import Googology.Trans.PoR.InaccPsi.R2.GzSRec

/-!
# THE SELF-READ UNION AT `evZ(Q)` OF A STAGE (systems `GzVD`)

Port of `R2.GzZU` to the systems `Gz.GzVD` and any stage `Bp : GzPB`: the union of all `gzSD Bp U0 d`,
`d < evZ(Q)`, has the bound `evZ(Q)` (the next `ζ`-point) and reads its own index: base reading `evZ(P(x))`, base
gate `0`, bound field `evZ(evZ(P(x)))`.  The tower `t_0 = 1`, `t_{k+1} = ε_{Q+t_k}` (`gzST`) is cofinal in `evZ(Q)`,
its systems have gate below every base (`gzST_gate`), and its readings `r_{k+1} = φ(1, P(x) + r_k)` (`gzSRR_succ`) are
cofinal in `evZ(P(x))` (`gzSRR_cof`).  The union starts the next stage (`gzSU_start`).

* `gzSN`, `gzSR`, `gzSg`, `gzS_small`, `gzST`, `gzST_lt`, `gzST_sup`, `gzST_B`, `gzST_gate`, `gzST_K`, `gzSRR`,
  `gzSRR_succ`, `gzSRR_cof`, `gzSU` (**THE UNION AT `evZ(Q)`**), `gzSU_B`, `gzSU_Z`, `gzSU_γ`, `gzSU_b`, `gzSU_R`,
  `gzSU_g`, `gzSU_start` (**IT STARTS THE NEXT STAGE**).

No new axiom.  New definitions: `gzSN`, `gzSR`, `gzSg`, `gzST`, `gzSRR`, `gzSU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gz

open Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The union: first member containing a code -/

section Def

variable (Bp : GzPB) (U0 : GzVD)

/-- The first system `gzSD Bp U0 ν` containing `c`. -/
noncomputable def gzSN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < evZ Bp.Q ∧ c < (gzSD Bp U0 ν).B}

/-- The reading of the union. -/
noncomputable def gzSR (c x : Ordinal.{0}) : Ordinal.{0} := (gzSD Bp U0 (gzSN Bp U0 c)).R c x

/-- The gate of the union. -/
noncomputable def gzSg (c : Ordinal.{0}) : Ordinal.{0} := (gzSD Bp U0 (gzSN Bp U0 c)).g c

/-- **The tower of the stage**: `t_0 = 1`, `t_{k+1} = φ(1, Q + t_k)`. -/
noncomputable def gzST : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (Bp.Q + gzST k)

/-- **The reading of the tower code `t_k`** at the base `x` (in `gzSD Bp U0 t_k`). -/
noncomputable def gzSRR (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (gzSD Bp U0 (gzST Bp k)).R (gzST Bp k) x

theorem gzST_lt : ∀ k : ℕ, gzST Bp k < evZ Bp.Q
  | 0 => one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
  | k + 1 => gzq_veb_lt_Z (gzST_lt k)

theorem gzST_pos : ∀ k : ℕ, 0 < gzST Bp k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (Bp.Q + gzST Bp k))

theorem gzST_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.Q + 1) ≤ Bp.Q + gzST Bp k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ Bp.Q + veblen 1 (Bp.Q + gzST Bp k)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `evZ(Q)`.** -/
theorem gzST_sup {t : Ordinal.{0}} (ht : t < evZ Bp.Q) : ∃ k : ℕ, t < gzST Bp k := by
  have ht' : t < evZ (Bp.Q) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  refine ⟨k + 1, (hk.trans_le (gzST_iter Bp k)).trans ?_⟩
  exact gzq_lt_veb Bp.Q_fix (gzST_pos Bp k) (gzST_lt Bp k)

theorem gzSRR_zero (x : Ordinal.{0}) : gzSRR Bp U0 0 x = 1 := (gzSD Bp U0 1).R_one x

end Def

section Union

variable {Bp : GzPB} {U0 : GzVD} (hU : GzSStart Bp U0)
include hU

theorem gzS_memB {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : ∃ ν, ν < evZ Bp.Q ∧ c < (gzSD Bp U0 ν).B :=
  ⟨c, hc, gzS_self hU hc⟩

omit hU in
theorem gzSN_spec {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (gzSD Bp U0 ν).B) :
    gzSN Bp U0 c ≤ ν ∧ gzSN Bp U0 c < evZ Bp.Q ∧ c < (gzSD Bp U0 (gzSN Bp U0 c)).B := by
  have hne : ({ν | ν < evZ Bp.Q ∧ c < (gzSD Bp U0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hU in
theorem gzSN_min {c μ : Ordinal.{0}} (hμ : μ < gzSN Bp U0 c) (hμl : μ < evZ Bp.Q) : ¬ c < (gzSD Bp U0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : gzSN Bp U0 c ≤ μ) (not_le.2 hμ)

theorem gzS_B_lt_Z {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : (gzSD Bp U0 c).B < evZ Bp.Q := by
  rw [gzS_B hU hc]; exact gzq_veb_lt_Z hc

theorem gzSN_high {c : Ordinal.{0}} (hc : evZ Bp.Q ≤ c) : gzSN Bp U0 c = 0 := by
  unfold gzSN
  have he : ({ν | ν < evZ Bp.Q ∧ c < (gzSD Bp U0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (gzS_B_lt_Z hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem gzSR_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (gzSD Bp U0 ν).B) (x : Ordinal.{0}) :
    gzSR Bp U0 c x = (gzSD Bp U0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := gzSN_spec hν hc
  exact ((gzS_ext hU h1 hν).1 c x h3).symm

theorem gzSg_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (gzSD Bp U0 ν).B) :
    gzSg Bp U0 c = (gzSD Bp U0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := gzSN_spec hν hc
  exact ((gzS_ext hU h1 hν).2 c h3).symm

omit hU in
theorem gzS_lim2 : IsSuccLimit (evZ Bp.Q) := ev_isSuccLimit_of_inE (evZ_E _)

theorem gzSR_succ (c x : Ordinal.{0}) : gzSR Bp U0 (c + 1) x = gzSR Bp U0 c x + 1 := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (gzS_lim2 (Bp := Bp)).add_one_lt h
    rw [gzSR_eq hU h1 (gzS_self hU h1), gzSR_eq hU h1 ((lt_add_one c).trans (gzS_self hU h1)),
      (gzSD Bp U0 (c + 1)).R_succ]
  · unfold gzSR
    rw [gzSN_high hU h, gzSN_high hU (h.trans (le_self_add (a := c) (b := 1))), (gzSD Bp U0 0).R_succ]

theorem gzSg_le_succ (c : Ordinal.{0}) : gzSg Bp U0 c ≤ gzSg Bp U0 (c + 1) := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (gzS_lim2 (Bp := Bp)).add_one_lt h
    rw [gzSg_eq hU h1 (gzS_self hU h1), gzSg_eq hU h1 ((lt_add_one c).trans (gzS_self hU h1))]
    exact (gzSD Bp U0 (c + 1)).g_le_succ c
  · unfold gzSg
    rw [gzSN_high hU h, gzSN_high hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (gzSD Bp U0 0).g_le_succ c

omit hU in
theorem gzS_zero_lt2 : (0 : Ordinal.{0}) < evZ Bp.Q := (evZ_E _).pos

/-- **A code of the union with gate below an `ε`-number `σ` lies in a member with base gate below `σ`.** -/
theorem gzS_small {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hσ : InE σ) (hg : gzSg Bp U0 c < σ) :
    ∃ μ, μ < evZ Bp.Q ∧ c < (gzSD Bp U0 μ).B ∧ (gzSD Bp U0 μ).γ < σ := by
  obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := gzSN_spec hk1 hk
  have hgN : gzSg Bp U0 c = (gzSD Bp U0 (gzSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (gzSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨gzSN Bp U0 c, hN1, hcN, ?_⟩
    rw [h0, gzSD_zero, hU.γ]; exact hσ.pos
  · have hm' : gzSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < gzSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (gzSD Bp U0 m).B ≤ c := not_lt.1 (gzSN_min hmN hml)
    have hs : gzSD Bp U0 (gzSN Bp U0 c) = (gzSD Bp U0 m).step := by rw [hm']; exact gzSD_succ Bp U0 m
    refine ⟨gzSN Bp U0 c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((gzSD Bp U0 m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [gzS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine gzSN_min hd hdl ?_
    rw [gzS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-! ## The tower readings -/

theorem gzST_B (k : ℕ) : (gzSD Bp U0 (gzST Bp k)).B = gzST Bp (k + 1) := gzS_B hU (gzST_lt Bp k)

omit hU in
theorem gzS_one_eq : gzSD Bp U0 1 = U0.step := by
  have h := gzSD_succ Bp U0 0
  rw [zero_add, gzSD_zero] at h
  exact h

/-- **Every `gzSD Bp U0 t_k` has base gate below every `ε`-number base.** -/
theorem gzST_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → (gzSD Bp U0 (gzST Bp k)).γ < x
  | 0, x, hx, _ => by
    show (gzSD Bp U0 1).γ < x
    rw [gzS_one_eq, GzVD.step_γ, hU.γ]; exact hx.pos
  | k + 1, x, hx, hx1 => by
    set a := gzST Bp k with ha
    have haZ : a < evZ Bp.Q := gzST_lt Bp k
    have hμ : gzST Bp (k + 1) = (gzSD Bp U0 a).B := (gzST_B hU k).symm
    have hμZ : gzST Bp (k + 1) < evZ Bp.Q := gzST_lt Bp (k + 1)
    have ha1 : a + 1 ≤ gzST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gzS_self hU haZ)
    have ha1Z : a + 1 < evZ Bp.Q := (gzS_lim2 (Bp := Bp)).add_one_lt haZ
    have hμB : gzST Bp (k + 1) < (gzSD Bp U0 (a + 1)).B := by
      rw [gzS_B hU ha1Z]
      show veblen 1 (Bp.Q + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [gzS_γ_iff hU hμZ hx hx1, (gzS_ext hU ha1 hμZ).2 _ hμB, gzSD_succ]
    show (gzSD Bp U0 a).step.g (gzST Bp (k + 1)) < x
    rw [hμ, GzVD.step_g_B]
    exact gzST_gate k x hx hx1

theorem gzST_K (S : InaccSeq.{0}) (k : ℕ) : (gzSD Bp U0 (gzST Bp k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact gzST_gate hU k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gzSRR_g (k : ℕ) : (gzSD Bp U0 (gzST Bp k)).g (gzST Bp k) < x :=
  (gzS_γ_iff hU (gzST_lt Bp k) hx hx1).1 (gzST_gate hU k x hx hx1)

/-- **`r_{k+1} = φ(1, P(x) + r_k)`.** -/
theorem gzSRR_succ (k : ℕ) : gzSRR Bp U0 (k + 1) x = veblen 1 (Bp.P x + gzSRR Bp U0 k x) := by
  set a := gzST Bp k with ha
  have haZ : a < evZ Bp.Q := gzST_lt Bp k
  have hμ : gzST Bp (k + 1) = (gzSD Bp U0 a).B := (gzST_B hU k).symm
  have hμZ : gzST Bp (k + 1) < evZ Bp.Q := gzST_lt Bp (k + 1)
  have ha1 : a + 1 ≤ gzST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gzS_self hU haZ)
  have ha1Z : a + 1 < evZ Bp.Q := (gzS_lim2 (Bp := Bp)).add_one_lt haZ
  have hμB : gzST Bp (k + 1) < (gzSD Bp U0 (a + 1)).B := by
    rw [gzS_B hU ha1Z]
    show veblen 1 (Bp.Q + a) < _
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
  have hγ : (gzSD Bp U0 a).γ < x := gzST_gate hU k x hx hx1
  unfold gzSRR
  rw [(gzS_ext hU ha1 hμZ).1 _ x hμB, gzSD_succ]
  show (gzSD Bp U0 a).step.R (gzST Bp (k + 1)) x = _
  have h1 : (1 : Ordinal.{0}) < (gzSD Bp U0 a).NB := (gzSD Bp U0 a).one_lt_B.trans (gzSD Bp U0 a).B_lt_NB
  have hpow := (gzSD Bp U0 a).hR_pow one_ne_zero h1 x
  rw [opow_one, (gzSD Bp U0 a).hR_one, opow_one] at hpow
  rw [GzVD.step_R, hμ, hpow, gzS_b hU haZ hx hx1 hγ]

theorem gzSRR_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.P x + 1) ≤ gzSRR Bp U0 (k + 1) x := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, gzSRR_succ hU hx hx1 0, gzSRR_zero]
    exact right_le_veblen 1 _
  | succ k ih =>
    rw [Function.iterate_succ_apply', gzSRR_succ hU hx hx1 (k + 1)]
    show veblen 1 _ ≤ _
    exact (isNormal_veblen 1).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `evZ(P(x))`.** -/
theorem gzSRR_cof {t : Ordinal.{0}} (ht : t < evZ (Bp.P x)) : ∃ k : ℕ, t < gzSRR Bp U0 k x := by
  have ht' : t < evZ (Bp.P x) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  exact ⟨k + 1, hk.trans_le (gzSRR_iter hU hx hx1 k)⟩

end Base

theorem gzS_b_lt {μ x : Ordinal.{0}} (hμ : μ < evZ Bp.Q) (hx : InE x) (hx1 : x < Om1)
    (hμx : (gzSD Bp U0 μ).γ < x) : (gzSD Bp U0 μ).b x < evZ (Bp.P x) := by
  have h := (gzSD Bp U0 μ).b_Z x hx hx1 hμx
  rw [gzS_Z hU hμ hx hx1] at h
  exact (lt_eN _).trans h

theorem gzS_R_lt {k c x : Ordinal.{0}} (hk1 : k < evZ Bp.Q) (hk : c < (gzSD Bp U0 k).B) (hx : InE x)
    (hx1 : x < Om1) (hg : (gzSD Bp U0 k).g c < x) : (gzSD Bp U0 k).R c x < evZ (Bp.P x) := by
  have h := (gzSD Bp U0 k).R_lt_Z x hx hx1 c hk hg
  rw [gzS_Z hU hk1 hx hx1] at h
  exact h

/-- **THE UNION AT `evZ(Q)`**: bound `evZ(Q)`, base gate `0`, base reading `evZ(P(x))` (its own index), bound field
`evZ(evZ(P(x)))`. -/
noncomputable def gzSU : GzVD where
  Z := fun x => evZ (evZ (Bp.P x))
  Z_fix := fun x _ _ => epsilon_evZ _
  Z_B3 := fun x hx hx1 => (gz_evZ_lt_B3 (Bp.evP_B3 hx hx1)).le
  B := evZ Bp.Q
  γ := 0
  γ_lt := gv_Om1_pos
  γ_cl := fun _ hZ _ _ => hZ.1
  γ_G := fun _ => rfl
  R := gzSR Bp U0
  g := gzSg Bp U0
  b := fun x => evZ (Bp.P x)
  ba := fun x => evZ (Bp.P x)
  ix := evZ Bp.Q
  B_E := evZ_E _
  G_le := Bp.G_le_Q.trans (lt_evZ _).le
  B_lt1 := Bp.evQ_lt1
  B_ix := (epsilon_evZ _).symm
  ix_mem := fun S a b ha _ => Bp.evQ_mem S ha
  g_lt := fun c hc => by
    rw [gzSg_eq hU hc (gzS_self hU hc)]; exact (gzSD Bp U0 c).g_lt c (gzS_self hU hc)
  g_zero := by rw [gzSg_eq hU gzS_zero_lt2 (gzSD Bp U0 0).B_pos]; exact (gzSD Bp U0 0).g_zero
  g_nat := fun k => by
    rw [gzSg_eq hU gzS_zero_lt2 ((gzSD Bp U0 0).nat_lt_B k)]; exact (gzSD Bp U0 0).g_nat k
  g_E := by rw [gzSg_eq hU gzS_zero_lt2 (gzSD Bp U0 0).E_lt_B]; exact (gzSD Bp U0 0).g_E
  g_lowE := fun c hc => by
    rw [gzSg_eq hU gzS_zero_lt2 (hc.trans (gzSD Bp U0 0).E_lt_B)]; exact (gzSD Bp U0 0).g_lowE c hc
  g_G0 := fun h => by
    rw [gzSg_eq hU h (gzS_self hU h)]; exact (gzSD Bp U0 (gcG 0)).g_G0 (gzS_self hU h)
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hxy
    have hx : x < (gzSD Bp U0 k).B := lt_of_le_of_lt le_self_add hk
    have hy : y < (gzSD Bp U0 k).B := lt_of_le_of_lt le_add_self hk
    rw [gzSg_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hx] at hgx; rw [gzSg_eq hU hk1 hy] at hgy
    exact (gzSD Bp U0 k).g_add Z hZ hωZ x y hk hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hy
    have hy' : y < (gzSD Bp U0 k).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hk
    rw [gzSg_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hy'] at hg
    exact (gzSD Bp U0 k).g_opow Z hZw hωZ y hk hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hcB
    rw [gzSg_eq hU hk1 hk]
    exact (gzSD Bp U0 k).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (gzS_B_lt_Z hU hk1).le.trans h)) c hc hk
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    have hc' : c < (gzSD Bp U0 k).B := (lt_add_one c).trans hk
    rw [gzSg_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hc'] at hg
    exact (gzSD Bp U0 k).g_succ Z hZ c hk hg
  g_le_succ := gzSg_le_succ hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSg_eq hU hk1 hk] at hg
    exact (gzSD Bp U0 k).mem S a b ha c hk hg
  R_zero := fun x => by rw [gzSR_eq hU gzS_zero_lt2 (gzSD Bp U0 0).B_pos]; exact (gzSD Bp U0 0).R_zero x
  R_nat := fun k x => by
    rw [gzSR_eq hU gzS_zero_lt2 ((gzSD Bp U0 0).nat_lt_B k)]; exact (gzSD Bp U0 0).R_nat k x
  R_E := fun x => by rw [gzSR_eq hU gzS_zero_lt2 (gzSD Bp U0 0).E_lt_B]; exact (gzSD Bp U0 0).R_E x
  R_succ := gzSR_succ hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSR_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hk] at hg
    exact (gzSD Bp U0 k).R_pos x hx hx1 c hc0 hk hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSR_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hk] at hg
    exact (gzSD Bp U0 k).R_omega x hx hx1 c hω hk hg
  R_lt_b := fun x hx hx1 _ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSR_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hk] at hg
    exact gzS_R_lt hU hk1 hk hx hx1 hg
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSR_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hk] at hg
    exact (gzS_R_lt hU hk1 hk hx hx1 hg).trans (lt_evZ _)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    have hd : d < (gzSD Bp U0 k).B := hdc.trans hk
    rw [gzSR_eq hU hk1 hk, gzSR_eq hU hk1 hd]; rw [gzSg_eq hU hk1 hk] at hgc; rw [gzSg_eq hU hk1 hd] at hgd
    exact (gzSD Bp U0 k).mono x hx hx1 c hk d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSR_eq hU hk1 hk] at hν; rw [gzSg_eq hU hk1 hk] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (gzSD Bp U0 k).cof x hx hx1 c hk hg ν hν
    have hd : d < (gzSD Bp U0 k).B := hdc.trans hk
    exact ⟨d, hdc, by rw [gzSg_eq hU hk1 hd]; exact hgd, by rw [gzSR_eq hU hk1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 _ ν hν => by
    obtain ⟨k, hk⟩ := gzSRR_cof hU hx hx1 hν
    have hkZ : gzST Bp k < evZ Bp.Q := gzST_lt Bp k
    have hkB : gzST Bp k < (gzSD Bp U0 (gzST Bp k)).B := gzS_self hU hkZ
    refine ⟨gzST Bp k, hkZ, ?_, ?_⟩
    · rw [gzSg_eq hU hkZ hkB]; exact gzSRR_g hU hx hx1 k
    · rw [gzSR_eq hU hkZ hkB]; exact hk
  b_E := fun x _ _ _ => evZ_E _
  x_lt_b := fun x hx hx1 _ => Bp.evP_gt hx hx1
  b_eN := fun x hx hx1 _ => gz_eN_fix hx hx1 (epsilon_evZ _) (Bp.evP_gt hx hx1) (Bp.evP_lt hx hx1)
  ba_lt := fun x hx hx1 _ => Bp.evP_lt hx hx1
  b_Z := fun x _ _ _ => go_eN_lt_evZ (lt_evZ (evZ (Bp.P x)))
  b_pi := fun _ _ hB _ => Bp.evP_pi hB
  ba_pi := fun _ _ hB _ => Bp.evP_pi hB
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    rw [gzSR_eq hU hk1 hk, gzSR_eq hU hk1 hk]; rw [gzSg_eq hU hk1 hk] at hg
    exact (gzSD Bp U0 k).ex σ ρ hB c hk hg
  dig := fun σ ρ hB _ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := gzS_small hU hd hB.1 hg
    rw [gzSR_eq hU hμ hdμ, gzSR_eq hU hμ hdμ]; rw [gzSg_eq hU hμ hdμ] at hg
    exact (gzSD Bp U0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (gzS_b_lt hU hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨k, hk1, hk⟩ := gzS_memB hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (gzSD Bp U0 k).ld c hl hk
    have hcpn : cp < (gzSD Bp U0 k).B := hcp.trans hk
    refine ⟨cp, lp, T, hcp, by rw [gzSg_eq hU hk1 hk, gzSg_eq hU hk1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← gzSg_eq hU hk1 hk]; exact hg)⟩
    rw [gzSg_eq hU hk1 hk] at hg
    rw [gzSR_eq hU hk1 hk, gzSR_eq hU hk1 hcpn]
    exact hdec x hx hx1 hg

theorem gzSU_B : (gzSU hU).B = evZ Bp.Q := rfl

theorem gzSU_Z (x : Ordinal.{0}) : (gzSU hU).Z x = evZ (evZ (Bp.P x)) := rfl

theorem gzSU_γ : (gzSU hU).γ = 0 := rfl

theorem gzSU_b (x : Ordinal.{0}) : (gzSU hU).b x = evZ (Bp.P x) := rfl

/-- **The union extends every `gzSD Bp U0 ν`, `ν < evZ(Q)`** (readings). -/
theorem gzSU_R {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (gzSD Bp U0 ν).B) (x : Ordinal.{0}) :
    (gzSU hU).R c x = (gzSD Bp U0 ν).R c x := gzSR_eq hU hν hc x

/-- **The union extends every `gzSD Bp U0 ν`, `ν < evZ(Q)`** (gates). -/
theorem gzSU_g {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (gzSD Bp U0 ν).B) :
    (gzSU hU).g c = (gzSD Bp U0 ν).g c := gzSg_eq hU hν hc

/-- **THE UNION AT `evZ(Q)` STARTS THE NEXT STAGE** `Bp'` (`Q' = evZ(Q)`, `P'(x) = evZ(P(x))`). -/
theorem gzSU_start (Bp' : GzPB) (hQ : Bp'.Q = evZ Bp.Q) (hP : ∀ x, InE x → x < Om1 → Bp'.P x = evZ (Bp.P x)) :
    GzSStart Bp' (gzSU hU) where
  ix := hQ.symm
  γ := rfl
  b := fun x hx hx1 => (hP x hx hx1).symm
  Z := fun x hx hx1 => by rw [hP x hx hx1]; rfl

end Union

end Googology.Trans.PoR.InaccPsi.R2.Gz
