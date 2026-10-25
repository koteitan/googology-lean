import Googology.Trans.PoR.InaccPsi.R2.HaSRec

/-!
# HaSU: THE SELF-READ UNION AT `evZ(Q)` OF A GATED STAGE

`Gz.gzSU` for a gated stage `Bp : Ha.HaPB`: the union of all `haSD Bp U0 d`, `d < evZ(Q)`, has the bound `evZ(Q)`, base
gate `γ_P`, base reading `evZ(P(x))`, bound field `evZ(evZ(P(x)))` above `γ_P` and `B₃(x)` below.  Codes `c ≥ Q` with
gate below a base `σ` force `γ_P < σ` (`haS_high_gate`); the tower systems have base gate below every base above
`γ_P` (`haST_gate`); the union starts the next stage (`haSU_start`).

* `haSN`, `haSR`, `haSg`, `haS_small`, `haS_high_gate`, `haST`, `haST_lt`, `haST_sup`, `haST_B`, `haST_gate`,
  `haST_K`, `haSRR`, `haSRR_succ`, `haSRR_cof`, `haSU` (**THE UNION AT `evZ(Q)`**), `haSU_B`, `haSU_Z`, `haSU_γ`,
  `haSU_b`, `haSU_R`, `haSU_g`, `haSU_start` (**IT STARTS THE NEXT STAGE**).

No new axiom.  New definitions: `haSN`, `haSR`, `haSg`, `haST`, `haSRR`, `haSU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz

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

variable (Bp : HaPB) (U0 : GzVD)

/-- The first system `haSD Bp U0 ν` containing `c`. -/
noncomputable def haSN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < evZ Bp.Q ∧ c < (haSD Bp U0 ν).B}

/-- The reading of the union. -/
noncomputable def haSR (c x : Ordinal.{0}) : Ordinal.{0} := (haSD Bp U0 (haSN Bp U0 c)).R c x

/-- The gate of the union. -/
noncomputable def haSg (c : Ordinal.{0}) : Ordinal.{0} := (haSD Bp U0 (haSN Bp U0 c)).g c

/-- **The tower of the stage**: `t_0 = 1`, `t_{k+1} = φ(1, Q + t_k)`. -/
noncomputable def haST : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (Bp.Q + haST k)

/-- **The reading of the tower code `t_k`** at the base `x` (in `haSD Bp U0 t_k`). -/
noncomputable def haSRR (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (haSD Bp U0 (haST Bp k)).R (haST Bp k) x

theorem haST_lt : ∀ k : ℕ, haST Bp k < evZ Bp.Q
  | 0 => one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
  | k + 1 => gzq_veb_lt_Z (haST_lt k)

theorem haST_pos : ∀ k : ℕ, 0 < haST Bp k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (Bp.Q + haST Bp k))

theorem haST_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.Q + 1) ≤ Bp.Q + haST Bp k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ Bp.Q + veblen 1 (Bp.Q + haST Bp k)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `evZ(Q)`.** -/
theorem haST_sup {t : Ordinal.{0}} (ht : t < evZ Bp.Q) : ∃ k : ℕ, t < haST Bp k := by
  have ht' : t < evZ (Bp.Q) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  refine ⟨k + 1, (hk.trans_le (haST_iter Bp k)).trans ?_⟩
  exact gzq_lt_veb Bp.Q_fix (haST_pos Bp k) (haST_lt Bp k)

theorem haSRR_zero (x : Ordinal.{0}) : haSRR Bp U0 0 x = 1 := (haSD Bp U0 1).R_one x

end Def

section Union

variable {Bp : HaPB} {U0 : GzVD} (hU : HaSStart Bp U0)
include hU

theorem haS_memB {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : ∃ ν, ν < evZ Bp.Q ∧ c < (haSD Bp U0 ν).B :=
  ⟨c, hc, haS_self hU hc⟩

omit hU in
theorem haSN_spec {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (haSD Bp U0 ν).B) :
    haSN Bp U0 c ≤ ν ∧ haSN Bp U0 c < evZ Bp.Q ∧ c < (haSD Bp U0 (haSN Bp U0 c)).B := by
  have hne : ({ν | ν < evZ Bp.Q ∧ c < (haSD Bp U0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hU in
theorem haSN_min {c μ : Ordinal.{0}} (hμ : μ < haSN Bp U0 c) (hμl : μ < evZ Bp.Q) : ¬ c < (haSD Bp U0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : haSN Bp U0 c ≤ μ) (not_le.2 hμ)

theorem haS_B_lt_Z {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : (haSD Bp U0 c).B < evZ Bp.Q := by
  rw [haS_B hU hc]; exact gzq_veb_lt_Z hc

theorem haSN_high {c : Ordinal.{0}} (hc : evZ Bp.Q ≤ c) : haSN Bp U0 c = 0 := by
  unfold haSN
  have he : ({ν | ν < evZ Bp.Q ∧ c < (haSD Bp U0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (haS_B_lt_Z hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem haSR_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (haSD Bp U0 ν).B) (x : Ordinal.{0}) :
    haSR Bp U0 c x = (haSD Bp U0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := haSN_spec hν hc
  exact ((haS_ext hU h1 hν).1 c x h3).symm

theorem haSg_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (haSD Bp U0 ν).B) :
    haSg Bp U0 c = (haSD Bp U0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := haSN_spec hν hc
  exact ((haS_ext hU h1 hν).2 c h3).symm

omit hU in
theorem haS_lim2 : IsSuccLimit (evZ Bp.Q) := ev_isSuccLimit_of_inE (evZ_E _)

theorem haSR_succ (c x : Ordinal.{0}) : haSR Bp U0 (c + 1) x = haSR Bp U0 c x + 1 := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (haS_lim2 (Bp := Bp)).add_one_lt h
    rw [haSR_eq hU h1 (haS_self hU h1), haSR_eq hU h1 ((lt_add_one c).trans (haS_self hU h1)),
      (haSD Bp U0 (c + 1)).R_succ]
  · unfold haSR
    rw [haSN_high hU h, haSN_high hU (h.trans (le_self_add (a := c) (b := 1))), (haSD Bp U0 0).R_succ]

theorem haSg_le_succ (c : Ordinal.{0}) : haSg Bp U0 c ≤ haSg Bp U0 (c + 1) := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (haS_lim2 (Bp := Bp)).add_one_lt h
    rw [haSg_eq hU h1 (haS_self hU h1), haSg_eq hU h1 ((lt_add_one c).trans (haS_self hU h1))]
    exact (haSD Bp U0 (c + 1)).g_le_succ c
  · unfold haSg
    rw [haSN_high hU h, haSN_high hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (haSD Bp U0 0).g_le_succ c

omit hU in
theorem haS_zero_lt2 : (0 : Ordinal.{0}) < evZ Bp.Q := (evZ_E _).pos

/-- **A code of the union with gate below an `ε`-number `σ > γ_P` lies in a member with base gate below `σ`.** -/
theorem haS_small {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hσ : InE σ) (hσ1 : σ < Om1) (hγσ : Bp.γP < σ)
    (hg : haSg Bp U0 c < σ) : ∃ μ, μ < evZ Bp.Q ∧ c < (haSD Bp U0 μ).B ∧ (haSD Bp U0 μ).γ < σ := by
  obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := haSN_spec hk1 hk
  have hgN : haSg Bp U0 c = (haSD Bp U0 (haSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (haSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨haSN Bp U0 c, hN1, hcN, ?_⟩
    rw [h0, haSD_zero]; exact (hU.γ σ hσ hσ1).2 hγσ
  · have hm' : haSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < haSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (haSD Bp U0 m).B ≤ c := not_lt.1 (haSN_min hmN hml)
    have hs : haSD Bp U0 (haSN Bp U0 c) = (haSD Bp U0 m).step := by rw [hm']; exact haSD_succ Bp U0 m
    refine ⟨haSN Bp U0 c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((haSD Bp U0 m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [haS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine haSN_min hd hdl ?_
    rw [haS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-- **A code `c ∈ [Q, evZ(Q))` of the union with gate below an `ε`-number `σ` forces `γ_P < σ`.** -/
theorem haS_high_gate {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hQc : Bp.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : haSg Bp U0 c < σ) : Bp.γP < σ := by
  obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := haSN_spec hk1 hk
  have hgN : haSg Bp U0 c = (haSD Bp U0 (haSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (haSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · exfalso
    rw [h0, haS_B hU haS_zero_lt2, add_zero, Bp.Q_fix] at hcN
    exact absurd hQc (not_le.2 hcN)
  · have hm' : haSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < haSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (haSD Bp U0 m).B ≤ c := not_lt.1 (haSN_min hmN hml)
    have hs : haSD Bp U0 (haSN Bp U0 c) = (haSD Bp U0 m).step := by rw [hm']; exact haSD_succ Bp U0 m
    rw [hgN, hs] at hg
    have hγm : (haSD Bp U0 m).γ < σ := ((haSD Bp U0 m).γ_le_sG hBc).trans_lt hg
    exact (max_lt_iff.1 ((haS_γ_iff hU hml hσ hσ1).1 hγm)).1
  · exfalso
    rw [haS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine haSN_min hd hdl ?_
    rw [haS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-! ## The tower readings -/

theorem haST_B (k : ℕ) : (haSD Bp U0 (haST Bp k)).B = haST Bp (k + 1) := haS_B hU (haST_lt Bp k)

omit hU in
theorem haS_one_eq : haSD Bp U0 1 = U0.step := by
  have h := haSD_succ Bp U0 0
  rw [zero_add, haSD_zero] at h
  exact h

/-- **Every `haSD Bp U0 t_k` has base gate below every `ε`-number base above `γ_P`.** -/
theorem haST_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → Bp.γP < x → (haSD Bp U0 (haST Bp k)).γ < x
  | 0, x, hx, hx1, hγ => by
    show (haSD Bp U0 1).γ < x
    rw [haS_one_eq, GzVD.step_γ]; exact (hU.γ x hx hx1).2 hγ
  | k + 1, x, hx, hx1, hγ => by
    set a := haST Bp k with ha
    have haZ : a < evZ Bp.Q := haST_lt Bp k
    have hμ : haST Bp (k + 1) = (haSD Bp U0 a).B := (haST_B hU k).symm
    have hμZ : haST Bp (k + 1) < evZ Bp.Q := haST_lt Bp (k + 1)
    have ha1 : a + 1 ≤ haST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact haS_self hU haZ)
    have ha1Z : a + 1 < evZ Bp.Q := (haS_lim2 (Bp := Bp)).add_one_lt haZ
    have hμB : haST Bp (k + 1) < (haSD Bp U0 (a + 1)).B := by
      rw [haS_B hU ha1Z]
      show veblen 1 (Bp.Q + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [haS_γ_iff hU hμZ hx hx1, (haS_ext hU ha1 hμZ).2 _ hμB, haSD_succ]
    show max Bp.γP ((haSD Bp U0 a).step.g (haST Bp (k + 1))) < x
    rw [hμ, GzVD.step_g_B]
    exact max_lt hγ (haST_gate k x hx hx1 hγ)

theorem haST_K (S : InaccSeq.{0}) (hK : Bp.γP < Td.tdK S) (k : ℕ) : (haSD Bp U0 (haST Bp k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact haST_gate hU k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1 hK

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Bp.γP < x)
include hx hx1 hγ

theorem haSRR_g (k : ℕ) : (haSD Bp U0 (haST Bp k)).g (haST Bp k) < x :=
  (max_lt_iff.1 ((haS_γ_iff hU (haST_lt Bp k) hx hx1).1 (haST_gate hU k x hx hx1 hγ))).2

/-- **`r_{k+1} = φ(1, P(x) + r_k)`.** -/
theorem haSRR_succ (k : ℕ) : haSRR Bp U0 (k + 1) x = veblen 1 (Bp.P x + haSRR Bp U0 k x) := by
  set a := haST Bp k with ha
  have haZ : a < evZ Bp.Q := haST_lt Bp k
  have hμ : haST Bp (k + 1) = (haSD Bp U0 a).B := (haST_B hU k).symm
  have hμZ : haST Bp (k + 1) < evZ Bp.Q := haST_lt Bp (k + 1)
  have ha1 : a + 1 ≤ haST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact haS_self hU haZ)
  have ha1Z : a + 1 < evZ Bp.Q := (haS_lim2 (Bp := Bp)).add_one_lt haZ
  have hμB : haST Bp (k + 1) < (haSD Bp U0 (a + 1)).B := by
    rw [haS_B hU ha1Z]
    show veblen 1 (Bp.Q + a) < _
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
  have hγa : (haSD Bp U0 a).γ < x := haST_gate hU k x hx hx1 hγ
  unfold haSRR
  rw [(haS_ext hU ha1 hμZ).1 _ x hμB, haSD_succ]
  show (haSD Bp U0 a).step.R (haST Bp (k + 1)) x = _
  have h1 : (1 : Ordinal.{0}) < (haSD Bp U0 a).NB := (haSD Bp U0 a).one_lt_B.trans (haSD Bp U0 a).B_lt_NB
  have hpow := (haSD Bp U0 a).hR_pow one_ne_zero h1 x
  rw [opow_one, (haSD Bp U0 a).hR_one, opow_one] at hpow
  rw [GzVD.step_R, hμ, hpow, haS_b hU haZ hx hx1 hγa]

theorem haSRR_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.P x + 1) ≤ haSRR Bp U0 (k + 1) x := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, haSRR_succ hU hx hx1 hγ 0, haSRR_zero]
    exact right_le_veblen 1 _
  | succ k ih =>
    rw [Function.iterate_succ_apply', haSRR_succ hU hx hx1 hγ (k + 1)]
    show veblen 1 _ ≤ _
    exact (isNormal_veblen 1).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `evZ(P(x))`.** -/
theorem haSRR_cof {t : Ordinal.{0}} (ht : t < evZ (Bp.P x)) : ∃ k : ℕ, t < haSRR Bp U0 k x := by
  have ht' : t < evZ (Bp.P x) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  exact ⟨k + 1, hk.trans_le (haSRR_iter hU hx hx1 hγ k)⟩

end Base

theorem haS_b_lt {μ x : Ordinal.{0}} (hμ : μ < evZ Bp.Q) (hx : InE x) (hx1 : x < Om1)
    (hμx : (haSD Bp U0 μ).γ < x) : (haSD Bp U0 μ).b x < evZ (Bp.P x) := by
  have hγ : Bp.γP < x := (max_lt_iff.1 ((haS_γ_iff hU hμ hx hx1).1 hμx)).1
  have h := (haSD Bp U0 μ).b_Z x hx hx1 hμx
  rw [haS_Z hU hμ hx hx1, Bp.Zst_eq hγ] at h
  exact (lt_eN _).trans h

theorem haS_R_lt {k c x : Ordinal.{0}} (hk1 : k < evZ Bp.Q) (hk : c < (haSD Bp U0 k).B) (hx : InE x)
    (hx1 : x < Om1) (hg : (haSD Bp U0 k).g c < x) : (haSD Bp U0 k).R c x < Bp.Zst x := by
  have h := (haSD Bp U0 k).R_lt_Z x hx hx1 c hk hg
  rw [haS_Z hU hk1 hx hx1] at h
  exact h

open Classical in
/-- The bound field of the union: `evZ(evZ(P(x)))` above `γ_P`, `B₃(x)` below. -/
noncomputable def haSUZ (Bp : HaPB) (x : Ordinal.{0}) : Ordinal.{0} :=
  if Bp.γP < x then evZ (evZ (Bp.P x)) else gzB3 x

omit hU in
theorem haSUZ_fix (x : Ordinal.{0}) : veblen 1 (haSUZ Bp x) = haSUZ Bp x := by
  unfold haSUZ
  split_ifs
  · exact epsilon_evZ _
  · have h := veblen_veblen_of_lt (one_lt_two (α := Ordinal.{0})) (gzB3 x)
    rw [gzB3_fix] at h; exact h

omit hU in
theorem haSUZ_B3 (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : haSUZ Bp x ≤ gzB3 x := by
  unfold haSUZ
  split_ifs with h
  · exact (gz_evZ_lt_B3 (Bp.evP_B3 hx hx1 h)).le
  · exact le_rfl

omit hU in
theorem haSUZ_ge (x : Ordinal.{0}) : Bp.Zst x ≤ haSUZ Bp x := by
  unfold haSUZ HaPB.Zst
  split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE UNION AT `evZ(Q)`**: bound `evZ(Q)`, base gate `γ_P`, base reading `evZ(P(x))` (its own index), bound field
`evZ(evZ(P(x)))` above `γ_P`. -/
noncomputable def haSU : GzVD where
  Z := haSUZ Bp
  Z_fix := fun x _ _ => haSUZ_fix x
  Z_B3 := haSUZ_B3
  B := evZ Bp.Q
  γ := Bp.γP
  γ_lt := Bp.γP_lt
  γ_cl := fun _ hZ hZ1 h => Bp.evQ_gate hZ hZ1 h
  γ_G := fun h => absurd h ((Bp.G_le_Q.trans_lt (lt_evZ _)).ne')
  R := haSR Bp U0
  g := haSg Bp U0
  b := fun x => evZ (Bp.P x)
  ba := fun x => evZ (Bp.P x)
  ix := evZ Bp.Q
  B_E := evZ_E _
  G_le := Bp.G_le_Q.trans (lt_evZ _).le
  B_lt1 := Bp.evQ_lt1
  B_ix := (epsilon_evZ _).symm
  ix_mem := fun S a b ha hb => Bp.evQ_mem S ha hb
  g_lt := fun c hc => by
    rw [haSg_eq hU hc (haS_self hU hc)]; exact (haSD Bp U0 c).g_lt c (haS_self hU hc)
  g_zero := by rw [haSg_eq hU haS_zero_lt2 (haSD Bp U0 0).B_pos]; exact (haSD Bp U0 0).g_zero
  g_nat := fun k => by
    rw [haSg_eq hU haS_zero_lt2 ((haSD Bp U0 0).nat_lt_B k)]; exact (haSD Bp U0 0).g_nat k
  g_E := by rw [haSg_eq hU haS_zero_lt2 (haSD Bp U0 0).E_lt_B]; exact (haSD Bp U0 0).g_E
  g_lowE := fun c hc => by
    rw [haSg_eq hU haS_zero_lt2 (hc.trans (haSD Bp U0 0).E_lt_B)]; exact (haSD Bp U0 0).g_lowE c hc
  g_G0 := fun h => by
    rw [haSg_eq hU h (haS_self hU h)]; exact (haSD Bp U0 (gcG 0)).g_G0 (haS_self hU h)
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hxy
    have hx : x < (haSD Bp U0 k).B := lt_of_le_of_lt le_self_add hk
    have hy : y < (haSD Bp U0 k).B := lt_of_le_of_lt le_add_self hk
    rw [haSg_eq hU hk1 hk]; rw [haSg_eq hU hk1 hx] at hgx; rw [haSg_eq hU hk1 hy] at hgy
    exact (haSD Bp U0 k).g_add Z hZ hωZ x y hk hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hy
    have hy' : y < (haSD Bp U0 k).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hk
    rw [haSg_eq hU hk1 hk]; rw [haSg_eq hU hk1 hy'] at hg
    exact (haSD Bp U0 k).g_opow Z hZw hωZ y hk hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hcB
    rw [haSg_eq hU hk1 hk]
    exact (haSD Bp U0 k).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (haS_B_lt_Z hU hk1).le.trans h)) c hc hk
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    have hc' : c < (haSD Bp U0 k).B := (lt_add_one c).trans hk
    rw [haSg_eq hU hk1 hk]; rw [haSg_eq hU hk1 hc'] at hg
    exact (haSD Bp U0 k).g_succ Z hZ c hk hg
  g_le_succ := haSg_le_succ hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSg_eq hU hk1 hk] at hg
    exact (haSD Bp U0 k).mem S a b ha c hk hg
  R_zero := fun x => by rw [haSR_eq hU haS_zero_lt2 (haSD Bp U0 0).B_pos]; exact (haSD Bp U0 0).R_zero x
  R_nat := fun k x => by
    rw [haSR_eq hU haS_zero_lt2 ((haSD Bp U0 0).nat_lt_B k)]; exact (haSD Bp U0 0).R_nat k x
  R_E := fun x => by rw [haSR_eq hU haS_zero_lt2 (haSD Bp U0 0).E_lt_B]; exact (haSD Bp U0 0).R_E x
  R_succ := haSR_succ hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSR_eq hU hk1 hk]; rw [haSg_eq hU hk1 hk] at hg
    exact (haSD Bp U0 k).R_pos x hx hx1 c hc0 hk hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSR_eq hU hk1 hk]; rw [haSg_eq hU hk1 hk] at hg
    exact (haSD Bp U0 k).R_omega x hx hx1 c hω hk hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSR_eq hU hk1 hk]; rw [haSg_eq hU hk1 hk] at hg
    have h := haS_R_lt hU hk1 hk hx hx1 hg
    rwa [Bp.Zst_eq hγx] at h
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSR_eq hU hk1 hk]; rw [haSg_eq hU hk1 hk] at hg
    have h := haS_R_lt hU hk1 hk hx hx1 hg
    show _ < haSUZ Bp x
    unfold haSUZ
    split_ifs with hγ
    · rw [Bp.Zst_eq hγ] at h; exact h.trans (lt_evZ _)
    · rwa [Bp.Zst_low hγ] at h
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    have hd : d < (haSD Bp U0 k).B := hdc.trans hk
    rw [haSR_eq hU hk1 hk, haSR_eq hU hk1 hd]; rw [haSg_eq hU hk1 hk] at hgc; rw [haSg_eq hU hk1 hd] at hgd
    exact (haSD Bp U0 k).mono x hx hx1 c hk d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSR_eq hU hk1 hk] at hν; rw [haSg_eq hU hk1 hk] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (haSD Bp U0 k).cof x hx hx1 c hk hg ν hν
    have hd : d < (haSD Bp U0 k).B := hdc.trans hk
    exact ⟨d, hdc, by rw [haSg_eq hU hk1 hd]; exact hgd, by rw [haSR_eq hU hk1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := haSRR_cof hU hx hx1 hγx hν
    have hkZ : haST Bp k < evZ Bp.Q := haST_lt Bp k
    have hkB : haST Bp k < (haSD Bp U0 (haST Bp k)).B := haS_self hU hkZ
    refine ⟨haST Bp k, hkZ, ?_, ?_⟩
    · rw [haSg_eq hU hkZ hkB]; exact haSRR_g hU hx hx1 hγx k
    · rw [haSR_eq hU hkZ hkB]; exact hk
  b_E := fun x _ _ _ => evZ_E _
  x_lt_b := fun x hx hx1 hγx => Bp.evP_gt hx hx1 hγx
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (epsilon_evZ _) (Bp.evP_gt hx hx1 hγx) (Bp.evP_lt hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => Bp.evP_lt hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < haSUZ Bp x
    unfold haSUZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ (evZ (Bp.P x)))
  b_pi := fun _ _ hB hγ => Bp.evP_pi hB hγ
  ba_pi := fun _ _ hB hγ => Bp.evP_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    rw [haSR_eq hU hk1 hk, haSR_eq hU hk1 hk]; rw [haSg_eq hU hk1 hk] at hg
    exact (haSD Bp U0 k).ex σ ρ hB c hk hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := haS_small hU hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [haSR_eq hU hμ hdμ, haSR_eq hU hμ hdμ]; rw [haSg_eq hU hμ hdμ] at hg
    exact (haSD Bp U0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (haS_b_lt hU hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨k, hk1, hk⟩ := haS_memB hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (haSD Bp U0 k).ld c hl hk
    have hcpn : cp < (haSD Bp U0 k).B := hcp.trans hk
    refine ⟨cp, lp, T, hcp, by rw [haSg_eq hU hk1 hk, haSg_eq hU hk1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← haSg_eq hU hk1 hk]; exact hg)⟩
    rw [haSg_eq hU hk1 hk] at hg
    rw [haSR_eq hU hk1 hk, haSR_eq hU hk1 hcpn]
    exact hdec x hx hx1 hg

theorem haSU_B : (haSU hU).B = evZ Bp.Q := rfl

theorem haSU_Z (x : Ordinal.{0}) : (haSU hU).Z x = haSUZ Bp x := rfl

theorem haSU_γ : (haSU hU).γ = Bp.γP := rfl

theorem haSU_b (x : Ordinal.{0}) : (haSU hU).b x = evZ (Bp.P x) := rfl

/-- **The union extends every `haSD Bp U0 ν`, `ν < evZ(Q)`** (readings). -/
theorem haSU_R {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (haSD Bp U0 ν).B) (x : Ordinal.{0}) :
    (haSU hU).R c x = (haSD Bp U0 ν).R c x := haSR_eq hU hν hc x

/-- **The union extends every `haSD Bp U0 ν`, `ν < evZ(Q)`** (gates). -/
theorem haSU_g {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (haSD Bp U0 ν).B) :
    (haSU hU).g c = (haSD Bp U0 ν).g c := haSg_eq hU hν hc

/-- **A code `c ∈ [Q, evZ(Q))` of the union with gate below a base `σ` forces its base gate below `σ`.** -/
theorem haSU_high_gate {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hQc : Bp.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (haSU hU).g c < σ) : (haSU hU).γ < σ := haS_high_gate hU hc hQc hσ hσ1 hg

/-- **THE UNION AT `evZ(Q)` STARTS THE NEXT STAGE** `Bp'` (`Q' = evZ(Q)`, the same gate at every base,
`P'(x) = evZ(P(x))` above it). -/
theorem haSU_start (Bp' : HaPB) (hQ : Bp'.Q = evZ Bp.Q)
    (hγ : ∀ x, InE x → x < Om1 → (Bp.γP < x ↔ Bp'.γP < x))
    (hP : ∀ x, InE x → x < Om1 → Bp'.γP < x → Bp'.P x = evZ (Bp.P x)) : HaSStart Bp' (haSU hU) where
  ix := hQ.symm
  γ := fun x hx hx1 => hγ x hx hx1
  b := fun x hx hx1 h => (hP x hx hx1 h).symm
  Z := fun x hx hx1 => by
    show haSUZ Bp x = Bp'.Zst x
    unfold haSUZ HaPB.Zst
    by_cases h : Bp.γP < x
    · rw [if_pos h, if_pos ((hγ x hx hx1).1 h), hP x hx hx1 ((hγ x hx hx1).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hγ x hx hx1).2 h'))]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Ha
