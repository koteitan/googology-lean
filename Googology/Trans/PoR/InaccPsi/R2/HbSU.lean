import Googology.Trans.PoR.InaccPsi.R2.HbSRec

/-!
# HbSU: THE SELF-READ UNION AT `evZ(Q)` OF A GATED STAGE

`Ha.haSU` (a textual copy) for `Hb.HbVD` and a stage `Bp : Hb.HbPB`: the union of all `hbSD Bp U0 d`, `d <
evZ(Q)`, has the bound `evZ(Q)`, base
gate `γ_P`, base reading `evZ(P(x))`, bound field `evZ(evZ(P(x)))` above `γ_P` and `Z_l(x)` below.  Codes `c ≥ Q` with
gate below a base `σ` force `γ_P < σ` (`hbS_high_gate`); the tower systems have base gate below every base above
`γ_P` (`hbST_gate`); the union starts the next stage (`hbSU_start`).

* `hbSN`, `hbSR`, `hbSg`, `hbS_small`, `hbS_high_gate`, `hbST`, `hbST_lt`, `hbST_sup`, `hbST_B`, `hbST_gate`,
  `hbST_K`, `hbSRR`, `hbSRR_succ`, `hbSRR_cof`, `hbSU` (**THE UNION AT `evZ(Q)`**), `hbSU_B`, `hbSU_Z`, `hbSU_γ`,
  `hbSU_b`, `hbSU_R`, `hbSU_g`, `hbSU_start` (**IT STARTS THE NEXT STAGE**).

No new axiom.  New definitions: `hbSN`, `hbSR`, `hbSg`, `hbST`, `hbSRR`, `hbSU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Ha

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

variable (Bp : HbPB) (U0 : HbVD)

/-- The first system `hbSD Bp U0 ν` containing `c`. -/
noncomputable def hbSN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < evZ Bp.Q ∧ c < (hbSD Bp U0 ν).B}

/-- The reading of the union. -/
noncomputable def hbSR (c x : Ordinal.{0}) : Ordinal.{0} := (hbSD Bp U0 (hbSN Bp U0 c)).R c x

/-- The gate of the union. -/
noncomputable def hbSg (c : Ordinal.{0}) : Ordinal.{0} := (hbSD Bp U0 (hbSN Bp U0 c)).g c

/-- **The tower of the stage**: `t_0 = 1`, `t_{k+1} = φ(1, Q + t_k)`. -/
noncomputable def hbST : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (Bp.Q + hbST k)

/-- **The reading of the tower code `t_k`** at the base `x` (in `hbSD Bp U0 t_k`). -/
noncomputable def hbSRR (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (hbSD Bp U0 (hbST Bp k)).R (hbST Bp k) x

theorem hbST_lt : ∀ k : ℕ, hbST Bp k < evZ Bp.Q
  | 0 => one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
  | k + 1 => gzq_veb_lt_Z (hbST_lt k)

theorem hbST_pos : ∀ k : ℕ, 0 < hbST Bp k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (Bp.Q + hbST Bp k))

theorem hbST_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.Q + 1) ≤ Bp.Q + hbST Bp k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ Bp.Q + veblen 1 (Bp.Q + hbST Bp k)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `evZ(Q)`.** -/
theorem hbST_sup {t : Ordinal.{0}} (ht : t < evZ Bp.Q) : ∃ k : ℕ, t < hbST Bp k := by
  have ht' : t < evZ (Bp.Q) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  refine ⟨k + 1, (hk.trans_le (hbST_iter Bp k)).trans ?_⟩
  exact gzq_lt_veb Bp.Q_fix (hbST_pos Bp k) (hbST_lt Bp k)

theorem hbSRR_zero (x : Ordinal.{0}) : hbSRR Bp U0 0 x = 1 := (hbSD Bp U0 1).R_one x

end Def

section Union

variable {Bp : HbPB} {U0 : HbVD} (hU : HbSStart Bp U0)
include hU

theorem hbS_memB {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : ∃ ν, ν < evZ Bp.Q ∧ c < (hbSD Bp U0 ν).B :=
  ⟨c, hc, hbS_self hU hc⟩

omit hU in
theorem hbSN_spec {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hbSD Bp U0 ν).B) :
    hbSN Bp U0 c ≤ ν ∧ hbSN Bp U0 c < evZ Bp.Q ∧ c < (hbSD Bp U0 (hbSN Bp U0 c)).B := by
  have hne : ({ν | ν < evZ Bp.Q ∧ c < (hbSD Bp U0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hU in
theorem hbSN_min {c μ : Ordinal.{0}} (hμ : μ < hbSN Bp U0 c) (hμl : μ < evZ Bp.Q) : ¬ c < (hbSD Bp U0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hbSN Bp U0 c ≤ μ) (not_le.2 hμ)

theorem hbS_B_lt_Z {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : (hbSD Bp U0 c).B < evZ Bp.Q := by
  rw [hbS_B hU hc]; exact gzq_veb_lt_Z hc

theorem hbSN_high {c : Ordinal.{0}} (hc : evZ Bp.Q ≤ c) : hbSN Bp U0 c = 0 := by
  unfold hbSN
  have he : ({ν | ν < evZ Bp.Q ∧ c < (hbSD Bp U0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hbS_B_lt_Z hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hbSR_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hbSD Bp U0 ν).B) (x : Ordinal.{0}) :
    hbSR Bp U0 c x = (hbSD Bp U0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hbSN_spec hν hc
  exact ((hbS_ext hU h1 hν).1 c x h3).symm

theorem hbSg_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hbSD Bp U0 ν).B) :
    hbSg Bp U0 c = (hbSD Bp U0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hbSN_spec hν hc
  exact ((hbS_ext hU h1 hν).2 c h3).symm

omit hU in
theorem hbS_lim2 : IsSuccLimit (evZ Bp.Q) := ev_isSuccLimit_of_inE (evZ_E _)

theorem hbSR_succ (c x : Ordinal.{0}) : hbSR Bp U0 (c + 1) x = hbSR Bp U0 c x + 1 := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (hbS_lim2 (Bp := Bp)).add_one_lt h
    rw [hbSR_eq hU h1 (hbS_self hU h1), hbSR_eq hU h1 ((lt_add_one c).trans (hbS_self hU h1)),
      (hbSD Bp U0 (c + 1)).R_succ]
  · unfold hbSR
    rw [hbSN_high hU h, hbSN_high hU (h.trans (le_self_add (a := c) (b := 1))), (hbSD Bp U0 0).R_succ]

theorem hbSg_le_succ (c : Ordinal.{0}) : hbSg Bp U0 c ≤ hbSg Bp U0 (c + 1) := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (hbS_lim2 (Bp := Bp)).add_one_lt h
    rw [hbSg_eq hU h1 (hbS_self hU h1), hbSg_eq hU h1 ((lt_add_one c).trans (hbS_self hU h1))]
    exact (hbSD Bp U0 (c + 1)).g_le_succ c
  · unfold hbSg
    rw [hbSN_high hU h, hbSN_high hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hbSD Bp U0 0).g_le_succ c

omit hU in
theorem hbS_zero_lt2 : (0 : Ordinal.{0}) < evZ Bp.Q := (evZ_E _).pos

/-- **A code of the union with gate below an `ε`-number `σ > γ_P` lies in a member with base gate below `σ`.** -/
theorem hbS_small {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hσ : InE σ) (hσ1 : σ < Om1) (hγσ : Bp.γP < σ)
    (hg : hbSg Bp U0 c < σ) : ∃ μ, μ < evZ Bp.Q ∧ c < (hbSD Bp U0 μ).B ∧ (hbSD Bp U0 μ).γ < σ := by
  obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := hbSN_spec hk1 hk
  have hgN : hbSg Bp U0 c = (hbSD Bp U0 (hbSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (hbSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hbSN Bp U0 c, hN1, hcN, ?_⟩
    rw [h0, hbSD_zero]; exact (hU.γ σ hσ hσ1).2 hγσ
  · have hm' : hbSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hbSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (hbSD Bp U0 m).B ≤ c := not_lt.1 (hbSN_min hmN hml)
    have hs : hbSD Bp U0 (hbSN Bp U0 c) = (hbSD Bp U0 m).step := by rw [hm']; exact hbSD_succ Bp U0 m
    refine ⟨hbSN Bp U0 c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((hbSD Bp U0 m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [hbS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine hbSN_min hd hdl ?_
    rw [hbS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-- **A code `c ∈ [Q, evZ(Q))` of the union with gate below an `ε`-number `σ` forces `γ_P < σ`.** -/
theorem hbS_high_gate {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hQc : Bp.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hbSg Bp U0 c < σ) : Bp.γP < σ := by
  obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := hbSN_spec hk1 hk
  have hgN : hbSg Bp U0 c = (hbSD Bp U0 (hbSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (hbSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · exfalso
    rw [h0, hbS_B hU hbS_zero_lt2, add_zero, Bp.Q_fix] at hcN
    exact absurd hQc (not_le.2 hcN)
  · have hm' : hbSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hbSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (hbSD Bp U0 m).B ≤ c := not_lt.1 (hbSN_min hmN hml)
    have hs : hbSD Bp U0 (hbSN Bp U0 c) = (hbSD Bp U0 m).step := by rw [hm']; exact hbSD_succ Bp U0 m
    rw [hgN, hs] at hg
    have hγm : (hbSD Bp U0 m).γ < σ := ((hbSD Bp U0 m).γ_le_sG hBc).trans_lt hg
    exact (max_lt_iff.1 ((hbS_γ_iff hU hml hσ hσ1).1 hγm)).1
  · exfalso
    rw [hbS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine hbSN_min hd hdl ?_
    rw [hbS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-! ## The tower readings -/

theorem hbST_B (k : ℕ) : (hbSD Bp U0 (hbST Bp k)).B = hbST Bp (k + 1) := hbS_B hU (hbST_lt Bp k)

omit hU in
theorem hbS_one_eq : hbSD Bp U0 1 = U0.step := by
  have h := hbSD_succ Bp U0 0
  rw [zero_add, hbSD_zero] at h
  exact h

/-- **Every `hbSD Bp U0 t_k` has base gate below every `ε`-number base above `γ_P`.** -/
theorem hbST_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → Bp.γP < x → (hbSD Bp U0 (hbST Bp k)).γ < x
  | 0, x, hx, hx1, hγ => by
    show (hbSD Bp U0 1).γ < x
    rw [hbS_one_eq, HbVD.step_γ]; exact (hU.γ x hx hx1).2 hγ
  | k + 1, x, hx, hx1, hγ => by
    set a := hbST Bp k with ha
    have haZ : a < evZ Bp.Q := hbST_lt Bp k
    have hμ : hbST Bp (k + 1) = (hbSD Bp U0 a).B := (hbST_B hU k).symm
    have hμZ : hbST Bp (k + 1) < evZ Bp.Q := hbST_lt Bp (k + 1)
    have ha1 : a + 1 ≤ hbST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact hbS_self hU haZ)
    have ha1Z : a + 1 < evZ Bp.Q := (hbS_lim2 (Bp := Bp)).add_one_lt haZ
    have hμB : hbST Bp (k + 1) < (hbSD Bp U0 (a + 1)).B := by
      rw [hbS_B hU ha1Z]
      show veblen 1 (Bp.Q + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [hbS_γ_iff hU hμZ hx hx1, (hbS_ext hU ha1 hμZ).2 _ hμB, hbSD_succ]
    show max Bp.γP ((hbSD Bp U0 a).step.g (hbST Bp (k + 1))) < x
    rw [hμ, HbVD.step_g_B]
    exact max_lt hγ (hbST_gate k x hx hx1 hγ)

theorem hbST_K (S : InaccSeq.{0}) (hK : Bp.γP < Td.tdK S) (k : ℕ) : (hbSD Bp U0 (hbST Bp k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact hbST_gate hU k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1 hK

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Bp.γP < x)
include hx hx1 hγ

theorem hbSRR_g (k : ℕ) : (hbSD Bp U0 (hbST Bp k)).g (hbST Bp k) < x :=
  (max_lt_iff.1 ((hbS_γ_iff hU (hbST_lt Bp k) hx hx1).1 (hbST_gate hU k x hx hx1 hγ))).2

/-- **`r_{k+1} = φ(1, P(x) + r_k)`.** -/
theorem hbSRR_succ (k : ℕ) : hbSRR Bp U0 (k + 1) x = veblen 1 (Bp.P x + hbSRR Bp U0 k x) := by
  set a := hbST Bp k with ha
  have haZ : a < evZ Bp.Q := hbST_lt Bp k
  have hμ : hbST Bp (k + 1) = (hbSD Bp U0 a).B := (hbST_B hU k).symm
  have hμZ : hbST Bp (k + 1) < evZ Bp.Q := hbST_lt Bp (k + 1)
  have ha1 : a + 1 ≤ hbST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact hbS_self hU haZ)
  have ha1Z : a + 1 < evZ Bp.Q := (hbS_lim2 (Bp := Bp)).add_one_lt haZ
  have hμB : hbST Bp (k + 1) < (hbSD Bp U0 (a + 1)).B := by
    rw [hbS_B hU ha1Z]
    show veblen 1 (Bp.Q + a) < _
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
  have hγa : (hbSD Bp U0 a).γ < x := hbST_gate hU k x hx hx1 hγ
  unfold hbSRR
  rw [(hbS_ext hU ha1 hμZ).1 _ x hμB, hbSD_succ]
  show (hbSD Bp U0 a).step.R (hbST Bp (k + 1)) x = _
  have h1 : (1 : Ordinal.{0}) < (hbSD Bp U0 a).NB := (hbSD Bp U0 a).one_lt_B.trans (hbSD Bp U0 a).B_lt_NB
  have hpow := (hbSD Bp U0 a).hR_pow one_ne_zero h1 x
  rw [opow_one, (hbSD Bp U0 a).hR_one, opow_one] at hpow
  rw [HbVD.step_R, hμ, hpow, hbS_b hU haZ hx hx1 hγa]

theorem hbSRR_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.P x + 1) ≤ hbSRR Bp U0 (k + 1) x := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, hbSRR_succ hU hx hx1 hγ 0, hbSRR_zero]
    exact right_le_veblen 1 _
  | succ k ih =>
    rw [Function.iterate_succ_apply', hbSRR_succ hU hx hx1 hγ (k + 1)]
    show veblen 1 _ ≤ _
    exact (isNormal_veblen 1).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `evZ(P(x))`.** -/
theorem hbSRR_cof {t : Ordinal.{0}} (ht : t < evZ (Bp.P x)) : ∃ k : ℕ, t < hbSRR Bp U0 k x := by
  have ht' : t < evZ (Bp.P x) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  exact ⟨k + 1, hk.trans_le (hbSRR_iter hU hx hx1 hγ k)⟩

end Base

theorem hbS_b_lt {μ x : Ordinal.{0}} (hμ : μ < evZ Bp.Q) (hx : InE x) (hx1 : x < Om1)
    (hμx : (hbSD Bp U0 μ).γ < x) : (hbSD Bp U0 μ).b x < evZ (Bp.P x) := by
  have hγ : Bp.γP < x := (max_lt_iff.1 ((hbS_γ_iff hU hμ hx hx1).1 hμx)).1
  have h := (hbSD Bp U0 μ).b_Z x hx hx1 hμx
  rw [hbS_Z hU hμ hx hx1, Bp.Zst_eq hγ] at h
  exact (lt_eN _).trans h

theorem hbS_R_lt {k c x : Ordinal.{0}} (hk1 : k < evZ Bp.Q) (hk : c < (hbSD Bp U0 k).B) (hx : InE x)
    (hx1 : x < Om1) (hg : (hbSD Bp U0 k).g c < x) : (hbSD Bp U0 k).R c x < Bp.Zst x := by
  have h := (hbSD Bp U0 k).R_lt_Z x hx hx1 c hk hg
  rw [hbS_Z hU hk1 hx hx1] at h
  exact h

open Classical in
/-- The bound field of the union: `evZ(evZ(P(x)))` above `γ_P`, `Z_l(x)` below. -/
noncomputable def hbSUZ (Bp : HbPB) (x : Ordinal.{0}) : Ordinal.{0} :=
  if Bp.γP < x then evZ (evZ (Bp.P x)) else Bp.Zl x

omit hU in
theorem hbSUZ_fix (x : Ordinal.{0}) : veblen 1 (hbSUZ Bp x) = hbSUZ Bp x := by
  unfold hbSUZ
  split_ifs
  · exact epsilon_evZ _
  · exact Bp.Zl_fix1 x

omit hU in
theorem hbSUZ_Zl (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hbSUZ Bp x ≤ Bp.Zl x := by
  unfold hbSUZ
  split_ifs with h
  · exact (hb_evZ_lt_fix2 (Bp.Zl_fix x) (Bp.evP_Zl hx hx1 h)).le
  · exact le_rfl

omit hU in
theorem hbSUZ_Bw (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hbSUZ Bp x ≤ hbBw x :=
  (hbSUZ_Zl x hx hx1).trans (Bp.Zl_Bw x hx hx1)

omit hU in
theorem hbSUZ_ge (x : Ordinal.{0}) : Bp.Zst x ≤ hbSUZ Bp x := by
  unfold hbSUZ HbPB.Zst
  split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE UNION AT `evZ(Q)`**: bound `evZ(Q)`, base gate `γ_P`, base reading `evZ(P(x))` (its own index), bound field
`evZ(evZ(P(x)))` above `γ_P`. -/
noncomputable def hbSU : HbVD where
  Z := hbSUZ Bp
  Z_fix := fun x _ _ => hbSUZ_fix x
  Z_Bw := hbSUZ_Bw
  B := evZ Bp.Q
  γ := Bp.γP
  γ_lt := Bp.γP_lt
  γ_cl := fun _ hZ hZ1 h => Bp.evQ_gate hZ hZ1 h
  γ_G := fun h => absurd h ((Bp.G_le_Q.trans_lt (lt_evZ _)).ne')
  R := hbSR Bp U0
  g := hbSg Bp U0
  b := fun x => evZ (Bp.P x)
  ba := fun x => evZ (Bp.P x)
  ix := evZ Bp.Q
  B_E := evZ_E _
  G_le := Bp.G_le_Q.trans (lt_evZ _).le
  B_lt1 := Bp.evQ_lt1
  B_ix := (epsilon_evZ _).symm
  ix_mem := fun S a b ha hb => Bp.evQ_mem S ha hb
  g_lt := fun c hc => by
    rw [hbSg_eq hU hc (hbS_self hU hc)]; exact (hbSD Bp U0 c).g_lt c (hbS_self hU hc)
  g_zero := by rw [hbSg_eq hU hbS_zero_lt2 (hbSD Bp U0 0).B_pos]; exact (hbSD Bp U0 0).g_zero
  g_nat := fun k => by
    rw [hbSg_eq hU hbS_zero_lt2 ((hbSD Bp U0 0).nat_lt_B k)]; exact (hbSD Bp U0 0).g_nat k
  g_E := by rw [hbSg_eq hU hbS_zero_lt2 (hbSD Bp U0 0).E_lt_B]; exact (hbSD Bp U0 0).g_E
  g_lowE := fun c hc => by
    rw [hbSg_eq hU hbS_zero_lt2 (hc.trans (hbSD Bp U0 0).E_lt_B)]; exact (hbSD Bp U0 0).g_lowE c hc
  g_G0 := fun h => by
    rw [hbSg_eq hU h (hbS_self hU h)]; exact (hbSD Bp U0 (gcG 0)).g_G0 (hbS_self hU h)
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hxy
    have hx : x < (hbSD Bp U0 k).B := lt_of_le_of_lt le_self_add hk
    have hy : y < (hbSD Bp U0 k).B := lt_of_le_of_lt le_add_self hk
    rw [hbSg_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hx] at hgx; rw [hbSg_eq hU hk1 hy] at hgy
    exact (hbSD Bp U0 k).g_add Z hZ hωZ x y hk hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hy
    have hy' : y < (hbSD Bp U0 k).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hk
    rw [hbSg_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hy'] at hg
    exact (hbSD Bp U0 k).g_opow Z hZw hωZ y hk hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hcB
    rw [hbSg_eq hU hk1 hk]
    exact (hbSD Bp U0 k).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hbS_B_lt_Z hU hk1).le.trans h)) c hc hk
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    have hc' : c < (hbSD Bp U0 k).B := (lt_add_one c).trans hk
    rw [hbSg_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hc'] at hg
    exact (hbSD Bp U0 k).g_succ Z hZ c hk hg
  g_le_succ := hbSg_le_succ hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSg_eq hU hk1 hk] at hg
    exact (hbSD Bp U0 k).mem S a b ha c hk hg
  R_zero := fun x => by rw [hbSR_eq hU hbS_zero_lt2 (hbSD Bp U0 0).B_pos]; exact (hbSD Bp U0 0).R_zero x
  R_nat := fun k x => by
    rw [hbSR_eq hU hbS_zero_lt2 ((hbSD Bp U0 0).nat_lt_B k)]; exact (hbSD Bp U0 0).R_nat k x
  R_E := fun x => by rw [hbSR_eq hU hbS_zero_lt2 (hbSD Bp U0 0).E_lt_B]; exact (hbSD Bp U0 0).R_E x
  R_succ := hbSR_succ hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSR_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hk] at hg
    exact (hbSD Bp U0 k).R_pos x hx hx1 c hc0 hk hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSR_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hk] at hg
    exact (hbSD Bp U0 k).R_omega x hx hx1 c hω hk hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSR_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hk] at hg
    have h := hbS_R_lt hU hk1 hk hx hx1 hg
    rwa [Bp.Zst_eq hγx] at h
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSR_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hk] at hg
    have h := hbS_R_lt hU hk1 hk hx hx1 hg
    show _ < hbSUZ Bp x
    unfold hbSUZ
    split_ifs with hγ
    · rw [Bp.Zst_eq hγ] at h; exact h.trans (lt_evZ _)
    · rwa [Bp.Zst_low hγ] at h
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    have hd : d < (hbSD Bp U0 k).B := hdc.trans hk
    rw [hbSR_eq hU hk1 hk, hbSR_eq hU hk1 hd]; rw [hbSg_eq hU hk1 hk] at hgc; rw [hbSg_eq hU hk1 hd] at hgd
    exact (hbSD Bp U0 k).mono x hx hx1 c hk d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSR_eq hU hk1 hk] at hν; rw [hbSg_eq hU hk1 hk] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hbSD Bp U0 k).cof x hx hx1 c hk hg ν hν
    have hd : d < (hbSD Bp U0 k).B := hdc.trans hk
    exact ⟨d, hdc, by rw [hbSg_eq hU hk1 hd]; exact hgd, by rw [hbSR_eq hU hk1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hbSRR_cof hU hx hx1 hγx hν
    have hkZ : hbST Bp k < evZ Bp.Q := hbST_lt Bp k
    have hkB : hbST Bp k < (hbSD Bp U0 (hbST Bp k)).B := hbS_self hU hkZ
    refine ⟨hbST Bp k, hkZ, ?_, ?_⟩
    · rw [hbSg_eq hU hkZ hkB]; exact hbSRR_g hU hx hx1 hγx k
    · rw [hbSR_eq hU hkZ hkB]; exact hk
  b_E := fun x _ _ _ => evZ_E _
  x_lt_b := fun x hx hx1 hγx => Bp.evP_gt hx hx1 hγx
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (epsilon_evZ _) (Bp.evP_gt hx hx1 hγx) (Bp.evP_lt hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => Bp.evP_lt hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hbSUZ Bp x
    unfold hbSUZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ (evZ (Bp.P x)))
  b_pi := fun _ _ hB hγ => Bp.evP_pi hB hγ
  ba_pi := fun _ _ hB hγ => Bp.evP_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    rw [hbSR_eq hU hk1 hk, hbSR_eq hU hk1 hk]; rw [hbSg_eq hU hk1 hk] at hg
    exact (hbSD Bp U0 k).ex σ ρ hB c hk hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := hbS_small hU hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hbSR_eq hU hμ hdμ, hbSR_eq hU hμ hdμ]; rw [hbSg_eq hU hμ hdμ] at hg
    exact (hbSD Bp U0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hbS_b_lt hU hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨k, hk1, hk⟩ := hbS_memB hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hbSD Bp U0 k).ld c hl hk
    have hcpn : cp < (hbSD Bp U0 k).B := hcp.trans hk
    refine ⟨cp, lp, T, hcp, by rw [hbSg_eq hU hk1 hk, hbSg_eq hU hk1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hbSg_eq hU hk1 hk]; exact hg)⟩
    rw [hbSg_eq hU hk1 hk] at hg
    rw [hbSR_eq hU hk1 hk, hbSR_eq hU hk1 hcpn]
    exact hdec x hx hx1 hg

theorem hbSU_B : (hbSU hU).B = evZ Bp.Q := rfl

theorem hbSU_Z (x : Ordinal.{0}) : (hbSU hU).Z x = hbSUZ Bp x := rfl

theorem hbSU_γ : (hbSU hU).γ = Bp.γP := rfl

theorem hbSU_b (x : Ordinal.{0}) : (hbSU hU).b x = evZ (Bp.P x) := rfl

/-- **The union extends every `hbSD Bp U0 ν`, `ν < evZ(Q)`** (readings). -/
theorem hbSU_R {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hbSD Bp U0 ν).B) (x : Ordinal.{0}) :
    (hbSU hU).R c x = (hbSD Bp U0 ν).R c x := hbSR_eq hU hν hc x

/-- **The union extends every `hbSD Bp U0 ν`, `ν < evZ(Q)`** (gates). -/
theorem hbSU_g {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hbSD Bp U0 ν).B) :
    (hbSU hU).g c = (hbSD Bp U0 ν).g c := hbSg_eq hU hν hc

/-- **A code `c ∈ [Q, evZ(Q))` of the union with gate below a base `σ` forces its base gate below `σ`.** -/
theorem hbSU_high_gate {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hQc : Bp.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hbSU hU).g c < σ) : (hbSU hU).γ < σ := hbS_high_gate hU hc hQc hσ hσ1 hg

/-- **THE UNION AT `evZ(Q)` STARTS THE NEXT STAGE** `Bp'` (`Q' = evZ(Q)`, the same gate at every base,
`P'(x) = evZ(P(x))` above it). -/
theorem hbSU_start (Bp' : HbPB) (hQ : Bp'.Q = evZ Bp.Q)
    (hγ : ∀ x, InE x → x < Om1 → (Bp.γP < x ↔ Bp'.γP < x))
    (hP : ∀ x, InE x → x < Om1 → Bp'.γP < x → Bp'.P x = evZ (Bp.P x))
    (hZl : ∀ x, InE x → x < Om1 → ¬ Bp.γP < x → Bp'.Zl x = Bp.Zl x) : HbSStart Bp' (hbSU hU) where
  ix := hQ.symm
  γ := fun x hx hx1 => hγ x hx hx1
  b := fun x hx hx1 h => (hP x hx hx1 h).symm
  Z := fun x hx hx1 => by
    show hbSUZ Bp x = Bp'.Zst x
    unfold hbSUZ HbPB.Zst
    by_cases h : Bp.γP < x
    · rw [if_pos h, if_pos ((hγ x hx hx1).1 h), hP x hx hx1 ((hγ x hx hx1).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hγ x hx hx1).2 h')), hZl x hx hx1 h]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hb
