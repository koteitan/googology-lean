import Googology.Trans.PoR.InaccPsi.R2.HcSRec

/-!
# HcSU: THE SELF-READ UNION AT `evZ(Q)` OF A GATED STAGE

(Textual copy of `Hb.HbSU` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

`Ha.haSU` (a textual copy) for `Hc.HcVD` and a stage `Bp : Hb.HcPB`: the union of all `hcSD Bp U0 d`, `d <
evZ(Q)`, has the bound `evZ(Q)`, base
gate `γ_P`, base reading `evZ(P(x))`, bound field `evZ(evZ(P(x)))` above `γ_P` and `Z_l(x)` below.  Codes `c ≥ Q` with
gate below a base `σ` force `γ_P < σ` (`hcS_high_gate`); the tower systems have base gate below every base above
`γ_P` (`hcST_gate`); the union starts the next stage (`hcSU_start`).

* `hcSN`, `hcSR`, `hcSg`, `hcS_small`, `hcS_high_gate`, `hcST`, `hcST_lt`, `hcST_sup`, `hcST_B`, `hcST_gate`,
  `hcST_K`, `hcSRR`, `hcSRR_succ`, `hcSRR_cof`, `hcSU` (**THE UNION AT `evZ(Q)`**), `hcSU_B`, `hcSU_Z`, `hcSU_γ`,
  `hcSU_b`, `hcSU_R`, `hcSU_g`, `hcSU_start` (**IT STARTS THE NEXT STAGE**).

No new axiom.  New definitions: `hcSN`, `hcSR`, `hcSg`, `hcST`, `hcSRR`, `hcSU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb

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

variable (Bp : HcPB) (U0 : HcVD)

/-- The first system `hcSD Bp U0 ν` containing `c`. -/
noncomputable def hcSN (c : Ordinal.{0}) : Ordinal.{0} := sInf {ν | ν < evZ Bp.Q ∧ c < (hcSD Bp U0 ν).B}

/-- The reading of the union. -/
noncomputable def hcSR (c x : Ordinal.{0}) : Ordinal.{0} := (hcSD Bp U0 (hcSN Bp U0 c)).R c x

/-- The gate of the union. -/
noncomputable def hcSg (c : Ordinal.{0}) : Ordinal.{0} := (hcSD Bp U0 (hcSN Bp U0 c)).g c

/-- **The tower of the stage**: `t_0 = 1`, `t_{k+1} = φ(1, Q + t_k)`. -/
noncomputable def hcST : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (Bp.Q + hcST k)

/-- **The reading of the tower code `t_k`** at the base `x` (in `hcSD Bp U0 t_k`). -/
noncomputable def hcSRR (k : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := (hcSD Bp U0 (hcST Bp k)).R (hcST Bp k) x

theorem hcST_lt : ∀ k : ℕ, hcST Bp k < evZ Bp.Q
  | 0 => one_lt_omega0.trans (omega0_lt_inE (evZ_E _))
  | k + 1 => gzq_veb_lt_Z (hcST_lt k)

theorem hcST_pos : ∀ k : ℕ, 0 < hcST Bp k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (Bp.Q + hcST Bp k))

theorem hcST_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.Q + 1) ≤ Bp.Q + hcST Bp k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ Bp.Q + veblen 1 (Bp.Q + hcST Bp k)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `evZ(Q)`.** -/
theorem hcST_sup {t : Ordinal.{0}} (ht : t < evZ Bp.Q) : ∃ k : ℕ, t < hcST Bp k := by
  have ht' : t < evZ (Bp.Q) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  refine ⟨k + 1, (hk.trans_le (hcST_iter Bp k)).trans ?_⟩
  exact gzq_lt_veb Bp.Q_fix (hcST_pos Bp k) (hcST_lt Bp k)

theorem hcSRR_zero (x : Ordinal.{0}) : hcSRR Bp U0 0 x = 1 := (hcSD Bp U0 1).R_one x

end Def

section Union

variable {Bp : HcPB} {U0 : HcVD} (hU : HcSStart Bp U0)
include hU

theorem hcS_memB {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : ∃ ν, ν < evZ Bp.Q ∧ c < (hcSD Bp U0 ν).B :=
  ⟨c, hc, hcS_self hU hc⟩

omit hU in
theorem hcSN_spec {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hcSD Bp U0 ν).B) :
    hcSN Bp U0 c ≤ ν ∧ hcSN Bp U0 c < evZ Bp.Q ∧ c < (hcSD Bp U0 (hcSN Bp U0 c)).B := by
  have hne : ({ν | ν < evZ Bp.Q ∧ c < (hcSD Bp U0 ν).B} : Set Ordinal.{0}).Nonempty := ⟨ν, hν, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hν, hc⟩, hm.1, hm.2⟩

omit hU in
theorem hcSN_min {c μ : Ordinal.{0}} (hμ : μ < hcSN Bp U0 c) (hμl : μ < evZ Bp.Q) : ¬ c < (hcSD Bp U0 μ).B :=
  fun hcμ => absurd (csInf_le' ⟨hμl, hcμ⟩ : hcSN Bp U0 c ≤ μ) (not_le.2 hμ)

theorem hcS_B_lt_Z {c : Ordinal.{0}} (hc : c < evZ Bp.Q) : (hcSD Bp U0 c).B < evZ Bp.Q := by
  rw [hcS_B hU hc]; exact gzq_veb_lt_Z hc

theorem hcSN_high {c : Ordinal.{0}} (hc : evZ Bp.Q ≤ c) : hcSN Bp U0 c = 0 := by
  unfold hcSN
  have he : ({ν | ν < evZ Bp.Q ∧ c < (hcSD Bp U0 ν).B} : Set Ordinal.{0}) = ∅ := by
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hν hcν
    exact absurd (hcν.trans (hcS_B_lt_Z hU hν)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hcSR_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hcSD Bp U0 ν).B) (x : Ordinal.{0}) :
    hcSR Bp U0 c x = (hcSD Bp U0 ν).R c x := by
  obtain ⟨h1, -, h3⟩ := hcSN_spec hν hc
  exact ((hcS_ext hU h1 hν).1 c x h3).symm

theorem hcSg_eq {c ν : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hcSD Bp U0 ν).B) :
    hcSg Bp U0 c = (hcSD Bp U0 ν).g c := by
  obtain ⟨h1, -, h3⟩ := hcSN_spec hν hc
  exact ((hcS_ext hU h1 hν).2 c h3).symm

omit hU in
theorem hcS_lim2 : IsSuccLimit (evZ Bp.Q) := ev_isSuccLimit_of_inE (evZ_E _)

theorem hcSR_succ (c x : Ordinal.{0}) : hcSR Bp U0 (c + 1) x = hcSR Bp U0 c x + 1 := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (hcS_lim2 (Bp := Bp)).add_one_lt h
    rw [hcSR_eq hU h1 (hcS_self hU h1), hcSR_eq hU h1 ((lt_add_one c).trans (hcS_self hU h1)),
      (hcSD Bp U0 (c + 1)).R_succ]
  · unfold hcSR
    rw [hcSN_high hU h, hcSN_high hU (h.trans (le_self_add (a := c) (b := 1))), (hcSD Bp U0 0).R_succ]

theorem hcSg_le_succ (c : Ordinal.{0}) : hcSg Bp U0 c ≤ hcSg Bp U0 (c + 1) := by
  rcases lt_or_ge c (evZ Bp.Q) with h | h
  · have h1 : c + 1 < evZ Bp.Q := (hcS_lim2 (Bp := Bp)).add_one_lt h
    rw [hcSg_eq hU h1 (hcS_self hU h1), hcSg_eq hU h1 ((lt_add_one c).trans (hcS_self hU h1))]
    exact (hcSD Bp U0 (c + 1)).g_le_succ c
  · unfold hcSg
    rw [hcSN_high hU h, hcSN_high hU (h.trans (le_self_add (a := c) (b := 1)))]
    exact (hcSD Bp U0 0).g_le_succ c

omit hU in
theorem hcS_zero_lt2 : (0 : Ordinal.{0}) < evZ Bp.Q := (evZ_E _).pos

/-- **A code of the union with gate below an `ε`-number `σ > γ_P` lies in a member with base gate below `σ`.** -/
theorem hcS_small {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hσ : InE σ) (hσ1 : σ < Om1) (hγσ : Bp.γP < σ)
    (hg : hcSg Bp U0 c < σ) : ∃ μ, μ < evZ Bp.Q ∧ c < (hcSD Bp U0 μ).B ∧ (hcSD Bp U0 μ).γ < σ := by
  obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := hcSN_spec hk1 hk
  have hgN : hcSg Bp U0 c = (hcSD Bp U0 (hcSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (hcSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · refine ⟨hcSN Bp U0 c, hN1, hcN, ?_⟩
    rw [h0, hcSD_zero]; exact (hU.γ σ hσ hσ1).2 hγσ
  · have hm' : hcSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hcSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (hcSD Bp U0 m).B ≤ c := not_lt.1 (hcSN_min hmN hml)
    have hs : hcSD Bp U0 (hcSN Bp U0 c) = (hcSD Bp U0 m).step := by rw [hm']; exact hcSD_succ Bp U0 m
    refine ⟨hcSN Bp U0 c, hN1, hcN, ?_⟩
    rw [hgN, hs] at hg
    rw [hs]
    exact ((hcSD Bp U0 m).γ_le_sG hBc).trans_lt hg
  · exfalso
    rw [hcS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine hcSN_min hd hdl ?_
    rw [hcS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-- **A code `c ∈ [Q, evZ(Q))` of the union with gate below an `ε`-number `σ` forces `γ_P < σ`.** -/
theorem hcS_high_gate {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hQc : Bp.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : hcSg Bp U0 c < σ) : Bp.γP < σ := by
  obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
  obtain ⟨-, hN1, hcN⟩ := hcSN_spec hk1 hk
  have hgN : hcSg Bp U0 c = (hcSD Bp U0 (hcSN Bp U0 c)).g c := rfl
  rcases zero_or_succ_or_isSuccLimit (hcSN Bp U0 c) with h0 | ⟨m, hm⟩ | hlim
  · exfalso
    rw [h0, hcS_B hU hcS_zero_lt2, add_zero, Bp.Q_fix] at hcN
    exact absurd hQc (not_le.2 hcN)
  · have hm' : hcSN Bp U0 c = m + 1 := by rw [← hm, Order.succ_eq_add_one]
    have hmN : m < hcSN Bp U0 c := by rw [hm']; exact lt_add_one m
    have hml : m < evZ Bp.Q := hmN.trans hN1
    have hBc : (hcSD Bp U0 m).B ≤ c := not_lt.1 (hcSN_min hmN hml)
    have hs : hcSD Bp U0 (hcSN Bp U0 c) = (hcSD Bp U0 m).step := by rw [hm']; exact hcSD_succ Bp U0 m
    rw [hgN, hs] at hg
    have hγm : (hcSD Bp U0 m).γ < σ := ((hcSD Bp U0 m).γ_le_sG hBc).trans_lt hg
    exact (max_lt_iff.1 ((hcS_γ_iff hU hml hσ hσ1).1 hγm)).1
  · exfalso
    rw [hcS_B hU hN1] at hcN
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hcN
    obtain ⟨d, hd, htd⟩ := (lt_add_iff hlim.bot_lt.ne').1 ht
    have hdl : d < evZ Bp.Q := hd.trans hN1
    refine hcSN_min hd hdl ?_
    rw [hcS_B hU hdl]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)

/-! ## The tower readings -/

theorem hcST_B (k : ℕ) : (hcSD Bp U0 (hcST Bp k)).B = hcST Bp (k + 1) := hcS_B hU (hcST_lt Bp k)

omit hU in
theorem hcS_one_eq : hcSD Bp U0 1 = U0.step := by
  have h := hcSD_succ Bp U0 0
  rw [zero_add, hcSD_zero] at h
  exact h

/-- **Every `hcSD Bp U0 t_k` has base gate below every `ε`-number base above `γ_P`.** -/
theorem hcST_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → Bp.γP < x → (hcSD Bp U0 (hcST Bp k)).γ < x
  | 0, x, hx, hx1, hγ => by
    show (hcSD Bp U0 1).γ < x
    rw [hcS_one_eq, HcVD.step_γ]; exact (hU.γ x hx hx1).2 hγ
  | k + 1, x, hx, hx1, hγ => by
    set a := hcST Bp k with ha
    have haZ : a < evZ Bp.Q := hcST_lt Bp k
    have hμ : hcST Bp (k + 1) = (hcSD Bp U0 a).B := (hcST_B hU k).symm
    have hμZ : hcST Bp (k + 1) < evZ Bp.Q := hcST_lt Bp (k + 1)
    have ha1 : a + 1 ≤ hcST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact hcS_self hU haZ)
    have ha1Z : a + 1 < evZ Bp.Q := (hcS_lim2 (Bp := Bp)).add_one_lt haZ
    have hμB : hcST Bp (k + 1) < (hcSD Bp U0 (a + 1)).B := by
      rw [hcS_B hU ha1Z]
      show veblen 1 (Bp.Q + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [hcS_γ_iff hU hμZ hx hx1, (hcS_ext hU ha1 hμZ).2 _ hμB, hcSD_succ]
    show max Bp.γP ((hcSD Bp U0 a).step.g (hcST Bp (k + 1))) < x
    rw [hμ, HcVD.step_g_B]
    exact max_lt hγ (hcST_gate k x hx hx1 hγ)

theorem hcST_K (S : InaccSeq.{0}) (hK : Bp.γP < Td.tdK S) (k : ℕ) : (hcSD Bp U0 (hcST Bp k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact hcST_gate hU k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1 hK

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Bp.γP < x)
include hx hx1 hγ

theorem hcSRR_g (k : ℕ) : (hcSD Bp U0 (hcST Bp k)).g (hcST Bp k) < x :=
  (max_lt_iff.1 ((hcS_γ_iff hU (hcST_lt Bp k) hx hx1).1 (hcST_gate hU k x hx hx1 hγ))).2

/-- **`r_{k+1} = φ(1, P(x) + r_k)`.** -/
theorem hcSRR_succ (k : ℕ) : hcSRR Bp U0 (k + 1) x = veblen 1 (Bp.P x + hcSRR Bp U0 k x) := by
  set a := hcST Bp k with ha
  have haZ : a < evZ Bp.Q := hcST_lt Bp k
  have hμ : hcST Bp (k + 1) = (hcSD Bp U0 a).B := (hcST_B hU k).symm
  have hμZ : hcST Bp (k + 1) < evZ Bp.Q := hcST_lt Bp (k + 1)
  have ha1 : a + 1 ≤ hcST Bp (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact hcS_self hU haZ)
  have ha1Z : a + 1 < evZ Bp.Q := (hcS_lim2 (Bp := Bp)).add_one_lt haZ
  have hμB : hcST Bp (k + 1) < (hcSD Bp U0 (a + 1)).B := by
    rw [hcS_B hU ha1Z]
    show veblen 1 (Bp.Q + a) < _
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
  have hγa : (hcSD Bp U0 a).γ < x := hcST_gate hU k x hx hx1 hγ
  unfold hcSRR
  rw [(hcS_ext hU ha1 hμZ).1 _ x hμB, hcSD_succ]
  show (hcSD Bp U0 a).step.R (hcST Bp (k + 1)) x = _
  have h1 : (1 : Ordinal.{0}) < (hcSD Bp U0 a).NB := (hcSD Bp U0 a).one_lt_B.trans (hcSD Bp U0 a).B_lt_NB
  have hpow := (hcSD Bp U0 a).hR_pow one_ne_zero h1 x
  rw [opow_one, (hcSD Bp U0 a).hR_one, opow_one] at hpow
  rw [HcVD.step_R, hμ, hpow, hcS_b hU haZ hx hx1 hγa]

theorem hcSRR_iter (k : ℕ) : Ordinal.epsilon^[k] (Bp.P x + 1) ≤ hcSRR Bp U0 (k + 1) x := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, hcSRR_succ hU hx hx1 hγ 0, hcSRR_zero]
    exact right_le_veblen 1 _
  | succ k ih =>
    rw [Function.iterate_succ_apply', hcSRR_succ hU hx hx1 hγ (k + 1)]
    show veblen 1 _ ≤ _
    exact (isNormal_veblen 1).monotone (ih.trans le_add_self)

/-- **The tower readings are cofinal in `evZ(P(x))`.** -/
theorem hcSRR_cof {t : Ordinal.{0}} (ht : t < evZ (Bp.P x)) : ∃ k : ℕ, t < hcSRR Bp U0 k x := by
  have ht' : t < evZ (Bp.P x) := ht
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 ht'
  exact ⟨k + 1, hk.trans_le (hcSRR_iter hU hx hx1 hγ k)⟩

end Base

theorem hcS_b_lt {μ x : Ordinal.{0}} (hμ : μ < evZ Bp.Q) (hx : InE x) (hx1 : x < Om1)
    (hμx : (hcSD Bp U0 μ).γ < x) : (hcSD Bp U0 μ).b x < evZ (Bp.P x) := by
  have hγ : Bp.γP < x := (max_lt_iff.1 ((hcS_γ_iff hU hμ hx hx1).1 hμx)).1
  have h := (hcSD Bp U0 μ).b_Z x hx hx1 hμx
  rw [hcS_Z hU hμ hx hx1, Bp.Zst_eq hγ] at h
  exact (lt_eN _).trans h

theorem hcS_R_lt {k c x : Ordinal.{0}} (hk1 : k < evZ Bp.Q) (hk : c < (hcSD Bp U0 k).B) (hx : InE x)
    (hx1 : x < Om1) (hg : (hcSD Bp U0 k).g c < x) : (hcSD Bp U0 k).R c x < Bp.Zst x := by
  have h := (hcSD Bp U0 k).R_lt_Z x hx hx1 c hk hg
  rw [hcS_Z hU hk1 hx hx1] at h
  exact h

open Classical in
/-- The bound field of the union: `evZ(evZ(P(x)))` above `γ_P`, `Z_l(x)` below. -/
noncomputable def hcSUZ (Bp : HcPB) (x : Ordinal.{0}) : Ordinal.{0} :=
  if Bp.γP < x then evZ (evZ (Bp.P x)) else Bp.Zl x

omit hU in
theorem hcSUZ_fix (x : Ordinal.{0}) : veblen 1 (hcSUZ Bp x) = hcSUZ Bp x := by
  unfold hcSUZ
  split_ifs
  · exact epsilon_evZ _
  · exact Bp.Zl_fix1 x

omit hU in
theorem hcSUZ_Zl (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hcSUZ Bp x ≤ Bp.Zl x := by
  unfold hcSUZ
  split_ifs with h
  · exact (hb_evZ_lt_fix2 (Bp.Zl_fix x) (Bp.evP_Zl hx hx1 h)).le
  · exact le_rfl

omit hU in
theorem hcSUZ_BR (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : hcSUZ Bp x ≤ hcBR x :=
  (hcSUZ_Zl x hx hx1).trans (Bp.Zl_BR x hx hx1)

omit hU in
theorem hcSUZ_ge (x : Ordinal.{0}) : Bp.Zst x ≤ hcSUZ Bp x := by
  unfold hcSUZ HcPB.Zst
  split_ifs
  · exact (lt_evZ _).le
  · exact le_rfl

/-- **THE UNION AT `evZ(Q)`**: bound `evZ(Q)`, base gate `γ_P`, base reading `evZ(P(x))` (its own index), bound field
`evZ(evZ(P(x)))` above `γ_P`. -/
noncomputable def hcSU : HcVD where
  Z := hcSUZ Bp
  Z_fix := fun x _ _ => hcSUZ_fix x
  Z_BR := hcSUZ_BR
  B := evZ Bp.Q
  γ := Bp.γP
  γ_lt := Bp.γP_lt
  γ_cl := fun _ hZ hZ1 h => Bp.evQ_gate hZ hZ1 h
  γ_G := fun h => absurd h ((Bp.G_le_Q.trans_lt (lt_evZ _)).ne')
  R := hcSR Bp U0
  g := hcSg Bp U0
  b := fun x => evZ (Bp.P x)
  ba := fun x => evZ (Bp.P x)
  ix := evZ Bp.Q
  B_E := evZ_E _
  G_le := Bp.G_le_Q.trans (lt_evZ _).le
  B_lt1 := Bp.evQ_lt1
  B_ix := (epsilon_evZ _).symm
  ix_mem := fun S a b ha hb => Bp.evQ_mem S ha hb
  g_lt := fun c hc => by
    rw [hcSg_eq hU hc (hcS_self hU hc)]; exact (hcSD Bp U0 c).g_lt c (hcS_self hU hc)
  g_zero := by rw [hcSg_eq hU hcS_zero_lt2 (hcSD Bp U0 0).B_pos]; exact (hcSD Bp U0 0).g_zero
  g_nat := fun k => by
    rw [hcSg_eq hU hcS_zero_lt2 ((hcSD Bp U0 0).nat_lt_B k)]; exact (hcSD Bp U0 0).g_nat k
  g_E := by rw [hcSg_eq hU hcS_zero_lt2 (hcSD Bp U0 0).E_lt_B]; exact (hcSD Bp U0 0).g_E
  g_lowE := fun c hc => by
    rw [hcSg_eq hU hcS_zero_lt2 (hc.trans (hcSD Bp U0 0).E_lt_B)]; exact (hcSD Bp U0 0).g_lowE c hc
  g_G0 := fun h => by
    rw [hcSg_eq hU h (hcS_self hU h)]; exact (hcSD Bp U0 (gcG 0)).g_G0 (hcS_self hU h)
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hxy
    have hx : x < (hcSD Bp U0 k).B := lt_of_le_of_lt le_self_add hk
    have hy : y < (hcSD Bp U0 k).B := lt_of_le_of_lt le_add_self hk
    rw [hcSg_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hx] at hgx; rw [hcSg_eq hU hk1 hy] at hgy
    exact (hcSD Bp U0 k).g_add Z hZ hωZ x y hk hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hy
    have hy' : y < (hcSD Bp U0 k).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hk
    rw [hcSg_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hy'] at hg
    exact (hcSD Bp U0 k).g_opow Z hZw hωZ y hk hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hcB
    rw [hcSg_eq hU hk1 hk]
    exact (hcSD Bp U0 k).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (hcS_B_lt_Z hU hk1).le.trans h)) c hc hk
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    have hc' : c < (hcSD Bp U0 k).B := (lt_add_one c).trans hk
    rw [hcSg_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hc'] at hg
    exact (hcSD Bp U0 k).g_succ Z hZ c hk hg
  g_le_succ := hcSg_le_succ hU
  mem := fun S a b ha c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSg_eq hU hk1 hk] at hg
    exact (hcSD Bp U0 k).mem S a b ha c hk hg
  R_zero := fun x => by rw [hcSR_eq hU hcS_zero_lt2 (hcSD Bp U0 0).B_pos]; exact (hcSD Bp U0 0).R_zero x
  R_nat := fun k x => by
    rw [hcSR_eq hU hcS_zero_lt2 ((hcSD Bp U0 0).nat_lt_B k)]; exact (hcSD Bp U0 0).R_nat k x
  R_E := fun x => by rw [hcSR_eq hU hcS_zero_lt2 (hcSD Bp U0 0).E_lt_B]; exact (hcSD Bp U0 0).R_E x
  R_succ := hcSR_succ hU
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSR_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hk] at hg
    exact (hcSD Bp U0 k).R_pos x hx hx1 c hc0 hk hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSR_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hk] at hg
    exact (hcSD Bp U0 k).R_omega x hx hx1 c hω hk hg
  R_lt_b := fun x hx hx1 hγx c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSR_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hk] at hg
    have h := hcS_R_lt hU hk1 hk hx hx1 hg
    rwa [Bp.Zst_eq hγx] at h
  R_lt_Z := fun x hx hx1 c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSR_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hk] at hg
    have h := hcS_R_lt hU hk1 hk hx hx1 hg
    show _ < hcSUZ Bp x
    unfold hcSUZ
    split_ifs with hγ
    · rw [Bp.Zst_eq hγ] at h; exact h.trans (lt_evZ _)
    · rwa [Bp.Zst_low hγ] at h
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    have hd : d < (hcSD Bp U0 k).B := hdc.trans hk
    rw [hcSR_eq hU hk1 hk, hcSR_eq hU hk1 hd]; rw [hcSg_eq hU hk1 hk] at hgc; rw [hcSg_eq hU hk1 hd] at hgd
    exact (hcSD Bp U0 k).mono x hx hx1 c hk d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSR_eq hU hk1 hk] at hν; rw [hcSg_eq hU hk1 hk] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (hcSD Bp U0 k).cof x hx hx1 c hk hg ν hν
    have hd : d < (hcSD Bp U0 k).B := hdc.trans hk
    exact ⟨d, hdc, by rw [hcSg_eq hU hk1 hd]; exact hgd, by rw [hcSR_eq hU hk1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨k, hk⟩ := hcSRR_cof hU hx hx1 hγx hν
    have hkZ : hcST Bp k < evZ Bp.Q := hcST_lt Bp k
    have hkB : hcST Bp k < (hcSD Bp U0 (hcST Bp k)).B := hcS_self hU hkZ
    refine ⟨hcST Bp k, hkZ, ?_, ?_⟩
    · rw [hcSg_eq hU hkZ hkB]; exact hcSRR_g hU hx hx1 hγx k
    · rw [hcSR_eq hU hkZ hkB]; exact hk
  b_E := fun x _ _ _ => evZ_E _
  x_lt_b := fun x hx hx1 hγx => Bp.evP_gt hx hx1 hγx
  b_eN := fun x hx hx1 hγx => gz_eN_fix hx hx1 (epsilon_evZ _) (Bp.evP_gt hx hx1 hγx) (Bp.evP_lt hx hx1 hγx)
  ba_lt := fun x hx hx1 hγx => Bp.evP_lt hx hx1 hγx
  b_Z := fun x _ _ hγx => by
    show _ < hcSUZ Bp x
    unfold hcSUZ; rw [if_pos hγx]
    exact go_eN_lt_evZ (lt_evZ (evZ (Bp.P x)))
  b_pi := fun _ _ hB hγ => Bp.evP_pi hB hγ
  ba_pi := fun _ _ hB hγ => Bp.evP_pi hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    rw [hcSR_eq hU hk1 hk, hcSR_eq hU hk1 hk]; rw [hcSg_eq hU hk1 hk] at hg
    exact (hcSD Bp U0 k).ex σ ρ hB c hk hg
  dig := fun σ ρ hB hγσ d hd hg P P' hat => by
    obtain ⟨μ, hμ, hdμ, hγμ⟩ := hcS_small hU hd hB.1 (hB.2.2.1.trans hB.2.2.2) hγσ hg
    rw [hcSR_eq hU hμ hdμ, hcSR_eq hU hμ hdμ]; rw [hcSg_eq hU hμ hdμ] at hg
    exact (hcSD Bp U0 μ).dig σ ρ hB hγμ d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (hcS_b_lt hU hμ hB.2.1 hB.2.2.2 (hγμ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨k, hk1, hk⟩ := hcS_memB hU hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (hcSD Bp U0 k).ld c hl hk
    have hcpn : cp < (hcSD Bp U0 k).B := hcp.trans hk
    refine ⟨cp, lp, T, hcp, by rw [hcSg_eq hU hk1 hk, hcSg_eq hU hk1 hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← hcSg_eq hU hk1 hk]; exact hg)⟩
    rw [hcSg_eq hU hk1 hk] at hg
    rw [hcSR_eq hU hk1 hk, hcSR_eq hU hk1 hcpn]
    exact hdec x hx hx1 hg

theorem hcSU_B : (hcSU hU).B = evZ Bp.Q := rfl

theorem hcSU_Z (x : Ordinal.{0}) : (hcSU hU).Z x = hcSUZ Bp x := rfl

theorem hcSU_γ : (hcSU hU).γ = Bp.γP := rfl

theorem hcSU_b (x : Ordinal.{0}) : (hcSU hU).b x = evZ (Bp.P x) := rfl

/-- **The union extends every `hcSD Bp U0 ν`, `ν < evZ(Q)`** (readings). -/
theorem hcSU_R {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hcSD Bp U0 ν).B) (x : Ordinal.{0}) :
    (hcSU hU).R c x = (hcSD Bp U0 ν).R c x := hcSR_eq hU hν hc x

/-- **The union extends every `hcSD Bp U0 ν`, `ν < evZ(Q)`** (gates). -/
theorem hcSU_g {ν c : Ordinal.{0}} (hν : ν < evZ Bp.Q) (hc : c < (hcSD Bp U0 ν).B) :
    (hcSU hU).g c = (hcSD Bp U0 ν).g c := hcSg_eq hU hν hc

/-- **A code `c ∈ [Q, evZ(Q))` of the union with gate below a base `σ` forces its base gate below `σ`.** -/
theorem hcSU_high_gate {c σ : Ordinal.{0}} (hc : c < evZ Bp.Q) (hQc : Bp.Q ≤ c) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (hcSU hU).g c < σ) : (hcSU hU).γ < σ := hcS_high_gate hU hc hQc hσ hσ1 hg

/-- **THE UNION AT `evZ(Q)` STARTS THE NEXT STAGE** `Bp'` (`Q' = evZ(Q)`, the same gate at every base,
`P'(x) = evZ(P(x))` above it). -/
theorem hcSU_start (Bp' : HcPB) (hQ : Bp'.Q = evZ Bp.Q)
    (hγ : ∀ x, InE x → x < Om1 → (Bp.γP < x ↔ Bp'.γP < x))
    (hP : ∀ x, InE x → x < Om1 → Bp'.γP < x → Bp'.P x = evZ (Bp.P x))
    (hZl : ∀ x, InE x → x < Om1 → ¬ Bp.γP < x → Bp'.Zl x = Bp.Zl x) : HcSStart Bp' (hcSU hU) where
  ix := hQ.symm
  γ := fun x hx hx1 => hγ x hx hx1
  b := fun x hx hx1 h => (hP x hx hx1 h).symm
  Z := fun x hx hx1 => by
    show hcSUZ Bp x = Bp'.Zst x
    unfold hcSUZ HcPB.Zst
    by_cases h : Bp.γP < x
    · rw [if_pos h, if_pos ((hγ x hx hx1).1 h), hP x hx hx1 ((hγ x hx hx1).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hγ x hx hx1).2 h')), hZl x hx hx1 h]

end Union

end Googology.Trans.PoR.InaccPsi.R2.Hc
