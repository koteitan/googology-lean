import Googology.Trans.PoR.InaccPsi.R2.GvU

/-!
# THE CODE `ε_{G+Ω₁}` IS LOCATED; THE FRONTIER `ι(Γ(ε_{G+Ω₁+ω}))`

`G = Γ_{Ω₁+1}`, `Γ(c) = Γ_{Ω₁+1+c}` (`gcG`), `K = ψ_{Ω₁}(Ω_ω)`, `P = Pv`, `L(0) = Nc.ncL S 0`.  The union
`gvU` (bound `ε_{G+Ω₁}`, base gate `0`, `R2.GvU`) has a step `gvS = gvU.step : Gs.GsD` (bound `ε_{G+Ω₁+1}`, base gate
`0`).  In `gvS` the code `ε_{G+Ω₁}` has gate `0 < K` (`GvD.step_g_B`), so the gated location theorem `Gs.gsLoc`
applies: **`Λ⁺ = ι(Γ(ε_{G+Ω₁})·ω)`, `P(Γ(ε_{G+Ω₁})·ω) < L(0)`**, with BLK^O, the exact reaches, ENUM-REACH and CapV
below it (`gv_locΩ`, `gv_enumΩ`, `gv_capVΩ`, `gv_blkΩ`).  Every constant index `ν ∈ [K, Ω₁)` (the round-90 wall) is
passed: `ε_{G+ν} < ε_{G+Ω₁}`.  The steps `gvIt n` (bounds `ε_{G+Ω₁+1+n}`, gate `0`) give the frontiers
`ι(Γ(ε_{G+Ω₁+1+n}))` and their supremum **`ι(Γ(ε_{G+Ω₁+ω}))`** (`gvW_cof`, `gvW_enum`, `gvW_capV`, `gvW_road`).

* `gvS`, `gvS_B`, `gvS_γ`, `gvS_g_Ω`; `gv_locΩ`, `gv_enumΩ`, `gv_capVΩ`, `gv_blkΩ`;
* `gvIt`, `gvIt_γ`, `gvIt_B`; `gvIt_sup`, `gvIt_enum`, `gvIt_capV`, `gvIt_blk`;
* `gvW`, `gvW_cof`, `gvW_enum`, `gvW_capV`, `gvW_road` (**THE ROAD**), `gvW_le_Om2`, `gvW_P`, `gvW_fr_order`
  (**`ι(Γ(ε_{G+K})) ≤ ι(Γ(ε_{G+Ω₁})) < ι(Γ(ε_{G+Ω₁})·ω) < ι(Γ(ε_{G+Ω₁+1})) ≤ ι(Γ(ε_{G+Ω₁+ω})) ≤ ι(Ω₂)`**).

No new axiom.  New definitions: `gvS`, `gvIt`, `gvW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gv_K_pos (S : InaccSeq.{0}) : (0 : Ordinal.{0}) < Td.tdK S := Td.tdK_SC.1

/-! ## The code `ε_{G+Ω₁}` -/

/-- **The step of the union**: bound `ε_{G+Ω₁+1}`, base gate `0`. -/
noncomputable def gvS : GsD := gvU.step

theorem gvS_B : gvS.B = veblen 1 (gcG 0 + Om1 + 1) := gvU.NB_eq

theorem gvS_γ : gvS.γ = 0 := rfl

/-- **The code `ε_{G+Ω₁}` has gate `0` in `gvS`.** -/
theorem gvS_g_Ω : gvS.g gvU.B = 0 := gvU.step_g_B

theorem gvΩ_lt_S : gvU.B < gvS.B := gvU.B_lt_NB

theorem gvΩ_E : gfE ≤ gvU.B := gvU.E_lt_B.le

section Om

variable (S : InaccSeq.{0})

theorem gvΩ_g : gvS.toRS.K.gt gvU.B < Td.tdK S := by
  rw [GsD.toRS_gt, gvS_g_Ω]; exact gv_K_pos S

/-- **THE CODE `ε_{G+Ω₁}` IS LOCATED**: `Λ⁺(X) = ι(Γ(ε_{G+Ω₁})·ω)`, `υ` of it `= P(Γ(ε_{G+Ω₁})·ω) < L(0)`. -/
theorem gv_locΩ : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gcG 0 + Om1)) * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG (veblen 1 (gcG 0 + Om1)) * ω) ∧
    Pv S (gcG (veblen 1 (gcG 0 + Om1)) * ω) < Nc.ncL S 0 :=
  ⟨gsX gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S), gsX_pkg gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S),
    gsLoc gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S)⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+Ω₁})·ω)`, fixed points included.** -/
theorem gv_enumΩ {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gcG 0 + Om1)) * ω)) :
    CdUpper S l ∧ CdLower S l :=
  gsEnum gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S) hr hl

/-- **CapV at every range restart below `ι(Γ(ε_{G+Ω₁})·ω)`.** -/
theorem gv_capVΩ {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gcG 0 + Om1)) * ω)) :
    CdCapV S l :=
  gsCapV gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S) hr hl

/-- **Theorem BLK^O below `υ_{Λ⁺} = P(Γ(ε_{G+Ω₁})·ω)`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem gv_blkΩ :
    (∀ c' d, c' < d → d < upsilon (xtB1 (gsX gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S))) →
      (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧
        μ < xtB1 (gsX gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S)) ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (gsX gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S)) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l)
        (upsilon (l + ω + 1) + xtOrec (gsX gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S)) l)) ∧
    (∀ α < upsilon (xtB1 (gsX gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S))), ¬ UpsPt α →
      ∀ γ, le1 α γ ↔ le1R α γ) :=
  gsBlk gvS.toRS gvU.B gvΩ_E gvΩ_lt_S S (gvΩ_g S)

end Om

/-! ## The steps `ε_{G+Ω₁+1+n}` -/

/-- **The steps above the union**: `gvIt 0 = gvS`, `gvIt (n+1) = (gvIt n).step`. -/
noncomputable def gvIt : ℕ → GsD
  | 0 => gvS
  | n + 1 => (gvIt n).step

theorem gvIt_γ : ∀ n, (gvIt n).γ = 0
  | 0 => gvS_γ
  | n + 1 => by show (gvIt n).step.γ = 0; rw [GsD.step_γ]; exact gvIt_γ n

theorem gvIt_B : ∀ n : ℕ, (gvIt n).B = veblen 1 (gcG 0 + Om1 + (n + 1 : ℕ))
  | 0 => by rw [Nat.cast_one]; exact gvS_B
  | n + 1 => by
    show (gvIt n).step.B = _
    rw [GsD.step_B, gvIt_B n, go_eN_veb, add_assoc]; push_cast; rfl

theorem gvIt_γK (S : InaccSeq.{0}) (n : ℕ) : (gvIt n).γ < Td.tdK S := by rw [gvIt_γ]; exact gv_K_pos S

/-- **`sup = ι(Γ(ε_{G+Ω₁+1+n}))`, `υ` of it `= P(Γ(ε_{G+Ω₁+1+n})) < L(0)`.** -/
theorem gvIt_sup (S : InaccSeq.{0}) (n : ℕ) :
    ((gvIt n).gsFam S (gvIt_γK S n)).famSup = iota S (gcG (gvIt n).B) ∧
    upsilon ((gvIt n).gsFam S (gvIt_γK S n)).famSup = Pv S (gcG (gvIt n).B) ∧
    Pv S (gcG (gvIt n).B) < Nc.ncL S 0 := (gvIt n).gsFam_sup S (gvIt_γK S n)

theorem gvIt_enum (S : InaccSeq.{0}) (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (gvIt n).B)) : CdUpper S l ∧ CdLower S l :=
  (gvIt n).gsFam_enum S (gvIt_γK S n) hr hl

theorem gvIt_capV (S : InaccSeq.{0}) (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (gvIt n).B)) : CdCapV S l :=
  (gvIt n).gsFam_capV S (gvIt_γK S n) hr hl

/-- **Theorem BLK^O below `P(Γ(ε_{G+Ω₁+1+n}))`**, with the exact reaches. -/
theorem gvIt_blk (S : InaccSeq.{0}) (n : ℕ) :
    (∀ c d, c < d → d < upsilon ((gvIt n).gsFam S (gvIt_γK S n)).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ((gvIt n).gsFam S (gvIt_γK S n)).famSup ∧
        c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < ((gvIt n).gsFam S (gvIt_γK S n)).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + ((gvIt n).gsFam S (gvIt_γK S n)).off k l)) ∧
    (∀ α < upsilon ((gvIt n).gsFam S (gvIt_γK S n)).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (gvIt n).gsFam_blk S (gvIt_γK S n)

/-! ## The frontier `ι(Γ(ε_{G+Ω₁+ω}))` -/

/-- **The new bound** `ε_{G+Ω₁+ω} = φ(1, G + Ω₁ + ω)`. -/
noncomputable def gvW : Ordinal.{0} := veblen 1 (gcG 0 + Om1 + ω)

theorem gvW_lim : IsSuccLimit gvW := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

theorem gvIt_lt_W (n : ℕ) : (gvIt n).B < gvW := by
  rw [gvIt_B]
  refine (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 ?_)
  exact natCast_lt_omega0 _

theorem gvW_codes {c : Ordinal.{0}} (hc : c < gvW) : ∃ n : ℕ, c < (gvIt n).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ isSuccLimit_omega0)).1 hc
  obtain ⟨n, hn⟩ := go_lt_add_omega ht
  refine ⟨n, ?_⟩
  rw [gvIt_B]
  refine hct.trans ((isNormal_veblen 1).strictMono (hn.trans_le ?_))
  exact (add_le_add_iff_left _).2 (by push_cast; exact le_self_add)

/-- **`ι(Γ(ε_{G+Ω₁+ω})) = sup_n ι(Γ(ε_{G+Ω₁+1+n}))`.** -/
theorem gvW_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gvW)) :
    ∃ n : ℕ, l < iota S (gcG (gvIt n).B) := by
  have hlim : IsSuccLimit (gcG gvW) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gvW)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gvW_lim e.2
  obtain ⟨n, hn⟩ := gvW_codes hβ
  exact ⟨n, he.trans_le (iota_mono _ _ (heβ.trans (gcG_lt hn)).le)⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+Ω₁+ω}))`, fixed points included** (UNCONDITIONAL). -/
theorem gvW_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvW)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, h⟩ := gvW_cof S hl
  exact gvIt_enum S n hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+Ω₁+ω}))`** (UNCONDITIONAL). -/
theorem gvW_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gvW)) :
    CdCapV S l := by
  obtain ⟨n, h⟩ := gvW_cof S hl
  exact gvIt_capV S n hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+Ω₁+ω}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gvW_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gvW) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gvW) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gvW) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < iota S (gcG gvW)
    · exact (gvW_enum S hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gvW)
    · exact (gvW_enum S hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gvW)
    · exact gvW_capV S hr h
    · exact hV l hr hω (not_lt.1 h)

/-! ## The place of the frontier -/

theorem gvW_lt_G1 : gvW < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : gcG 0 + Om1 + ω < gcG 1 :=
    (inE_indec hE).add_lt gv_ix_lt (omega0_lt_inE hE)
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+Ω₁+ω}) < Ω₂`.** -/
theorem gvW_le_Om2 : gcG gvW < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gvW < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gvW_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+Ω₁+ω})) < L(0)`.** -/
theorem gvW_P (S : InaccSeq.{0}) : Pv S (gcG gvW) < Nc.ncL S 0 := ga_Pv_lt_L0 S gvW_le_Om2.le

/-- **The order of the frontiers**: `ι(Γ(ε_{G+K})) ≤ ι(Γ(ε_{G+Ω₁})) < ι(Γ(ε_{G+Ω₁})·ω) < ι(Γ(ε_{G+Ω₁+1})) ≤
ι(Γ(ε_{G+Ω₁+ω})) ≤ ι(Ω₂)`, `P(Γ(ε_{G+Ω₁+ω})) ≤ P(Ω₂) < L(0)`; and `ε_{G+K} < ε_{G+Ω₁}`. -/
theorem gvW_fr_order (S : InaccSeq.{0}) :
    gsE S < gvU.B ∧ iota S (gcG (gsE S)) ≤ iota S (gcG gvU.B) ∧ iota S (gcG gvU.B) < iota S (gcG gvU.B * ω) ∧
      iota S (gcG gvU.B * ω) < iota S (gcG gvS.B) ∧ iota S (gcG gvS.B) ≤ iota S (gcG gvW) ∧
      iota S (gcG gvW) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gvW) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  have hEΩ : gsE S < gvU.B :=
    (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hK1)
  have hg0 : gvS.toRS.K.gt gvU.B < Td.tdK S := gvΩ_g S
  have hgoodΩ : Bt.Good S (gcG gvU.B) :=
    gs_good (K := gvS.toRS.K) fun Z _ hKZ => GxCl.atom (gsmG_atom (K := gvS.toRS.K) gvΩ_lt_S (hg0.trans_le hKZ))
  have hgoodΩw : Bt.Good S (gcG gvU.B * ω) := gsGood_mul gvS.toRS gvΩ_lt_S S hg0
  have hG : InE (gcG gvU.B) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hV : InE (gcG gvS.B) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hSW : gvS.B < gvW := gvIt_lt_W 0
  refine ⟨hEΩ, iota_mono _ _ (gcG_lt hEΩ).le,
    cd_iota_lt_of_good hgoodΩ (lt_mul_of_one_lt_right hG.pos one_lt_omega0),
    cd_iota_lt_of_good hgoodΩw (InE.mul_lt hV (gcG_lt gvΩ_lt_S) (omega0_lt_inE hV)),
    iota_mono _ _ (gcG_lt hSW).le, iota_mono _ _ gvW_le_Om2.le, Nm.Pv_mono gvW_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gv
