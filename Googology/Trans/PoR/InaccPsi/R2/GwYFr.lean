import Googology.Trans.PoR.InaccPsi.R2.GwYRec

/-!
# THE FRONTIER `ι(Γ(ζ_{G+2}))`

The tower `t'₀ = 1`, `t'_{k+1} = ε_{ζ_{G+1}+t'_k}` (`gwYT`) is cofinal in `ζ_{G+2}` (`gwYT_sup`), every `gwYD t'_k`
has base gate below every `ε`-number (`gwYT_gate`: the gate of the code `t'_{k+1}` is the base gate of `gwYD t'_k`,
by the step; `gwYD 1` is the step of the union at `ζ_{G+1}`, gate `0`).  So the bounds `ε_{ζ_{G+1}+t'_k} = t'_{k+1}`
are located (`Gw.gwZ_locD`) and **the new frontier is `ι(Γ(ζ_{G+2}))`** (was `ι(Γ(ζ_{G+1}))` at the start of the
round's second part, `ι(Γ(ε_{G+Ω₁·ε₀}))` before the round): ENUM-REACH, CapV at every range restart below it, BLK^O and
exact reaches below each located bound, all unconditionally.

* `gwY_loc`, `gwY_loc_enum`, `gwY_loc_capV` (every index `d < ζ_{G+2}` with `γ(gwYD d) < K`);
* `gwYT`, `gwYT_pos`, `gwYT_lt`, `gwYT_B`, `gwYT_gate`, `gwYT_K`, `gwYT_sup`; `gwZ2`, `gwZ2_codes`, `gwZ2_cof`,
  `gwZ2_enum`, `gwZ2_capV`, `gwZ2_blk`, `gwZ2_road` (**THE ROAD**), `gwZ2_le_Om2`, `gwZ2_P`, `gwZ2_fr_order`.

No new axiom.  New definitions: `gwYT`, `gwZ2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
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

/-! ## Every index with gate below `K` -/

section Loc

variable (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < evZ gwZ) (hγ : (gwYD ν).γ < Td.tdK S)
include hν hγ

/-- **`ε_{ζ_{G+1}+d}` IS LOCATED** for every `d < ζ_{G+2}` whose system has base gate below `K`. -/
theorem gwY_loc : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gwZ + ν)) * ω) ∧
    upsilon (xtB1 X) = Pv S (gcG (veblen 1 (gwZ + ν)) * ω) ∧
    Pv S (gcG (veblen 1 (gwZ + ν)) * ω) < Nc.ncL S 0 := by
  rw [← gwY_B hν]; exact gwZ_locD (gwYD ν) S hγ

theorem gwY_loc_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gwZ + ν)) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← gwY_B hν] at hl; exact gwZ_locD_enum (gwYD ν) S hγ hr hl

theorem gwY_loc_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gwZ + ν)) * ω)) :
    CdCapV S l := by
  rw [← gwY_B hν] at hl; exact gwZ_locD_capV (gwYD ν) S hγ hr hl

end Loc

/-! ## The tower `t'₀ = 1`, `t'_{k+1} = ε_{ζ_{G+1}+t'_k}` -/

/-- **The tower above `ζ_{G+1}`**: `t'₀ = 1`, `t'_{k+1} = φ(1, ζ_{G+1} + t'_k)`. -/
noncomputable def gwYT : ℕ → Ordinal.{0}
  | 0 => 1
  | k + 1 => veblen 1 (gwZ + gwYT k)

theorem gwYT_lt : ∀ k : ℕ, gwYT k < evZ gwZ
  | 0 => (one_lt_omega0.trans (omega0_lt_inE (evZ_E _)))
  | k + 1 => gwY_veb_lt_Z (gwYT_lt k)

theorem gwYT_pos : ∀ k : ℕ, 0 < gwYT k
  | 0 => zero_lt_one
  | k + 1 => InE.pos (omega0_opow_epsilon (gwZ + gwYT k))

theorem gwYT_B (k : ℕ) : (gwYD (gwYT k)).B = gwYT (k + 1) := gwY_B (gwYT_lt k)

theorem gwY_one_eq : gwYD 1 = gwZU.step := by
  have h := gwYD_succ 0
  rw [zero_add, gwYD_zero] at h
  exact h

/-- **Every `gwYD t'_k` has base gate below every `ε`-number base.** -/
theorem gwYT_gate : ∀ (k : ℕ) (x : Ordinal.{0}), InE x → x < Om1 → (gwYD (gwYT k)).γ < x
  | 0, x, hx, _ => by
    show (gwYD 1).γ < x
    rw [gwY_one_eq, GwZD.step_γ, gwZU_γ]; exact hx.pos
  | k + 1, x, hx, hx1 => by
    set a := gwYT k with ha
    have haZ : a < evZ gwZ := gwYT_lt k
    have hμ : gwYT (k + 1) = (gwYD a).B := (gwYT_B k).symm
    have hμZ : gwYT (k + 1) < evZ gwZ := gwYT_lt (k + 1)
    have ha1 : a + 1 ≤ gwYT (k + 1) := Order.add_one_le_of_lt (by rw [hμ]; exact gwY_self haZ)
    have ha1Z : a + 1 < evZ gwZ := (ev_isSuccLimit_of_inE (evZ_E _)).add_one_lt haZ
    have hμB : gwYT (k + 1) < (gwYD (a + 1)).B := by
      rw [gwY_B ha1Z]
      show veblen 1 (gwZ + a) < _
      exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one a))
    rw [gwY_γ_iff hμZ hx hx1, (gwY_ext ha1 hμZ).2 _ hμB, gwYD_succ]
    show (gwYD a).step.g (gwYT (k + 1)) < x
    rw [hμ, GwZD.step_g_B]
    exact gwYT_gate k x hx hx1

theorem gwYT_K (S : InaccSeq.{0}) (k : ℕ) : (gwYD (gwYT k)).γ < Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  exact gwYT_gate k _ (Low.opow_eq_self_of_SC Td.tdK_SC) hK1

theorem gwYT_iter (n : ℕ) : Ordinal.epsilon^[n] (gwZ + 1) ≤ gwZ + gwYT n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show veblen 1 _ ≤ gwZ + veblen 1 (gwZ + gwYT n)
    exact ((isNormal_veblen 1).monotone ih).trans le_add_self

/-- **The tower is cofinal in `ζ_{G+2}`.** -/
theorem gwYT_sup {t : Ordinal.{0}} (ht : t < evZ gwZ) : ∃ k : ℕ, t < gwYT k := by
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 ht
  refine ⟨n + 1, (hn.trans_le (gwYT_iter n)).trans ?_⟩
  exact gwY_lt_veb (gwYT_pos n) (gwYT_lt n)

/-! ## The frontier `ι(Γ(ζ_{G+2}))` -/

/-- **The new bound** `ζ_{G+2}`, the least fixed point of `ε` above `ζ_{G+1}`. -/
noncomputable def gwZ2 : Ordinal.{0} := evZ gwZ

theorem gwZ2_lim : IsSuccLimit gwZ2 := ev_isSuccLimit_of_inE (evZ_E _)

theorem gwZ2_codes {c : Ordinal.{0}} (hc : c < gwZ2) : ∃ k : ℕ, c < (gwYD (gwYT k)).B := by
  obtain ⟨k, hk⟩ := gwYT_sup hc
  exact ⟨k, hk.trans (gwY_self (gwYT_lt k))⟩

/-- **`ι(Γ(ζ_{G+2})) = sup_k ι(Γ(t'_{k+1})·ω)`**, below each the code `t'_{k+1}` is located. -/
theorem gwZ2_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gwZ2)) :
    ∃ k : ℕ, l < iota S (gcG (gwYD (gwYT k)).B * ω) := by
  have hlim : IsSuccLimit (gcG gwZ2) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gwZ2)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gwZ2_lim e.2
  obtain ⟨k, hk⟩ := gwZ2_codes hβ
  refine ⟨k, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hk)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(ζ_{G+2}))`, fixed points included** (UNCONDITIONAL). -/
theorem gwZ2_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gwZ2)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, h⟩ := gwZ2_cof S hl
  exact gwZ_locD_enum (gwYD (gwYT k)) S (gwYT_K S k) hr h

/-- **CapV at every range restart below `ι(Γ(ζ_{G+2}))`** (UNCONDITIONAL). -/
theorem gwZ2_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gwZ2)) :
    CdCapV S l := by
  obtain ⟨k, h⟩ := gwZ2_cof S hl
  exact gwZ_locD_capV (gwYD (gwYT k)) S (gwYT_K S k) hr h

/-- **BLK^O and the exact reaches below `P(Γ(t'_{k+1})·ω)` for every `k`** (UNCONDITIONAL). -/
theorem gwZ2_blk (S : InaccSeq.{0}) (k : ℕ) :
    let D := gwYD (gwYT k)
    let X := gsX D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gwZ_locD_g D S (gwYT_K S k))
    xtB1 X = iota S (gcG (gwYT (k + 1)) * ω) ∧
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  intro D X
  refine ⟨?_, gwZ_locD_blk D S (gwYT_K S k)⟩
  have h := (gsLoc D.step.toRS _ D.E_lt_B.le D.B_lt_NB S (gwZ_locD_g D S (gwYT_K S k))).1
  rw [← gwYT_B k]; exact h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ζ_{G+2}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gwZ2_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gwZ2) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gwZ2) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gwZ2) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => gwZ2_enum S hr h) (fun _ hr h => gwZ2_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- **`Γ(ζ_{G+2}) < Ω₂`.** -/
theorem gwZ2_le_Om2 : gcG gwZ2 < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gwZ2 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gwY_Z_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ζ_{G+2})) < L(0)`.** -/
theorem gwZ2_P (S : InaccSeq.{0}) : Pv S (gcG gwZ2) < Nc.ncL S 0 := ga_Pv_lt_L0 S gwZ2_le_Om2.le

theorem gwZw_lt_Z2 : gwZw < gwZ2 := gwY_veb_lt_Z (omega0_lt_inE (evZ_E _))

/-- **The order of the frontiers**: `ι(Γ(ζ_{G+1})) ≤ ι(Γ(ε_{ζ_{G+1}+ω})) ≤ ι(Γ(ζ_{G+2})) ≤ ι(Ω₂)`,
`ι(Γ(t'_{k+1})·ω) ≤ ι(Γ(ζ_{G+2}))` for every `k`, `P(Γ(ζ_{G+2})) ≤ P(Ω₂) < L(0)`. -/
theorem gwZ2_fr_order (S : InaccSeq.{0}) (k : ℕ) :
    gwZ < gwZw ∧ gwZw < gwZ2 ∧ iota S (gcG gwZ) ≤ iota S (gcG gwZw) ∧ iota S (gcG gwZw) ≤ iota S (gcG gwZ2) ∧
      iota S (gcG (gwYT (k + 1)) * ω) ≤ iota S (gcG gwZ2) ∧
      iota S (gcG gwZ2) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gwZ2) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG gwZ2) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hk : gwYT (k + 1) < gwZ2 := gwYT_lt (k + 1)
  have hZw := (gwZw_fr_order S).1
  exact ⟨hZw, gwZw_lt_Z2, iota_mono _ _ (gcG_lt hZw).le, iota_mono _ _ (gcG_lt gwZw_lt_Z2).le,
    iota_mono _ _ (InE.mul_lt hV (gcG_lt hk) (omega0_lt_inE hV)).le,
    iota_mono _ _ gwZ2_le_Om2.le, Nm.Pv_mono gwZ2_le_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gw
