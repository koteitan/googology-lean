import Googology.Trans.PoR.InaccPsi.R2.XtLim

/-!
# Two term systems: when the larger one contains the top of the smaller one

For term systems `X`, `Y` (`R2.XtGen`) such that the top of `Y` has an IMG package (`XtTopPkg Y`) and `X` has a term
`t` with `t(x) = top_Y(x)` (constants below every `υ`-point) and `top_Y(ρ) + 1 < top_X(ρ)` (`LyTopIn X Y`):

* `lyLeSucc` (the offset of `X` is at most `t(ρ) + 1` where it is at most `t(ρ_μ)` below);
* `lyLamGt` (**`Λ⁺(Y) < Λ(X)`**), `lyEq` (**`O_X = O_Y` below `Λ⁺(Y)`**), `lyAtB1` (**`O_X(Λ⁺(Y)) = top_Y(ρ) + 1`**);
* `lyLamLtB1` (`Λ(X) < Λ⁺(X)` when the top of `X` has an IMG package), `lyB1_ri`, `lyB1_lt`
  (**`Λ⁺(Y) < Λ⁺(X)`**), `lyReachB1` (**`lh(ρ_{Λ⁺(Y)}) = δ + top_Y(ρ) + 1`**);
* `lyGap` (`T(x)·x^a + 1 < T(x)·x^b` for `a < b`, the gap condition for layers).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- `X` contains the top of `Y` as a term, with a gap of more than `1`. -/
def LyTopIn (X Y : XtSys) : Prop :=
  ∃ t : X.Tm, (∀ x, UpsPt x → x < Om1 → X.CB t x ∧ X.val t x = Y.top x) ∧
    ∀ l, IsRestartIdx l → l < Om1 → Y.top (upsilon l) + 1 < X.top (upsilon l)

variable {X Y : XtSys}

/-- The offset is at most `t(ρ) + 1` when it is at most `t(ρ_μ)` below. -/
theorem lyLeSucc (t : X.Tm) (ht : ∀ x, UpsPt x → x < Om1 → X.CB t x) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl1 : l < Om1) (hbd : ∀ μ, IsRestartIdx μ → μ < l → xtOrec X μ ≤ X.val t (upsilon μ)) :
    xtOrec X l ≤ X.val t (upsilon l) + 1 := by
  refine xtOrec_le_of le_add_self (fun s hCB hc => ?_)
  obtain ⟨μ, hμ, -, hμl, hCBμ, hsμ⟩ := hc 0 (pos_iff_ne_zero.2 hl.1)
  have h1 : X.val s (upsilon μ) ≤ X.val t (upsilon μ) := hsμ.trans (hbd μ hμ hμl)
  have h2 := (X.uni_le _ _ (ups_ri hμ) (ups_ri hl) (bases_ri hμ hl hμl hl1) s t hCBμ
    (ht _ (ups_ri hμ) (ups_lt_Om1 μ (hμl.trans hl1)))).2 h1
  exact Order.lt_add_one_iff.2 h2

theorem lyEqMin (hP : XtTopPkg Y) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < xtB1 Y)
    (h2 : μ < xtLam X) : xtOrec X μ = xtOrec Y μ :=
  xt_off_eq xtSpecLam (xtSpec1 hP) hμ h2 h1

/-- **`Λ⁺(Y) < Λ(X)`.** -/
theorem lyLamGt (hP : XtTopPkg Y) (hE : LyTopIn X Y) : xtB1 Y < xtLam X := by
  obtain ⟨t, ht, hgap⟩ := hE
  by_contra hle
  push Not at hle
  have hL := xtLam_ri (X := X)
  have hL1 := xtLam_lt_Om1 (X := X)
  set Λ' := xtLam X with hΛ'
  have hbd : ∀ μ, IsRestartIdx μ → μ < Λ' → xtOrec X μ ≤ X.val t (upsilon μ) := fun μ hμ hμL => by
    rw [lyEqMin hP hμ (hμL.trans_le hle) hμL, (ht _ (ups_ri hμ) (ups_lt_Om1 μ (hμL.trans hL1))).2]
    exact xtOrec_le_top hμ (hμL.trans hL1)
  have h1 := lyLeSucc t (fun x hx hx1 => (ht x hx hx1).1) hL hL1 hbd
  rw [xtOrec_Lam, (ht _ (ups_ri hL) (ups_lt_Om1 Λ' hL1)).2] at h1
  exact absurd h1 (not_le.2 (hgap Λ' hL hL1))

/-- **`O_X = O_Y` below `Λ⁺(Y)`.** -/
theorem lyEq (hP : XtTopPkg Y) (hE : LyTopIn X Y) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ)
    (h1 : μ < xtB1 Y) : xtOrec X μ = xtOrec Y μ :=
  lyEqMin hP hμ h1 (h1.trans (lyLamGt hP hE))

theorem lyB1_ri (hP : XtTopPkg Y) : IsRestartIdx (xtB1 Y) :=
  ri_iff.2 ⟨(xtB1_spec hP).1.ne', xtB1_mult hP⟩

/-- **`O_X(Λ⁺(Y)) = top_Y(ρ) + 1`.** -/
theorem lyAtB1 (hP : XtTopPkg Y) (hE : LyTopIn X Y) :
    xtOrec X (xtB1 Y) = Y.top (upsilon (xtB1 Y)) + 1 := by
  obtain ⟨t, ht, hgap⟩ := hE
  have hl := lyB1_ri hP
  have hl1 := xtB1_lt_Om1 hP
  have hE : LyTopIn X Y := ⟨t, ht, hgap⟩
  refine le_antisymm ?_ ?_
  · have := lyLeSucc t (fun x hx hx1 => (ht x hx hx1).1) hl hl1 fun μ hμ hμl => by
      rw [lyEq hP hE hμ hμl, (ht _ (ups_ri hμ) (ups_lt_Om1 μ (hμl.trans hl1))).2]
      exact xtOrec_le_top hμ (hμl.trans hl1)
    rwa [(ht _ (ups_ri hl) (ups_lt_Om1 _ hl1)).2] at this
  · have hc : XtCof X (xtOrec X) (xtB1 Y) t := by
      intro ν hν
      obtain ⟨μ, ⟨hμ, hfr⟩, h1, h2⟩ := (xtB1_spec hP).2 ν hν
      have hμ1 : upsilon μ < Om1 := ups_lt_Om1 μ (h2.trans hl1)
      refine ⟨μ, hμ, h1, h2, (ht _ (ups_ri hμ) hμ1).1, ?_⟩
      rw [(ht _ (ups_ri hμ) hμ1).2, lyEq hP hE hμ h2, hfr]
    have := lt_xtOrec_of_cof hl hl1 (ht _ (ups_ri hl) (ups_lt_Om1 _ hl1)).1 hc
    rw [(ht _ (ups_ri hl) (ups_lt_Om1 _ hl1)).2] at this
    exact Order.add_one_le_of_lt this

/-- **`Λ(X) < Λ⁺(X)`** when the top of `X` has an IMG package. -/
theorem lyLamLtB1 (hP : XtTopPkg X) : xtLam X < xtB1 X := by
  obtain ⟨h0, hc⟩ := xtB1_spec hP
  obtain ⟨μ, ⟨hμ, hfr⟩, -, hμB⟩ := hc 0 h0
  exact (xtLam_le hμ hfr).trans_lt hμB

/-- **`Λ⁺(Y) < Λ⁺(X)`.** -/
theorem lyB1_lt (hPX : XtTopPkg X) (hP : XtTopPkg Y) (hE : LyTopIn X Y) : xtB1 Y < xtB1 X :=
  (lyLamGt hP hE).trans (lyLamLtB1 hPX)

/-- **The reach at `Λ⁺(Y)`**: `lh(ρ) = δ + top_Y(ρ) + 1`. -/
theorem lyReachB1 (hPX : XtTopPkg X) (hP : XtTopPkg Y) (hE : LyTopIn X Y) :
    IsReach R2C (upsilon (xtB1 Y)) (upsilon (xtB1 Y + ω + 1) + (Y.top (upsilon (xtB1 Y)) + 1)) := by
  rw [← lyAtB1 hP hE]
  exact xtReach1 hPX (lyB1_ri hP) (lyB1_lt hPX hP hE)

/-- **The gap between two powers of a layer**: `T(x)·x^a + 1 < T(x)·x^b` for `a < b`. -/
theorem lyGap (L : XtLay) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {a b : Ordinal.{0}} (hab : a < b) :
    L.sys.top x * x ^ a + 1 < L.sys.top x * x ^ b := by
  have h1x : 1 < x := one_lt_omega0.trans (omega0_lt_inE hx)
  set P := L.sys.top x * x ^ a with hP
  have hxT : x < L.sys.top x := L.top_gt x hx hx1
  have h1P : 1 < P := (h1x.trans hxT).trans_le (le_mul_left _ (opow_pos _ (zero_lt_one.trans h1x)))
  have h2x : (2 : Ordinal.{0}) ≤ x := by
    have := Order.add_one_le_of_lt h1x; rwa [one_add_one_eq_two] at this
  calc P + 1 < P + P := (add_lt_add_iff_left _).2 h1P
    _ = P * 2 := (Ordinal.mul_two _).symm
    _ ≤ P * x := mul_le_mul_right h2x _
    _ = L.sys.top x * x ^ (a + 1) := by rw [hP, opow_add_one, mul_assoc]
    _ ≤ L.sys.top x * x ^ b :=
        mul_le_mul_right (opow_le_opow_right (zero_lt_one.trans h1x) (Order.add_one_le_of_lt hab)) _

end Googology.Trans.PoR.InaccPsi.R2.Ly
