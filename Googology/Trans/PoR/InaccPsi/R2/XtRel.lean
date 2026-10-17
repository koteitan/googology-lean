import Googology.Trans.PoR.InaccPsi.R2.CpFix
import Googology.Trans.PoR.InaccPsi.R2.XtGen

/-!
# The generic offset above a restart and at an isolated fixed point of `υ`

For every term system `X` (`R2.XtGen`), with `e(x) = cdExp x` the last exponent and `-1 + e = cdOff e`:

* `xtRel` (**`O(λ₀ + z) = -1 + e(z)`** for a restart index `λ₀ < Ω₁`, `0 < z < ρ_{λ₀}`, `ω² ∣ z`): a term realized
  cofinally below `λ₀ + z` takes small values at the restarts of the last window, so it is a constant (`small`);
  every constant `c < -1 + e(z)` is realized there;
* `xtNonfix` (**`O(μ) = -1 + e(μ)`** at every restart index `ω² < μ < Ω₁` with `μ < υ_μ`);
* `xtIso` (**`O(F) = F`** at an isolated fixed point `F = υ_F` of `υ`, `CpIso F`).

These are `R2.CpRel`'s `cpVz_rel`, `R2.CpFix`'s `cpVz_nonfix`, `cpVz_iso` for any term system (there for
`VzOrec`); the proofs are the same, with `small` for `noB`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Cp

variable {X : XtSys}

/-- A realized term with value below the base is a constant. -/
theorem xt_const_of_small {s : X.Tm} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : X.CB s x)
    (hlt : X.val s x < x) : ∀ y, X.val s y = X.val s x := by
  rcases X.small s with h | h
  · exact fun y => h y x
  · exact absurd (h x hx hx1 hc) (not_le.2 hlt)

/-- **The offset above a restart**: `O(λ₀ + z) = -1 + e(z)` for a restart index `λ₀ < Ω₁` and `0 < z < ρ_{λ₀}`
with `ω² ∣ z`. -/
theorem xtRel {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hl01 : l0 < Om1) :
    ∀ z, 0 < z → z < upsilon l0 → ω * ω ∣ z → xtOrec X (l0 + z) = cdOff (cdExp z) := by
  have hρ1 : upsilon l0 < Om1 := ups_lt_Om1 l0 hl01
  have hd0 : ω * ω ∣ l0 := (ri_iff.1 hl0).2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz0 hzρ hzd
  have hz0' : z ≠ 0 := hz0.ne'
  set e := cdExp z with he_def
  have he2 : 2 ≤ e := cp_two_le_exp hz0' hzd
  obtain ⟨z1, hdec, hdz1⟩ := cdExp_decomp hz0'
  rw [← he_def] at hdec hdz1
  set l := l0 + z with hl_def
  have hl : IsRestartIdx l :=
    ri_iff.2 ⟨(lt_of_lt_of_le hz0 le_add_self).ne', dvd_add hd0 hzd⟩
  have hl1 : l < Om1 := Om1_add_lt hl01 (hzρ.trans hρ1)
  have hez : e ≤ z := by
    rw [hdec]; exact (right_le_opow e one_lt_omega0).trans le_add_self
  have hupl : upsilon l0 ≤ upsilon l := upsilon_normal.strictMono.monotone le_self_add
  have hwin : ∀ μ, IsRestartIdx μ → l0 + z1 < μ → μ < l →
      ∃ z', μ = l0 + z' ∧ 0 < z' ∧ z' < z ∧ ω * ω ∣ z' ∧ cdExp z' < e ∧
        xtOrec X μ = cdOff (cdExp z') := by
    intro μ hμ h1 h2
    obtain ⟨z', rfl⟩ := exists_add_of_le (le_self_add.trans h1.le)
    have h1' : z1 < z' := (add_lt_add_iff_left _).1 h1
    have h2' : z' < z := (add_lt_add_iff_left _).1 h2
    have hz'0 : 0 < z' := lt_of_le_of_lt zero_le h1'
    have hz'd : ω * ω ∣ z' := (dvd_add_iff hd0).1 (ri_iff.1 hμ).2
    have hw := cdWin hdz1 h1' (hdec ▸ h2')
    exact ⟨z', rfl, hz'0, h2', hz'd, hw.1, IH z' h2' hz'0 (h2'.trans hzρ) hz'd⟩
  have hνl : l0 + z1 < l := by
    rw [hl_def, hdec, ← add_assoc]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  refine le_antisymm ?_ ?_
  · refine xtOrec_le_of (cpOff_one_le he2) fun s hCB hc => ?_
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc _ hνl
    obtain ⟨z', rfl, hz'0, hz'z, hz'd, hez', hOμ⟩ := hwin μ hμ h1 h2
    have he'2 : 2 ≤ cdExp z' := cp_two_le_exp hz'0.ne' hz'd
    have hlt : X.val s (upsilon (l0 + z')) < cdOff e :=
      (hsμ.trans_eq hOμ).trans_lt (cpOff_lt (one_le_two.trans he'2) hez')
    have hρμ : cdOff e < upsilon (l0 + z') :=
      ((cdOff_le e).trans hez).trans_lt (hzρ.trans_le (upsilon_normal.strictMono.monotone le_self_add))
    rw [xt_const_of_small (ups_inE hμ) (ups_lt_Om1 _ (h2.trans hl1)) hCBμ (hlt.trans hρμ) (upsilon l)]
    exact hlt
  · rcases eq_or_lt_of_le he2 with he | he
    · rw [← he]
      have h2 : cdOff (2 : Ordinal.{0}) = 1 := by
        have := cpOff_nat 2
        simpa using this
      rw [h2]; exact one_le_xtOrec hl hl1
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨a', ha'2, ha'e, hca'⟩ := cpPick he hc
    have hcρ : c < upsilon l0 := (hc.trans_le ((cdOff_le e).trans hez)).trans hzρ
    have hCB : X.CB (X.cst c) (upsilon l) := X.cb_cstI _ _ (hcρ.trans_le hupl)
    have hcof : XtCof X (xtOrec X) l (X.cst c) := by
      intro ν hν
      set ν' := max ν (l0 + z1) with hν'
      have hν'l : ν' < l := max_lt hν hνl
      obtain ⟨w, hw⟩ := exists_add_of_le (le_max_right ν (l0 + z1) : l0 + z1 ≤ ν')
      have hwe : w < ω ^ e := by
        have : l0 + z1 + w < l0 + z1 + ω ^ e := by
          rw [← hw, add_assoc, ← hdec]; exact hν'l
        exact (add_lt_add_iff_left _).1 this
      have hpa : ω ^ a' ≠ 0 := (opow_pos _ omega0_pos).ne'
      set y := ω ^ a' * (w / ω ^ a' + 1) with hy
      have hwy : w < y := by rw [hy, mul_add_one]; exact lt_mul_div_add w hpa
      have hy0 : y ≠ 0 := (lt_of_le_of_lt zero_le hwy).ne'
      have hye : y < ω ^ e := by
        have h1 : y ≤ w + ω ^ a' := by
          rw [hy, mul_add_one]; exact add_le_add (mul_div_le w _) le_rfl
        exact h1.trans_lt (isPrincipal_add_omega0_opow e hwe
          ((opow_lt_opow_iff_right one_lt_omega0).2 ha'e))
      have hey : a' ≤ cdExp y := cdExp_max hy0 (dvd_mul_right _ _)
      set z' := z1 + y with hz'
      have hz'0 : z' ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hy0) le_add_self).ne'
      have hez' : cdExp z' = cdExp y := cpExp_add z1 hy0
      have hz'd : ω * ω ∣ z' := cp_ww_of_exp hz'0 (by rw [hez']; exact ha'2.trans hey)
      have hz'z : z' < z := by rw [hdec]; exact (add_lt_add_iff_left _).2 hye
      have hμ : IsRestartIdx (l0 + z') :=
        ri_iff.2 ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hz'0) le_add_self).ne', dvd_add hd0 hz'd⟩
      refine ⟨l0 + z', hμ, ?_, ?_, ?_, ?_⟩
      · calc ν ≤ ν' := le_max_left _ _
          _ = l0 + z1 + w := hw
          _ < l0 + z1 + y := (add_lt_add_iff_left _).2 hwy
          _ = l0 + z' := by rw [hz', add_assoc]
      · exact (add_lt_add_iff_left _).2 hz'z
      · exact X.cb_cstI _ _ (hcρ.trans_le (upsilon_normal.strictMono.monotone le_self_add))
      · rw [X.val_cst, IH z' hz'z (pos_iff_ne_zero.2 hz'0) (hz'z.trans hzρ) hz'd, hez']
        exact hca'.trans (cpOff_mono hey)
    have := lt_xtOrec_of_cof hl hl1 hCB hcof
    rwa [X.val_cst] at this

/-- **The offset off the fixed points of `υ`**: `O(μ) = -1 + e(μ)`. -/
theorem xtNonfix {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hww : ω * ω < μ) (hfix : μ < upsilon μ)
    (hμ1 : μ < Om1) : xtOrec X μ = cdOff (cdExp μ) := by
  obtain ⟨l0, z, hl0, hz0, hzρ, hzd, rfl⟩ := cpDecomp hμ hww hfix
  have hl01 : l0 < Om1 := (lt_add_of_pos_right l0 hz0).trans hμ1
  rw [xtRel hl0 hl01 z hz0 hzρ hzd, cpExp_add _ hz0.ne']

/-- **The offset at an isolated fixed point**: `O(F) = F`. -/
theorem xtIso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hF1 : F < Om1)
    (hiso : CpIso F) : xtOrec X F = F := by
  obtain ⟨hE, hp, hww⟩ := cp_fix_facts hF hfix
  obtain ⟨ν, hνF, hν⟩ := hiso
  set ν2 := max ν (ω * ω) with hν2
  have hν2F : ν2 < F := max_lt hνF hww
  have hwin : ∀ μ, IsRestartIdx μ → ν2 < μ → μ < F →
      ω * ω < μ ∧ μ < upsilon μ ∧ xtOrec X μ = cdOff (cdExp μ) := by
    intro μ hμ h1 h2
    have hww' : ω * ω < μ := (le_max_right _ _).trans_lt h1
    have hfx : μ < upsilon μ := hν μ hμ ((le_max_left _ _).trans_lt h1) h2
    exact ⟨hww', hfx, xtNonfix hμ hww' hfx (h2.trans hF1)⟩
  refine le_antisymm ?_ ?_
  · refine xtOrec_le_of (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le hww)) fun s hCB hc => ?_
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc _ hν2F
    obtain ⟨-, hfx, hOμ⟩ := hwin μ hμ h1 h2
    have hμle : X.val s (upsilon μ) ≤ μ :=
      (hsμ.trans_eq hOμ).trans ((cdOff_le _).trans (cpExp_le hμ.1))
    rw [xt_const_of_small (ups_inE hμ) (ups_lt_Om1 _ (h2.trans hF1)) hCBμ (hμle.trans_lt hfx) (upsilon F)]
    exact hμle.trans_lt h2
  · refine le_of_forall_lt fun c hcF => ?_
    have hCB : X.CB (X.cst c) (upsilon F) := X.cb_cstI _ _ (by rw [hfix]; exact hcF)
    have hcof : XtCof X (xtOrec X) F (X.cst c) := by
      intro ν0 hν0
      set ν1 := max (max ν0 ν2) c with hν1
      have hν1F : ν1 < F := max_lt (max_lt hν0 hν2F) hcF
      set a' := c + 1 + 1 with ha'
      have h1F : (1 : Ordinal.{0}) < F :=
        lt_of_le_of_lt (Order.one_le_iff_pos.2 (mul_pos omega0_pos omega0_pos)) hww
      have ha'F : a' < F := hp (hp hcF h1F) h1F
      have hpa : ω ^ a' ≠ 0 := (opow_pos _ omega0_pos).ne'
      set y := ω ^ a' * (ν1 / ω ^ a' + 1) with hy
      have hν1y : ν1 < y := by rw [hy, mul_add_one]; exact lt_mul_div_add ν1 hpa
      have hy0 : y ≠ 0 := (lt_of_le_of_lt zero_le hν1y).ne'
      have hyF : y < F := by
        have h1 : y ≤ ν1 + ω ^ a' := by
          rw [hy, mul_add_one]; exact add_le_add (mul_div_le ν1 _) le_rfl
        have h2 : ω ^ a' < F := by
          rw [← hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 ha'F
        exact h1.trans_lt (hp hν1F h2)
      have hey : a' ≤ cdExp y := cdExp_max hy0 (dvd_mul_right _ _)
      have h2a : (2 : Ordinal.{0}) ≤ a' := by
        rw [ha', add_assoc, one_add_one_eq_two]; exact le_add_self
      have hyd : ω * ω ∣ y := cp_ww_of_exp hy0 (h2a.trans hey)
      have hμ : IsRestartIdx y := ri_iff.2 ⟨hy0, hyd⟩
      have hν2y : ν2 < y := ((le_max_right ν0 ν2).trans (le_max_left _ c)).trans_lt hν1y
      obtain ⟨-, -, hOy⟩ := hwin y hμ hν2y hyF
      refine ⟨y, hμ, ((le_max_left ν0 ν2).trans (le_max_left _ c)).trans_lt hν1y, hyF, ?_, ?_⟩
      · exact X.cb_cstI _ _
          (((le_max_right _ c).trans_lt hν1y).trans_le upsilon_normal.strictMono.le_apply)
      · rw [X.val_cst, hOy]
        exact (le_self_add.trans (cpOff_add_one_ge (c + 1))).trans (cpOff_mono hey)
    have := lt_xtOrec_of_cof hF hF1 hCB hcof
    rwa [X.val_cst] at this

end Googology.Trans.PoR.InaccPsi.R2.Xt
