import Googology.Trans.PoR.InaccPsi.R2.CpFront
import Googology.Trans.PoR.InaccPsi.R2.XtGen

/-!
# The terms `φ(n, ·)`, `n < ω`, as a term system: `R2.VzO`, `R2.VzW` and `R2.CpFront` from the generic theorem

`vzSys` is the term system of `VzTm` (constants, the base, `ϑˣ(Ω₁·n + t)`, sums, `ω^t`; top `B(x) = VzB x`, the least
value of `φ(ω, ·)` above `x`).  Its fields are the repo's Lemma IMG (`RstK.pkgVz`), Lemma RS (`rsStep_Vz`), the
comparison (`uniVz_le`, from Lemma EXACT `vzv_pi`) and the representation (`vzv_repB`); the top has the IMG package
`RstK.vzPkgB`.  Then:

* `xtVz_orec` (**the generic offset is `VzOrec`**), `xtVz_lam` (**its frontier is `Λ_B`**), `xtVz_B1` (**its first
  limit of frontiers is `cpB1`**);
* `xtVz_blk` (= `vzBlk`), `xtVz_blk1` (= `cpBlk`), `xtVz_reach1` (= `cpReach`): the block theorems of the stages up to
  `cpB1`, as instances of `Xt.xtBlk` and `Xt.xtBlk1`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 VzTm

theorem xt_vzB_lt_next {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    VzB (upsilon l) < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact lt_of_le_of_lt (vzB_le_next (upsPt_inE hρU) (ups_lt_Om1 l hl1)
    (upsilon_normal.strictMono h1) hτU.2) (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system of `φ(n, ·)`, `n < ω`.** -/
noncomputable def vzSys : XtSys where
  Tm := VzTm
  val := VzTm.val
  CB := CBt
  cs := cst'
  cst := VzTm.cst
  top := VzB
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 _ hCB => vzv_lt_B (ups_inE hl) (ups_lt_Om1 l hl1) hCB
  one_le_top := fun l hl hl1 =>
    (one_le_iff_pos.2 (ups_inE hl).pos).trans
      ((vzv_lt_B (ups_inE hl) (ups_lt_Om1 l hl1) (t := bs) trivial).le)
  rep := fun l hl hl1 _ hv => vzv_repB (ups_inE hl) (ups_lt_Om1 l hl1) hv
  top_lt := fun l hl hl1 => xt_vzB_lt_next hl hl1
  pkg := fun _ _ _ _ hCB h1 R => R.pkgVz hCB h1
  rs := fun _ _ _ _ hCB => rsStep_Vz hCB
  uni_le := fun _ _ hσ hρ hB _ _ ht hu => uniVz_le hσ hρ hB ht hu
  small := fun t => by
    by_cases h : noB t
    · exact Or.inl (vzv_noB t h)
    · exact Or.inr (fun x hx hx1 hc => le_vzv_of_not_noB hx hx1 t hc h)

/-- **The generic offset of `vzSys` is `VzOrec`.** -/
theorem xtVz_orec : xtOrec vzSys = VzOrec :=
  (xtOrec_unique vzSys (O := VzOrec) (fun l => vzOrec_eq l)).symm

/-- **The frontier of `vzSys` is `Λ_B`.** -/
theorem xtVz_lam : xtLam vzSys = VzLam := by
  unfold xtLam VzLam
  rw [xtVz_orec]
  rfl

/-- The top `B` of `vzSys` has an IMG package (`RstK.vzPkgB`). -/
theorem xtVz_topPkg : XtTopPkg vzSys := fun _ _ _ R => R.vzPkgB

/-- **The first limit of frontiers of `vzSys` is `cpB1`.** -/
theorem xtVz_B1 : xtB1 vzSys = Cp.cpB1 := by
  unfold xtB1 Cp.cpB1 XtFrCof Cp.CpFrCof XtFr Cp.CpFr
  rw [xtVz_orec]
  rfl

/-- **`vzBlk` as an instance of the generic block theorem.** -/
theorem xtVz_blk {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ VzLam) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  have h := xtBlk (X := vzSys) hm hc (by rw [xtVz_lam]; exact hB)
  rwa [xtVz_orec] at h

/-- **`cpBlk` as an instance of the generic block theorem past the frontier.** -/
theorem xtVz_blk1 :
    (∀ c d, c < d → d < upsilon Cp.cpB1 → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < Cp.cpB1 ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < Cp.cpB1 →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon Cp.cpB1, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  have h := xtBlk1 xtVz_topPkg
  rwa [xtVz_orec, xtVz_B1] at h

/-- **`cpReach` from the generic theorem**: `lh(ρ_λ) = δ_λ + VzOrec(λ)` below `cpB1`. -/
theorem xtVz_reach1 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < Cp.cpB1) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l) := by
  have h := xtReach1 xtVz_topPkg hl (by rw [xtVz_B1]; exact hlB)
  rwa [xtVz_orec] at h

end Googology.Trans.PoR.InaccPsi.R2.Xt
