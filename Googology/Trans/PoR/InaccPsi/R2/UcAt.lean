import Googology.Trans.PoR.InaccPsi.R2.UcBd

/-!
# The parts of an atom below `B₂` and the atom rebuilt from images of its parts

`Ω₁ = Om1`, `X = Tl.tlX`, `F_β = Rh.rhF β`, `H_γ = Uc.ucH γ`, `B₂ = Uc.ucB`.  A strongly critical `z ∈ (Ω₁, B₂)` is
an **atom**: below `X` it is `F_λ(y)` with `λ = Tl.tlLev z`, `y = Tl.tlI λ z` (`R2.TlDat`); from `X` on it is `H_λ(y)`
with `λ = Uc.ucLev z`, `y = Uc.ucI λ z` (`R2.UcDat`).  Its **parts** are `λ` and `y` below `X`, the components of `λ`
and `y` from `X` on; `ucRebuild f z` is the atom of the same shape with every part `x` replaced by `f x` (for `H_λ(y)`:
`H_{ucMap f λ}(f y)`).

* `ucParts`, `ucRebuild`, `ucParts_F`, `ucRebuild_F` (**`F_β(y) < X` with `y < F_β(y)`: parts `{β, y}`, rebuilt
  `F_{f β}(f y)`**), `ucParts_H`, `ucRebuild_H` (**`X ≤ H_γ(y) < B₂` with `γ < E₂`, `y < H_γ(y)`: parts `comps(γ) ∪
  {y}`, rebuilt `H_{ucMap f γ}(f y)`**).

No new axiom.  New definitions: `ucParts`, `ucRebuild`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl

/-- **The parts of an atom**: `{λ, y}` for `F_λ(y)` below `X`; the components of `λ` and `y` for `H_λ(y)` from `X`
on. -/
def ucParts (z : Ordinal.{0}) : Set Ordinal.{0} :=
  if z < tlX then {tlLev z, tlI (tlLev z) z} else ucComps (ucLev z) ∪ {ucI (ucLev z) z}

/-- **The atom rebuilt from the images of its parts.** -/
noncomputable def ucRebuild (f : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) : Ordinal.{0} :=
  if z < tlX then rhF (f (tlLev z)) (f (tlI (tlLev z) z)) else ucH (ucMap f (ucLev z)) (f (ucI (ucLev z) z))

theorem ucParts_F {β y : Ordinal.{0}} (hX : rhF β y < tlX) (hy : y < rhF β y) : ucParts (rhF β y) = {β, y} := by
  rw [ucParts, if_pos hX, tlLev_F hy, tlI_rhF]

theorem ucRebuild_F (f : Ordinal.{0} → Ordinal.{0}) {β y : Ordinal.{0}} (hX : rhF β y < tlX)
    (hy : y < rhF β y) : ucRebuild f (rhF β y) = rhF (f β) (f y) := by
  rw [ucRebuild, if_pos hX, tlLev_F hy, tlI_rhF]

theorem ucParts_H {γ y : Ordinal.{0}} (hγ : γ < ucE) (hy : y < ucH γ y) (hX : tlX ≤ ucH γ y) :
    ucParts (ucH γ y) = ucComps γ ∪ {y} := by
  obtain ⟨hl, hi⟩ := ucLev_H hγ hy
  rw [ucParts, if_neg (not_lt.2 hX), hl, hi]

theorem ucRebuild_H (f : Ordinal.{0} → Ordinal.{0}) {γ y : Ordinal.{0}} (hγ : γ < ucE) (hy : y < ucH γ y)
    (hX : tlX ≤ ucH γ y) : ucRebuild f (ucH γ y) = ucH (ucMap f γ) (f y) := by
  obtain ⟨hl, hi⟩ := ucLev_H hγ hy
  rw [ucRebuild, if_neg (not_lt.2 hX), hl, hi]

end Googology.Trans.PoR.InaccPsi.R2.Uc
