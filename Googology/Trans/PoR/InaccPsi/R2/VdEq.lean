import Googology.Trans.PoR.InaccPsi.R2.VdBase
import Googology.Trans.PoR.InaccPsi.R2.CitedUz
import Googology.Trans.PoR.InaccPsi.R2.UiAgree
import Googology.Trans.PoR.InaccPsi.R2.UoUc

/-!
# The objects of `R2.VdBase` are those of `R2.UlK` / `R2.UlUB`

`Ul.UlK S s q` (the visibility closure at `Ω_{s+1}`), `Ul.ulD S s` (its datum), `Ul.ulH S s` (the lifted hierarchy).
The definitions of `R2.VdBase` were made below `R2.CitedUc` in the import graph so that `R2.CitedVd` can mention them;
they are the same objects:

* `vdK_iff` (**`VdK S s q x ↔ UlK S s q x`**), `vdD_eq` (**`vdD S s = ulD S s`**), `vdH_eq` (**`vdH S = ulH S 1`**),
  `vdLevSet_eq` (the level set read with `ulD`, `ulH`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

theorem vdK_toUl {s q x : Ordinal.{0}} (h : VdK S s q x) : UlK S s q x := by
  induction h with
  | small h => exact UlK.small h
  | zero => exact UlK.zero
  | inacc n => exact UlK.inacc n
  | inaccW => exact UlK.inaccW
  | add _ _ ihx ihy => exact UlK.add ihx ihy
  | phi _ _ ihx ihy => exact UlK.phi ihx ihy
  | om _ ih => exact UlK.om ih
  | coll hπ hπW _ _ ihπ ihe => exact UlK.coll hπ hπW ihπ ihe

theorem vdK_ofUl {s q x : Ordinal.{0}} (h : UlK S s q x) : VdK S s q x := by
  induction h with
  | small h => exact VdK.small h
  | zero => exact VdK.zero
  | inacc n => exact VdK.inacc n
  | inaccW => exact VdK.inaccW
  | add _ _ ihx ihy => exact VdK.add ihx ihy
  | phi _ _ ihx ihy => exact VdK.phi ihx ihy
  | om _ ih => exact VdK.om ih
  | coll hπ hπW _ _ ihπ ihe => exact VdK.coll hπ hπW ihπ ihe

/-- **`VdK S s q x ↔ UlK S s q x`.** -/
theorem vdK_iff {s q x : Ordinal.{0}} : VdK S s q x ↔ UlK S s q x := ⟨vdK_toUl, vdK_ofUl⟩

/-- **`vdD S s = ulD S s`.** -/
theorem vdD_eq (s : Ordinal.{0}) : vdD S s = ulD S s := by
  funext j
  unfold vdD ulD
  congr 1
  ext m
  exact vdK_iff

/-- **`vdH S = ulH S 1`.** -/
theorem vdH_eq : vdH S = ulH S 1 := by
  funext γ
  unfold vdH ulH
  rw [vdD_eq]

theorem vdLevSet_eq (z : Ordinal.{0}) :
    vdLevSet S z = {γ | γ < Om (1 + 1 + 1) ∧ ulD S 1 γ < z ∧ ulH S 1 γ z ≠ z} := by
  unfold vdLevSet; rw [vdD_eq, vdH_eq]

end Googology.Trans.PoR.InaccPsi.R2.Vd
