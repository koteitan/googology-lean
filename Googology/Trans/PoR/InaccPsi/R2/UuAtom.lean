import Googology.Trans.PoR.InaccPsi.R2.UuAtL

/-!
# The member systems at every `ψ₃`-atom below `Y₃`; the level statement past `Γ₂` at every level below `Y₃`

`T = Ug.ugTh`, `H_λ = cdHull S λ`, `CL₃ = Ug.UgCL`, `Γ₂ = ψ₃(0)`, `Y₃ = ψ₃(Ω₃)`.

* `uuAtomMS` (**`Uq.UqAtomMS S λ Y₃` IS A THEOREM**: a successor `d = d' + 1` by `Uu.uuMA_succ`, a limit `d` from the
  member system of `d` itself (an inner limit of `H_λ` below `ψ₃(d)`) by `Uu.uuMA_lim` / `Uu.uuMB_lim`);
* `uuFixY` (**`Uq.UqFixMS S λ Y₃`**), `uuLevY` (**THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < Y₃` OF
  `H_λ`**: `UjOwP (CL₃ E) E (T E)` and `UjLev (CL₃ E) E (T E)`, given only the restart hypotheses).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`UqAtomMS S λ Y₃` IS A THEOREM**: every `ψ₃`-atom `ψ₃(d)`, `1 ≤ d`, of `H_λ` below `Y₃` has a member system,
given those of the smaller limits. -/
theorem uuAtomMS : UqAtomMS S l (ugY S) := by
  intro d hdH hd1 hd hY IH
  rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d', hd'⟩ | hdl
  · rw [h0] at hd1; exact absurd hd1 (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hd'
    subst hd'
    exact Or.inl (uuMA_succ hl hX hdH hd hY)
  · rcases IH d hdH hdl hd with hA | hB
    · exact Or.inl (uuMA_lim hl hX hdH hdl hd hY hA)
    · exact Or.inr (uuMB_lim hl hX hdH hdl hd hY hB)

/-- **`UqFixMS S λ Y₃`**: every `W`-fixed limit `Γ₂ ≤ r < Y₃` of `H_λ` has a member system, given those of the
smaller limits. -/
theorem uuFixY : UqFixMS S l (ugY S) := uqFix_of_atoms hl hX (uuAtomMS hl hX) le_rfl

/-- **THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < Y₃` OF `H_λ`** (image `T E`, own predicate `CL₃ E`),
given only the restart hypotheses. -/
theorem uuLevY {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E) (hE : E < ugY S) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevAtoms hl hX (uuAtomMS hl hX) hEH hWE hE

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uu
