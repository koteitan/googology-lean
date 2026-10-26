import Googology.Trans.PoR.InaccPsi.R2.UcAt

/-!
# The objects of the citation below `θ = ψ_{Ω₂}(Ω_ω)`, defined below `R2.CitedUc` in the import graph

`B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `V = Ω₃ = Om (1 + 1 + 1)`, `Uc.ucG d L` the generic
hierarchy (`R2.UcH`).  These definitions repeat, at a place of the import graph below `R2.CitedUc`, those of
`R2.UlK` / `R2.UlUB` (`Ul.UlK`, `Ul.ulD`, `Ul.ulH`); `R2.VdEq` proves that they are the same objects.

* `VdK S s q` (**the visibility closure at `Ω_{s+1}`**: the closure of `q ∪ {0, I_n, I_ω}` under `+`, `φ`, `Ω_·` and
  every collapse `ψ_π`, `π ≠ Ω_{s+1}`), `vdD S s j` (**its datum**: the least `m` with `j ∈ VdK S s (m + 1)`);
  `vdD S 0 x` is the **`K⁽⁰⁾`-datum** of an ordinal `x` (defined for every ordinal, of the notation or not);
* `vdH S γ` (**the lifted hierarchy `Hˡ_γ` at `Ω₂`**, every level `γ`), `vdLevSet`, `vdLev`, `vdI` (**the normal
  form `z = Hˡ_λ(y)`**: `λ` the least level `< V` visible at `z` that does not fix `z`, `y` the index);
* `VdDatIn P M` (**some reading of the data of `M` satisfies `P`**: `ucDat M` below `B₂`, the `K⁽⁰⁾`-datum
  `vdD S 0 M` for some `S` with `B₂ ≤ M < θ`), `VdDatAll P M` (**every reading does**), `VdRng x` (`x < B₂` or
  `x < θ` for some `S`), `VdLtIn M v`, `VdLtAll M v` (**some / every reading of the data of `M` lies below `v`**: the
  `K⁽⁰⁾`-datum is compared with `v` through the strongly critical points `q ≤ v`, resp. `q ≥ v`).

No new axiom.  New definitions: `VdK`, `vdD`, `vdH`, `vdLevSet`, `vdLev`, `vdI`, `VdDatIn`, `VdDatAll`, `VdLtIn`,
`VdLtAll`, `VdRng`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

/-- **The visibility closure at the threshold `Ω_{s+1}`** (the same clauses as `Ul.UlK`). -/
inductive VdK (S : InaccSeq.{0}) (s q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < q → VdK S s q x
  | zero : VdK S s q 0
  | inacc (n : ℕ) : VdK S s q (S.I n)
  | inaccW : VdK S s q S.Iw
  | add {x y : Ordinal.{0}} : VdK S s q x → VdK S s q y → VdK S s q (x + y)
  | phi {x y : Ordinal.{0}} : VdK S s q x → VdK S s q y → VdK S s q (veblen x y)
  | om {x : Ordinal.{0}} : VdK S s q x → VdK S s q (Om x)
  | coll {π e : Ordinal.{0}} : S.InR π → π ≠ Om (s + 1) → VdK S s q π → VdK S s q e →
      VdK S s q (S.psi e π)

/-- **The datum of `j` at the threshold `Ω_{s+1}`**: the least `m` with `j ∈ VdK S s (m + 1)`. -/
noncomputable def vdD (S : InaccSeq.{0}) (s j : Ordinal.{0}) : Ordinal.{0} := sInf {m | VdK S s (m + 1) j}

/-- **The lifted hierarchy `Hˡ_γ` at `Ω₂`** (floor `Ω₁`, data `vdD S 1`). -/
noncomputable def vdH (S : InaccSeq.{0}) (γ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  ucG (vdD S 1) (Om 1) γ

/-- The levels below `V = Ω₃`, visible at `z`, that do not fix `z`. -/
def vdLevSet (S : InaccSeq.{0}) (z : Ordinal.{0}) : Set Ordinal.{0} :=
  {γ | γ < Om (1 + 1 + 1) ∧ vdD S 1 γ < z ∧ vdH S γ z ≠ z}

/-- **The level** of `z`. -/
noncomputable def vdLev (S : InaccSeq.{0}) (z : Ordinal.{0}) : Ordinal.{0} := sInf (vdLevSet S z)

/-- **The index** of `z` in `Hˡ_γ`. -/
noncomputable def vdI (S : InaccSeq.{0}) (γ z : Ordinal.{0}) : Ordinal.{0} := sInf {y | vdH S γ y = z}

/-- **Some reading of the data of the level `M` satisfies `P`**: `ucDat M` for `M < B₂`, the `K⁽⁰⁾`-datum for some
`S` with `B₂ ≤ M < θ`. -/
def VdDatIn (P : Ordinal.{0} → Prop) (M : Ordinal.{0}) : Prop :=
  (M < ucB ∧ P (ucDat M)) ∨ ∃ S : InaccSeq.{0}, ucB ≤ M ∧ M < ConjT.th S ∧ P (vdD S 0 M)

/-- **Every reading of the data of the level `M` satisfies `P`.** -/
def VdDatAll (P : Ordinal.{0} → Prop) (M : Ordinal.{0}) : Prop :=
  (M < ucB → P (ucDat M)) ∧ ∀ S : InaccSeq.{0}, ucB ≤ M → M < ConjT.th S → P (vdD S 0 M)

/-- **Some reading of the data of `M` lies below `v`**: `ucDat M < v` for `M < B₂`; for some `S` with `B₂ ≤ M < θ`, the
`K⁽⁰⁾`-datum lies below a strongly critical `q ≤ v` (the `K⁽⁰⁾`-datum is read only at strongly critical points). -/
def VdLtIn (M v : Ordinal.{0}) : Prop :=
  (M < ucB ∧ ucDat M < v) ∨
    ∃ S : InaccSeq.{0}, ucB ≤ M ∧ M < ConjT.th S ∧ ∃ q, SC q ∧ q ≤ v ∧ vdD S 0 M < q

/-- **Every reading of the data of `M` lies below `v`**: `ucDat M < v` for `M < B₂`; for every `S` with `B₂ ≤ M <
θ`, the `K⁽⁰⁾`-datum lies below every strongly critical `q ≥ v`. -/
def VdLtAll (M v : Ordinal.{0}) : Prop :=
  (M < ucB → ucDat M < v) ∧
    ∀ S : InaccSeq.{0}, ucB ≤ M → M < ConjT.th S → ∀ q, SC q → v ≤ q → vdD S 0 M < q

/-- **The range of the citation**: `x < B₂`, or `x < θ` for some `S`. -/
def VdRng (x : Ordinal.{0}) : Prop := x < ucB ∨ ∃ S : InaccSeq.{0}, x < ConjT.th S

theorem vdDatIn_uc {P : Ordinal.{0} → Prop} {M : Ordinal.{0}} (hM : M < ucB) (h : P (ucDat M)) : VdDatIn P M :=
  Or.inl ⟨hM, h⟩

theorem vdLtIn_uc {M v : Ordinal.{0}} (hM : M < ucB) (h : ucDat M < v) : VdLtIn M v := Or.inl ⟨hM, h⟩

theorem vdDatIn_th {P : Ordinal.{0} → Prop} {S : InaccSeq.{0}} {M : Ordinal.{0}} (hB : ucB ≤ M)
    (hM : M < ConjT.th S) (h : P (vdD S 0 M)) : VdDatIn P M :=
  Or.inr ⟨S, hB, hM, h⟩

end Googology.Trans.PoR.InaccPsi.R2.Vd
