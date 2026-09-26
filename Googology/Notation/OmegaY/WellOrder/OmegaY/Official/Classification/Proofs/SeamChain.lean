/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamChain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamLookup

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The chain of the copies left of `c_r` (the induction behind `BoundaryChainD`)

For a node `Q` of a new column `X = x + w·i` of a run (`x ∈ blockColumns`, block `0` included)
with origin `o` (the source of its emit), `ChainOK Q o` says: the scale-`k` chain of `R` from `Q`
reaches every node left of `c_r` that the scale-`k` chain of `M(s)` from `o` reaches.

`chainOK_of_step`: `ChainOK` holds for every such node once every node satisfies it from the
nodes of the columns left of it (`StepOK`, a strong induction on the column). `BoundaryChainD` is
`ChainOK` for the nodes of the copies of `x₀` (`boundaryChainD_of_step`).

The step is split by the kind of the node:

* `StepBlock0`: block `0` (the column `x₀`);
* `StepUpper`: an upper emit of a block `i ≥ 1`;
* `StepTop`: a lower emit of an inner column of a block `i ≥ 1` that is the top copy of its origin;
* `StepNonTop`: a lower emit of an inner column of a block `i ≥ 1` that is not the top copy;
* `StepX0`: a lower emit of the copy of `x₀` in a block `i ≥ 1`.
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt)

/-! ## Definitions -/

/-- `Q` is the node of the emit `j` of a new column, with origin `o`. -/
def OrigAt (M R : Mountain) (n cr x0 : Nat) (τ : Row) (Q o : Ref) : Prop :=
  ∃ i x es j, x ∈ blockColumns cr x0 n i ∧ Q.column = x + (x0 - cr) * i ∧ Q.index = j + 1 ∧
    emitsT (ctxAt M R x i cr (x0 - cr) x0 Q.column) τ = .ok es ∧
    (∃ c, Reserve.cell? R Q = some c) ∧ ∃ hj : j < es.length, es[j].2.src = o

/-- The chain of `Q` in `R` reaches the nodes left of `c_r` of the chain of `o` in `M`. -/
def ChainOK (R M : Mountain) (cr : Nat) (Q o : Ref) : Prop :=
  ∀ k (μ : Ref), μ.column < cr → ScaleReach M k o μ → ScaleReach R k Q μ

/-- `ChainOK` at `Q` from `ChainOK` at the nodes of the columns left of `Q`. -/
def StepOK (R M : Mountain) (n : Nat) (t : Cell) (root : Ref) (Q o : Ref) : Prop :=
  (∀ Q' o', Q'.column < Q.column →
    OrigAt M R n root.column (M.size - 1) (official t.row) Q' o' →
    ChainOK R M root.column Q' o') → ChainOK R M root.column Q o

/-- The data of a node of a new column. -/
def NodeData (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat)
    (es : List (Emit × Origin)) (j : Nat) : Prop :=
  Official.expandDiagram s n = .ok R ∧ Recon.Top s M t root ∧
    x ∈ blockColumns root.column (M.size - 1) n i ∧
    emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es ∧
    (∃ c, Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some c) ∧
    j < es.length

/-! ## The cases of the step -/

/-- The step for the nodes of block `0`. -/
def StepBlock0 : Prop :=
  ∀ s n R M t root x es j, NodeData s n R M t root 0 x es j → ∀ hj : j < es.length,
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * 0, j + 1⟩ es[j].2.src

/-- The step for an upper emit of a block `i ≥ 1`. -/
def StepUpper : Prop :=
  ∀ s n R M t root i x es j, NodeData s n R M t root i x es j → 0 < i →
    ∀ hj : j < es.length, es[j].2.isUpper = true →
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

/-- The step for a lower top copy of an inner column of a block `i ≥ 1`. -/
def StepTop : Prop :=
  ∀ s n R M t root i x es j, NodeData s n R M t root i x es j → 0 < i → x < M.size - 1 →
    ∀ hj : j < es.length, es[j].2.isUpper = false → IsTopAt es j →
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

/-- The step for a lower copy of an inner column of a block `i ≥ 1` that is not the top copy. -/
def StepNonTop : Prop :=
  ∀ s n R M t root i x es j, NodeData s n R M t root i x es j → 0 < i → x < M.size - 1 →
    ∀ hj : j < es.length, es[j].2.isUpper = false → ¬ IsTopAt es j →
    StepOK R M n t root ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

/-- The step for a lower emit of the copy of `x₀` in a block `i ≥ 1`. -/
def StepX0 : Prop :=
  ∀ s n R M t root i es j, NodeData s n R M t root i (M.size - 1) es j → 0 < i →
    ∀ hj : j < es.length, es[j].2.isUpper = false →
    StepOK R M n t root ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ es[j].2.src

/-! ## The induction -/

theorem stepOK_of_cases (h0 : StepBlock0) (hU : StepUpper) (hT : StepTop) (hN : StepNonTop)
    (hX : StepX0) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) :
    ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      StepOK R M n t root Q o := by
  intro Q o hQ
  obtain ⟨i, x, es, j, hx, hQc, hQi, hes, hcell, hj, ho⟩ := hQ
  have hQ : Q = ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ := by
    cases Q; simp only at hQc hQi; subst hQc hQi; rfl
  subst hQ ho
  simp only at hes
  have hD : NodeData s n R M t root i x es j := ⟨hrun, hTop, hx, hes, hcell, hj⟩
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    exact h0 s n R M t root x es j hD hj
  cases hup : es[j].2.isUpper
  · have hcr := hTop.lt
    obtain ⟨_, hxl⟩ := mem_blockColumns hcr hx
    rcases Nat.lt_or_eq_of_le hxl with hlt | heq
    · by_cases htop : IsTopAt es j
      · exact hT s n R M t root i x es j hD hi0 hlt hj hup htop
      · exact hN s n R M t root i x es j hD hi0 hlt hj hup htop
    · subst heq
      exact hX s n R M t root i es j hD hi0 hj hup
  · exact hU s n R M t root i x es j hD hi0 hj hup

/-- **`ChainOK` for every node of a new column**, from the steps. -/
theorem chainOK_of_step {R M : Mountain} {n : Nat} {t : Cell} {root : Ref}
    (hstep : ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      StepOK R M n t root Q o) :
    ∀ Q o, OrigAt M R n root.column (M.size - 1) (official t.row) Q o →
      ChainOK R M root.column Q o := by
  intro Q
  induction h : Q.column using Nat.strong_induction_on generalizing Q with
  | _ X ih =>
    intro o hQ
    apply hstep Q o hQ
    intro Q' o' hlt hQ'
    exact ih Q'.column (by omega) Q' rfl o' hQ'

/-- **`BoundaryChainD` from the five cases of the step.** -/
theorem boundaryChainD_of_cases (h0 : StepBlock0) (hU : StepUpper) (hT : StepTop)
    (hN : StepNonTop) (hX : StepX0) : BoundaryChainD := by
  intro s n R M t root hrun hTop i hi0 hin esB hes k hk kk m hm hr
  have hcr := hTop.lt
  have hstep := stepOK_of_cases h0 hU hT hN hX hrun hTop
  have hall := chainOK_of_step hstep
  -- the node exists
  have hXR : M.size - 1 + (M.size - 1 - root.column) * (i - 1) < R.size := by
    have := Proofs.CopyShape.Found.boundary_lt hrun hTop (i := i) hi0 hin
    rw [Classification.Proofs.ChainCorr.boundary_eq hcr hi0] at this
    exact this
  have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
  obtain ⟨lo, us, hD⟩ := colData_x0 E (m := i - 1) (by omega)
  have hee : esB = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  have hsz := hD.size
  have hk1 : k + 1 < (R[M.size - 1 + (M.size - 1 - root.column) * (i - 1)]'hD.XR).size := by
    rw [hsz, ← hee]; omega
  have hcell : ∃ c, Reserve.cell? R ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ =
      some c := by
    refine ⟨(R[M.size - 1 + (M.size - 1 - root.column) * (i - 1)]'hD.XR)[k + 1]'hk1, ?_⟩
    simp only [Reserve.cell?, Array.getElem?_eq_getElem hD.XR, Option.bind_eq_bind,
      Option.bind_some]
    exact Array.getElem?_eq_getElem hk1
  have hes' : emitsT (ctxAt M R (M.size - 1) (i - 1) root.column (M.size - 1 - root.column)
      (M.size - 1) (M.size - 1 + (M.size - 1 - root.column) * (i - 1))) (official t.row) =
      .ok esB := by
    unfold blockEmits at hes; exact hes
  have hO : OrigAt M R n root.column (M.size - 1) (official t.row)
      ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ esB[k].2.src :=
    ⟨i - 1, M.size - 1, esB, k, hD.xb, rfl, rfl, hes', hcell, hk, rfl⟩
  exact hall _ _ hO kk m hm hr

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.boundaryChainD_of_cases
