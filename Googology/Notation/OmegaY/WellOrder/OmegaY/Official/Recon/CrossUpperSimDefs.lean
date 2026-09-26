/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperSimDefs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSeam

set_option backward.do.legacy false

/-!
# Copies of block `i ≥ 1`: definitions and generic lemmas

This file prepares the reduction of `SeamLastPosHolds` and `InnerHolds`
(`CrossUpper.lean`, `CrossUpperSeam.lean`) to local statements about the copies of one block
(`CrossUpperSimMain.lean`).

Let `R` be the output of `s[n]`, `M = M(s)`, `c_r` the root column, `x₀` the last column,
`w = x₀ - c_r`, `τ` the row of the top of `x₀`, and `i ≥ 1` a block. A node `Z` of a new
column is a **copy** of a node `z` of `M` (`IsCopy`) when the origin of `Z` has the source `z`;
it is the **top copy** (`TopCopy`) when no node above `Z` in its column is a copy of `z`.

The relation `Cp i Z z` ("`Z` stands for `z` in block `i`"):

* `z` left of `c_r`: `Z` is in the column of `z`, at the row of `z` (the columns left of
  `x₀` are shared by `R` and `M`);
* `z` in `c_r`: `Z` is in the column `c_r + w·i`; if the node `z⁺` above `z` has a row
  `≥ τ`, then the node `Z⁺` above `Z` has the row of `z⁺`; and if `z` has a stored parent `b`
  (the stored parent of `z⁺`, left of `c_r`), the chain of stored parents of `R` from `Z`
  reaches `b` (a node of the shared columns). The chain may pass through the column `c_r` of
  `R` itself: for `s = (1,4,8,25,27,15)`, `n = 1`, the chain of `M(s)` `(3,1) → (2,1) → (1,1)`
  is matched by `(6,1) → (5,1) → (2,1) → (1,1)` in `R`;
* `c_r < col z < x₀`: `Z` is in the column `col z + w·i`; if `row z ≥ τ`, `Z` has the row of
  `z` (the upper part is copied unchanged); if `row z < τ`, `Z` is the top copy of `z`.

## Open statements (numerically checked, `reference/official/cross-upper-sim.cjs`)

* `CopyTop` (column shape): the highest node below `τ` of a column `y + w·i` of block `i` is
  the top copy of the highest node below `τ` of `y`.
* `CopyStepLower`: for the top copy `Z` of a node `z` with `row z < τ` of an inner column, the
  stored parent of `Z⁺` stands for the stored parent of `z⁺` (`Cp`).
* `CopyQLower`: for the top copy `U` of a node `z` with `row z < τ ≤ row z⁺`, the candidate
  `Q U` stands for `Q z`.

Status (`CrossUpperSimTop.lean`, `CrossUpperSimLow.lean`): `CopyTop` is proved from the open
statement `LowerPB.Emitted` (`copyTop_of_emitted`), and `CopyStepLower` from `CopyTop` and its
case `row z⁺ < τ` (`CopyStepLow`, `copyStepLower_of_low`). So `SeamLastPosHolds` and
`InnerHolds` follow from `Emitted`, `CopyQLower` and `CopyStepLow` (`seamLastPos_of_low`,
`inner_of_low`).

A first version of this reduction also asked, about `M(s)` only, that a node of `c_r` in the
middle of the chain from `Q n₀` has its upper node at a row `≥ τ`. That statement is **false**:
`s = (1,4,8,25,27,15)`, `N = (4, ω)`, chain `(3,1) → (2,1) → (1,1)` with `c_r = 2` and the node
above `(2,1)` at the row `2 < τ = ω` (found with random inputs of entries up to `40`; it holds
for all inputs of length `≤ 6` and entries `≤ 12`). The chain clause of `Cp` for `c_r` replaces
it.

## Generic lemmas

`HighestIn F P A`: `A` is the highest node of its column whose row satisfies `P`. Stored
parents (`HBAt`) and candidates (`Q_spec`) are of this form. For an upper copy `y ↦ Y`
(`UpperCopy`, rows `≥ τ` copied with their rows):

* `highestIn_twin`: in two shared columns the highest nodes have the same row;
* `highestIn_upperCopy_ge`: if the highest node of `y` is at a row `≥ τ`, the highest node of
  `Y` has the same row;
* `highestIn_upperCopy_lt`: if it is below `τ` and every row below `τ` satisfies `P`, both
  are the highest nodes below `τ`;
* `highestIn_upperCopy_upper`: if `P` is downward closed and holds below `τ`, and the node
  above the highest node of `y` is at a row `≥ τ`, then the node above the highest node of `Y`
  has the same row.
-/

namespace OmegaY.Official.Recon.CrossUpperSim

open Canonical Expansion Geometry Frame Classification
open CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## Copies -/

/-- `Z` is a copy of `z`: `Z` is a real node of a new column whose origin has the source `z`. -/
def IsCopy (s : List Nat) (n : Nat) (R M : Mountain) (Z : (Frame.ofMountain R).Node)
    (z : (Frame.ofMountain M).Node) : Prop :=
  1 ≤ Z.2.val ∧ ∃ o, OriginAt s n R Z.1.val (Z.2.val - 1) o ∧ o.src = Frame.ref z

/-- `Z` is the top copy of `z`: no node above `Z` in its column is a copy of `z`. -/
def TopCopy (s : List Nat) (n : Nat) (R M : Mountain) (Z : (Frame.ofMountain R).Node)
    (z : (Frame.ofMountain M).Node) : Prop :=
  IsCopy s n R M Z z ∧
    ∀ Z' : (Frame.ofMountain R).Node, Z'.1 = Z.1 → Z.2.val < Z'.2.val → ¬ IsCopy s n R M Z' z

theorem TopCopy.unique {s : List Nat} {n : Nat} {R M : Mountain}
    {Z Z' : (Frame.ofMountain R).Node} {z : (Frame.ofMountain M).Node}
    (h : TopCopy s n R M Z z) (h' : TopCopy s n R M Z' z) (hc : Z.1 = Z'.1) : Z = Z' := by
  apply node_eq_of_index hc
  rcases Nat.lt_trichotomy Z.2.val Z'.2.val with hl | he | hl
  · exact absurd h'.1 (h.2 Z' hc.symm hl)
  · exact he
  · exact absurd h.1 (h'.2 Z hc hl)

/-- The stand-in relation of block `i` (see the module doc). -/
def Cp (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (Z : (Frame.ofMountain R).Node) (z : (Frame.ofMountain M).Node) : Prop :=
  (z.1.val < root.column ∧ Z.1.val = z.1.val ∧
      (Frame.ofMountain R).height Z = (Frame.ofMountain M).height z) ∨
  (z.1.val = root.column ∧ Z.1.val = root.column + (M.size - 1 - root.column) * i ∧
      (∀ z', (Frame.ofMountain M).upper z = some z' → t.row ≤ (Frame.ofMountain M).height z' →
        ∃ Z', (Frame.ofMountain R).upper Z = some Z' ∧
          (Frame.ofMountain R).height Z' = (Frame.ofMountain M).height z') ∧
      (∀ b, (Frame.ofMountain M).rawParent z = some b →
        ∃ B, RawChain (Frame.ofMountain R) Z B ∧ B.1.val = b.1.val ∧
          (Frame.ofMountain R).height B = (Frame.ofMountain M).height b)) ∨
  (root.column < z.1.val ∧ z.1.val < M.size - 1 ∧
      Z.1.val = z.1.val + (M.size - 1 - root.column) * i ∧
      (t.row ≤ (Frame.ofMountain M).height z →
        (Frame.ofMountain R).height Z = (Frame.ofMountain M).height z) ∧
      ((Frame.ofMountain M).height z < t.row → TopCopy s n R M Z z))

theorem Cp.column {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
    {Z : (Frame.ofMountain R).Node} {z : (Frame.ofMountain M).Node}
    (h : Cp s n R M t root i Z z) :
    Z.1.val = shiftCol root.column (M.size - 1 - root.column) i z.1.val := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, _, h2, _⟩
  · rw [h2, shiftCol_of_lt h1]
  · rw [h2, shiftCol_of_le (le_of_eq h1.symm), h1]
  · rw [h2, shiftCol_of_le h1.le]

theorem rawChain_trans {F : Frame} {a b c : F.Node} (h1 : RawChain F a b)
    (h2 : RawChain F b c) : RawChain F a c := by
  induction h1 with
  | here => exact h2
  | step hraw _ ih => exact .step hraw (ih h2)

/-! ## Highest nodes -/

/-- `A` is the highest node of its column whose row satisfies `P`. -/
def HighestIn (F : Frame) (P : Row → Prop) (A : F.Node) : Prop :=
  P (F.height A) ∧ ∀ v : F.Node, v.1 = A.1 → P (F.height v) → v.2.val ≤ A.2.val

/-- The highest node of a column below `θ`. -/
def TopBelow (F : Frame) (θ : Row) (A : F.Node) : Prop := HighestIn F (· < θ) A

section Generic

variable {G F : Frame}

theorem HighestIn.unique {P : Row → Prop} {A B : F.Node}
    (hA : HighestIn F P A) (hB : HighestIn F P B) (hc : A.1 = B.1) : A = B :=
  node_eq_of_index hc (le_antisymm (hB.2 A hc hA.1) (hA.2 B hc.symm hB.1))

/-- The stored parent is the highest node below the row of the node above. -/
theorem highestIn_of_hb {Z Z' A : F.Node} (h : HBAt F Z) (hu : F.upper Z = some Z')
    (hr : F.rawParent Z = some A) : HighestIn F (· < F.height Z') A :=
  h Z' A hu hr

/-- The candidate is the highest node of its column at or below the row of the node. -/
theorem highestIn_of_Q (hF : F.Ordered) {u q : F.Node} (hq : F.Q u = some q) :
    HighestIn F (· ≤ F.height u) q := by
  obtain ⟨_, _, _, _, _, _, hle, hup⟩ := Q_spec hF hq
  refine ⟨hle, ?_⟩
  intro v hv hvle
  by_contra hn
  have hlen' : F.length v.1 = F.length q.1 := by rw [hv]
  have hlen : q.2.val + 1 < F.length q.1 := by have := v.2.isLt; omega
  let V : F.Node := ⟨q.1, ⟨q.2.val + 1, hlen⟩⟩
  have h1 := hup V (upper_eq_of_index rfl rfl)
  have h2 : F.height V ≤ F.height v := height_le_of_index hF hv.symm (by simp [V]; omega)
  exact absurd (lt_of_lt_of_le h1 (h2.trans hvle)) (lt_irrefl _)

/-- The highest node of a column with a property exists when the bottom (phantom) has it. -/
theorem exists_highestIn (F : Frame) (P : Row → Prop) [DecidablePred P] (c : Fin F.width)
    (h0 : 0 < F.length c) (hP0 : P (F.height ⟨c, ⟨0, h0⟩⟩)) :
    ∃ A : F.Node, A.1 = c ∧ HighestIn F P A := by
  let S : Finset (Fin (F.length c)) := Finset.univ.filter (fun k => P (F.height ⟨c, k⟩))
  have hne : S.Nonempty := ⟨⟨0, h0⟩, by simp [S, hP0]⟩
  let k := S.max' hne
  have hk : k ∈ S := Finset.max'_mem S hne
  refine ⟨⟨c, k⟩, rfl, (Finset.mem_filter.mp hk).2, ?_⟩
  intro v hv hPv
  obtain ⟨vc, vk⟩ := v
  simp only at hv
  subst hv
  have hvS : vk ∈ S := by simp [S, hPv]
  exact Finset.le_max' S vk hvS

/-- **Twins.** In two shared columns the highest nodes have the same row. -/
theorem highestIn_twin {R M : Mountain} {c : Nat} (hag : R[c]? = M[c]?) {P : Row → Prop}
    {A : (Frame.ofMountain R).Node} {a : (Frame.ofMountain M).Node} (hAc : A.1.val = c)
    (hac : a.1.val = c) (hA : HighestIn (Frame.ofMountain R) P A)
    (ha : HighestIn (Frame.ofMountain M) P a) :
    (Frame.ofMountain R).height A = (Frame.ofMountain M).height a := by
  obtain ⟨A', hA'1, hA'2, hA'c⟩ := twin_of_agree hag A hAc
  obtain ⟨a', ha'1, ha'2, ha'c⟩ := twin_of_agree' hag a hac
  have e1 : (Frame.ofMountain M).height A' = (Frame.ofMountain R).height A := by
    change ((Frame.ofMountain M).cell A').row = ((Frame.ofMountain R).cell A).row
    rw [hA'c]
  have e2 : (Frame.ofMountain R).height a' = (Frame.ofMountain M).height a := by
    change ((Frame.ofMountain R).cell a').row = ((Frame.ofMountain M).cell a).row
    rw [ha'c]
  have i1 : a'.2.val ≤ A.2.val := hA.2 a' (Fin.ext (by rw [ha'1, hAc])) (by rw [e2]; exact ha.1)
  have i2 : A'.2.val ≤ a.2.val := ha.2 A' (Fin.ext (by rw [hA'1, hac])) (by rw [e1]; exact hA.1)
  have hAa : A' = a := node_eq_of_index (Fin.ext (by rw [hA'1, hac])) (by omega)
  rw [← e1, hAa]

/-- The highest node at a row `≥ τ` is copied with its row. -/
theorem highestIn_upperCopy_ge (hG : G.Ordered) (hF : F.Ordered) {θ : Row} {f : Nat → Nat}
    {y Y : Nat} (C : UpperCopy G F θ f y Y) {P : Row → Prop} {a : G.Node} {A : F.Node}
    (hac : a.1.val = y) (hAc : A.1.val = Y) (ha : HighestIn G P a) (hA : HighestIn F P A)
    (hθ : θ ≤ G.height a) : F.height A = G.height a := by
  obtain ⟨Â, hÂc, hÂh⟩ := C.fwd a hac hθ
  have i1 : Â.2.val ≤ A.2.val := hA.2 Â (Fin.ext (by rw [hÂc, hAc])) (by rw [hÂh]; exact ha.1)
  have h1 : G.height a ≤ F.height A := by
    rw [← hÂh]
    exact height_le_of_index hF (Fin.ext (by rw [hÂc, hAc])) i1
  obtain ⟨v, hvc, hvh⟩ := C.bwd A hAc (hθ.trans h1)
  have i2 : v.2.val ≤ a.2.val := ha.2 v (Fin.ext (by rw [hvc, hac])) (by rw [hvh]; exact hA.1)
  have h2 : G.height v ≤ G.height a := height_le_of_index hG (Fin.ext (by rw [hvc, hac])) i2
  rw [hvh] at h2
  exact le_antisymm h2 h1

/-- The highest node below `τ` of a copy. -/
theorem highestIn_upperCopy_lt (hG : G.Ordered) {θ : Row} {f : Nat → Nat}
    {y Y : Nat} (C : UpperCopy G F θ f y Y) {P : Row → Prop} (hP : ∀ r, r < θ → P r)
    {a : G.Node} {A : F.Node} (hac : a.1.val = y) (hAc : A.1.val = Y) (ha : HighestIn G P a)
    (hA : HighestIn F P A) (hlt : G.height a < θ) : TopBelow G θ a ∧ TopBelow F θ A := by
  refine ⟨⟨hlt, fun v hv hvl => ha.2 v hv (hP _ hvl)⟩, ?_, fun v hv hvl => hA.2 v hv (hP _ hvl)⟩
  by_contra hn
  have hθA : θ ≤ F.height A := le_of_not_gt hn
  obtain ⟨v, hvc, hvh⟩ := C.bwd A hAc hθA
  have i2 : v.2.val ≤ a.2.val := ha.2 v (Fin.ext (by rw [hvc, hac])) (by rw [hvh]; exact hA.1)
  have h2 : G.height v ≤ G.height a := height_le_of_index hG (Fin.ext (by rw [hvc, hac])) i2
  rw [hvh] at h2
  exact absurd (lt_of_le_of_lt (hθA.trans h2) hlt) (lt_irrefl _)

/-- The node above the highest node of a copy. -/
theorem highestIn_upperCopy_upper (hG : G.Ordered) (hF : F.Ordered) {θ : Row}
    {f : Nat → Nat} {y Y : Nat} (C : UpperCopy G F θ f y Y) {P : Row → Prop}
    (hPd : ∀ r r', r ≤ r' → P r' → P r) (hP : ∀ r, r < θ → P r)
    {a a' : G.Node} {A : F.Node} (hac : a.1.val = y) (hAc : A.1.val = Y)
    (ha : HighestIn G P a) (hA : HighestIn F P A) (hau : G.upper a = some a')
    (hθ : θ ≤ G.height a') :
    ∃ A', F.upper A = some A' ∧ F.height A' = G.height a' := by
  obtain ⟨ha'1, ha'2⟩ := upper_spec hau
  obtain ⟨Â, hÂc, hÂh⟩ := C.fwd a' (by rw [ha'1]; exact hac) hθ
  have hnP : ¬ P (G.height a') := fun h => by
    have := ha.2 a' ha'1 h
    omega
  have hcol : A.1 = Â.1 := Fin.ext (by rw [hAc, hÂc])
  have hgt : A.2.val < Â.2.val := by
    by_contra hn
    have hle : F.height Â ≤ F.height A := height_le_of_index hF hcol.symm (by omega)
    rw [hÂh] at hle
    exact hnP (hPd _ _ hle hA.1)
  refine ⟨Â, ?_, hÂh⟩
  apply upper_eq_of_index hcol
  by_contra hne
  have hlen : F.length Â.1 = F.length A.1 := by rw [hcol]
  have hmid : A.2.val + 1 < F.length A.1 := by have := Â.2.isLt; omega
  let V : F.Node := ⟨A.1, ⟨A.2.val + 1, hmid⟩⟩
  have hVnP : ¬ P (F.height V) := fun h => by
    have := hA.2 V rfl h
    simp [V] at this
  have hVθ : θ ≤ F.height V := by
    by_contra hn
    exact hVnP (hP _ (lt_of_not_ge hn))
  have hVÂ : F.height V < F.height Â := height_lt_of_index hF hcol (by simp [V]; omega)
  obtain ⟨v, hvc, hvh⟩ := C.bwd V (by simp [V]; exact hAc) hVθ
  have hva : a.1 = v.1 := Fin.ext (by rw [hvc, hac])
  -- `v` is above `a`
  have hav : a.2.val < v.2.val := by
    by_contra hn
    have hle : G.height v ≤ G.height a := height_le_of_index hG hva.symm (by omega)
    rw [hvh] at hle
    exact hVnP (hPd _ _ hle ha.1)
  -- `v` is below `a'`
  have hva' : v.2.val < a'.2.val := by
    apply index_lt_of_height_lt hG (hva.symm.trans ha'1.symm)
    rw [hvh, ← hÂh]
    exact hVÂ
  omega

end Generic

/-! ## The open statements -/

/-- **Open (column shape).** The highest node below `τ` of a column `y + w·i` of block
`i ≥ 1` is the top copy of the highest node below `τ` of `y`. -/
def CopyTop : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U : (Frame.ofMountain R).Node) (z : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y →
      TopBelow (Frame.ofMountain R) t.row U → TopBelow (Frame.ofMountain M) t.row z →
      TopCopy s n R M U z

/-- **Open.** One stored-parent step from the top copy of a node below `τ` of an inner
column: the stored parent of `Z⁺` stands for the stored parent of `z⁺`. -/
def CopyStepLower : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i → i ≤ n →
    ∀ (Z : (Frame.ofMountain R).Node) (z a : (Frame.ofMountain M).Node),
      root.column < z.1.val → z.1.val < M.size - 1 →
      Z.1.val = z.1.val + (M.size - 1 - root.column) * i →
      (Frame.ofMountain M).height z < t.row → TopCopy s n R M Z z →
      (Frame.ofMountain M).rawParent z = some a →
      ∃ A, (Frame.ofMountain R).rawParent Z = some A ∧ Cp s n R M t root i A a

/-- **Open.** The candidate of the top copy `U` of a node `z` with `row z < τ ≤ row z⁺`
(in a column `y` of block `i`, `x₀` included) stands for the candidate of `z`. -/
def CopyQLower : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U : (Frame.ofMountain R).Node) (z z' : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      ∃ a A, (Frame.ofMountain M).Q z = some a ∧ (Frame.ofMountain R).Q U = some A ∧
        Cp s n R M t root i A a

end OmegaY.Official.Recon.CrossUpperSim
