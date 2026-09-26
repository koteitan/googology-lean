/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossKinds.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossLex
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Columns

set_option backward.do.legacy false

/-!
# `CrossLexHolds` split by the origin of the node above

In a new column `X` of a splice run, the node `(X, j + 1)` is made from the `j`-th emitted
node of the call of `copyColumn` that made column `X`. Its origin (`Classification.Origin`,
`Trace.lean`) is one of

* `plain src`: a level-1 item without a copied root row;
* `clean src false`: a copy of the root row `C`, without a cut bottom;
* `clean src true`: a copy of the root row `C` in a gap slot (*cut*, the flag `b = 1`);
* `upper src`: the upper part (rows `≥ τ`).

`OriginAt` records this origin together with the run data. Every real node of a new column
has one (`originAt_exists`). `CrossLexFor K` is `CrossLexHolds` for the nodes `u` whose
upper neighbour `u⁺` has an origin of kind `K`; the four kinds give `CrossLexHolds`
(`crossLexHolds_of_kinds`), hence `ChainHolds` with `ParentBelowHolds`
(`chainHolds_of_kinds`).

The cut kind does not occur: `crossLexFor_cut` derives it from `CutPredHolds`, a statement
about the emitted lists alone (every cut copy of a root-row node follows a copy of the same
node with the same emitted leg column). Then the node `u` below a cut node `u⁺` has its
stored parent in the column of the stored parent of `u⁺`, so `Q u` is in the column of `p`.

## Numerical check

On the 474 fixtures (`CrossLexTest.lean`) the 1062 cross nodes split as: `u⁺` plain 324,
clean 30, cut 0, upper 708; `CutPred` holds for every copied column (7181 cut emits).
`reference/official/cross-lex.cjs` on the standard samples S1–S3, S6 (`n = 1,2,3`):

| `u⁺` (`u`) | cross nodes |
|---|---:|
| plain (plain) | 17598 |
| plain (clean) | 2067 |
| plain (cut) | 5631 |
| clean (plain) | 1602 |
| upper (plain) | 73392 |
| upper (upper) | 10584 |

and 925614 cut nodes, each above a copy of the same root-row node. The random legal sample
(`--random 20000,10,10,7`) adds the pair upper (cut), 24 nodes.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame Classification

/-- The node `(X, j + 1)` of the output `R` of `s[n]` has origin `o`: it is made from the
`j`-th traced emit of the call of `copyColumn` that made the column `X = x + w·i`. -/
def OriginAt (s : List Nat) (n : Nat) (R : Mountain) (X j : Nat) (o : Origin) : Prop :=
  ∃ (M : Mountain) (col : Column) (t : Cell) (root : Ref) (x i : Nat)
    (es : List (Emit × Origin)) (em : Emit),
    Canonical.build s = .ok M ∧ M[M.size - 1]? = some col ∧ col.back? = some t ∧
    t.left = some root ∧ root.column < M.size - 1 ∧
    x ∈ blockColumns root.column (M.size - 1) n i ∧
    X = x + (M.size - 1 - root.column) * i ∧
    emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (official t.row) = .ok es ∧
    (∃ colX, R[X]? = some colX ∧
      copyColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (official t.row) = .ok colX ∧
      assemble (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
        (es.map Prod.fst) = .ok colX) ∧
    es[j]? = some (em, o)

/-- **Every real node of a new column has an origin.** -/
theorem originAt_exists {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {v : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ v.1.val) (hv : Real v) :
    ∃ o, OriginAt s n R v.1.val (v.2.val - 1) o := by
  obtain ⟨M, hM, hcases⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  have hvR : v.1.val < R.size := v.1.isLt
  rcases hcases with ⟨rfl, rfl⟩ | ⟨hne, col, t, hcol, ht, hcase⟩
  · have h0 : R.size = 0 := by rw [hMs]; rfl
    omega
  · rcases hcase with ⟨_, rfl⟩ | ⟨hτ, hn, root, hroot, hcr, _, _⟩
    · simp at hvR
      omega
    · obtain ⟨_, hinv⟩ := expandDiagram_splice hrun hM hcol ht
        (by rintro (h | h) <;> contradiction) hroot
      obtain ⟨_, hle, hall⟩ := hinv
      obtain ⟨i, x, _, hxb, hX, hcopy⟩ := hall v.1.val hvR (by omega)
      obtain ⟨es, hes, hasm⟩ := copyColumn_emitsT hcopy
      obtain ⟨hsize, _⟩ := assemble_spec hasm
      have hj : v.2.val - 1 < es.length := by
        have h1 := v.2.isLt
        change v.2.val < R[v.1.val].size at h1
        simp only [List.length_map] at hsize
        unfold Real at hv
        omega
      refine ⟨es[v.2.val - 1].2, M, col, t, root, x, i, es, es[v.2.val - 1].1, hM, hcol, ht,
        hroot, hcr, hxb, hX, hes, ⟨R[v.1.val], Array.getElem?_eq_getElem hvR, hcopy, hasm⟩, ?_⟩
      simp [List.getElem?_eq_getElem hj]

/-! ## The four kinds -/

def IsPlain (o : Origin) : Prop := ∃ r, o = .plain r
def IsClean (o : Origin) : Prop := ∃ r, o = .clean r false
def IsCut (o : Origin) : Prop := ∃ r, o = .clean r true
def IsUpper (o : Origin) : Prop := ∃ r, o = .upper r

theorem origin_kinds (o : Origin) : IsPlain o ∨ IsClean o ∨ IsCut o ∨ IsUpper o := by
  cases o with
  | plain r => exact Or.inl ⟨r, rfl⟩
  | clean r b =>
    cases b
    · exact Or.inr (Or.inl ⟨r, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨r, rfl⟩))
  | upper r => exact Or.inr (Or.inr (Or.inr ⟨r, rfl⟩))

/-- **Open (per kind).** `CrossLexHolds` for the nodes `u` whose upper neighbour `u⁺` has an
origin of kind `K`. -/
def CrossLexFor (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length - 1 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∃ c cp, RawChain (Frame.ofMountain R) q c ∧
        (Frame.ofMountain R).rawParent c = some p ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
        Lex (Frame.ofMountain R) up cp

/-- **`CrossLexHolds` from the four kinds.** -/
theorem crossLexHolds_of_kinds (hP : CrossLexFor IsPlain)
    (hC : CrossLexFor IsClean) (hK : CrossLexFor IsCut)
    (hU : CrossLexFor IsUpper) : CrossLexHolds := by
  intro s n R hrun u p q hx hu hraw hq hcol
  obtain ⟨up, hup, _⟩ := rawParent_spec hraw
  obtain ⟨hc1, _⟩ := upper_spec hup
  have hx' : s.length - 1 ≤ up.1.val := by rw [hc1]; exact hx
  obtain ⟨o, ho⟩ := originAt_exists hrun hx' (real_of_upper hup)
  have key : ∀ K, CrossLexFor K → K o →
      ∃ c up' cp, RawChain (Frame.ofMountain R) q c ∧
        (Frame.ofMountain R).rawParent c = some p ∧
        (Frame.ofMountain R).upper u = some up' ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height up' = (Frame.ofMountain R).height cp ∧
        Lex (Frame.ofMountain R) up' cp := by
    intro K hK hKo
    obtain ⟨c, cp, h1, h2, h3, h4, h5⟩ := hK s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo
    exact ⟨c, up, cp, h1, h2, hup, h3, h4, h5⟩
  rcases origin_kinds o with h | h | h | h
  · exact key _ hP h
  · exact key _ hC h
  · exact key _ hK h
  · exact key _ hU h

/-- **`ChainHolds` from `ParentBelowHolds` and the four kinds.** -/
theorem chainHolds_of_kinds (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hC : CrossLexFor IsClean) (hK : CrossLexFor IsCut)
    (hU : CrossLexFor IsUpper) : ChainHolds :=
  chainHolds_of_lex hPB (crossLexHolds_of_kinds hP hC hK hU)

/-- **`CrossChainHolds` from `ParentBelowHolds` and the four kinds.** -/
theorem crossChainHolds_of_kinds (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hC : CrossLexFor IsClean) (hK : CrossLexFor IsCut)
    (hU : CrossLexFor IsUpper) : CrossChainHolds :=
  crossChainHolds_of_lex hPB (crossLexHolds_of_kinds hP hC hK hU)

/-! ## The cut kind from the emitted lists -/

/-- In an emitted list, every cut copy of a root-row node follows a copy of the same node
with the same emitted leg column. -/
def CutPred (es : List (Emit × Origin)) : Prop :=
  ∀ j (hj : j < es.length) r, es[j].2 = .clean r true →
    ∃ (h : 0 < j) (b : Bool), es[j - 1].2 = .clean r b ∧
      es[j - 1].1.leftColumn = es[j].1.leftColumn

/-- **Open.** `CutPred` for the emitted lists of the copied columns of every run. -/
def CutPredHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (col : Column) (t : Cell) (root : Ref) (x i : Nat)
      (es : List (Emit × Origin)),
      Canonical.build s = .ok M → M[M.size - 1]? = some col → col.back? = some t →
      t.left = some root → root.column < M.size - 1 →
      x ∈ blockColumns root.column (M.size - 1) n i →
      emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
      CutPred es

/-- The cell of a node read from the column that contains it. -/
theorem frame_cell_of {R : Mountain} {v : (Frame.ofMountain R).Node} {colX : Column}
    {cell : Cell} (hX : R[v.1.val]? = some colX) (hc : colX[v.2.val]? = some cell) :
    (Frame.ofMountain R).cell v = cell := by
  obtain ⟨c, i⟩ := v
  change R[c.val][i.val] = cell
  simp only [Array.getElem?_eq_getElem (show c.val < R.size from c.isLt),
    Option.some.injEq] at hX
  subst hX
  simpa only [Array.getElem?_eq_getElem (show i.val < R[c.val].size from i.isLt),
    Option.some.injEq] using hc

/-- **The cut kind.** If every cut copy follows a copy of the same root-row node, the node
below a cut node has its stored parent in the column of the stored parent of the cut node,
so the candidate is in the column of the parent and the cross case does not occur. -/
theorem crossLexFor_cut (h : CutPredHolds) : CrossLexFor IsCut := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hK
  exfalso
  apply hcol
  obtain ⟨r, rfl⟩ := hK
  obtain ⟨M, col, t, root, x, i, es, em, hM, hcolM, ht, hroot, hcr, hxb, hX, hes,
    ⟨colX, hRX, _, hasm⟩, hj⟩ := ho
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hjlt : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, Origin.clean r true) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  rw [hX] at hes
  obtain ⟨hpos, b, hprev, hleft⟩ := h s n R hrun M col t root x i es hM hcolM ht hroot hcr hxb hes
    (up.2.val - 1) hjlt r (by rw [hej])
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) up.1.val
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  have hlen : (es.map Prod.fst).length = es.length := List.length_map _
  -- the cell of `u⁺`
  obtain ⟨cup, hcup, _, refp, hlp, hcolp⟩ := hcells (up.2.val - 1) (by rw [hlen]; exact hjlt)
  -- the cell of `u`
  obtain ⟨cu, hcu, _, refq, hlq, hcolq⟩ := hcells (up.2.val - 1 - 1) (by rw [hlen]; omega)
  have hRX' : R[up.1.val]? = some colX := hRX
  have hcellup : (Frame.ofMountain R).cell up = cup := by
    refine frame_cell_of hRX' ?_
    rw [show up.2.val = up.2.val - 1 + 1 by omega]
    exact hcup
  have hRXu : R[u.1.val]? = some colX := by rw [← hup1]; exact hRX'
  have hcellu : (Frame.ofMountain R).cell u = cu := by
    refine frame_cell_of hRXu ?_
    rw [show u.2.val = up.2.val - 1 - 1 + 1 by unfold Real at hu; omega]
    exact hcu
  -- the two left columns agree
  have hlegs : legColumn ctx (es.map Prod.fst)[up.2.val - 1 - 1] =
      legColumn ctx (es.map Prod.fst)[up.2.val - 1] := by
    simp only [List.getElem_map]
    unfold legColumn
    rw [hleft]
  -- the column of `p`
  obtain ⟨up', hup', hlup⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  rw [hcellup, hlp] at hlup
  have hrefp : refp = Frame.ref p := Option.some.inj hlup
  -- the column of `q`
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  obtain ⟨lft, hlft, _, _, hql, _⟩ := Q_spec hB.valid.toOrdered hq
  rw [hcellu, hlq] at hlft
  have hrefq : refq = Frame.ref lft := Option.some.inj hlft
  apply Fin.ext
  rw [hql]
  have e1 : lft.1.val = refq.column := by rw [hrefq]; rfl
  have e2 : p.1.val = refp.column := by rw [hrefp]; rfl
  rw [e1, e2, hcolq, hcolp, hlegs]

/-- **`ChainHolds` from `ParentBelowHolds`, `CutPredHolds` and three kinds.** -/
theorem chainHolds_of_three (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hC : CrossLexFor IsClean) (hK : CutPredHolds) (hU : CrossLexFor IsUpper) : ChainHolds :=
  chainHolds_of_kinds hPB hP hC (crossLexFor_cut hK) hU

/-- **`CrossChainHolds` from `ParentBelowHolds`, `CutPredHolds` and three kinds.** -/
theorem crossChainHolds_of_three (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hC : CrossLexFor IsClean) (hK : CutPredHolds) (hU : CrossLexFor IsUpper) :
    CrossChainHolds :=
  crossChainHolds_of_kinds hPB hP hC (crossLexFor_cut hK) hU

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.crossLexFor_cut
#print axioms OmegaY.Official.Recon.crossChainHolds_of_three
#print axioms OmegaY.Official.Recon.chainHolds_of_kinds
#print axioms OmegaY.Official.Recon.crossChainHolds_of_kinds
