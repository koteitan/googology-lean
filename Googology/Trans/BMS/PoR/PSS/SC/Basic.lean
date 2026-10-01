import PSS.Defs
import Bijectivity.Defs
import Mathlib.Data.List.TakeWhile

/-!
# Pair sequences as forests: parents, blocks, terms

This file sets up the tree view of a pair sequence `M : List (ℕ × ℕ)` used by
Theorem SC (`Googology/Trans/BMS/PoR/PSS/SC.lean`).  It follows §2 of `POR.md` and the
notation of §8b of `proof/COMB.md` in this directory.

* `xAt M j`, `yAt M j`: the two entries of column `j` (`0` out of range).
* `par M i`: the **row-0 parent** of column `i`, the largest `j < i` with
  `x_j < x_i`.  A column without a parent is a **root** (`roots M`).
* `children M u`, `ancs M u` (the proper row-0 ancestors, nearest first).
* `block l`: the first column of `l` followed by the columns up to the first
  one whose `x` is not larger.  `subtree M u = block (M.drop u)` is the
  contiguous block of `u` and its row-0 descendants.
* `sh c l` subtracts `c` from every `x`; `norm l` shifts `l` so that its first
  column has `x = 0`.  The **term** of `u` is `term M u = norm (subtree M u)`.
* Terms are compared by the lexicographic order `<ₚ` of pair sequences
  (`Bijectivity.ltPS`), with a proper prefix smaller.  `decLtPS` makes it
  decidable, so the conditions of Theorem SC can be evaluated on small inputs.
* `Tm`: a term as a finite tree with `y`-labels, `Tm.cols` its column
  sequence, `treeAt M u` the tree of column `u` and `forest M` the trees of
  the roots.  `Tm.Lt` is the order of `POR.md` §2 (the lexicographic order of
  the column sequences); `Tm.lt_node_iff` shows that it compares the root `y`
  first and then the child lists lexicographically.  The key step is
  `ltPS_flatten`: concatenations of blocks in normal form compare like the
  lists of blocks.

All functions are structural or fuelled, so `decide` evaluates them on small
inputs.
-/

namespace Googology.Trans.PSS.Forest

open Bijectivity (ltPS lePS)

/-- A pair sequence. -/
abbrev PS := List (ℕ × ℕ)

/-! ## Entries -/

/-- The first entry `x_j` of column `j` (`0` out of range). -/
def xAt (M : PS) (j : ℕ) : ℕ := (M.getD j (0, 0)).1

/-- The second entry `y_j` of column `j` (`0` out of range). -/
def yAt (M : PS) (j : ℕ) : ℕ := (M.getD j (0, 0)).2

theorem xAt_of_lt {M : PS} {j : ℕ} (h : j < M.length) : xAt M j = M[j].1 := by
  simp [xAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem yAt_of_lt {M : PS} {j : ℕ} (h : j < M.length) : yAt M j = M[j].2 := by
  simp [yAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem xAt_eq_entry (M : PS) (j : ℕ) : xAt M j = _root_.PSS.entry M 0 j := by
  unfold xAt _root_.PSS.entry
  cases h : M[j]? <;> simp [List.getD_eq_getElem?_getD, h]

theorem yAt_eq_entry (M : PS) (j : ℕ) : yAt M j = _root_.PSS.entry M 1 j := by
  unfold yAt _root_.PSS.entry
  cases h : M[j]? <;> simp [List.getD_eq_getElem?_getD, h]

/-! ## Row-0 parents, roots, children, ancestors -/

/-- The row-0 parent of column `i`: the largest `j < i` with `x_j < x_i`. -/
def par (M : PS) (i : ℕ) : Option ℕ :=
  ((List.range i).filter (fun j => decide (xAt M j < xAt M i))).getLast?

/-- Column `i` is a root: it has no row-0 parent. -/
def IsRoot (M : PS) (i : ℕ) : Prop := par M i = none

instance (M : PS) (i : ℕ) : Decidable (IsRoot M i) := by unfold IsRoot; infer_instance

/-- The roots of `M`, in order. -/
def roots (M : PS) : List ℕ := (List.range M.length).filter (fun i => par M i = none)

/-- The children of column `u`, in order. -/
def children (M : PS) (u : ℕ) : List ℕ :=
  (List.range M.length).filter (fun c => par M c = some u)

theorem par_spec {M : PS} {i p : ℕ} (h : par M i = some p) :
    p < i ∧ xAt M p < xAt M i ∧ ∀ j, p < j → j < i → xAt M i ≤ xAt M j := by
  unfold par at h
  set l := (List.range i).filter (fun j => decide (xAt M j < xAt M i)) with hl
  have hmem : p ∈ l := List.mem_of_getLast? h
  rw [hl, List.mem_filter, List.mem_range] at hmem
  refine ⟨hmem.1, by simpa using hmem.2, ?_⟩
  intro j hpj hji
  by_contra hlt
  push Not at hlt
  have hjl : j ∈ l := by
    rw [hl, List.mem_filter, List.mem_range]; exact ⟨hji, by simpa using hlt⟩
  -- `l` is sorted, so its last element is its largest
  have hsorted : l.Pairwise (· < ·) := (List.pairwise_lt_range).filter _
  obtain ⟨l', hl'⟩ := List.getLast?_eq_some_iff.mp h
  rw [hl'] at hsorted hjl
  rw [List.mem_append, List.mem_singleton] at hjl
  rcases hjl with hjl | rfl
  · exact absurd ((List.pairwise_append.mp hsorted).2.2 j hjl p (List.mem_singleton_self p))
      (by omega)
  · omega

theorem par_lt {M : PS} {i p : ℕ} (h : par M i = some p) : p < i := (par_spec h).1

/-- The proper row-0 ancestors of `i`, nearest first, with fuel. -/
def ancsAux (M : PS) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, i =>
    match par M i with
    | none => []
    | some p => p :: ancsAux M f p

/-- The proper row-0 ancestors of `i`, nearest first.  The fuel `i` suffices,
since parents have smaller indices. -/
def ancs (M : PS) (i : ℕ) : List ℕ := ancsAux M i i

/-! ## Blocks and terms -/

/-- The block at the head of `l`: the first column and the following columns
whose `x` is larger than its `x`. -/
def block : PS → PS
  | [] => []
  | p :: r => p :: r.takeWhile (fun q => decide (p.1 < q.1))

/-- `sh c l` subtracts `c` from the first entry of every column. -/
def sh (c : ℕ) (l : PS) : PS := l.map (fun q => (q.1 - c, q.2))

/-- `shUp c l` adds `c` to the first entry of every column. -/
def shUp (c : ℕ) (l : PS) : PS := l.map (fun q => (q.1 + c, q.2))

/-- Normalize `l` so that its first column has `x = 0`. -/
def norm (l : PS) : PS := sh (l.headD (0, 0)).1 l

/-- The term of the head of `l`: its block, normalized. -/
def termOf (l : PS) : PS := norm (block l)

/-- The subtree of column `u`: the contiguous block of `u` and its row-0
descendants. -/
def subtree (M : PS) (u : ℕ) : PS := block (M.drop u)

/-- The term `T(u)` of column `u`, normalized to `x = 0`. -/
def term (M : PS) (u : ℕ) : PS := termOf (M.drop u)

theorem term_eq (M : PS) (u : ℕ) : term M u = norm (subtree M u) := rfl

@[simp] theorem block_nil : block [] = [] := rfl

theorem block_cons (p : ℕ × ℕ) (r : PS) :
    block (p :: r) = p :: r.takeWhile (fun q => decide (p.1 < q.1)) := rfl

/-- If every later column of `l` is higher than the head, the block is all of `l`. -/
theorem block_cons_of_forall (p : ℕ × ℕ) (r : PS) (h : ∀ q ∈ r, p.1 < q.1) :
    block (p :: r) = p :: r := by
  rw [block_cons, List.takeWhile_eq_self_iff.mpr (by simpa using h)]

theorem termOf_cons_of_forall (p : ℕ × ℕ) (r : PS) (h : ∀ q ∈ r, p.1 < q.1) :
    termOf (p :: r) = sh p.1 (p :: r) := by
  rw [termOf, block_cons_of_forall p r h]; rfl

theorem sh_shUp (c : ℕ) (l : PS) : sh c (shUp c l) = l := by
  simp [sh, shUp, List.map_map, Function.comp_def]

theorem block_shUp (c : ℕ) (l : PS) : block (shUp c l) = shUp c (block l) := by
  cases l with
  | nil => rfl
  | cons p r =>
    simp only [shUp, List.map_cons, block_cons]
    congr 1
    rw [List.takeWhile_map]
    congr 1
    congr 1
    funext q
    simp

/-- Terms do not see a uniform shift of `x`. -/
theorem termOf_shUp (c : ℕ) (l : PS) : termOf (shUp c l) = termOf l := by
  unfold termOf norm
  rw [block_shUp]
  cases l with
  | nil => rfl
  | cons p r =>
    simp only [block_cons, shUp, List.map_cons, List.headD_cons, sh, List.map_map]
    congr 1
    · simp
    · apply List.map_congr_left
      intro q _
      simp; omega

/-! ## Deciding the lexicographic order -/

/-- `<ₚ` is decidable. -/
instance decLtPS : ∀ M N : PS, Decidable (ltPS M N)
  | [], [] => isFalse id
  | [], _ :: _ => isTrue trivial
  | _ :: _, [] => isFalse id
  | p :: M, q :: N =>
    haveI := decLtPS M N
    decidable_of_iff
      (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) ∨ (p.1 = q.1 ∧ p.2 = q.2 ∧ ltPS M N)) Iff.rfl

instance decLePS (M N : PS) : Decidable (lePS M N) := by unfold lePS; infer_instance

/-! ## The order on concatenated blocks -/

/-- `<ₚ` does not see a uniform raise of `x`. -/
theorem ltPS_shUp (c : ℕ) : ∀ l l' : PS, ltPS (shUp c l) (shUp c l') ↔ ltPS l l'
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | p :: l, q :: l' => by
    have ih := ltPS_shUp c l l'
    simp only [shUp] at ih
    simp only [shUp, List.map_cons, ltPS, ih, Nat.add_right_cancel_iff, Nat.add_lt_add_iff_right]

/-- Comparing `r ++ A` with `r' ++ B`, where every column of `r`, `r'` has
`x ≥ 1` and `A`, `B` are empty or start at `x = 0`. -/
theorem ltPS_append_tail {A B : PS} (hA : ∀ q ∈ A.head?, q.1 = 0)
    (hB : ∀ q ∈ B.head?, q.1 = 0) :
    ∀ {r r' : PS}, (∀ q ∈ r, 1 ≤ q.1) → (∀ q ∈ r', 1 ≤ q.1) →
      (ltPS (r ++ A) (r' ++ B) ↔ ltPS r r' ∨ (r = r' ∧ ltPS A B))
  | [], [], _, _ => by simp [ltPS]
  | [], q' :: r1, _, hr' => by
    have hq' := hr' q' (by simp)
    cases A with
    | nil => simp [ltPS]
    | cons p A' =>
      have hp := hA p (by simp)
      simp only [List.nil_append, List.cons_append, ltPS, true_or, iff_true]
      left; omega
  | q :: r0, [], hr, _ => by
    have hq := hr q (by simp)
    cases B with
    | nil => simp [ltPS]
    | cons p B' =>
      have hp := hB p (by simp)
      simp only [List.nil_append, List.cons_append, ltPS, reduceCtorEq, false_and, or_false,
        iff_false]
      omega
  | q :: r0, q' :: r1, hr, hr' => by
    have ih := ltPS_append_tail hA hB (r := r0) (r' := r1)
      (fun x hx => hr x (by simp [hx])) (fun x hx => hr' x (by simp [hx]))
    simp only [List.cons_append, ltPS, ih, List.cons.injEq, Prod.ext_iff]
    tauto

/-- A block in normal form: a first column `(0, y)`, then columns with `x ≥ 1`. -/
def NBlock (b : PS) : Prop := ∃ y r, b = (0, y) :: r ∧ ∀ q ∈ r, 1 ≤ q.1

theorem ltPS_append_block {a b A B : PS} (ha : NBlock a) (hb : NBlock b)
    (hA : ∀ q ∈ A.head?, q.1 = 0) (hB : ∀ q ∈ B.head?, q.1 = 0) :
    ltPS (a ++ A) (b ++ B) ↔ ltPS a b ∨ (a = b ∧ ltPS A B) := by
  obtain ⟨y, r, rfl, hr⟩ := ha
  obtain ⟨y', r', rfl, hr'⟩ := hb
  simp only [List.cons_append, ltPS, ltPS_append_tail hA hB hr hr', List.cons.injEq,
    Prod.mk.injEq]
  tauto

theorem head?_flatten_nblock : ∀ {as : List PS}, (∀ a ∈ as, NBlock a) →
    ∀ q ∈ as.flatten.head?, q.1 = 0
  | [], _ => by simp
  | a :: _, h => by
    obtain ⟨y, r, rfl, _⟩ := h a (by simp)
    simp

/-- **Concatenations of blocks compare like the lists of blocks.** -/
theorem ltPS_flatten : ∀ {as bs : List PS}, (∀ a ∈ as, NBlock a) → (∀ b ∈ bs, NBlock b) →
    (ltPS as.flatten bs.flatten ↔ List.Lex ltPS as bs)
  | [], [], _, _ => by simp [ltPS]
  | [], b :: _, _, hb => by
    obtain ⟨y, r, rfl, _⟩ := hb b (by simp)
    simp [ltPS]
  | a :: _, [], ha, _ => by
    obtain ⟨y, r, rfl, _⟩ := ha a (by simp)
    simp [ltPS]
  | a :: as, b :: bs, ha, hb => by
    have hA := head?_flatten_nblock (as := as) (fun x hx => ha x (by simp [hx]))
    have hB := head?_flatten_nblock (as := bs) (fun x hx => hb x (by simp [hx]))
    rw [List.flatten_cons, List.flatten_cons,
      ltPS_append_block (ha a (by simp)) (hb b (by simp)) hA hB,
      ltPS_flatten (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])),
      List.cons_lex_cons_iff]

/-! ## Terms as trees -/

/-- A term as a finite tree: a `y`-label and the list of child terms. -/
inductive Tm where
  | node (y : ℕ) (cs : List Tm)
  deriving Inhabited

mutual
/-- The column sequence of a tree, normalized to `x = 0`: the root `(0, y)`,
then the columns of the children, one level deeper. -/
def Tm.cols : Tm → PS
  | .node y cs => (0, y) :: shUp 1 (Tm.colsList cs)

/-- The columns of a list of trees, one after another. -/
def Tm.colsList : List Tm → PS
  | [] => []
  | c :: cs => c.cols ++ Tm.colsList cs
end

theorem Tm.colsList_eq : ∀ cs : List Tm, Tm.colsList cs = (cs.map Tm.cols).flatten
  | [] => rfl
  | c :: cs => by rw [Tm.colsList, Tm.colsList_eq cs]; rfl

theorem Tm.cols_node (y : ℕ) (cs : List Tm) :
    (Tm.node y cs).cols = (0, y) :: shUp 1 (cs.map Tm.cols).flatten := by
  rw [Tm.cols, Tm.colsList_eq]

theorem Tm.nblock_cols (t : Tm) : NBlock t.cols := by
  cases t with
  | node y cs =>
    refine ⟨y, _, Tm.cols_node y cs, ?_⟩
    intro q hq
    simp only [shUp, List.mem_map] at hq
    obtain ⟨q', _, rfl⟩ := hq
    simp

/-- The term order of `POR.md` §2: the lexicographic order of the column
sequences, with a proper prefix smaller. -/
def Tm.Lt (s t : Tm) : Prop := ltPS s.cols t.cols

/-- **The term order is the lexicographic order of `(y, child list)`**: first
the root `y`, then the lists of the children's column sequences,
lexicographically (a proper prefix is smaller). -/
theorem Tm.lt_node_iff (y y' : ℕ) (cs cs' : List Tm) :
    Tm.Lt (.node y cs) (.node y' cs') ↔
      y < y' ∨ (y = y' ∧ List.Lex ltPS (cs.map Tm.cols) (cs'.map Tm.cols)) := by
  unfold Tm.Lt
  rw [Tm.cols_node, Tm.cols_node]
  simp only [ltPS, lt_self_iff_false, false_or, true_and]
  rw [ltPS_shUp, ltPS_flatten (by simp [Tm.nblock_cols]) (by simp [Tm.nblock_cols])]

theorem mem_children {M : PS} {u c : ℕ} : c ∈ children M u ↔ c < M.length ∧ par M c = some u := by
  simp [children]

theorem lt_of_mem_children {M : PS} {u c : ℕ} (h : c ∈ children M u) : u < c :=
  par_lt (mem_children.mp h).2

/-- The tree of column `u` down to depth `f`. -/
def treeAux (M : PS) : ℕ → ℕ → Tm
  | 0, u => .node (yAt M u) []
  | f + 1, u => .node (yAt M u) ((children M u).map (treeAux M f))

/-- The tree of column `u`: its `y` and the trees of its children.  The depth
`M.length - u` suffices, since children have larger indices. -/
def treeAt (M : PS) (u : ℕ) : Tm := treeAux M (M.length - u) u

/-- The forest of `M`: the trees of its roots. -/
def forest (M : PS) : List Tm := (roots M).map (treeAt M)

end Googology.Trans.PSS.Forest
