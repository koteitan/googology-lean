import Googology.Trans.BMS.PoR.PSS.SC

/-!
# The term operations of `Φ`: anchor, log, `Coll_A`, lh

This file defines the operations of `POR.md` §3 on pair-sequence terms, close
to `por/phi.py`.

* A **term** is a tree `Forest.Tm` (`SC/Basic.lean`): a `y`-label and the list
  of child terms.  Its matrix is `Tm.cols`, normalized to `x = 0`.  An
  **ordinal** is a list of root terms; its matrix is `mat ts`, the column
  sequences one after another.  A matrix with several roots is the sum of its
  root terms.
* Terms are compared by `Tm.Lt`, the lexicographic order `<ₚ` of their column
  sequences (a proper prefix is smaller).
* `addT a b` is the sum with absorption of `pss.py`: the last terms of `a` that
  are below the first term of `b` are dropped.  `addAll` folds it from the
  left.
* `isEps`: `N = (0, (C_1..C_k))` is **epsilon** if `k ≥ 1` and `y(C_k) ≥ 1`.
* `anchor N = (0, (C_1..C_{k-1}))` for `k ≥ 2`.
* `log0 u = (0, B^hi) + B^lo_1 + ⋯ + B^lo_r`, and `lam N` (`λ(N)`) from the
  last child.  `bigL N` is `𝓛 N` of `proof/COMB.md`: `()` for `N = 1`, `(N)`
  for epsilon `N`, `log0 N` otherwise.
* `coll A s` is `Coll_A(s)`: `y = 0` is kept, `y = 1` becomes the blob
  `(0, A + Coll_A(B))`, `y ≥ 2` is lowered by one.  `collSum A B` is
  `Coll_A(B_1) + ⋯ + Coll_A(B_m)`.
* `lhF f N` is the reach `lh(N)` computed with fuel `f`, and
  `lh N = lhF (fuelOf N) N`, where `fuelOf N` is one more than the number of
  nodes on a longest root-to-leaf path of the last child `W_N` (COMB §8,
  Theorem T).  `foldInputs N` is the list of the points
  `(0, A + Coll_A(D_1..D_i))` and `Coll_A(E_j)` that the fold `⊕` of an epsilon
  `N` visits.

All definitions are structural or fuelled, so they compute.
-/

namespace Googology.Trans.PSS.Forest

open Bijectivity (ltPS lePS)

/-! ## Terms -/

mutual
/-- Decidable equality of terms. -/
def Tm.decEq : (s t : Tm) → Decidable (s = t)
  | .node y cs, .node y' cs' =>
    if hy : y = y' then
      match Tm.decEqList cs cs' with
      | isTrue h => isTrue (by rw [hy, h])
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    else isFalse (fun e => by cases e; exact hy rfl)

/-- Decidable equality of lists of terms. -/
def Tm.decEqList : (l l' : List Tm) → Decidable (l = l')
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | a :: l, a' :: l' =>
    match Tm.decEq a a' with
    | isTrue h =>
      match Tm.decEqList l l' with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (fun e => by cases e; exact h' rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
end

instance : DecidableEq Tm := Tm.decEq

/-- The `y`-label of the root. -/
def Tm.y : Tm → ℕ
  | .node y _ => y

/-- The children. -/
def Tm.cs : Tm → List Tm
  | .node _ cs => cs

@[simp] theorem Tm.y_node (y : ℕ) (cs : List Tm) : (Tm.node y cs).y = y := rfl
@[simp] theorem Tm.cs_node (y : ℕ) (cs : List Tm) : (Tm.node y cs).cs = cs := rfl

theorem Tm.eta (t : Tm) : Tm.node t.y t.cs = t := by cases t; rfl

/-- The matrix of an ordinal: the column sequences of its root terms, one after
another. -/
def mat (ts : List Tm) : PS := Tm.colsList ts

@[simp] theorem mat_nil : mat [] = [] := rfl

theorem mat_cons (t : Tm) (ts : List Tm) : mat (t :: ts) = t.cols ++ mat ts := rfl

theorem mat_eq_flatten (ts : List Tm) : mat ts = (ts.map Tm.cols).flatten := Tm.colsList_eq ts

theorem mat_append (ts us : List Tm) : mat (ts ++ us) = mat ts ++ mat us := by
  simp [mat_eq_flatten]

theorem Tm.cols_eq (y : ℕ) (cs : List Tm) : (Tm.node y cs).cols = (0, y) :: shUp 1 (mat cs) := by
  rw [Tm.cols]; rfl

instance (s t : Tm) : Decidable (Tm.Lt s t) := decLtPS _ _

mutual
/-- The height: the number of nodes on a longest root-to-leaf path. -/
def Tm.height : Tm → ℕ
  | .node _ cs => Tm.heightList cs + 1

/-- The largest height in a list of terms. -/
def Tm.heightList : List Tm → ℕ
  | [] => 0
  | c :: cs => max c.height (Tm.heightList cs)
end

end Googology.Trans.PSS.Forest

namespace Googology.Trans.PSS.Phi

open Forest

/-! ## The sum with absorption -/

/-- The sum of `pss.py`: drop the last terms of `a` that are below the first term
of `b`, then append `b`. -/
def addT (a b : List Tm) : List Tm :=
  match b with
  | [] => a
  | b0 :: _ => (a.reverse.dropWhile (fun t => decide (Tm.Lt t b0))).reverse ++ b

/-- The sum of a list of terms, from the left. -/
def addAll (ts : List Tm) : List Tm := ts.foldl (fun r t => addT r [t]) []

/-! ## Epsilon terms, anchor, log -/

/-- `N = (0, (C_1..C_k))` is epsilon: `k ≥ 1` and `y(C_k) ≥ 1`. -/
def isEps : Tm → Bool
  | .node 0 cs =>
    match cs.getLast? with
    | some c => decide (1 ≤ c.y)
    | none => false
  | .node (_ + 1) _ => false

/-- `anchor(N) = (0, (C_1..C_{k-1}))` for `k ≥ 2`: the last child is dropped. -/
def anchor : Tm → Option Tm
  | .node 0 cs => if 2 ≤ cs.length then some (.node 0 cs.dropLast) else none
  | .node (_ + 1) _ => none

/-- `log(u) = (0, B^hi) + B^lo_1 + ⋯ + B^lo_r` for `u = (0, B)` not epsilon; the
first term is left out when `B^hi` is empty. -/
def log0 (u : Tm) : List Tm :=
  let hi := u.cs.filter (fun s => decide (1 ≤ s.y))
  let lo := u.cs.filter (fun s => decide (s.y = 0))
  addAll ((if hi.isEmpty then [] else [.node 0 hi]) ++ lo)

/-- `λ(N)` for `N` not epsilon, from the last child `u = C_k`: `(u)` if `u` is
epsilon, `log(u)` otherwise. -/
def lam (N : Tm) : List Tm :=
  match N.cs.getLast? with
  | some u => if isEps u then [u] else log0 u
  | none => []

/-- `𝓛 N` of `proof/COMB.md`: `()` for `N = 1`, `(N)` for epsilon `N`, and
`log(N)` otherwise. -/
def bigL (N : Tm) : List Tm :=
  if N.cs = [] then [] else if isEps N then [N] else log0 N

/-! ## The collapse `Coll_A` -/

mutual
/-- `Coll_A(s)`: `y = 0` is kept, `y = 1` becomes `(0, A + Coll_A(B))`, `y ≥ 2`
is lowered by one. -/
def coll (A : List Tm) : Tm → Tm
  | .node 0 B => .node 0 B
  | .node 1 B => .node 0 (addT A (addAll (collList A B)))
  | .node (y + 2) B => .node (y + 1) (addAll (collList A B))

/-- The list of the `Coll_A` images. -/
def collList (A : List Tm) : List Tm → List Tm
  | [] => []
  | b :: B => coll A b :: collList A B
end

/-- `Coll_A(B) = Coll_A(B_1) + ⋯ + Coll_A(B_m)`. -/
def collSum (A B : List Tm) : List Tm := addAll (collList A B)

/-! ## The reach `lh` -/

/-- The children of `W = C_k`, the last child of `N`. -/
def lastKids (N : Tm) : List Tm := (N.cs.getLast?.map Tm.cs).getD []

/-- The points of the fold of an epsilon `N = (0, A)`: the terms
`(0, A + Coll_A(D_1) + ⋯ + Coll_A(D_i))` for `i = 1..p`, where the `D` are the
children of `W` with `y ≥ 2`, then `Coll_A(E_j)` for the children `E` of `W`
with `y ≤ 1`. -/
def foldInputs (N : Tm) : List Tm :=
  let A := N.cs
  let ghi := (lastKids N).filter (fun s => decide (2 ≤ s.y))
  let glo := (lastKids N).filter (fun s => decide (s.y ≤ 1))
  (List.range ghi.length).map (fun i => .node 0 (addT A (collSum A (ghi.take (i + 1))))) ++
    glo.map (coll A)

/-- `S ⊕ Y`: append `Y` if `Y ≤ S_1`, else continue from the reach of `Y`. -/
def oplus (lhY : Tm → List Tm) (S : List Tm) (Y : Tm) : List Tm :=
  match S with
  | [] => lhY Y
  | s1 :: _ => if Tm.Lt s1 Y then lhY Y else addT S [Y]

/-- `lh(N)` with fuel `f`.  With no fuel left it returns `(N)`. -/
def lhF : ℕ → Tm → List Tm
  | 0, N => [N]
  | f + 1, N =>
    if N.y ≠ 0 ∨ N.cs = [] then [N]
    else if !isEps N then addT [N] (lam N)
    else (foldInputs N).foldl (oplus (lhF f)) [N, N]

/-- The fuel of `lh(N)`: one more than the number of nodes on a longest
root-to-leaf path of the last child `W_N` (COMB §8, Theorem T). -/
def fuelOf (N : Tm) : ℕ := (N.cs.getLast?.map Tm.height).getD 0 + 1

/-- **The reach** `lh(N)`: the largest point `b` with `N ≤₁ b`, as an ordinal
(a list of root terms). -/
def lh (N : Tm) : List Tm := lhF (fuelOf N) N

/-! ## Reading matrices as terms -/

/-- The terms of the roots of a matrix `M`. -/
def ofMat (M : PS) : List Tm := forest M

/-! ## Small examples

Matrices are written as column lists.  `N = (0,0)(1,1)(2,2)` has the term
`(0, ((1, ((2, ())))))`. -/

/-- `(0,0)(1,1)(2,2)`. -/
def exN : Tm := .node 0 [.node 1 [.node 2 []]]

example : exN.cols = [(0, 0), (1, 1), (2, 2)] := by decide
example : forest [(0, 0), (1, 1), (2, 2)] = [exN] := by decide
example : isEps exN = true := by decide
/-- `Coll_A` of the column `(1,1)(2,2)` at `N = (0,0)(1,1)(2,2)` is
`(0,0)(1,1)(2,2)(1,1)` (`POR.md` §3.4). -/
example : (coll exN.cs (.node 1 [.node 2 []])).cols = [(0, 0), (1, 1), (2, 2), (1, 1)] := by
  decide
/-- `lh((0,0)(1,1)) = (0,0)(1,1) + (0,0)(1,1) = ω^ω · 2`: its fold has no
inputs. -/
example : mat (lh (.node 0 [.node 1 []])) = [(0, 0), (1, 1), (0, 0), (1, 1)] := by decide
/-- `(0,0)(1,0)` is `ω`: not epsilon, `λ = log((0,0)) = ()`, so `lh = (ω)`. -/
example : mat (lh (.node 0 [.node 0 []])) = [(0, 0), (1, 0)] := by decide
/-- `(0,0)(1,0)(2,0)` is `ω^ω`: `λ = log((0,0)(1,0)) = (1)`, so `lh = ω^ω + 1`. -/
example : mat (lh (.node 0 [.node 0 [.node 0 []]])) = [(0, 0), (1, 0), (2, 0), (0, 0)] := by
  decide
/-- `log((0,0)(1,1)(1,0)) = (0,0)(1,1) + (0,0)`. -/
example : mat (log0 (.node 0 [.node 1 [], .node 0 []])) = [(0, 0), (1, 1), (0, 0)] := by decide
/-- The fold of `N = (0,0)(1,1)(2,2)` visits `Y_1 = (0, A + Coll_A((2,2))) =
(0,0)(1,1)(2,2)(1,1)`, which is above `N`, so it jumps: `lh(N) = lh(Y_1) = Y_1 · 2`. -/
example : mat (lh exN) =
    [(0, 0), (1, 1), (2, 2), (1, 1), (0, 0), (1, 1), (2, 2), (1, 1)] := by
  decide
example : anchor (.node 0 [.node 1 [], .node 1 []]) = some (.node 0 [.node 1 []]) := by decide
/-- `𝓛((0,0)(1,1)) = ((0,0)(1,1))`: it is epsilon. -/
example : mat (bigL (.node 0 [.node 1 []])) = [(0, 0), (1, 1)] := by decide
/-- `𝓛((0,0)(1,0)(1,0)) = log = (0,0)(0,0)`: `ω^2 = ω^{1+1}`. -/
example : mat (bigL (.node 0 [.node 0 [], .node 0 []])) = [(0, 0), (0, 0)] := by decide
/-- `𝓛((0,0)(1,1)(1,0)(2,1)) = (0,0)(1,1) + (0,0)(1,1)`: the `y = 0` child `(1,0)(2,1)`
reads `(0,0)(1,1)`, equal to `(0, H)`, so nothing is absorbed. -/
example : mat (bigL (.node 0 [.node 1 [], .node 0 [.node 1 []]])) =
    [(0, 0), (1, 1), (0, 0), (1, 1)] := by decide
example : fuelOf exN = 3 := by decide

end Googology.Trans.PSS.Phi
