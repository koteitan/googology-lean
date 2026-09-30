import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

/-!
# Wilken's `ϑ`-terms `T¹`: syntax

This file gives the terms of Wilken's `T¹` (`τ = 1`, [W07a] Def 3.22) as a Lean
data type, with the syntactic operations of `por/tr.py`.  Nothing here speaks
about ordinals; the values are in `TR/Cited.lean`.

* A **principal term** `WP.th m ξ` is `ϑ_m(ξ)`.  Its argument `ξ` is a **sum**: a
  list of principal terms, the leftmost summand first (`[]` is `0`).
  `ϑ_0(0) = 1` (`one`) and `ϑ_m(0) = Ω_m` for `m ≥ 1` (`om m`).
* `starS m ξ` is the list of the `ϑ_m`-subterms of `ξ` that do not lie inside a
  `ϑ_k` with `k < m` (`pstar` of `tr.py`).  `ξ^{⋆_m}` of the paper is the
  largest of them, or `0` when there is none.
* `cmpF f p q` is the comparison of `tr.py` (`cmp_p`), with fuel `f`:
  - the level first;
  - on one level `m`, `ϑ_m(a) < ϑ_m(c)` iff
    `(a < c ∧ a^{⋆_m} < ϑ_m(c)) ∨ ϑ_m(a) ≤ c^{⋆_m}` ([W07a] Lemma 3.30).
  `cmpP p q = cmpF (size p + size q) p q`, and sums are compared
  lexicographically (`cmpS`).
* `addS`, `addAll`: the sum with absorption (`add`, `addall`).
* `omegaExp`, `logOmega`: `ω^Z` at level `m` and its inverse on principal
  terms (`omega_exp`, `log_omega`).
-/

namespace Googology.Trans.PSS.TR

/-- A principal term `ϑ_m(ξ)` of Wilken's `T¹`: the level `m` and the argument `ξ`,
a sum given as the list of its principal summands, the leftmost first. -/
inductive WP where
  | th (m : ℕ) (a : List WP)
  deriving Inhabited

mutual
/-- Decidable equality of principal terms. -/
def WP.decEq : (p q : WP) → Decidable (p = q)
  | .th m a, .th m' a' =>
    if hm : m = m' then
      match WP.decEqList a a' with
      | isTrue h => isTrue (by rw [hm, h])
      | isFalse h => isFalse (fun e => by cases e; exact h rfl)
    else isFalse (fun e => by cases e; exact hm rfl)

/-- Decidable equality of sums. -/
def WP.decEqList : (l l' : List WP) → Decidable (l = l')
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | a :: l, a' :: l' =>
    match WP.decEq a a' with
    | isTrue h =>
      match WP.decEqList l l' with
      | isTrue h' => isTrue (by rw [h, h'])
      | isFalse h' => isFalse (fun e => by cases e; exact h' rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
end

instance : DecidableEq WP := WP.decEq

/-- The level `m` of `ϑ_m(ξ)`. -/
def WP.lvl : WP → ℕ
  | .th m _ => m

/-- The argument `ξ` of `ϑ_m(ξ)`. -/
def WP.arg : WP → List WP
  | .th _ a => a

@[simp] theorem WP.lvl_th (m : ℕ) (a : List WP) : (WP.th m a).lvl = m := rfl
@[simp] theorem WP.arg_th (m : ℕ) (a : List WP) : (WP.th m a).arg = a := rfl

theorem WP.eta (p : WP) : WP.th p.lvl p.arg = p := by cases p; rfl

/-- `ϑ_0(0) = 1`. -/
def one : WP := .th 0 []

/-- `ϑ_m(0)`: `Ω_m` for `m ≥ 1`. -/
def om (m : ℕ) : WP := .th m []

/-! ## Induction and size -/

mutual
/-- Induction on principal terms. -/
theorem WP.ind {P : WP → Prop} (h : ∀ m a, (∀ q ∈ a, P q) → P (.th m a)) : ∀ p, P p
  | .th m a => h m a (WP.indList h a)

/-- Induction on principal terms, for the members of a sum. -/
theorem WP.indList {P : WP → Prop} (h : ∀ m a, (∀ q ∈ a, P q) → P (.th m a)) :
    ∀ a : List WP, ∀ q ∈ a, P q
  | [], _, hq => absurd hq List.not_mem_nil
  | d :: ds, q, hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact WP.ind h q
    · exact WP.indList h ds q hq
end

mutual
/-- The number of `ϑ`-symbols of a principal term. -/
def WP.size : WP → ℕ
  | .th _ a => WP.sizeS a + 1

/-- The number of `ϑ`-symbols of a sum. -/
def WP.sizeS : List WP → ℕ
  | [] => 0
  | p :: l => p.size + WP.sizeS l
end

@[simp] theorem WP.size_th (m : ℕ) (a : List WP) : (WP.th m a).size = WP.sizeS a + 1 := by
  rw [WP.size]

@[simp] theorem WP.sizeS_nil : WP.sizeS [] = 0 := by rw [WP.sizeS]

@[simp] theorem WP.sizeS_cons (p : WP) (l : List WP) :
    WP.sizeS (p :: l) = p.size + WP.sizeS l := by rw [WP.sizeS]

theorem WP.sizeS_append (l l' : List WP) : WP.sizeS (l ++ l') = WP.sizeS l + WP.sizeS l' := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]; omega

theorem WP.size_pos (p : WP) : 0 < p.size := by cases p; simp

theorem WP.size_le_sizeS {a : List WP} {q : WP} (h : q ∈ a) : q.size ≤ WP.sizeS a := by
  induction a with
  | nil => exact absurd h List.not_mem_nil
  | cons d ds ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h
      simp; omega

theorem WP.size_lt_of_mem {m : ℕ} {a : List WP} {q : WP} (h : q ∈ a) :
    q.size < (WP.th m a).size := by
  have := WP.size_le_sizeS h
  simp; omega

/-! ## Visible subterms -/

mutual
/-- The `ϑ_m`-subterms of `p` (itself included) not inside a `ϑ_k` with `k < m`. -/
def starP (m : ℕ) : WP → List WP
  | .th k a => if k < m then [] else if k = m then .th k a :: starS m a else starS m a

/-- The `ϑ_m`-subterms of the sum `ξ` not inside a `ϑ_k` with `k < m` (`pstar`). -/
def starS (m : ℕ) : List WP → List WP
  | [] => []
  | p :: l => starP m p ++ starS m l
end

@[simp] theorem starS_nil (m : ℕ) : starS m [] = [] := by rw [starS]

@[simp] theorem starS_cons (m : ℕ) (p : WP) (l : List WP) :
    starS m (p :: l) = starP m p ++ starS m l := by rw [starS]

theorem starP_th (m k : ℕ) (a : List WP) :
    starP m (.th k a) =
      if k < m then [] else if k = m then .th k a :: starS m a else starS m a := by
  rw [starP]

theorem starS_append (m : ℕ) (l l' : List WP) :
    starS m (l ++ l') = starS m l ++ starS m l' := by
  induction l with
  | nil => simp
  | cons p l ih => simp [ih]

/-! ## Comparison -/

/-- The lexicographic comparison of two sums, from a comparison of principal
terms; a proper prefix is smaller. -/
def lexCmp (c : WP → WP → Ordering) : List WP → List WP → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | p :: x, q :: y =>
    match c p q with
    | .eq => lexCmp c x y
    | o => o

/-- The comparison of principal terms of `tr.py` (`cmp_p`), with fuel.  On one
level `m`, `ϑ_m(a) < ϑ_m(c)` iff `(a < c ∧ a^{⋆_m} < ϑ_m(c)) ∨ ϑ_m(a) ≤ c^{⋆_m}`
([W07a] Lemma 3.30). -/
def cmpF : ℕ → WP → WP → Ordering
  | 0, _, _ => .eq
  | f + 1, p, q =>
    if p = q then .eq
    else if p.lvl < q.lvl then .lt
    else if q.lvl < p.lvl then .gt
    else
      let less : WP → WP → Bool := fun u v =>
        (lexCmp (cmpF f) u.arg v.arg == .lt &&
          (starS u.lvl u.arg).all (fun s => cmpF f s v == .lt)) ||
        (starS v.lvl v.arg).any (fun s => cmpF f u s != .gt)
      if less p q then .lt else if less q p then .gt else .eq

/-- The comparison of principal terms. -/
def cmpP (p q : WP) : Ordering := cmpF (p.size + q.size) p q

/-- The comparison of sums: lexicographic. -/
def cmpS (x y : List WP) : Ordering := lexCmp cmpP x y

/-! ## Sums -/

/-- The sum with absorption (`add` of `tr.py`): drop the last summands of `x`
that are below the first summand of `y`, then append `y`. -/
def addS (x y : List WP) : List WP :=
  match y with
  | [] => x
  | y0 :: _ => (x.reverse.dropWhile (fun p => cmpP p y0 == .lt)).reverse ++ y

/-- The sum of a list of sums, from the left (`addall`). -/
def addAll (xs : List (List WP)) : List WP := xs.foldl addS []

/-! ## `ω^Z` and `log_ω` -/

/-- `ϑ_m(Δ + η)` is an epsilon number above `Ω_m`: `p` has level `m` and the
first summand of its argument has level `≥ m + 1` (`is_eps_level`). -/
def isEpsLevel (p : WP) (m : ℕ) : Bool :=
  p.lvl == m &&
    match p.arg with
    | q :: _ => decide (m + 1 ≤ q.lvl)
    | [] => false

/-- `x = ε + n`: the first summand is an epsilon number of level `m` above `Ω_m`,
and the others are `1` (`is_eps_plus_n`). -/
def isEpsPlusN (x : List WP) (m : ℕ) : Bool :=
  match x with
  | p :: r => isEpsLevel p m && r.all (fun q => q == one)
  | [] => false

/-- `ω^x` as a principal term of level `m`, for `x` in `[Ω_m, Ω_{m+1})` (`m ≥ 1`)
or `x < Ω_1` (`m = 0`) (`omega_exp`; [WW11] Lemma 2.12(b)). -/
def omegaExp (x : List WP) (m : ℕ) : WP :=
  match x with
  | [] => .th m []
  | p :: r =>
    if r = [] ∧ isEpsLevel p m then p
    else if r ≠ [] ∧ isEpsPlusN (p :: r) m then .th m (p :: r).dropLast
    else if 1 ≤ m ∧ p = .th m [] then .th m r
    else .th m (p :: r)

/-- `1 + x`. -/
def onePlus (x : List WP) : List WP :=
  match x with
  | p :: _ => if p ≠ one then x else one :: x
  | [] => [one]

/-- `-1 + x`. -/
def minusOnePlus (x : List WP) : List WP :=
  match x with
  | p :: r => if p = one then r else x
  | [] => []

/-- `u` with `ω^u = p`, for a principal term `p` (`log_omega`). -/
def logOmega (p : WP) : List WP :=
  if isEpsLevel p p.lvl then [p]
  else if isEpsPlusN p.arg p.lvl then p.arg ++ [one]
  else if p.lvl = 0 then p.arg
  else addS [.th p.lvl []] p.arg

/-- `x = D + ρ`, with `D` the summands of level `≥ m` and `ρ` the rest
(`split_level`). -/
def splitLevel (x : List WP) (m : ℕ) : List WP × List WP :=
  (x.takeWhile (fun p => decide (m ≤ p.lvl)), x.dropWhile (fun p => decide (m ≤ p.lvl)))

/-! ## Display -/

mutual
/-- The notation of `show` in `tr.py`: `1`, `W`, `W2`, `t0(...)`, ... -/
partial def WP.show : WP → String
  | .th 0 [] => "1"
  | .th 1 [] => "W"
  | .th m [] => "W" ++ toString m
  | .th m a => "t" ++ toString m ++ "(" ++ WP.showS a ++ ")"

/-- The notation of a sum. -/
partial def WP.showS : List WP → String
  | [] => "0"
  | [p] => p.show
  | p :: l => p.show ++ "+" ++ WP.showS l
end

end Googology.Trans.PSS.TR
