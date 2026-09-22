import Googology.Notation.ExBuchholz.Order

/-!
# Standard forms

`OT` is the set of terms in standard form.  As in Buchholz, a principal term
`ψ_a(b)` is standard when every subterm of `b` that `ψ_a` can still reach lies
strictly below `b`, and a sum is standard when its principal terms are weakly
decreasing.

The collecting function `G` is Buchholz's, with the subscript generalised from
a numeral to a term: because the subscript `c` of an inner `ψ_c(d)` is itself a
term of the system, `c` is collected alongside `d`.
-/

namespace Googology.Notation.ExBuchholz.Term

/-- `G a t` collects the arguments that `ψ_a(·)` must bound: it descends into
every `ψ_c(d)` whose subscript satisfies `a ≤ c`, keeping `d`, and stops at the
ones with `c < a`.  The subscript `c` itself is *not* collected — only what is
reachable inside it. -/
def G (a : Term) : Term → List Term
  | nil => []
  | cons c d t =>
      (if a ≤ c then d :: (G a c ++ G a d) else []) ++ G a t

/-- The leading principal term of a term, if there is one. -/
def head? : Term → Option (Term × Term)
  | nil => none
  | cons a b _ => some (a, b)

/-- The principal terms do not increase across the head of `t`. -/
def descHead (a b : Term) (t : Term) : Bool :=
  match head? t with
  | none => true
  | some (c, d) => decide (psi c d ≤ psi a b)

/-- Standard form.  This is the notation system `OT`. -/
def isOT : Term → Bool
  | nil => true
  | cons a b t =>
      isOT a && isOT b && (G a b).all (fun x => decide (x < b))
        && isOT t && descHead a b t

/-- The standard forms, as a predicate. -/
def OT (x : Term) : Prop := isOT x = true

instance (x : Term) : Decidable (OT x) := by
  show Decidable (isOT x = true); infer_instance

/-! ### Sanity checks -/

#guard isOT t0
#guard isOT t1                      -- 1 = ψ_0(0)
#guard isOT t2                      -- 2 = 1 + 1
#guard isOT tw                      -- ω = ψ_0(1)
#guard isOT tW                      -- Ω = ψ_1(0)
#guard isOT (psi nil tW)            -- ε₀ = ψ_0(Ω)

-- `1 + ω` is not standard: the principal terms increase.
#guard !isOT (cons nil nil (cons nil t1 nil))

-- `ψ_0(ψ_0(Ω))` is not standard: `Ω` is not below the argument.
#guard !isOT (psi nil (psi nil tW))

end Googology.Notation.ExBuchholz.Term
