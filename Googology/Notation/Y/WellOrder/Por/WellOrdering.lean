/-
Uses `OneY.RootIndexed.actual_expansion_wellFounded` and the `OneY.Numeric` corollaries of
Phyrion, 1Y-Well-Ordering-Lean (https://github.com/Phyrion1343/1Y-Well-Ordering-Lean,
Apache-2.0), adapted in `OneY/`.
Taken from koteitan, 1y-wo-por, `Por/WellOrdering.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.Model
import Googology.Notation.Y.WellOrder.OneY.RootIndexed.ExpansionWellFounded
import Googology.Notation.Y.WellOrder.OneY.Dynamics

/-!
# The four final 1-Y theorems

This file plugs the model of `Por.Model` into the core theorem
`OneY.RootIndexed.actual_expansion_wellFounded`. It proves:

  * every descending chain of 1-Y expansions terminates (`expansion_wellFounded`);
  * the generated 1-Y sequences are strictly well-ordered (`generated_strictWellOrder`);
  * the descendants of each sequence are strictly well-ordered
    (`descendants_strictWellOrder`);
  * any choice of copy counts reaches the empty sequence (`expansion_chain_reaches_empty`).

No constructible universe and no admissible ordinal is used.
-/

namespace Por

open OneY.RootIndexed (exprDiagram)

/-- Every descending chain of actual nonempty 1-Y expansions terminates. -/
theorem expansion_wellFounded : WellFounded (ZeroY.ExpansionStep OneY.Numeric.expand) :=
  let h := model_obligations
  OneY.RootIndexed.actual_expansion_wellFounded (α := Ord) (· < ·) (fun _ => True) R
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 (fun s => h.2.2.2.2.2 (exprDiagram s))

/-- The standard generated 1-Y sequence order is a strict well-order. -/
theorem generated_strictWellOrder :
    StrictWellOrder OneY.Numeric.GeneratedExpr OneY.Numeric.GeneratedLt :=
  OneY.Numeric.generated_strictWellOrder expansion_wellFounded

/-- Every fixed starting sequence's generated descendant order is a strict well-order. -/
theorem descendants_strictWellOrder (s : ZeroY.Expr) :
    StrictWellOrder (OneY.Numeric.Descendant s) OneY.Numeric.DescendantLt :=
  OneY.Numeric.descendants_strictWellOrder expansion_wellFounded s

/-- Arbitrary choices of finite copy counts still reach the empty sequence. -/
theorem expansion_chain_reaches_empty (chain : ℕ → ZeroY.Expr)
    (hNext : ∀ n, ∃ N, chain (n + 1) = OneY.Numeric.expand (chain n) N) :
    ∃ n, (chain n).values = [] :=
  OneY.Numeric.expansion_chain_reaches_empty expansion_wellFounded chain hNext

end Por

#print axioms Por.finiteReflection
#print axioms Por.initial_all
#print axioms Por.model_obligations
#print axioms Por.expansion_wellFounded
#print axioms Por.generated_strictWellOrder
#print axioms Por.descendants_strictWellOrder
#print axioms Por.expansion_chain_reaches_empty
