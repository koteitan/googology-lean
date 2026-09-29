import Googology.Trans.PSS.Main.TIota

/-!
# Lemma CI: `Coll_A ↔ t ∘ ι` (`proof/PROOF-3.md` §13.2, §14.1)

Let `N = (0, A)` be a standard epsilon root, `α = 𝒯(N)`, and `W` the last child of `N`.
The **region terms** of `W` (`InReg W`) are `W`, the truncations `(y, first i children)` of
region terms, and the children with `y ≥ 1` of region terms.

**CI** (value form): for a region term `s` with `y(s) = m ≥ 1`,

```
val 𝒯_{m-1}(Coll_A s) = val (t^α_τ ∘ ι_{τ,α})(𝒯_m s) = val J(𝒯_m s).
```
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- **Region terms** of `W`: `W`, the truncations of region terms, and the children with
`y ≥ 1` of region terms. -/
inductive InReg (W : Tm) : Tm → Prop
  | self : InReg W W
  | take {s : Tm} : InReg W s → ∀ i, InReg W (.node s.y (s.cs.take i))
  | child {s c : Tm} : InReg W s → c ∈ s.cs → 1 ≤ c.y → InReg W c

/-- **CI** (`proof/PROOF-3.md` §13.2, value form). -/
theorem ci {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
    {s : Tm} (hs : InReg (H.getLast hne) s) :
    WP.valS (jP (trTm (.node 0 H)) (trTm s)) = (trTm (coll H s)).val := by
  sorry

end Googology.Trans.PSS.Main
