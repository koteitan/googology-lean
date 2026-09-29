import Googology.Trans.PSS.Main.CI
import Googology.Trans.PSS.Main.BarEps

/-!
# `E1_T` (`proof/PROOF-2.md` §12.5)

For a standard epsilon root `N` with `α = 𝒯(N) = ϑ_0(Δ + η)` and fold inputs
`Y_1, …, Y_n`:

```
val J(Δ) + ζ_α = o(N) + o(Y_1) + ⋯ + o(Y_n),
```

where `J = t^α_τ ∘ ι_{τ,α}` (`Main/TIota.lean`).  With `lam_eq_jS` this is E1.  The proof
uses CI (`Main/CI.lean`) and NS (`lemmaNS`, `Main/BarEps.lean`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- **`E1_T`** (`proof/PROOF-2.md` §12.5). -/
theorem e1T {N : Tm} (hN : Std N) (heps : isEps N = true) :
    WP.valS (jS (trTm N) (argD (trTm N).arg)) + zetaT (trTm N) =
      ordOf [N] + ((foldInputs N).map fun Y => ordOf [Y]).sum := by
  sorry

end Googology.Trans.PSS.Main
