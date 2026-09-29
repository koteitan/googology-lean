import Googology.Trans.PSS.Main.VF

/-!
# `o[V_M]` is closed under bar (`proof/PROOF-2.md` §11.3; `proof/PROOF-3.md` §14.2)

**Bar-closure** (`barClosure`): for every one-term node `(t) ∈ V_M` with
`o(t) > 1`, `bar(o(t)) ∈ o[V_M]`.

The paper's proof: for `t` not epsilon, §11.3 (Fact BAR from [CW12] Def 5.1,
Lemmas 5.4, 5.10 and [W07a] Lemmas 4.3, 4.9, with Lemma R); for `t` epsilon,
`Bar_T` (§13.3, §14.2: `bar(𝒯 t) = 𝒯(anchor t)`, or `1`, from Mono\*, SC, NS, CL,
EL, FD, LV, Lemma N⁺ and [W07a] Lemmas 3.30, 4.9, 6.4, 6.5) with Lemma TR, and
`V_M` is closed under anchor.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-- **Bar-closure** of `o[V_M]` (`proof/PROOF-2.md` §11.3, `proof/PROOF-3.md` §14.2). -/
theorem barClosure {M : List Tm} (hM : StdOrd M) {t : Tm} (ht : InV M [t])
    (h1 : 1 < ordOf [t]) : ∃ w, InV M w ∧ ordOf w = barO (ordOf [t]) := by
  sorry

end Googology.Trans.PSS.Main
