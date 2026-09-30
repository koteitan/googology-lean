import Googology.Trans.BMS.PoR.PSS.Main.VF

/-!
# `o[V_M]` is closed under bar (`proof/PROOF-2.md` §11.3; `proof/PROOF-3.md` §14.2)

**Bar-closure** (`barClosure`): for every one-term node `(t) ∈ V_M` with
`o(t) > 1`, `bar(o(t)) ∈ o[V_M]`.

For `t` not epsilon this is `barClosure_noneps` (§11.3, from Fact BAR and
Fact BAR₁, proved from [CW12] Def 5.1); for `t` epsilon it is `Bar_T` (`barEps`),
since `V_M` is closed under anchor.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-- **Bar-closure** of `o[V_M]` (`proof/PROOF-2.md` §11.3, `proof/PROOF-3.md` §14.2). -/
theorem barClosure {M : List Tm} (hM : StdOrd M) {t : Tm} (ht : InV M [t])
    (h1 : 1 < ordOf [t]) : ∃ w, InV M w ∧ ordOf w = barO (ordOf [t]) := by
  have hts : Std t := ((stdOrd_iff _).mp (stdOrd_of_inV hM ht)).2 t (by simp)
  have hcs : t.cs ≠ [] := by
    intro h
    have : t = Tm.node 0 [] := by rw [std_node_y hts, h]
    rw [this, ordOf_leaf'] at h1; exact lt_irrefl _ h1
  cases he : isEps t with
  | false => exact barClosure_noneps ht hts he hcs
  | true =>
    cases ha : anchor t with
    | none => exact ⟨[Tm.node 0 []], InV.one, by rw [(barEps hts he).2 ha, ordOf_leaf']⟩
    | some a => exact ⟨[a], InV.anc ht ha, ((barEps hts he).1 a ha).symm⟩

end Googology.Trans.PSS.Main
