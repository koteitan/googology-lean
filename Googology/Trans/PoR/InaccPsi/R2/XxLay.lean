import Googology.Trans.PoR.InaccPsi.R2.XxStep

/-!
# XxLay: THE OLD LEVELS OF THE LAYER `k` FROM THE SYSTEMS ALONE, AND WHAT THE SYSTEMS CONTAIN

With the frontier lemma over `Γ(k)` proved (`Xx.xxLayFront`, every `k + 1 < ε₀`), the reduction `Xk.xkLayLo_of`
needs only the systems `Xk.XkLaySys S k`:

* `xxLayLo_of_sys` (**`XkLaySys S k` ⇒ UPPER, LOWER, CapV at every range restart below `ι(Γ(φ(ℓ, Γ(k)+1))·ω)`,
  `ℓ < Γ(k)`**, `k + 1 < ε₀`);
* `xxLaySys_base` (**`XkLaySys S k` ⇒ UPPER, LOWER, CapV at every range restart below `ι(Γ(Γ(k))·ω)`**): for `k = 1`
  this is every range restart of region (A) (codes below `Γ(1)`, the (A3) part above `t₀` included), so the systems
  over `Γ(1)` are at least as strong as the location of all of region (A).

No new axiom.  New definitions: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xx

open Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gc
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **The old levels of the layer `k` from the systems alone** (`k + 1 < ε₀`). -/
theorem xxLayLo_of_sys {S : InaccSeq.{0}} {k : Ordinal.{0}} (hk : k + 1 < ε₀) (hS : XkLaySys S k) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG k ∧ l < Bt.iota S (gcG (veblen ℓ (gcG k + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l :=
  xkLayLo_of hS (xxLayFront S hk)

/-- **The systems over `Γ(k)` locate everything below `ι(Γ(Γ(k))·ω)`** (`k + 1 < ε₀`; `k = 1`: all of region (A)). -/
theorem xxLaySys_base {S : InaccSeq.{0}} {k : Ordinal.{0}} (hk : k + 1 < ε₀) (hS : XkLaySys S k) :
    ∀ l, Cd.CdRange S l → l < Bt.iota S (gcG (gcG k) * ω) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  intro l hr hl
  refine xxLayLo_of_sys hk hS l hr ⟨0, lt_of_le_of_lt zero_le (gcG_Om1_lt k),
    hl.trans_le (Bt.iota_mono (S := S) _ _ ?_)⟩
  refine mul_le_mul_left (gcG_le ?_) ω
  rw [veblen_zero_apply]
  exact (le_self_add : gcG k ≤ gcG k + 1).trans (right_le_opow _ one_lt_omega0)

end Googology.Trans.PoR.InaccPsi.R2.Xx
