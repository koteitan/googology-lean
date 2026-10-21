import Googology.Trans.PoR.InaccPsi.R2.LcCap

/-!
# LC-STRICT from the closure of the reading under the countable operations of the hull

`Lc.LcStrictAt S λ k` is `H(η_λ + G(θ_k·ω²)) ≤ Θ_λ(G(θ_{k+1}·ω²))`, `H(ζ) = ψ_{Ω₁}(A_ζ)`,
`A_ζ = Ω_ω + θ·ζ`.  `Lc.lcStrict_of_embed` reduces it to an order embedding into the hull.  A second
reduction, from the definition of `ψ` (`InaccSeq.psi_le_of_good`): with `A = A_{η_λ + G(θ_k·ω²)}` and
`β = Θ_λ(G(θ_{k+1}·ω²))`, LC-STRICT holds as soon as every countable member of `Cl(A, β)` is below `β`
(`lrStrict_of_closed`).  The hypothesis is satisfiable: it holds when `β = ψ_{Ω₁}(A)`, which is the
docs' identity `Θ(G(θ_{k+1}·ω²)) = H(η + G(θ_k·ω²))` (`lrClosed_of_eq`, F4 of `ψ`); it does not
follow from LC-STRICT alone (`β` need not be closed under `+`), so it is a sufficient condition.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The closure of `β` below `Ω₁` under the operations of `Cl(A, ·)`. -/
def LrClosedAt (S : InaccSeq.{0}) (A β : Ordinal.{0}) : Prop :=
  ∀ x ∈ S.CSet A β, x < Om (1 : Ordinal.{0}) → x < β

/-- **LC-STRICT from the closure of `β = Θ_λ(G(θ_{k+1}·ω²))`.** -/
theorem lrStrict_of_closed {l : Ordinal.{0}} {k : ℕ}
    (h : LrClosedAt S (ConjT.Aη S (cdEta S l + Lc.lcG S (Lc.lcTh S k * ω ^ 2)))
      (cdTheta S l (Lc.lcG S (Lc.lcTh S (k + 1) * ω ^ 2)))) :
    Lc.LcStrictAt S l k :=
  psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) h

/-- **The closure hypothesis holds at `β = ψ_{Ω₁}(A)`** (so it is satisfiable; F4). -/
theorem lrClosed_of_eq {A β : Ordinal.{0}} (h : β = S.psi A (Om 1)) : LrClosedAt S A β := by
  subst h
  exact fun x hx hx1 => lt_psi_of_mem Low.InR_Om_one hx hx1

end Googology.Trans.PoR.InaccPsi.R2.Lr
