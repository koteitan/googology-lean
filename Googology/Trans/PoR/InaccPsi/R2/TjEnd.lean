import Googology.Trans.PoR.InaccPsi.R2.TjRoad

/-!
# Where the node derivation stops: levels `≥ Ω₂`

`W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(b + W^{X₀ + W^y})`, `φ = veblen`, codes = `Le.LeCl Ω₂ Q`.

* `tjSLC_lt_Om2` (**the strong level condition holds only at levels `a < Ω₂`**: `η = a` gives `a < T < Ω₂`; so at
  a node `φ(Ω₂, x + 1)` the members `φ(ζ, φ(Ω₂, x) + 1)`, `ζ < Ω₂` codes, are own only for `ζ` below the bottom
  `T`, and the hull-limit rule `Td.TdDer.hlim` (cofinality among ALL hull elements `y < W^E`) does not apply);
* `tjLevW_cof` (**the cofinality that does hold at the level `Ω₂`**: a code `w` over a strongly critical `Q` with
  `w < φ(Ω₂, x + 1)` lies below `φ(ζ, φ(Ω₂, x) + 1)` for a code `ζ < Q`; `Td.tdCl_levDec` at `c = Ω₂`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Td

variable {S : InaccSeq.{0}}

/-- **The strong level condition holds only at levels `a < Ω₂`.** -/
theorem tjSLC_lt_Om2 {b X0 a : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (h : TjSLC S b X0 e a) :
    a < Om (1 + 1) :=
  (h a le_rfl).trans (psi_lt (InR_Om_succ 1) _)

/-- **The cofinality at the level `Ω₂` among the codes**: a code `w < φ(Ω₂, x + 1)` over a strongly critical `Q` is
below `φ(ζ, φ(Ω₂, x) + 1)` for a code `ζ < Q`. -/
theorem tjLevW_cof {Q x w : Ordinal.{0}} (hQ : SC Q) (hw : LeCl (Om (1 + 1)) Q w)
    (hlt : w < veblen (Om (1 + 1)) (x + 1)) :
    ∃ ζ, LeCl (Om (1 + 1)) Q ζ ∧ ζ < Q ∧ w < veblen ζ (veblen (Om (1 + 1)) x + 1) := by
  obtain ⟨ζ, hζ, hζW, hwζ⟩ := tdCl_levDec hQ ldOm2_SC ldOm2_SC.isSuccLimit w hw hlt
  exact ⟨ζ, hζ, tdCl_lt hQ ζ hζ hζW, hwζ⟩

end Googology.Trans.PoR.InaccPsi.R2.Tj
