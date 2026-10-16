import Googology.Trans.PoR.InaccPsi.R2.SkelC
import Googology.Trans.PoR.InaccPsi.R2.OPhi

/-!
# Lower bounds for `ν_C` from Theorem BLK^O

Theorem BLK^O says that every `<₂`-pair with right end below `υ_B` is standard (`B ≤ Λ_ε`), so
`υ_B ≤ ν_C`; in particular `υ_{Φ_Γ+ω²} ≤ ν_C`.  Hence the reach-free description of `SkelC`
(D1–D3, Lemma CAP) applies at least on `[0, υ_B)`.

* `ups_le_nuC` (`υ_B ≤ ν_C` for `B ≤ Λ_ε`), `upsPhi1_le_nuC` (`υ_{Φ_Γ+ω²} ≤ ν_C`),
  `PhiG_lt_nuC` (`Φ_Γ < ν_C`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_ε` (`ω² ∣ B`, `B < Ω₁`): the pairs below `υ_B` are standard
(Theorem BLK^O (i)). -/
theorem ups_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkO hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **`υ_{Φ_Γ+ω²} ≤ ν_C`**. -/
theorem upsPhi1_le_nuC : upsilon (PhiG + ω * ω) ≤ nuC := by
  refine le_nuC (ups_lt_Om1 _ (Om1_add_lt PhiG_lt_Om1 ww_lt_Om1)).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := (blkPhi1.1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **`Φ_Γ < ν_C`**. -/
theorem PhiG_lt_nuC : PhiG < nuC := by
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  refine lt_of_lt_of_le ?_ upsPhi1_le_nuC
  calc PhiG = upsilon PhiG := PhiG_ups.symm
    _ < upsilon (PhiG + ω * ω) := upsilon_normal.strictMono (lt_add_of_pos_right _ hww)

end Googology.Trans.PoR.InaccPsi.R2
