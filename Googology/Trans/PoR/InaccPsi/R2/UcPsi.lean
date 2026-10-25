import Googology.Trans.PoR.InaccPsi.R2.UcFn
import Googology.Trans.PoR.InaccPsi.R2.TwBase

/-!
# The first instances of `ψ_{Ω₂}(Ω₂^γ·(1 + D)) = H_γ(D)`

`ψ = ψ_{Ω₂} = S.psi · Ω₂`, `w_γ = Ω₂^γ = Le.leWe γ`, `F_β = Rh.rhF β`, `H_γ = Uc.ucH γ` (`R2.UcH`), `X = Tl.tlX`.
`H_γ` starts where `ψ(Ω₂^γ)` does:

* `ucS_eq_twS` (**the start of `H_β` inside `F_β` is `Tw.twS β`** for `1 ≤ β < X`);
* `uc_psiU_eq_H` (**`ψ(Ω₂^β) = H_β(0)`** for `1 ≤ β < X`), `uc_psiW_eq_H` (**`ψ(Ω₂^{Ω₂}) = H_{Ω₂}(0)`**);
* `uc_psiU_mul_H` (**`ψ(Ω₂^β·(1 + D)) = H_β(D)`** for `1 ≤ β < X`, `D < Ω₂` with `d < H_β(d)` for every `d ≤ D`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- **The start of `H_β` inside `F_β` is `twS β`** for `1 ≤ β < X`. -/
theorem ucS_eq_twS (S : InaccSeq.{0}) {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβX : β < tlX) : ucS β = Tw.twS β := by
  obtain ⟨-, hgt, hle⟩ := Tw.tw_psiU_s (S := S) h1 hβX
  rw [← Rj.rj_Om1] at hgt hle
  have hmax : max Om1 β < rhF β (Tw.twS β) := by
    rcases le_or_gt β Om1 with hβ | hβ
    · rw [max_eq_left hβ]; exact hgt
    · rw [max_eq_right hβ.le]
      have h0 : Tw.twS β = 0 := by
        unfold Tw.twS
        rw [← Rj.rj_Om1, if_neg (not_lt.2 hβ.le), if_neg hβ.ne']
      rw [h0]; exact tl_lt_G hβ hβX
  refine le_antisymm (ucS_le hmax) (not_lt.1 fun hlt => ?_)
  have h := hle _ hlt
  exact absurd ((le_max_left _ _).trans_lt (ucS_spec β)) (not_lt.2 h)

/-- **`ψ(Ω₂^β) = H_β(0)`** for `1 ≤ β < X`. -/
theorem uc_psiU_eq_H {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβX : β < tlX) :
    S.psi (leWe β) (Om (1 + 1)) = ucH β 0 := by
  rw [ucH_eq_F (hβX.trans tlX_lt_OmTwo), add_zero, ucS_eq_twS S h1 hβX]
  exact (Tw.tw_psiU_s h1 hβX).1

/-- **`ψ(Ω₂^{Ω₂}) = H_{Ω₂}(0)`** (`= X`). -/
theorem uc_psiW_eq_H : S.psi (leWe (Om (1 + 1))) (Om (1 + 1)) = ucH OmTwo 0 := by
  rw [ucH_Om2_zero]; exact Ts.ts_psiW_eq_X

/-- **`ψ(Ω₂^β·(1 + D)) = H_β(D)`** for `1 ≤ β < X` and `D < Ω₂` with `d < H_β(d)` for every `d ≤ D`. -/
theorem uc_psiU_mul_H {β D : Ordinal.{0}} (h1 : 1 ≤ β) (hβX : β < tlX) (hD : D < Om (1 + 1))
    (hcond : ∀ d, d ≤ D → d < ucH β d) :
    D < S.psi (leWe β * (1 + D)) (Om (1 + 1)) ∧ S.psi (leWe β * (1 + D)) (Om (1 + 1)) = ucH β D := by
  have hβ2 : β < OmTwo := hβX.trans tlX_lt_OmTwo
  have hc : rhF β (ucS β) = S.psi (leWe β) (Om (1 + 1)) := by
    rw [uc_psiU_eq_H h1 hβX, ucH_eq_F hβ2, add_zero]
  have h := Ts.ts_psiU_mul (S := S) (Tw.tw_lt_psiU β hβX) hc hD fun d hd => by
    have := hcond d hd; rwa [ucH_eq_F hβ2] at this
  rw [ucH_eq_F hβ2]; exact h

end Googology.Trans.PoR.InaccPsi.R2.Uc
