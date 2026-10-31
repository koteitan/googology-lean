import Googology.Trans.PoR.InaccPsi.R2.HbWFr
import Googology.Trans.PoR.InaccPsi.R2.LsName
import Googology.Trans.PoR.InaccPsi.R2.RlNoGo
import Googology.Trans.PoR.InaccPsi.R2.FxIso
import Googology.Trans.PoR.InaccPsi.R2.ShNu

/-!
# SkFX: the hypothesis region of the skeleton leaf `skRegB` reaches into the long region

The leaf `skRegB` of the round-115 skeleton asks UPPER / LOWER / CapV at every range restart `λ` that lies past
every frontier `ι(Γ(B)·ω)`, `B < Γ(1)`, and whose name exponent `e(η_λ)` is below `Ω₂`.  Its docstring places
this region below `ι(Ω₂)`.  Here: the region contains range restarts `λ` with `L(0) < υ_λ < L(1)` (names
`η_λ` with a successor code, hence `e(η_λ) < Ω₂`), so `skRegB` carries the long region, and with
`Sh.shNotLower` it says that no restart of the region is `ν_C`.
-/

set_option autoImplicit false

namespace R2Skel.SkFX

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2

/-- A successor code forces a name exponent below `Ω₂` (above it the code is a value of `ψ`, a limit). -/
theorem skfxExp_of_succ (S : InaccSeq.{0}) (l c : Ordinal.{0}) (h : Cd.cdCode S l = c + 1) :
    Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) := by
  by_contra hge
  have hc : Cd.cdCode S l = Cd.cdPi S (Cd.cdEta S l) := by
    show Cd.cdCodeOf S (Cd.cdEta S l) = _
    unfold Cd.cdCodeOf; rw [if_neg hge]
  have hSC : SC (Cd.cdPi S (Cd.cdEta S l)) := SC_psi (InR_Om_succ 1) _
  have hlim := hSC.isSuccLimit
  rw [← hc, h] at hlim
  have := hlim.succ_lt (lt_add_one c)
  rw [Order.succ_eq_add_one] at this
  exact lt_irrefl _ this

/-- `Γ(B)·ω < Ω₂` for every `B < Γ(1)`. -/
theorem skfxG_lt_Om2 {B : Ordinal.{0}} (hB : B < Gc.gcG 1) : Gc.gcG B * ω < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : Gc.gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : Gc.gcG B < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hB.trans hG1))
  have hE : InE (Om (1 + 1 : Ordinal.{0})) := Low.opow_eq_self_of_SC Gg.gg_SC_Om2
  exact InE.mul_lt hE (h2.trans Tf.tfBG_lt_Om2) (omega0_lt_inE hE)

/-- **The region of `skRegB` contains range restarts strictly between `L(0)` and `L(1)`.** -/
theorem skfxRegB_long (S : InaccSeq.{0}) : ∃ l, Cd.CdRange S l ∧
    (∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l) ∧
    Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧ Nc.ncL S 0 < upsilon l ∧ upsilon l < Nc.ncL S 1 := by
  have h01 : Nc.ncL S 0 < Nc.ncL S ((0 + 1 : ℕ) : Ordinal.{0}) := by
    simpa using (Rl.rlM_lt_L1 (S := S))
  obtain ⟨μ, hr, hγ, hlt, hcode⟩ := Ls.lsNames_L (S := S) 0 0 (Nc.ncL S 0) h01
  refine ⟨μ, hr, fun B hB => ?_, skfxExp_of_succ S μ _ hcode, hγ, by simpa using hlt⟩
  by_contra hno
  push Not at hno
  have h1 : upsilon μ ≤ upsilon (Bt.iota S (Gc.gcG B * ω)) := Bt.ups_mono hno.le
  rw [← Fx.fx_Pv_eq] at h1
  exact absurd (h1.trans_lt (Ga.ga_Pv_lt_L0 S (skfxG_lt_Om2 hB).le)) (not_lt.2 hγ.le)

/-- **With `Sh.shNotLower`**: the statement of `skRegB` implies that no restart of its region is `ν_C`. -/
theorem skfxRegB_nu (S : InaccSeq.{0})
    (hB : ∀ l, Cd.CdRange S l → (∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l) →
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l) :
    ∀ l, Cd.CdRange S l → (∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l) →
      Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → upsilon l ≠ nuC :=
  fun l hr hA he heq => Sh.shNotLower (S := S) heq (hB l hr hA he).2.1

end R2Skel.SkFX
