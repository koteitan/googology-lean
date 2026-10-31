import Googology.Trans.PoR.InaccPsi.R2.SkRXTop
import Googology.Trans.PoR.InaccPsi.R2.SfNF

/-!
# The top law at `Ω_{k+3}` with an image depending on the exponent `e` and the base `β`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T_X(β) = ψ₂(β + W^X)` (`leTe`), `Ω^x = leOe x`, `Y₂ = ψ₂(Ω₂)`.

The family law `WgTopFam S k λ`: for every code `e < Ω₂` there is an image `X̂_e : base ↦ image` with
`Vt.VtTopDyn λ 0 Ω_{k+3} X̂_e e`, i.e. `Θ(ψ₂(β + W^{Ω_{k+3}+e})) = ψ₁(Â_β + Ω^{X̂_e(β) + Θ e})` at every base `β`.

* `wgFam_of_skrx` (the refuted one-image form `SkRX.SkRXTopDynAll` implies the family form);
* `wgDyn_iff_pt` (**the family law is a statement per base**: `∃ X̂, VtTopDyn λ b X X̂ e` ⇔ at every base
  `β ≥ b` some `Z` satisfies the top law at `β` alone, `WgTopAt`);
* `wgSep01` (**REFUTE-FIRST test against `SkRX.skrxDyn01`**: two images `X̂₀` (for `e = 0`) and `X̂₁` (for `e = 1`)
  satisfy `X̂₀(0) ≤ Y₂ < X̂₀(Ω₃) ≤ X̂₁(0)`; so the contradiction of `skrxDyn01` is exactly the case `X̂₁ = X̂₀`,
  and every family has `X̂₁(0) ≠ X̂₀(0)`, `wgSep01_ne`);
* `wgTop0_base0` (**the law at `e = 0` holds at the base `β = 0` with the image `Y₂`**, at every restart with an
  own `A`), `wgTop0_base0_wit` (at the witness restart of `SkRX.skrxTopDynAll_false`, the restart of `m* = L(0)`).

No new axiom.  New definitions: the statement names `WgTopAt`, `WgTopFam`, `WgTopFamAll`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vn Googology.Trans.PoR.InaccPsi.R2.Vq

variable {S : InaccSeq.{0}}

/-- The top law at the single base `β` with the image `Z`. -/
def WgTopAt (S : InaccSeq.{0}) (l X Z e β : Ordinal.{0}) : Prop :=
  ∀ Â, Â ∈ S.CSet Â (S.psi Â (Om 1)) →
    gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
    gxTh (upsilon l) (ldAtR S l) (leTe S (X + e) β) =
      S.psi (Â + leOe (Z + gxTh (upsilon l) (ldAtR S l) e)) (Om 1)

/-- **The family law at `Ω_{k+3}`**: one image `X̂_e` per code exponent `e < Ω₂`, depending on the base. -/
def WgTopFam (S : InaccSeq.{0}) (k : ℕ) (l : Ordinal.{0}) : Prop :=
  ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
    ∃ Xh : Ordinal.{0} → Ordinal.{0}, Vt.VtTopDyn S l 0 (Om ((k + 3 : ℕ) : Ordinal.{0})) Xh e

/-- The family law at every level `k` and every restart with an own `A`. -/
def WgTopFamAll (S : InaccSeq.{0}) : Prop :=
  ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → WgTopFam S k l

/-- The one-image form (refuted by `SkRX.skrxTopDynAll_false`) implies the family form. -/
theorem wgFam_of_skrx (h : SkRX.SkRXTopDynAll S) : WgTopFamAll S := by
  intro k l ηx A hl hX hA hρ e he heW
  obtain ⟨Xh, hT⟩ := h k l ηx A hl hX hA hρ
  exact ⟨Xh, hT e he heW⟩

/-- **The family law is a statement per base.** -/
theorem wgDyn_iff_pt {l b X e : Ordinal.{0}} :
    (∃ Xh : Ordinal.{0} → Ordinal.{0}, Vt.VtTopDyn S l b X Xh e) ↔
      ∀ β, RoBaseE S l X e β → b ≤ β → ∃ Z, WgTopAt S l X Z e β := by
  constructor
  · rintro ⟨Xh, hT⟩ β hβ hbβ
    exact ⟨Xh β, fun Â hÂ hbase => hT β Â hβ hbβ hÂ hbase⟩
  · intro h
    classical
    refine ⟨fun β => if hβ : RoBaseE S l X e β ∧ b ≤ β then Classical.choose (h β hβ.1 hβ.2) else 0, ?_⟩
    intro β Â hβ hbβ hÂ hbase
    have hc := Classical.choose_spec (h β hβ hbβ)
    simp only [dif_pos (And.intro hβ hbβ)]
    exact hc Â hÂ hbase

section Main

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **REFUTE-FIRST against `SkRX.skrxDyn01`**: images `X̂₀` for `e = 0` and `X̂₁` for `e = 1` at `Ω₃` over the base
`0` satisfy `X̂₀(0) ≤ Y₂ < X̂₀(Ω₃) ≤ X̂₁(0)`. -/
theorem wgSep01 {X0 X1 : Ordinal.{0} → Ordinal.{0}}
    (h0 : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X0 0) (h1 : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X1 1) :
    X0 0 ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) ∧ S.psi (Om (1 + 1)) (Om (1 + 1)) < X0 (Om (1 + 1 + 1)) ∧
      X0 (Om (1 + 1 + 1)) ≤ X1 0 := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  set Y2 := S.psi (Om (1 + 1)) (Om (1 + 1)) with hY2
  have hY2SC : SC Y2 := SC_psi (InR_Om_succ 1) _
  have hΩ1Y2 : Om 1 < Y2 := (psiS_bounds (S := S) _ 1).1
  have hfix : leOe Y2 = Y2 := Ua.uaOe_fix (gg_SC_eps hY2SC) hΩ1Y2
  have hle0 := Vx.vxDyn_le0 hl hX hA hρ h0
  have hgt := Vx.vxDyn_gtOm3 hl hX hA hρ h0
  have hX0 : X0 0 ≤ Y2 := by
    by_contra h
    push Not at h
    have h' := leOe_lt h
    rw [hfix] at h'
    exact absurd hle0 (not_le.2 h')
  have hXO : Y2 < X0 (Om (1 + 1 + 1)) := by
    by_contra h
    push Not at h
    have h' := leOe_mono h
    rw [hfix] at h'
    exact absurd hgt (not_lt.2 h')
  refine ⟨hX0, hXO, ?_⟩
  -- the reading at β = Ω₃, e = 0
  have hAω := vnA_ge hl hX hA hρ
  have hle : A ≤ A + 1 + Y2 := le_self_add.trans le_self_add
  have hΩ2 : Om (1 + 1) < A + 1 + Y2 := (vkOmW.2.trans_le hAω).trans_le hle
  have hÂ : A + 1 + Y2 ∈ S.CSet (A + 1 + Y2) (S.psi (A + 1 + Y2) (Om 1)) :=
    CSet.add_mem (CSet.add_mem ((psi_mono (S := S) hκ1 hle).2 hA) (CSet.one_mem _ _)) (vqY2_mem hΩ2)
  have hbase := vnRead_W hl hX hA hρ (X := Om (1 + 1 + 1)) (by rw [vnWe_Om3]; exact ugY_lt_Om3.le)
    vnWe_Om3.le
  rw [vnWe_Om3] at hbase
  have hR3 := h0 _ _ (vqBase_Om3Om3 l) zero_le hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at hR3
  -- the reading at β = 0, e = 1
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have h3 : (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hB1 : RoBaseE S l (Om (1 + 1 + 1)) 1 0 := by
    have h13 : (1 : Ordinal.{0}) < Om (1 + 1 + 1) := gg_one_lt_of_SC (SC_Om h3)
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add]
      exact (leWe_lt_SC vkOmW.1 vkOmW.2 (vqOm3_add_lt h13)).1.trans_le (ConjT.OmW_le_A S _)
    · exact h'.trans_lt ((gg_one_lt_of_SC (SC_Om one_ne_zero)).trans (leOm1_lt_Te (S := S) _ _))
  have hR1 := h1 0 (A + 1) hB1 zero_le (Vx.vxHatA1 (S := S) hA) (ldBlk_zero hA hρ)
  rw [gxTh_small h1ρ.le] at hR1
  -- strict order of the two atoms
  have hlt : gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1 + 1)) (Om (1 + 1 + 1))) <
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1 + 1) + 1) 0) := by
    have hat : leTe S (Om (1 + 1 + 1)) (Om (1 + 1 + 1)) ∈ ldAtR S l := by
      unfold leTe
      rw [vnWe_Om3]
      exact ⟨_, CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _),
        vqOm3_lt_A l (vkOmW.1.isPrincipal Ry.ryOm3_lt Ry.ryOm3_lt), rfl⟩
    refine gxTh_lt (GxCl.atom hat) ?_
    unfold leTe
    rw [vnWe_Om3, zero_add]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) SkRX.skrxOm3_two_lt
      (CSet.add_mem (Ry.ryOm3_mem _ _) (Ry.ryOm3_mem _ _))
  rw [hR3, hR1] at hlt
  have hargs : A + 1 + Y2 + leOe (X0 (Om (1 + 1 + 1))) < A + 1 + leOe (X1 0 + 1) := by
    by_contra h
    push Not at h
    exact absurd hlt (not_lt.2 (psi_mono (S := S) hκ1 h).1)
  rw [add_assoc (A + 1) Y2] at hargs
  have h2 : leOe (X0 (Om (1 + 1 + 1))) < leOe (X1 0 + 1) :=
    le_add_self.trans_lt ((add_lt_add_iff_left (A + 1)).1 hargs)
  have h3' : X0 (Om (1 + 1 + 1)) < X1 0 + 1 := by
    by_contra h
    push Not at h
    exact absurd h2 (not_lt.2 (leOe_mono h))
  exact Order.lt_add_one_iff.1 h3'

/-- **Every family has `X̂₁(0) ≠ X̂₀(0)`**: the image must depend on the exponent. -/
theorem wgSep01_ne {X0 X1 : Ordinal.{0} → Ordinal.{0}}
    (h0 : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X0 0) (h1 : Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X1 1) :
    X0 0 < X1 0 := by
  obtain ⟨a, b, c⟩ := wgSep01 hl hX hA hρ h0 h1
  exact (a.trans_lt b).trans_le c

/-- **`e = 0` at the base `β = 0`**: `Θ(ψ₂(Ω₃)) = ψ₁(A + 1 + Ω^{Y₂})`, the top law at `β = 0` with the image `Y₂`. -/
theorem wgTop0_base0 :
    WgTopAt S l (Om (1 + 1 + 1)) (S.psi (Om (1 + 1)) (Om (1 + 1))) 0 0 := by
  intro Â hÂ hb
  have hb0 := ldBlk_zero hA hρ
  have hA1 := Vx.vxHatA1 (S := S) hA
  have e : Â = A + 1 :=
    le_antisymm (Sf.sfArg_le hÂ hA1 (by rw [← hb, hb0])) (Sf.sfArg_le hA1 hÂ (by rw [← hb, hb0]))
  subst e
  have hY2SC : SC (S.psi (Om (1 + 1)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  have hfix : leOe (S.psi (Om (1 + 1)) (Om (1 + 1))) = S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    Ua.uaOe_fix (gg_SC_eps hY2SC) (psiS_bounds (S := S) _ 1).1
  have hbase := vnRead_W hl hX hA hρ (X := Om (1 + 1 + 1)) (by rw [vnWe_Om3]; exact ugY_lt_Om3.le)
    vnWe_Om3.le
  unfold leTe
  rw [add_zero, zero_add, gxTh_zero, add_zero, hfix]
  exact hbase

end Main

/-- **Non-vacuity at the witness restart** (`m* = L(0)`, the witness of `SkRX.skrxTopDynAll_false`): the family
law at `e = 0` holds at the base `β = 0` with the image `Y₂`. -/
theorem wgTop0_base0_wit (S : InaccSeq.{0}) :
    ∃ l A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ WgTopAt S l (Om (1 + 1 + 1)) (S.psi (Om (1 + 1)) (Om (1 + 1))) 0 0 := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, hρ⟩ := vqA_spec hl hX (n := 0) hn
  exact ⟨l, _, hl, e.symm, hA, hρ, wgTop0_base0 hl hX hA hρ⟩

end Googology.Trans.PoR.InaccPsi.R2.Wg

#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgFam_of_skrx
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgDyn_iff_pt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgSep01
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgSep01_ne
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgTop0_base0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Wg.wgTop0_base0_wit
