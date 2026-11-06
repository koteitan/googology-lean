import Googology.Trans.PoR.InaccPsi.R2.KgPlat
import Googology.Trans.PoR.InaccPsi.R2.ZpWall
import Googology.Trans.PoR.InaccPsi.R2.ZpPreO

/-!
# Kh: THE TOP LAW AT EVERY NORMAL `b = β + W^{Ω_{k+3} + W^h·ζ + e}` (codes `h ≥ 1`, `ζ ≥ 1`, `e`), from normality alone

`Θ`, `T`, `A`, `W^x = leWe x`, `Zd.ZdLaw`, `Zy.ZyQ`, `Kc.KcE` as before.  The chain `Kc.kcTop` asks base conditions;
here they come from the normality of `b = β + W^E` (`W^{E+1} ∣ β`):

* the COMPONENTS `h, ζ, e` of `E = Ω_{k+3} + W^h·ζ + e` are members of `Cl(b, ψ₂ b)` (`khWE_mem`: `W^E` is the
  remainder of `b` by `W^{E+1}`; `khE_mem`: `E` from `log_ω W^E = Ω₂·E`; `khe_mem`, `khWhz_mem`, `khh_mem`, `khζ_mem`),
  so they lie below `ψ₂(b)`;
* `β` is normal (`Zp.zpPreO_norm`: the `W^{E+1}`-prefix of a normal argument is normal);
* the cumulative exponent condition `Kc.KcE` from `h < ψ₂(β + W^{Ω_{k+3} + W^{Ω₂}})` (`Kg.kgOwnExp`), the cumulative
  coefficient condition of `Zy.ZyQ` from `ζ < ψ₂(β + W^{Ω_{k+3} + W^{h+1}})` (`Kg.kgOwnBase`), the codes below `e`
  from `e < ψ₂(β + W^{Ω_{k+3} + W^h·ζ + Ω₂})` (`Kg.kgOwnBase` at `j = 0`).

* `khTop` (**THE TOP LAW AT EVERY NORMAL `β + W^{Ω_{k+3} + W^h·ζ + e}`**:
  `Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T b))`, with no hypothesis but the form, `b ∈ D` and normality).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Kc Googology.Trans.PoR.InaccPsi.R2.Kg

variable {S : InaccSeq.{0}}

theorem khMod {β E : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) : (β + leWe E) % leWe (E + 1) = leWe E := by
  obtain ⟨q, rfl⟩ := hdv
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (leWe_lt (lt_add_one E))]

/-- `W^E` is a member once `β + W^E` is, `W^{E+1} ∣ β`. -/
theorem khWE_mem {a c β E : Ordinal.{0}} (hdv : leWe (E + 1) ∣ β) (hb : β + leWe E ∈ S.CSet a c) :
    leWe E ∈ S.CSet a c := by
  have h := (Vh.vhC_div _ hb (Om (1 + 1) * (E + 1))).2.1
  have e : (β + leWe E) % ω ^ (Om (1 + 1) * (E + 1)) = leWe E := khMod hdv
  rwa [e] at h

/-- `E` is a member once `W^E` is. -/
theorem khE_mem {a c E : Ordinal.{0}} (h : leWe E ∈ S.CSet a c) : E ∈ S.CSet a c := by
  have hlog := leLog_mem h
  unfold leWe at hlog
  rw [Ordinal.log_opow one_lt_omega0] at hlog
  have h2 := (Vh.vhC_div _ hlog (Om (1 + 1))).2.2 (mxOm2_mem _ _)
  rwa [gg_SC_eps ldOm2_SC, Ordinal.mul_div_cancel _ ldOm2_SC.1.ne'] at h2

/-- The last code `e` of `X + e`, `Ω₂ ∣ X`, is a member once `X + e` is. -/
theorem khe_mem {a c X e : Ordinal.{0}} (hdv : Om (1 + 1) ∣ X) (he : e < Om (1 + 1)) (h : X + e ∈ S.CSet a c) :
    e ∈ S.CSet a c := by
  have h1 := (Vh.vhC_div _ h (Om (1 + 1))).2.1
  rw [gg_SC_eps ldOm2_SC] at h1
  obtain ⟨q, rfl⟩ := hdv
  rwa [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt he] at h1

/-- The part `X` of `X + e`, `Ω₂ ∣ X`, `e < Ω₂`, is a member once `X + e` is. -/
theorem khX_mem {a c X e : Ordinal.{0}} (hdv : Om (1 + 1) ∣ X) (he : e < Om (1 + 1)) (h : X + e ∈ S.CSet a c) :
    X ∈ S.CSet a c := by
  have h1 := (Vh.vhC_div _ h (Om (1 + 1))).1
  rw [gg_SC_eps ldOm2_SC] at h1
  obtain ⟨q, rfl⟩ := hdv
  rwa [Ordinal.mul_add_div _ ldOm2_SC.1.ne', Ordinal.div_eq_zero_of_lt he, add_zero] at h1

/-- `W^h·ζ` is a member once `X₀ + W^h·ζ` is, `W^{h+1} ∣ X₀`, `ζ < Ω₂`. -/
theorem khWhz_mem {a c X₀ h ζ : Ordinal.{0}} (hdv : leWe (h + 1) ∣ X₀) (hζ : ζ < Om (1 + 1))
    (hx : X₀ + leWe h * ζ ∈ S.CSet a c) : leWe h * ζ ∈ S.CSet a c := by
  have h1 := (Vh.vhC_div _ hx (Om (1 + 1) * (h + 1))).2.1
  have e : (X₀ + leWe h * ζ) % ω ^ (Om (1 + 1) * (h + 1)) = leWe h * ζ := by
    obtain ⟨q, hq⟩ := hdv
    show (X₀ + leWe h * ζ) % leWe (h + 1) = leWe h * ζ
    rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt]
    rw [leWe_succ]
    exact mul_lt_mul_of_pos_left hζ (leWe_pos h)
  rwa [e] at h1

/-- The exponent `h` is a member once `W^h·ζ` is, `0 < ζ < Ω₂`. -/
theorem khh_mem {a c h ζ : Ordinal.{0}} (hζ0 : ζ ≠ 0) (hζ : ζ < Om (1 + 1)) (hw : leWe h * ζ ∈ S.CSet a c) :
    h ∈ S.CSet a c := by
  have hlog := leLog_mem hw
  have hlogζ : log ω ζ < Om (1 + 1) := (log_le_self ω ζ).trans_lt hζ
  have e1 : log ω (leWe h * ζ) = Om (1 + 1) * h + log ω ζ := by
    unfold leWe
    have := log_opow_mul_add (b := ω) (u := Om (1 + 1) * h) (v := ζ) (w := 0) one_lt_omega0 hζ0
      (opow_pos _ omega0_pos)
    rwa [add_zero] at this
  rw [e1] at hlog
  have h2 := (Vh.vhC_div _ hlog (Om (1 + 1))).2.2 (mxOm2_mem _ _)
  rwa [gg_SC_eps ldOm2_SC, Ordinal.mul_add_div _ ldOm2_SC.1.ne', Ordinal.div_eq_zero_of_lt hlogζ, add_zero] at h2

/-- The coefficient `ζ` is a member once `W^h·ζ` and `h` are. -/
theorem khζ_mem {a c h ζ : Ordinal.{0}} (hh : h ∈ S.CSet a c) (hw : leWe h * ζ ∈ S.CSet a c) :
    ζ ∈ S.CSet a c := by
  have h1 := (Vh.vhC_div _ hw (Om (1 + 1) * h)).2.2 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hh)
  have e : leWe h * ζ / ω ^ (Om (1 + 1) * h) = ζ := Ordinal.mul_div_cancel ζ (leWe_pos h).ne'
  rwa [e] at h1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE TOP LAW AT EVERY NORMAL `b = β + W^{Ω_{k+3} + W^h·ζ + e}`** (`h ≥ 1`, `ζ ≥ 1`, `e` codes, `h, ζ < θ`,
`W^{E+1} ∣ β`). -/
theorem khTop (k : ℕ) {β h ζ e : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) h) (h1 : 1 ≤ h)
    (hθ : h < ConjT.th S) (hζc : GxCl (upsilon l) (ldAtR S l) ζ) (hζθ : ζ < ConjT.th S) (hζ0 : ζ ≠ 0)
    (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hdv : leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e + 1) ∣ β)
    (hbD : VbD S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e)))
    (hbn : β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e) ∈
      S.CSet (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e))
        (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e)) (Om (1 + 1)))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e))
      (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + leWe h * ζ + e)))
        (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X₀ := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hX₀def
  set X := X₀ + leWe h * ζ with hXdef
  set E := X + e with hEdef
  set b := β + leWe E with hbdef
  have hh2 : h < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
  have hζ2 : ζ < Om (1 + 1) := hζθ.trans (psi_lt hκ2 _)
  -- divisibilities
  have hX₀W : leWe X₀ = X₀ := Vn.vnWe_OmK k
  have hh1Ω : h + 1 ≤ X₀ := by
    refine (Order.add_one_le_of_lt hh2).trans (Om_le_Om.2 ?_)
    calc (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by
          simp [add_assoc]
      _ ≤ (k : Ordinal.{0}) + 1 + 1 + 1 := le_self_add
  have hdvX₀ : leWe (h + 1) ∣ X₀ := by
    have := leWe_dvd hh1Ω; rwa [hX₀W] at this
  have hΩ2X₀ : Om (1 + 1) ∣ X₀ := by
    have h2 : leWe 1 ∣ leWe (h + 1) := leWe_dvd (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_add_one h)))
    rw [leWe_one] at h2; exact h2.trans hdvX₀
  have hΩ2Wh : Om (1 + 1) ∣ leWe h * ζ := by
    have h2 : leWe 1 ∣ leWe h := leWe_dvd h1
    rw [leWe_one] at h2; exact h2.trans (dvd_mul_right _ _)
  have hΩ2X : Om (1 + 1) ∣ X := dvd_add hΩ2X₀ hΩ2Wh
  -- the components lie below `ψ₂(b)`
  have hWE := khWE_mem hdv hbn
  have hEm := khE_mem hWE
  have hem := khe_mem hΩ2X he2 hEm
  have hXm := khX_mem hΩ2X he2 hEm
  have hWhz := khWhz_mem hdvX₀ hζ2 hXm
  have hhm := khh_mem hζ0 hζ2 hWhz
  have hζm := khζ_mem hhm hWhz
  have hhb : h < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hhm hh2
  have hζb : ζ < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hζm hζ2
  have heb : e < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hem he2
  -- `β` is normal
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := Zp.zpPreO_norm hκ2 (Om (1 + 1) * (E + 1)) hbn
    have e1 : ω ^ (Om (1 + 1) * (E + 1)) * (b / ω ^ (Om (1 + 1) * (E + 1))) = β := by
      obtain ⟨q, hq⟩ := hdv
      show leWe (E + 1) * (b / leWe (E + 1)) = β
      rw [hbdef, hq, Ordinal.mul_add_div _ (leWe_pos _).ne',
        Ordinal.div_eq_zero_of_lt (leWe_lt (lt_add_one E)), add_zero]
    rwa [e1] at h
  -- bounds of `E`
  have hWhz_lt : leWe h * ζ + e < leWe (h + 1) := by
    have he' : e < leWe h := he2.trans_le (by rw [← leWe_one]; exact leWe_mono h1)
    calc leWe h * ζ + e < leWe h * ζ + leWe h := (add_lt_add_iff_left _).2 he'
      _ = leWe h * (ζ + 1) := (mul_add_one _ _).symm
      _ ≤ leWe h * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hζ2)
      _ = leWe (h + 1) := (leWe_succ h).symm
  have hEle1 : E ≤ X₀ + leWe (h + 1) := by
    rw [hEdef, hXdef, add_assoc]; exact add_le_add le_rfl hWhz_lt.le
  have hEle2 : X₀ + leWe (h + 1) ≤ X₀ + leWe (Om (1 + 1)) :=
    add_le_add le_rfl (leWe_mono (Order.add_one_le_of_lt hh2))
  have hbmono : ∀ Y, E ≤ Y → S.psi b (Om (1 + 1)) ≤ S.psi (β + leWe Y) (Om (1 + 1)) := fun Y hY =>
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono hY))).1
  -- the base conditions
  have hKcE : KcE S l X₀ h β := fun h' _ _ hle =>
    kgOwnExp h' ((hle.trans_lt hhb).trans_le (hbmono _ (hEle1.trans hEle2)))
  have hmid : h < S.psi (β + leWe (X₀ + leWe h)) (Om (1 + 1)) := hKcE h hc h1 le_rfl
  have hQ : ZyQ S l X₀ h h (KcE S l X₀ h) ζ β :=
    ⟨hKcE, hmid, fun ζ' _ hle => kgOwnBase (fun a c _ hq => CSet.of_lt hq) hmid ζ'
      ((hle.trans_lt hζb).trans_le (hbmono _ hEle1))⟩
  have hB : Ro.RoBaseE S l X e β := by
    refine ⟨(leWe_dvd (le_of_lt (lt_add_one E))).trans hdv, hβD.1,
      hbD.2.2.trans_le (ConjT.OmW_le_A S _), fun d _ => (psi_mono hκ2 le_self_add).2 hβn,
      fun e' _ hle => ?_⟩
    have h0 := kgOwnBase (S := S) (β := β) (g₀ := X) (j := 0) (qj := 0) (fun a c _ _ => CSet.zero_mem a c)
      (SC_psi hκ2 _).1 e' (by
        rw [zero_add, leWe_one]
        exact (hle.trans_lt heb).trans_le (hbmono _ (add_le_add le_rfl he2.le)))
    rwa [leWe_zero, one_mul] at h0
  have hlaw := kcTop hl hX hA hρ k h hc h1 hθ ζ hζc hζθ e hec he2 β hβD hB hQ
  unfold ZdLaw leTe at hlaw
  exact hlaw

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kh

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kh.khTop
