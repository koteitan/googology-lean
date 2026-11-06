import Googology.Trans.PoR.InaccPsi.R2.KhTop

/-!
# Ki: THE TOP LAW AT EVERY NORMAL `b = β + W^{Ω_{k+3} + W^{h₁}·ζ₁ + … + W^{h_n}·ζ_n + e}`, from normality alone

`Θ`, `T`, `A`, `W^x = leWe x`, `Zd.ZdLaw`, `Zy.ZyQ`, `Kc.KcE` as before.  A `W`-polynomial is a list `L` of pairs
`(h, ζ)` (`kiX X₀ L = X₀ + W^{h₁}·ζ₁ + … + W^{h_n}·ζ_n`), VALID below a bound `hb` when the exponents are codes
`1 ≤ h_n < … < h₁ < hb`, `h_i < θ`, and the coefficients codes `1 ≤ ζ_i < θ` (`KiValid`).  The base condition is the
accumulation `KiQ` of `Zy.ZyQ` and `Kc.KcE` along the list.

* `kiChain` (**THE CHAIN ALONG A `W`-POLYNOMIAL**: `Kc.kcChain` term by term, the shift `Zy.zySh` in between),
* `kiTail` (`kiX Y L + e < Y + W^{hb}` for a valid `L` below `hb ≥ 1`, `e < Ω₂`), `kiDvd`,
* `kiExtract` (**the components of a member `kiX X₀ L` are members**, `W^{h₁+1} ∣ X₀`),
* `kiCond` (**THE BASE CONDITIONS FROM NORMALITY**: `KiQ` and `Ro.RoBaseE` at a normal `β + W^{kiX X₀ L + e}`),
* `kiTop` (**THE TOP LAW AT EVERY NORMAL `β + W^{Ω_{k+3} + W^{h₁}·ζ₁ + … + W^{h_n}·ζ_n + e}`**).

No new axiom.  New definitions: `kiX`, `KiValid`, `KiQ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ki

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Zz Googology.Trans.PoR.InaccPsi.R2.Kc
  Googology.Trans.PoR.InaccPsi.R2.Kg Googology.Trans.PoR.InaccPsi.R2.Kh Googology.Trans.PoR.InaccPsi.R2.Xm

variable {S : InaccSeq.{0}}

/-- The `W`-polynomial `X₀ + W^{h₁}·ζ₁ + … + W^{h_n}·ζ_n`. -/
noncomputable def kiX (X₀ : Ordinal.{0}) : List (Ordinal.{0} × Ordinal.{0}) → Ordinal.{0}
  | [] => X₀
  | p :: L => kiX (X₀ + leWe p.1 * p.2) L

/-- A valid `W`-polynomial below the bound `hb`. -/
def KiValid (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} → List (Ordinal.{0} × Ordinal.{0}) → Prop
  | _, [] => True
  | hb, p :: L => GxCl (upsilon l) (ldAtR S l) p.1 ∧ 1 ≤ p.1 ∧ p.1 < ConjT.th S ∧ p.1 < hb ∧
      GxCl (upsilon l) (ldAtR S l) p.2 ∧ 0 < p.2 ∧ p.2 < ConjT.th S ∧ KiValid S l p.1 L

/-- The accumulated base condition along the list. -/
def KiQ (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    Ordinal.{0} → (Ordinal.{0} → Prop) → List (Ordinal.{0} × Ordinal.{0}) → Ordinal.{0} → Prop
  | _, Q₀, [], β => Q₀ β
  | X₀, Q₀, p :: L, β => KiQ S l (X₀ + leWe p.1 * p.2) (ZyQ S l X₀ p.1 p.1 (fun β' => Q₀ β' ∧ KcE S l X₀ p.1 β') p.2) L β

theorem kiQ_up {l : Ordinal.{0}} : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ : Ordinal.{0}) (Q₀ : Ordinal.{0} → Prop),
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') → ∀ β β', β ≤ β' → KiQ S l X₀ Q₀ L β → KiQ S l X₀ Q₀ L β'
  | [], _, _, hQup, β, β', hle, hQ => hQup β β' hle hQ
  | _ :: L, _, _, hQup, β, β', hle, hQ =>
    kiQ_up L _ _ (fun _ _ h hq => zyQ_up (fun _ _ h' hq' => ⟨hQup _ _ h' hq'.1, kcE_up h' hq'.2⟩) h hq) β β' hle hQ

/-- **The tail bound**: `kiX Y L + e < Y + W^{hb}` for a valid `L` below `hb ≥ 1` and `e < Ω₂`. -/
theorem kiTail {l : Ordinal.{0}} : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (Y hb e : Ordinal.{0}), 1 ≤ hb →
    KiValid S l hb L → e < Om (1 + 1) → kiX Y L + e < Y + leWe hb
  | [], Y, hb, e, h1, _, he => by
    show Y + e < Y + leWe hb
    exact (add_lt_add_iff_left Y).2 (he.trans_le (by rw [← leWe_one]; exact leWe_mono h1))
  | p :: L, Y, hb, e, _, hv, he => by
    obtain ⟨_, hp1, _, hphb, _, _, hpθ, hvL⟩ := hv
    have hp2 : p.2 < Om (1 + 1) := hpθ.trans (psi_lt (InR_Om_succ 1) _)
    have ih := kiTail L (Y + leWe p.1 * p.2) p.1 e hp1 hvL he
    show kiX (Y + leWe p.1 * p.2) L + e < Y + leWe hb
    calc kiX (Y + leWe p.1 * p.2) L + e < Y + leWe p.1 * p.2 + leWe p.1 := ih
      _ = Y + leWe p.1 * (p.2 + 1) := by rw [mul_add_one, add_assoc]
      _ ≤ Y + leWe p.1 * Om (1 + 1) := add_le_add le_rfl (leMulWe_mono (Order.add_one_le_of_lt hp2))
      _ = Y + leWe (p.1 + 1) := by rw [leWe_succ]
      _ ≤ Y + leWe hb := add_le_add le_rfl (leWe_mono (Order.add_one_le_of_lt hphb))

/-- `W^g ∣ kiX X₀ L` once `W^g ∣ X₀` and every exponent of `L` is at least `g`. -/
theorem kiDvd {l : Ordinal.{0}} : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ hb g : Ordinal.{0}),
    KiValid S l hb L → leWe g ∣ X₀ → (∀ p ∈ L, g ≤ p.1) → leWe g ∣ kiX X₀ L
  | [], _, _, _, _, hX, _ => hX
  | p :: L, X₀, _, g, hv, hX, hg =>
    kiDvd L (X₀ + leWe p.1 * p.2) p.1 g hv.2.2.2.2.2.2.2 (dvd_add hX ((leWe_dvd (hg p (List.mem_cons_self))).trans
      (dvd_mul_right _ _))) (fun q hq => hg q (List.mem_cons_of_mem _ hq))

theorem kiValid_ge {l : Ordinal.{0}} : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (hb : Ordinal.{0}),
    KiValid S l hb L → ∀ p ∈ L, 1 ≤ p.1 ∧ p.1 < hb
  | [], _, _, _, hp => absurd hp List.not_mem_nil
  | q :: L, hb, hv, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact ⟨hv.2.1, hv.2.2.2.1⟩
    · obtain ⟨h1, h2⟩ := kiValid_ge L q.1 hv.2.2.2.2.2.2.2 p hp'
      exact ⟨h1, h2.trans hv.2.2.2.1⟩

theorem kiValid_mem {l : Ordinal.{0}} : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (hb : Ordinal.{0}),
    KiValid S l hb L → ∀ p ∈ L, p.1 < ConjT.th S ∧ p.2 < ConjT.th S
  | [], _, _, _, hp => absurd hp List.not_mem_nil
  | q :: L, _, hv, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp'
    · exact ⟨hv.2.2.1, hv.2.2.2.2.2.2.1⟩
    · exact kiValid_mem L q.1 hv.2.2.2.2.2.2.2 p hp'

/-- `kiX` only adds. -/
theorem kiX_ge : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ : Ordinal.{0}), X₀ ≤ kiX X₀ L
  | [], _ => le_rfl
  | p :: L, X₀ => le_self_add.trans (kiX_ge L (X₀ + leWe p.1 * p.2))

/-- **The components of a member `kiX X₀ L` are members** (`W^{hb} ∣ X₀`). -/
theorem kiExtract {l a c : Ordinal.{0}} : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ hb : Ordinal.{0}),
    KiValid S l hb L → leWe hb ∣ X₀ → kiX X₀ L ∈ S.CSet a c → ∀ p ∈ L, p.1 ∈ S.CSet a c ∧ p.2 ∈ S.CSet a c
  | [], _, _, _, _, _, _, hp => absurd hp List.not_mem_nil
  | p :: L, X₀, hb, hv, hX, hY, q, hq => by
    obtain ⟨_, hp1, _, hphb, _, hp0, hpθ, hvL⟩ := hv
    have hp2 : p.2 < Om (1 + 1) := hpθ.trans (psi_lt (InR_Om_succ 1) _)
    set h := p.1 with hhdef
    set ζ := p.2 with hζdef
    set X₁ := X₀ + leWe h * ζ with hX₁
    set Y := kiX X₁ L with hYdef
    have hYm : Y ∈ S.CSet a c := hY
    -- `Y = X₁ + R`, `R < W^h`
    have hR := kiTail L X₁ h 0 hp1 hvL ldOm2_SC.1
    rw [add_zero] at hR
    have hX₁Y : X₁ ≤ Y := kiX_ge L X₁
    set R := Y - X₁ with hRdef
    have hRlt : R < leWe h := Ry.rySub_lt hX₁Y hR
    have eY : Y = X₀ + (leWe h * ζ + R) := by
      rw [← add_assoc, hRdef]; exact (Ordinal.add_sub_cancel_of_le hX₁Y).symm
    -- `Z = W^h·ζ + R` is the remainder of `Y` by `W^{h+1}`
    have hZlt : leWe h * ζ + R < leWe (h + 1) := by
      calc leWe h * ζ + R < leWe h * ζ + leWe h := (add_lt_add_iff_left _).2 hRlt
        _ = leWe h * (ζ + 1) := (mul_add_one _ _).symm
        _ ≤ leWe h * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hp2)
        _ = leWe (h + 1) := (leWe_succ h).symm
    have hdvX₀ : leWe (h + 1) ∣ X₀ := (leWe_dvd (Order.add_one_le_of_lt hphb)).trans hX
    have hZm : leWe h * ζ + R ∈ S.CSet a c := by
      have h1 := (Vh.vhC_div _ hYm (Om (1 + 1) * (h + 1))).2.1
      have e1 : Y % ω ^ (Om (1 + 1) * (h + 1)) = leWe h * ζ + R := by
        show Y % leWe (h + 1) = leWe h * ζ + R
        obtain ⟨q, hq⟩ := hdvX₀
        rw [eY, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hZlt]
      rwa [e1] at h1
    -- the exponent and the coefficient
    have hhm : h ∈ S.CSet a c := by
      have hlog := leLog_mem hZm
      have hlogζ : log ω ζ < Om (1 + 1) := (log_le_self ω ζ).trans_lt hp2
      have e1 : log ω (leWe h * ζ + R) = Om (1 + 1) * h + log ω ζ := by
        unfold leWe
        exact log_opow_mul_add (b := ω) (u := Om (1 + 1) * h) (v := ζ) (w := R) one_lt_omega0 hp0.ne' hRlt
      rw [e1] at hlog
      have h2 := (Vh.vhC_div _ hlog (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [gg_SC_eps ldOm2_SC, Ordinal.mul_add_div _ ldOm2_SC.1.ne', Ordinal.div_eq_zero_of_lt hlogζ,
        add_zero] at h2
    have hζm : ζ ∈ S.CSet a c := by
      have h1 := (Vh.vhC_div _ hZm (Om (1 + 1) * h)).2.2 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hhm)
      have e1 : (leWe h * ζ + R) / ω ^ (Om (1 + 1) * h) = ζ := by
        show (leWe h * ζ + R) / leWe h = ζ
        rw [Ordinal.mul_add_div _ (leWe_pos h).ne', Ordinal.div_eq_zero_of_lt hRlt, add_zero]
      rwa [e1] at h1
    rcases List.mem_cons.1 hq with rfl | hq'
    · exact ⟨hhm, hζm⟩
    · have hdvX₁ : leWe h ∣ X₁ := dvd_add ((leWe_dvd (le_of_lt (lt_add_one h))).trans hdvX₀) (dvd_mul_right _ _)
      exact kiExtract L X₁ h hvL hdvX₁ hYm q hq'

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hl hX hA hρ

/-- **THE CHAIN ALONG A `W`-POLYNOMIAL** over a shift `X₀` with the law at every `X₀ + e`. -/
theorem kiChain : ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (hb : Ordinal.{0}) {X₀ K₀ q₀ : Ordinal.{0}},
    ZdShQ S l X₀ K₀ q₀ → ∀ (Q₀ : Ordinal.{0} → Prop), (∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) →
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') →
    (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) →
    KiValid S l hb L → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (kiX X₀ L) e β → KiQ S l X₀ Q₀ L β → ZdLaw S l A (kiX X₀ L) e β
  | [], _, _, _, _, _, _, _, _, H0, _ => H0
  | p :: L, _, X₀, _, _, hs0, Q₀, hQq, hQup, H0, hv => by
    obtain ⟨hc, h1, hθ, _, hζc, hζ0, hζθ, hvL⟩ := hv
    have hQup' : ∀ β β', β ≤ β' → (Q₀ β ∧ KcE S l X₀ p.1 β) → (Q₀ β' ∧ KcE S l X₀ p.1 β') :=
      fun β β' h hq => ⟨hQup β β' h hq.1, kcE_up h hq.2⟩
    have H1 := kcChain hl hX hA hρ p.1 hc h1 hθ hs0 (fun β => Q₀ β ∧ KcE S l X₀ p.1 β)
      (fun β hq => hQq β hq.1) hQup' (fun β hq => hq.2)
      (fun e hec he2 β hβD hB hq => H0 e hec he2 β hβD hB hq.1) p.2 hζc hζθ
    exact kiChain L p.1 (zySh hl hX hs0 (zxEx_code hl hX hc hθ) hζc hζθ)
      (ZyQ S l X₀ p.1 p.1 (fun β => Q₀ β ∧ KcE S l X₀ p.1 β) p.2)
      (fun β hQ => zyThr (fun β hq => hQq β hq.1) hQ hζc (zyQh hQ hζ0)) (fun _ _ h hq => zyQ_up hQup' h hq)
      H1 hvL

omit hl hX hA hρ in
/-- **THE BASE CONDITIONS FROM NORMALITY** along the list (`KiQ`), at a base `β` of `b = β + W^{kiX X₀ L + e}`
whose components lie below `ψ₂ b`. -/
theorem kiCond {β e : Ordinal.{0}} (he2 : e < Om (1 + 1)) :
    ∀ (L : List (Ordinal.{0} × Ordinal.{0})) (X₀ hb : Ordinal.{0}) (Q₀ : Ordinal.{0} → Prop),
    KiValid S l hb L →
    (∀ p ∈ L, p.1 < S.psi (β + leWe (kiX X₀ L + e)) (Om (1 + 1)) ∧
      p.2 < S.psi (β + leWe (kiX X₀ L + e)) (Om (1 + 1))) →
    Q₀ β → KiQ S l X₀ Q₀ L β
  | [], _, _, _, _, _, hQ => hQ
  | p :: L, X₀, _, Q₀, hv, hcomp, hQ => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨hc, h1, hθ, _, hζc, hζ0, hζθ, hvL⟩ := hv
    have hh2 : p.1 < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    have hv' : KiValid S l (p.1 + 1) (p :: L) := ⟨hc, h1, hθ, lt_add_one _, hζc, hζ0, hζθ, hvL⟩
    have hE1 : kiX X₀ (p :: L) + e < X₀ + leWe (p.1 + 1) :=
      kiTail (p :: L) X₀ (p.1 + 1) e le_add_self hv' he2
    have hE2 : kiX X₀ (p :: L) + e < X₀ + leWe (Om (1 + 1)) :=
      hE1.trans_le (add_le_add le_rfl (leWe_mono (Order.add_one_le_of_lt hh2)))
    obtain ⟨hp1b, hp2b⟩ := hcomp p List.mem_cons_self
    have hKcE : KcE S l X₀ p.1 β := fun h' _ _ hle =>
      kgOwnExp h' ((hle.trans_lt hp1b).trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono hE2.le))).1)
    have hmid : p.1 < S.psi (β + leWe (X₀ + leWe p.1)) (Om (1 + 1)) := hKcE p.1 hc h1 le_rfl
    have hZ : ZyQ S l X₀ p.1 p.1 (fun β' => Q₀ β' ∧ KcE S l X₀ p.1 β') p.2 β :=
      ⟨⟨hQ, hKcE⟩, hmid, fun ζ' _ hle => kgOwnBase (fun a c _ hq => CSet.of_lt hq) hmid ζ'
        ((hle.trans_lt hp2b).trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono hE1.le))).1)⟩
    exact kiCond he2 L (X₀ + leWe p.1 * p.2) p.1 _ hvL (fun q hq => hcomp q (List.mem_cons_of_mem _ hq)) hZ

/-- **THE TOP LAW AT EVERY NORMAL `b = β + W^{Ω_{k+3} + W^{h₁}·ζ₁ + … + W^{h_n}·ζ_n + e}`** (a valid list below
`Ω₂`, `e` a code, `W^{E+1} ∣ β`). -/
theorem kiTop (k : ℕ) (L : List (Ordinal.{0} × Ordinal.{0})) (hv : KiValid S l (Om (1 + 1)) L) {β e : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hdv : leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e + 1) ∣ β)
    (hbD : VbD S l (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)))
    (hbn : β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e) ∈
      S.CSet (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e))
        (S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)) (Om (1 + 1)))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (kiX (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) L + e)))
        (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X₀ := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hX₀def
  set X := kiX X₀ L with hXdef
  set E := X + e with hEdef
  set b := β + leWe E with hbdef
  -- divisibilities
  have hX₀W : leWe X₀ = X₀ := Vn.vnWe_OmK k
  have hΩX₀ : Om (1 + 1) ≤ X₀ := Om_le_Om.2 (by
    calc (1 + 1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 + 1 := by simp [add_assoc]
      _ ≤ (k : Ordinal.{0}) + 1 + 1 + 1 := le_self_add)
  have hdvX₀ : leWe (Om (1 + 1)) ∣ X₀ := by have := leWe_dvd hΩX₀; rwa [hX₀W] at this
  have hdv1X₀ : leWe 1 ∣ X₀ := (leWe_dvd (gg_one_lt_of_SC ldOm2_SC).le).trans hdvX₀
  have hge := kiValid_ge L (Om (1 + 1)) hv
  have hΩ2X : Om (1 + 1) ∣ X := by
    have h := kiDvd L X₀ (Om (1 + 1)) 1 hv hdv1X₀ (fun p hp => (hge p hp).1)
    rwa [leWe_one] at h
  -- the components lie below `ψ₂(b)`
  have hWE := khWE_mem hdv hbn
  have hEm := khE_mem hWE
  have hem := khe_mem hΩ2X he2 hEm
  have hXm := khX_mem hΩ2X he2 hEm
  have hcomp := kiExtract L X₀ (Om (1 + 1)) hv hdvX₀ hXm
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hbounds : ∀ p ∈ L, p.1 < S.psi b (Om (1 + 1)) ∧ p.2 < S.psi b (Om (1 + 1)) := fun p hp =>
    ⟨lt_psi_of_mem hκ2 (hcomp p hp).1 ((kiValid_mem L _ hv p hp).1.trans hθ2),
      lt_psi_of_mem hκ2 (hcomp p hp).2 ((kiValid_mem L _ hv p hp).2.trans hθ2)⟩
  have heb : e < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hem he2
  have hKiQ : KiQ S l X₀ (fun _ => True) L β :=
    kiCond he2 L X₀ (Om (1 + 1)) (fun _ => True) hv hbounds trivial
  -- `β` is normal
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := Zp.zpPreO_norm hκ2 (Om (1 + 1) * (E + 1)) hbn
    have e1 : ω ^ (Om (1 + 1) * (E + 1)) * (b / ω ^ (Om (1 + 1) * (E + 1))) = β := by
      obtain ⟨q, hq⟩ := hdv
      show leWe (E + 1) * (b / leWe (E + 1)) = β
      rw [hbdef, hq, Ordinal.mul_add_div _ (leWe_pos _).ne',
        Ordinal.div_eq_zero_of_lt (leWe_lt (lt_add_one E)), add_zero]
    rwa [e1] at h
  have hB : Ro.RoBaseE S l X e β := by
    refine ⟨(leWe_dvd (le_of_lt (lt_add_one E))).trans hdv, hβD.1,
      hbD.2.2.trans_le (ConjT.OmW_le_A S _), fun d _ => (psi_mono hκ2 le_self_add).2 hβn,
      fun e' _ hle => ?_⟩
    have h0 := kgOwnBase (S := S) (β := β) (g₀ := X) (j := 0) (qj := 0) (fun a c _ _ => CSet.zero_mem a c)
      (SC_psi hκ2 _).1 e' (by
        rw [zero_add, leWe_one]
        exact (hle.trans_lt heb).trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono
          (add_le_add le_rfl he2.le)))).1)
    rwa [leWe_zero, one_mul] at h0
  have hlaw := kiChain hl hX hA hρ L (Om (1 + 1)) ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1)
    (fun _ => True) (fun _ _ => (SC_psi hκ2 _).1) (fun _ _ _ _ => trivial)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB) hv e hec he2 β hβD hB hKiQ
  unfold ZdLaw leTe at hlaw
  exact hlaw

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ki

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ki.kiTop
