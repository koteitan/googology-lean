import Googology.Trans.PoR.InaccPsi.R2.KqChain
import Googology.Trans.PoR.InaccPsi.R2.KjCoef

/-!
# Kr: THE TOP LAW AT EVERY NORMAL `b = β + W^E·γ`, `E = Ω_{k+3} + w + e`, `w` a `W`-term over the codes

`Θ`, `T`, `A`, `W^x = leWe x`, `Zd.ZdLaw`, `Zy.ZyQ`, `Ko.KoThr` as before; `w` is divisible by `Ω₂` (its code part, if
any, joins `e`).

* `krMax_mem`, `krExtract` (**the threshold of a member `W`-term is a member**), `krLt` (`w < G` for every strongly
  critical `G > Ω₂`), `krTwAdd` (the tower of `x ↦ X + x`);
* `koGOLd` (`Ko.koGOL` with any `d < Ω₂` for `1`: `q < ψ₂(β + W^{F(h + d)})` gives `q < ψ₂(β + W^{F(h)})`);
* `krPoly` (**THE CHAIN ALONG A `W`-TERM `w`**: over a shift `X₀` with the law at every `X₀ + e`, the law at
  `X₀ + w + e` on the bases with `q_w < ψ₂(β + W^{X₀ + w + e + 1})`; induction on `w = W^{g₁}·u + r`: `Kq.kqChain` at
  `g₁` with the base condition `Zy.ZyQ` from `Ko.koGOL_top` and `Ko.koCoef`, then `r` over `X₀ + W^{g₁}·u`);
* `krSucc` (the law at `(β + W^E·γ') + W^E`), `krTop` (**THE TOP LAW AT EVERY NORMAL `β + W^E·γ`**, `W^{E+1} ∣ β`,
  `E = Ω_{k+3} + w + e`, by induction on the code `γ` with `Kj.kjLim`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Zd
  Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Kg Googology.Trans.PoR.InaccPsi.R2.Kh Googology.Trans.PoR.InaccPsi.R2.Kj
  Googology.Trans.PoR.InaccPsi.R2.Kk Googology.Trans.PoR.InaccPsi.R2.Ko Googology.Trans.PoR.InaccPsi.R2.Kp
  Googology.Trans.PoR.InaccPsi.R2.Kq

variable {S : InaccSeq.{0}}

theorem krMax_mem {P : Ordinal.{0} → Prop} {a b : Ordinal.{0}} (ha : P a) (hb : P b) : P (max a b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- **The threshold of a member `W`-term is a member.** -/
theorem krExtract {l a c : Ordinal.{0}} : ∀ {w qw : Ordinal.{0}}, KoThr S l w qw → w ∈ S.CSet a c →
    qw ∈ S.CSet a c := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro w qw hk
  induction hk with
  | code _ _ => exact id
  | @term g₁ q₁ u r qr _ _ hu0 huθ _ hrlt ih₁ ihr =>
    intro hw
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    -- the exponent `g₁`
    have hg₁m : g₁ ∈ S.CSet a c := by
      have hlog := leLog_mem hw
      have hlogu : log ω u < Om (1 + 1) := (log_le_self ω u).trans_lt hu2
      have e1 : log ω (leWe g₁ * u + r) = Om (1 + 1) * g₁ + log ω u := by
        unfold leWe at hrlt ⊢
        exact log_opow_mul_add (b := ω) (u := Om (1 + 1) * g₁) (v := u) (w := r) one_lt_omega0 hu0.ne' hrlt
      rw [e1] at hlog
      have h2 := (Vh.vhC_div _ hlog (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [gg_SC_eps ldOm2_SC, Ordinal.mul_add_div _ ldOm2_SC.1.ne', Ordinal.div_eq_zero_of_lt hlogu,
        add_zero] at h2
    -- the coefficient `u` and the tail `r`
    have hum : u ∈ S.CSet a c := by
      have h1 := (Vh.vhC_div _ hw (Om (1 + 1) * g₁)).2.2 (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hg₁m)
      have e1 : (leWe g₁ * u + r) / ω ^ (Om (1 + 1) * g₁) = u := by
        show (leWe g₁ * u + r) / leWe g₁ = u
        rw [Ordinal.mul_add_div _ (leWe_pos g₁).ne', Ordinal.div_eq_zero_of_lt hrlt, add_zero]
      rwa [e1] at h1
    have hrm : r ∈ S.CSet a c := by
      have h1 := (Vh.vhC_div _ hw (Om (1 + 1) * g₁)).2.1
      have e1 : (leWe g₁ * u + r) % ω ^ (Om (1 + 1) * g₁) = r := by
        show (leWe g₁ * u + r) % leWe g₁ = r
        rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrlt]
      rwa [e1] at h1
    exact krMax_mem (ih₁ hg₁m) (krMax_mem hum (ihr hrm))

/-- `w < G` for every strongly critical `G > Ω₂`. -/
theorem krLt {l G : Ordinal.{0}} (hG : SC G) (h2 : Om (1 + 1) < G) : ∀ {w qw : Ordinal.{0}}, KoThr S l w qw →
    w < G := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro w qw hk
  induction hk with
  | code _ hθ => exact (hθ.trans (psi_lt hκ2 _)).trans h2
  | @term g₁ q₁ u r qr _ _ _ huθ _ hrlt ih₁ _ =>
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    have hlt : leWe g₁ * u + r < leWe (g₁ + 1) :=
      calc leWe g₁ * u + r < leWe g₁ * u + leWe g₁ := (add_lt_add_iff_left _).2 hrlt
        _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
        _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
    exact hlt.trans (leWe_lt_SC hG h2 (hG.isSuccLimit.add_one_lt ih₁)).1

/-- The tower of `x ↦ X + x`: `Ω₂·(X + x) = Ω₂·X + ω^{Ω₂}·x`, threshold `0`. -/
theorem krTwAdd (X : Ordinal.{0}) : KkTw S (fun v => X + v) (KaT.base (Om (1 + 1) * X) (Om (1 + 1))) 0 :=
  ⟨fun v => by
    show Om (1 + 1) * (X + v) = _
    rw [KaT.ev_base, gg_SC_eps ldOm2_SC, mul_add], fun a c _ _ => by
    show Om (1 + 1) ∈ S.CSet a c
    exact mxOm2_mem a c⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The ownership at the first use**, with any `d < Ω₂` for `1`. -/
theorem koGOLd {β d h q : Ordinal.{0}} (hd : d < Om (1 + 1)) (hk : KoThr S l h q) :
    ∀ {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {qF : Ordinal.{0}}, Monotone F → KkTw S F t₂ qF →
      qF < S.psi (β + leWe (F 1)) (Om (1 + 1)) → q < S.psi (β + leWe (F (h + d))) (Om (1 + 1)) →
        q < S.psi (β + leWe (F h)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hP : ∀ {F : Ordinal.{0} → Ordinal.{0}}, Monotone F → ∀ {x y : Ordinal.{0}}, x ≤ y →
      S.psi (β + leWe (F x)) (Om (1 + 1)) ≤ S.psi (β + leWe (F y)) (Om (1 + 1)) := fun hF _ _ hxy =>
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hF hxy)))).1
  induction hk with
  | @code g _ hθ =>
    intro F t₂ qF hF htw hqF hq
    have hg2 : g < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    exact kkOwn hF htw hqF g (hq.trans_le (hP hF (ldOm2_SC.isPrincipal hg2 hd).le))
  | @term g₁ q₁ u r qr hk₁ huc hu0 huθ hkr hrlt ih₁ ihr =>
    intro F t₂ qF hF htw hqF hq
    set p := leWe g₁ * u with hpdef
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    have hlt : p + r < leWe (g₁ + 1) :=
      calc p + r < p + leWe g₁ := (add_lt_add_iff_left _).2 hrlt
        _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
        _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
    have hdW : d < leWe (g₁ + 1) := hd.trans_le (by rw [← leWe_one]; exact leWe_mono le_add_self)
    have hh1 : p + r + d ≤ leWe (g₁ + 1) := by
      unfold leWe at hlt hdW ⊢
      exact (Ordinal.isPrincipal_add_omega0_opow _ hlt hdW).le
    have hq₁ : q₁ < S.psi (β + leWe (F (p + r + d))) (Om (1 + 1)) := (le_max_left _ _).trans_lt hq
    have hqu : u < S.psi (β + leWe (F (p + r + d))) (Om (1 + 1)) :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hq
    have hqr : qr < S.psi (β + leWe (F (p + r + d))) (Om (1 + 1)) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hq
    have hg₁ : q₁ < S.psi (β + leWe (F (leWe g₁))) (Om (1 + 1)) :=
      kpExpW hl hX hk₁ hF htw hqF (hq₁.trans_le (hP hF hh1))
    have hW1 : (1 : Ordinal.{0}) ≤ leWe g₁ := Order.one_le_iff_pos.2 (leWe_pos g₁)
    have hu : u < S.psi (β + leWe (F p)) (Om (1 + 1)) :=
      koCoef hl hX hk₁ hF htw (hqF.trans_le (hP hF hW1)) hg₁ u (hqu.trans_le (hP hF hh1))
    have hFA : Monotone fun v => F (p + v) := fun _ _ hle => hF (add_le_add le_rfl hle)
    have hr : qr < S.psi (β + leWe (F (p + r))) (Om (1 + 1)) :=
      ihr hFA (kpTwA htw p) (max_lt (hqF.trans_le (hP hF le_add_self)) (SC_psi hκ2 _).1) (by
        show qr < S.psi (β + leWe (F (p + (r + d)))) (Om (1 + 1))
        rw [← add_assoc]
        exact hqr)
    have hle1 : leWe g₁ ≤ p + r := (Ordinal.le_mul_left _ hu0).trans le_self_add
    exact max_lt (hg₁.trans_le (hP hF hle1)) (max_lt (hu.trans_le (hP hF le_self_add)) hr)

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE CHAIN ALONG A `W`-TERM `w`** (`Ω₂ ∣ w`) over a shift `X₀` with the law at every `X₀ + e`. -/
theorem krPoly : ∀ {w qw : Ordinal.{0}}, KoThr S l w qw → Om (1 + 1) ∣ w →
    ∀ {X₀ K₀ q₀ : Ordinal.{0}}, ZdShQ S l X₀ K₀ q₀ →
    ∀ (Q₀ : Ordinal.{0} → Prop), (∀ β, Q₀ β → q₀ < S.psi (β + leWe X₀) (Om (1 + 1))) →
    (∀ β β', β ≤ β' → Q₀ β → Q₀ β') →
    (∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X₀ e β →
      Q₀ β → ZdLaw S l A X₀ e β) →
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l (X₀ + w) e β →
      Q₀ β → qw < S.psi (β + leWe (X₀ + w + (e + 1))) (Om (1 + 1)) → ZdLaw S l A (X₀ + w) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro w qw hk
  induction hk with
  | @code g _ hθ =>
    intro hdv X₀ K₀ q₀ hs0 Q₀ hQq hQup H0 e hec he2 β hβD hB hQ _
    have hg0 : g = 0 := by
      by_contra h0
      exact absurd ((Ordinal.le_of_dvd h0 hdv).trans_lt (hθ.trans (psi_lt hκ2 _))) (lt_irrefl _)
    subst hg0
    rw [add_zero] at hB ⊢
    exact H0 e hec he2 β hβD hB hQ
  | @term g₁ q₁ u r qr hk₁ huc hu0 huθ hkr hrlt _ ihr =>
    intro hdv X₀ K₀ q₀ hs0 Q₀ hQq hQup H0 e hec he2 β hβD hB hQ hq
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    -- `g₁ ≥ 1`
    have hg₁1 : 1 ≤ g₁ := by
      rcases eq_or_ne g₁ 0 with h0 | h0
      · exfalso
        subst h0
        rw [leWe_zero] at hrlt
        have hr0 : r = 0 := Order.lt_one_iff.1 hrlt
        subst hr0
        rw [leWe_zero, one_mul, add_zero] at hdv
        exact absurd ((Ordinal.le_of_dvd hu0.ne' hdv).trans_lt hu2) (lt_irrefl _)
      · exact Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h0)
    -- `Ω₂ ∣ r`
    have hdvp : Om (1 + 1) ∣ leWe g₁ * u := by
      rw [← leWe_one]; exact (leWe_dvd hg₁1).trans (dvd_mul_right _ _)
    have hdvr : Om (1 + 1) ∣ r := by
      obtain ⟨k, hk⟩ := hdvp
      have h := Ordinal.mod_eq_zero_of_dvd hdv
      rw [hk, Ordinal.mul_add_mod_self] at h
      exact Ordinal.dvd_of_mod_eq_zero h
    -- the bound below `X₀ + W^{g₁+1}`
    have hrW : r + (e + 1) < leWe g₁ := by
      have he1 : e + 1 < leWe g₁ :=
        (ldOm2_SC.isSuccLimit.add_one_lt he2).trans_le (by rw [← leWe_one]; exact leWe_mono hg₁1)
      unfold leWe at hrlt he1 ⊢
      exact Ordinal.isPrincipal_add_omega0_opow _ hrlt he1
    have hwW : leWe g₁ * u + r + (e + 1) ≤ leWe (g₁ + 1) := by
      rw [add_assoc]
      calc leWe g₁ * u + (r + (e + 1)) ≤ leWe g₁ * u + leWe g₁ := add_le_add le_rfl hrW.le
        _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
        _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
    have hle : X₀ + (leWe g₁ * u + r) + (e + 1) ≤ X₀ + leWe (g₁ + 1) := by
      rw [add_assoc]
      exact add_le_add le_rfl hwW
    have hM : S.psi (β + leWe (X₀ + (leWe g₁ * u + r) + (e + 1))) (Om (1 + 1)) ≤
        S.psi (β + leWe (X₀ + leWe (g₁ + 1))) (Om (1 + 1)) :=
      (psi_mono hκ2 (add_le_add le_rfl (leWe_mono hle))).1
    have hq₁W : q₁ < S.psi (β + leWe (X₀ + leWe (g₁ + 1))) (Om (1 + 1)) := ((le_max_left _ _).trans_lt hq).trans_le hM
    have huW : u < S.psi (β + leWe (X₀ + leWe (g₁ + 1))) (Om (1 + 1)) :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hq).trans_le hM
    -- the base condition `ZyQ` of the chain at `g₁`
    have hq₁' : q₁ < S.psi (β + leWe (X₀ + leWe g₁)) (Om (1 + 1)) := koGOL_top hl hX hk₁ hq₁W
    have hown : ∀ ζ', GxCl (upsilon l) (ldAtR S l) ζ' → ζ' ≤ u →
        ζ' < S.psi (β + leWe (X₀ + leWe g₁ * ζ')) (Om (1 + 1)) := fun ζ' _ hζ' =>
      koCoef hl hX hk₁ (F := fun v => X₀ + v) (fun _ _ hle => add_le_add le_rfl hle) (krTwAdd X₀)
        (SC_psi hκ2 _).1 hq₁' ζ' (hζ'.trans_lt huW)
    have hZ : ZyQ S l X₀ g₁ q₁ Q₀ u β := ⟨hQ, hq₁', hown⟩
    -- the chain at `g₁`, then the tail `r` over `X₀ + W^{g₁}·u`
    have hch := kqChain hl hX hA hρ g₁ q₁ hk₁ hg₁1 hs0 Q₀ hQq hQup H0 u huc huθ
    obtain ⟨q', hs', hq'⟩ := kqSh hl hX hs0 (koEx hl hX hk₁) hQq huc huθ
    have h := ihr hdvr hs' (ZyQ S l X₀ g₁ q₁ Q₀ u) hq' (fun _ _ hle hQ' => zyQ_up hQup hle hQ') hch e hec he2 β
      hβD (by rw [← add_assoc X₀ (leWe g₁ * u) r] at hB; exact hB) hZ (by
        have hqr := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hq
        rwa [← add_assoc X₀ (leWe g₁ * u) r] at hqr)
    rwa [← add_assoc X₀ (leWe g₁ * u) r]

/-- **The law at `(β + W^E·γ') + W^E`**, `E = Ω_{k+3} + w + e` (`β` normal, `W^{E+1} ∣ β`, `E` a member of the
closures above `ψ₂(β + W^E)`, `γ' < ψ₂(β + W^E·γ')`). -/
theorem krSucc (k : ℕ) {w qw : Ordinal.{0}} (hk : KoThr S l w qw) (hwdv : Om (1 + 1) ∣ w)
    {β e γ' : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e + 1) ∣ β)
    (hED : VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e))
    (hEm : ∀ a c : Ordinal.{0}, S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e)) (Om (1 + 1)) ≤ c →
      Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e ∈ S.CSet a c)
    (hqw : qw < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + (e + 1))) (Om (1 + 1)))
    (heE : e < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e)) (Om (1 + 1)))
    (hγc : GxCl (upsilon l) (ldAtR S l) γ') (hγθ : γ' < ConjT.th S)
    (hγown : γ' < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ') (Om (1 + 1))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ' +
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e)) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ' +
        leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e))) (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X₀ := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hX₀def
  set X := X₀ + w with hXdef
  set E := X + e with hEdef
  set β' := β + leWe E * γ' with hβ'def
  have hγ2 : γ' < Om (1 + 1) := hγθ.trans (psi_lt hκ2 _)
  have hγH : γ' ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγc
  have hE1W : E + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hED.2.2
  have hWE1 : leWe (E + 1) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hE1W).1
  have hWγ : leWe E * γ' < leWe (E + 1) := by
    rw [leWe_succ]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
  have hβ'D : VbD S l β' :=
    ⟨CSet.add_mem hβD.1 (leMulWe_mem hED.1 hγH), CSet.add_mem hβD.2.1 (leMulWe_mem hED.2.1 (CSet.of_lt hγθ)),
      vkOmW.1.isPrincipal hβD.2.2 (hWγ.trans hWE1)⟩
  obtain ⟨hWED, -⟩ := zxTW hl hX hED
  have hbD' : VbD S l (β' + leWe E) :=
    ⟨CSet.add_mem hβ'D.1 hWED.1, CSet.add_mem hβ'D.2.1 hWED.2.1, vkOmW.1.isPrincipal hβ'D.2.2 hWED.2.2⟩
  -- `β'` is normal
  have hβ'n : β' ∈ S.CSet β' (S.psi β' (Om (1 + 1))) := by
    rcases eq_or_ne γ' 0 with h0 | h0
    · rw [hβ'def, h0, mul_zero, add_zero]; exact hβn
    · have hle : β + leWe E ≤ β' := add_le_add le_rfl (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 h0))
      exact CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβn)
        (leMulWe_mem (hEm _ _ (psi_mono hκ2 hle).1) (CSet.of_lt hγown))
  have hββ' : β + leWe E ≤ β' + leWe E := add_le_add le_self_add le_rfl
  have heb' : e < S.psi (β' + leWe E) (Om (1 + 1)) := heE.trans_le (psi_mono hκ2 hββ').1
  have hdvβ' : leWe E ∣ β' := dvd_add ((leWe_dvd (le_of_lt (lt_add_one E))).trans hdv) (dvd_mul_right _ _)
  have hB : Ro.RoBaseE S l X e β' := by
    refine ⟨hdvβ', hβ'D.1, hbD'.2.2.trans_le (ConjT.OmW_le_A S _), fun d _ => (psi_mono hκ2 le_self_add).2 hβ'n,
      fun e' _ hle => ?_⟩
    have h0 := kgOwnBase (S := S) (β := β') (g₀ := X) (j := 0) (qj := 0) (fun a c _ _ => CSet.zero_mem a c)
      (SC_psi hκ2 _).1 e' (by
        rw [zero_add, leWe_one]
        exact (hle.trans_lt heb').trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono
          (add_le_add le_rfl he2.le)))).1)
    rwa [leWe_zero, one_mul] at h0
  have hqw' : qw < S.psi (β' + leWe (X₀ + w + (e + 1))) (Om (1 + 1)) :=
    hqw.trans_le (psi_mono hκ2 (add_le_add le_self_add le_rfl)).1
  have hlaw := krPoly hl hX hA hρ hk hwdv ((zdSh_Om hl hX (S := S) k).toQ (leRho hl hX).1.1)
    (fun _ => True) (fun _ _ => (SC_psi hκ2 _).1) (fun _ _ _ _ => trivial)
    (fun e hec he2 β hβD hB _ => xmTopUp S k l ηx A hl hX hA hρ e β hec he2 hβD hB) e hec he2 β' hβ'D hB trivial
    hqw'
  unfold ZdLaw leTe at hlaw
  exact hlaw

/-- **THE TOP LAW AT EVERY NORMAL `b = β + W^E·γ`**, `E = Ω_{k+3} + w + e` (`w` a `W`-term over the codes, `Ω₂ ∣ w`,
`e` a code), `W^{E+1} ∣ β`, `γ` a code with `0 < γ < θ`. -/
theorem krTop (k : ℕ) {w qw : Ordinal.{0}} (hk : KoThr S l w qw) (hwdv : Om (1 + 1) ∣ w)
    {β e γ : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (he2 : e < Om (1 + 1)) (hβD : VbD S l β)
    (hdv : leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e + 1) ∣ β)
    (hγc : GxCl (upsilon l) (ldAtR S l) γ) (hγ0 : 0 < γ) (hγθ : γ < ConjT.th S)
    (hbD : VbD S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ))
    (hbn : β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ ∈
      S.CSet (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ)
        (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ) (Om (1 + 1)))) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + w + e) * γ))
        (Om (1 + 1))) (Om 1) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X₀ := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hX₀def
  set X := X₀ + w with hXdef
  set E := X + e with hEdef
  set b := β + leWe E * γ with hbdef
  have hγ2 : γ < Om (1 + 1) := hγθ.trans (psi_lt hκ2 _)
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt hκ2 _
  have hwx := koEx hl hX hk
  -- divisibilities and the size of `w`
  have hX₀W : leWe X₀ = X₀ := Vn.vnWe_OmK k
  have h3 : ((k : Ordinal.{0}) + 1 + 1 + 1) ≠ 0 := (add_pos_of_right zero_lt_one _).ne'
  have hwX₀ : w < X₀ := krLt (SC_Om h3) (Vn.vnOm2_lt_K k) hk
  have hdvX₀ : Om (1 + 1) ∣ X₀ := by
    have := leWe_dvd (e := 1) (e' := X₀) (Order.one_le_iff_pos.2 (Om_pos h3))
    rwa [hX₀W, leWe_one] at this
  have hΩ2X : Om (1 + 1) ∣ X := dvd_add hdvX₀ hwdv
  -- the components lie below `ψ₂(b)`
  have hEγ := kjEfrom hdv hγ0.ne' hγ2 hbn
  have hem := khe_mem hΩ2X he2 hEγ.1
  have hXm := khX_mem hΩ2X he2 hEγ.1
  have hwm : w ∈ S.CSet b (S.psi b (Om (1 + 1))) := by
    have h1 := (Vh.vhC_div _ hXm (Om (1 + 1) * X₀)).2.1
    have e1 : X % ω ^ (Om (1 + 1) * X₀) = w := by
      show (X₀ + w) % leWe X₀ = w
      have e2 : X₀ + w = X₀ * 1 + w := by rw [mul_one]
      rw [hX₀W, e2, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hwX₀]
    rwa [e1] at h1
  have hqwb : qw < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 (krExtract hk hwm) (hwx.qθ.trans hθ2)
  have heb : e < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hem he2
  have hγb : γ < S.psi b (Om (1 + 1)) := lt_psi_of_mem hκ2 hEγ.2 hγ2
  -- `E ∈ D`
  have hED : VbD S l E := by
    refine ⟨(kjEfrom hdv hγ0.ne' hγ2 hbD.1).1, (kjEfrom hdv hγ0.ne' hγ2 hbD.2.1).1, ?_⟩
    refine lt_of_le_of_lt ?_ hbD.2.2
    refine ((Ordinal.right_le_opow E one_lt_omega0).trans (opow_le_opow_right omega0_pos
      (Ordinal.le_mul_right E ldOm2_SC.1))).trans ?_
    exact (Ordinal.le_mul_left (leWe E) hγ0).trans le_add_self
  -- `β` is normal
  have hbW1 : b ≤ β + leWe (E + 1) := by
    rw [leWe_succ]; exact add_le_add le_rfl (leMulWe_mono hγ2.le)
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := Zp.zpPreO_norm hκ2 (Om (1 + 1) * (E + 1)) hbn
    have hlt : leWe E * γ < leWe (E + 1) := by rw [leWe_succ]; exact mul_lt_mul_of_pos_left hγ2 (leWe_pos E)
    have e1 : ω ^ (Om (1 + 1) * (E + 1)) * (b / ω ^ (Om (1 + 1) * (E + 1))) = β := by
      obtain ⟨q, hq⟩ := hdv
      show leWe (E + 1) * (b / leWe (E + 1)) = β
      rw [hbdef, hq, Ordinal.mul_add_div _ (leWe_pos _).ne', Ordinal.div_eq_zero_of_lt hlt, add_zero]
    rwa [e1] at h
  -- the components of `E` lie below `ψ₂(β + W^E)`
  have hqw : qw < S.psi (β + leWe (X₀ + w + (e + 1))) (Om (1 + 1)) :=
    hqwb.trans_le (psi_mono hκ2 (hbW1.trans_eq (by rw [hEdef, add_assoc]))).1
  have heE : e < S.psi (β + leWe E) (Om (1 + 1)) := by
    have h0 := kgOwnBase (S := S) (β := β) (g₀ := X) (j := 0) (qj := 0) (fun a c _ _ => CSet.zero_mem a c)
      (SC_psi hκ2 _).1 e (by
        rw [zero_add, leWe_one]
        exact heb.trans_le (psi_mono hκ2 (hbW1.trans (add_le_add le_rfl (leWe_mono
          (Order.add_one_le_of_lt ((add_lt_add_iff_left X).2 he2)))))).1)
    rwa [leWe_zero, one_mul] at h0
  have hqwX : qw < S.psi (β + leWe X) (Om (1 + 1)) :=
    koGOLd hl hX (ldOm2_SC.isSuccLimit.add_one_lt he2) hk (F := fun v => X₀ + v)
      (fun _ _ hle => add_le_add le_rfl hle) (krTwAdd X₀) (SC_psi hκ2 _).1 (by
        show qw < S.psi (β + leWe (X₀ + (w + (e + 1)))) (Om (1 + 1))
        rw [← add_assoc]
        exact hqw)
  have hEm : ∀ a c : Ordinal.{0}, S.psi (β + leWe E) (Om (1 + 1)) ≤ c → E ∈ S.CSet a c := fun a c hc => by
    have hqc : qw < c := (hqwX.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1).trans_le hc
    exact CSet.add_mem (CSet.add_mem (Vn.vnOmK3_mem k a c)
      (hwx.mem a c ((psiS_bounds (S := S) _ 1).1.le.trans hc) hqc)) (CSet.of_lt (heE.trans_le hc))
  have hown := kjOwnCoef (S := S) hEm
  have hγW : γ < S.psi (β + leWe (E + 1)) (Om (1 + 1)) := hγb.trans_le (psi_mono hκ2 hbW1).1
  -- induction on the coefficient
  have hall : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 0 < c → c ≤ γ →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe E * c) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe E * c)) (Om (1 + 1))) (Om 1) := by
    intro c
    induction c using WellFoundedLT.induction with
    | ind c IHc =>
    intro hc hc0 hcγ
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c', hc'⟩ | hlimc
    · exact absurd h0 hc0.ne'
    · rw [succ_eq_add_one] at hc'
      subst hc'
      have hc2 : c' + 1 < Om (1 + 1) := hcγ.trans_lt hγ2
      have hc'c : GxCl (upsilon l) (ldAtR S l) c' :=
        (ldHull_iff hl hX ((lt_add_one c').trans hc2)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hc2).2 hc))
      have hc'θ : c' < ConjT.th S := ((lt_add_one c').trans_le hcγ).trans hγθ
      have hc'own : c' < S.psi (β + leWe E * c') (Om (1 + 1)) :=
        hown c' (((lt_add_one c').trans_le hcγ).trans hγW)
      have e1 : β + leWe E * (c' + 1) = β + leWe E * c' + leWe E := by rw [mul_add_one, add_assoc]
      rw [e1]
      exact krSucc hl hX hA hρ k hk hwdv hec he2 hβD hβn hdv hED hEm hqw heE hc'c hc'θ hc'own
    · exact kjLim hl hX hA hρ hβD hED hc (hcγ.trans_lt hγθ) hlimc fun c' hc'c hc'0 hc'lt =>
        IHc c' hc'lt hc'c hc'0 (hc'lt.le.trans hcγ)
  exact hall γ hγc hγ0 le_rfl

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kr

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kr.krPoly
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kr.krTop
