import Googology.Trans.PoR.InaccPsi.R2.KnCls

/-!
# Ko: THE OWNERSHIP OF THE COMPONENTS OF A `W`-TERM AT ITS FIRST USE

`W^x = leWe x`, `T`, `Θ`, `Kl.KlWT`, `Kk.KkTw`, `Kk.kkOwn` as before.  An exponent context `F` (the exponent of
`β + W^{F(x)}`) with a `D`-level tower (`Kk.KkTw`) composes with the inner maps `x ↦ p + x`, `x ↦ W^x`,
`x ↦ W^j·x` (`KaT.comp`, `koTw_comp`).  `KoThr h q`: `h` is a `W`-term over the codes and `q` the maximum of its code
components (its threshold).

* `KaT.comp` (`(comp t s)(x) = t(s(x))`), `koTw_comp`, `koTw_top` (`x ↦ X + W^x`, threshold `0`);
* `koEx` (`KoThr h q ⇒ Zx.ZxEx λ h (T h) q`), `koWT`, `klKo`;
* `koCoef` (**the coefficient**: below `ψ₂(β + W^{F(W^{h+1})})` every `v` has `v < ψ₂(β + W^{F(W^h·v)})`, once the
  threshold of `h` lies below `ψ₂(β + W^{F(W^h)})`),
* `koGOL` (**THE OWNERSHIP OF THE COMPONENTS AT THE FIRST USE**: for every exponent context `F` with a `D`-level tower
  whose threshold lies below `ψ₂(β + W^{F(1)})`, `q < ψ₂(β + W^{F(h+1)})` gives `q < ψ₂(β + W^{F(h)})`; by induction
  on `h`: `Kk.kkOwn` for a code, `koCoef` for the coefficient, the induction over `F(W^x)` for the exponent `g₁` and
  over `F(W^{g₁}·u + x)` for the tail), `koGOL_top` (the context `x ↦ X + W^x`).

No new axiom.  New definitions: `KaT.comp`, `KoThr`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ko

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy
  Googology.Trans.PoR.InaccPsi.R2.Zz Googology.Trans.PoR.InaccPsi.R2.Ka Googology.Trans.PoR.InaccPsi.R2.Kg
  Googology.Trans.PoR.InaccPsi.R2.Ke Googology.Trans.PoR.InaccPsi.R2.Kk Googology.Trans.PoR.InaccPsi.R2.Kl

variable {S : InaccSeq.{0}}

/-- **The composite of two towers**: `(comp t s)(x) = t(s(x))`. -/
noncomputable def KaT.comp : KaT → KaT → KaT
  | KaT.base c m, KaT.base d n => KaT.base (c + ω ^ m * d) (m + n)
  | KaT.base c m, KaT.up d s => KaT.up (c + ω ^ m * d) (KaT.addC m s)
  | KaT.up c t, s => KaT.up c (KaT.comp t s)

theorem KaT.comp_ev : ∀ (t s : KaT) (x : Ordinal.{0}), (KaT.comp t s).ev x = t.ev (s.ev x)
  | KaT.base c m, KaT.base d n, x => by
    simp only [KaT.comp, KaT.ev_base]
    rw [mul_add, ← mul_assoc, ← opow_add, add_assoc]
  | KaT.base c m, KaT.up d s, x => by
    simp only [KaT.comp, KaT.ev_up, KaT.ev_base, KaT.addC_ev]
    rw [mul_add, ← opow_add, add_assoc]
  | KaT.up c t, s, x => by
    simp only [KaT.comp, KaT.ev_up]
    rw [KaT.comp_ev t s x]

theorem KaT.comp_bm {P : Ordinal.{0} → Prop} (hadd : ∀ x y, P x → P y → P (x + y)) :
    ∀ t s : KaT, P t.bm → P s.bm → P (KaT.comp t s).bm
  | KaT.base _ _, KaT.base _ _, ht, hs => by
    show P (_ + _)
    exact hadd _ _ ht hs
  | KaT.base _ _, KaT.up _ s, _, hs => by
    show P (KaT.addC _ s).bm
    rw [KaT.addC_bm]
    exact hs
  | KaT.up _ t, s, ht, hs => KaT.comp_bm hadd t s ht hs

/-- **The composite of an exponent context with an inner tower.** -/
theorem koTw_comp {F G : Ordinal.{0} → Ordinal.{0}} {t₂ s : KaT} {q qs : Ordinal.{0}} (htw : KkTw S F t₂ q)
    (hG : ∀ v, G v = s.ev v) (hs : ∀ a c : Ordinal.{0}, Om 1 ≤ c → qs < c → s.bm ∈ S.CSet a c) :
    KkTw S (fun v => F (G v)) (KaT.comp t₂ s) (max q qs) :=
  ⟨fun v => by
    show Om (1 + 1) * F (G v) = _
    rw [htw.ev2, hG, KaT.comp_ev],
    fun a c h hq => KaT.comp_bm (P := (· ∈ S.CSet a c)) (fun _ _ hx hy => CSet.add_mem hx hy) t₂ s
      (htw.bm2 a c h ((le_max_left _ _).trans_lt hq)) (hs a c h ((le_max_right _ _).trans_lt hq))⟩

/-- **The top context** `x ↦ X + W^x` has the tower `Ω₂·X + ω^{Ω₂ + Ω₂·x}`, threshold `0`. -/
theorem koTw_top (X : Ordinal.{0}) :
    KkTw S (fun v => X + leWe v) (KaT.up (Om (1 + 1) * X) (KaT.base (Om (1 + 1)) (Om (1 + 1)))) 0 :=
  ⟨fun v => by
    show Om (1 + 1) * (X + leWe v) = _
    rw [KaT.ev_up, KaT.ev_base, gg_SC_eps ldOm2_SC]
    unfold leWe
    rw [mul_add, kg_Om2_mul_opow], fun a c _ _ => by
    show Om (1 + 1) ∈ S.CSet a c
    exact mxOm2_mem a c⟩

/-- **A `W`-term with its threshold** (the maximum of its code components). -/
inductive KoThr (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} → Prop
  | code {g : Ordinal.{0}} : GxCl (upsilon l) (ldAtR S l) g → g < ConjT.th S → KoThr S l g g
  | term {g₁ q₁ u r qr : Ordinal.{0}} : KoThr S l g₁ q₁ → GxCl (upsilon l) (ldAtR S l) u → 0 < u →
      u < ConjT.th S → KoThr S l r qr → r < leWe g₁ → KoThr S l (leWe g₁ * u + r) (max q₁ (max u qr))

theorem koWT {l h q : Ordinal.{0}} (hk : KoThr S l h q) : KlWT S l h := by
  induction hk with
  | code hc hθ => exact KlWT.code hc hθ
  | term _ huc hu0 huθ _ hr ih₁ ihr => exact KlWT.term ih₁ huc hu0 huθ ihr hr

theorem klKo {l h : Ordinal.{0}} (hk : KlWT S l h) : ∃ q, KoThr S l h q := by
  induction hk with
  | code hc hθ => exact ⟨_, KoThr.code hc hθ⟩
  | term _ huc hu0 huθ _ hr ih₁ ihr =>
    obtain ⟨q₁, h₁⟩ := ih₁
    obtain ⟨qr, h₂⟩ := ihr
    exact ⟨_, KoThr.term h₁ huc hu0 huθ h₂ hr⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A `W`-term with its threshold is exponent data.** -/
theorem koEx {h q : Ordinal.{0}} (hk : KoThr S l h q) : ZxEx S l h (vbT S l h) q := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  induction hk with
  | @code g hc hθ =>
    have h := Zz.zxEx_code hl hX hc hθ
    have h2 : g < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    rwa [← vbT_code hl hX h2 ((ldHull_iff hl hX h2).2 hc)] at h
  | @term g₁ q₁ u r qr _ huc hu0 huθ _ hr h1 hrx =>
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    have huH : u ∈ cdHull S l := (ldHull_iff hl hX hu2).2 huc
    have hg1W : g₁ + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt h1.D.2.2
    have hlt : leWe g₁ * u + r < leWe (g₁ + 1) := by
      calc leWe g₁ * u + r < leWe g₁ * u + leWe g₁ := (add_lt_add_iff_left _).2 hr
        _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
        _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
    have hD : VbD S l (leWe g₁ * u + r) :=
      ⟨CSet.add_mem (leMulWe_mem h1.D.1 huH) hrx.D.1,
        CSet.add_mem (leMulWe_mem h1.D.2.1 (CSet.of_lt huθ)) hrx.D.2.1,
        hlt.trans (leWe_lt_SC vkOmW.1 vkOmW.2 hg1W).1⟩
    have hT : vbT S l (leWe g₁ * u + r) = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u + vbT S l r :=
      Vh.vhT_cnfW hl hX h1.D hrx.D huH hu2
    have hmax : ∀ c, max q₁ (max u qr) < c → q₁ < c ∧ u < c ∧ qr < c := fun c h =>
      ⟨(le_max_left _ _).trans_lt h, ((le_max_left _ _).trans (le_max_right _ _)).trans_lt h,
        ((le_max_right _ _).trans (le_max_right _ _)).trans_lt h⟩
    have hmaxΘ : ∀ c, gxTh (upsilon l) (ldAtR S l) (max q₁ (max u qr)) < c →
        gxTh (upsilon l) (ldAtR S l) q₁ < c ∧ gxTh (upsilon l) (ldAtR S l) u < c ∧
          gxTh (upsilon l) (ldAtR S l) qr < c := fun c h =>
      ⟨(gxTh_mono (le_max_left _ _)).trans_lt h, (gxTh_mono ((le_max_left _ _).trans (le_max_right _ _))).trans_lt h,
        (gxTh_mono ((le_max_right _ _).trans (le_max_right _ _))).trans_lt h⟩
    refine ⟨hD, rfl, fun a c h hq => ?_, fun a c h hq => ?_,
      zy_max_code h1.qc (zy_max_code huc hrx.qc), max_lt h1.qθ (max_lt huθ hrx.qθ)⟩
    · obtain ⟨h₁, h₂, h₃⟩ := hmax c hq
      exact CSet.add_mem (leMulWe_mem (h1.mem a c h h₁) (CSet.of_lt h₂)) (hrx.mem a c h h₃)
    · obtain ⟨h₁, h₂, h₃⟩ := hmaxΘ c hq
      rw [hT]
      exact CSet.add_mem (leMulOe_mem (h1.Hm a c h h₁) (CSet.of_lt h₂)) (hrx.Hm a c h h₃)

/-- **The coefficient over `F(W^h·x)`**: below `ψ₂(β + W^{F(W^{h+1})})` every `v` has `v < ψ₂(β + W^{F(W^h·v)})`. -/
theorem koCoef {β h q : Ordinal.{0}} (hk : KoThr S l h q) {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT}
    {qF : Ordinal.{0}} (hF : Monotone F) (htw : KkTw S F t₂ qF)
    (hqF : qF < S.psi (β + leWe (F (leWe h))) (Om (1 + 1))) (hq : q < S.psi (β + leWe (F (leWe h))) (Om (1 + 1))) :
    ∀ v, v < S.psi (β + leWe (F (leWe (h + 1)))) (Om (1 + 1)) →
      v < S.psi (β + leWe (F (leWe h * v))) (Om (1 + 1)) := by
  have hsM : ∀ v, leWe h * v = (KaT.base 0 (Om (1 + 1) * h)).ev v := fun v => by
    unfold leWe
    rw [KaT.ev_base, zero_add]
  have hm := (koEx hl hX hk).mem
  have htwM := koTw_comp htw hsM (qs := q) (fun a c hc hqc => by
    show Om (1 + 1) * h ∈ S.CSet a c
    exact ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (hm a c hc hqc))
  have hFM : Monotone fun v => F (leWe h * v) := fun _ _ hle => hF (leMulWe_mono hle)
  have hFM1 : max qF q < S.psi (β + leWe (F (leWe h * 1))) (Om (1 + 1)) := by
    rw [mul_one]
    exact max_lt hqF hq
  intro v hv
  refine kkOwn hFM htwM hFM1 v ?_
  show v < S.psi (β + leWe (F (leWe h * Om (1 + 1)))) (Om (1 + 1))
  rw [← leWe_succ]
  exact hv

/-- **THE OWNERSHIP OF THE COMPONENTS AT THE FIRST USE**: `q < ψ₂(β + W^{F(h+1)})` gives `q < ψ₂(β + W^{F(h)})`. -/
theorem koGOL {β h q : Ordinal.{0}} (hk : KoThr S l h q) :
    ∀ {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {qF : Ordinal.{0}}, Monotone F → KkTw S F t₂ qF →
      qF < S.psi (β + leWe (F 1)) (Om (1 + 1)) → q < S.psi (β + leWe (F (h + 1))) (Om (1 + 1)) →
        q < S.psi (β + leWe (F h)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hP : ∀ {F : Ordinal.{0} → Ordinal.{0}}, Monotone F → ∀ {x y : Ordinal.{0}}, x ≤ y →
      S.psi (β + leWe (F x)) (Om (1 + 1)) ≤ S.psi (β + leWe (F y)) (Om (1 + 1)) := fun hF _ _ hxy =>
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hF hxy)))).1
  induction hk with
  | @code g _ hθ =>
    intro F t₂ qF hF htw hqF hq
    have hg2 : g < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    exact kkOwn hF htw hqF g (hq.trans_le (hP hF (Order.add_one_le_of_lt hg2)))
  | @term g₁ q₁ u r qr hk₁ huc hu0 huθ hkr hrlt ih₁ ihr =>
    intro F t₂ qF hF htw hqF hq
    set p := leWe g₁ * u with hpdef
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    have hlt : p + r < leWe (g₁ + 1) :=
      calc p + r < p + leWe g₁ := (add_lt_add_iff_left _).2 hrlt
        _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
        _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
    have hh1 : p + r + 1 ≤ leWe (g₁ + 1) := Order.add_one_le_of_lt hlt
    have hq₁ : q₁ < S.psi (β + leWe (F (p + r + 1))) (Om (1 + 1)) := (le_max_left _ _).trans_lt hq
    have hqu : u < S.psi (β + leWe (F (p + r + 1))) (Om (1 + 1)) :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hq
    have hqr : qr < S.psi (β + leWe (F (p + r + 1))) (Om (1 + 1)) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hq
    -- the exponent `g₁` over `F(W^x)`
    have hsW : ∀ v, leWe v = (KaT.up 0 (KaT.base 0 (Om (1 + 1)))).ev v := fun v => by
      unfold leWe
      rw [KaT.ev_up, KaT.ev_base, gg_SC_eps ldOm2_SC]
      simp only [zero_add]
    have htwW := koTw_comp htw hsW (qs := 0) (fun a c _ _ => by
      show Om (1 + 1) ∈ S.CSet a c
      exact mxOm2_mem a c)
    have hFW : Monotone fun v => F (leWe v) := fun _ _ hle => hF (leWe_mono hle)
    have h1W : (1 : Ordinal.{0}) ≤ leWe 1 := by rw [leWe_one]; exact (gg_one_lt_of_SC ldOm2_SC).le
    have hg₁ : q₁ < S.psi (β + leWe (F (leWe g₁))) (Om (1 + 1)) :=
      ih₁ hFW htwW (max_lt (hqF.trans_le (hP hF h1W)) (SC_psi hκ2 _).1) (hq₁.trans_le (hP hF hh1))
    -- the coefficient `u` over `F(W^{g₁}·x)`
    have hW1 : (1 : Ordinal.{0}) ≤ leWe g₁ := Order.one_le_iff_pos.2 (leWe_pos g₁)
    have hu : u < S.psi (β + leWe (F p)) (Om (1 + 1)) :=
      koCoef hl hX hk₁ hF htw (hqF.trans_le (hP hF hW1)) hg₁ u (hqu.trans_le (hP hF hh1))
    -- the tail `r` over `F(p + x)`
    have hsA : ∀ v, p + v = (KaT.base p 0).ev v := fun v => by rw [KaT.ev_base, opow_zero, one_mul]
    have htwA := koTw_comp htw hsA (qs := 0) (fun a c _ _ => by
      show (0 : Ordinal.{0}) ∈ S.CSet a c
      exact CSet.zero_mem a c)
    have hFA : Monotone fun v => F (p + v) := fun _ _ hle => hF (add_le_add le_rfl hle)
    have hr : qr < S.psi (β + leWe (F (p + r))) (Om (1 + 1)) :=
      ihr hFA htwA (max_lt (hqF.trans_le (hP hF le_add_self)) (SC_psi hκ2 _).1) (by
        show qr < S.psi (β + leWe (F (p + (r + 1)))) (Om (1 + 1))
        rw [← add_assoc]
        exact hqr)
    have hle1 : leWe g₁ ≤ p + r := (Ordinal.le_mul_left _ hu0).trans le_self_add
    exact max_lt (hg₁.trans_le (hP hF hle1)) (max_lt (hu.trans_le (hP hF le_self_add)) hr)

/-- **The ownership at the first use** over a shift: `q < ψ₂(β + W^{X + W^{h+1}})` gives `q < ψ₂(β + W^{X + W^h})`. -/
theorem koGOL_top {β X h q : Ordinal.{0}} (hk : KoThr S l h q)
    (hq : q < S.psi (β + leWe (X + leWe (h + 1))) (Om (1 + 1))) :
    q < S.psi (β + leWe (X + leWe h)) (Om (1 + 1)) :=
  koGOL hl hX hk (F := fun v => X + leWe v) (fun _ _ hle => add_le_add le_rfl (leWe_mono hle)) (koTw_top X)
    (SC_psi (InR_Om_succ 1) _).1 hq

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ko

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ko.koGOL
