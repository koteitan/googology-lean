import Googology.Trans.PoR.InaccPsi.R2.KoOwn

/-!
# Kp: THE CLASSIFICATION OF THE LIMIT `W`-TERMS WITH THE OWNERSHIP OF THEIR PIECES

`W^x = leWe x`, `T`, `Θ`, `Ko.KoThr`, `Ke.KeCtx`, `Kk.KkTw` as before; `F` is an exponent context with a `D`-level
tower (`Kk.KkTw`, `Monotone F`, its threshold below `ψ₂(β + W^{F(1)})`), `P(x) = ψ₂(β + W^{F(x)})`.

* `kpPred` (`KoThr (x + 1) q ⇒ KoThr x q'`, `q' ≤ q`), `kpApp` (**appending** `W^j·v` to a `W`-term divisible by
  `W^{j+1}`, the threshold at most `max q_x (max q_j v)`);
* `kpTwW`, `kpTwA`, `kpTwPW` (the towers of `F(W^x)`, `F(p + x)`, `F(p + W^x)`), `kpExpW` (the exponent: `q₁ < P(W^{g₁+1})`
  gives `q₁ < P(W^{g₁})`), `kpLead` (**the leading term `W^{g₁}·u` is owned**: its threshold lies below `P(W^{g₁}·u)`);
* `kpClass` (**THE CLASSIFICATION WITH THE OWNERSHIP**: a limit `W`-term `g` with its threshold below `P(g)` is a point
  of continuity of `T` along `W`-terms `g' < g` with their thresholds below `P(g')`, or the top `C(Ω₂) = g` of a
  context `C` (`Ke.KeCtx`) with its threshold below `P(C(1))` whose values `C(v) < g` at the codes have their
  thresholds below `P(C(v))` once `v < P(C(v))`).  As `Kn.knClass`, by induction on the `W`-term, the context `F`
  moved to `F(p + x)` (a tail) and `F(p + W^x)` (a nested exponent).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy
  Googology.Trans.PoR.InaccPsi.R2.Zz Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Ke Googology.Trans.PoR.InaccPsi.R2.Kk Googology.Trans.PoR.InaccPsi.R2.Kl
  Googology.Trans.PoR.InaccPsi.R2.Km Googology.Trans.PoR.InaccPsi.R2.Kn Googology.Trans.PoR.InaccPsi.R2.Ko

variable {S : InaccSeq.{0}}

/-- The tower of `F(W^x)`. -/
theorem kpTwW {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {qF : Ordinal.{0}} (htw : KkTw S F t₂ qF) :
    KkTw S (fun v => F (leWe v)) (KaT.comp t₂ (KaT.up 0 (KaT.base 0 (Om (1 + 1))))) (max qF 0) :=
  koTw_comp (G := fun v => leWe v) htw (fun v => by
    unfold leWe
    rw [KaT.ev_up, KaT.ev_base, gg_SC_eps ldOm2_SC]
    simp only [zero_add]) (fun a c _ _ => by
    show Om (1 + 1) ∈ S.CSet a c
    exact mxOm2_mem a c)

/-- The tower of `F(p + x)`. -/
theorem kpTwA {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {qF : Ordinal.{0}} (htw : KkTw S F t₂ qF)
    (p : Ordinal.{0}) : KkTw S (fun v => F (p + v)) (KaT.comp t₂ (KaT.base p 0)) (max qF 0) :=
  koTw_comp (G := fun v => p + v) htw (fun v => by rw [KaT.ev_base, opow_zero, one_mul]) (fun a c _ _ => by
    show (0 : Ordinal.{0}) ∈ S.CSet a c
    exact CSet.zero_mem a c)

/-- The tower of `F(p + W^x)`. -/
theorem kpTwPW {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {qF : Ordinal.{0}} (htw : KkTw S F t₂ qF)
    (p : Ordinal.{0}) :
    KkTw S (fun v => F (p + leWe v)) (KaT.comp t₂ (KaT.up p (KaT.base 0 (Om (1 + 1))))) (max qF 0) :=
  koTw_comp (G := fun v => p + leWe v) htw (fun v => by
    unfold leWe
    rw [KaT.ev_up, KaT.ev_base, gg_SC_eps ldOm2_SC, zero_add]) (fun a c _ _ => by
    show Om (1 + 1) ∈ S.CSet a c
    exact mxOm2_mem a c)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `KoThr (x + 1) q ⇒ KoThr x q'` with `q' ≤ q`. -/
theorem kpPred : ∀ {y q : Ordinal.{0}}, KoThr S l y q → ∀ x, y = x + 1 → ∃ q', q' ≤ q ∧ KoThr S l x q' := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro y q hy
  induction hy with
  | @code g hc hθ =>
    intro x hx
    subst hx
    have h2 : x + 1 < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    have hH : x + 1 ∈ cdHull S l := (ldHull_iff hl hX h2).2 hc
    exact ⟨x, (lt_add_one x).le, KoThr.code ((ldHull_iff hl hX ((lt_add_one x).trans h2)).1
      (mem_of_add_one_mem hH)) ((lt_add_one x).trans hθ)⟩
  | @term g₁ q₁ u r qr hk₁ huc hu0 huθ hkr hrlt _ ihr =>
    intro x hx
    rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hr'⟩ | hlim
    · subst h0
      rw [add_zero] at hx
      rcases eq_or_ne g₁ 0 with hg0 | hg0
      · subst hg0
        rw [leWe_zero, one_mul] at hx
        subst hx
        have h2 : x + 1 < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
        have hH : x + 1 ∈ cdHull S l := (ldHull_iff hl hX h2).2 huc
        exact ⟨x, (lt_add_one x).le.trans ((le_max_left _ _).trans (le_max_right _ _)),
          KoThr.code ((ldHull_iff hl hX ((lt_add_one x).trans h2)).1 (mem_of_add_one_mem hH))
            ((lt_add_one x).trans huθ)⟩
      · exfalso
        have h := kn_lim_W hg0 hu0
        rw [hx] at h
        exact kn_not_lim_succ h
    · rw [succ_eq_add_one] at hr'
      subst hr'
      have hx' : x = leWe g₁ * u + r' := by
        rw [← add_assoc, ← succ_eq_add_one, ← succ_eq_add_one] at hx
        exact (Order.succ_injective hx).symm
      subst hx'
      obtain ⟨q', hq', hk'⟩ := ihr r' rfl
      exact ⟨_, max_le_max le_rfl (max_le_max le_rfl hq'),
        KoThr.term hk₁ huc hu0 huθ hk' ((lt_add_one r').trans hrlt)⟩
    · exfalso
      have h := isSuccLimit_add (leWe g₁ * u) hlim
      rw [hx] at h
      exact kn_not_lim_succ h

/-- **Appending a smaller term**: `x + W^j·v` with its threshold at most `max q_x (max q_j v)`. -/
theorem kpApp {j qj v : Ordinal.{0}} (hj : KoThr S l j qj) (hvc : GxCl (upsilon l) (ldAtR S l) v) (hv0 : 0 < v)
    (hvθ : v < ConjT.th S) : ∀ {x qx : Ordinal.{0}}, KoThr S l x qx → leWe (j + 1) ∣ x →
      ∃ q', KoThr S l (x + leWe j * v) q' ∧ q' ≤ max qx (max qj v) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hv2 : v < Om (1 + 1) := hvθ.trans (psi_lt hκ2 _)
  have hWjv : leWe j * v < leWe (j + 1) := by rw [leWe_succ]; exact mul_lt_mul_of_pos_left hv2 (leWe_pos j)
  intro x qx hx
  induction hx with
  | @code g _ hθ =>
    intro hdv
    have hg0 : g = 0 := by
      by_contra h0
      have hle := Ordinal.le_of_dvd h0 hdv
      have h1 : Om (1 + 1) ≤ leWe (j + 1) := by rw [← leWe_one]; exact leWe_mono le_add_self
      exact absurd ((h1.trans hle).trans_lt (hθ.trans (psi_lt hκ2 _))) (lt_irrefl _)
    subst hg0
    rw [zero_add]
    have hk := KoThr.term hj hvc hv0 hvθ (KoThr.code (GxCl.zero hρSC.1) (ConjT.SC_th S).1) (leWe_pos j)
    rw [add_zero] at hk
    exact ⟨_, hk, max_le (le_max_of_le_right (le_max_left _ _))
      (max_le (le_max_of_le_right (le_max_right _ _)) zero_le)⟩
  | @term g₁ q₁ u r qr hk₁ huc hu0 huθ hkr hrlt _ ihr =>
    intro hdv
    have hjg : j + 1 ≤ g₁ := by
      by_contra hc
      push Not at hc
      have hpos : leWe g₁ * u + r ≠ 0 := (lt_of_lt_of_le (leWe_pos g₁) ((Ordinal.le_mul_left _ hu0).trans
        le_self_add)).ne'
      have hle := Ordinal.le_of_dvd hpos hdv
      have hlt : leWe g₁ * u + r < leWe (g₁ + 1) := by
        have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
        calc leWe g₁ * u + r < leWe g₁ * u + leWe g₁ := (add_lt_add_iff_left _).2 hrlt
          _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
          _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
          _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
      exact absurd (hle.trans_lt hlt) (not_lt.2 (leWe_mono (Order.add_one_le_of_lt hc)))
    have hdvr : leWe (j + 1) ∣ r := by
      obtain ⟨k, hk⟩ := (leWe_dvd hjg).trans (dvd_mul_right (leWe g₁) u)
      have h := Ordinal.mod_eq_zero_of_dvd hdv
      rw [hk, Ordinal.mul_add_mod_self] at h
      exact Ordinal.dvd_of_mod_eq_zero h
    have hlt : r + leWe j * v < leWe g₁ := by
      have h2 : leWe j * v < leWe g₁ := hWjv.trans_le (leWe_mono hjg)
      unfold leWe at hrlt h2 ⊢
      exact Ordinal.isPrincipal_add_omega0_opow _ hrlt h2
    obtain ⟨q'', hk'', hq''⟩ := ihr hdvr
    rw [add_assoc]
    refine ⟨_, KoThr.term hk₁ huc hu0 huθ hk'' hlt, ?_⟩
    exact max_le (le_max_of_le_left (le_max_left _ _)) (max_le
      (le_max_of_le_left ((le_max_left _ _).trans (le_max_right _ _)))
      (hq''.trans (max_le (le_max_of_le_left ((le_max_right _ _).trans (le_max_right _ _))) (le_max_right _ _))))

/-- **The exponent**: `q₁ < P(W^{g₁+1})` gives `q₁ < P(W^{g₁})`. -/
theorem kpExpW {β g₁ q₁ : Ordinal.{0}} (hk₁ : KoThr S l g₁ q₁) {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT}
    {qF : Ordinal.{0}} (hF : Monotone F) (htw : KkTw S F t₂ qF) (hqF : qF < S.psi (β + leWe (F 1)) (Om (1 + 1)))
    (hq₁ : q₁ < S.psi (β + leWe (F (leWe (g₁ + 1)))) (Om (1 + 1))) :
    q₁ < S.psi (β + leWe (F (leWe g₁))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h1W : (1 : Ordinal.{0}) ≤ leWe 1 := by rw [leWe_one]; exact (gg_one_lt_of_SC ldOm2_SC).le
  exact koGOL hl hX hk₁ (fun _ _ hle => hF (leWe_mono hle)) (kpTwW htw)
    (max_lt (hqF.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hF h1W)))).1) (SC_psi hκ2 _).1) hq₁

/-- **The leading term `W^{g₁}·u` is owned**: its threshold lies below `P(W^{g₁}·u)`. -/
theorem kpLead {β g₁ q₁ u : Ordinal.{0}} (hk₁ : KoThr S l g₁ q₁) {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT}
    {qF : Ordinal.{0}} (hF : Monotone F) (htw : KkTw S F t₂ qF) (hqF : qF < S.psi (β + leWe (F 1)) (Om (1 + 1)))
    (hq₁ : q₁ < S.psi (β + leWe (F (leWe (g₁ + 1)))) (Om (1 + 1))) (huc : GxCl (upsilon l) (ldAtR S l) u)
    (hu0 : 0 < u) (huθ : u < ConjT.th S) (hu : u < S.psi (β + leWe (F (leWe (g₁ + 1)))) (Om (1 + 1))) :
    KoThr S l (leWe g₁ * u) (max q₁ (max u 0)) ∧
      max q₁ (max u 0) < S.psi (β + leWe (F (leWe g₁ * u))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hP : ∀ {x y : Ordinal.{0}}, x ≤ y →
      S.psi (β + leWe (F x)) (Om (1 + 1)) ≤ S.psi (β + leWe (F y)) (Om (1 + 1)) := fun hxy =>
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hF hxy)))).1
  have hk := KoThr.term hk₁ huc hu0 huθ (KoThr.code (GxCl.zero hρSC.1) (ConjT.SC_th S).1) (leWe_pos g₁)
  rw [add_zero] at hk
  refine ⟨hk, ?_⟩
  have hW1 : (1 : Ordinal.{0}) ≤ leWe g₁ := Order.one_le_iff_pos.2 (leWe_pos g₁)
  have hg₁ := kpExpW hl hX hk₁ hF htw hqF hq₁
  have huo := koCoef hl hX hk₁ hF htw (hqF.trans_le (hP hW1)) hg₁ u hu
  exact max_lt (hg₁.trans_le (hP (Ordinal.le_mul_left _ hu0))) (max_lt huo (SC_psi hκ2 _).1)

/-- **THE CLASSIFICATION OF THE LIMIT `W`-TERMS WITH THE OWNERSHIP OF THEIR PIECES.** -/
theorem kpClass {β : Ordinal.{0}} : ∀ {g qg : Ordinal.{0}}, KoThr S l g qg → IsSuccLimit g →
    ∀ {F : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {qF : Ordinal.{0}}, Monotone F → KkTw S F t₂ qF →
    qF < S.psi (β + leWe (F 1)) (Om (1 + 1)) → qg < S.psi (β + leWe (F g)) (Om (1 + 1)) →
    (∀ y, y < vbT S l g → ∃ g' q', KoThr S l g' q' ∧ 1 ≤ g' ∧ g' < g ∧ y < vbT S l g' ∧
      q' < S.psi (β + leWe (F g')) (Om (1 + 1))) ∨
    (∃ (C R : Ordinal.{0} → Ordinal.{0}) (t : KaT) (q : Ordinal.{0}),
      KeCtx S l C g R t q ∧ C (Om (1 + 1)) = g ∧ q < S.psi (β + leWe (F (C 1))) (Om (1 + 1)) ∧
      ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → C v < g ∧
        (v < S.psi (β + leWe (F (C v))) (Om (1 + 1)) →
          ∃ q', KoThr S l (C v) q' ∧ q' < S.psi (β + leWe (F (C v))) (Om (1 + 1)))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hρ0 : (0 : Ordinal.{0}) < upsilon l := hρSC.1
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρ0
  have h0θ : (0 : Ordinal.{0}) < ConjT.th S := (ConjT.SC_th S).1
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
  have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hpos1 : ∀ x : Ordinal.{0}, x ≠ 0 → 1 ≤ x := fun x h => Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h)
  have hT0 : vbT S l 0 = 0 := Vh.vhT_zero hl hX
  have hP : ∀ {F : Ordinal.{0} → Ordinal.{0}}, Monotone F → ∀ {x y : Ordinal.{0}}, x ≤ y →
      S.psi (β + leWe (F x)) (Om (1 + 1)) ≤ S.psi (β + leWe (F y)) (Om (1 + 1)) := fun hF _ _ hxy =>
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hF hxy)))).1
  have hPpos : ∀ x, (0 : Ordinal.{0}) < S.psi x (Om (1 + 1)) := fun x => (SC_psi hκ2 x).1
  have h1P : ∀ x, (1 : Ordinal.{0}) < S.psi x (Om (1 + 1)) := fun x =>
    (gg_one_lt_of_SC Ph.ph_SC_Om1).trans (psiS_bounds (S := S) x 1).1
  intro g qg hk
  induction hk with
  | @code g hc hθ =>
    intro hlim F t₂ qF hF htw hqF hq
    left
    intro y hy
    have h2 : g < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    rw [vbT_code hl hX h2 ((ldHull_iff hl hX h2).2 hc)] at hy
    obtain ⟨c, hcc, hcg, hcy⟩ := gxTh_onto (xmTh_lim hl hX h2 hlim y hy)
    have hc2 : c < Om (1 + 1) := hcg.trans h2
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [gxTh_zero] at hcy; exact absurd hcy.symm (lt_of_le_of_lt zero_le (lt_add_one y)).ne'
    refine ⟨c, c, KoThr.code hcc (hcg.trans hθ), hpos1 c hc0, hcg, ?_, ?_⟩
    · rw [vbT_code hl hX hc2 ((ldHull_iff hl hX hc2).2 hcc), hcy]
      exact lt_add_one y
    · exact kkOwn hF htw hqF c ((hcg.trans hq).trans_le (hP hF h2.le))
  | @term g₁ q₁ u r qr hk₁ huc hu0 huθ hkr hrlt ih₁ ihr =>
    intro hlim F t₂ qF hF htw hqF hq
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    have huH : u ∈ cdHull S l := (ldHull_iff hl hX hu2).2 huc
    have hg₁D := klD hl hX (koWT hk₁)
    have hrD := klD hl hX (koWT hkr)
    have hT : vbT S l (leWe g₁ * u + r) = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u + vbT S l r :=
      Vh.vhT_cnfW hl hX hg₁D hrD huH hu2
    have hTp : vbT S l (leWe g₁ * u) = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u := by
      have h := Vh.vhT_cnfW hl hX hg₁D (Xi.xiD_zero l) huH hu2
      rwa [add_zero, hT0, add_zero] at h
    have hglt : leWe g₁ * u + r < leWe (g₁ + 1) :=
      calc leWe g₁ * u + r < leWe g₁ * u + leWe g₁ := (add_lt_add_iff_left _).2 hrlt
        _ = leWe g₁ * (u + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g₁ * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hu2)
        _ = leWe (g₁ + 1) := (leWe_succ g₁).symm
    have hq₁ : q₁ < S.psi (β + leWe (F (leWe (g₁ + 1)))) (Om (1 + 1)) :=
      ((le_max_left _ _).trans_lt hq).trans_le (hP hF hglt.le)
    have hqu : u < S.psi (β + leWe (F (leWe (g₁ + 1)))) (Om (1 + 1)) :=
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hq).trans_le (hP hF hglt.le)
    have hqr' : qr < S.psi (β + leWe (F (leWe g₁ * u + r))) (Om (1 + 1)) :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hq
    have hlead : ∀ u', GxCl (upsilon l) (ldAtR S l) u' → 0 < u' → u' < ConjT.th S →
        u' < S.psi (β + leWe (F (leWe (g₁ + 1)))) (Om (1 + 1)) →
        KoThr S l (leWe g₁ * u') (max q₁ (max u' 0)) ∧
          max q₁ (max u' 0) < S.psi (β + leWe (F (leWe g₁ * u'))) (Om (1 + 1)) :=
      fun u' huc' hu0' huθ' hu' => kpLead hl hX hk₁ hF htw hqF hq₁ huc' hu0' huθ' hu'
    rcases eq_or_ne r 0 with hr0 | hr0
    · -- `g = W^{g₁}·u`
      subst hr0
      rw [add_zero] at hlim hT hq ⊢
      rw [hT0, add_zero] at hT
      rcases zero_or_succ_or_isSuccLimit u with hu00 | ⟨u', hu'⟩ | hulim
      · exact absurd hu00 hu0.ne'
      · -- `u = u' + 1`
        rw [succ_eq_add_one] at hu'
        subst hu'
        have hu'2 : u' < Om (1 + 1) := (lt_add_one u').trans hu2
        have hu'c : GxCl (upsilon l) (ldAtR S l) u' :=
          (ldHull_iff hl hX hu'2).1 (mem_of_add_one_mem huH)
        have hu'θ : u' < ConjT.th S := (lt_add_one u').trans huθ
        obtain ⟨qp, hkp, hqp⟩ : ∃ qp, KoThr S l (leWe g₁ * u') qp ∧
            qp < S.psi (β + leWe (F (leWe g₁ * u'))) (Om (1 + 1)) := by
          rcases eq_or_ne u' 0 with h0 | h0
          · subst h0
            rw [mul_zero]
            exact ⟨0, KoThr.code h0c h0θ, hPpos _⟩
          · exact ⟨_, hlead u' hu'c (pos_iff_ne_zero.2 h0) hu'θ ((lt_add_one u').trans hqu)⟩
        set p := leWe g₁ * u' with hpdef
        have hgeq : leWe g₁ * (u' + 1) = p + leWe g₁ := mul_add_one _ _
        have hpx := koEx hl hX hkp
        have hdvp : leWe g₁ ∣ p := dvd_mul_right _ _
        have hFpW : Monotone fun x => F (p + leWe x) := fun _ _ h => hF (add_le_add le_rfl (leWe_mono h))
        have htwpW := kpTwPW htw p
        have h1W : (1 : Ordinal.{0}) ≤ leWe 1 := by rw [leWe_one]; exact (gg_one_lt_of_SC ldOm2_SC).le
        have hthr : max qF 0 < S.psi (β + leWe (F (p + leWe 1))) (Om (1 + 1)) :=
          max_lt (hqF.trans_le (hP hF (h1W.trans le_add_self))) (hPpos _)
        rcases zero_or_succ_or_isSuccLimit g₁ with hg0 | ⟨j, hj⟩ | hg₁lim
        · exfalso
          subst hg0
          rw [leWe_zero, one_mul] at hlim
          exact kn_not_lim_succ hlim
        · -- the base context `v ↦ p + W^j·v`
          rw [succ_eq_add_one] at hj
          subst hj
          obtain ⟨qj, hqjle, hkj⟩ := kpPred hl hX hk₁ j rfl
          have hjx := koEx hl hX hkj
          have hqj : qj < S.psi (β + leWe (F (p + leWe j))) (Om (1 + 1)) :=
            koGOL hl hX hkj hFpW htwpW hthr (by
              show qj < S.psi (β + leWe (F (p + leWe (j + 1)))) (Om (1 + 1))
              rw [← hgeq]
              exact hqjle.trans_lt ((le_max_left _ _).trans_lt hq))
          right
          refine ⟨fun v => p + leWe j * v, fun x => vbT S l p + leOe (vbT S l j) * x,
            KaT.base (Om 1 * vbT S l p) (Om 1 + Om 1 * vbT S l j), max qp qj, ?_, ?_, ?_, ?_⟩
          · rw [hgeq]; exact keCtx_base hl hX hpx hjx
          · show p + leWe j * Om (1 + 1) = leWe (j + 1) * (u' + 1)
            rw [hgeq, leWe_succ]
          · show max qp qj < S.psi (β + leWe (F (p + leWe j * 1))) (Om (1 + 1))
            rw [mul_one]
            exact max_lt (hqp.trans_le (hP hF le_self_add)) hqj
          · intro v hv hvθ
            have hv2 : v < Om (1 + 1) := hvθ.trans (psi_lt hκ2 _)
            refine ⟨?_, fun hvown => ?_⟩
            · show p + leWe j * v < leWe (j + 1) * (u' + 1)
              rw [hgeq, leWe_succ]
              exact (add_lt_add_iff_left p).2 (mul_lt_mul_of_pos_left hv2 (leWe_pos j))
            · rcases eq_or_ne v 0 with h0 | h0
              · show ∃ q', KoThr S l (p + leWe j * v) q' ∧
                  q' < S.psi (β + leWe (F (p + leWe j * v))) (Om (1 + 1))
                rw [h0, mul_zero, add_zero]
                exact ⟨qp, hkp, hqp⟩
              · obtain ⟨q', hk', hq'le⟩ := kpApp hl hX hkj hv (pos_iff_ne_zero.2 h0) hvθ hkp hdvp
                refine ⟨q', hk', hq'le.trans_lt (max_lt (hqp.trans_le (hP hF le_self_add)) (max_lt
                  (hqj.trans_le (hP hF (add_le_add le_rfl (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 h0)))))
                  hvown))⟩
        · have hq₁' : q₁ < S.psi (β + leWe (F (p + leWe g₁))) (Om (1 + 1)) := by
            rw [← hgeq]; exact (le_max_left _ _).trans_lt hq
          rcases ih₁ hg₁lim hFpW htwpW hthr hq₁' with hcont₁ | ⟨C₁, R₁, t₁, q₁', hC₁, hC₁Ω, hq₁C, hC₁v⟩
          · -- `g₁` continuous ⇒ `g` continuous
            left
            intro y hy
            obtain ⟨hWg₁D, hWg₁T⟩ := zxTW hl hX hg₁D
            have hpD := klD hl hX (koWT hkp)
            have hTg : vbT S l (leWe g₁ * (u' + 1)) = vbT S l p + leOe (vbT S l g₁) := by
              rw [hgeq, Vh.vhT_add hl hX hpD hWg₁D, hWg₁T]
            rw [hTg] at hy
            rcases lt_or_ge y (vbT S l p) with hyp | hyp
            · have hp0 : p ≠ 0 := by rintro h0; rw [h0, hT0] at hyp; exact absurd hyp (not_lt.2 zero_le)
              exact ⟨p, qp, hkp, hpos1 p hp0, by rw [hgeq]; exact lt_add_of_pos_right p (leWe_pos g₁), hyp, hqp⟩
            · set y' := y - vbT S l p with hy'def
              have hy' : y' < leOe (vbT S l g₁) := Ry.rySub_lt hyp hy
              obtain ⟨g'', q'', hk'', hg''1, hg''lt, hyg'', hq''⟩ : ∃ g'' q'', KoThr S l g'' q'' ∧ 1 ≤ g'' ∧
                  g'' < g₁ ∧ y' < leOe (vbT S l g'') ∧
                  q'' < S.psi (β + leWe (F (p + leWe g''))) (Om (1 + 1)) := by
                rcases eq_or_ne y' 0 with h0 | h0
                · have h1g : (1 : Ordinal.{0}) < g₁ := by
                    have := hg₁lim.add_one_lt (pos_iff_ne_zero.2 hg₁lim.ne_bot); rwa [zero_add] at this
                  exact ⟨1, 1, KoThr.code h1c h1θ, le_rfl, h1g, by rw [h0]; exact opow_pos _ omega0_pos, h1P _⟩
                · have hlog : log ω y' < Om 1 * vbT S l g₁ := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hy'
                  have hsd : log ω y' / Om 1 < vbT S l g₁ := (Ordinal.lt_mul_iff_div_lt hO1).1 hlog
                  obtain ⟨g'', q'', hk'', hg''1, hg''lt, hsg, hq''⟩ := hcont₁ _ hsd
                  refine ⟨g'', q'', hk'', hg''1, hg''lt, (lt_opow_iff_log_lt one_lt_omega0 h0).2 ?_, hq''⟩
                  have := Ordinal.lt_mul_succ_div (log ω y') hO1
                  rw [Order.succ_eq_add_one] at this
                  exact this.trans_le (mul_le_mul_right (Order.add_one_le_of_lt hsg) _)
              have hdv'' : leWe (g'' + 1) ∣ p := (leWe_dvd (Order.add_one_le_of_lt hg''lt)).trans hdvp
              obtain ⟨q', hk', hq'le⟩ := kpApp hl hX hk'' h1c zero_lt_one h1θ hkp hdv''
              rw [mul_one] at hk'
              obtain ⟨hWg''D, hWg''T⟩ := zxTW hl hX (klD hl hX (koWT hk''))
              refine ⟨p + leWe g'', q', hk', (Order.one_le_iff_pos.2 (leWe_pos g'')).trans le_add_self,
                by rw [hgeq]; exact (add_lt_add_iff_left p).2 (leWe_lt hg''lt), ?_, ?_⟩
              · rw [Vh.vhT_add hl hX hpD hWg''D, hWg''T]
                have e1 : y = vbT S l p + y' := (Ordinal.add_sub_cancel_of_le hyp).symm
                rw [e1]
                exact (add_lt_add_iff_left _).2 hyg''
              · exact hq'le.trans_lt (max_lt (hqp.trans_le (hP hF le_self_add)) (max_lt hq'' (h1P _)))
          · -- `g₁` the top of a context ⇒ `g` the top of the nest
            right
            refine ⟨fun v => p + leWe (C₁ v), fun x => vbT S l p + leOe (R₁ x),
              KaT.up (Om 1 * vbT S l p) (KaT.addC (Om 1) t₁), max qp q₁', ?_, ?_, ?_, ?_⟩
            · rw [hgeq]; exact keCtx_nest hl hX hpx hC₁
            · show p + leWe (C₁ (Om (1 + 1))) = leWe g₁ * (u' + 1)
              rw [hC₁Ω, hgeq]
            · exact max_lt (hqp.trans_le (hP hF le_self_add)) hq₁C
            · intro v hv hvθ
              obtain ⟨hClt, hCown⟩ := hC₁v v hv hvθ
              refine ⟨by
                show p + leWe (C₁ v) < leWe g₁ * (u' + 1)
                rw [hgeq]; exact (add_lt_add_iff_left p).2 (leWe_lt hClt), fun hvown => ?_⟩
              obtain ⟨q'', hk'', hq''⟩ := hCown hvown
              have hdv' : leWe (C₁ v + 1) ∣ p := (leWe_dvd (Order.add_one_le_of_lt hClt)).trans hdvp
              obtain ⟨q', hk', hq'le⟩ := kpApp hl hX hk'' h1c zero_lt_one h1θ hkp hdv'
              rw [mul_one] at hk'
              exact ⟨q', hk', hq'le.trans_lt (max_lt (hqp.trans_le (hP hF le_self_add)) (max_lt hq'' (h1P _)))⟩
      · -- `u` a limit code: continuous
        left
        intro y hy
        rw [hT] at hy
        have hOE : leOe (vbT S l g₁) ≠ 0 := (opow_pos _ omega0_pos).ne'
        set t := y / leOe (vbT S l g₁) with htdef
        have htu : t < gxTh (upsilon l) (ldAtR S l) u := (Ordinal.lt_mul_iff_div_lt hOE).1 hy
        obtain ⟨c, hcc, hcu, hct⟩ := gxTh_onto (xmTh_lim hl hX hu2 hulim t htu)
        have hc0 : c ≠ 0 := by
          rintro rfl; rw [gxTh_zero] at hct; exact absurd hct.symm (lt_of_le_of_lt zero_le (lt_add_one t)).ne'
        have hcθ : c < ConjT.th S := hcu.trans huθ
        have hc2 : c < Om (1 + 1) := hcu.trans hu2
        obtain ⟨hkc, hqc⟩ := hlead c hcc (pos_iff_ne_zero.2 hc0) hcθ (hcu.trans hqu)
        refine ⟨leWe g₁ * c, _, hkc,
          (Order.one_le_iff_pos.2 (leWe_pos g₁)).trans (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hc0)),
          mul_lt_mul_of_pos_left hcu (leWe_pos g₁), ?_, hqc⟩
        have h := Vh.vhT_cnfW hl hX hg₁D (Xi.xiD_zero l) ((ldHull_iff hl hX hc2).2 hcc) hc2
        rw [add_zero, hT0, add_zero] at h
        rw [h, hct]
        have := Ordinal.lt_mul_succ_div y hOE
        rwa [Order.succ_eq_add_one] at this
    · -- `r > 0`: inherit from `r`
      have hrlim : IsSuccLimit r := by
        rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨r', hr'⟩ | h
        · exact absurd h0 hr0
        · exfalso
          rw [succ_eq_add_one] at hr'
          subst hr'
          rw [← add_assoc] at hlim
          exact kn_not_lim_succ hlim
        · exact h
      obtain ⟨hkp, hqp⟩ := hlead u huc hu0 huθ hqu
      set p := leWe g₁ * u with hpdef
      have hFA : Monotone fun x => F (p + x) := fun _ _ h => hF (add_le_add le_rfl h)
      have htwA := kpTwA htw p
      have hthrA : max qF 0 < S.psi (β + leWe (F (p + 1))) (Om (1 + 1)) :=
        max_lt (hqF.trans_le (hP hF le_add_self)) (hPpos _)
      have hpq : ∀ x, max q₁ (max u 0) < S.psi (β + leWe (F (p + x))) (Om (1 + 1)) := fun x =>
        hqp.trans_le (hP hF le_self_add)
      rcases ihr hrlim hFA htwA hthrA hqr' with hcont | ⟨C, R, t, q, hC, hCΩ, hqC, hCv⟩
      · left
        intro y hy
        rw [hT] at hy
        rcases lt_or_ge y (leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u) with hyp | hyp
        · exact ⟨p, _, hkp, (Order.one_le_iff_pos.2 (leWe_pos g₁)).trans (Ordinal.le_mul_left _ hu0),
            lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0), by rw [hTp]; exact hyp, hqp⟩
        · have hy' : y - leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u < vbT S l r := Ry.rySub_lt hyp hy
          obtain ⟨r', qr', hkr', hr'1, hr'lt, hyr', hqr''⟩ := hcont _ hy'
          refine ⟨p + r', max q₁ (max u qr'), KoThr.term hk₁ huc hu0 huθ hkr' (hr'lt.trans hrlt),
            hr'1.trans le_add_self, (add_lt_add_iff_left _).2 hr'lt, ?_, ?_⟩
          · rw [Vh.vhT_cnfW hl hX hg₁D (klD hl hX (koWT hkr')) huH hu2]
            have e1 : y = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u +
                (y - leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u) :=
              (Ordinal.add_sub_cancel_of_le hyp).symm
            rw [e1]
            exact (add_lt_add_iff_left _).2 hyr'
          · exact max_lt ((le_max_left _ _).trans_lt (hpq r'))
              (max_lt (((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hpq r')) hqr'')
      · right
        have hpx := koEx hl hX hkp
        refine ⟨fun v => p + C v, fun x => vbT S l p + R x, KaT.addC (Om 1 * vbT S l p) t,
          max (max q₁ (max u 0)) q, keCtx_prefix hl hX hpx hC, by simp only [hCΩ],
          max_lt (hpq _) hqC, fun v hv hvθ => ?_⟩
        obtain ⟨hClt, hCown⟩ := hCv v hv hvθ
        refine ⟨(add_lt_add_iff_left _).2 hClt, fun hvown => ?_⟩
        obtain ⟨q'', hk'', hq''⟩ := hCown hvown
        exact ⟨max q₁ (max u q''), KoThr.term hk₁ huc hu0 huθ hk'' (hClt.trans hrlt),
          max_lt ((le_max_left _ _).trans_lt (hpq (C v)))
            (max_lt (((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hpq (C v))) hq'')⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kp

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kp.kpClass
