import Googology.Trans.PoR.InaccPsi.R2.KlExp

/-!
# Km: A CONSTANT ON THE LEFT OF A CONTEXT, and the `W`-terms closed under the pieces of a context

* `keCtx_prefix`, `kkTw_prefix` (**a constant `p` on the left**: `v ↦ p + C(v)` is a context with
  `R(x) = T p + R_C(x)`, the towers `addC (Ω₁·T p) t`, `addC (Ω₂·p) t₂`);
* `klZero`, `klW` (`W^{g₁}·u` is a `W`-term), `klApp` (**appending a smaller term**: `x + W^j·v` is a `W`-term once
  `x` is, `W^{j+1} ∣ x`, `j` a `W`-term, `v` a code).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Km

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy
  Googology.Trans.PoR.InaccPsi.R2.Zz Googology.Trans.PoR.InaccPsi.R2.Ka Googology.Trans.PoR.InaccPsi.R2.Ke
  Googology.Trans.PoR.InaccPsi.R2.Kk Googology.Trans.PoR.InaccPsi.R2.Kl

variable {S : InaccSeq.{0}}

theorem klZero {l : Ordinal.{0}} (hρ0 : 0 < upsilon l) : KlWT S l 0 :=
  KlWT.code (GxCl.zero hρ0) (ConjT.SC_th S).1

/-- `W^{g₁}·u` is a `W`-term. -/
theorem klW {l g₁ u : Ordinal.{0}} (hρ0 : 0 < upsilon l) (hg : KlWT S l g₁) (huc : GxCl (upsilon l) (ldAtR S l) u)
    (hu0 : 0 < u) (huθ : u < ConjT.th S) : KlWT S l (leWe g₁ * u) := by
  have h := KlWT.term hg huc hu0 huθ (klZero hρ0) (leWe_pos g₁)
  rwa [add_zero] at h

theorem KaT.addC_InC' {P : Ordinal.{0} → Prop} {a : Ordinal.{0}} (hadd : ∀ c, P c → P (a + c)) :
    ∀ t : KaT, t.InC P → (KaT.addC a t).InC P
  | KaT.base _ _, hC => ⟨hadd _ hC.1, hC.2⟩
  | KaT.up _ _, hC => ⟨hadd _ hC.1, hC.2⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A constant on the left of a context.** -/
theorem keCtx_prefix {p P qp : Ordinal.{0}} {C : Ordinal.{0} → Ordinal.{0}} {g : Ordinal.{0}}
    {R : Ordinal.{0} → Ordinal.{0}} {t : KaT} {q : Ordinal.{0}} (hp : ZxEx S l p P qp) (hC : KeCtx S l C g R t q) :
    KeCtx S l (fun v => p + C v) (p + g) (fun x => P + R x) (KaT.addC (Om 1 * P) t) (max qp q) := by
  have hmaxΘ : ∀ c, gxTh (upsilon l) (ldAtR S l) (max qp q) < c →
      gxTh (upsilon l) (ldAtR S l) qp < c ∧ gxTh (upsilon l) (ldAtR S l) q < c := fun c h =>
    ⟨(gxTh_mono (le_max_left _ _)).trans_lt h, (gxTh_mono (le_max_right _ _)).trans_lt h⟩
  refine ⟨fun v hv hvθ => ?_, fun v hv => add_le_add le_rfl (hC.le v hv),
    fun _ _ hab => (add_lt_add_iff_left p).2 (hC.sm hab),
    fun a c v h1 hq hv => CSet.add_mem (hp.mem a c h1 ((le_max_left _ _).trans_lt hq))
      (hC.mem a c v h1 ((le_max_right _ _).trans_lt hq) hv),
    fun v hv hvθ => by rw [Vh.vhT_add hl hX hp.D (hC.D v hv hvθ), hp.T, hC.T v hv hvθ],
    by rw [Vh.vhT_add hl hX hp.D hC.gD, hp.T, hC.Tg],
    ⟨CSet.add_mem hp.D.1 hC.gD.1, CSet.add_mem hp.D.2.1 hC.gD.2.1, vkOmW.1.isPrincipal hp.D.2.2 hC.gD.2.2⟩,
    fun _ _ h => add_le_add le_rfl (hC.Rmono h), fun x => by rw [KaT.addC_ev, mul_add, hC.ev],
    fun a c h hq => by rw [KaT.addC_bm]; exact hC.bm a c h (hmaxΘ c hq).2, ?_,
    zy_max_code hp.qc hC.qc, max_lt hp.qθ hC.qθ⟩
  · have h := hC.D v hv hvθ
    exact ⟨CSet.add_mem hp.D.1 h.1, CSet.add_mem hp.D.2.1 h.2.1, vkOmW.1.isPrincipal hp.D.2.2 h.2.2⟩
  · refine KaT.addC_InC' (fun c hc a c' h hq => CSet.add_mem
      (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hp.Hm a c' h (hmaxΘ c' hq).1)) (hc a c' h hq)) t ?_
    exact KaT.InC.imp (fun y hy a c h hq => hy a c h (hmaxΘ c hq).2) t hC.consts

omit hl hX in
/-- **A constant on the left of a context** has the tower `addC (Ω₂·p) t₂`. -/
theorem kkTw_prefix {p qp : Ordinal.{0}} {C : Ordinal.{0} → Ordinal.{0}} {t₂ : KaT} {q : Ordinal.{0}}
    (htw : KkTw S C t₂ q) : KkTw S (fun v => p + C v) (KaT.addC (Om (1 + 1) * p) t₂) (max qp q) :=
  ⟨fun v => by rw [KaT.addC_ev, mul_add, htw.ev2], fun a c h hq => by
    rw [KaT.addC_bm]; exact htw.bm2 a c h ((le_max_right _ _).trans_lt hq)⟩

/-- **Appending a smaller term**: `x + W^j·v` is a `W`-term once `x` is, `W^{j+1} ∣ x`. -/
theorem klApp {j v : Ordinal.{0}} (hj : KlWT S l j) (hvc : GxCl (upsilon l) (ldAtR S l) v) (hv0 : 0 < v)
    (hvθ : v < ConjT.th S) : ∀ {x : Ordinal.{0}}, KlWT S l x → leWe (j + 1) ∣ x → KlWT S l (x + leWe j * v) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hv2 : v < Om (1 + 1) := hvθ.trans (psi_lt hκ2 _)
  have hWjv : leWe j * v < leWe (j + 1) := by rw [leWe_succ]; exact mul_lt_mul_of_pos_left hv2 (leWe_pos j)
  intro x hx
  induction hx with
  | @code g _ hθ =>
    intro hdv
    -- a code divisible by `W^{j+1} ≥ Ω₂` is `0`
    have hg0 : g = 0 := by
      by_contra h0
      have hle := Ordinal.le_of_dvd h0 hdv
      have h1 : Om (1 + 1) ≤ leWe (j + 1) := by rw [← leWe_one]; exact leWe_mono le_add_self
      exact absurd ((h1.trans hle).trans_lt (hθ.trans (psi_lt hκ2 _))) (lt_irrefl _)
    subst hg0
    rw [zero_add]
    exact klW hρSC.1 hj hvc hv0 hvθ
  | @term g₁ u r hg₁ huc hu0 huθ hr hrlt _ ihr =>
    intro hdv
    -- `W^{j+1} ∣ r`, so `j + 1 ≤ g₁` and the appended term stays below `W^{g₁}`
    have hjg : j + 1 ≤ g₁ := by
      by_contra hc
      push Not at hc
      -- `W^{g₁} ≤ W^{g₁}·u + r` is divisible by `W^{j+1} > W^{g₁}`: impossible below `W^{g₁+1}`
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
    rw [add_assoc]
    exact KlWT.term hg₁ huc hu0 huθ (ihr hdvr) hlt

end Main

end Googology.Trans.PoR.InaccPsi.R2.Km
