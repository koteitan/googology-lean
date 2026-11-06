import Googology.Trans.PoR.InaccPsi.R2.KmPre

/-!
# Kn: THE CLASSIFICATION OF THE LIMIT `W`-TERMS: a point of continuity of `T`, or the top of a context

`W^x = leWe x`, `Ω^x = leOe x`, `T`, `Θ`, `Kl.KlWT`, `Ke.KeCtx`, `Kk.KkTw` as before.

* `klPred` (`KlWT (x + 1) ⇒ KlWT x`);
* `knClass` (**EVERY LIMIT `W`-TERM `g` IS A POINT OF CONTINUITY OF `T` OR THE TOP OF A CONTEXT**: either every
  `y < T g` has `y < T g'` for a `W`-term `1 ≤ g' < g`, or there is a context `C` (`Ke.KeCtx` with target `g`, a
  `D`-level tower `Kk.KkTw`, `C(Ω₂) = g`) whose values at the codes are `W`-terms below `g`).  By induction on the
  `W`-term: a code is continuous; `W^{g₁}·u + r`, `r > 0`, inherits from `r` (a constant on the left); `W^{g₁}·u`
  with `u` a limit code is continuous; `W^{g₁}·u' + W^{g₁}` is the top of the base context `v ↦ W^{g₁}·u' + W^{j}·v`
  when `g₁ = j + 1`, and inherits from `g₁` (the nest `v ↦ W^{g₁}·u' + W^{C(v)}`) when `g₁` is a limit.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zx Googology.Trans.PoR.InaccPsi.R2.Zy
  Googology.Trans.PoR.InaccPsi.R2.Zz Googology.Trans.PoR.InaccPsi.R2.Xm Googology.Trans.PoR.InaccPsi.R2.Ka
  Googology.Trans.PoR.InaccPsi.R2.Ke Googology.Trans.PoR.InaccPsi.R2.Kk Googology.Trans.PoR.InaccPsi.R2.Kl
  Googology.Trans.PoR.InaccPsi.R2.Km

variable {S : InaccSeq.{0}}

theorem kn_not_lim_succ {x : Ordinal.{0}} (h : IsSuccLimit (x + 1)) : False :=
  lt_irrefl _ (h.add_one_lt (lt_add_one x))

theorem kn_lim_W {g₁ u : Ordinal.{0}} (hg : g₁ ≠ 0) (hu : 0 < u) : IsSuccLimit (leWe g₁ * u) := by
  unfold leWe
  refine isSuccLimit_mul_left (isSuccLimit_opow_left isSuccLimit_omega0 ?_) hu
  exact (mul_pos ldOm2_SC.1 (pos_iff_ne_zero.2 hg)).ne'

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `KlWT (x + 1) ⇒ KlWT x`. -/
theorem klPred : ∀ {y : Ordinal.{0}}, KlWT S l y → ∀ x, y = x + 1 → KlWT S l x := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  intro y hy
  induction hy with
  | @code g hc hθ =>
    intro x hx
    subst hx
    have h2 : x + 1 < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    have hH : x + 1 ∈ cdHull S l := (ldHull_iff hl hX h2).2 hc
    exact KlWT.code ((ldHull_iff hl hX ((lt_add_one x).trans h2)).1 (mem_of_add_one_mem hH))
      ((lt_add_one x).trans hθ)
  | @term g₁ u r hg₁ huc hu0 huθ hr hrlt _ ihr =>
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
        exact KlWT.code ((ldHull_iff hl hX ((lt_add_one x).trans h2)).1 (mem_of_add_one_mem hH))
          ((lt_add_one x).trans huθ)
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
      exact KlWT.term hg₁ huc hu0 huθ (ihr r' rfl) ((lt_add_one r').trans hrlt)
    · exfalso
      have h := isSuccLimit_add (leWe g₁ * u) hlim
      rw [hx] at h
      exact kn_not_lim_succ h

/-- **THE CLASSIFICATION OF THE LIMIT `W`-TERMS.** -/
theorem knClass : ∀ {g : Ordinal.{0}}, KlWT S l g → IsSuccLimit g →
    (∀ y, y < vbT S l g → ∃ g', KlWT S l g' ∧ 1 ≤ g' ∧ g' < g ∧ y < vbT S l g') ∨
    (∃ (C R : Ordinal.{0} → Ordinal.{0}) (t : KaT) (q : Ordinal.{0}) (t₂ : KaT),
      KeCtx S l C g R t q ∧ KkTw S C t₂ q ∧ C (Om (1 + 1)) = g ∧
      ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → KlWT S l (C v) ∧ C v < g) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hρ0 : (0 : Ordinal.{0}) < upsilon l := hρSC.1
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρ0
  have h1c : GxCl (upsilon l) (ldAtR S l) 1 := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
  have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hpos1 : ∀ x : Ordinal.{0}, x ≠ 0 → 1 ≤ x := fun x h => Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 h)
  have hT0 : vbT S l 0 = 0 := Vh.vhT_zero hl hX
  intro g hg
  induction hg with
  | @code g hc hθ =>
    intro hlim
    left
    intro y hy
    have h2 : g < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
    rw [vbT_code hl hX h2 ((ldHull_iff hl hX h2).2 hc)] at hy
    obtain ⟨c, hcc, hcg, hcy⟩ := gxTh_onto (xmTh_lim hl hX h2 hlim y hy)
    have hc2 : c < Om (1 + 1) := hcg.trans h2
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [gxTh_zero] at hcy; exact absurd hcy.symm (lt_of_le_of_lt zero_le (lt_add_one y)).ne'
    refine ⟨c, KlWT.code hcc (hcg.trans hθ), hpos1 c hc0, hcg, ?_⟩
    rw [vbT_code hl hX hc2 ((ldHull_iff hl hX hc2).2 hcc), hcy]
    exact lt_add_one y
  | @term g₁ u r hg₁ huc hu0 huθ hr hrlt ih₁ ihr =>
    intro hlim
    have hu2 : u < Om (1 + 1) := huθ.trans (psi_lt hκ2 _)
    have huH : u ∈ cdHull S l := (ldHull_iff hl hX hu2).2 huc
    have hg₁D := klD hl hX hg₁
    have hrD := klD hl hX hr
    have hpWT : KlWT S l (leWe g₁ * u) := klW hρ0 hg₁ huc hu0 huθ
    have hTp : vbT S l (leWe g₁ * u) = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u := by
      have h := Vh.vhT_cnfW hl hX hg₁D (Xi.xiD_zero l) huH hu2
      rwa [add_zero, hT0, add_zero] at h
    have hT : vbT S l (leWe g₁ * u + r) = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u + vbT S l r :=
      Vh.vhT_cnfW hl hX hg₁D hrD huH hu2
    rcases eq_or_ne r 0 with hr0 | hr0
    · -- `g = W^{g₁}·u`
      subst hr0
      rw [add_zero] at hlim hT ⊢
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
        set p := leWe g₁ * u' with hpdef
        have hgeq : leWe g₁ * (u' + 1) = p + leWe g₁ := mul_add_one _ _
        have hpW : KlWT S l p := by
          rcases eq_or_ne u' 0 with h0 | h0
          · rw [hpdef, h0, mul_zero]; exact klZero hρ0
          · exact klW hρ0 hg₁ hu'c (pos_iff_ne_zero.2 h0) hu'θ
        obtain ⟨qp, hpx⟩ := klEx hl hX hpW
        have hdvp : leWe g₁ ∣ p := dvd_mul_right _ _
        rcases zero_or_succ_or_isSuccLimit g₁ with hg0 | ⟨j, hj⟩ | hg₁lim
        · exfalso
          subst hg0
          rw [leWe_zero, one_mul] at hlim
          exact kn_not_lim_succ hlim
        · -- the base context `v ↦ p + W^j·v`
          rw [succ_eq_add_one] at hj
          subst hj
          have hjW : KlWT S l j := klPred hl hX hg₁ j rfl
          obtain ⟨qj, hjx⟩ := klEx hl hX hjW
          right
          refine ⟨fun v => p + leWe j * v, fun x => vbT S l p + leOe (vbT S l j) * x,
            KaT.base (Om 1 * vbT S l p) (Om 1 + Om 1 * vbT S l j), max qp qj,
            KaT.base (Om (1 + 1) * p) (Om (1 + 1) + Om (1 + 1) * j), ?_, ?_, ?_, ?_⟩
          · rw [hgeq]; exact keCtx_base hl hX hpx hjx
          · exact ⟨(kkTw_base (S := S) (g₀ := p) (fun a c h hq => hjx.mem a c h hq)).ev2,
              fun a c h hq => (kkTw_base (S := S) (g₀ := p) (fun a c h hq => hjx.mem a c h hq)).bm2 a c h
                ((le_max_right _ _).trans_lt hq)⟩
          · show p + leWe j * Om (1 + 1) = leWe (j + 1) * (u' + 1)
            rw [hgeq, leWe_succ]
          · intro v hv hvθ
            have hv2 : v < Om (1 + 1) := hvθ.trans (psi_lt hκ2 _)
            have hlt : p + leWe j * v < leWe (j + 1) * (u' + 1) := by
              rw [hgeq, leWe_succ]
              exact (add_lt_add_iff_left p).2 (mul_lt_mul_of_pos_left hv2 (leWe_pos j))
            rcases eq_or_ne v 0 with h0 | h0
            · show KlWT S l (p + leWe j * v) ∧ p + leWe j * v < leWe (j + 1) * (u' + 1)
              rw [h0, mul_zero, add_zero]
              exact ⟨hpW, by rw [hgeq]; exact lt_add_of_pos_right p (leWe_pos _)⟩
            · exact ⟨klApp hl hX hjW hv (pos_iff_ne_zero.2 h0) hvθ hpW hdvp, hlt⟩
        · rcases ih₁ hg₁lim with hcont₁ | ⟨C₁, R₁, t₁, q₁, t₂₁, hC₁, htw₁, hC₁Ω, hC₁v⟩
          · -- `g₁` continuous ⇒ `g` continuous
            left
            intro y hy
            obtain ⟨hWg₁D, hWg₁T⟩ := zxTW hl hX hg₁D
            have hpD := klD hl hX hpW
            have hTg : vbT S l (leWe g₁ * (u' + 1)) = vbT S l p + leOe (vbT S l g₁) := by
              rw [hgeq, Vh.vhT_add hl hX hpD hWg₁D, hWg₁T]
            rw [hTg] at hy
            rcases lt_or_ge y (vbT S l p) with hyp | hyp
            · have hp0 : p ≠ 0 := by rintro h0; rw [h0, hT0] at hyp; exact absurd hyp (not_lt.2 zero_le)
              exact ⟨p, hpW, hpos1 p hp0, by rw [hgeq]; exact lt_add_of_pos_right p (leWe_pos g₁), hyp⟩
            · set y' := y - vbT S l p with hy'def
              have hy' : y' < leOe (vbT S l g₁) := Ry.rySub_lt hyp hy
              obtain ⟨g'', hg''W, hg''1, hg''lt, hyg''⟩ : ∃ g'', KlWT S l g'' ∧ 1 ≤ g'' ∧ g'' < g₁ ∧
                  y' < leOe (vbT S l g'') := by
                rcases eq_or_ne y' 0 with h0 | h0
                · have h1g : (1 : Ordinal.{0}) < g₁ := by
                    have := hg₁lim.add_one_lt (pos_iff_ne_zero.2 hg₁lim.ne_bot); rwa [zero_add] at this
                  exact ⟨1, KlWT.code h1c h1θ, le_rfl, h1g, by rw [h0]; exact opow_pos _ omega0_pos⟩
                · have hlog : log ω y' < Om 1 * vbT S l g₁ := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hy'
                  have hsd : log ω y' / Om 1 < vbT S l g₁ := (Ordinal.lt_mul_iff_div_lt hO1).1 hlog
                  obtain ⟨g'', hg''W, hg''1, hg''lt, hsg⟩ := hcont₁ _ hsd
                  refine ⟨g'', hg''W, hg''1, hg''lt, (lt_opow_iff_log_lt one_lt_omega0 h0).2 ?_⟩
                  have := Ordinal.lt_mul_succ_div (log ω y') hO1
                  rw [Order.succ_eq_add_one] at this
                  exact this.trans_le (mul_le_mul_right (Order.add_one_le_of_lt hsg) _)
              have hdv'' : leWe (g'' + 1) ∣ p := (leWe_dvd (Order.add_one_le_of_lt hg''lt)).trans hdvp
              have hg'W := klApp hl hX hg''W h1c zero_lt_one h1θ hpW hdv''
              rw [mul_one] at hg'W
              obtain ⟨hWg''D, hWg''T⟩ := zxTW hl hX (klD hl hX hg''W)
              refine ⟨p + leWe g'', hg'W, (Order.one_le_iff_pos.2 (leWe_pos g'')).trans le_add_self,
                by rw [hgeq]; exact (add_lt_add_iff_left p).2 (leWe_lt hg''lt), ?_⟩
              rw [Vh.vhT_add hl hX hpD hWg''D, hWg''T]
              have e1 : y = vbT S l p + y' := (Ordinal.add_sub_cancel_of_le hyp).symm
              rw [e1]
              exact (add_lt_add_iff_left _).2 hyg''
          · -- `g₁` the top of a context ⇒ `g` the top of the nest
            right
            refine ⟨fun v => p + leWe (C₁ v), fun x => vbT S l p + leOe (R₁ x),
              KaT.up (Om 1 * vbT S l p) (KaT.addC (Om 1) t₁), max qp q₁,
              KaT.up (Om (1 + 1) * p) (KaT.addC (Om (1 + 1)) t₂₁), ?_, ?_, ?_, ?_⟩
            · rw [hgeq]; exact keCtx_nest hl hX hpx hC₁
            · exact ⟨(kkTw_nest (g₁ := p) htw₁).ev2, fun a c h hq =>
                (kkTw_nest (g₁ := p) htw₁).bm2 a c h ((le_max_right _ _).trans_lt hq)⟩
            · show p + leWe (C₁ (Om (1 + 1))) = leWe g₁ * (u' + 1)
              rw [hC₁Ω, hgeq]
            · intro v hv hvθ
              obtain ⟨hCW, hClt⟩ := hC₁v v hv hvθ
              have hdv' : leWe (C₁ v + 1) ∣ p := (leWe_dvd (Order.add_one_le_of_lt hClt)).trans hdvp
              have h := klApp hl hX hCW h1c zero_lt_one h1θ hpW hdv'
              rw [mul_one] at h
              exact ⟨h, by rw [hgeq]; exact (add_lt_add_iff_left p).2 (leWe_lt hClt)⟩
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
        refine ⟨leWe g₁ * c, klW hρ0 hg₁ hcc (pos_iff_ne_zero.2 hc0) hcθ,
          (Order.one_le_iff_pos.2 (leWe_pos g₁)).trans (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hc0)),
          mul_lt_mul_of_pos_left hcu (leWe_pos g₁), ?_⟩
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
      rcases ihr hrlim with hcont | ⟨C, R, t, q, t₂, hC, htw, hCΩ, hCv⟩
      · left
        intro y hy
        rw [hT] at hy
        rcases lt_or_ge y (leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u) with hyp | hyp
        · exact ⟨leWe g₁ * u, hpWT, (Order.one_le_iff_pos.2 (leWe_pos g₁)).trans (Ordinal.le_mul_left _ hu0),
            lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0), by rw [hTp]; exact hyp⟩
        · have hy' : y - leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u < vbT S l r := Ry.rySub_lt hyp hy
          obtain ⟨r', hr'W, hr'1, hr'lt, hyr'⟩ := hcont _ hy'
          refine ⟨leWe g₁ * u + r', KlWT.term hg₁ huc hu0 huθ hr'W (hr'lt.trans hrlt), hr'1.trans le_add_self,
            (add_lt_add_iff_left _).2 hr'lt, ?_⟩
          rw [Vh.vhT_cnfW hl hX hg₁D (klD hl hX hr'W) huH hu2]
          have e1 : y = leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u +
              (y - leOe (vbT S l g₁) * gxTh (upsilon l) (ldAtR S l) u) := (Ordinal.add_sub_cancel_of_le hyp).symm
          rw [e1]
          exact (add_lt_add_iff_left _).2 hyr'
      · right
        obtain ⟨qp, hpx⟩ := klEx hl hX hpWT
        refine ⟨fun v => leWe g₁ * u + C v, fun x => vbT S l (leWe g₁ * u) + R x,
          KaT.addC (Om 1 * vbT S l (leWe g₁ * u)) t, max qp q, KaT.addC (Om (1 + 1) * (leWe g₁ * u)) t₂,
          keCtx_prefix hl hX hpx hC, kkTw_prefix htw, by simp only [hCΩ], fun v hv hvθ => ?_⟩
        obtain ⟨hCW, hClt⟩ := hCv v hv hvθ
        exact ⟨KlWT.term hg₁ huc hu0 huθ hCW (hClt.trans hrlt), (add_lt_add_iff_left _).2 hClt⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kn

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kn.knClass
