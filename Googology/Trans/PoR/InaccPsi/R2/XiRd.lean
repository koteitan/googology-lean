import Googology.Trans.PoR.InaccPsi.R2.CitedXi
import Googology.Trans.PoR.InaccPsi.R2.LvETm

/-!
# XiRd: THE READING OF EVERY CODE BELOW `θ` AT EVERY BASE, ITS BASE CHANGE, AND THE COLLAPSE

For a countable `ε`-number `x`, `R_x := π_{x,ε_{x+1}} ∘ ι_{x,ε_{x+1}}` (`R2.wIo`, `R2.pi`).  On the codes `WDom S x`
(`c < x`, or `Ω₁ ≤ c < θ` with `P₀(c) ⊆ x`) it is strictly increasing, the identity below `x`, `R_x(Ω₁) = x`, maps
onto `Tˣ ∩ Ω₁`, and is therefore the order type function of `WDom S x`.  Then the base change and the collapse need no
induction on the codes:

* `wDom_mono`, `xiR`, `xi_bases`, `xi_io_TB`, `xiR_T`, `xiR_lt`, `xiR_small`, `xiR_Om1`, `xiR_onto`, `xiR_TB`
  (**`R_x(c) ∈ Tˣ[σ] ⇔ c ∈ WDom S σ`**), `xiR_add`;
* `xi_otp_of_iso` (**a strictly increasing map of a set of ordinals onto initial segments is its order type
  function**), `xiR_otp`;
* `xiR_pi` (**LEMMA EXACT FOR EVERY CODE BELOW `θ`**: `π_{σ,x}(R_x(c)) = R_σ(c)` for `c ∈ WDom S σ`, `σ < x`);
* `xi_dom_codes` (**the codes of `qtU` over a strongly critical `y` below `θ` are `WDom S y`**), `xiR_gx` (**`gxTh y
  (qtAt S y) c = R_y(c)`**).

No new axiom.  New definition: `xiR`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

theorem wDom_mono {α α' c : Ordinal.{0}} (h : α ≤ α') (hc : WDom S α c) : WDom S α' c := by
  rcases hc with hc | ⟨h1, h2, h3⟩
  · exact Or.inl (hc.trans_le h)
  · exact Or.inr ⟨h1, h2, fun p hp => (h3 p hp).trans_le h⟩

/-- **The reading** `R_x(c) = π_{x,ε_{x+1}}(ι_{x,ε_{x+1}}(c))`. -/
noncomputable def xiR (x c : Ordinal.{0}) : Ordinal.{0} := pi x (eN x) (wIo x (eN x) c)

/-- **A strictly increasing map of a set of ordinals onto initial segments is its order type function.** -/
theorem xi_otp_of_iso {C : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hmono : ∀ c d, c ∈ C → d ∈ C → c < d → f c < f d)
    (honto : ∀ c ∈ C, ∀ v < f c, ∃ d ∈ C, d < c ∧ f d = v) : ∀ c ∈ C, f c = Cd.cdOtp C c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  apply le_antisymm
  · refine le_of_forall_lt fun v hv => ?_
    obtain ⟨d, hd, hdc, rfl⟩ := honto c hc v hv
    rw [IH d hdc hd]; exact Cd.cdOtp_lt_of_mem hd hdc
  · refine le_of_forall_lt fun u hu => ?_
    obtain ⟨d, hd, hdc, rfl⟩ := Gg.ggOtp_onto C c u hu
    rw [← IH d hdc hd]; exact hmono d c hd hc hdc

section Base

variable (S) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include S hx hx1

omit S in
theorem xi_bases : Bases x (eN x) := ⟨hx, eN_E x, lt_eN x, (lve_eN_T hx hx1).2⟩

/-- `ι_{x,ε_{x+1}}(c) ∈ T^{ε_{x+1}}[x]` for `c ∈ WDom S x`. -/
theorem xi_io_TB : ∀ c, WDom S x c → wIo x (eN x) c ∈ TB (eN x) x := by
  obtain ⟨hid, -, -, -, hT, -, hPar⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  intro c hc
  refine ⟨(hT c (wDom_mono (lt_eN x).le hc)).1, ?_⟩
  rcases hc with hc | ⟨h1, h2, h3⟩
  · rw [hid c (hc.trans (lt_eN x)), Par_lt (eN_E x) (lve_eN_T hx hx1).2 (hc.trans (lt_eN x))]
    intro p hp
    rw [Finset.coe_singleton, mem_singleton_iff] at hp
    rw [hp]; exact hc
  · exact (hPar c (wDom_mono (lt_eN x).le (Or.inr ⟨h1, h2, h3⟩)) h1 x hx (lt_eN x).le).2 h3

theorem xiR_T : ∀ c, WDom S x c → xiR x c ∈ Tset x ∧ xiR x c < Om1 := by
  obtain ⟨-, -, -, -, hT, -, -⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  intro c hc
  have hB := xi_bases hx hx1
  have hm := xi_io_TB S hx hx1 c hc
  have h1 : wIo x (eN x) c < Om1 := (hT c (wDom_mono (lt_eN x).le hc)).2
  refine ⟨(pi_bijOn hB).1.mapsTo hm, ?_⟩
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  unfold xiR
  rw [← hpO]; exact (pi_bijOn hB).2 hm hOT h1

theorem xiR_lt : ∀ c d, WDom S x c → WDom S x d → c < d → xiR x c < xiR x d := by
  obtain ⟨-, -, hlt, -, -, -, -⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  intro c d hc hd hcd
  exact (pi_bijOn (xi_bases hx hx1)).2 (xi_io_TB S hx hx1 c hc) (xi_io_TB S hx hx1 d hd)
    (hlt c d (wDom_mono (lt_eN x).le hc) (wDom_mono (lt_eN x).le hd) hcd)

theorem xiR_small : ∀ c, c < x → xiR x c = c := by
  obtain ⟨hid, -, -, -, -, -, -⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  intro c hc
  unfold xiR
  rw [hid c (hc.trans (lt_eN x)), pi_lt (xi_bases hx hx1) hc]

theorem xiR_Om1 : xiR x Om1 = x := by
  obtain ⟨-, hO, -, -, -, -, -⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  unfold xiR
  rw [hO, (pi_base (xi_bases hx hx1)).2]

theorem xiR_onto : ∀ v, v ∈ Tset x → v < Om1 → ∃ c, WDom S x c ∧ xiR x c = v := by
  obtain ⟨hid, -, -, -, -, hon, hPar⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  have hB := xi_bases hx hx1
  intro v hv hv1
  obtain ⟨w, hw, rfl⟩ := (pi_bijOn hB).1.surjOn hv
  have hw1 : w < Om1 := by
    by_contra h
    push Not at h
    obtain ⟨hOT, hpO⟩ := pi_Om1 hB
    have := ((pi_bijOn hB).2.le_iff_le hOT hw).2 h
    rw [hpO] at this
    exact absurd hv1 (not_lt.2 this)
  obtain ⟨c, hc, rfl⟩ := hon w hw.1 hw1
  refine ⟨c, ?_, rfl⟩
  rcases hc with hc | ⟨h1, h2, h3⟩
  · left
    have hP := hw.2
    rw [hid c hc, Par_lt (eN_E x) (lve_eN_T hx hx1).2 hc] at hP
    exact hP (by simp)
  · exact Or.inr ⟨h1, h2, (hPar c (Or.inr ⟨h1, h2, h3⟩) h1 x hx (lt_eN x).le).1 hw.2⟩

/-- **`R_x(c) ∈ Tˣ[σ] ⇔ c ∈ WDom S σ`** for `c ∈ WDom S x` and an `ε`-number `σ ≤ x`. -/
theorem xiR_TB : ∀ c, WDom S x c → ∀ σ, InE σ → σ ≤ x → (xiR x c ∈ TB x σ ↔ WDom S σ c) := by
  obtain ⟨-, -, -, -, -, -, hPar⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  have hB := xi_bases hx hx1
  intro c hc σ hσ hσx
  have hT := (xiR_T S hx hx1 c hc).1
  rcases hc with hc | ⟨h1, h2, h3⟩
  · rw [xiR_small S hx hx1 c hc]
    rw [xiR_small S hx hx1 c hc] at hT
    constructor
    · intro h
      have hP := h.2
      rw [Par_lt hx hx1 hc] at hP
      exact Or.inl (hP (by simp))
    · rintro (h | ⟨h1, -, -⟩)
      · refine ⟨hT, ?_⟩
        rw [Par_lt hx hx1 hc]
        intro p hp
        rw [Finset.coe_singleton, mem_singleton_iff] at hp
        rw [hp]; exact h
      · exact absurd (hc.trans hx1) (not_lt.2 h1)
  · have hm := xi_io_TB S hx hx1 c (Or.inr ⟨h1, h2, h3⟩)
    have hPeq : Par x (xiR x c) = Par (eN x) (wIo x (eN x) c) := (pi_ht_Par hB hm).2
    have e := hPar c (wDom_mono (lt_eN x).le (Or.inr ⟨h1, h2, h3⟩)) h1 σ hσ (hσx.trans (lt_eN x).le)
    constructor
    · intro h
      exact Or.inr ⟨h1, h2, e.1 (by rw [← hPeq]; exact h.2)⟩
    · rintro (h | ⟨-, -, h'⟩)
      · exact absurd (h.trans (hσx.trans_lt hx1)) (not_lt.2 h1)
      · exact ⟨hT, by rw [hPeq]; exact e.2 h'⟩

theorem xiR_add : ∀ c d, WDom S x c → WDom S x d → WDom S x (c + d) →
    xiR x (c + d) = xiR x c + xiR x d := by
  obtain ⟨-, -, -, hadd, -, -, -⟩ :=
    wIo_spec S hx hx1 (eN_E x) (lve_eN_T hx hx1).1 (lt_eN x) (lve_eN_T hx hx1).2
  intro c d hc hd hcd
  unfold xiR
  rw [hadd c d (wDom_mono (lt_eN x).le hc) (wDom_mono (lt_eN x).le hd) (wDom_mono (lt_eN x).le hcd)]
  exact (pi_add (xi_bases hx hx1) (xi_io_TB S hx hx1 c hc) (xi_io_TB S hx hx1 d hd)).2

/-- **`R_x` is the order type function of `WDom S x`.** -/
theorem xiR_otp : ∀ c, WDom S x c → xiR x c = Cd.cdOtp {d | WDom S x d} c := by
  refine xi_otp_of_iso (fun c d hc hd hcd => xiR_lt S hx hx1 c d hc hd hcd) fun c hc v hv => ?_
  obtain ⟨hT, h1⟩ := xiR_T S hx hx1 c hc
  have hvT : v ∈ Tset x := vz_T_down hx hx1 hT h1 hv.le
  obtain ⟨d, hd, rfl⟩ := xiR_onto S hx hx1 v hvT (hv.trans h1)
  refine ⟨d, hd, ?_, rfl⟩
  by_contra hdc
  push Not at hdc
  rcases hdc.lt_or_eq with hlt | heq
  · exact absurd (xiR_lt S hx hx1 c d hc hd hlt) (not_lt.2 hv.le)
  · rw [heq] at hv; exact lt_irrefl _ hv

end Base

/-- **LEMMA EXACT FOR EVERY CODE BELOW `θ`**: for `ε`-numbers `σ < x < Ω₁` and `c ∈ WDom S σ`,
`R_x(c) ∈ Tˣ[σ]` and `π_{σ,x}(R_x(c)) = R_σ(c)`. -/
theorem xiR_pi {σ x : Ordinal.{0}} (hσ : InE σ) (hx : InE x) (hσx : σ < x) (hx1 : x < Om1) :
    ∀ c, WDom S σ c → xiR x c ∈ TB x σ ∧ pi σ x (xiR x c) = xiR σ c := by
  have hσ1 : σ < Om1 := hσx.trans hx1
  have hB : Bases σ x := ⟨hσ, hx, hσx, hx1⟩
  have hTB : ∀ c, WDom S σ c → xiR x c ∈ TB x σ := fun c hc =>
    (xiR_TB S hx hx1 c (wDom_mono hσx.le hc) σ hσ hσx.le).2 hc
  have hf : ∀ c, c ∈ {d | WDom S σ d} → pi σ x (xiR x c) = Cd.cdOtp {d | WDom S σ d} c := by
    refine xi_otp_of_iso (fun c d hc hd hcd => (pi_bijOn hB).2 (hTB c hc) (hTB d hd)
      (xiR_lt S hx hx1 c d (wDom_mono hσx.le hc) (wDom_mono hσx.le hd) hcd)) fun c hc v hv => ?_
    have hpT : pi σ x (xiR x c) ∈ Tset σ := (pi_bijOn hB).1.mapsTo (hTB c hc)
    have hp1 : pi σ x (xiR x c) < Om1 := by
      obtain ⟨hOT, hpO⟩ := pi_Om1 hB
      rw [← hpO]; exact (pi_bijOn hB).2 (hTB c hc) hOT (xiR_T S hx hx1 c (wDom_mono hσx.le hc)).2
    have hvT : v ∈ Tset σ := vz_T_down hσ hσ1 hpT hp1 hv.le
    obtain ⟨w, hw, rfl⟩ := (pi_bijOn hB).1.surjOn hvT
    have hw1 : w < Om1 := by
      by_contra h
      push Not at h
      obtain ⟨hOT, hpO⟩ := pi_Om1 hB
      have := ((pi_bijOn hB).2.le_iff_le hOT hw).2 h
      rw [hpO] at this
      exact absurd (hv.trans hp1) (not_lt.2 this)
    obtain ⟨d, hd, rfl⟩ := xiR_onto S hx hx1 w hw.1 hw1
    have hdσ : WDom S σ d := (xiR_TB S hx hx1 d hd σ hσ hσx.le).1 hw
    refine ⟨d, hdσ, ?_, rfl⟩
    by_contra hdc
    push Not at hdc
    have hle : pi σ x (xiR x c) ≤ pi σ x (xiR x d) :=
      ((pi_bijOn hB).2.le_iff_le (hTB c hc) (hTB d hdσ)).2
        (by
          rcases hdc.lt_or_eq with hlt | heq
          · exact (xiR_lt S hx hx1 c d (wDom_mono hσx.le hc) hd hlt).le
          · rw [heq])
    exact absurd hv (not_lt.2 hle)
  intro c hc
  exact ⟨hTB c hc, by rw [hf c hc, ← xiR_otp S hσ hσ1 c hc]⟩

/-- **The codes of `qtU` over a strongly critical `y < Ω₁` below `θ` are `WDom S y`.** -/
theorem xi_dom_codes {y c : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (hc : c < ConjT.th S) :
    GxCl y (Qt.qtAt S y) c ↔ WDom S y c := by
  have hyE : InE y := Low.opow_eq_self_of_SC hy
  obtain ⟨hsm, -, hV0⟩ := wP_spec S
  rw [Qt.qt_codes hy (by rw [← Rj.rj_Om1]; exact hy1.le) hc]
  have hL : Om (0 : Ordinal.{0}) < y := by rw [Om_zero]; exact hy.1
  rcases lt_or_ge c Om1 with h1 | h1
  · constructor
    · intro hK
      exact Or.inl (Ul.ulK_lt_W omega0_pos hy hL hK (by rw [zero_add, ← Rj.rj_Om1]; exact h1))
    · rintro (h | ⟨h, -, -⟩)
      · exact Ul.UlK.small h
      · exact absurd h1 (not_lt.2 h)
  · constructor
    · intro hK
      exact Or.inr ⟨h1, hc, (hV0 c y h1 hc hy hy1.le).2 hK⟩
    · rintro (h | ⟨-, -, h⟩)
      · exact absurd (h.trans hy1) (not_lt.2 h1)
      · exact (hV0 c y h1 hc hy hy1.le).1 h

/-- **THE COLLAPSE IS THE READING**: `gxTh y (qtAt S y) c = R_y(c)` for a strongly critical `y < Ω₁` and
`c ∈ WDom S y`. -/
theorem xiR_gx {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) :
    ∀ c, WDom S y c → gxTh y (Qt.qtAt S y) c = xiR y c := by
  have hyE : InE y := Low.opow_eq_self_of_SC hy
  have hyθ : y < ConjT.th S := hy1.trans (by rw [Rj.rj_Om1]; exact Vd.vd_Om1_lt_B.trans Vd.vd_B_lt_th)
  intro c hc
  have hcθ : c < ConjT.th S := by
    rcases hc with h | ⟨-, h, -⟩
    · exact h.trans hyθ
    · exact h
  rw [xiR_otp S hyE hy1 c hc]
  unfold gxTh gxSet
  exact Gg.ggOtp_congr c fun d hd => xi_dom_codes hy hy1 (hd.trans hcθ)

end Googology.Trans.PoR.InaccPsi.R2.Xi
