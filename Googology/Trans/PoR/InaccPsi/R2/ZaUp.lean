import Googology.Trans.PoR.InaccPsi.R2.ZaLv

/-!
# The level calculus below `θ` for the maps of FRAG: base change, inverse base change, congruence

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `π⁻¹ = up σ τ`, `θ = ConjT.th S`, `B₂ = Uc.ucB`, `Γ₀ = gamma 0`, `yvSub` the leaf substitution of
`R2.YvSub`.  For the FRAG step at moving levels `B₂ ≤ q`, `Ω₁·q < θ`, this module collects what the base change and
the inverse base change do to a level:

* `za_lv_congr`, `za_sub_congr` (**the leaf predicate and the substitution depend only on the leaves**);
* `za_up_lt_Om2`, `za_up_lt_th` (`π⁻¹` keeps `< Ω₂`, and then the value is `< θ`, `R2.uzTBound`);
* `za_lv_up` (**`YvLv P (π⁻¹ G) ⇔ YvLv (P ∘ π⁻¹) G`**), `za_sub_up` (**`yvSub π⁻¹ G = π⁻¹ G` and `yvSub f (π⁻¹ G) =
  yvSub (f ∘ π⁻¹) G`**);
* `za_up_dvd`, `za_up_level` (**the inverse image of a level `Ω₁·q ≥ B₂` is a level `Ω₁·q' ≥ B₂`**), `za_pi_level`
  (the same for `π`);
* `za_node_up` (**`π⁻¹(ϑ^σ(Ω₁·q + ρ)) = ϑᵗ(π⁻¹(Ω₁·q) + π⁻¹ ρ)`** for `Ω₁·q + ρ ∈ T^σ`, with the parts in `T^σ`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The leaf predicate depends only on the leaves.** -/
theorem za_lv_congr {P P' Q : Ordinal.{0} → Prop} {z : Ordinal.{0}} (hQ : YvLv S Q z)
    (h : ∀ x, Q x → (P x ↔ P' x)) : YvLv S P z ↔ YvLv S P' z :=
  ⟨fun hP => (yvLv_and hP hQ).mono fun x hx => (h x hx.2).1 hx.1,
    fun hP => (yvLv_and hP hQ).mono fun x hx => (h x hx.2).2 hx.1⟩

/-- **The substitution depends only on the leaves.** -/
theorem za_sub_congr {f g : Ordinal.{0} → Ordinal.{0}} {Q : Ordinal.{0} → Prop} {z : Ordinal.{0}}
    (hQ : YvLv S Q z) (h : ∀ x, Q x → f x = g x) : yvSub S f z = yvSub S g z := by
  obtain ⟨w, hw⟩ := yvR_ex (S := S) f hQ
  rw [yvSub_eq hw, yvSub_eq (yvR_congr (hQ.mono h) hw)]

theorem za_Om2_fix {σ τ : Ordinal.{0}} (h : Bases σ τ) : OmTwo ∈ TB τ σ ∧ pi σ τ OmTwo = OmTwo := by
  rw [← Ui.ui_one_W]
  exact yv_Om_fix h le_self_add (Ui.ui_s1_lt_omega (s := 1) one_lt_omega0)

/-- `π⁻¹` keeps `< Ω₂`. -/
theorem za_up_lt_Om2 {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hG : G ∈ Tset σ) (h2 : G < OmTwo) :
    up σ τ G < OmTwo := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  obtain ⟨o1, o2⟩ := za_Om2_fix h
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with hlt | heq
  · have := (pi_bijOn h).2 o1 u1 hlt
    rw [o2, u2] at this
    exact absurd this (not_lt.2 h2.le)
  · rw [← heq, o2] at u2
    exact absurd u2 h2.ne'

/-- `π⁻¹ G < θ` for `G ∈ T^σ ∩ Ω₂`. -/
theorem za_up_lt_th (S : InaccSeq.{0}) {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hG : G ∈ Tset σ)
    (h2 : G < OmTwo) : up σ τ G < ConjT.th S :=
  uzTBound (S := S) τ h.2.1 h.2.2.2 _ (up_spec h hG).1.1 (za_up_lt_Om2 h hG h2)

/-- **The leaves of `π⁻¹ G` are the `π⁻¹`-images of the leaves of `G`.** -/
theorem za_lv_up {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hG : G ∈ Tset σ) (h2 : G < OmTwo)
    (P : Ordinal.{0} → Prop) : YvLv S P (up σ τ G) ↔ YvLv S (fun x => P (up σ τ x)) G := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  have hz := za_up_lt_th S h hG h2
  have hL := (yv_TB_iff h hz).1 u1
  have e := za_lv_pi_th (S := S) h hσ hz u1 (fun x => P (up σ τ x))
  rw [u2] at e
  rw [e]
  exact (za_lv_congr hL fun x hx => by simp only [up_pi h hx]).symm

/-- **`yvSub π⁻¹ G = π⁻¹ G`, and substitutions compose after `π⁻¹`.** -/
theorem za_sub_up {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hG : G ∈ Tset σ) (h2 : G < OmTwo) :
    yvSub S (up σ τ) G = up σ τ G ∧
      ∀ f : Ordinal.{0} → Ordinal.{0}, yvSub S f (up σ τ G) = yvSub S (fun x => f (up σ τ x)) G := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  have hz := za_up_lt_th S h hG h2
  have hL := (yv_TB_iff h hz).1 u1
  refine ⟨(yv_up h hσ hG hz).1.symm, fun f => ?_⟩
  have e := yv_comp_sub (S := S) h hσ (fun x => f (up σ τ x)) hz hL (yvR_ex _ hL)
  rw [u2] at e
  rw [e]
  exact (za_sub_congr hL fun x hx => by simp only [Function.comp, up_pi h hx]).symm

/-- `B₂ ≤ x ⇒ B₂ ≤ π⁻¹ x` (`Γ₀ ≤ σ`). -/
theorem za_up_B_le (S : InaccSeq.{0}) {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hx : x ∈ Tset σ) (hB : ucB ≤ x) :
    ucB ≤ up σ τ x := by
  obtain ⟨u1, u2⟩ := up_spec h hx
  obtain ⟨b1, b2⟩ := yv_B_fix S h hσ
  by_contra hc
  have := (pi_bijOn h).2 u1 b1 (not_le.1 hc)
  rw [u2, b2] at this
  exact absurd this (not_lt.2 hB)

/-- `B₂ ≤ x ⇒ B₂ ≤ π x` (`Γ₀ ≤ σ`). -/
theorem za_pi_B_le (S : InaccSeq.{0}) {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hx : x ∈ TB τ σ) (hB : ucB ≤ x) :
    ucB ≤ pi σ τ x := by
  obtain ⟨b1, b2⟩ := yv_B_fix S h hσ
  rcases hB.lt_or_eq with hlt | heq
  · have := (pi_bijOn h).2 b1 hx hlt; rw [b2] at this; exact this.le
  · rw [← heq, b2]

theorem za_B_le_of_mul {q : Ordinal.{0}} (h : ucB ≤ Om1 * q) : ucB ≤ q := by
  by_contra hc
  exact absurd (Xe.xe_mul_lt_B (not_le.1 hc)) (not_lt.2 h)

/-- **`π⁻¹ x = Ω₁·k + r` splits**: for `x ∈ T^σ`, `Ω₁ ≤ x < Ω₂`, the parts `π⁻¹`-preimages are the parts of
`π⁻¹ x` (`up (Ω₁·(x/Ω₁)) = Ω₁·(H/Ω₁)`, `up (x mod Ω₁) = H mod Ω₁` with `H = π⁻¹ x`), all in `Tᵗ[σ]`. -/
theorem za_up_split (S : InaccSeq.{0}) {σ τ x : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hx : x ∈ Tset σ)
    (hx1 : Om1 ≤ x) (h2 : x < OmTwo) :
    let H := up σ τ x
    Om1 * (H / Om1) ∈ TB τ σ ∧ H % Om1 ∈ TB τ σ ∧
      pi σ τ (Om1 * (H / Om1)) = Om1 * (x / Om1) ∧ pi σ τ (H % Om1) = x % Om1 := by
  intro H
  obtain ⟨u1, u2⟩ := up_spec h hx
  have hHθ := za_up_lt_th S h hx h2
  obtain ⟨o1, o2⟩ := pi_Om1 h
  have hHO : Om1 ≤ H := by
    by_contra hc
    have := (pi_bijOn h).2 u1 o1 (not_le.1 hc)
    rw [u2, o2] at this
    exact absurd this (not_lt.2 hx1)
  have hτH : τ ≤ H := (h.2.2.2.le).trans hHO
  set a := Om1 * (H / Om1) with ha
  set r := H % Om1 with hr
  have hr1 : r < Om1 := Ordinal.mod_lt H Rj.rj_Om1_pos.ne'
  have hdec : a + r = H := Ordinal.div_add_mod H Om1
  have hOm : (ω : Ordinal.{0}) ^ (Om1 : Ordinal.{0}) = Om1 := Rj.rj_Om1_opow
  have hda : ω ^ (Om1 : Ordinal.{0}) ∣ a := by rw [hOm]; exact dvd_mul_right _ _
  have hrw : r < ω ^ (Om1 : Ordinal.{0}) := by rw [hOm]; exact hr1
  have haT : a ∈ TB τ σ := Si.siTB_of_comps h u1 hτH (fun p hp => by
    have := Vi.vi_comps_head a hda r hrw p hp; rwa [hdec] at this)
  have hrT : r ∈ TB τ σ := Si.siTB_of_comps h u1 hτH (fun p hp => by
    have := Rj.rj_comps_add a hda r hrw p hp; rwa [hdec] at this)
  obtain ⟨-, c2⟩ := pi_add h haT hrT
  have haθ : a < ConjT.th S := (le_self_add.trans_eq hdec).trans_lt hHθ
  obtain ⟨c, hc⟩ := yv_pi_dvd (S := S) h a haθ haT (dvd_mul_right _ _)
  have hπr : pi σ τ r < Om1 := down_lt_Om1 h hrT hr1
  rw [hdec, u2, hc] at c2
  have hdiv : x / Om1 = c := by
    rw [c2, Ordinal.mul_add_div _ Rj.rj_Om1_pos.ne', Ordinal.div_eq_zero_of_lt hπr, add_zero]
  have hmod : x % Om1 = pi σ τ r := by
    rw [c2, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hπr]
  exact ⟨haT, hrT, by rw [hc, hdiv], hmod.symm⟩

/-- **The inverse image of a level is a level**: `Ω₁·q ∈ T^σ`, `1 ≤ q`, `Ω₁·q < Ω₂` ⇒ `π⁻¹(Ω₁·q) = Ω₁·q'`, `1 ≤ q'`,
`Ω₁·q' < θ`, in `Tᵗ[σ]` (and `B₂ ≤ q ⇒ B₂ ≤ q'`). -/
theorem za_up_level {σ τ q : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hq1 : 1 ≤ q)
    (hG : Om1 * q ∈ Tset σ) (h2 : Om1 * q < OmTwo) :
    ∃ q', up σ τ (Om1 * q) = Om1 * q' ∧ 1 ≤ q' ∧ Om1 * q' < ConjT.th S ∧ Om1 * q' ∈ TB τ σ ∧
      pi σ τ (Om1 * q') = Om1 * q ∧ (ucB ≤ q → ucB ≤ q') := by
  have hx1 : Om1 ≤ Om1 * q := le_mul_left Om1 (one_le_iff_pos.1 hq1)
  obtain ⟨a1, r1, a2, r2⟩ := za_up_split S h hσ hG hx1 h2
  obtain ⟨u1, u2⟩ := up_spec h hG
  set H := up σ τ (Om1 * q) with hH
  have hmod0 : (Om1 * q) % Om1 = 0 := Ordinal.dvd_iff_mod_eq_zero.1 (dvd_mul_right _ _)
  have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
  have hr0 : H % Om1 = 0 := (pi_bijOn h).1.injOn r1 (mem_TB_of_lt h h0σ) (by rw [r2, hmod0, pi_lt h h0σ])
  have hHe : H = Om1 * (H / Om1) := by
    conv_lhs => rw [← Ordinal.div_add_mod H Om1, hr0, add_zero]
  have hHθ := za_up_lt_th S h hG h2
  refine ⟨H / Om1, hHe, ?_, hHe ▸ hHθ, hHe ▸ u1, by rw [← hHe]; exact u2, fun hB => ?_⟩
  · refine one_le_iff_ne_zero.2 fun e => ?_
    rw [e, mul_zero] at hHe
    rw [hHe, pi_lt h h0σ] at u2
    exact absurd u2.symm (lt_of_lt_of_le Rj.rj_Om1_pos hx1).ne'
  · have := za_up_B_le S h hσ hG (hB.trans (Xe.xe_le_mul q))
    change ucB ≤ H at this
    rw [hHe] at this
    exact za_B_le_of_mul this

/-- **The image of a level `≥ B₂` is a level `≥ B₂`** (`π`). -/
theorem za_pi_level {σ τ q : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hq1 : 1 ≤ q)
    (hθ : Om1 * q < ConjT.th S) (hT : Om1 * q ∈ TB τ σ) :
    ∃ q', pi σ τ (Om1 * q) = Om1 * q' ∧ 1 ≤ q' ∧ Om1 * q' < ConjT.th S ∧
      pi σ τ (Om1 * q) = yvSub S (pi σ τ) (Om1 * q) ∧ (ucB ≤ q → ucB ≤ q') := by
  obtain ⟨q', e, h1, hθ', hs⟩ := yv_level_img h hq1 hθ hT
  refine ⟨q', e, h1, hθ', hs, fun hB => ?_⟩
  have := za_pi_B_le S h hσ hT (hB.trans (Xe.xe_le_mul q))
  rw [e] at this
  exact za_B_le_of_mul this

/-- **`π⁻¹` at a `ϑ`-node with a moving level**: for `Ω₁·q + ρ ∈ T^σ` (`1 ≤ q`, `Ω₁·q < Ω₂`, `ρ < Ω₁`): the parts
`Ω₁·q`, `ρ` lie in `T^σ`, `π⁻¹(Ω₁·q + ρ) = π⁻¹(Ω₁·q) + π⁻¹ ρ` in `Tᵗ[σ]`, and `π⁻¹(ϑ^σ(Ω₁·q + ρ)) = ϑᵗ(π⁻¹(Ω₁·q) +
π⁻¹ ρ)`, a node in `Tᵗ[σ]`. -/
theorem za_node_up (S : InaccSeq.{0}) {σ τ q ρ : Ordinal.{0}} (h : Bases σ τ) (hσ : gamma 0 ≤ σ) (hq1 : 1 ≤ q)
    (hq2 : Om1 * q < OmTwo) (hx : Om1 * q + ρ ∈ Tset σ) (hρ1 : ρ < Om1) :
    Om1 * q ∈ Tset σ ∧ ρ ∈ Tset σ ∧ up σ τ (Om1 * q) + up σ τ ρ ∈ TB τ σ ∧
      up σ τ (Om1 * q + ρ) = up σ τ (Om1 * q) + up σ τ ρ ∧
      up σ τ (vt σ (Om1 * q + ρ)) = vt τ (up σ τ (Om1 * q) + up σ τ ρ) ∧
      vt τ (up σ τ (Om1 * q) + up σ τ ρ) ∈ TB τ σ := by
  have hO2 : (Om1 : Ordinal.{0}) < OmTwo := tqc_Om1_lt_OmTwo
  have hΓ1 : Om1 ≤ Om1 * q := le_mul_left Om1 (one_le_iff_pos.1 hq1)
  have hx1 : Om1 ≤ Om1 * q + ρ := hΓ1.trans le_self_add
  have hx2 : Om1 * q + ρ < OmTwo := (Lq.lq_SC_indec uc_SC_Om2).add_lt hq2 (hρ1.trans hO2)
  obtain ⟨a1, r1, a2, r2⟩ := za_up_split S h hσ hx hx1 hx2
  obtain ⟨u1, u2⟩ := up_spec h hx
  set H := up σ τ (Om1 * q + ρ) with hH
  have hdiv : (Om1 * q + ρ) / Om1 = q := by
    rw [Ordinal.mul_add_div _ Rj.rj_Om1_pos.ne', Ordinal.div_eq_zero_of_lt hρ1, add_zero]
  have hmod : (Om1 * q + ρ) % Om1 = ρ := by rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hρ1]
  rw [hdiv] at a2
  rw [hmod] at r2
  have hGT : Om1 * q ∈ Tset σ := by rw [← a2]; exact (pi_bijOn h).1.mapsTo a1
  have hρT : ρ ∈ Tset σ := by rw [← r2]; exact (pi_bijOn h).1.mapsTo r1
  have e1 : up σ τ (Om1 * q) = Om1 * (H / Om1) := by rw [← a2, up_pi h a1]
  have e2 : up σ τ ρ = H % Om1 := by rw [← r2, up_pi h r1]
  have hdec : up σ τ (Om1 * q) + up σ τ ρ = H := by rw [e1, e2]; exact Ordinal.div_add_mod H Om1
  have hH2 : H < OmTwo := za_up_lt_Om2 h hx hx2
  have hv := vt_memTwo h.2.1 h.2.2.2 u1.1 hH2
  have hvT : vt τ H ∈ TB τ σ := ⟨hv.1, by rw [hv.2.2.2.2]; exact u1.2⟩
  have hπv : pi σ τ (vt τ H) = vt σ (Om1 * q + ρ) := by rw [pi_vt_two h u1 hH2, u2]
  refine ⟨hGT, hρT, by rw [hdec]; exact u1, hdec.symm, ?_, by rw [hdec]; exact hvT⟩
  rw [hdec, ← hπv, up_pi h hvT]

end Googology.Trans.PoR.InaccPsi.R2.Za
