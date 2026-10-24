import Googology.Trans.PoR.InaccPsi.R2.TlDat
import Googology.Trans.PoR.InaccPsi.R2.TfCl

/-!
# Codes below `X` with the atoms `F_β(y)`: the closure and the data `Tl.tlDat`

`Ω₁ = Om1`, `F_β = Rh.rhF β` (`F₀ = Γ`), `X = Tl.tlX` (the least fixed point of `β ↦ F_β(0)` above `Ω₁`).  `TlCl Z` is
the set of codes over `Z`: generated from the ordinals below `Z` and `Ω₁` by `+`, `φ` and the atoms `F_β(y)` (`β, y`
codes, `F_β(y) > Ω₁`).  It extends `Tf.TfCl` (the atoms `Γ_ν = F₀(ν)`) to every atom below `X`.

* `TlCl`, `TlCl.zero`, `TlCl.one`, `TlCl.opow`, `TlCl.mul_nat`, `TlCl.mono`, `tlCl_of_tf` (`Tf.TfCl Z ⊆ TlCl Z`),
  `TlCl.lt_of_lt_Om1` (countable codes over a strongly critical `Z` are `< Z`);
* `tlDec` (**decomposition**: `w − x` and `log_ω w` are codes for codes `x ≤ w`);
* `tl_code` (**`z < X` with `tlDat z < a` is a code over `a`**), `tl_cl_inv` (inverse Veblen functions of a code),
  `tl_cl_atom` (**the level and the index of an atom code are codes**), `tl_cl_dat`, `tl_cl_iff` (**for a strongly
  critical `q` and `z < X`: `TlCl q z ↔ tlDat z < q`**; it extends `Tf.tf_cl_iff` from `B_Γ` to `X`),
  `tl_cl_opow_mul`, `tl_cl_Om1_mul`, `tl_cl_Om1_add`, `tl_cl_div` (`y ↦ y / Ω₁`), `tl_code_lvl`.

No new axiom.  New definition: `TlCl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rh

/-- **The codes over `Z` with the atoms `F_β(y)`** (`β, y` codes, `F_β(y) > Ω₁`): generated from the ordinals below
`Z` and `Ω₁` by `+`, `φ` and the atoms. -/
inductive TlCl (Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → TlCl Z x
  | om : TlCl Z Om1
  | add {x y : Ordinal.{0}} : TlCl Z x → TlCl Z y → TlCl Z (x + y)
  | phi {x y : Ordinal.{0}} : TlCl Z x → TlCl Z y → TlCl Z (veblen x y)
  | atom {β y : Ordinal.{0}} : TlCl Z β → TlCl Z y → Om1 < rhF β y → TlCl Z (rhF β y)

variable {Z : Ordinal.{0}}

theorem TlCl.mono {Z' : Ordinal.{0}} (h : Z ≤ Z') {x : Ordinal.{0}} (hx : TlCl Z x) : TlCl Z' x := by
  induction hx with
  | small h' => exact TlCl.small (lt_of_lt_of_le h' h)
  | om => exact TlCl.om
  | add _ _ ihx ihy => exact TlCl.add ihx ihy
  | phi _ _ ihx ihy => exact TlCl.phi ihx ihy
  | atom _ _ h1 ihβ ihy => exact TlCl.atom ihβ ihy h1

theorem TlCl.zero (hZ : 0 < Z) : TlCl Z 0 := TlCl.small hZ

theorem TlCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : TlCl Z c) : TlCl Z (ω ^ c) := by
  have := TlCl.phi (TlCl.zero hZ) h; rwa [veblen_zero_apply] at this

theorem TlCl.one (hZ : 0 < Z) : TlCl Z 1 := by
  have := TlCl.opow hZ (TlCl.zero hZ); rwa [opow_zero] at this

theorem TlCl.mul_nat (hZ : 0 < Z) {x : Ordinal.{0}} (h : TlCl Z x) : ∀ n : ℕ, TlCl Z (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact TlCl.zero hZ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact TlCl.add (TlCl.mul_nat hZ h n) h

/-- An atom `Γ_ν`, `ν > Ω₁` a code, is a code. -/
theorem TlCl.gam (hZ : 0 < Z) {ν : Ordinal.{0}} (h : TlCl Z ν) (h1 : Om1 < ν) : TlCl Z (gamma ν) := by
  have := TlCl.atom (TlCl.zero hZ) h (by rw [rhF_zero]; exact tf_Om1_lt_gamma.2 h1)
  rwa [rhF_zero] at this

/-- **`Tf.TfCl Z ⊆ TlCl Z`** (the atoms `Γ_ν = F₀(ν)`). -/
theorem tlCl_of_tf (hZ : 0 < Z) {x : Ordinal.{0}} (hx : TfCl Z x) : TlCl Z x := by
  induction hx with
  | small h => exact TlCl.small h
  | om => exact TlCl.om
  | add _ _ ihx ihy => exact TlCl.add ihx ihy
  | phi _ _ ihx ihy => exact TlCl.phi ihx ihy
  | gam _ h1 ih => exact TlCl.gam hZ ih h1

/-- A countable code over a strongly critical `Z` is below `Z`. -/
theorem TlCl.lt_of_lt_Om1 (hZ : SC Z) {x : Ordinal.{0}} (hx : TlCl Z x) : x < Om1 → x < Z := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hZ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1)) (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hZ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))
  | atom _ _ h1 _ _ => exact fun h => absurd (h1.trans h) (lt_irrefl _)

/-! ## Decomposition -/

theorem tl_SC_prin {z : Ordinal.{0}} (hz : SC z) : IsPrincipal (· + ·) z := by
  rw [← Low.opow_eq_self_of_SC hz]; exact isPrincipal_add_omega0_opow _

theorem tl_log_SC {z : Ordinal.{0}} (hz : SC z) : log ω z = z := by
  conv_lhs => rw [← Low.opow_eq_self_of_SC hz]
  exact log_opow one_lt_omega0 _

/-- **Decomposition**: for a strongly critical `Z`, a code `w` over `Z` has `w − x` (for every code `x ≤ w`) and
`log_ω w` codes over `Z`. -/
theorem tlDec (hZ : SC Z) : ∀ w, TlCl Z w →
    (∀ x, TlCl Z x → x ≤ w → TlCl Z (w - x)) ∧ TlCl Z (log ω w) := by
  have h0 : TlCl Z 0 := TlCl.zero hZ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, TlCl Z v → v ≤ w →
      (∀ x, TlCl Z x → x ≤ v → TlCl Z (v - x)) ∧ TlCl Z (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => TlCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      TlCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hp : IsPrincipal (· + ·) (Om1 : Ordinal.{0}) := by
      rw [← rj_Om1_opow]; exact isPrincipal_add_omega0_opow _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hp hx with e | e <;> rw [e]
      · exact TlCl.om
      · exact h0
    · have : log ω (Om1 : Ordinal.{0}) = Om1 := by
        conv_lhs => rw [← rj_Om1_opow]
        exact log_opow one_lt_omega0 _
      rw [this]; exact TlCl.om
  | @atom β y hβ hy h1 _ _ =>
    intro _
    have hSC := rhF_SC β y
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin (tl_SC_prin hSC) hx with e | e <;> rw [e]
      · exact TlCl.atom hβ hy h1
      · exact h0
    · rw [tl_log_SC hSC]; exact TlCl.atom hβ hy h1
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact TlCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : TlCl Z (x - u) := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact h0
    · rcases ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2
  | @phi a b ha hb iha ihb =>
    intro hle
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · exact TlCl.opow hZ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact TlCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact TlCl.phi ha hb

/-! ## Codes and data -/

/-- **A code**: `z < X` with `tlDat z < a` (`0 < a`) is a code over `a`. -/
theorem tl_code {a : Ordinal.{0}} (ha : 0 < a) : ∀ z : Ordinal.{0}, z < tlX → tlDat z < a → TlCl a z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzX hd
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tlDat_small h] at hd; exact TlCl.small hd
  · exact TlCl.om
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [tlDat_phi h hzX hE hI] at hd
      have h2 := tf_inv2_lt hE
      have e : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact TlCl.phi (IH _ hI (hI.trans hzX) ((le_max_left _ _).trans_lt hd))
        (IH _ h2 (h2.trans hzX) ((le_max_right _ _).trans_lt hd))
    · obtain ⟨hnf, hyz, hlz⟩ := tl_nf (tl_SC_of h hI) h hzX
      by_cases h0 : tlLev z = 0
      · have hg := tf_SC_gamma h hI
        have h1 : Om1 < tfIdx z := by rw [← tf_Om1_lt_gamma, hg]; exact h
        have hlt := tl_atom0_lt h hzX hI h0
        rw [tlDat_atom0 h hzX hE hI h0] at hd
        have hc := IH _ hlt (hlt.trans hzX) hd
        have e : (Om1 + 1) + (tfIdx z - (Om1 + 1)) = tfIdx z :=
          Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)
        rw [← hg]
        exact TlCl.gam ha (e ▸ TlCl.add (TlCl.add TlCl.om (TlCl.one ha)) hc) h1
      · rw [tlDat_atomF h hzX hE hI h0] at hd
        have hlv := IH _ hlz (hlz.trans hzX) ((le_max_left _ _).trans_lt hd)
        have hy := IH _ hyz (hyz.trans hzX) ((le_max_right _ _).trans_lt hd)
        rw [← hnf]
        exact TlCl.atom hlv hy (by rw [hnf]; exact h)
  · rw [tlDat_cnf h hzX hE] at hd
    have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := tf_log_lt h hE
    have hm := rj_mod_lt hz0
    have he := IH _ hl (hl.trans hzX) ((le_max_left _ _).trans_lt hd)
    have hr := IH _ hm (hm.trans hzX) ((le_max_right _ _).trans_lt hd)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z := Ordinal.div_add_mod z _
    rw [← hdec, hk]
    exact TlCl.add (TlCl.mul_nat ha (TlCl.opow ha he) k) hr

/-- **The codes over a countable `Z` are closed under the inverse Veblen function** at the `ε`-numbers `z > Ω₁` that
are not strongly critical. -/
theorem tl_cl_inv (hZ : Z ≤ Om1) : ∀ z, TlCl Z z → Om1 < z → ω ^ z = z → invVeblen₁ z < z →
    TlCl Z (invVeblen₁ z) ∧ TlCl Z (invVeblen₂ z) := by
  intro z hz
  induction hz with
  | small h => exact fun h1 _ _ => absurd (h.trans_le hZ) (not_lt.2 h1.le)
  | om => exact fun h1 _ _ => absurd h1 (lt_irrefl _)
  | @atom β y _ _ _ _ _ => exact fun _ _ hI => absurd hI (tl_SC_facts (rhF_SC β y)).2
  | @add x y _ _ ihx ihy =>
    intro h1 hE hI
    have hp : IsPrincipal (· + ·) (x + y) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
    rcases tf_prin_sum hp rfl with ex | ey
    · rw [← ex] at h1 hE hI ⊢; exact ihx h1 hE hI
    · rw [← ey] at h1 hE hI ⊢; exact ihy h1 hE hI
  | @phi x y hx hy _ ihy =>
    intro h1 hE hI
    rcases eq_or_lt_of_le (right_le_veblen x y) with ey | hlt
    · rw [← ey] at h1 hE hI ⊢; exact ihy h1 hE hI
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [veblen_zero_apply] at hE hlt
      exact absurd ((opow_right_inj one_lt_omega0).1 hE).symm hlt.ne
    rw [invVeblen₁_veblen hlt, invVeblen₂_veblen hx0 hlt]
    exact ⟨hx, hy⟩

/-- **The level and the index of an atom code are codes**: `TlCl Z z` for a strongly critical `z > Ω₁` (`Z ≤ Ω₁`)
gives `TlCl Z (tlLev z)` and `TlCl Z (tlI (tlLev z) z)`. -/
theorem tl_cl_atom (hZ : Z ≤ Om1) : ∀ z, TlCl Z z → SC z → Om1 < z →
    TlCl Z (tlLev z) ∧ TlCl Z (tlI (tlLev z) z) := by
  intro z hz
  induction hz with
  | small h => exact fun _ h1 => absurd (h.trans_le hZ) (not_lt.2 h1.le)
  | om => exact fun _ h1 => absurd h1 (lt_irrefl _)
  | @atom β y hβ hy _ _ ihy =>
    intro hSC h1
    rcases lt_or_eq_of_le (rhF_le_self β y) with hlt | heq
    · rw [tlLev_F hlt, tlI_rhF]; exact ⟨hβ, hy⟩
    · rw [← heq] at hSC h1 ⊢; exact ihy hSC h1
  | @add x y _ _ ihx ihy =>
    intro hSC h1
    rcases tf_prin_sum (tl_SC_prin hSC) rfl with ex | ey
    · rw [← ex] at hSC h1 ⊢; exact ihx hSC h1
    · rw [← ey] at hSC h1 ⊢; exact ihy hSC h1
  | @phi x y _ _ ihx ihy =>
    intro hSC h1
    rcases SC.eq_of_veblen_eq hSC rfl with ex | ey
    · rw [← ex] at hSC h1 ⊢; exact ihx hSC h1
    · rw [← ey] at hSC h1 ⊢; exact ihy hSC h1

/-- **The data of a code over a strongly critical `q` is below `q`.** -/
theorem tl_cl_dat {q : Ordinal.{0}} (hq : SC q) : ∀ z, TlCl q z → tlDat z < q := by
  rcases lt_or_ge Om1 q with hq1 | hq1
  · exact fun z _ => (tlDat_lt_Om1 z).trans hq1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tlDat_small h]; exact hz.lt_of_lt_Om1 hq h
  · rw [tlDat_Om1]; exact hq.1
  rcases le_or_gt tlX z with hX | hzX
  · rw [tlDat_big hX]; exact hq.1
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · obtain ⟨h1, h2⟩ := tl_cl_inv hq1 z hz h hE hI
      rw [tlDat_phi h hzX hE hI]
      exact max_lt (IH _ hI h1) (IH _ (tf_inv2_lt hE) h2)
    · have hSC := tl_SC_of h hI
      obtain ⟨hlv, hy⟩ := tl_cl_atom hq1 z hz hSC h
      obtain ⟨-, hyz, hlz⟩ := tl_nf hSC h hzX
      by_cases h0 : tlLev z = 0
      · have hg := tf_SC_gamma h hI
        have h1 : Om1 < tfIdx z := by rw [← tf_Om1_lt_gamma, hg]; exact h
        have hν : TlCl q (tfIdx z) := by rw [h0, tlI_zero] at hy; exact hy
        have hO : TlCl q (Om1 + 1) := TlCl.add TlCl.om (TlCl.one hq.1)
        have hc : TlCl q (tfIdx z - (Om1 + 1)) := (tlDec hq _ hν).1 _ hO (Order.add_one_le_of_lt h1)
        rw [tlDat_atom0 h hzX hE hI h0]
        exact IH _ (tl_atom0_lt h hzX hI h0) hc
      · rw [tlDat_atomF h hzX hE hI h0]
        exact max_lt (IH _ hlz hlv) (IH _ hyz hy)
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := tlDec hq z hz
    set g := log ω z with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hwk : TlCl q (ω ^ g * k) := TlCl.mul_nat hq.1 (TlCl.opow hq.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl q (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    rw [tlDat_cnf h hzX hE]
    exact max_lt (IH _ (tf_log_lt h hE) hlog) (IH _ (rj_mod_lt hz0) hr)

/-- **For a strongly critical `q` and `z < X`: `TlCl q z ↔ tlDat z < q`.** -/
theorem tl_cl_iff {q z : Ordinal.{0}} (hq : SC q) (hz : z < tlX) : TlCl q z ↔ tlDat z < q :=
  ⟨tl_cl_dat hq z, tl_code hq.1 z hz⟩

/-! ## Arithmetic of codes -/

/-- `TlCl y` is closed under `g ↦ ω^e·g` for a code `e`. -/
theorem tl_cl_opow_mul {y e : Ordinal.{0}} (hy : SC y) (he : TlCl y e) :
    ∀ g, TlCl y g → TlCl y (ω ^ e * g) := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact TlCl.zero hy.1
  obtain ⟨hsub, hlog⟩ := tlDec hy g hg
  have hwg := opow_log_le_self ω hg0
  have hgr := Ordinal.add_sub_cancel_of_le hwg
  rw [← hgr, mul_add, ← opow_add]
  exact TlCl.add (TlCl.opow hy.1 (TlCl.add he hlog))
    (IH _ (Ph.ph_sub_log_lt hg0) (hsub _ (TlCl.opow hy.1 hlog) hwg))

/-- `TlCl Z μ ⇒ TlCl Z (Ω₁·μ)`. -/
theorem tl_cl_Om1_mul {μ : Ordinal.{0}} (hZ : SC Z) (hμ : TlCl Z μ) : TlCl Z (Om1 * μ) := by
  have := tl_cl_opow_mul hZ TlCl.om μ hμ
  rwa [rj_Om1_opow] at this

/-- `TlCl Z (Ω₁ + μ) ↔ TlCl Z μ`. -/
theorem tl_cl_Om1_add {μ : Ordinal.{0}} (hZ : SC Z) : TlCl Z (Om1 + μ) ↔ TlCl Z μ := by
  refine ⟨fun h => ?_, fun h => TlCl.add TlCl.om h⟩
  have := (tlDec hZ _ h).1 _ TlCl.om le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The codes over a strongly critical `Z` are closed under `y ↦ y / Ω₁`.** -/
theorem tl_cl_div (hZ : SC Z) : ∀ y, TlCl Z y → TlCl Z (y / Om1) := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact TlCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := tlDec hZ y hy
  set g := log ω y with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  have hdec : ω ^ g * (y / ω ^ g) + y % ω ^ g = y := Ordinal.div_add_mod y _
  rw [hk] at hdec
  rcases lt_or_ge g Om1 with hgO | hgO
  · have hy1 : y < Om1 := by
      have h1 : y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
      refine h1.trans_le ?_
      rw [← rj_Om1_opow]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgO)
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact TlCl.zero hZ.1
  · set g' := g - Om1 with hg'
    have hge : Om1 + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : TlCl Z g' := (tlDec hZ g hlog).1 _ TlCl.om hgO
    have hwk : TlCl Z (ω ^ g * k) := TlCl.mul_nat hZ.1 (TlCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TlCl Z (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := rj_mod_lt hy0
    have e : y = Om1 * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, rj_Om1_opow, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hO0]
    exact TlCl.add (TlCl.mul_nat hZ.1 (TlCl.opow hZ.1 hg'C) k) (IH _ hry hr)

/-- **`tlDat (Ω₁ + μ) < b` makes `μ < X` a code over a strongly critical `b`.** -/
theorem tl_code_lvl {μ b : Ordinal.{0}} (hb : SC b) (hμ : μ < tlX) (hd : tlDat (Om1 + μ) < b) : TlCl b μ := by
  have hO : Om1 + μ < tlX := (Lq.lq_SC_indec tlX_SC).add_lt tlX_gt hμ
  exact (tl_cl_Om1_add hb).1 (tl_code hb.1 (Om1 + μ) hO hd)

end Googology.Trans.PoR.InaccPsi.R2.Tl
