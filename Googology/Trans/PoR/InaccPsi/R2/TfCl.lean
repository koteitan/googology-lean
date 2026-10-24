import Googology.Trans.PoR.InaccPsi.R2.TfTc

/-!
# Codes below `B_Γ` with the atoms `Γ_ν`: the closure and the data `Tf.tfDat`

`Ω₁ = Om1`, `Γ_ν = gamma ν`, `B_Γ = Tf.tfBG`.  `TfCl Z` is the set of codes over `Z`: generated from the ordinals below
`Z`, `Ω₁` and the atoms `Γ_ν` (`ν` a code, `ν > Ω₁`) by `+` and `φ`.  It extends `R2.LgCl` (one atom `Γ_{Ω₁+1}`) to
every atom below `B_Γ` (the atoms `ψ_{Ω₂}(c)`, `ν = Ω₁ + 1 + c`).

* `TfCl`, `TfCl.zero`, `TfCl.one`, `TfCl.opow`, `TfCl.mul_nat`, `TfCl.mono`, `tfCl_of_lg` (`LgCl Z ⊆ TfCl Z`),
  `TfCl.lt_of_lt_Om1` (countable codes over a strongly critical `Z` are `< Z`);
* `tfDec` (**decomposition**: `w − x` and `log_ω w` are codes for codes `x ≤ w`);
* `tf_code` (**`z < B_Γ` with `tfDat z < a` is a code over `a`**), `tf_cl_inv` (inverse Veblen functions of a code),
  `tf_cl_atom` (**the index of an atom code is a code**), `tf_cl_dat`, `tf_cl_iff` (**for a strongly critical `q` and
  `z < B_Γ`: `TfCl q z ↔ tfDat z < q`**; it extends `Tc.tc_cl_iff` from `Γ'` to `B_Γ`), `tf_cl_opow_mul`,
  `tf_cl_Om1_mul`, `tf_cl_Om1_add`, `tf_cl_div` (`y ↦ y / Ω₁`).

No new axiom.  New definition: `TfCl`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **The codes over `Z` with the atoms `Γ_ν`** (`ν > Ω₁` a code): generated from the ordinals below `Z`, `Ω₁` and
the atoms by `+` and `φ`. -/
inductive TfCl (Z : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Z → TfCl Z x
  | om : TfCl Z Om1
  | add {x y : Ordinal.{0}} : TfCl Z x → TfCl Z y → TfCl Z (x + y)
  | phi {x y : Ordinal.{0}} : TfCl Z x → TfCl Z y → TfCl Z (veblen x y)
  | gam {ν : Ordinal.{0}} : TfCl Z ν → Om1 < ν → TfCl Z (gamma ν)

variable {Z : Ordinal.{0}}

theorem TfCl.mono {Z' : Ordinal.{0}} (h : Z ≤ Z') {x : Ordinal.{0}} (hx : TfCl Z x) : TfCl Z' x := by
  induction hx with
  | small h' => exact TfCl.small (lt_of_lt_of_le h' h)
  | om => exact TfCl.om
  | add _ _ ihx ihy => exact TfCl.add ihx ihy
  | phi _ _ ihx ihy => exact TfCl.phi ihx ihy
  | gam _ h1 ih => exact TfCl.gam ih h1

theorem TfCl.zero (hZ : 0 < Z) : TfCl Z 0 := TfCl.small hZ

theorem TfCl.opow (hZ : 0 < Z) {c : Ordinal.{0}} (h : TfCl Z c) : TfCl Z (ω ^ c) := by
  have := TfCl.phi (TfCl.zero hZ) h; rwa [veblen_zero_apply] at this

theorem TfCl.one (hZ : 0 < Z) : TfCl Z 1 := by
  have := TfCl.opow hZ (TfCl.zero hZ); rwa [opow_zero] at this

theorem TfCl.mul_nat (hZ : 0 < Z) {x : Ordinal.{0}} (h : TfCl Z x) : ∀ n : ℕ, TfCl Z (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact TfCl.zero hZ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact TfCl.add (TfCl.mul_nat hZ h n) h

/-- **`LgCl Z ⊆ TfCl Z`** (the atom `Γ_{Ω₁+1}`). -/
theorem tfCl_of_lg (hZ : 0 < Z) {x : Ordinal.{0}} (hx : LgCl Z x) : TfCl Z x := by
  induction hx with
  | small h => exact TfCl.small h
  | om => rw [← rj_Om1]; exact TfCl.om
  | gam =>
    rw [tf_ggGam]
    exact TfCl.gam (TfCl.add TfCl.om (TfCl.one hZ)) (lt_add_one _)
  | add _ _ ihx ihy => exact TfCl.add ihx ihy
  | phi _ _ ihx ihy => exact TfCl.phi ihx ihy

/-- A countable code over a strongly critical `Z` is below `Z`. -/
theorem TfCl.lt_of_lt_Om1 (hZ : SC Z) {x : Ordinal.{0}} (hx : TfCl Z x) : x < Om1 → x < Z := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hZ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1)) (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hZ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))
  | gam _ h1 _ => exact fun h => absurd ((tf_Om1_lt_gamma.2 h1).trans h) (lt_irrefl _)

/-! ## Decomposition -/

theorem tf_gamma_prin (ν : Ordinal.{0}) : IsPrincipal (· + ·) (gamma ν) := by
  rw [← Low.opow_eq_self_of_SC (Lq.lq_gamma_SC ν)]; exact isPrincipal_add_omega0_opow _

theorem tf_log_gamma (ν : Ordinal.{0}) : log ω (gamma ν) = gamma ν := by
  conv_lhs => rw [← Low.opow_eq_self_of_SC (Lq.lq_gamma_SC ν)]
  exact log_opow one_lt_omega0 _

/-- **Decomposition**: for a strongly critical `Z`, a code `w` over `Z` has `w − x` (for every code `x ≤ w`) and
`log_ω w` codes over `Z`. -/
theorem tfDec (hZ : SC Z) : ∀ w, TfCl Z w →
    (∀ x, TfCl Z x → x ≤ w → TfCl Z (w - x)) ∧ TfCl Z (log ω w) := by
  have h0 : TfCl Z 0 := TfCl.zero hZ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, TfCl Z v → v ≤ w →
      (∀ x, TfCl Z x → x ≤ v → TfCl Z (v - x)) ∧ TfCl Z (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => TfCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      TfCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hp : IsPrincipal (· + ·) (Om1 : Ordinal.{0}) := by
      rw [← rj_Om1_opow]; exact isPrincipal_add_omega0_opow _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hp hx with e | e <;> rw [e]
      · exact TfCl.om
      · exact h0
    · have : log ω (Om1 : Ordinal.{0}) = Om1 := by
        conv_lhs => rw [← rj_Om1_opow]
        exact log_opow one_lt_omega0 _
      rw [this]; exact TfCl.om
  | @gam ν hν h1 _ =>
    intro _
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin (tf_gamma_prin ν) hx with e | e <;> rw [e]
      · exact TfCl.gam hν h1
      · exact h0
    · rw [tf_log_gamma]; exact TfCl.gam hν h1
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact TfCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : TfCl Z (x - u) := (IHo x hxw hx).1 u hu hux.le
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
        · exact TfCl.opow hZ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact TfCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact TfCl.phi ha hb

/-! ## Codes and data -/

/-- **A code**: `z < B_Γ` with `tfDat z < a` (`0 < a`) is a code over `a`. -/
theorem tf_code {a : Ordinal.{0}} (ha : 0 < a) : ∀ z : Ordinal.{0}, z < tfBG → tfDat z < a → TfCl a z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzB hd
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tfDat_small h] at hd; exact TfCl.small hd
  · exact TfCl.om
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [tfDat_phi h hzB hE hI] at hd
      have h2 := tf_inv2_lt hE
      have e : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact TfCl.phi (IH _ hI (hI.trans hzB) ((le_max_left _ _).trans_lt hd))
        (IH _ h2 (h2.trans hzB) ((le_max_right _ _).trans_lt hd))
    · have hg := tf_SC_gamma h hI
      have h1 : Om1 < tfIdx z := by rw [← tf_Om1_lt_gamma, hg]; exact h
      have hlt := tf_atom_lt h hzB hI
      rw [tfDat_atom h hzB hE hI] at hd
      have hc := IH _ hlt (hlt.trans hzB) hd
      have e : (Om1 + 1) + (tfIdx z - (Om1 + 1)) = tfIdx z :=
        Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)
      rw [← hg]
      exact TfCl.gam (e ▸ TfCl.add (TfCl.add TfCl.om (TfCl.one ha)) hc) h1
  · rw [tfDat_cnf h hzB hE] at hd
    have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := tf_log_lt h hE
    have hm := rj_mod_lt hz0
    have he := IH _ hl (hl.trans hzB) ((le_max_left _ _).trans_lt hd)
    have hr := IH _ hm (hm.trans hzB) ((le_max_right _ _).trans_lt hd)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z := Ordinal.div_add_mod z _
    rw [← hdec, hk]
    exact TfCl.add (TfCl.mul_nat ha (TfCl.opow ha he) k) hr

/-- An additive principal sum is one of its summands. -/
theorem tf_prin_sum {x y z : Ordinal.{0}} (hp : IsPrincipal (· + ·) z) (e : x + y = z) : x = z ∨ y = z := by
  rcases eq_or_lt_of_le (le_self_add : x ≤ x + y) with ex | hx
  · exact Or.inl (ex.trans e)
  rcases eq_or_lt_of_le (le_add_self : y ≤ x + y) with ey | hy
  · exact Or.inr (ey.trans e)
  rw [e] at hx hy
  have h := hp hx hy
  simp only at h
  rw [e] at h
  exact absurd h (lt_irrefl _)

/-- **The codes over a countable `Z` are closed under the inverse Veblen function** at the `ε`-numbers `z > Ω₁` that
are not atoms. -/
theorem tf_cl_inv (hZ : Z ≤ Om1) : ∀ z, TfCl Z z → Om1 < z → ω ^ z = z → invVeblen₁ z < z →
    TfCl Z (invVeblen₁ z) ∧ TfCl Z (invVeblen₂ z) := by
  intro z hz
  induction hz with
  | small h => exact fun h1 _ _ => absurd (h.trans_le hZ) (not_lt.2 h1.le)
  | om => exact fun h1 _ _ => absurd h1 (lt_irrefl _)
  | gam _ _ _ => exact fun _ _ hI => by rw [invVeblen₁_gamma] at hI; exact absurd hI (lt_irrefl _)
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

/-- **The index of an atom code is a code**: `TfCl Z Γ_ν` (`ν > Ω₁`, `Z ≤ Ω₁`) gives `TfCl Z ν`. -/
theorem tf_cl_atom (hZ : Z ≤ Om1) : ∀ z, TfCl Z z → ∀ ν, Om1 < ν → gamma ν = z → TfCl Z ν := by
  intro z hz
  induction hz with
  | small h =>
    exact fun ν h1 e => absurd ((h.trans_le hZ).trans (tf_Om1_lt_gamma.2 h1)) (by rw [e]; exact lt_irrefl _)
  | om => exact fun ν h1 e => absurd (tf_Om1_lt_gamma.2 h1) (by rw [e]; exact lt_irrefl _)
  | @gam μ hμ _ _ => exact fun ν _ e => by rw [gamma_inj.1 e]; exact hμ
  | @add x y _ _ ihx ihy =>
    intro ν h1 e
    rcases tf_prin_sum (e ▸ tf_gamma_prin ν) e.symm with ex | ey
    · exact ihx ν h1 ex.symm
    · exact ihy ν h1 ey.symm
  | @phi x y _ _ ihx ihy =>
    intro ν h1 e
    rcases SC.eq_of_veblen_eq (Lq.lq_gamma_SC ν) e.symm with ex | ey
    · exact ihx ν h1 ex.symm
    · exact ihy ν h1 ey.symm

/-- **The data of a code over a strongly critical `q` is below `q`.** -/
theorem tf_cl_dat {q : Ordinal.{0}} (hq : SC q) : ∀ z, TfCl q z → tfDat z < q := by
  rcases lt_or_ge Om1 q with hq1 | hq1
  · exact fun z _ => (tfDat_lt_Om1 z).trans hq1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tfDat_small h]; exact hz.lt_of_lt_Om1 hq h
  · rw [tfDat_Om1]; exact hq.1
  rcases le_or_gt tfBG z with hB | hzB
  · rw [tfDat_big hB]; exact hq.1
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · obtain ⟨h1, h2⟩ := tf_cl_inv hq1 z hz h hE hI
      rw [tfDat_phi h hzB hE hI]
      exact max_lt (IH _ hI h1) (IH _ (tf_inv2_lt hE) h2)
    · have hg := tf_SC_gamma h hI
      have h1 : Om1 < tfIdx z := by rw [← tf_Om1_lt_gamma, hg]; exact h
      have hν : TfCl q (tfIdx z) := tf_cl_atom hq1 z hz _ h1 hg
      have hO : TfCl q (Om1 + 1) := TfCl.add TfCl.om (TfCl.one hq.1)
      have hc : TfCl q (tfIdx z - (Om1 + 1)) := (tfDec hq _ hν).1 _ hO (Order.add_one_le_of_lt h1)
      rw [tfDat_atom h hzB hE hI]
      exact IH _ (tf_atom_lt h hzB hI) hc
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := tfDec hq z hz
    set g := log ω z with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hwk : TfCl q (ω ^ g * k) := TfCl.mul_nat hq.1 (TfCl.opow hq.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TfCl q (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    rw [tfDat_cnf h hzB hE]
    exact max_lt (IH _ (tf_log_lt h hE) hlog) (IH _ (rj_mod_lt hz0) hr)

/-- **For a strongly critical `q` and `z < B_Γ`: `TfCl q z ↔ tfDat z < q`.** -/
theorem tf_cl_iff {q z : Ordinal.{0}} (hq : SC q) (hz : z < tfBG) : TfCl q z ↔ tfDat z < q :=
  ⟨tf_cl_dat hq z, tf_code hq.1 z hz⟩

/-! ## Arithmetic of codes -/

/-- `TfCl y` is closed under `g ↦ ω^e·g` for a code `e`. -/
theorem tf_cl_opow_mul {y e : Ordinal.{0}} (hy : SC y) (he : TfCl y e) :
    ∀ g, TfCl y g → TfCl y (ω ^ e * g) := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact TfCl.zero hy.1
  obtain ⟨hsub, hlog⟩ := tfDec hy g hg
  have hwg := opow_log_le_self ω hg0
  have hgr := Ordinal.add_sub_cancel_of_le hwg
  rw [← hgr, mul_add, ← opow_add]
  exact TfCl.add (TfCl.opow hy.1 (TfCl.add he hlog))
    (IH _ (Ph.ph_sub_log_lt hg0) (hsub _ (TfCl.opow hy.1 hlog) hwg))

/-- `TfCl Z μ ⇒ TfCl Z (Ω₁·μ)`. -/
theorem tf_cl_Om1_mul {μ : Ordinal.{0}} (hZ : SC Z) (hμ : TfCl Z μ) : TfCl Z (Om1 * μ) := by
  have := tf_cl_opow_mul hZ TfCl.om μ hμ
  rwa [rj_Om1_opow] at this

/-- `TfCl Z (Ω₁ + μ) ↔ TfCl Z μ`. -/
theorem tf_cl_Om1_add {μ : Ordinal.{0}} (hZ : SC Z) : TfCl Z (Om1 + μ) ↔ TfCl Z μ := by
  refine ⟨fun h => ?_, fun h => TfCl.add TfCl.om h⟩
  have := (tfDec hZ _ h).1 _ TfCl.om le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The codes over a strongly critical `Z` are closed under `y ↦ y / Ω₁`.** -/
theorem tf_cl_div (hZ : SC Z) : ∀ y, TfCl Z y → TfCl Z (y / Om1) := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact TfCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := tfDec hZ y hy
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
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact TfCl.zero hZ.1
  · set g' := g - Om1 with hg'
    have hge : Om1 + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : TfCl Z g' := (tfDec hZ g hlog).1 _ TfCl.om hgO
    have hwk : TfCl Z (ω ^ g * k) := TfCl.mul_nat hZ.1 (TfCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TfCl Z (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := rj_mod_lt hy0
    have e : y = Om1 * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, rj_Om1_opow, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hO0]
    exact TfCl.add (TfCl.mul_nat hZ.1 (TfCl.opow hZ.1 hg'C) k) (IH _ hry hr)

end Googology.Trans.PoR.InaccPsi.R2.Tf
