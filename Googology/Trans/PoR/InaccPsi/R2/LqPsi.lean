import Googology.Trans.PoR.InaccPsi.R2.LqGam
import Googology.Trans.PoR.InaccPsi.R2.MxGam

/-!
# `ψ_{Ω₁}(A + d)` is the `d`-th strongly critical ordinal above `ψ_{Ω₁}(A)`, below the first fixed point of `Γ_`

`ψ = S.psi`, `Γ_ = Ordinal.gamma`.  An argument `A` is *own* when `A ∈ Cl(A, ψ_{Ω₁}(A))`; `d` is *valid* (for `A`)
when `d < ψ_{Ω₁}(A + d)` (the normal-form condition of `ψ_{Ω₁}(A + d)`).

* `lq_dvd_of_indec` (an additive principal `p ≥ Ω₁` is a multiple of `Ω₁`), `lq_mod_add_le` (`(x + y) mod Ω₁ ≤
  x mod Ω₁ + y mod Ω₁`), `lq_Om1_dvd_A` (**`Ω₁ ∣ A_η`**);
* `lq_psi_le` (**`ψ_{Ω₁}(A + D) ≤ s`** for a strongly critical `s` above `ψ_{Ω₁}(A)` and every `ψ_{Ω₁}(A + d)`, `d < D`;
  as `Mx.mxPsi_succ_le`);
* `lq_psi_inv` (**`ψ_{Ω₁}(A + D) ≤ q` for every `D ≤ Ω₁`** when `Ω₁ ∣ A` and the strongly critical `q > ψ_{Ω₁}(A)` lies
  above every `ψ_{Ω₁}(A + d)`, `d < q`: by induction on `Cl(A + D, q)`, every member `x` has `x mod Ω₁ < q`);
* `lq_psi_down` (**validity is closed downwards**);
* `lq_psi_gamma` (**`ψ_{Ω₁}(A + D) = Γ_{c+D}` at every valid `D`**, `Γ_c = ψ_{Ω₁}(A)`), `lq_psi_gamma_of` (**`D` is
  valid and `ψ_{Ω₁}(A + D) = Γ_{c+D}` when `d < Γ_{c+d}` for every `d ≤ D`**), `lq_psi_valid_cond` (a valid `D` has
  `d < Γ_{c+d}` for every `d ≤ D`).

No axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-! ## Multiples of `Ω₁` -/

/-- **An additive principal `p ≥ Ω₁` is a multiple of `Ω₁`.** -/
theorem lq_dvd_of_indec {p : Ordinal.{0}} (hp : Indec p) (h1 : Om 1 ≤ p) : Om 1 ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  have he : Om 1 ≤ e := by
    have : ω ^ Om (1 : Ordinal.{0}) ≤ ω ^ e := by rw [Bt.Om1_opow]; exact h1
    exact (opow_le_opow_iff_right one_lt_omega0).1 this
  refine ⟨ω ^ (e - Om 1), ?_⟩
  calc ω ^ e = ω ^ (Om 1 + (e - Om 1)) := by rw [Ordinal.add_sub_cancel_of_le he]
    _ = ω ^ Om (1 : Ordinal.{0}) * ω ^ (e - Om 1) := opow_add _ _ _
    _ = Om 1 * ω ^ (e - Om 1) := by rw [Bt.Om1_opow]

theorem lq_Om1_indec : Indec (Om (1 : Ordinal.{0})) := inE_indec Bt.Om1_opow

/-- `r + Ω₁·v = Ω₁·v` for `r < Ω₁`, `v ≥ 1`. -/
theorem lq_absorb {r v : Ordinal.{0}} (hr : r < Om 1) (hv : 1 ≤ v) : r + Om 1 * v = Om 1 * v := by
  rw [← Ordinal.add_sub_cancel_of_le hv, mul_add, mul_one, ← add_assoc, lq_Om1_indec.add_eq hr]

/-- **`(x + y) mod Ω₁ ≤ x mod Ω₁ + y mod Ω₁`.** -/
theorem lq_mod_add_le (x y : Ordinal.{0}) : (x + y) % Om 1 ≤ x % Om 1 + y % Om 1 := by
  have hb : (0 : Ordinal.{0}) < Om 1 := lq_Om1_indec.pos
  have hx := Ordinal.div_add_mod x (Om 1)
  have hy := Ordinal.div_add_mod y (Om 1)
  have hxr : x % Om 1 < Om 1 := Ordinal.mod_lt x hb.ne'
  have hyr : y % Om 1 < Om 1 := Ordinal.mod_lt y hb.ne'
  rcases eq_or_ne (y / Om 1) 0 with h0 | h0
  · rw [h0, mul_zero, zero_add] at hy
    have e : x + y = Om 1 * (x / Om 1) + (x % Om 1 + y % Om 1) := by
      conv_lhs => rw [← hx, ← hy]
      rw [add_assoc]
    rw [e, mul_add_mod_self, Ordinal.mod_eq_of_lt (lq_Om1_indec.add_lt hxr hyr)]
  · have e : x + y = Om 1 * (x / Om 1 + y / Om 1) + y % Om 1 := by
      conv_lhs => rw [← hx, ← hy]
      rw [add_assoc, ← add_assoc (x % Om 1), lq_absorb hxr (one_le_iff_ne_zero.2 h0), ← add_assoc, ← mul_add]
    rw [e, mul_add_mod_self, Ordinal.mod_eq_of_lt hyr]
    exact le_add_self

theorem lq_mod_indec {p : Ordinal.{0}} (hp : Indec p) (h1 : Om 1 ≤ p) : p % Om 1 = 0 :=
  Ordinal.mod_eq_zero_of_dvd (lq_dvd_of_indec hp h1)

theorem lq_SC_indec {p : Ordinal.{0}} (hp : SC p) : Indec p := inE_indec (Gg.gg_SC_eps hp)

/-- **`Ω₁ ∣ A_η`.** -/
theorem lq_Om1_dvd_A (η : Ordinal.{0}) : Om 1 ∣ ConjT.Aη S η := by
  have h1 : Om 1 ∣ Om (ω : Ordinal.{0}) :=
    lq_dvd_of_indec (lq_SC_indec (SC_Om omega0_pos.ne')) (Om_le_Om.2 one_lt_omega0.le)
  have h2 : Om 1 ∣ ConjT.th S := lq_dvd_of_indec (lq_SC_indec (ConjT.SC_th S)) (Bt.Om1_lt_th).le
  exact dvd_add h1 (h2.mul_right η)

/-! ## Upper bounds for `ψ_{Ω₁}(A + D)` -/

/-- **`ψ_{Ω₁}(A + D) ≤ s`** for a strongly critical `s` above `ψ_{Ω₁}(A)` and above every `ψ_{Ω₁}(A + d)`, `d < D`. -/
theorem lq_psi_le {A D s : Ordinal.{0}} (hs : SC s) (hAs : S.psi A (Om 1) < s)
    (hprev : ∀ d, d < D → S.psi (A + d) (Om 1) < s) : S.psi (A + D) (Om 1) ≤ s := by
  rcases le_or_gt (Om 1) s with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) ?_
  intro x hx
  induction hx with
  | @small x hxb => exact fun _ => hxb
  | zero => exact fun _ => hs.1
  | inacc n => exact fun h => absurd h (not_lt.2 (Gg.gg_Om1_lt_I S n).le)
  | inaccW => exact fun h => absurd h (not_lt.2 (Gg.gg_Om1_lt_Iw S).le)
  | @add x y _ _ ihx ihy =>
    intro h
    have hx1 : x < Om 1 := lt_of_le_of_lt le_self_add h
    have hy1 : y < Om 1 := lt_of_le_of_lt le_add_self h
    exact hs.isPrincipal (ihx hx1) (ihy hy1)
  | @phi x y _ _ ihx ihy =>
    intro h
    have hx1 : x < Om 1 := lt_of_le_of_lt (left_le_veblen x y) h
    have hy1 : y < Om 1 := lt_of_le_of_lt (right_le_veblen x y) h
    exact hs.2 x (ihx hx1) y (ihy hy1)
  | @om x _ _ =>
    intro h
    rw [Mx.mxOm_lt_one h, Om_zero]
    exact hs.1
  | @coll π e hπ _ _ _ _ =>
    intro h
    have hπ1 : π = Om 1 := by
      by_contra hne
      exact absurd h (not_lt.2 (Mx.mxOm1_le_psi hπ hne))
    subst hπ1
    show S.psi e.1 (Om 1) < s
    rcases lt_or_ge e.1 A with heA | heA
    · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heA.le).1 hAs
    · have hde : A + (e.1 - A) = e.1 := Ordinal.add_sub_cancel_of_le heA
      have hdD : e.1 - A < D := by
        have := e.2
        rw [← hde] at this
        exact (add_lt_add_iff_left A).1 this
      have := hprev _ hdD
      rwa [hde] at this

/-- **`ψ_{Ω₁}(A + D) ≤ q` for every `D ≤ Ω₁`** when `Ω₁ ∣ A` and the strongly critical `q > ψ_{Ω₁}(A)` is above every
`ψ_{Ω₁}(A + d)`, `d < q`. -/
theorem lq_psi_inv {A D q : Ordinal.{0}} (hA : Om 1 ∣ A) (hq : SC q) (hAq : S.psi A (Om 1) < q)
    (hD : D ≤ Om 1) (hprev : ∀ d, d < q → S.psi (A + d) (Om 1) < q) : S.psi (A + D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  have hqI : Indec q := lq_SC_indec hq
  have hinv : ∀ x, x ∈ S.CSet (A + D) q → x % Om 1 < q := by
    intro x hx
    induction hx with
    | @small x hxb => exact (Ordinal.mod_le x (Om 1)).trans_lt hxb
    | zero => rw [Ordinal.zero_mod]; exact hq.1
    | inacc n =>
      rw [lq_mod_indec (lq_SC_indec (SC_I (S := S) n)) (Gg.gg_Om1_lt_I S n).le]; exact hq.1
    | inaccW =>
      rw [lq_mod_indec (lq_SC_indec (SC_Iw (S := S))) (Gg.gg_Om1_lt_Iw S).le]; exact hq.1
    | @add x y _ _ ihx ihy => exact (lq_mod_add_le x y).trans_lt (hqI.add_lt ihx ihy)
    | @phi x y _ _ ihx ihy =>
      by_cases hv : veblen x y < Om 1
      · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
        have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
        rw [Ordinal.mod_eq_of_lt hx1] at ihx
        rw [Ordinal.mod_eq_of_lt hy1] at ihy
        rw [Ordinal.mod_eq_of_lt hv]
        exact hq.2 x ihx y ihy
      · push Not at hv
        rw [lq_mod_indec (Mw.mw_veblen_indec x y) hv]; exact hq.1
    | @om x _ _ =>
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [Om_zero, Ordinal.zero_mod]; exact hq.1
      · rw [lq_mod_indec (lq_SC_indec (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))]; exact hq.1
    | @coll π e hπ _ _ _ ihe =>
      show S.psi e.1 π % Om 1 < q
      by_cases hπ1 : π = Om 1
      · subst hπ1
        rw [Ordinal.mod_eq_of_lt (psi_lt Low.InR_Om_one _)]
        rcases lt_or_ge e.1 A with heA | heA
        · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heA.le).1 hAq
        · have hde : A + (e.1 - A) = e.1 := Ordinal.add_sub_cancel_of_le heA
          have hdD : e.1 - A < D := by
            have := e.2
            rw [← hde] at this
            exact (add_lt_add_iff_left A).1 this
          have hdΩ : e.1 - A < Om 1 := hdD.trans_le hD
          have hmod : e.1 % Om 1 = e.1 - A := by
            obtain ⟨k, hk⟩ := hA
            calc e.1 % Om 1 = (Om 1 * k + (e.1 - A)) % Om 1 := by rw [← hk, hde]
              _ = e.1 - A := by rw [mul_add_mod_self, Ordinal.mod_eq_of_lt hdΩ]
          rw [hmod] at ihe
          have := hprev _ ihe
          rwa [hde] at this
      · rw [lq_mod_indec (lq_SC_indec (SC_psi hπ e.1)) (Mx.mxOm1_le_psi hπ hπ1)]; exact hq.1
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := hinv x hx
  rwa [Ordinal.mod_eq_of_lt hx1] at this

/-! ## Validity -/

/-- **Validity is closed downwards** (`Ω₁ ∣ A`, `A` own). -/
theorem lq_psi_down {A d₁ d₂ : Ordinal.{0}} (hA : Om 1 ∣ A) (hown : A ∈ S.CSet A (S.psi A (Om 1)))
    (h12 : d₁ ≤ d₂) (hv : d₂ < S.psi (A + d₂) (Om 1)) : d₁ < S.psi (A + d₁) (Om 1) := by
  by_contra hle
  push Not at hle
  have hq : SC (S.psi (A + d₁) (Om 1)) := SC_psi Low.InR_Om_one _
  have hd0 : d₁ ≠ 0 := by
    rintro rfl
    exact absurd (lt_of_lt_of_le hq.1 hle) (lt_irrefl 0)
  have hAq : S.psi A (Om 1) < S.psi (A + d₁) (Om 1) :=
    (Mx.mxPsi_succ_gt hown).trans_le
      (psi_mono Low.InR_Om_one ((add_le_add_iff_left A).2 (one_le_iff_ne_zero.2 hd0))).1
  have hprev : ∀ d, d < S.psi (A + d₁) (Om 1) → S.psi (A + d) (Om 1) < S.psi (A + d₁) (Om 1) := by
    intro d hd
    have hdd : A + d < A + d₁ := (add_lt_add_iff_left A).2 (hd.trans_le hle)
    have hmem : A + d ∈ S.CSet (A + d₁) (S.psi (A + d₁) (Om 1)) :=
      CSet.add_mem ((psi_mono Low.InR_Om_one (le_self_add : A ≤ A + d₁)).2 hown) (CSet.of_lt hd)
    exact psi_lt_psi_of_mem Low.InR_Om_one hdd hmem
  have hD : d₂ ≤ Om 1 := hv.le.trans (psi_lt Low.InR_Om_one _).le
  have h := lq_psi_inv hA hq hAq hD hprev
  exact absurd ((h.trans hle).trans h12) (not_le.2 hv)

/-- The lower bound: `Γ_{c+D} ≤ ψ_{Ω₁}(A + D)` when `ψ_{Ω₁}(A + d) = Γ_{c+d}` is below `ψ_{Ω₁}(A + D)` for every
`d < D`. -/
theorem lq_psi_ge {A c D : Ordinal.{0}} (hc : gamma c = S.psi A (Om 1))
    (hlt : ∀ d, d < D → gamma (c + d) < S.psi (A + D) (Om 1)) : gamma (c + D) ≤ S.psi (A + D) (Om 1) := by
  obtain ⟨e, he⟩ := lq_SC_gamma (SC_psi (S := S) Low.InR_Om_one (A + D))
  rw [← he]
  have hce : c ≤ e := by
    have : S.psi A (Om 1) ≤ S.psi (A + D) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
    rw [← hc, ← he] at this; exact gamma_le_gamma.1 this
  refine gamma_le_gamma.2 (not_lt.1 fun hlt' => ?_)
  have hde : c + (e - c) = e := Ordinal.add_sub_cancel_of_le hce
  have hd : e - c < D := by rw [← hde] at hlt'; exact (add_lt_add_iff_left c).1 hlt'
  have h := hlt _ hd
  rw [hde, ← he] at h
  exact lt_irrefl _ h

/-- **`ψ_{Ω₁}(A + D) = Γ_{c+D}` at every valid `D`** (`Ω₁ ∣ A`, `A` own, `Γ_c = ψ_{Ω₁}(A)`). -/
theorem lq_psi_gamma {A c : Ordinal.{0}} (hA : Om 1 ∣ A) (hown : A ∈ S.CSet A (S.psi A (Om 1)))
    (hc : gamma c = S.psi A (Om 1)) :
    ∀ D, D < S.psi (A + D) (Om 1) → S.psi (A + D) (Om 1) = gamma (c + D) := by
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hv
  have hIH : ∀ d, d < D → S.psi (A + d) (Om 1) = gamma (c + d) :=
    fun d hd => IH d hd (lq_psi_down hA hown hd.le hv)
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [add_zero, add_zero, hc]
  apply le_antisymm
  · refine lq_psi_le (lq_gamma_SC _) ?_ fun d hd => ?_
    · rw [← hc]; exact gamma_lt_gamma.2 (lt_add_of_pos_right c (pos_iff_ne_zero.2 hD0))
    · rw [hIH d hd]; exact gamma_lt_gamma.2 ((add_lt_add_iff_left c).2 hd)
  · refine lq_psi_ge hc fun d hd => ?_
    rw [← hIH d hd]
    have hmem : A + d ∈ S.CSet (A + D) (S.psi (A + D) (Om 1)) :=
      CSet.add_mem ((psi_mono Low.InR_Om_one (le_self_add : A ≤ A + D)).2 hown) (CSet.of_lt (hd.trans hv))
    exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hd) hmem

/-- **`D` is valid and `ψ_{Ω₁}(A + D) = Γ_{c+D}` when `d < Γ_{c+d}` for every `d ≤ D`** (`A` own, `Γ_c = ψ_{Ω₁}(A)`). -/
theorem lq_psi_gamma_of {A c : Ordinal.{0}} (hown : A ∈ S.CSet A (S.psi A (Om 1)))
    (hc : gamma c = S.psi A (Om 1)) :
    ∀ D, (∀ d, d ≤ D → d < gamma (c + d)) → D < S.psi (A + D) (Om 1) ∧ S.psi (A + D) (Om 1) = gamma (c + D) := by
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hcond
  have hIH : ∀ d, d < D → S.psi (A + d) (Om 1) = gamma (c + d) :=
    fun d hd => (IH d hd fun d' hd' => hcond d' (hd'.trans hd.le)).2
  have heq : S.psi (A + D) (Om 1) = gamma (c + D) := by
    rcases eq_or_ne D 0 with rfl | hD0
    · rw [add_zero, add_zero, hc]
    apply le_antisymm
    · refine lq_psi_le (lq_gamma_SC _) ?_ fun d hd => ?_
      · rw [← hc]; exact gamma_lt_gamma.2 (lt_add_of_pos_right c (pos_iff_ne_zero.2 hD0))
      · rw [hIH d hd]; exact gamma_lt_gamma.2 ((add_lt_add_iff_left c).2 hd)
    · refine lq_psi_ge hc fun d hd => ?_
      rw [← hIH d hd]
      have hdv : d < S.psi (A + D) (Om 1) := by
        calc d < gamma (c + d) := hcond d hd.le
          _ = S.psi (A + d) (Om 1) := (hIH d hd).symm
          _ ≤ S.psi (A + D) (Om 1) := (psi_mono Low.InR_Om_one ((add_le_add_iff_left A).2 hd.le)).1
      have hmem : A + d ∈ S.CSet (A + D) (S.psi (A + D) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one (le_self_add : A ≤ A + D)).2 hown) (CSet.of_lt hdv)
      exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left A).2 hd) hmem
  exact ⟨by rw [heq]; exact hcond D le_rfl, heq⟩

/-- **A valid `D` has `d < Γ_{c+d}` for every `d ≤ D`** (`Ω₁ ∣ A`, `A` own, `Γ_c = ψ_{Ω₁}(A)`). -/
theorem lq_psi_valid_cond {A c D : Ordinal.{0}} (hA : Om 1 ∣ A) (hown : A ∈ S.CSet A (S.psi A (Om 1)))
    (hc : gamma c = S.psi A (Om 1)) (hv : D < S.psi (A + D) (Om 1)) : ∀ d, d ≤ D → d < gamma (c + d) := by
  intro d hd
  have hvd := lq_psi_down hA hown hd hv
  rw [lq_psi_gamma hA hown hc d hvd] at hvd
  exact hvd

end Googology.Trans.PoR.InaccPsi.R2.Lq
