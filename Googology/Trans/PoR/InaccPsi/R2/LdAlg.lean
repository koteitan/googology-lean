import Googology.Trans.PoR.InaccPsi.R2.LdEQ

/-!
# Division, left subtraction and multiplication by a strongly critical `κ` in the closures, and `B_n(κ·x)`

`κ` strongly critical (so `ω^κ = κ`), `Cl(a, b) = S.CSet a b`, `B_n = Bc.bcB S n`.

* `ldDivK_add_lt`, `ldDivK_add_ge` (`(x + y)/κ`), `ldDivK_prin` (**`p/κ = ω^{log p - κ}`** for an additive
  principal `p ≥ κ`);
* `ldSubK_mem` (**`Cl(a, b)` is closed under `x ↦ x - κ`** for `x ≥ κ`), `ldDivK_mem` (**and under `x ↦ x/κ`**);
* `ldMulK_small`, `ldMulK_mem` (**`κ·x ∈ Cl(a, b)` for `x ∈ Cl(a, b)`**, or `x < b`, when `κ ∈ Cl(a, b)`);
* `ldB_opow` (`B_n(ω^g) = ω^{B_n g}` on `MvD`), `ldB_mulK` (**`B_n(κ·x) = κ·B_n(x)`** for `B_n κ = κ` and every `x < κ`
  in a class of `MvD` closed under `log` and the tail).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-! ## Division by `κ` -/

theorem ldDivK_add_lt {κ : Ordinal.{0}} (hκ : SC κ) (x : Ordinal.{0}) {y : Ordinal.{0}} (hy : y < κ) :
    (x + y) / κ = x / κ := by
  have hκ0 : κ ≠ 0 := hκ.1.ne'
  have hr : x % κ < κ := Ordinal.mod_lt x hκ0
  have e : x + y = κ * (x / κ) + (x % κ + y) := by
    conv_lhs => rw [← Ordinal.div_add_mod x κ]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_div _ hκ0, Ordinal.div_eq_zero_of_lt (hκ.isPrincipal hr hy), add_zero]

theorem ldDivK_add_ge {κ : Ordinal.{0}} (hκ : SC κ) (x : Ordinal.{0}) {y : Ordinal.{0}} (hy : κ ≤ y) :
    (x + y) / κ = x / κ + y / κ := by
  have hκ0 : κ ≠ 0 := hκ.1.ne'
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  have hy' : y = κ * (y / κ) + y % κ := (Ordinal.div_add_mod y κ).symm
  have hq0 : y / κ ≠ 0 := by
    intro h0
    have : y < κ := by
      rw [hy', h0, mul_zero, zero_add]; exact Ordinal.mod_lt y hκ0
    exact absurd hy (not_le.2 this)
  have habs : x % κ + κ * (y / κ) = κ * (y / κ) := by
    refine Ordinal.add_of_omega0_opow_le (b := κ) ?_ ?_
    · rw [hE]; exact Ordinal.mod_lt x hκ0
    · rw [hE]; exact le_mul_left κ (pos_iff_ne_zero.2 hq0)
  have e : x + y = κ * (x / κ + y / κ) + y % κ := by
    conv_lhs => rw [← Ordinal.div_add_mod x κ, hy']
    rw [mul_add, add_assoc (κ * (x / κ)), ← add_assoc (x % κ), habs, add_assoc]
  rw [e, Ordinal.mul_add_div _ hκ0, Ordinal.div_eq_zero_of_lt (Ordinal.mod_lt y hκ0), add_zero]

/-- **`p/κ = ω^{log p - κ}`** for an additive principal `p ≥ κ`, and `p = κ·(p/κ)`. -/
theorem ldDivK_prin {κ p : Ordinal.{0}} (hκ : SC κ) (hp : IsPrincipal (· + ·) p) (h1 : κ ≤ p) :
    p / κ = ω ^ (log ω p - κ) ∧ κ ≤ log ω p ∧ p = κ * ω ^ (log ω p - κ) := by
  have hκ0 : κ ≠ 0 := hκ.1.ne'
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h0 | ⟨γ, rfl⟩
  · exact absurd (h0 ▸ h1) (not_le.2 hκ.1)
  · dsimp only at hp h1 ⊢
    rw [log_opow one_lt_omega0]
    have hγ : κ ≤ γ := by
      rw [← hE] at h1; exact (opow_le_opow_iff_right one_lt_omega0).1 h1
    have e : ω ^ γ = κ * ω ^ (γ - κ) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hγ]
      rw [opow_add, hE]
    refine ⟨?_, hγ, e⟩
    rw [e, Ordinal.mul_div_cancel _ hκ0]

/-! ## Left subtraction of `κ` -/

/-- **`Cl(a, b)` is closed under `x ↦ x - κ`** for `x ≥ κ`. -/
theorem ldSubK_mem {κ a b x : Ordinal.{0}} (hκ : SC κ) (hx : x ∈ S.CSet a b) : κ ≤ x → x - κ ∈ S.CSet a b := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → p ∈ S.CSet a b → κ ≤ p → p - κ ∈ S.CSet a b := by
    intro p hp hpC hκp
    rcases gg_sub_prin hp hκp with e | e
    · rw [e]; exact hpC
    · rw [e]; exact CSet.zero_mem a b
  induction hx with
  | small h => exact fun _ => CSet.of_lt ((Ordinal.sub_le_self _ _).trans_lt h)
  | zero => exact fun h => absurd h (not_le.2 hκ.1)
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal (CSet.I_mem a b n)
  | inaccW => exact prin (SC_Iw (S := S)).isPrincipal (CSet.Iw_mem a b)
  | @add x y _ hy ihx ihy =>
    intro h
    rcases le_or_gt κ x with hx' | hx'
    · have e : x + y - κ = (x - κ) + y := by
        refine Ordinal.sub_eq_of_add_eq ?_
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le hx']
      rw [e]; exact CSet.add_mem (ihx hx') hy
    · have hy' : κ ≤ y := by
        by_contra hy'
        push Not at hy'
        exact absurd h (not_le.2 (hκ.isPrincipal hx' hy'))
      have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
      have habs : x + κ = κ := Ordinal.add_of_omega0_opow_le (b := κ) (by rw [hE]; exact hx') (by rw [hE])
      have hxy : x + y = y := by
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hy']
        rw [← add_assoc, habs, Ordinal.add_sub_cancel_of_le hy']
      rw [hxy]; exact ihy hy'
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (CSet.phi_mem hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact fun h => absurd h (not_le.2 hκ.1)
    · exact prin (Om_isPrincipal hx0) (CSet.Om_mem hx)
  | @coll π e hπ hπC heC _ _ => exact prin (SC_psi hπ e.1).isPrincipal (CSet.psi_mem e.2 hπ hπC heC)

/-! ## Division by `κ` in the closures -/

/-- **`Cl(a, b)` is closed under `x ↦ x/κ`.** -/
theorem ldDivK_mem {κ a b x : Ordinal.{0}} (hκ : SC κ) (hx : x ∈ S.CSet a b) : x / κ ∈ S.CSet a b := by
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  -- a principal `p` with `ω^p = p`
  have fix : ∀ {p : Ordinal.{0}}, ω ^ p = p → p ∈ S.CSet a b → p / κ ∈ S.CSet a b := by
    intro p hpE hpC
    have hp : IsPrincipal (· + ·) p := by rw [← hpE]; exact isPrincipal_add_omega0_opow _
    rcases lt_or_ge p κ with h | h
    · rw [Ordinal.div_eq_zero_of_lt h]; exact CSet.zero_mem a b
    · obtain ⟨e, -, -⟩ := ldDivK_prin hκ hp h
      have hlog : log ω p = p := by conv_lhs => rw [← hpE]; exact log_opow one_lt_omega0 _
      rw [e, hlog]
      rcases gg_sub_prin hp h with e2 | e2
      · rw [e2, hpE]; exact hpC
      · rw [e2, opow_zero]; exact CSet.one_mem a b
  induction hx with
  | small h => exact CSet.of_lt ((Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ hκ.1)).trans_lt h)
  | zero => rw [Ordinal.zero_div]; exact CSet.zero_mem a b
  | inacc n => exact fix (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (CSet.I_mem a b n)
  | inaccW => exact fix (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (CSet.Iw_mem a b)
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y κ with h | h
    · rw [ldDivK_add_lt hκ x h]; exact ihx
    · rw [ldDivK_add_ge hκ x h]; exact CSet.add_mem ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      rcases lt_or_ge (ω ^ y) κ with h | h
      · rw [Ordinal.div_eq_zero_of_lt h]; exact CSet.zero_mem a b
      · obtain ⟨e, hlog, -⟩ := ldDivK_prin hκ (isPrincipal_add_omega0_opow y) h
        rw [log_opow one_lt_omega0] at e hlog
        rw [e]
        have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (ldSubK_mem hκ hy hlog)
        rwa [veblen_zero_apply] at this
    · exact fix (gg_veblen_eps hx0) (CSet.phi_mem hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_div]; exact CSet.zero_mem a b
    · exact fix (Low.opow_eq_self_of_SC (SC_Om hx0)) (CSet.Om_mem hx)
  | @coll π e hπ hπC heC _ _ =>
    exact fix (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (CSet.psi_mem e.2 hπ hπC heC)

/-! ## Multiplication by `κ` in the closures -/

/-- `κ·x ∈ Cl(a, b)` for every `x < b`, when `κ ∈ Cl(a, b)`. -/
theorem ldMulK_small {κ a b : Ordinal.{0}} (hκ : SC κ) (hκC : κ ∈ S.CSet a b) :
    ∀ x, x < b → κ * x ∈ S.CSet a b := by
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [mul_zero]; exact CSet.zero_mem a b
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hxlt : x < ω ^ log ω x * ω := by
    rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  have hrx : x - ω ^ log ω x < x := by
    refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
    have h' : ω ^ log ω x + x = x := by
      calc ω ^ log ω x + x = ω ^ log ω x + (x - ω ^ log ω x) := by rw [e]
        _ = x := hdec
    have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
    exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
  have hlog : log ω x < b := (log_le_self ω x).trans_lt hx
  have e : κ * x = ω ^ (κ + log ω x) + κ * (x - ω ^ log ω x) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add, hE]
  rw [e]
  refine CSet.add_mem ?_ (IH _ hrx (hrx.trans hx))
  have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.add_mem hκC (CSet.of_lt hlog))
  rwa [veblen_zero_apply] at this

/-- **`κ·x ∈ Cl(a, b)` for `x ∈ Cl(a, b)`**, when `κ ∈ Cl(a, b)`. -/
theorem ldMulK_mem {κ a b x : Ordinal.{0}} (hκ : SC κ) (hκC : κ ∈ S.CSet a b) (hx : x ∈ S.CSet a b) :
    κ * x ∈ S.CSet a b := by
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  have fix : ∀ {p : Ordinal.{0}}, ω ^ p = p → p ∈ S.CSet a b → κ * p ∈ S.CSet a b := by
    intro p hpE hpC
    have e : κ * p = ω ^ (κ + p) := by rw [opow_add, hE, hpE]
    rw [e]
    have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.add_mem hκC hpC)
    rwa [veblen_zero_apply] at this
  induction hx with
  | small h => exact ldMulK_small hκ hκC _ h
  | zero => rw [mul_zero]; exact CSet.zero_mem a b
  | inacc n => exact fix (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (CSet.I_mem a b n)
  | inaccW => exact fix (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (CSet.Iw_mem a b)
  | add _ _ ihx ihy => rw [mul_add]; exact CSet.add_mem ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      have e : κ * ω ^ y = ω ^ (κ + y) := by rw [opow_add, hE]
      rw [e]
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.add_mem hκC hy)
      rwa [veblen_zero_apply] at this
    · exact fix (gg_veblen_eps hx0) (CSet.phi_mem hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, mul_zero]; exact CSet.zero_mem a b
    · exact fix (Low.opow_eq_self_of_SC (SC_Om hx0)) (CSet.Om_mem hx)
  | @coll π e hπ hπC heC _ _ =>
    exact fix (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (CSet.psi_mem e.2 hπ hπC heC)

/-! ## `B_n(κ·x) = κ·B_n(x)` -/

/-- `B_n(ω^g) = ω^{B_n g}` on `MvD`. -/
theorem ldB_opow {n : ℕ} {g : Ordinal.{0}} (hg : MvD S g) :
    MvD S (ω ^ g) ∧ Bc.bcB S n (ω ^ g) = ω ^ Bc.bcB S n g := by
  by_cases hE : ω ^ g = g
  · have h := mwB_fix (S := S) (k := n) (m := 0) hg (by rw [Nat.cast_zero, veblen_zero_apply]; exact hE)
    rw [Nat.cast_zero, veblen_zero_apply] at h
    rw [hE]; exact ⟨hg, h.symm⟩
  · exact mvB_opow hg hE

/-- **`B_n(κ·x) = κ·B_n(x)`** for `B_n κ = κ` and every `x < κ` in a class `P ⊆ MvD` closed under `log` and the
tail. -/
theorem ldB_mulK {n : ℕ} {κ : Ordinal.{0}} (hκ : SC κ) (hDκ : MvD S κ) (hBκ : Bc.bcB S n κ = κ)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPκ : ∀ x, P x → x < κ) :
    ∀ x, P x → MvD S (κ * x) ∧ Bc.bcB S n (κ * x) = κ * Bc.bcB S n x := by
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hDx := hPD x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨by rw [mul_zero]; exact hDx, by rw [mul_zero, Bc.bcB_zero, mul_zero]⟩
  obtain ⟨hPg, hPr⟩ := hPdec x hx hx0
  set g := log ω x with hg
  have hlead : ω ^ g ≤ x := opow_log_le_self ω hx0
  have hxlt : x < ω ^ g * ω := by
    rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
  have hdec : ω ^ g + (x - ω ^ g) = x := Ordinal.add_sub_cancel_of_le hlead
  have hrx : x - ω ^ g < x := by
    refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
    have h' : ω ^ g + x = x := by
      calc ω ^ g + x = ω ^ g + (x - ω ^ g) := by rw [e]
        _ = x := hdec
    have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
    exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
  have hDg := hPD _ hPg
  have hDr := hPD _ hPr
  obtain ⟨hDκr, hBκr⟩ := IH _ hrx hPr
  obtain ⟨hDog, hBog⟩ := ldB_opow (n := n) hDg
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDog hDr
  rw [hdec] at hBx
  -- the lead term `κ·ω^g = ω^{κ+g}`
  obtain ⟨hDκg, hBκg⟩ := mvB_add (k := n) hDκ hDg
  rw [hBκ] at hBκg
  have hlt := hPκ x hx
  rcases eq_or_ne g 0 with hg0 | hg0
  · -- `κ·1 = κ`
    have hl : κ * ω ^ g = κ := by rw [hg0, opow_zero, mul_one]
    have e : κ * x = κ + κ * (x - ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, hl]
    have hB1 : Bc.bcB S n (ω ^ g) = 1 := by rw [hg0, opow_zero, mwB_one]
    have hBx' : Bc.bcB S n x = 1 + Bc.bcB S n (x - ω ^ g) := by rw [hBx, hB1]
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDκ hDκr
    rw [e, hBx', mul_add, mul_one]
    exact ⟨hDs, by rw [hBs, hBκ, hBκr]⟩
  · have hne : ω ^ (κ + g) ≠ κ + g := by
      intro h
      have h1 : κ + g < κ * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
        exact (add_lt_add_iff_left κ).2 ((log_le_self ω x).trans_lt hlt)
      have h2 : κ * 2 ≤ ω ^ (κ + g) := by
        rw [opow_add, hE]
        refine mul_le_mul_right ?_ κ
        have h3 : (ω : Ordinal.{0}) ≤ ω ^ g := by
          have := (opow_le_opow_iff_right one_lt_omega0).2 (Order.one_le_iff_ne_zero.2 hg0)
          rwa [opow_one] at this
        exact (natCast_lt_omega0 2).le.trans h3
      rw [h] at h2
      exact absurd h1 (not_lt.2 h2)
    obtain ⟨hDl, hBl⟩ := mvB_opow (k := n) hDκg hne
    have e : κ * x = ω ^ (κ + g) + κ * (x - ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, opow_add, hE]
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDl hDκr
    rw [e, hBx, hBog, mul_add]
    refine ⟨hDs, ?_⟩
    rw [hBs, hBl, hBκg, hBκr, opow_add, hE]

end Googology.Trans.PoR.InaccPsi.R2.Ld
