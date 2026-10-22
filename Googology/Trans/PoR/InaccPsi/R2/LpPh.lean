import Googology.Trans.PoR.InaccPsi.R2.LxZF
import Googology.Trans.PoR.InaccPsi.R2.LvGPh

/-!
# The reading of the codes with the atom `Γ_{Ω₁+1}` commutes with `φ`

`R2.PhVeb` proves the φ-law for the codes below `Γ_{Ω₁+1}` (`GgCl`).  Here the same for the codes `LgCl` of
`R2.LgCl` (the atom `Γ_{Ω₁+1} = ψ_{Ω₂}(0)`, below `Γ' = Γ_{Ω₁+2}`) and the reading `Θ' = lgTh`:

* `lpDec` (**the Veblen decomposition of a code**: `φ(a, b)` a code with `b < φ(a, b)` gives codes `a`, `b`; the new
  case is the atom: `φ(a, b) = Γ_{Ω₁+1}`, `b < Γ_{Ω₁+1}` forces `a = Γ_{Ω₁+1}`, `b = 0`);
* `lpTh_inj`, `lpTh_zero`, **`lpTh_phi` (THE φ-LAW: `Θ'_y(φ(a, b)) = φ(Θ'_y(a), Θ'_y(b))` for codes `a`, `b` over a
  strongly critical `y`)**, `lpTh_lt_Om1`, `lpTh_nat`, `lpTh_add_nat`, `lpTh_ne_zero`;
* `lpSplit` (a code is `a + n` with `ω ∣ a`, `a` a code, and `ω ∣ Θ'_y(a)`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph

variable {Z : Ordinal.{0}}

/-- **The Veblen decomposition of a code**: `x = φ(a, b)` a code with `b < x` gives codes `a`, `b`. -/
theorem lpDec (hZ : 0 < Z) {x : Ordinal.{0}} (hx : LgCl Z x) :
    ∀ a b, veblen a b = x → b < x → LgCl Z a ∧ LgCl Z b := by
  induction hx with
  | @small x h =>
    intro a b e hb
    exact ⟨LgCl.small ((e ▸ left_le_veblen a b).trans_lt h), LgCl.small (hb.trans h)⟩
  | om =>
    intro a b e hb
    have ha : a = Om 1 := by
      rcases lt_trichotomy a (Om 1) with h | h | h
      · exact absurd e (ph_SC_Om1.2 a h b hb).ne
      · exact h
      · exact absurd (e ▸ left_le_veblen a b) (not_le.2 h)
    subst ha
    have hb0 : b = 0 := by
      have h1 : veblen (Om 1) 0 = veblen (Om 1) b := by rw [ph_SC_Om1.veblen_zero, e]
      exact (veblen_inj.1 h1).symm
    exact ⟨LgCl.om, hb0 ▸ LgCl.zero hZ⟩
  | gam =>
    intro a b e hb
    have hS := ggGam_spec.1
    have ha : a = ggGam := by
      rcases lt_trichotomy a ggGam with h | h | h
      · exact absurd e (hS.2 a h b hb).ne
      · exact h
      · exact absurd (e ▸ left_le_veblen a b) (not_le.2 h)
    subst ha
    have hb0 : b = 0 := by
      have h1 : veblen ggGam 0 = veblen ggGam b := by rw [hS.veblen_zero, e]
      exact (veblen_inj.1 h1).symm
    exact ⟨LgCl.gam, hb0 ▸ LgCl.zero hZ⟩
  | @add u v hu hv ihu ihv =>
    intro a b e hb
    have hp : IsPrincipal (· + ·) (u + v) := e ▸ ph_veblen_prin a b
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at e hb; exact ihu a b e hb
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hp hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at e hb
      exact ihv a b e hb
  | @phi a' b' ha' hb' _ ihb =>
    intro a b e hb
    rcases veblen_eq_veblen_iff.1 e with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h1, h2]; exact ⟨ha', hb'⟩
    · rw [h2] at hb; exact absurd hb (lt_irrefl _)
    · exact ihb a b h2 (by rw [← h2, e]; exact hb)

variable {y : Ordinal.{0}}

theorem lpTh_zero : lgTh y 0 = 0 := lgTh_small zero_le

/-- `Θ_y` is injective on codes. -/
theorem lpTh_inj {u v : Ordinal.{0}} (hu : LgCl y u) (hv : LgCl y v) (h : lgTh y u = lgTh y v) : u = v := by
  rcases lt_trichotomy u v with h' | h' | h'
  · exact absurd h (lgTh_lt hu h').ne
  · exact h'
  · exact absurd h (lgTh_lt hv h').ne'

/-- **THE φ-LAW**: `Θ_y(φ(a, b)) = φ(Θ_y(a), Θ_y(b))` for codes `a`, `b` over a strongly critical `y`. -/
theorem lpTh_phi (hy : SC y) :
    ∀ a, LgCl y a → ∀ b, LgCl y b → lgTh y (veblen a b) = veblen (lgTh y a) (lgTh y b) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IHa =>
  intro ha b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hb
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [lpTh_zero, veblen_zero_apply, veblen_zero_apply, lgTh_opow hy hb]
  have hx : LgCl y (veblen a b) := LgCl.phi ha hb
  have hfa0 : lgTh y a ≠ 0 := by
    have := lgTh_lt (LgCl.zero hy.1) (pos_iff_ne_zero.2 ha0)
    rw [lpTh_zero] at this; exact this.ne'
  -- `Θ_y(φ(a, b))` is a common fixed point of the `φ(α, ·)`, `α < Θ_y(a)`
  have hfix : ∀ α < lgTh y a, veblen α (lgTh y (veblen a b)) = lgTh y (veblen a b) := by
    intro α hα
    obtain ⟨a', ha', ha'a, rfl⟩ := lgTh_onto hα
    rw [← IHa a' ha'a ha' (veblen a b) hx, veblen_veblen_of_lt ha'a]
  obtain ⟨β, hβ⟩ := (mem_range_veblen hfa0).2 hfix
  have hge : lgTh y b ≤ β := by
    refine le_of_forall_lt fun β' hβ' => ?_
    obtain ⟨b', hb', hb'b, rfl⟩ := lgTh_onto hβ'
    have h1 : lgTh y (veblen a b') < lgTh y (veblen a b) :=
      lgTh_lt (LgCl.phi ha hb') (veblen_lt_veblen_iff_right.2 hb'b)
    rw [IHb b' hb'b hb', ← hβ] at h1
    exact veblen_lt_veblen_iff_right.1 h1
  have hle : β ≤ lgTh y b := by
    by_contra hlt
    push Not at hlt
    have h1 : veblen (lgTh y a) (lgTh y b) < lgTh y (veblen a b) := by
      rw [← hβ]; exact veblen_lt_veblen_iff_right.2 hlt
    obtain ⟨w, hw, hwx, hwv⟩ := lgTh_onto h1
    have hwE : ω ^ w = w := by
      by_contra hne
      have hlt' : w < ω ^ w := lt_of_le_of_ne (right_le_opow w one_lt_omega0) (Ne.symm hne)
      have h2 := lgTh_lt hw hlt'
      rw [lgTh_opow hy hw, hwv, gg_veblen_eps hfa0] at h2
      exact lt_irrefl _ h2
    have hdec : veblen (invVeblen₁ w) (invVeblen₂ w) = w := by
      rw [veblen_invVeblen₁_invVeblen₂, hwE]
    have hb1 : invVeblen₂ w < w := by
      have := invVeblen₂_lt w; rwa [hwE] at this
    obtain ⟨ha1, hb1c⟩ := lpDec hy.1 hw _ _ hdec hb1
    rcases lt_trichotomy (invVeblen₁ w) a with h | h | h
    · have e1 : lgTh y (veblen (invVeblen₁ w) w) = lgTh y w := by
        rw [IHa _ h ha1 w hw, hwv, veblen_veblen_of_lt (lgTh_lt ha1 h)]
      have hgt : w < veblen (invVeblen₁ w) w := by
        have := (veblen_lt_veblen_iff_right (o := invVeblen₁ w)).2 hb1
        rwa [hdec] at this
      have h3 := lgTh_lt hw hgt
      rw [e1] at h3
      exact lt_irrefl _ h3
    · rw [h] at hdec
      have hb1b : invVeblen₂ w < b := by
        rw [← hdec] at hwx; exact veblen_lt_veblen_iff_right.1 hwx
      have h3 := IHb _ hb1b hb1c
      rw [hdec, hwv] at h3
      have h4 : veblen (lgTh y a) (lgTh y (invVeblen₂ w)) < veblen (lgTh y a) (lgTh y b) :=
        veblen_lt_veblen_iff_right.2 (lgTh_lt hb1c hb1b)
      rw [← h3] at h4
      exact lt_irrefl _ h4
    · have e1 : veblen a w = w := by
        have := veblen_veblen_of_lt h (invVeblen₂ w); rwa [hdec] at this
      have hwb : w < b := by
        rw [← e1] at hwx; exact veblen_lt_veblen_iff_right.1 hwx
      have h3 := lgTh_lt hw hwb
      rw [hwv] at h3
      exact absurd (right_le_veblen _ _) (not_le.2 h3)
  rw [← hβ, le_antisymm hle hge]

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem lpTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : LgCl y c) : lgTh y c < Om 1 := by
  induction hc with
  | small h => rw [lgTh_small h.le]; exact h.trans hy1
  | om => rw [lgTh_Om1 hy hy1]; exact hy1
  | gam =>
    have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
    rw [lgTh_Gam hy hy1, ← ph_Om1_eq]; exact (lgG_facts (gg_SC_eps hy) hy1').2.2.1
  | @add u v hu _ ihu ihv => rw [lgTh_add hy hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [lpTh_phi hy a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

theorem lpTh_nat (hy : SC y) (n : ℕ) : lgTh y (n : Ordinal.{0}) = n := lgTh_small (ph_nat_lt hy n).le

theorem lpTh_add_nat (hy : SC y) {u : Ordinal.{0}} (hu : LgCl y u) (n : ℕ) :
    lgTh y (u + n) = lgTh y u + n := by rw [lgTh_add hy hu, lpTh_nat hy]

theorem lpTh_ne_zero (hy : SC y) {c : Ordinal.{0}} (h0 : c ≠ 0) : lgTh y c ≠ 0 := by
  have := lgTh_lt (LgCl.zero hy.1) (pos_iff_ne_zero.2 h0) (d := c)
  rw [lpTh_zero] at this; exact this.ne'

/-! ## A code is `a + n` with `ω ∣ a` -/

/-- **A code is `a + n`** with `a` a code, `ω ∣ a`, `n < ω`, and `ω ∣ Θ_y(a)` at every strongly critical
`y ≥ Z` below `Ω₁`. -/
theorem lpSplit (hZ : SC Z) : ∀ b, LgCl Z b → ∃ a : Ordinal.{0}, ∃ n : ℕ, LgCl Z a ∧ ω ∣ a ∧ b = a + n ∧
    ∀ y, SC y → y < Om 1 → Z ≤ y → ω ∣ lgTh y a := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases lt_or_ge b ω with hbω | hbω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hbω
    exact ⟨0, n, LgCl.zero hZ.1, dvd_zero _, by rw [zero_add], fun y _ _ _ => by
      rw [lpTh_zero]; exact dvd_zero _⟩
  have hb0 : b ≠ 0 := (omega0_pos.trans_le hbω).ne'
  have hL : log ω b ≠ 0 := by
    intro h
    have := lt_opow_succ_log_self one_lt_omega0 b
    rw [h, Order.succ_eq_add_one, zero_add, opow_one] at this
    exact absurd hbω (not_le.2 this)
  obtain ⟨hsub, hlog⟩ := lgDec hZ b hb
  have hw : LgCl Z (ω ^ log ω b) := LgCl.opow hZ.1 hlog
  have hwb : ω ^ log ω b ≤ b := opow_log_le_self ω hb0
  have hr := hsub _ hw hwb
  have hbr : ω ^ log ω b + (b - ω ^ log ω b) = b := Ordinal.add_sub_cancel_of_le hwb
  rcases eq_or_ne (b - ω ^ log ω b) 0 with h0 | h0
  · -- `b = ω^L`
    rw [h0, add_zero] at hbr
    refine ⟨b, 0, hb, hbr ▸ ph_omega_dvd_opow hL, by rw [Nat.cast_zero, add_zero], fun y hy hy1 hZy => ?_⟩
    rw [← hbr, lgTh_opow hy (hlog.mono hZy)]
    exact ph_omega_dvd_opow (lpTh_ne_zero hy hL)
  · have hrb : b - ω ^ log ω b < b := by
      rcases (Ordinal.sub_le_self b (ω ^ log ω b)).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 : ω ^ log ω b + b = b := by conv_rhs => rw [← hbr]
                                            rw [h]
        have h2 := add_eq_right_iff_mul_omega0_le.1 h1
        rw [← opow_succ] at h2
        exact absurd (lt_opow_succ_log_self one_lt_omega0 b) (not_lt.2 h2)
    obtain ⟨a', n, ha', hd', he', hθ'⟩ := IH _ hrb (hr.mono le_rfl)
    refine ⟨ω ^ log ω b + a', n, LgCl.add hw ha', dvd_add (ph_omega_dvd_opow hL) hd', ?_,
      fun y hy hy1 hZy => ?_⟩
    · rw [add_assoc, ← he', hbr]
    · rw [lgTh_add hy (hw.mono hZy), lgTh_opow hy (hlog.mono hZy)]
      exact dvd_add (ph_omega_dvd_opow (lpTh_ne_zero hy hL)) (hθ' y hy hy1 hZy)

end Googology.Trans.PoR.InaccPsi.R2.Lp
