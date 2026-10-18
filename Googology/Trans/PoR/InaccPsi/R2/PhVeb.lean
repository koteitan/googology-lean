import Googology.Trans.PoR.InaccPsi.R2.GgOtp

/-!
# The reading over `y` commutes with `φ`

`GgCl y` are the codes over `y` (generated from the ordinals below `y` and `Ω₁` by `+` and `φ = veblen`),
`Θ_y = ggTh y` the reading over `y` (the order type of the codes below the argument).

* `phDec` (**the Veblen decomposition of a code**): if `x = φ(a, b)` is a code and `b < x`, then `a` and `b` are
  codes;
* `phTh_inj` (`Θ_y` is injective on codes), `phTh_zero`;
* `phTh_phi` (**THE φ-LAW**): for a strongly critical `y` and codes `a`, `b` over `y`,
  `Θ_y(φ(a, b)) = φ(Θ_y(a), Θ_y(b))`.  Induction on `a`, inside it on `b`: `Θ_y(φ(a, b))` is a common fixed point
  of the `φ(α, ·)`, `α < Θ_y(a)` (every such `α` is `Θ_y(a')` for a code `a' < a`), so it is `φ(Θ_y(a), β)`;
  `β ≥ Θ_y(b)` by the inner induction, and `β > Θ_y(b)` would give a code `w < φ(a, b)` with
  `Θ_y(w) = φ(Θ_y(a), Θ_y(b))`, an `ε`-number whose Veblen decomposition `w = φ(a₁, b₁)` (`phDec`) contradicts
  each of `a₁ < a`, `a₁ = a`, `a₁ > a`;
* `phTh_lt_Om1` (every reading of a code over `y` is below `Ω₁`), `phTh_add_nat`, `phTh_nat`;
* `phSplit` (**a code is `a + n`** with `ω ∣ a`, `a` a code, `n < ω`, and `ω ∣ Θ_y(a)` at every strongly critical
  `y ≥ Z` below `Ω₁`), `phSplit_uniq` (the decomposition `a + n`, `ω ∣ a`, is unique).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {Z : Ordinal.{0}}

theorem ph_SC_Om1 : SC (Om (1 : Ordinal.{0})) := SC_Om one_ne_zero

theorem ph_veblen_prin (a b : Ordinal.{0}) : IsPrincipal (· + ·) (veblen a b) := by
  obtain ⟨c, hc⟩ := veblen_mem_range_opow a b
  rw [← hc]; exact isPrincipal_add_omega0_opow c

/-- **The Veblen decomposition of a code**: `x = φ(a, b)` a code with `b < x` gives codes `a`, `b`. -/
theorem phDec (hZ : 0 < Z) {x : Ordinal.{0}} (hx : GgCl Z x) :
    ∀ a b, veblen a b = x → b < x → GgCl Z a ∧ GgCl Z b := by
  induction hx with
  | @small x h =>
    intro a b e hb
    exact ⟨GgCl.small ((e ▸ left_le_veblen a b).trans_lt h), GgCl.small (hb.trans h)⟩
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
    exact ⟨GgCl.om, hb0 ▸ GgCl.zero hZ⟩
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

theorem phTh_zero : ggTh y 0 = 0 := ggTh_small zero_le

/-- `Θ_y` is injective on codes. -/
theorem phTh_inj {u v : Ordinal.{0}} (hu : GgCl y u) (hv : GgCl y v) (h : ggTh y u = ggTh y v) : u = v := by
  rcases lt_trichotomy u v with h' | h' | h'
  · exact absurd h (ggTh_lt hu h').ne
  · exact h'
  · exact absurd h (ggTh_lt hv h').ne'

/-- **THE φ-LAW**: `Θ_y(φ(a, b)) = φ(Θ_y(a), Θ_y(b))` for codes `a`, `b` over a strongly critical `y`. -/
theorem phTh_phi (hy : SC y) :
    ∀ a, GgCl y a → ∀ b, GgCl y b → ggTh y (veblen a b) = veblen (ggTh y a) (ggTh y b) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IHa =>
  intro ha b
  induction b using WellFoundedLT.induction with
  | ind b IHb =>
  intro hb
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [phTh_zero, veblen_zero_apply, veblen_zero_apply, ggTh_opow hy hb]
  have hx : GgCl y (veblen a b) := GgCl.phi ha hb
  have hfa0 : ggTh y a ≠ 0 := by
    have := ggTh_lt (GgCl.zero hy.1) (pos_iff_ne_zero.2 ha0)
    rw [phTh_zero] at this; exact this.ne'
  -- `Θ_y(φ(a, b))` is a common fixed point of the `φ(α, ·)`, `α < Θ_y(a)`
  have hfix : ∀ α < ggTh y a, veblen α (ggTh y (veblen a b)) = ggTh y (veblen a b) := by
    intro α hα
    obtain ⟨a', ha', ha'a, rfl⟩ := ggTh_onto hα
    rw [← IHa a' ha'a ha' (veblen a b) hx, veblen_veblen_of_lt ha'a]
  obtain ⟨β, hβ⟩ := (mem_range_veblen hfa0).2 hfix
  have hge : ggTh y b ≤ β := by
    refine le_of_forall_lt fun β' hβ' => ?_
    obtain ⟨b', hb', hb'b, rfl⟩ := ggTh_onto hβ'
    have h1 : ggTh y (veblen a b') < ggTh y (veblen a b) :=
      ggTh_lt (GgCl.phi ha hb') (veblen_lt_veblen_iff_right.2 hb'b)
    rw [IHb b' hb'b hb', ← hβ] at h1
    exact veblen_lt_veblen_iff_right.1 h1
  have hle : β ≤ ggTh y b := by
    by_contra hlt
    push Not at hlt
    have h1 : veblen (ggTh y a) (ggTh y b) < ggTh y (veblen a b) := by
      rw [← hβ]; exact veblen_lt_veblen_iff_right.2 hlt
    obtain ⟨w, hw, hwx, hwv⟩ := ggTh_onto h1
    have hwE : ω ^ w = w := by
      by_contra hne
      have hlt' : w < ω ^ w := lt_of_le_of_ne (right_le_opow w one_lt_omega0) (Ne.symm hne)
      have h2 := ggTh_lt hw hlt'
      rw [ggTh_opow hy hw, hwv, gg_veblen_eps hfa0] at h2
      exact lt_irrefl _ h2
    have hdec : veblen (invVeblen₁ w) (invVeblen₂ w) = w := by
      rw [veblen_invVeblen₁_invVeblen₂, hwE]
    have hb1 : invVeblen₂ w < w := by
      have := invVeblen₂_lt w; rwa [hwE] at this
    obtain ⟨ha1, hb1c⟩ := phDec hy.1 hw _ _ hdec hb1
    rcases lt_trichotomy (invVeblen₁ w) a with h | h | h
    · have e1 : ggTh y (veblen (invVeblen₁ w) w) = ggTh y w := by
        rw [IHa _ h ha1 w hw, hwv, veblen_veblen_of_lt (ggTh_lt ha1 h)]
      have hgt : w < veblen (invVeblen₁ w) w := by
        have := (veblen_lt_veblen_iff_right (o := invVeblen₁ w)).2 hb1
        rwa [hdec] at this
      have h3 := ggTh_lt hw hgt
      rw [e1] at h3
      exact lt_irrefl _ h3
    · rw [h] at hdec
      have hb1b : invVeblen₂ w < b := by
        rw [← hdec] at hwx; exact veblen_lt_veblen_iff_right.1 hwx
      have h3 := IHb _ hb1b hb1c
      rw [hdec, hwv] at h3
      have h4 : veblen (ggTh y a) (ggTh y (invVeblen₂ w)) < veblen (ggTh y a) (ggTh y b) :=
        veblen_lt_veblen_iff_right.2 (ggTh_lt hb1c hb1b)
      rw [← h3] at h4
      exact lt_irrefl _ h4
    · have e1 : veblen a w = w := by
        have := veblen_veblen_of_lt h (invVeblen₂ w); rwa [hdec] at this
      have hwb : w < b := by
        rw [← e1] at hwx; exact veblen_lt_veblen_iff_right.1 hwx
      have h3 := ggTh_lt hw hwb
      rw [hwv] at h3
      exact absurd (right_le_veblen _ _) (not_le.2 h3)
  rw [← hβ, le_antisymm hle hge]

/-- Every reading of a code over `y` is below `Ω₁`. -/
theorem phTh_lt_Om1 (hy : SC y) (hy1 : y < Om 1) {c : Ordinal.{0}} (hc : GgCl y c) : ggTh y c < Om 1 := by
  induction hc with
  | small h => rw [ggTh_small h.le]; exact h.trans hy1
  | om => rw [ggTh_Om1 hy hy1]; exact hy1
  | @add u v hu _ ihu ihv => rw [ggTh_add hy hu]; exact ph_SC_Om1.isPrincipal ihu ihv
  | @phi a b ha hb iha ihb => rw [phTh_phi hy a ha b hb]; exact ph_SC_Om1.2 _ iha _ ihb

theorem ph_nat_lt (hy : SC y) (n : ℕ) : (n : Ordinal.{0}) < y :=
  (natCast_lt_omega0 n).trans_le (by
    have := hy.2 0 hy.1 1 (gg_one_lt_of_SC hy)
    rw [veblen_zero_apply, opow_one] at this; exact this.le)

theorem phTh_nat (hy : SC y) (n : ℕ) : ggTh y (n : Ordinal.{0}) = n := ggTh_small (ph_nat_lt hy n).le

theorem phTh_add_nat (hy : SC y) {u : Ordinal.{0}} (hu : GgCl y u) (n : ℕ) :
    ggTh y (u + n) = ggTh y u + n := by rw [ggTh_add hy hu, phTh_nat hy]

theorem phTh_ne_zero (hy : SC y) {c : Ordinal.{0}} (h0 : c ≠ 0) : ggTh y c ≠ 0 := by
  have := ggTh_lt (GgCl.zero hy.1) (pos_iff_ne_zero.2 h0) (d := c)
  rw [phTh_zero] at this; exact this.ne'

/-! ## A code is `a + n` with `ω ∣ a` -/

theorem ph_omega_dvd_opow {L : Ordinal.{0}} (hL : L ≠ 0) : ω ∣ ω ^ L := by
  have := opow_dvd_opow ω (Order.one_le_iff_ne_zero.2 hL)
  rwa [opow_one] at this

/-- **A code is `a + n`** with `a` a code, `ω ∣ a`, `n < ω`, and `ω ∣ Θ_y(a)` at every strongly critical
`y ≥ Z` below `Ω₁`. -/
theorem phSplit (hZ : SC Z) : ∀ b, GgCl Z b → ∃ a : Ordinal.{0}, ∃ n : ℕ, GgCl Z a ∧ ω ∣ a ∧ b = a + n ∧
    ∀ y, SC y → y < Om 1 → Z ≤ y → ω ∣ ggTh y a := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases lt_or_ge b ω with hbω | hbω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hbω
    exact ⟨0, n, GgCl.zero hZ.1, dvd_zero _, by rw [zero_add], fun y _ _ _ => by
      rw [phTh_zero]; exact dvd_zero _⟩
  have hb0 : b ≠ 0 := (omega0_pos.trans_le hbω).ne'
  have hL : log ω b ≠ 0 := by
    intro h
    have := lt_opow_succ_log_self one_lt_omega0 b
    rw [h, Order.succ_eq_add_one, zero_add, opow_one] at this
    exact absurd hbω (not_le.2 this)
  obtain ⟨hsub, hlog⟩ := ggDec hZ b hb
  have hw : GgCl Z (ω ^ log ω b) := GgCl.opow hZ.1 hlog
  have hwb : ω ^ log ω b ≤ b := opow_log_le_self ω hb0
  have hr := hsub _ hw hwb
  have hbr : ω ^ log ω b + (b - ω ^ log ω b) = b := Ordinal.add_sub_cancel_of_le hwb
  rcases eq_or_ne (b - ω ^ log ω b) 0 with h0 | h0
  · -- `b = ω^L`
    rw [h0, add_zero] at hbr
    refine ⟨b, 0, hb, hbr ▸ ph_omega_dvd_opow hL, by rw [Nat.cast_zero, add_zero], fun y hy hy1 hZy => ?_⟩
    rw [← hbr, ggTh_opow hy (hlog.mono hZy)]
    exact ph_omega_dvd_opow (phTh_ne_zero hy hL)
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
    refine ⟨ω ^ log ω b + a', n, GgCl.add hw ha', dvd_add (ph_omega_dvd_opow hL) hd', ?_,
      fun y hy hy1 hZy => ?_⟩
    · rw [add_assoc, ← he', hbr]
    · rw [ggTh_add hy (hw.mono hZy), ggTh_opow hy (hlog.mono hZy)]
      exact dvd_add (ph_omega_dvd_opow (phTh_ne_zero hy hL)) (hθ' y hy hy1 hZy)

/-- The decomposition `a + n` with `ω ∣ a` is unique. -/
theorem phSplit_uniq {a p : Ordinal.{0}} {n m : ℕ} (ha : ω ∣ a) (hp : ω ∣ p) (h : a + n = p + m) :
    a = p ∧ n = m := by
  have key : ∀ {a p : Ordinal.{0}} {n m : ℕ}, ω ∣ a → ω ∣ p → a < p → a + n < p + m := by
    intro a p n m ha hp hlt
    obtain ⟨q, rfl⟩ := ha
    obtain ⟨q', rfl⟩ := hp
    have hq : q < q' := (mul_lt_mul_iff_right₀ omega0_pos).1 hlt
    calc ω * q + n < ω * q + ω := (add_lt_add_iff_left _).2 (natCast_lt_omega0 n)
      _ = ω * (q + 1) := by rw [mul_add_one]
      _ ≤ ω * q' := by gcongr; exact Order.add_one_le_of_lt hq
      _ ≤ ω * q' + m := le_self_add
  rcases lt_trichotomy a p with h' | h' | h'
  · exact absurd h (key ha hp h').ne
  · subst h'
    exact ⟨rfl, by exact_mod_cast (add_left_cancel h)⟩
  · exact absurd h (key hp ha h').ne'

end Googology.Trans.PoR.InaccPsi.R2.Ph
