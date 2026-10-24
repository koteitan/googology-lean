import Googology.Trans.PoR.InaccPsi.R2.GkU0

/-!
# CODES BELOW `ζ_{Ω₁+1}`: gates of the parts, positivity, successors

* `guG_lt_Om1`, `gu_parts_g` (the parts of a code have their gates below every `x > ω` above the gate of the code);
* `guR_pos`, `gu_lead` (**`ε_{x+ν(x)} ≤ c(x)`**), `gu_succ_lt`;
* `guR_succ`, `guR_succ_all` (**`(b+1)(x) = b(x) + 1`**), `guG_succ`, `guG_le_succ`, `guG_le_succ_all`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

theorem guG_lt_Om1 : ∀ c, c < guB → guG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guG_low hcE]; exact gtc_lt_Om1 c hcE
  obtain ⟨-, -, -, hnB, hnc⟩ := guN_spec hcE hc
  obtain ⟨-, -, -, -, -, hkc, hrc, hdc⟩ := gu_parts hcE hc
  rw [guG_dec hcE hc]
  have hQ : ∀ a, a < c → guQ a < Om1 := fun a ha => (guQ_le a).trans_lt (IH a ha (ha.trans hc))
  exact max_lt (max_lt (hQ _ hnc) (hQ _ hkc)) (max_lt (hQ _ hdc) (IH _ hrc (hrc.trans hc)))

/-- **The parts have their gates below `x`** (`x > ω`) when the code has. -/
theorem gu_parts_g {x c : Ordinal.{0}} (hωx : ω < x) (h1 : gfE ≤ c) (h2 : c < guB) (hg : guG c < x) :
    guG (guN c) < x ∧ guG (log (guE c) c) < x ∧ guG (c / guE c ^ log (guE c) c) < x ∧
      guG (c % guE c ^ log (guE c) c) < x := by
  rw [guG_dec h1 h2] at hg
  exact ⟨guG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    guG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    guG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg)),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

theorem gu_parts_Q {x c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < guB) (hg : guG c < x) :
    guQ (guN c) < x ∧ guQ (log (guE c) c) < x ∧ guQ (c / guE c ^ log (guE c) c) < x ∧
      guG (c % guE c ^ log (guE c) c) < x := by
  rw [guG_dec h1 h2] at hg
  exact ⟨(le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg),
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hg),
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg)⟩

theorem guR_pos {x : Ordinal.{0}} (hx : InE x) : ∀ c, c ≠ 0 → c < guB → 0 < guR c x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc0 hc
  rcases lt_or_ge c gfE with hcE | hcE
  · rw [guR_low hcE]; exact rdc_pos hx hc0 hcE
  obtain ⟨-, hd0, -, -, -, -, -, hdc⟩ := gu_parts hcE hc
  rw [guR_dec hcE hc]
  exact lt_of_lt_of_le (mul_pos (opow_pos _ (guA_E _ _).pos) (IH _ hdc hd0 (hdc.trans hc))) le_self_add

theorem gu_one_le_N {x c : Ordinal.{0}} (hx : InE x) (h1 : gfE ≤ c) (h2 : c < guB) : 1 ≤ guR (guN c) x := by
  obtain ⟨hn1, -, -, hnB, -⟩ := guN_spec h1 h2
  exact one_le_iff_pos.2 (guR_pos hx _ (one_le_iff_ne_zero.1 hn1) hnB)

/-- **A code is read above its pseudo-base**: `ε_{x+ν(x)} ≤ c(x)`. -/
theorem gu_lead {x c : Ordinal.{0}} (hx : InE x) (h1 : gfE ≤ c) (h2 : c < guB) :
    guA x (guR (guN c) x) ^ guR (log (guE c) c) x * guR (c / guE c ^ log (guE c) c) x ≤ guR c x ∧
      guA x (guR (guN c) x) ≤ guR c x := by
  obtain ⟨hk, hd0, -, -, -, hkc, -, hdc⟩ := gu_parts h1 h2
  rw [guR_dec h1 h2]
  refine ⟨le_self_add, le_trans ?_ le_self_add⟩
  set B := guA x (guR (guN c) x)
  have hB := guA_E x (guR (guN c) x)
  calc B = B ^ (1 : Ordinal.{0}) * 1 := by rw [opow_one, mul_one]
    _ ≤ B ^ guR (log (guE c) c) x * 1 :=
        mul_le_mul_left (opow_le_opow_right hB.pos (one_le_iff_pos.2 (guR_pos hx _ hk (hkc.trans h2)))) _
    _ ≤ _ := mul_le_mul_right (one_le_iff_pos.2 (guR_pos hx _ hd0 (hdc.trans h2))) _

theorem gu_succ_lt {E k r : Ordinal.{0}} (hE : InE E) (hk : k ≠ 0) (hr : r < E ^ k) : r + 1 < E ^ k := by
  rw [gu_pow_eq hE] at hr ⊢
  have h1 : (1 : Ordinal.{0}) < ω ^ (E * k) := by
    rw [← opow_zero ω]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (mul_pos hE.pos (pos_iff_ne_zero.2 hk))
  exact isPrincipal_add_omega0_opow _ hr h1

/-- The successor of a code `b ≥ ε_{Ω₁+1}` in normal form: the rest goes up by one. -/
theorem gu_succ_nf {b : Ordinal.{0}} (h1 : gfE ≤ b) (h2 : b + 1 < guB) :
    b + 1 = evA Om1 (guN b) ^ log (guE b) b * (b / guE b ^ log (guE b) b) + (b % guE b ^ log (guE b) b + 1) ∧
      b % guE b ^ log (guE b) b + 1 < evA Om1 (guN b) ^ log (guE b) b ∧
      evA Om1 (guN b) ^ log (guE b) b * (b / guE b ^ log (guE b) b) + (b % guE b ^ log (guE b) b + 1) <
        evA Om1 (guN b + 1) := by
  have hbB : b < guB := (lt_add_one b).trans h2
  obtain ⟨-, -, hbN, -, -⟩ := guN_spec h1 hbB
  obtain ⟨hk, -, -, hr, hdec, -, -, -⟩ := gu_parts h1 hbB
  have e : b + 1 = evA Om1 (guN b) ^ log (guE b) b * (b / guE b ^ log (guE b) b) +
      (b % guE b ^ log (guE b) b + 1) := by
    rw [← add_assoc]; exact congrArg (· + 1) hdec.symm
  refine ⟨e, gu_succ_lt (guE_E b) hk hr, ?_⟩
  rw [← e]
  exact (ev_isSuccLimit_of_inE (evA_E _ _)).add_one_lt hbN

theorem guR_succ : ∀ b, b + 1 < guB → ∀ x : Ordinal.{0}, guR (b + 1) x = guR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 x
  have hbB : b < guB := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [guR_low hbE, guR_low (succ_lt_eW hbE), (rdc_succ b hbE x).1]
  obtain ⟨hn1, -, -, -, -⟩ := guN_spec hbE hbB
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gu_parts hbE hbB
  obtain ⟨e, hr1, hv⟩ := gu_succ_nf hbE hb1
  have hr1B : b % guE b ^ log (guE b) b + 1 < guB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, guR_cnf hn1 hk hd0 hdE hr1 hv (e ▸ hb1), IH _ hrb hr1B x, guR_dec hbE hbB x, add_assoc]

theorem guR_succ_all (b x : Ordinal.{0}) : guR (b + 1) x = guR b x + 1 := by
  rcases lt_or_ge (b + 1) guB with h | h
  · exact guR_succ b h x
  · have hb : guB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (guB_lim.add_one_lt hb) (not_lt.2 h)
    rw [guR_high h, guR_high hb]

theorem guG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, b + 1 < guB → guG b < Z → guG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hg
  have hbB : b < guB := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [guG_low hbE] at hg
    rw [guG_low (succ_lt_eW hbE)]
    exact (rdc_succ b hbE 0).2.2.trans_lt (hZ.add_one_lt hg)
  obtain ⟨hn1, -, -, -, -⟩ := guN_spec hbE hbB
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gu_parts hbE hbB
  obtain ⟨e, hr1, hv⟩ := gu_succ_nf hbE hb1
  have hr1B : b % guE b ^ log (guE b) b + 1 < guB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [guG_dec hbE hbB] at hg
  rw [e, guG_cnf hn1 hk hd0 hdE hr1 hv (e ▸ hb1)]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (IH _ hrb hr1B ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))

theorem guG_le_succ : ∀ b, b + 1 < guB → guG b ≤ guG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1
  have hbB : b < guB := (lt_add_one b).trans hb1
  rcases lt_or_ge b gfE with hbE | hbE
  · rw [guG_low hbE, guG_low (succ_lt_eW hbE)]; exact (rdc_succ b hbE 0).2.1
  obtain ⟨hn1, -, -, -, -⟩ := guN_spec hbE hbB
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gu_parts hbE hbB
  obtain ⟨e, hr1, hv⟩ := gu_succ_nf hbE hb1
  have hr1B : b % guE b ^ log (guE b) b + 1 < guB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [guG_dec hbE hbB, e, guG_cnf hn1 hk hd0 hdE hr1 hv (e ▸ hb1)]
  exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb hr1B))

theorem guG_le_succ_all (b : Ordinal.{0}) : guG b ≤ guG (b + 1) := by
  rcases lt_or_ge (b + 1) guB with h | h
  · exact guG_le_succ b h
  · have hb : guB ≤ b := by
      by_contra hb; push Not at hb; exact absurd (guB_lim.add_one_lt hb) (not_lt.2 h)
    rw [guG_high h, guG_high hb]

end Googology.Trans.PoR.InaccPsi.R2.Gk
