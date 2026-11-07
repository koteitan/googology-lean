import Googology.Trans.PoR.InaccPsi.R2.QfLh

/-!
# QfGap: THE GAP OF THE REACH CODES AT THE VEBLEN LEVELS, `qfLam(M') + Ω₁ ≤ qfLam(M)` FOR `M' < M`

`qfLam M = qfH(l) + (Ω₁·M − ω^l)`, `l = qfL M = log_ω(Ω₁·M)`, where the head `qfH(l)` depends on the leading
exponent only: `qfRe(c) + ω^l` (the case `cr < m`, `c = ω^{log_ω l}`), `qfRe(l)` (`ω^l = l`), `ω^l + logend(l)`.  The
head is `≥ ω^l`, and for `l' < l`: `qfH(l') + ω^{l'+1} ≤ qfH(l)` (`qf_head_gap`): the head of `l'` is below
`ω^{l'+1}` unless `l'` is an `ε`-code of infinite Veblen level or a case `cr < m`; there `qfRe` of the `ε`-code is
below `ω^{c + log_ω a_c + 1}`, and an `l` between the two is exactly a case `cr < m` with the same `c`.

* `qfH`, `qf_lam_head` (`qfLam M = qfH(qfL M) + (Ω₁·M − ω^{qfL M})`), `qf_re_ge`, `qf_re_lt`
  (**`p ≤ qfRe(p) < ω^{p + log_ω a_p + 1}`**), `qf_head_ge`, `qf_head_gap`, `qf_lam_gap` (**`qfLam(M') + Ω₁ ≤
  qfLam(M)`** for `ε_{Ω₁+1} ≤ M' < M`).

No new axiom.  New definition: `qfH`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Hc

/-- The condition `cr < m` read from the leading exponent `l`. -/
def QfCrL (l : Ordinal.{0}) : Prop :=
  ω ^ l ≠ l ∧ ω ^ (ω ^ log ω l) = ω ^ log ω l ∧ l < ω ^ log ω l + ω ^ log ω l ∧
    l - ω ^ log ω l ≤ log ω (invVeblen₁ (ω ^ log ω l))

open Classical in
/-- **The head of the reach code**, from the leading exponent `l`. -/
noncomputable def qfH (l : Ordinal.{0}) : Ordinal.{0} :=
  if QfCrL l then qfRe (ω ^ log ω l) + ω ^ l
  else if ω ^ l = l then qfRe l else ω ^ l + lg l

theorem qf_cr_iff (M : Ordinal.{0}) : QfCr M ↔ QfCrL (qfL M) := Iff.rfl

/-- **`qfLam M = qfH(qfL M) + (Ω₁·M − ω^{qfL M})`.** -/
theorem qf_lam_head {M : Ordinal.{0}} (hM0 : M ≠ 0) :
    qfLam M = qfH (qfL M) + (Om1 * M - ω ^ qfL M) := by
  classical
  have hL0 : Om1 * M ≠ 0 := mul_ne_zero rj_Om1_pos.ne' hM0
  have hDL : ω ^ qfL M ≤ Om1 * M := opow_log_le_self ω hL0
  unfold qfLam qfH
  by_cases hC : QfCr M
  · rw [if_pos hC, if_pos ((qf_cr_iff M).1 hC), add_assoc, Ordinal.add_sub_cancel_of_le hDL]
    rfl
  · rw [if_neg hC, if_neg (fun h => hC ((qf_cr_iff M).2 h))]
    split_ifs <;> rfl

/-- `1 + a < ω^{log_ω a + 1}` for `a ≥ 1`. -/
theorem qf_one_add_lt {a : Ordinal.{0}} (ha1 : 1 ≤ a) : 1 + a < ω ^ (log ω a + 1) := by
  have ha0 : a ≠ 0 := (lt_of_lt_of_le zero_lt_one ha1).ne'
  rcases lt_or_ge a ω with h | h
  · have hl : log ω a = 0 := log_eq_zero h
    rw [hl, zero_add, opow_one]
    obtain ⟨n, rfl⟩ := lt_omega0.1 h
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this]; exact natCast_lt_omega0 _
  · rw [one_add_of_omega0_le h, ← succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 a

/-- **`p ≤ qfRe(p)`** (no hypothesis). -/
theorem qf_re_ge' (p : Ordinal.{0}) : p ≤ qfRe p := by
  unfold qfRe
  exact (le_mul_of_one_le_right' le_self_add).trans (le_self_add.trans le_self_add)

/-- **An `ε`-number `p ∈ (Ω₁, Γ_{Ω₁+1})` in normal form**: `p = φ(a, b)`, `1 ≤ a < p`, `b < p`. -/
theorem qf_eps_dec' {p : Ordinal.{0}} (hp1 : Om 1 < p) (hpG : p < ggGam) (hpE : ω ^ p = p) :
    veblen (invVeblen₁ p) (invVeblen₂ p) = p ∧ invVeblen₂ p < p ∧ 1 ≤ invVeblen₁ p ∧ invVeblen₁ p < p := by
  have hdec : veblen (invVeblen₁ p) (invVeblen₂ p) = p := by rw [veblen_invVeblen₁_invVeblen₂, hpE]
  have hb1 : invVeblen₂ p < p := by have := invVeblen₂_lt p; rwa [hpE] at this
  have ha1 : 1 ≤ invVeblen₁ p := by
    refine one_le_iff_ne_zero.2 fun h0 => ?_
    rw [h0, veblen_zero_apply] at hdec
    have e : ω ^ invVeblen₂ p = ω ^ p := hdec.trans hpE.symm
    rw [(opow_right_inj one_lt_omega0).1 e] at hb1
    exact lt_irrefl _ hb1
  have hap : invVeblen₁ p < p := by
    refine lt_of_le_of_ne ((left_le_veblen (invVeblen₁ p) (invVeblen₂ p)).trans_eq hdec) fun e => ?_
    have hfix : veblen p 0 = p := by
      refine le_antisymm ?_ (left_le_veblen p 0)
      calc veblen p 0 ≤ veblen p (invVeblen₂ p) := (veblen_le_veblen_iff_right).2 zero_le
        _ = veblen (invVeblen₁ p) (invVeblen₂ p) := by rw [e]
        _ = p := hdec
    have hS := qf_SC_of_fix ((Om_pos one_ne_zero).trans hp1) hfix
    exact absurd (ggGam_le hS hp1) (not_le.2 hpG)
  exact ⟨hdec, hb1, ha1, hap⟩

theorem qf_log_eps {c : Ordinal.{0}} (hc : ω ^ c = c) : log ω c = c := by
  conv_lhs => rw [← hc]
  exact log_opow one_lt_omega0 c

/-- `log_ω l = e` for `ω^e ≤ l < ω^e + ω^e`. -/
theorem qf_log_eq {e l : Ordinal.{0}} (h1 : ω ^ e ≤ l) (h2 : l < ω ^ e + ω ^ e) : log ω l = e := by
  have hl0 : l ≠ 0 := (lt_of_lt_of_le (opow_pos e omega0_pos) h1).ne'
  refine (log_eq_iff one_lt_omega0 hl0 e).2 ⟨h1, h2.trans_le ?_⟩
  rw [opow_add, opow_one, ← mul_two_eq]
  exact mul_le_mul_right (by exact_mod_cast (natCast_lt_omega0 2).le) _

/-- An ordinal strictly between `c` and `c + c` (`c` additive principal) is not additive principal. -/
theorem qf_not_eps_between {c l : Ordinal.{0}} (hcI : Indec c) (hcl : c < l) (hlc : l < c + c) : ω ^ l ≠ l := by
  intro hE
  have hlI : Indec l := by rw [← hE]; exact indec_opow _
  exact absurd (hlI.add_lt hcl hcl) (not_lt.2 hlc.le)

/-- **The head is `≥ ω^l`.** -/
theorem qf_head_ge (l : Ordinal.{0}) : ω ^ l ≤ qfH l := by
  classical
  unfold qfH
  split_ifs with h1 h2
  · exact le_add_self
  · rw [h2]; exact qf_re_ge' l
  · exact le_self_add

/-- The case `cr < m` at `l ∈ (c, c + log_ω a_c + 1)` for an `ε`-code `c ∈ (Ω₁, Γ_{Ω₁+1})`. -/
theorem qf_crL_of {c l : Ordinal.{0}} (hc1 : Om 1 < c) (hcG : c < ggGam) (hcE : ω ^ c = c) (hcl : c < l)
    (hl : l < c + log ω (invVeblen₁ c) + 1) : QfCrL l ∧ ω ^ log ω l = c := by
  obtain ⟨-, -, ha1, hap⟩ := qf_eps_dec' hc1 hcG hcE
  have hcI : Indec c := by rw [← hcE]; exact indec_opow _
  have hlogc : log ω (invVeblen₁ c) + 1 < c := by
    have h1 : log ω (invVeblen₁ c) < c :=
      (log_le_self ω _).trans_lt hap
    exact (ev_isSuccLimit_of_inE hcE).add_one_lt h1
  have hlc : l < c + c := hl.trans_le (by rw [add_assoc]; exact add_le_add le_rfl hlogc.le)
  have hlog : log ω l = c := by
    refine qf_log_eq ?_ ?_
    · rw [hcE]; exact hcl.le
    · rw [hcE]; exact hlc
  have hsub : l - c ≤ log ω (invVeblen₁ c) := by
    by_contra hc'
    push Not at hc'
    have h1 : c + (log ω (invVeblen₁ c) + 1) ≤ c + (l - c) :=
      add_le_add le_rfl (Order.add_one_le_of_lt hc')
    rw [Ordinal.add_sub_cancel_of_le hcl.le, ← add_assoc] at h1
    exact absurd hl (not_lt.2 h1)
  have hw : ω ^ log ω l = c := by rw [hlog, hcE]
  refine ⟨⟨qf_not_eps_between hcI hcl hlc, by rw [hw, hcE], by rw [hw]; exact hlc, by rw [hw]; exact hsub⟩, hw⟩


section Re

variable {p : Ordinal.{0}} (hpE : ω ^ p = p) (ha1 : 1 ≤ invVeblen₁ p) (hap : invVeblen₁ p < p)
  (hbp : invVeblen₂ p < p)
include hpE ha1 hap hbp

/-- **`p ≤ qfRe(p)`.** -/
theorem qf_re_ge : p ≤ qfRe p := by
  unfold qfRe
  refine le_trans ?_ (le_self_add.trans le_self_add)
  exact le_mul_of_one_le_right' le_self_add

/-- **`qfRe(p) < ω^{p + log_ω a_p + 1}`.** -/
theorem qf_re_lt : qfRe p < ω ^ (p + log ω (invVeblen₁ p) + 1) := by
  set a := invVeblen₁ p with hadef
  set b := invVeblen₂ p with hbdef
  set W := ω ^ (p + log ω a + 1) with hW
  have hWI : Indec W := indec_opow _
  have hp0 : 0 < p := by rw [← hpE]; exact opow_pos _ omega0_pos
  have h1 : p * (1 + a) < W := by
    rw [hW, add_assoc, opow_add, hpE]
    exact (mul_lt_mul_iff_right₀ hp0).2 (qf_one_add_lt ha1)
  have hpW : p ≤ W := by
    rw [hW]; conv_lhs => rw [← hpE]
    exact opow_le_opow_right omega0_pos (le_self_add.trans le_self_add)
  have hpI : Indec p := by rw [← hpE]; exact indec_opow _
  have h2 : hcE a + lg b < p := by
    have he : hcE a < p := (hcE_le a).trans_lt hap
    have hl : lg b < p := by
      rcases eq_or_ne b 0 with h0 | h0
      · rw [h0, Qc.qc_lg_zero]; exact hp0
      · exact (lg_le h0).trans_lt hbp
    exact hpI.add_lt he hl
  unfold qfRe
  rw [← hadef, ← hbdef, add_assoc]
  exact hWI.add_lt h1 (h2.trans_le hpW)

end Re

/-- **THE GAP OF THE HEADS**: `qfH(l') + ω^{l'+1} ≤ qfH(l)` for `ε_{Ω₁+1} ≤ l' < l < Γ_{Ω₁+1}`. -/
theorem qf_head_gap {l' l : Ordinal.{0}} (hEl' : ggE ≤ l') (hll : l' < l) (hlG : l < ggGam) :
    qfH l' + ω ^ (l' + 1) ≤ qfH l := by
  classical
  have hO1E : Om 1 < ggE := ggE_spec.2
  have hl'1 : Om 1 < l' := hO1E.trans_le hEl'
  have hl'G : l' < ggGam := hll.trans hlG
  have hl'0 : l' ≠ 0 := (lt_of_le_of_lt zero_le hl'1).ne'
  have hsucc : l' + 1 ≤ l := Order.add_one_le_of_lt hll
  have hWl : ω ^ (l' + 1) ≤ ω ^ l := opow_le_opow_right omega0_pos hsucc
  by_cases hA : qfH l' < ω ^ (l' + 1)
  · rw [add_of_omega0_opow_le (b := l' + 1) hA le_rfl]
    exact hWl.trans (qf_head_ge l)
  push Not at hA
  -- the leading part `c' = ω^{log l'}` is `ε_{Ω₁+1}` or above
  have hlogE : ggE ≤ log ω l' := by
    have h := log_mono_right ω hEl'
    rwa [qf_log_eps ggE_spec.1] at h
  have hc'E : ggE ≤ ω ^ log ω l' := (right_le_opow _ one_lt_omega0).trans' hlogE
  have hc'l : ω ^ log ω l' ≤ l' := opow_log_le_self ω hl'0
  unfold qfH at hA
  by_cases hCr : QfCrL l'
  · rw [if_pos hCr] at hA
    obtain ⟨-, hcE, -, -⟩ := id hCr
    set c := ω ^ log ω l' with hcdef
    have hc1 : Om 1 < c := hO1E.trans_le hc'E
    have hcG : c < ggGam := hc'l.trans_lt hl'G
    obtain ⟨-, hb1, ha1, hap⟩ := qf_eps_dec' hc1 hcG hcE
    have hRe := qf_re_lt hcE ha1 hap hb1
    have hX : qfH l' + ω ^ (l' + 1) = qfRe c + ω ^ (l' + 1) := by
      unfold qfH; rw [if_pos hCr, add_assoc]
      congr 1
      exact add_of_omega0_opow_le (b := l' + 1)
        ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one l')) le_rfl
    rw [hX]
    rcases le_or_gt (c + log ω (invVeblen₁ c) + 1) l with hge | hlt
    · have h1 : qfRe c < ω ^ l := hRe.trans_le (opow_le_opow_right omega0_pos hge)
      calc qfRe c + ω ^ (l' + 1) ≤ qfRe c + ω ^ l := add_le_add le_rfl hWl
        _ = ω ^ l := add_of_omega0_opow_le (b := l) h1 le_rfl
        _ ≤ qfH l := qf_head_ge l
    · obtain ⟨hCl, hw⟩ := qf_crL_of hc1 hcG hcE (hc'l.trans_lt hll) hlt
      unfold qfH; rw [if_pos hCl, hw]
      exact add_le_add le_rfl hWl
  · rw [if_neg hCr] at hA
    by_cases hlE : ω ^ l' = l'
    · rw [if_pos hlE] at hA
      obtain ⟨-, hb1, ha1, hap⟩ := qf_eps_dec' hl'1 hl'G hlE
      have hRe := qf_re_lt hlE ha1 hap hb1
      have hX : qfH l' = qfRe l' := by unfold qfH; rw [if_neg hCr, if_pos hlE]
      rw [hX]
      have hWW : ω ^ (l' + 1) ≤ ω ^ (l' + log ω (invVeblen₁ l') + 1) :=
        opow_le_opow_right omega0_pos (add_le_add le_self_add le_rfl)
      have hsum : qfRe l' + ω ^ (l' + 1) < ω ^ (l' + log ω (invVeblen₁ l') + 1) := by
        rcases hWW.lt_or_eq with h | h
        · exact (indec_opow _).add_lt hRe h
        · exfalso
          have h1 : qfRe l' < ω ^ (l' + 1) := h ▸ hRe
          exact absurd hA (not_le.2 h1)
      rcases le_or_gt (l' + log ω (invVeblen₁ l') + 1) l with hge | hlt
      · exact (hsum.trans_le (opow_le_opow_right omega0_pos hge)).le.trans (qf_head_ge l)
      · obtain ⟨hCl, hw⟩ := qf_crL_of hl'1 hl'G hlE hll hlt
        unfold qfH; rw [if_pos hCl, hw]
        exact add_le_add le_rfl hWl
    · rw [if_neg hlE] at hA
      exfalso
      have hlgl : lg l' < ω ^ l' := (lg_le hl'0).trans_lt (lt_of_le_of_ne (right_le_opow l' one_lt_omega0)
        (Ne.symm hlE))
      have h1 : ω ^ l' + lg l' < ω ^ (l' + 1) := by
        rw [opow_add, opow_one]
        calc ω ^ l' + lg l' < ω ^ l' + ω ^ l' := (add_lt_add_iff_left _).2 hlgl
          _ = ω ^ l' * 2 := (mul_two_eq _).symm
          _ < ω ^ l' * ω := (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (natCast_lt_omega0 2)
      exact absurd hA (not_le.2 h1)

/-- **THE GAP OF THE REACH CODES**: `qfLam(M') + Ω₁ ≤ qfLam(M)` for `ε_{Ω₁+1} ≤ M' < M < Γ_{Ω₁+1}`. -/
theorem qf_lam_gap {M' M : Ordinal.{0}} (hEM' : ggE ≤ M') (hM'M : M' < M) (hMG : M < ggGam) :
    qfLam M' + Om1 ≤ qfLam M := by
  have hO0 : (0 : Ordinal.{0}) < Om1 := rj_Om1_pos
  have hM'0 : M' ≠ 0 := (lt_of_lt_of_le (show InE ggE from ggE_spec.1).pos hEM').ne'
  have hM0 : M ≠ 0 := (lt_of_le_of_lt zero_le hM'M).ne'
  rw [qf_lam_head hM'0, qf_lam_head hM0]
  set l' := qfL M' with hl'
  set l := qfL M with hl
  have hL'0 : Om1 * M' ≠ 0 := mul_ne_zero hO0.ne' hM'0
  have hD' : ω ^ l' ≤ Om1 * M' := opow_log_le_self ω hL'0
  have hgap : Om1 * M' + Om1 ≤ Om1 * M := by
    rw [← mul_add_one]; exact mul_le_mul_right (Order.add_one_le_of_lt hM'M) _
  have hll : l' ≤ l := log_mono_right ω ((le_self_add).trans hgap)
  have hEl' : ggE ≤ l' := by
    have h1 : ggE ≤ Om1 * M' := hEM'.trans (Ordinal.le_mul_right M' hO0)
    have h2 := log_mono_right ω h1
    rwa [qf_log_eps ggE_spec.1] at h2
  rcases hll.lt_or_eq with hlt | heq
  · have hLG : Om1 * M < ggGam := by
      have hS := ggGam_spec.1
      have hOG : (Om1 : Ordinal.{0}) < ggGam := by rw [rj_Om1]; exact ggGam_spec.2
      exact InE.mul_lt (Low.opow_eq_self_of_SC hS) hOG hMG
    have hlG : l < ggGam := (log_le_self ω _).trans_lt hLG
    have hrest : Om1 * M' - ω ^ l' + Om1 < ω ^ (l' + 1) := by
      have h1 : Om1 * M' - ω ^ l' < ω ^ (l' + 1) :=
        (Ordinal.sub_le_self _ _).trans_lt (lt_opow_succ_log_self one_lt_omega0 _)
      have h2 : (Om1 : Ordinal.{0}) < ω ^ (l' + 1) := by
        rw [rj_Om1]
        exact (ggE_spec.2.trans_le hEl').trans ((right_le_opow l' one_lt_omega0).trans_lt
          ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one l')))
      exact (indec_opow _).add_lt h1 h2
    calc qfH l' + (Om1 * M' - ω ^ l') + Om1 = qfH l' + (Om1 * M' - ω ^ l' + Om1) := by rw [add_assoc]
      _ ≤ qfH l' + ω ^ (l' + 1) := add_le_add le_rfl hrest.le
      _ ≤ qfH l := qf_head_gap hEl' hlt hlG
      _ ≤ _ := le_self_add
  · rw [← heq]
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    have hD : ω ^ l' ≤ Om1 * M := hD'.trans (le_self_add.trans hgap)
    have h1 : ω ^ l' + (Om1 * M' - ω ^ l' + Om1) ≤ ω ^ l' + (Om1 * M - ω ^ l') := by
      rw [← add_assoc, Ordinal.add_sub_cancel_of_le hD', Ordinal.add_sub_cancel_of_le hD]; exact hgap
    exact (add_le_add_iff_left _).1 h1

end Googology.Trans.PoR.InaccPsi.R2.Qf
