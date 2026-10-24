import Googology.Trans.PoR.InaccPsi.R2.TeStep

/-!
# The `ε`-step: the readings are increasing, below `ε_{V(x)+1}`, and every ordinal below it is one

`K : Tb.TbCS` with `K.B` an `ε`-number; `x` an `ε`-number below `Ω₁`, `V = K.V(x)` (an `ε`-number above `x`):

* `te_ord` (**the readings `teR` are strictly increasing in the code** (gates below `x`), every code `c ≥ K.B` reads
  at least `V`, and `c(x) < ω^{e(x)+1}` for `e = log_ω c`), `teR_mono`, `te_V_lt` (`V < e(x)` for every code
  `e > K.B`);
* `teR_lt` (**every reading is below `ε_{V+1}`**), `teR_ex` (**every ordinal below `ε_{V+1}` is a reading** of a code
  `< ε_{K.B+1}` with gate below `x`), `teR_rest` (`r(x) < ω^{e(x)}` for the rest `r` of a code with `log c > K.B`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable (K : Tb.TbCS) (hBE : InE K.B) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hBE hx hx1

omit hBE in
/-- Every code below `K.B` (gate below `x`) reads below `V(x)`. -/
theorem te_old {b : Ordinal.{0}} (hb : b < K.B) (hg : teG K b < x) : teR K b x < K.V x := by
  rw [teR_low K hb]; rw [teG_low K hb] at hg; exact K.R_lt x b hx hx1 hb hg

omit hx hx1 in
theorem te_logB : log ω K.B = K.B := by
  have hBe : ω ^ K.B = K.B := hBE
  conv_lhs => rw [← hBe]
  exact log_opow one_lt_omega0 _

/-- **The readings are strictly increasing in the code**; every code `c ≥ K.B` reads at least `V(x)`, and
`c(x) < ω^{e(x)+1}` for `e = log_ω c`. -/
theorem te_ord : ∀ c, c < eN K.B → teG K c < x →
    (∀ b, b < c → teG K b < x → teR K b x < teR K c x) ∧
      (K.B ≤ c → K.V x ≤ teR K c x ∧ teR K c x < ω ^ (teR K (log ω c) x + 1)) := by
  have hBe : ω ^ K.B = K.B := hBE
  have hVE : InE (K.V x) := K.V_E x hx hx1
  have hVe : ω ^ K.V x = K.V x := hVE
  have hVup : ∀ n : Ordinal.{0}, n < ω → K.V x * n < ω ^ (K.V x + 1) := by
    intro n hn
    calc K.V x * n < K.V x * ω := (mul_lt_mul_iff_right₀ hVE.pos).2 hn
      _ = ω ^ (K.V x + 1) := by rw [opow_add, opow_one, hVe]
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hgc
  rcases lt_trichotomy c K.B with hcB | rfl | hcB
  · refine ⟨fun b hbc hgb => ?_, fun h => absurd h (not_le.2 hcB)⟩
    have hbB := hbc.trans hcB
    rw [teR_low K hcB, teR_low K hbB]
    rw [teG_low K hcB] at hgc; rw [teG_low K hbB] at hgb
    exact K.R_mono x b c hx hcB hbc hgb hgc
  · refine ⟨fun b hbc hgb => ?_, fun _ => ?_⟩
    · rw [teR_B K]; exact te_old K hx hx1 hbc hgb
    · rw [teR_B K, te_logB K hBE, teR_B K]
      refine ⟨le_rfl, ?_⟩
      calc K.V x = ω ^ K.V x := hVe.symm
        _ < ω ^ (K.V x + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one _)
  obtain ⟨heB', hec, hn, hn0, hr, hrc, hdec⟩ := te_parts K hBE hcB hc
  by_cases heq : log ω c = K.B
  · -- `c = K.B·n + r`, `r < K.B`
    have hR : teR K c x = K.V x * (c / ω ^ log ω c) + K.R (c % ω ^ log ω c) x := teR_hiB K hcB hc heq x
    have hG : teG K c = K.G (c % ω ^ log ω c) := teG_hiB K hcB hc heq
    rw [hG] at hgc
    have hrB : c % ω ^ log ω c < K.B := by rw [heq, hBe] at hr ⊢; exact hr
    have hRr : K.R (c % ω ^ log ω c) x < K.V x := K.R_lt x _ hx hx1 hrB hgc
    have hVle : K.V x ≤ teR K c x := by rw [hR]; exact (Ordinal.le_mul_left _ hn0).trans le_self_add
    have hup : teR K c x < ω ^ (K.V x + 1) := by
      rw [hR]
      calc K.V x * (c / ω ^ log ω c) + K.R (c % ω ^ log ω c) x
          < K.V x * (c / ω ^ log ω c) + K.V x := (add_lt_add_iff_left _).2 hRr
        _ = K.V x * (c / ω ^ log ω c + 1) := by rw [mul_add_one]
        _ ≤ K.V x * ω := mul_le_mul_right (Order.add_one_le_of_lt hn) _
        _ = ω ^ (K.V x + 1) := by rw [opow_add, opow_one, hVe]
    refine ⟨fun b hbc hgb => ?_, fun _ => ⟨hVle, by rw [heq, teR_B K]; exact hup⟩⟩
    rcases lt_trichotomy b K.B with hbB | rfl | hbB
    · exact (te_old K hx hx1 hbB hgb).trans_le hVle
    · rw [teR_B K, hR]
      rcases eq_or_ne (c % ω ^ log ω c) 0 with h0 | h0
      · -- `n ≥ 2`
        have hn1 : c / ω ^ log ω c ≠ 1 := by
          intro h1
          rw [h0, h1, mul_one, add_zero, heq, hBe] at hdec
          exact absurd hdec hcB.ne
        have h2 : 1 < c / ω ^ log ω c := lt_of_le_of_ne (Order.one_le_iff_pos.2 hn0) (Ne.symm hn1)
        calc K.V x = K.V x * 1 := (mul_one _).symm
          _ < K.V x * (c / ω ^ log ω c) := (mul_lt_mul_iff_right₀ hVE.pos).2 h2
          _ ≤ _ := le_self_add
      · have hpos : 0 < K.R (c % ω ^ log ω c) x := by
          have := K.R_mono x 0 _ hx hrB (pos_iff_ne_zero.2 h0) (by rw [K.zero_G]; exact hx.pos) hgc
          rwa [K.zero_R] at this
        exact (Ordinal.le_mul_left _ hn0).trans_lt (lt_add_of_pos_right _ hpos)
    · -- `b > K.B`: `log b = K.B`
      have hbE : b < eN K.B := hbc.trans hc
      obtain ⟨hlb1, -, hnb, hnb0, hrb, -, hdecb⟩ := te_parts K hBE hbB hbE
      have hlb : log ω b = K.B := le_antisymm (heq ▸ log_mono_right ω hbc.le) hlb1
      rw [teR_hiB K hbB hbE hlb x, hR]
      rw [teG_hiB K hbB hbE hlb] at hgb
      have hrbB : b % ω ^ log ω b < K.B := by rw [hlb, hBe] at hrb ⊢; exact hrb
      rw [hlb] at hnb hnb0 hdecb hrbB hgb ⊢
      rw [heq] at hn hn0 hdec hrB hgc hRr hr ⊢
      have hnn : b / ω ^ K.B ≤ c / ω ^ K.B := by
        by_contra hlt
        push Not at hlt
        have h1 : c < ω ^ K.B * (c / ω ^ K.B + 1) := by
          rw [mul_add_one]; conv_lhs => rw [← hdec]
          exact (add_lt_add_iff_left _).2 hr
        have h2 : ω ^ K.B * (c / ω ^ K.B + 1) ≤ b := by
          rw [← hdecb]
          exact (mul_le_mul_right (Order.add_one_le_of_lt hlt) _).trans le_self_add
        exact absurd (hbc.trans (h1.trans_le h2)) (lt_irrefl _)
      have hRrb : K.R (b % ω ^ K.B) x < K.V x := K.R_lt x _ hx hx1 hrbB hgb
      rcases hnn.lt_or_eq with hnlt | hneq
      · calc K.V x * (b / ω ^ K.B) + K.R (b % ω ^ K.B) x
            < K.V x * (b / ω ^ K.B) + K.V x := (add_lt_add_iff_left _).2 hRrb
          _ = K.V x * (b / ω ^ K.B + 1) := by rw [mul_add_one]
          _ ≤ K.V x * (c / ω ^ K.B) := mul_le_mul_right (Order.add_one_le_of_lt hnlt) _
          _ ≤ _ := le_self_add
      · have hrr : b % ω ^ K.B < c % ω ^ K.B := by
          have h1 : ω ^ K.B * (c / ω ^ K.B) + b % ω ^ K.B < ω ^ K.B * (c / ω ^ K.B) + c % ω ^ K.B := by
            rw [hdec, ← hneq, hdecb]; exact hbc
          exact (add_lt_add_iff_left _).1 h1
        rw [hneq]
        exact (add_lt_add_iff_left _).2 (K.R_mono x _ _ hx hrB hrr hgb hgc)
  · -- `log c = e > K.B`
    have heB : K.B < log ω c := lt_of_le_of_ne heB' (Ne.symm heq)
    have hR : teR K c x = ω ^ teR K (log ω c) x * (c / ω ^ log ω c) + teR K (c % ω ^ log ω c) x :=
      teR_hi K hcB hc heq x
    rw [teG_hi K hcB hc heq] at hgc
    have hge : teG K (log ω c) < x := lt_of_le_of_lt (le_max_left _ _) hgc
    have hgr : teG K (c % ω ^ log ω c) < x := lt_of_le_of_lt (le_max_right _ _) hgc
    have heE : log ω c < eN K.B := hec.trans hc
    have IHe := IH _ hec heE hge
    have hVlt : K.V x < teR K (log ω c) x := by
      have := IHe.1 K.B heB (by rw [teG_B K]; exact hx.pos)
      rwa [teR_B K] at this
    have hsq : K.V x < ω ^ teR K (log ω c) x := hVlt.trans_le (right_le_opow _ one_lt_omega0)
    have hlow : ω ^ teR K (log ω c) x ≤ teR K c x := by
      rw [hR]; exact (Ordinal.le_mul_left _ hn0).trans le_self_add
    -- the reading of `log b < log c` is below that of `log c`
    have hlogR : ∀ b, K.B < b → b < c → teG K b < x → log ω b < log ω c →
        teR K (log ω b) x < teR K (log ω c) x := by
      intro b hbB hbc hgb hl
      have hbE : b < eN K.B := hbc.trans hc
      by_cases hlb : log ω b = K.B
      · rw [hlb, teR_B K]; exact hVlt
      · rw [teG_hi K hbB hbE hlb] at hgb
        exact IHe.1 _ hl (lt_of_le_of_lt (le_max_left _ _) hgb)
    have hrem : ∀ r', r' < c → r' < ω ^ log ω c → teG K r' < x → teR K r' x < ω ^ teR K (log ω c) x := by
      intro r' hr'c hr'e hgr'
      rcases lt_trichotomy r' K.B with hr'B | rfl | hr'B
      · exact (te_old K hx hx1 hr'B hgr').trans hsq
      · rw [teR_B K]; exact hsq
      · have hr'0 : r' ≠ 0 := (lt_of_le_of_lt zero_le hr'B).ne'
        have hl : log ω r' < log ω c := (lt_opow_iff_log_lt one_lt_omega0 hr'0).1 hr'e
        refine ((IH r' hr'c (hr'c.trans hc) hgr').2 hr'B.le).2.trans_le
          (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt (hlogR r' hr'B hr'c hgr' hl)))
    have hRr := hrem _ hrc hr hgr
    refine ⟨fun b hbc hgb => ?_, fun _ => ⟨hsq.le.trans hlow, ?_⟩⟩
    · rcases lt_trichotomy b K.B with hbB | rfl | hbB
      · exact ((te_old K hx hx1 hbB hgb).trans hsq).trans_le hlow
      · rw [teR_B K]; exact hsq.trans_le hlow
      have hbE : b < eN K.B := hbc.trans hc
      obtain ⟨-, -, hnb, hnb0, hrb, hrbb, hdecb⟩ := te_parts K hBE hbB hbE
      have hle : log ω b ≤ log ω c := log_mono_right ω hbc.le
      rcases hle.lt_or_eq with hlt | hleq
      · exact (((IH b hbc hbE hgb).2 hbB.le).2.trans_le (opow_le_opow_right omega0_pos
          (Order.add_one_le_of_lt (hlogR b hbB hbc hgb hlt)))).trans_le hlow
      · have hlb : log ω b ≠ K.B := by rw [hleq]; exact heq
        have hRb := teR_hi K hbB hbE hlb x
        rw [teG_hi K hbB hbE hlb] at hgb
        have hgrb : teG K (b % ω ^ log ω b) < x := lt_of_le_of_lt (le_max_right _ _) hgb
        rw [hleq] at hRb hnb hnb0 hrb hdecb hrbb hgrb
        have hnn : b / ω ^ log ω c ≤ c / ω ^ log ω c := by
          by_contra hlt
          push Not at hlt
          have h1 : c < ω ^ log ω c * (c / ω ^ log ω c + 1) := by
            rw [mul_add_one]
            calc c = ω ^ log ω c * (c / ω ^ log ω c) + c % ω ^ log ω c := hdec.symm
              _ < ω ^ log ω c * (c / ω ^ log ω c) + ω ^ log ω c := (add_lt_add_iff_left _).2 hr
          have h2 : ω ^ log ω c * (c / ω ^ log ω c + 1) ≤ b := by
            rw [← hdecb]
            exact (mul_le_mul_right (Order.add_one_le_of_lt hlt) _).trans le_self_add
          exact absurd (hbc.trans (h1.trans_le h2)) (lt_irrefl _)
        rcases hnn.lt_or_eq with hnlt | hneq
        · have hRrb := hrem _ (hrbb.trans hbc) hrb hgrb
          rw [hRb]
          calc ω ^ teR K (log ω c) x * (b / ω ^ log ω c) + teR K (b % ω ^ log ω c) x
              < ω ^ teR K (log ω c) x * (b / ω ^ log ω c) + ω ^ teR K (log ω c) x :=
                (add_lt_add_iff_left _).2 hRrb
            _ = ω ^ teR K (log ω c) x * (b / ω ^ log ω c + 1) := by rw [mul_add_one]
            _ ≤ ω ^ teR K (log ω c) x * (c / ω ^ log ω c) :=
                mul_le_mul_right (Order.add_one_le_of_lt hnlt) _
            _ ≤ teR K c x := by rw [hR]; exact le_self_add
        · have hrr : b % ω ^ log ω c < c % ω ^ log ω c := by
            have h1 : ω ^ log ω c * (c / ω ^ log ω c) + b % ω ^ log ω c <
                ω ^ log ω c * (c / ω ^ log ω c) + c % ω ^ log ω c := by
              rw [hdec, ← hneq, hdecb]; exact hbc
            exact (add_lt_add_iff_left _).1 h1
          rw [hRb, hR, hneq]
          exact (add_lt_add_iff_left _).2 ((IH _ hrc (hrc.trans hc) hgr).1 _ hrr hgrb)
    · rw [hR]
      calc ω ^ teR K (log ω c) x * (c / ω ^ log ω c) + teR K (c % ω ^ log ω c) x
          < ω ^ teR K (log ω c) x * (c / ω ^ log ω c) + ω ^ teR K (log ω c) x :=
            (add_lt_add_iff_left _).2 hRr
        _ = ω ^ teR K (log ω c) x * (c / ω ^ log ω c + 1) := by rw [mul_add_one]
        _ ≤ ω ^ teR K (log ω c) x * ω := mul_le_mul_right (Order.add_one_le_of_lt hn) _
        _ = ω ^ (teR K (log ω c) x + 1) := by rw [opow_add, opow_one]

theorem teR_mono {b c : Ordinal.{0}} (hc : c < eN K.B) (hbc : b < c) (hgb : teG K b < x) (hgc : teG K c < x) :
    teR K b x < teR K c x := (te_ord K hBE hx hx1 c hc hgc).1 b hbc hgb

/-- `V(x) < e(x)` for every code `e > K.B` with gate below `x`. -/
theorem te_V_lt {e : Ordinal.{0}} (he : K.B < e) (heE : e < eN K.B) (hg : teG K e < x) :
    K.V x < teR K e x := by
  have := teR_mono K hBE hx hx1 heE he (by rw [teG_B K]; exact hx.pos) hg
  rwa [teR_B K] at this

/-- `r(x) < ω^{e(x)}` for the rest `r = c mod ω^e` of a code `c` with `log c = e > K.B`. -/
theorem teR_rest {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) (he : log ω c ≠ K.B) (hg : teG K c < x) :
    teR K (c % ω ^ log ω c) x < ω ^ teR K (log ω c) x := by
  obtain ⟨heB', hec, -, -, hr, hrc, -⟩ := te_parts K hBE h1 h2
  have heB : K.B < log ω c := lt_of_le_of_ne heB' (Ne.symm he)
  rw [teG_hi K h1 h2 he] at hg
  obtain ⟨o1, o2, o3, o4, o5⟩ := te_mkE K hBE heB (hec.trans h2) one_pos one_lt_omega0 (opow_pos (log ω c) omega0_pos)
  rw [mul_one, add_zero] at o1 o2 o3 o4 o5
  have h := teR_mono K hBE hx hx1 o2 hr (lt_of_le_of_lt (le_max_right _ _) hg)
    (by rw [o5, teG_zero, max_eq_left zero_le]; exact lt_of_le_of_lt (le_max_left _ _) hg)
  rwa [o4, teR_zero, mul_one, add_zero] at h

/-- **Every reading is below `ε_{V(x)+1}`.** -/
theorem teR_lt : ∀ c, c < eN K.B → teG K c < x → teR K c x < eN (K.V x) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  have hE := eN_E (K.V x)
  rcases lt_trichotomy c K.B with hcB | rfl | hcB
  · exact (te_old K hx hx1 hcB hg).trans (lt_eN _)
  · rw [teR_B K]; exact lt_eN _
  · obtain ⟨-, hec, -, -, -, -, -⟩ := te_parts K hBE hcB hc
    have hlog : teR K (log ω c) x < eN (K.V x) := by
      by_cases he : log ω c = K.B
      · rw [he, teR_B K]; exact lt_eN _
      · have hg' := hg
        rw [teG_hi K hcB hc he] at hg'
        exact IH _ hec (hec.trans hc) (lt_of_le_of_lt (le_max_left _ _) hg')
    exact ((te_ord K hBE hx hx1 c hc hg).2 hcB.le).2.trans
      (hE.opow_lt ((ev_isSuccLimit_of_inE hE).add_one_lt hlog))

/-- **Every ordinal below `ε_{V(x)+1}` is the reading of a code `< ε_{K.B+1}` with gate below `x`.** -/
theorem teR_ex : ∀ ν, ν < eN (K.V x) → ∃ c, c < eN K.B ∧ teG K c < x ∧ teR K c x = ν := by
  have hBe : ω ^ K.B = K.B := hBE
  have hVE : InE (K.V x) := K.V_E x hx hx1
  have hVe : ω ^ K.V x = K.V x := hVE
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases lt_trichotomy ν (K.V x) with hνV | rfl | hνV
  · obtain ⟨c, hc, hg, hr⟩ := K.R_ex x ν hx hx1 hνV
    exact ⟨c, hc.trans (lt_eN _), by rw [teG_low K hc]; exact hg, by rw [teR_low K hc]; exact hr⟩
  · exact ⟨K.B, lt_eN _, by rw [teG_B K]; exact hx.pos, teR_B K _⟩
  have hν0 : ν ≠ 0 := (lt_of_le_of_lt zero_le hνV).ne'
  set E := log ω ν with hEdef
  have hVE' : K.V x ≤ E := le_log_of_opow_le one_lt_omega0 (by rw [hVe]; exact hνV.le)
  have hEν : E < ν := by
    refine lt_of_le_of_ne (log_le_self ω ν) fun he => ?_
    have h3 : ω ^ ν ≤ ν := by have := opow_log_le_self ω hν0; rwa [← hEdef, he] at this
    have hνE : InE ν := le_antisymm h3 (right_le_opow ν one_lt_omega0)
    exact absurd hν (not_lt.2 (eN_le hνV hνE))
  have hp : ω ^ E ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hN : ν / ω ^ E < ω := div_opow_log_lt ν one_lt_omega0
  have hN0 : 0 < ν / ω ^ E := div_opow_log_pos ω hν0
  have hW : ν % ω ^ E < ω ^ E := Ordinal.mod_lt ν hp
  have hWν : ν % ω ^ E < ν := hW.trans_le (opow_log_le_self ω hν0)
  have hdν : ω ^ E * (ν / ω ^ E) + ν % ω ^ E = ν := Ordinal.div_add_mod ν (ω ^ E)
  rcases hVE'.lt_or_eq with hVElt | hVEeq
  · -- `E > V(x)`
    obtain ⟨e, heE, hge, hre⟩ := IH E hEν (hEν.trans hν)
    obtain ⟨w, hwE, hgw, hrw⟩ := IH _ hWν (hWν.trans hν)
    have he : K.B < e := by
      rcases lt_trichotomy e K.B with h | h | h
      · exact absurd (hre ▸ te_old K hx hx1 h hge) (not_lt.2 hVElt.le)
      · rw [h, teR_B K] at hre; exact absurd hre hVElt.ne
      · exact h
    obtain ⟨o1, o2, -, o4, o5⟩ := te_mkE K hBE he heE one_pos one_lt_omega0 (opow_pos e omega0_pos)
    rw [mul_one, add_zero] at o1 o2 o4 o5
    have hr1 : teR K (ω ^ e) x = ω ^ E := by rw [o4, teR_zero, hre, mul_one, add_zero]
    have hg1 : teG K (ω ^ e) < x := by rw [o5, teG_zero, max_eq_left zero_le]; exact hge
    have hwe : w < ω ^ e := by
      by_contra hge'
      push Not at hge'
      rcases hge'.lt_or_eq with h | h
      · have := teR_mono K hBE hx hx1 hwE h hg1 hgw
        rw [hr1, hrw] at this
        exact absurd hW (not_lt.2 this.le)
      · rw [← h, hr1] at hrw
        exact absurd hW (by rw [← hrw]; exact lt_irrefl _)
    obtain ⟨-, k2, -, k4, k5⟩ := te_mkE K hBE he heE hN0 hN hwe
    refine ⟨ω ^ e * (ν / ω ^ E) + w, k2, by rw [k5]; exact max_lt hge hgw, ?_⟩
    rw [k4, hre, hrw, hdν]
  · -- `E = V(x)`: `ν = V(x)·N + W`, `W < V(x)`
    have hWV : ν % ω ^ E < K.V x := by rw [← hVEeq, hVe] at hW; rw [← hVEeq, hVe]; exact hW
    obtain ⟨w, hwB, hgw, hrw⟩ := K.R_ex x _ hx hx1 hWV
    obtain ⟨-, k2, k3, k4⟩ := te_mkB K hBE hN0 hN hwB
    refine ⟨K.B * (ν / ω ^ E) + w, k2, by rw [k4]; exact hgw, ?_⟩
    rw [k3 x, hrw]
    conv_rhs => rw [← hdν]
    rw [← hVEeq, hVe]

end Googology.Trans.PoR.InaccPsi.R2.Te
