import Googology.Trans.PoR.InaccPsi.R2.TbAt

/-!
# The codes below `ε_{Γ_{Ω₁+1}+1}`: Cantor normal form in base `ω` above `Γ_{Ω₁+1}²`

Below `Γ_{Ω₁+1}² = ω^{Γ_{Ω₁+1}·2}` a code is a code `Γ_{Ω₁+1}·γ + c'` of `R2.GmQ0` (reading `mqR`, gate `mqG`).  A code
`c ∈ [Γ_{Ω₁+1}², ε_{Γ_{Ω₁+1}+1})` is `ω^e·n + r` (`e = log_ω c ≥ Γ_{Ω₁+1}·2`, `0 < n < ω`, `r < ω^e`), with `e, r < c`;
its reading is `ω^{e(x)}·n + r(x)`, its gate the larger gate of `e` and `r`.

* `tbB` (`ε_{Γ_{Ω₁+1}+1}`), `tbR`, `tbG` (**the reading and the gate**, one well-founded recursion), `tb_parts`,
  `tb_mk` (the normal form and its parts), the unfolding lemmas;
* `tb_ord` (**the readings are strictly increasing in the code**, and `c(x) < ω^{e(x)+1}` above `Γ_{Ω₁+1}²`),
  `tbR_mono`, `tbR_two` (`Γ_{x+1}·2 ≤ e(x)` for `e ≥ Γ_{Ω₁+1}·2`), `tbR_lt` (**every reading is below
  `ε_{Γ_{x+1}+1}`**), `tbR_ex` (**every `ν < ε_{Γ_{x+1}+1}` is a reading** with gate below `x`), `tbR_succ`,
  `tbG_succ`.

No new axiom.  New definitions: `tbB`, `tbR`, `tbG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gc

/-- **The bound of the codes**: `ε_{Γ_{Ω₁+1}+1}`. -/
noncomputable def tbB : Ordinal.{0} := eN (gcG 0)

theorem tbB_E : InE tbB := eN_E _

theorem tbB_lim : IsSuccLimit tbB := ev_isSuccLimit_of_inE tbB_E

theorem tb_G0_lt_B : gcG 0 < tbB := lt_eN _

theorem tbQ_lt_B : mqB < tbB := by
  rw [mqB_eq]
  exact tbB_E.opow_lt ((inE_indec tbB_E).add_lt tb_G0_lt_B tb_G0_lt_B)

/-- No `ε`-number in `[Γ_{Ω₁+1}², ε_{Γ_{Ω₁+1}+1})`. -/
theorem tb_notE {c : Ordinal.{0}} (h1 : mqB ≤ c) (h2 : c < tbB) : ¬ InE c := fun hc =>
  absurd h2 (not_lt.2 (eN_le (mq_G0_lt_B.trans_le h1) hc))

/-- **The parts of a code `c ∈ [Γ_{Ω₁+1}², ε_{Γ_{Ω₁+1}+1})`.** -/
theorem tb_parts {c : Ordinal.{0}} (h1 : mqB ≤ c) (h2 : c < tbB) :
    gcG 0 + gcG 0 ≤ log ω c ∧ log ω c < c ∧ c / ω ^ log ω c < ω ∧ 0 < c / ω ^ log ω c ∧
      c % ω ^ log ω c < ω ^ log ω c ∧ c % ω ^ log ω c < c ∧
      ω ^ log ω c * (c / ω ^ log ω c) + c % ω ^ log ω c = c := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (gl_G0_E.pos.trans mq_G0_lt_B) h1).ne'
  have hle : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  have hp : ω ^ log ω c ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hm : c % ω ^ log ω c < ω ^ log ω c := Ordinal.mod_lt c hp
  refine ⟨le_log_of_opow_le one_lt_omega0 (by rw [← mqB_eq]; exact h1), ?_, div_opow_log_lt c one_lt_omega0,
    div_opow_log_pos ω hc0, hm, hm.trans_le hle, Ordinal.div_add_mod c _⟩
  refine lt_of_le_of_ne (log_le_self ω c) fun he => tb_notE h1 h2 ?_
  have h3 : ω ^ c ≤ c := by
    have := opow_log_le_self ω hc0
    rwa [he] at this
  exact le_antisymm h3 (right_le_opow c one_lt_omega0)

/-- **The reading** of a code: `mqR` below `Γ_{Ω₁+1}²`, `ω^{e(x)}·n + r(x)` above. -/
noncomputable def tbR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if _h : mqB ≤ c ∧ c < tbB then
    ω ^ tbR (log ω c) x * (c / ω ^ log ω c) + tbR (c % ω ^ log ω c) x
  else mqR c x
termination_by c
decreasing_by
  all_goals first
    | exact (tb_parts _h.1 _h.2).2.1
    | exact (tb_parts _h.1 _h.2).2.2.2.2.2.1

/-- **The gate** of a code: `mqG` below `Γ_{Ω₁+1}²`, the larger gate of `e` and `r` above. -/
noncomputable def tbG (c : Ordinal.{0}) : Ordinal.{0} :=
  if _h : mqB ≤ c ∧ c < tbB then max (tbG (log ω c)) (tbG (c % ω ^ log ω c)) else mqG c
termination_by c
decreasing_by
  all_goals first
    | exact (tb_parts _h.1 _h.2).2.1
    | exact (tb_parts _h.1 _h.2).2.2.2.2.2.1

theorem tbR_low {c : Ordinal.{0}} (hc : c < mqB) (x : Ordinal.{0}) : tbR c x = mqR c x := by
  rw [tbR, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

theorem tbG_low {c : Ordinal.{0}} (hc : c < mqB) : tbG c = mqG c := by
  rw [tbG, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

theorem tbR_hi {c : Ordinal.{0}} (h1 : mqB ≤ c) (h2 : c < tbB) (x : Ordinal.{0}) :
    tbR c x = ω ^ tbR (log ω c) x * (c / ω ^ log ω c) + tbR (c % ω ^ log ω c) x := by
  rw [tbR, dif_pos ⟨h1, h2⟩]

theorem tbG_hi {c : Ordinal.{0}} (h1 : mqB ≤ c) (h2 : c < tbB) :
    tbG c = max (tbG (log ω c)) (tbG (c % ω ^ log ω c)) := by
  rw [tbG, dif_pos ⟨h1, h2⟩]

/-- **A normal form `ω^e·n + r` and its parts.** -/
theorem tb_mk {e n r : Ordinal.{0}} (he : gcG 0 + gcG 0 ≤ e) (heB : e < tbB) (hn0 : 0 < n) (hn : n < ω)
    (hr : r < ω ^ e) :
    mqB ≤ ω ^ e * n + r ∧ ω ^ e * n + r < tbB ∧ log ω (ω ^ e * n + r) = e ∧
      (ω ^ e * n + r) / ω ^ e = n ∧ (ω ^ e * n + r) % ω ^ e = r := by
  have hp : ω ^ e ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mqB_eq]
    exact (opow_le_opow_right omega0_pos he).trans ((Ordinal.le_mul_left _ hn0).trans le_self_add)
  · calc ω ^ e * n + r < ω ^ e * n + ω ^ e := (add_lt_add_iff_left _).2 hr
      _ = ω ^ e * (n + 1) := by rw [mul_add_one]
      _ ≤ ω ^ e * ω := mul_le_mul_right (Order.add_one_le_of_lt hn) _
      _ = ω ^ (e + 1) := by rw [opow_add, opow_one]
      _ < tbB := tbB_E.opow_lt (tbB_lim.add_one_lt heB)
  · rw [log_opow_mul_add one_lt_omega0 hn0.ne' hr, log_eq_zero hn, add_zero]
  · rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

theorem tbR_mk {e n r : Ordinal.{0}} (he : gcG 0 + gcG 0 ≤ e) (heB : e < tbB) (hn0 : 0 < n) (hn : n < ω)
    (hr : r < ω ^ e) (x : Ordinal.{0}) : tbR (ω ^ e * n + r) x = ω ^ tbR e x * n + tbR r x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tb_mk he heB hn0 hn hr
  rw [tbR_hi h1 h2, h3, h4, h5]

theorem tbG_mk {e n r : Ordinal.{0}} (he : gcG 0 + gcG 0 ≤ e) (heB : e < tbB) (hn0 : 0 < n) (hn : n < ω)
    (hr : r < ω ^ e) : tbG (ω ^ e * n + r) = max (tbG e) (tbG r) := by
  obtain ⟨h1, h2, h3, -, h5⟩ := tb_mk he heB hn0 hn hr
  rw [tbG_hi h1 h2, h3, h5]

theorem tbR_zero (x : Ordinal.{0}) : tbR 0 x = 0 := by
  rw [tbR_low (gl_G0_E.pos.trans mq_G0_lt_B)]
  unfold mqR
  rw [Ordinal.zero_div, Ordinal.zero_mod, glR_zero, mul_zero, add_zero]

theorem tbG_zero : tbG 0 = 0 := by rw [tbG_low (gl_G0_E.pos.trans mq_G0_lt_B), mqG_zero]

/-- The code `Γ_{Ω₁+1}·2`. -/
theorem tb_two (x : Ordinal.{0}) :
    tbR (gcG 0 + gcG 0) x = lgG x * 2 ∧ tbG (gcG 0 + gcG 0) = 0 := by
  obtain ⟨h1, h2, h3⟩ := tbMq_two x
  rw [tbR_low h1, tbG_low h1]; exact ⟨h2, h3⟩

/-! ## `+1` -/

theorem tb_succ_parts {b : Ordinal.{0}} (h1 : mqB ≤ b) (h2 : b < tbB) :
    mqB ≤ b + 1 ∧ b + 1 < tbB ∧ log ω (b + 1) = log ω b ∧ (b + 1) / ω ^ log ω b = b / ω ^ log ω b ∧
      (b + 1) % ω ^ log ω b = b % ω ^ log ω b + 1 := by
  obtain ⟨he, -, hn, hn0, hr, -, hdec⟩ := tb_parts h1 h2
  have he1 : (1 : Ordinal.{0}) ≤ log ω b :=
    (Order.one_le_iff_pos.2 gl_G0_E.pos).trans (le_self_add.trans he)
  have hlim : IsSuccLimit (ω ^ log ω b) := Ph.ph_opow_lim (pos_iff_ne_zero.1 (lt_of_lt_of_le zero_lt_one he1))
  have hr1 : b % ω ^ log ω b + 1 < ω ^ log ω b := hlim.add_one_lt hr
  have heB : log ω b < tbB := (tb_parts h1 h2).2.1.trans h2
  obtain ⟨k1, k2, k3, k4, k5⟩ := tb_mk he heB hn0 hn hr1
  have e : ω ^ log ω b * (b / ω ^ log ω b) + (b % ω ^ log ω b + 1) = b + 1 := by rw [← add_assoc, hdec]
  rw [e] at k1 k2 k3 k4 k5
  exact ⟨k1, k2, k3, k4, k5⟩

/-- **`c(x)` moves by `+1` along `+1`.** -/
theorem tbR_succ : ∀ b x, b < tbB → tbR (b + 1) x = tbR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x hb
  rcases lt_or_ge b mqB with hQ | hQ
  · have hQ1 : b + 1 < mqB := mqB_lim.add_one_lt hQ
    rw [tbR_low hQ1, tbR_low hQ, mqR_succ]
  · obtain ⟨k1, k2, k3, k4, k5⟩ := tb_succ_parts hQ hb
    obtain ⟨-, -, -, -, -, hrb, -⟩ := tb_parts hQ hb
    rw [tbR_hi k1 k2, tbR_hi hQ hb, k3, k4, k5, IH _ hrb x (hrb.trans hb), add_assoc]

/-- **The gate moves along `+1`.** -/
theorem tbG_succ : ∀ b Z, b < tbB → IsSuccLimit Z → tbG b < Z → tbG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro Z hb hZ hg
  rcases lt_or_ge b mqB with hQ | hQ
  · rw [tbG_low (mqB_lim.add_one_lt hQ)]
    rw [tbG_low hQ] at hg
    exact mqG_succ hZ b hg
  · obtain ⟨k1, k2, k3, -, k5⟩ := tb_succ_parts hQ hb
    obtain ⟨-, -, -, -, -, hrb, -⟩ := tb_parts hQ hb
    rw [tbG_hi hQ hb] at hg
    rw [tbG_hi k1 k2, k3, k5]
    exact max_lt (lt_of_le_of_lt (le_max_left _ _) hg)
      (IH _ hrb Z (hrb.trans hb) hZ (lt_of_le_of_lt (le_max_right _ _) hg))

/-! ## Order -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem tb_sq_eq : lgG x * lgG x = ω ^ (lgG x * 2) := by
  have hE := (lgG_facts hx hx1).2.2.2.1
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one, opow_add, hE]

/-- **The readings are strictly increasing in the code**, and `c(x) < ω^{e(x)+1}` for `c ≥ Γ_{Ω₁+1}²`. -/
theorem tb_ord : ∀ c, c < tbB → tbG c < x →
    (∀ b, b < c → tbG b < x → tbR b x < tbR c x) ∧
      (mqB ≤ c → tbR c x < ω ^ (tbR (log ω c) x + 1)) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hgc
  rcases lt_or_ge c mqB with hQ | hQ
  · refine ⟨fun b hbc hgb => ?_, fun h => absurd h (not_le.2 hQ)⟩
    have hbQ := hbc.trans hQ
    rw [tbR_low hQ, tbR_low hbQ]
    rw [tbG_low hQ] at hgc
    rw [tbG_low hbQ] at hgb
    exact mqR_mono hx hx1 hQ hbc hgb hgc
  obtain ⟨he2, hec, hn, hn0, hr, hrc, hdec⟩ := tb_parts hQ hc
  set e := log ω c with hedef
  set n := c / ω ^ e with hndef
  set r := c % ω ^ e with hrdef
  have hR : tbR c x = ω ^ tbR e x * n + tbR r x := tbR_hi hQ hc x
  rw [tbG_hi hQ hc] at hgc
  have hge : tbG e < x := lt_of_le_of_lt (le_max_left _ _) hgc
  have hgr : tbG r < x := lt_of_le_of_lt (le_max_right _ _) hgc
  have heB : e < tbB := hec.trans hc
  have IHe := IH e hec heB hge
  have h2 : lgG x * 2 ≤ tbR e x := by
    obtain ⟨t1, t2⟩ := tb_two x
    rcases he2.lt_or_eq with h | h
    · rw [← t1]; exact (IHe.1 _ h (by rw [t2]; exact hx.pos)).le
    · rw [← h, t1]
  have hsq : lgG x * lgG x ≤ ω ^ tbR e x := by
    rw [tb_sq_eq hx hx1]; exact opow_le_opow_right omega0_pos h2
  have hrem : ∀ r', r' < c → r' < ω ^ e → tbG r' < x → tbR r' x < ω ^ tbR e x := by
    intro r' hr'c hr'e hgr'
    rcases lt_or_ge r' mqB with hr'Q | hr'Q
    · rw [tbR_low hr'Q]
      rw [tbG_low hr'Q] at hgr'
      exact (tbMq_lt_sq hx hx1 hr'Q hgr').trans_le hsq
    · have hr'0 : r' ≠ 0 := (lt_of_lt_of_le (gl_G0_E.pos.trans mq_G0_lt_B) hr'Q).ne'
      have hl : log ω r' < e := (lt_opow_iff_log_lt one_lt_omega0 hr'0).1 hr'e
      have hr'B : r' < tbB := hr'c.trans hc
      have hgl : tbG (log ω r') < x := by
        rw [tbG_hi hr'Q hr'B] at hgr'; exact lt_of_le_of_lt (le_max_left _ _) hgr'
      refine ((IH r' hr'c hr'B hgr').2 hr'Q).trans_le (opow_le_opow_right omega0_pos ?_)
      exact Order.add_one_le_of_lt (IHe.1 _ hl hgl)
  have hlow : ω ^ tbR e x ≤ tbR c x := by
    rw [hR]; exact (Ordinal.le_mul_left _ hn0).trans le_self_add
  have hRr := hrem r hrc hr hgr
  refine ⟨fun b hbc hgb => ?_, fun _ => ?_⟩
  · rcases lt_or_ge b mqB with hbQ | hbQ
    · rw [tbR_low hbQ]
      rw [tbG_low hbQ] at hgb
      exact ((tbMq_lt_sq hx hx1 hbQ hgb).trans_le hsq).trans_le hlow
    have hbB : b < tbB := hbc.trans hc
    obtain ⟨-, hebb, hnb, hnb0, hrb, hrbb, hdecb⟩ := tb_parts hbQ hbB
    have hRb : tbR b x = ω ^ tbR (log ω b) x * (b / ω ^ log ω b) + tbR (b % ω ^ log ω b) x :=
      tbR_hi hbQ hbB x
    have hgb' := hgb
    rw [tbG_hi hbQ hbB] at hgb'
    have hgeb : tbG (log ω b) < x := lt_of_le_of_lt (le_max_left _ _) hgb'
    have hgrb : tbG (b % ω ^ log ω b) < x := lt_of_le_of_lt (le_max_right _ _) hgb'
    have hle : log ω b ≤ e := log_mono_right ω hbc.le
    rcases hle.lt_or_eq with hlt | heq
    · refine ((IH b hbc hbB hgb).2 hbQ).trans_le (le_trans (opow_le_opow_right omega0_pos ?_) hlow)
      exact Order.add_one_le_of_lt (IHe.1 _ hlt hgeb)
    · rw [heq] at hRb hnb hnb0 hrb hdecb hrbb hgrb
      have hnn : b / ω ^ e ≤ n := by
        by_contra hlt
        push Not at hlt
        have h1 : c < ω ^ e * (n + 1) := by
          rw [← hdec, mul_add_one]; exact (add_lt_add_iff_left _).2 hr
        have h2 : ω ^ e * (n + 1) ≤ b := by
          rw [← hdecb]
          exact (mul_le_mul_right (Order.add_one_le_of_lt hlt) _).trans le_self_add
        exact absurd (hbc.trans (h1.trans_le h2)) (lt_irrefl _)
      rcases hnn.lt_or_eq with hnlt | hneq
      · have hRrb := hrem _ (hrbb.trans hbc) hrb hgrb
        rw [hRb]
        calc ω ^ tbR e x * (b / ω ^ e) + tbR (b % ω ^ e) x
            < ω ^ tbR e x * (b / ω ^ e) + ω ^ tbR e x := (add_lt_add_iff_left _).2 hRrb
          _ = ω ^ tbR e x * (b / ω ^ e + 1) := by rw [mul_add_one]
          _ ≤ ω ^ tbR e x * n := mul_le_mul_right (Order.add_one_le_of_lt hnlt) _
          _ ≤ tbR c x := by rw [hR]; exact le_self_add
      · have hrr : b % ω ^ e < r := by
          have h1 : ω ^ e * n + b % ω ^ e < ω ^ e * n + r := by
            rw [hdec, ← hneq, hdecb]; exact hbc
          exact (add_lt_add_iff_left _).1 h1
        rw [hRb, hR, hneq]
        exact (add_lt_add_iff_left _).2 ((IH r hrc (hrc.trans hc) hgr).1 _ hrr hgrb)
  · rw [hR]
    calc ω ^ tbR e x * n + tbR r x < ω ^ tbR e x * n + ω ^ tbR e x := (add_lt_add_iff_left _).2 hRr
      _ = ω ^ tbR e x * (n + 1) := by rw [mul_add_one]
      _ ≤ ω ^ tbR e x * ω := mul_le_mul_right (Order.add_one_le_of_lt hn) _
      _ = ω ^ (tbR e x + 1) := by rw [opow_add, opow_one]

theorem tbR_mono {b c : Ordinal.{0}} (hc : c < tbB) (hbc : b < c) (hgb : tbG b < x) (hgc : tbG c < x) :
    tbR b x < tbR c x := (tb_ord hx hx1 c hc hgc).1 b hbc hgb

/-- `Γ_{x+1}·2 ≤ e(x)` for every code `e ≥ Γ_{Ω₁+1}·2` with gate below `x`. -/
theorem tbR_two {e : Ordinal.{0}} (he : gcG 0 + gcG 0 ≤ e) (heB : e < tbB) (hg : tbG e < x) :
    lgG x * 2 ≤ tbR e x := by
  obtain ⟨t1, t2⟩ := tb_two x
  rcases he.lt_or_eq with h | h
  · rw [← t1]; exact (tbR_mono hx hx1 heB h (by rw [t2]; exact hx.pos) hg).le
  · rw [← h, t1]

/-- **Every reading is below `ε_{Γ_{x+1}+1}`.** -/
theorem tbR_lt : ∀ c, c < tbB → tbG c < x → tbR c x < eN (lgG x) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  have hE := eN_E (lgG x)
  rcases lt_or_ge c mqB with hQ | hQ
  · rw [tbR_low hQ]
    rw [tbG_low hQ] at hg
    exact (tbMq_lt_sq hx hx1 hQ hg).trans (InE.mul_lt hE (lt_eN _) (lt_eN _))
  · obtain ⟨-, hec, -, -, -, -, -⟩ := tb_parts hQ hc
    have hg' := hg
    rw [tbG_hi hQ hc] at hg'
    have he := IH _ hec (hec.trans hc) (lt_of_le_of_lt (le_max_left _ _) hg')
    exact ((tb_ord hx hx1 c hc hg).2 hQ).trans (hE.opow_lt ((ev_isSuccLimit_of_inE hE).add_one_lt he))

/-- **Every `ν < ε_{Γ_{x+1}+1}` is the reading of a code `c < ε_{Γ_{Ω₁+1}+1}` with gate below `x`.** -/
theorem tbR_ex : ∀ ν, ν < eN (lgG x) → ∃ c, c < tbB ∧ tbG c < x ∧ tbR c x = ν := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  have hGE := (lgG_facts hx hx1).2.2.2.1
  rcases lt_or_ge ν (lgG x * lgG x) with hsq | hsq
  · obtain ⟨c, hc, hg, hr⟩ := tbMq_ex hx hx1 hsq
    exact ⟨c, hc.trans tbQ_lt_B, by rw [tbG_low hc]; exact hg, by rw [tbR_low hc]; exact hr⟩
  have hν0 : ν ≠ 0 := (lt_of_lt_of_le (mul_pos (lgG_pos hx hx1) (lgG_pos hx hx1)) hsq).ne'
  -- `ν = ω^E·N + W`
  set E := log ω ν with hEdef
  have hE2 : lgG x * 2 ≤ E := le_log_of_opow_le one_lt_omega0 (by rw [← tb_sq_eq hx hx1]; exact hsq)
  have hEν : E < ν := by
    refine lt_of_le_of_ne (log_le_self ω ν) fun he => ?_
    have h3 : ω ^ ν ≤ ν := by have := opow_log_le_self ω hν0; rwa [← hEdef, he] at this
    have hνE : InE ν := le_antisymm h3 (right_le_opow ν one_lt_omega0)
    have hGν : lgG x < ν := by
      refine lt_of_lt_of_le ?_ hsq
      conv_lhs => rw [← mul_one (lgG x)]
      exact (mul_lt_mul_iff_right₀ (lgG_pos hx hx1)).2 (Lu.lu_one_lt_E hGE)
    exact absurd hν (not_lt.2 (eN_le hGν hνE))
  have hp : ω ^ E ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hN : ν / ω ^ E < ω := div_opow_log_lt ν one_lt_omega0
  have hN0 : 0 < ν / ω ^ E := div_opow_log_pos ω hν0
  have hW : ν % ω ^ E < ω ^ E := Ordinal.mod_lt ν hp
  have hWν : ν % ω ^ E < ν := hW.trans_le (opow_log_le_self ω hν0)
  obtain ⟨e, heB, hge, hre⟩ := IH E hEν (hEν.trans hν)
  obtain ⟨w, hwB, hgw, hrw⟩ := IH _ hWν (hWν.trans hν)
  obtain ⟨t1, t2⟩ := tb_two x
  have he2 : gcG 0 + gcG 0 ≤ e := by
    by_contra hlt
    push Not at hlt
    have := tbR_mono hx hx1 ((tbMq_two x).1.trans tbQ_lt_B) hlt hge (by rw [t2]; exact hx.pos)
    rw [hre, t1] at this
    exact absurd hE2 (not_le.2 this)
  -- `ω^e` is a code reading `ω^E`
  have hmk1 := tb_mk he2 heB one_pos one_lt_omega0 (opow_pos e omega0_pos)
  have hr1 : tbR (ω ^ e * 1 + 0) x = ω ^ E := by
    rw [tbR_mk he2 heB one_pos one_lt_omega0 (opow_pos e omega0_pos), tbR_zero, hre, mul_one, add_zero]
  have hg1 : tbG (ω ^ e * 1 + 0) < x := by
    rw [tbG_mk he2 heB one_pos one_lt_omega0 (opow_pos e omega0_pos), tbG_zero]
    exact max_lt hge hx.pos
  have hwe : w < ω ^ e := by
    by_contra hge'
    push Not at hge'
    have h1 : ω ^ e * 1 + 0 ≤ w := by rw [mul_one, add_zero]; exact hge'
    rcases h1.lt_or_eq with h | h
    · have := tbR_mono hx hx1 hwB h hg1 hgw
      rw [hr1, hrw] at this
      exact absurd hW (not_lt.2 this.le)
    · rw [← h, hr1] at hrw
      exact absurd hW (by rw [← hrw]; exact lt_irrefl _)
  refine ⟨ω ^ e * (ν / ω ^ E) + w, (tb_mk he2 heB hN0 hN hwe).2.1, ?_, ?_⟩
  · rw [tbG_mk he2 heB hN0 hN hwe]; exact max_lt hge hgw
  · rw [tbR_mk he2 heB hN0 hN hwe, hre, hrw]; exact Ordinal.div_add_mod ν (ω ^ E)

end Base

end Googology.Trans.PoR.InaccPsi.R2.Tb
