import Googology.Trans.PoR.InaccPsi.R2.GeTow

/-!
# Codes below `ε_{Ω₁+1}`: hereditary Cantor normal forms in `Ω₁` and their readings `Ω₁ ↦ x`

A code `a < ε_{Ω₁+1}` (`a ≠ 0`) is `Ω₁^l · q + r` with `l = log_{Ω₁} a < a`, a digit `0 < q < Ω₁` and `r < Ω₁^l`.  Its
**reading** at a base `x` is `rdc a x = x^{rdc l x} · q + rdc r x` (well-founded recursion on the code); its **gate**
`gtc a` is the largest digit occurring in it, hereditarily.  For codes below `Ω₁^ω` this is the reading of `R2.GeSub`.

* `gfE = ε_{Ω₁+1}`, `lt_Om1_pow` (`l < Ω₁^l` below `gfE`), `cnf_parts`, `rdc_dec` / `gtc_dec` (the recursion equations),
  `rdc_cnf` (the equations for every normal form `Ω₁^l·q + r`), `rdc_const` (a code `c < Ω₁` reads `c`);
* `rdc_mono` (**the reading is strictly increasing**), `rdc_lt_pow` (`r < Ω₁^c ⇒ rdc r x < x^{rdc c x}`), `rdc_surj`
  (**every `ν < rdc a x` is the reading of a code `b < a` with gate below `x`**), `rdc_lt_eN` (`rdc a x < ε_{x+1}`);
* the terms: `kmul` (`ω^{x+s}·q`), `tcx a` (**the term of `x · rdc a x`**), `tc a` (**the term of `rdc a x`**),
  `ev_tcx`, `ev_tc`, `cb_tcx`, `cb_tc`; `rdc_pi` (**Lemma EXACT for every code**, from `R2.pi_ev`);
* `rdc_succ` (`rdc (a+1) x = rdc a x + 1`, the gate moves by at most one), `rdc_lim` (**the last term of a limit code**:
  `rdc a x = rdc a' x + ω^{x·rdc l x + d}` with `ω^{x·rdc l x + d} ∣ rdc a' x`, uniformly above the gate),
  `rdc_lim_facts`
  (`logend(rdc a x) = x·rdc l x + d`, the value of the term `add (tcx l) (k d)`).

No new axiom.  New definitions: `gfE`, `rdc`, `gtc`, `kmul`, `tcx`, `mpred`, `tc`, `tlg`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- **The bound of the codes**: `ε_{Ω₁+1}`. -/
noncomputable def gfE : Ordinal.{0} := eN Om1

theorem gf_one_lt_Om1 : (1 : Ordinal.{0}) < Om1 := Lu.lu_one_lt_E Rj.rj_Om1_inE

theorem Om1_ne' : Om1 ≠ 0 := (zero_lt_one.trans gf_one_lt_Om1).ne'

theorem Om1_pow_eq (l : Ordinal.{0}) : Om1 ^ l = ω ^ (Om1 * l) := by
  rw [opow_mul, show ω ^ Om1 = Om1 from Rj.rj_Om1_inE]

theorem Om1_pow_ne (l : Ordinal.{0}) : Om1 ^ l ≠ 0 := opow_ne_zero _ Om1_ne'

theorem Om1_lt_eW : Om1 < gfE := lt_eN Om1

theorem eW_E : InE gfE := eN_E Om1

/-- **`l < Ω₁^l` for every `l < ε_{Ω₁+1}`.** -/
theorem lt_Om1_pow {l : Ordinal.{0}} (hl : l < gfE) : l < Om1 ^ l := by
  rcases (right_le_opow l gf_one_lt_Om1).lt_or_eq with h | h
  · exact h
  exfalso
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [opow_zero] at h
    exact zero_ne_one h
  have e : ω ^ (Om1 * l) = l := by rw [← Om1_pow_eq]; exact h.symm
  have h1 : Om1 * l ≤ l := by
    calc Om1 * l ≤ ω ^ (Om1 * l) := right_le_opow _ one_lt_omega0
      _ = l := e
  have h2 : Om1 * l = l := le_antisymm h1 (le_mul_right l (zero_lt_one.trans gf_one_lt_Om1))
  have hE : InE l := by unfold InE; rw [h2] at e; exact e
  have hΩl : Om1 ≤ l := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * l := mul_le_mul_left' (one_le_iff_ne_zero.2 hl0) _
      _ = l := h2
  rcases hΩl.lt_or_eq with hlt | heq
  · exact absurd (eN_le hlt hE) (not_le.2 hl)
  · have : Om1 < Om1 * Om1 := lt_mul_of_one_lt_right (zero_lt_one.trans gf_one_lt_Om1) gf_one_lt_Om1
    rw [heq] at this h2
    rw [h2] at this
    exact lt_irrefl _ this

theorem log_lt {a : Ordinal.{0}} (ha : a ≠ 0) (haW : a < gfE) : log Om1 a < a :=
  (lt_Om1_pow ((log_le_self Om1 a).trans_lt haW)).trans_le (opow_log_le_self Om1 ha)

theorem Om1_pow_lt_eW {l : Ordinal.{0}} (hl : l < gfE) : Om1 ^ l < gfE := by
  rw [Om1_pow_eq]
  have h : Om1 * l < gfE := eW_E.mul_lt Om1_lt_eW hl
  have := (opow_lt_opow_iff_right one_lt_omega0).2 h
  rwa [show ω ^ gfE = gfE from eW_E] at this

/-! ## The reading and the gate -/

/-- **The reading at the base `x`** of a code: `rdc (Ω₁^l·q + r) x = x^{rdc l x}·q + rdc r x`. -/
noncomputable def rdc (a x : Ordinal.{0}) : Ordinal.{0} :=
  if h : a ≠ 0 ∧ log Om1 a < a then
    x ^ rdc (log Om1 a) x * (a / Om1 ^ log Om1 a) + rdc (a % Om1 ^ log Om1 a) x
  else 0
termination_by a
decreasing_by
  all_goals first
    | exact h.2
    | exact mod_opow_log_lt_self Om1 h.1

/-- **The gate** of a code: its largest digit, hereditarily. -/
noncomputable def gtc (a : Ordinal.{0}) : Ordinal.{0} :=
  if h : a ≠ 0 ∧ log Om1 a < a then
    max (max (gtc (log Om1 a)) (a / Om1 ^ log Om1 a)) (gtc (a % Om1 ^ log Om1 a))
  else 0
termination_by a
decreasing_by
  all_goals first
    | exact h.2
    | exact mod_opow_log_lt_self Om1 h.1

theorem rdc_zero (x : Ordinal.{0}) : rdc 0 x = 0 := by
  rw [rdc, dif_neg (by simp)]

theorem gtc_zero : gtc 0 = 0 := by
  rw [gtc, dif_neg (by simp)]

theorem rdc_dec' {a : Ordinal.{0}} (h : a ≠ 0 ∧ log Om1 a < a) (x : Ordinal.{0}) :
    rdc a x = x ^ rdc (log Om1 a) x * (a / Om1 ^ log Om1 a) + rdc (a % Om1 ^ log Om1 a) x := by
  rw [rdc, dif_pos h]

theorem gtc_dec' {a : Ordinal.{0}} (h : a ≠ 0 ∧ log Om1 a < a) :
    gtc a = max (max (gtc (log Om1 a)) (a / Om1 ^ log Om1 a)) (gtc (a % Om1 ^ log Om1 a)) := by
  rw [gtc, dif_pos h]

theorem rdc_dec {a : Ordinal.{0}} (ha : a ≠ 0) (haW : a < gfE) (x : Ordinal.{0}) :
    rdc a x = x ^ rdc (log Om1 a) x * (a / Om1 ^ log Om1 a) + rdc (a % Om1 ^ log Om1 a) x :=
  rdc_dec' ⟨ha, log_lt ha haW⟩ x

theorem gtc_dec {a : Ordinal.{0}} (ha : a ≠ 0) (haW : a < gfE) :
    gtc a = max (max (gtc (log Om1 a)) (a / Om1 ^ log Om1 a)) (gtc (a % Om1 ^ log Om1 a)) :=
  gtc_dec' ⟨ha, log_lt ha haW⟩

/-- The parts of a nonzero code. -/
theorem parts {a : Ordinal.{0}} (ha : a ≠ 0) :
    0 < a / Om1 ^ log Om1 a ∧ a / Om1 ^ log Om1 a < Om1 ∧ a % Om1 ^ log Om1 a < Om1 ^ log Om1 a ∧
      Om1 ^ log Om1 a * (a / Om1 ^ log Om1 a) + a % Om1 ^ log Om1 a = a ∧ a % Om1 ^ log Om1 a < a ∧
      Om1 ^ log Om1 a ≤ a :=
  ⟨div_opow_log_pos Om1 ha, div_opow_log_lt a gf_one_lt_Om1, Ordinal.mod_lt a (Om1_pow_ne _),
    Ordinal.div_add_mod a _, mod_opow_log_lt_self Om1 ha, opow_log_le_self Om1 ha⟩

theorem gtc_parts {a : Ordinal.{0}} (ha : a ≠ 0) (haW : a < gfE) :
    gtc (log Om1 a) ≤ gtc a ∧ a / Om1 ^ log Om1 a ≤ gtc a ∧ gtc (a % Om1 ^ log Om1 a) ≤ gtc a := by
  rw [gtc_dec ha haW]
  exact ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩

/-- **The normal form `Ω₁^l·q + r`**: its logarithm, digit and rest. -/
theorem cnf_parts {l q r : Ordinal.{0}} (hq0 : q ≠ 0) (hq : q < Om1) (hr : r < Om1 ^ l) :
    log Om1 (Om1 ^ l * q + r) = l ∧ (Om1 ^ l * q + r) / Om1 ^ l = q ∧ (Om1 ^ l * q + r) % Om1 ^ l = r := by
  refine ⟨?_, ?_, ?_⟩
  · rw [log_opow_mul_add gf_one_lt_Om1 hq0 hr, log_eq_zero hq, add_zero]
  · rw [Ordinal.mul_add_div q (Om1_pow_ne l) r, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- **The recursion equations at every normal form** `Ω₁^l·q + r` (`l < ε_{Ω₁+1}`, `0 < q < Ω₁`, `r < Ω₁^l`). -/
theorem rdc_cnf {l q r : Ordinal.{0}} (hl : l < gfE) (hq0 : q ≠ 0) (hq : q < Om1) (hr : r < Om1 ^ l)
    (x : Ordinal.{0}) :
    rdc (Om1 ^ l * q + r) x = x ^ rdc l x * q + rdc r x ∧ gtc (Om1 ^ l * q + r) = max (max (gtc l) q) (gtc r) := by
  obtain ⟨e1, e2, e3⟩ := cnf_parts hq0 hq hr
  have hne : Om1 ^ l * q + r ≠ 0 := by
    have : 0 < Om1 ^ l * q := mul_pos (opow_pos _ (zero_lt_one.trans gf_one_lt_Om1)) (pos_iff_ne_zero.2 hq0)
    exact (lt_of_lt_of_le this le_self_add).ne'
  have hlt : log Om1 (Om1 ^ l * q + r) < Om1 ^ l * q + r := by
    rw [e1]
    exact (lt_Om1_pow hl).trans_le ((le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hq0)).trans le_self_add)
  rw [rdc_dec' ⟨hne, hlt⟩, gtc_dec' ⟨hne, hlt⟩, e1, e2, e3]
  exact ⟨rfl, rfl⟩

/-- **A code `c < Ω₁` reads `c`** and is its own gate. -/
theorem rdc_const {c : Ordinal.{0}} (hc : c < Om1) (x : Ordinal.{0}) : rdc c x = c ∧ gtc c = c := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨rdc_zero x, gtc_zero⟩
  have h0W : (0 : Ordinal.{0}) < gfE := (zero_lt_one.trans gf_one_lt_Om1).trans Om1_lt_eW
  obtain ⟨h1, h2⟩ := rdc_cnf (l := 0) (r := 0) h0W hc0 hc (by rw [opow_zero]; exact zero_lt_one) x
  simp only [opow_zero, one_mul, add_zero, rdc_zero, gtc_zero] at h1 h2
  refine ⟨h1, ?_⟩
  rw [h2]
  try simp [max_eq_right, max_eq_left]

/-! ## Order -/

section Order

variable {x : Ordinal.{0}} (hx : InE x)
include hx

theorem rdc_pos {a : Ordinal.{0}} (ha : a ≠ 0) (haW : a < gfE) : 0 < rdc a x := by
  rw [rdc_dec ha haW]
  exact lt_of_lt_of_le (mul_pos (opow_pos _ hx.pos) (parts ha).1) le_self_add

theorem pw_mul_lt {L q R : Ordinal.{0}} (hq : q < x) (hR : R < x ^ L) : x ^ L * q + R < x ^ (L + 1) := by
  calc x ^ L * q + R < x ^ L * q + x ^ L := (add_lt_add_iff_left _).2 hR
    _ = x ^ L * (q + 1) := by rw [mul_add_one]
    _ ≤ x ^ L * x := mul_le_mul_left' (add_one_le_of_lt hq) _
    _ = x ^ (L + 1) := by rw [opow_add, opow_one]

/-- **The reading is strictly increasing, and `r < Ω₁^c ⇒ rdc r x < x^{rdc c x}`** (codes with gate below `x`). -/
theorem rdc_mono_bound : ∀ a, a < gfE →
    (∀ b, b < a → gtc a < x → gtc b < x → rdc b x < rdc a x) ∧
    (∀ r, r < Om1 ^ a → gtc a < x → gtc r < x → rdc r x < x ^ rdc a x) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haW
  have hM : ∀ b, b < a → gtc a < x → gtc b < x → rdc b x < rdc a x := by
    intro b hba hga hgb
    have ha0 : a ≠ 0 := (lt_of_le_of_lt zero_le hba).ne'
    obtain ⟨hq0, -, hr, hdec, hra, hpa⟩ := parts ha0
    obtain ⟨gl, gq, gr⟩ := gtc_parts ha0 haW
    set l := log Om1 a with hl
    set q := a / Om1 ^ l with hq
    set r := a % Om1 ^ l with hrr
    have hla : l < a := log_lt ha0 haW
    have hRa : rdc a x = x ^ rdc l x * q + rdc r x := rdc_dec ha0 haW x
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [rdc_zero]; exact rdc_pos hx ha0 haW
    have hbW : b < gfE := hba.trans haW
    obtain ⟨hq0', -, hr', hdec', -, -⟩ := parts hb0
    obtain ⟨gl', gq', gr'⟩ := gtc_parts hb0 hbW
    set l' := log Om1 b with hl'
    set q' := b / Om1 ^ l' with hq'
    set r' := b % Om1 ^ l' with hrr'
    have hlb : l' < b := log_lt hb0 hbW
    have hRb : rdc b x = x ^ rdc l' x * q' + rdc r' x := rdc_dec hb0 hbW x
    have hll : l' ≤ l := log_mono_right Om1 hba.le
    have hBl' := (IH l' (hlb.trans hba) (hlb.trans hbW)).2 r' hr' (gl'.trans_lt hgb) (gr'.trans_lt hgb)
    have hq'x : q' < x := gq'.trans_lt hgb
    have hqx : q < x := gq.trans_lt hga
    have hxL : x ^ rdc l x ≤ rdc a x := by
      rw [hRa]; exact (le_mul_of_one_le_right' (one_le_iff_pos.2 hq0)).trans le_self_add
    rcases hll.lt_or_eq with hll | hll
    · have hLL := (IH l hla (hla.trans haW)).1 l' hll (gl.trans_lt hga) (gl'.trans_lt hgb)
      rw [hRb]
      exact (pw_mul_lt hx hq'x hBl').trans_le ((opow_le_opow_right hx.pos (add_one_le_of_lt hLL)).trans hxL)
    · have hqq : q' ≤ q := by
        rw [hq', hq, hll]; exact div_le_left hba.le _
      rcases hqq.lt_or_eq with hqq | hqq
      · rw [hRb, hRa, hll]
        rw [hll] at hBl'
        calc x ^ rdc l x * q' + rdc r' x < x ^ rdc l x * q' + x ^ rdc l x := (add_lt_add_iff_left _).2 hBl'
          _ = x ^ rdc l x * (q' + 1) := by rw [mul_add_one]
          _ ≤ x ^ rdc l x * q := mul_le_mul_left' (add_one_le_of_lt hqq) _
          _ ≤ x ^ rdc l x * q + rdc r x := le_self_add
      · have hrr2 : r' < r := by
          have h2 : Om1 ^ l * q + r' < Om1 ^ l * q + r := by
            have e1 : Om1 ^ l * q + r' = b := by rw [← hll, ← hqq]; exact hdec'
            rw [e1, hdec]; exact hba
          exact (add_lt_add_iff_left _).1 h2
        have hm := (IH r hra (hra.trans haW)).1 r' hrr2 (gr.trans_lt hga) (gr'.trans_lt hgb)
        rw [hRb, hRa, hll, hqq]
        exact (add_lt_add_iff_left _).2 hm
  refine ⟨hM, ?_⟩
  intro r hr hga hgr
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [rdc_zero]; exact opow_pos _ hx.pos
  have hrW : r < gfE := hr.trans (Om1_pow_lt_eW haW)
  have ha0 : a ≠ 0 := by rintro rfl; rw [opow_zero, Ordinal.lt_one_iff_zero] at hr; exact hr0 hr
  obtain ⟨-, -, hrr, -, -, -⟩ := parts hr0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hr0 hrW
  have hlr : log Om1 r < a := (lt_opow_iff_log_lt gf_one_lt_Om1 hr0).1 hr
  have hB := (IH _ hlr (hlr.trans haW)).2 _ hrr (gl.trans_lt hgr) (gr.trans_lt hgr)
  have hLL := hM _ hlr hga (gl.trans_lt hgr)
  rw [rdc_dec hr0 hrW]
  exact (pw_mul_lt hx (gq.trans_lt hgr) hB).trans_le (opow_le_opow_right hx.pos (add_one_le_of_lt hLL))

/-- **The reading is strictly increasing** on the codes with gate below `x`. -/
theorem rdc_mono {a b : Ordinal.{0}} (haW : a < gfE) (hba : b < a) (hga : gtc a < x) (hgb : gtc b < x) :
    rdc b x < rdc a x :=
  (rdc_mono_bound hx a haW).1 b hba hga hgb

theorem rdc_le_mono {a b : Ordinal.{0}} (haW : a < gfE) (hba : b ≤ a) (hga : gtc a < x) (hgb : gtc b < x) :
    rdc b x ≤ rdc a x := by
  rcases hba.lt_or_eq with h | rfl
  · exact (rdc_mono hx haW h hga hgb).le
  · exact le_rfl

theorem rdc_lt_pow {c r : Ordinal.{0}} (hcW : c < gfE) (hr : r < Om1 ^ c) (hgc : gtc c < x) (hgr : gtc r < x) :
    rdc r x < x ^ rdc c x :=
  (rdc_mono_bound hx c hcW).2 r hr hgc hgr

/-- **The reading reflects the order.** -/
theorem lt_of_rdc_lt {a b : Ordinal.{0}} (haW : a < gfE) (hbW : b < gfE) (hga : gtc a < x) (hgb : gtc b < x)
    (h : rdc a x < rdc b x) : a < b := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.2 (rdc_le_mono hx haW hle hga hgb))

/-- **The reading lies below `ε_{x+1}`.** -/
theorem rdc_lt_eN : ∀ a, gtc a < x → rdc a x < eN x := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro hg
  by_cases h : a ≠ 0 ∧ log Om1 a < a
  · have hE := eN_E x
    rw [rdc_dec' h]
    rw [gtc_dec' h] at hg
    simp only [max_lt_iff] at hg
    have hL := IH _ h.2 hg.1.1
    have hR := IH _ (mod_opow_log_lt_self Om1 h.1) hg.2
    have hxL : x * rdc (log Om1 a) x < eN x := hE.mul_lt (lt_eN x) hL
    have hP : x ^ rdc (log Om1 a) x < eN x := by
      rw [show x ^ rdc (log Om1 a) x = ω ^ (x * rdc (log Om1 a) x) by
        rw [opow_mul, show ω ^ x = x from hx]]
      have := (opow_lt_opow_iff_right one_lt_omega0).2 hxL
      rwa [show ω ^ eN x = eN x from hE] at this
    exact (inE_indec hE).add_lt (hE.mul_lt hP (hg.1.2.trans (lt_eN x))) hR
  · rw [rdc, dif_neg h]; exact (eN_E x).pos

end Order

/-! ## Surjectivity -/

section Surj

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x ≤ Om1)
include hx hx1

theorem rdc_surj_aux : ∀ c, c < gfE → gtc c < x →
    (∀ v, v < rdc c x → ∃ l', l' < c ∧ gtc l' < x ∧ rdc l' x = v) ∧
    (∀ ν, ν < x ^ rdc c x → ∃ b, b < Om1 ^ c ∧ gtc b < x ∧ rdc b x = ν) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcW hgc
  have hx0 : x ≠ 0 := hx.pos.ne'
  have hx1' : (1 : Ordinal.{0}) < x := Lu.lu_one_lt_E hx
  have S1 : ∀ v, v < rdc c x → ∃ l', l' < c ∧ gtc l' < x ∧ rdc l' x = v := by
    intro v hv
    have hc0 : c ≠ 0 := by rintro rfl; rw [rdc_zero] at hv; exact absurd hv (not_lt.2 zero_le)
    obtain ⟨hq0, hqΩ, hr, hdec, hrc, hpc⟩ := parts hc0
    obtain ⟨gl, gq, gr⟩ := gtc_parts hc0 hcW
    set l := log Om1 c with hl
    set q := c / Om1 ^ l with hq
    set r := c % Om1 ^ l with hrr
    have hlc : l < c := log_lt hc0 hcW
    have hlW : l < gfE := hlc.trans hcW
    rw [rdc_dec hc0 hcW] at hv
    have hxL0 : x ^ rdc l x ≠ 0 := opow_ne_zero _ hx0
    rcases lt_or_ge v (x ^ rdc l x * q) with hlt | hge
    · set q2 := v / x ^ rdc l x with hq2
      set v2 := v % x ^ rdc l x with hv2
      have hq2q : q2 < q := (Ordinal.div_lt hxL0).2 hlt
      have hv2L : v2 < x ^ rdc l x := Ordinal.mod_lt v hxL0
      obtain ⟨b2, hb2, hgb2, hrb2⟩ := (IH l hlc hlW (gl.trans_lt hgc)).2 v2 hv2L
      rcases eq_or_ne q2 0 with hq20 | hq20
      · have hvv : v = v2 := by
          have e := Ordinal.div_add_mod v (x ^ rdc l x)
          rw [← hq2, ← hv2, hq20, mul_zero, zero_add] at e
          exact e.symm
        exact ⟨b2, hb2.trans_le hpc, hgb2, by rw [hrb2, hvv]⟩
      · obtain ⟨e1, e2⟩ := rdc_cnf hlW hq20 (hq2q.trans hqΩ) hb2 x
        refine ⟨Om1 ^ l * q2 + b2, ?_, ?_, ?_⟩
        · calc Om1 ^ l * q2 + b2 < Om1 ^ l * q2 + Om1 ^ l := (add_lt_add_iff_left _).2 hb2
            _ = Om1 ^ l * (q2 + 1) := by rw [mul_add_one]
            _ ≤ Om1 ^ l * q := mul_le_mul_left' (add_one_le_of_lt hq2q) _
            _ ≤ Om1 ^ l * q + r := le_self_add
            _ = c := hdec
        · rw [e2]
          exact max_lt (max_lt (gl.trans_lt hgc) (hq2q.trans_le gq |>.trans hgc)) hgb2
        · rw [e1, hrb2, hq2, hv2, Ordinal.div_add_mod]
    · obtain ⟨μ, hμ⟩ : ∃ μ, v = x ^ rdc l x * q + μ := ⟨v - x ^ rdc l x * q, (Ordinal.add_sub_cancel_of_le hge).symm⟩
      have hμr : μ < rdc r x := by rw [hμ] at hv; exact (add_lt_add_iff_left _).1 hv
      obtain ⟨r2, hr2, hgr2, hrr2⟩ := (IH r hrc (hrc.trans hcW) (gr.trans_lt hgc)).1 μ hμr
      obtain ⟨e1, e2⟩ := rdc_cnf hlW hq0.ne' hqΩ (hr2.trans hr) x
      refine ⟨Om1 ^ l * q + r2, ?_, ?_, ?_⟩
      · rw [← hdec]; exact (add_lt_add_iff_left _).2 hr2
      · rw [e2]; exact max_lt (max_lt (gl.trans_lt hgc) (gq.trans_lt hgc)) hgr2
      · rw [e1, hrr2, hμ]
  refine ⟨S1, ?_⟩
  intro ν hν
  rcases eq_or_ne ν 0 with rfl | hν0
  · exact ⟨0, opow_pos _ (zero_lt_one.trans gf_one_lt_Om1), by rw [gtc_zero]; exact hx.pos, rdc_zero x⟩
  set v := log x ν with hv
  have hvc : v < rdc c x := (lt_opow_iff_log_lt hx1' hν0).1 hν
  obtain ⟨l', hl'c, hgl', hrl'⟩ := S1 v hvc
  have hl'W : l' < gfE := hl'c.trans hcW
  set q' := ν / x ^ v with hq'
  set ν' := ν % x ^ v with hν'
  have hq'0 : q' ≠ 0 := (div_opow_log_pos x hν0).ne'
  have hq'x : q' < x := div_opow_log_lt ν hx1'
  have hν'L : ν' < x ^ v := Ordinal.mod_lt ν (opow_ne_zero _ hx0)
  rw [← hrl'] at hν'L
  obtain ⟨b', hb', hgb', hrb'⟩ := (IH l' hl'c hl'W hgl').2 ν' hν'L
  obtain ⟨e1, e2⟩ := rdc_cnf hl'W hq'0 (hq'x.trans_le hx1) hb' x
  refine ⟨Om1 ^ l' * q' + b', ?_, ?_, ?_⟩
  · calc Om1 ^ l' * q' + b' < Om1 ^ l' * q' + Om1 ^ l' := (add_lt_add_iff_left _).2 hb'
      _ = Om1 ^ l' * (q' + 1) := by rw [mul_add_one]
      _ ≤ Om1 ^ l' * Om1 := mul_le_mul_left' (add_one_le_of_lt (hq'x.trans_le hx1)) _
      _ = Om1 ^ (l' + 1) := by rw [opow_add, opow_one]
      _ ≤ Om1 ^ c := opow_le_opow_right (zero_lt_one.trans gf_one_lt_Om1) (add_one_le_of_lt hl'c)
  · rw [e2]; exact max_lt (max_lt hgl' hq'x) hgb'
  · rw [e1, hrb', hrl', hq', hν', Ordinal.div_add_mod]

/-- **Every `ν < rdc a x` is the reading of a code `b < a` with gate below `x`** (`x ≤ Ω₁`). -/
theorem rdc_surj {a : Ordinal.{0}} (haW : a < gfE) (hg : gtc a < x) {ν : Ordinal.{0}} (hν : ν < rdc a x) :
    ∃ b, b < a ∧ gtc b < x ∧ rdc b x = ν :=
  (rdc_surj_aux hx hx1 a haW hg).1 ν hν

end Surj

/-! ## Terms for the readings -/

theorem gf_sub_log_lt {q : Ordinal.{0}} (hq : q ≠ 0) : q - ω ^ log ω q < q := by
  have hp : ω ^ log ω q ≤ q := opow_log_le_self ω hq
  have hq' : q < ω ^ log ω q * ω := by
    have := lt_opow_succ_log_self one_lt_omega0 q
    rwa [opow_succ] at this
  by_contra h
  push Not at h
  have h1 : ω ^ log ω q + q ≤ q := by
    calc ω ^ log ω q + q ≤ ω ^ log ω q + (q - ω ^ log ω q) := add_le_add le_rfl h
      _ = q := Ordinal.add_sub_cancel_of_le hp
  have h2 : ω ^ log ω q + q = q := le_antisymm h1 le_add_self
  exact absurd (add_eq_right_iff_mul_omega0_le.1 h2) (not_le.2 hq')

/-- **The term of `ω^{x+s}·q`.** -/
noncomputable def kmul (s : OT) (q : Ordinal.{0}) : OT :=
  if h : q = 0 then OT.k 0 else OT.add (OT.xw (OT.add s (OT.k (log ω q)))) (kmul s (q - ω ^ log ω q))
termination_by q
decreasing_by exact gf_sub_log_lt h

theorem ev_kmul (s : OT) (x : Ordinal.{0}) : ∀ q : Ordinal.{0}, OT.ev (kmul s q) x = ω ^ (x + OT.ev s x) * q := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  rw [kmul]
  split_ifs with h
  · rw [h, mul_zero]; rfl
  · simp only [OT.ev_add, OT.ev_xw, OT.ev_k]
    rw [IH _ (gf_sub_log_lt h), ← add_assoc, opow_add, ← mul_add,
      Ordinal.add_sub_cancel_of_le (opow_log_le_self ω h)]

theorem cb_kmul {s : OT} {b : Ordinal.{0}} (hs : OT.CB s b) (hb : 0 < b) :
    ∀ q : Ordinal.{0}, q < b → OT.CB (kmul s q) b := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rw [kmul]
  split_ifs with h
  · exact hb
  · exact ⟨⟨hs, (log_le_self ω q).trans_lt hq⟩, IH _ (gf_sub_log_lt h) ((sub_le_self _ _).trans_lt hq)⟩

/-- **The term of `x · rdc a x`.** -/
noncomputable def tcx (a : Ordinal.{0}) : OT :=
  if h : a ≠ 0 ∧ log Om1 a < a then
    OT.add (kmul (tcx (log Om1 a)) (a / Om1 ^ log Om1 a)) (tcx (a % Om1 ^ log Om1 a))
  else OT.k 0
termination_by a
decreasing_by
  all_goals first
    | exact h.2
    | exact mod_opow_log_lt_self Om1 h.1

theorem pw_eq' {x : Ordinal.{0}} (hx : InE x) (L : Ordinal.{0}) : x ^ L = ω ^ (x * L) := by
  rw [opow_mul, show ω ^ x = x from hx]

theorem ev_tcx {x : Ordinal.{0}} (hx : InE x) : ∀ a : Ordinal.{0}, OT.ev (tcx a) x = x * rdc a x := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  by_cases h : a ≠ 0 ∧ log Om1 a < a
  · rw [tcx, dif_pos h, rdc_dec' h]
    simp only [OT.ev_add]
    rw [ev_kmul, IH _ h.2, IH _ (mod_opow_log_lt_self Om1 h.1), mul_add, ← mul_assoc, pw_eq' hx]
    rw [show x * ω ^ (x * rdc (log Om1 a) x) = ω ^ (x + x * rdc (log Om1 a) x) by
      rw [opow_add, show ω ^ x = x from hx]]
  · rw [tcx, dif_neg h, rdc, dif_neg h, mul_zero]; rfl

theorem cb_tcx {b : Ordinal.{0}} (hb : 0 < b) : ∀ a : Ordinal.{0}, gtc a < b → OT.CB (tcx a) b := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro hg
  by_cases h : a ≠ 0 ∧ log Om1 a < a
  · rw [gtc_dec' h] at hg
    simp only [max_lt_iff] at hg
    rw [tcx, dif_pos h]
    exact ⟨cb_kmul (IH _ h.2 hg.1.1) hb _ hg.1.2, IH _ (mod_opow_log_lt_self Om1 h.1) hg.2⟩
  · rw [tcx, dif_neg h]; exact hb

/-- `l ↦ l - 1` on the finite codes, the identity on the others: `1 + rdc (mpred l) x = rdc l x` for `l ≠ 0`. -/
noncomputable def mpred (l : Ordinal.{0}) : Ordinal.{0} := if l < ω then Ordinal.pred l else l

/-- **The term of `rdc a x`.** -/
noncomputable def tc (a : Ordinal.{0}) : OT :=
  if h : a ≠ 0 ∧ log Om1 a < a then
    OT.add (if log Om1 a = 0 then OT.k (a / Om1 ^ log Om1 a)
        else kmul (tcx (mpred (log Om1 a))) (a / Om1 ^ log Om1 a))
      (tc (a % Om1 ^ log Om1 a))
  else OT.k 0
termination_by a
decreasing_by exact mod_opow_log_lt_self Om1 h.1

theorem omega_lt_Om1 : ω < Om1 := omega0_lt_inE Rj.rj_Om1_inE

theorem mpred_facts {l : Ordinal.{0}} (hl0 : l ≠ 0) (hlW : l < gfE) {x : Ordinal.{0}} (hx : InE x) (hg : gtc l < x) :
    1 + rdc (mpred l) x = rdc l x ∧ gtc (mpred l) ≤ gtc l := by
  unfold mpred
  split_ifs with hω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hω
    have hn : n ≠ 0 := by rintro rfl; exact hl0 (by simp)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hp : Ordinal.pred ((m + 1 : ℕ) : Ordinal.{0}) = (m : Ordinal.{0}) := by
      rw [Nat.cast_succ, ← succ_eq_add_one, Ordinal.pred_succ]
    have hmΩ : (m : Ordinal.{0}) < Om1 := (natCast_lt_omega0 m).trans omega_lt_Om1
    have hm1Ω : ((m + 1 : ℕ) : Ordinal.{0}) < Om1 := (natCast_lt_omega0 _).trans omega_lt_Om1
    rw [hp, (rdc_const hmΩ x).1, (rdc_const hm1Ω x).1, (rdc_const hmΩ x).2, (rdc_const hm1Ω x).2]
    refine ⟨?_, by exact_mod_cast Nat.le_succ m⟩
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_cast, ← Nat.cast_add, Nat.add_comm]
  · push Not at hω
    refine ⟨?_, le_rfl⟩
    have hωc : rdc ω x = ω ∧ gtc ω = ω := rdc_const omega_lt_Om1 x
    have hge : ω ≤ rdc l x := by
      rw [← hωc.1]
      exact rdc_le_mono hx hlW hω hg (by rw [hωc.2]; exact omega0_lt_inE hx)
    exact one_add_of_omega0_le hge

theorem ev_tc {x : Ordinal.{0}} (hx : InE x) : ∀ a : Ordinal.{0}, a < gfE → gtc a < x → OT.ev (tc a) x = rdc a x := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haW hg
  by_cases h : a ≠ 0 ∧ log Om1 a < a
  · rw [tc, dif_pos h, rdc_dec' h]
    obtain ⟨gl, -, gr⟩ := gtc_parts h.1 haW
    have hr := IH _ (mod_opow_log_lt_self Om1 h.1) ((mod_opow_log_lt_self Om1 h.1).trans haW) (gr.trans_lt hg)
    simp only [OT.ev_add]
    rw [hr]
    congr 1
    split_ifs with hl0
    · simp only [OT.ev_k, hl0, rdc_zero, opow_zero, one_mul]
    · rw [ev_kmul, ev_tcx hx]
      obtain ⟨e1, -⟩ := mpred_facts hl0 (h.2.trans haW) hx (gl.trans_lt hg)
      rw [← mul_one_add, e1, pw_eq' hx]
  · rw [tc, dif_neg h, rdc, dif_neg h]; rfl

theorem cb_tc {b : Ordinal.{0}} (hb : 0 < b) : ∀ a : Ordinal.{0}, a < gfE → gtc a < b → OT.CB (tc a) b := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haW hg
  by_cases h : a ≠ 0 ∧ log Om1 a < a
  · obtain ⟨gl, gq, gr⟩ := gtc_parts h.1 haW
    rw [tc, dif_pos h]
    refine ⟨?_, IH _ (mod_opow_log_lt_self Om1 h.1) ((mod_opow_log_lt_self Om1 h.1).trans haW) (gr.trans_lt hg)⟩
    split_ifs with hl0
    · exact gq.trans_lt hg
    · refine cb_kmul (cb_tcx hb _ ?_) hb _ (gq.trans_lt hg)
      unfold mpred
      split_ifs with hω
      · have hpl : Ordinal.pred (log Om1 a) < Om1 := (Ordinal.pred_le_self _).trans_lt (hω.trans omega_lt_Om1)
        rw [(rdc_const hpl 0).2]
        have hlΩ : log Om1 a < Om1 := hω.trans omega_lt_Om1
        exact (Ordinal.pred_le_self _).trans_lt (by rw [← (rdc_const hlΩ 0).2]; exact gl.trans_lt hg)
      · exact gl.trans_lt hg
  · rw [tc, dif_neg h]; exact hb

/-- **Lemma EXACT for every code**: `π_{σ,ρ}(rdc a ρ) = rdc a σ` for the codes with gate below `σ`. -/
theorem rdc_pi {σ ρ a : Ordinal.{0}} (hB : Bases σ ρ) (haW : a < gfE) (hg : gtc a < σ) :
    rdc a ρ ∈ TB ρ σ ∧ pi σ ρ (rdc a ρ) = rdc a σ := by
  have hcb := cb_tc hB.1.pos a haW hg
  obtain ⟨h1, h2⟩ := pi_ev hB (tc a) hcb
  rw [ev_tc hB.2.1 a haW (hg.trans hB.2.2.1)] at h1 h2
  rw [ev_tc hB.1 a haW hg] at h2
  exact ⟨h1, h2⟩

/-! ## Successor and limit codes -/

theorem eW_indec : Indec gfE := inE_indec eW_E

theorem succ_lt_eW {a : Ordinal.{0}} (ha : a < gfE) : a + 1 < gfE :=
  eW_indec.add_lt ha (gf_one_lt_Om1.trans Om1_lt_eW)

/-- **The successor code**: `rdc (a+1) x = rdc a x + 1`, and the gate moves by at most one. -/
theorem rdc_succ : ∀ a, a < gfE → ∀ x : Ordinal.{0},
    rdc (a + 1) x = rdc a x + 1 ∧ gtc a ≤ gtc (a + 1) ∧ gtc (a + 1) ≤ gtc a + 1 := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haW x
  rcases lt_or_ge a Om1 with haΩ | hΩa
  · have ha1 : a + 1 < Om1 := Rj.rj_Om1_inE |> fun h => (inE_indec h).add_lt haΩ gf_one_lt_Om1
    rw [(rdc_const haΩ x).1, (rdc_const ha1 x).1, (rdc_const haΩ x).2, (rdc_const ha1 x).2]
    exact ⟨rfl, le_self_add, le_rfl⟩
  have ha0 : a ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans gf_one_lt_Om1) hΩa).ne'
  obtain ⟨hq0, hqΩ, hr, hdec, hra, -⟩ := parts ha0
  set l := log Om1 a with hl
  set q := a / Om1 ^ l with hq
  set r := a % Om1 ^ l with hrr
  have hl0 : l ≠ 0 := (log_pos gf_one_lt_Om1 ha0 hΩa).ne'
  have hlW : l < gfE := (log_lt ha0 haW).trans haW
  have hindec : Indec (Om1 ^ l) := by rw [Om1_pow_eq]; exact indec_opow _
  have h1l : (1 : Ordinal.{0}) < Om1 ^ l := by
    calc (1 : Ordinal.{0}) < Om1 := gf_one_lt_Om1
      _ = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ Om1 ^ l := opow_le_opow_right (zero_lt_one.trans gf_one_lt_Om1) (one_le_iff_ne_zero.2 hl0)
  have hr1 : r + 1 < Om1 ^ l := hindec.add_lt hr h1l
  obtain ⟨e1, e2⟩ := rdc_cnf hlW hq0.ne' hqΩ hr x
  obtain ⟨f1, f2⟩ := rdc_cnf hlW hq0.ne' hqΩ hr1 x
  obtain ⟨i1, i2, i3⟩ := IH r hra (hra.trans haW) x
  have ea : a + 1 = Om1 ^ l * q + (r + 1) := by rw [← add_assoc, hdec]
  rw [ea, f1, f2, ← hdec, e1, e2, i1, add_assoc]
  refine ⟨rfl, max_le_max le_rfl i2, ?_⟩
  exact max_le ((le_max_left _ _).trans le_self_add) (i3.trans (add_le_add (le_max_right _ _) le_rfl))

/-- **The last term of a limit code**: `a = a' + Ω₁^l·ω^d`, read uniformly above the gate as
`rdc a x = rdc a' x + ω^{x·rdc l x + d}` with `ω^{x·rdc l x + d} ∣ rdc a' x`; `l` at most the leading exponent. -/
theorem rdc_lim : ∀ a, IsSuccLimit a → a < gfE →
    ∃ a' l d : Ordinal.{0}, a' < a ∧ gtc a' ≤ gtc a ∧ gtc l ≤ gtc a ∧ d ≤ gtc a ∧ l ≤ log Om1 a ∧ l < gfE ∧
      (l ≠ 0 ∨ d ≠ 0) ∧
      ∀ x, InE x → gtc a < x →
        rdc a x = rdc a' x + ω ^ (x * rdc l x + d) ∧ ω ^ (x * rdc l x + d) ∣ rdc a' x := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro hlim haW
  have ha0 : a ≠ 0 := hlim.bot_lt.ne'
  obtain ⟨hq0, hqΩ, hr, hdec, hra, -⟩ := parts ha0
  obtain ⟨gl, gq, gr⟩ := gtc_parts ha0 haW
  set l := log Om1 a with hl
  set q := a / Om1 ^ l with hq
  set r := a % Om1 ^ l with hrr
  have hlW : l < gfE := (log_lt ha0 haW).trans haW
  rcases eq_or_ne r 0 with hr0 | hr0
  · -- `a = Ω₁^l · q`
    obtain ⟨q', hqs, hqd, hq'q⟩ := lg_split hq0.ne'
    have hd : lg q ≤ q := lg_le hq0.ne'
    have hq'Ω : q' < Om1 := hq'q.trans hqΩ
    have hra' : ∀ x, rdc (Om1 ^ l * q') x = x ^ rdc l x * q' := by
      intro x
      rcases eq_or_ne q' 0 with h0 | h0
      · rw [h0, mul_zero, mul_zero, rdc_zero]
      · have := (rdc_cnf hlW h0 hq'Ω (opow_pos l (zero_lt_one.trans gf_one_lt_Om1)) x).1
        rwa [add_zero, rdc_zero, add_zero] at this
    have hga' : gtc (Om1 ^ l * q') ≤ gtc a := by
      rcases eq_or_ne q' 0 with h0 | h0
      · rw [h0, mul_zero, gtc_zero]; exact zero_le
      · have := (rdc_cnf hlW h0 hq'Ω (opow_pos l (zero_lt_one.trans gf_one_lt_Om1)) 0).2
        rw [add_zero, gtc_zero, max_eq_left zero_le] at this
        rw [this]
        exact max_le gl (hq'q.le.trans gq)
    have hea : a = Om1 ^ l * q := by rw [← hdec, hr0, add_zero]
    refine ⟨Om1 ^ l * q', l, lg q, ?_, hga', gl, hd.trans gq, le_rfl, hlW, ?_, fun x hx hgx => ?_⟩
    · rw [hea]; exact (mul_lt_mul_iff_right₀ (opow_pos l (zero_lt_one.trans gf_one_lt_Om1))).2 hq'q
    · rcases eq_or_ne l 0 with hl0 | hl0
      · right
        have hqa : a = q := by rw [hea, hl0, opow_zero, one_mul]
        exact (Gc.gc_lg_pos (hqa ▸ hlim)).ne'
      · left; exact hl0
    · rw [hra' x]
      have hRa : rdc a x = x ^ rdc l x * q := by
        rw [rdc_dec ha0 haW, ← hrr, hr0, rdc_zero, add_zero]
      refine ⟨?_, ?_⟩
      · rw [hRa]
        conv_lhs => rw [hqs]
        rw [mul_add, pw_eq' hx, ← opow_add]
      · rw [pw_eq' hx, opow_add]
        exact mul_dvd_mul_left _ hqd
  · -- `a = Ω₁^l·q + r` with a limit `r ≠ 0`
    have hrlim : IsSuccLimit r := by
      rcases zero_or_succ_or_isSuccLimit r with h | ⟨s, hs⟩ | h
      · exact absurd h hr0
      · exfalso
        have hs' : r = s + 1 := by rw [← succ_eq_add_one]; first | exact hs | exact hs.symm
        have e3 : succ (Om1 ^ l * q + s) = a := by rw [succ_eq_add_one, ← hdec, hs', add_assoc]
        exact hlim.isSuccPrelimit.succ_ne _ e3
      · exact h
    obtain ⟨r', l2, d2, hr'r, hg', hgl2, hd2, hl2, hl2W, hpos, hR⟩ := IH r hra hrlim (hra.trans haW)
    have hlog : log Om1 r < l := (lt_opow_iff_log_lt gf_one_lt_Om1 hr0).1 hr
    have hl2l : l2 < l := hl2.trans_lt hlog
    obtain ⟨e1, e2⟩ := rdc_cnf hlW hq0.ne' hqΩ (hr'r.trans hr) 0
    refine ⟨Om1 ^ l * q + r', l2, d2, ?_, ?_, hgl2.trans gr, hd2.trans gr, ?_, hl2W, hpos, fun x hx hgx => ?_⟩
    · rw [← hdec]; exact (add_lt_add_iff_left _).2 hr'r
    · rw [e2]; exact max_le (max_le gl gq) (hg'.trans gr)
    · exact hl2l.le.trans le_rfl
    · have hgr : gtc r < x := gr.trans_lt hgx
      obtain ⟨h1, h2⟩ := hR x hx hgr
      have hc := (rdc_cnf hlW hq0.ne' hqΩ (hr'r.trans hr) x).1
      have hRa : rdc a x = x ^ rdc l x * q + rdc r x := rdc_dec ha0 haW x
      rw [hc, hRa, h1, add_assoc]
      refine ⟨rfl, Ge.dvd_add' ?_ h2⟩
      have hLL : rdc l2 x < rdc l x := rdc_mono hx hlW hl2l (gl.trans_lt hgx) (hgl2.trans_lt hgr)
      have hd2x : d2 < x := hd2.trans_lt hgr
      rw [pw_eq' hx]
      refine dvd_trans (opow_dvd_opow ω ?_) (dvd_mul_right _ _)
      calc x * rdc l2 x + d2 ≤ x * rdc l2 x + x := add_le_add le_rfl hd2x.le
        _ = x * (rdc l2 x + 1) := by rw [mul_add_one]
        _ ≤ x * rdc l x := mul_le_mul_left' (add_one_le_of_lt hLL) _

/-- **The logend term**: `add (tcx l) (k d)` reads `x·rdc l x + d`. -/
noncomputable def tlg (l d : Ordinal.{0}) : OT := OT.add (tcx l) (OT.k d)

theorem ev_tlg {x : Ordinal.{0}} (hx : InE x) (l d : Ordinal.{0}) : OT.ev (tlg l d) x = x * rdc l x + d := by
  unfold tlg; simp only [OT.ev_add, OT.ev_k]; rw [ev_tcx hx]

theorem cb_tlg {b l d : Ordinal.{0}} (hb : 0 < b) (hl : gtc l < b) (hd : d < b) : OT.CB (tlg l d) b :=
  ⟨cb_tcx hb l hl, hd⟩

/-- **A limit code reads a limit `≥ ω`**, with `logend = x·rdc l x + d` (the value of the term `tlg l d`). -/
theorem rdc_lim_facts {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) :
    ∃ a' l d : Ordinal.{0}, a' < a ∧ gtc a' ≤ gtc a ∧ gtc l ≤ gtc a ∧ d ≤ gtc a ∧ l < gfE ∧
      ∀ x, InE x → gtc a < x →
        rdc a x = rdc a' x + ω ^ lg (rdc a x) ∧ ω ^ lg (rdc a x) ∣ rdc a' x ∧
          lg (rdc a x) = OT.ev (tlg l d) x ∧ ω ≤ rdc a x ∧ 1 + rdc a x = rdc a x ∧ IsSuccLimit (rdc a x) := by
  obtain ⟨a', l, d, h1, h2, h3, h4, -, hlW, h5, h6⟩ := rdc_lim a hl ha
  refine ⟨a', l, d, h1, h2, h3, h4, hlW, fun x hx hgx => ?_⟩
  obtain ⟨e1, e2⟩ := h6 x hx hgx
  have hlg : lg (rdc a x) = x * rdc l x + d := by rw [e1]; exact Ge.lg_add_opow e2
  have hpos : 0 < x * rdc l x + d := by
    rcases h5 with hl0 | hd0
    · exact lt_of_lt_of_le (mul_pos hx.pos (rdc_pos hx hl0 hlW)) le_self_add
    · exact lt_of_lt_of_le (pos_iff_ne_zero.2 hd0) le_add_self
  have hω : ω ≤ rdc a x := by
    rw [e1]
    refine le_trans ?_ le_add_self
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ (x * rdc l x + d) := opow_le_opow_right omega0_pos (one_le_iff_pos.2 hpos)
  have hdvdω : ω ∣ rdc a x := by
    rw [e1]
    have h1' : ω ∣ ω ^ (x * rdc l x + d) := by
      calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ∣ ω ^ (x * rdc l x + d) := opow_dvd_opow ω (one_le_iff_pos.2 hpos)
    exact Ge.dvd_add' (dvd_trans h1' e2) h1'
  have hne : rdc a x ≠ 0 := (lt_of_lt_of_le omega0_pos hω).ne'
  refine ⟨?_, ?_, by rw [hlg, ev_tlg hx], hω, one_add_of_omega0_le hω, ?_⟩
  · rw [hlg]; exact e1
  · rw [hlg]; exact e2
  · exact ⟨not_isMin_iff_ne_bot.2 hne, isSuccPrelimit_iff_omega0_dvd.2 hdvdω⟩

end Googology.Trans.PoR.InaccPsi.R2.Gf
