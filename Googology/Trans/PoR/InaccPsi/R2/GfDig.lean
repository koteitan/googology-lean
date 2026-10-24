import Googology.Trans.PoR.InaccPsi.R2.GfTow
import Googology.Trans.PoR.InaccPsi.R2.GeDig

/-!
# The digits of sums and powers of hereditary codes: the codes over a closed base `Z` have their gate below `Z`

For the codes `a < ε_{Ω₁+1}` of `R2.GfSub` (hereditary Cantor normal forms in `Ω₁`, gate = the largest digit):

* `gtc_lt_Om1` (every digit is below `Ω₁`), `gtc_add` (**the digits of `a + b` are digits of `a`, of `b`, or sums of
  two digits**: below every additively closed `Z`), `one_add_mpred`, `gtc_mpred`, `gtc_div` (**`gtc (y/Ω₁) ≤ gtc y` and
  `y mod Ω₁ ≤ gtc y`**), `gtc_opow` (**`ω^y = Ω₁^{y/Ω₁}·ω^{y mod Ω₁}` has its gate below `Z`**), `eps_lt_eW` (**an
  `ε`-number below `ε_{Ω₁+1}` is at most `Ω₁`**), `rdc_Om1` (the code `Ω₁` reads `x`, gate `1`);
* `gfCode_gate` (**a code over `Z` below `ε_{Ω₁+1}`, with every atom above `ε_{Ω₁+1}`, has its gate below `Z`**, for
  `Z ≤ Ω₁` closed under `+` and `φ`);
* `gf_count` (**the codes below `a` with gate below `y < Ω₁` are countably many**: the reading at `y` is injective);
* `eW_eq` (**`ε_{Ω₁+1} = φ(1, Ω₁+1)`**, from `φ(1, Ω₁) = Ω₁`).

No new axiom.  New definition: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx

/-- **Every digit is below `Ω₁`.** -/
theorem gtc_lt_Om1 : ∀ a, a < gfE → gtc a < Om1 := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haW
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [gtc_zero]; exact zero_lt_one.trans gf_one_lt_Om1
  obtain ⟨-, hq, -, -, hra, -⟩ := parts ha0
  rw [gtc_dec ha0 haW]
  have hl := log_lt ha0 haW
  exact max_lt (max_lt (IH _ hl (hl.trans haW)) hq) (IH _ hra (hra.trans haW))

theorem Om1_pow_indec (l : Ordinal.{0}) : Indec (Om1 ^ l) := by rw [Om1_pow_eq]; exact indec_opow _

theorem lt_pow_succ_log {b : Ordinal.{0}} : b < Om1 ^ (log Om1 b + 1) := by
  have := lt_opow_succ_log_self gf_one_lt_Om1 b
  rwa [succ_eq_add_one] at this

/-- **The digits of a sum of codes** lie below every additively closed `Z`. -/
theorem gtc_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) : ∀ a b, a < gfE → b < gfE →
    gtc a < Z → gtc b < Z → gtc (a + b) < Z := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro b haW hbW hga hgb
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add]; exact hgb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [add_zero]; exact hga
  obtain ⟨hq0, hqΩ, hr, hdec, hra, -⟩ := parts ha0
  obtain ⟨hq0', hqΩ', hr', hdec', -, -⟩ := parts hb0
  obtain ⟨gl, gq, gr⟩ := gtc_parts ha0 haW
  obtain ⟨gl', gq', gr'⟩ := gtc_parts hb0 hbW
  set l := log Om1 a with hl
  set q := a / Om1 ^ l with hq
  set r := a % Om1 ^ l with hrr
  set l' := log Om1 b with hl'
  set q' := b / Om1 ^ l' with hq'
  set r' := b % Om1 ^ l' with hrr'
  have hlW : l < gfE := (log_lt ha0 haW).trans haW
  have hl'W : l' < gfE := (log_lt hb0 hbW).trans hbW
  rcases lt_trichotomy l' l with hll | hll | hll
  · have hbl : b < Om1 ^ l :=
      lt_pow_succ_log.trans_le (opow_le_opow_right (zero_lt_one.trans gf_one_lt_Om1) (add_one_le_of_lt hll))
    have hrb : r + b < Om1 ^ l := (Om1_pow_indec l).add_lt hr hbl
    have e : a + b = Om1 ^ l * q + (r + b) := by rw [← hdec, add_assoc]
    rw [e, (rdc_cnf hlW hq0.ne' hqΩ hrb 0).2]
    exact max_lt (max_lt (gl.trans_lt hga) (gq.trans_lt hga))
      (IH r hra b (hra.trans haW) hbW (gr.trans_lt hga) hgb)
  · have habs : r + Om1 ^ l * q' = Om1 ^ l * q' := by
      rw [Om1_pow_eq] at hr ⊢
      exact add_of_omega0_opow_le hr (le_mul_of_one_le_right' (one_le_iff_pos.2 hq0'))
    have hqq : q + q' < Om1 := Om1_add_lt hqΩ hqΩ'
    have e : a + b = Om1 ^ l * (q + q') + r' := by
      rw [← hdec, ← hdec', hll, add_assoc, ← add_assoc r, habs, ← add_assoc, ← mul_add]
    rw [e, (rdc_cnf hlW (hq0.trans_le le_self_add).ne' hqq (hll ▸ hr') 0).2]
    exact max_lt (max_lt (gl.trans_lt hga) (hZ _ _ (gq.trans_lt hga) (gq'.trans_lt hgb))) (gr'.trans_lt hgb)
  · have hab : a < Om1 ^ l' :=
      lt_pow_succ_log.trans_le (opow_le_opow_right (zero_lt_one.trans gf_one_lt_Om1) (add_one_le_of_lt hll))
    have habs : a + Om1 ^ l' * q' = Om1 ^ l' * q' := by
      rw [Om1_pow_eq] at hab ⊢
      exact add_of_omega0_opow_le hab (le_mul_of_one_le_right' (one_le_iff_pos.2 hq0'))
    rw [← hdec', ← add_assoc, habs, hdec']
    exact hgb

theorem one_add_mpred {l : Ordinal.{0}} (hl0 : l ≠ 0) : 1 + mpred l = l := by
  unfold mpred
  split_ifs with hω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hω
    have hn : n ≠ 0 := by rintro rfl; exact hl0 (by simp)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.cast_succ, ← succ_eq_add_one, Ordinal.pred_succ, succ_eq_add_one]
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_cast, ← Nat.cast_add, Nat.add_comm, Nat.cast_add,
      Nat.cast_one]
  · push Not at hω; exact one_add_of_omega0_le hω

theorem gtc_mpred {l : Ordinal.{0}} : gtc (mpred l) ≤ gtc l := by
  unfold mpred
  split_ifs with hω
  · have hlΩ : l < Om1 := hω.trans omega_lt_Om1
    have hpl : Ordinal.pred l < Om1 := (Ordinal.pred_le_self _).trans_lt hlΩ
    rw [(rdc_const hpl 0).2, (rdc_const hlΩ 0).2]
    exact Ordinal.pred_le_self _
  · exact le_rfl

theorem mpred_le (l : Ordinal.{0}) : mpred l ≤ l := by
  unfold mpred; split_ifs
  · exact Ordinal.pred_le_self _
  · exact le_rfl

/-- **`gtc (y/Ω₁) ≤ gtc y` and `y mod Ω₁ ≤ gtc y`.** -/
theorem gtc_div : ∀ y, y < gfE → gtc (y / Om1) ≤ gtc y ∧ y % Om1 ≤ gtc y := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyW
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div, Ordinal.zero_mod]; exact ⟨le_rfl, zero_le⟩
  obtain ⟨hq0, hqΩ, hr, hdec, hra, -⟩ := parts hy0
  obtain ⟨gl, gq, gr⟩ := gtc_parts hy0 hyW
  set l := log Om1 y with hl
  set q := y / Om1 ^ l with hq
  set r := y % Om1 ^ l with hrr
  have hlW : l < gfE := (log_lt hy0 hyW).trans hyW
  rcases eq_or_ne l 0 with hl0 | hl0
  · have hyΩ : y < Om1 := by
      have := (lt_pow_succ_log (b := y))
      rwa [← hl, hl0, zero_add, opow_one] at this
    rw [Ordinal.div_eq_zero_of_lt hyΩ, Ordinal.mod_eq_of_lt hyΩ, gtc_zero, (rdc_const hyΩ 0).2]
    exact ⟨zero_le, le_rfl⟩
  set m := mpred l with hm
  have hmW : m < gfE := (mpred_le l).trans_lt hlW
  have hpow : Om1 ^ l = Om1 * Om1 ^ m := by
    conv_lhs => rw [← one_add_mpred hl0]
    rw [opow_add, opow_one]
  have hr2 : r / Om1 < Om1 ^ m := (Ordinal.div_lt Om1_ne').2 (by rw [← hpow]; exact hr)
  have ey : y = Om1 * (Om1 ^ m * q) + r := by rw [← mul_assoc, ← hpow, hdec]
  have ed : y / Om1 = Om1 ^ m * q + r / Om1 := by
    rw [ey, Ordinal.mul_add_div _ Om1_ne']
  have em : y % Om1 = r % Om1 := by rw [ey, Ordinal.mul_add_mod_self]
  obtain ⟨i1, i2⟩ := IH r hra (hra.trans hyW)
  refine ⟨?_, by rw [em]; exact i2.trans gr⟩
  rw [ed, (rdc_cnf hmW hq0.ne' hqΩ hr2 0).2]
  exact max_le (max_le (gtc_mpred.trans gl) gq) (i1.trans gr)

theorem Om1_mul_div_eq (y : Ordinal.{0}) : ω ^ y = Om1 ^ (y / Om1) * ω ^ (y % Om1) := by
  rw [Om1_pow_eq, ← opow_add, Ordinal.div_add_mod]

/-- **A power `ω^y` of a code**: `ω^y = Ω₁^{y/Ω₁}·ω^{y mod Ω₁}` has its gate below every `Z` closed under `ω^·`
containing the gate of `y`. -/
theorem gtc_opow {Z y : Ordinal.{0}} (hZ : ∀ u, u < Z → ω ^ u < Z) (hy : y < gfE) (hgy : gtc y < Z) :
    gtc (ω ^ y) < Z := by
  obtain ⟨g1, g2⟩ := gtc_div y hy
  have hdΩ : y % Om1 < Om1 := Ordinal.mod_lt y Om1_ne'
  have hwd : ω ^ (y % Om1) < Om1 := Om1_opow_lt hdΩ
  have hlW : y / Om1 < gfE := (Ordinal.div_le_of_le_mul (le_mul_right y (zero_lt_one.trans gf_one_lt_Om1))).trans_lt hy
  rw [Om1_mul_div_eq, ← add_zero (Om1 ^ (y / Om1) * ω ^ (y % Om1)),
    (rdc_cnf hlW (opow_pos _ omega0_pos).ne' hwd (opow_pos _ (zero_lt_one.trans gf_one_lt_Om1)) 0).2, gtc_zero]
  exact max_lt (max_lt (g1.trans_lt hgy) (hZ _ (g2.trans_lt hgy))) (lt_of_le_of_lt zero_le hgy)

/-- **An `ε`-number below `ε_{Ω₁+1}` is at most `Ω₁`.** -/
theorem eps_lt_eW {e : Ordinal.{0}} (he : ω ^ e = e) (hW : e < gfE) : e ≤ Om1 := by
  by_contra hlt
  push Not at hlt
  exact absurd (eN_le hlt he) (not_le.2 hW)

/-- **The code `Ω₁` reads `x`**, gate `1`. -/
theorem rdc_Om1 (x : Ordinal.{0}) : rdc Om1 x = x ∧ gtc Om1 = 1 := by
  have h := rdc_cnf (l := 1) (q := 1) (r := 0) (gf_one_lt_Om1.trans Om1_lt_eW) one_ne_zero gf_one_lt_Om1
    (opow_pos _ (zero_lt_one.trans gf_one_lt_Om1)) x
  rw [opow_one, mul_one, add_zero, (rdc_const gf_one_lt_Om1 x).1, opow_one, mul_one, rdc_zero, add_zero,
    (rdc_const gf_one_lt_Om1 0).2, gtc_zero, max_self, max_eq_left zero_le] at h
  exact h

/-- **A code over `Z` below `ε_{Ω₁+1}`, all of whose atoms lie above `ε_{Ω₁+1}`, has its gate below `Z`** (`Z ≤ Ω₁`,
closed under `+` and `φ`). -/
theorem gfCode_gate {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    (hAt : ∀ s ∈ At, gfE < s) {c : Ordinal.{0}} (hc : GxCl Z At c) : c < gfE → gtc c < Z := by
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hconst : ∀ x, x < Om1 → gtc x = x := fun x hx => (rdc_const hx 0).2
  induction hc with
  | @small x h => intro _; rw [hconst x (h.trans_le hZ1)]; exact h
  | om => intro _; rw [← Br.Om1_eq, (rdc_Om1 0).2]; exact h1Z
  | @atom s hs => intro h; exact absurd (hAt s hs) (not_lt.2 h.le)
  | @add x y _ _ ihx ihy =>
    intro h
    have hx : x < gfE := lt_of_le_of_lt le_self_add h
    have hy : y < gfE := lt_of_le_of_lt le_add_self h
    exact gtc_add hZa x y hx hy (ihx hx) (ihy hy)
  | @phi x y hx hy ihx ihy =>
    intro h
    have hyW : y < gfE := lt_of_le_of_lt (right_le_veblen x y) h
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h ⊢
      exact gtc_opow hZw hyW (ihy hyW)
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have hle := eps_lt_eW hE h
      rcases hle.lt_or_eq with hlt | heq
      · have hxO : x < Om1 := (left_le_veblen x y).trans_lt hlt
        have hyO : y < Om1 := (right_le_veblen x y).trans_lt hlt
        have hxZ : x < Z := by rw [← hconst x hxO]; exact ihx (hxO.trans Om1_lt_eW)
        have hyZ : y < Z := by rw [← hconst y hyO]; exact ihy (hyO.trans Om1_lt_eW)
        rw [hconst _ hlt]
        exact hZp x y hxZ hyZ
      · rw [heq, (rdc_Om1 0).2]; exact h1Z

/-- **The codes below `a` with gate below `y < Ω₁` are countably many.** -/
theorem gf_count {a y : Ordinal.{0}} (ha : a < gfE) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio a // gtc b.1 < y} := by
  have hyn : eN y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact Ge.eN_lt_Om1' hy hy1
  haveI := Gc.gc_countable hyn
  let f : {b : Iio a // gtc b.1 < y} → Iio (eN y) := fun b => ⟨rdc b.1.1 y, rdc_lt_eN hy _ b.2⟩
  refine Function.Injective.countable (f := f) fun b c hbc => ?_
  have hb := b.1.2.trans ha
  have hc := c.1.2.trans ha
  have e : rdc b.1.1 y = rdc c.1.1 y := congrArg Subtype.val hbc
  rcases lt_trichotomy b.1.1 c.1.1 with h | h | h
  · exact absurd e (rdc_mono hy hc h c.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (rdc_mono hy hb h b.2 c.2).ne'

/-- **`φ(1, Ω₁) = Ω₁`.** -/
theorem eps_Om1 : veblen 1 Om1 = Om1 := by
  have hlim : IsSuccLimit Om1 := by rw [Br.Om1_eq]; exact InaccSeq.Om_isSuccLimit one_ne_zero
  refine le_antisymm (((isNormal_veblen 1).le_iff_forall_le hlim).2 fun c hc => ?_) (right_le_veblen 1 Om1)
  have h := Ph.ph_SC_Om1.2 1 (by rw [← Br.Om1_eq]; exact gf_one_lt_Om1) c (by rw [← Br.Om1_eq]; exact hc)
  rw [← Br.Om1_eq] at h
  exact h.le

/-- **`ε_{Ω₁+1} = φ(1, Ω₁+1)`.** -/
theorem eW_eq : gfE = veblen 1 (Om1 + 1) := by
  have h := epsilon_succ_eq_nfp Om1
  simp only [epsilon] at h
  rw [eps_Om1, succ_eq_add_one] at h
  rw [h]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Gf
