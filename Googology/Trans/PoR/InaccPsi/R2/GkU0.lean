import Googology.Trans.PoR.InaccPsi.R2.GkPkg
import Googology.Trans.PoR.InaccPsi.R2.GjHI

/-!
# CODES WITH EVERY PSEUDO-BASE `ε_{Ω₁+ν}` BELOW `ζ_{Ω₁+1}`: one reading system, the definitions

Every code `c` with `ε_{Ω₁+1} ≤ c < ζ_{Ω₁+1} = evZ Ω₁` (the least `ε`-fixed point above `Ω₁`, `= φ(2, Ω₁+1)`) lies in
exactly one bracket `[ε_{Ω₁+ν}, ε_{Ω₁+ν+1})` (`ν = guN c ≥ 1`, `ν < c`); with `E = ε_{Ω₁+ν}` it has the normal form
`c = E^k·d + r` (`k = log_E c < c`, `0 < d < E`, `r < E^k`), and ALL FOUR parts `ν, k, d, r` are again codes below `c`.
The reading replaces `ε_{Ω₁+ν}` by the pseudo-base `ε_{x+ν(x)}`:

  `guR c x = ε_{x+ν(x)}^{k(x)}·d(x) + r(x)`  (codes below `ε_{Ω₁+1}` read by `rdc`, `Ω₁ ↦ x`),

one well-founded recursion for all bases at once.  The gate is the largest gate of the infinite parts.

* `guB` (`ζ_{Ω₁+1}`), `guN` (the index of the bracket), `guE` (`ε_{Ω₁+guN c}`), `guN_eq`, `guN_spec`;
* `gu_pow_eq` (`E^l = ω^{E·l}`), `gu_log_lt` (**`log_E c < c` for `E ≤ c < ε_{E+1}`**), `gu_parts`, `gu_cnf`;
* `guR`, `guG`, `guQ`, the unfolding lemmas `guR_dec`, `guG_dec`, `guR_low`, `guG_low`, `guR_high`, `guG_high`,
  `guR_cnf`, `guG_cnf`, `guR_base` (**`ε_{Ω₁+ν}` reads `ε_{x+ν(x)}`**), `guG_base`, `guR_E`, `guG_E`.

No new axiom.  New definitions: `guB`, `guN`, `guE`, `guR`, `guG`, `guQ`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

theorem gu_Om1_E : InE Om1 := Rj.rj_Om1_inE

/-- **The bound**: `ζ_{Ω₁+1}`, the least `ε`-fixed point above `Ω₁`. -/
noncomputable def guB : Ordinal.{0} := evZ Om1

theorem guB_E : InE guB := evZ_E Om1

theorem gu_evA_one : evA Om1 1 = gfE := by
  have h := evA_add_one Om1 0
  rw [zero_add, evA_zero gu_Om1_E] at h
  rw [h]; rfl

theorem gu_one_lt_guB : (1 : Ordinal.{0}) < guB :=
  (one_lt_omega0.trans omega_lt_Om1).trans (lt_evZ Om1)

theorem gfE_lt_guB : gfE < guB := by
  rw [← gu_evA_one]; exact evA_lt_evZ gu_Om1_E gu_one_lt_guB

theorem guB_lim : IsSuccLimit guB := ev_isSuccLimit_of_inE guB_E

theorem gu_evA_lt {n : Ordinal.{0}} (hn : n < guB) : evA Om1 n < guB := evA_lt_evZ gu_Om1_E hn

/-- **The index of the bracket** `[ε_{Ω₁+ν}, ε_{Ω₁+ν+1})` of `c`. -/
noncomputable def guN (c : Ordinal.{0}) : Ordinal.{0} := sInf {n | c < evA Om1 (n + 1)}

/-- **The pseudo-base of `c`**: `ε_{Ω₁+guN c}`. -/
noncomputable def guE (c : Ordinal.{0}) : Ordinal.{0} := evA Om1 (guN c)

theorem guN_eq {c n : Ordinal.{0}} (h1 : evA Om1 n ≤ c) (h2 : c < evA Om1 (n + 1)) : guN c = n := by
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) h2) (le_csInf ⟨n, h2⟩ fun m hm => ?_)
  by_contra hmn
  push Not at hmn
  have : evA Om1 (m + 1) ≤ evA Om1 n := evA_le_iff.2 (add_one_le_of_lt hmn)
  exact absurd (lt_of_lt_of_le hm (this.trans h1)) (lt_irrefl _)

theorem guN_spec {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < guB) :
    1 ≤ guN c ∧ evA Om1 (guN c) ≤ c ∧ c < evA Om1 (guN c + 1) ∧ guN c < guB ∧ guN c < c := by
  have hOc : Om1 ≤ c := Om1_lt_eW.le.trans h1
  have hcC : c < evA Om1 guB := h2.trans_le (le_evA_idx Om1 guB)
  obtain ⟨n, hnB, hn1, hn2⟩ := evA_bracket gu_Om1_E hOc hcC
  have he := guN_eq hn1 hn2
  rw [he]
  have h1n : 1 ≤ n := by
    by_contra h0
    push Not at h0
    rw [lt_one_iff_zero] at h0
    rw [h0, zero_add, gu_evA_one] at hn2
    exact absurd h1 (not_le.2 hn2)
  exact ⟨h1n, hn1, hn2, hnB, (lt_evA_self gu_Om1_E hnB).trans_le hn1⟩

theorem guE_E (c : Ordinal.{0}) : InE (guE c) := evA_E _ _

theorem gu_pow_eq {E : Ordinal.{0}} (hE : InE E) (l : Ordinal.{0}) : E ^ l = ω ^ (E * l) := by
  rw [opow_mul, show ω ^ E = E from hE]

/-- **`log_E c < c` for `E ≤ c < ε_{E+1}`** (`E` an `ε`-number): otherwise `c = E^c` would be an `ε`-number in
`(E, ε_{E+1})`. -/
theorem gu_log_lt {E c : Ordinal.{0}} (hE : InE E) (h1 : E ≤ c) (h2 : c < eN E) : log E c < c := by
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  have hc0 : c ≠ 0 := (lt_of_lt_of_le hE.pos h1).ne'
  have hle : E ^ log E c ≤ c := opow_log_le_self E hc0
  have hl1 : 1 ≤ log E c := le_log_of_opow_le hE1 (by rw [opow_one]; exact h1)
  rcases (right_le_opow (log E c) hE1).lt_or_eq with h | h
  · exact h.trans_le hle
  exfalso
  set l := log E c with hl
  have hlE : InE l := by
    refine le_antisymm ?_ (right_le_opow l one_lt_omega0)
    calc ω ^ l ≤ ω ^ (E * l) := opow_le_opow_right omega0_pos (le_mul_right l hE.pos)
      _ = E ^ l := (gu_pow_eq hE l).symm
      _ = l := h.symm
  have hEl : E ≤ l := by
    rw [h]; calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ E ^ l := opow_le_opow_right hE.pos hl1
  rcases hEl.lt_or_eq with hlt | heq
  · exact absurd ((eN_le hlt hlE).trans_lt ((right_le_opow l hE1).trans_lt (hle.trans_lt h2))) (lt_irrefl _)
  · have : E ^ (1 : Ordinal.{0}) < E ^ E := (opow_lt_opow_iff_right hE1).2 hE1
    rw [opow_one] at this
    rw [← heq] at h
    exact absurd h this.ne

/-- **The parts of a code** `ε_{Ω₁+1} ≤ c < ζ_{Ω₁+1}`: `c = E^k·d + r` with `E = guE c`, all parts below `c`. -/
theorem gu_parts {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < guB) :
    log (guE c) c ≠ 0 ∧ c / guE c ^ log (guE c) c ≠ 0 ∧ c / guE c ^ log (guE c) c < guE c ∧
      c % guE c ^ log (guE c) c < guE c ^ log (guE c) c ∧
      guE c ^ log (guE c) c * (c / guE c ^ log (guE c) c) + c % guE c ^ log (guE c) c = c ∧
      log (guE c) c < c ∧ c % guE c ^ log (guE c) c < c ∧ c / guE c ^ log (guE c) c < c := by
  obtain ⟨-, hEc, hcN, -, -⟩ := guN_spec h1 h2
  have hE := guE_E c
  have hE1 : (1 : Ordinal.{0}) < guE c := Lu.lu_one_lt_E hE
  have hc0 : c ≠ 0 := (lt_of_lt_of_le hE.pos hEc).ne'
  have hcN' : c < eN (guE c) := by rw [guE, ← evA_add_one]; exact hcN
  have hk1 := le_log_of_opow_le hE1 (show guE c ^ (1 : Ordinal.{0}) ≤ c by rw [opow_one]; exact hEc)
  have hdE := div_opow_log_lt c hE1
  exact ⟨(zero_lt_one.trans_le hk1).ne', (div_opow_log_pos (guE c) hc0).ne', hdE,
    Ordinal.mod_lt c (opow_ne_zero _ hE.pos.ne'), Ordinal.div_add_mod c _, gu_log_lt hE hEc hcN',
    mod_opow_log_lt_self _ hc0, hdE.trans_le hEc⟩

/-- **The normal form determines the parts**: for `E = ε_{Ω₁+n}` (`1 ≤ n < ζ_{Ω₁+1}`), `k ≠ 0`, `0 < d < E`,
`r < E^k` and `E^k·d + r < ε_{E+1}`, the index, the exponent, the digit and the rest of `E^k·d + r` are `n, k, d, r`. -/
theorem gu_cnf {n k d r : Ordinal.{0}} (hn : 1 ≤ n) (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < evA Om1 n)
    (hr : r < evA Om1 n ^ k) (hv : evA Om1 n ^ k * d + r < evA Om1 (n + 1)) :
    guN (evA Om1 n ^ k * d + r) = n ∧ guE (evA Om1 n ^ k * d + r) = evA Om1 n ∧
      log (evA Om1 n) (evA Om1 n ^ k * d + r) = k ∧ (evA Om1 n ^ k * d + r) / evA Om1 n ^ k = d ∧
      (evA Om1 n ^ k * d + r) % evA Om1 n ^ k = r ∧ gfE ≤ evA Om1 n ^ k * d + r := by
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  have hp : E ^ k ≠ 0 := opow_ne_zero _ hE.pos.ne'
  have hEv : E ≤ E ^ k * d + r := by
    calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hk)
      _ = E ^ k * 1 := (mul_one _).symm
      _ ≤ E ^ k * d := mul_le_mul_right (one_le_iff_ne_zero.2 hd0) _
      _ ≤ _ := le_self_add
  have hN := guN_eq hEv hv
  have hgE : gfE ≤ E := by rw [← gu_evA_one, hEdef]; exact evA_le_iff.2 hn
  refine ⟨hN, by rw [guE, hN], ?_, ?_, ?_, hgE.trans hEv⟩
  · rw [log_opow_mul_add hE1 hd0 hr, log_eq_zero hdE, add_zero]
  · rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-! ## The reading and the gate -/

/-- **The pseudo-base reading** `ε_{x+m}` (`m ≥ 1`), written as `ε_{ε_{x+1}+(m-1)}` so that `m = 1` gives `ε_{x+1}` at
every `x`. -/
noncomputable def guA (x m : Ordinal.{0}) : Ordinal.{0} := evA (eN x) (m - 1)

theorem guA_E (x m : Ordinal.{0}) : InE (guA x m) := evA_E _ _

theorem guA_one (x : Ordinal.{0}) : guA x 1 = eN x := by
  rw [guA, sub_self, evA_zero (eN_E x)]

/-- At an `ε`-number `x`, `guA x m = ε_{x+m}` for `m ≥ 1`. -/
theorem guA_eq {x m : Ordinal.{0}} (hx : InE x) (hm : 1 ≤ m) : guA x m = evA x m := by
  have h1 : eN x = evA x 1 := by rw [← zero_add (1 : Ordinal.{0}), evA_add_one, evA_zero hx]
  rw [guA, h1, evA_add, Ordinal.add_sub_cancel_of_le hm]

/-- **The reading** of a code at `x`: `ε_{x+ν(x)}^{k(x)}·d(x) + r(x)` above `ε_{Ω₁+1}`, `rdc` below, the identity at
and above the bound. -/
noncomputable def guR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c ∧ c < guB then
    guA x (guR (guN c) x) ^ guR (log (guE c) c) x * guR (c / guE c ^ log (guE c) c) x +
      guR (c % guE c ^ log (guE c) c) x
  else if c < gfE then rdc c x else c
termination_by c
decreasing_by
  all_goals first
    | exact (guN_spec h.1 h.2).2.2.2.2
    | exact (gu_parts h.1 h.2).2.2.2.2.2.1
    | exact (gu_parts h.1 h.2).2.2.2.2.2.2.2
    | exact (gu_parts h.1 h.2).2.2.2.2.2.2.1

/-- **The gate** of a code: the gates of its infinite index, exponent and digit, and of its rest. -/
noncomputable def guG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c ∧ c < guB then
    max (max (if guN c < ω then 0 else guG (guN c))
        (if log (guE c) c < ω then 0 else guG (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else guG (c / guE c ^ log (guE c) c))
        (guG (c % guE c ^ log (guE c) c)))
  else if c < gfE then gtc c else 0
termination_by c
decreasing_by
  all_goals first
    | exact (guN_spec h.1 h.2).2.2.2.2
    | exact (gu_parts h.1 h.2).2.2.2.2.2.1
    | exact (gu_parts h.1 h.2).2.2.2.2.2.2.2
    | exact (gu_parts h.1 h.2).2.2.2.2.2.2.1

/-- **The gate of a part**: `0` when finite. -/
noncomputable def guQ (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else guG a

theorem guR_low {c : Ordinal.{0}} (hc : c < gfE) (x : Ordinal.{0}) : guR c x = rdc c x := by
  rw [guR, dif_neg (fun h => absurd h.1 (not_le.2 hc)), if_pos hc]

theorem guG_low {c : Ordinal.{0}} (hc : c < gfE) : guG c = gtc c := by
  rw [guG, dif_neg (fun h => absurd h.1 (not_le.2 hc)), if_pos hc]

theorem guR_high {c : Ordinal.{0}} (hc : guB ≤ c) (x : Ordinal.{0}) : guR c x = c := by
  have hE : ¬ c < gfE := not_lt.2 (gfE_lt_guB.le.trans hc)
  rw [guR, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), if_neg hE]

theorem guG_high {c : Ordinal.{0}} (hc : guB ≤ c) : guG c = 0 := by
  have hE : ¬ c < gfE := not_lt.2 (gfE_lt_guB.le.trans hc)
  rw [guG, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), if_neg hE]

theorem guR_dec {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < guB) (x : Ordinal.{0}) :
    guR c x = guA x (guR (guN c) x) ^ guR (log (guE c) c) x * guR (c / guE c ^ log (guE c) c) x +
      guR (c % guE c ^ log (guE c) c) x := by
  rw [guR, dif_pos ⟨h1, h2⟩]

theorem guG_dec {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < guB) :
    guG c = max (max (guQ (guN c)) (guQ (log (guE c) c)))
      (max (guQ (c / guE c ^ log (guE c) c)) (guG (c % guE c ^ log (guE c) c))) := by
  rw [guG, dif_pos ⟨h1, h2⟩]; rfl

theorem guQ_le (a : Ordinal.{0}) : guQ a ≤ guG a := by
  unfold guQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem guR_zero (x : Ordinal.{0}) : guR 0 x = 0 := by rw [guR_low eW_E.pos, rdc_zero]

theorem guG_zero : guG 0 = 0 := by rw [guG_low eW_E.pos, gtc_zero]

theorem guR_nat (n : ℕ) (x : Ordinal.{0}) : guR n x = n := by
  have hn : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1
  rw [guR_low (hn.trans Om1_lt_eW), (rdc_const hn x).1]

theorem guR_one (x : Ordinal.{0}) : guR 1 x = 1 := by exact_mod_cast guR_nat 1 x

theorem guG_nat (n : ℕ) : guG n = n := by
  have hn : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1
  rw [guG_low (hn.trans Om1_lt_eW), (rdc_const hn 0).2]

theorem guQ_nat (n : ℕ) : guQ n = 0 := by unfold guQ; rw [if_pos (natCast_lt_omega0 n)]

theorem guQ_one : guQ 1 = 0 := by exact_mod_cast guQ_nat 1

theorem guQ_low {a : Ordinal.{0}} (ha : a < gfE) : guQ a = giQ a := by
  unfold guQ giQ; rw [guG_low ha]

/-- The gate of a part from its gate as a part, below every `Z > ω`. -/
theorem guG_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : guQ a < Z) : guG a < Z := by
  unfold guQ at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [guG_nat]; exact (natCast_lt_omega0 n).trans hωZ
  · exact h

theorem guR_cnf {n k d r : Ordinal.{0}} (hn : 1 ≤ n) (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < evA Om1 n)
    (hr : r < evA Om1 n ^ k) (hv : evA Om1 n ^ k * d + r < evA Om1 (n + 1)) (hB : evA Om1 n ^ k * d + r < guB)
    (x : Ordinal.{0}) : guR (evA Om1 n ^ k * d + r) x = guA x (guR n x) ^ guR k x * guR d x + guR r x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gu_cnf hn hk hd0 hdE hr hv
  rw [guR_dec h6 hB, h1, h2, h3, h4, h5]

theorem guG_cnf {n k d r : Ordinal.{0}} (hn : 1 ≤ n) (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < evA Om1 n)
    (hr : r < evA Om1 n ^ k) (hv : evA Om1 n ^ k * d + r < evA Om1 (n + 1)) (hB : evA Om1 n ^ k * d + r < guB) :
    guG (evA Om1 n ^ k * d + r) = max (max (guQ n) (guQ k)) (max (guQ d) (guG r)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gu_cnf hn hk hd0 hdE hr hv
  rw [guG_dec h6 hB, h1, h2, h3, h4, h5]

/-- `ε_{Ω₁+n}` as a normal form `E^1·1 + 0`. -/
theorem gu_base_nf {n : Ordinal.{0}} (hn : 1 ≤ n) (hnB : n < guB) :
    evA Om1 n = evA Om1 n ^ (1 : Ordinal.{0}) * 1 + 0 ∧ evA Om1 n ^ (1 : Ordinal.{0}) * 1 + 0 < evA Om1 (n + 1) ∧
      evA Om1 n ^ (1 : Ordinal.{0}) * 1 + 0 < guB := by
  rw [opow_one, mul_one, add_zero]
  exact ⟨rfl, evA_lt_iff.2 (lt_add_one n), gu_evA_lt hnB⟩

/-- **`ε_{Ω₁+n}` reads `ε_{x+n(x)}`.** -/
theorem guR_base {n : Ordinal.{0}} (hn : 1 ≤ n) (hnB : n < guB) (x : Ordinal.{0}) :
    guR (evA Om1 n) x = guA x (guR n x) := by
  obtain ⟨e, h1, h2⟩ := gu_base_nf hn hnB
  have hE1 : (1 : Ordinal.{0}) < evA Om1 n := Lu.lu_one_lt_E (evA_E _ _)
  have h := guR_cnf hn one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact (evA_E _ _).pos) h1 h2 x
  rw [← e] at h
  rw [h, guR_one, guR_zero, opow_one, mul_one, add_zero]

/-- The gate of `ε_{Ω₁+n}` is the gate of `n` as a part. -/
theorem guG_base {n : Ordinal.{0}} (hn : 1 ≤ n) (hnB : n < guB) : guG (evA Om1 n) = guQ n := by
  obtain ⟨e, h1, h2⟩ := gu_base_nf hn hnB
  have hE1 : (1 : Ordinal.{0}) < evA Om1 n := Lu.lu_one_lt_E (evA_E _ _)
  have h := guG_cnf hn one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact (evA_E _ _).pos) h1 h2
  rw [← e] at h
  rw [h, guQ_one, guG_zero]
  simp

theorem guR_E (x : Ordinal.{0}) : guR gfE x = eN x := by
  rw [← gu_evA_one, guR_base le_rfl gu_one_lt_guB, guR_one, guA_one]

theorem guG_E : guG gfE = 0 := by
  rw [← gu_evA_one, guG_base le_rfl gu_one_lt_guB, guQ_one]

end Googology.Trans.PoR.InaccPsi.R2.Gk
