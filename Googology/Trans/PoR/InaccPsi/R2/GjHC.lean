import Googology.Trans.PoR.InaccPsi.R2.GjImg

/-!
# HEREDITARY CODES BELOW `ε_{Ω₁+2}`: `E^k·d + r` with the exponent `k` again such a code

`R2.GiWc` reads the codes `E^k·d + r` (`E = ε_{Ω₁+1}`) with a finite exponent `k`.  Every `c` with
`E ≤ c < ε_{Ω₁+2} = ε_{E+1}` (the next `ε`-number after `E`) has `log_E c < c`, so the exponent can itself be read
recursively: `jhR c x = ε_{x+1}^{k(x)}·d(x) + r(x)` with `k(x) = jhR k x` (hereditary Cantor normal form to the base
`E`, digits `d < E` read by `rdc`).  The gate of an exponent counts only when it is infinite (`jhQ`).

* `jhB` (`ε_{Ω₁+2}`), `jh_log_lt` (**`log_E c < c` for `E ≤ c < ε_{E+1}`**), `jhR`, `jhG`, `jhQ`, the unfolding lemmas,
  `jhR_cnf`, `jhG_cnf`, `jhR_E`, `jhG_E`, `jhR_low`, `jhG_low`;
* `jh_one_add` (`1 + a` for a code `a`), `jhQ_one_add`, `jhB` facts (`jhB < Γ_{Ω₁+1}`, a limit), the
  towers `jhTw` (`E`, `E^E`, `E^{E^E}`, …, cofinal in `jhB`).

No new axiom.  New definitions: `jhB`, `jhR`, `jhG`, `jhQ`, `jhTw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gj

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The bound**: `ε_{Ω₁+2}`, the least `ε`-number above `E = ε_{Ω₁+1}`. -/
noncomputable def jhB : Ordinal.{0} := eN gfE

theorem jhB_E : InE jhB := eN_E gfE

theorem gfE_lt_jhB : gfE < jhB := lt_eN gfE

/-- **`log_E c < c` for `E ≤ c < ε_{E+1}`**: otherwise `c = E^c` would be an `ε`-number in `(E, ε_{E+1})`. -/
theorem jh_log_lt {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < jhB) : log gfE c < c := by
  have hc0 := gw_ne_of_le h1
  have hle : gfE ^ log gfE c ≤ c := opow_log_le_self gfE hc0
  have hl1 : 1 ≤ log gfE c := le_log_of_opow_le gw_one_lt (by rw [opow_one]; exact h1)
  rcases (right_le_opow (log gfE c) gw_one_lt).lt_or_eq with h | h
  · exact h.trans_le hle
  exfalso
  set l := log gfE c with hl
  have hlE : InE l := by
    refine le_antisymm ?_ (right_le_opow l one_lt_omega0)
    calc ω ^ l ≤ ω ^ (gfE * l) := opow_le_opow_right omega0_pos (le_mul_right l eW_E.pos)
      _ = gfE ^ l := (gw_pow_eq l).symm
      _ = l := h.symm
  have hEl : gfE ≤ l := by
    rw [h]; calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gfE ^ l := opow_le_opow_right eW_E.pos hl1
  rcases hEl.lt_or_eq with hlt | heq
  · exact absurd ((eN_le hlt hlE).trans_lt ((right_le_opow l gw_one_lt).trans_lt (hle.trans_lt h2))) (lt_irrefl _)
  · have : gfE ^ (1 : Ordinal.{0}) < gfE ^ gfE := (opow_lt_opow_iff_right gw_one_lt).2 gw_one_lt
    rw [opow_one] at this
    rw [← heq] at h
    exact absurd h this.ne

/-- **The reading** of `c = E^k·d + r` at `x`: `ε_{x+1}^{k(x)}·d(x) + r(x)`, the exponent read recursively. -/
noncomputable def jhR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c ∧ c < jhB then
    eN x ^ jhR (log gfE c) x * rdc (c / gfE ^ log gfE c) x + jhR (c % gfE ^ log gfE c) x
  else if c < gfE then rdc c x else c
termination_by c
decreasing_by
  all_goals first
    | exact jh_log_lt h.1 h.2
    | exact mod_opow_log_lt_self gfE (gw_ne_of_le h.1)

/-- **The gate** of `c = E^k·d + r`: the gate of `k` when infinite, of `d` when infinite, and of `r`. -/
noncomputable def jhG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c ∧ c < jhB then
    max (max (if log gfE c < ω then 0 else jhG (log gfE c)) (giQ (c / gfE ^ log gfE c))) (jhG (c % gfE ^ log gfE c))
  else if c < gfE then gtc c else 0
termination_by c
decreasing_by
  all_goals first
    | exact jh_log_lt h.1 h.2
    | exact mod_opow_log_lt_self gfE (gw_ne_of_le h.1)

/-- **The gate of an exponent**: `0` when finite. -/
noncomputable def jhQ (k : Ordinal.{0}) : Ordinal.{0} := if k < ω then 0 else jhG k

theorem jhR_low {c : Ordinal.{0}} (hc : c < gfE) (x : Ordinal.{0}) : jhR c x = rdc c x := by
  rw [jhR, dif_neg (fun h => absurd h.1 (not_le.2 hc)), if_pos hc]

theorem jhG_low {c : Ordinal.{0}} (hc : c < gfE) : jhG c = gtc c := by
  rw [jhG, dif_neg (fun h => absurd h.1 (not_le.2 hc)), if_pos hc]

/-- Above the bound the reading is the identity (so that `+1` is kept everywhere). -/
theorem jhR_high {c : Ordinal.{0}} (hc : jhB ≤ c) (x : Ordinal.{0}) : jhR c x = c := by
  have hE : ¬ c < gfE := not_lt.2 (gfE_lt_jhB.le.trans hc)
  rw [jhR, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), if_neg hE]

theorem jhG_high {c : Ordinal.{0}} (hc : jhB ≤ c) : jhG c = 0 := by
  have hE : ¬ c < gfE := not_lt.2 (gfE_lt_jhB.le.trans hc)
  rw [jhG, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), if_neg hE]

theorem jhR_dec {c : Ordinal.{0}} (hc : gfE ≤ c) (hcB : c < jhB) (x : Ordinal.{0}) :
    jhR c x = eN x ^ jhR (log gfE c) x * rdc (c / gfE ^ log gfE c) x + jhR (c % gfE ^ log gfE c) x := by
  rw [jhR, dif_pos ⟨hc, hcB⟩]

theorem jhG_dec {c : Ordinal.{0}} (hc : gfE ≤ c) (hcB : c < jhB) :
    jhG c = max (max (jhQ (log gfE c)) (giQ (c / gfE ^ log gfE c))) (jhG (c % gfE ^ log gfE c)) := by
  rw [jhG, dif_pos ⟨hc, hcB⟩]; rfl

theorem jhQ_le (k : Ordinal.{0}) : jhQ k ≤ jhG k := by
  unfold jhQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem jhQ_low {k : Ordinal.{0}} (hk : k < gfE) : jhQ k = giQ k := by
  unfold jhQ giQ; rw [jhG_low hk]

theorem jhQ_nat (n : ℕ) : jhQ n = 0 := by unfold jhQ; rw [if_pos (natCast_lt_omega0 n)]

theorem jhR_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gfE) (hr : r < gfE ^ k)
    (hB : gfE ^ k * d + r < jhB) (x : Ordinal.{0}) :
    jhR (gfE ^ k * d + r) x = eN x ^ jhR k x * rdc d x + jhR r x := by
  obtain ⟨h1, h2, h3, h4⟩ := gw_cnf hk hd0 hdE hr
  rw [jhR_dec h4 hB, h1, h2, h3]

theorem jhG_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gfE) (hr : r < gfE ^ k)
    (hB : gfE ^ k * d + r < jhB) : jhG (gfE ^ k * d + r) = max (max (jhQ k) (giQ d)) (jhG r) := by
  obtain ⟨h1, h2, h3, h4⟩ := gw_cnf hk hd0 hdE hr
  rw [jhG_dec h4 hB, h1, h2, h3]

theorem jhG_zero : jhG 0 = 0 := by rw [jhG_low eW_E.pos, gtc_zero]

theorem jhR_zero (x : Ordinal.{0}) : jhR 0 x = 0 := by rw [jhR_low eW_E.pos, rdc_zero]

theorem jhR_one (x : Ordinal.{0}) : jhR 1 x = 1 := by
  rw [jhR_low gw_one_lt, (rdc_const gf_one_lt_Om1 x).1]

theorem jhR_nat (n : ℕ) (x : Ordinal.{0}) : jhR n x = n := by
  have hn : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1
  rw [jhR_low (hn.trans Om1_lt_eW), (rdc_const hn x).1]

theorem jhB_gt_pow {k : Ordinal.{0}} (hk : k < jhB) : gfE ^ k < jhB := by
  rw [gw_pow_eq]; exact jhB_E.opow_lt (jhB_E.mul_lt gfE_lt_jhB hk)

theorem jh_mul_lt {k d : Ordinal.{0}} (hk : k < jhB) (hd : d < gfE) : gfE ^ k * d < jhB :=
  jhB_E.mul_lt (jhB_gt_pow hk) (hd.trans gfE_lt_jhB)

theorem jhG_E : jhG gfE = 0 := by
  have e : gfE = gfE ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  rw [e, jhG_cnf one_ne_zero one_ne_zero gw_one_lt (opow_pos _ eW_E.pos)
    (by rw [← e]; exact gfE_lt_jhB), giQ_one, jhG_zero]
  have : jhQ 1 = 0 := by exact_mod_cast jhQ_nat 1
  rw [this]; simp

theorem jhR_E (x : Ordinal.{0}) : jhR gfE x = eN x := by
  have e : gfE = gfE ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  rw [e, jhR_cnf one_ne_zero one_ne_zero gw_one_lt (opow_pos _ eW_E.pos) (by rw [← e]; exact gfE_lt_jhB),
    jhR_one, opow_one, (rdc_const gf_one_lt_Om1 x).1, mul_one, jhR_zero, add_zero]

/-- The parts of a code `E ≤ c < ε_{E+1}`. -/
theorem jh_parts {c : Ordinal.{0}} (hc : gfE ≤ c) (hcB : c < jhB) :
    log gfE c ≠ 0 ∧ c / gfE ^ log gfE c ≠ 0 ∧ c / gfE ^ log gfE c < gfE ∧
      c % gfE ^ log gfE c < gfE ^ log gfE c ∧ gfE ^ log gfE c * (c / gfE ^ log gfE c) + c % gfE ^ log gfE c = c ∧
      log gfE c < c ∧ c % gfE ^ log gfE c < c :=
  let ⟨h1, h2, h3, h4, h5⟩ := gw_parts hc
  ⟨h1, h2, h3, h4, h5, jh_log_lt hc hcB, mod_opow_log_lt_self gfE (gw_ne_of_le hc)⟩

/-! ## `1 + a` -/

theorem jh_one_add {a : Ordinal.{0}} (ha : ω ≤ a) : 1 + a = a := one_add_of_omega0_le ha

theorem jhQ_one_add (a : Ordinal.{0}) : jhQ (1 + a) = jhQ a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, jhQ_nat, jhQ_nat]
  · rw [jh_one_add ha]

/-! ## The towers `E`, `E^E`, `E^{E^E}`, … -/

/-- The towers: `jhTw 0 = E`, `jhTw (n+1) = E^{jhTw n}`. -/
noncomputable def jhTw : ℕ → Ordinal.{0}
  | 0 => gfE
  | n + 1 => gfE ^ jhTw n

theorem jhTw_lt : ∀ n : ℕ, jhTw n < jhB
  | 0 => gfE_lt_jhB
  | n + 1 => jhB_gt_pow (jhTw_lt n)

theorem jhTw_ge : ∀ n : ℕ, gfE ≤ jhTw n
  | 0 => le_rfl
  | n + 1 => by
    show gfE ≤ gfE ^ jhTw n
    calc gfE = gfE ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right eW_E.pos (gw_one_lt.le.trans (jhTw_ge n))

theorem jhTw_strict (n : ℕ) : jhTw n < jhTw (n + 1) := by
  show jhTw n < gfE ^ jhTw n
  have h1 := jh_log_lt (c := gfE ^ jhTw n) ((jhTw_ge n).trans (right_le_opow _ gw_one_lt)) (jhTw_lt (n + 1))
  rwa [log_opow gw_one_lt] at h1

theorem jhTw_cof {c : Ordinal.{0}} (hc : c < jhB) : ∃ n : ℕ, c < jhTw n := by
  have hle : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (gfE + 1) ≤ jhTw (n + 1) := by
    intro n
    induction n with
    | zero =>
      show gfE + 1 ≤ gfE ^ gfE
      have : gfE ^ (1 : Ordinal.{0}) < gfE ^ gfE := (opow_lt_opow_iff_right gw_one_lt).2 gw_one_lt
      rw [opow_one] at this
      exact Order.add_one_le_of_lt this
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      show ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (gfE + 1)) ≤ gfE ^ jhTw (n + 1)
      calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (gfE + 1)) ≤ ω ^ jhTw (n + 1) := opow_le_opow_right omega0_pos ih
        _ ≤ gfE ^ jhTw (n + 1) := opow_le_opow_left _ (omega_lt_Om1.trans Om1_lt_eW).le
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hle n)⟩

theorem jhB_lim : IsSuccLimit jhB := ev_isSuccLimit_of_inE jhB_E

theorem jhB_lt_G0 : jhB < gcG 0 := by
  have hSC := gcG_SC 0
  have hE : InE (gcG 0) := Low.opow_eq_self_of_SC hSC
  have h1 : evIx gfE + 1 < gcG 0 :=
    (ev_isSuccLimit_of_inE hE).add_one_lt ((evIx_le eW_E).trans_lt (gcG_eW_lt 0))
  have e : jhB = veblen 1 (evIx gfE + 1) := by
    have h := evA_add_one gfE 0
    rw [evA_zero eW_E, zero_add] at h
    rw [jhB, ← h]; rfl
  rw [e]
  exact hSC.2 1 (gw_one_lt.trans (gcG_eW_lt 0)) _ h1

end Googology.Trans.PoR.InaccPsi.R2.Gj
