import Googology.Trans.PoR.InaccPsi.R2.GnImg

/-!
# HEREDITARY CODES TO THE BASE `Γ_{Ω₁+1}`: `Γ_{Ω₁+1}^k·d + r` below `ε_{Γ_{Ω₁+1}+1}`

`R2.GmQ0` reads the codes `Γ_{Ω₁+1}·γ + c'` (`γ, c' < Γ_{Ω₁+1}`).  Every `c` with `G ≤ c < ε_{G+1}`
(`G = Γ_{Ω₁+1}`, the next `ε`-number after `G`) has `log_G c < c`, so the exponent can itself be read
recursively: `gnR c x = Γ_{x+1}^{k(x)}·d(x) + r(x)` with `k(x) = gnR k x` (hereditary Cantor normal form to the base
`G`, digits `d < G` read by `Gl.glR`).  This is `R2.GjHC` with the base `ε_{Ω₁+1}` replaced by `Γ_{Ω₁+1}` and the
digits `rdc` by `glR`.  The codes `Γ_{Ω₁+1}^k` (`k < ω`), `Γ_{Ω₁+1}^ω`, `Γ_{Ω₁+1}^{Γ_{Ω₁+1}}`, … are among them.

* `gnB` (`ε_{Γ_{Ω₁+1}+1}`), `gn_pow_eq`, `gn_cnf`, `gn_parts`, `gn_log_lt` (**`log_G c < c` for `G ≤ c < ε_{G+1}`**),
  `gnR`, `gnG`, `gnQ`, the unfolding lemmas, `gnR_cnf`, `gnG_cnf`, `gnR_G`, `gnG_G`, `gnR_low`, `gnG_low`;
* `gn_one_add`, `gnQ_one_add`, `gnB` facts (`gnB < Γ_{Ω₁+2}`, a limit, `gnB < Γ_{Ω₁+1+gnB}`), the towers `gnTw`
  (`G`, `G^G`, `G^{G^G}`, …, cofinal in `gnB`).

No new axiom.  New definitions: `gnB`, `gnR`, `gnG`, `gnQ`, `gnTw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The base `G = Γ_{Ω₁+1}` -/

theorem gn_one_lt : (1 : Ordinal.{0}) < gcG 0 := gl_one_lt_G0

theorem gn_ne_of_le {c : Ordinal.{0}} (h : gcG 0 ≤ c) : c ≠ 0 := (lt_of_lt_of_le gl_G0_E.pos h).ne'

theorem gn_pow_eq (k : Ordinal.{0}) : gcG 0 ^ k = ω ^ (gcG 0 * k) := by
  rw [opow_mul, geG_E]

theorem gn_pow_indec {k : Ordinal.{0}} : ∀ u v, u < gcG 0 ^ k → v < gcG 0 ^ k → u + v < gcG 0 ^ k := by
  intro u v hu hv
  rw [gn_pow_eq] at hu hv ⊢
  exact isPrincipal_add_omega0_opow _ hu hv

/-- **The normal form** `G^k·d + r`. -/
theorem gn_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gcG 0) (hr : r < gcG 0 ^ k) :
    log (gcG 0) (gcG 0 ^ k * d + r) = k ∧ (gcG 0 ^ k * d + r) / gcG 0 ^ k = d ∧
      (gcG 0 ^ k * d + r) % gcG 0 ^ k = r ∧ gcG 0 ≤ gcG 0 ^ k * d + r := by
  have hp : gcG 0 ^ k ≠ 0 := opow_ne_zero _ mg_G0_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [log_opow_mul_add gn_one_lt hd0 hr, log_eq_zero hdE, add_zero]
  · rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  · calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gcG 0 ^ k := opow_le_opow_right gl_G0_E.pos (one_le_iff_ne_zero.2 hk)
      _ = gcG 0 ^ k * 1 := (mul_one _).symm
      _ ≤ gcG 0 ^ k * d := mul_le_mul_left' (one_le_iff_ne_zero.2 hd0) _
      _ ≤ _ := le_self_add

/-- **The parts of a code `c ≥ G`.** -/
theorem gn_parts0 {c : Ordinal.{0}} (hc : gcG 0 ≤ c) :
    log (gcG 0) c ≠ 0 ∧ c / gcG 0 ^ log (gcG 0) c ≠ 0 ∧ c / gcG 0 ^ log (gcG 0) c < gcG 0 ∧
      c % gcG 0 ^ log (gcG 0) c < gcG 0 ^ log (gcG 0) c ∧
      gcG 0 ^ log (gcG 0) c * (c / gcG 0 ^ log (gcG 0) c) + c % gcG 0 ^ log (gcG 0) c = c := by
  have hc0 := gn_ne_of_le hc
  refine ⟨?_, (div_opow_log_pos (gcG 0) hc0).ne', div_opow_log_lt c gn_one_lt,
    Ordinal.mod_lt c (opow_ne_zero _ mg_G0_ne), Ordinal.div_add_mod c _⟩
  have := le_log_of_opow_le gn_one_lt (show gcG 0 ^ (1 : Ordinal.{0}) ≤ c by rw [opow_one]; exact hc)
  exact (zero_lt_one.trans_le this).ne'

/-! ## The bound `ε_{G+1}` -/

/-- **The bound**: `ε_{Γ_{Ω₁+1}+1}`, the least `ε`-number above `G = Γ_{Ω₁+1}`. -/
noncomputable def gnB : Ordinal.{0} := eN (gcG 0)

theorem gnB_E : InE gnB := eN_E (gcG 0)

theorem gn_G0_lt_B : gcG 0 < gnB := lt_eN (gcG 0)

theorem gnB_lim : IsSuccLimit gnB := ev_isSuccLimit_of_inE gnB_E

/-- **`log_G c < c` for `G ≤ c < ε_{G+1}`**: otherwise `c = G^c` would be an `ε`-number in `(G, ε_{G+1})`. -/
theorem gn_log_lt {c : Ordinal.{0}} (h1 : gcG 0 ≤ c) (h2 : c < gnB) : log (gcG 0) c < c := by
  have hc0 := gn_ne_of_le h1
  have hle : gcG 0 ^ log (gcG 0) c ≤ c := opow_log_le_self (gcG 0) hc0
  have hl1 : 1 ≤ log (gcG 0) c := le_log_of_opow_le gn_one_lt (by rw [opow_one]; exact h1)
  rcases (right_le_opow (log (gcG 0) c) gn_one_lt).lt_or_eq with h | h
  · exact h.trans_le hle
  exfalso
  set l := log (gcG 0) c with hl
  have hlE : InE l := by
    refine le_antisymm ?_ (right_le_opow l one_lt_omega0)
    calc ω ^ l ≤ ω ^ (gcG 0 * l) := opow_le_opow_right omega0_pos (le_mul_right l gl_G0_E.pos)
      _ = gcG 0 ^ l := (gn_pow_eq l).symm
      _ = l := h.symm
  have hEl : gcG 0 ≤ l := by
    rw [h]; calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ gcG 0 ^ l := opow_le_opow_right gl_G0_E.pos hl1
  rcases hEl.lt_or_eq with hlt | heq
  · exact absurd ((eN_le hlt hlE).trans_lt ((right_le_opow l gn_one_lt).trans_lt (hle.trans_lt h2))) (lt_irrefl _)
  · have : gcG 0 ^ (1 : Ordinal.{0}) < gcG 0 ^ gcG 0 := (opow_lt_opow_iff_right gn_one_lt).2 gn_one_lt
    rw [opow_one] at this
    rw [← heq] at h
    exact absurd h this.ne

/-! ## The reading and the gate -/

/-- **The reading** of `c = G^k·d + r` at `x`: `Γ_{x+1}^{k(x)}·d(x) + r(x)`, the exponent read recursively; below
`G` the reading `Gl.glR`. -/
noncomputable def gnR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c ∧ c < gnB then
    lgG x ^ gnR (log (gcG 0) c) x * glR (c / gcG 0 ^ log (gcG 0) c) x + gnR (c % gcG 0 ^ log (gcG 0) c) x
  else glR c x
termination_by c
decreasing_by
  all_goals first
    | exact gn_log_lt h.1 h.2
    | exact mod_opow_log_lt_self (gcG 0) (gn_ne_of_le h.1)

/-- **The gate** of `c = G^k·d + r`: the gate of `k` when infinite, of `d` when infinite, and of `r`. -/
noncomputable def gnG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c ∧ c < gnB then
    max (max (if log (gcG 0) c < ω then 0 else gnG (log (gcG 0) c)) (glQ (c / gcG 0 ^ log (gcG 0) c)))
      (gnG (c % gcG 0 ^ log (gcG 0) c))
  else glG c
termination_by c
decreasing_by
  all_goals first
    | exact gn_log_lt h.1 h.2
    | exact mod_opow_log_lt_self (gcG 0) (gn_ne_of_le h.1)

/-- **The gate of an exponent**: `0` when finite. -/
noncomputable def gnQ (k : Ordinal.{0}) : Ordinal.{0} := if k < ω then 0 else gnG k

theorem gnR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : gnR c x = glR c x := by
  rw [gnR, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

theorem gnG_low {c : Ordinal.{0}} (hc : c < gcG 0) : gnG c = glG c := by
  rw [gnG, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

/-- Above the bound the reading is the identity (so that `+1` is kept everywhere). -/
theorem gnR_high {c : Ordinal.{0}} (hc : gnB ≤ c) (x : Ordinal.{0}) : gnR c x = c := by
  rw [gnR, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), glR_high (gn_G0_lt_B.le.trans hc)]

theorem gnG_high {c : Ordinal.{0}} (hc : gnB ≤ c) : gnG c = 0 := by
  rw [gnG, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), glG_high (gn_G0_lt_B.le.trans hc)]

theorem gnR_dec {c : Ordinal.{0}} (hc : gcG 0 ≤ c) (hcB : c < gnB) (x : Ordinal.{0}) :
    gnR c x = lgG x ^ gnR (log (gcG 0) c) x * glR (c / gcG 0 ^ log (gcG 0) c) x +
      gnR (c % gcG 0 ^ log (gcG 0) c) x := by
  rw [gnR, dif_pos ⟨hc, hcB⟩]

theorem gnG_dec {c : Ordinal.{0}} (hc : gcG 0 ≤ c) (hcB : c < gnB) :
    gnG c = max (max (gnQ (log (gcG 0) c)) (glQ (c / gcG 0 ^ log (gcG 0) c))) (gnG (c % gcG 0 ^ log (gcG 0) c)) := by
  rw [gnG, dif_pos ⟨hc, hcB⟩]; rfl

theorem gnQ_le (k : Ordinal.{0}) : gnQ k ≤ gnG k := by
  unfold gnQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem gnQ_low {k : Ordinal.{0}} (hk : k < gcG 0) : gnQ k = glQ k := by
  unfold gnQ glQ; rw [gnG_low hk]

theorem gnQ_nat (n : ℕ) : gnQ n = 0 := by unfold gnQ; rw [if_pos (natCast_lt_omega0 n)]

theorem gnR_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gcG 0) (hr : r < gcG 0 ^ k)
    (hB : gcG 0 ^ k * d + r < gnB) (x : Ordinal.{0}) :
    gnR (gcG 0 ^ k * d + r) x = lgG x ^ gnR k x * glR d x + gnR r x := by
  obtain ⟨h1, h2, h3, h4⟩ := gn_cnf hk hd0 hdE hr
  rw [gnR_dec h4 hB, h1, h2, h3]

theorem gnG_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < gcG 0) (hr : r < gcG 0 ^ k)
    (hB : gcG 0 ^ k * d + r < gnB) : gnG (gcG 0 ^ k * d + r) = max (max (gnQ k) (glQ d)) (gnG r) := by
  obtain ⟨h1, h2, h3, h4⟩ := gn_cnf hk hd0 hdE hr
  rw [gnG_dec h4 hB, h1, h2, h3]

theorem gnG_zero : gnG 0 = 0 := by rw [gnG_low gl_G0_E.pos, glG_zero]

theorem gnR_zero (x : Ordinal.{0}) : gnR 0 x = 0 := by rw [gnR_low gl_G0_E.pos, glR_zero]

theorem gnR_one (x : Ordinal.{0}) : gnR 1 x = 1 := by rw [gnR_low gn_one_lt, glR_one]

theorem gn_nat_lt_G0 (n : ℕ) : (n : Ordinal.{0}) < gcG 0 := (gl_nat_lt_Om1 n).trans gl_Om1_lt_G0

theorem gnR_nat (n : ℕ) (x : Ordinal.{0}) : gnR n x = n := by rw [gnR_low (gn_nat_lt_G0 n), glR_nat]

theorem gnG_nat (n : ℕ) : gnG n = n := by rw [gnG_low (gn_nat_lt_G0 n), glG_nat]

theorem gnB_gt_pow {k : Ordinal.{0}} (hk : k < gnB) : gcG 0 ^ k < gnB := by
  rw [gn_pow_eq]; exact gnB_E.opow_lt (gnB_E.mul_lt gn_G0_lt_B hk)

theorem gn_mul_lt {k d : Ordinal.{0}} (hk : k < gnB) (hd : d < gcG 0) : gcG 0 ^ k * d < gnB :=
  gnB_E.mul_lt (gnB_gt_pow hk) (hd.trans gn_G0_lt_B)

theorem gn_G0_cnf : gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]

theorem gnG_G : gnG (gcG 0) = 0 := by
  rw [gn_G0_cnf, gnG_cnf one_ne_zero one_ne_zero gn_one_lt (opow_pos _ gl_G0_E.pos)
    (by rw [← gn_G0_cnf]; exact gn_G0_lt_B), glQ_one, gnG_zero]
  have : gnQ 1 = 0 := by exact_mod_cast gnQ_nat 1
  rw [this]; simp

theorem gnR_G (x : Ordinal.{0}) : gnR (gcG 0) x = lgG x := by
  rw [gn_G0_cnf, gnR_cnf one_ne_zero one_ne_zero gn_one_lt (opow_pos _ gl_G0_E.pos)
    (by rw [← gn_G0_cnf]; exact gn_G0_lt_B), gnR_one, opow_one, glR_one, mul_one, gnR_zero, add_zero]

/-- The parts of a code `G ≤ c < ε_{G+1}`. -/
theorem gn_parts {c : Ordinal.{0}} (hc : gcG 0 ≤ c) (hcB : c < gnB) :
    log (gcG 0) c ≠ 0 ∧ c / gcG 0 ^ log (gcG 0) c ≠ 0 ∧ c / gcG 0 ^ log (gcG 0) c < gcG 0 ∧
      c % gcG 0 ^ log (gcG 0) c < gcG 0 ^ log (gcG 0) c ∧
      gcG 0 ^ log (gcG 0) c * (c / gcG 0 ^ log (gcG 0) c) + c % gcG 0 ^ log (gcG 0) c = c ∧
      log (gcG 0) c < c ∧ c % gcG 0 ^ log (gcG 0) c < c :=
  let ⟨h1, h2, h3, h4, h5⟩ := gn_parts0 hc
  ⟨h1, h2, h3, h4, h5, gn_log_lt hc hcB, mod_opow_log_lt_self (gcG 0) (gn_ne_of_le hc)⟩

/-- The normal form of `b + 1` for `b ≥ G`. -/
theorem gn_succ_cnf {b : Ordinal.{0}} (hEb : gcG 0 ≤ b) :
    b + 1 = gcG 0 ^ log (gcG 0) b * (b / gcG 0 ^ log (gcG 0) b) + (b % gcG 0 ^ log (gcG 0) b + 1) ∧
      b % gcG 0 ^ log (gcG 0) b + 1 < gcG 0 ^ log (gcG 0) b := by
  obtain ⟨hk, -, -, hr, hdec⟩ := gn_parts0 hEb
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← hdec]
    rw [add_assoc]
  · rw [gn_pow_eq] at hr ⊢
    have hk0 : gcG 0 * log (gcG 0) b ≠ 0 := mul_ne_zero mg_G0_ne hk
    exact (Ph.ph_opow_lim hk0).add_one_lt hr

/-! ## `1 + a` -/

theorem gn_one_add {a : Ordinal.{0}} (ha : ω ≤ a) : 1 + a = a := one_add_of_omega0_le ha

theorem gnQ_one_add (a : Ordinal.{0}) : gnQ (1 + a) = gnQ a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, gnQ_nat, gnQ_nat]
  · rw [gn_one_add ha]

/-! ## The towers `G`, `G^G`, `G^{G^G}`, … -/

/-- The towers: `gnTw 0 = G`, `gnTw (n+1) = G^{gnTw n}`. -/
noncomputable def gnTw : ℕ → Ordinal.{0}
  | 0 => gcG 0
  | n + 1 => gcG 0 ^ gnTw n

theorem gnTw_lt : ∀ n : ℕ, gnTw n < gnB
  | 0 => gn_G0_lt_B
  | n + 1 => gnB_gt_pow (gnTw_lt n)

theorem gnTw_ge : ∀ n : ℕ, gcG 0 ≤ gnTw n
  | 0 => le_rfl
  | n + 1 => by
    show gcG 0 ≤ gcG 0 ^ gnTw n
    calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right gl_G0_E.pos (gn_one_lt.le.trans (gnTw_ge n))

theorem gnTw_strict (n : ℕ) : gnTw n < gnTw (n + 1) := by
  show gnTw n < gcG 0 ^ gnTw n
  have h1 := gn_log_lt (c := gcG 0 ^ gnTw n) ((gnTw_ge n).trans (right_le_opow _ gn_one_lt)) (gnTw_lt (n + 1))
  rwa [log_opow gn_one_lt] at h1

theorem gnTw_cof {c : Ordinal.{0}} (hc : c < gnB) : ∃ n : ℕ, c < gnTw n := by
  have hle : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (gcG 0 + 1) ≤ gnTw (n + 1) := by
    intro n
    induction n with
    | zero =>
      show gcG 0 + 1 ≤ gcG 0 ^ gcG 0
      have : gcG 0 ^ (1 : Ordinal.{0}) < gcG 0 ^ gcG 0 := (opow_lt_opow_iff_right gn_one_lt).2 gn_one_lt
      rw [opow_one] at this
      exact Order.add_one_le_of_lt this
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      show ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (gcG 0 + 1)) ≤ gcG 0 ^ gnTw (n + 1)
      calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (gcG 0 + 1)) ≤ ω ^ gnTw (n + 1) :=
            opow_le_opow_right omega0_pos ih
        _ ≤ gcG 0 ^ gnTw (n + 1) := opow_le_opow_left _ (omega0_lt_inE gl_G0_E).le
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hle n)⟩

/-- `ε_{G+1} < Γ_{Ω₁+2}`. -/
theorem gnB_lt_G1 : gnB < gcG 1 := by
  have hSC := gcG_SC 1
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC hSC
  have hG01 : gcG 0 < gcG 1 := gcG_lt zero_lt_one
  have h1 : evIx (gcG 0) + 1 < gcG 1 :=
    (ev_isSuccLimit_of_inE hE).add_one_lt ((evIx_le gl_G0_E).trans_lt hG01)
  have e : gnB = veblen 1 (evIx (gcG 0) + 1) := by
    have h := evA_add_one (gcG 0) 0
    rw [evA_zero gl_G0_E, zero_add] at h
    rw [gnB, ← h]; rfl
  rw [e]
  exact hSC.2 1 (gn_one_lt.trans hG01) _ h1

/-- `ε_{G+1} < Γ_{Ω₁+1+ε_{G+1}}` (the bound condition of a code system). -/
theorem gnB_V : gnB < gcG gnB :=
  gnB_lt_G1.trans_le (gcG_le (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le gn_G0_lt_B)))

end Googology.Trans.PoR.InaccPsi.R2.Gn
