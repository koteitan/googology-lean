import Googology.Trans.PoR.InaccPsi.R2.GlAt

/-!
# CODES BELOW `Γ_{Ω₁+1}`, GENERIC IN THE VEBLEN LEVEL: one reading, the definitions

Every code `c` with `ε_{Ω₁+1} ≤ c < Γ_{Ω₁+1}` lies in exactly one bracket `[e, ε_{e+1})` with `e = guE c` the largest
`ε`-number `≤ c`; `e = glPsi α η` (`R2.GlVb`: level `α = glK e ≥ 1`, index `η = glI e`, both below `e`), and
`c = e^j·d + r` (`j = log_e c < c`, `0 < d < e`, `r < e^j`).  The reading replaces `e` by the atom
`ϑˣ(Ω₁·α(x) + η(x))` with the READ level:

  `glR c x = ϑˣ(Ω₁·α(x) + η(x))^{j(x)}·d(x) + r(x)`  (codes below `ε_{Ω₁+1}` read by `rdc`, `Ω₁ ↦ x`),

one well-founded recursion for all bases and ALL levels `1 ≤ α < Γ_{Ω₁+1}` at once (the `ε`-atoms of round 82 are
`α = 1`, the `ζ`-atoms `α = 2`, the level `Ω₁` reads `x`, …).  The atom at `(1, 0)` is written `ε_{x+1}` (`glBA`) so
that `ε_{Ω₁+1}` reads `ε_{x+1}` at every `x`.

* `gl_N_spec` (the bracket of every code `≥ ε_{Ω₁+1}`), `gl_parts`, `gl_idx_lt`, `gl_lev_lt` (**the index and the
  level of the bracket's `ε`-number are below the code**), `gl_cnf`;
* `glBA`, `glBA_eq`, `glR`, `glG`, `glQ`, `glQE` (the gate of an `ε`-number code as a base), the unfolding lemmas
  `glR_dec`, `glG_dec`, `glR_low`, `glG_low`, `glR_high`,
  `glG_high`, `glR_cnf`, `glG_cnf`, `glR_base` (**`glPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))`**), `glG_base`, `glR_E`,
  `glG_E`.

No new axiom.  New definitions: `glBA`, `glR`, `glG`, `glQ`, `glQE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **The bracket** of a code `c ≥ ε_{Ω₁+1}`: `e = ε_{Ω₁+guN c} ≤ c < ε_{e+1}`, `1 ≤ guN c`. -/
theorem gl_N_spec {c : Ordinal.{0}} (h1 : gfE ≤ c) :
    1 ≤ guN c ∧ evA Om1 (guN c) ≤ c ∧ c < evA Om1 (guN c + 1) := by
  have hOc : Om1 ≤ c := Om1_lt_eW.le.trans h1
  have hcC : c < evA Om1 (c + 1) := (lt_add_one c).trans_le (le_evA_idx Om1 (c + 1))
  obtain ⟨n, -, hn1, hn2⟩ := evA_bracket gu_Om1_E hOc hcC
  have he := guN_eq hn1 hn2
  rw [he]
  have h1n : 1 ≤ n := by
    by_contra h0
    push Not at h0
    rw [lt_one_iff_zero] at h0
    rw [h0, zero_add, gu_evA_one] at hn2
    exact absurd h1 (not_le.2 hn2)
  exact ⟨h1n, hn1, hn2⟩

theorem gl_E_le {c : Ordinal.{0}} (h1 : gfE ≤ c) : guE c ≤ c := (gl_N_spec h1).2.1

theorem gl_lt_eN {c : Ordinal.{0}} (h1 : gfE ≤ c) : c < eN (guE c) := by
  rw [guE, ← evA_add_one]; exact (gl_N_spec h1).2.2

theorem gl_Om1_lt_E {c : Ordinal.{0}} (h1 : gfE ≤ c) : Om1 < guE c := by
  have h := (gl_N_spec h1).1
  calc Om1 < gfE := Om1_lt_eW
    _ = evA Om1 1 := gu_evA_one.symm
    _ ≤ evA Om1 (guN c) := evA_le_iff.2 h

theorem gl_gfE_le_E {c : Ordinal.{0}} (h1 : gfE ≤ c) : gfE ≤ guE c := by
  rw [← gu_evA_one]; exact evA_le_iff.2 (gl_N_spec h1).1

/-- **The data of the bracket's `ε`-number**: `guE c = glPsi α η` with `α = glK (guE c) ≥ 1`, `η = glI (guE c)`. -/
theorem gl_E_data {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) :
    1 ≤ glK (guE c) ∧ glK (guE c) < guE c ∧ glI (guE c) < guE c ∧ glPsi (glK (guE c)) (glI (guE c)) = guE c :=
  glData_spec (guE_E c) (gl_Om1_lt_E h1) ((gl_E_le h1).trans_lt h2)

/-- **The index of the bracket's `ε`-number lies below the code.** -/
theorem gl_idx_lt {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) : glI (guE c) < c :=
  (gl_E_data h1 h2).2.2.1.trans_le (gl_E_le h1)

/-- **The level of the bracket's `ε`-number lies below the code.** -/
theorem gl_lev_lt {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) : glK (guE c) < c :=
  (gl_E_data h1 h2).2.1.trans_le (gl_E_le h1)

/-- **The parts of a code** `ε_{Ω₁+1} ≤ c`: `c = e^j·d + r` with `e = guE c`, all parts below `c`. -/
theorem gl_parts {c : Ordinal.{0}} (h1 : gfE ≤ c) :
    log (guE c) c ≠ 0 ∧ c / guE c ^ log (guE c) c ≠ 0 ∧ c / guE c ^ log (guE c) c < guE c ∧
      c % guE c ^ log (guE c) c < guE c ^ log (guE c) c ∧
      guE c ^ log (guE c) c * (c / guE c ^ log (guE c) c) + c % guE c ^ log (guE c) c = c ∧
      log (guE c) c < c ∧ c % guE c ^ log (guE c) c < c ∧ c / guE c ^ log (guE c) c < c := by
  have hEc := gl_E_le h1
  have hcN' := gl_lt_eN h1
  have hE := guE_E c
  have hE1 : (1 : Ordinal.{0}) < guE c := Lu.lu_one_lt_E hE
  have hc0 : c ≠ 0 := (lt_of_lt_of_le hE.pos hEc).ne'
  have hk1 := le_log_of_opow_le hE1 (show guE c ^ (1 : Ordinal.{0}) ≤ c by rw [opow_one]; exact hEc)
  have hdE := div_opow_log_lt c hE1
  exact ⟨(zero_lt_one.trans_le hk1).ne', (div_opow_log_pos (guE c) hc0).ne', hdE,
    Ordinal.mod_lt c (opow_ne_zero _ hE.pos.ne'), Ordinal.div_add_mod c _, gu_log_lt hE hEc hcN',
    mod_opow_log_lt_self _ hc0, hdE.trans_le hEc⟩

/-- Every `ε`-number `e > Ω₁` is the bracket of `e^j·d + r` for `j ≠ 0`, `0 < d < e`, `r < e^j`, below `ε_{e+1}`. -/
theorem gl_cnf {e j d r : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) :
    guE (e ^ j * d + r) = e ∧ log e (e ^ j * d + r) = j ∧ (e ^ j * d + r) / e ^ j = d ∧
      (e ^ j * d + r) % e ^ j = r ∧ gfE ≤ e ^ j * d + r := by
  obtain ⟨n, hn⟩ := evA_surj gu_Om1_E he hOe.le
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have hp : e ^ j ≠ 0 := opow_ne_zero _ he.pos.ne'
  have hEv : e ≤ e ^ j * d + r := by
    calc e = e ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ e ^ j := opow_le_opow_right he.pos (one_le_iff_ne_zero.2 hj)
      _ = e ^ j * 1 := (mul_one _).symm
      _ ≤ e ^ j * d := mul_le_mul_right (one_le_iff_ne_zero.2 hd0) _
      _ ≤ _ := le_self_add
  have hN : guN (e ^ j * d + r) = n := guN_eq (by rw [hn]; exact hEv) (by rw [evA_add_one, hn]; exact hv)
  refine ⟨by rw [guE, hN, hn], ?_, ?_, ?_, eN_le hOe he |>.trans hEv⟩
  · rw [log_opow_mul_add hE1 hd0 hr, log_eq_zero hde, add_zero]
  · rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-! ## The reading and the gate -/

/-- **The atom of the base reading**: `ϑˣ(Ω₁·β + t)`, written `ε_{x+1}` at `(β, t) = (1, 0)`. -/
noncomputable def glBA (β t x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if β = 1 ∧ t = 0 then eN x else glA β t x

theorem glBA_eq {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (β t : Ordinal.{0}) :
    glBA β t x = glA β t x := by
  unfold glBA
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; exact (glA_one_zero hx hx1).symm
  · rfl

theorem glBA_one_zero (x : Ordinal.{0}) : glBA 1 0 x = eN x := by unfold glBA; rw [if_pos ⟨rfl, rfl⟩]

/-- **The reading** of a code at `x`: `ϑˣ(Ω₁·α(x) + η(x))^{j(x)}·d(x) + r(x)` above `ε_{Ω₁+1}` (`α = glK e`,
`η = glI e`, `e = guE c`), `rdc` below, the identity at and above `Γ_{Ω₁+1}`. -/
noncomputable def glR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c ∧ c < gcG 0 then
    glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ^ glR (log (guE c) c) x *
      glR (c / guE c ^ log (guE c) c) x + glR (c % guE c ^ log (guE c) c) x
  else if c < gfE then rdc c x else c
termination_by c
decreasing_by
  all_goals first
    | exact gl_lev_lt h.1 h.2
    | exact gl_idx_lt h.1 h.2
    | exact (gl_parts h.1).2.2.2.2.2.1
    | exact (gl_parts h.1).2.2.2.2.2.2.2
    | exact (gl_parts h.1).2.2.2.2.2.2.1

/-- **The gate** of a code: the gates of its infinite level, index, exponent and digit, and of its rest. -/
noncomputable def glG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gfE ≤ c ∧ c < gcG 0 then
    max (max (max (if glK (guE c) < ω then 0 else glG (glK (guE c)))
          (if glI (guE c) < ω then 0 else glG (glI (guE c))))
        (if log (guE c) c < ω then 0 else glG (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else glG (c / guE c ^ log (guE c) c))
        (glG (c % guE c ^ log (guE c) c)))
  else if c < gfE then gtc c else 0
termination_by c
decreasing_by
  all_goals first
    | exact gl_lev_lt h.1 h.2
    | exact gl_idx_lt h.1 h.2
    | exact (gl_parts h.1).2.2.2.2.2.1
    | exact (gl_parts h.1).2.2.2.2.2.2.2
    | exact (gl_parts h.1).2.2.2.2.2.2.1

/-- **The gate of a part**: `0` when finite. -/
noncomputable def glQ (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else glG a

/-- **The gate of an `ε`-number code as a base**: the gates of its level and its index as parts. -/
noncomputable def glQE (e : Ordinal.{0}) : Ordinal.{0} := max (glQ (glK e)) (glQ (glI e))

theorem glR_low {c : Ordinal.{0}} (hc : c < gfE) (x : Ordinal.{0}) : glR c x = rdc c x := by
  rw [glR, dif_neg (fun h => absurd h.1 (not_le.2 hc)), if_pos hc]

theorem glG_low {c : Ordinal.{0}} (hc : c < gfE) : glG c = gtc c := by
  rw [glG, dif_neg (fun h => absurd h.1 (not_le.2 hc)), if_pos hc]

theorem glR_high {c : Ordinal.{0}} (hc : gcG 0 ≤ c) (x : Ordinal.{0}) : glR c x = c := by
  have hE : ¬ c < gfE := not_lt.2 (gfE_lt_G0.le.trans hc)
  rw [glR, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), if_neg hE]

theorem glG_high {c : Ordinal.{0}} (hc : gcG 0 ≤ c) : glG c = 0 := by
  have hE : ¬ c < gfE := not_lt.2 (gfE_lt_G0.le.trans hc)
  rw [glG, dif_neg (fun h => absurd h.2 (not_lt.2 hc)), if_neg hE]

theorem glR_dec {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) (x : Ordinal.{0}) :
    glR c x = glBA (glR (glK (guE c)) x) (glR (glI (guE c)) x) x ^ glR (log (guE c) c) x *
      glR (c / guE c ^ log (guE c) c) x + glR (c % guE c ^ log (guE c) c) x := by
  rw [glR, dif_pos ⟨h1, h2⟩]

theorem glG_dec {c : Ordinal.{0}} (h1 : gfE ≤ c) (h2 : c < gcG 0) :
    glG c = max (max (glQE (guE c)) (glQ (log (guE c) c)))
      (max (glQ (c / guE c ^ log (guE c) c)) (glG (c % guE c ^ log (guE c) c))) := by
  rw [glG, dif_pos ⟨h1, h2⟩]; rfl

theorem glQ_le (a : Ordinal.{0}) : glQ a ≤ glG a := by
  unfold glQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem glR_zero (x : Ordinal.{0}) : glR 0 x = 0 := by rw [glR_low eW_E.pos, rdc_zero]

theorem glG_zero : glG 0 = 0 := by rw [glG_low eW_E.pos, gtc_zero]

theorem glR_nat (n : ℕ) (x : Ordinal.{0}) : glR n x = n := by
  have hn : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1
  rw [glR_low (hn.trans Om1_lt_eW), (rdc_const hn x).1]

theorem glR_one (x : Ordinal.{0}) : glR 1 x = 1 := by exact_mod_cast glR_nat 1 x

theorem glG_nat (n : ℕ) : glG n = n := by
  have hn : (n : Ordinal.{0}) < Om1 := (natCast_lt_omega0 n).trans omega_lt_Om1
  rw [glG_low (hn.trans Om1_lt_eW), (rdc_const hn 0).2]

theorem glQ_nat (n : ℕ) : glQ n = 0 := by unfold glQ; rw [if_pos (natCast_lt_omega0 n)]

theorem glQ_one : glQ 1 = 0 := by exact_mod_cast glQ_nat 1

theorem glQ_zero : glQ 0 = 0 := by exact_mod_cast glQ_nat 0

/-- The gate of a part from its gate as a part, below every `Z > ω`. -/
theorem glG_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : glQ a < Z) : glG a < Z := by
  unfold glQ at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [glG_nat]; exact (natCast_lt_omega0 n).trans hωZ
  · exact h

theorem glR_cnf {e j d r : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hB : e ^ j * d + r < gcG 0) (x : Ordinal.{0}) :
    glR (e ^ j * d + r) x = glBA (glR (glK e) x) (glR (glI e) x) x ^ glR j x * glR d x + glR r x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := gl_cnf he hOe hj hd0 hde hr hv
  rw [glR_dec h5 hB, h1, h2, h3, h4]

theorem glG_cnf {e j d r : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hB : e ^ j * d + r < gcG 0) :
    glG (e ^ j * d + r) = max (max (glQE e) (glQ j)) (max (glQ d) (glG r)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := gl_cnf he hOe hj hd0 hde hr hv
  rw [glG_dec h5 hB, h1, h2, h3, h4]

/-- An `ε`-number code `e` as the normal form `e^1·1 + 0`. -/
theorem gl_base_nf {e : Ordinal.{0}} (he : InE e) :
    e = e ^ (1 : Ordinal.{0}) * 1 + 0 ∧ e ^ (1 : Ordinal.{0}) * 1 + 0 < eN e := by
  rw [opow_one, mul_one, add_zero]
  exact ⟨rfl, lt_eN e⟩

/-- **The base reading** of an `ε`-number code `e ∈ (Ω₁, Γ_{Ω₁+1})`: `ϑˣ(Ω₁·α(x) + η(x))`. -/
theorem glR_base {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) (x : Ordinal.{0}) :
    glR e x = glBA (glR (glK e) x) (glR (glI e) x) x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := glR_cnf he hOe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 (h1 ▸ heB) x
  rw [← h1] at h
  rw [h, glR_one, glR_zero, opow_one, mul_one, add_zero]

/-- The gate of an `ε`-number code is the gate of its level and index as parts. -/
theorem glG_base {e : Ordinal.{0}} (he : InE e) (hOe : Om1 < e) (heB : e < gcG 0) : glG e = glQE e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := glG_cnf he hOe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 (h1 ▸ heB)
  rw [← h1] at h
  rw [h, glQ_one, glG_zero]
  simp

/-- **`glPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))`** (`1 ≤ α`, `α, η < Γ_{Ω₁+1}`). -/
theorem glR_psi {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 0) {η : Ordinal.{0}} (hηG : η < gcG 0)
    (x : Ordinal.{0}) : glR (glPsi α η) x = glBA (glR α x) (glR η x) x := by
  obtain ⟨e1, e2⟩ := glData_eq hα hαG hηG
  rw [glR_base (glPsi_E hα η) (glPsi_gt hα hαG η).1 (glPsi_lt_G hαG hηG), e1, e2]

theorem glG_psi {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 0) {η : Ordinal.{0}} (hηG : η < gcG 0) :
    glG (glPsi α η) = max (glQ α) (glQ η) := by
  rw [glG_base (glPsi_E hα η) (glPsi_gt hα hαG η).1 (glPsi_lt_G hαG hηG), glQE, (glData_eq hα hαG hηG).1,
    (glData_eq hα hαG hηG).2]

theorem glR_E (x : Ordinal.{0}) : glR gfE x = eN x := by
  rw [← gl_E_eq, glR_psi le_rfl gl_one_lt_G0 gl_G0_E.pos, glR_zero, glR_one, glBA_one_zero]

theorem glG_E : glG gfE = 0 := by
  rw [← gl_E_eq, glG_psi le_rfl gl_one_lt_G0 gl_G0_E.pos, glQ_zero, glQ_one, max_self]

end Googology.Trans.PoR.InaccPsi.R2.Gl
