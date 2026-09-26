/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LowerBndRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `referenceRow_coeff` a hypothesis is beta-reduced before a rewrite.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawAscend

set_option backward.do.legacy false

/-!
# Rows of the source mountain near a leg into the root column

Facts of the canonical mountain `M(s)` used by `LowerBndFirst.lean`, all from the jump law of
the canonical mountain (`JumpLaw.source_edge`: the row of a node is `bump σ (jump σ p)` for the
row `σ` below it and the highest row `p` of its leg column below it):

* `root_row_of_leg`: if a node `u` of a column has its leg in the column `c_r` and its row
  agrees with `θ = bump λ (d + 1)` at the exponents `≥ d + 1`, and the column of `u` has a row
  agreeing with `λ` there, then `c_r` has a row agreeing with `λ` at the exponents `≥ d + 1`.
* `pred_rows`: a column with a row `r` has the rows `r - k`, `k ≤ r_0` (only the finite
  coefficient changes).
* `leg_pred_row`: if a node with finite coefficient `m + 1` has its leg in `c_r`, then `c_r` has
  the row with finite coefficient `m` and the same higher coefficients.
* `x0_ascends`: the last column ascends at every node of the root column below `τ`.
-/

namespace OmegaY.Official.Recon.LowerBndSrc

open Canonical Expansion Dimension RowLaw JumpLaw

/-! ## Counting rows below a row -/

theorem filter_lt_mono (l : List Row) {a b : Row} (hab : a ≤ b) :
    (l.filter (fun r => decide (r < a))).length ≤ (l.filter (fun r => decide (r < b))).length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.filter_cons]
    by_cases ha : r < a
    · have hb : r < b := lt_of_lt_of_le ha hab
      simp only [ha, hb, decide_true, if_true, List.length_cons]
      omega
    · by_cases hb : r < b
      · simp only [ha, hb, decide_true, decide_false, if_true, List.length_cons,
          Bool.false_eq_true, if_false]
        omega
      · simp only [ha, hb, decide_false, Bool.false_eq_true, if_false]
        exact ih

theorem filter_lt_strict {l : List Row} {a b : Row} (ha : a ∈ l) (hab : a < b) :
    (l.filter (fun r => decide (r < a))).length < (l.filter (fun r => decide (r < b))).length := by
  induction l with
  | nil => cases ha
  | cons r l ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · simp only [lt_irrefl, hab, decide_true, decide_false, Bool.false_eq_true, if_false,
        if_true, List.length_cons]
      have := filter_lt_mono l hab.le
      omega
    · have ih' := ih ha'
      by_cases hra : r < a
      · have hrb : r < b := hra.trans hab
        simp only [hra, hrb, decide_true, if_true, List.length_cons]
        omega
      · by_cases hrb : r < b
        · simp only [hra, hrb, decide_true, decide_false, if_true, List.length_cons,
            Bool.false_eq_true, if_false]
          omega
        · simp only [hra, hrb, decide_false, Bool.false_eq_true, if_false]
          exact ih'

/-! ## A root row in the region of `λ` -/

/-- One step down the root column: a row `w` of `cr` in the region of `θ = bump λ (d + 1)` has
either the row below it in the region of `λ`, or the row below it again in the region of `θ`. -/
theorem root_row_step {s : List Nat} {M : Mountain} (hb : build s = .ok M) {cr : Nat}
    {lam : Row} {d : Nat} {w : Row} (hw : w ∈ rowsOf M cr)
    (hθ : ∀ m, d + 1 ≤ m → w.coeff m = (Row.bump lam (d + 1)).coeff m) :
    (∃ ρ ∈ realNodes M cr, ∀ m, d + 1 ≤ m → (official ρ.2.row).coeff m = lam.coeff m) ∨
      ∃ σ ∈ rowsOf M cr, σ < w ∧ ∀ m, d + 1 ≤ m → σ.coeff m = (Row.bump lam (d + 1)).coeff m := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
  have hne : official q.2.row ≠ 0 := by
    intro h0
    have := hθ (d + 1) le_rfl
    rw [h0, bump_coeff_at] at this
    simp at this
  obtain ⟨σ, l, ps, hσmem, hσlt, _, hl, _, hps, hpsσ, hrow⟩ := source_edge hb hq hne
  have hat := hθ (d + 1) le_rfl
  rw [hrow, bump_coeff_at] at hat
  rcases Nat.lt_trichotomy (Row.jump σ ps) (d + 1) with hE | hE | hE
  · -- the step is below `d + 1`: `σ` is again in the region of `θ`
    refine Or.inr ⟨σ, hσmem, hσlt, fun m hm => ?_⟩
    rw [← hθ m hm, hrow, bump_coeff_high (by omega)]
  · -- the step is at `d + 1`: `σ` is in the region of `λ`
    obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hσmem
    refine Or.inl ⟨p, hp, fun m hm => ?_⟩
    rw [hprow]
    rcases Nat.eq_or_lt_of_le hm with rfl | hm'
    · rw [hE, bump_coeff_at] at hat
      omega
    · have h1 := hθ m (by omega)
      rw [hrow, hE, bump_coeff_high hm', bump_coeff_high hm'] at h1
      exact h1
  · exfalso
    rw [bump_coeff_low hE] at hat
    omega

/-- **The root column enters the region of `λ`.** A row `w` of the column `cr` that agrees with
`θ = bump λ (d + 1)` at the exponents `≥ d + 1` has a lower row of `cr` that agrees with `λ`
there. -/
theorem root_row_of_high {s : List Nat} {M : Mountain} (hb : build s = .ok M) {cr : Nat}
    {lam : Row} {d : Nat} :
    ∀ (n : Nat) (w : Row), w ∈ rowsOf M cr →
      ((rowsOf M cr).filter (fun r => decide (r < w))).length ≤ n →
      (∀ m, d + 1 ≤ m → w.coeff m = (Row.bump lam (d + 1)).coeff m) →
      ∃ ρ ∈ realNodes M cr, ∀ m, d + 1 ≤ m → (official ρ.2.row).coeff m = lam.coeff m := by
  intro n
  induction n with
  | zero =>
    intro w hw hn hθ
    rcases root_row_step hb hw hθ with h | ⟨σ, hσmem, hσlt, _⟩
    · exact h
    · have := filter_lt_strict hσmem hσlt
      omega
  | succ n ih =>
    intro w hw hn hθ
    rcases root_row_step hb hw hθ with h | ⟨σ, hσmem, hσlt, hσθ⟩
    · exact h
    · have := filter_lt_strict hσmem hσlt
      exact ih σ hσmem (by omega) hσθ

/-- **A leg into `c_r` from the region of `θ`.** If a node `u` of the column `x` has its leg in
`c_r` and its row agrees with `θ = bump λ (d + 1)` at the exponents `≥ d + 1`, and `x` has a row
agreeing with `λ` there, then so does `c_r`. -/
theorem root_row_of_leg {s : List Nat} {M : Mountain} (hb : build s = .ok M) {x cr : Nat}
    {u : Ref × Cell} (hu : u ∈ realNodes M x) (hl : leftColumn u.2 = .ok cr)
    {lam : Row} {d : Nat}
    (hθ : ∀ m, d + 1 ≤ m → (official u.2.row).coeff m = (Row.bump lam (d + 1)).coeff m) :
    ∃ ρ ∈ realNodes M cr, ∀ m, d + 1 ≤ m → (official ρ.2.row).coeff m = lam.coeff m := by
  have hne : official u.2.row ≠ 0 := by
    intro h0
    have := hθ (d + 1) le_rfl
    rw [h0, bump_coeff_at] at this
    simp at this
  obtain ⟨σ, l, ps, _, _, _, hl', _, hps, hpsσ, hrow⟩ := source_edge hb hu hne
  rw [hl] at hl'
  obtain rfl := Except.ok.inj hl'
  have hat := hθ (d + 1) le_rfl
  rw [hrow, bump_coeff_at] at hat
  rcases Nat.lt_trichotomy (Row.jump σ ps) (d + 1) with hE | hE | hE
  · -- `ps` is in the region of `θ`
    have hpsθ : ∀ m, d + 1 ≤ m → ps.coeff m = (Row.bump lam (d + 1)).coeff m := by
      intro m hm
      rw [← Row.coeff_eq_of_jump_le (d := Row.jump σ ps) le_rfl (by omega), ← hθ m hm, hrow,
        bump_coeff_high (by omega)]
    exact root_row_of_high hb _ ps hps.1 le_rfl hpsθ
  · -- `ps` is in the region of `λ`
    obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hps.1
    refine ⟨p, hp, fun m hm => ?_⟩
    rw [hprow, ← Row.coeff_eq_of_jump_le (a := σ) (b := ps) (d := d + 1) (by omega) hm]
    rcases Nat.eq_or_lt_of_le hm with rfl | hm'
    · rw [hE, bump_coeff_at] at hat
      omega
    · have h1 := hθ m (by omega)
      rw [hrow, hE, bump_coeff_high hm', bump_coeff_high hm'] at h1
      exact h1
  · exfalso
    rw [bump_coeff_low hE] at hat
    omega

/-! ## Rows below a row with a finite part -/

theorem referenceRow_coeff {ρ : Row} (h : 0 < ρ.coeff 0) (m : Nat) :
    (referenceRow ρ).coeff m = if m = 0 then ρ.coeff 0 - 1 else ρ.coeff m := by
  have hb := referenceRow_bump h
  split_ifs with hm
  · subst hm
    have := congrArg (fun r => Row.coeff r 0) hb
    simp only [bump_coeff_at] at this
    omega
  · have := congrArg (fun r => Row.coeff r m) hb
    beta_reduce at this
    rw [bump_coeff_high (by omega)] at this
    exact this

/-- **The rows below a row of a canonical column.** -/
theorem pred_rows {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c : Nat} :
    ∀ (k : Nat) (q : Ref × Cell), q ∈ realNodes M c → k ≤ (official q.2.row).coeff 0 →
      ∃ q' ∈ realNodes M c, (official q'.2.row).coeff 0 = (official q.2.row).coeff 0 - k ∧
        ∀ m, 1 ≤ m → (official q'.2.row).coeff m = (official q.2.row).coeff m
  | 0, q, hq, _ => ⟨q, hq, by omega, fun _ _ => rfl⟩
  | k + 1, q, hq, hk => by
    obtain ⟨q1, hq1, h0, hm⟩ := pred_rows hb k q hq (by omega)
    have hpos : 0 < (official q1.2.row).coeff 0 := by omega
    obtain ⟨w, hw, hwrow, _⟩ := refRow_node hb hq1
    refine ⟨w, hw, ?_, fun m hm1 => ?_⟩
    · rw [hwrow, referenceRow_coeff hpos, if_pos rfl]
      omega
    · rw [hwrow, referenceRow_coeff hpos, if_neg (by omega)]
      exact hm m hm1

/-- **A leg into `c_r` from a finite step.** A node whose finite coefficient is `m + 1` and whose
leg is `cr` has, in `cr`, the row with finite coefficient `m` and the same higher coefficients. -/
theorem leg_pred_row {s : List Nat} {M : Mountain} (hb : build s = .ok M) {x cr : Nat}
    {u : Ref × Cell} (hu : u ∈ realNodes M x) (hl : leftColumn u.2 = .ok cr) {m : Nat}
    (hm : (official u.2.row).coeff 0 = m + 1) :
    ∃ p ∈ realNodes M cr, (official p.2.row).coeff 0 = m ∧
      ∀ k, 1 ≤ k → (official p.2.row).coeff k = (official u.2.row).coeff k := by
  have hne : official u.2.row ≠ 0 := by
    intro h0
    rw [h0] at hm
    simp at hm
  obtain ⟨σ, l, ps, _, _, _, hl', _, hps, _, hrow⟩ := source_edge hb hu hne
  rw [hl] at hl'
  obtain rfl := Except.ok.inj hl'
  have hE : Row.jump σ ps = 0 := by
    by_contra hE
    rw [hrow, bump_coeff_low (by omega)] at hm
    omega
  have hσ : σ = ps := Row.jump_eq_zero.mp hE
  obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hps.1
  refine ⟨p, hp, ?_, fun k hk => ?_⟩
  · rw [hprow, ← hσ]
    rw [hrow, hE, bump_coeff_at] at hm
    omega
  · rw [hprow, ← hσ, hrow, hE, bump_coeff_high (by omega)]

/-! ## The last column ascends -/

/-- **The last column ascends at every node of the root column below `τ`.** -/
theorem x0_ascends {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hT : Top s M t root)
    {ctx : Context} (hsrc : ctx.source = M) (hx : ctx.x = M.size - 1)
    (hrc : ctx.rootColumn = root.column) {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M root.column)
    (hlt : official ρ.2.row < official t.row) : ascends ctx (some ρ) = .ok true := by
  have hb := hT.build
  obtain ⟨q, hq, hqt⟩ := top_mem hT
  have hne : official q.2.row ≠ 0 := by rw [hqt]; exact hT.real
  have hlq : leftColumn q.2 = .ok root.column := by rw [hqt]; exact leftColumn_of hT.left
  obtain ⟨σ, l, ps, _, _, _, hl', _, hps, _, _⟩ := source_edge hb hq hne
  rw [hlq] at hl'
  obtain rfl := Except.ok.inj hl'
  have hq' : q ∈ realNodes M ctx.x := by rw [hx]; exact hq
  refine ascends_of_root_leg hb hsrc hq' hne (by rw [hrc]; exact hlq) (by rw [hrc]; exact hps)
    (by rw [hrc]; exact hρ) ?_
  apply hps.2.2 _ (List.mem_map.mpr ⟨ρ, hρ, rfl⟩)
  rw [hqt]
  exact hlt

end OmegaY.Official.Recon.LowerBndSrc

#print axioms OmegaY.Official.Recon.LowerBndSrc.root_row_of_leg
#print axioms OmegaY.Official.Recon.LowerBndSrc.pred_rows
#print axioms OmegaY.Official.Recon.LowerBndSrc.leg_pred_row
#print axioms OmegaY.Official.Recon.LowerBndSrc.x0_ascends
