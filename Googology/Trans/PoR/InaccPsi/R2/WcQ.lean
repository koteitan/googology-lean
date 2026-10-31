import Googology.Trans.PoR.InaccPsi.R2.VyOff
import Googology.Trans.PoR.InaccPsi.R2.CpRel

/-!
# A block map `Q` on all inner offsets with the last exponents prescribed

`Os` a finite set of positive `ω²`-multiples, `t : Os → On` with `t z ≥ 2` (the prescribed last exponents),
`e(z) = cdExp z` (the last exponent), `m(z) = cdOff(e z)`.

`wcG Os t z = (sup of wcG Os t z' over z' ∈ Os, z' < z) + ω^{t z}`, `wcQ Os t` its block map, `f = Vy.vyMap (wcQ Os t)`:

* `wcG_lt` (strictly increasing on `Os`), `wcG_exp` (**`e(wcG z) = t z`**), `wcG_dvd` (`ω² ∣ wcG z`), `wcG_bound`
  (`wcG z < ω^b` when `t < b` on `Os`), `wcG_absorb` (**`wcG z = ω^{t z}` when `t z' < t z` for every `z' < z` in `Os`**);
* `wcQ_spec` (**`f` is an `Sl.SlOff` map on `Os` with bound `ω^b`, `f z = wcG z`, `e(f z) = t z`**);
* `wcOff_target` (`x ≤ m(max 2 (x+1))`);
* `wcQ_wit_lo` (**THE BLOCK MAP AT THE VO WITNESS**: for `g = ω^{ω^E} ∈ Os` (`E ≥ 1`) and `g' = ω^{ω^{u'+1}}`,
  if every other `z ∈ Os` has `P(m z) < ω^{u'+1}` (`P` any map), some `Q` has `Q 0 = 0`,
  `Q g = g'`, `f` an `Sl.SlOff` map on `Os` with bound `ω^{ω^{u'+1}+1}`, and `P(m z) ≤ m(f z)` at every other `z`);
* `wcQ_carry` (**with `P = π_{υ_μ,υ_λ}`: EQ at the witness (`Vy.vyEQ_wit`) and the carry of every low decomposition
  `υ_{λ+z+ω+1} + m(z)` (`Vy.vyEQ_lo`) for one map `Q` on all of `Os`**);
* `wcQ_wit_sat`, `wcPiLo_low` (non-vacuity: the hypothesis holds for `π = π_{υ_μ,υ_λ}` at codes `m z < υ_μ`).

New definitions: `wcG`, `wcQ` (offset maps).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The greedy offset values**: `wcG z = sup_{z' ∈ Os, z' < z} wcG z' + ω^{t z}`. -/
noncomputable def wcG (Os : Finset Ordinal.{0}) (t : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) :
    Ordinal.{0} :=
  (Os.filter (fun z' : Ordinal.{0} => z' < z)).attach.sup (fun z' => wcG Os t z'.1) + ω ^ t z
termination_by z
decreasing_by exact (Finset.mem_filter.1 z'.2).2

theorem wcG_eq (Os : Finset Ordinal.{0}) (t : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) :
    wcG Os t z = (Os.filter (fun z' : Ordinal.{0} => z' < z)).attach.sup (fun z' => wcG Os t z'.1) + ω ^ t z := by
  rw [wcG]

variable {Os : Finset Ordinal.{0}} {t : Ordinal.{0} → Ordinal.{0}}

theorem wcG_le_sup {z z' : Ordinal.{0}} (hz' : z' ∈ Os) (h : z' < z) :
    wcG Os t z' ≤ (Os.filter (fun z' : Ordinal.{0} => z' < z)).attach.sup (fun z'' => wcG Os t z''.1) := by
  have hmem : z' ∈ Os.filter (fun z'' : Ordinal.{0} => z'' < z) := Finset.mem_filter.2 ⟨hz', h⟩
  exact Finset.le_sup (f := fun z'' => wcG Os t z''.1) (Finset.mem_attach _ ⟨z', hmem⟩)

/-- **`wcG` is strictly increasing on `Os`.** -/
theorem wcG_lt {z z' : Ordinal.{0}} (hz' : z' ∈ Os) (h : z' < z) : wcG Os t z' < wcG Os t z := by
  rw [wcG_eq Os t z]
  exact (wcG_le_sup hz' h).trans_lt (lt_add_of_pos_right _ (opow_pos _ omega0_pos))

theorem wc_cdExp_opow (e : Ordinal.{0}) : cdExp (ω ^ e) = e := by
  refine cdExp_eq (opow_ne_zero e omega0_ne_zero) dvd_rfl fun h => ?_
  have := Ordinal.le_of_dvd (opow_ne_zero e omega0_ne_zero) h
  exact absurd ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one e)) (not_lt.2 this)

/-- **The last exponent of `wcG z` is `t z`.** -/
theorem wcG_exp (z : Ordinal.{0}) : cdExp (wcG Os t z) = t z := by
  rw [wcG_eq, Cp.cpExp_add _ (opow_ne_zero _ omega0_ne_zero), wc_cdExp_opow]

/-- `ω² ∣ wcG z` for `z ∈ Os` when `t ≥ 2` on `Os`. -/
theorem wcG_dvd (ht2 : ∀ z ∈ Os, 2 ≤ t z) : ∀ z ∈ Os, ω ^ 2 ∣ wcG Os t z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rw [wcG_eq]
  have h2 : (ω : Ordinal.{0}) ^ 2 ∣ ω ^ t z := by
    rw [← opow_natCast]; exact opow_dvd_opow ω (by exact_mod_cast ht2 z hz)
  refine dvd_add ?_ h2
  set s := (Os.filter (fun z' : Ordinal.{0} => z' < z)).attach
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sup_empty]; exact dvd_zero _
  · obtain ⟨z', -, e⟩ := Finset.exists_mem_eq_sup s hne (fun z'' => wcG Os t z''.1)
    rw [e]
    have hm := Finset.mem_filter.1 z'.2
    exact IH _ hm.2 hm.1

/-- `wcG z < ω^b` for `z ∈ Os` when `t z' < b` for every `z' ≤ z` in `Os`. -/
theorem wcG_bound {b : Ordinal.{0}} : ∀ z ∈ Os, (∀ z' ∈ Os, z' ≤ z → t z' < b) → wcG Os t z < ω ^ b := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hb
  rw [wcG_eq]
  have hP := isPrincipal_add_omega0_opow b
  refine hP ?_ ((opow_lt_opow_iff_right one_lt_omega0).2 (hb z hz le_rfl))
  refine (Finset.sup_lt_iff (opow_pos b omega0_pos)).2 fun z' _ => ?_
  have hm := Finset.mem_filter.1 z'.2
  exact IH _ hm.2 hm.1 fun z'' hz'' h => hb z'' hz'' (h.trans hm.2.le)

/-- **Absorption**: `wcG z = ω^{t z}` when `t z' < t z` for every `z' < z` in `Os`. -/
theorem wcG_absorb {z : Ordinal.{0}} (hlt : ∀ z' ∈ Os, z' < z → t z' < t z) : wcG Os t z = ω ^ t z := by
  rw [wcG_eq]
  refine Ordinal.add_omega0_opow ?_
  refine (Finset.sup_lt_iff (opow_pos _ omega0_pos)).2 fun z' _ => ?_
  have hm := Finset.mem_filter.1 z'.2
  exact wcG_bound _ hm.1 fun z'' hz'' h => hlt z'' hz'' (h.trans_lt hm.2)

theorem wc_p2 : (ω : Ordinal.{0}) ^ 2 ≠ 0 := (pow_pos omega0_pos 2).ne'

open Classical in
/-- **The block map of `wcG`**: `Q(q) = wcG(ω²·q)/ω²` on the blocks of `Os`, the identity elsewhere. -/
noncomputable def wcQ (Os : Finset Ordinal.{0}) (t : Ordinal.{0} → Ordinal.{0}) (q : Ordinal.{0}) :
    Ordinal.{0} :=
  if q ≠ 0 ∧ ω ^ 2 * q ∈ Os then wcG Os t (ω ^ 2 * q) / ω ^ 2 else q

theorem wcQ_zero : wcQ Os t 0 = 0 := by unfold wcQ; simp

section Spec

variable (hOs : ∀ z ∈ Os, 0 < z ∧ ω ^ 2 ∣ z) (ht2 : ∀ z ∈ Os, 2 ≤ t z)
include hOs ht2

/-- `ω²·Q(z/ω²) = wcG z` on `Os`. -/
theorem wcQ_blk {z : Ordinal.{0}} (hz : z ∈ Os) : ω ^ 2 * wcQ Os t (z / ω ^ 2) = wcG Os t z := by
  obtain ⟨hz0, q, rfl⟩ := hOs z hz
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hz0; exact lt_irrefl _ hz0
  rw [Ordinal.mul_div_cancel q wc_p2]
  unfold wcQ
  rw [if_pos ⟨hq0, hz⟩]
  exact Ordinal.div_mul_cancel wc_p2 (wcG_dvd ht2 _ hz)

/-- **`f z = wcG z` on `Os`.** -/
theorem wcQ_val {z : Ordinal.{0}} (hz : z ∈ Os) : Vy.vyMap (wcQ Os t) z = wcG Os t z := by
  obtain ⟨-, q, e⟩ := hOs z hz
  have hm : z % ω ^ 2 = 0 := by rw [e]; exact Ordinal.mul_mod _ _
  unfold Vy.vyMap
  rw [hm, add_zero]
  exact wcQ_blk hOs ht2 hz

/-- **`f` is an `Sl.SlOff` map on `Os` with bound `ω^b`, and `e(f z) = t z` on `Os`.** -/
theorem wcQ_spec {b : Ordinal.{0}} (hb : ∀ z ∈ Os, t z < b) :
    Sl.SlOff (Vy.vyMap (wcQ Os t)) Os (ω ^ b) ∧ ∀ z ∈ Os, cdExp (Vy.vyMap (wcQ Os t) z) = t z := by
  refine ⟨Vy.vyMap_slOff wcQ_zero (fun x hx y hy hxy => ?_) (fun d hd => ?_),
    fun z hz => by rw [wcQ_val hOs ht2 hz, wcG_exp]⟩
  · have hp : (0 : Ordinal.{0}) < ω ^ 2 := pow_pos omega0_pos 2
    rcases Finset.mem_insert.1 hy with rfl | hy'
    · rw [Ordinal.zero_div] at hxy; exact absurd hxy (not_lt.2 zero_le)
    have hGy := wcQ_blk hOs ht2 hy'
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · rw [Ordinal.zero_div, wcQ_zero]
      refine pos_iff_ne_zero.2 fun h0 => ?_
      rw [h0, mul_zero, wcG_eq] at hGy
      exact absurd hGy.symm (ne_of_gt (lt_of_lt_of_le (opow_pos _ omega0_pos) le_add_self))
    · have hGx := wcQ_blk hOs ht2 hx'
      have hxy' : x < y := by
        obtain ⟨-, qx, ex⟩ := hOs x hx'
        obtain ⟨-, qy, ey⟩ := hOs y hy'
        rw [ex, ey, Ordinal.mul_div_cancel _ wc_p2, Ordinal.mul_div_cancel _ wc_p2] at hxy
        rw [ex, ey]; exact (mul_lt_mul_iff_right₀ hp).2 hxy
      have := wcG_lt (t := t) hx' hxy'
      rw [← hGx, ← hGy] at this
      exact (mul_lt_mul_iff_right₀ hp).1 this
  · rw [wcQ_val hOs ht2 hd]
    exact wcG_bound _ hd fun z' hz' _ => hb z' hz'

end Spec

/-- **`x ≤ m(e)` whenever `x + 1 ≤ e`.** -/
theorem wcOff_ge {x e : Ordinal.{0}} (h : x + 1 ≤ e) : x ≤ cdOff e := by
  unfold cdOff
  split_ifs with he
  · refine Ordinal.le_sub_of_add_le (le_trans ?_ h)
    rcases lt_or_ge x ω with hx | hx
    · obtain ⟨n, rfl⟩ := lt_omega0.1 hx
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]
    · rw [Ordinal.one_add_of_omega0_le hx]; exact le_self_add
  · exact le_self_add.trans h

/-- **THE BLOCK MAP AT THE VO WITNESS**: given `g = ω^{ω^E} ∈ Os` (`E ≥ 1`) and a map `P` with `P(m z) < ω^{u'+1}` at
every other `z ∈ Os`, some `Q` has `Q 0 = 0`, `Q g = ω^{ω^{u'+1}}`, `vyMap Q` an `Sl.SlOff` map on `Os` with bound
`ω^{ω^{u'+1}+1}`, `vyMap Q g = ω^{ω^{u'+1}}`, and `P(m z) ≤ m(e(vyMap Q z))` at every other `z ∈ Os`. -/
theorem wcQ_wit_lo {Os : Finset Ordinal.{0}} {E u' : Ordinal.{0}} (P : Ordinal.{0} → Ordinal.{0})
    (hE : 1 ≤ E) (hOs : ∀ z ∈ Os, 0 < z ∧ ω ^ 2 ∣ z) (hg : ω ^ ω ^ E ∈ Os)
    (hP : ∀ z ∈ Os, z ≠ ω ^ ω ^ E → P (cdOff (cdExp z)) < ω ^ (u' + 1)) :
    ∃ Q : Ordinal.{0} → Ordinal.{0}, Q 0 = 0 ∧ Q (ω ^ ω ^ E) = ω ^ ω ^ (u' + 1) ∧
      Vy.vyMap Q (ω ^ ω ^ E) = ω ^ ω ^ (u' + 1) ∧
      Sl.SlOff (Vy.vyMap Q) Os (ω ^ (ω ^ (u' + 1) + 1)) ∧
      ∀ z ∈ Os, z ≠ ω ^ ω ^ E → P (cdOff (cdExp z)) ≤ cdOff (cdExp (Vy.vyMap Q z)) := by
  classical
  set g := ω ^ ω ^ E with hgdef
  set T := ω ^ (u' + 1) with hTdef
  let t : Ordinal.{0} → Ordinal.{0} := fun z => if z = g then T else max 2 (P (cdOff (cdExp z)) + 1)
  have hTl : IsSuccLimit T := isSuccLimit_opow_left isSuccLimit_omega0 (by
    intro h; exact absurd h (ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one u'))))
  have h2T : (2 : Ordinal.{0}) < T := by
    have h2 : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
    exact h2.trans_le (left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u')))
  have htlt : ∀ z ∈ Os, z ≠ g → t z < T := by
    intro z hz hzg
    simp only [t, if_neg hzg]
    exact max_lt h2T (hTl.add_one_lt (hP z hz hzg))
  have ht2 : ∀ z ∈ Os, 2 ≤ t z := by
    intro z _
    by_cases hzg : z = g
    · simp only [t, if_pos hzg]; exact h2T.le
    · simp only [t, if_neg hzg]; exact le_max_left _ _
  have hb : ∀ z ∈ Os, t z < T + 1 := by
    intro z hz
    by_cases hzg : z = g
    · simp only [t, if_pos hzg]; exact lt_add_one T
    · exact (htlt z hz hzg).trans (lt_add_one T)
  obtain ⟨hoff, hexp⟩ := wcQ_spec hOs ht2 hb
  have hGg : wcG Os t g = ω ^ T := by
    rw [wcG_absorb (fun z' hz' h => by
      have := htlt z' hz' (ne_of_lt h); simpa [t, if_pos] using this)]
    simp [t]
  have hfg : Vy.vyMap (wcQ Os t) g = ω ^ T := (wcQ_val hOs ht2 hg).trans hGg
  have hblk : ω ^ 2 * g = g := Vu.vuPow_block hE
  have hT1 : (1 : Ordinal.{0}) ≤ u' + 1 := le_add_self
  have hblk' : ω ^ 2 * ω ^ T = ω ^ T := Vu.vuPow_block hT1
  refine ⟨wcQ Os t, wcQ_zero, ?_, hfg, hoff, fun z hz hzg => ?_⟩
  · have hdiv : g / ω ^ 2 = g := by
      conv_lhs => rw [← hblk]
      exact Ordinal.mul_div_cancel _ wc_p2
    have h := wcQ_blk hOs ht2 hg
    rw [hdiv, hGg] at h
    rw [← hblk'] at h
    exact mul_right_injective₀ wc_p2 h
  · rw [hexp z hz]
    simp only [t, if_neg hzg]
    exact wcOff_ge (le_max_right _ _)

/-- **Non-vacuity**: for `π = π_{υ_μ,υ_λ}` the hypothesis holds at every code `m z < υ_μ` (`π` fixes it). -/
theorem wcPiLo_low {σ τ c u' : Ordinal.{0}} (h : Bases σ τ) (hc : c < σ) (hσ : σ ≤ u') :
    pi σ τ c < ω ^ (u' + 1) := by
  rw [pi_lt h hc]
  exact (hc.trans_le hσ).trans_le ((right_le_opow u' one_lt_omega0).trans
    (opow_le_opow_right omega0_pos le_self_add))

/-- **Non-vacuity**: at `Os = {g}` the block map exists with no hypothesis. -/
theorem wcQ_wit_sat {E u' : Ordinal.{0}} (P : Ordinal.{0} → Ordinal.{0}) (hE : 1 ≤ E) :
    ∃ Q : Ordinal.{0} → Ordinal.{0}, Q 0 = 0 ∧ Q (ω ^ ω ^ E) = ω ^ ω ^ (u' + 1) ∧
      Sl.SlOff (Vy.vyMap Q) {ω ^ ω ^ E} (ω ^ (ω ^ (u' + 1) + 1)) := by
  have hpos : (0 : Ordinal.{0}) < ω ^ ω ^ E := opow_pos _ omega0_pos
  obtain ⟨Q, h0, hQ, -, hoff, -⟩ := wcQ_wit_lo (Os := {ω ^ ω ^ E}) (u' := u') P hE
    (fun z hz => by
      rw [Finset.mem_singleton.1 hz]
      exact ⟨hpos, ⟨_, (Vu.vuPow_block hE).symm⟩⟩) (Finset.mem_singleton_self _)
    (fun z hz hzg => absurd (Finset.mem_singleton.1 hz) hzg)
  exact ⟨Q, h0, hQ, hoff⟩

/-- **The carry at the low decompositions and EQ at the witness** for the block map of `wcQ_wit_lo`
(`Vy.vyEQ_lo`, `Vy.vyEQ_wit`): every hypothesis of these two theorems except the map ones is passed through. -/
theorem wcQ_carry {l μ η1 : Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hOs : ∀ z ∈ Os, 0 < z ∧ ω ^ 2 ∣ z) (hg : ω ^ ω ^ (upsilon (l + 1) + 1) ∈ Os)
    (hP : ∀ z ∈ Os, z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
      pi (upsilon μ) (upsilon l) (cdOff (cdExp z)) < ω ^ (upsilon (μ + 1) + 1))
    (hB : Bases (upsilon μ) (upsilon l)) (hμ : IsRestartIdx μ) (hμ1 : upsilon (μ + 1) < Om1)
    (hn : upsilon (μ + 2) < Nm.Pv S η1)
    (hCw : upsilon (μ + ω ^ ω ^ (upsilon (μ + 1) + 1) + ω + 1) < nuC)
    (hside : ∀ Q : Ordinal.{0} → Ordinal.{0}, ∀ z ∈ Os, z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
      ω ≤ Vy.vyMap Q z ∧ Vy.vyMap Q z < upsilon (μ + 2) ∧ upsilon (μ + Vy.vyMap Q z + ω + 1) < nuC) :
    ∃ Q : Ordinal.{0} → Ordinal.{0},
      Sl.SlOff (Vy.vyMap Q) Os (ω ^ (ω ^ (upsilon (μ + 1) + 1) + 1)) ∧
      Vr.vrImg l μ (Vy.vyMap Q) (Vr.vrEw (ω ^ ω ^ (upsilon (l + 1) + 1))) =
        cdR S (μ + ω ^ ω ^ (upsilon (μ + 1) + 1)) ∧
      ∀ z ∈ Os, z ≠ ω ^ ω ^ (upsilon (l + 1) + 1) →
        Vr.vrImg l μ (Vy.vyMap Q) (.add (.ub (z + ω + 1) .base) (.lo (cdOff (cdExp z)))) ≤
          cdR S (μ + Vy.vyMap Q z) := by
  obtain ⟨Q, -, hQ, -, hoff, hlo⟩ := wcQ_wit_lo (pi (upsilon μ) (upsilon l)) le_add_self hOs hg hP
  refine ⟨Q, hoff, (Vy.vyEQ_wit (S := S) hB hoff hQ hμ hμ1 hn hCw).2, fun z hz hzg => ?_⟩
  obtain ⟨hω, hfu, hC⟩ := hside Q z hz hzg
  exact (Vy.vyEQ_lo (S := S) hoff (hOs z hz).2 hμ hn hω hfu hC).2 (hlo z hz hzg)

#print axioms wcG_lt
#print axioms wcG_exp
#print axioms wcG_absorb
#print axioms wcQ_spec
#print axioms wcOff_ge
#print axioms wcQ_wit_lo
#print axioms wcPiLo_low
#print axioms wcQ_wit_sat
#print axioms wcQ_carry

end Googology.Trans.PoR.InaccPsi.R2.Wc
