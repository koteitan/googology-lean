import Googology.Trans.PoR.InaccPsi.R2.VuSingle
import Googology.Trans.PoR.InaccPsi.R2.VrWit

/-!
# Finite offset maps from a map on `ω²`-blocks, and EQ at the witness with them

`f = vyMap Q`: `f(ω²·q + r) = ω²·Q(q) + r` (`r < ω²`).

* `vyMap_slOff` (**every `Q` with `Q 0 = 0`, strictly increasing on the blocks of `insert 0 Os`, gives an
  `Sl.SlOff` map on `Os`**); `vyMap_single` (`Vu.vuSingleMap` is the case `Q = update id q q'`);
* `vyWit_move` (the witness block `ω^{ω^{υ_{a+1}+1}}` goes to `ω^{ω^{υ_{μ+1}+1}}` when `Q` does so);
* `vyEQ_wit` (**EQ at the witness of `Vo.voWit` for every such `f`**: `img(Ew) = r(μ + f(g))`, via `Vr.vrEQ_wit`);
* `vyWit_sat` (non-vacuity: such a `Q` exists on `{g}`);
* `vyEQ_lo` (**EQ at an inner restart whose reach is `υ_{λ+z+ω+1} + c`, `c < υ_{λ+1}`**: the carry holds iff
  `π_{υ_μ,υ_λ}(c) ≤ -1 + e(f z)`; via `Vr.vrEQ_code`).

New definition: `vyMap` (an offset map).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The offset map of a block map `Q`**: `ω²·Q(x/ω²) + x mod ω²`. -/
noncomputable def vyMap (Q : Ordinal.{0} → Ordinal.{0}) (x : Ordinal.{0}) : Ordinal.{0} :=
  ω ^ 2 * Q (x / ω ^ 2) + x % ω ^ 2

theorem vy_p : (0 : Ordinal.{0}) < ω ^ 2 := pow_pos omega0_pos 2

theorem vyMap_block_add (Q : Ordinal.{0} → Ordinal.{0}) {q r : Ordinal.{0}} (hr : r < ω ^ 2) :
    vyMap Q (ω ^ 2 * q + r) = ω ^ 2 * Q q + r := by
  have hp : (ω ^ 2 : Ordinal.{0}) ≠ 0 := vy_p.ne'
  have hd : (ω ^ 2 * q + r) / ω ^ 2 = q := by
    rw [Ordinal.mul_add_div q hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  have hm : (ω ^ 2 * q + r) % ω ^ 2 = r := by
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  unfold vyMap; rw [hd, hm]

theorem vyMap_block (Q : Ordinal.{0} → Ordinal.{0}) (q : Ordinal.{0}) :
    vyMap Q (ω ^ 2 * q) = ω ^ 2 * Q q := by
  have := vyMap_block_add Q (q := q) vy_p
  rwa [add_zero, add_zero] at this

/-- **A block map gives an offset map.** -/
theorem vyMap_slOff {Q : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}} {B : Ordinal.{0}}
    (h0 : Q 0 = 0)
    (hQ : ∀ x ∈ insert 0 Os, ∀ y ∈ insert 0 Os, x / ω ^ 2 < y / ω ^ 2 → Q (x / ω ^ 2) < Q (y / ω ^ 2))
    (hbd : ∀ d ∈ Os, vyMap Q d < B) : Sl.SlOff (vyMap Q) Os B := by
  have hp := vy_p
  refine ⟨?_, fun q r hr => ?_, fun q => ?_, ?_, hbd⟩
  · have := vyMap_block Q 0; rwa [mul_zero, h0, mul_zero] at this
  · rw [vyMap_block_add Q hr, vyMap_block]
  · rw [vyMap_block]; exact dvd_mul_right _ _
  · intro x hx y hy hxy
    have hx' : x ∈ insert 0 Os := by simpa using hx
    have hy' : y ∈ insert 0 Os := by simpa using hy
    have ex := (Ordinal.div_add_mod x (ω ^ 2)).symm
    have ey := (Ordinal.div_add_mod y (ω ^ 2)).symm
    have hrx : x % ω ^ 2 < ω ^ 2 := Ordinal.mod_lt x hp.ne'
    have hry : y % ω ^ 2 < ω ^ 2 := Ordinal.mod_lt y hp.ne'
    have fx : vyMap Q x = ω ^ 2 * Q (x / ω ^ 2) + x % ω ^ 2 := rfl
    have fy : vyMap Q y = ω ^ 2 * Q (y / ω ^ 2) + y % ω ^ 2 := rfl
    rcases lt_trichotomy (x / ω ^ 2) (y / ω ^ 2) with hq | hq | hq
    · have hQq := hQ x hx' y hy' hq
      rw [fx, fy]
      calc ω ^ 2 * Q (x / ω ^ 2) + x % ω ^ 2 < ω ^ 2 * Q (x / ω ^ 2) + ω ^ 2 :=
            (add_lt_add_iff_left _).2 hrx
        _ = ω ^ 2 * (Q (x / ω ^ 2) + 1) := by rw [mul_add_one]
        _ ≤ ω ^ 2 * Q (y / ω ^ 2) := mul_le_mul_right (Order.add_one_le_of_lt hQq) _
        _ ≤ ω ^ 2 * Q (y / ω ^ 2) + y % ω ^ 2 := le_self_add
    · have hr : x % ω ^ 2 < y % ω ^ 2 := by
        by_contra hle
        push Not at hle
        have : y ≤ x := by
          rw [ex, ey, hq]; exact add_le_add_right hle _
        exact absurd hxy (not_lt.2 this)
      rw [fx, fy, hq]; exact (add_lt_add_iff_left _).2 hr
    · exfalso
      have : y < x := by
        calc y = ω ^ 2 * (y / ω ^ 2) + y % ω ^ 2 := ey
          _ < ω ^ 2 * (y / ω ^ 2) + ω ^ 2 := (add_lt_add_iff_left _).2 hry
          _ = ω ^ 2 * (y / ω ^ 2 + 1) := by rw [mul_add_one]
          _ ≤ ω ^ 2 * (x / ω ^ 2) := mul_le_mul_right (Order.add_one_le_of_lt hq) _
          _ ≤ x := by conv_rhs => rw [ex]
                      exact le_self_add
      exact absurd hxy (not_lt.2 this.le)

/-- `Vu.vuSingleMap` is the block map of `update id q q'`. -/
theorem vyMap_single (q q' : Ordinal.{0}) :
    Vu.vuSingleMap q q' = vyMap (fun p => if p = q then q' else p) := rfl

/-- The witness block moves as `Q` does: `f(ω^{ω^E}) = ω^{ω^{E'}}` when `Q(ω^{ω^E}) = ω^{ω^{E'}}`. -/
theorem vyWit_move {Q : Ordinal.{0} → Ordinal.{0}} {E E' : Ordinal.{0}} (hE : 1 ≤ E) (hE' : 1 ≤ E')
    (hQ : Q (ω ^ ω ^ E) = ω ^ ω ^ E') : vyMap Q (ω ^ ω ^ E) = ω ^ ω ^ E' := by
  conv_lhs => rw [← Vu.vuPow_block hE]
  rw [vyMap_block, hQ, Vu.vuPow_block hE']

/-- **EQ at the witness of `Vo.voWit` for every block map**: with `g = ω^{ω^{υ_{λ+1}+1}}`,
`g' = ω^{ω^{υ_{μ+1}+1}}`, `Q g = g'` and `vyMap Q` an offset map, at a restart `μ` below a name level with
`υ_{μ+g'+ω+1} < ν_C`, the image of the witness decomposition is the reach `r(μ + g')`. -/
theorem vyEQ_wit {l μ B η1 : Ordinal.{0}} {Q : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hB : Bases (upsilon μ) (upsilon l)) (hf : Sl.SlOff (vyMap Q) Os B)
    (hQ : Q (ω ^ ω ^ (upsilon (l + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1))
    (hμ : IsRestartIdx μ) (hμ1 : upsilon (μ + 1) < Om1) (hn : upsilon (μ + 2) < Nm.Pv S η1)
    (hC : upsilon (μ + ω ^ ω ^ (upsilon (μ + 1) + 1) + ω + 1) < nuC) :
    vyMap Q (ω ^ ω ^ (upsilon (l + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1) ∧
      Vr.vrImg l μ (vyMap Q) (Vr.vrEw (ω ^ ω ^ (upsilon (l + 1) + 1))) =
        cdR S (μ + ω ^ ω ^ (upsilon (μ + 1) + 1)) := by
  have h1 : ∀ u : Ordinal.{0}, (1 : Ordinal.{0}) ≤ u + 1 := fun u => le_add_self
  have hmv := vyWit_move (Q := Q) (h1 _) (h1 _) hQ
  refine ⟨hmv, ?_⟩
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
  have hm := upsilon_normal.strictMono
  have hu2E : InE (upsilon (μ + 2)) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  have hωu2 : ω ≤ upsilon (μ + 2) := Vo.vo_omega_le hu2E (InE.pos hu2E)
  have hu12 : upsilon (μ + 1) < upsilon (μ + 2) :=
    hm ((add_lt_add_iff_left μ).2 (by norm_num))
  have hlt : ω ^ ω ^ (upsilon (μ + 1) + 1) < upsilon (μ + 2) :=
    hu2E.opow_lt (hu2E.opow_lt (hu2E.add_lt hu12 (one_lt_omega0.trans_le hωu2)))
  have hgd : ω ^ 2 ∣ ω ^ ω ^ (upsilon (l + 1) + 1) := ⟨_, (Vu.vuPow_block (h1 _)).symm⟩
  have hfd : ω ^ 2 ∣ ω ^ ω ^ (upsilon (μ + 1) + 1) := ⟨_, (Vu.vuPow_block (h1 _)).symm⟩
  have hω : ω ≤ ω ^ ω ^ (upsilon (μ + 1) + 1) := by
    have h2 : ω ≤ ω ^ (upsilon (μ + 1) + 1) := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one _))
    exact h2.trans (right_le_opow _ one_lt_omega0)
  have := Vr.vrEQ_wit (S := S) hB hf hgd hμ hμ1 hn (hmv ▸ hfd) (hmv ▸ hω) (hmv ▸ hlt)
    (by rw [hmv]; exact Vu.vuWitness_cdExp) (by rw [hmv]; exact hC)
  rwa [hmv] at this

/-- **EQ at an inner restart with a low decomposition**: the carry for `ub (z+ω+1) base + lo c` holds iff
`π_{υ_μ,υ_λ}(c) ≤ -1 + e(f z)`. -/
theorem vyEQ_lo {l μ z B η1 c : Ordinal.{0}} {Q : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hf : Sl.SlOff (vyMap Q) Os B) (hzd : ω ^ 2 ∣ z) (hμ : IsRestartIdx μ)
    (hn : upsilon (μ + 2) < Nm.Pv S η1) (hω : ω ≤ vyMap Q z) (hfu : vyMap Q z < upsilon (μ + 2))
    (hC : upsilon (μ + vyMap Q z + ω + 1) < nuC) :
    Vr.vrImg l μ (vyMap Q) (.add (.ub (z + ω + 1) .base) (.lo c)) ≤ cdR S (μ + vyMap Q z) ↔
      pi (upsilon μ) (upsilon l) c ≤ cdOff (cdExp (vyMap Q z)) := by
  have hfd : ω ^ 2 ∣ vyMap Q z := by
    obtain ⟨q, rfl⟩ := hzd; rw [vyMap_block]; exact dvd_mul_right _ _
  exact Vr.vrEQ_code (S := S) (.lo c) hf hzd hμ hn hfd hω hfu hC

/-- **Non-vacuity of the map hypotheses of `vyEQ_wit`**: some `Q` sends the witness block `g` to `g'` and gives an
offset map on `{g}` (from `Vu.vuVoWitness_slOff`). -/
theorem vyWit_sat (l μ : Ordinal.{0}) : ∃ Q : Ordinal.{0} → Ordinal.{0},
    Q (ω ^ ω ^ (upsilon (l + 1) + 1)) = ω ^ ω ^ (upsilon (μ + 1) + 1) ∧
      Sl.SlOff (vyMap Q) {ω ^ ω ^ (upsilon (l + 1) + 1)} (ω ^ ω ^ (upsilon (μ + 1) + 1) + 1) := by
  refine ⟨fun p => if p = ω ^ ω ^ (upsilon (l + 1) + 1) then ω ^ ω ^ (upsilon (μ + 1) + 1) else p, by simp, ?_⟩
  rw [← vyMap_single]
  exact Vu.vuVoWitness_slOff

#print axioms vyMap_slOff
#print axioms vyMap_single
#print axioms vyWit_move
#print axioms vyEQ_wit
#print axioms vyEQ_lo
#print axioms vyWit_sat

end Googology.Trans.PoR.InaccPsi.R2.Vy
