import Googology.Trans.PoR.InaccPsi.R2.SlShift

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vu

open Ordinal Set Finset Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Sl

noncomputable def vuSingleMap (q q' : Ordinal.{0}) (x : Ordinal.{0}) : Ordinal.{0} :=
  ω ^ 2 * (if x / (ω ^ 2) = q then q' else x / (ω ^ 2)) + x % (ω ^ 2)

theorem vuSingleMap_block_add {q q' n r : Ordinal.{0}} (hr : r < ω ^ 2) :
    vuSingleMap q q' (ω ^ 2 * n + r) = ω ^ 2 * (if n = q then q' else n) + r := by
  have hp : ω ^ 2 ≠ 0 := (pow_pos omega0_pos 2).ne'
  have hd : (ω ^ 2 * n + r) / (ω ^ 2) = n := by
    rw [Ordinal.mul_add_div n hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  have hm : (ω ^ 2 * n + r) % (ω ^ 2) = r := by
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  unfold vuSingleMap
  simp only [hd, hm]

theorem vuSingleMap_block {q q' n : Ordinal.{0}} :
    vuSingleMap q q' (ω ^ 2 * n) = ω ^ 2 * (if n = q then q' else n) := by
  rw [show ω ^ 2 * n = ω ^ 2 * n + 0 by simp,
    vuSingleMap_block_add (q := q) (q' := q') (n := n) (r := 0)
      (by exact pow_pos omega0_pos 2)]
  simp

theorem vuSingleMap_zero {q q' : Ordinal.{0}} (hq : 0 < q) :
    vuSingleMap q q' 0 = 0 := by
  have hd : (0 : Ordinal.{0}) / (ω ^ 2) = 0 := Ordinal.div_eq_zero_of_lt (pow_pos omega0_pos 2)
  have hm : (0 : Ordinal.{0}) % (ω ^ 2) = 0 := Ordinal.mod_eq_of_lt (pow_pos omega0_pos 2)
  unfold vuSingleMap
  rw [hd, hm, if_neg (ne_of_lt hq)]
  simp

theorem vuSingleMap_slOff {q q' z z' : Ordinal.{0}} (hq : 0 < q) (hq' : 0 < q')
    (hz : ω ^ 2 * q = z) (hz' : ω ^ 2 * q' = z') :
    SlOff (vuSingleMap q q') {z} (z' + 1) := by
  have hzpos : 0 < z := by rw [← hz]; exact mul_pos (pow_pos omega0_pos 2) hq
  have hz'pos : 0 < z' := by rw [← hz']; exact mul_pos (pow_pos omega0_pos 2) hq'
  have hfz : vuSingleMap q q' z = z' := by
    rw [← hz, vuSingleMap_block (q := q) (q' := q') (n := q)]
    simpa using hz'
  refine ⟨vuSingleMap_zero (q := q) (q' := q') hq, ?_, ?_, ?_, ?_⟩
  · intro n r hr
    rw [vuSingleMap_block_add (q := q) (q' := q') (n := n) hr,
      vuSingleMap_block (q := q) (q' := q') (n := n)]
  · intro n
    rw [vuSingleMap_block (q := q) (q' := q') (n := n)]
    exact dvd_mul_right _ _
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact (lt_irrefl _ hxy).elim
      · subst y
        rw [vuSingleMap_zero (q := q) (q' := q') hq, hfz]
        exact hz'pos
    · subst x
      rcases hy with rfl | hy
      · exact (not_lt_of_ge (le_of_lt hzpos) hxy).elim
      · subst y
        exact (lt_irrefl _ hxy).elim
  · intro d hd
    simp only [Finset.mem_singleton] at hd
    subst d
    rw [hfz]
    exact lt_add_one _


/-- Powers with exponent at least one absorb the finite prefix 2. -/
theorem vuPow_absorb {E : Ordinal.{0}} (hE : 1 ≤ E) :
    (2 : Ordinal.{0}) + ω ^ E = ω ^ E := by
  apply (add_eq_right_iff_mul_omega0_le).2
  have h2ω : (2 : Ordinal.{0}) * ω = ω := by
    exact mul_omega0 (by norm_num) (natCast_lt_omega0 2)
  rw [h2ω]
  simpa only [opow_one] using opow_le_opow_right omega0_pos hE

/-- The selected singleton block is represented exactly by the witness value. -/
theorem vuPow_block {E : Ordinal.{0}} (hE : 1 ≤ E) :
    ω ^ 2 * ω ^ (ω ^ E) = ω ^ (ω ^ E) := by
  have h2c : (2 : Ordinal.{0}) + ω ^ E = ω ^ E := vuPow_absorb hE
  rw [← opow_natCast, ← opow_add]
  exact congrArg (fun x : Ordinal.{0} => ω ^ x) h2c

/-- The exponent of the witness block is its inner epsilon-sized exponent. -/
theorem vuWitness_cdExp {E : Ordinal.{0}} :
    Cd.cdExp (ω ^ (ω ^ E)) = ω ^ E := by
  have h := Sf.sfCdExp_any 0 (ω ^ E)
  simpa using h

/-- The singleton map sends the witness to its renamed witness. -/
theorem vuWitness_move {E E' : Ordinal.{0}} (hE : 1 ≤ E) (hE' : 1 ≤ E') :
    vuSingleMap (ω ^ (ω ^ E)) (ω ^ (ω ^ E')) (ω ^ (ω ^ E)) = ω ^ (ω ^ E') := by
  calc
    vuSingleMap (ω ^ (ω ^ E)) (ω ^ (ω ^ E')) (ω ^ (ω ^ E)) =
        vuSingleMap (ω ^ (ω ^ E)) (ω ^ (ω ^ E')) (ω ^ 2 * ω ^ (ω ^ E)) := by
      rw [vuPow_block hE]
    _ = ω ^ 2 * ω ^ (ω ^ E') := by
      rw [vuSingleMap_block]
      simp
    _ = ω ^ (ω ^ E') := vuPow_block hE'

/-- The singleton witness `ω^(ω^E)` can be moved to `ω^(ω^E')` by an SlOff map. -/
theorem vuWitness_slOff {E E' : Ordinal.{0}} (hE : 1 ≤ E) (hE' : 1 ≤ E') :
    SlOff (vuSingleMap (ω ^ (ω ^ E)) (ω ^ (ω ^ E'))) {ω ^ (ω ^ E)}
      (ω ^ (ω ^ E') + 1) := by
  have hc : 0 < ω ^ (ω ^ E) := opow_pos (ω ^ E) omega0_pos
  have hc' : 0 < ω ^ (ω ^ E') := opow_pos (ω ^ E') omega0_pos
  have hz := vuPow_block hE
  have hz' := vuPow_block hE'
  exact vuSingleMap_slOff hc hc' hz hz'

/-- The `Vo` witness block at `a`, with its inner exponent renamed from
`υ_(a+1)+1` to `υ_(μ+1)+1`, has a singleton offset map satisfying `SlOff`. -/
theorem vuVoWitness_slOff {a μ : Ordinal.{0}} :
    SlOff
      (vuSingleMap (ω ^ (ω ^ (upsilon (a + 1) + 1)))
        (ω ^ (ω ^ (upsilon (μ + 1) + 1))))
      {ω ^ (ω ^ (upsilon (a + 1) + 1))}
      (ω ^ (ω ^ (upsilon (μ + 1) + 1)) + 1) := by
  apply vuWitness_slOff
  all_goals exact le_add_self

#print axioms vuSingleMap_slOff
#print axioms vuWitness_slOff
#print axioms vuPow_absorb
#print axioms vuPow_block
#print axioms vuWitness_cdExp
#print axioms vuWitness_move
#print axioms vuVoWitness_slOff

end Googology.Trans.PoR.InaccPsi.R2.Vu
