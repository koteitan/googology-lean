/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Keys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Keys.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Order.WithBot
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option

set_option backward.do.legacy false

/-!
Finite high-to-low root keys for weak omega-Y. A top coordinate is an actual
order-top marker, not an arbitrarily large natural number. The order is
lexicographic and the dimension is fixed throughout a trajectory.

This file proves the key arithmetic used by reflection and fill transport;
it does not assert that an omega-Y mountain supplies the required root bounds.
-/

namespace OmegaY.Keys

universe u

abbrev Key (m : Nat) (Label : Type u) := Lex (Fin m → WithTop Label)

variable {Label : Type u} [LinearOrder Label] {m n : Nat}

theorem key_wellFounded [WellFoundedLT Label] :
    WellFounded ((· < ·) : Key m Label → Key m Label → Prop) :=
  wellFounded_lt

/-- Finite templates name only internal vertices, or the fixed infinity marker. -/
abbrev Template (m n : Nat) := Fin m → Option (Fin n)

theorem template_finite (m n : Nat) : Finite (Template m n) := inferInstance

theorem template_countable (m n : Nat) : Countable (Template m n) := inferInstance

def eval (t : Template m n) (f : Fin n → Label) : Key m Label :=
  toLex fun i => match t i with
    | none => ⊤
    | some j => (f j : WithTop Label)

theorem eval_pointwise_le (t : Template m n) {f g : Fin n → Label}
    (h : ∀ i, g i ≤ f i) : ∀ i, eval t g i ≤ eval t f i := by
  intro i
  simp only [eval, Pi.toLex_apply]
  cases ht : t i with
  | none => simp [ht]
  | some j => simpa [ht] using WithTop.coe_le_coe.mpr (h j)

theorem eval_mono (t : Template m n) {f g : Fin n → Label}
    (h : ∀ i, g i ≤ f i) : eval t g ≤ eval t f :=
  Pi.toLex_monotone (eval_pointwise_le t h)

theorem eval_lt_control (t : Template m n) {f g : Fin n → Label}
    {control : Key m Label} (h : ∀ i, g i ≤ f i)
    (hOld : eval t f < control) : eval t g < control :=
  lt_of_le_of_lt (eval_mono t h) hOld

def relabel {n' : Nat} (t : Template m n) (mu : Fin n → Fin n') : Template m n' :=
  fun i => (t i).map mu

theorem eval_relabel {n' : Nat} (t : Template m n) (mu : Fin n → Fin n')
    (f : Fin n' → Label) : eval (relabel t mu) f = eval t (f ∘ mu) := by
  apply funext
  intro i
  simp only [eval, relabel, Pi.toLex_apply, Function.comp_apply]
  cases t i <;> rfl

theorem eval_relabel_of_labels {n' : Nat} (t : Template m n)
    (mu : Fin n → Fin n') (f : Fin n → Label) (g : Fin n' → Label)
    (h : ∀ i, g (mu i) = f i) : eval (relabel t mu) g = eval t f := by
  rw [eval_relabel]
  exact congrArg (eval t) (funext h)

/-- Pure combinatorial comparison: interpret the named vertices as their
ordered column indices, with infinity still strictly above all vertices. -/
def templateKey (t : Template m n) : Key m (Fin n) := eval t id

theorem eval_coordinate_map (t : Template m n) (f : Fin n → Label) (i : Fin m) :
    WithTop.map f (templateKey t i) = eval t f i := by
  simp only [templateKey, eval, Pi.toLex_apply]
  cases t i <;> rfl

theorem eval_lt_of_template_lt (t s : Template m n) (f : Fin n → Label)
    (hf : StrictMono f) (h : templateKey t < templateKey s) : eval t f < eval s f := by
  obtain ⟨i, hBefore, hAt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← eval_coordinate_map, ← eval_coordinate_map, hBefore j hj]
  · rw [← eval_coordinate_map, ← eval_coordinate_map]
    exact hf.withTop_map hAt

theorem eval_le_of_template_le (t s : Template m n) (f : Fin n → Label)
    (hf : StrictMono f) (h : templateKey t ≤ templateKey s) : eval t f ≤ eval s f := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact le_of_lt (eval_lt_of_template_lt t s f hf hlt)
  · apply le_of_eq
    apply funext
    intro i
    rw [← eval_coordinate_map, ← eval_coordinate_map, congrFun heq i]

/-- The roots are ordered from highest scale to lowest. `keep` finite
coordinates survive; all remaining coordinates are infinity. -/
def truncate (roots : Fin m → Label) (keep : Nat) : Key m Label :=
  toLex fun i => if i.val < keep then (roots i : WithTop Label) else ⊤

@[simp] theorem truncate_finite (roots : Fin m → Label) (keep : Nat)
    (i : Fin m) (hi : i.val < keep) :
    truncate roots keep i = (roots i : WithTop Label) := by
  simp [truncate, hi]

@[simp] theorem truncate_top (roots : Fin m → Label) (keep : Nat)
    (i : Fin m) (hi : keep ≤ i.val) : truncate roots keep i = ⊤ := by
  simp [truncate, Nat.not_lt.mpr hi]

theorem truncate_mono {small large : Fin m → Label} (keep : Nat)
    (h : ∀ i, i.val < keep → small i ≤ large i) :
    truncate small keep ≤ truncate large keep := by
  apply Pi.toLex_monotone
  intro i
  by_cases hi : i.val < keep
  · simpa only [truncate, Pi.toLex_apply, if_pos hi, WithTop.coe_le_coe] using h i hi
  · simp only [truncate, Pi.toLex_apply, if_neg hi, le_refl]

/-- A strict difference before either infinity suffix decides the key
comparison, regardless of how many infinity coordinates were newly inserted. -/
theorem truncate_lt_at {small large : Fin m → Label} {keepSmall keepLarge : Nat}
    (i : Fin m) (hiSmall : i.val < keepSmall) (hiLarge : i.val < keepLarge)
    (hBefore : ∀ j, j < i → small j = large j) (hAt : small i < large i) :
    truncate small keepSmall < truncate large keepLarge := by
  refine ⟨i, ?_, ?_⟩
  · intro j hji
    have hj : j.val < i.val := hji
    have hjs : j.val < keepSmall := Nat.lt_trans hj hiSmall
    have hjl : j.val < keepLarge := Nat.lt_trans hj hiLarge
    simp only [truncate, Pi.toLex_apply, if_pos hjs, if_pos hjl, hBefore j hji]
  · simp only [truncate, Pi.toLex_apply, if_pos hiSmall, if_pos hiLarge]
    exact WithTop.coe_lt_coe.mpr hAt

/-- This is the exact finite-prefix compensation needed for newly raised
fill jumps: the root decrease must occur inside the retained new prefix. -/
theorem fill_key_lt {newRoots sourceRoots : Fin m → Label}
    {newKeep sourceKeep : Nat}
    (h : ∃ i : Fin m, i.val < newKeep ∧ i.val < sourceKeep ∧
      (∀ j, j < i → newRoots j = sourceRoots j) ∧ newRoots i < sourceRoots i) :
    truncate newRoots newKeep < truncate sourceRoots sourceKeep := by
  obtain ⟨i, hn, hs, hp, hi⟩ := h
  exact truncate_lt_at i hn hs hp hi

/-- A shared root is permitted: `(a,a)` is below `(a,infinity)` even though
the first coordinates are identical. -/
theorem shared_root_before_infinity (a : Label) :
    (toLex (fun _ : Fin 2 => (a : WithTop Label)) : Key 2 Label) <
      toLex (fun i : Fin 2 => if i.val = 0 then (a : WithTop Label) else ⊤) := by
  refine ⟨1, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := Fin.ext (by omega)
    subst j
    simp
  · simp

end OmegaY.Keys

#print axioms OmegaY.Keys.key_wellFounded
#print axioms OmegaY.Keys.eval_mono
#print axioms OmegaY.Keys.fill_key_lt
#print axioms OmegaY.Keys.shared_root_before_infinity
