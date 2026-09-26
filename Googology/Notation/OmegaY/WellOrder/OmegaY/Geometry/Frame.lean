/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/Frame.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Geometry/Frame.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Build
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Fin.Basic

set_option backward.do.legacy false

/-!
# Finite sparse mountain frames

This is an indexed view of the actual finite columns. Cells and stored
references are exactly the executable builder's `Canonical.Cell` and
`Canonical.Ref`; index zero is retained for each phantom. The candidate and
numerical parent are defined by finite searches, not supplied as fields.
-/

namespace OmegaY.Geometry

structure Frame where
  width : Nat
  length : Fin width → Nat
  cells : (c : Fin width) → Fin (length c) → Canonical.Cell

namespace Frame

def ofMountain (mountain : Canonical.Mountain) : Frame where
  width := mountain.size
  length c := mountain[c.val].size
  cells c i := mountain[c.val][i.val]

abbrev Node (F : Frame) := (c : Fin F.width) × Fin (F.length c)

instance (F : Frame) : Fintype F.Node := inferInstanceAs (Fintype (Sigma _))
instance (F : Frame) : DecidableEq F.Node := inferInstanceAs (DecidableEq (Sigma _))

def ref {F : Frame} (u : F.Node) : Canonical.Ref := ⟨u.1.val, u.2.val⟩
def column {F : Frame} (u : F.Node) : Nat := u.1.val
def index {F : Frame} (u : F.Node) : Nat := u.2.val
def cell (F : Frame) (u : F.Node) : Canonical.Cell := F.cells u.1 u.2
def height (F : Frame) (u : F.Node) : Row := (F.cell u).row
def value (F : Frame) (u : F.Node) : Nat := (F.cell u).value
def Real {F : Frame} (u : F.Node) : Prop := 0 < u.2.val

def lookup (F : Frame) (r : Canonical.Ref) : Option F.Node :=
  if hc : r.column < F.width then
    if hi : r.index < F.length ⟨r.column, hc⟩ then
      some ⟨⟨r.column, hc⟩, ⟨r.index, hi⟩⟩
    else none
  else none

@[simp] theorem lookup_ref (F : Frame) (u : F.Node) : F.lookup (ref u) = some u := by
  cases u with
  | mk c i => simp [lookup, ref, c.isLt, i.isLt]

theorem lookup_spec {F : Frame} {r : Canonical.Ref} {u : F.Node}
    (h : F.lookup r = some u) : (ref u) = r := by
  unfold lookup at h
  split at h
  · split at h
    · obtain rfl := Option.some.inj h
      rfl
    · cases h
  · cases h

def upper (F : Frame) (u : F.Node) : Option F.Node :=
  if h : u.2.val + 1 < F.length u.1 then
    some ⟨u.1, ⟨u.2.val + 1, h⟩⟩ else none

theorem upper_spec {F : Frame} {u v : F.Node} (h : F.upper u = some v) :
    v.1 = u.1 ∧ v.2.val = u.2.val + 1 := by
  unfold upper at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · cases h

def aboveHeight (F : Frame) (u : F.Node) : Row :=
  ((F.upper u).map F.height).getD 0

@[simp] theorem aboveHeight_of_upper {F : Frame} {u v : F.Node}
    (h : F.upper u = some v) : F.aboveHeight u = F.height v := by
  simp [aboveHeight, h]

/-- The actual finite interval of allowed climbs from a stored endpoint. -/
def eligible (F : Frame) (u left : F.Node) : Finset (Fin (F.length left.1)) :=
  Finset.univ.filter fun i => left.2.val ≤ i.val ∧ F.height ⟨left.1, i⟩ ≤ F.height u

@[simp] theorem mem_eligible {F : Frame} {u left : F.Node}
    {i : Fin (F.length left.1)} : i ∈ F.eligible u left ↔
    left.2.val ≤ i.val ∧ F.height ⟨left.1, i⟩ ≤ F.height u := by
  simp [eligible]

/-- Follow the stored reference, then take the highest allowed column index. -/
def Q (F : Frame) (u : F.Node) : Option F.Node := do
  let stored ← (F.cell u).left
  let left ← F.lookup stored
  if h : (F.eligible u left).Nonempty then
    some ⟨left.1, (F.eligible u left).max' h⟩
  else none

/-- Inclusive threshold search. The threshold remains fixed after each Q step. -/
def seek (F : Frame) (threshold : Nat) : Nat → F.Node → Option F.Node
  | 0, _ => none
  | fuel + 1, u =>
      if 0 < F.value u ∧ F.value u < threshold then some u
      else (F.Q u).bind (F.seek threshold fuel)

/-- The numerical father is the first positive smaller value on the Q chain. -/
def P (F : Frame) (u : F.Node) : Option F.Node :=
  (F.Q u).bind (F.seek (F.value u) u.1.val)

/-- Local geometric facts about the finite columns and their stored legs.
No father-upper bound, row-shadow condition, or record-path assumption occurs.
-/
structure Ordered (F : Frame) : Prop where
  length_ge_two : ∀ c, 2 ≤ F.length c
  phantom : ∀ c (h : 0 < F.length c), F.cells c ⟨0, h⟩ = Canonical.phantom
  bottom_row : ∀ c (h : 1 < F.length c), (F.cells c ⟨1, h⟩).row = 1
  rows_strict : ∀ c, StrictMono (fun i => (F.cells c i).row)
  real_positive : ∀ u, Real u → 0 < F.value u
  stored_valid : ∀ u r, (F.cell u).left = some r →
    ∃ left, F.lookup r = some left ∧ left.1.val < u.1.val ∧
      F.height left ≤ F.height u

theorem value_zero_of_not_real {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hu : ¬ Real u) : F.value u = 0 := by
  have hi : u.2.val = 0 := by unfold Real at hu; omega
  have hi' : u.2 = ⟨0, by have := u.2.isLt; simpa [← hi] using this⟩ := Fin.ext hi
  change (F.cells u.1 u.2).value = 0
  rw [hi', hF.phantom]
  rfl

theorem real_of_value_pos {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hu : 0 < F.value u) : Real u := by
  by_contra hn
  rw [value_zero_of_not_real hF hn] at hu
  exact Nat.lt_irrefl _ hu

theorem one_le_height {F : Frame} (hF : F.Ordered) {u : F.Node} (hu : Real u) :
    (1 : Row) ≤ F.height u := by
  have hb : 1 < F.length u.1 := by have := hF.length_ge_two u.1; omega
  have hi : (⟨1, hb⟩ : Fin (F.length u.1)) ≤ u.2 := by exact Nat.succ_le_of_lt hu
  have h := (hF.rows_strict u.1).monotone hi
  simpa [height, cell, hF.bottom_row u.1 hb] using h

theorem Q_spec {F : Frame} (hF : F.Ordered) {u q : F.Node}
    (hq : F.Q u = some q) :
    ∃ left, (F.cell u).left = some (ref left) ∧
      left.1.val < u.1.val ∧ F.height left ≤ F.height u ∧
      q.1 = left.1 ∧ left.2.val ≤ q.2.val ∧ F.height q ≤ F.height u ∧
      (∀ v, F.upper q = some v → F.height u < F.height v) := by
  cases hs : (F.cell u).left with
  | none => simp [Q, hs] at hq
  | some stored =>
    obtain ⟨left, hl, hcol, hrow⟩ := hF.stored_valid u stored hs
    have hne : (F.eligible u left).Nonempty :=
      ⟨left.2, mem_eligible.mpr ⟨le_rfl, hrow⟩⟩
    have heq : (⟨left.1, (F.eligible u left).max' hne⟩ : F.Node) = q := by
      simpa [Q, hs, hl, hne] using hq
    obtain rfl := heq
    have hm := mem_eligible.mp (Finset.max'_mem (F.eligible u left) hne)
    refine ⟨left, congrArg some (lookup_spec hl).symm, hcol, hrow,
      rfl, hm.1, hm.2, ?_⟩
    intro v hv
    obtain ⟨hc, hi⟩ := upper_spec hv
    by_contra hn
    have hvr : F.height v ≤ F.height u := le_of_not_gt hn
    cases v with
    | mk c i =>
      dsimp at hc
      subst c
      have hvi : i ∈ F.eligible u left := mem_eligible.mpr ⟨by dsimp [index] at *; omega, hvr⟩
      have hmax := Finset.le_max' (F.eligible u left) i hvi
      change i.val ≤ ((F.eligible u left).max' hne).val at hmax
      dsimp [index] at hi
      omega

theorem Q_column_lt {F : Frame} (hF : F.Ordered) {u q : F.Node}
    (hq : F.Q u = some q) : q.1.val < u.1.val := by
  obtain ⟨left, _, hl, _, hc, _⟩ := Q_spec hF hq
  simpa only [column, hc] using hl

theorem Q_height_le {F : Frame} (hF : F.Ordered) {u q : F.Node}
    (hq : F.Q u = some q) : F.height q ≤ F.height u :=
  (Q_spec hF hq).choose_spec.2.2.2.2.2.1

theorem Q_upper_gt {F : Frame} (hF : F.Ordered) {u q v : F.Node}
    (hq : F.Q u = some q) (hv : F.upper q = some v) : F.height u < F.height v :=
  (Q_spec hF hq).choose_spec.2.2.2.2.2.2 v hv

theorem Q_real {F : Frame} (hF : F.Ordered) {u q : F.Node}
    (hu : Real u) (hq : F.Q u = some q) : Real q := by
  by_contra hn
  have hzero : q.2.val = 0 := by unfold Real at hn; omega
  have hlength : 1 < F.length q.1 := by have := hF.length_ge_two q.1; omega
  let v : F.Node := ⟨q.1, ⟨1, hlength⟩⟩
  have hv : F.upper q = some v := by simp [upper, hzero, v, hlength]
  have hgt := Q_upper_gt hF hq hv
  have hvrow : F.height v = 1 := hF.bottom_row q.1 hlength
  rw [hvrow] at hgt
  exact not_lt_of_ge (one_le_height hF hu) hgt

theorem Q_exists_of_left {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hleft : ∃ r, (F.cell u).left = some r) : ∃ q, F.Q u = some q := by
  obtain ⟨r, hr⟩ := hleft
  obtain ⟨left, hl, _, hrow⟩ := hF.stored_valid u r hr
  have hne : (F.eligible u left).Nonempty :=
    ⟨left.2, mem_eligible.mpr ⟨le_rfl, hrow⟩⟩
  exact ⟨⟨left.1, (F.eligible u left).max' hne⟩, by simp [Q, hr, hl, hne]⟩

theorem Q_eq_of_maximal {F : Frame} {u left : F.Node}
    (hleft : (F.cell u).left = some (ref left))
    (i : Fin (F.length left.1)) (hi : i ∈ F.eligible u left)
    (hmax : ∀ j ∈ F.eligible u left, j ≤ i) :
    F.Q u = some ⟨left.1, i⟩ := by
  have hne : (F.eligible u left).Nonempty := ⟨i, hi⟩
  have he : (F.eligible u left).max' hne = i :=
    le_antisymm (Finset.max'_le _ hne i hmax) (Finset.le_max' _ _ hi)
  simp [Q, hleft, lookup_ref, hne, he]

/-- If the next actual left-column row exceeds the ceiling, no climb occurs. -/
theorem Q_eq_left_of_barrier {F : Frame} (hF : F.Ordered) {u left : F.Node}
    (hleft : (F.cell u).left = some (ref left))
    (hrow : F.height left ≤ F.height u)
    (hbarrier : ∀ v, F.upper left = some v → F.height u < F.height v) :
    F.Q u = some left := by
  apply Q_eq_of_maximal hleft left.2 (mem_eligible.mpr ⟨le_rfl, hrow⟩)
  intro i hi
  by_contra hn
  have hil : left.2.val + 1 ≤ i.val := Nat.succ_le_of_lt (lt_of_not_ge hn)
  have hlen : left.2.val + 1 < F.length left.1 := lt_of_le_of_lt hil i.isLt
  let v : F.Node := ⟨left.1, ⟨left.2.val + 1, hlen⟩⟩
  have hv : F.upper left = some v := by simp [upper, hlen, v]
  have hvi : F.height v ≤ F.height ⟨left.1, i⟩ :=
    (hF.rows_strict left.1).monotone hil
  have hhi := (mem_eligible.mp hi).2
  exact not_lt_of_ge (hvi.trans hhi) (hbarrier v hv)

/-- If exactly the first upper row meets the ceiling, that upper node is Q. -/
theorem Q_eq_upper_at_equal {F : Frame} (hF : F.Ordered) {u left v : F.Node}
    (hleft : (F.cell u).left = some (ref left)) (hv : F.upper left = some v)
    (hrow : F.height v = F.height u) : F.Q u = some v := by
  obtain ⟨hc, hi⟩ := upper_spec hv
  cases v with
  | mk c i =>
    dsimp at hc
    subst c
    change i.val = left.2.val + 1 at hi
    apply Q_eq_of_maximal hleft i (mem_eligible.mpr ⟨by omega, hrow.le⟩)
    intro j hj
    by_contra hn
    have hij : i < j := lt_of_not_ge hn
    have hlt := hF.rows_strict left.1 hij
    have hhi := (mem_eligible.mp hj).2
    exact not_lt_of_ge (hhi.trans hrow.ge) hlt

/-- An inclusive operational trace, containing every rejected Q candidate. -/
inductive Hit (F : Frame) (threshold : Nat) : F.Node → F.Node → Prop
  | here {u : F.Node} (hpos : 0 < F.value u) (hsmall : F.value u < threshold) :
      Hit F threshold u u
  | next {u q p : F.Node} (hreject : ¬ (0 < F.value u ∧ F.value u < threshold))
      (hQ : F.Q u = some q) (rest : Hit F threshold q p) : Hit F threshold u p

theorem seek_sound {F : Frame} {threshold fuel : Nat} {u p : F.Node}
    (h : F.seek threshold fuel u = some p) : Hit F threshold u p := by
  induction fuel generalizing u with
  | zero => simp [seek] at h
  | succ fuel ih =>
    by_cases hs : 0 < F.value u ∧ F.value u < threshold
    · have he : u = p := by simpa [seek, hs] using h
      subst p
      exact .here hs.1 hs.2
    · cases hQ : F.Q u with
      | none => simp [seek, hs, hQ] at h
      | some q =>
        exact .next hs hQ (ih (by simpa [seek, hs, hQ] using h))

theorem Hit.run {F : Frame} (hF : F.Ordered) {threshold : Nat} {u p : F.Node}
    (h : Hit F threshold u p) :
    ∀ fuel, u.1.val < fuel → F.seek threshold fuel u = some p := by
  induction h with
  | here hpos hsmall =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel => simp [seek, hpos, hsmall]
  | next hreject hQ rest ih =>
    intro fuel hf
    have hcol := Q_column_lt hF hQ
    cases fuel with
    | zero => omega
    | succ fuel => simpa [seek, hreject, hQ] using ih fuel (by omega)

theorem Hit.result {F : Frame} {threshold : Nat} {u p : F.Node}
    (h : Hit F threshold u p) : 0 < F.value p ∧ F.value p < threshold := by
  induction h with
  | here hpos hsmall => exact ⟨hpos, hsmall⟩
  | next _ _ _ ih => exact ih

theorem Hit.column_le {F : Frame} (hF : F.Ordered) {threshold : Nat} {u p : F.Node}
    (h : Hit F threshold u p) : p.1.val ≤ u.1.val := by
  induction h with
  | here _ _ => exact le_rfl
  | next _ hQ _ ih => exact ih.trans (Q_column_lt hF hQ).le

theorem Hit.height_le {F : Frame} (hF : F.Ordered) {threshold : Nat} {u p : F.Node}
    (h : Hit F threshold u p) : F.height p ≤ F.height u := by
  induction h with
  | here _ _ => exact le_rfl
  | next _ hQ _ ih => exact ih.trans (Q_height_le hF hQ)

theorem P_iff {F : Frame} (hF : F.Ordered) {u p : F.Node} :
    F.P u = some p ↔ ∃ q, F.Q u = some q ∧ Hit F (F.value u) q p := by
  constructor
  · intro hp
    cases hQ : F.Q u with
    | none => simp [P, hQ] at hp
    | some q =>
      exact ⟨q, rfl, seek_sound (by simpa [P, hQ] using hp)⟩
  · rintro ⟨q, hQ, hit⟩
    have hr := hit.run hF u.1.val (Q_column_lt hF hQ)
    simpa [P, hQ] using hr

theorem P_value {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (hp : F.P u = some p) : 0 < F.value p ∧ F.value p < F.value u := by
  obtain ⟨q, _, hit⟩ := (P_iff hF).mp hp
  exact hit.result

theorem P_column_lt {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (hp : F.P u = some p) : p.1.val < u.1.val := by
  obtain ⟨q, hQ, hit⟩ := (P_iff hF).mp hp
  exact lt_of_le_of_lt (hit.column_le hF) (Q_column_lt hF hQ)

theorem P_height_le {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (hp : F.P u = some p) : F.height p ≤ F.height u := by
  obtain ⟨q, hQ, hit⟩ := (P_iff hF).mp hp
  exact (hit.height_le hF).trans (Q_height_le hF hQ)

/-- Raising a positive-search threshold cannot jump over its old first hit.
The old threshold trace continues from the new first hit. -/
theorem Hit.loosen {F : Frame} {small large : Nat} {u p : F.Node}
    (h : Hit F small u p) (hle : small ≤ large) :
    ∃ q, Hit F large u q ∧ Hit F small q p := by
  induction h with
  | here hpos hsmall =>
    exact ⟨_, .here hpos (lt_of_lt_of_le hsmall hle), .here hpos hsmall⟩
  | @next u q p hreject hQ rest ih =>
    by_cases hs : 0 < F.value u ∧ F.value u < large
    · exact ⟨u, .here hs.1 hs.2, .next hreject hQ rest⟩
    · obtain ⟨r, hr, hp⟩ := ih
      exact ⟨r, .next hs hQ hr, hp⟩

/-- Search totality from leftward real candidates and the actual first-column
value. It does not assume the existence of an upper node or any difference
recurrence, and therefore does not use `Normal`. -/
theorem threshold_hit_exists {F : Frame} (hF : F.Ordered)
    (hleft : ∀ u, Real u → 0 < u.1.val → ∃ r, (F.cell u).left = some r)
    (hfirst : ∀ u, Real u → u.1.val = 0 → F.value u = 1)
    {threshold : Nat} (ht : 1 < threshold) {u : F.Node} (hu : Real u) :
    ∃ p, Hit F threshold u p := by
  generalize hc : u.1.val = c
  induction c using Nat.strongRecOn generalizing u with
  | ind c ih =>
    by_cases hs : F.value u < threshold
    · exact ⟨u, .here (hF.real_positive u hu) hs⟩
    · have hnonzero : u.1.val ≠ 0 := by
        intro hzero
        have hv := hfirst u hu hzero
        exact hs (hv ▸ ht)
      obtain ⟨q, hq⟩ := Q_exists_of_left hF
        (hleft u hu (Nat.pos_of_ne_zero hnonzero))
      have hqreal := Q_real hF hu hq
      have hqcol : q.1.val < c := by simpa [hc] using Q_column_lt hF hq
      obtain ⟨p, hp⟩ := ih q.1.val hqcol hqreal rfl
      exact ⟨p, .next (fun h => hs h.2) hq hp⟩

theorem parent_exists_of_left_sources {F : Frame} (hF : F.Ordered)
    (hleft : ∀ u, Real u → 0 < u.1.val → ∃ r, (F.cell u).left = some r)
    (hfirst : ∀ u, Real u → u.1.val = 0 → F.value u = 1)
    {u : F.Node} (hu : 1 < F.value u) : ∃ p, F.P u = some p := by
  have hreal := real_of_value_pos hF (Nat.zero_lt_of_lt hu)
  have hnonzero : u.1.val ≠ 0 := by
    intro hzero
    have hv := hfirst u hreal hzero
    omega
  obtain ⟨q, hq⟩ := Q_exists_of_left hF
    (hleft u hreal (Nat.pos_of_ne_zero hnonzero))
  obtain ⟨p, hp⟩ := threshold_hit_exists hF hleft hfirst hu (Q_real hF hreal hq)
  exact ⟨p, (P_iff hF).mpr ⟨q, hq, hp⟩⟩

#print axioms Q_spec
#print axioms Q_real
#print axioms P_iff
#print axioms parent_exists_of_left_sources

end Frame
end OmegaY.Geometry
