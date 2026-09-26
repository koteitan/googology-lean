/-
The patterns-of-resemblance model of the omega-Y core, part 3 (this repository).
`Label`, `top`, `countable_iio_ordinal` and `countable_iio` are adapted from
Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Reflection/OrdinalSupply.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0); the rest is
new.  The closure `next`/`tower`/`lam` follows `Por/Closure.lean` of
koteitan/1y-wo-por (https://github.com/koteitan/1y-wo-por, Apache-2.0).
Taken from koteitan, wy-wo-por, `Por/Supply.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
The namespace `Por` is renamed to `OmegaY.Por`, since the 1-Y model of this repository uses `Por`.
-/
import Googology.Notation.OmegaY.WellOrder.Por.Relation
import Mathlib.SetTheory.Cardinal.Regular

set_option backward.do.legacy false

/-!
# Closed points below ω₁ and the initial representations

Labels are the ordinals `≤ ω₁`, with top `ω₁`. `Good α` says that the height-`α`
structure is a Σ₁-elementary substructure of the height-`ω₁` structure, with all
top bits defined. Formulas are countable, so closing a countable `γ` under
witnesses `ω` times gives a Good point (`good_cofinal`).

At a Good `α`, the top predicates of height `α` agree with those of `ω₁`
(`top_abs`, by induction on the key). Two Good points are related at every key
(`good_R`), so a chain of Good points represents every finite graph
(`initial_finite_graph`).
-/

/-! ## Supply below ω₁ -/

namespace OmegaY.Por.Supply

open OmegaY.Reflection Ordinal Cardinal

universe v w

/-- Phyrion's label type, verbatim. -/
abbrev Label : Type 1 := {o : Ordinal.{0} // o ≤ ω₁}

noncomputable def top : Label := ⟨ω₁, le_rfl⟩

variable {Key : Type v} [LinearOrder Key] [WellFoundedLT Key]
variable (S : KeySyntax.{1,v,w} Label Key)
variable [∀ n, Countable (S.Template n)]

/-- `α` is closed: every Σ₁ formula (all top bits defined, top predicates of
height `ω₁`) with parameters below `α` true below `ω₁` is true below `α`. -/
def Good (α : Label) : Prop :=
  ∀ (φ : Form S) (p : Fin φ.n → Label), (∀ i, φ.fixed i = true → p i < α) →
    Sat (relR S) (topR S top) (fun _ => True) top φ p →
    Sat (relR S) (topR S top) (fun _ => True) α φ p


set_option linter.unusedSectionVars false

/-! ### Labels -/

/-- The least label. -/
def zeroL : Label := ⟨0, (Ordinal.omega_pos 1).le⟩

theorem zeroL_lt_top : zeroL < top := Ordinal.omega_pos 1

theorem le_topL (x : Label) : x ≤ top := x.2

theorem countable_iio_ordinal {a : Ordinal.{0}} (ha : a < ω₁) :
    Countable (Set.Iio a) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  exact Cardinal.lt_aleph_one_iff.mp (lt_omega_iff_card_lt.mp ha)

theorem countable_iio {a : Label} (ha : a < top) : Countable (Set.Iio a) := by
  have := countable_iio_ordinal ha
  exact Function.Injective.countable
    (f := fun x : Set.Iio a => (⟨x.1.1, x.2⟩ : Set.Iio a.1)) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Set.Iio a.1 => z.1) h)

/-! ### Countability of formulas -/

/-- A code of a literal. -/
def litCode {n : Nat} : Lit S n →
    (Fin n × Fin n × Bool) ⊕ (S.Template n × Fin n × Fin n × Bool) ⊕
      (S.Template n × Fin n × Bool)
  | .lt i j pos => Sum.inl (i, j, pos)
  | .rel t i j pos => Sum.inr (Sum.inl (t, i, j, pos))
  | .top t i pos => Sum.inr (Sum.inr (t, i, pos))

theorem litCode_inj (n : Nat) : Function.Injective (litCode S (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [litCode]

instance lit_countable (n : Nat) : Countable (Lit S n) := (litCode_inj S n).countable

/-- A code of a formula. -/
def formCode (φ : Form S) : Σ n : Nat, (Fin n → Bool) × List (Lit S n) :=
  ⟨φ.n, φ.fixed, φ.lits⟩

theorem formCode_inj : Function.Injective (formCode S) := by
  rintro ⟨n, f, l⟩ ⟨n', f', l'⟩ h
  simp only [formCode, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

instance form_countable : Countable (Form S) := (formCode_inj S).countable

/-! ### Closure below ω₁ -/

open Classical in
/-- The height of a chosen witness in the full top structure (`0` if false). -/
noncomputable def wh (φ : Form S) (p : Fin φ.n → Label) : Ordinal.{0} :=
  if h : Sat (relR S) (topR S top) (fun _ => True) top φ p then
    ⨆ i : Fin φ.n, ((Classical.choose h i).1 + 1)
  else 0

theorem wh_lt (φ : Form S) (p : Fin φ.n → Label) : wh S φ p < ω₁ := by
  unfold wh
  split_ifs with h
  · exact Ordinal.iSup_lt_omega_one fun i =>
      (isSuccLimit_omega 1).add_one_lt ((Classical.choose_spec h).2.1 i)
  · exact Ordinal.omega_pos 1

theorem wit_lt_wh {φ : Form S} {p : Fin φ.n → Label}
    (h : Sat (relR S) (topR S top) (fun _ => True) top φ p) (i : Fin φ.n) :
    (Classical.choose h i).1 < wh S φ p := by
  unfold wh
  rw [dif_pos h]
  exact Ordinal.lt_iSup_add_one (fun i => (Classical.choose h i).1) i

/-- Formulas with parameters below `γ` (non-fixed entries set to `0`). -/
def Input (γ : Label) := Σ φ : Form S, Fin φ.n → Option (Set.Iio γ)

def toP {γ : Label} {n : Nat} (q : Fin n → Option (Set.Iio γ)) : Fin n → Label :=
  fun i => (q i).elim zeroL Subtype.val

theorem input_countable {γ : Label} (hγ : γ < top) : Countable (Input S γ) := by
  have := countable_iio hγ
  unfold Input
  infer_instance

noncomputable def nextO (γ : Label) : Ordinal.{0} :=
  max (γ.1 + 1) (⨆ q : Input S γ, wh S q.1 (toP q.2))

noncomputable def next (γ : Label) : Label := ⟨min (nextO S γ) ω₁, min_le_right _ _⟩

theorem wh_le_nextO (γ : Label) (q : Input S γ) : wh S q.1 (toP q.2) ≤ nextO S γ :=
  (le_ciSup (f := fun q : Input S γ => wh S q.1 (toP q.2))
    ⟨ω₁, by rintro _ ⟨q, rfl⟩; exact (wh_lt S _ _).le⟩ q).trans (le_max_right _ _)

theorem nextO_lt {γ : Label} (hγ : γ < top) : nextO S γ < ω₁ := by
  have := input_countable S hγ
  exact max_lt ((isSuccLimit_omega 1).add_one_lt hγ)
    (Ordinal.iSup_lt_omega_one fun q => wh_lt S _ _)

theorem next_val {γ : Label} (hγ : γ < top) : (next S γ).1 = nextO S γ :=
  min_eq_left (nextO_lt S hγ).le

theorem next_lt {γ : Label} (hγ : γ < top) : next S γ < top := by
  show (next S γ).1 < ω₁
  rw [next_val S hγ]
  exact nextO_lt S hγ

theorem lt_next {γ : Label} (hγ : γ < top) : γ < next S γ := by
  show γ.1 < (next S γ).1
  rw [next_val S hγ]
  exact (lt_add_one γ.1).trans_le (le_max_left _ _)

theorem wit_below {γ : Label} (hγ : γ < top) (φ : Form S) (p : Fin φ.n → Label)
    (hp : ∀ i, φ.fixed i = true → p i < γ)
    (h : Sat (relR S) (topR S top) (fun _ => True) top φ p) :
    Sat (relR S) (topR S top) (fun _ => True) (next S γ) φ p := by
  classical
  let q : Fin φ.n → Option (Set.Iio γ) := fun i =>
    if hi : φ.fixed i = true then some ⟨p i, hp i hi⟩ else none
  have hq : ∀ i, φ.fixed i = true → toP q i = p i := by
    intro i hi
    simp [q, toP, hi]
  unfold Sat at h
  obtain ⟨v, hv1, hv2, hv3⟩ := h
  have h' : Sat (relR S) (topR S top) (fun _ => True) top φ (toP q) := by
    unfold Sat
    exact ⟨v, fun i hi => (hv1 i hi).trans (hq i hi).symm, hv2, hv3⟩
  unfold Sat
  refine ⟨Classical.choose h', fun i hi => ((Classical.choose_spec h').1 i hi).trans (hq i hi),
    fun i => ?_, (Classical.choose_spec h').2.2⟩
  show (Classical.choose h' i).1 < (next S γ).1
  rw [next_val S hγ]
  exact (wit_lt_wh S h' i).trans_le (wh_le_nextO S γ ⟨φ, q⟩)

/-- `γ, next γ, next (next γ), …` -/
noncomputable def tower (γ : Label) : ℕ → Label
  | 0 => γ
  | t + 1 => next S (tower γ t)

theorem tower_lt {γ : Label} (hγ : γ < top) : ∀ t, tower S γ t < top
  | 0 => hγ
  | t + 1 => next_lt S (tower_lt hγ t)

theorem tower_succ_lt {γ : Label} (hγ : γ < top) (t : ℕ) : tower S γ t < tower S γ (t + 1) :=
  lt_next S (tower_lt S hγ t)

theorem tower_mono {γ : Label} (hγ : γ < top) : Monotone (tower S γ) :=
  monotone_nat_of_le_succ fun t => (tower_succ_lt S hγ t).le

noncomputable def lamO (γ : Label) : Ordinal.{0} := ⨆ t, (tower S γ t).1

theorem lamO_le (γ : Label) : lamO S γ ≤ ω₁ := ciSup_le fun t => (tower S γ t).2

noncomputable def lam (γ : Label) : Label := ⟨lamO S γ, lamO_le S γ⟩

theorem tower_le_lam (γ : Label) (t : ℕ) : tower S γ t ≤ lam S γ := by
  show (tower S γ t).1 ≤ lamO S γ
  exact le_ciSup (f := fun t => (tower S γ t).1)
    ⟨ω₁, by rintro _ ⟨t, rfl⟩; exact (tower S γ t).2⟩ t

theorem lam_lt {γ : Label} (hγ : γ < top) : lam S γ < top :=
  Ordinal.iSup_lt_omega_one fun t => tower_lt S hγ t

theorem lt_lam {γ : Label} (hγ : γ < top) : γ < lam S γ :=
  (tower_succ_lt S hγ 0).trans_le (tower_le_lam S γ 1)

theorem exists_tower {γ : Label} (hγ : γ < top) {n : Nat} (fx : Fin n → Bool)
    (p : Fin n → Label) (hp : ∀ i, fx i = true → p i < lam S γ) :
    ∃ t, ∀ i, fx i = true → p i < tower S γ t := by
  have : ∀ i, ∃ t, fx i = true → p i < tower S γ t := by
    intro i
    by_cases hi : fx i = true
    · have h : (p i).1 < ⨆ t, (tower S γ t).1 := hp i hi
      obtain ⟨t, ht⟩ := Ordinal.lt_iSup_iff.mp h
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose t ht using this
  exact ⟨Finset.univ.sup t, fun i hi =>
    (ht i hi).trans_le (tower_mono S hγ (Finset.le_sup (Finset.mem_univ i)))⟩

theorem lam_good {γ : Label} (hγ : γ < top) : Good S (lam S γ) := by
  intro φ p hp h
  obtain ⟨t, ht⟩ := exists_tower S hγ φ.fixed p hp
  have h2 := wit_below S (tower_lt S hγ t) φ p ht h
  unfold Sat at h2 ⊢
  obtain ⟨v, h1, hv, h3⟩ := h2
  exact ⟨v, h1, fun i => (hv i).trans_le (tower_le_lam S γ (t + 1)), h3⟩

theorem good_cofinal (seed : Label) (hseed : seed < top) :
    ∃ α : Label, seed < α ∧ α < top ∧ Good S α := by
  exact ⟨lam S seed, lt_lam S hseed, lam_lt S hseed, lam_good S hseed⟩

/-! ### Absoluteness at good points -/

theorem lit_true {n : Nat} {rl : Key → Label → Label → Prop} {tp : Key → Label → Prop}
    {allow : Key → Prop} {v : Fin n → Label} (l : Lit S n) (h : l.Holds rl tp allow v) :
    l.Holds rl tp (fun _ => True) v := by
  cases l with
  | lt i j pos => exact h
  | rel t i j pos => exact h
  | top t i pos => exact ⟨trivial, h.2⟩

theorem lit_lower {n : Nat} {rl : Key → Label → Label → Prop} {tp : Key → Label → Prop}
    {κ : Key} {v w : Fin n → Label} (hwv : ∀ i, w i ≤ v i) (l : Lit S n)
    (hv : l.Holds rl tp (· < κ) v) (hw : l.Holds rl tp (fun _ => True) w) :
    l.Holds rl tp (· < κ) w := by
  cases l with
  | lt i j pos => exact hw
  | rel t i j pos => exact hw
  | top t i pos => exact ⟨(S.monotone_eval t hwv).trans_lt hv.1, hw.2⟩

theorem lit_abs {α : Label} {κ : Key}
    (ih : ∀ κ' < κ, ∀ x, x < α → (R S κ' x α ↔ R S κ' x top))
    {n : Nat} (v : Fin n → Label) (hv : ∀ i, v i < α) (l : Lit S n) :
    l.Holds (relR S) (topR S α) (· < κ) v ↔ l.Holds (relR S) (topR S top) (· < κ) v := by
  cases l with
  | lt i j pos => exact Iff.rfl
  | rel t i j pos => exact Iff.rfl
  | top t i pos =>
    exact and_congr_right fun h => iff_congr (ih _ h _ (hv i)) Iff.rfl

/-- A witness in the full top structure is lowered below a good `α`, keeping the
entries below `α` and decreasing pointwise. -/
theorem lower {α : Label} (hα : Good S α) (φ : Form S) (v : Fin φ.n → Label)
    (hv : ∀ i, v i < top)
    (hl : ∀ l ∈ φ.lits, l.Holds (relR S) (topR S top) (fun _ => True) v) :
    ∃ w : Fin φ.n → Label, (∀ i, v i < α → w i = v i) ∧ (∀ i, w i < α) ∧
      (∀ i, w i ≤ v i) ∧ ∀ l ∈ φ.lits, l.Holds (relR S) (topR S top) (fun _ => True) w := by
  classical
  have h := hα ⟨φ.n, fun i => decide (v i < α), φ.lits⟩ v
    (fun i hi => of_decide_eq_true hi) (by unfold Sat; exact ⟨v, fun _ _ => rfl, hv, hl⟩)
  unfold Sat at h
  obtain ⟨w, hw1, hw2, hw3⟩ := h
  refine ⟨w, fun i hi => hw1 i (decide_eq_true hi), hw2, fun i => ?_, hw3⟩
  by_cases hi : v i < α
  · exact (hw1 i (decide_eq_true hi)).le
  · exact ((hw2 i).trans_le (not_lt.mp hi)).le

theorem absA {α : Label} (hα : Good S α) (κ : Key)
    (ih : ∀ κ' < κ, ∀ x, x < α → (R S κ' x α ↔ R S κ' x top))
    (φ : Form S) (p : Fin φ.n → Label) (hp : ∀ i, φ.fixed i = true → p i < α) :
    Sat (relR S) (topR S α) (· < κ) α φ p ↔ Sat (relR S) (topR S top) (· < κ) top φ p := by
  unfold Sat
  constructor
  · rintro ⟨v, h1, h2, h3⟩
    exact ⟨v, h1, fun i => (h2 i).trans_le (le_topL α),
      fun l hl => (lit_abs S ih v h2 l).mp (h3 l hl)⟩
  · rintro ⟨v, h1, h2, h3⟩
    obtain ⟨w, hw1, hw2, hw3, hw4⟩ :=
      lower S hα φ v h2 fun l hl => lit_true S l (h3 l hl)
    refine ⟨w, fun i hi => (hw1 i (by rw [h1 i hi]; exact hp i hi)).trans (h1 i hi), hw2,
      fun l hl => (lit_abs S ih w hw2 l).mpr (lit_lower S hw3 l (h3 l hl) (hw4 l hl))⟩

theorem top_abs {α : Label} (hα : Good S α) (hαt : α < top) (κ : Key) :
    ∀ x, x < α → (R S κ x α ↔ R S κ x top) := by
  refine WellFoundedLT.induction
    (motive := fun κ => ∀ x, x < α → (R S κ x α ↔ R S κ x top)) κ ?_
  intro κ ih x hx
  rw [R_iff S, R_iff S]
  constructor
  · rintro ⟨_, e⟩
    exact ⟨hx.trans_le (le_topL α), fun φ p hp => (e φ p hp).trans (absA S hα κ ih φ p fun i hi => (hp i hi).trans hx)⟩
  · rintro ⟨_, e⟩
    exact ⟨hx, fun φ p hp => (e φ p hp).trans (absA S hα κ ih φ p fun i hi => (hp i hi).trans hx).symm⟩

theorem absA' {α : Label} (hα : Good S α) (hαt : α < top) (κ : Key)
    (φ : Form S) (p : Fin φ.n → Label) (hp : ∀ i, φ.fixed i = true → p i < α) :
    Sat (relR S) (topR S α) (· < κ) α φ p ↔ Sat (relR S) (topR S top) (· < κ) top φ p :=
  absA S hα κ (fun κ' _ => top_abs S hα hαt κ') φ p hp

theorem good_R {α β : Label} (hα : Good S α) (hβ : Good S β) (hαβ : α < β)
    (hβt : β < top) (κ : Key) : R S κ α β := by
  rw [R_iff S]
  refine ⟨hαβ, fun φ p hp => ?_⟩
  rw [absA' S hα (hαβ.trans hβt) κ φ p hp,
    absA' S hβ hβt κ φ p fun i hi => (hp i hi).trans hαβ]

/-! ### Initial representations -/

noncomputable def points : ℕ → Label
  | 0 => lam S zeroL
  | k + 1 => lam S (points k)

theorem points_lt : ∀ k, points S k < top
  | 0 => lam_lt S zeroL_lt_top
  | k + 1 => lam_lt S (points_lt k)

theorem points_good : ∀ k, Good S (points S k)
  | 0 => lam_good S zeroL_lt_top
  | k + 1 => lam_good S (points_lt S k)

theorem points_strictMono : StrictMono (points S) :=
  strictMono_nat_of_lt_succ fun k => lt_lam S (points_lt S k)

/-- Phyrion's `initial_finite_graph`, verbatim statement, for this `R`. -/
theorem initial_finite_graph {n : Nat} (G : List (InternalAtom S n))
    (N : List (TopAtom S n)) :
    ∃ beta : Label, beta < top ∧ ∃ f : Fin n → Label,
      StrictMono f ∧ Bounded f beta ∧
      InternalHolds S (R S) G f ∧ TopHolds S (R S) N f beta := by
  refine ⟨points S n, points_lt S n, fun i => points S i.val, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact points_strictMono S hij
  · intro i
    exact points_strictMono S i.isLt
  · intro e _
    exact good_R S (points_good S _) (points_good S _)
      (points_strictMono S e.parent_lt_child) (points_lt S _) _
  · intro e _
    exact good_R S (points_good S _) (points_good S _)
      (points_strictMono S e.parent.isLt) (points_lt S _) _

end OmegaY.Por.Supply
