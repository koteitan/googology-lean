/-
The patterns-of-resemblance model of the omega-Y core, part 2 (this repository).
Taken from koteitan, wy-wo-por, `Por/Relation.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
The namespace `Por` is renamed to `OmegaY.Por`, since the 1-Y model of this repository uses `Por`.
-/
import Googology.Notation.OmegaY.WellOrder.Por.Formula

set_option backward.do.legacy false

/-!
# The relation `R`

  R θ a b  :⟺  a < b ∧ 𝔄^a_θ ≼_{Σ₁} 𝔄^b_θ.

`𝔄^c_θ` has domain `{x | x < c}`, the order, the internal relations
`Rel_t(v_i, v_j) :⟺ R (eval t v) v_i v_j` and the top predicates
`Top_t(v_i) :⟺ R (eval t v) v_i c`, the latter defined only for keys below `θ`.
`R` is defined by well-founded recursion on `(top, key)` in lexicographic order.

It proves the defining equation `R_iff`, strictness `R_lt`, key weakening
`key_weaken`, and the finite reflection `finite_reflection` in the exact form
the omega-Y core calls.
-/

namespace OmegaY.Por

open OmegaY.Reflection

universe u v w

variable {Label : Type u} {Key : Type v} [LinearOrder Label] [LinearOrder Key]
variable {S : KeySyntax.{u,v,w} Label Key}

variable [WellFoundedLT Label] [WellFoundedLT Key]

/-- Recursion stages `(top, key)`, lexicographic. -/
abbrev StageLT : (Label × Key) → (Label × Key) → Prop :=
  Prod.Lex (· < ·) (· < ·)

theorem stage_wf : WellFounded (StageLT (Label := Label) (Key := Key)) :=
  WellFounded.prod_lex wellFounded_lt wellFounded_lt

variable (S)

/-- One recursion step at stage `s = (b, θ)`: the set of `a` with `R θ a b`. -/
noncomputable def stepF (s : Label × Key) (IH : ∀ t, StageLT t s → Label → Prop) :
    Label → Prop :=
  fun a => ∃ hab : a < s.1,
    ElemL (S := S)
      (fun κ x y => ∃ h : y < s.1, IH (y, κ) (Prod.Lex.left _ _ h) x)
      (fun κ x => IH (a, κ) (Prod.Lex.left _ _ hab) x)
      (fun κ x => ∃ h : κ < s.2, IH (s.1, κ) (Prod.Lex.right _ h) x)
      s.2 a s.1

/-- `R θ a b`: the height-`a` structure is a Σ₁-elementary substructure of the
height-`b` structure, in the language whose top bits are defined below `θ`. -/
noncomputable def R (θ : Key) (a b : Label) : Prop :=
  stage_wf.fix (stepF S) (b, θ) a

/-- The true structures. -/
def relR : Key → Label → Label → Prop := fun κ x y => R S κ x y
def topR (c : Label) : Key → Label → Prop := fun κ x => R S κ x c

/-- The defining equation. -/
theorem R_iff {θ : Key} {a b : Label} :
    R S θ a b ↔ a < b ∧ ElemL (S := S) (relR S) (topR S a) (topR S b) θ a b := by
  have key : ∀ _ : a < b,
      ElemL (S := S) (fun κ x y => ∃ _ : y < b, R S κ x y) (topR S a)
        (fun κ x => ∃ _ : κ < θ, R S κ x b) θ a b ↔
      ElemL (S := S) (relR S) (topR S a) (topR S b) θ a b := by
    intro hab
    refine forall_congr' fun φ => forall_congr' fun p => forall_congr' fun _ =>
      iff_congr ?_ ?_
    · exact sat_congr (fun κ x y hy => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy.trans hab, h⟩⟩)
        (fun κ x _ => Iff.rfl)
    · exact sat_congr (fun κ x y hy => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy, h⟩⟩)
        (fun κ x hκ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hκ, h⟩⟩)
  show stage_wf.fix (stepF S) (b, θ) a ↔ _
  rw [WellFounded.fix_eq]
  exact ⟨fun ⟨hab, h⟩ => ⟨hab, (key hab).mp h⟩, fun ⟨hab, h⟩ => ⟨hab, (key hab).mpr h⟩⟩

theorem R_lt {θ : Key} {a b : Label} (h : R S θ a b) : a < b := ((R_iff S).mp h).1

/-- Key weakening. -/
theorem key_weaken {θ Θ : Key} {a b : Label} (hle : θ ≤ Θ) (h : R S Θ a b) :
    R S θ a b := by
  obtain ⟨hab, E⟩ := (R_iff S).mp h
  refine (R_iff S).mpr ⟨hab, ?_⟩
  intro φ p hp
  constructor
  · rintro ⟨w, hwp, hwa, hw⟩
    let φ' : Form S := ⟨φ.n, fun _ => true, φ.lits⟩
    have hs : Sat (relR S) (topR S a) (· < Θ) a φ' w :=
      ⟨w, fun _ _ => rfl, hwa, fun l hl =>
        Lit.holds_allow_mono (fun κ hκ => lt_of_lt_of_le hκ hle) (hw l hl)⟩
    obtain ⟨v, hvw, hvb, hv⟩ := (E φ' w (fun i _ => hwa i)).mp hs
    have hveq : v = w := funext fun i => hvw i rfl
    subst hveq
    exact ⟨v, hwp, hvb, fun l hl => Lit.holds_of_le (fun _ => le_rfl) (hw l hl) (hv l hl)⟩
  · rintro ⟨v, hvp, hvb, hv⟩
    let φ' : Form S := ⟨φ.n, fun i => decide (v i < a), φ.lits⟩
    have hs : Sat (relR S) (topR S b) (· < Θ) b φ' v :=
      ⟨v, fun _ _ => rfl, hvb, fun l hl =>
        Lit.holds_allow_mono (fun κ hκ => lt_of_lt_of_le hκ hle) (hv l hl)⟩
    obtain ⟨w, hwv, hwa, hw⟩ :=
      (E φ' v (fun i hi => of_decide_eq_true hi)).mpr hs
    have hle' : ∀ i, w i ≤ v i := fun i => by
      by_cases hi : v i < a
      · exact (hwv i (decide_eq_true hi)).le
      · exact (hwa i).le.trans (not_lt.mp hi)
    refine ⟨w, fun i hi => ?_, hwa, fun l hl => Lit.holds_of_le hle' (hv l hl) (hw l hl)⟩
    have hpi : v i = p i := hvp i hi
    have hva : v i < a := by rw [hpi]; exact hp i hi
    rw [hwv i (decide_eq_true hva), hpi]

/-- The literals of the reflected formula: the full order type, the internal atoms and the
demands toward the top. -/
def reflLits {n : Nat} (G : List (InternalAtom S n)) (N : List (TopAtom S n)) :
    List (Lit S n) :=
  ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => Lit.lt i j (decide (i < j)))
    ++ G.map (fun e => Lit.rel e.key e.parent e.child true)
    ++ N.map (fun e => Lit.top e.key e.parent true)

/-- The reflected formula: positions below `cut` are parameters. -/
def reflForm {n : Nat} (G : List (InternalAtom S n)) (N : List (TopAtom S n)) (cut : Fin n) :
    Form S :=
  ⟨n, fun i => decide (i < cut), reflLits S G N⟩

omit [WellFoundedLT Label] [WellFoundedLT Key] in
theorem reflLits_holds {n : Nat} (G : List (InternalAtom S n)) (N : List (TopAtom S n))
    {rel : Key → Label → Label → Prop} {top : Key → Label → Prop} {allow : Key → Prop}
    {v : Fin n → Label} :
    (∀ l ∈ reflLits S G N, l.Holds rel top allow v) ↔
      (∀ i j, (v i < v j ↔ i < j)) ∧
      (∀ e ∈ G, rel (S.eval e.key v) (v e.parent) (v e.child)) ∧
      (∀ e ∈ N, allow (S.eval e.key v) ∧ top (S.eval e.key v) (v e.parent)) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun e he => ?_, fun e he => ?_⟩
    · have := h (Lit.lt i j (decide (i < j))) (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
          List.mem_map_of_mem (List.mem_finRange j)⟩)))
      exact this.trans decide_eq_true_iff
    · have := h (Lit.rel e.key e.parent e.child true)
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he)))
      exact this.mpr rfl
    · have := h (Lit.top e.key e.parent true)
        (List.mem_append_right _ (List.mem_map_of_mem he))
      exact ⟨this.1, this.2.mpr rfl⟩
  · rintro ⟨hlt, hrel, htop⟩ l hl
    simp only [reflLits, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
      true_and] at hl
    rcases hl with (⟨i, j, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact (hlt i j).trans decide_eq_true_iff.symm
    · exact iff_of_true (hrel e he) rfl
    · exact ⟨(htop e he).1, iff_of_true (htop e he).2 rfl⟩

/-- Phyrion's `finite_reflection`, verbatim statement, for this `R`. -/
theorem finite_reflection {n : Nat} (G : List (InternalAtom S n))
    (N : List (TopAtom S n)) (f : Fin n → Label) (cut : Fin n)
    {theta : Key} {top : Label} (hmono : StrictMono f) (hbound : Bounded f top)
    (hG : InternalHolds S (R S) G f) (hkeys : KeysBelow S N f theta)
    (hN : TopHolds S (R S) N f top) (hcontrol : R S theta (f cut) top) :
    ∃ g : Fin n → Label, StrictMono g ∧ Bounded g (f cut) ∧
      (∀ i, i < cut → g i = f i) ∧ (∀ i, g i ≤ f i) ∧
      InternalHolds S (R S) G g ∧ TopHolds S (R S) N g (f cut) := by
  obtain ⟨_, E⟩ := (R_iff S).mp hcontrol
  have hp : ∀ i, (reflForm S G N cut).fixed i = true → f i < f cut :=
    fun i hi => hmono (of_decide_eq_true hi)
  have hs : Sat (relR S) (topR S top) (· < theta) top (reflForm S G N cut) f :=
    ⟨f, fun _ _ => rfl, hbound, (reflLits_holds S G N).mpr
      ⟨fun i j => hmono.lt_iff_lt, hG, fun e he => ⟨hkeys e he, hN e he⟩⟩⟩
  obtain ⟨g, hgf, hgb, hg⟩ := (E (reflForm S G N cut) f hp).mpr hs
  obtain ⟨hlt, hrel, htop⟩ := (reflLits_holds S G N).mp hg
  refine ⟨g, fun i j hij => (hlt i j).mpr hij, hgb, fun i hi => hgf i (decide_eq_true hi),
    fun i => ?_, hrel, fun e he => (htop e he).2⟩
  by_cases hi : i < cut
  · exact (hgf i (decide_eq_true hi)).le
  · exact (hgb i).le.trans (hmono.monotone (not_lt.mp hi))

end OmegaY.Por
