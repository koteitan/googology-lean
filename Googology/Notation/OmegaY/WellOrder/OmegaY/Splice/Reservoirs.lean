/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Splice/Reservoirs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Splice/Reservoirs.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Splice

set_option backward.do.legacy false

/-!
One reflection step with the entire finite reserve retained.  The hypotheses
classifying the new graph are finite geometric statements about its atoms.
They do not assume the existence of the next labels or next reserve relations.
-/

namespace OmegaY.Splice

universe u
variable {Label : Type u} [LinearOrder Label] [WellFoundedLT Label]
variable {m n : Nat}

/-- Literal transport of a virtual edge to the unchanged external label. -/
def mapTop {k : Nat} (mu : Fin n → Fin k)
    (e : TopAtom (Label := Label) m n) : TopAtom (Label := Label) m k where
  key := Keys.relabel e.key mu
  parent := mu e.parent

/-- All data that must survive between two successive reflection steps.
The control's parent is the next cut column. -/
structure ReservoirState
    (G F : List (Atom (Label := Label) m n))
    (T : List (TopAtom (Label := Label) m n))
    (control : TopAtom (Label := Label) m n)
    (f : Fin n → Label) (beta : Label) : Prop where
  strict : StrictMono f
  bounded : Reflection.Bounded f beta
  graph : Reflection.InternalHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) G f
  internal : Reflection.InternalHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) F f
  virtual : Reflection.TopHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) T f beta
  controlled : KeyReflection.R m (Keys.eval control.key f) (f control.parent) beta

/-- A demand may use a weaker key than its same-parent virtual reserve. -/
def DemandCovered (T N : List (TopAtom (Label := Label) m n)) : Prop :=
  ∀ d ∈ N, ∃ t ∈ T, d.parent = t.parent ∧
    Keys.templateKey d.key ≤ Keys.templateKey t.key

/-- Exact retained edges, weakened moved internal reserve edges, and weakened
seam demands are the three classes accepted by the semantic splice. -/
def ReservoirClassified (cut : Fin n)
    (G F : List (Atom (Label := Label) m n))
    (N : List (TopAtom (Label := Label) m n))
    (e : Atom (Label := Label) m (width cut)) : Prop :=
  (∃ s ∈ G, e = mapAtom (old cut) (old_strictMono cut) s) ∨
  (∃ s ∈ F, e.parent = moved cut s.parent ∧ e.child = moved cut s.child ∧
    Keys.templateKey e.key ≤ Keys.templateKey (Keys.relabel s.key (moved cut))) ∨
  (∃ d ∈ N, e.parent = old cut d.parent ∧ e.child = boundary cut ∧
    Keys.templateKey e.key ≤ Keys.templateKey (Keys.relabel d.key (old cut)))

theorem top_holds_map {k : Nat} (mu : Fin n → Fin k)
    (e : TopAtom (Label := Label) m n) (f : Fin n → Label) (h : Fin k → Label)
    {beta : Label} (hlabels : ∀ i, h (mu i) = f i)
    (he : KeyReflection.R m (Keys.eval e.key f) (f e.parent) beta) :
    KeyReflection.R m (Keys.eval (mapTop mu e).key h) (h (mapTop mu e).parent) beta := by
  change KeyReflection.R m (Keys.eval (Keys.relabel e.key mu) h) (h (mu e.parent)) beta
  rw [Keys.eval_relabel_of_labels e.key mu f h hlabels, hlabels e.parent]
  exact he

theorem DemandCovered.top_holds
    {T N : List (TopAtom (Label := Label) m n)} (hCovered : DemandCovered T N)
    {f : Fin n → Label} {beta : Label} (hMono : StrictMono f)
    (hT : Reflection.TopHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) T f beta) :
    Reflection.TopHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) N f beta := by
  intro d hd
  obtain ⟨t, ht, hp, hk⟩ := hCovered d hd
  change KeyReflection.R m (Keys.eval d.key f) (f d.parent) beta
  rw [hp]
  exact KeyReflection.weaken (Keys.eval_le_of_template_le _ _ _ hMono hk) (hT t ht)

theorem holds_weakened_seam (cut : Fin n)
    (d : TopAtom (Label := Label) m n) (e : Atom (Label := Label) m (width cut))
    (f g : Fin n → Label)
    (hp : e.parent = old cut d.parent) (hc : e.child = boundary cut)
    (hk : Keys.eval e.key (labels cut f g) ≤
      Keys.eval (Keys.relabel d.key (old cut)) (labels cut f g))
    (hd : KeyReflection.R m (Keys.eval d.key g) (g d.parent) (f cut)) :
    Holds e (labels cut f g) := by
  unfold Holds
  rw [hp, hc, labels_old, labels_boundary]
  apply KeyReflection.weaken _ hd
  simpa only [Keys.eval_relabel_of_labels d.key (old cut) g (labels cut f g)
    (labels_old cut f g)] using hk

@[simp] theorem moved_cut_eq_boundary (cut : Fin n) : moved cut cut = boundary cut := by
  simp [moved, boundary]

/-- The same external `beta` controls the next step.  In particular the output
contains literal moved copies of every reserve atom, even if it was unused by
the current graph classification.  The local demands need only be weaker than
their virtual reserves and strictly weaker than the current control key. -/
theorem splice_reservoirs
    (G F : List (Atom (Label := Label) m n))
    (T N : List (TopAtom (Label := Label) m n))
    (control : TopAtom (Label := Label) m n)
    (H : List (Atom (Label := Label) m (width control.parent)))
    (f : Fin n → Label) (beta : Label)
    (hState : ReservoirState G F T control f beta)
    (hCovered : DemandCovered T N)
    (hKeys : ∀ d ∈ N, Keys.templateKey d.key < Keys.templateKey control.key)
    (hClass : ∀ e ∈ H, ReservoirClassified control.parent G F N e) :
    ∃ g : Fin n → Label,
      (∀ i, i < control.parent → g i = f i) ∧
      (∀ i, g i ≤ f i) ∧
      (∀ i, labels control.parent f g (moved control.parent i) = f i) ∧
      ReservoirState H
        (F.map (mapAtom (moved control.parent) (moved_strictMono control.parent)))
        (T.map (mapTop (moved control.parent)))
        (mapTop (moved control.parent) control)
        (labels control.parent f g) beta := by
  have hInternal : Reflection.InternalHolds (KeyReflection.vectorSyntax m)
      (KeyReflection.R m) (G ++ F) f := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hState.graph e he
    · exact hState.internal e he
  have hDemands := hCovered.top_holds hState.strict hState.virtual
  have hBelow : Reflection.KeysBelow (KeyReflection.vectorSyntax m) N f
      (Keys.eval control.key f) := by
    intro d hd
    exact Keys.eval_lt_of_template_lt _ _ _ hState.strict (hKeys d hd)
  obtain ⟨g, hgm, hgb, hFix, hLe, hOld, hSeam⟩ :=
    Reflection.finite_reflection (KeyReflection.vectorSyntax m) (G ++ F) N f control.parent
      hState.strict hState.bounded hInternal hBelow hDemands hState.controlled
  have hMove := labels_moved control.parent f g hFix
  have hMono := labels_strictMono control.parent f g hState.strict hgm hgb
  refine ⟨g, hFix, hLe, hMove, ?_⟩
  refine ⟨hMono, labels_bounded control.parent f g hState.bounded hgb, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases hClass e he with ⟨s, hs, rfl⟩ | ⟨s, hs, hp, hc, hk⟩ | ⟨d, hd, hp, hc, hk⟩
    · exact holds_map (old control.parent) (old_strictMono control.parent) s g
        (labels control.parent f g) (labels_old control.parent f g)
        (hOld s (List.mem_append_left F hs))
    · exact holds_weakened_copy (moved control.parent) s e f (labels control.parent f g)
        hMove hp hc (Keys.eval_le_of_template_le _ _ _ hMono hk) (hState.internal s hs)
    · exact holds_weakened_seam control.parent d e f g hp hc
        (Keys.eval_le_of_template_le _ _ _ hMono hk) (hSeam d hd)
  · intro e he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    exact holds_map (moved control.parent) (moved_strictMono control.parent) s f
      (labels control.parent f g) hMove (hState.internal s hs)
  · intro e he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    exact top_holds_map (moved control.parent) t f (labels control.parent f g)
      hMove (hState.virtual t ht)
  · exact top_holds_map (moved control.parent) control f (labels control.parent f g)
      hMove hState.controlled

end OmegaY.Splice

#print axioms OmegaY.Splice.splice_reservoirs
