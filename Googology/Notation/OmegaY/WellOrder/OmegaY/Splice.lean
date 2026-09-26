/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Splice.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Splice.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.KeyReflection

set_option backward.do.legacy false

/-!
Finite block splicing for the actual multi-root reflection relation.
All column maps, labels and relation facts are constructed here. The geometric
classification of edges of the omega-Y copy algorithm is a separate obligation.
-/

namespace OmegaY.Splice

universe u
variable {Label : Type u} [LinearOrder Label] {n m : Nat}

def width (cut : Fin n) : Nat := n + (n - cut.val)

def old (cut : Fin n) (i : Fin n) : Fin (width cut) :=
  ⟨i.val, by unfold width; omega⟩

def moved (cut : Fin n) (i : Fin n) : Fin (width cut) :=
  if hi : i < cut then old cut i
  else ⟨n + (i.val - cut.val), by unfold width; omega⟩

def boundary (cut : Fin n) : Fin (width cut) :=
  ⟨n, by unfold width; have := cut.isLt; omega⟩

theorem old_strictMono (cut : Fin n) : StrictMono (old cut) := by
  intro i j h
  exact h

theorem moved_strictMono (cut : Fin n) : StrictMono (moved cut) := by
  intro i j hij
  unfold moved
  split <;> split <;> simp only [old, Fin.mk_lt_mk] <;> omega

def labels (cut : Fin n) (f g : Fin n → Label) (i : Fin (width cut)) : Label :=
  if hi : i.val < n then g ⟨i.val, hi⟩
  else f ⟨cut.val + i.val - n, by have := i.isLt; unfold width at *; omega⟩

@[simp] theorem labels_old (cut : Fin n) (f g : Fin n → Label) (i : Fin n) :
    labels cut f g (old cut i) = g i := by
  simp [labels, old, i.isLt]

@[simp] theorem labels_boundary (cut : Fin n) (f g : Fin n → Label) :
    labels cut f g (boundary cut) = f cut := by
  simp [labels, boundary]

theorem labels_moved (cut : Fin n) (f g : Fin n → Label)
    (hfix : ∀ i, i < cut → g i = f i) (i : Fin n) :
    labels cut f g (moved cut i) = f i := by
  unfold moved
  split
  · rw [labels_old]
    exact hfix i (by assumption)
  · rename_i hi
    have hv : cut.val ≤ i.val := by omega
    simp only [labels, Fin.val_mk, Nat.not_lt.mpr (Nat.le_add_right n _), dite_false]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

theorem labels_strictMono (cut : Fin n) (f g : Fin n → Label)
    (hf : StrictMono f) (hg : StrictMono g)
    (hbelow : Reflection.Bounded g (f cut)) : StrictMono (labels cut f g) := by
  intro i j hij
  have hiBound := i.isLt
  have hjBound := j.isLt
  have hiVal : i.val < j.val := hij
  unfold labels
  split
  · rename_i hin
    split
    · exact hg (by exact hij)
    · rename_i hjn
      refine lt_of_lt_of_le (hbelow _) (hf.monotone ?_)
      change cut.val ≤ cut.val + j.val - n
      omega
  · rename_i hin
    split
    · rename_i hjn
      omega
    · apply hf
      change cut.val + i.val - n < cut.val + j.val - n
      omega

theorem labels_bounded (cut : Fin n) (f g : Fin n → Label) {top : Label}
    (hf : Reflection.Bounded f top) (hg : Reflection.Bounded g (f cut)) :
    Reflection.Bounded (labels cut f g) top := by
  intro i
  unfold labels
  split
  · exact lt_trans (hg _) (hf cut)
  · exact hf _

abbrev Atom (m n : Nat) := Reflection.InternalAtom (KeyReflection.vectorSyntax (Label := Label) m) n
abbrev TopAtom (m n : Nat) := Reflection.TopAtom (KeyReflection.vectorSyntax (Label := Label) m) n

def mapAtom {k : Nat} (mu : Fin n → Fin k) (hmu : StrictMono mu)
    (e : Atom (Label := Label) m n) : Atom (Label := Label) m k where
  key := Keys.relabel e.key mu
  parent := mu e.parent
  child := mu e.child
  parent_lt_child := hmu e.parent_lt_child

def seamAtom (cut : Fin n) (d : TopAtom (Label := Label) m n) :
    Atom (Label := Label) m (width cut) where
  key := Keys.relabel d.key (old cut)
  parent := old cut d.parent
  child := boundary cut
  parent_lt_child := d.parent.isLt

/-- Pure finite column and key-template classification, without label or
reflection assumptions. -/
def Classified (cut : Fin n) (G : List (Atom (Label := Label) m n))
    (N : List (TopAtom (Label := Label) m n))
    (e : Atom (Label := Label) m (width cut)) : Prop :=
  (∃ s ∈ G, e = mapAtom (old cut) (old_strictMono cut) s) ∨
  (∃ s ∈ G, e.parent = moved cut s.parent ∧ e.child = moved cut s.child ∧
    Keys.templateKey e.key ≤ Keys.templateKey (Keys.relabel s.key (moved cut))) ∨
  (∃ d ∈ N, e = seamAtom cut d)

variable [WellFoundedLT Label]

def Holds (e : Atom (Label := Label) m n) (f : Fin n → Label) : Prop :=
  KeyReflection.R m (Keys.eval e.key f) (f e.parent) (f e.child)

theorem holds_map {k : Nat} (mu : Fin n → Fin k) (hmu : StrictMono mu)
    (e : Atom (Label := Label) m n) (f : Fin n → Label) (h : Fin k → Label)
    (hlabels : ∀ i, h (mu i) = f i) (he : Holds e f) : Holds (mapAtom mu hmu e) h := by
  change KeyReflection.R m (Keys.eval (Keys.relabel e.key mu) h)
    (h (mu e.parent)) (h (mu e.child))
  rw [Keys.eval_relabel_of_labels e.key mu f h hlabels,
    hlabels e.parent, hlabels e.child]
  exact he

/-- Source atoms can supply new edges whose keys are weaker than the exact
transported key. This includes a fill edge only after its root bound is proved. -/
theorem holds_weakened_copy {k : Nat} (mu : Fin n → Fin k)
    (e : Atom (Label := Label) m n) (fresh : Atom (Label := Label) m k)
    (f : Fin n → Label) (h : Fin k → Label)
    (hlabels : ∀ i, h (mu i) = f i)
    (hp : fresh.parent = mu e.parent) (hc : fresh.child = mu e.child)
    (hkey : Keys.eval fresh.key h ≤ Keys.eval (Keys.relabel e.key mu) h)
    (he : Holds e f) : Holds fresh h := by
  unfold Holds
  rw [hp, hc, hlabels e.parent, hlabels e.child]
  apply KeyReflection.weaken _ he
  simpa only [Keys.eval_relabel_of_labels e.key mu f h hlabels] using hkey

theorem holds_seam (cut : Fin n) (d : TopAtom (Label := Label) m n)
    (f g : Fin n → Label)
    (hd : KeyReflection.R m (Keys.eval d.key g) (g d.parent) (f cut)) :
    Holds (seamAtom cut d) (labels cut f g) := by
  change KeyReflection.R m (Keys.eval (Keys.relabel d.key (old cut)) (labels cut f g))
    (labels cut f g (old cut d.parent)) (labels cut f g (boundary cut))
  rw [Keys.eval_relabel_of_labels d.key (old cut) g (labels cut f g) (labels_old cut f g),
    labels_old, labels_boundary]
  exact hd

/-- One actual reflection plus a concrete label splice, simultaneously
preserving old atoms and exact moved atoms and bounding every new label. -/
theorem reflected_block (cut : Fin n)
    (G : List (Atom (Label := Label) m n))
    (N : List (TopAtom (Label := Label) m n)) (f : Fin n → Label)
    {theta : Keys.Key m Label} {top : Label}
    (hf : StrictMono f) (hb : Reflection.Bounded f top)
    (hG : Reflection.InternalHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) G f)
    (hk : Reflection.KeysBelow (KeyReflection.vectorSyntax m) N f theta)
    (hN : Reflection.TopHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) N f top)
    (hcontrol : KeyReflection.R m theta (f cut) top) :
    ∃ g : Fin n → Label,
      StrictMono (labels cut f g) ∧ Reflection.Bounded (labels cut f g) top ∧
      (∀ i, i < cut → g i = f i) ∧
      (∀ i, labels cut f g (moved cut i) = f i) ∧
      (∀ e ∈ G, Holds (mapAtom (old cut) (old_strictMono cut) e) (labels cut f g)) ∧
      (∀ e ∈ G, Holds (mapAtom (moved cut) (moved_strictMono cut) e) (labels cut f g)) ∧
      Reflection.TopHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) N g (f cut) := by
  obtain ⟨g, hgm, hgb, hfix, _hle, hgG, hgN⟩ :=
    Reflection.finite_reflection (KeyReflection.vectorSyntax m) G N f cut hf hb hG hk hN hcontrol
  refine ⟨g, labels_strictMono cut f g hf hgm hgb, labels_bounded cut f g hb hgb,
    hfix, labels_moved cut f g hfix, ?_, ?_, hgN⟩
  · intro e he
    exact holds_map (old cut) (old_strictMono cut) e g (labels cut f g)
      (labels_old cut f g) (hgG e he)
  · intro e he
    exact holds_map (moved cut) (moved_strictMono cut) e f (labels cut f g)
      (labels_moved cut f g hfix) (hG e he)

/-- Every edge of a classified output graph is represented below the old
top. The algorithm still has to supply `hclass`, including fill-key bounds. -/
theorem classified_graph_represented (cut : Fin n)
    (G : List (Atom (Label := Label) m n))
    (N : List (TopAtom (Label := Label) m n))
    (H : List (Atom (Label := Label) m (width cut))) (f : Fin n → Label)
    {theta : Keys.Key m Label} {top : Label}
    (hf : StrictMono f) (hb : Reflection.Bounded f top)
    (hG : Reflection.InternalHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) G f)
    (hk : Reflection.KeysBelow (KeyReflection.vectorSyntax m) N f theta)
    (hN : Reflection.TopHolds (KeyReflection.vectorSyntax m) (KeyReflection.R m) N f top)
    (hcontrol : KeyReflection.R m theta (f cut) top)
    (hclass : ∀ e ∈ H, Classified cut G N e) :
    ∃ h : Fin (width cut) → Label, StrictMono h ∧ Reflection.Bounded h top ∧
      (∀ i, h (moved cut i) = f i) ∧ ∀ e ∈ H, Holds e h := by
  obtain ⟨g, hmono, hbound, _hfix, hmove, hold, _hcopied, hseam⟩ :=
    reflected_block cut G N f hf hb hG hk hN hcontrol
  refine ⟨labels cut f g, hmono, hbound, hmove, ?_⟩
  intro e he
  rcases hclass e he with ⟨s, hs, rfl⟩ | ⟨s, hs, hp, hc, hkey⟩ | ⟨d, hd, rfl⟩
  · exact hold s hs
  · exact holds_weakened_copy (moved cut) s e f (labels cut f g) hmove hp hc
      (Keys.eval_le_of_template_le _ _ _ hmono hkey) (hG s hs)
  · exact holds_seam cut d f g (hseam d hd)

end OmegaY.Splice

#print axioms OmegaY.Splice.reflected_block
#print axioms OmegaY.Splice.holds_weakened_copy
#print axioms OmegaY.Splice.classified_graph_represented
