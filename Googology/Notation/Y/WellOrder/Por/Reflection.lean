/-
From koteitan, 1y-wo-por, `Por/Reflection.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.Relation
import Googology.Notation.Y.WellOrder.OneY.RootIndexed.Representation

/-!
# Finite reflection (obligation O6)

This file proves `finiteReflection`: the model satisfies the interface
`OneY.RootIndexed.FiniteReflection` of the core.

The proof writes the diagram and the demands toward the top as one Σ₁ formula
(`reflMat`). The old labels witness it below `β`. The relation
`R K θ (f cut) β` reflects it below `f cut`, and the new witnesses give the new
representation. Demands of layer `K` name their root, so they are visible at
level `(K, θ)`.
-/

open Classical Cardinal Ordinal

namespace Por

open OneY.RootIndexed (Atom Diagram TopAtom Representation Bounded Admissible FiniteReflection)

def getLt {m n : ℕ} (d : Diag m n) (a b : ℕ) : Bool :=
  if h : a < n ∧ b < n then d.1 ⟨a, h.1⟩ ⟨b, h.2⟩ else false

def getRel {m n : ℕ} (d : Diag m n) (j a b c : ℕ) : Bool :=
  if h : j < m ∧ a < n ∧ b < n ∧ c < n then
    d.2.1 ⟨j, h.1⟩ ⟨a, h.2.1⟩ ⟨b, h.2.2.1⟩ ⟨c, h.2.2.2⟩ else false

def getTop {m n : ℕ} (d : Diag m n) (j a b : ℕ) : Bool :=
  if h : j < m ∧ a < n ∧ b < n then d.2.2 ⟨j, h.1⟩ ⟨a, h.2.1⟩ ⟨b, h.2.2⟩ else false

theorem getLt_diagM {rel : RelF} {top : TopF} {allow : ℕ → ℕ → Prop} {m n : ℕ}
    {v : ℕ → Ord} {a b : ℕ} (ha : a < n) (hb : b < n) :
    getLt (diagM rel top allow m n v) a b = true ↔ v a < v b := by
  simp [getLt, diagM, ha, hb]

theorem getRel_diagM {rel : RelF} {top : TopF} {allow : ℕ → ℕ → Prop} {m n : ℕ}
    {v : ℕ → Ord} {j a b c : ℕ} (hj : j < m) (ha : a < n) (hb : b < n) (hc : c < n) :
    getRel (diagM rel top allow m n v) j a b c = true ↔ rel j (v a) (v b) (v c) := by
  simp [getRel, diagM, hj, ha, hb, hc]

theorem getTop_diagM {rel : RelF} {top : TopF} {allow : ℕ → ℕ → Prop} {m n : ℕ}
    {v : ℕ → Ord} {j a b : ℕ} (hj : j < m) (ha : a < n) (hb : b < n) :
    getTop (diagM rel top allow m n v) j a b = true ↔ (allow j a ∧ top j (v a) (v b)) := by
  simp [getTop, diagM, hj, ha, hb]

/-- A bound for all layers occurring in the diagram and in the demands. -/
def sigBound (G : Diagram) (needs : List TopAtom) : ℕ :=
  (G.atoms.map Atom.layer).sum + (needs.map TopAtom.layer).sum + 1

theorem atom_layer_lt {G : Diagram} {needs : List TopAtom} {e : Atom} (he : e ∈ G.atoms) :
    e.layer < sigBound G needs := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := Atom.layer) he)
  unfold sigBound
  omega

theorem need_layer_lt {G : Diagram} {needs : List TopAtom} {d : TopAtom} (hd : d ∈ needs) :
    d.layer < sigBound G needs := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := TopAtom.layer) hd)
  unfold sigBound
  omega

/-- The matrix of the reflected formula: order of all columns, all internal atoms, all
demands toward the top. -/
def reflMat (G : Diagram) (needs : List TopAtom) (m : ℕ) : Set (Diag m G.size) :=
  {d | (∀ i j, i < j → j < G.size → getLt d i j = true) ∧
       (∀ e ∈ G.atoms, getRel d e.layer e.root e.parent e.child = true) ∧
       (∀ dd ∈ needs, getTop d dd.layer dd.root dd.parent = true)}

theorem reflMat_iff (G : Diagram) (needs : List TopAtom)
    (hneeds : ∀ d ∈ needs, d.Valid G.size)
    (rel : RelF) (top : TopF) (allow : ℕ → ℕ → Prop) (v : ℕ → Ord) :
    diagM rel top allow (sigBound G needs) G.size v ∈ reflMat G needs (sigBound G needs) ↔
      (∀ i j, i < j → j < G.size → v i < v j) ∧
      (∀ e ∈ G.atoms, rel e.layer (v e.root) (v e.parent) (v e.child)) ∧
      (∀ dd ∈ needs, allow dd.layer dd.root ∧ top dd.layer (v dd.root) (v dd.parent)) := by
  refine and_congr (forall_congr' fun i => forall_congr' fun j => forall_congr' fun hij =>
    forall_congr' fun hj => getLt_diagM (by omega) hj) (and_congr ?_ ?_)
  · refine forall_congr' fun e => forall_congr' fun he => ?_
    obtain ⟨h1, h2, h3⟩ := G.valid e he
    exact getRel_diagM (atom_layer_lt he) (by omega) (by omega) h3
  · refine forall_congr' fun dd => forall_congr' fun hdd => ?_
    obtain ⟨h1, h2⟩ := hneeds dd hdd
    exact getTop_diagM (need_layer_lt hdd) (by omega) h2

/-- O6: `FiniteReflection` for the model. -/
theorem finiteReflection : FiniteReflection (α := Ord) (· < ·) (fun _ => True) R := by
  intro G cut K θ β f needs hcut hf _ hbound hctrl hvalid hadm hneeds
  obtain ⟨_, _, e⟩ := R_iff.mp hctrl
  let S : Set ℕ := {s | ∃ d ∈ needs, d.layer = K ∧ d.root = s}
  have hS : ∀ s ∈ S, s < cut ∧ f s < θ := by
    rintro s ⟨d, hd, hK, rfl⟩
    rcases hadm d hd with hlt | ⟨_, hr, hθ'⟩
    · exact absurd hK (Nat.ne_of_lt hlt)
    · exact ⟨hr, hθ'⟩
  have hallow : ∀ d ∈ needs, allowL K S d.layer d.root := by
    intro d hd
    rcases hadm d hd with hlt | ⟨hK, _, _⟩
    · exact Or.inl hlt
    · exact Or.inr ⟨hK, d, hd, hK, rfl⟩
  have hp : ∀ i < cut, f i < f cut := fun i hi => hf.ordered i cut hi hcut
  have hn : G.size ≤ cut + (G.size - cut) := by omega
  -- the formula holds in the structure of height `β`, witnessed by the old labels
  have hβ : Sat relR (topR β) (allowL K S) β (sigBound G needs) G.size
      (reflMat G needs (sigBound G needs)) (G.size - cut) cut f := by
    refine ⟨fun i => f (cut + i), fun i hi => hbound _ (by omega), ?_⟩
    have hv : cat cut f (fun i => f (cut + i)) = f := by
      funext i
      unfold cat
      split_ifs with h
      · rfl
      · show f (cut + (i - cut)) = f i
        congr 1
        omega
    rw [hv, reflMat_iff G needs hvalid]
    exact ⟨hf.ordered, hf.relations, fun d hd => ⟨hallow d hd, hneeds d hd⟩⟩
  -- reflect it into the structure of height `f cut`
  obtain ⟨y, hy, hD⟩ :=
    (e (sigBound G needs) G.size (reflMat G needs (sigBound G needs)) (G.size - cut) cut S f
      hn hp hS).mpr hβ
  rw [reflMat_iff G needs hvalid] at hD
  obtain ⟨hord, hrel, htop⟩ := hD
  refine ⟨cat cut f y, ⟨fun _ _ => trivial, hord, hrel⟩, fun i hi => cat_left hi,
    fun (i : ℕ) (hi : i < G.size) => cat_lt hp hy i (by omega), fun d hd => (htop d hd).2⟩

end Por
