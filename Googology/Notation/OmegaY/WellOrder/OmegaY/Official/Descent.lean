/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Descent.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.ReserveShape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Splice.IteratedReservoirs
import Googology.Notation.OmegaY.WellOrder.OmegaY.Model
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Prefix

set_option backward.do.legacy false

/-!
# Well-foundedness of the official expansion from the splice classification

A representation of a sequence `s` at dimension `D` is a strictly increasing
labelling of its columns below `ω₁` under which every leg atom of `M(s)`
(`Reserve.atomsOf s D`) holds. This file shows:

* every sequence has a representation (closed points, `Model.initial_finite_graph`);
* if `classifiedB s n D` is true and `s[n] = t` (official rule), every
  representation of `s` gives a representation of `t` whose labels are all below the
  last label of `s` (Phyrion's iterated splice theorem `Splice.iterated_reservoirs`);
* hence, if `classifiedB s n D` is true for every `s`, `n` and every `D` bounding the
  degrees of `M(s)`, the official expansion is well-founded.

The classification itself is not proved here; see `notes/04-official-design.md` §6.
-/

namespace OmegaY.Official.Descent

open Canonical Reserve

abbrev L := Model.Label

/-! ## Typed templates and atoms -/

/-- The entry of a raw key at index `i` (`none` is `⊤` or a missing entry). -/
def ent (K : RawKey) (i : Nat) : Option Nat := K[i]?.getD none

/-- The typed template of a raw key at width `n`. -/
def tmpl (m n : Nat) (K : RawKey) : Keys.Template m n :=
  fun i => match ent K i.val with
    | some v => if h : v < n then some ⟨v, h⟩ else none
    | none => none

/-- All column entries of a raw key are below `n`. -/
def Below (n : Nat) (K : RawKey) : Prop := ∀ i v, ent K i = some v → v < n

theorem tmpl_apply_some {m n : Nat} {K : RawKey} {i : Fin m} {v : Nat}
    (h : ent K i.val = some v) (hv : v < n) : tmpl m n K i = some ⟨v, hv⟩ := by
  simp [tmpl, h, hv]

theorem tmpl_apply_none {m n : Nat} {K : RawKey} {i : Fin m}
    (h : ent K i.val = none) : tmpl m n K i = none := by
  simp [tmpl, h]

theorem entryLt_spec {a b : Option Nat} (h : entryLt a b = true) :
    (∃ u v, a = some u ∧ b = some v ∧ u < v) ∨ (∃ u, a = some u ∧ b = none) := by
  cases a with
  | none => simp [entryLt] at h
  | some u =>
      cases b with
      | none => exact Or.inr ⟨u, rfl, rfl⟩
      | some v =>
          simp [entryLt] at h
          exact Or.inl ⟨u, v, rfl, rfl, h⟩

theorem ent_eq_of_getElem? {a b : RawKey} {j : Nat} (h : (a[j]? == b[j]?) = true) :
    ent a j = ent b j := by
  simp only [beq_iff_eq] at h
  simp [ent, h]

/-- The raw lexicographic order gives the order of template keys. -/
theorem templateKey_lt_of_keyLt {m n : Nat} {a b : RawKey} (ha : Below n a) (hb : Below n b)
    (h : keyLt m a b = true) :
    Keys.templateKey (tmpl m n a) < Keys.templateKey (tmpl m n b) := by
  simp only [keyLt, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨i, hi, hBefore, hAt⟩ := h
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · intro j hj
    have hj' : j.val < i := hj
    have he := ent_eq_of_getElem? (hBefore j.val hj')
    simp only [Keys.templateKey, Keys.eval, Pi.toLex_apply, tmpl, he]
  · have hAt' : entryLt (ent a i) (ent b i) = true := by simpa [ent] using hAt
    rcases entryLt_spec hAt' with ⟨u, v, hu, hv, huv⟩ | ⟨u, hu, hv⟩
    · have hun : u < n := ha i u hu
      have hvn : v < n := hb i v hv
      change Keys.templateKey (tmpl m n a) ⟨i, hi⟩ < Keys.templateKey (tmpl m n b) ⟨i, hi⟩
      simp only [Keys.templateKey, Keys.eval, Pi.toLex_apply, tmpl, hu, hv, hun, hvn, dite_true, id]
      exact WithTop.coe_lt_coe.mpr (show (⟨u, hun⟩ : Fin n) < ⟨v, hvn⟩ from huv)
    · have hun : u < n := ha i u hu
      change Keys.templateKey (tmpl m n a) ⟨i, hi⟩ < Keys.templateKey (tmpl m n b) ⟨i, hi⟩
      simp only [Keys.templateKey, Keys.eval, Pi.toLex_apply, tmpl, hu, hv, hun, dite_true, id]
      exact WithTop.coe_lt_top _

theorem templateKey_eq_of_keyEq {m n : Nat} {a b : RawKey}
    (h : keyEq m a b = true) : Keys.templateKey (tmpl m n a) = Keys.templateKey (tmpl m n b) := by
  simp only [keyEq, List.all_eq_true, List.mem_range] at h
  funext i
  have he := ent_eq_of_getElem? (h i.val i.isLt)
  simp only [Keys.templateKey, Keys.eval, Pi.toLex_apply, tmpl, he]

theorem templateKey_le_of_keyLe {m n : Nat} {a b : RawKey} (ha : Below n a) (hb : Below n b)
    (h : keyLe m a b = true) :
    Keys.templateKey (tmpl m n a) ≤ Keys.templateKey (tmpl m n b) := by
  simp only [keyLe, Bool.or_eq_true] at h
  rcases h with h | h
  · exact le_of_eq (templateKey_eq_of_keyEq h)
  · exact le_of_lt (templateKey_lt_of_keyLt ha hb h)

/-! ## Relabelling templates -/

theorem ent_map (K : RawKey) (g : Nat → Nat) (i : Nat) :
    ent (K.map (Option.map g)) i = (ent K i).map g := by
  simp only [ent, List.getElem?_map]
  cases K[i]? with
  | none => rfl
  | some e => rfl

theorem below_map {n n' : Nat} {K : RawKey} (hK : Below n K) (g : Nat → Nat)
    (hg : ∀ v, v < n → g v < n') : Below n' (K.map (Option.map g)) := by
  intro i v h
  rw [ent_map] at h
  cases he : ent K i with
  | none => simp [he] at h
  | some u =>
      simp only [he, Option.map_some, Option.some.injEq] at h
      subst h
      exact hg u (hK i u he)

/-- Relabelling a template along a column map that acts on values by `g`. -/
theorem relabel_tmpl {m n n' : Nat} {K : RawKey} (hK : Below n K) (g : Nat → Nat)
    (mu : Fin n → Fin n') (hmu : ∀ i, (mu i).val = g i.val) :
    Keys.relabel (tmpl m n K) mu = tmpl m n' (K.map (Option.map g)) := by
  funext i
  simp only [Keys.relabel, tmpl, ent_map]
  cases he : ent K i.val with
  | none => rfl
  | some v =>
      have hv : v < n := hK i.val v he
      have hgv : g v < n' := by rw [← hmu ⟨v, hv⟩]; exact (mu ⟨v, hv⟩).isLt
      simp only [hv, dite_true, Option.map, hgv]
      congr 1
      exact Fin.ext (hmu ⟨v, hv⟩)

theorem map_id_key (K : RawKey) : K.map (Option.map (fun v : Nat => v)) = K := by
  have : (Option.map fun v : Nat => v) = id := by funext o; cases o <;> rfl
  rw [this, List.map_id]

/-- Changing the width of a template along a map that keeps column values. -/
theorem relabel_tmpl_id {m n n' : Nat} {K : RawKey} (hK : Below n K)
    (mu : Fin n → Fin n') (hmu : ∀ i, (mu i).val = i.val) :
    Keys.relabel (tmpl m n K) mu = tmpl m n' K := by
  rw [relabel_tmpl hK (fun v => v) mu hmu, map_id_key]

/-- Evaluation does not depend on the width when the labels agree. -/
theorem eval_tmpl_width {m n n' : Nat} {K : RawKey} (hK : Below n K)
    (f : Fin n → L) (g : Fin n' → L) (hle : n ≤ n')
    (hfg : ∀ i : Fin n, g ⟨i.val, lt_of_lt_of_le i.isLt hle⟩ = f i) :
    Keys.eval (tmpl m n K) f = Keys.eval (tmpl m n' K) g := by
  rw [← relabel_tmpl_id (m := m) hK (fun i => ⟨i.val, lt_of_lt_of_le i.isLt hle⟩) (fun _ => rfl)]
  exact (Keys.eval_relabel_of_labels _ _ f g hfg).symm

/-! ## Typed atoms -/

/-- The typed internal atom of a raw atom at width `n`, if its columns fit. -/
def typedAtom (m n : Nat) (a : RawAtom) : Option (Splice.Atom (Label := L) m n) :=
  if h : a.parent < a.child ∧ a.child < n then
    some { key := tmpl m n a.key, parent := ⟨a.parent, by omega⟩, child := ⟨a.child, h.2⟩,
           parent_lt_child := h.1 }
  else none

def typedAtoms (m n : Nat) (A : List RawAtom) : List (Splice.Atom (Label := L) m n) :=
  A.filterMap (typedAtom m n)

/-- The typed top atom (child replaced by the external top) at width `n`. -/
def typedTop (m n : Nat) (a : RawAtom) : Option (Splice.TopAtom (Label := L) m n) :=
  if h : a.parent < n then some { key := tmpl m n a.key, parent := ⟨a.parent, h⟩ } else none

theorem mem_typedAtoms {m n : Nat} {A : List RawAtom} {e : Splice.Atom (Label := L) m n}
    (he : e ∈ typedAtoms m n A) :
    ∃ a ∈ A, e.parent.val = a.parent ∧ e.child.val = a.child ∧ e.key = tmpl m n a.key := by
  simp only [typedAtoms, List.mem_filterMap] at he
  obtain ⟨a, ha, hsome⟩ := he
  unfold typedAtom at hsome
  split at hsome
  · simp only [Option.some.injEq] at hsome
    subst hsome
    exact ⟨a, ha, rfl, rfl, rfl⟩
  · exact absurd hsome (by simp)

theorem typedAtom_mem {m n : Nat} {A : List RawAtom} {a : RawAtom} (ha : a ∈ A)
    (h : a.parent < a.child ∧ a.child < n) :
    ({ key := tmpl m n a.key, parent := ⟨a.parent, by omega⟩, child := ⟨a.child, h.2⟩,
       parent_lt_child := h.1 } : Splice.Atom (Label := L) m n) ∈ typedAtoms m n A := by
  simp only [typedAtoms, List.mem_filterMap]
  exact ⟨a, ha, by simp [typedAtom, h]⟩

theorem mem_typedTops {m n : Nat} {A : List RawAtom} {p : RawAtom → Bool}
    {e : Splice.TopAtom (Label := L) m n}
    (he : e ∈ A.filterMap (fun a => if p a then typedTop m n a else none)) :
    ∃ a ∈ A, p a = true ∧ e.parent.val = a.parent ∧ e.key = tmpl m n a.key := by
  simp only [List.mem_filterMap] at he
  obtain ⟨a, ha, hsome⟩ := he
  by_cases hp : p a = true
  · simp only [hp, if_true, typedTop] at hsome
    split at hsome
    · simp only [Option.some.injEq] at hsome
      subst hsome
      exact ⟨a, ha, hp, rfl, rfl⟩
    · exact absurd hsome (by simp)
  · simp [hp] at hsome

/-! ## Representations -/

/-- A representation of `s` at dimension `D`: strictly increasing labels below `ω₁`
under which every leg atom of `M(s)` holds. -/
structure Rep (D : Nat) (s : List Nat) where
  f : Fin s.length → L
  mono : StrictMono f
  bounded : ∀ i, f i < Reflection.OrdinalSupply.top
  holds : Reflection.InternalHolds (KeyReflection.vectorSyntax (D + 1))
    (KeyReflection.R (D + 1)) (typedAtoms (D + 1) s.length (atomsOf s D)) f

/-- Every sequence has a representation: closed points satisfy every finite atom list. -/
theorem rep_exists (D : Nat) (s : List Nat) : Nonempty (Rep D s) := by
  obtain ⟨beta, hbeta, f, hf, hb, hG, _⟩ :=
    Reflection.OrdinalSupply.initial_finite_graph (KeyReflection.vectorSyntax (Label := L) (D + 1))
      (typedAtoms (D + 1) s.length (atomsOf s D)) []
  exact ⟨⟨f, hf, fun i => lt_trans (hb i) hbeta, hG⟩⟩

/-! ## Facts read from the checks -/

theorem mem_of_getElem? {K : RawKey} {i : Nat} {e : Option Nat} (h : K[i]? = some e) : e ∈ K :=
  List.mem_of_getElem? h

theorem wellFormed_spec {D n : Nat} {a : RawAtom} (h : wellFormed D n a = true) :
    a.parent < a.child ∧ a.child < n ∧ Below (a.parent + 1) a.key := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hpc, hcn⟩, _⟩, hk⟩ := h
  refine ⟨hpc, hcn, ?_⟩
  intro i v hv
  have hmem : some v ∈ a.key := by
    unfold ent at hv
    cases hk' : a.key[i]? with
    | none => simp [hk'] at hv
    | some e =>
        simp only [hk', Option.getD_some] at hv
        subst hv
        exact mem_of_getElem? hk'
  have := hk (some v) hmem
  simp only [decide_eq_true_eq] at this
  omega

theorem Below.mono {n n' : Nat} {K : RawKey} (h : Below n K) (hle : n ≤ n') : Below n' K :=
  fun i v hv => lt_of_lt_of_le (h i v hv) hle

theorem baseOK_spec {D : Nat} {Es : List RawAtom} {e : RawAtom} (h : baseOK D Es e = true) :
    ∃ a ∈ Es, a.parent = e.parent ∧ a.child = e.child ∧ keyLe (D + 1) e.key a.key = true := by
  simp only [baseOK, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨a, ha, ⟨hp, hc⟩, hk⟩ := h
  exact ⟨a, ha, hp, hc, hk⟩

/-- The leg atoms of `s` hold under a representation, in raw form. -/
theorem Rep.holds_raw {D : Nat} {s : List Nat} {M : Mountain} (old : Rep D s)
    (hM : Canonical.build s = .ok M) {a : RawAtom} (ha : a ∈ atoms M D)
    (h : a.parent < a.child ∧ a.child < s.length) :
    KeyReflection.R (D + 1) (Keys.eval (tmpl (D + 1) s.length a.key) old.f)
      (old.f ⟨a.parent, by omega⟩) (old.f ⟨a.child, h.2⟩) := by
  have hmem : a ∈ atomsOf s D := by simp [atomsOf, hM, ha]
  exact old.holds _ (typedAtom_mem hmem h)

/-- A weaker key with the same endpoints holds, at any width that contains both keys. -/
theorem holds_of_keyLe {D n : Nat} {f : Fin n → L} (hf : StrictMono f) {a b : RawKey}
    (ha : Below n a) (hb : Below n b) (hab : keyLe (D + 1) a b = true) {p c : L}
    (h : KeyReflection.R (D + 1) (Keys.eval (tmpl (D + 1) n b) f) p c) :
    KeyReflection.R (D + 1) (Keys.eval (tmpl (D + 1) n a) f) p c :=
  KeyReflection.weaken
    (Keys.eval_le_of_template_le _ _ f hf (templateKey_le_of_keyLe ha hb hab)) h

/-! ## Deletion -/

/-- If `t` has one column less than `s` and every leg atom of `t` is weaker than a leg
atom of `s` with the same endpoints, the restricted labels represent `t`. -/
theorem descent_delete {D : Nat} {s t : List Nat} {M MO : Mountain}
    (hM : Canonical.build s = .ok M) (hMO : Canonical.build t = .ok MO)
    (hlen : t.length + 1 = s.length)
    (hwfS : ∀ a ∈ atoms M D, wellFormed D M.size a = true)
    (hwfO : ∀ a ∈ atoms MO D, wellFormed D MO.size a = true)
    (hbase : ∀ e ∈ atoms MO D, baseOK D (atoms M D) e = true) (old : Rep D s) :
    ∃ new : Rep D t, ∀ i, new.f i < old.f ⟨s.length - 1, by omega⟩ := by
  have hsM : M.size = s.length := Canonical.build_size hM
  have hsO : MO.size = t.length := Canonical.build_size hMO
  let g : Fin t.length → L := fun i => old.f ⟨i.val, by omega⟩
  have hg : StrictMono g := fun i j hij => old.mono (show i.val < j.val from hij)
  refine ⟨⟨g, hg, fun i => old.bounded _, ?_⟩, fun i => old.mono (show i.val < s.length - 1 by omega)⟩
  intro e he
  have heO : e ∈ typedAtoms (D + 1) t.length (atoms MO D) := by simpa [atomsOf, hMO] using he
  obtain ⟨a, ha, hp, hc, hk⟩ := mem_typedAtoms heO
  obtain ⟨hpa, hca, hKa⟩ := wellFormed_spec (hwfO a ha)
  obtain ⟨b, hb, hbp, hbc, hab⟩ := baseOK_spec (hbase a ha)
  obtain ⟨hpb, hcb, hKb⟩ := wellFormed_spec (hwfS b hb)
  have hold := old.holds_raw hM hb ⟨hpb, by omega⟩
  have hBa : Below s.length a.key := hKa.mono (by omega)
  have hBb : Below s.length b.key := hKb.mono (by omega)
  have hw := holds_of_keyLe old.mono hBa hBb hab hold
  have heval : Keys.eval (tmpl (D + 1) t.length a.key) g =
      Keys.eval (tmpl (D + 1) s.length a.key) old.f :=
    eval_tmpl_width (hKa.mono (by omega)) g old.f (by omega) (fun _ => rfl)
  change KeyReflection.R (D + 1) (Keys.eval e.key g) (g e.parent) (g e.child)
  rw [hk, heval]
  have hpe : g e.parent = old.f ⟨b.parent, by omega⟩ := by
    change old.f _ = _; congr 1; exact Fin.ext (by simp [hp, hbp])
  have hce : g e.child = old.f ⟨b.child, by omega⟩ := by
    change old.f _ = _; congr 1; exact Fin.ext (by simp [hc, hbc])
  rw [hpe, hce]
  exact hw

/-! ## Block columns -/

theorem blockSource_val {x y : Nat} (hRoot : y < x) (b : Nat) (i : Fin x) :
    (Splice.blockSource hRoot b i).val = mapColumn y (b * (x - y)) i.val := by
  unfold Splice.blockSource mapColumn
  split <;> simp_all

theorem moved_source_val {x y : Nat} (hRoot : y < x) (b : Nat) (i : Fin x) :
    (Splice.moved (Splice.blockCut hRoot b) (Splice.blockSource hRoot b i)).val =
      mapColumn y ((b + 1) * (x - y)) i.val := by
  have h := congrArg Fin.val (Splice.blockMoved_source hRoot b i)
  simp only [Splice.blockMoved, Fin.val_cast] at h
  rw [h, blockSource_val]

theorem mapColumn_lt {y sh v n : Nat} (hv : v + sh < n) : mapColumn y sh v < n := by
  unfold mapColumn; split <;> omega

theorem atom_ext {m n : Nat} {e e' : Splice.Atom (Label := L) m n} (hk : e.key = e'.key)
    (hp : e.parent = e'.parent) (hc : e.child = e'.child) : e = e' := by
  cases e; cases e'
  simp only at hk hp hc
  subst hk hp hc
  rfl

/-! ## The data of the iterated splice -/

section Splice

variable (D x y : Nat) (hRoot : y < x) (Es EO : List RawAtom) (Kc : RawKey)

/-- The internal reserve: the leg atoms of `s` below the last column. -/
def resF : List (Splice.Atom (Label := L) (D + 1) x) := typedAtoms (D + 1) x Es

/-- The virtual reserve: the leg atoms of `s` into the last column, as top atoms. -/
def resT : List (Splice.TopAtom (Label := L) (D + 1) x) :=
  Es.filterMap fun a => if a.child == x then typedTop (D + 1) x a else none

/-- The control: the key `Kc` from the root column. -/
def resControl : Splice.TopAtom (Label := L) (D + 1) x := ⟨tmpl (D + 1) x Kc, ⟨y, hRoot⟩⟩

/-- The graph after `b` blocks: the leg atoms of `s[n]` below `x + b w`. -/
def resG (b : Nat) : List (Splice.Atom (Label := L) (D + 1) (Splice.blockWidth x y b)) :=
  typedAtoms (D + 1) (Splice.blockWidth x y b) EO

/-- The seam demands of block `b`. -/
def resN (b : Nat) : List (Splice.TopAtom (Label := L) (D + 1) (Splice.blockWidth x y b)) :=
  EO.filterMap fun a =>
    if (a.child == Splice.blockWidth x y b && seamOK D y (x - y) x b Es Kc a) then
      typedTop (D + 1) (Splice.blockWidth x y b) a
    else none

end Splice

section Facts

variable {D x y : Nat} (hRoot : y < x) {Es EO : List RawAtom} {Kc : RawKey}

/-- The classification of every output atom, as checked by `classifiedWith`. -/
def Classified (D x y : Nat) (Es EO : List RawAtom) (Kc : RawKey) : Prop :=
  ∀ e ∈ EO, (if e.child < x then baseOK D Es e
    else reserveOK D y (x - y) x ((e.child - x) / (x - y)) Es e ||
      seamOK D y (x - y) x ((e.child - x) / (x - y)) Es Kc e) = true

theorem seamOK_spec {D cr w x0 b : Nat} {Es : List RawAtom} {Kc : RawKey} {e : RawAtom}
    (h : seamOK D cr w x0 b Es Kc e = true) :
    e.child = x0 + b * w ∧ keyLt (D + 1) e.key (mapKey cr (b * w) Kc) = true ∧
      ∃ a ∈ Es, a.child = x0 ∧ mapColumn cr (b * w) a.parent = e.parent ∧
        keyLe (D + 1) e.key (mapKey cr (b * w) a.key) = true := by
  simp only [seamOK, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨⟨hc, hk⟩, a, ha, ⟨hax, hap⟩, hak⟩ := h
  exact ⟨hc, hk, a, ha, hax, hap, hak⟩

theorem reserveOK_spec {D cr w x0 b : Nat} {Es : List RawAtom} {e : RawAtom}
    (h : reserveOK D cr w x0 b Es e = true) :
    ∃ pp, (e.parent < cr ∧ pp = e.parent ∨ ¬ e.parent < cr ∧ x0 + b * w ≤ e.parent ∧
        pp = cr + (e.parent - (x0 + b * w))) ∧
      ∃ a ∈ Es, a.child < x0 ∧ a.parent = pp ∧ a.child = cr + (e.child - (x0 + b * w)) ∧
        keyLe (D + 1) e.key (mapKey cr ((b + 1) * w) a.key) = true := by
  unfold reserveOK at h
  by_cases h1 : e.parent < cr
  · simp only [h1, if_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    obtain ⟨a, ha, ⟨⟨hax, hap⟩, hac⟩, hak⟩ := h
    exact ⟨e.parent, Or.inl ⟨h1, rfl⟩, a, ha, hax, hap, hac, hak⟩
  · by_cases h2 : x0 + b * w ≤ e.parent
    · simp only [h1, h2, if_true, if_false, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨a, ha, ⟨⟨hax, hap⟩, hac⟩, hak⟩ := h
      exact ⟨_, Or.inr ⟨h1, h2, rfl⟩, a, ha, hax, hap, hac, hak⟩
    · simp [h1, h2] at h

end Facts

/-! ## The initial state -/

/-- The labels of the first `x` columns. -/
def lowLabels {x : Nat} (f : Fin (x + 1) → L) : Fin x → L := fun i => f ⟨i.val, by omega⟩

/-- The labels of the zero-block graph. -/
def zeroLabels {x : Nat} (y : Nat) (f : Fin (x + 1) → L) : Fin (Splice.blockWidth x y 0) → L :=
  fun i => f ⟨i.val, by have := i.isLt; simp only [Splice.blockWidth] at this; omega⟩

/-- The facts about the input that the initial state reads. -/
structure InputFacts (D x : Nat) (Es : List RawAtom) (f : Fin (x + 1) → L) : Prop where
  mono : StrictMono f
  wf : ∀ a ∈ Es, wellFormed D (x + 1) a = true
  hold : ∀ a ∈ Es, ∀ h : a.parent < a.child ∧ a.child < x + 1,
    KeyReflection.R (D + 1) (Keys.eval (tmpl (D + 1) (x + 1) a.key) f)
      (f ⟨a.parent, by omega⟩) (f ⟨a.child, h.2⟩)

theorem InputFacts.low_eval {D x : Nat} {Es : List RawAtom} {f : Fin (x + 1) → L}
    (hI : InputFacts D x Es f) {a : RawAtom} (ha : a ∈ Es) :
    Keys.eval (tmpl (D + 1) x a.key) (lowLabels f) =
      Keys.eval (tmpl (D + 1) (x + 1) a.key) f := by
  obtain ⟨hpa, hca, hKa⟩ := wellFormed_spec (hI.wf a ha)
  exact eval_tmpl_width (hKa.mono (by omega)) (lowLabels f) f (by omega) (fun _ => rfl)

theorem resF_holds {D x : Nat} {Es : List RawAtom} {f : Fin (x + 1) → L}
    (hI : InputFacts D x Es f) :
    Reflection.InternalHolds (KeyReflection.vectorSyntax (D + 1)) (KeyReflection.R (D + 1))
      (resF D x Es) (lowLabels f) := by
  intro e he
  obtain ⟨a, ha, hp, hc, hk⟩ := mem_typedAtoms he
  obtain ⟨hpa, hca, _⟩ := wellFormed_spec (hI.wf a ha)
  have hold := hI.hold a ha ⟨hpa, by omega⟩
  change KeyReflection.R (D + 1) (Keys.eval e.key (lowLabels f)) (lowLabels f e.parent)
    (lowLabels f e.child)
  rw [hk, hI.low_eval ha]
  have hpe : lowLabels f e.parent = f ⟨a.parent, by omega⟩ := by
    simp only [lowLabels]; congr 1; exact Fin.ext (by simp [hp])
  have hce : lowLabels f e.child = f ⟨a.child, by omega⟩ := by
    have := e.child.isLt
    simp only [lowLabels]; congr 1; exact Fin.ext (by simp [hc])
  rw [hpe, hce]
  exact hold

theorem resT_holds {D x : Nat} {Es : List RawAtom} {f : Fin (x + 1) → L}
    (hI : InputFacts D x Es f) :
    Reflection.TopHolds (KeyReflection.vectorSyntax (D + 1)) (KeyReflection.R (D + 1))
      (resT D x Es) (lowLabels f) (f ⟨x, by omega⟩) := by
  intro e he
  obtain ⟨a, ha, hax, hp, hk⟩ := mem_typedTops he
  simp only [beq_iff_eq] at hax
  obtain ⟨hpa, _, _⟩ := wellFormed_spec (hI.wf a ha)
  have hold := hI.hold a ha ⟨hpa, by omega⟩
  change KeyReflection.R (D + 1) (Keys.eval e.key (lowLabels f)) (lowLabels f e.parent) _
  rw [hk, hI.low_eval ha]
  have hpe : lowLabels f e.parent = f ⟨a.parent, by omega⟩ := by
    simp only [lowLabels]; congr 1; exact Fin.ext (by simp [hp])
  have hce : f ⟨x, by omega⟩ = f ⟨a.child, by omega⟩ := by congr 1; exact Fin.ext (by simp [hax])
  rw [hpe, hce]
  exact hold

theorem resControl_holds {D x y : Nat} (hRoot : y < x) {Es : List RawAtom} {Kc : RawKey}
    {f : Fin (x + 1) → L} (hI : InputFacts D x Es f)
    (hctl : ∃ a ∈ Es, a.parent = y ∧ a.child = x ∧ a.key = Kc) :
    KeyReflection.R (D + 1) (Keys.eval (resControl D x y hRoot Kc).key (lowLabels f))
      (lowLabels f (resControl D x y hRoot Kc).parent) (f ⟨x, by omega⟩) := by
  obtain ⟨a, ha, hay, hax, hak⟩ := hctl
  subst hak
  obtain ⟨hpa, _, _⟩ := wellFormed_spec (hI.wf a ha)
  have hold := hI.hold a ha ⟨hpa, by omega⟩
  change KeyReflection.R (D + 1) (Keys.eval (tmpl (D + 1) x a.key) (lowLabels f))
    (lowLabels f ⟨y, hRoot⟩) _
  rw [hI.low_eval ha]
  have hpe : lowLabels f ⟨y, hRoot⟩ = f ⟨a.parent, by omega⟩ := by
    simp only [lowLabels]; congr 1; exact Fin.ext (by simp [hay])
  have hce : f ⟨x, by omega⟩ = f ⟨a.child, by omega⟩ := by congr 1; exact Fin.ext (by simp [hax])
  rw [hpe, hce]
  exact hold

theorem zero_labels_source {x y : Nat} (hRoot : y < x) (f : Fin (x + 1) → L) (i : Fin x) :
    zeroLabels y f (Splice.blockSource hRoot 0 i) = lowLabels f i := by
  simp only [zeroLabels, lowLabels]
  congr 1
  exact Fin.ext (by simp [Splice.blockSource_zero])

theorem initial_state {D x y : Nat} (hRoot : y < x) {Es EO : List RawAtom} {Kc : RawKey}
    {f : Fin (x + 1) → L} (hI : InputFacts D x Es f)
    (hctl : ∃ a ∈ Es, a.parent = y ∧ a.child = x ∧ a.key = Kc)
    (hwfO : ∀ a ∈ EO, a.child < x → Below (a.parent + 1) a.key)
    (hcls : Classified D x y Es EO Kc) :
    Splice.ReservoirState (resG D x y EO 0)
      ((resF D x Es).map (Splice.mapAtom (Splice.blockSource hRoot 0)
        (Splice.blockSource_strictMono hRoot 0)))
      ((resT D x Es).map (Splice.mapTop (Splice.blockSource hRoot 0)))
      (Splice.mapTop (Splice.blockSource hRoot 0) (resControl D x y hRoot Kc))
      (zeroLabels y f) (f ⟨x, by omega⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hI.mono (show i.val < j.val from hij)
  · intro i
    have := i.isLt
    simp only [Splice.blockWidth] at this
    exact hI.mono (show i.val < x by simpa using this)
  · intro e he
    obtain ⟨a, ha, hp, hc, hk⟩ := mem_typedAtoms he
    have hcx : a.child < x := by
      have := e.child.isLt; simp only [Splice.blockWidth] at this; omega
    have hc' := hcls a ha
    simp only [hcx, if_true] at hc'
    obtain ⟨b, hb, hbp, hbc, hab⟩ := baseOK_spec hc'
    obtain ⟨hpb, hcb, hKb⟩ := wellFormed_spec (hI.wf b hb)
    have hpa : a.parent < a.child := by
      have := e.parent_lt_child; rw [Fin.lt_def, hp, hc] at this; exact this
    have hKa : Below (a.parent + 1) a.key := hwfO a ha hcx
    have hold := hI.hold b hb ⟨hpb, hcb⟩
    have hw := holds_of_keyLe hI.mono (hKa.mono (by omega)) (hKb.mono (by omega)) hab hold
    have heval : Keys.eval (tmpl (D + 1) (Splice.blockWidth x y 0) a.key) (zeroLabels y f) =
        Keys.eval (tmpl (D + 1) (x + 1) a.key) f :=
      eval_tmpl_width (hKa.mono (by simp only [Splice.blockWidth]; omega)) _ f
        (by simp only [Splice.blockWidth]; omega) (fun _ => rfl)
    change KeyReflection.R (D + 1) (Keys.eval e.key (zeroLabels y f))
      (zeroLabels y f e.parent) (zeroLabels y f e.child)
    rw [hk, heval]
    have hpe : zeroLabels y f e.parent = f ⟨b.parent, by omega⟩ := by
      simp only [zeroLabels]; congr 1; exact Fin.ext (by simp [hp, hbp])
    have hce : zeroLabels y f e.child = f ⟨b.child, by omega⟩ := by
      simp only [zeroLabels]; congr 1; exact Fin.ext (by simp [hc, hbc])
    rw [hpe, hce]
    exact hw
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact Splice.holds_map _ _ e' (lowLabels f) (zeroLabels y f)
      (zero_labels_source hRoot f) (resF_holds hI e' he')
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact Splice.top_holds_map _ e' (lowLabels f) (zeroLabels y f)
      (zero_labels_source hRoot f) (resT_holds hI e' he')
  · exact Splice.top_holds_map _ _ (lowLabels f) (zeroLabels y f)
      (zero_labels_source hRoot f) (resControl_holds hRoot hI hctl)

/-! ## One block -/

theorem bw_eq (x y b : Nat) : Splice.blockWidth x y b = x + b * (x - y) := rfl

theorem mapKey_eq (cr sh : Nat) (K : RawKey) :
    mapKey cr sh K = K.map (Option.map (mapColumn cr sh)) := rfl

theorem below_mapKey {n n' cr sh : Nat} {K : RawKey} (hK : Below n K)
    (h : ∀ v, v < n → mapColumn cr sh v < n') : Below n' (mapKey cr sh K) := by
  rw [mapKey_eq]; exact below_map hK _ h

/-- The mapped template of an input atom along the block source map. -/
theorem relabel_source {D x y : Nat} (hRoot : y < x) (b : Nat) {K : RawKey} (hK : Below x K) :
    Keys.relabel (tmpl (D + 1) x K) (Splice.blockSource hRoot b) =
      tmpl (D + 1) (Splice.blockWidth x y b) (mapKey y (b * (x - y)) K) := by
  rw [mapKey_eq]
  exact relabel_tmpl hK _ _ (blockSource_val hRoot b)

theorem block_covered {D x y : Nat} (hRoot : y < x) {Es EO : List RawAtom} {Kc : RawKey}
    (hwfS : ∀ a ∈ Es, wellFormed D (x + 1) a = true)
    (hwfO : ∀ a ∈ EO, Below (a.parent + 1) a.key ∧ a.parent < a.child) (b : Nat) :
    Splice.DemandCovered ((resT D x Es).map (Splice.mapTop (Splice.blockSource hRoot b)))
      (resN D x y Es EO Kc b) := by
  intro d hd
  obtain ⟨a, ha, hpa, hp, hk⟩ := mem_typedTops hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hpa
  obtain ⟨hac, hseam⟩ := hpa
  obtain ⟨_, _, c, hc, hcx, hcp, hck⟩ := seamOK_spec hseam
  obtain ⟨hpc, _, hKc⟩ := wellFormed_spec (hwfS c hc)
  have hcpx : c.parent < x := by omega
  let t0 : Splice.TopAtom (Label := L) (D + 1) x := ⟨tmpl (D + 1) x c.key, ⟨c.parent, hcpx⟩⟩
  have ht0 : t0 ∈ resT D x Es := by
    simp only [resT, List.mem_filterMap]
    exact ⟨c, hc, by simp [hcx, typedTop, hcpx, t0]⟩
  refine ⟨Splice.mapTop (Splice.blockSource hRoot b) t0, List.mem_map.mpr ⟨t0, ht0, rfl⟩, ?_, ?_⟩
  · apply Fin.ext
    change d.parent.val = (Splice.blockSource hRoot b ⟨c.parent, hcpx⟩).val
    rw [hp, blockSource_val]
    exact hcp.symm
  · obtain ⟨hKa, hpca⟩ := hwfO a ha
    change Keys.templateKey d.key ≤
      Keys.templateKey (Keys.relabel (tmpl (D + 1) x c.key) (Splice.blockSource hRoot b))
    rw [hk, relabel_source hRoot b (hKc.mono (by omega))]
    apply templateKey_le_of_keyLe (hKa.mono (by omega))
    · apply below_mapKey (hKc.mono (show c.parent + 1 ≤ x by omega))
      intro v hv
      apply mapColumn_lt
      rw [bw_eq]
      have : b * (x - y) ≥ 0 := Nat.zero_le _
      omega
    · exact hck

theorem block_keys {D x y : Nat} (hRoot : y < x) {Es EO : List RawAtom} {Kc : RawKey}
    (hKc : Below x Kc) (hwfO : ∀ a ∈ EO, Below (a.parent + 1) a.key ∧ a.parent < a.child)
    (b : Nat) :
    ∀ d ∈ resN D x y Es EO Kc b, Keys.templateKey d.key <
      Keys.templateKey (Splice.mapTop (Splice.blockSource hRoot b) (resControl D x y hRoot Kc)).key := by
  intro d hd
  obtain ⟨a, ha, hpa, _, hk⟩ := mem_typedTops hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hpa
  obtain ⟨hac, hseam⟩ := hpa
  obtain ⟨_, hlt, _⟩ := seamOK_spec hseam
  obtain ⟨hKa, hpca⟩ := hwfO a ha
  change Keys.templateKey d.key <
    Keys.templateKey (Keys.relabel (tmpl (D + 1) x Kc) (Splice.blockSource hRoot b))
  rw [hk, relabel_source hRoot b hKc]
  apply templateKey_lt_of_keyLt (hKa.mono (by omega))
  · apply below_mapKey hKc
    intro v hv
    apply mapColumn_lt
    rw [bw_eq]
    omega
  · exact hlt

theorem width_cut_val {x y : Nat} (hRoot : y < x) (b : Nat) :
    Splice.width (Splice.blockCut hRoot b) = Splice.blockWidth x y (b + 1) :=
  Splice.width_blockCut hRoot b

theorem mapColumn_below {y sh v : Nat} (h : v < y) : mapColumn y sh v = v := by
  simp [mapColumn, h]

theorem mapColumn_above {y sh v : Nat} (h : ¬ v < y) : mapColumn y sh v = v + sh := by
  simp [mapColumn, h]

theorem block_class {D x y : Nat} (hRoot : y < x) {Es EO : List RawAtom} {Kc : RawKey}
    (hwfS : ∀ a ∈ Es, wellFormed D (x + 1) a = true)
    (hwfO : ∀ a ∈ EO, Below (a.parent + 1) a.key ∧ a.parent < a.child)
    (hcls : Classified D x y Es EO Kc) (b : Nat) :
    Splice.BlockReservoirGeometry hRoot b (resG D x y EO b)
      ((resF D x Es).map (Splice.mapAtom (Splice.blockSource hRoot b)
        (Splice.blockSource_strictMono hRoot b)))
      (resN D x y Es EO Kc b) (resG D x y EO (b + 1)) := by
  intro e he
  obtain ⟨e1, he1, rfl⟩ := List.mem_map.mp he
  obtain ⟨a, ha, hp, hc, hk⟩ := mem_typedAtoms he1
  obtain ⟨hKa, hpca⟩ := hwfO a ha
  have hcW : a.child < Splice.blockWidth x y (b + 1) := hc ▸ e1.child.isLt
  have hW : Splice.width (Splice.blockCut hRoot b) = Splice.blockWidth x y (b + 1) :=
    Splice.width_blockCut hRoot b
  have hmul : (b + 1) * (x - y) = b * (x - y) + (x - y) := Nat.succ_mul b (x - y)
  have hBW : Splice.blockWidth x y (b + 1) = x + b * (x - y) + (x - y) := by
    rw [bw_eq, hmul]; omega
  -- the fields of `e`
  have hepar : (Splice.mapAtom (Fin.cast hW.symm) (Splice.fin_cast_strictMono hW.symm) e1).parent.val
      = a.parent := by
    change (Fin.cast hW.symm e1.parent).val = _; simp [hp]
  have hechild : (Splice.mapAtom (Fin.cast hW.symm) (Splice.fin_cast_strictMono hW.symm) e1).child.val
      = a.child := by
    change (Fin.cast hW.symm e1.child).val = _; simp [hc]
  have hekey : (Splice.mapAtom (Fin.cast hW.symm) (Splice.fin_cast_strictMono hW.symm) e1).key =
      tmpl (D + 1) (Splice.width (Splice.blockCut hRoot b)) a.key := by
    change Keys.relabel e1.key (Fin.cast hW.symm) = _
    rw [hk]
    exact relabel_tmpl_id (hKa.mono (by omega)) _ (fun _ => rfl)
  have hKaW : Below (Splice.width (Splice.blockCut hRoot b)) a.key := hKa.mono (by rw [hW]; omega)
  by_cases hlow : a.child < Splice.blockWidth x y b
  · -- an old atom: it is in the previous graph
    left
    refine ⟨⟨tmpl (D + 1) (Splice.blockWidth x y b) a.key, ⟨a.parent, by omega⟩,
      ⟨a.child, hlow⟩, hpca⟩, typedAtom_mem ha ⟨hpca, hlow⟩, ?_⟩
    apply atom_ext
    · rw [hekey]
      change _ = Keys.relabel (tmpl (D + 1) (Splice.blockWidth x y b) a.key) (Splice.old (Splice.blockCut hRoot b))
      exact (relabel_tmpl_id (hKa.mono (by omega)) (Splice.old (Splice.blockCut hRoot b))
        (fun _ => rfl)).symm
    · exact Fin.ext (by rw [hepar]; rfl)
    · exact Fin.ext (by rw [hechild]; rfl)
  · have hge : Splice.blockWidth x y b ≤ a.child := Nat.le_of_not_lt hlow
    have hge' : x + b * (x - y) ≤ a.child := by rw [bw_eq] at hge; exact hge
    have hxle : x ≤ a.child := le_trans (by rw [bw_eq]; omega) hge
    have hdiv : (a.child - x) / (x - y) = b := by
      apply Nat.div_eq_of_lt_le
      · rw [bw_eq] at hge; omega
      · rw [hBW] at hcW; rw [hmul]; omega
    have hc' := hcls a ha
    simp only [show ¬ a.child < x by omega, if_false, hdiv, Bool.or_eq_true] at hc'
    rcases hc' with hres | hseam
    · -- a reserve atom
      right; left
      obtain ⟨pp, hpp, c, hcE, hcx, hcp, hcc, hck⟩ := reserveOK_spec hres
      obtain ⟨hpc, _, hKc⟩ := wellFormed_spec (hwfS c hcE)
      let c0 : Splice.Atom (Label := L) (D + 1) x :=
        ⟨tmpl (D + 1) x c.key, ⟨c.parent, by omega⟩, ⟨c.child, hcx⟩, hpc⟩
      refine ⟨Splice.mapAtom (Splice.blockSource hRoot b) (Splice.blockSource_strictMono hRoot b) c0,
        List.mem_map.mpr ⟨c0, typedAtom_mem hcE ⟨hpc, hcx⟩, rfl⟩, ?_, ?_, ?_⟩
      · apply Fin.ext
        change _ = (Splice.moved (Splice.blockCut hRoot b) (Splice.blockSource hRoot b ⟨c.parent, by omega⟩)).val
        rw [hepar, moved_source_val, hmul]
        rcases hpp with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · rw [mapColumn_below (show c.parent < y by omega)]; omega
        · rw [mapColumn_above (show ¬ c.parent < y by omega)]; omega
      · apply Fin.ext
        change _ = (Splice.moved (Splice.blockCut hRoot b) (Splice.blockSource hRoot b ⟨c.child, hcx⟩)).val
        rw [hechild, moved_source_val, hmul, mapColumn_above (show ¬ c.child < y by omega)]
        omega
      · rw [hekey]
        change Keys.templateKey (tmpl (D + 1) (Splice.width (Splice.blockCut hRoot b)) a.key) ≤ Keys.templateKey
          (Keys.relabel (Keys.relabel (tmpl (D + 1) x c.key) (Splice.blockSource hRoot b))
            (Splice.moved (Splice.blockCut hRoot b)))
        rw [Splice.relabel_comp]
        rw [relabel_tmpl (hKc.mono (by omega)) (mapColumn y ((b + 1) * (x - y)))
          (Splice.moved (Splice.blockCut hRoot b) ∘ Splice.blockSource hRoot b)
          (fun i => moved_source_val hRoot b i)]
        apply templateKey_le_of_keyLe hKaW
        · rw [← mapKey_eq]
          apply below_mapKey (hKc.mono (show c.parent + 1 ≤ x by omega))
          intro v hv
          apply mapColumn_lt
          rw [hW, hBW, hmul]
          omega
        · exact hck
    · -- a seam atom
      right; right
      obtain ⟨hcB, hlt, _⟩ := seamOK_spec hseam
      have hpB : a.parent < Splice.blockWidth x y b := by rw [bw_eq]; omega
      refine ⟨⟨tmpl (D + 1) (Splice.blockWidth x y b) a.key, ⟨a.parent, hpB⟩⟩, ?_, ?_, ?_, ?_⟩
      · simp only [resN, List.mem_filterMap]
        refine ⟨a, ha, ?_⟩
        have hcond : (a.child == Splice.blockWidth x y b &&
            seamOK D y (x - y) x b Es Kc a) = true := by
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨by rw [bw_eq]; exact hcB, hseam⟩
        simp [hcond, typedTop, hpB]
      · exact Fin.ext (by rw [hepar]; rfl)
      · apply Fin.ext
        rw [hechild]
        change a.child = Splice.blockWidth x y b
        rw [bw_eq]; exact hcB
      · rw [hekey]
        apply le_of_eq
        change _ = Keys.templateKey
          (Keys.relabel (tmpl (D + 1) (Splice.blockWidth x y b) a.key) (Splice.old (Splice.blockCut hRoot b)))
        rw [relabel_tmpl_id (hKa.mono (by rw [bw_eq]; omega))
          (Splice.old (Splice.blockCut hRoot b)) (fun _ => rfl)]

/-! ## Descent through the iterated splice -/

theorem descent_splice {D : Nat} {s t : List Nat} {n : Nat} {M MO : Mountain}
    (hM : Canonical.build s = .ok M) (hMO : Canonical.build t = .ok MO) (ρ : Root)
    (hcr : ρ.cr < ρ.x0) (hx : ρ.x0 + 1 = s.length)
    (hlen : t.length = ρ.x0 + n * (ρ.x0 - ρ.cr))
    (hctl : ∃ a ∈ atoms M D, a.parent = ρ.cr ∧ a.child = ρ.x0 ∧ a.key = ρ.control)
    (hwfS : ∀ a ∈ atoms M D, wellFormed D M.size a = true)
    (hwfO : ∀ a ∈ atoms MO D, wellFormed D MO.size a = true)
    (hcls : Classified D ρ.x0 ρ.cr (atoms M D) (atoms MO D) ρ.control)
    (old : Rep D s) :
    ∃ new : Rep D t, ∀ i, new.f i < old.f ⟨s.length - 1, by omega⟩ := by
  obtain ⟨x, y, Kc⟩ := ρ
  simp only at hcr hx hlen hctl hcls
  have hsM : M.size = s.length := Canonical.build_size hM
  have hsO : MO.size = t.length := Canonical.build_size hMO
  set Es := atoms M D with hEs
  set EO := atoms MO D with hEO
  let f : Fin (x + 1) → L := fun i => old.f ⟨i.val, by omega⟩
  have hI : InputFacts D x Es f := by
    refine ⟨fun i j hij => old.mono (show i.val < j.val from hij), ?_, ?_⟩
    · intro a ha; have := hwfS a ha; rwa [hsM, ← hx] at this
    · intro a ha h
      obtain ⟨_, _, hKa⟩ := wellFormed_spec (hwfS a ha)
      have hold := old.holds_raw hM ha ⟨h.1, by omega⟩
      have heval : Keys.eval (tmpl (D + 1) (x + 1) a.key) f =
          Keys.eval (tmpl (D + 1) s.length a.key) old.f :=
        eval_tmpl_width (hKa.mono (by omega)) f old.f (by omega) (fun _ => rfl)
      rw [heval]
      exact hold
  have hwfO' : ∀ a ∈ EO, Below (a.parent + 1) a.key ∧ a.parent < a.child := by
    intro a ha
    obtain ⟨hpc, _, hK⟩ := wellFormed_spec (hwfO a ha)
    exact ⟨hK, hpc⟩
  have hKc : Below x Kc := by
    obtain ⟨a, ha, hay, _, hak⟩ := hctl
    obtain ⟨_, _, hK⟩ := wellFormed_spec (hwfS a ha)
    rw [← hak]; exact hK.mono (by omega)
  obtain ⟨fn, hstate, _⟩ := Splice.iterated_reservoirs hcr (resG D x y EO) (resF D x Es)
    (resT D x Es) (resControl D x y hcr Kc) (resN D x y Es EO Kc) (zeroLabels y f)
    (f ⟨x, by omega⟩) rfl
    (initial_state hcr hI hctl (fun a ha _ => (hwfO' a ha).1) hcls)
    (fun b => block_covered hcr hI.wf hwfO' b)
    (fun b d hd => block_keys hcr hKc hwfO' b d hd)
    (fun b => block_class hcr hI.wf hwfO' hcls b) n
  have hlenW : t.length = Splice.blockWidth x y n := by rw [bw_eq]; exact hlen
  let g : Fin t.length → L := fun i => fn ⟨i.val, by omega⟩
  have hβ : f ⟨x, by omega⟩ = old.f ⟨s.length - 1, by omega⟩ := by
    change old.f _ = old.f _; congr 1; exact Fin.ext (by simp; omega)
  refine ⟨⟨g, fun i j hij => hstate.strict (show i.val < j.val from hij),
    fun i => lt_trans (hstate.bounded _) (old.bounded _), ?_⟩, fun i => ?_⟩
  · intro e he
    have heO : e ∈ typedAtoms (D + 1) t.length EO := by simpa [atomsOf, hMO] using he
    obtain ⟨a, ha, hp, hc, hk⟩ := mem_typedAtoms heO
    obtain ⟨hpa, _, hKa⟩ := wellFormed_spec (hwfO a ha)
    have hcW : a.child < Splice.blockWidth x y n := by rw [← hlenW, ← hc]; exact e.child.isLt
    have hG := hstate.graph _ (typedAtom_mem (m := D + 1) ha ⟨hpa, hcW⟩)
    have heval : Keys.eval (tmpl (D + 1) t.length a.key) g =
        Keys.eval (tmpl (D + 1) (Splice.blockWidth x y n) a.key) fn :=
      eval_tmpl_width (hKa.mono (by omega)) g fn (by omega) (fun _ => rfl)
    change KeyReflection.R (D + 1) (Keys.eval e.key g) (g e.parent) (g e.child)
    rw [hk, heval]
    have hpe : g e.parent = fn ⟨a.parent, by omega⟩ := by
      change fn _ = _; congr 1; exact Fin.ext (by simp [hp])
    have hce : g e.child = fn ⟨a.child, hcW⟩ := by
      change fn _ = _; congr 1; exact Fin.ext (by simp [hc])
    rw [hpe, hce]
    exact hG
  · rw [← hβ]
    exact hstate.bounded _

/-! ## Descent for one expansion -/

theorem build_of_expand {s t : List Nat} {n : Nat} (h : Official.expand s n = .ok t) :
    ∃ M, Canonical.build s = .ok M := by
  cases hb : Canonical.build s with
  | ok M => exact ⟨M, rfl⟩
  | error e =>
      exfalso
      simp [Official.expand, Official.expandDiagram, hb, Official.liftE, Except.mapError] at h
      cases h

/-- The facts that `classifiedB` checks, for an expansion that succeeds. -/
theorem classified_spec {s t : List Nat} {n D : Nat} {M : Mountain}
    (hM : Canonical.build s = .ok M) (hrun : Official.expand s n = .ok t)
    (hcls : classifiedB s n D = true) :
    ∃ MO, Canonical.build t = .ok MO ∧ degreeAtMost MO D = true ∧
      ((t.length + 1 = s.length ∧ ∀ e ∈ atoms MO D, baseOK D (atoms M D) e = true) ∨
        ∃ ρ : Root, root? M D = some ρ ∧ t.length = ρ.x0 + n * (ρ.x0 - ρ.cr) ∧
          Classified D ρ.x0 ρ.cr (atoms M D) (atoms MO D) ρ.control) := by
  simp only [classifiedB, classifiedWith, hM, hrun] at hcls
  split at hcls
  · exact absurd hcls (by simp)
  · rename_i MO hMO
    simp only [Bool.and_eq_true] at hcls
    obtain ⟨⟨_, hdO⟩, hrest⟩ := hcls
    refine ⟨MO, hMO, hdO, ?_⟩
    cases hroot : root? M D with
    | none =>
        rw [hroot] at hrest
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrest
        exact Or.inl hrest
    | some ρ =>
        rw [hroot] at hrest
        simp only at hrest
        split at hrest
        · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrest
          exact Or.inl hrest
        · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hrest
          obtain ⟨hlen, hall⟩ := hrest
          refine Or.inr ⟨ρ, rfl, hlen, ?_⟩
          intro e he
          have := hall e he
          split at this <;> simp_all

/-- One expansion: a representation of `s` gives a representation of `s[n]` whose
labels are below the last label of `s`, provided the classification holds. -/
theorem descent {D : Nat} {s t : List Nat} {n : Nat} (hs : s ≠ [])
    (hrun : Official.expand s n = .ok t) (hcls : classifiedB s n D = true) (old : Rep D s) :
    ∃ new : Rep D t, ∀ i, new.f i <
      old.f ⟨s.length - 1, by have := List.length_pos_iff.mpr hs; omega⟩ := by
  obtain ⟨M, hM⟩ := build_of_expand hrun
  obtain ⟨MO, hMO, _, hcase⟩ := classified_spec hM hrun hcls
  have hV := Canonical.build_valid_of_success hM
  have hwS := atoms_wellFormed hV D
  have hwO := atoms_wellFormed (Canonical.build_valid_of_success hMO) D
  rcases hcase with ⟨hlen, hbase⟩ | ⟨ρ, hroot, hlen, hcl⟩
  · exact descent_delete hM hMO hlen hwS hwO hbase old
  · obtain ⟨hx, hcr, hctl⟩ := root?_spec hV hroot
    rw [Canonical.build_size hM] at hx
    exact descent_splice hM hMO ρ hcr hx hlen hctl hwS hwO hcl old

/-- The degrees of `M(s)` are at most `D`. -/
def DegreeOK (s : List Nat) (D : Nat) : Prop :=
  ∀ M, Canonical.build s = .ok M → degreeAtMost M D = true

theorem degreeOK_of_classified {s t : List Nat} {n D : Nat}
    (hrun : Official.expand s n = .ok t) (hcls : classifiedB s n D = true) : DegreeOK t D := by
  obtain ⟨M, hM⟩ := build_of_expand hrun
  obtain ⟨MO, hMO, hdO, _⟩ := classified_spec hM hrun hcls
  intro M' hM'
  rw [hMO] at hM'
  cases hM'
  exact hdO

theorem le_foldl_max {L : List Nat} {v acc : Nat} (h : v ∈ L ∨ v ≤ acc) : v ≤ L.foldl max acc := by
  induction L generalizing acc with
  | nil => simpa using h
  | cons a L ih =>
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | h
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inr (le_max_right _ _)
        · exact Or.inl h
      · exact Or.inr (le_trans h (le_max_left _ _))

theorem degreeOK_dimOf (s : List Nat) : DegreeOK s (dimOf s) := by
  intro M hM
  simp only [degreeAtMost, List.all_eq_true, decide_eq_true_eq]
  intro col hcol c hc
  have hle : len c.row - 1 ≤ dimOf s := by
    simp only [dimOf, hM]
    apply le_foldl_max
    left
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨col, hcol, c, hc, rfl⟩
  omega

/-! ## Well-foundedness -/

/-- One step of the official expansion: `t = s[n]` for a nonempty `s`. -/
def Step (t s : List Nat) : Prop := s ≠ [] ∧ ∃ n, Official.expand s n = .ok t

/-- The splice classification for every expansion and every dimension bounding the
degrees of the input (`notes/04-official-design.md` §6). -/
def ClassificationHolds : Prop :=
  ∀ (s : List Nat) (n D : Nat), DegreeOK s D → classifiedB s n D = true

theorem acc_of_rep (h : ClassificationHolds) (D : Nat) (α : L) :
    ∀ s, DegreeOK s D → ∀ rep : Rep D s, (∀ i, rep.f i < α) → Acc Step s := by
  induction α using (wellFounded_lt (α := L)).induction with
  | _ α ih =>
    intro s hdeg rep hbound
    refine Acc.intro s ?_
    rintro t ⟨hs, n, hrun⟩
    have hcls := h s n D hdeg
    obtain ⟨new, hnew⟩ := descent hs hrun hcls rep
    exact ih _ (hbound _) t (degreeOK_of_classified hrun hcls) new hnew

/-- **Conditional well-foundedness.** If the splice classification holds for every
expansion, the official omega-Y expansion is well-founded on all finite sequences. -/
theorem wellFounded_of_classification (h : ClassificationHolds) : WellFounded Step := by
  refine ⟨fun s => ?_⟩
  obtain ⟨rep⟩ := rep_exists (dimOf s) s
  exact acc_of_rep h (dimOf s) Reflection.OrdinalSupply.top s (degreeOK_dimOf s) rep rep.bounded

end OmegaY.Official.Descent

#print axioms OmegaY.Official.Descent.descent
#print axioms OmegaY.Official.Descent.wellFounded_of_classification
