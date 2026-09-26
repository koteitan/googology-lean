/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Witness.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Columns
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Reduction

set_option backward.do.legacy false

/-!
# The canonical witness

Every node of an output column `X ≥ x₀` is emitted by the traced rule with an origin
`o` (`Trace.lean`): a node `o.src` of the input mountain `M(s)`. In the numerical
tests (`reference/official/classification-witness.cjs`), the leg atom of `o.src`
classifies the output leg atom of the node, always:

* as (seam) when `X` is the boundary `B = x₀ + b·w` of its block and the node is not
  from the upper part (then `o.src` is a node of column `x₀`);
* as (reserve) otherwise (then `o.src` is a node of column `cr + (X - B)`).

`WitnessOK` states this for one node, `WitnessHolds` for every node of every splice
expansion, and `spliceAtomsClassified_of_witness` shows that it gives
`SpliceAtomsClassified`, provided the result of `expandDiagram` is the canonical
mountain of the output (`Reconstructs`, item 1 of `notes/04-official-design.md` §6 in
its strong form).
-/

namespace OmegaY.Official.Classification

open Canonical Reserve Official Descent

def Origin.isUpper : Origin → Bool
  | .upper _ => true
  | _ => false

/-- The block `b = ⌊(X - x₀)/w⌋` of an output column. -/
def blockOf (x0 w X : Nat) : Nat := (X - x0) / w

/-- The classification of the output leg atom `e` of a node of column `X` with origin
`o` by the input leg atom `a` of `o.src`. -/
def WitnessOK (D cr w x0 : Nat) (Kc : RawKey) (X : Nat) (o : Origin) (e a : RawAtom) : Prop :=
  if X = x0 + blockOf x0 w X * w ∧ o.isUpper = false then
    a.child = x0 ∧ mapColumn cr (blockOf x0 w X * w) a.parent = e.parent ∧
      keyLe (D + 1) e.key (mapKey cr (blockOf x0 w X * w) a.key) = true ∧
      keyLt (D + 1) e.key (mapKey cr (blockOf x0 w X * w) Kc) = true
  else
    a.child < x0 ∧ a.child = cr + (X - (x0 + blockOf x0 w X * w)) ∧
      ((e.parent < cr ∧ a.parent = e.parent) ∨
        (¬ e.parent < cr ∧ x0 + blockOf x0 w X * w ≤ e.parent ∧
          a.parent = cr + (e.parent - (x0 + blockOf x0 w X * w)))) ∧
      keyLe (D + 1) e.key (mapKey cr ((blockOf x0 w X + 1) * w) a.key) = true

theorem classified_of_witness {D cr w x0 : Nat} {Kc : RawKey} {Es : List RawAtom}
    {o : Origin} {e a : RawAtom} (ha : a ∈ Es)
    (h : WitnessOK D cr w x0 Kc e.child o e a) :
    (reserveOK D cr w x0 ((e.child - x0) / w) Es e ||
      seamOK D cr w x0 ((e.child - x0) / w) Es Kc e) = true := by
  unfold WitnessOK blockOf at h
  split at h
  · rename_i hX
    obtain ⟨hac, hap, hkey, hctl⟩ := h
    simp only [Bool.or_eq_true]
    right
    simp only [seamOK, Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
    exact ⟨⟨hX.1, hctl⟩, a, ha, ⟨hac, hap⟩, hkey⟩
  · obtain ⟨hlt, hac, hpar, hkey⟩ := h
    simp only [Bool.or_eq_true]
    left
    unfold reserveOK
    rcases hpar with ⟨hp, hap⟩ | ⟨hp, hB, hap⟩
    · simp only [hp, if_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq]
      exact ⟨a, ha, ⟨⟨hlt, hap⟩, hac⟩, hkey⟩
    · simp only [hp, if_false, hB, if_true, List.any_eq_true, Bool.and_eq_true,
        decide_eq_true_eq, beq_iff_eq]
      exact ⟨a, ha, ⟨⟨hlt, hap⟩, hac⟩, hkey⟩

/-- Item 1 of `notes/04-official-design.md` §6 in the strong form: in the splice
branch, the mountain built by `expandDiagram` is the canonical mountain of the output
(numerically: check (a) of `reference/official/check.cjs`). -/
def Reconstructs : Prop :=
  ∀ s n D M out ρ R, SpliceCase s n D M out ρ → Official.expandDiagram s n = .ok R →
    Canonical.build out = .ok R

theorem outputBuilds_of_reconstructs (h : Reconstructs) : OutputBuilds := by
  intro s n D M out ρ hc
  obtain ⟨R, hR, _⟩ := expand_spec hc.run
  exact ⟨R, h s n D M out ρ R hc hR⟩

/-- Every node of every copied column is classified by the leg atom of its origin. -/
def WitnessHolds : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ X x i (_ : ρ.x0 ≤ X) (hXR : X < R.size), X = x + (ρ.x0 - ρ.cr) * i → i < n + 1 →
      x ∈ blockColumns ρ.cr ρ.x0 n i →
      copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X] →
      ∀ es, emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es →
      ∀ k (hk : k < es.length) e, legAtom? R D ⟨X, k + 1⟩ = some e →
        ∃ a ∈ atoms M D, legAtom? M D es[k].2.src = some a ∧
          WitnessOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ρ.control X es[k].2 e a

/-- The splice data of `expandDiagram` for a `SpliceCase`. -/
theorem spliceCase_data {s out : List Nat} {n D : Nat} {M : Mountain} {ρ : Root}
    (hc : SpliceCase s n D M out ρ) {R : Mountain} (hR : Official.expandDiagram s n = .ok R) :
    ∃ (col : Column) (t : Cell), M[M.size - 1]? = some col ∧ col.back? = some t ∧
      ρ.x0 = M.size - 1 ∧ ρ.cr < ρ.x0 ∧
      ColumnsInv M n ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (official t.row) R := by
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hR
  rw [hc.build] at hM'
  cases hM'
  have hV := build_valid_of_success hc.build
  have hsz := build_size hc.build
  have hx := (root?_spec hV hc.root).1
  rcases hcases with ⟨he, _⟩ | ⟨col, t, hcol, ht, hbr⟩
  · have : s = [] := List.isEmpty_iff.mp he
    subst this
    simp only [List.length_nil] at hsz
    omega
  · rcases hbr with ⟨hdel, _⟩ | ⟨hsp, root, htl, _, _, _⟩
    · rcases hdel with h0 | h0
      · have hr := hc.root
        rw [root?_none_of_official_zero hV D hcol ht h0] at hr
        cases hr
      · exact absurd h0 hc.copies
    · obtain ⟨ρ', hr', hx0, hcr'⟩ :=
        root?_of_official_ne_zero hV D hcol ht (fun h0 => hsp (Or.inl h0)) htl
      have hρ : ρ' = ρ := Option.some.inj (hr'.symm.trans hc.root)
      subst hρ
      obtain ⟨hlt, hinv⟩ := expandDiagram_splice hR hc.build hcol ht hsp htl
      rw [← hx0, ← hcr'] at hinv
      exact ⟨col, t, hcol, ht, hx0, by omega, hinv⟩

/-- **The witness reduction.** -/
theorem spliceAtomsClassified_of_witness (hrec : Reconstructs) (hW : WitnessHolds) :
    SpliceAtomsClassified := by
  intro s n D M out ρ MO hc hdeg hMO e he hge
  obtain ⟨R, hR, _⟩ := expand_spec hc.run
  have hRb := hrec s n D M out ρ R hc hR
  have hMOR : MO = R := Except.ok.inj (hMO.symm.trans hRb)
  subst hMOR
  obtain ⟨col, t, hcol, ht, _, _, hinv⟩ := spliceCase_data hc hR
  obtain ⟨_, _, hall⟩ := hinv
  obtain ⟨c, idx, ccol, hcsz, _, hccol, hidx, hidx0, hleg⟩ := mem_atoms_iff.mp he
  have hec : e.child = c := (legAtom?_spec hleg).1
  obtain ⟨i, x, hi, hx, hXeq, hcopy⟩ := hall c hcsz (by omega)
  obtain ⟨es, hes, hasm⟩ := copyColumn_emitsT hcopy
  obtain ⟨hsize, _⟩ := assemble_spec hasm
  obtain ⟨_, hccolEq⟩ := column_of_getElem? hccol
  obtain ⟨k, rfl⟩ : ∃ k, idx = k + 1 := ⟨idx - 1, by omega⟩
  have hk : k < es.length := by
    simp only [List.length_map] at hsize
    have hs2 := congrArg Array.size hccolEq
    omega
  obtain ⟨a, ha, _, hok⟩ := hW s n D M out ρ MO col t hc hdeg hR hRb hcol ht c x i
    (by omega) hcsz hXeq hi hx hcopy es hes k hk e hleg
  rw [← hec] at hok
  exact classified_of_witness ha hok

/-- Well-foundedness from the reconstruction, the degrees, the length and the canonical
witness. -/
theorem wellFounded_of_witness (h1 : Reconstructs) (h2 : DegreePreserved) (h3 : LengthOK)
    (h4 : WitnessHolds) : WellFounded Step :=
  wellFounded_of_splice (outputBuilds_of_reconstructs h1) h2 h3
    (spliceAtomsClassified_of_witness h1 h4)

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.spliceAtomsClassified_of_witness
#print axioms OmegaY.Official.Classification.wellFounded_of_witness
