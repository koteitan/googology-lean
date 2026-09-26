/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ChainSplit.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.FirstEmit

set_option backward.do.legacy false

/-!
# The chain condition split at the column of the candidate

`ChainHolds` (`Search.lean`) asks, for every real node `u` of a new column with a node
`u⁺` above it and stored parent `p = π(u⁺)`, that `p` is reached from the candidate
`Q u` by a chain of stored parents whose nodes before `p` have value at least `v(u)`.

This file removes the values from every link but the last one, and settles the case where
the candidate `Q u` lies in the column of `p`:

* `RawChain`: a chain of stored parents with no value condition. In a mountain with the
  value sums, values decrease strictly along it (`RawChain.value_le`), so the value
  condition of `ChainOK` only has to be checked at the last node `c` before `p`
  (`chainOK_of_rawChain`).
* `Q_eq_of_same_column`: if `Q u` is in the column of `p`, `p` is not above `u`
  (`row p ≤ row u`), and `p` is the highest node of its column up to the row of `u`,
  then `Q u = p`.
* In a new column of the official expansion, the stored parent `p` of `u⁺` is the answer
  of `Expansion.below`: the highest node of its column strictly below the row of `u⁺`
  (`rawParent_max`).

So `ChainHolds` follows from two statements (`chainHolds_of_split`):

* `ParentBelowHolds`: in a new column, `row π(u⁺) ≤ row u`;
* `CrossChainHolds`: in a new column, when `Q u` is not in the column of `p = π(u⁺)`, some
  chain of stored parents runs from `Q u` to a node `c` with `π(c⁺) = p` and
  `v(c) ≥ v(u)`.

In the numerical tests, `Q u` is in the column of `p` for 94% of the new nodes, and then
`Q u = p` always.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-! ## Chains of stored parents without values -/

/-- A chain of stored parents from `a` to `p`. -/
inductive RawChain (F : Frame) : F.Node → F.Node → Prop
  | here (p : F.Node) : RawChain F p p
  | step {a b p : F.Node} (hraw : F.rawParent a = some b) (rest : RawChain F b p) :
      RawChain F a p

theorem RawChain.snoc {F : Frame} {a c p : F.Node} (h : RawChain F a c)
    (hraw : F.rawParent c = some p) : RawChain F a p := by
  induction h with
  | here c => exact .step hraw (.here p)
  | step hab _ ih => exact .step hab (ih hraw)

/-- One stored-parent step in a valid mountain with the value sums: the parent is real and
has a smaller value. -/
theorem rawParent_step {R : Mountain} (hV : MountainValid R) (hS : MountainSums R)
    {a b : (Frame.ofMountain R).Node} (ha : Real a)
    (h : (Frame.ofMountain R).rawParent a = some b) :
    Real b ∧ (Frame.ofMountain R).value b < (Frame.ofMountain R).value a := by
  obtain ⟨upper, hUpper, _⟩ := rawParent_spec h
  obtain ⟨p', hp', _, hpos, hlt, _, _⟩ := hS.rawParent_upper hV ha hUpper
  have he : p' = b := Option.some.inj (hp'.symm.trans h)
  subst he
  exact ⟨real_of_value_pos hV.toOrdered hpos, hlt⟩

/-- Values do not increase along a chain of stored parents. -/
theorem RawChain.value_le {R : Mountain} (hV : MountainValid R) (hS : MountainSums R)
    {a c : (Frame.ofMountain R).Node} (h : RawChain (Frame.ofMountain R) a c) :
    Real a → Real c ∧ (Frame.ofMountain R).value c ≤ (Frame.ofMountain R).value a := by
  induction h with
  | here c => exact fun ha => ⟨ha, le_rfl⟩
  | step hraw _ ih =>
    intro ha
    obtain ⟨hb, hlt⟩ := rawParent_step hV hS ha hraw
    obtain ⟨hc, hle⟩ := ih hb
    exact ⟨hc, le_trans hle hlt.le⟩

/-- A chain of stored parents whose last node before `p` has value at least `th`
satisfies the value condition of `ChainTo` at every node. -/
theorem RawChain.chainTo {R : Mountain} (hV : MountainValid R) (hS : MountainSums R)
    {a c : (Frame.ofMountain R).Node} (h : RawChain (Frame.ofMountain R) a c) :
    Real a → ∀ {th : Nat} {p : (Frame.ofMountain R).Node},
      th ≤ (Frame.ofMountain R).value c → (Frame.ofMountain R).rawParent c = some p →
      ChainTo (Frame.ofMountain R) th a p := by
  induction h with
  | here c =>
    intro _ th p hth hp
    exact .step hth hp (.here p)
  | step hraw rest ih =>
    intro ha th p hth hp
    obtain ⟨hb, _⟩ := rawParent_step hV hS ha hraw
    have hle := (rest.value_le hV hS hb).2
    have hlt := (rawParent_step hV hS ha hraw).2
    exact .step (by omega) hraw (ih hb hth hp)

/-- **The chain condition from a chain of stored parents and one value inequality.** -/
theorem chainOK_of_rawChain {R : Mountain} (hV : MountainValid R) (hS : MountainSums R)
    {u p q c : (Frame.ofMountain R).Node} (hu : Real u)
    (hq : (Frame.ofMountain R).Q u = some q) (hc : RawChain (Frame.ofMountain R) q c)
    (hcp : (Frame.ofMountain R).rawParent c = some p)
    (hv : (Frame.ofMountain R).value u ≤ (Frame.ofMountain R).value c) :
    ChainOK (Frame.ofMountain R) u p :=
  ⟨q, hq, hc.chainTo hV hS (Q_real hV.toOrdered hu hq) hv hcp⟩

/-! ## The candidate in the column of the parent -/

/-- **`Q u = p`** when `Q u` is in the column of `p`, `p` is not above `u`, and `p` is the
highest node of its column whose row is at most the row of `u`. -/
theorem Q_eq_of_same_column {F : Frame} (hF : F.Ordered) {u q p : F.Node}
    (hq : F.Q u = some q) (hcol : q.1 = p.1) (hpu : F.height p ≤ F.height u)
    (hmax : ∀ z : F.Node, z.1 = p.1 → F.height z ≤ F.height u → z.2.val ≤ p.2.val) :
    q = p := by
  obtain ⟨qc, qi⟩ := q
  obtain ⟨pc, pi⟩ := p
  simp only at hcol
  subst hcol
  have hqp : qi.val ≤ pi.val := hmax ⟨qc, qi⟩ rfl (Q_height_le hF hq)
  have hpq : pi.val ≤ qi.val := by
    by_contra hlt
    have hlen : qi.val + 1 < F.length qc := by have := pi.isLt; omega
    let v : F.Node := ⟨qc, ⟨qi.val + 1, hlen⟩⟩
    have hv : F.upper ⟨qc, qi⟩ = some v := by simp [upper, hlen, v]
    have hgt := Q_upper_gt hF hq hv
    have hvp : F.height v ≤ F.height ⟨qc, pi⟩ :=
      (hF.rows_strict qc).monotone (show (⟨qi.val + 1, hlen⟩ : Fin _) ≤ pi by
        change qi.val + 1 ≤ pi.val
        omega)
    exact lt_irrefl _ (lt_of_lt_of_le hgt (hvp.trans hpu))
  have he : qi = pi := Fin.ext (le_antisymm hqp hpq)
  subst he
  rfl

/-! ## Stored parents in the new columns -/

/-- A cell of a new column above the bottom row has the answer of `Expansion.below` as its
left endpoint. -/
theorem newCol_left_below {m : Mountain} {col : Column} (hN : NewCol m col) {index : Nat}
    {cell : Cell} (h : col[index]? = some cell) (hrow : (1 : Row) < cell.row) :
    ∃ ref q nodes, cell.left = some ref ∧ m[q]? = some nodes ∧
      Expansion.below m q cell.row = .ok ref := by
  obtain ⟨cells, hfin, _, _, hlegs⟩ := hN
  obtain ⟨hShape, _⟩ := Expansion.finish_success_spec hfin
  have hShape' : ColumnShape (finishSort (phantom :: cells)) col := hShape
  obtain ⟨orig, horig, hsame⟩ := hShape'.getElem h
  have hmem : orig ∈ phantom :: cells :=
    (finishSort_perm _).mem_iff.mp (List.mem_of_getElem? horig)
  have hrow' : orig.row = cell.row := hsame.1
  rcases List.mem_cons.mp hmem with he | hc
  · exfalso
    rw [← hrow', he] at hrow
    exact absurd hrow (not_lt.mpr (Row.zero_le 1))
  · obtain ⟨ref, hleft, hcase⟩ := hlegs orig hc
    rcases hcase with ⟨h1, _⟩ | ⟨q, nodes, hq, hb⟩
    · exfalso
      rw [← hrow', h1] at hrow
      exact lt_irrefl _ hrow
    · refine ⟨ref, q, nodes, ?_, hq, ?_⟩
      · rw [← hsame.2]
        exact hleft
      · rw [← hrow']
        exact hb

/-- The basic facts of a run output (`Basic`), with the size of the source. -/
theorem run_basic {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) :
    ∃ M, Canonical.build s = .ok M ∧ M.size = s.length ∧ Inv M (M.size - 1) R ∧ Basic R := by
  obtain ⟨M, hM, _⟩ := Reconstruction.expandDiagram_cases hrun
  have hI := expandDiagram_inv hM n R hrun
  have hMs := Canonical.build_size hM
  exact ⟨M, hM, hMs, hI,
    basic_of_inv hM hI (fun c hc hx => bottomHolds s n R hrun c hc (by omega))⟩

/-- **The stored parent of a new node is the highest node of its column below the row of
the node above.** -/
theorem rawParent_max {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {u p : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ u.1.val) (hu : Real u)
    (hraw : (Frame.ofMountain R).rawParent u = some p) :
    ∃ up, (Frame.ofMountain R).upper u = some up ∧
      ∀ z : (Frame.ofMountain R).Node, z.1 = p.1 →
        (Frame.ofMountain R).height z < (Frame.ofMountain R).height up → z.2.val ≤ p.2.val := by
  obtain ⟨M, _, hMs, hI, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨up, hUp, hLeft⟩ := rawParent_spec hraw
  refine ⟨up, hUp, ?_⟩
  obtain ⟨hc1, hc2⟩ := upper_spec hUp
  obtain ⟨uc, ui⟩ := u
  obtain ⟨vc, vi⟩ := up
  simp only at hc1 hc2 hx
  subst hc1
  obtain ⟨_, hN⟩ := hI.2.2 vc.val vc.isLt (by omega)
  have hcell : R[vc.val][vi.val]? = some ((Frame.ofMountain R).cell ⟨vc, vi⟩) :=
    Array.getElem?_eq_getElem vi.isLt
  have hrow : (1 : Row) < ((Frame.ofMountain R).cell ⟨vc, vi⟩).row := by
    have h1 := one_le_height hF hu
    have h2 : (Frame.ofMountain R).height ⟨vc, ui⟩ < (Frame.ofMountain R).height ⟨vc, vi⟩ :=
      hF.rows_strict vc (show ui < vi by change ui.val < vi.val; omega)
    exact lt_of_le_of_lt h1 h2
  obtain ⟨ref, q, nodes, hl, hq, hb⟩ := newCol_left_below hN hcell hrow
  have href : ref = Frame.ref p := Option.some.inj (hl.symm.trans hLeft)
  subst href
  obtain ⟨hqc, _⟩ := below_result hq hb
  have hq' := Array.getElem?_eq_some_iff.mp hq
  obtain ⟨hqs, hqn⟩ := hq'
  have hqX : q < vc.val := by simp at hqs; omega
  have hqR : q < R.size := by have := vc.isLt; change vc.val < R.size at this; omega
  have hnodes : nodes = R[q] := by
    rw [← hqn]
    simp
  intro z hz hzrow
  have hzc : z.1.val = q := by
    rw [hz]
    exact hqc
  have hzcell : nodes[z.2.val]? = some ((Frame.ofMountain R).cell z) := by
    rw [hnodes]
    obtain ⟨zc, zi⟩ := z
    simp only at hzc
    subst hzc
    exact Array.getElem?_eq_getElem zi.isLt
  exact below_max_index hq hb hzcell hzrow

/-! ## The split -/

/-- **Open.** In a new column, the stored parent of the node above `u` is not above `u`. -/
def ParentBelowHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ u p : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p →
      (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u

/-- **Open.** In a new column, when the candidate `Q u` is not in the column of the stored
parent `p` of the node above `u`, a chain of stored parents runs from `Q u` to a node `c`
of value at least `v(u)` whose stored parent is `p`. -/
def CrossChainHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ u p q : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 →
      ∃ c, RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).rawParent c = some p ∧
        (Frame.ofMountain R).value u ≤ (Frame.ofMountain R).value c

/-- The candidate of a real node of a new column exists. -/
theorem Q_exists_new {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {u : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ u.1.val) (hu : Real u) : ∃ q, (Frame.ofMountain R).Q u = some q := by
  obtain ⟨M, _, hMs, hI, hB⟩ := run_basic hrun
  obtain ⟨hpos, _⟩ := hI.2.2 u.1.val u.1.isLt (by omega)
  refine Q_exists_of_left hB.valid.toOrdered ?_
  have hCV := hB.valid u.1.val u.1.isLt
  exact hCV.stored_exists u.2.val _ (Array.getElem?_eq_getElem u.2.isLt) hu hpos

/-- **`ChainHolds` from `ParentBelowHolds` and `CrossChainHolds`.** When the candidate is in
the column of the parent, it is the parent. -/
theorem chainHolds_of_split (hPB : ParentBelowHolds) (hX : CrossChainHolds) : ChainHolds := by
  intro s n R hrun u p hx hu hraw
  obtain ⟨M, _, _, _, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨q, hq⟩ := Q_exists_new hrun hx hu
  by_cases hcol : q.1 = p.1
  · obtain ⟨up, hUp, hmax⟩ := rawParent_max hrun hx hu hraw
    have hlt : (Frame.ofMountain R).height u < (Frame.ofMountain R).height up := by
      obtain ⟨hc1, hc2⟩ := upper_spec hUp
      obtain ⟨uc, ui⟩ := u
      obtain ⟨vc, vi⟩ := up
      simp only at hc1 hc2
      subst hc1
      exact hF.rows_strict _ (show ui < vi by change ui.val < vi.val; omega)
    have he := Q_eq_of_same_column hF hq hcol (hPB s n R hrun u p hx hu hraw)
      (fun z hz hzu => hmax z hz (lt_of_le_of_lt hzu hlt))
    subst he
    exact ⟨q, hq, .here q⟩
  · obtain ⟨c, hc, hcp, hv⟩ := hX s n R hrun u p q hx hu hraw hq hcol
    exact chainOK_of_rawChain hB.valid hB.sums hu hq hc hcp hv

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.chainHolds_of_split
