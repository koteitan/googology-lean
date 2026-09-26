/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerTree.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawSeam

set_option backward.do.legacy false

/-!
# The item tree of a lower part

The lower part of a new column is produced by the first items `L_{k,j}` and their
descendants (`Official.runItem`, `Official.childItems`). This file names the items of that
tree and proves what their outputs are, for any column of a successful run:

* `Desc ctx d A d' B`: the item `B` (level `d'`) is reached from `A` (level `d`) through
  successful calls of `childItems`; `InTree ctx τ d B`: `B` is reached from a first item.
* `desc_facts`: along `Desc`, the hypotheses `ItemOK` are kept, the target region of `B`
  lies in that of `A`, the run of `B` succeeds when that of `A` does, its output is part of
  the output of `A`, and **every node of the output of `A` whose row is in the target region
  of `B` is in the output of `B`**.
* `inTree_facts`: the same for the whole lower part `vs.flatten`.
* `run_coeff_lt`: the rows emitted by an item of level `d + 2` have height (coefficient
  `d`) below the number of its children.
-/

namespace OmegaY.Official.Recon.JumpLawLower

open Canonical Expansion Dimension RowLaw JumpLaw

/-! ## The tree -/

/-- `B` (level `d'`) is reached from `A` (level `d`) through successful `childItems`. -/
inductive Desc (ctx : Context) : Nat → Item → Nat → Item → Prop
  | refl (d : Nat) (A : Item) : Desc ctx d A d A
  | step {d : Nat} {A : Item} {cs : List Item} {c : Item} {d' : Nat} {B : Item} :
      childItems ctx (d + 2) A = .ok cs → c ∈ cs → Desc ctx (d + 1) c d' B →
      Desc ctx (d + 2) A d' B

/-- `B` (level `d`) is an item of the lower tree of the column. -/
def InTree (ctx : Context) (τ : Row) (d : Nat) (B : Item) : Prop :=
  ∃ F ∈ lowerItems τ, Desc ctx F.1 F.2 d B

/-! ## One step of the recursion -/

/-- The run of an item of level `d + 2` is the concatenation of the runs of its children. -/
theorem runItem_children {ctx : Context} {d : Nat} {A : Item} {L : List Emit}
    (h : runItem ctx (d + 2) A = .ok L) :
    ∃ cs outs, childItems ctx (d + 2) A = .ok cs ∧
      List.Forall₂ (fun c L' => runItem ctx (d + 1) c = .ok L') cs outs ∧ L = outs.flatten := by
  rw [runItem] at h
  obtain ⟨cs, hcs, h⟩ := Reconstruction.bind_ok h
  obtain ⟨outs, houts, h⟩ := Reconstruction.bind_ok h
  refine ⟨cs, outs, hcs, ok_mapM₂ (fun c L' => runItem ctx (d + 1) c = .ok L') cs _
    (fun c _ => RowLaw.ok_eq _) outs houts, ?_⟩
  exact (Except.ok.inj h).symm

/-- The children of an item satisfy the item hypotheses. -/
theorem child_itemOK {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item}
    (hA : ItemOK ctx (official t.row) (d + 2) A) {cs : List Item}
    (hcs : childItems ctx (d + 2) A = .ok cs) :
    ∀ j (hj : j < cs.length), ItemOK ctx (official t.row) (d + 1) cs[j] ∧
      cs[j].target = slot (d + 2) A.target j := by
  obtain ⟨n, F, σ, rfl, htgt, hsrc, _, _, hoff⟩ := childSpec hctx hA cs hcs
  intro j hj
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range]
  refine ⟨⟨?_, ?_, hoff j hj⟩, htgt j⟩
  · rw [htgt j]
    exact slot_zeroBelow d A.target j
  · intro r hr
    rw [hsrc j] at hr
    exact hA.below r (inRegion_of_slot hr)

/-! ## Descendants -/

/-- **What a descendant inherits.** -/
theorem desc_facts {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) :
    1 ≤ d → ItemOK ctx (official t.row) d A →
      1 ≤ d' ∧ d' ≤ d ∧ ItemOK ctx (official t.row) d' B ∧
      (∀ r, inRegion d' B.target r = true → inRegion d A.target r = true) ∧
      ∀ L, runItem ctx d A = .ok L → ∃ LB, runItem ctx d' B = .ok LB ∧
        (∀ em ∈ LB, em ∈ L) ∧ ∀ em ∈ L, inRegion d' B.target em.row = true → em ∈ LB := by
  induction hD with
  | refl d A =>
    intro hd hA
    exact ⟨hd, le_rfl, hA, fun _ h => h, fun L hL => ⟨L, hL, fun _ h => h, fun _ h _ => h⟩⟩
  | @step d A cs c d' B hcs hc hD ih =>
    intro _ hA
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨hcOK, hctgt⟩ := child_itemOK hctx hA hcs j hj
    obtain ⟨hd1, hdd, hBOK, hreg, hrun⟩ := ih (by omega) hcOK
    refine ⟨hd1, by omega, hBOK, fun r hr => ?_, ?_⟩
    · have := hreg r hr
      rw [hctgt] at this
      exact inRegion_of_slot this
    · intro L hL
      obtain ⟨cs', outs, hcs', hF, rfl⟩ := runItem_children hL
      rw [hcs] at hcs'
      obtain rfl := Except.ok.inj hcs'
      obtain ⟨hlen, hget⟩ := forall₂_getElem hF
      have hj' : j < outs.length := by omega
      obtain ⟨LB, hLB, hsub, hback⟩ := hrun outs[j] (hget j hj hj')
      refine ⟨LB, hLB, fun em hem => List.mem_flatten.mpr ⟨outs[j], List.getElem_mem hj',
        hsub em hem⟩, ?_⟩
      intro em hem hin
      obtain ⟨L', hL', hemL'⟩ := List.mem_flatten.mp hem
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
      have hm' : m < cs.length := by omega
      obtain ⟨hmOK, hmtgt⟩ := child_itemOK hctx hA hcs m hm'
      have hgood := runItem_good hctx (d + 1) (by omega) cs[m] hmOK outs[m] (hget m hm' hm)
      have hinm := hgood.1.2.1 em hemL'
      rw [hmtgt] at hinm
      have hinj := hreg em.row hin
      rw [hctgt] at hinj
      have e1 := (inRegion_slot_iff.mp hinm).2
      have e2 := (inRegion_slot_iff.mp hinj).2
      have hmj : m = j := by omega
      subst hmj
      exact hback em hemL' hin

/-- **The items of the lower tree.** -/
theorem inTree_facts {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) {d : Nat} {B : Item}
    (hB : InTree ctx (official t.row) d B) :
    1 ≤ d ∧ ItemOK ctx (official t.row) d B ∧ ∃ LB, runItem ctx d B = .ok LB ∧
      (∀ em ∈ LB, em ∈ vs.flatten) ∧
      ∀ em ∈ vs.flatten, inRegion d B.target em.row = true → em ∈ LB := by
  obtain ⟨F, hF, hD⟩ := hB
  obtain ⟨hFOK, hst, hF1, _⟩ := lower_itemOK (ctx := ctx) hF
  obtain ⟨hd1, _, hBOK, hreg, hrun⟩ := desc_facts hctx hD hF1 hFOK
  obtain ⟨LF, hLF, hLFsub⟩ := first_output hvs hF
  obtain ⟨LB, hLB, hsub, hback⟩ := hrun LF hLF
  refine ⟨hd1, hBOK, LB, hLB, fun em hem => hLFsub em (hsub em hem), ?_⟩
  intro em hem hin
  have hinF : inRegion F.1 F.2.source em.row = true := by
    rw [hst]; exact hreg em.row hin
  obtain ⟨L', hL', hemL', _⟩ := mem_first_output hctx hvs hF hem hinF
  rw [hLF] at hL'
  obtain rfl := Except.ok.inj hL'
  exact hback em hemL' hin

/-- The rows emitted by an item of level `d + 2` have height below its number of children. -/
theorem run_coeff_lt {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item}
    (hA : ItemOK ctx (official t.row) (d + 2) A) {L : List Emit}
    (hL : runItem ctx (d + 2) A = .ok L) {cs : List Item}
    (hcs : childItems ctx (d + 2) A = .ok cs) :
    ∀ em ∈ L, em.row.coeff d < cs.length := by
  obtain ⟨cs', outs, hcs', hF, rfl⟩ := runItem_children hL
  rw [hcs] at hcs'
  obtain rfl := Except.ok.inj hcs'
  obtain ⟨hlen, hget⟩ := forall₂_getElem hF
  intro em hem
  obtain ⟨L', hL', hemL'⟩ := List.mem_flatten.mp hem
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
  have hm' : m < cs.length := by omega
  obtain ⟨hmOK, hmtgt⟩ := child_itemOK hctx hA hcs m hm'
  have hgood := runItem_good hctx (d + 1) (by omega) cs[m] hmOK outs[m] (hget m hm' hm)
  have hinm := hgood.1.2.1 em hemL'
  rw [hmtgt] at hinm
  rw [(inRegion_slot_iff.mp hinm).2]
  exact hm'

end OmegaY.Official.Recon.JumpLawLower
