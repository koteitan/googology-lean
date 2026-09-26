/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCBSF.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBLift

set_option backward.do.legacy false

/-!
# Slot filling for the lower part of a column

`sf_tree`: if the lower part of a new column has a node in a region `Q` of level `d + 2`
(inside a first item), then it has a node in every slot `Q[j]` with `j` at most the height of that
node. The item of the tree with target `Q` has more children than that height, and every child
emits (`childSpecAll`).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

theorem sf_tree {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) {F : Nat × Item}
    (hF : F ∈ lowerItems (official t.row)) {d : Nat} (hd : d + 2 ≤ F.1) {Q : Row}
    (hQz : ZeroBelow (d + 1) Q) {em : Emit} (hem : em ∈ vs.flatten)
    (hemF : inRegion F.1 F.2.source em.row = true) (hemQ : inRegion (d + 2) Q em.row = true)
    {j : Nat} (hj : j ≤ em.row.coeff d) :
    ∃ em' ∈ vs.flatten, inRegion (d + 1) (slot (d + 2) Q j) em'.row = true := by
  obtain ⟨LF, hLF, hemLF, _⟩ := mem_first_output hctx hvs hF hem hemF
  obtain ⟨hFOK, _, hF1, _⟩ := lower_itemOK (ctx := ctx) hF
  obtain ⟨m', hm'⟩ : ∃ m', F.1 = d + 1 + 1 + m' := ⟨F.1 - (d + 2), by omega⟩
  have hFOK' := hFOK
  rw [hm'] at hFOK' hLF
  obtain ⟨J, LJ, hD, hLJ, hemJ⟩ := descend_to hctx (d + 1) m' F.2 LF em hFOK' hLF hemLF
  rw [← hm'] at hD
  have hJt : InTree ctx (official t.row) (d + 2) J := ⟨F, hF, hD⟩
  obtain ⟨_, hJOK, LB, hLB, hLBsub, _⟩ := inTree_facts hctx hvs hJt
  have hLBJ : LB = LJ := Except.ok.inj (hLB.symm.trans hLJ)
  subst hLBJ
  have hgood := runItem_good hctx (d + 2) (by omega) J hJOK LB hLB
  have hemT := hgood.1.2.1 em hemJ
  have hJQ : J.target = Q := region_eq (by simpa using hJOK.target) (by simpa using hQz) hemT hemQ
  have hH : Has ctx (d + 2) J.source := hgood.2.mpr (List.ne_nil_of_mem hemJ)
  obtain ⟨cs, outs, hcs, hF', hLBe⟩ := runItem_children hLB
  have hlt := run_coeff_lt hctx hJOK hLB hcs em hemJ
  have hjc : j < cs.length := by omega
  obtain ⟨n0, F0, σ0, hcsF, htgt, _, hall⟩ := childSpecAll hctx hJOK cs hcs
  have hn0 : cs.length = n0 := by rw [hcsF]; simp
  have hHj := hall hH j (by omega)
  have hcj : cs[j] = F0 j := by simp [hcsF]
  rw [← hcj] at hHj
  obtain ⟨hlen, hget⟩ := forall₂_getElem hF'
  have hjo : j < outs.length := by omega
  obtain ⟨hcOK, hctg⟩ := child_itemOK hctx hJOK hcs j hjc
  have hgc := runItem_good hctx (d + 1) (by omega) cs[j] hcOK outs[j] (hget j hjc hjo)
  obtain ⟨em', hem'⟩ := List.exists_mem_of_ne_nil _ (hgc.2.mp hHj)
  have hem'T := hgc.1.2.1 em' hem'
  rw [hctg, hJQ] at hem'T
  refine ⟨em', hLBsub em' ?_, hem'T⟩
  rw [hLBe]
  exact List.mem_flatten.mpr ⟨outs[j], List.getElem_mem hjo, hem'⟩

end OmegaY.Official.Recon.LRC
