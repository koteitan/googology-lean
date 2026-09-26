/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeftDone
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerLeftBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFinal

set_option backward.do.legacy false

/-!
# Tools for the lower row laws (`LowerRowsCopy`, `LowerRowsBoundary`)

Generic facts about the item tree of a new column, traced and untraced:

* `lowerT_of_run`: the traced lower part `lowerT` of a column whose lower part `LowerRun`
  succeeds, with the same emitted nodes.
* `desc_parent`: a descent that goes down at least one level ends with a child step.
* `tinTree`: every item of the tree has a traced output, which is a part of the traced lower
  part and holds every traced emit of the lower part whose row lies in its target region;
  every emit of it satisfies `EmitOK`.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr

/-! ## The traced lower part -/

theorem lowerT_of_run {ctx : Context} {τ : Row} {vs : List (List Emit)}
    (h : LowerRun ctx τ vs) :
    ∃ outsT, (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT ∧
      outsT.map (List.map Prod.fst) = vs ∧ lowerT ctx τ = .ok outsT.flatten := by
  have hL := mapM_map_fst (fun x : Nat × Item => runItem ctx x.1 x.2)
    (fun p => runItemT ctx p.1 p.2) (List.map Prod.fst) (fun p => runItemT_fst ctx p.1 p.2)
    (lowerItems τ)
  unfold LowerRun at h
  rw [h] at hL
  obtain ⟨outsT, houtsT, hEq⟩ := map_eq_ok hL
  refine ⟨outsT, houtsT, hEq, ?_⟩
  unfold lowerT
  simp only [houtsT, bind, Except.bind, pure, Except.pure]

theorem flatten_map_fst {outsT : List (List (Emit × Origin))} {vs : List (List Emit)}
    (h : outsT.map (List.map Prod.fst) = vs) : outsT.flatten.map Prod.fst = vs.flatten := by
  rw [← h, List.map_flatten]

/-! ## Descents -/

theorem desc_level_le {ctx : Context} {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) : d' ≤ d := by
  induction hD with
  | refl => exact le_rfl
  | step _ _ _ ih => omega

/-- A descent that goes down ends with a child step. -/
theorem desc_parent {ctx : Context} {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) (hlt : d' < d) :
    ∃ P cs, Desc ctx d A (d' + 1) P ∧ childItems ctx (d' + 1) P = .ok cs ∧ B ∈ cs := by
  induction hD with
  | refl => omega
  | @step d A cs c d' B hcs hc hD ih =>
    rcases Nat.lt_or_ge d' (d + 1) with h | h
    · obtain ⟨P, cs', hP, hcs', hB⟩ := ih h
      exact ⟨P, cs', .step hcs hc hP, hcs', hB⟩
    · -- the descent from `c` is trivial
      have hdd : d' = d + 1 := by
        cases hD with
        | refl => rfl
        | step _ _ hD' =>
          exfalso
          have := desc_level_le hD'
          omega
      subst hdd
      have hcB : c = B := by
        cases hD with
        | refl => rfl
        | step _ _ hD' => exact absurd (desc_level_le hD') (by omega)
      subst hcB
      exact ⟨A, cs, .refl _ _, hcs, hc⟩

theorem desc_eq {ctx : Context} {d : Nat} {A B : Item} (hD : Desc ctx d A d B) : A = B := by
  cases hD with
  | refl => rfl
  | step _ _ hD' => exact absurd (desc_level_le hD') (by omega)

/-! ## Traced outputs of the items of the tree -/

theorem runItem_of_T {ctx : Context} {d : Nat} {A : Item} {TA : List (Emit × Origin)}
    (h : runItemT ctx d A = .ok TA) : runItem ctx d A = .ok (TA.map Prod.fst) := by
  have := runItemT_fst ctx d A
  rw [h] at this
  exact this.symm

theorem runItemT_children {ctx : Context} {d : Nat} {A : Item} {TA : List (Emit × Origin)}
    (h : runItemT ctx (d + 2) A = .ok TA) :
    ∃ cs outs, childItems ctx (d + 2) A = .ok cs ∧
      List.Forall₂ (fun c L' => runItemT ctx (d + 1) c = .ok L') cs outs ∧ TA = outs.flatten := by
  rw [runItemT] at h
  obtain ⟨cs, hcs, h⟩ := Reconstruction.bind_ok h
  obtain ⟨outs, houts, h⟩ := Reconstruction.bind_ok h
  refine ⟨cs, outs, hcs, ok_mapM₂ (fun c L' => runItemT ctx (d + 1) c = .ok L') cs _
    (fun c _ => RowLaw.ok_eq _) outs houts, ?_⟩
  exact (Except.ok.inj h).symm

/-- The rows of a traced output lie in the target region. -/
theorem runItemT_region {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} (hd : 1 ≤ d) {A : Item}
    (hA : ItemOK ctx (official t.row) d A) {TA : List (Emit × Origin)}
    (h : runItemT ctx d A = .ok TA) : ∀ p ∈ TA, inRegion d A.target p.1.row = true := by
  intro p hp
  have hgood := runItem_good hctx d hd A hA _ (runItem_of_T h)
  exact hgood.1.2.1 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-- **What a descendant inherits, traced.** -/
theorem tdesc {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) :
    1 ≤ d → ItemOK ctx (official t.row) d A →
      Inner.ItemInvC ctx.source ctx.rootColumn d A →
      ∀ TA, runItemT ctx d A = .ok TA → ∃ TB, runItemT ctx d' B = .ok TB ∧
        (∀ p ∈ TB, p ∈ TA) ∧ (∀ p ∈ TA, inRegion d' B.target p.1.row = true → p ∈ TB) ∧
        Inner.ItemInvC ctx.source ctx.rootColumn d' B := by
  induction hD with
  | refl d A =>
    intro _ _ hinv TA hTA
    exact ⟨TA, hTA, fun _ h => h, fun _ h _ => h, hinv⟩
  | @step d A cs c d' B hcs hc hD ih =>
    intro _ hA hinv TA hTA
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    obtain ⟨hcOK, hctgt⟩ := child_itemOK hctx hA hcs j hj
    obtain ⟨hinvc, _, _⟩ := Inner.childItems_order hcs hinv
    obtain ⟨cs', outs, hcs', hF, rfl⟩ := runItemT_children hTA
    rw [hcs] at hcs'
    obtain rfl := Except.ok.inj hcs'
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    have hj' : j < outs.length := by omega
    obtain ⟨TB, hTB, hsub, hback, hinvB⟩ :=
      ih (by omega) hcOK (hinvc _ (List.getElem_mem hj)) outs[j] (hget j hj hj')
    refine ⟨TB, hTB, fun p hp => List.mem_flatten.mpr ⟨outs[j], List.getElem_mem hj',
      hsub p hp⟩, ?_, hinvB⟩
    intro p hp hin
    obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hp
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
    have hm' : m < cs.length := by omega
    obtain ⟨hmOK, hmtgt⟩ := child_itemOK hctx hA hcs m hm'
    have hinm := runItemT_region hctx (by omega) hmOK (hget m hm' hm) p hpL'
    rw [hmtgt] at hinm
    have hD1 := desc_facts hctx hD (by omega) hcOK
    have hinj := hD1.2.2.2.1 p.1.row hin
    rw [hctgt] at hinj
    have e1 := (inRegion_slot_iff.mp hinm).2
    have e2 := (inRegion_slot_iff.mp hinj).2
    have hmj : m = j := by omega
    subst hmj
    exact hback p hpL' hin

/-- The first items are separated: a row lies in the target region of at most one. -/
theorem first_unique (ctx : Context) {τ : Row} {a b : Nat} (ha : a < (lowerItems τ).length)
    (hb : b < (lowerItems τ).length) {r : Row}
    (hra : inRegion (lowerItems τ)[a].1 (lowerItems τ)[a].2.target r = true)
    (hrb : inRegion (lowerItems τ)[b].1 (lowerItems τ)[b].2.target r = true) : a = b := by
  have hsa := (lower_itemOK (ctx := ctx) (List.getElem_mem ha)).2.1
  have hsb := (lower_itemOK (ctx := ctx) (List.getElem_mem hb)).2.1
  rw [← hsa] at hra
  rw [← hsb] at hrb
  have hsep := List.pairwise_iff_getElem.mp (Inner.lowerItems_sep τ)
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact absurd (hsep a b ha hb h r r hra hrb) (lt_irrefl _)
  · exact h
  · exact absurd (hsep b a hb ha h r r hrb hra) (lt_irrefl _)

/-- **The items of the tree, traced.** -/
theorem tinTree {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT)
    {d : Nat} {B : Item} (hB : InTree ctx (official t.row) d B) :
    ∃ TB, runItemT ctx d B = .ok TB ∧ (∀ p ∈ TB, p ∈ outsT.flatten) ∧
      (∀ p ∈ outsT.flatten, inRegion d B.target p.1.row = true → p ∈ TB) ∧
      Inner.ItemInvC ctx.source ctx.rootColumn d B := by
  obtain ⟨F, hF, hD⟩ := hB
  obtain ⟨hFOK, _, hF1, _⟩ := lower_itemOK (ctx := ctx) hF
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hF
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
  have ha' : a < outsT.length := by omega
  have hinvF : Inner.ItemInvC ctx.source ctx.rootColumn (lowerItems (official t.row))[a].1
      (lowerItems (official t.row))[a].2 := by
    intro C hC
    rw [Inner.lowerItems_clean _ _ (List.getElem_mem ha)] at hC
    cases hC
  obtain ⟨TB, hTB, hsub, hback, hinvB⟩ :=
    tdesc hctx hD hF1 hFOK hinvF outsT[a] (hall a ha ha')
  refine ⟨TB, hTB, fun p hp => List.mem_flatten.mpr ⟨outsT[a], List.getElem_mem ha',
    hsub p hp⟩, ?_, hinvB⟩
  intro p hp hin
  obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hp
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hL'
  have hb' : b < (lowerItems (official t.row)).length := by omega
  obtain ⟨hbOK, _, hb1, _⟩ := lower_itemOK (ctx := ctx) (List.getElem_mem hb')
  have hinb := runItemT_region hctx hb1 hbOK (hall b hb' hb) p hpL'
  have hD1 := desc_facts hctx hD hF1 hFOK
  have hina := hD1.2.2.2.1 p.1.row hin
  have hab := first_unique ctx ha hb' hina hinb
  subst hab
  exact hback p hpL' hin

end OmegaY.Official.Recon.LRC
