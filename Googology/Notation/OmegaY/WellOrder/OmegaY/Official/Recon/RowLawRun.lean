/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawRun.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawChildren

set_option backward.do.legacy false

/-!
# Every processed item emits a good list

`runItem_good`: for every item satisfying `ItemOK` on which `Official.runItem` succeeds, the
emitted list is `Good` (a chain of bump steps in the target region, starting at the target
base) and it is nonempty exactly when the source column has a node in the source region.
The proof is by induction on the level, with `childSpec` and `flatten_good`.
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical Expansion Dimension

theorem flatten_ne_nil {Ls : List (List Emit)} {j : Nat} (hj : j < Ls.length) (h : Ls[j] ≠ []) :
    Ls.flatten ≠ [] := by
  intro hf
  apply h
  have hmem : Ls[j] ∈ Ls := List.getElem_mem hj
  rw [List.flatten_eq_nil_iff] at hf
  exact hf _ hmem

theorem exists_ne_nil_of_flatten {Ls : List (List Emit)} (h : Ls.flatten ≠ []) :
    ∃ j, ∃ hj : j < Ls.length, Ls[j] ≠ [] := by
  by_contra hn
  push Not at hn
  apply h
  rw [List.flatten_eq_nil_iff]
  intro L hL
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  exact hn j hj

/-- **Every processed item emits a good list.** -/
theorem runItem_good {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) :
    ∀ d, 1 ≤ d → ∀ it, ItemOK ctx (official t.row) d it →
      Ok (runItem ctx d it) (fun L => Good d it.target L ∧ (Has ctx d it.source ↔ L ≠ [])) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd1 it hit
    match d, ih, hd1 with
    | 1, _, _ =>
      rw [runItem]
      exact levelOne_good ctx it
    | d + 2, ih, _ =>
      rw [runItem]
      refine ok_bind (childSpec hctx hit) (fun children hch => ?_)
      obtain ⟨n, F, σ, rfl, htgt, hsrc, hmono, hfirst, hoff⟩ := hch
      let P : Item → List Emit → Prop := fun c L =>
        Good (d + 1) c.target L ∧ (Has ctx (d + 1) c.source ↔ L ≠ [])
      refine ok_bind (ok_mapM₂ P ((List.range n).map F) (runItem ctx (d + 1)) ?_)
        (fun outs houts => ok_pure ?_)
      · intro a ha
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
        have hj' : j < n := List.mem_range.mp hj
        refine ih (d + 1) (by omega) (by omega) (F j) ⟨?_, ?_, hoff j hj'⟩
        · rw [htgt j]
          exact slot_zeroBelow d it.target j
        · intro r hr
          rw [hsrc j] at hr
          exact hit.below r (inRegion_of_slot hr)
      · obtain ⟨hlen, hget⟩ := forall₂_getElem houts
        simp only [List.length_map, List.length_range] at hlen
        have hP : ∀ j (hj : j < outs.length), P (F j) outs[j] := by
          intro j hj
          have := hget j (by simp; omega) hj
          simpa using this
        have hpre : ∀ j j' (hj : j < outs.length) (hj' : j' < outs.length), j ≤ j' →
            outs[j'] ≠ [] → outs[j] ≠ [] := by
          intro j j' hj hj' hjj hne
          have h1 := (hP j' hj').2.mpr hne
          rw [hsrc j'] at h1
          have h2 := has_slot_mono hb h1 (hmono j j' hjj)
          rw [← hsrc j] at h2
          exact (hP j hj).2.mp h2
        obtain ⟨hc, hreg, hhead⟩ := flatten_good (d := d) (T := it.target) 0 outs
          (fun j hj => by
            have := (hP j hj).1
            rw [htgt j] at this
            simpa using this) hpre
        refine ⟨⟨hc, hreg, ?_⟩, ?_, ?_⟩
        · intro em hem
          rw [hhead em hem]
          exact slot_zero_of_zeroBelow hit.target
        · intro hH
          obtain ⟨hn, hF0⟩ := hfirst hH
          exact flatten_ne_nil (j := 0) (by omega) ((hP 0 (by omega)).2.mp hF0)
        · intro hne
          obtain ⟨j, hj, hL⟩ := exists_ne_nil_of_flatten hne
          have h1 := (hP j hj).2.mpr hL
          rw [hsrc j] at h1
          exact has_of_slot h1

end OmegaY.Official.Recon.RowLaw
