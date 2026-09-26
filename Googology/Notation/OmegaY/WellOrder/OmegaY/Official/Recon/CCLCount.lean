/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CCLCount.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLAsc
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CCLStep
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCM

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# Counting the emits of a node along the simulation (`CCL`, part (c))

Two copy contexts `cX`, `cY` of one block (`LRC.Pair`), and nodes `v` of `x`, `v'` of `y` of the
anchor row `C`. With the anchor facts `AnchE` (ascension below `C` agrees, ascension at `C`
carries from `x` to `y`, equal generations at `C`), every item `A` of the tree of `x` and every
similar item `B` of the tree of `y` (`LRC.Sim`) satisfy: `A` emits at most as many copies of `v`
as `B` emits copies of `v'` (`count_sim`).

The proof is by induction on the level. At level `d + 2` the emits of an item are the emits of its
children. A child `j` of `A` that emits a copy `θ` of `v` has, by `stepE` (the step of the
simulation, `CCLStep.lean`), a similar child `j` of `B`; the other children of `A` emit no copy of
`v` (`count_le_sum`). At level `1` the item `A` emits at most one node, and `B` (same source row
`C`, root row `C` if any) emits a copy of `v'`.

* `count_le_sum`, `levelOneT_src`;
* `count_sim`;
* `left_ge_of_asc`: the stored left end of `v` is at or right of `c_r` when `x` ascends at the
  row of `v`.
-/

namespace OmegaY.Official.Recon.CCL

open Canonical Expansion Geometry Frame Classification
open Reserve (cell?)
open Classification.Proofs.ChainCorr (cutOrigin)
open Classification.Proofs.CopyShape.ProfileLeg (AscRow)
open RPLLex (cnt)
open JumpLaw JumpLawLower LRC

/-! ## Sums -/

theorem cnt_nil (v : Ref) : cnt [] v = 0 := rfl

theorem cnt_append (l1 l2 : List (Emit × Origin)) (v : Ref) :
    cnt (l1 ++ l2) v = cnt l1 v + cnt l2 v := by
  unfold cnt; exact List.countP_append

theorem cnt_flatten_cons (a : List (Emit × Origin)) (l : List (List (Emit × Origin))) (v : Ref) :
    cnt (a :: l).flatten v = cnt a v + cnt l.flatten v := by
  rw [List.flatten_cons, cnt_append]

theorem cnt_flatten_zero {l : List (List (Emit × Origin))} {v : Ref}
    (h : ∀ j (hj : j < l.length), cnt l[j] v = 0) : cnt l.flatten v = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h0 : cnt a v = 0 := h 0 (by simp)
    have h1 : cnt l.flatten v = 0 := ih (fun j hj => h (j + 1) (by simp; omega))
    rw [cnt_flatten_cons, h0, h1]

/-- **Index-preserving comparison of flattened counts.** -/
theorem count_le_sum {v v' : Ref} :
    ∀ (l1 l2 : List (List (Emit × Origin))),
      (∀ j (h1 : j < l1.length), 0 < cnt l1[j] v →
        ∃ h2 : j < l2.length, cnt l1[j] v ≤ cnt l2[j] v') →
      cnt l1.flatten v ≤ cnt l2.flatten v'
  | [], _, _ => by simp [cnt_nil]
  | a :: l1, [], h => by
    have : cnt (a :: l1).flatten v = 0 := by
      apply cnt_flatten_zero
      intro j hj
      by_contra hn
      obtain ⟨h2, _⟩ := h j hj (by omega)
      simp at h2
    omega
  | a :: l1, b :: l2, h => by
    rw [cnt_flatten_cons, cnt_flatten_cons]
    have h0 : cnt a v ≤ cnt b v' := by
      by_cases hz : cnt a v = 0
      · omega
      · obtain ⟨_, hle⟩ := h 0 (by simp) (by simpa using Nat.pos_of_ne_zero hz)
        simpa using hle
    have ih := count_le_sum l1 l2 (fun j h1 hpos => by
      obtain ⟨h2, hle⟩ := h (j + 1) (by simp; omega) (by simpa using hpos)
      exact ⟨by simp at h2; omega, by simpa using hle⟩)
    omega

theorem exists_of_cnt_pos {l : List (Emit × Origin)} {v : Ref} (h : 0 < cnt l v) :
    ∃ p ∈ l, p.2.src = v := by
  unfold cnt at h
  obtain ⟨p, hp, hpv⟩ := List.countP_pos_iff.mp h
  exact ⟨p, hp, by simpa using hpv⟩

theorem one_le_cnt_of_mem {l : List (Emit × Origin)} {v : Ref} {p : Emit × Origin}
    (hp : p ∈ l) (hpv : p.2.src = v) : 1 ≤ cnt l v := by
  unfold cnt
  exact List.countP_pos_iff.mpr ⟨p, hp, by simp [hpv]⟩

/-! ## Level one -/

/-- A level-one item whose source row has a node, and which copies no other root row, emits a
copy of that node. -/
theorem levelOneT_src {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) {r : Ref} {c : Cell}
    (hn : nodeAt ctx.source ctx.x it.source = some (r, c))
    (hcl : it.clean = none ∨ it.clean = some it.source) : ∃ p ∈ ps, p.2.src = r := by
  unfold levelOneT at h
  rw [hn] at h
  rcases hcl with hcl | hcl
  · rw [hcl] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · obtain rfl := Except.ok.inj h
      exact ⟨_, List.mem_singleton_self _, rfl⟩
    · split at h
      · cases h
      · obtain rfl := Except.ok.inj h
        exact ⟨_, List.mem_singleton_self _, rfl⟩
  · rw [hcl] at h
    simp only [hn, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact ⟨_, List.mem_singleton_self _, rfl⟩

/-! ## The simulation of the counts -/

theorem runItemT_det {ctx : Context} {d : Nat} {A : Item} {T T' : List (Emit × Origin)}
    (h : runItemT ctx d A = .ok T) (h' : runItemT ctx d A = .ok T') : T = T' :=
  Except.ok.inj (h.symm.trans h')

/-- **The count simulation.** -/
theorem count_sim {cX cY : Context} (P : Pair cX cY) {s : List Nat} {t : Cell} {root : Ref}
    (rX : RunCtx s cX t root) (rY : RunCtx s cY t root)
    (hb : Canonical.build s = .ok cX.source) {C : Row} (H : AnchE cX cY C)
    {outsX outsY : List (List (Emit × Origin))}
    (houtsX : (lowerItems (official t.row)).mapM (fun p => runItemT cX p.1 p.2) = .ok outsX)
    (houtsY : (lowerItems (official t.row)).mapM (fun p => runItemT cY p.1 p.2) = .ok outsY)
    {v : Ref} {cv : Cell} (hcv : cell? cX.source v = some cv) (hvC : official cv.row = C)
    {v' : Ref} {cv' : Cell} (hv'm : (v', cv') ∈ realNodes cX.source cY.x)
    (hv'C : official cv'.row = C) (hnv' : nodeAt cX.source cY.x C = some (v', cv'))
    (hMDX : ∀ d A r cl, InTree cX (official t.row) (d + 2) A →
      topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDY : ∀ d B r cl, InTree cY (official t.row) (d + 2) B →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) B.source))
    (hMHY : ∀ d B, InTree cY (official t.row) (d + 2) B → ∀ C' r cl csRef csc g,
      B.clean = some C' → B.cutBottom = false →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C' = some (csRef, csc) →
      generations cX.source cX.rootColumn C' (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∀ d A B, InTree cX (official t.row) d A → InTree cY (official t.row) d B →
      Sim cX cY d A B → ∀ TA TB, runItemT cX d A = .ok TA → runItemT cY d B = .ok TB →
        cnt TA v ≤ cnt TB v' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro A B hAt hBt hsim TA TB hTA hTB
  rcases d with _ | _ | d
  · -- level 0
    have : TA = [] := by
      simp only [runItemT, pure, Except.pure] at hTA
      exact (Except.ok.inj hTA).symm
    subst this
    simp [cnt_nil]
  · -- level 1
    have hTA' : levelOneT cX A = .ok TA := hTA
    have hTB' : levelOneT cY B = .ok TB := hTB
    have hlen := Classification.Proofs.CopyShape.NoMA.levelOneT_length hTA'
    by_cases h0 : cnt TA v = 0
    · omega
    obtain ⟨θ, hθ, hθv⟩ := exists_of_cnt_pos (Nat.pos_of_ne_zero h0)
    have hcntA : cnt TA v ≤ 1 := by
      unfold cnt; exact (List.countP_le_length).trans hlen
    obtain ⟨TA2, hTA2, _, _, hinvA⟩ := tinTree rX houtsX hAt
    obtain rfl := runItemT_det hTA hTA2
    obtain ⟨TB2, hTB2, _, _, hinvB⟩ := tinTree rY houtsY hBt
    obtain rfl := runItemT_det hTB hTB2
    have hE := (Classification.Proofs.ChainCorr.Inner.levelOneT_order hTA' hinvA).2 θ hθ
    have hcθ : cell? cX.source θ.2.src = some cv := by rw [hθv]; exact hcv
    obtain ⟨hreg, _, _, _⟩ := eok_parts hE hcθ
    have hAs : official cv.row = A.source := Classification.inRegion_one hreg
    have hBs : B.source = C := by rw [hsim.source, ← hAs, hvC]
    have hnB : nodeAt cY.source cY.x B.source = some (v', cv') := by
      rw [P.src, hBs]; exact hnv'
    have hcl : B.clean = none ∨ B.clean = some B.source := by
      cases hBc : B.clean with
      | none => exact Or.inl rfl
      | some C'' =>
        right
        obtain ⟨r, ρc, htop, hrow⟩ := hinvB C'' hBc
        have := Classification.inRegion_one (Classification.topIn_inRegion htop)
        rw [← hrow, this]
    obtain ⟨p, hp, hpv⟩ := levelOneT_src hTB' hnB hcl
    have := one_le_cnt_of_mem hp hpv
    omega
  · -- level d + 2
    obtain ⟨csX, outs1, hcsX, hFX, rfl⟩ := runItemT_children (d := d) hTA
    obtain ⟨csY, outs2, hcsY, hFY, rfl⟩ := runItemT_children (d := d) hTB
    obtain ⟨hlX, hgX⟩ := RowLaw.forall₂_getElem hFX
    obtain ⟨hlY, hgY⟩ := RowLaw.forall₂_getElem hFY
    obtain ⟨TA2, hTA2, _, _, hinvA⟩ := tinTree rX houtsX hAt
    obtain rfl := runItemT_det hTA hTA2
    apply count_le_sum
    intro j hj hpos
    have hjc : j < csX.length := by omega
    obtain ⟨θ, hθ, hθv⟩ := exists_of_cnt_pos hpos
    have hcθ : cell? cX.source θ.2.src = some cv := by rw [hθv]; exact hcv
    -- the child `j` and its facts
    have hcjt : InTree cX (official t.row) (d + 1) csX[j] :=
      LowerLeftProof.inTree_snoc hAt hcsX (List.getElem_mem hjc)
    have hrj : runItemT cX (d + 1) csX[j] = .ok outs1[j] := hgX j hjc hj
    obtain ⟨Tj, hTj, _, _, hinvj⟩ := tinTree rX houtsX hcjt
    obtain rfl := runItemT_det hrj hTj
    have hθA : θ ∈ outs1.flatten := List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hθ⟩
    have hEA := (Classification.Proofs.ChainCorr.Inner.runItemT_order cX (d + 2) A _ hTA
      hinvA).2 θ hθA
    have hEc := (Classification.Proofs.ChainCorr.Inner.runItemT_order cX (d + 1) csX[j] _ hrj
      hinvj).2 θ hθ
    obtain ⟨hregc, _, _, _⟩ := eok_parts hEc hcθ
    have hw : inRegion (d + 1) (csX[j]'hjc).source (official (v', cv').2.row) = true := by
      show inRegion (d + 1) csX[j].source (official cv'.row) = true
      rw [hv'C, ← hvC]; exact hregc
    obtain ⟨ax, hax⟩ : ∃ ax, topIn cX.source cX.x (d + 2) A.source = some ax := by
      cases h : topIn cX.source cX.x (d + 2) A.source with
      | none =>
        have := Recon.childItems_none hcsX h
        rw [this] at hjc; simp at hjc
      | some ax => exact ⟨ax, rfl⟩
    have hBs := hsim.source
    obtain ⟨hjY, hsimj, _⟩ := stepE P hb H hcθ hvC hsim hcsX hcsY hax le_rfl (Nat.le_succ j) hjc
      hEA hEc hv'm hw (hMDX d A · · hAt)
      (fun r cl hρ hasc => by
        have := hMDY d B r cl hBt (by rw [hBs]; exact hρ) hasc
        rw [hBs] at this; exact this)
      (hMHY d B hBt)
    have hj2 : j < outs2.length := by omega
    refine ⟨hj2, ?_⟩
    have hcjtY : InTree cY (official t.row) (d + 1) csY[j] :=
      LowerLeftProof.inTree_snoc hBt hcsY (List.getElem_mem hjY)
    exact ih (d + 1) (by omega) csX[j] csY[j] hcjt hcjtY hsimj outs1[j] outs2[j] hrj
      (hgY j hjY hj2)

end OmegaY.Official.Recon.CCL

#print axioms OmegaY.Official.Recon.CCL.count_sim
