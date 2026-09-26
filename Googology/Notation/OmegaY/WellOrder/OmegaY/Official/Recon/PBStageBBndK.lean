/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/PBStageBBndK.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.PBStageBRootZero

set_option backward.do.legacy false

/-!
# The hypothetical copy of the root column runs (stage B, `c_r ≥ 1`)

`BoundaryPos` (`PBStageBRoot.lean`) asks first that the copy of the root column `c_r` in a block
`i ≥ 1` (the context `K = ⟨M, R, c_r, i, c_r, w, x₀⟩`, which the rule never runs) succeeds. This
file proves it for `c_r ≥ 1` (`kRun`):

* the root column ascends at each of its own nodes (`ascCr`, from `JumpLaw.refRow_node`);
* a copied root row `C` has zero generations (the root column is at or left of `c_r`);
* the boundary column has every row `< τ` of the root column (`CutPredMD.boundaryRootRowsHolds`),
  so a clean item that does not skip the bottom finds a boundary node;
* every real node of a column `≥ 1` has a left end, so `leftColumn` succeeds (for `c_r = 0` the
  bottom of column `0` has none: this is why `Boundary` fails there).
-/

namespace OmegaY.Official.Recon.LowerPB.StageB

open Canonical Expansion Geometry Frame Classification Reserve
open Classification.Proofs Classification.Proofs.CopyShape.PBStageB
open Classification.Proofs.CopyShape Classification.Proofs.CopyShape.InnerRow
open Classification.Proofs.ChainCorr.CopyMonoProof

/-- The root column ascends at each of its nodes. -/
theorem ascCr {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {ctx : Context}
    {cr : Nat} (hs : ctx.source = M) (hx : ctx.x = cr) (hr : ctx.rootColumn = cr)
    {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M cr) : ascends ctx (some ρ) = .ok true := by
  obtain ⟨w, hw, hwrow, _⟩ := JumpLaw.refRow_node hb hρ
  have hn := JumpLaw.nodeAt_eq_of_mem hb hw
  rw [hwrow] at hn
  have hwc : w.1.column = cr := (Recon.RowLaw.realNodes_column hw).1
  obtain ⟨ρr, ρc⟩ := ρ
  obtain ⟨wr, wc⟩ := w
  show (match nodeAt ctx.source ctx.x (referenceRow (official ρc.row)) with
      | none => pure false
      | some (ref, _) => reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref) = .ok true
  rw [hs, hx, hr]
  simp only at hn hwc
  rw [hn]
  simp only
  unfold reachesRoot
  rw [if_pos (by omega)]
  simp [hwc, pure, Except.pure]

/-- A real node of a column `c ≥ 1` has a left end. -/
theorem left_of_real {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c k : Nat}
    {cell : Cell} (hc0 : 0 < c) (hk : 1 ≤ k) (h : cell? M ⟨c, k⟩ = some cell) :
    ∃ r, cell.left = some r := by
  have hV := build_valid_of_success hb
  obtain ⟨u, hu, hcu⟩ := ControlProof.node_of_cell? h
  have hu1 : u.1.val = c := by have := congrArg Ref.column hu; exact this
  have hu2 : u.2.val = k := by have := congrArg Ref.index hu; exact this
  obtain ⟨r, hr⟩ := MountainValid.left_sources hV u (by show 0 < u.2.val; omega) (by omega)
  exact ⟨r, by rw [← hcu]; exact hr⟩

/-- The generations of a node of the root column are `0`. -/
theorem gen_root {M : Mountain} {cr : Nat} {C : Row} {ref : Ref} {cell : Cell}
    (hc : ref.column = cr) {g : Nat} (h : generations M cr C (cr + 1) ref cell 0 = .ok g) :
    g = 0 := by
  unfold generations at h
  rw [if_pos (by omega)] at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

/-- **The children of an item of the copy of the root column exist.** -/
theorem k_childItems_ok {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    {K : Context} {cr B : Nat} {τ : Row} (hs : K.source = M) (hx : K.x = cr)
    (hr : K.rootColumn = cr)
    (hbnd : ∀ d T, topIn K.result K.boundary d T = topIn R B d T)
    (hBR : ∀ p ∈ realNodes M cr, official p.2.row < τ →
      ∃ q ∈ realNodes R B, official q.2.row = official p.2.row)
    {d : Nat} {it : Item} (hoff : it.offset = 0) (hInv : ChainCorr.CopyMonoProof.Inv K (d + 2) it)
    (hST : it.cutBottom = false → it.source = it.target) (hbel : BelowTau τ (d + 2) it) :
    ∃ cs, childItems K (d + 2) it = .ok cs := by
  unfold childItems
  simp only [bind, Except.bind, pure, Except.pure]
  cases hxt : topIn K.source K.x (d + 2) it.source with
  | none => exact ⟨[], rfl⟩
  | some a =>
    obtain ⟨aRef, aCell⟩ := a
    have hρ : topIn K.source K.rootColumn (d + 2) it.source = some (aRef, aCell) := by
      rw [hr, ← hx]; exact hxt
    have hmem : (aRef, aCell) ∈ realNodes M cr := by
      rw [hs, hx] at hxt; exact (Recon.RowLaw.topIn_spec hxt).1
    have hasc := ascCr hb hs hx hr hmem
    simp only [hρ, hasc]
    rw [if_neg (by simp)]
    cases hcl : it.clean with
    | none =>
        by_cases hcb : it.cutBottom = true
        · simp only [hcb]; exact ⟨_, rfl⟩
        · simp only [hcb]; exact ⟨_, rfl⟩
    | some C =>
        simp only
        have hrt := hInv C hcl
        unfold rootTop at hrt
        rw [hρ] at hrt
        have hC : official aCell.row = C := Option.some.inj hrt
        have hnC : nodeAt K.source K.x C = some (aRef, aCell) := by
          rw [hs, hx, ← hC]; exact JumpLaw.nodeAt_eq_of_mem hb hmem
        rw [hnC]
        simp only
        have hac : aRef.column = cr := (Recon.RowLaw.realNodes_column hmem).1
        have hgen : generations K.source K.rootColumn C (K.x + 1) aRef aCell 0 = .ok 0 := by
          rw [hx, hr]; unfold generations; rw [if_pos (by omega)]; rfl
        rw [hgen]
        simp only
        have hnot : ¬ (¬ it.cutBottom = true ∧
            ((topIn K.result K.boundary (d + 2) it.target).isNone = true ∨ it.offset ≠ 0)) := by
          rintro ⟨hcb, hbad⟩
          rcases hbad with hn | ho
          · have hcb' : it.cutBottom = false := by simpa using hcb
            have hst := hST hcb'
            have hCτ : official aCell.row < τ := by
              rw [hC]; exact hbel.2 C hcl
            obtain ⟨q, hq, hqrow⟩ := hBR _ hmem hCτ
            obtain ⟨hqc, hq1, hqcell⟩ := Classification.mem_realNodes hq
            have hin : inRegion (d + 2) it.target (official q.2.row) = true := by
              rw [hqrow, ← hst]; exact topIn_inRegion hρ
            rw [hbnd] at hn
            have := topIn_ne_none_of_node hqc hq1 hqcell hin
            cases h' : topIn R B (d + 2) it.target with
            | none => exact this h'
            | some _ => rw [h'] at hn; cases hn
          · exact ho hoff
        rw [if_neg hnot]
        exact ⟨_, rfl⟩

/-- The invariants of the children of an item of the copy of the root column. -/
theorem k_children_inv {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {K : Context} {cr : Nat} (hs : K.source = M) (hx : K.x = cr) (hr : K.rootColumn = cr)
    (hblk : K.block ≠ 0) {d : Nat} {it : Item} {cs : List Item} (hcase : ChildCase K d it cs)
    (hoff : it.offset = 0) (hST : it.cutBottom = false → it.source = it.target) :
    ∀ c ∈ cs, c.offset = 0 ∧ (c.cutBottom = false → c.source = c.target) ∧
      (c.cutBottom = true → c.clean = none → ∃ ρ, topIn M cr (d + 1) c.source = some ρ) := by
  intro c hc
  cases hcase with
  | none _ => simp at hc
  | case1 a ha hasc hcl _ hcb =>
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      refine ⟨rfl, fun _ => by simp only; rw [hST hcb], fun h => by cases h⟩
  | case2 a ha ρr ρc hρ hasc hcl hcb L e hL he =>
      have hST' := hST hcb
      have haρ : a = (ρr, ρc) := by
        rw [hx] at ha; rw [hr] at hρ; exact Option.some.inj (ha.symm.trans hρ)
      subst haρ
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      have hj' : j < ((height (d + 2) (official ρc.row) : Int) + L + 1).toNat :=
        List.mem_range.mp hj
      have he0 : 0 ≤ e := by rw [he]; split <;> omega
      have hρM : topIn M cr (d + 2) it.source = some (ρr, ρc) := by rw [← hs, ← hr]; exact hρ
      unfold ChainCorr.CopyMonoProof.c2
      by_cases h1 : j < height (d + 2) (official ρc.row)
      · rw [if_pos h1]
        exact ⟨rfl, fun _ => by simp only; rw [hST'], fun h => by cases h⟩
      · rw [if_neg h1]
        by_cases h2 : (j : Int) < (height (d + 2) (official ρc.row) : Int) + L + e
        · rw [if_pos h2]
          refine ⟨rfl, fun hcb' => ?_, fun _ h => by cases h⟩
          have : j = height (d + 2) (official ρc.row) := by
            simp only [decide_eq_false_iff_not] at hcb'; omega
          simp only; rw [this, hST']
        · rw [if_neg h2]
          have hjL : (j : Int) = (height (d + 2) (official ρc.row) : Int) + L := by omega
          have hidx : ((j : Int) - L).toNat = height (d + 2) (official ρc.row) := by omega
          refine ⟨rfl, fun hcb' => ?_, fun _ _ => ⟨(ρr, ρc), ?_⟩⟩
          · exfalso
            simp only [decide_eq_false_iff_not] at hcb'
            exact hcb' ⟨hblk, hjL⟩
          · simp only; rw [hidx]; exact ChainCorr.Inner.topIn_slot hρM
  | case3 a ha ρr ρc hρ hasc hcl hcb e he =>
      have haρ : a = (ρr, ρc) := by
        rw [hx] at ha; rw [hr] at hρ; exact Option.some.inj (ha.symm.trans hρ)
      subst haρ
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hjr, hjR⟩ := List.mem_filter.mp hj
      have hj0 := List.mem_range.mp hjr
      rw [if_neg hblk] at hj0
      have hj' : j < heightOf (d + 2) (topIn K.result K.boundary (d + 2) it.target) +
          height (d + 2) (official ρc.row) + 1 := hj0
      have hjR' : height (d + 2) (official ρc.row) ≤ j := by simpa using hjR
      have he0 : 0 ≤ e := by rw [he]; split <;> omega
      have hρM : topIn M cr (d + 2) it.source = some (ρr, ρc) := by rw [← hs, ← hr]; exact hρ
      unfold ChainCorr.CopyMonoProof.c3
      by_cases h2 : (j : Int) < (heightOf (d + 2) (topIn K.result K.boundary (d + 2) it.target) :
          Int) + (height (d + 2) (official ρc.row) : Int) + e
      · rw [if_pos h2]
        refine ⟨rfl, ?_, ?_⟩
        · intro h; simp at h
        · intro _ h; simp at h
      · rw [if_neg h2]
        have hjeq : j = heightOf (d + 2) (topIn K.result K.boundary (d + 2) it.target) +
            height (d + 2) (official ρc.row) := by omega
        refine ⟨rfl, fun hcb' => ?_, fun _ _ => ⟨(ρr, ρc), ?_⟩⟩
        · exfalso; simp only [decide_eq_false_iff_not] at hcb'; exact hcb' hjeq
        · simp only
          rw [show j - heightOf (d + 2) (topIn K.result K.boundary (d + 2) it.target) =
            height (d + 2) (official ρc.row) by omega]
          exact ChainCorr.Inner.topIn_slot hρM
  | case4 a ha ρr ρc hρ hasc C hcl csRef cs0 hcs g hg hbd =>
      obtain ⟨hcsc, _, _, _⟩ := Classification.nodeAt_spec hcs
      rw [hs] at hg; rw [hx, hr] at hg
      have hg0 : g = 0 := gen_root (by simp only at hcsc; rw [hcsc, hx]) hg
      subst hg0
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      have hj' := List.mem_range.mp hj
      rw [if_neg hblk, hoff] at hj'
      unfold ChainCorr.CopyMonoProof.c4
      cases hcut : it.cutBottom with
      | true =>
          simp only [if_true]
          refine ⟨?_, ?_, ?_⟩
          · rw [hoff]; omega
          · intro h; simp at h
          · intro _ h; simp at h
      | false =>
          simp only [Bool.false_eq_true, if_false]
          have hST' := hST hcut
          by_cases h1 : j < height (d + 2) (official ρc.row)
          · rw [if_pos h1]
            exact ⟨rfl, fun _ => by simp only; rw [hST'], fun h => by cases h⟩
          · rw [if_neg h1]
            refine ⟨?_, fun hcb' => ?_, fun _ h => by cases h⟩
            · rw [hoff]; dsimp only; omega
            · have : j = height (d + 2) (official ρc.row) := by
                simp only [decide_eq_false_iff_not] at hcb'; omega
              simp only; rw [this, hST']

theorem mapM_ok_of_forall {α β ε : Type} {f : α → Except ε β} :
    ∀ (xs : List α), (∀ x ∈ xs, ∃ y, f x = .ok y) → ∃ ys, xs.mapM f = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
      obtain ⟨y, hy⟩ := h x List.mem_cons_self
      obtain ⟨ys, hys⟩ := mapM_ok_of_forall xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
      refine ⟨y :: ys, ?_⟩
      rw [List.mapM_cons, hy, hys]
      rfl

/-- **Every reached item of the copy of the root column runs.** -/
theorem kRunItem {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    {K : Context} {cr B : Nat} {τ : Row} (hs : K.source = M) (hx : K.x = cr)
    (hr : K.rootColumn = cr) (hcr0 : 0 < cr) (hblk : K.block ≠ 0)
    (hbnd : ∀ d T, topIn K.result K.boundary d T = topIn R B d T)
    (hBR : ∀ p ∈ realNodes M cr, official p.2.row < τ →
      ∃ q ∈ realNodes R B, official q.2.row = official p.2.row) :
    ∀ (d : Nat) (it : Item), Reach K τ (d + 1) it → ChainCorr.CopyMonoProof.Inv K (d + 1) it →
      it.offset = 0 → (it.cutBottom = false → it.source = it.target) →
      (it.cutBottom = true → it.clean = none → ∃ ρ, topIn M cr (d + 1) it.source = some ρ) →
      ∃ ps, runItemT K (d + 1) it = .ok ps
  | 0, it, _, hInv, _, _, _ => by
      show ∃ ps, levelOneT K it = .ok ps
      have hleft : ∀ (r : Ref) (c : Cell), nodeAt K.source K.x it.source = some (r, c) →
          ∃ l, leftColumn c = .ok l := by
        intro r c h
        obtain ⟨hrc, hr1, hrcell, _⟩ := Classification.nodeAt_spec h
        simp only at hrc hr1 hrcell
        rw [hs] at hrcell
        have hrr : r = ⟨cr, r.index⟩ := by rw [← hx, ← hrc]
        rw [hrr] at hrcell
        obtain ⟨l, hl⟩ := left_of_real hb hcr0 hr1 hrcell
        exact ⟨l.column, Recon.leftColumn_of hl⟩
      unfold levelOneT
      cases hsrc : nodeAt K.source K.x it.source with
      | none => exact ⟨[], rfl⟩
      | some q =>
          obtain ⟨srcRef, src⟩ := q
          obtain ⟨l, hl⟩ := hleft srcRef src hsrc
          simp only
          cases hC : it.clean with
          | some C =>
              have hCS : C = it.source := inRegion_one (rootTop_mem (hInv C hC))
              simp only
              rw [hCS, hsrc]
              simp only [bind, Except.bind, hl, pure, Except.pure]
              exact ⟨_, rfl⟩
          | none =>
              simp only
              split
              · exact ⟨_, rfl⟩
              · simp only [bind, Except.bind, hl, pure, Except.pure]
                exact ⟨_, rfl⟩
  | d + 1, it, hRe, hInv, hoff, hST, _ => by
      obtain ⟨cs, hcs⟩ := k_childItems_ok (R := R) hb hs hx hr hbnd hBR hoff hInv hST
        (CopyShape.reach_below hRe)
      have hcase := childItems_cases hcs
      have hCO := childItems_mono hInv hcs
      have hkids := k_children_inv hb hs hx hr hblk hcase hoff hST
      obtain ⟨outs, houts⟩ := mapM_ok_of_forall cs (fun c hc =>
        kRunItem hb hs hx hr hcr0 hblk hbnd hBR d c (Reach.child hRe hcs hc) (hCO.1 c hc).1
          (hkids c hc).1 (hkids c hc).2.1 (hkids c hc).2.2)
      refine ⟨outs.flatten, ?_⟩
      show (do
        let children ← childItems K (d + 2) it
        let outs ← children.mapM (runItemT K (d + 1))
        return outs.flatten) = .ok outs.flatten
      rw [hcs]
      simp only [bind, Except.bind, houts, pure, Except.pure]

/-- **The hypothetical copy of the root column runs** (`c_r ≥ 1`). -/
theorem kRun {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    {K : Context} {cr B : Nat} {τ : Row} (hs : K.source = M) (hx : K.x = cr)
    (hr : K.rootColumn = cr) (hcr0 : 0 < cr) (hblk : K.block ≠ 0)
    (hbnd : ∀ d T, topIn K.result K.boundary d T = topIn R B d T)
    (hBR : ∀ p ∈ realNodes M cr, official p.2.row < τ →
      ∃ q ∈ realNodes R B, official q.2.row = official p.2.row) :
    ∃ es, lowerT K τ = .ok es := by
  obtain ⟨outs, houts⟩ := mapM_ok_of_forall (f := fun p : Nat × Item => runItemT K p.1 p.2)
    (lowerItems τ) (fun q hq => by
    obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
    have hRe : Reach K τ q.1 q.2 := Reach.top hq
    subst hkj
    show ∃ y, runItemT K (k + 1) ⟨slot (k + 2) τ j, slot (k + 2) τ j, none, 0, false⟩ = .ok y
    exact kRunItem hb hs hx hr hcr0 hblk hbnd hBR k _ hRe (fun C hC => by cases hC) rfl
      (fun _ => rfl) (fun h => by cases h))
  refine ⟨outs.flatten, ?_⟩
  unfold lowerT
  simp only [bind, Except.bind, houts, pure, Except.pure]

end OmegaY.Official.Recon.LowerPB.StageB
