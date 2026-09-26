/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBGenLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBCutLegMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanParent

set_option backward.do.legacy false

/-!
# `GenLeg` holds (stage B)

`GenLeg` (`PBStageBCutLeg.lean`): let `v = (x, k)` have its left end in the column `ℓ ≥ c_r`, and
let `C` be a row with nodes `(x, C)` and `(ℓ, C)`, the node of `ℓ` at or below `v`. Then the
generations of `(ℓ, C)` are at most those of `(x, C)`.

## Proof

The chain of generations at the row `C` is the chain of candidate steps `Q` at the height `C`
(`ChainCorr.Inner.Clean.genStep_of_Q`). The canonical row shadow (`P_rowShadow`, the same tool
as `LowerPB.shadow`) gives a path of numerical parents at the height `C` from the node `(x, C)`
to the node `(ℓ, C)` (when `C` is below `v`; at the row of `v` the path is one step, the left
end of `v`). A numerical parent at the same height is reached by candidate steps at that height
(`P_iff`, `Hit`), so the chain of generations from `(x, C)` passes through `(ℓ, C)`
(`path_chain`), and the generations only add up along it (`gen_chain_le`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs

/-! ## Generations along a chain of steps -/

theorem gen_shift' (M : Mountain) (cr : Nat) (C : Row) :
    ∀ f r c g0 a, generations M cr C f r c g0 = .ok a →
      ∀ f' g0' b, generations M cr C f' r c g0' = .ok b → a + g0' = b + g0
  | 0, _, _, _, _, h => by simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, r, c, g0, a, h => by
    intro f' g0' b h'
    cases f' with
    | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at h'
    | succ f' =>
      unfold generations at h h'
      by_cases hc : r.column ≤ cr
      · rw [if_pos hc] at h h'
        simp only [pure, Except.pure, Except.ok.injEq] at h h'
        omega
      · rw [if_neg hc] at h h'
        simp only [bind, Except.bind] at h h'
        cases hl : leftColumn c with
        | error e => rw [hl] at h; cases h
        | ok p =>
          rw [hl] at h h'
          simp only at h h'
          by_cases hp : p < r.column
          · rw [if_neg (by omega)] at h h'
            cases hn : nodeAt M p C with
            | none => rw [hn] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
            | some q =>
              obtain ⟨r2, c2⟩ := q
              rw [hn] at h h'
              simp only at h h'
              have := gen_shift' M cr C f r2 c2 (g0 + 1) a h f' (g0' + 1) b h'
              omega
          · rw [if_pos (by omega)] at h
            simp [throw, throwThe, MonadExceptOf.throw] at h

theorem gen_add (M : Mountain) (cr : Nat) (C : Row) :
    ∀ f r c g, generations M cr C f r c g = (generations M cr C f r c 0).map (· + g)
  | 0, r, c, g => by simp [generations, throw, throwThe, MonadExceptOf.throw, Except.map]
  | f + 1, r, c, g => by
    unfold generations
    by_cases hc : r.column ≤ cr
    · rw [if_pos hc, if_pos hc]
      simp [pure, Except.pure, Except.map]
    · rw [if_neg hc, if_neg hc]
      simp only [bind, Except.bind]
      cases hl : leftColumn c with
      | error e => simp [Except.map]
      | ok p =>
        simp only
        by_cases hp : p < r.column
        · rw [if_neg (by omega), if_neg (by omega)]
          cases hn : nodeAt M p C with
          | none => simp [throw, throwThe, MonadExceptOf.throw, Except.map]
          | some q =>
            obtain ⟨r2, c2⟩ := q
            simp only
            rw [gen_add M cr C f r2 c2 (g + 1), gen_add M cr C f r2 c2 (0 + 1)]
            cases generations M cr C f r2 c2 0 with
            | error e => simp [Except.map]
            | ok v => simp [Except.map]; omega
        · rw [if_pos (by omega), if_pos (by omega)]
          simp [throw, throwThe, MonadExceptOf.throw, Except.map]

/-- **Generations along a chain of generation steps.** -/
theorem gen_chain_le {M : Mountain} (hV : MountainValid M) {cr : Nat} {C : Row} {a b : Ref}
    (h : Relation.ReflTransGen (ChainCorr.Inner.GenStep M cr) a b) :
    ∀ {ca : Cell}, cell? M a = some ca → official ca.row = C →
      ∀ {fa ga : Nat}, generations M cr C fa a ca 0 = .ok ga →
      ∀ {cb : Cell} {fb gb : Nat}, cell? M b = some cb →
        generations M cr C fb b cb 0 = .ok gb → gb ≤ ga := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro ca hca _ fa ga hga cb fb gb hcb hgb
      have hcc : cb = ca := Option.some.inj (hcb.symm.trans hca)
      subst hcc
      have := gen_shift' M cr C fa b cb 0 ga hga fb 0 gb hgb
      omega
  | @head a a' hab _ ih =>
      intro ca hca hC fa ga hga cb fb gb hcb hgb
      obtain ⟨hcr, ha1, ca', cb', l, hca', hl, hcol, hcb', hrow⟩ := hab
      have hcc : ca' = ca := Option.some.inj (hca'.symm.trans hca)
      subst hcc
      cases fa with
      | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at hga
      | succ f =>
          unfold generations at hga
          rw [if_neg (by omega)] at hga
          simp only [bind, Except.bind] at hga
          have hlc : leftColumn ca' = .ok l.column := Recon.leftColumn_of hl
          rw [hlc] at hga
          simp only at hga
          have hlt : l.column < a.column := left_lt_of_valid hV hca hl
          rw [if_neg (by omega)] at hga
          -- the node of the leg column at the row `C` is `a'`
          have hmem := mem_realNodes_of_cell' hcb' ha1
          obtain ⟨p', hp'⟩ := Recon.RowLaw.nodeAt_of_mem hmem
          have hp'' : nodeAt M l.column C = some p' := by
            rw [← hcol, ← hC]; simp only at hp'; rw [hrow] at hp'; exact hp'
          obtain ⟨p1, p2⟩ := p'
          obtain ⟨hpc, hp1, hpcell, hprow⟩ := Classification.nodeAt_spec hp''
          have hpa : p1 = a' := ref_eq_of_official hV (by simp only at hpc; rw [hpc, hcol]) hp1 ha1
            hpcell hcb' (by simp only at hprow; rw [hprow, ← hC, hrow])
          subst hpa
          have hpp : p2 = cb' := Option.some.inj (hpcell.symm.trans hcb')
          subst hpp
          rw [hp''] at hga
          simp only at hga
          rw [gen_add] at hga
          cases hg0 : generations M cr C f p1 p2 0 with
          | error e => rw [hg0] at hga; cases hga
          | ok v =>
              rw [hg0] at hga
              simp only [Except.map, Except.ok.injEq] at hga
              have := ih hcb' (by rw [hrow, hC]) hg0 hcb hgb
              omega

/-! ## Numerical-parent paths at one height are generation chains -/

section FrameChain

open Geometry Geometry.Frame

variable {M : Mountain}

theorem hit_pos {F : Frame} {th : Nat} {a b : F.Node} (h : Hit F th a b) : 0 < F.value b := by
  induction h with
  | here hpos _ => exact hpos
  | next _ _ _ ih => exact ih

theorem hit_chain (hO : (Frame.ofMountain M).Ordered) {cr th : Nat}
    {a b : (Frame.ofMountain M).Node} (h : Hit (Frame.ofMountain M) th a b) :
    Frame.Real a → cr ≤ b.1.val →
      (Frame.ofMountain M).height b = (Frame.ofMountain M).height a →
      Relation.ReflTransGen (ChainCorr.Inner.GenStep M cr) (Frame.ref a) (Frame.ref b) := by
  induction h with
  | here _ _ => intro _ _ _; exact Relation.ReflTransGen.refl
  | @next u q p _ hQ rest ih =>
      intro hu hcr hh
      have hq : Frame.Real q := Q_real hO hu hQ
      have h1 := rest.height_le hO
      have h2 := Q_height_le hO hQ
      have hqh : (Frame.ofMountain M).height q = (Frame.ofMountain M).height u :=
        le_antisymm h2 (hh ▸ h1)
      have hc1 := Q_column_lt hO hQ
      have hc2 := rest.column_le hO
      have hstep := ChainCorr.Inner.Clean.genStep_of_Q (cr := cr) hO hu hQ hqh (by omega)
      exact Relation.ReflTransGen.head hstep (ih hq hcr (hh.trans hqh.symm))

theorem pathColumnLe {F : Frame} (hF : F.Ordered) {a b : F.Node}
    (h : ParentPath F a b) : b.1.val ≤ a.1.val := by
  induction h with
  | refl _ => exact le_rfl
  | cons hp _ ih => exact le_trans ih (P_column_lt hF hp).le

theorem path_chain (hO : (Frame.ofMountain M).Ordered) {cr : Nat}
    {a b : (Frame.ofMountain M).Node} (h : ParentPath (Frame.ofMountain M) a b) :
    Frame.Real a → cr ≤ b.1.val →
      (Frame.ofMountain M).height b = (Frame.ofMountain M).height a →
      Relation.ReflTransGen (ChainCorr.Inner.GenStep M cr) (Frame.ref a) (Frame.ref b) := by
  induction h with
  | refl _ => intro _ _ _; exact Relation.ReflTransGen.refl
  | @cons u q p hp rest ih =>
      intro hu hcr hh
      obtain ⟨q0, hQ, hit⟩ := (P_iff hO).mp hp
      have hq0 : Frame.Real q0 := Q_real hO hu hQ
      have hq : Frame.Real q := real_of_value_pos hO (hit_pos hit)
      have h1 := rest.height_le hO
      have h2 := hit.height_le hO
      have h3 := Q_height_le hO hQ
      have hq0h : (Frame.ofMountain M).height q0 = (Frame.ofMountain M).height u :=
        le_antisymm h3 (hh ▸ h1.trans h2)
      have hqh : (Frame.ofMountain M).height q = (Frame.ofMountain M).height q0 :=
        le_antisymm h2 (hq0h ▸ hh ▸ h1)
      have hc1 := Q_column_lt hO hQ
      have hc2 := hit.column_le hO
      have hc3 := pathColumnLe hO rest
      have hstep := ChainCorr.Inner.Clean.genStep_of_Q (cr := cr) hO hu hQ hq0h (by omega)
      have hmid := hit_chain (cr := cr) hO hit hq0 (by omega) hqh
      exact Relation.ReflTransGen.head hstep (hmid.trans
        (ih hq hcr (hh.trans (hqh.trans hq0h).symm)))

end FrameChain

/-! ## The theorem -/

open Geometry Geometry.Frame in
/-- **`GenLeg` holds.** -/
theorem genLeg : GenLeg := by
  intro s M t root hTop x k cp lref hx _ hk hcp hl hlcr C ax ay cx cy gx gy hnx hny hle hgx hgy
  have hM := hTop.build
  have hV := build_valid_of_success hM
  have hN := build_normal_of_legal (build_success_legal hM) hM
  have hO := hN.toOrdered
  obtain ⟨haxc, hax1, hcx, hcxrow⟩ := Classification.nodeAt_spec hnx
  obtain ⟨hayc, hay1, hcy, hcyrow⟩ := Classification.nodeAt_spec hny
  simp only at haxc hax1 hcx hcxrow hayc hay1 hcy hcyrow
  suffices hch : Relation.ReflTransGen (ChainCorr.Inner.GenStep M root.column) ax ay from
    gen_chain_le hV hch hcx hcxrow hgx hcy hgy
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- the row of `v`: one step, the left end of `v`
    have hav : ax = ⟨x, k⟩ := ref_eq_of_official hV (by rw [haxc]) hax1 hk hcx hcp
      (by rw [hcxrow, ← hcyrow, heq])
    subst hav
    have hcc : cx = cp := Option.some.inj (hcx.symm.trans hcp)
    subst hcc
    exact Relation.ReflTransGen.single ⟨hx, hay1, cx, cy, lref, hcp, hl, hayc, hcy, heq⟩
  · -- below `v`: the row shadow gives a path of numerical parents at the row `C`
    obtain ⟨hc, hki, hkc⟩ := Proofs.canon_cell?_some_iff.mp hcp
    have hayc' : ay = ⟨lref.column, ay.index⟩ := by rw [← hayc]
    obtain ⟨hrc, hk'i, hk'c⟩ := Proofs.canon_cell?_some_iff.mp (by rw [← hayc']; exact hcy :
      cell? M ⟨lref.column, ay.index⟩ = some cy)
    let no : (Frame.ofMountain M).Node := ⟨⟨x, hc⟩, ⟨k, hki⟩⟩
    let nw : (Frame.ofMountain M).Node := ⟨⟨lref.column, hrc⟩, ⟨ay.index, hk'i⟩⟩
    have hnw : Frame.Real nw := hay1
    have hnoc : (Frame.ofMountain M).cell no = cp := hkc
    have hnwc : (Frame.ofMountain M).cell nw = cy := hk'c
    rcases Nat.lt_or_ge 1 k with hk2 | hk1
    · have hki' : k < M[x].size := hki
      let nu : (Frame.ofMountain M).Node := ⟨⟨x, hc⟩, ⟨k - 1, by change k - 1 < M[x].size; omega⟩⟩
      have hnu : Frame.Real nu := by show 0 < k - 1; omega
      have hup : (Frame.ofMountain M).upper nu = some no :=
        ControlProof.upper_eq_of_index rfl (show k = k - 1 + 1 by omega)
      have hleft : ((Frame.ofMountain M).cell no).left = some lref := by rw [hnoc]; exact hl
      obtain ⟨np, hlk, _, _⟩ := hO.stored_valid no lref hleft
      have hnp : Frame.ref np = lref := Frame.lookup_spec hlk
      have hraw : (Frame.ofMountain M).rawParent nu = some np :=
        Frame.rawParent_eq_of_upper_left hup (by rw [hnp]; exact hleft)
      obtain ⟨_, hmax⟩ := Proofs.Normal.rawParent_highest_below hN hnu hup hraw
      have hnpc : np.1.val = lref.column := by rw [← hnp]; rfl
      have hw1 : nw.1 = np.1 := Fin.ext (by simp [nw, hnpc])
      have hwle : nw.2.val ≤ np.2.val :=
        hmax nw hw1 (by
          show ((Frame.ofMountain M).cell nw).row < ((Frame.ofMountain M).cell no).row
          rw [hnwc, hnoc]
          exact hlt)
      have hwh : (Frame.ofMountain M).height nw ≤ (Frame.ofMountain M).height np :=
        ControlProof.height_le_of_index hO hw1 hwle
      have hP : (Frame.ofMountain M).P nu = some np := (hN.rawParent_eq_P hnu).symm.trans hraw
      obtain ⟨v, hv, hvc, _, hvh, hpath⟩ := P_rowShadow hN hP nw hnw hw1 hwh
      -- the start of the path is the node `(x, C)`
      have hvref : Frame.ref v = ax := by
        have hcv := ControlProof.cell?_ref (M := M) v
        refine ref_eq_of_official hV ?_ hv hax1 hcv hcx ?_
        · show v.1.val = ax.column
          rw [haxc, hvc]
        · rw [hcxrow]
          have : ((Frame.ofMountain M).cell v).row = cy.row := by
            rw [← hnwc]; exact hvh
          rw [this, hcyrow]
      have hwref : Frame.ref nw = ay := by rw [hayc']; rfl
      rw [← hvref, ← hwref]
      exact path_chain hO hpath hv (by show root.column ≤ lref.column; exact hlcr) hvh.symm
    · -- `k = 1`: `v` is the bottom node; no real node lies strictly below it
      have hk1' : k = 1 := by omega
      subst hk1'
      have hbot : cp.row = 1 := by
        rw [← hnoc]
        exact hO.bottom_row ⟨x, hc⟩ hki
      have h1 : (1 : Row) ≤ cy.row := by
        rw [← hnwc]
        exact Frame.one_le_height hO hnw
      rw [hbot] at hlt
      exact absurd (lt_of_le_of_lt h1 hlt) (lt_irrefl _)

/-- **`CutLeg` holds.** -/
theorem cutLeg : Recon.LowerPB.CutLeg := cutLeg_of_genLeg genLeg

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.genLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.cutLeg
