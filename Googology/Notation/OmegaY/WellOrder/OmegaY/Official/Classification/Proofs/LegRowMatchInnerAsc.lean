/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchInnerAsc.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LiftLegRightProof

set_option backward.do.legacy false

/-!
# A column and the leg column of a node above the root top ascend together

A statement about `M(s)` only. Let `(x, k)` be a node of `M(s)` with `c_r < x`, whose leg `l`
(the column of its stored left end) is right of `c_r`, and let `S` be a region of level `d + 2`
with a root-column top `ρ` and `row ρ < row (x, k) ∈ S`. Then `x` ascends in `S` iff `l` does
(`ascAgree`). Unlike `ConeApply.ascSame` (`ParentBelowLowerFixAscSame.lean`), no node of `l`
between `ρ` and `(x, k)` is needed.

Let `w` be the node below `(x, k)` and `p = P(w)` its parent (in `l`).

* `x` ascends ⇒ `l` ascends: `x` is in the cone of `ParentBelowLowerFixCone.lean` (`ascSetup`),
  and `C < height (x, k) < cap`, so the left end `p` of the edge below `(x, k)` is in a cone
  column (`Cone.Setup.left_in_cone`).
* `l` ascends ⇒ `x` ascends: `l` has a node `low` at the height `L` of `root` with a path to
  `root`. The parent `p` is not below `low`: otherwise the node above `p` is at or below `low`, and
  the father upper bound (`father_upper_bound_nodes`) gives
  `height (x, k) ≤ height (p⁺) ≤ L ≤ C < height (x, k)`. So the row shadow of the edge `w → p`
  (`P_rowShadow`) gives a node of `x` at the height `L` with a path to `low`, hence to `root`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

open Canonical Expansion Classification Reserve
open OmegaY.Geometry OmegaY.Geometry.Frame
open OmegaY.Official.Recon.LowerPB OmegaY.Official.Recon.LowerPB.LiftLegPf
open Classification.Proofs.ChainCorr

variable {M : Mountain}

/-! ## The ascension test from a path of numerical parents

(The same as in `ParentBelowLowerFixAscSame.lean`, repeated here so that this file depends only
on `LiftLegRightProof.lean`.) -/

/-- A numerical parent at the same height is the in-row parent of the test. -/
theorem weakParent_of_P' {s : List Nat} (hb : Canonical.build s = .ok M)
    {u p : (Frame.ofMountain M).Node} (hP : (Frame.ofMountain M).P u = some p)
    (hh : (Frame.ofMountain M).height p = (Frame.ofMountain M).height u) :
    Expansion.weakParent M (Frame.ref u) = .ok (some (Frame.ref p)) := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  have hv := P_value hO hP
  have hu : Frame.Real u := real_of_value_pos hO (by omega)
  have hraw := rawParent_of_P' hN hu hP
  have hlt := Frame.P_column_lt hO hP
  have hcu := ControlProof.cell?_ref (M := M) u
  have hcp := ControlProof.cell?_ref (M := M) p
  apply Expansion.weakParent_iff_twoLeg.mpr
  simp only [Reserve.rawParent, Option.bind_eq_bind, Option.bind_eq_some_iff] at hraw
  obtain ⟨col, hcol, up, hup, hleft⟩ := hraw
  obtain ⟨colu, hcolu, hcellu⟩ := cell?_spec hcu
  have hcc : colu = col := Option.some.inj (hcolu.symm.trans hcol)
  subst hcc
  obtain ⟨colp, hcolp, hcellp⟩ := cell?_spec hcp
  refine ⟨colu, _, up, _, hcolu, hcellu, hup, hleft, hlt, ⟨colp, hcolp, hcellp⟩, ?_⟩
  simpa [Frame.height] using hh

/-- **A path of numerical parents at one height to the root column passes the test.** -/
theorem reach_of_path {s : List Nat} (hb : Canonical.build s = .ok M) {cr : Nat}
    {u r : (Frame.ofMountain M).Node} (h : ParentPath (Frame.ofMountain M) u r) :
    (Frame.ofMountain M).height r = (Frame.ofMountain M).height u → r.1.val = cr →
      ∀ f, u.1.val < f → reachesRoot M cr f (Frame.ref u) = .ok true := by
  have hO := (build_normal_of_success hb).toOrdered
  induction h with
  | refl u =>
    intro _ hr f hf
    cases f with
    | zero => omega
    | succ f =>
      have hc : (Frame.ref u).column ≤ cr := by show u.1.val ≤ cr; omega
      simp only [reachesRoot, if_pos hc, pure, Except.pure]
      congr 1
      simp only [decide_eq_true_eq]
      show u.1.val = cr
      exact hr
  | @cons u q r hP rest ih =>
    intro hh hr f hf
    have h1 := Frame.P_height_le hO hP
    have h2 := rest.height_le hO
    have hq : (Frame.ofMountain M).height q = (Frame.ofMountain M).height u :=
      le_antisymm h1 (by rw [← hh]; exact h2)
    have hw := weakParent_of_P' hb hP hq
    have hlt := Frame.P_column_lt hO hP
    have hle := rest.column_le hO
    cases f with
    | zero => omega
    | succ f =>
      have hc : ¬ (Frame.ref u).column ≤ cr := by show ¬ u.1.val ≤ cr; omega
      conv_lhs => unfold reachesRoot
      rw [if_neg hc]
      simp only [liftE, hw, Except.mapError, bind, Except.bind]
      exact ih (by rw [hh, hq]) hr f (by omega)

/-- A real node of a column is the node found at its official row. -/
theorem nodeAt_of_node {s : List Nat} (hb : Canonical.build s = .ok M)
    (u : (Frame.ofMountain M).Node) (hu : Frame.Real u) :
    nodeAt M u.1.val (Official.official ((Frame.ofMountain M).cell u).row) =
      some (Frame.ref u, (Frame.ofMountain M).cell u) := by
  have hV := build_valid_of_success hb
  have hmem : (Frame.ref u, (Frame.ofMountain M).cell u) ∈ realNodes M u.1.val :=
    Classification.Proofs.CopyShape.mem_realNodes_of_cell' (ControlProof.cell?_ref (M := M) u)
      (show 1 ≤ u.2.val from hu)
  obtain ⟨p', hp'⟩ := Recon.RowLaw.nodeAt_of_mem hmem
  obtain ⟨hmem', hrow'⟩ := Recon.RowLaw.nodeAt_spec hp'
  have := realNodes_eq_of_official hV hmem' hmem hrow'
  rw [this] at hp'
  exact hp'

/-- **The test from a node of the cone.** -/
theorem ascends_of_cone {s : List Nat} (hb : Canonical.build s = .ok M) {ctx : Context}
    (hsrc : ctx.source = M) {cr : Nat} (hroot : ctx.rootColumn = cr) {ρr : Ref} {ρc : Cell}
    {low nr : (Frame.ofMountain M).Node} (hlr : Frame.Real low) (hlx : low.1.val = ctx.x)
    (hpath : ParentPath (Frame.ofMountain M) low nr)
    (hh : (Frame.ofMountain M).height nr = (Frame.ofMountain M).height low) (hnr : nr.1.val = cr)
    (hZ : Official.official ((Frame.ofMountain M).cell low).row =
      referenceRow (Official.official ρc.row)) :
    ascends ctx (some (ρr, ρc)) = .ok true := by
  unfold ascends
  simp only
  rw [hsrc, hroot, ← hlx, ← hZ, nodeAt_of_node hb low hlr]
  exact reach_of_path hb hpath hh hnr _ (by omega)


/-- **The frame form of `x ascends ⇒ l ascends`.** -/
theorem cone_leg_of_cone {F : Frame} {root rho : F.Node} {cap : Row}
    (S : Cone.Setup F root rho cap) {u w p : F.Node} (hcone : Cone.Cone F root u.1)
    (hur : u.1 ≠ root.1) (hwr : Real w) (hwu : F.upper w = some u) (hC : F.height rho < F.height u)
    (hcap : F.height u < cap) (hp : F.P w = some p) :
    Cone.Cone F root p.1 ∧ F.height root ≤ F.height p := by
  have hO := S.ordered
  obtain ⟨hwc, hwi⟩ := upper_spec hwu
  have hL : F.height root < F.height u := lt_of_le_of_lt S.L_le_C hC
  obtain ⟨w', hw'r, hw'u, hw'c, hLw'⟩ := S.lower hcone hL
  have hww : w' = w := by
    obtain ⟨_, h1⟩ := upper_spec hw'u
    rcases w' with ⟨c1, i1⟩
    rcases w with ⟨c2, i2⟩
    dsimp only at hw'c hwc h1 hwi
    have hc12 : c1 = c2 := hw'c.trans hwc
    subst hc12
    have : i1 = i2 := Fin.ext (by omega)
    subst this
    rfl
  subst hww
  exact S.left_in_cone hcone hur hwr hwu hw'c hLw' hcap hp
    (fun hwC => S.main w'.1.val w' p rfl (by rw [hw'c]; exact hcone) hwr hwC
      (lt_trans (Cone.height_lt_of_index_lt hO hw'c (by omega)) hcap) hp)

/-- **The frame form of `l ascends ⇒ x ascends`.** -/
theorem cone_of_cone_leg {F : Frame} {root rho : F.Node} {cap : Row}
    (S : Cone.Setup F root rho cap) {u w p : F.Node} (hwr : Real w) (hwu : F.upper w = some u)
    (hC : F.height rho < F.height u) (hp : F.P w = some p) (hcone : Cone.Cone F root p.1) :
    Cone.Cone F root u.1 := by
  have hN := S.normal
  have hO := S.ordered
  obtain ⟨hwc, _⟩ := upper_spec hwu
  obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
  -- `p` is not below `low`
  have hpl : F.height low ≤ F.height p := by
    by_contra hn
    have hlt : F.height p < F.height low := lt_of_not_ge hn
    have hidx : p.2.val < low.2.val := by
      by_contra hn
      exact absurd hlt (not_lt.mpr (Cone.height_le_of_index_le hO hlc (by omega)))
    have hlen : p.2.val + 1 < F.length p.1 := by
      have := idx_lt_len (F := F) hlc.symm
      omega
    have hup := Cone.upper_of_lt hlen
    have hub := father_upper_bound_nodes hN hp hwu hup
    have hle : F.height ⟨p.1, ⟨p.2.val + 1, hlen⟩⟩ ≤ F.height low :=
      Cone.height_le_of_index_le hO hlc.symm (by dsimp only; omega)
    have h1 : F.height u ≤ F.height root := by rw [← hlh]; exact hub.trans hle
    exact absurd (lt_of_le_of_lt h1 (lt_of_le_of_lt S.L_le_C hC)) (lt_irrefl _)
  obtain ⟨v, hvr, hvc, _, hvh, hvpath⟩ := P_rowShadow hN hp low hlr hlc hpl
  exact ⟨v, hvr, hvc.trans hwc.symm, hvh.trans hlh, hvpath.trans hlpath⟩

/-- **A column and the leg column of a node above the root top ascend together.** -/
theorem ascAgree {s : List Nat} (hb : Canonical.build s = .ok M) {cr x : Nat} (hcx : cr < x)
    {k : Nat} {cp : Cell} (hk : 1 ≤ k) (hcp : cell? M ⟨x, k⟩ = some cp) {lref : Ref}
    (hl : cp.left = some lref) (hlcr : cr < lref.column)
    {d : Nat} {S : Row} {ρr : Ref} {ρc : Cell} (hρ : topIn M cr (d + 2) S = some (ρr, ρc))
    (hS : inRegion (d + 2) S (Official.official cp.row) = true)
    (hlt : Official.official ρc.row < Official.official cp.row)
    (ctx ctx' : Context) (hsrc : ctx.source = M) (hsrc' : ctx'.source = M)
    (hroot : ctx.rootColumn = cr) (hroot' : ctx'.rootColumn = cr) (hx : ctx.x = x)
    (hx' : ctx'.x = lref.column) :
    ascends ctx (some (ρr, ρc)) = .ok true ↔ ascends ctx' (some (ρr, ρc)) = .ok true := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  -- the node `u = (x, k)`
  obtain ⟨nu, hnuref, hnucell⟩ := ControlProof.node_of_cell? hcp
  have hnur : Frame.Real nu := by
    show 0 < nu.2.val
    have : k = nu.2.val := by
      have := congrArg Ref.index hnuref
      simpa [Frame.ref] using this.symm
    omega
  have hnuc : nu.1.val = x := by
    have := congrArg Ref.column hnuref
    simpa [Frame.ref] using this
  have hnuh : (Frame.ofMountain M).height nu = cp.row := by
    show ((Frame.ofMountain M).cell nu).row = cp.row
    rw [hnucell]
  have hcp1 : (1 : Row) ≤ cp.row := by rw [← hnuh]; exact Frame.one_le_height hO hnur
  -- the top `ρ`
  obtain ⟨hρmem, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
  obtain ⟨_, hρ1, hρcell⟩ := Classification.mem_realNodes hρmem
  simp only at hρ1 hρcell
  obtain ⟨nρ0, hnρ0ref, hnρ0cell⟩ := ControlProof.node_of_cell? hρcell
  have hnρ0r : Frame.Real nρ0 := by
    show 0 < nρ0.2.val
    have : ρr.index = nρ0.2.val := by
      have := congrArg Ref.index hnρ0ref
      simpa [Frame.ref] using this.symm
    omega
  have hρrow1 : (1 : Row) ≤ ρc.row := by
    rw [← hnρ0cell]; exact Frame.one_le_height hO hnρ0r
  have hρu : ρc.row < cp.row := Recon.row_lt_of_official hcp1 hlt
  -- the node `w` below `u` and its parent `p` in the leg column
  have hlow : (Frame.ofMountain M).height nρ0 < (Frame.ofMountain M).height nu := by
    show ((Frame.ofMountain M).cell nρ0).row < ((Frame.ofMountain M).cell nu).row
    rw [hnρ0cell, hnucell]; exact hρu
  obtain ⟨w, hwr, hwu, hwc, _⟩ := real_lower_of_height_lt hO hnρ0r hlow
  obtain ⟨p, hp, _, _, hleft⟩ := hN.upper_step w nu hwr hwu
  have hlp : lref = Frame.ref p := by
    have h1 : ((Frame.ofMountain M).cell nu).left = some lref := by rw [hnucell]; exact hl
    exact Option.some.inj (h1.symm.trans hleft)
  have hpc : p.1.val = lref.column := by rw [hlp]; rfl
  -- the cap
  have hcap : (Frame.ofMountain M).height nu < Row.bump ρc.row (d + 1) := by
    rw [hnuh]
    have h := lt_bump_of_inRegion hρreg hS
    rw [← Recon.RowLaw.official_bump hρrow1 (d + 1)] at h
    exact Recon.row_lt_of_official (hρrow1.trans (le_of_lt (Row.lt_bump _ _))) h
  constructor
  · intro hasc
    obtain ⟨aref, acl, hna, hra⟩ := ascClean_of_ascends hasc
    rw [hsrc, hx] at hna
    rw [hsrc, hroot, hx] at hra
    obtain ⟨nr, nρ, na, _, hSetup, hnrc, hnac, hcone, hnρh, _, _, _, _, hZ⟩ :=
      ascSetup hb hcx hρ hna hra
    have hconeu : Cone.Cone (Frame.ofMountain M) nr nu.1 := by
      have : nu.1 = na.1 := Fin.ext (by rw [hnuc, hnac])
      rw [this]; exact hcone
    have hur : nu.1 ≠ nr.1 := by
      intro h
      have := congrArg Fin.val h
      rw [hnuc, hnrc] at this
      omega
    have hC : (Frame.ofMountain M).height nρ < (Frame.ofMountain M).height nu := by
      rw [hnρh, hnuh]; exact hρu
    obtain ⟨⟨low, hlr, hlc, hlh, hlpath⟩, _⟩ :=
      cone_leg_of_cone hSetup hconeu hur hwr hwu hC hcap hp
    refine ascends_of_cone hb hsrc' hroot' hlr ?_ hlpath hlh.symm hnrc ?_
    · rw [hx', ← hpc, hlc]
    · have : ((Frame.ofMountain M).cell low).row = ((Frame.ofMountain M).cell nr).row := hlh
      rw [this, hZ]
  · intro hasc
    obtain ⟨aref, acl, hna, hra⟩ := ascClean_of_ascends hasc
    rw [hsrc', hx'] at hna
    rw [hsrc', hroot', hx'] at hra
    obtain ⟨nr, nρ, na, _, hSetup, hnrc, hnac, hcone, hnρh, _, _, _, _, hZ⟩ :=
      ascSetup hb hlcr hρ hna hra
    have hconep : Cone.Cone (Frame.ofMountain M) nr p.1 := by
      have : p.1 = na.1 := Fin.ext (by rw [hpc, hnac])
      rw [this]; exact hcone
    have hC : (Frame.ofMountain M).height nρ < (Frame.ofMountain M).height nu := by
      rw [hnρh, hnuh]; exact hρu
    obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := cone_of_cone_leg hSetup hwr hwu hC hp hconep
    refine ascends_of_cone hb hsrc hroot hlr ?_ hlpath hlh.symm hnrc ?_
    · rw [hx, ← hnuc, hlc]
    · have : ((Frame.ofMountain M).cell low).row = ((Frame.ofMountain M).cell nr).row := hlh
      rw [this, hZ]

end OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.ascAgree
