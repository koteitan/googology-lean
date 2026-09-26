/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LiftLegRightProof.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerFixCone
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsPaRow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeftItems
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeItems

set_option backward.do.legacy false

/-!
# `LiftLegRight` holds (a proof with small imports)

`LiftLegRight` (`ChainCorrLegLeftItems.lean`, about `M(s)` only): let `x` (`c_r < x ≤ x₀`) ascend
in a region `S` (level `d + 2`, below `τ`) whose root-column top is `ρ`. Then every node of `x` in
a slot `S[k]` with `k ≥ h_S(ρ)` has its leg at or right of `c_r`.

The proof is the one of `Recon/ParentBelowLowerFixLiftLeg.lean` (`ascLegs`: *every* real node of
`x` in `S` has its leg at or right of `c_r`), with the tools of
`Recon/ParentBelowLowerFixConeApply.lean` that it needs repeated here. So this file depends only on
the frame statement `Cone.Setup.legRight` (`Recon/ParentBelowLowerFixCone.lean`, which imports
only the geometry files) and on tracked files; it does not import the files of the
`LowerParentBelowHolds` route (`ParentBelowLowerFixMain`, `ParentBelowLowerFixRule`, ...).

* nodes above the row `C` of `ρ`: `Cone.Setup.legRight`;
* nodes at or below `C`: the node `(x, C)` of `x` has its leg at or right of `c_r`, and going down a
  column the leg does not move left (`ChainCorr.rawParent_column_le_left`).

Main results: `liftLegRight`, `plainLegLeftRow`.
-/

namespace OmegaY.Official.Recon.LowerPB.LiftLegPf

open Canonical Expansion Classification Reserve
open OmegaY.Geometry OmegaY.Geometry.Frame
open Classification.Proofs.ChainCorr

/-! ## Rows -/

/-- Every row of a region of level `d + 2` containing `a` is below `bump a (d + 1)`. -/
theorem lt_bump_of_inRegion {d : Nat} {S a r : Row} (ha : inRegion (d + 2) S a = true)
    (hr : inRegion (d + 2) S r = true) : r < Row.bump a (d + 1) := by
  rw [Recon.RowLaw.inRegion_iff'] at ha hr
  apply Row.lt_iff.mpr
  refine ⟨d + 1, ?_, ?_⟩
  · intro j hj
    rw [Row.coeff_bump_high hj]
    change r.coeff j = a.coeff j
    rw [hr j (by omega), ha j (by omega)]
  · rw [Row.coeff_bump_at]
    change r.coeff (d + 1) < a.coeff (d + 1) + 1
    rw [hr (d + 1) (by omega), ha (d + 1) (by omega)]
    omega

/-- A row above `a` outside the region of level `d + 2` of `a` is at or above `bump a (d + 1)`. -/
theorem bump_le_of_not_inRegion {d : Nat} {S a r : Row} (ha : inRegion (d + 2) S a = true)
    (hlt : a < r) (hr : inRegion (d + 2) S r = false) : Row.bump a (d + 1) ≤ r := by
  have hj : ¬ Row.jump a r ≤ d + 1 := by
    intro h
    have hin : inRegion (d + 2) S r = true := by
      rw [Recon.RowLaw.inRegion_iff'] at ha ⊢
      intro k hk
      have := Row.jump_le_iff.mp h k (by omega)
      change r.coeff k = S.coeff k
      rw [← ha k hk]
      exact this.symm
    rw [hin] at hr
    cases hr
  exact (Row.bump_mono_exponent a (by omega : d + 1 ≤ Row.jump a r - 1)).trans
    (Row.bump_last_le hlt)

/-- `a < h` gives `bump a 0 ≤ h`. -/
theorem bump0_le_of_lt {a h : Row} (hlt : a < h) : Row.bump a 0 ≤ h :=
  (Row.bump_mono_exponent a (Nat.zero_le _)).trans (Row.bump_last_le hlt)

theorem le_of_official_le {a b : Row} (hb : (1 : Row) ≤ b)
    (h : Official.official a ≤ Official.official b) : a ≤ b := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  exact absurd h (not_le.mpr (Recon.official_strictMono hb hlt))

/-! ## Frames of `M(s)` -/

variable {M : Mountain}

theorem idx_lt_len {F : Frame} {u v : F.Node} (hc : u.1 = v.1) : v.2.val < F.length u.1 := by
  have := v.2.isLt
  rcases v with ⟨c, i⟩
  dsimp only at hc
  subst hc
  exact this

theorem P_of_rawParent (hN : (Frame.ofMountain M).Normal) {u : (Frame.ofMountain M).Node}
    (hu : Frame.Real u) {q : Ref} (h : Reserve.rawParent M (Frame.ref u) = some q) :
    ∃ p, (Frame.ofMountain M).P u = some p ∧ Frame.ref p = q := by
  have h1 := ControlProof.rawParent_ref (M := M) u
  rw [h] at h1
  cases hup : (Frame.ofMountain M).upper u with
  | none => rw [hup] at h1; cases h1
  | some v =>
    rw [hup, Option.bind_some] at h1
    obtain ⟨np, hlk, _, _⟩ := hN.toOrdered.stored_valid v q h1.symm
    have hnp : Frame.ref np = q := Frame.lookup_spec hlk
    have hleft : ((Frame.ofMountain M).cell v).left = some (Frame.ref np) := by
      rw [hnp]; exact h1.symm
    have hraw := Frame.rawParent_eq_of_upper_left hup hleft
    exact ⟨np, (hN.rawParent_eq_P hu).symm.trans hraw, hnp⟩

/-- **The ascension test is a path of numerical parents at one height.** -/
theorem reach_path {s : List Nat} (hb : Canonical.build s = .ok M) {cr : Nat} :
    ∀ (f : Nat) (u : (Frame.ofMountain M).Node), Frame.Real u →
      reachesRoot M cr f (Frame.ref u) = .ok true →
      ∃ r : (Frame.ofMountain M).Node, r.1.val = cr ∧
        (Frame.ofMountain M).height r = (Frame.ofMountain M).height u ∧
        ParentPath (Frame.ofMountain M) u r := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  intro f
  induction f with
  | zero =>
    intro u _ h
    simp [reachesRoot, throw, throwThe, MonadExceptOf.throw] at h
  | succ f ih =>
    intro u hu h
    by_cases hc : u.1.val ≤ cr
    · have hcol : (Frame.ref u).column ≤ cr := hc
      simp only [reachesRoot, if_pos hcol, pure, Except.pure, Except.ok.injEq,
        decide_eq_true_eq] at h
      exact ⟨u, h, rfl, .refl _⟩
    · obtain ⟨q, hw, hrq⟩ := CutParts.reachesRoot_next (show cr < (Frame.ref u).column by
        change cr < u.1.val; omega) h
      obtain ⟨col, cell', upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
        Recon.RowLaw.weakParent_some hw
      have hraw : Reserve.rawParent M (Frame.ref u) = some q := by
        simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
      obtain ⟨p, hp, hpq⟩ := P_of_rawParent hN hu hraw
      have hcu := ControlProof.cell?_ref (M := M) u
      have hcu' : cell? M (Frame.ref u) = some cell' := by simp [cell?, hcol, hcell]
      have hcue : (Frame.ofMountain M).cell u = cell' := Option.some.inj (hcu.symm.trans hcu')
      obtain ⟨colq, hcolq, hcq⟩ := cellAt_ok_iff.mp hpc
      have hcp := ControlProof.cell?_ref (M := M) p
      have hcp' : cell? M (Frame.ref p) = some parentCell := by
        rw [hpq]; simp [cell?, hcolq, hcq]
      have hcpe : (Frame.ofMountain M).cell p = parentCell := Option.some.inj (hcp.symm.trans hcp')
      have hph : (Frame.ofMountain M).height p = (Frame.ofMountain M).height u := by
        show ((Frame.ofMountain M).cell p).row = ((Frame.ofMountain M).cell u).row
        rw [hcpe, hcue, hprow]
      have hpr : Frame.Real p := Cone.real_of_one_le_height hO
        (by rw [hph]; exact Frame.one_le_height hO hu)
      obtain ⟨r, hrc, hrh, hpath⟩ := ih p hpr (by rw [hpq]; exact hrq)
      exact ⟨r, hrc, hrh.trans hph, .cons hp hpath⟩

/-- The raw parent of a real node is its parent (frame form). -/
theorem rawParent_of_P' (hN : (Frame.ofMountain M).Normal) {u p : (Frame.ofMountain M).Node}
    (hu : Frame.Real u) (hP : (Frame.ofMountain M).P u = some p) :
    Reserve.rawParent M (Frame.ref u) = some (Frame.ref p) := by
  obtain ⟨v, hv⟩ := hN.upper_of_parent hP
  have hleft := Cone.left_of_parent hN hu hv hP
  have h1 := ControlProof.rawParent_ref (M := M) u
  rw [hv, Option.bind_some, hleft] at h1
  exact h1

/-- **Legs do not move left going down a column.** If every left end of the node `v` is at or
right of `cr`, so is every left end of a real node below `v` in the same column. -/
theorem legs_below {s : List Nat} (hb : Canonical.build s = .ok M) {cr : Nat}
    {v : (Frame.ofMountain M).Node}
    (hv : ∀ l, ((Frame.ofMountain M).cell v).left = some l → cr ≤ l.column) :
    ∀ (n : Nat) (w : (Frame.ofMountain M).Node), w.1 = v.1 → v.2.val = w.2.val + n →
      Frame.Real w → ∀ l, ((Frame.ofMountain M).cell w).left = some l → cr ≤ l.column := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  intro n
  induction n with
  | zero =>
    intro w hwc hwi _ l hl
    have hwv : w = v := by
      rcases w with ⟨c1, i1⟩
      rcases v with ⟨c2, i2⟩
      dsimp only at hwc hwi
      subst hwc
      have : i1 = i2 := Fin.ext (by omega)
      subst this
      rfl
    subst hwv
    exact hv l hl
  | succ n ih =>
    intro w hwc hwi hw l hl
    have hlen : w.2.val + 1 < (Frame.ofMountain M).length w.1 := by
      have := idx_lt_len hwc
      omega
    have hup := Cone.upper_of_lt hlen
    obtain ⟨p, hp, _, _, hleft⟩ := hN.upper_step w _ hw hup
    have hraw := rawParent_of_P' hN hw hp
    have hle := rawParent_column_le_left hb (ControlProof.cell?_ref (M := M) w)
      (show 0 < (Frame.ref w).index from hw) hl hraw
    have := ih ⟨w.1, ⟨w.2.val + 1, hlen⟩⟩ hwc (by dsimp only; omega)
      (show 0 < w.2.val + 1 by omega) (Frame.ref p) hleft
    exact this.trans hle

/-- **The frame of an ascension.** -/
theorem ascSetup {s : List Nat} (hb : Canonical.build s = .ok M) {cr x : Nat} (hcx : cr < x)
    {d : Nat} {S : Row} {ρr : Ref} {ρc : Cell} (hρ : topIn M cr (d + 2) S = some (ρr, ρc))
    {aref : Ref} {acl : Cell}
    (hna : nodeAt M x (referenceRow (Official.official ρc.row)) = some (aref, acl))
    (hra : reachesRoot M cr (x + 1) aref = .ok true) :
    ∃ nr nρ na nC : (Frame.ofMountain M).Node,
      Cone.Setup (Frame.ofMountain M) nr nρ (Row.bump ρc.row (d + 1)) ∧ nr.1.val = cr ∧
      na.1.val = x ∧ Cone.Cone (Frame.ofMountain M) nr na.1 ∧
      (Frame.ofMountain M).height nρ = ρc.row ∧ nC.1 = na.1 ∧ Frame.Real nC ∧
      (Frame.ofMountain M).height nC = ρc.row ∧
      (∀ l, ((Frame.ofMountain M).cell nC).left = some l → cr ≤ l.column) ∧
      Official.official ((Frame.ofMountain M).cell nr).row =
        referenceRow (Official.official ρc.row) := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hna
  simp only at hac ha1 hacell harow
  obtain ⟨na, hnaref, hnacell⟩ := ControlProof.node_of_cell? hacell
  have hnar : Frame.Real na := by
    show 0 < na.2.val
    have : aref.index = na.2.val := by rw [← hnaref]; rfl
    omega
  have hnac : na.1.val = x := by
    have : aref.column = na.1.val := by rw [← hnaref]; rfl
    omega
  obtain ⟨nr, hnrc, hnrh, hpath⟩ :=
    reach_path hb (x + 1) na hnar (by rw [hnaref]; exact hra)
  have hnrr : Frame.Real nr := Cone.real_of_one_le_height hO
    (by rw [hnrh]; exact Frame.one_le_height hO hnar)
  -- the first step of the path
  obtain ⟨next, hnext, hncr⟩ : ∃ next, (Frame.ofMountain M).P na = some next ∧
      cr ≤ next.1.val := by
    cases hpath with
    | refl => omega
    | @cons _ next _ hp rest =>
      exact ⟨next, hp, by rw [← hnrc]; exact rest.column_le hO⟩
  -- the top `ρ` of the root column in `S`
  obtain ⟨hρmem, hρreg, hρmax⟩ := Recon.RowLaw.topIn_spec hρ
  obtain ⟨hρc, hρ1, hρcell⟩ := Classification.mem_realNodes hρmem
  simp only at hρc hρ1 hρcell
  obtain ⟨nρ, hnρref, hnρcell⟩ := ControlProof.node_of_cell? hρcell
  have hnρc : nρ.1 = nr.1 := by
    apply Fin.ext
    have h1 : nρ.1.val = ρr.column := by rw [← hnρref]; rfl
    rw [h1, hρc, hnrc]
  have hnρr : Frame.Real nρ := by
    show 0 < nρ.2.val
    have : ρr.index = nρ.2.val := by rw [← hnρref]; rfl
    omega
  have hρrow1 : (1 : Row) ≤ ρc.row := by
    rw [← hnρcell]; exact Frame.one_le_height hO hnρr
  have hnah : (Frame.ofMountain M).height na = acl.row := by
    show ((Frame.ofMountain M).cell na).row = acl.row
    rw [hnacell]
  have hnρh : (Frame.ofMountain M).height nρ = ρc.row := by
    show ((Frame.ofMountain M).cell nρ).row = ρc.row
    rw [hnρcell]
  have hacl1 : (1 : Row) ≤ acl.row := by rw [← hnah]; exact Frame.one_le_height hO hnar
  -- the shape, and the node `nC` of `x` at the height of `ρ`
  have hshape : (nρ = nr ∨ ((Frame.ofMountain M).upper nr = some nρ ∧
      (Frame.ofMountain M).height nρ = Row.bump ((Frame.ofMountain M).height nr) 0)) ∧
      ∃ nC : (Frame.ofMountain M).Node, nC.1 = na.1 ∧ Frame.Real nC ∧
        (Frame.ofMountain M).height nC = ρc.row ∧
        (∀ l, ((Frame.ofMountain M).cell nC).left = some l → cr ≤ l.column) := by
    by_cases h0 : 0 < (Official.official ρc.row).coeff 0
    · have hbump : Row.bump acl.row 0 = ρc.row := by
        apply CutParts.official_inj' (by
          exact hacl1.trans (le_of_lt (Row.lt_bump _ 0))) hρrow1
        rw [Recon.RowLaw.official_bump hacl1 0, harow]
        exact Recon.RowLaw.referenceRow_bump h0
      have hhρ : (Frame.ofMountain M).height nρ = Row.bump ((Frame.ofMountain M).height nr) 0 := by
        rw [hnρh, hnrh, hnah, hbump]
      refine ⟨Or.inr ⟨?_, hhρ⟩, ?_⟩
      · have hlt : (Frame.ofMountain M).height nr < (Frame.ofMountain M).height nρ := by
          rw [hhρ]; exact Row.lt_bump _ 0
        have hi : nr.2.val < nρ.2.val := by
          by_contra hn
          exact absurd hlt (not_lt.mpr (Cone.height_le_of_index_le hO hnρc (by omega)))
        have hlen : nr.2.val + 1 < (Frame.ofMountain M).length nr.1 := by
          have := idx_lt_len hnρc.symm
          omega
        have hup := Cone.upper_of_lt hlen
        rw [hup]
        congr 1
        apply node_eq_of_column_height hO
          (show (⟨nr.1, ⟨nr.2.val + 1, hlen⟩⟩ : (Frame.ofMountain M).Node).1 = nρ.1 from
            hnρc.symm)
        apply le_antisymm
        · exact Cone.height_le_of_index_le hO hnρc.symm (by dsimp only; omega)
        · rw [hhρ]
          exact bump0_le_of_lt (Cone.height_lt_of_index_lt hO rfl (by dsimp only; omega))
      · -- `nC` is the node above `na`; its left end is the in-row parent `next`
        obtain ⟨v, hv⟩ := hN.upper_of_parent hnext
        obtain ⟨hvc, hvi⟩ := Frame.upper_spec hv
        have hleft := Cone.left_of_parent hN hnar hv hnext
        have hnh : (Frame.ofMountain M).height next = (Frame.ofMountain M).height na := by
          apply le_antisymm (Frame.P_height_le hO hnext)
          cases hpath with
          | refl => omega
          | @cons _ next' _ hp rest =>
            have := Option.some.inj (hp.symm.trans hnext)
            subst this
            rw [← hnrh]
            exact rest.height_le hO
        refine ⟨v, hvc, by show 0 < v.2.val; omega, ?_, ?_⟩
        · rw [← aboveHeight_of_upper hv, hN.above_row hnext, hnh, Row.B_self, hnah, hbump]
        · intro l hl
          rw [hleft] at hl
          have := Option.some.inj hl
          subst this
          exact hncr
    · have hZ : referenceRow (Official.official ρc.row) = Official.official ρc.row := by
        unfold referenceRow
        rw [if_neg h0]
      have heq : acl.row = ρc.row :=
        CutParts.official_inj' hacl1 hρrow1 (by rw [harow, hZ])
      refine ⟨Or.inl (node_eq_of_column_height hO hnρc (by rw [hnρh, hnrh, hnah, heq])), ?_⟩
      -- `nC = na`; its raw parent `next` is at or left of its leg
      refine ⟨na, rfl, hnar, by rw [hnah, heq], ?_⟩
      intro l hl
      have hraw := rawParent_of_P' hN hnar hnext
      have hle := rawParent_column_le_left hb (ControlProof.cell?_ref (M := M) na)
        (show 0 < (Frame.ref na).index from hnar) hl hraw
      exact hncr.trans hle
  obtain ⟨hshape', nC, hnCc, hnCr, hnCh, hnCleg⟩ := hshape
  -- the cap
  have hcapo : Official.official (Row.bump ρc.row (d + 1)) =
      Row.bump (Official.official ρc.row) (d + 1) :=
    Recon.RowLaw.official_bump hρrow1 (d + 1)
  have hSetup : Cone.Setup (Frame.ofMountain M) nr nρ (Row.bump ρc.row (d + 1)) := by
    refine ⟨hN, hnrr, hnρc, hshape', ?_, ?_⟩
    · rw [hnρh]; exact Row.lt_bump _ _
    · intro v hv
      obtain ⟨hvc, hvi⟩ := Frame.upper_spec hv
      have hvr : Frame.Real v := by show 0 < v.2.val; omega
      have hv1 := Frame.one_le_height hO hvr
      have hvcell := ControlProof.cell?_ref (M := M) v
      have hvmem : (Frame.ref v, (Frame.ofMountain M).cell v) ∈ realNodes M cr := by
        have h := Classification.Proofs.CopyShape.mem_realNodes_of_cell' hvcell (by
          show 1 ≤ v.2.val; omega)
        have hvcol : (Frame.ref v).column = cr := by
          show v.1.val = cr
          rw [hvc, hnρc, hnrc]
        rw [hvcol] at h
        exact h
      have hnot : inRegion (d + 2) S
          (Official.official ((Frame.ofMountain M).cell v).row) = false := by
        by_contra hn
        have hin : inRegion (d + 2) S
            (Official.official ((Frame.ofMountain M).cell v).row) = true := by simpa using hn
        have := hρmax _ hvmem hin
        have hri : ρr.index = nρ.2.val := by rw [← hnρref]; rfl
        change v.2.val ≤ ρr.index at this
        omega
      have hlt : ρc.row < ((Frame.ofMountain M).cell v).row := by
        rw [← hnρh]
        exact Cone.height_lt_of_index_lt hO hvc.symm (by omega)
      have hle := bump_le_of_not_inRegion hρreg
        (Recon.official_strictMono hρrow1 hlt) hnot
      rw [← hcapo] at hle
      exact le_of_official_le hv1 hle
  have hZr : Official.official ((Frame.ofMountain M).cell nr).row =
      referenceRow (Official.official ρc.row) := by
    have : ((Frame.ofMountain M).cell nr).row = acl.row := by
      show (Frame.ofMountain M).height nr = acl.row
      rw [hnrh, hnah]
    rw [this, harow]
  exact ⟨nr, nρ, na, nC, hSetup, hnrc, hnac, ⟨na, hnar, rfl, hnrh.symm, hpath⟩, hnρh, hnCc,
    hnCr, hnCh, hnCleg, hZr⟩

/-- **Every node of an ascending column in the region has its leg at or right of `c_r`.** -/
theorem ascLegs {s : List Nat} (hb : Canonical.build s = .ok M) {cr x : Nat} (hcx : cr < x)
    {d : Nat} {S : Row} {ρr : Ref} {ρc : Cell} (hρ : topIn M cr (d + 2) S = some (ρr, ρc))
    {aref : Ref} {acl : Cell}
    (hna : nodeAt M x (referenceRow (Official.official ρc.row)) = some (aref, acl))
    (hra : reachesRoot M cr (x + 1) aref = .ok true)
    {k : Nat} {c : Cell} (hk : 1 ≤ k) (hc : cell? M ⟨x, k⟩ = some c)
    (hS : inRegion (d + 2) S (Official.official c.row) = true)
    {l : Ref} (hl : c.left = some l) : cr ≤ l.column := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨nr, nρ, na, nC, hSetup, hnrc, hnac, hcone, hnρh, hnCc, hnCr, hnCh, hnCleg, _⟩ :=
    ascSetup hb hcx hρ hna hra
  obtain ⟨_, hρreg, _⟩ := Recon.RowLaw.topIn_spec hρ
  have hρrow1 : (1 : Row) ≤ ρc.row := by
    rw [← hnρh]; exact Frame.one_le_height hO hSetup.rhoReal
  obtain ⟨nu, hnuref, hnucell⟩ := ControlProof.node_of_cell? hc
  have hnur : Frame.Real nu := by
    show 0 < nu.2.val
    have : k = nu.2.val := by
      have := congrArg Ref.index hnuref
      simpa [Frame.ref] using this.symm
    omega
  have hnuc : nu.1 = na.1 := by
    apply Fin.ext
    have h1 : nu.1.val = x := by
      have := congrArg Ref.column hnuref
      simpa [Frame.ref] using this
    rw [h1, hnac]
  have hc1 : (1 : Row) ≤ c.row := by rw [← hnucell]; exact Frame.one_le_height hO hnur
  have hnuh : (Frame.ofMountain M).height nu = c.row := by
    show ((Frame.ofMountain M).cell nu).row = c.row
    rw [hnucell]
  have hlnu : ((Frame.ofMountain M).cell nu).left = some l := by rw [hnucell]; exact hl
  by_cases hhigh : Official.official ρc.row < Official.official c.row
  · have hC : (Frame.ofMountain M).height nρ < (Frame.ofMountain M).height nu := by
      rw [hnρh, hnuh]
      exact Recon.row_lt_of_official hc1 hhigh
    have hcap : (Frame.ofMountain M).height nu < Row.bump ρc.row (d + 1) := by
      rw [hnuh]
      have h := lt_bump_of_inRegion hρreg hS
      rw [← Recon.RowLaw.official_bump hρrow1 (d + 1)] at h
      exact Recon.row_lt_of_official (hρrow1.trans (le_of_lt (Row.lt_bump _ _))) h
    have hconeu : Cone.Cone (Frame.ofMountain M) nr nu.1 := by rw [hnuc]; exact hcone
    obtain ⟨w, hwr, hwu, _, _⟩ := hSetup.lower hconeu (lt_of_le_of_lt hSetup.L_le_C hC)
    obtain ⟨p, hp, _, _, hleft⟩ := hN.upper_step w nu hwr hwu
    have hge := hSetup.legRight hwu hwr hconeu hC hcap hp
    have hlp : l = Frame.ref p := Option.some.inj (hlnu.symm.trans hleft)
    rw [hlp]
    show cr ≤ p.1.val
    rw [← hnrc]
    exact hge
  · have hle : c.row ≤ ρc.row := le_of_official_le hρrow1 (le_of_not_gt hhigh)
    have hidx : nu.2.val ≤ nC.2.val :=
      Cone.index_le_of_height_le hO (hnuc.trans hnCc.symm) (by rw [hnuh, hnCh]; exact hle)
    exact legs_below hb hnCleg (nC.2.val - nu.2.val) nu (hnuc.trans hnCc.symm) (by omega)
      hnur l hlnu

/-- **`LiftLegRight` holds.** -/
theorem liftLegRight_holds : Classification.Proofs.ChainCorr.LegLeft.LiftLegRight := by
  intro s M t root hTop ctx hsrc hroot hx hxle d S r cl _ hρ hasc k _ q hq hin l hl
  obtain ⟨aref, acl, hna, hra⟩ := ascClean_of_ascends hasc
  rw [hsrc] at hna
  rw [hsrc, hroot] at hra
  obtain ⟨hqc, hq1, hqcell⟩ := Classification.mem_realNodes hq
  have hS : inRegion (d + 2) S (Official.official q.2.row) = true :=
    (Recon.RowLaw.inRegion_slot_iff.mp hin).1
  have hqcell' : cell? M ⟨ctx.x, q.1.index⟩ = some q.2 := by
    rw [← hqc]; exact hqcell
  exact ascLegs hTop.build hx hρ hna hra hq1 hqcell' hS hl

/-- **`PlainLegLeftRow` holds** (`ChainCorrLegLeft.lean`: a plain copy whose origin has its leg
left of `c_r` keeps the row of its origin), by `LegLeft.plainLegLeftRow_of_lift`. -/
theorem plainLegLeftRow_holds : Classification.Proofs.ChainCorr.LegLeft.PlainLegLeftRow :=
  Classification.Proofs.ChainCorr.LegLeft.plainLegLeftRow_of_lift liftLegRight_holds

/-- **`LiftLegRight` holds** (the same as `liftLegRight_holds`). -/
theorem liftLegRight : Classification.Proofs.ChainCorr.LegLeft.LiftLegRight := liftLegRight_holds

/-- **`PlainLegLeftRow` holds** (the same as `plainLegLeftRow_holds`). -/
theorem plainLegLeftRow : Classification.Proofs.ChainCorr.LegLeft.PlainLegLeftRow :=
  plainLegLeftRow_holds

end OmegaY.Official.Recon.LowerPB.LiftLegPf

#print axioms OmegaY.Official.Recon.LowerPB.LiftLegPf.ascLegs
#print axioms OmegaY.Official.Recon.LowerPB.LiftLegPf.liftLegRight
#print axioms OmegaY.Official.Recon.LowerPB.LiftLegPf.plainLegLeftRow
