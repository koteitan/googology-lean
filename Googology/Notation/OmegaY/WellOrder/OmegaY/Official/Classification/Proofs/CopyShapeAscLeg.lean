/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeAscLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerAsc
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawSeam

set_option backward.do.legacy false

/-!
# A column and the leg column of a node ascend together in every region below the node

A statement about `M(s)` only (`ascLeg`). Let `v = (x, k)` be a node of `M(s)`, `c_r < x`, whose
left end is in a column `ℓ ≥ c_r`, and let `ρ` be the top of the column `c_r` in a region `S`
with `row ρ < row v`. Then `x` ascends in `S` iff `ℓ` does.

Unlike `InnerRow.ascAgree` (`LegRowMatchInnerAsc.lean`), `v` need not lie in `S`, `ℓ = c_r` is
allowed, and `c_r` is any column left of `x` (not only the root column of an expansion).

## Proof

Let `w` be the node below `v` and `p = P(w)` its parent (in `ℓ`). The frame of an ascension
(`LiftLegPf.ascSetup`) gives the root `r` (the node of `c_r` at the reference row `Z` of `ρ`) and
the cone of `r`: the columns with a node at the height of `r` from which the numerical parents
reach `r` at that height (`Cone.Cone`).

* `ℓ` ascends ⇒ `x` ascends: `ℓ` is in the cone; `p` is not below the node of `ℓ` at the height
  of `r` (else `height v ≤ height (p⁺) ≤ height r`, `father_upper_bound_nodes`), so the row
  shadow of the edge `w → p` (`P_rowShadow`) puts `x` in the cone (`cone_of_cone_legF`, the proof
  of `InnerRow.cone_of_cone_leg` without the setting).
* `x` ascends ⇒ `ℓ` ascends: the cap-free form of the cone theorem (`mainF`): for a node `u` of a
  cone column with `height u ≥ height ρ`, the parent `P(u)` is in a cone column at height
  `≥ height r`, or it is left of `c_r`. The proof is the proof of `Cone.Setup.main`
  (`ParentBelowLowerFixCone.lean`) without the cap: where the search of the parent reaches the
  root column or a stored left end left of `c_r`, the rest of the search stays left of `c_r`
  (`Hit.column_le`). Applied to `w`, and since `ℓ ≥ c_r`, `ℓ` is in the cone.

## Numerical evidence

`reference/official/asc-leg.cjs` (with the root column of the expansion, nodes of `x` at or below
`v` in regions below `τ`): 0 failures in 12875856 checks (all legal inputs of length `≤ 6`,
entries `≤ 12`) and 207263509 checks (200000 random inputs, entries `≤ 40`). For every column
`c_r` and every region with `row ρ < row v`: 0 failures in 5364689 checks (the test of this
task).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.AscLeg

open Canonical Expansion Classification Reserve
open OmegaY.Geometry OmegaY.Geometry.Frame
open OmegaY.Official.Recon.LowerPB OmegaY.Official.Recon.LowerPB.LiftLegPf
open Classification.Proofs.ChainCorr
open Classification.Proofs.CopyShape.InnerRow

variable {F : Frame}

/-! ## The cone theorem without a cap -/

/-- The conclusion of the cap-free cone theorem for a parent `p`. -/
def ConclF (F : Frame) (root p : F.Node) : Prop :=
  (Cone.Cone F root p.1 ∧ F.height root ≤ F.height p) ∨ p.1.val < root.1.val

/-- The left end of the edge below a node `y` of a cone column (`y` not in the root column,
`height y > L`), given the cap-free theorem for the node below `y`. -/
theorem left_in_coneF {root rho : F.Node} {cap : Row} (S : Cone.Setup F root rho cap)
    {y w pl : F.Node} (hcone : Cone.Cone F root y.1)
    (hyr : y.1 ≠ root.1) (hwr : Real w) (hwy : F.upper w = some y) (hwc : w.1 = y.1)
    (hLw : F.height root ≤ F.height w) (hpl : F.P w = some pl)
    (hIH : F.height rho ≤ F.height w → ConclF F root pl) : ConclF F root pl := by
  by_cases hwC : F.height rho ≤ F.height w
  · exact hIH hwC
  · have hwL : F.height w = F.height root := by
      rcases S.C_cases with hCL | hCL
      · exact absurd (by rw [hCL]; exact hLw) hwC
      · exact Cone.row_eq_of_lt_bump0 hLw (by rw [← hCL]; exact lt_of_not_ge hwC)
    obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
    have he : low = w := node_eq_of_column_height S.ordered (hlc.trans hwc.symm)
      (hlh.trans hwL.symm)
    subst he
    obtain ⟨next, hnext, hnr, hnh, hnpath, _⟩ :=
      S.low_parent hlr hlh hlpath (by rw [hwc]; exact hyr)
    have : next = pl := Option.some.inj (hnext.symm.trans hpl)
    subst this
    exact Or.inl ⟨⟨next, hnr, rfl, hnh, hnpath⟩, hnh.ge⟩

/-- If the stored left end of `y` is left of the root column, so is every search from `Q(y)`. -/
theorem hit_left_of_left {root : F.Node} (hO : F.Ordered) {y pl y' p : F.Node} {t : Nat}
    (hleft : (F.cell y).left = some (ref pl)) (hQ : F.Q y = some y') (rest : Hit F t y' p)
    (hpl : pl.1.val < root.1.val) : p.1.val < root.1.val := by
  obtain ⟨left, hl, _, _, hqc, _⟩ := Q_spec hO hQ
  have hlp : left = pl := Executable.ref_injective F (Option.some.inj (hl.symm.trans hleft))
  subst hlp
  have h1 := rest.column_le hO
  have : y'.1.val = left.1.val := by rw [hqc]
  omega

/-- **The search from a candidate in the cone, without a cap.** -/
theorem traceF {root rho : F.Node} {cap : Row} (S : Cone.Setup F root rho cap) {u p : F.Node}
    (hIH : ∀ (w pw : F.Node), w.1.val < u.1.val → Cone.Cone F root w.1 → Real w →
      F.height rho ≤ F.height w → F.P w = some pw → ConclF F root pw)
    (hpu : 0 < F.value p ∧ F.value p < F.value u) :
    ∀ (c : Nat) (y : F.Node), y.1.val = c → y.1.val < u.1.val → Cone.Cone F root y.1 →
      F.height rho ≤ F.height y → F.height y ≤ F.height u → Hit F (F.value u) y p →
      ConclF F root p := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
  intro y hyc hyu hcone hyC hyh hit
  have hO := S.ordered
  have hyreal : Real y :=
    Cone.real_of_one_le_height hO ((one_le_height hO S.rhoReal).trans hyC)
  cases hit with
  | here _ _ => exact Or.inl ⟨hcone, S.L_le_C.trans hyC⟩
  | @next _ y' _ hreject hQ rest =>
    have hvy : F.value u ≤ F.value y := by
      by_contra h
      exact hreject ⟨hO.real_positive y hyreal, lt_of_not_ge h⟩
    by_cases hyr : y.1 = root.1
    · -- the search leaves the root column to the left
      right
      have h1 := rest.column_le hO
      have h2 := Q_column_lt hO hQ
      have : y.1.val = root.1.val := by rw [hyr]
      omega
    · obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
      rcases eq_or_lt_of_le (S.L_le_C.trans hyC) with hL | hL
      · -- `height y = L`: continue from the parent of `y`
        have he : low = y := node_eq_of_column_height hO hlc (hlh.trans hL)
        subst he
        obtain ⟨next, hnext, hnr, hnh, hnpath, hncol⟩ := S.low_parent hlr hlh hlpath hyr
        have hfull : Hit F (F.value u) low p := .next hreject hQ rest
        obtain ⟨r, h1, h2⟩ := hfull.loosen hvy
        have hr : F.P low = some r := by
          cases h1 with
          | here _ hs => exact absurd hs (lt_irrefl _)
          | next _ hQ2 rest2 => exact (P_iff hO).mpr ⟨_, hQ2, rest2⟩
        have : r = next := Option.some.inj (hr.symm.trans hnext)
        subst this
        exact ih r.1.val (by omega) r rfl (by omega) ⟨r, hnr, rfl, hnh, hnpath⟩
          (by rw [hnh, hL]; exact hyC) (by rw [hnh, hL]; exact hyh) h2
      · -- `height y > L`: the candidate of `y` stays in the cone, or leaves `c_r` to the left
        obtain ⟨w, hwr, hwy, hwc, hLw⟩ := S.lower ⟨low, hlr, hlc, hlh, hlpath⟩ hL
        obtain ⟨pl, hpl, _, _, hleft⟩ := S.normal.upper_step w y hwr hwy
        have hin := left_in_coneF S ⟨low, hlr, hlc, hlh, hlpath⟩ hyr hwr hwy hwc hLw hpl
          (fun hwC => hIH w pl (by rw [hwc]; exact hyu)
            (by rw [hwc]; exact ⟨low, hlr, hlc, hlh, hlpath⟩) hwr hwC hpl)
        rcases hin with hin | hin
        · obtain ⟨q, hq, hqc, hqC, hqy⟩ := S.Q_control hin.1 hin.2 hleft hyC
          have : y' = q := Option.some.inj (hQ.symm.trans hq)
          subst this
          have hqcol := Q_column_lt hO hq
          exact ih y'.1.val (by omega) y' rfl (by omega) (by rw [hqc]; exact hin.1) hqC
            (hqy.trans hyh) rest
        · exact Or.inr (hit_left_of_left hO hleft hQ rest hin)

/-- **The cone theorem without a cap.** For a node `u` of a cone column with
`height u ≥ height ρ`, the parent `P(u)` is in a cone column at height `≥ height root`, or it is
left of the root column. -/
theorem mainF {root rho : F.Node} {cap : Row} (S : Cone.Setup F root rho cap) :
    ∀ (c : Nat) (u p : F.Node), u.1.val = c → Cone.Cone F root u.1 → Real u →
      F.height rho ≤ F.height u → F.P u = some p → ConclF F root p := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c outer =>
  intro u
  generalize hi : u.2.val = i
  induction i using Nat.strongRecOn generalizing u with
  | ind i inner =>
  intro p hc hcone hreal hC hp
  have hO := S.ordered
  by_cases hroot : u.1 = root.1
  · right
    have := P_column_lt hO hp
    have h' : u.1.val = root.1.val := by rw [hroot]
    omega
  · obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
    rcases eq_or_lt_of_le (S.L_le_C.trans hC) with hL | hL
    · -- `u` is the node of its column at height `L`
      have he : low = u := node_eq_of_column_height hO hlc (hlh.trans hL)
      subst he
      obtain ⟨next, hnext, hnr, hnh, hnpath, _⟩ := S.low_parent hlr hlh hlpath hroot
      have : next = p := Option.some.inj (hnext.symm.trans hp)
      subst this
      exact Or.inl ⟨⟨next, hnr, rfl, hnh, hnpath⟩, hnh.ge⟩
    · obtain ⟨w, hwr, hwu, hwc, hLw⟩ := S.lower ⟨low, hlr, hlc, hlh, hlpath⟩ hL
      obtain ⟨pl, hpl, _, _, hleft⟩ := S.normal.upper_step w u hwr hwu
      have hwi : w.2.val < i := by obtain ⟨_, hi'⟩ := upper_spec hwu; omega
      have hin := left_in_coneF S ⟨low, hlr, hlc, hlh, hlpath⟩ hroot hwr hwu hwc hLw hpl
        (fun hwC => inner w.2.val hwi w rfl pl (by rw [hwc]; exact hc)
          (by rw [hwc]; exact ⟨low, hlr, hlc, hlh, hlpath⟩) hwr hwC hpl)
      obtain ⟨q', hQ', hit⟩ := (P_iff hO).mp hp
      rcases hin with hin | hin
      · obtain ⟨q, hq, hqc, hqC, hqu⟩ := S.Q_control hin.1 hin.2 hleft hC
        have : q' = q := Option.some.inj (hQ'.symm.trans hq)
        subst this
        have hqcol := Q_column_lt hO hq
        exact traceF S
          (fun w pw hw hwc' hwr' hwC' hpw => outer w.1.val (by omega) w pw rfl hwc' hwr' hwC' hpw)
          (P_value hO hp) q'.1.val q' rfl hqcol (by rw [hqc]; exact hin.1) hqC hqu hit
      · exact Or.inr (hit_left_of_left hO hleft hQ' hit hin)

/-- **`ℓ` in the cone ⇒ `x` in the cone** (the proof of `InnerRow.cone_of_cone_leg`, with only
normality and `height root < height u`). -/
theorem cone_of_cone_legF (hN : F.Normal) {root u w p : F.Node} (hwr : Real w)
    (hwu : F.upper w = some u) (hL : F.height root < F.height u) (hp : F.P w = some p)
    (hcone : Cone.Cone F root p.1) : Cone.Cone F root u.1 := by
  have hO := hN.toOrdered
  obtain ⟨hwc, _⟩ := upper_spec hwu
  obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hcone
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
    exact absurd (lt_of_le_of_lt h1 hL) (lt_irrefl _)
  obtain ⟨v, hvr, hvc, _, hvh, hvpath⟩ := P_rowShadow hN hp low hlr hlc hpl
  exact ⟨v, hvr, hvc.trans hwc.symm, hvh.trans hlh, hvpath.trans hlpath⟩

/-! ## The theorem -/

/-- **A column and the leg column of a node ascend together in every region whose root-column
top is below the node.** -/
theorem ascLeg {M : Mountain} {s : List Nat} (hb : Canonical.build s = .ok M) {cr x : Nat}
    (hcx : cr < x) {k : Nat} {cp : Cell} (hk : 1 ≤ k) (hcp : cell? M ⟨x, k⟩ = some cp)
    {lref : Ref} (hl : cp.left = some lref) (hlcr : cr ≤ lref.column)
    {d : Nat} {S : Row} {ρr : Ref} {ρc : Cell} (hρ : topIn M cr (d + 2) S = some (ρr, ρc))
    (hlt : Official.official ρc.row < Official.official cp.row)
    (ctx ctx' : Context) (hsrc : ctx.source = M) (hsrc' : ctx'.source = M)
    (hroot : ctx.rootColumn = cr) (hroot' : ctx'.rootColumn = cr) (hx : ctx.x = x)
    (hx' : ctx'.x = lref.column) :
    ascends ctx (some (ρr, ρc)) = .ok true ↔ ascends ctx' (some (ρr, ρc)) = .ok true := by
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  -- the node `v = (x, k)`
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
  obtain ⟨hρmem, _, _⟩ := Recon.RowLaw.topIn_spec hρ
  obtain ⟨_, hρ1, hρcell⟩ := Classification.mem_realNodes hρmem
  simp only at hρ1 hρcell
  obtain ⟨nρ0, hnρ0ref, hnρ0cell⟩ := ControlProof.node_of_cell? hρcell
  have hnρ0r : Frame.Real nρ0 := by
    show 0 < nρ0.2.val
    have : ρr.index = nρ0.2.val := by
      have := congrArg Ref.index hnρ0ref
      simpa [Frame.ref] using this.symm
    omega
  have hρu : ρc.row < cp.row := Recon.row_lt_of_official hcp1 hlt
  -- the node `w` below `v` and its parent `p` in the leg column
  have hlow : (Frame.ofMountain M).height nρ0 < (Frame.ofMountain M).height nu := by
    show ((Frame.ofMountain M).cell nρ0).row < ((Frame.ofMountain M).cell nu).row
    rw [hnρ0cell, hnucell]; exact hρu
  obtain ⟨w, hwr, hwu, hwc, _⟩ := real_lower_of_height_lt hO hnρ0r hlow
  obtain ⟨p, hp, _, _, hleft⟩ := hN.upper_step w nu hwr hwu
  have hlp : lref = Frame.ref p := by
    have h1 : ((Frame.ofMountain M).cell nu).left = some lref := by rw [hnucell]; exact hl
    exact Option.some.inj (h1.symm.trans hleft)
  have hpc : p.1.val = lref.column := by rw [hlp]; rfl
  constructor
  · -- `x` ascends ⇒ `ℓ` ascends
    intro hasc
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
    have hL : (Frame.ofMountain M).height nr < (Frame.ofMountain M).height nu :=
      lt_of_le_of_lt hSetup.L_le_C hC
    obtain ⟨w', hw'r, hw'u, hw'c, hLw'⟩ := hSetup.lower hconeu hL
    have hww : w' = w := by
      obtain ⟨_, h1⟩ := upper_spec hw'u
      obtain ⟨hwc2, h2⟩ := upper_spec hwu
      rcases w' with ⟨c1, i1⟩
      rcases w with ⟨c2, i2⟩
      dsimp only at hw'c hwc2 h1 h2
      have hc12 : c1 = c2 := hw'c.trans hwc2
      subst hc12
      have : i1 = i2 := Fin.ext (by omega)
      subst this
      rfl
    subst hww
    have hconcl := left_in_coneF hSetup hconeu hur hw'r hw'u hw'c hLw' hp
      (fun hwC => mainF hSetup w'.1.val w' p rfl (by rw [hw'c]; exact hconeu) hw'r hwC hp)
    rcases hconcl with ⟨⟨low, hlr, hlc, hlh, hlpath⟩, _⟩ | hleftcr
    · refine ascends_of_cone hb hsrc' hroot' hlr ?_ hlpath hlh.symm hnrc ?_
      · rw [hx', ← hpc, hlc]
      · have : ((Frame.ofMountain M).cell low).row = ((Frame.ofMountain M).cell nr).row := hlh
        rw [this, hZ]
    · rw [hpc, hnrc] at hleftcr
      omega
  · -- `ℓ` ascends ⇒ `x` ascends
    intro hasc
    obtain ⟨aref, acl, hna, hra⟩ := ascClean_of_ascends hasc
    rw [hsrc', hx'] at hna
    rw [hsrc', hroot', hx'] at hra
    -- the root `nr` and the cone of `ℓ`
    obtain ⟨nr, hconep, hnrc, hZ, hLv⟩ : ∃ nr : (Frame.ofMountain M).Node,
        Cone.Cone (Frame.ofMountain M) nr p.1 ∧ nr.1.val = cr ∧
        Official.official ((Frame.ofMountain M).cell nr).row =
          referenceRow (Official.official ρc.row) ∧
        (Frame.ofMountain M).height nr < (Frame.ofMountain M).height nu := by
      rcases Nat.lt_or_eq_of_le hlcr with hlt' | heq
      · obtain ⟨nr, nρ, na, _, hSetup, hnrc, hnac, hcone, hnρh, _, _, _, _, hZ⟩ :=
          ascSetup hb hlt' hρ hna hra
        refine ⟨nr, ?_, hnrc, hZ, ?_⟩
        · have : p.1 = na.1 := Fin.ext (by rw [hpc, hnac])
          rw [this]; exact hcone
        · exact lt_of_le_of_lt hSetup.L_le_C (by rw [hnρh, hnuh]; exact hρu)
      · -- `ℓ = c_r`: the root is the node of `c_r` at the reference row
        obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hna
        simp only at hac ha1 hacell harow
        obtain ⟨na, hnaref, hnacell⟩ := ControlProof.node_of_cell? hacell
        have hnar : Frame.Real na := by
          show 0 < na.2.val
          have : aref.index = na.2.val := by rw [← hnaref]; rfl
          omega
        have hnac : na.1.val = cr := by
          have : aref.column = na.1.val := by rw [← hnaref]; rfl
          omega
        have hnarow : ((Frame.ofMountain M).cell na).row = acl.row := by rw [hnacell]
        refine ⟨na, ⟨na, hnar, Fin.ext (by rw [hnac, hpc, heq]), rfl, .refl _⟩, hnac, ?_, ?_⟩
        · rw [hnarow, harow]
        · show ((Frame.ofMountain M).cell na).row < ((Frame.ofMountain M).cell nu).row
          rw [hnarow, hnucell]
          have hacl1 : (1 : Row) ≤ acl.row := by
            rw [← hnarow]; exact Frame.one_le_height hO hnar
          apply Recon.row_lt_of_official hcp1
          rw [harow]
          exact lt_of_le_of_lt (Recon.JumpLaw.referenceRow_le _) hlt
    obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := cone_of_cone_legF hN hwr hwu hLv hp hconep
    refine ascends_of_cone hb hsrc hroot hlr ?_ hlpath hlh.symm hnrc ?_
    · rw [hx, ← hnuc, hlc]
    · have : ((Frame.ofMountain M).cell low).row = ((Frame.ofMountain M).cell nr).row := hlh
      rw [this, hZ]

/-- **`x` ascends ⇒ `ℓ` ascends, also when the root-column top is at the row of the node.**
(The converse can fail when `row ρ = row v`.) If the node of `x` at the reference height is `v`
itself, the candidate `Q(v)` is in `ℓ` at that height, and the search from `Q(v)` to `P(v)` is a
path of numerical parents at that height (`Hit.parentPath`). -/
theorem ascLegLe {M : Mountain} {s : List Nat} (hb : Canonical.build s = .ok M) {cr x : Nat}
    (hcx : cr < x) {k : Nat} {cp : Cell} (hk : 1 ≤ k) (hcp : cell? M ⟨x, k⟩ = some cp)
    {lref : Ref} (hl : cp.left = some lref) (hlcr : cr ≤ lref.column)
    {d : Nat} {S : Row} {ρr : Ref} {ρc : Cell} (hρ : topIn M cr (d + 2) S = some (ρr, ρc))
    (hle : Official.official ρc.row ≤ Official.official cp.row)
    (ctx ctx' : Context) (hsrc : ctx.source = M) (hsrc' : ctx'.source = M)
    (hroot : ctx.rootColumn = cr) (hroot' : ctx'.rootColumn = cr) (hx : ctx.x = x)
    (hx' : ctx'.x = lref.column) :
    ascends ctx (some (ρr, ρc)) = .ok true → ascends ctx' (some (ρr, ρc)) = .ok true := by
  intro hasc
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
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
  -- the height of the root is at most the height of `v`
  have hnr1 : (1 : Row) ≤ (Frame.ofMountain M).height nr :=
    Frame.one_le_height hO hSetup.rootReal
  have hLle : (Frame.ofMountain M).height nr ≤ (Frame.ofMountain M).height nu := by
    rw [hnuh]
    by_contra hn
    have hlt : cp.row < (Frame.ofMountain M).height nr := lt_of_not_ge hn
    have h1 := Recon.official_strictMono hcp1 hlt
    have h2 : Official.official ((Frame.ofMountain M).height nr) ≤ Official.official cp.row := by
      show Official.official ((Frame.ofMountain M).cell nr).row ≤ _
      rw [hZ]
      exact (Recon.JumpLaw.referenceRow_le _).trans hle
    exact absurd h1 (not_lt.mpr h2)
  -- the ref of the stored left end of `v`
  have hlnu : ((Frame.ofMountain M).cell nu).left = some lref := by rw [hnucell]; exact hl
  obtain ⟨left, hleft, _⟩ := hN.toOrdered.stored_valid nu lref hlnu
  have hlref : Frame.ref left = lref := Frame.lookup_spec hleft
  have hleftc : left.1.val = lref.column := by rw [← hlref]; rfl
  rcases lt_or_eq_of_le hLle with hL | hL
  · -- `v` above the reference height
    obtain ⟨w, hwr, hwu, hwc, hLw⟩ := hSetup.lower hconeu hL
    obtain ⟨p, hp, _, _, hpleft⟩ := hN.upper_step w nu hwr hwu
    have hlp : lref = Frame.ref p := Option.some.inj (hlnu.symm.trans hpleft)
    have hpc : p.1.val = lref.column := by rw [hlp]; rfl
    have hconcl := left_in_coneF hSetup hconeu hur hwr hwu hwc hLw hp
      (fun hwC => mainF hSetup w.1.val w p rfl (by rw [hwc]; exact hconeu) hwr hwC hp)
    rcases hconcl with ⟨⟨low, hlr, hlc, hlh, hlpath⟩, _⟩ | hleftcr
    · refine ascends_of_cone hb hsrc' hroot' hlr ?_ hlpath hlh.symm hnrc ?_
      · rw [hx', ← hpc, hlc]
      · have : ((Frame.ofMountain M).cell low).row = ((Frame.ofMountain M).cell nr).row := hlh
        rw [this, hZ]
    · rw [hpc, hnrc] at hleftcr
      omega
  · -- `v` is the node of `x` at the reference height: `Q(v)` is in `ℓ` at that height
    obtain ⟨low, hlr, hlc, hlh, hlpath⟩ := hconeu
    have he : low = nu := node_eq_of_column_height hO hlc (hlh.trans hL)
    subst he
    obtain ⟨next, hnext, _, hnh, hnpath, _⟩ := hSetup.low_parent hlr hlh hlpath hur
    obtain ⟨q, hQ, hit⟩ := (P_iff hO).mp hnext
    obtain ⟨left', hl', _, _, hqc, _, hqh, _⟩ := Q_spec hO hQ
    have hll : left' = left :=
      Executable.ref_injective _ (Option.some.inj (hl'.symm.trans (by rw [hlnu, hlref])))
    subst hll
    have hqr : Frame.Real q := Q_real hO hlr hQ
    have hqpos : 0 < (Frame.ofMountain M).value q := hO.real_positive q hqr
    have hqpath : ParentPath (Frame.ofMountain M) q next := hit.parentPath hO hqpos
    have hqh' : (Frame.ofMountain M).height q = (Frame.ofMountain M).height nr := by
      apply le_antisymm
      · rw [← hlh]; exact hqh
      · rw [← hnh]; exact hit.height_le hO
    refine ascends_of_cone hb hsrc' hroot' hqr ?_ (hqpath.trans hnpath) hqh'.symm hnrc ?_
    · rw [hx', ← hleftc, hqc]
    · have : ((Frame.ofMountain M).cell q).row = ((Frame.ofMountain M).cell nr).row := hqh'
      rw [this, hZ]

end OmegaY.Official.Classification.Proofs.CopyShape.AscLeg

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.AscLeg.mainF
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.AscLeg.ascLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.AscLeg.ascLegLe
