/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SRTMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.SRTTree
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRootRow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBBnd
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CPNMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `StepRootTop` holds (`SRT`)

`StepRootTop` (`SeamReduce.lean`): `Z` is the top copy (block `i ≥ 1`) of `z`, a node of an inner
column below `τ` whose stored parent `a` (the left end of `z⁺`) is in the root column, with
`z⁺` below `τ` and the node `a⁺` above `a` at or above `τ`. Then the node above the stored parent
`A` of `Z` is at the row of `a⁺`.

## The argument

`stand_of_highest` (`TopChainHi.lean`) gives the second clause of `Stand` when `a` and `A` are
the highest nodes of their columns below `τ`. For `a`, this is `a⁺ ≥ τ`. For `A` (the highest node
of `B_i` below the row of `Z⁺`, `lo_core`), it is `key`: every node of `B_i` below `τ` is below
`Z⁺`.

`key`: `rr := row a`. The top row is `τ = bump(row root, J)` (`PBStageB.topBump`), and
`row root ≤ rr`, so the rows `[rr, τ)` lie in one first item `F`: the one that holds `z⁺`
(`top_region`). The top of the root column in `F` is `a`, the column of `z` ascends there
(`ascends_of_root_leg`, the leg of `z⁺` is `c_r`), and the top of `B_i` in `F` is at height
`h_ρ + Δ` (`bnd_lift`). Nodes of `B_i` below `rr` are below `Z⁺` (`Z⁺` keeps its place above
the root row `rr`, `ecmp_of_colData`). The tree claim `LRC.SRT.claim` does the rest.
-/

namespace OmegaY.Official.Recon.TopChain.Seam.SRT

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand above IsTopAt)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve
  upper_of_above above_of_upper)

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- A new column from its column data. -/
theorem nc_of_colData (E : Env s n R M t root) {i x : Nat} {lo us : List (Emit × Origin)}
    (hi1 : 1 ≤ i)
    (hD : LowerPB.ColData s n R M t root (x + (M.size - 1 - root.column) * i) i x lo us) :
    JumpLaw.NewColumn s n R M t root i x := by
  have hcr := E.top.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hD.xb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR := hD.XR
  obtain ⟨i', x', hi', hx', hXeq, hcopy⟩ := E.CI.2.2 (x + (M.size - 1 - root.column) * i) hXR
    (by omega)
  obtain ⟨hii, hxx⟩ := Classification.Proofs.ChainCorr.NonTop.blockX_unique hcr hxg hxl hx'
    hXeq (by omega)
  subst hii hxx
  have hn0 : n ≠ 0 := by have := hD.iln; omega
  exact ⟨E.run, E.top, hn0, E.CI, hi', hD.xb, hXR, ⟨_, Array.getElem?_eq_getElem hXR, hcopy⟩⟩

/-- The lower part of a column as the flattened outputs of the first items. -/
theorem lowerT_flat {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∃ outs, (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) = .ok outs ∧
      lo = outs.flatten := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    exact ⟨outs, houts, (Except.ok.inj h).symm⟩

/-- **The rows `[row root, τ)` lie in one first item**, the one holding any row of them. -/
theorem top_region (hTop : Recon.Top s M t root) {rc : Cell}
    (hrc : Reserve.cell? M root = some rc) {k0 j0 : Nat}
    (hj0 : j0 < (official t.row).coeff k0) {ρz : Row}
    (hz : inRegion (k0 + 1) (slot (k0 + 2) (official t.row) j0) ρz = true)
    (hzr : official rc.row ≤ ρz) (hzτ : ρz < official t.row) :
    ∀ ρ', official rc.row ≤ ρ' → ρ' < official t.row →
      inRegion (k0 + 1) (slot (k0 + 2) (official t.row) j0) ρ' = true := by
  obtain ⟨rc', a, J, hrc', _, hτ, hag, _⟩ := Proofs.CopyShape.PBStageB.topBump hTop
  obtain rfl : rc' = rc := Option.some.inj (hrc'.symm.trans hrc)
  have hja : Row.jump a (official rc'.row) ≤ J := Row.jump_le_iff.mpr (fun q hq => hag q hq)
  have hτ' : official t.row = Row.bump (official rc'.row) J := by
    rw [hτ]; exact Row.bump_eq_of_jump_le hja
  have hk0 : J ≤ k0 := by
    by_contra hn
    rw [hτ', Row.coeff_bump_low (by omega)] at hj0
    omega
  have hzag : ∀ q, J ≤ q → ρz.coeff q = (official rc'.row).coeff q := by
    have := Row.jump_le_of_lt_bump hzr (by rw [← hτ']; exact hzτ)
    intro q hq
    exact (Row.jump_le_iff.mp this q hq).symm
  intro ρ' h1 h2
  have hag' := Row.jump_le_of_lt_bump h1 (by rw [← hτ']; exact h2)
  rw [RowLaw.inRegion_iff'] at hz ⊢
  intro q hq
  simp only [show k0 + 1 - 1 = k0 by omega] at hq hz
  rw [← hz q hq, hzag q (by omega)]
  exact (Row.jump_le_iff.mp hag' q (by omega)).symm

/-- `h_κ + (h_κ - h_ρ)·i = h_ρ + (h_κ - h_ρ)·(i + 1)`. -/
theorem lift_arith (hR hK i : Nat) (h : hR < hK) :
    ((hK + (hK - hR) * i : Nat) : Int) = (hR : Int) + ((hK : Int) - (hR : Int)) * ((i + 1 : Nat) : Int) := by
  obtain ⟨D, rfl⟩ : ∃ D, hK = hR + D := ⟨hK - hR, by omega⟩
  have e1 : hR + D - hR = D := by omega
  rw [e1]
  have e2 : ((hR + D : Nat) : Int) - (hR : Int) = (D : Int) := by omega
  rw [e2]
  push_cast
  rw [Int.mul_add, Int.mul_one]
  generalize (D : Int) * (i : Int) = X
  omega

/-- **Every node of `B_i` below `τ` is below `Z⁺`.** -/
theorem key {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCore s n R M t root i ZN VN A zN z'N aN lo us jz)
    (hac : aN.1.val = root.column) {ca' : Cell}
    (hca' : Reserve.cell? M (above (Frame.ref aN)) = some ca') (hθ : t.row ≤ ca'.row) :
    ∀ q ∈ realNodes R (root.column + (M.size - 1 - root.column) * i),
      official q.2.row < official t.row → official q.2.row < ((lo[jz + 1]'C.jzl)).1.row := by
  have E := C.E
  have hTop := E.top
  have hrun := E.run
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  have hG := E.G
  have hcr := hTop.lt
  have hi1 := C.hi1
  have hin := C.hin
  have hD := C.D
  have hzu := C.zu
  have hzraw := C.zraw
  have har := C.ar
  have haH := C.aH
  have hz'lt := C.z'lt
  have hpl : lo[jz + 1]'C.jzl ∈ lo ++ us := List.mem_append_left _ (List.getElem_mem _)
  have hpl' : lo[jz + 1]'C.jzl ∈ lo := List.getElem_mem _
  have hVsrc := C.Vsrc
  have hVcut := C.Vcut
  generalize lo[jz + 1]'C.jzl = p at hpl hpl' hVsrc hVcut ⊢
  clear C
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hNC := nc_of_colData E hi1 hD
  have hNCb := Classification.Proofs.P3T.boundary_nc hNC
  have rX := hNC.runCtx
  have hbnd := LRC.colCtx_bnd hNC
  have hMD := Proofs.CopyShape.Found.factMD_of_bctx hTop (LRC.colCtx_bctx hNC)
  have hMH := Proofs.CopyShape.Found.factMH_of_bctx hrun hTop hi1 hin (LRC.colCtx_bctx hNC)
  -- the origin `z⁺` of `p`
  have hcz : Reserve.cell? M p.2.src = some ((Frame.ofMountain M).cell z'N) := by
    rw [hVsrc]; exact LowerChainRecon.cell?_ref z'N
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  have hzr : Real z'N := by show 0 < z'N.2.val; omega
  have ha1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := one_le_height hG har
  generalize hcz' : (Frame.ofMountain M).cell z'N = cz at hcz
  have hczrow : (Frame.ofMountain M).height z'N = cz.row := by
    change ((Frame.ofMountain M).cell z'N).row = _; rw [hcz']
  generalize hrr : official ((Frame.ofMountain M).cell aN).row = rr
  have hrz : rr < official cz.row := by
    rw [← hrr, ← hczrow]; exact Recon.official_strictMono ha1 haH.1
  -- `p` is above the root row `rr`
  have hamem : (Frame.ref aN, (Frame.ofMountain M).cell aN) ∈ realNodes M root.column := by
    have := Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref aN) har
    have hc : (Frame.ref aN).column = root.column := hac
    rw [hc] at this; exact this
  have hRR : Classification.Proofs.ChainCorr.SRCmp.RootRow M root.column rr :=
    ⟨_, hamem, hrr⟩
  have hrp : rr < p.1.row := by
    have H := ecmp_of_colData hD p hpl _ hcz rr hRR
    exact (H.1 hVcut).1 hrz
  -- the root is not above `a`
  obtain ⟨rc, aT, J, hrc, hroot1, hτ, hag, hrcle⟩ := Proofs.CopyShape.PBStageB.topBump hTop
  have hrcτ : official rc.row < official t.row := by
    rw [hτ]; exact lt_of_le_of_lt hrcle (Row.lt_bump _ _)
  obtain ⟨a'N, ha'N, ha'c⟩ := node_of_cell hca'
  have ha'u := upper_of_above ha'N
  obtain ⟨ha'1, ha'2⟩ := upper_spec ha'u
  have ha'h : (Frame.ofMountain M).height a'N = ca'.row := by
    change ((Frame.ofMountain M).cell a'N).row = _; rw [ha'c]
  -- a node of the root column below `τ` is at or below `a`
  have hbelow : ∀ (vN : (Frame.ofMountain M).Node), vN.1 = aN.1 →
      (Frame.ofMountain M).height vN < t.row → vN.2.val ≤ aN.2.val := by
    intro vN hvc hvt
    by_contra hn
    have h1 := height_le_of_index hG (ha'1.trans hvc.symm) (show a'N.2.val ≤ vN.2.val by omega)
    rw [ha'h] at h1
    exact absurd (lt_of_lt_of_le hvt (le_trans hθ h1)) (lt_irrefl _)
  have hrcrr : official rc.row ≤ rr := by
    obtain ⟨rN, hrN, hrNc⟩ := node_of_cell hrc
    have hrcol : rN.1 = aN.1 := Fin.ext (by
      have := congrArg Ref.column hrN; simp [Frame.ref] at this; omega)
    have h4 : (Frame.ofMountain M).height rN = rc.row := by
      change ((Frame.ofMountain M).cell rN).row = _; rw [hrNc]
    have hrN1 : Real rN := by
      show 0 < rN.2.val
      have := congrArg Ref.index hrN; simp [Frame.ref] at this; omega
    have hrc1 : (1 : Row) ≤ rc.row := by rw [← h4]; exact one_le_height hG hrN1
    have h3 : rc.row < t.row :=
      CrossUpperSim.lt_of_official_lt (le_of_lt (tau_gt_one hTop)) hrcτ
    have hidx := hbelow rN hrcol (by rw [h4]; exact h3)
    have hle := height_le_of_index hG hrcol hidx
    rw [h4] at hle
    rw [← hrr]
    exact Recon.official_mono hrc1 hle
  -- the first item holding `p`
  obtain ⟨outs, houts, hlof⟩ := lowerT_flat hD.hlo
  have hpo : p ∈ outs.flatten := by rw [← hlof]; exact hpl'
  obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hpo
  obtain ⟨k, hkL, rfl⟩ := List.getElem_of_mem hL'
  obtain ⟨hlen, hall⟩ := Classification.mapM_except_spec _ _ _ houts
  have hk : k < (lowerItems (official t.row)).length := by omega
  have hFm := List.getElem_mem hk
  obtain ⟨k0, j0, _, hj0, hFeq⟩ := RowLaw.mem_lowerItems hFm
  have hrunF := hall k hk hkL
  rw [hFeq] at hrunF hFm
  -- the source region of `p`
  have hEOK := (Proofs.CopyShape.NoMA.runItemT_shapeW (JumpLaw.colCtx M R root (i' + 1) zN.1.val)
    (official t.row) R (root.column + (M.size - 1 - root.column) * (i' + 1)) hVM
    (by show 1 ≤ i' + 1; omega) hbnd hMD hMH k0 _ _ hrunF
    (Proofs.CopyShape.Reach.top hFm) (fun C h => by cases h)).1 p hpL'
  obtain ⟨_, _, c', hc', hsreg, _⟩ := hEOK
  have hc'' : Reserve.cell? M p.2.src = some c' := hc'
  have ec : c' = cz := Option.some.inj (hc''.symm.trans hcz)
  rw [ec] at hsreg
  simp only at hsreg
  have hzτ : official cz.row < official t.row :=
    (Classification.lowerItems_below (official t.row) _ hFm).1 _ hsreg
  have hreg := top_region hTop hrc hj0 hsreg (le_trans hrcrr hrz.le) hzτ
  have harS := hreg rr hrcrr (lt_trans hrz hzτ)
  -- the level is at least `2`
  obtain ⟨d, rfl⟩ : ∃ d, k0 = d + 1 := by
    rcases Nat.eq_zero_or_pos k0 with h0 | h0
    · exfalso
      subst h0
      have e1 := Classification.inRegion_one hsreg
      have e2 := Classification.inRegion_one harS
      rw [← e2] at e1
      exact absurd e1 (ne_of_gt hrz)
    · exact ⟨k0 - 1, by omega⟩
  generalize hS : slot (d + 1 + 2) (official t.row) j0 = S at hsreg hreg harS hFm hrunF
  -- the top of the root column in `S` is `a`
  have hrrcell : official ((Frame.ofMountain M).cell aN).row = rr := hrr
  have hamS : inRegion (d + 2) S
      (official ((Frame.ref aN, (Frame.ofMountain M).cell aN) : Ref × Cell).2.row) = true := by
    show inRegion (d + 2) S (official ((Frame.ofMountain M).cell aN).row) = true
    rw [hrr]; exact harS
  obtain ⟨ρr, ρc, hρ, hρmem, hρr⟩ : ∃ ρr ρc, topIn M root.column (d + 2) S = some (ρr, ρc) ∧
      (ρr, ρc) ∈ realNodes M root.column ∧ official ρc.row = rr := by
    cases htop : topIn M root.column (d + 2) S with
    | none =>
      have := RowLaw.topIn_none htop _ hamem
      rw [hamS] at this; cases this
    | some ρ =>
      obtain ⟨ρr, ρc⟩ := ρ
      obtain ⟨hρm, hρin, hρmax⟩ := RowLaw.topIn_spec htop
      have hi1' := hρmax _ hamem hamS
      obtain ⟨hρcol, hρ1, hρcell⟩ := Classification.mem_realNodes hρm
      obtain ⟨ρN, hρN, hρNc⟩ := node_of_cell hρcell
      have hρNcol : ρN.1 = aN.1 := Fin.ext (by
        have := congrArg Ref.column hρN; simp [Frame.ref] at this; simp only at hρcol; omega)
      have hρτ : official ρc.row < official t.row :=
        (Classification.lowerItems_below (official t.row) _ hFm).1 _ hρin
      have hρNh : (Frame.ofMountain M).height ρN = ρc.row := by
        change ((Frame.ofMountain M).cell ρN).row = _; rw [hρNc]
      have hρNr : Real ρN := by
        show 0 < ρN.2.val
        have := congrArg Ref.index hρN; simp [Frame.ref] at this; simp only at hρ1; omega
      have hidx := hbelow ρN hρNcol (by
        rw [hρNh]
        exact CrossUpperSim.lt_of_official_lt (le_of_lt (tau_gt_one hTop)) hρτ)
      have hidx' : aN.2.val ≤ ρN.2.val := by
        have := congrArg Ref.index hρN; simp [Frame.ref] at this; simp only at hi1'
        have h2 : (Frame.ref aN).index = aN.2.val := rfl
        omega
      have heq : ρN = aN := node_eq_of_index hρNcol (by omega)
      rw [heq] at hρNc
      have hcc : ρc = (Frame.ofMountain M).cell aN := hρNc.symm
      refine ⟨ρr, ρc, rfl, hρm, ?_⟩
      rw [hcc]; exact hrrcell
  -- the item `K = F` of the tree
  have hK : JumpLawLower.InTree (JumpLaw.colCtx M R root (i' + 1) zN.1.val) (official t.row)
      (d + 2) ⟨S, S, none, 0, false⟩ := ⟨_, hFm, .refl _ _⟩
  -- `z⁺` is a node of `x` in `S`
  have hzmem : (Frame.ref z'N, cz) ∈ realNodes M zN.1.val := by
    have := Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref z'N) hzr
    rw [hcz'] at this
    have hc : (Frame.ref z'N).column = zN.1.val := by
      show z'N.1.val = zN.1.val; rw [hz'1]
    rw [hc] at this; exact this
  obtain ⟨ax, hax⟩ : ∃ ax, topIn M zN.1.val (d + 2) S = some ax := by
    cases htop : topIn M zN.1.val (d + 2) S with
    | none =>
      have := RowLaw.topIn_none htop _ hzmem
      have h2 : inRegion (d + 2) S (official cz.row) = true := hsreg
      simp only at this
      rw [h2] at this; cases this
    | some ax => exact ⟨ax, rfl⟩
  -- the column of `z` ascends at `a`
  have hzleft : cz.left = some (Frame.ref aN) := by
    obtain ⟨up, hup, hleft⟩ := rawParent_spec hzraw
    rw [hzu] at hup
    obtain rfl := Option.some.inj hup
    rw [← hcz']; exact hleft
  have hasc : ascends (JumpLaw.colCtx M R root (i' + 1) zN.1.val) (some (ρr, ρc)) = .ok true := by
    refine JumpLaw.ascends_of_root_leg hb (ctxX := JumpLaw.colCtx M R root (i' + 1) zN.1.val) rfl
      hzmem (ne_of_gt (lt_of_le_of_lt (Row.zero_le _) hrz))
      (by
        have := Classification.Proofs.P3T.leftColumn_of_left hzleft
        rw [this]; show Except.ok aN.1.val = Except.ok root.column; rw [hac])
      (ps := rr) ⟨List.mem_map.mpr ⟨_, hamem, hrr⟩, hrz, ?_⟩ hρmem (le_of_eq hρr)
    intro r hr hrlt
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hvcol, hv1, hvcell⟩ := Classification.mem_realNodes hv
    have hvcol' : v.1.column = root.column := hvcol
    obtain ⟨vN, hvN, hvNc⟩ := node_of_cell hvcell
    have hvNcol : vN.1 = aN.1 := Fin.ext (by
      have := congrArg Ref.column hvN; simp [Frame.ref] at this; omega)
    have hvNr : Real vN := by
      show 0 < vN.2.val
      have := congrArg Ref.index hvN; simp [Frame.ref] at this; omega
    have hvh : (Frame.ofMountain M).height vN = v.2.row := by
      change ((Frame.ofMountain M).cell vN).row = _; rw [hvNc]
    have hz1 : (1 : Row) ≤ cz.row := by rw [← hczrow]; exact one_le_height hG hzr
    have hlt : v.2.row < cz.row := CrossUpperSim.lt_of_official_lt hz1 hrlt
    have hidx := haH.2 vN hvNcol (by rw [hvh, hczrow]; exact hlt)
    have hle := height_le_of_index hG hvNcol hidx
    rw [hvh] at hle
    rw [← hrr]
    exact Recon.official_mono (by rw [← hvh]; exact one_le_height hG hvNr) hle
  -- the top of `B` in `S`
  obtain ⟨_, hlt, qB, hqB, hqBco⟩ := LRC.bnd_lift hNC hNCb hK rfl rfl hax hρ hasc
  have hcase : (⟨S, S, none, 0, false⟩ : Item).cutBottom = false →
      ascends (JumpLaw.colCtx M R root (i' + 1) zN.1.val) (some (ρr, ρc)) = .ok true ∧
      ∃ q, topIn R (root.column + (M.size - 1 - root.column) * (i' + 1)) (d + 2) S = some q ∧
        (((official q.2.row).coeff d : Nat) : Int) = ((height (d + 2) rr : Nat) : Int) +
          (((heightOf (d + 2) (topIn M (M.size - 1) (d + 2) S) : Nat) : Int) -
            ((height (d + 2) rr : Nat) : Int)) * ((i' + 1 : Nat) : Int) := by
    intro _
    refine ⟨hasc, qB, hqB, ?_⟩
    rw [hqBco, ← hρr]
    exact lift_arith _ _ i' hlt
  -- the invariant at the first item
  have hINV : ∀ q ∈ realNodes R (root.column + (M.size - 1 - root.column) * (i' + 1)),
      official q.2.row < official t.row →
      inRegion (d + 2) S (official q.2.row) = true ∨ official q.2.row < p.1.row := by
    intro q _ hqτ
    by_cases h : official rc.row ≤ official q.2.row
    · exact Or.inl (hreg _ h hqτ)
    · exact Or.inr (lt_trans (lt_of_lt_of_le (lt_of_not_ge h) hrcrr) hrp)
  exact LRC.SRT.claim (ctx := JumpLaw.colCtx M R root (i' + 1) zN.1.val) rX
    (by show i' + 1 ≠ 0; omega) rfl rfl hbnd hVR hMD hMH hcz hrz d _ hK
    (fun C h => by cases h) rfl ρr ρc hρ hρr hcase hINV _ hrunF hpL'

/-- **`StepRootTop` holds.** -/
theorem stepRootTop : StepRootTop := by
  intro s n R M t root i hrun hTop hi0 hin Z z hTN a cz ca hraw hcz hca hlo hac A' hA' ca' hca' hθ
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, jz, hZ, hz, ha, C⟩ :=
    lo_core hrun hTop hi1 hin hTN hraw hcz hca hlo
  subst hZ hz ha
  have E := C.E
  have hG := E.G
  have hF := E.FR
  have hAA : A' = Frame.ref A :=
    Option.some.inj (hA'.symm.trans (reserve_rawParent_of_frame C.Araw))
  subst hAA
  have hacN : aN.1.val = root.column := hac
  have hK := key C hacN hca' hθ
  have ht1 := tau_gt_one hTop
  -- `a` is the highest node of its column below `τ`
  obtain ⟨a'N, ha'N, ha'c⟩ := node_of_cell hca'
  obtain ⟨ha'1, ha'2⟩ := upper_spec (upper_of_above ha'N)
  have ha'h : (Frame.ofMountain M).height a'N = ca'.row := by
    change ((Frame.ofMountain M).cell a'N).row = _; rw [ha'c]
  have haH : HighestIn (Frame.ofMountain M) (· < t.row) aN := by
    refine ⟨lt_trans C.aH.1 C.z'lt, fun v hv hvt => ?_⟩
    by_contra hn
    have h1 := height_le_of_index hG (ha'1.trans hv.symm) (show a'N.2.val ≤ v.2.val by omega)
    rw [ha'h] at h1
    exact absurd (lt_of_lt_of_le hvt (le_trans hθ h1)) (lt_irrefl _)
  -- `A` is the highest node of its column below `τ`
  have hVlt : (Frame.ofMountain R).height VN < t.row := by
    rw [C.Vrow]
    have h1 := C.D.lo_lt _ (List.getElem_mem C.jzl)
    have h2 := Recon.stored_strictMono h1
    rwa [Classification.stored_official (le_of_lt ht1)] at h2
  have hAcol : A.1.val = root.column + (M.size - 1 - root.column) * i := by
    rw [C.Ac, shiftCol_of_le (le_of_eq hacN.symm), hacN]
  have hAH : HighestIn (Frame.ofMountain R) (· < t.row) A := by
    refine ⟨lt_trans C.AH.1 hVlt, fun G hGA hGt => ?_⟩
    rcases Nat.eq_zero_or_pos G.2.val with h0 | hGr
    · omega
    have hGr' : Real G := hGr
    have hG1 : (1 : Row) ≤ (Frame.ofMountain R).height G := one_le_height hF hGr'
    have hmem : (Frame.ref G, (Frame.ofMountain R).cell G) ∈
        realNodes R (root.column + (M.size - 1 - root.column) * i) := by
      have := Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref G) hGr'
      have hc : (Frame.ref G).column = root.column + (M.size - 1 - root.column) * i := by
        show G.1.val = _; rw [hGA]; exact hAcol
      rw [hc] at this; exact this
    have hGτ : official ((Frame.ofMountain R).cell G).row < official t.row :=
      Recon.official_strictMono hG1 hGt
    have hlt := hK _ hmem hGτ
    apply C.AH.2 G hGA
    rw [C.Vrow]
    have h2 : stored (official ((Frame.ofMountain R).height G)) <
        stored ((lo[jz + 1]'C.jzl).1.row) := Recon.stored_strictMono hlt
    rwa [Classification.stored_official hG1] at h2
  have hS := stand_of_highest E hi1 hin (P := (· < t.row)) (fun r r' h h' => lt_of_le_of_lt h h')
    (fun r h => h) C.ar (by rw [hacN]; exact hTop.lt) C.Ac haH hAH
  exact (hS.2.1 hacN).2.1 ca' hca' hθ

/-- **`TopStepLoRoot` holds.** -/
theorem topStepLoRoot : TopStepLoRoot :=
  CPN.topStepLoRoot_of_stepRootTop stepRootTop

end OmegaY.Official.Recon.TopChain.Seam.SRT

#print axioms OmegaY.Official.Recon.TopChain.Seam.SRT.key
#print axioms OmegaY.Official.Recon.TopChain.Seam.SRT.stepRootTop
#print axioms OmegaY.Official.Recon.TopChain.Seam.SRT.topStepLoRoot
