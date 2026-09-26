/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQBiTopMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQBiTopAsc
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRootRow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredBoundary

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `BiTopLow` holds (`TSQ`)

`BiTopLow` (`TSQRootTop.lean`): the top copy `u` (block `i ≥ 1`) of `o = (x, C)`, a node below
`τ` whose leg is the root column `c_r`, with `o⁺` below `τ` and `pa = hAM(c_r, C)` with `pa⁺` at
or above `τ`. Every node of the boundary column `B = c_r + w·i` below `τ` is at or below `u`.

## The proof

* `pa` is the root `r` and `τ = B(row t⁻, row r)` (`root_tau`); `x` ascends at `r` (`asc_root`).
* The first item `F` holding `C` holds `row r` too, and every row below `τ` outside `F` is below
  the rows of `F` (`root_mem_first`, `below_first`: `F` is the last first item, of level
  `J + 1 ≥ 2` with `J = jump(row t⁻, row r)`; level `1` is excluded by `o⁺`). So `r` is the root
  top of `F`.
* `bnd_lift` (`Recon/LRCBLift.lean`): the top `q` of `B` in `F` has height `h_ρ + (h_κ - h_ρ)·i`,
  the lift of `F` in the tree of `X`.
* `lift_desc` (`TSQBiTopTree.lean`): the lower part of `X` has a copy `e` of `o` at a row at or
  above `q`.
* A node of `B` below `τ` is in `F` (then at or below `q`) or below `F` (then below `e`); and `e`
  is at or below the top copy `u`.

`biTopLow : BiTopLow`; with `TSQ.startRootTopUp_of_biTopLow`, `startRootTopUp : StartRootTopUp`.
-/

namespace OmegaY.Official.Recon.TSQ.BTL

open Canonical Classification Classification.Proofs.ChainCorr
open OmegaY.Geometry OmegaY.Geometry.Frame
open Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC Recon.TopChain

/-- `lowerT` is the concatenation of the runs of the first items. -/
theorem lowerT_outs {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∃ outs, (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) = .ok outs ∧
      lo = outs.flatten := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    exact ⟨outs, houts, (Except.ok.inj h).symm⟩

/-- **The rows of the copies of a node lie in the target of its first item.** -/
theorem first_row {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (hNC : NewColumn s n R M t root i x) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root i x) p.1 p.2) = .ok outsT)
    {a : Nat} (ha : a < (lowerItems (official t.row)).length) {cv : Cell}
    (hC : inRegion (lowerItems (official t.row))[a].1 (lowerItems (official t.row))[a].2.source
      (official cv.row) = true)
    {p : Emit × Origin} (hp : p ∈ outsT.flatten) (hpc : Reserve.cell? M p.2.src = some cv) :
    inRegion (lowerItems (official t.row))[a].1 (lowerItems (official t.row))[a].2.target
      p.1.row = true := by
  have rX := hNC.runCtx
  obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hp
  obtain ⟨a', ha', rfl⟩ := List.getElem_of_mem hL'
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
  have ha'' : a' < (lowerItems (official t.row)).length := by omega
  have hrun := hall a' ha'' ha'
  have hmem := List.getElem_mem ha''
  have hinv : Inner.ItemInvC (colCtx M R root i x).source (colCtx M R root i x).rootColumn
      (lowerItems (official t.row))[a'].1 (lowerItems (official t.row))[a'].2 := by
    intro C hCl
    rw [Inner.lowerItems_clean _ _ hmem] at hCl
    cases hCl
  have hE := (Inner.runItemT_order _ _ _ _ hrun hinv).2 p hpL'
  obtain ⟨hsrc, _⟩ := eok_parts hE hpc
  obtain ⟨hOK, hst, h1, _⟩ := lower_itemOK (ctx := colCtx M R root i x) hmem
  obtain ⟨_, hst', _, _⟩ := lower_itemOK (ctx := colCtx M R root i x) (List.getElem_mem ha)
  have hsrc' := hsrc
  rw [hst] at hsrc'
  have hC' := hC
  rw [hst'] at hC'
  have haa := first_unique (colCtx M R root i x) ha'' ha hsrc' hC'
  subst haa
  exact runItemT_region rX h1 hOK hrun p hpL'

/-- **`BiTopLow` holds.** -/
theorem biTopLow : TSQ.BiTopLow := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pa hcu hcv hl hpa hlo he
    hab hpaup V cV hVc hcV hVt
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hxg, hxl⟩ := Recon.mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[x + (M.size - 1 - root.column) * i]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
  have hFR := E.FR
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  have hjlo : j < lo.length := TSQ.lower_index hD hj hcv hlo
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  obtain ⟨k, cv', hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo (List.getElem_mem hjlo)
  have hcv2 : Reserve.cell? M lo[j].2.src = some cv := by rw [← hlj]; exact hcv
  rw [hsk] at hcv2
  have hcvv : cv = cv' := Option.some.inj (hcv2.symm.trans hcvk)
  subst hcvv
  have hxk : Reserve.cell? M ⟨x, k⟩ = some cv := hcvk
  have hsrcj : (lo ++ us)[j].2.src = ⟨x, k⟩ := by rw [hlj]; exact hsk
  -- the row of `u`
  have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by
    have := hD.size; rw [this, List.length_append]; omega
  obtain ⟨_, hrow, _⟩ := hD.node hk (by omega)
  have hcuR : cu = (R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1] := by
    unfold Reserve.cell? at hcu
    simp only [Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some,
      Array.getElem?_eq_getElem hk] at hcu
    exact (Option.some.inj hcu).symm
  have hcurow : cu.row = stored lo[j].1.row := by
    rw [hcuR, hrow]; simp only [Nat.add_sub_cancel, hlj]
  -- the nodes `o`, `o⁺` and `pa`
  obtain ⟨oN, hoN, hocell⟩ := ControlProof.node_of_cell? hxk
  have hox : oN.1.val = x := by have := congrArg Ref.column hoN; simpa [Frame.ref] using this
  have hoi : oN.2.val = k := by have := congrArg Ref.index hoN; simpa [Frame.ref] using this
  have hoR : Real oN := by show 0 < oN.2.val; omega
  have hoh : (Frame.ofMountain M).height oN = cv.row := by
    show ((Frame.ofMountain M).cell oN).row = cv.row; rw [hocell]
  obtain ⟨c', hc', hc't⟩ := hab
  rw [hsrcj] at hc'
  obtain ⟨opN, hopN, hopcell⟩ := ControlProof.node_of_cell? hc'
  have hup : (Frame.ofMountain M).upper oN = some opN :=
    LowerChainRecon.upper_of_above (by rw [hopN, hoN])
  have hopτ : (Frame.ofMountain M).height opN < t.row := by
    show ((Frame.ofMountain M).cell opN).row < t.row; rw [hopcell]; exact hc't
  obtain ⟨paN, hpaN, hpac, hpaR, hpaH⟩ := highestIn_of_highestAtMost hpa
  subst hpaN
  obtain ⟨ca, hca, hθ⟩ := hpaup
  have hpabar : ∀ up, (Frame.ofMountain M).upper paN = some up →
      t.row ≤ (Frame.ofMountain M).height up := by
    intro up hupa
    have href := LowerChainRecon.above_of_upper hupa
    have hcu' : Reserve.cell? M (LowerChain.above (Frame.ref paN)) =
        some ((Frame.ofMountain M).cell up) := by
      rw [← href]; exact ControlProof.cell?_ref up
    rw [hca] at hcu'
    show t.row ≤ ((Frame.ofMountain M).cell up).row
    rw [← Option.some.inj hcu']
    exact hθ
  have hl' : ((Frame.ofMountain M).cell oN).left = some l := by rw [hocell]; exact hl
  have hpa' : Reserve.highestAtMost M l.column ((Frame.ofMountain M).height oN) =
      some (Frame.ref paN) := by rw [hoh]; exact hpa
  have hasc := asc_root hb (R := R) (root := root) (i := i) hox hoR hup hopτ hl' he hpa' hpabar
  have hpaτ : (Frame.ofMountain M).height paN < t.row := lt_of_le_of_lt hpaH.1 hlo
  have hpac' : paN.1.val = root.column := by rw [hpac, he]
  obtain ⟨a, ha1, hpaa, hτ⟩ := root_tau hTop hpac' hpaτ hpabar
  -- official rows
  have hpa1 : (1 : Row) ≤ (Frame.ofMountain M).height paN := one_le_height hO hpaR
  have hcv1 : (1 : Row) ≤ cv.row := by rw [← hoh]; exact one_le_height hO hoR
  have hτo : official t.row = Row.B (official a)
      (official ((Frame.ofMountain M).cell paN).row) := by
    rw [hτ]; exact Inner.Clean.official_B ha1 hpa1
  have hbC : official ((Frame.ofMountain M).cell paN).row ≤ official cv.row :=
    Recon.official_mono hpa1 hpaH.1
  have hCτ : official cv.row < official t.row := Recon.official_strictMono hcv1 hlo
  -- the first item of `C`
  obtain ⟨k', j', hmem, hin⟩ := Recon.CutPredMD.lowerItems_cover hCτ
  obtain ⟨k'', j'', _, hj'', heq⟩ := mem_lowerItems hmem
  simp only [Prod.mk.injEq, Item.mk.injEq] at heq
  obtain ⟨hkk, hss, _, _, _, _⟩ := heq
  have hkk' : k' = k'' := by omega
  subst hkk'
  have hjj : j' = j'' := by
    have := congrArg (fun r : Row => r.coeff k') hss
    simp only [slot_coeff_at] at this
    exact this
  subst hjj
  rw [hτo] at hin hj''
  have hidx := first_index hbC hj'' hin
  -- the level is at least `2`
  obtain ⟨d, rfl⟩ : ∃ d, k' = d + 1 := by
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · exfalso
      have hJ : Row.jump (official a) (official ((Frame.ofMountain M).cell paN).row) = 0 := by
        rw [← hidx.1, h0]
      have hab' := Row.jump_eq_zero.mp hJ
      have hc'1 : (1 : Row) ≤ c'.row := by
        rw [← hopcell]; exact one_le_height hO (by
          obtain ⟨hc1, hc2⟩ := upper_spec hup
          show 0 < opN.2.val; omega)
      have hlt1 : official cv.row < official c'.row := by
        apply Recon.official_strictMono hcv1
        rw [← hoh, ← hopcell]
        obtain ⟨hc1, hc2⟩ := upper_spec hup
        exact ControlProof.height_lt_of_index hO hc1.symm (by omega)
      have hlt2 : official c'.row < official t.row := Recon.official_strictMono hc'1 hc't
      rw [hτo, Row.B, hJ, hab'] at hlt2
      have hge : official ((Frame.ofMountain M).cell paN).row ≤ official c'.row :=
        le_of_lt (lt_of_le_of_lt hbC hlt1)
      have := Recon.LowerPB.Cone.row_eq_of_lt_bump0 hge hlt2
      rw [this] at hlt1
      exact absurd (lt_of_le_of_lt hbC hlt1) (lt_irrefl _)
    · exact ⟨k' - 1, by omega⟩
  -- the first item `F` and its rows
  have hinT : inRegion (d + 1 + 1) (slot (d + 1 + 2) (official t.row) j') (official cv.row) =
      true := by rw [hτo]; exact hin
  have hbS : inRegion (d + 1 + 1) (slot (d + 1 + 2) (official t.row) j')
      (official ((Frame.ofMountain M).cell paN).row) = true := by
    rw [hτo]; exact root_mem_first hbC hj'' hin
  have hbelow : ∀ r r' : Row, r < official t.row →
      inRegion (d + 1 + 1) (slot (d + 1 + 2) (official t.row) j') r' = true →
      inRegion (d + 1 + 1) (slot (d + 1 + 2) (official t.row) j') r = false → r < r' := by
    rw [hτo]; exact fun r r' => below_first hbC hj'' hin
  have hFT : InTree (colCtx M R root i x) (official t.row) (d + 2)
      ⟨slot (d + 1 + 2) (official t.row) j', slot (d + 1 + 2) (official t.row) j', none, 0,
        false⟩ := ⟨_, hmem, .refl _ _⟩
  -- the root top of `F` is `pa`
  have hmemPa : (Frame.ref paN, (Frame.ofMountain M).cell paN) ∈ realNodes M root.column := by
    have := Classification.Proofs.CopyShape.mem_realNodes_of_cell' (ControlProof.cell?_ref paN)
      (show 1 ≤ (Frame.ref paN).index from hpaR)
    rwa [show (Frame.ref paN).column = root.column from hpac'] at this
  have hρ : topIn M root.column (d + 2) (slot (d + 1 + 2) (official t.row) j') =
      some (Frame.ref paN, (Frame.ofMountain M).cell paN) := by
    obtain ⟨ρr, ρc, htopρ, _⟩ := LowerLeftProof.top_ge hb hmemPa hbS
    obtain ⟨hρmem, hρin, hρmax⟩ := Recon.RowLaw.topIn_spec htopρ
    have hle1 := hρmax _ hmemPa hbS
    obtain ⟨hρc, hρi, hρcell⟩ := Classification.mem_realNodes hρmem
    obtain ⟨ρN, hρN, hρNcell⟩ := ControlProof.node_of_cell? hρcell
    have hρτ : ρc.row < t.row := by
      have h1 := (Classification.lowerItems_below _ _ hmem).1 _ hρin
      have hρ1 : (1 : Row) ≤ ρc.row := Classification.one_le_row hVM hρcell hρi
      exact Recon.row_lt_of_official (hTop.row_one_le) h1
    have hρcol : ρN.1 = paN.1 := by
      apply Fin.ext
      have := congrArg Ref.column hρN
      simp only [Frame.ref] at this
      rw [this, hρc, hpac']
    have hidx2 : ρN.2.val ≤ paN.2.val := by
      by_contra hn
      have hlen : paN.2.val + 1 < (Frame.ofMountain M).length paN.1 := by
        have := ρN.2.isLt
        have hl2 : (Frame.ofMountain M).length ρN.1 = (Frame.ofMountain M).length paN.1 := by
          rw [hρcol]
        omega
      have hupp := Recon.LowerPB.Cone.upper_of_lt hlen
      have h1 := hpabar _ hupp
      have h2 : (Frame.ofMountain M).height ⟨paN.1, ⟨paN.2.val + 1, hlen⟩⟩ ≤
          (Frame.ofMountain M).height ρN :=
        ControlProof.height_le_of_index hO hρcol.symm (by show paN.2.val + 1 ≤ ρN.2.val; omega)
      have h3 : (Frame.ofMountain M).height ρN = ρc.row := by
        show ((Frame.ofMountain M).cell ρN).row = _; rw [hρNcell]
      exact absurd (lt_of_le_of_lt (h1.trans (h2.trans (le_of_eq h3))) hρτ) (lt_irrefl _)
    have hle1' : paN.2.val ≤ ρr.index := hle1
    have hρNi : ρN.2.val = ρr.index := by
      have := congrArg Ref.index hρN
      simpa [Frame.ref] using this
    have hρeq : ρN = paN := ControlProof.node_eq_of_index hρcol (by omega)
    have e1 : ρr = Frame.ref paN := by rw [← hρeq]; exact hρN.symm
    have e2 : ρc = (Frame.ofMountain M).cell paN := by rw [← hρeq]; exact hρNcell.symm
    rw [htopρ, e1, e2]
  -- the new columns `X` and `B`
  have hNCx := TSQ.nc_of_colData' E hi1 hD
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hNCb := Classification.Proofs.P3T.boundary_nc hNCx
  have hom : ((⟨x, k⟩ : Ref), cv) ∈ realNodes M x :=
    Classification.Proofs.CopyShape.mem_realNodes_of_cell' hxk hk1
  obtain ⟨axr, axc, hax, _⟩ := LowerLeftProof.top_ge hb hom hinT
  obtain ⟨_, hρκ, q, hq, hqc⟩ := bnd_lift hNCx hNCb hFT rfl rfl hax hρ hasc
  -- the traced lower part and the non-gap copy `g`
  obtain ⟨outs, houts, hlo⟩ := lowerT_outs hD.hlo
  obtain ⟨g, hg, _, hgsrc⟩ := Classification.Proofs.CopyShape.Found.lowerT_covers hrun hTop hi1
    hin (colCtx_bctx hNCx) hD.hlo hk1 hxk hCτ
  rw [hlo] at hg
  obtain ⟨aF, haF, hFa⟩ := List.getElem_of_mem hmem
  have hrowS : ∀ p ∈ outs.flatten, p.2.src = ⟨x, k⟩ →
      inRegion (d + 2) (slot (d + 1 + 2) (official t.row) j') p.1.row = true := by
    intro p hp hps
    have := first_row hNCx houts haF (cv := cv) (by rw [hFa]; exact hinT) hp
      (by rw [hps]; exact hxk)
    rw [hFa] at this
    exact this
  have hno : nodeAt M x (official cv.row) = some (⟨x, k⟩, cv) :=
    Classification.Proofs.CutGap.nodeAt_of_cell hVM hxk hk1
  have hqc' : (official q.2.row).coeff d = (official ((Frame.ofMountain M).cell paN).row).coeff d +
      (heightOf (d + 2) (topIn M (M.size - 1) (d + 2) (slot (d + 1 + 2) (official t.row) j')) -
        (official ((Frame.ofMountain M).cell paN).row).coeff d) * (i' + 1) := by
    simp only [height_eq] at hρκ hqc
    rw [hqc, Nat.mul_succ]
    omega
  obtain ⟨e, he', hesrc, hqe⟩ := lift_desc hNCx (by omega) houts hno hasc hg hgsrc hxk hFT rfl rfl
    hρ hinT hbC rfl (by simpa [height_eq] using hρκ) hq hqc' (fun _ => hrowS g hg hgsrc)
  -- `e` is at or below the top copy `u`
  have heS := hrowS e he' hesrc
  have helo : e ∈ lo := by rw [hlo]; exact he'
  obtain ⟨je, hje, hjee⟩ := List.getElem_of_mem helo
  have hjej : je ≤ j := by
    by_contra hn
    have hje' : je < (lo ++ us).length := by rw [List.length_append]; omega
    have := htop je hje' hj (by omega)
    rw [List.getElem_append_left hje, hjee, hesrc, hsrcj] at this
    exact this rfl
  have hk2 : je + 1 < (R[x + (M.size - 1 - root.column) * (i' + 1)]'hXR).size := by omega
  obtain ⟨_, hrow2, _⟩ := hD.node hk2 (by omega)
  have hrow2' : (R[x + (M.size - 1 - root.column) * (i' + 1)]'hXR)[je + 1].row = stored e.1.row := by
    rw [hrow2]; simp only [Nat.add_sub_cancel]; rw [List.getElem_append_left hje, hjee]
  have hmono := (hFR.rows_strict ⟨x + (M.size - 1 - root.column) * (i' + 1), hXR⟩).monotone
    (show (⟨je + 1, hk2⟩ : Fin _) ≤ ⟨j + 1, hk⟩ from by show je + 1 ≤ j + 1; omega)
  have heu : stored e.1.row ≤ cu.row := by
    rw [← hrow2', hcurow]
    rw [hcuR] at hcurow
    have : (R[x + (M.size - 1 - root.column) * (i' + 1)]'hXR)[j + 1].row = stored lo[j].1.row := by
      rw [← hcurow]
    rw [← this]
    exact hmono
  -- the node `V` of `B`
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hrun
  have hVR : MountainValid R := hBasic.valid
  by_cases hV0 : V.index = 0
  · have : cV.row = 0 := by
      obtain ⟨VN, hVN, hVNcell⟩ := ControlProof.node_of_cell? hcV
      have hi0' : VN.2.val = 0 := by
        have := congrArg Ref.index hVN; simp only [Frame.ref] at this; omega
      have hlen : 0 < (Frame.ofMountain R).length VN.1 := by have := VN.2.isLt; omega
      have h0 : VN.2 = ⟨0, hlen⟩ := Fin.ext hi0'
      rw [← hVNcell]
      show ((Frame.ofMountain R).cells VN.1 VN.2).row = 0
      rw [h0, hFR.phantom VN.1 hlen]; rfl
    rw [this]; exact Row.zero_le _
  · have hV1 : 1 ≤ V.index := by omega
    have hVmem : (V, cV) ∈ realNodes R (root.column + (M.size - 1 - root.column) * (i' + 1)) := by
      have := Classification.Proofs.CopyShape.mem_realNodes_of_cell' hcV hV1
      rwa [hVc] at this
    have hcV1 : (1 : Row) ≤ cV.row := Classification.one_le_row hVR hcV hV1
    have hVτ : official cV.row < official t.row := Recon.official_strictMono hcV1 hVt
    have hVe : official cV.row ≤ e.1.row := by
      cases hVS : inRegion (d + 2) (slot (d + 1 + 2) (official t.row) j') (official cV.row) with
      | true =>
        obtain ⟨hqmem, _, hqmax⟩ := Recon.RowLaw.topIn_spec hq
        have hidx := hqmax (V, cV) hVmem hVS
        have hle := Classification.Proofs.CopyShape.MHProof.row_le_of_index hVR hVmem hqmem hidx
        exact (Recon.official_mono hcV1 hle).trans hqe
      | false => exact (hbelow _ _ hVτ heS hVS).le
    have : cV.row ≤ stored e.1.row := by
      rw [← Classification.stored_official hcV1]
      exact Classification.stored_mono hVe
    exact this.trans heu

end OmegaY.Official.Recon.TSQ.BTL

namespace OmegaY.Official.Recon.TSQ.BTL

/-- **`StartRootTopUp` holds.** -/
theorem startRootTopUp : TopStartFixParts.StartRootTopUp :=
  TSQ.startRootTopUp_of_biTopLow biTopLow

end OmegaY.Official.Recon.TSQ.BTL

#print axioms OmegaY.Official.Recon.TSQ.BTL.first_row
#print axioms OmegaY.Official.Recon.TSQ.BTL.biTopLow
#print axioms OmegaY.Official.Recon.TSQ.BTL.startRootTopUp
