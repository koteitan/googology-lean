/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQRootTop.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQCutRight

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `StartRootTopUp` from one statement about the boundary column (`TSQ`)

`StartRootTopUp` (`TopStartFixParts.lean`): `u` is the top copy (block `i ≥ 1`) of `o`, a node
below `row t` whose leg is the root column `c_r`, `o` has a node above it below `row t`,
`pa = hAM(c_r, row o)`, `pe = hAM(B_i, row u)` with `B_i = c_r + w·i`, and the node `pa⁺` above
`pa` is at or above `row t`. Then the node above `pe` has the row of `pa⁺`.

## The reduction

`TopChain.stand_of_highest` (proved) gives the clause when `pa` and `pe` are the highest nodes of
their columns below `row t`. For `pa` this is `pa⁺ ≥ row t`. For `pe` it is the open statement

* `BiTopLow` (**open**, numerically checked): in this setting every node of `B_i` below `row t` is
  at or below the row of `u` (then `pe`, the highest node of `B_i` at or below `row u`, is the
  highest node of `B_i` below `row t`).

Result: `startRootTopUp_of_biTopLow : BiTopLow → StartRootTopUp`.
-/

namespace OmegaY.Official.Recon.TSQ

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopChain
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- **Open.** In the setting of `StartRootTopUp` (the node `pa⁺` above `pa` at or above
`row t`), every node of the boundary column `B_i = c_r + w·i` below `row t` is at or below the
row of `u`. -/
def BiTopLow : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pa,
      Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      cv.row < t.row → l.column = root.column →
      HasAboveLow M t.row es[j].2.src →
      (∃ ca, Reserve.cell? M (above pa) = some ca ∧ t.row ≤ ca.row) →
      ∀ V cV, V.column = root.column + (M.size - 1 - root.column) * i →
        Reserve.cell? R V = some cV → cV.row < t.row → cV.row ≤ cu.row

/-- **`StartRootTopUp` from `BiTopLow`.** -/
theorem startRootTopUp_of_biTopLow (hB : BiTopLow) : TopStartFixParts.StartRootTopUp := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo he hab ca hca hθ
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[x + (M.size - 1 - root.column) * i]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := env_of hrun hTop hXR (by omega)
  have hG := E.G
  have hF := E.FR
  have hBi := hB s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pa hcu hcv hl
    hpa hlo he hab ⟨ca, hca, hθ⟩
  -- the row of `u` is below `row t`
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  have hjlo : j < lo.length := lower_index hD hj hcv hlo
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
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
  have hlt : lo[j].1.row < official t.row := hD.lo_lt _ (List.getElem_mem _)
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  have hcut : cu.row < t.row := by
    rw [hcurow]
    have := Recon.stored_strictMono hlt
    rwa [Classification.stored_official ht1] at this
  -- the highest nodes
  obtain ⟨paN, hpaN, hpac, hpar, hpaH⟩ := highestIn_of_highestAtMost hpa
  obtain ⟨peN, hpeN, hpec, _, hpeH⟩ := highestIn_of_highestAtMost hpe
  subst hpaN hpeN
  have hpac' : paN.1.val = root.column := by rw [hpac, he]
  have hpec' : peN.1.val = root.column + (M.size - 1 - root.column) * i := by
    rw [hpec, he, Classification.Proofs.ChainCorr.mapColumn_of_ge le_rfl]
  have hax : paN.1.val < M.size - 1 := by omega
  have hAc : peN.1.val = shiftCol root.column (M.size - 1 - root.column) i paN.1.val := by
    rw [shiftCol_of_le (le_of_eq hpac'.symm), hpac', hpec']
  have ha : HighestIn (Frame.ofMountain M) (· < t.row) paN := by
    refine ⟨lt_of_le_of_lt hpaH.1 hlo, fun v hv hvt => ?_⟩
    by_contra hn
    have hlen : paN.2.val + 1 < (Frame.ofMountain M).length paN.1 := by
      have h1 := v.2.isLt
      have h2 : (Frame.ofMountain M).length v.1 = (Frame.ofMountain M).length paN.1 := by rw [hv]
      omega
    let up : (Frame.ofMountain M).Node := ⟨paN.1, ⟨paN.2.val + 1, hlen⟩⟩
    have hup : Reserve.cell? M (above (Frame.ref paN)) = some ((Frame.ofMountain M).cell up) := by
      have := LowerChainRecon.cell?_ref up
      simpa [above, Frame.ref, up] using this
    have hθ' : t.row ≤ (Frame.ofMountain M).height up := by
      have := Option.some.inj (hca.symm.trans hup)
      show t.row ≤ ((Frame.ofMountain M).cell up).row
      rw [← this]
      exact hθ
    have hle : (Frame.ofMountain M).height up ≤ (Frame.ofMountain M).height v :=
      height_le_of_index hG (a := up) (b := v) hv.symm (by simp [up]; omega)
    exact absurd (lt_of_le_of_lt (hθ'.trans hle) hvt) (lt_irrefl _)
  have hA : HighestIn (Frame.ofMountain R) (· < t.row) peN := by
    refine ⟨lt_of_le_of_lt hpeH.1 hcut, fun V hV hVt => ?_⟩
    have hVc : (Frame.ref V).column = root.column + (M.size - 1 - root.column) * i := by
      show V.1.val = _
      rw [hV, hpec']
    have hle := hBi (Frame.ref V) _ hVc (LowerChainRecon.cell?_ref V) hVt
    exact hpeH.2 V hV hle
  have hS := stand_of_highest E hi1 hin (P := (· < t.row)) (fun r r' h h' => lt_of_le_of_lt h h')
    (fun r h => h) hpar hax hAc ha hA
  exact (hS.2.1 hpac').2.1 ca hca hθ

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Recon.TSQ.startRootTopUp_of_biTopLow
