/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQRootValueX0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQBiTopAsc

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `RootValueHi` in the last column (`TSQ`)

`RootValueHi` (`TSQRootValueParts.lean`) when the node `o` is in the last column `x₀`: the root
`r = P(t⁻)` is above `g` (the node `g⁺` above `g` is below `τ`, while `r⁺` is not), so the row
shadow of `P(t⁻) = r` (`P_rowShadow`) gives a path of numerical parents at the row `C` from the
node of `x₀` at the row `C`, which is `o`, to `g`; hence `v(g) < v(o)`.

What remains is `RootValueIn`: `RootValueHi` for a node `o` strictly left of `x₀`.

* `rootValueHi_of_in : RootValueIn → RootValueHi`;
* `topStartPaOUp_of_rootValueIn : RootValueIn → TopStartPaOUp`.
-/

namespace OmegaY.Official.Recon.TSQ.RVP

open Canonical Expansion Classification Reserve
open OmegaY.Geometry OmegaY.Geometry.Frame

/-- **Open (about `M(s)` alone).** `RootValueHi` for a node `o` strictly left of `x₀`. -/
def RootValueIn : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (x k : Nat) (co : Cell) (l : Ref), root.column < x → x < M.size - 1 → 1 ≤ k →
      Reserve.cell? M ⟨x, k⟩ = some co → co.row < t.row → co.left = some l →
      root.column < l.column →
      (∃ c', Reserve.cell? M ⟨x, k + 1⟩ = some c' ∧ c'.row < t.row) →
      referenceRow (official co.row) = official co.row →
      ∀ pa cpa, Reserve.highestAtMost M l.column co.row = some pa →
        Reserve.cell? M pa = some cpa → cpa.row = co.row →
        reachesRoot M root.column (l.column + 1) pa = .ok true →
      ∀ g cg, g.column = root.column → Reserve.cell? M g = some cg → cg.row = co.row →
        co.row ≠ 1 →
        (∃ ca, Reserve.cell? M (Classification.Proofs.ChainCorr.LowerChain.above g) = some ca ∧
          ca.row < t.row) →
        cg.value < co.value

variable {M : Mountain}

/-- The node `t⁻` below the top of the last column and its numerical parent, the root `r`,
whose node above is at or above `τ`. -/
theorem top_parent {s : List Nat} {t : Cell} {root : Ref} (hTop : Recon.Top s M t root) :
    ∃ ny nr : (Frame.ofMountain M).Node, Real ny ∧ ny.1.val = M.size - 1 ∧
      (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root ∧
      (∀ up, (Frame.ofMountain M).upper nr = some up → t.row ≤ (Frame.ofMountain M).height up) := by
  have hb := hTop.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  have hrl := hTop.lt
  have hsz : M.size - 1 < M.size := by omega
  have htop := hTop.top
  rw [Array.getElem?_eq_getElem hsz] at htop
  simp only [Option.bind_some, Array.back?] at htop
  obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
  let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
  have hT3 : 3 ≤ M[M.size - 1].size := by
    by_contra hn
    have h2 : M[M.size - 1].size = 2 := by
      have := hO.length_ge_two x0
      change 2 ≤ M[M.size - 1].size at this
      omega
    have htrow : t.row = 1 := by
      rw [← hTt]
      simp only [h2]
      exact hO.bottom_row x0 (by show 1 < M[M.size - 1].size; omega)
    exact hTop.real (by rw [htrow]; exact Classification.official_one)
  have hyl : M[M.size - 1].size - 2 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 2 < M[M.size - 1].size
    omega
  let ny : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 2, hyl⟩⟩
  have hTl : M[M.size - 1].size - 1 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 1 < M[M.size - 1].size
    omega
  let nt : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 1, hTl⟩⟩
  have hyreal : Frame.Real ny := by show 0 < M[M.size - 1].size - 2; omega
  have hyt : (Frame.ofMountain M).upper ny = some nt :=
    ControlProof.upper_eq_of_index rfl
      (by show M[M.size - 1].size - 1 = M[M.size - 1].size - 2 + 1; omega)
  have hntcell : (Frame.ofMountain M).cell nt = t := hTt
  have hrawy0 : Reserve.rawParent M ⟨M.size - 1, M[M.size - 1].size - 2⟩ = some root := by
    unfold Reserve.rawParent
    rw [Array.getElem?_eq_getElem hsz]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [show M[M.size - 1].size - 2 + 1 = M[M.size - 1].size - 1 by omega, htop]
    simpa using hTop.left
  have hrawy : ((Frame.ofMountain M).upper ny).bind
      (fun v => ((Frame.ofMountain M).cell v).left) = some root :=
    (ControlProof.rawParent_ref ny).symm.trans hrawy0
  obtain ⟨nr, hPy, hnr⟩ : ∃ nr, (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root := by
    rw [hyt] at hrawy
    simp only [Option.bind_some] at hrawy
    obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid nt root hrawy
    have hnr := Frame.lookup_spec hlk
    have hleft : ((Frame.ofMountain M).cell nt).left = some (Frame.ref nr) := by
      rw [hnr]; exact hrawy
    refine ⟨nr, ?_, hnr⟩
    rw [← hN.rawParent_eq_P hyreal]
    exact Frame.rawParent_eq_of_upper_left hyt hleft
  have hnt : (Frame.ofMountain M).height nt = t.row := by
    show ((Frame.ofMountain M).cell nt).row = t.row; rw [hntcell]
  refine ⟨ny, nr, hyreal, rfl, hPy, hnr, fun up hup => ?_⟩
  rw [← hnt]
  exact father_upper_bound_nodes hN hPy hyt hup

/-- **`RootValueHi` from `RootValueIn`** (the last column by the row shadow of `P(t⁻) = r`). -/
theorem rootValueHi_of_in (hIn : RootValueIn) : RootValueHi := by
  intro s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow hr' g cg
    hgc hcg hgrow hC hgup
  rcases Nat.lt_or_eq_of_le hxx with hlt | heq
  · exact hIn s M t root hTop x k co l hcx hlt hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow
      hr' g cg hgc hcg hgrow hC hgup
  · subst heq
    have hb := hTop.build
    have hN := build_normal_of_success hb
    have hO := hN.toOrdered
    obtain ⟨ny, nr, hyR, hyc, hPy, hnr, hnrbar⟩ := top_parent hTop
    obtain ⟨oN, hoN, hocell⟩ := ControlProof.node_of_cell? hco
    obtain ⟨gN, hgN, hgcell⟩ := ControlProof.node_of_cell? hcg
    have hoR : Real oN := by
      show 0 < oN.2.val
      have := congrArg Ref.index hoN; simp [Frame.ref] at this; omega
    have hgR : Real gN := by
      apply Recon.LowerPB.Cone.real_of_one_le_height hO
      show (1 : Row) ≤ ((Frame.ofMountain M).cell gN).row
      rw [hgcell, hgrow, ← hocell]
      exact one_le_height hO hoR
    have hgcol : gN.1 = nr.1 := by
      apply Fin.ext
      have h1 := congrArg Ref.column hgN
      have h2 := congrArg Ref.column hnr
      simp only [Frame.ref] at h1 h2
      rw [h1, h2, hgc]
    -- `g` is at or below `r`
    obtain ⟨ca, hca, hcat⟩ := hgup
    have hgle : (Frame.ofMountain M).height gN ≤ (Frame.ofMountain M).height nr := by
      by_contra hn
      have hidx : nr.2.val < gN.2.val := by
        by_contra hn'
        exact hn (ControlProof.height_le_of_index hO hgcol (by omega))
      have hlen : nr.2.val + 1 < (Frame.ofMountain M).length nr.1 := by
        have := gN.2.isLt
        have hl2 : (Frame.ofMountain M).length gN.1 = (Frame.ofMountain M).length nr.1 := by
          rw [hgcol]
        omega
      have hup := Recon.LowerPB.Cone.upper_of_lt hlen
      have h1 := hnrbar _ hup
      -- the node above `g` is at or above the node above `r`
      have hglen : gN.2.val + 1 < (Frame.ofMountain M).length gN.1 := by
        obtain ⟨gu, hgu, hguc⟩ := ControlProof.node_of_cell? hca
        have := congrArg Ref.index hgu
        simp only [Frame.ref, Classification.Proofs.ChainCorr.LowerChain.above] at this
        have h2 := gu.2.isLt
        have hc : gu.1 = gN.1 := by
          apply Fin.ext
          have := congrArg Ref.column hgu
          simp only [Frame.ref, Classification.Proofs.ChainCorr.LowerChain.above] at this
          rw [this]
          have := congrArg Ref.column hgN
          simp only [Frame.ref] at this
          rw [this]
        have hl2 : (Frame.ofMountain M).length gu.1 = (Frame.ofMountain M).length gN.1 := by
          rw [hc]
        have hgi := congrArg Ref.index hgN
        simp only [Frame.ref] at hgi
        omega
      have hgu := Recon.LowerPB.Cone.upper_of_lt hglen
      have hguh : (Frame.ofMountain M).height ⟨gN.1, ⟨gN.2.val + 1, hglen⟩⟩ = ca.row := by
        have href := LowerChainRecon.above_of_upper hgu
        have hc' : Reserve.cell? M (Classification.Proofs.ChainCorr.LowerChain.above
            (Frame.ref gN)) = some ((Frame.ofMountain M).cell ⟨gN.1, ⟨gN.2.val + 1, hglen⟩⟩) := by
          rw [← href]; exact ControlProof.cell?_ref _
        rw [hgN, hca] at hc'
        show ((Frame.ofMountain M).cell _).row = _
        rw [← Option.some.inj hc']
      have h3 : (Frame.ofMountain M).height ⟨nr.1, ⟨nr.2.val + 1, hlen⟩⟩ ≤
          (Frame.ofMountain M).height ⟨gN.1, ⟨gN.2.val + 1, hglen⟩⟩ :=
        ControlProof.height_le_of_index hO hgcol.symm (by show nr.2.val + 1 ≤ gN.2.val + 1; omega)
      rw [hguh] at h3
      exact absurd (lt_of_le_of_lt (h1.trans h3) hcat) (lt_irrefl _)
    obtain ⟨v, _, hvc, _, hvh, hvpath⟩ := P_rowShadow hN hPy gN hgR hgcol hgle
    have hvo : v = oN := by
      apply node_eq_of_column_height hO
      · apply Fin.ext
        have := congrArg Ref.column hoN
        simp only [Frame.ref] at this
        rw [hvc, hyc, this]
      · show ((Frame.ofMountain M).cell v).row = ((Frame.ofMountain M).cell oN).row
        have : ((Frame.ofMountain M).cell v).row = ((Frame.ofMountain M).cell gN).row := hvh
        rw [this, hgcell, hocell, hgrow]
    subst hvo
    have hne : v ≠ gN := by
      intro h
      have h1 := congrArg (fun z : (Frame.ofMountain M).Node => z.1.val) h
      have h2 := congrArg Ref.column hoN
      have h3 := congrArg Ref.column hgN
      simp only [Frame.ref] at h1 h2 h3
      omega
    have hval : (Frame.ofMountain M).value gN < (Frame.ofMountain M).value v := by
      cases hvpath with
      | refl => exact absurd rfl hne
      | cons hP rest => exact lt_of_le_of_lt (rest.value_le hO) (P_value hO hP).2
    have hgv : (Frame.ofMountain M).value gN = cg.value := by
      show ((Frame.ofMountain M).cell gN).value = _; rw [hgcell]
    have hov : (Frame.ofMountain M).value v = co.value := by
      show ((Frame.ofMountain M).cell v).value = _; rw [hocell]
    rw [← hgv, ← hov]
    exact hval

/-- **`TopStartPaOUp` from `RootValueIn`.** -/
theorem topStartPaOUp_of_rootValueIn (hIn : RootValueIn) : TopStartFixParts.TopStartPaOUp :=
  topStartPaOUp_of_rootValueHi (rootValueHi_of_in hIn)

end OmegaY.Official.Recon.TSQ.RVP

#print axioms OmegaY.Official.Recon.TSQ.RVP.top_parent
#print axioms OmegaY.Official.Recon.TSQ.RVP.rootValueHi_of_in
#print axioms OmegaY.Official.Recon.TSQ.RVP.topStartPaOUp_of_rootValueIn
