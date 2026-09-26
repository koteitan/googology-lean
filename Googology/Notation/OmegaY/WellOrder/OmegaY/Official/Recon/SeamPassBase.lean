/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/SeamPassBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLRoot
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# Passing a node of the root column (the base of `SeamStep`, `SeamStart`)

Notation: `c_r = col root`, `x₀ = |M| - 1`, `w = x₀ - c_r`, `τ = row t`, `B_i = c_r + w·i`.

`PassOK Q o` (for a node `Q` of a new column with origin `o`): for every node `μ` of the root
column whose upper node `μ⁺` is below `τ`, if the chain of stored parents of `M(s)` from `o`
passes `μ`, then the chain of stored parents of `R` from `Q` passes `μ`. This is the analogue of
`Seam.ChainOK` (which asks for the nodes left of `c_r`) for the nodes of `c_r` below the root.

This file has the side of `M(s)` and the induction:

* `ub_chain` (frame form) and `ub_ref`: along a chain of stored parents of a normal frame, from
  `o` to `μ ≠ o`: `row μ ≤ row o`, `row o⁺ ≤ row μ⁺`, and `μ` is the highest node of its
  column below `row o⁺` (Phyrion's father upper bound, iterated with `HBAt`);
* `ub_below`: if the chain of `o` passes `μ` (in `c_r`, `μ⁺` below `τ`), then `o` and `o⁺` are
  below `τ` (this makes the upper emits and the steps at or above `τ` vacuous);
* `x0Pass`: the chain of a node `ν` of `x₀` below `τ` passes the highest node of `c_r` at or
  below `row ν` (the first part of the proof of `SRX0.x0Reach`);
* `passOK_of_step`: the strong induction on the column (as `Seam.chainOK_of_step`).
-/

namespace OmegaY.Official.Recon.SeamPass

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt above)
open Recon.TopChain.Seam (OrigAt NodeData)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## Reachability without a scale -/

/-- The chain of stored parents from `p` reaches `q` (at some scale). -/
def Reach (M : Mountain) (p q : Ref) : Prop := ∃ k, ScaleReach M k p q

theorem Reach.refl (M : Mountain) (p : Ref) : Reach M p p := ⟨0, ScaleReach.refl p⟩

theorem Reach.trans {M : Mountain} {p q r : Ref} (h1 : Reach M p q) (h2 : Reach M q r) :
    Reach M p r := by
  obtain ⟨k1, h1⟩ := h1
  obtain ⟨k2, h2⟩ := h2
  exact ⟨max k1 k2, Classification.Proofs.ChainCorr.ScaleReach.trans
    (Classification.Proofs.ChainCorr.reach_mono h1 (le_max_left _ _))
    (Classification.Proofs.ChainCorr.reach_mono h2 (le_max_right _ _))⟩

theorem Reach.of_step {M : Mountain} {k : Nat} {p q : Ref} (h : MStep M k p q) : Reach M p q :=
  ⟨k, Classification.Proofs.ChainCorr.MStep.reach h⟩

theorem Reach.column_le {M : Mountain} {p q : Ref} (h : Reach M p q) : q.column ≤ p.column := by
  obtain ⟨k, h⟩ := h
  exact h.column_le

/-- A chain from `p` to `q ≠ p` starts with a step of `p`. -/
theorem Reach.head {M : Mountain} {p q : Ref} (h : Reach M p q) (hne : p ≠ q) :
    ∃ p' k, MStep M k p p' ∧ Reach M p' q := by
  obtain ⟨k, h⟩ := h
  obtain ⟨p', hs, hr⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head h hne
  exact ⟨p', k, hs, k, hr⟩

/-- Two nodes of the same column on one chain are equal (the chain moves strictly left). -/
theorem Reach.eq_of_column {M : Mountain} {p q : Ref} (h : Reach M p q)
    (hc : q.column = p.column) : p = q := by
  by_contra hne
  obtain ⟨p', _, hs, hr⟩ := h.head hne
  have h1 := hs.column_lt
  have h2 := hr.column_le
  omega

/-- A chain of `M` left of `x₀` is a chain of `R`. -/
theorem Reach.old {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) {p q : Ref}
    (h : Reach M p q) (hp : p.column < M.size - 1) : Reach R p q := by
  obtain ⟨k, h⟩ := h
  exact ⟨k, Recon.TopChain.Seam.reach_old hrun hTop h hp⟩

/-! ## The father upper bound along a chain (frame form) -/

section FrameUB

variable {F : Frame}

/-- **Along a chain of stored parents of a normal frame** from a real node `o` to `μ ≠ o`: `o⁺`
exists, `row μ ≤ row o`, every node of the column of `μ` below `row o⁺` is at or below `μ`, and
`row o⁺ ≤ row μ⁺`. -/
theorem ub_chain (hN : F.Normal) :
    ∀ {o μ : F.Node}, RawChain F o μ → o ≠ μ → Real o →
      ∃ o', F.upper o = some o' ∧ F.height μ ≤ F.height o ∧
        (∀ v : F.Node, v.1 = μ.1 → F.height v < F.height o' → v.2.val ≤ μ.2.val) ∧
        (∀ μ', F.upper μ = some μ' → F.height o' ≤ F.height μ') := by
  intro o μ h
  induction h with
  | here => intro hne; exact absurd rfl hne
  | @step a b p hraw rest ih =>
    intro _ ha
    have hO := hN.toOrdered
    obtain ⟨a', hau, _⟩ := rawParent_spec hraw
    have hHB := CrossUpper.hbAt_of_normal hN ha a' b hau hraw
    have hPb : F.P a = some b := (hN.rawParent_eq_P ha).symm.trans hraw
    have hba : F.height b ≤ F.height a := Frame.P_height_le hO hPb
    have hbr : Real b := real_of_value_pos hO (P_value hO hPb).1
    have hup : ∀ b', F.upper b = some b' → F.height a' ≤ F.height b' := by
      intro b' hb'
      obtain ⟨h1, h2⟩ := upper_spec hb'
      by_contra hn
      push Not at hn
      have := hHB.2 b' h1 hn
      omega
    by_cases hbp : b = p
    · subst hbp
      exact ⟨a', hau, hba, hHB.2, hup⟩
    · obtain ⟨b', hbu, h1, h2, h3⟩ := ih hbp hbr
      have hab' := hup b' hbu
      exact ⟨a', hau, h1.trans hba, fun v hv hvl => h2 v hv (lt_of_lt_of_le hvl hab'),
        fun μ' hμ' => hab'.trans (h3 μ' hμ')⟩

end FrameUB

/-! ## The father upper bound along a chain (reference form) -/

section RefUB

variable {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}

/-- **The reference form of `ub_chain`** for `M = M(s)`. -/
theorem ub_ref (hTop : Recon.Top s M t root) {o μ : Ref} (h : Reach M o μ) (hne : o ≠ μ)
    (ho1 : 1 ≤ o.index) :
    ∃ co co', Reserve.cell? M o = some co ∧ Reserve.cell? M (above o) = some co' ∧
      co.row < co'.row ∧ (∃ cμ, Reserve.cell? M μ = some cμ) ∧
      (∀ cμ, Reserve.cell? M μ = some cμ → cμ.row ≤ co.row) ∧
      (∀ cμ', Reserve.cell? M (above μ) = some cμ' → co'.row ≤ cμ'.row) ∧
      (∀ jj cc, Reserve.cell? M ⟨μ.column, jj⟩ = some cc → cc.row < co'.row → jj ≤ μ.index) := by
  have hN : (Frame.ofMountain M).Normal := build_normal_of_success hTop.build
  have hO := hN.toOrdered
  obtain ⟨k, hk⟩ := h
  -- the cell of `o`
  have hco : ∃ co, Reserve.cell? M o = some co := by
    cases hk with
    | refl => exact absurd rfl hne
    | step _ hc _ _ _ _ => exact ⟨_, hc⟩
  obtain ⟨co, hco⟩ := hco
  obtain ⟨oN, hoN, hoNc⟩ := LowerChainRecon.node_of_cell hco
  obtain ⟨μN, hμN, hch⟩ := LowerChainRecon.rawChain_of_scaleReach hk oN hoN
  have hne' : oN ≠ μN := by intro h; apply hne; rw [← hoN, ← hμN, h]
  have hor : Real oN := by
    show 0 < oN.2.val
    have := congrArg Ref.index hoN; simp only [Frame.ref] at this; omega
  obtain ⟨o', hou, h1, h2, h3⟩ := ub_chain hN hch hne' hor
  have hco' : Reserve.cell? M (above o) = some ((Frame.ofMountain M).cell o') := by
    rw [← hoN, ← LowerChainRecon.above_of_upper hou]; exact LowerChainRecon.cell?_ref o'
  obtain ⟨ho'1, ho'2⟩ := upper_spec hou
  have hlt : (Frame.ofMountain M).height oN < (Frame.ofMountain M).height o' :=
    height_lt_of_index hO ho'1.symm (by omega)
  have hcμN : Reserve.cell? M μ = some ((Frame.ofMountain M).cell μN) := by
    rw [← hμN]; exact LowerChainRecon.cell?_ref μN
  refine ⟨co, (Frame.ofMountain M).cell o', hco, hco', ?_, ⟨_, hcμN⟩, ?_, ?_, ?_⟩
  · rw [← hoNc]; exact hlt
  · intro cμ hcμ
    have : cμ = (Frame.ofMountain M).cell μN := by
      rw [← hμN, LowerChainRecon.cell?_ref] at hcμ; exact (Option.some.inj hcμ).symm
    rw [this, ← hoNc]; exact h1
  · intro cμ' hcμ'
    obtain ⟨μ'N, hμ'N, hμ'c⟩ := LowerChainRecon.node_of_cell hcμ'
    have hu : (Frame.ofMountain M).upper μN = some μ'N :=
      LowerChainRecon.upper_of_above (by rw [hμ'N, hμN])
    have := h3 μ'N hu
    change ((Frame.ofMountain M).cell o').row ≤ _
    rw [← hμ'c]; exact this
  · intro jj cc hcc hlt'
    obtain ⟨vN, hvN, hvc⟩ := LowerChainRecon.node_of_cell hcc
    have hv1 : vN.1 = μN.1 := Fin.ext (by
      have a1 := congrArg Ref.column hvN; have a2 := congrArg Ref.column hμN
      simp only [Frame.ref] at a1 a2; omega)
    have := h2 vN hv1 (by change ((Frame.ofMountain M).cell vN).row < _; rw [hvc]; exact hlt')
    have a1 := congrArg Ref.index hvN; have a2 := congrArg Ref.index hμN
    simp only [Frame.ref] at a1 a2
    omega

/-- **The chain of `o` passes `μ` (in `c_r`, `μ⁺` below `τ`)**: then `o ≠ μ` gives `o⁺` below
`τ`, and `o` itself is below `τ`. -/
theorem ub_below (hTop : Recon.Top s M t root) {o μ : Ref} (h : Reach M o μ) (hne : o ≠ μ)
    (ho1 : 1 ≤ o.index) {cμ' : Cell} (hcμ' : Reserve.cell? M (above μ) = some cμ')
    (hμτ : cμ'.row < t.row) :
    ∃ co co', Reserve.cell? M o = some co ∧ Reserve.cell? M (above o) = some co' ∧
      co.row < t.row ∧ co'.row < t.row := by
  obtain ⟨co, co', hco, hco', hlt, _, _, h3, _⟩ := ub_ref hTop h hne ho1
  have := h3 cμ' hcμ'
  exact ⟨co, co', hco, hco', lt_trans hlt (lt_of_le_of_lt this hμτ), lt_of_le_of_lt this hμτ⟩

/-- **The node `μ` is the node `g` of its column at the row of `o`** (when `g` exists). -/
theorem eq_of_row (hTop : Recon.Top s M t root) {o μ g : Ref} (h : Reach M o μ) (hne : o ≠ μ)
    (ho1 : 1 ≤ o.index) (hgc : g.column = μ.column) {co cg : Cell}
    (hco : Reserve.cell? M o = some co) (hcg : Reserve.cell? M g = some cg)
    (hrow : cg.row = co.row) : μ = g := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  obtain ⟨co2, co', hco2, _, hlt, ⟨cμ, hcμ⟩, h2, _, h4⟩ := ub_ref hTop h hne ho1
  obtain rfl : co2 = co := Option.some.inj (hco2.symm.trans hco)
  have hg' : Reserve.cell? M ⟨μ.column, g.index⟩ = some cg := by rw [← hgc]; exact hcg
  have i1 := h4 g.index cg hg' (by rw [hrow]; exact hlt)
  have i2 := Classification.Proofs.ChainCorr.Inner.index_le_of_row_le hV hgc.symm hcμ hcg
    (by rw [hrow]; exact h2 cμ hcμ)
  cases μ; cases g
  simp only at hgc i1 i2 ⊢
  subst hgc
  congr 1
  omega

end RefUB

/-! ## The chain of a node of `x₀` passes the root column (`x0Pass`) -/

namespace X0

open Canonical Reserve Official Descent Classification Proofs
open Geometry
open ChainCorr.Inner ChainCorr.SRX0

/-- A chain of numerical parents of a normal frame from a real node is a chain of stored
parents at some scale. -/
theorem reach_of_ppath {M : Mountain} (hF : (Frame.ofMountain M).Normal) :
    ∀ {u L : (Frame.ofMountain M).Node}, Frame.ParentPath (Frame.ofMountain M) u L →
      Frame.Real u → Reach M (Frame.ref u) (Frame.ref L) := by
  intro u L path
  induction path with
  | refl => intro _; exact Reach.refl M _
  | @cons u z L' hp rest ih =>
    intro hu
    have hO := hF.toOrdered
    have hzreal : Frame.Real z := Frame.real_of_value_pos hO (Frame.P_value hO hp).1
    have hraw : (Frame.ofMountain M).rawParent u = some z := (hF.rawParent_eq_P hu).trans hp
    refine Reach.trans ⟨_, ScaleReach.step (reserve_rawParent_of_frame hraw)
      (ControlProof.cell?_ref u) (ControlProof.cell?_ref z) le_rfl (Frame.P_column_lt hO hp)
      (ScaleReach.refl _)⟩ (ih hzreal)

/-- **`x0Pass`.** For a node `ν` of `x₀` below `τ`, the chain of stored parents of `M(s)` from
`ν` passes the highest node `q` of `c_r` at or below `row ν`. -/
theorem x0Pass {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hTop : Recon.Top s M t root)
    (ν : Ref) (cν : Cell) (hνc : ν.column = M.size - 1) (hν1 : 1 ≤ ν.index)
    (hcν : cell? M ν = some cν) (hlt : cν.row < t.row) (q : Ref)
    (hq : highestAtMost M root.column cν.row = some q) : Reach M ν q := by
  obtain ⟨νc, νi⟩ := ν
  simp only at hνc hν1
  subst hνc
  have hB := hTop.build
  have hF : (Frame.ofMountain M).Normal := build_normal_of_success hB
  have hO := hF.toOrdered
  -- the last column and its top
  have hrl := hTop.lt
  have hsz : M.size - 1 < M.size := by omega
  have htop := hTop.top
  rw [Array.getElem?_eq_getElem hsz] at htop
  simp only [Option.bind_some, Array.back?] at htop
  obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
  -- `ν` in the last column
  obtain ⟨_, hνi, hνcell⟩ := canon_cell?_some_iff.mp hcν
  have hνi' : νi < M[M.size - 1].size := hνi
  have hνT : νi + 1 < M[M.size - 1].size := by
    by_contra hn
    have hνe : νi = M[M.size - 1].size - 1 := by omega
    have h1 : M[M.size - 1][νi]? = some cν := by
      rw [Array.getElem?_eq_getElem hνi']
      exact congrArg some hνcell
    rw [hνe, htop] at h1
    have : t = cν := Option.some.inj h1
    subst this
    exact lt_irrefl _ hlt
  -- the node `y` just below `t`
  let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
  have hyl : M[M.size - 1].size - 2 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 2 < M[M.size - 1].size
    omega
  let ny : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 2, hyl⟩⟩
  have hyreal : Frame.Real ny := by show 0 < M[M.size - 1].size - 2; omega
  have hrawy0 : Reserve.rawParent M ⟨M.size - 1, M[M.size - 1].size - 2⟩ = some root := by
    unfold Reserve.rawParent
    rw [Array.getElem?_eq_getElem hsz]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [show M[M.size - 1].size - 2 + 1 = M[M.size - 1].size - 1 by omega, htop]
    simpa using hTop.left
  have hrawy : ((Frame.ofMountain M).upper ny).bind
      (fun v => ((Frame.ofMountain M).cell v).left) = some root :=
    (ControlProof.rawParent_ref ny).symm.trans hrawy0
  have hyP : ∃ nr, (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root := by
    cases hup : (Frame.ofMountain M).upper ny with
    | none => rw [hup] at hrawy; cases hrawy
    | some up =>
      rw [hup] at hrawy
      simp only [Option.bind_some] at hrawy
      obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid up root hrawy
      have hnr := Frame.lookup_spec hlk
      have hleft : ((Frame.ofMountain M).cell up).left = some (Frame.ref nr) := by
        rw [hnr]; exact hrawy
      refine ⟨nr, ?_, hnr⟩
      rw [← hF.rawParent_eq_P hyreal]
      exact Frame.rawParent_eq_of_upper_left hup hleft
  obtain ⟨nr, hPy, hnr⟩ := hyP
  let nν : (Frame.ofMountain M).Node := ⟨x0, ⟨νi, hνi'⟩⟩
  have hνref : Frame.ref nν = ⟨M.size - 1, νi⟩ := rfl
  have hνreal : Frame.Real nν := by show 0 < νi; omega
  have hcr : root.column < M.size - 1 := hrl
  have hhit : Hits (Frame.ofMountain M) nν root.column := by
    have hy : Hits (Frame.ofMountain M) ny root.column :=
      ⟨nr, .cons hPy (.refl nr), by rw [← hnr]; rfl⟩
    exact hits_down hF (M.size - 1) ny nν rfl rfl hνreal
      (by show νi ≤ M[M.size - 1].size - 2; omega) hcr hy
  obtain ⟨L, hpath, hLc⟩ := hhit
  cases hpath with
  | refl =>
    have : (M.size - 1 : Nat) = root.column := hLc
    omega
  | @cons _ x _ hPν rest =>
    -- `L` is `q`
    have hLh : (Frame.ofMountain M).height L ≤ (Frame.ofMountain M).height nν :=
      (rest.height_le hO).trans (Frame.P_height_le hO hPν)
    have hνcell' : (Frame.ofMountain M).cell nν = cν := hνcell
    have hLreal : Frame.Real L := Frame.real_of_value_pos hO
      (path_value_pos hO rest (Frame.P_value hO hPν).1)
    have hqL : q = Frame.ref L := by
      have hL' : highestAtMost M root.column cν.row = some (Frame.ref L) := by
        refine highestAtMost_of_max (cp := (Frame.ofMountain M).cell L) hLc hLreal
          (ControlProof.cell?_ref L) ?_ ?_
        · rw [← hνcell']; exact hLh
        · intro j c hjc hj0 hjrow
          obtain ⟨hc', hj', hcell⟩ := canon_cell?_some_iff.mp hjc
          let z : (Frame.ofMountain M).Node := ⟨⟨root.column, hc'⟩, ⟨j, hj'⟩⟩
          have hz : z.1 = L.1 := Fin.ext hLc.symm
          have := path_highest hF hPν rest hz (by
            show (M[root.column][j]).row ≤ ((Frame.ofMountain M).cell nν).row
            rw [hcell, hνcell']; exact hjrow)
          exact this
      rw [hL'] at hq
      exact (Option.some.inj hq).symm
    subst hqL
    exact reach_of_ppath hF (.cons hPν rest) hνreal

end X0

end OmegaY.Official.Recon.SeamPass

#print axioms OmegaY.Official.Recon.SeamPass.X0.x0Pass
#print axioms OmegaY.Official.Recon.SeamPass.ub_ref
