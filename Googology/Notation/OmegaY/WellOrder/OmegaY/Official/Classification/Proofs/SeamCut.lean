/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamCut.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamFinal

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The step from a gap copy that is not the top copy (`StepCutNT` from `CutParentNT`)

A gap copy `u` (clean copy with `b = 1`) of `m = (x, C)` that is not the top copy of `m` in its
column. Its generation chain `m → b → … → g` runs in the row `C` to the node `g = (c_r, C)` of the
root column.

* `cut_jump_lt` (rows): the step `u → u₁` of the output has a jump below the jump of the step
  `g → g₁` of `M(s)`. The gap copies of `m` lie strictly between `C` and the row of the node
  `g⁺` above `g` (the copies keep their place among the root rows, `SRCmp.emitsT_cmp`), and
  `row g⁺ = bump(C, jump(g, g₁))`; the jump law of the output gives `jump(u, u₁)`.
* `CutParentNT` (**open**, structural): the stored parent `u₁` of `u` is in the boundary column
  `B_i` (and then the leg of `m` is `c_r`), or it is a gap copy of the next generation `b` of `m`
  that is not the top copy of `b`.
* `stepCutNT_of_parent : CutParentNT → StepCutNT`: by induction along the walk, the chain of `u`
  reaches the step `g → g₁`; at the boundary column the origin `ν` of `u₁` looks up `g`
  (`hAM(c_r, row ν) = g`, the root rows again), and `SRX0.x0Reach` gives the step of `g` from `ν`.
  On the side of `M(s)`, every step from a node of the generation chain passes `g → g₁`
  (`cleanParentReachD'`).
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs.ChainCorr.Inner (GenStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt)
open CrossUpperSim CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index)

/-- **(open)** The stored parent of a gap copy that is not the top copy. -/
def CutParentNT : Prop :=
  ∀ s n R M t root i x es j, NodeData s n R M t root i x es j → 0 < i →
    ∀ hj : j < es.length, cutOrigin es[j].2 = true → ¬ IsTopAt es j →
    ∀ u1, Reserve.rawParent R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some u1 →
      (u1.column = root.column + (M.size - 1 - root.column) * i ∧
        ∃ b, GenStep M root.column es[j].2.src b ∧ b.column = root.column) ∨
      ∃ x' es' j', NodeData s n R M t root i x' es' j' ∧
        u1 = ⟨x' + (M.size - 1 - root.column) * i, j' + 1⟩ ∧
        ∃ hj' : j' < es'.length, cutOrigin es'[j'].2 = true ∧ ¬ IsTopAt es' j' ∧
          GenStep M root.column es[j].2.src es'[j'].2.src

/-! ## Rows -/

/-- Rows in `[C, bump C e)`: a bump between two of them has an exponent below `e`. -/
theorem exp_lt_of_between {C a b : Row} {e f : Nat} (hCa : C ≤ a) (hab : b = Row.bump a f)
    (hb : b < Row.bump C e) : f < e := by
  have hCb : C ≤ b := le_trans hCa (by rw [hab]; exact (Row.lt_bump _ _).le)
  have h1 : Row.jump C a ≤ e := Row.jump_le_of_lt_bump hCa (lt_of_le_of_lt (by
    rw [hab]; exact (Row.lt_bump _ _).le) hb)
  have h2 : Row.jump C b ≤ e := Row.jump_le_of_lt_bump hCb hb
  have h3 : Row.jump a b ≤ max (Row.jump a C) (Row.jump C b) := Row.jump_triangle a C b
  rw [hab, Row.jump_bump, Row.jump_comm a C] at h3
  have h4 := le_trans h3 (max_le h1 (by rw [← hab]; exact h2))
  omega

/-- The end of a generation chain in the root column is unique. -/
theorem genEnd_eq {M : Mountain} (hV : MountainValid M) {cr : Nat} {m g g' : Ref}
    (hg : Relation.ReflTransGen (GenStep M cr) m g) (hgc : g.column = cr)
    (hg' : Relation.ReflTransGen (GenStep M cr) m g') (hgc' : g'.column = cr) : g' = g := by
  have hU : Relator.RightUnique (GenStep M cr) := fun _ _ _ h h' =>
    Classification.Proofs.ChainCorr.Inner.GenStep.unique hV h h'
  rcases Relation.ReflTransGen.total_of_right_unique hU hg hg' with h | h
  · exact Classification.Proofs.ChainCorr.NonTop.genChain_stop (le_of_eq hgc) h
  · exact (Classification.Proofs.ChainCorr.NonTop.genChain_stop (le_of_eq hgc') h).symm

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- The cell at index `k + 1` of a new column. -/
theorem colCell {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {k : Nat} (hk : k < (lo ++ us).length) :
    ∃ c, Reserve.cell? R ⟨X, k + 1⟩ = some c ∧ c.row = stored ((lo ++ us)[k]).1.row ∧
      R[X]?.bind (·[k + 1]?) = some c := by
  have hk1 : k + 1 < (R[X]'hD.XR).size := by rw [hD.size]; omega
  obtain ⟨_, hrow, _⟩ := hD.node hk1 (by omega)
  refine ⟨(R[X]'hD.XR)[k + 1], ?_, by rw [hrow]; simp, ?_⟩ <;>
  · simp only [Reserve.cell?, Array.getElem?_eq_getElem hD.XR, Option.bind_eq_bind,
      Option.bind_some]
    exact Array.getElem?_eq_getElem hk1

/-- **The jump of the step from a gap copy that is not the top copy** is below the jump of the
step `g → g₁` of the end of the generation chain. -/
theorem cut_jump_lt {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {j j' : Nat}
    (hj' : j' < (lo ++ us).length) (hjj : j < j') (hcut : cutOrigin ((lo ++ us)[j]'(by omega)).2 = true)
    (hsrc : ((lo ++ us)[j']).2.src = ((lo ++ us)[j]'(by omega)).2.src)
    {g g1 : Ref} {cg cg1 cm : Cell} (hgc : g.column = root.column) (hg1 : 1 ≤ g.index)
    (hcg : Reserve.cell? M g = some cg) (hcm : Reserve.cell? M ((lo ++ us)[j]'(by omega)).2.src = some cm)
    (hrow : cg.row = cm.row) (hraw : Reserve.rawParent M g = some g1)
    (hcg1 : Reserve.cell? M g1 = some cg1)
    {u1 : Ref} {cu cu1 : Cell} (hru : Reserve.rawParent R ⟨X, j + 1⟩ = some u1)
    (hcu : Reserve.cell? R ⟨X, j + 1⟩ = some cu) (hcu1 : Reserve.cell? R u1 = some cu1) :
    Row.jump cu.row cu1.row < Row.jump cg.row cg1.row := by
  have hTop := hD.top
  have hrun := hD.run
  have hVM := build_valid_of_success hTop.build
  have hjl : j < (lo ++ us).length := by omega
  have hj1 : j + 1 < (lo ++ us).length := by omega
  -- the cells of `u`, `u⁺`, `T`
  obtain ⟨c0, hc0, hc0row, _⟩ := colCell hD hjl
  have e0 : c0 = cu := Option.some.inj (hc0.symm.trans hcu)
  rw [e0] at hc0row
  obtain ⟨c1, hc1, hc1row, _⟩ := colCell hD hj1
  obtain ⟨cT, hcT, hcTrow, _⟩ := colCell hD hj'
  -- the stored parent of `u` is the left end of `u⁺`
  obtain ⟨cu', hcu', hleft⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hru
  have hup : Classification.Proofs.ChainCorr.Inner.up (⟨X, j + 1⟩ : Ref) = ⟨X, j + 1 + 1⟩ := rfl
  rw [hup] at hcu'
  have e1 : cu' = c1 := Option.some.inj (hcu'.symm.trans hc1)
  rw [e1] at hleft
  -- the jump law of the output
  have hXR := hD.XR
  have hl' : R[X][j + 1]? = some cu := by
    have := hcu; simp only [Reserve.cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind,
      Option.bind_some] at this; exact this
  have hu' : R[X][j + 1 + 1]? = some c1 := by
    have := hc1; simp only [Reserve.cell?, Array.getElem?_eq_getElem hXR, Option.bind_eq_bind,
      Option.bind_some] at this; exact this
  have hx : s.length - 1 ≤ X := by
    have hMs := Canonical.build_size hTop.build
    have := hD.Xeq
    have hxg := hD.xgt
    have hxl := hD.xle
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have hx0 : x = M.size - 1 := by simpa [blockColumns] using hD.xb
      omega
    · have := Nat.le_mul_of_pos_right (M.size - 1 - root.column) h0
      omega
  obtain ⟨e, he⟩ := RowLaw.bumpChainHolds s n R hrun X hXR hx (j + 1) cu c1 hl' hu' (by omega)
  have hcell : cellAt R u1 = .ok cu1 := by
    rw [cellAt_ok_iff]
    unfold Reserve.cell? at hcu1
    cases hcol : R[u1.column]? with
    | none => rw [hcol] at hcu1; cases hcu1
    | some col =>
      rw [hcol] at hcu1
      exact ⟨col, rfl, by simpa using hcu1⟩
  have hjl' := LRC.jumpLawHolds s n R hrun X hXR hx (j + 1) _ _ _ _ e hl' hu' (by omega) hleft
    hcell he
  rw [hjl']
  -- the node above `g`
  obtain ⟨cgp, hcgp, hgpl⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hraw
  obtain ⟨q, cq, hql, hcq, hgprow, _, _⟩ :=
    Classification.Proofs.ChainCorr.Inner.Clean.upper_row hTop.build hcg hg1 hcgp
  rw [hgpl] at hql
  obtain rfl := Option.some.inj hql
  obtain rfl : cq = cg1 := Option.some.inj (hcq.symm.trans hcg1)
  have hcg11 : (1 : Row) ≤ cg.row := Classification.one_le_row hVM hcg hg1
  have hgpgt : cg.row < cgp.row := by rw [hgprow]; exact Row.lt_B _ _
  -- `u` is above `C`
  have hRg := rootRow_of_cell (root := root) hcg hg1 hgc
  have hECj := ecmp_of_colData hD _ (List.getElem_mem hjl) cm hcm
  have hlow : cg.row < cu.row := by
    have h1 := ((hECj _ hRg).2 hcut).1 (by rw [hrow])
    rw [hc0row]
    have := Recon.stored_strictMono h1
    rwa [Classification.stored_official hcg11] at this
  -- `T` is below `g⁺`
  have hgp1 : 1 ≤ (Classification.Proofs.ChainCorr.Inner.up g).index := by
    simp [Classification.Proofs.ChainCorr.Inner.up]
  have hRgp := rootRow_of_cell (root := root) hcgp hgp1 (by
    simp [Classification.Proofs.ChainCorr.Inner.up, hgc])
  have hcmT : Reserve.cell? M ((lo ++ us)[j']).2.src = some cm := by rw [hsrc]; exact hcm
  have hECT := ecmp_of_colData hD _ (List.getElem_mem hj') cm hcmT
  have hσ : official cm.row < official cgp.row := by
    rw [← hrow]; exact official_strictMono hcg11 hgpgt
  have hTlt : ((lo ++ us)[j']).1.row < official cgp.row := by
    cases hcT' : cutOrigin ((lo ++ us)[j']).2
    · exact ((hECT _ hRgp).1 hcT').2.2 hσ
    · exact ((hECT _ hRgp).2 hcT').2 hσ
  have hcgp1 : (1 : Row) ≤ cgp.row := le_trans hcg11 hgpgt.le
  have hcTlt : cT.row < cgp.row := by
    rw [hcTrow]
    have := Recon.stored_strictMono hTlt
    rwa [Classification.stored_official hcgp1] at this
  -- `u⁺` is at or below `T`
  have h1T : c1.row ≤ cT.row := by
    rw [hc1row, hcTrow]
    apply Classification.Proofs.ChainCorr.stored_le_iff.mpr
    rcases Nat.lt_or_eq_of_le (show j + 1 ≤ j' by omega) with hlt | heq
    · have := List.pairwise_iff_getElem.mp hD.sorted (j + 1) j'
        (by simp only [List.length_map]; exact hj1) (by simp only [List.length_map]; exact hj') hlt
      simp only [List.getElem_map] at this
      exact this.le
    · subst heq; exact le_rfl
  exact exp_lt_of_between hlow.le he (by
    have := lt_of_le_of_lt h1T hcTlt
    rw [hgprow] at this
    exact this)

/-- **The boundary lookup at a gap copy.** If the stored parent `u₁` of a gap copy `u` of `m`
(not the top copy) is in the boundary column `B_i`, the origin `ν` of `u₁` is a lower node of
`x₀` with `hAM(c_r, row ν) = g`, for the node `g` of the root column at the row of `m`. -/
theorem cut_bnd_lookup (E : CrossUpperSim.Env s n R M t root) {i : Nat} (hi0 : 0 < i)
    (hin : i ≤ n) {X x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {j j' : Nat}
    (hj' : j' < (lo ++ us).length) (hjj : j < j')
    (hcut : cutOrigin ((lo ++ us)[j]'(by omega)).2 = true)
    (hsrc : ((lo ++ us)[j']).2.src = ((lo ++ us)[j]'(by omega)).2.src)
    {g : Ref} {cg cm : Cell} (hgc : g.column = root.column) (hg1 : 1 ≤ g.index)
    (hcg : Reserve.cell? M g = some cg)
    (hcm : Reserve.cell? M ((lo ++ us)[j]'(by omega)).2.src = some cm) (hrow : cg.row = cm.row)
    {u1 : Ref} (hru : Reserve.rawParent R ⟨X, j + 1⟩ = some u1)
    (hu1c : u1.column = root.column + (M.size - 1 - root.column) * i) :
    ∃ esB k, ∃ hk : k < esB.length,
      blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) = .ok esB ∧
      u1 = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ ∧
      ∃ cν, Reserve.cell? M esB[k].2.src = some cν ∧ esB[k].2.src.column = M.size - 1 ∧
        1 ≤ esB[k].2.src.index ∧ cν.row < t.row ∧
        Reserve.highestAtMost M root.column cν.row = some g := by
  have hTop := E.top
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR E.run
  have hF := E.FR
  have hBeq := Classification.Proofs.ChainCorr.boundary_eq hcr hi0
  have hjl : j < (lo ++ us).length := by omega
  have hj1 : j + 1 < (lo ++ us).length := by omega
  obtain ⟨c0, hc0, hc0row, _⟩ := colCell hD hjl
  obtain ⟨c1, hc1, hc1row, _⟩ := colCell hD hj1
  -- frame nodes of `u`, `u⁺`, `u₁`
  obtain ⟨UN, hUN, hUNc⟩ := LowerChainRecon.node_of_cell hc0
  obtain ⟨VN, hVN, hVNc⟩ := LowerChainRecon.node_of_cell hc1
  obtain ⟨cu', hcu', hleft⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hru
  have hup : Classification.Proofs.ChainCorr.Inner.up (⟨X, j + 1⟩ : Ref) = ⟨X, j + 1 + 1⟩ := rfl
  rw [hup] at hcu'
  have e1 : cu' = c1 := Option.some.inj (hcu'.symm.trans hc1)
  rw [e1] at hleft
  obtain ⟨cq, hcq, _⟩ := Classification.Proofs.ChainCorr.Inner.left_cell hVR hc1 hleft
  obtain ⟨AN, hAN, hANc⟩ := LowerChainRecon.node_of_cell hcq
  have hV1 : VN.1 = UN.1 := Fin.ext (by
    have h1 := congrArg Ref.column hVN; have h2 := congrArg Ref.column hUN
    simp [Frame.ref] at h1 h2; omega)
  have huu : (Frame.ofMountain R).upper UN = some VN :=
    Classification.ControlProof.upper_eq_of_index hV1.symm (by
      have h1 := congrArg Ref.index hVN; have h2 := congrArg Ref.index hUN
      simp [Frame.ref] at h1 h2; omega)
  have hUr : Real UN := by
    show 0 < UN.2.val
    have := congrArg Ref.index hUN; simp [Frame.ref] at this; omega
  have hAraw : (Frame.ofMountain R).rawParent UN = some AN :=
    Geometry.Frame.rawParent_eq_of_upper_left huu (by rw [hVNc, hAN]; exact hleft)
  have hAH := CrossUpperSim.highestIn_of_hb (E.HB UN hUr) huu hAraw
  have hVh : (Frame.ofMountain R).height VN = stored ((lo ++ us)[j + 1]).1.row := by
    change ((Frame.ofMountain R).cell VN).row = _; rw [hVNc, hc1row]
  have hANcol : AN.1.val = M.size - 1 + (M.size - 1 - root.column) * (i - 1) := by
    have := congrArg Ref.column hAN; simp [Frame.ref] at this; omega
  -- the rows
  have hcg11 : (1 : Row) ≤ cg.row := Classification.one_le_row hVM hcg hg1
  have hRR := rootRow_of_cell (root := root) hcg hg1 hgc
  have hECu := ecmp_of_colData hD _ (List.getElem_mem hjl) cm hcm
  have hcmT : Reserve.cell? M ((lo ++ us)[j']).2.src = some cm := by rw [hsrc]; exact hcm
  have hECT := ecmp_le (ecmp_of_colData hD _ (List.getElem_mem hj')) hcmT
  have hC : official cg.row = official cm.row := by rw [hrow]
  have hsorted : ∀ a b (ha : a < (lo ++ us).length) (hb : b < (lo ++ us).length), a < b →
      ((lo ++ us)[a]).1.row < ((lo ++ us)[b]).1.row := by
    intro a b ha hb hab
    have := List.pairwise_iff_getElem.mp hD.sorted a b (by simp only [List.length_map]; exact ha)
      (by simp only [List.length_map]; exact hb) hab
    simpa only [List.getElem_map] using this
  have hρuT : ((lo ++ us)[j + 1]).1.row ≤ ((lo ++ us)[j']).1.row := by
    rcases Nat.lt_or_eq_of_le (show j + 1 ≤ j' by omega) with hlt | heq
    · exact (hsorted _ _ hj1 hj' hlt).le
    · subst heq; exact le_rfl
  -- `m` is below `τ`, so `T` is a lower emit
  have hCτ : official cm.row < official t.row := by
    have hup : ((lo ++ us)[j]'hjl).2.isUpper = false := by
      cases h : ((lo ++ us)[j]'hjl).2 with
      | clean r b => rfl
      | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
      | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hD.emitsT hjl hup
    have h2 : Reserve.cell? M ((lo ++ us)[j]'hjl).2.src = some c' := by simpa [ctxAt] using hc'
    have : c' = cm := Option.some.inj (h2.symm.trans hcm)
    rw [← this]; exact hlt'
  have hTlo : j' < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[j'] ∈ us := by
      rw [List.getElem_append_right (by omega)]; exact List.getElem_mem _
    obtain ⟨k2, c2, _, hc2, hup2, _, hτ2, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
    have hs2 : ((lo ++ us)[j']).2.src = ⟨upperColumn (ctxAt M R x i root.column
        (M.size - 1 - root.column) (M.size - 1) X), k2⟩ := by rw [hup2]; rfl
    have hc2' : Reserve.cell? M ((lo ++ us)[j']).2.src = some c2 := by
      rw [hs2]; simpa [ctxAt] using hc2
    have : c2 = cm := Option.some.inj (hc2'.symm.trans hcmT)
    rw [this] at hτ2
    exact absurd (lt_of_lt_of_le hCτ hτ2) (lt_irrefl _)
  have hρT : ((lo ++ us)[j']).1.row < official t.row := hD.lo_lt _ (by
    rw [List.getElem_append_left hTlo]; exact List.getElem_mem _)
  have hρu : official cm.row < ((lo ++ us)[j]'hjl).1.row :=
    ((hECu _ (by rw [← hC]; exact hRR)).2 hcut).1 le_rfl
  have hρu1 : ((lo ++ us)[j]'hjl).1.row < ((lo ++ us)[j + 1]).1.row :=
    hsorted _ _ hjl hj1 (by omega)
  -- boundary nodes below `u⁺` are at or below `u₁`
  have hbnd : ∀ p ∈ realNodes M root.column, official p.2.row ≤ official cm.row →
      ∃ G : (Frame.ofMountain R).Node, G.1 = AN.1 ∧ Real G ∧
        official ((Frame.ofMountain R).height G) = official p.2.row ∧ G.2.val ≤ AN.2.val := by
    intro p hp hpC
    obtain ⟨G, hGc, hGr, hGrow⟩ := bnd_node E hi0 hin hp (lt_of_le_of_lt hpC hCτ)
    have hGA : G.1 = AN.1 := Fin.ext (by rw [hGc, hANcol, hBeq])
    refine ⟨G, hGA, hGr, hGrow, hAH.2 G hGA ?_⟩
    rw [hVh]
    apply row_lt_of_official (JumpLaw.one_le_stored _)
    rw [JumpLaw.official_stored, hGrow]
    exact lt_of_le_of_lt hpC (lt_trans hρu hρu1)
  have hgmem : (g, cg) ∈ realNodes M root.column := by
    have := Proofs.CopyShape.mem_realNodes_of_cell' hcg hg1
    rwa [hgc] at this
  obtain ⟨G0, _, hG0r, _, hG0A⟩ := hbnd _ hgmem (le_of_eq hC)
  have hAr : Real AN := le_trans hG0r hG0A
  -- the emit of `u₁`
  obtain ⟨loB, usB, hDB⟩ := colData_x0 E (m := i - 1) (by omega)
  obtain ⟨hAk, hArow⟩ := node_row hDB hANcol hAr
  have hA1 : ((loB ++ usB)[AN.2.val - 1]).1.row < ((lo ++ us)[j + 1]).1.row := by
    have := hAH.1
    rw [hArow, hVh] at this
    exact LowerPB.lt_of_stored_lt this
  have hAlo : AN.2.val - 1 < loB.length := lower_of_row hDB hAk
    (lt_of_lt_of_le hA1 (le_trans hρuT hρT.le))
  have hfe : (loB ++ usB)[AN.2.val - 1] = loB[AN.2.val - 1] := List.getElem_append_left hAlo
  have hfmem : loB[AN.2.val - 1] ∈ loB := List.getElem_mem _
  obtain ⟨⟨_, _, _, _, _⟩, hfup⟩ := LowerPB.lowerT_good hDB.hlo _ hfmem
  obtain ⟨km, cν, hfsrc, hkm1, hcν, _⟩ := LowerPB.lowerT_src hDB.hlo hfmem
  have hfsrc' : ((loB ++ usB)[AN.2.val - 1]).2.src = ⟨M.size - 1, km⟩ := by
    rw [hfe, hfsrc]; rfl
  have hcν' : Reserve.cell? M ((loB ++ usB)[AN.2.val - 1]).2.src = some cν := by
    rw [hfsrc']; exact hcν
  have hcν1 : (1 : Row) ≤ cν.row := LowerPB.cell_row_one_le hVM hcν hkm1
  have hντ : official cν.row < official t.row := by
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hDB.emitsT hAk
      (by rw [hfe]; exact hfup)
    have : c' = cν := by
      have h2 : Reserve.cell? M ((loB ++ usB)[AN.2.val - 1]).2.src = some c' := by
        simpa [ctxAt] using hc'
      exact Option.some.inj (h2.symm.trans hcν')
    rw [← this]; exact hlt'
  have hP := ecmp_le (ecmp_of_colData hDB _ (List.getElem_mem hAk)) hcν'
  -- the root rows at or below `row ν` are those at or below `C`
  have hkey : ∀ r, Classification.Proofs.ChainCorr.SRCmp.RootRow M root.column r →
      (r ≤ official cν.row ↔ r ≤ official cm.row) := by
    intro r hr
    constructor
    · intro h
      have h1 := (hP r hr).1 h
      by_contra hn
      have h2 := (hECT r hr).2 (lt_of_not_ge hn)
      exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le hA1 (le_trans hρuT h2.le)))
        (lt_irrefl _)
    · intro h
      obtain ⟨p, hp, rfl⟩ := hr
      obtain ⟨G, hGA, hGr, hGrow, hGle⟩ := hbnd p hp h
      have h1 : official p.2.row ≤ ((loB ++ usB)[AN.2.val - 1]).1.row := by
        rw [← hGrow, ← JumpLaw.official_stored ((loB ++ usB)[AN.2.val - 1]).1.row, ← hArow]
        exact official_mono (one_le_height hF hGr) (height_le_of_index hF hGA hGle)
      by_contra hn
      have h2 := (hP _ ⟨p, hp, rfl⟩).2 (lt_of_not_ge hn)
      exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
  have hAeq : u1 = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), AN.2.val - 1 + 1⟩ := by
    have hAr' : 0 < AN.2.val := hAr
    rw [← hAN]; simp only [Frame.ref, hANcol]; congr 1; omega
  refine ⟨loB ++ usB, AN.2.val - 1, hAk, ?_, hAeq, cν, hcν', ?_, ?_, ?_, ?_⟩
  · show emitsT _ _ = _
    exact hDB.emitsT
  · rw [hfsrc']
  · rw [hfsrc']; exact hkm1
  · exact row_lt_of_official hTop.row_one_le hντ
  · refine Classification.Proofs.ChainCorr.Inner.highestAtMost_of_max hgc (by omega) hcg ?_ ?_
    · exact le_of_official_le hcν1 ((hkey _ hRR).mpr (le_of_eq hC))
    · intro jj cc hcc hjj hccle
      have hcc1 : (1 : Row) ≤ cc.row := LowerPB.cell_row_one_le hVM hcc hjj
      have hRc := rootRow_of_cell (root := root) hcc hjj rfl
      have hle := (hkey _ hRc).mp (official_mono hcc1 hccle)
      have hle' : cc.row ≤ cg.row := le_of_official_le hcg11 (by rw [hC]; exact hle)
      have hself := Classification.Proofs.ChainCorr.Inner.CleanRoot.hAM_self hVM (b := g)
        (by omega) hcg
      exact Classification.Proofs.ChainCorr.SRParts.hAM_max hself (q := ⟨root.column, jj⟩)
        (by simp [hgc]) hjj hcc hle'

/-- **The walk from a gap copy that is not the top copy**: the generation chain of its origin
ends at a node `g` of the root column; the output chain of the copy reaches every step `g → g₁`
of `M(s)`; and every chain of `M(s)` from a node of the generation chain right of `c_r` that
reaches the columns left of `c_r` passes a step `g → g₁`. -/
theorem cutWalk (hCP : CutParentNT) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root) :
    ∀ X i x es j, X = x + (M.size - 1 - root.column) * i → NodeData s n R M t root i x es j →
      0 < i → ∀ hj : j < es.length, cutOrigin es[j].2 = true → ¬ IsTopAt es j →
      (∀ Q' o', Q'.column < X → OrigAt M R n root.column (M.size - 1) (official t.row) Q' o' →
        ChainOK R M root.column Q' o') →
      ∃ g, Relation.ReflTransGen (GenStep M root.column) es[j].2.src g ∧
        g.column = root.column ∧
        (∀ k g1, MStep M k g g1 → ScaleReach R k ⟨X, j + 1⟩ g1) ∧
        (∀ k (μ m' : Ref), Relation.ReflTransGen (GenStep M root.column) es[j].2.src m' →
          root.column < m'.column → μ.column < root.column → ScaleReach M k m' μ →
          ∃ g1, MStep M k g g1 ∧ ScaleReach M k g1 μ) ∧
        (∀ m', Relation.ReflTransGen (GenStep M root.column) es[j].2.src m' →
          root.column ≤ m'.column) := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  intro i x es j hX hD hi0 hj hcut hnt IH
  subst hX
  have hin := hD.le_n hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hU : Relator.RightUnique (GenStep M root.column) := fun _ _ _ h h' =>
    Classification.Proofs.ChainCorr.Inner.GenStep.unique hVM h h'
  obtain ⟨E, lo, us, hDc, hee⟩ := colData_of_node hD
  subst hee
  have hD0 := hD
  obtain ⟨_, _, hx, hes, ⟨cu, hcu⟩, _⟩ := hD0
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  -- the top copy `T` above `u`
  have hnt' := hnt
  unfold IsTopAt at hnt'
  push Not at hnt'
  obtain ⟨j', hj', _, hjj, hsrcT⟩ := hnt'
  -- the source `m`, its cell and column
  obtain ⟨hsc, hs1, cm, hcm, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
  have hup : ((lo ++ us)[j]).2.isUpper = false := by
    cases h : ((lo ++ us)[j]).2 with
    | clean r b => rfl
    | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
    | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
  rw [hup] at hsc
  have hmc : ((lo ++ us)[j]).2.src.column = x := by simpa [ctxAt] using hsc
  -- the copy
  have hva : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i ⟨x + (M.size - 1 - root.column) * i, j + 1⟩
      (.clean ((lo ++ us)[j]).2.src true) := by
    refine ⟨x, lo ++ us, j, hxg, hxl, hx, rfl, rfl, hes, hj, ?_⟩
    cases h : ((lo ++ us)[j]).2 with
    | clean r b =>
        rw [h] at hcut
        cases b
        · simp [cutOrigin] at hcut
        · simp [h, Origin.src]
    | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
    | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
  -- the stored parent of `u`
  have hj1 : j + 1 < (lo ++ us).length := by omega
  have hk2 : j + 1 + 1 < (R[x + (M.size - 1 - root.column) * i]'hDc.XR).size := by
    rw [hDc.size]; omega
  obtain ⟨_, _, u1, hleft, _⟩ := hDc.node hk2 (by omega)
  obtain ⟨c1, hc1, _, _⟩ := colCell hDc hj1
  have hc1' : (R[x + (M.size - 1 - root.column) * i]'hDc.XR)[j + 1 + 1] = c1 := by
    have h2 : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1 + 1⟩ =
        some ((R[x + (M.size - 1 - root.column) * i]'hDc.XR)[j + 1 + 1]) := by
      simp only [Reserve.cell?, Array.getElem?_eq_getElem hDc.XR, Option.bind_eq_bind,
        Option.bind_some]
      exact Array.getElem?_eq_getElem hk2
    exact Option.some.inj (h2.symm.trans hc1)
  rw [hc1'] at hleft
  have hru : Reserve.rawParent R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some u1 :=
    Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mpr ⟨c1, hc1, hleft⟩
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  obtain ⟨_, ⟨cu1, hcu1⟩, hu1lt⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_cells hVR hru
  -- the M-side: the first step from `m` passes `g`
  have hMside : ∀ g, Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src g →
      g.column = root.column →
      (∀ m', Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src m' →
        root.column ≤ m'.column) →
      (∀ k (μ m' : Ref), Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src m' →
        m' ≠ ((lo ++ us)[j]).2.src → root.column < m'.column → μ.column < root.column →
        ScaleReach M k m' μ → ∃ g1, MStep M k g g1 ∧ ScaleReach M k g1 μ) →
      ∀ k (μ : Ref), μ.column < root.column → ScaleReach M k ((lo ++ us)[j]).2.src μ →
        ∃ g1, MStep M k g g1 ∧ ScaleReach M k g1 μ := by
    intro g hmg hgc hcolge hlater k μ hμ hr
    have hne : ((lo ++ us)[j]).2.src ≠ μ := by intro h; rw [← h] at hμ; omega
    obtain ⟨m'', hst, hrest⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
    rcases Classification.Proofs.ChainCorr.NonTop.SeamD.cleanParentReachD' hTop hva hst with
      hA | ⟨g', g1, hmg', hg'c, hgg1, hg1m⟩
    · rcases Nat.lt_or_ge root.column m''.column with hlt | hge
      · exact hlater k μ m'' hA.to_reflTransGen (by
          intro h; rw [h] at hA
          exact absurd (genChain_col_lt hVM hA) (lt_irrefl _)) hlt hμ hrest
      · have hm''c : m''.column = root.column :=
          le_antisymm hge (hcolge m'' hA.to_reflTransGen)
        have hm''g := genEnd_eq hVM hmg hgc hA.to_reflTransGen hm''c
        rw [hm''g] at hrest
        have hne' : g ≠ μ := by intro h; rw [← h] at hμ; omega
        obtain ⟨g1, hgg1, hg1μ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hrest hne'
        exact ⟨g1, hgg1, hg1μ⟩
    · have hg'g := genEnd_eq hVM hmg hgc hmg'.to_reflTransGen hg'c
      rw [hg'g] at hgg1
      exact ⟨g1, hgg1, Classification.Proofs.ChainCorr.ScaleReach.trans hg1m hrest⟩
  have hmx : root.column < ((lo ++ us)[j]).2.src.column := by rw [hmc]; exact hxg
  rcases hCP s n R M t root i x (lo ++ us) j hD hi0 hj hcut hnt u1 hru with
    ⟨hu1c, b, hmb, hbc⟩ | ⟨x', es', j', hD', hu1eq, hj'', hcut', hnt', hmb⟩
  · -- the stored parent is in the boundary column: `g = b`
    have hmb' := hmb
    obtain ⟨_, hb1, ca, cb, l, hca, hl, hbl, hcb, hbrow⟩ := hmb'
    have hafter : ∀ m', Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src m' →
        m' ≠ ((lo ++ us)[j]).2.src → m' = b := by
      intro m' h hne
      rcases Relation.ReflTransGen.cases_head h with h' | ⟨b', hmb'', hb'm'⟩
      · exact absurd h'.symm hne
      · have e := hU hmb'' hmb
        rw [e] at hb'm'
        exact Classification.Proofs.ChainCorr.NonTop.genChain_stop (le_of_eq hbc) hb'm'
    have hcolge : ∀ m', Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src m' →
        root.column ≤ m'.column := by
      intro m' h
      by_cases hne : m' = ((lo ++ us)[j]).2.src
      · rw [hne]; exact hmx.le
      · rw [hafter m' h hne, hbc]
    refine ⟨b, Relation.ReflTransGen.single hmb, hbc, ?_, ?_, hcolge⟩
    · intro k g1 hgg1
      obtain ⟨hraw, cb', cg1, hcb', hcg1, hjk, hglt⟩ := hgg1
      have e : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
      rw [e] at hjk
      have hlt := cut_jump_lt hDc hj' hjj hcut hsrcT hbc hb1 hcb hca hbrow hraw hcg1 hru hcu hcu1
      obtain ⟨esB, k0, hk0, hesB, hu1eqB, cν, hcν, hνc, hν1, hνt, hpa⟩ :=
        cut_bnd_lookup E hi0 hin hDc hj' hjj hcut hsrcT hbc hb1 hcb hca hbrow hru hu1c
      have hνg1 := Classification.Proofs.ChainCorr.SRX0.x0Reach s M t root hTop _ cν hνc hν1 hcν
        hνt b hpa k g1 ⟨hraw, cb, cg1, hcb, hcg1, hjk, hglt⟩
      have hO : OrigAt M R n root.column (M.size - 1) (official t.row) u1 esB[k0].2.src := by
        refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hu1eqB],
          by rw [hu1eqB], ?_, ⟨cu1, hcu1⟩, hk0, rfl⟩
        rw [hu1eqB]
        unfold blockEmits at hesB
        exact hesB
      have hg1c : g1.column < root.column := by rw [← hbc]; exact hglt
      have hR := IH u1 _ hu1lt hO k g1 hg1c hνg1
      exact ScaleReach.step hru hcu hcu1 (le_trans hlt.le hjk) hu1lt hR
    · intro k μ m' hmm' hcrm hμ hr'
      by_cases hne : m' = ((lo ++ us)[j]).2.src
      · rw [hne] at hr'
        refine hMside b (Relation.ReflTransGen.single hmb) hbc hcolge ?_ k μ hμ hr'
        intro k' μ' m'' h hne' hcr'' _ _
        have := hafter m'' h hne'
        rw [this] at hcr''
        omega
      · have := hafter m' hmm' hne
        rw [this] at hcrm
        omega
  · -- the stored parent is a gap copy of the next generation `b`
    have hlt' : x' + (M.size - 1 - root.column) * i < x + (M.size - 1 - root.column) * i := by
      have := hu1lt; rw [hu1eq] at this; exact this
    obtain ⟨g, hbg, hgc, ha', hb', hcolb⟩ := ih _ hlt' i x' es' j' rfl hD' hi0 hj'' hcut' hnt'
      (fun Q' o' h hO => IH Q' o' (lt_trans h hlt') hO)
    have hmg : Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src g :=
      Relation.ReflTransGen.head hmb hbg
    have hmgT : Relation.TransGen (GenStep M root.column) ((lo ++ us)[j]).2.src g :=
      Relation.TransGen.head' hmb hbg
    have hafter : ∀ m', Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src m' →
        m' ≠ ((lo ++ us)[j]).2.src →
        Relation.ReflTransGen (GenStep M root.column) es'[j'].2.src m' := by
      intro m' h hne
      rcases Relation.ReflTransGen.cases_head h with h' | ⟨b', hmb'', hb'm'⟩
      · exact absurd h'.symm hne
      · have e := hU hmb'' hmb
        rw [e] at hb'm'
        exact hb'm'
    have hcolge : ∀ m', Relation.ReflTransGen (GenStep M root.column) ((lo ++ us)[j]).2.src m' →
        root.column ≤ m'.column := by
      intro m' h
      by_cases hne : m' = ((lo ++ us)[j]).2.src
      · rw [hne]; exact hmx.le
      · exact hcolb m' (hafter m' h hne)
    refine ⟨g, hmg, hgc, ?_, ?_, hcolge⟩
    · intro k g1 hgg1
      obtain ⟨cg, hcg, hcgrow⟩ := Classification.Proofs.ChainCorr.Inner.Clean.chain_row hmgT cm hcm
      have hg1 : 1 ≤ g.index := by
        cases hmgT with
        | single h => exact h.2.1
        | tail _ h => exact h.2.1
      obtain ⟨hraw, cg', cg1, hcg', hcg1, hjk, hglt⟩ := hgg1
      have e : cg' = cg := Option.some.inj (hcg'.symm.trans hcg)
      rw [e] at hjk
      have hlt := cut_jump_lt hDc hj' hjj hcut hsrcT hgc hg1 hcg hcm hcgrow hraw hcg1 hru hcu hcu1
      have hR := ha' k g1 ⟨hraw, cg, cg1, hcg, hcg1, hjk, hglt⟩
      rw [← hu1eq] at hR
      exact ScaleReach.step hru hcu hcu1 (le_trans hlt.le hjk) hu1lt hR
    · intro k μ m' hmm' hcrm hμ hr'
      by_cases hne : m' = ((lo ++ us)[j]).2.src
      · rw [hne] at hr'
        refine hMside g hmg hgc hcolge ?_ k μ hμ hr'
        intro k' μ' m'' h hne' hcr'' hμ' hr''
        exact hb' k' μ' m'' (hafter m'' h hne') hcr'' hμ' hr''
      · exact hb' k μ m' (hafter m' hmm' hne) hcrm hμ hr'

end Run

/-- **`StepCutNT` from `CutParentNT`.** -/
theorem stepCutNT_of_parent (hCP : CutParentNT) : StepCutNT := by
  intro s n R M t root i x es j hD hi0 hj hcut hnt IH k μ hμ hr
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD0
  have hcr := hTop.lt
  obtain ⟨hxg, _⟩ := mem_blockColumns hcr hx
  obtain ⟨g, _, hgc, ha, hb, _⟩ := cutWalk hCP hrun hTop _ i x es j rfl hD hi0 hj hcut hnt IH
  obtain ⟨hsc, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  have hup : es[j].2.isUpper = false := by
    cases h : es[j].2 with
    | clean r b => rfl
    | plain r => rw [h] at hcut; simp [cutOrigin] at hcut
    | upper r => rw [h] at hcut; simp [cutOrigin] at hcut
  rw [hup] at hsc
  have hmc : es[j].2.src.column = x := by simpa [ctxAt] using hsc
  obtain ⟨g1, hgg1, hg1μ⟩ := hb k μ _ Relation.ReflTransGen.refl (by omega) hμ hr
  have hg1c : g1.column < root.column := by rw [← hgc]; exact hgg1.column_lt
  exact Classification.Proofs.ChainCorr.ScaleReach.trans (ha k g1 hgg1)
    (reach_old hrun hTop hg1μ (by omega))

/-- **`BoundaryChain` from `CutParentNT`.** -/
theorem boundaryChain_of_cutParent (hCP : CutParentNT) :
    Classification.Proofs.ChainCorr.BoundaryChain :=
  boundaryChain_of_cut (stepCutNT_of_parent hCP)

/-- **`TopStepLoRoot` from `CutParentNT` and `StepRootTop`.** -/
theorem topStepLoRoot_of_cutParent (hCP : CutParentNT) (hR : StepRootTop) : TopStepLoRoot :=
  topStepLoRoot_of_cut (stepCutNT_of_parent hCP) hR

/-- **`TopStartLoRoot` from `CutParentNT` and `StartRootTop`.** Vacuous: `StartRootTop` and
`TopStartLoRoot` are false (counterexample `(1,13,29,4,18,25,15)[1]`). -/
theorem topStartLoRoot_of_cutParent (hCP : CutParentNT) (hR : StartRootTop) : TopStartLoRoot :=
  topStartLoRoot_of_cut (stepCutNT_of_parent hCP) hR

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.cutWalk
#print axioms OmegaY.Official.Recon.TopChain.Seam.stepCutNT_of_parent
#print axioms OmegaY.Official.Recon.TopChain.Seam.boundaryChain_of_cutParent
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStepLoRoot_of_cutParent
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStartLoRoot_of_cutParent
