/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperWSim.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperWMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerChainRecon
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFinal

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CrossLexFor IsUpper` from a weakened start of the copied chains

`CrossUpperSim.CopyQLower` is **false** at `s = (1,21,5,20,30,23,20)`, `n = 1` (JS indices):
for the top copy `U = (8,4)` of `z = (4,3)` (row `ω < τ = ω·2 ≤ row z⁺ = ω²`),
`a = Q_M(z) = (2,2)` is the root (column `c_r = 2`) and `A = Q_R(U) = (6,3)`. The clause of
`Cp` for the root column asks that the node above `A` has the row `ω²` of the node above `a`;
but the node above `A` is `(6,4)`, of row `ω + 1` (the column `6 = c_r + w` holds the copy of
the lower part of `x₀` below `τ`). The chain of `R` from `A` is `(6,3) → (2,2) → (0,0)`: it
reaches `a` itself, whose upper node has the row `ω²`.

## The weak stand-in relation `Cw`

`Cw i Z z` is `Cp i Z z` (`CrossUpperSimDefs.lean`) with the clause on the node above, for `z`
in the root column, weakened to: if `row z⁺ ≥ τ`, the chain of `R` from `Z` reaches a node
`Z'` whose upper node is at the row of `z⁺` in some column `c_r + w·j`. The chain clause
(the chain of `R` from `Z` reaches the stored parent `b` of `z⁺`) is kept. `Cp → Cw`
(`cw_of_cp`).

The chain clause is all that a step of the chain needs (`cpw_step`, `cpw_chain`); the weakened
clause is what the end of the chain needs (`cpw_end`), and there any column `c_r + w·j` does
(`CrossUpperWMain.lean`: all these columns are upper copies of `c_r` with maps that agree
left of `c_r`).

## Results

* `CopyQLowerW` (**open**): `CopyQLower` with `Cw` for `Cp`;
* `seamLastPosW_of_sim : CopyTop → CopyQLowerW → CopyStepLower → SeamLastPosW`;
* `innerW_of_sim : CopyTop → CopyQLowerW → CopyStepLower → InnerHoldsW`;
* `crossLexFor_upper_of_W : TopStep → CopyQLowerW → CrossLexFor IsUpper` (with the proved
  `Emitted` for `CopyTop`, and `copyStepLower_of_topStep`).
-/

namespace OmegaY.Official.Recon.CrossUpperW

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- The weak stand-in relation of block `i` (see the module doc). -/
def Cw (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (Z : (Frame.ofMountain R).Node) (z : (Frame.ofMountain M).Node) : Prop :=
  (z.1.val < root.column ∧ Z.1.val = z.1.val ∧
      (Frame.ofMountain R).height Z = (Frame.ofMountain M).height z) ∨
  (z.1.val = root.column ∧ Z.1.val = root.column + (M.size - 1 - root.column) * i ∧
      (∀ b, (Frame.ofMountain M).rawParent z = some b →
        ∃ B, RawChain (Frame.ofMountain R) Z B ∧ B.1.val = b.1.val ∧
          (Frame.ofMountain R).height B = (Frame.ofMountain M).height b) ∧
      (∀ z', (Frame.ofMountain M).upper z = some z' → t.row ≤ (Frame.ofMountain M).height z' →
        ∃ Z' Z'' j, RawChain (Frame.ofMountain R) Z Z' ∧
          (Frame.ofMountain R).upper Z' = some Z'' ∧
          Z''.1.val = root.column + (M.size - 1 - root.column) * j ∧
          (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height z')) ∨
  (root.column < z.1.val ∧ z.1.val < M.size - 1 ∧
      Z.1.val = z.1.val + (M.size - 1 - root.column) * i ∧
      (t.row ≤ (Frame.ofMountain M).height z →
        (Frame.ofMountain R).height Z = (Frame.ofMountain M).height z) ∧
      ((Frame.ofMountain M).height z < t.row → TopCopy s n R M Z z))

section Rel

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}

theorem cw_of_cp {Z : (Frame.ofMountain R).Node} {z : (Frame.ofMountain M).Node}
    (h : Cp s n R M t root i Z z) : Cw s n R M t root i Z z := by
  rcases h with h | ⟨he, hZc, hup, hch⟩ | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨he, hZc, hch, fun z' hz' hθ => ?_⟩)
    obtain ⟨Z', hZu, hZh⟩ := hup z' hz' hθ
    exact ⟨Z, Z', i, .here Z, hZu, by rw [(upper_spec hZu).1, hZc], hZh⟩
  · exact Or.inr (Or.inr h)

theorem Cw.column {Z : (Frame.ofMountain R).Node} {z : (Frame.ofMountain M).Node}
    (h : Cw s n R M t root i Z z) :
    Z.1.val = shiftCol root.column (M.size - 1 - root.column) i z.1.val := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ | ⟨h1, _, h2, _⟩
  · rw [h2, shiftCol_of_lt h1]
  · rw [h2, shiftCol_of_le (le_of_eq h1.symm), h1]
  · rw [h2, shiftCol_of_le h1.le]

/-- **One step** with the weak relation. -/
theorem cpw_step (E : Env s n R M t root) (hCT : CopyTop) (hSL : CopyStepLower)
    (hi1 : 1 ≤ i) (hin : i ≤ n) {Z : (Frame.ofMountain R).Node}
    {z a : (Frame.ofMountain M).Node} (hz : Real z) (hzx : z.1.val < M.size - 1)
    (hC : Cw s n R M t root i Z z) (hraw : (Frame.ofMountain M).rawParent z = some a) :
    ∃ A, RawChain (Frame.ofMountain R) Z A ∧ Cw s n R M t root i A a := by
  rcases hC with h | ⟨he, _, hch, _⟩ | h
  · obtain ⟨A, hA, hCA⟩ := cp_step E hCT hSL hi1 hin hz hzx (Or.inl h) hraw
    exact ⟨A, hA, cw_of_cp hCA⟩
  · have haz : a.1.val < z.1.val := rawParent_column_lt E.G hraw
    obtain ⟨B, hB, hBc, hBh⟩ := hch a hraw
    exact ⟨B, hB, Or.inl ⟨by omega, hBc, hBh⟩⟩
  · obtain ⟨A, hA, hCA⟩ := cp_step E hCT hSL hi1 hin hz hzx (Or.inr (Or.inr h)) hraw
    exact ⟨A, hA, cw_of_cp hCA⟩

/-- **A chain of stored parents of `M` is matched by a chain of `R`** (weak relation). -/
theorem cpw_chain (E : Env s n R M t root) (hCT : CopyTop) (hSL : CopyStepLower)
    (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∀ {m c : (Frame.ofMountain M).Node}, RawChain (Frame.ofMountain M) m c → Real m →
      m.1.val < M.size - 1 → ∀ {Z : (Frame.ofMountain R).Node}, Cw s n R M t root i Z m →
        ∃ C, RawChain (Frame.ofMountain R) Z C ∧ Cw s n R M t root i C c := by
  intro m c h
  induction h with
  | here c => intro _ _ Z hC; exact ⟨Z, .here Z, hC⟩
  | @step a b c hraw _ ih =>
    intro ha hax Z hC
    have hG := E.G
    have hba : b.1.val < a.1.val := rawParent_column_lt hG hraw
    obtain ⟨A, hA, hCA⟩ := cpw_step E hCT hSL hi1 hin ha hax hC hraw
    have hPa : (Frame.ofMountain M).P a = some b := (E.NM.rawParent_eq_P ha).symm.trans hraw
    have hb : Real b := real_of_value_pos hG (P_value hG hPa).1
    obtain ⟨C, hCc, hCC⟩ := ih hb (by omega) hCA
    exact ⟨C, rawChain_trans hA hCc, hCC⟩

/-- **The last node** with the weak relation: the chain of `R` from `C` reaches a node `C₀`
whose upper node is at the row of `c⁺`, in the column `f(col c)`, or in a column `c_r + w·j`
when `c` is in the root column. -/
theorem cpw_end (E : Env s n R M t root) (hCT : CopyTop) (hi1 : 1 ≤ i)
    (hin : i ≤ n) {C : (Frame.ofMountain R).Node} {c c' : (Frame.ofMountain M).Node}
    (hcx : c.1.val < M.size - 1) (hC : Cw s n R M t root i C c)
    (hcu : (Frame.ofMountain M).upper c = some c') (hθ : t.row ≤ (Frame.ofMountain M).height c') :
    ∃ C0 C', RawChain (Frame.ofMountain R) C C0 ∧ (Frame.ofMountain R).upper C0 = some C' ∧
      (C'.1.val = shiftCol root.column (M.size - 1 - root.column) i c.1.val ∨
        (c.1.val = root.column ∧ ∃ j, C'.1.val = root.column + (M.size - 1 - root.column) * j)) ∧
      (Frame.ofMountain R).height C' = (Frame.ofMountain M).height c' := by
  rcases hC with h | ⟨he, _, _, hup⟩ | h
  · obtain ⟨C', h1, h2, h3⟩ := cp_end E hCT hi1 hin hcx (Or.inl h) hcu hθ
    exact ⟨C, C', .here C, h1, Or.inl h2, h3⟩
  · obtain ⟨Z', Z'', j, h1, h2, h3, h4⟩ := hup c' hcu hθ
    exact ⟨Z', Z'', h1, h2, Or.inr ⟨he, j, h3⟩, h4⟩
  · obtain ⟨C', h1, h2, h3⟩ := cp_end E hCT hi1 hin hcx (Or.inr (Or.inr h)) hcu hθ
    exact ⟨C, C', .here C, h1, Or.inl h2, h3⟩

end Rel

/-- **Open (weakened `CopyQLower`).** The candidate of the top copy `U` of a node `z` with
`row z < τ ≤ row z⁺` (in a column `y` of block `i`, `x₀` included) stands for the candidate of
`z` in the weak sense `Cw`. -/
def CopyQLowerW : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U : (Frame.ofMountain R).Node) (z z' : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      ∃ a A, (Frame.ofMountain M).Q z = some a ∧ (Frame.ofMountain R).Q U = some A ∧
        Cw s n R M t root i A a

theorem copyQLowerW_of_copyQLower (h : CopyQLower) : CopyQLowerW := by
  intro s n R M t root i y hrun hTop hi1 hy U z z' h1 h2 h3 h4 h5 h6 h7
  obtain ⟨a, A, ha, hA, hC⟩ := h s n R M t root i y hrun hTop hi1 hy U z z' h1 h2 h3 h4 h5 h6 h7
  exact ⟨a, A, ha, hA, cw_of_cp hC⟩

/-- **`SeamLastPosW` from the local statements** (weak start). -/
theorem seamLastPosW_of_sim (hCT : CopyTop) (hQL : CopyQLowerW) (hSL : CopyStepLower) :
    SeamLastPosW := by
  intro s n R M t root i hrun hTop hi1 hmem u p q up hu1 hu hU hup hτup hraw hq hcol
  have hcr := hTop.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have E := env_of hrun hTop u.1.isLt (by rw [hu1]; exact Nat.le_add_right _ _)
  have hG := E.G
  have hF := E.FR
  have hNM := E.NM
  have ht1 := tau_gt_one hTop
  -- `i < n`
  have hin : i < n := by
    unfold blockColumns at hmem
    rw [if_neg (by omega)] at hmem
    simp only [List.mem_range'_1] at hmem
    split at hmem
    · assumption
    · omega
  -- the top `t` of `x₀` and the node `t⁻` below it
  have hx0 : M.size - 1 < M.size := by omega
  obtain ⟨colx, hcolx, htop⟩ : ∃ colx, M[M.size - 1]? = some colx ∧ colx.back? = some t := by
    have h := hTop.top
    cases hc : M[M.size - 1]? with
    | none => rw [hc] at h; cases h
    | some colx => rw [hc] at h; exact ⟨colx, rfl, h⟩
  obtain ⟨_, hcolxe⟩ := Array.getElem?_eq_some_iff.mp hcolx
  subst hcolxe
  rw [Array.back?_eq_getElem?] at htop
  obtain ⟨htl, htc⟩ := Array.getElem?_eq_some_iff.mp htop
  let tN : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hx0⟩, ⟨M[M.size - 1].size - 1, htl⟩⟩
  have htNc : (Frame.ofMountain M).cell tN = t := htc
  have htNh : (Frame.ofMountain M).height tN = t.row := by
    change ((Frame.ofMountain M).cell tN).row = _
    rw [htNc]
  have htN2 : 2 ≤ tN.2.val := two_le_index hG (by rw [htNh]; exact ht1)
  let pM : (Frame.ofMountain M).Node := ⟨tN.1, ⟨tN.2.val - 1, by have := tN.2.isLt; omega⟩⟩
  have hpMu : (Frame.ofMountain M).upper pM = some tN :=
    upper_eq_of_index rfl (by simp [pM]; omega)
  have hpMr : Real pM := by show 0 < tN.2.val - 1; omega
  have hpMh : (Frame.ofMountain M).height pM < t.row := by
    rw [← htNh]
    exact height_lt_of_index hG rfl (by simp [pM]; omega)
  have hTpM : TopBelow (Frame.ofMountain M) t.row pM :=
    topBelow_of_upper hG hpMh hpMu (le_of_eq htNh.symm)
  have hTu : TopBelow (Frame.ofMountain R) t.row u := topBelow_of_upper hF hU hup hτup
  -- `u` is the top copy of `t⁻`, and `Q u` stands for `Q t⁻`
  have hTC := hCT s n R M t root i (M.size - 1) hrun hTop hi1 hmem u pM hu1 rfl hTu hTpM
  obtain ⟨a, A, hQa, hQA, hCA⟩ := hQL s n R M t root i (M.size - 1) hrun hTop hi1 hmem u pM tN
    hu1 rfl hpMr hpMh hpMu (le_of_eq htNh.symm) hTC
  rw [hq] at hQA
  obtain rfl := Option.some.inj hQA
  -- the root and the chain of `M(s)` from `Q t⁻` to it
  have htl' : ((Frame.ofMountain M).cell tN).left = some root := by rw [htNc]; exact hTop.left
  obtain ⟨rootN, hrl, _, _⟩ := hG.stored_valid tN root htl'
  have hrr : Frame.ref rootN = root := lookup_spec hrl
  have hrawp : (Frame.ofMountain M).rawParent pM = some rootN :=
    rawParent_eq_of_upper_left hpMu (by rw [hrr]; exact htl')
  have hrootc : rootN.1.val = root.column := by rw [← hrr]; rfl
  obtain ⟨hr1, hr2⟩ := hbAt_of_normal hNM hpMr tN rootN hpMu hrawp
  rw [htNh] at hr1
  have hPp : (Frame.ofMountain M).P pM = some rootN := (hNM.rawParent_eq_P hpMr).symm.trans hrawp
  obtain ⟨qM, hqM, hit⟩ := (P_iff hG).mp hPp
  have hqa : qM = a := Option.some.inj (hqM.symm.trans hQa)
  rw [hqa] at hit
  have har : Real a := Q_real hG hpMr hQa
  have hchain := ParentPath.rawChain hNM (hit.parentPath hG (hG.real_positive _ har)) har
  have hax : a.1.val < M.size - 1 := Q_column_lt hG hQa
  -- the chain of `R`
  obtain ⟨C, hCch, hCC⟩ := cpw_chain E hCT hSL hi1 hin.le hchain har hax hCA
  have hCcol := hCC.column
  rw [hrootc, shiftCol_of_le le_rfl] at hCcol
  -- the node `r⁺` above the root
  have hXeq : root.column + (M.size - 1 - root.column) * (i + 1) =
      M.size - 1 + (M.size - 1 - root.column) * i := by
    rw [Nat.mul_succ]
    generalize (M.size - 1 - root.column) * i = P
    omega
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc : up.1.val = root.column + (M.size - 1 - root.column) * (i + 1) := by
    rw [hXeq, hup1, hu1]
  have C0 := upperCopy_root E.top E.CI E.FR (i := i + 1) (by rw [← hupc]; exact up.1.isLt)
  obtain ⟨N, hNc, hNh⟩ := C0.bwd up hupc hτup
  have hrNc : rootN.1 = N.1 := Fin.ext (by rw [hrootc, hNc])
  have hrN : rootN.2.val < N.2.val :=
    index_lt_of_height_lt hG hrNc (by rw [hNh]; exact lt_of_lt_of_le hr1 hτup)
  have hlenr : rootN.2.val + 1 < (Frame.ofMountain M).length rootN.1 := by
    have := N.2.isLt
    have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length rootN.1 := by
      rw [hrNc]
    omega
  let rp : (Frame.ofMountain M).Node := ⟨rootN.1, ⟨rootN.2.val + 1, hlenr⟩⟩
  have hru : (Frame.ofMountain M).upper rootN = some rp := upper_eq_of_index rfl rfl
  have hrpτ : t.row ≤ (Frame.ofMountain M).height rp := by
    by_contra hlt
    have := hr2 rp rfl (by rw [htNh]; exact lt_of_not_ge hlt)
    simp [rp] at this
  have hrpup : (Frame.ofMountain M).height rp = (Frame.ofMountain R).height up := by
    apply le_antisymm
    · rw [← hNh]
      exact height_le_of_index hG hrNc (by simp [rp]; omega)
    · obtain ⟨Zr, hZrc, hZrh⟩ := C0.fwd rp (by simp [rp, hrootc]) hrpτ
      have hZu : u.1 = Zr.1 := Fin.ext (by rw [hZrc, ← hupc, hup1])
      have hi2 := index_lt_of_height_lt hF hZu (by rw [hZrh]; exact lt_of_lt_of_le hU hrpτ)
      rw [← hZrh]
      exact height_le_of_index hF (hup1.trans hZu) (by omega)
  -- the node above `C`
  have hrx : rootN.1.val < M.size - 1 := by omega
  obtain ⟨C0, C', hC0, hC'u, hC'c, hC'h⟩ := cpw_end E hCT hi1 hin.le hrx hCC hru hrpτ
  rcases hC'c with h | ⟨_, j, hj⟩
  · exact ⟨C0, C', i, rawChain_trans hCch hC0, hC'u,
      by rw [h, hrootc, shiftCol_of_le le_rfl], by rw [hC'h, hrpup]⟩
  · exact ⟨C0, C', j, rawChain_trans hCch hC0, hC'u, hj, by rw [hC'h, hrpup]⟩

/-- **`InnerHoldsW` from the local statements** (weak start). -/
theorem innerW_of_sim (hCT : CopyTop) (hQL : CopyQLowerW) (hSL : CopyStepLower) :
    InnerHoldsW := by
  intro s n R M t root i x hrun hTop hxb hxx0 u p q up n0 N np qM hu1 hu hup hτup hraw hq
    hcol hN1 hNh hn0N hn0raw hqM
  have hcr := hTop.lt
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hxb
  have hxlt : x < M.size - 1 := lt_of_le_of_ne hxle hxx0
  have hi1 : 1 ≤ i := by
    by_contra h
    have : i = 0 := by omega
    subst this
    simp [blockColumns] at hxb
    exact hxx0 hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hX0 : M.size - 1 ≤ x + (M.size - 1 - root.column) * i := by
    generalize (M.size - 1 - root.column) * i = P at hwi ⊢
    omega
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by rw [← hu1]; exact u.1.isLt
  have E := env_of hrun hTop hXR hX0
  have hG := E.G
  have hF := E.FR
  have hNM := E.NM
  have ht1 := tau_gt_one hTop
  have hin : i ≤ n := block_le E hxgt hxle hXR hX0
  have C0 := upperCopy_inner E hxgt hxlt hi1 hXR
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hNτ : t.row ≤ (Frame.ofMountain M).height N := by rw [hNh]; exact hτup
  obtain ⟨hN1', hN2'⟩ := upper_spec hn0N
  have hN2 := two_le_index hG (lt_of_lt_of_le ht1 hNτ)
  have hn0r : Real n0 := by unfold Real; omega
  have hn0c : n0.1.val = x := by rw [← hN1', hN1]
  have hqMr : Real qM := Q_real hG hn0r hqM
  have hqMx : qM.1.val < M.size - 1 := by
    have := Q_column_lt hG hqM
    omega
  -- `Q u` stands for `Q n₀`
  have hstart : Cw s n R M t root i q qM := by
    by_cases hU : t.row ≤ (Frame.ofMountain R).height u
    · -- `u` is in the upper part: it copies `n₀`
      obtain ⟨n', hn'c, hn'h⟩ := C0.bwd u hu1 hU
      have hn'N : n'.1 = N.1 := Fin.ext (by rw [hn'c, hN1])
      have hn'lt : (Frame.ofMountain M).height n' < (Frame.ofMountain M).height N := by
        rw [hn'h, hNh]
        exact height_lt_of_index hF hup1.symm (by omega)
      have hi' := index_lt_of_height_lt hG hn'N hn'lt
      have hlen' : n'.2.val + 1 < (Frame.ofMountain M).length n'.1 := by
        have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length n'.1 := by
          rw [hn'N]
        have := N.2.isLt
        omega
      let n'' : (Frame.ofMountain M).Node := ⟨n'.1, ⟨n'.2.val + 1, hlen'⟩⟩
      have hn'u : (Frame.ofMountain M).upper n' = some n'' := upper_eq_of_index rfl rfl
      obtain ⟨Z', hZu, _, hZh⟩ := C0.upper hG hF hn'c hu1 (by rw [hn'h]; exact hU)
        hn'h.symm hn'u
      rw [hup] at hZu
      obtain rfl := Option.some.inj hZu
      have hn''N : n'' = N := node_eq_of_height hG hn'N (by rw [← hZh, hNh])
      have hn'n0 : n' = n0 := by
        apply node_eq_of_index (hn'N.trans hN1')
        have := congrArg (fun z : (Frame.ofMountain M).Node => z.2.val) hn''N
        simp only [n''] at this
        omega
      subst hn'n0
      -- the column of `Q u`
      obtain ⟨LM, hLM, _, _, hqLM, _⟩ := Q_spec hG hqM
      obtain ⟨L, hL, _, _, hqL, _⟩ := Q_spec hF hq
      obtain ⟨Bref, hBl, hBc⟩ := C0.par n' u (Frame.ref LM) hn'c hu1 (by rw [hn'h]; exact hU)
        hn'h.symm hLM
      have hBL : Bref = Frame.ref L := Option.some.inj (hBl.symm.trans hL)
      have hqcol : q.1.val = shiftCol root.column (M.size - 1 - root.column) i qM.1.val := by
        rw [hqL, hqLM]
        have e : L.1.val = Bref.column := by rw [hBL]; rfl
        rw [e, hBc]
        rfl
      have hqR := highestIn_of_Q hF hq
      rw [← hn'h] at hqR
      exact cw_of_cp <| cp_of_highest E hCT hi1 hin (fun r r' h1 h2 => h1.trans h2)
        (fun r hr => hr.le.trans (by rw [hn'h]; exact hU)) hqMr hqMx hqcol
        (highestIn_of_Q hG hqM) hqR
    · -- `u` is the highest node of `X` below `τ`
      have hUl : (Frame.ofMountain R).height u < t.row := lt_of_not_ge hU
      have hTu : TopBelow (Frame.ofMountain R) t.row u := topBelow_of_upper hF hUl hup hτup
      have hn0τ : (Frame.ofMountain M).height n0 < t.row := by
        by_contra hn
        obtain ⟨W, hWc, hWh⟩ := C0.fwd n0 hn0c (le_of_not_gt hn)
        have hWup : W.1 = up.1 := Fin.ext (by rw [hWc, hup1, hu1])
        have h1 : W.2.val < up.2.val := index_lt_of_height_lt hF hWup (by
          rw [hWh, ← hNh]
          exact height_lt_of_index hG hN1'.symm (by omega))
        have h2 : (Frame.ofMountain R).height W ≤ (Frame.ofMountain R).height u :=
          height_le_of_index hF (hWup.trans hup1) (by omega)
        rw [hWh] at h2
        exact hn (lt_of_le_of_lt h2 hUl)
      have hTn0 : TopBelow (Frame.ofMountain M) t.row n0 :=
        topBelow_of_upper hG hn0τ hn0N hNτ
      have hTC := hCT s n R M t root i x hrun hTop hi1 hxb u n0 hu1 hn0c hTu hTn0
      obtain ⟨a, A, hQa, hQA, hCA⟩ := hQL s n R M t root i x hrun hTop hi1 hxb u n0 N hu1 hn0c
        hn0r hn0τ hn0N hNτ hTC
      rw [hq] at hQA
      rw [hqM] at hQa
      obtain rfl := Option.some.inj hQA
      obtain rfl := Option.some.inj hQa
      exact hCA
  -- the column of `p`
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  obtain ⟨N', hn0N', hNl⟩ := rawParent_spec hn0raw
  rw [hn0N] at hn0N'
  obtain rfl := Option.some.inj hn0N'
  obtain ⟨Aref, hA, hAc⟩ := C0.par N up (Frame.ref np) hN1 (by rw [hup1]; exact hu1) hNτ
    hNh.symm hNl
  have hAp : Aref = Frame.ref p := Option.some.inj (hA.symm.trans hpl)
  have hpcol : p.1.val = shiftCol root.column (M.size - 1 - root.column) i np.1.val := by
    have e : p.1.val = Aref.column := by rw [hAp]; rfl
    rw [e, hAc]
    rfl
  have hne : qM ≠ np := by
    intro h
    apply hcol
    apply Fin.ext
    rw [hstart.column, hpcol, h]
  -- the chain of `M(s)` and its match in `R`
  obtain ⟨cM, cMp, hchM, hcMraw, hcMu, hhN, _, _⟩ := normal_crossLex hNM hn0r hn0N hn0raw hqM hne
  obtain ⟨C, hCch, hCC⟩ := cpw_chain E hCT hSL hi1 hin hchM hqMr hqMx hstart
  have hcMx : cM.1.val < M.size - 1 := lt_of_le_of_lt (hchM.column_le hG) hqMx
  obtain ⟨C0, C', hC0, hCu, hC'c, hC'h⟩ :=
    cpw_end E hCT hi1 hin hcMx hCC hcMu (by rw [← hhN]; exact hNτ)
  exact ⟨cM, C0, C', hchM, hcMraw, rawChain_trans hCch hC0, hCu, hC'c,
    by rw [hC'h, ← hhN, hNh]⟩




/-! ## The main theorem -/

/-- **`CrossLexFor IsUpper` from `TopStep` and the weak start `CopyQLowerW`.** (`CopyTop` is
proved from the proved `Emitted`; `CopyStepLower` follows from `TopStep`.) -/
theorem crossLexFor_upper_of_W (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hQW : CopyQLowerW) : CrossLexFor IsUpper :=
  crossLexFor_upper_W
    (seamLastPosW_of_sim (copyTop_of_emitted Classification.Proofs.CopyShape.Final.emitted) hQW
      (LowerChainRecon.copyStepLower_of_topStep hTS))
    (innerW_of_sim (copyTop_of_emitted Classification.Proofs.CopyShape.Final.emitted) hQW
      (LowerChainRecon.copyStepLower_of_topStep hTS))

end OmegaY.Official.Recon.CrossUpperW

#print axioms OmegaY.Official.Recon.CrossUpperW.seamLastPosW_of_sim
#print axioms OmegaY.Official.Recon.CrossUpperW.innerW_of_sim
#print axioms OmegaY.Official.Recon.CrossUpperW.crossLexFor_upper_of_W
