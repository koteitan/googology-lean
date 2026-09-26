/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Pk4PairAbove.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4Pair

set_option backward.do.legacy false

/-!
# `PairAbove` holds

`CrossPlainPos.PairAbove K` (`CrossPlainPosSim.lean`): let `u⁺` be a node of a new column
`x + w·i` (`i ≥ 1`) with an origin of kind `K` and the source `N`, and `B` a node of `M(s)` with
`c_r < col B < col N`, the stored left end and the row of `N`. For every node `C` standing for the
node `B⁻` below `B` (`Cp`), the node `C⁺` above `C` has the row of `u⁺` and an origin of kind
plain or clean with the source `B`.

## Proof

* `B⁻` is below `τ` (`row B⁻ < row B = row N < τ`), so `C` is the top copy of `B⁻` in the
  column `Y = col B + w·i` (`Cp`, `col B⁻ = col B < x₀`).
* `B` is the origin of a non-cut emit `m` of `Y` (the covering part of `NoMA.emitsT_shapeW`).
  The origins of the emits of `Y` do not go down (`emitsT_order`), so `m` comes after the emit
  `j_C` of `C`, and the emit `j_C + 1` has an origin between `B⁻` and `B`: `B⁻` is excluded since
  `C` is the top copy, and `B` before `m` is excluded since a non-cut emit has an origin
  different from every earlier emit (`NNC`). So `m = j_C + 1`, and `C⁺` is the non-cut copy of
  `B`; it is below `τ`, so plain or clean.
* The rows (`copy_rows_eq`): if the common left end `l` is left of `c_r`, both copies are plain
  (a clean copy has an origin with its leg at or right of `c_r`, `emitsT_cleanLeg`) and keep the
  row of their origins (`emitsT_plainLeft`). Otherwise both rows are `Ψ_l(row N)`
  (`ProfileLeg.lowerT_formula`, `ProfileLeg.Ψ_leg`, `ProfileLeg.rowΨ_cmp`).

`pairAbove_all : ∀ K, (∀ o, K o → LowKind o) → PairAbove K`. The hypothesis `Lex N B` is not
used.
-/

namespace OmegaY.Official.Recon.Pk4

open Canonical Expansion Geometry Frame Classification
open CrossPlainPos (LowKind lowKind_notUpper)
open CrossUpperSim (Cp TopCopy IsCopy env_of block_le mem_blockColumns_of_inner)
open OmegaY.Official.Classification.Proofs.ChainCorr.Inner (SrcRel emitsT_order
  index_le_of_row_le ref_ext isCleanO)
open OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg (lowerT_formula Ψ_leg rowΨ_cmp
  topOK_topA blockEnv)

/-! ## Lower emits -/

/-- An emit whose origin is below `τ` is a lower emit. -/
theorem notUpper_of_below {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {p : Emit × Origin} (hp : p ∈ es) {c : Cell}
    (hc : Reserve.cell? ctx.source p.2.src = some c) (hlt : official c.row < τ) :
    p.2.isUpper = false := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := CrossPlain.emitsT_parts h
  rcases List.mem_append.mp hp with hp | hp
  · exact (Recon.LowerPB.lowerT_good hlo p hp).2
  · exfalso
    obtain ⟨k, c', _, hc', hpo, _, hτ, _⟩ := (Recon.LowerPB.upperT_spec hus).1 p hp
    rw [hpo] at hc
    simp only [Origin.src] at hc
    rw [hc'] at hc
    cases hc
    exact absurd hlt (not_lt.mpr hτ)

/-- The origin of a lower emit is below `τ`. -/
theorem below_of_notUpper {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {p : Emit × Origin} (hp : p ∈ es) (hnu : p.2.isUpper = false) :
    ∃ cv, Reserve.cell? ctx.source p.2.src = some cv ∧ official cv.row < τ := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := CrossPlain.emitsT_parts h
  rcases List.mem_append.mp hp with hp | hp
  · exact Recon.LowerPB.lowerT_below hlo p hp
  · have := CrossPlain.upperT_isUpper hus p hp
    rw [hnu] at this
    cases this

/-- A lower emit is in the lower part. -/
theorem mem_lower_of_notUpper {ctx : Context} {τ : Row} {lo us : List (Emit × Origin)}
    (hus : upperT ctx τ = .ok us) {p : Emit × Origin} (hp : p ∈ lo ++ us)
    (hnu : p.2.isUpper = false) : p ∈ lo := by
  rcases List.mem_append.mp hp with hp | hp
  · exact hp
  · have := CrossPlain.upperT_isUpper hus p hp
    rw [hnu] at this
    cases this

/-- The origin of a lower emit of `ctxAt … x …` is in the column `x`. -/
theorem src_col {M R : Mountain} {x i cr w x0 X : Nat} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT (ctxAt M R x i cr w x0 X) τ = .ok es) {p : Emit × Origin} (hp : p ∈ es)
    (hnu : p.2.isUpper = false) : p.2.src.column = x ∧ 1 ≤ p.2.src.index := by
  obtain ⟨hcol, hidx, _⟩ := emitsT_good h p hp
  simp only [hnu, Bool.false_eq_true, if_false] at hcol
  exact ⟨hcol, hidx⟩

/-! ## The rows of two copies -/

/-- **Two non-cut lower copies of nodes with the same stored left end and the same row have
the same row** (columns `x, y > c_r` of a block `1 ≤ i ≤ n`). -/
theorem copy_rows_eq {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {x y X Y : Nat}
    (hxg : root.column < x) (hxl : x ≤ M.size - 1) (hyg : root.column < y)
    (hyl : y ≤ M.size - 1) (hX : X = x + (M.size - 1 - root.column) * i)
    (hY : Y = y + (M.size - 1 - root.column) * i) {es esY : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (official t.row) = .ok es)
    (hesY : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) Y)
      (official t.row) = .ok esY)
    {p q : Emit × Origin} (hp : p ∈ es) (hq : q ∈ esY)
    (hpc : OmegaY.Official.Classification.Proofs.ChainCorr.cutOrigin p.2 = false) (hqc : OmegaY.Official.Classification.Proofs.ChainCorr.cutOrigin q.2 = false)
    (hpu : p.2.isUpper = false) (hqu : q.2.isUpper = false) {cN cB : Cell}
    (hcN : Reserve.cell? M p.2.src = some cN) (hcB : Reserve.cell? M q.2.src = some cB)
    {l : Ref} (hlN : cN.left = some l) (hlB : cB.left = some l) (hlx : l.column ≤ M.size - 1)
    (hrow : cN.row = cB.row) : p.1.row = q.1.row := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  obtain ⟨hpcol, hpidx⟩ := src_col hes hp hpu
  obtain ⟨hqcol, hqidx⟩ := src_col hesY hq hqu
  have hN1 : (1 : Row) ≤ cN.row := one_le_row hV hcN hpidx
  by_cases hlc : l.column < root.column
  · -- both copies are plain and keep the rows of their origins
    have hplain : ∀ {Z : Nat} {z : Nat} {e : Emit × Origin} {ees : List (Emit × Origin)} {cz : Cell},
        root.column < z → z ≤ M.size - 1 →
        emitsT (ctxAt M R z i root.column (M.size - 1 - root.column) (M.size - 1) Z)
          (official t.row) = .ok ees → e ∈ ees → e.2.isUpper = false →
        Reserve.cell? M e.2.src = some cz → cz.left = some l → e.1.row = official cz.row := by
      intro Z z e ees cz hzg hzl hees he heu hcz hlz
      cases ho : e.2 with
      | plain r =>
          have hcz' : Reserve.cell? M r = some cz := by
            have : e.2.src = r := by rw [ho]; rfl
            rw [← this]; exact hcz
          exact emitsT_plainLeft hTop (ctx := ctxAt M R z i root.column
            (M.size - 1 - root.column) (M.size - 1) Z) rfl rfl (by simp only [ctxAt]; omega)
            (by simp only [ctxAt]; omega) hees e he r ho cz hcz' l hlz hlc
      | clean r b =>
          exfalso
          have := emitsT_cleanLeg hTop (ctx := ctxAt M R z i root.column
            (M.size - 1 - root.column) (M.size - 1) Z) rfl rfl (by simp only [ctxAt]; omega)
            hees e he (by rw [ho]; rfl) cz hcz l hlz
          omega
      | upper r => rw [ho] at heu; cases heu
    rw [hplain hxg hxl hes hp hpu hcN hlN, hplain hyg hyl hesY hq hqu hcB hlB, hrow]
  · -- both rows are `Ψ_l` of the row of the origin
    have hlc' : root.column ≤ l.column := by omega
    have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ hi1
    have hBx : Recon.LowerPB.BCtx M R root.column (M.size - 1) i
        (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X) :=
      Recon.LowerPB.bctx_ctxAt (le_of_lt hxg) hxl (by omega)
    have hBy : Recon.LowerPB.BCtx M R root.column (M.size - 1) i
        (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) Y) :=
      Recon.LowerPB.bctx_ctxAt (le_of_lt hyg) hyl (by omega)
    have hBl : Recon.LowerPB.BCtx M R root.column (M.size - 1) i
        (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
          (root.column + (M.size - 1 - root.column) * i + 1)) :=
      Recon.LowerPB.bctx_ctxAt hlc' hlx (by omega)
    obtain ⟨lo, us, hlo, hus, hesq⟩ := CrossPlain.emitsT_parts hes
    obtain ⟨loY, usY, hloY, husY, hesqY⟩ := CrossPlain.emitsT_parts hesY
    subst hesq hesqY
    have hp' := mem_lower_of_notUpper hus hp hpu
    have hq' := mem_lower_of_notUpper husY hq hqu
    obtain ⟨qq, hqq, hin1, hrow1⟩ := lowerT_formula hrun hTop hi1 hin hBx hlo p hp'
      (by rw [Classification.Proofs.CopyShape.Found.cutO_eq]; exact hpc) cN hcN
    obtain ⟨qq', hqq', hin2, hrow2⟩ := lowerT_formula hrun hTop hi1 hin hBy hloY q hq'
      (by rw [Classification.Proofs.CopyShape.Found.cutO_eq]; exact hqc) cB hcB
    have hcoN : Reserve.cell? M ⟨x, p.2.src.index⟩ = some cN := by
      rw [← hpcol]; exact hcN
    have hcoB : Reserve.cell? M ⟨y, q.2.src.index⟩ = some cB := by
      rw [← hqcol]; exact hcB
    have e1 := Ψ_leg (n := n) hTop hBx hBl (by simp only [ctxAt]; omega) hpidx hcoN hlN rfl hqq
      hin1 le_rfl
    have e2 := Ψ_leg (n := n) hTop hBy hBl (by simp only [ctxAt]; omega) hqidx hcoB hlB rfl hqq'
      hin2 le_rfl
    have hT := topOK_topA (E := blockEnv M R root.column i)
      (ctx := ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
        (root.column + (M.size - 1 - root.column) * i + 1)) rfl rfl
    have hcmp := (rowΨ_cmp hT hqq hqq' hin1 hin2).2 (by rw [hrow])
    rw [hrow1, hrow2, e1, e2]
    exact hcmp

/-! ## `PairAbove` -/

/-- **`PairAbove K` for every kind `K` of plain or clean copies.** -/
theorem pairAbove_all (K : Origin → Prop) (hK : ∀ o, K o → LowKind o) :
    CrossPlainPos.PairAbove K := by
  intro s n R hrun M t root hTop i x hi hxb up o hX hup1 ho hKo N B Bm hN hleft hh hBN hcrB _
    hBmB C hCp
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi
  have hV : MountainValid M := build_valid_of_success hTop.build
  have hG : (Frame.ofMountain M).Ordered := (build_normal_of_success hTop.build).toOrdered
  -- the column `X` of `u⁺`
  obtain ⟨es, em, colX, hes, hRX, hasm, hj⟩ := LowerChainRecon.originAt_unpack2 hTop hxb hX ho
  have hjl : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hj
    exact Option.some.inj hj
  have hmem := List.getElem_mem hjl
  have hX0 : M.size - 1 ≤ up.1.val := by rw [hX]; omega
  have E := env_of hrun hTop up.1.isLt hX0
  have hin : i ≤ n := block_le E hxg hxl (by rw [← hX]; exact up.1.isLt) (by rw [← hX]; exact hX0)
  have hnu : o.isUpper = false := lowKind_notUpper o (hK o hKo)
  have hnu' : es[up.2.val - 1].2.isUpper = false := by rw [hej]; exact hnu
  -- the origin `N`
  have hcN : Reserve.cell? M es[up.2.val - 1].2.src = some ((Frame.ofMountain M).cell N) := by
    rw [hej]
    show Reserve.cell? M o.src = _
    rw [← hN]
    exact LowerChainRecon.cell?_ref N
  obtain ⟨hNcol, hNidx⟩ := src_col hes hmem hnu'
  have hNx : N.1.val = x := by
    have h1 : es[up.2.val - 1].2.src = Frame.ref N := by rw [hej]; exact hN.symm
    rw [h1] at hNcol
    exact hNcol
  obtain ⟨l, hl⟩ := left_of_lower hTop (ctx := ctxAt M R x i root.column
    (M.size - 1 - root.column) (M.size - 1) up.1.val) rfl (by simp only [ctxAt]; omega) hes hmem
    hnu' hcN
  have hlB : ((Frame.ofMountain M).cell B).left = some l := by rw [← hleft]; exact hl
  obtain ⟨left, hlk, hlc, _⟩ := hG.stored_valid B l hlB
  have hlref : Frame.ref left = l := Frame.lookup_spec hlk
  have hlcol : l.column < B.1.val := by rw [← hlref]; exact hlc
  obtain ⟨cvN, hcvN, hτN⟩ := below_of_notUpper hes hmem hnu'
  have hcvN' : cvN = (Frame.ofMountain M).cell N := Option.some.inj (hcvN.symm.trans hcN)
  subst hcvN'
  have hhNB : ((Frame.ofMountain M).cell N).row = ((Frame.ofMountain M).cell B).row := hh
  -- `B` and `B⁻`
  obtain ⟨hBm1, hBm2⟩ := upper_spec hBmB
  have hBmBc : Bm.1.val = B.1.val := by rw [hBm1]
  have hyx : B.1.val < M.size - 1 := by omega
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  have hBmlt : (Frame.ofMountain M).height Bm < (Frame.ofMountain M).height B :=
    LowerPB.Cone.height_lt_of_index_lt hG hBm1.symm (by omega)
  have hNτ : (Frame.ofMountain M).height N < t.row :=
    CrossUpperSim.lt_of_official_lt ht1 hτN
  have hBτ' : official ((Frame.ofMountain M).cell B).row < official t.row := by
    rw [← hhNB]; exact hτN
  have hBmτ : (Frame.ofMountain M).height Bm < t.row :=
    lt_trans hBmlt (by show ((Frame.ofMountain M).cell B).row < t.row; rw [← hhNB]; exact hNτ)
  -- `C` is the top copy of `B⁻`
  rcases hCp with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, hCc, _, hTC⟩
  · exfalso; omega
  · exfalso; omega
  obtain ⟨⟨hC1, oC, hoC, hoCsrc⟩, hCtop⟩ := hTC hBmτ
  have hyb : B.1.val ∈ blockColumns root.column (M.size - 1) n i :=
    mem_blockColumns_of_inner hi (by omega) hcrB hyx
  have hCc' : C.1.val = B.1.val + (M.size - 1 - root.column) * i := by rw [hCc, hBmBc]
  obtain ⟨esY, emC, colY, hesY, hRY, hasmY, hjC⟩ :=
    LowerChainRecon.originAt_unpack2 hTop hyb hCc' hoC
  have hjCl : C.2.val - 1 < esY.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjC
    cases hjC
  have hejC : esY[C.2.val - 1] = (emC, oC) := by
    rw [List.getElem?_eq_getElem hjCl] at hjC
    exact Option.some.inj hjC
  have hsrcC : esY[C.2.val - 1].2.src = Frame.ref Bm := by rw [hejC]; exact hoCsrc
  -- the facts of the column `Y`
  set ctxY := ctxAt M R B.1.val i root.column (M.size - 1 - root.column) (M.size - 1) C.1.val
    with hctxY
  have hBY : Recon.LowerPB.BCtx M R root.column (M.size - 1) i ctxY :=
    Recon.LowerPB.bctx_ctxAt (le_of_lt hcrB) (by omega) (by rw [hCc']; omega)
  have hMD := Classification.Proofs.CopyShape.Found.factMD_of_bctx hTop hBY
  have hMH := Classification.Proofs.CopyShape.Found.factMH_of_bctx hrun hTop hi hin hBY
  obtain ⟨hNNC, _, hcov⟩ := Classification.Proofs.CopyShape.NoMA.emitsT_shapeW ctxY _ _ _ hV
    (by simp only [hctxY, ctxAt]; omega) (fun _ _ => rfl) hMD hMH hesY
  have hord := emitsT_order (ctx := ctxY) hV hesY
  -- `B` is the origin of a non-cut emit `m`
  have hcB := LowerChainRecon.cell?_ref B
  have hcBm := LowerChainRecon.cell?_ref Bm
  obtain ⟨q, hq, hqsrc, hqcut⟩ := hcov (Frame.ref B) _ rfl (by show 1 ≤ B.2.val; omega) hcB
    (Or.inl hBτ')
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hq
  have hBm1r : (1 : Row) ≤ ((Frame.ofMountain M).cell Bm).row := by
    obtain ⟨_, hidx, _⟩ := emitsT_good hesY _ (List.getElem_mem hjCl)
    rw [hsrcC] at hidx
    exact one_le_row hV hcBm hidx
  have hoBmB : official ((Frame.ofMountain M).cell Bm).row <
      official ((Frame.ofMountain M).cell B).row := Recon.official_strictMono hBm1r hBmlt
  have hrefne : Frame.ref B ≠ Frame.ref Bm := by
    intro h
    have := congrArg Ref.index h
    simp only [Frame.ref] at this
    omega
  -- `m` comes after the emit of `C`
  have hmC : C.2.val - 1 < m := by
    rcases Nat.lt_trichotomy m (C.2.val - 1) with h | h | h
    · exfalso
      have hrel := List.pairwise_iff_getElem.mp hord m (C.2.val - 1) hm hjCl h
        _ _ (by rw [hqsrc]; exact hcB) (by rw [hsrcC]; exact hcBm)
      rcases hrel with h' | ⟨h', _⟩
      · exact absurd (lt_trans h' hoBmB) (lt_irrefl _)
      · rw [h'] at hoBmB; exact lt_irrefl _ hoBmB
    · exfalso
      subst h
      exact hrefne (hqsrc.symm.trans hsrcC)
    · exact h
  -- the node above `C`
  have hRYc : (R[C.1.val]'C.1.isLt) = colY := by
    rcases Array.getElem?_eq_some_iff.mp hRY with ⟨_, h⟩
    exact h
  have hsizeY : colY.size = esY.length + 1 := by
    have := (assemble_spec hasmY).1
    simpa using this
  have hlenY : C.2.val + 1 < (Frame.ofMountain R).length C.1 := by
    have e : (Frame.ofMountain R).length C.1 = esY.length + 1 := by
      show (R[C.1.val]'C.1.isLt).size = _
      rw [hRYc, hsizeY]
    omega
  set C' : (Frame.ofMountain R).Node := ⟨C.1, ⟨C.2.val + 1, hlenY⟩⟩ with hC'
  have hC'u : (Frame.ofMountain R).upper C = some C' := LowerPB.Cone.upper_of_lt hlenY
  have hC'c : C'.1.val = B.1.val + (M.size - 1 - root.column) * i := hCc'
  have hC'r : Real C' := by show 0 < C.2.val + 1; omega
  obtain ⟨hjC', hoC'⟩ := LowerChainRecon.originAt_of_emits E hi hyb hC'c hC'r hesY
  have hidxC' : C'.2.val - 1 = C.2.val - 1 + 1 := by show C.2.val + 1 - 1 = C.2.val - 1 + 1; omega
  -- the emit above the emit of `C` is the emit `m`
  have hm1 : m = C.2.val - 1 + 1 := by
    by_contra hne
    have hlt : C.2.val - 1 + 1 < m := by omega
    have hk1 : C.2.val - 1 + 1 < esY.length := by omega
    obtain ⟨hScol, hSidx, cS, hcS, _⟩ := emitsT_good hesY _ (List.getElem_mem hk1)
    have hScol' : esY[C.2.val - 1 + 1].2.src.column = B.1.val := by
      split_ifs at hScol with hup
      · rw [hScol]
        simp only [upperColumn, hctxY, ctxAt]
        rw [if_neg (by omega)]
      · exact hScol
    have hcS1 : (1 : Row) ≤ cS.row := one_le_row hV hcS hSidx
    have hr1 := List.pairwise_iff_getElem.mp hord (C.2.val - 1) (C.2.val - 1 + 1) hjCl hk1
      (by omega) _ _ (by rw [hsrcC]; exact hcBm) hcS
    have hr2 := List.pairwise_iff_getElem.mp hord (C.2.val - 1 + 1) m hk1 hm hlt
      _ _ hcS (by rw [hqsrc]; exact hcB)
    have ho1 : official ((Frame.ofMountain M).cell Bm).row ≤ official cS.row := by
      rcases hr1 with h' | ⟨h', _⟩
      · exact h'.le
      · exact h'.le
    have ho2 : official cS.row ≤ official ((Frame.ofMountain M).cell B).row := by
      rcases hr2 with h' | ⟨h', _⟩
      · exact h'.le
      · exact h'.le
    have hB1r : (1 : Row) ≤ ((Frame.ofMountain M).cell B).row := le_trans hBm1r hBmlt.le
    have i1 := index_le_of_row_le hV (by show Bm.1.val = _; rw [hScol']; exact hBmBc) hcBm hcS
      (CrossUpperSim.le_of_official_le hcS1 ho1)
    have i2 := index_le_of_row_le hV (by rw [hScol']; rfl) hcS hcB
      (CrossUpperSim.le_of_official_le hB1r ho2)
    simp only [Frame.ref] at i1 i2
    rcases Nat.lt_or_ge (esY[C.2.val - 1 + 1].2.src.index) B.2.val with h' | h'
    · -- the origin is `B⁻`: a copy of `B⁻` above `C`
      have hsrcBm : esY[C.2.val - 1 + 1].2.src = Frame.ref Bm :=
        ref_ext (by rw [hScol']; exact hBmBc.symm) (by simp only [Frame.ref]; omega)
      apply hCtop C' rfl (by show C.2.val < C.2.val + 1; omega)
      refine ⟨by show 1 ≤ C.2.val + 1; omega, _, hoC', ?_⟩
      have : esY[C'.2.val - 1] = esY[C.2.val - 1 + 1] := by congr 1
      rw [this]
      exact hsrcBm
    · -- the origin is `B`, earlier than the non-cut emit `m` of `B`
      have hsrcB : esY[C.2.val - 1 + 1].2.src = Frame.ref B :=
        ref_ext (by rw [hScol']; rfl) (by simp only [Frame.ref]; omega)
      have hnnc := List.pairwise_iff_getElem.mp hNNC (C.2.val - 1 + 1) m hk1 hm hlt
      exact hnnc hqcut (hsrcB.trans hqsrc.symm)
  subst hm1
  have hqnu : esY[C.2.val - 1 + 1].2.isUpper = false :=
    notUpper_of_below hesY (List.getElem_mem hm) (by rw [hqsrc]; exact hcB) hBτ'
  have hoeq : esY[C'.2.val - 1] = esY[C.2.val - 1 + 1] := by congr 1
  refine ⟨C', hC'u, ?_, esY[C.2.val - 1 + 1].2, ?_, ?_, hqsrc⟩
  · -- the rows
    rw [height_of_emit hRY hasmY C' rfl (by omega) (by show 1 ≤ C.2.val + 1; omega),
      height_of_emit hRX hasm up rfl hjl hup1, hoeq]
    congr 1
    have hBleft : B.1.val ≤ M.size - 1 := by omega
    exact (copy_rows_eq hrun hTop hi hin hcrB (by omega) hxg hxl hCc' hX hesY hes
      (List.getElem_mem hm) hmem hqcut (by
        rw [hej]
        rcases hK o hKo with ⟨r, hr⟩ | ⟨r, hr⟩ <;> rw [hr] <;> rfl) hqnu hnu'
      (by rw [hqsrc]; exact hcB) hcN hlB hl (by omega) hhNB.symm)
  · rw [← hoeq]; exact hoC'
  · -- the kind
    have hc := hqcut
    have hu := hqnu
    cases ho' : esY[C.2.val - 1 + 1].2 with
    | plain r => exact Or.inl ⟨r, rfl⟩
    | clean r b =>
        rw [ho'] at hc
        cases b with
        | false => exact Or.inr ⟨r, rfl⟩
        | true => simp [OmegaY.Official.Classification.Proofs.ChainCorr.cutOrigin] at hc
    | upper r => rw [ho'] at hu; cases hu

theorem pairAbove_plain : CrossPlainPos.PairAbove IsPlain :=
  pairAbove_all _ (fun _ h => Or.inl h)

theorem pairAbove_clean : CrossPlainPos.PairAbove IsClean :=
  pairAbove_all _ (fun _ h => Or.inr h)

end OmegaY.Official.Recon.Pk4

#print axioms OmegaY.Official.Recon.Pk4.copy_rows_eq
#print axioms OmegaY.Official.Recon.Pk4.pairAbove_plain
#print axioms OmegaY.Official.Recon.Pk4.pairAbove_clean
