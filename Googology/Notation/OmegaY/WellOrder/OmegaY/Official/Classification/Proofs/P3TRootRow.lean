/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/P3TRootRow.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.P3TRunTop

set_option backward.do.legacy false

/-!
# `CutJumpRootRow` holds (`P3T`)

`CutJumpRootRow` (`Pkg3Jump.lean`): for a gap copy `u` (block `i = i₀ + 1`, origin
`o = (x, a)`) whose leg is the root column `c_r`, with `pa` the node of `c_r` at the row `a` and
`pe` the highest node of the boundary column `B = c_r + w·i` at or below `row u`, if `pe` is not
at `row u`, then `pe` has a raw parent `q`, and `jump(row pe, row q) < jump(row pa, row b)` for
the raw parent `b` of `pa` (if any).

## The argument

* `root_core` (by induction up the path of `u` in the tree of `x`): let `P` be the plain item
  whose child `c` copies `a` (the root top of the source `S` of `P` is `pa`). Then `B` has nodes
  `q₁ < row u < q₂` in the target `T` of `P`:
  - `q₂`: the top of `B` in `T` lies in a slot above that of `c` (case 2: at `h_ρ + Δ`,
    `LRC.bnd_lift`; case 3: at `h_B`); in the remaining case (level 2) it is at `row u`,
    which is excluded.
  - `q₁`: the copies of `a` below `P` have offset `0` or `1` (the leg of `(x, a)` is `c_r`, one
    generation); an item copying `a` with offset `0` has a node of `B` in its target
    (`LRC.qb_tree`); the lowest one on the path has a child with offset `1`, in the slot
    `h_B + 1`, so the top of `B` there is below `row u`. (At level 1 offset `0` would put a node
    of `B` at `row u`.)
* `jump_of_bnodes`: then the node `pe⁺` above `pe` exists, `pe` and `pe⁺` lie in `T` (level
  `D`), and by the row law `row pe⁺ = bump (row pe) J` with `J = jump(row pe, row q)`, so
  `J + 2 ≤ D`.
* `ja_bound`: `pa` is the top of `c_r` in `S` (level `D`), so the node above it,
  `bump (row pa) J'`, leaves `S`: `D ≤ J' + 1`.

`cutJumpRootRow : CutJumpRootRow` (**proved**, no hypothesis).
-/

namespace OmegaY.Official.Classification.Proofs.P3T

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CutParts


section RootRow
open Recon Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC

theorem jump_of_region {D : Nat} {T a b : Row} (ha : inRegion D T a = true)
    (hb : inRegion D T b = true) : Row.jump a b ≤ D - 1 := by
  apply Row.jump_le_iff.mpr
  intro k hk
  rw [inRegion_iff'.mp ha k hk, inRegion_iff'.mp hb k hk]

theorem jump_official {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b) :
    Row.jump a b = Row.jump (official a) (official b) := by
  rw [← jump_stored (official a) (official b), Classification.stored_official ha,
    Classification.stored_official hb]

/-- **Two nodes of a column around a row, in one region.** If the column `Bc` of the canonical
output has nodes `q1`, `q2` in a region `T` of level `D` below and above the stored row `θs`,
the highest node `pe` of `Bc` at or below `θs` (not at `θs`) has a node above it, whose raw
parent `qq` gives `jump(row pe, row qq) + 2 ≤ D`. -/
theorem jump_of_bnodes {out : List Nat} {R : Mountain} (hcanon : Canonical.build out = .ok R)
    {Bc : Nat} (hBc : 0 < Bc) {θs : Row} {pe : Ref} {cpe : Cell}
    (hpe : highestAtMost R Bc θs = some pe) (hcpe : cell? R pe = some cpe)
    {D : Nat} {T : Row} {q1 q2 : Ref × Cell} (hq1 : q1 ∈ realNodes R Bc)
    (hq2 : q2 ∈ realNodes R Bc) (h1T : inRegion D T (official q1.2.row) = true)
    (h2T : inRegion D T (official q2.2.row) = true) (h1 : q1.2.row ≤ θs) (h2 : θs < q2.2.row) :
    ∃ qq cqq, rawParent R pe = some qq ∧ cell? R qq = some cqq ∧
      Row.jump cpe.row cqq.row + 2 ≤ D := by
  have hV := build_valid_of_success hcanon
  obtain ⟨hpc, hp0, col, hcol, hpi, hprow, hmax⟩ := highestAtMost_spec hpe
  obtain ⟨col1, k1, hc1, hk1, hq1e⟩ := mem_realNodes_iff.mp hq1
  obtain ⟨col2, k2, hc2, hk2, hq2e⟩ := mem_realNodes_iff.mp hq2
  rw [hcol] at hc1 hc2
  cases hc1; cases hc2
  have hcs : Bc < R.size := (Array.getElem?_eq_some_iff.mp hcol).1
  have hCV : ColumnValid R Bc col := by
    have := hV Bc hcs
    have e : R[Bc] = col := (Array.getElem?_eq_some_iff.mp hcol).2
    rw [e] at this; exact this
  obtain ⟨hk1s, hk1e⟩ := Array.getElem?_eq_some_iff.mp hk1
  obtain ⟨hk2s, hk2e⟩ := Array.getElem?_eq_some_iff.mp hk2
  have hcpe' : col[pe.index]? = some cpe := by
    unfold cell? at hcpe; rw [hpc, hcol] at hcpe; simpa using hcpe
  have hcpe2 : col[pe.index] = cpe := by
    rw [Array.getElem?_eq_getElem hpi] at hcpe'; exact Option.some.inj hcpe'
  have hle1 : k1 + 1 ≤ pe.index := hmax (k1 + 1) hk1s (by omega) (by rw [hk1e]; exact h1)
  have hlt2 : pe.index < k2 + 1 := by
    by_contra hn
    have hle : k2 + 1 ≤ pe.index := by omega
    have : q2.2.row ≤ cpe.row := by
      rcases Nat.lt_or_eq_of_le hle with hl | he
      · exact le_of_lt (hCV.rows_strict _ _ _ _ hk2 hcpe' hl)
      · rw [he] at hk2; rw [hk2] at hcpe'; cases hcpe'; exact le_rfl
    rw [hcpe2] at hprow
    exact absurd (lt_of_lt_of_le h2 (le_trans this hprow)) (lt_irrefl _)
  have hus : pe.index + 1 < col.size := by omega
  have hup? : col[pe.index + 1]? = some col[pe.index + 1] := Array.getElem?_eq_getElem hus
  set up := col[pe.index + 1] with hupdef
  have hupc : cell? R (ChainCorr.Inner.up pe) = some up := by
    unfold cell? ChainCorr.Inner.up; rw [hpc, hcol]; simpa using hup?
  obtain ⟨qq, hqq⟩ := hCV.stored_exists (pe.index + 1) up hup? (by omega) hBc
  obtain ⟨cqq, hcqq, _⟩ := ChainCorr.Inner.left_cell hV hupc hqq
  refine ⟨qq, cqq, ChainCorr.Inner.rawParent_eq_some.mpr ⟨up, hupc, hqq⟩, hcqq, ?_⟩
  have hlaw := ChainCorr.Inner.canon_rowLaw hcanon hp0 hcpe hupc hqq hcqq
  -- rows in the column
  have hr1 : q1.2.row ≤ cpe.row := by
    rcases Nat.lt_or_eq_of_le hle1 with hl | he
    · exact le_of_lt (hCV.rows_strict _ _ _ _ hk1 hcpe' hl)
    · rw [he] at hk1; rw [hk1] at hcpe'; cases hcpe'; exact le_rfl
  have hr2 : cpe.row < up.row := hCV.rows_strict _ _ _ _ hcpe' hup? (by omega)
  have hr3 : up.row ≤ q2.2.row := by
    rcases Nat.lt_or_eq_of_le (show pe.index + 1 ≤ k2 + 1 by omega) with hl | he
    · exact le_of_lt (hCV.rows_strict _ _ _ _ hup? hk2 hl)
    · rw [he] at hup?; rw [hup?] at hk2; rw [Option.some.inj hk2]
  have hone1 : (1 : Row) ≤ q1.2.row := realNodes_row_one_le hV hq1
  have hone2 : (1 : Row) ≤ cpe.row := le_trans hone1 hr1
  have hone3 : (1 : Row) ≤ up.row := le_trans hone2 (le_of_lt hr2)
  have hpT : inRegion D T (official cpe.row) = true :=
    CopyShape.ProfileLeg.region_between h1T h2T (official_mono hone1 hr1)
      (official_mono hone2 (le_trans (le_of_lt hr2) hr3))
  have huT : inRegion D T (official up.row) = true :=
    CopyShape.ProfileLeg.region_between h1T h2T (official_mono hone1 (le_trans hr1 (le_of_lt hr2)))
      (official_mono hone3 hr3)
  have hj := jump_of_region hpT huT
  rw [← jump_official hone2 hone3, hlaw, Row.B, Row.jump_bump] at hj
  omega

/-- **The top of a column in a region jumps out of it.** If `pa` is the top of the column in a
region of level `D`, the node above it (row `bump (row pa) J`) has `D ≤ J + 1`. -/
theorem ja_bound {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c D : Nat}
    {S : Row} {pa : Ref} {cpa : Cell} (htop : topIn M c D S = some (pa, cpa)) {b : Ref} {cb : Cell}
    (hpar : rawParent M pa = some b) (hcb : cell? M b = some cb) :
    D ≤ Row.jump cpa.row cb.row + 1 := by
  have hV := build_valid_of_success hb
  obtain ⟨hpm, hpS, hmax⟩ := RowLaw.topIn_spec htop
  obtain ⟨hpc, hp1, hcpa⟩ := Classification.mem_realNodes hpm
  simp only at hpc hp1 hcpa hpS
  obtain ⟨cu, hcu, hl⟩ := ChainCorr.Inner.rawParent_eq_some.mp hpar
  have hlaw := ChainCorr.Inner.canon_rowLaw hb (by omega) hcpa hcu hl hcb
  have hum : (ChainCorr.Inner.up pa, cu) ∈ realNodes M c := by
    have := CopyShape.mem_realNodes_of_cell' hcu (by simp [ChainCorr.Inner.up])
    rw [← hpc]; simpa [ChainCorr.Inner.up] using this
  by_contra hn
  have hj : Row.jump cpa.row cu.row ≤ D - 1 := by
    rw [hlaw, Row.B, Row.jump_bump]; omega
  have hone1 : (1 : Row) ≤ cpa.row := realNodes_row_one_le hV hpm
  have hone2 : (1 : Row) ≤ cu.row := realNodes_row_one_le hV hum
  rw [jump_official hone1 hone2] at hj
  have huS : inRegion D S (official cu.row) = true := by
    rw [inRegion_iff'] at hpS ⊢
    intro k hk
    rw [← Row.coeff_eq_of_jump_le hj hk]
    exact hpS k hk
  have := hmax _ hum huS
  simp [ChainCorr.Inner.up] at this

theorem eq_of_region2 {T x y : Row} (hx : inRegion 2 T x = true) (hy : inRegion 2 T y = true)
    (h0 : x.coeff 0 = y.coeff 0) : x = y := by
  apply Row.ext
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact h0
  · show x.coeff k = y.coeff k
    rw [inRegion_iff'.mp hx k (by omega), inRegion_iff'.mp hy k (by omega)]

/-- The boundary data of the root case, with the gap copy `p` (official row `θ`). -/
def Good (M R : Mountain) (cr Bc : Nat) (a θ : Row) : Prop :=
  ∃ D S T ρr ρc q1 q2, topIn M cr D S = some (ρr, ρc) ∧ official ρc.row = a ∧
    q1 ∈ realNodes R Bc ∧ q2 ∈ realNodes R Bc ∧ inRegion D T (official q1.2.row) = true ∧
    inRegion D T (official q2.2.row) = true ∧ official q1.2.row < θ ∧ θ < official q2.2.row

/-- A node of the boundary column in the target of `A`, below `θ`. -/
def LowB (R : Mountain) (Bc : Nat) (θ : Row) (D : Nat) (A : Item) : Prop :=
  ∃ q ∈ realNodes R Bc, inRegion D A.target (official q.2.row) = true ∧ official q.2.row < θ


theorem kid2_clean {D : Nat} {S T : Row} {blk hR : Nat} {lift : Int} {C : Row}
    {cs : List Item} (hget : ∀ j (hj : j < cs.length), cs[j] = c2 D S T blk hR lift C j)
    {j : Nat} (hj : j < cs.length) {C' : Row} (hcj : cs[j].clean = some C') :
    hR ≤ j ∧ (j : Int) < hR + lift + (if D = 2 then 1 else 0) ∧ cs[j].offset = 0 := by
  rw [hget j hj] at hcj ⊢
  rcases c2_cases (d := D) (S := S) (T := T) (i := blk) (hR := hR) (lift := lift) (C := C) j with
    ⟨_, h2⟩ | ⟨h1, h2, h3⟩ | ⟨_, _, _, h3, _⟩
  · rw [h2] at hcj; simp [k1] at hcj
  · rw [h3]; exact ⟨h1, h2, rfl⟩
  · rw [h3] at hcj; cases hcj

theorem kid3_clean {D : Nat} {S T : Row} {hR hB : Nat} {C : Row}
    {cs : List Item} (hget : ∀ t (ht : t < cs.length), cs[t] = c3 D S T hR hB C (t + hR))
    {j : Nat} (hj : j < cs.length) {C' : Row} (hcj : cs[j].clean = some C') :
    (j : Int) < hB + (if D = 2 then 1 else 0) ∧ cs[j].offset = 0 := by
  rw [hget j hj] at hcj ⊢
  rcases c3_cases (d := D) (S := S) (T := T) (hR := hR) (hB := hB) (C := C) (j + hR) with
    ⟨h1, h2⟩ | ⟨_, h2⟩
  · rw [h2]; refine ⟨by push_cast at h1; omega, rfl⟩
  · rw [h2] at hcj; cases hcj

/-- **The root case, on the item trees.** For a gap copy `p` (origin row `a`, leg `c_r`) in the
copy of the column `x` in block `i₀ + 1`, the boundary column `B` (the copy of `x₀` in block
`i₀`) has nodes below and above `row p` in the target `T` of the plain item `P` that copies the
root row `a` (whose root top, of row `a`, is the top of `c_r` in the source of `P`); unless `B`
has a node at `row p`. -/
theorem root_core {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i0 x : Nat} (hNCx : NewColumn s n R M t root (i0 + 1) x)
    (hNCb : NewColumn s n R M t root i0 (M.size - 1)) {vsB : List (List Emit)}
    (hvsB : LowerRun (colCtx M R root i0 (M.size - 1)) (official t.row) vsB)
    {outsX : List (List (Emit × Origin))}
    (hoX : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root (i0 + 1) x) p.1 p.2) = .ok outsX)
    {p : Emit × Origin} (hp : p ∈ outsX.flatten) {o : Ref} {cθ : Cell}
    (hpo : p.2 = .clean o true) (hu : (o, cθ) ∈ realNodes M x)
    (hnoθ : ∀ b ∈ realNodes R (root.column + (M.size - 1 - root.column) * (i0 + 1)),
      official b.2.row ≠ p.1.row) :
    Good M R root.column (root.column + (M.size - 1 - root.column) * (i0 + 1)) (official cθ.row)
      p.1.row := by
  have rX := hNCx.runCtx
  have hb : Canonical.build s = .ok M := hNCx.top.build
  have hblk : (colCtx M R root (i0 + 1) x).block ≠ 0 := by show i0 + 1 ≠ 0; omega
  obtain ⟨_, _, _, _, hBasic⟩ := Recon.run_basic hNCx.run
  have hVR : MountainValid R := hBasic.valid
  set a := official cθ.row with ha
  set Bc := root.column + (M.size - 1 - root.column) * (i0 + 1) with hBc
  have hcθ : cell? M o = some cθ := (Classification.mem_realNodes hu).2.2
  have hbnd := colCtx_bnd hNCx
  -- the boundary tops of the items with a cut bottom or offset `0`
  have hqb : ∀ d A, InTree (colCtx M R root (i0 + 1) x) (official t.row) d A →
      ((A.clean = none ∧ A.cutBottom = true) ∨ (A.clean ≠ none ∧ A.offset = 0)) →
      ∃ q, topIn R Bc d A.target = some q := by
    intro d A hA hk
    obtain ⟨F, hF, hD⟩ := hA
    have := qb_tree hNCx hNCb hvsB hF (F.1 - d) d A (by have := desc_level_le hD; omega) hD hk
    obtain ⟨em, hem, hin⟩ := this
    exact top_of_lower hNCb hvsB hem hin
  have claim : ∀ d A, InTree (colCtx M R root (i0 + 1) x) (official t.row) (d + 1) A →
      ∀ TA, runItemT (colCtx M R root (i0 + 1) x) (d + 1) A = .ok TA → p ∈ TA →
      Good M R root.column Bc a p.1.row ∨
        (A.clean = some a ∧ (A.offset = 0 → LowB R Bc p.1.row (d + 1) A)) := by
    intro d
    induction d with
    | zero =>
      intro A hA TA hTA hpA
      right
      obtain ⟨C, cs, hC, hn, _, hrow⟩ := levelOne_clean hTA hpA hpo
      obtain ⟨hnm, hnr⟩ := RowLaw.nodeAt_spec hn
      obtain ⟨_, _, hcell⟩ := Classification.mem_realNodes hnm
      have : cs = cθ := Option.some.inj (hcell.symm.trans hcθ)
      subst this
      have hCa : C = a := by rw [← hnr]
      refine ⟨by rw [hC, hCa], fun hoff => ?_⟩
      exfalso
      obtain ⟨q, hq⟩ := hqb 1 A hA (Or.inr ⟨by rw [hC]; simp, hoff⟩)
      obtain ⟨hqm, hqin, _⟩ := RowLaw.topIn_spec hq
      have := Classification.inRegion_one hqin
      exact hnoθ q hqm (by rw [this, hrow])
    | succ d ih =>
      intro A hA TA hTA hpA
      obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children (show runItemT
        (colCtx M R root (i0 + 1) x) (d + 2) A = .ok TA from hTA)
      obtain ⟨hlenF, hgetF⟩ := forall₂_getElem hF
      obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hpA
      obtain ⟨j, hjo, rfl⟩ := List.getElem_of_mem hL'
      have hj : j < cs.length := by omega
      have hcT : InTree (colCtx M R root (i0 + 1) x) (official t.row) (d + 1) cs[j] :=
        LowerLeftProof.inTree_snoc hA hcs (List.getElem_mem hj)
      rcases ih cs[j] hcT outs[j] (hgetF j hj hjo) hpL' with hres | ⟨hcj, hlow⟩
      · exact Or.inl hres
      obtain ⟨ax, hax⟩ : ∃ ax, topIn (colCtx M R root (i0 + 1) x).source
          (colCtx M R root (i0 + 1) x).x (d + 2) A.source = some ax := by
        cases h : topIn (colCtx M R root (i0 + 1) x).source (colCtx M R root (i0 + 1) x).x
          (d + 2) A.source with
        | none =>
          have := childItems_none hcs h
          rw [this] at hj; simp at hj
        | some ax => exact ⟨ax, rfl⟩
      have hct := LowerLeftProof.inTree_cleanTop hA
      obtain ⟨r, cl, hρ, hρa, hascX⟩ := clean_child_root hblk hcs hax hct hj hcj
      have hAOK := (LowerLeftProof.inTree_itemOK rX hA).2
      have hpj : inRegion (d + 1) cs[j].target p.1.row = true :=
        runItemT_region rX (by omega) (LowerLeftProof.inTree_itemOK rX hcT).2 (hgetF j hj hjo) p
          hpL'
      rw [(child_itemOK rX hAOK hcs j hj).2] at hpj
      obtain ⟨hpA2, hpc⟩ := inRegion_slot_iff.mp hpj
      -- a node of `B` in the target of `A` strictly above a slot ends the argument
      have hq2 : ∀ q, topIn R Bc (d + 2) A.target = some q → j < (official q.2.row).coeff d →
          ∃ q2 ∈ realNodes R Bc, inRegion (d + 2) A.target (official q2.2.row) = true ∧
            p.1.row < official q2.2.row := by
        intro q hq hjq
        obtain ⟨hqm, hqin, _⟩ := RowLaw.topIn_spec hq
        exact ⟨q, hqm, hqin, lt_of_coeff_lt hpA2 hqin (by rw [hpc]; exact hjq)⟩
      have hq2eq : d = 0 → ∀ q, topIn R Bc (d + 2) A.target = some q →
          (official q.2.row).coeff d = j → False := by
        intro hd0 q hq hjq
        subst hd0
        obtain ⟨hqm, hqin, _⟩ := RowLaw.topIn_spec hq
        exact hnoθ q hqm (eq_of_region2 hqin hpA2 (by rw [hpc]; exact hjq))
      cases hAcl : A.clean with
      | some C' =>
        right
        obtain ⟨ρ', hρ', hρ'r⟩ := hct C' hAcl
        rw [hρ] at hρ'
        rw [← Option.some.inj hρ'] at hρ'r
        simp only at hρ'r
        have hC'a : C' = a := by rw [← hρ'r, hρa]
        refine ⟨by rw [hC'a], fun hoff => ?_⟩
        by_cases hco : cs[j].offset = 0
        · obtain ⟨q, hqm, hqin, hqlt⟩ := hlow hco
          refine ⟨q, hqm, ?_, hqlt⟩
          rw [(child_itemOK rX hAOK hcs j hj).2] at hqin
          exact (inRegion_slot_iff.mp hqin).1
        · obtain ⟨_, _, _, _, _, _, _, hget⟩ := kids4 hcs hAcl hblk hax hρ hascX
          have hoffj := c4_offset (by rw [← hget j hj, hcj]; simp)
          rw [← hget j hj, hoff] at hoffj
          rw [hoffj] at hco
          obtain ⟨q, hq⟩ := hqb (d + 2) A hA (Or.inr ⟨by rw [hAcl]; simp, hoff⟩)
          obtain ⟨hqm, hqin, _⟩ := RowLaw.topIn_spec hq
          have hBq : heightOf (d + 2) (topIn (colCtx M R root (i0 + 1) x).result
              (colCtx M R root (i0 + 1) x).boundary (d + 2) A.target) =
              (official q.2.row).coeff d := by
            rw [hbnd, hq]; rfl
          rw [hBq] at hco
          have hlt : (official q.2.row).coeff d < j := by omega
          exact ⟨q, hqm, hqin, lt_of_coeff_lt hqin hpA2 (by rw [hpc]; exact hlt)⟩
      | none =>
        left
        -- the child copies `a` with offset `0`: a node of `B` below `p`
        have hoff0 : cs[j].offset = 0 := by
          cases hcb : A.cutBottom with
          | false =>
            obtain ⟨_, hgetX⟩ := kids2 hcs hAcl hcb hax hρ hascX
            exact (kid2_clean hgetX hj hcj).2.2
          | true =>
            obtain ⟨_, hgetX⟩ := kids3 hcs hAcl hcb hblk hax hρ hascX
            exact (kid3_clean hgetX hj hcj).2
        obtain ⟨q1, hq1m, hq1in, hq1lt⟩ := hlow hoff0
        rw [(child_itemOK rX hAOK hcs j hj).2] at hq1in
        have hq1in' := (inRegion_slot_iff.mp hq1in).1
        -- a node of `B` above `p`
        have hup : ∃ q2 ∈ realNodes R Bc, inRegion (d + 2) A.target (official q2.2.row) = true ∧
            p.1.row < official q2.2.row := by
          cases hcb : A.cutBottom with
          | false =>
            obtain ⟨_, hgetX⟩ := kids2 hcs hAcl hcb hax hρ hascX
            obtain ⟨_, hjl, _⟩ := kid2_clean hgetX hj hcj
            obtain ⟨_, hhlt, q, hq, hqc⟩ := bnd_lift hNCx hNCb hA hAcl hcb hax hρ hascX
            have e1 : heightOf (d + 2) (topIn (colCtx M R root (i0 + 1) x).source
                (colCtx M R root (i0 + 1) x).lastColumn (d + 2) A.source) =
                heightOf (d + 2) (topIn M (M.size - 1) (d + 2) A.source) := rfl
            have e2 : ((colCtx M R root (i0 + 1) x).block : Int) = ((i0 + 1 : Nat) : Int) := rfl
            rw [e1, e2] at hjl
            generalize heightOf (d + 2) (topIn M (M.size - 1) (d + 2) A.source) = hk at hjl hhlt hqc
            generalize height (d + 2) (official cl.row) = hR at hjl hhlt hqc
            have e3 : ((hk : Int) - hR) * ((i0 + 1 : Nat) : Int) =
                (((hk - hR) * i0 : Nat) : Int) + ((hk - hR : Nat) : Int) := by
              rw [← Nat.cast_sub (le_of_lt hhlt), ← Nat.cast_mul, ← Nat.cast_add, Nat.mul_add,
                Nat.mul_one]
            rw [e3] at hjl
            generalize (hk - hR) * i0 = P at hjl hqc
            rcases Nat.lt_or_ge j ((official q.2.row).coeff d) with hlt | hge
            · exact hq2 q hq hlt
            · exfalso
              by_cases hd0 : d = 0
              · have hne : j = (official q.2.row).coeff d := by
                  simp only [hd0, if_true] at hjl; omega
                exact hq2eq hd0 q hq hne.symm
              · have hne : d + 2 ≠ 2 := by omega
                simp only [hne, if_false] at hjl
                omega
          | true =>
            obtain ⟨_, hgetX⟩ := kids3 hcs hAcl hcb hblk hax hρ hascX
            obtain ⟨hjB, _⟩ := kid3_clean hgetX hj hcj
            obtain ⟨q, hq⟩ := hqb (d + 2) A hA (Or.inl ⟨hAcl, hcb⟩)
            have hBq : heightOf (d + 2) (topIn (colCtx M R root (i0 + 1) x).result
                (colCtx M R root (i0 + 1) x).boundary (d + 2) A.target) =
                (official q.2.row).coeff d := by
              rw [hbnd, hq]; rfl
            rw [hBq] at hjB
            rcases Nat.lt_or_ge j ((official q.2.row).coeff d) with hlt | hge
            · exact hq2 q hq hlt
            · exfalso
              by_cases hd0 : d = 0
              · have hne : j = (official q.2.row).coeff d := by
                  have hif : (if d + 2 = 2 then (1 : Int) else 0) = 1 := by simp [hd0]
                  rw [hif] at hjB; omega
                exact hq2eq hd0 q hq hne.symm
              · have hne : d + 2 ≠ 2 := by omega
                simp only [hne, if_false] at hjB
                omega
        obtain ⟨q2, hq2m, hq2in, hq2lt⟩ := hup
        exact ⟨d + 2, A.source, A.target, r, cl, q1, q2, hρ, hρa, hq1m, hq2m, hq1in', hq2in,
          hq1lt, hq2lt⟩
  -- the first item holding `p`
  obtain ⟨L, hL, hpL⟩ := List.mem_flatten.mp hp
  obtain ⟨k, hkL, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨hlen, hall⟩ := Classification.mapM_except_spec _ _ _ hoX
  have hk : k < (lowerItems (official t.row)).length := by omega
  have hFm := List.getElem_mem hk
  obtain ⟨_, _, hF1, _⟩ := RowLaw.lower_itemOK (ctx := colCtx M R root (i0 + 1) x) hFm
  obtain ⟨d, hd⟩ : ∃ d, (lowerItems (official t.row))[k].1 = d + 1 :=
    ⟨(lowerItems (official t.row))[k].1 - 1, by omega⟩
  have hT : InTree (colCtx M R root (i0 + 1) x) (official t.row) (d + 1)
      (lowerItems (official t.row))[k].2 := ⟨_, hFm, by rw [← hd]; exact .refl _ _⟩
  have hrun := hall k hk hkL
  rw [hd] at hrun
  rcases claim d _ hT _ hrun hpL with h | ⟨h, _⟩
  · exact h
  · rw [ChainCorr.Inner.lowerItems_clean _ _ hFm] at h
    cases h

end RootRow

open Recon.JumpLaw Recon.JumpLawLower in
/-- The boundary column `c_r + w·(i₀ + 1)`, the copy of `x₀` in block `i₀`, is a new column. -/
theorem boundary_nc {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i0 x : Nat} (hNCx : NewColumn s n R M t root (i0 + 1) x) :
    NewColumn s n R M t root i0 (M.size - 1) := by
  have hcr := hNCx.top.lt
  obtain ⟨hxgt, hxle⟩ := Recon.mem_blockColumns hcr hNCx.mem
  set w := M.size - 1 - root.column with hw
  have hlt : M.size - 1 + w * i0 < R.size := by
    have := hNCx.lt
    have e : w * (i0 + 1) = w * i0 + w := Nat.mul_succ w i0
    rw [e] at this
    omega
  obtain ⟨i', x', hi', hx', hBeq, hcopy⟩ := hNCx.inv.2.2 (M.size - 1 + w * i0) hlt
    (Nat.le_add_right _ _)
  obtain ⟨rfl, rfl⟩ := ChainCorr.block_unique_boundary hcr hx' hBeq
  exact ⟨hNCx.run, hNCx.top, hNCx.copies, hNCx.inv, hi', hx', hlt,
    ⟨_, Array.getElem?_eq_getElem hlt, hcopy⟩⟩

open ChainCorr.Pkg3 Recon Recon.RowLaw Recon.LRC in
/-- **`CutJumpRootRow` holds.** -/
theorem cutJumpRootRow : CutJumpRootRow := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hl hne
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨root, hTop, hcr, hx0, hNCx, hXeq, hctx⟩ := site_nc hS
  obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by have := hS.iPos; omega⟩
  have hNCb := boundary_nc hNCx
  obtain ⟨colB, hcolB, hcopyB⟩ := hNCb.copy
  obtain ⟨vsB, _, hvsB, _, _⟩ := Recon.RowLaw.copyColumn_parts hcopyB
  -- the gap copy
  have ho := origin_clean_of_cut rfl hcut
  obtain ⟨hsrcc, hidx, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hup : es[j].2.isUpper = false := by rw [ho]; rfl
  rw [hup] at hsrcc
  simp only [Bool.false_eq_true, if_false] at hsrcc
  change es[j].2.src.column = x at hsrcc
  have hesX := hS.emits
  rw [← hctx] at hesX
  obtain ⟨outsX, usX, hoX, hesXe, hupX⟩ := lower_of_emits hesX
  have hpX : es[j] ∈ outsX.flatten := by
    have hm : es[j] ∈ outsX.flatten ++ usX := by rw [← hesXe]; exact List.getElem_mem hj
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exact absurd (hupX _ h) (by rw [hup]; simp)
  have hsrcx : (es[j].2.src, cv) ∈ realNodes M x := by
    have := CopyShape.mem_realNodes_of_cell' hL.hcv hidx
    rw [hsrcc] at this
    exact this
  -- the row of the gap copy
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨c1, hc1, hr1⟩ := hcellsX j hj
  have hcu1 : cu = c1 := Option.some.inj (hL.hcu.symm.trans hc1)
  subst hcu1
  -- the leg column is the boundary column
  have himg := leg_image hS hj hL
  rw [hl, mapColumn_of_ge (le_refl _), hcr, hx0] at himg
  have hpe := hL.hpe
  rw [himg] at hpe
  obtain ⟨hpecol, hpe0, _⟩ := highestAtMost_spec hpe
  -- `B` has no node at the row of the gap copy
  have hnoθ : ∀ b ∈ realNodes R (root.column + (M.size - 1 - root.column) * (i0 + 1)),
      official b.2.row ≠ es[j].1.row := by
    intro b hb hbθ
    have hb1 := realNodes_row_one_le hVR hb
    have hbrow : b.2.row = cu.row := by
      rw [hr1, ← hbθ, Classification.stored_official hb1]
    obtain ⟨hbc, hbi, hbcell⟩ := Classification.mem_realNodes hb
    obtain ⟨_, _, colP, hcolP, hpi, hprow, hmax⟩ := highestAtMost_spec hpe
    have hpm : (pe, cpe) ∈ realNodes R (root.column + (M.size - 1 - root.column) * (i0 + 1)) := by
      have := CopyShape.mem_realNodes_of_cell' hL.hcpe (by omega)
      rw [hpecol] at this; exact this
    obtain ⟨col', k', hc', hk', hbe⟩ := mem_realNodes_iff.mp hb
    rw [hcolP] at hc'; cases hc'
    have hkle : k' + 1 ≤ pe.index :=
      hmax (k' + 1) (Array.getElem?_eq_some_iff.mp hk').1 (by omega)
        (by rw [(Array.getElem?_eq_some_iff.mp hk').2, hbrow])
    have h1 : b.2.row ≤ cpe.row := by
      have := CopyShape.MHProof.row_le_of_index hVR hb hpm (by rw [hbe]; exact hkle)
      exact this
    have h2 : cpe.row ≤ cu.row := ChainCorr.Pkg3.hAM_row_le hpe hL.hcpe
    exact hne (le_antisymm h2 (hbrow ▸ h1))
  obtain ⟨D', S, T, ρr, ρc, q1, q2, hρ, hρa, hq1m, hq2m, hq1T, hq2T, hq1lt, hq2lt⟩ :=
    root_core hNCx hNCb hvsB hoX hpX ho hsrcx hnoθ
  -- the root top is `pa`
  have hparow := cutPaRow s n D M out ρ R t X x (i0 + 1) es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  obtain ⟨hpacol, hpa0, _⟩ := highestAtMost_spec hL.hpa
  have hpam : (pa, cpa) ∈ realNodes M root.column := by
    have := CopyShape.mem_realNodes_of_cell' hL.hcpa hpa0
    rw [hpacol, hl, hcr] at this; exact this
  obtain ⟨hρm, _, _⟩ := RowLaw.topIn_spec hρ
  have hρpa : (ρr, ρc) = (pa, cpa) :=
    ChainCorr.realNodes_eq_of_official hV hρm hpam (by rw [hρa, hparow])
  rw [hρpa] at hρ
  -- the two jumps
  have hBc : 0 < root.column + (M.size - 1 - root.column) * (i0 + 1) := by
    have := hTop.lt
    have : 0 < (M.size - 1 - root.column) * (i0 + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have h1 : q1.2.row ≤ cu.row := by
    rw [hr1, ← Classification.stored_official (realNodes_row_one_le hVR hq1m)]
    exact le_of_lt (stored_lt_iff.mpr hq1lt)
  have h2 : cu.row < q2.2.row := by
    rw [hr1, ← Classification.stored_official (realNodes_row_one_le hVR hq2m)]
    exact stored_lt_iff.mpr hq2lt
  obtain ⟨qq, cqq, hqq, hcqq, hJe⟩ := jump_of_bnodes hS.canon hBc hpe hL.hcpe hq1m hq2m hq1T hq2T
    h1 h2
  refine ⟨qq, cqq, hqq, hcqq, fun b cb hpb hcb => ?_⟩
  have hJa := ja_bound hS.splice.build hρ hpb hcb
  omega


end OmegaY.Official.Classification.Proofs.P3T

#print axioms OmegaY.Official.Classification.Proofs.P3T.cutJumpRootRow
