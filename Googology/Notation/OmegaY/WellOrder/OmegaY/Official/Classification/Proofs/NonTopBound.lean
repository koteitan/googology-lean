/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/NonTopBound.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsB0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerBndRows

set_option backward.do.legacy false

/-!
# The boundary columns at a copied root row (`NonTopBound.lean`)

Let `C` be the row of a clean copy (`b = 0`): a row of the root column `c_r` that is the root
top of its level-2 region, inside a first item of level `≥ 2` (`CleanRowOK`, from
`CutGap.emitsT_cleanTop`). Let `P_i` be the node of the boundary column `c_r + w·i` at the row `C`
and `g = (c_r, C)`.

* `boundary_emit`: the emit of `P_{i'+1}` in the copy of `x₀` in block `i'` is a non-cut copy of
  the node `(x₀, C)`, and for `i' ≥ 1` it is the clean copy (`b = 0`) of `(x₀, C)`
  (`rootCmp`, `emitsT_upperRow`, `emitsT_plainAsc`, and `x₀` ascends: `LowerBndSrc.x0_ascends`).
* `walkX`: from a clean copy `v` of `a` in block `i ≥ 1` the output chain at scale `0` (at the row
  of `v`) passes the clean copies of the nodes of the generation chain of `a` right of `c_r` and
  ends at `P_i` (`cleanStepX`).
* **`boundRoot`**: every step `g → m''` of `M(s)` at scale `k` is reached by the scale-`k` chain of
  the output from `P_i`. Block `1`: `SRParts.boundaryChain_one` with `SRX0.x0Reach`; block
  `i + 1`: `P_{i+1}` is a clean copy of `(x₀, C)` in block `i`, whose walk ends at `P_i`.

All declarations are in the namespace `ChainCorr.NonTop`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner ChainCorr.Inner.Clean ChainCorr.Inner.CleanRoot

/-! ## Copied root rows -/

/-- `C` is a copied root row: it lies in a first item of level `≥ 2` and it is the row of the
root top of its level-2 region. -/
def CleanRowOK (M : Mountain) (cr : Nat) (τ C : Row) : Prop :=
  (∃ q ∈ lowerItems τ, 2 ≤ q.1 ∧ inRegion q.1 q.2.source C = true) ∧
  ∃ ρr ρc, topIn M cr 2 C = some (ρr, ρc) ∧ official ρc.row = C

theorem CleanRowOK.lt {M : Mountain} {cr : Nat} {τ C : Row} (h : CleanRowOK M cr τ C) : C < τ := by
  obtain ⟨⟨q, hq, _, hin⟩, _⟩ := h
  exact (lowerItems_below τ _ hq).1 _ hin

theorem CleanRowOK.rootRow {M : Mountain} {cr : Nat} {τ C : Row} (h : CleanRowOK M cr τ C) :
    SRCmp.RootRow M cr C := by
  obtain ⟨_, ρr, ρc, hρ, hρrow⟩ := h
  exact ⟨(ρr, ρc), (topIn_spec hρ).1, hρrow⟩

/-- The row of a clean copy is a copied root row. -/
theorem cleanRowOK_of_emit {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {p : Emit × Origin} (hp : p ∈ es) {r : Ref} {b : Bool}
    (hpr : p.2 = .clean r b) {c0 : Cell} (hc0 : cell? ctx.source r = some c0) :
    CleanRowOK ctx.source ctx.rootColumn τ (official c0.row) :=
  CutGap.emitsT_cleanTop h p hp r b hpr c0 hc0

/-! ## The copies of the last column -/

/-- The copy of `x₀` in a block `m < n` has emits. -/
theorem boundary_emits {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n) :
    ∃ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB := by
  obtain ⟨_, hcrx, hinv, hRs⟩ := SRParts.spliceData_facts hd
  have hXR : ρ.x0 + (ρ.x0 - ρ.cr) * m < R.size := by
    rw [hRs]
    have : (ρ.x0 - ρ.cr) * m < n * (ρ.x0 - ρ.cr) := by
      rw [Nat.mul_comm n]; exact Nat.mul_lt_mul_of_pos_left hm (by omega)
    omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 _ hXR (by omega)
  obtain ⟨hii, hxx⟩ := block_unique_boundary hcrx hx' hXeq
  subst hii hxx
  obtain ⟨es, hes, _⟩ := copyColumn_emitsT hcopy
  exact ⟨es, hes⟩

/-- `x₀` is a column of block `m < n`. -/
theorem x0_mem_block {cr x0 n m : Nat} (hcr : cr < x0) (hm : m < n) :
    x0 ∈ blockColumns cr x0 n m := by
  unfold blockColumns
  split
  · simp
  · simp only [List.mem_range'_1]
    omega

/-- **The emit of a copy of `x₀` at a copied root row `C`** is a non-cut copy of the node
`(x₀, C)`; in a block `m ≥ 1` it is the clean copy (`b = 0`) of that node. -/
theorem boundary_emit {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) {C : Row} (hC : CleanRowOK M ρ.cr (official t.row) C)
    (hrow : esB[k].1.row = C) :
    ∃ (a : Ref) (ca : Cell), cell? M a = some ca ∧ a.column = ρ.x0 ∧ 1 ≤ a.index ∧
      official ca.row = C ∧ esB[k].2.src = a ∧ cutOrigin esB[k].2 = false ∧
      (0 < m → esB[k].2 = .clean a false) := by
  obtain ⟨_, hcrx, _, _⟩ := SRParts.spliceData_facts hd
  obtain ⟨hsc, hsi, cv, hcv, _⟩ := SRParts.bsrc hes hk
  have hes' : emitsT (ctxAt M R ρ.x0 m ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (ρ.x0 + (ρ.x0 - ρ.cr) * m))
      (official t.row) = .ok esB := hes
  have hcmp := SRCmp.rootCmp s n D M out ρ R t hd m (by omega) ρ.x0 (x0_mem_block hcrx hm) esB hes
    esB[k] (List.getElem_mem hk) cv hcv C hC.rootRow
  have hCτ := hC.lt
  -- not a gap copy
  have hnc : cutOrigin esB[k].2 = false := by
    cases hco : cutOrigin esB[k].2
    · rfl
    · exfalso
      obtain ⟨h1, h2⟩ := hcmp.2 hco
      rw [hrow] at h1 h2
      rcases le_or_gt C (official cv.row) with hle | hlt
      · exact lt_irrefl _ (h1 hle)
      · exact lt_irrefl _ (h2 hlt)
  obtain ⟨h1, _, h3⟩ := hcmp.1 hnc
  rw [hrow] at h1 h3
  have hcrow : official cv.row = C := by
    rcases lt_trichotomy C (official cv.row) with hlt | heq | hgt
    · exact absurd (h1 hlt) (lt_irrefl _)
    · exact heq.symm
    · exact absurd (h3 hgt) (lt_irrefl _)
  -- not an upper copy
  have hnu : esB[k].2.isUpper = false := by
    cases hu : esB[k].2 with
    | upper r =>
        exfalso
        have hcr : cell? M r = some cv := by
          have : esB[k].2.src = r := by rw [hu]; rfl
          rw [← this]; exact hcv
        have := CutGap.emitsT_upperRow hes' esB[k] (List.getElem_mem hk) r hu cv
          (by simp only [ctxAt]; exact hcr)
        rw [hcrow] at this
        exact absurd hCτ (not_lt.mpr this)
    | plain r => rfl
    | clean r b => rfl
  rw [hnu] at hsc
  simp only [Bool.false_eq_true, if_false] at hsc
  refine ⟨esB[k].2.src, cv, hcv, hsc, hsi, hcrow, rfl, hnc, fun hm0 => ?_⟩
  -- not a plain copy in a block `m ≥ 1`
  cases hE : esB[k].2 with
  | upper r => rw [hE] at hnu; cases hnu
  | clean r b =>
      cases b
      · rfl
      · rw [hE] at hnc; cases hnc
  | plain r =>
      exfalso
      have hcv' : cell? M r = some cv := by
        have : esB[k].2.src = r := by rw [hE]; rfl
        rw [← this]; exact hcv
      obtain ⟨⟨qx, hqx, hqx2, hqxin⟩, ρr, ρc, hρ, hρrow⟩ := hC
      rcases CutGap.emitsT_plainAsc hes' esB[k] (List.getElem_mem hk) r hE cv
          (by simp only [ctxAt]; exact hcv') with ⟨q1, hq1, hq11, hq1in⟩ | hP
      · have hq1in' : inRegion q1.1 q1.2.source C = true := by rw [← hcrow]; exact hq1in
        have := Recon.JumpLaw.lowerItems_eq_of_common hqx hq1 hqxin hq1in'
        rw [this] at hqx2
        omega
      · obtain ⟨root, hTop, hroot, hx0⟩ := SRParts.data_top hd
        have hρ' : topIn M ρ.cr 2 (official cv.row) = some (ρr, ρc) := by rw [hcrow]; exact hρ
        have hf := hP r hE cv (by simp only [ctxAt]; exact hcv') ρr ρc
          (by simp only [ctxAt]; exact hρ') (by rw [hcrow]; exact hρrow)
        have ht := LowerBndSrc.x0_ascends hTop
          (ctx := ctxAt M R ρ.x0 m ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (ρ.x0 + (ρ.x0 - ρ.cr) * m))
          (by simp [ctxAt]) (by simp [ctxAt]; omega) (by simp [ctxAt]; omega)
          (ρ := (ρr, ρc)) (by rw [hroot]; exact (topIn_spec hρ).1) (by rw [hρrow]; exact hCτ)
        rw [ht] at hf
        cases hf

/-! ## The walk along the generation chain -/

/-- The source of a clean copy is right of `c_r` and a real node. -/
theorem cleanX_src {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v a : Ref} {b : Bool}
    (h : CopyAtX M R n cr x0 τ i v (.clean a b)) :
    cr < a.column ∧ 1 ≤ a.index ∧ ∃ ca, cell? M a = some ca := by
  obtain ⟨y, es, j, hcy, _, _, _, _, hes, hj, ho⟩ := h
  obtain ⟨hcol, hidx, c, hc, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [ho] at hcol hidx hc
  simp only [Origin.isUpper, Bool.false_eq_true, if_false, Origin.src, ctxAt] at hcol hidx hc
  exact ⟨by omega, hidx, c, hc⟩

/-- No generation step starts at or left of `c_r`. -/
theorem genChain_stop {M : Mountain} {cr : Nat} {b g : Ref} (hb : b.column ≤ cr)
    (h : Relation.ReflTransGen (GenStep M cr) b g) : g = b := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hbc, _⟩
  · rfl
  · exact absurd hbc.1 (by omega)

/-- **The walk from a clean copy.** From a clean copy `v` of `a` in block `i ≥ 1`, the output chain
at scale `0` reaches the clean copy of every node of the generation chain of `a` right of `c_r`,
and a node `P` of the boundary column `c_r + w·i` at the row of `v` when the chain reaches the
root column; the chain does reach it. -/
theorem walkX {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) :
    ∀ (x : Nat) (v a : Ref), a.column = x →
      CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∃ cv, cell? R v = some cv ∧
        (∃ g, Relation.TransGen (GenStep M ρ.cr) a g ∧ g.column = ρ.cr) ∧
        ∀ g', Relation.ReflTransGen (GenStep M ρ.cr) a g' → ρ.cr ≤ g'.column ∧
          (ρ.cr < g'.column → ∃ v', ScaleReach R 0 v v' ∧
            CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v' (.clean g' false)) ∧
          (g'.column = ρ.cr → ∃ (P : Ref) (cP : Cell), ScaleReach R 0 v P ∧
            P.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧ cell? R P = some cP ∧ cP.row = cv.row) := by
  have hV := build_valid_of_success hS.splice.build
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  intro v a hax hva
  obtain ⟨hacr, _, _⟩ := cleanX_src hva
  obtain ⟨b, v1, cv, c1, hab, hbcr, hraw, hcv, hc1, hrow, hlt, hin, hbd⟩ := cleanStepX hS hi0 hi hva
  have hstep : ScaleReach R 0 v v1 :=
    ScaleReach.step hraw hcv hc1 (by rw [hrow, Row.jump_self]) hlt (ScaleReach.refl v1)
  have hba : b.column < a.column := by
    obtain ⟨_, _, ca, cb, l, hca, hl, hbl, _, _⟩ := hab
    rw [hbl]; exact left_lt_of_valid hV hca hl
  -- the node `a` itself
  have hself : ρ.cr ≤ a.column ∧
      (ρ.cr < a.column → ∃ v', ScaleReach R 0 v v' ∧
        CopyAtX M R n ρ.cr ρ.x0 (official t.row) i v' (.clean a false)) ∧
      (a.column = ρ.cr → ∃ (P : Ref) (cP : Cell), ScaleReach R 0 v P ∧
        P.column = ρ.cr + (ρ.x0 - ρ.cr) * i ∧ cell? R P = some cP ∧ cP.row = cv.row) :=
    ⟨le_of_lt hacr, fun _ => ⟨v, ScaleReach.refl v, hva⟩, fun h => absurd h (by omega)⟩
  rcases Nat.lt_or_eq_of_le hbcr with hbgt | hbeq
  · -- the next generation is right of `c_r`: continue from its clean copy
    have hv1 := copyAtX_of_copyAt (hin hbgt)
    obtain ⟨cv1, hcv1, ⟨g, hbg, hgc⟩, hall⟩ := ih b.column (by omega) v1 b rfl hv1
    have e : cv1 = c1 := Option.some.inj (hcv1.symm.trans hc1)
    subst e
    refine ⟨cv, hcv, ⟨g, Relation.TransGen.head hab hbg, hgc⟩, fun g' hg' => ?_⟩
    rcases Relation.ReflTransGen.cases_head hg' with rfl | ⟨b', hab', hb'g'⟩
    · exact hself
    · have e2 : b' = b := GenStep.unique hV hab' hab
      subst e2
      obtain ⟨h1, h2, h3⟩ := hall g' hb'g'
      refine ⟨h1, fun h => ?_, fun h => ?_⟩
      · obtain ⟨v', hr, hc⟩ := h2 h
        exact ⟨v', ScaleReach.trans hstep hr, hc⟩
      · obtain ⟨P, cP, hr, hPc, hcP, hProw⟩ := h3 h
        exact ⟨P, cP, ScaleReach.trans hstep hr, hPc, hcP, by rw [hProw, hrow]⟩
  · -- the next generation is in the root column: `v₁` is the boundary node
    refine ⟨cv, hcv, ⟨b, Relation.TransGen.single hab, hbeq.symm⟩, fun g' hg' => ?_⟩
    rcases Relation.ReflTransGen.cases_head hg' with rfl | ⟨b', hab', hb'g'⟩
    · exact hself
    · have e2 : b' = b := GenStep.unique hV hab' hab
      subst e2
      have e3 := genChain_stop (le_of_eq hbeq.symm) hb'g'
      subst e3
      refine ⟨le_of_eq hbeq, fun h => absurd h (by omega), fun _ => ?_⟩
      exact ⟨v1, c1, hstep, hbd hbeq.symm, hc1, hrow⟩

/-! ## The boundary nodes at a copied root row -/

/-- A real node of the boundary column `c_r + w·i` is the cell of an emit of the copy of `x₀` in
block `i - 1`. -/
theorem boundary_node {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {P : Ref}
    {cP : Cell} (hPc : P.column = ρ.cr + (ρ.x0 - ρ.cr) * i) (hcP : cell? R P = some cP)
    (h1 : (1 : Row) ≤ cP.row) :
    ∃ esB k, ∃ hk : k < esB.length,
      blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB ∧
      P = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k + 1⟩ ∧ esB[k].1.row = official cP.row := by
  have hd := CopyShape.spliceData_of_setting hS
  have hVR := build_valid_of_success hS.canon
  obtain ⟨_, hcrx, _, _⟩ := SRParts.spliceData_facts hd
  obtain ⟨esB, hes⟩ := boundary_emits hd (m := i - 1) (by omega)
  obtain ⟨_, c, hcX, _, hsz, hcells⟩ := SRParts.bcol hd (by omega) hes
  have hP0 := CutParts.index_pos_of_one_le hVR hcP h1
  have hPX : P.column = ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) := by
    rw [hPc]; exact boundary_eq hcrx hi0
  have h2 : c[P.index]? = some cP := by
    unfold cell? at hcP
    rw [hPX, hcX] at hcP
    simpa using hcP
  have hlt : P.index < c.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at h2
    cases h2
  have hk : P.index - 1 < esB.length := by omega
  obtain ⟨cell, hcell, hcrow, _⟩ := hcells (P.index - 1) hk
  have hPeq : P = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), P.index - 1 + 1⟩ :=
    ChainCorr.ref_eq_of hPX (by simp only; omega)
  refine ⟨esB, P.index - 1, hk, hes, hPeq, ?_⟩
  rw [hPeq] at hcP
  have e : cell = cP := Option.some.inj (hcell.symm.trans hcP)
  subst e
  rw [hcrow, Recon.JumpLaw.official_stored]

/-- **The boundary node at a copied root row follows the step of the root node.** Let `P` be a
node of the boundary column `c_r + w·i` (`1 ≤ i ≤ n`) and `g` the node of the root column at the
same row `C`, a copied root row. Every step `g → m''` of `M(s)` at a scale `kk` is reached by the
scale-`kk` chain of the output from `P`. -/
theorem boundRoot {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) :
    ∀ i, 0 < i → i < n + 1 → ∀ (P g : Ref) (cP cg : Cell),
      P.column = ρ.cr + (ρ.x0 - ρ.cr) * i → cell? R P = some cP →
      g.column = ρ.cr → 1 ≤ g.index → cell? M g = some cg → cP.row = cg.row →
      CleanRowOK M ρ.cr (official t.row) (official cg.row) →
      ∀ kk m'', MStep M kk g m'' → ScaleReach R kk P m'' := by
  have hd := CopyShape.spliceData_of_setting hS
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, hcrx, _, _⟩ := SRParts.spliceData_facts hd
  obtain ⟨root, hTop, hroot, hx0⟩ := top_of_setting hS
  intro i
  induction i with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hi P g cP cg hPc hcP hgc hg1 hcg hrow hC kk m'' hst
    have hcg1 : (1 : Row) ≤ cg.row := one_le_row hV hcg hg1
    have h1 : (1 : Row) ≤ cP.row := by rw [hrow]; exact hcg1
    obtain ⟨esB, k, hk, hes, hPeq, herow⟩ := boundary_node hS (i := m + 1) (by omega) hi hPc hcP h1
    simp only [Nat.add_sub_cancel] at hes hPeq
    have herow' : esB[k].1.row = official cg.row := by rw [herow, hrow]
    obtain ⟨a, ca, hca, hac, ha1, hcaC, hsrc, _, hcl⟩ :=
      boundary_emit hd (m := m) (by omega) hes hk hC herow'
    have hcaeq : ca.row = cg.row :=
      official_inj' (one_le_row hV hca ha1) hcg1 hcaC
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      -- block `1`: the copy of `x₀` in block `0`
      have hmc : m''.column < ρ.cr := by rw [← hgc]; exact hst.column_lt
      have hhAM : highestAtMost M root.column ca.row = some g := by
        rw [hcaeq, hroot, ← hgc]; exact hAM_self hV (by omega) hcg
      have hlt : ca.row < t.row := by
        apply row_lt_of_official hTop.row_one_le
        rw [hcaC]; exact hC.lt
      have hr := SRX0.x0Reach s M t root hTop a ca (by rw [hac, hx0]) ha1 hca hlt g hhAM kk m'' hst
      rw [← hsrc] at hr
      have := SRParts.boundaryChain_one hd hes hk hmc hr
      rw [hPeq]
      exact this
    · -- block `m + 1 ≥ 2`: `P` is the clean copy of `(x₀, C)` in block `m`
      have hclean := hcl hmpos
      have hPX : CopyAtX M R n ρ.cr ρ.x0 (official t.row) m P (.clean a false) :=
        ⟨ρ.x0, esB, k, hcrx, le_refl _, x0_mem_block hcrx (by omega), by rw [hPeq],
          by rw [hPeq], by rw [hPeq]; exact hes, hk, hclean⟩
      obtain ⟨cv, hcv, ⟨g0, hag0, hg0c⟩, hall⟩ :=
        walkX hS hmpos (by omega) a.column P a rfl hPX
      obtain ⟨_, _, h3⟩ := hall g0 hag0.to_reflTransGen
      obtain ⟨P', cP', hr, hP'c, hcP', hP'row⟩ := h3 hg0c
      have e : cv = cP := Option.some.inj (hcv.symm.trans hcP)
      subst e
      have := ih hmpos (by omega) P' g cP' cg hP'c hcP' hgc hg1 hcg (by rw [hP'row, hrow]) hC kk
        m'' hst
      exact ScaleReach.trans (reach_mono hr (Nat.zero_le _)) this

end OmegaY.Official.Classification.Proofs.ChainCorr.NonTop

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.boundary_emit
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.walkX
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.NonTop.boundRoot

