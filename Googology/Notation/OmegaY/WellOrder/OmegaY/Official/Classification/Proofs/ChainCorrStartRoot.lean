/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrStartRoot.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartCopy

set_option backward.do.legacy false

/-!
# `StartRoot` from the chains of the boundary columns

`StartRoot` (`ChainCorrRegions.lean`) asks: for a node `u` of block `i ≥ 1` whose origin
`o = (x, σ)` is not a gap copy and whose leg is the root column `cr`, the highest node `pe`
of the boundary column `B = cr + w·i` at or below the row of `u` has a scale-`k` chain that
reaches `m''` whenever `pa → m''` is a step of the scale-`k` chain of `M(s)`; here `pa` is
the highest node of `cr` at or below `σ` and `k ≥ jump(σ, row pa)`.

The boundary column `B = x₀ + w·(i - 1)` is the copy of the column `x₀` made by block
`i - 1` (block `0` for `i = 1`). Its nodes have origins: nodes of `x₀` below the top row
`τ` (the lower part) and nodes of `cr` at or above `τ` (the upper part). The numerical
tests (`reference/official/startcopy-root-parts.cjs`) split `StartRoot` in two:

* `BoundaryChain`: the scale-`k` chain of a node `b` of `B` reaches every node left of `cr`
  that the scale-`k` chain of its origin reaches in `M(s)`. (The output chain from `b`
  passes through the copies of block `i - 1` and the earlier boundary columns; it follows
  the chain of `M(s)` from the origin as far as the columns left of `cr`.)
* `OriginReach`: the scale-`k` chain of `M(s)` from the origin of `pe` reaches `m''`.

`startRoot_of_parts` proves `StartRoot` from the two statements.

## Numerical tests

`reference/official/startcopy-root-parts.cjs` (counts: node-scale-target triples for
`BoundaryChain`, node-scale pairs for `OriginReach`):

| sample | `BoundaryChain` | `OriginReach` | failures |
|---|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 7327810 | 1223562 | 0 |
| legal, length ≤ 6, entries ≤ 6 | 174480 | 91188 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 121668 | 57897 | 0 |
| random legal (`--random 20000,10,10,7`) | 637050 | 315585 | 0 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs

/-! ## The statements -/

/-- (open) The chain of a node of the boundary column `x₀ + w·(i - 1)` follows the chain of
its origin as far as the columns left of `cr`. -/
def BoundaryChain : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length) kk (m : Ref), m.column < ρ.cr →
        ScaleReach M kk esB[k].2.src m →
        ScaleReach R kk ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k + 1⟩ m

/-- (open) The chain of `M(s)` from the origin of `pe` reaches the next node of the chain of
`pa`. -/
def OriginReach : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr →
      ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), pe.index = k + 1 →
      ∀ kk m'', Row.jump cv.row cpa.row ≤ kk → MStep M kk pa m'' →
        ScaleReach M kk esB[k].2.src m''

/-! ## The reduction -/

/-- The column `x₀ + w·m` is produced only by block `m` from `x₀`. -/
theorem block_unique_boundary {cr x0 n m i' x' : Nat} (hcr : cr < x0)
    (hx' : x' ∈ blockColumns cr x0 n i') (heq : x0 + (x0 - cr) * m = x' + (x0 - cr) * i') :
    i' = m ∧ x' = x0 := by
  have hw : 0 < x0 - cr := by omega
  have hx'le : x' ≤ x0 ∧ (0 < i' → cr < x') := by
    unfold blockColumns at hx'
    split at hx'
    · simp only [List.mem_singleton] at hx'
      exact ⟨by omega, fun h => by omega⟩
    · simp only [List.mem_range'_1] at hx'
      exact ⟨by split at hx' <;> omega, fun _ => by omega⟩
  rcases Nat.lt_trichotomy i' m with h | h | h
  · obtain ⟨d, rfl⟩ : ∃ d, m = i' + d + 1 := ⟨m - i' - 1, by omega⟩
    have h1 : (x0 - cr) * (i' + d + 1) = (x0 - cr) * i' + (x0 - cr) * (d + 1) := by
      rw [show i' + d + 1 = i' + (d + 1) by omega, Nat.mul_add]
    have h2 : x0 - cr ≤ (x0 - cr) * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · subst h
    exact ⟨rfl, by omega⟩
  · obtain ⟨d, rfl⟩ : ∃ d, i' = m + d + 1 := ⟨i' - m - 1, by omega⟩
    have h1 : (x0 - cr) * (m + d + 1) = (x0 - cr) * m + (x0 - cr) * (d + 1) := by
      rw [show m + d + 1 = m + (d + 1) by omega, Nat.mul_add]
    have h2 : x0 - cr ≤ (x0 - cr) * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have := hx'le.2 (by omega)
    omega

/-- The boundary column of block `i ≥ 1`: `cr + w·i = x₀ + w·(i - 1)`. -/
theorem boundary_eq {cr x0 i : Nat} (hcr : cr < x0) (hi : 0 < i) :
    cr + (x0 - cr) * i = x0 + (x0 - cr) * (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [Nat.mul_succ, Nat.add_sub_cancel]
  omega

/-- **`StartRoot` from the chains of the boundary columns.** -/
theorem startRoot_of_parts (hB : BoundaryChain) (hO : OriginReach) : StartRoot := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq kk m'' hk hst
  have hdat := hS.data
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  have hipos := hS.iPos
  -- the leg column is the boundary column `B`
  have himg := leg_image hS hj hL
  rw [heq, mapColumn_of_ge (le_refl _), boundary_eq hcrx hipos] at himg
  obtain ⟨hpecol, hpe0, colB, hcolB, hpeB, _, _⟩ := highestAtMost_spec hL.hpe
  obtain ⟨hBsz, _⟩ := column_of_getElem? hcolB
  have hB0 : ρ.x0 ≤ ref.column := by rw [himg]; omega
  obtain ⟨i', x', hi', hx', hBeq, hcopyB⟩ := hinv.2.2 ref.column hBsz hB0
  obtain ⟨hii, hxx⟩ := block_unique_boundary hcrx hx' (by rw [← himg]; exact hBeq)
  subst i' x'
  have hcolB' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hBsz
  have hcc : colB = R[ref.column] := Option.some.inj (hcolB.symm.trans hcolB')
  obtain ⟨esB, hesB, _⟩ := copyColumn_emitsT hcopyB
  obtain ⟨hszB, _⟩ := cells_of_copy hcolB' hcopyB hesB
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB := by
    have h' : ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) = ref.column := himg.symm
    simp only [blockEmits, h']
    exact hesB
  have hksl : pe.index - 1 < esB.length := by
    have : pe.index < colB.size := hpeB
    rw [hcc, hszB] at this
    omega
  have hpeidx : pe.index = pe.index - 1 + 1 := by omega
  -- the origin of `pe` reaches `m''`, and `m''` is left of `cr`
  have hreachM := hO s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB
    hbl (pe.index - 1) hksl hpeidx kk m'' hk hst
  have hpacol : pa.column = ρ.cr := by
    rw [(highestAtMost_spec hL.hpa).1, heq]
  have hm'' : m''.column < ρ.cr := hpacol ▸ hst.column_lt
  have hreachR := hB s n D M out ρ R t hdat i hipos hS.iLt esB hbl (pe.index - 1) hksl kk m''
    hm'' hreachM
  have hpe : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), pe.index - 1 + 1⟩ :=
    ref_eq_of (by rw [hpecol, himg]) hpeidx
  rw [hpe]
  exact hreachR

end OmegaY.Official.Classification.Proofs.ChainCorr

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.startRoot_of_parts
