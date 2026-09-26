/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsOriginLower.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsOrigin
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCopyMono

set_option backward.do.legacy false

/-!
# `OriginLower` from a lookup and a fact about `M(s)`

`OriginLower` (`StartRootPartsOrigin.lean`) is `OriginReach` when the origin `ν` of `pe` is a
node of the lower part of `x₀`. The numerical tests split it in two:

* `PaLookup` (about the rule): `pa`, the highest node of `cr` at or below the row `σ` of the
  origin of `u`, is also the highest node of `cr` at or below the row of `ν`.
* `X0Reach` (about `M(s)` only): for a node `ν` of the last column `x₀` below its top `t`, and
  `q` the highest node of the root column at or below the row of `ν`, the scale-`k` chain of
  `ν` reaches the next node `m''` of the scale-`k` chain of `q`, at every scale `k` where `q`
  has a step.

The origin of a lower emit is below `τ` (`CopyMonoProof.lowerT_mono`), so `ν` is below `t`.

`originLower_of_parts`: `OriginLower` from `PaLookup` and `X0Reach`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- (open) The highest node of `cr` at or below the row of the origin of `pe` is `pa`. -/
def PaLookup : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr →
      ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), pe.index = k + 1 → esB[k].2.isUpper = false →
      ∀ cν, cell? M esB[k].2.src = some cν → highestAtMost M ρ.cr cν.row = some pa

/-- (open, about `M(s)` only) A node of the last column below its top reaches the next node of
the chain of the highest node of the root column at or below its row. -/
def X0Reach : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (ν : Ref) (cν : Cell), ν.column = M.size - 1 → 1 ≤ ν.index → cell? M ν = some cν →
      cν.row < t.row →
      ∀ q, highestAtMost M root.column cν.row = some q →
      ∀ kk m'', MStep M kk q m'' → ScaleReach M kk ν m''

/-- The origin of a lower emit is below `τ`. -/
theorem lower_src_lt {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {j : Nat} (hj : j < es.length) (hlow : es[j].2.isUpper = false) :
    ∃ c, cell? ctx.source es[j].2.src = some c ∧ official c.row < τ := by
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := emitsT_split h
  obtain ⟨_, hUup⟩ := upperT_run hus
  obtain ⟨_, hbelow⟩ := CopyMonoProof.lowerT_mono hlo
  subst hsplit
  by_cases hjl : j < lo.length
  · rw [List.getElem_append_left hjl]
    exact hbelow _ (List.getElem_mem hjl)
  · have hjl' : lo.length ≤ j := by omega
    have hj2 : j - lo.length < us.length := by simp at hj; omega
    rw [List.getElem_append_right hjl'] at hlow
    rw [hUup _ (List.getElem_mem hj2)] at hlow
    cases hlow

/-- **`OriginLower` from `PaLookup` and `X0Reach`.** -/
theorem originLower_of_parts (hP : PaLookup) (hX : X0Reach) : OriginLower := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB hesB k hk
    hpek hlow kk m'' hkk hst
  have hd := hS.data
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨root, hTop, hrc, hx0⟩ := data_top hd
  obtain ⟨hνc, hν1, cν, hcν, _⟩ := bsrc hesB hk
  rw [hlow] at hνc
  simp only [Bool.false_eq_true, if_false] at hνc
  have hesB' : emitsT (bctx M R ρ.cr ρ.x0 (i - 1)) (official t.row) = .ok esB := hesB
  obtain ⟨c, hc, hcτ⟩ := lower_src_lt hesB' hk hlow
  change cell? M _ = some c at hc
  rw [hcν] at hc
  cases hc
  have hlt : cν.row < t.row := by
    by_contra hn
    push Not at hn
    exact absurd (Recon.official_mono hTop.row_one_le hn) (not_le.mpr hcτ)
  have hpa := hP s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB
    hesB k hk hpek hlow cν hcν
  rw [← hrc] at hpa
  exact hX s M t root hTop esB[k].2.src cν (by rw [hνc, hx0]) hν1 hcν hlt pa hpa kk m'' hst

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
