/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerLookupBump.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStepInner
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

set_option backward.do.legacy false

/-!
# `BumpCopyLower` (`ChainCorrStepInner.lean`) from `CopyFirst`

`ChainCorr.Inner.BumpCopyLower` asks, for two consecutive copy pairs `(v, m)` and
`(v⁺, m⁺)` of a block `i ≥ 1` (`v⁺ = up v`, `m⁺ = up m`):

  `jump(row v, row v⁺) ≤ jump(row m, row m⁺)`.

`LegJump.stepJump_general` (`ChainCorrStartLegJump.lean`) proves this whenever the emit of
`v⁺` is not a gap copy (`b = 1`). A `CopyNode` may be a gap copy only when its origin has no
raw parent, so the one case left is a gap copy `v⁺` of `m⁺`. It does not occur: the emit of
`v` (index `j - 1`) has the origin `m`, and the origin rows of the emits of an inner column
do not decrease (`Inner.copyMono_holds`, proved), so no emit before `v⁺` has the origin
`m⁺` (its row is above the row of `m`). Hence `v⁺` is the first emit of `m⁺`, and the first
emit of an origin is not a gap copy (`CopyFirst`, open, another agent's statement).

* `site_of_copyAt`: a node with a traced origin in an inner column gives a `Site`.
* **`bumpCopyLower_of_copyFirst : Inner.CopyFirst → Inner.BumpCopyLower`** (proved, no
  other hypothesis).

All declarations are in the namespace `ChainCorr.InnerLookup`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- A node with a traced origin in an inner column of block `i ≥ 1` gives a `Site`. -/
theorem site_of_copyAt {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {y : Nat} {es : List (Emit × Origin)} {X : Nat}
    (hcy : ρ.cr < y) (hyx : y < ρ.x0) (hyb : y ∈ blockColumns ρ.cr ρ.x0 n i)
    (hX : X = y + (ρ.x0 - ρ.cr) * i)
    (hes : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es) :
    ChainCorr.Site s n D M out ρ R t X y i es := by
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
  subst hcc
  have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
  subst htt
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  have hwi : (ρ.x0 - ρ.cr) * i ≤ n * (ρ.x0 - ρ.cr) := by
    rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
  have hw1 : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hi0
  have hXR : X < R.size := by omega
  have hX0 : ρ.x0 ≤ X := by omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 X hXR hX0
  obtain ⟨hii, hxx⟩ := block_unique hcrx hcy hyx hx' (hX.symm.trans hXeq) hi0
  subst hii
  subst hxx
  exact ⟨hS.splice, hS.deg, hS.run, hS.canon, ⟨col', hS.hcol, hS.ht⟩, hX0, hXR, hX, hi, hyb, hi0,
    ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩

/-- **`BumpCopyLower` from `CopyFirst`.** -/
theorem bumpCopyLower_of_copyFirst (hC2 : Inner.CopyFirst) : Inner.BumpCopyLower := by
  intro s n D M out ρ R col t hS i hi0 hi v m hvm hup _ cv cv' cm cm' hcv hcv' hcm hcm'
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨hv0, hm0⟩ := copyNode_index_pos hvm
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, hsrc, hcut⟩ := hup
  obtain ⟨y2, es2, j2, _, _, _, hvc2, hvi2, hes2, hj2, hsrc2, _⟩ := hvm
  simp only [up] at hvc hvi hes
  have hyy : y2 = y := by omega
  subst hyy
  have hee : es2 = es := Except.ok.inj (hes2.symm.trans hes)
  subst hee
  have hjj : j = j2 + 1 := by omega
  subst hjj
  have hes' : emitsT (ctxAt M R y2 i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y2 + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es2 := by rw [← hvc]; exact hes
  -- the emit of `v⁺` is not a gap copy
  have hnc : cutOrigin es2[j2 + 1].2 = false := by
    rcases hcut with h | h
    · exact h
    · apply hC2 s n D M out ρ R col t hS i hi0 hi y2 es2 hcy hyx hes' (j2 + 1) hj
      intro k' hk' hlt heq
      rw [hsrc] at heq
      have hck' : cell? M es2[k'].2.src = some cm' := by rw [heq]; exact hcm'
      have hck : cell? M es2[j2].2.src = some cm := by rw [hsrc2]; exact hcm
      have hle := copyMono_holds s n D M out ρ R col t hS i hi0 hi y2 es2 hcy hyx hes' k' j2 hk'
        hj2 (by omega) cm' cm hck' hck
      have hm' : cell? M ⟨m.column, m.index + 1⟩ = some cm' := hcm'
      have hm : cell? M ⟨m.column, m.index⟩ = some cm := hcm
      have hlt' := cell_row_lt hV hm hm' (by omega)
      exact absurd (lt_of_le_of_lt hle hlt') (lt_irrefl _)
  -- the site of `v⁺`
  have hSite := site_of_copyAt hS hi0 hi hcy hyx hyb hvc hes
  have hcu : cell? R ⟨v.column, j2 + 1 + 1⟩ = some cv' := by
    have : (up v) = ⟨v.column, j2 + 1 + 1⟩ := by simp [up, hvi2]
    rw [← this]; exact hcv'
  have hcd : cell? R ⟨v.column, j2 + 1⟩ = some cv := by
    have : v = ⟨v.column, j2 + 1⟩ := by cases v; simp_all
    rw [← this]; exact hcv
  have hsrcc : cell? M es2[j2 + 1].2.src = some cm' := by rw [hsrc]; exact hcm'
  have h2 : 2 ≤ es2[j2 + 1].2.src.index := by rw [hsrc]; simp [up]; omega
  have hcvd : cell? M ⟨es2[j2 + 1].2.src.column, es2[j2 + 1].2.src.index - 1⟩ = some cm := by
    rw [hsrc]
    have : (⟨(up m).column, (up m).index - 1⟩ : Ref) = m := by cases m; simp [up]
    rw [this]; exact hcm
  have hmain := LegJump.stepJump_general hSite hj hnc hcu hsrcc h2 (by omega) hcd hcvd
  rw [Row.jump_comm cv.row, Row.jump_comm cm.row]
  exact hmain

end OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.site_of_copyAt
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.InnerLookup.bumpCopyLower_of_copyFirst
