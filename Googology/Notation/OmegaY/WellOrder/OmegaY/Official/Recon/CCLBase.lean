/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CCLBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexNew

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CopyCountLe` from two statements about ascension (`CCL`)

`RPLLex.CopyCountLe` (`RPLLexNew.lean`): two nodes `v = (x, a)`, `v' = (y, b)` below `τ` of two
columns of a block `1 ≤ i ≤ n`, with the same row `C` and the same stored left end, and the
condition on the nodes above them (`v` is the top of `x`, or the left end of `v⁺` is not right of
the left end of `v'⁺`): `v` has at most as many emits in the copy of `x` as `v'` in the copy of `y`.

Every emit of `v` except one is a gap copy (`NNC`), and a gap copy of `v` exists only when the
column `x` ascends at a root top of row `C` (`AscRow`, from the proved `lowerT_cut`). So:

* if `x` does not ascend at `C`, `v` has exactly one emit, and `v'` has at least one (`cov`);
* if `x` ascends at `C`, then `y` ascends at `C` (**`AscCarry`**), and two columns that both
  ascend at `C` give the same number of emits (**`CountAsc`**, stated as `≤`).

## Results

* `cnt_le_one_of_not_asc`: no ascension at `C` ⇒ at most one emit;
* `copyCountLe_of : AscCarry → CountAsc → CopyCountLe`.

## Numerical check

`AscCarry` and `CountAsc` (with the ascension of the harness, `nodeAt` of the reference row and
the row parents): 0 failures, see the final report of this task.
-/

namespace OmegaY.Official.Recon.CCL

open Canonical Expansion Geometry Frame Classification
open Reserve (cell?)
open Classification.Proofs.ChainCorr (cutOrigin)
open Classification.Proofs.CopyShape.ProfileLeg (AscRow)
open RPLLex (cnt CopyCountLe ColOK colOK_of_run)

/-! ## The two statements -/

/-- The condition of `CopyCountLe` on the nodes above `v = (x, a)` and `v' = (y, b)`. -/
def AboveCond (M : Mountain) (x a y b : Nat) : Prop :=
  cell? M ⟨x, a + 1⟩ = none ∨ ∃ cu cu' l l', cell? M ⟨x, a + 1⟩ = some cu ∧
    cell? M ⟨y, b + 1⟩ = some cu' ∧ cu.left = some l ∧ cu'.left = some l' ∧
    l.column ≤ l'.column

/-- The copy context of the column `x` of block `i`. -/
abbrev bctx (M R : Mountain) (root : Ref) (i x : Nat) : Context :=
  ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i)

/-- **(b)** Under the condition on the nodes above, if the column `x` ascends at a root top of
row `C` (the row of `v`), so does the column `y`. -/
def AscCarry : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ (i x y : Nat), 0 < i → i ≤ n → x ∈ blockColumns root.column (M.size - 1) n i →
      y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (a b : Nat) (cv cv' : Cell), 1 ≤ a → 1 ≤ b →
      cell? M ⟨x, a⟩ = some cv → cell? M ⟨y, b⟩ = some cv' → cv.row = cv'.row →
      cv.row < t.row → cv.left = cv'.left → AboveCond M x a y b →
      AscRow (bctx M R root i x) (official cv.row) → AscRow (bctx M R root i y) (official cv.row)

/-- **(c)** Two columns of a block that both ascend at `C`: a node `v` of row `C` of the first
has at most as many emits as the node `v'` of row `C` of the second with the same left end. -/
def CountAsc : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ (i x y : Nat), 0 < i → i ≤ n → x ∈ blockColumns root.column (M.size - 1) n i →
      y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es esY, emitsT (bctx M R root i x) (official t.row) = .ok es →
      emitsT (bctx M R root i y) (official t.row) = .ok esY →
    ∀ (a b : Nat) (cv cv' : Cell), 1 ≤ a → 1 ≤ b →
      cell? M ⟨x, a⟩ = some cv → cell? M ⟨y, b⟩ = some cv' → cv.row = cv'.row →
      cv.row < t.row → cv.left = cv'.left →
      AscRow (bctx M R root i x) (official cv.row) →
      AscRow (bctx M R root i y) (official cv.row) →
      cnt es ⟨x, a⟩ ≤ cnt esY ⟨y, b⟩

/-! ## Counting -/

theorem countP_le_one {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Pairwise (fun a b => ¬ (p a = true ∧ p b = true)) → l.countP p ≤ 1
  | [], _ => by simp
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    rw [List.countP_cons]
    by_cases ha : p a = true
    · have : l.countP p = 0 := List.countP_eq_zero.mpr (fun b hb hpb => h.1 b hb ⟨ha, hpb⟩)
      simp [ha, this]
    · have := countP_le_one h.2
      simp [ha]
      omega

section Col

variable {ctx : Context} {τ : Row} {es : List (Emit × Origin)}

/-- **At most one emit** when no emit of `v` is a gap copy. -/
theorem cnt_le_one (C : ColOK ctx τ es) (v : Ref)
    (hnc : ∀ e ∈ es, e.2.src = v → cutOrigin e.2 = false) : cnt es v ≤ 1 := by
  unfold cnt
  apply countP_le_one
  refine C.nnc.imp_of_mem ?_
  intro p q _ hq hpq hpv
  obtain ⟨h1, h2⟩ := hpv
  simp only [decide_eq_true_eq] at h1 h2
  exact hpq (hnc q hq h2) (h1.trans h2.symm)

/-- **At least one emit** for a node below `τ` of the copied column. -/
theorem one_le_cnt (C : ColOK ctx τ es) {v : Ref} {c : Cell} (hv : v.column = ctx.x)
    (hv1 : 1 ≤ v.index) (hc : cell? ctx.source v = some c) (hτ : official c.row < τ) :
    1 ≤ cnt es v := by
  obtain ⟨q, hq, hqs, _⟩ := C.cov v c hv hv1 hc (Or.inl hτ)
  unfold cnt
  exact List.countP_pos_iff.mpr ⟨q, hq, by simp [hqs]⟩

end Col

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **No gap copy of `v` without ascension at the row of `v`** (from `lowerT_cut`). -/
theorem noCut_of_not_asc (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    {i x : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) (hxg : root.column < x) (hxl : x ≤ M.size - 1)
    {es : List (Emit × Origin)} (hes : emitsT (bctx M R root i x) (official t.row) = .ok es)
    {v : Ref} {cv : Cell} (hcv : cell? M v = some cv)
    (hA : ¬ AscRow (bctx M R root i x) (official cv.row)) :
    ∀ e ∈ es, e.2.src = v → cutOrigin e.2 = false := by
  intro e he hev
  obtain ⟨lo, us, hlo, hus, rfl⟩ := LowerPB.emitsT_split hes
  rcases List.mem_append.mp he with h | h
  · by_contra hcut
    have hcut' : LowerPB.cutO e.2 = true := by
      rw [Classification.Proofs.CopyShape.Found.cutO_eq]
      simpa using hcut
    have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hB : LowerPB.BCtx M R root.column (M.size - 1) i (bctx M R root i x) :=
      LowerPB.bctx_ctxAt (le_of_lt hxg) hxl (by omega)
    obtain ⟨_, _, _, _, _, _, hasc⟩ :=
      Classification.Proofs.CopyShape.ProfileLeg.lowerT_cut hrun hTop hi1 hin hB hlo e h hcut'
        cv (by rw [hev]; exact hcv)
    exact hA hasc
  · have hu := CrossPlain.upperT_isUpper hus e h
    cases ho : e.2 with
    | upper r => rfl
    | plain r => rw [ho] at hu; cases hu
    | clean r b => rw [ho] at hu; cases hu

/-- **One emit without ascension.** -/
theorem cnt_le_one_of_not_asc (hrun : Official.expandDiagram s n = .ok R)
    (hTop : Top s M t root) {i x : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) (hxg : root.column < x)
    (hxl : x ≤ M.size - 1) {es : List (Emit × Origin)}
    (hes : emitsT (bctx M R root i x) (official t.row) = .ok es)
    {v : Ref} {cv : Cell} (hcv : cell? M v = some cv)
    (hA : ¬ AscRow (bctx M R root i x) (official cv.row)) : cnt es v ≤ 1 := by
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have C := colOK_of_run hrun hTop hi1 hin hxg hxl (by omega) hes
  exact cnt_le_one C v (noCut_of_not_asc hrun hTop hi1 hin hxg hxl hes hcv hA)

end Run

/-! ## The reduction -/

/-- **`CopyCountLe` from `AscCarry` and `CountAsc`.** -/
theorem copyCountLe_of (hAC : AscCarry) (hCA : CountAsc) : CopyCountLe := by
  intro s n R hrun M t root hTop i x y hi0 hin hxb hyb es esY hes hesY a b cv cv' ha hb hcv hcv'
    hrow hτ hleft habove
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hyb
  by_cases hA : AscRow (bctx M R root i x) (official cv.row)
  · exact hCA s n R hrun M t root hTop i x y hi0 hin hxb hyb es esY hes hesY a b cv cv' ha hb hcv
      hcv' hrow hτ hleft hA
      (hAC s n R hrun M t root hTop i x y hi0 hin hxb hyb a b cv cv' ha hb hcv hcv' hrow hτ hleft
        habove hA)
  · have h1 := cnt_le_one_of_not_asc hrun hTop hi0 hin hxg hxl hes hcv hA
    have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ (by omega)
    have CY := colOK_of_run hrun hTop hi0 hin hyg hyl (by omega) hesY
    have hV : MountainValid M := build_valid_of_success hTop.build
    have h1' : (1 : Row) ≤ cv'.row := Classification.one_le_row hV hcv' hb
    have hτ' : official cv'.row < official t.row := official_strictMono h1' (by rw [← hrow]; exact hτ)
    have h2 := one_le_cnt CY (v := ⟨y, b⟩) rfl hb hcv' hτ'
    omega

end OmegaY.Official.Recon.CCL

#print axioms OmegaY.Official.Recon.CCL.cnt_le_one_of_not_asc
#print axioms OmegaY.Official.Recon.CCL.copyCountLe_of
