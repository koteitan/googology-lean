/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLower.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerTree

set_option backward.do.legacy false

/-!
# The lower pairs, reduced to the item of the parent column

`LowerPairsHolds` (`JumpLawUpper.lean`) is the jump law for consecutive nodes `λ < θ` of the
lower part of a new column `X = x + w·i`, `i ≥ 1`, with `θ = bump λ e`, leg `l` of `θ` and
parent row `p` read in `Y = φ_i(l)`. It asks `jump λ p = e`.

Let `T` be the region of level `e + 1` of `λ` (the rows that agree with `λ` at the exponents
`≥ e`). Its supremum is `bump λ e = θ`. So `p` is the top of `Y` in `T` whenever `Y` has a
row in `T`, and `jump λ p = e` says that this top lies in a slot of `T` (coefficient `e - 1`)
other than the slot of `λ`.

`lowerPairsHolds_of_parts` proves `LowerPairsHolds` from two named statements:

* `LowerLegGe` (proved from `LegBelowTop` in `JumpLawLowerLeg.lean`): the leg of every node
  of the lower part of a column of block `i ≥ 1` is at least `c_r`. Then `Y` is a new column.
* `LowerJHolds` (open; `JumpLawLowerSplit.lean` splits the rows form `LowerRowsHolds` into
  the open cases `LowerRowsCopy` and `LowerRowsBoundary`): the item tree of `Y` has an item
  `J'` with target `T`, whose source column has a node in its source region, and (for
  `e ≥ 1`) with at most `λ_{e-1}` children.

The proof reads everything else from the item trees (`JumpLawLowerTree.lean`): the item `J`
of the tree of `X` with target `T` exists (`descend_to`), and every row of `Y` in `T` is
emitted by `J'` (`inTree_facts`), so it has height (coefficient `e - 1`) below the number of
children of `J'` (`run_coeff_lt`). `LowerJHolds` receives the item `J` of `X`, its output
and the fact that `λ` is the highest row of `X` in `T` as hypotheses.
-/

namespace OmegaY.Official.Recon.JumpLawLower

open Canonical Expansion Dimension RowLaw JumpLaw

/-! ## The open statements -/

/-- The leg of every node of the lower part of a column of block `i ≥ 1` is at least the
root column. Proved from `LegBelowTop` (`ChainCorrStartLegJump.lean`, the same fact for the
source nodes) by `lowerLegGe_of_legBelowTop` (`JumpLawLowerLeg.lean`). -/
def LowerLegGe : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    NewColumn s n R M t root i x → 1 ≤ i →
    ∀ vs, LowerRun (colCtx M R root i x) (official t.row) vs →
      ∀ em ∈ vs.flatten, ∀ l, em.leftColumn = some l → root.column ≤ l

/-- **A lower pair.** `λ = lam` and `θ = bump λ e` are consecutive emitted nodes of the lower
part of the column `X = x + w·i` of block `i ≥ 1`, `l` is the leg of `θ`, and `J` is the item
of the tree of `X` of level `e + 1` whose target region contains `λ`; `λ` is emitted by `J`
and is the highest row of the lower part of `X` in that region. -/
structure LowerPair (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref)
    (i x : Nat) (lam θ : Row) (l e : Nat) (J : Item) : Prop where
  nc : NewColumn s n R M t root i x
  pos : 1 ≤ i
  run : ∃ vs us col, LowerRun (colCtx M R root i x) (official t.row) vs ∧
    UpperRun (colCtx M R root i x) (official t.row) us ∧
    assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col ∧
    ∃ k, ∃ hk : k + 1 < (vs.flatten ++ us).length, k + 1 < vs.flatten.length ∧
      (vs.flatten ++ us)[k].row = lam ∧ (vs.flatten ++ us)[k + 1].row = θ ∧
      (vs.flatten ++ us)[k + 1].leftColumn = some l ∧
      (∃ LJ, runItem (colCtx M R root i x) (e + 1) J = .ok LJ ∧ (vs.flatten ++ us)[k] ∈ LJ) ∧
      ∀ em ∈ vs.flatten, inRegion (e + 1) J.target em.row = true → em.row ≤ lam
  bump : θ = Row.bump lam e
  tree : InTree (colCtx M R root i x) (official t.row) (e + 1) J
  region : inRegion (e + 1) J.target lam = true

/-- **Open (rows form).** For a lower pair, the column `Y = φ_i(l)` read for the leg of `θ`
has a lower row in the region of `J`, and all its lower rows there lie in slots (coefficient
`e - 1`) below the slot of `λ`. For `e = 0` the region is `{λ}`, so this says `λ ∈ Y`. -/
def LowerRowsHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat)
    (lam θ : Row) (l e : Nat) (J : Item), LowerPair s n R M t root i x lam θ l e J →
    ∀ i' x', NewColumn s n R M t root i' x' →
      legCol (colCtx M R root i x) l = x' + (M.size - 1 - root.column) * i' →
      ∀ vsY, LowerRun (colCtx M R root i' x') (official t.row) vsY →
        (∃ em ∈ vsY.flatten, inRegion (e + 1) J.target em.row = true) ∧
        ∀ em ∈ vsY.flatten, inRegion (e + 1) J.target em.row = true →
          ∀ d, e = d + 1 → em.row.coeff d < lam.coeff d

/-- **Open (tree form).** For a lower pair, the item tree of `Y = φ_i(l)` has an item `J'`
with the target of `J`, a node of its source column in its source region, and, when
`e ≥ 1`, at most `λ_{e-1}` children. -/
def LowerJHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat)
    (lam θ : Row) (l e : Nat) (J : Item), LowerPair s n R M t root i x lam θ l e J →
    ∀ i' x', NewColumn s n R M t root i' x' →
      legCol (colCtx M R root i x) l = x' + (M.size - 1 - root.column) * i' →
      ∃ J', InTree (colCtx M R root i' x') (official t.row) (e + 1) J' ∧
        J'.target = J.target ∧ Has (colCtx M R root i' x') (e + 1) J'.source ∧
        ∀ d, e = d + 1 → ∀ cs, childItems (colCtx M R root i' x') (d + 2) J' = .ok cs →
          cs.length ≤ lam.coeff d

/-! ## Descending to the item of a row -/

/-- An emitted node of an item of level `e + 1 + m` is emitted by a descendant of level
`e + 1`. -/
theorem descend_to {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (e : Nat) :
    ∀ m (A : Item) (L : List Emit) (em : Emit), ItemOK ctx (official t.row) (e + 1 + m) A →
      runItem ctx (e + 1 + m) A = .ok L → em ∈ L →
      ∃ J LJ, Desc ctx (e + 1 + m) A (e + 1) J ∧ runItem ctx (e + 1) J = .ok LJ ∧ em ∈ LJ
  | 0, A, L, em, _, hL, hem => ⟨A, L, .refl _ _, hL, hem⟩
  | m + 1, A, L, em, hA, hL, hem => by
    have hd : e + 1 + (m + 1) = (e + m) + 2 := by omega
    rw [hd] at hA hL ⊢
    obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItem_children hL
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    obtain ⟨L', hL', hemL'⟩ := List.mem_flatten.mp hem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL'
    have hj' : j < cs.length := by omega
    obtain ⟨hcOK, _⟩ := child_itemOK hctx hA hcs j hj'
    have hd' : e + m + 1 = e + 1 + m := by omega
    rw [hd'] at hcOK
    have hrun := hget j hj' hj
    rw [hd'] at hrun
    obtain ⟨J, LJ, hD, hLJ, hemJ⟩ := descend_to hctx e m cs[j] outs[j] em hcOK hrun hemL'
    rw [← hd'] at hD
    exact ⟨J, LJ, .step hcs (List.getElem_mem hj') hD, hLJ, hemJ⟩

/-- A row above `τ`: it agrees with `τ` above `e` and exceeds it at `e`. -/
theorem lt_of_coeffs {τ θ : Row} {e : Nat} (hhi : ∀ q, e < q → θ.coeff q = τ.coeff q)
    (hat : τ.coeff e < θ.coeff e) : τ < θ :=
  Row.lt_iff.mpr ⟨e, fun q hq => (hhi q hq).symm, hat⟩

/-- **The item of `X` containing `λ`.** -/
theorem item_of_lambda {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) {em : Emit} (hem : em ∈ vs.flatten) {e : Nat}
    (hθ : Row.bump em.row e < official t.row) :
    ∃ J LJ, InTree ctx (official t.row) (e + 1) J ∧ runItem ctx (e + 1) J = .ok LJ ∧ em ∈ LJ ∧
      inRegion (e + 1) J.target em.row = true := by
  set τ := official t.row with hτ
  obtain ⟨F, hF, hin⟩ := lowerItems_cover τ (lower_lt hctx hvs em hem)
  obtain ⟨LF, hLF, hemF, _⟩ := mem_first_output hctx hvs hF hem hin
  obtain ⟨hFOK, hst, hF1, hagree⟩ := lower_itemOK (ctx := ctx) hF
  -- the level of the first item is at least `e + 1`
  have hlev : e + 1 ≤ F.1 := by
    by_contra hn
    apply absurd hθ
    apply not_lt.mpr
    apply le_of_lt
    apply lt_of_coeffs (e := e)
    · intro q hq
      rw [bump_coeff_high hq]
      rw [hst] at hin
      rw [inRegion_iff'.mp hin q (by omega), ← hagree q (by omega)]
    · rw [bump_coeff_at]
      rw [hst] at hin
      rw [inRegion_iff'.mp hin e (by omega), ← hagree e (by omega)]
      omega
  obtain ⟨m, hm⟩ : ∃ m, F.1 = e + 1 + m := ⟨F.1 - (e + 1), by omega⟩
  have hFOK' := hFOK
  rw [hm] at hFOK' hLF
  obtain ⟨J, LJ, hD, hLJ, hemJ⟩ := descend_to hctx e m F.2 LF em hFOK' hLF hemF
  rw [← hm] at hD
  have hJ : InTree ctx τ (e + 1) J := ⟨F, hF, hD⟩
  obtain ⟨_, hJOK, _⟩ := inTree_facts hctx hvs hJ
  have hgood := runItem_good hctx (e + 1) (by omega) J hJOK LJ hLJ
  exact ⟨J, LJ, hJ, hLJ, hemJ, hgood.1.2.1 em hemJ⟩

/-! ## The reductions -/

/-- **The tree form gives the rows form.** -/
theorem lowerRows_of_J (hJH : LowerJHolds) : LowerRowsHolds := by
  intro s n R M t root i x lam θ l e J hP i' x' hNC' hY vsY hvsY
  obtain ⟨J', hJ', htgt, hHas, hcount⟩ := hJH s n R M t root i x lam θ l e J hP i' x' hNC' hY
  have hctxY := hNC'.runCtx
  obtain ⟨_, hJ'OK, LB, hLB, hLBsub, hLBback⟩ := inTree_facts hctxY hvsY hJ'
  have hgood := runItem_good hctxY (e + 1) (by omega) J' hJ'OK LB hLB
  rw [htgt] at hLBback hgood
  refine ⟨?_, ?_⟩
  · obtain ⟨em0, hem0⟩ := List.exists_mem_of_ne_nil LB (hgood.2.mp hHas)
    exact ⟨em0, hLBsub em0 hem0, hgood.1.2.1 em0 hem0⟩
  · intro em hem hin d hd
    subst hd
    have hemB := hLBback em hem hin
    obtain ⟨cs, outs, hcs, _, _⟩ := runItem_children hLB
    have h1 := run_coeff_lt hctxY hJ'OK hLB hcs em hemB
    have h2 := hcount d rfl cs hcs
    omega

/-- **The jump law for the lower pairs from `LowerLegGe` and `LowerRowsHolds`.** -/
theorem lowerPairsHolds_of_rows (hleg : LowerLegGe) (hR : LowerRowsHolds) : LowerPairsHolds := by
  intro s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB
  have hctx := hNC.runCtx
  set τ := official t.row with hτ
  set E := vs.flatten ++ us with hE
  set w := M.size - 1 - root.column with hw
  have hL := lower_lt hctx hvs
  have hsorted := assemble_sorted hasm
  have hmemk1 : E[k + 1] ∈ vs.flatten := getElem_mem_left hk hkL
  have hmemk : E[k] ∈ vs.flatten := getElem_mem_left (by omega) (by omega)
  have hθτ : E[k + 1].row < τ := hL _ hmemk1
  -- the item of `X`
  obtain ⟨J, LJ, hJ, hLJ, hlamJ, hlamin⟩ := item_of_lambda hctx hvs hmemk (e := e)
    (by rw [← hθ]; exact hθτ)
  have hbJ : Row.bump E[k].row e = Row.bump J.target e := by
    simpa using bump_of_inRegion hlamin
  have hmax : ∀ em ∈ vs.flatten, inRegion (e + 1) J.target em.row = true → em.row ≤ E[k].row := by
    intro em hem hin
    apply le_of_consecutive hsorted hk (List.mem_append_left _ hem)
    rw [hθ, hbJ]
    simpa using lt_bump_of_inRegion hin
  have hP : LowerPair s n R M t root i x E[k].row E[k + 1].row l e J :=
    ⟨hNC, hi, ⟨vs, us, col, hvs, hus, hasm, k, hk, hkL, rfl, rfl, hleft, ⟨LJ, hLJ, hlamJ⟩, hmax⟩,
      hθ, hJ, hlamin⟩
  -- the column `Y`
  have hcr := hNC.top.lt
  have hcl : root.column ≤ l := hleg s n R M t root i x hNC hi vs hvs _ hmemk1 l hleft
  have hlegY : legCol (colCtx M R root i x) l = l + w * i := by
    unfold legCol
    rw [if_pos (show (colCtx M R root i x).rootColumn ≤ l from hcl)]
    rfl
  have hYs : l + w * i < R.size := by
    obtain ⟨em, hem, _⟩ := List.mem_map.mp hHB.1
    rw [hlegY] at hem
    by_contra hn
    rw [realNodes_eq_nil hn] at hem
    cases hem
  have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi
  have hY0 : M.size - 1 ≤ l + w * i := by omega
  obtain ⟨i', x', hNC', hY⟩ := newColumn_at hNC hY0 hYs
  obtain ⟨vsY, usY, colY, hvsY, husY, hasmY, hrowsY⟩ := hNC'.emits
  obtain ⟨⟨em0, hem0, hem0in⟩, hslot⟩ :=
    hR s n R M t root i x E[k].row E[k + 1].row l e J hP i' x' hNC' (by rw [hlegY]; exact hY) vsY hvsY
  -- the rows of `Y`
  rw [hlegY, hY, hrowsY] at hHB
  have hz : ZeroBelow e J.target := by
    obtain ⟨_, hJOK, _⟩ := inTree_facts hctx hvs hJ
    simpa using hJOK.target
  have hsup : Row.bump J.target e = E[k + 1].row := by
    rw [hθ, hbJ]
  have hem0lt : em0.row < E[k + 1].row := by
    rw [← hsup]
    have := lt_bump_of_inRegion hem0in
    simpa using this
  have hpge : em0.row ≤ p :=
    hHB.2.2 _ (List.mem_map.mpr ⟨em0, List.mem_append_left _ hem0, rfl⟩) hem0lt
  have hpin : inRegion (e + 1) J.target p = true := by
    apply inRegion_of_between
    · exact (base_le_of_inRegion (by simpa using hz) hem0in).trans hpge
    · simpa [hsup] using hHB.2.1
  -- the node of `p`
  obtain ⟨emp, hemp, hemprow⟩ := List.mem_map.mp hHB.1
  have hempL : emp ∈ vsY.flatten := by
    rcases List.mem_append.mp hemp with h | h
    · exact h
    · obtain ⟨hU1, _⟩ := upper_facts husY
      obtain ⟨_, _, _, hτ', _⟩ := hU1 emp h
      exfalso
      have := hHB.2.1
      rw [← hemprow] at this
      exact absurd (hτ'.trans_lt (this.trans hθτ)) (lt_irrefl _)
  -- the jump
  apply jump_eq_of_coeffs
  · intro q hq
    rw [inRegion_iff'.mp hlamin q (by omega), inRegion_iff'.mp hpin q (by omega)]
  · intro he
    obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
    have h1 := hslot emp hempL (by rw [hemprow]; exact hpin) d rfl
    rw [hemprow] at h1
    have h2 : E[k].row.coeff d = (vs.flatten ++ us)[k].row.coeff d := rfl
    simp only [Nat.add_sub_cancel]
    omega

/-- **The jump law for the lower pairs from `LowerLegGe` and `LowerJHolds`.** -/
theorem lowerPairsHolds_of_parts (hleg : LowerLegGe) (hJH : LowerJHolds) : LowerPairsHolds :=
  lowerPairsHolds_of_rows hleg (lowerRows_of_J hJH)

/-- **The jump law and the row law from the open parts.** -/
theorem jumpLawHolds_of_lowerRows (hleg : LowerLegGe) (hR : LowerRowsHolds) :
    RowLaw.JumpLawHolds :=
  jumpLawHolds_of_lowerPairs (lowerPairsHolds_of_rows hleg hR)

end OmegaY.Official.Recon.JumpLawLower

#print axioms OmegaY.Official.Recon.JumpLawLower.lowerPairsHolds_of_rows
#print axioms OmegaY.Official.Recon.JumpLawLower.lowerPairsHolds_of_parts
#print axioms OmegaY.Official.Recon.JumpLawLower.jumpLawHolds_of_lowerRows
