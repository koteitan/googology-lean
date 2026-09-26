/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawSeam.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawAscend

set_option backward.do.legacy false

/-!
# The seam at `τ`

`SeamTauHolds` (`JumpLawUpper.lean`) is the jump law for the pair `(λ, τ)` of a column of
block `i ≥ 1` whose first upper row is `τ` itself. Then `λ` is the top of the lower part,
and it lies in the first item `F` (level `K = jump τ a₀`) of the top `a₀` of the source
column `x` below `τ`, together with the parent row `p`. The jump law asks that the height
coordinate `K - 2` of `p` be below that of `λ`.

For a *plain* item (no copied root row, no cut bottom; all first items are plain) the
children are the slots `0, …, N` with `N = h_a + [x ascends]·Δ`, `Δ = (h_κ - h_ρ)·i`
(`plain_children`); every emitted row has height at most `N`, and the last child emits
(`plain_emission`). The comparison of heights then reads:

* `l < c_r`: `p` is the source parent row, of height below `h_a ≤ N_X`;
* `l > c_r`: `Y` copies `l` in the same block, `h_a(l) < h_a(x)`, and if `l` ascends in `F`
  so does `x` (`ascends_of_leg`);
* `l = c_r`: `Y` copies `x₀` in block `i - 1`, `x` ascends in `F` (`ascends_of_root_leg`),
  and `h_κ + (h_κ - h_ρ)(i-1) = h_ρ + Δ < h_a(x) + Δ`.

With `seamTauHolds`, the jump law and the row law follow from `LowerPairsHolds` alone
(`jumpLawHolds_of_lowerPairs`, `rowLawHolds_of_lowerPairs`).
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw

/-- The lift of a plain item in block `i`. -/
def liftOf (ctx : Context) (d : Nat) (S : Row) : Nat :=
  (heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) S) -
    heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) S)) * ctx.block

/-- **The children of a plain item.** -/
theorem plain_children {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {it : Item}
    (hit : ItemOK ctx (official t.row) (d + 2) it) (hcl : it.clean = none)
    (hcut : it.cutBottom = false) {a : Ref × Cell}
    (ha : topIn ctx.source ctx.x (d + 2) it.source = some a) :
    Ok (childItems ctx (d + 2) it) (fun children =>
      ∃ asc, ascends ctx (topIn ctx.source ctx.rootColumn (d + 2) it.source) = .ok asc ∧
        ∃ N, children.length = N + 1 ∧
          N = (official a.2.row).coeff d + (if asc then liftOf ctx d it.source else 0) ∧
          (∀ j (hj : j < children.length), children[j].target = slot (d + 2) it.target j) ∧
          ∀ (hN : N < children.length),
            children[N].source = slot (d + 2) it.source ((official a.2.row).coeff d)) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  unfold childItems
  dsimp only
  rw [ha]
  dsimp only
  have hTdef : height (d + 2) (official a.2.row) = (official a.2.row).coeff d := height_eq _ _
  refine ok_bind (ok_eq _) (fun asc hasc => ?_)
  split
  · -- case 1
    rename_i hasc'
    have hasc_false : asc = false := by simpa using hasc'
    subst hasc_false
    split
    · exact ok_throw_bind _ _
    · refine ok_pure ⟨false, hasc, (official a.2.row).coeff d, ?_, by simp, ?_, ?_⟩
      · simp [hTdef]
      · intro j hj; simp
      · intro hN; simp [hTdef]
  · rename_i hasc'
    have hasc_true : asc = true := by simpa using hasc'
    subst hasc_true
    obtain ⟨⟨ρRef, ρCell⟩, hρ, p, hp, hprow⟩ := node_of_ascends hctx hasc
    obtain ⟨_, hρin, _⟩ := topIn_spec hρ
    have hpin : inRegion (d + 2) it.source (official p.2.row) = true := by
      rw [hprow]; exact hρin
    have hRT : (official ρCell.row).coeff d ≤ (official a.2.row).coeff d := by
      refine coeff_le_of_inRegion hρin (topIn_spec ha).2.1 ?_
      rw [← hprow]
      exact topIn_row_max hb ha hp hpin
    have hρ' : topIn ctx.source root.column (d + 2) it.source = some (ρRef, ρCell) := by
      rw [← hctx.rootc]; exact hρ
    obtain ⟨⟨κRef, κCell⟩, hκ, hle⟩ := Top.rootCut_region hctx.top hit.below hρ'
    have hκ' : topIn ctx.source ctx.lastColumn (d + 2) it.source = some (κRef, κCell) := by
      rw [hctx.last]; exact hκ
    have hRK : (official ρCell.row).coeff d ≤ (official κCell.row).coeff d :=
      coeff_le_of_inRegion hρin (topIn_spec hκ).2.1 hle
    have hlift : liftOf ctx d it.source =
        ((official κCell.row).coeff d - (official ρCell.row).coeff d) * ctx.block := by
      simp only [liftOf, hκ', hρ, heightOf, height_eq]
    rw [hρ]
    generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB
    simp only [heightOf, height_eq]
    rw [hcl]
    simp only [hcut, Bool.false_eq_true, not_false_eq_true, if_true]
    rw [hκ']
    simp only
    refine ok_pure ⟨true, by rw [← hρ]; exact hasc,
      (official a.2.row).coeff d + liftOf ctx d it.source, ?_, by simp,
      ?_, ?_⟩
    · simp only [List.length_map, List.length_range, hlift]
      have : (((official κCell.row).coeff d : Int) - ((official ρCell.row).coeff d : Int)) *
          (ctx.block : Int) =
          (((official κCell.row).coeff d - (official ρCell.row).coeff d) * ctx.block : Nat) := by
        push_cast [Nat.cast_sub hRK]
        rfl
      rw [this]
      omega
    · intro j hj
      simp only [List.getElem_map, List.getElem_range]
      split_ifs <;> rfl
    · intro hN
      simp only [List.getElem_map, List.getElem_range]
      have hcast : (((official κCell.row).coeff d : Int) - ((official ρCell.row).coeff d : Int)) *
          (ctx.block : Int) =
          (((official κCell.row).coeff d - (official ρCell.row).coeff d) * ctx.block : Nat) := by
        push_cast [Nat.cast_sub hRK]
        rfl
      simp only [List.length_map, List.length_range] at hN
      rw [hlift] at hN ⊢
      rw [hcast] at hN ⊢
      generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e at hN ⊢
      have he : 0 ≤ e ∧ e ≤ 1 := by rw [← hedef]; split <;> omega
      generalize ((official κCell.row).coeff d - (official ρCell.row).coeff d) * ctx.block = L at hN ⊢
      split_ifs with h1 h2
      · omega
      · dsimp only
        congr 1
        omega
      · dsimp only
        congr 1
        omega

theorem ok_and {ε α : Type} {x : Except ε α} {P Q : α → Prop} (hP : Ok x P) (hQ : Ok x Q) :
    Ok x (fun a => P a ∧ Q a) := fun a h => ⟨hP a h, hQ a h⟩

/-- **The emission of a plain item.** Every emitted row has height at most
`N = h_a + [asc]·Δ`, and some emitted row has height exactly `N`. -/
theorem plain_emission {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} {it : Item}
    (hit : ItemOK ctx (official t.row) (d + 2) it) (hcl : it.clean = none)
    (hcut : it.cutBottom = false) {a : Ref × Cell}
    (ha : topIn ctx.source ctx.x (d + 2) it.source = some a) :
    Ok (runItem ctx (d + 2) it) (fun L =>
      ∃ asc, ascends ctx (topIn ctx.source ctx.rootColumn (d + 2) it.source) = .ok asc ∧
        (∀ em ∈ L, em.row.coeff d ≤
          (official a.2.row).coeff d + (if asc then liftOf ctx d it.source else 0)) ∧
        ∃ em ∈ L, em.row.coeff d =
          (official a.2.row).coeff d + (if asc then liftOf ctx d it.source else 0) ∧
          inRegion (d + 2) it.target em.row = true) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  rw [runItem]
  refine ok_bind (ok_and (childSpec hctx hit) (plain_children hctx hit hcl hcut ha))
    (fun children hch => ?_)
  obtain ⟨⟨n, F, σ, rfl, htgt, hsrc, _, _, hoff⟩, asc, hasc, N, hlen, hN, _, hlast⟩ := hch
  simp only [List.length_map, List.length_range] at hlen
  let P : Item → List Emit → Prop := fun c L =>
    Good (d + 1) c.target L ∧ (Has ctx (d + 1) c.source ↔ L ≠ [])
  refine ok_bind (ok_mapM₂ P ((List.range n).map F) (runItem ctx (d + 1)) ?_)
    (fun outs houts => ok_pure ?_)
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    have hj' : j < n := List.mem_range.mp hj
    refine runItem_good hctx (d + 1) (by omega) (F j) ⟨?_, ?_, hoff j hj'⟩
    · rw [htgt j]
      exact slot_zeroBelow d it.target j
    · intro r hr
      rw [hsrc j] at hr
      exact hit.below r (inRegion_of_slot hr)
  · obtain ⟨hlen', hget⟩ := forall₂_getElem houts
    simp only [List.length_map, List.length_range] at hlen'
    have hP : ∀ j (hj : j < outs.length), P (F j) outs[j] := by
      intro j hj
      have := hget j (by simp; omega) hj
      simpa using this
    refine ⟨asc, hasc, ?_, ?_⟩
    · intro em hem
      obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
      have hin := (hP j hj).1.2.1 em hemL
      rw [htgt j] at hin
      have := (inRegion_slot_iff.mp hin).2
      rw [← hN]
      omega
    · have hNo : N < outs.length := by omega
      have hsrcN : (F N).source = slot (d + 2) it.source ((official a.2.row).coeff d) := by
        have := hlast (by simp; omega)
        simpa using this
      have hHas : Has ctx (d + 1) (F N).source := by
        rw [hsrcN]
        obtain ⟨hamem, hain, _⟩ := topIn_spec ha
        exact ⟨a, hamem, inRegion_slot_iff.mpr ⟨hain, rfl⟩⟩
      have hne := (hP N hNo).2.mp hHas
      obtain ⟨em, hem⟩ := List.exists_mem_of_ne_nil _ hne
      have hin := (hP N hNo).1.2.1 em hem
      rw [htgt N] at hin
      refine ⟨em, List.mem_flatten.mpr ⟨_, List.getElem_mem hNo, hem⟩, ?_, inRegion_of_slot hin⟩
      rw [(inRegion_slot_iff.mp hin).2, hN]

/-! ## First items -/

theorem referenceRow_le (ρ : Row) : referenceRow ρ ≤ ρ := by
  by_cases h0 : 0 < ρ.coeff 0
  · have := referenceRow_bump h0
    conv_rhs => rw [← this]
    exact (Row.lt_bump _ _).le
  · unfold referenceRow
    rw [if_neg h0]

/-- The first item of level `d + 2` that contains a row `a₀` leaving `τ` at `d + 1`. -/
def firstItem (τ a0 : Row) (d : Nat) : Nat × Item :=
  (d + 2, ⟨slot (d + 3) τ (a0.coeff (d + 1)), slot (d + 3) τ (a0.coeff (d + 1)), none, 0, false⟩)

theorem firstItem_mem {τ a0 : Row} {d : Nat} (ha : a0 < τ) (hK : Row.jump τ a0 = d + 2) :
    firstItem τ a0 d ∈ lowerItems τ := by
  have hlt : a0.coeff (d + 1) < τ.coeff (d + 1) := by
    have := coeff_lt_of_lt ha
    rw [Row.jump_comm, hK] at this
    exact this
  have hlen : d + 1 < len τ := by
    by_contra hn
    have := coeff_of_le_len (a := τ) (k := d + 1) (by omega)
    omega
  unfold lowerItems firstItem
  refine List.mem_flatMap.mpr ⟨d + 1, by simpa using hlen, ?_⟩
  exact List.mem_map.mpr ⟨a0.coeff (d + 1), List.mem_range.mpr hlt, rfl⟩

theorem inRegion_firstItem {τ a0 : Row} {d : Nat} (hK : Row.jump τ a0 = d + 2) {r : Row} :
    inRegion (d + 2) (slot (d + 3) τ (a0.coeff (d + 1))) r = true ↔ Row.jump r a0 ≤ d + 1 := by
  rw [inRegion_iff', Row.jump_le_iff]
  simp only [show d + 2 - 1 = d + 1 by omega]
  constructor
  · intro h i hi
    rw [h i hi, coeff_slot]
    rw [if_neg (by omega)]
    split
    · rename_i he
      rw [show i = d + 1 by omega]
    · exact Row.coeff_eq_of_jump_le (d := d + 2) hK.le (by omega)
  · intro h i hi
    rw [h i hi, coeff_slot, if_neg (by omega)]
    split
    · rename_i he
      rw [show i = d + 1 by omega]
    · exact (Row.coeff_eq_of_jump_le (d := d + 2) hK.le (by omega)).symm

/-- Two first items with a common row are equal. -/
theorem lowerItems_eq_of_common {τ : Row} {G G' : Nat × Item} (hG : G ∈ lowerItems τ)
    (hG' : G' ∈ lowerItems τ) {r : Row} (h : inRegion G.1 G.2.source r = true)
    (h' : inRegion G'.1 G'.2.source r = true) : G = G' := by
  obtain ⟨k, j, _, hj, rfl⟩ := mem_lowerItems hG
  obtain ⟨k', j', _, hj', rfl⟩ := mem_lowerItems hG'
  simp only at h h'
  rw [inRegion_iff'] at h h'
  simp only [show k + 1 - 1 = k by omega, show k' + 1 - 1 = k' by omega] at h h'
  have hk : ∀ k j, j < τ.coeff k → (∀ i, k ≤ i → r.coeff i = (slot (k + 2) τ j).coeff i) →
      Row.jump τ r = k + 1 ∧ r.coeff k = j := by
    intro k j hj hr
    refine ⟨Row.jump_eq_succ_of_last ?_ ?_, ?_⟩
    · rw [hr k le_rfl, slot_coeff_at]; omega
    · intro i hi; rw [hr i (by omega), slot_coeff_high hi]
    · rw [hr k le_rfl, slot_coeff_at]
  obtain ⟨h1, h2⟩ := hk k j hj h
  obtain ⟨h1', h2'⟩ := hk k' j' hj' h'
  have hkk : k = k' := by omega
  subst hkk
  have hjj : j = j' := by rw [← h2, ← h2']
  subst hjj
  rfl

/-- The emission of a first item within the lower part. -/
theorem first_output {ctx : Context} {t : Cell} {vs : List (List Emit)} (hvs : LowerRun ctx (official t.row) vs)
    {G : Nat × Item} (hG : G ∈ lowerItems (official t.row)) :
    ∃ L, runItem ctx G.1 G.2 = .ok L ∧ ∀ em ∈ L, em ∈ vs.flatten := by
  have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) => runItem ctx p.1 p.2 = .ok L)
    (lowerItems (official t.row)) _ (fun p _ => ok_eq _) vs hvs
  obtain ⟨L, hL, hrun⟩ := forall₂_mem_left hF G hG
  exact ⟨L, hrun, fun em hem => List.mem_flatten.mpr ⟨L, hL, hem⟩⟩

/-- A lower row in the region of a first item is emitted by that item. -/
theorem mem_first_output {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)} (hvs : LowerRun ctx (official t.row) vs)
    {G : Nat × Item} (hG : G ∈ lowerItems (official t.row)) {em : Emit} (hem : em ∈ vs.flatten)
    (hin : inRegion G.1 G.2.source em.row = true) :
    ∃ L, runItem ctx G.1 G.2 = .ok L ∧ em ∈ L ∧ (L ≠ [] → Has ctx G.1 G.2.source) := by
  have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) =>
      runItem ctx p.1 p.2 = .ok L ∧ Good p.1 p.2.target L ∧ (Has ctx p.1 p.2.source ↔ L ≠ []))
    (lowerItems (official t.row)) _
    (fun p hp => ok_and (ok_eq _) (runItem_good hctx p.1 (lower_itemOK (ctx := ctx) hp).2.2.1 p.2
      (lower_itemOK (ctx := ctx) hp).1)) vs hvs
  obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
  obtain ⟨G', hG', hrun, hgood, hhas⟩ := forall₂_mem_right hF L hL
  obtain ⟨_, hst, _, _⟩ := lower_itemOK (ctx := ctx) hG'
  have hin' : inRegion G'.1 G'.2.source em.row = true := by rw [hst]; exact hgood.2.1 em hemL
  obtain rfl := lowerItems_eq_of_common hG' hG hin' hin
  exact ⟨L, hrun, hemL, hhas.mpr⟩

/-- The top of a column in a region, as the highest row of the column in it. -/
theorem topIn_of_highest {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c d : Nat}
    {b : Row} {v : Ref × Cell} (hv : v ∈ realNodes M c) (hin : inRegion d b (official v.2.row) = true)
    (hmax : ∀ w ∈ realNodes M c, inRegion d b (official w.2.row) = true →
      official w.2.row ≤ official v.2.row) :
    topIn M c d b = some v := by
  obtain ⟨a, ha⟩ := filter_last_exists (P := fun p => inRegion d b (official p.2.row)) hv hin
  have ha' : topIn M c d b = some a := ha
  obtain ⟨hamem, hain, _⟩ := topIn_spec ha'
  have h1 := topIn_row_max hb ha' hv hin
  have h2 := hmax a hamem hain
  rw [ha', realNodes_eq_of_row hb hamem hv (le_antisymm h2 h1)]

/-! ## The parent column of an upper node -/

/-- **The parent column `Y = φ_i(l)` of an upper node with leg `l ≥ c_r`** is a new column:
the copy of `l` in block `i` (`l > c_r`), or of `x₀` in block `i - 1` (`l = c_r`). -/
theorem leg_newColumn {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (hNC : NewColumn s n R M t root i x) (hi : 1 ≤ i) {l : Nat}
    (hlx : l < Classification.upperColumn (colCtx M R root i x)) (hl' : root.column ≤ l) :
    x ≠ M.size - 1 ∧ ∃ i' x'', NewColumn s n R M t root i' x'' ∧
      legCol (colCtx M R root i x) l = x'' + (M.size - 1 - root.column) * i' ∧
      ((root.column < l ∧ x'' = l ∧ i' = i) ∨
        (l = root.column ∧ x'' = M.size - 1 ∧ i' + 1 = i)) := by
  set w := M.size - 1 - root.column with hw
  have hcr := hNC.top.lt
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hNC.mem
  have hxne : x ≠ M.size - 1 := by
    intro hx
    rw [upperColumn_last hx] at hlx
    omega
  have hlx' : l < x := by
    rw [upperColumn_inner hxne] at hlx
    exact hlx
  have hleg : legCol (colCtx M R root i x) l = l + w * i := by
    unfold legCol
    rw [if_pos (show (colCtx M R root i x).rootColumn ≤ l from hl')]
    rfl
  have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi
  have hY0 : M.size - 1 ≤ l + w * i := by omega
  have hYs : l + w * i < R.size := by
    have := hNC.lt
    rw [← hw] at this
    omega
  obtain ⟨i', x'', hNC', hY⟩ := newColumn_at hNC hY0 hYs
  rw [← hw] at hY
  obtain ⟨hx''gt, hx''le⟩ := mem_blockColumns hcr hNC'.mem
  refine ⟨hxne, i', x'', hNC', by rw [hleg, hY], ?_⟩
  rcases Nat.eq_or_lt_of_le hl' with heq | hlt
  · subst heq
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have hdec := decomp_unique (w := w) (a := w - 1) (b := x'' - root.column - 1)
      (i := i0) (j := i') (by omega) (by omega) (by
        have e1 : w * (i0 + 1) = w * i0 + w := Nat.mul_succ w i0
        rw [e1] at hY
        generalize w * i0 = P at hY ⊢
        generalize w * i' = Q at hY ⊢
        omega)
    exact Or.inr ⟨rfl, by omega, by omega⟩
  · have hdec := decomp_unique (w := w) (a := l - root.column - 1) (b := x'' - root.column - 1)
      (i := i) (j := i') (by omega) (by omega) (by
        generalize w * i = P at hY ⊢
        generalize w * i' = Q at hY ⊢
        omega)
    exact Or.inl ⟨hlt, by omega, by omega⟩

/-! ## The seam at `τ` -/

/-- **The jump law at the seam `θ = τ`.** -/
theorem seamTauHolds : SeamTauHolds := by
  intro s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hθτ hleft hθ hHB
  have hb := hNC.top.build
  have hctx := hNC.runCtx
  have hsorted := assemble_sorted hasm
  obtain ⟨hU1, hU2⟩ := upper_facts hus
  have hL := lower_lt hctx hvs
  have hlt : (vs.flatten ++ us)[k].row < (vs.flatten ++ us)[k + 1].row := by rw [hθ]; exact Row.lt_bump _ _
  have hmem := getElem_mem_right (A := vs.flatten) (B := us) hk (by omega)
  obtain ⟨q, hq, hqrow, hτθ, l', hl', hl'e⟩ := hU1 _ hmem
  rw [hleft] at hl'e
  obtain rfl := Option.some.inj hl'e
  have hqθ : official q.2.row ≠ 0 := by
    rw [hqrow]
    intro h0
    rw [h0] at hlt
    exact absurd hlt (not_lt.mpr (Row.zero_le _))
  obtain ⟨σ, l'', ps, hσmem, hσlt, hσmax, hleft'', hlx, hHBs, hpsσ, hθs⟩ := source_edge hb hq hqθ
  rw [hl'] at hleft''
  obtain rfl := Except.ok.inj hleft''
  rw [hqrow] at hσlt hσmax hHBs hθs
  -- the lower row is the top of `X` below `(official t.row)`
  have hkL' : k < vs.flatten.length := by omega
  have hlτ : (vs.flatten ++ us)[k].row < (official t.row) := hL _ (getElem_mem_left (A := vs.flatten) (B := us) (by omega) hkL')
  have hpX : HighestBelow ((vs.flatten ++ us).map Emit.row) (official t.row) (vs.flatten ++ us)[k].row := by
    refine ⟨List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩, hlτ, ?_⟩
    intro r hr hrτ
    obtain ⟨em, hem, rfl⟩ := List.mem_map.mp hr
    exact le_of_consecutive hsorted hk hem (lt_of_lt_of_le hrτ hτθ)
  obtain ⟨a0, ha0⟩ := topBelow_exists hctx
  have ha0' := highestBelow_of_topBelow ha0
  have hsame0 := lower_top_sameL hctx hvs hus hpX ha0'
  have hστ : σ < (official t.row) := by rw [← hθτ]; exact hσlt
  -- `σ ≤ a₀`
  have hσa0 : σ ≤ a0 := by
    by_cases hx : x = M.size - 1
    · rw [upperColumn_last hx] at hσmem
      obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hσmem
      have hρt : ρ.2.row < t.row := by
        by_contra hn
        exact absurd hστ (not_lt.mpr (official_mono hNC.top.row_one_le (not_lt.mp hn)))
      obtain ⟨v, hv, hvrow⟩ := hNC.top.root_rows hρ hρt
      apply ha0'.2.2 _ _ hστ
      simp only [colCtx, Classification.ctxAt]
      rw [hx]
      exact List.mem_map.mpr ⟨v, hv, by rw [hvrow]⟩
    · rw [upperColumn_inner hx] at hσmem
      exact ha0'.2.2 _ hσmem hστ
  have ha0θ : a0 < (vs.flatten ++ us)[k + 1].row := lt_of_lt_of_le ha0'.2.1 hτθ
  have hθa0 : (vs.flatten ++ us)[k + 1].row = Row.bump a0 (Row.jump σ ps) := by
    rw [hθs]
    exact Row.bump_eq_of_jump_le (Row.jump_le_of_lt_bump hσa0 (by rw [← hθs]; exact ha0θ))
  have hja0 : Row.jump a0 ps = Row.jump σ ps := jump_of_lower hpsσ hσa0 ha0θ hθs rfl hθa0
  have hee : e = Row.jump σ ps := (bump_eq_bump (hθ.symm.trans hθs)).1
  rw [← hee] at hja0 hθa0
  have hK : Row.jump (official t.row) a0 = e + 1 := by
    rw [← hθτ, hθa0, Row.jump_comm, Row.jump_bump]
  -- the parent row
  have hpar := parent_cases hNC hi hlx hτθ hHBs hHB
  have hpsτ : ps < (official t.row) := lt_of_le_of_lt hpsσ hστ
  have hpps : Row.jump p ps ≤ e := by
    rcases hpar with rfl | ⟨_, _, hsame⟩
    · simp
    · have := Row.jump_triangle (official t.row) a0 ps
      unfold SameL at hsame
      omega
  have hla0 : Row.jump (vs.flatten ++ us)[k].row a0 ≤ e := by
    have := hsame0
    unfold SameL at this
    omega
  generalize hlamdef : (vs.flatten ++ us)[k].row = lam at hpX hla0 hsame0 ⊢
  apply jump_eq_of_coeffs
  · -- agreement above `e`
    have h1 := Row.jump_triangle lam a0 ps
    have h2 := Row.jump_triangle lam ps p
    rw [Row.jump_comm ps p] at h2
    exact Row.jump_le_iff.mp (by omega)
  · -- the difference at `e - 1`
    intro he
    obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hK' : Row.jump (official t.row) a0 = d + 2 := by rw [hK]
    -- `ps` is lower than `a₀` at `d`
    have hpsa0 : ps < a0 := lt_of_le_of_ne (hpsσ.trans hσa0) (by
      intro h; rw [h, Row.jump_self] at hja0; omega)
    have hpsd : ps.coeff d < a0.coeff d := by
      have := coeff_lt_of_lt hpsa0
      rw [Row.jump_comm, hja0] at this
      simpa using this
    -- the first item of `a₀`
    have hFmem := firstItem_mem ha0'.2.1 hK'
    have hFin : ∀ r, inRegion (d + 2) (firstItem (official t.row) a0 d).2.source r = true ↔
        Row.jump r a0 ≤ d + 1 := fun r => inRegion_firstItem hK'
    have hFit := (lower_itemOK (ctx := colCtx M R root i x) hFmem).1
    -- the top of `x` in the first item is `a₀`
    obtain ⟨va0, hva0, hva0row⟩ := List.mem_map.mp ha0'.1
    have hTopX : topIn M x (d + 2) (firstItem (official t.row) a0 d).2.source = some va0 := by
      apply topIn_of_highest hb hva0 ((hFin _).mpr (by rw [hva0row]; simp))
      intro w hw hwin
      rw [hva0row]
      exact ha0'.2.2 _ (List.mem_map.mpr ⟨w, hw, rfl⟩) (hFit.below _ hwin)
    -- the emission of `X` in the first item
    obtain ⟨LX, hrunX, hLXsub⟩ := first_output hvs hFmem
    obtain ⟨ascX, hascX, _, emX, hemX, hemXd, hemXin⟩ :=
      plain_emission hctx hFit rfl rfl hTopX LX hrunX
    have hlamin : inRegion (d + 2) (firstItem (official t.row) a0 d).2.target
        lam = true := (hFin _).mpr hla0
    have hemXE : emX.row ∈ (vs.flatten ++ us).map Emit.row :=
      List.mem_map.mpr ⟨emX, List.mem_append_left us (hLXsub emX hemX), rfl⟩
    have hemXτ : emX.row < official t.row := hL emX (hLXsub emX hemX)
    have hle : emX.row ≤ lam := hpX.2.2 emX.row hemXE hemXτ
    have hcoef : emX.row.coeff d ≤ lam.coeff d :=
      coeff_le_of_inRegion (d := d) hemXin hlamin hle
    have hva0d : (official va0.2.row).coeff d = a0.coeff d := by rw [hva0row]
    -- the height of the parent row
    suffices hpd : p.coeff d < lam.coeff d by
      intro h; rw [h] at hpd; exact lt_irrefl _ hpd
    rcases hpar with rfl | ⟨hpτ, _, hsame⟩
    · have : a0.coeff d ≤ emX.row.coeff d := by
        rw [hemXd, hva0d]; exact Nat.le_add_right _ _
      omega
    · -- the parent column is a new column `Y` of block `i`
      have hax : a0.coeff d ≤ emX.row.coeff d := by
        rw [hemXd, hva0d]; exact Nat.le_add_right _ _
      have hqτ : official q.2.row = official t.row := by rw [hqrow, hθτ]
      have hHBs' : HighestBelow (rowsOf M l) (official q.2.row) ps := by rw [hqrow]; exact hHBs
      have hpsF : Row.jump ps a0 ≤ d + 1 := by rw [Row.jump_comm, hja0]
      by_cases hlcr : l < root.column
      · -- `Y = l` is a column of `M(s)` and `p = ps`
        have hleg : legCol (colCtx M R root i x) l = l := by
          unfold legCol
          rw [if_neg (show ¬ (colCtx M R root i x).rootColumn ≤ l from by
            simp only [colCtx, Classification.ctxAt]; omega)]
        rw [hleg, rowsOf_congr (hNC.inv.1 l (by have := hNC.top.lt; omega)).symm] at hHB
        have := highestBelow_unique hHB hHBs
        subst this
        omega
      · have hl'' : root.column ≤ l := by omega
        obtain ⟨hxne, i', x'', hNC', hYeq, hcase⟩ := leg_newColumn hNC hi hlx hl''
        rw [upperColumn_inner hxne] at hq
        obtain ⟨vsY, usY, colY, hvsY, husY, hasmY, hrowsY⟩ := hNC'.emits
        rw [hYeq, hrowsY] at hHB
        obtain ⟨hUY1, _⟩ := upper_facts husY
        -- the parent row is emitted in the lower part of `Y`
        obtain ⟨emp, hemp, hemprow⟩ := List.mem_map.mp hHB.1
        have hemp' : emp ∈ vsY.flatten := by
          rcases List.mem_append.mp hemp with h | h
          · exact h
          · obtain ⟨_, _, _, hτ', _⟩ := hUY1 emp h
            rw [hemprow] at hτ'
            exact absurd hpτ (not_lt.mpr hτ')
        -- it lies in the first item of `a₀`
        have hpF : inRegion (d + 2) (firstItem (official t.row) a0 d).2.source emp.row = true := by
          rw [hFin, hemprow]
          have h1 : Row.jump (official t.row) ps ≤ d + 2 := by
            have := Row.jump_triangle (official t.row) a0 ps
            omega
          unfold SameL at hsame
          have h2 := Row.jump_triangle p ps a0
          omega
        have hctxY := hNC'.runCtx
        obtain ⟨LY, hrunY, hempLY, hHasY⟩ := mem_first_output hctxY hvsY hFmem hemp' hpF
        obtain ⟨v, hv, hvin⟩ := hHasY (List.ne_nil_of_mem hempLY)
        obtain ⟨aY, haY⟩ := filter_last_exists
          (P := fun p => inRegion (d + 2) (firstItem (official t.row) a0 d).2.source
            (official p.2.row)) hv hvin
        have haY' : topIn M x'' (d + 2) (firstItem (official t.row) a0 d).2.source = some aY := haY
        have hFitY := (lower_itemOK (ctx := colCtx M R root i' x'') hFmem).1
        obtain ⟨ascY, hascY, hupY, _⟩ := plain_emission hctxY hFitY rfl rfl haY' LY hrunY
        have hpY := hupY emp hempLY
        rw [hemprow] at hpY
        obtain ⟨haYmem, haYin, _⟩ := topIn_spec haY'
        -- the node of `ps`
        obtain ⟨vps, hvps, hvpsrow⟩ := List.mem_map.mp hHBs.1
        have hvpsF : inRegion (d + 2) (firstItem (official t.row) a0 d).2.source
            (official vps.2.row) = true := by rw [hvpsrow, hFin]; exact hpsF
        simp only [colCtx, Classification.ctxAt] at hascX hascY hemXd hpY
        rcases hcase with ⟨hlt, hx'', hi''⟩ | ⟨hlr, hx'', hii⟩
        · -- `Y` copies `l` in block `i`
          subst x'' i'
          have haYps : official aY.2.row = ps := by
            apply le_antisymm
            · exact hHBs.2.2 _ (List.mem_map.mpr ⟨aY, haYmem, rfl⟩)
                (lt_of_lt_of_le (hFit.below _ haYin) (by rw [hθτ]))
            · rw [← hvpsrow]; exact topIn_row_max hb haY' hvps hvpsF
          rw [haYps] at hpY
          cases ascY with
          | false =>
            simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hpY
            omega
          | true =>
            have hZ : ∀ ρ, topIn M root.column (d + 2) (firstItem (official t.row) a0 d).2.source =
                some ρ → referenceRow (official ρ.2.row) < official q.2.row := by
              intro ρ hρ
              rw [hqτ]
              exact lt_of_le_of_lt (referenceRow_le _) (hFit.below _ (topIn_spec hρ).2.1)
            have hX := ascends_of_leg hb (ctxX := colCtx M R root i x) (ctxY := colCtx M R root i l)
              rfl rfl rfl hq hqθ hl' hHBs' rfl hl'' hZ hascY
            simp only [colCtx, Classification.ctxAt] at hX
            rw [hascX] at hX
            obtain rfl := Except.ok.inj hX
            simp only [if_true] at hpY hemXd
            simp only [liftOf, colCtx, Classification.ctxAt] at hpY hemXd
            omega
        · -- `Y` copies `x₀` in block `i - 1`
          subst x''
          subst hlr
          obtain ⟨ρ, hρ⟩ := filter_last_exists
            (P := fun p => inRegion (d + 2) (firstItem (official t.row) a0 d).2.source
              (official p.2.row)) hvps hvpsF
          have hρ' : topIn M root.column (d + 2) (firstItem (official t.row) a0 d).2.source =
              some ρ := hρ
          obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ'
          have hρps : official ρ.2.row = ps := by
            apply le_antisymm
            · exact hHBs.2.2 _ (List.mem_map.mpr ⟨ρ, hρmem, rfl⟩)
                (lt_of_lt_of_le (hFit.below _ hρin) (by rw [hθτ]))
            · rw [← hvpsrow]; exact topIn_row_max hb hρ' hvps hvpsF
          have hX := ascends_of_root_leg hb (ctxX := colCtx M R root i x) rfl hq hqθ hl' hHBs'
            hρmem hρps.le
          simp only [colCtx, Classification.ctxAt] at hX
          rw [hρ'] at hascX
          rw [hascX] at hX
          obtain rfl := Except.ok.inj hX
          -- the root cut: `h_ρ ≤ h_κ`
          obtain ⟨κ, hκ, hle⟩ := Top.rootCut_region hNC.top hFit.below hρ'
          have hκ' : topIn M (M.size - 1) (d + 2) (firstItem (official t.row) a0 d).2.source =
              some κ := hκ
          rw [haY'] at hκ'
          replace hκ := hκ'
          obtain rfl := Option.some.inj hκ
          have hRK : ps.coeff d ≤ (official aY.2.row).coeff d := by
            rw [← hρps]
            exact coeff_le_of_inRegion hρin haYin hle
          simp only [if_true, liftOf, colCtx, Classification.ctxAt, hρ', haY', heightOf, height_eq,
            hρps] at hpY hemXd
          have hmul : ((official aY.2.row).coeff d - ps.coeff d) * i =
              ((official aY.2.row).coeff d - ps.coeff d) * i' +
                ((official aY.2.row).coeff d - ps.coeff d) := by
            rw [← hii, Nat.mul_succ]
          have hpY' : p.coeff d ≤ (official aY.2.row).coeff d +
              ((official aY.2.row).coeff d - ps.coeff d) * i' := by
            split_ifs at hpY <;> omega
          rw [hmul] at hemXd
          generalize ((official aY.2.row).coeff d - ps.coeff d) * i' = P at hemXd hpY'
          omega

end OmegaY.Official.Recon.JumpLaw

namespace OmegaY.Official.Recon.JumpLaw

/-- **The jump law from the lower pairs alone.** -/
theorem jumpLawHolds_of_lowerPairs (hlow : LowerPairsHolds) : RowLaw.JumpLawHolds :=
  jumpLawHolds_of_parts seamTauHolds hlow

/-- **The row law from the lower pairs alone.** -/
theorem rowLawHolds_of_lowerPairs (hlow : LowerPairsHolds) : RowLawHolds :=
  RowLaw.rowLawHolds_of_jumpLaw (jumpLawHolds_of_lowerPairs hlow)

end OmegaY.Official.Recon.JumpLaw

#print axioms OmegaY.Official.Recon.JumpLaw.seamTauHolds
#print axioms OmegaY.Official.Recon.JumpLaw.jumpLawHolds_of_lowerPairs
#print axioms OmegaY.Official.Recon.JumpLaw.rowLawHolds_of_lowerPairs
