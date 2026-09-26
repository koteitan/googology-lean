/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawBlock0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawSource

set_option backward.do.legacy false

/-!
# The jump law in block `0`

In block `0` (the column `x₀` of the output) the lift `Δ = (h_κ - h_ρ)·0` vanishes, so
every item is copied onto itself (`IdItem`): the lower part emits exactly the nodes of
the column `x₀` of `M(s)` below `τ`, with their rows and legs (`runItem_id`,
`lower_id`); the upper part emits the nodes of the root column `c_r` at or above `τ`.

The jump law of this column then follows from the row law of `M(s)`
(`source_edge`) and the transfer lemma `jump_of_lower`: the new node `θ` is a node `u⁺`
of `M(s)`; its parent column `l < x₀` is a column of `M(s)` itself; and the row `σ` of
the node below `u⁺` is emitted too (for `u⁺` in the root column below `τ`, by
`Top.root_rows`), so `σ ≤ λ`.
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw

/-! ## Covering `[0, τ)` by the first items -/

theorem chainTo_cover {β γ : Row} : ∀ {l : List (Nat × Row)}, RowLaw.ChainTo β γ l →
    ∀ r, β ≤ r → r < γ → ∃ q ∈ l, inRegion q.1 q.2 r = true
  | [], h, r, h1, h2 => by
    rw [h.nil rfl] at h1
    exact absurd h2 (not_lt.mpr h1)
  | q :: l, h, r, h1, h2 => by
    by_cases hr : r < Row.bump q.2 (q.1 - 1)
    · refine ⟨q, List.mem_cons_self, inRegion_of_between ?_ hr⟩
      rw [h.head_eq]
      exact h1
    · obtain ⟨q', hq', hin⟩ := chainTo_cover h.tail r (not_lt.mp hr) h2
      exact ⟨q', List.mem_cons_of_mem _ hq', hin⟩

theorem lowerItems_cover (τ : Row) {r : Row} (hr : r < τ) :
    ∃ p ∈ lowerItems τ, inRegion p.1 p.2.source r = true := by
  obtain ⟨q, hq, hin⟩ := chainTo_cover (lowerItems_chainTo τ) r (Row.zero_le r) hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨_, hst, _⟩ := lower_itemOK (ctx := ⟨#[], #[], 0, 0, 0, 0, 0⟩) hp
  exact ⟨p, hp, by rw [hst]; exact hin⟩

theorem forall₂_mem_left {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ x ∈ xs, ∃ y ∈ ys, P x y
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨y, hy, hxy⟩ := forall₂_mem_left rest x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

/-! ## The identity copy -/

/-- An item copied onto itself. -/
structure IdItem (d : Nat) (it : Item) : Prop where
  st : it.source = it.target
  off : it.offset = 0
  cut : it.cutBottom = false
  clean : ∀ C, it.clean = some C → d = 1 ∧ C = it.source

/-- The identity copy of the nodes of column `x` in the region `(d, S)`. -/
def IdOut (ctx : Context) (d : Nat) (S : Row) (L : List Emit) : Prop :=
  (∀ em ∈ L, ∃ p ∈ realNodes ctx.source ctx.x, official p.2.row = em.row ∧
      inRegion d S em.row = true ∧
      (em.row ≠ 0 → ∃ l, leftColumn p.2 = .ok l ∧ em.leftColumn = some l)) ∧
  (∀ p ∈ realNodes ctx.source ctx.x, inRegion d S (official p.2.row) = true →
      ∃ em ∈ L, em.row = official p.2.row)

theorem levelOne_id (ctx : Context) (it : Item) (hit : IdItem 1 it) :
    Ok (levelOne ctx it) (IdOut ctx 1 it.source) := by
  unfold levelOne
  cases hn : nodeAt ctx.source ctx.x it.source with
  | none =>
    refine ok_pure ⟨by simp, ?_⟩
    intro p hp hin
    exact absurd (inRegion_one_iff.mp hin) (nodeAt_none hn p hp)
  | some q =>
    obtain ⟨hq, hrow⟩ := nodeAt_spec hn
    obtain ⟨qref, qcell⟩ := q
    simp only at hq hrow ⊢
    have hall : ∀ (lc : Option Nat), ∀ p ∈ realNodes ctx.source ctx.x,
        inRegion 1 it.source (official p.2.row) = true →
        ∃ em ∈ [({ row := it.target, leftColumn := lc } : Emit)], em.row = official p.2.row := by
      intro lc p _ hin
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [← hit.st, inRegion_one_iff.mp hin]
    have hone : ∀ (lc : Option Nat),
        (it.target ≠ 0 → ∃ l, leftColumn qcell = .ok l ∧ lc = some l) →
        IdOut ctx 1 it.source [({ row := it.target, leftColumn := lc } : Emit)] := by
      intro lc hlc
      refine ⟨?_, hall lc⟩
      intro em hem
      rw [List.mem_singleton.mp hem]
      refine ⟨(qref, qcell), hq, by rw [hrow, hit.st], ?_, hlc⟩
      rw [← hit.st]
      exact inRegion_one_iff.mpr rfl
    cases hc : it.clean with
    | some C =>
      obtain ⟨_, rfl⟩ := hit.clean C hc
      simp only [hn]
      refine ok_bind (ok_eq _) (fun l hl => ok_pure (hone _ (fun _ => ⟨l, hl, rfl⟩)))
    | none =>
      simp only
      split
      · rename_i h0
        exact ok_pure (hone _ (fun h => absurd (by rw [← hit.st]; exact h0) h))
      · exact ok_bind (ok_eq _) (fun l hl => ok_pure (hone _ (fun _ => ⟨l, hl, rfl⟩)))

/-- The children of an item copied onto itself in block `0`. -/
def ChildId (ctx : Context) (d : Nat) (it : Item) (children : List Item) : Prop :=
  ∃ (N : Nat) (F : Nat → Item), children = (List.range N).map F ∧
    (∀ j, IdItem (d + 1) (F j) ∧ (F j).source = slot (d + 2) it.source j) ∧
    ∀ p ∈ realNodes ctx.source ctx.x, inRegion (d + 2) it.source (official p.2.row) = true →
      (official p.2.row).coeff d < N

theorem rho_slot {ρ S : Row} (h : inRegion 2 S ρ = true) : slot 2 S (ρ.coeff 0) = ρ := by
  apply row_ext
  intro k
  rw [coeff_slot]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    exact (inRegion_iff'.mp h k (by omega)).symm

theorem childItems_id {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (h0 : ctx.block = 0) {d : Nat} {it : Item}
    (hit : IdItem (d + 2) it) :
    Ok (childItems ctx (d + 2) it) (ChildId ctx d it) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  unfold childItems
  dsimp only
  split
  · rename_i hnone
    refine ok_pure ⟨0, fun j => ⟨slot (d + 2) it.source j, slot (d + 2) it.source j, none, 0,
      false⟩, by simp, fun j => ⟨⟨rfl, rfl, rfl, by simp⟩, rfl⟩, ?_⟩
    intro p hp hin
    have := topIn_none hnone p hp
    rw [hin] at this
    cases this
  · rename_i aRef aCell hA
    have hbound : ∀ p ∈ realNodes ctx.source ctx.x,
        inRegion (d + 2) it.source (official p.2.row) = true →
        (official p.2.row).coeff d < (official aCell.row).coeff d + 1 := by
      intro p hp hin
      have := coeff_le_of_inRegion hin (topIn_spec hA).2.1 (topIn_row_max hb hA hp hin)
      simp only at this
      omega
    have hTdef : height (d + 2) (official aCell.row) = (official aCell.row).coeff d := height_eq _ _
    have hsl : slot (d + 2) it.target = slot (d + 2) it.source := by rw [hit.st]
    refine ok_bind (ok_eq _) (fun asc hasc => ?_)
    split
    · -- case 1
      split
      · exact ok_throw_bind _ _
      · refine ok_pure ⟨_, _, rfl, fun j => ⟨⟨by simp [hsl], rfl, rfl, by simp⟩, rfl⟩, ?_⟩
        rw [hTdef]
        exact hbound
    · rename_i hasc'
      have hasc_true : asc = true := by simpa using hasc'
      subst hasc_true
      obtain ⟨⟨ρRef, ρCell⟩, hρ, _, _, _⟩ := node_of_ascends hctx hasc
      obtain ⟨_, hρin, _⟩ := topIn_spec hρ
      rw [hρ]
      generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB
      simp only [heightOf, height_eq]
      split
      · rename_i hcl
        split
        · -- case 2 with lift `0`
          rw [h0]
          simp only [Nat.cast_zero, mul_zero, add_zero, Int.sub_zero, ne_eq,
            not_true_eq_false, false_and, decide_false]
          generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
          have he : (e = 1 ∧ d = 0) ∨ e = 0 := by rw [← hedef]; split <;> omega
          refine ok_pure ⟨_, _, rfl, ?_, ?_⟩
          · intro j
            split_ifs with h1 h2
            · exact ⟨⟨by simp [hsl], rfl, rfl, by simp⟩, rfl⟩
            · -- the copied root row: `d = 0` and `j = h_ρ`
              have hd : d = 0 := by omega
              subst hd
              have hj : j = (official ρCell.row).coeff 0 := by omega
              subst hj
              refine ⟨⟨by simp [hsl], rfl, by simp, ?_⟩, rfl⟩
              intro C hC
              simp only [Option.some.injEq] at hC
              exact ⟨rfl, by rw [← hC]; exact (rho_slot hρin).symm⟩
            · refine ⟨⟨by simp [hsl], rfl, rfl, by simp⟩, ?_⟩
              simp
          · intro p hp hin
            have := hbound p hp hin
            omega
        · -- case 3 cannot occur
          rename_i hcut
          exact absurd (by simpa using hcut) (by simp [hit.cut])
      · -- case 4 cannot occur
        rename_i C hC
        exact absurd (hit.clean C hC).1 (by omega)

/-- **The identity copy in block `0`.** -/
theorem runItem_id {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (h0 : ctx.block = 0) :
    ∀ d, 1 ≤ d → ∀ it, IdItem d it → Ok (runItem ctx d it) (IdOut ctx d it.source) := by
  have hb : Canonical.build s = .ok ctx.source := hctx.top.build
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd1 it hit
    match d, ih, hd1 with
    | 1, _, _ =>
      rw [runItem]
      exact levelOne_id ctx it hit
    | d + 2, ih, _ =>
      rw [runItem]
      refine ok_bind (childItems_id hctx h0 hit) (fun children hch => ?_)
      obtain ⟨N, F, rfl, hF, hN⟩ := hch
      refine ok_bind (ok_mapM₂ (fun c L => IdOut ctx (d + 1) c.source L) ((List.range N).map F)
        (runItem ctx (d + 1)) ?_) (fun outs houts => ok_pure ?_)
      · intro a ha
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
        exact ih (d + 1) (by omega) (by omega) (F j) (hF j).1
      · obtain ⟨hlen, hget⟩ := forall₂_getElem houts
        simp only [List.length_map, List.length_range] at hlen
        have hP : ∀ j (hj : j < outs.length), IdOut ctx (d + 1) (slot (d + 2) it.source j) outs[j] := by
          intro j hj
          have := hget j (by simp; omega) hj
          simp only [List.getElem_map, List.getElem_range] at this
          rw [(hF j).2] at this
          exact this
        refine ⟨?_, ?_⟩
        · intro em hem
          obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
          obtain ⟨p, hp, hrow, hin, hleg⟩ := (hP j hj).1 em hemL
          exact ⟨p, hp, hrow, inRegion_of_slot hin, hleg⟩
        · intro p hp hin
          have hc := hN p hp hin
          have hj : (official p.2.row).coeff d < outs.length := by omega
          obtain ⟨em, hem, hrow⟩ := (hP _ hj).2 p hp (inRegion_slot_iff.mpr ⟨hin, rfl⟩)
          exact ⟨em, List.mem_flatten.mpr ⟨_, List.getElem_mem hj, hem⟩, hrow⟩

/-- **The lower part in block `0`.** -/
theorem lower_id {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (h0 : ctx.block = 0) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) :
    (∀ em ∈ vs.flatten, ∃ p ∈ realNodes ctx.source ctx.x, official p.2.row = em.row ∧
      em.row < official t.row ∧
      (em.row ≠ 0 → ∃ l, leftColumn p.2 = .ok l ∧ em.leftColumn = some l)) ∧
    (∀ p ∈ realNodes ctx.source ctx.x, official p.2.row < official t.row →
      ∃ em ∈ vs.flatten, em.row = official p.2.row) := by
  have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) => IdOut ctx p.1 p.2.source L)
    (lowerItems (official t.row)) _
    (fun p hp => runItem_id hctx h0 p.1 (lower_itemOK (ctx := ctx) hp).2.2.1 p.2
      (by
        obtain ⟨_, hst, _⟩ := lower_itemOK (ctx := ctx) hp
        obtain ⟨k, j, _, _, rfl⟩ := mem_lowerItems hp
        exact ⟨rfl, rfl, rfl, by simp⟩)) vs hvs
  refine ⟨?_, ?_⟩
  · intro em hem
    obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
    obtain ⟨p, hp, hPL⟩ := forall₂_mem_right hF L hL
    obtain ⟨q, hq, hrow, hin, hleg⟩ := hPL.1 em hemL
    have hbelow := (lower_itemOK (ctx := ctx) hp).1.below
    obtain ⟨_, hst, _⟩ := lower_itemOK (ctx := ctx) hp
    exact ⟨q, hq, hrow, hbelow _ hin, hleg⟩
  · intro q hq hlt
    obtain ⟨p, hp, hin⟩ := lowerItems_cover (official t.row) hlt
    obtain ⟨L, hL, hPL⟩ := forall₂_mem_left hF p hp
    obtain ⟨em, hem, hrow⟩ := hPL.2 q hq hin
    exact ⟨em, List.mem_flatten.mpr ⟨L, hL, hem⟩, hrow⟩

end OmegaY.Official.Recon.JumpLaw

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw

/-! ## Facts shared by all new columns -/

theorem NewColumn.runCtx {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (h : NewColumn s n R M t root i x) : RunCtx s (colCtx M R root i x) t root := by
  obtain ⟨hgt, hle⟩ := mem_blockColumns h.top.lt h.mem
  refine ⟨h.top, rfl, rfl, hgt, hle, ?_⟩
  simp only [colCtx, Classification.ctxAt, Array.size_extract]
  have := h.lt
  omega

theorem realNodes_congr {M M' : Mountain} {c : Nat} (h : M[c]? = M'[c]?) :
    realNodes M c = realNodes M' c := by
  unfold realNodes
  rw [h]

theorem rowsOf_congr {M M' : Mountain} {c : Nat} (h : M[c]? = M'[c]?) :
    rowsOf M c = rowsOf M' c := by
  unfold rowsOf
  rw [realNodes_congr h]

/-- **The upper part** emits the nodes of the column `x'` at or above `τ`, with their legs. -/
theorem upper_facts {ctx : Context} {τ : Row} {us : List Emit} (hus : UpperRun ctx τ us) :
    (∀ em ∈ us, ∃ p ∈ realNodes ctx.source (Classification.upperColumn ctx),
      official p.2.row = em.row ∧ τ ≤ em.row ∧
      ∃ l, leftColumn p.2 = .ok l ∧ em.leftColumn = some l) ∧
    (∀ p ∈ realNodes ctx.source (Classification.upperColumn ctx), τ ≤ official p.2.row →
      ∃ em ∈ us, em.row = official p.2.row) := by
  have hF := ok_mapM₂ (fun (x : Ref × Cell) (em : Emit) =>
      em.row = official x.2.row ∧ ∃ l, leftColumn x.2 = .ok l ∧ em.leftColumn = some l) _ _
    (fun x _ => by
      intro em hem
      cases hl : leftColumn x.2 with
      | error e => rw [hl] at hem; cases hem
      | ok v =>
        rw [hl] at hem
        cases hem
        exact ⟨rfl, v, rfl, rfl⟩) us hus
  refine ⟨?_, ?_⟩
  · intro em hem
    obtain ⟨p, hp, hrow, hleg⟩ := forall₂_mem_right hF em hem
    obtain ⟨hp', hτ⟩ := List.mem_filter.mp hp
    exact ⟨p, hp', hrow.symm, by rw [hrow]; simpa using hτ, hleg⟩
  · intro p hp hτ
    obtain ⟨em, hem, hrow, _⟩ := forall₂_mem_left hF p
      (List.mem_filter.mpr ⟨hp, by simpa using hτ⟩)
    exact ⟨em, hem, hrow⟩

/-! ## Block `0` -/

/-- **The jump law in block `0`.** -/
theorem colJump_block0 {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {x : Nat} (hNC : NewColumn s n R M t root 0 x) {vs : List (List Emit)} {us : List Emit}
    (hvs : LowerRun (colCtx M R root 0 x) (official t.row) vs)
    (hus : UpperRun (colCtx M R root 0 x) (official t.row) us) {col : Column}
    (hasm : assemble (colCtx M R root 0 x) (vs.flatten ++ us) = .ok col) :
    ColJump (colCtx M R root 0 x) R (vs.flatten ++ us) := by
  have hctx := hNC.runCtx
  have hb := hNC.top.build
  have hx : x = M.size - 1 := by
    have := hNC.mem
    simp [blockColumns] at this
    exact this
  subst hx
  set ctx := colCtx M R root 0 (M.size - 1) with hctxdef
  have hsrc : ctx.source = M := rfl
  have hxc : ctx.x = M.size - 1 := rfl
  have hup : Classification.upperColumn ctx = root.column := by
    simp [Classification.upperColumn, hctxdef, colCtx, Classification.ctxAt]
  set τ := official t.row with hτdef
  obtain ⟨hE1, hE2⟩ := lower_id hctx rfl hvs
  obtain ⟨hU1, hU2⟩ := upper_facts hus
  rw [hup, hsrc] at hU1 hU2
  rw [hsrc, hxc] at hE1 hE2
  have hsorted := assemble_sorted hasm
  intro k hk l e p hleft hθ hHB
  have hlt : (vs.flatten ++ us)[k].row < (vs.flatten ++ us)[k + 1].row := by rw [hθ]; exact Row.lt_bump _ _
  have hθ0 : (vs.flatten ++ us)[k + 1].row ≠ 0 := by
    intro h0
    rw [h0] at hlt
    exact absurd hlt (not_lt.mpr (Row.zero_le _))
  -- every emitted row of a node of `M(s)` is emitted
  have hemit : ∀ r, (r ∈ rowsOf M (M.size - 1) ∧ r < τ) ∨ (r ∈ rowsOf M root.column ∧ τ ≤ r) →
      ∃ em ∈ vs.flatten ++ us, em.row = r := by
    rintro r (⟨hr, hrτ⟩ | ⟨hr, hrτ⟩)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      obtain ⟨em, hem, hrow⟩ := hE2 q hq hrτ
      exact ⟨em, List.mem_append_left _ hem, hrow⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      obtain ⟨em, hem, hrow⟩ := hU2 q hq hrτ
      exact ⟨em, List.mem_append_right _ hem, hrow⟩
  -- the source node of the new node
  have hmem : (vs.flatten ++ us)[k + 1] ∈ vs.flatten ++ us := List.getElem_mem hk
  obtain ⟨c, q, hq, hqrow, hqleft, hcase⟩ : ∃ c, ∃ q ∈ realNodes M c,
      official q.2.row = (vs.flatten ++ us)[k + 1].row ∧ leftColumn q.2 = .ok l ∧
      ((c = M.size - 1 ∧ (vs.flatten ++ us)[k + 1].row < τ) ∨ (c = root.column ∧ τ ≤ (vs.flatten ++ us)[k + 1].row)) := by
    rcases List.mem_append.mp hmem with hm | hm
    · obtain ⟨q, hq, hrow, hτ', hleg⟩ := hE1 _ hm
      obtain ⟨l', hl', hl'e⟩ := hleg hθ0
      rw [hleft] at hl'e
      obtain rfl := Option.some.inj hl'e
      exact ⟨_, q, hq, hrow, hl', Or.inl ⟨rfl, hτ'⟩⟩
    · obtain ⟨q, hq, hrow, hτ', l', hl', hl'e⟩ := hU1 _ hm
      rw [hleft] at hl'e
      obtain rfl := Option.some.inj hl'e
      exact ⟨_, q, hq, hrow, hl', Or.inr ⟨rfl, hτ'⟩⟩
  have hqθ : official q.2.row ≠ 0 := by rw [hqrow]; exact hθ0
  obtain ⟨σ, l', ps, hσmem, hσlt, _, hleft', hl'c, hHBs, hpsσ, hθs⟩ := source_edge hb hq hqθ
  rw [hqleft] at hleft'
  obtain rfl := Except.ok.inj hleft'
  have hcx : c ≤ M.size - 1 := by
    rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact le_rfl
    · exact hNC.top.lt.le
  -- the parent column is a column of `M(s)`
  have hlegcol : legCol ctx l = l := by
    simp only [legCol, hctxdef, colCtx, Classification.ctxAt, Nat.mul_zero, Nat.add_zero]
    split <;> rfl
  have hrows : rowsOf R l = rowsOf M l :=
    rowsOf_congr (hNC.inv.1 l (by omega)).symm
  rw [hlegcol, hrows] at hHB
  rw [← hqrow] at hHB
  obtain rfl := highestBelow_unique hHB hHBs
  -- the row below the source node is emitted
  obtain ⟨em, hem, hemrow⟩ : ∃ em ∈ vs.flatten ++ us, em.row = σ := by
    apply hemit
    rcases hcase with ⟨rfl, hθτ⟩ | ⟨rfl, hθτ⟩
    · exact Or.inl ⟨hσmem, lt_trans hσlt (by rw [hqrow]; exact hθτ)⟩
    · by_cases hστ : τ ≤ σ
      · exact Or.inr ⟨hσmem, hστ⟩
      · left
        obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hσmem
        have hρt : ρ.2.row < t.row := by
          by_contra hn
          exact hστ (official_mono hNC.top.row_one_le (not_lt.mp hn))
        obtain ⟨v, hv, hvrow⟩ := hNC.top.root_rows hρ hρt
        refine ⟨List.mem_map.mpr ⟨v, hv, by rw [hvrow]⟩, lt_of_not_ge hστ⟩
  have hσl : σ ≤ (vs.flatten ++ us)[k].row := by
    rw [← hemrow]
    exact le_of_consecutive hsorted hk hem (by rw [hemrow, ← hqrow]; exact hσlt)
  exact jump_of_lower hpsσ hσl hlt (by rw [← hqrow]; exact hθs) rfl hθ

end OmegaY.Official.Recon.JumpLaw

#print axioms OmegaY.Official.Recon.JumpLaw.colJump_block0
