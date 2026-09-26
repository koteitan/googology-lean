/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/FirstEmit.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `topIn_zero_exists` the goal is beta-reduced before `rw [hrow]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RootCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Search

set_option backward.do.legacy false

/-!
# The first emitted node of a new column

Every column `X = x + i·w` made by `Official.copyColumn` begins with the node of the
official row `0` whose source leg is absent or the column `x - 1`: the item processing
of notes/03 §2.3–§2.4 starts with the region `[0, ω^{len τ - 1})` and always descends to
slot `0` first. On this path

* a plain item (no copied root row) keeps source and target `0`;
* a copied root row `C` is always the row of the top of the root column in the current
  region (so `C = 0` on the bottom row, whose leg is `x - 1`);
* case 2 never cuts the bottom of the slot-`0` child and never has an empty list of
  children, because `h_ρ ≤ h_κ` (`Top.rootCut`) and, at levels `≥ 3` with `h_ρ = 0`,
  `h_κ ≥ 1` (`Top.cut_pos`).

`FirstEmit.lean` proves `BottomHolds` of `Reduction.lean` this way (`bottomHolds`).
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Dimension

/-! ## The run context of a column -/

/-- The data of `expandDiagram` fixed while one column is copied. -/
structure RunCtx (s : List Nat) (ctx : Context) (t : Cell) (root : Ref) : Prop where
  top : Top s ctx.source t root
  last : ctx.lastColumn = ctx.source.size - 1
  rootc : ctx.rootColumn = root.column
  xgt : ctx.rootColumn < ctx.x
  xle : ctx.x ≤ ctx.lastColumn
  size : ctx.result.size = ctx.x + ctx.width * ctx.block

/-- The bottom node of a column of a canonical mountain. -/
theorem bottom_node {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c : Nat}
    (hc : c < M.size) :
    ∃ b : Cell, M[c][1]? = some b ∧ b.row = 1 ∧
      b.left = (if c = 0 then none else some ⟨c - 1, 0⟩) ∧
      (realNodes M c).head? = some (⟨c, 1⟩, b) := by
  have hV := build_valid_of_success hb
  obtain ⟨b, hb1, hleft⟩ := build_bottom_legs hb c hc
  refine ⟨b, hb1, (hV c hc).bottom_row b hb1, hleft, ?_⟩
  rw [List.head?_eq_getElem?, realNodes_getElem?, Array.getElem?_eq_getElem hc]
  simp only [Option.bind_some, zero_add, hb1, Option.map_some]

theorem nodeAt_zero {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c : Nat}
    (hc : c < M.size) :
    ∃ b : Cell, nodeAt M c 0 = some (⟨c, 1⟩, b) ∧ b.row = 1 ∧
      b.left = (if c = 0 then none else some ⟨c - 1, 0⟩) := by
  obtain ⟨b, _, hrow, hleft, hhead⟩ := bottom_node hb hc
  refine ⟨b, ?_, hrow, hleft⟩
  unfold nodeAt
  cases h : realNodes M c with
  | nil => rw [h] at hhead; cases hhead
  | cons a rest =>
    rw [h] at hhead
    obtain rfl := Option.some.inj hhead
    rw [List.find?_cons_of_pos]
    simp [hrow, official_one]

theorem bottom_mem {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c : Nat}
    (hc : c < M.size) : ∃ b : Cell, (⟨c, 1⟩, b) ∈ realNodes M c ∧ official b.row = 0 := by
  obtain ⟨b, _, hrow, _, hhead⟩ := bottom_node hb hc
  exact ⟨b, List.mem_of_head? hhead, by rw [hrow]; exact official_one⟩

theorem topIn_zero_exists {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {c : Nat} (hc : c < M.size) (d : Nat) : ∃ ρ, topIn M c d 0 = some ρ := by
  obtain ⟨b, hmem, hrow⟩ := bottom_mem hb hc
  unfold topIn
  exact filter_last_exists (P := fun p => inRegion d 0 (official p.2.row)) hmem
    (by beta_reduce; rw [hrow]; exact inRegion_zero_zero d)

theorem leftColumn_of {cell : Cell} {r : Ref} (h : cell.left = some r) :
    leftColumn cell = .ok r.column := by
  simp [leftColumn, Expansion.leftOf, h, liftE, Except.mapError, bind, Except.bind, pure,
    Except.pure]

/-! ## Items on the first path -/

/-- An item on the path of the first emitted node. -/
def FP (ctx : Context) (d : Nat) (it : Item) : Prop :=
  it.source = 0 ∧ it.target = 0 ∧ it.cutBottom = false ∧ it.offset = 0 ∧
    (it.clean = none ∨
      ∃ ρ, topIn ctx.source ctx.rootColumn d 0 = some ρ ∧ it.clean = some (official ρ.2.row))

/-- The emitted list starts with the node of row `0` with leg absent or `x - 1`. -/
def GoodHead (ctx : Context) (l : List Emit) : Prop :=
  ∃ e rest, l = e :: rest ∧ e.row = 0 ∧ (e.leftColumn = none ∨ e.leftColumn = some (ctx.x - 1))

theorem levelOne_first {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {it : Item} (hit : FP ctx 1 it) :
    Ok (levelOne ctx it) (GoodHead ctx) := by
  obtain ⟨hsrc, htgt, _, _, hclean⟩ := hit
  have hb := hctx.top.build
  have hxs : ctx.x < ctx.source.size := by
    have := hctx.xle; have := hctx.last; have := hctx.top.lt; omega
  obtain ⟨b, hnode, hrow, hleft⟩ := nodeAt_zero hb hxs
  have hx0 : ctx.x ≠ 0 := by have := hctx.xgt; omega
  rw [if_neg hx0] at hleft
  unfold levelOne
  rw [hsrc, hnode]
  dsimp only
  rcases hclean with hc | ⟨ρ, hρ, hc⟩
  · rw [hc]
    dsimp only
    rw [if_pos rfl]
    exact ok_pure ⟨_, [], rfl, htgt, Or.inl rfl⟩
  · rw [hc]
    dsimp only
    -- the copied row is `0`: the region of level 1 with base 0 is the row 0
    unfold topIn at hρ
    obtain ⟨_, hin, _⟩ := filter_last_max hρ
    have h0 : official ρ.2.row = 0 := (inRegion_one_zero _).mp hin
    rw [h0, hnode]
    dsimp only
    rw [leftColumn_of hleft]
    exact ok_pure ⟨_, [], rfl, htgt, Or.inr rfl⟩

theorem map_range_cons {α : Type} (f : Nat → α) {n : Nat} (hn : 0 < n) :
    ∃ rest, (List.range n).map f = f 0 :: rest := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map]
  exact ⟨_, rfl⟩

theorem topIn_in {M : Mountain} {c d : Nat} {b : Row} {ρ : Ref × Cell}
    (h : topIn M c d b = some ρ) : inRegion d b (official ρ.2.row) = true := by
  unfold topIn at h
  exact (filter_last_max h).2.1

/-- The top of the root column in the slot-`0` subregion, when it is the top of the region. -/
theorem topIn_slot_zero {M : Mountain} {c d : Nat} {ρ : Ref × Cell}
    (h : topIn M c (d + 2) 0 = some ρ) (h0 : height (d + 2) (official ρ.2.row) = 0) :
    topIn M c (d + 1) 0 = some ρ := by
  have hiff := inRegion_slot_zero (d := d + 2) (by omega)
  simp only [show d + 2 - 1 = d + 1 by omega] at hiff
  exact topIn_sub h (fun r hr => ((hiff r).mp hr).1) ((hiff _).mpr ⟨topIn_in h, h0⟩)

theorem FP_plain (ctx : Context) (d : Nat) : FP ctx d ⟨0, 0, none, 0, false⟩ :=
  ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩

/-- **The first child of an item on the first path is on the first path.** -/
theorem childItems_first {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} (hd : d + 2 ≤ len (official t.row)) {it : Item}
    (hit : FP ctx (d + 2) it) :
    Ok (childItems ctx (d + 2) it) (fun l => ∃ c0 rest, l = c0 :: rest ∧ FP ctx (d + 1) c0) := by
  obtain ⟨hsrc, htgt, hcut, hoff, hclean⟩ := hit
  have hb := hctx.top.build
  have hcrs : ctx.rootColumn < ctx.source.size := by
    have := hctx.top.lt; have := hctx.rootc; omega
  have hxs : ctx.x < ctx.source.size := by
    have := hctx.xle; have := hctx.last; have := hctx.top.lt; omega
  obtain ⟨⟨ρ1, ρ2⟩, hρ⟩ := topIn_zero_exists hb hcrs (d + 2)
  have hρ' : topIn ctx.source root.column (d + 2) 0 = some (ρ1, ρ2) := by
    rw [← hctx.rootc]; exact hρ
  obtain ⟨⟨κ1, κ2⟩, hκ, hRK⟩ := hctx.top.rootCut (by omega) hd hρ'
  have hκ' : topIn ctx.source ctx.lastColumn (d + 2) 0 = some (κ1, κ2) := by
    rw [hctx.last]; exact hκ
  have hP1 : 3 ≤ d + 2 → 1 ≤ height (d + 2) (official κ2.row) :=
    fun h3 => hctx.top.cut_pos h3 hd hκ
  have hsl : slot (d + 2) 0 0 = 0 := slot_zero_zero _
  unfold childItems
  dsimp only
  rw [hsrc, htgt, hρ, hκ']
  simp only [heightOf]
  split
  · rename_i hnone
    obtain ⟨_, hsome⟩ := topIn_zero_exists hb hxs (d + 2)
    rw [hsome] at hnone
    cases hnone
  · rename_i aRef aCell _
    refine ok_bind (ok_true _) (fun asc _ => ?_)
    split
    · -- case 1
      split
      · exact ok_throw_bind _ _
      · refine ok_pure ?_
        obtain ⟨rest, hrest⟩ := map_range_cons (fun (j : Nat) => (⟨slot (d + 2) 0 j,
          slot (d + 2) 0 j, none, 0, false⟩ : Item)) (n := height (d + 2) (official aCell.row) + 1)
          (by omega)
        refine ⟨_, rest, hrest, ?_⟩
        simp only [hsl]
        exact FP_plain ctx _
    · split
      · rename_i hcl
        split
        · -- case 2
          refine ok_pure ?_
          set hR := height (d + 2) (official ρ2.row) with hhR
          set hK := height (d + 2) (official κ2.row) with hhK
          have hlift : (0 : Int) ≤ ((hK : Int) - hR) * ctx.block := by
            apply Int.mul_nonneg
            · omega
            · exact Int.natCast_nonneg _
          obtain ⟨rest, hrest⟩ := map_range_cons (n := ((height (d + 2) (official aCell.row) : Int) +
            ((hK : Int) - hR) * ctx.block + 1).toNat) (fun (j : Nat) =>
              if j < hR then (⟨slot (d + 2) 0 j, slot (d + 2) 0 j, none, 0, false⟩ : Item)
              else if (j : Int) < hR + ((hK : Int) - hR) * ctx.block + (if d + 2 = 2 then 1 else 0)
              then ⟨slot (d + 2) 0 hR, slot (d + 2) 0 j, some (official ρ2.row), 0, decide (hR < j)⟩
              else ⟨slot (d + 2) 0 ((j : Int) - ((hK : Int) - hR) * ctx.block).toNat,
                slot (d + 2) 0 j, none, 0,
                decide (ctx.block ≠ 0 ∧ (j : Int) = hR + ((hK : Int) - hR) * ctx.block)⟩)
            (by omega)
          refine ⟨_, rest, hrest, ?_⟩
          try dsimp only
          by_cases h1 : 0 < hR
          · rw [if_pos h1]
            simp only [hsl]
            exact FP_plain ctx _
          · rw [if_neg h1]
            have hR0 : hR = 0 := by omega
            by_cases h2 : (((0 : Nat) : Int) < hR + ((hK : Int) - hR) * ctx.block +
                (if d + 2 = 2 then 1 else 0))
            · rw [if_pos h2, hR0, hsl]
              refine ⟨rfl, rfl, rfl, rfl, Or.inr ⟨(ρ1, ρ2), ?_, rfl⟩⟩
              exact topIn_slot_zero hρ hR0
            · rw [if_neg h2]
              have hd3 : ¬ d + 2 = 2 := by
                intro h2'
                rw [if_pos h2'] at h2
                omega
              rw [if_neg hd3] at h2
              have hK1 := hP1 (by omega)
              have hi0 : ctx.block = 0 := by
                by_contra hne
                have : (1 : Int) ≤ ((hK : Int) - hR) * ctx.block := by
                  rw [hR0]
                  have hpos : 1 ≤ hK * ctx.block := Nat.mul_pos (by omega) (by omega)
                  simp only [Nat.cast_zero, sub_zero]
                  exact_mod_cast hpos
                omega
              rw [hi0]
              simp only [Nat.cast_zero, mul_zero, sub_zero, Int.toNat_zero, hsl, ne_eq,
                not_true_eq_false, false_and, decide_false]
              exact FP_plain ctx _
        · rename_i hc
          exact absurd hcut (by simpa using hc)
      · -- case 4
        rename_i C hC
        rcases hclean with hc | ⟨ρ', hρ'', hc⟩
        · rw [hc] at hC; cases hC
        · rw [hρ] at hρ''
          obtain rfl := Option.some.inj hρ''
          rw [hc] at hC
          obtain rfl := Option.some.inj hC
          split
          · exact ok_throw_bind _ _
          · rename_i p _
            refine ok_bind (ok_true _) (fun p' _ => ?_)
            refine ok_bind (ok_true _) (fun g _ => ?_)
            split
            · exact ok_throw_bind _ _
            · refine ok_pure ?_
              rw [hcut, hoff]
              set hR := height (d + 2) (official ρ2.row) with hhR
              set hB := heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) 0)
              obtain ⟨rest, hrest⟩ := map_range_cons (n := ((if ctx.block = 0 then
                (height (d + 2) (official aCell.row) : Int) else (hB : Int) + g - ((0 : Nat) : Int)) + 1).toNat)
                (fun (j : Nat) =>
                  if false = true then (⟨slot (d + 2) 0 hR, slot (d + 2) 0 j, some (official ρ2.row),
                    ((j : Int) - hB + ((0 : Nat) : Int)).toNat, true⟩ : Item)
                  else if j < hR then ⟨slot (d + 2) 0 j, slot (d + 2) 0 j, none, 0, false⟩
                  else ⟨slot (d + 2) 0 hR, slot (d + 2) 0 j, some (official ρ2.row),
                    ((j : Int) - hB + ((0 : Nat) : Int)).toNat, decide (hR < j)⟩)
                (by split <;> omega)
              refine ⟨_, rest, hrest, ?_⟩
              try dsimp only
              rw [if_neg (by simp)]
              by_cases h1 : 0 < hR
              · rw [if_pos h1]
                simp only [hsl]
                exact FP_plain ctx _
              · rw [if_neg h1]
                have hR0 : hR = 0 := by omega
                rw [hR0, hsl]
                refine ⟨rfl, rfl, ?_, ?_, Or.inr ⟨(ρ1, ρ2), topIn_slot_zero hρ hR0, rfl⟩⟩
                · simp
                · simp only [Nat.cast_zero, add_zero, zero_sub]
                  omega

theorem ok_mapM_head {ε α β : Type} {f : α → Except ε β} {c0 : α} {rest : List α}
    {P : β → Prop} (h : Ok (f c0) P) :
    Ok ((c0 :: rest).mapM f) (fun outs => ∃ o0 os, outs = o0 :: os ∧ P o0) := by
  rw [List.mapM_cons]
  refine ok_bind h (fun o0 ho0 => ?_)
  refine ok_bind (ok_true _) (fun os _ => ok_pure ⟨o0, os, rfl, ho0⟩)

/-- **The first path through the item processing.** -/
theorem runItem_first {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) :
    ∀ d, 1 ≤ d → d ≤ len (official t.row) → ∀ it, FP ctx d it →
      Ok (runItem ctx d it) (GoodHead ctx) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd1 hdl it hit
    match d, ih, hd1, hdl with
    | 1, _, _, _ =>
      rw [runItem]
      exact levelOne_first hctx hit
    | d + 2, ih, _, hdl =>
      rw [runItem]
      refine ok_bind (childItems_first hctx hdl hit) (fun children hch => ?_)
      obtain ⟨c0, rest, rfl, hc0⟩ := hch
      refine ok_bind (ok_mapM_head (ih (d + 1) (by omega) (by omega) (by omega) c0 hc0))
        (fun outs houts => ok_pure ?_)
      obtain ⟨o0, os, rfl, ho0⟩ := houts
      obtain ⟨e, r, rfl, he, hl⟩ := ho0
      exact ⟨e, r ++ os.flatten, by simp, he, hl⟩

/-! ## The first lower item -/

theorem slot_top_zero (τ : Row) : slot (len τ + 1) τ 0 = 0 := by
  apply row_ext
  intro k
  rw [coeff_slot]
  split_ifs with h1 h2
  · exact (Row.coeff_zero k).symm
  · exact (Row.coeff_zero k).symm
  · rw [Row.coeff_zero]
    exact coeff_of_le_len (by omega)

theorem lowerItems_head {τ : Row} (hτ : τ ≠ 0) :
    ∃ rest, lowerItems τ = (len τ, ⟨0, 0, none, 0, false⟩) :: rest := by
  have hlen : 1 ≤ len τ := by
    by_contra h
    apply hτ
    apply row_ext
    intro i
    rw [Row.coeff_zero]
    exact coeff_of_le_len (by omega)
  have hc : τ.coeff (len τ - 1) ≠ 0 := coeff_top_ne_zero hlen
  unfold lowerItems
  obtain ⟨L, hL⟩ : ∃ L, len τ = L + 1 := ⟨len τ - 1, by omega⟩
  rw [hL, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatMap_cons]
  obtain ⟨m, hm⟩ : ∃ m, τ.coeff L = m + 1 := ⟨τ.coeff L - 1, by rw [hL] at hc; simp at hc; omega⟩
  rw [hm, List.range_succ_eq_map, List.map_cons]
  have := slot_top_zero τ
  rw [hL] at this
  dsimp only
  rw [show L + 2 = L + 1 + 1 by omega, this]
  exact ⟨_, rfl⟩

/-- The first cell of a new column. -/
def FirstCol (m : Mountain) (col : Column) : Prop :=
  ∃ b : Cell, col[1]? = some b ∧ b.row = 1 ∧ ∃ ref, b.left = some ref ∧
    (ref = ⟨m.size - 1, 0⟩ ∨ Expansion.below m (m.size - 1) 1 = .ok ref)

/-- The cell made from one emitted node, in more detail. -/
theorem assemble_cell_first (ctx : Context) (em : Emit) :
    Ok (match em.leftColumn with
      | some p => do
        let q := if ctx.rootColumn ≤ p then p + ctx.width * ctx.block else p
        let ref ← liftE (Expansion.below ctx.result q (stored em.row))
        pure (⟨stored em.row, 0, some ref⟩ : Cell)
      | none =>
        if em.row = 0 then pure (⟨stored em.row, 0, some ⟨ctx.result.size - 1, 0⟩⟩ : Cell)
        else throw .missingParent)
      (fun cell => cell.row = stored em.row ∧
        (em.leftColumn = none → cell.left = some ⟨ctx.result.size - 1, 0⟩) ∧
        ∀ p, em.leftColumn = some p → ∃ ref, cell.left = some ref ∧
          Expansion.below ctx.result (if ctx.rootColumn ≤ p then p + ctx.width * ctx.block else p)
            (stored em.row) = .ok ref) := by
  split
  · rename_i p hp
    intro cell h
    obtain ⟨ref, href, h⟩ := Reconstruction.bind_ok h
    cases h
    refine ⟨rfl, (fun h' => by rw [hp] at h'; cases h'), fun p' hp' => ?_⟩
    rw [hp] at hp'
    obtain rfl := Option.some.inj hp'
    exact ⟨ref, rfl, Reconstruction.liftE_ok href⟩
  · rename_i hp
    split
    · intro cell h
      cases h
      exact ⟨rfl, (fun _ => rfl), fun p' hp' => by rw [hp] at hp'; cases hp'⟩
    · exact ok_throw _

theorem assemble_first (ctx : Context) (hsize : ctx.result.size = ctx.x + ctx.width * ctx.block)
    (hx : ctx.rootColumn < ctx.x) {emits : List Emit} (hh : GoodHead ctx emits) :
    Ok (assemble ctx emits) (FirstCol ctx.result) := by
  obtain ⟨e0, erest, rfl, he0, hl0⟩ := hh
  unfold assemble
  dsimp only
  split
  · exact ok_throw_bind _ _
  · refine ok_bind (ok_forIn_check (fun pair : Emit × Emit => pair.1.row < pair.2.row) _ _ _ ?_)
      (fun _ hrows => ?_)
    · intro a _ b r h
      by_cases hq : a.1.row < a.2.row
      · simp only [hq, not_true_eq_false, if_false] at h
        exact ⟨hq, by cases h; exact ⟨_, rfl⟩⟩
      · simp only [hq, not_false_eq_true, if_true] at h
        cases h
    · refine ok_bind (ok_mapM₂ _ _ _ (fun em _ => assemble_cell_first ctx em))
        (fun cells hcells => ?_)
      intro col hcol
      have hfin := Reconstruction.liftE_ok hcol
      cases hcells with
      | cons hc0 hrest =>
        rename_i c0 crest
        obtain ⟨hrow0, hnone, hsome⟩ := hc0
        -- the rows are strictly increasing, so sorting keeps `phantom :: cells`
        have hmap : (c0 :: crest).map Cell.row = (e0 :: erest).map (fun em => stored em.row) :=
          forall₂_map (fun _ _ h => h.1) (List.Forall₂.cons ⟨hrow0, hnone, hsome⟩ hrest)
        have hpw : ((c0 :: crest).map Cell.row).Pairwise (· < ·) := by
          rw [hmap, List.pairwise_map]
          exact (pairwise_of_zip_tail' (r := fun a b : Emit => a.row < b.row) hrows).imp
            stored_strictMono
        have hsorted : (phantom :: c0 :: crest).Pairwise
            (fun a b : Cell => decide (a.row ≤ b.row) = true) := by
          rw [List.pairwise_cons]
          refine ⟨fun a _ => by simp [phantom, Row.zero_le], ?_⟩
          rw [List.pairwise_map] at hpw
          exact List.Pairwise.imp (fun {a b : Cell} (h' : a.row < b.row) =>
            decide_eq_true (le_of_lt h')) hpw
        obtain ⟨hShape, _⟩ := Expansion.finish_success_spec hfin
        rw [List.mergeSort_of_pairwise hsorted] at hShape
        have hsize1 : 1 < col.size := by
          have := ColumnShape.length hShape
          simp at this
          omega
        obtain ⟨orig, horig, hsame⟩ := ColumnShape.getElem hShape
          (Array.getElem?_eq_getElem hsize1)
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at horig
        subst horig
        refine ⟨col[1], Array.getElem?_eq_getElem hsize1, ?_, ?_⟩
        · rw [← hsame.1, hrow0, he0]
          exact stored_zero
        · rcases hl0 with hl | hl
          · exact ⟨_, (hsame.2.symm.trans (hnone hl)), Or.inl rfl⟩
          · obtain ⟨ref, hleft, hbelow⟩ := hsome _ hl
            refine ⟨ref, hsame.2.symm.trans hleft, Or.inr ?_⟩
            rw [he0, stored_zero, if_pos (by omega)] at hbelow
            rw [show ctx.x - 1 + ctx.width * ctx.block = ctx.result.size - 1 by omega] at hbelow
            exact hbelow

theorem GoodHead.append {ctx : Context} {l : List Emit} (h : GoodHead ctx l) (m : List Emit) :
    GoodHead ctx (l ++ m) := by
  obtain ⟨e, r, rfl, he, hl⟩ := h
  exact ⟨e, r ++ m, rfl, he, hl⟩

theorem len_pos_of_ne {τ : Row} (hτ : τ ≠ 0) : 1 ≤ len τ := by
  by_contra h
  apply hτ
  apply row_ext
  intro i
  rw [Row.coeff_zero]
  exact coeff_of_le_len (by omega)

/-- **The first cell of a column made by `copyColumn`.** -/
theorem copyColumn_first {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) :
    Ok (copyColumn ctx (official t.row)) (FirstCol ctx.result) := by
  obtain ⟨rest, hlow⟩ := lowerItems_head hctx.top.real
  have hlen := len_pos_of_ne hctx.top.real
  unfold copyColumn
  dsimp only
  rw [hlow, List.forIn_cons]
  refine ok_bind (Q := GoodHead ctx) ?_ (fun emits h1 => ?_)
  · refine ok_bind (Q := fun x => ∃ b, x = ForInStep.yield b ∧ GoodHead ctx b) ?_ (fun x hx => ?_)
    · refine ok_bind (runItem_first hctx _ hlen le_rfl _ (FP_plain ctx _)) (fun out hout => ?_)
      exact ok_pure ⟨_, rfl, by simpa using hout⟩
    · obtain ⟨b, rfl, hb⟩ := hx
      exact ok_forIn (GoodHead ctx) rest b _ hb
        (fun p _ l hl => ok_bind (ok_true _) (fun out _ => ok_pure (hl.append out)))
  · refine ok_bind (ok_forIn (GoodHead ctx) _ _ _ h1 (fun p _ l hl => ?_))
      (fun emits h2 => assemble_first ctx hctx.size hctx.xgt h2)
    split
    · exact ok_bind (ok_true _) (fun _ _ => ok_pure (hl.append _))
    · exact ok_pure hl

/-! ## The runs of `expandDiagram` -/

theorem leftOf_get (t : Cell) : Ok (liftE (Expansion.leftOf t)) (fun r => t.left = some r) := by
  intro r h
  have h' := Reconstruction.liftE_ok h
  unfold Expansion.leftOf at h'
  split at h'
  · rename_i r' hr
    cases h'
    exact hr
  · cases h'

theorem mem_blockColumns {cr x0 n i x : Nat} (hcr : cr < x0) (h : x ∈ blockColumns cr x0 n i) :
    cr < x ∧ x ≤ x0 := by
  unfold blockColumns at h
  split at h
  · simp only [List.mem_singleton] at h
    omega
  · rw [List.mem_range'_1] at h
    split at h <;> omega

theorem first_push {x0 : Nat} {R : Mountain}
    (h : ∀ c (hc : c < R.size), x0 ≤ c → FirstCol (R.extract 0 c) R[c]) {col : Column}
    (hcol : FirstCol R col) :
    ∀ c (hc : c < (R.push col).size), x0 ≤ c → FirstCol ((R.push col).extract 0 c) (R.push col)[c] := by
  intro c hc hx
  by_cases he : c = R.size
  · subst he
    simp only [Array.getElem_push_eq]
    rw [show (R.push col).extract 0 R.size = R by
      apply Array.ext
      · simp
      · intro i h1 h2
        simp]
    exact hcol
  · have hOld : c < R.size := by simp only [Array.size_push] at hc; omega
    simp only [Array.getElem_push_lt hOld]
    rw [show (R.push col).extract 0 c = R.extract 0 c by
      apply Array.ext
      · simp; omega
      · intro i h1 h2
        simp only [Array.size_extract, Array.size_push] at h1 h2
        simp only [Array.getElem_extract]
        rw [Array.getElem_push_lt (by omega)]]
    exact h c hOld hx

/-- **Every new column of a run begins with the right first cell.** -/
theorem expandDiagram_first {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    (copies : Nat) :
    Ok (Official.expandDiagram s copies)
      (fun R => ∀ c (hc : c < R.size), M.size - 1 ≤ c → FirstCol (R.extract 0 c) R[c]) := by
  unfold Official.expandDiagram
  have hbuild : Ok (liftE ((Canonical.build s).mapError Expansion.Error.canonical))
      (fun M' => M' = M) := by
    intro M' h
    rw [hb] at h
    cases h
    rfl
  refine ok_bind hbuild (fun M' hM' => ?_)
  subst M'
  dsimp only
  split
  · rename_i hs
    have : s = [] := List.isEmpty_iff.mp hs
    subst this
    have hM0 : M = #[] := Except.ok.inj (hb.symm.trans rfl)
    subst hM0
    exact ok_pure (fun c hc => by simp at hc)
  · refine ok_bind (ok_liftE (columnAt_get M _)) (fun lastCol hlast => ?_)
    refine ok_bind (ok_liftE (top_get lastCol)) (fun t ht => ?_)
    split
    · refine ok_pure ?_
      intro c hc hx
      simp at hc
      omega
    · rename_i hτ
      refine ok_bind (leftOf_get t) (fun root hroot => ?_)
      split
      · exact ok_throw_bind _ _
      · rename_i hcr
        have hcr' : root.column < M.size - 1 := not_not.mp hcr
        have hTop : Top s M t root := ⟨hb, by rw [hlast]; exact ht,
          fun h0 => hτ (Or.inl h0), hroot, hcr'⟩
        let I : Mountain → Prop := fun R =>
          ∀ c (hc : c < R.size), M.size - 1 ≤ c → FirstCol (R.extract 0 c) R[c]
        have hI0 : I (M.extract 0 (M.size - 1)) := by
          intro c hc hx
          simp at hc
          omega
        refine ok_bind (ok_forIn I _ _ _ hI0 (fun i _ R hR => ?_)) (fun R hR => ok_pure hR)
        refine ok_bind (ok_forIn I _ _ _ hR (fun x hx R hR => ?_)) (fun R hR => ok_pure hR)
        split
        · exact ok_throw_bind _ _
        · rename_i hsize
          have hsize' := not_not.mp hsize
          obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr' hx
          have hctx : RunCtx s ⟨M, R, x, i, root.column, M.size - 1 - root.column, M.size - 1⟩ t root :=
            ⟨hTop, rfl, rfl, hxgt, hxle, hsize'⟩
          refine ok_bind (copyColumn_first hctx) (fun col hcol => ok_pure ?_)
          exact first_push hR hcol

/-! ## The bottom of every new column -/

theorem firstCol_bottom {m : Mountain} (hV : MountainValid m) (hpos : 0 < m.size) {col : Column}
    (h : FirstCol m col) : BottomOK m.size col := by
  obtain ⟨b, hb, hrow, ref, hleft, hcase⟩ := h
  refine ⟨b, hb, hrow, ?_⟩
  rw [hleft]
  rcases hcase with rfl | hbelow
  · rfl
  · obtain ⟨nodes, hn⟩ := below_nodes hbelow
    obtain ⟨hcol, cell, hcell, hrow'⟩ := below_result hn hbelow
    have hlast : m.size - 1 < m.size := by omega
    have hnodes : m[m.size - 1] = nodes := (Array.getElem?_eq_some_iff.mp hn).2
    have hCV : ColumnValid m (m.size - 1) nodes := hnodes ▸ hV _ hlast
    have hidx : ref.index = 0 := by
      by_contra hne
      have := hCV.rows_strict 0 ref.index phantom cell hCV.phantom hcell (by omega)
      have h1 := row_one_le_of_ne_zero (ne_of_gt this)
      exact absurd hrow' (not_lt.mpr h1)
    congr 1
    cases ref
    simp_all

/-- The basic facts of every prefix of a run output, from the first cells. -/
theorem basic_extract {s : List Nat} {M R : Mountain} (hb : Canonical.build s = .ok M)
    (hI : Inv M (M.size - 1) R)
    (hF : ∀ c (hc : c < R.size), M.size - 1 ≤ c → FirstCol (R.extract 0 c) R[c]) :
    ∀ k, M.size - 1 + k ≤ R.size → Basic (R.extract 0 (M.size - 1 + k)) := by
  have hpop := extract_pop_of_inv hI
  obtain ⟨hs, hpre, hnew⟩ := hI
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.add_zero, hpop]
    exact (certified_of_build (Reconstruction.build_dropLast hb)).toBasic
  | succ k ih =>
    intro hk
    have hlt : M.size - 1 + k < R.size := by omega
    have hm := ih (by omega)
    rw [show M.size - 1 + (k + 1) = (M.size - 1 + k) + 1 by omega,
      Array.extract_succ_right (by omega) hlt]
    have hmsize : (R.extract 0 (M.size - 1 + k)).size = M.size - 1 + k := by simp; omega
    obtain ⟨hpos, hN⟩ := hnew _ hlt (by omega)
    have hBc : BottomOK (R.extract 0 (M.size - 1 + k)).size R[M.size - 1 + k] :=
      firstCol_bottom hm.valid (by omega) (hF _ hlt (by omega))
    exact basic_push_newCol hm (by omega) hN hBc

/-- **`BottomHolds`.** The bottom real cell of every new column is at stored row `1` with
the phantom of the previous column as its left endpoint. -/
theorem bottomHolds : BottomHolds := by
  intro s n R hrun c hc hx
  obtain ⟨M, hM, _⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  have hI := expandDiagram_inv hM n R hrun
  have hF := expandDiagram_first hM n R hrun
  have hbasic := basic_extract hM hI hF (c - (M.size - 1)) (by omega)
  rw [show M.size - 1 + (c - (M.size - 1)) = c by omega] at hbasic
  have hcs : (R.extract 0 c).size = c := by simp; omega
  have hpos : 0 < c := (hI.2.2 c hc (by omega)).1
  have := firstCol_bottom hbasic.valid (by omega) (hF c hc (by omega))
  rw [hcs] at this
  exact this

/-- **Reduction of `ReconstructionHolds` to the row law and the chain condition.** -/
theorem reconstructionHolds_of_rowLaw_chain (hR : RowLawHolds) (hC : ChainHolds) :
    Reconstruction.ReconstructionHolds :=
  reconstructionHolds_of_parts bottomHolds hR hC

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.bottomHolds
#print axioms OmegaY.Official.Recon.reconstructionHolds_of_rowLaw_chain
