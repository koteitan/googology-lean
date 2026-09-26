/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawColumn.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `copyColumn_bumpCol` the step `List.IsChain.rel_getLast_head_of_append`, which Mathlib v4.30.0 does not have, is taken from `List.isChain_append`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawLower
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Trace

set_option backward.do.legacy false

/-!
# Part (a) of the row law: consecutive rows of a new column are bump steps

`bumpChainHolds`: in every new column `c ≥ x₀` of a successful official `expandDiagram`,
consecutive cells `lower`, `upper` (above the phantom) satisfy `upper.row = bump lower.row e`
for some `e`. It depends only on the emitted rows:

* the lower part is a chain (`lower_flatten`);
* the upper part is the suffix of rows `≥ τ` of the column `x'` (`x' = x`, or `c_r` for
  `x = x₀`), a chain since the source columns are chains;
* the seam: the first upper row is `b = bump a_c e` with `a_c` the row below it in `x'`;
  `a_c ≤ a₀`, the highest row of column `x` below `τ` (for `x' = c_r` by
  `Top.root_rows`), so `b = bump a₀ e`, and `lower_flatten` gives the bump step from the
  last lower row to `b`.

`rowLawHolds_of_jumpLaw` then reduces `Recon.RowLawHolds` to `JumpLawHolds`: for such a pair
with `upper.row = bump lower.row e`, the parent cell `p` of `upper` has
`jump lower.row p.row = e` (part (b) of the plan in the Recon report).
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical Expansion Dimension

/-! ## The rows of a column split at `τ` -/

theorem chain_split {τ : Row} : ∀ {l : List Row}, l.IsChain BumpStep →
    l = l.filter (fun r => decide (r < τ)) ++ l.filter (fun r => decide (τ ≤ r))
  | [], _ => rfl
  | a :: rest, h => by
    by_cases ha : a < τ
    · have ih := chain_split (τ := τ) (l := rest) h.tail
      rw [List.filter_cons_of_pos (by simpa using ha),
        List.filter_cons_of_neg (by simpa using ha), List.cons_append, ← ih]
    · have hall : ∀ r ∈ a :: rest, τ ≤ r := fun r hr =>
        (not_lt.mp ha).trans (le_of_chain_head h r hr)
      rw [List.filter_eq_nil_iff.mpr (fun r hr => by simpa using hall r hr),
        List.filter_eq_self.mpr (fun r hr => by simpa using hall r hr), List.nil_append]

/-! ## `copyColumn` in parts -/

/-- The emitted nodes of `copyColumn`: the lower part `vs.flatten` and the upper part `us`. -/
theorem copyColumn_parts {ctx : Context} {τ : Row} {col : Column}
    (h : copyColumn ctx τ = .ok col) :
    ∃ vs us, (lowerItems τ).mapM (fun x : Nat × Item => runItem ctx x.1 x.2) = .ok vs ∧
      ((realNodes ctx.source (Classification.upperColumn ctx)).filter
          (fun p => decide (τ ≤ official p.2.row))).mapM
          (fun x : Ref × Cell => Except.bind (leftColumn x.2)
            (fun v => Except.ok ({ row := official x.2.row, leftColumn := some v } : Emit))) =
        .ok us ∧
      assemble ctx (vs.flatten ++ us) = .ok col := by
  unfold copyColumn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    obtain ⟨vs, hvs, hlow⟩ := Classification.forIn_acc_ok
      (fun x : Nat × Item => runItem ctx x.1 x.2) _ _ _ hlower
    split at h
    · cases h
    · rename_i all hall
      obtain ⟨us, hus, hup⟩ := Classification.forIn_filter_ok
        (fun x : Ref × Cell => τ ≤ official x.2.row)
        (fun x => leftColumn x.2) (fun x v => (⟨official x.2.row, some v⟩ : Emit)) _ _ _ hall
      refine ⟨vs, us, hvs, hus, ?_⟩
      rw [← h, hup, hlow, List.nil_append]

theorem upper_rows {ctx : Context} {τ : Row} {us : List Emit}
    (h : ((realNodes ctx.source (Classification.upperColumn ctx)).filter
          (fun p => decide (τ ≤ official p.2.row))).mapM
          (fun x : Ref × Cell => Except.bind (leftColumn x.2)
            (fun v => Except.ok ({ row := official x.2.row, leftColumn := some v } : Emit))) =
        .ok us) :
    us.map Emit.row = (rowsOf ctx.source (Classification.upperColumn ctx)).filter
      (fun r => decide (τ ≤ r)) := by
  have hF := ok_mapM₂ (fun (x : Ref × Cell) (em : Emit) => em.row = official x.2.row) _ _
    (fun x _ => by
      intro em hem
      cases hl : leftColumn x.2 with
      | error e => rw [hl] at hem; cases hem
      | ok v =>
        rw [hl] at hem
        cases hem
        rfl) us h
  rw [forall₂_map (fun _ _ h => h) hF, rowsOf, List.filter_map]
  rfl

/-! ## The first items -/

theorem lower_itemOK {ctx : Context} {τ : Row} {p : Nat × Item} (hp : p ∈ lowerItems τ) :
    ItemOK ctx τ p.1 p.2 ∧ p.2.source = p.2.target ∧ 1 ≤ p.1 ∧
      (∀ q, p.1 - 1 < q → τ.coeff q = p.2.target.coeff q) := by
  obtain ⟨k, j, _, hj, rfl⟩ := mem_lowerItems hp
  refine ⟨⟨?_, ?_, offsetOK_of_none rfl⟩, rfl, by simp, ?_⟩
  · show ZeroBelow (k + 1 - 1) (slot (k + 2) τ j)
    rw [show k + 1 - 1 = k by omega]
    exact slot_zeroBelow k τ j
  · intro r hr
    change inRegion (k + 1) (slot (k + 2) τ j) r = true at hr
    rw [inRegion_iff'] at hr
    simp only [show k + 1 - 1 = k by omega] at hr
    refine Row.lt_iff.mpr ⟨k, ?_, ?_⟩
    · intro q hq
      rw [hr q (by omega), slot_coeff_high hq]
    · rw [hr k le_rfl, slot_coeff_at]
      exact hj
  · intro q hq
    change k + 1 - 1 < q at hq
    change τ.coeff q = (slot (k + 2) τ j).coeff q
    rw [slot_coeff_high (by omega)]

/-! ## One new column -/

/-- Consecutive cells above the phantom are bump steps. -/
def BumpCol (col : Column) : Prop :=
  ∀ (index : Nat) (lower upper : Cell), col[index]? = some lower → col[index + 1]? = some upper →
    0 < index → BumpStep lower.row upper.row

theorem assemble_rows {ctx : Context} {emits : List Emit} {col : Column}
    (h : assemble ctx emits = .ok col) :
    ∀ k, (col[k + 1]?).map Cell.row = (emits[k]?).map (fun em => stored em.row) := by
  unfold assemble at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i u hrows
      have hrows' : ∀ pair ∈ emits.zip emits.tail, pair.1.row < pair.2.row := by
        have := ok_forIn_check (fun pair : Emit × Emit => pair.1.row < pair.2.row) (emits.zip emits.tail)
          PUnit.unit _ (by
            intro a _ b r hr
            by_cases hq : a.1.row < a.2.row
            · simp only [hq, not_true_eq_false, if_false] at hr
              exact ⟨hq, by cases hr; exact ⟨_, rfl⟩⟩
            · simp only [hq, not_false_eq_true, if_true] at hr
              cases hr) u hrows
        exact this
      split at h
      · cases h
      · rename_i cells hcells
        have hF := ok_mapM₂ (fun (em : Emit) (cell : Cell) => cell.row = stored em.row) emits _
          (fun em _ => fun cell hc => (assemble_cell ctx em cell hc).1) cells hcells
        have hfin := Reconstruction.liftE_ok h
        have hmap : cells.map Cell.row = emits.map (fun em => stored em.row) :=
          forall₂_map (fun _ _ h => h) hF
        have hpw : (cells.map Cell.row).Pairwise (· < ·) := by
          rw [hmap, List.pairwise_map]
          exact (pairwise_of_zip_tail' (r := fun a b : Emit => a.row < b.row) hrows').imp
            stored_strictMono
        have hsorted : (phantom :: cells).Pairwise
            (fun a b : Cell => decide (a.row ≤ b.row) = true) := by
          rw [List.pairwise_cons]
          refine ⟨fun a _ => by simp [phantom, Row.zero_le], ?_⟩
          rw [List.pairwise_map] at hpw
          exact List.Pairwise.imp (fun {a b : Cell} (h' : a.row < b.row) =>
            decide_eq_true (le_of_lt h')) hpw
        obtain ⟨hShape, _⟩ := Expansion.finish_success_spec hfin
        rw [List.mergeSort_of_pairwise hsorted] at hShape
        intro k
        have h1 := congrArg (fun l : List Row => l[k + 1]?) hShape.1
        simp only [List.map_cons, List.getElem?_cons_succ, List.getElem?_map,
          Array.getElem?_toList] at h1
        rw [← h1, ← List.getElem?_map, hmap, List.getElem?_map]

theorem bumpCol_of_emits {ctx : Context} {emits : List Emit} {col : Column}
    (h : assemble ctx emits = .ok col) (hc : EChain emits) : BumpCol col := by
  intro index lower upper hl hu hi
  have hr := assemble_rows h
  obtain ⟨k, rfl⟩ : ∃ k, index = k + 1 := ⟨index - 1, by omega⟩
  have h1 := hr k
  have h2 := hr (k + 1)
  rw [hl] at h1
  rw [hu] at h2
  have hk1 : k + 1 < emits.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h2
    cases h2
  rw [List.getElem?_eq_getElem (by omega)] at h1
  rw [List.getElem?_eq_getElem hk1] at h2
  simp only [Option.map_some, Option.some.injEq] at h1 h2
  rw [h1, h2]
  exact bumpStep_stored (List.isChain_iff_getElem.mp hc k hk1)

/-- The highest row of column `x` below `τ`. -/
theorem topBelow_exists {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) : ∃ a₀, TopBelow ctx (official t.row) a₀ := by
  have hb := hctx.top.build
  have hxs : ctx.x < ctx.source.size := by
    have := hctx.xle; have := hctx.last; have := hctx.top.lt; omega
  have hτ : (0 : Row) < official t.row :=
    lt_of_le_of_ne (Row.zero_le _) (Ne.symm hctx.top.real)
  obtain ⟨b, hb1, _⟩ := bottom_mem hb hxs
  let P : Ref × Cell → Bool := fun p => decide (official p.2.row < official t.row)
  obtain ⟨a, ha⟩ := filter_last_exists (P := P) hb1 (by simp [P, *])
  obtain ⟨hamem, haP, hmax⟩ := filter_last_max ha
  have hV := build_valid_of_success hb
  refine ⟨official a.2.row, ⟨a, hamem, rfl⟩, by simpa [P] using haP, ?_⟩
  intro p hp hlt
  exact official_mono (realNodes_row_one_le hV hp)
    (realNodes_row_le hV hp hamem (hmax p hp (by simpa [P] using hlt)))

/-- **One new column.** -/
theorem copyColumn_bumpCol {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {col : Column} (h : copyColumn ctx (official t.row) = .ok col) :
    BumpCol col := by
  have hb := hctx.top.build
  set τ := official t.row with hτdef
  obtain ⟨vs, us, hvs, hus, hasm⟩ := copyColumn_parts h
  -- the lower part
  have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) =>
      Good p.1 p.2.target L ∧ (Has ctx p.1 p.2.source ↔ L ≠ [])) (lowerItems τ) _
    (fun p hp => runItem_good hctx p.1 (lower_itemOK (ctx := ctx) hp).2.2.1 p.2
      (lower_itemOK (ctx := ctx) hp).1) vs hvs
  have hlen := hF.length_eq
  let xs : List (Nat × Row × List Emit) :=
    ((lowerItems τ).zip vs).map fun q => (q.1.1, q.1.2.target, q.2)
  have hxs1 : xs.map (fun x => (x.1, x.2.1)) = (lowerItems τ).map (fun p => (p.1, p.2.target)) := by
    simp only [xs, List.map_map]
    rw [show ((fun x : Nat × Row × List Emit => (x.1, x.2.1)) ∘
        fun q : (Nat × Item) × List Emit => (q.1.1, q.1.2.target, q.2)) =
        (fun p : Nat × Item => (p.1, p.2.target)) ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (le_of_eq hlen)]
  have hxs2 : xs.map (fun x => x.2.2) = vs := by
    simp only [xs, List.map_map]
    rw [show ((fun x : Nat × Row × List Emit => x.2.2) ∘
        fun q : (Nat × Item) × List Emit => (q.1.1, q.1.2.target, q.2)) = Prod.snd from rfl,
      List.map_snd_zip (le_of_eq hlen.symm)]
  have hok : ∀ x ∈ xs, LowerOK ctx τ x := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hP := List.forall₂_zip hF hq
    have hmem := List.of_mem_zip hq
    obtain ⟨hIt, hst, _, hagree⟩ := lower_itemOK (ctx := ctx) hmem.1
    refine ⟨hP.1, ?_, hIt.target, hagree, ?_⟩
    · rw [← hst]; exact hP.2
    · intro r hr
      exact hIt.below r (by rw [hst]; exact hr)
  have hch : ChainTo 0 τ (xs.map fun x => (x.1, x.2.1)) := by
    rw [hxs1]; exact lowerItems_chainTo τ
  obtain ⟨hlowc, hseam⟩ := lower_flatten hb xs 0 hch hok
  rw [hxs2] at hlowc hseam
  -- the upper part
  have hurows := upper_rows hus
  set xa := Classification.upperColumn ctx with hxa
  have hRch := rowsOf_chain hb xa
  have hsplit := chain_split (τ := τ) hRch
  have huc : EChain us := by
    have : (us.map Emit.row).IsChain BumpStep := by
      rw [hurows]
      exact hRch.suffix ⟨_, hsplit.symm⟩
    unfold EChain
    exact (List.isChain_map Emit.row).mp this
  refine bumpCol_of_emits hasm (List.IsChain.append hlowc huc ?_)
  intro a ha em hem
  -- the first upper row and the row below it in column `x'`
  have hemrow : em.row ∈ (us.map Emit.row).head? := by
    cases hu : us with
    | nil => rw [hu] at hem; cases hem
    | cons u0 us0 =>
      rw [hu, List.head?_cons] at hem
      obtain rfl := Option.some.inj hem
      simp
  rw [hurows] at hemrow
  obtain ⟨a₀, htop⟩ := topBelow_exists hctx
  have hxas : xa < ctx.source.size := by
    rw [hxa]; unfold Classification.upperColumn
    have := hctx.xle; have := hctx.last; have := hctx.top.lt; have := hctx.rootc
    split <;> omega
  obtain ⟨l0, hl0⟩ := rowsOf_head hb hxas
  have hτpos : (0 : Row) < τ := lt_of_le_of_ne (Row.zero_le _) (Ne.symm hctx.top.real)
  have hPne : (rowsOf ctx.source xa).filter (fun r => decide (r < τ)) ≠ [] := by
    rw [hl0, List.filter_cons_of_pos (by simpa using hτpos)]
    simp
  have hUne : (rowsOf ctx.source xa).filter (fun r => decide (τ ≤ r)) ≠ [] := by
    intro h0; rw [h0] at hemrow; cases hemrow
  have hstep : BumpStep (((rowsOf ctx.source xa).filter (fun r => decide (r < τ))).getLast hPne)
      (((rowsOf ctx.source xa).filter (fun r => decide (τ ≤ r))).head hUne) :=
    (List.isChain_append.1 (hsplit ▸ hRch)).2.2 _ (List.getLast?_eq_getLast hPne) _
      (List.head?_eq_some_head hUne)
  have hbrow : em.row = ((rowsOf ctx.source xa).filter (fun r => decide (τ ≤ r))).head hUne := by
    have := List.head?_eq_some_head hUne
    rw [this] at hemrow
    exact (Option.some.inj (Option.mem_def.mp hemrow)).symm
  set ac := ((rowsOf ctx.source xa).filter (fun r => decide (r < τ))).getLast hPne with hacdef
  obtain ⟨e, he⟩ := hstep
  rw [← hbrow] at he
  have hacmem := List.getLast_mem hPne
  rw [← hacdef] at hacmem
  obtain ⟨hacR, hacτ⟩ := List.mem_filter.mp hacmem
  have hacτ' : ac < τ := by simpa using hacτ
  have hbτ : τ ≤ em.row := by
    have := List.head_mem hUne
    rw [← hbrow] at this
    simpa using (List.mem_filter.mp this).2
  -- the row below the first upper row is at most `a₀`
  have hacle : ac ≤ a₀ := by
    obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hacR
    by_cases hx : ctx.x = ctx.lastColumn
    · have hxa' : xa = ctx.rootColumn := by
        rw [hxa]; unfold Classification.upperColumn; rw [if_pos hx]
      rw [hxa', hctx.rootc] at hp
      have hlt : p.2.row < t.row := row_lt_of_official hctx.top.row_one_le (by rw [hprow]; exact hacτ')
      obtain ⟨v, hv, hvrow⟩ := hctx.top.root_rows hp hlt
      have hv' : v ∈ realNodes ctx.source ctx.x := by rw [hx, hctx.last]; exact hv
      rw [← hprow, ← hvrow]
      exact htop.max v hv' (by rw [hvrow, hprow]; exact hacτ')
    · have hxa' : xa = ctx.x := by
        rw [hxa]; unfold Classification.upperColumn; rw [if_neg hx]
      rw [hxa'] at hp
      rw [← hprow]
      exact htop.max p hp (by rw [hprow]; exact hacτ')
  have hjump : Row.jump ac a₀ ≤ e :=
    Row.jump_le_of_lt_bump hacle (lt_of_lt_of_le htop.lt (by rw [← he]; exact hbτ))
  have hb0 : em.row = Row.bump a₀ e := by rw [he]; exact Row.bump_eq_of_jump_le hjump
  rw [hb0]
  exact hseam a₀ htop e (by rw [← hb0]; exact hbτ) a ha

/-! ## The whole run -/

/-- **Part (a) of the row law.** -/
def BumpChainHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ c (hc : c < R.size), s.length - 1 ≤ c →
      ∀ (index : Nat) (lower upper : Cell),
        R[c][index]? = some lower → R[c][index + 1]? = some upper → 0 < index →
        ∃ e, upper.row = Row.bump lower.row e

theorem bumpCol_push {x0 : Nat} {R : Mountain}
    (h : ∀ c (hc : c < R.size), x0 ≤ c → BumpCol R[c]) {col : Column} (hcol : BumpCol col) :
    ∀ c (hc : c < (R.push col).size), x0 ≤ c → BumpCol (R.push col)[c] := by
  intro c hc hx
  by_cases he : c = R.size
  · subst he
    simp only [Array.getElem_push_eq]
    exact hcol
  · have hOld : c < R.size := by simp only [Array.size_push] at hc; omega
    simp only [Array.getElem_push_lt hOld]
    exact h c hOld hx

theorem expandDiagram_bumpCol {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    (copies : Nat) :
    Ok (Official.expandDiagram s copies)
      (fun R => ∀ c (hc : c < R.size), M.size - 1 ≤ c → BumpCol R[c]) := by
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
          ∀ c (hc : c < R.size), M.size - 1 ≤ c → BumpCol R[c]
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
          have hctx : RunCtx s ⟨M, R, x, i, root.column, M.size - 1 - root.column, M.size - 1⟩ t
              root := ⟨hTop, rfl, rfl, hxgt, hxle, hsize'⟩
          refine ok_bind (fun col hcol => copyColumn_bumpCol hctx hcol) (fun col hcol => ok_pure ?_)
          exact bumpCol_push hR hcol

/-- **Part (a) of the row law holds.** -/
theorem bumpChainHolds : BumpChainHolds := by
  intro s n R hrun c hc hx index lower upper hl hu hi
  obtain ⟨M, hM, _⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  have hcol := expandDiagram_bumpCol hM n R hrun c hc (by omega)
  exact hcol index lower upper hl hu hi

/-! ## The row law from part (b) -/

/-- **Part (b) of the row law (open).** For consecutive cells `lower`, `upper` of a new column
with `upper.row = bump lower.row e`, the parent cell of `upper` (at its stored left endpoint)
has `jump lower.row parent.row = e`. -/
def JumpLawHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ c (hc : c < R.size), s.length - 1 ≤ c →
      ∀ (index : Nat) (lower upper parent : Cell) (ref : Ref) (e : Nat),
        R[c][index]? = some lower → R[c][index + 1]? = some upper → 0 < index →
        upper.left = some ref → cellAt R ref = .ok parent →
        upper.row = Row.bump lower.row e → Row.jump lower.row parent.row = e

/-- **The row law from part (b).** -/
theorem rowLawHolds_of_jumpLaw (h : JumpLawHolds) : RowLawHolds := by
  intro s n R hrun c hc hx index lower upper parent ref hl hu hi hleft hcell
  obtain ⟨e, he⟩ := bumpChainHolds s n R hrun c hc hx index lower upper hl hu hi
  have hj := h s n R hrun c hc hx index lower upper parent ref e hl hu hi hleft hcell he
  rw [he, Row.B, hj]

/-- **`ReconstructionHolds` from part (b) and the chain condition.** -/
theorem reconstructionHolds_of_jumpLaw_chain (hJ : JumpLawHolds) (hC : ChainHolds) :
    Reconstruction.ReconstructionHolds :=
  reconstructionHolds_of_rowLaw_chain (rowLawHolds_of_jumpLaw hJ) hC

end OmegaY.Official.Recon.RowLaw

#print axioms OmegaY.Official.Recon.RowLaw.bumpChainHolds
#print axioms OmegaY.Official.Recon.RowLaw.rowLawHolds_of_jumpLaw
