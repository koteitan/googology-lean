/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Dimension.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Reserve
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Finish
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Values
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Prefix
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.DecrementRows

set_option backward.do.legacy false

/-!
# Dimension preservation for the official expansion

Item 2 of `notes/04-official-design.md` §6: the official expansion does not raise
the degree of rows. This follows the structure of Phyrion's
`OmegaY/Expansion/SupportedDimension.lean` for the weak rule: a bound on every row of
the executable output diagram, then canonical reconstruction to pass to the
canonical mountain of the output values.

* `expandDiagram_degree` (no assumption): if every stored row of `M(s)` has degree
  at most `D` (`Reserve.degreeAtMost`), so does every stored row of the diagram
  `Official.expandDiagram s n`. Every emitted row of `copyColumn` is either a row of
  `M(s)` at or above the top row `τ`, or the target of an item; every target is a
  slot `slot d b j` of a region whose base `b` descends from `τ`, and a slot never has
  a coefficient at an exponent `≥ max (len b) (d - 1)`.
* `output_degree_delete` (no assumption): for `s = []`, `n = 0` or last entry `1`,
  the output is a prefix of `s`, so `M(s[n])` consists of columns of `M(s)`.
* `output_degree_of_reconstruct`, `output_degree_of_rowsSubset`: the degree bound
  for `M(s[n])` when `M(s[n])` is the output diagram, or when every row of `M(s[n])`
  occurs in it.
* `output_degree`: the bound for all expansions from `BlockReconstruction`
  (canonical reconstruction for the expansions that add blocks, item 1 of §6).
-/

namespace OmegaY.Official.Dimension

open Canonical

/-! ## Degrees of rows -/

/-- Every coefficient of exponent `≥ L` is zero. -/
def RowDeg (L : Nat) (r : Row) : Prop := ∀ i, L ≤ i → r.coeff i = 0

theorem len_eq (a : Row) : len a = a.coeffs.support.sup (fun i => i + 1) := by
  simp [len, Row.toList]

theorem len_le_iff {a : Row} {L : Nat} : len a ≤ L ↔ RowDeg L a := by
  rw [len_eq, Finset.sup_le_iff]
  constructor
  · intro h i hi
    by_contra hne
    have := h i (Finsupp.mem_support_iff.mpr hne)
    omega
  · intro h i hi
    by_contra hlt
    exact Finsupp.mem_support_iff.mp hi (h i (by omega))

theorem rowDeg_nat {L : Nat} (hL : 1 ≤ L) (n : Nat) : RowDeg L (n : Row) := by
  intro i hi
  simp only [Row.coeff_nat]
  split <;> omega

theorem rowDeg_official {L : Nat} (hL : 1 ≤ L) {r : Row} (h : RowDeg L r) :
    RowDeg L (official r) := by
  unfold official
  split
  · exact rowDeg_nat hL _
  · exact h

theorem rowDeg_stored {L : Nat} (hL : 1 ≤ L) {r : Row} (h : RowDeg L r) :
    RowDeg L (stored r) := by
  unfold stored
  split
  · exact rowDeg_nat hL _
  · exact h

theorem rowDeg_slot {L d : Nat} {base : Row} (hb : RowDeg L base) (hd : d ≤ L + 1) (j : Nat) :
    RowDeg L (slot d base j) := by
  intro i hi
  unfold slot
  rw [Row.coeff_ofList]
  by_cases hlt : i < max (len base) (d - 1)
  · simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
    have h1 : ¬ i + 2 < d := by omega
    have h2 : ¬ i + 2 = d := by omega
    simp only [h1, h2, if_false]
    exact hb i hi
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)]
    rfl


/-! ## Postconditions of successful runs -/

/-- Every successful result of `x` satisfies `P`. -/
def Ok {ε α : Type} (x : Except ε α) (P : α → Prop) : Prop := ∀ a, x = .ok a → P a

theorem ok_pure {ε α : Type} {P : α → Prop} {a : α} (h : P a) : Ok (pure a : Except ε α) P := by
  intro b hb
  cases hb
  exact h

theorem ok_throw {ε α : Type} {P : α → Prop} (e : ε) : Ok (throw e : Except ε α) P := by
  intro b hb
  cases hb

theorem ok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {Q : α → Prop}
    {P : β → Prop} (hx : Ok x Q) (hf : ∀ a, Q a → Ok (f a) P) : Ok (x >>= f) P := by
  intro b hb
  cases h : x with
  | error e => rw [h] at hb; cases hb
  | ok a => rw [h] at hb; exact hf a (hx a h) b hb

theorem ok_throw_bind {ε α β : Type} {P : β → Prop} (e : ε) (f : α → Except ε β) :
    Ok ((throw e : Except ε α) >>= f) P := by
  intro b hb
  cases hb

theorem ok_true {ε α : Type} (x : Except ε α) : Ok x (fun _ => True) := fun _ _ => trivial

theorem ok_mono {ε α : Type} {x : Except ε α} {P Q : α → Prop} (h : Ok x P)
    (hPQ : ∀ a, P a → Q a) : Ok x Q := fun a ha => hPQ a (h a ha)

theorem ok_forIn {ε α β : Type} (I : β → Prop) (xs : List α) (init : β)
    (f : α → β → Except ε (ForInStep β)) (h0 : I init)
    (hf : ∀ a ∈ xs, ∀ b, I b → Ok (f a b) (fun r => I r.value)) :
    Ok (forIn xs init f) I := by
  induction xs generalizing init with
  | nil => exact ok_pure h0
  | cons a as ih =>
    rw [List.forIn_cons]
    refine ok_bind (hf a (List.mem_cons_self) init h0) ?_
    intro r hr
    cases r with
    | done b => exact ok_pure hr
    | yield b => exact ih b hr (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha'))

theorem ok_mapM {ε α β : Type} (P : β → Prop) (xs : List α) (f : α → Except ε β)
    (hf : ∀ a ∈ xs, Ok (f a) P) : Ok (xs.mapM f) (fun ys => ∀ y ∈ ys, P y) := by
  induction xs with
  | nil => exact ok_pure (by simp)
  | cons a as ih =>
    rw [List.mapM_cons]
    refine ok_bind (hf a List.mem_cons_self) ?_
    intro b hb
    refine ok_bind (ih (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha'))) ?_
    intro bs hbs
    refine ok_pure ?_
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hb
    · exact hbs y hy


/-! ## Items -/

theorem ok_map_target {ε : Type} {α : Type} (xs : List α) (g : α → Item) (d : Nat) (base : Row)
    (hg : ∀ a, ∃ j, (g a).target = slot d base j) :
    Ok (pure (xs.map g) : Except ε (List Item)) (fun l => ∀ c ∈ l, ∃ j, c.target = slot d base j) :=
  ok_pure fun c hc => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hc
    exact hg a

theorem childItems_targets (ctx : Context) (d : Nat) (it : Item) :
    Ok (childItems ctx d it) (fun l => ∀ c ∈ l, ∃ j, c.target = slot d it.target j) := by
  unfold childItems
  dsimp only
  split
  · exact ok_pure (by simp)
  · refine ok_bind (ok_true _) (fun asc _ => ?_)
    split
    · split
      · exact ok_throw_bind _ _
      · exact ok_map_target _ _ _ _ (fun _ => ⟨_, rfl⟩)
    · split
      · split
        · exact ok_map_target _ _ _ _ (fun _ => by split_ifs <;> exact ⟨_, rfl⟩)
        · exact ok_map_target _ _ _ _ (fun _ => by split_ifs <;> exact ⟨_, rfl⟩)
      · split
        · exact ok_throw_bind _ _
        · refine ok_bind (ok_true _) (fun q _ => ?_)
          obtain ⟨csRef, cs⟩ := q
          dsimp only
          refine ok_bind (ok_true _) (fun g _ => ?_)
          split
          · exact ok_throw_bind _ _
          · exact ok_map_target _ _ _ _ (fun _ => by split_ifs <;> exact ⟨_, rfl⟩)


theorem levelOne_rows (ctx : Context) (it : Item) :
    Ok (levelOne ctx it) (fun l => ∀ e ∈ l, e.row = it.target) := by
  unfold levelOne
  split
  · exact ok_pure (by simp)
  · split
    · split
      · exact ok_throw _
      · refine ok_bind (ok_true _) (fun _ _ => ok_pure (by simp))
    · split
      · exact ok_pure (by simp)
      · refine ok_bind (ok_true _) (fun _ _ => ok_pure (by simp))

/-- Every row emitted by an item of level `d ≤ L + 1` whose target has degree
below `L` has degree below `L`. -/
theorem runItem_rows (ctx : Context) {L : Nat} :
    ∀ (d : Nat) (it : Item), RowDeg L it.target → d ≤ L + 1 →
      Ok (runItem ctx d it) (fun l => ∀ e ∈ l, RowDeg L e.row) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro it ht hd
    match d, ih, hd with
    | 0, _, _ =>
      rw [runItem]
      exact ok_pure (by simp)
    | 1, _, _ =>
      rw [runItem]
      exact ok_mono (levelOne_rows ctx it) (fun l hl e he => (hl e he) ▸ ht)
    | d + 2, ih, hd =>
      rw [runItem]
      refine ok_bind (childItems_targets ctx (d + 2) it) (fun children hc => ?_)
      refine ok_bind (ok_mapM (fun l => ∀ e ∈ l, RowDeg L e.row) children _ (fun c hcm => ?_)) (fun outs houts => ?_)
      · obtain ⟨j, hj⟩ := hc c hcm
        exact ih (d + 1) (by omega) c (hj ▸ rowDeg_slot ht hd j) (by omega)
      · refine ok_pure ?_
        intro e he
        obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp he
        exact houts l hl e hel


theorem lowerItems_spec (τ : Row) :
    ∀ p ∈ lowerItems τ, p.1 ≤ len τ ∧ ∃ j, p.2.target = slot (p.1 + 1) τ j := by
  intro p hp
  unfold lowerItems at hp
  obtain ⟨k, hk, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
  have hk' : k < len τ := by simpa using hk
  exact ⟨by dsimp only; omega, j, rfl⟩

/-! ## Columns and mountains -/

/-- Every stored row of the mountain has degree below `L`. -/
def MDeg (L : Nat) (M : Mountain) : Prop := ∀ col ∈ M.toList, ∀ c ∈ col.toList, RowDeg L c.row

theorem mDeg_iff (M : Mountain) (D : Nat) : Reserve.degreeAtMost M D = true ↔ MDeg (D + 1) M := by
  simp only [Reserve.degreeAtMost, List.all_eq_true, decide_eq_true_eq, MDeg, len_le_iff]

theorem mem_realNodes {M : Mountain} {c : Nat} {p : Ref × Cell} (hp : p ∈ realNodes M c) :
    ∃ col ∈ M.toList, p.2 ∈ col.toList := by
  unfold realNodes at hp
  split at hp
  · simp at hp
  · rename_i col hcol
    refine ⟨col, List.mem_iff_getElem?.mpr ⟨c, by simpa using hcol⟩, ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact List.of_mem_zip (List.mem_of_mem_drop hq) |>.2

theorem ok_liftE {α : Type} {x : Expansion.Result α} {P : α → Prop} (h : Ok x P) :
    Ok (liftE x) P := by
  intro a ha
  unfold liftE Except.mapError at ha
  cases hx : x with
  | error e => rw [hx] at ha; cases ha
  | ok b =>
    rw [hx] at ha
    cases ha
    exact h _ hx

theorem finish_rows {M : Mountain} {cells : List Cell} {column : Column}
    (h : Expansion.finish M cells = .ok column) :
    ∀ c ∈ column.toList, ∃ c' ∈ cells, c'.row = c.row := by
  intro c hc
  have hshape := (Expansion.finish_success_spec h).1.1
  have hrow : c.row ∈ column.toList.map Cell.row := List.mem_map.mpr ⟨c, hc, rfl⟩
  rw [← hshape] at hrow
  obtain ⟨c', hc', he⟩ := List.mem_map.mp hrow
  exact ⟨c', (List.mergeSort_perm _ _).mem_iff.mp hc', he⟩

theorem assemble_rows (ctx : Context) {L : Nat} (hL : 1 ≤ L) (emits : List Emit)
    (he : ∀ e ∈ emits, RowDeg L e.row) :
    Ok (assemble ctx emits) (fun col => ∀ c ∈ col.toList, RowDeg L c.row) := by
  unfold assemble
  dsimp only
  split
  · exact ok_throw_bind _ _
  · refine ok_bind (ok_true _) (fun _ _ => ?_)
    refine ok_bind (ok_mapM (fun c : Cell => RowDeg L c.row) emits _ (fun em hem => ?_))
      (fun cells hcells => ?_)
    · split
      · exact ok_bind (ok_true _) (fun _ _ => ok_pure (rowDeg_stored hL (he em hem)))
      · split
        · exact ok_pure (rowDeg_stored hL (he em hem))
        · exact ok_throw _
    · intro col hcol
      unfold liftE Except.mapError at hcol
      cases hf : Expansion.finish ctx.result (Canonical.phantom :: cells) with
      | error e => rw [hf] at hcol; cases hcol
      | ok col' =>
        rw [hf] at hcol
        cases hcol
        intro c hc
        obtain ⟨c', hc', hrow⟩ := finish_rows hf c hc
        rw [← hrow]
        rcases List.mem_cons.mp hc' with rfl | hc'
        · intro i _
          exact Row.coeff_zero i
        · exact hcells c' hc'


theorem copyColumn_rows (ctx : Context) {L : Nat} (hL : 1 ≤ L) (hM : MDeg L ctx.source)
    {τ : Row} (hτ : RowDeg L τ) :
    Ok (copyColumn ctx τ) (fun col => ∀ c ∈ col.toList, RowDeg L c.row) := by
  have hlen : len τ ≤ L := len_le_iff.mpr hτ
  unfold copyColumn
  dsimp only
  let I : List Emit → Prop := fun emits => ∀ e ∈ emits, RowDeg L e.row
  refine ok_bind (ok_forIn I _ _ _ (by simp [I]) (fun p hp emits hI => ?_)) (fun emits hI => ?_)
  · obtain ⟨d, it⟩ := p
    obtain ⟨hd, j, hj⟩ := lowerItems_spec τ _ hp
    dsimp only at hd hj ⊢
    refine ok_bind (runItem_rows ctx d it (hj ▸ rowDeg_slot hτ (by omega) j) (by omega))
      (fun out hout => ok_pure ?_)
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hI e he
    · exact hout e he
  · refine ok_bind (ok_forIn I _ _ _ hI (fun p hp emits hI => ?_)) (fun emits hI => ?_)
    · obtain ⟨ref, cell⟩ := p
      obtain ⟨col, hcol, hcell⟩ := mem_realNodes hp
      dsimp only at hcell ⊢
      split
      · refine ok_bind (ok_true _) (fun _ _ => ok_pure ?_)
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hI e he
        · rw [List.mem_singleton.mp he]
          exact rowDeg_official hL (hM col hcol cell hcell)
      · exact ok_pure hI
    · exact assemble_rows ctx hL emits hI


theorem mDeg_pop {L : Nat} {M : Mountain} (h : MDeg L M) : MDeg L M.pop := by
  intro col hcol
  rw [Array.toList_pop] at hcol
  exact h col (List.mem_of_mem_dropLast hcol)

theorem mDeg_extract {L : Nat} {M : Mountain} (h : MDeg L M) (a b : Nat) :
    MDeg L (M.extract a b) := by
  intro col hcol
  rw [Array.toList_extract] at hcol
  rw [List.extract_eq_drop_take'] at hcol
  exact h col (List.mem_of_mem_take (List.mem_of_mem_drop hcol))

theorem mDeg_push {L : Nat} {M : Mountain} (h : MDeg L M) {col : Column}
    (hcol : ∀ c ∈ col.toList, RowDeg L c.row) : MDeg L (M.push col) := by
  intro col' hcol'
  rw [Array.toList_push] at hcol'
  rcases List.mem_append.mp hcol' with hm | hm
  · exact h col' hm
  · rw [List.mem_singleton.mp hm]
    exact hcol

theorem columnAt_mem (M : Mountain) (c : Nat) :
    Ok (Expansion.columnAt M c) (fun col => col ∈ M.toList) := by
  intro col h
  unfold Expansion.columnAt at h
  split at h
  · rename_i col' hc
    cases h
    exact List.mem_iff_getElem?.mpr ⟨c, by simpa using hc⟩
  · cases h

theorem top_mem (col : Column) : Ok (Expansion.top col) (fun t => t ∈ col.toList) := by
  intro t h
  unfold Expansion.top at h
  split at h
  · rename_i t' ht
    cases h
    rw [Array.back?_eq_getElem?] at ht
    exact List.mem_iff_getElem?.mpr ⟨_, by simpa using ht⟩
  · cases h

/-- **Dimension preservation for the executable diagram.** Every row of the output
diagram of the official expansion has degree below `L`, when every row of the input
canonical mountain does. -/
theorem expandDiagram_mDeg {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {L : Nat} (hL : 1 ≤ L) (hM : MDeg L M) (copies : Nat) :
    Ok (Official.expandDiagram s copies) (MDeg L) := by
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
  · exact ok_pure hM
  · refine ok_bind (ok_liftE (columnAt_mem M _)) (fun lastCol hlast => ?_)
    refine ok_bind (ok_liftE (top_mem lastCol)) (fun t ht => ?_)
    have hτ : RowDeg L (official t.row) := rowDeg_official hL (hM lastCol hlast t ht)
    split
    · exact ok_pure (mDeg_pop hM)
    · refine ok_bind (ok_true _) (fun root _ => ?_)
      split
      · exact ok_throw_bind _ _
      · refine ok_bind (ok_forIn (MDeg L) _ _ _ (mDeg_extract hM _ _)
          (fun i _ R hR => ?_)) (fun R hR => ok_pure hR)
        refine ok_bind (ok_forIn (MDeg L) _ _ _ hR (fun x _ R hR => ?_))
          (fun R hR => ok_pure hR)
        split
        · exact ok_throw_bind _ _
        · exact ok_bind (copyColumn_rows _ hL hM hτ) (fun col hcol => ok_pure (mDeg_push hR hcol))


theorem expandDiagram_degree {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {D : Nat} (hd : Reserve.degreeAtMost M D = true) {copies : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s copies = .ok R) : Reserve.degreeAtMost R D = true :=
  (mDeg_iff R D).mpr (expandDiagram_mDeg hb (by omega) ((mDeg_iff M D).mp hd) copies R hrun)

/-! ## From the diagram to the canonical mountain of the output -/

theorem expand_run {s : List Nat} {n : Nat} {out : List Nat} (h : Official.expand s n = .ok out) :
    ∃ R, Official.expandDiagram s n = .ok R ∧ Expansion.valuesOf R = .ok out := by
  unfold Official.expand at h
  cases hR : Official.expandDiagram s n with
  | error e => rw [hR] at h; cases h
  | ok R =>
    rw [hR] at h
    refine ⟨R, rfl, ?_⟩
    unfold liftE Except.mapError at h
    cases hv : Expansion.valuesOf R with
    | error e => simp [hv, bind, Except.bind] at h
    | ok v => simp [hv, bind, Except.bind] at h; rw [h]

theorem valuesOf_bottom {R : Mountain} {out : List Nat} (h : Expansion.valuesOf R = .ok out) :
    out.map some = bottomValues R := by
  unfold Expansion.valuesOf at h
  unfold bottomValues
  generalize R.toList = l at h ⊢
  induction l generalizing out with
  | nil => cases h; rfl
  | cons col rest ih =>
    rw [List.mapM_cons] at h
    cases hc : col[1]? with
    | none => simp [hc, bind, Except.bind] at h
    | some b =>
      simp only [hc, bind, Except.bind] at h
      split at h
      · cases h
      · rename_i vs hr
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [bottomValue, hc, ih hr]

/-- A canonical mountain of a prefix of `s` has only columns of `M(s)`. -/
theorem mDeg_of_prefix {s t : List Nat} {M MO : Mountain} (hb : Canonical.build s = .ok M)
    (ht : Canonical.build t = .ok MO) (hpre : t <+: s) {L : Nat} (hM : MDeg L M) :
    MDeg L MO := by
  obtain ⟨u, rfl⟩ := hpre
  intro col hcol
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hcol
  have hlt : c < MO.size := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simpa using this
  have hsize := build_size ht
  have ht' : Canonical.build (t ++ []) = .ok MO := by simpa using ht
  have heq := build_common_prefix ht' hb (column := c) (by omega)
  apply hM col
  apply List.mem_iff_getElem?.mpr ⟨c, ?_⟩
  rw [Array.getElem?_toList, ← heq, ← Array.getElem?_toList]
  exact hc

/-- The degree part of the classification, assuming that every row of the output
canonical mountain occurs in the output diagram (canonical reconstruction). -/
theorem output_degree_of_rowsSubset {s out : List Nat} {n D : Nat} {M MO : Mountain}
    (hb : Canonical.build s = .ok M) (hd : Reserve.degreeAtMost M D = true)
    (hrun : Official.expand s n = .ok out)
    (hrec : ∀ R, Official.expandDiagram s n = .ok R → RowsSubset MO R) :
    Reserve.degreeAtMost MO D = true := by
  obtain ⟨R, hR, -⟩ := expand_run hrun
  have hRd := (mDeg_iff R D).mp (expandDiagram_degree hb hd hR)
  apply (mDeg_iff MO D).mpr
  intro col hcol c hc
  have hocc : RowOccurs MO c.row := ⟨col, hcol, c, hc, rfl⟩
  obtain ⟨col', hcol', c', hc', hrow⟩ := hrec R hR c.row hocc
  rw [← hrow]
  exact hRd col' hcol' c' hc'


/-! ## Deletion expansions -/

theorem last_column_one {front : List Nat} {M : Mountain}
    (hb : Canonical.build (front ++ [1]) = .ok M) :
    ∃ col, M[M.size - 1]? = some col ∧ ∀ t, col.back? = some t → t.row = 1 := by
  obtain ⟨middle, -, hlast⟩ := buildFrom_append_success_iff.mp (buildFrom_of_build hb)
  simp [buildFrom, buildColumn, growColumn, initialColumn, bind, Except.bind] at hlast
  subst hlast
  refine ⟨#[phantom, (⟨1, 1, if middle = #[] then none else some ⟨middle.size - 1, 0⟩⟩ : Cell)],
    by simp, ?_⟩
  intro t ht
  simp at ht
  rw [← ht]

theorem official_one : official (1 : Row) = 0 := by
  have hfin : isFinite (1 : Row) = true := by
    unfold isFinite
    exact decide_eq_true (len_le_iff.mpr (rowDeg_nat le_rfl 1))
  simp only [official, hfin, if_true]
  rfl

theorem columnAt_get (M : Mountain) (c : Nat) :
    Ok (Expansion.columnAt M c) (fun col => M[c]? = some col) := by
  intro col h
  unfold Expansion.columnAt at h
  split at h
  · rename_i col' hc
    cases h
    exact hc
  · cases h

theorem top_get (col : Column) : Ok (Expansion.top col) (fun t => col.back? = some t) := by
  intro t h
  unfold Expansion.top at h
  split at h
  · rename_i t' ht
    cases h
    exact ht
  · cases h

/-- When the input is empty, the last entry is `1`, or `n = 0`, the output diagram is
the input mountain or the input mountain without its last column. -/
theorem expandDiagram_delete {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {n : Nat} (hdel : s = [] ∨ n = 0 ∨ s.getLast? = some 1) :
    Ok (Official.expandDiagram s n) (fun R => R = M ∨ R = M.pop) := by
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
  · exact ok_pure (Or.inl rfl)
  · rename_i hne
    refine ok_bind (ok_liftE (columnAt_get M _)) (fun lastCol hlast => ?_)
    refine ok_bind (ok_liftE (top_get lastCol)) (fun t ht => ?_)
    split
    · exact ok_pure (Or.inr rfl)
    · rename_i hτ
      exfalso
      apply hτ
      rcases hdel with hs | hn | h1
      · subst hs
        simp at hne
      · exact Or.inr hn
      · left
        obtain ⟨front, hs⟩ := List.getLast?_eq_some_iff.mp h1
        rw [hs] at hb
        obtain ⟨col, hcol, htop⟩ := last_column_one hb
        rw [hcol] at hlast
        cases hlast
        rw [htop t ht]
        exact official_one


/-- **Dimension preservation for deletion expansions**, with no further assumption:
when the input is empty, its last entry is `1`, or `n = 0`, every row of the output
canonical mountain has degree at most `D`. -/
theorem output_degree_delete {s out : List Nat} {n D : Nat} {M MO : Mountain}
    (hb : Canonical.build s = .ok M) (hd : Reserve.degreeAtMost M D = true)
    (hdel : s = [] ∨ n = 0 ∨ s.getLast? = some 1)
    (hrun : Official.expand s n = .ok out) (hMO : Canonical.build out = .ok MO) :
    Reserve.degreeAtMost MO D = true := by
  obtain ⟨R, hR, hv⟩ := expand_run hrun
  have hout := valuesOf_bottom hv
  have hs := build_bottom_values hb
  have hinj : Function.Injective (List.map (some : Nat → Option Nat)) :=
    List.map_injective_iff.mpr (Option.some_injective _)
  have hpre : out <+: s := by
    rcases expandDiagram_delete hb hdel R hR with rfl | rfl
    · rw [hs] at hout
      rw [hinj hout]
    · have hpop : bottomValues M.pop = (s.dropLast).map some := by
        unfold bottomValues
        rw [Array.toList_pop, List.map_dropLast]
        unfold bottomValues at hs
        rw [hs, List.map_dropLast]
      rw [hpop] at hout
      rw [hinj hout]
      exact List.dropLast_prefix s
  exact (mDeg_iff MO D).mpr (mDeg_of_prefix hb hMO hpre ((mDeg_iff M D).mp hd))


/-! ## The degree part of the classification -/

/-- The degree part of the classification, assuming that the canonical mountain of
the output is the output diagram (the form of Phyrion's `expandDiagram_reconstruct`
for the weak rule; `Check.lean` checks it on 474 fixtures as `canonicalAgree`). -/
theorem output_degree_of_reconstruct {s out : List Nat} {n D : Nat} {M MO : Mountain}
    (hb : Canonical.build s = .ok M) (hd : Reserve.degreeAtMost M D = true)
    (hrun : Official.expand s n = .ok out) (hMO : Canonical.build out = .ok MO)
    (hrec : ∀ R, Official.expandDiagram s n = .ok R → Canonical.build out = .ok R) :
    Reserve.degreeAtMost MO D = true := by
  obtain ⟨R, hR, -⟩ := expand_run hrun
  have hMOR : MO = R := Except.ok.inj (hMO.symm.trans (hrec R hR))
  rw [hMOR]
  exact expandDiagram_degree hb hd hR

/-- Canonical reconstruction for the official rule, restricted to expansions that
add blocks: the canonical mountain of the output values is the output diagram. -/
def BlockReconstruction : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain) (out : List Nat),
    ¬ (s = [] ∨ n = 0 ∨ s.getLast? = some 1) →
    Official.expandDiagram s n = .ok R → Expansion.valuesOf R = .ok out →
    Canonical.build out = .ok R

/-- **Item 2 of `notes/04-official-design.md` §6 (dimension preservation)**, from
canonical reconstruction for block-adding expansions. Deletion expansions need no
assumption (`output_degree_delete`). -/
theorem output_degree (hrec : BlockReconstruction) {s out : List Nat} {n D : Nat}
    {M MO : Mountain} (hb : Canonical.build s = .ok M) (hd : Reserve.degreeAtMost M D = true)
    (hrun : Official.expand s n = .ok out) (hMO : Canonical.build out = .ok MO) :
    Reserve.degreeAtMost MO D = true := by
  by_cases hdel : s = [] ∨ n = 0 ∨ s.getLast? = some 1
  · exact output_degree_delete hb hd hdel hrun hMO
  · obtain ⟨R₀, hR₀, hv⟩ := expand_run hrun
    refine output_degree_of_reconstruct hb hd hrun hMO (fun R hR => ?_)
    have : R₀ = R := Except.ok.inj (hR₀.symm.trans hR)
    subst this
    exact hrec s n R₀ out hdel hR₀ hv

end OmegaY.Official.Dimension

#print axioms OmegaY.Official.Dimension.expandDiagram_degree
#print axioms OmegaY.Official.Dimension.output_degree_delete
#print axioms OmegaY.Official.Dimension.output_degree_of_rowsSubset
#print axioms OmegaY.Official.Dimension.output_degree
