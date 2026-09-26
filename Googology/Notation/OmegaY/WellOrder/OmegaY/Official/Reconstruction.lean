/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Reconstruction.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Descent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Values
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.Finish

set_option backward.do.legacy false

/-!
# The output mountain of the official expansion: size, legality, prefix

This file proves, for the official expansion `Official.expandDiagram` /
`Official.expand` (`Build.lean`), the facts that `notes/04-official-design.md` §6
lists as items 1 and 3 of `ClassificationHolds`, as far as they are proved here:

* **Length (item 3).** When `s[n]` succeeds, it has `x₀ + n·w` terms, or one term
  less than `s` when the top of the last column is on the bottom row (the last term
  is 1) or `n = 0` (`expand_length_delete`, `expand_length_splice`). The numbers
  are the ones `Reserve.root?` reads, so this is exactly the length conjunct of
  `Reserve.classifiedB`.
* **The output mountain can be built (item 1, first half).** The output is a legal
  sequence, so `Canonical.build` succeeds on it (`expand_build_ok`).
* **Reconstruction on the unchanged prefix (item 1, second half, partly).** The
  canonical mountain of the output and the assembled mountain agree on the columns
  `0, …, x₀ - 1` (`expand_build_prefix`), and they are equal when the expansion
  only deletes the last term (`expand_build_eq_delete`). That they are equal in
  general is stated as `ReconstructionHolds` and is not proved.
* **The classification check without items 1 and 3.** For a nonempty `s`,
  `classifiedB s n D` equals the conjunction of the degree checks and the atom
  classification `atomsClassified` (`classifiedB_eq`), so `ClassificationHolds`
  for nonempty sequences reduces to items 2 and 4 (`classificationHoldsNE_of_parts`).
* **Correction.** `Descent.ClassificationHolds` is false: for `s = []` the check
  `out.length + 1 = s.length` fails (`not_classificationHolds`). The descent only
  uses nonempty `s` (`Step` requires `s ≠ []`), so the well-foundedness theorem is
  restated with the nonempty version `ClassificationHoldsNE`
  (`wellFounded_of_classificationNE`).

The proofs read the program `expandDiagram` directly; they use no property of the
official rule beyond the shape of its loops and the success of `Expansion.finish`.
-/

namespace OmegaY.Official.Reconstruction

open Canonical Reserve

/-! ## Except and loops -/

section Loops

variable {ε α β γ : Type}

theorem bind_ok {x : Except ε α} {f : α → Except ε β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem liftE_ok {x : Expansion.Result α} {a : α} (h : liftE x = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => cases h; rfl

theorem mapError_ok {ε' : Type} {g : ε → ε'} {x : Except ε α} {a : α}
    (h : x.mapError g = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok b => cases h; rfl

/-- An invariant of a successful `for` loop in `Except` whose body always yields. -/
theorem forIn_invariant (P : γ → Prop) :
    ∀ {l : List α} {f : α → γ → Except ε (ForInStep γ)},
      (∀ a ∈ l, ∀ b y, P b → f a b = .ok y → ∃ b', y = .yield b' ∧ P b') →
      ∀ {init r : γ}, P init → forIn l init f = .ok r → P r
  | [], f, _, init, r, hi, h => by
      have h' : (Except.ok init : Except ε γ) = .ok r := h
      cases h'
      exact hi
  | a :: l, f, hf, init, r, hi, h => by
      rw [List.forIn_cons] at h
      obtain ⟨y, hy, h⟩ := bind_ok h
      obtain ⟨b', rfl, hb'⟩ := hf a (List.mem_cons_self) init y hi hy
      exact forIn_invariant P (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) hb' h

/-- An additive measure of a successful `for` loop in `Except` whose body always
yields. -/
theorem forIn_sum (g : γ → Nat) (k : α → Nat) :
    ∀ {l : List α} {f : α → γ → Except ε (ForInStep γ)},
      (∀ a ∈ l, ∀ b y, f a b = .ok y → ∃ b', y = .yield b' ∧ g b' = g b + k a) →
      ∀ {init r : γ}, forIn l init f = .ok r → g r = g init + (l.map k).sum
  | [], f, _, init, r, h => by
      have h' : (Except.ok init : Except ε γ) = .ok r := h
      cases h'
      simp
  | a :: l, f, hf, init, r, h => by
      rw [List.forIn_cons] at h
      obtain ⟨y, hy, h⟩ := bind_ok h
      obtain ⟨b', rfl, hb'⟩ := hf a (List.mem_cons_self) init y hy
      have := forIn_sum g k (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) h
      simp only [List.map_cons, List.sum_cons]
      omega

end Loops

/-! ## Values of a mountain -/

/-- A successful `valuesOf` reads the bottom value of every column. -/
theorem valuesOf_ok {R : Mountain} {out : List Nat} (h : Expansion.valuesOf R = .ok out) :
    Canonical.bottomValues R = out.map some := by
  unfold Expansion.valuesOf at h
  unfold Canonical.bottomValues
  generalize R.toList = cols at h ⊢
  induction cols generalizing out with
  | nil =>
      have h' : (Except.ok [] : Expansion.Result (List Nat)) = .ok out := h
      cases h'
      rfl
  | cons col cols ih =>
      rw [List.mapM_cons] at h
      obtain ⟨v, hv, h⟩ := bind_ok h
      obtain ⟨vs, hvs, h⟩ := bind_ok h
      have h' : (Except.ok (v :: vs) : Expansion.Result (List Nat)) = .ok out := h
      cases h'
      simp only [List.map_cons, ih hvs, List.cons.injEq, and_true]
      simp only [bottomValue]
      split at hv
      · rename_i bottom hb
        cases hv
        simp [hb]
      · cases hv

theorem valuesOf_length {R : Mountain} {out : List Nat} (h : Expansion.valuesOf R = .ok out) :
    out.length = R.size := by
  have := congrArg List.length (valuesOf_ok h)
  simpa [Canonical.bottomValues] using this.symm

/-! ## Finished columns -/

theorem backfilled_dropLast_pos {M : Mountain} {u : Cell} {rest : List Cell}
    (h : Expansion.Backfilled M u rest) (hu : 0 < u.value) :
    ∀ c ∈ (u :: rest).dropLast, 0 < c.value := by
  induction h with
  | nil upper =>
      intro c hc
      simp at hc
  | phantom upper lower _ _ =>
      intro c hc
      simp only [List.dropLast_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hu
      · simp at hc
  | @next upper lower rest ref parent _ _ _ hpos hvalue _ ih =>
      intro c hc
      have hl : 0 < lower.value := by omega
      rw [List.dropLast_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hu
      · exact ih hl c hc

/-- The bottom real node of a column returned by `Expansion.finish` has a positive
value. -/
theorem finish_bottom_pos {m : Mountain} {cells : List Cell} {col : Column}
    (h : Expansion.finish m cells = .ok col) {c : Cell} (hc : col[1]? = some c) :
    0 < c.value := by
  obtain ⟨_, upper, rest, hrev, hone, hback, _⟩ := Expansion.finish_success_spec h
  have hlist : col.toList = (upper :: rest).reverse := by
    rw [← hrev, List.reverse_reverse]
  have hne : (upper :: rest) ≠ [] := List.cons_ne_nil _ _
  have hsplit := List.dropLast_append_getLast hne
  have hc' : col.toList[1]? = some c := by simpa using hc
  rw [hlist, ← hsplit, List.reverse_append] at hc'
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.getElem?_cons_succ] at hc'
  have hmem : c ∈ (upper :: rest).dropLast := by
    have := List.mem_of_getElem? hc'
    simpa using this
  exact backfilled_dropLast_pos hback (by omega) c hmem

/-- A column made by `copyColumn` is returned by `Expansion.finish`. -/
theorem copyColumn_finish {ctx : Context} {τ : Row} {col : Column}
    (h : copyColumn ctx τ = .ok col) :
    ∃ m cells, Expansion.finish m cells = .ok col := by
  unfold copyColumn at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨emits, _, h⟩ := bind_ok h
  unfold assemble at h
  dsimp only at h
  split at h
  · obtain ⟨_, h1, _⟩ := bind_ok h
    cases h1
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨cells, _, h⟩ := bind_ok h
    exact ⟨_, _, liftE_ok h⟩

/-! ## The loops of `expandDiagram` -/

/-- A column returned by `Expansion.finish`. -/
def Finished (col : Column) : Prop := ∃ m cells, Expansion.finish m cells = .ok col

/-- The loop invariant of `expandDiagram`: the first `x₀` columns are those of `M`,
and every later column is a finished column. -/
def Good (M : Mountain) (x0 : Nat) (R : Mountain) : Prop :=
  x0 ≤ R.size ∧ (∀ c, c < x0 → R[c]? = M[c]?) ∧
    (∀ c col, x0 ≤ c → R[c]? = some col → Finished col)

theorem good_init {M : Mountain} {x0 : Nat} (hx : x0 ≤ M.size) :
    Good M x0 (M.extract 0 x0) := by
  refine ⟨by simp [Nat.min_eq_left hx], ?_, ?_⟩
  · intro c hc
    simp [Nat.min_eq_left hx, hc]
  · intro c col hc hcol
    simp [Array.getElem?_extract, Nat.min_eq_left hx] at hcol
    omega

theorem good_push {M : Mountain} {x0 : Nat} {R : Mountain} {col : Column}
    (h : Good M x0 R) (hc : Finished col) : Good M x0 (R.push col) := by
  obtain ⟨hs, hpre, hfin⟩ := h
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro c hcx
    rw [Array.getElem?_push]
    rw [if_neg (by omega)]
    exact hpre c hcx
  · intro c col' hcx hcol
    rw [Array.getElem?_push] at hcol
    split at hcol
    · cases hcol
      exact hc
    · exact hfin c col' hcx hcol

/-- The shape of a successful run of `expandDiagram`. -/
theorem expandDiagram_cases {s : List Nat} {n : Nat} {R : Mountain}
    (h : expandDiagram s n = .ok R) :
    ∃ M, Canonical.build s = .ok M ∧
      ((s = [] ∧ R = M) ∨
       (s ≠ [] ∧ ∃ col t, M[M.size - 1]? = some col ∧ col.back? = some t ∧
         (((official t.row = 0 ∨ n = 0) ∧ R = M.pop) ∨
          (official t.row ≠ 0 ∧ n ≠ 0 ∧ ∃ root, t.left = some root ∧
            root.column < M.size - 1 ∧
            R.size = (M.size - 1) + ((List.range (n + 1)).map
              (fun i => (blockColumns root.column (M.size - 1) n i).length)).sum ∧
            Good M (M.size - 1) R)))) := by
  unfold expandDiagram at h
  obtain ⟨M, hM, h⟩ := bind_ok h
  refine ⟨M, mapError_ok (liftE_ok hM), ?_⟩
  split at h
  · rename_i hs
    left
    refine ⟨List.isEmpty_iff.mp hs, ?_⟩
    cases h
    rfl
  · rename_i hs
    right
    refine ⟨fun he => hs (by simp [he]), ?_⟩
    obtain ⟨col, hcol, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    have hcol' : M[M.size - 1]? = some col := by
      have := liftE_ok hcol
      unfold Expansion.columnAt at this
      split at this
      · cases this; assumption
      · cases this
    have ht' : col.back? = some t := by
      have := liftE_ok ht
      unfold Expansion.top at this
      split at this
      · cases this; assumption
      · cases this
    refine ⟨col, t, hcol', ht', ?_⟩
    dsimp only at h
    split at h
    · rename_i hτ
      left
      exact ⟨hτ, by cases h; rfl⟩
    · rename_i hτ
      right
      have hτ' : official t.row ≠ 0 := fun e => hτ (Or.inl e)
      have hn : n ≠ 0 := fun e => hτ (Or.inr e)
      obtain ⟨root, hroot, h⟩ := bind_ok h
      have hroot' : t.left = some root := by
        have := liftE_ok hroot
        unfold Expansion.leftOf at this
        split at this
        · cases this; assumption
        · cases this
      split at h
      · obtain ⟨_, h1, _⟩ := bind_ok h
        cases h1
      · rename_i hcr
        have hcr' : root.column < M.size - 1 := not_not.mp hcr
        obtain ⟨R1, hR1, h⟩ := bind_ok h
        cases h
        refine ⟨hτ', hn, root, hroot', hcr', ?_, ?_⟩
        · have hsum := forIn_sum Array.size
            (fun i => (blockColumns root.column (M.size - 1) n i).length) ?_ hR1
          · rw [hsum]
            simp only [Array.size_extract]
            omega
          · intro i _ S y hy
            obtain ⟨S', hS', hy⟩ := bind_ok hy
            cases hy
            refine ⟨S', rfl, ?_⟩
            have hin := forIn_sum Array.size (fun _ => 1) ?_ hS'
            · rw [hin]
              simp
            · intro x _ S0 y0 hy0
              split at hy0
              · obtain ⟨_, h1, _⟩ := bind_ok hy0
                cases h1
              · obtain ⟨c, _, hy0⟩ := bind_ok hy0
                cases hy0
                exact ⟨_, rfl, by simp⟩
        · refine forIn_invariant (Good M (M.size - 1)) ?_ (good_init (by omega)) hR1
          intro i _ S y hS hy
          obtain ⟨S', hS', hy⟩ := bind_ok hy
          cases hy
          refine ⟨S', rfl, ?_⟩
          refine forIn_invariant (Good M (M.size - 1)) ?_ hS hS'
          intro x _ S0 y0 hS0 hy0
          split at hy0
          · obtain ⟨_, h1, _⟩ := bind_ok hy0
            cases h1
          · obtain ⟨c, hc, hy0⟩ := bind_ok hy0
            cases hy0
            exact ⟨_, rfl, good_push hS0 (copyColumn_finish hc)⟩

/-! ## The number of columns -/

theorem blockColumns_length (cr x0 n i : Nat) : (blockColumns cr x0 n i).length =
    if i = 0 then 1 else if i < n then x0 - cr else x0 - cr - 1 := by
  unfold blockColumns
  split <;> simp

theorem sum_first_blocks (w n : Nat) : ∀ m, m ≤ n →
    ((List.range m).map (fun i => if i = 0 then 1 else if i < n then w else w - 1)).sum =
      if m = 0 then 0 else 1 + (m - 1) * w
  | 0, _ => by simp
  | m + 1, hm => by
      rw [List.range_succ, List.map_append, List.sum_append, sum_first_blocks w n m (by omega)]
      rcases m with _ | k
      · simp
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_one_ne_zero, if_false, show k + 1 < n by omega, if_true,
          Nat.add_sub_cancel, Nat.succ_mul]
        omega

/-- The blocks `0, …, n` of `blockColumns` have `n · w` columns in total. -/
theorem sum_blocks {cr x0 n : Nat} (hcr : cr < x0) (hn : n ≠ 0) :
    ((List.range (n + 1)).map (fun i => (blockColumns cr x0 n i).length)).sum =
      n * (x0 - cr) := by
  simp only [blockColumns_length]
  rw [List.range_succ, List.map_append, List.sum_append,
    sum_first_blocks (x0 - cr) n n (le_refl n)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_one_ne_zero, if_false, Nat.lt_irrefl, Nat.add_sub_cancel, Nat.succ_mul]
  omega

/-! ## The root data read by `Reserve.root?` -/

/-- A real row above the bottom row is not official row `0`. -/
theorem official_ne_zero {r : Row} (h : (1 : Row) < r) : official r ≠ 0 := by
  unfold official
  split
  · rename_i hfin
    intro h0
    have hc0 := congrArg (fun q : Row => q.coeff 0) h0
    simp only [Row.coeff_nat, if_true, Row.coeff_zero] at hc0
    have hsup : r.coeffs.support.sup (fun i => i + 1) ≤ 1 := by
      have hf : decide ((List.map r.coeff (List.range (r.coeffs.support.sup fun i => i + 1))).length
          ≤ 1) = true := hfin
      simpa only [decide_eq_true_eq, List.length_map, List.length_range] using hf
    have hhigh : ∀ i, 1 ≤ i → r.coeff i = 0 := by
      intro i hi
      by_contra hne
      have hmem : i ∈ r.coeffs.support := Finsupp.mem_support_iff.mpr hne
      have hle : i + 1 ≤ r.coeffs.support.sup (fun i => i + 1) :=
        Finset.le_sup (f := fun i => i + 1) hmem
      omega
    have hle : r ≤ 1 := Row.le_of_coeff_le (fun i => by
      rcases i with _ | i
      · have h1 : (1 : Row).coeff 0 = 1 := Row.coeff_nat 1 0
        rw [h1]
        omega
      · rw [hhigh _ (by omega)]
        exact Nat.zero_le _)
    exact absurd h (not_lt_of_ge hle)
  · intro h0
    rw [h0] at h
    exact absurd h (not_lt_of_ge (Row.zero_le 1))

theorem highestAtMost_some {M : Mountain} (hV : MountainValid M) {l : Nat} (hl : l < M.size)
    {row : Row} (hrow : (1 : Row) ≤ row) : ∃ p, highestAtMost M l row = some p := by
  have hCV := hV l hl
  have h2 := hCV.size_ge_two
  have hb1 : 1 < M[l].size := by omega
  have hrow1 : M[l][1].row = 1 := hCV.bottom_row _ (Array.getElem?_eq_getElem hb1)
  let L := (List.range M[l].size).filter fun j =>
    0 < j && (match M[l][j]? with | some c => decide (c.row ≤ row) | none => false)
  have hmem : 1 ∈ L := by
    simp only [L, List.mem_filter, List.mem_range, hb1, true_and, Bool.and_eq_true,
      decide_eq_true_eq, Array.getElem?_eq_getElem hb1, hrow1]
    exact ⟨by omega, hrow⟩
  cases hlast : L.getLast? with
  | none =>
      rw [List.getLast?_eq_none_iff] at hlast
      rw [hlast] at hmem
      simp at hmem
  | some j =>
      refine ⟨⟨l, j⟩, ?_⟩
      simp only [highestAtMost, Array.getElem?_eq_getElem hl, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
      change (L.getLast?.bind fun j => some (⟨l, j⟩ : Ref)) = _
      rw [hlast]
      rfl

/-- The top of the last column is above the bottom row exactly when `root?` reads
the root; this is the direction from the program to `root?`. -/
theorem root?_of_top {M : Mountain} (hV : MountainValid M) (D : Nat) {col : Column} {t : Cell}
    {root : Ref} (hcol : M[M.size - 1]? = some col) (ht : col.back? = some t)
    (hτ : official t.row ≠ 0) (hroot : t.left = some root) (hcr : root.column < M.size - 1) :
    ∃ K, root? M D = some ⟨M.size - 1, root.column, K⟩ := by
  have hsz : M.size - 1 < M.size := (Array.getElem?_eq_some_iff.mp hcol).1
  have hcolEq : M[M.size - 1] = col := (Array.getElem?_eq_some_iff.mp hcol).2
  have hCV : ColumnValid M (M.size - 1) col := hcolEq ▸ hV _ hsz
  have h2 := hCV.size_ge_two
  have ht' : col[col.size - 1]? = some t := by rw [← Array.back?_eq_getElem?]; exact ht
  have hb1 : 1 < col.size := by omega
  have hbot : col[1].row = 1 := hCV.bottom_row _ (Array.getElem?_eq_getElem hb1)
  have hbig : ¬ col.size - 1 ≤ 1 := by
    intro hle
    have he : col.size - 1 = 1 := by omega
    rw [he, Array.getElem?_eq_getElem hb1] at ht'
    cases ht'
    rw [hbot] at hτ
    exact hτ (by decide)
  have hrow : (1 : Row) < t.row := by
    have := hCV.rows_strict 1 (col.size - 1) col[1] t (Array.getElem?_eq_getElem hb1) ht'
      (by omega)
    rwa [hbot] at this
  obtain ⟨p, hp⟩ := highestAtMost_some hV (show root.column < M.size by omega) (le_of_lt hrow)
  have hcell : cell? M ⟨M.size - 1, col.size - 1⟩ = some t := by
    simp [cell?, hcol, ht']
  have hla : legAtom? M D ⟨M.size - 1, col.size - 1⟩ =
      some ⟨root.column, M.size - 1, keyAt M D t.row p⟩ := by
    simp [legAtom?, hcell, hroot, hp]
  refine ⟨keyAt M D t.row p, ?_⟩
  unfold root?
  simp only [hcol, hbig, if_false, ht', hroot, hla, if_true]

/-- The direction from `root?` to the program. -/
theorem top_of_root? {M : Mountain} (hV : MountainValid M) {D : Nat} {ρ : Root}
    (h : root? M D = some ρ) {col : Column} {t : Cell}
    (hcol : M[M.size - 1]? = some col) (ht : col.back? = some t) :
    official t.row ≠ 0 ∧ ρ.x0 = M.size - 1 ∧ ∃ r, t.left = some r ∧ ρ.cr = r.column := by
  have hsz : M.size - 1 < M.size := (Array.getElem?_eq_some_iff.mp hcol).1
  have hcolEq : M[M.size - 1] = col := (Array.getElem?_eq_some_iff.mp hcol).2
  have hCV : ColumnValid M (M.size - 1) col := hcolEq ▸ hV _ hsz
  have h2 := hCV.size_ge_two
  have ht' : col[col.size - 1]? = some t := by rw [← Array.back?_eq_getElem?]; exact ht
  have hb1 : 1 < col.size := by omega
  have hbot : col[1].row = 1 := hCV.bottom_row _ (Array.getElem?_eq_getElem hb1)
  unfold root? at h
  simp only [hcol] at h
  split at h
  · cases h
  · rename_i hbig
    have hrow : (1 : Row) < t.row := by
      have := hCV.rows_strict 1 (col.size - 1) col[1] t (Array.getElem?_eq_getElem hb1) ht'
        (by omega)
      rwa [hbot] at this
    refine ⟨official_ne_zero hrow, ?_⟩
    simp only [ht'] at h
    cases hl : t.left with
    | none => simp [hl] at h
    | some r =>
        simp only [hl] at h
        split at h
        · cases h
        · split at h
          · cases h
            exact ⟨rfl, r, rfl, rfl⟩
          · cases h

/-! ## Item 3: the length of the output -/

theorem expand_ok {s : List Nat} {n : Nat} {out : List Nat} (h : expand s n = .ok out) :
    ∃ R, expandDiagram s n = .ok R ∧ Expansion.valuesOf R = .ok out := by
  unfold expand at h
  obtain ⟨R, hR, h⟩ := bind_ok h
  exact ⟨R, hR, liftE_ok h⟩

theorem build_eq {s : List Nat} {M M' : Mountain} (h : Canonical.build s = .ok M)
    (h' : Canonical.build s = .ok M') : M' = M := by
  rw [h] at h'
  injection h' with e
  exact e.symm

/-- **Length, deletion case.** When the top of the last column is on the bottom row
(`root?` reads no root; the last term is 1) or `n = 0`, `s[n]` is one term shorter
than `s`. -/
theorem expand_length_delete {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    (hs : s ≠ []) (hM : Canonical.build s = .ok M) (h : expand s n = .ok out)
    (hcase : root? M D = none ∨ n = 0) : out.length + 1 = s.length := by
  obtain ⟨R, hR, hv⟩ := expand_ok h
  rw [valuesOf_length hv, ← Canonical.build_size hM]
  obtain ⟨M', hM', hcases⟩ := expandDiagram_cases hR
  obtain rfl := build_eq hM hM'
  have hV := Canonical.build_valid_of_success hM
  have hpos : 0 < M'.size := by
    rw [Canonical.build_size hM]; exact List.length_pos_iff.mpr hs
  rcases hcases with ⟨he, _⟩ | ⟨_, col, t, hcol, ht, ⟨_, rfl⟩ | ⟨hτ, hn, root, hroot, hcr, _, _⟩⟩
  · exact absurd he hs
  · simp only [Array.size_pop]
    omega
  · exfalso
    obtain ⟨K, hK⟩ := root?_of_top hV D hcol ht hτ hroot hcr
    rcases hcase with h0 | h0
    · rw [hK] at h0; cases h0
    · exact hn h0

/-- **Length, splice case.** When `root?` reads the last column `x₀` and the root
column `c_r`, and `n ≠ 0`, `s[n]` has `x₀ + n·(x₀ - c_r)` terms. -/
theorem expand_length_splice {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    {ρ : Root} (hM : Canonical.build s = .ok M) (h : expand s n = .ok out)
    (hroot : root? M D = some ρ) (hn : n ≠ 0) : out.length = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
  obtain ⟨R, hR, hv⟩ := expand_ok h
  rw [valuesOf_length hv]
  obtain ⟨M', hM', hcases⟩ := expandDiagram_cases hR
  obtain rfl := build_eq hM hM'
  have hV := Canonical.build_valid_of_success hM
  obtain ⟨hx, hcrx, _⟩ := root?_spec hV hroot
  rcases hcases with ⟨he, _⟩ | ⟨_, col, t, hcol, ht, ⟨hτ, _⟩ | ⟨_, _, root, hroot', hcr, hsize, _⟩⟩
  · subst he
    rw [Canonical.build_size hM] at hx
    simp at hx
  · obtain ⟨hτ', _⟩ := top_of_root? hV hroot hcol ht
    rcases hτ with h0 | h0
    · exact absurd h0 hτ'
    · exact absurd h0 hn
  · obtain ⟨_, hx0, r, hr, hcr'⟩ := top_of_root? hV hroot hcol ht
    rw [hroot'] at hr
    injection hr with e
    subst e
    rw [hsize, sum_blocks hcr hn, hx0, hcr']

/-! ## Item 1: the output mountain can be built -/

theorem legal_dropLast {s : List Nat} (h : Legal s) : Legal s.dropLast := by
  rcases h with rfl | ⟨rest, rfl, hpos⟩
  · exact Or.inl rfl
  · rcases rest with _ | ⟨a, rest⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨(a :: rest).dropLast, by simp, ?_⟩
      intro v hv
      exact hpos v (List.mem_of_mem_dropLast hv)

theorem legal_pos {s : List Nat} (h : Legal s) : ∀ v ∈ s, 0 < v := by
  rcases h with rfl | ⟨rest, rfl, hpos⟩
  · simp
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact hpos v hv

theorem legal_of {out : List Nat} (hpos : ∀ v ∈ out, 0 < v) (hhead : out = [] ∨ out[0]? = some 1) :
    Legal out := by
  rcases out with _ | ⟨a, rest⟩
  · exact Or.inl rfl
  · rcases hhead with h | h
    · cases h
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact Or.inr ⟨rest, rfl, fun v hv => hpos v (List.mem_cons_of_mem _ hv)⟩

theorem map_some_inj {a b : List Nat} (h : a.map some = b.map some) : a = b :=
  List.map_injective_iff.mpr (fun _ _ e => Option.some.inj e) h

/-- The values of `M.pop` are the values of `s` without the last term. -/
theorem valuesOf_pop {s : List Nat} {M : Mountain} {out : List Nat}
    (hM : Canonical.build s = .ok M) (hv : Expansion.valuesOf M.pop = .ok out) :
    out = s.dropLast := by
  have h1 := valuesOf_ok hv
  have h2 := Canonical.build_bottom_values hM
  apply map_some_inj
  rw [← h1, List.map_dropLast, ← h2]
  simp [Canonical.bottomValues, Array.toList_pop, List.map_dropLast]

/-- The bottom value of column `c` of a mountain whose values are `out`. -/
theorem bottomValue_at {R : Mountain} {out : List Nat} (hv : Expansion.valuesOf R = .ok out)
    {c : Nat} {col : Column} (hc : R[c]? = some col) :
    ∃ v, out[c]? = some v ∧ bottomValue col = some v := by
  have h1 := congrArg (fun xs : List (Option Nat) => xs[c]?) (valuesOf_ok hv)
  simp only [Canonical.bottomValues, List.getElem?_map, Array.getElem?_toList, hc,
    Option.map_some] at h1
  cases ho : out[c]? with
  | none => simp [ho] at h1
  | some v =>
      simp only [ho, Option.map_some, Option.some.injEq] at h1
      exact ⟨v, rfl, h1⟩

theorem mem_values {R : Mountain} {out : List Nat} (hv : Expansion.valuesOf R = .ok out)
    {v : Nat} (hmem : v ∈ out) :
    ∃ (c : Nat) (col : Column) (cell : Cell), R[c]? = some col ∧ col[1]? = some cell ∧
      cell.value = v := by
  have h1 := valuesOf_ok hv
  have : some v ∈ Canonical.bottomValues R := by rw [h1]; exact List.mem_map_of_mem hmem
  obtain ⟨col, hcol, hb⟩ := List.mem_map.mp this
  obtain ⟨c, hc⟩ := List.mem_iff_getElem?.mp hcol
  simp only [bottomValue, Option.map_eq_some_iff] at hb
  obtain ⟨cell, hcell, hval⟩ := hb
  exact ⟨c, col, cell, by simpa using hc, hcell, hval⟩

/-- **The output is legal.** Every successful official expansion returns a legal
sequence. -/
theorem expand_legal {s : List Nat} {n : Nat} {out : List Nat} (h : expand s n = .ok out) :
    Legal out := by
  obtain ⟨R, hR, hv⟩ := expand_ok h
  obtain ⟨M, hM, hcases⟩ := expandDiagram_cases hR
  have hV := Canonical.build_valid_of_success hM
  have hL := Canonical.build_success_legal hM
  rcases hcases with ⟨rfl, rfl⟩ | ⟨_, col, t, hcol, ht, ⟨_, rfl⟩ | ⟨_, _, root, _, hcr, _, hgood⟩⟩
  · have := valuesOf_length hv
    rw [Canonical.build_size hM] at this
    simp only [List.length_nil] at this
    rw [List.length_eq_zero_iff.mp this]
    exact Or.inl rfl
  · rw [valuesOf_pop hM hv]
    exact legal_dropLast hL
  · obtain ⟨_, hpre, hfin⟩ := hgood
    apply legal_of
    · intro v hmem
      obtain ⟨c, col', cell, hc, hcell, rfl⟩ := mem_values hv hmem
      by_cases hcx : c < M.size - 1
      · rw [hpre c hcx] at hc
        obtain ⟨hcM, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hc
        have hCV : ColumnValid M c col' := hcolEq ▸ hV c hcM
        exact hCV.real_positive 1 cell hcell (by omega)
      · obtain ⟨m, cells, hf⟩ := hfin c col' (by omega) hc
        exact finish_bottom_pos hf hcell
    · right
      have h0 : (0 : Nat) < M.size - 1 := by omega
      have hR0 := hpre 0 h0
      obtain ⟨col0, hc0⟩ : ∃ col0, M[0]? = some col0 :=
        ⟨M[0], Array.getElem?_eq_getElem (by omega)⟩
      rw [hc0] at hR0
      obtain ⟨v, hv0, hb0⟩ := bottomValue_at hv hR0
      have hs0 := congrArg (fun xs : List (Option Nat) => xs[0]?) (Canonical.build_bottom_values hM)
      simp only [Canonical.bottomValues, List.getElem?_map, Array.getElem?_toList, hc0,
        Option.map_some, hb0] at hs0
      rcases hL with rfl | ⟨rest, rfl, _⟩
      · simp at hs0
      · simp only [List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hs0
        rw [hv0, hs0]

/-- **Item 1, the output mountain can be built.** -/
theorem expand_build_ok {s : List Nat} {n : Nat} {out : List Nat} (h : expand s n = .ok out) :
    ∃ MO, Canonical.build out = .ok MO ∧ MountainValid MO ∧ MO.size = out.length := by
  obtain ⟨MO, hMO, hV, _, hsz⟩ := Canonical.build_total_with_size (expand_legal h)
  exact ⟨MO, hMO, hV, hsz⟩

/-! ## Item 1: the output mountain is the assembled mountain, where proved -/

/-- The canonical mountain of `s` without its last term is `M(s)` without its last
column. -/
theorem build_dropLast {s : List Nat} {M : Mountain} (hM : Canonical.build s = .ok M) :
    Canonical.build s.dropLast = .ok M.pop := by
  obtain ⟨MO, hMO, _, _, hsz⟩ :=
    Canonical.build_total_with_size (legal_dropLast (Canonical.build_success_legal hM))
  have hMs := Canonical.build_size hM
  rcases List.eq_nil_or_concat' s with rfl | ⟨front, last, rfl⟩
  · have : M = #[] := by
      have h0 : Canonical.build ([] : List Nat) = .ok #[] := rfl
      exact build_eq h0 hM
    subst this
    rfl
  · simp only [List.dropLast_concat] at hMO hsz ⊢
    have hpre : ∀ c, c < front.length → MO[c]? = M[c]? := by
      intro c hc
      exact Canonical.build_common_prefix (leftTail := []) (rightTail := [last])
        (by simpa using hMO) hM hc
    rw [hMO]
    congr 1
    apply Array.ext_getElem?
    intro i
    rw [Array.getElem?_pop]
    simp only [List.length_append, List.length_singleton] at hMs
    split
    · exact hpre i (by omega)
    · rw [Array.getElem?_eq_none (by omega)]

/-- **Reconstruction in the deletion case.** When the expansion only deletes the
last term, the canonical mountain of the output is the returned mountain. -/
theorem expand_build_eq_delete {s : List Nat} {n D : Nat} {M R : Mountain} {out : List Nat}
    (hM : Canonical.build s = .ok M) (hR : expandDiagram s n = .ok R)
    (hv : Expansion.valuesOf R = .ok out) (hcase : root? M D = none ∨ n = 0) :
    Canonical.build out = .ok R := by
  obtain ⟨M', hM', hcases⟩ := expandDiagram_cases hR
  obtain rfl := build_eq hM hM'
  have hV := Canonical.build_valid_of_success hM
  rcases hcases with ⟨rfl, rfl⟩ | ⟨_, col, t, hcol, ht, ⟨_, rfl⟩ | ⟨hτ, hn, root, hroot, hcr, _, _⟩⟩
  · have := valuesOf_length hv
    rw [Canonical.build_size hM] at this
    simp only [List.length_nil] at this
    rw [List.length_eq_zero_iff.mp this]
    exact hM
  · rw [valuesOf_pop hM hv]
    exact build_dropLast hM
  · exfalso
    obtain ⟨K, hK⟩ := root?_of_top hV D hcol ht hτ hroot hcr
    rcases hcase with h0 | h0
    · rw [hK] at h0; cases h0
    · exact hn h0

/-- **Reconstruction on the unchanged prefix.** The canonical mountain of `s[n]` and
the returned mountain agree on every column left of the last column `x₀` of `s`. -/
theorem expand_build_prefix {s : List Nat} {n : Nat} {R MO : Mountain} {out : List Nat}
    (hR : expandDiagram s n = .ok R) (hv : Expansion.valuesOf R = .ok out)
    (hMO : Canonical.build out = .ok MO) :
    ∀ c, c + 1 < s.length → MO[c]? = R[c]? := by
  intro c hc
  obtain ⟨M, hM, hcases⟩ := expandDiagram_cases hR
  have hMs := Canonical.build_size hM
  rcases hcases with ⟨rfl, rfl⟩ | ⟨_, col, t, hcol, ht, ⟨_, rfl⟩ | ⟨_, _, root, _, hcr, _, hgood⟩⟩
  · simp at hc
  · rw [valuesOf_pop hM hv] at hMO
    rw [build_eq (build_dropLast hM) hMO]
  · obtain ⟨_, hpre, _⟩ := hgood
    have hx : M.size - 1 = s.length - 1 := by omega
    have hvals : ∀ i, i < s.length - 1 → out[i]? = s[i]? := by
      intro i hi
      have hRi := hpre i (by omega)
      obtain ⟨coli, hci⟩ : ∃ coli, M[i]? = some coli :=
        ⟨M[i], Array.getElem?_eq_getElem (by omega)⟩
      rw [hci] at hRi
      obtain ⟨v, hvo, hb⟩ := bottomValue_at hv hRi
      have hs := congrArg (fun xs : List (Option Nat) => xs[i]?) (Canonical.build_bottom_values hM)
      simp only [Canonical.bottomValues, List.getElem?_map, Array.getElem?_toList, hci,
        Option.map_some, hb] at hs
      rw [hvo]
      cases hsi : s[i]? with
      | none => simp [hsi] at hs
      | some u => simp only [hsi, Option.map_some, Option.some.injEq] at hs; rw [hs]
    have htake : out.take (s.length - 1) = s.take (s.length - 1) := by
      apply List.ext_getElem?
      intro i
      simp only [List.getElem?_take]
      split
      · exact hvals i (by omega)
      · rfl
    have hleft : Canonical.build (s.take (s.length - 1) ++ out.drop (s.length - 1)) = .ok MO := by
      rw [← htake, List.take_append_drop]; exact hMO
    have hright : Canonical.build (s.take (s.length - 1) ++ s.drop (s.length - 1)) = .ok M := by
      rw [List.take_append_drop]; exact hM
    rw [Canonical.build_common_prefix hleft hright (by simp; omega), hpre c (by omega)]

/-- **Open.** The returned mountain of every successful official expansion is the
canonical mountain of its values (for the weak rule this is Phyrion's
`Expansion.expandDiagram_reconstruct`). It is checked on the 474 fixtures of
`Check.lean` (`canonicalAgree`), proved above in the deletion case
(`expand_build_eq_delete`) and on the columns left of `x₀` (`expand_build_prefix`),
and not proved in general. It is not needed for `classifiedB`. -/
def ReconstructionHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain) (out : List Nat),
    expandDiagram s n = .ok R → Expansion.valuesOf R = .ok out → Canonical.build out = .ok R

/-! ## `classifiedB` without items 1 and 3 -/

/-- The atom part (item 4) of `classifiedB`, for the input mountain `M`, the output
mountain `MO` and the number of copies `n`. It is the body of
`Reserve.classifiedWith atoms root?` without the degree and length checks. -/
def atomsClassified (M MO : Mountain) (n D : Nat) : Bool :=
  match root? M D with
  | none => (atoms MO D).all (baseOK D (atoms M D))
  | some ρ =>
    if n = 0 then (atoms MO D).all (baseOK D (atoms M D))
    else
      (atoms MO D).all fun e =>
        if e.child < ρ.x0 then baseOK D (atoms M D) e
        else
          reserveOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ((e.child - ρ.x0) / (ρ.x0 - ρ.cr)) (atoms M D) e ||
            seamOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ((e.child - ρ.x0) / (ρ.x0 - ρ.cr)) (atoms M D)
              ρ.control e

/-- **`classifiedB` without items 1 and 3.** For a nonempty `s` whose expansion
succeeds, the output mountain can be built, and `classifiedB` is the conjunction of
the two degree checks (item 2) and the atom classification (item 4). -/
theorem classifiedB_eq {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    (hs : s ≠ []) (hM : Canonical.build s = .ok M) (h : expand s n = .ok out) :
    ∃ MO, Canonical.build out = .ok MO ∧
      classifiedB s n D = (degreeAtMost M D && degreeAtMost MO D && atomsClassified M MO n D) := by
  obtain ⟨MO, hMO, _, _⟩ := expand_build_ok h
  refine ⟨MO, hMO, ?_⟩
  unfold classifiedB classifiedWith
  simp only [hM, h, hMO]
  cases hr : root? M D with
  | none =>
      have hl := expand_length_delete (D := D) hs hM h (Or.inl hr)
      simp [atomsClassified, hr, hl]
  | some ρ =>
      by_cases hn : n = 0
      · have hl := expand_length_delete (D := D) hs hM h (Or.inr hn)
        simp [atomsClassified, hr, hn, hl]
      · have hl := expand_length_splice hM h hr hn
        simp [atomsClassified, hr, hn, hl]

/-! ## The classification for nonempty sequences -/

/-- `Descent.ClassificationHolds` is false: the empty sequence expands to itself, and
`classifiedB [] n D` asks for `out.length + 1 = s.length`. -/
theorem not_classificationHolds : ¬ Descent.ClassificationHolds := by
  intro h
  have := h [] 0 0 (by
    intro M hM
    have h0 : Canonical.build ([] : List Nat) = .ok #[] := rfl
    rw [h0] at hM
    injection hM with e
    subst e
    decide)
  revert this
  decide

/-- The classification for nonempty sequences, the case the descent uses. -/
def ClassificationHoldsNE : Prop :=
  ∀ (s : List Nat) (n D : Nat), s ≠ [] → Descent.DegreeOK s D → classifiedB s n D = true

theorem acc_of_repNE (h : ClassificationHoldsNE) (D : Nat) (α : Descent.L) :
    ∀ s, Descent.DegreeOK s D → ∀ rep : Descent.Rep D s, (∀ i, rep.f i < α) →
      Acc Descent.Step s := by
  induction α using (wellFounded_lt (α := Descent.L)).induction with
  | _ α ih =>
    intro s hdeg rep hbound
    refine Acc.intro s ?_
    rintro t ⟨hs, n, hrun⟩
    have hcls := h s n D hs hdeg
    obtain ⟨new, hnew⟩ := Descent.descent hs hrun hcls rep
    exact ih _ (hbound _) t (Descent.degreeOK_of_classified hrun hcls) new hnew

/-- **Conditional well-foundedness, corrected.** If the splice classification holds
for every expansion of a nonempty sequence, the official expansion is
well-founded. -/
theorem wellFounded_of_classificationNE (h : ClassificationHoldsNE) :
    WellFounded Descent.Step := by
  refine ⟨fun s => ?_⟩
  obtain ⟨rep⟩ := Descent.rep_exists (dimOf s) s
  exact acc_of_repNE h (dimOf s) Reflection.OrdinalSupply.top s (Descent.degreeOK_dimOf s) rep
    rep.bounded

/-- Items 2 and 4 of `notes/04-official-design.md` §6: what remains of the
classification once items 1 and 3 are proved. -/
def DegreeAndAtomsHold : Prop :=
  ∀ (s : List Nat) (n D : Nat) (M MO : Mountain) (out : List Nat),
    s ≠ [] → Descent.DegreeOK s D → Canonical.build s = .ok M → expand s n = .ok out →
      Canonical.build out = .ok MO →
      degreeAtMost MO D = true ∧ atomsClassified M MO n D = true

/-- **Reduction.** Items 2 and 4 give the classification for nonempty sequences. -/
theorem classificationHoldsNE_of_parts (h : DegreeAndAtomsHold) : ClassificationHoldsNE := by
  intro s n D hs hdeg
  cases hb : Canonical.build s with
  | error e => simp [classifiedB, classifiedWith, hb]
  | ok M =>
      cases he : expand s n with
      | error e => simp [classifiedB, classifiedWith, hb, he]
      | ok out =>
          obtain ⟨MO, hMO, heq⟩ := classifiedB_eq (D := D) hs hb he
          obtain ⟨h2, h4⟩ := h s n D M MO out hs hdeg hb he hMO
          rw [heq, hdeg M hb, h2, h4]
          rfl

/-- Items 2 and 4 give the well-foundedness of the official expansion. -/
theorem wellFounded_of_parts (h : DegreeAndAtomsHold) : WellFounded Descent.Step :=
  wellFounded_of_classificationNE (classificationHoldsNE_of_parts h)

end OmegaY.Official.Reconstruction

#print axioms OmegaY.Official.Reconstruction.expand_length_delete
#print axioms OmegaY.Official.Reconstruction.expand_length_splice
#print axioms OmegaY.Official.Reconstruction.expand_legal
#print axioms OmegaY.Official.Reconstruction.expand_build_ok
#print axioms OmegaY.Official.Reconstruction.expand_build_eq_delete
#print axioms OmegaY.Official.Reconstruction.expand_build_prefix
#print axioms OmegaY.Official.Reconstruction.classifiedB_eq
#print axioms OmegaY.Official.Reconstruction.not_classificationHolds
#print axioms OmegaY.Official.Reconstruction.wellFounded_of_classificationNE
#print axioms OmegaY.Official.Reconstruction.wellFounded_of_parts
