/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Shape.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `len_le_one_iff` a hypothesis is beta-reduced before `omega`; in `highestAtMost_some` the `none` case ends with `lt_irrefl` and the `some` case uses `erw` (the `match` written in the proof is a different matcher from the one in `highestAtMost`); in `root?_of_official_ne_zero` one bound `pcol[1].row ≤ t.row` is proved by `exact hprow.le.trans (le_of_lt hlt)` instead of `rw [hprow]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Locality
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Values
import Googology.Notation.OmegaY.WellOrder.OmegaY.Canonical.Prefix

set_option backward.do.legacy false

/-!
# The shape of one official expansion

Structural facts about `Official.expandDiagram` and `Official.expand` that do not
depend on how a column is copied:

* `expandDiagram_spec`: the three branches of `expandDiagram` (empty input; deletion
  of the last entry when the top of the last column is on the bottom row or `n = 0`;
  the splice branch). In the splice branch the result agrees with the input mountain
  on the columns below `x₀` and has at least `x₀` columns.
* `values_prefix`, `agree_of_take`: hence the output sequence starts with
  `s₀, …, s_{x₀-1}`, and the canonical mountain of the output agrees with `M(s)`
  below `x₀`.
* `root?_none_of_official_zero`, `root?_of_official_ne_zero`: the root data
  `Reserve.root?` used by `classifiedB` is `none` exactly in the deletion branch
  with a bottom top node, and otherwise names the root column of the expansion.
-/

namespace OmegaY.Official.Classification
open Canonical Reserve

theorem forIn_except_inv {α β ε : Type} (P : β → Prop) (f : α → β → Except ε (ForInStep β))
    (hf : ∀ a b s, P b → f a b = .ok s → P (match s with | .done b => b | .yield b => b)) :
    ∀ (xs : List α) (b r : β), P b → forIn xs b f = .ok r → P r := by
  intro xs
  induction xs with
  | nil =>
      intro b r hb h
      simp only [List.forIn_nil] at h
      cases h
      exact hb
  | cons a as ih =>
      intro b r hb h
      simp only [List.forIn_cons] at h
      cases hfa : f a b with
      | error e => simp [hfa] at h; cases h
      | ok s =>
          have hs := hf a b s hb hfa
          rw [hfa] at h
          cases s with
          | done b' => simp only [bind, Except.bind] at h; cases h; exact hs
          | yield b' => simp only [bind, Except.bind] at h; exact ih b' r hs h


theorem AgreeBelow.push {M R : Mountain} {k : Nat} (h : AgreeBelow M R k) (hk : k ≤ R.size)
    (col : Column) : AgreeBelow M (R.push col) k := by
  intro c hc
  rw [h c hc, Array.getElem?_push]
  simp [show c ≠ R.size by omega]

theorem expandDiagram_spec {values : List Nat} {copies : Nat} {R : Mountain}
    (h : Official.expandDiagram values copies = .ok R) :
    ∃ M, build values = .ok M ∧
      ((values.isEmpty = true ∧ R = M) ∨
       ∃ col t, M[M.size - 1]? = some col ∧ col.back? = some t ∧
        (((Official.official t.row = 0 ∨ copies = 0) ∧ R = M.pop) ∨
         (¬ (Official.official t.row = 0 ∨ copies = 0) ∧ ∃ root, t.left = some root ∧
           root.column < M.size - 1 ∧ AgreeBelow M R (M.size - 1) ∧ M.size - 1 ≤ R.size))) := by
  unfold Official.expandDiagram at h
  cases hb : build values with
  | error e => simp [hb, Official.liftE, Except.mapError] at h; cases h
  | ok M =>
    simp only [hb, Official.liftE, Except.mapError, bind, Except.bind, pure, Except.pure] at h
    refine ⟨M, rfl, ?_⟩
    by_cases he : values.isEmpty = true
    · rw [if_pos he] at h
      exact Or.inl ⟨he, (Except.ok.inj h).symm⟩
    · rw [if_neg he] at h
      right
      cases hc : Expansion.columnAt M (M.size - 1) with
      | error err => simp only [hc] at h; cases h
      | ok col =>
        have hcol : M[M.size - 1]? = some col := by
          unfold Expansion.columnAt at hc
          split at hc
          · rename_i r hr; cases hc; exact hr
          · cases hc
        simp only [hc] at h
        cases ht : Expansion.top col with
        | error err => simp only [ht] at h; cases h
        | ok t =>
          have htb : col.back? = some t := by
            unfold Expansion.top at ht
            split at ht
            · rename_i r hr; cases ht; exact hr
            · cases ht
          simp only [ht] at h
          refine ⟨col, t, hcol, htb, ?_⟩
          by_cases hτ : Official.official t.row = 0 ∨ copies = 0
          · rw [if_pos hτ] at h
            exact Or.inl ⟨hτ, (Except.ok.inj h).symm⟩
          · rw [if_neg hτ] at h
            right
            refine ⟨hτ, ?_⟩
            cases hl : Expansion.leftOf t with
            | error err => simp only [hl] at h; cases h
            | ok root =>
              have htl : t.left = some root := by
                unfold Expansion.leftOf at hl
                split at hl
                · rename_i r hr; cases hl; exact hr
                · cases hl
              simp only [hl] at h
              by_cases hcr : root.column < M.size - 1
              · rw [if_neg (not_not.mpr hcr)] at h
                refine ⟨root, htl, hcr, ?_⟩
                split at h
                · cases h
                · rename_i v hv
                  cases h
                  refine forIn_except_inv
                    (P := fun R => AgreeBelow M R (M.size - 1) ∧ M.size - 1 ≤ R.size) _ ?_ _ _ _
                    ⟨?_, ?_⟩ hv
                  · intro i s st hP hst
                    split at hst
                    · cases hst
                    · rename_i v' hv'
                      cases hst
                      refine forIn_except_inv
                        (P := fun R => AgreeBelow M R (M.size - 1) ∧ M.size - 1 ≤ R.size) _ ?_ _ _ _
                        hP hv'
                      intro x s2 st2 hP2 hst2
                      split at hst2
                      · simp [throw, throwThe, MonadExceptOf.throw] at hst2
                      · split at hst2
                        · cases hst2
                        · rename_i c _
                          cases hst2
                          exact ⟨hP2.1.push hP2.2 c, by simp only [Array.size_push]; omega⟩
                  · intro c hc
                    simp [hc]
                  · simp
              · rw [if_pos hcr] at h
                simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Values -/

theorem mapM_except_spec {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ i (h1 : i < xs.length) (h2 : i < ys.length), f xs[i] = .ok ys[i] := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp only [List.mapM_nil, pure, Except.pure] at h
      cases h
      simp
  | cons a as ih =>
      intro ys h
      simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
      cases hfa : f a with
      | error e => simp [hfa] at h
      | ok b =>
          simp only [hfa] at h
          cases hrest : as.mapM f with
          | error e => simp [hrest] at h
          | ok bs =>
              simp only [hrest, Except.ok.injEq] at h
              subst h
              obtain ⟨hlen, hall⟩ := ih bs hrest
              refine ⟨by simp [hlen], ?_⟩
              intro i h1 h2
              cases i with
              | zero => simpa using hfa
              | succ i => simpa using hall i (by simpa using h1) (by simpa using h2)

theorem valuesOf_spec {A : Mountain} {vs : List Nat} (h : Expansion.valuesOf A = .ok vs) :
    vs.length = A.size ∧ ∀ (c : Nat) (col : Column), A[c]? = some col →
      ∃ cell : Cell, col[1]? = some cell ∧ vs[c]? = some cell.value := by
  unfold Expansion.valuesOf at h
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ h
  simp only [Array.length_toList] at hlen
  refine ⟨hlen, ?_⟩
  intro c col hc
  have hcA : c < A.size := by
    rcases Nat.lt_or_ge c A.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hc
  have hcol : A[c] = col := by
    rw [Array.getElem?_eq_getElem hcA] at hc; exact Option.some.inj hc
  have hf := hall c (by simpa using hcA) (by omega)
  simp only [Array.getElem_toList, hcol] at hf
  split at hf
  · rename_i b hb
    refine ⟨b, hb, ?_⟩
    rw [List.getElem?_eq_getElem (show c < vs.length by omega), Except.ok.inj hf]
  · cases hf

theorem expand_spec {s out : List Nat} {n : Nat} (h : Official.expand s n = .ok out) :
    ∃ R, Official.expandDiagram s n = .ok R ∧ Expansion.valuesOf R = .ok out := by
  unfold Official.expand at h
  simp only [bind, Except.bind] at h
  cases hR : Official.expandDiagram s n with
  | error e => simp [hR] at h
  | ok R =>
      simp only [hR, Official.liftE, Except.mapError] at h
      refine ⟨R, rfl, ?_⟩
      cases hv : Expansion.valuesOf R with
      | error e => simp [hv] at h
      | ok v => simp only [hv, Except.ok.injEq] at h; rw [h]

/-- The values of the output agree with the input on the columns that the output
mountain shares with the input mountain. -/
theorem values_prefix {s out : List Nat} {M R : Mountain} {k : Nat}
    (hM : build s = .ok M) (hA : AgreeBelow M R k) (hkM : k ≤ M.size)
    (hv : Expansion.valuesOf R = .ok out) : out.take k = s.take k := by
  obtain ⟨_, hvals⟩ := valuesOf_spec hv
  have hsz := build_size hM
  apply List.ext_getElem?
  intro c
  simp only [List.getElem?_take]
  by_cases hc : c < k
  · simp only [hc, if_true]
    have hcM : c < M.size := by omega
    have hMc : M[c]? = some M[c] := Array.getElem?_eq_getElem hcM
    have hRc : R[c]? = some M[c] := (hA c hc).symm.trans hMc
    obtain ⟨cell, hcell, hout⟩ := hvals c M[c] hRc
    rw [hout]
    have hsc : c < s.length := by omega
    obtain ⟨column, hcolumn, hbv⟩ := build_bottom_at hM (List.getElem?_eq_getElem hsc)
    rw [hMc] at hcolumn
    cases hcolumn
    simp only [bottomValue, hcell, Option.map_some, Option.some.injEq] at hbv
    rw [List.getElem?_eq_getElem hsc, hbv]
  · simp [hc]

/-- Mountains of two sequences with a common prefix of length `k` agree below `k`. -/
theorem agree_of_take {s t : List Nat} {M MO : Mountain} {k : Nat}
    (hM : build s = .ok M) (hMO : build t = .ok MO) (htake : t.take k = s.take k)
    (hks : k ≤ s.length) : AgreeBelow M MO k := by
  intro c hc
  have hs : build (s.take k ++ s.drop k) = .ok M := by rw [List.take_append_drop]; exact hM
  have ht : build (s.take k ++ t.drop k) = .ok MO := by
    rw [← htake, List.take_append_drop]; exact hMO
  exact build_common_prefix hs ht (by simp; omega)

/-! ## The official row of the top of the last column -/

theorem len_le_one_iff (r : Row) : Official.len r ≤ 1 ↔ ∀ i, 1 ≤ i → r.coeff i = 0 := by
  simp only [Official.len, Row.toList, List.length_map, List.length_range]
  constructor
  · intro h i hi
    by_contra hne
    have hmem : i ∈ r.coeffs.support := Finsupp.mem_support_iff.mpr hne
    have := Finset.le_sup (f := fun i => i + 1) hmem
    beta_reduce at this
    omega
  · intro h
    apply Finset.sup_le
    intro i hi
    have hne : r.coeffs i ≠ 0 := Finsupp.mem_support_iff.mp hi
    by_contra hlt
    exact hne (h i (by omega))

theorem official_one : Official.official (1 : Row) = 0 := by
  have hfin : Official.isFinite (1 : Row) = true := by
    simp only [Official.isFinite, decide_eq_true_eq, len_le_one_iff]
    intro i hi
    change Row.coeff ((1 : Nat) : Row) i = 0
    simp [Row.coeff_nat]; omega
  simp only [Official.official, hfin, if_true]
  apply Row.ext
  intro i
  have h1 : Row.coeff (1 : Row) 0 = 1 := by
    change Row.coeff ((1 : Nat) : Row) 0 = 1
    simp [Row.coeff_nat]
  rw [h1]
  simp [Row.coeff_nat]

theorem official_ne_zero_of_one_lt {r : Row} (h : (1 : Row) < r) : Official.official r ≠ 0 := by
  intro h0
  unfold Official.official at h0
  split at h0
  · rename_i hfin
    simp only [Official.isFinite, decide_eq_true_eq, len_le_one_iff] at hfin
    have hc0 := congrArg (fun a : Row => a.coeff 0) h0
    simp only [Row.coeff_nat, Row.coeff_zero, if_true] at hc0
    have hle : r ≤ (1 : Row) := by
      apply Row.le_of_coeff_le
      intro i
      change r.coeff i ≤ Row.coeff ((1 : Nat) : Row) i
      rw [Row.coeff_nat]
      split
      · subst i; omega
      · rw [hfin i (by omega)]
    exact absurd h (not_lt.mpr hle)
  · subst h0
    exact absurd h (not_lt.mpr (Row.zero_le 1))

/-! ## The root data -/

theorem column_of_getElem? {M : Mountain} {c : Nat} {col : Column} (h : M[c]? = some col) :
    ∃ hc : c < M.size, M[c] = col := by
  have hc : c < M.size := by
    rcases Nat.lt_or_ge c M.size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at h
  refine ⟨hc, ?_⟩
  rw [Array.getElem?_eq_getElem hc] at h
  exact Option.some.inj h

theorem back?_spec {col : Column} {t : Cell} (h : col.back? = some t) :
    0 < col.size ∧ col[col.size - 1]? = some t := by
  have hpos : 0 < col.size := by
    rcases Nat.eq_zero_or_pos col.size with h0 | h0
    · simp [Array.back?, h0] at h
    · exact h0
  exact ⟨hpos, by simpa [Array.back?] using h⟩

/-- The top node of the last column is the bottom node exactly when its official row
is `0`; then `root?` is `none`. -/
theorem root?_none_of_official_zero {M : Mountain} (hV : MountainValid M) (D : Nat)
    {col : Column} {t : Cell} (hcol : M[M.size - 1]? = some col) (ht : col.back? = some t)
    (h0 : Official.official t.row = 0) : root? M D = none := by
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcol
  have hCV := hV (M.size - 1) hc
  rw [hcolEq] at hCV
  obtain ⟨_, htop⟩ := back?_spec ht
  have hsmall : col.size - 1 ≤ 1 := by
    by_contra hbig
    have h2 := hCV.size_ge_two
    have hb1 : col[1]? = some col[1] := Array.getElem?_eq_getElem (by omega)
    have hrow1 := hCV.bottom_row col[1] hb1
    have hlt := hCV.rows_strict 1 (col.size - 1) col[1] t hb1 htop (by omega)
    rw [hrow1] at hlt
    exact official_ne_zero_of_one_lt hlt h0
  unfold root?
  rw [hcol]
  simp [hsmall]

theorem highestAtMost_some {M : Mountain} {l : Nat} {column : Column} {row : Row}
    (hcol : M[l]? = some column) (hsize : 2 ≤ column.size) (hrow : column[1].row ≤ row) :
    ∃ p, highestAtMost M l row = some p := by
  unfold highestAtMost
  rw [hcol]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases hlast : ((List.range column.size).filter fun j =>
      0 < j && (match column[j]? with | some c => decide (c.row ≤ row) | none => false)).getLast? with
  | none =>
      exfalso
      rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at hlast
      have := hlast 1 (List.mem_range.mpr (by omega))
      simp [Array.getElem?_eq_getElem (show 1 < column.size by omega), hrow] at this
      exact absurd (lt_of_lt_of_le this hrow) (lt_irrefl _)
  | some j => exact ⟨_, by erw [hlast]; rfl⟩

/-- In the splice branch the root data exists and matches the root of the expansion. -/
theorem root?_of_official_ne_zero {M : Mountain} (hV : MountainValid M) (D : Nat)
    {col : Column} {t : Cell} {root : Ref} (hcol : M[M.size - 1]? = some col)
    (ht : col.back? = some t) (h0 : Official.official t.row ≠ 0) (hl : t.left = some root) :
    ∃ ρ, root? M D = some ρ ∧ ρ.x0 = M.size - 1 ∧ ρ.cr = root.column := by
  obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcol
  have hCV := hV (M.size - 1) hc
  rw [hcolEq] at hCV
  obtain ⟨_, htop⟩ := back?_spec ht
  have h2 := hCV.size_ge_two
  have hb1 : col[1]? = some col[1] := Array.getElem?_eq_getElem (by omega)
  have hrow1 := hCV.bottom_row col[1] hb1
  have hbig : ¬ col.size - 1 ≤ 1 := by
    intro hsmall
    have hidx : col.size - 1 = 1 := by omega
    rw [hidx, hb1] at htop
    cases htop
    rw [hrow1] at h0
    exact h0 official_one
  have hlt := hCV.rows_strict 1 (col.size - 1) col[1] t hb1 htop (by omega)
  rw [hrow1] at hlt
  obtain ⟨_, parent, hparent, _⟩ := hCV.stored_valid (col.size - 1) t root htop hl
  obtain ⟨pcol, hpcol, _⟩ := cellAt_ok_iff.mp hparent
  obtain ⟨hpc, hpcolEq⟩ := column_of_getElem? hpcol
  have hPV := hV root.column hpc
  rw [hpcolEq] at hPV
  have hps : 1 < pcol.size := by have := hPV.size_ge_two; omega
  have hp1 : pcol[1]? = some pcol[1] := Array.getElem?_eq_getElem hps
  have hprow := hPV.bottom_row pcol[1] hp1
  obtain ⟨p, hp⟩ := highestAtMost_some (row := t.row) hpcol hPV.size_ge_two
    (by exact hprow.le.trans (le_of_lt hlt))
  have hcell : cell? M ⟨M.size - 1, col.size - 1⟩ = some t := by
    simp [cell?, hcol, htop]
  have hleg : legAtom? M D ⟨M.size - 1, col.size - 1⟩ =
      some ⟨root.column, M.size - 1, keyAt M D t.row p⟩ := by
    simp only [legAtom?, hcell, hl, Option.bind_eq_bind, Option.bind_some]
    rw [hp]
    rfl
  refine ⟨⟨M.size - 1, root.column, keyAt M D t.row p⟩, ?_, rfl, rfl⟩
  unfold root?
  rw [hcol]
  simp [hbig, htop, hl, hleg]

end OmegaY.Official.Classification
