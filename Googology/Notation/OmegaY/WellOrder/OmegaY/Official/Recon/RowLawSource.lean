/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawSource.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawRows

set_option backward.do.legacy false

/-!
# The source columns are chains of bump steps

In the canonical mountain `M(s)` the official rows of every column, bottom to top, form a
chain of bump steps starting at `0` (the row law of the canonical mountain,
`row u⁺ = B (row u) (row π(u⁺)) = bump (row u) _`). Hence a column cannot jump over a
row `β` that vanishes below `m` into `[β, U)` for a row `U` that agrees with `β` above `m`
(`node_of_between`).

Also here:

* `Top.rootCut_region`: for a region below the top row `τ`, the top of the root column in
  the region is not above the top of the last column in the region (notes/03 §2.4,
  `h_ρ ≤ h_κ`), from Phyrion's `Preparation.root_row_support` (`Top.root_rows`);
* `node_of_ascends`: if a column `x > c_r` ascends in a region (`ascends`), it has a node
  at the row of the top `ρ` of the root column in the region.
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical Expansion Dimension

/-- The official rows of column `c`, bottom to top. -/
def rowsOf (M : Mountain) (c : Nat) : List Row := (realNodes M c).map (fun p => official p.2.row)

theorem realNodes_eq_nil {M : Mountain} {c : Nat} (hc : ¬ c < M.size) : realNodes M c = [] := by
  unfold realNodes
  rw [Array.getElem?_eq_none (by omega)]

/-- The row law of the canonical mountain, in official rows. -/
theorem rowsOf_chain {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) (c : Nat) :
    (rowsOf M c).IsChain BumpStep := by
  by_cases hc : c < M.size
  · have hcert := certified_of_build hb
    have hG := hcert.geometry c hc
    have hCV := hcert.valid c hc
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi0 : i < (rowsOf M c).length := by omega
    have g : ∀ j, (rowsOf M c)[j]? = (M[c][j + 1]?).map (fun cell => official cell.row) := by
      intro j
      rw [rowsOf, List.getElem?_map, realNodes_getElem?, Array.getElem?_eq_getElem hc,
        Option.bind_some]
      cases M[c][j + 1]? <;> rfl
    have g1 := g i
    have g2 := g (i + 1)
    rw [List.getElem?_eq_getElem hi0] at g1
    rw [List.getElem?_eq_getElem hi] at g2
    cases hl : M[c][i + 1]? with
    | none => rw [hl] at g1; cases g1
    | some lower =>
      cases hu : M[c][i + 1 + 1]? with
      | none => rw [hu] at g2; cases g2
      | some upper =>
        rw [hl] at g1
        rw [hu] at g2
        simp only [Option.map_some, Option.some.injEq] at g1 g2
        rw [g1, g2]
        obtain ⟨ref, parent, _, _, _, hrow⟩ := hG (i + 1) lower upper hl hu (by omega)
        have hlow : (1 : Row) ≤ lower.row :=
          row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 (i + 1) phantom lower hCV.phantom hl
            (by omega)))
        refine ⟨Row.jump lower.row parent.row, ?_⟩
        rw [hrow, Row.B, official_bump hlow]
  · rw [rowsOf, realNodes_eq_nil hc]
    exact List.IsChain.nil

theorem rowsOf_head {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c : Nat}
    (hc : c < M.size) : ∃ l, rowsOf M c = 0 :: l := by
  obtain ⟨b, _, hrow, _, hhead⟩ := bottom_node hb hc
  unfold rowsOf
  cases h : realNodes M c with
  | nil => rw [h] at hhead; cases hhead
  | cons a rest =>
    rw [h] at hhead
    obtain rfl := Option.some.inj hhead
    exact ⟨rest.map (fun p => official p.2.row), by simp [hrow, official_one]⟩

/-- **A column does not jump over `β`.** In a canonical mountain, if column `c` has a node in
`[β, U)` where `β` vanishes below `m` and `U` agrees with `β` above `m`, then column `c` has
a node at `β`. -/
theorem node_of_between {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {c : Nat} {β U : Row} {m : Nat} (hz : ZeroBelow m β)
    (hU : ∀ q, m < q → U.coeff q = β.coeff q) {p : Ref × Cell} (hp : p ∈ realNodes M c)
    (h1 : β ≤ official p.2.row) (h2 : official p.2.row < U) :
    ∃ p' ∈ realNodes M c, official p'.2.row = β := by
  have hc : c < M.size := by
    by_contra hn
    rw [realNodes_eq_nil hn] at hp
    cases hp
  obtain ⟨l, hl⟩ := rowsOf_head hb hc
  have hch := rowsOf_chain hb c
  rw [hl] at hch
  have hmem : official p.2.row ∈ 0 :: l := by
    rw [← hl]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have := mem_of_chain hz hU 0 l hch (Row.zero_le β) ⟨_, hmem, h1, h2⟩
  rw [← hl] at this
  obtain ⟨p', hp', he⟩ := List.mem_map.mp this
  exact ⟨p', hp', he⟩

/-! ## `nodeAt` and `topIn` -/

theorem nodeAt_spec {M : Mountain} {c : Nat} {ρ : Row} {p : Ref × Cell}
    (h : nodeAt M c ρ = some p) : p ∈ realNodes M c ∧ official p.2.row = ρ := by
  unfold nodeAt at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem nodeAt_of_mem {M : Mountain} {c : Nat} {p : Ref × Cell} (hp : p ∈ realNodes M c) :
    ∃ p', nodeAt M c (official p.2.row) = some p' := by
  unfold nodeAt
  cases h : (realNodes M c).find? (fun q => official q.2.row == official p.2.row) with
  | some p' => exact ⟨p', rfl⟩
  | none =>
    have := List.find?_eq_none.mp h p hp
    simp at this

theorem nodeAt_none {M : Mountain} {c : Nat} {ρ : Row} (h : nodeAt M c ρ = none) :
    ∀ p ∈ realNodes M c, official p.2.row ≠ ρ := by
  intro p hp he
  obtain ⟨p', hp'⟩ := nodeAt_of_mem hp
  rw [he, h] at hp'
  cases hp'

theorem topIn_none {M : Mountain} {c d : Nat} {b : Row} (h : topIn M c d b = none) :
    ∀ p ∈ realNodes M c, inRegion d b (official p.2.row) = false := by
  intro p hp
  by_contra hn
  have hP : inRegion d b (official p.2.row) = true := by simpa using hn
  obtain ⟨q, hq⟩ := filter_last_exists (P := fun p => inRegion d b (official p.2.row)) hp hP
  unfold topIn at h
  rw [hq] at h
  cases h

theorem topIn_spec {M : Mountain} {c d : Nat} {b : Row} {a : Ref × Cell}
    (h : topIn M c d b = some a) :
    a ∈ realNodes M c ∧ inRegion d b (official a.2.row) = true ∧
      ∀ q ∈ realNodes M c, inRegion d b (official q.2.row) = true → q.1.index ≤ a.1.index := by
  unfold topIn at h
  exact filter_last_max h

theorem realNodes_column {M : Mountain} {c : Nat} {p : Ref × Cell} (hp : p ∈ realNodes M c) :
    p.1.column = c ∧ 1 ≤ p.1.index := by
  obtain ⟨_, k, _, _, hp1⟩ := mem_realNodes_iff.mp hp
  rw [hp1]
  exact ⟨rfl, by simp⟩

/-- The official row of the top of a region is the largest official row of the column in
the region. -/
theorem topIn_row_max {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {c d : Nat} {b : Row} {a : Ref × Cell} (h : topIn M c d b = some a) {q : Ref × Cell}
    (hq : q ∈ realNodes M c) (hin : inRegion d b (official q.2.row) = true) :
    official q.2.row ≤ official a.2.row := by
  have hV := build_valid_of_success hb
  obtain ⟨ha, _, hmax⟩ := topIn_spec h
  exact official_mono (realNodes_row_one_le hV hq) (realNodes_row_le hV hq ha (hmax q hq hin))

/-! ## The root column and the last column in a region -/

/-- **Root cut in a region.** For a region all of whose rows are below the top row `τ`, the
top of the root column in the region is not above the top of the last column. -/
theorem Top.rootCut_region {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {d : Nat} {S : Row}
    (hbelow : ∀ r, inRegion d S r = true → r < official t.row)
    {ρ : Ref × Cell} (hρ : topIn M root.column d S = some ρ) :
    ∃ κ, topIn M (M.size - 1) d S = some κ ∧ official ρ.2.row ≤ official κ.2.row := by
  have hV := build_valid_of_success h.build
  obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ
  have hρlt : ρ.2.row < t.row := row_lt_of_official h.row_one_le (hbelow _ hρin)
  obtain ⟨v, hvmem, hvrow⟩ := h.root_rows hρmem hρlt
  have hvin : inRegion d S (official v.2.row) = true := by rw [hvrow]; exact hρin
  obtain ⟨κ, hκ⟩ := filter_last_exists (P := fun p => inRegion d S (official p.2.row)) hvmem hvin
  refine ⟨κ, hκ, ?_⟩
  rw [← hvrow]
  exact topIn_row_max h.build hκ hvmem hvin

/-! ## Ascending columns -/

theorem weakParent_some {M : Mountain} {a q : Ref}
    (h : Expansion.weakParent M a = .ok (some q)) :
    ∃ col cell upper parentCell, M[a.column]? = some col ∧ col[a.index]? = some cell ∧
      col[a.index + 1]? = some upper ∧ upper.left = some q ∧
      cellAt M q = .ok parentCell ∧ parentCell.row = cell.row := by
  unfold Expansion.weakParent at h
  simp only [bind, Except.bind] at h
  cases hcol : Expansion.columnAt M a.column with
  | error e => rw [hcol] at h; cases h
  | ok col =>
    rw [hcol] at h
    simp only at h
    cases hcell : Expansion.lookup M a with
    | error e => rw [hcell] at h; cases h
    | ok cell =>
      rw [hcell] at h
      simp only at h
      cases hup : col[a.index + 1]? with
      | none => rw [hup] at h; cases h
      | some upper =>
        rw [hup] at h
        simp only at h
        cases hleft : Expansion.leftOf upper with
        | error e => rw [hleft] at h; cases h
        | ok parent =>
          rw [hleft] at h
          simp only at h
          split at h
          · cases h
          · cases hpc : Expansion.lookup M parent with
            | error e => rw [hpc] at h; cases h
            | ok parentCell =>
              rw [hpc] at h
              simp only at h
              split at h
              · cases h
              · rename_i hne
                simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
                subst h
                have hcol' : M[a.column]? = some col := by
                  unfold Expansion.columnAt at hcol
                  split at hcol
                  · rename_i c hc
                    cases hcol
                    exact hc
                  · cases hcol
                obtain ⟨col', hcol'', hcell'⟩ := lookup_ok_iff.mp hcell
                have : col' = col := Option.some.inj (hcol''.symm.trans hcol')
                subst this
                refine ⟨col', cell, upper, parentCell, hcol', hcell', hup, ?_, cellAt_ok_iff.mpr (lookup_ok_iff.mp hpc),
                  not_not.mp hne⟩
                unfold Expansion.leftOf at hleft
                split at hleft
                · rename_i r hr
                  cases hleft
                  exact hr
                · cases hleft

theorem referenceRow_bump {ρ : Row} (h : 0 < ρ.coeff 0) : Row.bump (referenceRow ρ) 0 = ρ := by
  have href : ∀ k, (referenceRow ρ).coeff k = if k = 0 then ρ.coeff 0 - 1 else ρ.coeff k := by
    intro k
    unfold referenceRow
    rw [if_pos h, Row.coeff_ofList]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have hlen : 0 < ρ.toList.length := by
        by_contra hn
        have : len ρ = 0 := by unfold len; omega
        have := coeff_of_le_len (a := ρ) (k := 0) (by omega)
        omega
      simp [hlen]
    · rw [if_neg (by omega), List.getElem?_set_ne (by omega)]
      by_cases hk' : k < ρ.toList.length
      · rw [List.getElem?_eq_getElem hk']
        simp only [Option.getD_some]
        simp [Row.toList]
      · rw [List.getElem?_eq_none (by omega)]
        simp only [Option.getD_none]
        exact (coeff_of_le_len (by unfold len; omega)).symm
  apply row_ext
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [bump_coeff_at, href, if_pos rfl]
    omega
  · rw [bump_coeff_high hk, href, if_neg (by omega)]

/-- **An ascending column has a node at the row of the root top.** -/
theorem node_of_ascends {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {rho : Option (Ref × Cell)}
    (h : ascends ctx rho = .ok true) :
    ∃ ρ, rho = some ρ ∧ ∃ p ∈ realNodes ctx.source ctx.x, official p.2.row = official ρ.2.row := by
  have hb := hctx.top.build
  have hcert := certified_of_build hb
  unfold ascends at h
  cases rho with
  | none => cases h
  | some ρ =>
    obtain ⟨ρRef, rc⟩ := ρ
    refine ⟨_, rfl, ?_⟩
    simp only at h
    cases hn : nodeAt ctx.source ctx.x (referenceRow (official rc.row)) with
    | none => rw [hn] at h; cases h
    | some p =>
      obtain ⟨ref, cell⟩ := p
      rw [hn] at h
      simp only at h
      obtain ⟨hmem, hrow⟩ := nodeAt_spec hn
      by_cases h0 : 0 < (official rc.row).coeff 0
      · -- one step of the in-row parent
        obtain ⟨hcolx, hidx⟩ := realNodes_column hmem
        simp only at hcolx hidx
        unfold reachesRoot at h
        rw [if_neg (by rw [hcolx]; have := hctx.xgt; omega)] at h
        simp only [bind, Except.bind] at h
        cases hw : liftE (Expansion.weakParent ctx.source ref) with
        | error e => rw [hw] at h; cases h
        | ok wp =>
          rw [hw] at h
          cases wp with
          | none => simp only at h; cases h
          | some q =>
            have hw' := Reconstruction.liftE_ok hw
            obtain ⟨col, cell', upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
              weakParent_some hw'
            obtain ⟨col0, k, hc0, hck, hp1⟩ := mem_realNodes_iff.mp hmem
            simp only at hp1
            rw [hp1] at hcol hcell hup
            simp only at hcol hcell hup
            have hcc : col0 = col := Option.some.inj (hc0.symm.trans hcol)
            subst hcc
            have hce : cell' = cell := Option.some.inj (hcell.symm.trans hck)
            subst hce
            have hxs : ctx.x < ctx.source.size := (Array.getElem?_eq_some_iff.mp hc0).1
            have hcolEq : ctx.source[ctx.x] = col0 := (Array.getElem?_eq_some_iff.mp hc0).2
            have hG := hcert.geometry ctx.x hxs
            rw [hcolEq] at hG
            obtain ⟨ref2, parent2, hleft2, hcell2, _, hrow2⟩ := hG (k + 1) cell' upper hck hup
              (by omega)
            have href2 : ref2 = q := Option.some.inj (hleft2.symm.trans hleft)
            subst href2
            have hpe : parent2 = parentCell := by
              have := hcell2.symm.trans hpc
              cases this
              rfl
            subst hpe
            rw [hprow] at hrow2
            have hCV := hcert.valid ctx.x hxs
            rw [hcolEq] at hCV
            have hlow : (1 : Row) ≤ cell'.row :=
              row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 (k + 1) phantom cell' hCV.phantom
                hck (by omega)))
            have hupmem : ((⟨ctx.x, k + 1 + 1⟩ : Ref), upper) ∈ realNodes ctx.source ctx.x :=
              mem_realNodes_iff.mpr ⟨col0, k + 1, hc0, hup, rfl⟩
            refine ⟨_, hupmem, ?_⟩
            simp only
            rw [hrow2, Row.B_self, official_bump hlow 0]
            simp only at hrow
            rw [hrow]
            exact referenceRow_bump h0
      · have hr : referenceRow (official rc.row) = official rc.row := by
          unfold referenceRow
          rw [if_neg h0]
        rw [hr] at hrow
        exact ⟨_, hmem, hrow⟩

end OmegaY.Official.Recon.RowLaw
