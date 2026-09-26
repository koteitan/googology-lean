/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainBlock0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `block0_lower` and `block0_cells` the bound `1 ≤ colM[1].row` is closed by `exact hb1.ge` instead of `rw [hb1]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossKinds
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainNormal
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowUpper
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyBlockZero
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainsCanonParent

set_option backward.do.legacy false

/-!
# The cross case of `Lex` in block `0`

Block `0` of a splice run makes one column, `X = x₀`, of the output `R`. Its lower part (the
emits of the first items, rows below `τ`) is the identity copy of the column `x₀` of `M(s)`
below `τ` (`lower_id`, `emitsT_block0`), and the columns left of `x₀` are those of `M(s)`.
This file shows

* `block0_lower`: the `k`-th lower emit has the origin `(x₀, k + 1)`, and the lower part has
  exactly `|M(s)[x₀]| - 2` emits (every node of `x₀` but the phantom and the top `t`);
* `block0_cells`: the cells `R[x₀][k]` and `M(s)[x₀][k]` have the same row and the same
  stored left end for `1 ≤ k ≤ |M(s)[x₀]| - 2`; the next cell of `R[x₀]` (the first node of
  the upper part, a copy of a node of the root column `c_r`) has its left end left of `c_r`,
  while the top `t` of `M(s)[x₀]` has its left end in `c_r`.

With it, the nodes of the lower part of `R[x₀]` and of the columns left of `x₀` correspond
to nodes of `M(s)` with the same cells up to values, so stored parents, candidates `Q`,
chains of stored parents and rows are the same (`Corr`). The comparison `Lex` of `M(s)`
transfers to `R` (`B0.lex`): the only place where the two columns `x₀` differ is
above the top of the lower part, where `M(s)` continues with `t` (left end in `c_r`) and
`R` with a node whose left end is left of `c_r`, so an equal-parent step of `M(s)` at `t`
becomes a `left` step (or a `top` step) of `R`.

`crossLex_block0`: the conclusion of `CrossLexHolds` holds for every node `u` of the column
`x₀` of the output whose upper node `u⁺` is not a copy of the upper part (the kinds plain,
clean and cut), from the statement in the normal frame of `M(s)` (`normal_chain_exists`,
`normal_crossLex` in `CrossPlainNormal.lean`).

## What remains open

`CrossLexPos K` is `CrossLexFor K` restricted to the columns `X > x₀` (blocks `i ≥ 1`), and
`crossLexFor_plain_of_pos : CrossLexPos IsPlain → CrossLexFor IsPlain`,
`crossLexFor_clean_of_pos : CrossLexPos IsClean → CrossLexFor IsClean`.

In blocks `i ≥ 1` the copy is not the identity. `reference/official/cross-plain-pos.cjs`
shows that the comparison `Lex` of the output passes through gap copies (`b = 1`) and the
upper part, and its outcome (`top` / `left`) differs from that of `M(s)` for some nodes; for
about 30% of the plain nodes `u` is a gap copy, and then `q`, `p` and the chain are gap copies
as well. So no node-by-node transfer like `B0` works there; it needs the profile of the
copies of a block.

## Numerical check

`reference/official/cross-plain-pos.cjs` (`n = 1, 2, 3`), no failure:

| sample | block 0 plain / clean | `CrossLexPos` plain / clean |
|---|---:|---:|
| standard S1–S3, S6 | 6534 / 552 | 18762 / 1050 |
| legal, length ≤ 6, entries ≤ 6 | 4995 / 555 | 15657 / 813 |
| legal, length ≤ 5, entries ≤ 8 | 3693 / 420 | 11343 / 570 |
| random legal (`--random 20000,10,10,7`) | 11670 / 2055 | 49506 / 4065 |

It also checks the facts behind `B0` on every expansion (the lower part of `R[x₀]` equals
`M(s)[x₀]` below its top, with the same stored left ends) and, at every block-0 cross node,
that `M(s)` is in the cross case with the same `p` and `q`.
-/

namespace OmegaY.Official.Recon.CrossPlain

open Canonical Expansion Geometry Frame Classification

/-! ## The emitted list of a column -/

theorem emitsT_parts {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∃ lo us, lowerT ctx τ = .ok lo ∧ upperT ctx τ = .ok us ∧ es = lo ++ us := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lo hlo
    split at h
    · cases h
    · rename_i us hus
      cases h
      exact ⟨lo, us, hlo, hus, rfl⟩

theorem levelOneT_notUpper {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, p.2.isUpper = false := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              cases hlc : leftColumn cs with
              | error e => rw [hlc] at h; cases h
              | ok v =>
                  rw [hlc] at h
                  cases h
                  intro p hp
                  simp only [List.mem_singleton] at hp
                  subst hp
                  rfl
      | none =>
          simp only [hC] at h
          by_cases h0 : it.source = 0
          · rw [if_pos h0] at h
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            rfl
          · rw [if_neg h0] at h
            simp only [bind, Except.bind, pure, Except.pure] at h
            cases hlc : leftColumn src with
            | error e => rw [hlc] at h; cases h
            | ok v =>
                rw [hlc] at h
                cases h
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                rfl

theorem runItemT_notUpper (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx d it = .ok ps →
      ∀ p ∈ ps, p.2.isUpper = false
  | 0, _, ps, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, h => levelOneT_notUpper (by simpa [runItemT] using h)
  | d + 2, it, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children _
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, _, hc⟩ := mem_of_mapM houts hout
          exact runItemT_notUpper ctx (d + 1) c out hc p hpo

theorem lowerT_notUpper {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) : ∀ p ∈ lo, p.2.isUpper = false := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    intro p hp
    obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
    obtain ⟨q, _, hq⟩ := mem_of_mapM houts hout
    exact runItemT_notUpper ctx q.1 q.2 out hq p hpo

theorem upperT_isUpper {ctx : Context} {τ : Row} {us : List (Emit × Origin)}
    (h : upperT ctx τ = .ok us) : ∀ p ∈ us, p.2.isUpper = true := by
  unfold upperT at h
  intro p hp
  obtain ⟨q, _, hqp⟩ := mem_of_mapM h hp
  simp only [bind, Except.bind, pure, Except.pure] at hqp
  split at hqp
  · cases hqp
  · cases hqp
    rfl

/-- The traced lower part is a run of the lower part. -/
theorem lowerT_lowerRun {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∃ vs, JumpLaw.LowerRun ctx τ vs ∧ vs.flatten = lo.map Prod.fst := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    have hm := mapM_map_fst (fun x : Nat × Item => runItem ctx x.1 x.2)
      (fun p => runItemT ctx p.1 p.2) (List.map Prod.fst) (fun p => runItemT_fst ctx p.1 p.2)
      (lowerItems τ)
    rw [houts] at hm
    refine ⟨outs.map (List.map Prod.fst), hm.symm, ?_⟩
    rw [List.map_flatten]

/-! ## The lower part of block `0` -/

/-- A strictly increasing map from `[0, a)` onto `[1, b]` is `i ↦ i + 1`, and `a = b`. -/
theorem strictMono_cover {a b : Nat} (f : Nat → Nat)
    (hmono : ∀ i j, i < j → j < a → f i < f j)
    (hrange : ∀ i, i < a → 1 ≤ f i ∧ f i ≤ b)
    (hcov : ∀ m, 1 ≤ m → m ≤ b → ∃ i, i < a ∧ f i = m) :
    a = b ∧ ∀ i, i < a → f i = i + 1 := by
  have hge : ∀ i, i < a → i + 1 ≤ f i := by
    intro i
    induction i with
    | zero => intro h; exact (hrange 0 h).1
    | succ i ih =>
      intro h
      have h1 := ih (by omega)
      have h2 := hmono i (i + 1) (by omega) h
      omega
  have hle : ∀ i, i < a → f i ≤ i + 1 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_contra hgt
      obtain ⟨k, hk, hfk⟩ := hcov (i + 1) (by omega) (by have := (hrange i hi).2; omega)
      rcases Nat.lt_trichotomy k i with hki | rfl | hki
      · have h1 := ih k hki hk
        have h2 := hge k hk
        omega
      · omega
      · have := hmono i k hki hk
        omega
  have hf : ∀ i, i < a → f i = i + 1 := fun i hi => le_antisymm (hle i hi) (hge i hi)
  refine ⟨le_antisymm ?_ ?_, hf⟩
  · rcases Nat.eq_zero_or_pos a with h | h
    · omega
    · have h1 := hf (a - 1) (by omega)
      have h2 := (hrange (a - 1) (by omega)).2
      omega
  · rcases Nat.eq_zero_or_pos b with h | h
    · omega
    · obtain ⟨k, hk, hfk⟩ := hcov b h le_rfl
      have := hf k hk
      omega

theorem row_lt_of_official_lt {a b : Row} (hb : (1 : Row) ≤ b) (h : official a < official b) :
    a < b := by
  by_contra hn
  have := official_mono hb (not_lt.mp hn)
  exact absurd h (not_lt.mpr this)

theorem row_eq_of_official_eq {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b)
    (h : official a = official b) : a = b := by
  rw [← stored_official ha, ← stored_official hb, h]

/-- **The lower part of block `0`.** The `k`-th emit is a lower emit exactly when
`k < |M(s)[x₀]| - 2`, and then its origin is the node `(x₀, k + 1)`, at the row of that
node. -/
theorem block0_lower {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (h0 : ctx.block = 0) (hx : ctx.x = ctx.source.size - 1)
    {es : List (Emit × Origin)} (hes : emitsT ctx (official t.row) = .ok es)
    (hsort : ((es.map Prod.fst).map Emit.row).Pairwise (· < ·))
    {colM : Column} (hcolM : ctx.source[ctx.x]? = some colM) :
    colM.size - 2 ≤ es.length ∧
    (∀ k (hk : k < es.length), es[k].2.isUpper = false ↔ k < colM.size - 2) ∧
    ∀ k (hk : k < es.length), k < colM.size - 2 →
      es[k].2.src = ⟨ctx.x, k + 1⟩ ∧ ∃ cv, colM[k + 1]? = some cv ∧ official cv.row = es[k].1.row := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := emitsT_parts hes
  have hb := hctx.top.build
  have hV := Canonical.build_valid_of_success hb
  obtain ⟨hxM, hcolEq⟩ := column_of_getElem? hcolM
  have hCV : ColumnValid ctx.source ctx.x colM := by rw [← hcolEq]; exact hV ctx.x hxM
  -- the top of the column `x₀`
  have htop := hctx.top.top
  rw [← hx, hcolM] at htop
  replace htop : colM.back? = some t := by simpa using htop
  have hsz : 0 < colM.size := by
    rcases Nat.eq_zero_or_pos colM.size with h | h
    · rw [Array.back?_eq_getElem?, show colM.size - 1 = 0 by omega,
        Array.getElem?_eq_none (by omega)] at htop
      cases htop
    · exact h
  have htop' : colM[colM.size - 1]? = some t := by rw [← Array.back?_eq_getElem?]; exact htop
  have hle1 : ∀ m (hm : m < colM.size), 1 ≤ m → (1 : Row) ≤ colM[m].row := by
    intro m hm h1
    have hs2 := hCV.size_ge_two
    have hb1 := hCV.bottom_row colM[1] (Array.getElem?_eq_getElem (by omega))
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact hb1.ge
    · have := hCV.rows_strict 1 m colM[1] colM[m] (Array.getElem?_eq_getElem (by omega))
        (Array.getElem?_eq_getElem hm) h
      rw [hb1] at this
      exact this.le
  -- the facts on the lower emits
  have hmemlo : ∀ k (hk : k < lo.length), lo[k] ∈ lo ++ us :=
    fun k hk => List.mem_append_left _ (List.getElem_mem hk)
  have hnu : ∀ k (hk : k < lo.length), lo[k].2.isUpper = false :=
    fun k hk => lowerT_notUpper hlo _ (List.getElem_mem hk)
  have hgood : ∀ k (hk : k < lo.length), Good ctx lo[k] :=
    fun k hk => emitsT_good hes _ (hmemlo k hk)
  have hrowok : ∀ k (hk : k < lo.length), Proofs.RowOK ctx lo[k] :=
    fun k hk => Proofs.emitsT_block0 h0 hes _ (hmemlo k hk) (hnu k hk)
  obtain ⟨vs, hvs, hvsf⟩ := lowerT_lowerRun hlo
  obtain ⟨hE1, hE2⟩ := JumpLaw.lower_id hctx h0 hvs
  rw [hvsf] at hE1 hE2
  -- the origin of a lower emit
  have horig : ∀ k (hk : k < lo.length), lo[k].2.src.column = ctx.x ∧
      1 ≤ lo[k].2.src.index ∧ ∃ (hi : lo[k].2.src.index < colM.size),
        official colM[lo[k].2.src.index].row = lo[k].1.row ∧
        lo[k].1.row < official t.row := by
    intro k hk
    obtain ⟨hc, hi, _⟩ := hgood k hk
    rw [hnu k hk] at hc
    simp only [Bool.false_eq_true, if_false] at hc
    obtain ⟨cv, hcv, hrow⟩ := hrowok k hk
    obtain ⟨colv, hcolv, hcv⟩ := cell?_spec hcv
    rw [hc, hcolM] at hcolv
    obtain rfl := Option.some.inj hcolv
    obtain ⟨hlt, hcvEq⟩ := Array.getElem?_eq_some_iff.mp hcv
    obtain ⟨_, _, _, hτ, _⟩ := hE1 lo[k].1 (List.mem_map_of_mem (List.getElem_mem hk))
    exact ⟨hc, hi, hlt, by rw [hcvEq, hrow], hτ⟩
  let f : Nat → Nat := fun k => if h : k < lo.length then lo[k].2.src.index else 0
  have hfk : ∀ k (hk : k < lo.length), f k = lo[k].2.src.index := fun k hk => dif_pos hk
  have htrow : official t.row = official colM[colM.size - 1].row := by
    rw [(Array.getElem?_eq_some_iff.mp htop').2]
  have hrange : ∀ k, k < lo.length → 1 ≤ f k ∧ f k ≤ colM.size - 2 := by
    intro k hk
    rw [hfk k hk]
    obtain ⟨_, hi, hlt, hrow, hτ⟩ := horig k hk
    refine ⟨hi, ?_⟩
    by_contra hn
    have he : lo[k].2.src.index = colM.size - 1 := by omega
    rw [← hrow, htrow] at hτ
    simp only [he] at hτ
    exact lt_irrefl _ hτ
  have hmono : ∀ i j, i < j → j < lo.length → f i < f j := by
    intro i j hij hj
    have hi : i < lo.length := by omega
    rw [hfk i hi, hfk j hj]
    obtain ⟨_, hi1, hilt, hirow, _⟩ := horig i hi
    obtain ⟨_, hj1, hjlt, hjrow, _⟩ := horig j hj
    have hlt : lo[i].1.row < lo[j].1.row := by
      have hs2 : (lo.map (fun p => p.1.row)).Pairwise (· < ·) := by
        have h' := hsort
        simp only [List.map_append, List.map_map, List.pairwise_append] at h'
        exact h'.1
      have hp := List.pairwise_iff_getElem.mp hs2 i j (by simp; omega) (by simp; omega) hij
      simpa using hp
    rw [← hirow, ← hjrow] at hlt
    have hrl := row_lt_of_official_lt (hle1 _ hjlt hj1) hlt
    by_contra hn
    rcases Nat.eq_or_lt_of_le (not_lt.mp hn) with he | he
    · simp only [he] at hrl
      exact lt_irrefl _ hrl
    · have := hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem hjlt)
        (Array.getElem?_eq_getElem hilt) he
      exact lt_asymm hrl this
  have hcov : ∀ m, 1 ≤ m → m ≤ colM.size - 2 → ∃ k, k < lo.length ∧ f k = m := by
    intro m hm1 hm2
    have hmlt : m < colM.size := by omega
    have hmem : ((⟨ctx.x, m⟩ : Ref), colM[m]) ∈ realNodes ctx.source ctx.x :=
      mem_realNodes_iff.mpr ⟨colM, m - 1, hcolM, by
        rw [show m - 1 + 1 = m by omega]; exact Array.getElem?_eq_getElem hmlt,
        by simp only; congr 1; omega⟩
    have hrowlt : colM[m].row < colM[colM.size - 1].row :=
      hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem hmlt)
        (Array.getElem?_eq_getElem (by omega)) (by omega)
    have hτ : official colM[m].row < official t.row := by
      rw [htrow]
      exact official_strictMono (hle1 m hmlt hm1) hrowlt
    obtain ⟨em, hem, hemrow⟩ := hE2 _ hmem hτ
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hem
    obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hk
    refine ⟨k, hk', ?_⟩
    rw [hfk k hk']
    obtain ⟨_, hi1, hilt, hirow, _⟩ := horig k hk'
    have heq : colM[lo[k].2.src.index].row = colM[m].row :=
      row_eq_of_official_eq (hle1 _ hilt hi1) (hle1 m hmlt hm1) (by rw [hirow, hemrow])
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem hilt)
        (Array.getElem?_eq_getElem hmlt) h
      rw [heq] at this
      exact lt_irrefl _ this
    · have := hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem hmlt)
        (Array.getElem?_eq_getElem hilt) h
      rw [heq] at this
      exact lt_irrefl _ this
  obtain ⟨hlen, hfv⟩ := strictMono_cover f hmono hrange hcov
  refine ⟨by simp; omega, ?_, ?_⟩
  · intro k hk
    by_cases hkl : k < lo.length
    · simp only [List.getElem_append_left hkl]
      exact ⟨fun _ => by omega, fun _ => hnu k hkl⟩
    · simp only [List.getElem_append_right (by omega : lo.length ≤ k)]
      have hk' : k < lo.length + us.length := by simpa using hk
      have := upperT_isUpper hus _ (List.getElem_mem (by omega : k - lo.length < us.length))
      rw [this]
      simp only [Bool.true_eq_false, false_iff]
      omega
  · intro k hk hkL
    have hkl : k < lo.length := by omega
    simp only [List.getElem_append_left hkl]
    obtain ⟨hc, hi1, hilt, hirow, _⟩ := horig k hkl
    have hidx : lo[k].2.src.index = k + 1 := by rw [← hfk k hkl]; exact hfv k hkl
    refine ⟨?_, colM[k + 1], Array.getElem?_eq_getElem (by omega), ?_⟩
    · rw [← hc, ← hidx]
    · simp only [hidx] at hirow
      exact hirow

/-! ## The cells of the column `x₀` -/

/-- **The cells of block `0`.** The column `x₀` of the output has, at the indices
`1 ≤ k ≤ |M(s)[x₀]| - 2`, the rows and stored left ends of `M(s)[x₀]`; the next cell (the
first node of the upper part), if any, has its left end left of the root column. -/
theorem block0_cells {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {colM : Column} {t : Cell}
    {root : Ref} (hTop : Top s M t root) (hcolM : M[M.size - 1]? = some colM)
    (hI : Inv M (M.size - 1) R) (hx0 : M.size - 1 < R.size)
    {es : List (Emit × Origin)} {colX : Column}
    (hes : emitsT (ctxAt M R (M.size - 1) 0 root.column (M.size - 1 - root.column) (M.size - 1)
      (M.size - 1)) (official t.row) = .ok es)
    (hRX : R[M.size - 1]? = some colX)
    (hasm : assemble (ctxAt M R (M.size - 1) 0 root.column (M.size - 1 - root.column)
      (M.size - 1) (M.size - 1)) (es.map Prod.fst) = .ok colX) :
    (∀ k (hk : k < es.length), es[k].2.isUpper = false ↔ k < colM.size - 2) ∧
    colM.size - 1 ≤ colX.size ∧
    (∀ k, 1 ≤ k → k ≤ colM.size - 2 → ∃ (h1 : k < colX.size) (h2 : k < colM.size),
      colX[k].row = colM[k].row ∧ colX[k].left = colM[k].left) ∧
    (∀ h : colM.size - 1 < colX.size, ∃ r, colX[colM.size - 1].left = some r ∧
      r.column < root.column) := by
  set ctx := ctxAt M R (M.size - 1) 0 root.column (M.size - 1 - root.column) (M.size - 1)
    (M.size - 1) with hctxdef
  have hM := hTop.build
  have hV := Canonical.build_valid_of_success hM
  have hMs := Canonical.build_size hM
  have hcr := hTop.lt
  have hctx : RunCtx s ctx t root :=
    runCtx_ctxAt (n := n) hTop (by simp [blockColumns]) (by simp) hx0.le
  have hsrc : ctx.source = M := rfl
  have hxc : ctx.x = M.size - 1 := rfl
  have hsort := JumpLaw.assemble_sorted hasm
  obtain ⟨hLle, hiff, hlow⟩ := block0_lower hctx rfl rfl hes hsort hcolM
  obtain ⟨hsizeX, hcellsX⟩ := JumpLaw.assemble_below hasm
  simp only [List.length_map] at hsizeX
  obtain ⟨hxM, hcolEq⟩ := column_of_getElem? hcolM
  have hCV : ColumnValid M (M.size - 1) colM := by rw [← hcolEq]; exact hV _ hxM
  have hgood := emitsT_good hes
  refine ⟨hiff, by omega, ?_, ?_⟩
  · intro k hk1 hk2
    have hkX : k < colX.size := by omega
    have hkM : k < colM.size := by omega
    refine ⟨hkX, hkM, ?_⟩
    have hke : k - 1 < es.length := by omega
    obtain ⟨hsrck, cv, hcv, hcvrow⟩ := hlow (k - 1) hke (by omega)
    rw [show k - 1 + 1 = k by omega] at hcv
    have hcvk : colM[k] = cv := (Option.some.inj ((Array.getElem?_eq_getElem hkM).symm.trans hcv))
    subst hcvk
    obtain ⟨cell, hcell, hrow, hnone, hsome⟩ := hcellsX (k - 1) (by simpa using hke)
    rw [show k - 1 + 1 = k by omega] at hcell
    have hcellk : colX[k] = cell :=
      Option.some.inj ((Array.getElem?_eq_getElem hkX).symm.trans hcell)
    subst hcellk
    simp only [List.getElem_map] at hrow hnone hsome
    have hone : (1 : Row) ≤ colM[k].row := by
      have hb1 := hCV.bottom_row colM[1] (Array.getElem?_eq_getElem (by omega))
      rcases Nat.eq_or_lt_of_le hk1 with h | h
      · subst h; exact hb1.ge
      · have := hCV.rows_strict 1 k colM[1] colM[k] (Array.getElem?_eq_getElem (by omega))
          (Array.getElem?_eq_getElem hkM) h
        rw [hb1] at this
        exact this.le
    refine ⟨by rw [hrow, ← hcvrow, stored_official hone], ?_⟩
    rcases Nat.eq_or_lt_of_le hk1 with h1 | h1
    · -- the bottom node
      subst h1
      obtain ⟨b, hb, _, hbl⟩ := bottomHolds s n R hrun (M.size - 1) hx0 (by omega)
      obtain ⟨_, hRXeq⟩ := column_of_getElem? hRX
      rw [hRXeq] at hb
      have hbX : colX[1] = b := Option.some.inj ((Array.getElem?_eq_getElem hkX).symm.trans hb)
      have hMl := bottom_left hM (v := ⟨M.size - 1, 1⟩) (cv := colM[1])
        (by simp [Reserve.cell?, hcolM, Array.getElem?_eq_getElem hkM]) rfl (by simp; omega)
      rw [hbX, hbl, hMl]
    · -- a node above the bottom: both left ends are the highest node below the row
      have hrow0 : es[k - 1].1.row ≠ 0 := by
        rw [← hcvrow]
        apply official_ne_zero_of_one_lt
        have hb1 := hCV.bottom_row colM[1] (Array.getElem?_eq_getElem (by omega))
        have := hCV.rows_strict 1 k colM[1] colM[k] (Array.getElem?_eq_getElem (by omega))
          (Array.getElem?_eq_getElem hkM) h1
        rw [hb1] at this
        exact this
      obtain ⟨hgc, _, cv', hcv', hleg⟩ := hgood es[k - 1] (List.getElem_mem hke)
      have hnu : es[k - 1].2.isUpper = false := (hiff (k - 1) hke).mpr (by omega)
      rw [hsrck] at hcv'
      have hcv'k : cv' = colM[k] := by
        obtain ⟨colv, hcolv, hcvv⟩ := cell?_spec hcv'
        change M[M.size - 1]? = some colv at hcolv
        rw [hcolM] at hcolv
        obtain rfl := Option.some.inj hcolv
        rw [show k - 1 + 1 = k by omega, Array.getElem?_eq_getElem hkM] at hcvv
        exact (Option.some.inj hcvv).symm
      subst hcv'k
      obtain ⟨lref, hlref, hlc⟩ : ∃ lref : Ref, colM[k].left = some lref ∧
          es[k - 1].1.leftColumn = some lref.column := by
        rcases hleg with h | ⟨_, h0, _⟩
        · exact h
        · exact absurd (by rw [hcvrow] at h0; exact h0) hrow0
      obtain ⟨ref, href, hbelow⟩ := hsome lref.column hlc
      rw [href, hlref]
      congr 1
      -- the output left end
      have hlegc : JumpLaw.legCol ctx lref.column = lref.column := by
        simp only [JumpLaw.legCol, hctxdef, ctxAt, Nat.mul_zero, Nat.add_zero, ite_self]
      rw [hlegc] at hbelow
      -- the source left end, by the canonical parent
      have hlegal := build_success_legal hM
      have hrawM : Reserve.rawParent M ⟨M.size - 1, k - 1⟩ = some lref := by
        simp [Reserve.rawParent, hcolM, show k - 1 + 1 = k by omega,
          Array.getElem?_eq_getElem hkM, hlref]
      have hst : stored es[k - 1].1.row = colM[k].row := by rw [← hcvrow, stored_official hone]
      obtain ⟨cp, hcp, hcplt, hcpmax⟩ := Proofs.canonical_rawParent_highest_below hlegal hM
        (u := ⟨M.size - 1, k - 1⟩) (cv := colM[k])
        (by simp [Reserve.cell?, hcolM, show k - 1 + 1 = k by omega,
          Array.getElem?_eq_getElem hkM]) hrawM
      obtain ⟨lcol, hlcol, hlcp⟩ := cell?_spec hcp
      have hlx : lref.column < M.size - 1 := by
        obtain ⟨h', _⟩ := hCV.stored_valid k colM[k] lref (Array.getElem?_eq_getElem hkM) hlref
        exact h'
      have hres : ctx.result[lref.column]? = some lcol := by
        simp only [hctxdef, ctxAt]
        rw [JumpLaw.getElem?_extract_lt hlx, hI.2.1 _ hlx, hlcol]
      obtain ⟨hrc, rcell, hrcell, hrrow⟩ := below_result hres hbelow
      have h1 : ref.index ≤ lref.index := by
        refine hcpmax ref.index rcell ?_ (by rw [hst] at hrrow; exact hrrow)
        simp [Reserve.cell?, hlcol, hrcell]
      have h2 : lref.index ≤ ref.index := by
        refine below_max_index hres hbelow hlcp ?_
        rw [hst]
        exact hcplt
      obtain ⟨rc, ri⟩ := ref
      obtain ⟨lc, li⟩ := lref
      simp only at hrc h1 h2 ⊢
      rw [hrc, show ri = li by omega]
  · intro hlt
    have hL : colM.size - 2 < es.length := by have := hCV.size_ge_two; omega
    have hup : es[colM.size - 2].2.isUpper = true := by
      have := hiff (colM.size - 2) hL
      cases hb : es[colM.size - 2].2.isUpper
      · exact absurd (this.mp hb) (lt_irrefl _)
      · rfl
    obtain ⟨hgc, _, cv, hcv, hleg⟩ := hgood es[colM.size - 2] (List.getElem_mem hL)
    rw [hup] at hgc
    simp only [if_true, upperColumn, hctxdef, ctxAt, if_true] at hgc
    obtain ⟨lref, hlref, hlc⟩ : ∃ lref : Ref, cv.left = some lref ∧
        es[colM.size - 2].1.leftColumn = some lref.column := by
      rcases hleg with h | ⟨_, _, h⟩
      · exact h
      · rw [hup] at h; cases h
    obtain ⟨_, hspec⟩ := assemble_spec hasm
    obtain ⟨cell, hcell, _, ref, href, hrefc⟩ := hspec (colM.size - 2) (by simpa using hL)
    rw [show colM.size - 2 + 1 = colM.size - 1 by have := hCV.size_ge_two; omega] at hcell
    have hce : colX[colM.size - 1] = cell :=
      Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hcell)
    refine ⟨ref, by rw [hce]; exact href, ?_⟩
    rw [hrefc]
    simp only [List.getElem_map, legColumn, hlc, hctxdef, ctxAt, Nat.mul_zero, Nat.add_zero,
      ite_self]
    obtain ⟨colv, hcolv, hcvv⟩ := cell?_spec hcv
    change M[_]? = some colv at hcolv
    obtain ⟨hcs, hcolvEq⟩ := column_of_getElem? hcolv
    have hCVr := hV _ hcs
    rw [hcolvEq] at hCVr
    have := (hCVr.stored_valid _ cv lref hcvv hlref).1
    rw [hgc] at this
    exact this

/-! ## The correspondence of frames in block `0` -/

/-- The facts of block `0` used by the correspondence: the output `R` agrees with `M(s)` left
of `x₀`, and its column `x₀` (`colX`) agrees with `M(s)[x₀]` (`colM`) at the indices
`1 ≤ k ≤ |colM| - 2`; the next cell of `colX` has its left end left of the root column, and
the top of `colM` has its left end `root`. -/
structure B0 (R M : Mountain) (colM colX : Column) (root : Ref) : Prop where
  hcolM : M[M.size - 1]? = some colM
  hcolX : R[M.size - 1]? = some colX
  pre : ∀ c, c < M.size - 1 → R[c]? = M[c]?
  size : colM.size - 1 ≤ colX.size
  cells : ∀ k, 1 ≤ k → k ≤ colM.size - 2 → ∃ (h1 : k < colX.size) (h2 : k < colM.size),
    colX[k].row = colM[k].row ∧ colX[k].left = colM[k].left
  next : ∀ h : colM.size - 1 < colX.size, ∃ r, colX[colM.size - 1].left = some r ∧
    r.column < root.column
  top : ∃ h : colM.size - 1 < colM.size, colM[colM.size - 1].left = some root
  two : 2 ≤ colM.size
  normal : (Frame.ofMountain M).Normal
  ordR : (Frame.ofMountain R).Ordered

/-- `z` (a node of the output) corresponds to `z'` (a node of `M(s)`): the same reference,
left of `x₀` or in the lower part of `x₀` below the top. -/
def Corr {R M : Mountain} (colM : Column) (z : (Frame.ofMountain R).Node)
    (z' : (Frame.ofMountain M).Node) : Prop :=
  z.1.val = z'.1.val ∧ z.2.val = z'.2.val ∧
    (z'.1.val < M.size - 1 ∨ (z'.1.val = M.size - 1 ∧ 1 ≤ z'.2.val ∧ z'.2.val ≤ colM.size - 2))

section Frames

variable {R M : Mountain} {colM colX : Column} {root : Ref}

theorem fcell? (z : (Frame.ofMountain R).Node) {col : Column} (h : R[z.1.val]? = some col) :
    col[z.2.val]? = some ((Frame.ofMountain R).cell z) := by
  obtain ⟨hc, rfl⟩ := column_of_getElem? h
  exact Array.getElem?_eq_getElem z.2.isLt

theorem flength (z : (Frame.ofMountain R).Node) {col : Column} (h : R[z.1.val]? = some col) :
    (Frame.ofMountain R).length z.1 = col.size := by
  obtain ⟨hc, rfl⟩ := column_of_getElem? h
  rfl

theorem node_eq_of_ref {F : Frame} {a b : F.Node} (h : ref a = ref b) : a = b := by
  have h1 := F.lookup_ref a
  rw [h, F.lookup_ref b] at h1
  exact (Option.some.inj h1).symm

theorem ref_eq_iff {F : Frame} {a b : F.Node} :
    ref a = ref b ↔ a.1.val = b.1.val ∧ a.2.val = b.2.val := by
  constructor
  · intro h
    exact ⟨congrArg Canonical.Ref.column h, congrArg Canonical.Ref.index h⟩
  · rintro ⟨h1, h2⟩
    show (⟨a.1.val, a.2.val⟩ : Ref) = ⟨b.1.val, b.2.val⟩
    rw [h1, h2]

theorem Corr.ref_eq {z : (Frame.ofMountain R).Node} {z' : (Frame.ofMountain M).Node}
    (h : Corr colM z z') : ref z = ref z' := by
  show (⟨z.1.val, z.2.val⟩ : Ref) = ⟨z'.1.val, z'.2.val⟩
  rw [h.1, h.2.1]

/-- A node of `M(s)` in the domain has a corresponding node of the output. -/
theorem B0.toR (hB : B0 R M colM colX root) (z' : (Frame.ofMountain M).Node)
    (hd : z'.1.val < M.size - 1 ∨
      (z'.1.val = M.size - 1 ∧ 1 ≤ z'.2.val ∧ z'.2.val ≤ colM.size - 2)) :
    ∃ z : (Frame.ofMountain R).Node, Corr colM z z' := by
  have hMc : M[z'.1.val]? = some M[z'.1.val] := Array.getElem?_eq_getElem z'.1.isLt
  have hlenM : z'.2.val < M[z'.1.val].size := z'.2.isLt
  rcases hd with hd | ⟨hd, h1, h2⟩
  · have hR := hB.pre _ hd
    rw [hMc] at hR
    obtain ⟨hc, hcol⟩ := column_of_getElem? hR
    refine ⟨⟨⟨z'.1.val, hc⟩, ⟨z'.2.val, ?_⟩⟩, rfl, rfl, Or.inl hd⟩
    show z'.2.val < R[z'.1.val].size
    rw [hcol]
    exact hlenM
  · have hR := hB.hcolX
    rw [← hd] at hR
    obtain ⟨hc, hcol⟩ := column_of_getElem? hR
    refine ⟨⟨⟨z'.1.val, hc⟩, ⟨z'.2.val, ?_⟩⟩, rfl, rfl, Or.inr ⟨hd, h1, h2⟩⟩
    show z'.2.val < R[z'.1.val].size
    rw [hcol]
    have := hB.size
    omega

/-- A node of the output in the domain has a corresponding node of `M(s)`. -/
theorem B0.toM (hB : B0 R M colM colX root) (z : (Frame.ofMountain R).Node)
    (hd : z.1.val < M.size - 1 ∨
      (z.1.val = M.size - 1 ∧ 1 ≤ z.2.val ∧ z.2.val ≤ colM.size - 2)) :
    ∃ z' : (Frame.ofMountain M).Node, Corr colM z z' := by
  have hRc : R[z.1.val]? = some R[z.1.val] := Array.getElem?_eq_getElem z.1.isLt
  have hlenR : z.2.val < R[z.1.val].size := z.2.isLt
  rcases hd with hd | ⟨hd, h1, h2⟩
  · have hM := hB.pre _ hd
    rw [hRc] at hM
    obtain ⟨hc, hcol⟩ := column_of_getElem? hM.symm
    refine ⟨⟨⟨z.1.val, hc⟩, ⟨z.2.val, ?_⟩⟩, rfl, rfl, Or.inl hd⟩
    show z.2.val < M[z.1.val].size
    rw [hcol]
    exact hlenR
  · have hM := hB.hcolM
    rw [← hd] at hM
    obtain ⟨hc, hcol⟩ := column_of_getElem? hM
    refine ⟨⟨⟨z.1.val, hc⟩, ⟨z.2.val, ?_⟩⟩, rfl, rfl, Or.inr ⟨hd, h1, h2⟩⟩
    show z.2.val < M[z.1.val].size
    rw [hcol]
    omega

/-- Corresponding nodes have the same row and the same stored left end. -/
theorem B0.cell (hB : B0 R M colM colX root) {z : (Frame.ofMountain R).Node}
    {z' : (Frame.ofMountain M).Node} (h : Corr colM z z') :
    ((Frame.ofMountain R).cell z).row = ((Frame.ofMountain M).cell z').row ∧
      ((Frame.ofMountain R).cell z).left = ((Frame.ofMountain M).cell z').left := by
  obtain ⟨hc, hi, hd⟩ := h
  rcases hd with hd | ⟨hd, h1, h2⟩
  · have hMc : M[z'.1.val]? = some M[z'.1.val] := Array.getElem?_eq_getElem z'.1.isLt
    have hR : R[z.1.val]? = some M[z'.1.val] := by rw [hc, hB.pre _ hd, hMc]
    have e1 := fcell? z hR
    have e2 := fcell? z' hMc
    rw [hi] at e1
    rw [Option.some.inj (e1.symm.trans e2)]
    exact ⟨rfl, rfl⟩
  · have hR : R[z.1.val]? = some colX := by rw [hc, hd]; exact hB.hcolX
    have hM : M[z'.1.val]? = some colM := by rw [hd]; exact hB.hcolM
    obtain ⟨hk1, hk2, hrow, hleft⟩ := hB.cells z'.2.val h1 h2
    have e1 := fcell? z hR
    have e2 := fcell? z' hM
    rw [hi, Array.getElem?_eq_getElem hk1] at e1
    rw [Array.getElem?_eq_getElem hk2] at e2
    rw [← Option.some.inj e1, ← Option.some.inj e2]
    exact ⟨hrow, hleft⟩

theorem B0.height (hB : B0 R M colM colX root) {z : (Frame.ofMountain R).Node}
    {z' : (Frame.ofMountain M).Node} (h : Corr colM z z') :
    (Frame.ofMountain R).height z = (Frame.ofMountain M).height z' := (hB.cell h).1

/-- Two output nodes corresponding to the same node of `M(s)` are equal. -/
theorem Corr.unique {z w : (Frame.ofMountain R).Node} {z' : (Frame.ofMountain M).Node}
    (h1 : Corr colM z z') (h2 : Corr colM w z') : z = w :=
  node_eq_of_ref (h1.ref_eq.trans h2.ref_eq.symm)

theorem Corr.unique' {z : (Frame.ofMountain R).Node} {z' w' : (Frame.ofMountain M).Node}
    (h1 : Corr colM z z') (h2 : Corr colM z w') : z' = w' :=
  node_eq_of_ref (h1.ref_eq.symm.trans h2.ref_eq)

/-- The node above corresponds, below the top of the lower part. -/
theorem B0.upper (hB : B0 R M colM colX root) {z : (Frame.ofMountain R).Node}
    {z' : (Frame.ofMountain M).Node} (h : Corr colM z z')
    (hnt : z'.1.val < M.size - 1 ∨ z'.2.val < colM.size - 2) :
    (∀ v', (Frame.ofMountain M).upper z' = some v' →
        ∃ v, (Frame.ofMountain R).upper z = some v ∧ Corr colM v v') ∧
      (∀ v, (Frame.ofMountain R).upper z = some v →
        ∃ v', (Frame.ofMountain M).upper z' = some v' ∧ Corr colM v v') := by
  obtain ⟨hc, hi, hd⟩ := h
  refine ⟨fun v' hv' => ?_, fun v hv => ?_⟩
  · obtain ⟨hv1, hv2⟩ := upper_spec hv'
    have hv1' : v'.1.val = z'.1.val := congrArg Fin.val hv1
    have hdv : v'.1.val < M.size - 1 ∨
        (v'.1.val = M.size - 1 ∧ 1 ≤ v'.2.val ∧ v'.2.val ≤ colM.size - 2) := by
      rcases hd with hd | ⟨hd, _, _⟩
      · left; omega
      · rcases hnt with hnt | hnt
        · omega
        · right; exact ⟨by omega, by omega, by omega⟩
    obtain ⟨v, hv⟩ := hB.toR v' hdv
    refine ⟨v, ControlProof.upper_eq_of_index (Fin.ext ?_) ?_, hv⟩
    · rw [hc, hv.1, hv1]
    · rw [hv.2.1, hv2, hi]
  · obtain ⟨hv1, hv2⟩ := upper_spec hv
    have hv1' : v.1.val = z.1.val := congrArg Fin.val hv1
    have hdv : v.1.val < M.size - 1 ∨
        (v.1.val = M.size - 1 ∧ 1 ≤ v.2.val ∧ v.2.val ≤ colM.size - 2) := by
      rcases hd with hd | ⟨hd, _, _⟩
      · left; omega
      · rcases hnt with hnt | hnt
        · omega
        · right; exact ⟨by omega, by omega, by omega⟩
    obtain ⟨v', hv'⟩ := hB.toM v hdv
    refine ⟨v', ControlProof.upper_eq_of_index (Fin.ext ?_) ?_, hv'⟩
    · rw [← hc, ← hv'.1, hv1]
    · rw [← hv'.2.1, hv2, hi]

/-- Stored parents correspond, below the top of the lower part. -/
theorem B0.rawParent (hB : B0 R M colM colX root) {z : (Frame.ofMountain R).Node}
    {z' : (Frame.ofMountain M).Node} (h : Corr colM z z')
    (hnt : z'.1.val < M.size - 1 ∨ z'.2.val < colM.size - 2) :
    (∀ a', (Frame.ofMountain M).rawParent z' = some a' →
        ∃ a, (Frame.ofMountain R).rawParent z = some a ∧ Corr colM a a') ∧
      (∀ a, (Frame.ofMountain R).rawParent z = some a →
        ∃ a', (Frame.ofMountain M).rawParent z' = some a' ∧ Corr colM a a') := by
  have hzx : z'.1.val ≤ M.size - 1 := by
    rcases h.2.2 with hd | ⟨hd, _⟩ <;> omega
  refine ⟨fun a' ha' => ?_, fun a ha => ?_⟩
  · obtain ⟨v', hv', hl'⟩ := rawParent_spec ha'
    obtain ⟨v, hv, hvv⟩ := (hB.upper h hnt).1 v' hv'
    have hlt := rawParent_column_lt hB.normal.toOrdered ha'
    obtain ⟨a, ha⟩ := hB.toR a' (Or.inl (by omega))
    refine ⟨a, rawParent_eq_of_upper_left hv ?_, ha⟩
    rw [(hB.cell hvv).2, hl', ha.ref_eq]
  · obtain ⟨v, hv, hl⟩ := rawParent_spec ha
    obtain ⟨v', hv', hvv⟩ := (hB.upper h hnt).2 v hv
    have hlt := rawParent_column_lt hB.ordR ha
    obtain ⟨a', ha'⟩ := hB.toM a (Or.inl (by rw [h.1] at hlt; omega))
    refine ⟨a', rawParent_eq_of_upper_left hv' ?_, ha'⟩
    rw [← (hB.cell hvv).2, hl, ha'.ref_eq]

/-- Two nodes of one column, both at or below the row `H`, whose upper nodes are above `H`,
are equal. -/
theorem node_eq_of_top {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1) {H : Row}
    (ha : F.height a ≤ H) (hb : F.height b ≤ H)
    (hau : ∀ v, F.upper a = some v → H < F.height v)
    (hbu : ∀ v, F.upper b = some v → H < F.height v) : a = b := by
  have key : ∀ x y : F.Node, x.1 = y.1 → x.2.val < y.2.val → F.height y ≤ H →
      (∀ v, F.upper x = some v → H < F.height v) → False := by
    intro x y hxy hlt hy hxu
    have hlen : x.2.val + 1 < F.length x.1 := by
      have h1 := y.2.isLt
      have h2 : F.length x.1 = F.length y.1 := by rw [hxy]
      omega
    let v : F.Node := ⟨x.1, ⟨x.2.val + 1, hlen⟩⟩
    have hv : F.upper x = some v := ControlProof.upper_eq_of_index rfl rfl
    have h1 := hxu v hv
    have h2 : F.height v ≤ F.height y :=
      ControlProof.height_le_of_index hF hxy (by show x.2.val + 1 ≤ y.2.val; omega)
    exact absurd (lt_of_lt_of_le h1 (h2.trans hy)) (lt_irrefl _)
  rcases Nat.lt_trichotomy a.2.val b.2.val with h | h | h
  · exact (key a b hc h hb hau).elim
  · exact ControlProof.node_eq_of_index hc h
  · exact (key b a hc.symm h ha hbu).elim

/-- The candidates correspond. -/
theorem B0.Q (hB : B0 R M colM colX root) {z : (Frame.ofMountain R).Node}
    {z' : (Frame.ofMountain M).Node} (h : Corr colM z z') {q : (Frame.ofMountain R).Node}
    (hq : (Frame.ofMountain R).Q z = some q) :
    ∃ q', (Frame.ofMountain M).Q z' = some q' ∧ Corr colM q q' := by
  have hOR := hB.ordR
  have hOM := hB.normal.toOrdered
  obtain ⟨left, hleft, hlc, _, hql, _, hqh, hqu⟩ := Q_spec hOR hq
  have hzx : z.1.val ≤ M.size - 1 := by
    rcases h.2.2 with hd | ⟨hd, _⟩ <;> rw [h.1] <;> omega
  have hleftM : ((Frame.ofMountain M).cell z').left = some (ref left) := by
    rw [← (hB.cell h).2, hleft]
  obtain ⟨q', hq'⟩ := Q_exists_of_left hOM ⟨_, hleftM⟩
  refine ⟨q', hq', ?_⟩
  obtain ⟨left', hleft', _, _, hql', _, hqh', hqu'⟩ := Q_spec hOM hq'
  rw [hleftM] at hleft'
  have hll : ref left = ref left' := Option.some.inj hleft'
  have hqx : q.1.val < M.size - 1 := by rw [hql]; omega
  obtain ⟨q'', hq''⟩ := hB.toM q (Or.inl hqx)
  have he : q'' = q' := by
    refine node_eq_of_top hOM (H := (Frame.ofMountain M).height z') ?_ ?_ hqh' ?_ hqu'
    · apply Fin.ext
      rw [← hq''.1, hql, hql']
      exact congrArg Canonical.Ref.column hll
    · rw [← hB.height hq'', ← hB.height h]
      exact hqh
    · intro v' hv'
      obtain ⟨v, hv, hvv⟩ := (hB.upper hq'' (Or.inl (by rw [← hq''.1]; exact hqx))).1 v' hv'
      rw [← hB.height hvv, ← hB.height h]
      exact hqu v hv
  rw [← he]
  exact hq''

/-- Chains of stored parents of `M(s)` left of `x₀` are chains of the output. -/
theorem B0.chain (hB : B0 R M colM colX root) {a' c' : (Frame.ofMountain M).Node}
    (hc : RawChain (Frame.ofMountain M) a' c') :
    ∀ a : (Frame.ofMountain R).Node, Corr colM a a' → a'.1.val < M.size - 1 →
      ∃ c, RawChain (Frame.ofMountain R) a c ∧ Corr colM c c' := by
  induction hc with
  | here c' => exact fun a ha _ => ⟨a, .here a, ha⟩
  | @step a' b' c' hraw rest ih =>
    intro a ha hax
    obtain ⟨b, hb, hbb⟩ := (hB.rawParent ha (Or.inl hax)).1 b' hraw
    have hlt := rawParent_column_lt hB.normal.toOrdered hraw
    obtain ⟨c, hc, hcc⟩ := ih b hbb (by omega)
    exact ⟨c, .step hb hc, hcc⟩

end Frames

section LexTransfer

variable {R M : Mountain} {colM colX : Column} {root : Ref}

/-- The node of `M(s)` above a node of the lower part of `x₀` exists. -/
theorem B0.upper_x0 (hB : B0 R M colM colX root) {z' : (Frame.ofMountain M).Node}
    (hz : z'.1.val = M.size - 1) (hle : z'.2.val ≤ colM.size - 2) :
    ∃ v', (Frame.ofMountain M).upper z' = some v' := by
  have hlen : (Frame.ofMountain M).length z'.1 = colM.size :=
    flength z' (by rw [hz]; exact hB.hcolM)
  obtain ⟨h1, _⟩ := hB.top
  have h2 := hB.two
  have hlt : z'.2.val + 1 < (Frame.ofMountain M).length z'.1 := by omega
  exact ⟨⟨z'.1, ⟨z'.2.val + 1, hlt⟩⟩, ControlProof.upper_eq_of_index rfl rfl⟩

/-- At the top of the lower part, the stored parent in `M(s)` is `root` (the left end of `t`). -/
theorem B0.rawParent_top (hB : B0 R M colM colX root) {z' a' : (Frame.ofMountain M).Node}
    (hz : z'.1.val = M.size - 1) (hL : z'.2.val = colM.size - 2)
    (ha : (Frame.ofMountain M).rawParent z' = some a') : a'.1.val = root.column := by
  obtain ⟨v', hv', hl'⟩ := rawParent_spec ha
  obtain ⟨hv1, hv2⟩ := upper_spec hv'
  obtain ⟨htl, htop⟩ := hB.top
  have hM : M[v'.1.val]? = some colM := by rw [hv1, hz]; exact hB.hcolM
  have e := fcell? v' hM
  have h2 := hB.two
  rw [hv2, hL, show colM.size - 2 + 1 = colM.size - 1 by omega,
    Array.getElem?_eq_getElem htl] at e
  rw [← Option.some.inj e, htop] at hl'
  exact (congrArg Canonical.Ref.column (Option.some.inj hl')).symm

/-- At the top of the lower part, the output column ends or its stored parent is left of the
root column. -/
theorem B0.rawParent_top_R (hB : B0 R M colM colX root) {z : (Frame.ofMountain R).Node}
    (hz : z.1.val = M.size - 1) (hL : z.2.val = colM.size - 2) :
    (Frame.ofMountain R).upper z = none ∨
      ∃ a, (Frame.ofMountain R).rawParent z = some a ∧ a.1.val < root.column := by
  cases hv : (Frame.ofMountain R).upper z with
  | none => exact Or.inl rfl
  | some v =>
    right
    obtain ⟨hv1, hv2⟩ := upper_spec hv
    have hR : R[v.1.val]? = some colX := by rw [hv1, hz]; exact hB.hcolX
    have hlen := flength v hR
    have hvl : v.2.val < colX.size := by rw [← hlen]; exact v.2.isLt
    have hidx : v.2.val = colM.size - 1 := by
      have := hB.two
      omega
    obtain ⟨r, hr, hrc⟩ := hB.next (by omega)
    have e := fcell? v hR
    rw [Array.getElem?_eq_getElem hvl] at e
    have hleft : ((Frame.ofMountain R).cell v).left = some r := by
      rw [← Option.some.inj e]
      simp only [hidx]
      exact hr
    obtain ⟨a, hla, _, _⟩ := hB.ordR.stored_valid v r hleft
    have hra : ref a = r := lookup_spec hla
    refine ⟨a, rawParent_eq_of_upper_left hv (by rw [hleft, hra]), ?_⟩
    have : a.1.val = r.column := by rw [← hra]; rfl
    omega

/-- **`Lex` transfers from `M(s)` to the output.** For `z'` in the lower part of the column
`x₀` and `w'` left of `x₀`, `Lex z' w'` in `M(s)` gives `Lex z w` in the output for the
corresponding nodes. -/
theorem B0.lex (hB : B0 R M colM colX root) {z' w' : (Frame.ofMountain M).Node}
    (hl : Lex (Frame.ofMountain M) z' w') :
    ∀ (z w : (Frame.ofMountain R).Node), Corr colM z z' → Corr colM w w' →
      z'.1.val = M.size - 1 → w'.1.val < M.size - 1 → Lex (Frame.ofMountain R) z w := by
  induction hl with
  | @top z' w' hz =>
    intro z w hzz _ hzx _
    have hle : z'.2.val ≤ colM.size - 2 := by
      rcases hzz.2.2 with h | ⟨_, _, h⟩
      · omega
      · exact h
    obtain ⟨v', hv'⟩ := hB.upper_x0 hzx hle
    rw [hz] at hv'
    cases hv'
  | @left z' w' a' b' ha hb hab =>
    intro z w hzz hww hzx hwx
    obtain ⟨b, hbR, hbb⟩ := (hB.rawParent hww (Or.inl hwx)).1 b' hb
    have hle : z'.2.val ≤ colM.size - 2 := by
      rcases hzz.2.2 with h | ⟨_, _, h⟩
      · omega
      · exact h
    rcases Nat.lt_or_ge z'.2.val (colM.size - 2) with hlt | hge
    · obtain ⟨a, haR, haa⟩ := (hB.rawParent hzz (Or.inr hlt)).1 a' ha
      exact Lex.left haR hbR (by rw [haa.1, hbb.1]; exact hab)
    · have hL : z'.2.val = colM.size - 2 := by omega
      have ha1 := hB.rawParent_top hzx hL ha
      rcases hB.rawParent_top_R (z := z) (by rw [hzz.1]; exact hzx) (by rw [hzz.2.1]; exact hL)
        with hnone | ⟨a, haR, hac⟩
      · exact Lex.top hnone
      · exact Lex.left haR hbR (by rw [hbb.1]; omega)
  | @same z' w' z'' w'' a' hz hw ha hb hh rest ih =>
    intro z w hzz hww hzx hwx
    obtain ⟨b, hbR, hbb⟩ := (hB.rawParent hww (Or.inl hwx)).1 a' hb
    obtain ⟨wu, hwu, hwwu⟩ := (hB.upper hww (Or.inl hwx)).1 w'' hw
    have hle : z'.2.val ≤ colM.size - 2 := by
      rcases hzz.2.2 with h | ⟨_, _, h⟩
      · omega
      · exact h
    rcases Nat.lt_or_ge z'.2.val (colM.size - 2) with hlt | hge
    · obtain ⟨a, haR, haa⟩ := (hB.rawParent hzz (Or.inr hlt)).1 a' ha
      obtain ⟨zu, hzu, hzzu⟩ := (hB.upper hzz (Or.inr hlt)).1 z'' hz
      have hab : a = b := Corr.unique haa hbb
      subst hab
      obtain ⟨hz1, _⟩ := upper_spec hz
      obtain ⟨hw1, _⟩ := upper_spec hw
      refine Lex.same hzu hwu haR hbR ?_ (ih zu wu hzzu hwwu ?_ ?_)
      · rw [hB.height hzzu, hB.height hwwu, hh]
      · rw [hz1]; exact hzx
      · rw [hw1]; exact hwx
    · have hL : z'.2.val = colM.size - 2 := by omega
      have ha1 := hB.rawParent_top hzx hL ha
      rcases hB.rawParent_top_R (z := z) (by rw [hzz.1]; exact hzx) (by rw [hzz.2.1]; exact hL)
        with hnone | ⟨a, haR, hac⟩
      · exact Lex.top hnone
      · exact Lex.left haR hbR (by rw [hbb.1]; omega)

end LexTransfer

/-! ## The cross case in block `0` -/

/-- The block of a new column `X ≤ x₀` is `0`. -/
theorem block_zero_of_le {cr x0 n i x X : Nat} (hcr : cr < x0)
    (hx : x ∈ blockColumns cr x0 n i) (hX : X = x + (x0 - cr) * i) (hle : X ≤ x0) :
    i = 0 ∧ x = x0 := by
  obtain ⟨h1, h2⟩ := mem_blockColumns hcr hx
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp [blockColumns] at hx
    exact ⟨rfl, hx⟩
  · exfalso
    have : x0 - cr ≤ (x0 - cr) * i := Nat.le_mul_of_pos_right _ hi
    omega

/-- **The cross case in block `0`.** For a node `u` of the column `x₀` of the output whose
upper node `u⁺` is a copy of the lower part (its origin is not of the upper kind), the
conclusion of `CrossLexHolds` holds. -/
theorem crossLex_block0 {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R)
    {u p q up : (Frame.ofMountain R).Node} {o : Origin} (hx : u.1.val = s.length - 1)
    (hu : Real u) (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hq : (Frame.ofMountain R).Q u = some q) (hcol : q.1 ≠ p.1)
    (hup : (Frame.ofMountain R).upper u = some up)
    (ho : OriginAt s n R up.1.val (up.2.val - 1) o) (hK : o.isUpper = false) :
    ∃ c cp, RawChain (Frame.ofMountain R) q c ∧
      (Frame.ofMountain R).rawParent c = some p ∧ (Frame.ofMountain R).upper c = some cp ∧
      (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
      Lex (Frame.ofMountain R) up cp := by
  obtain ⟨M, colM, t, root, x, i, es, em, hM, hcolM, ht, hroot, hcr, hxb, hX, hes,
    ⟨colX, hRX, _, hasm⟩, hj⟩ := ho
  have hMs := Canonical.build_size hM
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupx : up.1.val = M.size - 1 := by rw [hup1, hx, hMs]
  obtain ⟨rfl, rfl⟩ := block_zero_of_le hcr hxb hX (by omega)
  rw [hupx] at hRX hes hasm
  -- the run data
  obtain ⟨M', col', t', root', hM', hcol', ht', hTop, _, hI⟩ :=
    run_new_column hrun (X := M.size - 1) (by rw [← hupx]; exact up.1.isLt) (by omega)
  rw [hM] at hM'
  obtain rfl := Except.ok.inj hM'
  rw [hcolM] at hcol'
  obtain rfl := Option.some.inj hcol'
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have hroot' : root' = root := by
    have := hTop.left
    rw [hroot] at this
    exact (Option.some.inj this).symm
  rw [hroot'] at hTop
  obtain ⟨hiff, hsize, hcells, hnext⟩ := block0_cells hrun hTop hcolM hI
    (by rw [← hupx]; exact up.1.isLt) hes hRX hasm
  have hV := Canonical.build_valid_of_success hM
  obtain ⟨hxM, hcolEq⟩ := column_of_getElem? hcolM
  have hCV : ColumnValid M (M.size - 1) colM := by rw [← hcolEq]; exact hV _ hxM
  obtain ⟨_, _, _, _, hBR⟩ := run_basic hrun
  have hB : B0 R M colM colX root :=
    { hcolM := hcolM
      hcolX := hRX
      pre := hI.2.1
      size := hsize
      cells := hcells
      next := hnext
      top := by
        have hsz := hCV.size_ge_two
        refine ⟨by omega, ?_⟩
        rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)] at ht
        rw [Option.some.inj ht]
        exact hroot
      two := hCV.size_ge_two
      normal := Canonical.build_normal_of_success hM
      ordR := hBR.valid.toOrdered }
  have hN := hB.normal
  -- the index of `u⁺` in the lower part
  have hjlt : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  have hjL : up.2.val - 1 < colM.size - 2 :=
    (hiff _ hjlt).mp (by rw [hej]; exact hK)
  have hu1 : 1 ≤ u.2.val := hu
  -- the corresponding nodes of `M(s)`
  obtain ⟨s0, hs0⟩ := hB.toM u (Or.inr ⟨by rw [hx, hMs], hu1, by omega⟩)
  have hs0x : s0.1.val = M.size - 1 := by rw [← hs0.1, hx, hMs]
  have hs0L : s0.2.val < colM.size - 2 := by rw [← hs0.2.1]; omega
  obtain ⟨sp, hsp, hupsp⟩ := (hB.upper hs0 (Or.inr hs0L)).2 up hup
  obtain ⟨pM, hpM, hppM⟩ := (hB.rawParent hs0 (Or.inr hs0L)).2 p hraw
  obtain ⟨q0, hq0, hqq0⟩ := hB.Q hs0 hq
  have hs0r : Real s0 := by show 0 < s0.2.val; rw [← hs0.2.1]; exact hu
  have hne : q0 ≠ pM := by
    intro he
    subst he
    exact hcol (Fin.ext (by rw [hqq0.1, hppM.1]))
  obtain ⟨cm, hcm, hcmp⟩ := normal_chain_exists hN hs0r hpM hq0 hne
  obtain ⟨cmu, hcmu, _⟩ := rawParent_spec hcmp
  obtain ⟨_, hrow, hlex⟩ := normal_crossLex hN hs0r hsp hpM hq0 hcm hcmp hcmu
  -- back to the output
  have hqx : q0.1.val < M.size - 1 := by
    have := Q_column_lt hN.toOrdered hq0
    omega
  obtain ⟨c, hc, hccm⟩ := hB.chain hcm q hqq0 hqx
  have hcmx : cm.1.val < M.size - 1 := by
    have := hcm.column_le hN.toOrdered
    omega
  obtain ⟨p', hp', hp'pM⟩ := (hB.rawParent hccm (Or.inl hcmx)).1 pM hcmp
  have hpp : p' = p := Corr.unique hp'pM hppM
  subst hpp
  obtain ⟨cp, hcp, hcpcm⟩ := (hB.upper hccm (Or.inl hcmx)).1 cmu hcmu
  refine ⟨c, cp, hc, hp', hcp, ?_, ?_⟩
  · rw [hB.height hupsp, hB.height hcpcm, hrow]
  · obtain ⟨hsp1, _⟩ := upper_spec hsp
    obtain ⟨hcmu1, _⟩ := upper_spec hcmu
    exact hB.lex hlex up cp hupsp hcpcm (by rw [hsp1]; exact hs0x) (by rw [hcmu1]; exact hcmx)

/-! ## The reduction to the columns right of `x₀` -/

/-- **Open (per kind), right of `x₀`.** `CrossLexFor K` for the nodes `u` in the columns
`X > x₀` (the blocks `i ≥ 1`). -/
def CrossLexPos (K : Origin → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (u p q up : (Frame.ofMountain R).Node) (o : Origin), s.length ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 → (Frame.ofMountain R).upper u = some up →
      OriginAt s n R up.1.val (up.2.val - 1) o → K o →
      ∃ c cp, RawChain (Frame.ofMountain R) q c ∧
        (Frame.ofMountain R).rawParent c = some p ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
        Lex (Frame.ofMountain R) up cp

/-- **`CrossLexFor K` from its part right of `x₀`**, for every kind `K` of the lower part:
the column `x₀` (block `0`) is `crossLex_block0`. -/
theorem crossLexFor_of_pos {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (h : CrossLexPos K) : CrossLexFor K := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hKo
  rcases Nat.lt_or_ge (s.length - 1) u.1.val with hlt | hge
  · exact h s n R hrun u p q up o (by omega) hu hraw hq hcol hup ho hKo
  · exact crossLex_block0 hrun (by omega) hu hraw hq hcol hup ho (hK o hKo)

theorem isPlain_notUpper : ∀ o, IsPlain o → o.isUpper = false := by
  rintro o ⟨r, rfl⟩
  rfl

theorem isClean_notUpper : ∀ o, IsClean o → o.isUpper = false := by
  rintro o ⟨r, rfl⟩
  rfl

/-- **`CrossLexFor IsPlain` from its part right of `x₀`.** -/
theorem crossLexFor_plain_of_pos (h : CrossLexPos IsPlain) : CrossLexFor IsPlain :=
  crossLexFor_of_pos isPlain_notUpper h

/-- **`CrossLexFor IsClean` from its part right of `x₀`.** -/
theorem crossLexFor_clean_of_pos (h : CrossLexPos IsClean) : CrossLexFor IsClean :=
  crossLexFor_of_pos isClean_notUpper h

end OmegaY.Official.Recon.CrossPlain

#print axioms OmegaY.Official.Recon.CrossPlain.crossLex_block0
#print axioms OmegaY.Official.Recon.CrossPlain.crossLexFor_plain_of_pos
#print axioms OmegaY.Official.Recon.CrossPlain.crossLexFor_clean_of_pos
