/-
Ported verbatim from koteitan/trio, `lean/Cofinality.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Cofinality.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Cofinality.lean: トリオ数列の Bachmann 共終性（基本列は標準形の中で共終）
への還元機構。

目標: `SeqlexCofinality : seqlex N M → ∃ n ≥ 1, sle N (M⟦n⟧)`（標準形上）。
`olt_ST_iff_seqlex` により translate 側の共終性
`tr N <o tr M → ∃ n, tr N ≤o tr (M⟦n⟧)` が従う（probe: 15038 対 0 失敗、
crux レベル 28010 対 0 失敗）。この章は yapss Cofinality.lean の 3 行版。
-/
import Googology.Trans.BMS.TrioCof.Invariant

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-! ## Part 0 — `seqlex` の配管 -/

theorem collt_trans {p q r : ℕ × ℕ × ℕ} (h1 : collt p q) (h2 : collt q r) :
    collt p r := by
  unfold collt at *
  omega

/-- `seqlex` is transitive. -/
theorem seqlex_trans : ∀ {A B C : TrioSeq}, seqlex A B → seqlex B C →
    seqlex A C := by
  intro A
  induction A with
  | nil =>
    intro B C _ h2
    rcases C with _ | ⟨c, C'⟩
    · rcases B with _ | ⟨b, B'⟩
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
    · simp
  | cons a A' ih =>
    intro B C h1 h2
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h1 (by simp)
    rcases C with _ | ⟨c, C'⟩
    · exact absurd h2 (by simp)
    rw [seqlex_cons_cons] at h1 h2 ⊢
    rcases h1 with p1 | ⟨rfl, s1⟩ <;> rcases h2 with p2 | ⟨rfl, s2⟩
    · exact Or.inl (collt_trans p1 p2)
    · exact Or.inl p1
    · exact Or.inl p2
    · exact Or.inr ⟨rfl, ih s1 s2⟩

/-- `≤` version of `seqlex`. -/
def sle (M N : TrioSeq) : Prop := M = N ∨ seqlex M N

theorem sle_refl (M : TrioSeq) : sle M M := Or.inl rfl

theorem seqlex_sle_trans {A B C : TrioSeq} (h1 : seqlex A B) (h2 : sle B C) :
    seqlex A C := by
  rcases h2 with rfl | h2
  · exact h1
  · exact seqlex_trans h1 h2

theorem sle_trans {A B C : TrioSeq} (h1 : sle A B) (h2 : sle B C) :
    sle A C := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (seqlex_sle_trans h1 h2)

/-- `seqlex` is monotone under extending the *larger* side on the right. -/
theorem seqlex_append_mono : ∀ {A B : TrioSeq}, seqlex A B → ∀ (C : TrioSeq),
    seqlex A (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · simp
  | cons a A' ih =>
    intro B h C
    rcases B with _ | ⟨b, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · exact Or.inr ⟨rfl, ih hs C⟩

/-- `sle` version of `seqlex_append_mono`. -/
theorem sle_append_mono {A B : TrioSeq} (h : sle A B) (C : TrioSeq) :
    sle A (B ++ C) := by
  rcases h with rfl | h
  · rcases C with _ | ⟨c, C'⟩
    · exact Or.inl (by simp)
    · exact Or.inr (seqlex_prefix (by simp) A)
  · exact Or.inr (seqlex_append_mono h C)

theorem sle_append_cancel (A : TrioSeq) {u v : TrioSeq} :
    sle (A ++ u) (A ++ v) ↔ sle u v := by
  unfold sle
  rw [seqlex_append_cancel]
  constructor
  · rintro (h | h)
    · exact Or.inl (List.append_cancel_left h)
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h

/-- **Snoc case analysis.**  A sequence below `D ++ [lp]` either stays `≤ D`,
or extends `D` by a first column strictly below `lp`. -/
theorem seqlex_snoc_cases : ∀ {D : TrioSeq} {lp : ℕ × ℕ × ℕ} {N : TrioSeq},
    seqlex N (D ++ [lp]) →
    sle N D ∨ ∃ q S, N = D ++ q :: S ∧ collt q lp := by
  intro D
  induction D with
  | nil =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (sle_refl _)
    · rw [List.nil_append, seqlex_cons_cons] at h
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inr ⟨q, S, rfl, h⟩
      · exact absurd h (by cases S <;> simp)
  | cons d D' ih =>
    intro lp N h
    rcases N with _ | ⟨q, S⟩
    · exact Or.inl (Or.inr (by simp))
    rw [List.cons_append, seqlex_cons_cons] at h
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl (Or.inr (Or.inl h))
    · rcases ih h with hle | ⟨q', S', rfl, hq'⟩
      · refine Or.inl ?_
        rcases hle with rfl | hle
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨rfl, hle⟩)
      · exact Or.inr ⟨q', S', by simp, hq'⟩

/-! ## Part 1 — 共終性の `seqlex` 形への還元 -/

/-- The `seqlex` form of trio Bachmann cofinality. -/
def SeqlexCofinality : Prop :=
  ∀ {M N : TrioSeq}, ST_TS M → ST_TS N → seqlex N M →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

theorem ts_cofinality_of_seqlex (H : SeqlexCofinality)
    {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) := by
  have hne : N ≠ M := by
    rintro rfl
    exact olt_irrefl _ h
  have hsl : seqlex N M := (olt_ST_iff_seqlex hN hM hne).1 h
  obtain ⟨n, hn, hres⟩ := H hM hN hsl
  refine ⟨n, hn, ?_⟩
  rcases hres with rfl | hlt
  · exact Or.inr rfl
  · by_cases he : N = M⟦n⟧
    · exact Or.inr (by rw [he])
    · exact Or.inl ((olt_ST_iff_seqlex hN (ST_TS.oper hM hn) he).2 hlt)

/-! ## Part 2 — `oper` の退化枝 -/

/-- **Branch `self`**: `M` has length `≤ 1`, so `M⟦n⟧ = M`. -/
theorem seqlex_cof_short {M N : TrioSeq} (hL : M.length - 1 = 0)
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) :=
  ⟨1, le_rfl, by rw [oper_eq_self_of_short 1 hL]; exact Or.inr h⟩

theorem dropLast_snoc_getD {M : TrioSeq} (hne : M ≠ []) :
    M.dropLast ++ [M.getD (M.length - 1) (0, 0, 0)] = M := by
  conv_rhs => rw [← List.dropLast_append_getLast hne]
  congr 1
  rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by
      have := List.length_pos_iff.2 hne
      omega)]
  rfl

/-- **Branch `zero`**: the last column is `(0,0,0)`, so `M⟦n⟧ = M.dropLast`.
Nothing squeezes strictly between `M.dropLast` and `M` because `(0,0,0)` is
the `collt`-minimum. -/
theorem seqlex_cof_zero {M N : TrioSeq} (hL : 1 < M.length)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0)
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hne : M ≠ [] := by
    intro he
    rw [he] at hL
    simp at hL
  have hlpz : M.getD (M.length - 1) (0, 0, 0) = (0, 0, 0) :=
    Prod.ext hz.1 (Prod.ext hz.2.1 hz.2.2)
  have hMsplit : M.dropLast ++ [M.getD (M.length - 1) (0, 0, 0)] = M :=
    dropLast_snoc_getD hne
  have hop : M⟦1⟧ = M.dropLast := by
    rw [oper_eq_pred_of_zero 1 (by omega) hz]
    unfold Pred
    rw [if_neg (by omega)]
  refine ⟨1, le_rfl, ?_⟩
  rw [hop]
  rcases seqlex_snoc_cases (D := M.dropLast) (lp := M.getD (M.length - 1) (0, 0, 0))
      (N := N) (by rw [hMsplit]; exact h) with hle | ⟨q, S, -, hq⟩
  · exact hle
  · rw [hlpz] at hq
    simp [collt] at hq

/-! ## Part 3 — bad 枝の crux への還元 -/

/-- **The bad-branch crux** (to be discharged by the copy-domination
machinery): a standard `N` extending the good prefix `M.dropLast` with a
column strictly below the dropped one is caught by some expansion. -/
def TrioBadCrux : Prop :=
  ∀ {M N : TrioSeq} {q : ℕ × ℕ × ℕ} {S : TrioSeq},
    ST_TS M → ST_TS N → 1 < M.length →
    ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) →
    N = M.dropLast ++ q :: S →
    collt q (M.getD (M.length - 1) (0, 0, 0)) →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

/-- The good prefix plus the zeroth copy is exactly `M.dropLast`. -/
theorem take_gcopy_zero {M : TrioSeq} (hL : 1 < M.length)
    (_hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    M.take (parent M (srow M (M.length - 1)) (M.length - 1))
      ++ seg M (parent M (srow M (M.length - 1)) (M.length - 1))
        (M.length - 1 - parent M (srow M (M.length - 1)) (M.length - 1))
      = M.dropLast := by
  have j0lt := nextR_index_lt (parent_nextR hp)
  set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
  have hdl : M.dropLast = M.take (M.length - 1) := List.dropLast_eq_take
  rw [hdl]
  have htk : (M.take (M.length - 1)).take j0 = M.take j0 := by
    rw [List.take_take]
    congr 1
    omega
  conv_rhs => rw [← List.take_append_drop j0 (M.take (M.length - 1))]
  rw [htk]
  congr 1
  rw [drop_seg]
  have hlen : (M.take (M.length - 1)).length = M.length - 1 := by
    rw [List.length_take]
    omega
  rw [hlen]
  unfold seg
  refine List.map_congr_left ?_
  intro j hj
  have hjb := List.mem_range'_1.1 hj
  have e0 : entry (M.take (M.length - 1)) 0 j = entry M 0 j := by
    unfold entry
    rw [getD_take (by omega)]
  have e1 : entry (M.take (M.length - 1)) 1 j = entry M 1 j := by
    unfold entry
    rw [getD_take (by omega)]
  have e2 : entry (M.take (M.length - 1)) 2 j = entry M 2 j := by
    unfold entry
    rw [getD_take (by omega)]
  rw [e0, e1, e2]

/-- **Branch `bad`, modulo the crux.** -/
theorem seqlex_cof_bad (H : TrioBadCrux) {M N : TrioSeq}
    (hM : ST_TS M) (hN : ST_TS N) (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (h : seqlex N M) : ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hp := hasParent_last_ST_TS hM (by omega) hz
  have hne : M ≠ [] := by
    intro he
    rw [he] at L
    simp at L
  rcases seqlex_snoc_cases (D := M.dropLast)
      (lp := M.getD (M.length - 1) (0, 0, 0)) (N := N)
      (by rw [dropLast_snoc_getD hne]; exact h) with hle | ⟨q, S, hNeq, hq⟩
  · -- `N` stays within the good part: the first expansion already contains it
    refine ⟨1, le_rfl, ?_⟩
    have hsplit : M⟦1⟧ = M.dropLast := by
      rw [oper_gcopies 1 (by omega) hz hp, gcopies_eq_from,
        show (1 : ℕ) = 0 + 1 from rfl, gcopiesFrom_succ, gcopiesFrom_zero,
        List.append_nil, gcopy_zero, take_gcopy_zero L hz hp]
    rw [hsplit]
    exact hle
  · exact H hM hN L hz hNeq hq

/-- **Trio Bachmann cofinality, modulo the crux.** -/
theorem seqlex_cofinality_of_crux (H : TrioBadCrux) : SeqlexCofinality := by
  intro M N hM hN h
  by_cases hL : M.length - 1 = 0
  · exact seqlex_cof_short hL h
  · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0
    · exact seqlex_cof_zero (by omega) hz h
    · exact seqlex_cof_bad H hM hN (by omega) hz h

/-- Translate-side cofinality, modulo the crux. -/
theorem ts_cofinality_of_crux (H : TrioBadCrux) {M N : TrioSeq}
    (hM : ST_TS M) (hN : ST_TS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  ts_cofinality_of_seqlex (seqlex_cofinality_of_crux H) hM hN h

/-! ## Part 4 — 複写支配の道具（splice と分割） -/

/-- **Splice.**  A strictly smaller argument block stays smaller once the
tails are attached, provided the left tail re-opens at or below the block base
while every column of the right block is strictly above it. -/
theorem seqlex_splice : ∀ {A B : TrioSeq}, seqlex A B →
    ∀ {U : TrioSeq}, (U = [] ∨ ∀ x ∈ B, collt (U.headI) x) →
    ∀ (C : TrioSeq), seqlex (A ++ U) (B ++ C) := by
  intro A
  induction A with
  | nil =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rcases U with _ | ⟨u, U'⟩
      · simp
      · refine Or.inl ?_
        rcases hU with h' | h'
        · exact absurd h' (by simp)
        · simpa using h' b0 (by simp)
  | cons a A' ihA =>
    intro B h U hU C
    rcases B with _ | ⟨b0, B'⟩
    · exact absurd h (by simp)
    · rw [seqlex_cons_cons] at h
      rcases h with hp | ⟨rfl, hs⟩
      · exact Or.inl hp
      · refine Or.inr ⟨rfl, ihA hs ?_ C⟩
        rcases hU with h' | h'
        · exact Or.inl h'
        · exact Or.inr (fun x hx => h' x (List.mem_cons_of_mem _ hx))

/-- The block split at the base level. -/
theorem split_block {v0 : ℕ} {R Y : TrioSeq} (hRgt : ∀ x ∈ R, v0 < x.1)
    (hYhd : Y = [] ∨ ¬ v0 < (Y.headI).1) :
    (R ++ Y).takeWhile (fun q => v0 < q.1) = R ∧
    (R ++ Y).dropWhile (fun q => v0 < q.1) = Y := by
  have hR' : ∀ x ∈ R, (fun q : ℕ × ℕ × ℕ => decide (v0 < q.1)) x = true := by
    intro x hx
    simpa using hRgt x hx
  rcases hYhd with rfl | hY
  · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
      by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
  · rcases Y with _ | ⟨y, Y'⟩
    · exact ⟨by simpa using List.takeWhile_eq_self_iff.2 hR',
        by simpa using List.dropWhile_eq_nil_iff.2 hR'⟩
    · simp only [List.headI] at hY
      exact ⟨by rw [takeWhile_append_all hR']; simp [hY],
        by rw [dropWhile_append_all hR']; simp [hY]⟩

theorem copies_zero_succ (blk : TrioSeq) (m : ℕ) :
    copies 0 0 blk (m + 1) = copies 0 0 blk m ++ blk := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp [shiftr01]

/-- **Exact-copy domination (`d0 = d1 = 0`).**  The base-level remainder `Y`
after a block `blk = (v0,w1,w2) :: R` of a CNF standard shape is dominated by
finitely many verbatim copies of `blk`. -/
theorem copy_dom_zero : ∀ (d : ℕ) (Y : TrioSeq) (v0 w1 w2 : ℕ) (R : TrioSeq),
    Y.length ≤ d →
    blockok v0 ((v0, w1, w2) :: (R ++ Y)) →
    (∀ x ∈ R, v0 < x.1) →
    (Y = [] ∨ ¬ v0 < (Y.headI).1) →
    cnf (translate ((v0, w1, w2) :: (R ++ Y))) →
    ∃ m, 1 ≤ m ∧ sle Y (copies 0 0 ((v0, w1, w2) :: R) m) := by
  intro d
  induction d with
  | zero =>
    intro Y v0 w1 w2 R hlen _ _ _ _
    have hY : Y = [] := by
      cases Y with
      | nil => rfl
      | cons y Y' => simp at hlen
    subst hY
    exact ⟨1, le_rfl, Or.inr (by rw [copies_one]; simp)⟩
  | succ d ih =>
    intro Y v0 w1 w2 R hlen hbo hRgt hYhd hcnf
    rcases Y with _ | ⟨⟨y1, y2, y3⟩, Y'⟩
    · exact ⟨1, le_rfl, Or.inr (by rw [copies_one]; simp)⟩
    have hyv : y1 = v0 := by
      have h1 : v0 ≤ y1 := hbo.2.1 (y1, y2, y3) (by simp)
      have h2 : ¬ v0 < y1 := by
        rcases hYhd with h' | h'
        · exact absurd h' (by simp)
        · simpa using h'
      omega
    subst hyv
    set R' := Y'.takeWhile (fun q => y1 < q.1) with hR'def
    set Y'' := Y'.dropWhile (fun q => y1 < q.1) with hY''def
    have hY'split : R' ++ Y'' = Y' := List.takeWhile_append_dropWhile
    have hR'gt : ∀ x ∈ R', y1 < x.1 := by
      intro x hx
      have := List.mem_takeWhile_imp hx
      simpa using this
    have hY''hd : Y'' = [] ∨ ¬ y1 < (Y''.headI).1 := by
      rcases hd : Y'' with _ | ⟨z, Z⟩
      · exact Or.inl rfl
      · refine Or.inr ?_
        have h := List.head?_dropWhile_not
          (fun q : ℕ × ℕ × ℕ => decide (y1 < q.1)) Y'
        rw [← hY''def, hd] at h
        simpa using h
    have hTy : translate ((y1, y2, y3) :: Y')
        = P y2 y3 (translate R') (translate Y'') := by
      have he : ((y1, y2, y3) :: R') ++ Y'' = (y1, y2, y3) :: Y' := by
        rw [List.cons_append, hY'split]
      rw [← he]
      exact translate_block_append hR'gt hY''hd
    have hTall : translate ((y1, w1, w2) :: (R ++ ((y1, y2, y3) :: Y')))
        = P w1 w2 (translate R) (translate ((y1, y2, y3) :: Y')) := by
      have he : ((y1, w1, w2) :: R) ++ ((y1, y2, y3) :: Y')
          = (y1, w1, w2) :: (R ++ ((y1, y2, y3) :: Y')) := by
        rw [List.cons_append]
      rw [← he]
      exact translate_block_append hRgt (Or.inr (by simp))
    rw [hTall, hTy] at hcnf
    obtain ⟨cR, hsib, ctail⟩ := cnf_P_P.1 hcnf
    have hy2 : y2 < w1 ∨ (y2 = w1 ∧ y3 < w2) ∨ (y2 = w1 ∧ y3 = w2) := by
      rcases Nat.lt_trichotomy y2 w1 with h | h | h
      · exact Or.inl h
      · rcases Nat.lt_trichotomy y3 w2 with h' | h' | h'
        · exact Or.inr (Or.inl ⟨h, h'⟩)
        · exact Or.inr (Or.inr ⟨h, h'⟩)
        · exact absurd (olt_P_P.2 (Or.inr (Or.inl ⟨h.symm, h'⟩))) hsib
      · exact absurd (olt_P_P.2 (Or.inl h)) hsib
    rcases hy2 with hlt | ⟨he1, hlt⟩ | ⟨he1, he2⟩
    · refine ⟨1, le_rfl, Or.inr ?_⟩
      rw [copies_one]
      exact Or.inl (Or.inr ⟨rfl, Or.inl hlt⟩)
    · refine ⟨1, le_rfl, Or.inr ?_⟩
      rw [copies_one]
      exact Or.inl (Or.inr ⟨rfl, Or.inr ⟨he1, hlt⟩⟩)
    · subst he1
      subst he2
      have hnolt : ¬ (translate R <o translate R') := by
        intro hcon
        exact hsib (olt_P_P.2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hcon⟩))))
      have hsp := split_block hRgt hYhd
      have hboY : blockok y1 ((y1, y2, y3) :: Y') := by
        have := blockok_tail hbo
        rwa [hsp.2] at this
      have hboR : blockok (y1 + 1) R := by
        have := blockok_arg hbo
        rwa [hsp.1] at this
      have hboR' : blockok (y1 + 1) R' := blockok_arg hboY
      by_cases hRR : R' = R
      · have hYeq : (y1, y2, y3) :: Y' = ((y1, y2, y3) :: R) ++ Y'' := by
          rw [List.cons_append, ← hY'split, hRR]
        have hlen'' : Y''.length ≤ d := by
          have h1 : (R' ++ Y'').length = Y'.length := by rw [hY'split]
          simp only [List.length_append] at h1
          simp only [List.length_cons] at hlen
          omega
        have hbo'' : blockok y1 ((y1, y2, y3) :: (R ++ Y'')) := by
          rw [← List.cons_append, ← hYeq]
          exact hboY
        have hcnf'' : cnf (translate ((y1, y2, y3) :: (R ++ Y''))) := by
          rw [← List.cons_append, ← hYeq, hTy]
          exact ctail
        obtain ⟨m, hm, hsle⟩ := ih Y'' y1 y2 y3 R hlen'' hbo'' hRgt hY''hd hcnf''
        refine ⟨m + 1, by omega, ?_⟩
        rw [copies_succ_cons, shiftr01_zero, hYeq, ← List.cons_append]
        exact (sle_append_cancel _).2 hsle
      · have hslR : seqlex R' R := by
          rcases seqlex_total R' R with he | h | h
          · exact absurd he hRR
          · exact h
          · exact absurd (seqlex_imp_olt (y1 + 1) R R' hboR hboR' h) hnolt
        refine ⟨2, by omega, Or.inr ?_⟩
        rw [show (2 : ℕ) = 1 + 1 from rfl, copies_succ_cons, shiftr01_zero,
          copies_one]
        refine Or.inr ⟨rfl, ?_⟩
        rw [← hY'split]
        refine seqlex_splice hslR ?_ _
        rcases hY''hd with h | h
        · exact Or.inl h
        · refine Or.inr (fun x hx => ?_)
          have h1 := hRgt x hx
          exact Or.inl (by omega)

/-- **The `d0 = 0` crux.**  When the dropped column is `(v0+1, 0, 0)`, the
continuation of `N` below it re-opens at or below `v0` and is dominated by
finitely many verbatim copies of the block. -/
theorem crux_zero {G R S : TrioSeq} {v0 w1 w2 : ℕ} {q : ℕ × ℕ × ℕ}
    (hN : ST_TS ((G ++ ((v0, w1, w2) :: R)) ++ q :: S))
    (hRgt : ∀ x ∈ R, v0 < x.1)
    (hq : collt q (v0 + 1, 0, 0)) :
    ∃ m, 1 ≤ m ∧ sle (q :: S) (copies 0 0 ((v0, w1, w2) :: R) m) := by
  have hqv : q.1 ≤ v0 := by
    rcases hq with h | ⟨h1, h | ⟨h2, h3⟩⟩
    · have h' : q.1 < v0 + 1 := h
      omega
    · have h' : q.2.1 < 0 := h
      omega
    · have h' : q.2.2 < 0 := h3
      omega
  rcases Nat.lt_or_ge q.1 v0 with hlt | hge
  · exact ⟨1, le_rfl, Or.inr (by
      rw [copies_one]
      exact Or.inl (Or.inl (by omega)))⟩
  have hqv0 : q.1 = v0 := by omega
  set Y := (q :: S).takeWhile (fun p => v0 ≤ p.1) with hYdef
  set V := (q :: S).dropWhile (fun p => v0 ≤ p.1) with hVdef
  have hYV : Y ++ V = q :: S := List.takeWhile_append_dropWhile
  have hYcons : Y = q :: S.takeWhile (fun p => v0 ≤ p.1) := by
    rw [hYdef, List.takeWhile_cons_of_pos (by simpa using hqv0.ge)]
  have hYge : ∀ x ∈ Y, v0 ≤ x.1 := by
    intro x hx
    have := List.mem_takeWhile_imp hx
    simpa using this
  have hVhd : V = [] ∨ ∃ z Z, V = z :: Z ∧ z.1 < v0 := by
    rcases hd : V with _ | ⟨z, Z⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨z, Z, rfl, ?_⟩
      have h := List.head?_dropWhile_not
        (fun p : ℕ × ℕ × ℕ => decide (v0 ≤ p.1)) (q :: S)
      rw [← hVdef, hd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 ≤ z.1) := by simpa using h
      omega
  have hNsplit : (G ++ ((v0, w1, w2) :: R)) ++ q :: S
      = (G ++ (((v0, w1, w2) :: R) ++ Y)) ++ V := by
    rw [← hYV]
    simp
  have hstN : steps1 ((G ++ ((v0, w1, w2) :: R)) ++ q :: S) :=
    (blockok_ST_TS hN).2.2
  have hstBY : steps1 (((v0, w1, w2) :: R) ++ Y) := by
    rw [hNsplit] at hstN
    exact (steps1_append.1 (steps1_append.1 hstN).1).2.1
  have hallBY : ∀ x ∈ ((v0, w1, w2) :: R) ++ Y, v0 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact (hRgt x hx).le
    · exact hYge x hx
  have hbo : blockok v0 (((v0, w1, w2) :: R) ++ Y) := ⟨by intro _; rfl, hallBY, hstBY⟩
  have hcnfN : cnf (translate ((G ++ ((v0, w1, w2) :: R)) ++ q :: S)) :=
    cnf_ST_TS hN
  have hcnfW : cnf (translate ((v0, w1, w2) :: (R ++ Y))) := by
    have h1 : cnf (translate ((G ++ (((v0, w1, w2) :: R) ++ Y)) ++ V)) := by
      rw [← hNsplit]
      exact hcnfN
    have h2 : cnf (translate (G ++ (((v0, w1, w2) :: R) ++ Y))) := by
      have := cnf_take h1 (G ++ (((v0, w1, w2) :: R) ++ Y)).length
      rwa [List.take_left] at this
    have h3 : cnf (translate (G ++ ((v0, w1, w2) :: (R ++ Y)))) := by
      rwa [List.cons_append] at h2
    exact cnf_tail (t := (v0, w1, w2)) (T' := R ++ Y)
      (fun x hx => hallBY x (by
        rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
        · exact List.mem_append_right _ h)) G h3
  obtain ⟨m, hm, hsle⟩ := copy_dom_zero Y.length Y v0 w1 w2 R le_rfl
    (by rwa [List.cons_append] at hbo) hRgt
    (Or.inr (by
      rw [hYcons]
      show ¬ v0 < q.1
      omega)) hcnfW
  refine ⟨m + 1, by omega, Or.inr ?_⟩
  rw [← hYV, copies_zero_succ]
  rcases hsle with heq | hlt
  · rw [← heq, seqlex_append_cancel]
    rcases hVhd with hV | ⟨z, Z, hV, hz⟩
    · rw [hV]
      simp
    · rw [hV]
      exact Or.inl (Or.inl (by omega))
  · refine seqlex_splice hlt ?_ _
    rcases hVhd with hV | ⟨z, Z, hV, hz⟩
    · exact Or.inl hV
    · refine Or.inr (fun x hx => ?_)
      have := copies_v0_le (fun y hy => (hRgt y hy).le) 0 0 m x hx
      rw [hV]
      refine Or.inl ?_
      simp only [List.headI]
      omega

/-- With both shifts zero, every guarded copy is the plain segment. -/
theorem gcopy_zero_shift (M : TrioSeq) (r L k : ℕ) :
    gcopy M r L 0 0 k = seg M r L := by
  unfold gcopy seg
  refine List.map_congr_left ?_
  intro j hj
  simp only [Nat.mul_zero, ite_self, Nat.add_zero]

/-- With both shifts zero, the guarded copies are the verbatim copies of the
segment (in the `copies` form over the cons-shape of the block). -/
theorem gcopiesFrom_zero_shift (M : TrioSeq) (r L k0 : ℕ) :
    ∀ m, gcopiesFrom M r L 0 0 k0 m
      = copies 0 0 (seg M r L) m := by
  intro m
  induction m generalizing k0 with
  | zero => rfl
  | succ m ih =>
    rw [gcopiesFrom_succ, gcopy_zero_shift, ih (k0 + 1), copies_succ_front,
      shiftr01_zero]

/-! ## Part 5 — 上昇 crux への還元（srow = 0 の枝は crux_zero で潰す） -/

/-- **The ascending crux**: the bad branch with a positive search row. -/
def TrioAscCrux : Prop :=
  ∀ {M N : TrioSeq} {q : ℕ × ℕ × ℕ} {S : TrioSeq},
    ST_TS M → ST_TS N → 1 < M.length →
    ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) →
    0 < srow M (M.length - 1) →
    N = M.dropLast ++ q :: S →
    collt q (M.getD (M.length - 1) (0, 0, 0)) →
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧)

theorem badCrux_of_asc (H : TrioAscCrux) : TrioBadCrux := by
  intro M N q S hM hN L hz hNeq hq
  by_cases hsr : 0 < srow M (M.length - 1)
  · exact H hM hN L hz hsr hNeq hq
  · -- `srow = 0`: the dropped column is `(v0+1, 0, 0)`
    push Not at hsr
    have hsr0 : srow M (M.length - 1) = 0 := by omega
    have hp := hasParent_last_ST_TS hM (by omega) hz
    have np := parent_nextR hp
    have j0lt : parent M (srow M (M.length - 1)) (M.length - 1)
        < M.length - 1 := nextR_index_lt np
    have chain := nextR_chain0 np
    have iv : ∀ k, parent M (srow M (M.length - 1)) (M.length - 1) < k →
        k ≤ M.length - 1 →
        entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
          < entry M 0 k :=
      fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
    -- the last-column pinning
    have hlp2 : entry M 2 (M.length - 1) = 0 := by
      by_contra hcon
      push Not at hcon
      have : srow M (M.length - 1) = 2 := by
        unfold srow
        rw [if_pos (by omega)]
      omega
    have hlp1 : entry M 1 (M.length - 1) = 0 := by
      by_contra hcon
      push Not at hcon
      have : srow M (M.length - 1) = 1 := by
        unfold srow
        rw [if_neg (by omega), if_pos (by omega)]
      omega
    have np0 : nextrel0 M (parent M (srow M (M.length - 1)) (M.length - 1))
        (M.length - 1) := by
      have np' := np
      unfold nextR at np'
      rw [if_pos hsr0] at np'
      exact np'
    set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
    set L' := M.length - 1 - j0 with hL'
    have hL'pos : 0 < L' := by omega
    have hj0b : j0 < M.length := by omega
    -- `e0 lp = e0 j0 + 1` via steps1 and the window
    have hst : steps1 M := (blockok_ST_TS hM).2.2
    have hstep := steps1_iff.1 hst j0 (by omega)
    have hlp0 : entry M 0 (M.length - 1) = entry M 0 j0 + 1 := by
      have hup : entry M 0 j0 < entry M 0 (M.length - 1) := iv _ j0lt le_rfl
      rcases Nat.eq_or_lt_of_le (show j0 + 1 ≤ M.length - 1 by omega) with he | hlt
      · have e1 : entry M 0 j0 = (M.getD j0 (0, 0, 0)).1 := rfl
        have e2 : entry M 0 (M.length - 1)
          = (M.getD (M.length - 1) (0, 0, 0)).1 := rfl
        have e3 : (M.getD (j0 + 1) (0, 0, 0)).1
            = (M.getD (M.length - 1) (0, 0, 0)).1 := by
          rw [he]
        omega
      · have hwin := np0.2.2.2.2 (j0 + 1) ⟨by omega, hlt⟩
        have e0 : entry M 0 (j0 + 1) = (M.getD (j0 + 1) (0, 0, 0)).1 := rfl
        have e1 : entry M 0 j0 = (M.getD j0 (0, 0, 0)).1 := rfl
        omega
    have hlpe : M.getD (M.length - 1) (0, 0, 0) = (entry M 0 j0 + 1, 0, 0) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show (M.getD (M.length - 1) (0, 0, 0)).1 = entry M 0 j0 + 1
        exact hlp0
      · exact hlp1
      · exact hlp2
    -- the list form of the good part
    have hsegL : seg M j0 L' = (entry M 0 j0, entry M 1 j0, entry M 2 j0)
        :: seg M (j0 + 1) (L' - 1) := by
      obtain ⟨l', hle⟩ : ∃ l', L' = l' + 1 := ⟨L' - 1, by omega⟩
      rw [hle, seg_cons, Nat.add_sub_cancel]
    have hdl : M.take j0 ++ seg M j0 L' = M.dropLast :=
      take_gcopy_zero L hz hp
    have hRgt : ∀ x ∈ seg M (j0 + 1) (L' - 1), entry M 0 j0 < x.1 := by
      intro x hx
      unfold seg at hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hjb := List.mem_range'_1.1 hj
      exact iv j (by omega) (by omega)
    -- apply the `d0 = 0` crux
    have hNst : ST_TS ((M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
          :: seg M (j0 + 1) (L' - 1))) ++ q :: S) := by
      have he2 : M.take j0 ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
          :: seg M (j0 + 1) (L' - 1)) = M.dropLast := by
        rw [← hsegL, hdl]
      rw [he2, ← hNeq]
      exact hN
    have hqz : collt q (entry M 0 j0 + 1, 0, 0) := by
      rw [hlpe] at hq
      exact hq
    obtain ⟨m, hm, hsle⟩ := crux_zero hNst hRgt hqz
    -- assemble
    refine ⟨m + 1, by omega, ?_⟩
    have hd0z : (if 0 < srow M (M.length - 1)
        then entry M 0 (M.length - 1) - entry M 0 j0 else 0) = 0 := by
      rw [if_neg (by omega)]
    have hd1z : (if 1 < srow M (M.length - 1)
        then entry M 1 (M.length - 1) - entry M 1 j0 else 0) = 0 := by
      rw [if_neg (by omega)]
    have hMn : M⟦m + 1⟧ = M.dropLast
        ++ copies 0 0 (seg M j0 L') m := by
      rw [oper_gcopies (m + 1) (by omega) hz hp, ← hj0, ← hL', hd0z, hd1z,
        gcopies_eq_from, gcopiesFrom_succ, gcopy_zero, gcopiesFrom_zero_shift,
        ← List.append_assoc, hdl]
    rw [hMn, hNeq]
    refine (sle_append_cancel _).2 ?_
    rw [hsegL]
    exact hsle

/-- With a zero row-1 lift every guarded copy is the uniformly shifted
segment. -/
theorem gcopy_d1zero (M : TrioSeq) (r L d0 k : ℕ) :
    gcopy M r L d0 0 k = shiftr01 (k * d0) 0 (seg M r L) := by
  unfold gcopy seg shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro j hj
  simp only [Function.comp_apply, Nat.mul_zero, ite_self, Nat.add_zero]

/-- The tail of a `d1 = 0` tower is one further uniform shift of the copies. -/
theorem gcopiesFrom_d1zero (M : TrioSeq) (r L d0 : ℕ) :
    ∀ m k0, gcopiesFrom M r L d0 0 (k0 + 1) m
      = shiftr01 d0 0 (shiftr01 (k0 * d0) 0 (copies d0 0 (seg M r L) m)) := by
  intro m
  induction m with
  | zero =>
    intro k0
    rw [gcopiesFrom_zero, copies_zero]
    rfl
  | succ m ih =>
    intro k0
    rw [gcopiesFrom_succ, ih (k0 + 1), gcopy_d1zero, copies_succ_front]
    unfold shiftr01
    simp only [List.map_append, List.map_map]
    congr 1
    · refine List.map_congr_left ?_
      intro p hp
      have h1 : (k0 + 1) * d0 = k0 * d0 + d0 := Nat.succ_mul k0 d0
      simp only [Function.comp_apply, Prod.mk.injEq, and_true]
      omega
    · refine List.map_congr_left ?_
      intro p hp
      have h1 : (k0 + 1) * d0 = k0 * d0 + d0 := Nat.succ_mul k0 d0
      simp only [Function.comp_apply, Prod.mk.injEq, and_true]
      omega

end Googology.Trans.BMS.TrioCof
