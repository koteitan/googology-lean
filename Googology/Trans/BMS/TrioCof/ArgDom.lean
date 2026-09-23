/-
Ported verbatim from koteitan/trio, `lean/ArgDom.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/ArgDom.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
ArgDom.lean: 引数支配（ホスト非依存の共終性核）。

核の比較器は**心材シフト** `hshift w1 e f`: 行 0 は一様に `+e`、行 1 は
「木の経路上で行 1 が `w1` を超え続ける心材」でのみ `+f`（遮断された
部分木は行 0 のみシフト）。ホスト内では経路補題によりガード付き写像
`(e0 j + e, e1 j + [le1 N r j]·f, e2 j)` と一致する。
-/
import Googology.Trans.BMS.TrioCof.Cofinality
import Googology.Trans.BMS.TrioCof.Zjump

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-- The heartwood shift: row 0 uniformly `+e`; row 1 `+f` on the heartwood
(the tree region reachable through columns with row 1 above `w1`). -/
def hshift (w1 e f : ℕ) : TrioSeq → TrioSeq
  | [] => []
  | p :: rest =>
      if w1 < p.2.1 then
        (p.1 + e, p.2.1 + f, p.2.2)
          :: (hshift w1 e f (rest.takeWhile fun q => p.1 < q.1)
              ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
      else
        (p.1 + e, p.2.1, p.2.2)
          :: (shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
              ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
  termination_by M => M.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

@[simp] theorem hshift_nil (w1 e f : ℕ) : hshift w1 e f [] = [] := by
  rw [hshift]

theorem hshift_cons (w1 e f : ℕ) (p : ℕ × ℕ × ℕ) (rest : TrioSeq) :
    hshift w1 e f (p :: rest)
      = if w1 < p.2.1 then
          (p.1 + e, p.2.1 + f, p.2.2)
            :: (hshift w1 e f (rest.takeWhile fun q => p.1 < q.1)
                ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1))
        else
          (p.1 + e, p.2.1, p.2.2)
            :: (shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
                ++ hshift w1 e f (rest.dropWhile fun q => p.1 < q.1)) := by
  rw [hshift]

/-- **The host bridge**: inside a host `M`, the heartwood shift of a sibling
forest `[a, a+l)` under a guarded tree parent `pa` is the guarded map. -/
theorem hshift_gseg {M : TrioSeq} {r e f : ℕ} :
    ∀ (l : ℕ), ∀ {a pa : ℕ}, le1 M r pa → pa < a → a + l ≤ M.length →
      (∀ j, a ≤ j → j < a + l → entry M 0 pa < entry M 0 j) →
      (∀ j, pa < j → j < a → entry M 0 a ≤ entry M 0 j) →
      (List.range' a l).map (fun j =>
          ((entry M 0 j + e,
            entry M 1 j + (if le1 M r j then f else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = hshift (entry M 1 r) e f ((List.range' a l).map fun j =>
            ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l IH =>
    intro a pa hpa ha hlen hup hpre
    rcases l with - | l
    · show ([] : TrioSeq) = hshift _ e f []
      rw [hshift_nil]
    have hedge : nextrel0 M pa a := by
      refine ⟨by omega, by omega, ha, hup a le_rfl (by omega), ?_⟩
      intro x ⟨hx1, hx2⟩
      exact hpre x hx1 hx2
    have hguard : le1 M r a ↔ entry M 1 r < entry M 1 a := le1_step hpa hedge
    set q : ℕ → Bool := fun j => decide (entry M 0 a < entry M 0 j) with hqdef
    obtain ⟨m, hm, ht, hd, hall, hend⟩ := range'_split_takeWhile q l (a + 1)
    have hqs : ((fun x : ℕ × ℕ × ℕ => decide (entry M 0 a < x.1))
          ∘ fun j => ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) = q := by
      funext j
      simp only [Function.comp_apply, hqdef]
    -- unfold both sides one step
    simp only [List.range'_succ, List.map_cons]
    rw [hshift_cons]
    simp only [List.takeWhile_map, List.dropWhile_map, hqs, ht, hd]
    have hlsplit : List.range' (a + 1) l
        = List.range' (a + 1) m ++ List.range' (a + 1 + m) (l - m) := by
      rw [← ht, ← hd, List.takeWhile_append_dropWhile]
    rw [hlsplit, List.map_append]
    -- the tail recursion is common to both branches
    have htail : (List.range' (a + 1 + m) (l - m)).map (fun j =>
          ((entry M 0 j + e,
            entry M 1 j + (if le1 M r j then f else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = hshift (entry M 1 r) e f ((List.range' (a + 1 + m) (l - m)).map fun j =>
            ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
      rcases Nat.eq_or_lt_of_le hm with rfl | hmL
      · rw [Nat.sub_self]
        show ([] : TrioSeq) = hshift _ e f []
        rw [hshift_nil]
      · have hqe := hend hmL
        have he0 : entry M 0 (a + 1 + m) ≤ entry M 0 a := by
          have : q (a + 1 + m) = false := hqe
          simp only [hqdef, decide_eq_false_iff_not, Nat.not_lt] at this
          exact this
        refine IH (l - m) (by omega) hpa (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          exact hup j (by omega) (by omega)
        · intro j h1 h2
          rcases Nat.lt_or_ge j a with hja | hja
          · exact le_trans he0 (hpre j h1 hja)
          · rcases Nat.eq_or_lt_of_le hja with rfl | hja'
            · exact he0
            · have := hall j (by omega) (by omega)
              simp only [hqdef, decide_eq_true_eq] at this
              exact le_trans he0 this.le
    by_cases hthr : entry M 1 r < entry M 1 a
    · rw [if_pos hthr, if_pos (hguard.2 hthr)]
      have hsub : (List.range' (a + 1) m).map (fun j =>
            ((entry M 0 j + e,
              entry M 1 j + (if le1 M r j then f else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
          = hshift (entry M 1 r) e f ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
        refine IH m (by omega) (hguard.2 hthr) (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          have := hall j h1 (by omega)
          simp only [hqdef, decide_eq_true_eq] at this
          exact this
        · intro j h1 h2
          omega
      rw [hsub, htail]
    · rw [if_neg hthr, if_neg (fun h => hthr (hguard.1 h)), Nat.add_zero]
      have hnog : ∀ j, a + 1 ≤ j → j < a + 1 + m → ¬ le1 M r j := by
        intro j h1 h2 hle1
        refine hthr (hguard.1 ?_)
        refine le1_of_le1_subtree (by omega)
          ((rtg1_to_rtg0 hpa.2.2).tail hedge) (by omega) ?_ hle1
        intro x hx1 hx2
        have := hall x (by omega) (by omega)
        simp only [hqdef, decide_eq_true_eq] at this
        exact this
      have hsub : (List.range' (a + 1) m).map (fun j =>
            ((entry M 0 j + e,
              entry M 1 j + (if le1 M r j then f else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
          = shiftr01 e 0 ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
        unfold shiftr01
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro j hj
        have hjb := List.mem_range'_1.1 hj
        simp only [Function.comp_apply]
        rw [if_neg (hnog j hjb.1 (by omega))]
      rw [hsub, htail]

/-! ## seqlex の道具 -/

theorem seqlex_of_sle_not_prefix : ∀ {W X Y : TrioSeq}, sle X (W ++ Y) →
    (∀ X', X ≠ W ++ X') → ∀ (Y' : TrioSeq), seqlex X (W ++ Y') := by
  intro W
  induction W with
  | nil =>
    intro X Y _ hnp _
    exact absurd (by simp : X = [] ++ X) (hnp X)
  | cons w W' ih =>
    intro X Y h hnp Y'
    rcases X with _ | ⟨x, X''⟩
    · simp
    · rw [List.cons_append] at h ⊢
      rcases h with he | hs
      · exact absurd he (by
          have := hnp Y
          rw [List.cons_append] at this
          exact this)
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inl hp
        · refine Or.inr ⟨rfl, ih (Y := Y) (Or.inr hs') ?_ Y'⟩
          intro Z hZ
          exact hnp Z (by rw [hZ, List.cons_append])

/-- A comparison that is already over by the end of `P` does not see `Y`. -/
theorem sle_take_of_short : ∀ {P X Y : TrioSeq}, sle X (P ++ Y) →
    X.length ≤ P.length → sle X P := by
  intro P
  induction P with
  | nil =>
    intro X Y _ hlen
    have : X = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact Or.inl this
  | cons p P' ih =>
    intro X Y h hlen
    rcases X with _ | ⟨x, X''⟩
    · exact Or.inr (by simp)
    · simp only [List.length_cons] at hlen
      rw [List.cons_append] at h
      rcases h with he | hs
      · have hx : x = p := by simpa using congrArg List.headI he
        have hX'' : X'' = P' ++ Y := by simpa using congrArg List.tail he
        have hY : Y = [] := by
          have : X''.length = P'.length + Y.length := by
            rw [hX'']
            simp
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [hY, List.append_nil] at hX''
        exact Or.inl (by rw [hx, hX''])
      · rw [seqlex_cons_cons] at hs
        rcases hs with hp | ⟨rfl, hs'⟩
        · exact Or.inr (Or.inl hp)
        · rcases ih (Or.inr hs') (by omega) with he' | hs''
          · exact Or.inl (by rw [he'])
          · exact Or.inr (Or.inr ⟨rfl, hs''⟩)

/-- Truncating the smaller side on the right keeps it below. -/
theorem sle_of_append_left {X Y W : TrioSeq} (h : sle (X ++ Y) W) : sle X W := by
  refine sle_trans ?_ h
  rcases Y with _ | ⟨y, Y'⟩
  · exact Or.inl (by simp)
  · exact Or.inr (seqlex_prefix (by simp) X)

/-! ## 統一核の定義 -/

/-- `hshift` with a zero row-1 lift is the uniform row-0 shift. -/
theorem hshift_f0 (w1 e : ℕ) : ∀ A : TrioSeq, hshift w1 e 0 A = shiftr01 e 0 A
  | [] => by
    rw [hshift_nil]
    rfl
  | p :: rest => by
    rw [hshift_cons]
    have h1 := hshift_f0 w1 e (rest.takeWhile fun q => p.1 < q.1)
    have h2 := hshift_f0 w1 e (rest.dropWhile fun q => p.1 < q.1)
    have hsplit : shiftr01 e 0 rest
        = shiftr01 e 0 (rest.takeWhile fun q => p.1 < q.1)
          ++ shiftr01 e 0 (rest.dropWhile fun q => p.1 < q.1) := by
      unfold shiftr01
      rw [← List.map_append, List.takeWhile_append_dropWhile]
    split_ifs with h
    · rw [h1, h2, shiftr01_cons, ← hsplit, Nat.add_zero]
    · rw [h2, shiftr01_cons, ← hsplit, Nat.add_zero]
  termination_by A => A.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

/-- Right-visible columns of `A` below level `L` carry row 1 at least `w`. -/
def SpineOK (A : TrioSeq) (L w : ℕ) : Prop :=
  ∀ (U V : TrioSeq) (x : ℕ × ℕ × ℕ), A = U ++ x :: V → x.1 < L →
    (∀ y ∈ V, x.1 < y.1) → w ≤ x.2.1

/-- **The host-free core of trio Bachmann cofinality** (probe: 57549
instances, 0 violations).  Two columns with the *same* label rows `(w1+·, z)`
at depths `u` and `u+e`, row-1 siblings via `SpineOK`; the deeper argument
`B` is dominated by the heartwood shift of the shallower argument. -/
def ArgDomCore : Prop :=
  ∀ {X A1 B A2 Z : TrioSeq} {u w1 z e f : ℕ},
    ST_TS ((X ++ (u, w1, z) :: (A1 ++ (u + e, w1 + f, z) :: (B ++ A2))) ++ Z) →
    0 < e → (f = 0 ∨ z = 0) →
    (∀ x ∈ A1, u < x.1) →
    (∀ x ∈ B, u + e < x.1) →
    (∀ x ∈ A2, u < x.1) →
    (A2 = [] ∨ (A2.headI).1 ≤ u + e) →
    (Z = [] ∨ (Z.headI).1 ≤ u) →
    SpineOK A1 (u + e) (w1 + 1) →
    sle B (hshift w1 e f (A1 ++ (u + e, w1 + f, z) :: (B ++ A2)))

/-! ## 一様シフトの道具（`i1 = 1`, `f = 0` の鎖） -/

theorem shiftr01_append (d0 d1 : ℕ) (A B : TrioSeq) :
    shiftr01 d0 d1 (A ++ B) = shiftr01 d0 d1 A ++ shiftr01 d0 d1 B :=
  List.map_append

theorem shiftr01_injective (d0 d1 : ℕ) {X Y : TrioSeq}
    (h : shiftr01 d0 d1 X = shiftr01 d0 d1 Y) : X = Y := by
  induction X generalizing Y with
  | nil =>
    rcases Y with - | ⟨y, Y'⟩
    · rfl
    · exact absurd h (by simp [shiftr01])
  | cons x X' ih =>
    rcases Y with - | ⟨y, Y'⟩
    · exact absurd h (by simp [shiftr01])
    · rw [shiftr01_cons, shiftr01_cons] at h
      obtain ⟨h1, h2⟩ := List.cons_eq_cons.1 h
      have hxy : x = y := by
        obtain ⟨x1, x2, x3⟩ := x
        obtain ⟨y1, y2, y3⟩ := y
        simp only [Prod.mk.injEq] at h1 ⊢
        omega
      rw [hxy, ih h2]

theorem collt_shiftr01 (d0 d1 : ℕ) {p q : ℕ × ℕ × ℕ} :
    collt ((p.1 + d0, p.2.1 + d1, p.2.2)) ((q.1 + d0, q.2.1 + d1, q.2.2))
      ↔ collt p q := by
  unfold collt
  dsimp only
  omega

theorem seqlex_shiftr01 (d0 d1 : ℕ) : ∀ {X Y : TrioSeq},
    seqlex (shiftr01 d0 d1 X) (shiftr01 d0 d1 Y) ↔ seqlex X Y := by
  intro X
  induction X with
  | nil =>
    intro Y
    rcases Y with - | ⟨y, Y'⟩
    · simp [shiftr01]
    · simp [shiftr01]
  | cons x X' ih =>
    intro Y
    rcases Y with - | ⟨y, Y'⟩
    · simp [shiftr01]
    · rw [shiftr01_cons, shiftr01_cons, seqlex_cons_cons, seqlex_cons_cons]
      constructor
      · rintro (hp | ⟨he, hs⟩)
        · exact Or.inl ((collt_shiftr01 d0 d1).1 hp)
        · refine Or.inr ⟨?_, ih.1 hs⟩
          obtain ⟨x1, x2, x3⟩ := x
          obtain ⟨y1, y2, y3⟩ := y
          simp only [Prod.mk.injEq] at he ⊢
          omega
      · rintro (hp | ⟨rfl, hs⟩)
        · exact Or.inl ((collt_shiftr01 d0 d1).2 hp)
        · exact Or.inr ⟨rfl, ih.2 hs⟩

theorem sle_shiftr01 (d0 d1 : ℕ) {X Y : TrioSeq} :
    sle (shiftr01 d0 d1 X) (shiftr01 d0 d1 Y) ↔ sle X Y := by
  unfold sle
  rw [seqlex_shiftr01]
  constructor
  · rintro (he | hs)
    · exact Or.inl (shiftr01_injective d0 d1 he)
    · exact Or.inr hs
  · rintro (rfl | hs)
    · exact Or.inl rfl
    · exact Or.inr hs

/-- `shiftr01` commutes with the copy tower. -/
theorem shiftr01_copies (d0 d1 : ℕ) (blk : TrioSeq) (n : ℕ) :
    shiftr01 d0 d1 (copies d0 d1 blk n) = copies d0 d1 (shiftr01 d0 d1 blk) n := by
  unfold copies shiftr01
  rw [List.map_flatMap]
  congr 1
  funext k
  rw [List.map_map, List.map_map]
  congr 1
  funext p
  dsimp only [Function.comp_apply]
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega, trivial⟩

/-- **The peel** (uniform case): a self-referential bound unfolds into the
copy tower. -/
theorem peel_aux (d w z : ℕ) : ∀ (n : ℕ) (X Q A2 : TrioSeq) (a : ℕ),
    X.length ≤ n →
    sle X (Q ++ (a, w, z) :: shiftr01 d 0 (X ++ A2)) →
    ∃ m, sle X (Q ++ copies d 0 ((a, w, z) :: shiftr01 d 0 Q) m) := by
  intro n
  induction n with
  | zero =>
    intro X Q A2 a hlen _
    have hX : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hX
    refine ⟨0, ?_⟩
    rw [copies_zero, List.append_nil]
    rcases Q with _ | ⟨q, Q'⟩
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  | succ n ih =>
    intro X Q A2 a hlen h
    by_cases hpre : ∃ X', X = Q ++ (a, w, z) :: X'
    · obtain ⟨X', rfl⟩ := hpre
      have hstep : sle X' (shiftr01 d 0 Q
          ++ (a + d, w, z) :: shiftr01 d 0 (X' ++ A2)) := by
        have h' : sle (Q ++ (a, w, z) :: X')
            (Q ++ (a, w, z) :: shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)) := h
        have hc : sle ((a, w, z) :: X')
            ((a, w, z) :: shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)) :=
          (sle_append_cancel Q).1 h'
        have hc2 : sle X' (shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)) :=
          (sle_append_cancel [(a, w, z)]).1 (by simpa using hc)
        have hrw : shiftr01 d 0 ((Q ++ (a, w, z) :: X') ++ A2)
            = shiftr01 d 0 Q ++ (a + d, w, z) :: shiftr01 d 0 (X' ++ A2) := by
          rw [List.append_assoc, List.cons_append, shiftr01_append, shiftr01_cons]
          rfl
        rwa [hrw] at hc2
      have hlen' : X'.length ≤ n := by
        simp only [List.length_append, List.length_cons] at hlen
        omega
      obtain ⟨m, hm⟩ := ih X' (shiftr01 d 0 Q) A2 (a + d) hlen' hstep
      refine ⟨m + 1, ?_⟩
      have hrw : Q ++ copies d 0 ((a, w, z) :: shiftr01 d 0 Q) (m + 1)
          = (Q ++ [(a, w, z)]) ++
              (shiftr01 d 0 Q
                ++ copies d 0 ((a + d, w, z)
                    :: shiftr01 d 0 (shiftr01 d 0 Q)) m) := by
        rw [copies_succ_front, shiftr01_copies, shiftr01_cons]
        simp
      rw [hrw]
      have he : Q ++ (a, w, z) :: X' = (Q ++ [(a, w, z)]) ++ X' := by simp
      rw [he]
      exact (sle_append_cancel _).2 hm
    · refine ⟨1, Or.inr ?_⟩
      rw [copies_one]
      have hW : sle X ((Q ++ [(a, w, z)]) ++ shiftr01 d 0 (X ++ A2)) := by
        simpa using h
      have hnp : ∀ X', X ≠ (Q ++ [(a, w, z)]) ++ X' := by
        intro X' hX'
        exact hpre ⟨X', by rw [hX']; simp⟩
      have := seqlex_of_sle_not_prefix hW hnp (shiftr01 d 0 Q)
      simpa using this

/-! ## スパイン条件の導出 -/

theorem getD_append_right' (A B : TrioSeq) (i : ℕ) :
    (A ++ B).getD (A.length + i) (0, 0, 0) = B.getD i (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

/-- **The spine condition from a row-1 ancestry to the dropped column.**
Right-visible columns of `R` are row-0 ancestors of the dropped column
(window pivot), hence chain nodes of the `le1`-ancestry; the path lemma
bounds their row 1 strictly above the root. -/
theorem spineOK_of_le1 {G R : TrioSeq} {v0 w1 w2 : ℕ} {lp : ℕ × ℕ × ℕ}
    (hle1 : le1 ((G ++ ((v0, w1, w2) :: R)) ++ [lp]) G.length
      (G ++ ((v0, w1, w2) :: R)).length) :
    SpineOK R lp.1 w1 := by
  intro U V x hR hxlt hV
  set M := (G ++ ((v0, w1, w2) :: R)) ++ [lp] with hMdef
  set A := G ++ ((v0, w1, w2) :: U) with hAdef
  have hMeq : M = A ++ (x :: (V ++ [lp])) := by
    rw [hMdef, hAdef, hR]
    simp
  have hAlen : A.length = G.length + 1 + U.length := by
    rw [hAdef]
    simp
    omega
  have hj1 : (G ++ ((v0, w1, w2) :: R)).length = A.length + 1 + V.length := by
    rw [hR, hAlen]
    simp
    omega
  have hMlen : M.length = (G ++ ((v0, w1, w2) :: R)).length + 1 := by
    rw [hMdef]
    simp
    omega
  have hgx : M.getD A.length (0, 0, 0) = x := by
    have h := getD_append_right' A (x :: (V ++ [lp])) 0
    rw [Nat.add_zero] at h
    rw [hMeq]
    exact h
  -- window: everything after `x` up to the dropped column is strictly above it
  have hwin : ∀ y, A.length < y → y ≤ (G ++ ((v0, w1, w2) :: R)).length →
      entry M 0 A.length < entry M 0 y := by
    intro y hy1 hy2
    obtain ⟨t, rfl⟩ : ∃ t, y = A.length + (t + 1) := ⟨y - A.length - 1, by omega⟩
    have hgy : M.getD (A.length + (t + 1)) (0, 0, 0)
        = (V ++ [lp]).getD t (0, 0, 0) := by
      conv_lhs => rw [hMeq]
      rw [getD_append_right' A (x :: (V ++ [lp])) (t + 1), List.getD_cons_succ]
    show (M.getD A.length (0, 0, 0)).1 < (M.getD (A.length + (t + 1)) (0, 0, 0)).1
    rw [hgx, hgy]
    rcases Nat.lt_or_ge t V.length with ht | ht
    · have hmem : (V ++ [lp]).getD t (0, 0, 0) ∈ V := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht,
          List.getElem?_eq_getElem ht]
        exact List.getElem_mem _
      exact hV _ hmem
    · have htv : t = V.length := by omega
      subst htv
      have he : (V ++ [lp]).getD V.length (0, 0, 0) = lp := by
        have h := getD_append_right' V [lp] 0
        rw [Nat.add_zero] at h
        exact h
      rw [he]
      exact hxlt
  -- `x` is a row-0 chain node of the ancestry
  have hxrtg : Relation.ReflTransGen (nextrel0 M) A.length
      (G ++ ((v0, w1, w2) :: R)).length := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l hl1 hl2
    exact hwin l hl1 hl2
  have hrootx : Relation.ReflTransGen (nextrel0 M) G.length A.length :=
    rtg0_comparable (rtg1_to_rtg0 hle1.2.2) hxrtg (by omega)
  have hbound := le1_chain_window hle1.2.2 A.length hrootx hxrtg (by omega)
  -- read the two row-1 values
  have hgr : M.getD G.length (0, 0, 0) = (v0, w1, w2) := by
    have h := getD_append_right' G (((v0, w1, w2) :: R) ++ [lp]) 0
    rw [Nat.add_zero] at h
    rw [hMdef, List.append_assoc]
    rw [h]
    rfl
  have e1 : entry M 1 G.length = w1 := by
    show (M.getD G.length (0, 0, 0)).2.1 = w1
    rw [hgr]
  have e2 : entry M 1 A.length = x.2.1 := by
    show (M.getD A.length (0, 0, 0)).2.1 = x.2.1
    rw [hgx]
  rw [e1, e2] at hbound
  omega

/-- The strict spine bound (same chain-window derivation, kept strict). -/
theorem spineOK_strict_of_le1 {G R : TrioSeq} {v0 w1 w2 : ℕ} {lp : ℕ × ℕ × ℕ}
    (hle1 : le1 ((G ++ ((v0, w1, w2) :: R)) ++ [lp]) G.length
      (G ++ ((v0, w1, w2) :: R)).length) :
    SpineOK R lp.1 (w1 + 1) := by
  intro U V x hR hxlt hV
  have h := spineOK_of_le1 (v0 := v0) (w2 := w2) hle1
  -- rerun the tail of the weak proof to recover the strict bound
  set M := (G ++ ((v0, w1, w2) :: R)) ++ [lp] with hMdef
  set A := G ++ ((v0, w1, w2) :: U) with hAdef
  have hMeq : M = A ++ (x :: (V ++ [lp])) := by
    rw [hMdef, hAdef, hR]
    simp
  have hAlen : A.length = G.length + 1 + U.length := by
    rw [hAdef]
    simp
    omega
  have hj1 : (G ++ ((v0, w1, w2) :: R)).length = A.length + 1 + V.length := by
    rw [hR, hAlen]
    simp
    omega
  have hMlen : M.length = (G ++ ((v0, w1, w2) :: R)).length + 1 := by
    rw [hMdef]
    simp
    omega
  have hgx : M.getD A.length (0, 0, 0) = x := by
    have h2 := getD_append_right' A (x :: (V ++ [lp])) 0
    rw [Nat.add_zero] at h2
    rw [hMeq]
    exact h2
  have hwin : ∀ y, A.length < y → y ≤ (G ++ ((v0, w1, w2) :: R)).length →
      entry M 0 A.length < entry M 0 y := by
    intro y hy1 hy2
    obtain ⟨t, rfl⟩ : ∃ t, y = A.length + (t + 1) := ⟨y - A.length - 1, by omega⟩
    have hgy : M.getD (A.length + (t + 1)) (0, 0, 0)
        = (V ++ [lp]).getD t (0, 0, 0) := by
      conv_lhs => rw [hMeq]
      rw [getD_append_right' A (x :: (V ++ [lp])) (t + 1), List.getD_cons_succ]
    show (M.getD A.length (0, 0, 0)).1 < (M.getD (A.length + (t + 1)) (0, 0, 0)).1
    rw [hgx, hgy]
    rcases Nat.lt_or_ge t V.length with ht | ht
    · have hmem : (V ++ [lp]).getD t (0, 0, 0) ∈ V := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left ht,
          List.getElem?_eq_getElem ht]
        exact List.getElem_mem _
      exact hV _ hmem
    · have htv : t = V.length := by omega
      subst htv
      have he : (V ++ [lp]).getD V.length (0, 0, 0) = lp := by
        have h2 := getD_append_right' V [lp] 0
        rw [Nat.add_zero] at h2
        exact h2
      rw [he]
      exact hxlt
  have hxrtg : Relation.ReflTransGen (nextrel0 M) A.length
      (G ++ ((v0, w1, w2) :: R)).length := by
    refine rtg0_of_window (by omega) (by omega) ?_
    intro l hl1 hl2
    exact hwin l hl1 hl2
  have hrootx : Relation.ReflTransGen (nextrel0 M) G.length A.length :=
    rtg0_comparable (rtg1_to_rtg0 hle1.2.2) hxrtg (by omega)
  have hbound := le1_chain_window hle1.2.2 A.length hrootx hxrtg (by omega)
  have hgr : M.getD G.length (0, 0, 0) = (v0, w1, w2) := by
    have h2 := getD_append_right' G (((v0, w1, w2) :: R) ++ [lp]) 0
    rw [Nat.add_zero] at h2
    rw [hMdef, List.append_assoc]
    rw [h2]
    rfl
  have e1 : entry M 1 G.length = w1 := by
    show (M.getD G.length (0, 0, 0)).2.1 = w1
    rw [hgr]
  have e2 : entry M 1 A.length = x.2.1 := by
    show (M.getD A.length (0, 0, 0)).2.1 = x.2.1
    rw [hgx]
  rw [e1, e2] at hbound
  omega

/-! ## `i1 = 1` の引数支配 -/

/-- Argument domination for the `i1 = 1` boundary continuation. -/
def AscArgDom1 : Prop :=
  ∀ {G R S : TrioSeq} {v0 w1 w2 d0 : ℕ},
    ST_TS ((G ++ ((v0, w1, w2) :: R)) ++ [(v0 + d0, w1 + 1, 0)]) →
    ST_TS ((G ++ ((v0, w1, w2) :: R)) ++ (v0 + d0, w1, w2) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 →
    le1 ((G ++ ((v0, w1, w2) :: R)) ++ [(v0 + d0, w1 + 1, 0)]) G.length
      (G ++ ((v0, w1, w2) :: R)).length →
    ∃ m, sle (S.takeWhile fun p => v0 + d0 < p.1)
      (shiftr01 d0 0 (R ++ copies d0 0 (shiftr01 d0 0 ((v0, w1, w2) :: R)) m))

theorem ascArgDom1_of_core (H : ArgDomCore) : AscArgDom1 := by
  intro G R S v0 w1 w2 d0 _ hN hRgt hd hle1
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set D := S.dropWhile (fun p => v0 + d0 < p.1) with hDdef
  set A2 := D.takeWhile (fun p => v0 < p.1) with hA2def
  set Z := D.dropWhile (fun p => v0 < p.1) with hZdef
  have hSsplit : Shi ++ D = S := List.takeWhile_append_dropWhile
  have hDsplit : A2 ++ Z = D := List.takeWhile_append_dropWhile
  have hShigt : ∀ x ∈ Shi, v0 + d0 < x.1 := by
    intro x hx
    simpa using List.mem_takeWhile_imp hx
  have hA2gt : ∀ x ∈ A2, v0 < x.1 := by
    intro x hx
    simpa using List.mem_takeWhile_imp hx
  have hDhd : D = [] ∨ (D.headI).1 ≤ v0 + d0 := by
    rcases hdd : D with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not
        (fun p : ℕ × ℕ × ℕ => decide (v0 + d0 < p.1)) S
      rw [← hDdef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 + d0 < z'.1) := by simpa using h
      simp only [List.headI]
      omega
  have hA2hd : A2 = [] ∨ (A2.headI).1 ≤ v0 + d0 := by
    rcases hdd : A2 with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hDne : D ≠ [] := by
        intro he
        rw [hA2def, he] at hdd
        simp at hdd
      have hhd : A2.headI = D.headI := by
        rcases hd2 : D with _ | ⟨y, Y⟩
        · exact absurd hd2 hDne
        · rw [hA2def, hd2]
          by_cases hy : v0 < y.1
          · rw [List.takeWhile_cons_of_pos (by simpa using hy)]
            rfl
          · rw [List.takeWhile_cons_of_neg (by simpa using hy)]
            rw [hA2def, hd2, List.takeWhile_cons_of_neg (by simpa using hy)] at hdd
            simp at hdd
      rw [← hdd, hhd]
      rcases hDhd with h | h
      · exact absurd h hDne
      · exact h
  have hZhd : Z = [] ∨ (Z.headI).1 ≤ v0 := by
    rcases hdd : Z with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not
        (fun p : ℕ × ℕ × ℕ => decide (v0 < p.1)) D
      rw [← hZdef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 < z'.1) := by simpa using h
      simp only [List.headI]
      omega
  have hNeq : (G ++ ((v0, w1, w2) :: R)) ++ (v0 + d0, w1, w2) :: S
      = (G ++ (v0, w1, w2) :: (R ++ (v0 + d0, w1, w2) :: (Shi ++ A2))) ++ Z := by
    rw [← hSsplit, ← hDsplit]
    simp
  have hspine : SpineOK R (v0 + d0) (w1 + 1) := by
    have h := spineOK_strict_of_le1 hle1
    simpa using h
  have hcore := H (X := G) (A1 := R) (B := Shi) (A2 := A2) (Z := Z)
    (u := v0) (w1 := w1) (z := w2) (e := d0) (f := 0)
    (by
      rw [Nat.add_zero]
      exact hNeq ▸ hN)
    hd (Or.inl rfl) hRgt hShigt hA2gt hA2hd hZhd hspine
  rw [Nat.add_zero, hshift_f0] at hcore
  have hbnd : shiftr01 d0 0 (R ++ (v0 + d0, w1, w2) :: (Shi ++ A2))
      = shiftr01 d0 0 R ++ (v0 + d0 + d0, w1, w2) :: shiftr01 d0 0 (Shi ++ A2) := by
    rw [shiftr01_append, shiftr01_cons]
    rfl
  rw [hbnd] at hcore
  obtain ⟨m, hm⟩ := peel_aux d0 w1 w2 Shi.length Shi (shiftr01 d0 0 R) A2
    (v0 + d0 + d0) le_rfl hcore
  refine ⟨m, ?_⟩
  have hgoal : shiftr01 d0 0 (R ++ copies d0 0 (shiftr01 d0 0 ((v0, w1, w2) :: R)) m)
      = shiftr01 d0 0 R
        ++ copies d0 0 ((v0 + d0 + d0, w1, w2)
            :: shiftr01 d0 0 (shiftr01 d0 0 R)) m := by
    rw [shiftr01_append, shiftr01_copies, shiftr01_cons, shiftr01_cons]
    rfl
  rw [hgoal]
  exact hm

theorem copies_succ_back (d0 d1 : ℕ) (blk : TrioSeq) (n : ℕ) :
    copies d0 d1 blk (n + 1) = copies d0 d1 blk n ++ shiftr01 (n * d0) (n * d1) blk := by
  unfold copies
  rw [List.range_succ, List.flatMap_append]
  simp

theorem shiftr01_length (d0 d1 : ℕ) (X : TrioSeq) :
    (shiftr01 d0 d1 X).length = X.length := by
  unfold shiftr01
  simp

theorem mem_shiftr01_le {d : ℕ} (e : ℕ) {X : TrioSeq} (h : ∀ x ∈ X, d ≤ x.1) :
    ∀ x ∈ shiftr01 e 0 X, d + e ≤ x.1 := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := mem_shiftr01.1 hx
  have := h p hp
  dsimp only
  omega

/-- **The first ascending branch closes with one extra copy.** -/
theorem asc_crux1 (H : AscArgDom1) {G R S : TrioSeq} {v0 w1 w2 d0 : ℕ}
    (hM : ST_TS ((G ++ ((v0, w1, w2) :: R)) ++ [(v0 + d0, w1 + 1, 0)]))
    (hN : ST_TS ((G ++ ((v0, w1, w2) :: R)) ++ (v0 + d0, w1, w2) :: S))
    (hRgt : ∀ x ∈ R, v0 < x.1) (hd : 0 < d0)
    (hle1 : le1 ((G ++ ((v0, w1, w2) :: R)) ++ [(v0 + d0, w1 + 1, 0)]) G.length
      (G ++ ((v0, w1, w2) :: R)).length) :
    ∃ m, 1 ≤ m ∧ sle ((v0 + d0, w1, w2) :: S)
      (shiftr01 d0 0 (copies d0 0 ((v0, w1, w2) :: R) m)) := by
  obtain ⟨m, hdom⟩ := H hM hN hRgt hd hle1
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set Slo := S.dropWhile (fun p => v0 + d0 < p.1) with hSlodef
  have hSsplit : Shi ++ Slo = S := List.takeWhile_append_dropWhile
  set blk' := shiftr01 d0 0 ((v0, w1, w2) :: R) with hblk'
  have hblk'cons : blk' = (v0 + d0, w1, w2) :: shiftr01 d0 0 R := by
    rw [hblk', shiftr01_cons]
    dsimp only
    rw [Nat.add_zero]
  have hDmGt : ∀ x ∈ R ++ copies d0 0 blk' m, v0 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hRgt x hx
    · rw [hblk'cons] at hx
      have := copies_v0_le (v0 := v0 + d0) (w1 := w1) (w2 := w2)
        (R := shiftr01 d0 0 R)
        (mem_shiftr01_le d0 (fun y hy => (hRgt y hy).le)) d0 0 m x hx
      omega
  have hSloHd : Slo = [] ∨ (Slo.headI).1 ≤ v0 + d0 := by
    rcases hdd : Slo with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not
        (fun p : ℕ × ℕ × ℕ => decide (v0 + d0 < p.1)) S
      rw [← hSlodef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 + d0 < z'.1) := by simpa using h
      simp only [List.headI]
      omega
  refine ⟨m + 2, by omega, ?_⟩
  have hinner : shiftr01 d0 0 (copies d0 0 blk' (m + 1))
      = shiftr01 d0 0 (copies d0 0 blk' m)
        ++ shiftr01 d0 0 (shiftr01 (m * d0) (m * 0) blk') := by
    rw [copies_succ_back, shiftr01_append]
  have htgt : shiftr01 d0 0 (copies d0 0 ((v0, w1, w2) :: R) (m + 2))
      = (v0 + d0, w1, w2) :: (shiftr01 d0 0 (R ++ copies d0 0 blk' m)
          ++ shiftr01 d0 0 (shiftr01 (m * d0) (m * 0) blk')) := by
    rw [shiftr01_copies, ← hblk', copies_succ_front, hinner, shiftr01_append,
      List.append_assoc]
    conv_lhs => rw [hblk'cons]
    rw [List.cons_append, ← hblk'cons]
  rw [htgt]
  have hEne : shiftr01 d0 0 (shiftr01 (m * d0) (m * 0) blk') ≠ [] := by
    rw [hblk'cons]
    simp [shiftr01]
  have hEhd : ((shiftr01 d0 0 (shiftr01 (m * d0) (m * 0) blk')).headI).1
      = v0 + d0 + m * d0 + d0 := by
    rw [hblk'cons, shiftr01_cons, shiftr01_cons]
    show v0 + d0 + m * d0 + d0 = v0 + d0 + m * d0 + d0
    rfl
  show sle ([((v0 + d0 : ℕ), (w1 : ℕ), (w2 : ℕ))] ++ S)
    ([((v0 + d0 : ℕ), (w1 : ℕ), (w2 : ℕ))] ++ _)
  rw [sle_append_cancel]
  rcases hdom with heq | hlt
  · have hS : S = shiftr01 d0 0 (R ++ copies d0 0 blk' m) ++ Slo := by
      rw [← hSsplit, heq]
    rw [hS]
    refine (sle_append_cancel _).2 ?_
    rcases hSloHd with h | h
    · rw [h]
      exact Or.inr (by simpa using hEne)
    · rcases hdd : Slo with _ | ⟨z', Z'⟩
      · exact Or.inr (by simpa using hEne)
      · rcases hb : shiftr01 d0 0 (shiftr01 (m * d0) (m * 0) blk') with _ | ⟨b, B⟩
        · exact absurd hb hEne
        · refine Or.inr (Or.inl ?_)
          rw [hdd] at h
          rw [hb] at hEhd
          simp only [List.headI] at h hEhd
          exact Or.inl (by omega)
  · refine Or.inr ?_
    rw [← hSsplit]
    refine seqlex_splice hlt ?_ _
    rcases hSloHd with h | h
    · exact Or.inl h
    · refine Or.inr (fun x hx => ?_)
      obtain ⟨y, hy, rfl⟩ := mem_shiftr01.1 hx
      have := hDmGt y hy
      refine Or.inl ?_
      dsimp only
      omega

/-! ## `srow = 1` の派遣 -/

set_option maxHeartbeats 1000000 in
/-- The `srow = 1` half of the ascending crux, from the core. -/
theorem trioAsc_srow1 (Hc : ArgDomCore) {M N : TrioSeq} {q : ℕ × ℕ × ℕ}
    {S : TrioSeq} (hM : ST_TS M) (hN : ST_TS N) (L1 : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hsr1 : srow M (M.length - 1) = 1)
    (hNeq : N = M.dropLast ++ q :: S)
    (hq : collt q (M.getD (M.length - 1) (0, 0, 0))) :
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
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
  have np1 : nextrel1 M (parent M (srow M (M.length - 1)) (M.length - 1))
      (M.length - 1) := by
    have np' := np
    unfold nextR at np'
    rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0), if_pos hsr1] at np'
    exact np'
  set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
  set L := M.length - 1 - j0 with hLdef
  have hLpos : 0 < L := by omega
  have hj0b : j0 < M.length := by omega
  -- pin the dropped column
  have hlp1 : entry M 1 (M.length - 1) = entry M 1 j0 + 1 :=
    nextrel1_snd_succ (r1ok_ST_TS hM) np1
  have hlp2 : entry M 2 (M.length - 1) = 0 := by
    by_contra hcon
    push Not at hcon
    have : srow M (M.length - 1) = 2 := by
      unfold srow
      rw [if_pos (by omega)]
    omega
  have hd0e : (if 0 < srow M (M.length - 1)
      then entry M 0 (M.length - 1) - entry M 0 j0 else 0)
      = entry M 0 (M.length - 1) - entry M 0 j0 := by
    rw [if_pos (by omega)]
  have hd1e : (if 1 < srow M (M.length - 1)
      then entry M 1 (M.length - 1) - entry M 1 j0 else 0) = 0 := by
    rw [if_neg (by omega)]
  set d0i := entry M 0 (M.length - 1) - entry M 0 j0 with hd0i
  have hd0pos : 0 < d0i := by
    have := iv (M.length - 1) j0lt le_rfl
    omega
  have hlp0 : entry M 0 (M.length - 1) = entry M 0 j0 + d0i := by
    have := iv (M.length - 1) j0lt le_rfl
    omega
  have hlpe : M.getD (M.length - 1) (0, 0, 0)
      = (entry M 0 j0 + d0i, entry M 1 j0 + 1, 0) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (M.getD (M.length - 1) (0, 0, 0)).1 = entry M 0 j0 + d0i
      exact hlp0
    · exact hlp1
    · exact hlp2
  rw [hlpe] at hq
  unfold collt at hq
  dsimp only at hq
  -- the first-copy root
  have hMn2 : ∀ m, M⟦m + 1⟧ = M.dropLast
      ++ shiftr01 d0i 0 (copies d0i 0 (seg M j0 L) m) := by
    intro m
    rw [oper_gcopies (m + 1) (by omega) hz hp, ← hj0, ← hLdef, hd0e, hd1e,
      gcopies_eq_from, gcopiesFrom_succ, gcopy_zero,
      gcopiesFrom_d1zero, ← List.append_assoc,
      take_gcopy_zero L1 hz hp]
    congr 1
    rw [Nat.zero_mul, shiftr01_zero]
  have hsegL : seg M j0 L
      = (entry M 0 j0, entry M 1 j0, entry M 2 j0) :: seg M (j0 + 1) (L - 1) := by
    obtain ⟨l', hle⟩ : ∃ l', L = l' + 1 := ⟨L - 1, by omega⟩
    rw [hle, seg_cons, Nat.add_sub_cancel]
  have hRgt : ∀ x ∈ seg M (j0 + 1) (L - 1), entry M 0 j0 < x.1 := by
    intro x hx
    unfold seg at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hjb := List.mem_range'_1.1 hj
    exact iv j (by omega) (by omega)
  -- the head of the first copy
  have hcopy1 : ∀ m, shiftr01 d0i 0 (copies d0i 0 (seg M j0 L) (m + 1))
      = (entry M 0 j0 + d0i, entry M 1 j0, entry M 2 j0)
        :: (shiftr01 d0i 0 (seg M (j0 + 1) (L - 1))
            ++ shiftr01 d0i 0 (shiftr01 d0i 0 (copies d0i 0 (seg M j0 L) m))) := by
    intro m
    rw [copies_succ_front, hsegL]
    unfold shiftr01
    simp only [List.map_append, List.map_cons, List.map_map]
    rfl
  rcases hq with hq1 | ⟨hqe1, hq2⟩
  · -- the continuation opens below the copy level: one copy decides
    refine ⟨2, by omega, ?_⟩
    rw [hMn2 1, hNeq, hcopy1 0]
    refine (sle_append_cancel _).2 (Or.inr ?_)
    exact Or.inl (Or.inl (show q.1 < entry M 0 j0 + d0i by omega))
  rcases hq2 with hq2 | ⟨hqe2, hq3⟩
  · -- strictly below in row 1 at the copy level
    rcases Nat.lt_or_ge q.2.1 (entry M 1 j0) with hql | hqg
    · refine ⟨2, by omega, ?_⟩
      rw [hMn2 1, hNeq, hcopy1 0]
      refine (sle_append_cancel _).2 (Or.inr ?_)
      exact Or.inl (Or.inr ⟨show q.1 = entry M 0 j0 + d0i by omega,
        Or.inl (show q.2.1 < entry M 1 j0 by omega)⟩)
    · have hqe : q.2.1 = entry M 1 j0 := by omega
      -- z-analysis at the boundary
      rcases Nat.lt_trichotomy q.2.2 (entry M 2 j0) with hzl | hze | hzg
      · refine ⟨2, by omega, ?_⟩
        rw [hMn2 1, hNeq, hcopy1 0]
        refine (sle_append_cancel _).2 (Or.inr ?_)
        exact Or.inl (Or.inr ⟨show q.1 = entry M 0 j0 + d0i by omega,
          Or.inr ⟨show q.2.1 = entry M 1 j0 by omega,
            show q.2.2 < entry M 2 j0 by omega⟩⟩)
      · -- the exact boundary: the ascending crux
        have hqeq : q = (entry M 0 j0 + d0i, entry M 1 j0, entry M 2 j0) :=
          Prod.ext (by omega) (Prod.ext (by omega) (by omega))
        have hMsh : (M.take j0
            ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
              :: seg M (j0 + 1) (L - 1)))
            ++ [((entry M 0 j0 + d0i, entry M 1 j0 + 1, 0) : ℕ × ℕ × ℕ)] = M := by
          rw [← hsegL]
          have h1 : M.take j0 ++ seg M j0 L = M.dropLast :=
            take_gcopy_zero L1 hz hp
          rw [h1, ← hlpe]
          exact dropLast_snoc_getD (by
            intro he
            rw [he] at L1
            simp at L1)
        have hNsh : (M.take j0
            ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
              :: seg M (j0 + 1) (L - 1)))
            ++ ((entry M 0 j0 + d0i, entry M 1 j0, entry M 2 j0) : ℕ × ℕ × ℕ)
              :: S = N := by
          rw [← hsegL]
          have h1 : M.take j0 ++ seg M j0 L = M.dropLast :=
            take_gcopy_zero L1 hz hp
          rw [h1, hNeq, ← hqeq]
        have hle1sh : le1 ((M.take j0
            ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
              :: seg M (j0 + 1) (L - 1)))
            ++ [((entry M 0 j0 + d0i, entry M 1 j0 + 1, 0) : ℕ × ℕ × ℕ)])
            (M.take j0).length
            (M.take j0
              ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
                :: seg M (j0 + 1) (L - 1))).length := by
          rw [hMsh]
          have htk : (M.take j0).length = j0 := by
            rw [List.length_take]
            omega
          have hbk : (M.take j0
              ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
                :: seg M (j0 + 1) (L - 1))).length = M.length - 1 := by
            rw [List.length_append, htk, List.length_cons]
            unfold seg
            rw [List.length_map, List.length_range']
            omega
          rw [htk, hbk]
          exact ⟨by omega, by omega, Relation.ReflTransGen.single np1⟩
        have hMst : ST_TS ((M.take j0
            ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
              :: seg M (j0 + 1) (L - 1)))
            ++ [((entry M 0 j0 + d0i, entry M 1 j0 + 1, 0) : ℕ × ℕ × ℕ)]) := by
          rw [hMsh]
          exact hM
        have hNst : ST_TS ((M.take j0
            ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0)
              :: seg M (j0 + 1) (L - 1)))
            ++ ((entry M 0 j0 + d0i, entry M 1 j0, entry M 2 j0) : ℕ × ℕ × ℕ)
              :: S) := by
          rw [hNsh]
          exact hN
        obtain ⟨m, hm1, hm⟩ := asc_crux1 (ascArgDom1_of_core Hc)
          hMst hNst hRgt hd0pos hle1sh
        refine ⟨m + 1, by omega, ?_⟩
        rw [hMn2 m, hNeq, hqeq]
        refine (sle_append_cancel _).2 ?_
        rw [← hsegL] at hm
        exact hm
      · -- z-jump at the boundary: impossible
        exfalso
        have hzj := zjump_ST_TS hN
        have hNlen : N.length = M.length + S.length := by
          rw [hNeq]
          simp
          omega
        have hgetN : ∀ x, x < M.length - 1 →
            N.getD x (0, 0, 0) = M.getD x (0, 0, 0) := by
          intro x hx
          rw [hNeq, getD_append_left (by
            rw [List.length_dropLast]
            omega)]
          rw [List.dropLast_eq_take, getD_take (by omega)]
        have hgetQ : N.getD (M.length - 1) (0, 0, 0) = q := by
          rw [hNeq]
          have h := getD_append_right' M.dropLast (q :: S) 0
          rw [Nat.add_zero] at h
          rw [show M.length - 1 = (M.dropLast).length from by
            rw [List.length_dropLast], h]
          rfl
        have := hzj j0 (M.length - 1) (by omega) (by omega)
          (by
            intro l h1 h2
            show entry N 0 j0 < entry N 0 l
            rcases Nat.eq_or_lt_of_le h2 with rfl | h2'
            · unfold entry
              rw [hgetN j0 (by omega), hgetQ]
              show (M.getD j0 (0, 0, 0)).1 < q.1
              have e0 : entry M 0 j0 = (M.getD j0 (0, 0, 0)).1 := rfl
              omega
            · unfold entry
              rw [hgetN j0 (by omega), hgetN l (by omega)]
              exact iv l h1 (by omega))
          (by
            show entry N 1 (M.length - 1) = entry N 1 j0
            unfold entry
            rw [hgetN j0 (by omega), hgetQ]
            show q.2.1 = (M.getD j0 (0, 0, 0)).2.1
            have e1 : entry M 1 j0 = (M.getD j0 (0, 0, 0)).2.1 := rfl
            omega)
          (by
            intro l h1 h2 h3 h4
            -- a right-visible column is a chain node of the dropped column
            have hlM : ∀ x, x ≤ l → entry N 0 x = entry M 0 x := by
              intro x hx
              unfold entry
              rw [hgetN x (by omega)]
            have hlrtg : Relation.ReflTransGen (nextrel0 M) l (M.length - 1) := by
              refine rtg0_of_window (by omega) (by omega) ?_
              intro l'' hl1 hl2
              rcases Nat.eq_or_lt_of_le hl2 with rfl | hl3
              · have := h3
                unfold entry at this
                rw [hgetN l (by omega), hgetQ] at this
                have this2 : (M.getD l (0, 0, 0)).1 < q.1 := this
                show entry M 0 l < entry M 0 (M.length - 1)
                have e0 : entry M 0 l = (M.getD l (0, 0, 0)).1 := rfl
                omega
              · have := h4 l'' hl1 hl3
                unfold entry at this
                rw [hgetN l (by omega), hgetN l'' (by omega)] at this
                exact this
            have hlrtg0 : Relation.ReflTransGen (nextrel0 M) j0 l :=
              rtg0_comparable chain hlrtg (by omega)
            have hbnd := le1_chain_window
              (Relation.ReflTransGen.single np1) l hlrtg0 hlrtg (by omega)
            show entry N 1 j0 ≤ entry N 1 l
            unfold entry
            rw [hgetN j0 (by omega), hgetN l (by omega)]
            show (M.getD j0 (0, 0, 0)).2.1 ≤ (M.getD l (0, 0, 0)).2.1
            have e1 : entry M 1 j0 = (M.getD j0 (0, 0, 0)).2.1 := rfl
            have e1' : entry M 1 l = (M.getD l (0, 0, 0)).2.1 := rfl
            omega)
        have e2q : entry N 2 (M.length - 1) = q.2.2 := by
          unfold entry
          rw [hgetQ]
          rfl
        have e2j : entry N 2 j0 = entry M 2 j0 := by
          unfold entry
          rw [hgetN j0 (by omega)]
        omega
  · exact absurd hq3 (by omega)

/-! ## 心材シフトの合成則（`srow = 2` の剥離用） -/

theorem shiftr01_comp (e e' : ℕ) (X : TrioSeq) :
    shiftr01 e 0 (shiftr01 e' 0 X) = shiftr01 (e + e') 0 X := by
  unfold shiftr01
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro p hp
  simp only [Function.comp_apply, Prod.mk.injEq, and_true]
  omega

theorem mem_hshift {w1 e f : ℕ} : ∀ {A : TrioSeq} {x : ℕ × ℕ × ℕ},
    x ∈ hshift w1 e f A → ∃ y ∈ A, x.1 = y.1 + e := by
  intro A
  induction A using hshift.induct (w1 := w1) with
  | case1 =>
    intro x hx
    rw [hshift_nil] at hx
    exact absurd hx (List.not_mem_nil)
  | case2 p rest hthr ih1 ih2 =>
    intro x hx
    rw [hshift_cons, if_pos hthr] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, by simp, rfl⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, he⟩ := ih1 hx
        exact ⟨y, List.mem_cons_of_mem _ ((List.takeWhile_sublist _).mem hy), he⟩
      · obtain ⟨y, hy, he⟩ := ih2 hx
        exact ⟨y, List.mem_cons_of_mem _ ((List.dropWhile_sublist _).mem hy), he⟩
  | case3 p rest hthr ih2 =>
    intro x hx
    rw [hshift_cons, if_neg hthr] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, by simp, rfl⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨y, hy, rfl⟩ := mem_shiftr01.1 hx
        exact ⟨y, List.mem_cons_of_mem _ ((List.takeWhile_sublist _).mem hy), rfl⟩
      · obtain ⟨y, hy, he⟩ := ih2 hx
        exact ⟨y, List.mem_cons_of_mem _ ((List.dropWhile_sublist _).mem hy), he⟩

theorem hshift_headI (w1 e f : ℕ) (p : ℕ × ℕ × ℕ) (rest : TrioSeq) :
    ((hshift w1 e f (p :: rest)).headI).1 = p.1 + e := by
  rw [hshift_cons]
  split_ifs <;> rfl

theorem hshift_ne_nil (w1 e f : ℕ) (p : ℕ × ℕ × ℕ) (rest : TrioSeq) :
    hshift w1 e f (p :: rest) ≠ [] := by
  rw [hshift_cons]
  split_ifs <;> exact List.cons_ne_nil _ _

/-- The image split of a level-separated pair of forests. -/
theorem hshift_split (w1 e' f' v : ℕ) (T D : TrioSeq)
    (hT : ∀ x ∈ T, v < x.1) (hD : D = [] ∨ (D.headI).1 ≤ v) :
    (hshift w1 e' f' T ++ hshift w1 e' f' D).takeWhile
        (fun q => v + e' < q.1) = hshift w1 e' f' T
    ∧ (hshift w1 e' f' T ++ hshift w1 e' f' D).dropWhile
        (fun q => v + e' < q.1) = hshift w1 e' f' D := by
  have hTall : ∀ x ∈ hshift w1 e' f' T,
      (fun q : ℕ × ℕ × ℕ => decide (v + e' < q.1)) x = true := by
    intro x hx
    obtain ⟨y, hy, he⟩ := mem_hshift hx
    have := hT y hy
    simp only [decide_eq_true_eq]
    omega
  constructor
  · rw [takeWhile_append_all hTall]
    rcases hD with rfl | hD
    · rw [hshift_nil]
      simp
    · rcases D with - | ⟨d, D'⟩
      · rw [hshift_nil]
        simp
      · have hhd := hshift_headI w1 e' f' d D'
        rcases he : hshift w1 e' f' (d :: D') with - | ⟨x, X⟩
        · exact absurd he (hshift_ne_nil w1 e' f' d D')
        · rw [List.takeWhile_cons_of_neg (by
            rw [he] at hhd
            simp only [List.headI] at hhd hD
            simp only [decide_eq_true_eq]
            omega)]
          simp
  · rw [dropWhile_append_all hTall]
    rcases hD with rfl | hD
    · rw [hshift_nil]
      simp
    · rcases D with - | ⟨d, D'⟩
      · rw [hshift_nil]
        simp
      · have hhd := hshift_headI w1 e' f' d D'
        rcases he : hshift w1 e' f' (d :: D') with - | ⟨x, X⟩
        · exact absurd he (hshift_ne_nil w1 e' f' d D')
        · rw [List.dropWhile_cons_of_neg (by
            rw [he] at hhd
            simp only [List.headI] at hhd hD
            simp only [decide_eq_true_eq]
            omega)]

/-- The analogous split for a uniformly shifted blocked forest. -/
theorem shiftr01_split (e' v : ℕ) (T D : TrioSeq)
    (hT : ∀ x ∈ T, v < x.1) (hD : D = [] ∨ (D.headI).1 ≤ v) (w1 f' : ℕ) :
    (shiftr01 e' 0 T ++ hshift w1 e' f' D).takeWhile
        (fun q => v + e' < q.1) = shiftr01 e' 0 T
    ∧ (shiftr01 e' 0 T ++ hshift w1 e' f' D).dropWhile
        (fun q => v + e' < q.1) = hshift w1 e' f' D := by
  have hTall : ∀ x ∈ shiftr01 e' 0 T,
      (fun q : ℕ × ℕ × ℕ => decide (v + e' < q.1)) x = true := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_shiftr01.1 hx
    have := hT y hy
    simp only [decide_eq_true_eq]
    show v + e' < y.1 + e'
    omega
  constructor
  · rw [takeWhile_append_all hTall]
    rcases hD with rfl | hD
    · rw [hshift_nil]
      simp
    · rcases D with - | ⟨d, D'⟩
      · rw [hshift_nil]
        simp
      · have hhd := hshift_headI w1 e' f' d D'
        rcases he : hshift w1 e' f' (d :: D') with - | ⟨x, X⟩
        · exact absurd he (hshift_ne_nil w1 e' f' d D')
        · rw [List.takeWhile_cons_of_neg (by
            rw [he] at hhd
            simp only [List.headI] at hhd hD
            simp only [decide_eq_true_eq]
            omega)]
          simp
  · rw [dropWhile_append_all hTall]
    rcases hD with rfl | hD
    · rw [hshift_nil]
      simp
    · rcases D with - | ⟨d, D'⟩
      · rw [hshift_nil]
        simp
      · have hhd := hshift_headI w1 e' f' d D'
        rcases he : hshift w1 e' f' (d :: D') with - | ⟨x, X⟩
        · exact absurd he (hshift_ne_nil w1 e' f' d D')
        · rw [List.dropWhile_cons_of_neg (by
            rw [he] at hhd
            simp only [List.headI] at hhd hD
            simp only [decide_eq_true_eq]
            omega)]

/-- **Composition of heartwood shifts** (same threshold). -/
theorem hshift_comp (w1 e f e' f' : ℕ) : ∀ A : TrioSeq,
    hshift w1 e f (hshift w1 e' f' A) = hshift w1 (e + e') (f + f') A := by
  intro A
  induction A using hshift.induct (w1 := w1) with
  | case1 =>
    rw [hshift_nil, hshift_nil, hshift_nil]
  | case2 p rest hthr ih1 ih2 =>
    have hDhd : rest.dropWhile (fun q => p.1 < q.1) = []
        ∨ ((rest.dropWhile (fun q => p.1 < q.1)).headI).1 ≤ p.1 := by
      rcases hd : rest.dropWhile (fun q => p.1 < q.1) with _ | ⟨z, Z⟩
      · exact Or.inl hd
      · refine Or.inr ?_
        have h := List.head?_dropWhile_not
          (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) rest
        rw [hd] at h
        simp only [List.head?_cons] at h
        have : ¬ (p.1 < z.1) := by simpa using h
        rw [hd]
        simp only [List.headI]
        omega
    have hsp := hshift_split w1 e' f' p.1
      (rest.takeWhile fun q => p.1 < q.1)
      (rest.dropWhile fun q => p.1 < q.1)
      (fun x hx => by simpa using List.mem_takeWhile_imp hx) hDhd
    rw [hshift_cons (w1 := w1) (e := e') (f := f'), if_pos hthr,
      hshift_cons]
    rw [if_pos (show w1 < ((p.1 + e', p.2.1 + f', p.2.2) : ℕ × ℕ × ℕ).2.1
      from by dsimp only; omega)]
    dsimp only
    rw [hsp.1, hsp.2, ih1, ih2, hshift_cons, if_pos hthr]
    congr 2
    · omega
    · exact Prod.ext (by omega) rfl
  | case3 p rest hthr ih2 =>
    have hDhd : rest.dropWhile (fun q => p.1 < q.1) = []
        ∨ ((rest.dropWhile (fun q => p.1 < q.1)).headI).1 ≤ p.1 := by
      rcases hd : rest.dropWhile (fun q => p.1 < q.1) with _ | ⟨z, Z⟩
      · exact Or.inl hd
      · refine Or.inr ?_
        have h := List.head?_dropWhile_not
          (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) rest
        rw [hd] at h
        simp only [List.head?_cons] at h
        have : ¬ (p.1 < z.1) := by simpa using h
        rw [hd]
        simp only [List.headI]
        omega
    have hsp := shiftr01_split e' p.1
      (rest.takeWhile fun q => p.1 < q.1)
      (rest.dropWhile fun q => p.1 < q.1)
      (fun x hx => by simpa using List.mem_takeWhile_imp hx) hDhd w1 f'
    rw [hshift_cons (w1 := w1) (e := e') (f := f'), if_neg hthr,
      hshift_cons]
    rw [if_neg (show ¬ w1 < ((p.1 + e', p.2.1, p.2.2) : ℕ × ℕ × ℕ).2.1
      from by dsimp only; omega)]
    dsimp only
    rw [hsp.1, hsp.2, ih2, shiftr01_comp, hshift_cons, if_neg hthr]
    congr 2
    omega

end Googology.Trans.BMS.TrioCof
