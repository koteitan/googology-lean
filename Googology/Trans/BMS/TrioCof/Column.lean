/-
Ported verbatim from koteitan/trio, `lean/Column.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Column.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
**列の不変量**（トリオ数列）、第 1 部: 接頭辞不変性。

親子関係・祖先関係・親の存在・探索行・展開のすべてが前置に不変であり、
行 0 の親子は前置と後半の境界を越えない。トリオでは行 1 の祖先 `le1` と
行 2 の親子 `nextrel2` の層が加わる。

2 行の Column.lean と同じ骨格。
-/
import Googology.Trans.BMS.TrioCof.Cnf
import Mathlib.Algebra.NeZero

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-! ## `oper` は末尾除去 + 後続 -/

/-- `M⟦n⟧ = M.dropLast ++ R` for some `R` (long `M`). -/
theorem oper_eq_dropLast_append {M : TrioSeq} {n : ℕ} (L : 1 < M.length)
    (n1 : 1 ≤ n) :
    ∃ R, M⟦n⟧ = M.dropLast ++ R := by
  have hPred : Pred M = M.dropLast := by
    unfold Pred
    rw [if_neg (by omega)]
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · refine ⟨[], ?_⟩
    rw [oper_eq_pred_of_zero n (by omega) hz, hPred, List.append_nil]
  · by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
    · -- bad case: the base copy re-creates the dropped-last prefix
      have np := parent_nextR hp
      set j1 := M.length - 1 with hj1
      set i1 := srow M j1 with hi1
      set j0 := parent M i1 j1 with hj0
      have j0lt : j0 < j1 := nextR_index_lt np
      set d0 := (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0) with hd0
      set d1 := (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) with hd1
      set B : ℕ → TrioSeq := fun k => (List.range' j0 (j1 - j0)).map
          (fun j => (entry M 0 j + (if le0 M j0 j then k * d0 else 0),
                     entry M 1 j + (if le1 M j0 j then k * d1 else 0),
                     entry M 2 j)) with hBdef
      have hMn : M⟦n⟧ = M.take j0 ++ (List.range n).flatMap B := by
        rw [oper_bad_unfold n (by omega) hz hp]
      have hB0 : B 0 = (List.range' j0 (j1 - j0)).map (fun j => M.getD j (0, 0, 0)) := by
        show (List.range' j0 (j1 - j0)).map
            (fun j => (entry M 0 j + (if le0 M j0 j then 0 * d0 else 0),
                       entry M 1 j + (if le1 M j0 j then 0 * d1 else 0),
                       entry M 2 j)) = _
        apply List.map_congr_left
        intro j hj
        rw [getD_eq_entries]
        simp
      have hdrop : M.dropLast = M.take j0
          ++ (List.range' j0 (j1 - j0)).map (fun j => M.getD j (0, 0, 0)) := by
        have hdl : M.dropLast = M.take j1 := by
          rw [List.dropLast_eq_take]
        rw [hdl]
        conv_lhs => rw [← List.take_append_drop j0 (M.take j1)]
        congr 1
        · rw [List.take_take, Nat.min_eq_left (by omega)]
        · rw [drop_eq_map_getD (M.take j1) j0 (0, 0, 0)]
          have hlen : (M.take j1).length = j1 := by
            rw [List.length_take]
            omega
          rw [hlen]
          apply List.map_congr_left
          intro j hj
          obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
          rw [getD_eq_getElem' _ _ (by rw [List.length_take]; omega),
            getD_eq_getElem' _ _ (by omega : j0 + 1 * i < M.length),
            List.getElem_take]
      have hrange : List.range n = 0 :: List.range' 1 (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp [List.range_eq_range', List.range'_succ]
      refine ⟨(List.range' 1 (n - 1)).flatMap B, ?_⟩
      rw [hMn, hrange, List.flatMap_cons, hB0, hdrop, List.append_assoc]
    · refine ⟨[], ?_⟩
      rw [oper_eq_pred_of_noParent n (by omega) hz hp, hPred, List.append_nil]

/-- `take` commutes with the peel below the last column. -/
theorem dropLast_take {l : TrioSeq} {i : ℕ} (hi : i ≤ l.length - 1) :
    l.dropLast.take i = l.take i := by
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left hi]

/-- **Prefix preservation under expansion**: copy 0 is unshifted, so `M⟦n⟧`
agrees with `M` on the first `M.length - 1` columns (`n ≥ 1`). -/
theorem oper_take_prefix {M : TrioSeq} {n i : ℕ} (L : 1 < M.length)
    (n1 : 1 ≤ n) (hi : i ≤ M.length - 1) :
    (M⟦n⟧).take i = M.take i := by
  obtain ⟨R, hR⟩ := oper_eq_dropLast_append L n1
  rw [hR, List.take_append, show i - M.dropLast.length = 0 from
    (by rw [List.length_dropLast]; omega),
    List.take_zero, List.append_nil, dropLast_take hi]

/-- Every `ST_TS` list is non-empty. -/
theorem stps_len_pos {M : TrioSeq} (hM : ST_TS M) : 0 < M.length := by
  induction hM with
  | diag v => rw [diagSeqT_cons (Nat.zero_le v)]; simp
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · obtain ⟨R, hR⟩ := oper_eq_dropLast_append L hn
      rw [hR, List.length_append, List.length_dropLast]; omega
    · rw [oper_eq_self_of_short n (by omega)]; exact ih

/-- Every `ST_TS` list begins with `(0,0,0)`. -/
theorem stps_head {M : TrioSeq} (hM : ST_TS M) : M.headD (0, 0, 0) = (0, 0, 0) := by
  induction hM with
  | diag v => rw [diagSeqT_cons (Nat.zero_le v)]; rfl
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · obtain ⟨R, hR⟩ := oper_eq_dropLast_append L hn
      rw [hR]
      match N, L with
      | a :: b :: u, _ =>
        simp only [List.dropLast_cons_cons, List.cons_append, List.headD_cons]
        simpa using ih
    · rw [oper_eq_self_of_short n (by omega)]; exact ih

/-! ## 接頭辞不変性 -/

/-- `getD` reads the right summand on out-of-`A` indices. -/
theorem getD_app_right (A T : TrioSeq) {i : ℕ} (h : A.length ≤ i) :
    (A ++ T).getD i (0, 0, 0) = T.getD (i - A.length) (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right h]

/-- `entry` is suffix-invariant. -/
theorem entry_append_right (A T : TrioSeq) (i j : ℕ) :
    entry (A ++ T) i (A.length + j) = entry T i j := by
  unfold entry
  rw [getD_app_right A T (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem nextrel0_append_right (A T : TrioSeq) (j0 j1 : ℕ) :
    nextrel0 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel0 T j0 j1 := by
  unfold nextrel0; rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [entry_append_right, entry_append_right] at h4
    refine ⟨by omega, by omega, by omega, h4, ?_⟩
    intro j hj
    have := h5 (A.length + j) (by omega)
    rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    rw [entry_append_right, entry_append_right]; exact h5 j' (by omega)

theorem rtg_nextrel0_lift (A T : TrioSeq) {j0 c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 T) j0 c) :
    Relation.ReflTransGen (nextrel0 (A ++ T)) (A.length + j0) (A.length + c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc hcd ih =>
    exact Relation.ReflTransGen.tail ih ((nextrel0_append_right A T b c).2 hcd)

theorem le0_append_right_of (A T : TrioSeq) {j0 j1 : ℕ} (h : le0 T j0 j1) :
    le0 (A ++ T) (A.length + j0) (A.length + j1) := by
  obtain ⟨hb0, hb1, hrt⟩ := h
  exact ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega,
    rtg_nextrel0_lift A T hrt⟩

theorem nextrel0_lt {M : TrioSeq} {a b : ℕ} (h : nextrel0 M a b) : a < b := h.2.2.1

theorem rtg_nextrel0_unlift (A T : TrioSeq) {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (A ++ T)) (A.length + a) c) :
    ∃ c', c = A.length + c' ∧ Relation.ReflTransGen (nextrel0 T) a c' := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail d e hde hef ih =>
    obtain ⟨d', rfl, ihd⟩ := ih
    have hge : A.length ≤ e :=
      le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (nextrel0_lt hef))
    obtain ⟨e', rfl⟩ : ∃ e', e = A.length + e' := ⟨e - A.length, by omega⟩
    exact ⟨e', rfl, Relation.ReflTransGen.tail ihd
      ((nextrel0_append_right A T d' e').1 hef)⟩

theorem le0_append_right (A T : TrioSeq) (j0 j1 : ℕ) :
    le0 (A ++ T) (A.length + j0) (A.length + j1) ↔ le0 T j0 j1 := by
  constructor
  · rintro ⟨hb0, hb1, hrt⟩
    rw [List.length_append] at hb0 hb1
    obtain ⟨c', hc', hrtT⟩ := rtg_nextrel0_unlift A T hrt
    have hjc : j1 = c' := by omega
    subst hjc
    exact ⟨by omega, by omega, hrtT⟩
  · exact le0_append_right_of A T

theorem nextrel0_no_cross (A T : TrioSeq) (hroot : entry T 0 0 = 0)
    {k j : ℕ} (hk : k < A.length) (hj : A.length ≤ j)
    (hpos : 0 < entry (A ++ T) 0 j) (hne : nextrel0 (A ++ T) k j) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hne
  have hjne : A.length < j := by
    rcases Nat.lt_or_ge A.length j with h | h
    · exact h
    · have : j = A.length := by omega
      subst this
      have hz : entry (A ++ T) 0 A.length = 0 := by
        have := entry_append_right A T 0 0; rw [Nat.add_zero] at this; rw [this, hroot]
      omega
  have hval := h5 A.length ⟨by omega, hjne⟩
  have hz : entry (A ++ T) 0 A.length = 0 := by
    have := entry_append_right A T 0 0; rw [Nat.add_zero] at this; rw [this, hroot]
  rw [hz] at hval; omega

theorem nextrel0_no_pred_zero {M : TrioSeq} {a b : ℕ} (hz : entry M 0 b = 0)
    (h : nextrel0 M a b) : False := by
  obtain ⟨_, _, _, h4, _⟩ := h; rw [hz] at h4; omega

theorem rtg_to_root {M : TrioSeq} {k b : ℕ} (hz : entry M 0 b = 0)
    (h : Relation.ReflTransGen (nextrel0 M) k b) : k = b := by
  cases h with
  | refl => rfl
  | tail _ hlast => exact absurd hlast (fun hh => nextrel0_no_pred_zero hz hh)

theorem le0_no_cross (A T : TrioSeq) (hroot : entry T 0 0 = 0)
    {k j1 : ℕ} (hk : k < A.length) (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (h : le0 (A ++ T) k (A.length + j1)) : False := by
  obtain ⟨-, -, hrt⟩ := h
  suffices H : ∀ e, Relation.ReflTransGen (nextrel0 (A ++ T)) k e →
      A.length ≤ e → 0 < entry (A ++ T) 0 e → A.length ≤ k by
    exact absurd (H _ hrt (by omega) hpos) (by omega)
  intro e hrt'
  induction hrt' with
  | refl => intro he _; exact he
  | @tail c d hcd hde ih =>
    intro hd hpd
    have hcA : A.length ≤ c := by
      by_contra hlt; push_neg at hlt
      exact nextrel0_no_cross A T hroot hlt hd hpd hde
    by_cases hcpos : 0 < entry (A ++ T) 0 c
    · exact ih hcA hcpos
    · have hcz : entry (A ++ T) 0 c = 0 := by omega
      have hkc : k = c := rtg_to_root hcz hcd
      omega

theorem nextrel1_append_right (A T : TrioSeq) (j0 j1 : ℕ) :
    nextrel1 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel1 T j0 j1 := by
  unfold nextrel1
  rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [entry_append_right, entry_append_right] at h4
    rw [le0_append_right] at h5
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    have := h6 (A.length + j) ⟨by omega, (le0_append_right A T j j1).2 hj2⟩
    rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4,
      (le0_append_right A T j0 j1).2 h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := by
      have : A.length ≤ j := by
        have := hj2.2.2
        have h := nextrel0_rtrancl_index_le this
        omega
      exact ⟨j - A.length, by omega⟩
    rw [le0_append_right] at hj2
    have := h6 j' ⟨by omega, hj2⟩
    rwa [entry_append_right, entry_append_right]

theorem rtg_nextrel1_lift (A T : TrioSeq) {j0 c : ℕ}
    (h : Relation.ReflTransGen (nextrel1 T) j0 c) :
    Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + j0) (A.length + c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc hcd ih =>
    exact Relation.ReflTransGen.tail ih ((nextrel1_append_right A T b c).2 hcd)

theorem rtg_nextrel1_unlift (A T : TrioSeq) {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel1 (A ++ T)) (A.length + a) c) :
    ∃ c', c = A.length + c' ∧ Relation.ReflTransGen (nextrel1 T) a c' := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail d e hde hef ih =>
    obtain ⟨d', rfl, ihd⟩ := ih
    have hge : A.length ≤ e :=
      le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (nextrel1_index_less hef))
    obtain ⟨e', rfl⟩ : ∃ e', e = A.length + e' := ⟨e - A.length, by omega⟩
    exact ⟨e', rfl, Relation.ReflTransGen.tail ihd
      ((nextrel1_append_right A T d' e').1 hef)⟩

theorem le1_append_right (A T : TrioSeq) (j0 j1 : ℕ) :
    le1 (A ++ T) (A.length + j0) (A.length + j1) ↔ le1 T j0 j1 := by
  constructor
  · rintro ⟨hb0, hb1, hrt⟩
    rw [List.length_append] at hb0 hb1
    obtain ⟨c', hc', hrtT⟩ := rtg_nextrel1_unlift A T hrt
    have hjc : j1 = c' := by omega
    subst hjc
    exact ⟨by omega, by omega, hrtT⟩
  · rintro ⟨hb0, hb1, hrt⟩
    exact ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega,
      rtg_nextrel1_lift A T hrt⟩

theorem nextrel2_append_right (A T : TrioSeq) (j0 j1 : ℕ) :
    nextrel2 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel2 T j0 j1 := by
  unfold nextrel2
  rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [entry_append_right, entry_append_right] at h4
    rw [le1_append_right] at h5
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    have := h6 (A.length + j) ⟨by omega, (le1_append_right A T j j1).2 hj2⟩
    rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4,
      (le1_append_right A T j0 j1).2 h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := by
      have : A.length ≤ j := by
        have := hj2.2.2
        have h := rtg1_index_le this
        omega
      exact ⟨j - A.length, by omega⟩
    rw [le1_append_right] at hj2
    have := h6 j' ⟨by omega, hj2⟩
    rwa [entry_append_right, entry_append_right]

theorem nextR_append_right (A T : TrioSeq) (i j0 j1 : ℕ) :
    nextR (A ++ T) i (A.length + j0) (A.length + j1) ↔ nextR T i j0 j1 := by
  unfold nextR
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]; exact nextrel0_append_right A T j0 j1
  · rw [if_neg hi, if_neg hi]
    by_cases hi1 : i = 1
    · rw [if_pos hi1, if_pos hi1]; exact nextrel1_append_right A T j0 j1
    · rw [if_neg hi1, if_neg hi1]; exact nextrel2_append_right A T j0 j1

theorem srow_append_right (A T : TrioSeq) (j : ℕ) :
    srow (A ++ T) (A.length + j) = srow T j := by
  unfold srow; rw [entry_append_right, entry_append_right]

theorem nextR_le0 {M : TrioSeq} {i k b : ℕ} (h : nextR M i k b) : le0 M k b := by
  unfold nextR at h
  by_cases hi : i = 0
  · rw [if_pos hi] at h; exact ⟨h.1, h.2.1, Relation.ReflTransGen.single h⟩
  · rw [if_neg hi] at h
    by_cases hi1 : i = 1
    · rw [if_pos hi1] at h; exact h.2.2.2.2.1
    · rw [if_neg hi1] at h
      obtain ⟨hb0, hb1, hrt⟩ := h.2.2.2.2.1
      exact ⟨hb0, hb1, rtg1_to_rtg0 hrt⟩

theorem nextR_src_in_T (A T : TrioSeq) (hroot : entry T 0 0 = 0)
    {i k j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (h : nextR (A ++ T) i k (A.length + j1)) : A.length ≤ k := by
  by_contra hlt; push_neg at hlt
  exact le0_no_cross A T hroot hlt hpos (nextR_le0 h)

theorem hasParent_append_right (A T : TrioSeq) (hroot : entry T 0 0 = 0)
    {i j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1)) :
    hasParent (A ++ T) i (A.length + j1) ↔ hasParent T i j1 := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, huniq⟩
    have hge := nextR_src_in_T A T hroot hpos hj0
    obtain ⟨j0', rfl⟩ : ∃ j0', j0 = A.length + j0' := ⟨j0 - A.length, by omega⟩
    refine ⟨j0', (nextR_append_right A T i j0' j1).1 hj0, ?_⟩
    intro y hy
    have : A.length + y = A.length + j0' :=
      huniq (A.length + y) ((nextR_append_right A T i y j1).2 hy)
    omega
  · rintro ⟨j0', hj0', huniq⟩
    refine ⟨A.length + j0', (nextR_append_right A T i j0' j1).2 hj0', ?_⟩
    intro y hy
    have hge := nextR_src_in_T A T hroot hpos hy
    obtain ⟨y', rfl⟩ : ∃ y', y = A.length + y' := ⟨y - A.length, by omega⟩
    have := huniq y' ((nextR_append_right A T i y' j1).1 hy)
    omega

theorem parent_append_right (A T : TrioSeq) (hroot : entry T 0 0 = 0)
    {i j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (hpT : hasParent T i j1) :
    parent (A ++ T) i (A.length + j1) = A.length + parent T i j1 := by
  have hpM : hasParent (A ++ T) i (A.length + j1) :=
    (hasParent_append_right A T hroot hpos).2 hpT
  exact hpM.unique (parent_nextR hpM)
    ((nextR_append_right A T i (parent T i j1) j1).2 (parent_nextR hpT))

theorem take_append_right (A T : TrioSeq) (j : ℕ) :
    (A ++ T).take (A.length + j) = A ++ T.take j := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- A single shifted copy-block reading `entry (A ++ T)` (with its guards)
equals the copy-block reading `entry T`. -/
theorem copyblock_append (A T : TrioSeq) (r a m k d0 d1 : ℕ) :
    (List.range' (A.length + a) m).map
      (fun j => (entry (A ++ T) 0 j
          + (if le0 (A ++ T) (A.length + r) j then k * d0 else 0),
        entry (A ++ T) 1 j
          + (if le1 (A ++ T) (A.length + r) j then k * d1 else 0),
        entry (A ++ T) 2 j))
    = (List.range' a m).map
      (fun j => (entry T 0 j + (if le0 T r j then k * d0 else 0),
        entry T 1 j + (if le1 T r j then k * d1 else 0),
        entry T 2 j)) := by
  have hshift : List.range' (A.length + a) m = (List.range' a m).map (A.length + ·) := by
    rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map]
    congr 1; funext x; simp; omega
  rw [hshift, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  rw [entry_append_right, entry_append_right, entry_append_right]
  rw [if_congr (le0_append_right A T r j) rfl rfl,
    if_congr (le1_append_right A T r j) rfl rfl]

theorem Pred_append_right (A T : TrioSeq) (hT : 2 ≤ T.length) :
    Pred (A ++ T) = A ++ Pred T := by
  unfold Pred
  rw [List.length_append, if_neg (by omega), if_neg (by omega),
    List.dropLast_append_of_ne_nil]
  intro h; rw [h] at hT; simp at hT

theorem no_hasParent_of_row0_zero {M : TrioSeq} {i j1 : ℕ}
    (hz : entry M 0 j1 = 0) (hp : hasParent M i j1) : False := by
  obtain ⟨j0, hj0, -⟩ := hp
  obtain ⟨-, -, hrt⟩ := nextR_le0 hj0
  exact absurd (rtg_to_root hz hrt) (Nat.ne_of_lt (nextR_index_lt hj0))

/-- **`oper`-prefix-commute**: `oper (A ++ T) n = A ++ oper T n` for `T`
root-anchored with `2 ≤ |T|`. -/
theorem oper_append_right (A T : TrioSeq) (n : ℕ) (hT : 2 ≤ T.length)
    (hroot : entry T 0 0 = 0) :
    oper (A ++ T) n = A ++ oper T n := by
  have hlenAT : (A ++ T).length - 1 = A.length + (T.length - 1) := by
    rw [List.length_append]; omega
  unfold oper
  set j1 := T.length - 1 with hj1
  rw [hlenAT]
  have hne_AT : ¬ (A.length + j1 = 0) := by omega
  have hne_T : ¬ (j1 = 0) := by omega
  rw [if_neg hne_AT, if_neg hne_T]
  have he0 : entry (A ++ T) 0 (A.length + j1) = entry T 0 j1 := entry_append_right A T 0 j1
  have he1 : entry (A ++ T) 1 (A.length + j1) = entry T 1 j1 := entry_append_right A T 1 j1
  have he2 : entry (A ++ T) 2 (A.length + j1) = entry T 2 j1 := entry_append_right A T 2 j1
  rw [he0, he1, he2]
  by_cases hz : entry T 0 j1 = 0 ∧ entry T 1 j1 = 0 ∧ entry T 2 j1 = 0
  · rw [if_pos hz, if_pos hz]; exact Pred_append_right A T hT
  · rw [if_neg hz, if_neg hz]
    have hidx : srow (A ++ T) (A.length + j1) = srow T j1 := srow_append_right A T j1
    rw [hidx]
    by_cases hp : hasParent T (srow T j1) j1
    · have hpos : 0 < entry (A ++ T) 0 (A.length + j1) := by
        rw [he0]
        by_contra hzero; push_neg at hzero
        exact no_hasParent_of_row0_zero (by omega) hp
      have hpAT : hasParent (A ++ T) (srow T j1) (A.length + j1) :=
        (hasParent_append_right A T hroot hpos).2 hp
      rw [if_neg (not_not.2 hpAT), if_neg (not_not.2 hp)]
      have hpar : parent (A ++ T) (srow T j1) (A.length + j1)
          = A.length + parent T (srow T j1) j1 := parent_append_right A T hroot hpos hp
      set j0 := parent T (srow T j1) j1 with hj0
      simp only [hpar]
      have hd0 : entry T 0 j1 - entry (A ++ T) 0 (A.length + j0)
          = entry T 0 j1 - entry T 0 j0 := by
        rw [entry_append_right]
      have hd1 : entry T 1 j1 - entry (A ++ T) 1 (A.length + j0)
          = entry T 1 j1 - entry T 1 j0 := by
        rw [entry_append_right]
      rw [hd0, hd1]
      have hrange : (A.length + j1) - (A.length + j0) = j1 - j0 := by omega
      rw [hrange, take_append_right, List.append_assoc]
      congr 1
      congr 1
      apply List.flatMap_congr
      intro k _
      exact copyblock_append A T j0 j0 (j1 - j0) k _ _
    · have hpAT : ¬ hasParent (A ++ T) (srow T j1) (A.length + j1) := by
        intro hh
        by_cases hpos : 0 < entry (A ++ T) 0 (A.length + j1)
        · exact hp ((hasParent_append_right A T hroot hpos).1 hh)
        · exact no_hasParent_of_row0_zero (by omega) hh
      rw [if_pos hp, if_pos hpAT]
      exact Pred_append_right A T hT

/-! ## 位置的不変量の定義と基底 -/

/-- 行 1 の規律: 行 0 が正の列には行 0 の親（ちょうど 1 段下、間に谷なし）が
あり、行 1 は親より高々 1 大きい。 -/
def r1ok (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → 0 < (M.getD j (0, 0, 0)).1 →
    ∃ k, k < j ∧ (M.getD k (0, 0, 0)).1 + 1 = (M.getD j (0, 0, 0)).1
      ∧ (∀ l, k < l → l < j → (M.getD j (0, 0, 0)).1 ≤ (M.getD l (0, 0, 0)).1)
      ∧ (M.getD j (0, 0, 0)).2.1 ≤ (M.getD k (0, 0, 0)).2.1 + 1

/-- 行 0 が 0 の列はラベルも 0。 -/
def z0ok (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → (M.getD j (0, 0, 0)).1 = 0 →
    (M.getD j (0, 0, 0)).2.1 = 0 ∧ (M.getD j (0, 0, 0)).2.2 = 0

/-- ラベル対は非増加（行 1 ≥ 行 2、BMOCF の Idx 条件）。 -/
def noninc (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → (M.getD j (0, 0, 0)).2.2 ≤ (M.getD j (0, 0, 0)).2.1

/- NOTE (2026-08-03): the all-pairs window-bound invariant `W2ok` that used to live
here is FALSE on `ST_TS` (counterexample line: … (0,0,0)(1,1,1)(2,0,0)(2,0,0) …),
and so is `A_x1 ≡ 1`.  Guarded (non-uniform) copies are real; the live route is the
chain-window characterization of `le1` (path lemma) plus the `lsub` heartwood lift
on terms.  See `Lift.lean`. -/

theorem diagSeqT_length (v : ℕ) : (diagSeqT 0 v).length = v + 1 := by
  unfold diagSeqT
  rw [List.length_map, List.length_range']
  omega

theorem diagSeqT_getD {v i : ℕ} (hi : i < v + 1) :
    (diagSeqT 0 v).getD i (0, 0, 0) = (i, i, min i 1) := by
  unfold diagSeqT
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hi)]
  simp

theorem r1ok_diagSeqT (v : ℕ) : r1ok (diagSeqT 0 v) := by
  intro j hj hpos
  rw [diagSeqT_length] at hj
  rw [diagSeqT_getD hj] at hpos
  have hj0 : 0 < j := by simpa using hpos
  refine ⟨j - 1, by omega, ?_, ?_, ?_⟩
  · rw [diagSeqT_getD hj, diagSeqT_getD (show j - 1 < v + 1 by omega)]
    show j - 1 + 1 = j
    omega
  · intro l hl1 hl2
    omega
  · rw [diagSeqT_getD hj, diagSeqT_getD (show j - 1 < v + 1 by omega)]
    show j ≤ (j - 1) + 1
    omega

theorem z0ok_diagSeqT (v : ℕ) : z0ok (diagSeqT 0 v) := by
  intro j hj h0
  rw [diagSeqT_length] at hj
  rw [diagSeqT_getD hj] at h0 ⊢
  simp at h0
  subst h0
  simp

theorem noninc_diagSeqT (v : ℕ) : noninc (diagSeqT 0 v) := by
  intro j hj
  rw [diagSeqT_length] at hj
  rw [diagSeqT_getD hj]
  show min j 1 ≤ j
  omega

/-! ## take / dropLast への遺伝 -/

theorem getD_take {M : TrioSeq} {m j : ℕ} (h : j < m) :
    (M.take m).getD j (0, 0, 0) = M.getD j (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos h]

theorem r1ok_take {M : TrioSeq} (h : r1ok M) (m : ℕ) : r1ok (M.take m) := by
  intro j hj hpos
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [getD_take hjm] at hpos
  obtain ⟨k, hk, he, hbetween, hsnd⟩ := h j hjM hpos
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · rw [getD_take (lt_trans hk hjm), getD_take hjm]
    exact he
  · intro l hl1 hl2
    rw [getD_take hjm, getD_take (lt_trans hl2 hjm)]
    exact hbetween l hl1 hl2
  · rw [getD_take hjm, getD_take (lt_trans hk hjm)]
    exact hsnd

theorem r1ok_dropLast {M : TrioSeq} (h : r1ok M) : r1ok M.dropLast := by
  rw [List.dropLast_eq_take]
  exact r1ok_take h _

theorem z0ok_take {M : TrioSeq} (h : z0ok M) (m : ℕ) : z0ok (M.take m) := by
  intro j hj h0
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [getD_take hjm] at h0 ⊢
  exact h j hjM h0

theorem z0ok_dropLast {M : TrioSeq} (h : z0ok M) : z0ok M.dropLast := by
  rw [List.dropLast_eq_take]
  exact z0ok_take h _

theorem noninc_take {M : TrioSeq} (h : noninc M) (m : ℕ) : noninc (M.take m) := by
  intro j hj
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [getD_take hjm]
  exact h j hjM

theorem noninc_dropLast {M : TrioSeq} (h : noninc M) : noninc M.dropLast := by
  rw [List.dropLast_eq_take]
  exact noninc_take h _

/-! ## コピー分解の添字計算 -/

theorem getD_append_left {G X : TrioSeq} {i : ℕ} (h : i < G.length) :
    (G ++ X).getD i (0, 0, 0) = G.getD i (0, 0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

theorem index_decomp {i L n : ℕ} (hL : 0 < L) (hi : i < n * L) :
    ∃ k q, k < n ∧ q < L ∧ i = k * L + q := by
  refine ⟨i / L, i % L, ?_, Nat.mod_lt _ hL, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hL).2 hi
  · calc i = L * (i / L) + i % L := (Nat.div_add_mod i L).symm
    _ = i / L * L + i % L := by rw [Nat.mul_comm]

theorem copies_map_length (B : TrioSeq) (f : ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (n : ℕ) :
    ((List.range n).flatMap fun k => B.map (f k)).length = n * B.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp [ih, Nat.succ_mul]

theorem copies_map_getD {B : TrioSeq} {n k q : ℕ} {f : ℕ → ℕ × ℕ × ℕ → ℕ × ℕ × ℕ}
    (hk : k < n) (hq : q < B.length) :
    ((List.range n).flatMap fun k => B.map (f k)).getD (k * B.length + q) (0, 0, 0)
      = f k (B.getD q (0, 0, 0)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hkn : k < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left,
        ← List.getD_eq_getElem?_getD]
      · exact ih hkn
      · rw [copies_map_length]
        calc k * B.length + q < k * B.length + B.length := by omega
        _ = (k + 1) * B.length := (Nat.succ_mul k B.length).symm
        _ ≤ n * B.length := Nat.mul_le_mul_right _ hkn
    · have hk_eq : k = n := by omega
      subst hk_eq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
          (by rw [copies_map_length]; exact Nat.le_add_right _ _),
        copies_map_length, Nat.add_sub_cancel_left]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.getElem?_map, List.getElem?_eq_getElem hq]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      rfl

/-- 一様コピー展開（悪い分岐の形、両行のシフト付き）。 -/
def copyExp (G B : TrioSeq) (d0 d1 n : ℕ) : TrioSeq :=
  G ++ (List.range n).flatMap fun k =>
    B.map fun p => (p.1 + k * d0, p.2.1 + k * d1, p.2.2)

theorem copyExp_length (G B : TrioSeq) (d0 d1 n : ℕ) :
    (copyExp G B d0 d1 n).length = G.length + n * B.length := by
  unfold copyExp
  rw [List.length_append, copies_map_length]

theorem copyExp_getD_pre {G B : TrioSeq} {d0 d1 n i : ℕ} (h : i < G.length) :
    (copyExp G B d0 d1 n).getD i (0, 0, 0) = G.getD i (0, 0, 0) :=
  getD_append_left h

theorem copyExp_getD_copy {G B : TrioSeq} {d0 d1 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) :
    (copyExp G B d0 d1 n).getD (G.length + (k * B.length + q)) (0, 0, 0)
      = ((B.getD q (0, 0, 0)).1 + k * d0,
         (B.getD q (0, 0, 0)).2.1 + k * d1,
         (B.getD q (0, 0, 0)).2.2) := by
  unfold copyExp
  rw [getD_app_right _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    copies_map_getD hk hq]

theorem hostM_getD_pre {G B : TrioSeq} {lp : ℕ × ℕ × ℕ} {i : ℕ} (h : i < G.length) :
    (G ++ B ++ [lp]).getD i (0, 0, 0) = G.getD i (0, 0, 0) := by
  rw [getD_append_left (by simp; omega), getD_append_left h]

theorem hostM_getD_blk {G B : TrioSeq} {lp : ℕ × ℕ × ℕ} {q : ℕ} (hq : q < B.length) :
    (G ++ B ++ [lp]).getD (G.length + q) (0, 0, 0) = B.getD q (0, 0, 0) := by
  rw [getD_append_left (by simp; omega),
    getD_app_right _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem hostM_length (G B : TrioSeq) (lp : ℕ × ℕ × ℕ) :
    (G ++ B ++ [lp]).length = G.length + B.length + 1 := by
  simp
  omega

end Googology.Trans.BMS.TrioCof
