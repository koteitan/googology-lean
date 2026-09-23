/-
Ported verbatim from koteitan/trio, `lean/Decrease.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Decrease.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
**展開の 1 歩は測度を真に減らす**（トリオ数列, BM4）。

`oper` の分岐の展開、悪い分岐のコピー分解、そして減少定理
`m_step_decreases : translate (M⟦n⟧) <o translate M`（`1 < |M|`, `1 ≤ n`）。

2 行の Decrease.lean と同じ骨格。トリオで変わる点:
- 行 0 の上昇ガード `A_x0` は悪い部分で常に真（`le0_interval_desc`）なので消える
- 行 1 の上昇ガード `A_x1` は残るが、減少には無関係（添字対優先順序では
  コピー先頭の lead 対だけが効き、内部の添字は比較に現れない）
- 上昇コピーの核は lead **対**の支配で閉じる: `i1 = 1` は第 1 成分、
  `i1 = 2` は第 1 成分が一致して第 2 成分（`nextrel2` の行 2 の減少）
-/
import Googology.Trans.BMS.TrioCof.Term

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-! ### The branches of `oper`, unfolded -/

theorem oper_eq_self_of_short {M : TrioSeq} (n : ℕ) (h : M.length - 1 = 0) :
    M⟦n⟧ = M := by
  simp only [oper]
  rw [if_pos h]

/-- `Pred` branch 1: the last column is `(0,0,0)`. -/
theorem oper_eq_pred_of_zero {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0) :
    M⟦n⟧ = Pred M := by
  simp only [oper]
  rw [if_neg hL, if_pos hz]

/-- `Pred` branch 2: no unique parent in row `i1`. -/
theorem oper_eq_pred_of_noParent {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : ¬ hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    M⟦n⟧ = Pred M := by
  simp only [oper]
  rw [if_neg hL, if_neg hz, if_pos hp]

/-- The bad branch of `M⟦n⟧`, unfolded. -/
theorem oper_bad_unfold {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    M⟦n⟧ = M.take (parent M (srow M (M.length - 1)) (M.length - 1))
      ++ (List.range n).flatMap fun k =>
          (List.range' (parent M (srow M (M.length - 1)) (M.length - 1))
            (M.length - 1 - parent M (srow M (M.length - 1)) (M.length - 1))).map
            fun j =>
              (entry M 0 j
                 + (if le0 M (parent M (srow M (M.length - 1)) (M.length - 1)) j
                    then k * (if 0 < srow M (M.length - 1)
                      then entry M 0 (M.length - 1)
                        - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
                      else 0)
                    else 0),
               entry M 1 j
                 + (if le1 M (parent M (srow M (M.length - 1)) (M.length - 1)) j
                    then k * (if 1 < srow M (M.length - 1)
                      then entry M 1 (M.length - 1)
                        - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
                      else 0)
                    else 0),
               entry M 2 j) := by
  simp only [oper]
  rw [if_neg hL, if_neg hz, if_neg (not_not_intro hp)]

/-! ## Appending a column strictly increases the measure -/

theorem translate_snoc_increase (C : TrioSeq) (m : ℕ × ℕ × ℕ) :
    translate C <o translate (C ++ [m]) := by
  induction C using translate.induct with
  | case1 => simp [translate]
  | case2 p rest ih1 ih2 =>
    by_cases allp : ∀ x ∈ rest, p.1 < x.1
    · have allp' : ∀ x ∈ rest, (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        intro x hx; simpa using allp x hx
      have tw : rest.takeWhile (fun q => p.1 < q.1) = rest :=
        List.takeWhile_eq_self_iff.2 allp'
      have dw : rest.dropWhile (fun q => p.1 < q.1) = [] :=
        List.dropWhile_eq_nil_iff.2 allp'
      by_cases hm : p.1 < m.1
      · have all' : ∀ x ∈ rest ++ [m],
            (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact allp' x hx
          · simp at hx
            simpa [hx] using hm
        have key : translate rest <o translate (rest ++ [m]) := by
          rw [tw] at ih1; exact ih1
        have eL : translate (p :: rest) = P p.2.1 p.2.2 (translate rest) Z :=
          translate_single_tree allp
        have eR : translate (p :: (rest ++ [m]))
            = P p.2.1 p.2.2 (translate (rest ++ [m])) Z :=
          translate_single_tree (by
            intro x hx
            rcases List.mem_append.1 hx with hx | hx
            · exact allp x hx
            · simp at hx
              simpa [hx] using hm)
        rw [List.cons_append, eL, eR]
        exact olt_P_b _ _ _ _ key
      · have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1) = rest := by
          rw [takeWhile_append_all allp']
          simp [hm]
        have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1) = [m] := by
          rw [dropWhile_append_all allp']
          simp [hm]
        have eL : translate (p :: rest) = P p.2.1 p.2.2 (translate rest) Z :=
          translate_single_tree allp
        have eR : translate (p :: (rest ++ [m]))
            = P p.2.1 p.2.2 (translate rest) (translate [m]) := by
          rw [translate, tw', dw']
        rw [List.cons_append, eL, eR]
        exact olt_P_c _ _ _ (by simp [translate])
    · push Not at allp
      obtain ⟨x, hx, hnx⟩ := allp
      have hnx' : ¬ (fun q : ℕ × ℕ × ℕ => decide (p.1 < q.1)) x = true := by
        simpa using hnx
      have tw' : (rest ++ [m]).takeWhile (fun q => p.1 < q.1)
          = rest.takeWhile (fun q => p.1 < q.1) := takeWhile_append_not hx hnx'
      have dw' : (rest ++ [m]).dropWhile (fun q => p.1 < q.1)
          = rest.dropWhile (fun q => p.1 < q.1) ++ [m] := dropWhile_append_not hx hnx'
      have eL : translate (p :: rest)
          = P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate (rest.dropWhile fun q => p.1 < q.1)) := by
        rw [translate]
      have eR : translate (p :: (rest ++ [m]))
          = P p.2.1 p.2.2 (translate (rest.takeWhile fun q => p.1 < q.1))
              (translate ((rest.dropWhile fun q => p.1 < q.1) ++ [m])) := by
        rw [translate, tw', dw']
      rw [List.cons_append, eL, eR]
      exact olt_P_c _ _ _ ih2

theorem translate_dropLast_decrease {C : TrioSeq} (h : C ≠ []) :
    translate C.dropLast <o translate C := by
  conv_rhs => rw [← List.dropLast_append_getLast h]
  exact translate_snoc_increase _ _

/-! ## Abstract bad-step cores -/

/-- Core for `i1 = 0` (exact copies). -/
theorem core_i0 {v0 w1 w2 : ℕ} {R T : TrioSeq} {lp : ℕ × ℕ × ℕ}
    (hR : ∀ x ∈ R, v0 < x.1) (vl : v0 < lp.1)
    (hT : T = [] ∨ ¬ v0 < (T.headI).1) :
    translate (((v0, w1, w2) :: R) ++ T) <o translate (((v0, w1, w2) :: R) ++ [lp]) := by
  have lhs : translate (((v0, w1, w2) :: R) ++ T)
      = P w1 w2 (translate R) (translate T) :=
    translate_block_append hR hT
  have rhs : translate (((v0, w1, w2) :: R) ++ [lp])
      = P w1 w2 (translate (R ++ [lp])) Z := by
    have all : ∀ x ∈ R ++ [lp], ((v0, w1, w2) : ℕ × ℕ × ℕ).1 < x.1 := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hR x hx
      · simp at hx
        simpa [hx] using vl
    calc translate (((v0, w1, w2) :: R) ++ [lp])
        = translate ((v0, w1, w2) :: (R ++ [lp])) := by rw [List.cons_append]
      _ = P w1 w2 (translate (R ++ [lp])) Z := translate_single_tree all
  rw [lhs, rhs]
  exact olt_P_b _ _ _ _ (translate_snoc_increase R lp)

/-- Core for the ascending copies (`i1 ∈ {1, 2}`).  The copy-rest is a single
tree rooted at the same row-0 as the dropped last column but with a
lexicographically smaller subscript pair; so it is dominated by `[lp]` and the
common bodies propagate the comparison. -/
theorem core_asc {v0 w1 w2 : ℕ} {R : TrioSeq} {c : ℕ × ℕ × ℕ} {C' : TrioSeq}
    {lp : ℕ × ℕ × ℕ}
    (hR : ∀ x ∈ R, v0 < x.1)
    (Cge : ∀ x ∈ C', c.1 ≤ x.1)
    (Croot : c.1 = lp.1)
    (lpv : v0 < lp.1)
    (lead_lt : c.2.1 < lp.2.1 ∨ (c.2.1 = lp.2.1 ∧ c.2.2 < lp.2.2)) :
    translate (((v0, w1, w2) :: R) ++ (c :: C'))
      <o translate (((v0, w1, w2) :: R) ++ [lp]) := by
  have hCdom : translate (c :: C') <o translate [lp] := by
    have leadC : lead (translate (c :: C')) = (c.2.1, c.2.2) := by
      rw [lead_translate]
    have : translate (c :: C') <o P lp.2.1 lp.2.2 Z Z :=
      olt_P_of_lead_lt _ _ (Or.inr (by rw [leadC]; simpa using lead_lt))
    calc translate (c :: C') <o P lp.2.1 lp.2.2 Z Z := this
      _ = translate [lp] := by
          rw [translate]
          simp [translate]
  have inner : translate (R ++ c :: C') <o translate (R ++ lp :: ([] : TrioSeq)) :=
    translate_ctx_cong hCdom Croot Cge (by simp) R
  have allRC : ∀ x ∈ R ++ c :: C', ((v0, w1, w2) : ℕ × ℕ × ℕ).1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact lt_of_lt_of_eq lpv Croot.symm
      · exact lt_of_lt_of_le (lt_of_lt_of_eq lpv Croot.symm) (Cge x hx)
  have allRlp : ∀ x ∈ R ++ [lp], ((v0, w1, w2) : ℕ × ℕ × ℕ).1 < x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hR x hx
    · simp at hx
      simpa [hx] using lpv
  have lhs : translate (((v0, w1, w2) :: R) ++ (c :: C'))
      = P w1 w2 (translate (R ++ c :: C')) Z := by
    rw [List.cons_append]
    exact translate_single_tree allRC
  have rhs : translate (((v0, w1, w2) :: R) ++ [lp])
      = P w1 w2 (translate (R ++ [lp])) Z := by
    rw [List.cons_append]
    exact translate_single_tree allRlp
  rw [lhs, rhs]
  exact olt_P_b _ _ _ _ (by simpa using inner)

/-! ## The `Pred` branches decrease -/

theorem translate_oper_pred {M : TrioSeq} (n : ℕ) (L : 1 < M.length)
    (br : (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0)
      ∨ ¬ hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    translate (M⟦n⟧) <o translate M := by
  have j1ne : M.length - 1 ≠ 0 := by omega
  have hMn : M⟦n⟧ = Pred M := by
    rcases br with hz | hp
    · exact oper_eq_pred_of_zero n j1ne hz
    · by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
          entry M 2 (M.length - 1) = 0
      · exact oper_eq_pred_of_zero n j1ne hz
      · exact oper_eq_pred_of_noParent n j1ne hz hp
  have hPred : Pred M = M.dropLast := by
    unfold Pred
    rw [if_neg (by omega)]
  rw [hMn, hPred]
  exact translate_dropLast_decrease (by
    intro h
    rw [h] at L
    simp at L)

/-! ## The bad branch -/

theorem parent_nextR {M : TrioSeq} {i j1 : ℕ} (hp : hasParent M i j1) :
    nextR M i (parent M i j1) j1 :=
  Classical.epsilon_spec hp.exists

theorem nextR_index_lt {M : TrioSeq} {i j0 j1 : ℕ} (h : nextR M i j0 j1) :
    j0 < j1 := by
  unfold nextR at h
  split at h
  · exact h.2.2.1
  · split at h
    · exact h.2.2.1
    · exact h.2.2.1

theorem nextR_chain0 {M : TrioSeq} {i j0 j1 : ℕ} (h : nextR M i j0 j1) :
    Relation.ReflTransGen (nextrel0 M) j0 j1 := by
  unfold nextR at h
  split at h
  · exact Relation.ReflTransGen.single h
  · split at h
    · exact h.2.2.2.2.1.2.2
    · exact rtg1_to_rtg0 h.2.2.2.2.1.2.2

open Classical in
/-- **Uniform copies.**  Under the row-1 descendance hypothesis `hA`
(discharged on standard forms by the window bound and `le1_window_desc`,
and vacuous when `d1 = 0`), both ascension guards collapse and the copies
become uniform shifts, as in the two-row system. -/
theorem oper_bad_uniform {M : TrioSeq} (n : ℕ) {i1 j0 d0 d1 : ℕ}
    (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hi1 : i1 = srow M (M.length - 1))
    (hj0 : j0 = parent M i1 (M.length - 1))
    (hd0 : d0 = if 0 < i1 then entry M 0 (M.length - 1) - entry M 0 j0 else 0)
    (hd1 : d1 = if 1 < i1 then entry M 1 (M.length - 1) - entry M 1 j0 else 0)
    (hA : ∀ j, j0 ≤ j → j < M.length - 1 → le1 M j0 j ∨ d1 = 0) :
    M⟦n⟧ = M.take j0 ++ (List.range n).flatMap fun k =>
      (List.range' j0 (M.length - 1 - j0)).map fun j =>
        (entry M 0 j + k * d0, entry M 1 j + k * d1, entry M 2 j) := by
  subst hi1
  subst hj0
  subst hd0
  subst hd1
  have np := parent_nextR hp
  have j0lt : parent M (srow M (M.length - 1)) (M.length - 1) < M.length - 1 :=
    nextR_index_lt np
  have chain := nextR_chain0 np
  have hdesc := le0_interval_desc chain (by omega)
  rw [oper_bad_unfold n hL hz hp]
  congr 1
  congr 1
  funext k
  apply List.map_congr_left
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
  have hg0 : le0 M (parent M (srow M (M.length - 1)) (M.length - 1))
      (parent M (srow M (M.length - 1)) (M.length - 1) + 1 * i) :=
    ⟨by omega, by omega, hdesc _ (by omega) (by omega)⟩
  rcases hA (parent M (srow M (M.length - 1)) (M.length - 1) + 1 * i)
      (by omega) (by omega) with h | h
  · rw [if_pos hg0, if_pos h]
  · rw [if_pos hg0, h]
    simp


theorem translate_oper_bad {M : TrioSeq} {n : ℕ} (L : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1))
    (hn : 1 ≤ n) :
    translate (M⟦n⟧) <o translate M := by
  have np : nextR M (srow M (M.length - 1))
      (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1) :=
    parent_nextR hp
  set j1 := M.length - 1 with hj1
  set i1 := srow M j1 with hi1
  set j0 := parent M i1 j1 with hj0
  have j0lt : j0 < j1 := nextR_index_lt np
  have chain : Relation.ReflTransGen (nextrel0 M) j0 j1 := nextR_chain0 np
  have iv : ∀ k, j0 < k → k ≤ j1 → entry M 0 j0 < entry M 0 k :=
    fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
  have hdesc : ∀ j, j0 ≤ j → j ≤ j1 → Relation.ReflTransGen (nextrel0 M) j0 j :=
    le0_interval_desc chain (by omega)
  set d0 := (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0) with hd0
  set d1 := (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) with hd1
  -- the copies, with the row-0 guard discharged by `le0_interval_desc`
  set B : ℕ → TrioSeq := fun k => (List.range' j0 (j1 - j0)).map
      (fun j => (entry M 0 j + k * d0,
                 entry M 1 j + (if le1 M j0 j then k * d1 else 0),
                 entry M 2 j)) with hBdef
  have hcopy : (fun k => (List.range' j0 (j1 - j0)).map fun j =>
      (entry M 0 j + (if le0 M j0 j then k * d0 else 0),
       entry M 1 j + (if le1 M j0 j then k * d1 else 0),
       entry M 2 j)) = B := by
    funext k
    rw [hBdef]
    apply List.map_congr_left
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
    rw [if_pos (show le0 M j0 (j0 + 1 * i) from
      ⟨by omega, by omega, hdesc _ (by omega) (by omega)⟩)]
  have hMn : M⟦n⟧ = M.take j0 ++ (List.range n).flatMap B := by
    rw [oper_bad_unfold n (by omega) hz hp]
    show M.take j0 ++ (List.range n).flatMap (fun k =>
        (List.range' j0 (j1 - j0)).map fun j =>
          (entry M 0 j + (if le0 M j0 j then k * d0 else 0),
           entry M 1 j + (if le1 M j0 j then k * d1 else 0),
           entry M 2 j)) = _
    rw [hcopy]
  -- the base block and the last column
  set R := (List.range' (j0 + 1) (j1 - (j0 + 1))).map (fun j => M.getD j (0, 0, 0))
    with hRdef
  set lp := M.getD j1 (0, 0, 0) with hlp
  have hsplit : List.range' j0 (j1 - j0) = j0 :: List.range' (j0 + 1) (j1 - (j0 + 1)) := by
    have h : j1 - j0 = (j1 - (j0 + 1)) + 1 := by omega
    rw [h, List.range'_succ]
  have hB0 : B 0 = (entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R := by
    show (List.range' j0 (j1 - j0)).map
        (fun j => (entry M 0 j + 0 * d0,
                   entry M 1 j + (if le1 M j0 j then 0 * d1 else 0),
                   entry M 2 j)) = _
    rw [hsplit]
    simp only [List.map_cons, Nat.zero_mul, Nat.add_zero, ite_self]
    rw [hRdef]
    rfl
  have hM' : M = M.take j0 ++ (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R)
      ++ [lp]) := by
    have dropM : M.drop j0 = (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R)
        ++ [lp]) := by
      rw [drop_eq_map_getD M j0 (0, 0, 0)]
      have hlen' : M.length - j0 = (j1 - j0) + 1 := by omega
      have hras : List.range' j0 ((j1 - j0) + 1)
          = List.range' j0 (j1 - j0) ++ [j1] := by
        have h := List.range'_append (s := j0) (m := j1 - j0) (n := 1) (step := 1)
        rw [List.range'_one] at h
        rw [show j0 + 1 * (j1 - j0) = j1 by omega] at h
        exact h.symm
      rw [hlen', hras, List.map_append, hsplit, List.map_cons, hRdef, hlp,
        getD_eq_entries]
      simp
    conv_lhs => rw [← List.take_append_drop j0 M]
    rw [dropM]
  -- membership facts
  have R_gt : ∀ x ∈ R, entry M 0 j0 < x.1 := by
    intro x hx
    rw [hRdef] at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
    rw [getD_eq_entries]
    exact iv _ (by omega) (by omega)
  have lp_gt : entry M 0 j0 < lp.1 := by
    rw [hlp, getD_eq_entries]
    exact iv j1 j0lt le_rfl
  -- split the copies into the base block and the rest `C`
  have hrange : List.range n = 0 :: List.range' 1 (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [List.range_eq_range', List.range'_succ]
  set C := (List.range' 1 (n - 1)).flatMap B with hC
  have hMn' : M⟦n⟧ = M.take j0 ++ (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R)
      ++ C) := by
    rw [hMn, hrange, List.flatMap_cons, hB0, hC]
  -- `entry M 0 j0` bounds everything in `C`
  have allC_v0 : ∀ x ∈ C, entry M 0 j0 ≤ x.1 := by
    intro x hx
    rw [hC] at hx
    obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hx
    rw [hBdef] at hk
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
    have hv : entry M 0 j0 ≤ entry M 0 (j0 + 1 * i) := by
      rcases Nat.eq_or_lt_of_le (Nat.le_add_right j0 (1 * i)) with h | h
      · rw [← h]
      · exact (iv _ h (by omega)).le
    calc entry M 0 j0 ≤ entry M 0 (j0 + 1 * i) := hv
      _ ≤ entry M 0 (j0 + 1 * i) + k * d0 := Nat.le_add_right _ _
  -- the core: `blk ++ C ≺ blk ++ [lp]`
  have core : translate (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R) ++ C)
      <o translate (((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R) ++ [lp]) := by
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · have : n - 1 = 0 := by omega
      have hCnil : C = [] := by rw [hC, this]; rfl
      exact core_i0 R_gt lp_gt (Or.inl hCnil)
    · -- expose the head of `C`
      have hsplit2 : List.range' 1 (n - 1) = 1 :: List.range' 2 (n - 2) := by
        have : n - 1 = (n - 2) + 1 := by omega
        rw [this, List.range'_succ]
      have hj0le1 : le1 M j0 j0 := ⟨by omega, by omega, .refl⟩
      have hB1 : B 1 = (entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0)
          :: ((List.range' (j0 + 1) (j1 - (j0 + 1))).map
                (fun j => (entry M 0 j + d0,
                           entry M 1 j + (if le1 M j0 j then d1 else 0),
                           entry M 2 j))) := by
        show (List.range' j0 (j1 - j0)).map
            (fun j => (entry M 0 j + 1 * d0,
                       entry M 1 j + (if le1 M j0 j then 1 * d1 else 0),
                       entry M 2 j)) = _
        rw [hsplit]
        simp only [List.map_cons, Nat.one_mul]
        rw [if_pos hj0le1]
      have hCcons : C = (entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0)
          :: (((List.range' (j0 + 1) (j1 - (j0 + 1))).map
                (fun j => (entry M 0 j + d0,
                           entry M 1 j + (if le1 M j0 j then d1 else 0),
                           entry M 2 j)))
              ++ (List.range' 2 (n - 2)).flatMap B) := by
        rw [hC, hsplit2, List.flatMap_cons, hB1, List.cons_append]
      by_cases hi : 0 < i1
      · -- ascending copies
        have d0pos : 0 < d0 := by
          rw [hd0, if_pos hi]
          have := iv j1 j0lt le_rfl
          omega
        have hd0eq : entry M 0 j1 = entry M 0 j0 + d0 := by
          rw [hd0, if_pos hi]
          have := iv j1 j0lt le_rfl
          omega
        have Cge : ∀ x ∈ ((List.range' (j0 + 1) (j1 - (j0 + 1))).map
              (fun j => (entry M 0 j + d0,
                         entry M 1 j + (if le1 M j0 j then d1 else 0),
                         entry M 2 j)))
            ++ (List.range' 2 (n - 2)).flatMap B,
            ((entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0) : ℕ × ℕ × ℕ).1
              ≤ x.1 := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
            obtain ⟨i, hi', rfl⟩ := List.mem_range'.1 hj
            have := iv (j0 + 1 + 1 * i) (by omega) (by omega)
            simp only []
            omega
          · obtain ⟨k, hkmem, hk⟩ := List.mem_flatMap.1 hx
            rw [hBdef] at hk
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
            obtain ⟨i, hi', rfl⟩ := List.mem_range'.1 hj
            have hk2 : 2 ≤ k := by
              have := List.mem_range'.1 hkmem
              omega
            have hv : entry M 0 j0 ≤ entry M 0 (j0 + 1 * i) := by
              rcases Nat.eq_or_lt_of_le (Nat.le_add_right j0 (1 * i)) with h | h
              · rw [← h]
              · exact (iv _ h (by omega)).le
            have hdk : d0 ≤ k * d0 := by
              calc d0 = 1 * d0 := (Nat.one_mul d0).symm
                _ ≤ k * d0 := Nat.mul_le_mul_right d0 (by omega)
            simp only []
            omega
        have Croot : ((entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0)
            : ℕ × ℕ × ℕ).1 = lp.1 := by
          rw [hlp, getD_eq_entries]
          simpa using hd0eq.symm
        have lead_lt :
            ((entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0) : ℕ × ℕ × ℕ).2.1
                < lp.2.1
              ∨ (((entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0)
                  : ℕ × ℕ × ℕ).2.1 = lp.2.1
                ∧ ((entry M 0 j0 + d0, entry M 1 j0 + d1, entry M 2 j0)
                  : ℕ × ℕ × ℕ).2.2 < lp.2.2) := by
          rw [hlp, getD_eq_entries]
          by_cases hi2 : 1 < i1
          · -- `i1 = 2`: the row-1 values meet, row 2 decides
            right
            have np2 : nextrel2 M j0 j1 := by
              have np' := np
              unfold nextR at np'
              rw [if_neg (by omega : ¬ i1 = 0), if_neg (by omega : ¬ i1 = 1)] at np'
              exact np'
            have h1lt : entry M 1 j0 < entry M 1 j1 :=
              rtg1_entry1_lt np2.2.2.2.2.1.2.2 (by omega)
            have hd1eq : d1 = entry M 1 j1 - entry M 1 j0 := by
              rw [hd1, if_pos hi2]
            constructor
            · simp only []
              omega
            · simpa using np2.2.2.2.1
          · -- `i1 = 1`: row 1 decides
            left
            have i1eq : i1 = 1 := by omega
            have np1 : nextrel1 M j0 j1 := by
              have np' := np
              unfold nextR at np'
              rw [if_neg (by omega : ¬ i1 = 0), if_pos i1eq] at np'
              exact np'
            have hd1z : d1 = 0 := by
              rw [hd1, if_neg hi2]
            simp only [hd1z]
            simpa using np1.2.2.2.1
        rw [hCcons]
        exact core_asc R_gt Cge Croot lp_gt lead_lt
      · -- exact copies (`i1 = 0`)
        have hd0z : d0 = 0 := by rw [hd0, if_neg hi]
        apply core_i0 R_gt lp_gt
        right
        rw [hCcons]
        simp [hd0z]
  -- lift through the good part by BADCTX
  have bc : translate (M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: (R ++ C)))
      <o translate (M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: (R ++ [lp]))) := by
    apply translate_ctx_cong
    · have e1 : ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R) ++ C
          = (entry M 0 j0, entry M 1 j0, entry M 2 j0) :: (R ++ C) := by simp
      have e2 : ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: R) ++ [lp]
          = (entry M 0 j0, entry M 1 j0, entry M 2 j0) :: (R ++ [lp]) := by simp
      rw [← e1, ← e2]
      exact core
    · rfl
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact (R_gt x hx).le
      · exact allC_v0 x hx
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact (R_gt x hx).le
      · simp at hx
        simp [hx, lp_gt.le]
  have hMn'' : M⟦n⟧ = M.take j0
      ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: (R ++ C)) := by
    rw [hMn']
    simp
  have hM'' : M = M.take j0
      ++ ((entry M 0 j0, entry M 1 j0, entry M 2 j0) :: (R ++ [lp])) := by
    conv_lhs => rw [hM']
    simp
  rw [hMn'']
  conv_rhs => rw [hM'']
  exact bc

/-! ## The decrease lemma -/

/-- Every expansion step on a sequence of length `> 1` strictly decreases the
measure, regardless of the copy count `n ≥ 1` (and regardless of
standardness). -/
theorem m_step_decreases {M : TrioSeq} {n : ℕ} (L : 1 < M.length) (hn : 1 ≤ n) :
    translate (M⟦n⟧) <o translate M := by
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · exact translate_oper_pred n L (Or.inl hz)
  · by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
    · exact translate_oper_bad L hz hp hn
    · exact translate_oper_pred n L (Or.inr hp)

end Googology.Trans.BMS.TrioCof
