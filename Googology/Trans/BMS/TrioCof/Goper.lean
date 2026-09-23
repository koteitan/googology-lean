/-
Ported verbatim from koteitan/trio, `lean/Goper.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Goper.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Goper.lean: 展開一歩での CNF 保存（無条件）と `cnf_ST_TS`。

`i1 ≤ 1` の枝は一様コピー（`hA` の右選言が自明）で既存の
`cnf_oper_i1eq0`/`cnf_oper_asc` に回し、`i1 = 2` の枝はガード付きコピー
`gcopies` に分解して心材タワー `cnf_gcopiesFrom` で閉じる。窓仮説は不要
（probe: 任意の cnf 行列 125550 展開で違反 0）。
-/
import Googology.Trans.BMS.TrioCof.Gcopy

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-- The `0`-th guarded copy is the plain segment. -/
theorem gcopy_zero (M : TrioSeq) (r L d0 d1 : ℕ) :
    gcopy M r L d0 d1 0 = seg M r L := by
  unfold gcopy seg
  refine List.map_congr_left ?_
  intro j hj
  simp only [Nat.zero_mul, ite_self, Nat.add_zero]

/-- The drop is a segment. -/
theorem drop_seg (M : TrioSeq) (a : ℕ) :
    M.drop a = seg M a (M.length - a) := by
  rw [drop_eq_map_getD M a (0, 0, 0)]
  unfold seg
  refine List.map_congr_left ?_
  intro j hj
  rw [getD_eq_entries]

/-- **The guarded decomposition of the bad branch**: the row-0 guard is
uniformly true on the block, so `M⟦n⟧` is the good part plus guarded copies. -/
theorem oper_gcopies {M : TrioSeq} (n : ℕ) (hL : M.length - 1 ≠ 0)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hp : hasParent M (srow M (M.length - 1)) (M.length - 1)) :
    M⟦n⟧ = M.take (parent M (srow M (M.length - 1)) (M.length - 1))
      ++ gcopies M (parent M (srow M (M.length - 1)) (M.length - 1))
          (M.length - 1 - parent M (srow M (M.length - 1)) (M.length - 1))
          (if 0 < srow M (M.length - 1)
            then entry M 0 (M.length - 1)
              - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
            else 0)
          (if 1 < srow M (M.length - 1)
            then entry M 1 (M.length - 1)
              - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
            else 0)
          n := by
  have np := parent_nextR hp
  have j0lt := nextR_index_lt np
  have chain := nextR_chain0 np
  rw [oper_bad_unfold n hL hz hp]
  congr 1
  unfold gcopies gcopy
  congr 1
  funext k
  refine List.map_congr_left ?_
  intro j hj
  have hjb := List.mem_range'_1.1 hj
  have hle0 : le0 M (parent M (srow M (M.length - 1)) (M.length - 1)) j :=
    ⟨by omega, by omega,
      le0_interval_desc chain (by omega) j hjb.1 (by omega)⟩
  rw [if_pos hle0]

/-- **CNF preservation for the guarded ascending branch** (`i1 = 2`, and in
fact any branch with `d0 > 0` once the lead data is provided). -/
theorem cnf_goper_asc {M : TrioSeq} {r L d0 d1 : ℕ} {G : TrioSeq} {n : ℕ}
    (hL : 1 ≤ L) (hlen : r + L < M.length)
    (hup1 : ∀ j, r < j → j ≤ r + L → entry M 0 r < entry M 0 j)
    (d0pos : 0 < d0)
    (hd0 : entry M 0 (r + L) = entry M 0 r + d0)
    (hglp : le1 M r (r + L) ∨ d1 = 0)
    (lead_lt : entry M 1 r + d1 < entry M 1 (r + L)
      ∨ (entry M 1 r + d1 = entry M 1 (r + L) ∧ entry M 2 r < entry M 2 (r + L)))
    (n1 : 1 ≤ n)
    (cM : cnf (translate (G ++ seg M r (L + 1)))) :
    cnf (translate (G ++ gcopies M r L d0 d1 n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hrb : r < M.length := by omega
  have hupI : ∀ j, r < j → j < r + L → entry M 0 r < entry M 0 j :=
    fun j h1 h2 => hup1 j h1 (by omega)
  obtain ⟨L', hLe⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hsegL : seg M r L
      = (entry M 0 r, entry M 1 r, entry M 2 r) :: seg M (r + 1) (L - 1) := by
    subst hLe
    rw [seg_cons, Nat.add_sub_cancel]
  have hsegcons : seg M r (L + 1)
      = (entry M 0 r, entry M 1 r, entry M 2 r) :: seg M (r + 1) L :=
    seg_cons M r L
  have segsplit : seg M r (L + 1)
      = seg M r L
        ++ [(entry M 0 (r + L), entry M 1 (r + L), entry M 2 (r + L))] :=
    seg_snoc M r L
  -- membership bounds
  have hmemseg : ∀ {a l : ℕ} (x : ℕ × ℕ × ℕ), x ∈ seg M a l →
      ∃ j, a ≤ j ∧ j < a + l ∧ x = (entry M 0 j, entry M 1 j, entry M 2 j) := by
    intro a l x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hjb := List.mem_range'_1.1 hj
    exact ⟨j, hjb.1, hjb.2, rfl⟩
  have hmemtow : ∀ {k0 mm : ℕ} (x : ℕ × ℕ × ℕ),
      x ∈ gcopiesFrom M r L d0 d1 k0 mm →
      ∃ j k', r ≤ j ∧ j < r + L ∧ k0 ≤ k' ∧
        x = (entry M 0 j + k' * d0,
             entry M 1 j + (if le1 M r j then k' * d1 else 0), entry M 2 j) := by
    intro k0 mm x hx
    unfold gcopiesFrom at hx
    obtain ⟨k', hk', hxk⟩ := List.mem_flatMap.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hxk
    have hjb := List.mem_range'_1.1 hj
    have hk'b := List.mem_range'_1.1 hk'
    exact ⟨j, k', hjb.1, hjb.2, hk'b.1, rfl⟩
  have hRgt : ∀ x ∈ seg M (r + 1) (L - 1), entry M 0 r < x.1 := by
    intro x hx
    obtain ⟨j, h1, h2, rfl⟩ := hmemseg x hx
    exact hupI j (by omega) (by omega)
  have hRgt' : ∀ x ∈ seg M (r + 1) L, entry M 0 r < x.1 := by
    intro x hx
    obtain ⟨j, h1, h2, rfl⟩ := hmemseg x hx
    exact hup1 j (by omega) (by omega)
  -- cnf of the block-with-last and of the tower
  have cM' : cnf (translate (G
      ++ (entry M 0 r, entry M 1 r, entry M 2 r) :: seg M (r + 1) L)) := by
    rwa [hsegcons] at cM
  have rT : ∀ x ∈ seg M (r + 1) L,
      ((entry M 0 r, entry M 1 r, entry M 2 r) : ℕ × ℕ × ℕ).1 ≤ x.1 :=
    fun x hx => (hRgt' x hx).le
  have cBlp : cnf (translate (seg M r (L + 1))) := by
    rw [hsegcons]
    exact cnf_tail rT G cM'
  have cTower : cnf (translate (gcopiesFrom M r L d0 d1 0 (m + 1))) :=
    cnf_gcopiesFrom hL hlen hup1 d0pos hd0 hglp lead_lt cBlp (m + 1) 0
  -- the tower in front-split form
  have towsucc : gcopiesFrom M r L d0 d1 0 (m + 1)
      = seg M r L ++ gcopiesFrom M r L d0 d1 1 m := by
    rw [gcopiesFrom_succ, gcopy_zero]
  have hcons1 : gcopiesFrom M r L d0 d1 0 (m + 1)
      = (entry M 0 r, entry M 1 r, entry M 2 r)
        :: (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m) := by
    rw [towsucc, hsegL, List.cons_append]
  -- the decrease against the original tail
  have decr : translate (gcopiesFrom M r L d0 d1 0 (m + 1))
      <o translate (seg M r (L + 1)) := by
    cases m with
    | zero =>
      rw [towsucc, gcopiesFrom_zero, List.append_nil, segsplit]
      exact translate_snoc_increase _ _
    | succ m' =>
      have hhd : gcopiesFrom M r L d0 d1 1 (m' + 1)
          = (entry M 0 r + 1 * d0, entry M 1 r + 1 * d1, entry M 2 r)
            :: (((List.range' (r + 1) (L - 1)).map fun j =>
                ((entry M 0 j + 1 * d0,
                  entry M 1 j + (if le1 M r j then 1 * d1 else 0),
                  entry M 2 j) : ℕ × ℕ × ℕ))
              ++ gcopiesFrom M r L d0 d1 2 m') := by
        rw [gcopiesFrom_succ, gcopy_head M hL hrb, List.cons_append]
      have Cge : ∀ x ∈ ((List.range' (r + 1) (L - 1)).map fun j =>
            ((entry M 0 j + 1 * d0,
              entry M 1 j + (if le1 M r j then 1 * d1 else 0),
              entry M 2 j) : ℕ × ℕ × ℕ))
            ++ gcopiesFrom M r L d0 d1 2 m',
          ((entry M 0 r + 1 * d0, entry M 1 r + 1 * d1,
            entry M 2 r) : ℕ × ℕ × ℕ).1 ≤ x.1 := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
          have hjb := List.mem_range'_1.1 hj
          show entry M 0 r + 1 * d0 ≤ entry M 0 j + 1 * d0
          have := hupI j (by omega) (by omega)
          omega
        · obtain ⟨j, k', h1, h2, h3, rfl⟩ := hmemtow x hx
          show entry M 0 r + 1 * d0 ≤ entry M 0 j + k' * d0
          have he0 : entry M 0 r ≤ entry M 0 j := by
            rcases Nat.eq_or_lt_of_le h1 with rfl | h
            · exact le_rfl
            · exact (hupI j h h2).le
          have hmul : 2 * d0 ≤ k' * d0 := Nat.mul_le_mul_right d0 h3
          have h2d : 2 * d0 = d0 + d0 := by omega
          have h1d : 1 * d0 = d0 := Nat.one_mul d0
          omega
      have core := core_asc (w1 := entry M 1 r) (w2 := entry M 2 r)
        (lp := (entry M 0 (r + L), entry M 1 (r + L), entry M 2 (r + L)))
        (R := seg M (r + 1) (L - 1)) hRgt Cge
        (by
          show entry M 0 r + 1 * d0
            = ((entry M 0 (r + L), entry M 1 (r + L), entry M 2 (r + L))
                : ℕ × ℕ × ℕ).1
          have := Nat.one_mul d0
          simp only []
          omega)
        (by
          show entry M 0 r
            < ((entry M 0 (r + L), entry M 1 (r + L), entry M 2 (r + L))
                : ℕ × ℕ × ℕ).1
          simp only []
          omega)
        (by
          have h1d : 1 * d1 = d1 := Nat.one_mul d1
          rcases lead_lt with h | ⟨h1, h2⟩
          · exact Or.inl (by simp only []; omega)
          · exact Or.inr ⟨by simp only []; omega, by simpa using h2⟩)
      rw [towsucc, hhd, segsplit, hsegL]
      exact core
  -- single-tree shapes and the argument decrease
  have st1 : translate (gcopiesFrom M r L d0 d1 0 (m + 1))
      = P (entry M 1 r) (entry M 2 r)
          (translate (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m))
          Z := by
    rw [hcons1]
    refine translate_single_tree ?_
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hRgt x hx
    · obtain ⟨j, k', h1, h2, h3, rfl⟩ := hmemtow x hx
      show entry M 0 r < entry M 0 j + k' * d0
      have he0 : entry M 0 r ≤ entry M 0 j := by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h
        · exact le_rfl
        · exact (hupI j h h2).le
      have hmul : 1 * d0 ≤ k' * d0 := Nat.mul_le_mul_right d0 h3
      have h1d : 1 * d0 = d0 := Nat.one_mul d0
      omega
  have st2 : translate (seg M r (L + 1))
      = P (entry M 1 r) (entry M 2 r) (translate (seg M (r + 1) L)) Z := by
    rw [hsegcons]
    exact translate_single_tree hRgt'
  have argA : translate (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m)
      <o translate (seg M (r + 1) L) := by
    have d := decr
    rw [st1, st2, olt_P_P] at d
    rcases d with h | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, -, h⟩
    · omega
    · omega
    · exact h
    · exact absurd h (not_olt_Z Z)
  have leadle : ∃ p1 p2 b1 c1 q1 q2 b2 c2,
      translate ((entry M 0 r, entry M 1 r, entry M 2 r)
        :: (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m))
        = P p1 p2 b1 c1
      ∧ translate ((entry M 0 r, entry M 1 r, entry M 2 r) :: seg M (r + 1) L)
        = P q1 q2 b2 c2
      ∧ P p1 p2 b1 Z ≤o P q1 q2 b2 Z := by
    refine ⟨entry M 1 r, entry M 2 r,
      translate (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m), Z,
      entry M 1 r, entry M 2 r, translate (seg M (r + 1) L), Z, ?_, ?_,
      Or.inl (olt_P_b _ _ _ _ argA)⟩
    · rw [← hcons1]
      exact st1
    · rw [← hsegcons]
      exact st2
  have decr' : translate ((entry M 0 r, entry M 1 r, entry M 2 r)
      :: (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m))
      <o translate ((entry M 0 r, entry M 1 r, entry M 2 r) :: seg M (r + 1) L) := by
    rw [← hcons1, ← hsegcons]
    exact decr
  have cTower' : cnf (translate ((entry M 0 r, entry M 1 r, entry M 2 r)
      :: (seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m))) := by
    rw [← hcons1]
    exact cTower
  have r1 : ∀ x ∈ seg M (r + 1) (L - 1) ++ gcopiesFrom M r L d0 d1 1 m,
      ((entry M 0 r, entry M 1 r, entry M 2 r) : ℕ × ℕ × ℕ).1 ≤ x.1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact (hRgt x hx).le
    · obtain ⟨j, k', h1, h2, h3, rfl⟩ := hmemtow x hx
      show entry M 0 r ≤ entry M 0 j + k' * d0
      have he0 : entry M 0 r ≤ entry M 0 j := by
        rcases Nat.eq_or_lt_of_le h1 with rfl | h
        · exact le_rfl
        · exact (hupI j h h2).le
      omega
  have key := cnf_ctx_cong cTower' decr' rfl leadle r1 rT G cM'
  rw [gcopies_eq_from, hcons1]
  exact key

/-! ## 展開一歩での CNF 保存（無条件）と標準形の CNF -/

/-- **CNF is preserved by one expansion step** — no window hypothesis and no
standardness: the `i1 = 2` branch runs through the guarded copies, the
`i1 ≤ 1` branches through the uniform machinery. -/
theorem cnf_oper {M : TrioSeq} {n : ℕ} (hn : 1 ≤ n) (cM : cnf (translate M)) :
    cnf (translate (M⟦n⟧)) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact cM
  · have L1 : 1 < M.length := by omega
    have Mne : M ≠ [] := by
      intro he
      rw [he] at L1
      simp at L1
    have hPred : Pred M = M.dropLast := by
      unfold Pred
      rw [if_neg (by omega)]
    by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz, hPred]
      exact cnf_dropLast Mne cM
    · by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
      · by_cases hi2 : 1 < srow M (M.length - 1)
        · -- the guarded route
          have np := parent_nextR hp
          have j0lt : parent M (srow M (M.length - 1)) (M.length - 1)
              < M.length - 1 := nextR_index_lt np
          have chain := nextR_chain0 np
          have iv : ∀ k, parent M (srow M (M.length - 1)) (M.length - 1) < k →
              k ≤ M.length - 1 →
              entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
                < entry M 0 k :=
            fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
          have np2 : nextrel2 M
              (parent M (srow M (M.length - 1)) (M.length - 1))
              (M.length - 1) := by
            have np' := np
            unfold nextR at np'
            rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
              if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
            exact np'
          have h1lt : entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
              < entry M 1 (M.length - 1) :=
            rtg1_entry1_lt np2.2.2.2.2.1.2.2 (by omega)
          set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
          have hpos : j0 + (M.length - 1 - j0) = M.length - 1 := by omega
          have hMsplit : M = M.take j0 ++ seg M j0 (M.length - 1 - j0 + 1) := by
            conv_lhs => rw [← List.take_append_drop j0 M]
            rw [drop_seg, show M.length - j0 = M.length - 1 - j0 + 1 from by omega]
          have cM2 : cnf (translate (M.take j0
              ++ seg M j0 (M.length - 1 - j0 + 1))) := hMsplit ▸ cM
          rw [oper_gcopies n hL hz hp, if_pos (by omega : 0 < srow M (M.length - 1)),
            if_pos hi2, ← hj0]
          refine cnf_goper_asc (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ hn cM2
          · intro j h1 h2
            rw [hpos] at h2
            exact iv j h1 h2
          · have := iv (M.length - 1) j0lt le_rfl
            omega
          · rw [hpos]
            have := iv (M.length - 1) j0lt le_rfl
            omega
          · rw [hpos]
            exact Or.inl np2.2.2.2.2.1
          · rw [hpos]
            right
            constructor
            · omega
            · exact np2.2.2.2.1
        · -- the uniform route (`i1 ≤ 1`)
          have hA : ∀ j, parent M (srow M (M.length - 1)) (M.length - 1) ≤ j →
              j < M.length - 1 →
              le1 M (parent M (srow M (M.length - 1)) (M.length - 1)) j ∨
              (if 1 < srow M (M.length - 1)
                then entry M 1 (M.length - 1)
                  - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
                else 0) = 0 :=
            fun j h1 h2 => Or.inr (by rw [if_neg hi2])
          obtain ⟨G, v0, w1, w2, R, d0, d1, lp, Meq, Mneq, hR, lpv, disj⟩ :=
            oper_bad_blocks L1 hz hp hn hA
          have cM' : cnf (translate (G ++ ((v0, w1, w2) :: R) ++ [lp])) := Meq ▸ cM
          rw [Mneq]
          rcases disj with ⟨d0z, d1z⟩ | ⟨d0pos, lphd, lead_lt⟩
          · subst d0z
            subst d1z
            rw [copies_replicate]
            exact cnf_oper_i1eq0 hR lpv hn cM'
          · exact cnf_oper_asc hR d0pos lead_lt lphd hn cM'
      · rw [oper_eq_pred_of_noParent n hL hz hp, hPred]
        exact cnf_dropLast Mne cM

/-- **標準形の Cantor 標準形性**: `ST_TS` の全行列の translate は CNF。 -/
theorem cnf_ST_TS {M : TrioSeq} (h : ST_TS M) : cnf (translate M) := by
  induction h with
  | diag v => exact cnf_diag v
  | oper hN hn ih => exact cnf_oper hn ih

end Googology.Trans.BMS.TrioCof
