/-
Ported verbatim from koteitan/trio, `lean/Invariant.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Invariant.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Invariant.lean: 位置的不変量の展開保存（ガード付きコピー上）。

`z0ok`（行 0 が 0 の列はラベルも 0）と `noninc`（行 2 ≤ 行 1）の
`oper` 保存。行 1 の規律 `r1ok` の保存はスパイン⊆D と climb を要する
別区画（続く部分）。
-/
import Googology.Trans.BMS.TrioCof.Goper
import Googology.Trans.BMS.TrioCof.Column

namespace Googology.Trans.BMS.TrioCof

open Classical

/-- Membership shape of a guarded-copies column. -/
theorem mem_gcopies {M : TrioSeq} {r L d0 d1 n : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ gcopies M r L d0 d1 n) :
    ∃ j k, r ≤ j ∧ j < r + L ∧ k < n ∧
      x = (entry M 0 j + k * d0,
           entry M 1 j + (if le1 M r j then k * d1 else 0), entry M 2 j) := by
  unfold gcopies at hx
  obtain ⟨k, hk, hxk⟩ := List.mem_flatMap.1 hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hxk
  have hjb := List.mem_range'_1.1 hj
  have hkb := List.mem_range.1 hk
  exact ⟨j, k, hjb.1, hjb.2, hkb, rfl⟩

theorem getD_mem_of_lt {A : TrioSeq} {j : ℕ} (hj : j < A.length) :
    A.getD j (0, 0, 0) ∈ A := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  exact List.getElem_mem hj

/-- Membership form of `noninc`. -/
theorem noninc_mem {M : TrioSeq} (h : noninc M) {x : ℕ × ℕ × ℕ} (hx : x ∈ M) :
    x.2.2 ≤ x.2.1 := by
  obtain ⟨i, hi, hxe⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hxe] at this
  exact this

theorem noninc_of_mem {M : TrioSeq} (h : ∀ x ∈ M, x.2.2 ≤ x.2.1) : noninc M := by
  intro j hj
  exact h _ (getD_mem_of_lt hj)

/-- Membership form of `z0ok`. -/
theorem z0ok_mem {M : TrioSeq} (h : z0ok M) {x : ℕ × ℕ × ℕ} (hx : x ∈ M)
    (hx0 : x.1 = 0) : x.2.1 = 0 ∧ x.2.2 = 0 := by
  obtain ⟨i, hi, hxe⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hxe] at this
  exact this hx0

theorem z0ok_of_mem {M : TrioSeq} (h : ∀ x ∈ M, x.1 = 0 → x.2.1 = 0 ∧ x.2.2 = 0) :
    z0ok M := by
  intro j hj h0
  exact h _ (getD_mem_of_lt hj) h0

/-- The entry triple at a valid position is a member. -/
theorem entry_triple_mem {M : TrioSeq} {j : ℕ} (hj : j < M.length) :
    ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ) ∈ M := by
  rw [← getD_eq_entries]
  exact getD_mem_of_lt hj

/-- **`noninc` is preserved by the expansion step.** -/
theorem noninc_oper {M : TrioSeq} {n : ℕ} (h : noninc M) : noninc (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact noninc_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact noninc_dropLast h
  case pos =>
    rw [oper_gcopies n hL hz hp]
    refine noninc_of_mem ?_
    intro x hx
    rcases List.mem_append.1 hx with hm | hm
    · exact noninc_mem h (List.mem_of_mem_take hm)
    · obtain ⟨l, k, h1, h2, h3, rfl⟩ := mem_gcopies hm
      have hl : l < M.length := by omega
      have h21 := noninc_mem h (entry_triple_mem hl)
      simp only [] at h21 ⊢
      omega

/-- **`z0ok` is preserved by the expansion step.** -/
theorem z0ok_oper {M : TrioSeq} {n : ℕ} (h : z0ok M) : z0ok (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact z0ok_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact z0ok_dropLast h
  case pos =>
    -- shift data: `d1 > 0` forces `d0 > 0`
    have np := parent_nextR hp
    have j0lt := nextR_index_lt np
    have chain := nextR_chain0 np
    have hd0pos : 0 < srow M (M.length - 1) →
        0 < entry M 0 (M.length - 1)
          - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1)) := by
      intro _
      have := le0_interval_gt chain (M.length - 1) ⟨j0lt, le_rfl⟩
      omega
    rw [oper_gcopies n hL hz hp]
    refine z0ok_of_mem ?_
    intro x hx hx0
    rcases List.mem_append.1 hx with hm | hm
    · exact z0ok_mem h (List.mem_of_mem_take hm) hx0
    · obtain ⟨l, k, h1, h2, h3, rfl⟩ := mem_gcopies hm
      have hl : l < M.length := by omega
      simp only [] at hx0 ⊢
      -- row 0 of the copy column is zero: base is zero and the shift vanishes
      have hbase : entry M 0 l = 0 ∧ k * (if 0 < srow M (M.length - 1)
          then entry M 0 (M.length - 1)
            - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
          else 0) = 0 := by omega
      have hz0 := z0ok_mem h (entry_triple_mem hl) hbase.1
      simp only [] at hz0
      constructor
      · -- the row-1 lift also vanishes
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp [hz0.1]
        · by_cases hi2 : 1 < srow M (M.length - 1)
          · -- `d1 > 0` would force `d0 > 0`, contradicting the zero row 0
            have hd0 := hd0pos (by omega)
            have : k * (entry M 0 (M.length - 1)
                - entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))) = 0 := by
              have := hbase.2
              rwa [if_pos (by omega : 0 < srow M (M.length - 1))] at this
            have hk0 : k = 0 := by
              rcases Nat.mul_eq_zero.1 this with h' | h'
              · exact h'
              · omega
            omega
          · rw [if_neg hi2]
            split_ifs <;> simp [hz0.1]
      · exact hz0.2

/-! ## スパイン補題: 鎖上の節はガードを継承する -/

/-- Any row-0 chain node between `r` and a row-1 descendant `j1` of `r` is
itself a row-1 descendant (the spine of the `t = 2` decomposition lies in the
heartwood).  Immediate from the path lemma. -/
theorem le1_of_chain_le1 {M : TrioSeq} {r x j1 : ℕ} (h : le1 M r j1)
    (hrx : Relation.ReflTransGen (nextrel0 M) r x)
    (hxj : Relation.ReflTransGen (nextrel0 M) x j1) : le1 M r x := by
  have hxb : x < M.length := by
    have h1 := nextrel0_rtrancl_index_le hxj
    have h2 := h.2.1
    omega
  refine (le1_iff_chain_window hxb hrx).2 ?_
  intro y hry hyx hyne
  exact le1_chain_window h.2.2 y hry (hyx.trans hxj) hyne

/-! ## `gcopies` の位置補題 -/

theorem gcopy_getD {M : TrioSeq} {r L d0 d1 k q : ℕ} (hq : q < L) :
    (gcopy M r L d0 d1 k).getD q (0, 0, 0)
      = (entry M 0 (r + q) + k * d0,
         entry M 1 (r + q) + (if le1 M r (r + q) then k * d1 else 0),
         entry M 2 (r + q)) := by
  unfold gcopy
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hq)]
  rw [Nat.one_mul]
  rfl

theorem gcopiesFrom_length (M : TrioSeq) (r L d0 d1 k0 m : ℕ) :
    (gcopiesFrom M r L d0 d1 k0 m).length = m * L := by
  induction m generalizing k0 with
  | zero => rw [gcopiesFrom_zero, Nat.zero_mul]; rfl
  | succ m ih =>
    rw [gcopiesFrom_succ, List.length_append, gcopy_len, ih, Nat.succ_mul]
    omega

theorem gcopiesFrom_getD {M : TrioSeq} {r L d0 d1 : ℕ} :
    ∀ {i q k0 m : ℕ}, i < m → q < L →
      (gcopiesFrom M r L d0 d1 k0 m).getD (i * L + q) (0, 0, 0)
        = (entry M 0 (r + q) + (k0 + i) * d0,
           entry M 1 (r + q)
             + (if le1 M r (r + q) then (k0 + i) * d1 else 0),
           entry M 2 (r + q)) := by
  intro i
  induction i with
  | zero =>
    intro q k0 m hi hq
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [gcopiesFrom_succ, Nat.zero_mul, Nat.zero_add,
      getD_append_left (by rw [gcopy_len]; exact hq), gcopy_getD hq,
      Nat.add_zero]
  | succ i ih =>
    intro q k0 m hi hq
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [gcopiesFrom_succ,
      getD_app_right _ _ (by rw [gcopy_len]; rw [Nat.succ_mul]; omega),
      gcopy_len,
      show (i + 1) * L + q - L = i * L + q from by rw [Nat.succ_mul]; omega,
      ih (by omega) hq]
    rw [show k0 + 1 + i = k0 + (i + 1) from by omega]

theorem gcopies_length (M : TrioSeq) (r L d0 d1 n : ℕ) :
    (gcopies M r L d0 d1 n).length = n * L := by
  rw [gcopies_eq_from, gcopiesFrom_length]

theorem gcopies_getD {M : TrioSeq} {r L d0 d1 k q n : ℕ}
    (hk : k < n) (hq : q < L) :
    (gcopies M r L d0 d1 n).getD (k * L + q) (0, 0, 0)
      = (entry M 0 (r + q) + k * d0,
         entry M 1 (r + q) + (if le1 M r (r + q) then k * d1 else 0),
         entry M 2 (r + q)) := by
  rw [gcopies_eq_from, gcopiesFrom_getD hk hq, Nat.zero_add]

/-! ## 行 1 の規律の保存 -/

/-- The r1ok witness is the unique row-0 Next source. -/
theorem witness_nextrel0 {M : TrioSeq} {j k : ℕ} (hj : j < M.length) (hk : k < j)
    (hlev : (M.getD k (0, 0, 0)).1 + 1 = (M.getD j (0, 0, 0)).1)
    (hwin : ∀ l, k < l → l < j → (M.getD j (0, 0, 0)).1 ≤ (M.getD l (0, 0, 0)).1) :
    nextrel0 M k j := by
  refine ⟨by omega, hj, hk, ?_, ?_⟩
  · show entry M 0 k < entry M 0 j
    have e1 : entry M 0 k = (M.getD k (0, 0, 0)).1 := rfl
    have e2 : entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl
    omega
  · intro l ⟨h1, h2⟩
    show entry M 0 j ≤ entry M 0 l
    have e1 : entry M 0 l = (M.getD l (0, 0, 0)).1 := rfl
    have e2 : entry M 0 j = (M.getD j (0, 0, 0)).1 := rfl
    have := hwin l h1 h2
    omega

/-- **Row-1 discipline is preserved by the expansion step.** -/
theorem r1ok_oper {M : TrioSeq} {n : ℕ} (h : r1ok M) : r1ok (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact r1ok_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact r1ok_dropLast h
  case pos =>
    have np := parent_nextR hp
    have j0lt : parent M (srow M (M.length - 1)) (M.length - 1)
        < M.length - 1 := nextR_index_lt np
    have chain := nextR_chain0 np
    have iv : ∀ k, parent M (srow M (M.length - 1)) (M.length - 1) < k →
        k ≤ M.length - 1 →
        entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
          < entry M 0 k :=
      fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
    -- `d1 ≠ 0` gives the `i1 = 2` facts
    have hd1i1 : (if 1 < srow M (M.length - 1)
        then entry M 1 (M.length - 1)
          - entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
        else 0) ≠ 0 →
        le1 M (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1) := by
      intro hne
      by_cases hi2 : 1 < srow M (M.length - 1)
      · have np2 : nextrel2 M
            (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1) := by
          have np' := np
          unfold nextR at np'
          rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
            if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
          exact np'
        exact np2.2.2.2.2.1
      · rw [if_neg hi2] at hne
        exact absurd rfl hne
    -- row 1 grows to the last column whenever `i1 ≥ 1`
    have h1lt' : 0 < srow M (M.length - 1) →
        entry M 1 (parent M (srow M (M.length - 1)) (M.length - 1))
          < entry M 1 (M.length - 1) := by
      intro hi1
      by_cases hi2 : 1 < srow M (M.length - 1)
      · have np2 : nextrel2 M
            (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1) := by
          have np' := np
          unfold nextR at np'
          rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
            if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
          exact np'
        exact rtg1_entry1_lt np2.2.2.2.2.1.2.2 (by omega)
      · have i1eq : srow M (M.length - 1) = 1 := by omega
        have np1 : nextrel1 M
            (parent M (srow M (M.length - 1)) (M.length - 1)) (M.length - 1) := by
          have np' := np
          unfold nextR at np'
          rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0), if_pos i1eq] at np'
          exact np'
        exact np1.2.2.2.1
    set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
    set L := M.length - 1 - j0 with hLdef
    set d0i := (if 0 < srow M (M.length - 1)
      then entry M 0 (M.length - 1) - entry M 0 j0 else 0) with hd0i
    set d1i := (if 1 < srow M (M.length - 1)
      then entry M 1 (M.length - 1) - entry M 1 j0 else 0) with hd1i
    have hd0pos : 0 < srow M (M.length - 1) → 0 < d0i := by
      intro hi1
      rw [hd0i, if_pos hi1]
      have := iv (M.length - 1) j0lt le_rfl
      omega
    have hd1d0 : d1i ≠ 0 → 0 < d0i := by
      intro hne
      refine hd0pos ?_
      by_contra hcon
      push Not at hcon
      rw [hd1i, if_neg (by omega)] at hne
      exact hne rfl
    have hLpos : 0 < L := by omega
    have hj0b : j0 < M.length := by omega
    have htklen : (M.take j0).length = j0 := by
      rw [List.length_take]
      omega
    rw [oper_gcopies n hL hz hp, ← hj0, ← hLdef, ← hd0i, ← hd1i]
    set X := M.take j0 ++ gcopies M j0 L d0i d1i n with hX
    have egG : ∀ x, x < j0 → X.getD x (0, 0, 0) = M.getD x (0, 0, 0) := by
      intro x hx
      rw [hX, getD_append_left (by rw [htklen]; exact hx), getD_take hx]
    have egC : ∀ k' q', k' < n → q' < L →
        X.getD (j0 + (k' * L + q')) (0, 0, 0)
          = (entry M 0 (j0 + q') + k' * d0i,
             entry M 1 (j0 + q')
               + (if le1 M j0 (j0 + q') then k' * d1i else 0),
             entry M 2 (j0 + q')) := by
      intro k' q' hk' hq'
      rw [hX, getD_app_right _ _ (by rw [htklen]; omega), htklen,
        show j0 + (k' * L + q') - j0 = k' * L + q' from by omega,
        gcopies_getD hk' hq']
    intro p hplen hppos
    rw [hX, List.length_append, htklen, gcopies_length] at hplen
    by_cases hpG : p < j0
    · -- take-part positions
      rw [egG p hpG] at hppos
      obtain ⟨k, hk, hlev, hwin, hval⟩ := h p (by omega) hppos
      refine ⟨k, hk, ?_, ?_, ?_⟩
      · rw [egG k (by omega), egG p hpG]
        exact hlev
      · intro l h1 h2
        rw [egG l (by omega), egG p hpG]
        exact hwin l h1 h2
      · rw [egG k (by omega), egG p hpG]
        exact hval
    · push Not at hpG
      obtain ⟨k, q, hkn, hqL, hpe⟩ :=
        index_decomp hLpos (show p - j0 < n * L by omega)
      have hpeq : p = j0 + (k * L + q) := by omega
      rw [hpeq, egC k q hkn hqL] at hppos
      rcases Nat.eq_zero_or_pos q with rfl | hqpos
      · -- copy roots
        rw [Nat.add_zero] at hppos
        rcases Nat.eq_zero_or_pos (k * d0i) with hkd0 | hkd0
        · -- unshifted root: the host witness at `j0` transfers
          have hd1z : k * d1i = 0 := by
            rcases Nat.mul_eq_zero.1 hkd0 with rfl | hd0z
            · exact Nat.zero_mul _
            · rcases Nat.eq_zero_or_pos d1i with h0 | hpos'
              · rw [h0, Nat.mul_zero]
              · exact absurd (hd1d0 (by omega)) (by omega)
          have hj0pos : 0 < (M.getD j0 (0, 0, 0)).1 := by
            have e0 : (M.getD j0 (0, 0, 0)).1 = entry M 0 j0 := rfl
            simp only [] at hppos
            omega
          obtain ⟨w, hw, hlev, hwin, hval⟩ := h j0 hj0b hj0pos
          refine ⟨w, by omega, ?_, ?_, ?_⟩
          · rw [egG w hw, hpeq, egC k 0 hkn hqL, Nat.add_zero]
            show (M.getD w (0, 0, 0)).1 + 1 = entry M 0 j0 + k * d0i
            have e0 : (M.getD j0 (0, 0, 0)).1 = entry M 0 j0 := rfl
            omega
          · intro l h1 h2
            rw [hpeq, Nat.add_zero] at h2
            rw [hpeq, egC k 0 hkn hqL, Nat.add_zero]
            show entry M 0 j0 + k * d0i ≤ (X.getD l (0, 0, 0)).1
            by_cases hlG : l < j0
            · rw [egG l hlG]
              have := hwin l h1 hlG
              have e0 : (M.getD j0 (0, 0, 0)).1 = entry M 0 j0 := rfl
              omega
            · push Not at hlG
              obtain ⟨k', q', hk'n, hq'L, hle⟩ :=
                index_decomp hLpos (show l - j0 < n * L by omega)
              have hleq : l = j0 + (k' * L + q') := by omega
              rw [hleq, egC k' q' hk'n hq'L]
              show entry M 0 j0 + k * d0i ≤ entry M 0 (j0 + q') + k' * d0i
              have hbase : entry M 0 j0 ≤ entry M 0 (j0 + q') := by
                rcases Nat.eq_zero_or_pos q' with rfl | hq'pos
                · rw [Nat.add_zero]
                · exact (iv (j0 + q') (by omega) (by omega)).le
              rcases Nat.mul_eq_zero.1 hkd0 with rfl | hd0z
              · rw [Nat.zero_mul]
                omega
              · rw [hd0z, Nat.mul_zero, Nat.mul_zero]
                omega
          · rw [egG w hw, hpeq, egC k 0 hkn hqL, Nat.add_zero]
            show entry M 1 j0 + (if le1 M j0 j0 then k * d1i else 0)
              ≤ (M.getD w (0, 0, 0)).2.1 + 1
            have hif : (if le1 M j0 j0 then k * d1i else 0) = 0 := by
              rw [hd1z]
              exact ite_self 0
            rw [hif]
            have e1 : (M.getD j0 (0, 0, 0)).2.1 = entry M 1 j0 := rfl
            omega
        · -- the climb: witness in the previous copy at the pre-drop level
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · rw [Nat.zero_mul] at hkd0
              omega
            · exact ⟨k - 1, by omega⟩
          have hd0ipos : 0 < d0i := by
            by_contra hcon
            push Not at hcon
            have : d0i = 0 := by omega
            rw [this, Nat.mul_zero] at hkd0
            omega
          have hsrow : 0 < srow M (M.length - 1) := by
            by_contra hcon
            push Not at hcon
            rw [hd0i, if_neg (by omega)] at hd0ipos
            omega
          have hd0e : d0i = entry M 0 (M.length - 1) - entry M 0 j0 := by
            rw [hd0i, if_pos hsrow]
          have hj1e0 : entry M 0 j0 < entry M 0 (M.length - 1) :=
            iv (M.length - 1) j0lt le_rfl
          have hj1pos : 0 < (M.getD (M.length - 1) (0, 0, 0)).1 := by
            have e0 : (M.getD (M.length - 1) (0, 0, 0)).1
              = entry M 0 (M.length - 1) := rfl
            omega
          obtain ⟨w, hw, hlev, hwin, hval⟩ := h (M.length - 1) (by omega) hj1pos
          have hwj0 : j0 ≤ w := by
            by_contra hcon
            push Not at hcon
            have := hwin j0 hcon j0lt
            have e1 : (M.getD (M.length - 1) (0, 0, 0)).1
              = entry M 0 (M.length - 1) := rfl
            have e2 : (M.getD j0 (0, 0, 0)).1 = entry M 0 j0 := rfl
            omega
          have hqw : w - j0 < L := by omega
          have hweq : j0 + (w - j0) = w := by omega
          refine ⟨j0 + (k' * L + (w - j0)), by
            have hsm : (k' + 1) * L = k' * L + L := Nat.succ_mul k' L
            omega, ?_, ?_, ?_⟩
          · rw [egC k' (w - j0) (by omega) hqw, hpeq, egC (k' + 1) 0 hkn hqL,
              Nat.add_zero, hweq]
            show entry M 0 w + k' * d0i + 1 = entry M 0 j0 + (k' + 1) * d0i
            have e1 : (M.getD w (0, 0, 0)).1 = entry M 0 w := rfl
            have e2 : (M.getD (M.length - 1) (0, 0, 0)).1
              = entry M 0 (M.length - 1) := rfl
            have hsm : (k' + 1) * d0i = k' * d0i + d0i := Nat.succ_mul k' d0i
            omega
          · intro l h1 h2
            rw [hpeq] at h2
            have hlq : ∃ q'', w - j0 < q'' ∧ q'' < L ∧ l = j0 + (k' * L + q'') := by
              have hsm : (k' + 1) * L = k' * L + L := Nat.succ_mul k' L
              exact ⟨l - j0 - k' * L, by omega, by omega, by omega⟩
            obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
            rw [egC k' q'' (by omega) hq2, hpeq, egC (k' + 1) 0 hkn hqL,
              Nat.add_zero]
            show entry M 0 j0 + (k' + 1) * d0i
              ≤ entry M 0 (j0 + q'') + k' * d0i
            have := hwin (j0 + q'') (by omega) (by omega)
            have e1 : (M.getD (M.length - 1) (0, 0, 0)).1
              = entry M 0 (M.length - 1) := rfl
            have e2 : (M.getD (j0 + q'') (0, 0, 0)).1
              = entry M 0 (j0 + q'') := rfl
            have hsm : (k' + 1) * d0i = k' * d0i + d0i := Nat.succ_mul k' d0i
            omega
          · rw [egC k' (w - j0) (by omega) hqw, hpeq, egC (k' + 1) 0 hkn hqL,
              Nat.add_zero, hweq]
            show entry M 1 j0 + (if le1 M j0 j0 then (k' + 1) * d1i else 0)
              ≤ entry M 1 w + (if le1 M j0 w then k' * d1i else 0) + 1
            have e1 : (M.getD (M.length - 1) (0, 0, 0)).2.1
              = entry M 1 (M.length - 1) := rfl
            have e2 : (M.getD w (0, 0, 0)).2.1 = entry M 1 w := rfl
            rw [if_pos (le1_refl hj0b)]
            rcases Nat.eq_zero_or_pos d1i with hd1z | hd1pos
            · rw [hd1z, Nat.mul_zero, Nat.mul_zero]
              have := h1lt' hsrow
              split_ifs <;> omega
            · have hi2 : 1 < srow M (M.length - 1) := by
                by_contra hcon
                push Not at hcon
                rw [hd1i, if_neg (by omega)] at hd1pos
                omega
              have hd1e : d1i = entry M 1 (M.length - 1) - entry M 1 j0 := by
                rw [hd1i, if_pos hi2]
              have hle1j1 : le1 M j0 (M.length - 1) := hd1i1 (by omega)
              have hedge : nextrel0 M w (M.length - 1) :=
                witness_nextrel0 (by omega) hw hlev hwin
              have hRTGw : Relation.ReflTransGen (nextrel0 M) j0 w :=
                rtg0_comparable chain (Relation.ReflTransGen.single hedge) hwj0
              have hgw : le1 M j0 w :=
                le1_of_chain_le1 hle1j1 hRTGw (Relation.ReflTransGen.single hedge)
              rw [if_pos hgw]
              have hsm : (k' + 1) * d1i = k' * d1i + d1i := Nat.succ_mul k' d1i
              have h1l := h1lt' hsrow
              omega
      · -- interior copy columns: the host witness stays in the same copy
        have hj0q : j0 < j0 + q := by omega
        have hpos' : 0 < (M.getD (j0 + q) (0, 0, 0)).1 := by
          have e0 : (M.getD (j0 + q) (0, 0, 0)).1 = entry M 0 (j0 + q) := rfl
          have := iv (j0 + q) hj0q (by omega)
          omega
        obtain ⟨w, hw, hlev, hwin, hval⟩ := h (j0 + q) (by omega) hpos'
        have hwj0 : j0 ≤ w := by
          by_contra hcon
          push Not at hcon
          have := hwin j0 hcon hj0q
          have e1 : (M.getD (j0 + q) (0, 0, 0)).1 = entry M 0 (j0 + q) := rfl
          have e2 : (M.getD j0 (0, 0, 0)).1 = entry M 0 j0 := rfl
          have := iv (j0 + q) hj0q (by omega)
          omega
        have hqw : w - j0 < L := by omega
        have hweq : j0 + (w - j0) = w := by omega
        refine ⟨j0 + (k * L + (w - j0)), by omega, ?_, ?_, ?_⟩
        · rw [egC k (w - j0) hkn hqw, hpeq, egC k q hkn hqL, hweq]
          show entry M 0 w + k * d0i + 1 = entry M 0 (j0 + q) + k * d0i
          have e1 : (M.getD w (0, 0, 0)).1 = entry M 0 w := rfl
          have e2 : (M.getD (j0 + q) (0, 0, 0)).1 = entry M 0 (j0 + q) := rfl
          omega
        · intro l h1 h2
          rw [hpeq] at h2
          have hlq : ∃ q'', w - j0 < q'' ∧ q'' < q ∧ l = j0 + (k * L + q'') :=
            ⟨l - j0 - k * L, by omega, by omega, by omega⟩
          obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
          rw [egC k q'' hkn (by omega), hpeq, egC k q hkn hqL]
          show entry M 0 (j0 + q) + k * d0i ≤ entry M 0 (j0 + q'') + k * d0i
          have := hwin (j0 + q'') (by omega) (by omega)
          have e1 : (M.getD (j0 + q) (0, 0, 0)).1 = entry M 0 (j0 + q) := rfl
          have e2 : (M.getD (j0 + q'') (0, 0, 0)).1 = entry M 0 (j0 + q'') := rfl
          omega
        · rw [egC k (w - j0) hkn hqw, hpeq, egC k q hkn hqL, hweq]
          show entry M 1 (j0 + q) + (if le1 M j0 (j0 + q) then k * d1i else 0)
            ≤ entry M 1 w + (if le1 M j0 w then k * d1i else 0) + 1
          have e1 : (M.getD (j0 + q) (0, 0, 0)).2.1 = entry M 1 (j0 + q) := rfl
          have e2 : (M.getD w (0, 0, 0)).2.1 = entry M 1 w := rfl
          by_cases hg : le1 M j0 (j0 + q)
          · -- the witness inherits the guard
            have hedge : nextrel0 M w (j0 + q) :=
              witness_nextrel0 (by omega) hw hlev hwin
            have hRTGq : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
              le0_interval_desc chain (by omega) (j0 + q) (by omega) (by omega)
            have hRTGw : Relation.ReflTransGen (nextrel0 M) j0 w :=
              rtg0_comparable hRTGq (Relation.ReflTransGen.single hedge) hwj0
            have hgw : le1 M j0 w :=
              le1_of_chain_le1 hg hRTGw (Relation.ReflTransGen.single hedge)
            rw [if_pos hg, if_pos hgw]
            omega
          · rw [if_neg hg]
            split_ifs <;> omega


/-! ## 標準形の不変量 -/

theorem r1ok_ST_TS {M : TrioSeq} (h : ST_TS M) : r1ok M := by
  induction h with
  | diag v => exact r1ok_diagSeqT v
  | oper hN hn ih => exact r1ok_oper ih

theorem z0ok_ST_TS {M : TrioSeq} (h : ST_TS M) : z0ok M := by
  induction h with
  | diag v => exact z0ok_diagSeqT v
  | oper hN hn ih => exact z0ok_oper ih

theorem noninc_ST_TS {M : TrioSeq} (h : ST_TS M) : noninc M := by
  induction h with
  | diag v => exact noninc_diagSeqT v
  | oper hN hn ih => exact noninc_oper ih

/-! ## 親の存在と一意性（標準形の最終列） -/

theorem blockok_head_zero {M : TrioSeq} (hb : blockok 0 M)
    (hne : 0 < M.length) : (M.getD 0 (0, 0, 0)).1 = 0 := by
  obtain ⟨m0, M', rfl⟩ : ∃ m0 M', M = m0 :: M' := by
    cases M with
    | nil => simp at hne
    | cons m0 M' => exact ⟨m0, M', rfl⟩
  rw [List.getD_cons_zero]
  have := hb.1 (by simp)
  rw [List.headI_cons] at this
  exact this

theorem parent0_exists {M : TrioSeq} (hb : blockok 0 M) {j : ℕ}
    (hj : j < M.length) (h0 : 0 < entry M 0 j) :
    ∃ k, nextrel0 M k j := by
  have hj0 : 0 < j := by
    by_contra hc
    push Not at hc
    have : j = 0 := by omega
    subst this
    have := blockok_head_zero hb (by omega)
    have e : entry M 0 0 = (M.getD 0 (0, 0, 0)).1 := rfl
    omega
  set P : ℕ → Prop := fun k => entry M 0 k < entry M 0 j with hP
  have hP0 : P 0 := by
    show entry M 0 0 < entry M 0 j
    have e : entry M 0 0 = (M.getD 0 (0, 0, 0)).1 := rfl
    have := blockok_head_zero hb (by omega)
    omega
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, ?_, ?_, ?_⟩
  · have := Nat.findGreatest_le (P := P) (j - 1)
    omega
  · have := Nat.findGreatest_le (P := P) (j - 1)
    omega
  · exact Nat.findGreatest_spec (Nat.zero_le _) hP0
  · intro l hl
    have hnl := Nat.findGreatest_is_greatest (P := P) hl.1 (by omega)
    rw [hP] at hnl
    push Not at hnl
    exact hnl

theorem chain_to_zero {M : TrioSeq} (hb : blockok 0 M) :
    ∀ lev j, entry M 0 j = lev → j < M.length →
      ∃ r, r ≤ j ∧ entry M 0 r = 0
        ∧ Relation.ReflTransGen (nextrel0 M) r j := by
  intro lev
  induction lev using Nat.strong_induction_on with
  | _ lev IH =>
    intro j he hj
    by_cases h0 : entry M 0 j = 0
    · exact ⟨j, le_rfl, h0, Relation.ReflTransGen.refl⟩
    · obtain ⟨k, hk⟩ := parent0_exists hb hj (by omega)
      have hklt : entry M 0 k < entry M 0 j := hk.2.2.2.1
      have hkj : k < j := hk.2.2.1
      obtain ⟨r, hr1, hr2, hr3⟩ :=
        IH (entry M 0 k) (by omega) k rfl hk.1
      exact ⟨r, by omega, hr2, hr3.tail hk⟩

theorem parent1_exists {M : TrioSeq} (hb : blockok 0 M) (hz : z0ok M)
    {j : ℕ} (hj : j < M.length) (h1 : 0 < entry M 1 j) :
    ∃ k, nextrel1 M k j := by
  obtain ⟨r, hrle, hr0, hchain⟩ := chain_to_zero hb (entry M 0 j) j rfl hj
  have hre1 : entry M 1 r = 0 := by
    have hz' := hz r (by omega)
    have e0 : entry M 0 r = (M.getD r (0, 0, 0)).1 := rfl
    have e1 : entry M 1 r = (M.getD r (0, 0, 0)).2.1 := rfl
    omega
  have hrj : r < j := by
    rcases Nat.eq_or_lt_of_le hrle with rfl | h
    · omega
    · exact h
  set P : ℕ → Prop := fun k => le0 M k j ∧ entry M 1 k < entry M 1 j with hP
  have hPr : P r := by
    refine ⟨⟨by omega, hj, hchain⟩, ?_⟩
    rw [hre1]
    exact h1
  have hspec := Nat.findGreatest_spec (P := P) (show r ≤ j - 1 by omega) hPr
  have hle := Nat.findGreatest_le (P := P) (j - 1)
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, by omega, hspec.2, hspec.1, ?_⟩
  · omega
  · intro j' hj'
    rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hj'.2.2.2) with rfl | hlt
    · exact le_rfl
    · by_contra hcon
      push Not at hcon
      exact Nat.findGreatest_is_greatest (P := P) hj'.1 (by omega)
        ⟨hj'.2, hcon⟩

/-- Iterated row-1 parents reach a zero-row-1 ancestor. -/
theorem le1_to_row1_zero {M : TrioSeq} (hb : blockok 0 M) (hz : z0ok M) :
    ∀ lev j, entry M 1 j = lev → j < M.length →
      ∃ c, le1 M c j ∧ entry M 1 c = 0 := by
  intro lev
  induction lev using Nat.strong_induction_on with
  | _ lev IH =>
    intro j he hj
    by_cases h1 : entry M 1 j = 0
    · exact ⟨j, le1_refl hj, h1⟩
    · obtain ⟨k, hk⟩ := parent1_exists hb hz hj (by omega)
      have hklt : entry M 1 k < entry M 1 j := hk.2.2.2.1
      obtain ⟨c, hc1, hc2⟩ := IH (entry M 1 k) (by omega) k rfl hk.1
      exact ⟨c, ⟨hc1.1, hj, hc1.2.2.tail hk⟩, hc2⟩

theorem parent2_exists {M : TrioSeq} (hb : blockok 0 M) (hz : z0ok M)
    (hni : noninc M) {j : ℕ} (hj : j < M.length) (h2 : 0 < entry M 2 j) :
    ∃ k, nextrel2 M k j := by
  have h1 : 0 < entry M 1 j := by
    have := hni j hj
    have e1 : entry M 1 j = (M.getD j (0, 0, 0)).2.1 := rfl
    have e2 : entry M 2 j = (M.getD j (0, 0, 0)).2.2 := rfl
    omega
  obtain ⟨c, hc, hc1⟩ := le1_to_row1_zero hb hz (entry M 1 j) j rfl hj
  have hc2 : entry M 2 c = 0 := by
    have := hni c hc.1
    have e1 : entry M 1 c = (M.getD c (0, 0, 0)).2.1 := rfl
    have e2 : entry M 2 c = (M.getD c (0, 0, 0)).2.2 := rfl
    omega
  have hcj : c < j := by
    rcases Nat.eq_or_lt_of_le (rtg1_index_le hc.2.2) with rfl | h
    · omega
    · exact h
  set P : ℕ → Prop := fun k => le1 M k j ∧ entry M 2 k < entry M 2 j with hP
  have hPc : P c := ⟨hc, by omega⟩
  have hspec := Nat.findGreatest_spec (P := P) (show c ≤ j - 1 by omega) hPc
  have hle := Nat.findGreatest_le (P := P) (j - 1)
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, by omega, hspec.2, hspec.1, ?_⟩
  · omega
  · intro j' hj'
    rcases Nat.eq_or_lt_of_le (rtg1_index_le hj'.2.2.2) with rfl | hlt
    · exact le_rfl
    · by_contra hcon
      push Not at hcon
      exact Nat.findGreatest_is_greatest (P := P) hj'.1 (by omega)
        ⟨hj'.2, hcon⟩

theorem nextrel1_unique {M : TrioSeq} {k1 k2 j : ℕ}
    (h1 : nextrel1 M k1 j) (h2 : nextrel1 M k2 j) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := h1.2.2.2.2.2 k2 ⟨h, h2.2.2.2.2.1⟩
    have := h2.2.2.2.1
    omega
  · exact h
  · have := h2.2.2.2.2.2 k1 ⟨h, h1.2.2.2.2.1⟩
    have := h1.2.2.2.1
    omega

theorem nextrel2_unique {M : TrioSeq} {k1 k2 j : ℕ}
    (h1 : nextrel2 M k1 j) (h2 : nextrel2 M k2 j) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := h1.2.2.2.2.2 k2 ⟨h, h2.2.2.2.2.1⟩
    have := h2.2.2.2.1
    omega
  · exact h
  · have := h2.2.2.2.2.2 k1 ⟨h, h1.2.2.2.2.1⟩
    have := h1.2.2.2.1
    omega

/-- **The last column of a standard-shaped host has a unique parent.** -/
theorem hp_last {M : TrioSeq} (hb : blockok 0 M) (hz : z0ok M)
    (hni : noninc M) (hlen : 0 < M.length)
    (hzz : ¬ M.getD (M.length - 1) (0, 0, 0) = (0, 0, 0)) :
    hasParent M (srow M (M.length - 1)) (M.length - 1) := by
  have e0 : entry M 0 (M.length - 1) = (M.getD (M.length - 1) (0, 0, 0)).1 := rfl
  have e1 : entry M 1 (M.length - 1) = (M.getD (M.length - 1) (0, 0, 0)).2.1 := rfl
  have e2 : entry M 2 (M.length - 1) = (M.getD (M.length - 1) (0, 0, 0)).2.2 := rfl
  by_cases h2 : 0 < entry M 2 (M.length - 1)
  · have hs : srow M (M.length - 1) = 2 := by
      unfold srow
      rw [if_pos h2]
    obtain ⟨k, hk⟩ := parent2_exists hb hz hni (by omega) h2
    refine ⟨k, ?_, ?_⟩
    · show nextR M (srow M (M.length - 1)) k (M.length - 1)
      unfold nextR
      rw [hs, if_neg (show ¬(2 : ℕ) = 0 by omega),
        if_neg (show ¬(2 : ℕ) = 1 by omega)]
      exact hk
    · intro y hy
      show y = k
      have hy' : nextR M (srow M (M.length - 1)) y (M.length - 1) := hy
      unfold nextR at hy'
      rw [hs, if_neg (show ¬(2 : ℕ) = 0 by omega),
        if_neg (show ¬(2 : ℕ) = 1 by omega)] at hy'
      exact nextrel2_unique hy' hk
  · by_cases h1 : 0 < entry M 1 (M.length - 1)
    · have hs : srow M (M.length - 1) = 1 := by
        unfold srow
        rw [if_neg h2, if_pos h1]
      obtain ⟨k, hk⟩ := parent1_exists hb hz (by omega) h1
      refine ⟨k, ?_, ?_⟩
      · show nextR M (srow M (M.length - 1)) k (M.length - 1)
        unfold nextR
        rw [hs, if_neg (show ¬(1 : ℕ) = 0 by omega), if_pos rfl]
        exact hk
      · intro y hy
        have hy' : nextR M (srow M (M.length - 1)) y (M.length - 1) := hy
        unfold nextR at hy'
        rw [hs, if_neg (show ¬(1 : ℕ) = 0 by omega), if_pos rfl] at hy'
        exact nextrel1_unique hy' hk
    · have h0 : 0 < entry M 0 (M.length - 1) := by
        by_contra hc
        push Not at hc
        have hz' := hz (M.length - 1) (by omega) (by omega)
        refine hzz ?_
        refine Prod.ext (by omega) (Prod.ext ?_ ?_)
        · have := hz'.1
          omega
        · have := hz'.2
          omega
      have hs : srow M (M.length - 1) = 0 := by
        unfold srow
        rw [if_neg h2, if_neg h1]
      obtain ⟨k, hk⟩ := parent0_exists hb (by omega) h0
      refine ⟨k, ?_, ?_⟩
      · show nextR M (srow M (M.length - 1)) k (M.length - 1)
        unfold nextR
        rw [hs, if_pos rfl]
        exact hk
      · intro y hy
        have hy' : nextR M (srow M (M.length - 1)) y (M.length - 1) := hy
        unfold nextR at hy'
        rw [hs, if_pos rfl] at hy'
        exact nextrel0_src_unique hy' hk

/-- **The `noparent` branch is empty on standard forms.** -/
theorem hasParent_last_ST_TS {M : TrioSeq} (hM : ST_TS M) (hlen : 0 < M.length)
    (hzz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0)) :
    hasParent M (srow M (M.length - 1)) (M.length - 1) := by
  refine hp_last (blockok_ST_TS hM) (z0ok_ST_TS hM) (noninc_ST_TS hM) hlen ?_
  intro he
  refine hzz ⟨?_, ?_, ?_⟩
  · show (M.getD (M.length - 1) (0, 0, 0)).1 = 0
    rw [he]
  · show (M.getD (M.length - 1) (0, 0, 0)).2.1 = 0
    rw [he]
  · show (M.getD (M.length - 1) (0, 0, 0)).2.2 = 0
    rw [he]

/-! ## 最終列での行 1 の +1 規律 -/

/-- If a column has a row-1 parent, its row-1 value is exactly one above the
parent's (via `r1ok` at the first chain step out of the parent). -/
theorem nextrel1_snd_succ {M : TrioSeq} (hr : r1ok M) {j0 j1 : ℕ}
    (h : nextrel1 M j0 j1) : entry M 1 j1 = entry M 1 j0 + 1 := by
  obtain ⟨hj0, hj1, hlt, hincr, hle0, hmin⟩ := h
  obtain ⟨c, hstep, hchain⟩ :
      ∃ c, nextrel0 M j0 c ∧ Relation.ReflTransGen (nextrel0 M) c j1 := by
    rcases Relation.ReflTransGen.cases_head hle0.2.2 with he | h
    · exact absurd he (by omega)
    · exact h
  have hcj0 : j0 < c := hstep.2.2.1
  have hclen : c < M.length := hstep.2.1
  have hcj1 : le0 M c j1 := ⟨hclen, hj1, hchain⟩
  have h1 : entry M 1 j1 ≤ entry M 1 c := hmin c ⟨hcj0, hcj1⟩
  have hc0 : 0 < (M.getD c (0, 0, 0)).1 := by
    have := hstep.2.2.2.1
    have e1 : entry M 0 c = (M.getD c (0, 0, 0)).1 := rfl
    omega
  obtain ⟨k, hkc, hk1, hkmin, hk2⟩ := hr c hclen hc0
  have hnk : nextrel0 M k c := witness_nextrel0 hclen hkc hk1 hkmin
  have hkj0 : k = j0 := nextrel0_src_unique hnk hstep
  rw [hkj0] at hk2
  have h2 : entry M 1 c ≤ entry M 1 j0 + 1 := by
    have e1 : entry M 1 c = (M.getD c (0, 0, 0)).2.1 := rfl
    have e2 : entry M 1 j0 = (M.getD j0 (0, 0, 0)).2.1 := rfl
    omega
  omega

/-! ## `z < 2` 断片の不変量: 行 2 は高々 1 -/

def z2ok (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → (M.getD j (0, 0, 0)).2.2 ≤ 1

theorem z2ok_mem {M : TrioSeq} (h : z2ok M) {x : ℕ × ℕ × ℕ} (hx : x ∈ M) :
    x.2.2 ≤ 1 := by
  obtain ⟨i, hi, hxe⟩ := List.getElem_of_mem hx
  have := h i (by omega)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), hxe] at this
  exact this

theorem z2ok_of_mem {M : TrioSeq} (h : ∀ x ∈ M, x.2.2 ≤ 1) : z2ok M := by
  intro j hj
  exact h _ (getD_mem_of_lt hj)

theorem z2ok_dropLast {M : TrioSeq} (h : z2ok M) : z2ok M.dropLast :=
  z2ok_of_mem fun x hx => z2ok_mem h (List.dropLast_subset _ hx)

theorem z2ok_diagSeqT (v : ℕ) : z2ok (diagSeqT 0 v) := by
  refine z2ok_of_mem ?_
  intro x hx
  unfold diagSeqT at hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  show min j 1 ≤ 1
  omega

theorem z2ok_oper {M : TrioSeq} {n : ℕ} (h : z2ok M) : z2ok (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact h
    · exact z2ok_dropLast h
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact h
    · exact z2ok_dropLast h
  case pos =>
    rw [oper_gcopies n hL hz hp]
    refine z2ok_of_mem ?_
    intro x hx
    rcases List.mem_append.1 hx with hm | hm
    · exact z2ok_mem h (List.mem_of_mem_take hm)
    · obtain ⟨l, k, h1, h2, h3, rfl⟩ := mem_gcopies hm
      have hl : l < M.length := by omega
      have := z2ok_mem h (entry_triple_mem hl)
      simpa using this

theorem z2ok_ST_TS {M : TrioSeq} (h : ST_TS M) : z2ok M := by
  induction h with
  | diag v => exact z2ok_diagSeqT v
  | oper hN hn ih => exact z2ok_oper ih

/-! ## 同 row-1 の z-jump 禁止（スパイン付き） -/

/-- `zjump`: inside a row-0 subtree, a column with the *same* row 1 as the
subtree root and a clean spine (right-visible columns carry row 1 at least
the root's) cannot raise row 2. -/
def zjump (M : TrioSeq) : Prop :=
  ∀ i j, i < j → j < M.length →
    (∀ l, i < l → l ≤ j → entry M 0 i < entry M 0 l) →
    entry M 1 j = entry M 1 i →
    (∀ l, i < l → l < j → entry M 0 l < entry M 0 j →
      (∀ l', l < l' → l' < j → entry M 0 l < entry M 0 l') →
      entry M 1 i ≤ entry M 1 l) →
    entry M 2 j ≤ entry M 2 i

theorem zjump_take {M : TrioSeq} (h : zjump M) (m : ℕ) : zjump (M.take m) := by
  intro i j hij hj hsub heq hsp
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  have he : ∀ x, x ≤ j → ∀ r, entry (M.take m) r x = entry M r x := by
    intro x hx r
    unfold entry
    rw [getD_take (by omega)]
  rw [he j le_rfl 2, he i (by omega) 2] at *
  refine h i j hij hjM ?_ ?_ ?_
  · intro l h1 h2
    have := hsub l h1 h2
    rwa [he i (by omega) 0, he l (by omega) 0] at this
  · have := heq
    rwa [he j le_rfl 1, he i (by omega) 1] at this
  · intro l h1 h2 h3 h4
    have := hsp l h1 h2 (by rwa [he l (by omega) 0, he j le_rfl 0]) (by
      intro l' hl1 hl2
      have := h4 l' hl1 hl2
      rwa [← he l (by omega) 0, ← he l' (by omega) 0] at this)
    rwa [he i (by omega) 1, he l (by omega) 1] at this

theorem zjump_dropLast {M : TrioSeq} (h : zjump M) : zjump M.dropLast := by
  rw [List.dropLast_eq_take]
  exact zjump_take h _

theorem zjump_diagSeqT (v : ℕ) : zjump (diagSeqT 0 v) := by
  intro i j hij hj hsub heq hsp
  rw [diagSeqT_length] at hj
  have ei : entry (diagSeqT 0 v) 1 i = i := by
    show (diagSeqT 0 v).getD i (0, 0, 0) |>.2.1 = i
    rw [diagSeqT_getD (by omega)]
  have ej : entry (diagSeqT 0 v) 1 j = j := by
    show (diagSeqT 0 v).getD j (0, 0, 0) |>.2.1 = j
    rw [diagSeqT_getD (by omega)]
  rw [ei, ej] at heq
  omega

/-! ## マーク列の行 1 親の存在 -/

/-- `markP1`: every marked column has a row-0 chain ancestor with strictly
smaller row 1 (hence a row-1 parent). -/
def markP1 (M : TrioSeq) : Prop :=
  ∀ j, j < M.length → (M.getD j (0, 0, 0)).2.2 = 1 →
    ∃ c, Relation.ReflTransGen (nextrel0 M) c j ∧
      (M.getD c (0, 0, 0)).2.1 < (M.getD j (0, 0, 0)).2.1

theorem nextrel0_take {M : TrioSeq} {m a b : ℕ} (hb : b < m)
    (h : nextrel0 M a b) : nextrel0 (M.take m) a b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, h3, ?_, ?_⟩
  · rw [List.length_take]
    omega
  · rw [List.length_take]
    omega
  · show entry (M.take m) 0 a < entry (M.take m) 0 b
    unfold entry
    rw [getD_take (by omega), getD_take (by omega)]
    exact h4
  · intro l hl
    show entry (M.take m) 0 b ≤ entry (M.take m) 0 l
    unfold entry
    rw [getD_take (by omega), getD_take (by omega)]
    exact h5 l hl

theorem rtg0_take {M : TrioSeq} {m a b : ℕ} (hb : b < m)
    (h : Relation.ReflTransGen (nextrel0 M) a b) :
    Relation.ReflTransGen (nextrel0 (M.take m)) a b := by
  induction h with
  | refl => exact .refl
  | @tail y z hay hyz ih =>
    have hy : y < m := by
      have := nextrel0_index_less hyz
      omega
    exact (ih hy).tail (nextrel0_take hb hyz)
  
theorem markP1_take {M : TrioSeq} (h : markP1 M) (m : ℕ) : markP1 (M.take m) := by
  intro j hj hm
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [getD_take hjm] at hm ⊢
  obtain ⟨c, hc1, hc2⟩ := h j hjM hm
  refine ⟨c, rtg0_take hjm hc1, ?_⟩
  have hcj : c ≤ j := nextrel0_rtrancl_index_le hc1
  rw [getD_take (by omega : c < m)]
  exact hc2

theorem markP1_dropLast {M : TrioSeq} (h : markP1 M) : markP1 M.dropLast := by
  rw [List.dropLast_eq_take]
  exact markP1_take h _

theorem markP1_diagSeqT (v : ℕ) : markP1 (diagSeqT 0 v) := by
  intro j hj hm
  rw [diagSeqT_length] at hj
  rw [diagSeqT_getD hj] at hm ⊢
  have hj1 : 1 ≤ j := by
    by_contra hc
    push Not at hc
    have hj0 : j = 0 := by omega
    subst hj0
    simp at hm
  refine ⟨j - 1, ?_, ?_⟩
  · refine Relation.ReflTransGen.single ?_
    refine ⟨by rw [diagSeqT_length]; omega, by rw [diagSeqT_length]; omega,
      by omega, ?_, ?_⟩
    · show entry (diagSeqT 0 v) 0 (j - 1) < entry (diagSeqT 0 v) 0 j
      unfold entry
      rw [diagSeqT_getD (by omega), diagSeqT_getD hj]
      show j - 1 < j
      omega
    · intro l hl
      omega
  · rw [diagSeqT_getD (show j - 1 < v + 1 by omega)]
    show j - 1 < j
    omega

/-- Blocker extraction: a failed guard yields a chain node at or below the
root's row 1. -/
theorem blocker_of_not_le1 {M : TrioSeq} {r j : ℕ}
    (hch : Relation.ReflTransGen (nextrel0 M) r j) (hb : j < M.length)
    (hne : ¬ le1 M r j) :
    ∃ b, Relation.ReflTransGen (nextrel0 M) r b ∧
      Relation.ReflTransGen (nextrel0 M) b j ∧ b ≠ r ∧
      entry M 1 b ≤ entry M 1 r := by
  by_contra hcon
  push Not at hcon
  refine hne ((le1_iff_chain_window hb hch).2 ?_)
  intro x hrx hxj hxne
  by_contra hcon2
  push Not at hcon2
  exact absurd (hcon x hrx hxj hxne) (by omega)

/-- Agreement transfer: a chain step is determined by entries up to `b`. -/
theorem nextrel0_of_agree {M X : TrioSeq} {a b : ℕ} (hb : b < X.length)
    (hag : ∀ x, x ≤ b → X.getD x (0, 0, 0) = M.getD x (0, 0, 0))
    (h : nextrel0 M a b) : nextrel0 X a b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by omega, hb, h3, ?_, ?_⟩
  · show entry X 0 a < entry X 0 b
    unfold entry
    rw [hag a (by omega), hag b le_rfl]
    exact h4
  · intro l hl
    show entry X 0 b ≤ entry X 0 l
    unfold entry
    rw [hag l (by omega), hag b le_rfl]
    exact h5 l hl

theorem rtg0_of_agree {M X : TrioSeq} {b : ℕ} (hb : b < X.length)
    (hag : ∀ x, x ≤ b → X.getD x (0, 0, 0) = M.getD x (0, 0, 0)) :
    ∀ {a c : ℕ}, c ≤ b → Relation.ReflTransGen (nextrel0 M) a c →
    Relation.ReflTransGen (nextrel0 X) a c := by
  intro a c hcb h
  induction h with
  | refl => exact .refl
  | @tail y z hay hyz ih =>
    have hy : y ≤ b := by
      have := nextrel0_index_less hyz
      omega
    exact (ih hy).tail (nextrel0_of_agree (by omega) (fun x hx => hag x (by omega)) hyz)


/-- **The marked-column row-1 parent survives the expansion.** -/
theorem markP1_oper {M : TrioSeq} {n : ℕ} (hn : 1 ≤ n)
    (hmp : markP1 M) : markP1 (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact hmp
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL hz]
    unfold Pred
    split_ifs
    · exact hmp
    · exact markP1_dropLast hmp
  by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL hz hp]
    unfold Pred
    split_ifs
    · exact hmp
    · exact markP1_dropLast hmp
  case pos =>
    have np := parent_nextR hp
    have j0lt : parent M (srow M (M.length - 1)) (M.length - 1)
        < M.length - 1 := nextR_index_lt np
    have chain := nextR_chain0 np
    have iv : ∀ k, parent M (srow M (M.length - 1)) (M.length - 1) < k →
        k ≤ M.length - 1 →
        entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
          < entry M 0 k :=
      fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
    set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
    set L := M.length - 1 - j0 with hLdef
    set d0i := (if 0 < srow M (M.length - 1)
      then entry M 0 (M.length - 1) - entry M 0 j0 else 0) with hd0i
    set d1i := (if 1 < srow M (M.length - 1)
      then entry M 1 (M.length - 1) - entry M 1 j0 else 0) with hd1i
    have hLpos : 0 < L := by omega
    have hj0b : j0 < M.length := by omega
    have htklen : (M.take j0).length = j0 := by
      rw [List.length_take]
      omega
    rw [oper_gcopies n hL hz hp, ← hj0, ← hLdef, ← hd0i, ← hd1i]
    set X := M.take j0 ++ gcopies M j0 L d0i d1i n with hX
    have hXlen : X.length = j0 + n * L := by
      rw [hX, List.length_append, htklen, gcopies_length]
    have egG : ∀ x, x < j0 → X.getD x (0, 0, 0) = M.getD x (0, 0, 0) := by
      intro x hx
      rw [hX, getD_append_left (by rw [htklen]; exact hx), getD_take hx]
    have egC : ∀ k' q', k' < n → q' < L →
        X.getD (j0 + (k' * L + q')) (0, 0, 0)
          = (entry M 0 (j0 + q') + k' * d0i,
             entry M 1 (j0 + q')
               + (if le1 M j0 (j0 + q') then k' * d1i else 0),
             entry M 2 (j0 + q')) := by
      intro k' q' hk' hq'
      rw [hX, getD_app_right _ _ (by rw [htklen]; omega), htklen,
        show j0 + (k' * L + q') - j0 = k' * L + q' from by omega,
        gcopies_getD hk' hq']
    -- the zero-copy agreement extends to `j0` itself
    have egG0 : ∀ x, x ≤ j0 → X.getD x (0, 0, 0) = M.getD x (0, 0, 0) := by
      intro x hx
      rcases Nat.eq_or_lt_of_le hx with rfl | hlt
      · have h := egC 0 0 (by omega) (by omega)
        rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero] at h
        rw [h, if_pos (le1_refl hj0b), Nat.zero_mul, Nat.zero_mul,
          Nat.add_zero, Nat.add_zero, getD_eq_entries]
      · exact egG x hlt
    -- the in-copy chain transfer
    have hcopychain : ∀ k', k' < n → ∀ {a b : ℕ}, j0 ≤ a →
        Relation.ReflTransGen (nextrel0 M) a b → b < j0 + L →
        Relation.ReflTransGen (nextrel0 X)
          (j0 + (k' * L + (a - j0))) (j0 + (k' * L + (b - j0))) := by
      intro k' hk' a b ha h
      induction h with
      | refl => exact fun _ => .refl
      | @tail y z hay hyz ih =>
        intro hb
        have hyb : j0 ≤ y := by
          have h1 := nextrel0_rtrancl_index_le hay
          omega
        have hyz' : y < z := nextrel0_index_less hyz
        have hmul1 : (k' + 1) * L ≤ n * L := Nat.mul_le_mul_right L (by omega)
        have hmul2 : (k' + 1) * L = k' * L + L := Nat.succ_mul k' L
        refine (ih (by omega)).tail ?_
        obtain ⟨e1', e2', e3', e4', e5'⟩ := hyz
        refine ⟨by rw [hXlen]; omega, by rw [hXlen]; omega, by omega, ?_, ?_⟩
        · show entry X 0 (j0 + (k' * L + (y - j0)))
            < entry X 0 (j0 + (k' * L + (z - j0)))
          unfold entry
          rw [egC k' (y - j0) hk' (by omega), egC k' (z - j0) hk' (by omega)]
          show entry M 0 (j0 + (y - j0)) + k' * d0i
            < entry M 0 (j0 + (z - j0)) + k' * d0i
          rw [show j0 + (y - j0) = y from by omega,
            show j0 + (z - j0) = z from by omega]
          omega
        · intro l ⟨hl1, hl2⟩
          have hlq : ∃ q'', y - j0 < q'' ∧ q'' < z - j0
              ∧ l = j0 + (k' * L + q'') :=
            ⟨l - j0 - k' * L, by omega, by omega, by omega⟩
          obtain ⟨q'', hq1, hq2, rfl⟩ := hlq
          show entry X 0 (j0 + (k' * L + (z - j0)))
            ≤ entry X 0 (j0 + (k' * L + q''))
          unfold entry
          rw [egC k' (z - j0) hk' (by omega), egC k' q'' hk' (by omega)]
          show entry M 0 (j0 + (z - j0)) + k' * d0i
            ≤ entry M 0 (j0 + q'') + k' * d0i
          have := e5' (j0 + q'') ⟨by omega, by omega⟩
          rw [show j0 + (z - j0) = z from by omega]
          omega
    intro pj hpj hmark
    rw [hXlen] at hpj
    by_cases hG : pj < j0
    · -- take part: the host witness transfers by agreement
      rw [egG pj hG] at hmark ⊢
      obtain ⟨c, hc1, hc2⟩ := hmp pj (by omega) hmark
      have hcpj : c ≤ pj := nextrel0_rtrancl_index_le hc1
      refine ⟨c, rtg0_of_agree (b := pj) (by rw [hXlen]; omega)
        (fun x hx => egG x (by omega)) le_rfl hc1, ?_⟩
      rw [egG c (by omega)]
      exact hc2
    · push Not at hG
      obtain ⟨k, q, hkn, hqL, hpe⟩ :=
        index_decomp hLpos (show pj - j0 < n * L by omega)
      have hpeq : pj = j0 + (k * L + q) := by omega
      rw [hpeq, egC k q hkn hqL] at hmark
      simp only [] at hmark
      -- the marked base column
      have hjm : (M.getD (j0 + q) (0, 0, 0)).2.2 = 1 := by
        have e2 : entry M 2 (j0 + q) = (M.getD (j0 + q) (0, 0, 0)).2.2 := rfl
        omega
      obtain ⟨c, hc1, hc2⟩ := hmp (j0 + q) (by omega) hjm
      by_cases hcG : c < j0
      · -- crossing witness: comparability to `j0`, hop below, then the window
        have hrtgj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
          le0_interval_desc chain (by omega) (j0 + q) (by omega) (by omega)
        have hcj0 : Relation.ReflTransGen (nextrel0 M) c j0 :=
          rtg0_comparable hc1 hrtgj0q (by omega)
        obtain ⟨pp, hcpp, hppj0⟩ : ∃ pp,
            Relation.ReflTransGen (nextrel0 M) c pp ∧ nextrel0 M pp j0 := by
          rcases hcj0.cases_tail with he | h
          · exact absurd he (by omega)
          · exact h
        have hppv : entry M 0 pp < entry M 0 j0 := hppj0.2.2.2.1
        have hppG : pp < j0 := nextrel0_index_less hppj0
        have hwin : Relation.ReflTransGen (nextrel0 X) pp (j0 + (k * L + q)) := by
          refine rtg0_of_window (by rw [hXlen]; omega) (by omega) ?_
          intro l hl1 hl2
          show entry X 0 pp < entry X 0 l
          unfold entry
          rw [egG pp hppG]
          by_cases hlG : l < j0
          · rw [egG l hlG]
            show entry M 0 pp < entry M 0 l
            have := hppj0.2.2.2.2 l ⟨by omega, by omega⟩
            omega
          · push Not at hlG
            obtain ⟨k'', q'', hk''n, hq''L, hle⟩ :=
              index_decomp hLpos (show l - j0 < n * L by omega)
            have hleq : l = j0 + (k'' * L + q'') := by omega
            rw [hleq, egC k'' q'' hk''n hq''L]
            show entry M 0 pp < entry M 0 (j0 + q'') + k'' * d0i
            have hbase : entry M 0 j0 ≤ entry M 0 (j0 + q'') := by
              rcases Nat.eq_zero_or_pos q'' with rfl | hq''pos
              · rw [Nat.add_zero]
              · exact (iv (j0 + q'') (by omega) (by omega)).le
            omega
        rw [hpeq]
        refine ⟨c, ?_, ?_⟩
        · exact (rtg0_of_agree (b := pp) (by rw [hXlen]; omega)
            (fun x hx => egG x (by omega)) le_rfl hcpp).trans hwin
        · rw [egG c (by omega), egC k q hkn hqL]
          show (M.getD c (0, 0, 0)).2.1
            < entry M 1 (j0 + q) + (if le1 M j0 (j0 + q) then k * d1i else 0)
          have e1 : entry M 1 (j0 + q) = (M.getD (j0 + q) (0, 0, 0)).2.1 := rfl
          split_ifs <;> omega
      · -- in-block witness: shift both, or swap to the blocker
        push Not at hcG
        have hrtgj0q : Relation.ReflTransGen (nextrel0 M) j0 (j0 + q) :=
          le0_interval_desc chain (by omega) (j0 + q) (by omega) (by omega)
        have hrtgj0c : Relation.ReflTransGen (nextrel0 M) j0 c :=
          rtg0_comparable hrtgj0q hc1 hcG
        have hcb : c < j0 + q := by
          rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hc1) with rfl | h'
          · exfalso
            have e := hc2
            omega
          · exact h'
        rw [hpeq]
        by_cases hDj : le1 M j0 (j0 + q)
        · -- the target is lifted; so is the whole chain
          have hDc : le1 M j0 c :=
            le1_of_chain_le1 hDj hrtgj0c hc1
          refine ⟨j0 + (k * L + (c - j0)), ?_, ?_⟩
          · have := hcopychain k hkn hcG hc1 (by omega)
            rwa [show j0 + (k * L + ((j0 + q) - j0)) = j0 + (k * L + q)
              from by omega] at this
          · rw [egC k (c - j0) hkn (by omega), egC k q hkn hqL,
              show j0 + (c - j0) = c from by omega]
            show (entry M 1 c + (if le1 M j0 c then k * d1i else 0), entry M 2 c).1
              < entry M 1 (j0 + q) + (if le1 M j0 (j0 + q) then k * d1i else 0)
            rw [if_pos hDc, if_pos hDj]
            have e1 : entry M 1 c = (M.getD c (0, 0, 0)).2.1 := rfl
            have e2 : entry M 1 (j0 + q) = (M.getD (j0 + q) (0, 0, 0)).2.1 := rfl
            show entry M 1 c + k * d1i < entry M 1 (j0 + q) + k * d1i
            omega
        · -- unlifted target
          by_cases hDc : le1 M j0 c
          · -- swap to the blocker
            have hw1c : entry M 1 j0 ≤ entry M 1 c := by
              rcases Nat.eq_or_lt_of_le hcG with rfl | h'
              · exact le_rfl
              · exact (rtg1_entry1_lt hDc.2.2 (by omega)).le
            obtain ⟨b, hb1, hb2, hb3, hb4⟩ :=
              blocker_of_not_le1 hrtgj0q (by omega) hDj
            have hbq : b < j0 + q ∨ b = j0 + q := by
              rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hb2) with rfl | h'
              · exact Or.inr rfl
              · exact Or.inl h'
            rcases hbq with hbq | rfl
            · have hbj0 : j0 < b := by
                have := nextrel0_rtrancl_index_le hb1
                omega
              have hbD : ¬ le1 M j0 b := by
                intro hle
                have := rtg1_entry1_lt hle.2.2 (by omega)
                omega
              refine ⟨j0 + (k * L + (b - j0)), ?_, ?_⟩
              · have := hcopychain k hkn (by omega : j0 ≤ b) hb2 (by omega)
                rwa [show j0 + (k * L + ((j0 + q) - j0)) = j0 + (k * L + q)
                  from by omega] at this
              · rw [egC k (b - j0) hkn (by omega), egC k q hkn hqL,
                  show j0 + (b - j0) = b from by omega]
                rw [if_neg hbD, if_neg hDj]
                show entry M 1 b + 0 < entry M 1 (j0 + q) + 0
                have e1 : entry M 1 b = (M.getD b (0, 0, 0)).2.1 := rfl
                have e2 : entry M 1 (j0 + q) = (M.getD (j0 + q) (0, 0, 0)).2.1 := rfl
                have e3 : entry M 1 c = (M.getD c (0, 0, 0)).2.1 := rfl
                have e4 : entry M 1 j0 = (M.getD j0 (0, 0, 0)).2.1 := rfl
                omega
            · -- the blocker is the target itself: contradiction with the lift
              exfalso
              have e2 : entry M 1 (j0 + q) = (M.getD (j0 + q) (0, 0, 0)).2.1 := rfl
              have e3 : entry M 1 c = (M.getD c (0, 0, 0)).2.1 := rfl
              have e4 : entry M 1 j0 = (M.getD j0 (0, 0, 0)).2.1 := rfl
              omega
          · -- both unlifted
            refine ⟨j0 + (k * L + (c - j0)), ?_, ?_⟩
            · have := hcopychain k hkn hcG hc1 (by omega)
              rwa [show j0 + (k * L + ((j0 + q) - j0)) = j0 + (k * L + q)
                from by omega] at this
            · rw [egC k (c - j0) hkn (by omega), egC k q hkn hqL,
                show j0 + (c - j0) = c from by omega]
              rw [if_neg hDc, if_neg hDj]
              show entry M 1 c + 0 < entry M 1 (j0 + q) + 0
              have e1 : entry M 1 c = (M.getD c (0, 0, 0)).2.1 := rfl
              have e2 : entry M 1 (j0 + q) = (M.getD (j0 + q) (0, 0, 0)).2.1 := rfl
              omega


theorem markP1_ST_TS {M : TrioSeq} (h : ST_TS M) : markP1 M := by
  induction h with
  | diag v => exact markP1_diagSeqT v
  | oper hN hn ih => exact markP1_oper hn ih

end Googology.Trans.BMS.TrioCof
