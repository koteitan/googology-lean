/-
Ported verbatim from koteitan/trio, `lean/Gcopy.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Gcopy.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Gcopy.lean: ガード付きコピー（上昇行列つきの悪い部分のコピー）の translate 分解。

`oper` の第 k コピーは位置 `j ∈ [r, r+L)` ごとに
`(e0 j + k·d0, e1 j + [le1 M r j]·k·d1, e2 j)`。行 0 のガードは
`le0_interval_desc` により全部 1 に潰れるが、行 1 のガードは残る。
経路補題（`le1_iff_chain_window`）により、ガード集合 = 木の経路上で
行 1 が `w1 = entry M 1 r` を超え続ける「心材」であり、コピーの translate は
`lsub w1 (k·d1)` を悪い部分の translate に施したものになる。
-/
import Googology.Trans.BMS.TrioCof.Lift

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-- The plain segment `[a, a+L)` of `M`, as a column list. -/
def seg (M : TrioSeq) (a L : ℕ) : TrioSeq :=
  (List.range' a L).map fun j => (entry M 0 j, entry M 1 j, entry M 2 j)

/-- The `k`-th guarded copy of the block `[r, r+L)` (row-0 lift already
uniform). -/
noncomputable def gcopy (M : TrioSeq) (r L d0 d1 k : ℕ) : TrioSeq :=
  (List.range' r L).map fun j =>
    (entry M 0 j + k * d0,
     entry M 1 j + (if le1 M r j then k * d1 else 0),
     entry M 2 j)

/-- `n` guarded copies. -/
noncomputable def gcopies (M : TrioSeq) (r L d0 d1 n : ℕ) : TrioSeq :=
  (List.range n).flatMap fun k => gcopy M r L d0 d1 k

@[simp] theorem seg_zero (M : TrioSeq) (a : ℕ) : seg M a 0 = [] := rfl

@[simp] theorem gcopy_len (M : TrioSeq) (r L d0 d1 k : ℕ) :
    (gcopy M r L d0 d1 k).length = L := by
  unfold gcopy
  simp

theorem seg_cons (M : TrioSeq) (a L : ℕ) :
    seg M a (L + 1)
      = (entry M 0 a, entry M 1 a, entry M 2 a) :: seg M (a + 1) L := by
  unfold seg
  rw [List.range'_succ, List.map_cons]

theorem gcopy_cons (M : TrioSeq) (r L d0 d1 k a : ℕ) :
    (List.range' a (L + 1)).map (fun j =>
        ((entry M 0 j + k * d0,
          entry M 1 j + (if le1 M r j then k * d1 else 0),
          entry M 2 j) : ℕ × ℕ × ℕ))
      = (entry M 0 a + k * d0,
         entry M 1 a + (if le1 M r a then k * d1 else 0),
         entry M 2 a)
        :: (List.range' (a + 1) L).map (fun j =>
          (entry M 0 j + k * d0,
           entry M 1 j + (if le1 M r j then k * d1 else 0),
           entry M 2 j)) := by
  rw [List.range'_succ, List.map_cons]

/-! ## 窓から鎖へ（`le0_interval_desc` の窓ベース核） -/

/-- Window-based row-0 descent: if every column of `(a, j]` lies strictly
above `a` in row 0, then `j` is a row-0 descendant of `a`. -/
theorem rtg0_of_window {M : TrioSeq} {a : ℕ} :
    ∀ {j : ℕ}, j < M.length →
      a ≤ j → (∀ l, a < l → l ≤ j → entry M 0 a < entry M 0 l) →
      Relation.ReflTransGen (nextrel0 M) a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hb haj hwin
    rcases Nat.eq_or_lt_of_le haj with rfl | hlt
    · exact .refl
    · have hPa : entry M 0 a < entry M 0 j := hwin j hlt le_rfl
      set Q : ℕ → Prop := fun q => entry M 0 q < entry M 0 j with hQ
      have haj1 : a ≤ j - 1 := by omega
      set p := Nat.findGreatest Q (j - 1) with hp
      have hQp : Q p := Nat.findGreatest_spec (P := Q) haj1 hPa
      have hap : a ≤ p := Nat.le_findGreatest haj1 hPa
      have hpj : p < j := by
        have : p ≤ j - 1 := Nat.findGreatest_le _
        omega
      have hstep : nextrel0 M p j := by
        refine ⟨by omega, hb, hpj, hQp, ?_⟩
        intro l ⟨hl1, hl2⟩
        by_contra hcon
        push Not at hcon
        exact absurd (Nat.findGreatest_is_greatest (P := Q) hl1 (by omega))
          (by simp only [hQ]; omega)
      have hrec : Relation.ReflTransGen (nextrel0 M) a p := by
        refine ih p hpj (by omega) hap ?_
        intro l hl1 hl2
        exact hwin l hl1 (by omega)
      exact hrec.tail hstep

/-! ## ガードの伝播 -/

/-- The guard survives on a subtree: if `j` lies in the row-0 subtree region
of `a` (window above `a`) and is a row-1 descendant of `r`, then so is `a`. -/
theorem le1_of_le1_subtree {M : TrioSeq} {r a j : ℕ}
    (hb : j < M.length)
    (hra : Relation.ReflTransGen (nextrel0 M) r a)
    (haj : a ≤ j)
    (hwin : ∀ l, a < l → l ≤ j → entry M 0 a < entry M 0 l)
    (h : le1 M r j) : le1 M r a := by
  have haj0 : Relation.ReflTransGen (nextrel0 M) a j := rtg0_of_window hb haj hwin
  have hab : a < M.length := by omega
  refine (le1_iff_chain_window hab hra).2 ?_
  intro x hrx hxa hxne
  exact le1_chain_window h.2.2 x hrx (hxa.trans haj0) hxne

/-- The guard is decided at the head: with a guarded tree parent `pa`, the
guard of `a` is exactly the row-1 threshold test at `a`. -/
theorem le1_step {M : TrioSeq} {r pa a : ℕ}
    (hpa : le1 M r pa) (hedge : nextrel0 M pa a) :
    le1 M r a ↔ entry M 1 r < entry M 1 a := by
  have hra : Relation.ReflTransGen (nextrel0 M) r a :=
    (rtg1_to_rtg0 hpa.2.2).tail hedge
  have hab : a < M.length := hedge.2.1
  rw [le1_iff_chain_window hab hra]
  constructor
  · intro h
    refine h a (rtg1_to_rtg0 hpa.2.2 |>.tail hedge) .refl ?_
    have h1 := rtg1_index_le hpa.2.2
    have h2 := nextrel0_index_less hedge
    omega
  · intro hthr x hrx hxa hxne
    rcases Nat.eq_or_lt_of_le (nextrel0_rtrancl_index_le hxa) with rfl | hxa'
    · exact hthr
    · -- `x` is a proper chain node of `a`, hence a chain node of `pa`
      have hxpa : Relation.ReflTransGen (nextrel0 M) x pa := by
        rcases hxa.cases_tail with rfl | ⟨c, hxc, hca⟩
        · exact absurd hxa' (lt_irrefl _)
        · rw [nextrel0_src_unique hca hedge] at hxc
          exact hxc
      exact le1_chain_window hpa.2.2 x hrx hxpa hxne

/-! ## `range'` の takeWhile 分割 -/

theorem range'_split_takeWhile (q : ℕ → Bool) :
    ∀ (L a : ℕ), ∃ m, m ≤ L ∧
      (List.range' a L).takeWhile q = List.range' a m ∧
      (List.range' a L).dropWhile q = List.range' (a + m) (L - m) ∧
      (∀ j, a ≤ j → j < a + m → q j = true) ∧
      (m < L → q (a + m) = false) := by
  intro L
  induction L with
  | zero =>
    intro a
    exact ⟨0, le_rfl, rfl, rfl, fun j h1 h2 => absurd h2 (by omega),
      fun h => absurd h (by omega)⟩
  | succ L ih =>
    intro a
    rw [List.range'_succ]
    by_cases hq : q a = true
    · obtain ⟨m, hm, ht, hd, hall, hend⟩ := ih (a + 1)
      refine ⟨m + 1, by omega, ?_, ?_, ?_, ?_⟩
      · rw [List.takeWhile_cons_of_pos hq, ht, List.range'_succ]
      · rw [List.dropWhile_cons_of_pos hq, hd,
          show a + (m + 1) = a + 1 + m from by omega,
          show L + 1 - (m + 1) = L - m from by omega]
      · intro j h1 h2
        rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
        · exact hq
        · exact hall j (by omega) (by omega)
      · intro h
        have := hend (by omega)
        rw [show a + (m + 1) = a + 1 + m by omega]
        exact this
    · refine ⟨0, by omega, ?_, ?_, ?_, ?_⟩
      · rw [List.takeWhile_cons_of_neg hq]
        rfl
      · rw [List.dropWhile_cons_of_neg hq]
        show a :: List.range' (a + 1) L = List.range' a (L + 1)
        rw [List.range'_succ]
      · intro j h1 h2
        exact absurd h2 (by omega)
      · intro _
        rw [Nat.add_zero]
        exact eq_false_of_ne_true hq

theorem tshift1_zero : ∀ t : Three, tshift1 0 t = t
  | Z => rfl
  | P a1 a2 b c => by
    rw [tshift1_P, tshift1_zero b, tshift1_zero c, Nat.add_zero]

/-! ## 中核: ガード付きセグメントの translate は心材リフト

`[a, a+L)` は共通の（ガードされた）木親 `pa` を持つ兄弟森。ガード付き
写像の translate は、素のセグメントの translate に `lsub w1 (k·d1)` を
施したものに一致する。 -/

theorem translate_gseg {M : TrioSeq} {r d0 d1 k : ℕ} :
    ∀ (L : ℕ), ∀ {a pa : ℕ}, le1 M r pa → pa < a → a + L ≤ M.length →
      (∀ j, a ≤ j → j < a + L → entry M 0 pa < entry M 0 j) →
      (∀ j, pa < j → j < a → entry M 0 a ≤ entry M 0 j) →
      translate ((List.range' a L).map fun j =>
          ((entry M 0 j + k * d0,
            entry M 1 j + (if le1 M r j then k * d1 else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = lsub (entry M 1 r) (k * d1)
            (translate ((List.range' a L).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
    intro a pa hpa ha hlen hup hpre
    rcases L with - | L
    · show translate [] = lsub (entry M 1 r) (k * d1) (translate [])
      simp [translate]
    -- the tree edge to the head
    have hedge : nextrel0 M pa a := by
      refine ⟨by omega, by omega, ha, hup a le_rfl (by omega), ?_⟩
      intro l ⟨hl1, hl2⟩
      exact hpre l hl1 hl2
    have hguard : le1 M r a ↔ entry M 1 r < entry M 1 a := le1_step hpa hedge
    -- split the rest at the subtree boundary
    set q : ℕ → Bool := fun j => decide (entry M 0 a < entry M 0 j) with hqdef
    obtain ⟨m, hm, ht, hd, hall, hend⟩ := range'_split_takeWhile q L (a + 1)
    have hqg : ((fun x : ℕ × ℕ × ℕ => decide (entry M 0 a + k * d0 < x.1))
          ∘ fun j => ((entry M 0 j + k * d0,
            entry M 1 j + (if le1 M r j then k * d1 else 0),
            entry M 2 j) : ℕ × ℕ × ℕ)) = q := by
      funext j
      simp only [Function.comp_apply, hqdef]
      rw [decide_eq_decide]
      omega
    have hqs : ((fun x : ℕ × ℕ × ℕ => decide (entry M 0 a < x.1))
          ∘ fun j => ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) = q := by
      funext j
      simp only [Function.comp_apply, hqdef]
    -- unfold both translates one step
    simp only [List.range'_succ, List.map_cons]
    rw [translate, translate]
    simp only [List.takeWhile_map, List.dropWhile_map, hqg, hqs, ht, hd]
    -- the two recursive calls
    have hsub : translate ((List.range' (a + 1) m).map fun j =>
          ((entry M 0 j + k * d0,
            entry M 1 j + (if le1 M r j then k * d1 else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = if entry M 1 r < entry M 1 a then
            lsub (entry M 1 r) (k * d1) (translate ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)))
          else translate ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
      by_cases hthr : entry M 1 r < entry M 1 a
      · rw [if_pos hthr]
        refine IH m (by omega) (hguard.2 hthr) (by omega) (by omega) ?_ ?_
        · intro j h1 h2
          have := hall j h1 (by omega)
          simp only [hqdef, decide_eq_true_eq] at this
          exact this
        · intro j h1 h2
          omega
      · rw [if_neg hthr]
        have hnog : ∀ j, a + 1 ≤ j → j < a + 1 + m → ¬ le1 M r j := by
          intro j h1 h2 hle1
          refine hthr (hguard.1 ?_)
          refine le1_of_le1_subtree (by omega)
            ((rtg1_to_rtg0 hpa.2.2).tail hedge) (by omega) ?_ hle1
          intro l hl1 hl2
          have := hall l (by omega) (by omega)
          simp only [hqdef, decide_eq_true_eq] at this
          exact this
        have hmap : ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j + k * d0,
                entry M 1 j + (if le1 M r j then k * d1 else 0),
                entry M 2 j) : ℕ × ℕ × ℕ))
            = shiftr01 (k * d0) 0 ((List.range' (a + 1) m).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ)) := by
          unfold shiftr01
          rw [List.map_map]
          refine List.map_congr_left ?_
          intro j hj
          have hjb := List.mem_range'_1.1 hj
          simp only [Function.comp_apply]
          rw [if_neg (hnog j hjb.1 (by omega))]
        rw [hmap, translate_shiftr01, tshift1_zero]
    have htail : translate ((List.range' (a + 1 + m) (L - m)).map fun j =>
          ((entry M 0 j + k * d0,
            entry M 1 j + (if le1 M r j then k * d1 else 0),
            entry M 2 j) : ℕ × ℕ × ℕ))
        = lsub (entry M 1 r) (k * d1)
            (translate ((List.range' (a + 1 + m) (L - m)).map fun j =>
              ((entry M 0 j, entry M 1 j, entry M 2 j) : ℕ × ℕ × ℕ))) := by
      rcases Nat.eq_or_lt_of_le hm with rfl | hmL
      · rw [Nat.sub_self]
        show translate [] = lsub (entry M 1 r) (k * d1) (translate [])
        simp [translate]
      · have hqe := hend hmL
        have he0 : entry M 0 (a + 1 + m) ≤ entry M 0 a := by
          have : q (a + 1 + m) = false := hqe
          simp only [hqdef, decide_eq_false_iff_not, Nat.not_lt] at this
          exact this
        refine IH (L - m) (by omega) hpa (by omega) (by omega) ?_ ?_
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
    rw [hsub, htail]
    -- assemble against the lifted right-hand side
    by_cases hthr : entry M 1 r < entry M 1 a
    · rw [if_pos hthr, if_pos (hguard.2 hthr), lsub_P_pos hthr]
    · rw [if_neg hthr, if_neg (fun h => hthr (hguard.1 h)), Nat.add_zero,
        lsub_P_neg hthr]

/-! ## コピー 1 個の translate -/

theorem le1_refl {M : TrioSeq} {r : ℕ} (h : r < M.length) : le1 M r r :=
  ⟨h, h, .refl⟩

/-- The `k`-th guarded copy of a block (root at `r`, interior strictly above
it in row 0) translates to the heartwood-lifted block term: the root is lifted
unconditionally, the interior through `lsub`. -/
theorem translate_gcopy {M : TrioSeq} {r L d0 d1 k : ℕ}
    (hL : 1 ≤ L) (hlen : r + L ≤ M.length)
    (hup : ∀ j, r < j → j < r + L → entry M 0 r < entry M 0 j) :
    translate (gcopy M r L d0 d1 k)
      = P (entry M 1 r + k * d1) (entry M 2 r)
          (lsub (entry M 1 r) (k * d1) (translate (seg M (r + 1) (L - 1)))) Z := by
  have hrb : r < M.length := by omega
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  unfold gcopy
  simp only [List.range'_succ, List.map_cons]
  rw [if_pos (le1_refl hrb)]
  rw [translate_single_tree (by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hjb := List.mem_range'_1.1 hj
    show entry M 0 r + k * d0 < entry M 0 j + k * d0
    have := hup j (by omega) (by omega)
    omega)]
  rw [translate_gseg L' (le1_refl hrb) (Nat.lt_succ_self r) (by omega)
    (fun j h1 h2 => hup j (by omega) (by omega)) (fun j h1 h2 => by omega)]
  rfl

/-! ## タワー: ガード付きコピー列 -/

noncomputable def gcopiesFrom (M : TrioSeq) (r L d0 d1 k0 m : ℕ) : TrioSeq :=
  (List.range' k0 m).flatMap fun k => gcopy M r L d0 d1 k

theorem gcopiesFrom_zero (M : TrioSeq) (r L d0 d1 k0 : ℕ) :
    gcopiesFrom M r L d0 d1 k0 0 = [] := rfl

theorem gcopiesFrom_succ (M : TrioSeq) (r L d0 d1 k0 m : ℕ) :
    gcopiesFrom M r L d0 d1 k0 (m + 1)
      = gcopy M r L d0 d1 k0 ++ gcopiesFrom M r L d0 d1 (k0 + 1) m := by
  unfold gcopiesFrom
  rw [List.range'_succ, List.flatMap_cons]

theorem gcopies_eq_from (M : TrioSeq) (r L d0 d1 n : ℕ) :
    gcopies M r L d0 d1 n = gcopiesFrom M r L d0 d1 0 n := by
  unfold gcopies gcopiesFrom
  rw [List.range_eq_range']

/-- Head/interior split of one guarded copy. -/
theorem gcopy_head (M : TrioSeq) {r L : ℕ} (hL : 1 ≤ L) (hrb : r < M.length)
    (d0 d1 k : ℕ) :
    gcopy M r L d0 d1 k
      = (entry M 0 r + k * d0, entry M 1 r + k * d1, entry M 2 r)
        :: (List.range' (r + 1) (L - 1)).map (fun j =>
          ((entry M 0 j + k * d0,
            entry M 1 j + (if le1 M r j then k * d1 else 0),
            entry M 2 j) : ℕ × ℕ × ℕ)) := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  unfold gcopy
  rw [List.range'_succ, List.map_cons, if_pos (le1_refl hrb), Nat.add_sub_cancel]

/-- Snoc split of the extended copy (block plus its last column). -/
theorem gcopy_snoc (M : TrioSeq) (r L d0 d1 k : ℕ) :
    gcopy M r (L + 1) d0 d1 k
      = gcopy M r L d0 d1 k ++
        [(entry M 0 (r + L) + k * d0,
          entry M 1 (r + L) + (if le1 M r (r + L) then k * d1 else 0),
          entry M 2 (r + L))] := by
  unfold gcopy
  have h := List.range'_append (s := r) (m := L) (n := 1) (step := 1)
  rw [Nat.one_mul] at h
  rw [← h, List.map_append]
  rfl

theorem seg_snoc (M : TrioSeq) (a L : ℕ) :
    seg M a (L + 1)
      = seg M a L ++ [(entry M 0 (a + L), entry M 1 (a + L), entry M 2 (a + L))] := by
  unfold seg
  have h := List.range'_append (s := a) (m := L) (n := 1) (step := 1)
  rw [Nat.one_mul] at h
  rw [← h, List.map_append]
  rfl

/-- Shape of a nonempty tower: a single tree headed by the first copy root. -/
theorem translate_gcopiesFrom {M : TrioSeq} {r L d0 d1 : ℕ}
    (hL : 1 ≤ L) (hlen : r + L ≤ M.length)
    (hup : ∀ j, r < j → j < r + L → entry M 0 r < entry M 0 j)
    (d0pos : 0 < d0) (k0 m : ℕ) :
    translate (gcopiesFrom M r L d0 d1 k0 (m + 1))
      = P (entry M 1 r + k0 * d1) (entry M 2 r)
          (translate (((List.range' (r + 1) (L - 1)).map fun j =>
              ((entry M 0 j + k0 * d0,
                entry M 1 j + (if le1 M r j then k0 * d1 else 0),
                entry M 2 j) : ℕ × ℕ × ℕ))
            ++ gcopiesFrom M r L d0 d1 (k0 + 1) m)) Z := by
  have hrb : r < M.length := by omega
  rw [gcopiesFrom_succ, gcopy_head M hL hrb, List.cons_append]
  exact translate_single_tree (by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hjb := List.mem_range'_1.1 hj
      show entry M 0 r + k0 * d0 < entry M 0 j + k0 * d0
      have := hup j (by omega) (by omega)
      omega
    · unfold gcopiesFrom at hx
      obtain ⟨k', hk', hxk⟩ := List.mem_flatMap.1 hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hxk
      have hjb := List.mem_range'_1.1 hj
      have hk'b := List.mem_range'_1.1 hk'
      show entry M 0 r + k0 * d0 < entry M 0 j + k' * d0
      have he0 : entry M 0 r ≤ entry M 0 j := by
        rcases Nat.eq_or_lt_of_le hjb.1 with rfl | h
        · exact le_rfl
        · exact (hup j h (by omega)).le
      have hmul : (k0 + 1) * d0 ≤ k' * d0 :=
        Nat.mul_le_mul_right d0 hk'b.1
      rw [Nat.succ_mul] at hmul
      omega)

/-- **タワーの cnf**: ガード付きコピー列は CNF を保つ。`lead_lt` は
最後の列（位置 `r+L`）との先頭対比較、`hglp` はその列のガード（`i1 = 2`
では `le1`、`i1 = 1` では `d1 = 0`）。 -/
theorem cnf_gcopiesFrom {M : TrioSeq} {r L d0 d1 : ℕ}
    (hL : 1 ≤ L) (hlen : r + L < M.length)
    (hup1 : ∀ j, r < j → j ≤ r + L → entry M 0 r < entry M 0 j)
    (d0pos : 0 < d0)
    (hd0 : entry M 0 (r + L) = entry M 0 r + d0)
    (hglp : le1 M r (r + L) ∨ d1 = 0)
    (lead_lt : entry M 1 r + d1 < entry M 1 (r + L)
      ∨ (entry M 1 r + d1 = entry M 1 (r + L) ∧ entry M 2 r < entry M 2 (r + L)))
    (cBlp : cnf (translate (seg M r (L + 1)))) :
    ∀ m k0, cnf (translate (gcopiesFrom M r L d0 d1 k0 m)) := by
  have hrb : r < M.length := by omega
  have hupI : ∀ j, r < j → j < r + L → entry M 0 r < entry M 0 j :=
    fun j h1 h2 => hup1 j h1 (by omega)
  have hsegtree : translate (seg M r (L + 1))
      = P (entry M 1 r) (entry M 2 r) (translate (seg M (r + 1) L)) Z := by
    rw [seg_cons]
    exact translate_single_tree (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hjb := List.mem_range'_1.1 hj
      exact hup1 j (by omega) (by omega))
  have cInt : cnf (translate (seg M (r + 1) L)) := by
    have h := cBlp
    rw [hsegtree] at h
    exact cnf_P_Z.1 h
  have cIntNoLp : cnf (translate (seg M (r + 1) (L - 1))) := by
    obtain ⟨L', hLe⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hne : seg M (r + 1) L ≠ [] := by
      unfold seg
      subst hLe
      rw [List.range'_succ, List.map_cons]
      exact List.cons_ne_nil _ _
    have h := cnf_dropLast hne cInt
    have hd : (seg M (r + 1) L).dropLast = seg M (r + 1) (L - 1) := by
      subst hLe
      rw [seg_snoc, List.dropLast_concat, Nat.add_sub_cancel]
    rwa [hd] at h
  have cg : ∀ k, cnf (translate (gcopy M r L d0 d1 k)) := by
    intro k
    rw [translate_gcopy hL (by omega) hupI, cnf_P_Z]
    exact cnf_lsub _ _ _ cIntNoLp
  have cgExt : ∀ k, cnf (translate (gcopy M r (L + 1) d0 d1 k)) := by
    intro k
    rw [translate_gcopy (by omega) (by omega)
      (fun j h1 h2 => hup1 j h1 (by omega)), cnf_P_Z]
    exact cnf_lsub _ _ _ cInt
  have lpcol : ∀ k : ℕ, (if le1 M r (r + L) then k * d1 else 0) = k * d1 := by
    intro k
    rcases hglp with h | h
    · rw [if_pos h]
    · subst h
      rw [Nat.mul_zero]
      split_ifs <;> rfl
  intro m
  induction m with
  | zero =>
    intro k0
    rw [gcopiesFrom_zero]
    show cnf (translate [])
    simp [translate]
  | succ m ih =>
    intro k0
    rcases m with - | m'
    · rw [show gcopiesFrom M r L d0 d1 k0 1 = gcopy M r L d0 d1 k0 from by
        rw [gcopiesFrom_succ, gcopiesFrom_zero, List.append_nil]]
      exact cg k0
    · rw [gcopiesFrom_succ]
      have restEq : gcopiesFrom M r L d0 d1 (k0 + 1) (m' + 1)
          = (entry M 0 r + (k0 + 1) * d0,
             entry M 1 r + (k0 + 1) * d1, entry M 2 r)
            :: (((List.range' (r + 1) (L - 1)).map fun j =>
                ((entry M 0 j + (k0 + 1) * d0,
                  entry M 1 j + (if le1 M r j then (k0 + 1) * d1 else 0),
                  entry M 2 j) : ℕ × ℕ × ℕ))
              ++ gcopiesFrom M r L d0 d1 (k0 + 2) m') := by
        rw [gcopiesFrom_succ, gcopy_head M hL hrb, List.cons_append]
      have tREST := translate_gcopiesFrom (d1 := d1) hL (by omega) hupI d0pos (k0 + 1) m'
      have tlp : translate ([((entry M 0 (r + L) + k0 * d0,
            entry M 1 (r + L) + k0 * d1, entry M 2 (r + L)))] : TrioSeq)
          = P (entry M 1 (r + L) + k0 * d1) (entry M 2 (r + L)) Z Z := by
        rw [translate]
        simp [translate]
      have hlead' : entry M 1 r + (k0 + 1) * d1 < entry M 1 (r + L) + k0 * d1
          ∨ (entry M 1 r + (k0 + 1) * d1 = entry M 1 (r + L) + k0 * d1
             ∧ entry M 2 r < entry M 2 (r + L)) := by
        rcases lead_lt with h | ⟨h1, h2⟩
        · left
          rw [Nat.succ_mul]
          omega
        · right
          constructor
          · rw [Nat.succ_mul]
            omega
          · exact h2
      rw [restEq]
      refine cnf_ctx_cong (z2 := (entry M 0 (r + L) + k0 * d0,
          entry M 1 (r + L) + k0 * d1, entry M 2 (r + L))) (T2 := [])
        ?_ ?_ ?_ ?_ ?_ ?_ (gcopy M r L d0 d1 k0) ?_
      · rw [← restEq]
        exact ih (k0 + 1)
      · rw [← restEq, tREST, tlp, olt_P_P]
        rcases hlead' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · show entry M 0 r + (k0 + 1) * d0 = entry M 0 (r + L) + k0 * d0
        rw [Nat.succ_mul]
        omega
      · refine ⟨entry M 1 r + (k0 + 1) * d1, entry M 2 r, _, Z,
          entry M 1 (r + L) + k0 * d1, entry M 2 (r + L), Z, Z,
          by rw [← restEq, tREST], tlp, Or.inl (olt_P_P.2 ?_)⟩
        rcases hlead' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
          have hjb := List.mem_range'_1.1 hj
          show entry M 0 r + (k0 + 1) * d0 ≤ entry M 0 j + (k0 + 1) * d0
          have := hupI j (by omega) (by omega)
          omega
        · unfold gcopiesFrom at hx
          obtain ⟨k', hk', hxk⟩ := List.mem_flatMap.1 hx
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hxk
          have hjb := List.mem_range'_1.1 hj
          have hk'b := List.mem_range'_1.1 hk'
          show entry M 0 r + (k0 + 1) * d0 ≤ entry M 0 j + k' * d0
          rw [Nat.succ_mul]
          have he0 : entry M 0 r ≤ entry M 0 j := by
            rcases Nat.eq_or_lt_of_le hjb.1 with rfl | h
            · exact le_rfl
            · exact (hupI j h (by omega)).le
          have hmul : (k0 + 2) * d0 ≤ k' * d0 :=
            Nat.mul_le_mul_right d0 hk'b.1
          rw [Nat.succ_mul, Nat.succ_mul] at hmul
          omega
      · intro x hx
        exact absurd hx (List.not_mem_nil)
      · have h := cgExt k0
        rw [gcopy_snoc, lpcol k0] at h
        exact h

end Googology.Trans.BMS.TrioCof
