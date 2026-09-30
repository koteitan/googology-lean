import Googology.Trans.BMS.PoR.PSS.SC.Step
import Googology.Trans.BMS.ExBuchholz.PSS.Rank

/-!
# Theorem SC, Part 2: a sequence satisfying SC is standard

`proof/COMB.md` §8b, Part 2.  Suppose `M` satisfies SC.  By induction on the
length, its prefix `Q = M.dropLast` is standard (SC is prefix-closed:
`sc_dropLast`).  Write `M = Q ++ [c]` and suppose `M` is not standard.

* `M` is below a diagonal sequence (`exists_ctps_gt_of_sc`), so there is a
  least standard `X` above `M` (`isWellOrder_ctpsLt`).  Every `X[n]` is
  standard and below `X`, hence below `M`.
* `X` does not end with `(0,0)` (`not_between_zero`), so it is in the copying
  case `ExpCase X j₀ d₀` (`ctps_expCase`).
* `exists_le_oper` gives `Q ≤ X[n]` for all large `n`, and `X[n] < Q ++ [c]`.
  So `X[n] = Q ++ w :: _` with `w < c` (`eq_append_of_between`); `|Q| ≥ j₁`,
  and `c < X_{j₁}` if `|Q| = j₁`.
* `ExpCase.config_false`: this configuration violates Sib or G\* of
  `M = X[n]↾|Q| ++ [c]`, or (when `|Q| = j₁`) contradicts (A) or (I0) of `X`.
  The comparison is between two consecutive copies `a < b = a + L` of the
  column `j₀` (or `b` and the last column): the term of `b` agrees with the
  term of `a` up to the position of `c`, and there `c` is above the column of
  `a`'s term.  When `i₁ = 0` the copies are siblings (Sib fails); when
  `i₁ = 1`, `b` is descending with `v(b) = a` (G\* fails).  This replaces
  the paper's appeal to Lemma 9: when `i₁ = 1` and `|Q| = j₁`, (A) gives
  `y_{j₀} = y_{j₁} - 1`, so no `c` fits between the two.

The main result is `ctps_of_SC`.
-/

namespace Googology.Trans.PSS.Forest

open _root_.PSS (oper entry Lng idx1 hasParent parent parents nextR Pred diagSeq)
open Googology.Trans.BMS (parAt parAux ParL)
open Bijectivity (ltPS lePS CTPS)

/-! ## SC is prefix-closed -/

theorem yAt_of_ge {M : PS} {j : ℕ} (h : M.length ≤ j) : yAt M j = 0 := by
  simp [yAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem r0_dropLast {M : PS} (h : R0 M) (hl : 2 ≤ M.length) : R0 M.dropLast := by
  obtain ⟨hhd, hroot⟩ := h
  have hne : M ≠ [] := by rintro rfl; simp at hl
  have hP := pert_dropLast hne
  refine ⟨?_, fun i hi hpar => ?_⟩
  · cases M with
    | nil => simp at hl
    | cons q M' =>
      cases M' with
      | nil => simp at hl
      | cons q' M'' => simpa [List.dropLast_cons_cons] using hhd
  · have hi' : i < M.length - 1 := by simpa using hi
    rw [hP.par_eq hi'] at hpar
    rw [hP.yAt_eq hi']
    exact hroot i (by omega) hpar

/-- **SC is prefix-closed.** -/
theorem sc_dropLast {M : PS} (h : SC M) (hl : 2 ≤ M.length) : SC M.dropLast :=
  ⟨r0_dropLast h.1 hl, I0_dropLast h.2.1, condA_dropLast h.2.2.1, sib_dropLast h.2.2.2.1,
    gstar_dropLast h.2.2.2.2⟩

/-! ## A sequence satisfying SC is below a diagonal sequence -/

theorem xAt_zero_of_r0 {M : PS} (hR : R0 M) : xAt M 0 = 0 ∧ yAt M 0 = 0 := by
  cases M with
  | nil => exact absurd hR.1 (by simp)
  | cons q M' =>
    have hq : q = (0, 0) := by simpa using hR.1
    subst hq
    simp [xAt, yAt]

theorem xAt_le_of_sc {M : PS} (hR : R0 M) (hI : I0 M) (j : ℕ) : xAt M j ≤ j := by
  induction j with
  | zero => rw [(xAt_zero_of_r0 hR).1]
  | succ j ih =>
    by_cases hj : j + 1 < M.length
    · have := hI j hj
      omega
    · rw [xAt_of_ge (by omega)]
      omega

theorem yAt_le_xAt_of_sc {M : PS} (hR : R0 M) (hA : CondA M) (j : ℕ) : yAt M j ≤ xAt M j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < M.length
    · cases hp : par M j with
      | none => rw [hR.2 j hj hp]; omega
      | some p =>
        have hpj := par_spec hp
        have h1 := hA j hj p (by omega) hp
        have h2 := ih p hpj.1
        omega
    · rw [yAt_of_ge (by omega)]
      omega

theorem PLt.irrefl (p : ℕ × ℕ) : ¬ PLt p p := by
  unfold PLt
  omega

theorem PLt.asymm {p q : ℕ × ℕ} (h : PLt p q) : ¬ PLt q p := by
  unfold PLt at *
  omega

/-- Columnwise `≤` with equal lengths gives `≤ₚ`. -/
theorem lePS_of_pointwise : ∀ {A B : PS}, A.length = B.length →
    (∀ j (h1 : j < A.length) (h2 : j < B.length), A[j] = B[j] ∨ PLt A[j] B[j]) → lePS A B
  | [], [], _, _ => Or.inl rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | a :: A, b :: B, hl, h => by
    have ih := lePS_of_pointwise (A := A) (B := B) (by simpa using hl)
      (fun j h1 h2 => by simpa using h (j + 1) (by simp; omega) (by simp; omega))
    rcases h 0 (by simp) (by simp) with he | hlt
    · simp only [List.getElem_cons_zero] at he
      subst he
      rcases ih with rfl | ih
      · exact Or.inl rfl
      · exact Or.inr ((ltPS_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl, ih⟩))
    · exact Or.inr ((ltPS_cons_iff _ _ _ _).mpr (Or.inl (by simpa using hlt)))

theorem ne_nil_of_r0 {M : PS} (h : R0 M) : M ≠ [] := by
  rintro rfl
  exact absurd h.1 (by simp)

theorem lePS_diagSeq_of_sc {M : PS} (h : SC M) : lePS M (diagSeq 0 (M.length - 1)) := by
  have hne := ne_nil_of_r0 h.1
  have hpos := List.length_pos_iff.mpr hne
  have hlen : (diagSeq 0 (M.length - 1)).length = M.length := by
    simp [diagSeq]
    omega
  apply lePS_of_pointwise hlen.symm
  intro j h1 h2
  have hd : (diagSeq 0 (M.length - 1))[j] = (j, j) := by simp [diagSeq]
  rw [hd]
  have hx := xAt_le_of_sc h.1 h.2.1 j
  have hy := yAt_le_xAt_of_sc h.1 h.2.2.1 j
  rw [xAt_of_lt h1] at hx
  rw [yAt_of_lt h1, xAt_of_lt h1] at hy
  unfold PLt
  by_cases hxj : M[j].1 = j
  · by_cases hyj : M[j].2 = j
    · left
      exact Prod.ext hxj hyj
    · right; right
      exact ⟨hxj, by omega⟩
  · right; left
    omega

/-- **A sequence satisfying SC that is not standard is below a standard one.** -/
theorem exists_ctps_gt_of_sc {M : PS} (h : SC M) (hM : ¬ CTPS M) : ∃ X, CTPS X ∧ ltPS M X := by
  rcases lePS_diagSeq_of_sc h with he | hlt
  · exact absurd (he ▸ Bijectivity.ctps_diagSeq _) hM
  · exact ⟨_, Bijectivity.ctps_diagSeq _, hlt⟩

/-! ## Lists between `Q` and `Q ++ [c]` -/

/-- **A list between `Q` and `Q ++ [c]` that is longer than `Q`** is
`Q ++ w :: _` with `w < c`. -/
theorem eq_append_of_between {c : ℕ × ℕ} :
    ∀ {Q Y : PS}, lePS Q Y → ltPS Y (Q ++ [c]) → Q.length < Y.length →
      ∃ w r, Y = Q ++ w :: r ∧ PLt w c
  | [], [], _, _, hl => by simp at hl
  | [], w :: r, _, hlt, _ => by
    refine ⟨w, r, rfl, ?_⟩
    rw [List.nil_append, ltPS_cons_iff] at hlt
    rcases hlt with hlt | ⟨_, hlt⟩
    · exact hlt
    · exact absurd hlt (not_ltPS_nil _)
  | _ :: _, [], _, _, hl => by simp at hl
  | q :: Q, y :: Y, hle, hlt, hl => by
    rw [List.cons_append, ltPS_cons_iff] at hlt
    have hle' : (q = y ∧ Q = Y) ∨ PLt q y ∨ (q = y ∧ ltPS Q Y) := by
      rcases hle with he | hlt'
      · simp only [List.cons.injEq] at he
        exact Or.inl he
      · rw [ltPS_cons_iff] at hlt'
        tauto
    rcases hlt with hyq | ⟨rfl, hlt⟩
    · exfalso
      rcases hle' with ⟨rfl, _⟩ | hqy | ⟨rfl, _⟩
      · exact PLt.irrefl _ hyq
      · exact PLt.asymm hyq hqy
      · exact PLt.irrefl _ hyq
    · have hQY : lePS Q Y := by
        rcases hle' with ⟨_, rfl⟩ | hqy | ⟨_, hQY⟩
        · exact Or.inl rfl
        · exact absurd hqy (PLt.irrefl _)
        · exact Or.inr hQY
      obtain ⟨w, r, rfl, hw⟩ := eq_append_of_between hQY hlt (by simpa using hl)
      exact ⟨w, r, rfl, hw⟩

/-- Nothing lies strictly between `D` and `D ++ [(0,0)]`. -/
theorem not_between_zero : ∀ {D M : PS}, ltPS D M → ltPS M (D ++ [(0, 0)]) → False
  | [], [], h, _ => not_ltPS_nil _ h
  | [], m :: M, _, h => by
    rw [List.nil_append, ltPS_cons_iff] at h
    rcases h with h | ⟨_, h⟩
    · unfold PLt at h
      omega
    · exact not_ltPS_nil _ h
  | _ :: _, [], h, _ => not_ltPS_nil _ h
  | d :: D, m :: M, h1, h2 => by
    rw [ltPS_cons_iff] at h1
    rw [List.cons_append, ltPS_cons_iff] at h2
    rcases h2 with h2 | ⟨rfl, h2⟩
    · rcases h1 with h1 | ⟨rfl, _⟩
      · exact PLt.asymm h1 h2
      · exact PLt.irrefl _ h2
    · rcases h1 with h1 | ⟨_, h1⟩
      · exact PLt.irrefl _ h1
      · exact not_between_zero h1 h2

theorem ltPS_asymm {A B : PS} (h1 : ltPS A B) (h2 : ltPS B A) : False :=
  Bijectivity.ltPS_irrefl A (Bijectivity.ltPS_trans h1 h2)

/-! ## A standard sequence that does not end with `(0,0)` copies -/

theorem ctps_expCase {X : PS} (hX : CTPS X) (hl : 1 < Lng X)
    (hz : ¬ (entry X 0 (Lng X - 1) = 0 ∧ entry X 1 (Lng X - 1) = 0)) :
    ∃ j0 d0, ExpCase X j0 d0 := by
  have hG := good_of_ctps hX
  have hi : Lng X - 1 < X.length := by simp only [Lng] at hl ⊢; omega
  have hhas : hasParent X (idx1 X (Lng X - 1)) (Lng X - 1) = true := by
    by_cases hy : 0 < entry X 1 (Lng X - 1)
    · have hidx : idx1 X (Lng X - 1) = 1 := by unfold idx1; rw [if_pos hy]
      rw [entry_one] at hy
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp (parAt1_ne_none hG _ hy)
      rw [hidx]
      unfold hasParent
      rw [parents_one_some hi hp]
      rfl
    · have hidx : idx1 X (Lng X - 1) = 0 := by unfold idx1; rw [if_neg hy]
      have hx : 0 < entry X 0 (Lng X - 1) := by omega
      rw [entry_zero, ← map_fst_getElem!] at hx
      cases hp : parAt (X.map Prod.fst) (Lng X - 1) with
      | none =>
        exfalso
        unfold parAt at hp
        have h0 := parAux_none _ _ _ hp 0 (by omega)
        simp only [map_fst_getElem!] at h0 hx
        have := hG.1
        omega
      | some p =>
        rw [hidx]
        unfold hasParent
        rw [parents_zero_some hi hp]
        rfl
  exact ⟨_, _, ⟨hl, hz, hhas, rfl, rfl⟩⟩

/-! ## The columns of `X[n]` -/

variable {X : PS} {j0 d0 : ℕ}

theorem yAt_oper_copy (h : ExpCase X j0 d0) {k n : ℕ} (hk : k < n)
    {r : ℕ} (hr : r < Lng X - 1 - j0) :
    yAt (oper X n) (j0 + k * (Lng X - 1 - j0) + r) = yAt X (j0 + r) := by
  have hg := getElem?_oper_copy h hk hr
  rw [yAt_eq_entry X]
  unfold yAt
  rw [List.getD_eq_getElem?_getD, hg]
  rfl

/-- The column `j₀ + m·L + r` of `X[n]` is the column `j₀ + r` of `X`, raised by `m·d₀`. -/
theorem ExpCase.col (h : ExpCase X j0 d0) {L : ℕ} (hL : Lng X - 1 - j0 = L) {m n r : ℕ}
    (hm : m < n) (hr : r < L) :
    xAt (oper X n) (j0 + m * L + r) = xAt X (j0 + r) + m * d0 ∧
      yAt (oper X n) (j0 + m * L + r) = yAt X (j0 + r) := by
  subst hL
  exact ⟨xAt_oper_copy h hm hr, yAt_oper_copy h hm hr⟩

/-- **`X[n]` is periodic from `j₀` on**, with period `L` and raise `d₀`. -/
theorem ExpCase.period (h : ExpCase X j0 d0) {L : ℕ} (hL : Lng X - 1 - j0 = L) {n j : ℕ}
    (hj0 : j0 ≤ j) (hj : j + L < (oper X n).length) :
    xAt (oper X n) (j + L) = xAt (oper X n) j + d0 ∧
      yAt (oper X n) (j + L) = yAt (oper X n) j := by
  subst hL
  have hlen := length_oper_copies h n
  obtain ⟨k, r, hk, hr, rfl⟩ := h.decomp (m := n) hj0 (by omega)
  obtain ⟨L, hL⟩ : ∃ L, Lng X - 1 - j0 = L := ⟨_, rfl⟩
  rw [hL] at hr hlen hj ⊢
  have hk1 : k + 1 < n := by
    by_contra hc
    push Not at hc
    have : n * L ≤ (k + 1) * L := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, one_mul] at this
    omega
  have e : j0 + k * L + r + L = j0 + (k + 1) * L + r := by rw [Nat.add_mul, one_mul]; omega
  rw [e, (h.col hL hk1 hr).1, (h.col hL hk hr).1, (h.col hL hk1 hr).2, (h.col hL hk hr).2]
  refine ⟨?_, rfl⟩
  rw [Nat.add_mul, one_mul]
  omega

/-! ## Two facts about `X` -/

/-- When `i₁ = 0`, `x_{j₁} ≤ x_{j₀} + 1` (by (I0), since `j₀` is the row-0 parent of `j₁`). -/
theorem ExpCase.x_last_le (h : ExpCase X j0 d0) (hI : I0 X) (hi : idx1 X (Lng X - 1) = 0) :
    xAt X (Lng X - 1) ≤ xAt X j0 + 1 := by
  have hn := h.nextR_true
  rw [hi] at hn
  simp only [nextR, ↓reduceIte] at hn
  obtain ⟨_, _, _, hmin⟩ := (nextrel0_iff X j0 (Lng X - 1)).mp hn
  have hj := h.j0_lt
  have hstep := hI j0 (by simp only [Lng] at hj ⊢; omega)
  rcases Nat.lt_or_ge (j0 + 1) (Lng X - 1) with h1 | h1
  · have := hmin (j0 + 1) (by omega) h1
    rw [← xAt_eq_map, ← xAt_eq_map] at this
    omega
  · rw [show Lng X - 1 = j0 + 1 by omega]
    exact hstep

/-- When `i₁ = 1`, `y_{j₁} ≤ y_{j₀} + 1` (by (A) at the child of `j₀` on the path to `j₁`). -/
theorem ExpCase.y_last_le (h : ExpCase X j0 d0) (hA : CondA X) (hi : idx1 X (Lng X - 1) = 1) :
    yAt X (Lng X - 1) ≤ yAt X j0 + 1 := by
  classical
  have hanc := h.anc
  have hlen := hanc.lt_length
  have hone := h.one hi
  have hex : ∃ a, j0 < a ∧ a ≤ Lng X - 1 ∧ (a = Lng X - 1 ∨ Anc X a (Lng X - 1)) :=
    ⟨_, hanc.1, le_rfl, Or.inl rfl⟩
  obtain ⟨ha1, ha2, ha3⟩ := Nat.find_spec hex
  have hpar : par X (Nat.find hex) = some j0 := by
    rw [par_eq_some_iff]
    refine ⟨hanc.of_le ha1 ha2, fun e he => ?_⟩
    by_contra hej
    push Not at hej
    have hea := he.1
    apply Nat.find_min hex hea
    refine ⟨hej, by omega, Or.inr ?_⟩
    rcases ha3 with heq | hA'
    · rw [heq] at he
      exact he
    · exact he.trans hA'
  have hc := hA _ (by omega) j0 (by omega) hpar
  rcases ha3 with heq | hA'
  · rw [heq] at hc
    exact hc
  · have := hone.2.2 _ ha1 hA'
    omega

/-! ## Tools for the comparison -/

/-- Two columns at the same height with only higher columns between them have
the same parent. -/
theorem par_eq_of_level {M : PS} {a b : ℕ} (hab : a < b) (hx : xAt M a = xAt M b)
    (hmid : ∀ j, a < j → j < b → xAt M a < xAt M j) : par M a = par M b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  unfold par
  rw [List.range_add, List.filter_append]
  have h2 : ((List.range d).map (a + ·)).filter (fun j => decide (xAt M j < xAt M (a + d))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro j hj
    simp only [List.mem_map, List.mem_range] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simp only [decide_eq_true_eq, not_lt]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [Nat.add_zero]
      omega
    · have := hmid (a + i) (by omega) (by omega)
      omega
  rw [h2, List.append_nil, ← hx]

theorem length_sh_take_drop (M : PS) (x e a : ℕ) :
    (sh x ((M.take e).drop a)).length = min e M.length - a := by
  simp [length_sh]

theorem getElem?_sh_take_drop (M : PS) (x : ℕ) {e a r : ℕ} (he : a + r < e)
    (hM : a + r < M.length) :
    (sh x ((M.take e).drop a))[r]? = some (xAt M (a + r) - x, yAt M (a + r)) := by
  rw [sh, List.getElem?_map, List.getElem?_drop, List.getElem?_take_of_lt he,
    List.getElem?_eq_getElem hM, xAt_of_lt hM, yAt_of_lt hM]
  rfl

/-- **Comparison by positions**: `A <ₚ B` if they agree before `k`, and at `k`
`A` ends or has a lower column. -/
theorem ltPS_of_getElem? {A B : PS} {k : ℕ} (hk : k < B.length) (hkA : k ≤ A.length)
    (hagree : ∀ r < k, A[r]? = B[r]?)
    (hlast : ∀ v w, A[k]? = some v → B[k]? = some w → PLt v w) : ltPS A B := by
  have htake : A.take k = B.take k := by
    apply List.ext_getElem?
    intro r
    by_cases hr : r < k
    · rw [List.getElem?_take_of_lt hr, List.getElem?_take_of_lt hr]
      exact hagree r hr
    · rw [List.getElem?_eq_none (by simp only [List.length_take]; omega),
        List.getElem?_eq_none (by simp only [List.length_take]; omega)]
  rcases Nat.lt_or_ge k A.length with hkA' | hkA'
  · refine Bijectivity.ltPS_of_agree hkA' hk htake ?_
    rw [Bijectivity.pairAt_eq_getElem A hkA', Bijectivity.pairAt_eq_getElem B hk]
    exact hlast _ _ (List.getElem?_eq_getElem hkA') (List.getElem?_eq_getElem hk)
  · have hA : A = B.take k := by rw [← htake, List.take_of_length_le hkA']
    rw [hA]
    exact Bijectivity.ltPS_take B hk

theorem not_ltPS_single_zero {M : PS} (h : R0 M) : ¬ ltPS M [(0, 0)] := by
  intro hlt
  cases M with
  | nil => exact absurd h.1 (by simp)
  | cons m M' =>
    have hm : m = (0, 0) := by simpa using h.1
    subst hm
    rw [ltPS_cons_iff] at hlt
    rcases hlt with h' | ⟨_, h'⟩
    · exact PLt.irrefl _ h'
    · exact not_ltPS_nil _ h'

/-! ## The configuration is impossible -/

/-- **The core of Part 2.**  Let `X` be in the copying case, `p ≥ j₁` a
position of `X[n]`, and `c` a column above the column `p` of `X[n]` (and below
the last column of `X` if `p = j₁`).  Then `M = X[n]↾p ++ [c]` violates Sib or
G\*. -/
theorem ExpCase.config_false (h : ExpCase X j0 d0) (hA : CondA X) (hI : I0 X)
    {n p : ℕ} (hp1 : Lng X - 1 ≤ p) (hpn : p < (oper X n).length) {c : ℕ × ℕ}
    (hw : PLt (xAt (oper X n) p, yAt (oper X n) p) c)
    (hc : p = Lng X - 1 → PLt c (xAt X (Lng X - 1), yAt X (Lng X - 1)))
    (hS : Sib ((oper X n).take p ++ [c])) (hG : Gstar ((oper X n).take p ++ [c])) : False := by
  have hj := h.j0_lt
  have hanc0 := h.anc
  obtain ⟨L, hL⟩ : ∃ L, Lng X - 1 - j0 = L := ⟨_, rfl⟩
  obtain ⟨j1, hj1⟩ : ∃ j1, Lng X - 1 = j1 := ⟨_, rfl⟩
  have hLj : j1 = j0 + L := by omega
  have hLpos : 0 < L := by omega
  have hNlen : (oper X n).length = j0 + n * L := by rw [length_oper_copies h, hL]
  have hcol : ∀ {m r : ℕ}, m < n → r < L →
      xAt (oper X n) (j0 + m * L + r) = xAt X (j0 + r) + m * d0 ∧
        yAt (oper X n) (j0 + m * L + r) = yAt X (j0 + r) := fun hm hr => h.col hL hm hr
  have hper : ∀ {j : ℕ}, j0 ≤ j → j + L < (oper X n).length →
      xAt (oper X n) (j + L) = xAt (oper X n) j + d0 ∧
        yAt (oper X n) (j + L) = yAt (oper X n) j := fun hj0 hjL => h.period hL hj0 hjL
  have hanc : ∀ r, 0 < r → r < L → xAt X j0 < xAt X (j0 + r) :=
    fun r h1 h2 => hanc0.2 _ (by omega) (by omega)
  rw [hj1] at hanc0 hp1 hc
  set N := oper X n with hN
  set M := N.take p ++ [c] with hM
  have hMlen : M.length = p + 1 := by
    simp only [hM, List.length_append, List.length_take, List.length_singleton]
    omega
  have hMne : M ≠ [] := by
    rw [← List.length_pos_iff]
    omega
  have hxM : ∀ j < p, xAt M j = xAt N j := fun j hj => by
    rw [hM, xAt_append_left (by simp only [List.length_take]; omega), xAt_take hj]
  have hyM : ∀ j < p, yAt M j = yAt N j := fun j hj => by
    rw [hM, yAt_append_left (by simp only [List.length_take]; omega), yAt_take hj]
  have hMp : M[p]? = some c := by
    rw [hM, List.getElem?_append_right (by simp only [List.length_take]; omega)]
    simp [Nat.min_eq_left hpn.le]
  have hxMp : xAt M p = c.1 := by
    unfold xAt
    rw [List.getD_eq_getElem?_getD, hMp]
    rfl
  have hyMp : yAt M p = c.2 := by
    unfold yAt
    rw [List.getD_eq_getElem?_getD, hMp]
    rfl
  have hw' := hw
  simp only [PLt] at hw'
  -- `p = j₀ + q·L + t` with `1 ≤ t ≤ L`
  obtain ⟨q, s, hs, hpq⟩ : ∃ q s, s < L ∧ p = j0 + q * L + (s + 1) :=
    ⟨(p - j0 - 1) / L, (p - j0 - 1) % L, Nat.mod_lt _ hLpos, by
      have := Nat.div_add_mod (p - j0 - 1) L
      rw [Nat.mul_comm] at this
      omega⟩
  obtain ⟨t, ht⟩ : ∃ t, s + 1 = t := ⟨_, rfl⟩
  rw [ht] at hpq
  have ht1 : 1 ≤ t := by omega
  have htL : t ≤ L := by omega
  have hqn : q < n := by
    by_contra hc'
    push Not at hc'
    have : n * L ≤ q * L := Nat.mul_le_mul_right _ hc'
    omega
  by_cases hαc : idx1 X (Lng X - 1) = 0 ∧ t = L ∧ c.1 = xAt N p
  · -- **Case α** (`i₁ = 0`, `c` at the height of the copy of `j₀`): Sib fails
    -- between the last copy `b` of `j₀` and the last column.
    obtain ⟨hi, htL', hcx⟩ := hαc
    have hd0 := h.d0_zero hi
    obtain ⟨b, hb⟩ : ∃ b, j0 + q * L = b := ⟨_, rfl⟩
    have hpb : p = b + L := by omega
    have hb0 := hcol (m := q) (r := 0) hqn hLpos
    rw [hb] at hb0
    simp only [Nat.add_zero] at hb0
    have hpx := hper (j := b) (by omega) (by omega)
    rw [← hpb] at hpx
    have hmid : ∀ j, b < j → j < p → xAt M b < xAt M j := by
      intro j h1 h2
      obtain ⟨r, rfl⟩ : ∃ r, j = b + r := ⟨j - b, by omega⟩
      have e1 := hxM b (by omega)
      have e2 := hxM (b + r) h2
      have e3 := hcol (m := q) (r := r) hqn (by omega)
      rw [hb] at e3
      have e4 := hanc r (by omega) (by omega)
      omega
    have hxbp : xAt M b = xAt M p := by
      have e1 := hxM b (by omega)
      omega
    have hpar : par M b = par M p := par_eq_of_level (by omega) hxbp hmid
    have hsib := hS b (by omega) p (by omega) (by omega) hpar
    have hlast : term M p = [(0, yAt M p)] := by
      have := term_last hMne
      rwa [show M.length - 1 = p by omega] at this
    obtain ⟨r, hr⟩ := term_head (M := M) (u := b) (by omega)
    have hy : yAt M b < yAt M p := by
      have e1 := hyM b (by omega)
      omega
    have hlt : ltPS (term M b) (term M p) := by
      rw [hr, hlast]
      exact ltPS_head _ _ hy
    exact Bijectivity.ltPS_irrefl _ (ltPS_of_ltPS_of_lePS hlt hsib)
  by_cases hq0 : q = 0
  · -- **Case `p = j₁`**: contradicts (I0) or (A) of `X`.
    subst hq0
    simp only [zero_mul, Nat.add_zero] at hpq
    have htL' : t = L := by omega
    have hpj1 : p = j1 := by omega
    have hcc := hc hpj1
    simp only [PLt] at hcc
    have hw0 := hcol (m := 0) (r := 0) (by omega) hLpos
    simp only [zero_mul, Nat.add_zero] at hw0
    have hpx := hper (j := j0) le_rfl (by omega)
    rw [show j0 + L = p by omega] at hpx
    rcases idx1_cases X with hi | hi
    · have hd0 := h.d0_zero hi
      have hx1 := h.x_last_le hI hi
      have hy1 : yAt X (Lng X - 1) = 0 := by
        rw [yAt_eq_entry]
        unfold idx1 at hi
        split at hi
        · omega
        · omega
      rw [hj1] at hx1 hy1
      have hne : c.1 ≠ xAt N p := fun he => hαc ⟨hi, htL', he⟩
      omega
    · obtain ⟨hx1, hy1, _⟩ := h.one hi
      have hy2 := h.y_last_le hA hi
      rw [hj1] at hx1 hy1 hy2
      omega
  -- **Main case**: two consecutive copies `a < a + L` of `j₀`, both before `p`.
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, j0 + q' * L = a := ⟨_, rfl⟩
  have hpa : p = a + L + t := by
    rw [Nat.add_mul, one_mul] at hpq
    omega
  have hq'n : q' < n := by omega
  have hbp : a + L < p := by omega
  have hca : ∀ r, r < L →
      xAt N (a + r) = xAt X (j0 + r) + q' * d0 ∧ yAt N (a + r) = yAt X (j0 + r) := by
    intro r hr
    have := hcol (m := q') hq'n hr
    rw [ha] at this
    exact this
  have hcb : ∀ r, r ≤ t →
      xAt N (a + L + r) = xAt N (a + r) + d0 ∧ yAt N (a + L + r) = yAt N (a + r) := by
    intro r hr
    have := hper (j := a + r) (by omega) (by omega)
    rw [show a + r + L = a + L + r by omega] at this
    exact this
  have ha0 := hca 0 hLpos
  simp only [Nat.add_zero] at ha0
  have hb0 := hcb 0 (by omega)
  simp only [Nat.add_zero] at hb0
  have hwp := hcb t le_rfl
  rw [← hpa] at hwp
  have hat : xAt N a ≤ xAt N (a + t) ∧ (t < L → xAt N a < xAt N (a + t)) := by
    rcases Nat.lt_or_ge t L with htl | htl
    · have e1 := hca t htl
      have e2 := hanc t (by omega) htl
      exact ⟨by omega, fun _ => by omega⟩
    · have htL' : t = L := by omega
      rw [htL']
      exact ⟨by omega, fun h' => absurd h' (by omega)⟩
  -- `c` is above the copy `a + L`
  have hxcb : xAt N (a + L) < c.1 := by
    rcases Nat.lt_or_ge t L with htl | htl
    · have := hat.2 htl
      omega
    · have htL' : t = L := by omega
      rcases idx1_cases X with hi | hi
      · have hd0 := h.d0_zero hi
        have hne : c.1 ≠ xAt N p := fun he => hαc ⟨hi, htL', he⟩
        rw [htL'] at hwp
        omega
      · have hd := (h.one hi).1
        rw [hj1] at hd
        have hx := hanc0.2 j1 (by omega) le_rfl
        rw [htL'] at hwp
        omega
  -- the term of `b = a + L` runs to the end
  have hTB : term M (a + L) = sh (xAt M (a + L)) ((M.take (p + 1)).drop (a + L)) := by
    apply term_eq_of_end (by omega) (by omega)
    · intro j h1 h2
      have e1 := hxM _ hbp
      rcases Nat.lt_or_ge j p with hjp | hjp
      · obtain ⟨r, rfl⟩ : ∃ r, j = a + L + r := ⟨j - (a + L), by omega⟩
        have e2 := hxM _ hjp
        have e3 := hcb r (by omega)
        have e4 := hca r (by omega)
        have e5 := hanc r (by omega) (by omega)
        omega
      · rw [show j = p by omega, hxMp]
        omega
    · intro h'
      omega
  -- the term of `a`: it ends at `a + L` (`i₁ = 0`) or runs to the end (`i₁ = 1`)
  have hTA : ∃ e, a + L ≤ e ∧ e ≤ p + 1 ∧ term M a = sh (xAt M a) ((M.take e).drop a) := by
    rcases idx1_cases X with hi | hi
    · refine ⟨a + L, le_rfl, by omega, term_eq_of_end (by omega) (by omega) ?_ ?_⟩
      · intro j h1 h2
        obtain ⟨r, rfl⟩ : ∃ r, j = a + r := ⟨j - a, by omega⟩
        have e1 := hxM a (by omega)
        have e2 := hxM (a + r) (by omega)
        have e3 := hca r (by omega)
        have e4 := hanc r (by omega) (by omega)
        omega
      · intro _
        have hd0 := h.d0_zero hi
        have e1 := hxM a (by omega)
        have e2 := hxM (a + L) hbp
        omega
    · refine ⟨p + 1, by omega, le_rfl, term_eq_of_end (by omega) (by omega) ?_ (fun h' => by omega)⟩
      have hd := (h.one hi).1
      rw [hj1] at hd
      have hx := hanc0.2 j1 (by omega) le_rfl
      intro j h1 h2
      have e1 := hxM a (by omega)
      rcases Nat.lt_or_ge j (a + L) with hj' | hj'
      · obtain ⟨r, rfl⟩ : ∃ r, j = a + r := ⟨j - a, by omega⟩
        have e2 := hxM (a + r) (by omega)
        have e3 := hca r (by omega)
        have e4 := hanc r (by omega) (by omega)
        omega
      · rcases Nat.lt_or_ge j p with hjp | hjp
        · obtain ⟨r, rfl⟩ : ∃ r, j = a + L + r := ⟨j - (a + L), by omega⟩
          have e2 := hxM (a + L + r) hjp
          have e3 := hcb r (by omega)
          rcases Nat.eq_zero_or_pos r with hr0 | hr0
          · subst hr0
            simp only [Nat.add_zero] at e2 e3 ⊢
            omega
          · have e4 := hca r (by omega)
            have e5 := hanc r hr0 (by omega)
            omega
        · rw [show j = p by omega, hxMp]
          omega
  obtain ⟨e, he1, he2, hTAe⟩ := hTA
  -- **the term of `a` is below the term of `a + L`**
  have hABlt : ltPS (term M a) (term M (a + L)) := by
    rw [hTAe, hTB]
    apply ltPS_of_getElem? (k := t)
    · rw [length_sh_take_drop]
      omega
    · rw [length_sh_take_drop]
      omega
    · intro r hr
      rw [getElem?_sh_take_drop _ _ (by omega) (by omega),
        getElem?_sh_take_drop _ _ (by omega) (by omega)]
      have e1 := hxM a (by omega)
      have e2 := hxM (a + L) hbp
      have e3 := hxM (a + r) (by omega)
      have e4 := hxM (a + L + r) (by omega)
      have e5 := hyM (a + r) (by omega)
      have e6 := hyM (a + L + r) (by omega)
      have e7 := hcb r (by omega)
      have e8 := hca r (by omega)
      have e9 : xAt X j0 ≤ xAt X (j0 + r) := by
        rcases Nat.eq_zero_or_pos r with hr0 | hr0
        · subst hr0
          simp
        · exact (hanc r hr0 (by omega)).le
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor <;> omega
    · intro v w hv hw2
      obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp hv
      rw [length_sh_take_drop] at hlen
      rw [getElem?_sh_take_drop _ _ (by omega) (by omega)] at hv
      rw [getElem?_sh_take_drop _ _ (by omega) (by omega)] at hw2
      obtain rfl := Option.some.inj hv
      obtain rfl := Option.some.inj hw2
      rw [show a + L + t = p by omega, hxMp, hyMp]
      have e1 := hxM a (by omega)
      have e2 := hxM (a + L) hbp
      have e3 := hxM (a + t) (by omega)
      have e5 := hyM (a + t) (by omega)
      have e6 := hat.1
      simp only [PLt]
      omega
  rcases idx1_cases X with hi | hi
  · -- `i₁ = 0`: the copies are siblings, and Sib fails.
    have hd0 := h.d0_zero hi
    have hpar : par M a = par M (a + L) := by
      apply par_eq_of_level (by omega)
      · have e1 := hxM a (by omega)
        have e2 := hxM (a + L) hbp
        omega
      · intro j h1 h2
        obtain ⟨r, rfl⟩ : ∃ r, j = a + r := ⟨j - a, by omega⟩
        have e1 := hxM a (by omega)
        have e2 := hxM (a + r) (by omega)
        have e3 := hca r (by omega)
        have e4 := hanc r (by omega) (by omega)
        omega
    have hsib := hS a (by omega) (a + L) (by omega) (by omega) hpar
    exact Bijectivity.ltPS_irrefl _ (ltPS_of_ltPS_of_lePS hABlt hsib)
  · -- `i₁ = 1`: the copies are nested, `a + L` is descending with `v = a`, and G* fails.
    obtain ⟨hd, hy01, hyanc⟩ := h.one hi
    rw [hj1] at hd hy01 hyanc
    have hx := hanc0.2 j1 (by omega) le_rfl
    have hAnc : Anc M a (a + L) := ⟨by omega, fun j h1 h2 => by
      have e1 := hxM a (by omega)
      rcases Nat.lt_or_ge j (a + L) with hj' | hj'
      · obtain ⟨r, rfl⟩ : ∃ r, j = a + r := ⟨j - a, by omega⟩
        have e2 := hxM (a + r) (by omega)
        have e3 := hca r (by omega)
        have e4 := hanc r (by omega) (by omega)
        omega
      · have e2 := hxM (a + L) hbp
        rw [show j = a + L by omega]
        omega⟩
    have hyab : yAt M a = yAt M (a + L) := by
      rw [hyM a (by omega), hyM (a + L) hbp, hb0.2]
    have hmid : ∀ e', Anc M e' (a + L) → a < e' → yAt M (a + L) < yAt M e' := by
      intro e' he' hae'
      have he'b := he'.1
      obtain ⟨r, rfl⟩ : ∃ r, e' = a + r := ⟨e' - a, by omega⟩
      have hr : r < L := by omega
      have hAX : Anc X (j0 + r) j1 := ⟨by omega, fun j h1 h2 => by
        rcases Nat.lt_or_ge j j1 with hjj | hjj
        · obtain ⟨r', rfl⟩ : ∃ r', j = j0 + r' := ⟨j - j0, by omega⟩
          have e1 := he'.2 (a + r') (by omega) (by omega)
          have e2 := hxM (a + r) (by omega)
          have e3 := hxM (a + r') (by omega)
          have e4 := hca r hr
          have e5 := hca r' (by omega)
          omega
        · rw [show j = j1 by omega]
          have e1 := he'.2 (a + L) (by omega) le_rfl
          have e2 := hxM (a + r) (by omega)
          have e3 := hxM (a + L) hbp
          have e4 := hca r hr
          omega⟩
      have hy := hyanc (j0 + r) (by omega) hAX
      have e1 := hyM (a + r) (by omega)
      have e2 := hyM (a + L) hbp
      have e3 := (hca r hr).2
      omega
    have hvOf : vOf M (a + L) = some a := vOf_eq_some_iff.mpr ⟨hAnc, hyab.le, hmid⟩
    have hdesc : Descending M (a + L) := by
      rw [descending_iff]
      obtain ⟨pb, hpb⟩ := par_isSome_of_anc hAnc
      refine ⟨pb, hpb, ?_⟩
      have hle := le_par_of_anc hpb hAnc
      rcases Nat.eq_or_lt_of_le hle with heq | hlt'
      · rw [← heq]
        omega
      · exact (hmid pb (anc_of_par hpb) hlt').le
    have hgs := hG (a + L) (by omega) hdesc a (by omega) hvOf
    exact ltPS_asymm hABlt hgs

/-! ## Theorem SC, Part 2 -/

theorem ctps_of_SC_len : ∀ (k : ℕ) (M : PS), M.length = k → SC M → CTPS M := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M hk h
  have hne := ne_nil_of_r0 h.1
  have hpos := List.length_pos_iff.mpr hne
  rcases Nat.lt_or_ge M.length 2 with hl | hl
  · obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp (by omega : M.length = 1)
    have hq : q = (0, 0) := by simpa using h.1.1
    subst hq
    exact Bijectivity.ctps_zero_singleton
  have hQ : CTPS M.dropLast := ih _ (by rw [← hk, List.length_dropLast]; omega) _ rfl
    (sc_dropLast h hl)
  have hMX : ¬ ltPS M [(0, 0)] := not_ltPS_single_zero h.1
  obtain ⟨Q, c, hMQ⟩ : ∃ Q c, M = Q ++ [c] :=
    ⟨M.dropLast, M.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  have hQe : M.dropLast = Q := by rw [hMQ]; simp
  rw [hQe] at hQ
  subst hMQ
  by_contra hM
  -- the least standard sequence above `M`
  obtain ⟨X0, hX0, hMX0⟩ := exists_ctps_gt_of_sc h hM
  obtain ⟨⟨X, hX⟩, hXS, hXmin⟩ := (IsWellFounded.wf : WellFounded CtpsLt).has_min
    {Y : {Y : PS // CTPS Y} | ltPS (Q ++ [c]) Y.1} ⟨⟨X0, hX0⟩, hMX0⟩
  simp only [Set.mem_setOf_eq] at hXS
  have hmin : ∀ Y, CTPS Y → ltPS (Q ++ [c]) Y → ¬ ltPS Y X :=
    fun Y hY hMY => hXmin ⟨Y, hY⟩ hMY
  have hXne := ctps_ne_nil hX
  have hXl : 1 < Lng X := by
    by_contra hc
    have hX1 : X.length = 1 := by
      have := List.length_pos_iff.mpr hXne
      simp only [Lng] at hc
      omega
    rw [ctps_single hX hX1] at hXS
    exact hMX hXS
  -- every `X[n]` is below `M`
  have hbelow : ∀ n, 1 ≤ n → ltPS (oper X n) (Q ++ [c]) := by
    intro n hn
    have hXn := Bijectivity.ctps_oper hX hn
    have hlt := Bijectivity.oper_ltPS hXl n hn
    rcases ltPS_trichotomy (oper X n) (Q ++ [c]) with h1 | h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hXn) hM
    · exact absurd hlt (hmin _ hXn h1)
  -- `X` does not end with `(0,0)`
  by_cases hz : entry X 0 (Lng X - 1) = 0 ∧ entry X 1 (Lng X - 1) = 0
  · have h1 := hbelow 1 le_rfl
    rw [Bijectivity.oper_of_last_zero hXl hz.1 hz.2 1] at h1
    have hPred : Pred X = X.dropLast := by
      simp only [Pred, show ¬ Lng X ≤ 1 by omega, ↓reduceIte]
    rw [hPred] at h1
    have hi : X.length - 1 < X.length := by simp only [Lng] at hXl; omega
    have hlast : X.getLast hXne = (0, 0) := by
      rw [List.getLast_eq_getElem]
      refine Prod.ext ?_ ?_
      · rw [← xAt_of_lt hi, xAt_eq_entry]
        exact hz.1
      · rw [← yAt_of_lt hi, yAt_eq_entry]
        exact hz.2
    have hXe : X = X.dropLast ++ [(0, 0)] := by
      conv_lhs => rw [← List.dropLast_append_getLast hXne]
      rw [hlast]
    rw [hXe] at hXS
    exact not_between_zero h1 hXS
  obtain ⟨j0, d0, hE⟩ := ctps_expCase hX hXl hz
  -- `Q ≤ X[n]` for all large `n`
  have hQM : ltPS Q (Q ++ [c]) := ltPS_append_right Q (by simp)
  obtain ⟨n0, hn0, hQn0⟩ := exists_le_oper hQ hX (Bijectivity.ltPS_trans hQM hXS)
  obtain ⟨n, hn⟩ : ∃ n, n0 + Q.length + 2 = n := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ := Bijectivity.oper_prefix X hn0 (by omega : n0 ≤ n)
  have hQn : lePS Q (oper X n) :=
    Bijectivity.lePS_trans hQn0 (by rw [hR]; exact lePS_of_prefix (List.prefix_append _ _))
  have hlenN : Q.length < (oper X n).length := by
    rw [length_oper_copies hE]
    have hL := hE.L_pos
    have : n ≤ n * (Lng X - 1 - j0) := Nat.le_mul_of_pos_right _ hL
    omega
  obtain ⟨w, r, hNQ, hwc⟩ := eq_append_of_between hQn (hbelow n (by omega)) hlenN
  have hNp : (oper X n)[Q.length]? = some w := by rw [hNQ]; simp
  have hxw : xAt (oper X n) Q.length = w.1 := by
    unfold xAt
    rw [List.getD_eq_getElem?_getD, hNp]
    rfl
  have hyw : yAt (oper X n) Q.length = w.2 := by
    unfold yAt
    rw [List.getD_eq_getElem?_getD, hNp]
    rfl
  have hNtake : (oper X n).take Q.length = Q := by rw [hNQ]; simp
  have htake1 : (oper X n).take (Lng X - 1) = X.take (Lng X - 1) := hE.take_oper (by omega)
  -- `|Q| ≥ j₁`
  have hp1 : Lng X - 1 ≤ Q.length := by
    by_contra hc
    push Not at hc
    have e1 : X.take (Q.length + 1) = Q ++ [w] := by
      have e2 : ((oper X n).take (Lng X - 1)).take (Q.length + 1) =
          (oper X n).take (Q.length + 1) := by
        rw [List.take_take]
        congr 1
        omega
      have e3 : (X.take (Lng X - 1)).take (Q.length + 1) = X.take (Q.length + 1) := by
        rw [List.take_take]
        congr 1
        omega
      rw [← e3, ← htake1, e2, hNQ, List.take_length_add_append]
      rfl
    have hXlt : ltPS X (Q ++ [c]) := by
      rw [← List.take_append_drop (Q.length + 1) X, e1, List.append_assoc, List.singleton_append]
      exact (Bijectivity.ltPS_append_cancel _ _ _).mpr ((ltPS_cons_iff _ _ _ _).mpr (Or.inl hwc))
    exact ltPS_asymm hXlt hXS
  -- `c` is below the last column of `X` when `|Q| = j₁`
  have hcl : Q.length = Lng X - 1 → PLt c (xAt X (Lng X - 1), yAt X (Lng X - 1)) := by
    intro hpe
    have hQe' : Q = X.take (Lng X - 1) := by rw [← hNtake, hpe, htake1]
    have hi : Lng X - 1 < X.length := by simp only [Lng] at hXl ⊢; omega
    have hXe : X = X.take (Lng X - 1) ++ [(xAt X (Lng X - 1), yAt X (Lng X - 1))] := by
      rw [xAt_of_lt hi, yAt_of_lt hi]
      conv_lhs => rw [← List.take_append_drop (Lng X - 1) X]
      congr 1
      rw [List.drop_eq_getElem_cons hi, List.drop_eq_nil_of_le (by simp only [Lng]; omega)]
    have h2 : ltPS (X.take (Lng X - 1) ++ [c])
        (X.take (Lng X - 1) ++ [(xAt X (Lng X - 1), yAt X (Lng X - 1))]) := by
      rw [← hXe, ← hQe']
      exact hXS
    rw [Bijectivity.ltPS_append_cancel, ltPS_cons_iff] at h2
    rcases h2 with h' | ⟨_, h'⟩
    · exact h'
    · exact absurd h' (not_ltPS_nil _)
  have hSC : SC ((oper X n).take Q.length ++ [c]) := by rw [hNtake]; exact h
  exact hE.config_false (condA_of_stps hX.1) (I0_of_stps hX.1) hp1 hlenN
    (by rw [hxw, hyw]; exact hwc) hcl hSC.2.2.2.1 hSC.2.2.2.2

/-- **Theorem SC, Part 2: a sequence satisfying SC is standard** (COMB §8b). -/
theorem ctps_of_SC {M : PS} (h : SC M) : CTPS M := ctps_of_SC_len _ M rfl h

end Googology.Trans.PSS.Forest
