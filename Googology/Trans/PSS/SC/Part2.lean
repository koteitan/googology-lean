import Googology.Trans.PSS.SC.Step
import Googology.Trans.PSS.Rank

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

end Googology.Trans.PSS.Forest
