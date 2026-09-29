import Googology.Trans.PSS.TR.Spine

/-!
# The fundamental sequence on terms

`proof/TR-2.md` §4b.0.  Let `t = rebuild sp ℓ` be a standard root with children
(`d = |sp| ≥ 1`), `ℓ = (d, y_ℓ)` its last column.  `oper t.cols (n+1)` is:

* **Case `i₁ = 1`** (`y_ℓ > 0`, `oper_case1`): `j₀` is the path node `a_i` with
  `y_i < y_ℓ` and `y_h ≥ y_ℓ` for `i < h < d`, and
  `M[n+1] = rebuild (sp.take i) (j0T sp i n)` with `j0T 0 = a_i⁻` (`a_i` without
  `ℓ`) and `j0T (n+1) = rebuild (sp.drop i) (j0T n)`: the slot of `ℓ` holds the
  previous block (item (S) of the paper).
* **Case `i₁ = 0`** (`y_ℓ = 0`, `oper_case0`): `j₀ = a_{d-1}` is the parent of the
  leaf `ℓ`, and `M[n]` has `n` sibling copies of `a_{d-1}⁻` (`dupNode`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi
open _root_.PSS (oper entry Lng idx1)
open Bijectivity (CTPS)

/-- The term of a spine without the bottom: `a_0⁻`. -/
def rmT : Spine → Tm
  | [] => .node 0 []
  | [(y, cs)] => .node y cs
  | (y, cs) :: e :: sp => .node y (cs ++ [rmT (e :: sp)])

theorem rmT_cols : ∀ {sp : Spine}, sp ≠ [] → (rmT sp).cols = cut sp
  | [], h => absurd rfl h
  | [(y, cs)], _ => by simp [rmT, cut, Tm.cols_eq]
  | (y, cs) :: (y', cs') :: sp, _ => by
    rw [rmT, Tm.cols_eq, mat_append, mat_cons, mat_nil, List.append_nil,
      rmT_cols (List.cons_ne_nil _ _)]
    rfl

/-- The blocks of `j₀` in the case `i₁ = 1`: `j0T 0 = a_i⁻`, and the slot of `ℓ`
holds the previous block. -/
def j0T (sp : Spine) (i : ℕ) : ℕ → Tm
  | 0 => rmT (sp.drop i)
  | n + 1 => rebuild (sp.drop i) (j0T sp i n)

/-- The node `M[n]` in the case `i₁ = 0`. -/
def dupNode (sp : Spine) (n : ℕ) : List Tm :=
  let j0m : Tm := .node (sp.getLast?.map Prod.fst |>.getD 0) (sp.getLast?.map Prod.snd |>.getD [])
  if sp.length = 1 then List.replicate n j0m
  else [rebuild (sp.take (sp.length - 2))
    (.node (sp[sp.length - 2]?.map Prod.fst |>.getD 0)
      ((sp[sp.length - 2]?.map Prod.snd |>.getD []) ++ List.replicate n j0m))]

/-! ## The copies of `oper` -/

theorem copyB_eq {M : PS} {j0 j1 d0 k : ℕ} (hj : j0 ≤ j1) (hj1 : j1 ≤ M.length) :
    copyB M j0 j1 d0 k = shUp (k * d0) ((M.drop j0).take (j1 - j0)) := by
  apply List.ext_getElem
  · simp [copyB, shUp]; omega
  · intro r h1 h2
    simp only [copyB, List.getElem_map, List.getElem_range', shUp, List.getElem_take,
      List.getElem_drop]
    have hr : j0 + r < M.length := by simp [copyB] at h1; omega
    simp [entry, List.getElem?_eq_getElem hr]

theorem cols_split_at (sp : Spine) (u : Tm) {i : ℕ} (hi : i ≤ sp.length) :
    (rebuild sp u).cols = cut (sp.take i) ++ shUp i (rebuild (sp.drop i) u).cols := by
  have e : rebuild sp u = rebuild (sp.take i) (rebuild (sp.drop i) u) := by
    rw [← rebuild_append, List.take_append_drop]
  have hlen : (sp.take i).length = i := by simp; omega
  rw [e, rebuild_cols, hlen]

theorem take_cols_pos (sp : Spine) (yl : ℕ) {i : ℕ} (hi : i ≤ sp.length) :
    (rebuild sp (.node yl [])).cols.take (pos sp i) = cut (sp.take i) := by
  rw [cols_split_at sp _ hi, pos, List.take_left]

theorem drop_cols_pos (sp : Spine) (yl : ℕ) {i : ℕ} (hi : i ≤ sp.length) :
    (rebuild sp (.node yl [])).cols.drop (pos sp i) =
      shUp i (cut (sp.drop i)) ++ [(sp.length, yl)] := by
  rw [cols_split_at sp _ hi, pos, List.drop_left, rebuild_cols, leaf_cols, shUp_append']
  simp only [shUp, List.map_cons, List.map_nil, List.length_drop, zero_add]
  congr 3; omega

theorem length_cut_split (sp : Spine) {i : ℕ} (hi : i ≤ sp.length) :
    (cut sp).length = pos sp i + (cut (sp.drop i)).length := by
  have := congrArg List.length (cols_split_at sp (.node 0 []) hi)
  rw [length_rebuild_cols, List.length_append, length_shUp, length_rebuild_cols] at this
  rw [pos]; omega

theorem block_cols_pos (sp : Spine) (yl : ℕ) {i : ℕ} (hi : i ≤ sp.length) :
    ((rebuild sp (.node yl [])).cols.drop (pos sp i)).take ((cut sp).length - pos sp i) =
      shUp i (cut (sp.drop i)) := by
  rw [drop_cols_pos sp yl hi, length_cut_split sp hi,
    show pos sp i + (cut (sp.drop i)).length - pos sp i = (shUp i (cut (sp.drop i))).length by
      rw [length_shUp]; omega, List.take_left]

theorem Lng_rebuild (sp : Spine) (yl : ℕ) :
    Lng (rebuild sp (.node yl [])).cols - 1 = (cut sp).length := by
  rw [Lng, length_rebuild_cols]; omega

theorem entry_last (sp : Spine) (yl : ℕ) :
    entry (rebuild sp (.node yl [])).cols 0 (cut sp).length = sp.length ∧
      entry (rebuild sp (.node yl [])).cols 1 (cut sp).length = yl := by
  rw [← xAt_eq_entry, ← yAt_eq_entry]; exact xAt_last sp yl

theorem cut_ne_nil {sp : Spine} (h : sp ≠ []) : cut sp ≠ [] := by
  obtain ⟨⟨y, cs⟩, sp', rfl⟩ := List.exists_cons_of_ne_nil h
  simp [cut]

theorem one_lt_Lng {sp : Spine} (h : sp ≠ []) (yl : ℕ) : 1 < Lng (rebuild sp (.node yl [])).cols := by
  rw [Lng, length_rebuild_cols]
  have := List.length_pos_of_ne_nil (cut_ne_nil h)
  omega

theorem pos_mono {sp : Spine} {h i : ℕ} (hhi : h < i) (hi : i ≤ sp.length) : pos sp h < pos sp i := by
  unfold pos
  have e : sp.take i = sp.take h ++ (sp.drop h).take (i - h) := by
    rw [← List.take_add]; congr 1; omega
  rw [e, cut_append, List.length_append, length_shUp]
  have hne : (sp.drop h).take (i - h) ≠ [] := by
    intro e'; rw [List.take_eq_nil_iff] at e'; simp at e'; omega
  have := List.length_pos_of_ne_nil (cut_ne_nil hne)
  omega

theorem expCase_rebuild {sp : Spine} {yl : ℕ} (hC : CTPS (rebuild sp (.node yl [])).cols)
    (hsp : sp ≠ []) : ∃ j0 d0, ExpCase (rebuild sp (.node yl [])).cols j0 d0 := by
  refine ctps_expCase hC (one_lt_Lng hsp yl) ?_
  rw [Lng_rebuild, (entry_last sp yl).1]
  intro hc
  exact (List.length_pos_of_ne_nil hsp).ne' hc.1

theorem cut_single (e : ℕ × List Tm) : cut [e] = (0, e.1) :: shUp 1 (mat e.2) := by
  obtain ⟨y, cs⟩ := e; simp [cut]

theorem copies_one (M : PS) (j0 j1 d0 : ℕ) : copies M j0 j1 d0 1 = copyB M j0 j1 d0 0 := by
  simp [copies]

theorem block_eq {sp : Spine} {yl i : ℕ} (hi : i < sp.length) (d0 k : ℕ) :
    copyB (rebuild sp (.node yl [])).cols (pos sp i) (Lng (rebuild sp (.node yl [])).cols - 1) d0 k
      = shUp (k * d0) (shUp i (cut (sp.drop i))) := by
  rw [copyB_eq, Lng_rebuild, block_cols_pos sp yl hi.le]
  · rw [Lng_rebuild]; exact (pos_lt_cut_length hi).le
  · rw [Lng_rebuild, length_rebuild_cols]; omega

/-- **The case `i₁ = 1`.** -/
theorem oper_case1 {sp : Spine} {yl : ℕ} (hC : CTPS (rebuild sp (.node yl [])).cols)
    (hsp : sp ≠ []) (hyl : 0 < yl) :
    ∃ i, ∃ hi : i < sp.length, (sp[i]).1 < yl ∧
      (∀ h (hh : h < sp.length), i < h → yl ≤ (sp[h]).1) ∧
      ∀ n, oper (rebuild sp (.node yl [])).cols (n + 1) = (rebuild (sp.take i) (j0T sp i n)).cols := by
  set M := (rebuild sp (.node yl [])).cols with hM
  obtain ⟨j0, d0, h⟩ := expCase_rebuild hC hsp
  have hLng : Lng M - 1 = (cut sp).length := Lng_rebuild sp yl
  have hi1 : idx1 M (Lng M - 1) = 1 := by
    unfold idx1; rw [if_pos]; rw [hLng, (entry_last sp yl).2]; exact hyl
  have hanc := h.anc
  rw [hLng] at hanc
  obtain ⟨i, hi, rfl⟩ := anc_eq_pos hanc
  obtain ⟨hx, hy, hmin⟩ := h.one hi1
  rw [hLng, (xAt_pos hi yl).1, (xAt_last sp yl).1] at hx
  rw [hLng, (xAt_pos hi yl).2, (xAt_last sp yl).2] at hy
  refine ⟨i, hi, hy, fun h' hh hih => ?_, fun n => ?_⟩
  · have := hmin (pos sp h') (pos_mono hih hh.le) (by rw [hLng]; exact anc_pos hh yl)
    rwa [hLng, (xAt_last sp yl).2, (xAt_pos hh yl).2] at this
  · have hd0 : d0 = sp.length - i := by omega
    have hdi : (sp.drop i).length = sp.length - i := by simp
    rw [oper_eq_copies h (n + 1), take_cols_pos sp yl hi.le]
    conv_rhs => rw [rebuild_cols, show (sp.take i).length = i by simp; omega]
    congr 1
    induction n with
    | zero =>
      rw [copies_one, block_eq hi, zero_mul, shUp_zero', j0T, rmT_cols (by simp; omega)]
    | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by omega, copies_add, ih, copies_one, block_eq hi,
        zero_mul, shUp_zero', j0T, rebuild_cols, hdi, one_mul, hd0, shUp_append', shUp_shUp,
        shUp_shUp, Nat.add_comm]

theorem mat_replicate_succ (x : Tm) (n : ℕ) :
    mat (List.replicate (n + 1) x) = mat (List.replicate n x) ++ x.cols := by
  rw [List.replicate_succ', mat_append, mat_cons, mat_nil, List.append_nil]

/-- **The case `i₁ = 0`.** -/
theorem oper_case0 {sp : Spine} {yl : ℕ} (hC : CTPS (rebuild sp (.node yl [])).cols)
    (hsp : sp ≠ []) (hyl : yl = 0) :
    ∀ n, oper (rebuild sp (.node yl [])).cols (n + 1) = mat (dupNode sp (n + 1)) := by
  set M := (rebuild sp (.node yl [])).cols with hM
  obtain ⟨j0, d0, h⟩ := expCase_rebuild hC hsp
  have hLng : Lng M - 1 = (cut sp).length := Lng_rebuild sp yl
  have hi0 : idx1 M (Lng M - 1) = 0 := by
    unfold idx1; rw [if_neg]; rw [hLng, (entry_last sp yl).2, hyl]; exact lt_irrefl 0
  have hd0 : d0 = 0 := h.d0_zero hi0
  have hanc := h.anc
  rw [hLng] at hanc
  obtain ⟨i, hi, rfl⟩ := anc_eq_pos hanc
  set d := sp.length with hd
  -- `j₀` is the parent of `ℓ`: `i = d - 1`
  have hid : i = d - 1 := by
    by_contra hne
    have hlt : i < d - 1 := by omega
    have hn := h.nextR_true
    rw [hi0] at hn
    simp only [_root_.PSS.nextR, ↓reduceIte] at hn
    obtain ⟨-, -, -, hmin⟩ := (nextrel0_iff M _ _).mp hn
    have h1 := hmin (pos sp (d - 1)) (pos_mono hlt (by omega))
      (by rw [hLng]; exact pos_lt_cut_length (by omega))
    rw [← xAt_eq_map, ← xAt_eq_map, hLng, (xAt_last sp yl).1, (xAt_pos (by omega) yl).1] at h1
    omega
  subst hid
  have hdrop : sp.drop (d - 1) = [sp[d - 1]'(by omega)] := by
    rw [List.drop_eq_getElem_cons (by omega)]
    simp [List.drop_eq_nil_of_le (show sp.length ≤ d - 1 + 1 by omega)]
  set j0m : Tm := .node (sp.getLast?.map Prod.fst |>.getD 0) (sp.getLast?.map Prod.snd |>.getD [])
    with hj0m
  have hj0m' : j0m = .node (sp[d - 1]'(by omega)).1 (sp[d - 1]'(by omega)).2 := by
    rw [hj0m, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]; rfl
  have hblock : ∀ k, copyB M (pos sp (d - 1)) (Lng M - 1) d0 k = shUp (d - 1) j0m.cols := by
    intro k
    rw [block_eq (by omega), hd0, mul_zero, shUp_zero', hdrop, hj0m', Tm.cols_eq, cut_single]
  have hcopies : ∀ n, copies M (pos sp (d - 1)) (Lng M - 1) d0 n =
      shUp (d - 1) (mat (List.replicate n j0m)) := by
    intro n
    induction n with
    | zero => simp [copies, shUp]
    | succ n ih =>
      rw [copies_add, ih, copies_one, hblock, hd0, mul_zero, shUp_zero', mat_replicate_succ,
        shUp_append']
  intro n
  rw [oper_eq_copies h (n + 1), take_cols_pos sp yl (by omega), hcopies, dupNode]
  simp only [← hj0m, ← hd]
  split_ifs with h1
  · rw [h1]; simp [cut, shUp_zero']
  · rw [mat_cons, mat_nil, List.append_nil, rebuild_cols, Tm.cols_eq, mat_append]
    have hsp2 : sp.take (d - 1) = sp.take (d - 2) ++ [sp[d - 2]'(by omega)] := by
      rw [show d - 1 = d - 2 + 1 by omega, List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [hsp2, cut_append, List.getElem?_eq_getElem (by omega)]
    have hlen : (sp.take (d - 2)).length = d - 2 := by simp; omega
    simp only [hlen, cut_single, Option.map_some, Option.getD_some, shUp_append',
      shUp_cons, shUp_shUp, List.append_assoc, List.cons_append]
    rw [show 1 + (d - 2) = d - 1 by omega]

end Googology.Trans.PSS.TR
