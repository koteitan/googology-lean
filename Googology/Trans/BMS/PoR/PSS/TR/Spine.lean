import Googology.Trans.BMS.PoR.PSS.TR.PHi

/-!
# The rightmost path of a term

A term `t` is its rightmost path: `t = rebuild sp ℓ`, where the **spine** `sp`
lists, for each node `a_0 = t, a_1, …, a_{d-1}` above the last column `ℓ`, its `y`
and its children before the next path node (`exists_spine`).  The columns are
`t.cols = cut sp ++ [(d, y_ℓ)]` (`rebuild_cols`), and the path node `a_i` is the
column `pos sp i = |cut (sp.take i)|`, with `x = i` (`xAt_pos`); every later
column is higher (`x_gt_of_pos_lt`).  So the row-0 ancestors of the last column
are exactly the path nodes (`anc_eq_pos`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi

/-- The spine of a path: for each node, its `y` and its children before the path
child. -/
abbrev Spine := List (ℕ × List Tm)

/-- The term with the spine `sp` and the term `u` at the bottom of the path. -/
def rebuild : Spine → Tm → Tm
  | [], u => u
  | (y, cs) :: sp, u => .node y (cs ++ [rebuild sp u])

/-- The columns of the spine, down to (not including) the bottom. -/
def cut : Spine → PS
  | [] => []
  | (y, cs) :: sp => (0, y) :: shUp 1 (mat cs ++ cut sp)

@[simp] theorem rebuild_nil (u : Tm) : rebuild [] u = u := rfl

@[simp] theorem rebuild_cons (y : ℕ) (cs : List Tm) (sp : Spine) (u : Tm) :
    rebuild ((y, cs) :: sp) u = .node y (cs ++ [rebuild sp u]) := rfl

theorem rebuild_append (sp sp' : Spine) (u : Tm) :
    rebuild (sp ++ sp') u = rebuild sp (rebuild sp' u) := by
  induction sp with
  | nil => rfl
  | cons e sp ih => obtain ⟨y, cs⟩ := e; simp [ih]

theorem shUp_append' (c : ℕ) (l l' : PS) : shUp c (l ++ l') = shUp c l ++ shUp c l' :=
  List.map_append

theorem shUp_shUp (a b : ℕ) (l : PS) : shUp a (shUp b l) = shUp (b + a) l := by
  simp only [shUp, List.map_map]
  apply List.map_congr_left
  intro q _
  simp [Nat.add_assoc]

theorem shUp_zero' (l : PS) : shUp 0 l = l := by simp [shUp]

theorem shUp_cons (c : ℕ) (q : ℕ × ℕ) (l : PS) : shUp c (q :: l) = (q.1 + c, q.2) :: shUp c l :=
  rfl

theorem rebuild_cols (sp : Spine) (u : Tm) :
    (rebuild sp u).cols = cut sp ++ shUp sp.length u.cols := by
  induction sp with
  | nil => simp [cut, shUp_zero']
  | cons e sp ih =>
    obtain ⟨y, cs⟩ := e
    rw [rebuild_cons, Tm.cols_eq, mat_append, mat_cons, mat_nil, List.append_nil, ih, cut]
    simp only [List.length_cons, shUp_append', shUp_shUp, List.cons_append, List.append_assoc]

theorem cut_append (sp sp' : Spine) : cut (sp ++ sp') = cut sp ++ shUp sp.length (cut sp') := by
  induction sp with
  | nil => simp [cut, shUp_zero']
  | cons e sp ih =>
    obtain ⟨y, cs⟩ := e
    simp only [List.cons_append, cut, ih, List.length_cons, shUp_append', shUp_shUp,
      List.append_assoc]

theorem leaf_cols (y : ℕ) : (Tm.node y []).cols = [(0, y)] := by
  rw [Tm.cols_eq]; rfl

/-- Every term is its rightmost path down to a leaf. -/
theorem exists_spine : ∀ (t : Tm), ∃ sp yl, t = rebuild sp (.node yl [])
  | .node y cs => by
    rcases eq_or_ne cs [] with rfl | hne
    · exact ⟨[], y, rfl⟩
    · obtain ⟨sp, yl, e⟩ := exists_spine (cs.getLast hne)
      refine ⟨(y, cs.dropLast) :: sp, yl, ?_⟩
      rw [rebuild_cons, ← e, List.dropLast_append_getLast hne]
termination_by t => t.size
decreasing_by exact Tm.size_lt_of_mem (List.getLast_mem hne)

/-! ## Positions -/

/-- The column of the path node `a_i`. -/
def pos (sp : Spine) (i : ℕ) : ℕ := (cut (sp.take i)).length

theorem cols_split {sp : Spine} {i : ℕ} (hi : i < sp.length) (yl : ℕ) :
    (rebuild sp (.node yl [])).cols =
      cut (sp.take i) ++ ((i, (sp[i]).1) :: (shUp (i + 1) (mat (sp[i]).2 ++ cut (sp.drop (i + 1)))
        ++ [(sp.length, yl)])) := by
  have hsp : sp = sp.take i ++ sp[i] :: sp.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i sp]
    rw [List.drop_eq_getElem_cons hi]
  have hlen : (sp.take i).length = i := by simp; omega
  have hcut : cut sp = cut (sp.take i) ++ shUp i (cut (sp[i] :: sp.drop (i + 1))) := by
    conv_lhs => rw [hsp]
    rw [cut_append, hlen]
  rw [rebuild_cols, leaf_cols, hcut]
  obtain ⟨y, cs⟩ := sp[i]
  simp only [cut, shUp, List.map_cons, List.map_nil, List.map_append, List.map_map,
    Function.comp_def, List.append_assoc, List.cons_append, zero_add]
  congr 3
  · apply List.map_congr_left; intro q _
    rw [show q.1 + 1 + i = q.1 + (i + 1) by omega]
  · congr 1
    apply List.map_congr_left; intro q _
    rw [show q.1 + 1 + i = q.1 + (i + 1) by omega]

theorem xAt_pos {sp : Spine} {i : ℕ} (hi : i < sp.length) (yl : ℕ) :
    xAt (rebuild sp (.node yl [])).cols (pos sp i) = i ∧
      yAt (rebuild sp (.node yl [])).cols (pos sp i) = (sp[i]).1 := by
  rw [cols_split hi yl, pos]
  constructor
  · have := xAt_append_right (cut (sp.take i)) ((i, (sp[i]).1) :: shUp (i + 1)
      (mat (sp[i]).2 ++ cut (sp.drop (i + 1))) ++ [(sp.length, yl)]) 0
    simpa using this
  · have := yAt_append_right (cut (sp.take i)) ((i, (sp[i]).1) :: shUp (i + 1)
      (mat (sp[i]).2 ++ cut (sp.drop (i + 1))) ++ [(sp.length, yl)]) 0
    simpa using this

theorem length_rebuild_cols (sp : Spine) (yl : ℕ) :
    (rebuild sp (.node yl [])).cols.length = (cut sp).length + 1 := by
  rw [rebuild_cols, leaf_cols]; simp [length_shUp]

/-- The last column is `(d, y_ℓ)`. -/
theorem xAt_last (sp : Spine) (yl : ℕ) :
    xAt (rebuild sp (.node yl [])).cols (cut sp).length = sp.length ∧
      yAt (rebuild sp (.node yl [])).cols (cut sp).length = yl := by
  rw [rebuild_cols, leaf_cols]
  constructor
  · have := xAt_append_right (cut sp) (shUp sp.length [(0, yl)]) 0
    simpa [shUp] using this
  · have := yAt_append_right (cut sp) (shUp sp.length [(0, yl)]) 0
    simpa [shUp] using this

/-- Every column after the path node `a_i` is higher than it. -/
theorem x_gt_of_pos_lt {sp : Spine} {i : ℕ} (hi : i < sp.length) (yl : ℕ) {j : ℕ}
    (h1 : pos sp i < j) (h2 : j < (rebuild sp (.node yl [])).cols.length) :
    i < xAt (rebuild sp (.node yl [])).cols j := by
  have hsplit := cols_split hi yl
  set R := shUp (i + 1) (mat (sp[i]).2 ++ cut (sp.drop (i + 1))) ++ [(sp.length, yl)]
  have hR : ∀ q ∈ R, i < q.1 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · simp only [shUp, List.mem_map] at hq
      obtain ⟨q', _, rfl⟩ := hq
      omega
    · rw [List.mem_singleton.mp hq]; exact hi
  obtain ⟨r, rfl⟩ : ∃ r, j = pos sp i + 1 + r := ⟨j - pos sp i - 1, by omega⟩
  have hlenM : (rebuild sp (.node yl [])).cols.length = (cut (sp.take i)).length + 1 + R.length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hr : r < R.length := by rw [hlenM] at h2; rw [pos] at h2; omega
  rw [hsplit]
  rw [show pos sp i + 1 + r = (cut (sp.take i)).length + (1 + r) by rw [pos]; omega,
    xAt_append_right]
  rw [show 1 + r = r + 1 by omega, xAt_cons_succ]
  rw [xAt_of_lt hr]
  exact hR _ (List.getElem_mem hr)

theorem pos_lt_cut_length {sp : Spine} {i : ℕ} (hi : i < sp.length) :
    pos sp i < (cut sp).length := by
  have := length_rebuild_cols sp 0
  have hsplit := cols_split hi 0
  have := congrArg List.length hsplit
  simp only [List.length_append, List.length_cons] at this
  rw [pos]
  omega

/-- The path nodes are the row-0 ancestors of the last column. -/
theorem anc_pos {sp : Spine} {i : ℕ} (hi : i < sp.length) (yl : ℕ) :
    Anc (rebuild sp (.node yl [])).cols (pos sp i) (cut sp).length := by
  refine ⟨pos_lt_cut_length hi, fun j h1 h2 => ?_⟩
  rw [(xAt_pos hi yl).1]
  exact x_gt_of_pos_lt hi yl h1 (by rw [length_rebuild_cols]; omega)

theorem anc_eq_pos {sp : Spine} {yl a : ℕ} (h : Anc (rebuild sp (.node yl [])).cols a (cut sp).length) :
    ∃ i < sp.length, a = pos sp i := by
  set M := (rebuild sp (.node yl [])).cols
  set i := xAt M a
  have hlen : M.length = (cut sp).length + 1 := length_rebuild_cols sp yl
  -- `i < d`: otherwise the last column is not higher
  have hid : i < sp.length := by
    by_contra hc
    have := h.2 (cut sp).length h.1 le_rfl
    rw [(xAt_last sp yl).1] at this
    omega
  refine ⟨i, hid, ?_⟩
  rcases lt_trichotomy a (pos sp i) with hlt | heq | hgt
  · exfalso
    have := h.2 (pos sp i) hlt (pos_lt_cut_length hid).le
    rw [(xAt_pos hid yl).1] at this
    exact lt_irrefl _ this
  · exact heq
  · exfalso
    have := x_gt_of_pos_lt hid yl hgt (by rw [hlen]; exact Nat.lt_succ_of_lt h.1)
    exact lt_irrefl _ this

end Googology.Trans.PSS.TR
