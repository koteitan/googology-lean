import Googology.Trans.PSS.TR.Dup

/-!
# Blocks of path nodes: positions, Lemma W, one propagation step

`proof/TR-2.md` §4b.0 (Positions) and §4b.1 (Lemma W).

* `PosRel c cn`: the columns of `cn` agree with those of `c` up to the last column
  `q` of `c`, then continue (`Q ≠ ()`) with a column below `q`.  Then `cn < c`
  (`PosRel.lt`), it lifts to the parent (`PosRel.up`, `PosRel.rebuild`).
* `witness_lt` (**Lemma W**): the witnesses of `a` are below `a⟨n⟩`.
* `wit_bound`: M4 with `E = 𝒯(a⟨n⟩)`.
* `path_step`: one step of the propagation, by P-lo or P-hi.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal
open Bijectivity (ltPS lePS)

/-! ## Columns -/

theorem ltPS_replace_last :
    ∀ {A R : PS} {q : ℕ × ℕ} {Q : PS}, ltPS A (R ++ [q]) → A.length ≤ R.length → Q ≠ [] →
      ltPS A (R ++ Q)
  | [], R, q, Q, _, _, hQ => by
    obtain ⟨q0, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
    cases R <;> exact trivial
  | a :: A, [], q, Q, _, hl, _ => by simp at hl
  | a :: A, r :: R, q, Q, h, hl, hQ => by
    rw [List.cons_append, ltPS_cons_iff] at h ⊢
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, ltPS_replace_last h (by simp at hl; omega) hQ⟩

/-- `cn` continues `c` below its last column. -/
def PosRel (c cn : Tm) : Prop :=
  ∃ R q Q, c.cols = R ++ [q] ∧ cn.cols = R ++ Q ∧ Q ≠ [] ∧ ∀ q' ∈ Q.head?, PLt q' q

theorem PosRel.lt {c cn : Tm} (h : PosRel c cn) : cn < c := by
  obtain ⟨R, q, Q, hc, hcn, hQ, hq⟩ := h
  rw [Tm.lt_def, hc, hcn]
  obtain ⟨q0, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
  refine (Bijectivity.ltPS_append_cancel R (q0 :: Q') [q]).mpr ?_
  rw [ltPS_cons_iff]
  exact Or.inl (hq q0 (by simp))

theorem PLt_shUp {p q : ℕ × ℕ} (c : ℕ) (h : PLt p q) : PLt (p.1 + c, p.2) (q.1 + c, q.2) := by
  unfold PLt at *; simp only; omega

theorem PosRel.up {c cn : Tm} (h : PosRel c cn) (k : ℕ) (cs : List Tm) :
    PosRel (.node k (cs ++ [c])) (.node k (cs ++ [cn])) := by
  obtain ⟨R, q, Q, hc, hcn, hQ, hq⟩ := h
  refine ⟨(0, k) :: shUp 1 (mat cs ++ R), (q.1 + 1, q.2), shUp 1 Q, ?_, ?_, ?_, ?_⟩
  · rw [Tm.cols_eq, mat_append, mat_cons, mat_nil, List.append_nil, hc]
    simp [shUp]
  · rw [Tm.cols_eq, mat_append, mat_cons, mat_nil, List.append_nil, hcn]
    simp [shUp]
  · simpa [shUp] using hQ
  · intro q' hq'
    obtain ⟨q0, Q', rfl⟩ := List.exists_cons_of_ne_nil hQ
    simp only [shUp, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hq'
    rw [← hq']
    exact PLt_shUp 1 (hq q0 (by simp))

theorem PosRel.rebuild {c cn : Tm} (h : PosRel c cn) :
    ∀ sp : Spine, PosRel (rebuild sp c) (rebuild sp cn)
  | [] => h
  | (y, cs) :: sp => (PosRel.rebuild h sp).up y cs

/-! ## Lemma W -/

theorem cols_length_eq_size (t : Tm) : t.cols.length = t.size := by
  induction t using Tm.ind with
  | h y cs ih =>
    rw [Tm.cols_eq, List.length_cons, length_shUp, mat_eq_flatten, List.length_flatten,
      Tm.size_node, sizeList_eq_sum, List.map_map]
    congr 1
    apply congrArg
    apply List.map_congr_left
    intro c hc
    exact ih c hc

/-- **Lemma W** (`proof/TR-2.md` §4b.1): the witnesses of `a` are below `a⟨n⟩`. -/
theorem witness_lt {k : ℕ} {cs : List Tm} {an : Tm} (hv : Valid (.node k cs))
    (hpos : PosRel (.node k cs) an) :
    (∀ u, Reach k (.node k cs) u → u < an) ∧
      (∀ j < cs.length, Tm.node k (cs.take j) < an) := by
  obtain ⟨R, q, Q, hc, han, hQ, -⟩ := hpos
  have hlenR : R.length + 1 = (Tm.node k cs).size := by
    rw [← cols_length_eq_size, hc]; simp
  have key : ∀ u : Tm, u < .node k cs → u.size < (Tm.node k cs).size → u < an := by
    intro u hu hs
    rw [Tm.lt_def, hc] at hu
    rw [Tm.lt_def, han]
    exact ltPS_replace_last hu (by rw [cols_length_eq_size]; omega) hQ
  refine ⟨fun u hu => key u (hv.reach_lt hu).1 hu.size_lt, fun j hj => key _ ?_ ?_⟩
  · refine (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, ?_⟩)
    conv_rhs => rw [← List.take_append_drop j cs]
    exact lt_of_prefix (by intro e; rw [List.drop_eq_nil_iff] at e; omega)
  · have hne : cs ≠ [] := by rintro rfl; simp at hj
    exact size_lt_of_sublist_dropLast hne (take_sublist_dropLast hj)

/-- **M4 with `E = 𝒯(a⟨n⟩)`**: the visible `ϑ_k`-subterms of the argument of an
epsilon `𝒯(a)` are below `𝒯(a⟨n⟩)`, for a valid epsilon block `a⟨n⟩`. -/
theorem wit_bound {k : ℕ} {H : List Tm} (hv : Valid (.node k H)) (hne : H ≠ [])
    (hl : (H.getLast hne).y = k + 1) {L : List Tm} (hvn : Valid (.node k L)) (hneL : L ≠ [])
    (hlL : (L.getLast hneL).y = k + 1) (hpos : PosRel (.node k H) (.node k L)) :
    ∀ z ∈ starS k (argOf k H), z.val < (trTm (.node k L)).val := by
  obtain ⟨hE1, hE2⟩ := trTm_eps_isEps hneL hlL
  obtain ⟨hw1, hw2⟩ := witness_lt hv hpos
  refine bound hv hne hl hE2 hE1 (fun u hu => ?_) (fun j hj => ?_)
  · exact mono (hv.reach_lt hu).2 hvn (hw1 u hu)
  · exact mono (hv.take j) hvn (hw2 j hj)

/-! ## One propagation step -/

/-- **One step up the path**, by P-lo (the last child of level `≤ k`) or P-hi
(the last child of level `k + 1`). -/
theorem path_step {k m : ℕ} {P : WP → Prop} (hP1 : P one) (hPo : P (om m)) (hmk : m ≤ k)
    {cs : List Tm} {c : Tm} {cn : ℕ → Tm} (hv : Valid (.node k (cs ++ [c])))
    (hvn : ∀ n, Valid (.node k (cs ++ [cn n])))
    (hyeq : c.y = k + 1 → ∀ n, (cn n).y = k + 1) (hylo : c.y ≤ k → ∀ n, (cn n).y ≤ k)
    (hpos : ∀ n, PosRel c (cn n))
    (hcase : c.y = k + 1 → (∀ n, dOf k (cn n) = dOf k c) ∨ rhoOf k c = [])
    (hLC : LC m P c cn) :
    LC m P (.node k (cs ++ [c])) (fun n => .node k (cs ++ [cn n])) := by
  have hcy : c.y ≤ k + 1 := hv.y_le (by simp)
  rcases (show c.y = k + 1 ∨ c.y ≤ k by omega) with hc | hc
  · have hcn := hyeq hc
    have hne : cs ++ [c] ≠ [] := by simp
    have hl : ((cs ++ [c]).getLast hne).y = k + 1 := by simpa using hc
    have hall := hv.eps_all hne hl
    have hvc : Valid c := hv.child (by simp)
    have hvcn : ∀ n, Valid (cn n) := fun n => (hvn n).child (by simp)
    refine eps_lc hP1 hPo hmk hc hcn (fun h hh => hall h (by simp [hh]))
      (fun n => mono (hvcn n) hvc (hpos n).lt) (hcase hc) (fun hHne => ?_) (fun n => ?_)
      (lcx_of_lc hmk hc hcn hLC) (fun n => ?_) (fun β _ hB _ => Bm.arg (by simpa using hmk) hB)
    · exact mono_le hvc (hv.child (by simp [List.getLast_mem hHne]))
        ((List.pairwise_append.mp hv.desc).2.2 _ (List.getLast_mem hHne) c (by simp))
    · have hvcs : Valid (.node k cs) := by
        have := (hvn n).take cs.length; rwa [List.take_left] at this
      exact mono hvcs (hvn n)
        ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, lt_of_prefix (by simp)⟩))
    · exact wit_bound hv hne hl (hvn n) (by simp) (by simpa using hcn n) ((hpos n).up k cs)
  · exact p_lo hP1 hPo hc (hylo hc) hLC

end Googology.Trans.PSS.TR
