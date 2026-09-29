import Googology.Trans.PSS.Main.Basic

/-!
# The ordinals of nodes

`proof/PROOF.md` §2: a node `M = t_1 ⋯ t_m` (a non-increasing list of standard
root terms) has `o(M) = o(t_1) + ⋯ + o(t_m)` with each `o(t_i)` additive
principal (Lemma 2.2), so the list `anfOf M = (o(t_1), …, o(t_m))` is the
additive normal form of `o(M)` (`anf_anfOf`, `sum_anfOf`), and the additive
normal form is unique (`anf_unique`).

* `ordOf_addT`: `o(add(a, b)) = o(a) + o(b)` (Lemma 2.2 (c)).
* `log_ordOf_cons`, `lead_ordOf_cons`: the leading term of `o(t :: S)` is
  `o(t)`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-! ## Sums below a principal number -/

theorem sum_lt_of_forall_lt {P : Ordinal.{0}} (hP : Pr P) :
    ∀ {l : List Ordinal.{0}}, (∀ x ∈ l, x < P) → l.sum < P
  | [], _ => by simpa using hP.pos
  | x :: l, h => by
    rw [List.sum_cons]
    exact hP.add_lt (h x (by simp)) (sum_lt_of_forall_lt hP (fun y hy => h y (by simp [hy])))

/-- The leading exponent of an additive normal form. -/
theorem sum_cons_lt_opow_succ {x : Ordinal.{0}} {l : List Ordinal.{0}}
    (hl : ∀ y ∈ l, y ≤ ω ^ x) : ω ^ x + l.sum < ω ^ (x + 1) := by
  have hP : Pr (ω ^ (x + 1)) := pr_opow _
  have hlt : ω ^ x < ω ^ (x + 1) := (opow_lt_opow_iff_right one_lt_omega0).mpr (lt_add_one x)
  exact hP.add_lt hlt (sum_lt_of_forall_lt hP (fun y hy => lt_of_le_of_lt (hl y hy) hlt))

/-- The additive normal form is unique. -/
theorem anf_unique : ∀ {l l' : List Ordinal.{0}}, ANF l → ANF l' → l.sum = l'.sum → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: l', _, h', e => by
    exfalso
    rw [List.sum_nil, List.sum_cons] at e
    have := (h'.1 y (by simp)).pos
    exact (add_eq_zero_iff.mp e.symm).1 ▸ this |> lt_irrefl _
  | x :: l, [], h, _, e => by
    exfalso
    rw [List.sum_nil, List.sum_cons] at e
    have := (h.1 x (by simp)).pos
    exact (add_eq_zero_iff.mp e).1 ▸ this |> lt_irrefl _
  | x :: l, y :: l', h, h', e => by
    obtain ⟨a, rfl⟩ := pr_iff.mp (h.1 x (by simp))
    obtain ⟨b, rfl⟩ := pr_iff.mp (h'.1 y (by simp))
    have hl : ∀ z ∈ l, z ≤ ω ^ a := (List.pairwise_cons.mp h.2).1
    have hl' : ∀ z ∈ l', z ≤ ω ^ b := (List.pairwise_cons.mp h'.2).1
    rw [List.sum_cons, List.sum_cons] at e
    have hloga : log ω (ω ^ a + l.sum) = a := by
      rw [log_eq_iff one_lt_omega0 (by
        intro h0; exact (opow_pos a omega0_pos).ne' (add_eq_zero_iff.mp h0).1)]
      exact ⟨le_self_add, sum_cons_lt_opow_succ hl⟩
    have hlogb : log ω (ω ^ b + l'.sum) = b := by
      rw [log_eq_iff one_lt_omega0 (by
        intro h0; exact (opow_pos b omega0_pos).ne' (add_eq_zero_iff.mp h0).1)]
      exact ⟨le_self_add, sum_cons_lt_opow_succ hl'⟩
    have hab : a = b := by rw [← hloga, e, hlogb]
    subst hab
    have e' : l.sum = l'.sum := (add_left_cancel_iff).mp e
    rw [anf_unique ⟨fun z hz => h.1 z (by simp [hz]), (List.pairwise_cons.mp h.2).2⟩
      ⟨fun z hz => h'.1 z (by simp [hz]), (List.pairwise_cons.mp h'.2).2⟩ e']

/-! ## Roots are additive principal -/

theorem ordOf_single_eq_opow {t : Tm} (ht : Std t) : ordOf [t] = ω ^ ordOf (bigL t) := by
  rw [ordOf_single, lemmaR ht, ordOf]

theorem pr_ordOf_single {t : Tm} (ht : Std t) : Pr (ordOf [t]) := by
  rw [ordOf_single_eq_opow ht]; exact pr_opow _

theorem ordOf_single_le {s t : Tm} (hs : Std s) (ht : Std t) (h : s ≤ t) :
    ordOf [s] ≤ ordOf [t] := by
  refine (ordOf_le_iff (stdOrd_single hs) (stdOrd_single ht)).mp ?_
  rcases h.lt_or_eq with h | h
  · exact Or.inr (single_lt_single h)
  · exact Or.inl (by rw [h])

theorem ordOf_single_lt {s t : Tm} (hs : Std s) (ht : Std t) (h : s < t) :
    ordOf [s] < ordOf [t] :=
  (ordOf_lt_iff (stdOrd_single hs) (stdOrd_single ht)).mp (single_lt_single h)

theorem ordOf_single_lt_iff {s t : Tm} (hs : Std s) (ht : Std t) :
    ordOf [s] < ordOf [t] ↔ s < t := by
  constructor
  · intro h
    by_contra h'
    exact absurd (ordOf_single_le ht hs (not_lt.mp h')) (not_le.mpr h)
  · exact ordOf_single_lt hs ht

/-! ## The additive normal form of `o(M)` -/

/-- The list `(o(t_1), …, o(t_m))` of a node. -/
noncomputable def anfOf (S : List Tm) : List Ordinal.{0} := S.map (fun t => ordOf [t])

theorem anf_anfOf {S : List Tm} (hS : StdOrd S) : ANF (anfOf S) := by
  rw [stdOrd_iff] at hS
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact pr_ordOf_single (hS.2 t ht)
  · unfold anfOf
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb h => ordOf_single_le (hS.2 b hb) (hS.2 a ha) h)
      hS.1

theorem sum_anfOf : ∀ {S : List Tm}, StdOrd S → (anfOf S).sum = ordOf S
  | [], _ => by simp [anfOf, ordOf_nil]
  | t :: S, h => by
    simp only [anfOf, List.map_cons, List.sum_cons]
    rw [ordOf_cons h]
    congr 1
    exact sum_anfOf (stdOrd_of_append_right (A := [t]) h)

theorem take_anfOf (S : List Tm) (i : ℕ) : (anfOf S).take i = anfOf (S.take i) := by
  simp [anfOf, List.map_take]

theorem stdOrd_take {S : List Tm} (h : StdOrd S) (i : ℕ) : StdOrd (S.take i) := by
  have := List.take_append_drop i S
  rw [← this] at h
  exact stdOrd_of_append_left h

theorem stdOrd_drop {S : List Tm} (h : StdOrd S) (i : ℕ) : StdOrd (S.drop i) := by
  have := List.take_append_drop i S
  rw [← this] at h
  exact stdOrd_of_append_right h

/-- The ordinals of the roots are below `o(t)` times... : every root after the first is
at most the first. -/
theorem ordOf_lt_opow_succ {t : Tm} {S : List Tm} (h : StdOrd (t :: S)) {x : Ordinal.{0}}
    (hx : ordOf [t] = ω ^ x) : ordOf (t :: S) < ω ^ (x + 1) := by
  rw [← sum_anfOf h]
  simp only [anfOf, List.map_cons, List.sum_cons]
  rw [hx]
  apply sum_cons_lt_opow_succ
  intro y hy
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  rw [← hx]
  have hd := (stdOrd_iff _).mp h
  exact ordOf_single_le (hd.2 s (by simp [hs])) (hd.2 t (by simp))
    ((List.pairwise_cons.mp hd.1).1 s hs)

/-- `log_ω o(t :: S)` is the exponent of `o(t)`. -/
theorem log_ordOf_cons {t : Tm} {S : List Tm} (h : StdOrd (t :: S)) {x : Ordinal.{0}}
    (hx : ordOf [t] = ω ^ x) : log ω (ordOf (t :: S)) = x := by
  have hpos : ordOf (t :: S) ≠ 0 := by
    rw [ordOf_cons h, hx]
    intro h0; exact (opow_pos x omega0_pos).ne' (add_eq_zero_iff.mp h0).1
  rw [log_eq_iff one_lt_omega0 hpos]
  refine ⟨?_, ordOf_lt_opow_succ h hx⟩
  rw [ordOf_cons h, hx]; exact le_self_add

/-- **The leading term** `lead(β) = ω^{log_ω β}` of the additive normal form. -/
noncomputable def lead (β : Ordinal.{0}) : Ordinal.{0} := ω ^ log ω β

theorem lead_ordOf_cons {t : Tm} {S : List Tm} (h : StdOrd (t :: S)) :
    lead (ordOf (t :: S)) = ordOf [t] := by
  have ht : Std t := ((stdOrd_iff _).mp h).2 t (by simp)
  rw [lead, log_ordOf_cons h (ordOf_single_eq_opow ht), ordOf_single_eq_opow ht]

theorem lead_le {β : Ordinal.{0}} (hβ : β ≠ 0) : lead β ≤ β := opow_log_le_self ω hβ

/-- A principal number above the leading term is above the whole ordinal. -/
theorem lt_of_lead_lt {β Y : Ordinal.{0}} (hY : Pr Y) (h : lead β < Y) : β < Y := by
  obtain ⟨y, rfl⟩ := pr_iff.mp hY
  have h1 : log ω β < y := (opow_lt_opow_iff_right one_lt_omega0).mp h
  exact lt_of_lt_of_le (lt_opow_succ_log_self one_lt_omega0 β)
    ((opow_le_opow_iff_right one_lt_omega0).mpr (Order.add_one_le_iff.mpr h1))

/-! ## `o(add(a, b)) = o(a) + o(b)` -/

theorem sum_lt_of_all_lt {S : List Tm} (hS : StdOrd S) {b : Tm} (hb : Std b)
    (h : ∀ x ∈ S, x < b) : ordOf S < ordOf [b] := by
  rw [← sum_anfOf hS]
  apply sum_lt_of_forall_lt (pr_ordOf_single hb)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact ordOf_single_lt (((stdOrd_iff _).mp hS).2 x hx) hb (h x hx)

/-- **Lemma 2.2 (c)**: `o(add(a, b)) = o(a) + o(b)`. -/
theorem ordOf_addT {a b : List Tm} (ha : StdOrd a) (hb : StdOrd b) :
    ordOf (addT a b) = ordOf a + ordOf b := by
  rcases b with _ | ⟨b0, B⟩
  · rw [addT_nil, ordOf_nil, add_zero]
  · have hda := ((stdOrd_iff _).mp ha).1
    have hb0 : Std b0 := ((stdOrd_iff _).mp hb).2 b0 (by simp)
    rw [addT_cons hda]
    set p : Tm → Bool := fun x => !decide (x < b0)
    have hsplit : a = a.takeWhile p ++ a.dropWhile p := (List.takeWhile_append_dropWhile).symm
    have ha' : StdOrd (a.takeWhile p ++ a.dropWhile p) := hsplit ▸ ha
    have h1 : StdOrd (a.takeWhile p ++ b0 :: B) := by
      have := stdOrd_addT ha hb
      rwa [addT_cons hda] at this
    rw [ordOf_append' h1]
    conv_rhs => rw [hsplit, ordOf_append' ha']
    rw [add_assoc]
    congr 1
    -- the dropped terms are absorbed by `b0`
    have hd : StdOrd (a.dropWhile p) := stdOrd_of_append_right ha'
    have hlt : ∀ x ∈ a.dropWhile p, x < b0 := by
      intro x hx
      have hdd : Desc (a.dropWhile p) := ((stdOrd_iff _).mp hd).1
      cases hdrop : a.dropWhile p with
      | nil => rw [hdrop] at hx; simp at hx
      | cons y ys =>
        have hy : p y = false := by
          have := List.head_dropWhile_not p (l := a) (by rw [hdrop]; simp)
          simpa [hdrop] using this
        have hy' : y < b0 := by simpa [p] using hy
        rw [hdrop] at hx hdd
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hy'
        · exact lt_of_le_of_lt ((List.pairwise_cons.mp hdd).1 x hx) hy'
    have habs : ordOf (a.dropWhile p) + ordOf [b0] = ordOf [b0] :=
      (pr_ordOf_single hb0).add_eq (sum_lt_of_all_lt hd hb0 hlt)
    rw [ordOf_cons hb, ← add_assoc, habs]

/-! ## The ordinals of nodes are below `T¹ ∩ Ω_1` -/

theorem nfs_trNode (S : List Tm) : NFS (trNode S) :=
  (addAll_spec (fun x hx => by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact NFS.single (trTm_nfp t))).1

theorem ordOf_mem_T1set {S : List Tm} (hS : StdOrd S) : ordOf S ∈ T1set := by
  refine ⟨trNode S, nfs_trNode S, ?_, tr S hS⟩
  apply valS_lt_Om (nfs_trNode S) (m := 0)
  intro q hq
  obtain ⟨x, hx, hqx⟩ := mem_addAll hq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_singleton.mp hqx, (trTm_nf t).2]
  have := std_node_y (((stdOrd_iff _).mp hS).2 t ht)
  rw [this]; rfl

/-- `o(M) < T¹ ∩ Ω_1` for every node. -/
theorem ordOf_lt_T1bound {S : List Tm} (hS : StdOrd S) : ordOf S < T1bound :=
  lt_T1bound_of_mem (ordOf_mem_T1set hS)

end Googology.Trans.PSS.Main
