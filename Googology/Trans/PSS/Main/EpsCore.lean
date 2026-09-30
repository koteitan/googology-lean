import Googology.Trans.PSS.Main.FactBar1

/-!
# Small facts on roots used by the epsilon-root files

These lemmas were in `Main/Reach.lean`, `Main/Pattern.lean` and
`Main/BarNonEps.lean`.  They are collected here, before `Main/Fold.lean`, so that
`Main/EpsRoots.lean` and `Main/BarEps.lean` (KEY, NS) can be imported by
`Main/E12.lean`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

theorem opow_inj {a b : Ordinal.{0}} (h : ω ^ a = ω ^ b) : a = b :=
  le_antisymm ((opow_le_opow_iff_right one_lt_omega0).mp h.le)
    ((opow_le_opow_iff_right one_lt_omega0).mp h.ge)

theorem ordOf_leaf' : ordOf [Tm.node 0 []] = 1 := TR.ordOf_leaf

theorem std_leaf : Std (Tm.node 0 []) := by
  show Bijectivity.CTPS (Tm.node 0 []).cols
  rw [TR.cols_leaf]; exact (ctps_iff_SC _).mpr (by decide)

theorem ordOf_inj {x y : List Tm} (hx : StdOrd x) (hy : StdOrd y) (h : ordOf x = ordOf y) :
    x = y := by
  rcases (ordOf_le_iff hx hy).mpr h.le with e | e
  · exact e
  · exact absurd h (ne_of_lt ((ordOf_lt_iff hx hy).mp e))

theorem ordOf_le_iff' {x y : List Tm} (hx : StdOrd x) (hy : StdOrd y) :
    ordOf x ≤ ordOf y ↔ (x = y ∨ x < y) := (ordOf_le_iff hx hy).symm

/-- A node with two or more roots is not additive principal. -/
theorem not_pr_of_two {t t' : Tm} {S : List Tm} (h : StdOrd (t :: t' :: S)) :
    ¬ Pr (ordOf (t :: t' :: S)) := by
  intro hP
  have ht : Std t := ((stdOrd_iff _).mp h).2 t (by simp)
  obtain ⟨p, hp⟩ := pr_iff.mp hP
  have hlog := log_ordOf_cons h (ordOf_single_eq_opow ht)
  rw [hp, log_opow one_lt_omega0] at hlog
  rw [ordOf_cons h, hlog, ← ordOf_single_eq_opow ht] at hp
  have hpos : 0 < ordOf (t' :: S) := by
    have := (ordOf_lt_iff stdOrd_nil (stdOrd_of_append_right (A := [t]) h)).mp (by simp)
    rwa [ordOf_nil] at this
  have := lt_add_of_pos_right (ordOf [t]) hpos
  rw [hp] at this
  exact lt_irrefl _ this

theorem anchor_node {cs : List Tm} (h : 2 ≤ cs.length) :
    anchor (.node 0 cs) = some (.node 0 cs.dropLast) := by
  simp [anchor, h]

/-! ## Epsilon roots -/

theorem one_lt_ordOf_of_cs {N : Tm} (hN : Std N) (hcs : N.cs ≠ []) : 1 < ordOf [N] := by
  rw [← ordOf_leaf']
  apply ordOf_single_lt std_leaf hN
  rw [std_node_y hN]
  exact (Tm.lt_iff_cs_lt (s := Tm.node 0 []) (t := Tm.node 0 N.cs) rfl).mpr
    (by obtain ⟨c, cs, h⟩ := List.exists_cons_of_ne_nil hcs; rw [h]; exact List.nil_lt_cons _ _)


theorem last_child_of_noneps {N C : Tm} (hN : Std N) (hne : isEps N = false)
    (hC : N.cs.getLast? = some C) : C.y = 0 ∧ C ∈ loOf N ∧ Std C := by
  have hN0 : N.y = 0 := by rw [std_node_y hN]; rfl
  have hCy : C.y = 0 := isEps_eq_false_y hN0 hne hC
  have hCmem : C ∈ N.cs := List.mem_of_getLast? hC
  exact ⟨hCy, List.mem_filter.mpr ⟨hCmem, by simp [hCy]⟩,
    std_of_tgood_y0 (tgood_child hN hCmem) hCy⟩

theorem log0_getLast {N C : Tm} (hne : isEps N = false) (hN : Std N)
    (hC : N.cs.getLast? = some C) : (log0 N).getLast? = some C := by
  obtain ⟨hCy, -, -⟩ := last_child_of_noneps hN hne hC
  unfold log0
  rw [getLast?_addAll, List.getLast?_append]
  have : (N.cs.filter (fun s => decide (s.y = 0))).getLast? = some C := by
    rw [← List.dropLast_append_getLast? C hC, List.filter_append]
    simp [hCy]
  rw [this]; rfl

/-- **An epsilon value comes from an epsilon root.** -/
theorem isEps_of_InE {z : Tm} (hz : Std z) (h : InE (ordOf [z])) : isEps z = true := by
  by_contra hne
  have hne' : isEps z = false := by simpa using hne
  by_cases hcs : z.cs = []
  · have hz1 : z = Tm.node 0 [] := by rw [std_node_y hz, hcs]
    rw [hz1, ordOf_leaf'] at h
    simp [InE] at h; exact absurd h (ne_of_gt one_lt_omega0)
  · obtain ⟨C, hC⟩ : ∃ C, z.cs.getLast? = some C := by
      cases h' : z.cs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h') hcs
      | some C => exact ⟨C, rfl⟩
    have hlog : ordOf [z] = ω ^ ordOf (log0 z) := by
      rw [ordOf_single, lemmaR_log hz hne']; rfl
    have e : ordOf [z] = ordOf (log0 z) := by
      have := h; unfold InE at this; rw [hlog] at this ⊢
      exact opow_inj this
    have hlz : log0 z = [z] := ordOf_inj (stdOrd_log0 hz) (stdOrd_single hz) e.symm
    have hl := log0_getLast hne' hz hC
    rw [hlz] at hl
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    obtain ⟨-, hCl, -⟩ := last_child_of_noneps hz hne' hC
    have := lt_of_mem_lo hz hCl
    rw [← hl] at this
    exact lt_irrefl _ this

theorem y_of_eps_child {z c : Tm} (hz : Std z) (he : isEps z = true) (hc : c ∈ z.cs) : c.y = 1 := by
  have hv := valid_of_std hz
  rw [std_node_y hz] at hv
  have hne : z.cs ≠ [] := List.ne_nil_of_mem hc
  have hl : (z.cs.getLast hne).y = 0 + 1 := by
    have h1 := y_le_of_std hz (List.getLast_mem hne)
    have h2 : 1 ≤ (z.cs.getLast hne).y := by
      have := he
      rw [std_node_y hz] at this
      simp only [isEps, List.getLast?_eq_some_getLast hne, decide_eq_true_eq] at this
      exact this
    omega
  have := hv.eps_all hne hl c hc
  omega

end Googology.Trans.PSS.Main
