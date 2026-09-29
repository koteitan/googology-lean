import Googology.Trans.PSS.Main.BarEps
import Googology.Trans.PSS.Main.Cited2

/-!
# Tools for PL (`proof/PROOF-3.md` §14.3)

* `mem_loc_dropLast`: an element of the localization of `b` other than `b` is a suffix
  maximum below `b`.
* `eps_root_le_hi'`: every epsilon root below a non-epsilon root `w` is below `(0, hi(w))`
  (the proof of `eps_root_le_hi` of `Main/BarNonEps.lean`, which comes after `Main/E12.lean`).
* `prefix_addT`: a proper prefix of `A + π` is a prefix of `A` or `A + π|_q`.
* `pref_or_lt`: a list of `y = 2` terms below `G ++ L` (with `L` of `y ≤ 1`) is a prefix of
  `G` or below one.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-! ## The localization -/

theorem locFrom_split {α : WP} (hα : NFP α) : ∀ (n : ℕ) (cur : Ordinal.{0}), 1 ≤ cur →
    ∀ (l₁ : List WP) (q : WP) (l₂ : List WP), locFrom α n cur = l₁ ++ q :: l₂ →
      SufMax α q ∧ cur < q.val ∧ ∀ r ∈ l₂, q.val < r.val := by
  intro n
  induction n with
  | zero => intro cur _ l₁ q l₂ h; simp [locFrom] at h
  | succ n ih =>
    intro cur h1 l₁ q l₂ h
    cases hstep : locStep α cur with
    | none => simp [locFrom, hstep] at h
    | some q0 =>
      have eL : locFrom α (n + 1) cur = q0 :: locFrom α n q0.val := by simp [locFrom, hstep]
      rw [eL] at h
      obtain ⟨hq0s, -⟩ := locStep_sufMax hα h1 hstep
      obtain ⟨-, hcq0, -⟩ := locStep_some hstep
      rcases l₁ with _ | ⟨x, l₁⟩
      · simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hq0s, hcq0, fun r hr => ?_⟩
        obtain ⟨l₁', l₂', e⟩ := List.append_of_mem hr
        exact (ih q0.val hq0s.2.1.le l₁' r l₂' e).2.1
      · simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        obtain ⟨a1, a2, a3⟩ := ih q0.val hq0s.2.1.le l₁ q l₂ h
        exact ⟨a1, lt_trans hcq0 a2, a3⟩

theorem locFrom_sub0 {α : WP} : ∀ (n : ℕ) (cur : Ordinal.{0}) (q : WP),
    q ∈ locFrom α n cur → q ∈ sub0 α := by
  intro n
  induction n with
  | zero => intro cur q h; simp [locFrom] at h
  | succ n ih =>
    intro cur q h
    cases hstep : locStep α cur with
    | none => simp [locFrom, hstep] at h
    | some q0 =>
      have eL : locFrom α (n + 1) cur = q0 :: locFrom α n q0.val := by simp [locFrom, hstep]
      rw [eL] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact (locStep_some hstep).1
      · exact ih _ _ h

theorem mem_loc_sub0 {b q : WP} (h : q ∈ loc b) : q ∈ sub0 b := locFrom_sub0 _ _ _ h

/-- An element of the localization of `b` other than `b` is a suffix maximum below `b`. -/
theorem mem_loc_dropLast {b : WP} (hb : NFP b) (hb0 : b.lvl = 0) (h1 : 1 < b.val) {γ : WP}
    (hγ : γ ∈ (loc b).dropLast) : SufMax b γ ∧ γ.val < b.val := by
  have hcnt : cntAbove b 1 ≤ (sub0 b).length := List.length_filter_le _ _
  obtain ⟨hlast, -, -⟩ := locFrom_spec hb hb0 _ 1 le_rfl h1 hcnt
  have hl : (loc b).dropLast ++ [b] = loc b := List.dropLast_append_getLast? b hlast
  obtain ⟨l₁, l₂, e⟩ := List.append_of_mem hγ
  have e' : loc b = l₁ ++ γ :: (l₂ ++ [b]) := by rw [← hl, e]; simp
  obtain ⟨a1, -, a3⟩ := locFrom_split hb _ 1 le_rfl l₁ γ (l₂ ++ [b]) e'
  exact ⟨a1, a3 b (by simp)⟩

/-- A term whose argument has a part of level `≥ 1` is an epsilon number of level `0`. -/
theorem isEpsLevel_of_argD {g : WP} (h0 : g.lvl = 0) (h : argD g.arg ≠ []) :
    isEpsLevel g 0 = true := by
  obtain ⟨m, a⟩ := g
  simp only [WP.lvl_th] at h0; subst h0
  simp only [WP.arg_th] at h
  cases a with
  | nil => simp [argD] at h
  | cons q a =>
    have hq : 1 ≤ q.lvl := by
      by_contra hq
      apply h
      simp [argD, hq]
    simp [isEpsLevel, WP.arg, hq]

/-! ## Epsilon roots below a non-epsilon root -/

/-- **Every epsilon root below a non-epsilon root `w` is below `(0, hi(w))`** (as
`eps_root_le_hi` of `Main/BarNonEps.lean`). -/
theorem eps_root_le_hi' {w z : Tm} (hw : Std w) (hwe : isEps w = false) (hwc : w.cs ≠ [])
    (hz : Std z) (hze : isEps z = true) (hzw : z ≤ w) :
    hiOf w ≠ [] ∧ z ≤ Tm.node 0 (hiOf w) := by
  obtain ⟨C, hC⟩ : ∃ C, w.cs.getLast? = some C := by
    cases h' : w.cs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h') hwc
    | some C => exact ⟨C, rfl⟩
  obtain ⟨-, hCl, -⟩ := last_child_of_noneps hw hwe hC
  have hzne : z.cs ≠ [] := by
    intro h; rw [std_node_y hz, h] at hze; simp [isEps] at hze
  have hzw' : z < w := lt_of_le_of_ne hzw (fun e => by rw [e] at hze; rw [hze] at hwe; simp at hwe)
  have hB : z.cs < hiOf w ++ loOf w := by
    rw [← cs_eq_hi_append_lo hw]
    exact (Tm.lt_iff_cs_lt (by rw [std_node_y hz, std_node_y hw]; rfl)).mp hzw'
  have key : z.cs ++ [] < hiOf w ++ loOf w ↔
      z.cs < hiOf w ∨ (z.cs = hiOf w ∧ [] < loOf w) := by
    apply lex_blocks
    intro a ha b hb
    have hay : a.y = 1 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact y_of_eps_child hz hze ha
      · exact y_of_mem_hi hw ha
    have hby : b.y = 0 := by
      simp only [List.nil_append] at hb; exact y_of_mem_lo hb
    exact Tm.lt_of_y_lt (by omega)
  rw [List.append_nil] at key
  rcases key.mp hB with h | ⟨h, -⟩
  · refine ⟨fun hh => by rw [hh] at h; exact List.not_lt_nil _ h, le_of_lt ?_⟩
    rw [std_node_y hz]
    exact (Tm.lt_iff_cs_lt (s := Tm.node 0 z.cs) (t := Tm.node 0 (hiOf w)) rfl).mpr h
  · refine ⟨fun hh => hzne (by rw [h, hh]), le_of_eq ?_⟩
    rw [std_node_y hz, h]

/-! ## Lists -/

theorem prefix_addT {A π X : List Tm} (hA : Desc A) (hX : X <+: addT A π)
    (hlt : X.length < (addT A π).length) :
    X <+: A ∨ ∃ q, 1 ≤ q ∧ q < π.length ∧ X = addT A (π.take q) := by
  cases π with
  | nil => left; simpa [addT_nil] using hX
  | cons b0 B =>
    rw [addT_cons hA] at hX hlt
    set A' := A.takeWhile (fun a => !decide (a < b0)) with hA'def
    have hA' : A' <+: A := List.takeWhile_prefix _
    have hXe : X = (A' ++ b0 :: B).take X.length := List.prefix_iff_eq_take.mp hX
    by_cases hle : X.length ≤ A'.length
    · left
      rw [hXe, List.take_append_of_le_length hle]
      exact (List.take_prefix _ _).trans hA'
    · right
      have hq : 1 ≤ X.length - A'.length := by omega
      refine ⟨X.length - A'.length, hq, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons] at hlt ⊢; omega
      · obtain ⟨q', hq'⟩ : ∃ q', X.length - A'.length = q' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
        rw [hq', List.take_succ_cons, addT_cons hA, ← hA'def, hXe, List.take_append,
          List.take_of_length_le (by omega), hq', List.take_succ_cons]

/-- A non-empty list of `y = 2` terms below `G ++ L`, where `L` has `y ≤ 1`, is `G|_i` or
below `G|_i` for some `i ∈ [1, |G|]`. -/
theorem pref_or_lt : ∀ (σ G L : List Tm), (∀ c ∈ σ, c.y = 2) → (∀ l ∈ L, l.y ≤ 1) → σ ≠ [] →
    σ < G ++ L → ∃ i, 1 ≤ i ∧ i ≤ G.length ∧ (σ = G.take i ∨ σ < G.take i)
  | [], _, _, _, _, hne, _ => absurd rfl hne
  | s :: σ, [], L, hσ, hL, _, h => by
    exfalso
    cases L with
    | nil => exact List.not_lt_nil _ h
    | cons l L =>
      have hls : l < s := Tm.lt_of_y_lt (by rw [hσ s (by simp)]; have := hL l (by simp); omega)
      rcases List.cons_lt_cons_iff.mp h with h1 | ⟨e, -⟩
      · exact lt_asymm h1 hls
      · rw [e] at hls; exact lt_irrefl _ hls
  | s :: σ, g :: G, L, hσ, hL, _, h => by
    rw [List.cons_append] at h
    rcases List.cons_lt_cons_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact ⟨1, le_rfl, by simp, Or.inr (by simp [List.cons_lt_cons_iff, h1])⟩
    · by_cases hσn : σ = []
      · subst hσn; exact ⟨1, le_rfl, by simp, Or.inl (by simp)⟩
      · obtain ⟨i, hi1, hiG, hi⟩ := pref_or_lt σ G L (fun c hc => hσ c (by simp [hc])) hL hσn h2
        refine ⟨i + 1, by omega, by simp; omega, ?_⟩
        rw [List.take_succ_cons]
        rcases hi with e | lt
        · exact Or.inl (by rw [e])
        · exact Or.inr (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, lt⟩))

end Googology.Trans.PSS.Main
