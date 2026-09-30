import Googology.Trans.BMS.PoR.PSS.Main.Basic

/-!
# The localization, read off: suffix maxima of the argument

For `α = ϑ_0(ξ)` of `T¹`, the localization ([W07a] Def 4.6) picks, above the
current element, the `ϑ_0`-subterm with the largest argument.  So its elements are
the **suffix maxima** (`SufMax α q`): the subterms `q > 1` whose argument is larger
than the argument of every subterm above `q`.  In particular (`locPred_spec`):

* `α_{n-1}` (`locPred α`) is the largest suffix maximum below `α`, or `τ = 1`
  when there is none.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order

/-- The value of the argument of `ϑ_m(ξ)`. -/
noncomputable def argV (q : WP) : Ordinal.{0} := WP.valS q.arg

/-- `q` is a **suffix maximum** of `α`: a `ϑ_0`-subterm above `1` whose argument is
larger than the argument of every `ϑ_0`-subterm of `α` above `q`. -/
def SufMax (α q : WP) : Prop :=
  q ∈ sub0 α ∧ 1 < q.val ∧ ∀ r ∈ sub0 α, q.val < r.val → argV r < argV q

theorem sub0_spec {α : WP} (hα : NFP α) {q : WP} (hq : q ∈ sub0 α) : NFP q ∧ q.lvl = 0 :=
  let h := starP_spec 0 α hα q hq; ⟨h.1, h.2.1⟩

theorem self_mem_sub0 {a : List WP} : WP.th 0 a ∈ sub0 (.th 0 a) := by
  unfold sub0; rw [starP_th]; simp

theorem sub0_th (a : List WP) : sub0 (.th 0 a) = .th 0 a :: starS 0 a := by
  unfold sub0; rw [starP_th]; simp

theorem val_le_of_mem_sub0 {a : List WP} (hα : NFP (.th 0 a)) {q : WP}
    (hq : q ∈ sub0 (.th 0 a)) : q.val ≤ (WP.th 0 a).val := by
  rw [sub0_th] at hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact le_rfl
  · exact (star_lt_val hα q hq).le

/-- Two principal terms of level `0` with arguments of equal value are equal. -/
theorem eq_of_argV_eq {q r : WP} (hq : NFP q) (hr : NFP r) (hq0 : q.lvl = 0) (hr0 : r.lvl = 0)
    (h : argV q = argV r) : q = r := by
  obtain ⟨m, a⟩ := q
  obtain ⟨m', c⟩ := r
  simp only [WP.lvl_th] at hq0 hr0
  subst hq0; subst hr0
  have := eq_of_valS_eq hq.nfs hr.nfs h
  rw [this]

theorem locStep_none {α : WP} {cur : Ordinal.{0}} (h : locStep α cur = none) :
    ∀ q ∈ sub0 α, q.val ≤ cur := by
  intro q hq
  unfold locStep at h
  rw [List.argmax_eq_none] at h
  by_contra hlt
  push Not at hlt
  have : q ∈ (sub0 α).filter (fun q => decide (cur < q.val)) :=
    List.mem_filter.mpr ⟨hq, by simpa using hlt⟩
  rw [h] at this; simp at this

theorem locStep_some {α : WP} {cur : Ordinal.{0}} {q : WP} (h : locStep α cur = some q) :
    q ∈ sub0 α ∧ cur < q.val ∧ ∀ r ∈ sub0 α, cur < r.val → argV r ≤ argV q := by
  unfold locStep at h
  have hm := List.argmax_mem (Option.mem_def.mpr h)
  have hq := List.mem_filter.mp hm
  refine ⟨hq.1, by simpa using hq.2, fun r hr hlt => ?_⟩
  have hr' : r ∈ (sub0 α).filter (fun q => decide (cur < q.val)) :=
    List.mem_filter.mpr ⟨hr, by simpa using hlt⟩
  have := List.le_of_mem_argmax (f := fun q => WP.valS q.arg) hr' (by
    convert Option.mem_def.mpr h)
  exact this

/-- The step from `cur` picks the least suffix maximum above `cur`. -/
theorem locStep_sufMax {α : WP} (hα : NFP α) {cur : Ordinal.{0}} (h1 : 1 ≤ cur) {q : WP}
    (h : locStep α cur = some q) :
    SufMax α q ∧ ∀ q', SufMax α q' → cur < q'.val → q.val ≤ q'.val := by
  obtain ⟨hq, hlt, hmax⟩ := locStep_some h
  obtain ⟨hqn, hq0⟩ := sub0_spec hα hq
  refine ⟨⟨hq, lt_of_le_of_lt h1 hlt, fun r hr hqr => ?_⟩, fun q' hq' hcq' => ?_⟩
  · obtain ⟨hrn, hr0⟩ := sub0_spec hα hr
    refine lt_of_le_of_ne (hmax r hr (lt_trans hlt hqr)) (fun e => ?_)
    have := eq_of_argV_eq hrn hqn hr0 hq0 e
    rw [this] at hqr; exact lt_irrefl _ hqr
  · by_contra hlt'
    push Not at hlt'
    have h1' := hq'.2.2 q hq hlt'
    have h2' := hmax q' hq'.1 hcq'
    exact absurd h1' (not_lt.mpr h2')

/-- The number of `ϑ_0`-subterm occurrences above `cur`. -/
noncomputable def cntAbove (α : WP) (cur : Ordinal.{0}) : ℕ :=
  ((sub0 α).filter (fun q => decide (cur < q.val))).length

theorem cntAbove_lt {α : WP} {cur : Ordinal.{0}} {q : WP} (hq : q ∈ sub0 α) (hlt : cur < q.val) :
    cntAbove α q.val < cntAbove α cur := by
  unfold cntAbove
  have e : (sub0 α).filter (fun r => decide (q.val < r.val)) =
      ((sub0 α).filter (fun r => decide (cur < r.val))).filter (fun r => decide (q.val < r.val)) := by
    rw [List.filter_filter]
    congr 1
    funext r
    by_cases h : q.val < r.val
    · simp [h, lt_trans hlt h]
    · simp [h]
  rw [e, List.length_filter_lt_length_iff_exists]
  exact ⟨q, List.mem_filter.mpr ⟨hq, by simpa using hlt⟩, by simp⟩

theorem locFrom_spec {α : WP} (hα : NFP α) (hα0 : α.lvl = 0) :
    ∀ (n : ℕ) (cur : Ordinal.{0}), 1 ≤ cur → cur < α.val → cntAbove α cur ≤ n →
      (locFrom α n cur).getLast? = some α ∧
      (∀ q, (locFrom α n cur).dropLast.getLast? = some q →
        SufMax α q ∧ cur < q.val ∧ q.val < α.val ∧
          ∀ q', SufMax α q' → q'.val < α.val → q'.val ≤ q.val) ∧
      ((locFrom α n cur).dropLast.getLast? = none →
        ∀ q', SufMax α q' → cur < q'.val → α.val ≤ q'.val) := by
  intro n
  induction n with
  | zero =>
    intro cur h1 hlt hcnt
    exfalso
    have hmem : α ∈ (sub0 α).filter (fun q => decide (cur < q.val)) := by
      obtain ⟨m, a⟩ := α
      simp only [WP.lvl_th] at hα0; subst hα0
      exact List.mem_filter.mpr ⟨self_mem_sub0, by simpa using hlt⟩
    have := List.length_pos_of_mem hmem
    unfold cntAbove at hcnt; omega
  | succ n ih =>
    intro cur h1 hlt hcnt
    obtain ⟨m, a⟩ := α
    simp only [WP.lvl_th] at hα0; subst hα0
    set α := WP.th 0 a with hαdef
    have hαmem : α ∈ sub0 α := self_mem_sub0
    cases hstep : locStep α cur with
    | none => exact absurd (locStep_none hstep α hαmem) (not_le.mpr hlt)
    | some q =>
      obtain ⟨hqs, hleast⟩ := locStep_sufMax hα h1 hstep
      obtain ⟨hqmem, hcq, -⟩ := locStep_some hstep
      have hqα : q.val ≤ α.val := val_le_of_mem_sub0 hα hqmem
      have eL : locFrom α (n + 1) cur = q :: locFrom α n q.val := by
        simp [locFrom, hstep]
      rw [eL]
      rcases hqα.lt_or_eq with hqα | hqα
      · -- continue from `q`
        have hcnt' : cntAbove α q.val ≤ n := by
          have := cntAbove_lt hqmem hcq; omega
        obtain ⟨hl, hsome, hnone⟩ := ih q.val (le_of_lt hqs.2.1) hqα hcnt'
        have hne : locFrom α n q.val ≠ [] := by
          intro h; rw [h] at hl; simp at hl
        refine ⟨?_, ?_, ?_⟩
        · rw [List.getLast?_cons, hl]; rfl
        · intro p hp
          rw [List.dropLast_cons_of_ne_nil hne] at hp
          rw [List.getLast?_cons] at hp
          cases hd : (locFrom α n q.val).dropLast.getLast? with
          | none =>
            rw [hd] at hp
            simp only [Option.getD_none, Option.some.injEq] at hp
            subst hp
            refine ⟨hqs, hcq, hqα, fun q' hq' hq'α => ?_⟩
            by_contra hgt
            push Not at hgt
            exact absurd (hnone hd q' hq' hgt) (not_le.mpr hq'α)
          | some p' =>
            rw [hd] at hp
            simp only [Option.getD_some, Option.some.injEq] at hp
            subst hp
            obtain ⟨a1, a2, a3, a4⟩ := hsome p' hd
            exact ⟨a1, lt_trans hcq a2, a3, a4⟩
        · intro hd
          rw [List.dropLast_cons_of_ne_nil hne, List.getLast?_cons] at hd
          simp at hd
      · -- `q = α`: the localization ends
        have hqeq : q = α := eq_of_val_eq (sub0_spec hα hqmem).1 hα hqα
        subst hqeq
        have enil : locFrom α n α.val = [] := by
          cases n with
          | zero => rfl
          | succ n =>
            have : locStep α α.val = none := by
              cases h' : locStep α α.val with
              | none => rfl
              | some r =>
                obtain ⟨hr, hr', -⟩ := locStep_some h'
                exact absurd (val_le_of_mem_sub0 hα hr) (not_le.mpr hr')
            simp [locFrom, this]
        rw [enil]
        refine ⟨rfl, fun p hp => by simp at hp, fun _ q' hq' hcq' => hleast q' hq' hcq'⟩

/-- **`α_{n-1}`** (`locPred`): the largest suffix maximum below `α`, or `1`. -/
theorem locPred_spec {α : WP} (hα : NFP α) (hα0 : α.lvl = 0) (h1 : 1 < α.val) :
    (∃ q, SufMax α q ∧ q.val < α.val ∧ (∀ q', SufMax α q' → q'.val < α.val → q'.val ≤ q.val) ∧
      locPred α = q) ∨
    ((∀ q', SufMax α q' → α.val ≤ q'.val) ∧ locPred α = TR.one) := by
  have hcnt : cntAbove α 1 ≤ (sub0 α).length := List.length_filter_le _ _
  obtain ⟨-, hsome, hnone⟩ := locFrom_spec hα hα0 _ 1 le_rfl h1 hcnt
  unfold locPred loc
  cases hd : (locFrom α (sub0 α).length 1).dropLast.getLast? with
  | some q =>
    obtain ⟨a1, -, a3, a4⟩ := hsome q hd
    exact Or.inl ⟨q, a1, a3, a4, rfl⟩
  | none =>
    exact Or.inr ⟨fun q' hq' => hnone hd q' hq' hq'.2.1, rfl⟩

/-- A convenient form: if `q` is a suffix maximum below `α` and no suffix maximum lies
strictly between `q` and `α`, then `α_{n-1} = q`. -/
theorem locPred_eq {α q : WP} (hα : NFP α) (hα0 : α.lvl = 0) (hq : SufMax α q)
    (hqα : q.val < α.val) (hmax : ∀ q', SufMax α q' → q'.val < α.val → q'.val ≤ q.val) :
    locPred α = q := by
  have h1 : 1 < α.val := lt_trans hq.2.1 hqα
  rcases locPred_spec hα hα0 h1 with ⟨p, hp, hpα, hpmax, e⟩ | ⟨hno, -⟩
  · rw [e]
    have h1' := hmax p hp hpα
    have h2' := hpmax q hq hqα
    exact eq_of_val_eq (sub0_spec hα hp.1).1 (sub0_spec hα hq.1).1 (le_antisymm h1' h2')
  · exact absurd (hno q hq) (not_le.mpr hqα)

/-- If no suffix maximum lies below `α`, then `α_{n-1} = τ = 1`. -/
theorem locPred_eq_one {α : WP} (hα : NFP α) (hα0 : α.lvl = 0) (h1 : 1 < α.val)
    (hno : ∀ q', SufMax α q' → α.val ≤ q'.val) : locPred α = TR.one := by
  rcases locPred_spec hα hα0 h1 with ⟨p, hp, hpα, -, -⟩ | ⟨-, e⟩
  · exact absurd (hno p hp) (not_le.mpr hpα)
  · exact e

end Googology.Trans.PSS.Main
