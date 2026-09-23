import Googology.Notation.ExBuchholz.System

/-!
# The fundamental sequence is cofinal

`fs_lt` says `X[z] < X`.  This file proves the other half of calling `[ ]` a
fundamental sequence: nothing standard below `X` is above all of its members.

```
dom X = 1   ⟹  Y < X → Y ≤ X[0]
dom X = ω   ⟹  Y < X → ∃ n, Y < X[n]
```

for standard `X` and `Y`, with no bound on the subscripts.  The one-row
version is `Trans/BMS/Cofinal.lean`; it never meets Buchholz's case 4.

## Case 4

There `X = ψ_A(B)`, `dom B = ψ_Z(0)` is not below `X`, and
`X[n] = ψ_A(B[W_n])` for the tower `W₀ = ψ_{Z₀}(0)`,
`W_{i+1} = ψ_{Z₀}(B[W_i])`, `Z₀ = Z[0]`.  A standard `ψ_A(e)` below `X` has
`e < B` and `G_A(e) < e`.  The step that makes it work is
`lt_fs_psi_of_G`:

```
d < V,  G_{Z₀}(d) < β   ⟹   d < V[ψ_{Z₀}(β)]
```

for `V` with a term-indexed domain.  It is an induction on `V`, one case per
branch of `dom`, and every case is short.  With `β = B[W_n]` its conclusion
is `d < B[W_{n+1}]`.  So `exists_lt_fs_tower` bounds each member of
`G_{Z₀}(d)` by some rung, by induction on size, takes the largest rung, and
climbs one more.  `A ≤ Z₀` makes `G_{Z₀}(e) ⊆ G_A(e)`, so `e` qualifies.
-/

namespace Googology.Notation.ExBuchholz.Term

/-! ### `G` facts -/

theorem G_mem_cons_tail {u p q r x : Term} (hx : x ∈ G u r) : x ∈ G u (cons p q r) := by
  rw [G_cons]; exact List.mem_append_right _ hx

theorem G_mem_cons_arg {u p q r : Term} (h : u ≤ p) : q ∈ G u (cons p q r) := by
  rw [G_cons, if_pos h]
  exact List.mem_append_left _ (List.mem_cons_self ..)

theorem G_mem_cons_sub {u p q r x : Term} (h : u ≤ p) (hx : x ∈ G u p) :
    x ∈ G u (cons p q r) := by
  rw [G_cons, if_pos h]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx))

theorem G_mem_cons_argG {u p q r x : Term} (h : u ≤ p) (hx : x ∈ G u q) :
    x ∈ G u (cons p q r) := by
  rw [G_cons, if_pos h]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))

/-- `G` is closed under itself: what it sees in a member, it sees already. -/
theorem G_mem_trans (u : Term) : ∀ d x : Term, x ∈ G u d → ∀ y ∈ G u x, y ∈ G u d := by
  intro d
  induction d with
  | nil => intro x hx; cases hx
  | cons p q r ihp ihq ihr =>
    intro x hx y hy
    rw [G_cons] at hx
    rcases List.mem_append.mp hx with hx | hx
    · split at hx
      · next hup =>
        rcases List.mem_cons.mp hx with rfl | hx
        · exact G_mem_cons_argG hup hy
        rcases List.mem_append.mp hx with hx | hx
        · exact G_mem_cons_sub hup (ihp x hx y hy)
        · exact G_mem_cons_argG hup (ihq x hx y hy)
      · cases hx
    · exact G_mem_cons_tail (ihr x hx y hy)

/-! ### The shapes of `dom` and `fs` at a collapse -/

theorem dom_psi_nil_of_one {a : Term} (g2 : dom a = t1) :
    dom (cons a nil nil) = cons a nil nil := by
  have g1 : dom a ≠ nil := by rw [g2]; exact fun h => Term.noConfusion h
  rw [dom]; simp_all

theorem fs_psi_nil_of_one {a Y : Term} (g2 : dom a = t1) :
    fs (cons a nil nil) Y = Y := by
  have g1 : dom a ≠ nil := by rw [g2]; exact fun h => Term.noConfusion h
  rw [fs]; simp_all

theorem dom_psi_nil_of_lim {a : Term} (g1 : dom a ≠ nil) (g2 : dom a ≠ t1) :
    dom (cons a nil nil) = dom a := by rw [dom]; simp_all

theorem fs_psi_nil_of_lim {a Y : Term} (g1 : dom a ≠ nil) (g2 : dom a ≠ t1) :
    fs (cons a nil nil) Y = psi (fs a Y) nil := by rw [fs]; simp_all

theorem dom_psi_of_one {a b : Term} (e2 : dom b = t1) : dom (cons a b nil) = tw := by
  have e1 : dom b ≠ nil := by rw [e2]; exact fun h => Term.noConfusion h
  rw [dom]; simp_all

theorem dom_psi_of_tw {a b : Term} (e3 : dom b = tw) : dom (cons a b nil) = tw := by
  have e1 : dom b ≠ nil := by rw [e3]; exact fun h => Term.noConfusion h
  rw [dom]; simp_all

theorem fs_psi_of_tw {a b Y : Term} (e3 : dom b = tw) : fs (cons a b nil) Y = psi a (fs b Y) := by
  have e1 : dom b ≠ nil := by rw [e3]; exact fun h => Term.noConfusion h
  have e2 : dom b ≠ t1 := by rw [e3]; decide
  rw [fs]; simp_all

theorem dom_psi_of_lt {a b : Term} (e1 : dom b ≠ nil) (e2 : dom b ≠ t1) (e3 : dom b ≠ tw)
    (e4 : dom b < cons a b nil) : dom (cons a b nil) = dom b := by rw [dom]; simp_all

theorem fs_psi_of_lt {a b Y : Term} (e1 : dom b ≠ nil) (e2 : dom b ≠ t1) (e3 : dom b ≠ tw)
    (e4 : dom b < cons a b nil) : fs (cons a b nil) Y = psi a (fs b Y) := by
  rw [fs]; simp_all

theorem dom_psi_of_case4 {a b : Term} (e1 : dom b ≠ nil) (e2 : dom b ≠ t1) (e3 : dom b ≠ tw)
    (e4 : ¬ dom b < cons a b nil) : dom (cons a b nil) = tw := by rw [dom]; simp_all

theorem numVal_of_numeral : ∀ n : Nat, numVal (numeral n) = n
  | 0 => rfl
  | k + 1 => by
    show numVal (cons nil nil (numeral k)) = k + 1
    rw [numVal, numVal_of_numeral k]

theorem fs_psi_of_one_numeral {a b : Term} (e2 : dom b = t1) (n : Nat) :
    fs (cons a b nil) (numeral n) = repeatPrin a (fs b nil) n := by
  have e1 : dom b ≠ nil := by rw [e2]; exact fun h => Term.noConfusion h
  have hn := isNum_numeral n
  have hv := numVal_of_numeral n
  rw [fs]; simp_all

/-! ### The bound behind case 4 -/

/-- **What `G` at the level `Z₀` does not see, the next rung of the tower
catches.**  For `V` with a term-indexed domain `ψ_Z(0)` and `Z₀ = Z[0]`: a
standard `d < V` whose `G_{Z₀}` is below `β` is below `V[ψ_{Z₀}(β)]`. -/
theorem lt_fs_psi_of_G : ∀ V : Term, OT V → dom V ≠ nil → dom V ≠ t1 → dom V ≠ tw →
    ∀ β d : Term, OT d → d < V → (∀ x ∈ G (fs (subOf (dom V)) nil) d, x < β) →
    d < fs V (psi (fs (subOf (dom V)) nil) β) := by
  intro V
  induction V with
  | nil => intro _ h0; exact absurd rfl h0
  | cons a b t iha ihb iht =>
    intro hV h0 h1 hw β d hd hdV hG
    cases t with
    | cons c' d' u =>
      have hdom : dom (cons a b (cons c' d' u)) = dom (cons c' d' u) := rfl
      rw [hdom] at h0 h1 hw hG ⊢
      show d < fs (cons a b (cons c' d' u)) _
      rw [fs]
      cases d with
      | nil => exact nil_lt_cons _ _ _
      | cons p q r =>
        rcases cons_lt_cons_iff.mp hdV with h | ⟨h, hr⟩
        · exact cons_lt_cons_iff.mpr (Or.inl h)
        · injection h with e1 e2 _
          subst e1; subst e2
          refine cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ?_⟩)
          exact iht (OT_tail hV) h0 h1 hw β r (OT_tail hd) hr
            (fun x hx => hG x (G_mem_cons_tail hx))
    | nil =>
      cases d with
      | nil =>
        refine lt_of_le_of_ne (nil_le _) (fun h => fs_ne_nil h0 h1 hw ?_ h.symm)
        exact fun h' => Term.noConfusion h'
      | cons p q r =>
        have hpq : psi p q < psi a b := cons_lt_psi_iff.mp hdV
        by_cases e1 : dom b = nil
        · have hb : b = nil := dom_eq_nil_iff.mp e1
          subst hb
          have hpa : p < a := by
            rcases psi_lt_psi_iff.mp hpq with h | ⟨_, h⟩
            · exact h
            · exact absurd h (not_lt_nil _)
          by_cases g1 : dom a = nil
          · have ha : a = nil := dom_eq_nil_iff.mp g1
            subst ha
            exact (h1 (by decide)).elim
          · by_cases g2 : dom a = t1
            · have hdV' := dom_psi_nil_of_one g2
              rw [hdV'] at hG ⊢
              rw [fs_psi_nil_of_one g2]
              simp only [subOf] at hG ⊢
              have hle : p ≤ fs a nil := le_pred_of_lt (OT_fst hV) g2 hpa
              refine cons_lt_psi_iff.mpr ?_
              rcases le_iff_lt_or_eq.mp hle with h | h
              · exact psi_lt_psi_iff.mpr (Or.inl h)
              · refine psi_lt_psi_iff.mpr (Or.inr ⟨h, ?_⟩)
                subst h
                exact hG q (G_mem_cons_arg (le_refl _))
            · have hdV' := dom_psi_nil_of_lim g1 g2
              rw [hdV'] at h0 h1 hw hG ⊢
              rw [fs_psi_nil_of_lim g1 g2]
              refine cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl ?_))
              refine iha (OT_fst hV) h0 h1 hw β p (OT_fst hd) hpa ?_
              intro x hx
              by_cases hz : fs (subOf (dom a)) nil ≤ p
              · exact hG x (G_mem_cons_sub hz hx)
              · rw [G_eq_nil_of_le p _ (OT_fst hd) (le_of_lt (lt_of_not_le hz))] at hx
                cases hx
        · have hbne : b ≠ nil := fun h => e1 (by rw [h]; rfl)
          by_cases e2 : dom b = t1
          · exact absurd (dom_psi_of_one e2) hw
          · by_cases e3 : dom b = tw
            · exact absurd (dom_psi_of_tw e3) hw
            · by_cases e4 : dom b < cons a b nil
              · have hdV' := dom_psi_of_lt e1 e2 e3 e4
                rw [hdV'] at hG ⊢
                rw [fs_psi_of_lt e1 e2 e3 e4]
                refine cons_lt_psi_iff.mpr ?_
                rcases psi_lt_psi_iff.mp hpq with h | ⟨h, hqb⟩
                · exact psi_lt_psi_iff.mpr (Or.inl h)
                · subst h
                  refine psi_lt_psi_iff.mpr (Or.inr ⟨rfl, ?_⟩)
                  -- `Z₀ < Z ≤ p`, so `G_{Z₀}` reaches inside the argument.
                  obtain ⟨Z, hZ⟩ : ∃ Z, dom b = cons Z nil nil := by
                    rcases dom_shape b with h | h | h
                    · exact absurd h e1
                    · exact absurd h e3
                    · exact h
                  have hZ0 : fs (subOf (dom b)) nil < subOf (dom b) := subOf_fs_lt e1 e2 e3
                  have hZp : subOf (dom b) ≤ p := by
                    have e4' := e4
                    rw [hZ] at e4'
                    rw [hZ]
                    rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp e4') with h | ⟨h, _⟩
                    · exact le_of_lt h
                    · exact h ▸ le_refl _
                  have hup : fs (subOf (dom b)) nil ≤ p := le_of_lt (lt_of_lt_of_le' hZ0 hZp)
                  exact ihb (OT_snd hV) e1 e2 e3 β q (OT_snd hd) hqb
                    (fun x hx => hG x (G_mem_cons_argG hup hx))
              · exact absurd (dom_psi_of_case4 e1 e2 e3 e4) hw

/-! ### The tower is cofinal -/

theorem tower_val_mono {Z₀ B : Term} (e1 : dom B ≠ nil) (e2 : dom B ≠ t1) (e3 : dom B ≠ tw)
    {i j : Nat} (h : i ≤ j) : fs B (tower Z₀ B i) ≤ fs B (tower Z₀ B j) := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (le_of_lt (tower_val_lt e1 e2 e3 _))

/-- A finite list, each member below some value of a monotone sequence, is
below one value. -/
theorem exists_bound_list {f : Nat → Term} (hf : ∀ {i j : Nat}, i ≤ j → f i ≤ f j) :
    ∀ l : List Term, (∀ x ∈ l, ∃ n, x < f n) → ∃ N, ∀ x ∈ l, x < f N := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, fun x hx => absurd hx List.not_mem_nil⟩
  | cons y l ih =>
    intro h
    obtain ⟨n, hn⟩ := h y List.mem_cons_self
    obtain ⟨N, hN⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨max n N, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact lt_of_lt_of_le' hn (hf (le_max_left n N))
    · exact lt_of_lt_of_le' (hN x hx) (hf (le_max_right n N))

/-- **The tower of case 4 climbs past everything `G_{Z₀}` keeps below `B`.** -/
theorem exists_lt_fs_tower {B : Term} (hB : OT B) (e1 : dom B ≠ nil) (e2 : dom B ≠ t1)
    (e3 : dom B ≠ tw) : ∀ d : Term, OT d → d < B →
    (∀ x ∈ G (fs (subOf (dom B)) nil) d, x < B) →
    ∃ n, d < fs B (tower (fs (subOf (dom B)) nil) B n) := by
  intro d
  induction hs : size d using Nat.strong_induction_on generalizing d with
  | _ s ih =>
    intro hd hdB hG
    have hbound : ∀ x ∈ G (fs (subOf (dom B)) nil) d,
        ∃ n, x < fs B (tower (fs (subOf (dom B)) nil) B n) := by
      intro x hx
      exact ih (size x) (hs ▸ size_lt_of_mem_G _ d x hx) x rfl
        (OT_of_mem_G _ d hd x hx) (hG x hx)
        (fun y hy => hG y (G_mem_trans _ d x hx y hy))
    obtain ⟨N, hN⟩ := exists_bound_list (tower_val_mono e1 e2 e3) _ hbound
    exact ⟨N + 1, lt_fs_psi_of_G B hB e1 e2 e3 _ d hd hdB hN⟩

/-! ### Cofinality at an `ω`-limit -/

/-- A standard sum whose head is at most `ψ_A(B)` is below some multiple of
it. -/
theorem exists_lt_repeatPrin {A B : Term} : ∀ Y : Term, OT Y → HeadLe (psi A B) Y →
    ∃ k, Y < repeatPrin A B k := by
  intro Y
  induction Y with
  | nil => intro _ _; exact ⟨1, nil_lt_cons _ _ _⟩
  | cons p q r _ _ ihr =>
    intro hY hle
    rcases le_iff_lt_or_eq.mp (show psi p q ≤ psi A B from hle) with h | h
    · exact ⟨1, cons_lt_cons_iff.mpr (Or.inl h)⟩
    · injection h with e1 e2 _
      subst e1; subst e2
      obtain ⟨k, hk⟩ := ihr (OT_tail hY) (OT_headLe_tail hY)
      exact ⟨k + 1, cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hk⟩)⟩

/-- **At an `ω`-limit the fundamental sequence is cofinal**: anything standard
below a standard `X` with `dom X = ω` is below some `X[n]`. -/
theorem exists_lt_fs_numeral : ∀ X : Term, OT X → dom X = tw →
    ∀ Y : Term, OT Y → Y < X → ∃ n, Y < fs X (numeral n) := by
  intro X
  induction X with
  | nil => intro _ h; exact absurd h (by decide)
  | cons a b t iha ihb iht =>
    intro hX hdX Y hY hYX
    cases t with
    | cons c' d' u =>
      have hdom : dom (cons a b (cons c' d' u)) = dom (cons c' d' u) := rfl
      rw [hdom] at hdX
      have hfs : ∀ n, fs (cons a b (cons c' d' u)) (numeral n)
          = cons a b (fs (cons c' d' u) (numeral n)) := fun n => by rw [fs]
      cases Y with
      | nil => exact ⟨0, by rw [hfs]; exact nil_lt_cons _ _ _⟩
      | cons p q r =>
        rcases cons_lt_cons_iff.mp hYX with h | ⟨h, hr⟩
        · exact ⟨0, by rw [hfs]; exact cons_lt_cons_iff.mpr (Or.inl h)⟩
        · injection h with e1 e2 _
          subst e1; subst e2
          obtain ⟨n, hn⟩ := iht (OT_tail hX) hdX r (OT_tail hY) hr
          exact ⟨n, by rw [hfs]; exact cons_lt_cons_iff.mpr (Or.inr ⟨rfl, hn⟩)⟩
    | nil =>
      by_cases e1 : dom b = nil
      · have hb : b = nil := dom_eq_nil_iff.mp e1
        subst hb
        by_cases g1 : dom a = nil
        · have ha : a = nil := dom_eq_nil_iff.mp g1
          subst ha
          exact absurd hdX (by decide)
        · by_cases g2 : dom a = t1
          · rw [dom_psi_nil_of_one g2] at hdX
            injection hdX with _ h2 _
            exact absurd h2 (fun h => Term.noConfusion h)
          · rw [dom_psi_nil_of_lim g1 g2] at hdX
            simp only [fs_psi_nil_of_lim g1 g2]
            cases Y with
            | nil => exact ⟨0, nil_lt_cons _ _ _⟩
            | cons p q r =>
              have hpa : p < a := by
                rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hYX) with h | ⟨_, h⟩
                · exact h
                · exact absurd h (not_lt_nil _)
              obtain ⟨n, hn⟩ := iha (OT_fst hX) hdX p (OT_fst hY) hpa
              exact ⟨n, cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl hn))⟩
      · by_cases e2 : dom b = t1
        · simp only [fs_psi_of_one_numeral e2]
          refine exists_lt_repeatPrin Y hY ?_
          cases Y with
          | nil => trivial
          | cons p q r =>
            show psi p q ≤ psi a (fs b nil)
            rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hYX) with h | ⟨h, hqb⟩
            · exact le_of_lt (psi_lt_psi_iff.mpr (Or.inl h))
            · subst h
              rcases le_iff_lt_or_eq.mp (le_pred_of_lt (OT_snd hX) e2 hqb) with h | h
              · exact le_of_lt (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, h⟩))
              · rw [h]; exact le_refl _
        · by_cases e3 : dom b = tw
          · simp only [fs_psi_of_tw e3]
            cases Y with
            | nil => exact ⟨0, nil_lt_cons _ _ _⟩
            | cons p q r =>
              rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hYX) with h | ⟨h, hqb⟩
              · exact ⟨0, cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl h))⟩
              · subst h
                obtain ⟨n, hn⟩ := ihb (OT_snd hX) e3 q (OT_snd hY) hqb
                exact ⟨n, cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hn⟩))⟩
          · by_cases e4 : dom b < cons a b nil
            · rw [dom_psi_of_lt e1 e2 e3 e4] at hdX
              exact absurd hdX e3
            · simp only [fs_numeral e1 e2 e3 e4]
              cases Y with
              | nil => exact ⟨0, nil_lt_cons _ _ _⟩
              | cons p q r =>
                rcases psi_lt_psi_iff.mp (cons_lt_psi_iff.mp hYX) with h | ⟨h, hqb⟩
                · exact ⟨0, cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inl h))⟩
                · subst h
                  -- `p < Z`, and `Z` is a successor, so `p ≤ Z₀`.
                  obtain ⟨Z, hZ⟩ : ∃ Z, dom b = cons Z nil nil := by
                    rcases dom_shape b with h | h | h
                    · exact absurd h e1
                    · exact absurd h e3
                    · exact h
                  have hsub : subOf (dom b) = Z := by rw [hZ]; rfl
                  have hOTZ : OT Z := hsub ▸ OT_subOf_dom (OT_snd hX) e1 e3
                  have hdZ : dom Z = t1 := dom_sub_dom_eq_one b Z hZ e2
                  have hpZ : p < Z := by
                    rcases lt_trichotomy (psi Z nil) (psi p b) with h | h | h
                    · exact absurd (hZ ▸ h) e4
                    · injection h with _ h2 _
                      exact absurd h2.symm (fun h' => e1 (by rw [h']; rfl))
                    · rcases psi_lt_psi_iff.mp h with h' | ⟨_, h'⟩
                      · exact h'
                      · exact absurd h' (not_lt_nil _)
                  have hup : p ≤ fs (subOf (dom b)) nil := by
                    rw [hsub]; exact le_pred_of_lt hOTZ hdZ hpZ
                  have hG : ∀ x ∈ G (fs (subOf (dom b)) nil) q, x < b := fun x hx =>
                    lt_trans (OT_G_lt (OT_head hY) x (G_subset_of_le hup q x hx)) hqb
                  obtain ⟨n, hn⟩ := exists_lt_fs_tower (OT_snd hX) e1 e2 e3 q (OT_snd hY) hqb hG
                  exact ⟨n, cons_lt_psi_iff.mpr (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, hn⟩))⟩

/-! ### Cofinality of one expansion step -/

/-- **Anything standard below a countable standard form is at most one of its
expansions.**  At a successor that is the predecessor, at an `ω`-limit a
member of the fundamental sequence. -/
theorem exists_le_fs_idx {X : Term} (hX : OT X) (hc : X < tW) (hne : X ≠ nil)
    {Y : Term} (hY : OT Y) (hYX : Y < X) : ∃ n, Y ≤ fs X (idx X n) := by
  rcases dom_eq_one_or_tw X hX hc hne with h | h
  · exact ⟨0, by rw [idx, if_pos h]; exact le_pred_of_lt hX h hYX⟩
  · have hne' : dom X ≠ t1 := by rw [h]; decide
    obtain ⟨n, hn⟩ := exists_lt_fs_numeral X hX h Y hY hYX
    exact ⟨n, by rw [idx, if_neg hne']; exact le_of_lt hn⟩

/-- The same, stated on the states of `exbOT`. -/
theorem exbOT_exists_le_step (A : exbOT.State) (hne : A.1 ≠ nil) {Y : Term} (hY : OT Y)
    (hYA : Y < A.1) : ∃ n, Y ≤ (exbOT.step A n).1 :=
  exists_le_fs_idx A.2.1 A.2.2 hne hY hYA

end Googology.Notation.ExBuchholz.Term
