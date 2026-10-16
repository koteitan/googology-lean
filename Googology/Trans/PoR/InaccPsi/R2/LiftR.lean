import Googology.Trans.PoR.InaccPsi.R2.LiftK

/-!
# The rest of LIFT-0, and the block shape of Theorem SH, in `R₂^C`

`R2.NestK` and `R2.LiftK` prove the pair, shape, reach and gap clauses of LIFT-0 for the first block
`U_k = {u ≤ T_k : u ≤₁ T_k}` of every level.  Here:

* the remaining clauses of LIFT-0 (the project's Theorem LIFT-0, second and fourth items):
  `gap_reach` (a point below a positive member `u` of `U` that is `≤₁` a point `≥ u` is itself a positive
  member), `lh_closed` (**`[0, s_k)` is closed under `lh`**, `s_k = min U_k`), `gap_lh` (**a point strictly
  between two consecutive members of `U_k` has its reach below the upper one**), `same_way` (**a point
  below a member `u` of `U_k` is related to all of `[u, T_k]` in the same way**, for `≤₁` and for `≤₂`),
  `sK_spec` (`s_k` exists), `liftK_rest` (all of these at every level, with `C09_nestk`);
* the block shape of the project's Theorem SH ("LIFT-0 holds for every block of every level"):
  `TkA ξ k` (`T_k(ξ)`, the least top of a `k`-nest above `ξ`), `capA` (no point of `(ξ, T_k(ξ)]` reaches
  beyond `T_k(ξ)`), and, for the block `U_k(ξ) = {u ∈ (ξ, T_k(ξ)] : u ≤₁ T_k(ξ)}`: `succ_xA`,
  `pred_TA`, `noLeft_belowA`, `noRight_UA`, `U_shapeA`, `reach_UA`, `nests_belowA`, `oCA` (the copies of
  the first-block clauses, with the minimality of `T_k(ξ)` among the nests above `ξ` in place of that of
  `T_k`), `TkA_le_Tk` (`T_{m+1}(ξ) ≤ T_{j+m+1}` for `ξ < T_j`), `sh_block` (**the block of level `m+1`
  above any `ξ < T_ω`**: it exists, lies in the core, and has the LIFT-0 shape, Theorem O^C included).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## The remaining clauses of LIFT-0 -/

/-- A point `α` below a positive `u ≤₁ T` that is `≤₁` some `g ≥ u` is positive and `≤₁ T`. -/
theorem gap_reach {T u α g : Ordinal.{0}} (hu0 : 0 < u) (hu : le1 u T) (hαu : α < u) (hg : u ≤ g)
    (h1 : le1 α g) : 0 < α ∧ le1 α T := by
  have hαu1 : le1 α u := le1_of_le_of_le1 hαu.le hg h1
  refine ⟨?_, le1_trans hαu1 hu⟩
  rcases eq_or_ne α 0 with rfl | h0
  · exact absurd hαu1 (not_le1_zero hu0)
  · exact pos_iff_ne_zero.2 h0

/-- **`[0, s)` is closed under `lh`** when `s` is the least positive `u ≤₁ T`. -/
theorem lh_closed {T s : Ordinal.{0}} (hs0 : 0 < s) (hs : le1 s T)
    (hmin : ∀ u, 0 < u → u < s → ¬ le1 u T) : ∀ α < s, ∀ g, le1 α g → g < s := by
  intro α hα g h1
  by_contra hg
  push Not at hg
  obtain ⟨hα0, hαT⟩ := gap_reach hs0 hs hα hg h1
  exact hmin α hα0 hα hαT

/-- **A point strictly between two consecutive positive `u ≤₁ T` has its reach below the upper one.** -/
theorem gap_lh {T u1 u2 : Ordinal.{0}} (hu2 : le1 u2 T)
    (hcons : ∀ u, u1 < u → u < u2 → ¬ le1 u T) :
    ∀ α, u1 < α → α < u2 → ∀ g, le1 α g → g < u2 := by
  intro α h1 h2 g hg
  by_contra hge
  push Not at hge
  obtain ⟨-, hαT⟩ := gap_reach (lt_of_le_of_lt zero_le (h1.trans h2)) hu2 h2 hge hg
  exact hcons α h1 h2 hαT

section Rest

variable {m : ℕ} {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1) a b) (hT : b 0 = Tk (m + 1))
include hN hT

/-- The only `≤₂`-relation `c ≤₂ w` with `c < u ≤ w ≤ T` (`u` a positive member of `U`) is `x ≤₂ T`. -/
theorem le2_cross {u c w : Ordinal.{0}} (hu : le1 u (b 0)) (hcu : c < u) (huw : u ≤ w)
    (h2 : le2 c w) : c = a 0 ∧ w = b 0 := by
  have hc1 : le1 c (b 0) := le1_trans (le1_of_le_of_le1 hcu.le huw (le2_le1 h2)) hu
  rcases lt_trichotomy c (a 0) with hlt | heq | hgt
  · exact absurd h2 (noLeft_below hN hT hlt hc1 w (lt_of_lt_of_le hcu huw))
  · subst heq
    exact ⟨rfl, succ_x hN hT w (lt_of_lt_of_le hcu huw) h2⟩
  · exact absurd hc1 (gap_empty hN hT hgt (lt_of_lt_of_le hcu (le1_le hu)))

/-- **A point below a member `u` of `U` is related to all of `[u, T]` in the same way** (for `≤₁` and
for `≤₂`). -/
theorem same_way {u : Ordinal.{0}} (hu : le1 u (b 0)) :
    ∀ c < u, ∀ g, u ≤ g → g ≤ b 0 → ((le1 c g ↔ le1 c u) ∧ (le2 c g ↔ le2 c u)) := by
  intro c hcu g hug hgT
  refine ⟨⟨fun h => le1_of_le_of_le1 hcu.le hug h,
    fun h => le1_of_le_of_le1 (hcu.le.trans hug) hgT (le1_trans h hu)⟩, ?_⟩
  rcases eq_or_lt_of_le hug with rfl | hlt
  · exact Iff.rfl
  have hno : ∀ w, u ≤ w → w ≤ b 0 → le2 c w → u = b 0 := by
    intro w huw hwT h2
    obtain ⟨rfl, -⟩ := le2_cross hN hT hu hcu huw h2
    rcases eq_or_lt_of_le (le1_le hu) with e | hlt'
    · exact e
    · exact absurd hu (gap_empty hN hT hcu hlt')
  constructor
  · intro h2
    exact absurd (hno g hug hgT h2 ▸ hlt) (not_lt.2 hgT)
  · intro h2
    exact absurd (hno u le_rfl (le1_le hu) h2 ▸ hlt) (not_lt.2 hgT)

omit hT in
/-- **`s_k = min U_k` exists**: a least positive `s ≤₁ T` (and `s ≤ x`). -/
theorem sK_spec : ∃ s, 0 < s ∧ s ≤ a 0 ∧ le1 s (b 0) ∧ ∀ u, 0 < u → u < s → ¬ le1 u (b 0) := by
  have hx0 : 0 < a 0 := pos_iff_ne_zero.2 (hN.indec (hN.a_mem (by omega))).ne_zero
  have hx1 : le1 (a 0) (b 0) := le2_le1 (lv_x2 hN)
  set S : Set Ordinal.{0} := {u | 0 < u ∧ le1 u (b 0)} with hS
  have hne : S.Nonempty := ⟨a 0, hx0, hx1⟩
  have hmem := csInf_mem hne
  refine ⟨sInf S, hmem.1, csInf_le (OrderBot.bddBelow S) ⟨hx0, hx1⟩, hmem.2, fun u hu0 hus hu1 => ?_⟩
  exact absurd (csInf_le (OrderBot.bddBelow S) ⟨hu0, hu1⟩) (not_le.2 hus)

end Rest

/-- **The rest of LIFT-0 at level `k = m + 1`** in `R₂^C`: with `x = x_k`, `T = T_k` and
`s = s_k = min U_k`: `[0, s)` is closed under `lh`; a point strictly between two consecutive members of
`U_k` has its reach below the upper one; a point below a member `u` of `U_k` is related to all of
`[u, T]` in the same way. -/
theorem liftK_rest (m : ℕ) : ∃ x s, 0 < s ∧ s ≤ x ∧ x < Tk (m + 1) ∧ le2 x (Tk (m + 1)) ∧
    le1 s (Tk (m + 1)) ∧ (∀ u, 0 < u → u < s → ¬ le1 u (Tk (m + 1))) ∧
    (∀ α < s, ∀ g, le1 α g → g < s) ∧
    (∀ u1 u2, le1 u2 (Tk (m + 1)) → (∀ u, u1 < u → u < u2 → ¬ le1 u (Tk (m + 1))) →
      ∀ α, u1 < α → α < u2 → ∀ g, le1 α g → g < u2) ∧
    (∀ u, le1 u (Tk (m + 1)) → ∀ c < u, ∀ g, u ≤ g → g ≤ Tk (m + 1) →
      ((le1 c g ↔ le1 c u) ∧ (le2 c g ↔ le2 c u))) := by
  have h1 := Tk_lt_Om1_all (k := m + 1) (by omega)
  obtain ⟨a, b, hN, hT⟩ := Tk_attained h1
  obtain ⟨s, hs0, hsx, hs1, hmin⟩ := sK_spec hN
  rw [← hT]
  exact ⟨a 0, s, hs0, hsx, lv_xT hN, lv_x2 hN, hs1, hmin, lh_closed hs0 hs1 hmin,
    fun _ _ hu2 hcons => gap_lh hu2 hcons, fun u hu => same_way hN hT hu⟩

/-! ## The blocks above `ξ` (the shape part of Theorem SH) -/

/-- `T_k(ξ)`: the least top of a `k`-nest whose outer left end is above `ξ` (`Ω₁` if there is none). -/
noncomputable def TkA (ξ : Ordinal.{0}) (k : ℕ) : Ordinal.{0} :=
  sInf (insert Om1 {y | ∃ a b, NestSeq k a b ∧ ξ < a 0 ∧ b 0 = y})

theorem TkA_le {ξ : Ordinal.{0}} {k : ℕ} {a b : ℕ → Ordinal.{0}} (h : NestSeq k a b)
    (hξ : ξ < a 0) : TkA ξ k ≤ b 0 :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨a, b, h, hξ, rfl⟩)

theorem TkA_attained {ξ : Ordinal.{0}} {k : ℕ} (h1 : TkA ξ k < Om1) :
    ∃ a b, NestSeq k a b ∧ ξ < a 0 ∧ b 0 = TkA ξ k := by
  rcases csInf_mem (s := insert Om1 {y | ∃ a b, NestSeq k a b ∧ ξ < a 0 ∧ b 0 = y})
    ⟨Om1, Set.mem_insert _ _⟩ with h | h
  · exact absurd (h ▸ h1 : Om1 < Om1) (lt_irrefl _)
  · exact h

/-- **`T_k(0) = T_k`** for `k ≥ 1` (the outer left end of a nest is positive). -/
theorem TkA_zero {k : ℕ} (hk : 1 ≤ k) : TkA 0 k = Tk k := by
  have hset : {y | ∃ a b : ℕ → Ordinal.{0}, NestSeq k a b ∧ 0 < a 0 ∧ b 0 = y} =
      {y | ∃ a b : ℕ → Ordinal.{0}, NestSeq k a b ∧ b 0 = y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, h, -, rfl⟩; exact ⟨a, b, h, rfl⟩
    · rintro ⟨a, b, h, rfl⟩
      exact ⟨a, b, h, pos_iff_ne_zero.2 (h.indec (h.a_mem (by omega))).ne_zero, rfl⟩
  unfold TkA Tk
  rw [hset]

/-- **CAP at `T_k(ξ)`**: no point of `(ξ, T_k(ξ)]` is `≤₁` a point `> T_k(ξ)`. -/
theorem capA {k : ℕ} (hk : 1 ≤ k) {ξ : Ordinal.{0}} {a b : ℕ → Ordinal.{0}} (hN : NestSeq k a b)
    (hξ : ξ < a 0) (hT : b 0 = TkA ξ k) :
    ∀ α, ξ < α → α ≤ b 0 → ∀ g, b 0 < g → ¬ le1 α g := by
  classical
  intro α hξα hα g hg hαg
  set Rs := nestPts k a b with hRs
  set X := Rs.filter (· < α) with hX
  set Y := Rs.filter (fun z => ¬ z < α) with hY
  have hXY : X ∪ Y = Rs := Finset.filter_union_filter_not_eq _ _
  have hcl : Closed (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hXY]; exact hN.closed
  obtain ⟨Yt, hYt, -, -, f, hf, hfix, hmap⟩ := le1_cof hαg hξα X Y
    (fun z hz => (Finset.mem_filter.1 hz).2)
    (fun z hz => ⟨not_lt.1 (Finset.mem_filter.1 hz).2,
      lt_of_le_of_lt ((hN.bounds (Finset.mem_filter.1 hz).1).2) hg⟩) hcl
  have hsub : (↑(nestPts k a b) : Set Ordinal.{0}) = ↑(X ∪ Y) := by rw [hXY]
  have hfN : NestSeq k (fun i => f (a i)) (fun i => f (b i)) :=
    hN.map (hsub ▸ hf.1.2.1) (fun x hx y hy hxy => hf.2.2 x (hsub ▸ hx) y (hsub ▸ hy) hxy)
  have ha0 : a 0 ∈ Rs := hN.a_mem (by omega)
  have hξf : ξ < f (a 0) := by
    by_cases h0 : a 0 < α
    · rw [hfix _ (Finset.mem_filter.2 ⟨ha0, h0⟩)]; exact hξ
    · exact (hYt _ (hmap _ (Finset.mem_filter.2 ⟨ha0, h0⟩))).1
  have hbY : b 0 ∈ Y := Finset.mem_filter.2 ⟨hN.b_mem hk, not_lt.2 hα⟩
  have hfT : f (b 0) < α := (hYt _ (hmap (b 0) hbY)).2
  exact absurd (TkA_le hfN hξf) (not_le.2 (lt_of_lt_of_le hfT (hT ▸ hα)))

section LevelA

variable {m : ℕ} {ξ : Ordinal.{0}} {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1) a b)
  (hξ : ξ < a 0) (hT : b 0 = TkA ξ (m + 1))
include hN hξ hT

theorem lvA_cap : ∀ α, ξ < α → α ≤ b 0 → ∀ g, b 0 < g → ¬ le1 α g :=
  capA (by omega) hN hξ hT

omit hξ in
/-- From a member `u ∈ (ξ, x]` of `U(ξ)`, every `<₂`-successor `w` of `u` has `T(ξ) ≤ w`. -/
theorem lvA_up {u : Ordinal.{0}} (hu : le1 u (b 0)) (hξu : ξ < u) (hux : u ≤ a 0) :
    ∀ w, u < w → le2 u w → b 0 ≤ w := by
  intro w huw h2
  obtain ⟨a', b', hN', ha', hb'⟩ := nest_up hN.tail hu
    (fun _ => ⟨hux.trans (hN.1 0 (by omega)).1.le, (hN.1 0 (by omega)).2⟩) h2 huw
  rw [hT, ← hb']; exact TkA_le hN' (ha' ▸ hξu)

/-- **The only `<₂`-successor of `x(ξ)` is `T(ξ)`.** -/
theorem succ_xA : ∀ w, a 0 < w → le2 (a 0) w → w = b 0 := by
  intro w hw h2
  have h1 := lvA_up hN hT (le2_le1 (lv_x2 hN)) hξ le_rfl w hw h2
  rcases eq_or_lt_of_le h1 with e | hlt
  · exact e.symm
  · exact absurd (le2_le1 h2) (lvA_cap hN hξ hT _ hξ (lv_xT hN).le w hlt)

/-- **No member of `U(ξ)` lies in `(x(ξ), T(ξ))`.** -/
theorem gap_emptyA {u : Ordinal.{0}} (h1 : a 0 < u) (h2 : u < b 0) : ¬ le1 u (b 0) := by
  intro hu
  have hx2 := le2_of_le1 h1.le h2.le (lv_x2 hN) hu
  exact absurd (succ_xA hN hξ hT u h1 hx2) (ne_of_lt h2)

/-- **No member of `U(ξ)` below `x(ξ)` is a `<₂`-left end.** -/
theorem noLeft_belowA {u : Ordinal.{0}} (hξu : ξ < u) (hux : u < a 0) (hu : le1 u (b 0)) :
    ∀ w, u < w → ¬ le2 u w := by
  intro w huw h2
  have hTw := lvA_up hN hT hu hξu hux.le w huw h2
  rcases eq_or_lt_of_le hTw with e | hlt
  · subst e
    have hx1 := le2_le1 (lv_x2 hN)
    have hux2 := le2_of_le1 hux.le (lv_xT hN).le h2 hx1
    have := lvA_up hN hT hu hξu hux.le (a 0) hux hux2
    exact absurd this (not_le.2 (lv_xT hN))
  · exact lvA_cap hN hξ hT u hξu (hux.trans (lv_xT hN)).le w hlt (le2_le1 h2)

/-- **`x(ξ)` is the only `<₂`-predecessor of `T(ξ)` above `ξ`.** -/
theorem pred_TA : ∀ c, ξ < c → c < b 0 → le2 c (b 0) → c = a 0 := by
  intro c hξc hc h2
  rcases lt_trichotomy c (a 0) with hlt | heq | hgt
  · exact absurd h2 (noLeft_belowA hN hξ hT hξc hlt (le2_le1 h2) _ hc)
  · exact heq
  · exact absurd (le2_le1 h2) (gap_emptyA hN hξ hT hgt hc)

/-- **No member of `U(ξ)` other than `T(ξ)` is a `<₂`-right end of a pair above `ξ`.** -/
theorem noRight_UA {u : Ordinal.{0}} (huT : u < b 0) (hu : le1 u (b 0)) :
    ∀ c, ξ < c → c < u → ¬ le2 c u := by
  intro c hξc hcu h2
  have hc1 : le1 c (b 0) := le1_trans (le2_le1 h2) hu
  rcases lt_trichotomy c (a 0) with hlt | heq | hgt
  · exact noLeft_belowA hN hξ hT hξc hlt hc1 u hcu h2
  · subst heq
    exact absurd (succ_xA hN hξ hT u hcu h2) (ne_of_lt huT)
  · exact gap_emptyA hN hξ hT hgt (hcu.trans huT) hc1

/-- **The shape of `U(ξ)`**: for `u > ξ`, `u ≤ T(ξ) ∧ u ≤₁ T(ξ)` iff `u ∈ Pred₁(x(ξ))`, `u = x(ξ)` or
`u = T(ξ)`. -/
theorem U_shapeA (u : Ordinal.{0}) :
    (u ≤ b 0 ∧ le1 u (b 0)) ↔ ((u < a 0 ∧ le1 u (a 0)) ∨ u = a 0 ∨ u = b 0) := by
  have hx1 := le2_le1 (lv_x2 hN)
  constructor
  · rintro ⟨hu, hu1⟩
    rcases lt_trichotomy u (a 0) with hlt | heq | hgt
    · exact Or.inl ⟨hlt, le1_of_le_of_le1 hlt.le (lv_xT hN).le hu1⟩
    · exact Or.inr (Or.inl heq)
    · rcases eq_or_lt_of_le hu with he | hlt'
      · exact Or.inr (Or.inr he)
      · exact absurd hu1 (gap_emptyA hN hξ hT hgt hlt')
  · rintro (⟨hlt, hu1⟩ | rfl | rfl)
    · exact ⟨(hlt.trans (lv_xT hN)).le, le1_trans hu1 hx1⟩
    · exact ⟨(lv_xT hN).le, hx1⟩
    · exact ⟨le_rfl, le1_refl _⟩

/-- **Every member of `U(ξ)` has reach exactly `T(ξ)`.** -/
theorem reach_UA {u : Ordinal.{0}} (hξu : ξ < u) (hu : u ≤ b 0) (hu1 : le1 u (b 0)) :
    IsReach R2C u (b 0) :=
  ⟨hu1, fun g hg => not_lt.1 (fun h => lvA_cap hN hξ hT u hξu hu g h hg)⟩

omit hξ hT in
/-- **The gaps of `U(ξ)` contain `m`-nests**: below every positive member `u ≤ x(ξ)`, above any `z < u`,
lies an `m`-nest. -/
theorem nests_belowA {u : Ordinal.{0}} (hux : u ≤ a 0) (hu : le1 u (b 0)) :
    ∀ z < u, ∃ a' b', NestSeq m a' b' ∧ (0 < m → z < a' 0 ∧ b' 0 < u) := by
  classical
  intro z hz
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨a, b, ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩,
      fun h => absurd h (lt_irrefl 0)⟩
  have hI := hN.tail
  set Z := nestPts m (fun i => a (i + 1)) (fun i => b (i + 1)) with hZdef
  have hZin : ∀ y ∈ Z, u ≤ y ∧ y < b 0 := fun y hy =>
    ⟨hux.trans ((hN.1 0 (by omega)).1.le.trans (hI.bounds hy).1),
      lt_of_le_of_lt (hI.bounds hy).2 (hN.1 0 (by omega)).2⟩
  obtain ⟨Yt, hy1, -, -, f, hf, -, hmap⟩ := le1_cof hu hz ∅ Z (by simp) hZin
    (by simpa using hI.closed)
  have hsub : (↑Z : Set Ordinal.{0}) = ↑(∅ ∪ Z) := by simp
  have hfN := hI.map (hsub ▸ hf.1.2.1) (fun x hx y hy hxy => hf.2.2 x (hsub ▸ hx) y (hsub ▸ hy) hxy)
  refine ⟨_, _, hfN, fun _ => ⟨?_, ?_⟩⟩
  · exact (hy1 _ (hmap _ (hI.a_mem hm))).1
  · exact (hy1 _ (hmap _ (hI.b_mem hm))).2

/-- **Theorem O^C for the block above `ξ`** (given `[0, T(ξ)] ⊆ Core(R₂^C)`): every proper initial
segment of `Pred₁(x(ξ)) ∩ (ξ, x(ξ))` is finite. -/
theorem oCA (hcore : Set.Iic (b 0) ⊆ Core R2C) :
    ∀ s < a 0, Set.Finite {u | ξ < u ∧ u < s ∧ le1 u (a 0)} := by
  classical
  have hx1 := le2_le1 (lv_x2 hN)
  have hxT := lv_xT hN
  set S : Ordinal.{0} → Set Ordinal.{0} := fun t => {u | ξ < u ∧ u < t ∧ le1 u (a 0)} with hS
  intro s hs
  by_contra hinf
  set Tt : Set Ordinal.{0} := {t | t ≤ s ∧ (S t).Infinite} with hTt
  have hsT : s ∈ Tt := ⟨le_rfl, hinf⟩
  set s0 := sInf Tt with hs0
  have hs0T : s0 ∈ Tt := csInf_mem ⟨s, hsT⟩
  have hfin : ∀ t < s0, (S t).Finite := by
    intro t ht
    by_contra hti
    exact absurd (csInf_le (OrderBot.bddBelow Tt) ⟨ht.le.trans hs0T.1, hti⟩) (not_le.2 ht)
  obtain ⟨u0, hu0⟩ := hs0T.2.nonempty
  have hξs0 : ξ < s0 := hu0.1.trans hu0.2.1
  have hcof : ∀ z < s0, ∃ u, z < u ∧ u < s0 ∧ le1 u (a 0) := by
    intro z hz
    by_contra hno
    push Not at hno
    set z' := max z ξ with hz'
    have hz's : z' < s0 := max_lt hz hξs0
    apply hs0T.2
    refine ((hfin z' hz's).union (Set.finite_singleton z')).subset ?_
    rintro u ⟨hξu, hu, hu1⟩
    rcases lt_trichotomy u z' with h | h | h
    · exact Or.inl ⟨hξu, h, hu1⟩
    · exact Or.inr h
    · exact absurd hu1 (hno u (lt_of_le_of_lt (le_max_left _ _) h) hu)
  have hs0pos : 0 < s0 := lt_of_le_of_lt zero_le hξs0
  have hs0x : s0 < a 0 := lt_of_le_of_lt hs0T.1 hs
  have hs01 : le1 s0 (a 0) :=
    le1_of_cof_left hs0x.le hs0pos (fun z hz => by
      obtain ⟨u, h1', h2', h3'⟩ := hcof z hz
      exact ⟨u, h1', h2'.le, h3'⟩)
  have hs0I : Indec s0 := indec_of_lt1 hs01 hs0x
  have hs0T1 : le1 s0 (b 0) := le1_trans hs01 hx1
  have hcs : s0 ∈ Core R2C := hcore (show s0 ≤ b 0 from (hs0x.trans hxT).le)
  have hr : IsReach R2C s0 (b 0) := reach_UA hN hξ hT hξs0 (hs0x.trans hxT).le hs0T1
  obtain ⟨v, hv, hv2⟩ := cp hs0I hcs hr (fun γ hγ => by
    obtain ⟨u, h1', h2', h3'⟩ := hcof γ hγ
    exact ⟨u, h1', h2', le1_trans h3' hx1⟩)
  exact noLeft_belowA hN hξ hT hξs0 hs0x hs0T1 v hv hv2

end LevelA

/-- The first `m + 1` pairs of a longer nest form an `(m+1)`-nest. -/
theorem NestSeq.take {n m : ℕ} {a b : ℕ → Ordinal.{0}} (h : NestSeq n a b) (hmn : m ≤ n) :
    NestSeq m a b :=
  ⟨fun i hi => h.1 i (by omega), fun i hi => h.2 i (by omega)⟩

/-- **`T_{m+1}(ξ) ≤ T_{j+m+1}` for `ξ < T_j`** (`j ≥ 1`; with `C09_nestk`): the nest with top `T_{j+m+1}`
has its outer left end above `T_{j+m} ≥ T_j > ξ`. -/
theorem TkA_le_Tk {ξ : Ordinal.{0}} {j : ℕ} (hj : 1 ≤ j) (hξ : ξ < Tk j) (m : ℕ) :
    TkA ξ (m + 1) ≤ Tk (j + m + 1) := by
  have h1 := Tk_lt_Om1_all (k := j + m + 1) (by omega)
  obtain ⟨a, b, hN, hT⟩ := Tk_attained h1
  have hx0 : 0 < a 0 := pos_iff_ne_zero.2 (hN.indec (hN.a_mem (by omega))).ne_zero
  have hlt : Tk (j + m) < a 0 :=
    Tk_lt_mem hN hT (by omega) hx0 le_rfl (le2_le1 (lv_x2 hN))
  have hmono : Tk j ≤ Tk (j + m) := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have := Tk_strictMono.monotone (show j' ≤ j' + m by omega)
    simpa [Nat.add_right_comm] using this
  rw [← hT]
  exact TkA_le (hN.take (by omega)) (hξ.trans_le (hmono.trans hlt.le))

/-- **The block of level `m + 1` above any `ξ < T_ω`** (the shape part of Theorem SH, with
`C09_nestk`): for `ξ < T_j`, `T(ξ) = T_{m+1}(ξ)` is attained by an `(m+1)`-nest above `ξ` with outer left
end `x(ξ)`; `T(ξ) ≤ T_{j+m+1} < Ω₁` and `[0, T(ξ)] ⊆ Core(R₂^C)`; no point of `(ξ, T(ξ)]` reaches beyond
`T(ξ)`; `x(ξ)` is the only `<₂`-predecessor of `T(ξ)` above `ξ` and `T(ξ)` its only `<₂`-successor;
`U(ξ) = Pred₁(x(ξ)) ∪ {x(ξ), T(ξ)}` above `ξ`; no member of `U(ξ)` below `x(ξ)` is a `<₂`-left end;
every member of `U(ξ)` has reach `T(ξ)`; every proper initial segment of `Pred₁(x(ξ)) ∩ (ξ, x(ξ))` is
finite. -/
theorem sh_block {ξ : Ordinal.{0}} {j : ℕ} (hj : 1 ≤ j) (hξ : ξ < Tk j) (m : ℕ) :
    ∃ x, ξ < x ∧ x < TkA ξ (m + 1) ∧ le2 x (TkA ξ (m + 1)) ∧ TkA ξ (m + 1) ≤ Tk (j + m + 1) ∧
    TkA ξ (m + 1) < Om1 ∧ Set.Iic (TkA ξ (m + 1)) ⊆ Core R2C ∧
    (∀ α, ξ < α → α ≤ TkA ξ (m + 1) → ∀ g, TkA ξ (m + 1) < g → ¬ le1 α g) ∧
    (∀ c, ξ < c → c < TkA ξ (m + 1) → le2 c (TkA ξ (m + 1)) → c = x) ∧
    (∀ w, x < w → le2 x w → w = TkA ξ (m + 1)) ∧
    (∀ u, ξ < u → ((u ≤ TkA ξ (m + 1) ∧ le1 u (TkA ξ (m + 1))) ↔
      ((u < x ∧ le1 u x) ∨ u = x ∨ u = TkA ξ (m + 1)))) ∧
    (∀ u, ξ < u → u < x → le1 u x → ∀ w, u < w → ¬ le2 u w) ∧
    (∀ u, ξ < u → u ≤ TkA ξ (m + 1) → le1 u (TkA ξ (m + 1)) → IsReach R2C u (TkA ξ (m + 1))) ∧
    (∀ s < x, Set.Finite {u | ξ < u ∧ u < s ∧ le1 u x}) := by
  have hle := TkA_le_Tk hj hξ m
  have h1 : TkA ξ (m + 1) < Om1 := lt_of_le_of_lt hle (Tk_lt_Om1_all (by omega))
  obtain ⟨a, b, hN, hξa, hT⟩ := TkA_attained h1
  have hcore : Set.Iic (b 0) ⊆ Core R2C := by
    obtain ⟨a', b', hN', hT'⟩ := Tk_attained (Tk_lt_Om1_all (k := j + m + 1) (by omega))
    have hc := Tk_core (by omega) hN' hT'
    intro z hz
    exact hc (show z ≤ Tk (j + m + 1) from (Set.mem_Iic.1 hz).trans (hT ▸ hle))
  have hx1 := le2_le1 (lv_x2 hN)
  rw [← hT] at h1 hle ⊢
  exact ⟨a 0, hξa, lv_xT hN, lv_x2 hN, hle, h1, hcore, lvA_cap hN hξa hT, pred_TA hN hξa hT,
    succ_xA hN hξa hT, fun u _ => U_shapeA hN hξa hT u,
    fun u hξu hux hu1 => noLeft_belowA hN hξa hT hξu hux (le1_trans hu1 hx1),
    fun u hξu hu hu1 => reach_UA hN hξa hT hξu hu hu1, oCA hN hξa hT hcore⟩

end Googology.Trans.PoR.InaccPsi.R2
