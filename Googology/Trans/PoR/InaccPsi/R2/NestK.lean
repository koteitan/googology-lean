import Googology.Trans.PoR.InaccPsi.R2.NuRst

/-!
# `k`-nests in `R₂^C`: the first block of every level (LIFT-0) and Theorem O^C at every level

A **`k`-nest** is `a₀ < a₁ < ⋯ < a_{k-1} < b_{k-1} < ⋯ < b₀` with `aᵢ <₂ bᵢ` (`NestSeq k a b`, defined in
`R2.NestDef`); its top is
`b₀`, its outer left end `a₀`.  `T_k` (`Tk k`) is the least top of a `k`-nest (`Ω₁` if there is none).
Fix a `(m+1)`-nest `(a, b)` with top `T = T_{m+1}` and outer left end `x = a₀`, and let
`U = {u ≤ T : u ≤₁ T}`.  Everything below holds for a given nest, with no new axiom.

* `nest_up` (**NEST-UP**): if `u ≤₁ T`, an `m`-nest lies in `[u, T)`, and `u <₂ w`, then `(u, w)` is
  the outer pair of an `(m+1)`-nest.  The `m`-nest is copied below `u` ([C09] Def 5.3 clause 1 of
  `≤₁`, `le1_cof`), so it is covered cofinally below `u`, and clause 2 of `u ≤₂ w` puts a covered copy
  into `(u, w)`;
* `nest_core_k`, `Tk_lt_Om1` (`T_k < Ω₁`: a copy of a `k`-nest is isominimal, [C09] Thm 14.10, and the
  core is countable, [C09] Cor 15.15), `cap_Tk` (**CAP at `T_k`**: no `α ≤ T_k` is `≤₁` a point
  `> T_k`), `Tk_core` (`[0, T_k] ⊆ Core(R₂^C)`, [C09] Thm 14.14);
* the first block of level `m+1` (the project's Theorem LIFT-0): `succ_x` (the only `<₂`-successor of
  `x` is `T`), `noLeft_below` (no member of `U` below `x` is a `<₂`-left end), `gap_empty` (no member of
  `U` in `(x, T)`), `pred_T` (`x` is the only `<₂`-predecessor of `T`), `noRight_U` (no member of `U`
  other than `T` is a `<₂`-right end), `U_shape` (`U = Pred₁(x) ∪ {x, T}`), `reach_U` (every member of
  `U` has reach `T`), `nests_below` (below every positive member of `U`, above any smaller point, lies
  an `m`-nest: the gaps of `U` contain `m`-nests), `Tk_lt_mem` (`T_m < s` for every positive
  `s ∈ U`, in particular `T_m < s_{m+1}`);
* `oC` (**Theorem O^C at level `m+1`**: every proper initial segment of `Pred₁(x)` is finite; with
  `pred1_cof`, `Pred₁(x)` has order type `ω`).  Proof as for level 2: otherwise the `ω`-th member `s`
  is `≤₁ x`, in the core, has reach `T` and cofinal `≤₁`-predecessors, so Theorem CP makes it a
  `<₂`-left end, against `noLeft_below`;
* `Tk_lt_succ` (`T_{m+1} < T_{m+2}` when a `(m+2)`-nest exists), `Tk_two` (`T₂ = T_C = ν_C`).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## `k`-nests -/

/-- The points of a `k`-nest. -/
noncomputable def nestPts (k : ℕ) (a b : ℕ → Ordinal.{0}) : Finset Ordinal.{0} :=
  (Finset.range k).image a ∪ (Finset.range k).image b

/-- `x` in front of a sequence. -/
def consS (x : Ordinal.{0}) (a : ℕ → Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => x
  | i + 1 => a i

namespace NestSeq

theorem mem_iff {k : ℕ} {a b : ℕ → Ordinal.{0}} {z : Ordinal.{0}} :
    z ∈ nestPts k a b ↔ (∃ i, i < k ∧ a i = z) ∨ ∃ i, i < k ∧ b i = z := by
  simp [nestPts]

theorem a_mem {k : ℕ} {a b : ℕ → Ordinal.{0}} (_h : NestSeq k a b) {i : ℕ} (hi : i < k) :
    a i ∈ nestPts k a b := mem_iff.2 (Or.inl ⟨i, hi, rfl⟩)

theorem b_mem {k : ℕ} {a b : ℕ → Ordinal.{0}} (_h : NestSeq k a b) {i : ℕ} (hi : i < k) :
    b i ∈ nestPts k a b := mem_iff.2 (Or.inr ⟨i, hi, rfl⟩)

variable {k : ℕ} {a b : ℕ → Ordinal.{0}} (h : NestSeq k a b)
include h

theorem a_mono : ∀ d i, i + d + 1 < k → a i < a (i + d + 1)
  | 0, i, hi => (h.1 i hi).1
  | d + 1, i, hi => (a_mono d i (by omega)).trans (h.1 (i + d + 1) (by omega)).1

theorem b_anti : ∀ d i, i + d + 1 < k → b (i + d + 1) < b i
  | 0, i, hi => (h.1 i hi).2
  | d + 1, i, hi => (h.1 (i + d + 1) (by omega)).2.trans (b_anti d i (by omega))

theorem a_le {i j : ℕ} (hij : i ≤ j) (hj : j < k) : a i ≤ a j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
    exact (a_mono h d i hj).le

theorem b_le {i j : ℕ} (hij : i ≤ j) (hj : j < k) : b j ≤ b i := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
    exact (b_anti h d i hj).le

theorem a_lt_b {i j : ℕ} (hi : i < k) (hj : j < k) : a i < b j :=
  lt_of_le_of_lt (h.a_le (show i ≤ k - 1 by omega) (by omega))
    (lt_of_lt_of_le (h.2 (k - 1) (by omega)).1 (h.b_le (show j ≤ k - 1 by omega) (by omega)))

theorem bounds {z : Ordinal.{0}} (hz : z ∈ nestPts k a b) : a 0 ≤ z ∧ z ≤ b 0 := by
  rcases mem_iff.1 hz with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact ⟨h.a_le (Nat.zero_le i) hi, (h.a_lt_b hi (by omega)).le⟩
  · exact ⟨(h.a_lt_b (by omega) hi).le, h.b_le (Nat.zero_le i) hi⟩

theorem indec {z : Ordinal.{0}} (hz : z ∈ nestPts k a b) : Indec z := by
  rcases mem_iff.1 hz with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
  · exact indec_of_lt1 (le2_le1 (h.2 i hi).2) (h.2 i hi).1
  · exact (indec_of_lt2_right (h.2 i hi).2 (h.2 i hi).1).1

theorem closed : Closed (↑(nestPts k a b) : Set Ordinal.{0}) :=
  closed_of_indec fun _ hz => h.indec (Finset.mem_coe.1 hz)



/-- The image of a nest under a map that keeps `<` and `≤₂` on its points. -/
theorem map {f : Ordinal.{0} → Ordinal.{0}}
    (hmono : StrictMonoOn f (↑(nestPts k a b) : Set Ordinal.{0}))
    (h2 : ∀ x ∈ (↑(nestPts k a b) : Set Ordinal.{0}), ∀ y ∈ (↑(nestPts k a b) : Set Ordinal.{0}),
      le2 x y → le2 (f x) (f y)) :
    NestSeq k (fun i => f (a i)) (fun i => f (b i)) := by
  refine ⟨fun i hi => ⟨?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩
  · exact hmono (h.a_mem (by omega)) (h.a_mem hi) (h.1 i hi).1
  · exact hmono (h.b_mem hi) (h.b_mem (by omega)) (h.1 i hi).2
  · exact hmono (h.a_mem hi) (h.b_mem hi) (h.2 i hi).1
  · exact h2 _ (h.a_mem hi) _ (h.b_mem hi) (h.2 i hi).2

end NestSeq

/-- The inner nest. -/
theorem NestSeq.tail {m : ℕ} {a b : ℕ → Ordinal.{0}} (h : NestSeq (m + 1) a b) :
    NestSeq m (fun i => a (i + 1)) (fun i => b (i + 1)) :=
  ⟨fun i hi => h.1 (i + 1) (by omega), fun i hi => h.2 (i + 1) (by omega)⟩

/-- A pair around a nest. -/
theorem NestSeq.cons {m : ℕ} {a b : ℕ → Ordinal.{0}} (h : NestSeq m a b) {x y : Ordinal.{0}}
    (hin : 0 < m → x < a 0 ∧ b 0 < y) (hxy : x < y) (h2 : le2 x y) :
    NestSeq (m + 1) (consS x a) (consS y b) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases i with _ | i
    · exact hin (by omega)
    · exact h.1 i (by omega)
  · rcases i with _ | i
    · exact ⟨hxy, h2⟩
    · exact h.2 i (by omega)

/-! ## NEST-UP -/

/-- **NEST-UP**: if `u ≤₁ T`, an `m`-nest lies in `[u, T)` and `u <₂ w`, then `(u, w)` is the outer pair
of an `(m+1)`-nest. -/
theorem nest_up {m : ℕ} {a b : ℕ → Ordinal.{0}} (hN : NestSeq m a b) {u T w : Ordinal.{0}}
    (hu : le1 u T) (hin : 0 < m → u ≤ a 0 ∧ b 0 < T) (h2 : le2 u w) (huw : u < w) :
    ∃ a' b', NestSeq (m + 1) a' b' ∧ a' 0 = u ∧ b' 0 = w := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨consS u a, consS w b, hN.cons (fun h => absurd h (lt_irrefl 0)) huw h2, rfl, rfl⟩
  obtain ⟨hua, hbT⟩ := hin hm
  set Z := nestPts m a b with hZdef
  have hZ : Closed (↑Z : Set Ordinal.{0}) := hN.closed
  have hZin : ∀ y ∈ Z, u ≤ y ∧ y < T := fun y hy =>
    ⟨hua.trans (hN.bounds hy).1, lt_of_le_of_lt (hN.bounds hy).2 hbT⟩
  have hcof : CofCov R2C ∅ Z R2C u := by
    intro c' hc'
    obtain ⟨Yt, hy1, -, h3, f, hf, -, -⟩ := le1_cof hu hc' ∅ Z (by simp) hZin
      (by simpa using hZ)
    exact ⟨Yt, hy1, h3, f, by simpa using hf⟩
  obtain ⟨_, -, H2⟩ := le2_iff.1 h2
  obtain ⟨Y, hY, -, g, hg⟩ := H2 ∅ (by simp) Z R2C hZ hcof u huw
  have hgN : NestSeq m (fun i => g (a i)) (fun i => g (b i)) :=
    hN.map hg.1.2.1 (fun x hx y hy hxy => hg.2.2 x hx y hy hxy)
  have hmap : ∀ z ∈ Z, g z ∈ Y := by
    intro z hz
    have := hg.1.1.mapsTo (Finset.mem_coe.2 hz)
    simpa using this
  have ha0 := hY _ (hmap _ (hN.a_mem hm))
  have hb0 := hY _ (hmap _ (hN.b_mem hm))
  exact ⟨consS u (fun i => g (a i)), consS w (fun i => g (b i)),
    hgN.cons (fun _ => ⟨ha0.1, hb0.2⟩) huw h2, rfl, rfl⟩

/-! ## `T_k`, its countability, CAP and the core -/

/-- `T_k`: the least top of a `k`-nest (`Ω₁` if there is none). -/
noncomputable def Tk (k : ℕ) : Ordinal.{0} :=
  sInf (insert Om1 {y | ∃ a b, NestSeq k a b ∧ b 0 = y})

/-- A `k`-nest exists. -/
def NestEx (k : ℕ) : Prop := ∃ a b, NestSeq k a b

theorem Tk_le_Om1 (k : ℕ) : Tk k ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem Tk_le {k : ℕ} {a b : ℕ → Ordinal.{0}} (h : NestSeq k a b) : Tk k ≤ b 0 :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨a, b, h, rfl⟩)

theorem Tk_attained {k : ℕ} (h1 : Tk k < Om1) : ∃ a b, NestSeq k a b ∧ b 0 = Tk k := by
  rcases csInf_mem (s := insert Om1 {y | ∃ a b, NestSeq k a b ∧ b 0 = y}) ⟨Om1, Set.mem_insert _ _⟩
    with h | h
  · exact absurd (h ▸ h1 : Om1 < Om1) (lt_irrefl _)
  · exact h

/-- A `k`-nest in the core of `R₂^C` ([C09] Thm 14.10 for the finite closed set of its points). -/
theorem nest_core_k {k : ℕ} (hk : 1 ≤ k) (hex : NestEx k) :
    ∃ a b, NestSeq k a b ∧ b 0 ∈ Core R2C := by
  obtain ⟨a, b, h⟩ := hex
  obtain ⟨Ps, ⟨g, hg⟩, -, hmin⟩ := C09_thm14_10 h.closed
  have hgN : NestSeq k (fun i => g (a i)) (fun i => g (b i)) :=
    h.map hg.1.2.1 (fun x hx y hy hxy => (hg.2.2 x hx y hy).1 hxy)
  refine ⟨_, _, hgN, Ps, hmin, ?_⟩
  exact Finset.mem_coe.1 (hg.1.1.mapsTo (Finset.mem_coe.2 (h.b_mem hk)))

/-- **`T_k < Ω₁`** when a `k`-nest exists (the core is countable, [C09] Cor 15.15). -/
theorem Tk_lt_Om1 {k : ℕ} (hk : 1 ≤ k) (hex : NestEx k) : Tk k < Om1 := by
  obtain ⟨a, b, hN, hy⟩ := nest_core_k hk hex
  obtain ⟨κ, hκ, hC⟩ := C09_cor15_15
  rw [hC] at hy
  exact lt_of_le_of_lt (Tk_le hN) (lt_trans hy hκ)

/-- **Lemma CAP at `T_k`**: if a `k`-nest has top `T_k`, no `α ≤ T_k` is `≤₁` a point `> T_k`. -/
theorem cap_Tk {k : ℕ} (hk : 1 ≤ k) {a b : ℕ → Ordinal.{0}} (hN : NestSeq k a b)
    (hT : b 0 = Tk k) : ∀ α ≤ Tk k, ∀ g, Tk k < g → ¬ le1 α g := by
  classical
  intro α hα g hg hαg
  rcases eq_or_ne α 0 with rfl | hα0
  · exact not_le1_zero (lt_of_le_of_lt zero_le hg) hαg
  set Rs := nestPts k a b with hRs
  have hRle : ∀ z ∈ Rs, z ≤ Tk k := fun z hz => hT ▸ (hN.bounds hz).2
  set X := Rs.filter (· < α) with hX
  set Y := Rs.filter (fun z => ¬ z < α) with hY
  have hXY : X ∪ Y = Rs := Finset.filter_union_filter_not_eq _ _
  have hcl : Closed (↑(X ∪ Y) : Set Ordinal.{0}) := by rw [hXY]; exact hN.closed
  obtain ⟨Yt, hYt, -, -, f, hf, -, hmap⟩ := le1_cof hαg (pos_iff_ne_zero.2 hα0) X Y
    (fun z hz => (Finset.mem_filter.1 hz).2)
    (fun z hz => ⟨not_lt.1 (Finset.mem_filter.1 hz).2,
      lt_of_le_of_lt (hRle z (Finset.mem_filter.1 hz).1) hg⟩) hcl
  have hsub : (↑(nestPts k a b) : Set Ordinal.{0}) = ↑(X ∪ Y) := by rw [hXY]
  have hfN : NestSeq k (fun i => f (a i)) (fun i => f (b i)) :=
    hN.map (hsub ▸ hf.1.2.1) (fun x hx y hy hxy => hf.2.2 x (hsub ▸ hx) y (hsub ▸ hy) hxy)
  have hbY : b 0 ∈ Y := Finset.mem_filter.2 ⟨hN.b_mem hk, not_lt.2 (hT ▸ hα)⟩
  have hfT : f (b 0) < α := (hYt _ (hmap (b 0) hbY)).2
  exact absurd (Tk_le hfN) (not_le.2 (lt_of_lt_of_le hfT hα))

/-- **`[0, T_k] ⊆ Core(R₂^C)`** if a `k`-nest has top `T_k` ([C09] Thm 14.14, Cor 15.15). -/
theorem Tk_core {k : ℕ} (hk : 1 ≤ k) {a b : ℕ → Ordinal.{0}} (hN : NestSeq k a b)
    (hT : b 0 = Tk k) : Set.Iic (Tk k) ⊆ Core R2C := by
  obtain ⟨κ0, -, hC⟩ := C09_cor15_15
  have hTκ : Tk k < κ0 := by
    by_contra hle
    push Not at hle
    by_cases hex : ∃ κ, LeInfC κ
    · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC hex
      have h1 := C09_thm14_14.1 κ hκ
      rw [hC] at h1
      have hκκ0 : κ = κ0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have : κ ∈ Set.Iio κ0 := h
          rw [h1] at this; exact lt_irrefl _ (Set.mem_Iio.1 this)
        · have : κ0 ∈ Set.Iio κ := h
          rw [← h1] at this; exact lt_irrefl _ (Set.mem_Iio.1 this)
      have hle1 := hκ.1 (Tk k + 1) (hκκ0 ▸ hle.trans (le_self_add))
      exact cap_Tk hk hN hT κ (hκκ0 ▸ hle) _ (lt_add_one _) hle1
    · have h2 := C09_thm14_14.2 hex
      rw [hC] at h2
      have : κ0 ∈ (Set.univ : Set Ordinal.{0}) := trivial
      rw [← h2] at this; exact lt_irrefl _ (Set.mem_Iio.1 this)
  intro z hz
  rw [hC]
  exact lt_of_le_of_lt hz hTκ

/-! ## The first block of level `m + 1` -/

section Level

variable {m : ℕ} {a b : ℕ → Ordinal.{0}} (hN : NestSeq (m + 1) a b) (hT : b 0 = Tk (m + 1))
include hN hT

omit hT in
theorem lv_xT : a 0 < b 0 := (hN.2 0 (by omega)).1

omit hT in
theorem lv_x2 : le2 (a 0) (b 0) := (hN.2 0 (by omega)).2

theorem lv_cap : ∀ α ≤ b 0, ∀ g, b 0 < g → ¬ le1 α g := by
  rw [hT]; exact cap_Tk (by omega) hN hT

/-- From a member `u ≤ x` of `U`, every `<₂`-successor `w` of `u` has `T ≤ w` (NEST-UP with the inner
nest, then the minimality of `T`). -/
theorem lv_up {u : Ordinal.{0}} (hu : le1 u (b 0)) (hux : u ≤ a 0) :
    ∀ w, u < w → le2 u w → b 0 ≤ w := by
  intro w huw h2
  obtain ⟨a', b', hN', -, hb'⟩ := nest_up hN.tail hu
    (fun _ => ⟨hux.trans (hN.1 0 (by omega)).1.le, (hN.1 0 (by omega)).2⟩) h2 huw
  rw [hT, ← hb']; exact Tk_le hN'

/-- **The only `<₂`-successor of `x` is `T`.** -/
theorem succ_x : ∀ w, a 0 < w → le2 (a 0) w → w = b 0 := by
  intro w hw h2
  have h1 := lv_up hN hT (le2_le1 (lv_x2 hN)) le_rfl w hw h2
  rcases eq_or_lt_of_le h1 with e | hlt
  · exact e.symm
  · exact absurd (le2_le1 h2) (lv_cap hN hT _ (lv_xT hN).le w hlt)

/-- **No member of `U` lies in `(x, T)`.** -/
theorem gap_empty {u : Ordinal.{0}} (h1 : a 0 < u) (h2 : u < b 0) : ¬ le1 u (b 0) := by
  intro hu
  have hx2 := le2_of_le1 h1.le h2.le (lv_x2 hN) hu
  exact absurd (succ_x hN hT u h1 hx2) (ne_of_lt h2)

/-- **No member of `U` below `x` is a `<₂`-left end.** -/
theorem noLeft_below {u : Ordinal.{0}} (hux : u < a 0) (hu : le1 u (b 0)) :
    ∀ w, u < w → ¬ le2 u w := by
  intro w huw h2
  have hTw := lv_up hN hT hu hux.le w huw h2
  rcases eq_or_lt_of_le hTw with e | hlt
  · -- `u <₂ T`, so `u <₂ x` (`≤₂` respects `≤₁`), and NEST-UP gives a nest with top `x < T`
    subst e
    have hx1 := le2_le1 (lv_x2 hN)
    have hux2 := le2_of_le1 hux.le (lv_xT hN).le h2 hx1
    have := lv_up hN hT hu hux.le (a 0) hux hux2
    exact absurd this (not_le.2 (lv_xT hN))
  · exact lv_cap hN hT u (hux.trans (lv_xT hN)).le w hlt (le2_le1 h2)

/-- **`x` is the only `<₂`-predecessor of `T`.** -/
theorem pred_T : ∀ c < b 0, le2 c (b 0) → c = a 0 := by
  intro c hc h2
  rcases lt_trichotomy c (a 0) with hlt | heq | hgt
  · exact absurd h2 (noLeft_below hN hT hlt (le2_le1 h2) _ hc)
  · exact heq
  · exact absurd (le2_le1 h2) (gap_empty hN hT hgt hc)

/-- **No member of `U` other than `T` is a `<₂`-right end.** -/
theorem noRight_U {u : Ordinal.{0}} (huT : u < b 0) (hu : le1 u (b 0)) :
    ∀ c < u, ¬ le2 c u := by
  intro c hcu h2
  have hc1 : le1 c (b 0) := le1_trans (le2_le1 h2) hu
  rcases lt_trichotomy c (a 0) with hlt | heq | hgt
  · exact noLeft_below hN hT hlt hc1 u hcu h2
  · subst heq
    exact absurd (succ_x hN hT u hcu h2) (ne_of_lt huT)
  · exact gap_empty hN hT hgt (hcu.trans huT) hc1

/-- **The shape of `U`**: `u ≤ T ∧ u ≤₁ T` iff `u ∈ Pred₁(x)`, `u = x` or `u = T`. -/
theorem U_shape (u : Ordinal.{0}) :
    (u ≤ b 0 ∧ le1 u (b 0)) ↔ ((u < a 0 ∧ le1 u (a 0)) ∨ u = a 0 ∨ u = b 0) := by
  have hx1 := le2_le1 (lv_x2 hN)
  constructor
  · rintro ⟨hu, hu1⟩
    rcases lt_trichotomy u (a 0) with hlt | heq | hgt
    · exact Or.inl ⟨hlt, le1_of_le_of_le1 hlt.le (lv_xT hN).le hu1⟩
    · exact Or.inr (Or.inl heq)
    · rcases eq_or_lt_of_le hu with he | hlt'
      · exact Or.inr (Or.inr he)
      · exact absurd hu1 (gap_empty hN hT hgt hlt')
  · rintro (⟨hlt, hu1⟩ | rfl | rfl)
    · exact ⟨(hlt.trans (lv_xT hN)).le, le1_trans hu1 hx1⟩
    · exact ⟨(lv_xT hN).le, hx1⟩
    · exact ⟨le_rfl, le1_refl _⟩

/-- **Every member of `U` has reach exactly `T`.** -/
theorem reach_U {u : Ordinal.{0}} (hu : u ≤ b 0) (hu1 : le1 u (b 0)) : IsReach R2C u (b 0) :=
  ⟨hu1, fun g hg => not_lt.1 (fun h => lv_cap hN hT u hu g h hg)⟩

/-- **The gaps of `U` contain `m`-nests**: below every positive member `u ≤ x` of `U`, above any
`z < u`, lies an `m`-nest (a copy of the inner nest, [C09] Def 5.3 clause 1 of `u ≤₁ T`). -/
theorem nests_below {u : Ordinal.{0}} (hux : u ≤ a 0) (hu : le1 u (b 0)) :
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

/-- **`T_m < s` for every positive member `s ≤ x` of `U`** (`m ≥ 1`); in particular `T_m < s_{m+1}`. -/
theorem Tk_lt_mem (hm : 1 ≤ m) {s : Ordinal.{0}} (hs0 : 0 < s) (hsx : s ≤ a 0)
    (hs : le1 s (b 0)) : Tk m < s := by
  obtain ⟨a', b', hN', hb⟩ := nests_below hN hT hsx hs 0 hs0
  exact lt_of_le_of_lt (Tk_le hN') (hb (by omega)).2

/-- **Theorem O^C at level `m + 1`**: every proper initial segment of `Pred₁(x)` is finite (and
`Pred₁(x)` is cofinal in `x`, `pred1_cof`), so `Pred₁(x)` has order type `ω`. -/
theorem oC : ∀ s < a 0, Set.Finite {u | u < s ∧ le1 u (a 0)} := by
  classical
  have hx1 := le2_le1 (lv_x2 hN)
  have hxT := lv_xT hN
  set S : Ordinal.{0} → Set Ordinal.{0} := fun t => {u | u < t ∧ le1 u (a 0)} with hS
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
  have hcof : ∀ z < s0, ∃ u, z < u ∧ u < s0 ∧ le1 u (a 0) := by
    intro z hz
    by_contra hno
    push Not at hno
    apply hs0T.2
    refine ((hfin z hz).union (Set.finite_singleton z)).subset ?_
    rintro u ⟨hu, hu1⟩
    rcases lt_trichotomy u z with h | h | h
    · exact Or.inl ⟨h, hu1⟩
    · exact Or.inr h
    · exact absurd hu1 (hno u h hu)
  have hs0pos : 0 < s0 := by
    obtain ⟨u, hu⟩ := hs0T.2.nonempty
    exact lt_of_le_of_lt zero_le hu.1
  have hs0x : s0 < a 0 := lt_of_le_of_lt hs0T.1 hs
  have hs01 : le1 s0 (a 0) :=
    le1_of_cof_left hs0x.le hs0pos (fun z hz => by
      obtain ⟨u, h1', h2', h3'⟩ := hcof z hz
      exact ⟨u, h1', h2'.le, h3'⟩)
  have hs0I : Indec s0 := indec_of_lt1 hs01 hs0x
  have hs0T1 : le1 s0 (b 0) := le1_trans hs01 hx1
  have hcore : s0 ∈ Core R2C := Tk_core (by omega) hN hT (by rw [← hT]; exact (hs0x.trans hxT).le)
  have hr : IsReach R2C s0 (b 0) := reach_U hN hT (hs0x.trans hxT).le hs0T1
  obtain ⟨v, hv, hv2⟩ := cp hs0I hcore hr (fun γ hγ => by
    obtain ⟨u, h1', h2', h3'⟩ := hcof γ hγ
    exact ⟨u, h1', h2', le1_trans h3' hx1⟩)
  exact noLeft_below hN hT hs0x hs0T1 v hv hv2

end Level

/-! ## Comparing levels -/

/-- **`T_{m+1} < T_{m+2}`** when an `(m+2)`-nest exists (its inner nest has a smaller top). -/
theorem Tk_lt_succ {m : ℕ} (hex : NestEx (m + 2)) : Tk (m + 1) < Tk (m + 2) := by
  obtain ⟨a, b, hN, hT⟩ := Tk_attained (Tk_lt_Om1 (by omega) hex)
  rw [← hT]
  exact lt_of_le_of_lt (Tk_le hN.tail) (hN.1 0 (by omega)).2

/-- A `2`-nest is a realization of PS. -/
theorem nest2_iff {a b : ℕ → Ordinal.{0}} :
    NestSeq 2 a b ↔ PSReal (a 0) (a 1) (b 1) (b 0) := by
  constructor
  · intro h
    exact ⟨(h.1 0 (by omega)).1, (h.2 1 (by omega)).1, (h.1 0 (by omega)).2,
      (h.2 0 (by omega)).2, (h.2 1 (by omega)).2⟩
  · rintro ⟨h1, h2, h3, hp, hp'⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have : i = 0 := by omega
      subst this; exact ⟨h1, h3⟩
    · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact ⟨h1.trans (h2.trans h3), hp⟩
      · exact ⟨h2, hp'⟩

/-- **`T₂ = T_C = ν_C`.** -/
theorem Tk_two : Tk 2 = nuC := by
  rw [nuC_eq_TnestC]
  have hset : {y | ∃ a b : ℕ → Ordinal.{0}, NestSeq 2 a b ∧ b 0 = y} =
      {y | ∃ x x' y', PSReal x x' y' y} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, h, rfl⟩
      exact ⟨a 0, a 1, b 1, nest2_iff.1 h⟩
    · rintro ⟨x, x', y', h⟩
      refine ⟨consS x (fun _ => x'), consS y (fun _ => y'), nest2_iff.2 ?_, rfl⟩
      exact h
  unfold Tk TnestC
  rw [hset]

end Googology.Trans.PoR.InaccPsi.R2
