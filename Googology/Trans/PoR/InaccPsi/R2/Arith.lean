import Googology.Trans.PoR.InaccPsi.R2.Basic

/-!
# Closed embeddings of `R₀ = (On; ≤, 0, +)`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.

For `R₀ = (On; ≤, 0, +)` (the arithmetic part of `R₂^C`) this file proves, with no axiom:

* `Indec`, `indec_iff`: the indecomposables of `R₀` ([C09] Def 2.1) are the nonzero additive
  principal numbers;
* `APL`, `pc`: every ordinal is the sum of a unique non-increasing list of indecomposables (its
  Cantor normal form with repetitions); `pc_add`: the list of `x + y`;
* `Closed.pc_mem`: a closed set contains the components of its elements;
* **[C09] Lemma 4.4** (`le_of_le_on_indec`, `eq_of_eq_on_indec`): two closed embeddings of a closed
  set that compare on its indecomposables compare everywhere;
* **[C09] Lemma 4.5** (`ext_arithIso`, `ext_closed`, `ext_indec`, `ext_unique`): an order
  preserving map `f` of the indecomposables of a closed set `A` into the indecomposables extends to
  the closed embedding `ext f` of `A` (`ξ₁ + ⋯ + ξₙ ↦ f ξ₁ + ⋯ + f ξₙ`), and this extension is
  unique;
* **[C09] Lemma 5.5 (7)** (`indec_of_lt1`, `exists_indec_of_lt1`, `indec_of_lt2_right`): a proper
  `≤₁`-left end is indecomposable and a limit of indecomposables; a proper `≤₂`-right end is
  indecomposable and a limit of indecomposables.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

/-! ## Indecomposables -/

/-- `x` is indecomposable in `R₀` ([C09] Def 2.1): `x` is neither the constant `0` nor a sum of two
smaller ordinals. -/
def Indec (x : Ordinal.{0}) : Prop := ¬ DecompR0 x

theorem indec_iff {x : Ordinal.{0}} : Indec x ↔ x ≠ 0 ∧ IsPrincipal (· + ·) x := by
  rw [isPrincipal_add_iff_add_lt_ne_self]
  constructor
  · intro h
    exact ⟨fun h0 => h (Or.inl h0), fun b hb c hc hbc => h (Or.inr ⟨b, c, hb, hc, hbc⟩)⟩
  · rintro ⟨h0, hp⟩ (h | ⟨y, z, hy, hz, hyz⟩)
    · exact h0 h
    · exact hp y hy z hz hyz

theorem Indec.ne_zero {x : Ordinal.{0}} (h : Indec x) : x ≠ 0 := (indec_iff.1 h).1

theorem Indec.pos {x : Ordinal.{0}} (h : Indec x) : 0 < x := pos_iff_ne_zero.2 h.ne_zero

theorem Indec.add_lt {x a b : Ordinal.{0}} (h : Indec x) (ha : a < x) (hb : b < x) : a + b < x :=
  (indec_iff.1 h).2 ha hb

theorem Indec.add_eq {x a : Ordinal.{0}} (h : Indec x) (ha : a < x) : a + x = x :=
  (indec_iff.1 h).2.add_eq_right ha

theorem indec_opow (e : Ordinal.{0}) : Indec (ω ^ e) :=
  indec_iff.2 ⟨(opow_pos e omega0_pos).ne', isPrincipal_add_omega0_opow e⟩

theorem not_decompR0_of_indec {x : Ordinal.{0}} (h : Indec x) : ¬ DecompR0 x := h

/-- An ordinal that is a limit of indecomposables (and not `0`) is indecomposable. -/
theorem indec_of_limit {b : Ordinal.{0}} (hb : 0 < b)
    (h : ∀ b' < b, ∃ p, b' < p ∧ p < b ∧ Indec p) : Indec b := by
  refine indec_iff.2 ⟨hb.ne', fun u v hu hv => ?_⟩
  obtain ⟨p, hp1, hp2, hp⟩ := h (max u v) (max_lt hu hv)
  exact lt_trans (hp.add_lt (lt_of_le_of_lt (le_max_left _ _) hp1)
    (lt_of_le_of_lt (le_max_right _ _) hp1)) hp2

/-- The image of a point that is not decomposable in `A`, under an arithmetic isomorphism onto a
closed set, is indecomposable. -/
theorem ArithIso.indec_of_not_decompIn {A B : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : ArithIso A B h) (hB : Closed B) {x : Ordinal.{0}} (hx : x ∈ A) (hnd : ¬ DecompIn A x) :
    Indec (h x) := by
  intro hd
  rcases hB (h x) (hh.1.mapsTo hx) hd with h0 | ⟨u, hu, v, hv, hu1, hv1, huv⟩
  · apply hnd; left
    have : h x + h x = h x := by rw [h0, add_zero]
    exact add_self_eq_self ((hh.2.2 x hx x hx x hx).2 this)
  · obtain ⟨u', hu'A, rfl⟩ := hh.1.surjOn hu
    obtain ⟨v', hv'A, rfl⟩ := hh.1.surjOn hv
    exact hnd (Or.inr ⟨u', hu'A, v', hv'A, (hh.2.1.lt_iff_lt hu'A hx).1 hu1,
      (hh.2.1.lt_iff_lt hv'A hx).1 hv1, (hh.2.2 u' hu'A v' hv'A x hx).2 huv⟩)

/-- An indecomposable element of a set is not decomposable in it. -/
theorem not_decompIn_of_indec {A : Set Ordinal.{0}} {x : Ordinal.{0}} (h : Indec x) :
    ¬ DecompIn A x := by
  rintro (h0 | ⟨y, -, z, -, hy, hz, hyz⟩)
  · exact h (Or.inl h0)
  · exact h (Or.inr ⟨y, z, hy, hz, hyz⟩)

/-- A covering of a closed set onto a closed set maps indecomposables to indecomposables. -/
theorem ArithIso.indec {A B : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : ArithIso A B h) (hB : Closed B) {x : Ordinal.{0}} (hx : x ∈ A) (hI : Indec x) :
    Indec (h x) :=
  hh.indec_of_not_decompIn hB hx (not_decompIn_of_indec hI)

/-- A set of indecomposables is closed. -/
theorem closed_of_indec {A : Set Ordinal.{0}} (h : ∀ x ∈ A, Indec x) : Closed A :=
  fun x hx hd => absurd hd (h x hx)

/-! ## Non-increasing lists of indecomposables -/

/-- A non-increasing list of indecomposables (a Cantor normal form, written with repetitions). -/
def APL (L : List Ordinal.{0}) : Prop := (∀ a ∈ L, Indec a) ∧ L.Pairwise (fun a b => b ≤ a)

theorem APL.nil : APL [] := ⟨by simp, List.Pairwise.nil⟩

theorem APL.cons_iff {a : Ordinal.{0}} {L : List Ordinal.{0}} :
    APL (a :: L) ↔ Indec a ∧ (∀ b ∈ L, b ≤ a) ∧ APL L := by
  unfold APL
  simp only [List.mem_cons, forall_eq_or_imp, List.pairwise_cons]
  tauto

theorem APL.tail {a : Ordinal.{0}} {L : List Ordinal.{0}} (h : APL (a :: L)) : APL L :=
  (APL.cons_iff.1 h).2.2

theorem APL.le_head {a : Ordinal.{0}} {L : List Ordinal.{0}} (h : APL (a :: L)) {b : Ordinal.{0}}
    (hb : b ∈ L) : b ≤ a :=
  (APL.cons_iff.1 h).2.1 b hb

theorem sum_lt_of_forall_lt {L : List Ordinal.{0}} {h : Ordinal.{0}} (hh : Indec h)
    (hL : ∀ a ∈ L, a < h) : L.sum < h := by
  induction L with
  | nil => simpa using hh.pos
  | cons a L ih =>
    rw [List.sum_cons]
    exact hh.add_lt (hL a (by simp)) (ih fun b hb => hL b (by simp [hb]))

theorem le_sum_of_mem {L : List Ordinal.{0}} {a : Ordinal.{0}} (ha : a ∈ L) : a ≤ L.sum := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · exact le_self_add
    · exact (ih ha).trans (le_add_self)

/-- Lexicographic order of lists (a proper prefix is smaller). -/
def LexLt : List Ordinal.{0} → List Ordinal.{0} → Prop
  | [], [] => False
  | [], _ :: _ => True
  | _ :: _, [] => False
  | a :: l, b :: m => a < b ∨ (a = b ∧ LexLt l m)

theorem lexLt_irrefl : ∀ L : List Ordinal.{0}, ¬ LexLt L L
  | [] => by simp [LexLt]
  | a :: l => by
    simp only [LexLt, lt_irrefl, false_or, true_and]
    exact lexLt_irrefl l

theorem lexLt_total : ∀ L M : List Ordinal.{0}, L ≠ M → LexLt L M ∨ LexLt M L
  | [], [] => fun h => absurd rfl h
  | [], _ :: _ => fun _ => Or.inl trivial
  | _ :: _, [] => fun _ => Or.inr trivial
  | a :: l, b :: m => fun h => by
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact Or.inl (Or.inl hab)
    · have hlm : l ≠ m := fun e => h (by rw [e])
      rcases lexLt_total l m hlm with h' | h'
      · exact Or.inl (Or.inr ⟨rfl, h'⟩)
      · exact Or.inr (Or.inr ⟨rfl, h'⟩)
    · exact Or.inr (Or.inl hab)

theorem sum_lt_of_lexLt : ∀ {L M : List Ordinal.{0}}, APL L → APL M → LexLt L M → L.sum < M.sum
  | [], [], _, _, h => absurd h (by simp [LexLt])
  | [], b :: m, _, hM, _ => by
    rw [List.sum_nil, List.sum_cons]
    exact lt_of_lt_of_le (APL.cons_iff.1 hM).1.pos (le_self_add)
  | _ :: _, [], _, _, h => absurd h (by simp [LexLt])
  | a :: l, b :: m, hL, hM, h => by
    rcases h with hab | ⟨rfl, h⟩
    · have hb := (APL.cons_iff.1 hM).1
      have hlt : (a :: l).sum < b := by
        refine sum_lt_of_forall_lt hb fun c hc => ?_
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hab
        · exact lt_of_le_of_lt (hL.le_head hc) hab
      exact lt_of_lt_of_le hlt (by rw [List.sum_cons]; exact le_self_add)
    · rw [List.sum_cons, List.sum_cons]
      exact (add_lt_add_iff_left a).2 (sum_lt_of_lexLt hL.tail hM.tail h)

/-- A non-increasing list of indecomposables is determined by its sum. -/
theorem eq_of_sum_eq {L M : List Ordinal.{0}} (hL : APL L) (hM : APL M) (h : L.sum = M.sum) :
    L = M := by
  by_contra hne
  rcases lexLt_total L M hne with h' | h'
  · exact absurd h (sum_lt_of_lexLt hL hM h').ne
  · exact absurd h.symm (sum_lt_of_lexLt hM hL h').ne

theorem lexLt_iff_sum_lt {L M : List Ordinal.{0}} (hL : APL L) (hM : APL M) :
    LexLt L M ↔ L.sum < M.sum := by
  refine ⟨sum_lt_of_lexLt hL hM, fun h => ?_⟩
  by_cases hne : L = M
  · subst hne; exact absurd h (lt_irrefl _)
  rcases lexLt_total L M hne with h' | h'
  · exact h'
  · exact absurd (sum_lt_of_lexLt hM hL h') (not_lt.2 h.le)

/-- Every ordinal is the sum of a non-increasing list of indecomposables. -/
theorem exists_APL (x : Ordinal.{0}) : ∃ L, APL L ∧ L.sum = x := by
  induction x using WellFoundedLT.induction with
  | ind x IH =>
    rcases eq_or_ne x 0 with rfl | hx
    · exact ⟨[], APL.nil, by simp⟩
    have hpx : ω ^ log ω x ≤ x := opow_log_le_self ω hx
    have hxp : x < ω ^ log ω x * ω := by
      rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
    have hpy : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hpx
    have hyx : x - ω ^ log ω x < x := by
      refine lt_of_le_of_ne (sub_le_self x _) fun hyx => ?_
      rw [hyx] at hpy
      exact absurd (add_eq_right_iff_mul_omega0_le.1 hpy) (not_le.2 hxp)
    obtain ⟨L, hL, hLs⟩ := IH _ hyx
    refine ⟨ω ^ log ω x :: L, APL.cons_iff.2 ⟨indec_opow _, fun b hb => ?_, hL⟩,
      by rw [List.sum_cons, hLs, hpy]⟩
    by_contra hbp
    have hbI : Indec b := hL.1 b hb
    have h1 : ω ^ log ω x + b = b := hbI.add_eq (not_le.1 hbp)
    have h2 : ω ^ log ω x * ω ≤ b := add_eq_right_iff_mul_omega0_le.1 h1
    have h3 : b ≤ x - ω ^ log ω x := hLs ▸ le_sum_of_mem hb
    exact absurd (h2.trans (h3.trans hyx.le)) (not_le.2 hxp)

/-- `pc x`: the components of `x` (with repetitions, non-increasing). -/
noncomputable def pc (x : Ordinal.{0}) : List Ordinal.{0} := Classical.choose (exists_APL x)

theorem pc_APL (x : Ordinal.{0}) : APL (pc x) := (Classical.choose_spec (exists_APL x)).1

theorem pc_sum (x : Ordinal.{0}) : (pc x).sum = x := (Classical.choose_spec (exists_APL x)).2

theorem pc_eq {x : Ordinal.{0}} {L : List Ordinal.{0}} (hL : APL L) (h : L.sum = x) : pc x = L :=
  eq_of_sum_eq (pc_APL x) hL (by rw [pc_sum, h])

theorem pc_zero : pc 0 = [] := pc_eq APL.nil (by simp)

theorem pc_indec {x : Ordinal.{0}} (hx : Indec x) : pc x = [x] :=
  pc_eq (APL.cons_iff.2 ⟨hx, by simp, APL.nil⟩) (by simp)

theorem indec_of_mem_pc {x a : Ordinal.{0}} (ha : a ∈ pc x) : Indec a := (pc_APL x).1 a ha

theorem le_of_mem_pc {x a : Ordinal.{0}} (ha : a ∈ pc x) : a ≤ x :=
  pc_sum x ▸ le_sum_of_mem ha

/-! ## Addition -/

/-- The list of `L.sum + M.sum`: the components of `L` that are `≥` the head of `M`, then `M`. -/
noncomputable def addL (L : List Ordinal.{0}) : List Ordinal.{0} → List Ordinal.{0}
  | [] => L
  | h :: m => L.takeWhile (fun a => decide (h ≤ a)) ++ h :: m

theorem lt_of_mem_dropWhile {h : Ordinal.{0}} : ∀ {L : List Ordinal.{0}},
    L.Pairwise (fun a b => b ≤ a) → ∀ a ∈ L.dropWhile (fun a => decide (h ≤ a)), a < h
  | [], _ => by simp
  | b :: l, hL => by
    intro a ha
    by_cases hb : h ≤ b
    · rw [List.dropWhile_cons_of_pos (by simpa using hb)] at ha
      exact lt_of_mem_dropWhile (List.pairwise_cons.1 hL).2 a ha
    · rw [List.dropWhile_cons_of_neg (by simpa using hb)] at ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact not_le.1 hb
      · exact lt_of_le_of_lt ((List.pairwise_cons.1 hL).1 a ha) (not_le.1 hb)

theorem addL_sum {L M : List Ordinal.{0}} (hL : APL L) (hM : APL M) :
    (addL L M).sum = L.sum + M.sum := by
  cases M with
  | nil => simp [addL]
  | cons h m =>
    simp only [addL, List.sum_append]
    have hsplit := List.takeWhile_append_dropWhile (p := fun a => decide (h ≤ a)) (l := L)
    have hD : (L.dropWhile (fun a => decide (h ≤ a))).sum < h :=
      sum_lt_of_forall_lt (APL.cons_iff.1 hM).1 (lt_of_mem_dropWhile hL.2)
    have hDh : (L.dropWhile (fun a => decide (h ≤ a))).sum + h = h :=
      (APL.cons_iff.1 hM).1.add_eq hD
    have hLs : L.sum = (L.takeWhile (fun a => decide (h ≤ a))).sum +
        (L.dropWhile (fun a => decide (h ≤ a))).sum := by
      rw [← List.sum_append, hsplit]
    rw [hLs, List.sum_cons, add_assoc, ← add_assoc (L.dropWhile _).sum, hDh]

theorem addL_APL {L M : List Ordinal.{0}} (hL : APL L) (hM : APL M) : APL (addL L M) := by
  cases M with
  | nil => simpa [addL] using hL
  | cons h m =>
    simp only [addL]
    have hT : List.Sublist (L.takeWhile (fun a => decide (h ≤ a))) L := List.takeWhile_sublist _
    refine ⟨fun a ha => ?_, ?_⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact hL.1 a (hT.subset ha)
      · exact hM.1 a ha
    · rw [List.pairwise_append]
      refine ⟨hL.2.sublist hT, hM.2, fun a ha b hb => ?_⟩
      have hha : h ≤ a := by simpa using List.mem_takeWhile_imp ha
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hha
      · exact (hM.le_head hb).trans hha

theorem mem_addL {L M : List Ordinal.{0}} {a : Ordinal.{0}} (ha : a ∈ addL L M) :
    a ∈ L ∨ a ∈ M := by
  cases M with
  | nil => exact Or.inl ha
  | cons h m =>
    rcases List.mem_append.1 ha with ha | ha
    · exact Or.inl ((List.takeWhile_sublist _).subset ha)
    · exact Or.inr ha

theorem pc_add (x y : Ordinal.{0}) : pc (x + y) = addL (pc x) (pc y) :=
  pc_eq (addL_APL (pc_APL x) (pc_APL y)) (by rw [addL_sum (pc_APL x) (pc_APL y), pc_sum, pc_sum])

/-! ## Maps of lists -/

theorem map_takeWhile_of_strictMonoOn {S : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : StrictMonoOn f S) {h : Ordinal.{0}} (hh : h ∈ S) : ∀ {L : List Ordinal.{0}},
    (∀ a ∈ L, a ∈ S) → (L.takeWhile (fun a => decide (h ≤ a))).map f =
      (L.map f).takeWhile (fun a => decide (f h ≤ a))
  | [], _ => by simp
  | a :: l, hl => by
    have ha : a ∈ S := hl a (by simp)
    have hiff : f h ≤ f a ↔ h ≤ a := hf.le_iff_le hh ha
    have ih := map_takeWhile_of_strictMonoOn hf hh (L := l) (fun b hb => hl b (by simp [hb]))
    by_cases hha : h ≤ a
    · rw [List.takeWhile_cons_of_pos (by simpa using hha), List.map_cons, List.map_cons,
        List.takeWhile_cons_of_pos (by simpa using hiff.2 hha), ih]
    · rw [List.takeWhile_cons_of_neg (by simpa using hha), List.map_cons,
        List.takeWhile_cons_of_neg (by simpa [hiff] using hha)]
      simp

theorem map_addL {S : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hf : StrictMonoOn f S)
    {L M : List Ordinal.{0}} (hL : ∀ a ∈ L, a ∈ S) (hM : ∀ a ∈ M, a ∈ S) :
    (addL L M).map f = addL (L.map f) (M.map f) := by
  cases M with
  | nil => simp [addL]
  | cons h m =>
    simp only [addL, List.map_append, List.map_cons,
      map_takeWhile_of_strictMonoOn hf (hM h (by simp)) hL]

theorem APL.map {S : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hf : StrictMonoOn f S)
    (hfI : ∀ a ∈ S, Indec (f a)) {L : List Ordinal.{0}} (hL : APL L) (hLS : ∀ a ∈ L, a ∈ S) :
    APL (L.map f) := by
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact hfI a (hLS a ha)
  · rw [List.pairwise_map]
    exact hL.2.imp_of_mem fun {a b} ha hb hab => (hf.le_iff_le (hLS b hb) (hLS a ha)).2 hab

theorem lexLt_map {S : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (hf : StrictMonoOn f S) :
    ∀ {L M : List Ordinal.{0}}, (∀ a ∈ L, a ∈ S) → (∀ a ∈ M, a ∈ S) →
      (LexLt (L.map f) (M.map f) ↔ LexLt L M)
  | [], [], _, _ => by simp [LexLt]
  | [], _ :: _, _, _ => by simp [LexLt]
  | _ :: _, [], _, _ => by simp [LexLt]
  | a :: l, b :: m, hL, hM => by
    have ha := hL a (by simp)
    have hb := hM b (by simp)
    simp only [List.map_cons, LexLt]
    rw [hf.lt_iff_lt ha hb, hf.injOn.eq_iff ha hb,
      lexLt_map hf (fun c hc => hL c (by simp [hc])) (fun c hc => hM c (by simp [hc]))]

theorem map_inj_of_injOn {S : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hf : Set.InjOn f S) : ∀ {L M : List Ordinal.{0}}, (∀ a ∈ L, a ∈ S) → (∀ a ∈ M, a ∈ S) →
      L.map f = M.map f → L = M
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l, b :: m, hL, hM, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf (hL a (by simp)) (hM b (by simp)) h.1,
      map_inj_of_injOn hf (fun c hc => hL c (by simp [hc])) (fun c hc => hM c (by simp [hc])) h.2]

/-! ## Closed sets and their components -/

/-- The indecomposable elements of `A`. -/
def IndecIn (A : Set Ordinal.{0}) : Set Ordinal.{0} := {x | x ∈ A ∧ Indec x}

/-- A closed set contains the components of its elements. -/
theorem Closed.pc_mem {A : Set Ordinal.{0}} (hA : Closed A) : ∀ x ∈ A, ∀ a ∈ pc x, a ∈ A := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
    intro hx a ha
    by_cases hI : Indec x
    · rw [pc_indec hI] at ha
      rw [List.mem_singleton.1 ha]; exact hx
    · rcases hA x hx (not_not.1 hI) with h0 | ⟨y, hy, z, hz, hyx, hzx, hyz⟩
      · subst h0; rw [pc_zero] at ha; simp at ha
      · rw [← hyz, pc_add] at ha
        rcases mem_addL ha with ha | ha
        · exact IH y hyx hy a ha
        · exact IH z hzx hz a ha

theorem Closed.pc_mem_indecIn {A : Set Ordinal.{0}} (hA : Closed A) {x : Ordinal.{0}}
    (hx : x ∈ A) : ∀ a ∈ pc x, a ∈ IndecIn A :=
  fun a ha => ⟨hA.pc_mem x hx a ha, indec_of_mem_pc ha⟩

/-! ## [C09] Lemma 4.4 -/

/-- **[C09] Lemma 4.4**: if two arithmetic isomorphisms of a closed set `A` (onto any sets) satisfy
`h₁(a) ≤ h₂(a)` on the indecomposables of `A`, then `h₁(x) ≤ h₂(x)` for all `x ∈ A`. -/
theorem le_of_le_on_indec {A B₁ B₂ : Set Ordinal.{0}} (hA : Closed A)
    {h₁ h₂ : Ordinal.{0} → Ordinal.{0}} (h₁i : ArithIso A B₁ h₁) (h₂i : ArithIso A B₂ h₂)
    (hle : ∀ a ∈ A, Indec a → h₁ a ≤ h₂ a) : ∀ x ∈ A, h₁ x ≤ h₂ x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
    intro hx
    by_cases hI : Indec x
    · exact hle x hx hI
    · rcases hA x hx (not_not.1 hI) with h0 | ⟨y, hy, z, hz, hyx, hzx, hyz⟩
      · subst h0; rw [h₁i.map_zero hx, h₂i.map_zero hx]
      · rw [← (h₁i.2.2 y hy z hz x hx).1 hyz, ← (h₂i.2.2 y hy z hz x hx).1 hyz]
        exact add_le_add (IH y hyx hy) (IH z hzx hz)

/-- **[C09] Lemma 4.4**, second part: arithmetic isomorphisms of a closed set that agree on its
indecomposables agree. -/
theorem eq_of_eq_on_indec {A B₁ B₂ : Set Ordinal.{0}} (hA : Closed A)
    {h₁ h₂ : Ordinal.{0} → Ordinal.{0}} (h₁i : ArithIso A B₁ h₁) (h₂i : ArithIso A B₂ h₂)
    (heq : ∀ a ∈ A, Indec a → h₁ a = h₂ a) : ∀ x ∈ A, h₁ x = h₂ x := fun x hx =>
  le_antisymm (le_of_le_on_indec hA h₁i h₂i (fun a ha hI => (heq a ha hI).le) x hx)
    (le_of_le_on_indec hA h₂i h₁i (fun a ha hI => (heq a ha hI).ge) x hx)

/-! ## [C09] Lemma 4.5 -/

/-- The closed embedding of [C09] Lemma 4.5: `ξ₁ + ⋯ + ξₙ ↦ f ξ₁ + ⋯ + f ξₙ`. -/
noncomputable def ext (f : Ordinal.{0} → Ordinal.{0}) (x : Ordinal.{0}) : Ordinal.{0} :=
  ((pc x).map f).sum

section Ext

variable {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}

theorem ext_indec {x : Ordinal.{0}} (hx : Indec x) : ext f x = f x := by
  simp [ext, pc_indec hx]

theorem ext_zero : ext f 0 = 0 := by simp [ext, pc_zero]

theorem ext_lt_iff (hA : Closed A) (hf : StrictMonoOn f (IndecIn A))
    (hfI : ∀ a ∈ IndecIn A, Indec (f a)) {x y : Ordinal.{0}} (hx : x ∈ A) (hy : y ∈ A) :
    ext f x < ext f y ↔ x < y := by
  have hSx := hA.pc_mem_indecIn hx
  have hSy := hA.pc_mem_indecIn hy
  show ((pc x).map f).sum < ((pc y).map f).sum ↔ x < y
  rw [← lexLt_iff_sum_lt (APL.map hf hfI (pc_APL x) hSx) (APL.map hf hfI (pc_APL y) hSy),
    lexLt_map hf hSx hSy, lexLt_iff_sum_lt (pc_APL x) (pc_APL y), pc_sum, pc_sum]

theorem ext_add_iff (hA : Closed A) (hf : StrictMonoOn f (IndecIn A))
    (hfI : ∀ a ∈ IndecIn A, Indec (f a)) {x y z : Ordinal.{0}} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) : ext f x + ext f y = ext f z ↔ x + y = z := by
  have hSx := hA.pc_mem_indecIn hx
  have hSy := hA.pc_mem_indecIn hy
  have hSz := hA.pc_mem_indecIn hz
  have hSxy : ∀ a ∈ addL (pc x) (pc y), a ∈ IndecIn A := fun a ha =>
    (mem_addL ha).elim (hSx a) (hSy a)
  have key : ext f x + ext f y = ((addL (pc x) (pc y)).map f).sum := by
    rw [map_addL hf hSx hSy, addL_sum (APL.map hf hfI (pc_APL x) hSx)
      (APL.map hf hfI (pc_APL y) hSy)]
    rfl
  constructor
  · intro h
    have hl : (addL (pc x) (pc y)).map f = (pc z).map f :=
      eq_of_sum_eq (APL.map hf hfI (addL_APL (pc_APL x) (pc_APL y)) hSxy)
        (APL.map hf hfI (pc_APL z) hSz) (by rw [← key, h]; rfl)
    have he := map_inj_of_injOn hf.injOn hSxy hSz hl
    calc x + y = (pc x).sum + (pc y).sum := by rw [pc_sum, pc_sum]
      _ = (addL (pc x) (pc y)).sum := (addL_sum (pc_APL x) (pc_APL y)).symm
      _ = (pc z).sum := by rw [he]
      _ = z := pc_sum z
  · intro h
    rw [key, ← pc_add, h]
    rfl

/-- **[C09] Lemma 4.5**: an order preserving map `f` of the indecomposables of a closed set `A` into
the indecomposables extends to an arithmetic isomorphism `ext f` of `A` onto its image. -/
theorem ext_arithIso (hA : Closed A) (hf : StrictMonoOn f (IndecIn A))
    (hfI : ∀ a ∈ IndecIn A, Indec (f a)) : ArithIso A (ext f '' A) (ext f) := by
  refine ⟨⟨fun x hx => ⟨x, hx, rfl⟩, fun x hx y hy hxy => ?_, fun y hy => hy⟩, ?_, ?_⟩
  · rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy ((ext_lt_iff hA hf hfI hx hy).2 h).ne
    · exact h
    · exact absurd hxy.symm ((ext_lt_iff hA hf hfI hy hx).2 h).ne
  · intro x hx y hy hxy
    exact (ext_lt_iff hA hf hfI hx hy).2 hxy
  · intro x hx y hy z hz
    exact (ext_add_iff hA hf hfI hx hy hz).symm

/-- **[C09] Lemma 4.5**: the range of `ext f` is closed ("a closed embedding"). -/
theorem ext_closed (hA : Closed A) (hf : StrictMonoOn f (IndecIn A))
    (hfI : ∀ a ∈ IndecIn A, Indec (f a)) : Closed (ext f '' A) := by
  rintro _ ⟨x, hx, rfl⟩ hd
  by_cases hI : Indec x
  · rw [ext_indec hI] at hd
    exact absurd hd (hfI x ⟨hx, hI⟩)
  · rcases hA x hx (not_not.1 hI) with h0 | ⟨y, hy, z, hz, hyx, hzx, hyz⟩
    · subst h0; left; exact ext_zero
    · right
      exact ⟨ext f y, ⟨y, hy, rfl⟩, ext f z, ⟨z, hz, rfl⟩, (ext_lt_iff hA hf hfI hy hx).2 hyx,
        (ext_lt_iff hA hf hfI hz hx).2 hzx, (ext_add_iff hA hf hfI hy hz hx).2 hyz⟩

/-- **[C09] Lemma 4.5**, uniqueness: an arithmetic isomorphism of a closed set that agrees with `f`
on the indecomposables is `ext f`. -/
theorem ext_unique (hA : Closed A) (hf : StrictMonoOn f (IndecIn A))
    (hfI : ∀ a ∈ IndecIn A, Indec (f a)) {B : Set Ordinal.{0}} {h : Ordinal.{0} → Ordinal.{0}}
    (hh : ArithIso A B h) (heq : ∀ a ∈ A, Indec a → h a = f a) : ∀ x ∈ A, h x = ext f x :=
  eq_of_eq_on_indec hA hh (ext_arithIso hA hf hfI) (fun a ha hI => by rw [heq a ha hI, ext_indec hI])

/-- `ext f` fixes every element of `A` whose components are fixed by `f`. -/
theorem ext_fix {x : Ordinal.{0}} (h : ∀ a ∈ pc x, f a = a) : ext f x = x := by
  unfold ext
  rw [List.map_congr_left h, List.map_id', pc_sum]

end Ext

/-! ## [C09] Lemma 5.5 (7) -/

theorem closed_singleton_zero : Closed ({0} : Set Ordinal.{0}) :=
  fun x hx _ => Or.inl (by simpa using hx)

/-- **[C09] Lemma 5.5 (7)(a)**, first part: if `α <₁ β` then `α` is indecomposable. -/
theorem indec_of_lt1 {a b : Ordinal.{0}} (h : le1 a b) (hab : a < b) : Indec a := by
  classical
  intro hd
  rcases hd with h0 | ⟨y, z, hy, hz, hyz⟩
  · subst h0
    obtain ⟨_, H⟩ := le1_iff.1 h
    obtain ⟨Yt, h1, -, -, f, hf⟩ := H ∅ {0} (by simp) (by simp [hab])
      (by simpa using closed_singleton_zero)
    have hm := hf.1.1.mapsTo (show (0 : Ordinal.{0}) ∈ (↑(∅ ∪ {0} : Finset Ordinal.{0}) :
      Set Ordinal.{0}) by simp)
    simp only [Finset.empty_union,
      Finset.mem_coe] at hm
    exact absurd (h1 _ hm) (not_lt.2 zero_le)
  · have ha0 : 0 < a := lt_of_le_of_lt zero_le hy
    obtain ⟨C, hsub, hC, hCb⟩ := exists_closed {y, z}
    have hCa : ∀ c ∈ C, c < a := by
      intro c hc
      obtain ⟨s, hs, hcs⟩ := hCb c hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact lt_of_le_of_lt hcs hy
      · exact lt_of_le_of_lt hcs hz
    have hyC : y ∈ C := hsub (by simp)
    have hzC : z ∈ C := hsub (by simp)
    have hcl : Closed ↑(C ∪ {a}) := by
      intro w hw hdw
      simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Finset.mem_coe,
        Set.mem_singleton_iff] at hw
      rcases hw with hw | rfl
      · exact (hC w hw hdw).mono (by simp)
      · exact Or.inr ⟨y, by simp [hyC], z, by simp [hzC], hy, hz, hyz⟩
    obtain ⟨Yt, h1, -, -, f, hf, hfix, hY⟩ := le1_cof h ha0 C {a} hCa (by simp [hab]) hcl
    have hfa : f a ∈ Yt := hY a (by simp)
    have hyz' : f y + f z = f a :=
      (hf.1.2.2 y (by simp [hyC]) z (by simp [hzC]) a (by simp)).1 hyz
    rw [hfix y hyC, hfix z hzC, hyz] at hyz'
    exact absurd hyz' (h1 _ hfa).2.ne'

/-- **[C09] Lemma 5.5 (7)(a)**: if `α <₁ β` then `α` is a limit of indecomposables. -/
theorem exists_indec_of_lt1 {a b a' : Ordinal.{0}} (h : le1 a b) (hab : a < b) (ha' : a' < a) :
    ∃ p, a' < p ∧ p < a ∧ Indec p := by
  classical
  have hI := indec_of_lt1 h hab
  have hcl : Closed ↑((∅ : Finset Ordinal.{0}) ∪ {a}) :=
    closed_of_indec (fun x hx => by simp at hx; rw [hx]; exact hI)
  obtain ⟨Yt, h1, -, h3, f, hf, -, hY⟩ := le1_cof h ha' ∅ {a} (by simp) (by simp [hab]) hcl
  have hfa : f a ∈ Yt := hY a (by simp)
  refine ⟨f a, (h1 _ hfa).1, (h1 _ hfa).2, ?_⟩
  exact hf.1.indec h3 (by simp) hI

/-- **[C09] Lemma 5.5 (7)(b)**: if `α <₂ β` then `β` is indecomposable and a limit of
indecomposables. -/
theorem indec_of_lt2_right {a b : Ordinal.{0}} (h : le2 a b) (hab : a < b) :
    Indec b ∧ ∀ b' < b, ∃ p, b' < p ∧ p < b ∧ Indec p := by
  classical
  have h1 := le2_le1 h
  have hI := indec_of_lt1 h1 hab
  obtain ⟨_, -, H2⟩ := le2_iff.1 h
  have hZ : Closed ↑({a} : Finset Ordinal.{0}) :=
    closed_of_indec (fun x hx => by simp at hx; rw [hx]; exact hI)
  have hcof : CofCov R2C ∅ {a} R2C a := by
    intro c' hc'
    obtain ⟨Yt, hy1, -, h3, f, hf, -, -⟩ := le1_cof h1 hc' ∅ {a} (by simp) (by simp [hab])
      (by simpa using hZ)
    exact ⟨Yt, hy1, h3, f, by simpa using hf⟩
  have hcofb := H2 ∅ (by simp) {a} R2C hZ hcof
  have hlim : ∀ b' < b, ∃ p, b' < p ∧ p < b ∧ Indec p := by
    intro b' hb'
    obtain ⟨Y, hY, hcl, g, hg⟩ := hcofb b' hb'
    have hga : g a ∈ (↑(∅ ∪ Y) : Set Ordinal.{0}) := hg.1.1.mapsTo (by simp)
    have hgaY : g a ∈ Y := by simpa using hga
    exact ⟨g a, (hY _ hgaY).1, (hY _ hgaY).2, hg.1.indec hcl (by simp) hI⟩
  exact ⟨indec_of_limit (lt_of_le_of_lt zero_le hab) hlim, hlim⟩

end Googology.Trans.PoR.InaccPsi.R2
