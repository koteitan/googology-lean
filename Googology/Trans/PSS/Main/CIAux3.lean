import Googology.Trans.PSS.Main.CIAux2

/-!
# CI, part 3: `jN` commutes with the operations of `𝒯`

On `T¹_α` (`DomA a`), `jN a` commutes with the sum with absorption (`addS`, `addAll`),
`-1 + ·`, `splitLevel`, `runStart`, and ([W07a] Lemma 7.2, "ι-exp" of `proof/PROOF-3.md`
§13.0) with `ω^·` and `log_ω` (lowering the level by one; `ω^·` at level `1` goes to
`ω^·` at level `0`, with `ϑ_1(0) = Ω_1 ↦ α`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

set_option linter.unusedSectionVars false

theorem dropWhile_map_congr {α β : Type*} {f : α → β} {P : α → Bool} {Q : β → Bool} :
    ∀ {l : List α}, (∀ p ∈ l, Q (f p) = P p) → (l.map f).dropWhile Q = (l.dropWhile P).map f
  | [], _ => by simp
  | p :: l, h => by
    rw [List.map_cons, List.dropWhile_cons, List.dropWhile_cons, h p (by simp)]
    split_ifs
    · exact dropWhile_map_congr (fun q hq => h q (by simp [hq]))
    · rfl

theorem tail_eq_dropLast_of_all {x : WP} : ∀ {r : List WP}, (∀ q ∈ r, q = x) →
    r.tail = r.dropLast
  | [], _ => rfl
  | [_], _ => rfl
  | q :: q' :: r, h => by
    have ih := tail_eq_dropLast_of_all (r := q' :: r) (fun z hz => h z (by simp [hz]))
    simp only [List.tail_cons] at ih
    rw [List.tail_cons, List.dropLast_cons₂, ← ih, h q (by simp), h q' (by simp)]

theorem omegaExp_cons (p : WP) (r : List WP) (m : ℕ) :
    omegaExp (p :: r) m =
      if r = [] ∧ isEpsLevel p m = true then p
      else if r ≠ [] ∧ isEpsPlusN (p :: r) m = true then .th m (p :: r).dropLast
      else if 1 ≤ m ∧ p = .th m [] then .th m r
      else .th m (p :: r) := rfl

section Comm

variable {a : WP} (ha : NFP a) (h0 : a.lvl = 0)
include ha h0

theorem cmpP_jN {p q : WP} (hp : DomA a p) (hq : DomA a q) :
    cmpP (jN a p) (jN a q) = cmpP p q := by
  rw [cmpP_eq (nfp_jN ha h0 hp) (nfp_jN ha h0 hq), cmpP_eq hp.1 hq.1]
  rcases lt_trichotomy p.val q.val with h | h | h
  · rw [(compare_lt_iff_lt).mpr h, (compare_lt_iff_lt).mpr (jN_lt ha h0 hp hq h)]
  · rw [eq_of_val_eq hp.1 hq.1 h]; simp
  · rw [(compare_gt_iff_gt).mpr h, (compare_gt_iff_gt).mpr (jN_lt ha h0 hq hp h)]

theorem addS_jN {x y : List WP} (hx : ∀ p ∈ x, DomA a p) (hy : ∀ p ∈ y, DomA a p) :
    addS (x.map (jN a)) (y.map (jN a)) = (addS x y).map (jN a) := by
  cases y with
  | nil => simp [addS]
  | cons y0 y' =>
    simp only [List.map_cons, addS]
    have key := dropWhile_map_congr (l := x.reverse) (f := jN a)
      (P := fun p => cmpP p y0 == .lt) (Q := fun p => cmpP p (jN a y0) == .lt) (fun p hp => by
        simp only
        rw [cmpP_jN ha h0 (hx p (List.mem_reverse.mp hp)) (hy y0 (by simp))])
    rw [List.map_append, List.map_cons, ← List.map_reverse, key, ← List.map_reverse]

theorem addAll_foldl_jN : ∀ (xs : List (List WP)) {r : List WP}, (∀ p ∈ r, DomA a p) →
    (∀ x ∈ xs, ∀ p ∈ x, DomA a p) →
    (xs.map (fun x => x.map (jN a))).foldl addS (r.map (jN a)) = (xs.foldl addS r).map (jN a)
  | [], _, _, _ => rfl
  | x :: xs, r, hr, hxs => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons,
      addS_jN ha h0 hr (hxs x (by simp))]
    refine addAll_foldl_jN xs (fun p hp => ?_) (fun x' hx' => hxs x' (by simp [hx']))
    rcases mem_addS hp with h | h
    · exact hr p h
    · exact hxs x (by simp) p h

theorem addAll_jN {xs : List (List WP)} (hxs : ∀ x ∈ xs, ∀ p ∈ x, DomA a p) :
    addAll (xs.map (fun x => x.map (jN a))) = (addAll xs).map (jN a) := by
  unfold addAll
  have := addAll_foldl_jN ha h0 xs (r := []) (by simp) hxs
  simpa using this

theorem jN_eq_one {p : WP} (hp : DomA a p) (ha1 : a ≠ TR.one) : jN a p = TR.one ↔ p = TR.one := by
  constructor
  · intro h
    obtain ⟨k, b⟩ := p
    rcases k with _ | _ | k
    · rw [jN_zero] at h; exact h
    · by_cases hb : b = []
      · subst hb; rw [jN_one_nil] at h; exact absurd h ha1
      · have hl := (g1 ha h0 hp).2.2 rfl (by simpa using hb)
        rw [h, val_one] at hl
        exact absurd (lt_of_lt_of_le hl (one_le_val ha)) (lt_irrefl _)
    · rw [jN_add_two] at h; simp [TR.one] at h
  · rintro rfl; exact jN_one_eq a

theorem minusOnePlus_jN {x : List WP} (hx : ∀ p ∈ x, DomA a p) (ha1 : a ≠ TR.one) :
    minusOnePlus (x.map (jN a)) = (minusOnePlus x).map (jN a) := by
  cases x with
  | nil => rfl
  | cons p r =>
    have e := jN_eq_one ha h0 (hx p (by simp)) ha1
    by_cases hp1 : p = TR.one
    · simp [minusOnePlus, hp1, jN_one_eq]
    · have : ¬ jN a p = TR.one := fun h => hp1 (e.mp h)
      simp [minusOnePlus, hp1, this]

theorem splitLevel_jN {m : ℕ} (hm : 1 ≤ m) (x : List WP) :
    splitLevel (x.map (jN a)) m =
      ((splitLevel x (m + 1)).1.map (jN a), (splitLevel x (m + 1)).2.map (jN a)) := by
  have hP : ∀ q : WP, decide (m ≤ (jN a q).lvl) = decide (m + 1 ≤ q.lvl) := fun q => by
    rw [jN_lvl h0]; by_cases h : m + 1 ≤ q.lvl <;> simp [h] <;> omega
  simp only [splitLevel]
  rw [List.takeWhile_map, List.dropWhile_map]
  simp only [Function.comp_def, hP]

theorem runStart_jN {ds : List (List WP)} (hds : ∀ d ∈ ds, ∀ p ∈ d, DomA a p) :
    runStart (ds.map (fun d => d.map (jN a))) = runStart ds := by
  unfold runStart
  rw [List.getLast?_map]
  cases hl : ds.getLast? with
  | none => rfl
  | some Δ =>
    simp only [Option.map_some]
    have hΔ : Δ ∈ ds := List.mem_of_getLast? hl
    have hinj : ∀ d ∈ ds, (d.map (jN a) == Δ.map (jN a)) = (d == Δ) := by
      intro d hd
      have hmapinj : d.map (jN a) = Δ.map (jN a) ↔ d = Δ := by
        constructor
        · intro h
          refine List.ext_getElem (by simpa using congrArg List.length h) (fun i h1 h2 => ?_)
          have := congrArg (fun l => l[i]?) h
          simp only [List.getElem?_map] at this
          rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
          simp only [Option.map_some, Option.some.injEq] at this
          exact jN_inj ha h0 (hds d hd _ (List.getElem_mem h1)) (hds Δ hΔ _ (List.getElem_mem h2))
            this
        · rintro rfl; rfl
      by_cases h : d = Δ
      · simp [h]
      · have : ¬ d.map (jN a) = Δ.map (jN a) := fun e => h (hmapinj.mp e)
        simp [h, this]
    rw [← List.map_reverse, dropWhile_map_congr (P := fun d => d == Δ), List.length_map]
    intro d hd
    exact hinj d (List.mem_reverse.mp hd)

theorem addS_single_lt {y0 : WP} {ys : List WP} (h : cmpP a y0 = .lt) :
    addS [a] (y0 :: ys) = y0 :: ys := by
  simp [addS, h]

theorem addS_single_nlt {y0 : WP} {ys : List WP} (h : cmpP a y0 ≠ .lt) :
    addS [a] (y0 :: ys) = a :: y0 :: ys := by
  simp [addS, h]

theorem domA_om (k : ℕ) : DomA a (.th (k + 1) []) :=
  ⟨nfp_th_nil _, fun z hz => by
    rw [starP_th, if_neg (by omega), if_neg (by omega)] at hz; simp at hz⟩

theorem isEpsLevel_jN_gen (k : ℕ) (q : WP) :
    isEpsLevel (jN a q) (k + 1) = isEpsLevel q (k + 2) := by
  obtain ⟨m, b⟩ := q
  rcases m with _ | _ | m
  · rw [jN_zero]; simp [isEpsLevel]
  · have hl : (jN a (.th 1 b)).lvl = 0 := by rw [jN_lvl h0]; rfl
    have e1 : isEpsLevel (jN a (.th 1 b)) (k + 1) = false := by
      simp [isEpsLevel, hl]
    rw [e1]; simp [isEpsLevel]
  · rw [jN_add_two, jNL_eq_map]
    cases b with
    | nil => simp [isEpsLevel]
    | cons q l =>
      simp only [isEpsLevel, WP.lvl_th, WP.arg_th, List.map_cons, jN_lvl h0]
      by_cases h : m = k
      · subst h; simp; omega
      · have : (m == k) = false := by simp [h]
        simp [this]

theorem isEpsLevel_jN_one {b : List WP} (hb : b ≠ []) (hbn : NFS b) :
    isEpsLevel (jN a (.th 1 b)) 0 = isEpsLevel (.th 1 b) 1 := by
  have hb' : ¬ b.isEmpty = true := by simpa using hb
  obtain ⟨q, l, rfl⟩ := List.exists_cons_of_ne_nil hb
  rw [jN_one, jNTop, if_neg hb', jNL_eq_map]
  by_cases h2 : 2 ≤ q.lvl
  · have hne : ¬ ((q :: l).takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty = true := by
      simp [h2]
    rw [if_neg hne]
    have hq1 : 1 ≤ (jN a q).lvl := by rw [jN_lvl h0]; omega
    have hlen : ((q :: l).takeWhile (fun q => decide (2 ≤ q.lvl))).length =
        (l.takeWhile (fun q => decide (2 ≤ q.lvl))).length + 1 := by simp [h2]
    split_ifs
    · rw [hlen]; simp [isEpsLevel, hq1, h2]
    · simp [isEpsLevel, hq1, h2]
  · have he : ((q :: l).takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty = true := by
      simp [h2]
    rw [if_pos he]
    have e2 : isEpsLevel (.th 1 (q :: l)) 1 = false := by simp [isEpsLevel]; omega
    rw [e2]
    have hall : ∀ v ∈ q :: l, v.lvl ≤ 1 := NFS.lvl_le_of_head hbn (by omega)
    generalize hL : (if (q :: l).head? = some TR.one then ((q :: l).map (jN a)).drop 1
      else (q :: l).map (jN a)) = L
    have hLl : ∀ z ∈ L, z.lvl = 0 := by
      intro z hz
      rw [← hL] at hz
      have hzq : z ∈ (q :: l).map (jN a) := by
        split_ifs at hz
        · exact List.mem_of_mem_drop hz
        · exact hz
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hzq
      rw [jN_lvl h0]; have := hall v hv; omega
    cases L with
    | nil => simp [addS, isEpsLevel, h0]
    | cons y0 ys =>
      have hy0 := hLl y0 (by simp)
      by_cases hc : cmpP a y0 = .lt
      · rw [addS_single_lt ha h0 hc]; simp [isEpsLevel, hy0]
      · rw [addS_single_nlt ha h0 hc]; simp [isEpsLevel, h0]

theorem isEpsPlusN_jN (k : ℕ) {x : List WP} (hx : ∀ p ∈ x, DomA a p) (ha1 : a ≠ TR.one) :
    isEpsPlusN (x.map (jN a)) (k + 1) = isEpsPlusN x (k + 2) := by
  cases x with
  | nil => rfl
  | cons p r =>
    simp only [List.map_cons, isEpsPlusN, isEpsLevel_jN_gen ha h0]
    congr 1
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro h q hq
      have := h (jN a q) (List.mem_map_of_mem hq)
      simp only [beq_iff_eq] at this ⊢
      exact (jN_eq_one ha h0 (hx q (by simp [hq])) ha1).mp this
    · intro h z hz
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      have := h q hq
      simp only [beq_iff_eq] at this ⊢
      rw [this, jN_one_eq]

theorem jN_eq_om {p : WP} (k : ℕ) : jN a p = .th (k + 1) [] ↔ p = .th (k + 2) [] := by
  constructor
  · intro h
    obtain ⟨m, b⟩ := p
    rcases m with _ | _ | m
    · rw [jN_zero] at h; simp at h
    · have hl : (jN a (.th 1 b)).lvl = 0 := by rw [jN_lvl h0]; rfl
      rw [h] at hl; simp at hl
    · rw [jN_add_two, jNL_eq_map] at h
      simp only [WP.th.injEq, List.map_eq_nil_iff] at h
      rw [h.2, show m = k by omega]
  · rintro rfl; rw [jN_add_two]; simp [jNL_eq_map]

/-- **ι-exp** at levels `≥ 2`: `jN(ω^Z) = ω^{jN(Z)}`, one level lower. -/
theorem omegaExp_jN_high (k : ℕ) {Z : List WP} (hZ : ∀ p ∈ Z, DomA a p) (ha1 : a ≠ TR.one) :
    jN a (omegaExp Z (k + 2)) = omegaExp (Z.map (jN a)) (k + 1) := by
  cases Z with
  | nil => simp [omegaExp, jN_add_two, jNL_eq_map]
  | cons p r =>
    have hpe := isEpsLevel_jN_gen ha h0 k p
    have hpn := isEpsPlusN_jN ha h0 k hZ ha1
    simp only [List.map_cons] at hpn ⊢
    have hom := jN_eq_om ha h0 (p := p) k
    have hr : (r.map (jN a) = []) ↔ r = [] := List.map_eq_nil_iff
    rw [omegaExp_cons, omegaExp_cons]
    by_cases hA : r = [] ∧ isEpsLevel p (k + 2) = true
    · rw [if_pos hA, if_pos ⟨hr.mpr hA.1, by rw [hpe]; exact hA.2⟩]
    have hA' : ¬ (r.map (jN a) = [] ∧ isEpsLevel (jN a p) (k + 1) = true) :=
      fun h => hA ⟨hr.mp h.1, by rw [← hpe]; exact h.2⟩
    rw [if_neg hA, if_neg hA']
    by_cases hB : r ≠ [] ∧ isEpsPlusN (p :: r) (k + 2) = true
    · have hB' : r.map (jN a) ≠ [] ∧ isEpsPlusN (jN a p :: r.map (jN a)) (k + 1) = true :=
        ⟨fun h => hB.1 (hr.mp h), by rw [hpn]; exact hB.2⟩
      rw [if_pos hB, if_pos hB', jN_add_two, jNL_eq_map, List.map_dropLast, List.map_cons]
    have hB' : ¬ (r.map (jN a) ≠ [] ∧ isEpsPlusN (jN a p :: r.map (jN a)) (k + 1) = true) :=
      fun h => hB ⟨fun h' => h.1 (hr.mpr h'), by rw [← hpn]; exact h.2⟩
    rw [if_neg hB, if_neg hB']
    by_cases hC : 1 ≤ k + 2 ∧ p = .th (k + 2) []
    · have hC' : 1 ≤ k + 1 ∧ jN a p = .th (k + 1) [] := ⟨by omega, hom.mpr hC.2⟩
      rw [if_pos hC, if_pos hC', jN_add_two, jNL_eq_map]
    have hC' : ¬ (1 ≤ k + 1 ∧ jN a p = .th (k + 1) []) := fun h => hC ⟨by omega, hom.mp h.2⟩
    rw [if_neg hC, if_neg hC', jN_add_two, jNL_eq_map, List.map_cons]

theorem jN_one_cons_low {q : WP} {l : List WP} (hq : q.lvl ≤ 1) (hq1 : q ≠ TR.one) :
    jN a (.th 1 (q :: l)) = .th 0 (addS [a] ((q :: l).map (jN a))) := by
  rw [jN_one, jNTop, jNL_eq_map]
  have h1 : ¬ (q :: l).isEmpty = true := by simp
  have h2 : ((q :: l).takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty = true := by
    simp [List.takeWhile_cons]; omega
  rw [if_neg h1, if_pos h2, if_neg (by simpa using hq1)]

theorem jN_one_cons_one {l : List WP} :
    jN a (.th 1 (TR.one :: l)) = .th 0 (addS [a] (l.map (jN a))) := by
  rw [jN_one, jNTop, jNL_eq_map]
  have h1 : ¬ (TR.one :: l).isEmpty = true := by simp
  have h2 : ((TR.one :: l).takeWhile (fun q => decide (2 ≤ q.lvl))).isEmpty = true := by
    simp [List.takeWhile_cons, TR.one]
  rw [if_neg h1, if_pos h2, if_pos (by simp)]
  rfl

/-- **ι-exp** at level `1`: `jN(ω^Z) = ω^{jN(Z)}` at level `0` (`Ω_1 ↦ α`). -/
theorem omegaExp_jN_one {Z : List WP} (hZ : ∀ p ∈ Z, DomA a p) (hZn : NFS Z)
    (hl : ∀ q ∈ Z, q.lvl ≤ 1) (hΩ : Om 1 ≤ WP.valS Z) (ha1 : a ≠ TR.one)
    (hae : isEpsLevel a 0 = true) :
    jN a (omegaExp Z 1) = omegaExp (Z.map (jN a)) 0 := by
  cases Z with
  | nil => simp at hΩ; exact absurd hΩ (Om_pos 1).ne'
  | cons p r =>
    have hp1 : p.lvl = 1 := by
      have := hl p (by simp)
      by_contra h
      have hall := NFS.lvl_le_of_head hZn (m := 0) (by omega)
      have := valS_lt_Om hZn hall
      exact absurd hΩ (not_le.mpr (by simpa using this))
    have hpD := hZ p (by simp)
    have hrl : ∀ q ∈ r, q.lvl ≤ 1 := fun q hq => hl q (by simp [hq])
    have hrD : ∀ q ∈ r, DomA a q := fun q hq => hZ q (by simp [hq])
    have hrn : NFS r := hZn.of_cons
    have hr0 : ∀ q ∈ r, q.val ≤ p.val := hZn.le_head
    have hr : (r.map (jN a) = []) ↔ r = [] := List.map_eq_nil_iff
    have hones : (∀ q ∈ r, q = TR.one) ↔ (∀ z ∈ r.map (jN a), z = TR.one) := by
      constructor
      · intro h z hz
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
        rw [h q hq, jN_one_eq]
      · intro h q hq
        exact (jN_eq_one ha h0 (hrD q hq) ha1).mp (h _ (List.mem_map_of_mem hq))
    have hB0 : ∀ z : WP, isEpsPlusN (z :: r.map (jN a)) 0 = true ↔
        isEpsLevel z 0 = true ∧ ∀ q ∈ r, q = TR.one := fun z => by
      rw [isEpsPlusN_cons, hones]
    obtain ⟨m, b⟩ := p
    simp only [WP.lvl_th] at hp1; subst hp1
    rw [List.map_cons, omegaExp_cons, omegaExp_cons]
    have hnotA0 : isEpsLevel (.th 1 []) 1 = false := by simp [isEpsLevel]
    by_cases hbn : b = []
    · -- `p = Ω_1`
      subst hbn
      rw [if_neg (by simp [hnotA0]), if_neg (by rw [isEpsPlusN_cons, hnotA0]; simp),
        if_pos ⟨le_rfl, rfl⟩, jN_one_nil]
      by_cases hre : r = []
      · subst hre; simp [hae, jN_one_nil]
      rw [if_neg (fun h => hre (hr.mp h.1))]
      by_cases hall : ∀ q ∈ r, q = TR.one
      · rw [if_pos ⟨fun h => hre (hr.mp h), (hB0 a).mpr ⟨hae, hall⟩⟩]
        obtain ⟨q0, r', rfl⟩ := List.exists_cons_of_ne_nil hre
        rw [hall q0 (by simp), jN_one_cons_one ha h0]
        have hall' : ∀ z ∈ TR.one :: r', z = TR.one := by
          intro z hz
          rcases List.mem_cons.mp hz with h | h
          · exact h
          · exact hall z (List.mem_cons_of_mem _ h)
        have hr' : r'.map (jN a) = r' := by
          conv_rhs => rw [← List.map_id r']
          exact List.map_congr_left (fun q hq => by rw [hall' q (by simp [hq]), jN_one_eq]; rfl)
        have ht : (TR.one :: r').dropLast = r' := (tail_eq_dropLast_of_all hall').symm
        rw [List.map_cons, jN_one_eq, hr', List.dropLast_cons_of_ne_nil (by simp), ht]
        cases r' with
        | nil => simp [addS]
        | cons r0 r'' =>
          rw [addS_single_nlt ha h0]
          rw [hall' r0 (by simp), cmpP_eq ha nfp_one, val_one]
          simp only [ne_eq, compare_lt_iff_lt, not_lt]; exact one_le_val ha
      · rw [if_neg (fun h => hall ((hB0 a).mp h.2).2), if_neg (by omega)]
        obtain ⟨q0, r', rfl⟩ := List.exists_cons_of_ne_nil hre
        have hq0l := hrl q0 (by simp)
        have hq01 : q0 ≠ TR.one := by
          rintro rfl
          apply hall
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · rfl
          · have hle := hrn.le_head q hq
            exact eq_of_val_eq (hrn.1 q (by simp [hq])) nfp_one
              (le_antisymm hle (by rw [val_one]; exact one_le_val (hrn.1 q (by simp [hq]))))
        rw [jN_one_cons_low ha h0 hq0l hq01, List.map_cons, addS_single_nlt ha h0]
        -- `cmpP a (jN q0) ≠ lt`: `q0 = Ω_1` or a constant
        have hq0D := hrD q0 (by simp)
        rw [cmpP_eq ha (nfp_jN ha h0 hq0D)]
        simp only [ne_eq, compare_lt_iff_lt, not_lt]
        rcases Nat.lt_or_ge q0.lvl 1 with hlv | hlv
        · obtain ⟨k0, c0⟩ := q0
          simp only [WP.lvl_th] at hlv
          have : k0 = 0 := by omega
          subst this
          rw [jN_zero]
          exact (hq0D.2 _ (by rw [starP_th]; simp)).le
        · have hq0v : q0.val ≤ (WP.th 1 []).val := hr0 q0 (by simp)
          have hq0om : q0 = .th 1 [] := by
            refine eq_of_val_eq hq0D.1 (nfp_th_nil 1) (le_antisymm hq0v ?_)
            rw [WP.val_th, WP.valS_nil, vartheta_zero]
            exact Om_le_val_of_le_lvl hq0D.1 hlv
          rw [hq0om, jN_one_nil]
    · -- `p = ϑ_1(b)`, `b ≠ 0`
      have hpe := isEpsLevel_jN_one ha h0 hbn hpD.1.nfs
      have hlt : cmpP a (jN a (.th 1 b)) = .lt := by
        rw [cmpP_lt_iff ha (nfp_jN ha h0 hpD)]
        exact (g1 ha h0 hpD).2.2 rfl (by simpa using hbn)
      have hpn1 : WP.th 1 b ≠ TR.one := by simp [TR.one]
      by_cases hA : r = [] ∧ isEpsLevel (.th 1 b) 1 = true
      · rw [if_pos hA, if_pos ⟨hr.mpr hA.1, by rw [hpe]; exact hA.2⟩]
      have hA' : ¬ (r.map (jN a) = [] ∧ isEpsLevel (jN a (.th 1 b)) 0 = true) :=
        fun h => hA ⟨hr.mp h.1, by rw [← hpe]; exact h.2⟩
      rw [if_neg hA, if_neg hA']
      by_cases hB : r ≠ [] ∧ isEpsPlusN (.th 1 b :: r) 1 = true
      · have hB0' := isEpsPlusN_cons.mp hB.2
        have hB' : r.map (jN a) ≠ [] ∧ isEpsPlusN (jN a (.th 1 b) :: r.map (jN a)) 0 = true :=
          ⟨fun h => hB.1 (hr.mp h), (hB0 _).mpr ⟨by rw [hpe]; exact hB0'.1, hB0'.2⟩⟩
        rw [if_pos hB, if_pos hB']
        rw [List.dropLast_cons_of_ne_nil hB.1, jN_one_cons_low ha h0 (by simp) hpn1,
          List.map_cons, addS_single_lt ha h0 hlt,
          List.dropLast_cons_of_ne_nil (fun h => hB.1 (hr.mp h)), List.map_dropLast]
      have hB' : ¬ (r.map (jN a) ≠ [] ∧ isEpsPlusN (jN a (.th 1 b) :: r.map (jN a)) 0 = true) :=
        fun h => hB ⟨fun h' => h.1 (hr.mpr h'),
          isEpsPlusN_cons.mpr ⟨by rw [← hpe]; exact ((hB0 _).mp h.2).1, ((hB0 _).mp h.2).2⟩⟩
      have hC : ¬ (1 ≤ 1 ∧ WP.th 1 b = WP.th 1 []) := fun h => hbn (by simpa using h.2)
      have hC' : ¬ (1 ≤ 0 ∧ jN a (.th 1 b) = WP.th 0 []) := fun h => by omega
      rw [if_neg hB, if_neg hB', if_neg hC, if_neg hC',
        jN_one_cons_low ha h0 (by simp) hpn1, List.map_cons, addS_single_lt ha h0 hlt]

/-- **ι-exp** for `log_ω` at levels `≥ 2`. -/
theorem logOmega_jN_high (k : ℕ) {c : List WP} (hc : ∀ q ∈ c, DomA a q) (ha1 : a ≠ TR.one) :
    logOmega (jN a (.th (k + 2) c)) = (logOmega (.th (k + 2) c)).map (jN a) := by
  have hpe := isEpsLevel_jN_gen ha h0 k (.th (k + 2) c)
  have hpn := isEpsPlusN_jN ha h0 k hc ha1
  rw [jN_add_two, jNL_eq_map] at hpe ⊢
  simp only [logOmega, WP.lvl_th, WP.arg_th]
  rw [hpe, hpn]
  split_ifs with h1 h2 h3
  · simp [jN_add_two, jNL_eq_map]
  · simp [jN_one_eq]
  · exact absurd h3 (by simp)
  · have := addS_jN ha h0 (x := [.th (k + 2) []]) (y := c)
      (by simpa using domA_om ha h0 (k + 1)) hc
    rw [← this]
    simp [jN_add_two, jNL_eq_map]

end Comm

end Googology.Trans.PSS.Main
