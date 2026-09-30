import Googology.Trans.BMS.PoR.PSS.TR.Basic

/-!
# Sums, powers of `ω`, and the images of `𝒯` are terms of `T¹`

* `addS_spec`, `addAll_spec`: the sum with absorption of `tr.py` is a sum of
  `T¹`, with the ordinal sum as value.
* `omegaExp_spec`: `ω^x` at level `m` is a principal term of `T¹` of level `m`
  with value `ω^{val x}` (from (Exp) and (E)).
* `logOmega_spec`: `ω^{val (log_ω p)} = val p`.
* `splitLevel_spec`: `x = D + ρ`.
* `trF_nf`: **every image `𝒯_{y(s)}(s)` is a principal term of `T¹` of level
  `y(s)`**, for every term `s` and fuel.
-/

namespace Googology.Trans.PSS.TR

open Ordinal Order Forest

/-! ## Lists -/

theorem mem_dropWhile_of_upward {α : Type*} {P : α → Bool} :
    ∀ {l : List α}, l.Pairwise (fun a b => P a = true → P b = true) →
      ∀ b ∈ l.dropWhile (fun a => !P a), P b = true
  | [], _, b, hb => by simp at hb
  | a :: l, h, b, hb => by
    rw [List.pairwise_cons] at h
    by_cases ha : P a = true
    · rw [List.dropWhile_cons_of_neg (by simp [ha])] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact h.1 b hb ha
    · rw [List.dropWhile_cons_of_pos (by simpa using ha)] at hb
      exact mem_dropWhile_of_upward h.2 b hb

theorem NFS.append_iff {x y : List WP} :
    NFS (x ++ y) ↔ NFS x ∧ NFS y ∧ ∀ p ∈ x, ∀ q ∈ y, q.val ≤ p.val := by
  unfold NFS
  rw [List.pairwise_append]
  simp only [List.mem_append]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨fun p hp => h1 p (Or.inl hp), h2⟩, ⟨fun p hp => h1 p (Or.inr hp), h3⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨fun p hp => hp.elim (h1 p) (h3 p), h2, h4, h5⟩

theorem NFS.sublist {x y : List WP} (hy : NFS y) (h : x.Sublist y) : NFS x :=
  ⟨fun p hp => hy.1 p (h.subset hp), hy.2.sublist h⟩

theorem NFS.takeWhile {x : List WP} (hx : NFS x) (P : WP → Bool) : NFS (x.takeWhile P) :=
  hx.sublist (List.takeWhile_sublist _)

theorem NFS.dropWhile {x : List WP} (hx : NFS x) (P : WP → Bool) : NFS (x.dropWhile P) :=
  hx.sublist (List.dropWhile_sublist _)

theorem NFS.dropLast {x : List WP} (hx : NFS x) : NFS x.dropLast :=
  hx.sublist (List.dropLast_sublist _)

theorem NFS.tail {x : List WP} (hx : NFS x) : NFS x.tail :=
  hx.sublist (List.tail_sublist _)

theorem head_dropWhile_false {α : Type*} {P : α → Bool} :
    ∀ {l : List α} {p : α} {r : List α}, l.dropWhile P = p :: r → P p = false
  | [], _, _, h => by simp at h
  | a :: l, p, r, h => by
    by_cases ha : P a = true
    · rw [List.dropWhile_cons_of_pos ha] at h
      exact head_dropWhile_false h
    · rw [List.dropWhile_cons_of_neg ha] at h
      cases h
      simpa using ha

theorem nfp_th {m : ℕ} {a : List WP} (ha : NFS a) (hl : ∀ q ∈ a, q.lvl ≤ m + 1) :
    NFP (.th m a) :=
  NFP.th ha.1 hl ha.2

/-! ## The sum with absorption -/

theorem mem_addS {x y : List WP} {q : WP} (h : q ∈ addS x y) : q ∈ x ∨ q ∈ y := by
  cases y with
  | nil => exact Or.inl h
  | cons y0 y' =>
    rw [addS, List.mem_append, List.mem_reverse] at h
    rcases h with h | h
    · exact Or.inl (List.mem_reverse.mp ((List.dropWhile_sublist _).subset h))
    · exact Or.inr h

/-- **The sum with absorption is the ordinal sum** (on sums of `T¹`). -/
theorem addS_spec {x y : List WP} (hx : NFS x) (hy : NFS y) :
    NFS (addS x y) ∧ WP.valS (addS x y) = WP.valS x + WP.valS y := by
  cases y with
  | nil => exact ⟨hx, by simp [addS]⟩
  | cons y0 y' =>
    set P : WP → Bool := fun p => cmpP p y0 == .lt with hP
    have hPv : ∀ p ∈ x, (P p = true ↔ p.val < y0.val) := fun p hp => by
      simp only [hP, beq_iff_eq]
      exact cmpP_lt_iff (hx.1 p hp) hy.head
    have hup : x.Pairwise (fun a b => P a = true → P b = true) := by
      refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab hPa => ?_) hx.2
      exact (hPv b hb).mpr (lt_of_le_of_lt hab ((hPv a ha).mp hPa))
    have hadd : addS x (y0 :: y') = x.takeWhile (fun a => !P a) ++ y0 :: y' := by
      rw [addS, Phi.reverse_dropWhile_reverse P hup]
    have hsplit := List.takeWhile_append_dropWhile (p := fun a => !P a) (l := x)
    set T := x.takeWhile (fun a => !P a)
    set D := x.dropWhile (fun a => !P a)
    have hD : ∀ q ∈ D, q.val < y0.val := fun q hq =>
      (hPv q ((List.dropWhile_sublist _).subset hq)).mp (mem_dropWhile_of_upward hup q hq)
    have hT : ∀ q ∈ T, y0.val ≤ q.val := fun q hq => by
      have h1 := List.mem_takeWhile_imp hq
      have hnp : ¬ (P q = true) := by simpa using h1
      exact not_lt.mp (fun h => hnp ((hPv q ((List.takeWhile_sublist _).subset hq)).mpr h))
    rw [hadd]
    refine ⟨NFS.append_iff.mpr ⟨hx.takeWhile _, hy, fun p hp q hq => ?_⟩, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hT p hp
      · exact le_trans (hy.le_head q hq) (hT p hp)
    · have hxv : WP.valS x = WP.valS T + WP.valS D := by
        rw [← valS_append, hsplit]
      have hDv : WP.valS D + y0.val = y0.val :=
        (val_isPrincipal hy.head).add_eq_right
          (valS_lt_of_forall (val_isPrincipal hy.head) (val_pos hy.head) hD)
      rw [valS_append, hxv, WP.valS_cons, add_assoc, ← add_assoc (WP.valS D), hDv]

theorem mem_addAll_foldl : ∀ (xs : List (List WP)) (r : List WP) {q : WP},
    q ∈ xs.foldl addS r → q ∈ r ∨ ∃ x ∈ xs, q ∈ x
  | [], r, q, h => Or.inl h
  | x :: xs, r, q, h => by
    rw [List.foldl_cons] at h
    rcases mem_addAll_foldl xs _ h with h | ⟨x', hx', hq⟩
    · rcases mem_addS h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨x, by simp, h⟩
    · exact Or.inr ⟨x', by simp [hx'], hq⟩

theorem mem_addAll {xs : List (List WP)} {q : WP} (h : q ∈ addAll xs) : ∃ x ∈ xs, q ∈ x := by
  rcases mem_addAll_foldl xs [] h with h | h
  · simp at h
  · exact h

theorem addAll_foldl_spec : ∀ (xs : List (List WP)) {r : List WP}, NFS r → (∀ x ∈ xs, NFS x) →
    NFS (xs.foldl addS r) ∧ WP.valS (xs.foldl addS r) = WP.valS r + (xs.map WP.valS).sum
  | [], r, hr, _ => ⟨hr, by simp⟩
  | x :: xs, r, hr, hxs => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := addS_spec hr (hxs x (by simp))
    obtain ⟨h3, h4⟩ := addAll_foldl_spec xs h1 (fun x' hx' => hxs x' (by simp [hx']))
    refine ⟨h3, ?_⟩
    rw [h4, h2, List.map_cons, List.sum_cons, add_assoc]

/-- **`addAll` is the ordinal sum.** -/
theorem addAll_spec {xs : List (List WP)} (hxs : ∀ x ∈ xs, NFS x) :
    NFS (addAll xs) ∧ WP.valS (addAll xs) = (xs.map WP.valS).sum := by
  obtain ⟨h1, h2⟩ := addAll_foldl_spec xs NFS.nil hxs
  exact ⟨h1, by rw [addAll, h2, WP.valS_nil, zero_add]⟩

/-! ## Levels of sums -/

/-- A sum of `T¹` whose value is at least `Ω_m` has a first summand of level
`≥ m`. -/
theorem NFS.head_lvl_ge {x : List WP} (hx : NFS x) {m : ℕ} (h : Om m ≤ WP.valS x) :
    ∃ p r, x = p :: r ∧ m ≤ p.lvl := by
  cases x with
  | nil =>
    rw [WP.valS_nil] at h
    exact absurd (Om_pos m) (not_lt.mpr h)
  | cons p r =>
    refine ⟨p, r, rfl, ?_⟩
    by_contra hlt
    cases m with
    | zero => omega
    | succ m =>
      exact absurd h (not_le.mpr (valS_lt_Om hx (hx.lvl_le_of_head (by omega))))

/-- The value of a principal term of level `m` is at least `Ω_m`, so a sum
containing one is too. -/
theorem Om_le_valS_of_mem {x : List WP} (hx : NFS x) {p : WP} (hp : p ∈ x) {m : ℕ}
    (hm : m ≤ p.lvl) : Om m ≤ WP.valS x := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hp
  rw [valS_append, WP.valS_cons]
  exact le_trans (Om_le_val_of_le_lvl (hx.1 p hp) hm) (le_trans le_self_add le_add_self)

/-! ## `ω^x` -/

theorem isEpsLevel_iff {p : WP} {m : ℕ} :
    isEpsLevel p m = true ↔ p.lvl = m ∧ ∃ q ∈ p.arg.head?, m + 1 ≤ q.lvl := by
  obtain ⟨k, a⟩ := p
  cases a with
  | nil => simp [isEpsLevel]
  | cons q a => simp [isEpsLevel]

theorem eps_val {p : WP} (hp : NFP p) (h : isEpsLevel p p.lvl = true) :
    Om p.lvl < p.val ∧ ω ^ p.val = p.val := by
  obtain ⟨k, a⟩ := p
  exact (eps_iff hp).mp (isEpsLevel_iff.mp h).2

theorem isEpsPlusN_cons {p : WP} {r : List WP} {m : ℕ} :
    isEpsPlusN (p :: r) m = true ↔ isEpsLevel p m = true ∧ ∀ q ∈ r, q = one := by
  simp [isEpsPlusN]

/-- `ω^x` at level `m`: for a sum `x` of `T¹` with summands of level `≤ m`, and
`x ≥ Ω_m` when `m ≥ 1`. -/
theorem omegaExp_spec {x : List WP} {m : ℕ} (hx : NFS x) (hl : ∀ q ∈ x, q.lvl ≤ m)
    (hm : 1 ≤ m → Om m ≤ WP.valS x) :
    NFP (omegaExp x m) ∧ (omegaExp x m).lvl = m ∧ (omegaExp x m).val = ω ^ WP.valS x := by
  cases x with
  | nil =>
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · refine ⟨nfp_th_nil 0, rfl, ?_⟩
      rw [omegaExp, WP.val_th, WP.valS_nil, vartheta_zero, Om_zero, opow_zero]
    · exact absurd (hm hpos) (by rw [WP.valS_nil]; exact not_le.mpr (Om_pos m))
  | cons p r =>
    have hlm : ∀ q ∈ p :: r, q.lvl ≤ m + 1 := fun q hq => le_trans (hl q hq) (Nat.le_succ m)
    rw [omegaExp]
    split_ifs with h1 h2 h3
    · -- `x = ε`
      obtain ⟨rfl, he⟩ := h1
      have hlv := (isEpsLevel_iff.mp he).1
      refine ⟨hx.head, hlv, ?_⟩
      rw [valS_single, (eps_val hx.head (hlv ▸ he)).2]
    · -- `x = ε + n`, `n ≥ 1`
      obtain ⟨hr, he⟩ := h2
      obtain ⟨he1, hones⟩ := isEpsPlusN_cons.mp he
      have hlast : (p :: r).getLast (by simp) = one := by
        rw [List.getLast_cons hr]
        exact hones _ (List.getLast_mem hr)
      have hsplit : p :: r = (p :: r).dropLast ++ [one] := by
        conv_lhs => rw [← List.dropLast_append_getLast (l := p :: r) (by simp)]
        rw [hlast]
      have hd : (p :: r).dropLast = p :: r.dropLast := List.dropLast_cons_of_ne_nil hr
      have hnd : NFS (p :: r).dropLast := hx.dropLast
      have hepd : isEpsPlusN (p :: r).dropLast m = true := by
        rw [hd, isEpsPlusN_cons]
        exact ⟨he1, fun q hq => hones q (List.dropLast_subset _ hq)⟩
      have hnf : NFP (.th m (p :: r).dropLast) :=
        nfp_th hnd (fun q hq => hlm q (List.dropLast_subset _ hq))
      refine ⟨hnf, rfl, ?_⟩
      rw [val_exp_eps hnf hepd]
      conv_rhs => rw [hsplit, valS_append, valS_single, val_one]
    · -- `x = Ω_m + r`
      obtain ⟨hm1, rfl⟩ := h3
      have hr : NFS r := hx.of_cons
      have hnf : NFP (.th m r) := nfp_th hr (fun q hq => hlm q (by simp [hq]))
      have hne : isEpsPlusN r m = false := by
        cases r with
        | nil => rfl
        | cons q r' =>
          by_contra hc
          rw [Bool.not_eq_false, isEpsPlusN_cons] at hc
          have hq : NFP q := hr.head
          have hql := (isEpsLevel_iff.mp hc.1).1
          have := (eps_val hq (hql ▸ hc.1)).1
          rw [hql] at this
          have hle := hx.le_head q (by simp)
          rw [WP.val_th, WP.valS_nil, vartheta_zero] at hle
          exact absurd hle (not_le.mpr this)
      refine ⟨hnf, rfl, ?_⟩
      rw [val_exp hnf (fun q hq => hl q (by simp [hq])) hne, expBase,
        if_neg (by omega), WP.valS_cons, WP.val_th, WP.valS_nil, vartheta_zero]
    · -- the general case `ϑ_m(x)` (`ϑ_m(-Ω_m + x)` with `-Ω_m + x = x`)
      have hnf : NFP (.th m (p :: r)) := nfp_th hx hlm
      have hne : isEpsPlusN (p :: r) m = false := by
        by_contra hc
        rw [Bool.not_eq_false] at hc
        rcases eq_or_ne r [] with hr | hr
        · exact h1 ⟨hr, (isEpsPlusN_cons.mp hc).1⟩
        · exact h2 ⟨hr, hc⟩
      refine ⟨hnf, rfl, ?_⟩
      rw [val_exp hnf hl hne, expBase]
      split_ifs with hm0
      · rw [zero_add]
      · congr 1
        have hpos : 1 ≤ m := by omega
        obtain ⟨p', r', he, hp'⟩ := hx.head_lvl_ge (hm hpos)
        cases he
        have hpm : p.lvl = m := le_antisymm (hl p (by simp)) hp'
        have hpv : Om m < p.val := by
          refine lt_of_le_of_ne (Om_le_val_of_le_lvl hx.head hpm.ge) (fun e => ?_)
          have : p = .th m [] := eq_of_val_eq hx.head (nfp_th_nil m)
            (by rw [← e, WP.val_th, WP.valS_nil, vartheta_zero])
          exact h3 ⟨hpos, this⟩
        rw [WP.valS_cons, ← add_assoc, (val_isPrincipal hx.head).add_eq_right hpv]

/-! ## `log_ω` -/

/-- The argument of a principal term of `T¹` that is not an epsilon number of its
level has summands of level `≤` its level. -/
theorem arg_lvl_le_of_not_eps {m : ℕ} {a : List WP} (h : NFP (.th m a))
    (he : isEpsLevel (.th m a) m = false) : ∀ q ∈ a, q.lvl ≤ m := by
  cases a with
  | nil => simp
  | cons q a =>
    have hq : q.lvl ≤ m := by
      by_contra hc
      have : isEpsLevel (.th m (q :: a)) m = true :=
        isEpsLevel_iff.mpr ⟨rfl, q, by simp, by omega⟩
      rw [this] at he; exact Bool.noConfusion he
    exact h.nfs.lvl_le_of_head hq

/-- **`log_ω`**: `ω^{log_ω p} = p`; the summands have level `≤` that of `p`. -/
theorem logOmega_spec {p : WP} (hp : NFP p) :
    NFS (logOmega p) ∧ ω ^ WP.valS (logOmega p) = p.val ∧ ∀ q ∈ logOmega p, q.lvl ≤ p.lvl := by
  obtain ⟨m, a⟩ := p
  simp only [logOmega, WP.lvl_th, WP.arg_th]
  split_ifs with h1 h2 h3
  · refine ⟨NFS.single hp, ?_, by simp⟩
    rw [valS_single]
    exact (eps_val hp (by simpa using h1)).2
  · obtain ⟨q, r, rfl⟩ : ∃ q r, a = q :: r := by
      cases a with
      | nil => simp [isEpsPlusN] at h2
      | cons q r => exact ⟨q, r, rfl⟩
    obtain ⟨he1, hones⟩ := isEpsPlusN_cons.mp h2
    have hnfs : NFS (q :: r ++ [one]) := by
      refine NFS.append_iff.mpr ⟨hp.nfs, NFS.single nfp_one, fun p' hp' q' hq' => ?_⟩
      rw [List.mem_singleton.mp hq', val_one]
      exact one_le_val (hp.nfs.1 p' hp')
    refine ⟨hnfs, ?_, ?_⟩
    · rw [val_exp_eps hp h2, valS_append, valS_single, val_one]
    · intro p' hp'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with (rfl | hp') | rfl
      · exact le_of_eq (isEpsLevel_iff.mp he1).1
      · rw [hones p' hp']; simp [one]
      · simp [one]
  · subst h3
    have hl := arg_lvl_le_of_not_eps hp (by simpa using h1)
    refine ⟨hp.nfs, ?_, hl⟩
    rw [val_exp hp hl (by simpa using h2), expBase, if_pos rfl, zero_add]
  · have hl := arg_lvl_le_of_not_eps hp (by simpa using h1)
    obtain ⟨hn, hv⟩ := addS_spec (NFS.single (nfp_th_nil m)) hp.nfs
    refine ⟨hn, ?_, fun q hq => ?_⟩
    · rw [hv, val_exp hp hl (by simpa using h2), expBase, if_neg h3, valS_single, WP.val_th,
        WP.valS_nil, vartheta_zero]
    · rcases mem_addS hq with hq | hq
      · rw [List.mem_singleton.mp hq]; simp
      · exact hl q hq

/-! ## `D + ρ` -/

theorem splitLevel_spec {x : List WP} (hx : NFS x) (m : ℕ) :
    x = (splitLevel x m).1 ++ (splitLevel x m).2 ∧ NFS (splitLevel x m).1 ∧
      NFS (splitLevel x m).2 ∧ (∀ q ∈ (splitLevel x m).1, m ≤ q.lvl) ∧
      ∀ q ∈ (splitLevel x m).2, q.lvl < m := by
  simp only [splitLevel]
  refine ⟨(List.takeWhile_append_dropWhile).symm, hx.takeWhile _, hx.dropWhile _,
    fun q hq => by simpa using List.mem_takeWhile_imp hq, ?_⟩
  intro q hq
  -- the first summand of the rest has level `< m`, and the others are smaller
  set P : WP → Bool := fun p => decide (m ≤ p.lvl)
  have hnd := hx.dropWhile P
  cases e : x.dropWhile P with
  | nil => rw [e] at hq; simp at hq
  | cons p r =>
    have hp : ¬ m ≤ p.lvl := by
      have := head_dropWhile_false e
      simpa [P] using this
    rw [e] at hq hnd
    exact lt_of_le_of_lt (hnd.lvl_le_of_head (le_refl p.lvl) q hq) (by omega)

/-! ## The images of `𝒯` are terms of `T¹` -/

theorem minusOnePlus_sublist (x : List WP) : (minusOnePlus x).Sublist x := by
  cases x with
  | nil => exact List.Sublist.slnil
  | cons p r =>
    simp only [minusOnePlus]
    split_ifs
    · exact List.sublist_cons_self p r
    · exact List.Sublist.refl _

/-- `ω^ρ` at the level of the first summand of `ρ`. -/
theorem omegaExp_expLvl_spec {ρ : List WP} (hρ : NFS ρ) :
    NFP (omegaExp ρ (expLvl ρ)) ∧ (omegaExp ρ (expLvl ρ)).lvl = expLvl ρ ∧
      (omegaExp ρ (expLvl ρ)).val = ω ^ WP.valS ρ := by
  refine omegaExp_spec hρ ?_ ?_
  · cases ρ with
    | nil => simp
    | cons q r => exact hρ.lvl_le_of_head (by simp [expLvl])
  · intro h1
    cases ρ with
    | nil => simp [expLvl] at h1
    | cons q r =>
      exact le_trans (Om_le_val_of_le_lvl hρ.head (by simp [expLvl])) le_valS_head

theorem expLvl_le {ρ : List WP} {k : ℕ} (h : ∀ q ∈ ρ, q.lvl ≤ k) : expLvl ρ ≤ k := by
  cases ρ with
  | nil => simp [expLvl]
  | cons q r => exact h q (by simp)

/-- The epsilon case of `𝒯` gives a principal term of `T¹` of level `k`. -/
theorem epsImg_nf {k : ℕ} {vs : List WP} {pre : ℕ → WP} (hvs : ∀ v ∈ vs, NFP v)
    (hlast : ∀ v ∈ vs.getLast?, v.lvl = k + 1) (hpre : ∀ j, NFP (pre j) ∧ (pre j).lvl = k) :
    NFP (epsImg k vs pre) ∧ (epsImg k vs pre).lvl = k := by
  -- the parts `D_i + ρ_i`
  have hmon : ∀ v, NFP v → NFS (splitLevel (logOmega v) (k + 1)).1 ∧
      NFS (splitLevel (logOmega v) (k + 1)).2 ∧
      (∀ q ∈ (splitLevel (logOmega v) (k + 1)).1, k + 1 ≤ q.lvl ∧ q.lvl ≤ v.lvl) ∧
      ∀ q ∈ (splitLevel (logOmega v) (k + 1)).2, q.lvl ≤ k := by
    intro v hv
    obtain ⟨hl1, hl2, hl3⟩ := logOmega_spec hv
    obtain ⟨h1, h2, h3, h4, h5⟩ := splitLevel_spec hl1 (k + 1)
    refine ⟨h2, h3, fun q hq => ⟨h4 q hq, hl3 q ?_⟩, fun q hq => Nat.lt_succ_iff.mp (h5 q hq)⟩
    rw [h1]; exact List.mem_append_left _ hq
  simp only [epsImg]
  set mons := vs.map (fun v => splitLevel (logOmega v) (k + 1)) with hmons
  set Δ := (mons.getLast?.map Prod.fst).getD [] with hΔ
  set j := runStart (mons.map Prod.fst)
  set c := addAll ((mons.drop j).map (fun m => [omegaExp m.2 (expLvl m.2)])) with hc
  have hmem : ∀ m ∈ mons, NFS m.1 ∧ NFS m.2 ∧ ∀ q ∈ m.2, q.lvl ≤ k := by
    intro m hm
    rw [hmons, List.mem_map] at hm
    obtain ⟨v, hv, rfl⟩ := hm
    obtain ⟨h1, h2, -, h4⟩ := hmon v (hvs v hv)
    exact ⟨h1, h2, h4⟩
  have hΔn : NFS Δ ∧ ∀ q ∈ Δ, q.lvl = k + 1 := by
    rw [hΔ, hmons, List.getLast?_map]
    cases e : vs.getLast? with
    | none => exact ⟨NFS.nil, by simp⟩
    | some v =>
      have hv := List.mem_of_getLast? e
      obtain ⟨h1, -, h3, -⟩ := hmon v (hvs v hv)
      have hvl := hlast v (by simp [e])
      exact ⟨h1, fun q hq => le_antisymm (hvl ▸ (h3 q hq).2) (h3 q hq).1⟩
  have hcn : NFS c ∧ ∀ q ∈ c, q.lvl ≤ k := by
    have hparts : ∀ x ∈ (mons.drop j).map (fun m => [omegaExp m.2 (expLvl m.2)]),
        NFS x ∧ ∀ q ∈ x, q.lvl ≤ k := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨m, hm, rfl⟩ := hx
      obtain ⟨-, h2, h3⟩ := hmem m (List.mem_of_mem_drop hm)
      obtain ⟨e1, e2, -⟩ := omegaExp_expLvl_spec h2
      refine ⟨NFS.single e1, fun q hq => ?_⟩
      rw [List.mem_singleton.mp hq, e2]
      exact expLvl_le h3
    refine ⟨(addAll_spec (fun x hx => (hparts x hx).1)).1, fun q hq => ?_⟩
    obtain ⟨x, hx, hqx⟩ := mem_addAll hq
    exact (hparts x hx).2 q hqx
  have hηn : NFS (minusOnePlus c) ∧ ∀ q ∈ minusOnePlus c, q.lvl ≤ k :=
    ⟨hcn.1.sublist (minusOnePlus_sublist c),
      fun q hq => hcn.2 q ((minusOnePlus_sublist c).subset hq)⟩
  have hη'n : ∀ η' : List WP, (η' = minusOnePlus c ∨ η' = addS [pre j] (minusOnePlus c)) →
      NFS η' ∧ ∀ q ∈ η', q.lvl ≤ k := by
    rintro η' (rfl | rfl)
    · exact hηn
    · refine ⟨(addS_spec (NFS.single (hpre j).1) hηn.1).1, fun q hq => ?_⟩
      rcases mem_addS hq with hq | hq
      · rw [List.mem_singleton.mp hq, (hpre j).2]
      · exact hηn.2 q hq
  have key : ∀ η' : List WP, NFS η' → (∀ q ∈ η', q.lvl ≤ k) →
      NFP (WP.th k (addS Δ η')) := by
    intro η' h1 h2
    refine nfp_th (addS_spec hΔn.1 h1).1 (fun q hq => ?_)
    rcases mem_addS hq with hq | hq
    · exact le_of_eq (hΔn.2 q hq)
    · exact Nat.le_succ_of_le (h2 q hq)
  refine ⟨?_, rfl⟩
  split_ifs with h1 h2
  · exact key _ hηn.1 hηn.2
  · obtain ⟨a, b⟩ := hη'n _ (Or.inr rfl); exact key _ a b
  · exact key _ hηn.1 hηn.2

/-- **Every image `𝒯_{y(s)}(s)` is a principal term of `T¹` of level `y(s)`**, for
every term and every fuel. -/
theorem trF_nf : ∀ (f : ℕ) (s : Tm), NFP (trF f s) ∧ (trF f s).lvl = s.y
  | 0, s => ⟨nfp_th_nil _, rfl⟩
  | f + 1, .node k ch => by
    have IH := trF_nf f
    unfold trF
    split
    · exact ⟨nfp_th_nil _, rfl⟩
    · rename_i last hlast
      by_cases hy : last.y = k + 1
      · rw [if_pos hy]
        refine epsImg_nf (fun v hv => ?_) (fun v hv => ?_) (fun j => IH _)
        · rw [List.mem_map] at hv
          obtain ⟨c, -, rfl⟩ := hv
          exact (IH c).1
        · rw [List.getLast?_map, hlast] at hv
          simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hv
          rw [← hv, (IH last).2, hy]
      · rw [if_neg hy]
        dsimp only
        set hi := ch.filter (fun c => decide (c.y = k + 1))
        set lo := ch.filter (fun c => decide (c.y ≤ k))
        set head : List (List WP) :=
          if hi ≠ [] then [[trF f (.node k hi)]] else if 1 ≤ k then [[.th k []]] else []
          with hhead
        have hheadp : ∀ x ∈ head, ∃ p, x = [p] ∧ NFP p ∧ p.lvl = k := by
          intro x hx
          rw [hhead] at hx
          split_ifs at hx
          · exact ⟨_, List.mem_singleton.mp hx, IH _⟩
          · exact ⟨_, List.mem_singleton.mp hx, nfp_th_nil k, rfl⟩
          · simp at hx
        have hparts : ∀ x ∈ head ++ lo.map (fun c => [trF f c]),
            NFS x ∧ ∀ q ∈ x, q.lvl ≤ k := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨p, rfl, hp, hpl⟩ := hheadp x hx
            exact ⟨NFS.single hp, fun q hq => by rw [List.mem_singleton.mp hq, hpl]⟩
          · rw [List.mem_map] at hx
            obtain ⟨c, hc, rfl⟩ := hx
            refine ⟨NFS.single (IH c).1, fun q hq => ?_⟩
            rw [List.mem_singleton.mp hq, (IH c).2]
            simpa using (List.mem_filter.mp hc).2
        obtain ⟨hZn, hZv⟩ := addAll_spec (fun x hx => (hparts x hx).1)
        have hZl : ∀ q ∈ addAll (head ++ lo.map (fun c => [trF f c])), q.lvl ≤ k := by
          intro q hq
          obtain ⟨x, hx, hqx⟩ := mem_addAll hq
          exact (hparts x hx).2 q hqx
        refine (fun h => ⟨h.1, h.2.1⟩) (omegaExp_spec hZn hZl (fun hk => ?_))
        rw [hZv, List.map_append, List.sum_append]
        refine le_trans ?_ le_self_add
        have hne : head ≠ [] := by
          rw [hhead]; split_ifs <;> simp_all
        obtain ⟨x, xs, hxs⟩ := List.exists_cons_of_ne_nil hne
        obtain ⟨p, rfl, hp, hpl⟩ := hheadp x (by rw [hxs]; simp)
        rw [hxs, List.map_cons, List.sum_cons, valS_single]
        exact le_trans (Om_le_val_of_le_lvl hp hpl.ge) le_self_add

/-- **`𝒯_{y(s)}(s)` is a principal term of `T¹` of level `y(s)`.** -/
theorem trTm_nf (s : Tm) : NFP (trTm s) ∧ (trTm s).lvl = s.y := trF_nf _ s

end Googology.Trans.PSS.TR
