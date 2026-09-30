import Googology.Trans.PSS.Main.SPlus
import Googology.Trans.PSS.Main.FactBar1

/-!
# Theorem FIN: `P_1(α)` is finite, without [W07c]

For a base `σ ∈ {1} ∪ E` and `y < T¹ ∩ Ω_1`, `C^σ(y)` (`InC σ y`) is the least set that
contains `0`, `σ`, `y` and is closed under additive decomposition, `lh` on `(σ, T¹ ∩ Ω_1)`
and bar on the principal elements of `(σ, T¹ ∩ Ω_1)`.  `P_1(α)` (`InP1 α`) is inside
`C^1(α)`.

**Theorem FIN** (`finite_inC`): `C^σ(y)` is finite.  Induction on
`(ht_σ(y), y)`, lexicographic.  In each case a finite set `R ∋ y` closed under the operations
is exhibited:

* `y` not principal, or `y ≤ σ`: the partial sums of `y`, with `C^σ(c)` for its components
  `c > σ` (all `< y`);
* `y > σ` principal, not epsilon, `y = ω^{y'}`: `lh(y) = y + logend(y')` ([W07b] Thm 2.2),
  the sums `y + (partial sum of logend(y'))`, with `C^σ(c)` for the components of
  `logend(y')` and `C^σ(bar y)`;
* `y > σ` epsilon: `D := C^y(lh y)` is finite by the induction hypothesis, since
  `ht_y(lh y) < ht_σ(y)` ([W07b] Lemma 4.5, `htB_lh`); `R` is `{0, σ, y}`, the elements of
  `D` above `y`, and `C^σ(ξ)` for `ξ = bar(y)` and the elements `ξ < y` of `D`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order

/-! ## `bar(α) < α` -/

/-- The principal level-`0` term of an additive principal `y < T¹ ∩ Ω_1`. -/
theorem exists_term_of_pr {y : Ordinal.{0}} (hP : Pr y) (hT : y < T1bound) :
    ∃ p : WP, NFP p ∧ p.lvl = 0 ∧ p.val = y := by
  obtain ⟨u, hu, hus, hu0⟩ := exists_nfs_of_lt_T1bound hT
  have hul : u.map WP.val = [y] :=
    anf_unique (anf_of_nfs hu) (anf_single hP) (by rw [← valS_eq_sum_map, hus]; simp)
  obtain ⟨p, rfl⟩ : ∃ p, u = [p] := by
    rcases u with _ | ⟨p, _ | ⟨p', u⟩⟩
    · simp at hul
    · exact ⟨p, rfl⟩
    · simp at hul
  exact ⟨p, hu.1 p (by simp), hu0 p (by simp), by simpa using hul⟩

/-- **`bar(α) < α`** for additive principal `α ∈ (1, T¹ ∩ Ω_1)` ([CW12] Def 5.1: `ϑ(Δ + η')`
with `η'` a proper initial part of `η`, or `α_{n-1}`). -/
theorem barO_lt {y : Ordinal.{0}} (hP : Pr y) (h1 : 1 < y) (hT : y < T1bound) : barO y < y := by
  obtain ⟨p, hp, hp0, rfl⟩ := exists_term_of_pr hP hT
  rw [barO_eq hp hp0]
  have hloc : (locPred p).val < p.val := by
    rcases locPred_spec hp hp0 h1 with ⟨q, -, hqp, -, e⟩ | ⟨-, e⟩
    · rw [e]; exact hqp
    · rw [e, val_one]; exact h1
  cases hg : (argE p.arg).getLast? with
  | none => rw [barT_none hg]; exact hloc
  | some η0 =>
    by_cases hc : η0 = TR.one ∨ ((argE p.arg).dropLast ≠ [] ∧
        ¬ supPt (argD p.arg) (argE p.arg).dropLast)
    · rw [barT_pos hg hc]
      obtain ⟨m, a⟩ := p
      simp only [WP.lvl_th] at hp0
      subst hp0
      change (argE a).getLast? = some η0 at hg
      have hne : argE a ≠ [] := by intro h; rw [h] at hg; simp at hg
      have hlast : (argE a).getLast hne = η0 := by
        rw [List.getLast?_eq_some_getLast hne] at hg; exact Option.some.inj hg
      have ha : a = (argD a ++ (argE a).dropLast) ++ [η0] := by
        rw [List.append_assoc, ← hlast, List.dropLast_append_getLast hne]
        unfold argD argE; exact List.takeWhile_append_dropWhile.symm
      have hna : NFS a := hp.nfs
      have hη0 : NFP η0 := hna.1 η0 (by rw [ha]; simp)
      have hb : NFP (.th 0 (argD a ++ (argE a).dropLast)) := by
        refine nfp_th (hna.sublist ?_) (fun q hq => ?_)
        · conv_rhs => rw [ha]
          exact List.sublist_append_left _ _
        · have hlv : ∀ q ∈ a, q.lvl ≤ 0 + 1 := by
            cases hp with
            | th _ hl _ => exact hl
          exact hlv q (by rw [ha]; exact List.mem_append_left _ hq)
      show (WP.th 0 (argD a ++ (argE a).dropLast)).val < (WP.th 0 a).val
      rw [val_lt_val_iff hb hp]
      refine Or.inl ⟨?_, fun s hs => ?_⟩
      · have e : WP.valS a = WP.valS (argD a ++ (argE a).dropLast) + η0.val := by
          conv_lhs => rw [ha]
          rw [valS_append (argD a ++ (argE a).dropLast) [η0], valS_single]
        rw [e]
        exact lt_add_of_pos_right _ (val_pos hη0)
      · obtain ⟨z, hz, hsz⟩ := mem_starS hs
        refine star_lt_val hp s ?_
        exact mem_starS_of (by rw [ha]; exact List.mem_append_left _ hz) hsz
    · rw [barT_neg hg hc]; exact hloc

/-! ## The closure `C^σ(y)` -/

/-- **`C^σ(y)`**: the closure of `{0, σ, y}` under additive decomposition, `lh` on
`(σ, T¹ ∩ Ω_1)` and bar on the principal elements of `(σ, T¹ ∩ Ω_1)`. -/
inductive InC (σ y : Ordinal.{0}) : Ordinal.{0} → Prop
  | zero : InC σ y 0
  | base : InC σ y σ
  | self : InC σ y y
  | comp {l : List Ordinal.{0}} : ANF l → InC σ y l.sum → ∀ x ∈ l, InC σ y x
  | psum {l : List Ordinal.{0}} : ANF l → InC σ y l.sum → ∀ i, InC σ y (l.take i).sum
  | lh {β δ : Ordinal.{0}} : InC σ y β → σ < β → β < T1bound → IsLh β δ → InC σ y δ
  | bar {β : Ordinal.{0}} : InC σ y β → Pr β → σ < β → β < T1bound → InC σ y (barO β)

/-- A set closed under the operations of `C^σ`. -/
def ClosedC (σ : Ordinal.{0}) (R : Set Ordinal.{0}) : Prop :=
  0 ∈ R ∧ σ ∈ R ∧ (∀ l, ANF l → l.sum ∈ R → (∀ x ∈ l, x ∈ R) ∧ ∀ i, (l.take i).sum ∈ R) ∧
    (∀ β ∈ R, σ < β → β < T1bound → ∀ δ, IsLh β δ → δ ∈ R) ∧
    (∀ β ∈ R, Pr β → σ < β → β < T1bound → barO β ∈ R)

theorem InC.sub {σ y : Ordinal.{0}} {R : Set Ordinal.{0}} (hR : ClosedC σ R) (hy : y ∈ R)
    {β : Ordinal.{0}} (h : InC σ y β) : β ∈ R := by
  induction h with
  | zero => exact hR.1
  | base => exact hR.2.1
  | self => exact hy
  | comp hl _ x hx ih => exact (hR.2.2.1 _ hl ih).1 x hx
  | psum hl _ i ih => exact (hR.2.2.1 _ hl ih).2 i
  | lh _ h1 h2 hδ ih => exact hR.2.2.2.1 _ ih h1 h2 _ hδ
  | bar _ hP h1 h2 ih => exact hR.2.2.2.2 _ ih hP h1 h2

/-- The parts of the finite sets used in the proof: a set `T` and the closures `C^σ(z)`,
`z ∈ K`. -/
def RR (σ : Ordinal.{0}) (T K : Set Ordinal.{0}) : Set Ordinal.{0} :=
  T ∪ {β | ∃ z ∈ K, InC σ z β}

theorem closedC_RR {σ : Ordinal.{0}} {T K : Set Ordinal.{0}} (h0 : 0 ∈ T) (hσ : σ ∈ T)
    (hdec : ∀ t ∈ T, ∀ l, ANF l → l.sum = t →
      (∀ x ∈ l, x ∈ RR σ T K) ∧ ∀ i, (l.take i).sum ∈ RR σ T K)
    (hlh : ∀ t ∈ T, σ < t → t < T1bound → ∀ δ, IsLh t δ → δ ∈ RR σ T K)
    (hbar : ∀ t ∈ T, Pr t → σ < t → t < T1bound → barO t ∈ RR σ T K) :
    ClosedC σ (RR σ T K) := by
  refine ⟨Or.inl h0, Or.inl hσ, fun l hl hs => ?_, fun β hβ h1 h2 δ hδ => ?_,
    fun β hβ hP h1 h2 => ?_⟩
  · rcases hs with hs | ⟨z, hz, hs⟩
    · exact hdec _ hs l hl rfl
    · exact ⟨fun x hx => Or.inr ⟨z, hz, InC.comp hl hs x hx⟩,
        fun i => Or.inr ⟨z, hz, InC.psum hl hs i⟩⟩
  · rcases hβ with hβ | ⟨z, hz, hβ⟩
    · exact hlh _ hβ h1 h2 δ hδ
    · exact Or.inr ⟨z, hz, InC.lh hβ h1 h2 hδ⟩
  · rcases hβ with hβ | ⟨z, hz, hβ⟩
    · exact hbar _ hβ hP h1 h2
    · exact Or.inr ⟨z, hz, InC.bar hβ hP h1 h2⟩

theorem RR_finite {σ : Ordinal.{0}} {T K : Set Ordinal.{0}} (hT : T.Finite) (hK : K.Finite)
    (hC : ∀ z ∈ K, {β | InC σ z β}.Finite) : (RR σ T K).Finite := by
  refine hT.union ?_
  have : {β | ∃ z ∈ K, InC σ z β} = ⋃ z ∈ K, {β | InC σ z β} := by ext; simp
  rw [this]
  exact hK.biUnion hC

theorem self_mem_RR {σ z : Ordinal.{0}} {T K : Set Ordinal.{0}} (hz : z ∈ K) : z ∈ RR σ T K :=
  Or.inr ⟨z, hz, InC.self⟩

/-! ## Additive normal forms -/

/-- The partial sums and components of an additive normal form. -/
def Acl (l : List Ordinal.{0}) : Set Ordinal.{0} := {x | x ∈ l ∨ ∃ i, x = (l.take i).sum}

theorem Acl.decomp {ly : List Ordinal.{0}} (hly : ANF ly) {t : Ordinal.{0}} (ht : t ∈ Acl ly)
    {l : List Ordinal.{0}} (hl : ANF l) (hs : l.sum = t) :
    (∀ x ∈ l, x ∈ Acl ly) ∧ ∀ i, (l.take i).sum ∈ Acl ly := by
  rcases ht with ht | ⟨j, rfl⟩
  · have hP : Pr t := hly.1 t ht
    have e : l = [t] := anf_unique hl (anf_single hP) (by simp [hs])
    subst e
    refine ⟨fun x hx => Or.inl (by rw [List.mem_singleton.mp hx]; exact ht), fun i => ?_⟩
    rcases i with _ | i
    · exact Or.inr ⟨0, by simp⟩
    · exact Or.inl (by simpa using ht)
  · have e : l = ly.take j := anf_unique hl (hly.sublist (List.take_sublist _ _)) hs
    subst e
    refine ⟨fun x hx => Or.inl (List.mem_of_mem_take hx), fun i => Or.inr ⟨min i j, ?_⟩⟩
    rw [List.take_take]

theorem Acl.mem_of_pr {ly : List Ordinal.{0}} (hly : ANF ly) {t : Ordinal.{0}}
    (ht : t ∈ Acl ly) (hP : Pr t) : t ∈ ly := by
  rcases ht with ht | ⟨j, rfl⟩
  · exact ht
  · have e : ly.take j = [(ly.take j).sum] :=
      anf_unique (hly.sublist (List.take_sublist _ _)) (anf_single hP) (by simp)
    have : (ly.take j).sum ∈ ly.take j := by rw [e]; simp
    exact List.mem_of_mem_take this

theorem Acl.le {ly : List Ordinal.{0}} {t : Ordinal.{0}} (ht : t ∈ Acl ly) : t ≤ ly.sum := by
  rcases ht with ht | ⟨j, rfl⟩
  · exact mem_le_sum ht
  · exact take_sum_le ly j

theorem Acl.finite (ly : List Ordinal.{0}) : (Acl ly).Finite := by
  have : Acl ly ⊆ {x | x ∈ ly} ∪ Set.range (fun i : Fin (ly.length + 1) => (ly.take i).sum) := by
    rintro x (hx | ⟨j, rfl⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨⟨min j ly.length, Nat.lt_succ_of_le (min_le_right _ _)⟩, ?_⟩
      simp only
      rcases le_total j ly.length with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, List.take_length, List.take_of_length_le h]
  exact (ly.finite_toSet.union (Set.finite_range _)).subset this

theorem decomp_zero {l : List Ordinal.{0}} (hl : ANF l) (hs : l.sum = 0) : l = [] :=
  anf_unique hl ⟨by simp, List.Pairwise.nil⟩ (by simp [hs])

theorem pr_base {σ : Ordinal.{0}} (hσ : σ = 1 ∨ InE σ) : Pr σ := by
  rcases hσ with rfl | hE
  · exact pr_one
  · exact hE.pr

/-- The decomposition of `0` and of the base. -/
theorem decomp_zero_base {σ : Ordinal.{0}} (hσ : σ = 1 ∨ InE σ) {R : Set Ordinal.{0}}
    (h0 : 0 ∈ R) (hσR : σ ∈ R) {t : Ordinal.{0}} (ht : t = 0 ∨ t = σ) {l : List Ordinal.{0}}
    (hl : ANF l) (hs : l.sum = t) : (∀ x ∈ l, x ∈ R) ∧ ∀ i, (l.take i).sum ∈ R := by
  rcases ht with rfl | rfl
  · rw [decomp_zero hl hs]; exact ⟨by simp, fun i => by simpa using h0⟩
  · have e : l = [t] := anf_unique hl (anf_single (pr_base hσ)) (by simp [hs])
    subst e
    refine ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hσR, fun i => ?_⟩
    rcases i with _ | i
    · simpa using h0
    · simpa using hσR

/-! ## `lh` of a non-epsilon principal number -/

/-- For `y = ω^{y'} > 1` not epsilon, `lh(y) = y + logend(y')` ([W07b] Thm 2.2). -/
theorem isLh_noneps {y' : Ordinal.{0}} (h1 : 1 < ω ^ y') (hE : ¬ InE (ω ^ y')) :
    IsLh (ω ^ y') (ω ^ y' + logend y') := by
  have hyq : y' < ω ^ y' :=
    lt_of_le_of_ne (right_le_opow y' one_lt_omega0) (fun e => hE (by unfold InE; rw [← e]; exact e.symm))
  have hz : logend y' < ω ^ y' := lt_of_le_of_lt (logend_le_self y') hyq
  have hz1 : logend y' + 1 < ω ^ y' := (pr_opow y').add_lt hz h1
  refine ⟨?_, fun γ hγ => ?_⟩
  · rcases (zero_le : 0 ≤ logend y').lt_or_eq with h0 | h0
    · exact (le1_add_iff h0 hz.le).mpr ⟨y', rfl, le_rfl⟩
    · rw [← h0, add_zero]; exact le1_refl _
  · by_contra hc
    push Not at hc
    have h' : ω ^ y' + (logend y' + 1) ≤ γ := by rw [← add_assoc]; exact Order.add_one_le_of_lt hc
    have hl1 := le1_of_le le_self_add h' hγ
    obtain ⟨α', hα', hle⟩ := (le1_add_iff (by simp) hz1.le).mp hl1
    rw [← opow_inj' hα'] at hle
    exact absurd hle (not_le.mpr (Order.lt_add_one_iff.mpr le_rfl))

/-! ## Theorem FIN -/

theorem htB_le {σ x y : Ordinal.{0}} {n : ℕ} (hσ : σ = 1 ∨ InE σ) (hσT : σ < T1bound)
    (hxy : x ≤ y) (hy : y < T1bound) (hn : htB σ y ≤ n) : htB σ x ≤ n :=
  le_trans (htB_mono hσ hσT hxy hy) hn

theorem finite_inC_aux : ∀ (n : ℕ) (y : Ordinal.{0}) {σ : Ordinal.{0}}, (σ = 1 ∨ InE σ) →
    σ < T1bound → y < T1bound → htB σ y ≤ n → {β | InC σ y β}.Finite := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro y
  induction y using WellFoundedLT.induction with
  | _ y IHy =>
  intro σ hσ hσT hyT hn
  -- the recursive calls at the base `σ`
  have hrec : ∀ z, z < y → {β | InC σ z β}.Finite := fun z hz =>
    IHy z hz hσ hσT (lt_trans hz hyT) (htB_le hσ hσT hz.le hyT hn)
  have hσP := pr_base hσ
  by_cases hA : ¬ Pr y ∨ y ≤ σ
  · -- `y` not principal, or `y ≤ σ`
    obtain ⟨ly, hly, hlys⟩ := exists_anf_of_lt hyT
    set T : Set Ordinal.{0} := {0, σ} ∪ Acl ly with hTd
    set K : Set Ordinal.{0} := {c | c ∈ ly ∧ σ < c} with hKd
    have hKy : ∀ c ∈ K, c < y := by
      rintro c ⟨hc, hσc⟩
      rcases hA with hA | hA
      · -- a component of a non-principal sum is below it
        rcases ly with _ | ⟨a, t⟩
        · simp at hc
        rcases t with _ | ⟨b, t⟩
        · simp at hlys; exact absurd (hlys ▸ hly.1 a (by simp)) hA
        have hca : c ≤ a := by
          rcases List.mem_cons.mp hc with rfl | hc
          · exact le_rfl
          · exact (List.pairwise_cons.mp hly.2).1 c hc
        rw [← hlys, List.sum_cons]
        exact lt_of_le_of_lt hca (lt_add_of_pos_right _
          (lt_of_lt_of_le (hly.1 b (by simp)).pos (mem_le_sum (by simp))))
      · exact absurd (lt_of_lt_of_le hσc (le_trans (mem_le_sum hc) (hlys ▸ hA))) (lt_irrefl _)
    have hsub : {β | InC σ y β} ⊆ RR σ T K := by
      intro β hβ
      refine InC.sub (closedC_RR (Or.inl (by simp)) (Or.inl (by simp)) ?_ ?_ ?_) ?_ hβ
      · intro t ht l hl hs
        rcases ht with ht | ht
        · exact decomp_zero_base hσ (Or.inl (Or.inl (by simp))) (Or.inl (Or.inl (by simp)))
            (by simpa using ht) hl hs
        · obtain ⟨h1, h2⟩ := Acl.decomp hly ht hl hs
          exact ⟨fun x hx => Or.inl (Or.inr (h1 x hx)), fun i => Or.inl (Or.inr (h2 i))⟩
      · intro t ht hσt htT δ hδ
        rcases ht with ht | ht
        · rcases ht with rfl | rfl
          · exact absurd hσt (not_lt.mpr zero_le)
          · exact absurd hσt (lt_irrefl _)
        · by_cases hP : Pr t
          · exact Or.inr ⟨t, ⟨Acl.mem_of_pr hly ht hP, hσt⟩, InC.lh InC.self hσt htT hδ⟩
          · rw [hδ.unique (isLh_self_of_not_inL (not_inL_of_not_pr hP))]
            exact Or.inl (Or.inr ht)
      · intro t ht hP hσt htT
        rcases ht with ht | ht
        · rcases ht with rfl | rfl
          · exact absurd hσt (not_lt.mpr zero_le)
          · exact absurd hσt (lt_irrefl _)
        · exact Or.inr ⟨t, ⟨Acl.mem_of_pr hly ht hP, hσt⟩, InC.bar InC.self hP hσt htT⟩
      · exact Or.inl (Or.inr (Or.inr ⟨ly.length, by rw [List.take_length, hlys]⟩))
    refine Set.Finite.subset (RR_finite ((Set.toFinite _).union (Acl.finite ly)) ?_
      (fun z hz => hrec z (hKy z hz))) hsub
    exact (ly.finite_toSet).subset (fun c hc => hc.1)
  push Not at hA
  obtain ⟨hP, hσy⟩ := hA
  have h1y : 1 < y := by
    rcases hσ with rfl | hE
    · exact hσy
    · exact lt_trans hE.one_lt hσy
  have hbar := barO_lt hP h1y hyT
  by_cases hE : ¬ InE y
  · -- `y` principal, not epsilon: `lh(y) = y + logend(y')`
    obtain ⟨y', rfl⟩ := pr_iff.mp hP
    have hlh := isLh_noneps h1y hE
    set z := logend y' with hz
    have hzy : z < ω ^ y' := lt_of_le_of_lt (logend_le_self y')
      (lt_of_le_of_ne (right_le_opow y' one_lt_omega0) (fun e => hE (by unfold InE; rw [← e]; exact e.symm)))
    obtain ⟨lz, hlz, hlzs⟩ := exists_anf_of_lt (lt_trans hzy hyT)
    have hlzy : ∀ c ∈ lz, c < ω ^ y' := fun c hc => lt_of_le_of_lt (hlzs ▸ mem_le_sum hc) hzy
    set T : Set Ordinal.{0} := {0, σ} ∪ {x | ∃ i, x = ω ^ y' + (lz.take i).sum} with hTd
    set K : Set Ordinal.{0} := {barO (ω ^ y')} ∪ {c | c ∈ lz} with hKd
    have hyT' : ω ^ y' ∈ T := Or.inr ⟨0, by simp⟩
    have hanf : ∀ i, ANF (ω ^ y' :: lz.take i) := fun i =>
      ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hP
        · exact hlz.1 x (List.mem_of_mem_take hx),
       List.pairwise_cons.mpr ⟨fun x hx => (hlzy x (List.mem_of_mem_take hx)).le,
        hlz.2.sublist (List.take_sublist _ _)⟩⟩
    have hnp : ∀ i, (lz.take i).sum ≠ 0 → ¬ Pr (ω ^ y' + (lz.take i).sum) := by
      intro i h0 hP'
      have hp : (lz.take i).sum < ω ^ y' := lt_of_le_of_lt (take_sum_le lz i) (hlzs ▸ hzy)
      have := hP'.add_lt (lt_add_of_pos_right _ (pos_iff_ne_zero.mpr h0))
        (lt_of_lt_of_le hp le_self_add)
      exact lt_irrefl _ this
    have hsub : {β | InC σ (ω ^ y') β} ⊆ RR σ T K := by
      intro β hβ
      refine InC.sub (closedC_RR (Or.inl (by simp)) (Or.inl (by simp)) ?_ ?_ ?_) ?_ hβ
      · intro t ht l hl hs
        rcases ht with ht | ⟨i, rfl⟩
        · exact decomp_zero_base hσ (Or.inl (Or.inl (by simp))) (Or.inl (Or.inl (by simp)))
            (by simpa using ht) hl hs
        · have e : l = ω ^ y' :: lz.take i := anf_unique hl (hanf i) (by rw [hs]; simp)
          subst e
          refine ⟨fun x hx => ?_, fun j => ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact Or.inl hyT'
            · exact self_mem_RR (Or.inr (List.mem_of_mem_take hx))
          · rcases j with _ | j
            · exact Or.inl (Or.inl (by simp))
            · refine Or.inl (Or.inr ⟨min j i, ?_⟩)
              rw [List.take_succ_cons, List.sum_cons, List.take_take]
      · intro t ht hσt htT δ hδ
        rcases ht with ht | ⟨i, rfl⟩
        · rcases ht with rfl | rfl
          · exact absurd hσt (not_lt.mpr zero_le)
          · exact absurd hσt (lt_irrefl _)
        · by_cases h0 : (lz.take i).sum = 0
          · rw [h0, add_zero] at hδ
            rw [hδ.unique hlh]
            exact Or.inl (Or.inr ⟨lz.length, by rw [List.take_length, hlzs]⟩)
          · rw [hδ.unique (isLh_self_of_not_inL (not_inL_of_not_pr (hnp i h0)))]
            exact Or.inl (Or.inr ⟨i, rfl⟩)
      · intro t ht hP' hσt htT
        rcases ht with ht | ⟨i, rfl⟩
        · rcases ht with rfl | rfl
          · exact absurd hσt (not_lt.mpr zero_le)
          · exact absurd hσt (lt_irrefl _)
        · by_cases h0 : (lz.take i).sum = 0
          · rw [h0, add_zero]; exact self_mem_RR (Or.inl rfl)
          · exact absurd hP' (hnp i h0)
      · exact Or.inl hyT'
    have hTfin : T.Finite := by
      refine (Set.toFinite _).union ?_
      have : {x | ∃ i, x = ω ^ y' + (lz.take i).sum} = (fun x => ω ^ y' + x) '' Acl lz ∩
          {x | ∃ i, x = ω ^ y' + (lz.take i).sum} := by
        ext x; constructor
        · rintro ⟨i, rfl⟩; exact ⟨⟨_, Or.inr ⟨i, rfl⟩, rfl⟩, ⟨i, rfl⟩⟩
        · exact fun h => h.2
      rw [this]
      exact ((Acl.finite lz).image _).subset Set.inter_subset_left
    refine Set.Finite.subset (RR_finite hTfin ?_ (fun c hc => hrec c ?_)) hsub
    · exact (Set.finite_singleton _).union lz.finite_toSet
    · rcases hc with hc | hc
      · rw [Set.mem_singleton_iff.mp hc]; exact hbar
      · exact hlzy c hc
  · -- `y` epsilon: base change to `y`
    push Not at hE
    obtain ⟨L, hL⟩ := exists_isLh hyT
    have hLT : L < T1bound := lt_T1bound_of_le1 h1y hyT hL.1
    have hht := htB_lh hσ hσy hE hyT hL
    have hDfin : {β | InC y L β}.Finite :=
      IHn _ (lt_of_lt_of_le hht hn) L (Or.inr hE) hyT hLT le_rfl
    set D := {β | InC y L β} with hDd
    set T : Set Ordinal.{0} := {0, σ, y} ∪ {x | x ∈ D ∧ y < x} with hTd
    set K : Set Ordinal.{0} := {barO y} ∪ {x | x ∈ D ∧ x < y} with hKd
    have hyT' : y ∈ T := Or.inl (by simp)
    have memD : ∀ w ∈ D, w ∈ RR σ T K := by
      intro w hw
      rcases lt_trichotomy w y with h | rfl | h
      · exact self_mem_RR (Or.inr ⟨hw, h⟩)
      · exact Or.inl hyT'
      · exact Or.inl (Or.inr ⟨hw, h⟩)
    have hsub : {β | InC σ y β} ⊆ RR σ T K := by
      intro β hβ
      refine InC.sub (closedC_RR (Or.inl (by simp)) (Or.inl (by simp)) ?_ ?_ ?_) ?_ hβ
      · intro t ht l hl hs
        rcases ht with ht | ⟨htD, hyt⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
          rcases ht with rfl | rfl | rfl
          · exact decomp_zero_base hσ (Or.inl (Or.inl (by simp))) (Or.inl (Or.inl (by simp)))
              (Or.inl rfl) hl hs
          · exact decomp_zero_base hσ (Or.inl (Or.inl (by simp))) (Or.inl (Or.inl (by simp)))
              (Or.inr rfl) hl hs
          · exact decomp_zero_base (Or.inr hE) (Or.inl (Or.inl (by simp)))
              (Or.inl hyT') (Or.inr rfl) hl hs
        · have hsD : InC y L l.sum := by rw [hs]; exact htD
          exact ⟨fun x hx => memD x (InC.comp hl hsD x hx), fun i => memD _ (InC.psum hl hsD i)⟩
      · intro t ht hσt htT δ hδ
        rcases ht with ht | ⟨htD, hyt⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
          rcases ht with rfl | rfl | rfl
          · exact absurd hσt (not_lt.mpr zero_le)
          · exact absurd hσt (lt_irrefl _)
          · rw [hδ.unique hL]; exact memD _ InC.self
        · exact memD _ (InC.lh htD hyt htT hδ)
      · intro t ht hP' hσt htT
        rcases ht with ht | ⟨htD, hyt⟩
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
          rcases ht with rfl | rfl | rfl
          · exact absurd hσt (not_lt.mpr zero_le)
          · exact absurd hσt (lt_irrefl _)
          · exact self_mem_RR (Or.inl rfl)
        · exact memD _ (InC.bar htD hP' hyt htT)
      · exact Or.inl hyT'
    refine Set.Finite.subset (RR_finite ((Set.toFinite _).union
      (hDfin.subset (fun x hx => hx.1))) ((Set.finite_singleton _).union
      (hDfin.subset (fun x hx => hx.1))) (fun c hc => hrec c ?_)) hsub
    rcases hc with hc | hc
    · rw [Set.mem_singleton_iff.mp hc]; exact hbar
    · exact hc.2

/-- **Theorem FIN**: `C^σ(y)` is finite for `σ ∈ {1} ∪ E` and
`σ, y < T¹ ∩ Ω_1`. -/
theorem finite_inC {σ y : Ordinal.{0}} (hσ : σ = 1 ∨ InE σ) (hσT : σ < T1bound)
    (hyT : y < T1bound) : {β | InC σ y β}.Finite :=
  finite_inC_aux _ y hσ hσT hyT le_rfl

/-- `P_1(α) ⊆ C^1(α)`. -/
theorem inC_of_inP1 {α β : Ordinal.{0}} (h : InP1 α β) : InC 1 α β := by
  induction h with
  | zero => exact InC.zero
  | one => exact InC.base
  | self => exact InC.self
  | comp hl _ x hx ih => exact InC.comp hl ih x hx
  | psum hl _ i ih => exact InC.psum hl ih i
  | lh _ h1 h2 hδ ih => exact InC.lh ih h1 h2 hδ
  | bar _ hP h1 h2 ih => exact InC.bar ih hP h1 h2

/-- **`P_1(α)` is finite** (Theorem FIN at `σ = 1`), without [CW12] Cor 6.3 and [W07c]. -/
theorem finite_P1 {α : Ordinal.{0}} (h1 : 1 < α) (h : α < T1bound) : {β | InP1 α β}.Finite :=
  (finite_inC (Or.inl rfl) (lt_trans h1 h) h).subset (fun _ hβ => inC_of_inP1 hβ)

end Googology.Trans.PSS.Main
