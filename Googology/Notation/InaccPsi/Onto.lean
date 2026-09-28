import Googology.Notation.InaccPsi.NFM

/-!
# Completeness: every member of `⋃_a Cl(a, 0)` has a normal form

`Correct.lean` proves that the value map is injective on normal forms and carries `cmp` to
the order of the ordinals. This file proves the other half:

```
{|t| : t ∈ NF} = ⋃_a Cl(a, 0)                                     (Term.vals_eq)
```

so every member of `⋃_a Cl(a, 0)` is the value of exactly one normal form
(`Term.existsUnique_NF`).

* `⊆`: every term, normal or not, has its value in some `Cl(a, 0)` (`exists_mem_CSet`).
* `⊇`: induction on the closure. Sums, Veblen values and `Ω` are direct (`addNF`,
  `phi_mem_Vals`, `Om_mem_Vals`). A collapse `ψ_κ(ξ)` (`psi_mem_Vals`, by induction on `ξ`)
  gets the argument `M(ξ)` of `NFM.lean`: it is a value (`MQ_val`, with the collapses below
  `ξ` from the induction), it lies in its own closure, and `KLt_complete` turns that into
  the normal-form condition `K_{ψ_κ(M(ξ))}(M(ξ)) < M(ξ)`.
* `KLt_complete` is the converse of the soundness of `K` (Pohlers's (178)): for a normal
  form `t`, `|t| ∈ Cl(|α|, |μ|)` gives `KLt μ t α`. Its collapse case is
  `InaccSeq.arg_mem_of_psi_mem`.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Set

universe u

namespace InaccSeq

variable {S : InaccSeq.{u}}

/-- At arguments in their own closures, `ψ_κ` reflects `<`. -/
theorem lt_of_psi_lt {κ a b : Ordinal.{u}} (hκ : S.InR κ) (ha : a ∈ S.CSet a (S.psi a κ))
    (hb : b ∈ S.CSet b (S.psi b κ)) (h : S.psi a κ < S.psi b κ) : a < b := by
  have hc := compare_psi hκ ha hb
  rw [compare_lt_iff_lt.2 h] at hc
  exact compare_lt_iff_lt.1 hc.symm

end InaccSeq

namespace Term

open InaccSeq

variable (S : InaccSeq.{u})

/-! ## Every value lies in some `Cl(a, 0)` -/

/-- **Every term has its value in some `Cl(a, 0)`.** -/
theorem exists_mem_CSet : ∀ t : Term, ∃ a, val S t ∈ S.CSet a 0
  | zero => ⟨0, CSet.zero_mem 0 0⟩
  | inacc n => ⟨0, CSet.I_mem 0 0 n⟩
  | inaccW => ⟨0, CSet.Iw_mem 0 0⟩
  | add a b => by
    obtain ⟨x, hx⟩ := exists_mem_CSet a
    obtain ⟨y, hy⟩ := exists_mem_CSet b
    exact ⟨max x y, CSet.add_mem (CSet_mono (le_max_left x y) le_rfl hx)
      (CSet_mono (le_max_right x y) le_rfl hy)⟩
  | phi a b => by
    obtain ⟨x, hx⟩ := exists_mem_CSet a
    obtain ⟨y, hy⟩ := exists_mem_CSet b
    exact ⟨max x y, CSet.phi_mem (CSet_mono (le_max_left x y) le_rfl hx)
      (CSet_mono (le_max_right x y) le_rfl hy)⟩
  | om a => by
    obtain ⟨x, hx⟩ := exists_mem_CSet a
    exact ⟨x, CSet.Om_mem hx⟩
  | psiS s a => by
    obtain ⟨x, hx⟩ := exists_mem_CSet s
    obtain ⟨y, hy⟩ := exists_mem_CSet a
    refine ⟨max (max x y) (val S a + 1), CSet.psi_mem
      (lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)) (InR_Om_succ _)
      (CSet.Om_mem (CSet.succ_mem (CSet_mono ?_ le_rfl hx))) (CSet_mono ?_ le_rfl hy)⟩
    · exact (le_max_left x y).trans (le_max_left _ _)
    · exact (le_max_right x y).trans (le_max_left _ _)
  | psiI n a => by
    obtain ⟨y, hy⟩ := exists_mem_CSet a
    exact ⟨max y (val S a + 1), CSet.psi_mem (lt_of_lt_of_le (lt_add_one _) (le_max_right _ _))
      (InR_I n) (CSet.I_mem _ _ n) (CSet_mono (le_max_left _ _) le_rfl hy)⟩

theorem val_lt_Lam (t : Term) : val S t < S.Lam := by
  obtain ⟨a, h⟩ := exists_mem_CSet S t
  exact lt_Lam_of_mem zero_le h

variable {S}

/-! ## Comparisons with a collapse that is not yet known to be normal -/

/-- The converse of `lt_psiI_of_cmp`: below `ψ^I_n(a)` in value is below it for `cmp`. -/
theorem cmp_psiI_of_lt {n : ℕ} {a : Term} (ha : NF a)
    (hsa : val S a ∈ S.CSet (val S a) (val S (psiI n a))) :
    ∀ {x : Term}, NF x → val S x < val S (psiI n a) → cmp x (psiI n a) = .lt
  | zero, _, _ => cmp_zero_left (by simp)
  | inacc m, _, h => by
    have hnm : ¬ n ≤ m := fun hnm => absurd h (not_lt.2 (psiI_lt_I _ hnm).le)
    simp only [cmp, if_neg hnm]
  | inaccW, _, h => absurd h (not_lt.2 (psiI_lt_Iw (S := S) _ n).le)
  | add c d, hx, h => by
    rw [cmp_add_left c d rfl, if_pos (cmp_psiI_of_lt ha hsa hx.1 (lt_of_le_of_lt le_self_add h))]
  | phi c d, hx, h => by
    have hc := cmp_psiI_of_lt ha hsa hx.1 (lt_of_le_of_lt (left_le_veblen _ _) h)
    rw [cmp_phi_left_lt rfl hc]
    exact cmp_psiI_of_lt ha hsa hx.2.1 (lt_of_le_of_lt (right_le_veblen _ _) h)
  | om c, hx, h => by
    rw [cmp_om_F c rfl]
    exact cmp_psiI_of_lt ha hsa hx.1 (lt_of_le_of_lt (le_Om _) h)
  | psiS s c, hx, h => by
    have hs : val S s < val S (psiI n a) :=
      lt_trans (lt_of_le_of_lt (le_Om _) (psiS_bounds _ _).1) h
    have hcard : cmp (cardT s) (psiI n a) = .lt := by
      unfold cardT
      split_ifs
      · exact cmp_zero_left (by simp)
      · exact cmp_psiI_of_lt ha hsa hx.1 hs
      · rw [cmp_om_F s rfl]; exact cmp_psiI_of_lt ha hsa hx.1 hs
    rw [cmp_psiS_K s c rfl, if_pos hcard]
  | psiI m c, hx, h => by
    rw [cmp_psiI_psiI]
    split_ifs with hmn
    · subst hmn
      exact (cmp_lt_iff S hx.1 ha).2
        (lt_of_psi_lt (InR_I m) (sem_of_NF (S := S) hx).2 hsa h)
    · have : m < n := by
        rcases lt_trichotomy m n with h' | h' | h'
        · exact h'
        · exact absurd h' hmn
        · exact absurd h (not_lt.2 (psiI_lt_psiI _ _ h').le)
      exact compare_lt_iff_lt.2 this

theorem cmp_K_psiS_of_lt {s a k : Term} (hs : NF s) (hk : NF k) (hK : k.isK = true)
    (h : val S k < val S (psiS s a)) : cmp k (psiS s a) = .lt := by
  obtain ⟨κ, hκ⟩ := exists_Om_of_isK S hK
  rw [hκ] at h
  have hle : κ ≤ val S s := (Om_lt_psiS _ _).1 h
  have hnc : ¬ cmp k (cardT s) = .gt := by
    rw [cmp_eq_compare S hk (NF_cardT hs), val_cardT, hκ]
    intro hc
    exact absurd (Om_le_Om.2 hle) (not_le.2 (compare_gt_iff_gt.1 hc))
  rw [cmp_K_psiS s a hK, if_neg hnc]

/-- The converse of `lt_psiS_of_cmp`: below `ψ^S_s(a)` in value is below it for `cmp`. -/
theorem cmp_psiS_of_lt {s a : Term} (hs : NF s) (ha : NF a)
    (hsa : val S a ∈ S.CSet (val S a) (val S (psiS s a))) :
    ∀ {x : Term}, NF x → val S x < val S (psiS s a) → cmp x (psiS s a) = .lt
  | zero, _, _ => cmp_zero_left (by simp)
  | inacc _, hx, h => cmp_K_psiS_of_lt hs hx rfl h
  | inaccW, hx, h => cmp_K_psiS_of_lt hs hx rfl h
  | om _, hx, h => cmp_K_psiS_of_lt hs hx rfl h
  | psiI _ _, hx, h => cmp_K_psiS_of_lt hs hx rfl h
  | add c d, hx, h => by
    rw [cmp_add_left c d rfl, if_pos (cmp_psiS_of_lt hs ha hsa hx.1 (lt_of_le_of_lt le_self_add h))]
  | phi c d, hx, h => by
    have hc := cmp_psiS_of_lt hs ha hsa hx.1 (lt_of_le_of_lt (left_le_veblen _ _) h)
    rw [cmp_phi_left_lt rfl hc]
    exact cmp_psiS_of_lt hs ha hsa hx.2.1 (lt_of_le_of_lt (right_le_veblen _ _) h)
  | psiS t b, hx, h => by
    rw [cmp_psiS_psiS]
    rcases lt_trichotomy (val S t) (val S s) with hts | hts | hts
    · have hc : cmp t s = .lt := (cmp_lt_iff S hx.1 hs).2 hts
      rw [if_neg (by rw [hc]; decide), hc]
    · obtain rfl := eq_of_val_eq S hx.1 hs hts
      rw [if_pos (cmp_self _)]
      exact (cmp_lt_iff S hx.2.1 ha).2
        (lt_of_psi_lt (InR_Om_succ _) (sem_of_NF (S := S) hx).2.2 hsa h)
    · exact absurd h (not_lt.2
        (lt_trans ((Om_psiS_lt_Om _ _).2 hts) (psiS_bounds _ _).1).le)

/-! ## The converse of the soundness of `K` -/

/-- **Completeness of `K`** (the other half of Pohlers's (178)): for a normal form `t`,
`|t| ∈ Cl(|α|, |μ|)` gives `K_μ(t) < α`. The bound `μ` need not be normal; only the
comparisons with it in the direction `.lt` are used. -/
theorem KLt_complete {μ α : Term}
    (hμ : ∀ x, NF x → val S x < val S μ → cmp x μ = .lt)
    (hα : ∀ y, NF y → val S y < val S α → cmp y α = .lt) (hμL : val S μ ≤ S.Lam) :
    ∀ {t : Term}, NF t → val S t ∈ S.CSet (val S α) (val S μ) → KLt μ t α
  | zero, _, _ => trivial
  | inacc _, _, _ => trivial
  | inaccW, _, _ => trivial
  | add a b, h, hm => by
    obtain ⟨g, hg⟩ := exists_opow_of_principal (isPrincipal_val S h.1 h.2.2.1)
      (val_ne_zero S h.1 (NF.ne_zero_of_isPrin h.2.2.1))
    have hle : val S (head b) ≤ val S a := by
      have hh := h.2.2.2.2
      rw [cmp_eq_compare S h.2.1.head h.1] at hh
      exact not_lt.1 fun h' => hh (compare_gt_iff_gt.2 h')
    have hb : val S b < ω ^ (g + 1) :=
      val_lt_of_head_lt (exact_all (S := S) b.size) le_rfl h.2.1 (sem_of_NF h.2.1)
        (isPrincipal_add_omega0_opow _) (lt_of_le_of_lt (hle.trans hg.le) (opow_lt_opow_add_one g))
    have hv : val S (add a b) = ω ^ g + val S b := by
      show val S a + val S b = _; rw [hg]
    have hne : val S (add a b) ≠ 0 := by
      rw [hv]; exact (lt_of_lt_of_le (opow_pos g omega0_pos) le_self_add).ne'
    obtain ⟨h1, h2⟩ := lead_tail_mem hm hne
    rw [hv, lead_opow_add hb, ← hg] at h1
    rw [hv, tail_opow_add hb] at h2
    exact ⟨KLt_complete hμ hα hμL h.1 h1, KLt_complete hμ hα hμL h.2.1 h2⟩
  | phi a b, h, hm => by
    have ha : val S a < val S (phi a b) := (cmp_lt_iff S h.1 h).1 h.2.2.1
    have hb : val S b < val S (phi a b) := (cmp_lt_iff S h.2.1 h).1 h.2.2.2
    obtain ⟨h1, h2⟩ := mem_of_veblen_mem hm ha hb
    exact ⟨KLt_complete hμ hα hμL h.1 h1, KLt_complete hμ hα hμL h.2.1 h2⟩
  | om c, h, hm => by
    by_cases hlt : val S (om c) < val S μ
    · exact Or.inl (hμ _ h hlt)
    · exact Or.inr (KLt_complete hμ hα hμL h.1 (mem_of_Om_mem hm))
  | psiS s b, h, hm => by
    by_cases hlt : val S (psiS s b) < val S μ
    · exact Or.inl (hμ _ h hlt)
    have sb := sem_of_NF (S := S) h
    obtain ⟨hbC, hbα⟩ := arg_mem_of_psi_mem (κ := Om (val S s + 1)) (d := val S b)
      (InR_Om_succ _) hm (not_lt.1 hlt) hμL sb.2.2
    have hb := psiS_bounds (S := S) (val S b) (val S s)
    have hsC : val S s ∈ S.CSet (val S α) (val S μ) :=
      mem_of_Om_mem (Om_mem_of_between hm hb.1.le hb.2)
    exact Or.inr ⟨hα _ h.2.1 hbα, KLt_complete hμ hα hμL h.1 hsC,
      KLt_complete hμ hα hμL h.2.1 hbC⟩
  | psiI n b, h, hm => by
    by_cases hlt : val S (psiI n b) < val S μ
    · exact Or.inl (hμ _ h hlt)
    have sb := sem_of_NF (S := S) h
    obtain ⟨hbC, hbα⟩ := arg_mem_of_psi_mem (κ := S.I n) (d := val S b)
      (InR_I n) hm (not_lt.1 hlt) hμL sb.2
    exact Or.inr ⟨hα _ h.1 hbα, KLt_complete hμ hα hμL h.1 hbC⟩

/-! ## Normal-form addition -/

/-- Addition of normal forms: the summands of the left term below the head of the right one
are absorbed. -/
def addNF (x y : Term) : Term :=
  match x with
  | zero => y
  | add a b => if y = zero then add a b else if cmp a (head y) = .lt then y else add a (addNF b y)
  | x => if y = zero then x else if cmp x (head y) = .lt then y else add x y

theorem addNF_add (a b y : Term) : addNF (add a b) y =
    if y = zero then add a b else if cmp a (head y) = .lt then y else add a (addNF b y) := rfl

theorem addNF_prin {x : Term} (hx : x.isPrin = true) (y : Term) :
    addNF x y = if y = zero then x else if cmp x (head y) = .lt then y else add x y := by
  cases x <;> simp [isPrin, isSC] at hx <;> rfl

theorem isPrin_head {y : Term} (hy : NF y) (h0 : y ≠ zero) : (head y).isPrin = true := by
  cases y with
  | zero => exact absurd rfl h0
  | add a b => exact hy.2.2.1
  | _ => rfl

theorem head_of_isPrin {x : Term} (hx : x.isPrin = true) : head x = x := by
  cases x <;> simp [isPrin, isSC] at hx <;> rfl

theorem val_add_absorb {y : Term} (hy : NF y) (h0 : y ≠ zero) {v : Ordinal.{u}}
    (hv : v < val S (head y)) : v + val S y = val S y := by
  have hP := isPrincipal_val S hy.head (isPrin_head hy h0)
  have key := isPrincipal_add_iff_add_left_eq_self.1 hP v hv
  cases y with
  | add h r =>
    show v + (val S h + val S r) = val S h + val S r
    rw [← add_assoc]; exact congrArg (· + val S r) key
  | _ => exact key

theorem addNF_spec_prin {x y : Term} (hx : NF x) (hP : x.isPrin = true) (hy : NF y) :
    NF (addNF x y) ∧ val S (addNF x y) = val S x + val S y ∧
      (head (addNF x y) = head x ∨ head (addNF x y) = head y) := by
  have hhx := head_of_isPrin hP
  rw [addNF_prin hP]
  by_cases hy0 : y = zero
  · subst hy0
    rw [if_pos rfl]
    exact ⟨hx, (add_zero _).symm, Or.inl rfl⟩
  rw [if_neg hy0]
  by_cases hlt : cmp x (head y) = .lt
  · rw [if_pos hlt]
    have hv : val S x < val S (head y) := (cmp_lt_iff S hx hy.head).1 hlt
    exact ⟨hy, (val_add_absorb hy hy0 hv).symm, Or.inr rfl⟩
  · rw [if_neg hlt]
    refine ⟨⟨hx, hy, hP, hy0, ?_⟩, rfl, Or.inl hhx.symm⟩
    rw [cmp_eq_compare S hy.head hx]
    rw [cmp_eq_compare S hx hy.head] at hlt
    intro hg
    exact hlt (compare_lt_iff_lt.2 (compare_gt_iff_gt.1 hg))

/-- **`addNF` adds normal forms**, and the head of the result is one of the two heads. -/
theorem addNF_spec : ∀ {x : Term}, NF x → ∀ {y : Term}, NF y →
    NF (addNF x y) ∧ val S (addNF x y) = val S x + val S y ∧
      (head (addNF x y) = head x ∨ head (addNF x y) = head y)
  | zero, _, _, hy => ⟨hy, (zero_add _).symm, Or.inr rfl⟩
  | add a b, hx, y, hy => by
    rw [addNF_add]
    by_cases hy0 : y = zero
    · subst hy0
      rw [if_pos rfl]
      exact ⟨hx, (add_zero _).symm, Or.inl rfl⟩
    rw [if_neg hy0]
    by_cases hlt : cmp a (head y) = .lt
    · rw [if_pos hlt]
      have hv : val S (add a b) < val S (head y) :=
        val_lt_of_head_lt (exact_all (S := S) _) le_rfl hx (sem_of_NF hx)
          (isPrincipal_val S hy.head (isPrin_head hy hy0)) ((cmp_lt_iff S hx.1 hy.head).1 hlt)
      exact ⟨hy, (val_add_absorb hy hy0 hv).symm, Or.inr rfl⟩
    · rw [if_neg hlt]
      obtain ⟨h1, h2, h3⟩ := addNF_spec hx.2.1 hy
      refine ⟨⟨hx.1, h1, hx.2.2.1, ?_, ?_⟩, ?_, Or.inl rfl⟩
      · intro h
        rw [h] at h2
        exact val_ne_zero S hx.2.1 hx.2.2.2.1
          (le_antisymm (le_self_add.trans h2.symm.le) zero_le)
      · rcases h3 with e3 | e3 <;> rw [e3]
        · exact hx.2.2.2.2
        · rw [cmp_eq_compare S hy.head hx.1]
          rw [cmp_eq_compare S hx.1 hy.head] at hlt
          intro hg
          exact hlt (compare_lt_iff_lt.2 (compare_gt_iff_gt.1 hg))
      · show val S a + val S (addNF b y) = (val S a + val S b) + val S y
        rw [h2, add_assoc]
  | inacc _, hx, _, hy => addNF_spec_prin hx rfl hy
  | inaccW, hx, _, hy => addNF_spec_prin hx rfl hy
  | phi _ _, hx, _, hy => addNF_spec_prin hx rfl hy
  | om _, hx, _, hy => addNF_spec_prin hx rfl hy
  | psiS _ _, hx, _, hy => addNF_spec_prin hx rfl hy
  | psiI _ _, hx, _, hy => addNF_spec_prin hx rfl hy

/-! ## Veblen terms -/

theorem cmp_phi_of_lt_SC {c d t : Term} (hc : NF c) (hd : NF d) (ht : NF t)
    (hSC : t.isSC = true) (h : val S t < veblen (val S c) (val S d)) :
    cmp t (phi c d) = .lt := by
  have hγ := SC_val S ht hSC
  rcases lt_trichotomy (val S t) (val S c) with h1 | h1 | h1
  · rw [cmp_phi_right_lt hSC ((cmp_lt_iff S ht hc).2 h1)]
  · obtain rfl := eq_of_val_eq S ht hc h1
    rw [cmp_phi_right_eq hSC (cmp_self _)]
    refine cmp_zero_left fun hd0 => ?_
    subst hd0
    have h' : val S t < veblen (val S t) 0 := h
    rw [hγ.veblen_zero] at h'
    exact lt_irrefl _ h'
  · rw [cmp_phi_right_gt hSC (by rw [cmp_eq_compare S ht hc]; exact compare_gt_iff_gt.2 h1)]
    refine (cmp_lt_iff S ht hd).2 ?_
    have h2 : veblen (val S c) (val S t) < veblen (val S c) (val S d) := by
      rw [hγ.veblen_right h1]; exact h
    exact veblen_lt_veblen_iff_right.1 h2

/-- Below `φ(c, d)` in value is below it for `cmp`, for normal `c, d` (with `φ(c, d)` itself
not yet known to be normal). -/
theorem cmp_phi_of_lt {c d : Term} (hc : NF c) (hd : NF d) :
    ∀ {x : Term}, NF x → val S x < veblen (val S c) (val S d) → cmp x (phi c d) = .lt
  | zero, _, _ => cmp_zero_left (by simp)
  | add x1 x2, hx, h => by
    rw [cmp_add_left x1 x2 (t := phi c d) rfl,
      if_pos (cmp_phi_of_lt hc hd hx.1 (lt_of_le_of_lt le_self_add h))]
  | phi x1 x2, hx, h => by
    rcases lt_trichotomy (val S x1) (val S c) with h1 | h1 | h1
    · rw [cmp_phi_phi_lt ((cmp_lt_iff S hx.1 hc).2 h1)]
      exact cmp_phi_of_lt hc hd hx.2.1 (lt_of_le_of_lt (right_le_veblen _ _) h)
    · obtain rfl := eq_of_val_eq S hx.1 hc h1
      rw [cmp_phi_phi_eq (cmp_self _)]
      have h' : veblen (val S x1) (val S x2) < veblen (val S x1) (val S d) := h
      exact (cmp_lt_iff S hx.2.1 hd).2 (veblen_lt_veblen_iff_right.1 h')
    · rw [cmp_phi_phi_gt (by rw [cmp_eq_compare S hx.1 hc]; exact compare_gt_iff_gt.2 h1)]
      refine (cmp_lt_iff S hx hd).2 ?_
      have h2 : veblen (val S c) (veblen (val S x1) (val S x2)) < veblen (val S c) (val S d) := by
        rw [veblen_veblen_of_lt h1]; exact h
      exact veblen_lt_veblen_iff_right.1 h2
  | inacc _, hx, h => cmp_phi_of_lt_SC hc hd hx rfl h
  | inaccW, hx, h => cmp_phi_of_lt_SC hc hd hx rfl h
  | om _, hx, h => cmp_phi_of_lt_SC hc hd hx rfl h
  | psiS _ _, hx, h => cmp_phi_of_lt_SC hc hd hx rfl h
  | psiI _ _, hx, h => cmp_phi_of_lt_SC hc hd hx rfl h

/-! ## The values of normal forms -/

variable (S) in
/-- The values of the normal forms. -/
def Vals : Set Ordinal.{u} := {x | ∃ t : Term, t.NF ∧ val S t = x}

theorem zero_mem_Vals : (0 : Ordinal.{u}) ∈ Vals S := ⟨zero, trivial, rfl⟩

theorem I_mem_Vals (n : ℕ) : S.I n ∈ Vals S := ⟨inacc n, trivial, rfl⟩

theorem Iw_mem_Vals : S.Iw ∈ Vals S := ⟨inaccW, trivial, rfl⟩

theorem add_mem_Vals {x y : Ordinal.{u}} (hx : x ∈ Vals S) (hy : y ∈ Vals S) :
    x + y ∈ Vals S := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨h1, h2, -⟩ := addNF_spec (S := S) ha hb
  exact ⟨_, h1, h2⟩

theorem phi_mem_Vals {x y : Ordinal.{u}} (hx : x ∈ Vals S) (hy : y ∈ Vals S) :
    veblen x y ∈ Vals S := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  by_cases hxa : veblen (val S a) (val S b) = val S a
  · rw [hxa]; exact ⟨a, ha, rfl⟩
  by_cases hxb : veblen (val S a) (val S b) = val S b
  · rw [hxb]; exact ⟨b, hb, rfl⟩
  have hal := lt_of_le_of_ne (left_le_veblen (val S a) (val S b)) (Ne.symm hxa)
  have hbl := lt_of_le_of_ne (right_le_veblen (val S a) (val S b)) (Ne.symm hxb)
  exact ⟨phi a b, ⟨ha, hb, cmp_phi_of_lt ha hb ha hal, cmp_phi_of_lt ha hb hb hbl⟩, rfl⟩

theorem Om_mem_Vals {x : Ordinal.{u}} (hx : x ∈ Vals S) : Om x ∈ Vals S := by
  obtain ⟨a, ha, rfl⟩ := hx
  by_cases h0 : a = zero
  · subst h0; exact ⟨zero, trivial, Om_zero.symm⟩
  by_cases hF : a.isF = true
  · exact ⟨a, ha, (Om_val_of_isF S hF).symm⟩
  · exact ⟨om a, ⟨ha, h0, by simpa using hF⟩, rfl⟩

theorem lt_Lam_of_mem_Vals {x : Ordinal.{u}} (hx : x ∈ Vals S) : x < S.Lam := by
  obtain ⟨t, _, rfl⟩ := hx
  exact val_lt_Lam S t

theorem comp_mem_Vals_prin {t : Term} (ht : NF t) (hP : t.isPrin = true) {h : Ordinal.{u}}
    (hc : Comp h (val S t)) : (ω : Ordinal.{u}) ^ h ∈ Vals S := by
  rw [Comp.eq_of_principal (isPrincipal_val S ht hP) (val_ne_zero S ht (NF.ne_zero_of_isPrin hP))
    hc]
  exact ⟨t, ht, rfl⟩

/-- The principal summands of a value are values. -/
theorem comp_mem_Vals : ∀ {t : Term}, NF t → ∀ {h : Ordinal.{u}}, Comp h (val S t) →
    (ω : Ordinal.{u}) ^ h ∈ Vals S
  | zero, _, h, hc => absurd hc (not_comp_zero h)
  | add _ _, ht, _, hc => (Comp.add hc).elim (comp_mem_Vals ht.1) (comp_mem_Vals ht.2.1)
  | inacc _, ht, _, hc => comp_mem_Vals_prin ht rfl hc
  | inaccW, ht, _, hc => comp_mem_Vals_prin ht rfl hc
  | phi _ _, ht, _, hc => comp_mem_Vals_prin ht rfl hc
  | om _, ht, _, hc => comp_mem_Vals_prin ht rfl hc
  | psiS _ _, ht, _, hc => comp_mem_Vals_prin ht rfl hc
  | psiI _ _, ht, _, hc => comp_mem_Vals_prin ht rfl hc

/-- If `Ω_{s+1}` is a value, so is `s`. -/
theorem mem_Vals_of_Om_succ {s : Ordinal.{u}} (h : Om (s + 1) ∈ Vals S) : s ∈ Vals S := by
  obtain ⟨t, ht, hv⟩ := h
  have hs1 : s + 1 ≠ 0 := (add_pos_of_right zero_lt_one s).ne'
  have hSC : t.isSC = true := isSC_of_SC S ht (hv ▸ SC_Om hs1)
  -- a fixed point of `Ω` is not `Ω_{s+1}`
  have notF : ¬ Om (val S t) = val S t := fun hf => by
    rw [hv, Om_inj] at hf
    exact Om_ne_add_one (s + 1) s hf
  cases t with
  | om c =>
    have hc : val S c = s + 1 := Om_inj.1 hv
    refine mem_of_comps zero_mem_Vals (fun _ _ => add_mem_Vals) s fun g hg => ?_
    exact comp_mem_Vals ht.1 (hc ▸ hg.add_one)
  | psiS s' c =>
    exfalso
    have hb := psiS_bounds (S := S) (val S c) (val S s')
    exact not_Om_of_between hb.1 hb.2 _ hv
  | inacc n => exact absurd (Om_val_of_isF S (t := inacc n) rfl) notF
  | inaccW => exact absurd (Om_val_of_isF S (t := inaccW) rfl) notF
  | psiI n c => exact absurd (Om_val_of_isF S (t := psiI n c) rfl) notF
  | zero => simp [isSC] at hSC
  | add _ _ => simp [isSC] at hSC
  | phi _ _ => simp [isSC] at hSC

/-! ## Collapses of values -/

/-- The values satisfy `MQ` for `R = Cl(ξ, g)`, once the collapses below `ξ` are values. -/
theorem MQ_val {ξ g : Ordinal.{u}} (hT : Closed S ξ (Vals S)) :
    ∀ {t : Term}, NF t → MQ S ξ g (Vals S) (val S t)
  | zero, _ => MQ_zero
  | inacc n, _ => MQ_mem hT (SC_I n) (CSet.I_mem ξ g n) (I_mem_Vals n)
  | inaccW, _ => MQ_mem hT SC_Iw (CSet.Iw_mem ξ g) Iw_mem_Vals
  | add _ _, h => MQ_add (MQ_val hT h.1) (MQ_val hT h.2.1)
  | phi _ _, h => MQ_phi hT (MQ_val hT h.1) (MQ_val hT h.2.1)
  | om _, h => MQ_Om hT (MQ_val hT h.1)
  | psiS s a, h => MQ_psiS hT (MQ_val hT h.1).1 (MQ_val hT h.2.1).1 ⟨psiS s a, h, rfl⟩
  | psiI n a, h => MQ_psiI hT (MQ_val hT h.1).1 ⟨psiI n a, h, rfl⟩

variable (S) in
/-- **The collapse of a value is a value.** By induction on the argument `ξ`: the argument
is moved up to `M(ξ)`, which is a value (`MQ_val`, needing the collapses below `ξ` only) and
lies in its own closure, so the collapse at `M(ξ)` is a normal form (`KLt_complete`), and it
names the same ordinal (`psi_M_eq`). -/
theorem psi_mem_Vals : ∀ ξ : Ordinal.{u}, ξ ∈ Vals S →
    (∀ n, S.psi ξ (S.I n) ∈ Vals S) ∧ (∀ s, s ∈ Vals S → S.psi ξ (Om (s + 1)) ∈ Vals S) := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | _ ξ IH =>
  intro hξ
  have hT : Closed S ξ (Vals S) :=
    { zero := zero_mem_Vals
      I := I_mem_Vals
      add := fun _ _ => add_mem_Vals
      phi := fun _ _ => phi_mem_Vals
      om := fun _ => Om_mem_Vals
      psiS := fun s w hs hw hwξ => (IH w hwξ hw).2 s hs
      psiI := fun n w hw hwξ => (IH w hwξ hw).1 n
      lt := fun _ hx => lt_Lam_of_mem_Vals hx }
  have hL := lt_Lam_of_mem_Vals hξ
  obtain ⟨t, ht, rfl⟩ := hξ
  have key : ∀ κ, S.InR κ → ∃ m : Term, NF m ∧
      val S m = S.M (val S t) (S.psi (val S t) κ) (val S t) := fun κ _ =>
    M_mem_of_Good hT _ hL (MQ_val (g := S.psi (val S t) κ) hT ht).1
  constructor
  · intro n
    obtain ⟨m, hm, hmv⟩ := key _ (InR_I n)
    have hself := M_mem_self (InR_I n) hL
    rw [← hmv] at hself
    refine ⟨psiI n m, ⟨hm, ?_⟩, ?_⟩
    · exact KLt_complete (μ := psiI n m) (α := m)
        (fun x hx h => cmp_psiI_of_lt hm hself hx h) (fun y hy h => (cmp_lt_iff S hy hm).2 h)
        ((psi_lt (InR_I n) _).trans (I_lt_Lam n)).le hm hself
    · show S.psi (val S m) (S.I n) = _
      rw [hmv, psi_M_eq (InR_I n) hL]
  · intro s hs
    obtain ⟨st, hst, rfl⟩ := hs
    obtain ⟨m, hm, hmv⟩ := key _ (InR_Om_succ (val S st))
    have hself := M_mem_self (InR_Om_succ (val S st)) hL
    rw [← hmv] at hself
    refine ⟨psiS st m, ⟨hst, hm, ?_⟩, ?_⟩
    · exact KLt_complete (μ := psiS st m) (α := m)
        (fun x hx h => cmp_psiS_of_lt hst hm hself hx h)
        (fun y hy h => (cmp_lt_iff S hy hm).2 h)
        ((psiS_bounds _ _).2.trans (Om_lt_Lam (add_one_lt_Lam (val_lt_Lam S st)))).le hm hself
    · show S.psi (val S m) (Om (val S st + 1)) = _
      rw [hmv, psi_M_eq (InR_Om_succ _) hL]

/-! ## The theorem -/

variable (S) in
/-- **Every member of `Cl(a, 0)` is the value of a normal form.** -/
theorem mem_Vals_of_mem_CSet {a x : Ordinal.{u}} (hx : x ∈ S.CSet a 0) : x ∈ Vals S := by
  induction hx with
  | small h => exact absurd h (not_lt.2 zero_le)
  | zero => exact zero_mem_Vals
  | inacc n => exact I_mem_Vals n
  | inaccW => exact Iw_mem_Vals
  | add _ _ ihx ihy => exact add_mem_Vals ihx ihy
  | phi _ _ ihx ihy => exact phi_mem_Vals ihx ihy
  | om _ ih => exact Om_mem_Vals ih
  | @coll π e hπ _ _ ihπ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exact (psi_mem_Vals S e.1 ihe).1 n
    · exact (psi_mem_Vals S e.1 ihe).2 s (mem_Vals_of_Om_succ ihπ)

variable (S) in
/-- **Completeness.** The values of the normal forms are exactly `⋃_a Cl(a, 0)`. -/
theorem vals_eq : {x | ∃ t : Term, t.NF ∧ Term.val S t = x} = ⋃ a, S.CSet a 0 := by
  ext x
  constructor
  · rintro ⟨t, _, rfl⟩
    exact mem_iUnion.2 (exists_mem_CSet S t)
  · intro hx
    obtain ⟨a, ha⟩ := mem_iUnion.1 hx
    exact mem_Vals_of_mem_CSet S ha

variable (S) in
/-- **Existence of normal forms.** -/
theorem exists_NF {x : Ordinal.{u}} (hx : x ∈ ⋃ a, S.CSet a 0) :
    ∃ t : Term, t.NF ∧ val S t = x := by
  rw [← vals_eq S] at hx; exact hx

variable (S) in
/-- **Existence and uniqueness of normal forms.** Each member of `⋃_a Cl(a, 0)` is the value
of exactly one normal form. -/
theorem existsUnique_NF {x : Ordinal.{u}} (hx : x ∈ ⋃ a, S.CSet a 0) :
    ∃! t : Term, t.NF ∧ val S t = x := by
  obtain ⟨t, ht, hv⟩ := exists_NF S hx
  exact ⟨t, ⟨ht, hv⟩, fun t' h' => eq_of_val_eq S h'.1 ht (h'.2.trans hv.symm)⟩

end Term

end Googology.Notation.InaccPsi
