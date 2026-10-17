import Googology.Trans.PoR.InaccPsi.R2.BcChain

/-!
# The domain of the base change: bounds on the `ψ_{Ω₁}`-arguments, and the prefix test

`α_k = Ω_ω·2 + P'·k` (`bcAlpha`), `α_ω = Ω_ω·2 + ω^{P'+1} = Ω_ω·2 + P'·ω` (`bcAlphaW`).

* `val_pre`, `val_preW`: the chains `bcPre k`, `bcPreW` have the values `α_k`, `α_ω`;
* `bcArgsLt S A t`: every `ψ^S_0`-subterm `ψ_{Ω₁}(a)` of `t` has `|a| < A`;
* `bcArgsLt_of_lt` (**argument bound**): a normal form `t` with `|t| < ψ_{Ω₁}(A)` has all its
  `ψ_{Ω₁}`-arguments below `A` (the `K`-sets of the normal forms; `ψ` is monotone);
* `bc_pre_iff` (**prefix test**): for `k ≥ 1` and a normal form `a` with `|a| < α_ω`, the
  summands of `a` begin with `bcPre k` iff `α_k ≤ |a|` (the only principal number in
  `[P', P'·ω)` is `P'`);
* `bc_rest_le`: the rest of a prefixed normal form has its head `≤ P'`.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

section Dom

variable (S : InaccSeq.{0})

/-- `α_k = Ω_ω·2 + P'·k`. -/
noncomputable def bcAlpha (k : ℕ) : Ordinal.{0} :=
  Om Ordinal.omega0 + Om Ordinal.omega0 + Nc.ncPp S * (k : Ordinal.{0})

/-- `α_ω = Ω_ω·2 + ω^{P'+1}`. -/
noncomputable def bcAlphaW : Ordinal.{0} :=
  Om Ordinal.omega0 + Om Ordinal.omega0 + Ordinal.omega0 ^ (Nc.ncPp S + 1)

theorem sum_replicate_ord (x : Ordinal.{0}) : ∀ k : ℕ, (List.replicate k x).sum = x * k
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.sum_cons, sum_replicate_ord x k,
      show ((k + 1 : ℕ) : Ordinal.{0}) = ((1 + k : ℕ) : Ordinal.{0}) by rw [Nat.add_comm],
      Nat.cast_add, Nat.cast_one, mul_add, mul_one]

theorem val_pre (k : ℕ) : val S (bcApp (bcPre k) zero) = bcAlpha S k := by
  rw [val_bcApp]
  simp only [bcPre, List.map_cons, List.map_replicate, List.sum_cons, val_tW, val_tPp,
    sum_replicate_ord, val, add_zero, bcAlpha, add_assoc]

theorem val_preW : val S (bcApp bcPreW zero) = bcAlphaW S := by
  rw [val_bcApp]
  simp only [bcPreW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, val_tW,
    val_tWp, val, add_zero, bcAlphaW, add_assoc]

theorem bcAlpha_lt_W (k : ℕ) : bcAlpha S k < bcAlphaW S := by
  unfold bcAlpha bcAlphaW
  refine (add_lt_add_iff_left _).2 ?_
  have e : Nc.ncPp S = Ordinal.omega0 ^ Nc.ncPp S := (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)).symm
  calc Nc.ncPp S * (k : Ordinal.{0}) = Ordinal.omega0 ^ Nc.ncPp S * (k : Ordinal.{0}) := by
        rw [← e]
    _ < Ordinal.omega0 ^ (Nc.ncPp S + 1) :=
        Ordinal.omega0_opow_mul_nat_lt (Order.lt_add_one_iff.2 le_rfl) k

/-- Every `ψ_{Ω₁}`-argument in `t` is below `A`. -/
def bcArgsLt (A : Ordinal.{0}) : Term → Prop
  | zero => True
  | inacc _ => True
  | inaccW => True
  | add a b => bcArgsLt A a ∧ bcArgsLt A b
  | phi a b => bcArgsLt A a ∧ bcArgsLt A b
  | om a => bcArgsLt A a
  | psiS s a => bcArgsLt A s ∧ bcArgsLt A a ∧ (s = zero → val S a < A)
  | psiI _ a => bcArgsLt A a

theorem bcArgsLt_of_sub {A : Ordinal.{0}} {x t : Term} (hs : bcSub x t) (h : bcArgsLt S A t) :
    bcArgsLt S A x := by
  rcases hs with rfl | hs
  · exact h
  induction t with
  | zero => exact hs.elim
  | inacc _ => exact hs.elim
  | inaccW => exact hs.elim
  | add a b iha ihb =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact iha h.1 hs
    · exact h.2
    · exact ihb h.2 hs
  | phi a b iha ihb =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact iha h.1 hs
    · exact h.2
    · exact ihb h.2 hs
  | om a iha =>
    rcases hs with rfl | hs
    · exact h
    · exact iha h hs
  | psiS s a ihs iha =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact ihs h.1 hs
    · exact h.2.1
    · exact iha h.2.1 hs
  | psiI _ a iha =>
    rcases hs with rfl | hs
    · exact h
    · exact iha h hs

theorem bcArgsLt_mono {A B : Ordinal.{0}} (hAB : A ≤ B) {t : Term} (h : bcArgsLt S A t) :
    bcArgsLt S B t := by
  induction t with
  | zero => trivial
  | inacc _ => trivial
  | inaccW => trivial
  | add a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | phi a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | om a iha => exact iha h
  | psiS s a ihs iha => exact ⟨ihs h.1, iha h.2.1, fun hs => (h.2.2 hs).trans_le hAB⟩
  | psiI _ a iha => exact iha h

end Dom

theorem NF_of_sub {x t : Term} (hs : bcSub x t) (h : NF t) : NF x := by
  rcases hs with rfl | hs
  · exact h
  induction t with
  | zero => exact hs.elim
  | inacc _ => exact hs.elim
  | inaccW => exact hs.elim
  | add a b iha ihb =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact iha h.1 hs
    · exact h.2.1
    · exact ihb h.2.1 hs
  | phi a b iha ihb =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact iha h.1 hs
    · exact h.2.1
    · exact ihb h.2.1 hs
  | om a iha =>
    rcases hs with rfl | hs
    · exact h.1
    · exact iha h.1 hs
  | psiS s a ihs iha =>
    rcases hs with (rfl | hs) | (rfl | hs)
    · exact h.1
    · exact ihs h.1 hs
    · exact h.2.1
    · exact iha h.2.1 hs
  | psiI _ a iha =>
    rcases hs with rfl | hs
    · exact h.1
    · exact iha h.1 hs

section Bound

variable (S : InaccSeq.{0})

theorem Om_one_le_val_om {a : Term} (h : NF (om a)) : Om 1 ≤ val S (om a) := by
  have h0 : val S a ≠ 0 := val_ne_zero S h.1 h.2.1
  show Om 1 ≤ Om (val S a)
  exact Om_le_Om.2 (Order.one_le_iff_ne_zero.2 h0)

theorem Om_one_lt_val_psiS {s a : Term} (hs : NF s) (hs0 : s ≠ zero) :
    Om 1 < val S (psiS s a) := by
  have h0 : val S s ≠ 0 := val_ne_zero S hs hs0
  exact lt_of_le_of_lt (Om_le_Om.2 (Order.one_le_iff_ne_zero.2 h0)) (val_psiS_bounds S s a).1

theorem val_psiS_zero (a : Term) : val S (psiS zero a) = S.psi (val S a) (Om 1) := by
  simp only [val, zero_add]

/-- The stage of the argument bound (simultaneously for the `K`-recursion). -/
theorem bcArgs_stage (A : Ordinal.{0}) : ∀ N : ℕ, ∀ t : Term, t.size ≤ N → NF t →
    (val S t < S.psi A (Om 1) → bcArgsLt S A t) ∧
    (∀ μ α : Term, NF μ → NF α → val S μ ≤ S.psi A (Om 1) → val S α < A → KLt μ t α →
      bcArgsLt S A t) := by
  have hpsi1 : S.psi A (Om 1) < Om 1 := InaccSeq.psi_lt (S := S) InaccSeq.InR_Om1 A
  intro N
  induction N with
  | zero => intro t ht; exact absurd ht (by have := size_pos t; omega)
  | succ N ih =>
    intro t ht hNF
    have P1 : val S t < S.psi A (Om 1) → bcArgsLt S A t := by
      intro hv
      cases t with
      | zero => trivial
      | inacc _ => trivial
      | inaccW => trivial
      | add a b =>
        simp only [size] at ht
        exact ⟨(ih a (by omega) hNF.1).1 (lt_of_le_of_lt le_self_add hv),
          (ih b (by omega) hNF.2.1).1 (lt_of_le_of_lt le_add_self hv)⟩
      | phi a b =>
        simp only [size] at ht
        have ha := (cmp_lt_iff S hNF.1 hNF).1 hNF.2.2.1
        have hb := (cmp_lt_iff S hNF.2.1 hNF).1 hNF.2.2.2
        exact ⟨(ih a (by omega) hNF.1).1 (ha.trans hv), (ih b (by omega) hNF.2.1).1 (hb.trans hv)⟩
      | om a =>
        exact absurd (lt_of_le_of_lt (Om_one_le_val_om S hNF) (hv.trans hpsi1)) (lt_irrefl _)
      | psiS s a =>
        by_cases hs0 : s = zero
        · subst hs0
          have haA : val S a < A := by
            by_contra hc
            rw [not_lt] at hc
            have := (InaccSeq.psi_mono (S := S) InaccSeq.InR_Om1 hc).1
            rw [val_psiS_zero] at hv
            exact absurd (lt_of_le_of_lt this hv) (lt_irrefl _)
          simp only [size] at ht
          refine ⟨trivial, (ih a (by omega) hNF.2.1).2 _ a hNF hNF.2.1 hv.le haA hNF.2.2,
            fun _ => haA⟩
        · exact absurd (lt_of_lt_of_le (Om_one_lt_val_psiS S hNF.1 hs0) (hv.trans hpsi1).le)
            (lt_irrefl _)
      | psiI n a =>
        exact absurd ((val_psiI_bounds S n a).2.2.1.trans (hv.trans hpsi1)) (lt_irrefl _)
    refine ⟨P1, fun μ α hμ hα hμA hαA hK => ?_⟩
    cases t with
    | zero => trivial
    | inacc _ => trivial
    | inaccW => trivial
    | add a b =>
      simp only [size] at ht
      exact ⟨(ih a (by omega) hNF.1).2 μ α hμ hα hμA hαA hK.1,
        (ih b (by omega) hNF.2.1).2 μ α hμ hα hμA hαA hK.2⟩
    | phi a b =>
      simp only [size] at ht
      exact ⟨(ih a (by omega) hNF.1).2 μ α hμ hα hμA hαA hK.1,
        (ih b (by omega) hNF.2.1).2 μ α hμ hα hμA hαA hK.2⟩
    | om a =>
      simp only [size] at ht
      rcases hK with hK | hK
      · have := (cmp_lt_iff S hNF hμ).1 hK
        exact absurd (lt_of_le_of_lt (Om_one_le_val_om S hNF)
          (lt_of_lt_of_le this (hμA.trans hpsi1.le))) (lt_irrefl _)
      · exact (ih a (by omega) hNF.1).2 μ α hμ hα hμA hαA hK
    | psiS s a =>
      rcases hK with hK | ⟨hb, hKs, hKa⟩
      · exact P1 (lt_of_lt_of_le ((cmp_lt_iff S hNF hμ).1 hK) hμA)
      · simp only [size] at ht
        refine ⟨(ih s (by omega) hNF.1).2 μ α hμ hα hμA hαA hKs,
          (ih a (by omega) hNF.2.1).2 μ α hμ hα hμA hαA hKa, fun _ => ?_⟩
        exact ((cmp_lt_iff S hNF.2.1 hα).1 hb).trans hαA
    | psiI n a =>
      rcases hK with hK | ⟨_, hKa⟩
      · exact P1 (lt_of_lt_of_le ((cmp_lt_iff S hNF hμ).1 hK) hμA)
      · simp only [size] at ht
        exact (ih a (by omega) hNF.1).2 μ α hμ hα hμA hαA hKa

/-- **Argument bound.** A normal form below `ψ_{Ω₁}(A)` has all its `ψ_{Ω₁}`-arguments below `A`. -/
theorem bcArgsLt_of_lt {A : Ordinal.{0}} {t : Term} (ht : NF t) (hv : val S t < S.psi A (Om 1)) :
    bcArgsLt S A t :=
  (bcArgs_stage S A t.size t le_rfl ht).1 hv

end Bound

/-! ## The prefix test -/

theorem head_bcSl {v : Term} (hv : v ≠ zero) : ∃ ys, bcSl v = head v :: ys := by
  cases v with
  | zero => exact absurd rfl hv
  | add a b => exact ⟨bcSl b, rfl⟩
  | _ => exact ⟨[], rfl⟩

theorem bcNFL_bcSl : ∀ {a : Term}, NF a → bcNFL (bcSl a)
  | zero, _ => trivial
  | add u v, h => by
    obtain ⟨ys, hys⟩ := head_bcSl h.2.2.2.1
    show bcNFL (u :: bcSl v)
    rw [hys]
    have ih := bcNFL_bcSl h.2.1
    rw [hys] at ih
    exact ⟨h.1, h.2.2.1, h.2.2.2.2, ih⟩
  | inacc _, h => ⟨h, rfl⟩
  | inaccW, h => ⟨h, rfl⟩
  | phi _ _, h => ⟨h, rfl⟩
  | om _, h => ⟨h, rfl⟩
  | psiS _ _, h => ⟨h, rfl⟩
  | psiI _ _, h => ⟨h, rfl⟩

theorem bcLcmp_nil_right_ne_lt (X : List Term) : bcLcmp X [] ≠ .lt := by
  cases X <;> simp [bcLcmp]

section Prefix

theorem eq_of_cmp_eq (S : InaccSeq.{0}) {x y : Term} (hx : NF x) (hy : NF y) (h : cmp x y = .eq) : x = y :=
  eq_of_val_eq S hx hy (compare_eq_iff_eq.1 ((cmp_eq_compare S hx hy).symm.trans h))

/-- No principal normal form strictly between `P'` and `P'·ω`. -/
theorem not_between_Pp (S : InaccSeq.{0}) {y : Term} (hy : NF y) (hP : y.isPrin = true)
    (h1 : cmp y tPp = .gt) (h2 : cmp y tWp = .lt) : False := by
  have hv1 : val S tPp < val S y := by
    have := (cmp_eq_compare S hy NF_tPp).symm.trans h1
    exact compare_gt_iff_gt.1 this
  have hv2 : val S y < val S tWp := (cmp_lt_iff S hy NF_tWp).1 h2
  rw [val_tPp] at hv1
  rw [val_tWp] at hv2
  have hy0 : val S y ≠ 0 := val_ne_zero S hy (NF.ne_zero_of_isPrin hP)
  obtain ⟨g, hg⟩ := exists_opow_of_principal (isPrincipal_val S hy hP) hy0
  rw [hg] at hv1 hv2
  rw [← Low.opow_eq_self_of_SC (Nc.ncPp_SC S)] at hv1
  have a1 := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).1 hv1
  have a2 := (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).1 hv2
  exact absurd (Order.lt_add_one_iff.1 a2) (not_le.2 a1)

theorem cmp_lt_tWp_of_le (S : InaccSeq.{0}) {y : Term} (hy : NF y) (h : cmp y tPp ≠ .gt) : cmp y tWp = .lt := by
  rw [cmp_lt_iff S hy NF_tWp]
  have : val S y ≤ val S tPp := by
    have e := cmp_eq_compare S hy NF_tPp
    rcases hc : compare (val S y) (val S tPp) with _ | _ | _
    · exact (compare_lt_iff_lt.1 hc).le
    · exact (compare_eq_iff_eq.1 hc).le
    · rw [hc] at e; exact absurd e h
  refine lt_of_le_of_lt this ?_
  rw [val_tPp, val_tWp]
  calc Nc.ncPp S = Ordinal.omega0 ^ Nc.ncPp S := (Low.opow_eq_self_of_SC (Nc.ncPp_SC S)).symm
    _ < Ordinal.omega0 ^ (Nc.ncPp S + 1) :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (Order.lt_add_one_iff.2 le_rfl)

theorem pre_rep (S : InaccSeq.{0}) : ∀ (j : ℕ) (Y : List Term), bcNFL Y →
    bcLcmp Y (List.replicate j tPp) ≠ .lt → (∀ y ∈ Y.head?, cmp y tWp = .lt) →
    (List.replicate j tPp).isPrefixOf Y = true
  | 0, Y, _, _, _ => by simp
  | j + 1, [], _, h, _ => by simp [List.replicate_succ, bcLcmp] at h
  | j + 1, y :: Y, hN, h, hy => by
    have hyW : cmp y tWp = .lt := hy y rfl
    have hyN : NF y ∧ y.isPrin = true := by
      cases Y with
      | nil => exact hN
      | cons _ _ => exact ⟨hN.1, hN.2.1⟩
    rw [List.replicate_succ] at h ⊢
    simp only [bcLcmp] at h
    by_cases hc : cmp y tPp = .eq
    · rw [if_pos hc] at h
      have e := eq_of_cmp_eq S hyN.1 NF_tPp hc
      subst e
      simp only [List.isPrefixOf, beq_self_eq_true, Bool.true_and]
      cases Y with
      | nil => exact pre_rep S j [] trivial h (by simp)
      | cons y' Y' =>
        exact pre_rep S j (y' :: Y') hN.2.2.2 h (fun z hz => by
          simp at hz; subst hz
          exact cmp_lt_tWp_of_le S (bcNFL_NF hN.2.2.2 _ (by simp)) hN.2.2.1)
    · rw [if_neg hc] at h
      have hgt : cmp y tPp = .gt := by
        rcases hh : cmp y tPp with _ | _ | _
        · exact absurd hh h
        · exact absurd hh hc
        · rfl
      exact (not_between_Pp S hyN.1 hyN.2 hgt hyW).elim

end Prefix

theorem cmp_tOne_tOm : cmp tOne tOm = .lt := by
  show cmp (phi zero zero) (phi zero tOne) = .lt
  rw [cmp_phi_phi_eq (cmp_self zero)]
  exact cmp_zero_left tOne_ne_zero

theorem cmp_tPp_tW : cmp tPp tW = .lt := by
  show cmp (psiS tOne (add tW tW)) (om tOm) = .lt
  rw [cmp_psiS_K _ _ (k := om tOm) rfl]
  have : cardT tOne = om tOne := by simp [cardT, tOne, isF]
  rw [this]
  have h2 : cmp (om tOne) (om tOm) = .lt := by
    simp only [Term.cmp]; exact cmp_tOne_tOm
  rw [h2]; simp

theorem cmp_tWp_tW : cmp tWp tW = .lt := by
  show cmp (phi zero (add tPp tOne)) tW = .lt
  rw [cmp_phi_left_lt (t := tW) rfl (cmp_zero_left (by simp [tW])),
    cmp_add_left tPp tOne (t := tW) rfl, cmp_tPp_tW]
  simp

theorem prin_tW : tW.isPrin = true := rfl
theorem prin_tPp : tPp.isPrin = true := rfl
theorem prin_tWp : tWp.isPrin = true := rfl

theorem prin_pre (k : ℕ) : ∀ p ∈ bcPre k, p.isPrin = true := by
  intro p hp
  simp only [bcPre, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | rfl | ⟨-, rfl⟩ <;> rfl

theorem prin_preW : ∀ p ∈ bcPreW, p.isPrin = true := by
  intro p hp
  simp only [bcPreW, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> rfl

theorem bcNFL_rep : ∀ k : ℕ, bcNFL (List.replicate (k + 1) tPp)
  | 0 => ⟨NF_tPp, rfl⟩
  | k + 1 => by
    rw [List.replicate_succ]
    have ih := bcNFL_rep k
    rw [List.replicate_succ] at ih ⊢
    exact ⟨NF_tPp, rfl, by rw [cmp_self]; simp, ih⟩

theorem bcNFL_pre : ∀ k : ℕ, bcNFL (bcPre k)
  | 0 => ⟨NF_tW, rfl, by rw [cmp_self]; simp, NF_tW, rfl⟩
  | k + 1 => by
    have h := bcNFL_rep k
    rw [List.replicate_succ] at h
    refine ⟨NF_tW, rfl, by rw [cmp_self]; simp, NF_tW, rfl, ?_, ?_⟩
    · show cmp tPp tW ≠ .gt
      rw [cmp_tPp_tW]; simp
    · show bcNFL (tPp :: List.replicate k tPp)
      exact h

theorem bcNFL_preW : bcNFL bcPreW :=
  ⟨NF_tW, rfl, by rw [cmp_self]; simp, NF_tW, rfl, by rw [cmp_tWp_tW]; simp, NF_tWp, rfl⟩

theorem NF_pre (k : ℕ) : NF (bcApp (bcPre k) zero) :=
  NF_bcApp (bcNFL_pre k) (by simp [bcPre]) (Or.inl rfl)

theorem NF_preW : NF (bcApp bcPreW zero) :=
  NF_bcApp bcNFL_preW (by simp [bcPreW]) (Or.inl rfl)

theorem bcLast_rep (x : Term) : ∀ k : ℕ, bcLast (List.replicate (k + 1) x) = x
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, List.replicate_succ]
    show bcLast (x :: List.replicate k x) = x
    rw [← List.replicate_succ]; exact bcLast_rep x k

theorem bcLast_pre (k : ℕ) : bcLast (bcPre (k + 1)) = tPp := by
  show bcLast (tW :: tW :: List.replicate (k + 1) tPp) = tPp
  rw [List.replicate_succ]
  show bcLast (tPp :: List.replicate k tPp) = tPp
  rw [← List.replicate_succ]; exact bcLast_rep tPp k

theorem bcLast_preW : bcLast bcPreW = tWp := rfl

theorem bcNFL_tail {x : Term} {X : List Term} (h : bcNFL (x :: X)) : bcNFL X := by
  cases X with
  | nil => trivial
  | cons y Y => exact h.2.2.2

section PrefixTest

variable (S : InaccSeq.{0})

theorem step_W (S : InaccSeq.{0}) {x : Term} {X Q R : List Term} (hx : NF x)
    (h1 : bcLcmp (x :: X) (tW :: Q) ≠ .lt) (h2 : bcLcmp (x :: X) (tW :: R) = .lt) :
    x = tW ∧ bcLcmp X Q ≠ .lt ∧ bcLcmp X R = .lt := by
  simp only [bcLcmp] at h1 h2
  rcases hc : cmp x tW with _ | _ | _
  · rw [hc] at h1; simp at h1
  · rw [if_pos hc] at h1 h2
    exact ⟨eq_of_cmp_eq S hx NF_tW hc, h1, h2⟩
  · rw [hc] at h2; simp at h2

theorem cmp_val_ne_lt {a b : Term} (ha : NF a) (hb : NF b) (h : val S b ≤ val S a) :
    cmp a b ≠ .lt := by
  rw [Ne, cmp_lt_iff S ha hb, not_lt]; exact h

/-- **The prefix test.** For a normal form `a` with `|a| < α_ω`: the summands of `a` begin with
`bcPre k` iff `α_k ≤ |a|`. -/
theorem bc_pre_iff {k : ℕ} {a : Term} (ha : NF a) (haW : val S a < bcAlphaW S) :
    (bcPre k).isPrefixOf (bcSl a) = true ↔ bcAlpha S k ≤ val S a := by
  constructor
  · intro h
    have e := bcApp_of_prefix (prin_pre k) ha h
    rw [e, val_bcApp, ← val_pre S k, val_bcApp]
    simp only [val, add_zero]
    exact le_self_add
  · intro h
    have h1 : bcLcmp (bcSl a) (bcPre k) ≠ .lt := by
      have := cmp_val_ne_lt S ha (NF_pre k) (by rw [val_pre]; exact h)
      rwa [cmp_chain ha (NF_pre k), bcSl_bcApp (prin_pre k), show bcSl zero = [] from rfl, List.append_nil] at this
    have h2 : bcLcmp (bcSl a) bcPreW = .lt := by
      have := (cmp_lt_iff S ha NF_preW).2 (by rw [val_preW]; exact haW)
      rwa [cmp_chain ha NF_preW, bcSl_bcApp prin_preW, show bcSl zero = [] from rfl, List.append_nil] at this
    have hN := bcNFL_bcSl ha
    generalize bcSl a = X at h1 h2 hN
    rcases X with _ | ⟨x0, X1⟩
    · simp [bcPre, bcLcmp] at h1
    have hx0 : NF x0 := bcNFL_NF hN x0 (by simp)
    obtain ⟨rfl, h1', h2'⟩ := step_W S hx0 h1 h2
    rcases X1 with _ | ⟨x1, X2⟩
    · simp [bcLcmp] at h1'
    have hN1 := bcNFL_tail hN
    have hx1 : NF x1 := bcNFL_NF hN1 x1 (by simp)
    obtain ⟨rfl, h1'', h2''⟩ := step_W S hx1 h1' h2'
    have hN2 := bcNFL_tail hN1
    have hrep := pre_rep S k X2 hN2 h1'' (by
      intro y hy
      rcases X2 with _ | ⟨y0, Y⟩
      · simp at hy
      · simp only [List.head?, Option.mem_def, Option.some.injEq] at hy
        subst hy
        simp only [bcLcmp] at h2''
        by_cases hc : cmp y0 tWp = .eq
        · rw [if_pos hc] at h2''; exact absurd h2'' (bcLcmp_nil_right_ne_lt Y)
        · rwa [if_neg hc] at h2'')
    simp only [bcPre, List.isPrefixOf, beq_self_eq_true, Bool.true_and]
    exact hrep

/-- The rest of a prefixed normal form has its head `≤ P'`. -/
theorem bc_rest_le {k : ℕ} {a : Term} (ha : NF a)
    (hpre : (bcPre (k + 1)).isPrefixOf (bcSl a) = true) :
    bcDrop (bcPre (k + 1)).length a = zero ∨
      (NF (bcDrop (bcPre (k + 1)).length a) ∧
        cmp (head (bcDrop (bcPre (k + 1)).length a)) tPp ≠ .gt) := by
  by_cases h0 : bcDrop (bcPre (k + 1)).length a = zero
  · exact Or.inl h0
  · right
    have e := bcApp_of_prefix (prin_pre (k + 1)) ha hpre
    have := NF_bcApp_rest (P := bcPre (k + 1)) (by simp [bcPre]) (prin_pre (k + 1))
      (e ▸ ha) h0
    rwa [bcLast_pre] at this

/-- The value of a prefixed normal form. -/
theorem val_of_pre {k : ℕ} {a : Term} (ha : NF a) (hpre : (bcPre k).isPrefixOf (bcSl a) = true) :
    val S a = bcAlpha S k + val S (bcDrop (bcPre k).length a) := by
  conv_lhs => rw [bcApp_of_prefix (prin_pre k) ha hpre]
  rw [val_bcApp, ← val_pre S k, val_bcApp]
  simp only [val, add_zero]

theorem val_bcApp_preW (r : Term) : val S (bcApp bcPreW r) = bcAlphaW S + val S r := by
  rw [val_bcApp, ← val_preW S, val_bcApp]
  simp only [val, add_zero]

end PrefixTest

end Googology.Trans.PoR.InaccPsi.R2.Bc
