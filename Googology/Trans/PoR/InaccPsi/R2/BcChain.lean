import Googology.Trans.PoR.InaccPsi.R2.BcTerm
import Googology.Trans.PoR.InaccPsi.R2.NcName

/-!
# Chains of summands: comparison, decomposition, values, normal forms, subterms, constants

* `cmp_chain`: on normal forms, `cmp` is the lexicographic comparison `bcLcmp` of the summand
  lists;
* `bcSl_bcApp`, `bcApp_of_prefix`: a normal form whose summands begin with `P` is
  `bcApp P (bcDrop |P| a)`; `val_bcApp`: its value is `ΣP + |rest|`;
* `NF_bcApp`, `NF_bcApp_rest`: normal forms of chains (`bcNFL`: a nonincreasing list of principal
  normal forms);
* `bcPSub` (proper subterm), `bcSub`; `bcFree` (no `ψ^S_0`-subterm): `bcSig` fixes free terms;
* the constants `1, ω, Ω_ω, P', ω^{P'+1}`: normal forms, values, freeness.

No axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bc

open Googology.Notation.InaccPsi Googology.Notation.InaccPsi.Term

/-! ## Summand lists of principal terms -/

theorem bcSl_prin {t : Term} (h : t.isPrin = true) : bcSl t = [t] := by
  cases t <;> simp_all [isPrin, isSC, bcSl]

theorem bcSl_ne_nil {t : Term} (h : t ≠ zero) : bcSl t ≠ [] := by
  cases t <;> simp_all [bcSl]

theorem not_isPrin_add (a b : Term) : (add a b).isPrin = false := rfl

/-- **On normal forms `cmp` is lexicographic on summand lists.** -/
theorem cmp_chain : ∀ {s t : Term}, NF s → NF t → cmp s t = bcLcmp (bcSl s) (bcSl t)
  | zero, t, _, _ => by
    by_cases h : t = zero
    · subst h; simp [Term.cmp, bcSl, bcLcmp]
    · rw [cmp_zero_left h]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil h)
      simp [bcSl, hx, bcLcmp]
  | add a b, t, hs, ht => by
    have hb0 : b ≠ zero := hs.2.2.2.1
    have hsl : bcSl b ≠ [] := bcSl_ne_nil hb0
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_add, cmp_chain hs.2.1 ht.2.1]
      simp only [bcSl, bcLcmp]
    | _ =>
      rw [cmp_add_left a b rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hsl
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp a _ <;> simp
  | inacc n, t, hs, ht => by
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_right c d rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil ht.2.2.2.1)
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp _ c <;> simp
    | _ => simp only [bcSl, bcLcmp]; rcases h : Term.cmp _ _ <;> simp
  | inaccW, t, hs, ht => by
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_right c d rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil ht.2.2.2.1)
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp _ c <;> simp
    | _ => simp only [bcSl, bcLcmp]; rcases h : Term.cmp _ _ <;> simp
  | phi a' b', t, hs, ht => by
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_right c d rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil ht.2.2.2.1)
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp _ c <;> simp
    | _ => simp only [bcSl, bcLcmp]; rcases h : Term.cmp _ _ <;> simp
  | om a', t, hs, ht => by
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_right c d rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil ht.2.2.2.1)
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp _ c <;> simp
    | _ => simp only [bcSl, bcLcmp]; rcases h : Term.cmp _ _ <;> simp
  | psiS s' a', t, hs, ht => by
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_right c d rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil ht.2.2.2.1)
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp _ c <;> simp
    | _ => simp only [bcSl, bcLcmp]; rcases h : Term.cmp _ _ <;> simp
  | psiI n' a', t, hs, ht => by
    cases t with
    | zero => rw [cmp_zero_right (by simp)]; simp [bcSl, bcLcmp]
    | add c d =>
      rw [cmp_add_right c d rfl]
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (bcSl_ne_nil ht.2.2.2.1)
      simp only [bcSl, bcLcmp, hx]
      rcases h : Term.cmp _ c <;> simp
    | _ => simp only [bcSl, bcLcmp]; rcases h : Term.cmp _ _ <;> simp

/-! ## `bcApp` -/

theorem bcApp_cons_cons (x y : Term) (ys : List Term) (r : Term) :
    bcApp (x :: y :: ys) r = add x (bcApp (y :: ys) r) := rfl

theorem bcApp_single (x r : Term) : bcApp [x] r = if r = zero then x else add x r := rfl

theorem bcApp_ne_zero {P : List Term} (hP : ∀ p ∈ P, p.isPrin = true) (hne : P ≠ []) (r : Term) :
    bcApp P r ≠ zero := by
  match P, hne with
  | [x], _ =>
    rw [bcApp_single]; split_ifs
    · exact NF.ne_zero_of_isPrin (hP x (by simp))
    · simp
  | x :: y :: ys, _ => rw [bcApp_cons_cons]; simp

theorem head_bcApp {x : Term} (hx : x.isPrin = true) (xs : List Term) (r : Term) :
    head (bcApp (x :: xs) r) = x := by
  match xs with
  | [] => rw [bcApp_single]; split_ifs
          · exact head_of_isPrin hx
          · rfl
  | y :: ys => rw [bcApp_cons_cons]; rfl

theorem bcSl_bcApp : ∀ {P : List Term}, (∀ p ∈ P, p.isPrin = true) → ∀ r : Term,
    bcSl (bcApp P r) = P ++ bcSl r
  | [], _, r => rfl
  | [x], hP, r => by
    rw [bcApp_single]
    split_ifs with h
    · subst h; rw [bcSl_prin (hP x (by simp))]; rfl
    · rfl
  | x :: y :: ys, hP, r => by
    rw [bcApp_cons_cons]
    simp only [bcSl]
    rw [bcSl_bcApp (fun p hp => hP p (List.mem_cons_of_mem _ hp)) r]
    rfl

/-- **Decomposition.** A normal form whose summands begin with `P` is `P` followed by the rest. -/
theorem bcApp_of_prefix : ∀ {P : List Term}, (∀ p ∈ P, p.isPrin = true) → ∀ {a : Term}, NF a →
    P.isPrefixOf (bcSl a) = true → a = bcApp P (bcDrop P.length a)
  | [], _, a, _, _ => rfl
  | [x], hP, a, ha, hpre => by
    cases a with
    | zero => simp [bcSl] at hpre
    | add u v =>
      simp only [bcSl, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at hpre
      obtain ⟨rfl, -⟩ := hpre
      show add x v = bcApp [x] v
      rw [bcApp_single, if_neg ha.2.2.2.1]
    | _ =>
      simp only [bcSl, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at hpre
      obtain ⟨rfl, -⟩ := hpre
      simp [bcDrop, bcApp_single]
  | x :: y :: ys, hP, a, ha, hpre => by
    cases a with
    | add u v =>
      simp only [bcSl, List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at hpre
      obtain ⟨hx, hpre'⟩ := hpre
      subst hx
      have e := bcApp_of_prefix (fun p hp => hP p (List.mem_cons_of_mem _ hp)) ha.2.1 hpre'
      rw [bcApp_cons_cons]
      show add _ v = add _ (bcApp (y :: ys) (bcDrop (y :: ys).length v))
      rw [← e]
    | zero => simp [bcSl] at hpre
    | inacc n => simp [bcSl, List.isPrefixOf] at hpre
    | inaccW => simp [bcSl, List.isPrefixOf] at hpre
    | phi _ _ => simp [bcSl, List.isPrefixOf] at hpre
    | om _ => simp [bcSl, List.isPrefixOf] at hpre
    | psiS _ _ => simp [bcSl, List.isPrefixOf] at hpre
    | psiI _ _ => simp [bcSl, List.isPrefixOf] at hpre

/-- The prefix test on a chain `P ++ rest`. -/
theorem isPrefixOf_bcApp {P : List Term} (hP : ∀ p ∈ P, p.isPrin = true) (r : Term) :
    P.isPrefixOf (bcSl (bcApp P r)) = true := by
  rw [bcSl_bcApp hP, List.isPrefixOf_iff_prefix]; exact List.prefix_append _ _

theorem bcDrop_bcApp : ∀ {P : List Term}, (∀ p ∈ P, p.isPrin = true) → ∀ r : Term,
    bcDrop P.length (bcApp P r) = r
  | [], _, r => rfl
  | [x], hP, r => by
    rw [bcApp_single]
    split_ifs with h
    · subst h
      have hx := hP x (by simp)
      cases x <;> simp_all [isPrin, isSC, bcDrop]
    · rfl
  | x :: y :: ys, hP, r => by
    rw [bcApp_cons_cons]
    show bcDrop (ys.length + 1) (bcApp (y :: ys) r) = r
    exact bcDrop_bcApp (fun p hp => hP p (List.mem_cons_of_mem _ hp)) r

/-- Lexicographic comparison with a common prefix. -/
theorem bcLcmp_append_left (P : List Term) (X Y : List Term) :
    bcLcmp (P ++ X) (P ++ Y) = bcLcmp X Y := by
  induction P with
  | nil => rfl
  | cons p P ih => simp only [List.cons_append, bcLcmp, cmp_self, if_true, ih]

/-! ## Values -/

section Val

variable (S : InaccSeq.{0})

theorem val_bcApp : ∀ (P : List Term) (r : Term),
    val S (bcApp P r) = (P.map (val S)).sum + val S r
  | [], r => by simp [bcApp]
  | [x], r => by
    rw [bcApp_single]
    split_ifs with h
    · subst h; simp [val]
    · simp [val]
  | x :: y :: ys, r => by
    rw [bcApp_cons_cons]
    simp only [val, List.map_cons, List.sum_cons]
    rw [val_bcApp (y :: ys) r]
    simp only [List.map_cons, List.sum_cons, add_assoc]

end Val

/-! ## Normal forms of chains -/

/-- A nonincreasing list of principal normal forms. -/
def bcNFL : List Term → Prop
  | [] => True
  | [x] => NF x ∧ x.isPrin = true
  | x :: y :: ys => NF x ∧ x.isPrin = true ∧ cmp y x ≠ .gt ∧ bcNFL (y :: ys)

/-- The last element (`zero` for the empty list). -/
def bcLast : List Term → Term
  | [] => zero
  | [x] => x
  | _ :: y :: ys => bcLast (y :: ys)

theorem bcNFL_prin : ∀ {P : List Term}, bcNFL P → ∀ p ∈ P, p.isPrin = true
  | [], _, p, hp => by simp at hp
  | [x], h, p, hp => by simp at hp; subst hp; exact h.2
  | x :: y :: ys, h, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.2.1
    · exact bcNFL_prin h.2.2.2 p hp

theorem bcNFL_NF : ∀ {P : List Term}, bcNFL P → ∀ p ∈ P, NF p
  | [], _, p, hp => by simp at hp
  | [x], h, p, hp => by simp at hp; subst hp; exact h.1
  | x :: y :: ys, h, p, hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact bcNFL_NF h.2.2.2 p hp

/-- **A chain is a normal form** when its list is, and the rest fits under the last summand. -/
theorem NF_bcApp : ∀ {P : List Term}, bcNFL P → P ≠ [] → ∀ {r : Term},
    (r = zero ∨ (NF r ∧ cmp (head r) (bcLast P) ≠ .gt)) → NF (bcApp P r)
  | [x], hP, _, r, hr => by
    rw [bcApp_single]
    split_ifs with h0
    · exact hP.1
    · rcases hr with h | ⟨hr, hc⟩
      · exact absurd h h0
      · exact ⟨hP.1, hr, hP.2, h0, hc⟩
  | x :: y :: ys, hP, _, r, hr => by
    rw [bcApp_cons_cons]
    have ih := NF_bcApp (P := y :: ys) hP.2.2.2 (by simp) hr
    refine ⟨hP.1, ih, hP.2.1, bcApp_ne_zero (bcNFL_prin hP.2.2.2) (by simp) r, ?_⟩
    rw [head_bcApp (bcNFL_prin hP.2.2.2 y (by simp))]
    exact hP.2.2.1

/-- The rest of a normal chain fits under the last summand. -/
theorem NF_bcApp_rest : ∀ {P : List Term}, P ≠ [] → (∀ p ∈ P, p.isPrin = true) → ∀ {r : Term},
    NF (bcApp P r) → r ≠ zero → NF r ∧ cmp (head r) (bcLast P) ≠ .gt
  | [x], _, _, r, h, hr0 => by
    rw [bcApp_single, if_neg hr0] at h
    exact ⟨h.2.1, h.2.2.2.2⟩
  | x :: y :: ys, _, hP, r, h, hr0 => by
    rw [bcApp_cons_cons] at h
    exact NF_bcApp_rest (P := y :: ys) (by simp)
      (fun p hp => hP p (List.mem_cons_of_mem _ hp)) h.2.1 hr0

theorem NF_bcDrop : ∀ (j : ℕ) {a : Term}, NF a → NF (bcDrop j a)
  | 0, _, h => h
  | j + 1, add _ _, h => NF_bcDrop j h.2.1
  | _ + 1, zero, _ => trivial
  | _ + 1, inacc _, _ => trivial
  | _ + 1, inaccW, _ => trivial
  | _ + 1, phi _ _, _ => trivial
  | _ + 1, om _, _ => trivial
  | _ + 1, psiS _ _, _ => trivial
  | _ + 1, psiI _ _, _ => trivial

/-! ## Subterms -/

/-- Proper subterm. -/
def bcPSub (x : Term) : Term → Prop
  | zero => False
  | inacc _ => False
  | inaccW => False
  | add a b => (x = a ∨ bcPSub x a) ∨ (x = b ∨ bcPSub x b)
  | phi a b => (x = a ∨ bcPSub x a) ∨ (x = b ∨ bcPSub x b)
  | om a => x = a ∨ bcPSub x a
  | psiS s a => (x = s ∨ bcPSub x s) ∨ (x = a ∨ bcPSub x a)
  | psiI _ a => x = a ∨ bcPSub x a

/-- Subterm. -/
def bcSub (x t : Term) : Prop := x = t ∨ bcPSub x t

theorem bcPSub_trans {x y : Term} (z : Term) (hxy : bcPSub x y) (hyz : bcSub y z) :
    bcPSub x z := by
  rcases hyz with rfl | hyz
  · exact hxy
  induction z with
  | zero => exact hyz.elim
  | inacc _ => exact hyz.elim
  | inaccW => exact hyz.elim
  | add a b iha ihb =>
    rcases hyz with (rfl | h) | (rfl | h)
    · exact Or.inl (Or.inr hxy)
    · exact Or.inl (Or.inr (iha h))
    · exact Or.inr (Or.inr hxy)
    · exact Or.inr (Or.inr (ihb h))
  | phi a b iha ihb =>
    rcases hyz with (rfl | h) | (rfl | h)
    · exact Or.inl (Or.inr hxy)
    · exact Or.inl (Or.inr (iha h))
    · exact Or.inr (Or.inr hxy)
    · exact Or.inr (Or.inr (ihb h))
  | om a iha =>
    rcases hyz with rfl | h
    · exact Or.inr hxy
    · exact Or.inr (iha h)
  | psiS s a ihs iha =>
    rcases hyz with (rfl | h) | (rfl | h)
    · exact Or.inl (Or.inr hxy)
    · exact Or.inl (Or.inr (ihs h))
    · exact Or.inr (Or.inr hxy)
    · exact Or.inr (Or.inr (iha h))
  | psiI _ a iha =>
    rcases hyz with rfl | h
    · exact Or.inr hxy
    · exact Or.inr (iha h)

theorem bcSub_refl (x : Term) : bcSub x x := Or.inl rfl

theorem bcSub_trans {x y z : Term} (h1 : bcSub x y) (h2 : bcSub y z) : bcSub x z := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (bcPSub_trans z h1 h2)

theorem bcPSub_of_sub_psub {x y z : Term} (h1 : bcSub x y) (h2 : bcPSub y z) : bcPSub x z := by
  rcases h1 with rfl | h1
  · exact h2
  · exact bcPSub_trans z h1 (Or.inr h2)

theorem bcPSub_size : ∀ {x t : Term}, bcPSub x t → x.size < t.size
  | x, zero, h => h.elim
  | x, inacc _, h => h.elim
  | x, inaccW, h => h.elim
  | x, add a b, h => by
    rcases h with (rfl | h) | (rfl | h)
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
  | x, phi a b, h => by
    rcases h with (rfl | h) | (rfl | h)
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
  | x, om a, h => by
    rcases h with rfl | h
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
  | x, psiS s a, h => by
    rcases h with (rfl | h) | (rfl | h)
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega
  | x, psiI _ a, h => by
    rcases h with rfl | h
    · simp only [size]; omega
    · have := bcPSub_size h; simp only [size]; omega

theorem bcSub_size {x t : Term} (h : bcSub x t) : x.size ≤ t.size := by
  rcases h with rfl | h
  · exact le_rfl
  · exact (bcPSub_size h).le

theorem bcSub_bcDrop : ∀ (j : ℕ) (a : Term), bcDrop j a = zero ∨ bcSub (bcDrop j a) a
  | 0, a => Or.inr (bcSub_refl a)
  | j + 1, add u v => by
    rcases bcSub_bcDrop j v with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rcases h with h | h; exact Or.inl h; exact Or.inr h)))
  | _ + 1, zero => Or.inl rfl
  | _ + 1, inacc _ => Or.inl rfl
  | _ + 1, inaccW => Or.inl rfl
  | _ + 1, phi _ _ => Or.inl rfl
  | _ + 1, om _ => Or.inl rfl
  | _ + 1, psiS _ _ => Or.inl rfl
  | _ + 1, psiI _ _ => Or.inl rfl

/-- `bcDrop (j+1)` of a chain is a proper subterm (or `zero`). -/
theorem bcPSub_bcDrop_succ (j : ℕ) (a : Term) :
    bcDrop (j + 1) a = zero ∨ bcPSub (bcDrop (j + 1) a) a := by
  cases a with
  | add u v =>
    rcases bcSub_bcDrop j v with h | h
    · exact Or.inl h
    · right; show bcPSub (bcDrop j v) (add u v)
      exact Or.inr (by rcases h with h | h; exact Or.inl h; exact Or.inr h)
  | _ => exact Or.inl rfl

/-! ## Free terms: no `ψ^S_0`-subterm -/

/-- `t` has no subterm `ψ^S_0(a)`. -/
def bcFree : Term → Prop
  | zero => True
  | inacc _ => True
  | inaccW => True
  | add a b => bcFree a ∧ bcFree b
  | phi a b => bcFree a ∧ bcFree b
  | om a => bcFree a
  | psiS s a => s ≠ zero ∧ bcFree s ∧ bcFree a
  | psiI _ a => bcFree a

theorem bcSig_free {Ps Pt : List Term} {t : Term} (h : bcFree t) : bcSig Ps Pt t = t := by
  induction t with
  | zero => simp
  | inacc _ => simp
  | inaccW => simp
  | add a b iha ihb => simp [iha h.1, ihb h.2]
  | phi a b iha ihb => simp [iha h.1, ihb h.2]
  | om a iha => simp [iha h]
  | psiS s a ihs iha => rw [bcSig_psiS_ne h.1, ihs h.2.1, iha h.2.2]
  | psiI _ a iha => simp [iha h]

theorem bcFree_of_sub {x t : Term} (hs : bcSub x t) (h : bcFree t) : bcFree x := by
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
    · exact h.2.1
    · exact ihs h.2.1 hs
    · exact h.2.2
    · exact iha h.2.2 hs
  | psiI _ a iha =>
    rcases hs with rfl | hs
    · exact h
    · exact iha h hs

theorem bcFree_bcApp : ∀ {P : List Term}, (∀ p ∈ P, bcFree p) → ∀ {r : Term}, bcFree r →
    bcFree (bcApp P r)
  | [], _, _, hr => hr
  | [x], hP, r, hr => by
    rw [bcApp_single]; split_ifs
    · exact hP x (by simp)
    · exact ⟨hP x (by simp), hr⟩
  | x :: y :: ys, hP, r, hr => by
    rw [bcApp_cons_cons]
    exact ⟨hP x (by simp), bcFree_bcApp (fun p hp => hP p (List.mem_cons_of_mem _ hp)) hr⟩

/-! ## The constants -/

theorem tOne_ne_zero : tOne ≠ zero := by simp [tOne]

theorem bcFree_tOne : bcFree tOne := ⟨trivial, trivial⟩
theorem bcFree_tOm : bcFree tOm := ⟨trivial, bcFree_tOne⟩
theorem bcFree_tW : bcFree tW := bcFree_tOm
theorem bcFree_tPp : bcFree tPp := ⟨tOne_ne_zero, bcFree_tOne, bcFree_tW, bcFree_tW⟩
theorem bcFree_tWp : bcFree tWp := ⟨trivial, bcFree_tPp, bcFree_tOne⟩

theorem NF_tOne : NF tOne := ⟨trivial, trivial, cmp_zero_left (by simp), cmp_zero_left (by simp)⟩

theorem NF_tOm : NF tOm := by
  refine ⟨trivial, NF_tOne, cmp_zero_left (by simp), ?_⟩
  show cmp (phi zero zero) (phi zero tOne) = .lt
  rw [cmp_phi_phi_eq (cmp_self zero)]
  exact cmp_zero_left tOne_ne_zero

theorem NF_tW : NF tW := ⟨NF_tOm, by simp [tOm], rfl⟩

theorem NF_add_tW_tW : NF (add tW tW) :=
  ⟨NF_tW, NF_tW, rfl, by simp [tW], by rw [show head tW = tW from rfl, cmp_self]; simp⟩

theorem KLt_tW (μ α : Term) : KLt μ tW α := by
  simp [tW, tOm, tOne, KLt]

theorem KLt_tOne (μ α : Term) : KLt μ tOne α := by
  simp [tOne, KLt]

theorem NF_tPp : NF tPp := by
  refine ⟨NF_tOne, NF_add_tW_tW, ?_⟩
  exact ⟨KLt_tW _ _, KLt_tW _ _⟩

theorem cmp_tOne_tPp : cmp tOne tPp = .lt := by
  show cmp (phi zero zero) tPp = .lt
  rw [cmp_phi_left_lt (t := tPp) rfl (cmp_zero_left (by simp [tPp]))]
  exact cmp_zero_left (by simp [tPp])

theorem cmp_tPp_tWp : cmp tPp tWp = .lt := by
  show cmp tPp (phi zero (add tPp tOne)) = .lt
  rw [cmp_phi_right_gt (t := tPp) rfl (cmp_zero_right (by simp [tPp])),
    cmp_add_right tPp tOne (t := tPp) rfl, cmp_self]
  simp

theorem NF_add_tPp_tOne : NF (add tPp tOne) :=
  ⟨NF_tPp, NF_tOne, rfl, tOne_ne_zero, by
    rw [show head tOne = tOne from rfl, cmp_tOne_tPp]; simp⟩

theorem NF_tWp : NF tWp := by
  refine ⟨trivial, NF_add_tPp_tOne, cmp_zero_left (by simp), ?_⟩
  show cmp (add tPp tOne) tWp = .lt
  rw [cmp_add_left tPp tOne (t := tWp) rfl, cmp_tPp_tWp]; simp

/-- `KLt μ P' α` holds as soon as `Ω_ω·2 < α`. -/
theorem KLt_tPp {μ α : Term} (h : cmp (add tW tW) α = .lt) : KLt μ tPp α := by
  show KLt μ (psiS tOne (add tW tW)) α
  simp only [KLt]
  exact Or.inr ⟨h, KLt_tOne _ _, KLt_tW _ _, KLt_tW _ _⟩

theorem KLt_tWp {μ α : Term} (h : cmp (add tW tW) α = .lt) : KLt μ tWp α := by
  show KLt μ (phi zero (add tPp tOne)) α
  simp only [KLt]
  exact ⟨trivial, KLt_tPp h, KLt_tOne _ _⟩

section ConstVal

variable (S : InaccSeq.{0})

theorem val_tOne : val S tOne = 1 := by
  simp [tOne, val]

theorem val_tOm : val S tOm = Ordinal.omega0 := by
  simp [tOm, val, val_tOne]

theorem val_tW : val S tW = Om Ordinal.omega0 := by
  simp [tW, val, val_tOm]

theorem val_tPp : val S tPp = Nc.ncPp S := by
  simp only [tPp, val, val_tOne, val_tW]; rfl

theorem val_tWp : val S tWp = Ordinal.omega0 ^ (Nc.ncPp S + 1) := by
  simp only [tWp, val, val_tPp, val_tOne]
  rw [Ordinal.veblen_zero_apply]

end ConstVal

end Googology.Trans.PoR.InaccPsi.R2.Bc
