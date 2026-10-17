import Googology.Trans.PoR.InaccPsi.R2.BrLs1

/-!
# LOW-STEP, part 2: the argument `A + ζ` and Lemma PMAX (InaccPsi side)

* `dropT k c`: the term `c` without its first `k` summands; `dropT_spec`: if the value of a normal `c` is
  `l₁ + ⋯ + lₖ + z` with weakly decreasing principal `lᵢ` and `z` below `ω^{log lᵢ + 1}`, then
  `dropT k c` is a normal term with value `z` (the additive normal form of `A + ζ` is that of `A`
  followed by that of `ζ`);
* `Alist m n = [Ω_ω, θ·ω (m times), θ (n times)]`, whose sum is `A_{ω·m+n} = Ω_ω + θ·(ω·m + n)`;
* `topAtoms`, `pmax`: the largest top atom `ψ_{Ω₂}(d)` of a term (reached through sums and `φ`-arguments);
  `pmax_mono` (**Lemma PMAX**): `ζ < ζ' < Ω₂ ⇒ pmax ζ ≤ pmax ζ'`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-! ## Dropping summands -/

/-- `c` without its first `k` summands. -/
def dropT : ℕ → Term → Term
  | 0, c => c
  | k + 1, .add _ b => dropT k b
  | _ + 1, _ => .zero

theorem dropT_size : ∀ (k : ℕ) (c : Term), (dropT k c).size ≤ c.size
  | 0, c => le_rfl
  | k + 1, .add a b => (dropT_size k b).trans (by simp [Term.size]; omega)
  | _ + 1, .zero => le_rfl
  | _ + 1, .inacc _ => le_rfl
  | _ + 1, .inaccW => le_rfl
  | _ + 1, .phi _ _ => by simp [dropT, Term.size]
  | _ + 1, .om _ => by simp [dropT, Term.size]
  | _ + 1, .psiS _ _ => by simp [dropT, Term.size]
  | _ + 1, .psiI _ _ => by simp [dropT, Term.size]

/-- The leading summand and the rest of a normal sum. -/
theorem NF_add_lead_tail {a b : Term} (h : Term.NF (.add a b)) :
    lead (Term.val S (.add a b)) = Term.val S a ∧ tail (Term.val S (.add a b)) = Term.val S b := by
  have hp := Term.isPrincipal_val S h.1 h.2.2.1
  have h0 : Term.val S a ≠ 0 := Term.val_ne_zero S h.1 (Term.NF.ne_zero_of_isPrin h.2.2.1)
  obtain ⟨hlt, hP⟩ := principal_lt_next hp h0
  have hb : Term.val S b < ω ^ (Ordinal.log ω (Term.val S a) + 1) :=
    val_lt_of_head h.2.1 hP (lt_of_le_of_lt (NF_add_head_le h) hlt)
  exact lead_tail_sum hp h0 hb

theorem prin_lead_tail {t : Term} (h : Term.NF t) (hp : t.isPrin = true) :
    lead (Term.val S t) = Term.val S t ∧ tail (Term.val S t) = 0 :=
  lead_tail_of_principal (Term.isPrincipal_val S h hp) (Term.val_ne_zero S h (Term.NF.ne_zero_of_isPrin hp))

theorem NF_cases (t : Term) (h : Term.NF t) : t = .zero ∨ (∃ a b, t = .add a b) ∨ t.isPrin = true := by
  cases t <;> simp [Term.isPrin, Term.isSC]

/-- A sum of a weakly decreasing list of nonzero principal ordinals, below the next power of its first. -/
theorem sum_lt_next {l : Ordinal.{0}} (hl : IsPrincipal (· + ·) l) (hl0 : l ≠ 0) :
    ∀ (L : List Ordinal.{0}), (∀ x ∈ L, x ≤ l) → (∀ x ∈ L, IsPrincipal (· + ·) x) →
      L.foldr (· + ·) 0 < ω ^ (Ordinal.log ω l + 1)
  | [], _, _ => opow_pos _ omega0_pos
  | x :: L, h1, h2 => by
    obtain ⟨hlt, hP⟩ := principal_lt_next hl hl0
    exact hP (lt_of_le_of_lt (h1 x List.mem_cons_self) hlt)
      (sum_lt_next hl hl0 L (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
        (fun y hy => h2 y (List.mem_cons_of_mem _ hy)))

/-- **The additive normal form of `l₁ + ⋯ + lₖ + z`.** -/
theorem dropT_spec : ∀ (L : List Ordinal.{0}) (c : Term) (z : Ordinal.{0}), Term.NF c →
    (∀ l ∈ L, IsPrincipal (· + ·) l ∧ l ≠ 0) → L.Pairwise (· ≥ ·) →
    (∀ l ∈ L, z < ω ^ (Ordinal.log ω l + 1)) →
    Term.val S c = L.foldr (· + ·) 0 + z →
    Term.NF (dropT L.length c) ∧ Term.val S (dropT L.length c) = z
  | [], c, z, hc, _, _, _, hv => by
    simp only [List.foldr_nil, zero_add] at hv
    exact ⟨hc, hv⟩
  | l :: L, c, z, hc, hp, hpw, hz, hv => by
    have hl := hp l List.mem_cons_self
    have hrest : L.foldr (· + ·) 0 + z < ω ^ (Ordinal.log ω l + 1) := by
      obtain ⟨_, hP⟩ := principal_lt_next hl.1 hl.2
      refine hP (sum_lt_next hl.1 hl.2 L (fun x hx => ?_) (fun x hx => (hp x (List.mem_cons_of_mem _ hx)).1))
        (hz l List.mem_cons_self)
      exact (List.pairwise_cons.1 hpw).1 x hx
    have hlt := lead_tail_sum hl.1 hl.2 hrest
    simp only [List.foldr_cons] at hv
    rw [add_assoc] at hv
    rcases NF_cases c hc with rfl | ⟨a, b, rfl⟩ | hpc
    · simp only [Term.val] at hv
      exact absurd hv.symm (ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hl.2) le_self_add))
    · obtain ⟨e1, e2⟩ := NF_add_lead_tail (S := S) hc
      rw [hv, hlt.1] at e1
      rw [hv, hlt.2] at e2
      have := dropT_spec L b z hc.2.1 (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        (List.pairwise_cons.1 hpw).2 (fun x hx => hz x (List.mem_cons_of_mem _ hx)) e2.symm
      simpa [dropT] using this
    · obtain ⟨e1, e2⟩ := prin_lead_tail (S := S) hc hpc
      rw [hv, hlt.2] at e2
      have hz0 : z = 0 := (Ordinal.add_eq_zero_iff.1 e2).2
      have hL : L = [] := by
        rcases L with _ | ⟨x, L'⟩
        · rfl
        · exfalso
          have hx := hp x (List.mem_cons_of_mem _ List.mem_cons_self)
          have h0 := (Ordinal.add_eq_zero_iff.1 e2).1
          simp only [List.foldr_cons] at h0
          exact hx.2 (Ordinal.add_eq_zero_iff.1 h0).1
      subst hL hz0
      have hdz : dropT 1 c = .zero := by
        cases c <;> simp_all [dropT, Term.isPrin, Term.isSC]
      simp only [List.length_cons, List.length_nil, zero_add, hdz]
      exact ⟨trivial, rfl⟩

/-! ## The list of `A_{ω·m+n}` -/

/-- `[Ω_ω, θ·ω (m times), θ (n times)]`. -/
noncomputable def Alist (S : InaccSeq.{0}) (m n : ℕ) : List Ordinal.{0} :=
  Om (ω : Ordinal.{0}) :: (List.replicate m (ConjT.th S * ω) ++ List.replicate n (ConjT.th S))

theorem foldr_replicate (x : Ordinal.{0}) : ∀ k : ℕ, (List.replicate k x).foldr (· + ·) 0 = x * k
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.foldr_cons, foldr_replicate x k]
    have e : ((k + 1 : ℕ) : Ordinal.{0}) = 1 + (k : Ordinal.{0}) := by
      rw [Nat.add_comm, Nat.cast_add, Nat.cast_one]
    rw [e, mul_add, mul_one]

theorem foldr_append_add (L1 L2 : List Ordinal.{0}) :
    (L1 ++ L2).foldr (· + ·) 0 = L1.foldr (· + ·) 0 + L2.foldr (· + ·) 0 := by
  induction L1 with
  | nil => simp
  | cons x L ih => simp only [List.cons_append, List.foldr_cons, ih, add_assoc]

theorem Alist_sum (m n : ℕ) :
    (Alist S m n).foldr (· + ·) 0 = ConjT.Aη S (ω * m + n) := by
  rw [Alist, List.foldr_cons, foldr_append_add, foldr_replicate, foldr_replicate, ConjT.Aη,
    mul_add, mul_assoc]

theorem Alist_length (m n : ℕ) : (Alist S m n).length = 1 + m + n := by
  simp [Alist]; omega

theorem th_omega_principal : IsPrincipal (· + ·) (ConjT.th S * ω) := by
  have e : ConjT.th S * ω = ω ^ (ConjT.th S + 1) := by
    rw [opow_add, opow_one, Low.opow_eq_self_of_SC (ConjT.SC_th S)]
  rw [e]; exact isPrincipal_add_omega0_opow _

theorem th_pos : 0 < ConjT.th S := (ConjT.SC_th S).1

theorem th_lt_Om2 : ConjT.th S < Om ((1 : Ordinal.{0}) + 1) := psi_lt (InR_Om_succ 1) _

theorem Om_omega_gt_th_omega : ConjT.th S * ω < Om (ω : Ordinal.{0}) := by
  have h := (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).2 0 (Om_pos omega0_ne_zero)
    (ConjT.th S + 1) ?_
  · rw [veblen_zero_apply, opow_add, opow_one, Low.opow_eq_self_of_SC (ConjT.SC_th S)] at h
    exact h
  · have h2 : ConjT.th S < Om (ω : Ordinal.{0}) :=
      th_lt_Om2.trans (Om_lt_Om.2 (by
        have : ((1 : Ordinal.{0}) + 1) = ((2 : ℕ) : Ordinal.{0}) := by norm_num
        rw [this]; exact natCast_lt_omega0 2))
    exact (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).isPrincipal h2
      (lt_of_lt_of_le one_lt_omega0 (omega0_lt_Om omega0_ne_zero).le)

/-! ## Top atoms and Lemma PMAX -/

/-- The top atoms: the terms reached through sums and `φ`-arguments that are not sums or `φ`-terms. -/
def topAtoms : Term → List Term
  | .zero => []
  | .add a b => topAtoms a ++ topAtoms b
  | .phi a b => topAtoms a ++ topAtoms b
  | t => [t]

/-- `t = ψ_{Ω₂}(d)`. -/
def IsP2 (S : InaccSeq.{0}) (t : Term) : Prop := ∃ s d, t = .psiS s d ∧ Term.val S s = 1

open Classical in
/-- The largest `ψ_{Ω₂}`-term of a list (by value). -/
noncomputable def pmaxL (S : InaccSeq.{0}) : List Term → Option Term
  | [] => none
  | t :: l => if IsP2 S t then (match pmaxL S l with
      | none => some t
      | some u => if Term.val S u ≤ Term.val S t then some t else some u) else pmaxL S l

/-- `pmax ζ`: the largest top atom `ψ_{Ω₂}(d)` of `ζ`. -/
noncomputable def pmax (S : InaccSeq.{0}) (ζ : Term) : Option Term := pmaxL S (topAtoms ζ)

/-- The value of `pmax` (`0` for none). -/
noncomputable def pv (S : InaccSeq.{0}) : Option Term → Ordinal.{0}
  | none => 0
  | some u => Term.val S u

theorem pmaxL_spec : ∀ L : List Term,
    (pmaxL S L = none → ∀ v ∈ L, ¬ IsP2 S v) ∧
    (∀ u, pmaxL S L = some u → u ∈ L ∧ IsP2 S u ∧ ∀ v ∈ L, IsP2 S v → Term.val S v ≤ Term.val S u)
  | [] => ⟨fun _ v hv => by simp at hv, fun u h => by simp [pmaxL] at h⟩
  | t :: l => by
    obtain ⟨ih1, ih2⟩ := pmaxL_spec l
    by_cases ht : IsP2 S t
    · rcases hl : pmaxL S l with _ | w
      · refine ⟨fun h => by simp [pmaxL, ht, hl] at h, fun u h => ?_⟩
        simp only [pmaxL, ht, if_true, hl] at h
        cases h
        refine ⟨List.mem_cons_self, ht, fun v hv hv2 => ?_⟩
        rcases List.mem_cons.1 hv with rfl | hv
        · exact le_rfl
        · exact absurd hv2 (ih1 hl v hv)
      · obtain ⟨hw1, hw2, hw3⟩ := ih2 w hl
        refine ⟨fun h => by simp only [pmaxL, ht, if_true, hl] at h; split_ifs at h, fun u h => ?_⟩
        simp only [pmaxL, ht, if_true, hl] at h
        split_ifs at h with hle
        · cases h
          refine ⟨List.mem_cons_self, ht, fun v hv hv2 => ?_⟩
          rcases List.mem_cons.1 hv with rfl | hv
          · exact le_rfl
          · exact (hw3 v hv hv2).trans hle
        · cases h
          refine ⟨List.mem_cons_of_mem _ hw1, hw2, fun v hv hv2 => ?_⟩
          rcases List.mem_cons.1 hv with rfl | hv
          · exact (not_le.1 hle).le
          · exact hw3 v hv hv2
    · simp only [pmaxL, ht, if_false]
      refine ⟨fun h v hv => ?_, fun u h => ?_⟩
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact ht
        · exact ih1 h v hv
      · obtain ⟨h1, h2, h3⟩ := ih2 u h
        refine ⟨List.mem_cons_of_mem _ h1, h2, fun v hv hv2 => ?_⟩
        rcases List.mem_cons.1 hv with rfl | hv
        · exact absurd hv2 ht
        · exact h3 v hv hv2

theorem le_pv {ζ v : Term} (hv : v ∈ topAtoms ζ) (h2 : IsP2 S v) : Term.val S v ≤ pv S (pmax S ζ) := by
  rcases hp : pmax S ζ with _ | u
  · exact absurd h2 ((pmaxL_spec (S := S) (topAtoms ζ)).1 hp v hv)
  · exact ((pmaxL_spec (S := S) (topAtoms ζ)).2 u hp).2.2 v hv h2

theorem topAtom_NF : ∀ {t a : Term}, Term.NF t → a ∈ topAtoms t → Term.NF a
  | .zero, a, _, h => by simp [topAtoms] at h
  | .add x y, a, hn, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact topAtom_NF hn.1 h
    · exact topAtom_NF hn.2.1 h
  | .phi x y, a, hn, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact topAtom_NF hn.1 h
    · exact topAtom_NF hn.2.1 h
  | .om _, a, hn, h => by simp [topAtoms] at h; subst h; exact hn
  | .psiS _ _, a, hn, h => by simp [topAtoms] at h; subst h; exact hn
  | .inacc _, a, hn, h => by simp [topAtoms] at h; subst h; exact hn
  | .inaccW, a, hn, h => by simp [topAtoms] at h; subst h; exact hn
  | .psiI _ _, a, hn, h => by simp [topAtoms] at h; subst h; exact hn

/-- A top atom is at most the term. -/
theorem topAtom_le : ∀ {t a : Term}, Term.NF t → a ∈ topAtoms t → Term.val S a ≤ Term.val S t
  | .zero, a, _, h => by simp [topAtoms] at h
  | .add x y, a, hn, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact (topAtom_le hn.1 h).trans (val_le_add_left x y)
    · exact (topAtom_le hn.2.1 h).trans (val_le_add_right x y)
  | .phi x y, a, hn, h => by
    obtain ⟨hx, hy⟩ := NF_phi_lt (S := S) hn
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact (topAtom_le hn.1 h).trans hx.le
    · exact (topAtom_le hn.2.1 h).trans hy.le
  | .om _, a, _, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .psiS _ _, a, _, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .inacc _, a, _, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .inaccW, a, _, h => by simp [topAtoms] at h; subst h; exact le_rfl
  | .psiI _ _, a, _, h => by simp [topAtoms] at h; subst h; exact le_rfl

/-- If every top atom is below a strongly critical `P`, so is the term. -/
theorem lt_of_topAtoms {P : Ordinal.{0}} (hP : SC P) :
    ∀ {t : Term}, (∀ a ∈ topAtoms t, Term.val S a < P) → Term.val S t < P
  | .zero, _ => hP.1
  | .add x y, h => by
    simp only [topAtoms, List.mem_append] at h
    simp only [Term.val]
    exact hP.isPrincipal (lt_of_topAtoms hP fun a ha => h a (Or.inl ha))
      (lt_of_topAtoms hP fun a ha => h a (Or.inr ha))
  | .phi x y, h => by
    simp only [topAtoms, List.mem_append] at h
    simp only [Term.val]
    exact hP.2 _ (lt_of_topAtoms hP fun a ha => h a (Or.inl ha)) _
      (lt_of_topAtoms hP fun a ha => h a (Or.inr ha))
  | .om _, h => h _ (by simp [topAtoms])
  | .psiS _ _, h => h _ (by simp [topAtoms])
  | .inacc _, h => h _ (by simp [topAtoms])
  | .inaccW, h => h _ (by simp [topAtoms])
  | .psiI _ _, h => h _ (by simp [topAtoms])

theorem Om2_lt_Om_omega : Om ((1 : Ordinal.{0}) + 1) < Om (ω : Ordinal.{0}) := by
  refine Om_lt_Om.2 ?_
  have : ((1 : Ordinal.{0}) + 1) = ((2 : ℕ) : Ordinal.{0}) := by norm_num
  rw [this]; exact natCast_lt_omega0 2

/-- A top atom below `Ω₂` that is not `ψ_{Ω₂}(d)` is at most `Ω₁`. -/
theorem atom_le_Om1 {a : Term} (hn : Term.NF a) (ha : ∀ x y, a ≠ .add x y) (hp : ∀ x y, a ≠ .phi x y)
    (ha0 : a ≠ .zero) (hlt : Term.val S a < Om ((1 : Ordinal.{0}) + 1)) (h2 : ¬ IsP2 S a) :
    Term.val S a ≤ Om (1 : Ordinal.{0}) := by
  cases a with
  | zero => exact absurd rfl ha0
  | add x y => exact absurd rfl (ha x y)
  | phi x y => exact absurd rfl (hp x y)
  | om b =>
    simp only [Term.val] at hlt ⊢
    have hb : Term.val S b < 1 + 1 := Om_lt_Om.1 hlt
    refine Om_le_Om.2 ?_
    rw [← Order.succ_eq_add_one, Order.lt_succ_iff] at hb
    exact hb
  | psiS s d =>
    have hb := Term.val_psiS_bounds S s d
    by_cases hs1 : Term.val S s = 1
    · exact absurd ⟨s, d, rfl, hs1⟩ h2
    · rcases lt_or_gt_of_ne hs1 with hs | hs
      · rw [Order.lt_one_iff] at hs
        rw [hs, zero_add] at hb
        exact hb.2.le
      · have : Om ((1 : Ordinal.{0}) + 1) ≤ Om (Term.val S s) := by
          refine Om_le_Om.2 ?_
          rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hs
        exact absurd (this.trans_lt (hb.1.trans hlt)) (lt_irrefl _)
  | inacc n =>
    simp only [Term.val] at hlt
    exact absurd (hlt.trans Om2_lt_Om_omega) (not_lt.2 (Om_omega_lt_I n).le)
  | inaccW =>
    simp only [Term.val] at hlt
    exact absurd (hlt.trans Om2_lt_Om_omega) (not_lt.2 ((Om_omega_lt_I 0).trans_le (S.I_le_Iw 0)).le)
  | psiI n b =>
    simp only [Term.val] at hlt
    exact absurd (hlt.trans Om2_lt_Om_omega) (not_lt.2 (Om_omega_lt_psiI _ _).le)

theorem topAtom_shape : ∀ {t a : Term}, a ∈ topAtoms t →
    a ≠ .zero ∧ (∀ x y, a ≠ .add x y) ∧ ∀ x y, a ≠ .phi x y
  | .zero, a, h => by simp [topAtoms] at h
  | .add x y, a, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact topAtom_shape h
    · exact topAtom_shape h
  | .phi x y, a, h => by
    simp only [topAtoms, List.mem_append] at h
    rcases h with h | h
    · exact topAtom_shape h
    · exact topAtom_shape h
  | .om _, a, h => by simp [topAtoms] at h; subst h; simp
  | .psiS _ _, a, h => by simp [topAtoms] at h; subst h; simp
  | .inacc _, a, h => by simp [topAtoms] at h; subst h; simp
  | .inaccW, a, h => by simp [topAtoms] at h; subst h; simp
  | .psiI _ _, a, h => by simp [topAtoms] at h; subst h; simp

/-- **Lemma PMAX.**  `ζ < ζ' < Ω₂` gives `pmax ζ ≤ pmax ζ'`. -/
theorem pmax_mono {ζ ζ' : Term} (hn : Term.NF ζ) (hn' : Term.NF ζ')
    (hlt : Term.val S ζ < Term.val S ζ') (hb : Term.val S ζ' < Om ((1 : Ordinal.{0}) + 1)) :
    pv S (pmax S ζ) ≤ pv S (pmax S ζ') := by
  by_contra hgt
  rw [not_le] at hgt
  rcases hp : pmax S ζ with _ | u
  · rw [hp] at hgt; exact absurd hgt (not_lt.2 zero_le)
  rw [hp] at hgt
  obtain ⟨hu1, ⟨s, d, rfl, hs⟩, _⟩ := (pmaxL_spec (S := S) (topAtoms ζ)).2 _ hp
  have hnu : Term.NF (.psiS s d) := topAtom_NF hn hu1
  have hSC : SC (Term.val S (.psiS s d)) := Term.SC_val S hnu rfl
  have hOm1 : Om (1 : Ordinal.{0}) < Term.val S (.psiS s d) := by
    have := (Term.val_psiS_bounds S s d).1; rwa [hs] at this
  have hall : ∀ a ∈ topAtoms ζ', Term.val S a < Term.val S (.psiS s d) := by
    intro a ha
    by_cases h2 : IsP2 S a
    · exact lt_of_le_of_lt (le_pv ha h2) hgt
    · obtain ⟨h0, hadd, hphi⟩ := topAtom_shape ha
      exact lt_of_le_of_lt (atom_le_Om1 (topAtom_NF hn' ha) hadd hphi h0
        (lt_of_le_of_lt (topAtom_le hn' ha) hb) h2) hOm1
  have h1 := lt_of_topAtoms hSC hall
  have h2 := topAtom_le (S := S) hn hu1
  exact absurd (h1.trans_le h2) (not_lt.2 hlt.le)

end Googology.Trans.PoR.InaccPsi.R2.Br
