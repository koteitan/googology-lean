import Googology.Notation.ExBuchholz.WF

/-!
# Sums: from principal terms to every standard form

Granting that every standard principal term `ψ_a(b)` is accessible, every
standard form is accessible, so the order on standard forms is well founded.

The argument reads a standard form through `cmp_cons_cons'` as a leading
principal term followed by a tail.  Because a standard form has weakly
decreasing principal terms (`OT_tail_head_le`), a standard form whose head is
at most `p` is a block of copies of `p` followed by a term whose head is
strictly below `p`.  `lead_lex` says the comparison reads that presentation
lexicographically, so the induction runs on the block length in `Nat` and,
within a fixed length, on accessibility of the part after the block.
-/

namespace Googology.Notation.ExBuchholz.Term

def HeadLe (p : Term) : Term → Prop
  | nil => True
  | cons c d _ => psi c d ≤ p

def leadCount (p : Term) : Term → Nat
  | nil => 0
  | cons c d t => if psi c d = p then leadCount p t + 1 else 0

def dropLead (p : Term) : Term → Term
  | nil => nil
  | cons c d t => if psi c d = p then dropLead p t else cons c d t

theorem OT_headLe_tail {c d s : Term} (h : OT (cons c d s)) : HeadLe (psi c d) s := by
  cases s with
  | nil => trivial
  | cons e f v => exact OT_tail_head_le h

theorem OT_dropLead (p : Term) : ∀ {t : Term}, OT t → OT (dropLead p t)
  | nil, h => h
  | cons c d t, h => by
      simp only [dropLead]
      split
      · exact OT_dropLead p (OT_tail h)
      · exact h

theorem cons_lt_cons_iff {a b t c d u : Term} :
    cons a b t < cons c d u ↔
      psi a b < psi c d ∨ (psi a b = psi c d ∧ t < u) := by
  show (cmp (cons a b t) (cons c d u) = .lt) ↔ _
  rw [cmp_cons_cons']
  constructor
  · intro h
    cases hpq : cmp (psi a b) (psi c d) with
    | lt => exact Or.inl hpq
    | eq => rw [hpq] at h; exact Or.inr ⟨cmp_eq_iff.mp hpq, h⟩
    | gt => rw [hpq] at h; exact Ordering.noConfusion h
  · rintro (h | ⟨h, h'⟩)
    · rw [show cmp (psi a b) (psi c d) = .lt from h]; rfl
    · rw [cmp_eq_iff.mpr h]; exact h'

theorem nil_lt_cons (c d u : Term) : nil < cons c d u := rfl

theorem headLe_of_lt {p t y : Term} (hlet : HeadLe p t) (h : y < t) : HeadLe p y := by
  cases y with
  | nil => trivial
  | cons c d s =>
    cases t with
    | nil => exact absurd h (not_lt_nil _)
    | cons e f v =>
      rcases cons_lt_cons_iff.mp h with hlt | ⟨heq, _⟩
      · exact le_trans (le_of_lt hlt) hlet
      · show psi c d ≤ p
        rw [heq]; exact hlet

theorem dropLead_head_lt {p : Term} : ∀ t : Term, OT t → HeadLe p t →
    ∀ c d s, dropLead p t = cons c d s → psi c d < p := by
  intro t
  induction t with
  | nil => intro _ _ c d s h; exact Term.noConfusion h
  | cons c' d' t' _ _ iht =>
    intro hOT hle c d s h
    simp only [dropLead] at h
    split at h
    · next heq => exact iht (OT_tail hOT) (heq ▸ OT_headLe_tail hOT) c d s h
    · next hne => cases h; exact lt_of_le_of_ne hle hne

theorem lead_lex {p : Term} : ∀ t u : Term, OT t → OT u → HeadLe p t → HeadLe p u →
    t < u →
    leadCount p t < leadCount p u ∨
      (leadCount p t = leadCount p u ∧ dropLead p t < dropLead p u) := by
  intro t
  induction t with
  | nil =>
    intro u _ _ _ _ h
    cases u with
    | nil => exact absurd h (lt_irrefl nil)
    | cons e f v =>
      by_cases hef : psi e f = p
      · left
        simp only [leadCount, if_pos hef]
        exact Nat.succ_pos _
      · right
        simp only [leadCount, if_neg hef, dropLead]
        exact ⟨trivial, nil_lt_cons e f v⟩
  | cons c d s _ _ ihs =>
    intro u hOTt hOTu hlet hleu h
    cases u with
    | nil => exact absurd h (not_lt_nil _)
    | cons e f v =>
      rcases cons_lt_cons_iff.mp h with hlt | ⟨heq, hsv⟩
      · by_cases hef : psi e f = p
        · left
          have hcd : psi c d ≠ p := by
            intro hcd; rw [hcd, hef] at hlt; exact lt_irrefl p hlt
          simp only [leadCount, if_neg hcd, if_pos hef]
          exact Nat.succ_pos _
        · right
          have hcd : psi c d ≠ p := by
            intro hcd
            rw [hcd] at hlt
            exact not_le_of_lt hlt hleu
          simp only [leadCount, if_neg hcd, if_neg hef, dropLead]
          exact ⟨trivial, h⟩
      · by_cases hcd : psi c d = p
        · have hef : psi e f = p := heq.symm.trans hcd
          have hs : HeadLe p s := hcd ▸ OT_headLe_tail hOTt
          have hv : HeadLe p v := hef ▸ OT_headLe_tail hOTu
          simp only [leadCount, if_pos hcd, if_pos hef, dropLead]
          rcases ihs v (OT_tail hOTt) (OT_tail hOTu) hs hv hsv with hk | ⟨hk, hd⟩
          · left; omega
          · right; exact ⟨by omega, hd⟩
        · have hef : psi e f ≠ p := fun x => hcd (heq.trans x)
          right
          simp only [leadCount, if_neg hcd, if_neg hef, dropLead]
          exact ⟨trivial, h⟩

/-- If an accessible standard form `p` bounds the head, the whole standard
form is accessible.  No global hypothesis is needed: the accessibility of `p`
is what the induction runs on. -/
theorem acc_of_headLe :
    ∀ p, Acc OTLt p → OT p → ∀ t, OT t → HeadLe p t → Acc OTLt t := by
  intro p hp
  induction hp with
  | intro p _ IH =>
    intro hOTp
    have Hsub : ∀ t, OT t → (∀ c d s, t = cons c d s → psi c d < p) → Acc OTLt t := by
      intro t hOT hlt
      cases t with
      | nil => exact acc_nil
      | cons c d s =>
        exact IH (psi c d) ⟨OT_head hOT, hOTp, hlt c d s rfl⟩ (OT_head hOT) _ hOT
          (le_refl _)
    have HaccDrop : ∀ t, OT t → HeadLe p t → Acc OTLt (dropLead p t) := fun t hOT hle =>
      Hsub _ (OT_dropLead p hOT) (dropLead_head_lt t hOT hle)
    have Claim : ∀ n : Nat, Acc Nat.lt n →
        ∀ w : Term, Acc OTLt w →
        ∀ t : Term, OT t → HeadLe p t → leadCount p t = n → dropLead p t = w →
        Acc OTLt t := by
      intro n hn
      induction hn with
      | intro n _ ihn =>
        intro w hw
        induction hw with
        | intro w _ ihw =>
          intro t hOTt hlet hcnt hdrp
          constructor
          rintro y ⟨hOTy, _, hylt⟩
          have hley : HeadLe p y := headLe_of_lt hlet hylt
          rcases lead_lex y t hOTy hOTt hley hlet hylt with hk | ⟨hk, hdd⟩
          · exact ihn (leadCount p y) (hcnt ▸ hk) (dropLead p y)
              (HaccDrop y hOTy hley) y hOTy hley rfl rfl
          · exact ihw (dropLead p y)
              ⟨OT_dropLead p hOTy, hdrp ▸ OT_dropLead p hOTt, hdrp ▸ hdd⟩
              y hOTy hley (hk.trans hcnt) rfl
    intro t hOTt hlet
    exact Claim (leadCount p t) (Nat.lt_wfRel.wf.apply _) (dropLead p t)
      (HaccDrop t hOTt hlet) t hOTt hlet rfl rfl

/-- Granting accessibility of the principal terms, every standard form is
accessible. -/
theorem acc_of_OT (HP : ∀ a b, OT (psi a b) → Acc OTLt (psi a b)) :
    ∀ t, OT t → Acc OTLt t := by
  intro t hOT
  cases t with
  | nil => exact acc_nil
  | cons a b r =>
    exact acc_of_headLe (psi a b) (HP a b (OT_head hOT)) (OT_head hOT) _ hOT
      (le_refl _)

/-- **The order on standard forms is well founded, granting accessibility of
the principal terms.**  A term outside `OT` is accessible for free, since
`OTLt y t` demands `OT t`. -/
theorem wellFounded_OTLt (HP : ∀ a b, OT (psi a b) → Acc OTLt (psi a b)) :
    WellFounded OTLt := by
  constructor
  intro t
  by_cases h : OT t
  · exact acc_of_OT HP t h
  · exact ⟨t, fun _ hy => absurd hy.2.1 h⟩

/-! ## Structural size, and reading the standard-form condition -/

/-- The structural size of a term, the measure of the induction below. -/
def size : Term → Nat
  | nil => 0
  | cons a b t => size a + size b + size t + 1

@[simp] theorem size_nil : size nil = 0 := rfl
@[simp] theorem size_cons (a b t : Term) :
    size (cons a b t) = size a + size b + size t + 1 := rfl

@[simp] theorem G_nil (a : Term) : G a nil = [] := rfl
theorem G_cons (a c d t : Term) :
    G a (cons c d t) =
      (if a ≤ c then c :: d :: (G a c ++ G a d) else []) ++ G a t := rfl

theorem lt_of_le_of_lt' {x y z : Term} (h₁ : x ≤ y) (h₂ : y < z) : x < z := by
  rcases le_iff_lt_or_eq.mp h₁ with h | rfl
  · exact lt_trans h h₂
  · exact h₂

theorem lt_of_not_le {x y : Term} (h : ¬ x ≤ y) : y < x := by
  rcases lt_trichotomy x y with h' | rfl | h'
  · exact absurd (le_of_lt h') h
  · exact absurd (le_refl x) h
  · exact h'

/-- Two principal terms compare lexicographically on subscript and argument. -/
theorem psi_lt_psi_iff {a b c d : Term} :
    psi a b < psi c d ↔ a < c ∨ (a = c ∧ b < d) := by
  show (cmp (cons a b nil) (cons c d nil) = .lt) ↔ _
  simp only [cmp]
  constructor
  · intro h
    cases hac : cmp a c with
    | lt => exact Or.inl hac
    | eq =>
      rw [hac] at h
      cases hbd : cmp b d with
      | lt => exact Or.inr ⟨cmp_eq_iff.mp hac, hbd⟩
      | eq => rw [hbd] at h; exact Ordering.noConfusion h
      | gt => rw [hbd] at h; exact Ordering.noConfusion h
    | gt => rw [hac] at h; exact Ordering.noConfusion h
  · rintro (h | ⟨h, h'⟩)
    · rw [show cmp a c = .lt from h]; rfl
    · rw [cmp_eq_iff.mpr h, show cmp b d = .lt from h']; rfl

theorem OT_fst {c d r : Term} (h : OT (cons c d r)) : OT c := by
  simp only [OT, isOT, Bool.and_eq_true] at h
  exact h.1.1.1.1

theorem OT_snd {c d r : Term} (h : OT (cons c d r)) : OT d := by
  simp only [OT, isOT, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- The terms `G` collects are standard forms. -/
theorem OT_of_mem_G (a : Term) : ∀ t : Term, OT t → ∀ z ∈ G a t, OT z := by
  intro t
  induction t with
  | nil => intro _ z hz; cases hz
  | cons c d r ihc ihd ihr =>
    intro h z hz
    rw [G_cons] at hz
    rcases List.mem_append.mp hz with hz | hz
    · split at hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · exact OT_fst h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact OT_snd h
        rcases List.mem_append.mp hz with hz | hz
        · exact ihc (OT_fst h) z hz
        · exact ihd (OT_snd h) z hz
      · cases hz
    · exact ihr (OT_tail h) z hz

/-- The terms `G` collects are structurally smaller. -/
theorem size_lt_of_mem_G (a : Term) : ∀ t : Term, ∀ z ∈ G a t, size z < size t := by
  intro t
  induction t with
  | nil => intro z hz; cases hz
  | cons c d r ihc ihd ihr =>
    intro z hz
    rw [G_cons] at hz
    rcases List.mem_append.mp hz with hz | hz
    · split at hz
      · rcases List.mem_cons.mp hz with rfl | hz
        · simp; omega
        rcases List.mem_cons.mp hz with rfl | hz
        · simp; omega
        rcases List.mem_append.mp hz with hz | hz
        · have := ihc z hz; simp; omega
        · have := ihd z hz; simp; omega
      · cases hz
    · have := ihr z hz; simp; omega

/-- The standard-form condition, read off. -/
theorem OT_G_lt {a b : Term} (h : OT (psi a b)) : ∀ z ∈ G a b, z < b := by
  simp only [OT, isOT, descHead, head?, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at h
  exact fun z hz => h.1.1.2 z hz

/-- A tail whose head is below a principal term is itself below it. -/
theorem lt_psi_of_headLe {t a b c d : Term} (h : HeadLe (psi a b) t)
    (hlt : psi a b < psi c d) : t < psi c d := by
  cases t with
  | nil => exact nil_lt_cons c d nil
  | cons a' b' r' => exact cons_lt_cons_iff.mpr (Or.inl (lt_of_le_of_lt' h hlt))

end Googology.Notation.ExBuchholz.Term
