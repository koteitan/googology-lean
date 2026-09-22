import Googology.Core
import Googology.Notation.ExBuchholz.Eval
/-!
# The evaluation is strictly monotone on standard forms

This is the correctness of the notation system, and it discharges the
hypothesis of `wellFounded_OTLt`.

`main` proves two statements at once, because each needs the other. Reading
`G a (cons c d r)` splits on `a ≤ c`, and the other branch has `c < a`
syntactically, so the closure statement needs the monotonicity statement; and
the monotonicity statement needs the closure statement for two principal terms
that share a subscript.

The measure is `size x` for the monotonicity half and `size a + size t` for the
closure half, and every call strictly decreases:

* monotonicity at `cons a b t` calls itself at `(a,c)`, `(b,d)`, `(t,u)`,
  `(t, ψ_c(d))` and `(z, b)` for `z ∈ G a b`, all of which have a strictly
  smaller left term, and calls the closure half at `(a,b)`;
* the closure half at `(a, cons c d r)` calls itself at `(a,c)`, `(a,d)`,
  `(a,r)`, and calls monotonicity at `(c,a)`, whose measure `size c` is below
  `size a + size (cons c d r)`.
-/

namespace Googology.Notation.ExBuchholz.Term
open Googology.Notation.ExBuchholz Ordinal

/-- The simultaneous induction: monotonicity of the evaluation, and the
semantic reading of the standard-form condition. -/
theorem main : ∀ n : Nat,
    (∀ x y : Term, size x ≤ n → OT x → OT y → x < y → x.val < y.val) ∧
    (∀ a t : Term, size a + size t ≤ n → OT a → OT t →
      ∀ β : Ordinal, (∀ z ∈ G a t, z.val < β) → t.val ∈ Ord.CSet a.val β) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  refine ⟨?_, ?_⟩
  · intro x y hsz hx hy hlt
    cases x with
    | nil =>
      cases y with
      | nil => exact absurd hlt (lt_irrefl nil)
      | cons c d u => exact val_pos (fun h => Term.noConfusion h)
    | cons a b t =>
      cases y with
      | nil => exact absurd hlt (not_lt_nil _)
      | cons c d u =>
        simp only [size_cons] at hsz
        rcases cons_lt_cons_iff.mp hlt with hhead | ⟨hheq, htu⟩
        · have hP : Ord.psi b.val a.val < Ord.psi d.val c.val := by
            rcases psi_lt_psi_iff.mp hhead with hac | ⟨rfl, hbd⟩
            · have hv : a.val < c.val :=
                (ih (size a) (by omega)).1 a c le_rfl (OT_fst hx) (OT_fst hy) hac
              exact psi_lt_of_sub_lt hv
            · have hbd' : b.val < d.val :=
                (ih (size b) (by omega)).1 b d le_rfl (OT_snd hx) (OT_snd hy) hbd
              have hGb : ∀ z ∈ G a b, z.val < b.val := by
                intro z hz
                have hzsz : size z < size b := size_lt_of_mem_G a b z hz
                exact (ih (size z) (by omega)).1 z b le_rfl
                  (OT_of_mem_G a b (OT_snd hx) z hz) (OT_snd hx) (OT_G_lt (OT_head hx) z hz)
              have hmem : b.val ∈ Ord.CSet a.val b.val :=
                (ih (size a + size b) (by omega)).2 a b le_rfl
                  (OT_fst hx) (OT_snd hx) b.val hGb
              exact psi_lt_of_arg_lt hmem hbd' (val_mem_CSet a d.val)
          have hT : t.val < Ord.psi d.val c.val := by
            have h2 : t.val < (psi c d).val :=
              (ih (size t) (by omega)).1 t (psi c d) le_rfl
                (OT_tail hx) (OT_head hy) (lt_psi_of_headLe (OT_headLe_tail hx) hhead)
            rwa [val_psi] at h2
          rw [val_cons, val_cons]
          exact lt_of_lt_of_le (Ord.isPrincipal_add_psi d.val c.val hP hT) le_self_add
        · obtain ⟨rfl, rfl⟩ : a = c ∧ b = d := by
            injection hheq with h1 h2 _
            exact ⟨h1, h2⟩
          rw [val_cons, val_cons]
          have h : t.val < u.val :=
            (ih (size t) (by omega)).1 t u le_rfl (OT_tail hx) (OT_tail hy) htu
          exact (add_lt_add_iff_left _).mpr h
  · intro a t hsz ha ht β hG
    cases t with
    | nil => exact Ord.CSet.zero_mem _ _
    | cons c d r =>
      simp only [size_cons] at hsz
      rw [val_cons]
      refine Ord.Clos.add ?_ ?_
      · by_cases hac : a ≤ c
        · have hmemc : c ∈ G a (cons c d r) := by
            rw [G_cons, if_pos hac]; exact List.mem_append_left _ (List.mem_cons_self ..)
          have hmemd : d ∈ G a (cons c d r) := by
            rw [G_cons, if_pos hac]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          have hGc : ∀ z ∈ G a c, z.val < β := by
            intro z hz
            refine hG z ?_
            rw [G_cons, if_pos hac]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append_left _ hz)))
          have hGd : ∀ z ∈ G a d, z.val < β := by
            intro z hz
            refine hG z ?_
            rw [G_cons, if_pos hac]
            exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append_right _ hz)))
          have hc : c.val ∈ Ord.CSet a.val β :=
            (ih (size a + size c) (by omega)).2 a c le_rfl ha (OT_fst ht) β hGc
          have hd : d.val ∈ Ord.CSet a.val β :=
            (ih (size a + size d) (by omega)).2 a d le_rfl ha (OT_snd ht) β hGd
          exact Ord.Clos.coll (e := ⟨d.val, hG d hmemd⟩) hc hd
        · have hcv : c.val < a.val :=
            (ih (size c) (by omega)).1 c a le_rfl (OT_fst ht) ha (lt_of_not_le hac)
          refine Ord.Clos.small ?_
          refine lt_of_lt_of_le (Ord.psi_lt_Omega_succ d.val c.val) ?_
          refine Ord.Omega_mono ?_
          rwa [← Order.succ_eq_add_one, Order.succ_le_iff]
      · have hGr : ∀ z ∈ G a r, z.val < β := by
          intro z hz
          exact hG z (by rw [G_cons]; exact List.mem_append_right _ hz)
        exact (ih (size a + size r) (by omega)).2 a r le_rfl ha (OT_tail ht) β hGr


/-- **The evaluation is strictly monotone on standard forms.**  This is the
correctness of the notation system. -/
theorem val_lt_val {x y : Term} (hx : OT x) (hy : OT y) (h : x < y) :
    x.val < y.val :=
  (main (size x)).1 x y le_rfl hx hy h

/-- The standard-form condition, semantically: the argument of a standard
principal term is reachable inside its own closure. -/
theorem val_mem_CSet_arg {a b : Term} (h : OT (psi a b)) :
    b.val ∈ Ord.CSet a.val b.val := by
  refine (main (size a + size b)).2 a b le_rfl (OT_fst h) (OT_snd h) b.val ?_
  intro z hz
  exact val_lt_val (OT_of_mem_G a b (OT_snd h) z hz) (OT_snd h) (OT_G_lt h z hz)

/-- The evaluation as an order-preserving map into the ordinals. -/
noncomputable def valHom : OrdHom OTLt (· < · : Ordinal → Ordinal → Prop) where
  map := Term.val
  map_lt := fun {_ _} h => val_lt_val h.1 h.2.1 h.2.2

/-- **The order on standard forms is well founded**, with no hypothesis. -/
theorem OTLt_wf : WellFounded OTLt := valHom.wf Ordinal.lt_wf

/-- Every standard principal term is accessible — the hypothesis that
`wellFounded_OTLt` was stated with. -/
theorem acc_principal (a b : Term) (_ : OT (psi a b)) : Acc OTLt (psi a b) :=
  OTLt_wf.apply _

example : WellFounded OTLt := wellFounded_OTLt acc_principal

/-! ## The standard forms are a well order -/

/-- Distinct standard forms name distinct ordinals. -/
theorem val_inj_of_OT {x y : Term} (hx : OT x) (hy : OT y) (h : x.val = y.val) :
    x = y := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · exact absurd h (val_lt_val hx hy hlt).ne
  · rfl
  · exact absurd h.symm (val_lt_val hy hx hlt).ne

theorem OTLt_irrefl (x : Term) : ¬ OTLt x x := fun h => lt_irrefl x h.2.2

theorem OTLt_trans {x y z : Term} (h₁ : OTLt x y) (h₂ : OTLt y z) : OTLt x z :=
  ⟨h₁.1, h₂.2.1, lt_trans h₁.2.2 h₂.2.2⟩

theorem OTLt_trichotomous {x y : Term} (hx : OT x) (hy : OT y) :
    OTLt x y ∨ x = y ∨ OTLt y x := by
  rcases lt_trichotomy x y with h | h | h
  · exact Or.inl ⟨hx, hy, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hy, hx, h⟩)

end Googology.Notation.ExBuchholz.Term
