import Googology.Notation.ExBuchholz.NF
import Googology.Notation.ExBuchholz.Level
import Googology.Notation.ExBuchholz.Mono
import Googology.Notation.ExBuchholz.FS

/-!
# `val` is onto `C_0(Λ)`

`Mono.lean` proves that `val` is strictly monotone on standard forms, so it is
injective there.  This file proves the other half: **every member of
`C_0(Λ)` is the value of a standard form.**  Together,

```
val : OT ≅ C_0(Λ)            (as ordered sets)
```

which is the statement the notation system is for.  In particular every
ordinal below `ψ_0(Λ)` is the value of exactly one standard form
(`existsUnique_OT_of_lt_psi_Lam`), and a standard form names a countable
ordinal exactly when it names one below `ψ_0(Λ)` (`val_lt_psi_Lam_iff`).

The proof is by induction on the closure `C_0(Λ)`.  The sum clause needs
normal-form addition, `addNF`: drop the summands of the left term that are
below the head of the right one.  The collapse clause needs, for standard `s`
and `e`, a standard form naming `ψ_s(e)`, and `psi_mem_Vals` supplies it by
induction on `e`:

* the argument is moved up to `M(e)`, the least member of `C_s(e)` at or above
  `e` — `Ord.psi_M_eq` says `ψ_s(M(e)) = ψ_s(e)`;
* `M(e)` is the value of a standard form, by `Ord.M_mem_of_comp` and
  `comp_M_mem_Vals` with `S` the set of values, which needs the collapse
  clause only below `e` — that is the induction;
* `M(e)` lies in its own closure (`Ord.M_mem_self`), and `G_lt_of_mem_CSet`
  turns that into the syntactic condition `G_s(M(e)) < M(e)`, so `ψ_s(M(e))`
  is a standard form.

`G_lt_of_mem_CSet` is the converse of the closure half of `Mono.main`:
`val X ∈ C_u(β)` implies that everything `G_u` collects from `X` is below `β`.
Its collapse case is `Ord.arg_mem_of_psi_mem`.
-/

namespace Googology.Notation.ExBuchholz.Term

open Ordinal

theorem lt_of_val_lt_OT {x y : Term} (hx : OT x) (hy : OT y) (h : val x < val y) : x < y := by
  rcases lt_trichotomy x y with hlt | rfl | hlt
  · exact hlt
  · exact absurd h (_root_.lt_irrefl _)
  · exact absurd (val_lt_val hy hx hlt) (not_lt.mpr h.le)

theorem val_le_val_OT {x y : Term} (hx : OT x) (hy : OT y) (h : x ≤ y) : val x ≤ val y := by
  rcases le_iff_lt_or_eq.mp h with hlt | rfl
  · exact (val_lt_val hx hy hlt).le
  · exact _root_.le_refl _

theorem val_t1_eq : val t1 = 1 := by
  rw [show t1 = psi nil nil from rfl, val_psi, val_nil, Ord.psi_zero_arg, Ord.Omega_zero]

theorem headLe_trans {p q t : Term} (h : HeadLe p t) (hpq : p ≤ q) : HeadLe q t := by
  cases t with
  | nil => trivial
  | cons c d u => exact le_trans h hpq

/-- The summands after the head of a standard form stay below `ω^(g+1)`,
where `ω^g` is the value of the head. -/
theorem val_lt_of_headLe : ∀ t : Term, OT t → ∀ c d : Term, OT (psi c d) →
    HeadLe (psi c d) t → ∀ g : Ordinal, val (psi c d) = ω ^ g → val t < ω ^ (g + 1) := by
  intro t
  induction t with
  | nil => intro _ c d _ _ g _; rw [val_nil]; exact Ordinal.opow_pos _ omega0_pos
  | cons c' d' t' _ _ iht =>
    intro hOT c d hOTp hle g hg
    have h1 : val (psi c' d') ≤ ω ^ g := hg ▸ val_le_val_OT (OT_head hOT) hOTp hle
    have h2 : val t' < ω ^ (g + 1) :=
      iht (OT_tail hOT) c d hOTp (headLe_trans (OT_headLe_tail hOT) hle) g hg
    rw [val_cons, ← val_psi]
    exact Ordinal.isPrincipal_add_omega0_opow (g + 1)
      (lt_of_le_of_lt h1 (Ord.opow_lt_opow_add_one g)) h2

/-! ### Reading the closure through `G` -/

/-- **`val X ∈ C_u(β)` forces everything `G_u` collects from `X` below `β`.**
This is the converse of the closure half of `Mono.main`. -/
theorem G_lt_of_mem_CSet : ∀ X : Term, OT X → ∀ U : Term, OT U → ∀ β : Ordinal.{0},
    val X ∈ Ord.CSet (val U) β → ∀ z ∈ G U X, val z < β := by
  intro X
  induction X with
  | nil => intro _ U _ β _ z hz; exact absurd hz List.not_mem_nil
  | cons c d r ihc ihd ihr =>
    intro hOT U hU β hmem z hz
    have hOTp : OT (psi c d) := OT_head hOT
    obtain ⟨g, hg⟩ := Ord.exists_opow_of_principal (Ord.isPrincipal_add_psi (val d) (val c))
      (ne_of_gt (Ord.psi_pos _ _))
    have hr : val r < ω ^ (g + 1) :=
      val_lt_of_headLe r (OT_tail hOT) c d hOTp (OT_headLe_tail hOT) g (by rw [val_psi]; exact hg)
    have hX : val (cons c d r) = ω ^ g + val r := by rw [val_cons, hg]
    have hX0 : val (cons c d r) ≠ 0 := by
      rw [hX]
      exact ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos g omega0_pos) (self_le_add_right _ _))
    obtain ⟨hpS, hrS⟩ := Ord.lead_tail_mem hmem hX0
    rw [hX, Ord.lead_opow_add hr, ← hg] at hpS
    rw [hX, Ord.tail_opow_add hr] at hrS
    rw [G_cons] at hz
    rcases List.mem_append.1 hz with hz1 | hz2
    · split_ifs at hz1 with hUc
      · have hle : val U ≤ val c := val_le_val_OT hU (OT_fst hOT) hUc
        obtain ⟨hdS, hdβ, hcS⟩ := Ord.arg_mem_of_psi_mem (val_lt_Lam U) (val_lt_Lam c) hle hpS
          (val_mem_CSet_arg hOTp)
        rcases List.mem_cons.1 hz1 with rfl | hz3
        · exact hdβ
        · rcases List.mem_append.1 hz3 with h | h
          · exact ihc (OT_fst hOT) U hU β hcS z h
          · exact ihd (OT_snd hOT) U hU β hdS z h
      · exact absurd hz1 List.not_mem_nil
    · exact ihr (OT_tail hOT) U hU β hrS z hz2

/-- **A collapse whose argument lies in its own closure is a standard form.** -/
theorem OT_psi_of_mem {U Z : Term} (hU : OT U) (hZ : OT Z)
    (h : val Z ∈ Ord.CSet (val U) (val Z)) : OT (psi U Z) :=
  OT_psi_of hU hZ (fun x hx => lt_of_val_lt_OT (OT_of_mem_G U Z hZ x hx) hZ
    (G_lt_of_mem_CSet Z hZ U hU (val Z) h x hx))

/-! ### Normal-form addition -/

/-- Addition of standard forms: the summands of the left term below the head of
the right one are absorbed. -/
def addNF : Term → Term → Term
  | nil, y => y
  | cons a b t, nil => cons a b t
  | cons a b t, cons c d u =>
      if psi a b < psi c d then cons c d u else cons a b (addNF t (cons c d u))

theorem OT_cons_of {a b t : Term} (hp : OT (psi a b)) (ht : OT t) (hle : HeadLe (psi a b) t) :
    OT (cons a b t) := by
  have hp' : isOT (cons a b nil) = true := hp
  have ht' : isOT t = true := ht
  show isOT (cons a b t) = true
  simp only [isOT, Bool.and_eq_true] at hp' ⊢
  obtain ⟨⟨⟨⟨ha, hb⟩, hG⟩, _⟩, _⟩ := hp'
  exact ⟨⟨⟨⟨ha, hb⟩, hG⟩, ht'⟩, descHead_of_headLe hle⟩

theorem le_of_not_lt_term {x y : Term} (h : ¬ x < y) : y ≤ x := by
  rcases lt_trichotomy y x with h1 | h1 | h1
  · exact le_of_lt h1
  · rw [h1]; exact le_refl x
  · exact absurd h1 h

/-- **`addNF` adds standard forms**, and keeps a bound on the head. -/
theorem addNF_spec : ∀ x : Term, OT x → ∀ y : Term, OT y →
    OT (addNF x y) ∧ val (addNF x y) = val x + val y ∧
      ∀ p, HeadLe p x → HeadLe p y → HeadLe p (addNF x y) := by
  intro x
  induction x with
  | nil =>
    intro _ y hy
    exact ⟨hy, by rw [val_nil, zero_add]; rfl, fun _ _ h => h⟩
  | cons a b t _ _ iht =>
    intro hx y hy
    cases y with
    | nil => exact ⟨hx, by rw [val_nil, add_zero]; rfl, fun _ h _ => h⟩
    | cons c d u =>
      by_cases h : psi a b < psi c d
      · have heq : addNF (cons a b t) (cons c d u) = cons c d u := by
          show (if psi a b < psi c d then _ else _) = _
          rw [if_pos h]
        rw [heq]
        refine ⟨hy, ?_, fun _ _ h => h⟩
        have hlt : cons a b t < psi c d := cons_lt_cons_iff.2 (Or.inl h)
        have hv : val (cons a b t) < val (psi c d) := val_lt_val hx (OT_head hy) hlt
        rw [val_psi] at hv
        rw [val_cons c d u, ← add_assoc, (Ord.isPrincipal_add_psi _ _).add_eq_right hv]
      · have heq : addNF (cons a b t) (cons c d u) = cons a b (addNF t (cons c d u)) := by
          show (if psi a b < psi c d then _ else _) = _
          rw [if_neg h]
        rw [heq]
        obtain ⟨h1, h2, h3⟩ := iht (OT_tail hx) (cons c d u) hy
        have hyle : HeadLe (psi a b) (cons c d u) := le_of_not_lt_term h
        refine ⟨OT_cons_of (OT_head hx) h1 (h3 _ (OT_headLe_tail hx) hyle), ?_,
          fun _ hp _ => hp⟩
        rw [val_cons, h2, val_cons a b t, add_assoc]

/-! ### The values of standard forms -/

/-- The values of standard forms. -/
def Vals : Set Ordinal.{0} := {x | ∃ X : Term, OT X ∧ val X = x}

theorem zero_mem_Vals : (0 : Ordinal.{0}) ∈ Vals := ⟨nil, by decide, rfl⟩

theorem add_mem_Vals {x y : Ordinal.{0}} (hx : x ∈ Vals) (hy : y ∈ Vals) : x + y ∈ Vals := by
  obtain ⟨X, hX, rfl⟩ := hx
  obtain ⟨Y, hY, rfl⟩ := hy
  obtain ⟨h1, h2, -⟩ := addNF_spec X hX Y hY
  exact ⟨_, h1, h2⟩

theorem one_mem_Vals : (1 : Ordinal.{0}) ∈ Vals := ⟨t1, by decide, val_t1_eq⟩

theorem Omega_mem_Vals {w : Ordinal.{0}} (hw : w ∈ Vals) : Ord.Omega w ∈ Vals := by
  obtain ⟨W, hW, rfl⟩ := hw
  exact ⟨psi W nil, OT_psi_nil hW, by rw [val_psi, val_nil, Ord.psi_zero_arg]⟩

/-- The principal summands of a value, and `M` of them, are values — granted
the collapse clause below `a`. -/
theorem comp_M_mem_Vals {c a : Ordinal.{0}} (ha : 0 < a)
    (hcoll : ∀ t y, t ∈ Vals → y ∈ Vals → y < a → Ord.psi y t ∈ Vals) :
    ∀ X : Term, OT X → ∀ g, Ord.Comp g (val X) →
      (ω : Ordinal) ^ g ∈ Vals ∧ Ord.M c a (ω ^ g) ∈ Vals := by
  intro X
  induction X with
  | nil => intro _ g hc; exact absurd hc (Ord.not_comp_zero g)
  | cons c' d r ihc ihd ihr =>
    intro hOT g hc
    rw [val_cons] at hc
    rcases hc.add with h | h
    · obtain ⟨h', hh⟩ := Ord.exists_opow_of_principal (Ord.isPrincipal_add_psi (val d) (val c'))
        (ne_of_gt (Ord.psi_pos _ _))
      rw [hh] at h
      rw [h.eq_of_opow, ← hh]
      have hOTp := OT_head hOT
      have hpV : Ord.psi (val d) (val c') ∈ Vals := ⟨psi c' d, hOTp, val_psi c' d⟩
      refine ⟨hpV, ?_⟩
      refine Ord.M_psi_mem ha (fun _ _ => add_mem_Vals) one_mem_Vals (fun w hw => Omega_mem_Vals hw)
        hcoll (val_lt_Lam c') (val_lt_Lam d) hpV ⟨c', OT_fst hOT, rfl⟩ ?_ ?_
      · exact Ord.M_mem_of_comp ha zero_mem_Vals (fun _ _ => add_mem_Vals) (val c')
          (val_lt_Lam c') (ihc (OT_fst hOT))
      · exact Ord.M_mem_of_comp ha zero_mem_Vals (fun _ _ => add_mem_Vals) (val d)
          (val_lt_Lam d) (ihd (OT_snd hOT))
    · exact ihr (OT_tail hOT) g h

/-- **The collapse of values is a value.**  The argument is moved up to
`M(e)`, which is a value by the induction on `e` and lies in its own closure,
so the collapse there is a standard form, and it names the same ordinal. -/
theorem psi_mem_Vals : ∀ e : Ordinal.{0}, ∀ s, s ∈ Vals → e ∈ Vals → Ord.psi e s ∈ Vals := by
  intro e
  induction e using WellFoundedLT.induction with
  | _ e IH =>
    intro s hs he
    obtain ⟨Sb, hSb, rfl⟩ := hs
    obtain ⟨E, hE, rfl⟩ := he
    rcases eq_or_ne (val E) 0 with h0 | h0
    · rw [h0, Ord.psi_zero_arg]
      exact Omega_mem_Vals ⟨Sb, hSb, rfl⟩
    · have hpos : 0 < val E := pos_iff_ne_zero.2 h0
      have hL := val_lt_Lam E
      have hcoll : ∀ t y, t ∈ Vals → y ∈ Vals → y < val E → Ord.psi y t ∈ Vals :=
        fun t y ht hy hya => IH y hya t ht hy
      have hm : Ord.M (val Sb) (val E) (val E) ∈ Vals :=
        Ord.M_mem_of_comp hpos zero_mem_Vals (fun _ _ => add_mem_Vals) (val E) hL
          (comp_M_mem_Vals hpos hcoll E hE)
      obtain ⟨Z, hZ, hvZ⟩ := hm
      refine ⟨psi Sb Z, OT_psi_of_mem hSb hZ ?_, ?_⟩
      · rw [hvZ]
        exact Ord.M_mem_self hpos hL
      · rw [val_psi, hvZ, Ord.psi_M_eq hpos hL]

/-! ### The theorem -/

/-- **Every member of `C_0(Λ)` is the value of a standard form.** -/
theorem mem_Vals_of_mem_CSet {x : Ordinal.{0}} (hx : x ∈ Ord.CSet 0 Lam) : x ∈ Vals := by
  induction hx with
  | small h =>
    rw [Ord.Omega_zero, Order.lt_one_iff] at h
    rw [h]
    exact zero_mem_Vals
  | add _ _ ihx ihy => exact add_mem_Vals ihx ihy
  | coll _ _ ihu ihe => exact psi_mem_Vals _ _ ihu ihe

/-- Every standard form names a member of `C_0(Λ)`. -/
theorem val_mem_CSet_Lam {X : Term} (h : OT X) : val X ∈ Ord.CSet 0 Lam := by
  have := (main (size nil + size X)).2 nil X le_rfl (by decide) h Lam (fun z _ => val_lt_Lam z)
  rwa [val_nil] at this

/-- **The values of the standard forms are exactly `C_0(Λ)`.** -/
theorem Vals_eq : Vals = Ord.CSet 0 Lam := by
  ext x
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact val_mem_CSet_Lam hX
  · exact mem_Vals_of_mem_CSet

/-- **Each member of `C_0(Λ)` is the value of exactly one standard form.** -/
theorem existsUnique_OT_of_mem {x : Ordinal.{0}} (hx : x ∈ Ord.CSet 0 Lam) :
    ∃! X : Term, OT X ∧ val X = x := by
  obtain ⟨X, hX, hv⟩ := mem_Vals_of_mem_CSet hx
  refine ⟨X, ⟨hX, hv⟩, fun Y hY => ?_⟩
  exact val_inj_of_OT hY.1 hX (by rw [hY.2, hv])

/-- **Every ordinal below `ψ_0(Λ)` is the value of exactly one standard form.** -/
theorem existsUnique_OT_of_lt_psi_Lam {α : Ordinal.{0}} (h : α < Ord.psi Lam 0) :
    ∃! X : Term, OT X ∧ val X = α :=
  existsUnique_OT_of_mem (Ord.mem_CSet_of_lt_psi h)

/-- **A standard form names a countable ordinal exactly when it names one below
`ψ_0(Λ)`.**  So `ψ_0(Λ)` is the supremum of what the countable standard forms
name, and they name every ordinal below it. -/
theorem val_lt_psi_Lam_iff {X : Term} (h : OT X) :
    val X < Ord.psi Lam 0 ↔ val X < Ord.Omega 1 := by
  constructor
  · intro hlt
    refine _root_.lt_trans hlt ?_
    have := Ord.psi_lt_Omega_succ Lam 0
    rwa [zero_add] at this
  · intro hlt
    refine Ord.lt_psi_of_mem (val_mem_CSet_Lam h) (Ord.card_le_of_lt_Omega_succ ?_)
    rwa [zero_add]

/-- On standard forms the term order is the value order. -/
theorem lt_iff_val_lt {X Y : Term} (hX : OT X) (hY : OT Y) : X < Y ↔ val X < val Y :=
  ⟨val_lt_val hX hY, lt_of_val_lt_OT hX hY⟩

/-- **The standard forms and `C_0(Λ)` are one set written two ways**: `val` is
a bijection, and by `lt_iff_val_lt` it carries the term order to the ordinal
order. -/
noncomputable def valEquiv : {X : Term // OT X} ≃ Ord.CSet 0 Lam where
  toFun X := ⟨val X.1, val_mem_CSet_Lam X.2⟩
  invFun x := ⟨Classical.choose (mem_Vals_of_mem_CSet x.2),
    (Classical.choose_spec (mem_Vals_of_mem_CSet x.2)).1⟩
  left_inv X := by
    apply Subtype.ext
    have h := Classical.choose_spec (mem_Vals_of_mem_CSet (val_mem_CSet_Lam X.2))
    exact val_inj_of_OT h.1 X.2 h.2
  right_inv x := Subtype.ext (Classical.choose_spec (mem_Vals_of_mem_CSet x.2)).2

end Googology.Notation.ExBuchholz.Term
