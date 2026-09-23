import Googology.Notation.ExBuchholz.System
import «Buchholz-1986».«Buchholz-1986-2.2»
import «Buchholz-1986».«Buchholz-1986-2.1-order»
import Bijectivity.«23-trans-bijectivity»

/-!
# Buchholz terms of pss-proof as extended Buchholz terms

[koteitan/pss-proof](https://github.com/koteitan/pss-proof) writes Buchholz's
terms as `BT`: a finite sum of principal terms `D_u a`, where the subscript
`u` is a natural number or `ω`.  The extended Buchholz terms here allow any
term as the subscript.  So a `BT` term is an extended term whose subscripts
are numerals or `ω`:

```
toTerm 0          = 0
toTerm (D_u a + t) = ψ_{sub u}(toTerm a) + toTerm t
sub n = the numeral n,   sub ω = tw   (the term ψ_0(1), whose value is ω)
```

The results:

* `toTerm_injective`: the map is injective;
* `lessBT_iff_lt`: it preserves and reflects the order;
* `isOT_toTerm`: a term is standard in pss-proof (`OT`, i.e. `OT_{Bω}`, `D_ω`
  allowed) exactly when its image is standard here;
* `toTerm_bijOn_OT`: it is a bijection from the standard terms onto the
  standard forms whose subscripts are all numerals or `tw`;
* `toTerm_bijOn_TransRange`: it is a bijection from the standard terms below
  `D_0 D_ω 0` (pss-proof's `TransRange`, the image of `Trans`) onto the standard
  forms below `ψ_0(Ω_ω)` whose subscripts are all numerals or `tw`.  These are
  countable: `lt_tW_of_lt_psiOmegaOmega`.
* `dfree_iff_natSubs`, `toTerm_bijOn_OT_B`: `D_ω`-free terms are the ones whose
  subscripts are all numerals.
-/

namespace Googology.Trans.PSS

open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-- The pss-proof term type. -/
abbrev BT := _root_.PSS.BT
/-- The pss-proof principal term type. -/
abbrev BP := _root_.PSS.BP

/-! ## Subscripts -/

/-- The subscript `u` as a term: a numeral, or `tw` for `ω`. -/
def sub (u : ℕ∞) : Term := ENat.recTopCoe tw numeral u

@[simp] theorem sub_top : sub ⊤ = tw := rfl
@[simp] theorem sub_coe (n : ℕ) : sub (n : ℕ∞) = numeral n := rfl

theorem numeral_succ (n : ℕ) : numeral (n + 1) = cons nil nil (numeral n) := rfl

theorem numeral_lt_numeral_iff : ∀ m n : ℕ, numeral m < numeral n ↔ m < n
  | 0, 0 => ⟨fun h => absurd h (lt_irrefl _), fun h => absurd h (Nat.lt_irrefl 0)⟩
  | 0, n + 1 => by
      simp only [Nat.zero_lt_succ, iff_true]
      exact nil_lt_cons _ _ _
  | m + 1, 0 => by
      simp only [Nat.not_lt_zero, iff_false]
      exact not_lt_nil _
  | m + 1, n + 1 => by
      rw [numeral_succ, numeral_succ, cons_lt_cons_iff, numeral_lt_numeral_iff m n]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact absurd h (lt_irrefl _)
        · omega
      · intro h; exact Or.inr ⟨rfl, by omega⟩

theorem numeral_injective : Function.Injective numeral := by
  intro m n h
  rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
  · have := (numeral_lt_numeral_iff m n).mpr hmn
    rw [h] at this; exact absurd this (lt_irrefl _)
  · exact hmn
  · have := (numeral_lt_numeral_iff n m).mpr hmn
    rw [h] at this; exact absurd this (lt_irrefl _)

theorem numeral_ne_tw (n : ℕ) : numeral n ≠ tw := by
  intro h
  have := numeral_lt_tw n
  rw [h] at this
  exact lt_irrefl _ this

theorem sub_lt_sub_iff : ∀ u v : ℕ∞, sub u < sub v ↔ u < v := by
  intro u v
  induction u using ENat.recTopCoe with
  | top =>
    induction v using ENat.recTopCoe with
    | top => simp only [sub_top, lt_self_iff_false, iff_false]; exact lt_irrefl _
    | coe n =>
      simp only [sub_top, sub_coe, not_top_lt, iff_false]
      exact lt_asymm (numeral_lt_tw n)
  | coe m =>
    induction v using ENat.recTopCoe with
    | top => simp only [sub_top, sub_coe, ENat.coe_lt_top, iff_true]; exact numeral_lt_tw m
    | coe n => simp only [sub_coe, Nat.cast_lt]; exact numeral_lt_numeral_iff m n

theorem sub_injective : Function.Injective sub := by
  intro u v h
  rcases lt_trichotomy u v with huv | huv | huv
  · have := (sub_lt_sub_iff u v).mpr huv
    rw [h] at this; exact absurd this (lt_irrefl _)
  · exact huv
  · have := (sub_lt_sub_iff v u).mpr huv
    rw [h] at this; exact absurd this (lt_irrefl _)

theorem sub_le_sub_iff (u v : ℕ∞) : sub u ≤ sub v ↔ u ≤ v := by
  rw [le_iff_lt_or_eq, _root_.le_iff_lt_or_eq, sub_lt_sub_iff, sub_injective.eq_iff]

theorem OT_sub (u : ℕ∞) : OT (sub u) := by
  induction u using ENat.recTopCoe with
  | top => decide
  | coe n => exact OT_numeral n

/-! ## The map -/

mutual
  /-- A pss-proof Buchholz term as an extended Buchholz term. -/
  def toTerm : BT → Term
    | .trm ps => toTermL ps
  /-- A list of principal terms as a sum. -/
  def toTermL : List BP → Term
    | [] => nil
    | .db u a :: ps => cons (sub u) (toTerm a) (toTermL ps)
end

@[simp] theorem toTerm_trm (ps : List BP) : toTerm (.trm ps) = toTermL ps := by
  simp [toTerm]
@[simp] theorem toTermL_nil : toTermL [] = nil := by simp [toTermL]
@[simp] theorem toTermL_cons (u : ℕ∞) (a : BT) (ps : List BP) :
    toTermL (.db u a :: ps) = cons (sub u) (toTerm a) (toTermL ps) := by
  simp [toTermL]

theorem toTerm_Dprin (u : ℕ∞) (a : BT) :
    toTerm (_root_.PSS.Dprin u a) = psi (sub u) (toTerm a) := by
  simp [_root_.PSS.Dprin]

theorem toTerm_BZero : toTerm _root_.PSS.BZero = nil := by
  simp [_root_.PSS.BZero]

/-! ## Order -/

mutual
  theorem lt_of_lessBT : ∀ a b : BT, _root_.PSS.lessBT a b = true → toTerm a < toTerm b
    | .trm as, .trm bs, h => by
        simp only [_root_.PSS.lessBT] at h
        simp only [toTerm_trm]
        exact lt_of_lessBPList as bs h
  theorem lt_of_lessBPList : ∀ as bs : List BP,
      _root_.PSS.lessBPList as bs = true → toTermL as < toTermL bs
    | [], [], h => by simp [_root_.PSS.lessBPList] at h
    | [], .db v b :: bs, _ => by
        simp only [toTermL_nil, toTermL_cons]
        exact nil_lt_cons _ _ _
    | _ :: _, [], h => by simp [_root_.PSS.lessBPList] at h
    | .db u a :: as, .db v b :: bs, h => by
        simp only [toTermL_cons]
        simp only [_root_.PSS.lessBPList, _root_.PSS.lessBP, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
        rw [cons_lt_cons_iff, psi_lt_psi_iff]
        rcases h with (h | ⟨rfl, h⟩) | ⟨h, h'⟩
        · exact Or.inl (Or.inl ((sub_lt_sub_iff u v).mpr h))
        · exact Or.inl (Or.inr ⟨rfl, lt_of_lessBT a b h⟩)
        · cases h
          exact Or.inr ⟨rfl, lt_of_lessBPList as bs h'⟩
end

/-- **The map is injective.** -/
theorem toTerm_injective : Function.Injective toTerm := by
  intro a b h
  rcases _root_.PSS.lessBT_linear_trichotomy a b with hab | hab | hab
  · have := lt_of_lessBT a b hab
    rw [h] at this; exact absurd this (lt_irrefl _)
  · exact hab
  · have := lt_of_lessBT b a hab
    rw [h] at this; exact absurd this (lt_irrefl _)

/-- **The map preserves and reflects the order.** -/
theorem lessBT_iff_lt (a b : BT) : _root_.PSS.lessBT a b = true ↔ toTerm a < toTerm b := by
  refine ⟨lt_of_lessBT a b, fun h => ?_⟩
  rcases _root_.PSS.lessBT_linear_trichotomy a b with hab | hab | hab
  · exact hab
  · subst hab; exact absurd h (lt_irrefl _)
  · exact absurd h (lt_asymm (lt_of_lessBT b a hab))

theorem leBT_iff_le (a b : BT) : _root_.PSS.leBT a b = true ↔ toTerm a ≤ toTerm b := by
  simp only [_root_.PSS.leBT, Bool.or_eq_true, beq_iff_eq, lessBT_iff_lt, le_iff_lt_or_eq,
    toTerm_injective.eq_iff]

/-! ## The collecting function `G` -/

/-- What `G` sees in a subscript is `0` or `1`. -/
theorem mem_G_sub {a x : Term} (u : ℕ∞) (hx : x ∈ G a (sub u)) : x = nil ∨ x = t1 := by
  induction u using ENat.recTopCoe with
  | top =>
    by_cases h : a ≤ nil
    · simp [G_cons, h] at hx; tauto
    · simp [G_cons, h] at hx
  | coe n => exact Or.inl (G_numeral_eq_nil n _ x hx)

mutual
  theorem G_of_gatherBT (u : ℕ∞) : ∀ (b y : BT),
      y ∈ _root_.PSS.gatherBT u b → toTerm y ∈ G (sub u) (toTerm b)
    | .trm ps, y, h => by
        simp only [_root_.PSS.gatherBT] at h
        simp only [toTerm_trm]
        exact G_of_gatherBPList u ps y h
  theorem G_of_gatherBPList (u : ℕ∞) : ∀ (ps : List BP) (y : BT),
      y ∈ _root_.PSS.gatherBPList u ps → toTerm y ∈ G (sub u) (toTermL ps)
    | [], y, h => by simp [_root_.PSS.gatherBPList] at h
    | .db v b :: ps, y, h => by
        simp only [_root_.PSS.gatherBPList, _root_.PSS.gatherBP, List.mem_append] at h
        simp only [toTermL_cons, G_cons, List.mem_append]
        rcases h with h | h
        · split at h
          · rename_i huv
            rw [if_pos ((sub_le_sub_iff u v).mpr (by simpa using huv))]
            simp only [List.mem_cons] at h
            rcases h with rfl | h
            · exact Or.inl (List.mem_cons_self ..)
            · exact Or.inl (List.mem_cons_of_mem _
                (List.mem_append_right _ (G_of_gatherBT u b y h)))
          · simp at h
        · exact Or.inr (G_of_gatherBPList u ps y h)
end

mutual
  theorem gatherBT_of_G (u : ℕ∞) : ∀ (b : BT) (x : Term), x ∈ G (sub u) (toTerm b) →
      (∃ y ∈ _root_.PSS.gatherBT u b, toTerm y = x) ∨ x = nil ∨ x = t1
    | .trm ps, x, h => by
        simp only [toTerm_trm] at h
        simp only [_root_.PSS.gatherBT]
        exact gatherBPList_of_G u ps x h
  theorem gatherBPList_of_G (u : ℕ∞) : ∀ (ps : List BP) (x : Term),
      x ∈ G (sub u) (toTermL ps) →
      (∃ y ∈ _root_.PSS.gatherBPList u ps, toTerm y = x) ∨ x = nil ∨ x = t1
    | [], x, h => by simp at h
    | .db v b :: ps, x, h => by
        simp only [toTermL_cons, G_cons, List.mem_append] at h
        simp only [_root_.PSS.gatherBPList, _root_.PSS.gatherBP, List.mem_append]
        rcases h with h | h
        · split at h
          · rename_i huv
            have huv' : u ≤ v := (sub_le_sub_iff u v).mp huv
            simp only [List.mem_cons, List.mem_append] at h
            rcases h with rfl | h | h
            · exact Or.inl ⟨b, Or.inl (by simp [huv']), rfl⟩
            · exact Or.inr (mem_G_sub v h)
            · rcases gatherBT_of_G u b x h with ⟨y, hy, rfl⟩ | h'
              · exact Or.inl ⟨y, Or.inl (by simp [huv', hy]), rfl⟩
              · exact Or.inr h'
          · simp at h
        · rcases gatherBPList_of_G u ps x h with ⟨y, hy, rfl⟩ | h'
          · exact Or.inl ⟨y, Or.inr hy, rfl⟩
          · exact Or.inr h'
end

theorem ne_nil_of_mem_G {a x y : Term} (h : x ∈ G a y) : y ≠ nil := by
  rintro rfl; simp at h

theorem t1_not_mem_G_t1 (a : Term) : t1 ∉ G a t1 := by
  simp only [G_cons, G_nil, List.append_nil]
  split <;> simp

theorem t1_lt_of_ne {y : Term} (h0 : y ≠ nil) (h1 : y ≠ t1) : t1 < y := by
  cases y with
  | nil => exact absurd rfl h0
  | cons c d t =>
    rw [cons_lt_cons_iff, psi_lt_psi_iff]
    by_cases hc : c = nil
    · subst hc
      by_cases hd : d = nil
      · subst hd
        refine Or.inr ⟨rfl, ?_⟩
        cases t with
        | nil => exact absurd rfl h1
        | cons _ _ _ => exact nil_lt_cons _ _ _
      · refine Or.inl (Or.inr ⟨rfl, ?_⟩)
        cases d with
        | nil => exact absurd rfl hd
        | cons _ _ _ => exact nil_lt_cons _ _ _
    · refine Or.inl (Or.inl ?_)
      cases c with
      | nil => exact absurd rfl hc
      | cons _ _ _ => exact nil_lt_cons _ _ _

/-- The side condition of a standard principal term corresponds. -/
theorem G_cond_iff (u : ℕ∞) (b : BT) :
    (∀ x ∈ G (sub u) (toTerm b), x < toTerm b) ↔
      (∀ y ∈ _root_.PSS.gatherBT u b, _root_.PSS.lessBT y b = true) := by
  constructor
  · intro h y hy
    exact (lessBT_iff_lt y b).mpr (h _ (G_of_gatherBT u b y hy))
  · intro h x hx
    rcases gatherBT_of_G u b x hx with ⟨y, hy, rfl⟩ | rfl | rfl
    · exact (lessBT_iff_lt y b).mp (h y hy)
    · cases hb : toTerm b with
      | nil => exact absurd hb (ne_nil_of_mem_G hx)
      | cons _ _ _ => exact nil_lt_cons _ _ _
    · refine t1_lt_of_ne (ne_nil_of_mem_G hx) ?_
      intro hb
      rw [hb] at hx
      exact t1_not_mem_G_t1 _ hx

/-! ## Standard forms -/

mutual
  theorem isOT_toTerm_iff : ∀ t : BT, isOT (toTerm t) = true ↔ _root_.PSS.isOT_BT t = true
    | .trm ps => by
        simp only [toTerm_trm, _root_.PSS.isOT_BT, Bool.and_eq_true]
        exact isOT_toTermL_iff ps
  theorem isOT_toTermL_iff : ∀ ps : List BP,
      isOT (toTermL ps) = true ↔
        (_root_.PSS.isOT_BPList ps = true ∧ _root_.PSS.descP ps = true)
    | [] => by simp [isOT, _root_.PSS.isOT_BPList, _root_.PSS.descP]
    | .db u a :: ps => by
        have ha := isOT_toTerm_iff a
        have hps := isOT_toTermL_iff ps
        have hG := G_cond_iff u a
        have hsub : isOT (sub u) = true := OT_sub u
        simp only [toTermL_cons, isOT, Bool.and_eq_true, List.all_eq_true,
          decide_eq_true_eq, hsub, true_and]
        simp only [_root_.PSS.isOT_BPList, _root_.PSS.isOT_BP, Bool.and_eq_true,
          List.all_eq_true]
        rw [ha, hps, hG]
        cases ps with
        | nil =>
          simp [descHead, head?, _root_.PSS.descP]
        | cons q qs =>
          cases q with
          | db v b =>
            have hd : descHead (sub u) (toTerm a) (toTermL (.db v b :: qs)) = true ↔
                _root_.PSS.leBT (.trm [.db v b]) (.trm [.db u a]) = true := by
              rw [leBT_iff_le]
              simp [descHead, head?, toTermL_cons]
            rw [hd]
            simp only [_root_.PSS.descP, Bool.and_eq_true]
            tauto
end

/-- **Standard terms correspond.** -/
theorem isOT_toTerm (t : BT) : isOT (toTerm t) = _root_.PSS.isOT_BT t :=
  Bool.eq_iff_iff.mpr (isOT_toTerm_iff t)

theorem OT_toTerm_iff (t : BT) : OT (toTerm t) ↔ t ∈ _root_.PSS.OT :=
  isOT_toTerm_iff t

/-! ## The image -/

/-- A subscript that is a numeral or `tw`. -/
def NatOmegaSub (a : Term) : Prop := (∃ n : ℕ, a = numeral n) ∨ a = tw

/-- Every subscript in the term, at any depth, is a numeral or `tw`.
(Subscripts are not searched inside: they must themselves be numerals or `tw`.) -/
def NatOmegaSubs : Term → Prop
  | nil => True
  | cons a b t => NatOmegaSub a ∧ NatOmegaSubs b ∧ NatOmegaSubs t

/-- Every subscript in the term, at any depth, is a numeral. -/
def NatSubs : Term → Prop
  | nil => True
  | cons a b t => (∃ n : ℕ, a = numeral n) ∧ NatSubs b ∧ NatSubs t

theorem natOmegaSub_sub (u : ℕ∞) : NatOmegaSub (sub u) := by
  induction u using ENat.recTopCoe with
  | top => exact Or.inr rfl
  | coe n => exact Or.inl ⟨n, rfl⟩

mutual
  theorem natOmegaSubs_toTerm : ∀ t : BT, NatOmegaSubs (toTerm t)
    | .trm ps => by simpa using natOmegaSubs_toTermL ps
  theorem natOmegaSubs_toTermL : ∀ ps : List BP, NatOmegaSubs (toTermL ps)
    | [] => by simp [NatOmegaSubs]
    | .db u a :: ps => by
        simp only [toTermL_cons, NatOmegaSubs]
        exact ⟨natOmegaSub_sub u, natOmegaSubs_toTerm a, natOmegaSubs_toTermL ps⟩
end

/-- The subscript read back. -/
noncomputable def unsub (a : Term) : ℕ∞ := if a = tw then ⊤ else (numVal a : ℕ∞)

theorem numVal_numeral : ∀ n : ℕ, numVal (numeral n) = n
  | 0 => rfl
  | n + 1 => by rw [numeral_succ]; show numVal (numeral n) + 1 = n + 1; rw [numVal_numeral n]

theorem sub_unsub {a : Term} (h : NatOmegaSub a) : sub (unsub a) = a := by
  rcases h with ⟨n, rfl⟩ | rfl
  · rw [unsub, if_neg (numeral_ne_tw n), numVal_numeral]; rfl
  · rfl

/-- The inverse map, on terms whose subscripts are numerals or `tw`. -/
noncomputable def ofTerm : Term → BT
  | nil => .trm []
  | cons a b t => .trm (.db (unsub a) (ofTerm b) :: _root_.PSS.untrm (ofTerm t))

theorem toTermL_untrm (s : BT) : toTermL (_root_.PSS.untrm s) = toTerm s := by
  cases s; simp [_root_.PSS.untrm]

theorem toTerm_ofTerm : ∀ x : Term, NatOmegaSubs x → toTerm (ofTerm x) = x
  | nil, _ => by simp [ofTerm]
  | cons a b t, h => by
      obtain ⟨ha, hb, ht⟩ := h
      simp only [ofTerm, toTerm_trm, toTermL_cons, toTermL_untrm, sub_unsub ha,
        toTerm_ofTerm b hb, toTerm_ofTerm t ht]

theorem range_toTerm : Set.range toTerm = {x | NatOmegaSubs x} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩; exact natOmegaSubs_toTerm t
  · intro h; exact ⟨ofTerm x, toTerm_ofTerm x h⟩

/-- **The standard terms of pss-proof are exactly the standard forms whose
subscripts are numerals or `tw`.** -/
theorem toTerm_bijOn_OT :
    Set.BijOn toTerm _root_.PSS.OT {x | OT x ∧ NatOmegaSubs x} := by
  refine ⟨fun t ht => ⟨(OT_toTerm_iff t).mpr ht, natOmegaSubs_toTerm t⟩,
    toTerm_injective.injOn, ?_⟩
  rintro x ⟨hx, hs⟩
  refine ⟨ofTerm x, ?_, toTerm_ofTerm x hs⟩
  rw [← OT_toTerm_iff, toTerm_ofTerm x hs]
  exact hx

/-! ## Below `D_0 D_ω 0` -/

/-- `ψ_0(Ω_ω)` as a term. -/
abbrev psiOmegaOmega : Term := psi nil (psi tw nil)

theorem sub_zero : sub 0 = nil := rfl

theorem toTerm_DzeroDomegaZero : toTerm Bijectivity.DzeroDomegaZero = psiOmegaOmega := by
  simp [Bijectivity.DzeroDomegaZero, _root_.PSS.Dprin, sub_zero]

/-- Below `ψ_0(Ω_ω)` is below `Ω`: these forms are countable. -/
theorem lt_tW_of_lt_psiOmegaOmega {x : Term} (h : x < psiOmegaOmega) : x < tW :=
  lt_trans h (by decide)

/-- **The standard terms below `D_0 D_ω 0` are exactly the standard forms
below `ψ_0(Ω_ω)` whose subscripts are numerals or `tw`.**  The left side is
`TransRange`, the image of pss-proof's `Trans` on the standard pair
sequences. -/
theorem toTerm_bijOn_TransRange :
    Set.BijOn toTerm Bijectivity.TransRange
      {x | OT x ∧ NatOmegaSubs x ∧ x < psiOmegaOmega} := by
  refine ⟨fun t ht => ⟨(OT_toTerm_iff t).mpr ht.1, natOmegaSubs_toTerm t, ?_⟩,
    toTerm_injective.injOn, ?_⟩
  · rw [← toTerm_DzeroDomegaZero, ← lessBT_iff_lt]; exact ht.2
  · rintro x ⟨hx, hs, hlt⟩
    refine ⟨ofTerm x, ⟨?_, ?_⟩, toTerm_ofTerm x hs⟩
    · show ofTerm x ∈ _root_.PSS.OT
      rw [← OT_toTerm_iff, toTerm_ofTerm x hs]; exact hx
    · rw [lessBT_iff_lt, toTerm_ofTerm x hs, toTerm_DzeroDomegaZero]; exact hlt

/-! ## `D_ω`-free terms -/

mutual
  theorem dfree_iff_natSubs : ∀ t : BT, _root_.PSS.dfree_BT t = true ↔ NatSubs (toTerm t)
    | .trm ps => by
        simp only [_root_.PSS.dfree_BT, toTerm_trm]
        exact dfreeL_iff_natSubs ps
  theorem dfreeL_iff_natSubs : ∀ ps : List BP,
      _root_.PSS.dfree_BPList ps = true ↔ NatSubs (toTermL ps)
    | [] => by simp [_root_.PSS.dfree_BPList, NatSubs]
    | .db u a :: ps => by
        simp only [_root_.PSS.dfree_BPList, _root_.PSS.dfree_BP, Bool.and_eq_true,
          toTermL_cons, NatSubs, bne_iff_ne, ne_eq]
        rw [dfree_iff_natSubs a, dfreeL_iff_natSubs ps]
        have hu : ¬ u = ⊤ ↔ ∃ n : ℕ, sub u = numeral n := by
          induction u using ENat.recTopCoe with
          | top => simp only [not_true_eq_false, sub_top, false_iff, not_exists]
                   exact fun n h => numeral_ne_tw n h.symm
          | coe m => simp only [ENat.coe_ne_top, not_false_eq_true, sub_coe, true_iff]
                     exact ⟨m, rfl⟩
        rw [hu]
        tauto
end

theorem natOmegaSubs_of_natSubs : ∀ {x : Term}, NatSubs x → NatOmegaSubs x
  | nil, _ => trivial
  | cons _ _ _, ⟨ha, hb, ht⟩ =>
      ⟨Or.inl ha, natOmegaSubs_of_natSubs hb, natOmegaSubs_of_natSubs ht⟩

/-- **The `D_ω`-free standard terms (`OT_B`) are exactly the standard forms whose
subscripts are all numerals.** -/
theorem toTerm_bijOn_OT_B :
    Set.BijOn toTerm _root_.PSS.OT_B {x | OT x ∧ NatSubs x} := by
  refine ⟨fun t ht => ⟨(OT_toTerm_iff t).mpr ht.1, (dfree_iff_natSubs t).mp ht.2⟩,
    toTerm_injective.injOn, ?_⟩
  rintro x ⟨hx, hs⟩
  have hs' := natOmegaSubs_of_natSubs hs
  refine ⟨ofTerm x, ⟨?_, ?_⟩, toTerm_ofTerm x hs'⟩
  · show ofTerm x ∈ _root_.PSS.OT
    rw [← OT_toTerm_iff, toTerm_ofTerm x hs']; exact hx
  · show _root_.PSS.dfree_BT (ofTerm x) = true
    rw [dfree_iff_natSubs, toTerm_ofTerm x hs']; exact hs

end Googology.Trans.PSS
