import Googology.Trans.PSS.Expand
import Googology.Trans.PSS.Terms
import Googology.Trans.BMS.RankVal
import Googology.Notation.ExBuchholz.Onto
import Googology.Rank
import «6».«6.7-standard-prefix»
import Bijectivity.«15-successor-fseq»

/-!
# Pair sequences: the rank is the value of the term

This file gives the pair sequence system `pairL` an ordinal, and proves that
the ordinal is the rank.

The term of a pair sequence `M` is `pairTerm M = toTerm (Trans M)`: first
pss-proof's `Trans`, then the map of `Terms.lean` into extended Buchholz
terms.  The states of `pairL` are the standard pair sequences of pss-proof and
the empty list (`isPair_iff`).  The empty list is one extra state at the
bottom.  So the ordinal of a state is

```
pairOrdL []  = 0
pairOrdL M   = 1 + val (pairTerm M)      (M ≠ [])
```

`1 + α` is `α + 1` when `α` is finite and `α` when `α` is infinite.

The results:

* `toTerm_bijOn_TransRange_OT`: `toTerm` is a bijection from `TransRange` onto
  all standard forms below `ψ_0(Ω_ω)`.  The key step is
  `natSubs_of_lt_psiOmegaOmega`: a standard form below `ψ_0(Ω_ω)` has only
  numerals as subscripts.
* `pairTerm_bijOn`: `pairTerm` is a bijection from the standard pair sequences
  onto the standard forms below `ψ_0(Ω_ω)`, and `ltPS_iff_pairTerm_lt`: it
  keeps the lexicographic order.
* `typein_ctpsLt`: the order type of the standard pair sequences below `M` is
  `val (pairTerm M)`.
* `rank_pairL_eq`: the rank of a state is `pairOrdL`.  `typein_pairLt` and
  `rank_eq_typein`: this is also the order type of the states below it.
* The columns of the ordinal table, for `pairOrdEval`:
  defined (`pairOrdEval`, and `val_pairOrdTerm` for the form `val ∘ t`),
  injective (`pairOrd_injective`), surjective onto the ordinals below
  `ψ_0(Ω_ω)` (`range_pairOrd`, `val_psiOmegaOmega`), decreasing
  (`pairOrdEval.val_lt`), equal to the rank (`rank_pairL_eq`,
  `pairOrdEval_eq_rankEval`), order-preserving (`ltPS_iff_pairOrd_lt`).

The rank needs that expansion is cofinal below a state: every standard `N < M`
is at most some `M[n]` (`exists_le_oper`).  It comes from pss-proof's
`ltPS_ltExpPS`.
-/

namespace Googology.Trans.PSS

open Googology.Trans.BMS (pairL PairState expand2L pairL_wf pairL_step_val)
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term
open Bijectivity (CTPS)

/-! ## Standard forms below `ψ_0(Ω_ω)` -/

/-- `Ω_ω` as a term. -/
abbrev tOmegaW : Term := psi tw nil

theorem eq_nil_of_lt_t1 : ∀ {x : Term}, x < t1 → x = nil
  | nil, _ => rfl
  | cons a b t, h => by
    exfalso
    rcases cons_lt_cons_iff.mp h with h1 | ⟨_, h2⟩
    · rcases psi_lt_psi_iff.mp h1 with h3 | ⟨_, h4⟩
      · exact not_lt_nil _ h3
      · exact not_lt_nil _ h4
    · exact not_lt_nil _ h2

theorem sub_le_of_psi_le {a b c d : Term} (h : psi a b ≤ psi c d) : a ≤ c := by
  rcases le_iff_lt_or_eq.mp h with h | h
  · rcases psi_lt_psi_iff.mp h with h | ⟨rfl, _⟩
    · exact le_of_lt h
    · exact le_refl _
  · injection h with h1
    rw [h1]
    exact le_refl _

/-- A standard form below `ω` is a numeral. -/
theorem numeral_of_lt_tw : ∀ c : Term, OT c → c < tw → ∃ n, c = numeral n
  | nil, _, _ => ⟨0, rfl⟩
  | cons a b t, hc, hlt => by
    have hab : a = nil ∧ b = nil := by
      rcases cons_lt_cons_iff.mp hlt with h1 | ⟨_, h2⟩
      · rcases psi_lt_psi_iff.mp h1 with h3 | ⟨h3, h4⟩
        · exact absurd h3 (not_lt_nil _)
        · exact ⟨h3, eq_nil_of_lt_t1 h4⟩
      · exact absurd h2 (not_lt_nil _)
    obtain ⟨rfl, rfl⟩ := hab
    have ht : t < tw := by
      cases t with
      | nil => exact nil_lt_cons _ _ _
      | cons c d u =>
        have hle := OT_tail_head_le hc
        have hcd : c = nil ∧ d = nil := by
          rcases le_iff_lt_or_eq.mp hle with h | h
          · exact absurd (eq_nil_of_lt_t1 h) (by intro h'; cases h')
          · injection h with h1 h2
            exact ⟨h1, h2⟩
        obtain ⟨rfl, rfl⟩ := hcd
        exact cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inr ⟨rfl, nil_lt_cons _ _ _⟩)))
    obtain ⟨n, rfl⟩ := numeral_of_lt_tw t (OT_tail hc) ht
    exact ⟨n + 1, rfl⟩

theorem lt_tOmegaW_of_sub {c d t : Term} (h : c < tw) : cons c d t < tOmegaW :=
  cons_lt_cons_iff.mpr (Or.inl (psi_lt_psi_iff.mpr (Or.inl h)))

theorem sub_lt_tw_of_lt {c d t : Term} (h : cons c d t < tOmegaW) : c < tw := by
  rcases cons_lt_cons_iff.mp h with h1 | ⟨_, h2⟩
  · rcases psi_lt_psi_iff.mp h1 with h3 | ⟨_, h4⟩
    · exact h3
    · exact absurd h4 (not_lt_nil _)
  · exact absurd h2 (not_lt_nil _)

/-- A standard form below `Ω_ω`, whose collected arguments are also below
`Ω_ω`, has only numerals as subscripts. -/
theorem natSubs_of_G_lt : ∀ z : Term, OT z → z < tOmegaW →
    (∀ e ∈ G nil z, e < tOmegaW) → NatSubs z
  | nil, _, _, _ => trivial
  | cons c d t, hz, hlt, hG => by
    have hG' : G nil (cons c d t) = (d :: (G nil c ++ G nil d)) ++ G nil t := by
      rw [G_cons, if_pos (nil_le c)]
    have hc := sub_lt_tw_of_lt hlt
    have ht : t < tOmegaW := by
      cases t with
      | nil => exact nil_lt_cons _ _ _
      | cons c' d' t' =>
        apply lt_tOmegaW_of_sub
        rcases le_iff_lt_or_eq.mp (sub_le_of_psi_le (OT_tail_head_le hz)) with h | h
        · exact lt_trans h hc
        · rw [h]; exact hc
    refine ⟨numeral_of_lt_tw c (OT_fst hz) hc, ?_, ?_⟩
    · exact natSubs_of_G_lt d (OT_snd hz) (hG d (by rw [hG']; simp))
        (fun e he => hG e (by rw [hG']; simp [he]))
    · exact natSubs_of_G_lt t (OT_tail hz) ht (fun e he => hG e (by rw [hG']; simp [he]))

/-- A standard form whose principal terms are all `ψ_0(d)` with `d < Ω_ω` has
only numerals as subscripts. -/
theorem natSubs_of_head : ∀ x : Term, OT x →
    (∀ c d t, x = cons c d t → c = nil ∧ d < tOmegaW) → NatSubs x
  | nil, _, _ => trivial
  | cons c d t, hx, h => by
    obtain ⟨rfl, hd⟩ := h c d t rfl
    have hGd : ∀ e ∈ G nil d, e < d := OT_G_lt (OT_head hx)
    refine ⟨⟨0, rfl⟩, natSubs_of_G_lt d (OT_snd hx) hd (fun e he => lt_trans (hGd e he) hd),
      natSubs_of_head t (OT_tail hx) ?_⟩
    rintro c' d' t' rfl
    rcases le_iff_lt_or_eq.mp (OT_tail_head_le hx) with h' | h'
    · rcases psi_lt_psi_iff.mp h' with h1 | ⟨h1, h2⟩
      · exact absurd h1 (not_lt_nil _)
      · exact ⟨h1, lt_trans h2 hd⟩
    · injection h' with h1 h2
      exact ⟨h1, h2 ▸ hd⟩

/-- **A standard form below `ψ_0(Ω_ω)` has only numerals as subscripts.** -/
theorem natSubs_of_lt_psiOmegaOmega {x : Term} (hx : OT x) (hlt : x < psiOmegaOmega) :
    NatSubs x := by
  refine natSubs_of_head x hx ?_
  rintro c d t rfl
  rcases cons_lt_cons_iff.mp hlt with h | ⟨_, h'⟩
  · rcases psi_lt_psi_iff.mp h with h1 | ⟨h1, h2⟩
    · exact absurd h1 (not_lt_nil _)
    · exact ⟨h1, h2⟩
  · exact absurd h' (not_lt_nil _)

/-- **`toTerm` is a bijection from `TransRange` onto all standard forms below
`ψ_0(Ω_ω)`.** -/
theorem toTerm_bijOn_TransRange_OT :
    Set.BijOn toTerm Bijectivity.TransRange {x | OT x ∧ x < psiOmegaOmega} := by
  have h := toTerm_bijOn_TransRange
  refine ⟨fun t ht => ⟨(h.mapsTo ht).1, (h.mapsTo ht).2.2⟩, h.injOn, ?_⟩
  rintro x ⟨hx, hlt⟩
  exact h.surjOn ⟨hx, natOmegaSubs_of_natSubs (natSubs_of_lt_psiOmegaOmega hx hlt), hlt⟩

/-! ## The term of a standard pair sequence -/

/-- The extended Buchholz term of a pair sequence: pss-proof's `Trans`, then
`toTerm`. -/
def pairTerm (M : List (ℕ × ℕ)) : Term := toTerm (_root_.PSS.Trans M)

theorem ctps_ne_nil {M : List (ℕ × ℕ)} (h : CTPS M) : M ≠ [] := _root_.PSS.STPS_TPS M h.1

theorem ctps_single {M : List (ℕ × ℕ)} (h : CTPS M) (hL : M.length = 1) : M = [(0, 0)] := by
  cases M with
  | nil => simp at hL
  | cons x t =>
    cases t with
    | nil =>
      have hx : x = (0, 0) := h.2
      rw [hx]
    | cons _ _ => simp at hL

theorem pairTerm_mem {M : List (ℕ × ℕ)} (hM : CTPS M) :
    OT (pairTerm M) ∧ pairTerm M < psiOmegaOmega :=
  toTerm_bijOn_TransRange_OT.mapsTo (Bijectivity.trans_mapsTo hM)

theorem OT_pairTerm {M : List (ℕ × ℕ)} (hM : CTPS M) : OT (pairTerm M) := (pairTerm_mem hM).1

theorem pairTerm_lt {M : List (ℕ × ℕ)} (hM : CTPS M) : pairTerm M < psiOmegaOmega :=
  (pairTerm_mem hM).2

theorem pairTerm_single : pairTerm [(0, 0)] = nil := by
  rw [pairTerm, Bijectivity.Trans_zero_singleton', toTerm_BZero]

/-- **`pairTerm` keeps the lexicographic order.** -/
theorem ltPS_iff_pairTerm_lt {M N : List (ℕ × ℕ)} (hM : CTPS M) (hN : CTPS N) :
    M <ₚ N ↔ pairTerm M < pairTerm N := by
  rw [Bijectivity.trans_order_iso hM hN, lessBT_iff_lt]
  rfl

theorem ltPS_iff_val_lt {M N : List (ℕ × ℕ)} (hM : CTPS M) (hN : CTPS N) :
    M <ₚ N ↔ val (pairTerm M) < val (pairTerm N) := by
  rw [ltPS_iff_pairTerm_lt hM hN]
  exact lt_iff_val_lt (OT_pairTerm hM) (OT_pairTerm hN)

/-- **`pairTerm` is a bijection from the standard pair sequences onto the
standard forms below `ψ_0(Ω_ω)`.** -/
theorem pairTerm_bijOn : Set.BijOn pairTerm {M | CTPS M} {x | OT x ∧ x < psiOmegaOmega} :=
  Set.BijOn.comp toTerm_bijOn_TransRange_OT Bijectivity.trans_bijOn

theorem exists_ctps_of_lt {x : Term} (hx : OT x) (hlt : x < psiOmegaOmega) :
    ∃ M, CTPS M ∧ pairTerm M = x :=
  pairTerm_bijOn.surjOn ⟨hx, hlt⟩

theorem val_pairTerm_injOn : Set.InjOn (fun N => val (pairTerm N)) {N | CTPS N} := by
  intro N hN N' hN' h
  apply pairTerm_bijOn.injOn hN hN'
  rcases Term.lt_trichotomy (pairTerm N) (pairTerm N') with h1 | h1 | h1
  · exact absurd h (_root_.ne_of_lt (val_lt_val (OT_pairTerm hN) (OT_pairTerm hN') h1))
  · exact h1
  · exact absurd h (_root_.ne_of_lt (val_lt_val (OT_pairTerm hN') (OT_pairTerm hN) h1)).symm

/-- **Below a standard pair sequence `M`, the standard pair sequences are the
ordinals below `val (pairTerm M)`.** -/
theorem val_pairTerm_bijOn_below {M : List (ℕ × ℕ)} (hM : CTPS M) :
    Set.BijOn (fun N => val (pairTerm N)) {N | CTPS N ∧ N <ₚ M}
      (Set.Iio (val (pairTerm M))) := by
  refine ⟨fun N hN => (ltPS_iff_val_lt hN.1 hM).mp hN.2,
    fun N hN N' hN' h => val_pairTerm_injOn hN.1 hN'.1 h, ?_⟩
  intro α hα
  obtain ⟨Y, ⟨hY, hYM, hvY⟩, -⟩ :=
    existsUnique_OT_lt_of_lt_val (OT_pairTerm hM) (lt_tW_of_lt_psiOmegaOmega (pairTerm_lt hM)) hα
  obtain ⟨N, hN, rfl⟩ := exists_ctps_of_lt hY (lt_trans hYM (pairTerm_lt hM))
  exact ⟨N, ⟨hN, (ltPS_iff_pairTerm_lt hN hM).mpr hYM⟩, hvY⟩

/-! ## Cofinality of expansion -/

/-- **Expansion is cofinal below a standard pair sequence**: every standard
`N < M` is at most some `M[n]`. -/
theorem exists_le_oper {M N : List (ℕ × ℕ)} (hN : CTPS N) (hM : CTPS M) (h : N <ₚ M) :
    ∃ n, 1 ≤ n ∧ N ≤ₚ _root_.PSS.oper M n := by
  obtain ⟨a, hne, ha, rfl⟩ := Bijectivity.ltPS_ltExpPS hN hM h
  cases a with
  | nil => exact absurd rfl hne
  | cons n a =>
    exact ⟨n, ha n (by simp),
      Bijectivity.expand_lePS a (_root_.PSS.oper M n) (fun m hm => ha m (by simp [hm]))⟩

/-! ## Order types -/

section OrderType

variable {α : Type} (r : α → α → Prop) (g : α → Ordinal.{0})

/-- A map into the ordinals that is injective and turns `r` into `<`, as a
relation embedding. -/
def relEmbOfIff (hinj : Function.Injective g) (hg : ∀ a b, r a b ↔ g a < g b) :
    r ↪r (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  ⟨⟨g, hinj⟩, fun {a b} => (hg a b).symm⟩

theorem isWellOrder_of_iff (hinj : Function.Injective g) (hg : ∀ a b, r a b ↔ g a < g b) :
    IsWellOrder α r :=
  (relEmbOfIff r g hinj hg).isWellOrder

/-- If the image of `g` is closed downward, `g` is the order type of the
initial segments. -/
theorem typein_eq_of_iff [IsWellOrder α r] (hinj : Function.Injective g)
    (hg : ∀ a b, r a b ↔ g a < g b) (hd : ∀ a β, β < g a → ∃ b, g b = β) (a : α) :
    Ordinal.typein r a = g a := by
  let f : InitialSeg r (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
    { toRelEmbedding := relEmbOfIff r g hinj hg
      mem_range_of_rel' := fun a β h => by
        obtain ⟨b, hb⟩ := hd a β h
        exact ⟨b, hb⟩ }
  exact InitialSeg.eq ((Ordinal.typein r : PrincipalSeg r (· < ·)) :
    InitialSeg r (· < · : Ordinal.{0} → Ordinal.{0} → Prop)) f a

theorem injective_of_iff (htri : ∀ a b, r a b ∨ a = b ∨ r b a)
    (hg : ∀ a b, r a b ↔ g a < g b) : Function.Injective g := by
  intro a b h
  rcases htri a b with h1 | h1 | h1
  · exact absurd h (_root_.ne_of_lt ((hg a b).mp h1))
  · exact h1
  · exact absurd h (_root_.ne_of_lt ((hg b a).mp h1)).symm

end OrderType

theorem ltPS_trichotomy (M N : List (ℕ × ℕ)) : M <ₚ N ∨ M = N ∨ N <ₚ M := by
  rcases Bijectivity.lePS_total M N with h | h
  · rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · rcases h with h | h
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr h)

/-- The lexicographic order on the standard pair sequences. -/
def CtpsLt (a b : {M : List (ℕ × ℕ) // CTPS M}) : Prop := a.1 <ₚ b.1

theorem ctpsLt_iff (a b : {M : List (ℕ × ℕ) // CTPS M}) :
    CtpsLt a b ↔ (fun c : {M : List (ℕ × ℕ) // CTPS M} => val (pairTerm c.1)) a <
      (fun c : {M : List (ℕ × ℕ) // CTPS M} => val (pairTerm c.1)) b :=
  ltPS_iff_val_lt a.2 b.2

theorem ctps_val_injective :
    Function.Injective (fun c : {M : List (ℕ × ℕ) // CTPS M} => val (pairTerm c.1)) :=
  fun a b h => Subtype.ext (val_pairTerm_injOn a.2 b.2 h)

instance isWellOrder_ctpsLt : IsWellOrder {M : List (ℕ × ℕ) // CTPS M} CtpsLt :=
  isWellOrder_of_iff CtpsLt _ ctps_val_injective ctpsLt_iff

/-- **The order type of the standard pair sequences below `M` is
`val (pairTerm M)`.** -/
theorem typein_ctpsLt (M : {M : List (ℕ × ℕ) // CTPS M}) :
    Ordinal.typein CtpsLt M = val (pairTerm M.1) := by
  refine typein_eq_of_iff CtpsLt (fun c => val (pairTerm c.1)) ctps_val_injective ctpsLt_iff
    (fun a β hβ => ?_) M
  obtain ⟨N, ⟨hN, _⟩, hvN⟩ := (val_pairTerm_bijOn_below a.2).surjOn hβ
  exact ⟨⟨N, hN⟩, hvN⟩

/-! ## The ordinal of a state -/

/-- The ordinal of a state of `pairL`: `0` for the empty list, and
`1 + val (pairTerm M)` otherwise. -/
noncomputable def pairOrdL (l : List (ℕ × ℕ)) : Ordinal.{0} :=
  if l = [] then 0 else 1 + val (pairTerm l)

/-- The same ordinal as a term: `0`, or `1 + pairTerm M` in normal form. -/
def pairOrdTerm (l : List (ℕ × ℕ)) : Term :=
  if l = [] then nil else addNF t1 (pairTerm l)

theorem pairOrdL_nil : pairOrdL [] = 0 := by simp [pairOrdL]

theorem pairOrdL_of_ne {l : List (ℕ × ℕ)} (h : l ≠ []) : pairOrdL l = 1 + val (pairTerm l) := by
  simp [pairOrdL, h]

theorem pairOrdL_pos {l : List (ℕ × ℕ)} (h : l ≠ []) : 0 < pairOrdL l := by
  rw [pairOrdL_of_ne h]
  exact _root_.lt_of_lt_of_le zero_lt_one le_self_add

theorem OT_pairOrdTerm {l : List (ℕ × ℕ)} (hl : IsPair l) : OT (pairOrdTerm l) := by
  unfold pairOrdTerm
  split_ifs with h
  · decide
  · have hC := ((isPair_iff l).mp hl).resolve_left h
    exact (addNF_spec t1 (by decide) _ (OT_pairTerm hC)).1

/-- **The ordinal of a state is the value of a term**: `pairOrdL = val ∘ pairOrdTerm`. -/
theorem val_pairOrdTerm {l : List (ℕ × ℕ)} (hl : IsPair l) :
    val (pairOrdTerm l) = pairOrdL l := by
  unfold pairOrdTerm pairOrdL
  split_ifs with h
  · rfl
  · have hC := ((isPair_iff l).mp hl).resolve_left h
    rw [(addNF_spec t1 (by decide) _ (OT_pairTerm hC)).2.1, val_t1_eq]

/-- **The ordinal of states keeps the lexicographic order.** -/
theorem ltPS_iff_pairOrdL_lt {l m : List (ℕ × ℕ)} (hl : IsPair l) (hm : IsPair m) :
    l <ₚ m ↔ pairOrdL l < pairOrdL m := by
  rcases (isPair_iff l).mp hl with rfl | hlC <;> rcases (isPair_iff m).mp hm with rfl | hmC
  · simp [pairOrdL_nil, Bijectivity.ltPS]
  · obtain ⟨x, m', rfl⟩ := List.exists_cons_of_ne_nil (ctps_ne_nil hmC)
    rw [pairOrdL_nil]
    exact iff_of_true trivial (pairOrdL_pos (by simp))
  · obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil (ctps_ne_nil hlC)
    rw [pairOrdL_nil]
    exact iff_of_false (by simp [Bijectivity.ltPS]) not_lt_zero
  · rw [pairOrdL_of_ne (ctps_ne_nil hlC), pairOrdL_of_ne (ctps_ne_nil hmC),
      add_lt_add_iff_left]
    exact ltPS_iff_val_lt hlC hmC

/-- One step goes down in the lexicographic order. -/
theorem step_ltPS {a b : PairState} (h : pairL.Rel b a) : b.1 <ₚ a.1 := by
  obtain ⟨hna, k, rfl⟩ := h
  have hne : a.1 ≠ [] := hna
  have hC : CTPS a.1 := ((isPair_iff a.1).mp a.2).resolve_left hne
  by_cases hL : 2 ≤ a.1.length
  · rw [pairL_step_eq_oper a k hL]
    refine Bijectivity.ltExpPS_ltPS_of_lng (by show 1 < a.1.length; omega)
      ⟨[k + 1], by simp, by simp, rfl⟩
  · have h1 : a.1.length = 1 := by
      have := List.length_pos_of_ne_nil hne
      omega
    rw [pairL_step_val, ctps_single hC h1, expand2L_single]
    exact trivial

/-- **The ordinal translation of the pair sequence system.** -/
noncomputable def pairOrdEval : Eval pairL (· < · : Ordinal.{0} → Ordinal.{0} → Prop) where
  val l := pairOrdL l.1
  val_lt a b h := (ltPS_iff_pairOrdL_lt b.2 a.2).mp (step_ltPS h)

/-- **Order-preserving**: for states, the lexicographic order is the order of
the ordinals. -/
theorem ltPS_iff_pairOrd_lt (a b : PairState) :
    a.1 <ₚ b.1 ↔ pairOrdEval.val a < pairOrdEval.val b :=
  ltPS_iff_pairOrdL_lt a.2 b.2

/-- **Injective.** -/
theorem pairOrd_injective : Function.Injective pairOrdEval.val :=
  injective_of_iff (fun a b : PairState => a.1 <ₚ b.1) _
    (fun a b => by
      rcases ltPS_trichotomy a.1 b.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr h))
    ltPS_iff_pairOrd_lt

/-- `ψ_0(Ω_ω)` as an ordinal. -/
theorem val_psiOmegaOmega : val psiOmegaOmega = Ord.psi (Ord.Omega Ordinal.omega0) 0 := by
  have htw : val tw = Ordinal.omega0 := Googology.Trans.BMS.val_tw
  rw [show psiOmegaOmega = psi nil (psi tw nil) from rfl, val_psi, val_psi, val_nil, htw,
    Ord.psi_zero_arg]

theorem omega0_le_val_psiOmegaOmega : Ordinal.omega0 ≤ val psiOmegaOmega := by
  have htw : val tw = Ordinal.omega0 := Googology.Trans.BMS.val_tw
  rw [← htw]
  exact (val_lt_val (by decide) (by decide) (by decide : tw < psiOmegaOmega)).le

theorem pairOrdL_lt_bound {M : List (ℕ × ℕ)} (hM : CTPS M) :
    pairOrdL M < val psiOmegaOmega := by
  rw [pairOrdL_of_ne (ctps_ne_nil hM)]
  have ha : val (pairTerm M) < val psiOmegaOmega :=
    val_lt_val (OT_pairTerm hM) (by decide) (pairTerm_lt hM)
  rcases lt_or_ge (val (pairTerm M)) Ordinal.omega0 with h | h
  · exact _root_.lt_of_lt_of_le (Ordinal.isPrincipal_add_omega0 Ordinal.one_lt_omega0 h)
      omega0_le_val_psiOmegaOmega
  · rw [Ordinal.one_add_of_omega0_le h]
    exact ha

/-- **Surjective**: the ordinals of the states are exactly the ordinals below
`ψ_0(Ω_ω)`. -/
theorem range_pairOrd : Set.range pairOrdEval.val = Set.Iio (val psiOmegaOmega) := by
  ext α
  constructor
  · rintro ⟨l, rfl⟩
    rcases (isPair_iff l.1).mp l.2 with h | h
    · show pairOrdL l.1 < _
      rw [h, pairOrdL_nil]
      exact val_pos (by intro h'; cases h')
    · exact pairOrdL_lt_bound h
  · intro hα
    rcases eq_or_ne α 0 with rfl | hα0
    · exact ⟨⟨[], isPair_nil⟩, pairOrdL_nil⟩
    · have hαβ : 1 + (α - 1) = α :=
        Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.mpr hα0)
      have hβ : α - 1 < val psiOmegaOmega :=
        _root_.lt_of_le_of_lt (_root_.le_trans le_add_self hαβ.le) hα
      obtain ⟨Y, ⟨hY, hYlt, hvY⟩, -⟩ :=
        existsUnique_OT_lt_of_lt_val (by decide : OT psiOmegaOmega)
          (by decide : psiOmegaOmega < tW) hβ
      obtain ⟨M, hM, rfl⟩ := exists_ctps_of_lt hY hYlt
      refine ⟨⟨M, isPair_of_ctps hM⟩, ?_⟩
      show pairOrdL M = α
      rw [pairOrdL_of_ne (ctps_ne_nil hM), hvY, hαβ]

/-! ## The rank -/

/-- **The rank of a state of `pairL` is its ordinal**: `0` for `[]`, and
`1 + val (toTerm (Trans M))` for a standard pair sequence `M`. -/
theorem rank_pairL_eq (l : pairL.State) : IsWellFounded.rank pairL.Rel l = pairOrdL l.1 := by
  induction l using WellFounded.induction pairL_wf with
  | _ l IH =>
    refine le_antisymm (Eval.rank_le pairOrdEval l) ?_
    refine le_of_forall_lt (fun α hα => ?_)
    have hne : l.1 ≠ [] := by
      intro h
      rw [h, pairOrdL_nil] at hα
      exact not_lt_zero hα
    have hC : CTPS l.1 := ((isPair_iff l.1).mp l.2).resolve_left hne
    have hna : ¬ pairL.halted l := hne
    rcases eq_or_ne α 0 with rfl | hα0
    · exact Rewrite.rank_pos hna
    · have hαβ : 1 + (α - 1) = α :=
        Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.mpr hα0)
      rw [pairOrdL_of_ne hne, ← hαβ, add_lt_add_iff_left] at hα
      obtain ⟨N, ⟨hN, hNl⟩, hvN⟩ := (val_pairTerm_bijOn_below hC).surjOn hα
      have hL : 2 ≤ l.1.length := by
        by_contra hL
        have h1 : l.1.length = 1 := by
          have := List.length_pos_of_ne_nil hne
          omega
        rw [ctps_single hC h1, pairTerm_single, val_nil] at hα
        exact not_lt_zero hα
      obtain ⟨n, hn, hle⟩ := exists_le_oper hN hC hNl
      have hs : (pairL.step l (n - 1)).1 = _root_.PSS.oper l.1 n := by
        rw [pairL_step_eq_oper l (n - 1) hL, Nat.sub_add_cancel hn]
      have hrel : pairL.Rel (pairL.step l (n - 1)) l := ⟨hna, n - 1, rfl⟩
      have hsC : CTPS (pairL.step l (n - 1)).1 := hs ▸ Bijectivity.ctps_oper hC hn
      have hle' : pairOrdL N ≤ pairOrdL (pairL.step l (n - 1)).1 := by
        rw [hs]
        rcases hle with h | h
        · rw [h]
        · exact ((ltPS_iff_pairOrdL_lt (isPair_of_ctps hN)
            (isPair_of_ctps (hs ▸ hsC))).mp h).le
      calc α = pairOrdL N := by
              simp only at hvN
              rw [pairOrdL_of_ne (ctps_ne_nil hN), hvN, hαβ]
        _ ≤ pairOrdL (pairL.step l (n - 1)).1 := hle'
        _ = IsWellFounded.rank pairL.Rel (pairL.step l (n - 1)) := (IH _ hrel).symm
        _ < IsWellFounded.rank pairL.Rel l := IsWellFounded.rank_lt_of_rel hrel

/-- **Equals the rank**: the ordinal translation and the rank are one map. -/
theorem pairOrdEval_eq_rankEval : pairOrdEval.val = (Rewrite.rankEval pairL_wf).val := by
  funext l
  exact (rank_pairL_eq l).symm

/-- The lexicographic order on the states of `pairL`. -/
def PairLt (a b : PairState) : Prop := a.1 <ₚ b.1

instance isWellOrder_pairLt : IsWellOrder PairState PairLt :=
  isWellOrder_of_iff PairLt _ pairOrd_injective ltPS_iff_pairOrd_lt

/-- **The order type of the states below `l` is its ordinal.** -/
theorem typein_pairLt (l : PairState) : Ordinal.typein PairLt l = pairOrdL l.1 := by
  refine typein_eq_of_iff PairLt pairOrdEval.val pairOrd_injective ltPS_iff_pairOrd_lt
    (fun a β hβ => ?_) l
  have hb : β ∈ Set.Iio (val psiOmegaOmega) := by
    have ha : pairOrdEval.val a ∈ Set.range pairOrdEval.val := ⟨a, rfl⟩
    rw [range_pairOrd] at ha
    exact _root_.lt_trans hβ ha
  rw [← range_pairOrd] at hb
  exact hb

/-- **The rank of a state is the order type of the states below it.** -/
theorem rank_eq_typein (l : PairState) :
    IsWellFounded.rank pairL.Rel l = Ordinal.typein PairLt l := by
  rw [rank_pairL_eq, typein_pairLt]

end Googology.Trans.PSS
