import Googology.Trans.PoR.InaccPsi.R2.RxLv

/-!
# The level shift is strictly increasing and keeps the hulls

`RxE S W` the domain, `κ = rxL S Z At W` the level shift, `h = rxH S W` the least stage, `W = rxW Z At`,
`ψ_k = ψ_{Ω_k}`.

* `rxE_psi`, `rxL_psiE` (**`ψ_{k+1}(α)` is a member for a normal member `α`, at a larger stage, and
  `κ ψ_{k+1}(α) = ψ_{k+2}(κ α)`**);
* `RxMonoQ`, `RxTrQ` (the two statements of the induction, at the right end `R`, the left stage `H`, the left
  end `L`, below the stage bound `M`);
* `rxMT` (**THE SHIFT THEOREM**): for members `x' < x`, `κ x' < κ x` (MONO); and for a normal member `α` at a
  finite level `k ≥ 1` and a member `y ∈ Cl(α, ψ_{k+1}(α))`, `κ y ∈ Cl(κ α, ψ_{k+2}(κ α))` (TRANSFER).  One
  induction on (the larger stage, the right end, the stage of the left end, the left end): a collapse
  `ψ_{k+1}(d') < ψ_{k+1}(d)` with normal arguments has `d' < d` and `d' ∈ Cl(d, ψ_{k+1}(d))` (MONO at the
  arguments, a smaller stage, and TRANSFER at `(d', d)`, a smaller left stage); TRANSFER at a member below
  `ψ_{k+1}(α)` is MONO at the same configuration, and a collapse `ψ_{j+1}(e) ≥ ψ_{k+1}(α)` in the hull has its
  argument `e < α` in the hull (`arg_mem_of_psi_mem`);
* `rxL_mono` (**`κ` is strictly increasing on the domain**), `rxL_tr` (**TRANSFER**).

No new axiom.  New definitions: `RxMonoQ`, `RxTrQ` (statements of the induction).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

theorem rxC_nat (a b : Ordinal.{0}) (k : ℕ) : (k : Ordinal.{0}) ∈ S.CSet a b := by
  induction k with
  | zero => exact CSet.zero_mem a b
  | succ k ih => rw [Nat.cast_succ]; exact CSet.succ_mem ih

theorem rxC_Om_nat (a b : Ordinal.{0}) (k : ℕ) : Om (k : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.Om_mem (rxC_nat a b k)

theorem rxC_Om_succ (a b : Ordinal.{0}) (k : ℕ) : Om ((k : Ordinal.{0}) + 1) ∈ S.CSet a b :=
  CSet.Om_mem (CSet.succ_mem (rxC_nat a b k))

theorem rxC_Om_succ2 (a b : Ordinal.{0}) (k : ℕ) : Om ((k : Ordinal.{0}) + 1 + 1) ∈ S.CSet a b :=
  CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (rxC_nat a b k)))

theorem rxMs_stage_le {T x y : Ordinal.{0}} (hx : x < S.Lam) (h : rxMs S T y < rxMs S T x) :
    rxH S T y ≤ rxH S T x := by
  by_contra hc
  exact absurd (rxMs_lt_stage hx (not_le.1 hc)) (not_lt.2 h.le)

/-- **`ψ_{k+1}(α)` is a member** for a normal member `α`. -/
theorem rxE_psi {T α : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hα : RxE S T α)
    (hn : α ∈ S.CSet α (S.psi α (Om ((k : Ordinal.{0}) + 1)))) :
    RxE S T (S.psi α (Om ((k : Ordinal.{0}) + 1))) := by
  refine ⟨RxN.psi (InR_Om_succ _) (rxNat_ne_one hk) (RxN.om (RxN.succ (rxN_nat k))) hα.1 hn, ?_, ?_⟩
  · rcases lt_or_ge (S.psi α (Om ((k : Ordinal.{0}) + 1))) (ConjT.th S) with h | h
    · exact CSet.of_lt h
    · exact CSet.psi_mem hα.2.2 (InR_Om_succ _) (rxC_Om_succ _ _ k) hα.2.1
  · refine (psi_lt (InR_Om_succ _) _).trans (Om_lt_Om.2 ?_)
    exact_mod_cast (show ((k + 1 : ℕ) : Ordinal.{0}) < ω from natCast_lt_omega0 _)

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)

/-- **`κ ψ_{k+1}(α) = ψ_{k+2}(κ α)`** and `h α < h ψ_{k+1}(α)`, for a normal member `α`. -/
theorem rxL_psiE {α : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hα : RxE S (rxW Z At) α)
    (hn : α ∈ S.CSet α (S.psi α (Om ((k : Ordinal.{0}) + 1)))) :
    rxL S Z At (rxW Z At) (S.psi α (Om ((k : Ordinal.{0}) + 1))) =
      S.psi (rxL S Z At (rxW Z At) α) (Om ((k : Ordinal.{0}) + 1 + 1)) ∧
      rxH S (rxW Z At) α < rxH S (rxW Z At) (S.psi α (Om ((k : Ordinal.{0}) + 1))) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hX := rxE_psi hk hα hn
  have hb := psiS_bounds (S := S) α (k : Ordinal.{0})
  have hS := SC_psi (S := S) (InR_Om_succ (k : Ordinal.{0})) α
  have h1 : Om 1 < S.psi α (Om ((k : Ordinal.{0}) + 1)) := (rxOm1_le_nat hk).trans_lt hb.1
  have hΩ : ¬ ∃ j : ℕ, S.psi α (Om ((k : Ordinal.{0}) + 1)) = Om (j : Ordinal.{0}) := fun ⟨j, e⟩ =>
    not_Om_of_between hb.1 hb.2 (j : Ordinal.{0}) e
  obtain ⟨j, hj, d, hdE, hdn, he, hdh⟩ := rxE_atom hW1 hX hS h1 hΩ
  have hjk : (j : Ordinal.{0}) + 1 = k + 1 := by
    have := sub_eq_of_psi_eq (InR_Om_succ _) (InR_Om_succ _) he.symm
    exact Om_inj.1 this
  have hjk' : j = k := by
    have : j + 1 = k + 1 := by exact_mod_cast hjk
    omega
  subst hjk'
  have hdα : d = α := by
    have hc := compare_psi (InR_Om_succ _) hdn hn
    rw [← he, compare_eq_iff_eq.2 rfl] at hc
    exact compare_eq_iff_eq.1 hc.symm
  subst hdα
  rw [← he] at hdh
  exact ⟨rxL_atom hj hdn (rxE_lt_Lam hdE) hdh, hdh⟩

end K

/-- **MONO at `(L, R)`**, stage bound `M`, left stage `H`. -/
def RxMonoQ (S : InaccSeq.{0}) (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (M : ℕ) (R : Ordinal.{0}) (H : ℕ)
    (L : Ordinal.{0}) : Prop :=
  RxE S (rxW Z At) L → RxE S (rxW Z At) R → rxH S (rxW Z At) L = H →
    max (rxH S (rxW Z At) L) (rxH S (rxW Z At) R) ≤ M → L < R →
    rxL S Z At (rxW Z At) L < rxL S Z At (rxW Z At) R

/-- **TRANSFER at `(L, α)`** with `R = ψ_{k+1}(α)`, stage bound `M`, left stage `H`. -/
def RxTrQ (S : InaccSeq.{0}) (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (M : ℕ) (R : Ordinal.{0}) (H : ℕ)
    (L : Ordinal.{0}) : Prop :=
  ∀ α : Ordinal.{0}, ∀ k : ℕ, RxE S (rxW Z At) L → RxE S (rxW Z At) α → 1 ≤ k →
    α ∈ S.CSet α (S.psi α (Om ((k : Ordinal.{0}) + 1))) → S.psi α (Om ((k : Ordinal.{0}) + 1)) = R →
    rxH S (rxW Z At) L = H → max (rxH S (rxW Z At) L) (rxH S (rxW Z At) R) ≤ M →
    L ∈ S.CSet α R →
    rxL S Z At (rxW Z At) L ∈ S.CSet (rxL S Z At (rxW Z At) α)
      (S.psi (rxL S Z At (rxW Z At) α) (Om ((k : Ordinal.{0}) + 1 + 1)))

section Main

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
include hZ hZ1 hAt

local notation "κ" => rxL S Z At (rxW Z At)
local notation "hh" => rxH S (rxW Z At)

/-- **THE SHIFT THEOREM** (MONO and TRANSFER below every stage bound `M`). -/
theorem rxMT (M : ℕ) : (∀ R H L, RxMonoQ S Z At M R H L) ∧ (∀ R H L, RxTrQ S Z At M R H L) := by
  have hW := rxW_SC hZ hZ1 hAt
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  induction M using Nat.strong_induction_on with
  | _ M IHM =>
  have inner : ∀ R H L, RxMonoQ S Z At M R H L ∧ RxTrQ S Z At M R H L := by
    intro R
    induction R using WellFoundedLT.induction with
    | ind R IHR =>
    intro H
    induction H using Nat.strong_induction_on with
    | _ H IHH =>
    intro L
    induction L using WellFoundedLT.induction with
    | ind L IHL =>
    have use : ∀ H' L', H' ≤ H → (H' < H ∨ L' < L) →
        RxMonoQ S Z At M R H' L' ∧ RxTrQ S Z At M R H' L' := by
      intro H' L' hH hor
      rcases hH.lt_or_eq with hlt | rfl
      · exact IHH H' hlt L'
      · rcases hor with h | h
        · exact absurd h (lt_irrefl _)
        · exact IHL L' h
    -- MONO at `(L, R)`
    have hMono : RxMonoQ S Z At M R H L := by
      intro hLE hRE hLH hM hLR
      have hRL : R < S.Lam := rxE_lt_Lam hRE
      have hLL : L < S.Lam := rxE_lt_Lam hLE
      -- MONO at pairs with a smaller right end
      have monoR : ∀ x' x, x < R → RxE S (rxW Z At) x' → RxE S (rxW Z At) x →
          max (hh x') (hh x) ≤ M → x' < x → κ x' < κ x := fun x' x hx hx'E hxE hm hlt =>
        (IHR x hx (hh x') x').1 hx'E hxE rfl hm hlt
      -- MONO at `(y, R)` with `y < L` at a stage not above `H`
      have monoL : ∀ y, y < L → hh y ≤ H → RxE S (rxW Z At) y → κ y < κ R := fun y hy hyh hyE =>
        (use (hh y) y hyh (Or.inr hy)).1 hyE hRE rfl
          (max_le (hyh.trans (hLH ▸ le_max_left _ _) |>.trans hM) (le_max_right _ _ |>.trans hM))
          (hy.trans hLR)
      -- MONO at a smaller stage bound
      have monoM : ∀ x' x, max (hh x') (hh x) < M → RxE S (rxW Z At) x' → RxE S (rxW Z At) x →
          x' < x → κ x' < κ x := fun x' x hm hx'E hxE hlt =>
        ((IHM _ hm).1 x (hh x') x') hx'E hxE rfl le_rfl hlt
      rcases lt_or_ge R (Om 1) with hR1 | hR1
      · obtain ⟨e1, -, hR2⟩ := rxL_small hZ hZ1 hAt hRE hR1
        obtain ⟨e2, -, -⟩ := rxL_small hZ hZ1 hAt hLE (hLR.trans hR1)
        rw [e1, e2]; exact ruInv_lt hR2 hLR
      rcases lt_or_ge L (Om 1) with hL1 | hL1
      · obtain ⟨e2, h2, -⟩ := rxL_small hZ hZ1 hAt hLE hL1
        rw [e2]
        exact h2.trans_le (by simpa using rxL_ge_lev R hRE 1 le_rfl (by rw [Nat.cast_one]; exact hR1))
      have hR1' : Om 1 < R := hL1.trans_lt hLR
      by_cases hS : SC R
      · -- `R = ψ_{j+1}(d)` an atom
        by_cases hΩ : ∃ j : ℕ, R = Om (j : Ordinal.{0})
        · obtain ⟨j, rfl⟩ := hΩ
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := by
            refine ⟨j - 1, ?_⟩
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · subst h0
              rw [Nat.cast_zero, Om_zero] at hR1'; exact absurd hR1' (not_lt.2 zero_le)
            · omega
          rw [rxL_Om (by omega)]
          have hLj : L < Om ((j' : Ordinal.{0}) + 1) := by rw [← Nat.cast_succ]; exact hLR
          have := rxL_lt_lev hZ hZ1 hAt L hLE j' hLj
          rw [Nat.cast_succ]; exact this
        obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := rxE_atom hW1 hRE hS hR1' hΩ
        rw [rxL_atom hj hdn (rxE_lt_Lam hdE) hdh]
        have hbR := psiS_bounds (S := S) d (j : Ordinal.{0})
        by_cases hS' : SC L
        · by_cases hΩ' : ∃ i : ℕ, L = Om (i : Ordinal.{0})
          · obtain ⟨i, rfl⟩ := hΩ'
            have hi : 1 ≤ i := by
              by_contra h0
              have : i = 0 := by omega
              subst this
              rw [Nat.cast_zero, Om_zero] at hL1; exact absurd hL1 (not_le.2 (Om_pos one_ne_zero))
            rw [rxL_Om hi]
            have hij : (i : Ordinal.{0}) < j + 1 := Om_lt_Om.1 (hLR.trans hbR.2)
            exact (Om_le_Om.2 (add_le_add (Order.lt_add_one_iff.1 hij) le_rfl)).trans_lt
              (psiS_bounds (S := S) _ _).1
          · have hL1' : Om 1 < L := lt_of_le_of_ne hL1 fun e => hΩ' ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
            obtain ⟨i, hi, d', hd'E, hd'n, rfl, hd'h⟩ := rxE_atom hW1 hLE hS' hL1' hΩ'
            rw [rxL_atom hi hd'n (rxE_lt_Lam hd'E) hd'h]
            have hbL := psiS_bounds (S := S) d' (i : Ordinal.{0})
            rcases lt_trichotomy i j with hij | rfl | hij
            · have hij' : (i : Ordinal.{0}) + 1 ≤ j := by exact_mod_cast hij
              exact (psi_lt (InR_Om_succ _) _).trans_le
                ((Om_le_Om.2 (add_le_add hij' le_rfl)).trans (psiS_bounds (S := S) _ _).1.le)
            · have hdd : d' < d := lt_of_psi_lt (InR_Om_succ _) hd'n hdn hLR
              have hm1 : max (hh d') (hh d) < M := by
                have := max_lt_max hd'h hdh
                exact this.trans_le (hLH ▸ hM)
              have hK : κ d' < κ d := monoM d' d hm1 hd'E hdE hdd
              have hd'C : d' ∈ S.CSet d (S.psi d (Om ((i : Ordinal.{0}) + 1))) :=
                (psi_mono (S := S) (InR_Om_succ _) hdd.le).2 hd'n
              have hT := (use (hh d') d' (hLH ▸ hd'h.le) (Or.inl (hLH ▸ hd'h))).2 d i hd'E hdE hi hdn rfl rfl
                (max_le ((hd'h.le.trans (le_max_left _ _)).trans hM) (le_max_right _ _ |>.trans hM)) hd'C
              exact psi_lt_psi_of_mem (InR_Om_succ _) hK hT
            · have hij' : (j : Ordinal.{0}) + 1 ≤ i := by exact_mod_cast hij
              exact absurd ((Om_le_Om.2 hij').trans_lt (hbL.1.trans hLR)) (not_lt.2 hbR.2.le)
        · have hL1' : Om 1 < L := lt_of_le_of_ne hL1 fun e => hS' (e ▸ Ph.ph_SC_Om1)
          have hX : SC (S.psi (κ d) (Om ((j : Ordinal.{0}) + 1 + 1))) := SC_psi (InR_Om_succ _) _
          refine rxL_step_lt hX hLE hL1' hS' fun y hyE hym hyx => ?_
          have := monoL y hyx (hLH ▸ rxMs_stage_le hLL hym) hyE
          rwa [rxL_atom hj hdn (rxE_lt_Lam hdE) hdh] at this
      · -- `R` not strongly critical
        by_cases hboth : ω ^ R = R ∧ ω ^ L = L
        · obtain ⟨a, b, hab, hb, -, haE, hbE, hK, hane, hah, hbh⟩ :=
            rxLDecV hZ hRE hR1 hboth.1
          obtain ⟨a', b', hab', hb', ha'le, ha'E, hb'E, hK', -, ha'h, hb'h⟩ :=
            rxLDecV hZ hLE hL1 hboth.2
          have ha : a < R := hane hS
          have hmax : ∀ {p q : Ordinal.{0}}, hh p ≤ hh L → hh q ≤ hh R → max (hh p) (hh q) ≤ M :=
            fun hp hq => (max_le_max hp hq).trans hM
          have hmax' : ∀ {p q : Ordinal.{0}}, hh p ≤ hh R → hh q ≤ hh L → max (hh p) (hh q) ≤ M :=
            fun hp hq => (max_le (hp.trans (le_max_right _ _)) (hq.trans (le_max_left _ _))).trans hM
          rw [hK, hK']
          have hlt' := hLR
          rw [← hab, ← hab'] at hlt'
          rcases veblen_lt_veblen_iff.1 hlt' with ⟨e, h⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
          · rw [e]
            exact veblen_lt_veblen_iff_right.2 (monoR b' b hb hb'E hbE (hmax hb'h hbh) h)
          · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨monoR a' a ha ha'E haE (hmax ha'h hah) h, ?_⟩))
            rw [← hK]
            exact monoL b' hb' (hLH ▸ hb'h) hb'E
          · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inr ⟨monoR a a' (ha'le.trans_lt hLR) haE ha'E
              (hmax' hah ha'h) h, ?_⟩))
            rw [← hK']
            rw [hab'] at h2
            exact monoR L b hb hLE hbE (hmax le_rfl hbh) h2
        · obtain ⟨n, hn1, hdm, hK, hℓ, hr, hop, hrlt, hopx, hℓ1, hcase, hℓh, hrh, hoh⟩ :=
            rxLDecK hZ hZ1 hAt hRE hR1
          obtain ⟨n', hn1', hdm', hK', hℓ', hr', hop', hrlt', hopx', hℓ1', hcase', hℓh', hrh', hoh'⟩ :=
            rxLDecK hZ hZ1 hAt hLE hL1
          have hmLL : ∀ {p q : Ordinal.{0}}, hh p ≤ hh L → hh q ≤ hh L → max (hh p) (hh q) ≤ M :=
            fun hp hq => (max_le hp hq).trans ((le_max_left _ _).trans hM)
          have hmLR : ∀ {p q : Ordinal.{0}}, hh p ≤ hh L → hh q ≤ hh R → max (hh p) (hh q) ≤ M :=
            fun hp hq => (max_le_max hp hq).trans hM
          have hℓle : log ω L ≤ log ω R := log_mono_right ω hLR.le
          have hrb : κ (L % ω ^ log ω L) < ω ^ κ (log ω L) := by
            rw [← rxL_opow hZ hZ1 hAt hℓ' hop' hℓ1']
            exact monoR _ _ (hopx'.trans_lt hLR) hr' hop' (hmLL hrh' hoh') hrlt'
          have hK'lt : κ L < ω ^ κ (log ω L) * ((n' : Ordinal.{0}) + 1) := by
            rw [hK', mul_add_one]; exact (add_lt_add_iff_left _).2 hrb
          have hKζ : ω ^ κ (log ω R) ≤ κ R := by
            rw [hK]; exact (le_mul_left _ (by exact_mod_cast hn1)).trans le_self_add
          rcases hℓle.lt_or_eq with hℓlt | hℓeq
          · have hKℓ : κ (log ω L) < κ (log ω R) := by
              rcases hcase with hε | hℓζ
              · have hne' : ω ^ L ≠ L := fun h => hboth ⟨hε, h⟩
                have hℓ'ζ' : log ω L < L := by
                  rcases hcase' with h | h
                  · exact absurd h hne'
                  · exact h
                have e := ruLog_eps hε
                rw [e]
                exact monoL _ hℓ'ζ' (hLH ▸ hℓh') hℓ'
              · exact monoR _ _ hℓζ hℓ' hℓ (hmLR hℓh' hℓh) hℓlt
            calc κ L < ω ^ κ (log ω L) * ((n' : Ordinal.{0}) + 1) := hK'lt
              _ ≤ ω ^ κ (log ω L) * ω := by
                  gcongr; exact (Order.add_one_le_of_lt (natCast_lt_omega0 n')).trans_eq (by rfl)
              _ = ω ^ (κ (log ω L) + 1) := (opow_add_one _ _).symm
              _ ≤ ω ^ κ (log ω R) := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hKℓ)
              _ ≤ κ R := hKζ
          · rw [hℓeq] at hK'lt hdm' hrlt' hK' hrh'
            have hnle : n' ≤ n := by
              by_contra hc
              push Not at hc
              have h2 : ω ^ log ω R * ((n + 1 : ℕ) : Ordinal.{0}) ≤ L := by
                rw [hdm']; exact (mul_le_mul_right (by exact_mod_cast hc) _).trans le_self_add
              have h3 : R < ω ^ log ω R * ((n + 1 : ℕ) : Ordinal.{0}) := by
                rw [Nat.cast_succ, mul_add_one]
                conv_lhs => rw [hdm]
                exact (add_lt_add_iff_left _).2 hrlt
              exact absurd (h3.trans_le h2) (not_lt.2 hLR.le)
            rcases hnle.lt_or_eq with hnlt | hneq
            · calc κ L < ω ^ κ (log ω R) * ((n' : Ordinal.{0}) + 1) := hK'lt
                _ ≤ ω ^ κ (log ω R) * n := by
                    gcongr; exact_mod_cast Nat.succ_le_of_lt hnlt
                _ ≤ κ R := by rw [hK]; exact le_self_add
            · subst hneq
              have hrr : L % ω ^ log ω R < R % ω ^ log ω R := by
                have h4 := hLR
                rw [hdm, hdm'] at h4
                exact (add_lt_add_iff_left _).1 h4
              rw [hK, hK']
              refine (add_lt_add_iff_left _).2 (monoR _ _ (hrlt.trans_le hopx) ?_ hr (hmLR hrh' hrh) hrr)
              rw [← hℓeq]; exact hr'
    -- TRANSFER at `(L, α)`, `R = ψ_{k+1}(α)`
    have hTr : RxTrQ S Z At M R H L := by
      intro α k hLE hαE hk hαn hR hLH hM hLC
      have hRE : RxE S (rxW Z At) R := hR ▸ rxE_psi hk hαE hαn
      obtain ⟨hKR, hαh⟩ := rxL_psiE hk hαE hαn
      rw [hR] at hKR hαh
      rcases lt_or_ge L R with hsmall | hbig
      · have := hMono hLE hRE hLH hM hsmall
        rw [hKR] at this
        exact CSet.of_lt this
      have hR1 : Om 1 < R := hR ▸ (rxOm1_le_nat hk).trans_lt (psiS_bounds (S := S) α _).1
      have hL1 : Om 1 < L := hR1.trans_le hbig
      have hRL : R ≤ S.Lam := (rxE_lt_Lam hRE).le
      -- TRANSFER at the parts of `L`
      have trL : ∀ y, y < L → hh y ≤ H → RxE S (rxW Z At) y → y ∈ S.CSet α R →
          κ y ∈ S.CSet (κ α) (S.psi (κ α) (Om ((k : Ordinal.{0}) + 1 + 1))) := fun y hy hyh hyE hyC =>
        (use (hh y) y hyh (Or.inr hy)).2 α k hyE hαE hk hαn hR rfl
          (max_le ((hyh.trans (hLH ▸ le_max_left _ _)).trans hM) ((le_max_right _ _).trans hM)) hyC
      by_cases hΩ : ∃ j : ℕ, L = Om (j : Ordinal.{0})
      · obtain ⟨j, rfl⟩ := hΩ
        have hj : 1 ≤ j := by
          by_contra h0
          have : j = 0 := by omega
          subst this
          rw [Nat.cast_zero, Om_zero] at hL1; exact absurd hL1 (not_lt.2 zero_le)
        rw [rxL_Om hj]; exact rxC_Om_succ _ _ j
      by_cases hS : SC L
      · obtain ⟨j, hj, e, heE, hen, rfl, heh⟩ := rxE_atom hW1 hLE hS hL1 hΩ
        rw [rxL_atom hj hen (rxE_lt_Lam heE) heh]
        obtain ⟨heC, heα⟩ := arg_mem_of_psi_mem (InR_Om_succ _) hLC hbig hRL hen
        have hm1 : max (hh e) (hh α) < M := by
          have := max_lt_max heh hαh
          exact this.trans_le (hLH ▸ hM)
        have hK : κ e < κ α := ((IHM _ hm1).1 α (hh e) e) heE hαE rfl le_rfl heα
        have hT := (use (hh e) e (hLH ▸ heh.le) (Or.inl (hLH ▸ heh))).2 α k heE hαE hk hαn hR rfl
          (max_le ((heh.le.trans (le_max_left _ _)).trans hM) ((le_max_right _ _).trans hM)) heC
        exact CSet.psi_mem hK (InR_Om_succ _) (rxC_Om_succ2 _ _ j) hT
      · by_cases hε : ω ^ L = L
        · obtain ⟨a, b, hab, hb, -, haE, hbE, hK, hane, hah, hbh⟩ := rxLDecV hZ hLE hL1.le hε
          have ha : a < L := hane hS
          obtain ⟨haC, hbC⟩ := rxCDecV hLC a b hab hb
          rw [hK]
          exact CSet.phi_mem (trL a ha (hLH ▸ hah) haE haC) (trL b hb (hLH ▸ hbh) hbE hbC)
        · obtain ⟨n, -, hdm, hK, hℓ, hr, -, -, -, -, hcase, hℓh, hrh, -⟩ :=
            rxLDecK hZ hZ1 hAt hLE hL1.le
          have hlt : log ω L < L := ruLog_lt hL1 hε
          have hrlt : L % ω ^ log ω L < L := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans hL1).ne'
          have hℓC : log ω L ∈ S.CSet α R := (rxCDec L hLC).2
          have hmC : ω ^ log ω L * n ∈ S.CSet α R := by
            have hop : ω ^ log ω L ∈ S.CSet α R := by
              have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hℓC; rwa [veblen_zero_apply] at this
            exact ConjT.mul_nat_mem S hop n
          have hrC : L % ω ^ log ω L ∈ S.CSet α R := by
            have := (rxCDec L hLC).1 _ hmC (le_self_add.trans_eq hdm.symm)
            have e : L - ω ^ log ω L * n = L % ω ^ log ω L := by
              have e0 := Ordinal.add_sub_cancel (ω ^ log ω L * n) (L % ω ^ log ω L)
              rwa [← hdm] at e0
            rwa [e] at this
          rw [hK]
          have h1m := trL _ hlt (hLH ▸ hℓh) hℓ hℓC
          have h2m := trL _ hrlt (hLH ▸ hrh) hr hrC
          have hop : ω ^ κ (log ω L) ∈ S.CSet (κ α) (S.psi (κ α) (Om ((k : Ordinal.{0}) + 1 + 1))) := by
            have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) h1m; rwa [veblen_zero_apply] at this
          exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m
    exact ⟨hMono, hTr⟩
  exact ⟨fun R H L => (inner R H L).1, fun R H L => (inner R H L).2⟩

/-- **`κ` is strictly increasing on the domain.** -/
theorem rxL_mono {x' x : Ordinal.{0}} (hx' : RxE S (rxW Z At) x') (hx : RxE S (rxW Z At) x)
    (h : x' < x) : rxL S Z At (rxW Z At) x' < rxL S Z At (rxW Z At) x :=
  (rxMT hZ hZ1 hAt (max (rxH S (rxW Z At) x') (rxH S (rxW Z At) x))).1 x _ x' hx' hx rfl le_rfl h

/-- **TRANSFER**: `y ∈ Cl(α, ψ_{k+1}(α)) ⇒ κ y ∈ Cl(κ α, ψ_{k+2}(κ α))` for a normal member `α`, `k ≥ 1`. -/
theorem rxL_tr {y α : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hy : RxE S (rxW Z At) y)
    (hα : RxE S (rxW Z At) α) (hn : α ∈ S.CSet α (S.psi α (Om ((k : Ordinal.{0}) + 1))))
    (hC : y ∈ S.CSet α (S.psi α (Om ((k : Ordinal.{0}) + 1)))) :
    rxL S Z At (rxW Z At) y ∈ S.CSet (rxL S Z At (rxW Z At) α)
      (S.psi (rxL S Z At (rxW Z At) α) (Om ((k : Ordinal.{0}) + 1 + 1))) :=
  (rxMT hZ hZ1 hAt (max (rxH S (rxW Z At) y)
    (rxH S (rxW Z At) (S.psi α (Om ((k : Ordinal.{0}) + 1)))))).2 _ _ y α k hy hα hk hn rfl rfl le_rfl hC

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rx
