import Googology.Trans.PoR.InaccPsi.R2.UsVis
import Googology.Trans.PoR.InaccPsi.R2.MxLev
import Googology.Trans.PoR.InaccPsi.R2.UoB

/-!
# The least collapse above a member of the visibility closure one threshold down, and the datum at `W`

`W = Ω_{s+1}`, `V = Ω_{s+2}` (`s` finite), `ψ_π = S.psi · π`; `i < s`, `X = Ul.UlK S i q` (the visibility closure one
threshold down, `q` strongly critical, `q ≤ Ω_{i+1}`).  An argument `e` is *own at `π`* when `e ∈ Cl(e, ψ_π e)`.

* `uw_K_CSet` (**`X ⊆ Cl(Λ, q)`**), `uw_lt_psiLam` (**a member of `X` below `Ω_{r+1}` is below `ψ_{Ω_{r+1}}(Λ)`**);
* `uw_M_least` (**`M(x)` is the least own argument at or above `x`**);
* `uw_next` (**the least collapse above a member**: for `i < r < ω` and `z ∈ X` below `Ω_{r+1}` there is an own
  `e ∈ X` with `z < ψ_{Ω_{r+1}}(e') ↔ e ≤ e'` for every own `e'`; by well-founded induction on `z` along its Cantor and
  Veblen parts, a strongly critical `z = ψ(a)` giving `e = M(a + 1)`);
* `uw_dat_K` (**the datum at `W` of a member of `X` is in `X`**: for a normal form `t` with `val t ∈ X`,
  `ulDatT W t ∈ X`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Us

variable {S : InaccSeq.{0}}

/-- **`K^{(i)}_q ⊆ Cl(Λ, q)`** for `q ≤ Λ`. -/
theorem uw_K_CSet {i q : Ordinal.{0}} (hqL : q ≤ S.Lam) {x : Ordinal.{0}} (hx : UlK S i q x) :
    x ∈ S.CSet S.Lam q := by
  induction hx with
  | small h => exact CSet.of_lt h
  | zero => exact CSet.zero_mem _ _
  | inacc n => exact CSet.I_mem _ _ n
  | inaccW => exact CSet.Iw_mem _ _
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
  | om _ ih => exact CSet.Om_mem ih
  | coll hπ _ _ _ ihπ ihe => exact CSet.psi_mem (lt_Lam_of_mem hqL ihe) hπ ihπ ihe

/-- **A member of `K^{(i)}_q` below `Ω_{r+1}` is below `ψ_{Ω_{r+1}}(Λ)`** (`q ≤ Λ`, `q ≤ ψ_{Ω_{r+1}}(Λ)`). -/
theorem uw_lt_psiLam {i q r : Ordinal.{0}} (hqL : q ≤ S.Lam) (hqr : q ≤ S.psi S.Lam (Om (r + 1)))
    {x : Ordinal.{0}} (hx : UlK S i q x) (hxr : x < Om (r + 1)) : x < S.psi S.Lam (Om (r + 1)) :=
  lt_psi_of_mem (InR_Om_succ r) (CSet_mono le_rfl hqr (uw_K_CSet hqL hx)) hxr

/-- **`M(x)` is the least own argument at or above `x`** (`x < Λ`). -/
theorem uw_M_least {κ x e : Ordinal.{0}} (hκ : S.InR κ) (hx : x < S.Lam) (he : e ∈ S.CSet e (S.psi e κ))
    (hxe : x ≤ e) : S.M x (S.psi x κ) x ≤ e := by
  refine not_lt.1 fun h => ?_
  have hown := M_mem_self hκ hx
  have hc := compare_psi hκ he hown
  rw [compare_lt_iff_lt.2 h] at hc
  have h1 : S.psi e κ < S.psi (S.M x (S.psi x κ) x) κ := compare_lt_iff_lt.1 hc
  rw [psi_M_eq hκ hx] at h1
  exact absurd (psi_mono hκ hxe).1 (not_le.2 h1)

/-- The bound `q ≤ ψ_{Ω_{r+1}}(e)` for `q ≤ Ω_{i+1}`, `i < r`. -/
theorem uw_q_le {i q r : Ordinal.{0}} (hir : i < r) (hqL : q ≤ Om (i + 1)) (e : Ordinal.{0}) :
    q ≤ S.psi e (Om (r + 1)) :=
  hqL.trans ((Om_le_Om.2 (Order.add_one_le_of_lt hir)).trans (psiS_bounds e r).1.le)

/-- Combining two bounds: the larger own argument. -/
theorem uw_next_max {r z z1 z2 : Ordinal.{0}} {P : Ordinal.{0} → Prop}
    (h1 : ∃ e1, P e1 ∧ e1 ∈ S.CSet e1 (S.psi e1 (Om (r + 1))) ∧
      ∀ e', e' ∈ S.CSet e' (S.psi e' (Om (r + 1))) → (z1 < S.psi e' (Om (r + 1)) ↔ e1 ≤ e'))
    (h2 : ∃ e2, P e2 ∧ e2 ∈ S.CSet e2 (S.psi e2 (Om (r + 1))) ∧
      ∀ e', e' ∈ S.CSet e' (S.psi e' (Om (r + 1))) → (z2 < S.psi e' (Om (r + 1)) ↔ e2 ≤ e'))
    (hz : ∀ e', e' ∈ S.CSet e' (S.psi e' (Om (r + 1))) →
      (z < S.psi e' (Om (r + 1)) ↔ z1 < S.psi e' (Om (r + 1)) ∧ z2 < S.psi e' (Om (r + 1)))) :
    ∃ e, P e ∧ e ∈ S.CSet e (S.psi e (Om (r + 1))) ∧
      ∀ e', e' ∈ S.CSet e' (S.psi e' (Om (r + 1))) → (z < S.psi e' (Om (r + 1)) ↔ e ≤ e') := by
  obtain ⟨e1, p1, o1, k1⟩ := h1
  obtain ⟨e2, p2, o2, k2⟩ := h2
  rcases le_total e1 e2 with h | h
  · refine ⟨e2, p2, o2, fun e' he' => ?_⟩
    rw [hz e' he', k1 e' he', k2 e' he']
    exact ⟨fun hh => hh.2, fun hh => ⟨h.trans hh, hh⟩⟩
  · refine ⟨e1, p1, o1, fun e' he' => ?_⟩
    rw [hz e' he', k1 e' he', k2 e' he']
    exact ⟨fun hh => hh.1, fun hh => ⟨hh, h.trans hh⟩⟩

/-- **The least collapse above a member below `Ω_{r+1}`**: for `i < r < ω`, `q` strongly critical, `q ≤ Ω_{i+1}`, and
`z ∈ K^{(i)}_q` with `z < Ω_{r+1}`: some own `e ∈ K^{(i)}_q` has `z < ψ_{Ω_{r+1}}(e') ↔ e ≤ e'` for every own `e'`. -/
theorem uw_next {i q r : Ordinal.{0}} (hr : r < ω) (hir : i < r) (hq : SC q) (hqL : q ≤ Om (i + 1)) :
    ∀ z, UlK S i q z → z < Om (r + 1) → ∃ e, UlK S i q e ∧ e ∈ S.CSet e (S.psi e (Om (r + 1))) ∧
      ∀ e', e' ∈ S.CSet e' (S.psi e' (Om (r + 1))) → (z < S.psi e' (Om (r + 1)) ↔ e ≤ e') := by
  have hκ : S.InR (Om (r + 1)) := InR_Om_succ r
  have hi : i < ω := hir.trans hr
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  have hSCe : ∀ e', SC (S.psi e' (Om (r + 1))) := fun e' => SC_psi hκ e'
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzr
  by_cases h0 : z < S.psi 0 (Om (r + 1))
  · exact ⟨0, UlK.zero, CSet.zero_mem _ _, fun e' _ =>
      ⟨fun _ => zero_le, fun _ => h0.trans_le (psi_mono hκ zero_le).1⟩⟩
  have h0' : S.psi 0 (Om (r + 1)) ≤ z := not_lt.1 h0
  have hz0 : z ≠ 0 := fun e => by rw [e] at h0'; exact absurd h0' (not_le.2 (hSCe 0).1)
  by_cases ht : tail z = 0
  · have hlz : lead z = z := by have := lead_add_tail hz0; rwa [ht, add_zero] at this
    set b := log ω z with hbdef
    have hbz : b ≤ z := log_le_self ω z
    have hbK : UlK S i q b := (ulK_dec hq z hz).2
    have hzb : ω ^ b = z := hlz
    rcases hbz.lt_or_eq with hlt | heq
    · obtain ⟨e, h1, h2, h3⟩ := IH b hlt hbK (hlt.trans hzr)
      refine ⟨e, h1, h2, fun e' he' => ?_⟩
      rw [← h3 e' he']
      constructor
      · exact fun h => hlt.trans h
      · intro h
        have := (hSCe e').2 0 (hSCe e').1 b h
        rwa [veblen_zero_apply, hzb] at this
    · have hE : InE z := by
        show ω ^ z = z
        conv_lhs => rw [← heq]
        exact hzb
      by_cases hSC : SC z
      · have hLz : Om r < z := (psiS_bounds 0 r).1.trans_le h0'
        have hzB : z < S.psi S.Lam (Om (r + 1)) := uw_lt_psiLam hqΛ (uw_q_le hir hqL _) hz hzr
        obtain ⟨a, hown, hza⟩ := Ui.ui_own_of_SC hr hSC hLz hzB
        have haK : UlK S i q a := uoArg hqΛ hκ hown (by rw [hza]; exact hz) (uw_q_le hir hqL a)
        have ha1 : UlK S i q (a + 1) := UlK.add haK UlK.one
        have ha1L : a + 1 < S.Lam := lt_Lam_of_mem hqΛ (uw_K_CSet hqΛ ha1)
        refine ⟨S.M (a + 1) (S.psi (a + 1) (Om (r + 1))) (a + 1), uoM_mem hqΛ ha1 (uw_q_le hir hqL _),
          M_mem_self hκ ha1L, fun e' he' => ?_⟩
        rw [← hza]
        constructor
        · intro h
          have hae : a < e' := (Ui.ui_own_lt_iff hown he').1 h
          exact uw_M_least hκ ha1L he' (Order.add_one_le_of_lt hae)
        · intro h
          have h1 := (psi_mono hκ h).1
          rw [psi_M_eq hκ ha1L] at h1
          exact (Ui.ui_psi_lt_of_own hown (lt_add_one a)).trans_le h1
      · obtain ⟨hdec, ha, hb, -⟩ := Mx.mxDec hE (pos_iff_ne_zero.2 hz0) hSC
        have hzv : veblen (invVeblen₁ z) (invVeblen₂ z) = z := hdec
        have hK := uoK_veb (S := S) (s := i) (q := q) (by rw [hzv]; exact hz) (by rw [hzv]; exact ha)
          (by rw [hzv]; exact hb)
        exact uw_next_max (P := UlK S i q) (IH _ ha hK.1 (ha.trans hzr)) (IH _ hb hK.2 (hb.trans hzr))
          fun e' _ => ⟨fun h => ⟨ha.trans h, hb.trans h⟩, fun h => by
            have := (hSCe e').2 _ h.1 _ h.2; rwa [hzv] at this⟩
  · have hlz : lead z < z := by
      have e1 := lead_add_tail hz0
      conv_rhs => rw [← e1]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ht)
    have htz : tail z < z := tail_lt hz0
    obtain ⟨hlK, htK⟩ := uoK_lead_tail hq hz hz0
    exact uw_next_max (P := UlK S i q) (IH _ hlz hlK (hlz.trans hzr)) (IH _ htz htK (htz.trans hzr))
      fun e' _ => ⟨fun h => ⟨hlz.trans h, htz.trans h⟩, fun h => by
        have hP : lead z + tail z < S.psi e' (Om (r + 1)) := (hSCe e').isPrincipal h.1 h.2
        rwa [lead_add_tail hz0] at hP⟩

/-- **The datum at `W` of a member of `K^{(i)}_q` is in `K^{(i)}_q`** (`i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`):
for a normal form `t` with `val t ∈ K^{(i)}_q`, `ulDatT W t ∈ K^{(i)}_q`. -/
theorem uw_dat_K {i q s : Ordinal.{0}} (his : i < s) (hs : s < ω) (hq : SC q) (hqL : q ≤ Om (i + 1)) :
    ∀ t : Term, NF t → UlK S i q (val S t) → UlK S i q (ulDatT S (Om (s + 1)) t) := by
  have hi : i < ω := his.trans hs
  have hqΛ : q ≤ S.Lam := us_qΛ hi hqL
  have hqW : q ≤ Om (s + 1) := hqL.trans (Om_le_Om.2 (Order.add_one_le_of_lt (his.trans (lt_add_one s))))
  have hmax : ∀ a b : Ordinal.{0}, UlK S i q a → UlK S i q b → UlK S i q (max a b) := fun a b ha hb => by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact hb
    · rw [max_eq_left h]; exact ha
  intro t
  induction t with
  | zero => intro _ _; exact UlK.zero
  | inacc n =>
    intro _ hm
    by_cases h : val S (inacc n) < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    · simp only [ulDatT, if_neg h]; exact UlK.zero
  | inaccW =>
    intro _ hm
    by_cases h : val S inaccW < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    · simp only [ulDatT, if_neg h]; exact UlK.zero
  | add a b iha ihb =>
    intro hN hm
    by_cases h : val S (add a b) < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    have h0 : val S (add a b) ≠ 0 := fun e => h (by rw [e]; exact (Ui.ui_SC_W s).1)
    obtain ⟨hl, ht⟩ := uoK_lead_tail hq hm h0
    obtain ⟨hla, htb⟩ := Ui.ui_add_parts (S := S) hN
    rw [hla] at hl; rw [htb] at ht
    simp only [ulDatT, if_neg h]
    exact hmax _ _ (iha hN.1 hl) (ihb hN.2.1 ht)
  | phi a b iha ihb =>
    intro hN hm
    by_cases h : val S (phi a b) < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    have hN' := hN
    obtain ⟨hNa, hNb, hca, hcb⟩ := hN
    have hav : val S a < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNa hN'
      rw [e] at hca; exact compare_lt_iff_lt.1 hca
    have hbv : val S b < val S (phi a b) := by
      have e := Term.cmp_eq_compare S hNb hN'
      rw [e] at hcb; exact compare_lt_iff_lt.1 hcb
    obtain ⟨hma, hmb⟩ := uoK_veb hm hav hbv
    simp only [ulDatT, if_neg h]
    exact hmax _ _ (iha hNa hma) (ihb hNb hmb)
  | om a iha =>
    intro hN hm
    by_cases h : val S (om a) < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    simp only [ulDatT, if_neg h]
    exact iha hN.1 (uoK_Om hm)
  | psiS σ a ihs iha =>
    intro hN hm
    by_cases h : val S (psiS σ a) < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    have hβz : q ≤ S.psi (val S a) (Om (val S σ + 1)) := hqW.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    have hma := uoArg hqΛ (InR_Om_succ _) hsem.2.2 hm hβz
    have hms := ulK_of_succ hq (uoK_Om (uoSub hqΛ (InR_Om_succ _) hsem.2.2 hm hβz))
    simp only [ulDatT, if_neg h]
    exact hmax _ _ (ihs hN.1 hms) (iha hN.2.1 hma)
  | psiI n a iha =>
    intro hN hm
    by_cases h : val S (psiI n a) < Om (s + 1)
    · rw [ulDatT_small h]; exact hm
    have hβz : q ≤ S.psi (val S a) (S.I n) := hqW.trans (not_lt.1 h)
    have hsem := Term.sem_of_NF (S := S) hN
    simp only [ulDatT, if_neg h]
    exact iha hN.1 (uoArg hqΛ (InR_I n) hsem.2 hm hβz)

end Googology.Trans.PoR.InaccPsi.R2.Uw
