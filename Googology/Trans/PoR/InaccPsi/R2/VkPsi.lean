import Googology.Trans.PoR.InaccPsi.R2.VkCode

/-!
# The collapse bound `ψ_{Ω_{s+1}}(a) ≤ Q` through the codes above the level `s + 1`, with no bound on `a`

`VkA k Q` are the codes over `Q` above the level `k` (module `Vk.VkCode`).  `Uj.ujPsi_le` takes the remainders
modulo `Y_{s+2} = ψ_{Ω_{s+2}}(Ω_{s+2})` and so sees only arguments below `Y_{s+2}`; here **every** member of
`Cl(a, Q)` is a code above the level `s + 1` (every strongly critical ordinal `≥ Ω_{s+1}` is a code), so the bound
holds for every argument `a`, one proof for every level `s`.

* `vkKey` (**every member of `Cl(a, Q)` is a code**, given the collapse hypothesis), `vkPsi_le`
  (**`ψ_{Ω_{s+1}}(a) ≤ Q`**), `vkPsi2_le` (`s = 1`), `vkPsi1_le` (`s = 0`);
* `vkA_boundY` (**the digit at position `y` of a code is below `Q`**), `vkA_boundK`, `vkA_SC_ge` (**a strongly
  critical code `w ≥ Q` is `≥ Ω_k`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- **Every member of `Cl(a, Q)` is a code above the level `s + 1`**, given the collapse hypothesis. -/
theorem vkKey {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1) < S.I n)
    (hcoll : ∀ e, e < a → VkA (s + 1) Q e → S.psi e (Om (s + 1)) < Q) :
    ∀ x ∈ S.CSet a Q, VkA (s + 1) Q x := by
  intro x hx
  induction hx with
  | small h => exact VkA.small h
  | zero => exact VkA.zero hQ.1
  | inacc n => exact VkA.big (hI n).le (SC_I n)
  | inaccW => exact VkA.big ((hI 0).le.trans (Ordinal.le_iSup (fun n => S.I n) 0)) SC_Iw
  | add _ _ ihx ihy => exact VkA.add ihx ihy
  | phi _ _ ihx ihy => exact VkA.phi ihx ihy
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact VkA.zero hQ.1
    rcases lt_or_ge x (s + 1) with hx | hx
    · refine VkA.small (lt_of_le_of_lt (Om_le_Om.2 ?_) hsQ)
      rw [← Order.succ_eq_add_one] at hx; exact Order.lt_succ_iff.1 hx
    · exact VkA.big (Om_le_Om.2 hx) (SC_Om hx0)
  | @coll π e hπ _ _ _ ihe =>
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exact VkA.big (lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (hsC _ _))) (hI n)).le
        (SC_psi (InR_I n) _)
    rcases lt_trichotomy t s with hts | hts | hts
    · refine VkA.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hsQ.le))
      exact Order.add_one_le_of_lt hts
    · subst hts; exact VkA.small (hcoll e.1 e.2 ihe)
    · exact VkA.big ((Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt hts)).le (SC_psi (InR_Om_succ t) _)

/-- **`ψ_{Ω_{s+1}}(a) ≤ Q`** for a strongly critical `Q > Ω_s`, if `ψ_{Ω_{s+1}}(e) < Q` for every code `e < a`
above the level `s + 1`. -/
theorem vkPsi_le {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1) < S.I n)
    (hcoll : ∀ e, e < a → VkA (s + 1) Q e → S.psi e (Om (s + 1)) < Q) :
    S.psi a (Om (s + 1)) ≤ Q := by
  have key := vkKey hQ hsQ hsC hI hcoll
  exact psi_le_of_good (CSet.Om_mem (CSet.succ_mem (hsC _ _))) fun x hx hxκ => vkA_lt_om hQ (key x hx) hxκ

/-- **`ψ_{Ω₂}(a) ≤ Q`** through the codes above the level 2. -/
theorem vkPsi2_le {a Q : Ordinal.{0}} (hQ : SC Q) (hΩQ : Om 1 < Q)
    (hcoll : ∀ e, e < a → VkA (1 + 1) Q e → S.psi e (Om (1 + 1)) < Q) :
    S.psi a (Om (1 + 1)) ≤ Q :=
  vkPsi_le (s := 1) hQ hΩQ (fun a b => CSet.one_mem a b) Mx.mxOm2_lt_I hcoll

/-- **`ψ_{Ω₁}(a) ≤ T`** through the codes above the level 1. -/
theorem vkPsi1_le {a T : Ordinal.{0}} (hT : SC T)
    (hcoll : ∀ e, e < a → VkA 1 T e → S.psi e (Om 1) < T) :
    S.psi a (Om 1) ≤ T := by
  have h := vkPsi_le (S := S) (s := 0) (a := a) hT (by rw [Om_zero]; exact hT.1)
    (fun a b => CSet.zero_mem a b)
    (fun n => by rw [zero_add]; exact (Om_lt_Om.2 (lt_add_one 1)).trans (Mx.mxOm2_lt_I n))
    (fun e he hc => by rw [zero_add] at hc ⊢; exact hcoll e he hc)
  rwa [zero_add] at h

/-- **The digit at position `y` of a code is below `Q`**: a code below `ω^{Ω_k·y + Ω_k}` is below `ω^{Ω_k·y}·Q`,
for every code `y`. -/
theorem vkA_boundY {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0) {y : Ordinal.{0}} (hy : VkA k Q y) :
    ∀ x, VkA k Q x → x < ω ^ (Om k * y + Om k) → x < ω ^ (Om k * y) * Q := by
  have eQ : ω ^ (Om k * y) * Q = ω ^ (Om k * y + Q) := by rw [opow_add, gg_SC_eps hQ]
  have hpr : IsPrincipal (· + ·) (ω ^ (Om k * y) * Q) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  have hκy := vkA_mulK hQ hk y hy
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := vkDec hQ x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (VkA.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < Om k * y + Om k := (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < ω ^ (Om k * y) * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a (Om k * y) with h | h
    · exact h.trans_le le_self_add
    · have hc : VkA k Q (a - Om k * y) := (vkDec hQ a hlog).1 _ hκy h
      have hdec' : Om k * y + (a - Om k * y) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - Om k * y < Om k := by
        have : Om k * y + (a - Om k * y) < Om k * y + Om k := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (vkA_lt_om hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

/-- **The position of the leading digit of a code is below `Q`**: a code below `Ω_k·Ω_k` is below `Ω_k·Q`. -/
theorem vkA_boundK {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0) :
    ∀ x, VkA k Q x → x < Om k * Om k → x < Om k * Q := by
  have hκ : SC (Om k) := SC_Om hk
  have hE : ω ^ Om k = Om k := gg_SC_eps hκ
  have eQ : Om k * Q = ω ^ (Om k + Q) := by rw [opow_add, hE, gg_SC_eps hQ]
  have eK : Om k * Om k = ω ^ (Om k + Om k) := by rw [opow_add, hE]
  have hpr : IsPrincipal (· + ·) (Om k * Q) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := vkDec hQ x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (VkA.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < Om k + Om k := by
    rw [eK] at hxb; exact (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < Om k * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a (Om k) with h | h
    · exact h.trans_le le_self_add
    · have hc : VkA k Q (a - Om k) := (vkDec hQ a hlog).1 _ (VkA.om hQ.1 le_rfl) h
      have hdec' : Om k + (a - Om k) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - Om k < Om k := by
        have : Om k + (a - Om k) < Om k + Om k := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (vkA_lt_om hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

/-- **A strongly critical code `w ≥ Q` is `≥ Ω_k`.** -/
theorem vkA_SC_ge {k Q : Ordinal.{0}} : ∀ w, VkA k Q w → SC w → Q ≤ w → Om k ≤ w := by
  intro w hw
  induction hw with
  | small h => exact fun _ hQ => absurd h (not_lt.2 hQ)
  | big h1 _ => exact fun _ _ => h1
  | @add x y _ _ ihx ihy =>
    intro hS hQ
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at hS hQ ⊢; exact ihx hS hQ
    have hy : y = x + y := by
      rcases (le_add_self : y ≤ x + y).lt_or_eq with h | h
      · exact absurd (hS.isPrincipal (lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)) h) (lt_irrefl _)
      · exact h
    rw [← hy] at hS hQ ⊢; exact ihy hS hQ
  | @phi x y _ _ ihx ihy =>
    intro hS hQ
    rcases (right_le_veblen x y).lt_or_eq with h | h
    · obtain ⟨e1, -⟩ := ugSC_veb hS rfl h
      have hS' : SC x := by rw [e1]; exact hS
      have hQ' : Q ≤ x := by rw [e1]; exact hQ
      rw [← e1]; exact ihx hS' hQ'
    · rw [← h] at hS hQ ⊢; exact ihy hS hQ

end Googology.Trans.PoR.InaccPsi.R2.Vk
