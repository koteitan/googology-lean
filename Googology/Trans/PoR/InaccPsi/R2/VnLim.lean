import Googology.Trans.PoR.InaccPsi.R2.VnTopK

/-!
# The pointwise limit rule with base-relative members (no self-membership, no bound)

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^X = Ω₂^X`, `Ω^x = Ω₁^x`, `T_X(β) = ψ_{Ω₂}(β + W^X)`.

* `vnKeyM`, `vnPsi_leM`, `vnPsi1_leM` (**`ψ_{Ω_{s+1}}(a) ≤ Q` from `ψ_{Ω_{s+1}}(e) < Q` at the members
  `e < a` of `Cl(a, Q)` only**, through the codes `Vk.VkA`);
* `vnTopPt` (**THE POINTWISE LIMIT RULE**: at one base `β` with `Θ(ψ₂(β)) = ψ₁(Â)`, the top
  `Θ(T_X(β)) = ψ₁(Â + Ω^{X̂})` follows from members asked only for the exponents `x < X` of the hull with
  `x ∈ Cl(β + W^{x+1}, T_{x+1}(β))`, and on the image side only for `z < X̂` in `Cl(Â + Ω^{X̂}, Θ(T_X(β)))`; a member
  `X'` needs only `X' ∈ Cl(β + W^{X'}, T_{X'}(β))` (relative to the base), its image `X̂'` only
  `X̂' ∈ Cl(Â + Ω^{X̂'}, ψ₁(Â + Ω^{X̂'}))`, and its top at this `β` alone).  Unlike `Vk.vkTopLimSh`, the members may lie
  in `[Y_{k+3}, Ω_{k+3})`, where no `Vk.VkSh` exists (`Vn.vnNoSh`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Vk

variable {S : InaccSeq.{0}}

/-- **Every member of `Cl(a, Q)` is a code `VkA (s+1) Q`**, the collapse hypothesis asked only at the members of
`Cl(a, Q)`. -/
theorem vnKeyM {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1) < S.I n)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a Q → S.psi e (Om (s + 1)) < Q) :
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
  | @coll π e hπ _ heC _ _ =>
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exact VkA.big (lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (hsC _ _))) (hI n)).le
        (SC_psi (InR_I n) _)
    rcases lt_trichotomy t s with hts | hts | hts
    · refine VkA.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hsQ.le))
      exact Order.add_one_le_of_lt hts
    · subst hts; exact VkA.small (hcoll e.1 e.2 heC)
    · exact VkA.big ((Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt hts)).le (SC_psi (InR_Om_succ t) _)

/-- **`ψ_{Ω_{s+1}}(a) ≤ Q`** from the collapses of the members `e < a` of `Cl(a, Q)`. -/
theorem vnPsi_leM {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1) < S.I n)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a Q → S.psi e (Om (s + 1)) < Q) :
    S.psi a (Om (s + 1)) ≤ Q :=
  psi_le_of_good (CSet.Om_mem (CSet.succ_mem (hsC _ _))) fun x hx hxκ =>
    vkA_lt_om hQ (vnKeyM hQ hsQ hsC hI hcoll x hx) hxκ

/-- **`ψ_{Ω₁}(a) ≤ T`** from the collapses of the members `e < a` of `Cl(a, T)`. -/
theorem vnPsi1_leM {a T : Ordinal.{0}} (hT : SC T)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a T → S.psi e (Om 1) < T) : S.psi a (Om 1) ≤ T := by
  have h := vnPsi_leM (S := S) (s := 0) (a := a) hT (by rw [Om_zero]; exact hT.1)
    (fun a b => CSet.zero_mem a b)
    (fun n => by rw [zero_add]; exact (Om_lt_Om.2 (lt_add_one 1)).trans (Mx.mxOm2_lt_I n))
    (fun e he hc => by rw [zero_add]; exact hcoll e he hc)
  rwa [zero_add] at h

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE POINTWISE LIMIT RULE WITH BASE-RELATIVE MEMBERS.** -/
theorem vnTopPt {X Xh β Â : Ordinal.{0}} (hXH : X ∈ cdHull S l) (hb : RoBaseE S l X 0 β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
    (hup : ∀ x, x ∈ cdHull S l → x ∈ S.CSet (β + leWe (x + 1)) (S.psi (β + leWe (x + 1)) (Om (1 + 1))) →
      x < X → ∃ X' Xh', X' ≤ X ∧ x < X' ∧ Xh' < Xh ∧
        Xh' ∈ S.CSet (Â + leOe Xh') (S.psi (Â + leOe Xh') (Om 1)) ∧
        gxTh (upsilon l) (ldAtR S l) (leTe S X' β) = S.psi (Â + leOe Xh') (Om 1))
    (hlo : ∀ z, z ∈ S.CSet (Â + leOe Xh) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) → z < Xh →
      ∃ X' Xh', X' < X ∧ z < Xh' ∧ X' ∈ cdHull S l ∧
        X' ∈ S.CSet (β + leWe X') (S.psi (β + leWe X') (Om (1 + 1))) ∧
        gxTh (upsilon l) (ldAtR S l) (leTe S X' β) = S.psi (Â + leOe Xh') (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S X β) = S.psi (Â + leOe Xh) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set Y := S.psi (Â + leOe Xh) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe Xh) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  have htop : leTe S X β ∈ ldAtR S l :=
    ⟨β + leWe X, CSet.add_mem hβH (leWe_mem hXH), hβA, rfl⟩
  have hup' : gxTh (upsilon l) (ldAtR S l) (leTe S X β) ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, haA, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d0, had0, heq, hd0H, -, hself⟩ := tnNf_atom hl hX haH haA
    rw [← heq] at hts ⊢
    obtain ⟨d, rfl⟩ := exists_add_of_le (haβ.trans had0)
    have hd : d < leWe X := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := taSub_mem (S := S) _ hd0H β
      rwa [Ordinal.add_sub_cancel] at h1
    have hdC : d ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) := by
      have h1 := taSub_mem (S := S) _ hself β
      rwa [Ordinal.add_sub_cancel] at h1
    have hlogd : log ω d < Om (1 + 1) * X :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxX : log ω d / Om (1 + 1) < X := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdW : β + d ≤ β + leWe (log ω d / Om (1 + 1) + 1) :=
      (add_le_add_iff_left β).2 (roLt_We_log d).le
    have hxC : log ω d / Om (1 + 1) ∈ S.CSet (β + leWe (log ω d / Om (1 + 1) + 1))
        (S.psi (β + leWe (log ω d / Om (1 + 1) + 1)) (Om (1 + 1))) :=
      (psi_mono (S := S) (InR_Om_succ 1) hdW).2 (ldDivK_mem ldOm2_SC (leLog_mem hdC))
    obtain ⟨X', Xh', -, hxX', hXh', hXh'C, e1⟩ := hup _ hxH hxC hxX
    have hdX' : d < leWe X' := (roLt_We_log d).trans_le (leWe_mono (Order.add_one_le_of_lt hxX'))
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdX'.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S X' β) < Y
    rw [e1]
    have hlt2 : Â + leOe Xh' < Â + leOe Xh := (add_lt_add_iff_left Â).2 (leOe_lt hXh')
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt2 (CSet.add_mem hÂY
      (leOe_mem ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 hXh'C)))
  apply le_antisymm hup'
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  have hÂT : S.psi Â (Om 1) < gxTh (upsilon l) (ldAtR S l) (leTe S X β) := by
    rw [← hbase]; exact hTs _ hβat hβs
  refine vnPsi1_leM hTSC fun e he heC => ?_
  rcases le_or_gt e Â with heÂ | heÂ
  · exact lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 hÂT
  obtain ⟨r, rfl⟩ := exists_add_of_le heÂ.le
  have hr : r < leOe Xh := (add_lt_add_iff_left Â).1 he
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero]; exact hÂT
  have hrC : r ∈ S.CSet (Â + leOe Xh) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) := by
    have h1 := taSub_mem (S := S) _ heC Â
    rwa [Ordinal.add_sub_cancel] at h1
  have hzC : log ω r / Om 1 ∈ S.CSet (Â + leOe Xh) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) :=
    ldDivK_mem Ph.ph_SC_Om1 (leLog_mem hrC)
  have hlogr : log ω r < Om 1 * Xh :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
  have hz : log ω r / Om 1 < Xh := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
  obtain ⟨X', Xh', hX'X, hzX', hX'H, hX'm, e1⟩ := hlo _ hzC hz
  have hrX' : r < leOe Xh' := (roLt_Oe_log r).trans_le (leOe_mono (Order.add_one_le_of_lt hzX'))
  have hat1 : leTe S X' β ∈ ldAtR S l :=
    ⟨β + leWe X', CSet.add_mem hβH (leWe_mem hX'H),
      lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono hX'X.le)) hβA, rfl⟩
  have hX'm' : X' ∈ S.CSet (β + leWe X) (S.psi (β + leWe X) (Om (1 + 1))) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono hX'X.le))).2 hX'm
  have hlt1 : leTe S X' β < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leWe_lt hX'X))
      (CSet.add_mem (hβown _ le_rfl) (leWe_mem hX'm'))
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrX'.le)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Main

end Googology.Trans.PoR.InaccPsi.R2.Vn
