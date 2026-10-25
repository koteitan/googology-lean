import Googology.Trans.PoR.InaccPsi.R2.TjEnd

/-!
# The limit rule restricted to codes (the top law at a limit shift)

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^X = Ω₂^X`, `Ω^x = Ω₁^x`, `T_X(β) = ψ_{Ω₂}(β + W^X)`, `G1 = ψ_{Ω₂}(0)`.

* `tnKey1` (**the key induction at `κ = Ω₁`**: if `ψ_{Ω₁}(e) < Q` for every `e < a` in `Cl(a, Q)`, then
  `x % G1` is a level-1 code over `Q` for every `x ∈ Cl(a, Q)`);
* `tnNf_atom` (**the normal-form argument of a hull atom**: `ψ_{Ω₂}(a) = ψ_{Ω₂}(d)` with `a ≤ d`, `d` in the
  hull, `d < A_η`, `d ∈ Cl(d, ψ_{Ω₂}(d))`);
* `tnTopLimC` (**THE LIMIT RULE RESTRICTED TO CODES**: `Rv.rvTopLimSh` where the members are asked only for the
  exponents `x < X` of the hull with `x ∈ Cl(β + W^{x+1}, T_{x+1}(β))` (the exponents of the normal-form atoms
  below `T_X(β)`), and on the image side only for the level-1 codes `z < X̂` over `Θ(T_X(β))`; members are shifts
  relative to the base `β` itself).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- **The key induction at `κ = Ω₁`, with the collapse hypothesis asked only at members of `Cl(a, Q)`.** -/
theorem tnKey1 {a Q : Ordinal.{0}} (hQ : SC Q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a Q → S.psi e (Om 1) < Q) :
    ∀ x ∈ S.CSet a Q, LeCl (Om 1) Q (x % S.psi 0 (Om (1 + 1))) := by
  set G := S.psi 0 (Om (1 + 1)) with hG_def
  have hGSC : SC G := SC_psi (InR_Om_succ 1) 0
  have hG2 : G < Om (1 + 1) := psi_lt (InR_Om_succ 1) 0
  have hQ0 : 0 < Q := hQ.1
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < G → LeCl (Om 1) Q p) →
      LeCl (Om 1) Q (p % G) := by
    intro p hp h
    rcases ldModK_prin hGSC hp with ⟨hpG, e⟩ | e
    · rw [e]; exact h hpG
    · rw [e]; exact LeCl.zero hQ0
  have hIG : ∀ n, G < S.I n := fun n => hG2.trans (mxOm2_lt_I n)
  intro x hx
  induction hx with
  | small h => exact LeCl.small ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact LeCl.zero hQ0
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal fun h => absurd (h.trans (hIG n)) (lt_irrefl _)
  | inaccW =>
    exact prin (SC_Iw (S := S)).isPrincipal fun h =>
      absurd (h.trans ((hIG 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0))) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y G with hy | hy
    · rw [ldModK_add_lt hGSC x hy]
      have hy' : LeCl (Om 1) Q y := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
      exact LeCl.add ihx hy'
    · rw [ldModK_add_ge hGSC x hy]; exact ihy
  | @phi x y _ _ ihx ihy =>
    refine prin (Ph.ph_veblen_prin x y) fun h => ?_
    have hx1 : x < G := lt_of_le_of_lt (left_le_veblen x y) h
    have hy1 : y < G := lt_of_le_of_lt (right_le_veblen x y) h
    rw [Ordinal.mod_eq_of_lt hx1] at ihx
    rw [Ordinal.mod_eq_of_lt hy1] at ihy
    exact LeCl.phi ihx ihy
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact LeCl.zero hQ0
    refine prin (Om_isPrincipal hx0) fun h => ?_
    rcases lt_trichotomy x 1 with hx | hx | hx
    · exact absurd (Order.lt_one_iff.1 hx) hx0
    · rw [hx]; exact LeCl.om
    · exfalso
      have h2 : (1 + 1 : Ordinal.{0}) ≤ x := by
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hx
      exact absurd (h.trans hG2) (not_lt.2 (Om_le_Om.2 h2))
  | @coll π e hπ _ heC _ =>
    refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (CSet.one_mem _ _))) (mxOm2_lt_I n)
      exact absurd ((h2.trans h).trans hG2) (lt_irrefl _)
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [zero_add]
      exact LeCl.small (hcoll e.1 e.2 heC)
    · exfalso
      have ht1 : 1 ≤ t := Order.one_le_iff_ne_zero.2 ht0
      rcases ht1.lt_or_eq with ht | rfl
      · have h4 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (Om (t + 1)) :=
          (Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt ht)
        exact absurd ((h4.trans h).trans hG2) (lt_irrefl _)
      · have h4 : G ≤ S.psi e.1 (Om (1 + 1)) := (psi_mono (S := S) (InR_Om_succ 1) zero_le).1
        exact absurd (h4.trans_lt h) (lt_irrefl _)

/-- `ρ_λ ≤ Λ`. -/
theorem tnRho_le_Lam {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    upsilon l ≤ S.Lam := by
  have hκL : Om (1 + 1 : Ordinal.{0}) ≤ S.Lam := (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0)).le
  exact ((leRho hl hX).2.trans gg_Om1_lt_Om2).le.trans hκL

/-- **The normal-form argument of a hull atom.** -/
theorem tnNf_atom {l ηx a : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (haH : a ∈ cdHull S l) (haA : a < ConjT.Aη S (cdEta S l)) :
    ∃ d, a ≤ d ∧ S.psi d (Om (1 + 1)) = S.psi a (Om (1 + 1)) ∧ d ∈ cdHull S l ∧
      d < ConjT.Aη S (cdEta S l) ∧ d ∈ S.CSet d (S.psi d (Om (1 + 1))) := by
  have hρL := tnRho_le_Lam hl hX
  have haL : a < S.Lam := lt_Lam_of_mem hρL haH
  obtain ⟨-, had⟩ := M_spec (S := S) (e := a) (g := S.psi a (Om (1 + 1))) haL
  have heq := psi_M_eq (S := S) (InR_Om_succ 1) haL
  have hself := M_mem_self (S := S) (InR_Om_succ 1) haL
  have hmem : S.psi (S.M a (S.psi a (Om (1 + 1))) a) (Om (1 + 1)) ∈ cdHull S l := by
    rw [heq]; exact CSet.psi_mem haA (InR_Om_succ 1) (Mx.mxOm2_mem _ _) haH
  have hρz : upsilon l ≤ S.psi (S.M a (S.psi a (Om (1 + 1))) a) (Om (1 + 1)) :=
    ((leRho hl hX).2.trans (psiS_bounds (S := S) _ 1).1).le
  obtain ⟨h1, h2⟩ := arg_mem_of_psi_mem (InR_Om_succ 1) hmem hρz hρL hself
  exact ⟨_, had, heq, h1, h2, hself⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LIMIT RULE RESTRICTED TO CODES.** -/
theorem tnTopLimC {b X Xh : Ordinal.{0}} (hs : RvSh S l b X Xh)
    (hup : ∀ β Â, RoBaseE S l X 0 β → b ≤ β → Â ∈ S.CSet Â (S.psi Â (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
      ∀ x, x ∈ cdHull S l → x ∈ S.CSet (β + leWe (x + 1)) (S.psi (β + leWe (x + 1)) (Om (1 + 1))) → x < X →
      ∃ X' Xh', X' ≤ X ∧ x < X' ∧ Xh' < Xh ∧ RvSh S l β X' Xh' ∧ RvTop S l β X' Xh' 0)
    (hlo : ∀ β Â, RoBaseE S l X 0 β → b ≤ β → Â ∈ S.CSet Â (S.psi Â (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
      ∀ z, LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) z → z < Xh →
      ∃ X' Xh', X' < X ∧ z < Xh' ∧ RvSh S l β X' Xh' ∧ RvTop S l β X' Xh' 0) :
    RvTop S l b X Xh 0 := by
  intro β Â hb hbβ hÂ hbase
  have hupβ := hup β Â hb hbβ hÂ hbase
  have hloβ := hlo β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hb' := hb
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
    ⟨β + leWe X, CSet.add_mem hβH (leWe_mem hs.hull), hβA, rfl⟩
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
    obtain ⟨X', Xh', hX'X, hxX', hXh', hXhC, hT'⟩ := hupβ _ hxH hxC hxX
    have hdX' : d < leWe X' := (roLt_We_log d).trans_le (leWe_mono (Order.add_one_le_of_lt hxX'))
    have e1 := hT' β Â (roBaseE_shift hb' (by rw [add_zero]; exact hX'X) zero_le) le_rfl hÂ hbase
    rw [add_zero, gxTh_zero, add_zero] at e1
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdX'.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S X' β) < Y
    rw [e1]
    have hlt2 : Â + leOe Xh' < Â + leOe Xh := (add_lt_add_iff_left Â).2 (leOe_lt hXh')
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt2 (CSet.add_mem
      ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
      (leOe_mem (rvMemh hXhC (x := β + leWe X') le_rfl
        (e1.le.trans (psi_mono (S := S) Low.InR_Om_one hlt2.le).1))))
  apply le_antisymm hup'
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  have hÂT : S.psi Â (Om 1) < gxTh (upsilon l) (ldAtR S l) (leTe S X β) := by
    rw [← hbase]; exact hTs _ hβat hβs
  refine lePsi1_le hTSC fun x hx hcode => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · exact lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 hÂT
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe Xh := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero]; exact hÂT
  -- the remainder `r` is a level-1 code over `Θ(T_X(β))`
  have hG1 := rwG_SC (S := S)
  have hXhG : Xh < S.psi 0 (Om (1 + 1)) := (le_self_add.trans_lt hs.ltG)
  have hrG : r < S.psi 0 (Om (1 + 1)) := hr.trans (leOe_lt_SC hG1 rwO_lt_G hXhG).1
  rw [ldModK_add_lt hG1 Â hrG] at hcode
  have hÂc : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) (Â % S.psi 0 (Om (1 + 1))) := by
    have h := tnKey1 (S := S) (SC_psi Low.InR_Om_one Â)
      (fun e he heC => psi_lt_psi_of_mem Low.InR_Om_one he heC) Â hÂ
    exact Sn.snLeCl_mono h hÂT.le
  have hrc : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) r := by
    have h := (leClDec hTSC Ph.ph_SC_Om1 _ hcode).1 _ hÂc le_self_add
    rwa [Ordinal.add_sub_cancel] at h
  have hzc : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) (log ω r / Om 1) :=
    sjCl_div hTSC Ph.ph_SC_Om1 _ (leClDec hTSC Ph.ph_SC_Om1 r hrc).2
  have hlogr : log ω r < Om 1 * Xh :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
  have hz : log ω r / Om 1 < Xh := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
  obtain ⟨X', Xh', hX'X, hzX', hX'C, hT'⟩ := hloβ _ hzc hz
  have hrX' : r < leOe Xh' := (roLt_Oe_log r).trans_le (leOe_mono (Order.add_one_le_of_lt hzX'))
  have e1 := hT' β Â (roBaseE_shift hb' (by rw [add_zero]; exact hX'X.le) zero_le) le_rfl hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at e1
  have hat1 : leTe S X' β ∈ ldAtR S l :=
    ⟨β + leWe X', CSet.add_mem hβH (leWe_mem hX'C.hull),
      lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono hX'X.le)) hβA, rfl⟩
  have hlt1 : leTe S X' β < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leWe_lt hX'X))
      (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (rvMem hX'C (x := β + leWe X) ((add_le_add_iff_left β).2 (leWe_mono hX'X.le)) le_rfl)))
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrX'.le)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tn
