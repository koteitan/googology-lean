import Googology.Trans.PoR.InaccPsi.R2.UmPre

/-!
# The limit rule restricted to codes past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_X(β) = ψ_{Ω₂}(β + W^X)`, `Y_{s+2} = ψ_{Ω_{s+2}}(Ω_{s+2})`,
`C_k(Q) = Ug.UgC S k Q`.

`Tn.tnKey1` and `Tn.tnTopLimC` with the shifts past `Γ₂` (`Uj.UjSh`), the collapse bound `Uj.ujPsi1_le` modulo
`Y₂` and the level-1 codes with the atoms `ψ_{Ω₂}(d)`.

* `umKeyC` (**every element of `Cl(a, Q)` has its remainder modulo `Y_{s+2}` a level-`(s+1)` code**, with the
  collapse hypothesis asked only at the members of `Cl(a, Q)`), `umKey1` (`Â % Y₂` is a level-1 code over
  `ψ_{Ω₁}(Â)` for an own `Â`);
* `umTopLimC` (**THE LIMIT RULE RESTRICTED TO CODES PAST `Γ₂`**: the top at a shift `X` past `Γ₂` from smaller
  shifts with tops above every hull `x < X` with `x ∈ Cl(β + W^{x+1}, T_{x+1}(β))` and above every level-1 code
  `z < X̂` over `Θ(T_X(β))`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **Every element of `Cl(a, Q)` has its remainder modulo `Y_{s+2}` a level-`(s+1)` code**, the collapse
hypothesis asked only at the members of `Cl(a, Q)`. -/
theorem umKeyC {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1 + 1) < S.I n)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a Q → S.psi e (Om (s + 1)) < Q) :
    ∀ x ∈ S.CSet a Q, UgC S (s + 1) Q (x % ujY S s) := by
  set Y := ujY S s with hY_def
  have hYSC : SC Y := ujY_SC s
  have hY3 : Y < Om (s + 1 + 1) := ujY_lt s
  have hQ0 : 0 < Q := hQ.1
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < Y → UgC S (s + 1) Q p) →
      UgC S (s + 1) Q (p % Y) := by
    intro p hp h
    rcases ldModK_prin hYSC hp with ⟨hpY, e⟩ | e
    · rw [e]; exact h hpY
    · rw [e]; exact UgC.zero hQ0
  have hIY : ∀ n, Y < S.I n := fun n => hY3.trans (hI n)
  intro x hx
  induction hx with
  | small h => exact UgC.small ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact UgC.zero hQ0
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal fun h => absurd (h.trans (hIY n)) (lt_irrefl _)
  | inaccW =>
    exact prin (SC_Iw (S := S)).isPrincipal fun h =>
      absurd (h.trans ((hIY 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0))) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y Y with hy | hy
    · rw [ldModK_add_lt hYSC x hy]
      have hy' : UgC S (s + 1) Q y := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
      exact UgC.add ihx hy'
    · rw [ldModK_add_ge hYSC x hy]; exact ihy
  | @phi x y _ _ ihx ihy =>
    refine prin (Ph.ph_veblen_prin x y) fun h => ?_
    have hx1 : x < Y := lt_of_le_of_lt (left_le_veblen x y) h
    have hy1 : y < Y := lt_of_le_of_lt (right_le_veblen x y) h
    rw [Ordinal.mod_eq_of_lt hx1] at ihx
    rw [Ordinal.mod_eq_of_lt hy1] at ihy
    exact UgC.phi ihx ihy
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact UgC.zero hQ0
    refine prin (Om_isPrincipal hx0) fun h => ?_
    rcases lt_trichotomy x (s + 1) with hx | hx | hx
    · refine UgC.small (lt_of_le_of_lt (Om_le_Om.2 ?_) hsQ)
      rw [← Order.succ_eq_add_one] at hx; exact Order.lt_succ_iff.1 hx
    · rw [hx]; exact UgC.om
    · exfalso
      have h2 : s + 1 + 1 ≤ x := by
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hx
      exact absurd (h.trans hY3) (not_lt.2 (Om_le_Om.2 h2))
  | @coll π e hπ _ heC _ ihe =>
    refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exfalso
      have h2 : Om (s + 1 + 1) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (hsC _ _)))) (hI n)
      exact absurd ((h2.trans h).trans hY3) (lt_irrefl _)
    rcases lt_trichotomy t s with hts | hts | hts
    · refine UgC.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hsQ.le))
      exact Order.add_one_le_of_lt hts
    · subst hts; exact UgC.small (hcoll e.1 e.2 heC)
    · rcases (Order.add_one_le_of_lt hts).lt_or_eq with h3 | h3
      · exfalso
        have h4 : Om (s + 1 + 1) < S.psi e.1 (Om (t + 1)) := (Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt h3)
        exact absurd ((h4.trans h).trans hY3) (lt_irrefl _)
      · subst h3
        have hlt := ujArg_lt hsC h
        have heY : e.1 < Y := hlt.trans h
        rw [Ordinal.mod_eq_of_lt heY] at ihe
        exact UgC.psi ihe hlt


/-- **`Â % Y₂` is a level-1 code over `ψ_{Ω₁}(Â)`** for an own `Â`. -/
theorem umKey1 {Â : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1))) : UgC S 1 (S.psi Â (Om 1)) (Â % ujY S 0) := by
  have hQ : SC (S.psi Â (Om 1)) := SC_psi Low.InR_Om_one Â
  have h := umKeyC (S := S) (s := 0) (a := Â) (Q := S.psi Â (Om 1)) hQ (by rw [Om_zero]; exact hQ.1)
    (fun a b => CSet.zero_mem a b) (fun n => by rw [zero_add]; exact Mx.mxOm2_lt_I n)
    (fun e he heC => by rw [zero_add]; exact psi_lt_psi_of_mem Low.InR_Om_one he heC) Â hÂ
  rwa [zero_add] at h

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LIMIT RULE RESTRICTED TO CODES PAST `Γ₂`.** -/
theorem umTopLimC {b X Xh : Ordinal.{0}} (hs : UjSh S l b X Xh)
    (hup : ∀ β Â, RoBaseE S l X 0 β → b ≤ β → Â ∈ S.CSet Â (S.psi Â (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
      ∀ x, x ∈ cdHull S l → x ∈ S.CSet (β + leWe (x + 1)) (S.psi (β + leWe (x + 1)) (Om (1 + 1))) → x < X →
      ∃ X' Xh', X' ≤ X ∧ x < X' ∧ Xh' < Xh ∧ UjSh S l β X' Xh' ∧ RvTop S l β X' Xh' 0)
    (hlo : ∀ β Â, RoBaseE S l X 0 β → b ≤ β → Â ∈ S.CSet Â (S.psi Â (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
      ∀ z, UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) z → z < Xh →
      ∃ X' Xh', X' < X ∧ z < Xh' ∧ UjSh S l β X' Xh' ∧ RvTop S l β X' Xh' 0) :
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
      (leOe_mem (ujMemh hXhC (hXh'.le.trans ((ujLe_Oe Xh).trans le_add_self)) (x := β + leWe X') le_rfl
        (e1.le.trans (psi_mono (S := S) Low.InR_Om_one hlt2.le).1))))
  apply le_antisymm hup'
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  have hÂT : S.psi Â (Om 1) < gxTh (upsilon l) (ldAtR S l) (leTe S X β) := by
    rw [← hbase]; exact hTs _ hβat hβs
  refine ujPsi1_le hTSC fun x hx hcode => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · exact lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 hÂT
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe Xh := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero]; exact hÂT
  -- the remainder `r` is a level-1 code over `Θ(T_X(β))`
  have hG1 : SC (ujY S 0) := ujY_SC 0
  have hΩG1 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hXhG : Xh < ujY S 0 := (le_self_add.trans_lt hs.ltYh)
  have hrG : r < ujY S 0 := hr.trans (leOe_lt_SC hG1 hΩG1 hXhG).1
  rw [ldModK_add_lt hG1 Â hrG] at hcode
  have hÂc : UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) (Â % ujY S 0) :=
    UgC.mono hÂT.le (umKey1 hÂ)
  have hrc : UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) r := by
    have h := (ugCDec hTSC one_ne_zero _ hcode).1 _ hÂc le_self_add
    rwa [Ordinal.add_sub_cancel] at h
  have hzc : UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S X β)) (log ω r / Om 1) :=
    ugC_div hTSC one_ne_zero _ (ugCDec hTSC one_ne_zero r hrc).2
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
        (leWe_mem (ujMem hX'C (hX'X.le.trans ((ujLe_We X).trans le_add_self)) (x := β + leWe X)
          ((add_le_add_iff_left β).2 (leWe_mono hX'X.le)) le_rfl)))
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrX'.le)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1


end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
