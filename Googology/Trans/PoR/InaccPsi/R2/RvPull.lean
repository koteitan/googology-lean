import Googology.Trans.PoR.InaccPsi.R2.RvTopE

/-!
# Relative shifts: the pull-back `RvTop X e` (every code `e`) `⇒ RvTop (X + Ω₂) 0`, image `X̂ + Ω₁`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `(X, X̂)` own relative to `b`,
`EL_j = Ro.roEL S X β j`.

* `rvEL_lt_succ`, `rvEL_mono`, `rvEL_sup` (`T_{X+W}(β) = sup_j EL_j` for `β ≥ b`), `rvTW_ge`, `rvTW_gt`,
  `rvBaseE_of_W`, `rvTopW` (**THE PULL-BACK** at the bases `β ≥ b`), as `Rq.rqTopW`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

section Base

variable {l b X Xh β : Ordinal.{0}} (hs : RvSh S l b X Xh)
  (hβown : ∀ d, d ≤ leWe (X + Om (1 + 1)) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1)))) (hbβ : b ≤ β)

include hs hβown hbβ

theorem rvEL_lt_succ : ∀ j, roEL S X β j < roEL S X β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := rvEL_lt_succ j
    have hle : roEL S X β (j + 1) ≤ roEL S X β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X).2 IH.le)))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 IH))) ?_
    refine CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X).2 (roEL_lt_Om2 X β (j + 1)).le)))
      (leWe_mem (CSet.add_mem (rvMem hs (rvWX_le hbβ X _) le_rfl) (CSet.of_lt (IH.trans_le hle))))

theorem rvEL_mono {j j' : ℕ} (h : j ≤ j') : roEL S X β j ≤ roEL S X β j' :=
  (strictMono_nat_of_lt_succ (fun i => rvEL_lt_succ hs hβown hbβ i)).monotone h

/-- **`T_{X+W}(β) = sup_j EL_j`.** -/
theorem rvEL_sup (hβd : leWe (X + Om (1 + 1)) ∣ β) {x : Ordinal.{0}} (hx : x < leTe S (X + Om (1 + 1)) β) :
    ∃ j, x < roEL S X β j := by
  have hbdd : BddAbove (Set.range (roEL S X β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, roEL S X β j ↔ ∃ j, y < roEL S X β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, roEL S X β j < ⨆ j, roEL S X β j :=
    fun j => (hlt _).2 ⟨j + 1, rvEL_lt_succ hs hβown hbβ j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, roEL S X β j := hKQ 0
  have hQSC : SC (⨆ j, roEL S X β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (rvEL_mono hs hβown hbβ (le_max_left i j))
    have hj' := hj.trans_le (rvEL_mono hs hβown hbβ (le_max_right i j))
    exact ((roEL_SC X β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, roEL S X β j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hX1 : S.psi (β + leWe X) (Om (1 + 1)) < roEL S X β 1 := by
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2
      (leWe_lt (lt_add_of_pos_right X (Om_pos one_ne_zero)))) ?_
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X).2 gg_Om1_lt_Om2.le)))
      (leWe_mem (rvMem hs (rvWX_le hbβ X _) le_rfl))
  have hβ1 : S.psi β (Om (1 + 1)) < roEL S X β 1 :=
    lt_of_le_of_lt (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1 hX1
  have hFQ : leTe S (X + Om (1 + 1)) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβ1).trans (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X + Om (1 + 1)) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact (hβ1.trans (hKQ 1))
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X + Om (1 + 1))) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X + Om (1 + 1))) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hs.ltG3).2] at hc2
    have hm : (β + x') % leWe (X + Om (1 + 1)) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨hsub, hlog⟩ := leClDec hQSC ldOm2_SC x' hc2
    have hla : log ω x' < Om (1 + 1) * X + Om (1 + 1) * Om (1 + 1) := by
      rw [← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X) with h1 | h1
    · have hxX : x' < leWe X := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans_lt hX1).trans
        (hKQ 1)
    have hXC : LeCl (Om (1 + 1)) Q (Om (1 + 1) * X) :=
      LeCl.mulK hQSC ldOm2_SC X (rvCl hs hQSC (add_le_add_left hbβ _) (hX1.trans (hKQ 1)).le)
    have hu := (leClDec hQSC ldOm2_SC (log ω x') hlog).1 _ hXC h1
    have hdec : Om (1 + 1) * X + (log ω x' - Om (1 + 1) * X) = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : log ω x' - Om (1 + 1) * X < Om (1 + 1) * Om (1 + 1) := by
      have : Om (1 + 1) * X + (log ω x' - Om (1 + 1) * X) < Om (1 + 1) * X + Om (1 + 1) * Om (1 + 1) := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    have hb := leCl_boundK hQSC ldOm2_SC _ hu hu2
    have hq : (log ω x' - Om (1 + 1) * X) / Om (1 + 1) < Q := (Ordinal.lt_mul_iff_div_lt hW0).1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h2 : log ω x' + 1 ≤ Om (1 + 1) * (X + roEL S X β j) := by
      rw [mul_add, ← hdec, add_assoc]
      refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
      calc log ω x' - Om (1 + 1) * X
          < Om (1 + 1) * ((log ω x' - Om (1 + 1) * X) / Om (1 + 1)) + Om (1 + 1) :=
            Ordinal.lt_mul_div_add _ hW0
        _ = Om (1 + 1) * ((log ω x' - Om (1 + 1) * X) / Om (1 + 1) + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * roEL S X β j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x' < leWe (X + roEL S X β j) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2)
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{X+x}) ≥ T_{X+W}(β)` for `x ≥ T_{X+W}(β)`. -/
theorem rvTW_ge (hβd : leWe (X + Om (1 + 1)) ∣ β) {x : Ordinal.{0}} (hx : leTe S (X + Om (1 + 1)) β ≤ x) :
    leTe S (X + Om (1 + 1)) β ≤ S.psi (β + leWe (X + x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := rvEL_sup hs hβown hbβ hβd h
  have h1 : roEL S X β (j + 1) ≤ S.psi (β + leWe (X + x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X).2 ((roEL_le_top X β j).trans hx))))).1
  exact absurd (hj.trans_le ((rvEL_lt_succ hs hβown hbβ j).le.trans h1)) (lt_irrefl _)

/-- **Every `x < T_{X+W}(β)` is an own exponent at the shift `X`.** -/
theorem rvTW_gt (hβd : leWe (X + Om (1 + 1)) ∣ β) {x : Ordinal.{0}} (hx : x < leTe S (X + Om (1 + 1)) β) :
    x < S.psi (β + leWe (X + x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := rvEL_sup hs hβown hbβ hβd hx
  exact roEL_gt X β j x hj

end Base

/-- **A base of exponent `X + W` is a base of shift `X` and exponent `e`** for every `e < T_{X+W}(β)`. -/
theorem rvBaseE_of_W {b X Xh l β e : Ordinal.{0}} (hs : RvSh S l b X Xh) (hbβ : b ≤ β)
    (hb : RoBaseE S l (X + Om (1 + 1)) 0 β)
    (he : e < leTe S (X + Om (1 + 1)) β) : RoBaseE S l X e β := by
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have heW : e ≤ Om (1 + 1) := (he.trans (leTe_lt_Om2 _ _)).le
  have hle : X + e ≤ X + Om (1 + 1) := (add_le_add_iff_left X).2 heW
  refine ⟨(leWe_dvd hle).trans hβd, hβH, lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono hle)) hβA,
    fun d hd => hβown d (hd.trans (leWe_mono hle)), fun e' _ h' => ?_⟩
  exact rvTW_gt hs hβown hbβ hβd (h'.trans_lt he)

section Main

variable {l b X Xh : Ordinal.{0}} (hs : RvSh S l b X Xh) {ηx : Ordinal.{0}} (hl : IsRestartIdx l)
  (hX : upsilon l < Pv S ηx)

include hs hl hX

/-- **THE PULL-BACK: `RoTop X e` for every code `e` gives `RoTop (X + Ω₂) 0` with the image `X̂ + Ω₁`.** -/
theorem rvTopW (hT : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e) :
    RvTop S l b (X + Om (1 + 1)) (Xh + Om 1) 0 := by
  intro β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (X + Om (1 + 1)) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  have h0T : (0 : Ordinal.{0}) < T := (Om_pos one_ne_zero).trans (leOm1_lt_Te _ _)
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρ0
  set Y := S.psi (Â + leOe (Xh + Om 1)) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh + Om 1)) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the tops `T_{X+g}(β)`, `g < T` a code
  have hsubG : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g < T →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X + g) β) =
        S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g)) (Om 1) ∧
      leTe S (X + g) β ∈ ldAtR S l ∧ leTe S (X + g) β < T ∧
      S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g)) (Om 1) < Y := by
    intro g hg hgT
    have hgW : g < Om (1 + 1) := hgT.trans (leTe_lt_Om2 _ _)
    have hgH : g ∈ cdHull S l := (ldHull_iff hl hX hgW).2 hg
    have hbg := rvBaseE_of_W hs hbβ hb' hgT
    have hexpg : g < S.psi (β + leWe (X + g)) (Om (1 + 1)) := hbg.2.2.2.2 g hg le_rfl
    have e1 := hT g hg hgW β Â hbg hbβ hÂ hbase
    have hlt : β + leWe (X + g) < β + leWe (X + Om (1 + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 hgW))
    have hΘg1 : gxTh (upsilon l) (ldAtR S l) g < Om 1 := by
      refine (gxTh_lt hg hexpg).trans ?_
      change gxTh (upsilon l) (ldAtR S l) (leTe S (X + g) β) < Om 1
      rw [e1]; exact psi_lt Low.InR_Om_one _
    refine ⟨e1, ⟨β + leWe (X + g), CSet.add_mem hβH (leWe_mem (CSet.add_mem hs.hull hgH)),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem (rvMem hs (rvWX_le hbβ X _) le_rfl) (CSet.of_lt hgT))))
    · have hlt2 : Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g) < Â + leOe (Xh + Om 1) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh).2 hΘg1))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (rvMemh hs (rvWX_le hbβ X g) e1.le) (CSet.of_lt ?_)))
      rw [← e1]
      exact gxTh_lt hg hexpg
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (X + Om (1 + 1)), CSet.add_mem hβH (leWe_mem (CSet.add_mem hs.hull (mxOm2_mem _ _))),
      hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) T ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe (X + Om (1 + 1)) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X + Om (1 + 1))) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X + Om (1 + 1))) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X + Om (1 + 1)) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X + Om (1 + 1)) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxW : x < X + Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    have hWx : leWe x ≤ d := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
    obtain ⟨g', hg'c, hg'T, hdg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < T ∧ d < leWe (X + g') := by
      rcases lt_or_ge x X with hxX | hxX
      · refine ⟨0, hc0, h0T, hdx.trans_le (leWe_mono ?_)⟩
        rw [add_zero]; exact Order.add_one_le_of_lt hxX
      · have hgm := roModX hs.dvd hxX hxW
        have hgH : x - X ∈ cdHull S l := by rw [← hgm]; exact ldModK_mem ldOm2_SC hxH
        have hgW' : x - X < Om (1 + 1) := by
          have : X + (x - X) < X + Om (1 + 1) := by rwa [Ordinal.add_sub_cancel_of_le hxX]
          exact (add_lt_add_iff_left X).1 this
        have hgc := (ldHull_iff hl hX hgW').1 hgH
        have hgT : x - X < T := by
          by_contra h
          push Not at h
          have h1 := rvTW_ge hs hβown hbβ hβd h
          rw [Ordinal.add_sub_cancel_of_le hxX] at h1
          exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hWx)).1)
            (not_le.2 hts)
        refine ⟨x - X + 1, hcode1 _ hgc (ldOm2_SC.isSuccLimit.succ_lt hgW'), hTSC0.isSuccLimit.succ_lt hgT, ?_⟩
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxX]; exact hdx
    obtain ⟨e1, -, -, hY1⟩ := hsubG g' hg'c hg'T
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdg'.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < Y
    rw [e1]; exact hY1
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < T :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  refine lePsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Xh + Om 1) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * (Xh + Om 1)) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (Xh + Om 1)) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hs.ltG).2] at hc2
  have hmod : (Â + r) % leOe (Xh + Om 1) = Â % leOe (Xh + Om 1) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Xh + Om 1) + r with hy_def
  have hyP : y < leOe (Xh + Om 1) := isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have hlogy : w < Om 1 * Xh + Om 1 * Om 1 := by
    rw [← mul_add]
    exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hylt := lt_opow_succ_log_self one_lt_omega0 y
  rw [Order.succ_eq_add_one] at hylt
  obtain ⟨hsub, hlogC⟩ := leClDec hTSC Ph.ph_SC_Om1 y hc2
  obtain ⟨g', hg'c, hg'T, hyg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < T ∧
      y < leOe (Xh + gxTh (upsilon l) (ldAtR S l) g') := by
    rcases lt_or_ge w (Om 1 * Xh) with h1 | h1
    · refine ⟨0, hc0, h0T, hylt.trans_le ?_⟩
      rw [gxTh_zero, add_zero]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1)
    have hXC := LeCl.mulK hTSC Ph.ph_SC_Om1 Xh (rvClh hs hTSC (rvWX_le hbβ X _) le_rfl)
    have hwC : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) T) w := hlogC
    have hu := (leClDec hTSC Ph.ph_SC_Om1 w hwC).1 _ hXC h1
    have hdec : Om 1 * Xh + (w - Om 1 * Xh) = w := Ordinal.add_sub_cancel_of_le h1
    have hu2 : w - Om 1 * Xh < Om 1 * Om 1 := by
      have : Om 1 * Xh + (w - Om 1 * Xh) < Om 1 * Xh + Om 1 * Om 1 := by rw [hdec]; exact hlogy
      exact (add_lt_add_iff_left _).1 this
    have hb := leCl_boundK hTSC Ph.ph_SC_Om1 _ hu hu2
    have hq : (w - Om 1 * Xh) / Om 1 < gxTh (upsilon l) (ldAtR S l) T := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hb
    obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hq
    have hgW : g < Om (1 + 1) := hgT.trans (leTe_lt_Om2 _ _)
    refine ⟨g + 1, hcode1 _ hgc (ldOm2_SC.isSuccLimit.succ_lt hgW), hTSC0.isSuccLimit.succ_lt hgT,
      hylt.trans_le (opow_le_opow_right omega0_pos ?_)⟩
    have key : w + 1 ≤ Om 1 * (Xh + ((w - Om 1 * Xh) / Om 1 + 1)) := by
      rw [mul_add]
      calc w + 1 = Om 1 * Xh + ((w - Om 1 * Xh) + 1) := by rw [← add_assoc, hdec]
        _ ≤ Om 1 * Xh + Om 1 * ((w - Om 1 * Xh) / Om 1 + 1) := by
          refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
          calc w - Om 1 * Xh < Om 1 * ((w - Om 1 * Xh) / Om 1) + Om 1 := Ordinal.lt_mul_div_add _ hΩ0
            _ = Om 1 * ((w - Om 1 * Xh) / Om 1 + 1) := (mul_add_one _ _).symm
    rw [hΘsucc g hgc, hgx]; exact key
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG g' hg'c hg'T
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
    ((add_le_add_iff_left Â).2 (hry.trans hyg'.le))).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
