import Googology.Trans.PoR.InaccPsi.R2.LeELay

/-!
# The block law at every code exponent `e`, and the readings below `ψ_{Ω₂}(Ω₂^{Ω₂})`

`Θ = gxTh ρ_λ (ldAtR λ)` (`= Θ_λ` below `Ω₂`), `W^e = Ω₂^e`, `Ω^x = Ω₁^x`, `T_e(β) = ψ_{Ω₂}(β + W^e)`.

`LeOwnH S λ e β c v` (**`c` is an own argument of exponent `e` over the base `β`, with level-1 image `v`**):
`(e, c, v) = (0, 0, 0)`; `(1, c, Θ c)` for a code `c < ldTop β`; and `(e + 1, W^e·γ + c', Ω^{Θ e}·Θ γ + v')` for
codes `e ≥ 1`, `γ ≠ 0`, `γ < T_{e+1}(β)` and `(e', c', v')` own over `β + W^e·γ` with `e' ≤ e`.  So `v = h(c)` reads
the base-`Ω₂` digits and their exponents at base `Ω₁`: `h(Σ W^{e_i}·γ_i) = Σ Ω^{Θ e_i}·Θ γ_i`.

* `leStepA` (the sub-bases: `Θ(ψ_{Ω₂}(β + W^e·γ)) = ψ_{Ω₁}(Â + Ω^{Θ e}·Θ γ)`), `leTopSucc`, `leTopLim`, `leTopE`
  (**`Θ(T_e(β)) = ψ_{Ω₁}(Â + Ω^{Θ e})` for every code `e ≥ 1`** and every base `β` of exponent `e` with
  `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, `Â` own: by induction on `e`; limits by the digit position bound `Le.leCl_boundK`);
* `leOwnRead` (**THE BLOCK LAW: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + v)`** for every own `(e, c, v)`);
* `leClsE` (**every atom of the block of exponent `e` is `≤ ψ_{Ω₂}(β)` or `ψ_{Ω₂}(β + c)` with `(e', c, v)` own,
  `e' ≤ e`**);
* `leTh_FWW` (**every atom `t < ψ_{Ω₂}(Ω₂^{Ω₂})` is `ψ_{Ω₂}(c)` with `(e, c, v)` own over `0`,
  `e < ψ_{Ω₂}(Ω₂^{Ω₂})`, and
  `Θ_λ(t) = ψ_{Ω₁}(A + 1 + v)`**).

No new axiom.  New definition: `LeOwnH`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **The own arguments of exponent `e` over `β`, with their level-1 images.** -/
inductive LeOwnH (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop
  | zero {β : Ordinal.{0}} : LeOwnH S l 0 β 0 0
  | one {β c : Ordinal.{0}} : GxCl (upsilon l) (ldAtR S l) c → c < ldTop S β →
      LeOwnH S l 1 β c (gxTh (upsilon l) (ldAtR S l) c)
  | succ {e e' β γ c' v : Ordinal.{0}} : GxCl (upsilon l) (ldAtR S l) e → 1 ≤ e →
      GxCl (upsilon l) (ldAtR S l) γ → γ ≠ 0 → γ < leTe S (e + 1) β → e' ≤ e →
      LeOwnH S l e' (β + leWe e * γ) c' v →
      LeOwnH S l (e + 1) β (leWe e * γ + c')
        (leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ + v)

theorem leHatE_own {Â y x : Ordinal.{0}} (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hy : y < S.psi (Â + leOe y * x) (Om 1)) (hx : x < S.psi (Â + leOe y * x) (Om 1)) :
    Â + leOe y * x ∈ S.CSet (Â + leOe y * x) (S.psi (Â + leOe y * x) (Om 1)) :=
  CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leMulOe_mem (CSet.of_lt hy) (CSet.of_lt hx))

theorem leOe_mem {a b y : Ordinal.{0}} (hy : y ∈ S.CSet a b) : leOe y ∈ S.CSet a b := by
  have := leMulOe_mem (S := S) hy (CSet.one_mem a b); rwa [mul_one] at this

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The sub-bases of a block of exponent `e + 1`**, given the tops of exponent `e`. -/
theorem leStepA {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hT : ∀ β' Â', LeBaseE S l e β' → Â' ∈ S.CSet Â' (S.psi Â' (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β' (Om (1 + 1))) = S.psi Â' (Om 1) →
      gxTh (upsilon l) (ldAtR S l) (leTe S e β') =
        S.psi (Â' + leOe (gxTh (upsilon l) (ldAtR S l) e)) (Om 1))
    {β Â : Ordinal.{0}} (hb : LeBaseE S l (e + 1) β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (e + 1) β →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe e * γ) (Om (1 + 1))) =
        S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) ∧
      Â + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ ∈
        S.CSet (Â + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ)
          (S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ) (Om 1)) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have hμ0 : leWe e ≠ 0 := (leWe_pos _).ne'
  set O := leOe (gxTh (upsilon l) (ldAtR S l) e) with hO_def
  have hO0 : O ≠ 0 := (leOe_pos _).ne'
  have hβd' : leWe e * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd
  have hβA' : β + leWe e * Om (1 + 1) < ConjT.Aη S (cdEta S l) := by rw [← leWe_succ]; exact hβA
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (hexp.trans (psi_lt (InR_Om_succ 1) _))).2 hec
  have hsub : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (e + 1) β →
      LeBaseE S l e (β + leWe e * γ) := fun γ hγ hγT =>
    leBaseE_sub hl hX hb' hec ((ldHull_iff hl hX (hγT.trans (leTe_lt_Om2 _ _))).2 hγ) hγT
  have hγs : ∀ γ, γ < leTe S (e + 1) β → γ < S.psi (β + leWe e * γ) (Om (1 + 1)) :=
    fun γ h => leTe_gt hβown hexp hβd h
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hsat : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
      S.psi (β + leWe e * γ) (Om (1 + 1)) ∈ ldAtR S l := by
    intro γ hγ hγW
    refine ⟨β + leWe e * γ, CSet.add_mem hβH (leMulWe_mem heH ((ldHull_iff hl hX hγW).2 hγ)), ?_, rfl⟩
    exact ((add_lt_add_iff_left β).2 (leMulWe_lt hγW)).trans hβA'
  have hslt : ∀ γ γ', γ < γ' → γ' ≤ Om (1 + 1) → 0 < γ' → γ < S.psi (β + leWe e * γ') (Om (1 + 1)) →
      S.psi (β + leWe e * γ) (Om (1 + 1)) < S.psi (β + leWe e * γ') (Om (1 + 1)) := by
    intro γ γ' h hγ'W hγ'0 hown
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulWe_lt h)) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (CSet.of_lt ?_) (CSet.of_lt hown))
    · rw [leWe_succ]; exact leMulWe_mono hγ'W
    · refine hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
      calc leWe e = leWe e * 1 := (mul_one _).symm
        _ ≤ leWe e * γ' := leMulWe_mono (Order.one_le_iff_pos.2 hγ'0)
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hrle : ∀ r γ', GxCl (upsilon l) (ldAtR S l) γ' → r / O = gxTh (upsilon l) (ldAtR S l) γ' →
      r ≤ O * gxTh (upsilon l) (ldAtR S l) (γ' + 1) := by
    intro r γ' hγ' hx
    rw [hΘsucc γ' hγ', ← hx, mul_add_one]
    exact (Ordinal.lt_mul_div_add r hO0).le
  have hΘeX : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < leTe S (e + 1) β → 0 < γ →
      gxTh (upsilon l) (ldAtR S l) e < gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe e * γ) (Om (1 + 1))) := by
    intro γ hγ hγT hγ0
    refine gxTh_lt hec (hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1)
    calc leWe e = leWe e * 1 := (mul_one _).symm
      _ ≤ leWe e * γ := leMulWe_mono (Order.one_le_iff_pos.2 hγ0)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hγT
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  suffices E : gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe e * γ) (Om (1 + 1))) =
      S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) by
    refine ⟨E, ?_⟩
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [gxTh_zero, mul_zero, add_zero]; exact hÂ
    refine leHatE_own hÂ ?_ ?_
    · rw [← E]; exact hΘeX γ hγ hγT (pos_iff_ne_zero.2 hγ0)
    · rw [← E]; exact gxTh_lt hγ (hγs γ hγT)
  rcases zero_or_succ_or_isSuccLimit γ with h0 | ⟨γ', hγ'⟩ | hlim
  · subst h0
    rw [mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]; exact hbase
  · rw [succ_eq_add_one] at hγ'
    subst hγ'
    have hγ'c : GxCl (upsilon l) (ldAtR S l) γ' :=
      (ldHull_iff hl hX ((lt_add_one γ').trans hγW)).1 (mem_of_add_one_mem ((ldHull_iff hl hX hγW).2 hγ))
    have hγ'T : γ' < leTe S (e + 1) β := (lt_add_one γ').trans hγT
    obtain ⟨e', own'⟩ := IH γ' (lt_add_one γ') hγ'c hγ'T
    have h := hT (β + leWe e * γ') _ (hsub γ' hγ'c hγ'T) own' e'
    have eT : leTe S e (β + leWe e * γ') = S.psi (β + leWe e * (γ' + 1)) (Om (1 + 1)) := by
      unfold leTe; rw [add_assoc, ← mul_add_one]
    rw [eT, add_assoc, ← mul_add_one] at h
    rw [h, hΘsucc γ' hγ'c]
  · have hγ0 : γ ≠ 0 := hlim.ne_bot
    have hΘ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
      have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hγ0)
      rwa [gxTh_zero] at this
    have hsγ := hsat γ hγ hγW
    set X := S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) with hX_def
    have hÂX : Â ∈ S.CSet (Â + O * gxTh (upsilon l) (ldAtR S l) γ) X :=
      (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
    have hÂlt : S.psi Â (Om 1) < X :=
      psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (mul_pos (leOe_pos _) hΘ0)) hÂX
    have hlt1 : ∀ γ1, GxCl (upsilon l) (ldAtR S l) γ1 → γ1 < γ →
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe e * γ1) (Om (1 + 1))) =
          S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) ∧
        S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) γ1) (Om 1) < X := by
      intro γ1 hγ1 h1
      obtain ⟨e1, own1⟩ := IH γ1 h1 hγ1 (h1.trans hγT)
      have hlt : Â + O * gxTh (upsilon l) (ldAtR S l) γ1 < Â + O * gxTh (upsilon l) (ldAtR S l) γ :=
        (add_lt_add_iff_left Â).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 (gxTh_lt hγ1 h1))
      exact ⟨e1, psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)⟩
    apply le_antisymm
    · refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
      intro t ht hts
      obtain ⟨a, haH, -, rfl⟩ := ht
      rcases lt_or_ge a β with haβ | haβ
      · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
      have haγ : a < β + leWe e * γ := by
        by_contra h
        push Not at h
        exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
      obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 hβd' haβ (haγ.trans ((add_lt_add_iff_left β).2 (leMulWe_lt hγW)))
      have hgγ : a % (leWe e * Om (1 + 1)) / leWe e < γ := by
        by_contra h
        push Not at h
        exact absurd (((add_le_add_iff_left β).2 (leMulWe_mono h)).trans hlo) (not_le.2 haγ)
      have hgH : a % (leWe e * Om (1 + 1)) / leWe e ∈ cdHull S l := by
        have h1 : a % (leWe e * Om (1 + 1)) ∈ cdHull S l := by
          rw [← leWe_succ]; exact leModP_mem _ haH
        have h2 : a % (leWe e * Om (1 + 1)) < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
          have : leWe e * Om (1 + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
            rw [← leWe_succ]; unfold leWe; rw [mul_add_one]
          rw [← this]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
        exact leDivOp_mem (dvd_mul_right _ _) h1 h2
      have hgc := (ldHull_iff hl hX hgW).1 hgH
      have hg1γ := hlim.succ_lt hgγ
      have hg1c := hcode1 _ hgc (hg1γ.trans hγW)
      obtain ⟨e1, hlt⟩ := hlt1 _ hg1c hg1γ
      refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
      rw [e1]; exact hlt
    · obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsγ
      refine ldPsi1_le hTSC fun x hx _ => ?_
      have hβs : S.psi β (Om (1 + 1)) < S.psi (β + leWe e * γ) (Om (1 + 1)) := by
        have := hslt 0 γ (pos_iff_ne_zero.2 hγ0) hγW.le (pos_iff_ne_zero.2 hγ0)
          ((pos_iff_ne_zero.2 hγ0).trans (hγs γ hγT))
        rwa [mul_zero, add_zero] at this
      rcases le_or_gt x Â with hxÂ | hxÂ
      · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
        rw [← hbase]; exact hTs _ hβat hβs
      obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
      have hr : r < O * gxTh (upsilon l) (ldAtR S l) γ := (add_lt_add_iff_left Â).1 hx
      have hx' : r / O < gxTh (upsilon l) (ldAtR S l) γ := (Ordinal.lt_mul_iff_div_lt hO0).1 hr
      obtain ⟨γ', hγ'c, hγ'γ, hγ'x⟩ := gxTh_onto hx'
      have hγ'1 := hlim.succ_lt hγ'γ
      have hγ'1c := hcode1 _ hγ'c (hγ'1.trans hγW)
      obtain ⟨e1, -⟩ := hlt1 _ hγ'1c hγ'1
      refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
        ((add_le_add_iff_left Â).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
      rw [← e1]
      exact hTs _ (hsat _ hγ'1c (hγ'1.trans hγW)) (hslt _ γ hγ'1 hγW.le (pos_iff_ne_zero.2 hγ0)
        (hγ'1.trans (hγs γ hγT)))

/-- **The top of a block of exponent `e + 1`**: `Θ(T_{e+1}(β)) = ψ_{Ω₁}(Â + Ω^{Θ(e+1)})`. -/
theorem leTopSucc {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hT : ∀ β' Â', LeBaseE S l e β' → Â' ∈ S.CSet Â' (S.psi Â' (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β' (Om (1 + 1))) = S.psi Â' (Om 1) →
      gxTh (upsilon l) (ldAtR S l) (leTe S e β') =
        S.psi (Â' + leOe (gxTh (upsilon l) (ldAtR S l) e)) (Om 1))
    {β Â : Ordinal.{0}} (hb : LeBaseE S l (e + 1) β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (e + 1) β) =
      S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) (e + 1))) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hA := leStepA hl hX hec hT hb hÂ hbase
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have hμ0 : leWe e ≠ 0 := (leWe_pos _).ne'
  set O := leOe (gxTh (upsilon l) (ldAtR S l) e) with hO_def
  have hO0 : O ≠ 0 := (leOe_pos _).ne'
  have hβd' : leWe e * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (hexp.trans (psi_lt (InR_Om_succ 1) _))).2 hec
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hrle : ∀ r γ', GxCl (upsilon l) (ldAtR S l) γ' → r / O = gxTh (upsilon l) (ldAtR S l) γ' →
      r ≤ O * gxTh (upsilon l) (ldAtR S l) (γ' + 1) := by
    intro r γ' hγ' hx
    rw [hΘsucc γ' hγ', ← hx, mul_add_one]
    exact (Ordinal.lt_mul_div_add r hO0).le
  have hTW : leTe S (e + 1) β = S.psi (β + leWe e * Om (1 + 1)) (Om (1 + 1)) := leTe_succ e β
  have hγs : ∀ γ, γ < leTe S (e + 1) β → γ < S.psi (β + leWe e * γ) (Om (1 + 1)) :=
    fun γ h => leTe_gt hβown hexp hβd h
  have htat : leTe S (e + 1) β ∈ ldAtR S l :=
    ⟨β + leWe (e + 1), CSet.add_mem hβH (leWe_mem (CSet.succ_mem heH)), hβA, rfl⟩
  rw [hΘsucc e hec, leOe_succ]
  set X := S.psi (Â + O * Om 1) (Om 1) with hX_def
  have hÂX : Â ∈ S.CSet (Â + O * Om 1) X := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < X :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (mul_pos (leOe_pos _) (Om_pos one_ne_zero))) hÂX
  have hsubX : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g < leTe S (e + 1) β →
      S.psi (Â + O * gxTh (upsilon l) (ldAtR S l) g) (Om 1) < X := by
    intro g hg hgT
    obtain ⟨e1, own1⟩ := hA g hg hgT
    have hΘ1' : gxTh (upsilon l) (ldAtR S l) g < Om 1 := by
      refine (gxTh_lt hg (hγs g hgT)).trans ?_
      rw [e1]; exact psi_lt Low.InR_Om_one _
    have hlt : Â + O * gxTh (upsilon l) (ldAtR S l) g < Â + O * Om 1 :=
      (add_lt_add_iff_left Â).2 ((mul_lt_mul_iff_right₀ (leOe_pos _)).2 hΘ1')
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono (S := S) Low.InR_Om_one hlt.le).2 own1)
  have hsubT : ∀ g, g < leTe S (e + 1) β → S.psi (β + leWe e * g) (Om (1 + 1)) < leTe S (e + 1) β := by
    intro g hgT
    rw [hTW]
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leMulWe_lt (hgT.trans (leTe_lt_Om2 _ _)))) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (CSet.of_lt ?_) (CSet.of_lt (by rw [← hTW]; exact hgT)))
    · rw [leWe_succ]
    · refine hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
      calc leWe e = leWe e * 1 := (mul_one _).symm
        _ ≤ leWe e * Om (1 + 1) := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC)).le
  have hsat : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
      S.psi (β + leWe e * γ) (Om (1 + 1)) ∈ ldAtR S l := by
    intro γ hγ hγW
    refine ⟨β + leWe e * γ, CSet.add_mem hβH (leMulWe_mem heH ((ldHull_iff hl hX hγW).2 hγ)), ?_, rfl⟩
    refine lt_of_lt_of_le ((add_lt_add_iff_left β).2 (leMulWe_lt hγW)) ?_
    rw [← leWe_succ]; exact hβA.le
  have hup : gxTh (upsilon l) (ldAtR S l) (leTe S (e + 1) β) ≤ X := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    have ha2 : a < β + leWe e * Om (1 + 1) := by
      by_contra h
      push Not at h
      rw [hTW] at hts
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
    obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 hβd' haβ ha2
    have hgH : a % (leWe e * Om (1 + 1)) / leWe e ∈ cdHull S l := by
      have h1 : a % (leWe e * Om (1 + 1)) ∈ cdHull S l := by
        rw [← leWe_succ]; exact leModP_mem _ haH
      have h2 : a % (leWe e * Om (1 + 1)) < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
        have : leWe e * Om (1 + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
          rw [← leWe_succ]; unfold leWe; rw [mul_add_one]
        rw [← this]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
      exact leDivOp_mem (dvd_mul_right _ _) h1 h2
    have hgc := (ldHull_iff hl hX hgW).1 hgH
    have hgT : a % (leWe e * Om (1 + 1)) / leWe e < leTe S (e + 1) β := by
      by_contra h
      push Not at h
      have h1 := leTe_ge hβown hexp hβd h
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) hlo).1) (not_le.2 hts)
    have hg1T := (leTe_SC (S := S) (e + 1) β).isSuccLimit.succ_lt hgT
    have hg1c := hcode1 _ hgc (hg1T.trans (leTe_lt_Om2 _ _))
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1) ?_
    rw [(hA _ hg1c hg1T).1]; exact hsubX _ hg1c hg1T
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htat
  have hT1 : gxTh (upsilon l) (ldAtR S l) (leTe S (e + 1) β) < Om 1 := hup.trans_lt (psi_lt Low.InR_Om_one _)
  have heT : e < leTe S (e + 1) β :=
    hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono (lt_add_one e).le))).1
  have hΘeT := gxTh_lt hec heT
  refine lePsi1_le hTSC fun x hx hc => ?_
  have hβs : S.psi β (Om (1 + 1)) < leTe S (e + 1) β := by
    unfold leTe
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < O * Om 1 := (add_lt_add_iff_left Â).1 hx
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hy1 : gxTh (upsilon l) (ldAtR S l) e + 1 < S.psi 0 (Om (1 + 1)) :=
    (Ph.ph_SC_Om1.isSuccLimit.succ_lt (hΘeT.trans hT1)).trans hΩG1
  have eP : O * Om 1 = leOe (gxTh (upsilon l) (ldAtR S l) e + 1) := (leOe_succ _).symm
  have eP2 : leOe (gxTh (upsilon l) (ldAtR S l) e + 1) =
      ω ^ (Om 1 * gxTh (upsilon l) (ldAtR S l) e + Om 1) := by unfold leOe; rw [mul_add_one]
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * (gxTh (upsilon l) (ldAtR S l) e + 1)) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (gxTh (upsilon l) (ldAtR S l) e + 1)) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hy1).2] at hc2
  rw [eP] at hr
  have hmod : (Â + r) % leOe (gxTh (upsilon l) (ldAtR S l) e + 1) =
      Â % leOe (gxTh (upsilon l) (ldAtR S l) e + 1) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  have hlt' : Â % leOe (gxTh (upsilon l) (ldAtR S l) e + 1) + r <
      ω ^ (Om 1 * gxTh (upsilon l) (ldAtR S l) e + Om 1) := by
    rw [← eP2]; exact isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hbnd := leCl_boundY hTSC Ph.ph_SC_Om1 (LeCl.small hΘeT) _ hc2 hlt'
  change _ < O * _ at hbnd
  have hrT : r < O * gxTh (upsilon l) (ldAtR S l) (leTe S (e + 1) β) := le_add_self.trans_lt hbnd
  have hx' := (Ordinal.lt_mul_iff_div_lt hO0).1 hrT
  obtain ⟨γ', hγ'c, hγ'T, hγ'x⟩ := gxTh_onto hx'
  have hγ'1T := (leTe_SC (S := S) (e + 1) β).isSuccLimit.succ_lt hγ'T
  have hγ'1c := hcode1 _ hγ'c (hγ'1T.trans (leTe_lt_Om2 _ _))
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
    ((add_le_add_iff_left Â).2 (hrle r γ' hγ'c hγ'x.symm))).1 ?_
  rw [← (hA _ hγ'1c hγ'1T).1]
  exact hTs _ (hsat _ hγ'1c (hγ'1T.trans (leTe_lt_Om2 _ _))) (hsubT _ hγ'1T)

/-- **The top of a block of a limit exponent `e`**: `Θ(T_e(β)) = ψ_{Ω₁}(Â + Ω^{Θ e})`. -/
theorem leTopLim {e : Ordinal.{0}} (hlim : IsSuccLimit e) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hIH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → 1 ≤ e' → e' < e → ∀ β' Â', LeBaseE S l e' β' →
      Â' ∈ S.CSet Â' (S.psi Â' (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi β' (Om (1 + 1))) = S.psi Â' (Om 1) →
      gxTh (upsilon l) (ldAtR S l) (leTe S e' β') =
        S.psi (Â' + leOe (gxTh (upsilon l) (ldAtR S l) e')) (Om 1))
    {β Â : Ordinal.{0}} (hb : LeBaseE S l e β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S e β) = S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) e)) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec le_rfl
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
  have he0 : e ≠ 0 := hlim.ne_bot
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  have hΘe0 : 0 < gxTh (upsilon l) (ldAtR S l) e := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 he0)
    rwa [gxTh_zero] at this
  set X := S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) e)) (Om 1) with hX_def
  have hÂX : Â ∈ S.CSet (Â + leOe (gxTh (upsilon l) (ldAtR S l) e)) X :=
    (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < X := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂX
  -- the smaller tops
  have hsubE : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g + 1 < e →
      gxTh (upsilon l) (ldAtR S l) (leTe S (g + 1) β) =
        S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) (g + 1))) (Om 1) ∧
      leTe S (g + 1) β ∈ ldAtR S l ∧ leTe S (g + 1) β < leTe S e β ∧
      S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) (g + 1))) (Om 1) < X := by
    intro g hg hg1
    have hg1W : g + 1 < Om (1 + 1) := hg1.trans heW
    have hg1c := hcode1 g hg (hg1W)
    have hg1H : g + 1 ∈ cdHull S l := (ldHull_iff hl hX hg1W).2 hg1c
    have hexp1 : g + 1 < S.psi (β + leWe (g + 1)) (Om (1 + 1)) := hexpA _ hg1c hg1.le
    have e1 := hIH (g + 1) hg1c le_add_self hg1 β Â (leBaseE_mono hg1.le hb') hÂ hbase
    have hlt : β + leWe (g + 1) < β + leWe e := (add_lt_add_iff_left β).2 (leWe_lt hg1)
    refine ⟨e1, ⟨β + leWe (g + 1), CSet.add_mem hβH (leWe_mem hg1H), hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · refine psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl) (leWe_mem (CSet.of_lt ?_)))
      exact hexp1.trans_le (psi_mono (S := S) (InR_Om_succ 1) hlt.le).1
    · have hΘlt : gxTh (upsilon l) (ldAtR S l) (g + 1) < gxTh (upsilon l) (ldAtR S l) e := gxTh_lt hg1c hg1
      have hlt2 : Â + leOe (gxTh (upsilon l) (ldAtR S l) (g + 1)) < Â + leOe (gxTh (upsilon l) (ldAtR S l) e) :=
        (add_lt_add_iff_left Â).2 (leOe_lt hΘlt)
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leOe_mem (CSet.of_lt ?_))
      rw [← e1]
      exact gxTh_lt hg1c (hexp1.trans_le (le_refl _))
  have htop : leTe S e β ∈ ldAtR S l :=
    ⟨β + leWe e, CSet.add_mem hβH (leWe_mem ((ldHull_iff hl hX heW).2 hec)), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) (leTe S e β) ≤ X := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe e := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * e) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * e) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe e = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    have hlogd : log ω d < Om (1 + 1) * e :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hge : log ω d / Om (1 + 1) < e := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hgH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hgc := (ldHull_iff hl hX (hge.trans heW)).1 hgH
    have hg1 := hlim.succ_lt hge
    have hdg : d < leWe (log ω d / Om (1 + 1) + 1) := by
      unfold leWe
      calc d < ω ^ (log ω d + 1) := by
            rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d
        _ ≤ ω ^ (Om (1 + 1) * (log ω d / Om (1 + 1) + 1)) := by
            refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
            rw [mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0
    obtain ⟨e1, -, -, hX1⟩ := hsubE _ hgc hg1
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdg.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < X
    rw [e1]; exact hX1
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hT1 : gxTh (upsilon l) (ldAtR S l) (leTe S e β) < Om 1 := hup.trans_lt (psi_lt Low.InR_Om_one _)
  have hΘeT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hec hexp
  have hΘe1 : gxTh (upsilon l) (ldAtR S l) e < Om 1 := hΘeT.trans hT1
  refine lePsi1_le hTSC fun x hx hc => ?_
  have hβs : S.psi β (Om (1 + 1)) < leTe S e β := by
    unfold leTe
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (gxTh (upsilon l) (ldAtR S l) e) := (add_lt_add_iff_left Â).1 hx
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * gxTh (upsilon l) (ldAtR S l) e) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (gxTh (upsilon l) (ldAtR S l) e)) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 (hΘe1.trans hΩG1)).2] at hc2
  have hmod : (Â + r) % leOe (gxTh (upsilon l) (ldAtR S l) e) =
      Â % leOe (gxTh (upsilon l) (ldAtR S l) e) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (gxTh (upsilon l) (ldAtR S l) e) + r with hy_def
  have hyP : y < leOe (gxTh (upsilon l) (ldAtR S l) e) :=
    isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  have hlogy : log ω y < Om 1 * gxTh (upsilon l) (ldAtR S l) e :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hlogC := (leClDec hTSC Ph.ph_SC_Om1 y hc2).2
  have hb := leCl_boundK hTSC Ph.ph_SC_Om1 _ hlogC
    (hlogy.trans ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 hΘe1))
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hδT := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hb
  have hδe := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogy
  obtain ⟨g, hgc, -, hgx⟩ := gxTh_onto hδT
  have hge : g < e := by
    by_contra h
    push Not at h
    exact absurd (hgx ▸ gxTh_mono h) (not_le.2 hδe)
  have hg1 := hlim.succ_lt hge
  have hyg : y < leOe (gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    rw [hΘsucc g hgc, hgx]
    unfold leOe
    calc y < ω ^ (log ω y + 1) := by
          rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 y
      _ ≤ ω ^ (Om 1 * (log ω y / Om 1 + 1)) := by
          refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
          rw [mul_add_one]; exact Ordinal.lt_mul_div_add _ hΩ0
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubE g hgc hg1
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one
    ((add_le_add_iff_left Â).2 (hry.trans hyg.le))).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

/-- **`Θ(T_e(β)) = ψ_{Ω₁}(Â + Ω^{Θ e})` for every code `e ≥ 1`.** -/
theorem leTopE : ∀ e, GxCl (upsilon l) (ldAtR S l) e → 1 ≤ e → ∀ β Â, LeBaseE S l e β →
    Â ∈ S.CSet Â (S.psi Â (Om 1)) →
    gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
    gxTh (upsilon l) (ldAtR S l) (leTe S e β) = S.psi (Â + leOe (gxTh (upsilon l) (ldAtR S l) e)) (Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hec he1 β Â hb hÂ hbase
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | he00
    · -- the base case `e = 1`
      rw [zero_add] at hb ⊢
      obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
      rw [leWe_one] at hβd hβA hβown
      have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
      rw [leTe_one, hΘ1, leOe_one]
      exact ldBlk_next hl hX hβown hβd hβH hβA hÂ hbase
    · have he0W : e0 < Om (1 + 1) := by
        obtain ⟨-, -, -, -, hexpA⟩ := hb
        exact (lt_add_one e0).trans ((hexpA _ hec le_rfl).trans (psi_lt (InR_Om_succ 1) _))
      have he0c : GxCl (upsilon l) (ldAtR S l) e0 :=
        (ldHull_iff hl hX he0W).1 (mem_of_add_one_mem ((ldHull_iff hl hX
          (ldOm2_SC.isSuccLimit.succ_lt he0W)).2 hec))
      exact leTopSucc hl hX he0c (fun β' Â' hb' hÂ' hbase' =>
        IH e0 (lt_add_one e0) he0c (Order.one_le_iff_ne_zero.2 he00) β' Â' hb' hÂ' hbase') hb hÂ hbase
  · exact leTopLim hl hX hlim hec (fun e' he' he'1 he'e => IH e' he'e he' he'1) hb hÂ hbase

/-- **THE BLOCK LAW**: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + v)` for every own `(e, c, v)` over a base `β` of exponent `e`. -/
theorem leOwnRead {e β c v : Ordinal.{0}} (h : LeOwnH S l e β c v) : ∀ Â, LeBaseE S l e β →
    Â ∈ S.CSet Â (S.psi Â (Om 1)) →
    gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1) →
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + c) (Om (1 + 1))) = S.psi (Â + v) (Om 1) ∧
    Â + v ∈ S.CSet (Â + v) (S.psi (Â + v) (Om 1)) ∧ v < leOe (gxTh (upsilon l) (ldAtR S l) e) ∧
      c < leWe e := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  induction h with
  | zero =>
    intro Â _ hÂ hbase
    rw [add_zero, add_zero, gxTh_zero, leOe_zero, leWe_zero]
    exact ⟨hbase, hÂ, one_pos, one_pos⟩
  | @one β c hc hcF =>
    intro Â hb hÂ hbase
    obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
    rw [leWe_one] at hβd hβA hβown
    have hstep := ldBlk_step hl hX hβown hβd hβH hβA hÂ hbase c hc hcF
    have hlt : gxTh (upsilon l) (ldAtR S l) c < S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
      rw [← hstep]; exact gxTh_lt hc (ldTop_gt hβown hβd hcF)
    refine ⟨hstep, CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (CSet.of_lt hlt), ?_, ?_⟩
    · rw [hΘ1, leOe_one]; exact hlt.trans (psi_lt Low.InR_Om_one _)
    · rw [leWe_one]; exact hcF.trans (ldTop_lt_Om2 β)
  | @succ e e' β γ c' v hec he1 hγc hγ0 hγT he'e _ ih =>
    intro Â hb hÂ hbase
    have hT := fun β' Â' hb' hÂ' hbase' => leTopE hl hX e hec he1 β' Â' hb' hÂ' hbase'
    obtain ⟨eγ, ownγ⟩ := leStepA hl hX hec hT hb hÂ hbase γ hγc hγT
    have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
    have hbsub := leBaseE_sub hl hX hb hec ((ldHull_iff hl hX hγW).2 hγc) hγT
    obtain ⟨e2, own2, hv, hc'⟩ := ih _ (leBaseE_mono he'e hbsub) ownγ eγ
    rw [← add_assoc β, ← add_assoc Â]
    refine ⟨e2, own2, ?_, ?_⟩
    · obtain ⟨hβd, -, -, hβown, hexpA⟩ := hb
      have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
      have hγs : γ < S.psi (β + leWe e * γ) (Om (1 + 1)) := leTe_gt hβown hexp hβd hγT
      have hΘγ1 : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := by
        refine (gxTh_lt hγc hγs).trans ?_
        rw [eγ]; exact psi_lt Low.InR_Om_one _
      have hvO : v < leOe (gxTh (upsilon l) (ldAtR S l) e) := hv.trans_le (leOe_mono (gxTh_mono he'e))
      rw [gxTh_add hρSC hAt hec 1, hΘ1, leOe_succ]
      calc leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ + v
          < leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) γ +
              leOe (gxTh (upsilon l) (ldAtR S l) e) := (add_lt_add_iff_left _).2 hvO
        _ = leOe (gxTh (upsilon l) (ldAtR S l) e) * (gxTh (upsilon l) (ldAtR S l) γ + 1) := (mul_add_one _ _).symm
        _ ≤ leOe (gxTh (upsilon l) (ldAtR S l) e) * Om 1 := mul_le_mul_right (Order.add_one_le_of_lt hΘγ1) _
    · have hc'e : c' < leWe e := hc'.trans_le (leWe_mono he'e)
      rw [leWe_succ]
      calc leWe e * γ + c' < leWe e * γ + leWe e := (add_lt_add_iff_left _).2 hc'e
        _ = leWe e * (γ + 1) := (mul_add_one _ _).symm
        _ ≤ leWe e * Om (1 + 1) := leMulWe_mono (Order.add_one_le_of_lt hγW)

/-- **Every atom of the block of exponent `e` is `≤ ψ_{Ω₂}(β)` or `ψ_{Ω₂}(β + c)` with `(e', c, v)` own, `e' ≤ e`.** -/
theorem leClsE : ∀ e, GxCl (upsilon l) (ldAtR S l) e → 1 ≤ e → ∀ β, LeBaseE S l e β →
    ∀ t ∈ ldAtR S l, t < leTe S e β →
      t ≤ S.psi β (Om (1 + 1)) ∨
        ∃ e' c v, e' ≤ e ∧ LeOwnH S l e' β c v ∧ t = S.psi (β + c) (Om (1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have h1T : ∀ e β, (1 : Ordinal.{0}) < leTe S e β := fun e β =>
    (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_Te _ _)
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hec he1 β hb t ht htT
  have hb' := hb
  obtain ⟨hβd, hβH, -, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec le_rfl
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | he00
    · rw [zero_add] at hβd hβown htT
      rw [leWe_one] at hβd hβown
      rw [leTe_one] at htT
      rcases ldBlk_cls hl hX hβown hβd ⟨a, haH, haA, rfl⟩ htT with h | ⟨c, hc, hcF, e⟩
      · exact Or.inl h
      · exact Or.inr ⟨1, c, _, by rw [zero_add], LeOwnH.one hc hcF, e⟩
    have he0W : e0 < Om (1 + 1) := (lt_add_one e0).trans heW
    have he0c : GxCl (upsilon l) (ldAtR S l) e0 :=
      (ldHull_iff hl hX he0W).1 (mem_of_add_one_mem ((ldHull_iff hl hX heW).2 hec))
    have he01 : 1 ≤ e0 := Order.one_le_iff_ne_zero.2 he00
    have hexp0 : e0 < S.psi (β + leWe e0) (Om (1 + 1)) := hexpA e0 he0c (lt_add_one e0).le
    have hμ0 : leWe e0 ≠ 0 := (leWe_pos _).ne'
    have hβd' : leWe e0 * Om (1 + 1) ∣ β := by rw [← leWe_succ]; exact hβd
    have hTW : leTe S (e0 + 1) β = S.psi (β + leWe e0 * Om (1 + 1)) (Om (1 + 1)) := leTe_succ e0 β
    have ha2 : a < β + leWe e0 * Om (1 + 1) := by
      by_contra h
      push Not at h
      rw [hTW] at htT
      exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
    obtain ⟨hgW, hlo, hhi⟩ := leSplitE hμ0 hβd' haβ ha2
    set g := a % (leWe e0 * Om (1 + 1)) / leWe e0 with hg_def
    have hgH : g ∈ cdHull S l := by
      have h1 : a % (leWe e0 * Om (1 + 1)) ∈ cdHull S l := by
        rw [← leWe_succ]; exact leModP_mem _ haH
      have h2 : a % (leWe e0 * Om (1 + 1)) < ω ^ (Om (1 + 1) * e0 + Om (1 + 1)) := by
        have : leWe e0 * Om (1 + 1) = ω ^ (Om (1 + 1) * e0 + Om (1 + 1)) := by
          rw [← leWe_succ]; unfold leWe; rw [mul_add_one]
        rw [← this]; exact Ordinal.mod_lt _ (mul_ne_zero hμ0 ldOm2_SC.1.ne')
      exact leDivOp_mem (dvd_mul_right _ _) h1 h2
    have hgc := (ldHull_iff hl hX hgW).1 hgH
    have hgT : g < leTe S (e0 + 1) β := by
      by_contra h
      push Not at h
      have h1 := leTe_ge hβown hexp0 hβd h
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) hlo).1) (not_le.2 htT)
    have hb2 := leBaseE_sub hl hX hb' he0c hgH hgT
    rcases lt_or_ge (S.psi a (Om (1 + 1))) (leTe S e0 (β + leWe e0 * g)) with hlt | hge
    · rcases IH e0 (lt_add_one e0) he0c he01 _ hb2 _ ⟨a, haH, haA, rfl⟩ hlt with hle | ⟨e1, c', v, he1e0, hown, e⟩
      · have heq : S.psi a (Om (1 + 1)) = S.psi (β + leWe e0 * g) (Om (1 + 1)) :=
          le_antisymm hle (psi_mono (S := S) (InR_Om_succ 1) hlo).1
        rcases eq_or_ne g 0 with hg0 | hg0
        · rw [hg0, mul_zero, add_zero] at heq; exact Or.inl heq.le
        · refine Or.inr ⟨e0 + 1, leWe e0 * g + 0, _, le_rfl,
            LeOwnH.succ he0c he01 hgc hg0 hgT zero_le LeOwnH.zero, ?_⟩
          rw [add_zero]; exact heq
      · rcases eq_or_ne g 0 with hg0 | hg0
        · rw [hg0, mul_zero, add_zero] at hown e
          exact Or.inr ⟨e1, c', v, he1e0.trans (lt_add_one e0).le, hown, e⟩
        · exact Or.inr ⟨e0 + 1, leWe e0 * g + c', _, le_rfl,
            LeOwnH.succ he0c he01 hgc hg0 hgT he1e0 hown, by rw [← add_assoc]; exact e⟩
    · have hg1T := (leTe_SC (S := S) (e0 + 1) β).isSuccLimit.succ_lt hgT
      have hg1c := hcode1 _ hgc (hg1T.trans (leTe_lt_Om2 _ _))
      have eT : leTe S e0 (β + leWe e0 * g) = S.psi (β + leWe e0 * (g + 1)) (Om (1 + 1)) := by
        unfold leTe; rw [add_assoc, ← mul_add_one]
      rw [eT] at hge
      refine Or.inr ⟨e0 + 1, leWe e0 * (g + 1) + 0, _, le_rfl,
        LeOwnH.succ he0c he01 hg1c (add_pos_of_right zero_lt_one g).ne' hg1T zero_le
          LeOwnH.zero, ?_⟩
      rw [add_zero]
      exact le_antisymm (psi_mono (S := S) (InR_Om_succ 1) hhi.le).1 hge
  · obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe e := by
      by_contra h
      push Not at h
      exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact Or.inl le_rfl
    have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * e) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * e) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe e = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    have hlogd : log ω d < Om (1 + 1) * e :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hge : log ω d / Om (1 + 1) < e := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hgH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hgc := (ldHull_iff hl hX (hge.trans heW)).1 hgH
    have hg1 := hlim.succ_lt hge
    have hg1c := hcode1 _ hgc (hg1.trans heW)
    have hdg : d < leWe (log ω d / Om (1 + 1) + 1) := by
      unfold leWe
      calc d < ω ^ (log ω d + 1) := by
            rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d
        _ ≤ ω ^ (Om (1 + 1) * (log ω d / Om (1 + 1) + 1)) := by
            refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
            rw [mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0
    have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S (log ω d / Om (1 + 1) + 1) β :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdg.le)).1
    rcases hle.lt_or_eq with hlt | heq
    · rcases IH _ hg1 hg1c le_add_self β (leBaseE_mono hg1.le hb') _ ⟨β + d, haH, haA, rfl⟩ hlt with
        h | ⟨e1, c, v, he1, hown, e⟩
      · exact Or.inl h
      · exact Or.inr ⟨e1, c, v, he1.trans hg1.le, hown, e⟩
    · have hg2 := hlim.succ_lt hg1
      refine Or.inr ⟨log ω d / Om (1 + 1) + 1 + 1, leWe (log ω d / Om (1 + 1) + 1) * 1 + 0, _, hg2.le,
        LeOwnH.succ hg1c le_add_self hc1 one_ne_zero (h1T _ _) zero_le LeOwnH.zero, ?_⟩
      rw [heq, mul_one, add_zero]; rfl

/-- **Every atom `t < ψ_{Ω₂}(Ω₂^{Ω₂})` is `ψ_{Ω₂}(c)` with `(e, c, v)` own over `0`, and
`Θ_λ(t) = ψ_{Ω₁}(A + 1 + v)`.** -/
theorem leTh_FWW {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ t ∈ ldAtR S l, t < leFWW S → ∃ e c v, e < leFWW S ∧ LeOwnH S l e 0 c v ∧ t = S.psi c (Om (1 + 1)) ∧
      gxTh (upsilon l) (ldAtR S l) t = S.psi (A + 1 + v) (Om 1) ∧
      A + 1 + v ∈ S.CSet (A + 1 + v) (S.psi (A + 1 + v) (Om 1)) ∧
      v < leOe (gxTh (upsilon l) (ldAtR S l) e) ∧ c < leWe e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hbase0 := ldBlk_zero hA hρ
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hF0 : (0 : Ordinal.{0}) < leFWW S := (Om_pos one_ne_zero).trans (psiS_bounds (S := S) _ 1).1
  intro t ht htF
  obtain ⟨a, haH, haA, rfl⟩ := ht
  have hrep : ∃ e c v, e < leFWW S ∧ LeOwnH S l e 0 c v ∧
      S.psi a (Om (1 + 1)) = S.psi c (Om (1 + 1)) := by
    rcases eq_or_ne a 0 with rfl | ha0
    · exact ⟨0, 0, 0, hF0, LeOwnH.zero, rfl⟩
    have haW : a < leWe (Om (1 + 1)) := by
      by_contra h
      push Not at h
      exact absurd htF (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
    have hloga : log ω a < Om (1 + 1) * Om (1 + 1) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω ha0).trans_lt haW)
    have hgW : log ω a / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hloga
    have hgH : log ω a / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem haH)
    have hgc := (ldHull_iff hl hX hgW).1 hgH
    have hgF : log ω a / Om (1 + 1) < leFWW S := by
      by_contra h
      push Not at h
      have h1 := leFWW_ge (S := S) h
      have h2 : leWe (log ω a / Om (1 + 1)) ≤ a := by
        unfold leWe
        exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω ha0)
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) h2).1) (not_le.2 htF)
    set E := log ω a / Om (1 + 1) + 1 with hE_def
    have hEF : E < leFWW S := leFWW_SC.isSuccLimit.succ_lt hgF
    have hEW : E < Om (1 + 1) := hEF.trans leFWW_lt_Om2
    have hEc : GxCl (upsilon l) (ldAtR S l) E := (ldHull_iff hl hX hEW).1 (CSet.succ_mem hgH)
    have haE : a < leWe E := by
      unfold leWe
      calc a < ω ^ (log ω a + 1) := by
            rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 a
        _ ≤ ω ^ (Om (1 + 1) * E) := by
            refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
            rw [hE_def, mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0
    have hle : S.psi a (Om (1 + 1)) ≤ leTe S E 0 := by
      unfold leTe; rw [zero_add]; exact (psi_mono (S := S) (InR_Om_succ 1) haE.le).1
    rcases hle.lt_or_eq with hlt | heq
    · rcases leClsE hl hX E hEc le_add_self 0 (leBaseE_zero l hEF) _ ⟨a, haH, haA, rfl⟩ hlt with
        h0 | ⟨e', c, v, he', hown, e⟩
      · exact ⟨0, 0, 0, hF0, LeOwnH.zero, le_antisymm h0 (psi_mono (S := S) (InR_Om_succ 1) zero_le).1⟩
      · rw [zero_add] at e; exact ⟨e', c, v, he'.trans_lt hEF, hown, e⟩
    · have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
      have h1T : (1 : Ordinal.{0}) < leTe S (E + 1) 0 :=
        (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).trans (leOm1_lt_Te _ _)
      refine ⟨E + 1, leWe E * 1 + 0, _, leFWW_SC.isSuccLimit.succ_lt hEF,
        LeOwnH.succ hEc le_add_self hc1 one_ne_zero h1T zero_le LeOwnH.zero, ?_⟩
      rw [heq, mul_one, add_zero]; unfold leTe; rw [zero_add]
  obtain ⟨e, c, v, heF, hown, he⟩ := hrep
  obtain ⟨e1, own, hv, hc⟩ := leOwnRead hl hX hown (A + 1) (leBaseE_zero l heF) hA1 hbase0
  rw [zero_add] at e1
  exact ⟨e, c, v, heF, hown, he, by rw [he]; exact e1, own, hv, hc⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Le
