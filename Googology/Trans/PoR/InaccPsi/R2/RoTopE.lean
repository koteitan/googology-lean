import Googology.Trans.PoR.InaccPsi.R2.RoBlk

/-!
# The tops at every shifted code exponent: `RoTop X 0 ⇒ RoTop X e` for every code `e`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `(X, X̂)` a shift (`Ro.RoSh`).

* `roModX` (`x % Ω₂ = x − X` for `X ≤ x < X + Ω₂`, `Ω₂ ∣ X`);
* `roTopLim` (**the top at a limit code `e`**: `Θ(T_{X+e}(β)) = ψ_{Ω₁}(Â + Ω^{X̂+Θ e})` from the smaller tops;
  "`≤`": the leading exponent `x` of an atom below `T_{X+e}(β)` is `< X` or `X + g` with a code `g < e`;
  "`≥`": the position `z` of the leading digit of `r < Ω^{X̂+Θ e}` is `< X̂` or `X̂ + Θ g` with a code `g < e`);
* `roTopE` (**`RoTop X 0` gives `RoTop X e` for every code `e`**: one induction on the code, `Ro.roTopSucc` at
  successors, `roTopLim` at limits).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- `x % Ω₂ = x − X` for `X ≤ x < X + Ω₂` and `Ω₂ ∣ X`. -/
theorem roModX {X x : Ordinal.{0}} (hd : Om (1 + 1) ∣ X) (h1 : X ≤ x) (h2 : x < X + Om (1 + 1)) :
    x % Om (1 + 1) = x - X := by
  obtain ⟨q, rfl⟩ := hd
  have hlt : x - Om (1 + 1) * q < Om (1 + 1) := by
    have : Om (1 + 1) * q + (x - Om (1 + 1) * q) < Om (1 + 1) * q + Om (1 + 1) := by
      rwa [Ordinal.add_sub_cancel_of_le h1]
    exact (add_lt_add_iff_left _).1 this
  conv_lhs => rw [← Ordinal.add_sub_cancel_of_le h1]
  rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]

/-- `y < Ω^{z+1}` for `z = log_ω y / Ω₁`. -/
theorem roLt_Oe_log (y : Ordinal.{0}) : y < leOe (log ω y / Om 1 + 1) := by
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  unfold leOe
  calc y < ω ^ (log ω y + 1) := by
        rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 y
    _ ≤ ω ^ (Om 1 * (log ω y / Om 1 + 1)) := by
        refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
        rw [mul_add_one]; exact Ordinal.lt_mul_div_add _ hΩ0

/-- `d < W^{x+1}` for `x = log_ω d / Ω₂`. -/
theorem roLt_We_log (d : Ordinal.{0}) : d < leWe (log ω d / Om (1 + 1) + 1) := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  unfold leWe
  calc d < ω ^ (log ω d + 1) := by
        rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 d
    _ ≤ ω ^ (Om (1 + 1) * (log ω d / Om (1 + 1) + 1)) := by
        refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
        rw [mul_add_one]; exact Ordinal.lt_mul_div_add _ hW0

section Main

variable {X Xh : Ordinal.{0}} (hs : RoSh S X Xh) {l ηx : Ordinal.{0}} (hl : IsRestartIdx l)
  (hX : upsilon l < Pv S ηx)

include hs hl hX

/-- **The top of a block of a limit code exponent `X + e`**, from the smaller tops. -/
theorem roTopLim {e : Ordinal.{0}} (hlim : IsSuccLimit e) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (heW : e < Om (1 + 1)) (hIH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e → RoTop S l X Xh e') :
    RoTop S l X Xh e := by
  intro β Â hb hÂ hbase
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have he0 : e ≠ 0 := hlim.ne_bot
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hΘsucc : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ →
      gxTh (upsilon l) (ldAtR S l) (γ + 1) = gxTh (upsilon l) (ldAtR S l) γ + 1 := fun γ hγ => by
    rw [gxTh_add hρSC hAt hγ 1, hΘ1]
  have hcode1 : ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ + 1 < Om (1 + 1) →
      GxCl (upsilon l) (ldAtR S l) (γ + 1) := fun γ hγ h =>
    (ldHull_iff hl hX h).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one γ).trans h)).2 hγ))
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set Y := S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e)) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e)) Y :=
    (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the smaller tops
  have hsubE : ∀ g, GxCl (upsilon l) (ldAtR S l) g → g < e →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X + g) β) =
        S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g)) (Om 1) ∧
      leTe S (X + g) β ∈ ldAtR S l ∧ leTe S (X + g) β < leTe S (X + e) β ∧
      S.psi (Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g)) (Om 1) < Y := by
    intro g hg hge
    have hgW : g < Om (1 + 1) := hge.trans heW
    have hgH : g ∈ cdHull S l := (ldHull_iff hl hX hgW).2 hg
    have hexpg : g < S.psi (β + leWe (X + g)) (Om (1 + 1)) := hexpA _ hg hge.le
    have e1 := hIH g hg hge β Â (roBaseE_mono hge.le hb') hÂ hbase
    have hlt : β + leWe (X + g) < β + leWe (X + e) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 hge))
    refine ⟨e1, ⟨β + leWe (X + g), CSet.add_mem hβH (leWe_mem (CSet.add_mem (hs.mem _ _) hgH)),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · refine psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem (hs.mem _ _) (CSet.of_lt ?_))))
      exact hexpg.trans_le (psi_mono (S := S) (InR_Om_succ 1) hlt.le).1
    · have hΘlt : gxTh (upsilon l) (ldAtR S l) g < gxTh (upsilon l) (ldAtR S l) e := gxTh_lt hg hge
      have hlt2 : Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) g) <
          Â + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh).2 hΘlt))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (hs.memh _ _) (CSet.of_lt ?_)))
      rw [← e1]
      exact gxTh_lt hg hexpg
  have h0e : (0 : Ordinal.{0}) < e := pos_iff_ne_zero.2 he0
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρ0
  have htop : leTe S (X + e) β ∈ ldAtR S l :=
    ⟨β + leWe (X + e), CSet.add_mem hβH (leWe_mem (CSet.add_mem (hs.mem _ _) heH)), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) (leTe S (X + e) β) ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe (X + e) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X + e)) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X + e)) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X + e) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X + e) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxe : x < X + e := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    -- the exponent `g'` of a smaller top above `ψ_{Ω₂}(β + d)`
    obtain ⟨g', hg'c, hg'e, hdg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < e ∧ d < leWe (X + g') := by
      rcases lt_or_ge x X with hxX | hxX
      · refine ⟨0, hc0, h0e, hdx.trans_le (leWe_mono ?_)⟩
        rw [add_zero]; exact Order.add_one_le_of_lt hxX
      · have hxW : x < X + Om (1 + 1) := hxe.trans ((add_lt_add_iff_left X).2 heW)
        have hgm := roModX hs.dvd hxX hxW
        have hgH : x - X ∈ cdHull S l := by rw [← hgm]; exact ldModK_mem ldOm2_SC hxH
        have hge : x - X < e := by
          have : X + (x - X) < X + e := by rwa [Ordinal.add_sub_cancel_of_le hxX]
          exact (add_lt_add_iff_left X).1 this
        have hgc := (ldHull_iff hl hX (hge.trans heW)).1 hgH
        refine ⟨x - X + 1, hcode1 _ hgc ((hlim.succ_lt hge).trans heW), hlim.succ_lt hge, ?_⟩
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxX]; exact hdx
    obtain ⟨e1, -, -, hY1⟩ := hsubE g' hg'c hg'e
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdg'.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < Y
    rw [e1]; exact hY1
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  refine ldPsi1_le hTSC fun x hx _ => ?_
  have hβs : S.psi β (Om (1 + 1)) < leTe S (X + e) β := by
    unfold leTe
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  set z := log ω r / Om 1 with hz_def
  have hlogr : log ω r < Om 1 * (Xh + gxTh (upsilon l) (ldAtR S l) e) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
  have hze : z < Xh + gxTh (upsilon l) (ldAtR S l) e := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
  have hrz := roLt_Oe_log r
  rw [← hz_def] at hrz
  obtain ⟨g', hg'c, hg'e, hrg'⟩ : ∃ g', GxCl (upsilon l) (ldAtR S l) g' ∧ g' < e ∧
      r < leOe (Xh + gxTh (upsilon l) (ldAtR S l) g') := by
    rcases lt_or_ge z Xh with hzX | hzX
    · refine ⟨0, hc0, h0e, hrz.trans_le (leOe_mono ?_)⟩
      rw [gxTh_zero, add_zero]; exact Order.add_one_le_of_lt hzX
    · have hz' : z - Xh < gxTh (upsilon l) (ldAtR S l) e := by
        have : Xh + (z - Xh) < Xh + gxTh (upsilon l) (ldAtR S l) e := by
          rwa [Ordinal.add_sub_cancel_of_le hzX]
        exact (add_lt_add_iff_left Xh).1 this
      obtain ⟨g, hgc, hge, hgz⟩ := gxTh_onto hz'
      refine ⟨g + 1, hcode1 _ hgc ((hlim.succ_lt hge).trans heW), hlim.succ_lt hge, ?_⟩
      rw [hΘsucc g hgc, hgz, ← add_assoc, Ordinal.add_sub_cancel_of_le hzX]; exact hrz
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubE g' hg'c hg'e
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg'.le)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

/-- **`RoTop X 0` gives `RoTop X e` for every code `e`.** -/
theorem roTopE (h0 : RoTop S l X Xh 0) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hec heW
  rcases zero_or_succ_or_isSuccLimit e with h | ⟨e0, he0⟩ | hlim
  · subst h; exact h0
  · rw [succ_eq_add_one] at he0
    subst he0
    have he0W : e0 < Om (1 + 1) := (lt_add_one e0).trans heW
    have he0c : GxCl (upsilon l) (ldAtR S l) e0 :=
      (ldHull_iff hl hX he0W).1 (mem_of_add_one_mem ((ldHull_iff hl hX heW).2 hec))
    exact roTopSucc hs hl hX he0c (IH e0 (lt_add_one e0) he0c he0W)
  · exact roTopLim hs hl hX hlim hec heW (fun e' he' he'e => IH e' he'e he' (he'e.trans heW))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ro
