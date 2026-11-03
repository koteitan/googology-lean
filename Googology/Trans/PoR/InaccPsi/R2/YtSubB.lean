import Googology.Trans.PoR.InaccPsi.R2.YtSubL

/-!
# The sub-bases `a = β + W^{X+e}·γ` (`γ` a limit code) are bases with a law at both ends; their atoms move

`B_n = Bc.bcB S n`, "window", "IH(s)" as in `Yj.yjBaseFacts`, `X = Ω_{k+3}`, `T = Vb.vbT`.

* `ytB_lim` (**`B_n` keeps limits** on a class of `MvD` closed under `log` and the tail);
* `ytDvdE` (**the divisibility move for any code exponent `e₁ < ψ₂(t)`**: `W^{X+e₁} ∣ x ⇒ W^{X+B_n e₁} ∣ B_n x` for every
  `x ∈ D ∩ Cl(t, ψ₂ t)`, `t = β + W^{X+e}`; `Yj.yjDvd` is the case `e₁ = e`, same proof);
* `ytSubGt`, `ytSubD` (`γ < ψ₂(a)`, `a ∈ D`);
* `ytSubBase` (**EVERY SUB-BASE WITH A LIMIT COEFFICIENT IS A BASE WITH A LAW AT BOTH ENDS**: `Yj.YjBase λ λ' A' a
  (1 + ψ₂(T a))` and `B_n a = B_n β + W^{X+B_n e}·B_n γ`, under IH below `ψ₂(a)`);
* `ytSubMove` (**EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃)` ABOVE EVERY SUB-BASE MOVES** under the premise of WallBelow at `s`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

/-- **`B_n` keeps limits** on a class of `MvD` closed under `log` and the tail. -/
theorem ytB_lim {n : ℕ} (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) :
    ∀ x, P x → IsSuccLimit x → IsSuccLimit (Bc.bcB S n x) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hlim
  have hx0 : x ≠ 0 := hlim.ne_bot
  obtain ⟨hPL, hPr⟩ := hPdec x hx hx0
  set L := log ω x with hLdef
  set y := x - ω ^ L with hydef
  have hle : ω ^ L ≤ x := opow_log_le_self ω hx0
  have hxy : x = ω ^ L + y := (Ordinal.add_sub_cancel_of_le hle).symm
  have hDL := hPD _ hPL
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDL
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDo (hPD _ hPr)
  rw [← hxy] at hBx
  rw [hBx, hBo]
  have hxlt : x < ω ^ L * ω := by
    have h := lt_opow_succ_log_self one_lt_omega0 x
    rwa [opow_succ] at h
  have hL0 : L ≠ 0 := by
    intro h0
    have hω : x < ω := by have := hxlt; rwa [h0, opow_zero, one_mul] at this
    exact absurd (omega0_le_of_isSuccLimit hlim) (not_le.2 hω)
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hBL0 : Bc.bcB S n L ≠ 0 := by
    have h := leB_le (n := n) hD1 hDL (Order.one_le_iff_ne_zero.2 hL0)
    rw [mwB_one] at h
    exact (zero_lt_one.trans_le h).ne'
  rcases eq_or_ne y 0 with hy0 | hy0
  · rw [hy0, Bc.bcB_zero, add_zero]; exact isSuccLimit_opow_left isSuccLimit_omega0 hBL0
  · have hylim : IsSuccLimit y := by
      rcases zero_or_succ_or_isSuccLimit y with h | ⟨z, hz⟩ | h
      · exact absurd h hy0
      · exfalso
        rw [hxy, ← hz, Ordinal.add_succ] at hlim
        exact not_isSuccLimit_succ _ hlim
      · exact h
    have hylt : y < x := by
      rcases (Ordinal.sub_le_self x (ω ^ L)).lt_or_eq with h | h
      · exact h
      · exfalso
        have hyx : y = x := h
        have h2 : ω ^ L + x = x := by
          conv_rhs => rw [hxy]
          rw [hyx]
        exact absurd (add_eq_right_iff_mul_omega0_le.1 h2) (not_le.2 hxlt)
    exact isSuccLimit_add _ (IH y hylt hPr hylim)

/-- `γ < ψ₂(β + W^{X+e}·γ)` and `β + W^{X+e}·γ ∈ D` for a sub-base. -/
theorem ytSubGt {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (k : ℕ)
    {e β γ : Ordinal.{0}} (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β)
    (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hγ : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β) :
    γ < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1)) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨hβd, -, -, hβown, hexpA⟩ := hb
  rw [← add_assoc] at hβd hβown
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have hXeC : ∀ x, 1 ≤ x → X + e ∈ S.CSet (β + leWe (X + e) * x) (S.psi (β + leWe (X + e) * x) (Om (1 + 1))) := by
    intro x hx
    refine CSet.add_mem (Vn.vnOmK3_mem k _ _) (CSet.of_lt (hexp.trans_le ?_))
    refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * x := leMulWe_mono hx
  have hEQ : ∀ Q, SC Q → leKe S (X + e) β 1 < Q → VkA (1 + 1) Q (X + e) := by
    intro Q hQ h1
    refine ytXe_vkA k hQ.1 ((hexp.trans_le ?_).trans h1)
    refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
    show leWe (X + e) ≤ leWe (X + e) * Om 1
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * Om 1 := leMulWe_mono (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le
  exact ytTe_gt hβown hXeC hβd hEQ hγ

theorem ytSubD {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (k : ℕ)
    {e β γ : Ordinal.{0}} (hβD : VbD S l β) (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β)
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hγ : GxCl (upsilon l) (ldAtR S l) γ)
    (hγT : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β) :
    VbD S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨-, -, -, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt hκ2 _)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hβ1W : β + leWe (X + e + 1) < Om ω :=
    vkOmW.1.isPrincipal hβD.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal (vkOmW.1.isPrincipal
      (Wv.wvOmK_lt_W k) (heW.trans ldOm2_lt_OmW)) (one_lt_omega0.trans (Lw.lw_omega_lt_SC vkOmW.1)))).1
  have hTθ : leTe S (X + e + 1) β ≤ ConjT.th S := (psi_mono hκ2 hβ1W.le).1
  have heθ : e < ConjT.th S := hexp.trans_le ((psi_mono hκ2 ((add_le_add_iff_left β).2
    (leWe_mono (le_self_add : X + e ≤ X + e + 1)))).1.trans hTθ)
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγW).2 hγ
  have h := (ytT_sub (S := S) hl hX k hβD heH heW heθ hγH hγW (hγT.trans_le hTθ)).1
  rw [add_zero] at h
  have hlt : β + leWe (X + e) * γ < Om ω := by
    refine lt_of_le_of_lt ((add_le_add_iff_left β).2 ?_) hβ1W
    rw [leWe_succ]; exact leMulWe_mono hγW.le
  exact ⟨CSet.add_mem hβD.1 h.1, CSet.add_mem hβD.2.1 h.2.1, hlt⟩

section Win

variable {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hR h1 hr hl' hB

/-- **THE DIVISIBILITY MOVE for every code exponent `e₁ < ψ₂(t)`.** -/
theorem ytDvdE (k : ℕ) {e β e1 : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))
    (he1c : GxCl (upsilon l) (ldAtR S l) e1)
    (he1s : e1 < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) :
    ∀ x, VbD S l x →
      x ∈ S.CSet (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))
        (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) →
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e1) ∣ x →
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e1) ∣ Bc.bcB S n x := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := Yd.ydBaseE_lt k hβD hb
  have he2 : e < Om (1 + 1) := he.trans (psi_lt hκ2 _)
  have hes : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec le_rfl
  -- `B_n W^{X+e} = W^{X+B_n e}`
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (β + leWe (X + e)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  have hX0 : X ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'
  obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB (S := S) k) P hPD hPdec hPW
    ⟨he1c, he1s, he1s.trans (psi_lt hκ2 _)⟩ ⟨he1c, he1s, he1s.trans (psi_lt hκ2 _)⟩
  have hTM := fun x (hx : VbD S l x) (hxC : x ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1)))) =>
    Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH x hx hxC
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxD hxC hdv
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨⟨hLD, hLC⟩, ⟨hrD, hrC⟩⟩ := yjParts hxD hxC
  obtain ⟨hDL, -, -⟩ := hTM _ hLD hLC
  obtain ⟨hDr, -, -⟩ := hTM _ hrD hrC
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * m + x % ω ^ log ω x := by
    rw [← hm]; exact (Ordinal.div_add_mod x _).symm
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDL
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDom hDr
  rw [← hdm] at hBx
  rw [hBx, hBom, hBo]
  -- the exponent bound `Ω₂·(X+e) ≤ L` and its move
  have hWle : ω ^ (Om (1 + 1) * (X + e1)) ≤ x := Ordinal.le_of_dvd hx0 hdv
  have hpL : Om (1 + 1) * (X + e1) ≤ log ω x := (Ordinal.opow_le_iff_le_log one_lt_omega0 hx0).1 hWle
  have hWo : leWe (X + e1) ≤ ω ^ log ω x := opow_le_opow_right omega0_pos hpL
  have hBWo : Bc.bcB S n (leWe (X + e1)) ≤ Bc.bcB S n (ω ^ log ω x) := by
    rcases hWo.lt_or_eq with h | h
    · exact ((mvB_lt_iff hDW hDo).2 h).le
    · rw [h]
  rw [hBW, hBo] at hBWo
  have hp' : Om (1 + 1) * (X + Bc.bcB S n e1) ≤ Bc.bcB S n (log ω x) :=
    (opow_le_opow_iff_right one_lt_omega0).1 hBWo
  refine dvd_add (Dvd.dvd.mul_right (opow_dvd_opow ω hp') _) ?_
  have hrlt : x % ω ^ log ω x < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  refine IHx _ hrlt hrD hrC ?_
  have h2 : leWe (X + e1) ∣ ω ^ log ω x * m := Dvd.dvd.mul_right (opow_dvd_opow ω hpL) _
  rw [hdm] at hdv
  exact (Ordinal.dvd_add_iff h2).1 hdv


end Win

section Win2

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY SUB-BASE WITH A LIMIT COEFFICIENT IS A BASE WITH A LAW AT BOTH ENDS.** -/
theorem ytSubBase (k : ℕ) {e β γ : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β) (hγ : GxCl (upsilon l) (ldAtR S l) γ)
    (hγT : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β) (hlim : IsSuccLimit γ)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ)
        (1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ)) (Om (1 + 1))) ∧
      Bc.bcB S n (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) =
        Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) * Bc.bcB S n γ := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set a := β + leWe (X + e) * γ with hadef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hX0 : X ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hbe : Ro.RoBaseE S l X e β := Ro.roBaseE_mono (lt_add_one e).le hb
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγW).2 hγ
  have hγs : γ < S.psi a (Om (1 + 1)) := ytSubGt hl hX k hb hec hγT
  have hγ0 : γ ≠ 0 := hlim.ne_bot
  have hta : S.psi (β + leWe (X + e)) (Om (1 + 1)) ≤ S.psi a (Om (1 + 1)) := by
    refine (psi_mono hκ2 ((add_le_add_iff_left β).2 ?_)).1
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * γ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hγ0)
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hta)
  obtain ⟨hdv', hD'⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  obtain ⟨hDβ, hDe, hBec, hBe2, hbe', -⟩ := Yd.ydBaseMoveB hR h1 hr hl' hB k hec hβD hbe IHt hdv' hD'
  -- the exponent `e + 1`
  have hes : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hbe.2.2.2.2 e hec le_rfl
  have he1s : e + 1 < S.psi (β + leWe (X + e)) (Om (1 + 1)) := (SC_psi hκ2 _).isSuccLimit.succ_lt hes
  have heW : e < Om (1 + 1) := hes.trans (psi_lt hκ2 _)
  have he1W : e + 1 < Om (1 + 1) := he1s.trans (psi_lt hκ2 _)
  have he1c : GxCl (upsilon l) (ldAtR S l) (e + 1) :=
    (ldHull_iff hl hX he1W).1 (CSet.succ_mem ((ldHull_iff hl hX heW).2 hec))
  have hβC : β ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) := hbe.2.2.2.1 _ le_rfl
  have hdv1 := ytDvdE hR h1 hr hl' hB k hec hβD hbe IHt he1c he1s β hβD hβC hb.1
  obtain ⟨hDe1, hBe1⟩ := mvB_add (k := n) hDe hD1
  rw [mwB_one] at hBe1
  rw [hBe1] at hdv1
  have hΩW : ∀ y : Ordinal.{0}, 1 ≤ y → Om (1 + 1) ≤ leWe y := fun y hy => by
    rw [← leWe_one]; exact leWe_mono hy
  have hXB1 : (1 : Ordinal.{0}) ≤ X + Bc.bcB S n e :=
    (one_lt_omega0.trans (Lw.lw_omega_lt_SC (SC_Om (add_pos_of_right zero_lt_one _).ne'))).le.trans le_self_add
  have hb1' : Ro.RoBaseE S l' X (Bc.bcB S n e + 1) (Bc.bcB S n β) := by
    obtain ⟨-, hH', -, hown', hexp'⟩ := hbe'
    refine ⟨hdv1, hH', ?_, fun d _ => ytOwnAll (fun d hd => hown' d (hd.trans (hΩW _ hXB1))) d,
      fun e'' he'' h' => ?_⟩
    · have hgW : X + (Bc.bcB S n e + 1) < Om ω :=
        vkOmW.1.isPrincipal (Wv.wvOmK_lt_W k) ((ldOm2_SC.isSuccLimit.succ_lt hBe2).trans ldOm2_lt_OmW)
      exact (vkOmW.1.isPrincipal hD'.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1).trans_le (ConjT.OmW_le_A S _)
    · rcases h'.lt_or_eq with h | h
      · exact hexp' e'' he'' (Order.lt_add_one_iff.1 h)
      · subst h
        have h0 := hexp' (Bc.bcB S n e) hBec le_rfl
        refine ((SC_psi hκ2 _).isSuccLimit.succ_lt h0).trans_le ?_
        exact (psi_mono hκ2 ((add_le_add_iff_left _).2 (leWe_mono ((add_le_add_iff_left X).2 le_self_add)))).1
  -- the class of the codes below `ψ₂(a)`
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi a (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  obtain ⟨-, -, hDWγ, hBWγ⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB k) P hPD hPdec hPW
    ⟨hec, hes.trans_le hta, heW⟩ ⟨hγ, hγs, hγW⟩
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDWγ
  rw [hBWγ] at hBa
  obtain ⟨hDγ, hBγc, -, -, -⟩ := IH γ hγ hγs
  have hBlim : IsSuccLimit (Bc.bcB S n γ) := ytB_lim P hPD hPdec γ ⟨hγ, hγs, hγW⟩ hlim
  -- `B_n γ < T_{X+B_n e+1}(B_n β)`
  obtain ⟨hDW1, hBW1, -, -⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB k) P hPD hPdec hPW
    ⟨he1c, he1s.trans_le hta, he1W⟩ ⟨hγ, hγs, hγW⟩
  rw [hBe1] at hBW1
  obtain ⟨hDβW, hBβW⟩ := mvB_add (k := n) hDβ hDW1
  have hTown : β + leWe (X + (e + 1)) ∈ S.CSet (β + leWe (X + (e + 1)))
      (S.psi (β + leWe (X + (e + 1))) (Om (1 + 1))) :=
    CSet.add_mem (hb.2.2.2.1 _ le_rfl) (leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _)
      (CSet.of_lt (hb.2.2.2.2 (e + 1) he1c le_rfl))))
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDβW hTown
  have hBγT : Bc.bcB S n γ < leTe S (X + Bc.bcB S n e + 1) (Bc.bcB S n β) := by
    have hγT' : γ < S.psi (β + leWe (X + (e + 1))) (Om (1 + 1)) := by
      have h := hγT; unfold leTe at h; rwa [add_assoc] at h
    have h := (mvB_lt_iff (k := n) hDγ hDT).2 hγT'
    rw [hBT, hBβW, hBW1] at h
    unfold leTe
    rw [show X + Bc.bcB S n e + 1 = X + (Bc.bcB S n e + 1) from add_assoc _ _ _]
    exact h
  have hBγW : Bc.bcB S n γ < Om (1 + 1) := hBγT.trans (leTe_lt_Om2 _ _)
  have hBγH : Bc.bcB S n γ ∈ cdHull S l' := (ldHull_iff hl' hX' hBγW).2 hBγc
  -- the `λ` side
  have hDaD : VbD S l a := ytSubD hl hX k hβD hb hec hγ hγT
  have hbs := ytBaseSub hl hX k hb hec hγH hγT
  have htn : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hbs.2.2.2.1 0 zero_le; rwa [add_zero] at h
  obtain ⟨-, hDT', hTmv⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH a hDaD htn
  have hlaw := ytSubLaw hl hX hown hρA k hec hβD hb hγ hγT hlim
  have hhi : S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l a) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← hlaw]; exact yjTh_hi hR h1 hr hl' hB (yjPsi2_leW hDaD.2.2)
  obtain ⟨hDψ, hBψ, -⟩ := Xq.xqSigMove hl hX hown hρA hA' hρ' h1.le hB hDaD htn hDT' hhi
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hD1 hDψ
  rw [mwB_one, hBψ] at hBD
  have hat := Xq.xqOwn hl hX hown hρA hDaD htn
  -- the `λ'` side
  have hDa' : VbD S l' (Bc.bcB S n β + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ) :=
    ytSubD hl' hX' k hD' hb1' hBec hBγc hBγT
  have hbs' := ytBaseSub hl' hX' k hb1' hBec hBγH hBγT
  have htn' : Bc.bcB S n β + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ ∈
      S.CSet (Bc.bcB S n β + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ)
        (S.psi (Bc.bcB S n β + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ) (Om (1 + 1))) := by
    have h := hbs'.2.2.2.1 0 zero_le; rwa [add_zero] at h
  have hlaw' := ytSubLaw hl' hX' hA' hρ' k hBec hD' hb1' hBγc hBγT hBlim
  have hat' := Xq.xqOwn hl' hX' hA' hρ' hDa' htn'
  rw [← hBa, hTmv] at hlaw' hat'
  have hXe1 : (1 : Ordinal.{0}) ≤ X + e :=
    (one_lt_omega0.trans (Lw.lw_omega_lt_SC (SC_Om (add_pos_of_right zero_lt_one _).ne'))).le.trans le_self_add
  have hdva : Om (1 + 1) ∣ a := by
    exact (leWe_one ▸ leWe_dvd hXe1).trans hbs.1
  have hdva' : Om (1 + 1) ∣ Bc.bcB S n β + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ := by
    exact (leWe_one ▸ leWe_dvd hXB1).trans hbs'.1
  refine ⟨⟨hDaD, hdva, fun d hd => hbs.2.2.2.1 d (hd.trans (hΩW _ hXe1)),
    hDa, hDD, by rw [← add_assoc]; exact hat, by rw [← add_assoc]; exact hlaw,
    hBa ▸ hDa', hBa ▸ hdva', ?_, by rw [hBD, ← add_assoc]; exact hat', by rw [hBD, ← add_assoc]; exact hlaw'⟩, hBa⟩
  intro d hd
  rw [hBa]
  exact hbs'.2.2.2.1 d (hd.trans (hΩW _ hXB1))

/-- **EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃)` ABOVE EVERY SUB-BASE `a = β + W^{X+e}·γ` (`γ` a limit code) MOVES** under the
premise of WallBelow at `s`. -/
theorem ytSubMove (k : ℕ) {e β γ : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β) (hγ : GxCl (upsilon l) (ldAtR S l) γ)
    (hγT : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β) (hlim : IsSuccLimit γ)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1)) ≤ s)
    (hsY : s < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ + ugY S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨hba, hBa⟩ := ytSubBase hR h1 hr hl' hB hA' hρ' k hec hβD hb hγ hγT hlim
    fun x hx hxs => IH x hx (hxs.trans_le hsa)
  have hbe : Ro.RoBaseE S l X e β := Ro.roBaseE_mono (lt_add_one e).le hb
  have hta : S.psi (β + leWe (X + e)) (Om (1 + 1)) ≤ s := by
    refine le_trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1 hsa
    calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
      _ ≤ leWe (X + e) * γ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hlim.ne_bot)
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hta)
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hd : ugY S ∣ β + leWe (X + e) * γ :=
    dvd_add ((ytY_dvd_We k e).trans hbe.1) ((ytY_dvd_We k e).trans (dvd_mul_right _ _))
  have hd' : ugY S ∣ Bc.bcB S n (β + leWe (X + e) * γ) := by
    rw [hBa]
    exact dvd_add ((ytY_dvd_We k _).trans hdv') ((ytY_dvd_We k _).trans (dvd_mul_right _ _))
  exact ytUxMove hR h1 hr hl' hB hA' hρ' hba hd hd' hs hsa hsY IH

end Win2

end Googology.Trans.PoR.InaccPsi.R2.Yt
