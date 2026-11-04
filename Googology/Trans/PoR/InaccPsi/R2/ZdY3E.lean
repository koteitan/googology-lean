import Googology.Trans.PoR.InaccPsi.R2.ZdPlatR
import Googology.Trans.PoR.InaccPsi.R2.YyY3G

/-!
# THE SUB-BASES `a + W^{Y₃+e}·γ` OF THE SHIFT `Y₃` AT EVERY CODE EXPONENT `e`

`Y₃ = ugY S = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `W^x = leWe x`, `Ω^x = leOe x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `B_n`,
"window", `A'`, `Yj.YjBase`, "IH(s)" as in `Yy.yyBaseY3G`, `E^a = ψ₂(a + W^{Y₃+Ω₂})`.  `Yy.yyBaseY3G` is the exponent
`e = 0`; here `e` is any code with `e + 1 < E^a` (the own clause of the exponent `e + 1`; above `E^a` there is no
atom: `Yd.ydTopFailB`).  The own clause at `λ'` comes from the plateau `Zd.zdOwnBr_iff` (membership of `Y₃` only in
the closures above `Ω₃`) and its move `zdOwnMoveBr`:

* `zdOm2_mulY`, `zdShB_Y3` (`B_n` fixes `Ω₂·Y₃ = Y₃` and `Ω₁·Y₂ = Y₂`), `zdY3r` (`Y₃ ∈ Cl(a, b)` for `a > β ≥ Ω₃`),
* `zdFixBr`, `zdOwnMoveBr` (**THE OWN CLAUSE MOVES** for a shift in the closures above the base),
* `zdWdvd3` (`W^{Y₃+x} ∣ a` for `x ≤ Ω₂` when `Ω₃ ∣ a`),
* `zdBaseY3E` (**`a + W^{Y₃+e}·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every code `e` with `e + 1 < E^a` and every
  code `0 < γ < ψ₂(a + W^{Y₃+e+1})`, image `D + Ω^{Y₂+Θe}·Θγ`, `B_n(a + W^{Y₃+e}·γ) = B_n a + W^{Y₃+B_n e}·B_n γ`,
  given `Yj.YjBase λ λ' A' a D`, `W^{Y₃+e+1} ∣ a`, `W^{Y₃+B_n e+1} ∣ B_n a`, `Ω₃ ≤ a` and IH below
  `ψ₂(a + W^{Y₃+e}·γ)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Yd

variable {S : InaccSeq.{0}}

theorem zdOm2_mulY : Om (1 + 1 : Ordinal.{0}) * ugY S = ugY S := by
  have hE := gg_SC_eps (uqY_SC (S := S))
  have hA : Om (1 + 1) + ugY S = ugY S := Ordinal.add_absorp (by rw [hE]; exact uqW_lt_Y) hE.le
  calc Om (1 + 1) * ugY S = ω ^ Om (1 + 1) * ω ^ ugY S := by rw [gg_SC_eps ldOm2_SC, hE]
    _ = ω ^ (Om (1 + 1) + ugY S) := (opow_add _ _ _).symm
    _ = ugY S := by rw [hA, hE]

theorem zdOm1_mulY2 : Om (1 : Ordinal.{0}) * S.psi (Om (1 + 1)) (Om (1 + 1)) = S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  have h1 : Om (1 : Ordinal.{0}) < S.psi (Om (1 + 1)) (Om (1 + 1)) := (psiS_bounds (S := S) _ 1).1
  have hE := gg_SC_eps (Vq.vqY2_SC (S := S))
  have hA : Om 1 + S.psi (Om (1 + 1)) (Om (1 + 1)) = S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    Ordinal.add_absorp (by rw [hE]; exact h1) hE.le
  calc Om 1 * S.psi (Om (1 + 1)) (Om (1 + 1)) = ω ^ Om 1 * ω ^ S.psi (Om (1 + 1)) (Om (1 + 1)) := by
        rw [gg_SC_eps Ph.ph_SC_Om1, hE]
    _ = ω ^ (Om 1 + S.psi (Om (1 + 1)) (Om (1 + 1))) := (opow_add _ _ _).symm
    _ = S.psi (Om (1 + 1)) (Om (1 + 1)) := by rw [hA, hE]

/-- **`B_n` fixes `Ω₂·Y₃ = Y₃` and `Ω₁·Y₂ = Y₂`**: the shift data of `(Y₃, Y₂)` for `Ro.roB_We`, `Ro.roB_Oe`. -/
theorem zdShB_Y3 : Ro.RoShB S (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))) := by
  refine ⟨Vq.vqY2_SC.1.ne', fun n => ?_⟩
  obtain ⟨hDY, hBY⟩ := Yy.yyY3_D (S := S) (n := n)
  obtain ⟨hDY2, hBY2⟩ := Yy.yyY2_D (S := S) (n := n)
  rw [zdOm2_mulY, zdOm1_mulY2]
  exact ⟨hDY, hBY, hDY2, hBY2⟩

theorem zdY3r {β : Ordinal.{0}} (hβ3 : Om (1 + 1 + 1) ≤ β) : ∀ a b : Ordinal.{0}, β < a → ugY S ∈ S.CSet a b :=
  fun _ _ h => Vq.vqY3_mem (hβ3.trans_lt h)

/-- **`W^{Y₃+x} ∣ a`** for every `x ≤ Ω₂` when `Ω₃ ∣ a`. -/
theorem zdWdvd3 {a x : Ordinal.{0}} (hd : Om (1 + 1 + 1) ∣ a) (hx : x ≤ Om (1 + 1)) : leWe (ugY S + x) ∣ a := by
  have h3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_right zero_lt_one _).ne'
  have hle : ugY S + x ≤ Om (1 + 1 + 1) :=
    (h3.isPrincipal ugY_lt_Om3 (hx.trans_lt (Om_lt_Om.2 (lt_add_one _)))).le
  have h := leWe_dvd hle
  rw [Vn.vnWe_Om3] at h
  exact h.trans hd

section Data

variable {X Xh : Ordinal.{0}} (hX0 : X ≠ 0) (hShB : Ro.RoShB S X Xh)
include hX0 hShB

/-- **`B_n e^β_m = e^{B_n β}_m`** for a shift `X` in the closures above `β` (`β` normal in the domain). -/
theorem zdFixBr (n : ℕ) {β : Ordinal.{0}} (hXr : ∀ a b : Ordinal.{0}, β < a → X ∈ S.CSet a b)
    (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) :
    ∀ m, MvD S (ydEB S X β m) ∧ Bc.bcB S n (ydEB S X β m) = ydEB S X (Bc.bcB S n β) m
  | 0 => by
    rw [ydEB_zero, ydEB_zero]
    have hc : (0 : Ordinal.{0}) < Bc.bcC S n := (Lw.lw_L_SC S _).1
    exact ⟨mvD_of_lt (Lw.lw_L_SC S ω).1, Bc.bcB_fix' S n 0 hc⟩
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨hDm, hBm⟩ := zdFixBr n hXr hDβ hβ m
    set P : Ordinal.{0} → Prop := fun x => x = 0 ∨ (x = ydEB S X β m ∧ SC x) with hP
    have hPD : ∀ x, P x → MvD S x := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact mvD_of_lt (Lw.lw_L_SC S ω).1
      · exact hDm
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := by
      rintro x (rfl | ⟨hx, hxS⟩) hx0
      · exact absurd rfl hx0
      · have hl : log ω x = x := by
          conv_lhs => rw [← gg_SC_eps hxS]
          exact log_opow one_lt_omega0 x
        rw [hl, gg_SC_eps hxS, Ordinal.sub_self]
        exact ⟨Or.inr ⟨hx, hxS⟩, Or.inl rfl⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := by
      rintro x (rfl | ⟨rfl, -⟩)
      · exact ldOm2_SC.1
      · exact ydEB_lt_Om2 X β m
    have hPm : P (ydEB S X β m) := by
      cases m with
      | zero => exact Or.inl rfl
      | succ j => exact Or.inr ⟨rfl, ydEB_SC X β j⟩
    obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 hShB P hPD hPdec hPW hPm hPm
    rw [hBm] at hBW
    obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDβ hDW
    rw [hBW] at hBa
    have hown : β + leWe (X + ydEB S X β m) ∈ S.CSet (β + leWe (X + ydEB S X β m))
        (S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))) := by
      refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβ)
        (leWe_mem (CSet.add_mem (hXr _ _ (lt_add_of_pos_right β (leWe_pos _))) (CSet.of_lt ?_)))
      rw [← ydEB_succ]; exact zdEBr_lt_succ hXr hβ m
    obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa hown
    rw [hBa] at hBs
    rw [ydEB_succ, ydEB_succ]
    exact ⟨hDs, hBs⟩

/-- **THE OWN CLAUSE MOVES** for a shift `X` in the closures above `β` and above `B_n β`. -/
theorem zdOwnMoveBr (n : ℕ) {β e : Ordinal.{0}} (hXr : ∀ a b : Ordinal.{0}, β < a → X ∈ S.CSet a b)
    (hXr' : ∀ a b : Ordinal.{0}, Bc.bcB S n β < a → X ∈ S.CSet a b)
    (hDβ : MvD S β) (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hDe : MvD S e)
    (he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :
    Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (X + Om (1 + 1))) (Om (1 + 1)) ∧
      ∀ e'', e'' ≤ Bc.bcB S n e → e'' < S.psi (Bc.bcB S n β + leWe (X + e'')) (Om (1 + 1)) := by
  obtain ⟨m, hm⟩ := zdLtTopBr hXr hβ he
  obtain ⟨hDm, hBm⟩ := zdFixBr hX0 hShB n hXr hDβ hβ m
  have h := (mvB_lt_iff (k := n) hDe hDm).2 hm
  rw [hBm] at h
  have hB' : Bc.bcB S n e < S.psi (Bc.bcB S n β + leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
    h.trans_le (ydEB_le_top _ _ m)
  exact ⟨hB', (zdOwnBr_iff hXr' (ydNormB n hDβ hβ) _).2 hB'⟩

end Data

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

set_option maxHeartbeats 1000000 in
/-- **`a + W^{Y₃+e}·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every code `e` with `e + 1 < E^a` and every code
`0 < γ < ψ₂(a + W^{Y₃+e+1})`. -/
theorem zdBaseY3E {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (ha3 : Om (1 + 1 + 1) ≤ a)
    {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hdv : leWe (ugY S + (e + 1)) ∣ a)
    (hdv' : leWe (ugY S + (Bc.bcB S n e + 1)) ∣ Bc.bcB S n a)
    (heE : e + 1 < S.psi (a + leWe (ugY S + Om (1 + 1))) (Om (1 + 1))) {γ : Ordinal.{0}}
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγ0 : γ ≠ 0) (hγT : γ < leTe S (ugY S + e + 1) a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + leWe (ugY S + e) * γ) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (a + leWe (ugY S + e) * γ)
        (D + leOe (S.psi (Om (1 + 1)) (Om (1 + 1)) + gxTh (upsilon l) (ldAtR S l) e) *
          gxTh (upsilon l) (ldAtR S l) γ) ∧
      Bc.bcB S n (a + leWe (ugY S + e) * γ) = Bc.bcB S n a + leWe (ugY S + Bc.bcB S n e) * Bc.bcB S n γ := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨hρSC', -⟩ := leRho hl' hX'
  set Y := ugY S with hYdef
  set Y2 := S.psi (Om (1 + 1)) (Om (1 + 1)) with hY2def
  have hY0 : Y ≠ 0 := uqY_SC.1.ne'
  have ha3' : Om (1 + 1 + 1) ≤ Bc.bcB S n a := Yy.yyB_ge3 hb.mv_a ha3
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have han' : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a) (S.psi (Bc.bcB S n a) (Om (1 + 1))) := by
    have h := hb.own' 0 zero_le; rwa [add_zero] at h
  have hYW : Y < Om ω := ugY_lt_Om3.trans Ry.ryOm3_lt
  have hY3H : ∀ {l0 : Ordinal.{0}}, Y ∈ cdHull S l0 := fun {l0} =>
    Vq.vqY3_mem (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))
  have hXr := zdY3r (S := S) ha3
  have hXr' := zdY3r (S := S) ha3'
  -- the exponent `e`
  have he1E : ∀ e', e' ≤ e + 1 → e' < S.psi (a + leWe (Y + e')) (Om (1 + 1)) := (zdOwnBr_iff hXr han _).2 heE
  have hes : e < S.psi (a + leWe (Y + e)) (Om (1 + 1)) := he1E e le_self_add
  have he2 : e < Om (1 + 1) := hes.trans (psi_lt hκ2 _)
  have he12 : e + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt he2
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX he2).2 hec
  have he1c : GxCl (upsilon l) (ldAtR S l) (e + 1) := (ldHull_iff hl hX he12).1 (CSet.succ_mem heH)
  have hγ1 : (1 : Ordinal.{0}) ≤ γ := Order.one_le_iff_ne_zero.2 hγ0
  have hWle : leWe (Y + e) ≤ leWe (Y + e) * γ := Ordinal.le_mul_left _ (zero_lt_one.trans_le hγ1)
  have hsle : S.psi (a + leWe (Y + e)) (Om (1 + 1)) ≤ S.psi (a + leWe (Y + e) * γ) (Om (1 + 1)) :=
    (psi_mono hκ2 ((add_le_add_iff_left a).2 hWle)).1
  have hes' : e < S.psi (a + leWe (Y + e) * γ) (Om (1 + 1)) := hes.trans_le hsle
  have he1s' : e + 1 < S.psi (a + leWe (Y + e) * γ) (Om (1 + 1)) := (SC_psi hκ2 _).isSuccLimit.add_one_lt hes'
  -- the base of exponent `e + 1` at `λ`
  have hbE : Ro.RoBaseE S l Y (e + 1) a := by
    refine ⟨hdv, hb.D_a.1, ?_, fun d _ => (psi_mono hκ2 le_self_add).2 han, fun e' _ h => he1E e' h⟩
    exact (vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2
      (vkOmW.1.isPrincipal hYW (he12.trans ldOm2_lt_OmW))).1).trans_le (ConjT.OmW_le_A S _)
  have hs := Vq.vqSh_Y3_rst hl hX hown hρA (le_refl (Om (1 + 1 + 1)))
  have hT := Vq.vqTopY3E hl hX hown hρA (le_refl (Om (1 + 1 + 1))) e hec he2
  have hst := Vq.vqStepA hs hl hX hown hρA hec hT hbE ha3 hb.hat hb.law
  -- `γ`
  have hγ2 : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγ
  obtain ⟨hEC, hEL⟩ := Vq.vqE_data hs ha3 hes
  have hγs : γ < S.psi (a + leWe (Y + e) * γ) (Om (1 + 1)) :=
    vkTe_gt (fun d _ => (psi_mono hκ2 le_self_add).2 han) hEC (by rw [add_assoc]; exact hdv) hEL hγT
  obtain ⟨hDγ, hBγc, -, hΘγX, hΘγ⟩ := IH γ hγ hγs
  obtain ⟨hDe, hBec, hBeP, hΘeX, hΘe⟩ := IH e hec hes'
  obtain ⟨hDe1, hBe1c, -, -, -⟩ := IH (e + 1) he1c he1s'
  have hBe2 : Bc.bcB S n e < Om (1 + 1) := hBeP.trans Lj.ljThP_lt_Om2
  -- `B_n(W^{Y₃+e}·γ) = W^{Y₃+B_n e}·B_n γ`, `B_n(W^{Y₃+(e+1)}) = W^{Y₃+(B_n e+1)}`
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (a + leWe (Y + e) * γ) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  obtain ⟨hDW, -, hDWγ, hBWγ⟩ := Ro.roB_We (n := n) hY0 zdShB_Y3 P hPD hPdec hPW
    ⟨hec, hes', he2⟩ ⟨hγ, hγs, hγ2⟩
  obtain ⟨hDW1, hBW1, -, -⟩ := Ro.roB_We (n := n) hY0 zdShB_Y3 P hPD hPdec hPW
    ⟨he1c, he1s', he12⟩ ⟨he1c, he1s', he12⟩
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hBe1 : Bc.bcB S n (e + 1) = Bc.bcB S n e + 1 := by
    obtain ⟨-, h⟩ := mvB_add (k := n) hDe (mvD_of_lt h1L); rw [h, hB1]
  rw [hBe1] at hBW1
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hb.mv_a hDWγ
  rw [hBWγ] at hBa
  -- the readings at `λ`
  obtain ⟨hlaw, hat⟩ := hst γ hγ hγT
  set Θe := gxTh (upsilon l) (ldAtR S l) e with hΘedef
  set Θγ := gxTh (upsilon l) (ldAtR S l) γ with hΘγdef
  have hΘes : Θe < S.psi (ConjT.Aη S (cdEta S l) + D + leOe (Y2 + Θe) * Θγ) (Om 1) := by
    rw [← hlaw]; exact gxTh_lt hec hes'
  have hΘγs : Θγ < S.psi (ConjT.Aη S (cdEta S l) + D + leOe (Y2 + Θe) * Θγ) (Om 1) := by
    rw [← hlaw]; exact gxTh_lt hγ hγs
  have hΘe1 : Θe < Om 1 := hΘes.trans (psi_lt Low.InR_Om_one _)
  have hΘγ1 : Θγ < Om 1 := hΘγs.trans (psi_lt Low.InR_Om_one _)
  -- `B_n(D + Ω^{Y₂+Θe}·Θγ)`
  obtain ⟨hDO, hBO⟩ := Ro.roB_Oe (n := n) zdShB_Y3 hΘe1 hΘeX hΘγ1 hΘγX
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hb.mv_D hDO
  rw [hBO, ← hΘe, ← hΘγ] at hBD
  -- the base of exponent `B_n e + 1` at `λ'`
  obtain ⟨-, hown'⟩ := zdOwnMoveBr hY0 zdShB_Y3 n hXr hXr' hb.mv_a han hDe1 heE
  rw [hBe1] at hown'
  have hBe12 : Bc.bcB S n e + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hBe2
  have hbE' : Ro.RoBaseE S l' Y (Bc.bcB S n e + 1) (Bc.bcB S n a) := by
    refine ⟨hdv', hb.D_a'.1, ?_, fun d _ => (psi_mono hκ2 le_self_add).2 han',
      fun e' _ h => hown' e' h⟩
    exact (vkOmW.1.isPrincipal hb.D_a'.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2
      (vkOmW.1.isPrincipal hYW (hBe12.trans ldOm2_lt_OmW))).1).trans_le (ConjT.OmW_le_A S _)
  have hs' := Vq.vqSh_Y3_rst hl' hX' hA' hρ' (le_refl (Om (1 + 1 + 1)))
  have hT' := Vq.vqTopY3E hl' hX' hA' hρ' (le_refl (Om (1 + 1 + 1))) (Bc.bcB S n e) hBec hBe2
  have hst' := Vq.vqStepA hs' hl' hX' hA' hρ' hBec hT' hbE' ha3' hb.hat' hb.law'
  -- `B_n γ < ψ₂(B_n a + W^{Y₃+B_n e+1})`
  have hTmem : a + leWe (Y + (e + 1)) ∈ S.CSet (a + leWe (Y + (e + 1))) (S.psi (a + leWe (Y + (e + 1))) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 han)
      (leWe_mem (CSet.add_mem (Vq.vqY3_mem (ha3.trans_lt (lt_add_of_pos_right _ (leWe_pos _))))
        (CSet.of_lt (he1E (e + 1) le_rfl))))
  obtain ⟨hDaW, hBaW⟩ := mvB_add (k := n) hb.mv_a hDW1
  rw [hBW1] at hBaW
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTmem
  rw [hBaW] at hBT
  have hγT' : γ < S.psi (a + leWe (Y + (e + 1))) (Om (1 + 1)) := by
    have h := hγT; unfold leTe at h; rwa [add_assoc] at h
  have hBγT : Bc.bcB S n γ < leTe S (Y + Bc.bcB S n e + 1) (Bc.bcB S n a) := by
    have h := (mvB_lt_iff (k := n) hDγ hDT).2 hγT'
    rw [hBT] at h
    unfold leTe; rwa [add_assoc]
  obtain ⟨hlaw', hat'⟩ := hst' _ hBγc hBγT
  have hBes : Bc.bcB S n e < S.psi (Bc.bcB S n a + leWe (Y + Bc.bcB S n e)) (Om (1 + 1)) :=
    hown' _ le_self_add
  obtain ⟨hEC', hEL'⟩ := Vq.vqE_data hs' ha3' hBes
  have hBγs : Bc.bcB S n γ < S.psi (Bc.bcB S n a + leWe (Y + Bc.bcB S n e) * Bc.bcB S n γ) (Om (1 + 1)) :=
    vkTe_gt (fun d _ => (psi_mono hκ2 le_self_add).2 han') hEC' (by rw [add_assoc]; exact hdv') hEL' hBγT
  have hBγ2 : Bc.bcB S n γ < Om (1 + 1) := hBγT.trans (leTe_lt_Om2 _ _)
  have hBγH : Bc.bcB S n γ ∈ cdHull S l' := (ldHull_iff hl' hX' hBγ2).2 hBγc
  have hBeH : Bc.bcB S n e ∈ cdHull S l' := (ldHull_iff hl' hX' hBe2).2 hBec
  -- bounds and memberships
  have hWγW : ∀ {x g : Ordinal.{0}}, x < Om (1 + 1) → g < Om (1 + 1) → leWe (Y + x) * g < Om ω := by
    intro x g hx hg
    have hx1 : x + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hx
    refine lt_of_le_of_lt ?_ (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal hYW (hx1.trans ldOm2_lt_OmW))).1
    show leWe (Y + x) * g ≤ leWe (Y + (x + 1))
    rw [← add_assoc, leWe_succ]; exact leMulWe_mono hg.le
  have hθ : ∀ {x c : Ordinal.{0}}, x < Om ω → c < S.psi x (Om (1 + 1)) → c < ConjT.th S := fun {x c} hx hc =>
    hc.trans_le (psi_mono hκ2 hx.le).1
  have hW2 : ∀ x, Om (1 + 1) ∣ leWe (Y + x) := fun x => by
    have h := leWe_dvd ((gg_one_lt_of_SC uqY_SC).le.trans (le_self_add : Y ≤ Y + x)); rwa [leWe_one] at h
  have hownG : ∀ {b0 x g : Ordinal.{0}}, Om (1 + 1 + 1) ≤ b0 → b0 ∈ S.CSet b0 (S.psi b0 (Om (1 + 1))) →
      x < S.psi (b0 + leWe (Y + x)) (Om (1 + 1)) → g ≠ 0 → g < S.psi (b0 + leWe (Y + x) * g) (Om (1 + 1)) →
      ∀ d, d ≤ Om (1 + 1) → b0 + leWe (Y + x) * g ∈
        S.CSet (b0 + leWe (Y + x) * g + d) (S.psi (b0 + leWe (Y + x) * g + d) (Om (1 + 1))) := by
    intro b0 x g hb0 hb0n hx hg0 hg d _
    have hle1 : b0 + leWe (Y + x) ≤ b0 + leWe (Y + x) * g + d :=
      ((add_le_add_iff_left b0).2 (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hg0))).trans le_self_add
    have hle2 : b0 + leWe (Y + x) * g ≤ b0 + leWe (Y + x) * g + d := le_self_add
    refine CSet.add_mem ((psi_mono hκ2 (le_self_add.trans hle2)).2 hb0n) (leMulWe_mem (CSet.add_mem ?_ ?_) ?_)
    · exact Vq.vqY3_mem (hb0.trans_lt ((lt_add_of_pos_right _ (leWe_pos _)).trans_le hle1))
    · exact CSet.of_lt (hx.trans_le (psi_mono hκ2 hle1).1)
    · exact CSet.of_lt (hg.trans_le (psi_mono hκ2 hle2).1)
  have haγW : a + leWe (Y + e) * γ < Om ω := vkOmW.1.isPrincipal hb.D_a.2.2 (hWγW he2 hγ2)
  have haγW' : Bc.bcB S n a + leWe (Y + Bc.bcB S n e) * Bc.bcB S n γ < Om ω :=
    vkOmW.1.isPrincipal hb.D_a'.2.2 (hWγW hBe2 hBγ2)
  have hBγ0 : Bc.bcB S n γ ≠ 0 := by
    intro h0
    have h := (mvB_lt_iff (k := n) (mvD_of_lt (Lw.lw_L_SC S ω).1) hDγ).2 (pos_iff_ne_zero.2 hγ0)
    rw [Bc.bcB_zero, h0] at h
    exact lt_irrefl _ h
  refine ⟨⟨⟨CSet.add_mem hb.D_a.1 (leMulWe_mem (CSet.add_mem hY3H heH) hγH),
      CSet.add_mem hb.D_a.2.1 (leMulWe_mem (CSet.add_mem (Vq.vqY3_mem Ry.ryOm3_lt) (CSet.of_lt (hθ haγW hes')))
        (CSet.of_lt (hθ haγW hγs))), haγW⟩,
    dvd_add hb.dvd (Dvd.dvd.mul_right (hW2 e) _), hownG ha3 han hes hγ0 hγs, hDa, hDD,
    by rw [← add_assoc]; exact hat, by rw [← add_assoc]; exact hlaw, ?_, ?_, ?_, ?_, ?_⟩, hBa⟩
  · rw [hBa]
    exact ⟨CSet.add_mem hb.D_a'.1 (leMulWe_mem (CSet.add_mem hY3H hBeH) hBγH),
      CSet.add_mem hb.D_a'.2.1 (leMulWe_mem (CSet.add_mem (Vq.vqY3_mem Ry.ryOm3_lt)
        (CSet.of_lt (hθ haγW' (hBes.trans_le (psi_mono hκ2 ((add_le_add_iff_left _).2
          (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hBγ0)))).1)))) (CSet.of_lt (hθ haγW' hBγs))), haγW'⟩
  · rw [hBa]; exact dvd_add hb.dvd' (Dvd.dvd.mul_right (hW2 _) _)
  · rw [hBa]; exact hownG ha3' han' hBes hBγ0 hBγs
  · rw [hBD, ← add_assoc]; exact hat'
  · rw [hBa, hBD, ← add_assoc]; exact hlaw'

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zd
