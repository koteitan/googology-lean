import Googology.Trans.PoR.InaccPsi.R2.YyY3
import Googology.Trans.PoR.InaccPsi.R2.VqSucc

/-!
# The ψ₃-offsets below `W^{Y₃+1} = Y₃·Ω₂`: the bases `a + Y₃·γ` and every atom of `[ψ₂(a), ψ₂(a + W^{Y₃+1}))`

`Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `W^x = leWe x`, `T^a = ψ₂(a + W^{Y₃+1})` (`leTe S (Y₃ + 1) a`), `B_n`,
"window", `A'`, `Yj.YjBase`, "IH(s)" as in `Yy.yyY3Move`.  This is `Yt.ytBaseG` / `Yt.ytAtMove` one level up: the
coefficient `Ω₂·γ` becomes `Y₃·γ`, the image `Ω₁·Θγ` becomes `Y₂·Θγ`; the readings at `λ` and `λ'` come from the
base-relative shift `(Y₃, Y₂)` (`Vq.vqSh_Y3_rst`, `Vq.vqTopY3`, `Vq.vqStepA`).

* `yyWY1_D` (`B_n` fixes `W^{Y₃+1}`), `yyT_le` (**`γ ≥ T^a ⇒ T^a ≤ ψ₂(a + Y₃·γ)`**);
* `yyBaseY3G` (**`a + Y₃·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every code `γ < T^a`, image `D + Y₂·Θγ`,
  `B_n(a + Y₃·γ) = B_n a + Y₃·B_n γ`, given `Yj.YjBase λ λ' A' a D`, `a ≥ Ω₃`, `W^{Y₃+1} ∣ a`, `W^{Y₃+1} ∣ B_n a`
  and IH below `ψ₂(a + Y₃·γ)`);
* `yyY3MoveW` (**EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+1})` MOVES** under IH(s): the offsets `δ < Y₃·Ω₂`);
* `yyTopMoveY3W` (**the same above every top atom `t = β + W^{Ω_{k+3}+e}`**; supersedes `Yy.yyTopMoveY3`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

theorem yyWY1_eq : leWe (ugY S + 1) = ω ^ (ugY S + Om (1 + 1)) := by
  rw [leWe_succ, Vq.vqWeY3, opow_add, gg_SC_eps uqY_SC, gg_SC_eps ldOm2_SC]

/-- `B_n` fixes `W^{Y₃+1}`. -/
theorem yyWY1_D {n : ℕ} : MvD S (leWe (ugY S + 1)) ∧ Bc.bcB S n (leWe (ugY S + 1)) = leWe (ugY S + 1) := by
  obtain ⟨hDY, hBY⟩ := yyY3_D (S := S) (n := n)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hD2
  rw [hBY, hB2] at hBs
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  rw [hBs] at hBo
  rw [yyWY1_eq]; exact ⟨hDo, hBo⟩

theorem yyWY1_lt : leWe (ugY S + 1) < Om ω :=
  (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal (ugY_lt_Om3.trans Ry.ryOm3_lt)
    (gg_one_lt_of_SC vkOmW.1))).1

theorem yyY_dvd_WY1 : ugY S ∣ leWe (ugY S + 1) := by
  rw [leWe_succ, Vq.vqWeY3]; exact dvd_mul_right _ _

/-- `B_n` is monotone at `Ω₃`: `Ω₃ ≤ a ⇒ Ω₃ ≤ B_n a`. -/
theorem yyB_ge3 {n : ℕ} {a : Ordinal.{0}} (hDa : MvD S a) (ha3 : Om (1 + 1 + 1) ≤ a) :
    Om (1 + 1 + 1) ≤ Bc.bcB S n a := by
  obtain ⟨hD3, hB3⟩ := Vs.vsW_D (S := S) (s := 1 + 1) (by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2) (n := n)
  rcases ha3.lt_or_eq with h | h
  · have := (mvB_lt_iff (k := n) hD3 hDa).2 h; rw [hB3] at this; exact this.le
  · rw [← h, hB3]

/-- The data of the shift `Y₃` over a normal base `a ≥ Ω₃`: own, closure and code conditions. -/
theorem yyEdata {l A a : Ordinal.{0}} (hs : Vq.VqSh S l A (Om (1 + 1 + 1)) (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))))
    (ha3 : Om (1 + 1 + 1) ≤ a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    (∀ d, d ≤ leWe (ugY S + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1)))) ∧
      ugY S ∈ S.CSet (a + leWe (ugY S)) (S.psi (a + leWe (ugY S)) (Om (1 + 1))) ∧
      ∀ Q, SC Q → leKe S (ugY S) a 1 < Q → VkA (1 + 1) Q (ugY S) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have he : (0 : Ordinal.{0}) < S.psi (a + leWe (ugY S + 0)) (Om (1 + 1)) := (SC_psi hκ2 _).1
  obtain ⟨-, hEL⟩ := Vq.vqE_data hs ha3 he
  rw [add_zero] at hEL
  refine ⟨fun d _ => (psi_mono hκ2 le_self_add).2 han, Vq.vqY3_mem ?_, hEL⟩
  rw [Vq.vqWeY3]; exact ha3.trans_lt (lt_add_of_pos_right _ uqY_SC.1)

/-- **`γ ≥ T^a ⇒ T^a ≤ ψ₂(a + Y₃·γ)`** (the top is a fixed point of the layer iteration). -/
theorem yyT_le {a γ : Ordinal.{0}}
    (hβown : ∀ d, d ≤ leWe (ugY S + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
    (hEC : ugY S ∈ S.CSet (a + leWe (ugY S)) (S.psi (a + leWe (ugY S)) (Om (1 + 1))))
    (hβd : leWe (ugY S + 1) ∣ a) (hEL : ∀ Q, SC Q → leKe S (ugY S) a 1 < Q → VkA (1 + 1) Q (ugY S))
    (hγ : leTe S (ugY S + 1) a ≤ γ) :
    leTe S (ugY S + 1) a ≤ S.psi (a + ugY S * γ) (Om (1 + 1)) := by
  refine le_of_forall_lt fun x hx => ?_
  obtain ⟨j, hj⟩ := Vk.vkKe_sup hβown hEC hβd hEL hx
  have h1 := leKe_gt (S := S) (ugY S) a j x hj
  rw [Vq.vqWeY3] at h1
  exact h1.trans_le (psi_mono (InR_Om_succ 1) ((add_le_add_iff_left a).2
    (mul_le_mul_left' (hx.le.trans hγ) _))).1

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **`a + Y₃·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every code `γ < T^a`. -/
theorem yyBaseY3G {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hdv : leWe (ugY S + 1) ∣ a)
    (hdv' : leWe (ugY S + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {γ : Ordinal.{0}}
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγT : γ < leTe S (ugY S + 1) a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + ugY S * γ) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (a + ugY S * γ)
        (D + S.psi (Om (1 + 1)) (Om (1 + 1)) * gxTh (upsilon l) (ldAtR S l) γ) ∧
      Bc.bcB S n (a + ugY S * γ) = Bc.bcB S n a + ugY S * Bc.bcB S n γ := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hρSC : SC (upsilon l) := (leRho hl hX).1
  have hρSC' : SC (upsilon l') := (leRho hl' hX').1
  set A := ConjT.Aη S (cdEta S l) with hAdef
  obtain ⟨hDY, hBY⟩ := yyY3_D (S := S) (n := n)
  obtain ⟨hDY2, hBY2⟩ := yyY2_D (S := S) (n := n)
  obtain ⟨hDW, hBW⟩ := yyWY1_D (S := S) (n := n)
  have ha3' : Om (1 + 1 + 1) ≤ Bc.bcB S n a := yyB_ge3 hb.mv_a ha3
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have han' : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a) (S.psi (Bc.bcB S n a) (Om (1 + 1))) := by
    have h := hb.own' 0 zero_le; rwa [add_zero] at h
  have hYW : ugY S < Om ω := ugY_lt_Om3.trans Ry.ryOm3_lt
  have hY3H : ∀ {l0 : Ordinal.{0}}, ugY S ∈ cdHull S l0 := fun {l0} =>
    Vq.vqY3_mem (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))
  -- the bases of exponent `0 + 1` of the shift `Y₃`
  have hbase1 : ∀ {l0 x : Ordinal.{0}}, VbD S l0 x → leWe (ugY S + 1) ∣ x → x ∈ S.CSet x (S.psi x (Om (1 + 1))) →
      Ro.RoBaseE S l0 (ugY S) (0 + 1) x := by
    intro l0 x hxD hxd hxn
    unfold Ro.RoBaseE
    rw [zero_add]
    refine ⟨hxd, hxD.1, (vkOmW.1.isPrincipal hxD.2.2 yyWY1_lt).trans_le (ConjT.OmW_le_A S _),
      fun d _ => (psi_mono hκ2 le_self_add).2 hxn, fun e' _ he' => ?_⟩
    exact he'.trans_lt (gg_one_lt_of_SC (SC_psi hκ2 _))
  have hs := Vq.vqSh_Y3_rst hl hX hown hρA (le_refl (Om (1 + 1 + 1)))
  have hs' := Vq.vqSh_Y3_rst hl' hX' hA' hρ' (le_refl (Om (1 + 1 + 1)))
  have hT := Vq.vqTopY3 hl hX hown hρA (le_refl (Om (1 + 1 + 1)))
  have hT' := Vq.vqTopY3 hl' hX' hA' hρ' (le_refl (Om (1 + 1 + 1)))
  have hst := Vq.vqStepA hs hl hX hown hρA (GxCl.zero hρSC.1) hT (hbase1 hb.D_a hdv han) ha3 hb.hat hb.law
  have hst' := Vq.vqStepA hs' hl' hX' hA' hρ' (GxCl.zero hρSC'.1) hT' (hbase1 hb.D_a' hdv' han') ha3'
    hb.hat' hb.law'
  have hfix0 : leOe (S.psi (Om (1 + 1)) (Om (1 + 1))) = S.psi (Om (1 + 1)) (Om (1 + 1)) :=
    Ua.uaOe_fix (gg_SC_eps Vq.vqY2_SC) (psiS_bounds (S := S) _ 1).1
  simp only [gxTh_zero, add_zero, hfix0, Vq.vqWeY3] at hst hst'
  -- `γ`
  have hγ2 : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  have hγH : γ ∈ cdHull S l := (ldHull_iff hl hX hγ2).2 hγ
  obtain ⟨hown1, hEC, hEL⟩ := yyEdata hs ha3 han
  have hγs : γ < S.psi (a + ugY S * γ) (Om (1 + 1)) := by
    have h := Vk.vkTe_gt hown1 hEC hdv hEL hγT
    rwa [Vq.vqWeY3] at h
  obtain ⟨hDγ, hBγc, -, hΘγX, hΘγ⟩ := IH γ hγ hγs
  -- `B_n(Y₃·γ) = Y₃·B_n γ`
  have hρAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨hDβ, hBβ⟩ := ldB_mulK (n := n) uqY_SC hDY hBY
    (fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < S.psi (a + ugY S * γ) (Om (1 + 1)) ∧ x < Om (1 + 1))
    (fun x hx => (IH x hx.1 hx.2.1).1)
    (fun x hx hx0 => by
      obtain ⟨hsub, hlog⟩ := gxDec hρSC hρAt x hx.1
      have hlx : log ω x ≤ x := log_le_self ω x
      have hle : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
      exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
        ⟨hsub _ (GxCl.opow hρSC.1 hlog) hle, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
          (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩)
    (fun x hx => hx.2.2.trans uqW_lt_Y) γ ⟨hγ, hγs, hγ2⟩
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hb.mv_a hDβ
  rw [hBβ] at hBa
  -- the reading at `λ`
  obtain ⟨hlaw, hat⟩ := hst γ hγ hγT
  set Θγ := gxTh (upsilon l) (ldAtR S l) γ with hΘγdef
  have hΘγs : Θγ < S.psi (A + D + S.psi (Om (1 + 1)) (Om (1 + 1)) * Θγ) (Om 1) := by rw [← hlaw]; exact gxTh_lt hγ hγs
  have hΘγ1 : Θγ < Om 1 := hΘγs.trans (psi_lt Low.InR_Om_one _)
  -- `B_n(D + Y₂·Θγ)`
  obtain ⟨hDY2γ, hBY2γ⟩ := ldB_mulK (n := n) Vq.vqY2_SC hDY2 hBY2
    (fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1)) (fun x hx => mvD_of_lt (hx.2.trans hLw))
    (fun x hx _ => ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩)
    (fun x hx => hx.1.trans (psiS_bounds (S := S) _ 1).1) Θγ ⟨hΘγ1, hΘγX⟩
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hb.mv_D hDY2γ
  rw [hBY2γ, ← hΘγ] at hBD
  -- `B_n γ < T^{B_n a}`
  have hTmem : a + leWe (ugY S + 1) ∈ S.CSet (a + leWe (ugY S + 1)) (S.psi (a + leWe (ugY S + 1)) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 han)
      (leWe_mem (CSet.add_mem (Vq.vqY3_mem (ha3.trans_lt (lt_add_of_pos_right _ (leWe_pos _)))) (CSet.one_mem _ _)))
  obtain ⟨hDaW, hBaW⟩ := mvB_add (k := n) hb.mv_a hDW
  rw [hBW] at hBaW
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDaW hTmem
  rw [hBaW] at hBT
  have hBγT : Bc.bcB S n γ < leTe S (ugY S + 1) (Bc.bcB S n a) := by
    have h := (mvB_lt_iff (k := n) hDγ hDT).2 hγT
    unfold leTe at h ⊢; rwa [hBT] at h
  have hBγ2 : Bc.bcB S n γ < Om (1 + 1) := hBγT.trans (leTe_lt_Om2 _ _)
  have hBγH : Bc.bcB S n γ ∈ cdHull S l' := (ldHull_iff hl' hX' hBγ2).2 hBγc
  obtain ⟨hown1', hEC', hEL'⟩ := yyEdata hs' ha3' han'
  have hBγs : Bc.bcB S n γ < S.psi (Bc.bcB S n a + ugY S * Bc.bcB S n γ) (Om (1 + 1)) := by
    have h := Vk.vkTe_gt hown1' hEC' hdv' hEL' hBγT
    rwa [Vq.vqWeY3] at h
  -- the reading at `λ'`
  obtain ⟨hlaw', hat'⟩ := hst' _ hBγc hBγT
  -- bounds and memberships
  have hYγW : ∀ {x : Ordinal.{0}}, x < Om (1 + 1) → ugY S * x < Om ω := fun {x} hx => by
    refine lt_of_le_of_lt ?_ (yyWY1_lt (S := S))
    rw [leWe_succ, Vq.vqWeY3]; exact mul_le_mul_left' hx.le _
  have hθ : ∀ {x c : Ordinal.{0}}, x < Om ω → c < S.psi x (Om (1 + 1)) → c < ConjT.th S := fun {x c} hx hc =>
    hc.trans_le (psi_mono hκ2 hx.le).1
  have hYmem : ∀ {x c g b0 : Ordinal.{0}}, Om (1 + 1 + 1) ≤ b0 → b0 + ugY S * g ≤ x → g < c →
      ugY S * g ∈ S.CSet x c := by
    intro x c g b0 hb0 hx hgc
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [mul_zero]; exact CSet.zero_mem _ _
    · refine ldMulK_mem uqY_SC (Vq.vqY3_mem ?_) (CSet.of_lt hgc)
      exact (hb0.trans_lt (lt_add_of_pos_right _ (mul_pos uqY_SC.1 (pos_iff_ne_zero.2 hg0)))).trans_le hx
  have hownG : ∀ {b0 g : Ordinal.{0}}, Om (1 + 1 + 1) ≤ b0 →
      (∀ d, d ≤ Om (1 + 1) → b0 ∈ S.CSet (b0 + d) (S.psi (b0 + d) (Om (1 + 1)))) →
      g < S.psi (b0 + ugY S * g) (Om (1 + 1)) →
      ∀ d, d ≤ Om (1 + 1) → b0 + ugY S * g ∈ S.CSet (b0 + ugY S * g + d) (S.psi (b0 + ugY S * g + d) (Om (1 + 1))) := by
    intro b0 g hb0 hown0 hg d _
    have h0 := Yt.ytOwnAll hown0 (ugY S * g + d)
    rw [← add_assoc] at h0
    exact CSet.add_mem h0 (hYmem hb0 le_self_add (hg.trans_le (psi_mono hκ2 le_self_add).1))
  have hdvdG : ∀ {b0 g : Ordinal.{0}}, Om (1 + 1) ∣ b0 → Om (1 + 1) ∣ b0 + ugY S * g := fun h =>
    dvd_add h (Dvd.dvd.mul_right yyOm2_dvd_Y _)
  have haγW : a + ugY S * γ < Om ω := vkOmW.1.isPrincipal hb.D_a.2.2 (hYγW hγ2)
  have haγW' : Bc.bcB S n a + ugY S * Bc.bcB S n γ < Om ω := vkOmW.1.isPrincipal hb.D_a'.2.2 (hYγW hBγ2)
  refine ⟨⟨⟨CSet.add_mem hb.D_a.1 (ldMulK_mem uqY_SC hY3H hγH),
      CSet.add_mem hb.D_a.2.1 (ldMulK_mem uqY_SC (Vq.vqY3_mem Ry.ryOm3_lt) (CSet.of_lt (hθ haγW hγs))),
      vkOmW.1.isPrincipal hb.D_a.2.2 (hYγW hγ2)⟩,
    hdvdG hb.dvd, hownG ha3 hb.own hγs, hDa, hDD, by rw [← add_assoc]; exact hat,
    by rw [← add_assoc]; exact hlaw, ?_, ?_, ?_, ?_, ?_⟩, hBa⟩
  · rw [hBa]
    exact ⟨CSet.add_mem hb.D_a'.1 (ldMulK_mem uqY_SC hY3H hBγH),
      CSet.add_mem hb.D_a'.2.1 (ldMulK_mem uqY_SC (Vq.vqY3_mem Ry.ryOm3_lt) (CSet.of_lt (hθ haγW' hBγs))),
      haγW'⟩
  · rw [hBa]; exact hdvdG hb.dvd'
  · rw [hBa]; exact hownG ha3' hb.own' hBγs
  · rw [hBD, ← add_assoc]; exact hat'
  · rw [hBa, hBD, ← add_assoc]; exact hlaw'

/-- **EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+1})` MOVES** above a base `a ≥ Ω₃` with a law at both ends,
`W^{Y₃+1} ∣ a`, `W^{Y₃+1} ∣ B_n a`, under IH(s). -/
theorem yyY3MoveW {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hdv : leWe (ugY S + 1) ∣ a)
    (hdv' : leWe (ugY S + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < leTe S (ugY S + 1) a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have hs0 := Vq.vqSh_Y3_rst hl hX hown hρA (le_refl (Om (1 + 1 + 1)))
  obtain ⟨hown1, hEC, hEL⟩ := yyEdata hs0 ha3 han
  have hYa : ugY S ∣ a := yyY_dvd_WY1.trans hdv
  have hYa' : ugY S ∣ Bc.bcB S n a := yyY_dvd_WY1.trans hdv'
  -- the block of `s`
  have hsat := hs
  obtain ⟨c, hcH, hcA, rfl⟩ := hs
  rcases lt_or_ge c a with hca | hca
  · -- `s = ψ₂ a`
    have hle : S.psi c (Om (1 + 1)) ≤ S.psi a (Om (1 + 1)) := (psi_mono hκ2 hca.le).1
    have he : S.psi c (Om (1 + 1)) = S.psi (a + ugY S * 0) (Om (1 + 1)) := by
      rw [mul_zero, add_zero]; exact le_antisymm hle hsa
    have hsY : S.psi c (Om (1 + 1)) < S.psi (a + ugY S) (Om (1 + 1)) := by
      rw [he, mul_zero, add_zero]
      exact psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ uqY_SC.1) ((psi_mono hκ2 le_self_add).2 han)
    exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hb hYa hYa' hsat hsa hsY IH
  set d := c - a with hd
  have ec : c = a + d := (Ordinal.add_sub_cancel_of_le hca).symm
  have hcW : c < a + leWe (ugY S + 1) := by
    by_contra h; push Not at h
    exact absurd ((psi_mono hκ2 h).1.trans_lt hsT) (lt_irrefl _)
  have hdW : d < ugY S * Om (1 + 1) := by
    have h := Ry.rySub_lt hca hcW; rwa [leWe_succ, Vq.vqWeY3] at h
  have hY0 : ugY S ≠ 0 := uqY_SC.1.ne'
  set γ := d / ugY S with hγdef
  have hγ2 : γ < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hY0).1 hdW
  have hdC : d ∈ cdHull S l := Ta.taSub_mem c hcH a
  have hγH : γ ∈ cdHull S l := by
    have h := (Vh.vhC_div d hdC (ugY S)).2.2 (Vq.vqY3_mem (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)))
    rwa [gg_SC_eps uqY_SC] at h
  have hγc : GxCl (upsilon l) (ldAtR S l) γ := (ldHull_iff hl hX hγ2).1 hγH
  have hdγ : ugY S * γ ≤ d := Ordinal.mul_div_le d (ugY S)
  have hdγ1 : d < ugY S * (γ + 1) := by
    have := Ordinal.lt_mul_succ_div d hY0; rwa [Order.succ_eq_add_one] at this
  -- `γ < T^a`
  have hγT : γ < leTe S (ugY S + 1) a := by
    by_contra h; push Not at h
    have h2 := yyT_le hown1 hEC hdv hEL h
    have h3 : S.psi (a + ugY S * γ) (Om (1 + 1)) ≤ S.psi c (Om (1 + 1)) := by
      rw [ec]; exact (psi_mono hκ2 ((add_le_add_iff_left a).2 hdγ)).1
    exact absurd ((h2.trans h3).trans_lt hsT) (lt_irrefl _)
  have hsγ : S.psi (a + ugY S * γ) (Om (1 + 1)) ≤ S.psi c (Om (1 + 1)) := by
    rw [ec]; exact (psi_mono hκ2 ((add_le_add_iff_left a).2 hdγ)).1
  have hsγ1 : S.psi c (Om (1 + 1)) ≤ S.psi (a + ugY S * γ + ugY S) (Om (1 + 1)) := by
    rw [ec, add_assoc, ← mul_add_one]; exact (psi_mono hκ2 ((add_le_add_iff_left a).2 hdγ1.le)).1
  rcases hsγ1.lt_or_eq with hlt | heq
  · obtain ⟨hbγ, hBγ⟩ := yyBaseY3G hR h1 hr hl' hB hA' hρ' hb hdv hdv' ha3 hγc hγT
      fun x hx hxs => IH x hx (hxs.trans_le hsγ)
    have hYγ : ugY S ∣ a + ugY S * γ := dvd_add hYa (dvd_mul_right _ _)
    have hYγ' : ugY S ∣ Bc.bcB S n (a + ugY S * γ) := by rw [hBγ]; exact dvd_add hYa' (dvd_mul_right _ _)
    exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hbγ hYγ hYγ' hsat hsγ hlt IH
  · -- `s = ψ₂(a + Y₃·(γ+1))`, the base atom of the next block
    have hTSC : SC (leTe S (ugY S + 1) a) := SC_psi hκ2 _
    have hγ1T : γ + 1 < leTe S (ugY S + 1) a := hTSC.isSuccLimit.add_one_lt hγT
    have hγ1c : GxCl (upsilon l) (ldAtR S l) (γ + 1) :=
      (ldHull_iff hl hX (hγ1T.trans (leTe_lt_Om2 _ _))).1 (CSet.succ_mem hγH)
    have e1 : a + ugY S * γ + ugY S = a + ugY S * (γ + 1) := by rw [mul_add_one, add_assoc]
    rw [e1] at heq
    obtain ⟨hbγ, hBγ⟩ := yyBaseY3G hR h1 hr hl' hB hA' hρ' hb hdv hdv' ha3 hγ1c hγ1T
      fun x hx hxs => IH x hx (hxs.trans_le heq.ge)
    have hYγ : ugY S ∣ a + ugY S * (γ + 1) := dvd_add hYa (dvd_mul_right _ _)
    have hYγ' : ugY S ∣ Bc.bcB S n (a + ugY S * (γ + 1)) := by
      rw [hBγ]; exact dvd_add hYa' (dvd_mul_right _ _)
    have hown2 := hbγ.own 0 zero_le
    rw [add_zero] at hown2
    have hsY : S.psi c (Om (1 + 1)) < S.psi (a + ugY S * (γ + 1) + ugY S) (Om (1 + 1)) := by
      rw [heq]
      exact psi_lt_psi_of_mem hκ2 (lt_add_of_pos_right _ uqY_SC.1) ((psi_mono hκ2 le_self_add).2 hown2)
    exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hbγ hYγ hYγ' hsat heq.ge hsY IH

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+1})` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under the
premise of WallBelow at `s` (supersedes `Yy.yyTopMoveY3` and `Yt.ytTopMoveY`). -/
theorem yyTopMoveY3W (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < leTe S (ugY S + 1) (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hW : ∀ e', leWe (ugY S + 1) ∣ leWe (X + e') := fun e' => by
    unfold leWe
    refine opow_dvd_opow ω (mul_le_mul_left' ?_ _)
    exact (Order.add_one_le_of_lt (ugY_lt_Om3.trans_le (Yt.ytOm3_le_X k))).trans le_self_add
  have hd : leWe (ugY S + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : leWe (ugY S + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]
    exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := by
      calc X = leWe X := (Vn.vnWe_OmK k).symm
        _ ≤ leWe (X + e) := leWe_mono le_self_add
    exact (Yt.ytOm3_le_X k).trans (hXle.trans le_add_self)
  exact yyY3MoveW hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yy
