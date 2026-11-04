import Googology.Trans.PoR.InaccPsi.R2.ZdY3Up

/-!
# THE SUB-BASES AND THE INDUCTION ON THE EXPONENT, GENERIC IN THE RELATIVE SHIFT

`W^x = leWe x`, `Ω^x = leOe x`, `Θ`, `B_n`, "window", `A'`, `Yj.YjBase`, "IH(s)" as in `Zd.zdBaseY3E`.  A relative
shift `(X, X̂)` (`ZdRS S X X̂`): `X ≠ 0`, `X < Ω_ω`, `X ∈ Cl(c, b)` for every `c > Ω₃`, `B_n` fixes `Ω₂·X` and `Ω₁·X̂`,
at every restart `(X, X̂)` is a `Vq.VqSh` at the base `Ω₃` with the top `Rv.RvTop λ Ω₃ X X̂ e` at every code `e`.
`(Y₃, Y₂)` is one (`zdRS_Y3`).

* `zdBaseXE` (**`a + W^{X+e}·γ` IS A BASE WITH A LAW AT BOTH ENDS**; `Zd.zdBaseY3E` is `X = Y₃`),
* `zdXUp` (**THE INDUCTION ON THE EXPONENT**: the moves below `ψ₂(a + W^X)` over every base give the moves below
  `ψ₂(a + W^{X+e})` for every `e ≤ Ω₂`; `Zd.zdY3Up` is `X = Y₃`).

No new axiom.  New definition: `ZdRS` (the data of a relative shift).
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

/-- **A relative shift `(X, X̂)` at the base `Ω₃`**: the data used by `zdBaseXE` and `zdXUp`. -/
structure ZdRS (S : InaccSeq.{0}) (X Xh : Ordinal.{0}) : Prop where
  ne : X ≠ 0
  lt : X < Om ω
  mem : ∀ c b : Ordinal.{0}, Om (1 + 1 + 1) < c → X ∈ S.CSet c b
  shB : Ro.RoShB S X Xh
  sh : ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Pv S ηx → A ∈ S.CSet A (S.psi A (Om 1)) →
    S.psi A (Om 1) = upsilon l → Vq.VqSh S l A (Om (1 + 1 + 1)) X Xh
  top : ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Pv S ηx → A ∈ S.CSet A (S.psi A (Om 1)) →
    S.psi A (Om 1) = upsilon l → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      Rv.RvTop S l (Om (1 + 1 + 1)) X Xh e

/-- **`(Y₃, Y₂)` is a relative shift.** -/
theorem zdRS_Y3 : ZdRS S (ugY S) (S.psi (Om (1 + 1)) (Om (1 + 1))) :=
  ⟨uqY_SC.1.ne', ugY_lt_Om3.trans Ry.ryOm3_lt, fun _ _ h => Vq.vqY3_mem h, zdShB_Y3,
    fun _ _ _ hl hX hA hρ => Vq.vqSh_Y3_rst hl hX hA hρ (le_refl _),
    fun _ _ _ hl hX hA hρ => Vq.vqTopY3E hl hX hA hρ (le_refl _)⟩

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

set_option maxHeartbeats 1000000 in
/-- **`a + W^{X+e}·γ` IS A BASE WITH A LAW AT BOTH ENDS** for every relative shift `X` of `ZdRS`, every code `e`
with `e + 1 < ψ₂(a + W^{X+Ω₂})` and every code `0 < γ < ψ₂(a + W^{X+e+1})` (`Zd.zdBaseY3E` is `X = Y₃`). -/
theorem zdBaseXE {X Xh : Ordinal.{0}} (hrs : ZdRS S X Xh) {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (ha3 : Om (1 + 1 + 1) ≤ a)
    {e : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hdv : leWe (X + (e + 1)) ∣ a)
    (hdv' : leWe (X + (Bc.bcB S n e + 1)) ∣ Bc.bcB S n a)
    (heE : e + 1 < S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1))) {γ : Ordinal.{0}}
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγ0 : γ ≠ 0) (hγT : γ < leTe S (X + e + 1) a)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + leWe (X + e) * γ) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (a + leWe (X + e) * γ)
        (D + leOe (Xh + gxTh (upsilon l) (ldAtR S l) e) *
          gxTh (upsilon l) (ldAtR S l) γ) ∧
      Bc.bcB S n (a + leWe (X + e) * γ) = Bc.bcB S n a + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  obtain ⟨hρSC', -⟩ := leRho hl' hX'
  set Y := X with hYdef
  set Y2 := Xh with hY2def
  have hY0 : Y ≠ 0 := hrs.ne
  have ha3' : Om (1 + 1 + 1) ≤ Bc.bcB S n a := Yy.yyB_ge3 hb.mv_a ha3
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have han' : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a) (S.psi (Bc.bcB S n a) (Om (1 + 1))) := by
    have h := hb.own' 0 zero_le; rwa [add_zero] at h
  have hYW : Y < Om ω := hrs.lt
  have hY3H : ∀ {l0 : Ordinal.{0}}, Y ∈ cdHull S l0 := fun {l0} =>
    hrs.mem _ _ (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))
  have hXr : ∀ c b : Ordinal.{0}, a < c → X ∈ S.CSet c b := fun c b h => hrs.mem c b (ha3.trans_lt h)
  have hXr' : ∀ c b : Ordinal.{0}, Bc.bcB S n a < c → X ∈ S.CSet c b := fun c b h => hrs.mem c b (ha3'.trans_lt h)
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
  have hs := hrs.sh l _ _ hl hX hown hρA
  have hT := hrs.top l _ _ hl hX hown hρA e hec he2
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
  obtain ⟨hDW, -, hDWγ, hBWγ⟩ := Ro.roB_We (n := n) hY0 hrs.shB P hPD hPdec hPW
    ⟨hec, hes', he2⟩ ⟨hγ, hγs, hγ2⟩
  obtain ⟨hDW1, hBW1, -, -⟩ := Ro.roB_We (n := n) hY0 hrs.shB P hPD hPdec hPW
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
  obtain ⟨hDO, hBO⟩ := Ro.roB_Oe (n := n) hrs.shB hΘe1 hΘeX hΘγ1 hΘγX
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) hb.mv_D hDO
  rw [hBO, ← hΘe, ← hΘγ] at hBD
  -- the base of exponent `B_n e + 1` at `λ'`
  obtain ⟨-, hown'⟩ := zdOwnMoveBr hY0 hrs.shB n hXr hXr' hb.mv_a han hDe1 heE
  rw [hBe1] at hown'
  have hBe12 : Bc.bcB S n e + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hBe2
  have hbE' : Ro.RoBaseE S l' Y (Bc.bcB S n e + 1) (Bc.bcB S n a) := by
    refine ⟨hdv', hb.D_a'.1, ?_, fun d _ => (psi_mono hκ2 le_self_add).2 han',
      fun e' _ h => hown' e' h⟩
    exact (vkOmW.1.isPrincipal hb.D_a'.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2
      (vkOmW.1.isPrincipal hYW (hBe12.trans ldOm2_lt_OmW))).1).trans_le (ConjT.OmW_le_A S _)
  have hs' := hrs.sh l' _ _ hl' hX' hA' hρ'
  have hT' := hrs.top l' _ _ hl' hX' hA' hρ' (Bc.bcB S n e) hBec hBe2
  have hst' := Vq.vqStepA hs' hl' hX' hA' hρ' hBec hT' hbE' ha3' hb.hat' hb.law'
  -- `B_n γ < ψ₂(B_n a + W^{Y₃+B_n e+1})`
  have hTmem : a + leWe (Y + (e + 1)) ∈ S.CSet (a + leWe (Y + (e + 1))) (S.psi (a + leWe (Y + (e + 1))) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 han)
      (leWe_mem (CSet.add_mem (hrs.mem _ _ (ha3.trans_lt (lt_add_of_pos_right _ (leWe_pos _))))
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
    have h := leWe_dvd ((Order.one_le_iff_ne_zero.2 hrs.ne).trans (le_self_add : Y ≤ Y + x)); rwa [leWe_one] at h
  have hownG : ∀ {b0 x g : Ordinal.{0}}, Om (1 + 1 + 1) ≤ b0 → b0 ∈ S.CSet b0 (S.psi b0 (Om (1 + 1))) →
      x < S.psi (b0 + leWe (Y + x)) (Om (1 + 1)) → g ≠ 0 → g < S.psi (b0 + leWe (Y + x) * g) (Om (1 + 1)) →
      ∀ d, d ≤ Om (1 + 1) → b0 + leWe (Y + x) * g ∈
        S.CSet (b0 + leWe (Y + x) * g + d) (S.psi (b0 + leWe (Y + x) * g + d) (Om (1 + 1))) := by
    intro b0 x g hb0 hb0n hx hg0 hg d _
    have hle1 : b0 + leWe (Y + x) ≤ b0 + leWe (Y + x) * g + d :=
      ((add_le_add_iff_left b0).2 (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hg0))).trans le_self_add
    have hle2 : b0 + leWe (Y + x) * g ≤ b0 + leWe (Y + x) * g + d := le_self_add
    refine CSet.add_mem ((psi_mono hκ2 (le_self_add.trans hle2)).2 hb0n) (leMulWe_mem (CSet.add_mem ?_ ?_) ?_)
    · exact hrs.mem _ _ (hb0.trans_lt ((lt_add_of_pos_right _ (leWe_pos _)).trans_le hle1))
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
      CSet.add_mem hb.D_a.2.1 (leMulWe_mem (CSet.add_mem (hrs.mem _ _ Ry.ryOm3_lt) (CSet.of_lt (hθ haγW hes')))
        (CSet.of_lt (hθ haγW hγs))), haγW⟩,
    dvd_add hb.dvd (Dvd.dvd.mul_right (hW2 e) _), hownG ha3 han hes hγ0 hγs, hDa, hDD,
    by rw [← add_assoc]; exact hat, by rw [← add_assoc]; exact hlaw, ?_, ?_, ?_, ?_, ?_⟩, hBa⟩
  · rw [hBa]
    exact ⟨CSet.add_mem hb.D_a'.1 (leMulWe_mem (CSet.add_mem hY3H hBeH) hBγH),
      CSet.add_mem hb.D_a'.2.1 (leMulWe_mem (CSet.add_mem (hrs.mem _ _ Ry.ryOm3_lt)
        (CSet.of_lt (hθ haγW' (hBes.trans_le (psi_mono hκ2 ((add_le_add_iff_left _).2
          (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hBγ0)))).1)))) (CSet.of_lt (hθ haγW' hBγs))), haγW'⟩
  · rw [hBa]; exact dvd_add hb.dvd' (Dvd.dvd.mul_right (hW2 _) _)
  · rw [hBa]; exact hownG ha3' han' hBes hBγ0 hBγs
  · rw [hBD, ← add_assoc]; exact hat'
  · rw [hBa, hBD, ← add_assoc]; exact hlaw'

set_option maxHeartbeats 1000000 in
/-- **THE INDUCTION ON THE EXPONENT, GENERIC IN THE RELATIVE SHIFT**: if every atom `ψ₂(a) ≤ s < ψ₂(a + W^X)` moves
(over every base with `W^X ∣ a`, `W^X ∣ B_n a`), then every atom `ψ₂(a) ≤ s < ψ₂(a + W^{X+e})` moves, `e ≤ Ω₂`. -/
theorem zdXUp {X Xh : Ordinal.{0}} (hrs : ZdRS S X Xh)
    (HB : ∀ a D, YjBase S n l l' A' a D → leWe X ∣ a → leWe X ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a →
      ∀ s ∈ ldAtR S l, S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + leWe X) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)) :
    ∀ e, MvD S e → e ≤ Om (1 + 1) → ∀ a D, YjBase S n l l' A' a D →
    leWe (X + e) ∣ a → leWe (X + Bc.bcB S n e) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a →
    ∀ s ∈ ldAtR S l, S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + leWe (X + e)) (Om (1 + 1)) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set Y := X with hYdef
  have hY0 : Y ≠ 0 := hrs.ne
  have hYW : Y < Om ω := hrs.lt
  have hYdv : ∀ x, leWe Y ∣ leWe (Y + x) := fun x => leWe_dvd (le_self_add : Y ≤ Y + x)
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IHe =>
  intro hDe he2 a D hb hdv hdv' ha3 s hs hsa hse IH
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have hYa : leWe Y ∣ a := (hYdv e).trans hdv
  have hYa' : leWe Y ∣ Bc.bcB S n a := (hYdv _).trans hdv'
  -- the argument of `s` in normal form
  have heW : Y + e < Om ω := vkOmW.1.isPrincipal hYW (he2.trans_lt ldOm2_lt_OmW)
  have haeW : a + leWe (Y + e) < Om ω :=
    vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 heW).1
  have hsθ : s < ConjT.th S := hse.trans_le (psi_mono hκ2 haeW.le).1
  obtain ⟨d, hdD, hds, hdn⟩ := vbReach hl hX hs hsθ
  subst hds
  have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
    psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
  have hdle : ∀ x, S.psi x (Om (1 + 1)) ≤ S.psi d (Om (1 + 1)) → x ≤ d := fun x hx => by
    by_contra hc; push Not at hc
    exact absurd (hdnx x hc) (not_lt.2 hx)
  have had : a ≤ d := hdle a hsa
  have hdae : d < a + leWe (Y + e) := by
    by_contra hc; push Not at hc
    exact absurd ((psi_mono hκ2 hc).1.trans_lt hse) (lt_irrefl _)
  -- the case `d < a + Y₃`
  rcases lt_or_ge d (a + leWe Y) with hdY | hdY
  · exact HB a D hb hYa hYa' ha3 _ hs hsa (hdnx _ hdY) IH
  -- the leading term `W^{Y₃+e₁}·γ` of `δ = d - a`
  set δ := d - a with hδdef
  have hdδ : d = a + δ := (Ordinal.add_sub_cancel_of_le had).symm
  have hYδ : leWe Y ≤ δ := by
    by_contra hc; push Not at hc
    exact absurd (by rw [hdδ]; exact (add_lt_add_iff_left a).2 hc : d < a + leWe Y) (not_lt.2 hdY)
  have hδ0 : δ ≠ 0 := ((leWe_pos _).trans_le hYδ).ne'
  have hδW : δ < leWe (Y + e) := by
    by_contra hc; push Not at hc
    exact absurd (by rw [hdδ]; exact (add_le_add_iff_left a).2 hc : a + leWe (Y + e) ≤ d) (not_le.2 hdae)
  set L := log ω δ with hLdef
  have hYL : Om (1 + 1) * Y ≤ L := by
    rw [hLdef, ← Ordinal.opow_le_iff_le_log one_lt_omega0 hδ0]; exact hYδ
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  set E₁ := L / Om (1 + 1) with hE₁def
  have hYE : Y ≤ E₁ := by
    rw [hE₁def, Ordinal.le_div hΩ0]; exact hYL
  set e₁ := E₁ - Y with he₁def
  have hE₁ : Y + e₁ = E₁ := Ordinal.add_sub_cancel_of_le hYE
  have hLlt : L < Om (1 + 1) * (Y + e) := (lt_opow_iff_log_lt one_lt_omega0 hδ0).1 hδW
  have hE₁lt : E₁ < Y + e := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hLlt
  have he₁e : e₁ < e := by
    rw [← hE₁] at hE₁lt; exact (add_lt_add_iff_left Y).1 hE₁lt
  have hW₁ : leWe (Y + e₁) ≤ δ := by
    rw [hE₁]; unfold leWe
    exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le L _)).trans (opow_log_le_self ω hδ0)
  have hδW1 : δ < leWe (Y + e₁ + 1) := by
    have hL1 : L < Om (1 + 1) * (E₁ + 1) := by
      have := Ordinal.lt_mul_succ_div L hΩ0; rwa [Order.succ_eq_add_one] at this
    rw [hE₁]; unfold leWe
    exact (lt_opow_iff_log_lt one_lt_omega0 hδ0).2 hL1
  have hWpos : leWe (Y + e₁) ≠ 0 := (leWe_pos _).ne'
  set γ := δ / leWe (Y + e₁) with hγdef
  set r := δ % leWe (Y + e₁) with hrdef
  have hδγ : δ = leWe (Y + e₁) * γ + r := (Ordinal.div_add_mod δ _).symm
  have hrW : r < leWe (Y + e₁) := Ordinal.mod_lt δ hWpos
  have hγ0 : γ ≠ 0 := by
    intro h0
    have : δ = r := by rw [hδγ, h0, mul_zero, zero_add]
    exact absurd (this ▸ hrW) (not_lt.2 hW₁)
  have hγ2 : γ < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hWpos).1 (by rw [← leWe_succ]; exact hδW1)
  -- memberships
  have hdH : d ∈ cdHull S l := hdD.1
  have hδH : δ ∈ cdHull S l := Ta.taSub_mem d hdH a
  have hLH : L ∈ cdHull S l := leLog_mem hδH
  have hE₁H : E₁ ∈ cdHull S l := by
    have h := (Vh.vhC_div L hLH (Om (1 + 1))).2.2 (mxOm2_mem _ _); rwa [gg_SC_eps ldOm2_SC] at h
  have he₁H : e₁ ∈ cdHull S l := Ta.taSub_mem E₁ hE₁H Y
  have hYe₁H : Y + e₁ ∈ cdHull S l := by rw [hE₁]; exact hE₁H
  have hγH : γ ∈ cdHull S l := (Vh.vhC_div δ hδH (Om (1 + 1) * (Y + e₁))).2.2
    (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hYe₁H)
  have he₁2 : e₁ < Om (1 + 1) := he₁e.trans_le he2
  have he₁c : GxCl (upsilon l) (ldAtR S l) e₁ := (ldHull_iff hl hX he₁2).1 he₁H
  have hγc : GxCl (upsilon l) (ldAtR S l) γ := (ldHull_iff hl hX hγ2).1 hγH
  have hbd : a + leWe (Y + e₁) * γ ≤ d := by
    rw [hdδ, hδγ]; exact (add_le_add_iff_left a).2 le_self_add
  have hsb : S.psi (a + leWe (Y + e₁) * γ) (Om (1 + 1)) ≤ S.psi d (Om (1 + 1)) := (psi_mono hκ2 hbd).1
  have hγ1 : leWe (Y + e₁) ≤ leWe (Y + e₁) * γ := Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hγ0)
  -- the own clause `e₁ + 1 < E^a`
  have hXr : ∀ c b : Ordinal.{0}, a < c → X ∈ S.CSet c b := fun c b h => hrs.mem c b (ha3.trans_lt h)
  have he₁E : e₁ < S.psi (a + leWe (Y + Om (1 + 1))) (Om (1 + 1)) := by
    by_contra hc; push Not at hc
    have h1 := zdTopE_ge hXr han hc
    have h2 : S.psi (a + leWe (Y + e₁)) (Om (1 + 1)) ≤ S.psi d (Om (1 + 1)) :=
      (psi_mono hκ2 (((add_le_add_iff_left a).2 hγ1).trans hbd)).1
    have h3 : S.psi (a + leWe (Y + e)) (Om (1 + 1)) ≤ S.psi (a + leWe (Y + Om (1 + 1))) (Om (1 + 1)) :=
      (psi_mono hκ2 ((add_le_add_iff_left a).2 (leWe_mono ((add_le_add_iff_left Y).2 he2)))).1
    exact absurd ((h1.trans h2).trans_lt (hse.trans_le h3)) (lt_irrefl _)
  have he₁1E : e₁ + 1 < S.psi (a + leWe (Y + Om (1 + 1))) (Om (1 + 1)) :=
    (SC_psi hκ2 _).isSuccLimit.add_one_lt he₁E
  have hes₁ : e₁ < S.psi (a + leWe (Y + e₁)) (Om (1 + 1)) := (zdOwnBr_iff hXr han e₁).2 he₁E e₁ le_rfl
  have he₁s : e₁ < S.psi d (Om (1 + 1)) :=
    hes₁.trans_le ((psi_mono hκ2 ((add_le_add_iff_left a).2 hγ1)).1.trans hsb)
  obtain ⟨hDe₁, -, -, -, -⟩ := IH e₁ he₁c he₁s
  have hBlt : Bc.bcB S n e₁ < Bc.bcB S n e := (mvB_lt_iff (k := n) hDe₁ hDe).2 he₁e
  have hdv1 : leWe (Y + (e₁ + 1)) ∣ a :=
    (leWe_dvd ((add_le_add_iff_left Y).2 (Order.add_one_le_of_lt he₁e))).trans hdv
  have hdv1' : leWe (Y + (Bc.bcB S n e₁ + 1)) ∣ Bc.bcB S n a :=
    (leWe_dvd ((add_le_add_iff_left Y).2 (Order.add_one_le_of_lt hBlt))).trans hdv'
  -- `γ < T_{Y₃+e₁+1}(a)`
  have hγT : γ < leTe S (Y + e₁ + 1) a := by
    by_contra hc; push Not at hc
    obtain ⟨hEC, hEL⟩ := Vq.vqE_data (hrs.sh l _ _ hl hX hown hρA) ha3 hes₁
    have hT := zdT_le (E := Y + e₁) (fun d' _ => (psi_mono hκ2 le_self_add).2 han) hEC
      (by rw [add_assoc]; exact hdv1) hEL hc
    have hdT : d < a + leWe (Y + e₁ + 1) := by rw [hdδ]; exact (add_lt_add_iff_left a).2 hδW1
    exact absurd ((hT.trans hsb).trans_lt (hdnx _ hdT)) (lt_irrefl _)
  -- the sub-base `b = a + W^{Y₃+e₁}·γ`
  obtain ⟨hbb, hBb⟩ := zdBaseXE hR h1 hr hl' hB hA' hρ' hrs hb ha3 he₁c hdv1 hdv1' he₁1E hγc hγ0 hγT
    (fun x hx hxs => IH x hx (hxs.trans_le hsb))
  refine IHe e₁ he₁e hDe₁ he₁2.le _ _ hbb ?_ ?_ (ha3.trans le_self_add) _ hs hsb ?_ IH
  · exact dvd_add ((leWe_dvd ((add_le_add_iff_left Y).2 he₁e.le)).trans hdv) (dvd_mul_right _ _)
  · rw [hBb]; exact dvd_add ((leWe_dvd ((add_le_add_iff_left Y).2 hBlt.le)).trans hdv') (dvd_mul_right _ _)
  · refine hdnx _ ?_
    rw [hdδ, hδγ, ← add_assoc]
    exact (add_lt_add_iff_left _).2 hrW

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zd
