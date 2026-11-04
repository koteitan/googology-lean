import Googology.Trans.PoR.InaccPsi.R2.ZiTopC

/-!
# THE MOVES BELOW `P + Ω₂·Ω₂` OVER A FIXED PREFIX `P`: the moving shifts `P + Ω₂·ξ` for EVERY code `ξ`

`Θ`, `W^x`, `B_n`, "window", `A'`, `Yj.YjBase`, "IH(s)", `Zd.ZdBot` as in `Zd.zdXUp`; `(P, P̂)` a fixed relative shift
`Zd.ZdRS S P P̂`, `X_ξ = Zi.ziXp P ξ = P + Ω₂·ξ`, `X̂_y = Zi.ziXhp P̂ y = P̂ + Ω₁·y`, `T(a) = Zi.ziTC S P a`.

A code `ξ` of `λ` (below `T(a₀)`, so own over the root base `a₀`) gives the MOVING relative shift
`(P + Ω₂·ξ, P̂ + Ω₁·Θ_λ ξ) ↦ (P + Ω₂·B_n ξ, P̂ + Ω₁·Θ_{λ'}(B_n ξ))` once the codes below some `s₀ > ξ` move.

* `ziB_Xr`, `ziB_WXr`, `ziB_Xhr` (`B_n(Ω₂·X_ξ) = Ω₂·X_{B_n ξ}`, `B_n W^{X_ξ} = W^{X_{B_n ξ}}`,
  `B_n(Ω₁·X̂_y) = Ω₁·X̂_{B_n y}`), `ziTC_move` (**`B_n T(a₀) = T(B_n a₀)`**),
* `ziRSC` (**THE CODE SHIFT IS A MOVING RELATIVE SHIFT** `Zi.ZiRS` at the root `a₀`),
* `ziBotC` (**`Zi.ZiBotM` at every code shift**: induction on the code `ξ < s₀`, `ξ < T(a₀)`: `0` from `Zd.ZdBot P`,
  successors by `Zi.ziXUpM`, limits by the leading exponent of the argument),
* `ziBotPlat` (**`Zd.ZdBot P ⇒ Zd.ZdBot (P + Ω₂·Ω₂)`**),
* `ziBotW2`, `ziPsi3OffW2` (the prefix `Y₃`: **every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·Ω₂})` moves** over every base
  with a law at both ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, under IH(s); contains `Zd.zdPsi3OffE0` and `Zi.ziPsi3OffK`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Yd
  Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

theorem ziB_K2 {n : ℕ} : MvD S (Om (1 + 1) + Om (1 + 1) : Ordinal.{0}) ∧
    Bc.bcB S n (Om (1 + 1) + Om (1 + 1) : Ordinal.{0}) = Om (1 + 1) + Om (1 + 1) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hD, hB⟩ := mvB_add (k := n) hD2 hD2
  rw [hB2] at hB; exact ⟨hD, hB⟩

theorem ziB_K1 {n : ℕ} : MvD S (Om 1 + Om 1 : Ordinal.{0}) ∧ Bc.bcB S n (Om 1 + Om 1 : Ordinal.{0}) = Om 1 + Om 1 := by
  obtain ⟨hD1, hB1⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hD, hB⟩ := mvB_add (k := n) hD1 hD1
  rw [hB1] at hB; exact ⟨hD, hB⟩

/-- **`B_n(Ω₂·(Y₃ + Ω₂·ξ)) = Ω₂·(Y₃ + Ω₂·B_n ξ)`** for `ξ` in a decomposition-closed class of `B_n`-domain
members below `Ω₂ + Ω₂`. -/
theorem ziB_Xr {n : ℕ} {P0 Pt : Ordinal.{0}} (hP : ZdRS S P0 Pt) (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x))
    (hPK : ∀ x, P x → x < Om (1 + 1) + Om (1 + 1)) {ξ : Ordinal.{0}} (hξ : P ξ) :
    MvD S (Om (1 + 1) * ziXp P0 ξ) ∧ Bc.bcB S n (Om (1 + 1) * ziXp P0 ξ) = Om (1 + 1) * ziXp P0 (Bc.bcB S n ξ) := by
  obtain ⟨hDK, hBK⟩ := ziB_K2 (S := S) (n := n)
  obtain ⟨hDm, hBm⟩ := leB_mulOp2 (n := n) hDK P hPD hPdec hPK ξ hξ
  rw [hBK] at hBm
  obtain ⟨hDY, hBY, -, -⟩ := hP.shB.2 n
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hDm
  rw [hBY, hBm] at hBs
  rw [ziOm2_mul_Xp, ziOm2_mul_Xp]
  exact ⟨hDs, hBs⟩

theorem ziB_WXr {n : ℕ} {P0 Pt : Ordinal.{0}} (hP : ZdRS S P0 Pt) (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x))
    (hPK : ∀ x, P x → x < Om (1 + 1) + Om (1 + 1)) {ξ : Ordinal.{0}} (hξ : P ξ) :
    MvD S (leWe (ziXp P0 ξ)) ∧ Bc.bcB S n (leWe (ziXp P0 ξ)) = leWe (ziXp P0 (Bc.bcB S n ξ)) := by
  obtain ⟨hD, hB⟩ := ziB_Xr (n := n) hP P hPD hPdec hPK hξ
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hD
  rw [hB] at hBo
  unfold leWe; exact ⟨hDo, hBo⟩

/-- **`B_n(Ω₁·(Y₂ + Ω₁·y)) = Ω₁·(Y₂ + Ω₁·B_n y)`** for countable `y < c_{n+1}`. -/
theorem ziB_Xhr {n : ℕ} {P0 Pt : Ordinal.{0}} (hP : ZdRS S P0 Pt) {y : Ordinal.{0}} (hy1 : y < Om 1)
    (hyc : y < Bc.bcC S (n + 1)) :
    MvD S (Om 1 * ziXhp Pt y) ∧ Bc.bcB S n (Om 1 * ziXhp Pt y) = Om 1 * ziXhp Pt (Bc.bcB S n y) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDK, hBK⟩ := ziB_K1 (S := S) (n := n)
  have hK1 : Om (1 : Ordinal.{0}) ≤ Om 1 + Om 1 := le_self_add
  obtain ⟨hDm, hBm⟩ := leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le hK1) y ⟨hy1, hyc⟩
  rw [hBK] at hBm
  obtain ⟨-, -, hDY, hBY⟩ := hP.shB.2 n
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDY hDm
  rw [hBY, hBm] at hBs
  have e : ∀ x : Ordinal.{0}, Om 1 * ziXhp Pt x = Om 1 * Pt + ω ^ (Om 1 + Om 1) * x :=
    fun x => by unfold ziXhp; rw [mul_add, opow_add, gg_SC_eps Ph.ph_SC_Om1, mul_assoc]
  rw [e, e]
  exact ⟨hDs, hBs⟩

/-- `Ω₂` and `0` form a decomposition-closed class. -/
theorem ziB_WXrOm2 {n : ℕ} {P0 Pt : Ordinal.{0}} (hP : ZdRS S P0 Pt) :
    MvD S (leWe (ziXp P0 (Om (1 + 1)))) ∧ Bc.bcB S n (leWe (ziXp P0 (Om (1 + 1)))) = leWe (ziXp P0 (Om (1 + 1))) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  have hl2 : log ω (Om (1 + 1 : Ordinal.{0})) = Om (1 + 1) := by
    conv_lhs => rw [← gg_SC_eps ldOm2_SC]
    exact log_opow one_lt_omega0 _
  have h := ziB_WXr (S := S) (n := n) hP (fun x => x = 0 ∨ x = Om (1 + 1))
    (by rintro x (rfl | rfl); exacts [vbD0, hD2])
    (by
      rintro x (rfl | rfl) hx0
      · exact absurd rfl hx0
      · rw [hl2, gg_SC_eps ldOm2_SC, Ordinal.sub_self]; exact ⟨Or.inr rfl, Or.inl rfl⟩)
    (by rintro x (rfl | rfl); exacts [(ldOm2_SC.1).trans_le le_self_add, lt_add_of_pos_right _ ldOm2_SC.1])
    (Or.inr rfl)
  rwa [hB2] at h

/-- **`B_n T(a₀) = T(B_n a₀)`** for a base `a₀ ≥ Ω₃` in the domain, normal at `Ω₂`. -/
theorem ziTC_move {n : ℕ} {P0 Pt : Ordinal.{0}} (hP : ZdRS S P0 Pt) {a : Ordinal.{0}} (hDa : MvD S a) (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (ha3 : Om (1 + 1 + 1) ≤ a) : MvD S (ziTC S P0 a) ∧ Bc.bcB S n (ziTC S P0 a) = ziTC S P0 (Bc.bcB S n a) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hDW, hBW⟩ := ziB_WXrOm2 (S := S) (n := n) hP
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDa hDW
  rw [hBW] at hBs
  have hown : a + leWe (ziXp P0 (Om (1 + 1))) ∈ S.CSet (a + leWe (ziXp P0 (Om (1 + 1))))
      (S.psi (a + leWe (ziXp P0 (Om (1 + 1)))) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 han) (leWe_mem (CSet.add_mem
      (hP.mem _ _ (ha3.trans_lt (lt_add_of_pos_right _ (leWe_pos _))))
      (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _))))
  obtain ⟨hD, hB⟩ := mxB_atom (n := n) hDs hown
  rw [hBs] at hB
  unfold ziTC; exact ⟨hD, hB⟩

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

variable {P0 Pt : Ordinal.{0}} (hP : ZdRS S P0 Pt)

include hR h1 hr hl' hB hA' hρ' hP

set_option maxHeartbeats 1000000 in
/-- **THE CODE SHIFT IS A MOVING RELATIVE SHIFT**: for a base `a₀ ≥ Ω₃` with a law at both ends, a code `ξ < T(a₀)`
and an `s₀ > ξ` below which the codes move, `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·Θξ) ↦ (Y₃ + Ω₂·B_n ξ, Y₂ + Ω₁·Θ'(B_n ξ))` is a
`Zi.ZiRS` at the root `a₀`. -/
theorem ziRSC {a₀ D₀ s₀ : Ordinal.{0}} (hb₀ : YjBase S n l l' A' a₀ D₀) (ha3 : Om (1 + 1 + 1) ≤ a₀)
    (IH₀ : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s₀ → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))
    {ξ : Ordinal.{0}} (hξc : GxCl (upsilon l) (ldAtR S l) ξ) (hξs : ξ < s₀) (hξT : ξ < ziTC S P0 a₀) :
    ZiRS S n l l' A' a₀ (ziXp P0 ξ) (ziXhp Pt (gxTh (upsilon l) (ldAtR S l) ξ))
      (ziXp P0 (Bc.bcB S n ξ)) (ziXhp Pt (gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n ξ))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have ha3' : Om (1 + 1 + 1) ≤ Bc.bcB S n a₀ := Yy.yyB_ge3 hb₀.mv_a ha3
  have han : a₀ ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1))) := by have h := hb₀.own 0 zero_le; rwa [add_zero] at h
  have hξ2 : ξ < Om (1 + 1) := hξT.trans (ziTC_lt_Om2 P0 a₀)
  obtain ⟨hDξ, hBξc, hBξP, hΘξc, hΘξ⟩ := IH₀ ξ hξc hξs
  have hBξ2 : Bc.bcB S n ξ < Om (1 + 1) := hBξP.trans Lj.ljThP_lt_Om2
  -- the class of codes below `s₀`
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧ x < s₀ ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH₀ x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPK : ∀ x, P x → x < Om (1 + 1) + Om (1 + 1) := fun x hx => hx.2.2.trans_le le_self_add
  have hPξ : P ξ := ⟨hξc, hξs, hξ2⟩
  obtain ⟨hDX, hBX⟩ := ziB_Xr (n := n) hP P hPD hPdec hPK hPξ
  obtain ⟨hDW, hBW⟩ := ziB_WXr (n := n) hP P hPD hPdec hPK hPξ
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1 :=
    hΘξc.trans ((Bc.bcC_lt S (n + 1)).trans (psi_lt Low.InR_Om_one _))
  obtain ⟨hDXh, hBXh⟩ := ziB_Xhr (n := n) hP hΘ1 hΘξc
  rw [← hΘξ] at hBXh
  -- the own conditions
  have hownξ : ξ < S.psi (a₀ + leWe (ziXp P0 ξ)) (Om (1 + 1)) := (ziOwnC_iff P0 a₀ ξ).2 hξT ξ le_rfl
  obtain ⟨hDT, hBT⟩ := ziTC_move (n := n) hP hb₀.mv_a han ha3
  have hBξT : Bc.bcB S n ξ < ziTC S P0 (Bc.bcB S n a₀) := by
    rw [← hBT]; exact (mvB_lt_iff (k := n) hDξ hDT).2 hξT
  have hownξ' : Bc.bcB S n ξ < S.psi (Bc.bcB S n a₀ + leWe (ziXp P0 (Bc.bcB S n ξ))) (Om (1 + 1)) :=
    (ziOwnC_iff P0 _ _).2 hBξT _ le_rfl
  have hXlt : ∀ x, x < Om (1 + 1) → ziXp P0 x < Om ω := fun x hx =>
    vkOmW.1.isPrincipal hP.lt (zdMul2_lt hx)
  have hs := ziVqShC hP hl hX hown hρA ha3 hξc hξT
  have hs' := ziVqShC hP hl' hX' hA' hρ' ha3' hBξc hBξT
  refine ⟨?_, ?_, hXlt ξ hξ2, hXlt _ hBξ2, hs.hull, hs'.hull, fun c b hc hb => ?_, fun c b hc hb => ?_,
    ⟨?_, ?_, hDX, hBX, hDXh, hBXh⟩, hs, hs', ziTopC hP hl hX hown hρA ha3 ξ hξc hξT,
    ziTopC hP hl' hX' hA' hρ' ha3' _ hBξc hBξT⟩
  · unfold ziXp; exact ((pos_iff_ne_zero.2 hP.ne).trans_le le_self_add).ne'
  · unfold ziXp; exact ((pos_iff_ne_zero.2 hP.ne).trans_le le_self_add).ne'
  · exact CSet.add_mem (hP.mem _ _ (ha3.trans_lt hc))
      (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (hownξ.trans_le hb)))
  · exact CSet.add_mem (hP.mem _ _ (ha3'.trans_lt hc))
      (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt (hownξ'.trans_le hb)))
  · unfold ziXhp; exact ((pos_iff_ne_zero.2 hP.shB.1).trans_le le_self_add).ne'
  · unfold ziXhp; exact ((pos_iff_ne_zero.2 hP.shB.1).trans_le le_self_add).ne'

set_option maxHeartbeats 1000000 in
/-- **`Zi.ZiBotM` AT EVERY CODE SHIFT**: below `s₀` (the codes below `s₀` move) every code `ξ < s₀`, `ξ < T(a₀)` gives
the moves below the shift `Y₃ + Ω₂·ξ` over every base `a ≥ a₀`. -/
theorem ziBotC (HB0 : ZdBot S n l l' A' P0) {a₀ D₀ s₀ : Ordinal.{0}} (hb₀ : YjBase S n l l' A' a₀ D₀)
    (ha3 : Om (1 + 1 + 1) ≤ a₀)
    (IH₀ : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s₀ → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → ξ < s₀ → ξ < ziTC S P0 a₀ →
      ZiBotM S n l l' A' a₀ (ziXp P0 ξ) (ziXp P0 (Bc.bcB S n ξ)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IHξ =>
  intro hξc hξs hξT
  have hξ2 : ξ < Om (1 + 1) := hξT.trans (ziTC_lt_Om2 P0 a₀)
  rcases zero_or_succ_or_isSuccLimit ξ with h0 | ⟨ζ, hζ⟩ | hlim
  · subst h0
    rw [Bc.bcB_zero, ziXp_zero]
    intro a D hb ha0 _ hdv hdv' s hs hsa hsT IH
    exact HB0 a D hb hdv hdv' (ha3.trans ha0) s hs hsa hsT IH
  · rw [succ_eq_add_one] at hζ
    subst hζ
    have hζ2 : ζ < Om (1 + 1) := (lt_add_one ζ).trans hξ2
    have hζc : GxCl (upsilon l) (ldAtR S l) ζ :=
      (ldHull_iff hl hX hζ2).1 (mem_of_add_one_mem ((ldHull_iff hl hX hξ2).2 hξc))
    have hζs : ζ < s₀ := (lt_add_one ζ).trans hξs
    have hζT : ζ < ziTC S P0 a₀ := (lt_add_one ζ).trans hξT
    have hrs := ziRSC hR h1 hr hl' hB hA' hρ' hP hb₀ ha3 IH₀ hζc hζs hζT
    have HB := IHξ ζ (lt_add_one ζ) hζc hζs hζT
    obtain ⟨hDζ, -, -, -, -⟩ := IH₀ ζ hζc hζs
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    have hBs : Bc.bcB S n (ζ + 1) = Bc.bcB S n ζ + 1 := by
      obtain ⟨-, h⟩ := mvB_add (k := n) hDζ (mvD_of_lt h1L); rw [h, hB1]
    have h := ziXUpM hR h1 hr hl' hB hA' hρ' hrs HB (Om (1 + 1)) hD2 le_rfl
    rw [hB2, ← ziXp_succ, ← ziXp_succ] at h
    rw [hBs]
    exact h
  · intro a D hb ha0 ha0' hdv hdv' s hs hsa hsT IH
    have hξ0 : (0 : Ordinal.{0}) < ξ := pos_iff_ne_zero.2 hlim.ne_bot
    have hXW : ziXp P0 ξ < Om ω := vkOmW.1.isPrincipal hP.lt (zdMul2_lt hξ2)
    have haW : a + leWe (ziXp P0 ξ) < Om ω :=
      vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 hXW).1
    have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 haW.le).1
    obtain ⟨d, hdD, hds, hdn⟩ := vbReach hl hX hs hsθ
    subst hds
    have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
      psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
    have had : a ≤ d := by
      by_contra hc; push Not at hc
      exact absurd (hdnx a hc) (not_lt.2 hsa)
    have hdae : d < a + leWe (ziXp P0 ξ) := by
      by_contra hc; push Not at hc
      exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
    set δ := d - a with hδdef
    have hdδ : d = a + δ := (Ordinal.add_sub_cancel_of_le had).symm
    have hδ : δ < leWe (ziXp P0 ξ) := Ry.rySub_lt had hdae
    -- a code `ζ < ξ` with `δ < W^{Y₃+Ω₂·ζ}`
    obtain ⟨ζ, hζc, hζξ, hδζ⟩ : ∃ ζ, GxCl (upsilon l) (ldAtR S l) ζ ∧ ζ < ξ ∧ δ < leWe (ziXp P0 ζ) := by
      rcases lt_or_ge δ (leWe (ziXp P0 0)) with h0 | h0
      · exact ⟨0, GxCl.zero hρSC.1, hξ0, h0⟩
      have hδ0 : δ ≠ 0 := ((leWe_pos _).trans_le h0).ne'
      set L := log ω δ with hLdef
      have hδH : δ ∈ cdHull S l := Ta.taSub_mem d hdD.1 a
      have hLH : L ∈ cdHull S l := leLog_mem hδH
      set E₁ := L / Om (1 + 1) with hE₁def
      have hE₁H : E₁ ∈ cdHull S l := by
        have h := (Vh.vhC_div L hLH (Om (1 + 1))).2.2 (mxOm2_mem _ _); rwa [gg_SC_eps ldOm2_SC] at h
      have hYL : Om (1 + 1) * P0 ≤ L := by
        rw [hLdef, ← Ordinal.opow_le_iff_le_log one_lt_omega0 hδ0]
        have h := h0; rw [ziXp_zero] at h; exact h
      have hYE : P0 ≤ E₁ := by rw [hE₁def, Ordinal.le_div hW0]; exact hYL
      have hLlt : L < Om (1 + 1) * ziXp P0 ξ := (lt_opow_iff_log_lt one_lt_omega0 hδ0).1 hδ
      have hE₁lt : E₁ < ziXp P0 ξ := (Ordinal.lt_mul_iff_div_lt hW0).1 hLlt
      set e₁ := E₁ - P0 with he₁def
      have he₁lt : e₁ < Om (1 + 1) * ξ := Ry.rySub_lt hYE hE₁lt
      set q := e₁ / Om (1 + 1) with hqdef
      have hqξ : q < ξ := (Ordinal.div_lt hW0).2 he₁lt
      have hqH : q ∈ cdHull S l := by
        have h := (Vh.vhC_div _ (Ta.taSub_mem E₁ hE₁H P0) (Om (1 + 1))).2.2 (mxOm2_mem _ _)
        rwa [gg_SC_eps ldOm2_SC] at h
      have hq1 : q + 1 < ξ := hlim.add_one_lt hqξ
      have hq12 : q + 1 < Om (1 + 1) := hq1.trans hξ2
      have hq1c : GxCl (upsilon l) (ldAtR S l) (q + 1) :=
        (ldHull_iff hl hX hq12).1 (CSet.succ_mem hqH)
      refine ⟨q + 1, hq1c, hq1, ?_⟩
      have he₁q : e₁ < Om (1 + 1) * (q + 1) := by
        have := Ordinal.lt_mul_succ_div e₁ hW0; rwa [Order.succ_eq_add_one] at this
      have hE₁q : E₁ < ziXp P0 (q + 1) := by
        have e1 : E₁ = P0 + e₁ := (Ordinal.add_sub_cancel_of_le hYE).symm
        unfold ziXp; rw [e1]; exact (add_lt_add_iff_left _).2 he₁q
      have hLq : L < Om (1 + 1) * ziXp P0 (q + 1) := by
        have hL1 : L < Om (1 + 1) * (E₁ + 1) := by
          have := Ordinal.lt_mul_succ_div L hW0; rwa [Order.succ_eq_add_one] at this
        exact hL1.trans_le (mul_le_mul_left' (Order.add_one_le_of_lt hE₁q) _)
      unfold leWe
      exact (lt_opow_iff_log_lt one_lt_omega0 hδ0).2 hLq
    have hζs : ζ < s₀ := hζξ.trans hξs
    obtain ⟨hDζ, -, -, -, -⟩ := IH₀ ζ hζc hζs
    obtain ⟨hDξ, -, -, -, -⟩ := IH₀ ξ hξc hξs
    have hBle : Bc.bcB S n ζ ≤ Bc.bcB S n ξ := ((mvB_lt_iff (k := n) hDζ hDξ).2 hζξ).le
    refine IHξ ζ hζξ hζc hζs (hζξ.trans hξT) a D hb ha0 ha0'
      ((leWe_dvd (ziXp_mono P0 hζξ.le)).trans hdv) ((leWe_dvd (ziXp_mono P0 hBle)).trans hdv') _ hs hsa ?_ IH
    refine hdnx _ ?_
    rw [hdδ]; exact (add_lt_add_iff_left a).2 hδζ

set_option maxHeartbeats 1000000 in
/-- **THE MOVES BELOW THE PLATEAU SHIFT `P + Ω₂·Ω₂`**: for a fixed prefix `(P, P̂)` (`Zd.ZdRS`), the moves below `P`
(`Zd.ZdBot`) give the moves below `P + Ω₂·Ω₂` over every base `a ≥ Ω₃` with `W^{P+Ω₂·Ω₂} ∣ a`,
`W^{P+Ω₂·Ω₂} ∣ B_n a`. -/
theorem ziBotPlat (HB0 : ZdBot S n l l' A' P0) : ZdBot S n l l' A' (ziXp P0 (Om (1 + 1))) := by
  intro a D hb hdv hdv' ha3 s hs hsa hsT IH
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hdvX : ∀ x, x ≤ Om (1 + 1) → leWe (ziXp P0 x) ∣ leWe (ziXp P0 (Om (1 + 1))) := fun x hx =>
    leWe_dvd (ziXp_mono P0 hx)
  have hXW : ziXp P0 (Om (1 + 1)) < Om ω := by
    have h22 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1)) := by
      rw [veblen_zero_apply, opow_add, gg_SC_eps ldOm2_SC]
    have hm : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < Om ω := by
      rw [h22]; exact vkOmW.1.2 0 vkOmW.1.1 _ (vkOmW.1.isPrincipal ldOm2_lt_OmW ldOm2_lt_OmW)
    unfold ziXp
    exact vkOmW.1.isPrincipal hP.lt hm
  have haW : a + leWe (ziXp P0 (Om (1 + 1))) < Om ω :=
    vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 hXW).1
  have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 haW.le).1
  obtain ⟨d, hdD, hds, hdn⟩ := vbReach hl hX hs hsθ
  subst hds
  have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
    psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
  have had : a ≤ d := by
    by_contra hc; push Not at hc
    exact absurd (hdnx a hc) (not_lt.2 hsa)
  have hdae : d < a + leWe (ziXp P0 (Om (1 + 1))) := by
    by_contra hc; push Not at hc
    exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
  set δ := d - a with hδdef
  have hdδ : d = a + δ := (Ordinal.add_sub_cancel_of_le had).symm
  have hδ : δ < leWe (ziXp P0 (Om (1 + 1))) := Ry.rySub_lt had hdae
  -- below `W^P`
  have hP0 : leWe P0 ∣ leWe (ziXp P0 (Om (1 + 1))) := by
    have h := hdvX 0 zero_le; rwa [ziXp_zero] at h
  rcases lt_or_ge δ (leWe P0) with h0 | h0
  · exact HB0 a D hb (hP0.trans hdv) (hP0.trans hdv') ha3 _ hs hsa
      (hdnx _ (by rw [hdδ]; exact (add_lt_add_iff_left a).2 h0)) IH
  -- the leading coefficient `q` of `δ`
  have hδ0 : δ ≠ 0 := ((leWe_pos _).trans_le h0).ne'
  have hδC : δ ∈ S.CSet d (S.psi d (Om (1 + 1))) := Ta.taSub_mem d hdn a
  have hδH : δ ∈ cdHull S l := Ta.taSub_mem d hdD.1 a
  set L := log ω δ with hLdef
  set E₁ := L / Om (1 + 1) with hE₁def
  have hYL : Om (1 + 1) * P0 ≤ L := by
    rw [hLdef, ← Ordinal.opow_le_iff_le_log one_lt_omega0 hδ0]; exact h0
  have hYE : P0 ≤ E₁ := by rw [hE₁def, Ordinal.le_div hW0]; exact hYL
  have hLlt : L < Om (1 + 1) * ziXp P0 (Om (1 + 1)) := (lt_opow_iff_log_lt one_lt_omega0 hδ0).1 hδ
  have hE₁lt : E₁ < ziXp P0 (Om (1 + 1)) := (Ordinal.lt_mul_iff_div_lt hW0).1 hLlt
  set e₁ := E₁ - P0 with he₁def
  have he₁lt : e₁ < Om (1 + 1) * Om (1 + 1) := Ry.rySub_lt hYE hE₁lt
  set q := e₁ / Om (1 + 1) with hqdef
  have hq2 : q < Om (1 + 1) := (Ordinal.div_lt hW0).2 he₁lt
  have hmem : ∀ {B : Set Ordinal.{0}}, (B = cdHull S l ∨ B = S.CSet d (S.psi d (Om (1 + 1)))) → δ ∈ B → q ∈ B := by
    rintro B (rfl | rfl) hδB
    · have hL := leLog_mem hδB
      have hE := (Vh.vhC_div L hL (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rw [gg_SC_eps ldOm2_SC] at hE
      have h := (Vh.vhC_div _ (Ta.taSub_mem E₁ hE P0) (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [gg_SC_eps ldOm2_SC] at h
    · have hL := leLog_mem hδB
      have hE := (Vh.vhC_div L hL (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rw [gg_SC_eps ldOm2_SC] at hE
      have h := (Vh.vhC_div _ (Ta.taSub_mem E₁ hE P0) (Om (1 + 1))).2.2 (mxOm2_mem _ _)
      rwa [gg_SC_eps ldOm2_SC] at h
  have hqH : q ∈ cdHull S l := hmem (Or.inl rfl) hδH
  have hqC : q ∈ S.CSet d (S.psi d (Om (1 + 1))) := hmem (Or.inr rfl) hδC
  have hqs : q < S.psi d (Om (1 + 1)) := lt_psi_of_mem hκ2 hqC hq2
  have hq1s : q + 1 < S.psi d (Om (1 + 1)) := (SC_psi hκ2 _).isSuccLimit.add_one_lt hqs
  have hq12 : q + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hq2
  have hq1c : GxCl (upsilon l) (ldAtR S l) (q + 1) := (ldHull_iff hl hX hq12).1 (CSet.succ_mem hqH)
  have hq1T : q + 1 < ziTC S P0 a := hq1s.trans hsT
  -- `δ < W^{P+Ω₂·(q+1)}`
  have hδq : δ < leWe (ziXp P0 (q + 1)) := by
    have he₁q : e₁ < Om (1 + 1) * (q + 1) := by
      have := Ordinal.lt_mul_succ_div e₁ hW0; rwa [Order.succ_eq_add_one] at this
    have hE₁q : E₁ < ziXp P0 (q + 1) := by
      have e1 : E₁ = P0 + e₁ := (Ordinal.add_sub_cancel_of_le hYE).symm
      unfold ziXp; rw [e1]; exact (add_lt_add_iff_left _).2 he₁q
    have hLq : L < Om (1 + 1) * ziXp P0 (q + 1) := by
      have hL1 : L < Om (1 + 1) * (E₁ + 1) := by
        have := Ordinal.lt_mul_succ_div L hW0; rwa [Order.succ_eq_add_one] at this
      exact hL1.trans_le (mul_le_mul_left' (Order.add_one_le_of_lt hE₁q) _)
    unfold leWe
    exact (lt_opow_iff_log_lt one_lt_omega0 hδ0).2 hLq
  obtain ⟨-, -, hBqP, -, -⟩ := IH (q + 1) hq1c hq1s
  have hBq2 : Bc.bcB S n (q + 1) < Om (1 + 1) := hBqP.trans Lj.ljThP_lt_Om2
  exact ziBotC hR h1 hr hl' hB hA' hρ' hP HB0 hb ha3 IH (q + 1) hq1c hq1s hq1T a D hb le_rfl le_rfl
    ((hdvX _ hq12.le).trans hdv) ((hdvX _ hBq2.le).trans hdv') _ hs hsa
    (hdnx _ (by rw [hdδ]; exact (add_lt_add_iff_left a).2 hδq)) IH

end Win

section WinY

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE MOVES BELOW `Y₃ + Ω₂·Ω₂`** (`Zd.ZdBot` at the shift `Y₃ + Ω₂·Ω₂`; the prefix `(Y₃, Y₂)`, `Zd.zdRS_Y3`,
`Zd.zdBot_chain` at `0`). -/
theorem ziBotW2 : ZdBot S n l l' A' (zdXr S (Om (1 + 1))) :=
  ziBotPlat hR h1 hr hl' hB hA' hρ' zdRS_Y3 (by
    have h := zdBot_chain hR h1 hr hl' hB hA' hρ' 0 (epsilon_pos 0).le
    rwa [zdXr_zero] at h)

/-- **THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·Ω₂}`**: above every base `a ≥ Ω₃` with a law at both ends, `Ω₃ ∣ a`,
`Ω₃ ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·Ω₂})` moves under IH(s) (contains `Zd.zdPsi3OffE0`,
`Zi.ziPsi3OffK`). -/
theorem ziPsi3OffW2 {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + leWe (zdXr S (Om (1 + 1)))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have h3 : leWe (zdXr S (Om (1 + 1))) ∣ Om (1 + 1 + 1) := by
    have hlt : zdXr S (Om (1 + 1)) < Om (1 + 1 + 1) := by
      have h3 : SC (Om (1 + 1 + 1 : Ordinal.{0})) := SC_Om (add_pos_of_right zero_lt_one _).ne'
      have h23 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
      have h22 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = veblen 0 (Om (1 + 1) + Om (1 + 1)) := by
        rw [veblen_zero_apply, opow_add, gg_SC_eps ldOm2_SC]
      have hm : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < Om (1 + 1 + 1) := by
        rw [h22]; exact h3.2 0 h3.1 _ (h3.isPrincipal h23 h23)
      unfold zdXr; exact h3.isPrincipal ugY_lt_Om3 hm
    have h := leWe_dvd hlt.le; rwa [Vn.vnWe_Om3] at h
  exact ziBotW2 hR h1 hr hl' hB hA' hρ' a D hb (h3.trans hd3) (h3.trans hd3') ha3 s hs hsa hsT IH

end WinY

end Googology.Trans.PoR.InaccPsi.R2.Zi
