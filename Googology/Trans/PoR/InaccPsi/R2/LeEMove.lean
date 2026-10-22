import Googology.Trans.PoR.InaccPsi.R2.LeEBlk

/-!
# The reading moves below `ψ_{Ω₂}(Ω₂^{Ω₂})`, and the road with the moves at the codes `ψ_{Ω₂}(Ω₂^{Ω₂}) ≤ m_λ ≤ θ·ω`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^e = Ω₂^e`, `Ω^x = Ω₁^x`, `F_{W} = ψ_{Ω₂}(Ω₂^{Ω₂})`
(`Le.leFWW`).

* `leB_mulOp2` (**`B_n(ω^K·x) = ω^{B_n K}·B_n x`** for every `x < K` in a class of `MvD` closed under `log` and the
  tail), `leB_We`, `leB_Oe` (`B_n(W^e) = W^{B_n e}`, `B_n(Ω^y) = Ω^{B_n y}`), `leB_FWW` (`B_n F_W = F_W`);
* `leOwnH_code`, `leOwnH_own`, `leOwnH_mem` (the exponent of an own argument is a code; an own argument is own in the
  closure sense, in the hull, below `A_{η_λ}`);
* `leDigMoveE` (**the digits and the exponents move**: if the codes below `ψ_{Ω₂}(β + c)` move, then
  `(B_n e, B_n c, B_n v)` is own at `λ'` over `B_n β`), `leAtMove_FWW` (**every atom below `F_W` moves** once the
  codes below it move), `leThMove_FWW` (**`MxThMove` at every long code `m_λ < F_W`**, no hypothesis);
* `LeThMoveU S` (a hypothesis name): the reading moves at the codes `F_W ≤ m_λ ≤ θ·ω`; `leThMoveT_of_U`,
  `leThMoveU_of_T` (equivalent to `Le.LeThMoveT` and to `Ld.LdThMoveS`), `leRoadU` (**the road**), `leThMoveU_of`
  (satisfiability: from `MxThMoveW`, `MxEQth` and `L(ω+1) ≤ ν_C`).

No new axiom.  New definition: the hypothesis name `LeThMoveU`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf

variable {S : InaccSeq.{0}}

/-! ## `B_n(ω^K·x) = ω^{B_n K}·B_n x` -/

/-- **`B_n(ω^K·x) = ω^{B_n K}·B_n(x)`** for every `x < K` in a class `P ⊆ MvD` closed under `log` and the tail. -/
theorem leB_mulOp2 {n : ℕ} {K : Ordinal.{0}} (hDK : MvD S K)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPK : ∀ x, P x → x < K) :
    ∀ x, P x → MvD S (ω ^ K * x) ∧ Bc.bcB S n (ω ^ K * x) = ω ^ Bc.bcB S n K * Bc.bcB S n x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  have hDx := hPD x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨by rw [mul_zero]; exact hDx, by rw [mul_zero, Bc.bcB_zero, mul_zero]⟩
  obtain ⟨hPg, hPr⟩ := hPdec x hx hx0
  set g := log ω x with hg
  have hlead : ω ^ g ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ g + (x - ω ^ g) = x := Ordinal.add_sub_cancel_of_le hlead
  have hDg := hPD _ hPg
  have hDr := hPD _ hPr
  obtain ⟨hDκr, hBκr⟩ := IH _ (leRest_lt hx0) hPr
  obtain ⟨hDog, hBog⟩ := ldB_opow (n := n) hDg
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDog hDr
  rw [hdec] at hBx
  obtain ⟨hDK', hBK'⟩ := ldB_opow (n := n) hDK
  obtain ⟨hDKg, hBKg⟩ := mvB_add (k := n) hDK hDg
  have hlt := hPK x hx
  rcases eq_or_ne g 0 with hg0 | hg0
  · have hl : ω ^ K * ω ^ g = ω ^ K := by rw [hg0, opow_zero, mul_one]
    have e : ω ^ K * x = ω ^ K + ω ^ K * (x - ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, hl]
    have hB1 : Bc.bcB S n (ω ^ g) = 1 := by rw [hg0, opow_zero, mwB_one]
    have hBx' : Bc.bcB S n x = 1 + Bc.bcB S n (x - ω ^ g) := by rw [hBx, hB1]
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDK' hDκr
    rw [e, hBx', mul_add, mul_one]
    exact ⟨hDs, by rw [hBs, hBK', hBκr]⟩
  · have hne : ω ^ (K + g) ≠ K + g := by
      intro h
      have hgK : g < K := (log_le_self ω x).trans_lt hlt
      have h1 : K + g < K * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
        exact (add_lt_add_iff_left K).2 hgK
      have h2 : K * 2 ≤ ω ^ (K + g) := by
        rw [opow_add]
        have h3 : (ω : Ordinal.{0}) ≤ ω ^ g := by
          have := (opow_le_opow_iff_right one_lt_omega0).2 (Order.one_le_iff_ne_zero.2 hg0)
          rwa [opow_one] at this
        calc K * 2 ≤ ω ^ K * 2 := mul_le_mul_left (right_le_opow K one_lt_omega0) 2
          _ ≤ ω ^ K * ω := mul_le_mul_right (natCast_lt_omega0 2).le _
          _ ≤ ω ^ K * ω ^ g := mul_le_mul_right h3 _
      rw [h] at h2
      exact absurd h1 (not_lt.2 h2)
    obtain ⟨hDl, hBl⟩ := mvB_opow (k := n) hDKg hne
    have e : ω ^ K * x = ω ^ (K + g) + ω ^ K * (x - ω ^ g) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, opow_add]
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDl hDκr
    rw [e, hBx, hBog, mul_add]
    refine ⟨hDs, ?_⟩
    rw [hBs, hBl, hBKg, hBκr, opow_add]

/-- `B_n(Ω₁·y) = Ω₁·B_n y` for a countable `y < c_{n+1}`. -/
theorem leB_mulOm1 {n : ℕ} {y : Ordinal.{0}} (hy1 : y < Om 1) (hyc : y < Bc.bcC S (n + 1)) :
    MvD S (Om 1 * y) ∧ Bc.bcB S n (Om 1 * y) = Om 1 * Bc.bcB S n y := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  exact ldB_mulK (n := n) Ph.ph_SC_Om1 hDO hBO (fun x => x < Om 1 ∧ x < Bc.bcC S (n + 1))
    (fun x hx => mvD_of_lt (hx.2.trans hLw))
    (fun x hx _ => ⟨⟨(log_le_self ω x).trans_lt hx.1, (log_le_self ω x).trans_lt hx.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hx.1, (Ordinal.sub_le_self _ _).trans_lt hx.2⟩⟩)
    (fun x hx => hx.1) y ⟨hy1, hyc⟩

/-- `B_n(Ω^y·x) = Ω^{B_n y}·B_n x` for countable `1 ≤ y`, `x` below `c_{n+1}`. -/
theorem leB_Oe {n : ℕ} {y x : Ordinal.{0}} (hy1 : y < Om 1) (hyc : y < Bc.bcC S (n + 1)) (hy0 : 1 ≤ y)
    (hx1 : x < Om 1) (hxc : x < Bc.bcC S (n + 1)) :
    MvD S (leOe y * x) ∧ Bc.bcB S n (leOe y * x) = leOe (Bc.bcB S n y) * Bc.bcB S n x := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDK, hBK⟩ := leB_mulOm1 (S := S) (n := n) hy1 hyc
  have h := leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => hz.1.trans_le (le_mul_left _ (Order.one_le_iff_pos.1 hy0))) x ⟨hx1, hxc⟩
  rw [hBK] at h
  exact h

/-- `B_n(Ω^y) = Ω^{B_n y}`. -/
theorem leB_Oe1 {n : ℕ} {y : Ordinal.{0}} (hy1 : y < Om 1) (hyc : y < Bc.bcC S (n + 1)) :
    MvD S (leOe y) ∧ Bc.bcB S n (leOe y) = leOe (Bc.bcB S n y) := by
  obtain ⟨hDK, hBK⟩ := leB_mulOm1 (S := S) (n := n) hy1 hyc
  obtain ⟨hD, hB⟩ := ldB_opow (n := n) hDK
  unfold leOe; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-- `B_n(Ω₂·e) = Ω₂·B_n e` and `B_n(W^e·γ) = W^{B_n e}·B_n γ` for codes in a class `P` of `MvD` closed under `log` and
the tail. -/
theorem leB_We {n : ℕ} (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1))
    {e γ : Ordinal.{0}} (he : P e) (he1 : 1 ≤ e) (hγ : P γ) :
    MvD S (leWe e) ∧ Bc.bcB S n (leWe e) = leWe (Bc.bcB S n e) ∧
      MvD S (leWe e * γ) ∧ Bc.bcB S n (leWe e * γ) = leWe (Bc.bcB S n e) * Bc.bcB S n γ := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDK, hBK⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 P hPD hPdec hPW e he
  obtain ⟨hD, hB⟩ := ldB_opow (n := n) hDK
  have h := leB_mulOp2 (n := n) hDK P hPD hPdec
    (fun z hz => (hPW z hz).trans_le (le_mul_left _ (Order.one_le_iff_pos.1 he1))) γ hγ
  rw [hBK] at h
  refine ⟨hD, ?_, h⟩
  unfold leWe; rw [hB, hBK]

/-! ## Own arguments -/

section Own

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- The exponent of an own argument is a code. -/
theorem leOwnH_code {e β c v : Ordinal.{0}} (h : LeOwnH S l e β c v) (heW : e < Om (1 + 1)) :
    GxCl (upsilon l) (ldAtR S l) e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  cases h with
  | zero => exact GxCl.zero hρSC.1
  | one => exact GxCl.small (gg_one_lt_of_SC hρSC)
  | succ hec _ _ _ _ _ _ =>
    exact (ldHull_iff hl hX heW).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one _).trans heW)).2 hec))

/-- An own argument is own in the closure sense. -/
theorem leOwnH_own {e β c v : Ordinal.{0}} (h : LeOwnH S l e β c v) :
    LeBaseE S l e β → β + c ∈ S.CSet (β + c) (S.psi (β + c) (Om (1 + 1))) := by
  induction h with
  | zero => intro hb; rw [add_zero]; exact hb.2.2.2.1 0 zero_le |> fun h => by rwa [add_zero] at h
  | @one β c hc hcF =>
    intro hb
    obtain ⟨hβd, -, -, hβown, -⟩ := hb
    rw [leWe_one] at hβd hβown
    exact ldOwn hβown hβd hcF
  | @succ e e' β γ c' v hec he1 hγc hγ0 hγT he'e _ ih =>
    intro hb
    have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
    rw [← add_assoc]
    exact ih (leBaseE_mono he'e (leBaseE_sub hl hX hb hec ((ldHull_iff hl hX hγW).2 hγc) hγT))

/-- An own argument is in the hull and below `A_{η_λ}`. -/
theorem leOwnH_mem {e β c v : Ordinal.{0}} (h : LeOwnH S l e β c v) :
    LeBaseE S l e β → β + c ∈ cdHull S l ∧ β + c < ConjT.Aη S (cdEta S l) := by
  induction h with
  | zero =>
    intro hb; rw [add_zero]
    exact ⟨hb.2.1, lt_of_le_of_lt le_self_add hb.2.2.1⟩
  | @one β c hc hcF =>
    intro hb
    obtain ⟨-, hβH, hβA, -, -⟩ := hb
    rw [leWe_one] at hβA
    have hc2 : c < Om (1 + 1) := hcF.trans (ldTop_lt_Om2 β)
    exact ⟨CSet.add_mem hβH ((ldHull_iff hl hX hc2).2 hc), ((add_lt_add_iff_left β).2 hc2).trans hβA⟩
  | @succ e e' β γ c' v hec he1 hγc hγ0 hγT he'e _ ih =>
    intro hb
    have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
    rw [← add_assoc]
    exact ih (leBaseE_mono he'e (leBaseE_sub hl hX hb hec ((ldHull_iff hl hX hγW).2 hγc) hγT))

end Own

theorem leB_le {n : ℕ} {x y : Ordinal.{0}} (hx : MvD S x) (hy : MvD S y) (h : x ≤ y) :
    Bc.bcB S n x ≤ Bc.bcB S n y := by
  rcases h.lt_or_eq with h | rfl
  · exact ((mvB_lt_iff (k := n) hx hy).2 h).le
  · exact le_rfl

/-! ## The digits and the exponents move -/

/-- **The digits and the exponents move**: if the codes below `ψ_{Ω₂}(β + c)` move, then `(B_n e, B_n c, B_n v)` is own
at `λ'` over `B_n β`. -/
theorem leDigMoveE {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    {e β c v : Ordinal.{0}} (h : LeOwnH S l e β c v) :
    LeBaseE S l e β → MvD S β →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + c) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S e ∧ MvD S c ∧ MvD S (β + c) ∧ Bc.bcB S n (β + c) = Bc.bcB S n β + Bc.bcB S n c ∧ MvD S v ∧
      LeOwnH S l' (Bc.bcB S n e) (Bc.bcB S n β) (Bc.bcB S n c) (Bc.bcB S n v) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  induction h with
  | zero =>
    intro _ hDβ _
    rw [add_zero, Bc.bcB_zero, add_zero]
    exact ⟨hD0, hD0, hDβ, rfl, hD0, LeOwnH.zero⟩
  | @one β c hc hcF =>
    intro hb hDβ IH
    obtain ⟨hβd, -, -, hβown, -⟩ := hb
    rw [leWe_one] at hβd hβown
    obtain ⟨hDc, hBc, hΘX, hΘe⟩ := IH c hc (ldTop_gt hβown hβd hcF)
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDc
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    obtain ⟨hDβW, hBβW⟩ := mvB_add (k := n) hDβ hD2
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDβW (CSet.add_mem (hβown _ le_rfl) (mxOm2_mem _ _))
    have hBcF : Bc.bcB S n c < ldTop S (Bc.bcB S n β) := by
      have h := (mvB_lt_iff (k := n) hDc hDT).2 hcF
      unfold ldTop at h ⊢
      rwa [hBT, hBβW, hB2] at h
    refine ⟨hD1, hDc, hDs, hBs, mvD_of_lt (hΘX.trans hLw), ?_⟩
    rw [mwB_one, ← hΘe]
    exact LeOwnH.one hBc hBcF
  | @succ e e' β γ c' v hec he1 hγc hγ0 hγT he'e _ ih =>
    intro hb hDβ IH
    have hb' := hb
    obtain ⟨hβd, -, -, hβown, hexpA⟩ := hb
    have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
    have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
    have he1W : e + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt heW
    have he1c : GxCl (upsilon l) (ldAtR S l) (e + 1) :=
      (ldHull_iff hl hX he1W).1 (CSet.succ_mem ((ldHull_iff hl hX heW).2 hec))
    have hexp1 : e + 1 < S.psi (β + leWe (e + 1)) (Om (1 + 1)) := hexpA (e + 1) he1c le_rfl
    have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
    have hγ1 : 1 ≤ γ := Order.one_le_iff_ne_zero.2 hγ0
    have hγs : γ < S.psi (β + leWe e * γ) (Om (1 + 1)) := leTe_gt hβown hexp hβd hγT
    have hle1 : S.psi (β + leWe e * γ) (Om (1 + 1)) ≤ S.psi (β + (leWe e * γ + c')) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) (by rw [← add_assoc]; exact le_self_add)).1
    have hle2 : S.psi (β + leWe e) (Om (1 + 1)) ≤ S.psi (β + leWe e * γ) (Om (1 + 1)) := by
      refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
      calc leWe e = leWe e * 1 := (mul_one _).symm
        _ ≤ leWe e * γ := leMulWe_mono hγ1
    have hes : e < S.psi (β + (leWe e * γ + c')) (Om (1 + 1)) := (hexp.trans_le hle2).trans_le hle1
    have he1s : e + 1 < S.psi (β + (leWe e * γ + c')) (Om (1 + 1)) :=
      (SC_psi (InR_Om_succ 1) _).isSuccLimit.succ_lt hes
    obtain ⟨hDe, hBec, hΘeX, hΘe⟩ := IH e hec hes
    obtain ⟨hDγ, hBγc, hΘγX, hΘγ⟩ := IH γ hγc (hγs.trans_le hle1)
    -- the class of the codes below `ψ_{Ω₂}(β + c)`
    set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
      x < S.psi (β + (leWe e * γ + c')) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
    have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
      obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
      have hlx : log ω x ≤ x := log_le_self ω x
      have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
      exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
        ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
          (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
    obtain ⟨-, -, hDμγ, hBμγ⟩ := leB_We (n := n) P hPD hPdec hPW ⟨hec, hes, heW⟩ he1
      ⟨hγc, hγs.trans_le hle1, hγW⟩
    obtain ⟨hDW1, hBW1, -, -⟩ := leB_We (n := n) P hPD hPdec hPW ⟨he1c, he1s, he1W⟩
      (le_add_self) (⟨hγc, hγs.trans_le hle1, hγW⟩ : P γ)
    obtain ⟨hDβ', hBβ'⟩ := mvB_add (k := n) hDβ hDμγ
    have hb2 := leBaseE_mono he'e (leBaseE_sub hl hX hb' hec ((ldHull_iff hl hX hγW).2 hγc) hγT)
    obtain ⟨hDe', hDc', -, -, hDv, hown'⟩ := ih hb2 hDβ' (fun x hx hxs => IH x hx (by
      rw [← add_assoc]; exact hxs))
    rw [hBβ', hBμγ] at hown'
    obtain ⟨hDc, hBc⟩ := mvB_add (k := n) hDμγ hDc'
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDc
    obtain ⟨hDe1, hBe1⟩ := mvB_add (k := n) hDe hD1
    rw [mwB_one] at hBe1
    -- `B_n(T_{e+1}(β)) = T_{B_n e + 1}(B_n β)`
    obtain ⟨hDβW, hBβW⟩ := mvB_add (k := n) hDβ hDW1
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDβW
      (CSet.add_mem (hβown _ le_rfl) (leWe_mem (CSet.of_lt hexp1)))
    have hBγT : Bc.bcB S n γ < leTe S (Bc.bcB S n e + 1) (Bc.bcB S n β) := by
      have h := (mvB_lt_iff (k := n) hDγ hDT).2 hγT
      unfold leTe at h ⊢
      rwa [hBT, hBβW, hBW1, hBe1] at h
    -- the values
    have hΘeO : gxTh (upsilon l) (ldAtR S l) e < Om 1 := hΘeX.trans hc1
    have hΘγO : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := hΘγX.trans hc1
    have hΘe1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) e := by rw [← hΘ1]; exact gxTh_mono he1
    obtain ⟨hDOΘ, hBOΘ⟩ := leB_Oe (S := S) (n := n) hΘeO hΘeX hΘe1 hΘγO hΘγX
    obtain ⟨hDsum, hBsum⟩ := mvB_add (k := n) hDOΘ hDv
    have hBe1' : 1 ≤ Bc.bcB S n e := by rw [← mwB_one (S := S) n]; exact leB_le hD1 hDe he1
    have hBγ0 : Bc.bcB S n γ ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDγ).2 (pos_iff_ne_zero.2 hγ0)
      rw [Bc.bcB_zero] at this; exact this.ne'
    have hBe'e : Bc.bcB S n e' ≤ Bc.bcB S n e := leB_le hDe' hDe he'e
    refine ⟨hDe1, hDc, hDs, hBs, hDsum, ?_⟩
    rw [hBe1, hBc, hBμγ, hBsum, hBOΘ, ← hΘe, ← hΘγ]
    exact LeOwnH.succ hBec hBe1' hBγc hBγ0 hBγT hBe'e hown'

/-! ## The atoms below `ψ_{Ω₂}(Ω₂^{Ω₂})` move -/

theorem leWW_lt_OmW : leWe (Om (1 + 1 : Ordinal.{0})) < Om ω :=
  ldOpow_lt_SC (SC_Om omega0_ne_zero) ldOm2sq_lt_OmW

theorem leFWW_lt_th : leFWW S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) leWW_lt_OmW (leWe_mem (mxOm2_mem _ _))

theorem leOm1_lt_FWW : Om (1 : Ordinal.{0}) < leFWW S := (psiS_bounds (S := S) _ 1).1

theorem leFw_le_FWW : leFw S ≤ leFWW S := by
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  unfold leWe
  exact opow_le_opow_right omega0_pos (mul_le_mul_right (Lw.lw_omega_lt_SC ldOm2_SC).le _)

/-- `B_n(ψ_{Ω₂}(Ω₂^{Ω₂})) = ψ_{Ω₂}(Ω₂^{Ω₂})`. -/
theorem leB_FWW {n : ℕ} : MvD S (leFWW S) ∧ Bc.bcB S n (leFWW S) = leFWW S := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  have hne : ω ^ (Om (1 + 1 : Ordinal.{0}) + Om (1 + 1)) ≠ Om (1 + 1) + Om (1 + 1) := by
    intro h
    have h1 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) < Om (1 + 1) * ω := by
      have e2 : Om (1 + 1 : Ordinal.{0}) + Om (1 + 1) = Om (1 + 1) * 2 := by
        rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
      rw [e2]; exact (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (by exact_mod_cast natCast_lt_omega0 2)
    have h2 : Om (1 + 1 : Ordinal.{0}) * ω ≤ ω ^ (Om (1 + 1) + Om (1 + 1)) := by
      rw [ldW2_eq]; exact opow_le_opow_right omega0_pos (add_le_add_right (Order.one_le_iff_ne_zero.2
        ldOm2_SC.1.ne') _)
    rw [h] at h2
    exact absurd h1 (not_lt.2 h2)
  obtain ⟨hDo, hBo⟩ := mvB_opow (k := n) hDs hne
  have hWW : MvD S (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) ∧
      Bc.bcB S n (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
    rw [ldOm2sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB2]⟩
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hWW.1
  rw [hWW.2] at hBW
  obtain ⟨hDF, hBF⟩ := mxB_atom (n := n) hDW (leWe_mem (mxOm2_mem _ _))
  refine ⟨hDF, ?_⟩
  unfold leFWW leWe; rw [hBF, hBW]

/-- **Every atom below `ψ_{Ω₂}(Ω₂^{Ω₂})` moves** once the codes below it move. -/
theorem leAtMove_FWW {n : ℕ} {l l' A A' ηx ηx' : Ordinal.{0}} (hl : IsRestartIdx l) (hl' : IsRestartIdx l')
    (hX : upsilon l < Pv S ηx) (hX' : upsilon l' < Pv S ηx')
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ : S.psi A (Om 1) = upsilon l) (hρ' : S.psi A' (Om 1) = upsilon l')
    (hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1))
    (hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1)) :
    ∀ s ∈ ldAtR S l, s < leFWW S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < leFWW S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < leFWW S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  intro s hs hsF IHx
  obtain ⟨e, c, v, heF, hown, rfl, hth, hownv, hv, -⟩ := leTh_FWW hl hX hA hρ s hs hsF
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hb0 := leBaseE_zero (S := S) l heF
  obtain ⟨hDe, hDc, -, -, hDv, hBown⟩ := leDigMoveE (n := n) (l' := l') hl hX hown hb0 hD0
    (fun x hx hxs => by
      rw [zero_add] at hxs
      obtain ⟨h1, h2, -, h4, h5⟩ := IHx x hx hxs
      exact ⟨h1, h2, h4, h5⟩)
  rw [Bc.bcB_zero] at hBown
  have hownc : c ∈ S.CSet c (S.psi c (Om (1 + 1))) := by
    have := leOwnH_own hl hX hown hb0; rwa [zero_add] at this
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDc hownc
  obtain ⟨hDF, hBF⟩ := leB_FWW (S := S) (n := n)
  have hBeF : Bc.bcB S n e < leFWW S := by
    have := (mvB_lt_iff (k := n) hDe hDF).2 heF; rwa [hBF] at this
  have hb0' := leBaseE_zero (S := S) l' hBeF
  have hownB : Bc.bcB S n c ∈ S.CSet (Bc.bcB S n c) (S.psi (Bc.bcB S n c) (Om (1 + 1))) := by
    have := leOwnH_own hl' hX' hBown hb0'; rwa [zero_add] at this
  obtain ⟨hBH, hBA⟩ := leOwnH_mem hl' hX' hBown hb0'
  rw [zero_add] at hBH hBA
  have hA'1 : A' + 1 ∈ S.CSet (A' + 1) (S.psi (A' + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA') (CSet.one_mem _ _)
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  obtain ⟨hth', -, -, hBcW⟩ := leOwnRead hl' hX' hBown (A' + 1) hb0' hA'1 (ldBlk_zero hA' hρ')
  rw [zero_add] at hth'
  have hBW : Bc.bcB S n c < leWe (Om (1 + 1)) :=
    hBcW.trans (leWe_lt (hBeF.trans leFWW_lt_Om2))
  -- `d = 1 + v ≤ θ`
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hΘe1 : gxTh (upsilon l) (ldAtR S l) e < Om 1 := by
    rcases eq_or_ne e 0 with rfl | he0
    · rw [gxTh_zero]; exact Om_pos one_ne_zero
    have hec := leOwnH_code hl hX hown (heF.trans leFWW_lt_Om2)
    have hT := leTopE hl hX e hec (Order.one_le_iff_ne_zero.2 he0) 0 (A + 1) hb0 hA1 (ldBlk_zero hA hρ)
    have heT : e < leTe S e 0 := by unfold leTe; rw [zero_add]; exact leFWW_gt heF
    refine (gxTh_lt hec heT).trans ?_
    rw [hT]; exact psi_lt Low.InR_Om_one _
  have hvG : v < S.psi 0 (Om (1 + 1)) := hv.trans (leOe_lt_SC hG1 hΩG1 (hΘe1.trans hΩG1)).1
  have hdθ : 1 + v ≤ ConjT.th S :=
    (hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) hvG).le.trans
      (psi_mono (S := S) (InR_Om_succ 1) zero_le).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDd, hBd⟩ := mvB_add (k := n) hD1 hDv
  have hownd : A + (1 + v) ∈ S.CSet (A + (1 + v)) (S.psi (A + (1 + v)) (Om 1)) := by
    rw [← add_assoc]; exact hownv
  refine ⟨hDs, ?_, ?_, ?_, ?_⟩
  · rw [hBs]; exact ⟨_, hBH, hBA, rfl⟩
  · rw [hBs]
    exact psi_lt_psi_of_mem (InR_Om_succ 1) hBW ((psi_mono (S := S) (InR_Om_succ 1) hBW.le).2 hownB)
  · rw [hth, add_assoc]; exact hbX _ hdθ
  · rw [hBs, hth', hth, add_assoc A, hBψ _ hDd hownd hdθ, hBd, mwB_one, add_assoc]

/-- **`MxThMove` at every long code `m_λ < ψ_{Ω₂}(Ω₂^{Ω₂})`.** -/
theorem leThMove_FWW {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (he : ggGam < cdExp (cdEta S l)) (hK : cdCode S l < leFWW S) :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) := by
    rw [← Lw.lw_L_eq S]; exact h2
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set η := cdEta S l with hη_def
  set A := ConjT.Aη S η with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hAL : A < S.Lam := (sfA_lt (S := S) (n := n) (hpv ▸ h2)).2
  have hown : A ∈ S.CSet A (S.psi A (Om 1)) := sfOwn hg hAL
  set e := cdExp η with he_def
  have hωe : (ω : Ordinal.{0}) ≤ e := (Lw.lw_omega_lt_SC ggGam_spec.1).le.trans he.le
  have hWA : Om ω ≤ A := le_self_add
  have he2 : e < Om (1 + 1) := by
    by_contra h
    have hc : cdCode S l = cdPi S η := by
      show cdCodeOf S η = _; unfold cdCodeOf; rw [if_neg h]
    have hle : leFWW S ≤ cdPi S η := (psi_mono (S := S) (InR_Om_succ 1) (leWW_lt_OmW.le.trans hWA)).1
    exact absurd (hc ▸ hK) (not_lt.2 hle)
  have hcode : cdCode S l = e := by
    show cdCodeOf S η = e
    rw [cdCodeOf_of_lt he2]; unfold cdOff; rw [if_neg (not_lt.2 hωe)]
  have heF : e < leFWW S := hcode ▸ hK
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmemH : e ∈ cdHull S l := by unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  have hge : GxCl (upsilon l) (ldAtR S l) e := (ldHull_iff hl hX he2).1 hmemH
  have hmem0 : e ∈ ⋃ a, S.CSet a 0 := by
    refine Set.mem_iUnion.2 ⟨A, mxHull_sub0 ?_⟩
    have : e ∈ S.CSet A (upsilon l) := hmemH
    rwa [← hρA] at this
  obtain ⟨η', -, hBη', hη', hexp'⟩ := mvExp_move hl.1 h1 h2 (heF.trans leFWW_lt_th) hmem0
  have hl'eq : l' = Bt.iota S η' := Tp.tpUps_inj (hB.symm.trans hBη')
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hsucc := mxUps_succ hl hX
  have hbX : ∀ d, d ≤ ConjT.th S → S.psi (A + d) (Om 1) < Bc.bcC S (n + 1) := by
    intro d hd
    have h3 : S.psi (A + d) (Om 1) ≤ upsilon (l + 1) := by
      rw [hsucc]; exact (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left A).2 hd)).1
    exact (h3.trans_lt hu1).trans hδr
  have hρ0 : (0 : Ordinal.{0}) < Pv S η := hpv ▸ mvUps_pos hl
  obtain ⟨A', hA', hBP, -⟩ := mxB_psi_add (n := n) hg (hpv ▸ h1.le) (by rw [add_zero]; exact hρ0)
    (by rw [add_zero]; show Pv S η < Bc.bcC S (n + 1); rw [hpv]; exact h2)
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hBψ : ∀ d, MvD S d → A + d ∈ S.CSet (A + d) (S.psi (A + d) (Om 1)) → d ≤ ConjT.th S →
      Bc.bcB S n (S.psi (A + d) (Om 1)) = S.psi (A' + Bc.bcB S n d) (Om 1) := by
    intro d hDd hownd hdθ
    obtain ⟨A'', hA'', hBP'', hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDd hownd (hbX d hdθ)
    have : A'' = A' := mxPsi_inj hA'' hA' (by rw [← hBP'', hBP])
    rw [hBd, this]
  have hρSC : SC (upsilon l) := hρA ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρA ▸ psi_lt Low.InR_Om_one A
  have hρ'SC : SC (upsilon l') := hρA' ▸ SC_psi Low.InR_Om_one A'
  have hρ'1 : upsilon l' < Om 1 := hρA' ▸ psi_lt Low.InR_Om_one A'
  obtain ⟨hDe, -, hBeF, -, hEq⟩ := ldGxStepRec (n := n) hρSC hρ1 hρ'SC hρ'1 (ldAt_GxAt _ _)
    (ldAt_GxAt _ _) hB (Lw.lw_L_SC S _) h2 hLw leFWW_SC leOm1_lt_FWW.le
    (leAtMove_FWW hl hl' hX hX' hown hA' hρA hρA' hbX hBψ) e hge heF
  have hΩe : Om (1 : Ordinal.{0}) < Bc.bcB S n e := by
    obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
    have h3 := (mvB_lt_iff (k := n) hDO hDe).2 (ggGam_spec.2.trans he)
    rwa [hBO] at h3
  have hωBe : (ω : Ordinal.{0}) ≤ Bc.bcB S n e := (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le.trans hΩe.le
  have hcode' : cdCode S l' = Bc.bcB S n e := by
    rw [hl'eq]
    show cdCodeOf S (cdEta S (Bt.iota S η')) = _
    rw [hη', cdCodeOf_of_lt (hexp' ▸ hBeF.trans leFWW_lt_Om2), hexp']
    unfold cdOff; rw [if_neg (not_lt.2 hωBe)]
  rw [hcode, hcode', ldTheta hl hX he2.le, ldTheta hl' hX' (hBeF.trans leFWW_lt_Om2).le]
  exact hEq.symm

/-! ## The remaining reading moves and the road -/

/-- **The reading moves at the codes `ψ_{Ω₂}(Ω₂^{Ω₂}) ≤ m_λ ≤ θ·ω`.** -/
def LeThMoveU (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l ≤ ConjT.th S * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **`LeThMoveU` gives `LeThMoveT`** (and so `Ld.LdThMoveS`). -/
theorem leThMoveT_of_U (h : LeThMoveU S) : LeThMoveT S := by
  intro n l l' hR h1 hr hl' hB hm hF hw
  by_cases hK : cdCode S l < leFWW S
  · exact leThMove_FWW hR h1 hr hl' hB
      (ldGam_lt_Fw.trans_le (ldFw_le_G2.trans (leG2_le_Fw.trans (hF.trans (cdCodeOf_le_exp S _))))) hK
  · exact h n l l' hR h1 hr hl' hB hm (not_lt.1 hK) hw

/-- `LeThMoveT` gives `LeThMoveU` (so `LeThMoveU` is not the stronger hypothesis). -/
theorem leThMoveU_of_T (h : LeThMoveT S) : LeThMoveU S :=
  fun n l l' hR h1 hr hl' hB hm hF hw => h n l l' hR h1 hr hl' hB hm (leFw_le_FWW.trans hF) hw

/-- **The road with `MxLhTopG`, `L(ω+1) ≤ ν_C → LeThMoveU` and `L(ω+1) ≤ ν_C → LdEQhi`.** -/
theorem leRoadU (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LeThMoveU S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → LdEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  leRoadT hU hO hL hV hN hlh (fun hν => leThMoveT_of_U (hth hν)) hhi

/-- **Satisfiability**: `LeThMoveU` follows from `MxThMoveW` and `MxEQth` (given `L(ω+1) ≤ ν_C`), so the hypotheses of
`leRoadU` follow from those of `Mx.mxRoad5`. -/
theorem leThMoveU_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : MxThMoveW S) (hE : MxEQth S) : LeThMoveU S :=
  leThMoveU_of_T (leThMoveT_of hν hW hE)

end Googology.Trans.PoR.InaccPsi.R2.Le
