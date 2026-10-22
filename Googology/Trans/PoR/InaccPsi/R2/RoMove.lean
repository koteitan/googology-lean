import Googology.Trans.PoR.InaccPsi.R2.RoCls

/-!
# The own arguments over a family of shifts move under the base change `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`.
`RoShB S X X̂` (**the shift is fixed by every `B_n`**): `X̂ ≠ 0`, `B_n(Ω₂·X) = Ω₂·X`, `B_n(Ω₁·X̂) = Ω₁·X̂` (all in the
domain `MvD`); e.g. `X = Ω₂·k`, `X̂ = Ω₁·k`.

* `roB_We` (**`B_n(W^{X+e}·γ) = W^{X+B_n e}·B_n γ`**), `roB_Oe` (**`B_n(Ω^{X̂+y}·x) = Ω^{X̂+B_n y}·B_n x`**),
  `roB_WeW` (`B_n(W^{X'+W}) = W^{X'+W}` for `X' = 0` or a fixed shift);
* `roDigMove` (**the digits and the exponents move**: if the codes below `ψ_{Ω₂}(β + c)` move, then
  `(X, B_n e, B_n c, B_n v)` is own at `λ'` over `B_n β`; the same family of shifts at `λ'`).

No new axiom.  New definition: `RoShB`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ro

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

/-- **The shift is fixed by every base change.** -/
def RoShB (S : InaccSeq.{0}) (X Xh : Ordinal.{0}) : Prop :=
  Xh ≠ 0 ∧ ∀ n : ℕ, MvD S (Om (1 + 1) * X) ∧ Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * X ∧
    MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * Xh

/-- **`B_n(W^{X+e}·γ) = W^{X+B_n e}·B_n γ`.** -/
theorem roB_We {n : ℕ} {X Xh : Ordinal.{0}} (hX0 : X ≠ 0) (hB : RoShB S X Xh)
    (P : Ordinal.{0} → Prop) (hPD : ∀ x, P x → MvD S x)
    (hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x)) (hPW : ∀ x, P x → x < Om (1 + 1))
    {e γ : Ordinal.{0}} (he : P e) (hγ : P γ) :
    MvD S (leWe (X + e)) ∧ Bc.bcB S n (leWe (X + e)) = leWe (X + Bc.bcB S n e) ∧
      MvD S (leWe (X + e) * γ) ∧ Bc.bcB S n (leWe (X + e) * γ) = leWe (X + Bc.bcB S n e) * Bc.bcB S n γ := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDWe, hBWe⟩ := ldB_mulK (n := n) ldOm2_SC hD2 hB2 P hPD hPdec hPW e he
  obtain ⟨hDWX, hBWX, -, -⟩ := hB.2 n
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDWX hDWe
  rw [hBWX, hBWe] at hBK
  obtain ⟨hD, hBo⟩ := ldB_opow (n := n) hDK
  have hWX : Om (1 + 1) ≤ Om (1 + 1) * X := le_mul_left _ (pos_iff_ne_zero.2 hX0)
  have h := leB_mulOp2 (n := n) hDK P hPD hPdec
    (fun z hz => ((hPW z hz).trans_le hWX).trans_le le_self_add) γ hγ
  rw [hBK] at h hBo
  unfold leWe
  rw [mul_add, mul_add]
  exact ⟨hD, hBo, h⟩

/-- **`B_n(Ω^{X̂+y}·x) = Ω^{X̂+B_n y}·B_n x`** for countable `y`, `x` below `c_{n+1}`. -/
theorem roB_Oe {n : ℕ} {X Xh : Ordinal.{0}} (hB : RoShB S X Xh) {y x : Ordinal.{0}} (hy1 : y < Om 1)
    (hyc : y < Bc.bcC S (n + 1)) (hx1 : x < Om 1) (hxc : x < Bc.bcC S (n + 1)) :
    MvD S (leOe (Xh + y) * x) ∧ Bc.bcB S n (leOe (Xh + y) * x) = leOe (Xh + Bc.bcB S n y) * Bc.bcB S n x := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDy, hBy⟩ := leB_mulOm1 (S := S) (n := n) hy1 hyc
  obtain ⟨-, -, hDX, hBX⟩ := hB.2 n
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDX hDy
  rw [hBX, hBy] at hBK
  have hΩX : Om (1 : Ordinal.{0}) ≤ Om 1 * Xh := le_mul_left _ (pos_iff_ne_zero.2 hB.1)
  have h := leB_mulOp2 (n := n) hDK (fun z => z < Om 1 ∧ z < Bc.bcC S (n + 1))
    (fun z hz => mvD_of_lt (hz.2.trans hLw))
    (fun z hz _ => ⟨⟨(log_le_self ω z).trans_lt hz.1, (log_le_self ω z).trans_lt hz.2⟩,
      ⟨(Ordinal.sub_le_self _ _).trans_lt hz.1, (Ordinal.sub_le_self _ _).trans_lt hz.2⟩⟩)
    (fun z hz => (hz.1.trans_le hΩX).trans_le le_self_add) x ⟨hx1, hxc⟩
  rw [hBK] at h
  unfold leOe
  rw [mul_add, mul_add]
  exact h

/-- `B_n(Ω₂·Ω₂) = Ω₂·Ω₂`. -/
theorem roB_W2 {n : ℕ} : MvD S (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) ∧
    Bc.bcB S n (Om (1 + 1 : Ordinal.{0}) * Om (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hD2 hD2
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDs
  rw [ldOm2sq_eq]; exact ⟨hDo, by rw [hBo, hBs, hB2]⟩

/-- `B_n(W^{X'+W}) = W^{X'+W}` for `X' = 0` or a fixed shift. -/
theorem roB_WeW {n : ℕ} {X' : Ordinal.{0}} (h : X' = 0 ∨ ∃ Xh', RoShB S X' Xh') :
    MvD S (leWe (X' + Om (1 + 1))) ∧ Bc.bcB S n (leWe (X' + Om (1 + 1))) = leWe (X' + Om (1 + 1)) := by
  rcases h with rfl | ⟨Xh', hB⟩
  · rw [zero_add]; exact rnB_WW
  obtain ⟨hDX, hBX, -, -⟩ := hB.2 n
  obtain ⟨hDW, hBW⟩ := roB_W2 (S := S) (n := n)
  obtain ⟨hDK, hBK⟩ := mvB_add (k := n) hDX hDW
  rw [hBX, hBW] at hBK
  obtain ⟨hD, hBo⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBo
  unfold leWe; rw [mul_add]; exact ⟨hD, hBo⟩

section Main

variable {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Sh : Ordinal.{0} → Ordinal.{0} → Prop}
  (hSh : ∀ X Xh, Sh X Xh → RoSh S X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e)
  (hShB : ∀ X Xh, Sh X Xh → RoShB S X Xh)

include hl hX hSh hShB

/-- **The digits and the exponents move**: if the codes below `ψ_{Ω₂}(β + c)` move, then `(X, B_n e, B_n c, B_n v)`
is own at `λ'` over `B_n β`. -/
theorem roDigMove {X e β c v : Ordinal.{0}} (h : RoOwn S l Sh X e β c v) :
    RoBaseE S l X e β → MvD S β →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + c) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S e ∧ MvD S c ∧ MvD S (β + c) ∧ Bc.bcB S n (β + c) = Bc.bcB S n β + Bc.bcB S n c ∧ MvD S v ∧
      RoOwn S l' Sh X (Bc.bcB S n e) (Bc.bcB S n β) (Bc.bcB S n c) (Bc.bcB S n v) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  induction h with
  | @low e β c v hown =>
    intro hb hDβ IH
    have hbE : LeBaseE S l e β := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb
      simp only [zero_add] at h1 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨hDe, hDc, hDs, hBs, hDv, hown'⟩ := leDigMoveE (n := n) (l' := l') hl hX hown hbE hDβ IH
    exact ⟨hDe, hDc, hDs, hBs, hDv, RoOwn.low hown'⟩
  | @succ X Xh e X' e' β γ c' v hsh hec hγc hγ0 hγT hcond hsub ih =>
    intro hb hDβ IH
    obtain ⟨hs, -⟩ := hSh X Xh hsh
    have hB := hShB X Xh hsh
    have hX' : X' = 0 ∨ ∃ Xh', RoSh S X' Xh' := by
      rcases roOwn_sh hsub with h0 | ⟨Xh', h'⟩
      · exact Or.inl h0
      · exact Or.inr ⟨Xh', (hSh _ _ h').1⟩
    have hXB' : X' = 0 ∨ ∃ Xh', RoShB S X' Xh' := by
      rcases roOwn_sh hsub with h0 | ⟨Xh', h'⟩
      · exact Or.inl h0
      · exact Or.inr ⟨Xh', hShB _ _ h'⟩
    obtain ⟨hbsub, hb2⟩ := roBase_next hl hX hSh hsh hec hγc hγT hcond hX' hb
    obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
    obtain ⟨-, -, -, -, hexpA⟩ := hb
    have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
    obtain ⟨hEC, hEG, hEL⟩ := roE_data hs hexp
    have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
    have he1W : e + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt heW
    have he1c : GxCl (upsilon l) (ldAtR S l) (e + 1) :=
      (ldHull_iff hl hX he1W).1 (CSet.succ_mem ((ldHull_iff hl hX heW).2 hec))
    have hexp1 : e + 1 < S.psi (β + leWe (X + (e + 1))) (Om (1 + 1)) := hexpA (e + 1) he1c le_rfl
    have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
    have hγ1 : 1 ≤ γ := Order.one_le_iff_ne_zero.2 hγ0
    have hγs : γ < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) := roTe_gt hβown hEC hβd hEG hEL hγT
    have hle1 : S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) ≤
        S.psi (β + (leWe (X + e) * γ + c')) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) (by rw [← add_assoc]; exact le_self_add)).1
    have hle2 : S.psi (β + leWe (X + e)) (Om (1 + 1)) ≤ S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) := by
      refine (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
      calc leWe (X + e) = leWe (X + e) * 1 := (mul_one _).symm
        _ ≤ leWe (X + e) * γ := leMulWe_mono hγ1
    have hes : e < S.psi (β + (leWe (X + e) * γ + c')) (Om (1 + 1)) := (hexp.trans_le hle2).trans_le hle1
    have he1s : e + 1 < S.psi (β + (leWe (X + e) * γ + c')) (Om (1 + 1)) :=
      (SC_psi (InR_Om_succ 1) _).isSuccLimit.succ_lt hes
    obtain ⟨hDe, hBec, hΘeX, hΘe⟩ := IH e hec hes
    obtain ⟨hDγ, hBγc, hΘγX, hΘγ⟩ := IH γ hγc (hγs.trans_le hle1)
    -- the class of the codes below `ψ_{Ω₂}(β + c)`
    set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
      x < S.psi (β + (leWe (X + e) * γ + c')) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
    have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
    have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
      obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
      have hlx : log ω x ≤ x := log_le_self ω x
      have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
      exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
        ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
          (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
    have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
    obtain ⟨-, -, hDμγ, hBμγ⟩ := roB_We (n := n) hs.ne hB P hPD hPdec hPW ⟨hec, hes, heW⟩
      ⟨hγc, hγs.trans_le hle1, hγW⟩
    obtain ⟨hDW1, hBW1, -, -⟩ := roB_We (n := n) hs.ne hB P hPD hPdec hPW ⟨he1c, he1s, he1W⟩
      (⟨hγc, hγs.trans_le hle1, hγW⟩ : P γ)
    obtain ⟨hDβ', hBβ'⟩ := mvB_add (k := n) hDβ hDμγ
    obtain ⟨hDe', hDc', -, -, hDv, hown'⟩ := ih hb2 hDβ' (fun x hx hxs => IH x hx (by
      rw [← add_assoc]; exact hxs))
    rw [hBβ', hBμγ] at hown'
    obtain ⟨hDc, hBc⟩ := mvB_add (k := n) hDμγ hDc'
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDc
    obtain ⟨hDe1, hBe1⟩ := mvB_add (k := n) hDe hD1
    rw [mwB_one] at hBe1
    -- `B_n(T_{X+e+1}(β)) = T_{X+B_n e+1}(B_n β)`
    obtain ⟨hDβW, hBβW⟩ := mvB_add (k := n) hDβ hDW1
    have hTown : β + leWe (X + (e + 1)) ∈
        S.CSet (β + leWe (X + (e + 1))) (S.psi (β + leWe (X + (e + 1))) (Om (1 + 1))) := by
      refine CSet.add_mem (hβown _ (by rw [add_assoc])) (leWe_mem (CSet.add_mem (hs.mem _ _) (CSet.of_lt hexp1)))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDβW hTown
    have hBγT : Bc.bcB S n γ < leTe S (X + Bc.bcB S n e + 1) (Bc.bcB S n β) := by
      have hγT' : γ < S.psi (β + leWe (X + (e + 1))) (Om (1 + 1)) := by
        rw [← add_assoc]; exact hγT
      have h := (mvB_lt_iff (k := n) hDγ hDT).2 hγT'
      unfold leTe
      rwa [hBT, hBβW, hBW1, hBe1, ← add_assoc] at h
    -- the condition on the lower own argument
    have hcond' : (X' = X ∧ Bc.bcB S n e' ≤ Bc.bcB S n e) ∨
        (X' + Om (1 + 1) ≤ X ∧ Bc.bcB S n e' <
          leTe S (X' + Om (1 + 1)) (Bc.bcB S n β + leWe (X + Bc.bcB S n e) * Bc.bcB S n γ)) := by
      rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, leB_le hDe' hDe h2⟩
      · refine Or.inr ⟨h1, ?_⟩
        obtain ⟨hDWW, hBWW⟩ := roB_WeW (S := S) (n := n) hXB'
        obtain ⟨hDβWW, hBβWW⟩ := mvB_add (k := n) hDβ' hDWW
        obtain ⟨-, -, -, hβ'own, -⟩ := hbsub
        have hle3 : leWe (X' + Om (1 + 1)) ≤ leWe (X + e) := leWe_mono (h1.trans le_self_add)
        have hXC : X' ∈ S.CSet (β + leWe (X + e) * γ + leWe (X' + Om (1 + 1)))
            (S.psi (β + leWe (X + e) * γ + leWe (X' + Om (1 + 1))) (Om (1 + 1))) := by
          rcases hX' with rfl | ⟨Xh', hs'⟩
          · exact CSet.zero_mem _ _
          · exact hs'.mem _ _
        obtain ⟨hDT', hBT'⟩ := mxB_atom (n := n) hDβWW
          (CSet.add_mem (hβ'own _ hle3) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _))))
        have h := (mvB_lt_iff (k := n) hDe' hDT').2 h2
        unfold leTe
        rwa [hBT', hBβWW, hBWW, hBβ', hBμγ] at h
    -- the values
    have hΘeO : gxTh (upsilon l) (ldAtR S l) e < Om 1 := hΘeX.trans hc1
    have hΘγO : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := hΘγX.trans hc1
    obtain ⟨hDOΘ, hBOΘ⟩ := roB_Oe (S := S) (n := n) hB hΘeO hΘeX hΘγO hΘγX
    obtain ⟨hDsum, hBsum⟩ := mvB_add (k := n) hDOΘ hDv
    have hBγ0 : Bc.bcB S n γ ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDγ).2 (pos_iff_ne_zero.2 hγ0)
      rw [Bc.bcB_zero] at this; exact this.ne'
    refine ⟨hDe1, hDc, hDs, hBs, hDsum, ?_⟩
    rw [hBe1, hBc, hBμγ, hBsum, hBOΘ, ← hΘe, ← hΘγ]
    exact RoOwn.succ hsh hBec hBγc hBγ0 hBγT hcond' hown'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ro
