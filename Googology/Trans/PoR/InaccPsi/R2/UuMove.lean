import Googology.Trans.PoR.InaccPsi.R2.UuOwn

/-!
# The own arguments over a base-indexed family past `Γ₂` move under `B_n`, the shift moving with them

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`.  `Rw.rwDigMove` for
families of shifts past `Γ₂` (`Uj.UjSh`, bound `Y₃`), with the same move hypothesis `hShB`.

* `uuDigMove` (**the digits, the exponents and the shift move**: if the codes below `ψ₂(β + c)` move, then
  `(X_B, B_n e, B_n c, B_n v)` is own at `λ'` over `B_n β` for `Sh'`, `B_n(Ω₂·X) = Ω₂·X_B`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Main

variable {n : ℕ} {l l' ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Sh Sh' : Ordinal.{0} → Ordinal.{0} → Ordinal.{0} → Prop}
  (hSh : ∀ b X Xh, Sh b X Xh → UjSh S l b X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RvTop S l b X Xh e)
  (hShB : ∀ b X Xh, Sh b X Xh → MvD S b → b ∈ S.CSet b (S.psi b (Om (1 + 1))) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (b + leWe X) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    Xh ≠ 0 ∧ ∃ XB XhB, Sh' (Bc.bcB S n b) XB XhB ∧ MvD S (Om (1 + 1) * X) ∧
      Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
      MvD S (Om 1 * Xh) ∧ Bc.bcB S n (Om 1 * Xh) = Om 1 * XhB)

include hl hX hSh hShB

/-- **The digits, the exponents and the shift move** (base-indexed families). -/
theorem uuDigMove {X e β c v : Ordinal.{0}} (h : RwOwn S l Sh X e β c v) :
    RoBaseE S l X e β → MvD S β →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + c) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S e ∧ MvD S c ∧ MvD S (β + c) ∧ Bc.bcB S n (β + c) = Bc.bcB S n β + Bc.bcB S n c ∧ MvD S v ∧
      ∃ XB, MvD S (Om (1 + 1) * X) ∧ Bc.bcB S n (Om (1 + 1) * X) = Om (1 + 1) * XB ∧
        RwOwn S l' Sh' XB (Bc.bcB S n e) (Bc.bcB S n β) (Bc.bcB S n c) (Bc.bcB S n v) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc1 : Bc.bcC S (n + 1) < Om 1 := hLw.trans (psi_lt Low.InR_Om_one _)
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hW0 : (0 : Ordinal.{0}) < Om (1 + 1) := ldOm2_SC.1
  induction h with
  | @low e β c v hown =>
    intro hb hDβ IH
    have hbE : LeBaseE S l e β := by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hb
      simp only [zero_add] at h1 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨hDe, hDc, hDs, hBs, hDv, hown'⟩ := leDigMoveE (n := n) (l' := l') hl hX hown hbE hDβ IH
    refine ⟨hDe, hDc, hDs, hBs, hDv, 0, by rw [mul_zero]; exact hD0, by rw [mul_zero, Bc.bcB_zero],
      RwOwn.low hown'⟩
  | @succ X Xh e X' e' β γ c' v hsh hec hγc hγ0 hγT hcond hsub ih =>
    intro hb hDβ IH
    obtain ⟨hs, -⟩ := hSh β X Xh hsh
    have hX' := Rw.rwOwn_sh hsub
    obtain ⟨hbsub, hb2⟩ := uuBase_next hl hX hSh hsh hec hγc hγT hcond hX' hb
    obtain ⟨hβd, hβA, hβown⟩ := roBase_succ hb
    obtain ⟨-, -, -, hβown0, hexpA⟩ := hb
    have hβo : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
      have := hβown0 0 zero_le; rwa [add_zero] at this
    have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
    obtain ⟨hEC, hEG, hEL⟩ := ujE_data hs le_rfl hexp
    have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
    have he1W : e + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt heW
    have he1c : GxCl (upsilon l) (ldAtR S l) (e + 1) :=
      (ldHull_iff hl hX he1W).1 (CSet.succ_mem ((ldHull_iff hl hX heW).2 hec))
    have hexp1 : e + 1 < S.psi (β + leWe (X + (e + 1))) (Om (1 + 1)) := hexpA (e + 1) he1c le_rfl
    have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
    have hγ1 : 1 ≤ γ := Order.one_le_iff_ne_zero.2 hγ0
    have hγs : γ < S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) := ujTe_gt hβown hEC hβd hEG hEL hγT
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
    -- the shift moves
    have hWXs : S.psi (β + leWe X) (Om (1 + 1)) ≤ S.psi (β + (leWe (X + e) * γ + c')) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((rvWX_le_mul le_rfl X e γ hγ0).trans
        (by rw [← add_assoc]; exact le_self_add))).1
    obtain ⟨hXh0, XB, XhB, hsh', hDX, hBX, hDXh, hBXh⟩ :=
      hShB β X Xh hsh hDβ hβo (fun x hx hxs => IH x hx (hxs.trans_le hWXs))
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
    obtain ⟨-, -, hDμγ, hBμγ⟩ := rqB_We (n := n) hs.ne hDX hBX P hPD hPdec hPW ⟨hec, hes, heW⟩
      ⟨hγc, hγs.trans_le hle1, hγW⟩
    obtain ⟨hDW1, hBW1, -, -⟩ := rqB_We (n := n) hs.ne hDX hBX P hPD hPdec hPW ⟨he1c, he1s, he1W⟩
      (⟨hγc, hγs.trans_le hle1, hγW⟩ : P γ)
    obtain ⟨hDβ', hBβ'⟩ := mvB_add (k := n) hDβ hDμγ
    obtain ⟨hDe', hDc', -, -, hDv, X'B, hDX', hBX', hown'⟩ := ih hb2 hDβ' (fun x hx hxs => IH x hx (by
      rw [← add_assoc]; exact hxs))
    rw [hBβ', hBμγ] at hown'
    obtain ⟨hDc, hBc⟩ := mvB_add (k := n) hDμγ hDc'
    obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDβ hDc
    obtain ⟨hDe1, hBe1⟩ := mvB_add (k := n) hDe hD1
    rw [mwB_one] at hBe1
    -- `B_n(T_{X+e+1}(β)) = T_{X_B+B_n e+1}(B_n β)`
    obtain ⟨hDβW, hBβW⟩ := mvB_add (k := n) hDβ hDW1
    have hTown : β + leWe (X + (e + 1)) ∈
        S.CSet (β + leWe (X + (e + 1))) (S.psi (β + leWe (X + (e + 1))) (Om (1 + 1))) := by
      refine CSet.add_mem (hβown _ (by rw [add_assoc]))
        (leWe_mem (CSet.add_mem (ujMem hs (ujX_le_base X (e + 1) β) (rvWX_le le_rfl X (e + 1)) le_rfl)
          (CSet.of_lt hexp1)))
    obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDβW hTown
    have hBγT : Bc.bcB S n γ < leTe S (XB + Bc.bcB S n e + 1) (Bc.bcB S n β) := by
      have hγT' : γ < S.psi (β + leWe (X + (e + 1))) (Om (1 + 1)) := by
        rw [← add_assoc]; exact hγT
      have h := (mvB_lt_iff (k := n) hDγ hDT).2 hγT'
      unfold leTe
      rwa [hBT, hBβW, hBW1, hBe1, ← add_assoc] at h
    -- the condition on the lower own argument
    have hcond' : (X'B = XB ∧ Bc.bcB S n e' ≤ Bc.bcB S n e) ∨
        (X'B + Om (1 + 1) ≤ XB ∧ Bc.bcB S n e' <
          leTe S (X'B + Om (1 + 1)) (Bc.bcB S n β + leWe (XB + Bc.bcB S n e) * Bc.bcB S n γ)) := by
      rcases hcond with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1
        rw [hBX] at hBX'
        exact Or.inl ⟨(mul_left_cancel₀ hW0.ne' hBX').symm, leB_le hDe' hDe h2⟩
      · obtain ⟨hDWW, hBWW⟩ := rqB_WeW (S := S) (n := n) hDX' hBX'
        obtain ⟨hD2, hB2⟩ := roB_W2 (S := S) (n := n)
        obtain ⟨hDs2, hBs2⟩ := mvB_add (k := n) hDX' hD2
        rw [hBX', hB2] at hBs2
        have hXle : Om (1 + 1) * X' + Om (1 + 1) * Om (1 + 1) ≤ Om (1 + 1) * X := by
          rw [← mul_add]; exact mul_le_mul_right h1 _
        have hXle' := leB_le (n := n) hDs2 hDX hXle
        rw [hBs2, hBX, ← mul_add] at hXle'
        refine Or.inr ⟨(mul_le_mul_iff_right₀ hW0).1 hXle', ?_⟩
        obtain ⟨hDβWW, hBβWW⟩ := mvB_add (k := n) hDβ' hDWW
        obtain ⟨-, -, -, hβ'own, -⟩ := hbsub
        have hle3 : leWe (X' + Om (1 + 1)) ≤ leWe (X + e) := leWe_mono (h1.trans le_self_add)
        have hXC : X' ∈ S.CSet (β + leWe (X + e) * γ + leWe (X' + Om (1 + 1)))
            (S.psi (β + leWe (X + e) * γ + leWe (X' + Om (1 + 1))) (Om (1 + 1))) := by
          rcases hX' with rfl | ⟨Xh', hs'⟩
          · exact CSet.zero_mem _ _
          · exact ujMem (hSh _ _ _ hs').1 (ujX_le_base X' _ _) (rvWX_le le_rfl X' _) le_rfl
        obtain ⟨hDT', hBT'⟩ := mxB_atom (n := n) hDβWW
          (CSet.add_mem (hβ'own _ hle3) (leWe_mem (CSet.add_mem hXC (mxOm2_mem _ _))))
        have h := (mvB_lt_iff (k := n) hDe' hDT').2 h2
        unfold leTe
        rwa [hBT', hBβWW, hBWW, hBβ', hBμγ] at h
    -- the values
    have hΘeO : gxTh (upsilon l) (ldAtR S l) e < Om 1 := hΘeX.trans hc1
    have hΘγO : gxTh (upsilon l) (ldAtR S l) γ < Om 1 := hΘγX.trans hc1
    obtain ⟨hDOΘ, hBOΘ⟩ := rqB_Oe (S := S) (n := n) hXh0 hDXh hBXh hΘeO hΘeX hΘγO hΘγX
    obtain ⟨hDsum, hBsum⟩ := mvB_add (k := n) hDOΘ hDv
    have hBγ0 : Bc.bcB S n γ ≠ 0 := by
      have := (mvB_lt_iff (k := n) hD0 hDγ).2 (pos_iff_ne_zero.2 hγ0)
      rw [Bc.bcB_zero] at this; exact this.ne'
    refine ⟨hDe1, hDc, hDs, hBs, hDsum, XB, hDX, hBX, ?_⟩
    rw [hBe1, hBc, hBμγ, hBsum, hBOΘ, ← hΘe, ← hΘγ]
    exact RwOwn.succ hsh' hBec hBγc hBγ0 hBγT hcond' hown'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uu
