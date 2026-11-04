import Googology.Trans.PoR.InaccPsi.R2.ZiTower

/-!
# THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·Ω₂·K₃}` ABOVE EVERY TOP ATOM, AND THE REFUTE-FIRST RECORDS OF ROUND 132

`W^x`, `B_n`, "window", `A'`, "IH(s)" as in `Zd.zdTopMoveY3E0`; `K₃ = ψ_{Ω₁}(Ω₃ + 1)`, `P_η = Zi.ziPP S η`.

* `ziTopMoveWK` (above every top atom `t = β + W^{Ω_{k+3}+e}`), `ziTopMoveCstWK` (above every top atom of
  `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ψ_{Ω₁}(0)`): every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·Ω₂·K₃})` moves under IH(s);
* `ziTestE0` (REFUTE FIRST, (a) at the shift `Y₃ + Ω₂·ε₀`: it is a fixed relative shift with image `Y₂ + Ω₁·ε₀`,
  and the atom `ψ₂(Ω₃ + W^{Y₃+Ω₂·ε₀})` moves at every window under IH),
* `ziTestY3two` (REFUTE FIRST, (a) at the shift `Y₃·2`: `Y₃·2 = Y₃ + Ω₂·Ω₂·Y₃ = P_{Y₃}`, `Y₃·2 ≥ Y₃ + Ω₂·Ω₂·Ω₂`, so it
  lies past every proved region; `Y₃` is a constant fixed by `B_n`).

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

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·Ω₂·K₃})` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under IH(s) (`Zd.zdTopMoveY3E0` is the bound `W^{Y₃+Ω₂·ε₀}`). -/
theorem ziTopMoveWK (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + leWe (ziPP S (ziK3 S))) (Om (1 + 1)))
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
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((Yt.ytOm3_le_X k).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := by
      calc X = leWe X := (Vn.vnWe_OmK k).symm
        _ ≤ leWe (X + e) := leWe_mono le_self_add
    exact (Yt.ytOm3_le_X k).trans (hXle.trans le_add_self)
  exact ziPsi3OffWK hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·Ω₂·K₃})` ABOVE EVERY TOP ATOM `t = β + W^{X_ξ+e}` MOVES**, `X_ξ = Ω_{k+3} + Ω₂·ξ`, `ξ < ψ_{Ω₁}(0)` (`Zd.zdTopMoveChainY3E0` is `ξ < ε₀` and the offsets below `W^{Y₃+Ω₂·ε₀}`, `Zi.ziTopMoveCstY3K` the offsets below `W^{Y₃+Ω₂·K₃}`). -/
theorem ziTopMoveCstWK (k : ℕ) {ξ : Ordinal.{0}} (hξ : ξ < ziG S) {e β : Ordinal.{0}}
    (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β) (hbe : Ro.RoBaseE S l (zdX k ξ) e β)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (zdX k ξ + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (zdX k ξ + e) + leWe (ziPP S (ziK3 S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := zdX k ξ with hXdef
  have hm : ZdMv S X := ziMv_cst k hξ
  have HL : ZdHL S X := ziHL_cst k hξ
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := zdTopBase hm hR h1 hr hl' hB HL hA' hρ' hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := zdBaseFacts hm hR h1 hr hl' hB hec hβD hbe IHt
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((zdOm3_le_X k ξ).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := (le_self_add : X ≤ X + e).trans
      ((Ordinal.le_mul_right _ ldOm2_SC.1).trans (Ordinal.right_le_opow _ one_lt_omega0))
    exact (zdOm3_le_X k ξ).trans (hXle.trans le_add_self)
  exact ziPsi3OffWK hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

/-- **REFUTE FIRST, (a) at `Y₃ + Ω₂·ε₀`**: `(Y₃ + Ω₂·ε₀, Y₂ + Ω₁·ε₀)` is a fixed relative shift (`Zi.ziRS_cst`),
and the atom `ψ₂(Ω₃ + W^{Y₃+Ω₂·ε₀})` (above the top atom `Ω₃ = W^{Ω₃+0}`) moves at every window under IH. -/
theorem ziTestE0 :
    ZdRS S (zdXr S ε₀) (zdXhr S ε₀) ∧
      (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1)) ∈ ldAtR S l →
        (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1)) →
          MvD S x ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
          gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
        MvD S (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1))) ∧
          Bc.bcB S n (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1))) ∈ ldAtR S l' ∧
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1)))) =
            Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1))))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have he0K : (ε₀ : Ordinal.{0}) < ziK3 S := ziEps0_lt_G.trans_le ziG_le_K3
  refine ⟨ziRS_cst he0K, fun hs IH => ?_⟩
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero (leRho hR.1 hX).1.1
  have hb0 := Xm.xmRB0 (S := S) 0 l (Om_pos one_ne_zero)
  have e0 : (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by
    rw [zero_add, add_zero, Nat.cast_zero, zero_add]; exact Vn.vnWe_Om3
  have hK : zdXr S ε₀ < ziPP S (ziK3 S) := by
    have h1' : zdXr S ε₀ < zdXr S (Om (1 + 1)) :=
      zdXr_lt ((ziEps0_lt_G (S := S)).trans ((ziG_lt_Om1 (S := S)).trans (Om_lt_Om.2 (lt_add_one 1))))
    refine h1'.trans_le ?_
    unfold zdXr ziPP
    exact (add_le_add_iff_left _).2 (Ordinal.le_mul_left _ ((epsilon_pos 0).trans he0K))
  have hmem : Om (1 + 1 + 1) + leWe (zdXr S ε₀) ∈ S.CSet (Om (1 + 1 + 1) + leWe (ziPP S (ziK3 S)))
      (S.psi (Om (1 + 1 + 1) + leWe (ziPP S (ziK3 S))) (Om (1 + 1))) :=
    CSet.add_mem (Ry.ryOm3_mem _ _) (leWe_mem ((ziRS_cst he0K).mem _ _ (lt_add_of_pos_right _ (leWe_pos _))))
  have h := ziTopMoveWK hR h1 hr hl' hB hA' hρ' 0 h0c (Xi.xiD_zero l) hb0
    (s := S.psi (Om (1 + 1 + 1) + leWe (zdXr S ε₀)) (Om (1 + 1))) hs
    (by rw [e0]; exact (psi_mono hκ2 le_self_add).1)
    (by rw [e0]; exact psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left _).2 (leWe_lt hK)) hmem) IH
  exact h

end Win

/-- **REFUTE FIRST, (a) at `Y₃·2`**: `Y₃·2 = Y₃ + Ω₂·Ω₂·Y₃` (the tower shift `P_{Y₃}`), and
`Y₃ + Ω₂·Ω₂·Ω₂ ≤ Y₃·2`: the shift `Y₃·2` lies past `W^{Y₃+Ω₂·Ω₂·K₃}` and past the whole code range of every chain
proved here; `B_n` fixes `Y₃`. -/
theorem ziTestY3two :
    ugY S * 2 = ziPP S (ugY S) ∧ ziPP S (Om (1 + 1)) ≤ ugY S * 2 ∧ ziPP S (ziK3 S) < ugY S * 2 ∧
      ∀ n : ℕ, Bc.bcB S n (ugY S) = ugY S := by
  have hY := Uq.uqY_SC (S := S)
  have h2Y : Om (1 + 1 : Ordinal.{0}) < ugY S := Uq.uqW_lt_Y
  have hEY : ω ^ ugY S = ugY S := gg_SC_eps hY
  have h22Y : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * ugY S = ugY S := by
    have hA : Om (1 + 1) + Om (1 + 1) + ugY S = ugY S :=
      Ordinal.add_absorp (by rw [hEY]; exact hY.isPrincipal h2Y h2Y) hEY.le
    calc Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * ugY S = ω ^ (Om (1 + 1) + Om (1 + 1) + ugY S) := by
          rw [opow_add, opow_add, gg_SC_eps ldOm2_SC, hEY]
      _ = ugY S := by rw [hA, hEY]
  have e2 : ugY S * 2 = ugY S + ugY S := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
  have hPY : ziPP S (ugY S) = ugY S * 2 := by unfold ziPP; rw [h22Y, e2]
  refine ⟨hPY.symm, ?_, ?_, fun n => (Yy.yyY3_D (S := S) (n := n)).2⟩
  · rw [← hPY]; exact ziPP_mono h2Y.le
  · rw [← hPY]; exact ziPP_lt ((ziK3_lt_Om2 (S := S)).trans h2Y)

end Googology.Trans.PoR.InaccPsi.R2.Zi
