import Googology.Trans.PoR.InaccPsi.R2.TaMove

/-!
# Every atom below `ψ_{Ω₂}(φ(Γ₀, Ω₂ + 1))` moves, and the road

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `E_Γ = φ(Γ₀, Ω₂ + 1)` (`Ta.taTop`), `θ⁺ = Lj.ljThP`,
`F_ω = ψ_{Ω₂}(ε_{Ω₂+ω})` (`Sw.SwAtMove14`), `F_Γ = ψ_{Ω₂}(E_Γ)`.

* `taAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(E_Γ)` moves once the codes below it move**:
  `St.stAtMoveG` with the level system `Ta.taLS` and its move `Ta.taLSB`; no other hypothesis);
* `TaAtMove15` (**the move of the atoms `F_Γ ≤ s ≤ θ`**, a hypothesis name), `taAtMove14_of15`,
  `taAtMove15_of14` (**`Sw.SwAtMove14 ⇔ TaAtMove15`**);
* `taRoadL` (**the road with `TaAtMove15`, `Rn.RnThMoveM`, `Rn.RnEQhi2`**, each under `L(ω+1) ≤ ν_C`),
  `taRoadL_hyps`.

No new axiom.  New definition: `TaAtMove15` (a hypothesis name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

theorem taTop_We : leWe (taTop S) = taTop S := taWe_veb gamma_pos.ne' (le_refl 1)

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(φ(Γ₀, Ω₂ + 1))` moves** once the codes below it move. -/
theorem taAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (taTop S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => taLS hl hX) (fun _ _ _ _ _ hl hX hl' hX' => taLSB hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 (by rw [taTop_We, taTop_We]; exact hsT) IH

/-- `ψ_{Ω₂}(ε_{Ω₂+ω}) ≤ ψ_{Ω₂}(φ(Γ₀, Ω₂ + 1))`. -/
theorem taFw_le_top : S.psi (Sw.swTop S) (Om (1 + 1)) ≤ S.psi (taTop S) (Om (1 + 1)) := by
  have hlt : Sw.swTop S < taTop S := by
    unfold Sw.swTop taTop
    have hp := Ph.ph_veblen_prin (gamma 0) (Om (1 + 1) + 1)
    have hW : Om (1 + 1 : Ordinal.{0}) < veblen (gamma 0) (Om (1 + 1) + 1) := taKy_lt (le_refl 1)
    have hωW : ω < veblen (gamma 0) (Om (1 + 1) + 1) := (Lw.lw_omega_lt_SC ldOm2_SC).trans hW
    exact (veblen_lt_veblen_iff).2 (Or.inr (Or.inl ⟨(one_lt_omega0.trans (omega0_lt_gamma 0)), hp hW hωW⟩))
  exact (psi_mono (S := S) (InR_Om_succ 1) hlt.le).1

/-- **The move of the atoms `ψ_{Ω₂}(φ(Γ₀, Ω₂ + 1)) ≤ s ≤ θ`** (a hypothesis name). -/
def TaAtMove15 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (taTop S) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TaAtMove15` gives `Sw.SwAtMove14`.** -/
theorem taAtMove14_of15 (h : TaAtMove15 S) : Sw.SwAtMove14 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (taTop S) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) (Sw.swTop_lim (S := S)).bot_lt (CSet.zero_mem _ _)).trans_le hsT
    exact taAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Sw.SwAtMove14` gives `TaAtMove15`.** -/
theorem taAtMove15_of14 (h : Sw.SwAtMove14 S) : TaAtMove15 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (taFw_le_top.trans hsT) hsθ IH

/-- **The road with `TaAtMove15`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem taRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TaAtMove15 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sw.swRoadL hU hO hL hV hN hlh (fun hν => taAtMove14_of15 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `taRoadL` follows from that of `Sw.swRoadL`. -/
theorem taRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → Sw.SwAtMove14 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TaAtMove15 S :=
  fun hν => taAtMove15_of14 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Ta
