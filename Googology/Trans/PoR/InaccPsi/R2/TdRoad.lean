import Googology.Trans.PoR.InaccPsi.R2.TdMove

/-!
# Every atom below `ψ_{Ω₂}(φ(K, Ω₂ + 1))` moves, and the road

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `K = ψ_{Ω₁}(Ω_ω)`, `E_K = φ(K, Ω₂ + 1)`
(`Td.tdTop`), `E_Γ = φ(Γ₀, Ω₂ + 1)` (`Ta.taTop`), `θ⁺ = Lj.ljThP`, `θ = ψ_{Ω₂}(Ω_ω)`.

* `tdAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(E_K)` moves once the codes below it move**:
  `St.stAtMoveG` with `tdLS` and `tdLSB`; no other hypothesis);
* `tdTaTop_le`, `tdFG_le_top` (`ψ_{Ω₂}(E_Γ) ≤ ψ_{Ω₂}(E_K)`);
* `TdAtMove16` (**the move of the atoms `ψ_{Ω₂}(E_K) ≤ s ≤ θ`**, a hypothesis name), `tdAtMove15_of16`,
  `tdAtMove16_of15` (**`Ta.TaAtMove15 ⇔ TdAtMove16`**);
* `tdRoadL` (**the road with `TdAtMove16`, `Rn.RnThMoveM`, `Rn.RnEQhi2`**, each under `L(ω+1) ≤ ν_C`),
  `tdRoadL_hyps`.

No new axiom.  New definition: `TdAtMove16` (a hypothesis name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

theorem tdTop_We : leWe (tdTop S) = tdTop S := taWe_veb tdK_SC.1.ne' (le_refl 1)

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(φ(K, Ω₂ + 1))` moves** once the codes below it move. -/
theorem tdAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (tdTop S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => tdLS hl hX) (fun _ _ _ _ _ hl hX hl' hX' => tdLSB hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 (by rw [tdTop_We, tdTop_We]; exact hsT) IH

/-- `φ(Γ₀, Ω₂ + 1) ≤ φ(K, Ω₂ + 1)`. -/
theorem tdTaTop_le : taTop S ≤ tdTop S := veblen_left_monotone _ tdGam_le_K

/-- `ψ_{Ω₂}(φ(Γ₀, Ω₂ + 1)) ≤ ψ_{Ω₂}(φ(K, Ω₂ + 1))`. -/
theorem tdFG_le_top : S.psi (taTop S) (Om (1 + 1)) ≤ S.psi (tdTop S) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) tdTaTop_le).1

/-- **The move of the atoms `ψ_{Ω₂}(φ(K, Ω₂ + 1)) ≤ s ≤ θ`** (a hypothesis name). -/
def TdAtMove16 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (tdTop S) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TdAtMove16` gives `Ta.TaAtMove15`.** -/
theorem tdAtMove15_of16 (h : TdAtMove16 S) : TaAtMove15 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (tdTop S) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) (taTop_lim (S := S)).bot_lt (CSet.zero_mem _ _)).trans_le hsT
    exact tdAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Ta.TaAtMove15` gives `TdAtMove16`.** -/
theorem tdAtMove16_of15 (h : TaAtMove15 S) : TdAtMove16 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (tdFG_le_top.trans hsT) hsθ IH

/-- **The road with `TdAtMove16`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem tdRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TdAtMove16 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  taRoadL hU hO hL hV hN hlh (fun hν => tdAtMove15_of16 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `tdRoadL` follows from that of `Ta.taRoadL`. -/
theorem tdRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TaAtMove15 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TdAtMove16 S :=
  fun hν => tdAtMove16_of15 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Td
