import Googology.Trans.PoR.InaccPsi.R2.SwMove

/-!
# Every atom below `ψ_{Ω₂}(ε_{Ω₂+ω})` moves, and the road

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `ε_{Ω₂+ω} = Sw.swTop`, `θ⁺ = Lj.ljThP`,
`F_W = ψ_{Ω₂}(W^{W^{ε_{Ω₂+1} + Ω₂²}})` (`St.StAtMove13`), `F_ω = ψ_{Ω₂}(ε_{Ω₂+ω})`.

* `swAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(ε_{Ω₂+ω})` moves once the codes below it move**:
  `St.stAtMoveG` with the level system `Sw.swLS` and its move `Sw.swLSB`; no other hypothesis);
* `SwAtMove14` (**the move of the atoms `F_ω ≤ s ≤ θ`**, a hypothesis name), `swAtMove13_of14`,
  `swAtMove14_of13` (**`St.StAtMove13 ⇔ SwAtMove14`**);
* `swRoadL` (**the road with `SwAtMove14`, `Rn.RnThMoveM`, `Rn.RnEQhi2`**, each under `L(ω+1) ≤ ν_C`),
  `swRoadL_hyps`.

No new axiom.  New definition: `SwAtMove14` (a hypothesis name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(ε_{Ω₂+ω})` moves** once the codes below it move. -/
theorem swAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (swTop S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => swLS hl hX) (fun _ _ _ _ _ hl hX hl' hX' => swLSB hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 (by rw [swTop_We, swTop_We]; exact hsT) IH

/-- `ψ_{Ω₂}(W^{W^{ε + Ω₂²}}) ≤ ψ_{Ω₂}(ε_{Ω₂+ω})`. -/
theorem swFW_le_top : S.psi (leWe (leWe (stEW S))) (Om (1 + 1)) ≤ S.psi (swTop S) (Om (1 + 1)) := by
  have hlt : stEW S < swTop S := by
    have h0 : veblen 1 (Om (1 + 1) + 1) = swL 0 := by unfold swL; rw [Nat.cast_zero, zero_add]
    have hε := swL_lt_top (S := S) 0
    rw [← h0] at hε
    have hp : IsPrincipal (· + ·) (swTop S) := Ph.ph_veblen_prin 1 _
    unfold stEW
    exact hp hε (stW2_lt_eps.trans hε)
  have h := leWe_mono (leWe_mono hlt.le)
  rw [swTop_We, swTop_We] at h
  exact (psi_mono (S := S) (InR_Om_succ 1) h).1

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(ε_{Ω₂+ω}) ≤ s ≤ θ`** (a hypothesis name). -/
def SwAtMove14 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (swTop S) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`SwAtMove14` gives `St.StAtMove13`.** -/
theorem swAtMove13_of14 (h : SwAtMove14 S) : StAtMove13 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (swTop S) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_pos _) (CSet.zero_mem _ _)).trans_le hsT
    exact swAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`St.StAtMove13` gives `SwAtMove14`.** -/
theorem swAtMove14_of13 (h : StAtMove13 S) : SwAtMove14 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (swFW_le_top.trans hsT) hsθ IH

/-- **The road with `SwAtMove14`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem swRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → SwAtMove14 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  stRoadL hU hO hL hV hN hlh (fun hν => swAtMove13_of14 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `swRoadL` follows from that of `St.stRoadL`. -/
theorem swRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → StAtMove13 S) :
    Nc.ncL S (ω + 1) ≤ nuC → SwAtMove14 S :=
  fun hν => swAtMove14_of13 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Sw
