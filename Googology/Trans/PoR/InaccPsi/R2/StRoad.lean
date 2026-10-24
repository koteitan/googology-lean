import Googology.Trans.PoR.InaccPsi.R2.StEW

/-!
# The atoms below `ψ_{Ω₂}(W^{W^{ε + Ω₂²}})` move, and the road with the atoms above them

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `ε = ε_{Ω₂+1}`,
`F_G = ψ_{Ω₂}(W^{W^{ε+Ω₂²}})` (the new bound), `T_{ε+Ω₂}(0) = ψ_{Ω₂}(W^{ε+Ω₂})` (the bound of `Sq.SqAtMove12`),
`θ⁺ = Lj.ljThP`.

* `stAtMoveEG` (**every atom `ψ_{Ω₂}(0) < s < F_G` moves** once the codes below it move: `B_n s` is an atom at
  `λ'`, `B_n s < θ⁺`, `Θ_λ s < c_{n+1}`, `Θ_{λ'}(B_n s) = B_n(Θ_λ s)`; `St.stAtMoveG` for the system
  `St.stLS_EW` with its move `St.stLSB_EW`; no other hypothesis);
* `stT_le_FG` (`T_{ε+Ω₂}(0) ≤ F_G`);
* `StAtMove13 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_G ≤ s ≤ θ`; `stAtMove12_of13`
  (**`StAtMove13` gives `Sq.SqAtMove12`**), `stAtMove13_of12` (the converse), `stRoadL` (**the road**),
  `stRoadL_hyps`.

No new axiom.  New definition: the hypothesis name `StAtMove13`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.St

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq

variable {S : InaccSeq.{0}}

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{ε + Ω₂²}})` moves** once the codes below it move. -/
theorem stAtMoveEG {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe (stEW S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => stLS_EW hl hX) (fun _ _ _ _ _ hl hX hl' hX' => stLSB_EW hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `ψ_{Ω₂}(W^{ε+Ω₂}) ≤ ψ_{Ω₂}(W^{W^{ε + Ω₂²}})`. -/
theorem stT_le_FG :
    leTe S (veblen 1 (Om (1 + 1) + 1) + Om (1 + 1)) 0 ≤ S.psi (leWe (leWe (stEW S))) (Om (1 + 1)) := by
  unfold leTe
  rw [zero_add]
  refine (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono ?_)).1
  have hpr : IsPrincipal (· + ·) (leWe (stEW S)) := isPrincipal_add_omega0_opow _
  have hεlt : veblen 1 (Om (1 + 1) + 1) < leWe (stEW S) := by
    conv_lhs => rw [← sqEps_We]
    exact leWe_lt (lt_add_of_pos_right _ (mul_pos ldOm2_SC.1 ldOm2_SC.1))
  have hWlt : Om (1 + 1 : Ordinal.{0}) < leWe (stEW S) := by
    rw [← leWe_one]
    exact leWe_lt (sqOne_le_eps.trans_lt (lt_add_of_pos_right _ (mul_pos ldOm2_SC.1 ldOm2_SC.1)))
  exact (hpr hεlt hWlt).le

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{ε + Ω₂²}}) ≤ s ≤ θ`.** -/
def StAtMove13 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (stEW S))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`StAtMove13` gives `Sq.SqAtMove12`.** -/
theorem stAtMove12_of13 (h : StAtMove13 S) : SqAtMove12 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (stEW S))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      ((psi_lt_psi_of_mem (InR_Om_succ 1) veblen_pos (CSet.zero_mem _ _)).trans sqFeps_lt_T).trans_le hsT
    exact stAtMoveEG hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Sq.SqAtMove12` gives `StAtMove13`.** -/
theorem stAtMove13_of12 (h : SqAtMove12 S) : StAtMove13 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (stT_le_FG.trans hsT) hsθ IH

/-- **The road with `StAtMove13`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem stRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → StAtMove13 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  sqRoadL hU hO hL hV hN hlh (fun hν => stAtMove12_of13 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `stRoadL` follows from that of `Sq.sqRoadL`. -/
theorem stRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → SqAtMove12 S) :
    Nc.ncL S (ω + 1) ≤ nuC → StAtMove13 S :=
  fun hν => stAtMove13_of12 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.St
