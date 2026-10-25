import Googology.Trans.PoR.InaccPsi.R2.TnSys3

/-!
# The atoms below `ψ_{Ω₂}(W^{W^{G + Ω₂³}})` move, and the road with the atoms above them

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `G = φ(Ω₂, 1)`,
`F_N = ψ_{Ω₂}(W^{W^{G+Ω₂³}})` (the new bound), `θ⁺ = Lj.ljThP`.

* `tnAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < F_N` moves** once the codes below it move: `St.stAtMoveG` for the
  system `Tn.tnLS3` with its move `Tn.tnLSB3`; no other hypothesis);
* `tnG_le_FN` (`ψ_{Ω₂}(G) ≤ F_N`);
* `TnAtMove18 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_N ≤ s ≤ θ`; `tnAtMove17_of18`
  (**`TnAtMove18` gives `Tj.TjAtMove17`**), `tnAtMove18_of17` (the converse), `tnRoadL` (**the road**),
  `tnRoadL_hyps`.

No new axiom.  New definition: the hypothesis name `TnAtMove18`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj

variable {S : InaccSeq.{0}}

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{G + Ω₂³}})` moves** once the codes below it move. -/
theorem tnAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe (tnGW3 S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => tnLS3 hl hX) (fun _ _ _ _ _ hl hX hl' hX' => tnLSB3 hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `e ≤ W^e`. -/
theorem tnLe_We (e : Ordinal.{0}) : e ≤ leWe e :=
  (Ordinal.le_mul_right e ldOm2_SC.1).trans (right_le_opow _ one_lt_omega0)

/-- `ψ_{Ω₂}(G) ≤ ψ_{Ω₂}(W^{W^{G + Ω₂³}})`. -/
theorem tnG_le_FN :
    S.psi (veblen (Om (1 + 1)) 1) (Om (1 + 1)) ≤ S.psi (leWe (leWe (tnGW3 S))) (Om (1 + 1)) := by
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  calc veblen (Om (1 + 1)) 1 ≤ tnGW3 S := le_self_add
    _ ≤ leWe (tnGW3 S) := tnLe_We _
    _ ≤ leWe (leWe (tnGW3 S)) := tnLe_We _

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{G + Ω₂³}}) ≤ s ≤ θ`.** -/
def TnAtMove18 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (tnGW3 S))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TnAtMove18` gives `Tj.TjAtMove17`.** -/
theorem tnAtMove17_of18 (h : TnAtMove18 S) : TjAtMove17 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (tnGW3 S))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le hsT
    exact tnAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Tj.TjAtMove17` gives `TnAtMove18`.** -/
theorem tnAtMove18_of17 (h : TjAtMove17 S) : TnAtMove18 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (tnG_le_FN.trans hsT) hsθ IH

/-- **The road with `TnAtMove18`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem tnRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TnAtMove18 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tjRoadL hU hO hL hV hN hlh (fun hν => tnAtMove17_of18 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `tnRoadL` follows from that of `Tj.tjRoadL`. -/
theorem tnRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TjAtMove17 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TnAtMove18 S :=
  fun hν => tnAtMove18_of17 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Tn
