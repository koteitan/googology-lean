import Googology.Trans.PoR.InaccPsi.R2.UaMove

/-!
# The atom move below `ψ_{Ω₂}(W^{W^{X₃}})` and the road

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `G = φ(Ω₂, 1)`, `X₃ = Ua.uaX3 = φ(Ω₂ + 1, 0)`, `θ = ConjT.th S`.

* `uaAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{X₃}})` moves** once the codes below it move;
  `St.stAtMoveG` with `Ua.uaLS`, `Ua.uaLSB`);
* `UaAtMove24` (**`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{X₃}}) ≤ s ≤ θ`**), `uaAtMove23_of24`,
  `uaAtMove24_of23`, `uaAtMove17_of24` (`UaAtMove24 ⇒ Tj.TjAtMove17`);
* `uaRoad` (**the road of `Tx.txRoad2` with `UaAtMove24`** in place of `Tx.TxAtMove23`), `uaRoad_hyps`.

No new axiom.  New definition: the statement name `UaAtMove24`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{X₃}})` moves** once the codes below it move. -/
theorem uaAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe uaX3)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => uaLS hl hX) (fun _ _ _ _ _ hl hX hl' hX' => uaLSB hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `G·Ω₂ < X₃`. -/
theorem uaGW_lt_X3 : txGW S < uaX3 := by
  have hε : ω ^ uaX3 = uaX3 := gg_veblen_eps (zero_lt_one.trans_le le_add_self).ne'
  have hGX : veblen (Om (1 + 1 : Ordinal.{0})) 1 < uaX3 := uaG_lt_X2.trans uaX2_lt_X3
  exact tuMul_lt_fix hε hGX (tgOm_lt_G.trans hGX)

/-- `ψ_{Ω₂}(W^{W^{G·Ω₂}}) ≤ ψ_{Ω₂}(W^{W^{X₃}})`. -/
theorem uaF_le :
    S.psi (leWe (leWe (txGW S))) (Om (1 + 1)) ≤ S.psi (leWe (leWe uaX3)) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (leWe_mono uaGW_lt_X3.le))).1

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{X₃}}) ≤ s ≤ θ`.** -/
def UaAtMove24 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe uaX3)) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`UaAtMove24` gives `Tx.TxAtMove23`.** -/
theorem uaAtMove23_of24 (h : UaAtMove24 S) : TxAtMove23 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe uaX3)) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le
        (tnG_le_FN.trans (tuFN_le.trans (tuFU_le.trans (tuFE_le.trans (txF_le.trans (txF2_le.trans hsT))))))
    exact uaAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Tx.TxAtMove23` gives `UaAtMove24`.** -/
theorem uaAtMove24_of23 (h : TxAtMove23 S) : UaAtMove24 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (uaF_le.trans hsT) hsθ IH

/-- **`UaAtMove24` gives `Tj.TjAtMove17`.** -/
theorem uaAtMove17_of24 (h : UaAtMove24 S) : TjAtMove17 S := txAtMove17_of23 (uaAtMove23_of24 h)

/-- **The road with `UaAtMove24`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem uaRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → UaAtMove24 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  txRoad2 hU hO hL hV hN hlh (fun hν => uaAtMove23_of24 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `uaRoad` follows from that of `Tx.txRoad2`. -/
theorem uaRoad_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TxAtMove23 S) :
    Nc.ncL S (ω + 1) ≤ nuC → UaAtMove24 S :=
  fun hν => uaAtMove24_of23 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Ua
