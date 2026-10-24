import Googology.Trans.PoR.InaccPsi.R2.TjMove

/-!
# Every atom below `ψ_{Ω₂}(φ(Ω₂, 1))` moves, and the road

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `G = φ(Ω₂, 1)`, `E_K = φ(K, Ω₂ + 1)` (`Td.tdTop`),
`K = ψ_{Ω₁}(Ω_ω)`, `θ⁺ = Lj.ljThP`, `θ = ψ_{Ω₂}(Ω_ω)`.

* `tjAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(G)` moves once the codes below it move**: `St.stAtMoveG`
  with `Tj.tjLS` and `Tj.tjLSB`; no other hypothesis);
* `tjTdTop_lt`, `tjFK_le` (`ψ_{Ω₂}(E_K) ≤ ψ_{Ω₂}(G)`);
* `TjAtMove17` (**the move of the atoms `ψ_{Ω₂}(G) ≤ s ≤ θ`**, a hypothesis name), `tjAtMove16_of17`,
  `tjAtMove17_of16` (**`Td.TdAtMove16 ⇔ TjAtMove17`**);
* `tjRoadL` (**the road with `TjAtMove17`, `Rn.RnThMoveM`, `Rn.RnEQhi2`**, each under `L(ω+1) ≤ ν_C`),
  `tjRoadL_hyps`.

No new axiom.  New definition: `TjAtMove17` (a hypothesis name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

variable {S : InaccSeq.{0}}

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(φ(Ω₂, 1))` moves** once the codes below it move. -/
theorem tjAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (veblen (Om (1 + 1)) 1) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => tjLS hl hX) (fun _ _ _ _ _ hl hX hl' hX' => tjLSB hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 (by rw [tgWe_G, tgWe_G]; exact hsT) IH

/-- `φ(K, Ω₂ + 1) < φ(Ω₂, 1)`. -/
theorem tjTdTop_lt : tdTop S < veblen (Om (1 + 1)) 1 := by
  have h : Om (1 + 1 : Ordinal.{0}) + 1 < veblen (Om (1 + 1)) 1 := tjG_lim.add_one_lt tgOm_lt_G
  calc tdTop S = veblen (tdK S) (Om (1 + 1) + 1) := rfl
    _ < veblen (tdK S) (veblen (Om (1 + 1)) 1) := (veblen_lt_veblen_iff_right).2 h
    _ = veblen (Om (1 + 1)) 1 := veblen_veblen_of_lt tdK_lt_Om2 1

/-- `ψ_{Ω₂}(φ(K, Ω₂ + 1)) ≤ ψ_{Ω₂}(φ(Ω₂, 1))`. -/
theorem tjFK_le : S.psi (tdTop S) (Om (1 + 1)) ≤ S.psi (veblen (Om (1 + 1)) 1) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) tjTdTop_lt.le).1

/-- **The move of the atoms `ψ_{Ω₂}(φ(Ω₂, 1)) ≤ s ≤ θ`** (a hypothesis name). -/
def TjAtMove17 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (veblen (Om (1 + 1)) 1) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TjAtMove17` gives `Td.TdAtMove16`.** -/
theorem tjAtMove16_of17 (h : TjAtMove17 S) : TdAtMove16 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (veblen (Om (1 + 1)) 1) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) (tdTop_lim (S := S)).bot_lt (CSet.zero_mem _ _)).trans_le hsT
    exact tjAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Td.TdAtMove16` gives `TjAtMove17`.** -/
theorem tjAtMove17_of16 (h : TdAtMove16 S) : TjAtMove17 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (tjFK_le.trans hsT) hsθ IH

/-- **The road with `TjAtMove17`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem tjRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TjAtMove17 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tdRoadL hU hO hL hV hN hlh (fun hν => tjAtMove16_of17 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `tjRoadL` follows from that of `Td.tdRoadL`. -/
theorem tjRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TdAtMove16 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TjAtMove17 S :=
  fun hν => tjAtMove17_of16 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Tj
