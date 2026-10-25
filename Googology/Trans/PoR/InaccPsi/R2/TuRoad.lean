import Googology.Trans.PoR.InaccPsi.R2.TuSys

/-!
# The atoms below `ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂}}})` move, and the road with the atoms above them

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `G = φ(Ω₂, 1)`,
`F_U = ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂}}})` (the new bound), `θ⁺ = Lj.ljThP`.

* `tuAtMoveTop` (**every atom `ψ_{Ω₂}(0) < s < F_U` moves** once the codes below it move: `St.stAtMoveG` for the
  system `Tu.tuLS` with its move `Tu.tuLSB`; no other hypothesis);
* `tuFN_le` (`ψ_{Ω₂}(W^{W^{G+Ω₂³}}) ≤ F_U`);
* `TuAtMove19 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_U ≤ s ≤ θ`; `tuAtMove18_of19`
  (**`TuAtMove19` gives `Tn.TnAtMove18`**), `tuAtMove19_of18` (the converse), `tuAtMove17_of19`
  (**`TuAtMove19` gives `Tj.TjAtMove17`**), `tuRoadL` (**the road**), `tuRoadL_hyps`.

No new axiom.  New definition: the hypothesis name `TuAtMove19`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- **Every atom `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂}}})` moves** once the codes below it move. -/
theorem tuAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (leWe (leWe (tuGB S))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  stAtMoveG (fun _ _ hl hX => tuLS hl hX) (fun _ _ _ _ _ hl hX hl' hX' => tuLSB hl hX hl' hX')
    hR h1 hr hl' hB s hs hs0 hsT IH

/-- `G + Ω₂³ ≤ G + Ω₂^{Ω₂}`. -/
theorem tuGW3_le : tnGW3 S ≤ tuGB S := by
  unfold tnGW3 tuGB
  refine (add_le_add_iff_left _).2 ?_
  rw [← tnW3_opow]
  exact opow_le_opow_right omega0_pos (mul_le_mul_left' (le_of_lt (by
    have h3 : (1 + 1 + 1 : Ordinal.{0}) < ω := by
      have : (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) := by norm_num
      rw [this]; exact nat_lt_omega0 3
    exact h3.trans (Lw.lw_omega_lt_SC ldOm2_SC))) _)

/-- `ψ_{Ω₂}(W^{W^{G + Ω₂³}}) ≤ ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂}}})`. -/
theorem tuFN_le :
    S.psi (leWe (leWe (tnGW3 S))) (Om (1 + 1)) ≤ S.psi (leWe (leWe (tuGB S))) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (leWe_mono tuGW3_le))).1

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(W^{W^{G + Ω₂^{Ω₂}}}) ≤ s ≤ θ`.** -/
def TuAtMove19 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (tuGB S))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`TuAtMove19` gives `Tn.TnAtMove18`.** -/
theorem tuAtMove18_of19 (h : TuAtMove19 S) : TnAtMove18 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi (leWe (leWe (tuGB S))) (Om (1 + 1))) with hlt | hge
  · have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le (tnG_le_FN.trans hsT)
    exact tuAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Tn.TnAtMove18` gives `TuAtMove19`.** -/
theorem tuAtMove19_of18 (h : TnAtMove18 S) : TuAtMove19 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (tuFN_le.trans hsT) hsθ IH

/-- **`TuAtMove19` gives `Tj.TjAtMove17`.** -/
theorem tuAtMove17_of19 (h : TuAtMove19 S) : TjAtMove17 S := tnAtMove17_of18 (tuAtMove18_of19 h)

/-- **The road with `TuAtMove19`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem tuRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → TuAtMove19 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tnRoadL hU hO hL hV hN hlh (fun hν => tuAtMove18_of19 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `tuRoadL` follows from that of `Tn.tnRoadL`. -/
theorem tuRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → TnAtMove18 S) :
    Nc.ncL S (ω + 1) ≤ nuC → TuAtMove19 S :=
  fun hν => tuAtMove19_of18 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Tu
