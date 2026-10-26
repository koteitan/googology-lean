import Googology.Trans.PoR.InaccPsi.R2.UxB

/-!
# The atom move below `ψ_{Ω₂}(Y₃)` and the road with the atom hypothesis only on `[ψ_{Ω₂}(Y₃), θ]`

`B_n = Bc.bcB S n`, `Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `Γ₂ = ψ_{Ω₃}(0)`, `Y₃ = ψ_{Ω₃}(Ω₃)`,
`θ = ConjT.th S`, `θ⁺ = Lj.ljThP`.

* `uxAtMoveTop` (**EVERY ATOM `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(Y₃)` MOVES** once the codes below it move: `Ux.uxAtMoveG` with
  the level system `Uu.uuLSY` of all levels below `Y₃` and its move `Ux.uxLSB_Y`; `Y₃ ≤ W^{W^{Y₃}}`);
* `UxAtMove26` (**the atom move for the atoms `ψ_{Ω₂}(Y₃) ≤ s ≤ θ`**), `uxAtMove25_of26` (**`UxAtMove26 ⇒
  Ud.UdAtMove25`**: the atoms in `[ψ_{Ω₂}(ψ_{Ω₃}(0)), ψ_{Ω₂}(Y₃))` move with no hypothesis), `uxAtMove26_of25`,
  `uxAtMove10_of26` (`UxAtMove26 ⇒ Rw.RwAtMove10`);
* `uxRoad` (**the road of `Ud.udRoad` with `UxAtMove26` in place of `Ud.UdAtMove25`**), `uxRoad_hyps`;
* `uxTh_Y_wall` (**THE WALL AT `Y₃`**: `Ug.ugTh S λ Y₃ = 0`; `Y₃` is strongly critical, not `ψ₃` of a normal
  argument below it and not a Veblen node, so the image `T` of the levels stops at `Y₃`, where `T Y₃ = ψ_{Ω₂}(Ω₂)`
  is expected; the levels `≥ Y₃` of the atoms `≥ ψ_{Ω₂}(Y₃)` need `Ω₃ ↦ Ω₂` and the `ψ₄`-atoms).

No new axiom.  New definition: the statement name `UxAtMove26`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ux

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uj Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Uu

variable {S : InaccSeq.{0}}

/-- `Y₃ ≤ W^{W^{Y₃}}`. -/
theorem uxY_le_WW : ugY S ≤ leWe (leWe (ugY S)) := (ujLe_We _).trans (leWe_mono (ujLe_We _))

/-- **EVERY ATOM `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(Y₃)` MOVES** once the codes below it move. -/
theorem uxAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsY : s < S.psi (ugY S) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  uxAtMoveG (Eb := ugY S) (Th := ugTh S) (fun _ _ hl hX => uuLSY hl hX)
    (fun _ _ _ _ _ hl hX hl' hX' => uxLSB_Y hl hX hl' hX') hR h1 hr hl' hB s hs hs0
    (hsY.trans_le (psi_mono (S := S) (InR_Om_succ 1) uxY_le_WW).1) IH

/-- **The atom move for the atoms `ψ_{Ω₂}(Y₃) ≤ s ≤ θ`.** -/
def UxAtMove26 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (ugY S) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- `ψ_{Ω₂}(0) < ψ_{Ω₂}(ψ_{Ω₃}(0))`. -/
theorem uxG1_lt : S.psi 0 (Om (1 + 1)) < S.psi (S.psi 0 (Om (1 + 1 + 1))) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (SC_psi ugInR3 0).1 (CSet.zero_mem _ _)

/-- `ψ_{Ω₂}(ψ_{Ω₃}(0)) ≤ ψ_{Ω₂}(Y₃)`. -/
theorem uxGam_le_Y : S.psi (S.psi 0 (Om (1 + 1 + 1))) (Om (1 + 1)) ≤ S.psi (ugY S) (Om (1 + 1)) :=
  (psi_mono (S := S) (InR_Om_succ 1) ujG3_lt_Y.le).1

/-- **`UxAtMove26` gives `Ud.UdAtMove25`**: the atoms in `[ψ_{Ω₂}(ψ_{Ω₃}(0)), ψ_{Ω₂}(Y₃))` move with no hypothesis. -/
theorem uxAtMove25_of26 (h : UxAtMove26 S) : UdAtMove25 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsG hsθ IH
  rcases lt_or_ge s (S.psi (ugY S) (Om (1 + 1))) with hlt | hge
  · exact uxAtMoveTop hR h1 hr hl' hB s hs (uxG1_lt.trans_le hsG) hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hge hsθ IH

/-- **`Ud.UdAtMove25` gives `UxAtMove26`.** -/
theorem uxAtMove26_of25 (h : UdAtMove25 S) : UxAtMove26 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsY hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (uxGam_le_Y.trans hsY) hsθ IH

/-- **`UxAtMove26` gives `Rw.RwAtMove10`.** -/
theorem uxAtMove10_of26 (h : UxAtMove26 S) : RwAtMove10 S := udAtMove10_of25 (uxAtMove25_of26 h)

/-- **The road with `UxAtMove26`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem uxRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → UxAtMove26 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  udRoad hU hO hL hV hN hlh (fun hν => uxAtMove25_of26 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `uxRoad` follows from that of `Ud.udRoad`. -/
theorem uxRoad_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → UdAtMove25 S) :
    Nc.ncL S (ω + 1) ≤ nuC → UxAtMove26 S :=
  fun hν => uxAtMove26_of25 (hat hν)

/-- **THE WALL AT `Y₃`**: the image of the levels is `0` at `Y₃ = ψ_{Ω₃}(Ω₃)`. -/
theorem uxTh_Y_wall (l : Ordinal.{0}) : ugTh S l (ugY S) = 0 := by
  have hSC : SC (ugY S) := uqY_SC
  have hW : Om (1 + 1 : Ordinal.{0}) < ugY S := uqW_lt_Y
  have h1 : ¬ Sg.sgLW (ugY S) < ugY S := by rw [(ugSC_W hSC hW).1]; exact lt_irrefl _
  have h3 : ¬ (ugD S (ugY S) < ugY S ∧ S.psi (ugD S (ugY S)) (Om (1 + 1 + 1)) = ugY S) := fun h => by
    have := uxPsi3_lt_Y h.1; rw [h.2] at this; exact lt_irrefl _ this
  have h2 : ¬ (invVeblen₁ (ugY S) < ugY S ∧ invVeblen₂ (ugY S) < ugY S) := fun h =>
    (Uc.uc_SC_facts hSC).2 h.1
  rw [ugTh, dif_neg (not_lt.2 uxGam_lt_Y.le), dif_neg h1, dif_neg h3, dif_neg h2]

end Googology.Trans.PoR.InaccPsi.R2.Ux
