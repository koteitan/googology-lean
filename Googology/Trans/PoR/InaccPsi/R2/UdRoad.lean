import Googology.Trans.PoR.InaccPsi.R2.UdMove

/-!
# The atom move below `ψ_{Ω₂}(ψ_{Ω₃}(0))` and the road

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)` (`Ud.udGam_eq`),
`θ = ConjT.th S`.

* `udAtMoveTop` (**EVERY ATOM `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(ψ_{Ω₃}(0))` MOVES** once the codes below it move: `s` is below
  `ψ_{Ω₂}(W^{W^{X_k}})` for some `k` (`Ud.udPsi_Gam`), and `St.stAtMoveG` with `Ud.udLSX k`, `Ud.udLSBX k`);
* `UdAtMove25` (**`LjAtMove` for the atoms `ψ_{Ω₂}(ψ_{Ω₃}(0)) ≤ s ≤ θ`**), `udAtMove24_of25`, `udAtMove25_of24`,
  `udAtMove17_of25` (`UdAtMove25 ⇒ Tj.TjAtMove17`), `udAtMove10_of25` (`UdAtMove25 ⇒ Rw.RwAtMove10`);
* `udLS_wall` (**every level system `St.StLS S λ E_b Th` has `E_b < Γ₂`**: the atoms `≥ ψ_{Ω₂}(ψ_{Ω₃}(0))` need
  exponents `≥ ψ_{Ω₃}(0)`, outside the present level systems);
* `udRoad` (**the road of `Ua.uaRoad` with `UdAtMove25`** in place of `Ua.UaAtMove24`), `udRoad_hyps`.

No new axiom.  New definition: the statement name `UdAtMove25`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ud

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
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **EVERY ATOM `ψ_{Ω₂}(0) < s < ψ_{Ω₂}(Γ₂)` MOVES** once the codes below it move. -/
theorem udAtMoveTop {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi uaGam (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨k, hk⟩ := udPsi_Gam hsT
  exact stAtMoveG (fun _ _ hl hX => udLSX hl hX k) (fun _ _ _ _ _ hl hX hl' hX' => udLSBX hl hX hl' hX' k)
    hR h1 hr hl' hB s hs hs0 hk IH

/-- **The same with the bound written `ψ_{Ω₂}(ψ_{Ω₃}(0))`.** -/
theorem udAtMoveTop3 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (s : Ordinal.{0}) (hs : s ∈ ldAtR S l) (hs0 : S.psi 0 (Om (1 + 1)) < s)
    (hsT : s < S.psi (S.psi 0 (Om (1 + 1 + 1))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  udAtMoveTop hR h1 hr hl' hB s hs hs0 (by rw [udGam_eq]; exact hsT) IH

/-- `ψ_{Ω₂}(W^{W^{X₃}}) ≤ ψ_{Ω₂}(Γ₂)`. -/
theorem udF_le : S.psi (leWe (leWe uaX3)) (Om (1 + 1)) ≤ S.psi uaGam (Om (1 + 1)) := by
  have hW : leWe uaGam = uaGam := (uaWfix (gg_SC_eps uaGam_spec.1) uaGam_spec.2).2
  refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
  calc leWe (leWe uaX3) ≤ leWe (leWe uaGam) := leWe_mono (leWe_mono uaX3_lt_Gam.le)
    _ = uaGam := by rw [hW, hW]

/-- **`LjAtMove` for the atoms `ψ_{Ω₂}(ψ_{Ω₃}(0)) ≤ s ≤ θ`.** -/
def UdAtMove25 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (S.psi 0 (Om (1 + 1 + 1))) (Om (1 + 1)) ≤ s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`UdAtMove25` gives `Ua.UaAtMove24`.** -/
theorem udAtMove24_of25 (h : UdAtMove25 S) : UaAtMove24 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH
  rcases lt_or_ge s (S.psi uaGam (Om (1 + 1))) with hlt | hge
  · have hsT' := uaF_le.trans hsT
    have hs0 : S.psi 0 (Om (1 + 1)) < s :=
      (psi_lt_psi_of_mem (InR_Om_succ 1) tjG_lim.bot_lt (CSet.zero_mem _ _)).trans_le
        (tnG_le_FN.trans (tuFN_le.trans (tuFU_le.trans (tuFE_le.trans (txF_le.trans (txF2_le.trans hsT'))))))
    exact udAtMoveTop hR h1 hr hl' hB s hs hs0 hlt IH
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs (by rw [← udGam_eq]; exact hge) hsθ IH

/-- **`Ua.UaAtMove24` gives `UdAtMove25`.** -/
theorem udAtMove25_of24 (h : UaAtMove24 S) : UdAtMove25 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsT hsθ IH =>
    h n l l' hR h1 hr hl' hB hm hF hK s hs (udF_le.trans (by rw [udGam_eq]; exact hsT)) hsθ IH

/-- **`UdAtMove25` gives `Tj.TjAtMove17`.** -/
theorem udAtMove17_of25 (h : UdAtMove25 S) : TjAtMove17 S := uaAtMove17_of24 (udAtMove24_of25 h)

/-- **`UdAtMove25` gives `Rw.RwAtMove10`** (through `Tj.TjAtMove17`, `Td.TdAtMove16`, …, `Sn.SnAtMove11`). -/
theorem udAtMove10_of25 (h : UdAtMove25 S) : RwAtMove10 S :=
  snAtMove10_of11 (sqAtMove11_of12 (stAtMove12_of13 (swAtMove13_of14 (taAtMove14_of15
    (tdAtMove15_of16 (tjAtMove16_of17 (udAtMove17_of25 h)))))))

/-- **THE WALL OF THE LEVEL SYSTEMS**: every `St.StLS S λ E_b Th` has `E_b < Γ₂ = ψ_{Ω₃}(0)`; the exponents
`≥ Γ₂` of the atoms `ψ_{Ω₂}(ψ_{Ω₃}(0)) ≤ s ≤ θ` lie outside every level system of the present kind. -/
theorem udLS_wall {l Eb : Ordinal.{0}} {Th : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}} (h : StLS S l Eb Th) :
    Eb < uaGam := by
  rw [udGam_eq]; exact h.ltG3

/-- **The road with `UdAtMove25`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem udRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → UdAtMove25 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  uaRoad hU hO hL hV hN hlh (fun hν => udAtMove24_of25 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `udRoad` follows from that of `Ua.uaRoad`. -/
theorem udRoad_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → UaAtMove24 S) :
    Nc.ncL S (ω + 1) ≤ nuC → UdAtMove25 S :=
  fun hν => udAtMove25_of24 (hat hν)

end Googology.Trans.PoR.InaccPsi.R2.Ud
