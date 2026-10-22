import Googology.Trans.PoR.InaccPsi.R2.LjRed

/-!
# `LdEQhi` split at `θ⁺`, and the roads with the atom moves

`B_n = Bc.bcB S n`, `θ = ψ_{Ω₂}(Ω_ω)`, `θ⁺ = ψ_{Ω₂}(Ω_ω + 1)` (`Lj.ljThP`), `F_W = ψ_{Ω₂}(Ω₂^{Ω₂})`,
`r(λ) = k_λ(Θ_λ(m_λ))`, `δ_λ = υ_{λ+ω+1}`.

* `LjThMoveQ S` (a hypothesis name): **the reading moves at the codes `θ·ω < m_λ < θ⁺`**; `LjEQhi S`: **EQ at the codes
  `m_λ ≥ θ⁺`** (the only codes where `Θ_λ(m_λ)` can reach `δ_λ`);
* `ljLdEQhi_of_Q` (**`LjThMoveQ` and `LjEQhi` give `Ld.LdEQhi`**, given `L(ω+1) ≤ ν_C`: below `θ⁺` the reading is below
  `δ_λ` and `k_λ` moves by `Mv.mvk_move`), `ljThMoveQ_of`, `ljEQhi_of` (**`Ld.LdEQhi` gives both**: `k_{λ'}` is
  injective), `ljLdEQhi_iff`;
* `ljLeThMoveU_of_at`, `ljThMoveQ_of_at` (**`LjAtMove` gives `Le.LeThMoveU` and `LjThMoveQ`**);
* `ljRoadQ` (**the road** with `LeThMoveU`, `LjThMoveQ`, `LjEQhi`; its hypotheses follow from those of `Le.leRoadU`:
  `ljRoadQ_hyps`), `ljRoadA` (**the road** with `LjAtMove` and `LjEQhi` only).

No new axiom.  New definitions: the hypothesis names `LjThMoveQ`, `LjEQhi`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- **The reading moves at the codes `θ·ω < m_λ < θ⁺`.** -/
def LjThMoveQ (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ConjT.th S * ω < cdCode S l → cdCode S l < ljThP S →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **EQ at the codes `m_λ ≥ θ⁺`.** -/
def LjEQhi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ljThP S ≤ cdCode S l → Bc.bcB S n (cdR S l) = cdR S l'

/-- `Θ_λ(m_λ) < δ_λ` at a range restart with `m_λ ≤ θ⁺` below `L(n+2)`. -/
theorem ljTheta_lt_delta_R {n : ℕ} {l : Ordinal.{0}} (hR : CdRange S l) (hr : cdR S l < Bc.bcC S (n + 1))
    (hK : cdCode S l ≤ ljThP S) : cdTheta S l (cdCode S l) < cdDelta l := by
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hR.1 h2
  exact ljTheta_lt_delta hR.1 hX hown hK

/-- **`LjThMoveQ` and `LjEQhi` give `LdEQhi`** (given `L(ω+1) ≤ ν_C`). -/
theorem ljLdEQhi_of_Q (hν : Nc.ncL S (ω + 1) ≤ nuC) (hQ : LjThMoveQ S) (hE : LjEQhi S) : LdEQhi S := by
  intro n l l' hR h1 hr hl' hB hm hw
  by_cases hP : cdCode S l < ljThP S
  · have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
    have hΘδ := ljTheta_lt_delta_R hR hr hP.le
    have hΘ := hQ n l l' hR h1 hr hl' hB hm hw hP
    show Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l'))
    rw [← mvk_move hν hR.1 hl' h1 hδr hB hΘδ, hΘ]
  · exact hE n l l' hR h1 hr hl' hB hm (not_lt.1 hP)

/-- **`LdEQhi` gives `LjEQhi`.** -/
theorem ljEQhi_of (h : LdEQhi S) : LjEQhi S :=
  fun n l l' hR h1 hr hl' hB hm hP => h n l l' hR h1 hr hl' hB hm (ljThW_lt_ThP.trans_le hP)

/-- **`LdEQhi` gives `LjThMoveQ`** (given `L(ω+1) ≤ ν_C`): `k_{λ'}(B_n Θ_λ(m_λ)) = B_n r(λ) = r(λ')`, and `k_{λ'}` is
injective. -/
theorem ljThMoveQ_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (h : LdEQhi S) : LjThMoveQ S := by
  intro n l l' hR h1 hr hl' hB hm hw hP
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hΘδ := ljTheta_lt_delta_R hR hr hP.le
  have hEQ := h n l l' hR h1 hr hl' hB hm hw
  change Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) at hEQ
  rw [← mvk_move hν hR.1 hl' h1 hδr hB hΘδ] at hEQ
  exact (cdk_inj l').1 hEQ

/-- **`LdEQhi ⇔ LjThMoveQ ∧ LjEQhi`** (given `L(ω+1) ≤ ν_C`). -/
theorem ljLdEQhi_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) : LdEQhi S ↔ LjThMoveQ S ∧ LjEQhi S :=
  ⟨fun h => ⟨ljThMoveQ_of hν h, ljEQhi_of h⟩, fun h => ljLdEQhi_of_Q hν h.1 h.2⟩

/-- **`LjAtMove` gives `LeThMoveU`.** -/
theorem ljLeThMoveU_of_at (hat : LjAtMove S) : LeThMoveU S :=
  fun _ _ _ hR h1 hr hl' hB hm hF hw =>
    ljThMove_P hat hR h1 hr hl' hB hm hF (hw.trans_lt ljThW_lt_ThP)

/-- **`LjAtMove` gives `LjThMoveQ`.** -/
theorem ljThMoveQ_of_at (hat : LjAtMove S) : LjThMoveQ S :=
  fun _ _ _ hR h1 hr hl' hB hm hw hP =>
    ljThMove_P hat hR h1 hr hl' hB hm ((leFWW_lt_th.trans ldTh_lt_thw).trans hw).le hP

/-- **The road with `LeThMoveU`, `LjThMoveQ` and `LjEQhi`** (each under `L(ω+1) ≤ ν_C`). -/
theorem ljRoadQ (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → LeThMoveU S)
    (hQ : Nc.ncL S (ω + 1) ≤ nuC → LjThMoveQ S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → LjEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  leRoadU hU hO hL hV hN hlh hth (fun hν => ljLdEQhi_of_Q hν (hQ hν) (hhi hν))

/-- **Satisfiability**: the hypotheses `LjThMoveQ`, `LjEQhi` of `ljRoadQ` follow from `LdEQhi` of `Le.leRoadU`, so
`ljRoadQ` asks no more than `Le.leRoadU`. -/
theorem ljRoadQ_hyps (hhi : Nc.ncL S (ω + 1) ≤ nuC → LdEQhi S) :
    (Nc.ncL S (ω + 1) ≤ nuC → LjThMoveQ S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → LjEQhi S) :=
  ⟨fun hν => ljThMoveQ_of hν (hhi hν), fun hν => ljEQhi_of (hhi hν)⟩

/-- **The road with `LjAtMove` and `LjEQhi`** (each under `L(ω+1) ≤ ν_C`). -/
theorem ljRoadA (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → LjAtMove S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → LjEQhi S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ljRoadQ hU hO hL hV hN hlh (fun hν => ljLeThMoveU_of_at (hat hν)) (fun hν => ljThMoveQ_of_at (hat hν)) hhi

end Googology.Trans.PoR.InaccPsi.R2.Lj
