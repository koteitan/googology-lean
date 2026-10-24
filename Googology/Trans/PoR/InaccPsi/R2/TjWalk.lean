import Googology.Trans.PoR.InaccPsi.R2.TjGen

/-!
# The bridge: the closure condition gives the strong level condition at every node

`W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, `G = φ(Ω₂, 1)`, codes = `Le.LeCl Ω₂ Q`, `CL E` the closure condition
(`E` a code over every strongly critical `Q ≥ T_E`), `Sj.SjDesc` the descent property.

* `tjWalk` (**THE WALK**: along a term with `Tg.TgOwn`, a descent map `e`, `e(val) ≤ E < e(G)`, every node
  `φ(a, Ω₂ + Y)` has the strong level condition: for every `η ≤ a`, `η < T_{e(φ(η, Ω₂ + 1))}`, by the code gap
  `Tg.tgLevOwnF` at the node value `φ(η, Ω₂ + 1) > Ω₂`);
* `tjOwn_of_cl` (**THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES `TjOwn id` OF ITS
  NORMAL-FORM TERM**, with `Tg.tgOwn_of_cl` for the coefficients).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

variable {S : InaccSeq.{0}}

section Walk

variable {l : Ordinal.{0}} {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **THE WALK: every node gets the strong level condition** by the code gap below `φ(Ω₂, 1)`. -/
theorem tjWalk : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TgWF S l t → TgOwn S β X0 e t →
    (∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e 0))) (Om (1 + 1)) ≤ Q → SjDesc Q e) →
    e (taV t) ≤ E → E < e (veblen (Om (1 + 1)) 1) → taV t < veblen (Om (1 + 1)) 1 → TjOwn S β X0 e t
  | .zero, _, _, _, _, _, _, _, _ => trivial
  | .phi a Y, e, he, ⟨_, _, haW, hYw, hY1, _⟩, ⟨_, hYo⟩, hD, hEt, hEG, hvG => by
    have he' : Monotone (fun y => e (veblen a (Om (1 + 1) + y))) := fun _ _ h => he (taNode_mono _ a h)
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe ((fun y => e (veblen a (Om (1 + 1) + y))) 0)))
        (Om (1 + 1)) ≤ Q → SjDesc Q (fun y => e (veblen a (Om (1 + 1) + y))) :=
      fun Q hQ hQb => tgDesc_node hQ haW (hD Q hQ ((tjT_mono le_rfl le_rfl (he zero_le)).trans hQb))
    refine ⟨fun η hη => ?_, tjWalk Y _ he' hYw hYo hD' hEt ?_ ((taLe_node _ a _).trans_lt hvG)⟩
    · have hΩ : Om (1 + 1) < veblen η (Om (1 + 1) + 1) := (lt_add_one _).trans_le (right_le_veblen η _)
      have hlo : e (veblen η (Om (1 + 1) + 1)) ≤ E :=
        (he ((veblen_left_monotone _ hη).trans (taNode_mono _ a hY1))).trans hEt
      exact tgLevOwnF hβd hβown hX0cl hX0G3 hEcl he hD hΩ le_rfl hlo hEG
    · exact hEG.trans_le (he ((le_add_self.trans (right_le_veblen a _))))
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPo, hRo, hco⟩, hD, hEt, hEG, hvG => by
    have hTm : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (β + leWe (X0 + leWe x)) (Om (1 + 1)) ≤
        S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) := fun h => tjT_mono le_rfl le_rfl h
    have hWR : leWe (taV R) ≤ leWe (taV R) * c := by simpa using leMulWe_mono (e := taV R) hc1
    have hPG : taV P < veblen (Om (1 + 1)) 1 :=
      (le_self_add : taV P ≤ taV P + leWe (taV R) * c).trans_lt hvG
    have hRG : taV R < veblen (Om (1 + 1)) 1 :=
      ((taLe_We _).trans (hWR.trans (le_add_self : leWe (taV R) * c ≤ taV P + leWe (taV R) * c))).trans_lt hvG
    have hPle : e (taV P) ≤ E := (he (le_self_add : taV P ≤ taV P + leWe (taV R) * c)).trans hEt
    have hPcl := (tgDat (b := β) (X0 := X0) P e he hPw hPo).2.2.1
    have he' : Monotone (fun r => e (taV P + leWe r)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hD' : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe (e (taV P + leWe 0)))) (Om (1 + 1)) ≤ Q →
        SjDesc Q (fun r => e (taV P + leWe r)) := by
      intro Q hQ hQb u V z hz h1 h2
      obtain ⟨w, hw, hw1, hw2⟩ := hD Q hQ ((hTm (he zero_le)).trans hQb) _ _ z hz h1 h2
      have hPQ : LeCl (Om (1 + 1)) Q (taV P) := hPcl Q hQ ((hTm (he le_self_add)).trans hQb)
      have hPw' : taV P ≤ w := le_self_add.trans hw1
      have hwP := (leClDec hQ ldOm2_SC w hw).1 _ hPQ hPw'
      have e1 : taV P + (w - taV P) = w := Ordinal.add_sub_cancel_of_le hPw'
      have h3 : leWe u ≤ w - taV P := (add_le_add_iff_left (taV P)).1 (by rw [e1]; exact hw1)
      have h4 : w - taV P < leWe V := (add_lt_add_iff_left (taV P)).1 (by rw [e1]; exact hw2)
      obtain ⟨h5, h6⟩ := sjLogW h3 h4
      exact ⟨_, sjCl_div hQ ldOm2_SC _ (leClDec hQ ldOm2_SC _ hwP).2, h5, h6⟩
    have hRle : e (taV P + leWe (taV R)) ≤ E := (he ((add_le_add_iff_left _).2 hWR)).trans hEt
    have hEG' : E < e (taV P + leWe (veblen (Om (1 + 1)) 1)) := by
      rw [tgWe_G]; exact hEG.trans_le (he le_add_self)
    exact ⟨tjWalk P e he hPw hPo hD hPle hEG hPG, tjWalk R _ he' hRw hRo hD' hRle hEG' hRG, hco⟩

end Walk

section All

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE CLOSURE CONDITION OF `E ∈ H_λ`, `E < φ(Ω₂, 1)`, AT A PROPER BASE GIVES `TjOwn id` OF ITS NORMAL-FORM
TERM**: the strong level condition at every node, `Sg.SgLimC` at every coefficient. -/
theorem tjOwn_of_cl {β X0 E : Ordinal.{0}} (hβd : leWe (X0 + leWe E) ∣ β)
    (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hX0m : X0 ∈ S.CSet 0 (S.psi (β + leWe X0) (Om (1 + 1))))
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
    (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
    (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)
    (hEH : E ∈ cdHull S l) (hE : E < veblen (Om (1 + 1)) 1) : TjOwn S β X0 (fun y => y) (taTm E) := by
  obtain ⟨hw, -, hv⟩ := tgTm_spec hl hX E hEH hE
  have hTg := tgOwn_of_cl hl hX hβd hβown hX0m hX0cl hX0G3 hEcl hEH hE
  exact tjWalk hβd hβown hX0cl hX0G3 hEcl (taTm E) (fun y => y) (fun _ _ h => h) hw hTg
    (fun Q _ _ => sjDesc_id Q) (by rw [hv]) hE (by rw [hv]; exact hE)

end All

end Googology.Trans.PoR.InaccPsi.R2.Tj
