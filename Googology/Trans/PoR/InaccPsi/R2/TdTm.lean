import Googology.Trans.PoR.InaccPsi.R2.TdVeb

/-!
# Well-formed terms with Veblen nodes `φ(a, Ω₂ + Y)` for every level `a` below `K`

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `K = tdK S = ψ_{Ω₁}(Ω_ω)`, `TdSm S a`: `1 ≤ a < K`.  The terms,
contexts, values, images and own predicates
are those of `Ta` (`Ta.TaT`, `Ta.TaC`, `Ta.taV`, `Ta.taI`, `Ta.TaOwn`); only the well-formedness changes: a node
`phi a Y` is well formed for `TdSm S a` (in `Ta`: `a < Γ₀`).

* `TdWF`, `TdWFC`; `tdV_node`, `tdI_node`, `tdV_cat`, `tdI_cat`, `tdWF_cat`, `tdOwn_cat`;
* `tdSm_hull` (`a ∈ H_λ`, as `a < K ≤ ρ_λ`), `tdV_hull`, `tdV_lt_G3`, `tdDat` (**the data of an own term** above
  `T_{X₀ + W^{e(val)}}(b)`: at a node the level is below `K ≤ T` and below `K ≤ Θ T`).

No new axiom.  New definitions: `TdWF`, `TdWFC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-! ## Terms and contexts -/

/-- Well-formed terms: codes `1 ≤ c < Ω₂` at every coefficient, levels below `K` and nonzero arguments at the nodes. -/
def TdWF (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaT → Prop
  | .zero => True
  | .phi a Y => TdSm S a ∧ TdWF S l Y ∧ 1 ≤ taV Y ∧ 1 ≤ taI S l Y
  | .term P R c => TdWF S l P ∧ TdWF S l R ∧ GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧ c < Om (1 + 1)

/-- Well-formed contexts. -/
def TdWFC (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TdWFC S l K ∧ TdWF S l Q
  | .lft K => TdWFC S l K
  | .phi K a => TdWFC S l K ∧ TdSm S a

/-! ## Order and monotonicity -/

/-! ## Values of nonzero terms -/

/-- A node's value is a fixed point of `W^·`: `W^{φ(a, Ω₂ + Y)}·1 = φ(a, Ω₂ + Y)`. -/
theorem tdV_node {a : Ordinal.{0}} {Y : TaT} (ha : TdSm S a) (hY : 1 ≤ taV Y) :
    leWe (taV (TaT.phi a Y)) * 1 = taV (TaT.phi a Y) := by
  rw [mul_one]; exact taWe_veb (tdSm_ne0 ha) hY

theorem tdI_node {l a : Ordinal.{0}} {Y : TaT} (ha : TdSm S a) (hY : 1 ≤ taI S l Y)
    (h1 : (1 : Ordinal.{0}) ≤ upsilon l) :
    leOe (taI S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 = taI S l (TaT.phi a Y) := by
  rw [gxTh_small h1, mul_one]; exact taOe_veb (tdSm_ne0 ha) hY

/-! ## Concatenation -/

theorem tdV_cat {l : Ordinal.{0}} (A : TaT) : ∀ B : TaT, TdWF S l B → taV (taCat A B) = taV A + taV B
  | .zero, _ => (add_zero _).symm
  | .phi a Y, ⟨ha, _, hY, _⟩ => by
    show taV A + leWe (taV (TaT.phi a Y)) * 1 = taV A + taV (TaT.phi a Y)
    rw [tdV_node ha hY]
  | .term P R c, ⟨hP, _⟩ => by
    show taV (taCat A P) + leWe (taV R) * c = taV A + (taV P + leWe (taV R) * c)
    rw [tdV_cat A P hP, add_assoc]

theorem tdI_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (A : TaT) :
    ∀ B : TaT, TdWF S l B → taI S l (taCat A B) = taI S l A + taI S l B
  | .zero, _ => (add_zero _).symm
  | .phi a Y, ⟨ha, _, _, hY⟩ => by
    show taI S l A + leOe (taI S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 = taI S l A + taI S l (TaT.phi a Y)
    rw [tdI_node ha hY h1]
  | .term P R c, ⟨hP, _⟩ => by
    show taI S l (taCat A P) + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c =
      taI S l A + (taI S l P + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c)
    rw [tdI_cat h1 A P hP, add_assoc]

theorem tdWF_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l) {A : TaT} (hA : TdWF S l A) :
    ∀ B : TaT, TdWF S l B → TdWF S l (taCat A B)
  | .zero, _ => hA
  | .phi _ _, hB => ⟨hA, hB, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩
  | .term P R c, ⟨hP, hR, hc⟩ => ⟨tdWF_cat h1 hA P hP, hR, hc⟩

/-- The own predicate of a concatenation. -/
theorem tdOwn_cat {l b X0 : Ordinal.{0}} {A : TaT} : ∀ (B : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    TdWF S l B → TaOwn S b X0 e A → TaOwn S b X0 (fun y => e (taV A + y)) B → TaOwn S b X0 e (taCat A B)
  | .zero, _, _, _, hA, _ => hA
  | .phi a Y, e, he, _, hA, hB => by
    refine ⟨hA, ?_, sgLimC_one⟩
    show TaOwn S b X0 (fun y => e (taV A + leWe (veblen a (Om (1 + 1) + y)))) Y
    exact taOwn_mono le_rfl le_rfl Y _ _
      (fun _ _ h => he ((add_le_add_iff_left _).2 (taNode_mono _ a h)))
      (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono (taNode_mono _ a h))))
      (fun y => he ((add_le_add_iff_left _).2 (taLe_We _))) hB
  | .term P R c, e, he, ⟨hPw, _⟩, hA, ⟨hP, hR, hc⟩ => by
    have eV := tdV_cat A P hPw
    refine ⟨tdOwn_cat P e he hPw hA hP, ?_, ?_⟩
    · refine taOwn_mono le_rfl le_rfl R _ _
        (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => ?_) hR
      show e (taV A + (taV P + leWe y)) ≤ e (taV (taCat A P) + leWe y)
      rw [eV, add_assoc]
    · refine sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leMulWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => ?_) le_rfl le_rfl hc
      show e (taV A + (taV P + leWe (taV R) * z)) ≤ e (taV (taCat A P) + leWe (taV R) * z)
      rw [eV, add_assoc]

/-! ## The data of terms -/

section Data

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem tdSm_hull {a : Ordinal.{0}} (ha : TdSm S a) : a ∈ cdHull S l :=
  CSet.of_lt (tdSm_lt ha (tdK_le_rho hl hX))

theorem tdV_hull : ∀ t : TaT, TdWF S l t → taV t ∈ cdHull S l
  | .zero, _ => CSet.zero_mem _ _
  | .phi a Y, ⟨ha, hY, _, _⟩ => CSet.phi_mem (tdSm_hull hl hX ha) (CSet.add_mem (mxOm2_mem _ _) (tdV_hull Y hY))
  | .term P R c, ⟨hP, hR, hc, _, hcW⟩ =>
    CSet.add_mem (tdV_hull P hP) (leMulWe_mem (tdV_hull R hR) ((ldHull_iff hl hX hcW).2 hc))

/-- Values of well-formed terms are below `ψ_{Ω₃}(0)`, images below `ψ_{Ω₂}(0)`. -/
theorem tdV_lt_G3 : ∀ t : TaT, TdWF S l t →
    taV t < S.psi 0 (Om (1 + 1 + 1)) ∧ taI S l t < S.psi 0 (Om (1 + 1))
  | .zero, _ => ⟨rwG3_SC.1, rwG_SC.1⟩
  | .phi a Y, ⟨ha, hY, _, _⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨h1, h2⟩ := tdV_lt_G3 Y hY
    exact ⟨hG3.2 a (tdSm_lt ha tdK_le_G3) _ (hG3.isPrincipal rwW_lt_G3 h1),
      hG1.2 a (tdSm_lt ha (tdK_le_psi2 0)) _ (hG1.isPrincipal rwO_lt_G h2)⟩
  | .term P R c, ⟨hP, hR, _, _, hcW⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨hP1, hP2⟩ := tdV_lt_G3 P hP
    obtain ⟨hR1, hR2⟩ := tdV_lt_G3 R hR
    have hΘc := Sn.snTh_lt_Om1 hl hX hcW.le
    exact ⟨hG3.isPrincipal hP1 (ldMul_lt_SC hG3 (leWe_lt_SC hG3 rwW_lt_G3 hR1).1 (hcW.trans rwW_lt_G3)),
      hG1.isPrincipal hP2 (ldMul_lt_SC hG1 (leOe_lt_SC hG1 rwO_lt_G hR2).1 (hΘc.trans rwO_lt_G))⟩

/-- **The data of an own term above the bottom `T_{X₀ + W^{e(val)}}(b)`.** -/
theorem tdDat {b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TdWF S l t →
    TaOwn S b X0 e t →
    (∀ c, S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1)) ≤ c → taV t ∈ S.CSet 0 c) ∧
    (∀ c, gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1))) ≤ c →
      taI S l t ∈ S.CSet 0 c) ∧
    (∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (taV t)) ∧
    (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1))) ≤ Q →
      LeCl (Om 1) Q (taI S l t))
  | .zero, _, _, _, _ => ⟨fun _ _ => CSet.zero_mem _ _, fun _ _ => CSet.zero_mem _ _,
      fun Q hQ _ => LeCl.zero hQ.1, fun Q hQ _ => LeCl.zero hQ.1⟩
  | .phi a Y, e, he, ⟨ha, hYw, _, _⟩, hYo => by
    have he' : Monotone (fun y => e (veblen a (Om (1 + 1) + y))) := fun _ _ h => he (taNode_mono _ a h)
    obtain ⟨h1, h2, h3, h4⟩ := tdDat Y _ he' hYw hYo
    set T := S.psi (b + leWe (X0 + leWe (e (taV (TaT.phi a Y))))) (Om (1 + 1)) with hT
    have hgT : tdK S ≤ T := tdK_le_psi2 _
    have hgΘT : tdK S ≤ gxTh (upsilon l) (ldAtR S l) T := tdTh_K hl hX hgT
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun Q hQ hc => ?_, fun Q hQ hc => ?_⟩
    · exact CSet.phi_mem (tdSm_mem ha (hgT.trans hc)) (CSet.add_mem (mxOm2_mem _ _) (h1 c hc))
    · exact CSet.phi_mem (tdSm_mem ha (hgΘT.trans hc)) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (h2 c hc))
    · exact LeCl.phi (LeCl.small (tdSm_lt ha (hgT.trans hc))) (LeCl.add LeCl.om (h3 Q hQ hc))
    · exact LeCl.phi (LeCl.small (tdSm_lt ha (hgΘT.trans hc))) (LeCl.add LeCl.om (h4 Q hQ hc))
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPo, hRo, hco⟩ => by
    set T := S.psi (b + leWe (X0 + leWe (e (taV (TaT.term P R c))))) (Om (1 + 1)) with hT
    have hval : taV (TaT.term P R c) = taV P + leWe (taV R) * c := rfl
    have himg : taI S l (TaT.term P R c) = taI S l P + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c := rfl
    have hTmono : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (b + leWe (X0 + leWe (e x))) (Om (1 + 1)) ≤
        S.psi (b + leWe (X0 + leWe (e y))) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (he h)))))).1
    have heR : Monotone (fun r => e (taV P + leWe r)) := fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hG : Monotone (fun z => e (taV P + leWe (taV R) * z)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))
    have hPT := hTmono (show taV P ≤ taV (TaT.term P R c) from le_self_add)
    have hRT := hTmono (show taV P + leWe (taV R) ≤ taV (TaT.term P R c) from
      (add_le_add_iff_left _).2 (by simpa using leMulWe_mono (e := taV R) hc1))
    obtain ⟨hP1, hP2, hP3, hP4⟩ := tdDat P e he hPw hPo
    obtain ⟨hR1, hR2, hR3, hR4⟩ := tdDat R _ heR hRw hRo
    have hcT : c < T := sgCode_lt hG hco
    have hΘc : gxTh (upsilon l) (ldAtR S l) c < gxTh (upsilon l) (ldAtR S l) T := gxTh_lt hc hcT
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_, fun Q hQ hc' => ?_, fun Q hQ hc' => ?_⟩
    · rw [hval]
      exact CSet.add_mem (hP1 c' (hPT.trans hc'))
        (leMulWe_mem (hR1 c' (hRT.trans hc')) (CSet.of_lt (hcT.trans_le hc')))
    · rw [himg]
      exact CSet.add_mem (hP2 c' ((gxTh_mono hPT).trans hc'))
        (leMulOe_mem (hR2 c' ((gxTh_mono hRT).trans hc')) (CSet.of_lt (hΘc.trans_le hc')))
    · rw [hval]
      exact LeCl.add (hP3 Q hQ (hPT.trans hc')) (rvCl_mulOp hQ (LeCl.mulK hQ ldOm2_SC _ (hR3 Q hQ (hRT.trans hc')))
        ldOm2_SC _ (LeCl.small (hcT.trans_le hc')))
    · rw [himg]
      exact LeCl.add (hP4 Q hQ ((gxTh_mono hPT).trans hc'))
        (rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (hR4 Q hQ ((gxTh_mono hRT).trans hc'))) Ph.ph_SC_Om1 _
          (LeCl.small (hΘc.trans_le hc')))

end Data

end Googology.Trans.PoR.InaccPsi.R2.Td
