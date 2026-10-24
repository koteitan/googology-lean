import Googology.Trans.PoR.InaccPsi.R2.TgCont

/-!
# Terms with code levels: nodes `φ(a, Ω₂ + Y)` for every code `1 ≤ a < Ω₂` of `λ`, own levels and their data

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `T_y(b, X₀) = ψ_{Ω₂}(b + W^{X₀ + W^y})`, codes of `λ` =
`GxCl ρ_λ (ldAtR λ)`.  The terms and contexts are those of `Ta` (`Ta.TaT`, `Ta.TaC`, values `Ta.taV`); the image
reads the levels by `Θ` (`Td.tdIL`: `φ(a, Ω₂ + Y) ↦ φ(Θ a, Ω₁ + Ŷ)`).

* `TgWF` (**a node level is any code `1 ≤ a < Ω₂` of `λ`**), `TgNX` (every node off its fixed points),
  `TgOwn` (**the own predicate with the level condition**: at a node evaluated by `e`, `a < T_{e(φ(a, Ω₂ + Y))}`;
  at a coefficient `Sg.SgLimC` as in `Ta.TaOwn`);
* `tgWF_of_td`, `tgOwn_of_td` (**the terms of `Td` are terms of `Tg`**: a level `a < K` is below every `T`);
* `tgV_node`, `tgI_node`, `tgV_cat`, `tgI_cat`, `tgWF_cat`, `tgV_pos`, `tgV_hull`, `tgV_lt_G3`;
* `tgDat` (**THE DATA OF AN OWN TERM WITH CODE LEVELS** above `T_{e(val)}`: at a node the level is below `T` by
  the level condition, and `Θ a < Θ T`).

No new axiom.  New definitions: `TgWF`, `TgNX`, `TgOwn`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td

variable {S : InaccSeq.{0}}

/-- **Well-formed terms with code levels**: codes `1 ≤ c < Ω₂` at every coefficient, code levels `1 ≤ a < Ω₂` and
nonzero arguments at the nodes. -/
def TgWF (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaT → Prop
  | .zero => True
  | .phi a Y => GxCl (upsilon l) (ldAtR S l) a ∧ 1 ≤ a ∧ a < Om (1 + 1) ∧ TgWF S l Y ∧ 1 ≤ taV Y ∧
      1 ≤ tdIL S l Y
  | .term P R c => TgWF S l P ∧ TgWF S l R ∧ GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧ c < Om (1 + 1)

/-- **Every node off its fixed points**: `Ω₂ + Y < φ(a, Ω₂ + Y)`. -/
def TgNX : TaT → Prop
  | .zero => True
  | .phi a Y => Om (1 + 1) + taV Y < veblen a (Om (1 + 1) + taV Y) ∧ TgNX Y
  | .term P R _ => TgNX P ∧ TgNX R

/-- **The own predicate with the level condition**: `a < T_{e(φ(a, Ω₂ + Y))}` at a node, `Sg.SgLimC` at a
coefficient. -/
def TgOwn (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, .zero => True
  | e, .phi a Y => a < S.psi (b + leWe (X0 + leWe (e (veblen a (Om (1 + 1) + taV Y))))) (Om (1 + 1)) ∧
      TgOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | e, .term P R c => TgOwn S b X0 e P ∧ TgOwn S b X0 (fun r => e (taV P + leWe r)) R ∧
      SgLimC S (fun z => e (taV P + leWe (taV R) * z)) c b X0

/-! ## Values, images and concatenation -/

theorem tgV_node {a : Ordinal.{0}} {Y : TaT} (ha1 : 1 ≤ a) (hY : 1 ≤ taV Y) :
    leWe (taV (TaT.phi a Y)) * 1 = taV (TaT.phi a Y) := by
  rw [mul_one]; exact taWe_veb (zero_lt_one.trans_le ha1).ne' hY

theorem tgI_node {l a : Ordinal.{0}} {Y : TaT} (hΘa : 1 ≤ gxTh (upsilon l) (ldAtR S l) a) (hY : 1 ≤ tdIL S l Y)
    (h1 : (1 : Ordinal.{0}) ≤ upsilon l) :
    leOe (tdIL S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 = tdIL S l (TaT.phi a Y) := by
  rw [gxTh_small h1, mul_one]; exact taOe_veb (zero_lt_one.trans_le hΘa).ne' hY

theorem tgTh_one {l a : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (ha1 : 1 ≤ a) :
    1 ≤ gxTh (upsilon l) (ldAtR S l) a := by
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1
  exact hΘ1 ▸ gxTh_mono ha1

theorem tgV_cat {l : Ordinal.{0}} (A : TaT) : ∀ B : TaT, TgWF S l B → taV (taCat A B) = taV A + taV B
  | .zero, _ => (add_zero _).symm
  | .phi a Y, ⟨_, ha1, _, _, hY, _⟩ => by
    show taV A + leWe (taV (TaT.phi a Y)) * 1 = taV A + taV (TaT.phi a Y)
    rw [tgV_node ha1 hY]
  | .term P R c, ⟨hP, _⟩ => by
    show taV (taCat A P) + leWe (taV R) * c = taV A + (taV P + leWe (taV R) * c)
    rw [tgV_cat A P hP, add_assoc]

theorem tgI_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (A : TaT) :
    ∀ B : TaT, TgWF S l B → tdIL S l (taCat A B) = tdIL S l A + tdIL S l B
  | .zero, _ => (add_zero _).symm
  | .phi a Y, ⟨_, ha1, _, _, _, hY⟩ => by
    show tdIL S l A + leOe (tdIL S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 =
      tdIL S l A + tdIL S l (TaT.phi a Y)
    rw [tgI_node (tgTh_one h1 ha1) hY h1]
  | .term P R c, ⟨hP, _⟩ => by
    show tdIL S l (taCat A P) + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c =
      tdIL S l A + (tdIL S l P + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c)
    rw [tgI_cat h1 A P hP, add_assoc]

theorem tgWF_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l) {A : TaT} (hA : TgWF S l A) :
    ∀ B : TaT, TgWF S l B → TgWF S l (taCat A B)
  | .zero, _ => hA
  | .phi _ _, hB => ⟨hA, hB, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩
  | .term P _ _, ⟨hP, hR, hc⟩ => ⟨tgWF_cat h1 hA P hP, hR, hc⟩

theorem tgNX_cat {A : TaT} (hA : TgNX A) : ∀ B : TaT, TgNX B → TgNX (taCat A B)
  | .zero, _ => hA
  | .phi _ _, hB => ⟨hA, hB⟩
  | .term P _ _, ⟨hP, hR⟩ => ⟨tgNX_cat hA P hP, hR⟩

/-- A nonzero well-formed term has value and image `≥ 1`. -/
theorem tgV_pos {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) :
    ∀ Q : TaT, TgWF S l Q → Q ≠ TaT.zero → 1 ≤ taV Q ∧ 1 ≤ tdIL S l Q
  | .zero, _, h => absurd rfl h
  | .phi _ _, _, _ => ⟨Order.one_le_iff_pos.2 veblen_pos, Order.one_le_iff_pos.2 veblen_pos⟩
  | .term P R c, ⟨_, _, _, hc1, _⟩, _ => by
    have hΘc : 1 ≤ gxTh (upsilon l) (ldAtR S l) c := tgTh_one h1 hc1
    refine ⟨?_, ?_⟩
    · show 1 ≤ taV P + leWe (taV R) * c
      exact (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc1))).trans le_add_self
    · show 1 ≤ tdIL S l P + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c
      exact (Order.one_le_iff_pos.2 (mul_pos (leOe_pos _) (zero_lt_one.trans_le hΘc))).trans le_add_self

/-! ## The terms of `Td` -/

section Td

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The well-formed terms of `Td` (levels below `K`) are well formed with code levels.** -/
theorem tgWF_of_td : ∀ t : TaT, TdWF S l t → TgWF S l t
  | .zero, _ => trivial
  | .phi a Y, ⟨ha, hY, hY1, hI1⟩ =>
    ⟨GxCl.small (tdSm_lt ha (tdK_le_rho hl hX)), ha.1, tdSm_lt_Om2 ha, tgWF_of_td Y hY, hY1,
      by rw [tdIL_eq hl hX Y hY]; exact hI1⟩
  | .term P R c, ⟨hP, hR, hc⟩ => ⟨tgWF_of_td P hP, tgWF_of_td R hR, hc⟩

omit hl hX in
/-- **The own terms of `Td` are own with code levels**: a level `a < K` is below every `T`. -/
theorem tgOwn_of_td {b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), TdWF S l t →
    TaOwn S b X0 e t → TgOwn S b X0 e t
  | .zero, _, _, _ => trivial
  | .phi _ Y, _, ⟨ha, hY, _, _⟩, hYo => ⟨tdSm_lt ha (tdK_le_psi2 _), tgOwn_of_td Y _ hY hYo⟩
  | .term P R _, e, ⟨hP, hR, _⟩, ⟨hPo, hRo, hco⟩ => ⟨tgOwn_of_td P e hP hPo, tgOwn_of_td R _ hR hRo, hco⟩

end Td

/-! ## The data of terms -/

section Data

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem tgV_hull : ∀ t : TaT, TgWF S l t → taV t ∈ cdHull S l
  | .zero, _ => CSet.zero_mem _ _
  | .phi _ Y, ⟨hac, _, haW, hY, _, _⟩ =>
    CSet.phi_mem ((ldHull_iff hl hX haW).2 hac) (CSet.add_mem (mxOm2_mem _ _) (tgV_hull Y hY))
  | .term P R _, ⟨hP, hR, hc, _, hcW⟩ =>
    CSet.add_mem (tgV_hull P hP) (leMulWe_mem (tgV_hull R hR) ((ldHull_iff hl hX hcW).2 hc))

/-- Values of well-formed terms are below `ψ_{Ω₃}(0)`, images below `ψ_{Ω₂}(0)`. -/
theorem tgV_lt_G3 : ∀ t : TaT, TgWF S l t →
    taV t < S.psi 0 (Om (1 + 1 + 1)) ∧ tdIL S l t < S.psi 0 (Om (1 + 1))
  | .zero, _ => ⟨rwG3_SC.1, rwG_SC.1⟩
  | .phi a Y, ⟨_, _, haW, hY, _, _⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨h1, h2⟩ := tgV_lt_G3 Y hY
    exact ⟨hG3.2 a (haW.trans rwW_lt_G3) _ (hG3.isPrincipal rwW_lt_G3 h1),
      hG1.2 _ ((Sn.snTh_lt_Om1 hl hX haW.le).trans rwO_lt_G) _ (hG1.isPrincipal rwO_lt_G h2)⟩
  | .term P R c, ⟨hP, hR, _, _, hcW⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨hP1, hP2⟩ := tgV_lt_G3 P hP
    obtain ⟨hR1, hR2⟩ := tgV_lt_G3 R hR
    have hΘc := Sn.snTh_lt_Om1 hl hX hcW.le
    exact ⟨hG3.isPrincipal hP1 (ldMul_lt_SC hG3 (leWe_lt_SC hG3 rwW_lt_G3 hR1).1 (hcW.trans rwW_lt_G3)),
      hG1.isPrincipal hP2 (ldMul_lt_SC hG1 (leOe_lt_SC hG1 rwO_lt_G hR2).1 (hΘc.trans rwO_lt_G))⟩

omit hl hX in
/-- **THE DATA OF AN OWN TERM WITH CODE LEVELS above the bottom `T_{X₀ + W^{e(val)}}(b)`.** -/
theorem tgDat {b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TgWF S l t →
    TgOwn S b X0 e t →
    (∀ c, S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1)) ≤ c → taV t ∈ S.CSet 0 c) ∧
    (∀ c, gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1))) ≤ c →
      tdIL S l t ∈ S.CSet 0 c) ∧
    (∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (taV t)) ∧
    (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (taV t)))) (Om (1 + 1))) ≤ Q →
      LeCl (Om 1) Q (tdIL S l t))
  | .zero, _, _, _, _ => ⟨fun _ _ => CSet.zero_mem _ _, fun _ _ => CSet.zero_mem _ _,
      fun Q hQ _ => LeCl.zero hQ.1, fun Q hQ _ => LeCl.zero hQ.1⟩
  | .phi a Y, e, he, ⟨hac, _, _, hYw, _, _⟩, ⟨haT, hYo⟩ => by
    have he' : Monotone (fun y => e (veblen a (Om (1 + 1) + y))) := fun _ _ h => he (taNode_mono _ a h)
    obtain ⟨h1, h2, h3, h4⟩ := tgDat Y _ he' hYw hYo
    have hΘa : gxTh (upsilon l) (ldAtR S l) a <
        gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (taV (TaT.phi a Y))))) (Om (1 + 1))) :=
      gxTh_lt hac haT
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun Q hQ hc => ?_, fun Q hQ hc => ?_⟩
    · exact CSet.phi_mem (CSet.of_lt (haT.trans_le hc)) (CSet.add_mem (mxOm2_mem _ _) (h1 c hc))
    · exact CSet.phi_mem (CSet.of_lt (hΘa.trans_le hc)) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (h2 c hc))
    · exact LeCl.phi (LeCl.small (haT.trans_le hc)) (LeCl.add LeCl.om (h3 Q hQ hc))
    · exact LeCl.phi (LeCl.small (hΘa.trans_le hc)) (LeCl.add LeCl.om (h4 Q hQ hc))
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, _⟩, ⟨hPo, hRo, hco⟩ => by
    set T := S.psi (b + leWe (X0 + leWe (e (taV (TaT.term P R c))))) (Om (1 + 1)) with hT
    have hval : taV (TaT.term P R c) = taV P + leWe (taV R) * c := rfl
    have himg : tdIL S l (TaT.term P R c) = tdIL S l P + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c := rfl
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
    obtain ⟨hP1, hP2, hP3, hP4⟩ := tgDat P e he hPw hPo
    obtain ⟨hR1, hR2, hR3, hR4⟩ := tgDat R _ heR hRw hRo
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

end Googology.Trans.PoR.InaccPsi.R2.Tg
