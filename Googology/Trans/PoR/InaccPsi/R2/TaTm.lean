import Googology.Trans.PoR.InaccPsi.R2.TaVeb

/-!
# Exponent terms with Veblen nodes `φ(a, Ω₂ + Y)`, generic in the small Veblen level `a`

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `TaSm a`: `1 ≤ a < Γ₀`.

**Terms** `TaT`: `zero`, `phi a Y` (**the Veblen node**, value `φ(a, Ω₂ + Y)`, image `φ(a, Ω₁ + Ŷ)`; for `Y ≥ 1`
it is a fixed point of `W^·`: `ε_{Ω₂+1+k}` is `phi 1 (k+1)`, `ζ_{Ω₂+1}` is `phi 2 1`), `term P R c = P + W^R·c`.
**Contexts** `TaC`: `hole`, `pfx K Q = K(Q + _)`, `lft K = K(W^_)`, `phi K a = K(φ(a, Ω₂ + _))`.
`taCat A B` has the value `A + B` (`A ⊕ phi a Y = A + W^{φ(a, Ω₂ + Y)}·1`).
The own predicate `TaOwn` is `Sg.SgOwn` with the evaluation passed through `φ(a, Ω₂ + ·)` at a node.

* `taE_normal` (**every context is a normal function**), `taOwn_mono`, `taOwnC_mono`, `taV_cat`, `taI_cat`,
  `taOwn_cat`, `taV_hull`, `taV_lt_G3`, `taDat` (**the data of an own term**: as `Sw.swDat`, through the nodes).

No new axiom.  New definitions: `TaT`, `TaC`, `taV`, `taI`, `taE`, `taEh`, `TaWF`, `TaWFC`, `TaOwn`, `TaOwnC`,
`taCat`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-! ## Terms and contexts -/

/-- **Exponent terms with Veblen nodes**: `zero`, `phi a Y` (`φ(a, Ω₂ + Y)`), `term P R c = P + W^R·c`. -/
inductive TaT : Type 1
  | zero : TaT
  | phi : Ordinal.{0} → TaT → TaT
  | term : TaT → TaT → Ordinal.{0} → TaT

/-- **Contexts**: `hole`, `pfx K Q = K(Q + _)`, `lft K = K(W^_)`, `phi K a = K(φ(a, Ω₂ + _))`. -/
inductive TaC : Type 1
  | hole : TaC
  | pfx : TaC → TaT → TaC
  | lft : TaC → TaC
  | phi : TaC → Ordinal.{0} → TaC

/-- The value of a term. -/
noncomputable def taV : TaT → Ordinal.{0}
  | .zero => 0
  | .phi a Y => veblen a (Om (1 + 1) + taV Y)
  | .term P R c => taV P + leWe (taV R) * c

/-- The image of a term (`Ω₂ ↦ Ω₁`, codes read by `Θ`, the Veblen level kept). -/
noncomputable def taI (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaT → Ordinal.{0}
  | .zero => 0
  | .phi a Y => veblen a (Om 1 + taI S l Y)
  | .term P R c => taI S l P + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c

/-- The evaluation of a context. -/
noncomputable def taE : TaC → Ordinal.{0} → Ordinal.{0}
  | .hole, y => y
  | .pfx K Q, y => taE K (taV Q + y)
  | .lft K, y => taE K (leWe y)
  | .phi K a, y => taE K (veblen a (Om (1 + 1) + y))

/-- The image evaluation of a context. -/
noncomputable def taEh (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaC → Ordinal.{0} → Ordinal.{0}
  | .hole, v => v
  | .pfx K Q, v => taEh S l K (taI S l Q + v)
  | .lft K, v => taEh S l K (leOe v)
  | .phi K a, v => taEh S l K (veblen a (Om 1 + v))

/-- Well-formed terms: codes `1 ≤ c < Ω₂` at every coefficient, small levels and nonzero arguments at the nodes. -/
def TaWF (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaT → Prop
  | .zero => True
  | .phi a Y => TaSm a ∧ TaWF S l Y ∧ 1 ≤ taV Y ∧ 1 ≤ taI S l Y
  | .term P R c => TaWF S l P ∧ TaWF S l R ∧ GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧ c < Om (1 + 1)

/-- Well-formed contexts. -/
def TaWFC (S : InaccSeq.{0}) (l : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TaWFC S l K ∧ TaWF S l Q
  | .lft K => TaWFC S l K
  | .phi K a => TaWFC S l K ∧ TaSm a

/-- **The own predicate of a term at the evaluation `e`** (`Sg.SgLimC` at every coefficient). -/
def TaOwn (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → TaT → Prop
  | _, .zero => True
  | e, .phi a Y => TaOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Y
  | e, .term P R c => TaOwn S b X0 e P ∧ TaOwn S b X0 (fun r => e (taV P + leWe r)) R ∧
      SgLimC S (fun z => e (taV P + leWe (taV R) * z)) c b X0

/-- The own predicate of the prefixes of a context. -/
def TaOwnC (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : TaC → Prop
  | .hole => True
  | .pfx K Q => TaOwnC S b X0 K ∧ TaOwn S b X0 (taE K) Q
  | .lft K => TaOwnC S b X0 K
  | .phi K _ => TaOwnC S b X0 K

/-- **Concatenation**: the value of `A ⊕ B` is `A + B` (for well-formed `B`). -/
def taCat : TaT → TaT → TaT
  | A, .zero => A
  | A, .phi a Y => .term A (.phi a Y) 1
  | A, .term P R c => .term (taCat A P) R c

/-! ## Order and monotonicity -/

theorem taNode_normal (κ a : Ordinal.{0}) : Order.IsNormal (fun y => veblen a (κ + y)) :=
  (isNormal_veblen a).comp (isNormal_add_right κ)

/-- **Every context is a normal function.** -/
theorem taE_normal : ∀ K : TaC, Order.IsNormal (taE K)
  | .hole => Order.IsNormal.id
  | .pfx K Q => (taE_normal K).comp (isNormal_add_right (taV Q))
  | .lft K => (taE_normal K).comp ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right ldOm2_SC.1))
  | .phi K a => (taE_normal K).comp (taNode_normal _ a)

theorem taEh_normal (l : Ordinal.{0}) : ∀ K : TaC, Order.IsNormal (taEh S l K)
  | .hole => Order.IsNormal.id
  | .pfx K Q => (taEh_normal l K).comp (isNormal_add_right (taI S l Q))
  | .lft K => (taEh_normal l K).comp ((isNormal_opow one_lt_omega0).comp
      (isNormal_mul_right (Om_pos one_ne_zero)))
  | .phi K a => (taEh_normal l K).comp (taNode_normal _ a)

theorem taE_strictMono (K : TaC) : StrictMono (taE K) := (taE_normal K).strictMono

theorem taE_mono (K : TaC) : Monotone (taE K) := (taE_strictMono K).monotone

theorem taEh_strictMono (l : Ordinal.{0}) (K : TaC) : StrictMono (taEh S l K) := (taEh_normal l K).strictMono

theorem taNode_mono (κ a : Ordinal.{0}) : Monotone (fun y => veblen a (κ + y)) :=
  (taNode_normal κ a).strictMono.monotone

/-- `x ≤ W^x`. -/
theorem taLe_We (x : Ordinal.{0}) : x ≤ leWe x :=
  (Ordinal.le_mul_right x ldOm2_SC.1).trans (right_le_opow _ one_lt_omega0)

/-- `y ≤ φ(a, κ + y)`. -/
theorem taLe_node (κ a y : Ordinal.{0}) : y ≤ veblen a (κ + y) := le_add_self.trans (right_le_veblen a _)

/-- **The own predicate is monotone in the base, the offset and the evaluation.** -/
theorem taOwn_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ (t : TaT) (e e' : Ordinal.{0} → Ordinal.{0}), Monotone e → Monotone e' → (∀ y, e y ≤ e' y) →
      TaOwn S b X0 e t → TaOwn S b' X0' e' t
  | .zero, _, _, _, _, _, _ => trivial
  | .phi a Y, e, e', he, he', hle, h =>
    taOwn_mono hb hX Y _ _ (fun _ _ h => he (taNode_mono _ a h)) (fun _ _ h => he' (taNode_mono _ a h))
      (fun y => hle _) h
  | .term P R c, e, e', he, he', hle, ⟨hP, hR, hc⟩ => by
    refine ⟨taOwn_mono hb hX P e e' he he' hle hP,
      taOwn_mono hb hX R _ _ (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
      sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => hle _) hb hX hc⟩

theorem taOwnC_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ K : TaC, TaOwnC S b X0 K → TaOwnC S b' X0' K
  | .hole, _ => trivial
  | .pfx K Q, ⟨hK, hQ⟩ => ⟨taOwnC_mono hb hX K hK,
      taOwn_mono hb hX Q _ _ (taE_mono K) (taE_mono K) (fun _ => le_rfl) hQ⟩
  | .lft K, hK => taOwnC_mono hb hX K hK
  | .phi K _, hK => taOwnC_mono hb hX K hK

/-! ## Values of nonzero terms -/

/-- A node's value is a fixed point of `W^·`: `W^{φ(a, Ω₂ + Y)}·1 = φ(a, Ω₂ + Y)`. -/
theorem taV_node {a : Ordinal.{0}} {Y : TaT} (ha : TaSm a) (hY : 1 ≤ taV Y) :
    leWe (taV (TaT.phi a Y)) * 1 = taV (TaT.phi a Y) := by
  rw [mul_one]; exact taWe_veb (taSm_ne0 ha) hY

theorem taI_node {l a : Ordinal.{0}} {Y : TaT} (ha : TaSm a) (hY : 1 ≤ taI S l Y) (h1 : (1 : Ordinal.{0}) ≤ upsilon l) :
    leOe (taI S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 = taI S l (TaT.phi a Y) := by
  rw [gxTh_small h1, mul_one]; exact taOe_veb (taSm_ne0 ha) hY

/-! ## Concatenation -/

theorem taV_cat {l : Ordinal.{0}} (A : TaT) : ∀ B : TaT, TaWF S l B → taV (taCat A B) = taV A + taV B
  | .zero, _ => (add_zero _).symm
  | .phi a Y, ⟨ha, _, hY, _⟩ => by
    show taV A + leWe (taV (TaT.phi a Y)) * 1 = taV A + taV (TaT.phi a Y)
    rw [taV_node ha hY]
  | .term P R c, ⟨hP, _⟩ => by
    show taV (taCat A P) + leWe (taV R) * c = taV A + (taV P + leWe (taV R) * c)
    rw [taV_cat A P hP, add_assoc]

theorem taI_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (A : TaT) :
    ∀ B : TaT, TaWF S l B → taI S l (taCat A B) = taI S l A + taI S l B
  | .zero, _ => (add_zero _).symm
  | .phi a Y, ⟨ha, _, _, hY⟩ => by
    show taI S l A + leOe (taI S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 = taI S l A + taI S l (TaT.phi a Y)
    rw [taI_node ha hY h1]
  | .term P R c, ⟨hP, _⟩ => by
    show taI S l (taCat A P) + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c =
      taI S l A + (taI S l P + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c)
    rw [taI_cat h1 A P hP, add_assoc]

theorem taWF_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l) {A : TaT} (hA : TaWF S l A) :
    ∀ B : TaT, TaWF S l B → TaWF S l (taCat A B)
  | .zero, _ => hA
  | .phi _ _, hB => ⟨hA, hB, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩
  | .term P R c, ⟨hP, hR, hc⟩ => ⟨taWF_cat h1 hA P hP, hR, hc⟩

/-- The own predicate of a concatenation. -/
theorem taOwn_cat {l b X0 : Ordinal.{0}} {A : TaT} : ∀ (B : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    TaWF S l B → TaOwn S b X0 e A → TaOwn S b X0 (fun y => e (taV A + y)) B → TaOwn S b X0 e (taCat A B)
  | .zero, _, _, _, hA, _ => hA
  | .phi a Y, e, he, _, hA, hB => by
    refine ⟨hA, ?_, sgLimC_one⟩
    show TaOwn S b X0 (fun y => e (taV A + leWe (veblen a (Om (1 + 1) + y)))) Y
    exact taOwn_mono le_rfl le_rfl Y _ _
      (fun _ _ h => he ((add_le_add_iff_left _).2 (taNode_mono _ a h)))
      (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono (taNode_mono _ a h))))
      (fun y => he ((add_le_add_iff_left _).2 (taLe_We _))) hB
  | .term P R c, e, he, ⟨hPw, _⟩, hA, ⟨hP, hR, hc⟩ => by
    have eV := taV_cat A P hPw
    refine ⟨taOwn_cat P e he hPw hA hP, ?_, ?_⟩
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

/-- A small level lies in every closure whose bound is at least `Γ₀`. -/
theorem taSm_mem {a A c : Ordinal.{0}} (ha : TaSm a) (hc : gamma 0 ≤ c) : a ∈ S.CSet A c :=
  CSet.of_lt (ha.2.trans_le hc)

theorem taGam_le_psi2 (x : Ordinal.{0}) : gamma 0 ≤ S.psi x (Om (1 + 1)) := taGam_le_SC (SC_psi (InR_Om_succ 1) x)

section Data

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `Γ₀ ≤ Θ x` for `x ≥ Γ₀`. -/
theorem taTh_gam {x : Ordinal.{0}} (hx : gamma 0 ≤ x) : gamma 0 ≤ gxTh (upsilon l) (ldAtR S l) x := by
  have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hx
  rwa [gxTh_small (taGam_le_SC (leRho hl hX).1)] at h

theorem taSm_hull {a : Ordinal.{0}} (ha : TaSm a) : a ∈ cdHull S l :=
  CSet.of_lt (taSm_lt_SC ha (leRho hl hX).1)

theorem taV_hull : ∀ t : TaT, TaWF S l t → taV t ∈ cdHull S l
  | .zero, _ => CSet.zero_mem _ _
  | .phi a Y, ⟨ha, hY, _, _⟩ => CSet.phi_mem (taSm_hull hl hX ha) (CSet.add_mem (mxOm2_mem _ _) (taV_hull Y hY))
  | .term P R c, ⟨hP, hR, hc, _, hcW⟩ =>
    CSet.add_mem (taV_hull P hP) (leMulWe_mem (taV_hull R hR) ((ldHull_iff hl hX hcW).2 hc))

/-- Values of well-formed terms are below `ψ_{Ω₃}(0)`, images below `ψ_{Ω₂}(0)`. -/
theorem taV_lt_G3 : ∀ t : TaT, TaWF S l t →
    taV t < S.psi 0 (Om (1 + 1 + 1)) ∧ taI S l t < S.psi 0 (Om (1 + 1))
  | .zero, _ => ⟨rwG3_SC.1, rwG_SC.1⟩
  | .phi a Y, ⟨ha, hY, _, _⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨h1, h2⟩ := taV_lt_G3 Y hY
    exact ⟨hG3.2 a (taSm_lt_SC ha hG3) _ (hG3.isPrincipal rwW_lt_G3 h1),
      hG1.2 a (taSm_lt_SC ha hG1) _ (hG1.isPrincipal rwO_lt_G h2)⟩
  | .term P R c, ⟨hP, hR, _, _, hcW⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨hP1, hP2⟩ := taV_lt_G3 P hP
    obtain ⟨hR1, hR2⟩ := taV_lt_G3 R hR
    have hΘc := Sn.snTh_lt_Om1 hl hX hcW.le
    exact ⟨hG3.isPrincipal hP1 (ldMul_lt_SC hG3 (leWe_lt_SC hG3 rwW_lt_G3 hR1).1 (hcW.trans rwW_lt_G3)),
      hG1.isPrincipal hP2 (ldMul_lt_SC hG1 (leOe_lt_SC hG1 rwO_lt_G hR2).1 (hΘc.trans rwO_lt_G))⟩

/-- **The data of an own term above the bottom `T_{X₀ + W^{e(val)}}(b)`.** -/
theorem taDat {b X0 : Ordinal.{0}} : ∀ (t : TaT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TaWF S l t →
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
    obtain ⟨h1, h2, h3, h4⟩ := taDat Y _ he' hYw hYo
    set T := S.psi (b + leWe (X0 + leWe (e (taV (TaT.phi a Y))))) (Om (1 + 1)) with hT
    have hgT : gamma 0 ≤ T := taGam_le_psi2 _
    have hgΘT : gamma 0 ≤ gxTh (upsilon l) (ldAtR S l) T := taTh_gam hl hX hgT
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun Q hQ hc => ?_, fun Q hQ hc => ?_⟩
    · exact CSet.phi_mem (taSm_mem ha (hgT.trans hc)) (CSet.add_mem (mxOm2_mem _ _) (h1 c hc))
    · exact CSet.phi_mem (taSm_mem ha (hgΘT.trans hc)) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (h2 c hc))
    · exact LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (LeCl.add LeCl.om (h3 Q hQ hc))
    · exact LeCl.phi (LeCl.small (taSm_lt_SC ha hQ)) (LeCl.add LeCl.om (h4 Q hQ hc))
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
    obtain ⟨hP1, hP2, hP3, hP4⟩ := taDat P e he hPw hPo
    obtain ⟨hR1, hR2, hR3, hR4⟩ := taDat R _ heR hRw hRo
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

end Googology.Trans.PoR.InaccPsi.R2.Ta
