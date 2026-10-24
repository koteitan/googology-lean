import Googology.Trans.PoR.InaccPsi.R2.SwDiv

/-!
# Exponent terms with the leaves `ε_{Ω₂+1+k}`

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `L_k = ε_{Ω₂+1+k} = φ(1, Ω₂ + (k+1))` (`swL`),
`L̂_k = ε_{Ω₁+1+k}` (`swLh`).

**Terms** `SwT`: `zero`, `eps k` (the leaf `L_k`, image `L̂_k`), `term P R c = P + W^R·c`; **contexts** `SwC`:
`hole`, `pfx K Q = K(Q + _)`, `lft K = K(W^_)` (the terms and contexts of `Sg.SgT`, `Sg.SgC` with the leaves added).
`swCat A B` has the value `A + B` (`A ⊕ eps k = A + W^{L_k}·1`, since `W^{L_k} = L_k`).
The own predicate `SwOwn` is `Sg.SgOwn` with `True` at the leaves (the limit condition `Sg.SgLimC` at every
coefficient).

* `swK_mul_L`, `swL_We` (`W^{L_k} = L_k`), `swLh_Oe`, `swL_mem`, `swL_cl` (**a leaf is a code over every `Q`**),
  `swL_lt_G3`, `swLh_lt_G`, `swL_lt_top` (`L_k < ε_{Ω₂+ω}`), `swL_strictMono`;
* `swE_normal` (**every context is a normal function**), `swE_strictMono`, `swOwn_mono`, `swOwnC_mono`,
  `swV_cat`, `swI_cat`, `swWF_cat`, `swOwn_cat`, `swV_hull`, `swDat` (**the data of an own term**).

No new axiom.  New definitions: `swL`, `swLh`, `SwT`, `SwC`, `swV`, `swI`, `swE`, `swEh`, `SwWF`, `SwWFC`, `SwOwn`,
`SwOwnC`, `swCat`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-! ## The leaves -/

/-- **The leaf `L_k = ε_{Ω₂+1+k}`.** -/
noncomputable def swL (k : ℕ) : Ordinal.{0} := veblen 1 (Om (1 + 1) + ((k : Ordinal.{0}) + 1))

/-- **The image leaf `L̂_k = ε_{Ω₁+1+k}`.** -/
noncomputable def swLh (k : ℕ) : Ordinal.{0} := veblen 1 (Om 1 + ((k : Ordinal.{0}) + 1))

theorem swK_lt_L {κ : Ordinal.{0}} (k : ℕ) : κ < veblen 1 (κ + ((k : Ordinal.{0}) + 1)) :=
  (lt_add_of_pos_right κ (zero_lt_one.trans_le le_add_self)).trans_le (right_le_veblen 1 _)

/-- `κ·L = L` for the leaves over a strongly critical `κ`. -/
theorem swK_mul_L {κ : Ordinal.{0}} (hκ : SC κ) (k : ℕ) :
    κ * veblen 1 (κ + ((k : Ordinal.{0}) + 1)) = veblen 1 (κ + ((k : Ordinal.{0}) + 1)) := by
  set L := veblen 1 (κ + ((k : Ordinal.{0}) + 1))
  have hE : ω ^ L = L := gg_veblen_eps one_ne_zero
  have h1 : κ < ω ^ L := by rw [hE]; exact swK_lt_L k
  calc κ * L = ω ^ κ * ω ^ L := by rw [gg_SC_eps hκ, hE]
    _ = ω ^ (κ + L) := (opow_add _ _ _).symm
    _ = ω ^ L := by rw [Ordinal.add_of_omega0_opow_le h1 hE.le]
    _ = L := hE

theorem swL_We (k : ℕ) : leWe (swL k) = swL k := by
  unfold leWe swL; rw [swK_mul_L ldOm2_SC, gg_veblen_eps one_ne_zero]

theorem swLh_Oe (k : ℕ) : leOe (swLh k) = swLh k := by
  unfold leOe swLh; rw [swK_mul_L Ph.ph_SC_Om1, gg_veblen_eps one_ne_zero]

theorem swW_lt_L (k : ℕ) : Om (1 + 1 : Ordinal.{0}) < swL k := swK_lt_L k

theorem swO_lt_Lh (k : ℕ) : Om (1 : Ordinal.{0}) < swLh k := swK_lt_L k

theorem swL_mem {a b : Ordinal.{0}} (k : ℕ) : swL k ∈ S.CSet a b :=
  CSet.phi_mem (CSet.one_mem _ _) (CSet.add_mem (mxOm2_mem _ _) (CSet.add_mem (scNat_mem a b k) (CSet.one_mem _ _)))

theorem swLh_mem {a b : Ordinal.{0}} (k : ℕ) : swLh k ∈ S.CSet a b :=
  CSet.phi_mem (CSet.one_mem _ _)
    (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.add_mem (scNat_mem a b k) (CSet.one_mem _ _)))

/-- **A leaf is a code over every strongly critical `Q`.** -/
theorem swL_cl {Q : Ordinal.{0}} (hQ : SC Q) (k : ℕ) : LeCl (Om (1 + 1)) Q (swL k) :=
  LeCl.phi (LeCl.small (gg_one_lt_of_SC hQ))
    (LeCl.add LeCl.om (LeCl.add (scNat_cl hQ k) (LeCl.small (gg_one_lt_of_SC hQ))))

theorem swLh_cl {Q : Ordinal.{0}} (hQ : SC Q) (k : ℕ) : LeCl (Om 1) Q (swLh k) :=
  LeCl.phi (LeCl.small (gg_one_lt_of_SC hQ))
    (LeCl.add LeCl.om (LeCl.add (scNat_cl hQ k) (LeCl.small (gg_one_lt_of_SC hQ))))

theorem swNat1_lt_SC {G : Ordinal.{0}} (hG : SC G) (k : ℕ) : (k : Ordinal.{0}) + 1 < G :=
  (Ordinal.natCast_lt_omega0 (k + 1)).trans_le' (by rw [Nat.cast_succ]) |>.trans (Lw.lw_omega_lt_SC hG)

theorem swL_lt_G3 (k : ℕ) : swL k < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  exact hG3.2 1 (gg_one_lt_of_SC hG3) _ (hG3.isPrincipal rwW_lt_G3 (swNat1_lt_SC hG3 k))

theorem swLh_lt_G (k : ℕ) : swLh k < S.psi 0 (Om (1 + 1)) := by
  have hG1 := rwG_SC (S := S)
  exact hG1.2 1 (gg_one_lt_of_SC hG1) _ (hG1.isPrincipal rwO_lt_G (swNat1_lt_SC hG1 k))

theorem swL_one_le (k : ℕ) : (1 : Ordinal.{0}) ≤ swL k :=
  (gg_one_lt_of_SC ldOm2_SC).le.trans (swW_lt_L k).le

theorem swLh_one_le (k : ℕ) : (1 : Ordinal.{0}) ≤ swLh k :=
  (gg_one_lt_of_SC Ph.ph_SC_Om1).le.trans (swO_lt_Lh k).le

/-- **The top `ε_{Ω₂+ω}` of the leaves**, and its image `ε_{Ω₁+ω}`. -/
noncomputable def swTop (_S : InaccSeq.{0}) : Ordinal.{0} := veblen 1 (Om (1 + 1) + ω)

theorem swL_lt_top (k : ℕ) : swL k < swTop S := by
  unfold swL swTop
  refine (veblen_right_strictMono 1).lt_iff_lt.2 ((add_lt_add_iff_left _).2 ?_)
  have := Ordinal.natCast_lt_omega0 (k + 1); rwa [Nat.cast_succ] at this

theorem swL_strictMono : StrictMono swL := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold swL
  refine (veblen_right_strictMono 1).lt_iff_lt.2 ((add_lt_add_iff_left _).2 ?_)
  rw [Nat.cast_succ]; exact lt_add_one _

theorem swLh_strictMono : StrictMono swLh := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold swLh
  refine (veblen_right_strictMono 1).lt_iff_lt.2 ((add_lt_add_iff_left _).2 ?_)
  rw [Nat.cast_succ]; exact lt_add_one _

theorem swTop_lt_G3 : swTop S < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  exact hG3.2 1 (gg_one_lt_of_SC hG3) _ (hG3.isPrincipal rwW_lt_G3 (Lw.lw_omega_lt_SC hG3))

/-! ## Terms and contexts -/

/-- **Exponent terms with leaves**: `zero`, `eps k` (`L_k`), `term P R c = P + W^R·c`. -/
inductive SwT : Type 1
  | zero : SwT
  | eps : ℕ → SwT
  | term : SwT → SwT → Ordinal.{0} → SwT

/-- **Contexts**: `hole`, `pfx K Q = K(Q + _)`, `lft K = K(W^_)`. -/
inductive SwC : Type 1
  | hole : SwC
  | pfx : SwC → SwT → SwC
  | lft : SwC → SwC

/-- The value of a term. -/
noncomputable def swV : SwT → Ordinal.{0}
  | .zero => 0
  | .eps k => swL k
  | .term P R c => swV P + leWe (swV R) * c

/-- The image of a term (`Ω₂ ↦ Ω₁`, `L_k ↦ L̂_k`, codes read by `Θ`). -/
noncomputable def swI (S : InaccSeq.{0}) (l : Ordinal.{0}) : SwT → Ordinal.{0}
  | .zero => 0
  | .eps k => swLh k
  | .term P R c => swI S l P + leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) c

/-- The evaluation of a context. -/
noncomputable def swE : SwC → Ordinal.{0} → Ordinal.{0}
  | .hole, y => y
  | .pfx K Q, y => swE K (swV Q + y)
  | .lft K, y => swE K (leWe y)

/-- The image evaluation of a context. -/
noncomputable def swEh (S : InaccSeq.{0}) (l : Ordinal.{0}) : SwC → Ordinal.{0} → Ordinal.{0}
  | .hole, v => v
  | .pfx K Q, v => swEh S l K (swI S l Q + v)
  | .lft K, v => swEh S l K (leOe v)

/-- Codes `1 ≤ c < Ω₂` at every coefficient. -/
def SwWF (S : InaccSeq.{0}) (l : Ordinal.{0}) : SwT → Prop
  | .zero => True
  | .eps _ => True
  | .term P R c => SwWF S l P ∧ SwWF S l R ∧ GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧ c < Om (1 + 1)

/-- Every prefix of a context is well formed. -/
def SwWFC (S : InaccSeq.{0}) (l : Ordinal.{0}) : SwC → Prop
  | .hole => True
  | .pfx K Q => SwWFC S l K ∧ SwWF S l Q
  | .lft K => SwWFC S l K

/-- **The own predicate of a term at the evaluation `e`** (`Sg.SgLimC` at every coefficient). -/
def SwOwn (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : (Ordinal.{0} → Ordinal.{0}) → SwT → Prop
  | _, .zero => True
  | _, .eps _ => True
  | e, .term P R c => SwOwn S b X0 e P ∧ SwOwn S b X0 (fun r => e (swV P + leWe r)) R ∧
      SgLimC S (fun z => e (swV P + leWe (swV R) * z)) c b X0

/-- The own predicate of the prefixes of a context. -/
def SwOwnC (S : InaccSeq.{0}) (b X0 : Ordinal.{0}) : SwC → Prop
  | .hole => True
  | .pfx K Q => SwOwnC S b X0 K ∧ SwOwn S b X0 (swE K) Q
  | .lft K => SwOwnC S b X0 K

/-- **Concatenation**: the value of `A ⊕ B` is `A + B`. -/
def swCat : SwT → SwT → SwT
  | A, .zero => A
  | A, .eps k => .term A (.eps k) 1
  | A, .term P R c => .term (swCat A P) R c

/-! ## Order and monotonicity -/

/-- **Every context is a normal function.** -/
theorem swE_normal : ∀ K : SwC, Order.IsNormal (swE K)
  | .hole => Order.IsNormal.id
  | .pfx K Q => (swE_normal K).comp (isNormal_add_right (swV Q))
  | .lft K => (swE_normal K).comp ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right ldOm2_SC.1))

theorem swEh_normal (l : Ordinal.{0}) : ∀ K : SwC, Order.IsNormal (swEh S l K)
  | .hole => Order.IsNormal.id
  | .pfx K Q => (swEh_normal l K).comp (isNormal_add_right (swI S l Q))
  | .lft K => (swEh_normal l K).comp ((isNormal_opow one_lt_omega0).comp
      (isNormal_mul_right (Om_pos one_ne_zero)))

theorem swE_strictMono (K : SwC) : StrictMono (swE K) := (swE_normal K).strictMono

theorem swE_mono (K : SwC) : Monotone (swE K) := (swE_strictMono K).monotone

theorem swEh_strictMono (l : Ordinal.{0}) (K : SwC) : StrictMono (swEh S l K) := (swEh_normal l K).strictMono

/-- **The own predicate is monotone in the base, the offset and the evaluation.** -/
theorem swOwn_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ (t : SwT) (e e' : Ordinal.{0} → Ordinal.{0}), Monotone e → Monotone e' → (∀ y, e y ≤ e' y) →
      SwOwn S b X0 e t → SwOwn S b' X0' e' t
  | .zero, _, _, _, _, _, _ => trivial
  | .eps _, _, _, _, _, _, _ => trivial
  | .term P R c, e, e', he, he', hle, ⟨hP, hR, hc⟩ => by
    refine ⟨swOwn_mono hb hX P e e' he he' hle hP,
      swOwn_mono hb hX R _ _ (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
      sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h)))
        (fun _ _ h => he' ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => hle _) hb hX hc⟩

theorem swOwnC_mono {b b' X0 X0' : Ordinal.{0}} (hb : b ≤ b') (hX : X0 ≤ X0') :
    ∀ K : SwC, SwOwnC S b X0 K → SwOwnC S b' X0' K
  | .hole, _ => trivial
  | .pfx K Q, ⟨hK, hQ⟩ => ⟨swOwnC_mono hb hX K hK,
      swOwn_mono hb hX Q _ _ (swE_mono K) (swE_mono K) (fun _ => le_rfl) hQ⟩
  | .lft K, hK => swOwnC_mono hb hX K hK

/-! ## Concatenation -/

theorem swV_cat (A : SwT) : ∀ B : SwT, swV (swCat A B) = swV A + swV B
  | .zero => (add_zero _).symm
  | .eps k => by
    show swV A + leWe (swL k) * 1 = swV A + swL k
    rw [mul_one, swL_We]
  | .term P R c => by
    show swV (swCat A P) + leWe (swV R) * c = swV A + (swV P + leWe (swV R) * c)
    rw [swV_cat A P, add_assoc]

theorem swI_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) (A : SwT) :
    ∀ B : SwT, swI S l (swCat A B) = swI S l A + swI S l B
  | .zero => (add_zero _).symm
  | .eps k => by
    show swI S l A + leOe (swLh k) * gxTh (upsilon l) (ldAtR S l) 1 = swI S l A + swLh k
    rw [swLh_Oe, gxTh_small h1, mul_one]
  | .term P R c => by
    show swI S l (swCat A P) + leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) c =
      swI S l A + (swI S l P + leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) c)
    rw [swI_cat h1 A P, add_assoc]

theorem swWF_cat {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l) {A : SwT} (hA : SwWF S l A) :
    ∀ B : SwT, SwWF S l B → SwWF S l (swCat A B)
  | .zero, _ => hA
  | .eps _, _ => ⟨hA, trivial, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩
  | .term P R c, ⟨hP, hR, hc⟩ => ⟨swWF_cat h1 hA P hP, hR, hc⟩

/-- The own predicate of a concatenation. -/
theorem swOwn_cat {b X0 : Ordinal.{0}} {A : SwT} : ∀ (B : SwT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
    SwOwn S b X0 e A → SwOwn S b X0 (fun y => e (swV A + y)) B → SwOwn S b X0 e (swCat A B)
  | .zero, _, _, hA, _ => hA
  | .eps _, _, _, hA, _ => ⟨hA, trivial, sgLimC_one⟩
  | .term P R c, e, he, hA, ⟨hP, hR, hc⟩ => by
    have eV := swV_cat A P
    refine ⟨swOwn_cat P e he hA hP, ?_, ?_⟩
    · refine swOwn_mono le_rfl le_rfl R _ _
        (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => ?_) hR
      show e (swV A + (swV P + leWe y)) ≤ e (swV (swCat A P) + leWe y)
      rw [eV, add_assoc]
    · refine sgLimC_mono (fun _ _ h => he ((add_le_add_iff_left _).2 ((add_le_add_iff_left _).2 (leMulWe_mono h))))
        (fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))) (fun z => ?_) le_rfl le_rfl hc
      show e (swV A + (swV P + leWe (swV R) * z)) ≤ e (swV (swCat A P) + leWe (swV R) * z)
      rw [eV, add_assoc]

/-! ## The data of terms -/

section Data

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem swV_hull : ∀ t : SwT, SwWF S l t → swV t ∈ cdHull S l
  | .zero, _ => CSet.zero_mem _ _
  | .eps k, _ => swL_mem k
  | .term P R c, ⟨hP, hR, hc, _, hcW⟩ =>
    CSet.add_mem (swV_hull P hP) (leMulWe_mem (swV_hull R hR) ((ldHull_iff hl hX hcW).2 hc))

/-- Values of well-formed terms are below `ψ_{Ω₃}(0)`, images below `ψ_{Ω₂}(0)`. -/
theorem swV_lt_G3 : ∀ t : SwT, SwWF S l t →
    swV t < S.psi 0 (Om (1 + 1 + 1)) ∧ swI S l t < S.psi 0 (Om (1 + 1))
  | .zero, _ => ⟨rwG3_SC.1, rwG_SC.1⟩
  | .eps k, _ => ⟨swL_lt_G3 k, swLh_lt_G k⟩
  | .term P R c, ⟨hP, hR, _, _, hcW⟩ => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    obtain ⟨hP1, hP2⟩ := swV_lt_G3 P hP
    obtain ⟨hR1, hR2⟩ := swV_lt_G3 R hR
    have hΘc := Sn.snTh_lt_Om1 hl hX hcW.le
    exact ⟨hG3.isPrincipal hP1 (ldMul_lt_SC hG3 (leWe_lt_SC hG3 rwW_lt_G3 hR1).1 (hcW.trans rwW_lt_G3)),
      hG1.isPrincipal hP2 (ldMul_lt_SC hG1 (leOe_lt_SC hG1 rwO_lt_G hR2).1 (hΘc.trans rwO_lt_G))⟩

omit hl hX in
/-- **The data of an own term above the bottom `T_{X₀ + W^{e(val)}}(b)`.** -/
theorem swDat {b X0 : Ordinal.{0}} : ∀ (t : SwT) (e : Ordinal.{0} → Ordinal.{0}), Monotone e → SwWF S l t →
    SwOwn S b X0 e t →
    (∀ c, S.psi (b + leWe (X0 + leWe (e (swV t)))) (Om (1 + 1)) ≤ c → swV t ∈ S.CSet 0 c) ∧
    (∀ c, gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (swV t)))) (Om (1 + 1))) ≤ c →
      swI S l t ∈ S.CSet 0 c) ∧
    (∀ Q, SC Q → S.psi (b + leWe (X0 + leWe (e (swV t)))) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q (swV t)) ∧
    (∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe (e (swV t)))) (Om (1 + 1))) ≤ Q →
      LeCl (Om 1) Q (swI S l t))
  | .zero, _, _, _, _ => ⟨fun _ _ => CSet.zero_mem _ _, fun _ _ => CSet.zero_mem _ _,
      fun Q hQ _ => LeCl.zero hQ.1, fun Q hQ _ => LeCl.zero hQ.1⟩
  | .eps k, _, _, _, _ => ⟨fun _ _ => swL_mem k, fun _ _ => swLh_mem k,
      fun Q hQ _ => swL_cl hQ k, fun Q hQ _ => swLh_cl hQ k⟩
  | .term P R c, e, he, ⟨hPw, hRw, hc, hc1, hcW⟩, ⟨hPo, hRo, hco⟩ => by
    set T := S.psi (b + leWe (X0 + leWe (e (swV (SwT.term P R c))))) (Om (1 + 1)) with hT
    have hval : swV (SwT.term P R c) = swV P + leWe (swV R) * c := rfl
    have himg : swI S l (SwT.term P R c) = swI S l P + leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) c := rfl
    have hTmono : ∀ {x y : Ordinal.{0}}, x ≤ y → S.psi (b + leWe (X0 + leWe (e x))) (Om (1 + 1)) ≤
        S.psi (b + leWe (X0 + leWe (e y))) (Om (1 + 1)) := fun h =>
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (leWe_mono (he h)))))).1
    have heR : Monotone (fun r => e (swV P + leWe r)) := fun _ _ h => he ((add_le_add_iff_left _).2 (leWe_mono h))
    have hG : Monotone (fun z => e (swV P + leWe (swV R) * z)) :=
      fun _ _ h => he ((add_le_add_iff_left _).2 (leMulWe_mono h))
    have hPT := hTmono (show swV P ≤ swV (SwT.term P R c) from le_self_add)
    have hRT := hTmono (show swV P + leWe (swV R) ≤ swV (SwT.term P R c) from
      (add_le_add_iff_left _).2 (by simpa using leMulWe_mono (e := swV R) hc1))
    obtain ⟨hP1, hP2, hP3, hP4⟩ := swDat P e he hPw hPo
    obtain ⟨hR1, hR2, hR3, hR4⟩ := swDat R _ heR hRw hRo
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

end Googology.Trans.PoR.InaccPsi.R2.Sw
