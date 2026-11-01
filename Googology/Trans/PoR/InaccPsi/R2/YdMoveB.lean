import Googology.Trans.PoR.InaccPsi.R2.YdBeta
import Googology.Trans.PoR.InaccPsi.R2.YdRef

/-!
# The base-data move over a base `β ≠ 0`, reduced to the two base facts at `λ'`

`X = Ω_{k+3}`, `W^x = leWe x`, `t = β + W^{X+e}`, `B_n = Bc.bcB S n`, "window" as in `Yd.ydBaseMove`.

* `ydTopAtB` (**`ψ₂(β + W^{X+Ω₂})` is an atom of `λ` for every `β ∈ D`**), `ydBaseE_lt` (**`Ro.RoBaseE λ X e β`,
  `β ∈ D` ⇒ `e < E^β_X`**);
* `ydBaseMoveB` (**THE BASE-DATA MOVE over every top base `(e, β)`** at a window, under the moves of the codes below
  `ψ₂ t`, GIVEN only the two base facts at `λ'`: `W^{X+B_n e} ∣ B_n β` and `B_n β ∈ D_{λ'}`; the own clause and the
  normality at `λ'` are PROVED (`Yd.ydOwnMoveB`, `Yd.ydNormB`), the bound `B_n β + W^{X+B_n e} < A_{η_λ'}` follows from
  `B_n β < Ω_ω`, and `B_n t = B_n β + W^{X+B_n e}`);
* `ydTopMoveB` (**every top atom `ψ₂(β + W^{X+e})` moves** under the same two base facts);
* `ydNonvacB` (non-vacuity: at `(e, β) = (0, Ω_{k+3})` every hypothesis, the two base facts included, holds at every
  window; `ydTopMoveB` there is not covered by `Yd.ydTopMove`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

theorem ydBW_lt (k : ℕ) {β e : Ordinal.{0}} (hβ : β < Om ω) (he : e ≤ Om (1 + 1)) :
    β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) < Om ω :=
  vkOmW.1.isPrincipal hβ (ydW_lt k he)

/-- **`ψ₂(β + W^{X+Ω₂})` is an atom of `λ` for every `β ∈ D`.** -/
theorem ydTopAtB (k : ℕ) {l β : Ordinal.{0}} (hβD : VbD S l β) :
    S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ∈ ldAtR S l :=
  ⟨_, CSet.add_mem hβD.1 (leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) (mxOm2_mem _ _))),
    (ydBW_lt k hβD.2.2 le_rfl).trans_le (ConjT.OmW_le_A S _), rfl⟩

/-- **`Ro.RoBaseE λ X e β`, `β ∈ D` ⇒ `e < E^β_X`.** -/
theorem ydBaseE_lt (k : ℕ) {l e β : Ordinal.{0}} (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) :
    e < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) := by
  by_contra hc
  push Not at hc
  have h1 := hb.2.2.2.2 _ (GxCl.atom (ydTopAtB k hβD)) hc
  exact absurd (h1.trans_le (ydTopFailB _ _)) (lt_irrefl _)

/-- **NON-VACUITY**: `(e, β) = (0, Ω_{k+3})` is a top base in `D` at every `λ`, and `B_n` fixes `Ω_{k+3}`. -/
theorem ydNonvacB (k n : ℕ) (l : Ordinal.{0}) :
    VbD S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ∧
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ∧
      Bc.bcB S n (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) = Om ((k : Ordinal.{0}) + 1 + 1 + 1) ∧
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) ∣ Om ((k : Ordinal.{0}) + 1 + 1 + 1) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hW : leWe (X + 0) = X := by rw [add_zero]; exact Vn.vnWe_OmK k
  have hs : (k : Ordinal.{0}) + 1 + 1 < ω := (lt_add_one _).trans (vkNat_lt_omega k)
  have hD : VbD S l X := ⟨Vn.vnOmK3_mem k _ _, Vn.vnOmK3_mem k _ _, hXW⟩
  refine ⟨hD, ⟨by rw [hW], hD.1, ?_, fun d _ => ?_, fun e' _ he' => ?_⟩, (Vs.vsW_D (S := S) hs (n := n)).2,
    by rw [hW]⟩
  · rw [hW]
    exact (vkOmW.1.isPrincipal hXW hXW).trans_le (ConjT.OmW_le_A S _)
  · exact Vn.vnOmK3_mem k _ _
  · have he0 : e' = 0 := le_antisymm he' zero_le
    subst he0
    exact (SC_psi hκ2 _).1

section Win

variable {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')

include hR h1 hr hl' hB

/-- **THE BASE-DATA MOVE over every top base `(e, β)`, given the two base facts at `λ'`.** -/
theorem ydBaseMoveB (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))
    (hdiv' : leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) ∣ Bc.bcB S n β)
    (hD' : VbD S l' (Bc.bcB S n β)) :
    MvD S β ∧ MvD S e ∧ GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n e) ∧ Bc.bcB S n e < Om (1 + 1) ∧
      Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Bc.bcB S n e) (Bc.bcB S n β) ∧
      Bc.bcB S n (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
        Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by
    have h := hb.2.2.2.1 0 zero_le; rwa [add_zero] at h
  have hβC : β ∈ S.CSet (β + leWe (X + e)) (S.psi (β + leWe (X + e)) (Om (1 + 1))) := hb.2.2.2.1 _ le_rfl
  have he : e < S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1)) := ydBaseE_lt k hβD hb
  have he2 : e < Om (1 + 1) := he.trans (psi_lt hκ2 _)
  have hes : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hb.2.2.2.2 e hec le_rfl
  obtain ⟨hDe, hBec, hBeP, -, -⟩ := IH e hec hes
  obtain ⟨hDβ, -, -⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH β hβD hβC
  obtain ⟨-, hown'⟩ := ydOwnMoveB k n hDβ hβn hDe he
  -- `B_n W^{X+e} = W^{X+B_n e}`
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set P : Ordinal.{0} → Prop := fun x => GxCl (upsilon l) (ldAtR S l) x ∧
    x < S.psi (β + leWe (X + e)) (Om (1 + 1)) ∧ x < Om (1 + 1) with hP_def
  have hPD : ∀ x, P x → MvD S x := fun x hx => (IH x hx.1 hx.2.1).1
  have hPdec : ∀ x, P x → x ≠ 0 → P (log ω x) ∧ P (x - ω ^ log ω x) := fun x hx hx0 => by
    obtain ⟨hsub, hlog⟩ := gxDec hρSC hAt x hx.1
    have hlx : log ω x ≤ x := log_le_self ω x
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    exact ⟨⟨hlog, hlx.trans_lt hx.2.1, hlx.trans_lt hx.2.2⟩,
      ⟨hsub _ (GxCl.opow hρSC.1 hlog) hlead, (Ordinal.sub_le_self _ _).trans_lt hx.2.1,
        (Ordinal.sub_le_self _ _).trans_lt hx.2.2⟩⟩
  have hPW : ∀ x, P x → x < Om (1 + 1) := fun x hx => hx.2.2
  have hX0 : X ≠ 0 := (Om_pos (add_pos_of_right zero_lt_one _).ne').ne'
  obtain ⟨hDW, hBW, -, -⟩ := Ro.roB_We (n := n) hX0 (Xv.xvShB (S := S) k) P hPD hPdec hPW
    ⟨hec, hes, he2⟩ ⟨hec, hes, he2⟩
  obtain ⟨-, hBt⟩ := mvB_add (k := n) hDβ hDW
  rw [hBW] at hBt
  have hBe2 : Bc.bcB S n e < Om (1 + 1) := hBeP.trans Lj.ljThP_lt_Om2
  -- the top base at `λ'`
  have hβn' := ydNormB n hDβ hβn
  refine ⟨hDβ, hDe, hBec, hBe2, ⟨hdiv', hD'.1, ?_, fun d _ => (psi_mono hκ2 le_self_add).2 hβn',
    fun e'' _ he'' => hown' e'' he''⟩, hBt⟩
  exact (ydBW_lt k hD'.2.2 hBe2.le).trans_le (ConjT.OmW_le_A S _)

/-- **Every top atom `ψ₂(β + W^{X+e})` moves**, given the two base facts at `λ'`. -/
theorem ydTopMoveB (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x))
    (hdiv' : leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) ∣ Bc.bcB S n β)
    (hD' : VbD S l' (Bc.bcB S n β)) :
    MvD S (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e)) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', A', hA', hρA'⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨-, -, hBec, hBe2, hb', hmv⟩ := ydBaseMoveB hR h1 hr hl' hB k hec hβD hb IH hdiv' hD'
  have he2 : e < Om (1 + 1) := (ydBaseE_lt k hβD hb).trans (psi_lt hκ2 _)
  have hsθ : S.psi (β + leWe (X + e)) (Om (1 + 1)) ≤ Lj.ljThP S :=
    ((psi_mono hκ2 (ydBW_lt k hβD.2.2 he2.le).le).1).trans Lj.ljTh_lt_ThP.le
  have hhi : gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + e)) (Om (1 + 1))) < Bc.bcC S (n + 1) := by
    rw [← ldTheta hl hX (hsθ.trans Lj.ljThP_lt_Om2.le)]
    exact ((Lj.ljTheta_lt_delta hl hX hown hsθ).trans_le (cdR_ge S l)).trans hr
  obtain ⟨hDs, hBs, hmove⟩ := Xq.xqTopMove hl hX hl' hX' hown hρA hA' hρA' h1.le hB k hec he2 hβD hb
    hBec hBe2 hD' hb' hmv IH hhi
  have hBeH : Bc.bcB S n e ∈ cdHull S l' := (ldHull_iff hl' hX' hBe2).2 hBec
  have hatom : S.psi (Bc.bcB S n β + leWe (X + Bc.bcB S n e)) (Om (1 + 1)) ∈ ldAtR S l' :=
    ⟨_, CSet.add_mem hD'.1 (leWe_mem (CSet.add_mem (Vn.vnOmK3_mem k _ _) hBeH)),
      (ydBW_lt k hD'.2.2 hBe2.le).trans_le (ConjT.OmW_le_A S _), rfl⟩
  exact ⟨hDs, hBs, hBs ▸ hatom, hmove⟩

/-- **NON-VACUITY at a window**: at `(e, β) = (0, Ω_{k+3})` the two base facts at `λ'` hold. -/
theorem ydNonvacW (k : ℕ) :
    leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n 0) ∣ Bc.bcB S n (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ∧
      VbD S l' (Bc.bcB S n (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) := by
  obtain ⟨-, -, hBX, hdv⟩ := ydNonvacB (S := S) k n l'
  obtain ⟨hD, -, -, -⟩ := ydNonvacB (S := S) k n l'
  have h0 : Bc.bcB S n 0 = 0 := Bc.bcB_fix' S n 0 (Lw.lw_L_SC S _).1
  rw [h0, hBX]
  exact ⟨hdv, hD⟩

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yd

#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydTopAtB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydBaseE_lt
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydNonvacB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydBaseMoveB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydTopMoveB
#print axioms Googology.Trans.PoR.InaccPsi.R2.Yd.ydNonvacW
