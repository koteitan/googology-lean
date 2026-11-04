import Googology.Trans.PoR.InaccPsi.R2.YyY3G
import Googology.Trans.PoR.InaccPsi.R2.YyOm2

/-!
# REFUTE-FIRST points of round 130 (leaf read54)

`t = W^{Ω₃} = Ω₃` (the top base `(e, β) = (0, 0)` of the level `k = 0`), `Y₃ = ψ_{Ω₃}(Ω₃)`, `G₃ = ψ_{Ω₃}(0)`.

* `yyG3_two_lt` (`G₃·2 < Y₃`: the point `δ = ψ₃(0)·2` lies below `Y₃`, inside the region of `Yt.ytTopMoveY`);
* `yyTestMoveOm3` (**every atom `ψ₂(Ω₃ + δ)`, `δ < Y₃·Ω₂`, `Ω₃ + δ` normal and in the hull, MOVES** at every window
  under the premise of WallBelow at it), `yyTestY3` (**`δ = Y₃`**), `yyTestG3` (**`δ = ψ₃(0)·2`**),
  `yyTestY3two` (**`δ = Y₃·2`**): skPsi3Off is not refuted at these points;
* `yyTestOm2` (**the top law at the exponent `X + Ω₂` over `β = 0`**: `Θ(ψ₂(W^{Ω_{k+3}+Ω₂})) =
  ψ₁(A + 1 + ψ₂(Ω^{Ω_{k+2}+Ω₁}))`, at every restart with its own `A`), `yyTestOm2_wit` (non-vacuity at `m* = L(0)`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-- `ψ₃(0)·2 < Y₃`. -/
theorem yyG3_two_lt : S.psi 0 (Om (1 + 1 + 1)) * 2 < ugY S := by
  have hκ3 : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  have hG : S.psi 0 (Om (1 + 1 + 1)) < ugY S :=
    psi_lt_psi_of_mem hκ3 (Om_pos (add_pos_of_right zero_lt_one _).ne') (CSet.zero_mem _ _)
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
  exact uqY_SC.isPrincipal hG hG

/-- `0 + W^{Ω₃+0} = Ω₃` at the level `k = 0`. -/
theorem yyT0 : (0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) = Om (1 + 1 + 1) := by
  rw [add_zero, Vn.vnWe_OmK 0, zero_add, Nat.cast_zero, zero_add]

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **Every atom `ψ₂(Ω₃ + δ)` with `δ < Y₃·Ω₂` moves** at every window under the premise of WallBelow at it. -/
theorem yyTestMoveOm3 {δ : Ordinal.{0}} (hδ : δ < ugY S * Om (1 + 1))
    (hown : Om (1 + 1 + 1) + δ ∈ S.CSet (Om (1 + 1 + 1) + δ) (S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1))))
    (hH : Om (1 + 1 + 1) + δ ∈ cdHull S l)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1)))) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hδW : Om (1 + 1 + 1) + δ < Om ω := by
    refine vkOmW.1.isPrincipal Ry.ryOm3_lt (hδ.trans_le ?_ |>.trans (yyWY1_lt (S := S)))
    rw [leWe_succ, Vq.vqWeY3]
  have hs : S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨_, hH, hδW.trans_le (ConjT.OmW_le_A S _), rfl⟩
  have hTa := yyT0
  have hst : S.psi ((0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0)) (Om (1 + 1)) ≤
      S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1)) := by
    rw [hTa]; exact (psi_mono hκ2 le_self_add).1
  have hsT : S.psi (Om (1 + 1 + 1) + δ) (Om (1 + 1)) <
      leTe S (ugY S + 1) ((0 : Ordinal.{0}) + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0)) := by
    rw [hTa]
    unfold leTe
    refine psi_lt_psi_of_mem hκ2 ?_ ?_
    · rw [leWe_succ, Vq.vqWeY3]; exact (add_lt_add_iff_left _).2 hδ
    · have hW : leWe (ugY S + 1) = ugY S * Om (1 + 1) := by rw [leWe_succ, Vq.vqWeY3]
      have hle : Om (1 + 1 + 1) + δ ≤ Om (1 + 1 + 1) + leWe (ugY S + 1) :=
        (add_le_add_iff_left _).2 (hδ.le.trans hW.ge)
      exact CSet_mono hle (psi_mono hκ2 hle).1 hown
  obtain ⟨hρSC, -⟩ := leRho hR.1 (Xv.xvWin hR h1 hr hl' hB).1
  exact yyTopMoveY3W hR h1 hr hl' hB hA' hρ' 0 (GxCl.zero hρSC.1) (Xi.xiD_zero l) (Xi.xiBase_zero 0 l) hs hst
    hsT IH

/-- **REFUTE-FIRST at `δ = Y₃` over `t = Ω₃`**: the atom `ψ₂(Ω₃ + Y₃)` moves. -/
theorem yyTestY3
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + ugY S) (Om (1 + 1)))) := by
  have h3 : ∀ {x c : Ordinal.{0}}, Om (1 + 1 + 1) < x → ugY S ∈ S.CSet x c := fun h => Vq.vqY3_mem h
  have hlt : Om (1 + 1 + 1) < Om (1 + 1 + 1) + ugY S := lt_add_of_pos_right _ uqY_SC.1
  refine yyTestMoveOm3 hR h1 hr hl' hB hA' hρ' ?_ (CSet.add_mem (Ry.ryOm3_mem _ _) (h3 hlt))
    (CSet.add_mem (Ry.ryOm3_mem _ _) (h3 (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)))) IH
  calc ugY S = ugY S * 1 := (mul_one _).symm
    _ < ugY S * Om (1 + 1) := (mul_lt_mul_iff_right₀ uqY_SC.1).2 (gg_one_lt_of_SC ldOm2_SC)

/-- **REFUTE-FIRST at `δ = Y₃·2` over `t = Ω₃`**: the atom `ψ₂(Ω₃ + Y₃·2)` moves. -/
theorem yyTestY3two
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + ugY S * 2) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (Om (1 + 1 + 1) + ugY S * 2) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om (1 + 1 + 1) + ugY S * 2) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + ugY S * 2) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + ugY S * 2) (Om (1 + 1)))) := by
  have h3 : ∀ {x c : Ordinal.{0}}, Om (1 + 1 + 1) < x → ugY S ∈ S.CSet x c := fun h => Vq.vqY3_mem h
  have hlt : Om (1 + 1 + 1) < Om (1 + 1 + 1) + ugY S * 2 :=
    lt_add_of_pos_right _ (mul_pos uqY_SC.1 (by norm_num))
  have hm : ∀ {x c : Ordinal.{0}}, Om (1 + 1 + 1) < x → ugY S * 2 ∈ S.CSet x c := fun {x c} h => by
    have := ConjT.mul_nat_mem S (h3 (c := c) h) 2
    rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
  refine yyTestMoveOm3 hR h1 hr hl' hB hA' hρ' ?_ (CSet.add_mem (Ry.ryOm3_mem _ _) (hm hlt))
    (CSet.add_mem (Ry.ryOm3_mem _ _) (hm (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _)))) IH
  exact (mul_lt_mul_iff_right₀ uqY_SC.1).2
    ((show (2 : Ordinal.{0}) < ω by exact_mod_cast natCast_lt_omega0 2).trans (Lw.lw_omega_lt_SC ldOm2_SC))

/-- **REFUTE-FIRST at `δ = ψ₃(0)·2` over `t = Ω₃`**: the atom `ψ₂(Ω₃ + ψ₃(0)·2)` moves. -/
theorem yyTestG3
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (Om (1 + 1 + 1) + S.psi 0 (Om (1 + 1 + 1)) * 2) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (Om (1 + 1 + 1) + S.psi 0 (Om (1 + 1 + 1)) * 2) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (Om (1 + 1 + 1) + S.psi 0 (Om (1 + 1 + 1)) * 2) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + S.psi 0 (Om (1 + 1 + 1)) * 2) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + S.psi 0 (Om (1 + 1 + 1)) * 2) (Om (1 + 1)))) := by
  have hG : ∀ {x c : Ordinal.{0}}, 0 < x → S.psi 0 (Om (1 + 1 + 1)) * 2 ∈ S.CSet x c := fun {x c} h => by
    have := ConjT.mul_nat_mem S (b := c) (CSet.psi_mem h (InR_Om_succ (1 + 1)) (Ry.ryOm3_mem _ _) (CSet.zero_mem _ _)) 2
    rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
  have hpos : (0 : Ordinal.{0}) < Om (1 + 1 + 1) + S.psi 0 (Om (1 + 1 + 1)) * 2 :=
    (Om_pos (add_pos_of_right zero_lt_one _).ne').trans_le le_self_add
  refine yyTestMoveOm3 hR h1 hr hl' hB hA' hρ' ?_ (CSet.add_mem (Ry.ryOm3_mem _ _) (hG hpos))
    (CSet.add_mem (Ry.ryOm3_mem _ _) (hG ((Om_pos (add_pos_of_right zero_lt_one _).ne').trans
      (Ry.ryOm3_lt.trans_le (ConjT.OmW_le_A S _))))) IH
  calc S.psi 0 (Om (1 + 1 + 1)) * 2 < ugY S := yyG3_two_lt
    _ = ugY S * 1 := (mul_one _).symm
    _ < ugY S * Om (1 + 1) := (mul_lt_mul_iff_right₀ uqY_SC.1).2 (gg_one_lt_of_SC ldOm2_SC)

end Win

/-- **REFUTE-FIRST of (2') at `E = Ω₂` over `β = 0`**: `Θ(ψ₂(W^{Ω_{k+3}+Ω₂})) = ψ₁(A + 1 + ψ₂(Ω^{Ω_{k+2}+Ω₁}))` at every
restart with its own `A`. -/
theorem yyTestOm2 {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) (k : ℕ) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (leOe (Om ((k : Ordinal.{0}) + 1 + 1) + Om 1)) (Om (1 + 1))) (Om 1) := by
  have h := yyLawOm2 hl hX hA hρ k (Xi.xiD_zero l) (CSet.zero_mem _ _) (fun _ => dvd_zero _)
  obtain ⟨-, hT⟩ := yyTW hl hX k (Xi.xiD_zero l)
  rw [hT, Vh.vhT_zero hl hX, zero_add, zero_add] at h
  exact h

/-- **Non-vacuity of `yyTestOm2`**: at the restart of `m* = L(0)` with its own `A`. -/
theorem yyTestOm2_wit (S : InaccSeq.{0}) (k : ℕ) :
    ∃ l A : Ordinal.{0}, IsRestartIdx l ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧ S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (leOe (Om ((k : Ordinal.{0}) + 1 + 1) + Om 1)) (Om (1 + 1))) (Om 1) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  exact ⟨l, _, hl, hA, hρ, yyTestOm2 hl hX hA hρ k⟩

end Googology.Trans.PoR.InaccPsi.R2.Yy
