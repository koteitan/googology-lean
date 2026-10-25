import Googology.Trans.PoR.InaccPsi.R2.UjCode

/-!
# The own parameters of a shape past `Γ₂`: `T_{X₀ + G*}(β) = sup_j SQ_j` over offsets past `Γ₂`

`W^E = Ω₂^E`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `SQ_j = Sc.scSq S G X₀ β j` (`SQ_0 = Ω₁`,
`SQ_{j+1} = ψ_{Ω₂}(β + W^{X₀ + G(SQ_j)})`), `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`, `Γ₂ = ψ_{Ω₃}(0)`,
`C_k(Q) = Ug.UgC S k Q` (codes of level `k` with `ψ_{Ω_{k+1}}`-atoms).

`Sc.scSq_lt_succ`, `Sc.scSq_sup`, `Sc.scSq_ge`, `Sc.scSq_gtT` with the offset `X₀` own relative to itself
(`X₀ ∈ Cl(X₀, ·)`, since `Γ₂` is in no `Cl(0, ·)`), the level codes `C_2` for `X₀` and the bound `Y₃`.  The closure
law of a shape is asked for the level codes (`UmShCl`, `UmImCl`); below `Γ₂` (resp. `ψ_{Ω₂}(0)`) it is the closure
law of `Sc` (`umShCl_of_sc`, `umImCl_of_sc`), since the level codes below these bounds have no atom
(`Ug.ugC_toLe`, `umC1_toLe`).

* `UmShCl`, `UmImCl`, `umC1_toLe`, `umShCl_of_sc`, `umImCl_of_sc`;
* `umSq_lt_succ`, `umSq_mono`, `umSq_sup` (**`T_{X₀ + G*}(β) = sup_j SQ_j` over offsets past `Γ₂`**), `umSq_ge`,
  `umSq_gtT`.

No new axiom.  New definitions: `UmShCl`, `UmImCl`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **The closure law of a shape `G` with top `G*` at `Q` for the level-2 codes.** -/
def UmShCl (S : InaccSeq.{0}) (G : Ordinal.{0} → Ordinal.{0}) (Gs Q : Ordinal.{0}) : Prop :=
  ∀ w, UgC S (1 + 1) Q w → w < Om (1 + 1) * Gs → ∃ ζ, ζ < Q ∧ w < Om (1 + 1) * G ζ

/-- **The closure law of an image shape `Ĝ` with top `Ĝ*` at `Q` for the level-1 codes.** -/
def UmImCl (S : InaccSeq.{0}) (Gh : Ordinal.{0} → Ordinal.{0}) (Ghs Q : Ordinal.{0}) : Prop :=
  ∀ w, UgC S 1 Q w → w < Om 1 * Ghs → ∃ v, v < Q ∧ w < Om 1 * Gh (v + 1)

/-- **A level-1 code below `ψ_{Ω₂}(0)` is a code without atoms.** -/
theorem umC1_toLe {Q x : Ordinal.{0}} (hx : UgC S 1 Q x) : x < S.psi 0 (Om (1 + 1)) → LeCl (Om 1) Q x := by
  induction hx with
  | small h => exact fun _ => LeCl.small h
  | om => exact fun _ => LeCl.om
  | @add x y _ _ ihx ihy =>
    exact fun h => LeCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => LeCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @psi d _ _ _ => exact fun h => absurd (psi_mono (S := S) (InR_Om_succ 1) zero_le).1 (not_le.2 h)

/-- **Below `Γ₂` the closure law of `Sc` is the closure law for the level-2 codes.** -/
theorem umShCl_of_sc {G : Ordinal.{0} → Ordinal.{0}} {Gs Q : Ordinal.{0}} (h : ScShCl G Gs Q)
    (hG : Om (1 + 1) * Gs ≤ Ua.uaGam) : UmShCl S G Gs Q :=
  fun w hw hlt => h w (ugC_toLe hw (hlt.trans_le hG)) hlt

/-- **Below `ψ_{Ω₂}(0)` the image closure law of `Sc` is the one for the level-1 codes.** -/
theorem umImCl_of_sc {Gh : Ordinal.{0} → Ordinal.{0}} {Ghs Q : Ordinal.{0}} (h : ScImCl Gh Ghs Q)
    (hG : Om 1 * Ghs ≤ S.psi 0 (Om (1 + 1))) : UmImCl S Gh Ghs Q :=
  fun w hw hlt => h w (umC1_toLe hw (hlt.trans_le hG)) hlt

section Seq

variable {G : Ordinal.{0} → Ordinal.{0}} {X0 β : Ordinal.{0}}
  {Gs : Ordinal.{0}} (hGst : StrictMono G) (hGs : ∀ x, x < Om (1 + 1) → G x ≤ Gs)
  (hβown : ∀ d, d ≤ leWe (X0 + Gs) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0m : X0 ∈ S.CSet X0 (S.psi (β + leWe X0) (Om (1 + 1))))
  (hGm : ∀ x c, x ∈ S.CSet 0 c → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c → G x ∈ S.CSet 0 c)

include hGst hGs hβown hX0m hGm

theorem umSq_lt_succ : ∀ j, scSq S G X0 β j < scSq S G X0 β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := umSq_lt_succ j
    have hle : scSq S G X0 β (j + 1) ≤ scSq S G X0 β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone IH.le))))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (hGst IH)))) ?_
    set c := scSq S G X0 β (j + 2) with hc
    have hX0 : X0 ∈ S.CSet (β + leWe (X0 + G (scSq S G X0 β (j + 1)))) c :=
      CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
    have hbot : S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
        ((add_le_add_iff_left X0).2 (hGst.monotone (scSq_Om1_le (j + 1))))))).1
    have hGj : G (scSq S G X0 β j) ∈ S.CSet 0 c := hGm _ c (CSet.of_lt (IH.trans_le hle)) hbot
    exact CSet.add_mem (hβown _ (leWe_mono ((add_le_add_iff_left X0).2 (hGs _ (scSq_lt_Om2 _)))))
      (leWe_mem (CSet.add_mem hX0 (CSet_mono zero_le le_rfl hGj)))

theorem umSq_mono {j j' : ℕ} (h : j ≤ j') : scSq S G X0 β j ≤ scSq S G X0 β j' :=
  (strictMono_nat_of_lt_succ (fun i => umSq_lt_succ hGst hGs hβown hX0m hGm i)).monotone h

/-- **`T_{X₀ + G*}(β) = sup_j SQ_j`** for a shape `G` with its closure law, over an offset past `Γ₂`. -/
theorem umSq_sup (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → UmShCl S G Gs Q)
    (hβd : leWe (X0 + Gs) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q X0)
    (hX0G3 : X0 + Gs < ugY S)
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + Gs) β) : ∃ j, x < scSq S G X0 β j := by
  have hbdd : BddAbove (Set.range (scSq S G X0 β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, scSq S G X0 β j ↔ ∃ j, y < scSq S G X0 β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, scSq S G X0 β j < ⨆ j, scSq S G X0 β j :=
    fun j => (hlt _).2 ⟨j + 1, umSq_lt_succ hGst hGs hβown hX0m hGm j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, scSq S G X0 β j := hKQ 0
  have hQSC : SC (⨆ j, scSq S G X0 β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (umSq_mono hGst hGs hβown hX0m hGm (le_max_left i j))
    have hj' := hj.trans_le (umSq_mono hGst hGs hβown hX0m hGm (le_max_right i j))
    exact ((scSq_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, scSq S G X0 β j with hQ
  have hG3 : SC (ugY S) := ujY_SC (S := S) 1
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hbot1 : S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) = scSq S G X0 β 1 := rfl
  have hX1 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ scSq S G X0 β 1 :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hβ1 : S.psi β (Om (1 + 1)) ≤ scSq S G X0 β 1 :=
    (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1.trans hX1
  have hFQ : leTe S (X0 + Gs) β ≤ Q := by
    refine ujPsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact ((psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans hβ1).trans_lt (hKQ 1)
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + Gs) := (add_lt_add_iff_left β).1 hx
    rcases eq_or_ne x' 0 with rfl | hx0
    · rw [add_zero]; exact hβ1.trans_lt (hKQ 1)
    have hc2 := ugC_mod hQSC h2 (Om (1 + 1) * (X0 + Gs)) hc
    change UgC S (1 + 1) Q ((β + x') % ugY S % leWe (X0 + Gs)) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + Gs) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    obtain ⟨-, hlog⟩ := ugCDec hQSC h2 x' hc2
    have hla : log ω x' < Om (1 + 1) * X0 + Om (1 + 1) * Gs := by
      rw [← mul_add]
      exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx'W)
    have hx'lt := lt_opow_succ_log_self one_lt_omega0 x'
    rw [Order.succ_eq_add_one] at hx'lt
    rcases lt_or_ge (log ω x') (Om (1 + 1) * X0) with h1 | h1
    · have hxX : x' < leWe X0 := hx'lt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxX.le)).1.trans hX1).trans_lt
        (hKQ 1)
    have hXC : UgC S (1 + 1) Q (Om (1 + 1) * X0) :=
      ugC_mulK hQSC h2 X0 (hX0cl Q hQSC (hX1.trans_lt (hKQ 1)).le)
    have hu := (ugCDec hQSC h2 (log ω x') hlog).1 _ hXC h1
    have hdec : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) = log ω x' := Ordinal.add_sub_cancel_of_le h1
    have hu2 : log ω x' - Om (1 + 1) * X0 < Om (1 + 1) * Gs := by
      have : Om (1 + 1) * X0 + (log ω x' - Om (1 + 1) * X0) < Om (1 + 1) * X0 + Om (1 + 1) * Gs := by
        rw [hdec]; exact hla
      exact (add_lt_add_iff_left _).1 this
    obtain ⟨ζ, hζQ, hζ⟩ := hcl Q hQSC (by rw [hbot1]; exact (hKQ 1).le) _ hu hu2
    obtain ⟨j, hj⟩ := (hlt _).1 hζQ
    have h2' : log ω x' + 1 ≤ Om (1 + 1) * (X0 + G (scSq S G X0 β j)) := by
      rw [mul_add, ← hdec, add_assoc]
      exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt (hζ.trans_le
        (mul_le_mul_right (hGst.monotone hj.le) _)))
    have hxW : x' < leWe (X0 + G (scSq S G X0 β j)) := hx'lt.trans_le (opow_le_opow_right omega0_pos h2')
    exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hxW.le)).1).trans_lt (hKQ (j + 1))
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{X₀ + G x}) ≥ T_{X₀ + G*}(β)` for `x ≥ T_{X₀ + G*}(β)`, over an offset past `Γ₂`. -/
theorem umSq_ge (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → UmShCl S G Gs Q)
    (hβd : leWe (X0 + Gs) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q X0)
    (hX0G3 : X0 + Gs < ugY S)
    {x : Ordinal.{0}} (hx : leTe S (X0 + Gs) β ≤ x) :
    leTe S (X0 + Gs) β ≤ S.psi (β + leWe (X0 + G x)) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := umSq_sup hGst hGs hβown hX0m hGm hcl hβd hX0cl hX0G3 h
  have h1 : scSq S G X0 β (j + 1) ≤ S.psi (β + leWe (X0 + G x)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone ((scSq_le_top hGs j).trans hx)))))).1
  exact absurd (hj.trans_le ((umSq_lt_succ hGst hGs hβown hX0m hGm j).le.trans h1)) (lt_irrefl _)

/-- **Every code below the top is an own parameter of the shape**, over an offset past `Γ₂`. -/
theorem umSq_gtT (hcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → UmShCl S G Gs Q)
    (hβd : leWe (X0 + Gs) ∣ β)
    (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q X0)
    (hX0G3 : X0 + Gs < ugY S)
    {x : Ordinal.{0}} (hx : x < leTe S (X0 + Gs) β) :
    x < S.psi (β + leWe (X0 + G x)) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := umSq_sup hGst hGs hβown hX0m hGm hcl hβd hX0cl hX0G3 hx
  exact scSq_gt hGst.monotone j x hj

end Seq

end Googology.Trans.PoR.InaccPsi.R2.Um
