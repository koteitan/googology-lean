import Googology.Trans.PoR.InaccPsi.R2.UmLimB

/-!
# The collapse lemma over offsets past `Γ₂`

`W^E = Ω₂^E`, `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Γ₂ = ψ_{Ω₃}(0)`, `C_2(Q) = Ug.UgC S 2 Q`
(level-2 codes with the atoms `ψ_{Ω₃}(d)`), `CL E β X₀ = Sn.SnCL S E β X₀`, `CL₃ = Ug.UgCL` (with the atoms).

`Sj.sjCode` with the offset `X₀` a level-2 code (`X₀ + W^E < Y₃`) and the collapse bound `Uj.ujPsi2_le`.

* `umCl_mem` (**a level-2 code `x < a` over `Q` lies in `Cl(a, Q)`**: the atoms `ψ_{Ω₃}(d) ≤ x` have `d < a`);
* `umCode` (**THE COLLAPSE LEMMA PAST `Γ₂`**: every `y ≤ E` has a level-2 code over `T_y` in `[y, E]`);
* `umCollD` (**the collapse below an own level past `Γ₂`**: at a base, `CL₃ E β X₀` and `y ≤ E` give `z ∈ [y, E]`
  a level-2 code over every strongly critical `Q ≥ T_y`), `umCollD_le` (the same with `CL` for `E < Γ₂`: `z` is a
  code `Le.LeCl Ω₂ Q`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **A level-2 code `x < a` over `Q` lies in `Cl(a, Q)`.** -/
theorem umCl_mem {Q a x : Ordinal.{0}} (hx : UgC S (1 + 1) Q x) : x < a → x ∈ S.CSet a Q := by
  induction hx with
  | small h => exact fun _ => CSet.of_lt h
  | om => exact fun _ => mxOm2_mem _ _
  | @add x y _ _ ihx ihy =>
    exact fun h => CSet.add_mem (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => CSet.phi_mem (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @psi d _ hdl ihd =>
    intro h
    have hda : d < a := hdl.trans h
    exact CSet.psi_mem hda (InR_Om_succ (1 + 1))
      (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem _ _)))) (ihd hda)

section Code

variable {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q X0)
  (hX0G3 : X0 + leWe E < ugY S)
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **THE COLLAPSE LEMMA PAST `Γ₂`: every `y ≤ E` has a level-2 code over `T_y` in `[y, E]`.** -/
theorem umCode {y : Ordinal.{0}} (hyE : y ≤ E) :
    ∃ z, y ≤ z ∧ z ≤ E ∧ UgC S (1 + 1) (S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1))) z := by
  set Q := S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) with hQ_def
  by_contra H
  push Not at H
  have hQSC : SC Q := SC_psi (InR_Om_succ 1) _
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) _ 1).1
  have hG3 : SC (ugY S) := ujY_SC (S := S) 1
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < ugY S := ujY_gt (S := S) 1
  have h2 : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero
  have hdy : leWe (X0 + leWe y) ≤ leWe (X0 + leWe E) :=
    leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hyE))
  have hβQ : S.psi β (Om (1 + 1)) < Q :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ hdy)
  have hX0Q : UgC S (1 + 1) Q X0 :=
    hX0cl Q hQSC (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hTE : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q := by
    refine ujPsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact (psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβQ
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe E) := (add_lt_add_iff_left β).1 hx
    have hc2 := ugC_mod hQSC h2 (Om (1 + 1) * (X0 + leWe E)) hc
    change UgC S (1 + 1) Q ((β + x') % ugY S % leWe (X0 + leWe E)) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leWe E) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    rcases lt_or_ge x' (leWe (X0 + leWe y)) with hlt | hge
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hlt)
        (CSet.add_mem (hβown _ hdy) (umCl_mem hc2 (hlt.trans_le le_add_self)))
    · exfalso
      obtain ⟨h1, h2'⟩ := sjLogW hge hx'W
      have hMc : UgC S (1 + 1) Q (log ω x' / Om (1 + 1)) := ugC_div hQSC h2 _ (ugCDec hQSC h2 x' hc2).2
      have hXM : X0 ≤ log ω x' / Om (1 + 1) := le_self_add.trans h1
      have hMX := (ugCDec hQSC h2 _ hMc).1 X0 hX0Q hXM
      have e : X0 + (log ω x' / Om (1 + 1) - X0) = log ω x' / Om (1 + 1) := Ordinal.add_sub_cancel_of_le hXM
      have h1' : leWe y ≤ log ω x' / Om (1 + 1) - X0 := (add_le_add_iff_left X0).1 (by rw [e]; exact h1)
      have h2'' : log ω x' / Om (1 + 1) - X0 < leWe E := (add_lt_add_iff_left X0).1 (by rw [e]; exact h2')
      obtain ⟨h3, h4⟩ := sjLogW h1' h2''
      exact H _ h3 h4.le (ugC_div hQSC h2 _ (ugCDec hQSC h2 _ hMX).2)
  exact H E hyE le_rfl (hEcl Q hQSC hTE)

end Code

/-- **THE COLLAPSE BELOW AN OWN LEVEL PAST `Γ₂`**: at a base, `CL₃ E β X₀` and `y ≤ E` give a level-2 code
`z ∈ [y, E]` over every strongly critical `Q ≥ T_y(β, X₀)`. -/
theorem umCollD {l β X0 Xh0 E y : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hG3 : X0 + leWe E < ugY S) (hb : RoBaseE S l (X0 + leWe E) 0 β)
    (hcl : UgCL S E β X0) (hyE : y ≤ E) :
    ∃ z, y ≤ z ∧ z ≤ E ∧
      ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) ≤ Q → UgC S (1 + 1) Q z := by
  obtain ⟨hβd, -, -, hβown, -⟩ := hb
  rw [add_zero] at hβd hβown
  obtain ⟨-, -, -, -, hX0cl, -⟩ := ujOff_data hoff
  obtain ⟨z, h1, h2, hz⟩ := umCode (S := S) hβd hβown hX0cl hG3 hcl hyE
  exact ⟨z, h1, h2, fun Q _ hQ' => UgC.mono hQ' hz⟩

/-- **The collapse below an own level `E < Γ₂` past `Γ₂`** with the closure condition `CL`: the code `z` is a code
`Le.LeCl Ω₂ Q`. -/
theorem umCollD_le {l β X0 Xh0 E y : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hG3 : X0 + leWe E < ugY S) (hb : RoBaseE S l (X0 + leWe E) 0 β)
    (hcl : SnCL S E β X0) (hEG : E < Ua.uaGam) (hyE : y ≤ E) :
    ∃ z, y ≤ z ∧ z ≤ E ∧
      ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q z := by
  obtain ⟨z, h1, h2, hz⟩ := umCollD hoff hG3 hb (ugCL_of_sn hcl) hyE
  exact ⟨z, h1, h2, fun Q hQ hQ' => ugC_toLe (hz Q hQ hQ') (h2.trans_lt hEG)⟩

end Googology.Trans.PoR.InaccPsi.R2.Um
