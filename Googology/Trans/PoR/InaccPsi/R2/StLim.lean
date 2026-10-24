import Googology.Trans.PoR.InaccPsi.R2.StAt

/-!
# Three rules for the level statements: the hull-limit rule, the collapse below an own level, the upgrade

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`,
`CL E β X₀ = Sn.SnCL S E β X₀` (`E` is a code over every strongly critical `Q ≥ T_E(β, X₀)`).
A **base** for `X₀ + W^E` is `Ro.RoBaseE S λ (X₀ + W^E) 0 β`.

* `stTopLimCore` (the top at `X₀ + W^E` over one offset from own data and a supply of members),
  `stLevLimH` (**THE HULL-LIMIT RULE**: `Sq.sqLevLim` with the members chosen per element: if every hull element
  `y < W^E` lies below some `W^e` and every `z < Ω^Ê` below some `Ω^ê`, `e < E`, `ê < Ê` a level whose own
  predicate holds, then `Sc.ScLev Ow E Ê`), `stLevLimB` (**the same with the members needed only at the bases**);
* `stCollD` (**THE COLLAPSE BELOW AN OWN LEVEL**: at a base, `CL E β X₀` and `y ≤ E` give `z ∈ [y, E]` that is a
  code over every strongly critical `Q ≥ T_y(β, X₀)`; `Sj.sjCode`);
* `stLevUp` (**THE UPGRADE**: a level statement with own predicate `Ow` holds with every monotone own predicate
  `Ow'` that gives `Ow` at the bases).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.St

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `X₀ + W^E` over one offset** from own data and a supply of members. -/
theorem stTopLimCore {E Eh b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe Eh + Om 1 < S.psi 0 (Om (1 + 1))) (hEo : ScOwn S l b X0 E Eh)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hup : ∀ y, y ∈ cdHull S l → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ z, z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    RvTop S l b (X0 + leWe E) (Xh0 + leOe Eh) 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 := sqTh_one (S := S) hl hX
  have hG3S := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  -- a member `X₀ + W^e`
  have hm : ∀ e eh (Owe : Ordinal.{0} → Ordinal.{0} → Prop), ScOwP S l Owe e eh → ScLev S l Owe e eh →
      Owe b X0 → e < E → eh < Eh →
      RvSh S l b (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) ∧
      RvTop S l b (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) 0 := by
    intro e eh Owe hPk hLk hOk hek hehk
    have hE1 : e + 1 ≤ E := Order.add_one_le_of_lt hek
    have hdE : leWe (e + 1) ∣ X0 := (leWe_dvd hE1).trans hd
    have hG3' : X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hE1)) _) hG3
    have hG' : Xh0 + leOe (eh + 1) + Om 1 < S.psi 0 (Om (1 + 1)) :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2
        (leOe_mono (Order.add_one_le_of_lt hehk))) _) hG
    have h := scFam hl hX hPk hLk hoff hdE hG3' hG' hOk 1
      (GxCl.small (gg_one_lt_of_SC hρSC)) ⟨0, show (1 : Ordinal.{0}) < Om 1 from sqOne_lt_Om1⟩
      (by rw [hΘ1]; exact sqOne_lt_Om1)
    refine rvOff_ne h fun h' => (leWe_pos e).ne' ?_
    have := le_antisymm (h' ▸ le_add_self : leWe e * 1 ≤ 0) zero_le
    rwa [mul_one] at this
  -- the shift `X₀ + W^E`
  have hX0 : X0 < S.psi 0 (Om (1 + 1 + 1)) := (le_self_add.trans le_self_add).trans_lt hG3
  have hXh0 : Xh0 < S.psi 0 (Om (1 + 1)) := (le_self_add.trans le_self_add).trans_lt hG
  have hW : leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    (leWe_lt_SC hG3S rwW_lt_G3 (hG3S.isSuccLimit.succ_lt hEG)).1
  have hO : leOe (Eh + 1) < S.psi 0 (Om (1 + 1)) :=
    (leOe_lt_SC hG1 rwO_lt_G (hG1.isSuccLimit.succ_lt hEhG)).1
  have hs : RvSh S l b (X0 + leWe E) (Xh0 + leOe Eh) := by
    have h := scSh_m hl hX hoff hEo (ζ := 1) (GxCl.small (gg_one_lt_of_SC hρSC))
      (gg_one_lt_of_SC ldOm2_SC) one_ne_zero (sqOne_lt_Om1.trans (psiS_bounds (S := S) _ 1).1)
      (by rw [hΘ1]; exact sqOne_lt_Om1) (hG3S.isPrincipal (hG3S.isPrincipal hX0 hW) rwW_lt_G3)
      (hG1.isPrincipal (hG1.isPrincipal hXh0 hO) rwO_lt_G)
    rwa [mul_one, hΘ1, mul_one] at h
  refine rvTopLimSh hl hX hs ?_ ?_
  · intro x hxH hx
    obtain ⟨e, eh, Owe, hPk, hLk, hOk, hek, hehk, hyx⟩ : ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
        ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe b X0 ∧ e < E ∧ eh < Eh ∧ x < X0 + leWe e := by
      rcases lt_or_ge x X0 with h | h
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -⟩ := hlo 0 (leOe_pos _)
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        have hy : y < leWe E := (add_lt_add_iff_left X0).1 hx
        have hyH : y ∈ cdHull S l := snHullRem hxH hd hy
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, a6⟩ := hup y hyH hy
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, (add_lt_add_iff_left X0).2 a6⟩
    obtain ⟨hsk, htk⟩ := hm e eh Owe hPk hLk hOk hek hehk
    refine ⟨_, _, ?_, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_le_add_iff_left X0).2 (leWe_mono hek.le)
    · rw [mul_one]; exact hyx
    · rw [hΘ1, mul_one]; exact (add_lt_add_iff_left Xh0).2 (leOe_lt hehk)
  · intro z hz
    obtain ⟨e, eh, Owe, hPk, hLk, hOk, hek, hehk, hzk⟩ : ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
        ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe b X0 ∧ e < E ∧ eh < Eh ∧ z < Xh0 + leOe eh := by
      rcases lt_or_ge z Xh0 with h | h
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -⟩ := hlo 0 (leOe_pos _)
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, a6⟩ := hlo y ((add_lt_add_iff_left Xh0).1 hz)
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, (add_lt_add_iff_left Xh0).2 a6⟩
    obtain ⟨hsk, htk⟩ := hm e eh Owe hPk hLk hOk hek hehk
    refine ⟨_, _, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_lt_add_iff_left X0).2 (leWe_lt hek)
    · rw [hΘ1, mul_one]; exact hzk

/-- **THE HULL-LIMIT RULE.** -/
theorem stLevLimH {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : ScOwP S l Ow E Eh)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hup : ∀ b X0, Ow b X0 → ∀ y, y ∈ cdHull S l → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ b X0, Ow b X0 → ∀ z, z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    ScLev S l Ow E Eh :=
  fun b X0 Xh0 hoff hd hG3 hG hOw => stTopLimCore hl hX hoff hd hG3 hG (hP.dat b X0 hOw) hEG hEhG
    (hup b X0 hOw) (hlo b X0 hOw)

/-- **THE HULL-LIMIT RULE AT THE BASES**: the members are needed only at the bases of `X₀ + W^E`. -/
theorem stLevLimB {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : ScOwP S l Ow E Eh)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hup : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ y, y ∈ cdHull S l → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ z, z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    ScLev S l Ow E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw β Â hb hbβ hÂ hbase
  have hoffβ := rvOff_mono hbβ hoff
  have hOwβ := hP.mono b β X0 X0 hOw hbβ le_rfl
  exact stTopLimCore hl hX hoffβ hd hG3 hG (hP.dat β X0 hOwβ) hEG hEhG
    (hup β X0 Xh0 hoffβ hd hG3 hb hOwβ) (hlo β X0 Xh0 hoffβ hd hG3 hb hOwβ) β Â hb le_rfl hÂ hbase

end Main

/-- **THE COLLAPSE BELOW AN OWN LEVEL**: at a base, `CL E β X₀` and `y ≤ E` give a code `z ∈ [y, E]` over
every strongly critical `Q ≥ T_y(β, X₀)`. -/
theorem stCollD {l β X0 Xh0 E y : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1))) (hb : RoBaseE S l (X0 + leWe E) 0 β)
    (hcl : SnCL S E β X0) (hyE : y ≤ E) :
    ∃ z, y ≤ z ∧ z ≤ E ∧
      ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q z := by
  obtain ⟨hβd, -, -, hβown, -⟩ := hb
  rw [add_zero] at hβd hβown
  obtain ⟨-, -, -, -, hX0cl, -⟩ := rvOff_data hoff
  obtain ⟨z, h1, h2, hz⟩ := sjCode (S := S) hβd hβown hX0cl hG3 hcl hyE
  exact ⟨z, h1, h2, fun Q _ hQ' => snLeCl_mono hz hQ'⟩

/-- **THE UPGRADE**: `ScLev Ow` gives `ScLev Ow'` for a monotone `Ow'` that gives `Ow` at the bases. -/
theorem stLevUp {l : Ordinal.{0}} {Ow Ow' : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}}
    (hL : ScLev S l Ow E Eh) (hmono : ∀ b β X0, Ow' b X0 → b ≤ β → Ow' β X0)
    (hconv : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 →
      X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) → RoBaseE S l (X0 + leWe E) 0 β → Ow' β X0 → Ow β X0) :
    ScLev S l Ow' E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw β Â hb hbβ hÂ hbase
  have hoffβ := rvOff_mono hbβ hoff
  exact hL β X0 Xh0 hoffβ hd hG3 hG (hconv β X0 Xh0 hoffβ hd hG3 hb (hmono b β X0 hOw hbβ)) β Â hb le_rfl hÂ hbase

end Googology.Trans.PoR.InaccPsi.R2.St
