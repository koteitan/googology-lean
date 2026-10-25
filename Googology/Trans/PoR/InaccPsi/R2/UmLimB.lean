import Googology.Trans.PoR.InaccPsi.R2.UmGam

/-!
# The hull-limit rule and the upgrade past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`,
`Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`.  A **base** for `X₀ + W^E` is `Ro.RoBaseE S λ (X₀ + W^E) 0 β`.

`St.stTopLimCore`, `St.stLevLimH`, `St.stLevLimB`, `St.stLevUp` with the offsets past `Γ₂` (`Uj.UjOff`), the own
data `Uj.UjOwP`, the level statement `Uj.UjLev`, the family `Uj.ujFam`, the shifts `Uj.ujSh_own` and the limit
shift `Uj.ujTopLimSh`.  No bound `E < Γ₂` is asked: the bounds are those of the offset (`< Y₃`, `< Y₂`).

* `umTopLimCore` (the top at `X₀ + W^E` over one offset past `Γ₂` from own data and a supply of members),
  `umLevLimH` (**THE HULL-LIMIT RULE PAST `Γ₂`**), `umLevLimB` (**the same with the members needed only at the
  bases**);
* `umLevUp` (**THE UPGRADE PAST `Γ₂`**: a level statement with own predicate `Ow` holds with every monotone own
  predicate `Ow'` that gives `Ow` at the bases).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `X₀ + W^E` over one offset past `Γ₂`** from own data and a supply of members. -/
theorem umTopLimCore {E Eh b X0 Xh0 : Ordinal.{0}} (hoff : UjOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < ugY S)
    (hG : Xh0 + leOe Eh + Om 1 < ujY S 0) (hEo : UjOwn S l b X0 E Eh)
    (hup : ∀ y, y ∈ cdHull S l → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ z, z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    RvTop S l b (X0 + leWe E) (Xh0 + leOe Eh) 0 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 := sqTh_one (S := S) hl hX
  -- a member `X₀ + W^e`
  have hm : ∀ e eh (Owe : Ordinal.{0} → Ordinal.{0} → Prop), UjOwP S l Owe e eh → UjLev S l Owe e eh →
      Owe b X0 → e < E → eh < Eh →
      UjSh S l b (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) ∧
      RvTop S l b (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) 0 := by
    intro e eh Owe hPk hLk hOk hek hehk
    have hE1 : e + 1 ≤ E := Order.add_one_le_of_lt hek
    have hdE : leWe (e + 1) ∣ X0 := (leWe_dvd hE1).trans hd
    have hG3' : X0 + leWe (e + 1) + Om (1 + 1) < ugY S :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hE1)) _) hG3
    have hG' : Xh0 + leOe (eh + 1) + Om 1 < ujY S 0 :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2
        (leOe_mono (Order.add_one_le_of_lt hehk))) _) hG
    have h := ujFam hl hX hPk hLk hoff hdE hG3' hG' hOk 1
      (GxCl.small (gg_one_lt_of_SC hρSC)) ⟨0, show (1 : Ordinal.{0}) < Om 1 from sqOne_lt_Om1⟩
      (by rw [hΘ1]; exact sqOne_lt_Om1)
    refine ujOff_ne h fun h' => (leWe_pos e).ne' ?_
    have := le_antisymm (h' ▸ le_add_self : leWe e * 1 ≤ 0) zero_le
    rwa [mul_one] at this
  -- the shift `X₀ + W^E`
  have hs : UjSh S l b (X0 + leWe E) (Xh0 + leOe Eh) := ujSh_own hoff hEo hG3 hG
  refine ujTopLimSh hl hX hs ?_ ?_
  · intro x hxH hx
    obtain ⟨e, eh, Owe, hPk, hLk, hOk, hek, hehk, hyx⟩ : ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
        UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe b X0 ∧ e < E ∧ eh < Eh ∧ x < X0 + leWe e := by
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
        UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe b X0 ∧ e < E ∧ eh < Eh ∧ z < Xh0 + leOe eh := by
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

/-- **THE HULL-LIMIT RULE PAST `Γ₂`.** -/
theorem umLevLimH {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : UjOwP S l Ow E Eh)
    (hup : ∀ b X0, Ow b X0 → ∀ y, y ∈ cdHull S l → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ b X0, Ow b X0 → ∀ z, z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe b X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    UjLev S l Ow E Eh :=
  fun b X0 _Xh0 hoff hd hG3 hG hOw => umTopLimCore hl hX hoff hd hG3 hG (hP.dat b X0 hOw)
    (hup b X0 hOw) (hlo b X0 hOw)

/-- **THE HULL-LIMIT RULE PAST `Γ₂` AT THE BASES**: the members are needed only at the bases of `X₀ + W^E`. -/
theorem umLevLimB {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : UjOwP S l Ow E Eh)
    (hup : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < ugY S →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ y, y ∈ cdHull S l → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < ugY S →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ z, z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    UjLev S l Ow E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw β Â hb hbβ hÂ hbase
  have hoffβ := ujOff_mono hbβ hoff
  have hOwβ := hP.mono b β X0 X0 hOw hbβ le_rfl
  exact umTopLimCore hl hX hoffβ hd hG3 hG (hP.dat β X0 hOwβ)
    (hup β X0 Xh0 hoffβ hd hG3 hb hOwβ) (hlo β X0 Xh0 hoffβ hd hG3 hb hOwβ) β Â hb le_rfl hÂ hbase

end Main

/-- **THE UPGRADE PAST `Γ₂`**: `UjLev Ow` gives `UjLev Ow'` for a monotone `Ow'` that gives `Ow` at the bases. -/
theorem umLevUp {l : Ordinal.{0}} {Ow Ow' : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}}
    (hL : UjLev S l Ow E Eh) (hmono : ∀ b β X0, Ow' b X0 → b ≤ β → Ow' β X0)
    (hconv : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 →
      X0 + leWe E + Om (1 + 1) < ugY S → RoBaseE S l (X0 + leWe E) 0 β → Ow' β X0 → Ow β X0) :
    UjLev S l Ow' E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw β Â hb hbβ hÂ hbase
  have hoffβ := ujOff_mono hbβ hoff
  exact hL β X0 Xh0 hoffβ hd hG3 hG (hconv β X0 Xh0 hoffβ hd hG3 hb (hmono b β X0 hOw hbβ)) β Â hb le_rfl hÂ hbase


end Googology.Trans.PoR.InaccPsi.R2.Um
