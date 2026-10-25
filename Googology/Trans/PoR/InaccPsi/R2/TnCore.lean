import Googology.Trans.PoR.InaccPsi.R2.TnLim

/-!
# The level statement from members asked only at codes

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_X(β) = ψ_{Ω₂}(β + W^X)`, `G1 = ψ_{Ω₂}(0)`,
`G3 = ψ_{Ω₃}(0)`.

* `tnTopLimCore` (**the top at `X₀ + W^E` over one offset from own data and a supply of members asked only at the
  exponents `X₀ + y` that lie in `Cl(β + W^{X₀+y+1}, T_{X₀+y+1}(β))` and at the level-1 codes `z < Ω^Ê` over
  `Θ(T_{X₀+W^E}(β))`**, at every base `β ≥ b`; `Tn.tnTopLimC` with the members of `Sc.scFam`);
* `tnLevLimC` (**THE LEVEL STATEMENT FROM CODE-RESTRICTED MEMBERS**: the same with the members needed only at the
  bases of `X₀ + W^E`; the code-restricted version of `St.stLevLimB`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `X₀ + W^E` over one offset from members asked only at codes.** -/
theorem tnTopLimCore {E Eh b X0 Xh0 : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe Eh + Om 1 < S.psi 0 (Om (1 + 1))) (hEo : ScOwn S l b X0 E Eh)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hup : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → ∀ y, y ∈ cdHull S l →
      X0 + y ∈ S.CSet (β + leWe (X0 + y + 1)) (S.psi (β + leWe (X0 + y + 1)) (Om (1 + 1))) → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → ∀ z,
      LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) z → z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    RvTop S l b (X0 + leWe E) (Xh0 + leOe Eh) 0 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hG3S := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  -- a member `X₀ + W^e` relative to the base `β`
  have hm : ∀ β, b ≤ β → ∀ e eh (Owe : Ordinal.{0} → Ordinal.{0} → Prop), ScOwP S l Owe e eh →
      ScLev S l Owe e eh → Owe β X0 → e < E → eh < Eh →
      RvSh S l β (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) ∧
      RvTop S l β (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) 0 := by
    intro β hbβ e eh Owe hPk hLk hOk hek hehk
    have hE1 : e + 1 ≤ E := Order.add_one_le_of_lt hek
    have hdE : leWe (e + 1) ∣ X0 := (leWe_dvd hE1).trans hd
    have hG3' : X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hE1)) _) hG3
    have hG' : Xh0 + leOe (eh + 1) + Om 1 < S.psi 0 (Om (1 + 1)) :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2
        (leOe_mono (Order.add_one_le_of_lt hehk))) _) hG
    have h := scFam hl hX hPk hLk (rvOff_mono hbβ hoff) hdE hG3' hG' hOk 1
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
  -- the image `Θ(T)` is strongly critical and a member exists at every base
  have hTSC : ∀ β, RoBaseE S l (X0 + leWe E) 0 β →
      SC (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) := by
    intro β hb
    obtain ⟨-, hβH, hβA, -, -⟩ := hb
    rw [add_zero] at hβA
    exact (ldAtom_ge hρSC hρ1 hAt ⟨β + leWe (X0 + leWe E), CSet.add_mem hβH (leWe_mem hs.hull), hβA, rfl⟩).1
  have hany : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh := by
    intro β hbβ hb
    obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -⟩ := hlo β hbβ hb 0 (LeCl.zero (hTSC β hb).1) (leOe_pos _)
    exact ⟨e, eh, Owe, a1, a2, a3, a4, a5⟩
  refine tnTopLimC hl hX hs ?_ ?_
  · intro β Â hb hbβ hÂ hbase x hxH hxC hx
    obtain ⟨e, eh, Owe, hPk, hLk, hOk, hek, hehk, hyx⟩ : ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
        ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧ e < E ∧ eh < Eh ∧ x < X0 + leWe e := by
      rcases lt_or_ge x X0 with h | h
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5⟩ := hany β hbβ hb
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        have hy : y < leWe E := (add_lt_add_iff_left X0).1 hx
        have hyH : y ∈ cdHull S l := snHullRem hxH hd hy
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, a6⟩ := hup β hbβ hb y hyH hxC hy
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, (add_lt_add_iff_left X0).2 a6⟩
    obtain ⟨hsk, htk⟩ := hm β hbβ e eh Owe hPk hLk hOk hek hehk
    refine ⟨_, _, ?_, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_le_add_iff_left X0).2 (leWe_mono hek.le)
    · rw [mul_one]; exact hyx
    · rw [hΘ1, mul_one]; exact (add_lt_add_iff_left Xh0).2 (leOe_lt hehk)
  · intro β Â hb hbβ hÂ hbase z hzc hz
    obtain ⟨e, eh, Owe, hPk, hLk, hOk, hek, hehk, hzk⟩ : ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
        ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧ e < E ∧ eh < Eh ∧ z < Xh0 + leOe eh := by
      rcases lt_or_ge z Xh0 with h | h
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5⟩ := hany β hbβ hb
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        have hXh0c : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) Xh0 := by
          obtain ⟨-, -, -, -, -, hcl⟩ := rvOff_data hoff
          refine hcl _ (hTSC β hb) (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) ?_).1)
          exact add_le_add hbβ (leWe_mono le_self_add)
        have hyc : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) y := by
          have h1 := (leClDec (hTSC β hb) Ph.ph_SC_Om1 _ hzc).1 _ hXh0c le_self_add
          rwa [Ordinal.add_sub_cancel] at h1
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, a6⟩ :=
          hlo β hbβ hb y hyc ((add_lt_add_iff_left Xh0).1 hz)
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, (add_lt_add_iff_left Xh0).2 a6⟩
    obtain ⟨hsk, htk⟩ := hm β hbβ e eh Owe hPk hLk hOk hek hehk
    refine ⟨_, _, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_lt_add_iff_left X0).2 (leWe_lt hek)
    · rw [hΘ1, mul_one]; exact hzk

/-- **THE LEVEL STATEMENT FROM CODE-RESTRICTED MEMBERS** (the members are needed only at the bases). -/
theorem tnLevLimC {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : ScOwP S l Ow E Eh)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hup : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ y, y ∈ cdHull S l →
      X0 + y ∈ S.CSet (β + leWe (X0 + y + 1)) (S.psi (β + leWe (X0 + y + 1)) (Om (1 + 1))) → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ z,
      LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) z → z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    ScLev S l Ow E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw
  exact tnTopLimCore hl hX hoff hd hG3 hG (hP.dat b X0 hOw) hEG hEhG
    (fun β hbβ hb => hup β X0 Xh0 (rvOff_mono hbβ hoff) hd hG3 hb (hP.mono b β X0 X0 hOw hbβ le_rfl))
    (fun β hbβ hb => hlo β X0 Xh0 (rvOff_mono hbβ hoff) hd hG3 hb (hP.mono b β X0 X0 hOw hbβ le_rfl))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tn
