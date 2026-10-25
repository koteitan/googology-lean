import Googology.Trans.PoR.InaccPsi.R2.UmTopC

/-!
# The level statement past `Γ₂` from code-restricted members, and the generic limit step past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_X(β) = ψ_{Ω₂}(β + W^X)`, `CL = Sn.SnCL`,
`G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`, `Y₃ = ψ_{Ω₃}(Ω₃)`, `Y₂ = ψ_{Ω₂}(Ω₂)`.

`Tn.tnTopLimCore`, `Tn.tnLevLimC`, `Tn.tnLevLimM` with the offsets past `Γ₂` (`Uj.UjOff`), the own data `Uj.UjOwP`,
the level statement `Uj.UjLev`, the family `Uj.ujFam`, the shifts `Uj.ujSh_own`, the limit rule restricted to codes
`Um.umTopLimC` and the level-1 codes `Ug.UgC S 1` (below `G1` they are the codes `Le.LeCl Ω₁`, `Um.umC1_toLe`).

* `umTopLimCoreC` (the top at `X₀ + W^E` over one offset past `Γ₂` from members asked only at codes);
* `umLevLimC` (**THE LEVEL STATEMENT PAST `Γ₂` FROM CODE-RESTRICTED MEMBERS**, members only at the bases);
* `umLevLimM` (**THE GENERIC LIMIT STEP PAST `Γ₂`**: (COF), (COF̂), the own data of `E < G3` (image `Ê < G1`), and
  for every code `1 ≤ c < Ω₂` the own data and the level statement past `Γ₂` of `M(c) < E` with the image
  `M̂(Θ c) < Ê`, the closure condition of `M(c)` at a base from `c < T_{M(c)}` ⇒ `UjLev (CL E) E Ê`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The top at `X₀ + W^E` over one offset past `Γ₂` from members asked only at codes.** -/
theorem umTopLimCoreC {E Eh b X0 Xh0 : Ordinal.{0}} (hoff : UjOff S l b X0 Xh0) (hd : leWe E ∣ X0)
    (hG3 : X0 + leWe E + Om (1 + 1) < ugY S)
    (hG : Xh0 + leOe Eh + Om 1 < ujY S 0) (hEo : UjOwn S l b X0 E Eh)
    (hup : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → ∀ y, y ∈ cdHull S l →
      X0 + y ∈ S.CSet (β + leWe (X0 + y + 1)) (S.psi (β + leWe (X0 + y + 1)) (Om (1 + 1))) → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β → ∀ z,
      UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) z → z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    RvTop S l b (X0 + leWe E) (Xh0 + leOe Eh) 0 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  -- a member `X₀ + W^e` relative to the base `β`
  have hm : ∀ β, b ≤ β → ∀ e eh (Owe : Ordinal.{0} → Ordinal.{0} → Prop), UjOwP S l Owe e eh →
      UjLev S l Owe e eh → Owe β X0 → e < E → eh < Eh →
      UjSh S l β (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) ∧
      RvTop S l β (X0 + leWe e * 1) (Xh0 + leOe eh * gxTh (upsilon l) (ldAtR S l) 1) 0 := by
    intro β hbβ e eh Owe hPk hLk hOk hek hehk
    have hE1 : e + 1 ≤ E := Order.add_one_le_of_lt hek
    have hdE : leWe (e + 1) ∣ X0 := (leWe_dvd hE1).trans hd
    have hG3' : X0 + leWe (e + 1) + Om (1 + 1) < ugY S :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hE1)) _) hG3
    have hG' : Xh0 + leOe (eh + 1) + Om 1 < ujY S 0 :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2
        (leOe_mono (Order.add_one_le_of_lt hehk))) _) hG
    have h := ujFam hl hX hPk hLk (ujOff_mono hbβ hoff) hdE hG3' hG' hOk 1
      (GxCl.small (gg_one_lt_of_SC hρSC)) ⟨0, show (1 : Ordinal.{0}) < Om 1 from sqOne_lt_Om1⟩
      (by rw [hΘ1]; exact sqOne_lt_Om1)
    refine ujOff_ne h fun h' => (leWe_pos e).ne' ?_
    have := le_antisymm (h' ▸ le_add_self : leWe e * 1 ≤ 0) zero_le
    rwa [mul_one] at this
  -- the shift `X₀ + W^E`
  have hs : UjSh S l b (X0 + leWe E) (Xh0 + leOe Eh) := ujSh_own hoff hEo hG3 hG
  -- the image `Θ(T)` is strongly critical and a member exists at every base
  have hTSC : ∀ β, RoBaseE S l (X0 + leWe E) 0 β →
      SC (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) := by
    intro β hb
    obtain ⟨-, hβH, hβA, -, -⟩ := hb
    rw [add_zero] at hβA
    exact (ldAtom_ge hρSC hρ1 hAt ⟨β + leWe (X0 + leWe E), CSet.add_mem hβH (leWe_mem hs.hull), hβA, rfl⟩).1
  have hany : ∀ β, b ≤ β → RoBaseE S l (X0 + leWe E) 0 β →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh := by
    intro β hbβ hb
    obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -⟩ := hlo β hbβ hb 0 (UgC.zero (hTSC β hb).1) (leOe_pos _)
    exact ⟨e, eh, Owe, a1, a2, a3, a4, a5⟩
  refine umTopLimC hl hX hs ?_ ?_
  · intro β Â hb hbβ hÂ hbase x hxH hxC hx
    obtain ⟨e, eh, Owe, hPk, hLk, hOk, hek, hehk, hyx⟩ : ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop,
        UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧ e < E ∧ eh < Eh ∧ x < X0 + leWe e := by
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
        UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧ e < E ∧ eh < Eh ∧ z < Xh0 + leOe eh := by
      rcases lt_or_ge z Xh0 with h | h
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5⟩ := hany β hbβ hb
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        have hXh0c : UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) Xh0 := by
          obtain ⟨-, -, -, -, -, hcl⟩ := ujOff_data hoff
          refine hcl _ (hTSC β hb) (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) ?_).1)
          exact add_le_add hbβ (leWe_mono le_self_add)
        have hyc : UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) y := by
          have h1 := (ugCDec (hTSC β hb) one_ne_zero _ hzc).1 _ hXh0c le_self_add
          rwa [Ordinal.add_sub_cancel] at h1
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, a6⟩ :=
          hlo β hbβ hb y hyc ((add_lt_add_iff_left Xh0).1 hz)
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, (add_lt_add_iff_left Xh0).2 a6⟩
    obtain ⟨hsk, htk⟩ := hm β hbβ e eh Owe hPk hLk hOk hek hehk
    refine ⟨_, _, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_lt_add_iff_left X0).2 (leWe_lt hek)
    · rw [hΘ1, mul_one]; exact hzk

/-- **THE LEVEL STATEMENT PAST `Γ₂` FROM CODE-RESTRICTED MEMBERS** (the members are needed only at the bases). -/
theorem umLevLimC {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : UjOwP S l Ow E Eh)
    (hup : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < ugY S →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ y, y ∈ cdHull S l →
      X0 + y ∈ S.CSet (β + leWe (X0 + y + 1)) (S.psi (β + leWe (X0 + y + 1)) (Om (1 + 1))) → y < leWe E →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ y < leWe e)
    (hlo : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < ugY S →
      RoBaseE S l (X0 + leWe E) 0 β → Ow β X0 → ∀ z,
      UgC S 1 (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) z → z < leOe Eh →
      ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧ Owe β X0 ∧
        e < E ∧ eh < Eh ∧ z < leOe eh) :
    UjLev S l Ow E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw
  exact umTopLimCoreC hl hX hoff hd hG3 hG (hP.dat b X0 hOw)
    (fun β hbβ hb => hup β X0 Xh0 (ujOff_mono hbβ hoff) hd hG3 hb (hP.mono b β X0 X0 hOw hbβ le_rfl))
    (fun β hbβ hb => hlo β X0 Xh0 (ujOff_mono hbβ hoff) hd hG3 hb (hP.mono b β X0 X0 hOw hbβ le_rfl))


/-- **THE GENERIC LIMIT STEP PAST `Γ₂`.** -/
theorem umLevLimM {E Eh : Ordinal.{0}} {M Mh : Ordinal.{0} → Ordinal.{0}} (hM : Monotone M) (hMh : Monotone Mh)
    (hP : UjOwP S l (SnCL S E) E Eh) (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hcof : ∀ Q, SC Q → Om 1 < Q → ∀ w, LeCl (Om (1 + 1)) Q w → w < E → ∃ c', c' < Q ∧ w < M c')
    (hcofh : ∀ Q, SC Q → ∀ w, LeCl (Om 1) Q w → w < Eh → ∃ c', c' < Q ∧ w < Mh c')
    (hmem : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      UjOwP S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧
      UjLev S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧
      M c < E ∧ Mh (gxTh (upsilon l) (ldAtR S l) c) < Eh)
    (hcl : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < ugY S →
      RoBaseE S l (X0 + leWe E) 0 β → SnCL S E β X0 → ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c →
      c < Om (1 + 1) → c < S.psi (β + leWe (X0 + leWe (M c))) (Om (1 + 1)) → SnCL S (M c) β X0) :
    UjLev S l (SnCL S E) E Eh := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  -- a member at every code `1 ≤ c < T_E` of `λ`
  have hmemb : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → leWe E ∣ X0 →
      X0 + leWe E + Om (1 + 1) < ugY S → RoBaseE S l (X0 + leWe E) 0 β → SnCL S E β X0 →
      ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) →
      UjOwP S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧
      UjLev S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧ SnCL S (M c) β X0 ∧
      M c < E ∧ Mh (gxTh (upsilon l) (ldAtR S l) c) < Eh := by
    intro β X0 Xh0 hoff hd hG3 hb hOw c hc hc1 hcT
    have hcW : c < Om (1 + 1) := hcT.trans (psi_lt (InR_Om_succ 1) _)
    obtain ⟨h1, h2, h3, h4⟩ := hmem c hc hc1 hcW
    exact ⟨h1, h2, hcl β X0 Xh0 hoff hd hG3 hb hOw c hc hc1 hcW (tnOwnLevM hl hX hM hEG hcof hc hcT), h3, h4⟩
  refine umLevLimC hl hX hP ?_ ?_
  · intro β X0 Xh0 hoff hd hG3 hb hOw y hyH hyC hy
    have hb' := hb
    obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
    rw [add_zero] at hβd hβA hβown
    obtain ⟨-, hX0H, hX0m, -, -, -⟩ := ujOff_data hoff
    set a := X0 + y + 1 with ha_def
    have hE0 : E ≠ 0 := (zero_lt_one.trans_le (hP.dat β X0 hOw).one).ne'
    have hEW : IsSuccLimit (leWe E) := Ph.ph_opow_lim (mul_ne_zero ldOm2_SC.1.ne' hE0)
    have hyG : y + 1 < leWe E := hEW.add_one_lt hy
    have ha_lt : a < X0 + leWe E := by
      rw [ha_def, add_assoc]; exact (add_lt_add_iff_left X0).2 hyG
    have hyC' : y ∈ S.CSet (β + leWe a) (S.psi (β + leWe a) (Om (1 + 1))) := by
      have h1 := taSub_mem (S := S) _ hyC X0
      rwa [Ordinal.add_sub_cancel] at h1
    have hargH : β + leWe a ∈ cdHull S l :=
      CSet.add_mem hβH (leWe_mem (CSet.succ_mem (CSet.add_mem hX0H hyH)))
    have hle : β + leWe a ≤ β + leWe (X0 + leWe E) := (add_le_add_iff_left β).2 (leWe_mono ha_lt.le)
    have hs'at : S.psi (β + leWe a) (Om (1 + 1)) ∈ ldAtR S l := ⟨_, hargH, hle.trans_lt hβA, rfl⟩
    have hmemC : β + leWe a ∈ S.CSet (β + leWe (X0 + leWe E)) (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) := by
      have hX0' : X0 ∈ S.CSet (β + leWe (X0 + leWe E)) (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) :=
        CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono (le_self_add : X0 ≤ X0 + leWe E)))).1 hX0m
      have hy' := (psi_mono (S := S) (InR_Om_succ 1) hle).2 hyC'
      exact CSet.add_mem (hβown _ le_rfl) (leWe_mem (CSet.succ_mem (CSet.add_mem hX0' hy')))
    have hs'T : S.psi (β + leWe a) (Om (1 + 1)) < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) :=
      psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leWe_lt ha_lt)) hmemC
    have hs'1 : 1 ≤ S.psi (β + leWe a) (Om (1 + 1)) := (gg_one_lt_of_SC (SC_psi (InR_Om_succ 1) _)).le
    obtain ⟨hPk, hLk, hOk, hek, hehk⟩ :=
      hmemb β X0 Xh0 hoff hd hG3 hb' hOw _ (GxCl.atom hs'at) hs'1 hs'T
    refine ⟨_, _, _, hPk, hLk, hOk, hek, hehk, ?_⟩
    rcases eq_or_ne y 0 with rfl | hy0
    · exact leWe_pos _
    set w := log ω y / Om (1 + 1) with hw
    have hwE : w < E := tnLogW_lt hy0 hy
    have hwC : w ∈ S.CSet (β + leWe a) (S.psi (β + leWe a) (Om (1 + 1))) := ldDivK_mem ldOm2_SC (leLog_mem hyC')
    have hsSC : SC (S.psi (β + leWe a) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
    have hwc : LeCl (Om (1 + 1)) (S.psi (β + leWe a) (Om (1 + 1))) w :=
      snLeCl_mem hsSC le_rfl hwC (hwE.trans hEG)
    obtain ⟨c', hc's, hwc'⟩ := hcof _ hsSC (psiS_bounds (S := S) _ 1).1 w hwc hwE
    exact (roLt_We_log y).trans_le (leWe_mono (Order.add_one_le_of_lt (hwc'.trans_le (hM hc's.le))))
  · intro β X0 Xh0 hoff hd hG3 hb hOw z hzc hz
    have hb' := hb
    obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
    rw [add_zero] at hβd hβA hβown
    obtain ⟨-, hX0H, -, -, -, -⟩ := ujOff_data hoff
    have hTat : leTe S (X0 + leWe E) β ∈ ldAtR S l :=
      ⟨_, CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leWe_mem (hP.dat β X0 hOw).hull))), hβA, rfl⟩
    have hTSC := (ldAtom_ge hρSC hρ1 hAt hTat).1
    have hTlim : IsSuccLimit (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) := (SC_psi (InR_Om_succ 1) _).isSuccLimit
    have hpre : ∀ ζh, ζh < gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β) →
        ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ 1 ≤ c ∧ c < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ∧
          ζh ≤ gxTh (upsilon l) (ldAtR S l) c := by
      intro ζh hζh
      obtain ⟨c, hc, hcm, hΘc⟩ := gxTh_onto hζh
      refine ⟨c + 1, GxCl.add hc (GxCl.small (gg_one_lt_of_SC hρSC)), le_add_self, hTlim.add_one_lt hcm, ?_⟩
      rw [← hΘc]; exact gxTh_mono le_self_add
    obtain ⟨ζh, hζhT, hzζ⟩ : ∃ ζh, ζh < gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β) ∧
        z < leOe (Mh ζh) := by
      rcases eq_or_ne z 0 with rfl | hz0
      · exact ⟨0, hTSC.1, leOe_pos _⟩
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      set w := log ω z / Om 1 with hw
      have hwG : w < Eh := by
        have hlog : log ω z < Om 1 * Eh :=
          (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hz0).trans_lt hz)
        exact (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlog
      have hwc : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E) β)) w :=
        umC1_toLe (ugC_div hTSC one_ne_zero _ (ugCDec hTSC one_ne_zero z hzc).2) (hwG.trans hEhG)
      obtain ⟨ζh, hζh, hwζ⟩ := hcofh _ hTSC w hwc hwG
      exact ⟨ζh, hζh, (roLt_Oe_log z).trans_le (leOe_mono (Order.add_one_le_of_lt hwζ))⟩
    obtain ⟨c, hc, hc1, hcT, hζc⟩ := hpre ζh hζhT
    obtain ⟨hPk, hLk, hOk, hek, hehk⟩ := hmemb β X0 Xh0 hoff hd hG3 hb' hOw c hc hc1 hcT
    exact ⟨_, _, _, hPk, hLk, hOk, hek, hehk, hzζ.trans_le (leOe_mono (hMh hζc))⟩


end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
