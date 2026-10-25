import Googology.Trans.PoR.InaccPsi.R2.TnOwn

/-!
# The generic limit step: members `M(c)` indexed by the codes `c` below the bottom

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_y(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^y})`,
`CL = Sn.SnCL`, `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

A limit level `E` with image `Ê` and two monotone maps `M`, `M̂` (the members `M(c)` with the images `M̂(Θ c)`):

* (COF) every code `w < E` over a strongly critical `Q > Ω₁` (generator `Ω₂`) is below `M(c)` for some `c < Q`;
* (COF̂) every level-1 code `w < Ê` over a strongly critical `Q` is below `M̂(ĉ)` for some `ĉ < Q`.

* `tnAtom_ltM`, `tnOwnMemM`, `tnOwnLevM` (**THE GENERIC OWN LEMMA**: under (COF), every code `c < T_E(β, X₀)` of
  `λ` has `c < T_{M(c)}(β, X₀)`; no hypothesis on `β`, `X₀`; `Tn.tnOwnLev` is the case `E = φ(Ω₂, 1)`,
  `M(c) = φ(c, Ω₂ + 1)`);
* `tnLevLimM` (**THE GENERIC LIMIT STEP**: (COF), (COF̂), the own data of `E`, and for every code `1 ≤ c < Ω₂` the
  own data and the level statement of `M(c) < E` with the image `M̂(Θ c) < Ê`, the closure condition of `M(c)` at a
  base from `c < T_{M(c)}` ⇒ `Sc.ScLev (CL E) E Ê`; by `Tn.tnLevLimC`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj

variable {S : InaccSeq.{0}}

/-- **The normal-form argument of an atom `ψ_{Ω₂}(d) ≤ c` below `T_E`** is below `β + W^{X₀ + W^{M(c)}}`. -/
theorem tnAtom_ltM {E β X0 c d : Ordinal.{0}} {M : Ordinal.{0} → Ordinal.{0}} (hM : Monotone M)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1)))
    (hcof : ∀ Q, SC Q → Om 1 < Q → ∀ w, LeCl (Om (1 + 1)) Q w → w < E → ∃ c', c' < Q ∧ w < M c')
    (hself : d ∈ S.CSet d (S.psi d (Om (1 + 1)))) (hdc : S.psi d (Om (1 + 1)) ≤ c)
    (hcT : c < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) :
    d < β + leWe (X0 + leWe (M c)) := by
  have hpos : 0 < leWe (M c) := leWe_pos _
  rcases lt_or_ge d β with hdβ | hβd
  · exact hdβ.trans_le le_self_add
  obtain ⟨δ, rfl⟩ := exists_add_of_le hβd
  refine (add_lt_add_iff_left β).2 ?_
  have hδG : δ < leWe (X0 + leWe E) := by
    by_contra h
    push Not at h
    have := (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1
    exact absurd (this.trans hdc) (not_le.2 hcT)
  have hδC : δ ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := by
    have h1 := taSub_mem (S := S) _ hself β
    rwa [Ordinal.add_sub_cancel] at h1
  rcases lt_or_ge δ (leWe X0) with hδX | hδX
  · exact hδX.trans_le (leWe_mono le_self_add)
  have hδ0 : δ ≠ 0 := (lt_of_lt_of_le (leWe_pos X0) hδX).ne'
  set u := log ω δ / Om (1 + 1) with hu
  have hXu : X0 ≤ u := tnLogW_ge hδX
  have huG : u < X0 + leWe E := tnLogW_lt hδ0 hδG
  have huC : u ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := ldDivK_mem ldOm2_SC (leLog_mem hδC)
  obtain ⟨v, hv⟩ := exists_add_of_le hXu
  have hvC : v ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := by
    have h1 := taSub_mem (S := S) _ huC X0
    rwa [hv, Ordinal.add_sub_cancel] at h1
  have hvG : v < leWe E := by
    rw [hv] at huG; exact (add_lt_add_iff_left X0).1 huG
  have hu1 : u + 1 ≤ X0 + leWe (M c) := by
    rw [hv, add_assoc]
    refine (add_le_add_iff_left X0).2 (Order.add_one_le_of_lt ?_)
    rcases eq_or_ne v 0 with rfl | hv0
    · exact hpos
    set w := log ω v / Om (1 + 1) with hw
    have hwE : w < E := tnLogW_lt hv0 hvG
    have hwC : w ∈ S.CSet (β + δ) (S.psi (β + δ) (Om (1 + 1))) := ldDivK_mem ldOm2_SC (leLog_mem hvC)
    have hsSC : SC (S.psi (β + δ) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
    have hwc : LeCl (Om (1 + 1)) (S.psi (β + δ) (Om (1 + 1))) w :=
      snLeCl_mem hsSC le_rfl hwC (hwE.trans hEG)
    obtain ⟨c', hc's, hwc'⟩ := hcof _ hsSC (psiS_bounds (S := S) _ 1).1 w hwc hwE
    have hwφ : w < M c := hwc'.trans_le (hM (hc's.le.trans hdc))
    exact (roLt_We_log v).trans_le (leWe_mono (Order.add_one_le_of_lt hwφ))
  exact (roLt_We_log δ).trans_le (leWe_mono hu1)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The generic own lemma, membership form.** -/
theorem tnOwnMemM {E β X0 c : Ordinal.{0}} {M : Ordinal.{0} → Ordinal.{0}} (hM : Monotone M)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1)))
    (hcof : ∀ Q, SC Q → Om 1 < Q → ∀ w, LeCl (Om (1 + 1)) Q w → w < E → ∃ c', c' < Q ∧ w < M c')
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcT : c < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) :
    c ∈ S.CSet (β + leWe (X0 + leWe (M c))) (S.psi (β + leWe (X0 + leWe (M c))) (Om (1 + 1))) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  set α := β + leWe (X0 + leWe (M c)) with hα
  have key : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x ≤ c → x ∈ S.CSet α (S.psi α (Om (1 + 1))) := by
    intro x hx
    induction hx with
    | small h => exact fun _ => CSet.of_lt (h.trans (hρ1.trans (psiS_bounds (S := S) _ 1).1))
    | om => exact fun _ => CSet.Om_mem (CSet.one_mem _ _)
    | @atom s hs =>
      intro hsc
      obtain ⟨a, haH, haA, rfl⟩ := hs
      obtain ⟨d, -, heq, -, -, hself⟩ := tnNf_atom hl hX haH haA
      rw [← heq] at hsc ⊢
      have hdα : d < α := tnAtom_ltM hM hEG hcof hself hsc hcT
      exact CSet.psi_mem hdα (InR_Om_succ 1) (Mx.mxOm2_mem _ _)
        ((psi_mono (S := S) (InR_Om_succ 1) hdα.le).2 hself)
    | @add x y _ _ ihx ihy =>
      intro h
      exact CSet.add_mem (ihx (le_self_add.trans h)) (ihy (le_add_self.trans h))
    | @phi x y _ _ ihx ihy =>
      intro h
      exact CSet.phi_mem (ihx ((left_le_veblen x y).trans h)) (ihy ((right_le_veblen x y).trans h))
  exact key c hc le_rfl

/-- **THE GENERIC OWN LEMMA**: `c < T_{M(c)}(β, X₀)` for every code `c < T_E(β, X₀)` of `λ`. -/
theorem tnOwnLevM {E β X0 c : Ordinal.{0}} {M : Ordinal.{0} → Ordinal.{0}} (hM : Monotone M)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1)))
    (hcof : ∀ Q, SC Q → Om 1 < Q → ∀ w, LeCl (Om (1 + 1)) Q w → w < E → ∃ c', c' < Q ∧ w < M c')
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcT : c < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))) :
    c < S.psi (β + leWe (X0 + leWe (M c))) (Om (1 + 1)) :=
  lt_psi_of_mem (InR_Om_succ 1) (tnOwnMemM hl hX hM hEG hcof hc hcT) (hcT.trans (psi_lt (InR_Om_succ 1) _))

/-- **THE GENERIC LIMIT STEP.** -/
theorem tnLevLimM {E Eh : Ordinal.{0}} {M Mh : Ordinal.{0} → Ordinal.{0}} (hM : Monotone M) (hMh : Monotone Mh)
    (hP : ScOwP S l (SnCL S E) E Eh) (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    (hcof : ∀ Q, SC Q → Om 1 < Q → ∀ w, LeCl (Om (1 + 1)) Q w → w < E → ∃ c', c' < Q ∧ w < M c')
    (hcofh : ∀ Q, SC Q → ∀ w, LeCl (Om 1) Q w → w < Eh → ∃ c', c' < Q ∧ w < Mh c')
    (hmem : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      ScOwP S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧
      ScLev S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧
      M c < E ∧ Mh (gxTh (upsilon l) (ldAtR S l) c) < Eh)
    (hcl : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 → X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe E) 0 β → SnCL S E β X0 → ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c →
      c < Om (1 + 1) → c < S.psi (β + leWe (X0 + leWe (M c))) (Om (1 + 1)) → SnCL S (M c) β X0) :
    ScLev S l (SnCL S E) E Eh := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  -- a member at every code `1 ≤ c < T_E` of `λ`
  have hmemb : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → leWe E ∣ X0 →
      X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) → RoBaseE S l (X0 + leWe E) 0 β → SnCL S E β X0 →
      ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) →
      ScOwP S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧
      ScLev S l (SnCL S (M c)) (M c) (Mh (gxTh (upsilon l) (ldAtR S l) c)) ∧ SnCL S (M c) β X0 ∧
      M c < E ∧ Mh (gxTh (upsilon l) (ldAtR S l) c) < Eh := by
    intro β X0 Xh0 hoff hd hG3 hb hOw c hc hc1 hcT
    have hcW : c < Om (1 + 1) := hcT.trans (psi_lt (InR_Om_succ 1) _)
    obtain ⟨h1, h2, h3, h4⟩ := hmem c hc hc1 hcW
    exact ⟨h1, h2, hcl β X0 Xh0 hoff hd hG3 hb hOw c hc hc1 hcW (tnOwnLevM hl hX hM hEG hcof hc hcT), h3, h4⟩
  refine tnLevLimC hl hX hP hEG hEhG ?_ ?_
  · intro β X0 Xh0 hoff hd hG3 hb hOw y hyH hyC hy
    have hb' := hb
    obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
    rw [add_zero] at hβd hβA hβown
    obtain ⟨-, hX0H, hX0m, -, -, -⟩ := rvOff_data hoff
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
        CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
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
    obtain ⟨-, hX0H, -, -, -, -⟩ := rvOff_data hoff
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
        sjCl_div hTSC Ph.ph_SC_Om1 _ (leClDec hTSC Ph.ph_SC_Om1 z hzc).2
      obtain ⟨ζh, hζh, hwζ⟩ := hcofh _ hTSC w hwc hwG
      exact ⟨ζh, hζh, (roLt_Oe_log z).trans_le (leOe_mono (Order.add_one_le_of_lt hwζ))⟩
    obtain ⟨c, hc, hc1, hcT, hζc⟩ := hpre ζh hζhT
    obtain ⟨hPk, hLk, hOk, hek, hehk⟩ := hmemb β X0 Xh0 hoff hd hG3 hb' hOw c hc hc1 hcT
    exact ⟨_, _, _, hPk, hLk, hOk, hek, hehk, hzζ.trans_le (leOe_mono (hMh hζc))⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tn
