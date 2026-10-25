import Googology.Trans.PoR.InaccPsi.R2.UmColl

/-!
# Levels over a prefix past `Γ₂`: `P + c` for every code `c < Ω₂`, and the next prefix `P + Ω₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`,
`CL E = Sn.SnCL S E` (the closure condition), `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0) = Γ₂`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

**A prefix past `Γ₂`** (`UmPD S λ P P̂`): a prefix `St.StPD` (`Ω₂ ∣ P`, `P` in the hull, `1 ≤ P < G3`, `P̂ < G1`, the
image condition, `Sc.ScLev (CL P) P P̂`) with the level statement past `Γ₂` `Uj.UjLev (CL P) P P̂`.  `St.stPreDown`,
`St.stPreLev`, `St.stPreW` with the offsets past `Γ₂`, the collapse `Um.umCollD_le`, the hull-limit rule
`Um.umLevLimB`, the upgrade `Um.umLevUp`, the successor step `Uj.ujLev_succ` and the level step `Um.umLev_om`.

* `umPreDown` (**at a base past `Γ₂`, `CL (P + c)` gives `CL (P + c')` for every `c' ≤ c`**);
* `umPreLev` (**THE LEVELS OVER A PREFIX PAST `Γ₂`: `UjLev (CL (P + c)) (P + c) (P̂ + Θ c)` for every code
  `c < Ω₂`**);
* `umPreW` (**THE NEXT PREFIX PAST `Γ₂`: `P + Ω₂` with the image `P̂ + Ω₁` is a prefix past `Γ₂`**).

No new axiom.  New definition: `UmPD`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **A prefix past `Γ₂`**: a prefix of `St` with the level statement past `Γ₂`. -/
structure UmPD (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop where
  sc : StPD S l P Ph
  lev : UjLev S l (SnCL S P) P Ph

/-- **At a base past `Γ₂`, `CL (P + c)` gives `CL (P + c')` for every `c' ≤ c`** (`P + c < Γ₂`). -/
theorem umPreDown {l β X0 Xh0 P c c' : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + c) < ugY S) (hb : RoBaseE S l (X0 + leWe (P + c)) 0 β)
    (hd : Om (1 + 1) ∣ P) (hcW : c < Om (1 + 1)) (hEG : P + c < Ua.uaGam) (hcl : SnCL S (P + c) β X0)
    (hc' : c' ≤ c) :
    SnCL S (P + c') β X0 := by
  obtain ⟨z, hz1, hz2, hz⟩ := umCollD_le hoff hG3 hb hcl hEG ((add_le_add_iff_left P).2 hc')
  obtain ⟨w, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hwc : w ≤ c := (add_le_add_iff_left P).1 hz2
  have hwW : w < Om (1 + 1) := hwc.trans_lt hcW
  have hc'w : c' ≤ w := (add_le_add_iff_left P).1 hz1
  intro Q hQ hQ'
  obtain ⟨hPQ, hwQ⟩ := stCodeHead hQ hd hwW (hz Q hQ hQ')
  exact LeCl.add hPQ (LeCl.small (hc'w.trans_lt (LeCl.lt_of_lt hQ hwQ hwW)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LEVELS OVER A PREFIX PAST `Γ₂`.** -/
theorem umPreLev {P Ph : Ordinal.{0}} (hD : UmPD S l P Ph) : ∀ c, GxCl (upsilon l) (ldAtR S l) c →
    c < Om (1 + 1) → UjLev S l (SnCL S (P + c)) (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hGam : ∀ c, c < Om (1 + 1) → P + c < Ua.uaGam := fun c hcW => by
    rw [Ud.udGam_eq]; exact rwG3_SC.isPrincipal hD.sc.ltG3 (hcW.trans rwW_lt_G3)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcW
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c0, hc0⟩ | hlim
  · subst h0
    rw [add_zero, gxTh_zero, add_zero]
    exact hD.lev
  · rw [succ_eq_add_one] at hc0
    subst hc0
    have hc0c : GxCl (upsilon l) (ldAtR S l) c0 := rqCode_pred hl hX hc hcW
    have hc0W : c0 < Om (1 + 1) := (lt_add_one c0).trans hcW
    have IH0 := IH c0 (lt_add_one c0) hc0c hc0W
    have hS := ujLev_succ hl hX (umOwP_of_sc (stPreOwP hl hX hD.sc hc0c hc0W)) IH0 (fun _ _ h => h)
    have e1 : P + (c0 + 1) = P + c0 + 1 := (add_assoc _ _ _).symm
    have e2 : Ph + gxTh (upsilon l) (ldAtR S l) (c0 + 1) = Ph + gxTh (upsilon l) (ldAtR S l) c0 + 1 := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, add_assoc]
    have hS' : UjLev S l (SnCL S (P + c0)) (P + (c0 + 1)) (Ph + gxTh (upsilon l) (ldAtR S l) c0 + 1) := by
      rw [e1]; exact hS
    rw [e2]
    refine umLevUp hS' (fun b β X0 h hb => snCL_mono h hb le_rfl) ?_
    intro β X0 Xh0 hoff _ hG3 hb h
    exact umPreDown hoff (le_self_add.trans_lt hG3) hb hD.sc.dvd hcW (hGam (c0 + 1) hcW) h le_self_add
  · have hP := umOwP_of_sc (stPreOwP hl hX hD.sc hc hcW)
    have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    -- the members `P + c'` own at a base
    have hmem : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → X0 + leWe (P + c) < ugY S →
        RoBaseE S l (X0 + leWe (P + c)) 0 β → SnCL S (P + c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → c' < c →
        ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧
          Owe β X0 ∧ e < P + c ∧ eh < Ph + gxTh (upsilon l) (ldAtR S l) c ∧
          e = P + c' ∧ eh = Ph + gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'c
      have hc'W := hc'c.trans hcW
      exact ⟨_, _, SnCL S (P + c'), umOwP_of_sc (stPreOwP hl hX hD.sc hc' hc'W), IH c' hc'c hc' hc'W,
        umPreDown hoff hG3 hb hD.sc.dvd hcW (hGam c hcW) hcl hc'c.le, (add_lt_add_iff_left _).2 hc'c,
        (add_lt_add_iff_left _).2 (gxTh_lt hc' hc'c), rfl, rfl⟩
    refine umLevLimB hl hX hP ?_ ?_
    · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
      have hG3' := le_self_add.trans_lt hG3
      rcases lt_or_ge y (leWe P) with hyP | hyP
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1c
        exact ⟨_, eh, Owe, a1, a2, a3, a4, a5, hyP.trans_le (leWe_mono le_self_add)⟩
      · obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
        set Y := log ω y / Om (1 + 1) with hY_def
        have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
        obtain ⟨c'', hc''⟩ := exists_add_of_le hY1
        have hc''c : c'' < c := (add_lt_add_iff_left _).1 (hc'' ▸ hY2)
        have hc''W : c'' < Om (1 + 1) := hc''c.trans hcW
        have hc''H : c'' ∈ cdHull S l := by
          have h := leModP_mem (S := S) (Om (1 + 1)) hYH
          obtain ⟨q, hq⟩ := hD.sc.dvd
          rwa [stW_opow, hc'', hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc''W] at h
        have hc''c' : GxCl (upsilon l) (ldAtR S l) c'' := (ldHull_iff hl hX hc''W).1 hc''H
        have hc1' : c'' + 1 < c := hlim.succ_lt hc''c
        have hcc := rqCode_succ hl hX hc''c' (hc1'.trans hcW)
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc hc1'
        refine ⟨_, eh, Owe, a1, a2, a3, a4, a5, ?_⟩
        have h := roLt_We_log y
        rwa [← hY_def, hc'', add_assoc] at h
    · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
      have hG3' := le_self_add.trans_lt hG3
      set Θc := gxTh (upsilon l) (ldAtR S l) c with hΘc
      have hq : log ω z / Om 1 < Ph + Θc := by
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [log_zero_right, Ordinal.zero_div]
          have h0 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hlim.ne_bot)
          rw [gxTh_zero] at h0
          exact h0.trans_le le_add_self
        · have h := (lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz
          exact (Ordinal.lt_mul_iff_div_lt (Om_pos one_ne_zero).ne').1 h
      have hzq := roLt_Oe_log z
      rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1c
        refine ⟨e, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        exact (Order.add_one_le_of_lt hqP).trans le_self_add
      · obtain ⟨v, hv⟩ := exists_add_of_le hqP
        have hvc : v < Θc := (add_lt_add_iff_left _).1 (hv ▸ hq)
        obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hvc
        have hc1' : c0 + 1 < c := hlim.succ_lt hc0c
        have hcc := rqCode_succ hl hX hc0 (hc1'.trans hcW)
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc hc1'
        refine ⟨e, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        rw [hv, gxTh_add hρSC hAt hc0, hΘ1, e0, add_assoc]

/-- **THE NEXT PREFIX PAST `Γ₂`: `P + Ω₂` with the image `P̂ + Ω₁`.** -/
theorem umPreW {P Ph : Ordinal.{0}} (hD : UmPD S l P Ph) : UmPD S l (P + Om (1 + 1)) (Ph + Om 1) := by
  have hD' := stPreW hl hX hD.sc
  refine ⟨hD', ?_⟩
  -- the level statement with the own predicate `P own above T_{P+1}`
  set Ow : Ordinal.{0} → Ordinal.{0} → Prop := fun b X0 =>
    ∀ Q, SC Q → leTe S (X0 + leWe (P + 1)) b ≤ Q → LeCl (Om (1 + 1)) Q P with hOw_def
  have hmono : ∀ b β X0, Ow b X0 → b ≤ β → Ow β X0 := by
    intro b β X0 hOw hbβ Q hQ hQ'
    refine hOw Q hQ (le_trans ?_ hQ')
    unfold leTe
    exact (psi_mono (S := S) (InR_Om_succ 1) (add_le_add hbβ le_rfl)).1
  have hL0 : UjLev S l Ow (P + Om (1 + 1)) (Ph + Om 1) := by
    refine umLev_om hl hX (g := fun z => P + z) (gh := fun v => Ph + v) ?_ hD'.ltG3 hD'.ltG hmono ?_
    · intro b X0 hOw
      have hT : SC (leTe S (X0 + leWe (P + 1)) b) := leTe_SC _ _
      obtain ⟨h1, h2⟩ := hD.sc.img _ hT hOw
      exact scShp_pre hl hX (scShp_code hl hX _ _) hD.sc.hull (sjCl_mem (hOw _ hT le_rfl)) h1 hOw h2
        (k := Om (1 + 1)) stW_opow.symm hD.sc.dvd
    · intro ζ hζ h1 hζW _
      have hL := umPreLev hl hX hD ζ hζ hζW
      intro b X0 Xh0 hoff hd hG3 hG hO
      obtain ⟨hOw, j, hj⟩ := hO
      refine hL b X0 Xh0 hoff hd hG3 hG ?_
      intro Q hQ hQ'
      have hζT : ζ < S.psi (b + leWe (X0 + leWe (P + ζ))) (Om (1 + 1)) :=
        scSq_gt (G := fun z => leWe (P + z)) (fun a c h => leWe_mono ((add_le_add_iff_left P).2 h)) j ζ hj
      have hTle : leTe S (X0 + leWe (P + 1)) b ≤ S.psi (b + leWe (X0 + leWe (P + ζ))) (Om (1 + 1)) := by
        unfold leTe
        exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono ((add_le_add_iff_left X0).2
          (leWe_mono ((add_le_add_iff_left P).2 h1)))))).1
      exact LeCl.add (hOw Q hQ (hTle.trans hQ')) (LeCl.small (hζT.trans_le hQ'))
  have hEG : P + Om (1 + 1) < Ua.uaGam := by rw [Ud.udGam_eq]; exact hD'.ltG3
  refine umLevUp hL0 (fun b β X0 h hb => snCL_mono h hb le_rfl) ?_
  intro β X0 Xh0 hoff _ hG3 hb hcl Q hQ hQ'
  have hy : P + 1 ≤ P + Om (1 + 1) := (add_le_add_iff_left P).2 (gg_one_lt_of_SC ldOm2_SC).le
  obtain ⟨z, hz1, hz2, hz⟩ := umCollD_le hoff (le_self_add.trans_lt hG3) hb hcl hEG hy
  have hzQ := hz Q hQ (by unfold leTe at hQ'; exact hQ')
  obtain ⟨w, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hwW : w ≤ Om (1 + 1) := (add_le_add_iff_left P).1 hz2
  rcases hwW.lt_or_eq with hlt | rfl
  · exact (stCodeHead hQ hD.sc.dvd hlt hzQ).1
  · exact stCodeHeadW hQ hD.sc.dvd hzQ

end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
