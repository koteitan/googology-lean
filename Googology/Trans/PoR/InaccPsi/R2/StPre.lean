import Googology.Trans.PoR.InaccPsi.R2.StLim

/-!
# Levels over a prefix: `P + c` for every code `c < Ω₂`, and the next prefix `P + Ω₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`,
`CL E = Sn.SnCL S E` (the closure condition), `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

**The image condition** `StImg S λ P P̂`: whenever `P` is a code over every strongly critical `Q ≥ T`, `P̂ ∈ Cl(0, Θ T)`
and `P̂` is a level-1 code over every strongly critical `Q ≥ Θ T`.  **A prefix** `StPD S λ P P̂`: `Ω₂ ∣ P`, `P` in
the hull, `1 ≤ P < G3`, `P̂ < G1`, the image condition and the level statement `Sc.ScLev (CL P) P P̂`.
`ε = ε_{Ω₂+1}` with `ε̂ = ε_{Ω₁+1}` is a prefix (`St.stPD_eps`, in `StLad`).

* `stCodeHead`, `stCodeHeadW` (a code `P + c`, `c < Ω₂`, or `P + Ω₂` with `Ω₂ ∣ P` gives the codes `P` and `c`);
* `stOwP_img` (**the image condition gives the own data** `Sc.ScOwP (CL P) P P̂`), `stImg_add`;
* `stPreDown` (**at a base, `CL (P + c)` gives `CL (P + c')` for every `c' ≤ c`**, by the collapse `St.stCollD`);
* `stPreLev` (**THE LEVELS OVER A PREFIX: `Sc.ScLev (CL (P + c)) (P + c) (P̂ + Θ c)` for every code `c < Ω₂`**:
  successors by `Sc.scLev_succ` and the upgrade `St.stLevUp`, limits by the hull-limit rule at the bases
  `St.stLevLimB`, the members `P + c'` own at the base by `stPreDown`);
* `stPreW` (**THE NEXT PREFIX: `P + Ω₂` with the image `P̂ + Ω₁` is a prefix**: `Sc.scLev_om` with the shape
  `ζ ↦ P + ζ` (`Sc.scShp_pre` of `Sc.scShp_code`), the members from `stPreLev`, then the upgrade).

No new axiom.  New definitions: `StImg`, `StPD`.
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

/-- **The image condition** of a level `P` with the image `P̂`. -/
def StImg (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop :=
  ∀ T, SC T → (∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P) →
    Ph ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) ∧
      ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → LeCl (Om 1) Q Ph

/-- **A prefix**: a level `P` divisible by `Ω₂` with its image, the image condition and the level statement. -/
structure StPD (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop where
  dvd : Om (1 + 1) ∣ P
  hull : P ∈ cdHull S l
  one : 1 ≤ P
  ltG3 : P < S.psi 0 (Om (1 + 1 + 1))
  ltG : Ph < S.psi 0 (Om (1 + 1))
  img : StImg S l P Ph
  lev : ScLev S l (SnCL S P) P Ph

/-- `ω^{Ω₂} = Ω₂`. -/
theorem stW_opow : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC ldOm2_SC

/-- **A code `P + c`** (`Ω₂ ∣ P`, `c < Ω₂`) **gives the codes `P` and `c`.** -/
theorem stCodeHead {Q P c : Ordinal.{0}} (hQ : SC Q) (hd : Om (1 + 1) ∣ P) (hc : c < Om (1 + 1))
    (h : LeCl (Om (1 + 1)) Q (P + c)) : LeCl (Om (1 + 1)) Q P ∧ LeCl (Om (1 + 1)) Q c := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd
  have e1 : (Om (1 + 1) * q + c) / Om (1 + 1) = q := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hc, add_zero]
  have h1 := sjCl_div hQ ldOm2_SC _ h
  rw [e1] at h1
  refine ⟨LeCl.mulK hQ ldOm2_SC _ h1, ?_⟩
  have h2 := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1)) h
  rwa [stW_opow, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc] at h2

/-- **A code `P + Ω₂`** (`Ω₂ ∣ P`) **gives the code `P`.** -/
theorem stCodeHeadW {Q P : Ordinal.{0}} (hQ : SC Q) (hd : Om (1 + 1) ∣ P)
    (h : LeCl (Om (1 + 1)) Q (P + Om (1 + 1))) : LeCl (Om (1 + 1)) Q P := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd
  have e1 : (Om (1 + 1) * q + Om (1 + 1)) / Om (1 + 1) = q + 1 := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_self hW0]
  have h1 := sjCl_div hQ ldOm2_SC _ h
  rw [e1] at h1
  exact LeCl.mulK hQ ldOm2_SC _ (snPred hQ ldOm2_SC q h1)

/-- **At a base, `CL (P + c)` gives `CL (P + c')` for every `c' ≤ c`.** -/
theorem stPreDown {l β X0 Xh0 P c c' : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + c) < S.psi 0 (Om (1 + 1 + 1))) (hb : RoBaseE S l (X0 + leWe (P + c)) 0 β)
    (hd : Om (1 + 1) ∣ P) (hcW : c < Om (1 + 1)) (hcl : SnCL S (P + c) β X0) (hc' : c' ≤ c) :
    SnCL S (P + c') β X0 := by
  obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl ((add_le_add_iff_left P).2 hc')
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

omit hl hX in
/-- **The image condition gives the own data.** -/
theorem stOwP_img {P Ph : Ordinal.{0}} (himg : StImg S l P Ph) (hPH : P ∈ cdHull S l) (hP1 : 1 ≤ P) :
    ScOwP S l (SnCL S P) P Ph := by
  refine ⟨fun b X0 hcl => ?_, fun _ _ _ _ h hb hX0 => snCL_mono h hb hX0⟩
  have hT : SC (S.psi (b + leWe (X0 + leWe P)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  obtain ⟨h1, h2⟩ := himg _ hT hcl
  exact ⟨hP1, hPH, sjCl_mem (hcl _ hT le_rfl), h1, hcl, h2⟩

/-- The image condition of `P + c`, `c < Ω₂` a code. -/
theorem stImg_add {P Ph c : Ordinal.{0}} (himg : StImg S l P Ph) (hd : Om (1 + 1) ∣ P)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcW : c < Om (1 + 1)) :
    StImg S l (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) := by
  intro T hT hcl
  have hP : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
    (stCodeHead hQ hd hcW (hcl Q hQ hTQ)).1
  have hcT : c < T := LeCl.lt_of_lt hT (stCodeHead hT hd hcW (hcl T hT le_rfl)).2 hcW
  have hΘ := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
  obtain ⟨h1, h2⟩ := himg T hT hP
  exact ⟨CSet.add_mem h1 (CSet.of_lt hΘ), fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) (LeCl.small (hΘ.trans_le hΘQ))⟩

/-- The own data of `P + c`. -/
theorem stPreOwP {P Ph c : Ordinal.{0}} (hD : StPD S l P Ph) (hc : GxCl (upsilon l) (ldAtR S l) c)
    (hcW : c < Om (1 + 1)) :
    ScOwP S l (SnCL S (P + c)) (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) :=
  stOwP_img (stImg_add hl hX hD.img hD.dvd hc hcW) (CSet.add_mem hD.hull ((ldHull_iff hl hX hcW).2 hc))
    (hD.one.trans le_self_add)

/-- **THE LEVELS OVER A PREFIX.** -/
theorem stPreLev {P Ph : Ordinal.{0}} (hD : StPD S l P Ph) : ∀ c, GxCl (upsilon l) (ldAtR S l) c →
    c < Om (1 + 1) → ScLev S l (SnCL S (P + c)) (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hG3S := rwG3_SC (S := S)
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
    have hS := scLev_succ hl hX (stPreOwP hl hX hD hc0c hc0W) IH0 (fun _ _ h => h)
    have e1 : P + (c0 + 1) = P + c0 + 1 := (add_assoc _ _ _).symm
    have e2 : Ph + gxTh (upsilon l) (ldAtR S l) (c0 + 1) = Ph + gxTh (upsilon l) (ldAtR S l) c0 + 1 := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, add_assoc]
    have hS' : ScLev S l (SnCL S (P + c0)) (P + (c0 + 1)) (Ph + gxTh (upsilon l) (ldAtR S l) c0 + 1) := by
      rw [e1]; exact hS
    rw [e2]
    refine stLevUp hS' (fun b β X0 h hb => snCL_mono h hb le_rfl) ?_
    intro β X0 Xh0 hoff _ hG3 hb h
    exact stPreDown hoff (le_self_add.trans_lt hG3) hb hD.dvd hcW h le_self_add
  · have hP := stPreOwP hl hX hD hc hcW
    have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have hEG : P + c < S.psi 0 (Om (1 + 1 + 1)) := hG3S.isPrincipal hD.ltG3 (hcW.trans rwW_lt_G3)
    have hEhG : Ph + gxTh (upsilon l) (ldAtR S l) c < S.psi 0 (Om (1 + 1)) :=
      rwG_SC.isPrincipal hD.ltG ((snTh_lt_Om1 hl hX hcW.le).trans rwO_lt_G)
    -- the members `P + c'` own at a base
    have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → X0 + leWe (P + c) < S.psi 0 (Om (1 + 1 + 1)) →
        RoBaseE S l (X0 + leWe (P + c)) 0 β → SnCL S (P + c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → c' < c →
        ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧
          Owe β X0 ∧ e < P + c ∧ eh < Ph + gxTh (upsilon l) (ldAtR S l) c ∧
          e = P + c' ∧ eh = Ph + gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'c
      have hc'W := hc'c.trans hcW
      exact ⟨_, _, SnCL S (P + c'), stPreOwP hl hX hD hc' hc'W, IH c' hc'c hc' hc'W,
        stPreDown hoff hG3 hb hD.dvd hcW hcl hc'c.le, (add_lt_add_iff_left _).2 hc'c,
        (add_lt_add_iff_left _).2 (gxTh_lt hc' hc'c), rfl, rfl⟩
    refine stLevLimB hl hX hP hEG hEhG ?_ ?_
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
          obtain ⟨q, hq⟩ := hD.dvd
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

/-- **THE NEXT PREFIX: `P + Ω₂` with the image `P̂ + Ω₁`.** -/
theorem stPreW {P Ph : Ordinal.{0}} (hD : StPD S l P Ph) : StPD S l (P + Om (1 + 1)) (Ph + Om 1) := by
  have hG3S := rwG3_SC (S := S)
  -- the image condition
  have himg : StImg S l (P + Om (1 + 1)) (Ph + Om 1) := by
    intro T hT hcl
    obtain ⟨h1, h2⟩ := hD.img T hT fun Q hQ hTQ => stCodeHeadW hQ hD.dvd (hcl Q hQ hTQ)
    exact ⟨CSet.add_mem h1 (CSet.Om_mem (CSet.one_mem _ _)), fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) LeCl.om⟩
  refine ⟨dvd_add hD.dvd dvd_rfl, CSet.add_mem hD.hull (mxOm2_mem _ _), hD.one.trans le_self_add,
    hG3S.isPrincipal hD.ltG3 rwW_lt_G3, rwG_SC.isPrincipal hD.ltG rwO_lt_G, himg, ?_⟩
  -- the level statement with the own predicate `P own above T_{P+1}`
  set Ow : Ordinal.{0} → Ordinal.{0} → Prop := fun b X0 =>
    ∀ Q, SC Q → leTe S (X0 + leWe (P + 1)) b ≤ Q → LeCl (Om (1 + 1)) Q P with hOw_def
  have hmono : ∀ b β X0, Ow b X0 → b ≤ β → Ow β X0 := by
    intro b β X0 hOw hbβ Q hQ hQ'
    refine hOw Q hQ (le_trans ?_ hQ')
    unfold leTe
    exact (psi_mono (S := S) (InR_Om_succ 1) (add_le_add hbβ le_rfl)).1
  have hL0 : ScLev S l Ow (P + Om (1 + 1)) (Ph + Om 1) := by
    refine scLev_om hl hX (g := fun z => P + z) (gh := fun v => Ph + v) ?_ hmono ?_
    · intro b X0 hOw
      have hT : SC (leTe S (X0 + leWe (P + 1)) b) := leTe_SC _ _
      obtain ⟨h1, h2⟩ := hD.img _ hT hOw
      exact scShp_pre hl hX (scShp_code hl hX _ _) hD.hull (sjCl_mem (hOw _ hT le_rfl)) h1 hOw h2
        (k := Om (1 + 1)) stW_opow.symm hD.dvd
    · intro ζ hζ h1 hζW
      have hL := stPreLev hl hX hD ζ hζ hζW
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
  refine stLevUp hL0 (fun b β X0 h hb => snCL_mono h hb le_rfl) ?_
  intro β X0 Xh0 hoff _ hG3 hb hcl Q hQ hQ'
  have hy : P + 1 ≤ P + Om (1 + 1) := (add_le_add_iff_left P).2 (gg_one_lt_of_SC ldOm2_SC).le
  obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff (le_self_add.trans_lt hG3) hb hcl hy
  have hzQ := hz Q hQ (by unfold leTe at hQ'; exact hQ')
  obtain ⟨w, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hwW : w ≤ Om (1 + 1) := (add_le_add_iff_left P).1 hz2
  rcases hwW.lt_or_eq with hlt | rfl
  · exact (stCodeHead hQ hD.dvd hlt hzQ).1
  · exact stCodeHeadW hQ hD.dvd hzQ

end Main

end Googology.Trans.PoR.InaccPsi.R2.St
