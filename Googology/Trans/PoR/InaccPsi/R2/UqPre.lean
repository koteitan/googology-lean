import Googology.Trans.PoR.InaccPsi.R2.UqGen

/-!
# Levels over a prefix past `Γ₂` with the bound `Y₃`: `P + c` for every code `c < Ω₂`, and the prefix `P + Ω₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β, X₀) = ψ_{Ω₂}(β + W^{X₀ + W^E})`,
`C_k(Q) = Ug.UgC S k Q`, `CL₃ E = Ug.UgCL S E`, `Y₃ = ψ_{Ω₃}(Ω₃)`; prefixes past `Γ₂` `Uq.UqPD`.

`Um.umPreDown`, `Um.umPreLev`, `Um.umPreW` for the prefixes `Uq.UqPD` (bound `Y₃`, no `Sc` field): the collapse
`Um.umCollD` with the closure condition `CL₃`, the head lemmas `Uq.uqHead`, `Uq.uqHeadW`, the own data from the image
condition `Uq.uqOwP_img`, the hull-limit rule `Um.umLevLimB`, the upgrade `Um.umLevUp`, the successor step
`Uj.ujLev_succ`; the next prefix by the generic limit step `Uq.uqLevLimM` (members `P + c`, images `P̂ + Θ c`).

* `uqPreDown` (**at a base past `Γ₂`, `CL₃ (P + c)` gives `CL₃ (P + c')` for every `c' ≤ c`**);
* `uqPreLev` (**THE LEVELS OVER A PREFIX PAST `Γ₂`: `UjLev (CL₃ (P + c)) (P + c) (P̂ + Θ c)` for every code `c < Ω₂`**);
* `uqCofW`, `uqCofO` (the cofinality conditions of `P + Ω₂`, `P̂ + Ω₁` for the members `P + c`, `P̂ + v`);
* `uqPreW` (**THE NEXT PREFIX PAST `Γ₂`: `P + Ω₂` with the image `P̂ + Ω₁`**, `Ω₁ ∣ P̂`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj
  Googology.Trans.PoR.InaccPsi.R2.Um

variable {S : InaccSeq.{0}}

/-- **At a base past `Γ₂`, `CL₃ (P + c)` gives `CL₃ (P + c')` for every `c' ≤ c`.** -/
theorem uqPreDown {l β X0 Xh0 P c c' : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + c) < ugY S) (hb : RoBaseE S l (X0 + leWe (P + c)) 0 β)
    (hd : Om (1 + 1) ∣ P) (hcW : c < Om (1 + 1)) (hcl : UgCL S (P + c) β X0) (hc' : c' ≤ c) :
    UgCL S (P + c') β X0 := by
  obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoff hG3 hb hcl ((add_le_add_iff_left P).2 hc')
  obtain ⟨w, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hwc : w ≤ c := (add_le_add_iff_left P).1 hz2
  have hwW : w < Om (1 + 1) := hwc.trans_lt hcW
  have hc'w : c' ≤ w := (add_le_add_iff_left P).1 hz1
  intro Q hQ hQ'
  obtain ⟨hPQ, -, hwQ⟩ := uqHead hQ hd hwW (hz Q hQ hQ')
  exact UgC.add hPQ (UgC.small (hc'w.trans_lt hwQ))

/-- `P + c < Y₃` for `P < Y₃`, `c < Ω₂`. -/
theorem uqAdd_ltY {P c : Ordinal.{0}} (hP : P < ugY S) (hc : c ≤ Om (1 + 1)) : P + c < ugY S :=
  uqY_SC.isPrincipal hP (hc.trans_lt uqW_lt_Y)

/-- **The cofinality condition of `P + Ω₂`** for the members `P + c` (`Ω₂ ∣ P`), at every strongly critical `Q`. -/
theorem uqCofW {P : Ordinal.{0}} (hd : Om (1 + 1) ∣ P) :
    ∀ Q, SC Q → Om 1 < Q → ∀ w, UgC S (1 + 1) Q w → w < P + Om (1 + 1) → ∃ c', c' < Q ∧ w < P + c' := by
  intro Q hQ _ w hw hwE
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hu := ugC_mod hQ ugTwo_ne (Om (1 + 1)) hw
  rw [stW_opow] at hu
  have huW : w % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt _ hW0
  have huQ := ugC_lt_om hQ hu huW
  refine ⟨w % Om (1 + 1) + 1, hQ.isSuccLimit.add_one_lt huQ, ?_⟩
  obtain ⟨q, hq⟩ := hd
  have hdiv : w / Om (1 + 1) ≤ q := by
    have : w < Om (1 + 1) * (q + 1) := by rw [mul_add_one, ← hq]; exact hwE
    exact Order.lt_add_one_iff.1 ((Ordinal.lt_mul_iff_div_lt hW0).1 this)
  calc w = Om (1 + 1) * (w / Om (1 + 1)) + w % Om (1 + 1) := (Ordinal.div_add_mod w _).symm
    _ ≤ Om (1 + 1) * q + w % Om (1 + 1) := add_le_add_left (mul_le_mul_right hdiv _) _
    _ < P + (w % Om (1 + 1) + 1) := by rw [hq]; exact (add_lt_add_iff_left _).2 (lt_add_one _)

/-- **The cofinality condition of `P̂ + Ω₁`** for the members `P̂ + v` (`Ω₁ ∣ P̂`), at every strongly critical `Q`. -/
theorem uqCofO {Ph : Ordinal.{0}} (hd : Om 1 ∣ Ph) :
    ∀ Q, SC Q → ∀ w, UgC S 1 Q w → w < Ph + Om 1 → ∃ c', c' < Q ∧ w < Ph + c' := by
  intro Q hQ w hw hwE
  have hO0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hu := ugC_mod hQ one_ne_zero (Om 1) hw
  rw [Low.opow_eq_self_of_SC (SC_Om one_ne_zero)] at hu
  have huW : w % Om 1 < Om 1 := Ordinal.mod_lt _ hO0
  have huQ := ugC_lt_om hQ hu huW
  refine ⟨w % Om 1 + 1, hQ.isSuccLimit.add_one_lt huQ, ?_⟩
  obtain ⟨q, hq⟩ := hd
  have hdiv : w / Om 1 ≤ q := by
    have : w < Om 1 * (q + 1) := by rw [mul_add_one, ← hq]; exact hwE
    exact Order.lt_add_one_iff.1 ((Ordinal.lt_mul_iff_div_lt hO0).1 this)
  calc w = Om 1 * (w / Om 1) + w % Om 1 := (Ordinal.div_add_mod w _).symm
    _ ≤ Om 1 * q + w % Om 1 := add_le_add_left (mul_le_mul_right hdiv _) _
    _ < Ph + (w % Om 1 + 1) := by rw [hq]; exact (add_lt_add_iff_left _).2 (lt_add_one _)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LEVELS OVER A PREFIX PAST `Γ₂` WITH THE BOUND `Y₃`.** -/
theorem uqPreLev {P Ph : Ordinal.{0}} (hD : UqPD S l P Ph) : ∀ c, GxCl (upsilon l) (ldAtR S l) c →
    c < Om (1 + 1) → UjLev S l (UgCL S (P + c)) (P + c) (Ph + gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
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
    have hS := ujLev_succ hl hX (uqPreOwP hl hX hD hc0c hc0W) IH0 (fun _ _ h => h)
    have e1 : P + (c0 + 1) = P + c0 + 1 := (add_assoc _ _ _).symm
    have e2 : Ph + gxTh (upsilon l) (ldAtR S l) (c0 + 1) = Ph + gxTh (upsilon l) (ldAtR S l) c0 + 1 := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, add_assoc]
    have hS' : UjLev S l (UgCL S (P + c0)) (P + (c0 + 1)) (Ph + gxTh (upsilon l) (ldAtR S l) c0 + 1) := by
      rw [e1]; exact hS
    rw [e2]
    refine umLevUp hS' (fun b β X0 h hb => ugCL_mono h hb le_rfl) ?_
    intro β X0 Xh0 hoff _ hG3 hb h
    exact uqPreDown hoff (le_self_add.trans_lt hG3) hb hD.dvd hcW h le_self_add
  · have hP := uqPreOwP hl hX hD hc hcW
    have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    -- the members `P + c'` own at a base
    have hmem : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → X0 + leWe (P + c) < ugY S →
        RoBaseE S l (X0 + leWe (P + c)) 0 β → UgCL S (P + c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → c' < c →
        ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e eh ∧ UjLev S l Owe e eh ∧
          Owe β X0 ∧ e < P + c ∧ eh < Ph + gxTh (upsilon l) (ldAtR S l) c ∧
          e = P + c' ∧ eh = Ph + gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'c
      have hc'W := hc'c.trans hcW
      exact ⟨_, _, UgCL S (P + c'), uqPreOwP hl hX hD hc' hc'W, IH c' hc'c hc' hc'W,
        uqPreDown hoff hG3 hb hD.dvd hcW hcl hc'c.le, (add_lt_add_iff_left _).2 hc'c,
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

/-- **THE NEXT PREFIX PAST `Γ₂`: `P + Ω₂` with the image `P̂ + Ω₁`** (`Ω₁ ∣ P̂`). -/
theorem uqPreW {P Ph : Ordinal.{0}} (hD : UqPD S l P Ph) (hdh : Om 1 ∣ Ph) :
    UqPD S l (P + Om (1 + 1)) (Ph + Om 1) := by
  have hYW : P + Om (1 + 1) < ugY S := uqAdd_ltY hD.ltY le_rfl
  have himg := uqImg_W hD.img hD.dvd
  have hPH : P + Om (1 + 1) ∈ cdHull S l := CSet.add_mem hD.hull (mxOm2_mem _ _)
  have hP1 : 1 ≤ P + Om (1 + 1) := hD.one.trans le_self_add
  refine ⟨dvd_add hD.dvd dvd_rfl, hPH, hP1, hYW, himg, ?_⟩
  refine uqLevLimM hl hX (M := fun c => P + c) (Mh := fun v => Ph + v)
    (fun _ _ h => (add_le_add_iff_left _).2 h) (fun _ _ h => (add_le_add_iff_left _).2 h)
    (uqOwP_img hl hX himg hPH hP1) hYW (uqCofW hD.dvd) (uqCofO hdh) ?_ ?_
  · intro c hc _ hcW
    exact ⟨uqPreOwP hl hX hD hc hcW, uqPreLev hl hX hD c hc hcW, (add_lt_add_iff_left _).2 hcW,
      (add_lt_add_iff_left _).2 (snTh_lt_Om1 hl hX hcW.le)⟩
  · intro β X0 Xh0 hoff _ hG3 hb hcl c _ hc1 _ hcT Q hQ hQ'
    have hy : P + 1 ≤ P + Om (1 + 1) := (add_le_add_iff_left P).2 (gg_one_lt_of_SC ldOm2_SC).le
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD hoff (le_self_add.trans_lt hG3) hb hcl hy
    have hTle : S.psi (β + leWe (X0 + leWe (P + 1))) (Om (1 + 1)) ≤ Q :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono ((add_le_add_iff_left X0).2
        (leWe_mono ((add_le_add_iff_left P).2 hc1)))))).1.trans hQ'
    have hzQ := hz Q hQ hTle
    obtain ⟨w, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
    have hwW : w ≤ Om (1 + 1) := (add_le_add_iff_left P).1 hz2
    have hPQ : UgC S (1 + 1) Q P := by
      rcases hwW.lt_or_eq with hlt | rfl
      · exact (uqHead hQ hD.dvd hlt hzQ).1
      · exact uqHeadW hQ hD.dvd hzQ
    exact UgC.add hPQ (UgC.small (hcT.trans_le hQ'))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
