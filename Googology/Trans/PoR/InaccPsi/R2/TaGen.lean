import Googology.Trans.PoR.InaccPsi.R2.TaTw

/-!
# Every own term with Veblen nodes is derived

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `SQ_j(g) = Sc.scSq S (z ↦ W^{g z}) X₀ b j`,
`TaSm a`: `1 ≤ a < Γ₀`.

One induction on the value `v`, inside it on the context and the term, as in `Sw.swGen_all`, with the new cases:
* `K(φ(a, Ω₂ + Q + 1))` (a context ending in a node, at a successor argument): **the family-limit rule**
  `Ta.TaDer.flim` with the members `K(W^{R_i})` of `Ta.taTw_family` (towers `W^·` for `a = 1`, `φ(a', Ω₂ + ·)` for
  `a = a' + 1`, the levels `a' < a` for a limit `a`), the own data from `Ta.taOwP_succ`;
* `K(φ(a, Ω₂ + Y) + 1)` at the hole: the successor;
* `K(W^{φ(a, Ω₂ + Y)}·1)`: the node read as the context `K(W^{φ(a, Ω₂ + ·)})` applied to `Y` (a term statement
  carried along the structural induction).

* `taGen_all` (**THE GENERATION: at every value both parts hold**);
* `taDer_term` (**every well-formed term `t` with `val t ≥ 1` is derived**, own predicate `TaOwn id t`, image
  `taI t`), `taLev_term` (**the level statement `Sc.ScLev` at every such term**).

No new axiom.  New definition: `TaGenAt` (a statement name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

/-- **The generation statement at the value `v`.** -/
def TaGenAt (S : InaccSeq.{0}) (l v : Ordinal.{0}) : Prop :=
  (∀ (K : TaC) (Q : TaT), TaWFC S l K → TaWF S l Q → taE K (taV Q + 1) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (taE K) Q) →
    TaDer S l Ow (taE K (taV Q + 1)) (taEh S l K (taI S l Q + 1))) ∧
  (∀ (K : TaC) (R : TaT) (c : Ordinal.{0}), TaWFC S l K → TaWF S l R → GxCl (upsilon l) (ldAtR S l) c →
    1 ≤ c → c < Om (1 + 1) → taE K (leWe (taV R) * c) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (fun r => taE K (leWe r)) R ∧
      SgLimC S (fun z => taE K (leWe (taV R) * z)) c b X0) →
    TaDer S l Ow (taE K (leWe (taV R) * c)) (taEh S l K (leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c)))

variable {S : InaccSeq.{0}}

section Gen

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- Contexts stay below `ψ_{Ω₃}(0)` and their images below `ψ_{Ω₂}(0)`. -/
theorem taE_lt_G3 : ∀ K : TaC, TaWFC S l K → ∀ y yh, y < S.psi 0 (Om (1 + 1 + 1)) → yh < S.psi 0 (Om (1 + 1)) →
    taE K y < S.psi 0 (Om (1 + 1 + 1)) ∧ taEh S l K yh < S.psi 0 (Om (1 + 1))
  | .hole, _, _, _, h1, h2 => ⟨h1, h2⟩
  | .pfx K Q, ⟨hK, hQ⟩, y, yh, h1, h2 => by
    obtain ⟨a1, a2⟩ := taV_lt_G3 hl hX Q hQ
    exact taE_lt_G3 K hK _ _ (rwG3_SC.isPrincipal a1 h1) (rwG_SC.isPrincipal a2 h2)
  | .lft K, hK, y, yh, h1, h2 =>
    taE_lt_G3 K hK _ _ (leWe_lt_SC rwG3_SC rwW_lt_G3 h1).1 (leOe_lt_SC rwG_SC rwO_lt_G h2).1
  | .phi K a, ⟨hK, ha⟩, y, yh, h1, h2 => by
    have hG3 := rwG3_SC (S := S)
    have hG1 := rwG_SC (S := S)
    exact taE_lt_G3 K hK _ _ (hG3.2 a (taSm_lt_SC ha hG3) _ (hG3.isPrincipal rwW_lt_G3 h1))
      (hG1.2 a (taSm_lt_SC ha hG1) _ (hG1.isPrincipal rwO_lt_G h2))

/-- **THE NODE AT A SUCCESSOR ARGUMENT: `K(φ(a, Ω₂ + Q + 1))` is derived** from its members by the family-limit
rule. -/
theorem taDer_node {v : Ordinal.{0}} (IH : ∀ y, y < v → TaGenAt S l y) (K : TaC) (a : Ordinal.{0}) (Q : TaT)
    (hKw : TaWFC S l K) (ha : TaSm a) (hQw : TaWF S l Q) (hv : taE (TaC.phi K a) (taV Q + 1) = v)
    (Ow : Ordinal.{0} → Ordinal.{0} → Prop) (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')
    (hown : ∀ b X0, Ow b X0 → TaOwnC S b X0 (TaC.phi K a) ∧ TaOwn S b X0 (taE (TaC.phi K a)) Q) :
    TaDer S l Ow (taE (TaC.phi K a) (taV Q + 1)) (taEh S l (TaC.phi K a) (taI S l Q + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  have ha0 := taSm_ne0 ha
  obtain ⟨ι, R, hRw, hRo, hRlt, hRcof, hRhlt, hRhcof⟩ := taTw_family h1ρ ha Q hQw
  set L := veblen a (Om (1 + 1) + (taV Q + 1)) with hL
  set Lh := veblen a (Om 1 + (taI S l Q + 1)) with hLh
  have eE : taE (TaC.phi K a) (taV Q + 1) = taE K L := rfl
  have eEh : taEh S l (TaC.phi K a) (taI S l Q + 1) = taEh S l K Lh := rfl
  have hWL : leWe L = L := taWe_veb ha0 le_add_self
  have hOL : leOe Lh = Lh := taOe_veb ha0 le_add_self
  have hLlim : IsSuccLimit L := taVeb_lim ha0
  have hLhlim : IsSuccLimit Lh := taVeb_lim ha0
  have hmlt : ∀ i, taE K (leWe (taV (R i)) * 1) < taE K L := by
    intro i
    refine taE_strictMono K ?_
    rw [mul_one, ← hWL]; exact leWe_lt (hRlt i)
  have hmhlt : ∀ i, taEh S l K (leOe (taI S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1) < taEh S l K Lh := by
    intro i
    refine taEh_strictMono l K ?_
    rw [hΘ1, mul_one, ← hOL]; exact leOe_lt (hRhlt i)
  have hG3 := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  obtain ⟨hQ3, hQ1⟩ := taV_lt_G3 hl hX Q hQw
  have hb := taE_lt_G3 hl hX (TaC.phi K a) ⟨hKw, ha⟩ _ _ (hG3.add_one_lt hQ3) (hG1.add_one_lt hQ1)
  rw [eE, eEh] at hb ⊢
  refine TaDer.flim (ι := ι) (e := fun i => taE K (leWe (taV (R i)) * 1))
    (eh := fun i => taEh S l K (leOe (taI S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1)) (Ow' := fun _ => Ow)
    (taOwP_succ hl hX (K := TaC.phi K a) ⟨hKw, ha⟩ hQw hmono hown) hb.1 hb.2 (fun i => ?_)
    (fun _ _ _ h => h) hmlt hmhlt ?_ ?_
  · have hlt : taE K (leWe (taV (R i)) * 1) < v := by rw [← hv, eE]; exact hmlt i
    exact (IH _ hlt).2 K (R i) 1 hKw (hRw i) (GxCl.small h1ρ) le_rfl (gg_one_lt_of_SC ldOm2_SC) rfl Ow hmono
      (fun b X0 h => ⟨(hown b X0 h).1, hRo i b X0 (taE K) (taE_mono K) (hown b X0 h).2, sgLimC_one⟩)
  · intro y hy
    have hnorm : Order.IsNormal (fun x => leWe (taE K x)) :=
      ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right ldOm2_SC.1)).comp (taE_normal K)
    obtain ⟨x, hx, hyx⟩ := (hnorm.lt_iff_exists_lt hLlim).1 hy
    obtain ⟨i, hi⟩ := hRcof x hx
    refine ⟨i, hyx.trans (hnorm.strictMono ?_)⟩
    show x < leWe (taV (R i)) * 1
    rw [mul_one]; exact hi.trans_le (taLe_We _)
  · intro z hz
    have hnorm : Order.IsNormal (fun x => leOe (taEh S l K x)) :=
      ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right (Om_pos one_ne_zero))).comp (taEh_normal l K)
    obtain ⟨x, hx, hzx⟩ := (hnorm.lt_iff_exists_lt hLhlim).1 hz
    obtain ⟨i, hi⟩ := hRhcof x hx
    refine ⟨i, hzx.trans (hnorm.strictMono ?_)⟩
    show x < leOe (taI S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1
    rw [hΘ1, mul_one]
    exact hi.trans_le ((Ordinal.le_mul_right _ (Om_pos one_ne_zero)).trans (right_le_opow _ one_lt_omega0))

/-- **THE GENERATION at every value.** -/
theorem taGen_all : ∀ v, TaGenAt S l v := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  -- the first part, by induction on the context
  have hA : ∀ (K : TaC) (Q : TaT), TaWFC S l K → TaWF S l Q → taE K (taV Q + 1) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (taE K) Q) →
      TaDer S l Ow (taE K (taV Q + 1)) (taEh S l K (taI S l Q + 1)) := by
    intro K
    induction K with
    | hole =>
      intro Q hKw hQw hv Ow hmono hown
      cases Q with
      | zero =>
        have h1 : TaDer S l (fun b X0 => ∃ j, (1 : Ordinal.{0}) < rwEX S X0 b j) 1
            (gxTh (upsilon l) (ldAtR S l) 1) :=
          TaDer.code (GxCl.small h1ρ) le_rfl hW1
        refine taDer_cast (TaDer.weaken h1 (fun _ _ _ => ⟨0, gg_one_lt_of_SC Ph.ph_SC_Om1⟩) hmono) ?_ ?_
        · show (1 : Ordinal.{0}) = 0 + 1; rw [zero_add]
        · show gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [zero_add, hΘ1]
      | phi a Y =>
        obtain ⟨ha, hYw, hY1, hYh1⟩ := hQw
        have hlt : taE TaC.hole (leWe (taV (TaT.phi a Y)) * 1) < v := by
          rw [← hv]; show leWe (taV (TaT.phi a Y)) * 1 < taV (TaT.phi a Y) + 1
          rw [taV_node ha hY1]; exact lt_add_one _
        have hD := (IH _ hlt).2 TaC.hole (TaT.phi a Y) 1 trivial ⟨ha, hYw, hY1, hYh1⟩ (GxCl.small h1ρ) le_rfl
          hW1 rfl Ow hmono (fun b X0 h => ⟨trivial, taOwn_mono le_rfl le_rfl Y
            (fun y => veblen a (Om (1 + 1) + y)) (fun y => leWe (veblen a (Om (1 + 1) + y)))
            (taNode_mono _ a) (fun _ _ hxy => leWe_mono (taNode_mono _ a hxy)) (fun y => taLe_We _)
            (hown b X0 h).2, sgLimC_one⟩)
        refine taDer_cast (TaDer.succ hD) ?_ ?_
        · show leWe (taV (TaT.phi a Y)) * 1 + 1 = taV (TaT.phi a Y) + 1; rw [taV_node ha hY1]
        · show leOe (taI S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 + 1 = taI S l (TaT.phi a Y) + 1
          rw [taI_node ha hYh1 h1ρ.le]
      | term P R c =>
        obtain ⟨hPw, hRw, hc, hc1, hcW⟩ := hQw
        have hlt : taV (TaT.term P R c) < v := by rw [← hv]; exact lt_add_one _
        have hD := (IH _ hlt).2 (TaC.pfx TaC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl Ow hmono
          (fun b X0 h => by
            obtain ⟨-, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨trivial, hP⟩, hR, hcl⟩)
        exact TaDer.succ hD
    | pfx K Q' IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have e1 : taV (taCat Q' Q) + 1 = taV Q' + (taV Q + 1) := by rw [taV_cat Q' Q hQw, add_assoc]
      have e2 : taI S l (taCat Q' Q) + 1 = taI S l Q' + (taI S l Q + 1) := by
        rw [taI_cat h1ρ.le Q' Q hQw, add_assoc]
      have hD := IHK (taCat Q' Q) hKw.1 (taWF_cat h1ρ hKw.2 Q hQw) (by rw [e1]; exact hv) Ow hmono
        (fun b X0 h => by
          obtain ⟨⟨hK, hQ'⟩, hQ⟩ := hown b X0 h
          exact ⟨hK, taOwn_cat Q (taE K) (taE_mono K) hQw hQ' hQ⟩)
      exact taDer_cast hD (by rw [e1]; rfl) (by rw [e2]; rfl)
    | lft K IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have hGm : Monotone (fun z => leWe (taE K (leWe (taV Q) * z))) :=
        fun _ _ h => leWe_mono (taE_mono K (leMulWe_mono h))
      refine TaDer.om (g := fun z => taE K (leWe (taV Q) * z))
        (gh := fun v => taEh S l K (leOe (taI S l Q) * v))
        (fun b X0 h => (taShp_path hl hX (K := K) (F := Q) hKw hQw (hown b X0 h).1 (hown b X0 h).2).shp) hmono ?_
      intro ζ hζ h1 hζW
      have hlt : taE K (leWe (taV Q) * ζ) < v := by
        rw [← hv]; exact taE_strictMono K (rvWe_lt_succ hζW)
      exact (IH _ hlt).2 K Q ζ hKw hQw hζ h1 hζW rfl _ (scOwSq_mono hGm hmono ζ)
        (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩)
    | phi K a _ =>
      intro Q hKw hQw hv Ow hmono hown
      exact taDer_node hl hX IH K a Q hKw.1 hKw.2 hQw hv Ow hmono hown
  -- the second part: from `c = 1` to every code `c`
  have hC : ∀ R : TaT, TaWF S l R →
      (∀ K : TaC, TaWFC S l K → taE K (leWe (taV R) * 1) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (fun r => taE K (leWe r)) R) →
        TaDer S l Ow (taE K (leWe (taV R) * 1))
          (taEh S l K (leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) 1))) →
      ∀ (K : TaC) (c : Ordinal.{0}), TaWFC S l K → GxCl (upsilon l) (ldAtR S l) c →
      1 ≤ c → c < Om (1 + 1) → taE K (leWe (taV R) * c) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (fun r => taE K (leWe r)) R ∧
        SgLimC S (fun z => taE K (leWe (taV R) * z)) c b X0) →
      TaDer S l Ow (taE K (leWe (taV R) * c)) (taEh S l K (leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c)) := by
    intro R hRw hB1 K c hKw hc hc1 hcW hv Ow hmono hown
    have hGm : Monotone (fun z => taE K (leWe (taV R) * z)) := fun _ _ h => taE_mono K (leMulWe_mono h)
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨d, hd⟩ | hlim
    · subst h0; exact absurd hc1 (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hd
      subst hd
      have hdc := rqCode_pred hl hX hc hcW
      rcases eq_or_ne d 0 with rfl | hd0
      · rw [zero_add] at hv ⊢
        exact hB1 K hKw hv Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, (hown b X0 h).2.1⟩)
      · have hd1 : 1 ≤ d := Order.one_le_iff_ne_zero.2 hd0
        have e1 : taV (TaT.term TaT.zero R d) + leWe (taV R) * 1 = leWe (taV R) * (d + 1) := by
          show 0 + leWe (taV R) * d + leWe (taV R) * 1 = _; rw [zero_add, mul_one, mul_add_one]
        have e2 : taI S l (TaT.term TaT.zero R d) + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) 1 =
            leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) (d + 1) := by
          show 0 + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) d +
            leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) 1 = _
          rw [zero_add, hΘ1, mul_one, rqTh_succ hl hX hdc, mul_add_one]
        have hD := hB1 (TaC.pfx K (TaT.term TaT.zero R d)) ⟨hKw, trivial, hRw, hdc, hd1, (lt_add_one d).trans hcW⟩
          (by show taE K (taV (TaT.term TaT.zero R d) + leWe (taV R) * 1) = v; rw [e1]; exact hv) Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hR, hcl⟩ := hown b X0 h
            have hle : ∀ y, taE K y ≤ taE K (0 + y) := fun y => taE_mono K le_add_self
            refine ⟨⟨hK, trivial, taOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => taE_mono K (leWe_mono h))
              (fun _ _ h => taE_mono K ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
              sgLimC_mono hGm (fun _ _ h => taE_mono K ((add_le_add_iff_left _).2 (leMulWe_mono h)))
                (fun z => hle _) le_rfl le_rfl (sgLimC_le hcl le_self_add)⟩, ?_⟩
            exact taOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => taE_mono K (leWe_mono h))
              (fun _ _ h => taE_mono K ((add_le_add_iff_left _).2 (leWe_mono h)))
              (fun y => taE_mono K le_add_self) hR)
        exact taDer_cast hD (by show taE K (taV (TaT.term TaT.zero R d) + leWe (taV R) * 1) = _; rw [e1])
          (by show taEh S l K (taI S l (TaT.term TaT.zero R d) +
            leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) 1) = _; rw [e2])
    · have hlimD := TaDer.lim (g := fun z => taE K (leWe (taV R) * z))
        (gh := fun v => taEh S l K (leOe (taI S l R) * v)) (Ow := Ow)
        (fun b X0 h => (taShp_path hl hX (K := K) (F := R) hKw hRw (hown b X0 h).1 (hown b X0 h).2.1).shp)
        hmono hc hcW hlim
        (fun ζ hζ hζc => by
          have hζ1 := hlim.succ_lt hζc
          have hlt : taE K (leWe (taV R) * (ζ + 1)) < v := by rw [← hv]; exact taE_strictMono K (leMulWe_lt hζ1)
          have hGm' : Monotone (fun z => leWe (taE K (leWe (taV R) * z))) := fun _ _ h => leWe_mono (hGm h)
          exact (IH _ hlt).2 K R (ζ + 1) hKw hRw (rqCode_succ hl hX hζ (hζ1.trans hcW)) le_add_self
            (hζ1.trans hcW) rfl _ (scOwSq_mono hGm' hmono (ζ + 1))
            (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2.1, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩))
      exact TaDer.weaken hlimD (fun b X0 h => ⟨h, (hown b X0 h).2.2 c le_rfl hlim⟩) hmono
  -- the structural induction on the exponent: the full second part, and the term statement at a context
  have key : ∀ R : TaT,
      (∀ (K : TaC) (c : Ordinal.{0}), TaWFC S l K → TaWF S l R → GxCl (upsilon l) (ldAtR S l) c →
        1 ≤ c → c < Om (1 + 1) → taE K (leWe (taV R) * c) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (fun r => taE K (leWe r)) R ∧
          SgLimC S (fun z => taE K (leWe (taV R) * z)) c b X0) →
        TaDer S l Ow (taE K (leWe (taV R) * c))
          (taEh S l K (leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c))) ∧
      (∀ K : TaC, TaWFC S l K → TaWF S l R → 1 ≤ taV R → taE K (taV R) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → TaOwnC S b X0 K ∧ TaOwn S b X0 (taE K) R) →
        TaDer S l Ow (taE K (taV R)) (taEh S l K (taI S l R))) := by
    intro R
    induction R with
    | zero =>
      refine ⟨fun K c hKw hRw => hC TaT.zero hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw,
        fun _ _ _ h1 => absurd h1 (not_le.2 zero_lt_one)⟩
      have e1 : leWe (taV TaT.zero) * 1 = taV TaT.zero + 1 := by
        show leWe 0 * 1 = 0 + 1; rw [leWe_zero, mul_one, zero_add]
      have e2 : leOe (taI S l TaT.zero) * gxTh (upsilon l) (ldAtR S l) 1 = taI S l TaT.zero + 1 := by
        show leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [leOe_zero, hΘ1, mul_one, zero_add]
      rw [e1, e2]
      exact hA K TaT.zero hKw trivial (by rw [← e1]; exact hv) Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, trivial⟩)
    | phi a Y IHY =>
      obtain ⟨-, IHD⟩ := IHY
      refine ⟨fun K c hKw hRw => hC (TaT.phi a Y) hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw, ?_⟩
      · obtain ⟨ha, hYw, hY1, _⟩ := hRw
        have hD := IHD (TaC.phi (TaC.lft K) a) ⟨hKw, ha⟩ hYw hY1
          (by show taE K (leWe (veblen a (Om (1 + 1) + taV Y))) = v; rw [← hv, mul_one]; rfl) Ow hmono
          (fun b X0 h => ⟨(hown b X0 h).1, (hown b X0 h).2⟩)
        refine taDer_cast hD ?_ ?_
        · show taE K (leWe (veblen a (Om (1 + 1) + taV Y))) = taE K (leWe (taV (TaT.phi a Y)) * 1)
          rw [mul_one]; rfl
        · show taEh S l K (leOe (veblen a (Om 1 + taI S l Y))) =
            taEh S l K (leOe (taI S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1)
          rw [hΘ1, mul_one]; rfl
      · intro K hKw hRw _ hv Ow hmono hown
        obtain ⟨ha, hYw, hY1, _⟩ := hRw
        exact IHD (TaC.phi K a) ⟨hKw, ha⟩ hYw hY1 hv Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, (hown b X0 h).2⟩)
    | term P' R' c' _ IHR =>
      obtain ⟨IHRB, -⟩ := IHR
      refine ⟨fun K c hKw hRw => hC (TaT.term P' R' c') hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw, ?_⟩
      · obtain ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ := hRw
        have hD := IHRB (TaC.pfx (TaC.lft K) P') c' ⟨hKw, hP'w⟩ hR'w hc' hc'1 hc'W
          (by show taE K (leWe (taV P' + leWe (taV R') * c')) = v; rw [← hv, mul_one]; rfl) Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨hK, hP⟩, hR, hcl⟩)
        exact taDer_cast hD (by show taE K (leWe (taV P' + leWe (taV R') * c')) = _; rw [mul_one]; rfl)
          (by show taEh S l K (leOe (taI S l P' + leOe (taI S l R') * gxTh (upsilon l) (ldAtR S l) c')) = _
              rw [hΘ1, mul_one]; rfl)
      · intro K hKw hRw _ hv Ow hmono hown
        obtain ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ := hRw
        exact IHRB (TaC.pfx K P') c' ⟨hKw, hP'w⟩ hR'w hc' hc'1 hc'W hv Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨hK, hP⟩, hR, hcl⟩)
  exact ⟨hA, fun K R c hKw hRw hc hc1 hcW hv => (key R).1 K c hKw hRw hc hc1 hcW hv⟩

omit hl hX in
/-- The own predicate of a term at the top level is monotone in the base and the offset. -/
theorem taOwn_top_mono (t : TaT) : ∀ b β X0 X0', TaOwn S b X0 (fun y => y) t → b ≤ β → X0 ≤ X0' →
    TaOwn S β X0' (fun y => y) t :=
  fun _ _ _ _ h hb hX0 => taOwn_mono hb hX0 t _ _ monotone_id monotone_id (fun _ => le_rfl) h

/-- **Every well-formed term `t` with `val t ≥ 1` is derived** (own predicate `TaOwn id t`, image `taI t`). -/
theorem taDer_term : ∀ t : TaT, TaWF S l t → 1 ≤ taV t →
    TaDer S l (fun b X0 => TaOwn S b X0 (fun y => y) t) (taV t) (taI S l t)
  | .zero, _, h1 => absurd h1 (not_le.2 zero_lt_one)
  | .phi a Y, hw, _ => by
    obtain ⟨hρSC, -⟩ := leRho hl hX
    have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
    have hw' := hw
    obtain ⟨ha, _, hY1, hYh1⟩ := hw'
    have hD := (taGen_all hl hX _).2 TaC.hole (TaT.phi a Y) 1 trivial hw (GxCl.small h1ρ) le_rfl
      (gg_one_lt_of_SC ldOm2_SC) rfl (fun b X0 => TaOwn S b X0 (fun y => y) (TaT.phi a Y))
      (taOwn_top_mono _) (fun b X0 h => ⟨trivial, taOwn_mono le_rfl le_rfl Y
        (fun y => veblen a (Om (1 + 1) + y)) (fun y => leWe (veblen a (Om (1 + 1) + y)))
        (taNode_mono _ a) (fun _ _ hxy => leWe_mono (taNode_mono _ a hxy)) (fun y => taLe_We _) h, sgLimC_one⟩)
    exact taDer_cast hD (taV_node ha hY1) (taI_node ha hYh1 h1ρ.le)
  | .term P R c, ⟨hPw, hRw, hc, hc1, hcW⟩, _ =>
    (taGen_all hl hX _).2 (TaC.pfx TaC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl _
      (taOwn_top_mono _) (fun b X0 ⟨hP, hR, hcl⟩ => ⟨⟨trivial, hP⟩, hR, hcl⟩)

/-- **The level statement at every well-formed term with nodes**: `Sc.ScLev (TaOwn id t) (val t) (taI t)`. -/
theorem taLev_term (t : TaT) (ht : TaWF S l t) (h1 : 1 ≤ taV t) :
    ScLev S l (fun b X0 => TaOwn S b X0 (fun y => y) t) (taV t) (taI S l t) :=
  (taDer_sound hl hX (taDer_term hl hX t ht h1)).1

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Ta
