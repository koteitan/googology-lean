import Googology.Trans.PoR.InaccPsi.R2.TjMem

/-!
# THE NODE DERIVATION WITH CODE LEVELS: every own term with nodes at code levels `1 ≤ a < Ω₂` is derived

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, terms and contexts of `Ta`, values
`Ta.taV`, `Ta.taE`, images `Td.tdIL`, `Tg.tgEh` (the levels read by `Θ`).  The induction of `Td.tdGen_all` with the
well-formed terms `Tg.TgWF` and the own predicate `Tj.TjOwn`; derivations `Td.TdDer`.

* `tjDer_node` (**THE NODE AT A SUCCESSOR ARGUMENT `K(φ(a, Ω₂ + Q + 1))`**: at a successor code level by the
  members of `Tj.tjTw_family`; at a limit code level `a` by the members `φ(c', Ω₂ + φ(a, Ω₂ + Q) + 1)`, `c' < a`
  codes, which are cofinal among the hull elements (`Td.tdHull_levDec`, `Tj.tjCtx_cof`) and whose images are
  cofinal (`Td.tdTh_levCof`): the hull-limit rule `Td.TdDer.hlim`; every member is own wherever the node is own);
* `TjGenAt`, `tjGen_all` (**THE GENERATION at every value**);
* `tjDer_term` (**every well-formed term `t` with code levels and `val t ≥ 1` is derived** with the own predicate
  `TjOwn id t`), `tjLev_term`, `tjOwP_term` (**`Sc.ScLev` and `Sc.ScOwP` at every such term**, by
  `Td.tdDer_sound`).

No new axiom.  New definition: `TjGenAt` (a statement name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

/-- **The generation statement at the value `v`.** -/
def TjGenAt (S : InaccSeq.{0}) (l v : Ordinal.{0}) : Prop :=
  (∀ (K : TaC) (Q : TaT), TgWFC S l K → TgWF S l Q → taE K (taV Q + 1) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (taE K) Q) →
    TdDer S l Ow (taE K (taV Q + 1)) (tgEh S l K (tdIL S l Q + 1))) ∧
  (∀ (K : TaC) (R : TaT) (c : Ordinal.{0}), TgWFC S l K → TgWF S l R → GxCl (upsilon l) (ldAtR S l) c →
    1 ≤ c → c < Om (1 + 1) → taE K (leWe (taV R) * c) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (fun r => taE K (leWe r)) R ∧
      SgLimC S (fun z => taE K (leWe (taV R) * z)) c b X0) →
    TdDer S l Ow (taE K (leWe (taV R) * c)) (tgEh S l K (leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c)))

variable {S : InaccSeq.{0}}

section Gen

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE NODE AT A SUCCESSOR ARGUMENT WITH A CODE LEVEL: `K(φ(a, Ω₂ + Q + 1))` is derived** from its members by
the hull-limit rule. -/
theorem tjDer_node {v : Ordinal.{0}} (IH : ∀ y, y < v → TjGenAt S l y) (K : TaC) (a : Ordinal.{0}) (Q : TaT)
    (hKw : TgWFC S l K) (hac : GxCl (upsilon l) (ldAtR S l) a) (ha1 : 1 ≤ a) (haW : a < Om (1 + 1))
    (hQw : TgWF S l Q) (hv : taE (TaC.phi K a) (taV Q + 1) = v)
    (Ow : Ordinal.{0} → Ordinal.{0} → Prop) (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')
    (hown : ∀ b X0, Ow b X0 → TjOwnC S b X0 (TaC.phi K a) ∧ TjOwn S b X0 (taE (TaC.phi K a)) Q) :
    TdDer S l Ow (taE (TaC.phi K a) (taV Q + 1)) (tgEh S l (TaC.phi K a) (tdIL S l Q + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  set Θa := gxTh (upsilon l) (ldAtR S l) a with hΘa_def
  have hΘa1 : 1 ≤ Θa := tgTh_one h1ρ.le ha1
  have hΘa0 : Θa ≠ 0 := (zero_lt_one.trans_le hΘa1).ne'
  have hKa : TgWFC S l (TaC.phi K a) := ⟨hKw, hac, ha1, haW⟩
  set L := veblen a (Om (1 + 1) + (taV Q + 1)) with hL
  set Lh := veblen Θa (Om 1 + (tdIL S l Q + 1)) with hLh
  have eE : taE (TaC.phi K a) (taV Q + 1) = taE K L := rfl
  have eEh : tgEh S l (TaC.phi K a) (tdIL S l Q + 1) = tgEh S l K Lh := rfl
  have hWL : leWe L = L := taWe_veb ha0 le_add_self
  have hOL : leOe Lh = Lh := taOe_veb hΘa0 le_add_self
  have hLlim : IsSuccLimit L := taVeb_lim ha0
  have hLhlim : IsSuccLimit Lh := taVeb_lim hΘa0
  have hG3 := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  obtain ⟨hQ3, hQ1⟩ := tgV_lt_G3 hl hX Q hQw
  have hb := tjE_lt_G3 hl hX (TaC.phi K a) hKa _ _ (hG3.add_one_lt hQ3) (hG1.add_one_lt hQ1)
  have hP := tjOwP_succ hl hX (K := TaC.phi K a) hKa hQw hmono hown
  rw [eE, eEh] at hb hP ⊢
  have hnormV : Order.IsNormal (fun x => leWe (taE K x)) :=
    ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right ldOm2_SC.1)).comp (taE_normal K)
  have hnormI : Order.IsNormal (fun x => leOe (tgEh S l K x)) :=
    ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right (Om_pos one_ne_zero))).comp (tgEh_normal l K)
  -- the members are derived by the induction hypothesis
  have hmem : ∀ R : TaT, TgWF S l R → taV R < L →
      (∀ b X0, Ow b X0 → TjOwn S b X0 (fun r => taE K (leWe r)) R) →
      TdDer S l Ow (taE K (leWe (taV R) * 1)) (tgEh S l K (leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) 1)) := by
    intro R hRw hRL hRo
    have hlt : taE K (leWe (taV R) * 1) < v := by
      rw [← hv, eE, mul_one]; exact taE_strictMono K (hWL ▸ leWe_lt hRL)
    exact (IH _ hlt).2 K R 1 hKw hRw (GxCl.small h1ρ) le_rfl hW1 rfl Ow hmono
      (fun b X0 h => ⟨(hown b X0 h).1.1, hRo b X0 h, sgLimC_one⟩)
  have hvalLt : ∀ R : TaT, taV R < L → taE K (leWe (taV R) * 1) < taE K L := fun R hR => by
    rw [mul_one]; exact taE_strictMono K (hWL ▸ leWe_lt hR)
  have himgLt : ∀ R : TaT, tdIL S l R < Lh →
      tgEh S l K (leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) 1) < tgEh S l K Lh := fun R hR => by
    rw [hΘ1, mul_one]; exact tgEh_strictMono l K (hOL ▸ leOe_lt hR)
  by_cases hlim : IsSuccLimit a
  · -- a limit code level: the members `φ(c', Ω₂ + t₀)`, `c' < a` codes
    obtain ⟨hv0, hi0, hw0⟩ := tjBase_val hl hX hac ha1 haW Q hQw
    have hv1 : 1 ≤ taV (taBase a Q) := hv0 ▸ le_add_self
    have hi1 : 1 ≤ tdIL S l (taBase a Q) := hi0 ▸ le_add_self
    have h1a : 1 < a := by
      have := hlim.add_one_lt (pos_iff_ne_zero.2 hlim.ne_bot); rwa [zero_add] at this
    set ι := {c' : Ordinal.{0} // GxCl (upsilon l) (ldAtR S l) c' ∧ 1 ≤ c' ∧ c' < a} with hι
    let R : ι → TaT := fun i => TaT.phi i.1 (taBase a Q)
    have hRw : ∀ i : ι, TgWF S l (R i) := fun i => ⟨i.2.1, i.2.2.1, i.2.2.2.trans haW, hw0, hv1, hi1⟩
    have hRv : ∀ i : ι, taV (R i) < L := by
      intro i
      show veblen i.1 (Om (1 + 1) + taV (taBase a Q)) < L
      rw [hv0]
      exact (taVeb_lim_lt (κ := Om (1 + 1)) (z := Om (1 + 1) + taV Q) ha0 i.2.2.2
        ((le_self_add.trans_lt (lt_add_one _)).trans_le (right_le_veblen a _))).trans_eq (by rw [hL, add_assoc])
    have hRi : ∀ i : ι, tdIL S l (R i) < Lh := by
      intro i
      show veblen (gxTh (upsilon l) (ldAtR S l) i.1) (Om 1 + tdIL S l (taBase a Q)) < Lh
      rw [hi0]
      exact (taVeb_lim_lt (κ := Om 1) (z := Om 1 + tdIL S l Q) hΘa0 (gxTh_lt i.2.1 i.2.2.2)
        ((le_self_add.trans_lt (lt_add_one _)).trans_le (right_le_veblen _ _))).trans_eq (by rw [hLh, add_assoc])
    -- a code `c'' < a` gives a member at `max c'' 1`
    have hmax : ∀ c'', GxCl (upsilon l) (ldAtR S l) c'' → c'' < a →
        ∃ i : ι, c'' ≤ i.1 := fun c'' hc'' hc''a => by
      rcases le_total c'' 1 with h | h
      · exact ⟨⟨1, GxCl.small h1ρ, le_rfl, h1a⟩, h⟩
      · exact ⟨⟨c'', hc'', h, hc''a⟩, le_rfl⟩
    refine TdDer.hlim (ι := ι) (e := fun i => taE K (leWe (taV (R i)) * 1))
      (eh := fun i => tgEh S l K (leOe (tdIL S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1))
      (Ow' := fun _ => Ow) hP hb.1 hb.2 (fun i => hmem (R i) (hRw i) (hRv i) (fun b X0 h => ?_))
      (fun i => hvalLt (R i) (hRv i)) (fun i => himgLt (R i) (hRi i)) ?_ ?_
    · obtain ⟨⟨_, hs⟩, hQo⟩ := hown b X0 h
      exact tjLim_own i.2.2.2.le (taE_mono K) hs Q hQo
    · -- the values: cofinal among the hull elements
      intro b X0 hO y hyH hy
      rcases eq_or_ne y 0 with rfl | hy0
      · exact ⟨⟨1, GxCl.small h1ρ, le_rfl, h1a⟩, hO, leWe_pos _⟩
      have hElim : IsSuccLimit (taE K L) := (taE_normal K).map_isSuccLimit hLlim
      have hlog : sgLW y < taE K L := by
        by_contra hc
        push Not at hc
        exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hy0))) (not_le.2 hy)
      have hy'H : sgLW y + 1 ∈ cdHull S l := CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem hyH))
      obtain ⟨x, hxH, hxL, hyx⟩ := tjCtx_cof K hKw L hLlim (sgLW y + 1) hy'H (hElim.add_one_lt hlog)
      have hxL' : x < veblen a ((Om (1 + 1) + taV Q) + 1) := hxL.trans_eq (by rw [hL, add_assoc])
      obtain ⟨c'', hc''H, hc''a, hxc⟩ := tdHull_levDec hlim x hxH hxL'
      obtain ⟨i, hi⟩ := hmax c'' ((ldHull_iff hl hX (hc''a.trans haW)).1 hc''H) hc''a
      refine ⟨i, hO, ?_⟩
      have hxR : x < leWe (taV (R i)) * 1 := by
        rw [mul_one]
        refine (hxc.trans_le ?_).trans_le (taLe_We _)
        show veblen c'' (veblen a (Om (1 + 1) + taV Q) + 1) ≤ veblen i.1 (Om (1 + 1) + taV (taBase a Q))
        rw [hv0]
        exact (veblen_left_monotone _ hi).trans ((veblen_le_veblen_iff_right).2 le_add_self)
      exact (sgLW_lt y).trans_le ((leWe_mono hyx.le).trans (leWe_lt (taE_strictMono K hxR)).le)
    · -- the images: cofinal
      intro b X0 hO z hz
      obtain ⟨x, hx, hzx⟩ := (hnormI.lt_iff_exists_lt hLhlim).1 hz
      have hx' : x < veblen Θa ((Om 1 + tdIL S l Q) + 1) := by
        have : Lh = veblen Θa ((Om 1 + tdIL S l Q) + 1) := by rw [hLh, add_assoc]
        rw [← this]; exact hx
      obtain ⟨c'', hc'', hc''a, hxc⟩ := tdTh_levCof hρSC hlim hx'
      obtain ⟨i, hi⟩ := hmax c'' hc'' hc''a
      refine ⟨i, hO, hzx.trans (hnormI.strictMono ?_)⟩
      show x < leOe (tdIL S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1
      rw [hΘ1, mul_one]
      refine (hxc.trans_le ?_).trans_le ((Ordinal.le_mul_right _ (Om_pos one_ne_zero)).trans
        (right_le_opow _ one_lt_omega0))
      show veblen (gxTh (upsilon l) (ldAtR S l) c'') (veblen Θa (Om 1 + tdIL S l Q) + 1) ≤
        veblen (gxTh (upsilon l) (ldAtR S l) i.1) (Om 1 + tdIL S l (taBase a Q))
      rw [hi0]
      exact (veblen_left_monotone _ (gxTh_mono hi)).trans ((veblen_le_veblen_iff_right).2 le_add_self)
  · -- a successor code level: the towers
    obtain ⟨ι, R, hRw, hRo, hRlt, hRcof, hRhlt, hRhcof⟩ := tjTw_family hl hX hac ha1 haW hlim Q hQw
    refine TdDer.hlim (ι := ι) (e := fun i => taE K (leWe (taV (R i)) * 1))
      (eh := fun i => tgEh S l K (leOe (tdIL S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1))
      (Ow' := fun _ => Ow) hP hb.1 hb.2
      (fun i => hmem (R i) (hRw i) (hRlt i) (fun b X0 h =>
        hRo i b X0 (taE K) (taE_mono K) (hown b X0 h).1.2 (hown b X0 h).2))
      (fun i => hvalLt (R i) (hRlt i)) (fun i => himgLt (R i) (hRhlt i)) ?_ ?_
    · intro b X0 hO y _ hy
      obtain ⟨x, hx, hyx⟩ := (hnormV.lt_iff_exists_lt hLlim).1 hy
      obtain ⟨i, hi⟩ := hRcof x hx
      refine ⟨i, hO, hyx.trans (hnormV.strictMono ?_)⟩
      show x < leWe (taV (R i)) * 1
      rw [mul_one]; exact hi.trans_le (taLe_We _)
    · intro b X0 hO z hz
      obtain ⟨x, hx, hzx⟩ := (hnormI.lt_iff_exists_lt hLhlim).1 hz
      obtain ⟨i, hi⟩ := hRhcof x hx
      refine ⟨i, hO, hzx.trans (hnormI.strictMono ?_)⟩
      show x < leOe (tdIL S l (R i)) * gxTh (upsilon l) (ldAtR S l) 1
      rw [hΘ1, mul_one]
      exact hi.trans_le ((Ordinal.le_mul_right _ (Om_pos one_ne_zero)).trans (right_le_opow _ one_lt_omega0))

/-- **THE GENERATION at every value.** -/
theorem tjGen_all : ∀ v, TjGenAt S l v := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  -- the first part, by induction on the context
  have hA : ∀ (K : TaC) (Q : TaT), TgWFC S l K → TgWF S l Q → taE K (taV Q + 1) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (taE K) Q) →
      TdDer S l Ow (taE K (taV Q + 1)) (tgEh S l K (tdIL S l Q + 1)) := by
    intro K
    induction K with
    | hole =>
      intro Q hKw hQw hv Ow hmono hown
      cases Q with
      | zero =>
        have h1 : TdDer S l (fun b X0 => ∃ j, (1 : Ordinal.{0}) < rwEX S X0 b j) 1
            (gxTh (upsilon l) (ldAtR S l) 1) :=
          TdDer.code (GxCl.small h1ρ) le_rfl hW1
        refine tdDer_cast (TdDer.weaken h1 (fun _ _ _ => ⟨0, gg_one_lt_of_SC Ph.ph_SC_Om1⟩) hmono) ?_ ?_
        · show (1 : Ordinal.{0}) = 0 + 1; rw [zero_add]
        · show gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [zero_add, hΘ1]
      | phi a Y =>
        have hQw' := hQw
        obtain ⟨hac, ha1, haW, hYw, hY1, hYh1⟩ := hQw'
        have hlt : taE TaC.hole (leWe (taV (TaT.phi a Y)) * 1) < v := by
          rw [← hv]; show leWe (taV (TaT.phi a Y)) * 1 < taV (TaT.phi a Y) + 1
          rw [tgV_node ha1 hY1]; exact lt_add_one _
        have hD := (IH _ hlt).2 TaC.hole (TaT.phi a Y) 1 trivial hQw (GxCl.small h1ρ) le_rfl
          hW1 rfl Ow hmono (fun b X0 h => ⟨trivial, tjOwn_mono le_rfl le_rfl (TaT.phi a Y) (fun y => y)
            (fun r => leWe r) monotone_id (fun _ _ h => leWe_mono h) (fun y => taLe_We y) (hown b X0 h).2,
            sgLimC_one⟩)
        refine tdDer_cast (TdDer.succ hD) ?_ ?_
        · show leWe (taV (TaT.phi a Y)) * 1 + 1 = taV (TaT.phi a Y) + 1; rw [tgV_node ha1 hY1]
        · show leOe (tdIL S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1 + 1 = tdIL S l (TaT.phi a Y) + 1
          rw [tgI_node (tgTh_one h1ρ.le ha1) hYh1 h1ρ.le]
      | term P R c =>
        obtain ⟨hPw, hRw, hc, hc1, hcW⟩ := hQw
        have hlt : taV (TaT.term P R c) < v := by rw [← hv]; exact lt_add_one _
        have hD := (IH _ hlt).2 (TaC.pfx TaC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl Ow hmono
          (fun b X0 h => by
            obtain ⟨-, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨trivial, hP⟩, hR, hcl⟩)
        exact TdDer.succ hD
    | pfx K Q' IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have e1 : taV (taCat Q' Q) + 1 = taV Q' + (taV Q + 1) := by rw [tgV_cat Q' Q hQw, add_assoc]
      have e2 : tdIL S l (taCat Q' Q) + 1 = tdIL S l Q' + (tdIL S l Q + 1) := by
        rw [tgI_cat h1ρ.le Q' Q hQw, add_assoc]
      have hD := IHK (taCat Q' Q) hKw.1 (tgWF_cat h1ρ hKw.2 Q hQw) (by rw [e1]; exact hv) Ow hmono
        (fun b X0 h => by
          obtain ⟨⟨hK, hQ'⟩, hQ⟩ := hown b X0 h
          exact ⟨hK, tjOwn_cat Q (taE K) (taE_mono K) hQw hQ' hQ⟩)
      exact tdDer_cast hD (by rw [e1]; rfl) (by rw [e2]; rfl)
    | lft K IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have hGm : Monotone (fun z => leWe (taE K (leWe (taV Q) * z))) :=
        fun _ _ h => leWe_mono (taE_mono K (leMulWe_mono h))
      refine TdDer.om (g := fun z => taE K (leWe (taV Q) * z))
        (gh := fun v => tgEh S l K (leOe (tdIL S l Q) * v)) (fun b X0 h => ?_) hmono ?_
      · obtain ⟨hKo, hQo⟩ := hown b X0 h
        obtain ⟨A, hAK, hAT⟩ := tjOwnC_lev K hKo (leWe (taV Q) * 1)
          (by rw [mul_one]; exact Order.one_le_iff_pos.2 (leWe_pos _))
        exact (tgShp_path hl hX (K := K) (F := Q) hKw hQw (tjOwnC_tg K hKw hKo)
          (tjOwn_tg Q _ (fun _ _ h => taE_mono K (leWe_mono h)) hQw hQo) hAK hAT).shp
      intro ζ hζ h1 hζW
      have hlt : taE K (leWe (taV Q) * ζ) < v := by
        rw [← hv]; exact taE_strictMono K (rvWe_lt_succ hζW)
      exact (IH _ hlt).2 K Q ζ hKw hQw hζ h1 hζW rfl _ (scOwSq_mono hGm hmono ζ)
        (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩)
    | phi K a _ =>
      intro Q hKw hQw hv Ow hmono hown
      obtain ⟨hKw', hac, ha1, haW⟩ := hKw
      exact tjDer_node hl hX IH K a Q hKw' hac ha1 haW hQw hv Ow hmono hown
  -- the second part: from `c = 1` to every code `c`
  have hC : ∀ R : TaT, TgWF S l R →
      (∀ K : TaC, TgWFC S l K → taE K (leWe (taV R) * 1) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (fun r => taE K (leWe r)) R) →
        TdDer S l Ow (taE K (leWe (taV R) * 1))
          (tgEh S l K (leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) 1))) →
      ∀ (K : TaC) (c : Ordinal.{0}), TgWFC S l K → GxCl (upsilon l) (ldAtR S l) c →
      1 ≤ c → c < Om (1 + 1) → taE K (leWe (taV R) * c) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (fun r => taE K (leWe r)) R ∧
        SgLimC S (fun z => taE K (leWe (taV R) * z)) c b X0) →
      TdDer S l Ow (taE K (leWe (taV R) * c))
        (tgEh S l K (leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c)) := by
    intro R hRw hB1 K c hKw hc hc1 hcW hv Ow hmono hown
    have hGm : Monotone (fun z => taE K (leWe (taV R) * z)) := fun _ _ h => taE_mono K (leMulWe_mono h)
    have hshp : ∀ b X0, Ow b X0 → ScShp S l (fun z => taE K (leWe (taV R) * z))
        (fun v => tgEh S l K (leOe (tdIL S l R) * v)) (taE K (leWe (taV R + 1)))
        (tgEh S l K (leOe (tdIL S l R + 1)))
        (leTe S (X0 + leWe ((fun z => taE K (leWe (taV R) * z)) 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe ((fun z => taE K (leWe (taV R) * z)) 1)) b)) := by
      intro b X0 h
      obtain ⟨hKo, hRo, -⟩ := hown b X0 h
      obtain ⟨A, hAK, hAT⟩ := tjOwnC_lev K hKo (leWe (taV R) * 1)
        (by rw [mul_one]; exact Order.one_le_iff_pos.2 (leWe_pos _))
      exact (tgShp_path hl hX (K := K) (F := R) hKw hRw (tjOwnC_tg K hKw hKo)
        (tjOwn_tg R _ (fun _ _ h => taE_mono K (leWe_mono h)) hRw hRo) hAK hAT).shp
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
        have e2 : tdIL S l (TaT.term TaT.zero R d) + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) 1 =
            leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) (d + 1) := by
          show 0 + leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) d +
            leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) 1 = _
          rw [zero_add, hΘ1, mul_one, rqTh_succ hl hX hdc, mul_add_one]
        have hD := hB1 (TaC.pfx K (TaT.term TaT.zero R d)) ⟨hKw, trivial, hRw, hdc, hd1, (lt_add_one d).trans hcW⟩
          (by show taE K (taV (TaT.term TaT.zero R d) + leWe (taV R) * 1) = v; rw [e1]; exact hv) Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hR, hcl⟩ := hown b X0 h
            have hle : ∀ y, taE K y ≤ taE K (0 + y) := fun y => taE_mono K le_add_self
            refine ⟨⟨hK, trivial, tjOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => taE_mono K (leWe_mono h))
              (fun _ _ h => taE_mono K ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
              sgLimC_mono hGm (fun _ _ h => taE_mono K ((add_le_add_iff_left _).2 (leMulWe_mono h)))
                (fun z => hle _) le_rfl le_rfl (sgLimC_le hcl le_self_add)⟩, ?_⟩
            exact tjOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => taE_mono K (leWe_mono h))
              (fun _ _ h => taE_mono K ((add_le_add_iff_left _).2 (leWe_mono h)))
              (fun y => taE_mono K le_add_self) hR)
        exact tdDer_cast hD (by show taE K (taV (TaT.term TaT.zero R d) + leWe (taV R) * 1) = _; rw [e1])
          (by show tgEh S l K (tdIL S l (TaT.term TaT.zero R d) +
            leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) 1) = _; rw [e2])
    · have hlimD := TdDer.lim (g := fun z => taE K (leWe (taV R) * z))
        (gh := fun v => tgEh S l K (leOe (tdIL S l R) * v)) (Ow := Ow) hshp hmono hc hcW hlim
        (fun ζ hζ hζc => by
          have hζ1 := hlim.succ_lt hζc
          have hlt : taE K (leWe (taV R) * (ζ + 1)) < v := by rw [← hv]; exact taE_strictMono K (leMulWe_lt hζ1)
          have hGm' : Monotone (fun z => leWe (taE K (leWe (taV R) * z))) := fun _ _ h => leWe_mono (hGm h)
          exact (IH _ hlt).2 K R (ζ + 1) hKw hRw (rqCode_succ hl hX hζ (hζ1.trans hcW)) le_add_self
            (hζ1.trans hcW) rfl _ (scOwSq_mono hGm' hmono (ζ + 1))
            (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2.1, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩))
      exact TdDer.weaken hlimD (fun b X0 h => ⟨h, (hown b X0 h).2.2 c le_rfl hlim⟩) hmono
  -- the structural induction on the exponent: the full second part, and the term statement at a context
  have key : ∀ R : TaT,
      (∀ (K : TaC) (c : Ordinal.{0}), TgWFC S l K → TgWF S l R → GxCl (upsilon l) (ldAtR S l) c →
        1 ≤ c → c < Om (1 + 1) → taE K (leWe (taV R) * c) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (fun r => taE K (leWe r)) R ∧
          SgLimC S (fun z => taE K (leWe (taV R) * z)) c b X0) →
        TdDer S l Ow (taE K (leWe (taV R) * c))
          (tgEh S l K (leOe (tdIL S l R) * gxTh (upsilon l) (ldAtR S l) c))) ∧
      (∀ K : TaC, TgWFC S l K → TgWF S l R → 1 ≤ taV R → taE K (taV R) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → TjOwnC S b X0 K ∧ TjOwn S b X0 (taE K) R) →
        TdDer S l Ow (taE K (taV R)) (tgEh S l K (tdIL S l R))) := by
    intro R
    induction R with
    | zero =>
      refine ⟨fun K c hKw hRw => hC TaT.zero hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw,
        fun _ _ _ h1 => absurd h1 (not_le.2 zero_lt_one)⟩
      have e1 : leWe (taV TaT.zero) * 1 = taV TaT.zero + 1 := by
        show leWe 0 * 1 = 0 + 1; rw [leWe_zero, mul_one, zero_add]
      have e2 : leOe (tdIL S l TaT.zero) * gxTh (upsilon l) (ldAtR S l) 1 = tdIL S l TaT.zero + 1 := by
        show leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [leOe_zero, hΘ1, mul_one, zero_add]
      rw [e1, e2]
      exact hA K TaT.zero hKw trivial (by rw [← e1]; exact hv) Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, trivial⟩)
    | phi a Y IHY =>
      obtain ⟨-, IHD⟩ := IHY
      refine ⟨fun K c hKw hRw => hC (TaT.phi a Y) hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw, ?_⟩
      · obtain ⟨hac, ha1, haW, hYw, hY1, _⟩ := hRw
        have hD := IHD (TaC.phi (TaC.lft K) a) ⟨hKw, hac, ha1, haW⟩ hYw hY1
          (by show taE K (leWe (veblen a (Om (1 + 1) + taV Y))) = v; rw [← hv, mul_one]; rfl) Ow hmono
          (fun b X0 h => ⟨⟨(hown b X0 h).1, (hown b X0 h).2.1⟩, (hown b X0 h).2.2⟩)
        refine tdDer_cast hD ?_ ?_
        · show taE K (leWe (veblen a (Om (1 + 1) + taV Y))) = taE K (leWe (taV (TaT.phi a Y)) * 1)
          rw [mul_one]; rfl
        · show tgEh S l K (leOe (veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdIL S l Y))) =
            tgEh S l K (leOe (tdIL S l (TaT.phi a Y)) * gxTh (upsilon l) (ldAtR S l) 1)
          rw [hΘ1, mul_one]; rfl
      · intro K hKw hRw _ hv Ow hmono hown
        obtain ⟨hac, ha1, haW, hYw, hY1, _⟩ := hRw
        exact IHD (TaC.phi K a) ⟨hKw, hac, ha1, haW⟩ hYw hY1 hv Ow hmono
          (fun b X0 h => ⟨⟨(hown b X0 h).1, (hown b X0 h).2.1⟩, (hown b X0 h).2.2⟩)
    | term P' R' c' _ IHR =>
      obtain ⟨IHRB, -⟩ := IHR
      refine ⟨fun K c hKw hRw => hC (TaT.term P' R' c') hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw, ?_⟩
      · obtain ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ := hRw
        have hD := IHRB (TaC.pfx (TaC.lft K) P') c' ⟨hKw, hP'w⟩ hR'w hc' hc'1 hc'W
          (by show taE K (leWe (taV P' + leWe (taV R') * c')) = v; rw [← hv, mul_one]; rfl) Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨hK, hP⟩, hR, hcl⟩)
        exact tdDer_cast hD (by show taE K (leWe (taV P' + leWe (taV R') * c')) = _; rw [mul_one]; rfl)
          (by show tgEh S l K (leOe (tdIL S l P' + leOe (tdIL S l R') * gxTh (upsilon l) (ldAtR S l) c')) = _
              rw [hΘ1, mul_one]; rfl)
      · intro K hKw hRw _ hv Ow hmono hown
        obtain ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ := hRw
        exact IHRB (TaC.pfx K P') c' ⟨hKw, hP'w⟩ hR'w hc' hc'1 hc'W hv Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨hK, hP⟩, hR, hcl⟩)
  exact ⟨hA, fun K R c hKw hRw hc hc1 hcW hv => (key R).1 K c hKw hRw hc hc1 hcW hv⟩

/-- **Every well-formed term `t` with code levels and `val t ≥ 1` is derived** (own predicate `TjOwn id t`,
image `tdIL t`). -/
theorem tjDer_term : ∀ t : TaT, TgWF S l t → 1 ≤ taV t →
    TdDer S l (fun b X0 => TjOwn S b X0 (fun y => y) t) (taV t) (tdIL S l t)
  | .zero, _, h1 => absurd h1 (not_le.2 zero_lt_one)
  | .phi a Y, hw, _ => by
    obtain ⟨hρSC, -⟩ := leRho hl hX
    have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
    have hw' := hw
    obtain ⟨_, ha1, _, _, hY1, hYh1⟩ := hw'
    have hD := (tjGen_all hl hX _).2 TaC.hole (TaT.phi a Y) 1 trivial hw (GxCl.small h1ρ) le_rfl
      (gg_one_lt_of_SC ldOm2_SC) rfl (fun b X0 => TjOwn S b X0 (fun y => y) (TaT.phi a Y))
      (tjOwn_top_mono _) (fun b X0 h => ⟨trivial, tjOwn_mono le_rfl le_rfl (TaT.phi a Y) (fun y => y)
        (fun r => leWe r) monotone_id (fun _ _ h => leWe_mono h) (fun y => taLe_We y) h, sgLimC_one⟩)
    exact tdDer_cast hD (tgV_node ha1 hY1) (tgI_node (tgTh_one h1ρ.le ha1) hYh1 h1ρ.le)
  | .term P R c, ⟨hPw, hRw, hc, hc1, hcW⟩, _ =>
    (tjGen_all hl hX _).2 (TaC.pfx TaC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl _
      (tjOwn_top_mono _) (fun b X0 ⟨hP, hR, hcl⟩ => ⟨⟨trivial, hP⟩, hR, hcl⟩)

/-- **The level statement and the own data at every well-formed term with code levels**:
`Sc.ScLev (TjOwn id t) (val t) (tdIL t)` and `Sc.ScOwP (TjOwn id t) (val t) (tdIL t)`. -/
theorem tjLev_term (t : TaT) (ht : TgWF S l t) (h1 : 1 ≤ taV t) :
    ScLev S l (fun b X0 => TjOwn S b X0 (fun y => y) t) (taV t) (tdIL S l t) ∧
      ScOwP S l (fun b X0 => TjOwn S b X0 (fun y => y) t) (taV t) (tdIL S l t) :=
  tdDer_sound hl hX (tjDer_term hl hX t ht h1)

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Tj
