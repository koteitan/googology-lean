import Googology.Trans.PoR.InaccPsi.R2.SwDer

/-!
# Every own term with leaves is derived

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `SQ_j(g) = Sc.scSq S (z ↦ W^{g z}) X₀ b j`,
`L_k = ε_{Ω₂+1+k}`, `L̂_k = ε_{Ω₁+1+k}`.

One induction on the value `v`, inside it on the context and the term, as in `Sg.sgGen_all`, with two new cases:
* `K(L_k + 1)` at the hole: the successor of `L_k`;
* `K(W^{L_k}·1) = K(L_k)` (**the leaf**): the ω-limit rule `Sw.SwDer.wlim` with the members
  `K(W^{t_j}·1)`, `t_j` the tower terms of `L_k` (values `< v`, derived by the induction hypothesis with the same
  own predicate), cofinal because `K` and `W^·` are normal functions and the tower is cofinal in `L_k`; the own data
  of `K(L_k)` from the prefixes of `K` (`Sw.swOwP_ctx`).

* `swGen_all` (**THE GENERATION: at every value both parts hold**);
* `swDer_term` (**every well-formed term `t` with `val t ≥ 1`, leaves included, is derived**, own predicate
  `SwOwn id t`, image `swI t`), `swLev_term` (**the level statement `Sc.ScLev` at every such term**).

No new axiom.  New definition: `SwGenAt` (a statement name).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

/-- **The generation statement at the value `v`.** -/
def SwGenAt (S : InaccSeq.{0}) (l v : Ordinal.{0}) : Prop :=
  (∀ (K : SwC) (Q : SwT), SwWFC S l K → SwWF S l Q → swE K (swV Q + 1) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → SwOwnC S b X0 K ∧ SwOwn S b X0 (swE K) Q) →
    SwDer S l Ow (swE K (swV Q + 1)) (swEh S l K (swI S l Q + 1))) ∧
  (∀ (K : SwC) (R : SwT) (c : Ordinal.{0}), SwWFC S l K → SwWF S l R → GxCl (upsilon l) (ldAtR S l) c →
    1 ≤ c → c < Om (1 + 1) → swE K (leWe (swV R) * c) = v →
    ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
    (∀ b X0, Ow b X0 → SwOwnC S b X0 K ∧ SwOwn S b X0 (fun r => swE K (leWe r)) R ∧
      SgLimC S (fun z => swE K (leWe (swV R) * z)) c b X0) →
    SwDer S l Ow (swE K (leWe (swV R) * c)) (swEh S l K (leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) c)))

variable {S : InaccSeq.{0}}

theorem swDer_cast {l : Ordinal.{0}} {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {x x' y y' : Ordinal.{0}}
    (h : SwDer S l Ow x y) (hx : x = x') (hy : y = y') : SwDer S l Ow x' y' := hx ▸ hy ▸ h

theorem swL_lim (k : ℕ) : IsSuccLimit (swL k) := by
  unfold swL
  rw [← gg_veblen_eps (x := (1 : Ordinal.{0})) one_ne_zero]
  exact isSuccLimit_opow_left isSuccLimit_omega0 (veblen_pos).ne'

theorem swLh_lim (k : ℕ) : IsSuccLimit (swLh k) := by
  unfold swLh
  rw [← gg_veblen_eps (x := (1 : Ordinal.{0})) one_ne_zero]
  exact isSuccLimit_opow_left isSuccLimit_omega0 (veblen_pos).ne'

section Gen

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LEAF: `K(L_k)` is derived** from the members `K(W^{t_j}·1)` by the ω-limit rule. -/
theorem swDer_leaf {v : Ordinal.{0}} (IH : ∀ y, y < v → SwGenAt S l y) (k : ℕ) (K : SwC) (hKw : SwWFC S l K)
    (hv : swE K (leWe (swV (SwT.eps k)) * 1) = v) (Ow : Ordinal.{0} → Ordinal.{0} → Prop)
    (hmono : ∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0')
    (hown : ∀ b X0, Ow b X0 → SwOwnC S b X0 K) :
    SwDer S l Ow (swE K (leWe (swV (SwT.eps k)) * 1))
      (swEh S l K (leOe (swI S l (SwT.eps k)) * gxTh (upsilon l) (ldAtR S l) 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  have eE : leWe (swV (SwT.eps k)) * 1 = swL k := by show leWe (swL k) * 1 = _; rw [mul_one, swL_We]
  have eEh : leOe (swI S l (SwT.eps k)) * gxTh (upsilon l) (ldAtR S l) 1 = swLh k := by
    show leOe (swLh k) * _ = _; rw [hΘ1, mul_one, swLh_Oe]
  rw [eE, eEh]
  rw [eE] at hv
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1ρ
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  set e : ℕ → Ordinal.{0} := fun j => swE K (leWe (swV (swTw k j)) * 1) with he
  set eh : ℕ → Ordinal.{0} := fun j => swEh S l K (leOe (swI S l (swTw k j)) * gxTh (upsilon l) (ldAtR S l) 1)
    with heh
  have hval : ∀ j, swV (swTw k j) = swTwg (Om (1 + 1)) k j := fun j => (swTw_val (S := S) h1ρ k j).1
  have himg : ∀ j, swI S l (swTw k j) = swTwg (Om 1) k j := fun j => (swTw_val h1ρ k j).2
  have hek : ∀ j, e j < swE K (swL k) := by
    intro j
    refine swE_strictMono K ?_
    rw [hval, mul_one]
    exact swOpow_lt ldOm2_SC (swTwg_lt ldOm2_SC k j)
  have hehk : ∀ j, eh j < swEh S l K (swLh k) := by
    intro j
    refine swEh_strictMono l K ?_
    rw [himg, hΘ1, mul_one]
    exact swOpow_lt Ph.ph_SC_Om1 (swTwg_lt Ph.ph_SC_Om1 k j)
  refine SwDer.wlim (e := e) (eh := eh) ?_ ?_ ?_ (fun j => ?_) hek hehk ?_ ?_
  · exact swOwP_ctx hl hX hKw hmono hown (swL_mem k) (fun _ => swL_mem k) (fun _ => swLh_mem k)
      (fun Q hQ => swL_cl hQ k) (fun Q hQ => swLh_cl hQ k)
      ((swL_one_le k).trans (swE_strictMono K).le_apply)
  · exact (swE_lt_G3 hl hX K hKw _ _ (swL_lt_G3 k) (swLh_lt_G k)).1
  · exact (swE_lt_G3 hl hX K hKw _ _ (swL_lt_G3 k) (swLh_lt_G k)).2
  · have hlt : e j < v := hv ▸ hek j
    exact (IH _ hlt).2 K (swTw k j) 1 hKw (swTw_wf h1ρ k j) hc1 le_rfl hW1 rfl Ow hmono
      (fun b X0 h => ⟨hown b X0 h, swTw_own k j _, sgLimC_one⟩)
  · intro y hy
    have hnorm : Order.IsNormal (fun x => leWe (swE K x)) :=
      ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right ldOm2_SC.1)).comp (swE_normal K)
    obtain ⟨x, hx, hyx⟩ := (hnorm.lt_iff_exists_lt (swL_lim k)).1 hy
    obtain ⟨j, hj⟩ := swTwg_cof ldOm2_SC k hx
    refine ⟨j, hyx.trans (hnorm.strictMono ?_)⟩
    show x < leWe (swV (swTw k j)) * 1
    rw [hval, mul_one]
    exact hj.trans_le (right_le_opow _ one_lt_omega0 |>.trans
      (opow_le_opow_right omega0_pos (Ordinal.le_mul_right _ ldOm2_SC.1)))
  · intro z hz
    have hnorm : Order.IsNormal (fun x => leOe (swEh S l K x)) :=
      ((isNormal_opow one_lt_omega0).comp (isNormal_mul_right (Om_pos one_ne_zero))).comp (swEh_normal l K)
    obtain ⟨x, hx, hzx⟩ := (hnorm.lt_iff_exists_lt (swLh_lim k)).1 hz
    obtain ⟨j, hj⟩ := swTwg_cof Ph.ph_SC_Om1 k hx
    refine ⟨j, hzx.trans (hnorm.strictMono ?_)⟩
    show x < leOe (swI S l (swTw k j)) * gxTh (upsilon l) (ldAtR S l) 1
    rw [himg, hΘ1, mul_one]
    exact hj.trans_le (right_le_opow _ one_lt_omega0 |>.trans
      (opow_le_opow_right omega0_pos (Ordinal.le_mul_right _ (Om_pos one_ne_zero))))

/-- **THE GENERATION at every value.** -/
theorem swGen_all : ∀ v, SwGenAt S l v := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1ρ.le
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  -- the first part, by induction on the context
  have hA : ∀ (K : SwC) (Q : SwT), SwWFC S l K → SwWF S l Q → swE K (swV Q + 1) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → SwOwnC S b X0 K ∧ SwOwn S b X0 (swE K) Q) →
      SwDer S l Ow (swE K (swV Q + 1)) (swEh S l K (swI S l Q + 1)) := by
    intro K
    induction K with
    | hole =>
      intro Q hKw hQw hv Ow hmono hown
      cases Q with
      | zero =>
        have h1 : SwDer S l (fun b X0 => ∃ j, (1 : Ordinal.{0}) < rwEX S X0 b j) 1
            (gxTh (upsilon l) (ldAtR S l) 1) :=
          SwDer.code (GxCl.small h1ρ) le_rfl (gg_one_lt_of_SC ldOm2_SC)
        refine swDer_cast (SwDer.weaken h1 (fun _ _ _ => ⟨0, gg_one_lt_of_SC Ph.ph_SC_Om1⟩) hmono) ?_ ?_
        · show (1 : Ordinal.{0}) = 0 + 1; rw [zero_add]
        · show gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [zero_add, hΘ1]
      | eps k =>
        have hlt : swE SwC.hole (leWe (swV (SwT.eps k)) * 1) < v := by
          rw [← hv]; show leWe (swL k) * 1 < swL k + 1; rw [mul_one, swL_We]; exact lt_add_one _
        have hD := (IH _ hlt).2 SwC.hole (SwT.eps k) 1 trivial trivial (GxCl.small h1ρ) le_rfl
          (gg_one_lt_of_SC ldOm2_SC) rfl Ow hmono (fun _ _ _ => ⟨trivial, trivial, sgLimC_one⟩)
        refine swDer_cast (SwDer.succ hD) ?_ ?_
        · show leWe (swL k) * 1 + 1 = swL k + 1; rw [mul_one, swL_We]
        · show leOe (swLh k) * gxTh (upsilon l) (ldAtR S l) 1 + 1 = swLh k + 1; rw [hΘ1, mul_one, swLh_Oe]
      | term P R c =>
        obtain ⟨hPw, hRw, hc, hc1, hcW⟩ := hQw
        have hlt : swV (SwT.term P R c) < v := by rw [← hv]; exact lt_add_one _
        have hD := (IH _ hlt).2 (SwC.pfx SwC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl Ow hmono
          (fun b X0 h => by
            obtain ⟨-, hP, hR, hcl⟩ := hown b X0 h
            exact ⟨⟨trivial, hP⟩, hR, hcl⟩)
        exact SwDer.succ hD
    | pfx K Q' IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have e1 : swV (swCat Q' Q) + 1 = swV Q' + (swV Q + 1) := by rw [swV_cat, add_assoc]
      have e2 : swI S l (swCat Q' Q) + 1 = swI S l Q' + (swI S l Q + 1) := by rw [swI_cat h1ρ.le, add_assoc]
      have hD := IHK (swCat Q' Q) hKw.1 (swWF_cat h1ρ hKw.2 Q hQw) (by rw [e1]; exact hv) Ow hmono
        (fun b X0 h => by
          obtain ⟨⟨hK, hQ'⟩, hQ⟩ := hown b X0 h
          exact ⟨hK, swOwn_cat Q (swE K) (swE_mono K) hQ' hQ⟩)
      exact swDer_cast hD (by rw [e1]; rfl) (by rw [e2]; rfl)
    | lft K IHK =>
      intro Q hKw hQw hv Ow hmono hown
      have hGm : Monotone (fun z => leWe (swE K (leWe (swV Q) * z))) :=
        fun _ _ h => leWe_mono (swE_mono K (leMulWe_mono h))
      refine SwDer.om (g := fun z => swE K (leWe (swV Q) * z))
        (gh := fun v => swEh S l K (leOe (swI S l Q) * v))
        (fun b X0 h => swShp_path hl hX hKw hQw (hown b X0 h).1 (hown b X0 h).2) hmono ?_
      intro ζ hζ h1 hζW
      have hlt : swE K (leWe (swV Q) * ζ) < v := by
        rw [← hv]; exact swE_strictMono K (rvWe_lt_succ hζW)
      exact (IH _ hlt).2 K Q ζ hKw hQw hζ h1 hζW rfl _ (scOwSq_mono hGm hmono ζ)
        (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩)
  -- the second part: from `c = 1` to every code `c`
  have hC : ∀ R : SwT, SwWF S l R →
      (∀ K : SwC, SwWFC S l K → swE K (leWe (swV R) * 1) = v →
        ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
        (∀ b X0, Ow b X0 → SwOwnC S b X0 K ∧ SwOwn S b X0 (fun r => swE K (leWe r)) R) →
        SwDer S l Ow (swE K (leWe (swV R) * 1))
          (swEh S l K (leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) 1))) →
      ∀ (K : SwC) (c : Ordinal.{0}), SwWFC S l K → GxCl (upsilon l) (ldAtR S l) c →
      1 ≤ c → c < Om (1 + 1) → swE K (leWe (swV R) * c) = v →
      ∀ Ow : Ordinal.{0} → Ordinal.{0} → Prop, (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ b X0, Ow b X0 → SwOwnC S b X0 K ∧ SwOwn S b X0 (fun r => swE K (leWe r)) R ∧
        SgLimC S (fun z => swE K (leWe (swV R) * z)) c b X0) →
      SwDer S l Ow (swE K (leWe (swV R) * c)) (swEh S l K (leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) c)) := by
    intro R hRw hB1 K c hKw hc hc1 hcW hv Ow hmono hown
    have hGm : Monotone (fun z => swE K (leWe (swV R) * z)) := fun _ _ h => swE_mono K (leMulWe_mono h)
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨d, hd⟩ | hlim
    · subst h0; exact absurd hc1 (not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hd
      subst hd
      have hdc := rqCode_pred hl hX hc hcW
      rcases eq_or_ne d 0 with rfl | hd0
      · rw [zero_add] at hv ⊢
        exact hB1 K hKw hv Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, (hown b X0 h).2.1⟩)
      · have hd1 : 1 ≤ d := Order.one_le_iff_ne_zero.2 hd0
        have e1 : swV (SwT.term SwT.zero R d) + leWe (swV R) * 1 = leWe (swV R) * (d + 1) := by
          show 0 + leWe (swV R) * d + leWe (swV R) * 1 = _; rw [zero_add, mul_one, mul_add_one]
        have e2 : swI S l (SwT.term SwT.zero R d) + leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) 1 =
            leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) (d + 1) := by
          show 0 + leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) d +
            leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) 1 = _
          rw [zero_add, hΘ1, mul_one, rqTh_succ hl hX hdc, mul_add_one]
        have hD := hB1 (SwC.pfx K (SwT.term SwT.zero R d)) ⟨hKw, trivial, hRw, hdc, hd1, (lt_add_one d).trans hcW⟩
          (by show swE K (swV (SwT.term SwT.zero R d) + leWe (swV R) * 1) = v; rw [e1]; exact hv) Ow hmono
          (fun b X0 h => by
            obtain ⟨hK, hR, hcl⟩ := hown b X0 h
            have hle : ∀ y, swE K y ≤ swE K (0 + y) := fun y => swE_mono K le_add_self
            refine ⟨⟨hK, trivial, swOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => swE_mono K (leWe_mono h))
              (fun _ _ h => swE_mono K ((add_le_add_iff_left _).2 (leWe_mono h))) (fun y => hle _) hR,
              sgLimC_mono hGm (fun _ _ h => swE_mono K ((add_le_add_iff_left _).2 (leMulWe_mono h)))
                (fun z => hle _) le_rfl le_rfl (sgLimC_le hcl le_self_add)⟩, ?_⟩
            exact swOwn_mono le_rfl le_rfl R _ _ (fun _ _ h => swE_mono K (leWe_mono h))
              (fun _ _ h => swE_mono K ((add_le_add_iff_left _).2 (leWe_mono h)))
              (fun y => swE_mono K le_add_self) hR)
        exact swDer_cast hD (by show swE K (swV (SwT.term SwT.zero R d) + leWe (swV R) * 1) = _; rw [e1])
          (by show swEh S l K (swI S l (SwT.term SwT.zero R d) +
            leOe (swI S l R) * gxTh (upsilon l) (ldAtR S l) 1) = _; rw [e2])
    · have hlimD := SwDer.lim (g := fun z => swE K (leWe (swV R) * z))
        (gh := fun v => swEh S l K (leOe (swI S l R) * v)) (Ow := Ow)
        (fun b X0 h => swShp_path hl hX hKw hRw (hown b X0 h).1 (hown b X0 h).2.1) hmono hc hcW hlim
        (fun ζ hζ hζc => by
          have hζ1 := hlim.succ_lt hζc
          have hlt : swE K (leWe (swV R) * (ζ + 1)) < v := by rw [← hv]; exact swE_strictMono K (leMulWe_lt hζ1)
          have hGm' : Monotone (fun z => leWe (swE K (leWe (swV R) * z))) := fun _ _ h => leWe_mono (hGm h)
          exact (IH _ hlt).2 K R (ζ + 1) hKw hRw (rqCode_succ hl hX hζ (hζ1.trans hcW)) le_add_self
            (hζ1.trans hcW) rfl _ (scOwSq_mono hGm' hmono (ζ + 1))
            (fun b X0 ⟨h, j, hj⟩ => ⟨(hown b X0 h).1, (hown b X0 h).2.1, fun η hη _ => ⟨j, hη.trans_lt hj⟩⟩))
      exact SwDer.weaken hlimD (fun b X0 h => ⟨h, (hown b X0 h).2.2 c le_rfl hlim⟩) hmono
  refine ⟨hA, fun K R => ?_⟩
  induction R generalizing K with
  | zero =>
    intro c hKw hRw
    refine hC SwT.zero hRw (fun K hKw hv Ow hmono hown => ?_) K c hKw
    have e1 : leWe (swV SwT.zero) * 1 = swV SwT.zero + 1 := by
      show leWe 0 * 1 = 0 + 1; rw [leWe_zero, mul_one, zero_add]
    have e2 : leOe (swI S l SwT.zero) * gxTh (upsilon l) (ldAtR S l) 1 = swI S l SwT.zero + 1 := by
      show leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = 0 + 1; rw [leOe_zero, hΘ1, mul_one, zero_add]
    rw [e1, e2]
    exact hA K SwT.zero hKw trivial (by rw [← e1]; exact hv) Ow hmono (fun b X0 h => ⟨(hown b X0 h).1, trivial⟩)
  | eps k =>
    intro c hKw hRw
    exact hC (SwT.eps k) hRw (fun K hKw hv Ow hmono hown =>
      swDer_leaf hl hX IH k K hKw hv Ow hmono (fun b X0 h => (hown b X0 h).1)) K c hKw
  | term P' R' c' _ IHR =>
    intro c hKw hRw
    obtain ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ := hRw
    refine hC (SwT.term P' R' c') ⟨hP'w, hR'w, hc', hc'1, hc'W⟩ (fun K hKw hv Ow hmono hown => ?_) K c hKw
    have hD := IHR (SwC.pfx (SwC.lft K) P') c' ⟨hKw, hP'w⟩ hR'w hc' hc'1 hc'W
      (by show swE K (leWe (swV P' + leWe (swV R') * c')) = v; rw [← hv, mul_one]; rfl) Ow hmono
      (fun b X0 h => by
        obtain ⟨hK, hP, hR, hcl⟩ := hown b X0 h
        exact ⟨⟨hK, hP⟩, hR, hcl⟩)
    exact swDer_cast hD (by show swE K (leWe (swV P' + leWe (swV R') * c')) = _; rw [mul_one]; rfl)
      (by show swEh S l K (leOe (swI S l P' + leOe (swI S l R') * gxTh (upsilon l) (ldAtR S l) c')) = _
          rw [hΘ1, mul_one]; rfl)

omit hl hX in
/-- The own predicate of a term at the top level is monotone in the base and the offset. -/
theorem swOwn_top_mono (t : SwT) : ∀ b β X0 X0', SwOwn S b X0 (fun y => y) t → b ≤ β → X0 ≤ X0' →
    SwOwn S β X0' (fun y => y) t :=
  fun _ _ _ _ h hb hX0 => swOwn_mono hb hX0 t _ _ monotone_id monotone_id (fun _ => le_rfl) h

/-- **Every well-formed term `t` with `val t ≥ 1` is derived** (own predicate `SwOwn id t`, image `swI t`). -/
theorem swDer_term : ∀ t : SwT, SwWF S l t → 1 ≤ swV t →
    SwDer S l (fun b X0 => SwOwn S b X0 (fun y => y) t) (swV t) (swI S l t)
  | .zero, _, h1 => absurd h1 (not_le.2 zero_lt_one)
  | .eps k, _, _ => by
    obtain ⟨hρSC, -⟩ := leRho hl hX
    have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
    have hD := (swGen_all hl hX _).2 SwC.hole (SwT.eps k) 1 trivial trivial (GxCl.small h1ρ) le_rfl
      (gg_one_lt_of_SC ldOm2_SC) rfl (fun b X0 => SwOwn S b X0 (fun y => y) (SwT.eps k))
      (swOwn_top_mono _) (fun _ _ _ => ⟨trivial, trivial, sgLimC_one⟩)
    refine swDer_cast hD ?_ ?_
    · show leWe (swL k) * 1 = swL k; rw [mul_one, swL_We]
    · show leOe (swLh k) * gxTh (upsilon l) (ldAtR S l) 1 = swLh k
      rw [gxTh_small h1ρ.le, mul_one, swLh_Oe]
  | .term P R c, ⟨hPw, hRw, hc, hc1, hcW⟩, _ =>
    (swGen_all hl hX _).2 (SwC.pfx SwC.hole P) R c ⟨trivial, hPw⟩ hRw hc hc1 hcW rfl _
      (swOwn_top_mono _) (fun b X0 ⟨hP, hR, hcl⟩ => ⟨⟨trivial, hP⟩, hR, hcl⟩)

/-- **The level statement at every well-formed term with leaves**: `Sc.ScLev (SwOwn id t) (val t) (swI t)`. -/
theorem swLev_term (t : SwT) (ht : SwWF S l t) (h1 : 1 ≤ swV t) :
    ScLev S l (fun b X0 => SwOwn S b X0 (fun y => y) t) (swV t) (swI S l t) :=
  (swDer_sound hl hX (swDer_term hl hX t ht h1)).1

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Sw
