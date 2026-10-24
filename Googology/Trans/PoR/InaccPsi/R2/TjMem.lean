import Googology.Trans.PoR.InaccPsi.R2.TjOwn

/-!
# The members below a node `φ(a, Ω₂ + Q + 1)` with a code level `a`

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `H_λ = cdHull S λ`, `L = φ(a, Ω₂ + Q + 1)`,
`L̂ = φ(Θ a, Ω₁ + Q̂ + 1)`.  The towers are those of `Ta` (`Ta.taBase`, `Ta.taTwW`, `Ta.taTwP`).

* `tjOmS_val`, `tjOmS_wf`, `tjBase_val`, `tjTwW_val`, `tjTwW_wf`, `tjTwP_wf` (values, images with the levels read by
  `Θ`, well-formedness with code levels);
* `tjBase_own`, `tjTwW_own`, `tjTwP_own` (**the strong level condition of the parent level `a` gives the own
  predicate of the members**: every member level is `≤ a` and every member evaluation is above the parent's);
* `tjTw_family` (**THE MEMBERS AT A SUCCESSOR CODE LEVEL**: towers `φ(a', Ω₂ + ·)` for `a = a' + 1`, `W`-towers
  for `a = 1`; own wherever the parent is own, values cofinal in `L`, images cofinal in `L̂`);
* `tjLim_own`, `tjLim_lt` (the members `φ(c', Ω₂ + t₀)` at a limit code level, `c' < a` codes);
* `tjCtx_cof` (**hull elements below `K(L)` are below `K(x)` for a hull element `x < L`**, `L` a limit).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

variable {S : InaccSeq.{0}}

/-! ## Own members -/

theorem tjBase_own {b X0 a : Ordinal.{0}} {e e' : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (he' : Monotone e') (hle : ∀ x, e x ≤ e' x) (hs : TjSLC S b X0 e a) :
    ∀ Q : TaT, TjOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TjOwn S b X0 e' (taBase a Q)
  | .zero, _ => ⟨⟨trivial, ⟨trivial, trivial, sgLimC_one⟩, sgLimC_one⟩, trivial, sgLimC_one⟩
  | .phi c Y, h => ⟨⟨trivial, ⟨tjSLC_mono le_rfl le_rfl
        (fun x => (hle x).trans (he' ((taLe_We x).trans le_add_self))) hs,
      tjOwn_mono le_rfl le_rfl (.phi c Y) _ _ (fun _ _ hxy => he (taNode_mono _ a hxy))
        (fun _ _ hxy => he' ((add_le_add_iff_left _).2 (leWe_mono (taNode_mono _ a hxy))))
        (fun y => (hle _).trans (he' ((taLe_We _).trans le_add_self))) h⟩, sgLimC_one⟩, trivial, sgLimC_one⟩
  | .term P R c, h => ⟨⟨trivial, ⟨tjSLC_mono le_rfl le_rfl
        (fun x => (hle x).trans (he' ((taLe_We x).trans le_add_self))) hs,
      tjOwn_mono le_rfl le_rfl (.term P R c) _ _ (fun _ _ hxy => he (taNode_mono _ a hxy))
        (fun _ _ hxy => he' ((add_le_add_iff_left _).2 (leWe_mono (taNode_mono _ a hxy))))
        (fun y => (hle _).trans (he' ((taLe_We _).trans le_add_self))) h⟩, sgLimC_one⟩, trivial, sgLimC_one⟩

theorem tjTwW_own {b X0 : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e) {t0 : TaT}
    (h0 : TjOwn S b X0 (fun r => e (leWe r)) t0) : ∀ j, TjOwn S b X0 (fun r => e (leWe r)) (taTwW t0 j)
  | 0 => h0
  | j + 1 => ⟨trivial, tjOwn_mono le_rfl le_rfl _ _ _ (fun _ _ h => he (leWe_mono h))
      (fun _ _ h => he (leWe_mono ((add_le_add_iff_left _).2 (leWe_mono h))))
      (fun r => he (leWe_mono ((taLe_We r).trans le_add_self))) (tjTwW_own he h0 j), sgLimC_one⟩

theorem tjTwP_own {b X0 a' : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (hs : TjSLC S b X0 e a') {t0 : TaT}
    (h0 : TjOwn S b X0 (fun r => e (leWe r)) t0) : ∀ j, TjOwn S b X0 (fun r => e (leWe r)) (taTwP a' t0 j)
  | 0 => h0
  | j + 1 => by
    refine ⟨tjSLC_mono le_rfl le_rfl (fun x => he (taLe_We x)) hs, ?_⟩
    show TjOwn S b X0 (fun y => e (leWe (veblen a' (Om (1 + 1) + y)))) (taTwP a' t0 j)
    exact tjOwn_mono le_rfl le_rfl (taTwP a' t0 j) _ _ (fun _ _ h => he (leWe_mono h))
      (fun _ _ h => he (leWe_mono (taNode_mono _ a' h)))
      (fun r => he (leWe_mono (taLe_node _ a' r))) (tjTwP_own he hs h0 j)

/-! ## Values and images -/

section Val

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem tjOne : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC (leRho hl hX).1

theorem tjTh1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (tjOne hl hX).le

theorem tjOmS_val : taV taOmS = Om (1 + 1) + 1 ∧ tdIL S l taOmS = Om 1 + 1 := by
  have hΘ1 := tjTh1 hl hX
  show (0 + leWe (0 + leWe 0 * 1) * 1) + leWe 0 * 1 = _ ∧
    (0 + leOe (0 + leOe 0 * gxTh (upsilon l) (ldAtR S l) 1) * gxTh (upsilon l) (ldAtR S l) 1) +
      leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
  simp only [hΘ1, leWe_zero, leOe_zero, mul_one, zero_add, taLeWe_one, taLeOe_one]
  exact ⟨trivial, trivial⟩

theorem tjOmS_wf : TgWF S l taOmS := by
  have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (tjOne hl hX)
  have hW := gg_one_lt_of_SC ldOm2_SC
  exact ⟨⟨trivial, ⟨trivial, trivial, hc, le_rfl, hW⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩

/-- **The base term**: value `φ(a, Ω₂ + Q) + 1`, image `φ(Θ a, Ω₁ + Q̂) + 1`, well formed with code levels. -/
theorem tjBase_val {a : Ordinal.{0}} (hac : GxCl (upsilon l) (ldAtR S l) a) (ha1 : 1 ≤ a) (haW : a < Om (1 + 1)) :
    ∀ Q : TaT, TgWF S l Q →
    taV (taBase a Q) = veblen a (Om (1 + 1) + taV Q) + 1 ∧
    tdIL S l (taBase a Q) = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdIL S l Q) + 1 ∧
    TgWF S l (taBase a Q) := by
  have h1 := tjOne hl hX
  have hΘ1 := tjTh1 hl hX
  have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
  have hW := gg_one_lt_of_SC ldOm2_SC
  have hΘa : 1 ≤ gxTh (upsilon l) (ldAtR S l) a := tgTh_one h1.le ha1
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
  have hΘa0 : gxTh (upsilon l) (ldAtR S l) a ≠ 0 := (zero_lt_one.trans_le hΘa).ne'
  intro Q hQ
  cases Q with
  | zero =>
    obtain ⟨e1, e2⟩ := tjOmS_val hl hX
    refine ⟨?_, ?_, tjOmS_wf hl hX⟩
    · show taV taOmS = _
      rw [e1]; show _ = veblen a (Om (1 + 1) + 0) + 1
      rw [add_zero, ldOm2_SC.veblen_right haW]
    · show tdIL S l taOmS = _
      rw [e2]; show _ = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + 0) + 1
      rw [add_zero, Ph.ph_SC_Om1.veblen_right (Sn.snTh_lt_Om1 hl hX haW.le)]
  | phi b Y =>
    obtain ⟨hv, hi⟩ := tgV_pos h1.le (TaT.phi b Y) hQ (by simp)
    refine ⟨?_, ?_, ⟨⟨trivial, ⟨hac, ha1, haW, hQ, hv, hi⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩⟩
    · show 0 + leWe (veblen a (Om (1 + 1) + taV (.phi b Y))) * 1 + leWe 0 * 1 = _
      rw [mul_one, taWe_veb ha0 hv, zero_add, leWe_zero, mul_one]
    · show 0 + leOe (veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdIL S l (.phi b Y))) *
        gxTh (upsilon l) (ldAtR S l) 1 + leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      rw [hΘ1, mul_one, taOe_veb hΘa0 hi, zero_add, leOe_zero, mul_one]
  | term P R c =>
    obtain ⟨hv, hi⟩ := tgV_pos h1.le (TaT.term P R c) hQ (by simp)
    refine ⟨?_, ?_, ⟨⟨trivial, ⟨hac, ha1, haW, hQ, hv, hi⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩⟩
    · show 0 + leWe (veblen a (Om (1 + 1) + taV (.term P R c))) * 1 + leWe 0 * 1 = _
      rw [mul_one, taWe_veb ha0 hv, zero_add, leWe_zero, mul_one]
    · show 0 + leOe (veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdIL S l (.term P R c))) *
        gxTh (upsilon l) (ldAtR S l) 1 + leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      rw [hΘ1, mul_one, taOe_veb hΘa0 hi, zero_add, leOe_zero, mul_one]

theorem tjTwW_val (t0 : TaT) (j : ℕ) :
    taV (taTwW t0 (j + 1)) = ω ^ (Om (1 + 1) * taV (taTwW t0 j)) ∧
    tdIL S l (taTwW t0 (j + 1)) = ω ^ (Om 1 * tdIL S l (taTwW t0 j)) := by
  have hΘ1 := tjTh1 hl hX
  show 0 + leWe (taV (taTwW t0 j)) * 1 = _ ∧
    0 + leOe (tdIL S l (taTwW t0 j)) * gxTh (upsilon l) (ldAtR S l) 1 = _
  rw [hΘ1, mul_one, mul_one, zero_add, zero_add]
  exact ⟨rfl, rfl⟩

theorem tjTwW_wf {t0 : TaT} (ht0 : TgWF S l t0) : ∀ j, TgWF S l (taTwW t0 j)
  | 0 => ht0
  | j + 1 => ⟨trivial, tjTwW_wf ht0 j, GxCl.small (tjOne hl hX), le_rfl, gg_one_lt_of_SC ldOm2_SC⟩

omit hl hX in
theorem tjTwP_wf {a' : Ordinal.{0}} (hac : GxCl (upsilon l) (ldAtR S l) a') (ha1 : 1 ≤ a')
    (haW : a' < Om (1 + 1)) {t0 : TaT} (ht0 : TgWF S l t0) (hv0 : 1 ≤ taV t0) (hi0 : 1 ≤ tdIL S l t0) :
    ∀ j, TgWF S l (taTwP a' t0 j) ∧ 1 ≤ taV (taTwP a' t0 j) ∧ 1 ≤ tdIL S l (taTwP a' t0 j)
  | 0 => ⟨ht0, hv0, hi0⟩
  | j + 1 => by
    obtain ⟨hw, hv, hi⟩ := tjTwP_wf hac ha1 haW ht0 hv0 hi0 j
    exact ⟨⟨hac, ha1, haW, hw, hv, hi⟩, Order.one_le_iff_pos.2 veblen_pos, Order.one_le_iff_pos.2 veblen_pos⟩

/-- **THE MEMBERS AT A SUCCESSOR CODE LEVEL `a`** below `L = φ(a, Ω₂ + Q + 1)`: own wherever the parent node is
own (strong level condition of `a`), values cofinal in `L`, images cofinal in `L̂ = φ(Θ a, Ω₁ + Q̂ + 1)`. -/
theorem tjTw_family {a : Ordinal.{0}} (hac : GxCl (upsilon l) (ldAtR S l) a) (ha1 : 1 ≤ a)
    (haW : a < Om (1 + 1)) (hnl : ¬ IsSuccLimit a) (Q : TaT) (hQ : TgWF S l Q) :
    ∃ (ι : Type 1) (R : ι → TaT), (∀ i, TgWF S l (R i)) ∧
      (∀ i b X0 (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TjSLC S b X0 e a →
        TjOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TjOwn S b X0 (fun r => e (leWe r)) (R i)) ∧
      (∀ i, taV (R i) < veblen a (Om (1 + 1) + (taV Q + 1))) ∧
      (∀ x, x < veblen a (Om (1 + 1) + (taV Q + 1)) → ∃ i, x < taV (R i)) ∧
      (∀ i, tdIL S l (R i) < veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + (tdIL S l Q + 1))) ∧
      (∀ x, x < veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + (tdIL S l Q + 1)) → ∃ i, x < tdIL S l (R i)) := by
  obtain ⟨hv0, hi0, hw0⟩ := tjBase_val hl hX hac ha1 haW Q hQ
  rw [← add_assoc, ← add_assoc]
  have hv1 : 1 ≤ taV (taBase a Q) := hv0 ▸ le_add_self
  have hi1 : 1 ≤ tdIL S l (taBase a Q) := hi0 ▸ le_add_self
  have hz : Om (1 + 1) ≤ Om (1 + 1) + taV Q := le_self_add
  have hzh : Om 1 ≤ Om 1 + tdIL S l Q := le_self_add
  have hown0 : ∀ b X0 (e : Ordinal.{0} → Ordinal.{0}), Monotone e → TjSLC S b X0 e a →
      TjOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q →
      TjOwn S b X0 (fun r => e (leWe r)) (taBase a Q) :=
    fun b X0 e he hs h => tjBase_own he (fun _ _ h => he (leWe_mono h)) (fun x => he (taLe_We x)) hs Q h
  rcases zero_or_succ_or_isSuccLimit a with h0 | ⟨a', ha'⟩ | hlim
  · exact absurd (h0 ▸ ha1) (not_le.2 zero_lt_one)
  · rw [Order.succ_eq_add_one] at ha'
    subst ha'
    have ha'c : GxCl (upsilon l) (ldAtR S l) a' := rqCode_pred hl hX hac haW
    have hΘs : gxTh (upsilon l) (ldAtR S l) (a' + 1) = gxTh (upsilon l) (ldAtR S l) a' + 1 :=
      rqTh_succ hl hX ha'c
    rw [hΘs] at hi0 ⊢
    rcases eq_or_ne a' 0 with rfl | ha'0
    · have e1 : (0 : Ordinal.{0}) + 1 = 1 := zero_add 1
      have hΘ0 : gxTh (upsilon l) (ldAtR S l) 0 = 0 := gxTh_zero
      rw [hΘ0] at hi0 ⊢
      refine ⟨ULift ℕ, fun j => taTwW (taBase (0 + 1) Q) j.down, fun j => tjTwW_wf hl hX hw0 j.down,
        fun j b X0 e he _ h => tjTwW_own he (hown0 b X0 e he ‹_› h) j.down, ?_⟩
      have hW := taTwW_ord ldOm2_SC hz (fun j => taV (taTwW (taBase (0 + 1) Q) j))
        (by show taV (taBase (0 + 1) Q) = _; rw [hv0, e1]) (fun j => (tjTwW_val hl hX _ j).1)
      have hWh := taTwW_ord Ph.ph_SC_Om1 hzh (fun j => tdIL S l (taTwW (taBase (0 + 1) Q) j))
        (by show tdIL S l (taBase (0 + 1) Q) = _; rw [hi0, e1]) (fun j => (tjTwW_val hl hX _ j).2)
      simp only [e1] at hW hWh ⊢
      refine ⟨fun j => hW.1 j.down, fun x hx => ?_, fun j => hWh.1 j.down, fun x hx => ?_⟩
      · obtain ⟨j, hj⟩ := hW.2 x hx; exact ⟨⟨j⟩, hj⟩
      · obtain ⟨j, hj⟩ := hWh.2 x hx; exact ⟨⟨j⟩, hj⟩
    · have ha'1 : 1 ≤ a' := Order.one_le_iff_ne_zero.2 ha'0
      have ha'W : a' < Om (1 + 1) := (lt_add_one a').trans haW
      have hΘa'1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) a' := tgTh_one (tjOne hl hX).le ha'1
      refine ⟨ULift ℕ, fun j => taTwP a' (taBase (a' + 1) Q) j.down,
        fun j => (tjTwP_wf ha'c ha'1 ha'W hw0 hv1 hi1 j.down).1,
        fun j b X0 e he hs h => tjTwP_own he (tjSLC_le (lt_add_one a').le hs)
          (hown0 b X0 e he hs h) j.down, ?_⟩
      have hP := taTwP_ord (κ := Om (1 + 1)) (a' := a') hz (fun j => taV (taTwP a' (taBase (a' + 1) Q) j))
        hv0 (fun j => rfl)
      have hPh := taTwP_ord (κ := Om 1) (a' := gxTh (upsilon l) (ldAtR S l) a') hzh
        (fun j => tdIL S l (taTwP a' (taBase (a' + 1) Q) j)) hi0 (fun j => rfl)
      refine ⟨fun j => hP.1 j.down, fun x hx => ?_, fun j => hPh.1 j.down, fun x hx => ?_⟩
      · obtain ⟨j, hj⟩ := hP.2 x hx; exact ⟨⟨j⟩, hj⟩
      · obtain ⟨j, hj⟩ := hPh.2 x hx; exact ⟨⟨j⟩, hj⟩
  · exact absurd hlim hnl

omit hl hX in
/-- **The members at a limit code level are own** wherever the parent node is own. -/
theorem tjLim_own {a c' : Ordinal.{0}} (hc'a : c' ≤ a) {b X0 : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}}
    (he : Monotone e) (hs : TjSLC S b X0 e a) (Q : TaT)
    (hQo : TjOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q) :
    TjOwn S b X0 (fun r => e (leWe r)) (TaT.phi c' (taBase a Q)) := by
  refine ⟨tjSLC_mono le_rfl le_rfl (fun x => he (taLe_We x)) (tjSLC_le hc'a hs), ?_⟩
  exact tjBase_own he (fun _ _ h => he (leWe_mono (taNode_mono _ c' h)))
    (fun x => he ((taLe_node _ c' x).trans (taLe_We _))) hs Q hQo

end Val

/-! ## Hull elements through a context -/

section Cof

variable {l : Ordinal.{0}}

/-- **Hull elements below `K(L)` are below `K(x)` for a hull element `x < L`** (`L` a limit). -/
theorem tjCtx_cof : ∀ K : TaC, TgWFC S l K → ∀ L, IsSuccLimit L → ∀ y, y ∈ cdHull S l → y < taE K L →
    ∃ x, x ∈ cdHull S l ∧ x < L ∧ y < taE K x
  | .hole, _, L, hL, y, hy, hyL => ⟨y + 1, CSet.succ_mem hy, hL.add_one_lt hyL, lt_add_one y⟩
  | .pfx K Q, ⟨hKw, _⟩, L, hL, y, hy, hyL => by
    have hL' : IsSuccLimit (taV Q + L) := (isNormal_add_right (taV Q)).map_isSuccLimit hL
    obtain ⟨x', hx', hx'L, hyx'⟩ := tjCtx_cof K hKw (taV Q + L) hL' y hy hyL
    have h1L : (1 : Ordinal.{0}) < L := by
      have := hL.add_one_lt (pos_iff_ne_zero.2 hL.ne_bot); rwa [zero_add] at this
    rcases lt_or_ge x' (taV Q) with hlt | hge
    · exact ⟨1, CSet.one_mem _ _, h1L, hyx'.trans (taE_strictMono K (hlt.trans_le le_self_add))⟩
    · have e1 : taV Q + (x' - taV Q) = x' := Ordinal.add_sub_cancel_of_le hge
      have hsub : x' - taV Q < L := Ordinal.sub_lt_of_lt_add hx'L hL.bot_lt
      refine ⟨x' - taV Q + 1, CSet.succ_mem (taSub_mem _ hx' _), hL.add_one_lt hsub, hyx'.trans ?_⟩
      show taE K x' < taE K (taV Q + (x' - taV Q + 1))
      exact taE_strictMono K (by rw [← add_assoc, e1]; exact lt_add_one x')
  | .lft K, hKw, L, hL, y, hy, hyL => by
    have hL' : IsSuccLimit (leWe L) := taLim_We hL.bot_lt
    obtain ⟨x', hx', hx'L, hyx'⟩ := tjCtx_cof K hKw (leWe L) hL' y hy hyL
    have h1L : (1 : Ordinal.{0}) < L := by
      have := hL.add_one_lt (pos_iff_ne_zero.2 hL.ne_bot); rwa [zero_add] at this
    rcases eq_or_ne x' 0 with rfl | hx'0
    · exact ⟨1, CSet.one_mem _ _, h1L, hyx'.trans (taE_strictMono K (leWe_pos 1))⟩
    · have hlog : sgLW x' < L := by
        by_contra hc
        push Not at hc
        exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hx'0))) (not_le.2 hx'L)
      refine ⟨sgLW x' + 1, CSet.succ_mem (ldDivK_mem ldOm2_SC (leLog_mem hx')), hL.add_one_lt hlog,
        hyx'.trans (taE_strictMono K (sgLW_lt x'))⟩
  | .phi K a, ⟨hKw, _, ha1, _⟩, L, hL, y, hy, hyL => by
    have ha0 : a ≠ 0 := (zero_lt_one.trans_le ha1).ne'
    have hL' : IsSuccLimit (veblen a (Om (1 + 1) + L)) := taVeb_lim ha0
    obtain ⟨x', hx', hx'L, hyx'⟩ := tjCtx_cof K hKw _ hL' y hy hyL
    have h1L : (1 : Ordinal.{0}) < L := by
      have := hL.add_one_lt (pos_iff_ne_zero.2 hL.ne_bot); rwa [zero_add] at this
    have hone : ∀ u, u + 1 ≤ Om (1 + 1) + 1 → x' < veblen a (u + 1) →
        ∃ x, x ∈ cdHull S l ∧ x < L ∧ y < taE (TaC.phi K a) x := fun u hu hxu =>
      ⟨1, CSet.one_mem _ _, h1L, hyx'.trans (taE_strictMono K (hxu.trans_le ((veblen_le_veblen_iff_right).2 hu)))⟩
    rcases lt_or_ge x' (veblen a 0) with h0 | h0
    · exact hone 0 (by rw [zero_add]; exact le_add_self) (h0.trans_le ((veblen_le_veblen_iff_right).2 zero_le))
    obtain ⟨u, hu, hu1, hu2⟩ := tdHull_idx hx' h0
    rcases lt_or_ge u (Om (1 + 1)) with huW | huW
    · exact hone u ((Order.add_one_le_of_lt huW).trans le_self_add) hu2
    · have huL : u < Om (1 + 1) + L := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hx'L)
      have e1 : Om (1 + 1) + (u - Om (1 + 1)) = u := Ordinal.add_sub_cancel_of_le huW
      have hsub : u - Om (1 + 1) < L := Ordinal.sub_lt_of_lt_add huL hL.bot_lt
      refine ⟨u - Om (1 + 1) + 1, CSet.succ_mem (taSub_mem _ hu _), hL.add_one_lt hsub, hyx'.trans ?_⟩
      show taE K x' < taE K (veblen a (Om (1 + 1) + (u - Om (1 + 1) + 1)))
      rw [← add_assoc, e1]
      exact taE_strictMono K hu2

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Tj
