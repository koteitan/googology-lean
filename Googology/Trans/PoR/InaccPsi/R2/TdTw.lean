import Googology.Trans.PoR.InaccPsi.R2.TdCtx

/-!
# The members below a successor index `φ(a, Ω₂ + Q + 1)` for every level `a` below `K`

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `K = tdK S = ψ_{Ω₁}(Ω_ω)`,
`TdSm S a`: `1 ≤ a < K`.  The towers are those of `Ta` (`Ta.taTwW`, `Ta.taTwP`,
`Ta.taBase`); at a limit level the family `φ(a', Ω₂ + t₀)`, `1 ≤ a' < a`, all below `K`.

* `tdOmS_wf`, `tdV_pos`, `tdBase_val`, `tdTwW_wf`, `tdTwP_wf`;
* `tdTw_family` (**THE MEMBERS: well-formed terms `R_i`, own wherever `Q` is own below the node, values cofinal
  in `L = φ(a, Ω₂ + Q + 1)`, images cofinal in `L̂ = φ(a, Ω₁ + Q̂ + 1)`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-! ## Terms -/

/-! ## Values -/

section Val

variable {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l)

include h1

omit h1 in
theorem tdOmS_wf (h1 : (1 : Ordinal.{0}) < upsilon l) : TdWF S l taOmS := by
  have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
  have hW := gg_one_lt_of_SC ldOm2_SC
  exact ⟨⟨trivial, ⟨trivial, trivial, hc, le_rfl, hW⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩

/-- A nonzero well-formed term has value and image `≥ 1`. -/
theorem tdV_pos : ∀ Q : TaT, TdWF S l Q → Q ≠ TaT.zero → 1 ≤ taV Q ∧ 1 ≤ taI S l Q
  | .zero, _, h => absurd rfl h
  | .phi _ _, _, _ => ⟨Order.one_le_iff_pos.2 veblen_pos, Order.one_le_iff_pos.2 veblen_pos⟩
  | .term P R c, ⟨_, _, hc, hc1, _⟩, _ => by
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    have hΘc : 1 ≤ gxTh (upsilon l) (ldAtR S l) c := hΘ1 ▸ gxTh_mono hc1
    refine ⟨?_, ?_⟩
    · show 1 ≤ taV P + leWe (taV R) * c
      exact (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc1))).trans le_add_self
    · show 1 ≤ taI S l P + leOe (taI S l R) * gxTh (upsilon l) (ldAtR S l) c
      exact (Order.one_le_iff_pos.2 (mul_pos (leOe_pos _) (zero_lt_one.trans_le hΘc))).trans le_add_self

/-- **The base term**: value `φ(a, Ω₂ + Q) + 1`, image `φ(a, Ω₁ + Q̂) + 1`, well formed. -/
theorem tdBase_val {a : Ordinal.{0}} (ha : TdSm S a) : ∀ Q : TaT, TdWF S l Q →
    taV (taBase a Q) = veblen a (Om (1 + 1) + taV Q) + 1 ∧
    taI S l (taBase a Q) = veblen a (Om 1 + taI S l Q) + 1 ∧ TdWF S l (taBase a Q)
  | .zero, _ => by
    obtain ⟨e1, e2⟩ := taOmS_val (S := S) h1
    refine ⟨?_, ?_, tdOmS_wf h1⟩
    · show taV taOmS = _
      rw [e1]; show _ = veblen a (Om (1 + 1) + 0) + 1
      rw [add_zero, ldOm2_SC.veblen_right (tdSm_lt_Om2 ha)]
    · show taI S l taOmS = _
      rw [e2]; show _ = veblen a (Om 1 + 0) + 1
      rw [add_zero, Ph.ph_SC_Om1.veblen_right (tdSm_lt_Om1 ha)]
  | .phi b Y, hQ => by
    obtain ⟨hv, hi⟩ := tdV_pos h1 (TaT.phi b Y) hQ (by simp)
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
    have hW := gg_one_lt_of_SC ldOm2_SC
    refine ⟨?_, ?_, ⟨⟨trivial, ⟨ha, hQ, hv, hi⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩⟩
    · show 0 + leWe (veblen a (Om (1 + 1) + taV (.phi b Y))) * 1 + leWe 0 * 1 = _
      rw [mul_one, taWe_veb (tdSm_ne0 ha) hv, zero_add, leWe_zero, mul_one]
    · show 0 + leOe (veblen a (Om 1 + taI S l (.phi b Y))) * gxTh (upsilon l) (ldAtR S l) 1 +
        leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      rw [hΘ1, mul_one, taOe_veb (tdSm_ne0 ha) hi, zero_add, leOe_zero, mul_one]
  | .term P R c, hQ => by
    obtain ⟨hv, hi⟩ := tdV_pos h1 (TaT.term P R c) hQ (by simp)
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
    have hW := gg_one_lt_of_SC ldOm2_SC
    refine ⟨?_, ?_, ⟨⟨trivial, ⟨ha, hQ, hv, hi⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩⟩
    · show 0 + leWe (veblen a (Om (1 + 1) + taV (.term P R c))) * 1 + leWe 0 * 1 = _
      rw [mul_one, taWe_veb (tdSm_ne0 ha) hv, zero_add, leWe_zero, mul_one]
    · show 0 + leOe (veblen a (Om 1 + taI S l (.term P R c))) * gxTh (upsilon l) (ldAtR S l) 1 +
        leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      rw [hΘ1, mul_one, taOe_veb (tdSm_ne0 ha) hi, zero_add, leOe_zero, mul_one]

end Val

/-! ## The towers on values -/

/-! ## The towers on terms -/

section TwT

variable {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l)

theorem tdTwW_wf (h1 : (1 : Ordinal.{0}) < upsilon l) {t0 : TaT} (ht0 : TdWF S l t0) :
    ∀ j, TdWF S l (taTwW t0 j)
  | 0 => ht0
  | j + 1 => ⟨trivial, tdTwW_wf h1 ht0 j, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩

theorem tdTwP_wf {a' : Ordinal.{0}} (ha' : TdSm S a') {t0 : TaT} (ht0 : TdWF S l t0) (hv0 : 1 ≤ taV t0)
    (hi0 : 1 ≤ taI S l t0) : ∀ j, TdWF S l (taTwP a' t0 j) ∧ 1 ≤ taV (taTwP a' t0 j) ∧ 1 ≤ taI S l (taTwP a' t0 j)
  | 0 => ⟨ht0, hv0, hi0⟩
  | j + 1 => by
    obtain ⟨hw, hv, hi⟩ := tdTwP_wf ha' ht0 hv0 hi0 j
    exact ⟨⟨ha', hw, hv, hi⟩, Order.one_le_iff_pos.2 veblen_pos, Order.one_le_iff_pos.2 veblen_pos⟩

end TwT

/-- **THE MEMBERS below `L = φ(a, Ω₂ + Q + 1)`**: well-formed terms `R_i`, own wherever `Q` is own below the
node, values below `L` and cofinal in `L`, images below `L̂ = φ(a, Ω₁ + Q̂ + 1)` and cofinal in `L̂`. -/
theorem tdTw_family {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l) {a : Ordinal.{0}} (ha : TdSm S a)
    (Q : TaT) (hQ : TdWF S l Q) :
    ∃ (ι : Type 1) (R : ι → TaT), (∀ i, TdWF S l (R i)) ∧
      (∀ i b X0 (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
        TaOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TaOwn S b X0 (fun r => e (leWe r)) (R i)) ∧
      (∀ i, taV (R i) < veblen a (Om (1 + 1) + (taV Q + 1))) ∧
      (∀ x, x < veblen a (Om (1 + 1) + (taV Q + 1)) → ∃ i, x < taV (R i)) ∧
      (∀ i, taI S l (R i) < veblen a (Om 1 + (taI S l Q + 1))) ∧
      (∀ x, x < veblen a (Om 1 + (taI S l Q + 1)) → ∃ i, x < taI S l (R i)) := by
  obtain ⟨hv0, hi0, hw0⟩ := tdBase_val h1 ha Q hQ
  rw [← add_assoc, ← add_assoc]
  have hv1 : 1 ≤ taV (taBase a Q) := hv0 ▸ le_add_self
  have hi1 : 1 ≤ taI S l (taBase a Q) := hi0 ▸ le_add_self
  have hz : Om (1 + 1) ≤ Om (1 + 1) + taV Q := le_self_add
  have hzh : Om 1 ≤ Om 1 + taI S l Q := le_self_add
  have hown0 : ∀ b X0 (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
      TaOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TaOwn S b X0 (fun r => e (leWe r)) (taBase a Q) :=
    fun b X0 e he h => taBase_own he (fun _ _ h => he (leWe_mono h)) (fun x => he (taLe_We x)) Q h
  rcases zero_or_succ_or_isSuccLimit a with h0 | ⟨a', ha'⟩ | hlim
  · exact absurd h0 (tdSm_ne0 ha)
  · rw [Order.succ_eq_add_one] at ha'
    subst ha'
    rcases eq_or_ne a' 0 with rfl | ha'0
    · have e1 : (0 : Ordinal.{0}) + 1 = 1 := zero_add 1
      refine ⟨ULift ℕ, fun j => taTwW (taBase (0 + 1) Q) j.down, fun j => tdTwW_wf h1 hw0 j.down,
        fun j b X0 e he h => taTwW_own he (hown0 b X0 e he h) j.down, ?_⟩
      have hW := taTwW_ord ldOm2_SC hz (fun j => taV (taTwW (taBase (0 + 1) Q) j))
        (by show taV (taBase (0 + 1) Q) = _; rw [hv0, e1]) (fun j => (taTwW_val (S := S) _ j h1).1)
      have hWh := taTwW_ord Ph.ph_SC_Om1 hzh (fun j => taI S l (taTwW (taBase (0 + 1) Q) j))
        (by show taI S l (taBase (0 + 1) Q) = _; rw [hi0, e1]) (fun j => (taTwW_val _ j h1).2)
      simp only [e1] at hW hWh ⊢
      refine ⟨fun j => hW.1 j.down, fun x hx => ?_, fun j => hWh.1 j.down, fun x hx => ?_⟩
      · obtain ⟨j, hj⟩ := hW.2 x hx; exact ⟨⟨j⟩, hj⟩
      · obtain ⟨j, hj⟩ := hWh.2 x hx; exact ⟨⟨j⟩, hj⟩
    · have ha's : TdSm S a' := ⟨Order.one_le_iff_ne_zero.2 ha'0, (lt_add_one a').trans ha.2⟩
      refine ⟨ULift ℕ, fun j => taTwP a' (taBase (a' + 1) Q) j.down, fun j => (tdTwP_wf ha's hw0 hv1 hi1 j.down).1,
        fun j b X0 e he h => taTwP_own he (hown0 b X0 e he h) j.down, ?_⟩
      have hP := taTwP_ord (κ := Om (1 + 1)) (a' := a') hz (fun j => taV (taTwP a' (taBase (a' + 1) Q) j))
        hv0 (fun j => rfl)
      have hPh := taTwP_ord (κ := Om 1) (a' := a') hzh (fun j => taI S l (taTwP a' (taBase (a' + 1) Q) j))
        hi0 (fun j => rfl)
      refine ⟨fun j => hP.1 j.down, fun x hx => ?_, fun j => hPh.1 j.down, fun x hx => ?_⟩
      · obtain ⟨j, hj⟩ := hP.2 x hx; exact ⟨⟨j⟩, hj⟩
      · obtain ⟨j, hj⟩ := hPh.2 x hx; exact ⟨⟨j⟩, hj⟩
  · have h1a : 1 < a := by
      have := hlim.add_one_lt (pos_iff_ne_zero.2 hlim.ne_bot); rwa [zero_add] at this
    refine ⟨{a' : Ordinal.{0} // TdSm S a' ∧ a' < a}, fun i => TaT.phi i.1 (taBase a Q),
      fun i => ⟨i.2.1, hw0, hv1, hi1⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro i b X0 e he h
      show TaOwn S b X0 (fun y => e (leWe (veblen i.1 (Om (1 + 1) + y)))) (taBase a Q)
      exact taBase_own he (fun _ _ hxy => he (leWe_mono (taNode_mono _ i.1 hxy)))
        (fun x => he ((taLe_node _ i.1 x).trans (taLe_We _))) Q h
    · intro i
      show veblen i.1 (Om (1 + 1) + taV (taBase a Q)) < _
      rw [hv0]
      exact taVeb_lim_lt (tdSm_ne0 ha) i.2.2 ((hz.trans_lt (lt_add_one _)).trans_le (right_le_veblen a _))
    · intro x hx
      obtain ⟨a', ha', hxa⟩ := taVeb_lim_cof hlim hx
      refine ⟨⟨max a' 1, ⟨le_max_right _ _, (max_lt ha' h1a).trans ha.2⟩, max_lt ha' h1a⟩, ?_⟩
      show x < veblen (max a' 1) (Om (1 + 1) + taV (taBase a Q))
      rw [hv0]
      exact hxa.trans_le ((veblen_left_monotone _ (le_max_left _ _)).trans
        ((veblen_le_veblen_iff_right).2 le_add_self))
    · intro i
      show veblen i.1 (Om 1 + taI S l (taBase a Q)) < _
      rw [hi0]
      exact taVeb_lim_lt (tdSm_ne0 ha) i.2.2 ((hzh.trans_lt (lt_add_one _)).trans_le (right_le_veblen a _))
    · intro x hx
      obtain ⟨a', ha', hxa⟩ := taVeb_lim_cof hlim hx
      refine ⟨⟨max a' 1, ⟨le_max_right _ _, (max_lt ha' h1a).trans ha.2⟩, max_lt ha' h1a⟩, ?_⟩
      show x < veblen (max a' 1) (Om 1 + taI S l (taBase a Q))
      rw [hi0]
      exact hxa.trans_le ((veblen_left_monotone _ (le_max_left _ _)).trans
        ((veblen_le_veblen_iff_right).2 le_add_self))

end Googology.Trans.PoR.InaccPsi.R2.Td
