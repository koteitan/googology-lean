import Googology.Trans.PoR.InaccPsi.R2.TaDer

/-!
# The members below a successor index `φ(a, Ω₂ + Q + 1)`: towers and the levels below a limit level

`W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `TaSm a`: `1 ≤ a < Γ₀`, `t₀ = φ(a, Ω₂ + Q) + 1`.

`L = φ(a, Ω₂ + Q + 1)` is the limit of
* `a = 1`: the tower `t_{j+1} = W^{t_j}` (`taTwW`);
* `a = a' + 1`, `a' ≥ 1`: the tower `t_{j+1} = φ(a', Ω₂ + t_j)` (`taTwP`);
* `a` a limit: the family `φ(a', Ω₂ + t₀)`, `1 ≤ a' < a` (no `ω`-sequence is needed: `Ta.TaDer.flim`).

* `taOmS` (the term `Ω₂ + 1`), `taBase` (**the base term `t₀`**, value `φ(a, Ω₂ + Q) + 1`, also for `Q = 0`), its
  value, image, well-formedness and own predicate;
* `taOpow_lt`, `taTwW_ord`, `taTwP_ord` (**the towers stay below `L` and are cofinal in `L`**, at any strongly
  critical `κ`, so for the values and the images);
* `taTw_family` (**THE MEMBERS: a family of well-formed terms `R_i`, own wherever `Q` is own below the node, with
  values below `L` cofinal in `L` and images below `L̂ = φ(a, Ω₁ + Q̂ + 1)` cofinal in `L̂`**).

No new axiom.  New definitions: `taOmS`, `taBase`, `taTwW`, `taTwP`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-! ## Terms -/

/-- The term `Ω₂ + 1`. -/
def taOmS : TaT := .term (.term .zero (.term .zero .zero 1) 1) .zero 1

/-- **The base term `t₀`** of the members below `φ(a, Ω₂ + Q + 1)`: value `φ(a, Ω₂ + Q) + 1`. -/
def taBase (a : Ordinal.{0}) : TaT → TaT
  | .zero => taOmS
  | .phi b Y => .term (.term .zero (.phi a (.phi b Y)) 1) .zero 1
  | .term P R c => .term (.term .zero (.phi a (.term P R c)) 1) .zero 1

/-- The tower `t_{j+1} = W^{t_j}`. -/
def taTwW (t0 : TaT) : ℕ → TaT
  | 0 => t0
  | j + 1 => .term .zero (taTwW t0 j) 1

/-- The tower `t_{j+1} = φ(a', Ω₂ + t_j)`. -/
def taTwP (a' : Ordinal.{0}) (t0 : TaT) : ℕ → TaT
  | 0 => t0
  | j + 1 => .phi a' (taTwP a' t0 j)

theorem taLeOe_one : leOe 1 = Om 1 := by unfold leOe; rw [mul_one, gg_SC_eps Ph.ph_SC_Om1]

theorem taLeWe_one : leWe 1 = Om (1 + 1) := by unfold leWe; rw [mul_one, gg_SC_eps ldOm2_SC]

/-! ## Values -/

section Val

variable {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l)

include h1

theorem taOmS_val : taV taOmS = Om (1 + 1) + 1 ∧ taI S l taOmS = Om 1 + 1 := by
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
  show (0 + leWe (0 + leWe 0 * 1) * 1) + leWe 0 * 1 = _ ∧
    (0 + leOe (0 + leOe 0 * gxTh (upsilon l) (ldAtR S l) 1) * gxTh (upsilon l) (ldAtR S l) 1) +
      leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
  simp only [hΘ1, leWe_zero, leOe_zero, mul_one, zero_add, taLeWe_one, taLeOe_one]
  exact ⟨trivial, trivial⟩

omit h1 in
theorem taOmS_wf (h1 : (1 : Ordinal.{0}) < upsilon l) : TaWF S l taOmS := by
  have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
  have hW := gg_one_lt_of_SC ldOm2_SC
  exact ⟨⟨trivial, ⟨trivial, trivial, hc, le_rfl, hW⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩

/-- A nonzero well-formed term has value and image `≥ 1`. -/
theorem taV_pos : ∀ Q : TaT, TaWF S l Q → Q ≠ TaT.zero → 1 ≤ taV Q ∧ 1 ≤ taI S l Q
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
theorem taBase_val {a : Ordinal.{0}} (ha : TaSm a) : ∀ Q : TaT, TaWF S l Q →
    taV (taBase a Q) = veblen a (Om (1 + 1) + taV Q) + 1 ∧
    taI S l (taBase a Q) = veblen a (Om 1 + taI S l Q) + 1 ∧ TaWF S l (taBase a Q)
  | .zero, _ => by
    obtain ⟨e1, e2⟩ := taOmS_val (S := S) h1
    refine ⟨?_, ?_, taOmS_wf h1⟩
    · show taV taOmS = _
      rw [e1]; show _ = veblen a (Om (1 + 1) + 0) + 1
      rw [add_zero, ldOm2_SC.veblen_right (taSm_lt_Om2 ha)]
    · show taI S l taOmS = _
      rw [e2]; show _ = veblen a (Om 1 + 0) + 1
      rw [add_zero, Ph.ph_SC_Om1.veblen_right (taSm_lt_Om1 ha)]
  | .phi b Y, hQ => by
    obtain ⟨hv, hi⟩ := taV_pos h1 (TaT.phi b Y) hQ (by simp)
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
    have hW := gg_one_lt_of_SC ldOm2_SC
    refine ⟨?_, ?_, ⟨⟨trivial, ⟨ha, hQ, hv, hi⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩⟩
    · show 0 + leWe (veblen a (Om (1 + 1) + taV (.phi b Y))) * 1 + leWe 0 * 1 = _
      rw [mul_one, taWe_veb (taSm_ne0 ha) hv, zero_add, leWe_zero, mul_one]
    · show 0 + leOe (veblen a (Om 1 + taI S l (.phi b Y))) * gxTh (upsilon l) (ldAtR S l) 1 +
        leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      rw [hΘ1, mul_one, taOe_veb (taSm_ne0 ha) hi, zero_add, leOe_zero, mul_one]
  | .term P R c, hQ => by
    obtain ⟨hv, hi⟩ := taV_pos h1 (TaT.term P R c) hQ (by simp)
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
    have hW := gg_one_lt_of_SC ldOm2_SC
    refine ⟨?_, ?_, ⟨⟨trivial, ⟨ha, hQ, hv, hi⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩⟩
    · show 0 + leWe (veblen a (Om (1 + 1) + taV (.term P R c))) * 1 + leWe 0 * 1 = _
      rw [mul_one, taWe_veb (taSm_ne0 ha) hv, zero_add, leWe_zero, mul_one]
    · show 0 + leOe (veblen a (Om 1 + taI S l (.term P R c))) * gxTh (upsilon l) (ldAtR S l) 1 +
        leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      rw [hΘ1, mul_one, taOe_veb (taSm_ne0 ha) hi, zero_add, leOe_zero, mul_one]

end Val

/-! ## The towers on values -/

/-- `ω^{κ·x} < L` for `x < L`, `κ < L`, `L = φ(a, w)`, `a ≠ 0`. -/
theorem taOpow_lt {κ a w x : Ordinal.{0}} (hκ : SC κ) (ha : a ≠ 0) (hκL : κ < veblen a w)
    (hx : x < veblen a w) : ω ^ (κ * x) < veblen a w := by
  have hE : ω ^ veblen a w = veblen a w := gg_veblen_eps ha
  have hp := Ph.ph_veblen_prin a w
  have hk : κ * x < veblen a w := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [mul_zero]; exact veblen_pos
    have hlt : κ * x ≤ ω ^ (κ + x) := by
      rw [opow_add, gg_SC_eps hκ]
      exact mul_le_mul_right (right_le_opow x one_lt_omega0) _
    refine hlt.trans_lt ?_
    conv_rhs => rw [← hE]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (hp hκL hx)
  conv_rhs => rw [← hE]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 hk

/-- **The tower `t_{j+1} = ω^{κ·t_j}` from `φ(1, z) + 1`** stays below `φ(1, z+1)` and is cofinal in it. -/
theorem taTwW_ord {κ z : Ordinal.{0}} (hκ : SC κ) (hκz : κ ≤ z) (u : ℕ → Ordinal.{0})
    (hu0 : u 0 = veblen 1 z + 1) (hus : ∀ j, u (j + 1) = ω ^ (κ * u j)) :
    (∀ j, u j < veblen 1 (z + 1)) ∧ ∀ x, x < veblen 1 (z + 1) → ∃ j, x < u j := by
  have hκL : κ < veblen 1 (z + 1) := (hκz.trans_lt (lt_add_one z)).trans_le (right_le_veblen 1 _)
  refine ⟨fun j => ?_, fun x hx => ?_⟩
  · induction j with
    | zero => rw [hu0]; exact (taVeb_lim one_ne_zero).add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one z))
    | succ j ih => rw [hus]; exact taOpow_lt hκ one_ne_zero hκL ih
  · have e := taVeb_succ 0 z
    rw [zero_add] at e
    rw [e] at hx
    refine taTw_cof (f := veblen 0) (g := fun t => ω ^ (κ * t)) (veblen_right_strictMono 0).monotone
      (fun t => ?_) hx u (by rw [hu0]) hus
    rw [veblen_zero_apply]
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right t hκ.1)

/-- **The tower `t_{j+1} = φ(a', κ + t_j)` from `φ(a'+1, z) + 1`** stays below `φ(a'+1, z+1)` and is cofinal. -/
theorem taTwP_ord {κ a' z : Ordinal.{0}} (hκz : κ ≤ z) (u : ℕ → Ordinal.{0})
    (hu0 : u 0 = veblen (a' + 1) z + 1) (hus : ∀ j, u (j + 1) = veblen a' (κ + u j)) :
    (∀ j, u j < veblen (a' + 1) (z + 1)) ∧ ∀ x, x < veblen (a' + 1) (z + 1) → ∃ j, x < u j := by
  have ha0 : a' + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have hκL : κ < veblen (a' + 1) (z + 1) := (hκz.trans_lt (lt_add_one z)).trans_le (right_le_veblen _ _)
  refine ⟨fun j => ?_, fun x hx => ?_⟩
  · induction j with
    | zero => rw [hu0]; exact (taVeb_lim ha0).add_one_lt ((veblen_lt_veblen_iff_right).2 (lt_add_one z))
    | succ j ih =>
      rw [hus]
      calc veblen a' (κ + u j) < veblen a' (veblen (a' + 1) (z + 1)) :=
            (veblen_lt_veblen_iff_right).2 (Ph.ph_veblen_prin _ _ hκL ih)
        _ = veblen (a' + 1) (z + 1) := veblen_veblen_of_lt (lt_add_one a') _
  · rw [taVeb_succ a' z] at hx
    exact taTw_cof (f := veblen a') (g := fun t => veblen a' (κ + t)) (veblen_right_strictMono a').monotone
      (fun t => (veblen_le_veblen_iff_right).2 le_add_self) hx u (by rw [hu0]) hus

/-! ## The towers on terms -/

section TwT

variable {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l)

theorem taTwW_val (t0 : TaT) (j : ℕ) (h1 : (1 : Ordinal.{0}) < upsilon l) :
    taV (taTwW t0 (j + 1)) = ω ^ (Om (1 + 1) * taV (taTwW t0 j)) ∧
    taI S l (taTwW t0 (j + 1)) = ω ^ (Om 1 * taI S l (taTwW t0 j)) := by
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
  show 0 + leWe (taV (taTwW t0 j)) * 1 = _ ∧
    0 + leOe (taI S l (taTwW t0 j)) * gxTh (upsilon l) (ldAtR S l) 1 = _
  rw [hΘ1, mul_one, mul_one, zero_add, zero_add]
  exact ⟨rfl, rfl⟩

theorem taTwW_wf (h1 : (1 : Ordinal.{0}) < upsilon l) {t0 : TaT} (ht0 : TaWF S l t0) :
    ∀ j, TaWF S l (taTwW t0 j)
  | 0 => ht0
  | j + 1 => ⟨trivial, taTwW_wf h1 ht0 j, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩

theorem taTwP_wf {a' : Ordinal.{0}} (ha' : TaSm a') {t0 : TaT} (ht0 : TaWF S l t0) (hv0 : 1 ≤ taV t0)
    (hi0 : 1 ≤ taI S l t0) : ∀ j, TaWF S l (taTwP a' t0 j) ∧ 1 ≤ taV (taTwP a' t0 j) ∧ 1 ≤ taI S l (taTwP a' t0 j)
  | 0 => ⟨ht0, hv0, hi0⟩
  | j + 1 => by
    obtain ⟨hw, hv, hi⟩ := taTwP_wf ha' ht0 hv0 hi0 j
    exact ⟨⟨ha', hw, hv, hi⟩, Order.one_le_iff_pos.2 veblen_pos, Order.one_le_iff_pos.2 veblen_pos⟩

end TwT

/-- The base term is own wherever `Q` is own below the node. -/
theorem taBase_own {b X0 a : Ordinal.{0}} {e e' : Ordinal.{0} → Ordinal.{0}} (he : Monotone e)
    (he' : Monotone e') (hle : ∀ x, e x ≤ e' x) :
    ∀ Q : TaT, TaOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TaOwn S b X0 e' (taBase a Q)
  | .zero, _ => ⟨⟨trivial, ⟨trivial, trivial, sgLimC_one⟩, sgLimC_one⟩, trivial, sgLimC_one⟩
  | .phi c Y, h => ⟨⟨trivial, taOwn_mono le_rfl le_rfl (.phi c Y) _ _
      (fun _ _ hxy => he (taNode_mono _ a hxy))
      (fun _ _ hxy => he' ((add_le_add_iff_left _).2 (leWe_mono (taNode_mono _ a hxy))))
      (fun y => (hle _).trans (he' ((taLe_We _).trans le_add_self))) h, sgLimC_one⟩, trivial, sgLimC_one⟩
  | .term P R c, h => ⟨⟨trivial, taOwn_mono le_rfl le_rfl (.term P R c) _ _
      (fun _ _ hxy => he (taNode_mono _ a hxy))
      (fun _ _ hxy => he' ((add_le_add_iff_left _).2 (leWe_mono (taNode_mono _ a hxy))))
      (fun y => (hle _).trans (he' ((taLe_We _).trans le_add_self))) h, sgLimC_one⟩, trivial, sgLimC_one⟩

theorem taTwW_own {b X0 : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e) {t0 : TaT}
    (h0 : TaOwn S b X0 (fun r => e (leWe r)) t0) : ∀ j, TaOwn S b X0 (fun r => e (leWe r)) (taTwW t0 j)
  | 0 => h0
  | j + 1 => ⟨trivial, taOwn_mono le_rfl le_rfl _ _ _ (fun _ _ h => he (leWe_mono h))
      (fun _ _ h => he (leWe_mono ((add_le_add_iff_left _).2 (leWe_mono h))))
      (fun r => he (leWe_mono ((taLe_We r).trans le_add_self))) (taTwW_own he h0 j), sgLimC_one⟩

theorem taTwP_own {b X0 a' : Ordinal.{0}} {e : Ordinal.{0} → Ordinal.{0}} (he : Monotone e) {t0 : TaT}
    (h0 : TaOwn S b X0 (fun r => e (leWe r)) t0) : ∀ j, TaOwn S b X0 (fun r => e (leWe r)) (taTwP a' t0 j)
  | 0 => h0
  | j + 1 => by
    show TaOwn S b X0 (fun y => e (leWe (veblen a' (Om (1 + 1) + y)))) (taTwP a' t0 j)
    exact taOwn_mono le_rfl le_rfl (taTwP a' t0 j) _ _ (fun _ _ h => he (leWe_mono h))
      (fun _ _ h => he (leWe_mono (taNode_mono _ a' h)))
      (fun r => he (leWe_mono (taLe_node _ a' r))) (taTwP_own he h0 j)

/-- **THE MEMBERS below `L = φ(a, Ω₂ + Q + 1)`**: well-formed terms `R_i`, own wherever `Q` is own below the
node, values below `L` and cofinal in `L`, images below `L̂ = φ(a, Ω₁ + Q̂ + 1)` and cofinal in `L̂`. -/
theorem taTw_family {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l) {a : Ordinal.{0}} (ha : TaSm a)
    (Q : TaT) (hQ : TaWF S l Q) :
    ∃ (ι : Type 1) (R : ι → TaT), (∀ i, TaWF S l (R i)) ∧
      (∀ i b X0 (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
        TaOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TaOwn S b X0 (fun r => e (leWe r)) (R i)) ∧
      (∀ i, taV (R i) < veblen a (Om (1 + 1) + (taV Q + 1))) ∧
      (∀ x, x < veblen a (Om (1 + 1) + (taV Q + 1)) → ∃ i, x < taV (R i)) ∧
      (∀ i, taI S l (R i) < veblen a (Om 1 + (taI S l Q + 1))) ∧
      (∀ x, x < veblen a (Om 1 + (taI S l Q + 1)) → ∃ i, x < taI S l (R i)) := by
  obtain ⟨hv0, hi0, hw0⟩ := taBase_val h1 ha Q hQ
  rw [← add_assoc, ← add_assoc]
  have hv1 : 1 ≤ taV (taBase a Q) := hv0 ▸ le_add_self
  have hi1 : 1 ≤ taI S l (taBase a Q) := hi0 ▸ le_add_self
  have hz : Om (1 + 1) ≤ Om (1 + 1) + taV Q := le_self_add
  have hzh : Om 1 ≤ Om 1 + taI S l Q := le_self_add
  have hown0 : ∀ b X0 (e : Ordinal.{0} → Ordinal.{0}), Monotone e →
      TaOwn S b X0 (fun y => e (veblen a (Om (1 + 1) + y))) Q → TaOwn S b X0 (fun r => e (leWe r)) (taBase a Q) :=
    fun b X0 e he h => taBase_own he (fun _ _ h => he (leWe_mono h)) (fun x => he (taLe_We x)) Q h
  rcases zero_or_succ_or_isSuccLimit a with h0 | ⟨a', ha'⟩ | hlim
  · exact absurd h0 (taSm_ne0 ha)
  · rw [Order.succ_eq_add_one] at ha'
    subst ha'
    rcases eq_or_ne a' 0 with rfl | ha'0
    · have e1 : (0 : Ordinal.{0}) + 1 = 1 := zero_add 1
      refine ⟨ULift ℕ, fun j => taTwW (taBase (0 + 1) Q) j.down, fun j => taTwW_wf h1 hw0 j.down,
        fun j b X0 e he h => taTwW_own he (hown0 b X0 e he h) j.down, ?_⟩
      have hW := taTwW_ord ldOm2_SC hz (fun j => taV (taTwW (taBase (0 + 1) Q) j))
        (by show taV (taBase (0 + 1) Q) = _; rw [hv0, e1]) (fun j => (taTwW_val (S := S) _ j h1).1)
      have hWh := taTwW_ord Ph.ph_SC_Om1 hzh (fun j => taI S l (taTwW (taBase (0 + 1) Q) j))
        (by show taI S l (taBase (0 + 1) Q) = _; rw [hi0, e1]) (fun j => (taTwW_val _ j h1).2)
      simp only [e1] at hW hWh ⊢
      refine ⟨fun j => hW.1 j.down, fun x hx => ?_, fun j => hWh.1 j.down, fun x hx => ?_⟩
      · obtain ⟨j, hj⟩ := hW.2 x hx; exact ⟨⟨j⟩, hj⟩
      · obtain ⟨j, hj⟩ := hWh.2 x hx; exact ⟨⟨j⟩, hj⟩
    · have ha's : TaSm a' := ⟨Order.one_le_iff_ne_zero.2 ha'0, (lt_add_one a').trans ha.2⟩
      refine ⟨ULift ℕ, fun j => taTwP a' (taBase (a' + 1) Q) j.down, fun j => (taTwP_wf ha's hw0 hv1 hi1 j.down).1,
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
    refine ⟨{a' : Ordinal.{0} // TaSm a' ∧ a' < a}, fun i => TaT.phi i.1 (taBase a Q),
      fun i => ⟨i.2.1, hw0, hv1, hi1⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro i b X0 e he h
      show TaOwn S b X0 (fun y => e (leWe (veblen i.1 (Om (1 + 1) + y)))) (taBase a Q)
      exact taBase_own he (fun _ _ hxy => he (leWe_mono (taNode_mono _ i.1 hxy)))
        (fun x => he ((taLe_node _ i.1 x).trans (taLe_We _))) Q h
    · intro i
      show veblen i.1 (Om (1 + 1) + taV (taBase a Q)) < _
      rw [hv0]
      exact taVeb_lim_lt (taSm_ne0 ha) i.2.2 ((hz.trans_lt (lt_add_one _)).trans_le (right_le_veblen a _))
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
      exact taVeb_lim_lt (taSm_ne0 ha) i.2.2 ((hzh.trans_lt (lt_add_one _)).trans_le (right_le_veblen a _))
    · intro x hx
      obtain ⟨a', ha', hxa⟩ := taVeb_lim_cof hlim hx
      refine ⟨⟨max a' 1, ⟨le_max_right _ _, (max_lt ha' h1a).trans ha.2⟩, max_lt ha' h1a⟩, ?_⟩
      show x < veblen (max a' 1) (Om 1 + taI S l (taBase a Q))
      rw [hi0]
      exact hxa.trans_le ((veblen_left_monotone _ (le_max_left _ _)).trans
        ((veblen_le_veblen_iff_right).2 le_add_self))

end Googology.Trans.PoR.InaccPsi.R2.Ta
