import Googology.Trans.PoR.InaccPsi.R2.SgGen

/-!
# Every exponent below `ε_{Ω₂+1}` is derived: the normal-form term and the image `Θ̂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `ε_{Ω₂+1} = φ(1, Ω₂ + 1)`.

* `sgLW` (`log_W E = log_ω E / Ω₂`), `sgLW_le` (`W^{log_W E} ≤ E`), `sgLW_lt` (`E < W^{log_W E + 1}`),
  `sgLW_lt_self` (**`log_W E < E` for `1 ≤ E < ε_{Ω₂+1}`**);
* `sgTmH` (**the normal-form term of `E`**: `W^e·q + r` with `e = log_W E`, `q = E / W^e`, `r = E mod W^e`),
  `sgThH` (**`Θ̂ E`, the image of the normal-form term**: `Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`, `Ω₂ ↦ Ω₁`, codes
  read by `Θ`), `sgTmH_spec` (**every `E ∈ H_λ`, `E < ε_{Ω₂+1}`, is the value of its well-formed normal-form
  term**: the digits are codes by `ldDivK_mem`, `leDivOp_mem`, `leModP_mem`), `sgThH_cnf`, `sgThH_code`
  (`Θ̂ E = Θ E` for codes);
* `sgDer_all` (**every `E ∈ H_λ` with `1 ≤ E < ε_{Ω₂+1}` is derived**, image `Θ̂ E`, own predicate the own
  predicate of its normal-form term), `sgLev_all` (**THE TOP LAW AT EVERY EXPONENT BELOW `ε_{Ω₂+1}`**:
  `Θ(ψ_{Ω₂}(β + W^{X₀ + W^E})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Θ̂ E}})` at every base `β ≥ b` of `Ro.RoBaseE` with a
  reading `Θ(ψ_{Ω₂} β) = ψ_{Ω₁} Â`, for every offset `Rv.RvOff b X₀ X̂₀` with `W^E ∣ X₀` and the size bounds,
  whenever `SgOwn b X₀ id (sgTmH E)` holds).

No new axiom.  New definitions: `sgLW`, `sgTmH`, `sgThH`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc

/-- `log_W E = log_ω E / Ω₂`. -/
noncomputable def sgLW (E : Ordinal.{0}) : Ordinal.{0} := log ω E / Om (1 + 1)

theorem sgLW_le {E : Ordinal.{0}} (hE : 0 < E) : leWe (sgLW E) ≤ E :=
  (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hE.ne')

theorem sgLW_lt (E : Ordinal.{0}) : E < leWe (sgLW E + 1) := by
  have h1 := lt_opow_succ_log_self one_lt_omega0 E
  rw [Order.succ_eq_add_one] at h1
  refine h1.trans_le (opow_le_opow_right omega0_pos ?_)
  rw [sgLW, mul_add_one]
  exact Order.add_one_le_of_lt (Ordinal.lt_mul_div_add _ ldOm2_SC.1.ne')

/-- **`log_W E < E` below `ε_{Ω₂+1}`.** -/
theorem sgLW_lt_self {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) : sgLW E < E := by
  have hE0 : 0 < E := zero_lt_one.trans_le hE1
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  by_contra h
  push Not at h
  have hle : sgLW E ≤ E :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω E)
  have heq : sgLW E = E := le_antisymm hle h
  have hWE : leWe E ≤ E := by have h0 := sgLW_le hE0; rwa [heq] at h0
  have h2 : E ≤ Om (1 + 1) * E := Ordinal.le_mul_right E ldOm2_SC.1
  have h3 : Om (1 + 1) * E ≤ leWe E := right_le_opow _ one_lt_omega0
  have hm : Om (1 + 1) * E = E := le_antisymm (h3.trans hWE) h2
  have hfix : ω ^ E = E := by
    refine le_antisymm ?_ (right_le_opow _ one_lt_omega0)
    calc ω ^ E = leWe E := by unfold leWe; rw [hm]
      _ ≤ E := hWE
  have hΩE : Om (1 + 1) < E := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · calc Om (1 + 1) = Om (1 + 1) * 1 := (mul_one _).symm
        _ ≤ Om (1 + 1) * E := mul_le_mul_right hE1 _
        _ = E := hm
    · have : Om (1 + 1) * 1 < Om (1 + 1) * Om (1 + 1) := (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hW1
      rw [mul_one, e] at this
      rw [e] at hm
      rw [hm] at this
      exact lt_irrefl _ this
  obtain ⟨a, rfl⟩ := (mem_range_veblen one_ne_zero).2 (fun b hb => by
    rw [Order.lt_one_iff] at hb; subst hb; rw [veblen_zero_apply]; exact hfix)
  have ha : a < Om (1 + 1) + 1 := (veblen_right_strictMono 1).lt_iff_lt.1 hE
  have h4 : veblen 1 a ≤ veblen 1 (Om (1 + 1)) :=
    (veblen_right_strictMono 1).monotone (Order.le_of_lt_add_one ha)
  rw [ldOm2_SC.veblen_right hW1] at h4
  exact absurd (hΩE.trans_le h4) (lt_irrefl _)

/-- **The normal-form term of `E`**: `W^e·q + r`, `e = log_W E`, `q = E / W^e`, `r = E mod W^e`. -/
noncomputable def sgTmH (E : Ordinal.{0}) : SgT :=
  if h : 0 < E ∧ sgLW E < E then
    sgCat (SgT.term SgT.zero (sgTmH (sgLW E)) (E / leWe (sgLW E))) (sgTmH (E % leWe (sgLW E)))
  else SgT.zero
termination_by E
decreasing_by
  · exact h.2
  · exact (Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le h.1)

/-- **`Θ̂ E`**: the image of the normal-form term (`Ω₂ ↦ Ω₁`, codes read by `Θ`). -/
noncomputable def sgThH (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} := sgI S l (sgTmH E)

variable {S : InaccSeq.{0}}

theorem sgTmH_zero : sgTmH 0 = SgT.zero := by
  rw [sgTmH, dif_neg (fun h => lt_irrefl _ h.1)]

theorem sgTmH_eq {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    sgTmH E = sgCat (SgT.term SgT.zero (sgTmH (sgLW E)) (E / leWe (sgLW E))) (sgTmH (E % leWe (sgLW E))) := by
  rw [sgTmH, dif_pos ⟨zero_lt_one.trans_le hE1, sgLW_lt_self hE1 hE⟩]

/-- **`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`.** -/
theorem sgThH_cnf (l : Ordinal.{0}) {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    sgThH S l E = leOe (sgThH S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      sgThH S l (E % leWe (sgLW E)) := by
  unfold sgThH
  rw [sgTmH_eq hE1 hE, sgI_cat]
  show 0 + _ + _ = _
  rw [zero_add]

theorem sgThH_zero (l : Ordinal.{0}) : sgThH S l 0 = 0 := by unfold sgThH; rw [sgTmH_zero]; rfl

/-- **`Θ̂ E = Θ E` for the codes `1 ≤ E < Ω₂`.** -/
theorem sgThH_code (l : Ordinal.{0}) {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hEW : E < Om (1 + 1)) :
    sgThH S l E = gxTh (upsilon l) (ldAtR S l) E := by
  have hE : E < veblen 1 (Om (1 + 1) + 1) :=
    hEW.trans_le ((le_self_add : Om (1 + 1) ≤ Om (1 + 1) + 1).trans (right_le_veblen 1 _))
  have hlog : sgLW E = 0 := by
    unfold sgLW
    refine Ordinal.div_eq_zero_of_lt ?_
    have h := (opow_lt_opow_iff_right one_lt_omega0).1
      ((opow_log_le_self ω (zero_lt_one.trans_le hE1).ne').trans_lt (hEW.trans_le (gg_SC_eps ldOm2_SC).ge))
    exact h
  rw [sgThH_cnf l hE1 hE, hlog, sgThH_zero, leOe_zero, leWe_zero, Ordinal.div_one, Ordinal.mod_one,
    sgThH_zero, one_mul, add_zero]

section Spec

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `E ∈ H_λ` below `ε_{Ω₂+1}` is the value of its well-formed normal-form term.** -/
theorem sgTmH_spec : ∀ E, E ∈ cdHull S l → E < veblen 1 (Om (1 + 1) + 1) →
    SgWF S l (sgTmH E) ∧ sgV (sgTmH E) = E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [sgTmH_zero]; exact ⟨trivial, rfl⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  set e := sgLW E with he
  have hel : e < E := sgLW_lt_self hE1 hE
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hrH : E % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hE2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
  have hqW : E / leWe e < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : E / leWe e ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hEH ?_
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt E
  have hq1 : 1 ≤ E / leWe e := Order.one_le_iff_pos.2 ((Ordinal.div_pos hW0).2 hWe)
  obtain ⟨hew, hev⟩ := IH e hel heH (hel.trans hE)
  obtain ⟨hrw, hrv⟩ := IH _ hr hrH (hr.trans hE)
  rw [sgTmH_eq hE1 hE]
  refine ⟨sgWF_cat (A := SgT.term SgT.zero (sgTmH e) (E / leWe e))
    ⟨trivial, hew, (ldHull_iff hl hX hqW).1 hqH, hq1, hqW⟩ _ hrw, ?_⟩
  rw [sgV_cat, hrv]
  show 0 + leWe (sgV (sgTmH (sgLW E))) * (E / leWe (sgLW E)) + E % leWe e = E
  rw [zero_add, ← he, hev]
  exact Ordinal.div_add_mod E (leWe e)

/-- **Every `E ∈ H_λ` with `1 ≤ E < ε_{Ω₂+1}` is derived** (image `Θ̂ E`). -/
theorem sgDer_all {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    ScDer S l (fun b X0 => SgOwn S b X0 (fun y => y) (sgTmH E)) E (sgThH S l E) := by
  obtain ⟨hw, hv⟩ := sgTmH_spec hl hX E hEH hE
  have h := sgDer_term hl hX (sgTmH E) hw (by rw [hv]; exact hE1)
  rw [hv] at h; exact h

/-- **THE TOP LAW AT EVERY EXPONENT `1 ≤ E < ε_{Ω₂+1}` of `H_λ`** (`Sc.ScLev` with the own predicate of the
normal-form term and the image `Θ̂ E`). -/
theorem sgLev_all {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen 1 (Om (1 + 1) + 1)) :
    ScLev S l (fun b X0 => SgOwn S b X0 (fun y => y) (sgTmH E)) E (sgThH S l E) :=
  (scDer_sound hl hX (sgDer_all hl hX hEH hE1 hE)).1

end Spec

end Googology.Trans.PoR.InaccPsi.R2.Sg
