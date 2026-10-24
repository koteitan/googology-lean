import Googology.Trans.PoR.InaccPsi.R2.TdGen

/-!
# Normal-form terms below `E_K = φ(K, Ω₂ + 1)`

`W^E = Ω₂^E`, `log_W E = Sg.sgLW E`, `K = tdK S = ψ_{Ω₁}(Ω_ω)`, `TdSm S a`: `1 ≤ a < K`, `E_K = tdTop S = φ(K,
Ω₂ + 1)` (the least common fixed point above `Ω₂`
of all `φ(a, ·)`, `a < K`), `inv₁`, `inv₂` (Mathlib's `invVeblen₁`, `invVeblen₂`).  The normal-form term
`Ta.taTm` and the image `Θ̂ = Ta.taTh` are those of `Ta` (they are defined for every ordinal).

* `tdNode_nf` (**every `W`-fixed point `1 ≤ E < E_K` is a node `φ(a, y)` with `TdSm S a`**, `Ω₂ < y < E`);
* `tdTh_cnf` (`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`), `tdTm_spec` (**every `E ∈ H_λ` below `E_K` is the value of
  its well-formed normal-form term**), `tdTm_nf` (that term is normal).

No new axiom.  New definition: `tdTop`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- **The top `E_K = φ(K, Ω₂ + 1)`**. -/
noncomputable def tdTop (S : InaccSeq.{0}) : Ordinal.{0} := veblen (tdK S) (Om (1 + 1) + 1)

/-- **Every `W`-fixed point `1 ≤ E < E_K` is a node** `φ(inv₁ E, inv₂ E)` with a level below `K` and
`Ω₂ < inv₂ E < E`. -/
theorem tdNode_nf {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < tdTop S) (hfix : ¬ sgLW E < E) :
    TdSm S (invVeblen₁ E) ∧ Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E ∧
      veblen (invVeblen₁ E) (invVeblen₂ E) = E := by
  have hW1 : (1 : Ordinal.{0}) < Om (1 + 1) := gg_one_lt_of_SC ldOm2_SC
  have hle : sgLW E ≤ E :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω E)
  have heq : sgLW E = E := le_antisymm hle (not_lt.1 hfix)
  have hWE : leWe E ≤ E := by have h0 := sgLW_le (zero_lt_one.trans_le hE1); rwa [heq] at h0
  have h2 : E ≤ Om (1 + 1) * E := Ordinal.le_mul_right E ldOm2_SC.1
  have h3 : Om (1 + 1) * E ≤ leWe E := right_le_opow _ one_lt_omega0
  have hm : Om (1 + 1) * E = E := le_antisymm (h3.trans hWE) h2
  have hfixω : ω ^ E = E := by
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
  have hval : veblen (invVeblen₁ E) (invVeblen₂ E) = E := by rw [veblen_invVeblen₁_invVeblen₂, hfixω]
  have hlt2 : invVeblen₂ E < E := by have := invVeblen₂_lt E; rwa [hfixω] at this
  have h1a : 1 ≤ invVeblen₁ E := by
    refine mem_range_veblen_iff_le_invVeblen₁.1 ?_
    rw [hfixω]
    refine (mem_range_veblen one_ne_zero).2 fun b hb => ?_
    rw [Order.lt_one_iff] at hb; subst hb; rw [veblen_zero_apply]; exact hfixω
  have hg : invVeblen₁ E < tdK S := by
    by_contra hc
    push Not at hc
    have hr : ω ^ E ∈ range (veblen (tdK S)) := mem_range_veblen_iff_le_invVeblen₁.2 hc
    rw [hfixω] at hr
    obtain ⟨z, hz⟩ := hr
    have hΩ : veblen (tdK S) (Om (1 + 1)) = Om (1 + 1) := ldOm2_SC.veblen_right tdK_lt_Om2
    have hzΩ : Om (1 + 1) < z := by
      rw [← hΩ, ← hz] at hΩE; exact (veblen_lt_veblen_iff_right).1 hΩE
    have : tdTop S ≤ E := by
      rw [← hz]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hzΩ)
    exact absurd hE (not_lt.2 this)
  have ha : TdSm S (invVeblen₁ E) := ⟨h1a, hg⟩
  refine ⟨ha, ?_, hlt2, hval⟩
  by_contra hc
  push Not at hc
  have : E ≤ Om (1 + 1) := by
    rw [← hval]
    calc veblen (invVeblen₁ E) (invVeblen₂ E) ≤ veblen (invVeblen₁ E) (Om (1 + 1)) :=
          (veblen_le_veblen_iff_right).2 hc
      _ = Om (1 + 1) := ldOm2_SC.veblen_right (tdSm_lt_Om2 ha)
  exact absurd hΩE (not_lt.2 this)

/-- **`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`** off the fixed points (the remainder's term well formed). -/
theorem tdTh_cnf {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) {E : Ordinal.{0}} (h : 0 < E ∧ sgLW E < E)
    (hr : TdWF S l (taTm (E % leWe (sgLW E)))) :
    taTh S l E = leOe (taTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      taTh S l (E % leWe (sgLW E)) := by
  unfold taTh
  rw [taTm_eq h, tdI_cat h1 _ _ hr]
  show 0 + _ + _ = _
  rw [zero_add]

section Spec

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `E ∈ H_λ` below `E_K` is the value of its well-formed normal-form term.** -/
theorem tdTm_spec : ∀ E, E ∈ cdHull S l → E < tdTop S → TdWF S l (taTm E) ∧ taV (taTm E) = E := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [taTm_zero]; exact ⟨trivial, rfl⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  · set e := sgLW E with he
    have hel : e < E := hc.2
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
    rw [taTm_eq hc]
    refine ⟨tdWF_cat h1ρ (A := TaT.term TaT.zero (taTm e) (E / leWe e))
      ⟨trivial, hew, (ldHull_iff hl hX hqW).1 hqH, hq1, hqW⟩ _ hrw, ?_⟩
    rw [tdV_cat _ _ hrw, hrv]
    show 0 + leWe (taV (taTm (sgLW E))) * (E / leWe (sgLW E)) + E % leWe e = E
    rw [zero_add, ← he, hev]
    exact Ordinal.div_add_mod E (leWe e)
  · obtain ⟨ha, hΩy, hyE, hval⟩ := tdNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    set a := invVeblen₁ E
    set y := invVeblen₂ E
    have haE : a < E := (tdSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : y ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : y - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : y - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    obtain ⟨hw, hv⟩ := IH _ hy'E hy'H (hy'E.trans hE)
    have hv1 : 1 ≤ taV (taTm (y - Om (1 + 1))) := by rw [hv]; exact taNode_one hΩy
    have hne : taTm (y - Om (1 + 1)) ≠ TaT.zero := fun h0 => by
      rw [h0] at hv1; exact absurd hv1 (not_le.2 zero_lt_one)
    have hi1 := (tdV_pos h1ρ _ hw hne).2
    rw [taTm_node hc ⟨hΩy, hyE⟩]
    refine ⟨⟨ha, hw, hv1, hi1⟩, ?_⟩
    show veblen a (Om (1 + 1) + taV (taTm (y - Om (1 + 1)))) = E
    rw [hv, taNode_add hΩy, hval]

end Spec

/-! ## Normal form -/

/-- **The normal-form term of every `E ∈ H_λ` below `E_K` is normal, with exponents `≤ log_W E`.** -/
theorem tdTm_nf {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ E, E ∈ cdHull S l → E < tdTop S → TaNF (taTm E) ∧ TaEU (sgLW E + 1) (taTm E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [taTm_zero]; exact ⟨trivial, trivial⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  · have hel : sgLW E < E := hc.2
    have hWe : leWe (sgLW E) ≤ E := sgLW_le hpos
    have hW0 : leWe (sgLW E) ≠ 0 := (leWe_pos _).ne'
    have hrW : E % leWe (sgLW E) < leWe (sgLW E) := Ordinal.mod_lt _ hW0
    have hr : E % leWe (sgLW E) < E := hrW.trans_le hWe
    have heH : sgLW E ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
    have hrH : E % leWe (sgLW E) ∈ cdHull S l := leModP_mem (Om (1 + 1) * sgLW E) hEH
    obtain ⟨hen, -⟩ := IH _ hel heH (hel.trans hE)
    obtain ⟨hrn, hru⟩ := IH _ hr hrH (hr.trans hE)
    have hev := (tdTm_spec hl hX _ heH (hel.trans hE)).2
    have hrU : TaEU (sgLW E) (taTm (E % leWe (sgLW E))) := by
      rcases eq_or_ne (E % leWe (sgLW E)) 0 with h0 | h0
      · rw [h0, taTm_zero]; trivial
      have h1 : leWe 0 ≤ E % leWe (sgLW E) := by
        rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 h0
      exact taEU_mono (Order.add_one_le_of_lt (sjLogW h1 hrW).2) _ hru
    rw [taTm_eq hc]
    refine ⟨?_, ?_⟩
    · have hA : TaNF (TaT.term TaT.zero (taTm (sgLW E)) (E / leWe (sgLW E))) := ⟨trivial, hen, trivial⟩
      have hAm : ∀ x, x < sgLW E → TaEL x (TaT.term TaT.zero (taTm (sgLW E)) (E / leWe (sgLW E))) :=
        fun x hx => ⟨by rw [hev]; exact hx, trivial⟩
      exact taNF_cat hA hAm _ hrn hrU
    · have hA : TaEU (sgLW E + 1) (TaT.term TaT.zero (taTm (sgLW E)) (E / leWe (sgLW E))) :=
        ⟨by rw [hev]; exact Order.lt_add_one_iff.2 le_rfl, trivial⟩
      exact taEU_cat hA _ (taEU_mono le_self_add _ hrU)
  · obtain ⟨ha, hΩy, hyE, hval⟩ := tdNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    have haE : invVeblen₁ E < E := (tdSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : invVeblen₂ E - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : invVeblen₂ E - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    obtain ⟨hn, -⟩ := IH _ hy'E hy'H (hy'E.trans hE)
    have hvE := (tdTm_spec hl hX E hEH hE).2
    have heqW : sgLW E = E := le_antisymm
      ((Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω E))
      (not_lt.1 fun h => hc ⟨hpos, h⟩)
    have hnode := taTm_node hc ⟨hΩy, hyE⟩
    refine ⟨?_, ?_⟩
    · rw [hnode]; exact hn
    · have : TaEU (sgLW E + 1) (taTm E) := by
        rw [hnode]
        show taV (TaT.phi (invVeblen₁ E) (taTm (invVeblen₂ E - Om (1 + 1)))) < sgLW E + 1
        rw [← hnode, hvE, heqW]; exact lt_add_one E
      exact this

end Googology.Trans.PoR.InaccPsi.R2.Td
