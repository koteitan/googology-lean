import Googology.Trans.PoR.InaccPsi.R2.TgTm

/-!
# The normal-form term with code levels of every `E ∈ H_λ` below `φ(Ω₂, 1)`

`W^E = Ω₂^E`, `H_λ = cdHull S λ`, `Ta.taTm` the normal-form term (base `Ω₂` off the `W`-fixed points, a node
`φ(inv₁ E, inv₂ E)` at a `W`-fixed point).  Below `φ(Ω₂, 1)` every node level `inv₁ E` is a code `1 ≤ a < Ω₂`
of `λ` (`Td.tdNode_nfW`, `LdHull.ldHull_iff`).

* `tgTm_spec` (**EVERY `E ∈ H_λ` BELOW `φ(Ω₂, 1)` IS THE VALUE OF ITS WELL-FORMED NORMAL-FORM TERM WITH CODE
  LEVELS, every node off its fixed points**), `tgTm_nf` (the term is normal, exponents `≤ log_W E`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td

variable {S : InaccSeq.{0}}

section Spec

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `E ∈ H_λ` below `φ(Ω₂, 1)` is the value of its well-formed normal-form term with code levels**, every
node off its fixed points. -/
theorem tgTm_spec : ∀ E, E ∈ cdHull S l → E < veblen (Om (1 + 1)) 1 →
    TgWF S l (taTm E) ∧ TgNX (taTm E) ∧ taV (taTm E) = E := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [taTm_zero]; exact ⟨trivial, trivial, rfl⟩
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
    obtain ⟨hew, hen, hev⟩ := IH e hel heH (hel.trans hE)
    obtain ⟨hrw, hrn, hrv⟩ := IH _ hr hrH (hr.trans hE)
    rw [taTm_eq hc]
    refine ⟨tgWF_cat h1ρ (A := TaT.term TaT.zero (taTm e) (E / leWe e))
      ⟨trivial, hew, (ldHull_iff hl hX hqW).1 hqH, hq1, hqW⟩ _ hrw,
      tgNX_cat (A := TaT.term TaT.zero (taTm e) (E / leWe e)) ⟨trivial, hen⟩ _ hrn, ?_⟩
    rw [tgV_cat _ _ hrw, hrv]
    show 0 + leWe (taV (taTm (sgLW E))) * (E / leWe (sgLW E)) + E % leWe e = E
    rw [zero_add, ← he, hev]
    exact Ordinal.div_add_mod E (leWe e)
  · obtain ⟨ha1, haW, hΩy, hyE, hval⟩ := tdNode_nfW hE1 hE (fun h => hc ⟨hpos, h⟩)
    set a := invVeblen₁ E
    set y := invVeblen₂ E
    have haE : a < E := haW.trans (hΩy.trans hyE)
    have hmem := mem_of_veblen_mem (S := S) (by rw [hval]; exact hEH) (by rw [hval]; exact haE)
      (by rw [hval]; exact hyE)
    have hac : GxCl (upsilon l) (ldAtR S l) a := (ldHull_iff hl hX haW).1 hmem.1
    have hy'H : y - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hmem.2 _
    have hy'E : y - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    obtain ⟨hw, hn, hv⟩ := IH _ hy'E hy'H (hy'E.trans hE)
    have hv1 : 1 ≤ taV (taTm (y - Om (1 + 1))) := by rw [hv]; exact taNode_one hΩy
    have hne : taTm (y - Om (1 + 1)) ≠ TaT.zero := fun h0 => by
      rw [h0] at hv1; exact absurd hv1 (not_le.2 zero_lt_one)
    have hi1 := (tgV_pos h1ρ.le _ hw hne).2
    have hy : Om (1 + 1) + taV (taTm (y - Om (1 + 1))) = y := by rw [hv, taNode_add hΩy]
    rw [taTm_node hc ⟨hΩy, hyE⟩]
    refine ⟨⟨hac, ha1, haW, hw, hv1, hi1⟩, ⟨?_, hn⟩, ?_⟩
    · show Om (1 + 1) + taV (taTm (y - Om (1 + 1))) < veblen a (Om (1 + 1) + taV (taTm (y - Om (1 + 1))))
      rw [hy, hval]; exact hyE
    · show veblen a (Om (1 + 1) + taV (taTm (y - Om (1 + 1)))) = E
      rw [hy, hval]

/-- **The normal-form term of every `E ∈ H_λ` below `φ(Ω₂, 1)` is normal, with exponents `≤ log_W E`.** -/
theorem tgTm_nf : ∀ E, E ∈ cdHull S l → E < veblen (Om (1 + 1)) 1 →
    TaNF (taTm E) ∧ TaEU (sgLW E + 1) (taTm E) := by
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
    have hev := (tgTm_spec hl hX _ heH (hel.trans hE)).2.2
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
  · obtain ⟨_, haW, hΩy, hyE, hval⟩ := tdNode_nfW hE1 hE (fun h => hc ⟨hpos, h⟩)
    have haE : invVeblen₁ E < E := haW.trans (hΩy.trans hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : invVeblen₂ E - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : invVeblen₂ E - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    obtain ⟨hn, -⟩ := IH _ hy'E hy'H (hy'E.trans hE)
    have hvE := (tgTm_spec hl hX E hEH hE).2.2
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

end Spec

end Googology.Trans.PoR.InaccPsi.R2.Tg
