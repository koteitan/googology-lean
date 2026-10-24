import Googology.Trans.PoR.InaccPsi.R2.TaGen

/-!
# Normal-form terms with Veblen nodes below `φ(Γ₀, Ω₂ + 1)`, and the image `Θ̂`

`W^E = Ω₂^E`, `log_W E = log_ω E / Ω₂` (`Sg.sgLW`), `E_Γ = φ(Γ₀, Ω₂ + 1)` (`Ta.taTop`: the least common fixed point
above `Ω₂` of all `φ(a, ·)`, `a < Γ₀`), `inv₁`, `inv₂` (Mathlib's `invVeblen₁`, `invVeblen₂`:
`φ(inv₁ x, inv₂ x) = ω^x`).

* `taNode_nf` (**every `W`-fixed point `E` with `1 ≤ E < E_Γ` is a node**: `E = φ(a, y)`, `a = inv₁ E` small,
  `Ω₂ < y = inv₂ E < E`);
* `taTm E` (**the normal-form term**: `W^e·q ⊕ taTm r` off the fixed points (`e = log_W E`, `q = E / W^e`,
  `r = E mod W^e`), `phi (inv₁ E) (taTm (inv₂ E - Ω₂))` at a fixed point), `taTm_spec` (**every `E ∈ H_λ` below
  `E_Γ` is the value of its well-formed normal-form term**);
* `taTh S λ E = taI (taTm E)` (**the image `Θ̂`**), `taTh_cnf` (`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`),
  `taTh_node` (**the φ law `Θ̂(φ(a, Ω₂ + y)) = φ(a, Ω₁ + Θ̂ y)`**);
* `TaEL`, `TaEU`, `TaNF`, `taTm_nf` (**the normal-form term is normal, with exponents `≤ log_W E`**).

No new axiom.  New definitions: `taTop`, `taTm`, `taTh`, `TaEL`, `TaEU`, `TaNF`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ta

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

/-- **The top `E_Γ = φ(Γ₀, Ω₂ + 1)`**. -/
noncomputable def taTop (_S : InaccSeq.{0}) : Ordinal.{0} := veblen (gamma 0) (Om (1 + 1) + 1)

theorem taGam_lt_Om2 : gamma 0 < Om (1 + 1 : Ordinal.{0}) :=
  (taGam_le_SC Ph.ph_SC_Om1).trans_lt gg_Om1_lt_Om2

/-- **Every `W`-fixed point `1 ≤ E < E_Γ` is a node** `φ(inv₁ E, inv₂ E)` with a small level and
`Ω₂ < inv₂ E < E`. -/
theorem taNode_nf {E : Ordinal.{0}} (hE1 : 1 ≤ E) (hE : E < taTop S) (hfix : ¬ sgLW E < E) :
    TaSm (invVeblen₁ E) ∧ Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E ∧
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
  have hg : invVeblen₁ E < gamma 0 := by
    by_contra hc
    push Not at hc
    have hr : ω ^ E ∈ range (veblen (gamma 0)) := mem_range_veblen_iff_le_invVeblen₁.2 hc
    rw [hfixω] at hr
    obtain ⟨z, hz⟩ := hr
    have hΩ : veblen (gamma 0) (Om (1 + 1)) = Om (1 + 1) := ldOm2_SC.veblen_right taGam_lt_Om2
    have hzΩ : Om (1 + 1) < z := by
      rw [← hΩ, ← hz] at hΩE; exact (veblen_lt_veblen_iff_right).1 hΩE
    have : taTop S ≤ E := by
      rw [← hz]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hzΩ)
    exact absurd hE (not_lt.2 this)
  have ha : TaSm (invVeblen₁ E) := ⟨h1a, hg⟩
  refine ⟨ha, ?_, hlt2, hval⟩
  by_contra hc
  push Not at hc
  have : E ≤ Om (1 + 1) := by
    rw [← hval]
    calc veblen (invVeblen₁ E) (invVeblen₂ E) ≤ veblen (invVeblen₁ E) (Om (1 + 1)) :=
          (veblen_le_veblen_iff_right).2 hc
      _ = Om (1 + 1) := ldOm2_SC.veblen_right (taSm_lt_Om2 ha)
  exact absurd hΩE (not_lt.2 this)

open Classical in
/-- **The normal-form term of `E`** (the base-`Ω₂` normal form off the fixed points, a node at a fixed point). -/
noncomputable def taTm (E : Ordinal.{0}) : TaT :=
  if h' : 0 < E ∧ sgLW E < E then
    taCat (TaT.term TaT.zero (taTm (sgLW E)) (E / leWe (sgLW E))) (taTm (E % leWe (sgLW E)))
  else if h : Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E then
    TaT.phi (invVeblen₁ E) (taTm (invVeblen₂ E - Om (1 + 1)))
  else TaT.zero
termination_by E
decreasing_by
  · exact h'.2
  · exact (Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le h'.1)
  · exact (Ordinal.sub_le_self _ _).trans_lt h.2

theorem taTm_zero : taTm 0 = TaT.zero := by
  rw [taTm, dif_neg (fun h => lt_irrefl _ h.1), dif_neg]
  rw [invVeblen₂_zero]; exact fun h => absurd h.1 (not_lt.2 zero_le)

theorem taTm_eq {E : Ordinal.{0}} (h : 0 < E ∧ sgLW E < E) :
    taTm E = taCat (TaT.term TaT.zero (taTm (sgLW E)) (E / leWe (sgLW E))) (taTm (E % leWe (sgLW E))) := by
  rw [taTm, dif_pos h]

theorem taTm_node {E : Ordinal.{0}} (h0 : ¬ (0 < E ∧ sgLW E < E))
    (h : Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E) :
    taTm E = TaT.phi (invVeblen₁ E) (taTm (invVeblen₂ E - Om (1 + 1))) := by
  rw [taTm, dif_neg h0, dif_pos h]

/-- **The image `Θ̂ E`** of the normal-form term. -/
noncomputable def taTh (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} := taI S l (taTm E)

theorem taTh_zero (l : Ordinal.{0}) : taTh S l 0 = 0 := by unfold taTh; rw [taTm_zero]; rfl

/-- The pieces of a node: `inv₂ E = Ω₂ + (inv₂ E - Ω₂)`. -/
theorem taNode_add {E : Ordinal.{0}} (h : Om (1 + 1) < invVeblen₂ E) :
    Om (1 + 1) + (invVeblen₂ E - Om (1 + 1)) = invVeblen₂ E := Ordinal.add_sub_cancel_of_le h.le

theorem taNode_one {E : Ordinal.{0}} (h : Om (1 + 1) < invVeblen₂ E) : 1 ≤ invVeblen₂ E - Om (1 + 1) := by
  refine Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 fun h0 => ?_)
  have := taNode_add h
  rw [h0, add_zero] at this
  exact absurd this h.ne

/-- **`Θ̂(W^e·q + r) = Ω^{Θ̂ e}·Θ q + Θ̂ r`** off the fixed points (the remainder's term well formed). -/
theorem taTh_cnf {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) {E : Ordinal.{0}} (h : 0 < E ∧ sgLW E < E)
    (hr : TaWF S l (taTm (E % leWe (sgLW E)))) :
    taTh S l E = leOe (taTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      taTh S l (E % leWe (sgLW E)) := by
  unfold taTh
  rw [taTm_eq h, taI_cat h1 _ _ hr]
  show 0 + _ + _ = _
  rw [zero_add]

/-- **The φ law: `Θ̂(φ(a, Ω₂ + y)) = φ(a, Ω₁ + Θ̂ y)`** at a node (`a = inv₁ E`, `Ω₂ + y = inv₂ E`). -/
theorem taTh_node {l E : Ordinal.{0}} (h0 : ¬ (0 < E ∧ sgLW E < E))
    (h : Om (1 + 1) < invVeblen₂ E ∧ invVeblen₂ E < E) :
    taTh S l E = veblen (invVeblen₁ E) (Om 1 + taTh S l (invVeblen₂ E - Om (1 + 1))) := by
  unfold taTh; rw [taTm_node h0 h]; rfl

section Spec

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every `E ∈ H_λ` below `E_Γ` is the value of its well-formed normal-form term.** -/
theorem taTm_spec : ∀ E, E ∈ cdHull S l → E < taTop S → TaWF S l (taTm E) ∧ taV (taTm E) = E := by
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
    refine ⟨taWF_cat h1ρ (A := TaT.term TaT.zero (taTm e) (E / leWe e))
      ⟨trivial, hew, (ldHull_iff hl hX hqW).1 hqH, hq1, hqW⟩ _ hrw, ?_⟩
    rw [taV_cat _ _ hrw, hrv]
    show 0 + leWe (taV (taTm (sgLW E))) * (E / leWe (sgLW E)) + E % leWe e = E
    rw [zero_add, ← he, hev]
    exact Ordinal.div_add_mod E (leWe e)
  · obtain ⟨ha, hΩy, hyE, hval⟩ := taNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    set a := invVeblen₁ E
    set y := invVeblen₂ E
    have haE : a < E := (taSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : y ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : y - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : y - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    obtain ⟨hw, hv⟩ := IH _ hy'E hy'H (hy'E.trans hE)
    have hv1 : 1 ≤ taV (taTm (y - Om (1 + 1))) := by rw [hv]; exact taNode_one hΩy
    have hne : taTm (y - Om (1 + 1)) ≠ TaT.zero := fun h0 => by
      rw [h0] at hv1; exact absurd hv1 (not_le.2 zero_lt_one)
    have hi1 := (taV_pos h1ρ _ hw hne).2
    rw [taTm_node hc ⟨hΩy, hyE⟩]
    refine ⟨⟨ha, hw, hv1, hi1⟩, ?_⟩
    show veblen a (Om (1 + 1) + taV (taTm (y - Om (1 + 1)))) = E
    rw [hv, taNode_add hΩy, hval]

end Spec

/-! ## Normal form -/

/-- Every exponent of the term exceeds `r` (a node counts as the exponent of its own value). -/
def TaEL (r : Ordinal.{0}) : TaT → Prop
  | .zero => True
  | .phi a Y => r < taV (.phi a Y)
  | .term P R _ => r < taV R ∧ TaEL r P

/-- Every exponent of the term is below `r`. -/
def TaEU (r : Ordinal.{0}) : TaT → Prop
  | .zero => True
  | .phi a Y => taV (.phi a Y) < r
  | .term P R _ => taV R < r ∧ TaEU r P

/-- **Normal form**: the exponents of the prefix exceed the last exponent, recursively, also inside the nodes. -/
def TaNF : TaT → Prop
  | .zero => True
  | .phi _ Y => TaNF Y
  | .term P R _ => TaNF P ∧ TaNF R ∧ TaEL (taV R) P

theorem taEL_cat {r : Ordinal.{0}} {A : TaT} (hA : TaEL r A) : ∀ B, TaEL r B → TaEL r (taCat A B)
  | .zero, _ => hA
  | .phi _ _, h => ⟨h, hA⟩
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1, taEL_cat hA P h2⟩

theorem taEU_cat {r : Ordinal.{0}} {A : TaT} (hA : TaEU r A) : ∀ B, TaEU r B → TaEU r (taCat A B)
  | .zero, _ => hA
  | .phi _ _, h => ⟨h, hA⟩
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1, taEU_cat hA P h2⟩

theorem taEU_mono {r r' : Ordinal.{0}} (h : r ≤ r') : ∀ t, TaEU r t → TaEU r' t
  | .zero, _ => trivial
  | .phi _ _, h1 => h1.trans_le h
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1.trans_le h, taEU_mono h P h2⟩

theorem taNF_cat {m : Ordinal.{0}} {A : TaT} (hA : TaNF A) (hAm : ∀ x, x < m → TaEL x A) :
    ∀ B, TaNF B → TaEU m B → TaNF (taCat A B)
  | .zero, _, _ => hA
  | .phi _ _, hB, h => ⟨hA, hB, hAm _ h⟩
  | .term P _ _, ⟨hP, hR, hPR⟩, ⟨hRm, hPm⟩ => ⟨taNF_cat hA hAm P hP hPm, hR, taEL_cat (hAm _ hRm) P hPR⟩

/-- **The normal-form term of every `E ∈ H_λ` below `E_Γ` is normal, with exponents `≤ log_W E`.** -/
theorem taTm_nf {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    ∀ E, E ∈ cdHull S l → E < taTop S → TaNF (taTm E) ∧ TaEU (sgLW E + 1) (taTm E) := by
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
    have hev := (taTm_spec hl hX _ heH (hel.trans hE)).2
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
  · obtain ⟨ha, hΩy, hyE, hval⟩ := taNode_nf hE1 hE (fun h => hc ⟨hpos, h⟩)
    have haE : invVeblen₁ E < E := (taSm_lt_Om2 ha).trans (hΩy.trans hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := (mem_of_veblen_mem (by rw [hval]; exact hEH)
      (by rw [hval]; exact haE) (by rw [hval]; exact hyE)).2
    have hy'H : invVeblen₂ E - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : invVeblen₂ E - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    obtain ⟨hn, -⟩ := IH _ hy'E hy'H (hy'E.trans hE)
    have hvE := (taTm_spec hl hX E hEH hE).2
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

end Googology.Trans.PoR.InaccPsi.R2.Ta
