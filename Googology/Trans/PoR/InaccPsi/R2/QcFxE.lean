import Googology.Trans.PoR.InaccPsi.R2.QcFxD

/-!
# QcFxE: THE TOP DATA AT A FIXED POINT `E = H_λ(y)` OF `Γ` IN `[X, B₂)` — THE NEW SEGMENT BASE

As `Va.vs_fx_pi`, `Va.vs_fx_cl`, `Va.vsTopFix` from `X` on.  The reading `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` of `E` is exact:
`π` commutes with `ϑ` below `Ω₂` (`R2.pi_vt_two`), with sums (`R2.pi_add`), and with the level reading
`Ω₁·λ(x)`: on `Ω₁·(Ω₁^{A}·c + R) = ω^{Ω₁·(1+A)}·c + Ω₁·R` by the digits of the members at the component `c`
(`Qc.QDS.dig`) with `ω^{Ω₁·(1+A) + β} = Ω₁·ω^{Ω₁·A + β}` (`R2.siOm1_opow_TB`), by induction on the level (`qs_lv_pi`).
`E` is a code (`UcCl.hatom`: the components of `λ` and the parts of `y` are codes).

* `qs_lv_E` (the level readings are below `ε_{Ω₁+1}`), `qs_exE`, `qs_digE` (the codes below `E` are exact, with their
  digits), `qs_lv_pi` (**the level readings are exact**), `qs_fx_pi` (**the reading of `E` is exact**), `qs_fx_cl`;
* `qsTopFix` (**THE TOP DATA AT A FIXED POINT OF `Γ`**, the segment base `vaFB E = E` read `qcA E` itself).

No new axiom.  New definition: `qsTopFix`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Ge

section Lev

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < ucB)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QsGood e)

include hE hBE hEB hlim hIH

/-- **The level readings with components codes below `E` are below `ε_{Ω₁+1}`.** -/
theorem qs_lv_E {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ γ, γ < ucE → (∀ d ∈ ucComps γ, d < E ∧ qcG d < x) → qcLvx E γ x < ggE := by
  intro γ hγE hγD
  set fE : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vQ d x else 0 with hfEdef
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have hf0 : fE 0 = 0 := by simp only [hfEdef, if_pos hE0, vQ_zero]
  have hD0 : (fun d => d < E ∧ qcG d < x) 0 := ⟨hE0, by rw [qcG_zero]; exact hx.pos⟩
  have hfΩ : ∀ d, (fun d => d < E ∧ qcG d < x) d → fE d < Om1 := fun d hd => by
    simp only [hfEdef, if_pos hd.1]; exact (qs_T hE hBE hEB hlim hIH hx hx1 hd.1 hd.2).2.1
  have hfm : ∀ d d', (fun d => d < E ∧ qcG d < x) d → (fun d => d < E ∧ qcG d < x) d' → d < d' →
      fE d < fE d' := fun d d' hd hd' hdd => by
    simp only [hfEdef, if_pos hd.1, if_pos hd'.1]
    exact qs_mono hE hBE hEB hlim hIH hx hx1 hdd hd'.1 hd.2 hd'.2
  exact (qcLv_main fE (fun d => d < E ∧ qcG d < x) hf0 hD0 hfΩ hfm γ hγE hγD).1

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **The codes below `E` are exact.** -/
theorem qs_exE {c : Ordinal.{0}} (hc : c < E) (hgc : qcG c < σ) :
    vQ c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vQ c ρ) = vQ c σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -, -⟩ := qs_mem hEB hlim hIH hBE hc
  have hGc := qs_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
  rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
  exact M.ex σ ρ c hB hcM hGc

/-- **The digits of the codes below `E`**: `π(ω^P·c(ρ)) = ω^{P'}·c(σ)` when `π(ω^{P+β}) = ω^{P'+π(β)}` for the
countable `β`. -/
theorem qs_digE {d : Ordinal.{0}} (hd : d < E) (hgd : qcG d < σ) (P P' : Ordinal.{0})
    (hP : ∀ β, β ∈ TB ρ σ → β < Om1 →
      ω ^ (P + β) ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ (P + β)) = ω ^ (P' + R2.pi σ ρ β)) :
    ω ^ P * vQ d ρ ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ P * vQ d ρ) = ω ^ P' * vQ d σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [vQ_zero, vQ_zero, mul_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  obtain ⟨e, M, -, -, -, -, -, hdM, -, -, -, hEg, -, hR, hG, -, -⟩ := qs_mem hEB hlim hIH hBE hd
  have hGd := qs_memG (omega0_lt_inE hB.1) hEg hgd hG hdM hgd
  have hEgρ : M.Eg < ρ := ((M.Eg_le d hd0).trans_lt hGd).trans hB.2.2.1
  rw [← hR d hdM ρ hB.2.1 hρ1 (hGd.trans hB.2.2.1), ← hR d hdM σ hB.1 hσ1 hGd]
  exact M.dig σ ρ d hB hdM hGd P P' fun β hβT hβ => hP β hβT (hβ.trans (M.V_lt ρ hB.2.1 hρ1 hEgρ))

/-- **The level readings are exact**: `Ω₁·λ(ρ) ∈ T^ρ[σ]` and `π(Ω₁·λ(ρ)) = Ω₁·λ(σ)` for a level with its
components codes below `E` with gates below `σ`. -/
theorem qs_lv_pi : ∀ γ : Ordinal.{0}, γ < ucE → (∀ d ∈ ucComps γ, d < E ∧ qcG d < σ) →
    Om1 * qcLvx E γ ρ ∈ TB ρ σ ∧ R2.pi σ ρ (Om1 * qcLvx E γ ρ) = Om1 * qcLvx E γ σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE hγD
  rcases lt_or_ge γ OmTwo with hγ2 | hγ2
  · have hd := hγD γ (by rw [ucComps_small hγ2]; exact mem_singleton _)
    have hv : ∀ x, qcLvx E γ x = vQ γ x := fun x => by unfold qcLvx; rw [qcLv_small _ hγ2, if_pos hd.1]
    obtain ⟨h1, h2⟩ := qs_exE hE hBE hEB hlim hIH hB hd.1 hd.2
    have hlt := (qs_T hE hBE hEB hlim hIH hB.2.1 hρ1 hd.1 (hd.2.trans hB.2.2.1)).2.1
    obtain ⟨h3, h4⟩ := siOm1_mul_TB hB h1 hlt
    rw [hv ρ, hv σ]
    exact ⟨h3, by rw [h4, h2]⟩
  have hc := ucComps_big hγ2 hγE
  have hlog := uc_log_lt hγ2 hγE
  have hmod := uc_mod_lt hγ2
  have haD : ∀ d ∈ ucComps (log OmTwo γ), d < E ∧ qcG d < σ := fun d hd => hγD d (by rw [hc]; exact Or.inl hd)
  have hrD : ∀ d ∈ ucComps (γ % OmTwo ^ log OmTwo γ), d < E ∧ qcG d < σ := fun d hd =>
    hγD d (by rw [hc]; exact Or.inr (Or.inr hd))
  have hdD : γ / OmTwo ^ log OmTwo γ < E ∧ qcG (γ / OmTwo ^ log OmTwo γ) < σ :=
    hγD _ (by rw [hc]; exact Or.inr (Or.inl rfl))
  obtain ⟨a1, a2⟩ := IH _ hlog (hlog.trans hγE) haD
  obtain ⟨r1, r2⟩ := IH _ hmod (hmod.trans hγE) hrD
  have hv : ∀ x, qcLvx E γ x = Om1 ^ qcLvx E (log OmTwo γ) x * vQ (γ / OmTwo ^ log OmTwo γ) x +
      qcLvx E (γ % OmTwo ^ log OmTwo γ) x := fun x => by
    unfold qcLvx; rw [qcLv_big _ hγ2 hγE, if_pos hdD.1]
  have e1 : ∀ A : Ordinal.{0}, Om1 * Om1 ^ A = ω ^ (Om1 * (1 + A)) := fun A => by
    rw [← qc_Om1_opow_eq, opow_add, opow_one]
  have hdec : ∀ x, Om1 * qcLvx E γ x = ω ^ (Om1 * (1 + qcLvx E (log OmTwo γ) x)) *
      vQ (γ / OmTwo ^ log OmTwo γ) x + Om1 * qcLvx E (γ % OmTwo ^ log OmTwo γ) x := fun x => by
    calc Om1 * qcLvx E γ x = Om1 * (Om1 ^ qcLvx E (log OmTwo γ) x * vQ (γ / OmTwo ^ log OmTwo γ) x +
          qcLvx E (γ % OmTwo ^ log OmTwo γ) x) := by rw [hv x]
      _ = Om1 * Om1 ^ qcLvx E (log OmTwo γ) x * vQ (γ / OmTwo ^ log OmTwo γ) x +
          Om1 * qcLvx E (γ % OmTwo ^ log OmTwo γ) x := by rw [mul_add, mul_assoc]
      _ = _ := by rw [e1]
  -- the digits at the coefficient
  have haρ : (∀ d ∈ ucComps (log OmTwo γ), d < E ∧ qcG d < ρ) := fun d hd =>
    ⟨(haD d hd).1, (haD d hd).2.trans hB.2.2.1⟩
  have hAE : qcLvx E (log OmTwo γ) ρ < ggE :=
    qs_lv_E hE hBE hEB hlim hIH hB.2.1 hρ1 _ (hlog.trans hγE) haρ
  have e2 : ∀ A β : Ordinal.{0}, ω ^ (Om1 * (1 + A) + β) = Om1 * ω ^ (Om1 * A + β) := fun A β => by
    rw [mul_add, mul_one, add_assoc, opow_add, rj_Om1_opow]
  have hP : ∀ β, β ∈ TB ρ σ → β < Om1 →
      ω ^ (Om1 * (1 + qcLvx E (log OmTwo γ) ρ) + β) ∈ TB ρ σ ∧
        R2.pi σ ρ (ω ^ (Om1 * (1 + qcLvx E (log OmTwo γ) ρ) + β)) =
          ω ^ (Om1 * (1 + qcLvx E (log OmTwo γ) σ) + R2.pi σ ρ β) := by
    intro β hβT hβ1
    obtain ⟨b1, b2⟩ := pi_add hB a1 hβT
    have hbE : Om1 * qcLvx E (log OmTwo γ) ρ + β < ggE := hgE.add_lt (hgE.mul_lt hOE hAE) (hβ1.trans hOE)
    obtain ⟨s1, s2⟩ := siOm1_opow_TB hB hbE
    rw [e2, e2]
    exact ⟨s1.2 b1, by rw [s2 b1, b2, a2]⟩
  obtain ⟨t1, t2⟩ := qs_digE hE hBE hEB hlim hIH hB hdD.1 hdD.2 _ _ hP
  obtain ⟨s1, s2⟩ := pi_add hB t1 r1
  rw [hdec ρ, hdec σ]
  exact ⟨s1, by rw [s2, t2, r2]⟩

end Lev

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < ucB) (hXE : tlX ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QsGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)

include hE hBE hEB hXE hlim hIH hA hi

/-- **The reading of the fixed point is exact.** -/
theorem qs_fx_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (qcQE E) < σ) :
    qcA E ρ ∈ TB ρ σ ∧ R2.pi σ ρ (qcA E ρ) = qcA E σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hgρ := hgσ.trans hB.2.2.1
  obtain ⟨-, -, hlE, -, hyE, -, hne, -⟩ := qs_fx_dat hEB hXE hA hi
  obtain ⟨hcompσ, -, -, -, -, -, -⟩ := qs_fx_parts hE hBE hEB hXE hlim hIH hA hi hB.1 hσ1 hgσ
  obtain ⟨-, -, hNE, -, -, hK1, -⟩ := qs_fx_parts hE hBE hEB hXE hlim hIH hA hi hB.2.1 hρ1 hgρ
  obtain ⟨-, hgF, hg0y⟩ := qs_fix_gates hA hi hEB
  have hK : qcK (ucLev E) (ucI (ucLev E) E) ρ ∈ TB ρ σ ∧
      R2.pi σ ρ (qcK (ucLev E) (ucI (ucLev E) E) ρ) = qcK (ucLev E) (ucI (ucLev E) E) σ := by
    unfold qcK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      obtain ⟨f1, f2⟩ := qs_exE hE hBE hEB hlim hIH hB (hpy.trans hyE) (hgp.trans_lt hgσ)
      obtain ⟨o1, o2⟩ := qs_exE hE hBE hEB hlim hIH hB ((Ordinal.sub_le_self _ _).trans_lt hyE) (hgo.trans_lt hgσ)
      obtain ⟨s1, s2⟩ := pi_add hB f1 o1
      exact ⟨s1, by rw [s2, f2, o2]⟩
    · exact qs_exE hE hBE hEB hlim hIH hB hyE ((hg0y hF).trans_lt hgσ)
  obtain ⟨l1, l2⟩ := qs_lv_pi hE hBE hEB hlim hIH hB (ucLev E) hlE hcompσ
  obtain ⟨o1, o2⟩ := lgPi_OmOm hB
  have harg : ∀ x, Om1 * (Om1 + qcLvx E (ucLev E) x) + qcK (ucLev E) (ucI (ucLev E) E) x =
      Om1 * Om1 + Om1 * qcLvx E (ucLev E) x + qcK (ucLev E) (ucI (ucLev E) E) x := fun x => by rw [mul_add]
  obtain ⟨a1, a2⟩ := pi_add hB o1 l1
  obtain ⟨b1, b2⟩ := pi_add hB a1 hK.1
  have h2 := qc_arg_lt hNE hK1
  rw [harg ρ] at h2
  rw [qcA_fix hA hi hXE hEB ρ, qcA_fix hA hi hXE hEB σ, harg ρ, harg σ]
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hB.2.1 hρ1 b1.1 h2
  refine ⟨⟨hvT, by rw [hPar]; exact b1.2⟩, ?_⟩
  rw [pi_vt_two hB b1 h2, b2, a2, o2, l2, hK.2]

/-- **The fixed point is a code over every strongly critical `Z` above its gate.** -/
theorem qs_fx_cl {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (qcQE E) < Z) : UcCl Z E := by
  obtain ⟨-, -, hlE, hlc, hyE, hFy, hne, -⟩ := qs_fx_dat hEB hXE hA hi
  obtain ⟨hgc, hgF, hg0y⟩ := qs_fix_gates hA hi hEB
  have hcomp : ∀ d ∈ ucComps (ucLev E), UcCl Z d := fun d hd =>
    qs_cl_code hE hBE hEB hlim hIH hZ ((le_ucC hd).trans_lt hlc) ((hgc d hd).trans_lt hgZ)
  have hy : UcCl Z (ucI (ucLev E) E) := by
    by_cases hF : QcFixH (ucLev E) (ucI (ucLev E) E)
    · obtain ⟨-, -, hpy⟩ := qc_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      have hp := qs_cl_code hE hBE hEB hlim hIH hZ (hpy.trans hyE) (hgp.trans_lt hgZ)
      have ho := qs_cl_code hE hBE hEB hlim hIH hZ ((Ordinal.sub_le_self _ _).trans_lt hyE) (hgo.trans_lt hgZ)
      have h := UcCl.add (UcCl.add hp (UcCl.one hZ.1)) ho
      rwa [Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpy)] at h
    · exact qs_cl_code hE hBE hEB hlim hIH hZ hyE ((hg0y hF).trans_lt hgZ)
  have h := UcCl.hatom hlE hcomp hy (by rw [hFy]; exact hXE)
  rwa [hFy] at h

/-- **THE TOP DATA AT A FIXED POINT OF `Γ`**: the new segment base, read `qcA E` itself. -/
noncomputable def qsTopFix : QsTop E where
  Ei := E
  W := qcA E
  E_eq := zm_fix_of_gamma (qs_fx_dat hEB hXE hA hi).1
  Ei_cl := fun Z hZ hgZ => qs_fx_cl hE hBE hEB hXE hlim hIH hA hi hZ hgZ
  V_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hVT, hVE, -, hVX, -⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
    refine ⟨hVT, hVE, ?_, hVX⟩
    rw [(qs_fx_dat hEB hXE hA hi).2.2.2.2.2.2.2, vQ_base' hE (va_G_le_BG.trans hBE.le) hEB]
  Vq := fun x hx hx1 hgx => by
    obtain ⟨-, -, hVT, hVE, -, -, hV1⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
    rw [(qs_fx_dat hEB hXE hA hi).2.2.2.2.2.2.2, vQ_base' hE (va_G_le_BG.trans hBE.le) hEB]
    exact ⟨qcA E x, hVT, hV1, lt_add_of_pos_right _ hVE.pos, gmq_gt hx hx1 hVT hV1⟩
  W_T := fun x hx hx1 hgx => by
    obtain ⟨-, hcl, hVT, -, hxV, -, hV1⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
    exact ⟨hVT, hV1, vs_eN_cl hx hx1 hVT hV1 hxV hcl⟩
  V_pi := fun σ ρ hB hgσ => qs_fx_pi hE hBE hEB hXE hlim hIH hA hi hB hgσ
  W_pi := fun σ ρ hB hgσ => qs_fx_pi hE hBE hEB hXE hlim hIH hA hi hB hgσ
  lt := fun x hx hx1 hgx c hc hg => qs_fx_lt hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx c hc hg
  top := fun x hx hx1 hgx ν hν => qs_fx_top hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx ν hν
  B_cl := fun Z hZ hgZ => by
    rw [(qs_fx_dat hEB hXE hA hi).2.2.2.2.2.2.2]; exact qs_fx_cl hE hBE hEB hXE hlim hIH hA hi hZ hgZ
  D_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hVT, hVE, hxV, hVX, -⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
    rw [(qs_fx_dat hEB hXE hA hi).2.2.2.2.2.2.2, vQ_base' hE (va_G_le_BG.trans hBE.le) hEB]
    exact ⟨hVT, hVE, hxV, hVX⟩
  D_pi := fun σ ρ hB hgσ => by
    rw [(qs_fx_dat hEB hXE hA hi).2.2.2.2.2.2.2, vQ_base' hE (va_G_le_BG.trans hBE.le) hEB,
      vQ_base' hE (va_G_le_BG.trans hBE.le) hEB]
    exact qs_fx_pi hE hBE hEB hXE hlim hIH hA hi hB hgσ
  nc := fun c x hx hx1 hl hc hg => by
    have hgx : max ω (qcQE E) < x := (le_max_left _ _).trans_lt hg
    have hgc : qcG c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨-, -, hVT, -, -, -, hV1⟩ := qs_fx_V hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx
    rw [(qs_fx_dat hEB hXE hA hi).2.2.2.2.2.2.2, vQ_base' hE (va_G_le_BG.trans hBE.le) hEB]
    have h0 : vQ 0 x < vQ c x := qs_mono hE hBE hEB hlim hIH hx hx1 (pos_iff_ne_zero.2 hl.bot_lt.ne') hc
      (by rw [qcG_zero]; exact hx.pos) hgc
    rw [vQ_zero] at h0
    exact vs_nc_lt hx hx1 hVT hV1 h0 (qs_fx_lt hE hBE hEB hXE hlim hIH hA hi hx hx1 hgx c hc hgc)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qc
