import Googology.Trans.PoR.InaccPsi.R2.QdTopB2

/-!
# QdFxE: THE TOP DATA AT A FIXED POINT `E = Hᵛ_λ(y)` OF `Γ` IN `[B₂, B₃)` — THE NEW SEGMENT BASE

As `Qc.QcFxE` with the Veblen levels.  The reading `ϑˣ(Ω₁·(Ω₁+λ(x)) + K(x))` of `E` is exact: `π` commutes with `ϑ`
below `Ω₂` (`R2.pi_vt_two`), with sums (`R2.pi_add`), and with `Ω₁·λ(x)` (`qd_lv_pi`, by the clauses of the level:
a leaf by `R2.siOm1_mul_TB`, `Ω₂` by `R2.lgPi_OmOm`, an `ε`-number `λ(x) > Ω₁` is `Ω₁·λ(x)` itself and exact by
`Qd.qdLv_pi`, a Cantor clause `ω^{l(x)}·n + r(x)` by `R2.siOm1_opow_TB` for `l < E₂` and `Qd.qd_pi_opow` from `E₂`
on, where `Ω₁·ω^{l(x)} = ω^{l(x)}`).  `E` is a code (`Qd.QdCl.hatom`).  The cofinality is `Qd.qd_fx_top` above `B₂`
and `Qd.qd_B2_top` at `B₂`.

* `qd_exE` (the codes below `E` are exact), `qd_Om1_mul_eps`, `qd_lv_pi` (**the level readings are exact**),
  `qd_fx_pi` (**the reading of `E` is exact**), `qd_fx_cl`;
* `qdTopFix` (**THE TOP DATA AT A FIXED POINT OF `Γ`**, with Lemma IMG at the Veblen levels).

No new axiom.  New definition: `qdTopFix`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yw
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- `Ω₁·e = e` for an `ε`-number `e > Ω₁`. -/
theorem qd_Om1_mul_eps {e : Ordinal.{0}} (he : InE e) (h1 : Om1 < e) : Om1 * e = e :=
  calc Om1 * e = ω ^ Om1 * ω ^ e := by rw [rj_Om1_opow, he]
    _ = ω ^ (Om1 + e) := (opow_add _ _ _).symm
    _ = ω ^ e := by rw [add_eq_right_iff_mul_omega0_le.2 (he.mul_lt h1 (omega0_lt_inE he)).le]
    _ = e := he

variable (S : InaccSeq.{0})

section Lev

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)

include S hE hBE hEB hlim hIH

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **The codes below `E` are exact.** -/
theorem qd_exE {c : Ordinal.{0}} (hc : c < E) (hgc : qdGt c < σ) :
    vD c ρ ∈ TB ρ σ ∧ R2.pi σ ρ (vD c ρ) = vD c σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  obtain ⟨e, M, -, -, -, -, -, hcM, -, -, -, hEg, -, hR, hG, -, -⟩ := qd_mem S hEB hlim hIH hBE hc
  have hGc := qd_memG (omega0_lt_inE hB.1) hEg hgc hG hcM hgc
  rw [← hR c hcM ρ hB.2.1 hρ1 (hGc.trans hB.2.2.1), ← hR c hcM σ hB.1 hσ1 hGc]
  exact M.ex σ ρ c hB hcM hGc

/-- **The level readings are exact**: `Ω₁·λ(ρ) ∈ T^ρ[σ]` and `π(Ω₁·λ(ρ)) = Ω₁·λ(σ)` for a Veblen level with its leaves
codes below `E` with gates below `σ`. -/
theorem qd_lv_pi : ∀ γ : Ordinal.{0}, γ < qdG2 → (∀ d ∈ qdComps γ, d < E ∧ qdGt d < σ) →
    Om1 * qdLvx E γ ρ ∈ TB ρ σ ∧ R2.pi σ ρ (Om1 * qdLvx E γ ρ) = Om1 * qdLvx E γ σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  set fρ : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vD d ρ else 0 with hfρ
  set fσ : Ordinal.{0} → Ordinal.{0} := fun d => if d < E then vD d σ else 0 with hfσ
  set Dm : Ordinal.{0} → Prop := fun d => d < E ∧ qdGt d < σ with hDm
  have hE0 : (0 : Ordinal.{0}) < E := hE.pos
  have h1E : (1 : Ordinal.{0}) < E := lu_one_lt_E hE
  have hf0ρ : fρ 0 = 0 := by simp only [hfρ, if_pos hE0, vD_zero]
  have hf0σ : fσ 0 = 0 := by simp only [hfσ, if_pos hE0, vD_zero]
  have hf1ρ : fρ 1 = 1 := by simp only [hfρ, if_pos h1E, vD_one]
  have hf1σ : fσ 1 = 1 := by simp only [hfσ, if_pos h1E, vD_one]
  have hD0 : Dm 0 := ⟨hE0, by rw [qdGt_zero]; exact hB.1.pos⟩
  have hD1 : Dm 1 := ⟨h1E, by
    rw [show (1 : Ordinal.{0}) = ((1 : ℕ) : Ordinal.{0}) by norm_num, qdGt_nat]
    exact (natCast_lt_omega0 1).trans hωσ⟩
  have hfΩρ : ∀ d, Dm d → fρ d < Om1 := fun d hd => by
    simp only [hfρ, if_pos hd.1]
    exact (qd_T S hE hBE hEB hlim hIH hB.2.1 hρ1 hd.1 (hd.2.trans hB.2.2.1)).2.1
  have hfΩσ : ∀ d, Dm d → fσ d < Om1 := fun d hd => by
    simp only [hfσ, if_pos hd.1]
    exact (qd_T S hE hBE hEB hlim hIH hB.1 hσ1 hd.1 hd.2).2.1
  have hfmρ : ∀ d d', Dm d → Dm d' → d < d' → fρ d < fρ d' := fun d d' hd hd' hdd => by
    simp only [hfρ, if_pos hd.1, if_pos hd'.1]
    exact qd_mono S hE hBE hEB hlim hIH hB.2.1 hρ1 hdd hd'.1 (hd.2.trans hB.2.2.1) (hd'.2.trans hB.2.2.1)
  have hfmσ : ∀ d d', Dm d → Dm d' → d < d' → fσ d < fσ d' := fun d d' hd hd' hdd => by
    simp only [hfσ, if_pos hd.1, if_pos hd'.1]
    exact qd_mono S hE hBE hEB hlim hIH hB.1 hσ1 hdd hd'.1 hd.2 hd'.2
  have hex : ∀ d, Dm d → fρ d ∈ TB ρ σ ∧ R2.pi σ ρ (fρ d) = fσ d := fun d hd => by
    simp only [hfρ, hfσ, if_pos hd.1]
    exact qd_exE S hE hBE hEB hlim hIH hB hd.1 hd.2
  have hpi := qdLv_pi hB fρ fσ Dm hf0ρ hD0 hfΩρ hfmρ hex
  have hmainρ := qdLv_main fρ Dm hf0ρ hD0 hfΩρ hfmρ
  have hmainσ := qdLv_main fσ Dm hf0σ hD0 hfΩσ hfmσ
  have hcE : ∀ d ∈ qdComps ucE, Dm d := fun d hd => by rw [qdComps_E2 d hd]; exact hD1
  have hemp : ∀ d ∈ qdComps OmTwo, Dm d := by
    rw [qdComps_Om2]; exact fun _ h => absurd h (Set.notMem_empty _)
  -- the threshold `E₂`
  have hlowρ : ∀ l, l < ucE → (∀ d ∈ qdComps l, Dm d) → qdLv fρ l < ggE := fun l hl hlD => by
    rw [← qdLv_E2 fρ hf1ρ]; exact (hmainρ ucE qd_E_lt_G2 hcE).2.2.2.2.2 l hl hlD
  have hhigh : ∀ f : Ordinal.{0} → Ordinal.{0}, f 1 = 1 →
      (∀ z, z < qdG2 → (∀ d ∈ qdComps z, Dm d) → ∀ z', z' < z → (∀ d ∈ qdComps z', Dm d) →
        qdLv f z' < qdLv f z) →
      ∀ l, l < qdG2 → ucE ≤ l → (∀ d ∈ qdComps l, Dm d) → ggE ≤ qdLv f l := fun f hf1 hord l hlG hl hlD => by
    rw [← qdLv_E2 f hf1]
    rcases hl.lt_or_eq with h | h
    · exact (hord l hlG hlD ucE h hcE).le
    · rw [h]
  have hordρ : ∀ z, z < qdG2 → (∀ d ∈ qdComps z, Dm d) → ∀ z', z' < z → (∀ d ∈ qdComps z', Dm d) →
      qdLv fρ z' < qdLv fρ z := fun z hz hzD => (hmainρ z hz hzD).2.2.2.2.2
  have hordσ : ∀ z, z < qdG2 → (∀ d ∈ qdComps z, Dm d) → ∀ z', z' < z → (∀ d ∈ qdComps z', Dm d) →
      qdLv fσ z' < qdLv fσ z := fun z hz hzD => (hmainσ z hz hzD).2.2.2.2.2
  have e1 : ∀ L, ggE ≤ L → Om1 * ω ^ L = ω ^ L := fun L hL => by
    calc Om1 * ω ^ L = ω ^ Om1 * ω ^ L := by rw [rj_Om1_opow]
      _ = ω ^ (Om1 + L) := (opow_add _ _ _).symm
      _ = ω ^ L := by
        rw [add_eq_right_iff_mul_omega0_le.2 ((hgE.mul_lt hOE (omega0_lt_inE hgE)).le.trans hL)]
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγG hγD
  show Om1 * qdLv fρ γ ∈ TB ρ σ ∧ R2.pi σ ρ (Om1 * qdLv fρ γ) = Om1 * qdLv fσ γ
  rcases lt_trichotomy γ OmTwo with hγ2 | rfl | hγ2
  · -- a leaf
    have hd := hγD γ (by rw [qdComps_small hγ2]; exact mem_singleton _)
    rw [qdLv_small fρ hγ2, qdLv_small fσ hγ2]
    obtain ⟨h1, h2⟩ := hex γ hd
    obtain ⟨h3, h4⟩ := siOm1_mul_TB hB h1 (hfΩρ γ hd)
    exact ⟨h3, by rw [h4, h2]⟩
  · rw [qdLv_Om2, qdLv_Om2]; exact lgPi_OmOm hB
  by_cases hE' : ω ^ γ = γ
  · -- an `ε`-number: the readings are `ε`-numbers above `Ω₁`
    have hρE := (hmainρ γ hγG hγD).2.2.2.2.1 hγ2.le hE'
    have hσE := (hmainσ γ hγG hγD).2.2.2.2.1 hγ2.le hE'
    have hOρ : Om1 < qdLv fρ γ := by have h := hordρ γ hγG hγD OmTwo hγ2 hemp; rwa [qdLv_Om2] at h
    have hOσ : Om1 < qdLv fσ γ := by have h := hordσ γ hγG hγD OmTwo hγ2 hemp; rwa [qdLv_Om2] at h
    rw [qd_Om1_mul_eps hρE hOρ, qd_Om1_mul_eps hσE hOσ]
    exact hpi γ hγG hγD
  -- the Cantor clause `ω^l·n + r`
  obtain ⟨-, -, -, hnω, hl2, hlz⟩ := qd_cnf_parts hγ2 hE'
  have hrz : γ % ω ^ log ω γ < γ := rj_mod_lt (qd_Om2_pos.trans hγ2).ne'
  have hc := qdComps_cnf hγ2 hγG hE'
  have hlD : ∀ d ∈ qdComps (log ω γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inl hd)
  have hrD : ∀ d ∈ qdComps (γ % ω ^ log ω γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inr hd)
  have hlG : log ω γ < qdG2 := hlz.trans hγG
  obtain ⟨l1, l2⟩ := hpi (log ω γ) hlG hlD
  have hOl : Om1 ≤ qdLv fρ (log ω γ) := (hmainρ _ hlG hlD).2.2.2.1 hl2
  have hA : Om1 * ω ^ qdLv fρ (log ω γ) ∈ TB ρ σ ∧
      R2.pi σ ρ (Om1 * ω ^ qdLv fρ (log ω γ)) = Om1 * ω ^ qdLv fσ (log ω γ) := by
    rcases lt_or_ge (log ω γ) ucE with hlE | hlE
    · obtain ⟨i1, i2⟩ := siOm1_opow_TB hB (hlowρ _ hlE hlD)
      exact ⟨i1.2 l1, by rw [i2 l1, l2]⟩
    · have hLρ := hhigh fρ hf1ρ hordρ _ hlG hlE hlD
      have hLσ := hhigh fσ hf1σ hordσ _ hlG hlE hlD
      obtain ⟨o1, o2⟩ := qd_pi_opow hB l1 hOl (hmainρ _ hlG hlD).1
      rw [e1 _ hLρ, e1 _ hLσ]
      exact ⟨o1, by rw [o2, l2]⟩
  obtain ⟨k, hk⟩ := lt_omega0.1 hnω
  obtain ⟨m1, m2⟩ := pi_mul_nat hB hA.1 hA.2 k
  obtain ⟨r1, r2⟩ := IH _ hrz (hrz.trans hγG) hrD
  change Om1 * qdLv fρ (γ % ω ^ log ω γ) ∈ TB ρ σ at r1
  change R2.pi σ ρ (Om1 * qdLv fρ (γ % ω ^ log ω γ)) = Om1 * qdLv fσ (γ % ω ^ log ω γ) at r2
  obtain ⟨s1, s2⟩ := pi_add hB m1 r1
  rw [qdLv_cnf fρ hγ2 hγG hE', qdLv_cnf fσ hγ2 hγG hE', hk, mul_add, mul_add, ← mul_assoc, ← mul_assoc]
  exact ⟨s1, by rw [s2, m2, r2]⟩

end Lev

section Fix

variable {E : Ordinal.{0}} (hE : InE E) (hBE : tfBG < E) (hEB : E < qdB) (hXE : ucB ≤ E)
  (hlim : ∀ e, InE e → e < E → eN e < E) (hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e)
  (hA : YhAt E) (hi : ¬ yhJ E < E)

include S hE hBE hEB hXE hlim hIH hA hi

/-- **The reading of the fixed point is exact.** -/
theorem qd_fx_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (hgσ : max ω (qdQEt E) < σ) :
    qdA E ρ ∈ TB ρ σ ∧ R2.pi σ ρ (qdA E ρ) = qdA E σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hgρ := hgσ.trans hB.2.2.1
  obtain ⟨-, -, hlG, -, hyE, -, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨hcompσ, -, -, -, -, -, -⟩ := qd_fx_parts S hE hBE hEB hXE hlim hIH hA hi hB.1 hσ1 hgσ
  obtain ⟨-, -, hNG, -, -, hK1, -⟩ := qd_fx_parts S hE hBE hEB hXE hlim hIH hA hi hB.2.1 hρ1 hgρ
  obtain ⟨-, hgF, hg0y⟩ := qd_fix_gates S hA hi hXE hEB
  have hK : qdRK (qdLev E) (qdI (qdLev E) E) ρ ∈ TB ρ σ ∧
      R2.pi σ ρ (qdRK (qdLev E) (qdI (qdLev E) E) ρ) = qdRK (qdLev E) (qdI (qdLev E) E) σ := by
    unfold qdRK
    split_ifs with hF
    · obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      obtain ⟨f1, f2⟩ := qd_exE S hE hBE hEB hlim hIH hB (hpy.trans hyE) (hgp.trans_lt hgσ)
      obtain ⟨o1, o2⟩ := qd_exE S hE hBE hEB hlim hIH hB ((Ordinal.sub_le_self _ _).trans_lt hyE)
        (hgo.trans_lt hgσ)
      obtain ⟨s1, s2⟩ := pi_add hB f1 o1
      exact ⟨s1, by rw [s2, f2, o2]⟩
    · exact qd_exE S hE hBE hEB hlim hIH hB hyE ((hg0y hF).trans_lt hgσ)
  obtain ⟨l1, l2⟩ := qd_lv_pi S hE hBE hEB hlim hIH hB (qdLev E) hlG hcompσ
  obtain ⟨o1, o2⟩ := lgPi_OmOm hB
  have harg : ∀ x, Om1 * (Om1 + qdLvx E (qdLev E) x) + qdRK (qdLev E) (qdI (qdLev E) E) x =
      Om1 * Om1 + Om1 * qdLvx E (qdLev E) x + qdRK (qdLev E) (qdI (qdLev E) E) x := fun x => by rw [mul_add]
  obtain ⟨a1, a2⟩ := pi_add hB o1 l1
  obtain ⟨b1, b2⟩ := pi_add hB a1 hK.1
  have h2 := qd_arg_lt hNG hK1
  rw [harg ρ] at h2
  rw [qdA_fix S hA hi hXE hEB ρ, qdA_fix S hA hi hXE hEB σ, harg ρ, harg σ]
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hB.2.1 hρ1 b1.1 h2
  refine ⟨⟨hvT, by rw [hPar]; exact b1.2⟩, ?_⟩
  rw [pi_vt_two hB b1 h2, b2, a2, o2, l2, hK.2]

/-- **The fixed point is a code over every strongly critical `Z` above its gate.** -/
theorem qd_fx_cl {Z : Ordinal.{0}} (hZ : SC Z) (hgZ : max ω (qdQEt E) < Z) : QdCl Z E := by
  obtain ⟨-, -, hlG, hlc, hyE, hFy, hne, -⟩ := qd_fx_dat S hEB hXE hA hi
  obtain ⟨hgc, hgF, hg0y⟩ := qd_fix_gates S hA hi hXE hEB
  have hcomp : ∀ d ∈ qdComps (qdLev E), QdCl Z d := fun d hd =>
    qd_cl_code S hE hBE hEB hlim hIH hZ ((qdFold_lt_iff hE.pos _).1 hlc d hd) ((hgc d hd).trans_lt hgZ)
  have hy : QdCl Z (qdI (qdLev E) E) := by
    by_cases hF : QdFixH (qdLev E) (qdI (qdLev E) E)
    · obtain ⟨-, -, hpy⟩ := qd_fpH_mem hne hF
      obtain ⟨hgp, hgo⟩ := hgF hF
      have hp := qd_cl_code S hE hBE hEB hlim hIH hZ (hpy.trans hyE) (hgp.trans_lt hgZ)
      have ho := qd_cl_code S hE hBE hEB hlim hIH hZ ((Ordinal.sub_le_self _ _).trans_lt hyE) (hgo.trans_lt hgZ)
      have h := QdCl.add (QdCl.add hp (QdCl.one hZ.1)) ho
      rwa [Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hpy)] at h
    · exact qd_cl_code S hE hBE hEB hlim hIH hZ hyE ((hg0y hF).trans_lt hgZ)
  have h := QdCl.hatom hlG hcomp hy (by rw [hFy]; exact hXE)
  rwa [hFy] at h

/-- **THE TOP DATA AT A FIXED POINT OF `Γ`** in `[B₂, B₃)`: the new segment base, read `qdA E` itself (with Lemma IMG
at the Veblen levels). -/
noncomputable def qdTopFix (hI : QdImgH) : QdTop E where
  Ei := E
  W := qdA E
  E_eq := zm_fix_of_gamma (qd_fx_dat S hEB hXE hA hi).1
  Ei_cl := fun Z hZ hgZ => qd_fx_cl S hE hBE hEB hXE hlim hIH hA hi hZ hgZ
  V_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hVT, hVE, -, hVX, -⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
    refine ⟨hVT, hVE, ?_, hVX⟩
    rw [(qd_fx_dat S hEB hXE hA hi).2.2.2.2.2.2.2, vD_base' hE (va_G_le_BG.trans hBE.le) hEB]
  Vq := fun x hx hx1 hgx => by
    obtain ⟨-, -, hVT, hVE, -, -, hV1⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
    rw [(qd_fx_dat S hEB hXE hA hi).2.2.2.2.2.2.2, vD_base' hE (va_G_le_BG.trans hBE.le) hEB]
    exact ⟨qdA E x, hVT, hV1, lt_add_of_pos_right _ hVE.pos, gmq_gt hx hx1 hVT hV1⟩
  W_T := fun x hx hx1 hgx => by
    obtain ⟨-, hcl, hVT, -, hxV, -, hV1⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
    exact ⟨hVT, hV1, vs_eN_cl hx hx1 hVT hV1 hxV hcl⟩
  V_pi := fun σ ρ hB hgσ => qd_fx_pi S hE hBE hEB hXE hlim hIH hA hi hB hgσ
  W_pi := fun σ ρ hB hgσ => qd_fx_pi S hE hBE hEB hXE hlim hIH hA hi hB hgσ
  lt := fun x hx hx1 hgx c hc hg => qd_fx_lt S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx c hc hg
  top := fun x hx hx1 hgx ν hν => by
    rcases hXE.lt_or_eq with hBE2 | hBE2
    · exact qd_fx_top S hE hBE hEB hXE hlim hIH hA hi hx hx1 hBE2 hI hgx ν hν
    · rw [← hBE2, qd_B2_read S] at hν
      rw [← hBE2]
      obtain ⟨b, hb, hgb, hνb⟩ := qd_B2_top S hx hx1 ν hν
      exact ⟨b, hb, by rw [qdGt_low hb]; exact hgb, by rw [vD_low hb]; exact hνb⟩
  B_cl := fun Z hZ hgZ => by
    rw [(qd_fx_dat S hEB hXE hA hi).2.2.2.2.2.2.2]; exact qd_fx_cl S hE hBE hEB hXE hlim hIH hA hi hZ hgZ
  D_T := fun x hx hx1 hgx => by
    obtain ⟨-, -, hVT, hVE, hxV, hVX, -⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
    rw [(qd_fx_dat S hEB hXE hA hi).2.2.2.2.2.2.2, vD_base' hE (va_G_le_BG.trans hBE.le) hEB]
    exact ⟨hVT, hVE, hxV, hVX⟩
  D_pi := fun σ ρ hB hgσ => by
    rw [(qd_fx_dat S hEB hXE hA hi).2.2.2.2.2.2.2, vD_base' hE (va_G_le_BG.trans hBE.le) hEB,
      vD_base' hE (va_G_le_BG.trans hBE.le) hEB]
    exact qd_fx_pi S hE hBE hEB hXE hlim hIH hA hi hB hgσ
  nc := fun c x hx hx1 hl hc hg => by
    have hgx : max ω (qdQEt E) < x := (le_max_left _ _).trans_lt hg
    have hgc : qdGt c < x := (le_max_right _ _).trans_lt hg
    obtain ⟨-, -, hVT, -, -, -, hV1⟩ := qd_fx_V S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx
    rw [(qd_fx_dat S hEB hXE hA hi).2.2.2.2.2.2.2, vD_base' hE (va_G_le_BG.trans hBE.le) hEB]
    have h0 : vD 0 x < vD c x := qd_mono S hE hBE hEB hlim hIH hx hx1 (pos_iff_ne_zero.2 hl.bot_lt.ne') hc
      (by rw [qdGt_zero]; exact hx.pos) hgc
    rw [vD_zero] at h0
    exact vs_nc_lt hx hx1 hVT hV1 h0 (qd_fx_lt S hE hBE hEB hXE hlim hIH hA hi hx hx1 hI hgx c hc hgc)

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Qd
