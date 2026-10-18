import Googology.Trans.PoR.InaccPsi.R2.PhLL

/-!
# THEOREM UNI with a reference base, and its instances up to the top codes

`PhPolyR X E` (**terms for the codes below `E` given a reference base**) is `Gg.GgPoly X E` asked only for the
`Z` below some strongly critical `υ`-point `ρ < Ω₁`; at such a `ρ` the comparison of two terms is the comparison of
their codes, and Lemma EXACT moves it to every `υ`-point base (this is what the decreasing exponent lists of
`Ly.lyEB` need).  `GgPoly X E` gives `PhPolyR X E` (`phPolyR_of`).

* `phUni` (**THEOREM UNI**, `Gg.ggUni` with `PhPolyR`): `E ≤ ggGam`, `PhPolyR X E`, `F = υ_F` a named restart index
  with `e(η_F) ≤ E` ⟹ `O_X(F) = Θ_F(e(η_F))`; `phUniTh` (the same with `Θ_F(m_F)`);
* `ph_cl_lt_Gam` (every code over `Z ≤ ggGam` is below `ggGam`);
* `phVz`, `phVzO` (**`Θ_F(m_F) = VzOrec(F) = Θ_F(e(η_F))` at every named fixed point with
  `e(η_F) ≤ phB = φ(ω, Ω₁ + 1)`**), `phLL`, `phLLO` (**`Θ_F(m_F) = O_{LL k}(F)` with `e(η_F) ≤ ω^{phB + Ω₁·ω·k}`**),
  `phLLiterO` (the layers `(xtLL k).iter n`, `e(η_F) ≤ ω^{phB + Ω₁·ω·k + Ω₁·n}`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- **Terms for the codes below `E`, given a reference base**: `GgPoly X E` asked only for the `Z` below some
strongly critical `υ`-point `ρ < Ω₁`. -/
def PhPolyR (X : XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GgCl Z c → c < E → (∃ ρ, UpsPt ρ ∧ SC ρ ∧ ρ < Om 1 ∧ Z ≤ ρ) → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = ggTh y c

theorem phPolyR_of {X : XtSys} {E : Ordinal.{0}} (h : GgPoly X E) : PhPolyR X E :=
  fun Z c hc hcE _ => h Z c hc hcE

/-- **Reduction to strongly critical `Z`** for `PhPolyR`. -/
theorem phPolyR_of_SC {X : XtSys} {E : Ordinal.{0}}
    (h : ∀ Z, SC Z → Z < Om 1 → (∃ ρ, UpsPt ρ ∧ SC ρ ∧ ρ < Om 1 ∧ Z ≤ ρ) → ∀ c, GgCl Z c → c < E →
      ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y → X.CB s y ∧ X.val s y = ggTh y c) : PhPolyR X E := by
  intro Z c hc hcE hρ
  obtain ⟨ρ, hρU, hρS, hρ1, hZρ⟩ := hρ
  have hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y := ⟨ρ, hρS, hρ1, hZρ⟩
  have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
  obtain ⟨h1, h2, h3⟩ := hmem
  obtain ⟨s, hs⟩ := h _ h1 h2 ⟨ρ, hρU, hρS, hρ1, csInf_le' ⟨hρS, hρ1, hZρ⟩⟩ c (hc.mono h3) hcE
  exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)⟩

theorem phUni {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ ggGam) (hP : PhPolyR X E) :
    ∀ F ηx, IsRestartIdx F → upsilon F = F → upsilon F < Pv S ηx → cdExp (cdEta S F) ≤ E →
      xtOrec X F = ggTh F (cdExp (cdEta S F)) := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro ηx hF hfix hX heE
  have hF1 : F < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have hF1' : F < Om1 := by rw [Br.Om1_eq]; exact hF1
  have hSC : SC F := ggSC_fix hF hfix hX
  have hww := gg_ww_lt hF hfix
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp (gg_name_ne hF hfix hX)
  obtain ⟨hwin0, hwin⟩ := ggWin hF hX hdec hd
  have hFe : F ≤ cdExp (cdEta S F) := Fx.fxExp_fix hF hfix hX
  have hFth : F ≤ ggTh F (cdExp (cdEta S F)) := by
    calc F = ggTh F F := (ggTh_small le_rfl).symm
      _ ≤ _ := ggTh_mono hFe
  -- the named fixed points below `F`
  have hfx : ∀ μ, IsRestartIdx μ → upsilon μ = μ → μ < F →
      upsilon μ < Pv S ηx ∧ SC μ ∧ UpsPt μ := by
    intro μ hμ hfixμ h2
    have hXμ : upsilon μ < Pv S ηx := (upsilon_normal.strictMono h2).trans hX
    refine ⟨hXμ, ggSC_fix hμ hfixμ hXμ, ?_⟩
    have := upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)
    rwa [hfixμ] at this
  have hUF : UpsPt F := by
    have := upsPt_upsilon (pos_iff_ne_zero.2 hF.1)
    rwa [hfix] at this
  apply le_antisymm
  · -- `O_X(F) ≤ Θ_F(e(η_F))`
    refine xtOrec_le_of ((Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le hww)).trans hFth)
      fun s hCB hc => ?_
    have hνF : max (iota S η0) (ω * ω) < F := max_lt hwin0 hww
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc _ hνF
    have hww' : ω * ω < μ := (le_max_right _ _).trans_lt h1
    have hw0 : iota S η0 < μ := (le_max_left _ _).trans_lt h1
    have hμ1 : μ < Om1 := h2.trans hF1'
    rcases (upsilon_normal.strictMono.le_apply : μ ≤ upsilon μ).lt_or_eq with hnf | hfxe
    · have hO := xtNonfix (X := X) hμ hww' hnf hμ1
      have hle : X.val s (upsilon μ) ≤ μ := by
        rw [hO] at hsμ; exact hsμ.trans ((cdOff_le _).trans (cpExp_le hμ.1))
      rw [xt_const_of_small (ups_inE hμ) (ups_lt_Om1 _ hμ1) hCBμ (hle.trans_lt hnf) (upsilon F)]
      exact (hle.trans_lt h2).trans_le hFth
    · have hfixμ : upsilon μ = μ := hfxe.symm
      obtain ⟨hXμ, hSCμ, hUμ⟩ := hfx μ hμ hfixμ h2
      have heμ : cdExp (cdEta S μ) < cdExp (cdEta S F) := hwin μ hμ hw0 h2
      have hOμ := IH μ h2 ηx hμ hfixμ hXμ (heμ.le.trans heE)
      rw [hfixμ] at hCBμ hsμ
      rw [hOμ] at hsμ
      have hmem : GgCl μ (cdExp (cdEta S μ)) :=
        ggExpMem hμ hfixμ hXμ ((heμ.trans_le heE).trans_le hE)
      obtain ⟨c, hcC, hcle, hcv⟩ := ggTh_le_onto hmem hsμ
      have hcE : c < E := (hcle.trans_lt heμ).trans_le heE
      obtain ⟨t, ht⟩ := hP μ c hcC hcE ⟨μ, hUμ, hSCμ, h2.trans hF1, le_rfl⟩
      obtain ⟨htCBμ, htμ⟩ := ht μ hSCμ (h2.trans hF1) le_rfl
      obtain ⟨-, htF⟩ := ht F hSC hF1 h2.le
      have hB : Bases μ F := ⟨upsPt_inE hUμ, upsPt_inE hUF, h2, hF1'⟩
      have e1 := X.uni_le μ F hUμ hUF hB t s htCBμ hCBμ
      have e2 := X.uni_le μ F hUμ hUF hB s t hCBμ htCBμ
      have hsF : X.val s F = X.val t F :=
        le_antisymm (e2.2 (by rw [htμ, hcv])) (e1.2 (by rw [htμ, hcv]))
      rw [hfix, hsF, htF]
      exact ggTh_lt (hcC.mono h2.le) (hcle.trans_lt heμ)
  · -- `Θ_F(e(η_F)) ≤ O_X(F)`
    classical
    unfold ggTh
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    by_cases hcC : c.1 ∈ ggSet F
    · rw [if_pos hcC]
      refine Order.add_one_le_of_lt ?_
      have hcC' : GgCl F c.1 := hcC
      rcases lt_or_ge c.1 (Om 1) with hcO | hcO
      · have hcF : c.1 < F := hcC'.lt_of_lt_Om1 hSC hcO
        have h1 := lt_xtOrec_of_cof hF hF1' (X.cb_cstI _ _ (by rw [hfix]; exact hcF))
          (Nn.nn_const_cof (X := X) hF hfix hF1' hcF)
        rw [X.val_cst] at h1
        show ggTh F c.1 < _
        rw [ggTh_small hcF.le]; exact h1
      · obtain ⟨Z, hZF, hcZ⟩ := hcC'.support hSC
        obtain ⟨s, hs⟩ := hP Z c.1 hcZ (c.2.trans_le heE) ⟨F, hUF, hSC, hF1, hZF.le⟩
        obtain ⟨hsCB, hsv⟩ := hs F hSC hF1 hZF.le
        have hcof : XtCof X (xtOrec X) F s := by
          intro ν hν
          obtain ⟨μ, hμ, hfixμ, h1, h2, hZμ, hexp⟩ := ggCof hF hfix hX hcZ hcO c.2 hZF hν
          obtain ⟨hXμ, hSCμ, -⟩ := hfx μ hμ hfixμ h2
          have hOμ := IH μ h2 ηx hμ hfixμ hXμ (by rw [hexp]; exact c.2.le.trans heE)
          obtain ⟨hCBμ, hvμ⟩ := hs μ hSCμ (h2.trans hF1) hZμ
          refine ⟨μ, hμ, h1, h2, by rw [hfixμ]; exact hCBμ, ?_⟩
          rw [hfixμ, hvμ, hOμ, hexp]
        have h1 := lt_xtOrec_of_cof hF hF1' (by rw [hfix]; exact hsCB) hcof
        rw [hfix, hsv] at h1
        exact h1
    · rw [if_neg hcC]; exact zero_le

/-- **THEOREM UNI with `Θ_F(m_F)`** (reference-base version). -/
theorem phUniTh {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ ggGam) (hP : PhPolyR X E) {F ηx : Ordinal.{0}}
    (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ E) :
    cdTheta S F (cdCode S F) = xtOrec X F := by
  rw [ggCode_eq hF hfix hX (he.trans hE), ggTheta_eq hF hfix hX (he.trans hE),
    phUni hE hP F ηx hF hfix hX he]

/-- Every code over `Z ≤ ggGam` is below `ggGam`. -/
theorem ph_cl_lt_Gam {Z : Ordinal.{0}} (hZ : Z ≤ ggGam) {c : Ordinal.{0}} (hc : GgCl Z c) : c < ggGam := by
  induction hc with
  | small h => exact h.trans_le hZ
  | om => exact ggGam_spec.2
  | add _ _ ihu ihv => exact ggGam_spec.1.isPrincipal ihu ihv
  | phi _ _ iha ihb => exact ggGam_spec.1.2 _ iha _ ihb

/-- The codes over `Ω₁` are below `ggGam`. -/
theorem ph_lt_Gam {c : Ordinal.{0}} (hc : GgCl (Om 1) c) : c < ggGam := ph_cl_lt_Gam ggGam_spec.2.le hc

theorem ph_B_lt_Gam : phB < ggGam := ph_lt_Gam (ph_cl_B ph_SC_Om1)

theorem ph_LL_lt_Gam (k : ℕ) : ω ^ phLLe k < ggGam := ph_lt_Gam (GgCl.opow ph_SC_Om1.1 (ph_cl_LLe k ph_SC_Om1))

theorem ph_LLiter_lt_Gam (k n : ℕ) : ω ^ (phLLe k + Om 1 * n) < ggGam :=
  ph_lt_Gam (GgCl.opow ph_SC_Om1.1 (GgCl.add (ph_cl_LLe k ph_SC_Om1) (GgCl.mul_nat ph_SC_Om1.1 GgCl.om n)))

/-- **THEOREM UNI for `VzOrec` up to `phB`**: `Θ_F(m_F) = VzOrec(F)` at every named fixed point `F` with
`e(η_F) ≤ phB = φ(ω, Ω₁ + 1)`. -/
theorem phVz {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phB) : cdTheta S F (cdCode S F) = VzOrec F := by
  rw [← xtVz_orec]; exact ggUniTh ph_B_lt_Gam.le phPoly_vz hF hfix hX he

/-- **`O_{vzSys}(F) = Θ_F(e(η_F))`** at every named fixed point with `e(η_F) ≤ phB`. -/
theorem phVzO {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phB) : VzOrec F = ggTh F (cdExp (cdEta S F)) := by
  rw [← xtVz_orec]; exact ggUni ph_B_lt_Gam.le phPoly_vz F ηx hF hfix hX he

/-- **THEOREM UNI for `xtLL k` up to the code of its top.** -/
theorem phLL (k : ℕ) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ ω ^ phLLe k) :
    cdTheta S F (cdCode S F) = xtOrec (xtLL k).sys F :=
  ggUniTh (ph_LL_lt_Gam k).le (phPoly_LL k).1 hF hfix hX he

theorem phLLO (k : ℕ) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ ω ^ phLLe k) :
    xtOrec (xtLL k).sys F = ggTh F (cdExp (cdEta S F)) :=
  ggUni (ph_LL_lt_Gam k).le (phPoly_LL k).1 F ηx hF hfix hX he

/-- **THEOREM UNI for `(xtLL k).iter n` up to the code of its top.** -/
theorem phLLiterO (k n : ℕ) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ ω ^ (phLLe k + Om 1 * n)) :
    xtOrec ((xtLL k).iter n).sys F = ggTh F (cdExp (cdEta S F)) :=
  ggUni (ph_LLiter_lt_Gam k n).le (phPoly_LLiter k n).1 F ηx hF hfix hX he

end Googology.Trans.PoR.InaccPsi.R2.Ph
