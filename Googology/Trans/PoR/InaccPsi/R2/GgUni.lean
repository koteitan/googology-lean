import Googology.Trans.PoR.InaccPsi.R2.GgFix
import Googology.Trans.PoR.InaccPsi.R2.NnLev

/-!
# THE NOTATION STATEMENT AT EVERY FIXED POINT OF `υ` WITH A CODE UP TO `E`, BY ONE INDUCTION

`Θ_λ(m)` (`Cd.cdTheta`) is the order type of the codes of `Cl(A_{η_λ}, ρ_λ)` below `m`, `m_λ` the code
(`Cd.cdCode`), `e(η) = cdExp η` the last exponent, `O_X = xtOrec X`.

* `ggHull_iff`, `ggTheta_eq`, `ggCode_eq`, `ggSC_fix`, `ggExpMem`: at a named fixed point `F = υ_F`, the hull
  below `ggGam` is the set of codes over `F` (`Gg.ggCl_of_CSet`), so `Θ_F(m) = Θ^Gg_F(m)` (`Gg.ggTh`) for
  `m ≤ ggGam`, `m_F = e(η_F)` when `e(η_F) ≤ ggGam`, and `e(η_F)` is a code over `F`;
* `GgPoly X E` (**terms for the codes below `E`**): for every code `c < E` over `Z` some term of `X` has the value
  `Θ^Gg_y(c)` at every strongly critical `y < Ω₁` with `Z ≤ y`;
* `ggUni` (**THEOREM UNI**): for every term system `X` with `GgPoly X E`, `E ≤ ggGam`, every restart index
  `F = υ_F` with a name and `e(η_F) ≤ E` has `O_X(F) = Θ^Gg_F(e(η_F))`.  One induction on `F`:
  - `≥`: a code `c < e(η_F)` below `Ω₁` is a constant `c < F`, realized cofinally (`Nn.nn_const_cof`); a code
    `c ≥ Ω₁` is a code over some `Z < F` (`GgCl.support`), its term `s` is realized at the cofinal fixed points
    `μ` with `e(η_μ) = c` (`Gg.ggCof`), where `s(μ) = Θ_μ(c) = O_X(μ)` by the induction hypothesis;
  - `≤`: a term `s` realized cofinally is realized at a restart `μ` of the window `(ι(η₀), F)`; if `μ < υ_μ`,
    `O_X(μ) ≤ μ` and `s` is a constant; if `μ = υ_μ`, `s(μ) ≤ O_X(μ) = Θ_μ(e(η_μ))` with `e(η_μ) < e(η_F)`
    (`Gg.ggWin`), so `s(μ) = Θ_μ(c) = t_c(μ)` for a code `c ≤ e(η_μ)`, and by EXACT (`uni_le`) `s(F) = t_c(F) =
    Θ_F(c) < Θ_F(e(η_F))`;
* `ggUniTh` (the same with `Θ_F(m_F)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

theorem ggGam_lt_Om2 (S : InaccSeq.{0}) : ggGam < Om (1 + 1) :=
  (ggGam_le (SC_psi (InR_Om_succ 1) 0) (psiS_bounds (S := S) 0 1).1).trans_lt (psi_lt (InR_Om_succ 1) 0)

/-- A named fixed point of `υ` is strongly critical. -/
theorem ggSC_fix {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : SC F := by
  have := Pv_SC S (cdEta S F)
  rwa [cdEta_pv hF.1 hX, hfix] at this

/-- The key condition of the hull at a named restart: its countable members are below `ρ_F`. -/
theorem ggKey {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hX : upsilon F < Pv S ηx) :
    ∀ y ∈ cdHull S F, y < Om 1 → y < upsilon F := by
  intro y hy hy1
  have hpv := cdEta_pv hF.1 hX
  unfold cdHull at hy
  rw [← hpv] at hy ⊢
  exact lt_psi_of_mem Low.InR_Om_one hy hy1

/-- **At a named fixed point the hull below `ggGam` is the set of codes over `F`.** -/
theorem ggHull_iff {F ηx x : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hx : x < ggGam) : x ∈ cdHull S F ↔ GgCl F x := by
  constructor
  · intro h
    have h0 : 0 < upsilon F := by rw [hfix]; exact pos_iff_ne_zero.2 hF.1
    have := ggCl_of_CSet h0 (ggKey hF hX) x h hx
    rwa [hfix] at this
  · intro h
    exact h.mem_CSet (by rw [hfix])

/-- **`Θ_F(m) = Θ^Gg_F(m)`** for `m ≤ ggGam` at a named fixed point. -/
theorem ggTheta_eq {F ηx m : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hm : m ≤ ggGam) : cdTheta S F m = ggTh F m :=
  ggOtp_congr m fun _ hx => ggHull_iff hF hfix hX (hx.trans_le hm)

theorem gg_ww_lt {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) : ω * ω < F :=
  (cp_fix_facts hF hfix).2.2

/-- **`m_F = e(η_F)`** at a named fixed point with `e(η_F) ≤ ggGam`. -/
theorem ggCode_eq {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ ggGam) : cdCode S F = cdExp (cdEta S F) := by
  have hFe := Fx.fxExp_fix hF hfix hX
  have hω : ω ≤ cdExp (cdEta S F) :=
    ((le_mul_left _ omega0_pos).trans (gg_ww_lt hF hfix).le).trans hFe
  unfold cdCode
  rw [cdCodeOf_of_lt (he.trans_lt (ggGam_lt_Om2 S)), cpOff_of_ge hω]

/-- **The last exponent of the name of a named fixed point is a code over it** (when below `ggGam`). -/
theorem ggExpMem {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) < ggGam) : GgCl F (cdExp (cdEta S F)) := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmem : cdExp (cdEta S F) ∈ cdHull S F := by
    unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  exact (ggHull_iff hF hfix hX he).1 hmem

/-- **Terms for the codes below `E`**: for every code `c < E` over `Z` some term of `X` has the value `Θ^Gg_y(c)`
at every strongly critical `y < Ω₁` with `Z ≤ y`. -/
def GgPoly (X : XtSys) (E : Ordinal.{0}) : Prop :=
  ∀ Z c, GgCl Z c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y →
    X.CB s y ∧ X.val s y = ggTh y c

theorem gg_name_ne {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : cdEta S F ≠ 0 := by
  obtain ⟨-, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  intro h
  rw [h, iota_zero] at hι
  have h1 : (1 : Ordinal.{0}) < ω * ω := lt_of_lt_of_le one_lt_omega0 (le_mul_left _ omega0_pos)
  exact absurd (hι ▸ gg_ww_lt hF hfix) (not_lt.2 h1.le)

/-- **THEOREM UNI**: for every term system `X` with terms for the codes below `E ≤ ggGam`, every named restart
index `F = υ_F` with `e(η_F) ≤ E` has `O_X(F) = Θ^Gg_F(e(η_F))`. -/
theorem ggUni {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ ggGam) (hP : GgPoly X E) :
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
      obtain ⟨t, ht⟩ := hP μ c hcC hcE
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
        obtain ⟨s, hs⟩ := hP Z c.1 hcZ (c.2.trans_le heE)
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

/-- **THEOREM UNI with `Θ_F(m_F)`.** -/
theorem ggUniTh {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ ggGam) (hP : GgPoly X E) {F ηx : Ordinal.{0}}
    (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ E) :
    cdTheta S F (cdCode S F) = xtOrec X F := by
  rw [ggCode_eq hF hfix hX (he.trans hE), ggTheta_eq hF hfix hX (he.trans hE),
    ggUni hE hP F ηx hF hfix hX he]

end Googology.Trans.PoR.InaccPsi.R2.Gg
