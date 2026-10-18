import Googology.Trans.PoR.InaccPsi.R2.NnLev

/-!
# The generic offset at the `Γ`-points that are not fixed points of `GG`, and `O(F) ≥ F·F + F` at the fixed points
of `GG`

`GG` enumerates `{0} ∪ {Γ-points}` (`R2.OffG2`), `invGG F` the index of a `Γ`-point.  For every term system `X` with
linear and square terms (`NnLin X`, `NnSq X`), `O = xtOrec X`:

* `nnGG` (**THEOREM GG at every height**): at every restart `F < Ω₁` that is a `Γ`-point with `GG(F) ≠ F`,
  **`O(F) = F·F + logend(a)`**, `F = GG(a)`.  (Upper bound: a term realized at a point `μ` near `F` is a constant,
  or below `μ·(γ_μ + 1)`, `γ_μ < μ`, at a point that is not a `Γ`-point (Theorem LEVEL), or below
  `μ·μ + logend(a)` at a `Γ`-point `μ = GG(a_μ)`, `a₀ < a_μ < a`.  Lower bound: `nnGam`, and `x·x + d`,
  `d < logend(a)`, realized at the `Γ`-points `GG(β)`, `ω^d ∣ β`.)  This is `R2.Nm.Orec_GG_eq` (there below `Φ_Γ`,
  for `R2.Orec`) at every height below `Ω₁`, for every such term system;
* `nnPhi` (**the fixed points of `GG`**): at every restart `F < Ω₁` with `GG(F) = F`, `F·F + F ≤ O(F)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable {X : XtSys}

theorem nn_gp_fix {F : Ordinal.{0}} (hG : IsGP F) : upsilon F = F := by
  have := hG.2 0 hG.1; rwa [VG_zero] at this

theorem nn_GG_inv {F : Ordinal.{0}} (hG : IsGP F) : GG (invGG F) = F := by
  obtain ⟨α, hα⟩ := GG_surj hG
  rw [← hα, invGG_GG]

/-- The `GG`-fixed points below `F = GG(a)` lie below `a`. -/
theorem nn_GG_le {F a μ : Ordinal.{0}} (hV : GG a = F) (hμF : μ < F) (haμ : a < μ) : GG μ ≠ μ := by
  intro h
  have : GG μ < GG a := by rw [h, hV]; exact hμF
  exact absurd (GG_strictMono.lt_iff_lt.1 this) (not_lt.2 haμ.le)

/-- The offset at the `Γ`-points below `F` that are not fixed points of `GG`. -/
def NnGGBelow (X : XtSys) (F : Ordinal.{0}) : Prop :=
  ∀ μ < F, IsRestartIdx μ → μ < Om1 → IsGP μ → GG μ ≠ μ → xtOrec X μ = μ * μ + lg (invGG μ)

/-- **`x·x + d` is realized cofinally below a `Γ`-point `F = GG(B)`** (`B` a limit) at the `Γ`-points `GG(β)`,
`β < B`, `ω^d ∣ β`, that are not fixed points of `GG` (`hstep`: such `β` exist cofinally, non-fixed once
`GG(β) > b'`). -/
theorem nn_cof_sq {F B b' d : Ordinal.{0}} (hF1 : F < Om1)
    (hO : NnGGBelow X F) (hV : GG B = F) (hBlim : IsSuccLimit B) (hb' : b' < F)
    (hstep : ∀ β1, β1 < B → ∃ β, β1 < β ∧ β < B ∧ ω ^ d ∣ β ∧ (b' < GG β → GG (GG β) ≠ GG β))
    (hdF : d < F) (s : X.Tm) (hs : ∀ y, UpsPt y → y < Om1 → d < y → X.CB s y ∧ X.val s y = y * y + d) :
    XtCof X (xtOrec X) F s := by
  intro ν hν
  set ν' := max (max ν d) b' with hν'
  have hν'F : ν' < F := max_lt (max_lt hν hdF) hb'
  obtain ⟨β1, hβ1B, hνβ1⟩ := (GG_normal.lt_iff_exists_lt hBlim).1 (show ν' < GG B by rw [hV]; exact hν'F)
  obtain ⟨β, hβ1β, hβB, hdvd, hwin⟩ := hstep β1 hβ1B
  have hβpos : 0 < β := lt_of_le_of_lt zero_le hβ1β
  set μ := GG β with hμ
  have hμF : μ < F := by rw [hμ, ← hV]; exact GG_strictMono hβB
  have hν'μ : ν' < μ := hνβ1.trans (GG_strictMono hβ1β)
  have hμG : IsGP μ := isGP_GG hβpos
  have hμfix : upsilon μ = μ := nn_gp_fix hμG
  have hμ0 : 0 < μ := hμG.1
  have hμr : IsRestartIdx μ := ri_of_fp hμ0 hμfix
  have hμ1 : μ < Om1 := hμF.trans hF1
  have hμne : GG μ ≠ μ := hwin ((le_max_right _ _).trans_lt hν'μ)
  have hOμ := hO μ hμF hμr hμ1 hμG hμne
  rw [hμ, invGG_GG, ← hμ] at hOμ
  have hdβ : d ≤ lg β := cdExp_max hβpos.ne' hdvd
  have hdμ : d < μ := ((le_max_right ν d).trans (le_max_left _ _)).trans_lt hν'μ
  obtain ⟨hCB, hval⟩ := hs μ (hμfix ▸ upsPt_upsilon hμ0) hμ1 hdμ
  refine ⟨μ, hμr, ((le_max_left ν d).trans (le_max_left _ _)).trans_lt hν'μ, hμF, ?_, ?_⟩
  · rw [hμfix]; exact hCB
  · rw [hμfix, hval, hOμ]; exact (add_le_add_iff_left _).2 hdβ

/-- The bound carried from a point `μ` near `F` to `F`, by the comparison of terms. -/
theorem nn_carry {μ F : Ordinal.{0}} (hUμ : UpsPt μ) (hU : UpsPt F) (hB : Bases μ F) {s u : X.Tm}
    (hsCB : X.CB s μ) (huCB : X.CB u μ) (hlt : X.val s μ < X.val u μ) : X.val s F < X.val u F := by
  by_contra hge
  push Not at hge
  exact absurd ((X.uni_le μ F hUμ hU hB u s huCB hsCB).1 hge) (not_le.2 hlt)

/-- **THEOREM GG at every height**: at a restart `F < Ω₁` that is a `Γ`-point with `GG(F) ≠ F`,
`O(F) = F·F + logend(a)`, `F = GG(a)`. -/
theorem nnGG (hX : NnLin X) (hS : NnSq X) : ∀ F, IsRestartIdx F → F < Om1 → IsGP F → GG F ≠ F →
    xtOrec X F = F * F + lg (invGG F) := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro hF hF1 hG hGF
  have hfix := nn_gp_fix hG
  obtain ⟨hE, hp, hww, hlim, hU⟩ := nn_fix_facts hF hfix
  have hF0 : 0 < F := hE.pos
  have hO : NnGGBelow X F := fun μ hμ hμr hμ1 hμG hμne => IH μ hμ hμr hμ1 hμG hμne
  set a := invGG F with ha
  have hV : GG a = F := nn_GG_inv hG
  have ha0 : a ≠ 0 := by intro h0; rw [h0, GG_zero] at hV; exact hF0.ne hV
  have haF : a < F := by
    refine lt_of_le_of_ne (by have := GG_strictMono.id_le a; rwa [hV] at this) fun e => ?_
    rw [e] at hV; exact hGF hV
  have hlgF : lg a < F := (lg_le ha0).trans_lt haF
  obtain ⟨a0, hdec, hdva⟩ := cdExp_decomp ha0
  have ha0a : a0 < a := by
    conv_rhs => rw [hdec]
    exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hGa0 : GG a0 < F := by rw [← hV]; exact GG_strictMono ha0a
  refine le_antisymm ?_ ?_
  · -- the upper bound
    have hY1 : 1 ≤ F * F + lg a :=
      (Order.one_le_iff_pos.2 hF0).trans ((le_mul_left F hF0).trans le_self_add)
    refine xtOrec_le_of hY1 fun s hCB hc => ?_
    rw [hfix] at hCB ⊢
    set ν0 := max (max a (GG a0)) (ω * ω) with hν0
    have hν0F : ν0 < F := max_lt (max_lt haF hGa0) hww
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc ν0 hν0F
    have hμ1 : μ < Om1 := h2.trans hF1
    have hμ0 : 0 < μ := lt_of_le_of_lt zero_le h1
    rcases (upsilon_normal.strictMono.le_apply : μ ≤ upsilon μ).lt_or_eq with hnf | hfx
    · have hwwμ : ω * ω < μ := (le_max_right _ _).trans_lt h1
      have hOμ := xtNonfix (X := X) hμ hwwμ hnf hμ1
      have hle : X.val s (upsilon μ) ≤ μ := (hsμ.trans_eq hOμ).trans ((cdOff_le _).trans (cpExp_le hμ.1))
      rw [xt_const_of_small (ups_inE hμ) (ups_lt_Om1 μ hμ1) hCBμ (hle.trans_lt hnf) F]
      exact (hle.trans_lt h2).trans_le ((le_mul_left F hF0).trans le_self_add)
    · have hμfix : upsilon μ = μ := hfx.symm
      rw [hμfix] at hCBμ hsμ
      obtain ⟨hEμ, -, -, hlimμ, hUμ⟩ := nn_fix_facts hμ hμfix
      have hBases : Bases μ F := ⟨hEμ, hE, h2, hF1⟩
      have haμ : a < μ := ((le_max_left a (GG a0)).trans (le_max_left _ _)).trans_lt h1
      by_cases hμG : IsGP μ
      · -- a `Γ`-point `μ = GG(a_μ)`, `a₀ < a_μ < a`
        have hμne : GG μ ≠ μ := nn_GG_le hV h2 haμ
        have hOμ := IH μ h2 hμ hμ1 hμG hμne
        have hVμ : GG (invGG μ) = μ := nn_GG_inv hμG
        have haμa : invGG μ < a := by
          have : GG (invGG μ) < GG a := by rw [hVμ, hV]; exact h2
          exact GG_strictMono.lt_iff_lt.1 this
        have ha0aμ : a0 < invGG μ := by
          have : GG a0 < GG (invGG μ) := by
            rw [hVμ]; exact ((le_max_right a (GG a0)).trans (le_max_left _ _)).trans_lt h1
          exact GG_strictMono.lt_iff_lt.1 this
        have hwin := cdWin hdva ha0aμ (hdec ▸ haμa)
        obtain ⟨u, hu⟩ := hS (lg a)
        obtain ⟨huCB, huval⟩ := hu μ hUμ hμ1 ((lg_le ha0).trans_lt haμ)
        obtain ⟨-, huvalF⟩ := hu F hU hF1 hlgF
        have hlt' : X.val s μ < X.val u μ := by
          rw [huval]
          calc X.val s μ ≤ xtOrec X μ := hsμ
            _ = μ * μ + lg (invGG μ) := hOμ
            _ < μ * μ + lg a := (add_lt_add_iff_left _).2 hwin.1
        have := nn_carry hUμ hU hBases hCBμ huCB hlt'
        rwa [huvalF] at this
      · -- not a `Γ`-point: Theorem LEVEL
        have hOμ := nnLev hX μ hμ hμ1 hμfix hμG
        obtain ⟨-, hγμμ, -, hαμ0, hαμμ, -, -⟩ := nn_lev_data hμfix (nn_ng_of_gp hμ0 hμG)
        have hlgμ : lg (invG (levG μ) μ) < μ := (lg_le hαμ0).trans_lt hαμμ
        obtain ⟨u, hu⟩ := hX (levG μ + 1) 0
        obtain ⟨huCB, huval⟩ := hu μ hUμ hμ1 (hlimμ.add_one_lt hγμμ) hμ0
        have hγF : levG μ + 1 < F := hlim.add_one_lt (hγμμ.trans h2)
        obtain ⟨-, huvalF⟩ := hu F hU hF1 hγF hF0
        have hlt' : X.val s μ < X.val u μ := by
          rw [huval, add_zero, mul_add_one]
          calc X.val s μ ≤ xtOrec X μ := hsμ
            _ = μ * levG μ + lg (invG (levG μ) μ) := hOμ
            _ < μ * levG μ + μ := (add_lt_add_iff_left _).2 hlgμ
        have := nn_carry hUμ hU hBases hCBμ huCB hlt'
        rw [huvalF, add_zero] at this
        calc X.val s F < F * (levG μ + 1) := this
          _ ≤ F * F := mul_le_mul_right hγF.le F
          _ ≤ F * F + lg a := le_self_add
  · -- the lower bound
    refine le_of_forall_lt fun v hv => ?_
    by_cases hvF : v < F * F
    · exact hvF.trans_le (nnGam hX hF hF1 hfix hG)
    · push Not at hvF
      set d := v - F * F with hd
      have hdv : F * F + d = v := Ordinal.add_sub_cancel_of_le hvF
      have hdlt : d < lg a := (sub_lt_of_le hvF).2 hv
      have hdF : d < F := hdlt.trans hlgF
      have he0 : cdExp a ≠ 0 := (lt_of_le_of_lt zero_le hdlt).ne'
      have hω : ω ∣ ω ^ cdExp a := by
        have := opow_dvd_opow ω (Order.one_le_iff_ne_zero.2 he0); rwa [opow_one] at this
      have halim : IsSuccLimit a :=
        Ordinal.isSuccLimit_iff.2 ⟨ha0, isSuccPrelimit_iff_omega0_dvd.2 (by rw [hdec]; exact dvd_add (hω.trans hdva) hω)⟩
      obtain ⟨s, hs⟩ := hS d
      have hstep : ∀ β1, β1 < a → ∃ β, β1 < β ∧ β < a ∧ ω ^ d ∣ β ∧ (a < GG β → GG (GG β) ≠ GG β) := by
        intro β1 hβ1
        have hα01 : a0 + 1 < a := halim.add_one_lt ha0a
        set β0 := max β1 (a0 + 1) with hβ0
        have hβ0a : β0 < a := max_lt hβ1 hα01
        have hpd : ω ^ d ≠ 0 := (opow_pos _ omega0_pos).ne'
        refine ⟨ω ^ d * (β0 / ω ^ d + 1), ?_, ?_, dvd_mul_right _ _, fun h => ?_⟩
        · exact (le_max_left β1 (a0 + 1)).trans_lt (by rw [mul_add_one]; exact lt_mul_div_add β0 hpd)
        · obtain ⟨w, hw⟩ := exists_add_of_le (show a0 ≤ β0 from
            ((lt_add_one a0).trans_le (le_max_right β1 (a0 + 1))).le)
          have hwe : w < ω ^ cdExp a := by
            have : a0 + w < a0 + ω ^ cdExp a := by rw [← hw, ← hdec]; exact hβ0a
            exact (add_lt_add_iff_left _).1 this
          have hde' : ω ^ d < ω ^ cdExp a := (opow_lt_opow_iff_right one_lt_omega0).2 hdlt
          calc ω ^ d * (β0 / ω ^ d + 1) ≤ β0 + ω ^ d := by
                rw [mul_add_one]; exact add_le_add (mul_div_le β0 _) le_rfl
            _ = a0 + (w + ω ^ d) := by rw [hw, add_assoc]
            _ < a0 + ω ^ cdExp a := (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow _ hwe hde')
            _ = a := hdec.symm
        · refine nn_GG_le hV ?_ h
          rw [← hV]
          refine GG_strictMono ?_
          obtain ⟨w, hw⟩ := exists_add_of_le (show a0 ≤ β0 from
            ((lt_add_one a0).trans_le (le_max_right β1 (a0 + 1))).le)
          have hwe : w < ω ^ cdExp a := by
            have : a0 + w < a0 + ω ^ cdExp a := by rw [← hw, ← hdec]; exact hβ0a
            exact (add_lt_add_iff_left _).1 this
          have hde' : ω ^ d < ω ^ cdExp a := (opow_lt_opow_iff_right one_lt_omega0).2 hdlt
          calc ω ^ d * (β0 / ω ^ d + 1) ≤ β0 + ω ^ d := by
                rw [mul_add_one]; exact add_le_add (mul_div_le β0 _) le_rfl
            _ = a0 + (w + ω ^ d) := by rw [hw, add_assoc]
            _ < a0 + ω ^ cdExp a := (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow _ hwe hde')
            _ = a := hdec.symm
      have hcof := nn_cof_sq hF1 hO hV halim haF hstep hdF s hs
      obtain ⟨hCB, hval⟩ := hs F hU hF1 hdF
      have := lt_xtOrec_of_cof hF hF1 (by rw [hfix]; exact hCB) hcof
      rwa [hfix, hval, hdv] at this

/-- **The fixed points of `GG`**: `F·F + F ≤ O(F)` at every restart `F < Ω₁` with `GG(F) = F`. -/
theorem nnPhi (hX : NnLin X) (hS : NnSq X) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1)
    (hGF : GG F = F) : F * F + F ≤ xtOrec X F := by
  have hF0 : 0 < F := pos_iff_ne_zero.2 hF.1
  have hG : IsGP F := by rw [← hGF]; exact isGP_GG hF0
  have hfix := nn_gp_fix hG
  obtain ⟨hE, hp, -, hlim, hU⟩ := nn_fix_facts hF hfix
  have hO : NnGGBelow X F := fun μ _ hμr hμ1 hμG hμne => nnGG hX hS μ hμr hμ1 hμG hμne
  refine le_of_forall_lt fun v hv => ?_
  by_cases hvF : v < F * F
  · exact hvF.trans_le (nnGam hX hF hF1 hfix hG)
  · push Not at hvF
    set d := v - F * F with hd
    have hdv : F * F + d = v := Ordinal.add_sub_cancel_of_le hvF
    have hdF : d < F := (sub_lt_of_le hvF).2 hv
    obtain ⟨s, hs⟩ := hS d
    have hstep : ∀ β1, β1 < F → ∃ β, β1 < β ∧ β < F ∧ ω ^ d ∣ β ∧ (0 < GG β → GG (GG β) ≠ GG β) := by
      intro β1 hβ1
      obtain ⟨β, hβ1β, hβle, hdvd, hnp, hβpos⟩ := nn_pick (β0 := β1) (r := d)
      have hβF : β < F := hβle.trans_lt (hp (hp hβ1 (nn_opow_lt hE hdF)) (nn_opow_lt hE hdF))
      refine ⟨β, hβ1β, hβF, hdvd, fun _ h => ?_⟩
      have hβfix : GG β = β := GG_strictMono.injective h
      have hβG : IsGP β := by rw [← hβfix]; exact isGP_GG hβpos
      have hu := nn_gp_fix hβG
      exact hnp (cp_fix_facts (ri_of_fp hβpos hu) hu).2.1
    have hcof := nn_cof_sq (B := F) hF1 hO hGF hlim hF0 hstep hdF s hs
    obtain ⟨hCB, hval⟩ := hs F hU hF1 hdF
    have := lt_xtOrec_of_cof hF hF1 (by rw [hfix]; exact hCB) hcof
    rwa [hfix, hval, hdv] at this

end Googology.Trans.PoR.InaccPsi.R2.Nn
