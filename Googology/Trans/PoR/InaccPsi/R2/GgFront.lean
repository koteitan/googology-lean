import Googology.Trans.PoR.InaccPsi.R2.GgRoad

/-!
# The frontiers lie at or above `ι(ε_{Ω₁+1})`

`ggE = ε_{Ω₁+1}`, `eN x` the least `ε`-number above `x`.  A frontier of a term system `X` is a restart `λ` with
`O_X(λ) = top(ρ_λ)` (`Xt.XtFr`).

* `ggTh_le_eN` (`Θ_y(ggE) ≤ eN(y)`: every code below `ggE` is read below the next `ε`-number), `gg_eN_lt_B`
  (`eN(x) < B(x)`, by the term `ϑˣ(Ω₁)` of `VzTm`);
* `ggFr_fix` (a frontier `λ > ω²` of a system with `eN(x) < top(x)` is a fixed point of `υ`, since `O(λ) ≤ λ`
  off the fixed points), `ggFr_exp` (**a named frontier has `e(η_λ) > ε_{Ω₁+1}`**, by THEOREM UNI),
  `ggFr_iota` (**every frontier `λ > ω²` is `≥ ι(ε_{Ω₁+1})`**; an unnamed one is above every `ι(η)`),
  `ggB1_iota` (the first limit of frontiers too);
* `ggVz_LamB`, `ggVz_B1`, `ggLamK`, `ggW2`, `ggLyE_B1`: **`ι(ε_{Ω₁+1}) ≤ Λ_B, cpB1, Λ⁺_k, Λ_{ω²}, Λ⁺(lyEB)`**, so
  `P(ε_{Ω₁+1}) ≤ ρ` at each of them (before: `Φ_Γ = P(Ω₁^{Ω₁+1}) ≤ Λ_B`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Gg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

theorem gg_eN_prin (y : Ordinal.{0}) : IsPrincipal (· + ·) (eN y) := by
  rw [← (eN_E y : ω ^ eN y = eN y)]; exact isPrincipal_add_omega0_opow _

/-- **Every code below `ggE` is read below the next `ε`-number**: `Θ_y(ggE) ≤ eN(y)`. -/
theorem ggTh_le_eN {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y ggE ≤ eN y := by
  have key : ∀ c, GgCl y c → c < ggE → ggTh y c < eN y := by
    intro c hc
    induction hc with
    | small h => intro _; rw [ggTh_small h.le]; exact h.trans (lt_eN y)
    | om => intro _; rw [ggTh_Om1 hy hy1]; exact lt_eN y
    | @add u v hu _ ihu ihv =>
      intro h
      rw [ggTh_add hy hu]
      exact gg_eN_prin y (ihu (lt_of_le_of_lt le_self_add h)) (ihv (lt_of_le_of_lt le_add_self h))
    | @phi a b ha hb _ ihb =>
      intro h
      rcases eq_or_ne a 0 with rfl | ha0
      · rw [veblen_zero_apply, ggTh_opow hy hb]
        have h1 := ihb (lt_of_le_of_lt (right_le_veblen 0 b) h)
        calc ω ^ ggTh y b < ω ^ eN y := (opow_lt_opow_iff_right one_lt_omega0).2 h1
          _ = eN y := eN_E y
      · have hE := gg_veblen_eps (y := b) ha0
        have hle : veblen a b ≤ Om 1 := by
          by_contra hgt
          push Not at hgt
          exact absurd (ggE_le hE hgt) (not_le.2 h)
        rcases hle.lt_or_eq with hlt | heq
        · have hvy : veblen a b < y := (GgCl.phi ha hb).lt_of_lt_Om1 hy hlt
          rw [ggTh_small hvy.le]; exact hvy.trans (lt_eN y)
        · rw [heq, ggTh_Om1 hy hy1]; exact lt_eN y
  classical
  unfold ggTh
  rw [cdOtp_eq]
  refine ciSup_le' fun c => ?_
  by_cases hc : c.1 ∈ ggSet y
  · rw [if_pos hc]; exact Order.add_one_le_of_lt (key c.1 hc c.2)
  · rw [if_neg hc]; exact zero_le

/-- **`eN(x) < B(x)`**: the value `ϑˣ(Ω₁)` of a term of `VzTm` is an `ε`-number above `x`. -/
theorem gg_eN_lt_B {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < VzB x := by
  have hx0 : 0 < x := by
    rcases eq_or_ne x 0 with h | h
    · exfalso; have := hx; rw [h] at this; unfold InE at this; rw [opow_zero] at this
      exact one_ne_zero this
    · exact pos_iff_ne_zero.2 h
  have h := vz_th_facts (k := 1) hx hx1 le_rfl (mem_T_of_le hx hx1 zero_le) (lt_of_le_of_lt zero_le hx1)
  have hle : eN x ≤ vt x (Om1 * ((1 : ℕ) : Ordinal.{0}) + 0) := eN_le h.2.2.2.1 h.2.2.2.2.2.1
  have hlt := vzv_lt_B hx hx1 (t := VzTm.th 1 (VzTm.cst 0)) ⟨le_rfl, hx0⟩
  exact hle.trans_lt hlt

/-- A frontier `λ > ω²` of a system with `eN(x) < top(x)` is a fixed point of `υ`. -/
theorem ggFr_fix {X : XtSys} (htop : ∀ x, InE x → x < Om1 → eN x < X.top x) {l : Ordinal.{0}}
    (hl : XtFr X l) (hl1 : l < Om1) (hww : ω * ω < l) : upsilon l = l := by
  by_contra hne
  have hnf : l < upsilon l := lt_of_le_of_ne upsilon_normal.strictMono.le_apply (Ne.symm hne)
  have hO := xtNonfix (X := X) hl.1 hww hnf hl1
  have h1 : xtOrec X l ≤ l := by rw [hO]; exact (cdOff_le _).trans (cpExp_le hl.1.1)
  have h2 : upsilon l < X.top (upsilon l) :=
    (lt_eN _).trans (htop _ (ups_inE hl.1) (ups_lt_Om1 l hl1))
  rw [hl.2] at h1
  exact absurd (h1.trans_lt hnf) (not_lt.2 h2.le)

/-- **A named frontier has `e(η_λ) > ε_{Ω₁+1}`.** -/
theorem ggFr_exp {X : XtSys} (hP : GgPoly X ggE) {l ηx : Ordinal.{0}} (htop : eN l < X.top l)
    (hl : XtFr X l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) : ggE < cdExp (cdEta S l) := by
  by_contra h
  push Not at h
  have hO := ggUni ggE_le_ggGam hP l ηx hl.1 hfix hX h
  have hSC := ggSC_fix hl.1 hfix hX
  have hl1 : l < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have h2 : xtOrec X l ≤ eN l := by
    rw [hO]; exact (ggTh_mono h).trans (ggTh_le_eN hSC hl1)
  rw [hl.2, hfix] at h2
  exact absurd h2 (not_le.2 htop)

/-- **Every frontier `λ > ω²` of a system with terms for the codes below `ggE` and `eN(x) < top(x)` is
`≥ ι(ε_{Ω₁+1})`.** -/
theorem ggFr_iota {X : XtSys} (hP : GgPoly X ggE) (htop : ∀ x, InE x → x < Om1 → eN x < X.top x)
    {l : Ordinal.{0}} (hl : XtFr X l) (hl1 : l < Om1) (hww : ω * ω < l) : iota S ggE ≤ l := by
  have hfix := ggFr_fix htop hl hl1 hww
  by_cases hn : ∃ ηx, upsilon l < Pv S ηx
  · obtain ⟨ηx, hX⟩ := hn
    have hl1' : l < Om1 := hl1
    have he := ggFr_exp hP (htop l (by have := ups_inE hl.1; rwa [hfix] at this) hl1') hl hfix hX
    obtain ⟨-, hι, -, -⟩ := cdEta_pv_spec (S := S) hl.1.1 hX
    obtain ⟨η0, hdec, -⟩ := cdExp_decomp (gg_name_ne hl.1 hfix hX)
    have hlt : ggE < cdEta S l := by
      calc ggE = ω ^ ggE := ggE_spec.1.symm
        _ < ω ^ cdExp (cdEta S l) := (opow_lt_opow_iff_right one_lt_omega0).2 he
        _ ≤ cdEta S l := by conv_rhs => rw [hdec]
                            exact le_add_self
    rw [← hι]; exact iota_mono _ _ hlt.le
  · push Not at hn
    have h : upsilon (iota S ggE) ≤ upsilon l := by rw [ups_iota S ggE]; exact hn ggE
    exact upsilon_normal.strictMono.le_iff_le.1 h

/-- **The first limit of frontiers is `≥ ι(ε_{Ω₁+1})`.** -/
theorem ggB1_iota {X : XtSys} (hP : GgPoly X ggE) (htop : ∀ x, InE x → x < Om1 → eN x < X.top x)
    (hPk : XtTopPkg X) : iota S ggE ≤ xtB1 X := by
  obtain ⟨h0, hcof⟩ := xtB1_spec hPk
  obtain ⟨μ1, hμ1, -, hμ1B⟩ := hcof 0 h0
  obtain ⟨μ, hμ, h1, hμB⟩ := hcof μ1 hμ1B
  have hww : ω * ω < μ := by
    have h2 : ω * ω ≤ μ1 := by
      obtain ⟨q, hq⟩ := (ri_iff.1 hμ1.1).2
      rw [hq]
      have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact (ri_iff.1 hμ1.1).1 hq
      exact le_mul_left _ (pos_iff_ne_zero.2 hq0)
    exact h2.trans_lt h1
  exact (ggFr_iota hP htop hμ (hμB.trans (xtB1_lt_Om1 hPk)) hww).trans hμB.le

theorem gg_htop_vz : ∀ x, InE x → x < Om1 → eN x < vzSys.top x := fun _ hx hx1 => gg_eN_lt_B hx hx1

theorem gg_htop_LL (k : ℕ) : ∀ x, InE x → x < Om1 → eN x < (xtLL k).sys.top x := by
  intro x hx hx1
  rw [xtLL_top]
  have hx0 : x ≠ 0 := by
    intro h; have := hx; rw [h] at this; unfold InE at this; rw [opow_zero] at this; exact one_ne_zero this
  have h1 : 1 ≤ x ^ (ω * (k : Ordinal.{0})) := Order.one_le_iff_pos.2 (opow_pos _ (pos_iff_ne_zero.2 hx0))
  exact (gg_eN_lt_B hx hx1).trans_le (le_mul_of_one_le_right' h1)

theorem gg_htop_lyEB : ∀ x, InE x → x < Om1 → eN x < Ly.lyEB.top x := by
  intro x hx hx1
  rw [Ly.lyEB_top]
  exact (gg_eN_lt_B hx hx1).trans (lt_eN _)

/-- **`ι(ε_{Ω₁+1}) ≤ Λ_B`.** -/
theorem ggVz_LamB : iota S ggE ≤ VzLam := by
  have hfx := (Nn.nnVz_fr cpFr_Lam vzLam_lt_Om1).1
  have hfr : XtFr vzSys VzLam := ⟨vzLam_ri, by rw [xtVz_orec]; exact vzOrec_Lam⟩
  exact ggFr_iota ggPoly_vz gg_htop_vz hfr vzLam_lt_Om1 (cp_fix_facts vzLam_ri hfx).2.2

/-- **`ι(ε_{Ω₁+1}) ≤ cpB1 = Λ_B⁺`.** -/
theorem ggVz_B1 : iota S ggE ≤ cpB1 := by
  have hfx := (Nn.nnVz_fr Fx.fxB1_fr cpB1_lt_Om1).1
  have hfr : XtFr vzSys cpB1 := ⟨Fx.fxB1_fr.1, by rw [xtVz_orec]; exact Fx.fxB1_fr.2⟩
  exact ggFr_iota ggPoly_vz gg_htop_vz hfr cpB1_lt_Om1 (cp_fix_facts Fx.fxB1_fr.1 hfx).2.2

/-- **`ι(ε_{Ω₁+1}) ≤ Λ⁺_k`** for every layer. -/
theorem ggLamK (k : ℕ) : iota S ggE ≤ xtLamK k :=
  ggB1_iota (ggPoly_LL k) (gg_htop_LL k) (xtLL k).topPkg

/-- **`ι(ε_{Ω₁+1}) ≤ Λ_{ω²}`.** -/
theorem ggW2 : iota S ggE ≤ xtFamW2.famSup := (ggLamK 0).trans (xtFamW2.famBd_lt 0).le

/-- **`ι(ε_{Ω₁+1}) ≤ Λ⁺(lyEB)`.** -/
theorem ggLyE_B1 : iota S ggE ≤ xtB1 Ly.lyEB := ggB1_iota ggPoly_lyEB gg_htop_lyEB Ly.lyEB_topPkg

end Googology.Trans.PoR.InaccPsi.R2.Gg
