import Googology.Trans.PoR.InaccPsi.R2.RaRead

/-!
# The supply asked only cofinally at each named point, and the road without the realizers at `L(ω)`

`a` a named point (`ι(η_a) = a = P(η_a)`, `ω^{Ω₁} ∣ η_a`), `m* = L(0)`, `L(n+1)`, `r(μ) = k_μ(Θ_μ(m_μ))`.
`Ls.lsReal_named` asks the supply `Ls.LsSupCode S k` (`υ_{μ+ρ_μ} ≤ r(μ)` at EVERY Range restart with the code
`G_{k+1} + 1`) and the cofinality of that family below `a`.  Its proof uses, for each `γ < a`, ONE Range restart
`μ` with `γ < ρ_μ < a`, `ω^{Ω₁} ∣ η_μ` and `υ_{μ+γ'} ≤ r(μ)` for one `γ' ≥ γ` below `ρ_μ`.  So:

* `RaSupAt S a` (**the supply at `a`**: for every `γ < a` a Range restart `μ` with `γ < ρ_μ < a`,
  `ω^{Ω₁} ∣ η_μ` and `υ_{μ+γ} ≤ r(μ)`; no code, no family, no `k`), `raSupAt_of_code` (**`LsSupCode S k` and
  the family below `a` give `RaSupAt S a`**), `raSupAt_M`, `raSupAt_L` (at `m*` and every `L(n+1)` from
  `LsSupCode S k`), `raSupAt_of_read` (from `RaSupRead S k`), `RaLe1At S a` and `raSupAt_iff_le1` (**under
  UPPER/LOWER the supply is exactly `ρ_μ ≤₁ υ_{μ+γ}` at cofinal Range restarts `μ`**);
* `raReal_named` (**`LrReal S a υ_{a+β}`** for `β < a`, `ω² ∣ β`, from `RaSupAt S a`, UPPER/LOWER at the
  `Rz.RzRest` Range restarts, `CxStdPairTop`, `a < ν_C`, `υ_{a+β} ≤ ν_C`), `raReal_upto` (**every target below
  `υ_{a+a}`**, given `a < ν_C`, `υ_{a+a} ≤ ν_C`, `υ_{a+a} ≤ L(ω+1)`);
* `raNamed_T` (**`CxNamed` from `CxT`, `RaSupAt` at `m*` and every `L(n+1)` and the uncovered targets above
  `υ_{a+a}`**: the realizers at `L(ω)` and `CvNoPair L(ω) L(ω+1)` enter the road only through
  `T: L(ω) ≤₁ L(ω+1)`), `raT_of_real` (`CvNoPair`, `LrRealCof` at `L(ω)` and LOWER give `T`),
  `raRoad_T` (**the road** with `RaSupAt` at the named points and `T`), `raRoad_gapR` (the hypotheses of
  `Ls.lsRoad_gapR` give those of `raRoad_T`: the road asks strictly less).

No new axiom.  New definitions: `RaSupAt`, `RaLe1At`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ra

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv
  Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Ls

variable {S : InaccSeq.{0}}

/-- **The supply at `a`**: Range restarts `μ` cofinal below `a` with `ω^{Ω₁} ∣ η_μ` and `υ_{μ+γ} ≤ r(μ)`. -/
def RaSupAt (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ ω ^ Om 1 ∣ cdEta S μ ∧
    upsilon (μ + γ) ≤ cdR S μ

/-- **`LsSupCode S k` and the family below `a` give `RaSupAt S a`.** -/
theorem raSupAt_of_code {a : Ordinal.{0}} {k : ℕ}
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ cdCode S μ = lsG S (k + 1) + 1)
    (hk : LsSupCode S k) : RaSupAt S a := by
  intro γ hγ
  obtain ⟨μ, hR, h1, h2, hc⟩ := hcof γ hγ
  exact ⟨μ, hR, h1, h2, lsDiv_of_code hc,
    (upsilon_normal.strictMono.monotone (add_le_add le_rfl h1.le)).trans (hk μ hR hc)⟩

theorem raSupAt_M {k : ℕ} (hk : LsSupCode S k) : RaSupAt S (Nc.ncL S 0) :=
  raSupAt_of_code (lsNames_M (S := S) k) hk

theorem raSupAt_L {k : ℕ} (hk : LsSupCode S k) (n : ℕ) :
    RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
  raSupAt_of_code (lsNames_L (S := S) n k) hk

theorem raSupAt_of_read {k : ℕ} (h : RaSupRead S k) :
    RaSupAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
  ⟨raSupAt_M (raSupCode_of_read h), raSupAt_L (raSupCode_of_read h)⟩

/-- **The supply as `≤₁`**: Range restarts `μ` cofinal below `a` with `ω^{Ω₁} ∣ η_μ` and `ρ_μ ≤₁ υ_{μ+γ}`. -/
def RaLe1At (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ ω ^ Om 1 ∣ cdEta S μ ∧
    le1 (upsilon μ) (upsilon (μ + γ))

/-- **Under UPPER and LOWER at the `Rz.RzRest` Range restarts, the supply at `a` is exactly `RaLe1At S a`**:
the reach `r(μ)` is the `≤₁`-reach of `ρ_μ`, so `υ_{μ+γ} ≤ r(μ) ⇔ ρ_μ ≤₁ υ_{μ+γ}`.  The supply at `a` is a
family of `≤₁`-facts at lower restarts of the same kind as `a ≤₁ b` (realizers at `μ`), not a new kind
of statement. -/
theorem raSupAt_iff_le1 {a : Ordinal.{0}} (hza : upsilon Rz.rzLam < a)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) : RaSupAt S a ↔ RaLe1At S a := by
  have hm := upsilon_normal.strictMono
  constructor
  · intro h γ hγ
    obtain ⟨μ, hR, h1, h2, hd, hs⟩ := h (max γ (upsilon Rz.rzLam)) (max_lt hγ hza)
    have hzμ : Rz.rzLam ≤ μ := (hm.lt_iff_lt.1 ((le_max_right _ _).trans_lt h1)).le
    have hlow : le1 (upsilon μ) (cdR S μ) := hL μ hR (Or.inl hzμ)
    refine ⟨μ, hR, (le_max_left _ _).trans_lt h1, h2, hd, le1_of_le_of_le1 (hm.monotone le_self_add)
      ((hm.monotone (add_le_add le_rfl (le_max_left _ _))).trans hs) hlow⟩
  · intro h γ hγ
    obtain ⟨μ, hR, h1, h2, hd, hle⟩ := h (max γ (upsilon Rz.rzLam)) (max_lt hγ hza)
    have hzμ : Rz.rzLam ≤ μ := (hm.lt_iff_lt.1 ((le_max_right _ _).trans_lt h1)).le
    have hup : ¬ le1 (upsilon μ) (cdR S μ + 1) := hU μ hR (Or.inl hzμ)
    have hs : upsilon (μ + max γ (upsilon Rz.rzLam)) ≤ cdR S μ := by
      by_contra hlt
      rw [not_le] at hlt
      exact hup (le1_of_le_of_le1 ((cdRho_lt_R S μ).le.trans le_self_add)
        (Order.add_one_le_of_lt hlt) hle)
    exact ⟨μ, hR, (le_max_left _ _).trans_lt h1, h2, hd,
      (hm.monotone (add_le_add le_rfl (le_max_left _ _))).trans hs⟩

/-- **`LrReal S a υ_{a+β}` for every `β < a` with `ω² ∣ β`** at a named point `a`, from `RaSupAt S a`. -/
theorem raReal_named {a ηa β : Ordinal.{0}}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνβ : upsilon (a + β) ≤ nuC) (hβL : upsilon (a + β) < Nc.ncL S (ω + 1))
    (hβ : ω ^ 2 ∣ β) (hβa : β < a) (hsup : RaSupAt S a)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : CxStdPairTop S) (haL : a ≤ Nc.ncL S (ω + 1)) :
    LrReal S a (upsilon (a + β)) := by
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have ha1' : a < Om 1 := by rw [← hP]; exact Nm.Pv_lt_Om1 S ηa
  have ha1 : a < Om1 := by rw [Br.Om1_eq]; exact ha1'
  have haE : InE a := by rw [← hua]; exact upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hri.1))
  have hB0a : cdB0 < a := by
    obtain ⟨μ, hR, -, h2, -⟩ := hsup 0 (pos_iff_ne_zero.2 hri.1)
    refine lt_of_le_of_lt hR.2.1 ?_
    rw [← hua] at h2; exact hm.lt_iff_lt.1 h2
  -- the inner offsets
  have hinner : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → g + ω + 1 < β := by
    intro g _ hgβ hgd
    have h1 := lr_dvd_add_le hgd hβ hgβ
    have h2 := lr_omega_mul_add_one_lt 1
    rw [Nat.cast_one, mul_one] at h2
    rw [add_assoc]; exact (lr_addL (a := g) h2).trans_le h1
  have hgP : ∀ g, g < β → g ≤ Nm.Pv S ηa := fun g hgβ => by rw [hP]; exact (hgβ.trans hβa).le
  -- the codes and values at the inner restarts `a + g`
  have hcodeA : ∀ g, 0 < g → g < β → cdCode S (a + g) = cdOff (cdExp g) := by
    intro g hg0 hgβ
    have := (lsCode_shift hg hdiv hg0.ne' (hgP g hgβ)).2
    rwa [hι] at this
  have hrA : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g →
      cdR S (a + g) = upsilon (a + (g + ω + 1)) + cdOff (cdExp g) := by
    intro g hg0 hgβ hgd
    have hri' : IsRestartIdx (a + g) := ⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le),
      dvd_add hri.2 hgd⟩
    have hC : upsilon (a + g + ω + 1) < nuC := by
      refine lt_of_lt_of_le (hm ?_) hνβ
      rw [add_assoc, add_assoc]; exact lr_addL (a := a) (by rw [← add_assoc]; exact hinner g hg0 hgβ hgd)
    have hsh : cdCode S (a + g) ≤ upsilon (a + g) := by
      rw [hcodeA g hg0 hgβ]
      exact (lsOff_le g hg0.ne').trans ((hgβ.trans hβa).le.trans
        ((le_of_eq hua.symm).trans (hm.monotone le_self_add)))
    rw [lsR_short hri' hC hsh, hcodeA g hg0 hgβ]
    unfold cdDelta; simp only [add_assoc]
  -- the shift
  have hrb : ∀ g, 0 < g → g < β → cdOff (cdExp g) < a := fun g hg0 hgβ =>
    (lsOff_le g hg0.ne').trans_lt (hgβ.trans hβa)
  have hreal := lsReal_shiftR (S := S) (l := a) (β := β) hri (by rw [hua]; exact ha1)
    (by rw [hua]; exact hν) hνβ ?_ ?_ ?_ (Or.inr ⟨hstd, by rw [hua]; exact haL⟩)
  · rwa [hua] at hreal
  · -- UPPER at the inner restarts
    intro g hg0 hgβ hgd
    refine hU _ ⟨⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hri.2 hgd⟩,
      hB0a.le.trans le_self_add, (hm (lr_addL (a := a) hgβ)).trans hβL, ?_⟩
      (Or.inl (hzl.le.trans le_self_add))
    rw [hcodeA g hg0 hgβ]
    exact (lsOff_le g hg0.ne').trans_lt ((hgβ.trans (hβa.trans ha1')).trans (Lw.lw_Om1_lt_Pp S))
  · -- the form of the inner reaches
    intro g hg0 hgβ hgd
    exact Or.inr ⟨g + ω + 1, cdOff (cdExp g), hinner g hg0 hgβ hgd,
      by rw [hua]; exact hrb g hg0 hgβ, hrA g hg0 hgβ hgd⟩
  · -- the Range restarts with the supply and the carry
    intro γ hγ
    rw [hua] at hγ
    have hzua : upsilon Rz.rzLam < a := by rw [← hua]; exact hm hzl
    set γ' := max γ (max β (upsilon Rz.rzLam)) with hγ'def
    obtain ⟨μ, hR, hγμ, hμa, hdivμ, hsupμ⟩ := hsup γ' (max_lt hγ (max_lt hβa hzua))
    have hγ' : γ < upsilon μ := (le_max_left _ _).trans_lt hγμ
    have hββ : β ≤ γ' := (le_max_left _ _).trans (le_max_right _ _)
    have hβμ : β < upsilon μ := hββ.trans_lt hγμ
    have hzμ : Rz.rzLam < μ :=
      hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hγμ)
    have hμa' : μ < a := by rw [← hua] at hμa; exact hm.lt_iff_lt.1 hμa
    have hpv := lsPv_range hR
    obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
      (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
    have hgPμ : ∀ g, g < β → g ≤ Nm.Pv S (cdEta S μ) := fun g hgβ => by
      rw [hpv]; exact (hgβ.trans hβμ).le
    refine ⟨μ, hR, hγ', by rw [hua]; exact hμa, (haE.add_lt hμa' hβa).le, ?_, ?_⟩
    · -- the supply `υ_{μ+β} ≤ υ_{μ+γ'} ≤ r(μ)`
      exact (hm.monotone (add_le_add le_rfl hββ)).trans hsupμ
    · -- the carry
      intro g hg0 hgβ hgd
      have hcM : cdCode S (μ + g) = cdOff (cdExp g) := by
        have := (lsCode_shift hgμ hdivμ hg0.ne' (hgPμ g hgβ)).2
        rwa [hιμ] at this
      have hriμ : IsRestartIdx (μ + g) := ⟨fun h => hR.1.1 (le_antisymm (h ▸ le_self_add) zero_le),
        dvd_add hR.1.2 hgd⟩
      have hμga : μ + g < a := haE.add_lt hμa' (hgβ.trans hβa)
      have hRμ : CdRange S (μ + g) := by
        refine ⟨hriμ, hR.2.1.trans le_self_add, ?_, ?_⟩
        · exact (hm hμga).trans_le (by rw [hua]; exact haL)
        · rw [hcM]
          exact (lsOff_le g hg0.ne').trans_lt ((hgβ.trans (hβa.trans ha1')).trans (Lw.lw_Om1_lt_Pp S))
      have hCμ : upsilon (μ + g + ω + 1) < nuC := by
        refine ((hm ?_).trans_eq hua).trans hν
        rw [add_assoc, add_assoc]
        exact haE.add_lt hμa' (by rw [← add_assoc]; exact (hinner g hg0 hgβ hgd).trans hβa)
      have hshμ : cdCode S (μ + g) ≤ upsilon (μ + g) := by
        rw [hcM]
        exact (lsOff_le g hg0.ne').trans ((hgβ.trans hβμ).le.trans (hm.monotone le_self_add))
      have hrμ : cdR S (μ + g) = upsilon (μ + (g + ω + 1)) + cdOff (cdExp g) := by
        rw [lsR_short hriμ hCμ hshμ, hcM]
        unfold cdDelta; simp only [add_assoc]
      refine ⟨hL _ hRμ (Or.inl (hzμ.le.trans le_self_add)), fun hbig => ?_, fun h p hpγ hr => ?_⟩
      · exfalso
        rw [hrA g hg0 hgβ hgd] at hbig
        have h1 := lsUps_add_lt (ζ := a + (g + ω + 1)) (p := cdOff (cdExp g))
          ((hrb g hg0 hgβ).trans_le ((le_of_eq hua.symm).trans (hm.monotone le_self_add)))
        have h2 : upsilon (succ (a + (g + ω + 1))) ≤ upsilon (a + β) := by
          refine hm.monotone ?_
          rw [lr_succ_add]
          exact lr_addLe (a := a) (Order.succ_le_of_lt (hinner g hg0 hgβ hgd))
        exact absurd (hbig.trans_lt (h1.trans_le h2)) (lt_irrefl _)
      · rw [hrA g hg0 hgβ hgd] at hr
        have hpa : p < upsilon a := by rw [hua]; exact hpγ.trans (hγ'.trans hμa)
        obtain ⟨hh, hpp⟩ := lsUps_add_inj (by rw [hua]; exact hrb g hg0 hgβ) hpa hr
        rw [← hh, ← hpp, hrμ]

/-- **Every target below `υ_{a+a}` is realized at a named point `a`**, given `a < ν_C`, `υ_{a+a} ≤ ν_C`,
`υ_{a+a} ≤ L(ω+1)` and `RaSupAt S a`. -/
theorem raReal_upto {a ηa : Ordinal.{0}}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνa : upsilon (a + a) ≤ nuC) (haa : upsilon (a + a) ≤ Nc.ncL S (ω + 1))
    (hsup : RaSupAt S a)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : CxStdPairTop S) :
    ∀ y < upsilon (a + a), ∃ t, y < t ∧ t ≤ upsilon (a + a) ∧ LrReal S a t := by
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have haE : InE a := by rw [← hua]; exact upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hri.1))
  have hw2a : (ω : Ordinal.{0}) ^ 2 ≤ a := Ordinal.le_of_dvd hri.1 hri.2
  have hωa : (ω : Ordinal.{0}) ≤ a := by
    refine le_trans ?_ hw2a
    rw [pow_two]; exact Ordinal.le_mul_left ω omega0_pos
  have hww : (ω : Ordinal.{0}) ^ 2 < a := by
    have e : (ω : Ordinal.{0}) ^ (2 : ℕ) = ω ^ ((2 : ℕ) : Ordinal.{0}) := (opow_natCast _ _).symm
    have h2 : ((2 : ℕ) : Ordinal.{0}) < a := (Ordinal.natCast_lt_omega0 2).trans_le hωa
    rw [e]
    calc ω ^ ((2 : ℕ) : Ordinal.{0}) < ω ^ a := (opow_lt_opow_iff_right one_lt_omega0).2 h2
      _ = a := haE
  have h1a : (1 : Ordinal.{0}) < a := one_lt_omega0.trans_le hωa
  have haa' : a < upsilon (a + a) := by
    calc a = upsilon a := hua.symm
      _ < upsilon (a + a) := hm (lt_add_of_pos_right a (pos_iff_ne_zero.2 hri.1))
  have haL : a ≤ Nc.ncL S (ω + 1) := haa'.le.trans haa
  intro y hy
  have hlim : IsSuccLimit (a + a) := isSuccLimit_add _ (ri_lim hri)
  obtain ⟨ζ, hζ, hyζ⟩ := (upsilon_normal.lt_iff_exists_lt hlim).1 hy
  obtain ⟨d, hd, hζd⟩ : ∃ d < a, ζ ≤ a + d := by
    rcases le_or_gt ζ a with h | h
    · exact ⟨0, pos_iff_ne_zero.2 hri.1, by rw [add_zero]; exact h⟩
    · obtain ⟨d, rfl⟩ := exists_add_of_le h.le
      exact ⟨d, (add_lt_add_iff_left a).1 hζ, le_rfl⟩
  set β := ω ^ 2 * (d + 1) with hβdef
  have hβa : β < a := haE.mul_lt hww (haE.add_lt hd h1a)
  have hdβ : d < β := (lt_add_one d).trans_le (Ordinal.le_mul_right (d + 1) (pow_pos omega0_pos 2))
  have hβaa : upsilon (a + β) < upsilon (a + a) := hm (lr_addL (a := a) hβa)
  refine ⟨upsilon (a + β), hyζ.trans_le (hm.monotone (hζd.trans (lr_addLe (a := a) hdβ.le))), hβaa.le, ?_⟩
  exact raReal_named hg hι hP hdiv hri hzl hν (hβaa.le.trans hνa) (hβaa.trans_le haa)
    (dvd_mul_right _ _) hβa hsup hU hL hstd haL

/-- The realizers below `υ_{a+a}` at `m*` and at every `L(n+1)`, with `υ_{a+a} ≤ b`. -/
theorem raNamed_R (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S)
    (hs0 : RaSupAt S (Nc.ncL S 0)) (hsn : ∀ n : ℕ, RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) :
    (∀ y < upsilon (Nc.ncL S 0 + Nc.ncL S 0), ∃ t, y < t ∧ t ≤ Nc.ncL S 1 ∧ LrReal S (Nc.ncL S 0) t) ∧
    ∀ n : ℕ, ∀ y < upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})),
        ∃ t, y < t ∧ t ≤ Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ∧
          LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) t := by
  have hLw : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := lsM_named (S := S)
    have hb : upsilon (Nc.ncL S 0 + Nc.ncL S 0) ≤ Nc.ncL S 1 := by
      have := lsAA_le hg hι hP
      rwa [← mul_one (Nc.ncPp S), ← Lw.lw_L_eq] at this
    have hb1 : Nc.ncL S 1 ≤ Nc.ncL S ω := Pp.ppL_mono one_lt_omega0.le
    have hua : Nc.ncL S 0 < upsilon (Nc.ncL S 0 + Nc.ncL S 0) := by
      have h := Bt.ups_iota S (Om ω); rw [hι] at h
      calc Nc.ncL S 0 = upsilon (Nc.ncL S 0) := (h.trans hP).symm
        _ < _ := upsilon_normal.strictMono (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hri.1))
    intro y hy
    obtain ⟨t, h1, h2, h3⟩ := raReal_upto hg hι hP hdiv hri hzl
      (hua.trans_le (hb.trans (hb1.trans hlow))) (hb.trans (hb1.trans hlow))
      (hb.trans (hb1.trans hLw.le)) hs0 hU hL hstd y hy
    exact ⟨t, h1, h2.trans hb, h3⟩
  · obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := lsL_named (S := S) n
    have hb : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) ≤
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have := lsAA_le hg hι hP
      have e : Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncPp S =
          Om ω + Nc.ncPp S * ((n + 2 : ℕ) : Ordinal.{0}) := (Rm.rm_eta_succ (S := S) (n + 1)).symm
      rwa [e, ← Lw.lw_L_eq] at this
    have hb1 : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (n + 1)).le
    have hua : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) <
        upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})); rw [hι] at h
      calc Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :=
            (h.trans hP).symm
        _ < _ := upsilon_normal.strictMono (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hri.1))
    intro y hy
    obtain ⟨t, h1, h2, h3⟩ := raReal_upto hg hι hP hdiv hri hzl
      (hua.trans_le (hb.trans (hb1.trans hlow))) (hb.trans (hb1.trans hlow))
      (hb.trans (hb1.trans hLw.le)) (hsn n) hU hL hstd y hy
    exact ⟨t, h1, h2.trans hb, h3⟩

/-- **`T: L(ω) ≤₁ L(ω+1)` from `CvNoPair L(ω) L(ω+1)`, the realizers cofinal below `L(ω+1)` and LOWER.** -/
theorem raT_of_real (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : CxT S :=
  lrLe1_of_realCof (Rz.rzLOWER_of_rest hL) (Qq.qqL_lt_succ S).le hP hw

/-- **`CxNamed` from `T`, the supply at `m*` and every `L(n+1)` and the uncovered targets above `υ_{a+a}`.** -/
theorem raNamed_T (hlow : Nc.ncL S ω ≤ nuC) (hstd : CxStdPairTop S)
    (hs0 : RaSupAt S (Nc.ncL S 0)) (hsn : ∀ n : ℕ, RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hT : CxT S) : CxNamed S := by
  have hL' := Rz.rzLOWER_of_rest hL
  obtain ⟨r0, rn⟩ := raNamed_R (S := S) hlow hstd hs0 hsn hU hL
  refine ⟨?_, fun n => ?_, hT⟩
  · obtain ⟨l, hl, e⟩ := cvM_restart (S := S)
    exact lsLe1_of_gapCof hL' (Pp.ppL_mono zero_le)
      (cvNoPair_of_nu hl e ((Pp.ppL_mono one_lt_omega0.le).trans hlow)) r0 h0
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    exact lsLe1_of_gapCof hL' (Pp.ppL_lt_succ n).le
      (cvNoPair_of_nu hl e ((Pp.ppL_lt_omega (n + 1)).le.trans hlow)) (rn n) (hn n)

/-- **The road with the supply asked at `m*` and every `L(n+1)` only (`RaSupAt`), the realizers asked only at
the uncovered targets `≥ υ_{a+a}`, and `T` in place of the realizers at `L(ω)`.** -/
theorem raRoad_T (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hEQ : CxEQtop S) (htop : CxTCtopOff S) (hups : CxUpsRestTop S)
    (hs0 : RaSupAt S (Nc.ncL S 0)) (hsn : ∀ n : ℕ, RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))
    (h0 : LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hT : CxT S) (hmove : CxStdMoveTop S) (hstd : CxStdPairTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hU' := Rz.rzUPPER_of_rest hU hO
  have hV' := Rz.rzCapV_of_rest hV
  exact cxRoad_rz hU hO hL hV hEQ htop hups
    (raNamed_T (cdLow_enum hU' hV') hstd hs0 hsn hU hL h0 hn hT) hmove hstd

/-- **The hypotheses of `Ls.lsRoad_gapR` give those of `raRoad_T`**: `LsSupCode S k` gives `RaSupAt` at the
named points, and `CvNoPair`, `LrRealCof` at `L(ω)` give `T`. -/
theorem raRoad_gapR {k : ℕ} (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hk : LsSupCode S k) (hP : CvNoPair (Nc.ncL S ω) (Nc.ncL S (ω + 1)))
    (hw : LrRealCof S (Nc.ncL S ω) (Nc.ncL S (ω + 1))) :
    RaSupAt S (Nc.ncL S 0) ∧ (∀ n : ℕ, RaSupAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ∧ CxT S :=
  ⟨raSupAt_M hk, raSupAt_L hk, raT_of_real hL hP hw⟩

end Googology.Trans.PoR.InaccPsi.R2.Ra
