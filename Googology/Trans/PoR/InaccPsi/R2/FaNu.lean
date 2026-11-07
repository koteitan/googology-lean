import Googology.Trans.PoR.InaccPsi.R2.YxSpec

/-!
# Fa: `X < ν_C` FROM THE CAPS JUST BELOW EACH RESTART

`Yx.yxNu_gt` asks the caps at all restarts below `X`.  Its proof reads the caps only at restarts cofinally below the left end of the first
non-standard pair.  So a restart of unknown reach (a base of the induction on the code) does no harm:

* `faNu_gt` (**the caps just below every restart below `X ≤ L(ω)` give `X < ν_C`**).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The caps just below every restart below `X ≤ L(ω)` give `X < ν_C`.** -/
theorem faNu_gt {X : Ordinal.{0}} (hX : X ≤ Nc.ncL S ω)
    (hcof : ∀ L, IsRestartIdx L → upsilon L < X → ∃ x, x < upsilon L ∧ ∀ μ, IsRestartIdx μ → cdB0 ≤ μ → x < upsilon μ →
      upsilon μ < upsilon L → cdCode S μ < Nc.ncPp S → CdCapAt S μ) : X < nuC := by
  by_contra hlt
  have hνL : nuC ≤ X := not_lt.1 hlt
  obtain ⟨l, hl, -, hlν, -, -, -, hP, hW, -⟩ := Lb.lbFirst
  have hLeq : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  have hlT : upsilon l < Pv S (Om ω + Nc.ncPp S * ω) := hLeq ▸ (hlν.trans_le (hνL.trans hX))
  have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ l hl1 (cd_lt_iota hlT).le
  -- the least `η` with `ι(η) = λ`
  have hne : {η | iota S η = l}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = l}) = l := csInf_mem hne
  have hmin : ∀ η < sInf {η | iota S η = l}, iota S η ≠ l := fun η h he =>
    (csInf_le' (s := {η | iota S η = l}) he).not_gt h
  generalize sInf {η | iota S η = l} = ηm at hηm hmin
  have hpvm : Pv S ηm = upsilon l := by
    calc Pv S ηm = upsilon (iota S ηm) := (ups_iota S ηm).symm
      _ = upsilon l := by rw [hηm]
  have hηm0 : ηm ≠ 0 := by
    rintro rfl
    rw [iota_zero] at hηm
    exact (ri_lim hl).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hηm)
  obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hηm0
  generalize cdExp ηm = e at hdec hdvd
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < l := lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  -- a restart witness `ρ_μ ≤₁ ν_C` with `μ ∈ (ι(η₀), λ)`
  obtain ⟨x1, hx1, hcap1⟩ := hcof l hl (hlν.trans_le hνL)
  obtain ⟨y, hνy', hyl, hy⟩ := hP (max (upsilon (iota S η0)) x1) (max_lt (upsilon_normal.strictMono hν) hx1)
  have hνy : upsilon (iota S η0) < y := (le_max_left _ _).trans_lt hνy'
  have hxy : x1 < y := (le_max_right _ _).trans_lt hνy'
  obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνy
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  obtain ⟨hg, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hηm.symm)
  have hpvμ : Pv S (cdEta S μ) = upsilon μ := by
    calc Pv S (cdEta S μ) = upsilon (iota S (cdEta S μ)) := (ups_iota S _).symm
      _ = upsilon μ := by rw [hιμ]
  have hx0 : η0 < cdEta S μ := by
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) η0 _ h
    rw [hιμ] at h'
    exact absurd h' (not_le.2 hμν)
  have hxm : cdEta S μ < η0 + ω ^ e := by
    rw [← hdec]
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) (cdEta S μ) ηm h
    rw [hιμ, hηm] at h'
    exact absurd h' (not_le.2 hμl)
  obtain ⟨hxe, hxw⟩ := cdWin hdvd hx0 hxm
  -- the cap of `μ` is at most `ρ_λ`
  have hcapl : cdCapB S μ ≤ upsilon l := by
    unfold cdCapB
    calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
      _ = upsilon l := hpvm
  -- the cap of `μ` applies
  have hcode : cdCode S μ < Nc.ncPp S := by
    rcases lt_or_ge (upsilon μ) (cdMstar S) with hlev | hlev
    · exact cdCode_lt_level1 hμ.1 hlev
    · have hx1' : Om ω ≤ cdEta S μ := by
        by_contra h
        push Not at h
        have h1' := Pv_lt_succ hg
        have h2' : Pv S (cdEta S μ + 1) ≤ Pv S (Om ω) := Pv_mono (Order.add_one_le_of_lt h)
        rw [hpvμ] at h1'
        exact absurd (h1'.trans_le h2') (not_lt.2 hlev)
      have htop : η0 + ω ^ e < Om ω + Nc.ncPp S * ω := by
        rw [← hdec]
        by_contra h
        push Not at h
        have h' := Pv_mono (S := S) h
        rw [hpvm] at h'
        exact absurd (hlT.trans_le h') (lt_irrefl _)
      have hxP : cdExp (cdEta S μ) < Nc.ncPp S := by
        by_contra h
        push Not at h
        exact cd_l2_contra hdvd hx1' hxm htop (lt_of_le_of_lt h hxe)
      show cdCodeOf S (cdEta S μ) < Nc.ncPp S
      rw [cdCodeOf_of_lt (hxP.trans (cdPp_lt_Om2 S))]
      exact (cdOff_le _).trans_lt hxP
  have hcapμ : CdCapAt S μ := hcap1 μ hμ hBμ hxy hyl hcode
  exact absurd ((hcapμ nuC hy).trans_le hcapl) (not_lt.2 hlν.le)

end Googology.Trans.PoR.InaccPsi.R2.Fa
