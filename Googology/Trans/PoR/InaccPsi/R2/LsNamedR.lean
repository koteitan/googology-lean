import Googology.Trans.PoR.InaccPsi.R2.LsSup
import Googology.Trans.PoR.InaccPsi.R2.LsShift
import Googology.Trans.PoR.InaccPsi.R2.PhFr

/-!
# Realizers at `m*` and `L(n+1)` for every target below `υ_{a+a}`: the inner restarts with short codes

`a = m*` or `a = L(n+1)`: a Γ-point with `ι(η_a) = a = P(η_a)` (`η_a = Ω_ω + P'·ξ`, `Lw.lw_iota_L`), so
`υ_a = a` and the restart index of `a` is `a`.  The inner restarts of the targets below `υ_{a+a} = P(η_a + a)`
are `a + g` (`0 < g < a`, `ω² ∣ g`) with the name `η_a + g` (`Rz.rz_iota_shift`), the short code
`m_g = -1 + e(g) < a` (`e` the last exponent) and, the first block being capped at `δ` (`R2.block_le1`), the
reach value `r(a + g) = δ_{a+g} + m_g = υ_{a+g+ω+1} + m_g`.  The image restarts `μ + g` of the FRAG shift have
the same code and value `υ_{μ+g+ω+1} + m_g`.  So:

* `lsClosed` (**every `δ_λ + x`, `x < δ_λ`, is closed** at a restart index whose first block lies below `ν_C`;
  `Rz.rzClosed` without the restart context `RstK`), `lsR_short` (**`r(λ) = δ_λ + m_λ`** for a short code
  `m_λ ≤ ρ_λ`);
* `lsExp_add`, `lsCode_shift` (**`η_{ι(η)+g} = η + g` and `m_{ι(η)+g} = -1 + e(g)`** for a good `η` with
  `ω^{Ω₁} ∣ η` and `0 < g ≤ P(η)`), `lsDiv_of_code` (`m_μ = G' + 1` gives `ω^{Ω₁} ∣ η_μ`),
  `lsUps_add_inj` (`υ_{λ+h} + p` determines `h` and `p` for `p < υ_λ`);
* `lsReal_named` (**`LrReal S a υ_{a+β}` for every `β < a` with `ω² ∣ β`**), from `LsSupCode S k` (the supply
  `υ_{μ+β} ≤ υ_{μ+ρ_μ} ≤ r(μ)`; it follows from LC-STRICT, `lsSupCode_of_strict`), UPPER at the Range
  restarts `a + g`, LOWER at the Range restarts `μ + g` (both `Rz.RzRest`), `CxStdPairTop`, `υ_{a+β} ≤ ν_C`,
  by `lsReal_shiftR` with the carry `LsCarry` discharged;
* `lsNamed_R` (**at `m*` and every `L(n+1)`, every target below `υ_{a+a}` is realized**, given `L(ω) ≤ ν_C`),
  `lsLe1_of_gapCof`, `lsNamed_gapR`, `lsRoad_gapR` (**the road with the realizers at `m*` and `L(n+1)` asked
  only at the targets `≥ υ_{a+a}` that no restart reach covers**), `lsRoadGapR_hyp_of_gap2` (its hypotheses
  follow from those of `lsRoad_gap2`).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rl
  Googology.Trans.PoR.InaccPsi.R2.Cx Googology.Trans.PoR.InaccPsi.R2.Cv
  Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-! ## Short reaches -/

theorem lsBlk0 (l : Ordinal.{0}) : l + ω * (((0 : ℕ) + 1 : ℕ) : Ordinal.{0}) + 1 = l + ω + 1 := by
  simp

/-- **Every `δ_λ + x` with `x < δ_λ` is closed relative to `λ`** (first block below `ν_C`). -/
theorem lsClosed {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon (l + ω + 1) < nuC)
    (hx : x < cdDelta l) : cdClosed l (cdDelta l + x) := by
  refine ⟨le_self_add, fun a ha hay g hag => ?_⟩
  by_cases had : a ≤ cdDelta l
  · have hC' : upsilon (l + ω * (((0 : ℕ) + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by rw [lsBlk0]; exact hC
    have hb0 : upsilon (botI l 0) < a := by simpa [botI] using ha
    have ha2 : a ≤ upsilon (l + ω * (((0 : ℕ) + 1 : ℕ) : Ordinal.{0}) + 1) := by rw [lsBlk0]; exact had
    have h := ((block_le1 (Or.inr hl) 0 hC' hb0 ha2 g).1 hag).1
    rw [lsBlk0] at h
    exact h.trans le_self_add
  · have hδa : cdDelta l < a := not_le.1 had
    have ha2 : a < cdDelta l + cdDelta l := lt_of_le_of_lt hay ((add_lt_add_iff_left _).2 hx)
    have hga : g ≤ a := by
      by_contra hlt
      exact Rz.rz_not_indec hδa ha2 (indec_of_lt1 hag (not_le.1 hlt))
    exact hga.trans hay

/-- **`r(λ) = δ_λ + m_λ`** for a short code `m_λ ≤ ρ_λ` (first block below `ν_C`). -/
theorem lsR_short {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : upsilon (l + ω + 1) < nuC)
    (hm : cdCode S l ≤ upsilon l) : cdR S l = cdDelta l + cdCode S l := by
  have hmδ : cdCode S l < cdDelta l := hm.trans_lt (cdRho_lt_delta l)
  unfold cdR cdRc
  rw [cdTheta_small S hm]
  exact cdk_interval (fun y hy => Or.inl (lsClosed hl hC (lt_of_le_of_lt hy hmδ))) _ le_rfl

/-! ## Names and codes of the inner restarts -/

theorem lsExp_le {g : Ordinal.{0}} (hg0 : g ≠ 0) : cdExp g ≤ g :=
  (right_le_opow _ one_lt_omega0).trans (Ordinal.le_of_dvd hg0 (cdExp_dvd hg0))

/-- `e(η + g) = e(g)` when `ω^{Ω₁} ∣ η` and `0 < g < Ω₁`. -/
theorem lsExp_add {η g : Ordinal.{0}} (hdiv : ω ^ Om 1 ∣ η) (hg0 : g ≠ 0) (hg1 : g < Om 1) :
    cdExp (η + g) = cdExp g := by
  have hO : SC (Om (1 : Ordinal.{0})) := SC_Om one_ne_zero
  have he1 : cdExp g + 1 < Om 1 := hO.add_one_lt ((lsExp_le hg0).trans_lt hg1)
  have hd1 : ω ^ (cdExp g + 1) ∣ η := (opow_dvd_opow ω he1.le).trans hdiv
  have hd0 : ω ^ cdExp g ∣ η := (opow_dvd_opow ω (le_self_add)).trans hd1
  have hne : η + g ≠ 0 := fun h => hg0 (le_antisymm (h ▸ le_add_self) zero_le)
  exact cdExp_eq hne (dvd_add hd0 (cdExp_dvd hg0)) fun h => cdExp_not_dvd hg0 ((dvd_add_iff hd1).1 h)

/-- **`η_{ι(η)+g} = η + g` and `m_{ι(η)+g} = -1 + e(g)`.** -/
theorem lsCode_shift {η g : Ordinal.{0}} (hg : Bt.Good S η) (hdiv : ω ^ Om 1 ∣ η) (hg0 : g ≠ 0)
    (hgP : g ≤ Nm.Pv S η) :
    cdEta S (Bt.iota S η + g) = η + g ∧ cdCode S (Bt.iota S η + g) = cdOff (cdExp g) := by
  have hg1 : g < Om 1 := hgP.trans_lt (Nm.Pv_lt_Om1 S η)
  have hlt : g < Nm.Pv S (η + g) :=
    hgP.trans_lt ((Nm.Pv_lt_succ hg).trans_le (Nm.Pv_mono (add_le_add le_rfl
      (Order.one_le_iff_ne_zero.2 hg0))))
  have hgood : Bt.Good S (η + g) := Rz.rz_good_shift hg hlt
  have he : cdEta S (Bt.iota S η + g) = η + g := cdEta_unique hgood (Rz.rz_iota_shift hg hgP)
  refine ⟨he, ?_⟩
  unfold cdCode
  rw [he]
  have hexp := lsExp_add hdiv hg0 hg1
  have h2 : cdExp (η + g) < Om (1 + 1) := by
    rw [hexp]
    exact ((lsExp_le hg0).trans_lt hg1).trans (Om_lt_Om.2 (lt_add_one 1))
  rw [cdCodeOf_of_lt h2, hexp]

theorem lsOff_le (g : Ordinal.{0}) (hg0 : g ≠ 0) : cdOff (cdExp g) ≤ g := (cdOff_le _).trans (lsExp_le hg0)

/-- `m_μ = G' + 1` gives `ω^{Ω₁} ∣ η_μ`. -/
theorem lsDiv_of_code {μ : Ordinal.{0}} {k : ℕ} (hc : cdCode S μ = lsG S (k + 1) + 1) :
    ω ^ Om 1 ∣ cdEta S μ := by
  have hG1 : Om 1 ≤ lsG S (k + 1) + 1 := (lsG_Om1 (S := S) (k + 1)).le.trans le_self_add
  rcases eq_or_ne (cdEta S μ) 0 with h0 | h0
  · rw [h0]; exact dvd_zero _
  unfold cdCode cdCodeOf at hc
  split_ifs at hc with he
  · unfold cdOff at hc
    split_ifs at hc with hw
    · exfalso
      have h1 : cdExp (cdEta S μ) - 1 < ω := (Ordinal.sub_le_self _ _).trans_lt hw
      rw [hc] at h1
      exact absurd ((Pp.ppOmega_lt_SC (lsG_SC (S := S) _)).trans (lt_add_one _)) (not_lt.2 h1.le)
    · rw [← hc] at hG1
      exact (opow_dvd_opow ω hG1).trans (cdExp_dvd h0)
  · exact absurd hc ((SC_psi (InR_Om_succ 1) _).ne_add_one _)

/-- `υ_{λ+h} + p = υ_{λ+h'} + p'` with `p, p' < υ_λ` gives `h = h'` and `p = p'`. -/
theorem lsUps_add_inj {l h h' p p' : Ordinal.{0}} (hp : p < upsilon l) (hp' : p' < upsilon l)
    (e : upsilon (l + h) + p = upsilon (l + h') + p') : h = h' ∧ p = p' := by
  have hm := upsilon_normal.strictMono
  have hph : p < upsilon (l + h) := hp.trans_le (hm.monotone le_self_add)
  have hph' : p' < upsilon (l + h') := hp'.trans_le (hm.monotone le_self_add)
  have hs := lr_seg_unique (y := upsilon (l + h) + p) le_self_add (lsUps_add_lt hph)
    (by rw [e]; exact le_self_add) (by rw [e]; exact lsUps_add_lt hph')
  have hh : h = h' := (add_left_cancel hs)
  subst hh
  exact ⟨rfl, add_left_cancel e⟩

/-! ## The realizers at a named point -/

/-- **`LrReal S a υ_{a+β}` for every `β < a` with `ω² ∣ β`** at a named point `a = ι(η_a) = P(η_a)`. -/
theorem lsReal_named {a ηa β : Ordinal.{0}} {k : ℕ}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνβ : upsilon (a + β) ≤ nuC) (hβL : upsilon (a + β) < Nc.ncL S (ω + 1))
    (hβ : ω ^ 2 ∣ β) (hβa : β < a)
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ cdCode S μ = lsG S (k + 1) + 1)
    (hk : LsSupCode S k)
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
    obtain ⟨μ, hR, -, h2, -⟩ := hcof 0 (pos_iff_ne_zero.2 hri.1)
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
      exact (lsOff_le g hg0.ne').trans ((hgβ.trans hβa).le.trans ((le_of_eq hua.symm).trans (hm.monotone le_self_add)))
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
    obtain ⟨μ, hR, hγμ, hμa, hc⟩ := hcof (max γ (max β (upsilon Rz.rzLam)))
      (max_lt hγ (max_lt hβa hzua))
    have hγ' : γ < upsilon μ := (le_max_left _ _).trans_lt hγμ
    have hβμ : β < upsilon μ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hγμ
    have hzμ : Rz.rzLam < μ := hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hγμ)
    have hμa' : μ < a := by rw [← hua] at hμa; exact hm.lt_iff_lt.1 hμa
    have hpv := lsPv_range hR
    obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
      (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
    have hdivμ := lsDiv_of_code hc
    have hgPμ : ∀ g, g < β → g ≤ Nm.Pv S (cdEta S μ) := fun g hgβ => by
      rw [hpv]; exact (hgβ.trans hβμ).le
    refine ⟨μ, hR, hγ', by rw [hua]; exact hμa, (haE.add_lt hμa' hβa).le, ?_, ?_⟩
    · -- the supply `υ_{μ+β} ≤ r(μ)` from LC-STRICT
      exact (hm.monotone (add_le_add le_rfl hβμ.le)).trans (hk μ hR hc)
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

end Googology.Trans.PoR.InaccPsi.R2.Ls
