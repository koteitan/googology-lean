import Googology.Trans.PoR.InaccPsi.R2.SrCode

/-!
# Realizers at `m*` and every `L(n+1)` up to `υ_{a+ε_{a+1}}`: the offset map is the base change `π_{ρ_μ,a}`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`a = m*` or `a = L(n+1)`, a named point with `ι(η_a) = a = P(η_a)`, `ω^{Ω₁} ∣ η_a`.  The inner restarts below
`υ_{a+ε_{a+1}}` are `a + g`, `0 < g < ε_{a+1}`, with name `η_a + g` and short code `-1 + e(g)` (all codes
`a·a`, `a^a`, … below `ε_{a+1}` included).  Write `g = rdc A a` (`A` the code of `g`, gate below `a`).  For a
Range restart `μ` (code `G_{k+1}+1`) with `ρ_μ` above the gates of the configuration, the offset map
`g ↦ rdc A ρ_μ` is `π_{ρ_μ,a}` (`Sr.srF`), and the image restart `μ + rdc A ρ_μ` has the code
`-1 + e(rdc A ρ_μ) = π_{ρ_μ,a}(-1 + e(g))` (`Sr.srLim_pi`).  The realizer map is `π_{ρ_μ,a}` on `seg(a)`
(`So.soShiftCore`), so the inner reach `υ_{a+g+ω+1} + (-1 + e(g))` is carried exactly (`Sr.srReal_gen`); the
supply `υ_{μ+ε_{ρ_μ+1}} ≤ r(μ)` is `Sr.srSupE`.

* `srUps_lt` (`υ_{a+ε_{a+1}} < b` for a `υ`-fixed limit `b > a = υ_a`);
* `srRealE_named` (**`LrReal S a υ_{a+ε_{a+1}}`** at a named point, from the family below `a`, UPPER at the inner
  restarts, LOWER at their images, `CxStdPairTop`), `srRealE_M`, `srRealE_L` (**at `m*` and at every `L(n+1)`,
  given `L(ω) ≤ ν_C`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- `μ + ε_{ρ+1} ≤ a` for `μ ≤ ρ < a`, `a` an `ε`-number. -/
theorem srAddEN_le {μ ρ a : Ordinal.{0}} (hμρ : μ ≤ ρ) (hρa : ρ < a) (ha : InE a) : μ + eN ρ ≤ a := by
  have hE := eN_E ρ
  have e : μ + eN ρ = eN ρ := by
    have h := Ordinal.add_of_omega0_opow_le (a := μ) (b := eN ρ) (c := eN ρ)
      (by rw [show ω ^ eN ρ = eN ρ from hE]; exact hμρ.trans_lt (lt_eN ρ)) (le_of_eq hE)
    exact h
  rw [e]; exact eN_le hρa ha

/-- `g + ω + 1 < ε_{x+1}` for `g < ε_{x+1}` with `ω² ∣ g`. -/
theorem srInner {x g : Ordinal.{0}} (hg : g < eN x) (hd : ω ^ 2 ∣ g) : g + ω + 1 < eN x := by
  have h2 : ω + 1 < ω ^ 2 := by
    have := lr_omega_mul_add_one_lt 1
    rwa [Nat.cast_one, mul_one] at this
  rw [add_assoc]
  exact (lr_addL (a := g) h2).trans_le (lr_dvd_add_le hd (So.soW_dvd_E (eN_E x)) hg)

/-- **`υ_{a+ε_{a+1}} < b`** for `a = υ_a < b = υ_b`, `b` a limit. -/
theorem srUps_lt {a b : Ordinal.{0}} (hua : upsilon a = a) (hub : upsilon b = b) (hbl : IsSuccLimit b)
    (hab : a < b) : upsilon (a + eN a) < b := by
  have hm := upsilon_normal.strictMono
  have h1 : eN a ≤ upsilon (succ a) := by
    refine eN_le ?_ (Sl.slUpsE a)
    nth_rewrite 1 [← hua]; exact hm (lt_succ a)
  have h2 : upsilon (succ a) < b := by
    rw [← hub]; exact hm (hbl.succ_lt hab)
  have hE := eN_E a
  have e : a + eN a = eN a :=
    Ordinal.add_of_omega0_opow_le (by rw [show ω ^ eN a = eN a from hE]; exact lt_eN a) (le_of_eq hE)
  rw [e, ← hub]
  exact hm (h1.trans_lt h2)

/-- **Realizer maps at a named point `a` up to `υ_{a+ε_{a+1}}`**, the offset map `π_{ρ_μ,a}`. -/
theorem srRealE_named {a ηa : Ordinal.{0}} {k : ℕ}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνβ : upsilon (a + eN a) ≤ nuC) (hβL : upsilon (a + eN a) < Nc.ncL S (ω + 1))
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧
      cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : Cx.CxStdPairTop S) (haL : a ≤ Nc.ncL S (ω + 1)) :
    LrReal S a (upsilon (a + eN a)) := by
  classical
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have ha1' : a < Om 1 := by rw [← hP]; exact Nm.Pv_lt_Om1 S ηa
  have ha1 : a < Om1 := by rw [Br.Om1_eq]; exact ha1'
  have haE : InE a := by rw [← hP]; exact Sl.slPv_E ηa
  have hEa1 : eN a < Om 1 := by have := srEN_lt_Om1 hg; rwa [hP] at this
  have hB0a : cdB0 < a := by
    obtain ⟨μ, hR, -, h2, -⟩ := hcof 0 (pos_iff_ne_zero.2 hri.1)
    refine lt_of_le_of_lt hR.2.1 ?_
    rw [← hua] at h2; exact hm.lt_iff_lt.1 h2
  have hgP : ∀ g, g < eN a → g < eN (Nm.Pv S ηa) := fun g h => by rw [hP]; exact h
  have hEsucc : eN a ≤ upsilon (succ a) := by
    refine eN_le ?_ (Sl.slUpsE a)
    nth_rewrite 1 [← hua]; exact hm (lt_succ a)
  -- the codes and the reaches at the inner restarts `a + g`
  have hcodeA : ∀ g, 0 < g → g < eN a → cdCode S (a + g) = cdOff (cdExp g) := by
    intro g hg0 hgβ
    have := (srCode_shift hg hdiv hg0.ne' (hgP g hgβ)).2
    rwa [hι] at this
  have hrA : ∀ g, 0 < g → g < eN a → ω ^ 2 ∣ g →
      cdR S (a + g) = upsilon (a + (g + ω + 1)) + cdOff (cdExp g) := by
    intro g hg0 hgβ hgd
    have hri' : IsRestartIdx (a + g) := ⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le),
      dvd_add hri.2 hgd⟩
    have hC : upsilon (a + g + ω + 1) < nuC := by
      refine lt_of_lt_of_le (hm ?_) hνβ
      rw [add_assoc, add_assoc]; exact lr_addL (a := a) (by rw [← add_assoc]; exact srInner hgβ hgd)
    have hsh : cdCode S (a + g) ≤ upsilon (a + g) := by
      rw [hcodeA g hg0 hgβ]
      exact (Ls.lsOff_le g hg0.ne').trans (le_add_self.trans hm.le_apply)
    rw [Ls.lsR_short hri' hC hsh, hcodeA g hg0 hgβ]
    unfold cdDelta; simp only [add_assoc]
  have hreal := srReal_gen (S := S) (l := a) (β := eN a) hri (by rw [hua]; exact ha1)
    (by rw [hua]; exact hν) hνβ ?_ ?_ ?_ hstd (by rw [hua]; exact haL)
  · rwa [hua] at hreal
  · -- UPPER at the inner restarts
    intro g hg0 hgβ hgd
    refine hU _ ⟨⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hri.2 hgd⟩,
      hB0a.le.trans le_self_add, (hm (lr_addL (a := a) hgβ)).trans hβL, ?_⟩
      (Or.inl (hzl.le.trans le_self_add))
    rw [hcodeA g hg0 hgβ]
    exact (Ls.lsOff_le g hg0.ne').trans_lt ((hgβ.trans hEa1).trans (Lw.lw_Om1_lt_Pp S))
  · -- the form of the inner reaches
    intro g hg0 hgβ hgd
    refine Or.inr ⟨g + ω + 1, cdOff (cdExp g), lt_of_le_of_lt zero_le (lt_add_one _), srInner hgβ hgd,
      ((Ls.lsOff_le g hg0.ne').trans_lt hgβ).trans_le hEsucc, hrA g hg0 hgβ hgd⟩
  · -- the Range restarts, the offset map `π_{ρ_μ,a}`, the supply and the carry
    intro γ hγ Os hOs
    rw [hua] at hγ
    have hzua : upsilon Rz.rzLam < a := by rw [← hua]; exact hm hzl
    have hwOs : ∀ d ∈ Os, ω ^ 2 * (d / ω ^ 2) < eN a := fun d hd =>
      (le_self_add.trans_eq (Ordinal.div_add_mod d (ω ^ 2))).trans_lt (hOs d hd)
    have hga : ∀ d ∈ Os, Gf.gtc (srCd a (ω ^ 2 * (d / ω ^ 2))) < a := fun d hd =>
      (srCd_spec haE ha1.le (hwOs d hd)).2.1
    set M := Os.sup (fun d => Gf.gtc (srCd a (ω ^ 2 * (d / ω ^ 2)))) with hMdef
    have hMa : M < a := (Finset.sup_lt_iff haE.pos).2 hga
    obtain ⟨μ, hR, hγμ, hμa, hc⟩ := hcof (max γ (max M (upsilon Rz.rzLam)))
      (max_lt hγ (max_lt hMa hzua))
    have hγ' : γ < upsilon μ := (le_max_left _ _).trans_lt hγμ
    have hMρ : M < upsilon μ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hγμ
    have hzμ : Rz.rzLam < μ :=
      hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hγμ)
    have hμa' : μ < a := by rw [← hua] at hμa; exact hm.lt_iff_lt.1 hμa
    have hρE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hR.1.1))
    have hB : Bases (upsilon μ) a := ⟨hρE, haE, hμa, ha1⟩
    have hgt : ∀ d ∈ Os, Gf.gtc (srCd a (ω ^ 2 * (d / ω ^ 2))) < upsilon μ := fun d hd =>
      (Finset.le_sup (f := fun d => Gf.gtc (srCd a (ω ^ 2 * (d / ω ^ 2)))) hd).trans_lt hMρ
    have hoff := srOff hB Os hOs hgt
    have hμB : μ + eN (upsilon μ) ≤ a := srAddEN_le hm.le_apply hμa haE
    refine ⟨μ, srF (upsilon μ) a, eN (upsilon μ), hR, hγ', by rw [hua]; exact hμa, hμB,
      So.soW_dvd_E (eN_E _), (srSupE k hR hc).2, hoff, ?_⟩
    intro g hgO hg0 hgd
    have hgβ := hOs g hgO
    have hwg : ω ^ 2 * (g / ω ^ 2) = g := by
      have hm0 : g % ω ^ 2 = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hgd
      have := Ordinal.div_add_mod g (ω ^ 2); rwa [hm0, add_zero] at this
    have hgtg : Gf.gtc (srCd a g) < upsilon μ := by have := hgt g hgO; rwa [hwg] at this
    obtain ⟨hAW, -, hAr⟩ := srCd_spec haE ha1.le hgβ
    set A := srCd a g with hAdef
    have hfg : srF (upsilon μ) a g = Gf.rdc A (upsilon μ) := srF_eq hB hgβ hgd hgtg
    have hAlim : IsSuccLimit A :=
      srCode_lim hAW (by rw [hAr]; exact hg0.ne') (by rw [hAr]; exact (dvd_pow_self ω two_ne_zero).trans hgd)
    obtain ⟨hpiC, hdvd⟩ := srLim_pi hB hAW hAlim hgtg
    rw [hAr] at hpiC hdvd
    have hpv := Ls.lsPv_range hR
    obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
      (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
    have hdivμ := Ls.lsDiv_of_code hc
    have hfgB : srF (upsilon μ) a g < eN (upsilon μ) := hoff.bd g hgO
    have hfg0 : srF (upsilon μ) a g ≠ 0 := by
      rw [hfg]; exact (Gf.rdc_pos hρE hAlim.bot_lt.ne' hAW).ne'
    have hcM : cdCode S (μ + srF (upsilon μ) a g) = cdOff (cdExp (srF (upsilon μ) a g)) := by
      have := (srCode_shift hgμ hdivμ hfg0 (by rw [hpv]; exact hfgB)).2
      rwa [hιμ] at this
    have hgdW : ω ^ 2 ∣ srF (upsilon μ) a g := by rw [hfg]; exact hdvd hgd
    have hriμ : IsRestartIdx (μ + srF (upsilon μ) a g) :=
      ⟨fun h => hR.1.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hR.1.2 hgdW⟩
    have hμfa : μ + srF (upsilon μ) a g + ω + 1 < a := by
      calc μ + srF (upsilon μ) a g + ω + 1 = μ + (srF (upsilon μ) a g + ω + 1) := by
            rw [add_assoc, add_assoc, add_assoc]
        _ < μ + eN (upsilon μ) := lr_addL (a := μ) (srInner hfgB hgdW)
        _ ≤ a := hμB
    have hCμ : upsilon (μ + srF (upsilon μ) a g + ω + 1) < nuC :=
      ((hm hμfa).trans_eq hua).trans hν
    have hshμ : cdCode S (μ + srF (upsilon μ) a g) ≤ upsilon (μ + srF (upsilon μ) a g) := by
      rw [hcM]; exact (Ls.lsOff_le _ hfg0).trans (le_add_self.trans hm.le_apply)
    have hrμ : cdR S (μ + srF (upsilon μ) a g) =
        upsilon (μ + (srF (upsilon μ) a g + ω + 1)) + cdOff (cdExp (srF (upsilon μ) a g)) := by
      rw [Ls.lsR_short hriμ hCμ hshμ, hcM]; unfold cdDelta; simp only [add_assoc]
    have hRμ : CdRange S (μ + srF (upsilon μ) a g) := by
      refine ⟨hriμ, hR.2.1.trans le_self_add, ?_, ?_⟩
      · exact ((hm (lt_of_le_of_lt (le_self_add.trans le_self_add) hμfa)).trans_eq hua).trans_le haL
      · rw [hcM]
        refine (Ls.lsOff_le _ hfg0).trans_lt ((hfgB.trans ?_).trans (Lw.lw_Om1_lt_Pp S))
        rw [← hpv]; exact srEN_lt_Om1 hgμ
    refine ⟨hL _ hRμ (Or.inl (hzμ.le.trans le_self_add)), fun hbig => ?_,
      fun h hhO c hh0 hcs hr => ?_⟩
    · exfalso
      rw [hrA g hg0 hgβ hgd] at hbig
      have hgl : g < a + (g + ω + 1) :=
        lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one (g + ω))) le_add_self
      have hcl : cdOff (cdExp g) < upsilon (a + (g + ω + 1)) :=
        (Ls.lsOff_le g hg0.ne').trans_lt (hgl.trans_le hm.le_apply)
      have h1 := Ls.lsUps_add_lt hcl
      have h3 : upsilon (succ (a + (g + ω + 1))) ≤ upsilon (a + eN a) := by
        refine hm.monotone ?_
        rw [lr_succ_add]
        exact lr_addLe (a := a) (Order.succ_le_of_lt (srInner hgβ hgd))
      exact absurd (hbig.trans_lt (h1.trans_le h3)) (lt_irrefl _)
    · have hc0 : cdOff (cdExp g) < upsilon (succ a) :=
        ((Ls.lsOff_le g hg0.ne').trans_lt hgβ).trans_le hEsucc
      obtain ⟨hhh, hcc⟩ := srUps_inj (lt_of_le_of_lt zero_le (lt_add_one _)) hh0 hc0 hcs
        ((hrA g hg0 hgβ hgd).symm.trans hr)
      rw [← hhh, ← hcc, hua, hpiC, hrμ, ← hfg]
      have hres : srF (upsilon μ) a (g + ω + 1) = srF (upsilon μ) a g + (ω + 1) := by
        have h2 : ω + 1 < ω ^ 2 := by
          have := lr_omega_mul_add_one_lt 1
          rwa [Nat.cast_one, mul_one] at this
        have := srF_res (upsilon μ) a (g / ω ^ 2) (ω + 1) h2
        rw [hwg] at this
        rw [add_assoc]; exact this
      rw [hres, add_assoc]

/-- **The realizers at `m*` up to `υ_{m*+ε_{m*+1}} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem srRealE_M (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + eN (Nc.ncL S 0))) ∧
      upsilon (Nc.ncL S 0 + eN (Nc.ncL S 0)) < Nc.ncL S 1 := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsM_named (S := S)
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) 0
  have hua : upsilon (Nc.ncL S 0) = Nc.ncL S 0 := by
    have h := Bt.ups_iota S (Om ω); rw [hι] at h; exact h.trans hP
  have hb : upsilon (Nc.ncL S 0 + eN (Nc.ncL S 0)) < Nc.ncL S 1 := by
    have hu1 : upsilon (Nc.ncL S 1) = Nc.ncL S 1 := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; simpa using h.trans hP1
    have hE1 : InE (Nc.ncL S 1) := by
      have := Sl.slPv_E (S := S) (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; simpa using this
    exact srUps_lt hua hu1 (So.soE_lim hE1) (Rl.rlM_lt_L1 (S := S))
  have hL1w : Nc.ncL S 1 ≤ Nc.ncL S ω := Pp.ppL_mono one_lt_omega0.le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨srRealE_named hg hι hP hdiv hri hzl ((Rl.rlM_lt_L1 (S := S)).trans_le (hL1w.trans hlow))
    (hb.le.trans (hL1w.trans hlow)) (hb.trans_le hL1w |>.trans hLw1) (Ls.lsNames_M (S := S) 0) hU hL
    hstd (Pp.ppL_mono zero_le), hb⟩

/-- **The realizers at `L(n+1)` up to `υ_{a+ε_{a+1}} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem srRealE_L (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsL_named (S := S) n
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) (n + 1)
  have hua : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
    have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})); rw [hι] at h; exact h.trans hP
  have hb : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + eN (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) <
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
    have hu1 : upsilon (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; exact h.trans hP1
    have hE1 : InE (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) := by
      have := Sl.slPv_E (S := S) (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; exact this
    exact srUps_lt hua hu1 (So.soE_lim hE1) (Pp.ppL_lt_succ (S := S) n)
  have h2w : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (n + 1)).le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨srRealE_named hg hι hP hdiv hri hzl ((Pp.ppL_lt_omega n).trans_le hlow)
    (hb.le.trans (h2w.trans hlow)) ((hb.trans_le h2w).trans hLw1) (Ls.lsNames_L (S := S) n 0) hU hL
    hstd ((Pp.ppL_lt_omega n).le.trans hLw1.le), hb⟩

end Googology.Trans.PoR.InaccPsi.R2.Sr
