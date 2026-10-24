import Googology.Trans.PoR.InaccPsi.R2.TbCS

/-!
# Realizers at `m*` and every `L(n+1)` up to `υ_{a+V(a)}` for any offset code system `TbCS`

The proofs are those of `R2.SuReal` with `Su.SuCS` replaced by `Tb.TbCS`.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`K : TbCS` an offset code system with bound `V`.  `a = m*` or `a = L(n+1)`, a named point with `ι(η_a) = a = P(η_a)`,
`ω^{Ω₁} ∣ η_a`.  The inner restarts below `υ_{a+V(a)}` are `a + g`, `0 < g < V(a)`, with name `η_a + g` and short
code `-1 + e(g)` (`TbCS.tbCode_shift`).  Write `g = R c a` (`c` the code of `g`, gate below `a`).  For a Range
restart `μ` (code `G_{k+1}+1`) with `ρ_μ` above the gates of the configuration, the offset map `g ↦ R c ρ_μ` is
`π_{ρ_μ,a}` (`TbCS.tbF`), and the image restart `μ + R c ρ_μ` has the code `-1 + e(R c ρ_μ) = π_{ρ_μ,a}(-1 + e(g))`
(`TbCS.tbLim_pi`).  The realizer map is `π_{ρ_μ,a}` on `seg(a)` (`Sr.srReal_gen`); the supply
`υ_{μ+V(ρ_μ)} ≤ r(μ)` is `TbCS.tbSup`.

* `tbV_le_ups` (`V(a) ≤ υ_{a+1}`), `tbUps_named_lt` (`υ_{a+V(a)} < b` for a `υ`-fixed `ε`-number `b > a`);
* `tbReal_named` (**`LrReal S a υ_{a+V(a)}`** at a named point), `tbReal_M`, `tbReal_L` (**at `m*` and at every
  `L(n+1)`, given `L(ω) ≤ ν_C`**, with `υ_{a+V(a)}` below the next point).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- `V(a) ≤ υ_{a+1}` at a named point `a = ι(η_a) = P(η_a)`. -/
theorem tbV_le_ups (K : TbCS) {a ηa : Ordinal.{0}} (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a)
    (hP : Nm.Pv S ηa = a) : K.V a ≤ upsilon (succ a) := by
  have h1 : Bt.iota S (ηa + 1) = a + 1 := by rw [Bt.iota_good hg, hι]
  have h2 : upsilon (succ a) = Nm.Pv S (ηa + 1) := by
    rw [succ_eq_add_one, ← h1, Bt.ups_iota]
  rw [h2]
  have := K.tbV_le_succ hg
  rwa [hP] at this

/-- **Realizer maps at a named point `a` up to `υ_{a+V(a)}`**, the offset map `π_{ρ_μ,a}` through the codes of `K`. -/
theorem tbReal_named (K : TbCS) {a ηa : Ordinal.{0}} {k : ℕ}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνβ : upsilon (a + K.V a) ≤ nuC) (hβL : upsilon (a + K.V a) < Nc.ncL S (ω + 1))
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧
      cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : Cx.CxStdPairTop S) (haL : a ≤ Nc.ncL S (ω + 1)) :
    LrReal S a (upsilon (a + K.V a)) := by
  classical
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have ha1' : a < Om 1 := by rw [← hP]; exact Nm.Pv_lt_Om1 S ηa
  have ha1 : a < Om1 := by rw [Br.Om1_eq]; exact ha1'
  have haE : InE a := by rw [← hP]; exact Sl.slPv_E ηa
  have haU : UpsPt a := by rw [← hua]; exact upsPt_upsilon (pos_iff_ne_zero.2 hri.1)
  have hVa1 : K.V a < Om 1 := by have := K.tbV_lt_Om1 hg; rwa [hP] at this
  have hVE : InE (K.V a) := K.V_E a haE ha1
  have hB0a : cdB0 < a := by
    obtain ⟨μ, hR, -, h2, -⟩ := hcof 0 (pos_iff_ne_zero.2 hri.1)
    refine lt_of_le_of_lt hR.2.1 ?_
    rw [← hua] at h2; exact hm.lt_iff_lt.1 h2
  have hgP : ∀ g, g < K.V a → g < K.V (Nm.Pv S ηa) := fun g h => by rw [hP]; exact h
  have hEsucc : K.V a ≤ upsilon (succ a) := tbV_le_ups K hg hι hP
  -- the codes and the reaches at the inner restarts `a + g`
  have hcodeA : ∀ g, 0 < g → g < K.V a → cdCode S (a + g) = cdOff (cdExp g) := by
    intro g hg0 hgβ
    have := (K.tbCode_shift hg hdiv hg0.ne' (hgP g hgβ)).2
    rwa [hι] at this
  have hrA : ∀ g, 0 < g → g < K.V a → ω ^ 2 ∣ g →
      cdR S (a + g) = upsilon (a + (g + ω + 1)) + cdOff (cdExp g) := by
    intro g hg0 hgβ hgd
    have hri' : IsRestartIdx (a + g) := ⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le),
      dvd_add hri.2 hgd⟩
    have hC : upsilon (a + g + ω + 1) < nuC := by
      refine lt_of_lt_of_le (hm ?_) hνβ
      rw [add_assoc, add_assoc]; exact lr_addL (a := a) (by rw [← add_assoc]; exact Su.suInner hVE hgβ hgd)
    have hsh : cdCode S (a + g) ≤ upsilon (a + g) := by
      rw [hcodeA g hg0 hgβ]
      exact (Ls.lsOff_le g hg0.ne').trans (le_add_self.trans hm.le_apply)
    rw [Ls.lsR_short hri' hC hsh, hcodeA g hg0 hgβ]
    unfold cdDelta; simp only [add_assoc]
  have hreal := Sr.srReal_gen (S := S) (l := a) (β := K.V a) hri (by rw [hua]; exact ha1)
    (by rw [hua]; exact hν) hνβ ?_ ?_ ?_ hstd (by rw [hua]; exact haL)
  · rwa [hua] at hreal
  · -- UPPER at the inner restarts
    intro g hg0 hgβ hgd
    refine hU _ ⟨⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hri.2 hgd⟩,
      hB0a.le.trans le_self_add, (hm (lr_addL (a := a) hgβ)).trans hβL, ?_⟩
      (Or.inl (hzl.le.trans le_self_add))
    rw [hcodeA g hg0 hgβ]
    exact (Ls.lsOff_le g hg0.ne').trans_lt ((hgβ.trans hVa1).trans (Lw.lw_Om1_lt_Pp S))
  · -- the form of the inner reaches
    intro g hg0 hgβ hgd
    refine Or.inr ⟨g + ω + 1, cdOff (cdExp g), lt_of_le_of_lt zero_le (lt_add_one _), Su.suInner hVE hgβ hgd,
      ((Ls.lsOff_le g hg0.ne').trans_lt hgβ).trans_le hEsucc, hrA g hg0 hgβ hgd⟩
  · -- the Range restarts, the offset map `π_{ρ_μ,a}`, the supply and the carry
    intro γ hγ Os hOs
    rw [hua] at hγ
    have hzua : upsilon Rz.rzLam < a := by rw [← hua]; exact hm hzl
    have hwOs : ∀ d ∈ Os, ω ^ 2 * (d / ω ^ 2) < K.V a := fun d hd =>
      (le_self_add.trans_eq (Ordinal.div_add_mod d (ω ^ 2))).trans_lt (hOs d hd)
    have hga : ∀ d ∈ Os, K.G (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) < a := fun d hd =>
      (K.tbCd_spec haE ha1 (hwOs d hd)).2.1
    set M := Os.sup (fun d => K.G (K.tbCd a (ω ^ 2 * (d / ω ^ 2)))) with hMdef
    have hMa : M < a := (Finset.sup_lt_iff haE.pos).2 hga
    obtain ⟨μ, hR, hγμ, hμa, hc⟩ := hcof (max γ (max M (upsilon Rz.rzLam)))
      (max_lt hγ (max_lt hMa hzua))
    have hγ' : γ < upsilon μ := (le_max_left _ _).trans_lt hγμ
    have hMρ : M < upsilon μ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hγμ
    have hzμ : Rz.rzLam < μ :=
      hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hγμ)
    have hρE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hR.1.1))
    have hρ1 : upsilon μ < Om1 := hμa.trans ha1
    have hB : Bases (upsilon μ) a := ⟨hρE, haE, hμa, ha1⟩
    have hgt : ∀ d ∈ Os, K.G (K.tbCd a (ω ^ 2 * (d / ω ^ 2))) < upsilon μ := fun d hd =>
      (Finset.le_sup (f := fun d => K.G (K.tbCd a (ω ^ 2 * (d / ω ^ 2)))) hd).trans_lt hMρ
    have hoff := K.tbOff hB Os hOs hgt
    have hVρE : InE (K.V (upsilon μ)) := K.V_E _ hρE hρ1
    have hμB : μ + K.V (upsilon μ) ≤ a :=
      Su.suAddV_le hm.le_apply (K.V_gt _ hρE hρ1) hVρE (K.V_le _ _ hρE hρ1 hμa haU)
    refine ⟨μ, K.tbF (upsilon μ) a, K.V (upsilon μ), hR, hγ', by rw [hua]; exact hμa, hμB,
      So.soW_dvd_E hVρE, (K.tbSup k hR hc).2, hoff, ?_⟩
    intro g hgO hg0 hgd
    have hgβ := hOs g hgO
    have hwg : ω ^ 2 * (g / ω ^ 2) = g := by
      have hm0 : g % ω ^ 2 = 0 := (Ordinal.dvd_iff_mod_eq_zero).1 hgd
      have := Ordinal.div_add_mod g (ω ^ 2); rwa [hm0, add_zero] at this
    have hgtg : K.G (K.tbCd a g) < upsilon μ := by have := hgt g hgO; rwa [hwg] at this
    obtain ⟨hAW, -, hAr⟩ := K.tbCd_spec haE ha1 hgβ
    set A := K.tbCd a g with hAdef
    have hfg : K.tbF (upsilon μ) a g = K.R A (upsilon μ) := K.tbF_eq hB hgβ hgd hgtg
    have hAlim : IsSuccLimit A :=
      K.tbCode_lim hAW (by rw [hAr]; exact hg0.ne') (by rw [hAr]; exact (dvd_pow_self ω two_ne_zero).trans hgd)
    obtain ⟨hpiC, hdvd⟩ := K.tbLim_pi hB hAW hAlim hgtg
    rw [hAr] at hpiC hdvd
    have hpv := Ls.lsPv_range hR
    obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
      (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
    have hdivμ := Ls.lsDiv_of_code hc
    have hfgB : K.tbF (upsilon μ) a g < K.V (upsilon μ) := hoff.bd g hgO
    have hfg0 : K.tbF (upsilon μ) a g ≠ 0 := by
      rw [hfg]; exact (K.R_pos hρE hAW hAlim.bot_lt.ne' hgtg).ne'
    have hcM : cdCode S (μ + K.tbF (upsilon μ) a g) = cdOff (cdExp (K.tbF (upsilon μ) a g)) := by
      have := (K.tbCode_shift hgμ hdivμ hfg0 (by rw [hpv]; exact hfgB)).2
      rwa [hιμ] at this
    have hgdW : ω ^ 2 ∣ K.tbF (upsilon μ) a g := by rw [hfg]; exact hdvd hgd
    have hriμ : IsRestartIdx (μ + K.tbF (upsilon μ) a g) :=
      ⟨fun h => hR.1.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hR.1.2 hgdW⟩
    have hμfa : μ + K.tbF (upsilon μ) a g + ω + 1 < a := by
      calc μ + K.tbF (upsilon μ) a g + ω + 1 = μ + (K.tbF (upsilon μ) a g + ω + 1) := by
            rw [add_assoc, add_assoc, add_assoc]
        _ < μ + K.V (upsilon μ) := lr_addL (a := μ) (Su.suInner hVρE hfgB hgdW)
        _ ≤ a := hμB
    have hCμ : upsilon (μ + K.tbF (upsilon μ) a g + ω + 1) < nuC :=
      ((hm hμfa).trans_eq hua).trans hν
    have hshμ : cdCode S (μ + K.tbF (upsilon μ) a g) ≤ upsilon (μ + K.tbF (upsilon μ) a g) := by
      rw [hcM]; exact (Ls.lsOff_le _ hfg0).trans (le_add_self.trans hm.le_apply)
    have hrμ : cdR S (μ + K.tbF (upsilon μ) a g) =
        upsilon (μ + (K.tbF (upsilon μ) a g + ω + 1)) + cdOff (cdExp (K.tbF (upsilon μ) a g)) := by
      rw [Ls.lsR_short hriμ hCμ hshμ, hcM]; unfold cdDelta; simp only [add_assoc]
    have hRμ : CdRange S (μ + K.tbF (upsilon μ) a g) := by
      refine ⟨hriμ, hR.2.1.trans le_self_add, ?_, ?_⟩
      · exact ((hm (lt_of_le_of_lt (le_self_add.trans le_self_add) hμfa)).trans_eq hua).trans_le haL
      · rw [hcM]
        refine (Ls.lsOff_le _ hfg0).trans_lt ((hfgB.trans ?_).trans (Lw.lw_Om1_lt_Pp S))
        rw [← hpv]; exact K.tbV_lt_Om1 hgμ
    refine ⟨hL _ hRμ (Or.inl (hzμ.le.trans le_self_add)), fun hbig => ?_,
      fun h hhO c hh0 hcs hr => ?_⟩
    · exfalso
      rw [hrA g hg0 hgβ hgd] at hbig
      have hgl : g < a + (g + ω + 1) :=
        lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one (g + ω))) le_add_self
      have hcl : cdOff (cdExp g) < upsilon (a + (g + ω + 1)) :=
        (Ls.lsOff_le g hg0.ne').trans_lt (hgl.trans_le hm.le_apply)
      have h1 := Ls.lsUps_add_lt hcl
      have h3 : upsilon (succ (a + (g + ω + 1))) ≤ upsilon (a + K.V a) := by
        refine hm.monotone ?_
        rw [lr_succ_add]
        exact lr_addLe (a := a) (Order.succ_le_of_lt (Su.suInner hVE hgβ hgd))
      exact absurd (hbig.trans_lt (h1.trans_le h3)) (lt_irrefl _)
    · have hc0 : cdOff (cdExp g) < upsilon (succ a) :=
        ((Ls.lsOff_le g hg0.ne').trans_lt hgβ).trans_le hEsucc
      obtain ⟨hhh, hcc⟩ := Sr.srUps_inj (lt_of_le_of_lt zero_le (lt_add_one _)) hh0 hc0 hcs
        ((hrA g hg0 hgβ hgd).symm.trans hr)
      rw [← hhh, ← hcc, hua, hpiC, hrμ, ← hfg]
      have hres : K.tbF (upsilon μ) a (g + ω + 1) = K.tbF (upsilon μ) a g + (ω + 1) := by
        have h2 : ω + 1 < ω ^ 2 := by
          have := lr_omega_mul_add_one_lt 1
          rwa [Nat.cast_one, mul_one] at this
        have := K.tbF_res (upsilon μ) a (g / ω ^ 2) (ω + 1) h2
        rw [hwg] at this
        rw [add_assoc]; exact this
      rw [hres, add_assoc]

/-- `υ_{a+V(a)} < b` at a named point `a = ι(η) = P(η)` below a `υ`-fixed `ε`-number `b`. -/
theorem tbUps_named_lt (K : TbCS) {a ηa b : Ordinal.{0}} (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a)
    (hP : Nm.Pv S ηa = a) (hub : upsilon b = b) (hbE : InE b) (hab : a < b) :
    upsilon (a + K.V a) < b := by
  have ha1 : a < Om1 := by rw [Br.Om1_eq, ← hP]; exact Nm.Pv_lt_Om1 S ηa
  have haE : InE a := by rw [← hP]; exact Sl.slPv_E ηa
  exact Su.suUps_lt hub (So.soE_lim hbE) hab (K.V_E a haE ha1) (K.V_gt a haE ha1) (tbV_le_ups K hg hι hP)

/-- **The realizers at `m*` up to `υ_{m*+V(m*)} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem tbReal_M (K : TbCS) (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0))) ∧
      upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0)) < Nc.ncL S 1 := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsM_named (S := S)
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) 0
  have hb : upsilon (Nc.ncL S 0 + K.V (Nc.ncL S 0)) < Nc.ncL S 1 := by
    have hu1 : upsilon (Nc.ncL S 1) = Nc.ncL S 1 := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; simpa using h.trans hP1
    have hE1 : InE (Nc.ncL S 1) := by
      have := Sl.slPv_E (S := S) (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; simpa using this
    exact tbUps_named_lt K hg hι hP hu1 hE1 (Rl.rlM_lt_L1 (S := S))
  have hL1w : Nc.ncL S 1 ≤ Nc.ncL S ω := Pp.ppL_mono one_lt_omega0.le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨tbReal_named K hg hι hP hdiv hri hzl ((Rl.rlM_lt_L1 (S := S)).trans_le (hL1w.trans hlow))
    (hb.le.trans (hL1w.trans hlow)) (hb.trans_le hL1w |>.trans hLw1) (Ls.lsNames_M (S := S) 0) hU hL
    hstd (Pp.ppL_mono zero_le), hb⟩

/-- **The realizers at `L(n+1)` up to `υ_{a+V(a)} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem tbReal_L (K : TbCS) (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsL_named (S := S) n
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) (n + 1)
  have hb : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + K.V (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) <
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
    have hu1 : upsilon (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; exact h.trans hP1
    have hE1 : InE (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) := by
      have := Sl.slPv_E (S := S) (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; exact this
    exact tbUps_named_lt K hg hι hP hu1 hE1 (Pp.ppL_lt_succ (S := S) n)
  have h2w : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (n + 1)).le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨tbReal_named K hg hι hP hdiv hri hzl ((Pp.ppL_lt_omega n).trans_le hlow)
    (hb.le.trans (h2w.trans hlow)) ((hb.trans_le h2w).trans hLw1) (Ls.lsNames_L (S := S) n 0) hU hL
    hstd ((Pp.ppL_lt_omega n).le.trans hLw1.le), hb⟩

end Googology.Trans.PoR.InaccPsi.R2.Tb
