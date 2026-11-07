import Googology.Trans.PoR.InaccPsi.R2.ZoBC
import Googology.Trans.PoR.InaccPsi.R2.ZnWin
import Googology.Trans.PoR.InaccPsi.R2.ZtIso

/-!
# Zo: the block induction on `[l₀, ι(Ω_ω))` with the value input

`Zo.zoInt`, `Zo.zoBC` take at the `υ`-fixed restarts the RS input `Zc.ZcRsIn ∨ Zh.ZhSupInB`.  The windows take
also the value input `Zn.ZnRsVal` (from the code continuity, `Zn.znVal_of_cont`, by `Zn.znRs_all`).  Here the same for
the block `[l₀, ι(Ω_ω))`, `l₀ = Zo.zoBase S`:

* `zoInt3`, `zoBC3`, `zoBC3_nu` (**`zoInt`, `zoBC`, `zoBC_nu` with the input `ZcRsIn ∨ ZhSupInB ∨ ZnRsVal`**, given
  `υ_B ≤ ν_C`; `Zn.znIn_of_B`, `Zn.znRs_all` in place of `Zh.zhIn_of_B`, `Zh.zhRs_all`);
* `zoRsF3` (**the input at the `υ`-fixed restarts of the block from three parts**: the short readings
  (`Zn.znRsIn_fixShort`), the isolated restarts (`Zt.ztIsoCode`), the code continuity where `ρ_λ < Θ_λ(m_λ) ≤ υ_{λ+1}`
  and LOWER or the supply where `υ_{λ+1} < Θ_λ(m_λ)`, by `Zn.znRsF_of_parts2`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The relative block induction on `[l₀, B)` with the value input** (`zoInt` with `Zn.ZnRsVal`). -/
theorem zoInt3 {l0 B : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hB : IsRestartIdx B) (hlt : l0 < B)
    (hBm : upsilon B ≤ cdMstar S)
    (hcap : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ)
    (hLlow : ∀ μ, CdRange S μ → μ < l0 → CdLower S μ)
    (hbase0 : CdRange S l0 → CdCapAt S l0 ∧ CdLower S l0)
    (hgiven : Yx.YxGivenIn (Ys.ysO S) l0)
    (hin : Zc.ZcInR S l0 B)
    (hVF : ∀ μ, CdRange S μ → l0 < μ → μ < B → upsilon μ = μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ →
      CdCapV S μ)
    (hrsF : ∀ l, IsRestartIdx l → l0 < l → l < B → upsilon l = l → upsilon B ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B ∨ Zn.ZnRsVal (Ys.ysO S) l) :
    upsilon B ≤ nuC ∧ ∀ μ, CdRange S μ → l0 < μ → μ < B → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ := by
  have hm := upsilon_normal.strictMono
  have hρB : upsilon l0 < upsilon B := hm hlt
  have hBP : upsilon B ≤ Pv S (Om ω) := hBm
  have hB1 : B < Om1 :=
    hm.le_apply.trans_lt (hBm.trans_lt (by rw [Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _))
  -- the base below `ν_C`
  have hρ0 : upsilon l0 < nuC :=
    zoNu_gt0 (hρB.le.trans hBm) fun μ hμ hB' h => hcap μ (zoRange_lt hμ hB' (h.trans (hρB.trans_le hBm))) h
  have Sp : Yx.YxSpec (Ys.ysO S) l0 B := by
    refine ⟨hl0, (ri_iff.1 hB).2, hB1, hlt, land_C hl0 hρ0.le, fun l hl h0 h1 => ?_⟩
    rcases h0.lt_or_eq with h0 | rfl
    · exact hin l hl h0 h1
    · exact Or.inr hgiven
  -- CapV below `ν_C` on the interval
  have hVL : ∀ μ, CdRange S μ → l0 < μ → μ < B → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → CdCapV S μ := by
    intro μ hr h0 h1 hμν hns
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hVF μ hr h0 h1 he.symm hμν hns
    · exfalso
      exact hns (Zh.zh_short_of_nonfix hr.1 (Zh.zh_ww_lt hl0 h0) hfix ((hm h1).trans_le hBP))
  have hVν : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → upsilon μ < nuC →
      CdCapV S μ := by
    intro μ hr h0 h1 hν
    obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
    exact Zh.zhCapV_of hr hν (h1.trans_le hBP) (hVL μ hr i0 i1 hν)
  obtain ⟨hν, Sp'⟩ := zoSpec_caps0 Sp hBm hcap (fun h => (hbase0 h).1) (fun μ _ => rfl) hVν
  -- LOWER at the range restarts `≤ l₀`
  have hL0 : ∀ μ, CdRange S μ → μ ≤ l0 → CdLower S μ := by
    intro μ hr hμ
    rcases hμ.lt_or_eq with hμ | rfl
    · exact hLlow μ hr hμ
    · exact (hbase0 hr).2
  -- the RS input at every restart of the interval
  have hrs : ∀ l, IsRestartIdx l → l0 < l → l < B →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupIn S l B ∨ Zn.ZnRsVal (Ys.ysO S) l := by
    intro l hl h1 h2
    refine Zn.znIn_of_B hl hν hBP h2 ?_
    rcases eq_or_lt_of_le hm.le_apply with he | hfix
    · exact hrsF l hl h1 h2 he.symm hν
    · exact Or.inl (Zh.zhRsIn_nonfix hl (Zh.zh_ww_lt hl0 h1) hfix ((hm h2).trans_le hν)
        ((hm h2).trans_le hBP))
  have hRS := Zn.znRs_all Sp' hν (fun μ _ => rfl) hL0 hrs
  refine ⟨hν, fun μ hr h0 h1 => ?_⟩
  have hR : upsilon (μ + ω + 1) + Ys.ysO S μ = cdR S μ := Ys.ysO_eq S μ
  have hU : CdUpper S μ := Ys.ysUpper_all Sp' hr.1 h0.le h1 hR
  have hL : CdLower S μ := by unfold CdLower; rw [← hR]; exact hRS μ hr.1 h0 h1
  exact ⟨hU, hL, Zh.zhCapV_of hr ((hm h1).trans_le hν) ((hm h1).trans_le hBP)
    (hVL μ hr h0 h1 ((hm h1).trans_le hν))⟩

/-- **Regions (B-hi) and (C) with the value input** (`zoBC` with `Zn.ZnRsVal`). -/
theorem zoBC3
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hbase : CdUpper S (zoBase S) ∧ CdLower S (zoBase S) ∧ CdCapV S (zoBase S))
    (hgiven : Yx.YxGivenIn (Ys.ysO S) (zoBase S))
    (hin : Zc.ZcInR S (zoBase S) (zoTop S))
    (hVF : ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → upsilon μ = μ → upsilon μ < nuC →
      ¬ Zh.ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l → upsilon (zoTop S) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (zoTop S) ∨ Zn.ZnRsVal (Ys.ysO S) l) :
    (zoBase S < zoTop S → Nc.ncL S 0 ≤ nuC) ∧
    ∀ l, CdRange S l → iota S (Om (1 + 1)) ≤ l → upsilon l < cdMstar S →
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hm := upsilon_normal.strictMono
  have hlowB : ∀ μ, CdRange S μ → μ < zoBase S → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ :=
    fun μ hr h => hlow μ hr (zoBase_lt_iota hr.1 h)
  have run : zoBase S < zoTop S → upsilon (zoTop S) ≤ nuC ∧
      ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ := by
    intro hlt
    refine zoInt3 zoBase_spec.1 zoTop_ri hlt zoTop_ups.le (fun μ hr h => ?_)
      (fun μ hr h => (hlowB μ hr h).2.1)
      (fun _ => ⟨cdCapAt_of_upper hbase.1 hbase.2.2, hbase.2.1⟩) hgiven hin hVF hrsF
    have h' : μ < zoBase S := hm.lt_iff_lt.1 h
    exact cdCapAt_of_upper (hlowB μ hr h').1 (hlowB μ hr h').2.2
  refine ⟨fun hlt => ?_, fun l hr hι hlm => ?_⟩
  · have e : Nc.ncL S 0 = upsilon (zoTop S) := by
      rw [zoTop_ups, Lw.lw_L_eq S 0, mul_zero, add_zero]
    rw [e]; exact (run hlt).1
  · obtain ⟨hb, ht⟩ := zoBase_lt_of hr.1 hι hlm
    rcases eq_or_lt_of_le hb with he | hlt
    · rw [← he]; exact hbase
    · exact (run (hlt.trans ht)).2 l hr hlt ht

/-- **`L(0) ≤ ν_C`** from the hypotheses of `zoBC3` (the interval is not empty). -/
theorem zoBC3_nu
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hbase : CdUpper S (zoBase S) ∧ CdLower S (zoBase S) ∧ CdCapV S (zoBase S))
    (hgiven : Yx.YxGivenIn (Ys.ysO S) (zoBase S))
    (hin : Zc.ZcInR S (zoBase S) (zoTop S))
    (hVF : ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → upsilon μ = μ → upsilon μ < nuC →
      ¬ Zh.ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l → upsilon (zoTop S) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (zoTop S) ∨ Zn.ZnRsVal (Ys.ysO S) l) : Nc.ncL S 0 ≤ nuC :=
  (zoBC3 hlow hbase hgiven hin hVF hrsF).1 zoBase_lt_top


/-- **The input at the `υ`-fixed restarts of the block from three parts.** -/
theorem zoRsF3
    (hP1 : ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l → ¬ Cp.CpIso l →
      upsilon (zoTop S) ≤ nuC → upsilon l < cdTheta S l (cdCode S l) →
      cdTheta S l (cdCode S l) ≤ upsilon (succ l) → Zn.ZnThCont S l)
    (hP2 : ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l → ¬ Cp.CpIso l →
      upsilon (zoTop S) ≤ nuC → upsilon (succ l) < cdTheta S l (cdCode S l) →
      CdLower S l ∨ Zh.ZhSupInB S l (zoTop S)) :
    ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l → upsilon (zoTop S) ≤ nuC →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (zoTop S) ∨ Zn.ZnRsVal (Ys.ysO S) l := by
  intro l hl h0 h1 hfix hνB
  have hm : upsilon l < cdMstar S := by rw [← zoTop_ups (S := S)]; exact upsilon_normal.strictMono h1
  have hlν : upsilon l < nuC := (upsilon_normal.strictMono h1).trans_le hνB
  by_cases hθ : cdTheta S l (cdCode S l) ≤ upsilon l
  · exact Or.inl (Zn.znRsIn_fixShort (η1 := Om ω) hl hfix hlν hm hθ)
  · exact Zn.znRsF_of_parts2 (Zt.ztIsoCode _ _) hP1 hP2 l hl h0 h1 hfix hνB (not_le.1 hθ)

end Googology.Trans.PoR.InaccPsi.R2.Zo
