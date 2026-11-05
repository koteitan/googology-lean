import Googology.Trans.PoR.InaccPsi.R2.ZoInt
import Googology.Trans.PoR.InaccPsi.R2.XhName
import Googology.Trans.PoR.InaccPsi.R2.GaEnd
import Googology.Trans.PoR.InaccPsi.R2.PhFr
import Googology.Trans.PoR.InaccPsi.R2.YfCell
import Googology.Trans.PoR.InaccPsi.R2.WjSplit
import Googology.Trans.PoR.InaccPsi.R2.GgUni

/-!
# Zo: regions (B-hi) and (C) by ONE relative block induction from the least restart index `≥ ι(Ω₂)`

Every range restart of (B-hi) (names `Ω₂·q + ζ`, `1 ≤ q`, `ζ < Ω₂`, `e(ζ) < Ω₂`, below `Ω_ω`) and of (C)
(names with `e(η) ≥ Ω₂`, all below `L(0)`) lies in `[ι(Ω₂), ι(Ω_ω))`, and every range restart below `ι(Ω₂)`
lies in (A) or (B-lo).  So both regions, the A-type cells, the far offsets and the layer cells alike, are covered
by `Zo.zoInt` on `[l₀, ι(Ω_ω))` with `l₀ = zoBase S`, the least restart index `≥ ι(Ω₂)` (no cell transport,
no base data `Yf.YfRel` at `ι(Ω₂·q)`):

* `zoBase`, `zoBase_spec`, `zoBase_le`, `zoBase_lt_iota`, `zoB0_le_base`, `zoBase_lt_top`;
* `zoName` / `zoNameC`: a (B-hi) name or a (C) name gives `ι(Ω₂) ≤ λ` and `ρ_λ < m*`;
* `zoBC` (**THE ASSEMBLY**): UPPER ∧ LOWER ∧ CapV below `ι(Ω₂)` (regions (A), (B-lo)), at the base `l₀` (if it is a
  range restart), the base reach datum at `l₀`, the pair-free inputs `Zc.ZcInR`, CapV at the `υ`-fixed
  long-exponent restarts and the RS input at the `υ`-fixed restarts of `(l₀, ι(Ω_ω))` give UPPER ∧ LOWER ∧ CapV
  at every range restart `λ ≥ ι(Ω₂)` with `ρ_λ < m*`, and `L(0) ≤ ν_C`;
* `zoBC_of_target` (**NON-VACUITY**): the inputs follow from the target on `[l₀, ι(Ω_ω))` and the chain reach data;
* `zoC_fix` (REFUTE FIRST for (C)): every (C) range restart is a `υ`-fixed point, so its inputs are those of
  the fixed restarts (no short-exponent theorem applies there);
* `zoBC_nonempty`: the induction interval is not empty (it contains the (B-hi) restarts of `Xh.xhBhi_nonempty`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The top of the induction: `ι(Ω_ω)`, with `υ = m* = L(0)`. -/
noncomputable abbrev zoTop (S : InaccSeq.{0}) : Ordinal.{0} := iota S (Om ω)

/-- **The base**: the least restart index `≥ ι(Ω₂)`. -/
noncomputable def zoBase (S : InaccSeq.{0}) : Ordinal.{0} :=
  sInf {l | IsRestartIdx l ∧ iota S (Om (1 + 1)) ≤ l}

theorem zoTop_ri : IsRestartIdx (zoTop S) := by
  have h := Yx.yxBase_ri (S := S) 0
  simpa using h

theorem zoTop_ups : upsilon (zoTop S) = cdMstar S := ups_iota S (Om ω)

theorem zoIota2_lt_top : iota S (Om (1 + 1)) < zoTop S := (Ga.gaEnd_Om2 (S := S) le_rfl).2.1

theorem zoBase_spec : IsRestartIdx (zoBase S) ∧ iota S (Om (1 + 1)) ≤ zoBase S :=
  csInf_mem (s := {l | IsRestartIdx l ∧ iota S (Om (1 + 1)) ≤ l}) ⟨zoTop S, zoTop_ri, zoIota2_lt_top.le⟩

theorem zoBase_le {l : Ordinal.{0}} (hl : IsRestartIdx l) (h : iota S (Om (1 + 1)) ≤ l) : zoBase S ≤ l :=
  csInf_le' ⟨hl, h⟩

theorem zoBase_lt_iota {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < zoBase S) :
    μ < iota S (Om (1 + 1)) := by
  by_contra h'
  exact absurd (zoBase_le hμ (not_lt.1 h')) (not_le.2 h)

theorem zoBase_le_top : zoBase S ≤ zoTop S := zoBase_le zoTop_ri zoIota2_lt_top.le

/-- `B₀ ≤ l₀`: `Λ_B ≤ ι(phB) < ι(Ω₂) ≤ l₀`, both restart indices. -/
theorem zoB0_le_base : cdB0 ≤ zoBase S := by
  have hph : iota S Ph.phB < iota S (Om (1 + 1)) :=
    cd_iota_lt_of_good (Ph.phGood fun _ hZ => Ph.ph_cl_B hZ) (Ph.ph_B_lt_Gam.trans (Gg.ggGam_lt_Om2 S))
  have hlt : VzLam < zoBase S :=
    (Ph.phFr_vz (S := S)).2.1.trans_lt (hph.trans_le zoBase_spec.2)
  have h := Lr.lr_dvd_add_le (Yf.yfBase_wit S).1.2 zoBase_spec.1.2 hlt
  rwa [pow_two] at h

/-- The induction interval is not empty: it contains a (B-hi) range restart. -/
theorem zoBC_nonempty0 : ∃ l, CdRange S l ∧ zoBase S ≤ l ∧ l < zoTop S := by
  obtain ⟨l, hr, -, h0, -, hι⟩ := Xh.xhBhi_nonempty S
  have e : Nc.ncL S 0 = cdMstar S := by rw [Lw.lw_L_eq S 0, mul_zero, add_zero]
  have hm : upsilon l < cdMstar S := e ▸ h0
  refine ⟨l, hr, zoBase_le hr.1 hι, ?_⟩
  rw [← zoTop_ups (S := S)] at hm
  exact upsilon_normal.strictMono.lt_iff_lt.1 hm

/-- **The base is a range restart** (a restart index `≥ B₀` below `m*`). -/
theorem zoBase_range : CdRange S (zoBase S) := by
  refine zoRange_lt zoBase_spec.1 zoB0_le_base ?_
  rw [← zoTop_ups (S := S)]
  rcases eq_or_lt_of_le (zoBase_le_top (S := S)) with he | hlt
  · exfalso
    obtain ⟨l, hr, hb, ht⟩ := zoBC_nonempty0 (S := S)
    exact absurd (hb.trans_lt ht) (by rw [he]; exact lt_irrefl _)
  · exact upsilon_normal.strictMono hlt

/-- **A name `Ω₂ ≤ η_λ < Ω_ω`** gives `ι(Ω₂) ≤ λ` and `ρ_λ < m*`. -/
theorem zoName {l : Ordinal.{0}} (hr : CdRange S l) (h1 : Om (1 + 1) ≤ cdEta S l) (h2 : cdEta S l < Om ω) :
    iota S (Om (1 + 1)) ≤ l ∧ upsilon l < cdMstar S := by
  obtain ⟨hg, hι, -⟩ := Wj.wjEta_spec (S := S) hr.1.1 hr.2.2.1
  refine ⟨hι ▸ iota_mono _ _ h1, ?_⟩
  have hlt : l < zoTop S := hι ▸ cd_iota_lt_of_good hg h2
  rw [← zoTop_ups (S := S)]
  exact upsilon_normal.strictMono hlt

/-- **A (C) name** (`e(η_λ) ≥ Ω₂`, `ρ_λ < L(0)`) gives `ι(Ω₂) ≤ λ` and `ρ_λ < m*`. -/
theorem zoNameC {l : Ordinal.{0}} (hr : CdRange S l) (he : Om (1 + 1) ≤ cdExp (cdEta S l))
    (h0 : upsilon l < Nc.ncL S 0) : iota S (Om (1 + 1)) ≤ l ∧ upsilon l < cdMstar S := by
  refine ⟨(Wj.wjC_props hr he).2.1, ?_⟩
  have e : Nc.ncL S 0 = cdMstar S := by rw [Lw.lw_L_eq S 0, mul_zero, add_zero]
  exact e ▸ h0

/-- The top is above the base strictly as soon as some range restart `λ ≥ ι(Ω₂)` has `ρ_λ < m*`. -/
theorem zoBase_lt_of {l : Ordinal.{0}} (hl : IsRestartIdx l) (hι : iota S (Om (1 + 1)) ≤ l)
    (hm : upsilon l < cdMstar S) : zoBase S ≤ l ∧ l < zoTop S := by
  refine ⟨zoBase_le hl hι, ?_⟩
  rw [← zoTop_ups (S := S)] at hm
  exact upsilon_normal.strictMono.lt_iff_lt.1 hm

/-- **THE ASSEMBLY FOR (B-hi) ∪ (C).** -/
theorem zoBC
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hbase : CdUpper S (zoBase S) ∧ CdLower S (zoBase S) ∧ CdCapV S (zoBase S))
    (hgiven : Yx.YxGivenIn (Ys.ysO S) (zoBase S))
    (hin : Zc.ZcInR S (zoBase S) (zoTop S))
    (hVF : ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → upsilon μ = μ → upsilon μ < nuC →
      ¬ Zh.ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (zoTop S)) :
    (zoBase S < zoTop S → Nc.ncL S 0 ≤ nuC) ∧
    ∀ l, CdRange S l → iota S (Om (1 + 1)) ≤ l → upsilon l < cdMstar S →
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hm := upsilon_normal.strictMono
  have hlowB : ∀ μ, CdRange S μ → μ < zoBase S → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ :=
    fun μ hr h => hlow μ hr (zoBase_lt_iota hr.1 h)
  have run : zoBase S < zoTop S → upsilon (zoTop S) ≤ nuC ∧
      ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ := by
    intro hlt
    refine zoInt zoBase_spec.1 zoTop_ri hlt zoTop_ups.le (fun μ hr h => ?_)
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

/-- **NON-VACUITY of `zoBC`**: its interval inputs follow from UPPER, LOWER, CapV at the range restarts of
`(l₀, ι(Ω_ω))` and the chain reach data at the restarts of `[l₀, ι(Ω_ω))`. -/
theorem zoBC_of_target (hlt : zoBase S < zoTop S)
    (hU : ∀ μ, CdRange S μ → zoBase S ≤ μ → μ < zoTop S → CdUpper S μ)
    (hL : ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → CdLower S μ)
    (hV : ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → zoBase S ≤ l → l < zoTop S → Ys.YsReachIn l 0 (upsilon l)) :
    Yx.YxGivenIn (Ys.ysO S) (zoBase S) ∧ Zc.ZcInR S (zoBase S) (zoTop S) ∧
      (∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → upsilon μ = μ → upsilon μ < nuC →
        ¬ Zh.ZhShortExp S μ → CdCapV S μ) ∧
      (∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l →
        Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (zoTop S)) :=
  zoInt_of_target zoB0_le_base zoTop_ups.le hU hL hV hR zoBase_spec.1 hlt

/-- **REFUTE FIRST for (C)**: every (C) range restart is a `υ`-fixed point (a non-fixed restart below `ν_C`'s
name bound has a short last exponent `e < ρ_λ < Ω₂`, `Zh.zh_short_of_nonfix`). -/
theorem zoC_fix {l : Ordinal.{0}} (hr : CdRange S l) (he : Om (1 + 1) ≤ cdExp (cdEta S l))
    (h0 : upsilon l < Nc.ncL S 0) : upsilon l = l := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hι, hlm⟩ := zoNameC hr he h0
  have hww : ω * ω < l := by
    have h1 : VzLam < l := by
      have hph : iota S Ph.phB < iota S (Om (1 + 1)) :=
        cd_iota_lt_of_good (Ph.phGood fun _ hZ => Ph.ph_cl_B hZ) (Ph.ph_B_lt_Gam.trans (Gg.ggGam_lt_Om2 S))
      exact (Ph.phFr_vz (S := S)).2.1.trans_lt (hph.trans_le hι)
    exact Zh.zh_ww_lt (Yf.yfBase_wit S).1 h1
  rcases eq_or_lt_of_le hm.le_apply with h | hfix
  · exact h.symm
  · exfalso
    have hs := Zh.zh_short_of_nonfix (η1 := Om ω) hr.1 hww hfix hlm
    have hlt : upsilon l < Om (1 + 1) :=
      (hlm.trans (Nm.Pv_lt_Om1 S _)).trans (Gg.gg_Om1_lt_Om2)
    exact absurd he (not_le.2 (hs.2.trans hlt))

/-- **The base is strictly below the top.** -/
theorem zoBase_lt_top : zoBase S < zoTop S := by
  obtain ⟨l, -, hb, ht⟩ := zoBC_nonempty0 (S := S)
  exact hb.trans_lt ht

/-- **`L(0) ≤ ν_C`** from the assembly's hypotheses (the interval is not empty). -/
theorem zoBC_nu
    (hlow : ∀ μ, CdRange S μ → μ < iota S (Om (1 + 1)) → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hbase : CdUpper S (zoBase S) ∧ CdLower S (zoBase S) ∧ CdCapV S (zoBase S))
    (hgiven : Yx.YxGivenIn (Ys.ysO S) (zoBase S))
    (hin : Zc.ZcInR S (zoBase S) (zoTop S))
    (hVF : ∀ μ, CdRange S μ → zoBase S < μ → μ < zoTop S → upsilon μ = μ → upsilon μ < nuC →
      ¬ Zh.ZhShortExp S μ → CdCapV S μ)
    (hrsF : ∀ l, IsRestartIdx l → zoBase S < l → l < zoTop S → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (zoTop S)) : Nc.ncL S 0 ≤ nuC :=
  (zoBC hlow hbase hgiven hin hVF hrsF).1 zoBase_lt_top

/-- **A (B-hi) name** `Ω₂·q + ζ` (`1 ≤ q`) below `Ω_ω` gives `ι(Ω₂) ≤ λ` and `ρ_λ < m*`. -/
theorem zoNameB {l q ζ : Ordinal.{0}} (hr : CdRange S l) (he : cdEta S l = Om (1 + 1) * q + ζ) (hq : 1 ≤ q)
    (hη : cdEta S l < Om ω) : iota S (Om (1 + 1)) ≤ l ∧ upsilon l < cdMstar S := by
  refine zoName hr ?_ hη
  rw [he]
  calc Om (1 + 1) = Om (1 + 1) * 1 := (mul_one _).symm
    _ ≤ Om (1 + 1) * q := mul_le_mul_left' hq _
    _ ≤ Om (1 + 1) * q + ζ := le_self_add

end Googology.Trans.PoR.InaccPsi.R2.Zo
