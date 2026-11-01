import Googology.Trans.PoR.InaccPsi.R2.XoTest
import Googology.Trans.PoR.InaccPsi.R2.XlW
import Googology.Trans.PoR.InaccPsi.R2.XjShift

/-!
# The supply road with moving-leaf levels

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The fourth supply road `Xb.xbRoad` / `Xj.xjRoad` is vacuous (`Xj.xbRoad_false`): its forms keep the `ϑ`-levels
constant.  `xoRoad` has the conclusion of `Xl.xlwRoad` (the current frontier `ι(Γ(φ(G+Ω₁, 0))·ω)`), with the supply
`Xo.XoVisGen` (moving-leaf forms, carry `Xo.XoCarry` over every restricted moving-leaf decomposition) at `m*` and
every `L(n+1)`, and the open bridge `Xo.XoRealB`.

* `xoReal_of_xb` (**the bridge holds wherever the forms are constant-level forms with data below some `c < υ_λ`**:
  then it is `Xj.xbRealB_holds`, with `Xo.xoSup_ww`), `xoGen_iff` (**`XoGen` is UPPER at the inner restarts and
  `XoSup`**: the forms clause always holds, `Xo.xoForms_all`), `xoVisI_of_gen`, `xoVis_all`, `xoRoadAll`, `xoRoad`, `xoRoadH` (the frontier
  of `Hl.hlU`, the argument shape of `Xb.xbRoad`);
* `xoVis_gap` (**NON-VACUITY against `Xj.xjVis_ref`**: at the window of `X′` the forms clause of `XoGen` holds; the
  refutation of the four earlier roads went through the forms clause only).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xo

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The bridge where the forms have constant levels**: `XoGen` whose forms are `Xb.XbForm`s gives the realizer
(`Xj.xbRealB_holds`; the moving-leaf carry contains the constant-level one, `xoSup_ww`). -/
theorem xoReal_of_xb {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hνβ : upsilon (l + β) ≤ nuC) (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1))
    (h : XoGen S l β)
    (hold : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ Xb.XbForm S l β g) :
    Lr.LrReal S (upsilon l) (upsilon (l + β)) :=
  Xj.xbRealB_holds l β hl hl1 hν hνβ hstd hlL ⟨h.1, hold, xoSup_ww h.2.2⟩

/-- **`XoGen` is UPPER at the inner restarts and `XoSup`** (the forms clause always holds). -/
theorem xoGen_iff {l β : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) :
    XoGen S l β ↔ (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g)) ∧ XoSup S l β :=
  ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun g _ _ _ => xoForms_all S hl0 hb1 g, h.2⟩⟩

/-- **`XoVisGen` and the bridge give the visible statements `Tk.TkVisI`.** -/
theorem xoVisI_of_gen (hB : XoRealB S) (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l)
    (hb : b ≤ nuC) (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : XoVisGen S l b c) :
    Tk.TkVisI S (upsilon l) b c := by
  refine Tk.tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, hB l β hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- The visible statements at `m*` and every `L(n+1)` from `XoVisGen` and the bridge. -/
theorem xoVis_all (hB : XoRealB S) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XoVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XoVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    Tk.TkVisI S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))) ∧
      ∀ n : ℕ, Tk.TkVisI S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})))) := by
  have hν := Sh.shNu hU hV hVt hL
  have hstd : Cx.CxStdPairTop S := Tp.tpStdPairTop hν
  have hLW : CdLOWER S := Rz.rzLOWER_of_rest hL
  have hlt : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S (ω + 1) := fun k =>
    ((Pp.ppL_lt_omega k).trans (Qq.qqL_lt_succ S)).le
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
    have h1 : Nc.ncL S 1 ≤ Nc.ncL S (ω + 1) := by simpa using hlt 0
    have := xoVisI_of_gen hB hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := xoVisI_of_gen hB hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

/-- **The road with UPPER / LOWER / CapV at every Range restart** (the common core of `xoRoad`, `xoRoadH`). -/
theorem xoRoadAll
    (hUall : ∀ l, CdRange S l → CdUpper S l)
    (hLall : ∀ l, CdRange S l → CdLower S l)
    (hVall : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hVhigh : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : XoRealB S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XoVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XoVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  have hν0 := Wd.wdNu (S := S) (fun l hr _ => hUall l hr) (fun l hr _ => hLall l hr)
    (fun l hr hu _ => hVall l hr hu) (fun l hr hu _ => hVhigh l hr hu)
  have hEQtop : Cx.CxEQtop S := (Wd.wdEQtop_iff hν0).2 ⟨hT hν0, hF hν0⟩
  have htop : Cx.CxTCtopOff S := Wa.waTCtopOff hν0
  have hmove : Cx.CxStdMoveTop S := Wa.waStdMoveTop
  have hUR : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l := fun l hr _ => hUall l hr
  have hLR : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l := fun l hr _ => hLall l hr
  have hVlow : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l :=
    fun l hr hu _ => hVall l hr hu
  have hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l := by
    intro l hr hlR hfix
    exact (Rz.rzUpper_nonfix hr.1 hlR hfix (Rz.rz_range_pv hr)).1.1 (hUall l hr)
  obtain ⟨v0, vn⟩ := xoVis_all hB hUR hLR hVlow hVhigh h0 hn
  have hv := Tk.tkRoadVis hUR hO hLR hVlow hVhigh hEQtop htop hmove v0 vn
  rcases hv with ⟨hEQ, hTC, hB2, hTT, hCL, _, _, _, _, _, _, _, _, _⟩
  have hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
    intro n
    exact (Cx.cxTCAt_L_iff hTT n).1 (hTC n _ (Cx.cxC_lt n))
  have hrest : CdTCrest S := fun n x hx => Or.inr (Or.inr (hTC n x hx))
  have hh := Hl.hlU_road S (fun l hr _ => hUall l hr) (fun l hr _ => hLall l hr)
    (fun l hr hu _ => hVall l hr hu) hCL hEQ hrest hB2
  have hν : Nc.ncL S (ω + 1) ≤ nuC := hh.1.symm.le
  exact Vp.vpRoadA (fun l hr _ => hUall l hr) (fun l hr _ => hLall l hr) (fun l hr hu _ => hVall l hr hu)
    hEQ hν Vs.vsPiLev hTT hcl

/-- **THE SUPPLY ROAD WITH MOVING-LEAF LEVELS** (conclusion of `Xl.xlwRoad`): UPPER / LOWER / CapV past
`ι(Γ(φ(G+Ω₁, 0))·ω)`, `WdThLow`, `WdEQfar` (under `L(ω+1) ≤ ν_C`), the bridge `XoRealB`, and `XoVisGen` at `m*`
and every `L(n+1)`. -/
theorem xoRoad
    (hUH : ∀ l, CdRange S l → Xl.XlWPast S l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Xl.XlWPast S l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Xl.XlWPast S l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Xl.XlWPast S l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : XoRealB S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XoVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XoVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  refine xoRoadAll (fun l hr => ?_) (fun l hr => ?_) (fun l hr hu => ?_) (fun l hr hu => ?_) hT hF hB h0 hn
  · by_cases h : Xl.XlWPast S l
    · exact hUH l hr h
    · exact (Xl.xlw_notPast S hr h).1
  · by_cases h : Xl.XlWPast S l
    · exact hLH l hr h
    · exact (Xl.xlw_notPast S hr h).2.1
  · by_cases h : Xl.XlWPast S l
    · exact hVH l hr hu h
    · exact (Xl.xlw_notPast S hr h).2.2
  · by_cases h : Xl.XlWPast S l
    · exact hVt l hr hu h
    · exact (Xl.xlw_notPast S hr h).2.2

/-- **The same road with UPPER / LOWER / CapV asked past the frontier of `Hl.hlU`** (the argument shape of
`Xb.xbRoad`, used by the skeleton root). -/
theorem xoRoadH
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : XoRealB S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XoVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XoVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  refine xoRoadAll (fun l hr => ?_) (fun l hr => ?_) (fun l hr hu => ?_) (fun l hr hu => ?_) hT hF hB h0 hn
  · by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
    · exact hUH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1
  · by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
    · exact hLH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2
  · by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  · by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
    · exact hVt l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)

/-- **NON-VACUITY against the refutation of the earlier roads** (`Xj.xjVis_ref`, `Ww.wwVis_ref`, `Wu.wuVis_ref`):
at `L(k)`, for every window `υ_{λ+β} ∈ (υ_{λ+X′+ω²}, L(k+1)]`, the forms clause of `XoGen` holds at every offset
(`xoForms_all`; at `X′` by the explicit decomposition `xoXjE`), so `XoGen` there is UPPER and `XoSup` only. -/
theorem xoVis_gap (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ1 : upsilon (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) + β))
    (hβ2 : upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) :
    (XoGen S (Nc.ncL S (k : Ordinal.{0})) β ↔
      (∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (Nc.ncL S (k : Ordinal.{0}) + g)) ∧
        XoSup S (Nc.ncL S (k : Ordinal.{0})) β) ∧
    (upsilon (Nc.ncL S (k : Ordinal.{0}) + β) ≤ cdR S (Nc.ncL S (k : Ordinal.{0}) + Xj.xjX S k) ∨
      XoForm S (Nc.ncL S (k : Ordinal.{0})) β (Xj.xjX S k)) := by
  obtain ⟨hl0, -, -, -, -, -, hL1O, -, -⟩ := Vr.vr_facts (S := S) k
  exact ⟨xoGen_iff hl0 (hβ2.trans hL1O.le), xoForm_gap k hν hβ1 hβ2⟩

end Googology.Trans.PoR.InaccPsi.R2.Xo
