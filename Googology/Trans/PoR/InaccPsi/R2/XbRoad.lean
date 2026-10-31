import Googology.Trans.PoR.InaccPsi.R2.XbReal

/-!
# The road with the shift clause at `ϑ`-nodes in place of the bridge

`Ww.wwRoad` with its bridge hypothesis `hB : Ww.WwRealB S` replaced by `hS : XbShift S` (the shift
`Vl.vlShiftCore` with the `ϑ`-node clause `XbThCl`), and its supply `Ww.WwVisGen` by `XbVisGen` (the repaired forms
with constant `ϑ`-levels; `XbVisGen ⇒ Ww.WwVisGen`, `xbVisGen_ww`).

* `xbVisI_of_gen`, `xbVis_all`, `xbRoad` (**the conclusion of `Ww.wwRoad` from hUH, hLH, hVH, hVt, hT, hF,
  `XbShift S`, `XbVisGen` at `m*` and every `L(n+1)`**), `xbRoadZ` (the same with UPPER / LOWER / CapV only above
  the frontier `F_Z` of `Ws.wsRoadZ`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`XbVisGen` and the bridge give the visible statements `Tk.TkVisI`.** -/
theorem xbVisI_of_gen (hB : XbRealB S) (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l)
    (hb : b ≤ nuC) (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : XbVisGen S l b c) :
    Tk.TkVisI S (upsilon l) b c := by
  refine Tk.tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, hB l β hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- The visible statements at `m*` and every `L(n+1)` from `XbVisGen` and the bridge. -/
theorem xbVis_all (hB : XbRealB S) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
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
    have := xbVisI_of_gen hB hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := xbVisI_of_gen hB hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

/-- **THE ROAD WITH THE REPAIRED SUPPLY** (conclusion of `Wf.wfRoad`): UPPER / LOWER / CapV above the frontier of
`Hl.hlU`, `WdThLow`, `WdEQfar` (under `L(ω+1) ≤ ν_C`), the shift `XbShift` (in place of the bridge `Ww.WwRealB`), and `XbVisGen` at `m*` and every
`L(n+1)`. -/
theorem xbRoad
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  have hν0 := Wd.wdNu hUH hLH hVH hVt
  have hEQtop : Cx.CxEQtop S := (Wd.wdEQtop_iff hν0).2 ⟨hT hν0, hF hν0⟩
  have htop : Cx.CxTCtopOff S := Wa.waTCtopOff hν0
  have hmove : Cx.CxStdMoveTop S := Wa.waStdMoveTop
  let F : Ordinal.{0} := Bt.iota S (Gc.gcG Hl.hlU.B * ω)
  have hUall : ∀ l, CdRange S l → CdUpper S l := by
    intro l hr
    by_cases h : F ≤ l
    · exact hUH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).1
  have hLall : ∀ l, CdRange S l → CdLower S l := by
    intro l hr
    by_cases h : F ≤ l
    · exact hLH l hr h
    · exact (Hl.hlU_enum S hr (lt_of_not_ge h)).2
  have hVlow : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hVhigh : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l := by
    intro l hr hu
    by_cases h : F ≤ l
    · exact hVt l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  have hUR : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l := fun l hr _ => hUall l hr
  have hLR : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l := fun l hr _ => hLall l hr
  have hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l := by
    intro l hr hlR hfix
    exact (Rz.rzUpper_nonfix hr.1 hlR hfix (Rz.rz_range_pv hr)).1.1 (hUall l hr)
  obtain ⟨v0, vn⟩ := xbVis_all (xbRealB hS) hUR hLR hVlow hVhigh h0 hn
  have hv := Tk.tkRoadVis hUR hO hLR hVlow hVhigh hEQtop htop hmove v0 vn
  rcases hv with ⟨hEQ, hTC, hB2, hTT, hCL, _, _, _, _, _, _, _, _, _⟩
  have hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1)) := by
    intro n
    exact (Cx.cxTCAt_L_iff hTT n).1 (hTC n _ (Cx.cxC_lt n))
  have hrest : CdTCrest S := fun n x hx => Or.inr (Or.inr (hTC n x hx))
  have hh := Hl.hlU_road S hUH hLH hVH hCL hEQ hrest hB2
  have hν : Nc.ncL S (ω + 1) ≤ nuC := hh.1.symm.le
  have hUV : ∀ l, CdRange S l → Bt.iota S Ge.geV ≤ l → CdUpper S l := fun l hr _ => hUall l hr
  have hLV : ∀ l, CdRange S l → Bt.iota S Ge.geV ≤ l → CdLower S l := fun l hr _ => hLall l hr
  have hVV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → CdCapV S l := by
    intro l hr hu _
    by_cases h : F ≤ l
    · exact hVH l hr hu h
    · exact Hl.hlU_capV S hr (lt_of_not_ge h)
  exact Vp.vpRoadA hUV hLV hVV hEQ hν Vs.vsPiLev hTT hcl

/-- **The repaired road over the current frontier** `F_Z = ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)` of `Ws.wsRoadZ`: UPPER / LOWER /
CapV asked only above `F_Z`. -/
theorem xbRoadZ
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hS : XbShift S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      XbVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      XbVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  have h := xbRoad (S := S) (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_)
    hT hF hS h0 hn
  · exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG Ws.wsVz.B * ω)) with h | h
    · exact (Ws.wsZ_enum S hr h).1
    · exact hUH l hr h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG Ws.wsVz.B * ω)) with h | h
    · exact (Ws.wsZ_enum S hr h).2
    · exact hLH l hr h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG Ws.wsVz.B * ω)) with h | h
    · exact Ws.wsZ_capV S hr h
    · exact hVH l hr hu h
  · rcases lt_or_ge l (Bt.iota S (Gc.gcG Ws.wsVz.B * ω)) with h | h
    · exact Ws.wsZ_capV S hr h
    · exact hVt l hr hu h

end Googology.Trans.PoR.InaccPsi.R2.Xb
