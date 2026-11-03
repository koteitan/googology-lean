import Googology.Trans.PoR.InaccPsi.R2.YqReal

/-!
# The supply road with the bridge asked only on the windows `υ_{λ+β} ≤ L(ω+1)`

`Xo.xoRoadH` uses its bridge `Xo.XoRealB` only through `Xo.xoVisI_of_gen`, at windows `υ_{λ+β} ≤ b ≤ L(ω+1)`.  The
four theorems of `R2.XoRoad` are restated with `Yq.XoRealBL` (`yqVisI_of_gen`, `yqVis_all`, `yqRoadAll`,
`yqRoadH`; `Xo.XoRealB S ⇒ Yq.XoRealBL S` is `Yq.yqRealBL_of`, so the new road asks less), and `yqRoadS` is the road
with the bridge replaced by the shift clause `Yq.XoShift S` (`Yq.yqRealBL`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xo

variable {S : InaccSeq.{0}}

/-- **`XoVisGen` and the bridge `XoRealBL` give the visible statements `Tk.TkVisI`.** -/
theorem yqVisI_of_gen (hB : XoRealBL S) (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l)
    (hb : b ≤ nuC) (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : XoVisGen S l b c) :
    Tk.TkVisI S (upsilon l) b c := by
  refine Tk.tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, hB l β hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) (hβb.trans hbL) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- The visible statements at `m*` and every `L(n+1)` from `XoVisGen` and the bridge `XoRealBL`. -/
theorem yqVis_all (hB : XoRealBL S) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
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
    have := yqVisI_of_gen hB hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := yqVisI_of_gen hB hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

/-- **The road with UPPER / LOWER / CapV at every Range restart** (`Xo.xoRoadAll` with the bridge `XoRealBL`). -/
theorem yqRoadAll
    (hUall : ∀ l, CdRange S l → CdUpper S l)
    (hLall : ∀ l, CdRange S l → CdLower S l)
    (hVall : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l)
    (hVhigh : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : XoRealBL S)
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
  obtain ⟨v0, vn⟩ := yqVis_all hB hUR hLR hVlow hVhigh h0 hn
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

/-- **`Xo.xoRoadH` with the bridge `XoRealBL`** (windows `υ_{λ+β} ≤ L(ω+1)` only). -/
theorem yqRoadH
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : XoRealBL S)
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
  refine yqRoadAll (fun l hr => ?_) (fun l hr => ?_) (fun l hr hu => ?_) (fun l hr hu => ?_) hT hF hB h0 hn
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

/-- **THE SUPPLY ROAD WITH THE SHIFT CLAUSE** (`yqRoadH` with the bridge from `XoShift S`). -/
theorem yqRoadS
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hSh : XoShift S)
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
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) :=
  yqRoadH hUH hLH hVH hVt hT hF (yqRealBL hSh) h0 hn

end Googology.Trans.PoR.InaccPsi.R2.Yq
