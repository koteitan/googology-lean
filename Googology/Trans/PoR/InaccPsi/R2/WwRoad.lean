import Googology.Trans.PoR.InaccPsi.R2.WwForm

/-!
# The road with the repaired supply

`Wf.wfRoad` is vacuous (`Ww.wwRoad_false`).  `wwRoad` has the conclusion of `Wf.wfRoad`; its supply hypotheses are
`WwVisGen` (repaired forms with `ϑ`-nodes of any level, `Ww.WwForm`) at `m*` and every `L(n+1)`, and the open bridge
`WwRealB` (the realizer `Wf.wfReal_gen` for the repaired forms: the image `ϑ^{υ_{μ+f(h)}}(Ω₁·M + img e)` of a
`ϑ`-node, needs [W07a] Def 6.2 / Lemma 6.3 at levels `M ≥ B₂`).

* `WwRealB` (statement), `wwRealB_of` (**on decompositions without `ϑ`-nodes the bridge is `Wf.wfReal_gen`**:
  `WwGen` with only old forms gives the realizer), `wwVisI_of_gen`, `wwVis_all`, `wwRoad`, `wwRoadZ` (the same with
  UPPER / LOWER / CapV asked only above the frontier `F_Z` of `Ws.wsRoadZ`).

No new axiom.  New definition: `WwRealB` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ww

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The realizer bridge for the repaired forms** (open): `WwGen` at `(λ, β)` gives the realizer up to `υ_{λ+β}`
(the hypotheses of `Wf.wfReal_gen`, with `WwGen` in place of `Wf.WfGen`). -/
def WwRealB (S : InaccSeq.{0}) : Prop :=
  ∀ l β : Ordinal.{0}, IsRestartIdx l → upsilon l < Om1 → upsilon l < nuC → upsilon (l + β) ≤ nuC →
    Cx.CxStdPairTop S → upsilon l ≤ Nc.ncL S (ω + 1) → WwGen S l β → Lr.LrReal S (upsilon l) (upsilon (l + β))

/-- **The bridge holds where the forms are old**: if every repaired form demanded by `WwGen` is an old one, the
realizer is `Wf.wfReal_gen` (so the bridge only asks the new `ϑ`-nodes). -/
theorem wwRealB_of {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hνβ : upsilon (l + β) ≤ nuC) (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1))
    (h : WwGen S l β)
    (hold : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨ Vr.VrForm S l β g) :
    Lr.LrReal S (upsilon l) (upsilon (l + β)) :=
  Wf.wfReal_gen hl hl1 hν hνβ h.1 hold (wwSup_wf h.2.2) hstd hlL

/-- **`WwVisGen` and the bridge give the visible statements `Tk.TkVisI`.** -/
theorem wwVisI_of_gen (hB : WwRealB S) (hL : CdLOWER S) {l b c : Ordinal.{0}} (hl : IsRestartIdx l)
    (hb : b ≤ nuC) (hbL : b ≤ Nc.ncL S (ω + 1)) (hstd : Cx.CxStdPairTop S) (h : WwVisGen S l b c) :
    Tk.TkVisI S (upsilon l) b c := by
  refine Tk.tkVisI_of_real hL hl rfl hb fun ν h1 h2 h3 h4 h5 h6 => ?_
  obtain ⟨β, hνβ, hβb, hG⟩ := h ν h1 h2 h3 h4 h5 h6
  have hν : upsilon l < nuC := (h4.trans h3).trans_le hb
  exact ⟨_, hνβ, hβb, hB l β hl (hν.trans_le nuC_le_Om1) hν (hβb.trans hb) hstd
    ((h4.trans h3).le.trans hbL) hG⟩

/-- The visible statements at `m*` and every `L(n+1)` from `WwVisGen` and the bridge. -/
theorem wwVis_all (hB : WwRealB S) (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      WwVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      WwVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
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
    have := wwVisI_of_gen hB hLW hl (h1.trans hν) h1 hstd (h0 l hl e)
    rwa [← e] at this
  · obtain ⟨l, hl, e⟩ := Pp.ppL_succ_restart (S := S) n
    have := wwVisI_of_gen hB hLW hl ((hlt (n + 1)).trans hν) (hlt (n + 1)) hstd (hn n l hl e)
    rwa [← e] at this

/-- **THE ROAD WITH THE REPAIRED SUPPLY** (conclusion of `Wf.wfRoad`): UPPER / LOWER / CapV above the frontier of
`Hl.hlU`, `WdThLow`, `WdEQfar` (under `L(ω+1) ≤ ν_C`), the bridge `WwRealB`, and `WwVisGen` at `m*` and every
`L(n+1)`. -/
theorem wwRoad
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : WwRealB S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      WwVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      WwVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
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
  obtain ⟨v0, vn⟩ := wwVis_all hB hUR hLR hVlow hVhigh h0 hn
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
theorem wwRoadZ
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdLower S l)
    (hVH : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Ws.wsVz.B * ω) ≤ l → CdCapV S l)
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (hB : WwRealB S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      WwVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      WwVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) := by
  have h := wwRoad (S := S) (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hu _ => ?_) (fun l hr hu _ => ?_)
    hT hF hB h0 hn
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

end Googology.Trans.PoR.InaccPsi.R2.Ww
