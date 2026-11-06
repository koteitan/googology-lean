import Googology.Trans.PoR.InaccPsi.R2.HoRoad
import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WhSucc
import Googology.Trans.PoR.InaccPsi.R2.WhRefute
import Googology.Trans.PoR.InaccPsi.R2.WjSplit
import Googology.Trans.PoR.InaccPsi.R2.WjVeb
import Googology.Trans.PoR.InaccPsi.R2.WmA1
import Googology.Trans.PoR.InaccPsi.R2.WnSucc
import Googology.Trans.PoR.InaccPsi.R2.WnLv3
import Googology.Trans.PoR.InaccPsi.R2.WoTop
import Googology.Trans.PoR.InaccPsi.R2.WpStep
import Googology.Trans.PoR.InaccPsi.R2.WsZeta
import Googology.Trans.PoR.InaccPsi.R2.WtTow
import Googology.Trans.PoR.InaccPsi.R2.WxTop
import Googology.Trans.PoR.InaccPsi.R2.WyLv
import Googology.Trans.PoR.InaccPsi.R2.XcQ
import Googology.Trans.PoR.InaccPsi.R2.XfFr
import Googology.Trans.PoR.InaccPsi.R2.XlW
import Googology.Trans.PoR.InaccPsi.R2.XhLev
import Googology.Trans.PoR.InaccPsi.R2.XkLay
import Googology.Trans.PoR.InaccPsi.R2.XpFr
import Googology.Trans.PoR.InaccPsi.R2.XuStart
import Googology.Trans.PoR.InaccPsi.R2.XxLay
import Googology.Trans.PoR.InaccPsi.R2.YcDirect
import Googology.Trans.PoR.InaccPsi.R2.YfWin
import Googology.Trans.PoR.InaccPsi.R2.YhRS
import Googology.Trans.PoR.InaccPsi.R2.YhDir
import Googology.Trans.PoR.InaccPsi.R2.YiWin
import Googology.Trans.PoR.InaccPsi.R2.YrDir
import Googology.Trans.PoR.InaccPsi.R2.YsRsAll
import Googology.Trans.PoR.InaccPsi.R2.YxVac
import Googology.Trans.PoR.InaccPsi.R2.ZcSup
import Googology.Trans.PoR.InaccPsi.R2.ZhFix
import Googology.Trans.PoR.InaccPsi.R2.ZnIn
import Googology.Trans.PoR.InaccPsi.R2.YwLad
import Googology.Trans.PoR.InaccPsi.R2.ZbE0
import Googology.Trans.PoR.InaccPsi.R2.ZgSq
import Googology.Trans.PoR.InaccPsi.R2.ZmCd
import Googology.Trans.PoR.InaccPsi.R2.ZoBC
import Googology.Trans.PoR.InaccPsi.R2.ZrBase
import Googology.Trans.PoR.InaccPsi.R2.ZrRead
import Googology.Trans.PoR.InaccPsi.R2.ZsCap
import Googology.Trans.PoR.InaccPsi.R2.ZtIso

/-!
# SkF: skeleton (map) of the part "frontier" of `Wd.wdRoadL`

The four hypotheses `hUH`, `hLH`, `hVH`, `hVt` of `Wd.wdRoadL` (UPPER / LOWER / CapV at range restarts
`λ ≥ ι(Γ(φ(Ω₁·Ω₁, G+1))·ω)`).  `Ho.hoWaRoad_hyp_iff` moves them to `λ ≥ F_Ho = ι(Γ(φ(Ω₁³, G+1))·ω)`.

Which restarts are needed: every `λ` with `CdRange S λ`, i.e. `B₀ ≤ λ`, `υ_λ < L(ω+1)`, code `m_λ < P′`
(by `Te.teCode_hi_iff` these are ALL restarts in `[B₀, L(ω+1))` except the `L(k)` and `L(ω)`).  They fall in three
regions:
* (A) `λ < ι(Γ(B)·ω)` for some code `B < Γ(1)` (`Hg.HgVD` systems; levels `ℓ` of `φ(ℓ, G+1)`, `ℓ < Γ(1)`);
* (B) past every such frontier, name exponent `e(η_λ) < Ω₂` (atoms `Γ(c)`, `c ≥ 1`, inside codes, up to `ι(Ω₂)`);
* (C) `e(η_λ) ≥ Ω₂` (`Gc.gc_past_Om2`: `ι(Ω₂) ≤ λ`, `m_λ = π_η`), up to `L(ω+1)` — the long region.
Region (A) splits by the level `ℓ`: (A1) `ℓ < ε_{Ω₁+1}` (Cantor normal form in `Ω₁`-powers, read `Ω₁ ↦ x` by
`Gf.rdc`, gate `Gf.gtc`), (A2) Veblen-form levels `ε_{Ω₁+1} ≤ ℓ < G`, (A3) levels containing `G`.
(A1) is ONE generic induction over `ℓ` (`skFam`, by well-founded recursion from `skStep`).

Skeleton only: the OPEN nodes are `sorry`.  No axiom.

Round 116 (leaf gam41, modules `R2.Wh*`; the PROVED nodes below can be checked only after the merge, since they use
the new modules): `skShape`, `skDigitGate`, `skLvOfGate`, `skStepBase`, `skCofLev` PROVED.  Two statement
corrections: (1) the shapes `ShPow`, `ShExpLim`, `ShCoefLim` had `e : ℕ` (untyped `e` in `Om1 ^ e` elaborates to
`Monoid.npow`); with `e : ℕ` the shape leaf is FALSE (`skShapeNat_false`, witness `Ω₁^ω`); they now ask
`e : Ordinal`.  (2) The entry predicate `SkAt` carries no invariant tying the system to the package (no start
condition over `G`, no gate bound), so the steps would have to extend ARBITRARY digit systems; the induction now runs
on `SkAtW` (= `Wh.WhAt`: `SkAt` + gate `≤ gtc ℓ`, every `ε`-number above the gate is above `gtc ℓ`, the system is a
start over `G` at the package).  On it `skStepBaseW` and `skStepSuccW` are PROVED; `skStepPowW`, `skStepExpLimW`,
`skStepCoefLimW` are OPEN.  The original `skStep*` leaves are REPLACED (kept, not used).

Round 116 (leaf reg1, modules `R2.Wj*`): the nodes of (A2), (A3), (B) and (C) below come from leaf reg1.
Region (C) lies entirely below `L(0)` (`skLongMid`, `skLongTop` vacuous); old (B) is re-split by the windows
`[L(k), L(k+1))` (`Wj.wjRegB_iff`, `skSplit`); the A2/A3 cut moves to `φ(G, 1)` (`Wj.wjA2Cof`, `Wj.wjA3Cof`).
The A2 nodes use reg1's `SkAtG` (`↔ SkAt` below `ε_{Ω₁+1}`), not gam41's stronger `SkAtW`.

Round 117 (leaf gam42, modules `R2.Wm*`; the PROVED nodes below can be checked only after the merge, since they use
the new modules): the coherence `SkCohW` relates packages by `Hn.HnkExt`, which is vacuous across a gate drop
(`skOldVacuous`; a drop exists: `Ω₁·ω < Ω₁²`, `gtc(Ω₁²) = 2 < ω = gtc(Ω₁·ω)`), so a limit entry could not be shown to
extend every member.  The induction now runs on the CORRECTED coherence `SkCohW2` (= `Wm.WmCoh`), whose package
relation `Wm.WmExt` lowers by the pseudo-base gate (`Wm.wmLowr`: only `g' ≤ Q.γ`); `SkCohW2 ⇒ SkCohW`
(`skCohW2_old`).  On it: base, successor, EVERY level with an `ω`-sequence (`Wm.WmFs`: all coefficient limits, and
the exponent limits whose exponent has an `ω`-sequence) are PROVED; the one remaining leaf is `skStepOm1W2` (the levels
of cofinality `Ω₁`).  The family on all levels below `Ω₁²` is proved with no hypothesis (`skFamSq`).  The old
`skStepPowW`, `skStepExpLimW`, `skStepCoefLimW`, `skStep` are REPLACED; `skFam` keeps its statement and is REDUCED to
`skStepOm1W2`.  The frontier does not move yet.

Round 117 (leaf reg2, modules `R2.Wn*`; the PROVED nodes below can be checked only after the merge):
`skShapeG`, `skLvOfGateG`, `skGateBn` PROVED.  `SkAtG` has the defect gam41 found in `SkAt` (no start condition
of the system over `G` at the package), and `Wh.WhAt` cannot be used past `ε_{Ω₁+1}` (its base `Wh.whGW` asks
`ℓ(x) + x < ε_{x+1}`, false for every level `ℓ ≥ ε_{Ω₁+1}`); the (A2) induction now runs on `SkAtWG` (= `Wn.WnAt`:
`glR`/`glG`, and the base `Wn.wnGW` whose outer low field `hdNx (Γ_{x+1}+1) (Γ_{x+1})` needs no bound on the
level).  On it `skStepBaseWG` and `skStepSuccWG` are PROVED; `skStepPowWG`, `skStepCoefLimWG`, `skStepExpLimWG`
are OPEN; the `SkAtG` steps are REPLACED (kept, not used).
(A3): `Hn.HnLv` cannot carry an (A3) level and `G` is not in `range φ(L, ·)` for `L > G` (`skA3NoBand`,
`skA3NoGBase`); the (A3) datum is `Wn.WnLv3` (non-vacuity `skA3Datum0` at `t₀`), the package `Wn.WnPk3`, and the
ladder invariant is `SkPk3W` (= `Wn.WnEnt3`: package at `t_n` + pseudo-base `φ(t_n, G)`); the SUSPECT of
`skSysA3Step` is CONFIRMED (its invariant carries no level datum) and the node is REPLACED by `skSysA3StepW`.

Round 118 (leaf gam43, modules `R2.Wo*`; the PROVED nodes below can be checked only after the merge, since they use
the new modules): REGION A1 IS CLOSED.  An entry is now a FAMILY OF SYSTEMS OVER ALL RAW BASE DATA
(`Wo.WoSpec`: point, reading, code gate, low field; every datum good up to the level, pseudo-bases and `G` alike), so
two entries extend each other over every datum with no gate condition and the gate drop is no obstacle.  ONE generic
induction (`Wo.woStep_all`): base, successor (`Hn.hnwU` over the two-gate base `Wo.woWB`), `ω`-limits (`Wm.WmFs`,
chain union), and the levels of cofinality `Ω₁` (`Wo.wo_fs1`: an `Ω₁`-sequence of levels; `Wo.woStep_om1`:
`Ho.hoOU` with SMALL from the region gates).  The family gives `Wh.WhAt` entries that extend each other in the
corrected sense (`Wo.woFamW2`), so `skFam`, `skSysAll`, `skSysA1` are PROVED with their statements unchanged; the
leaf `skStepOm1W2` (`Wm.WmOm1Step`: arbitrary coherent families) is REPLACED (not proved, not needed).  The system at
`φ(ε_{Ω₁+1}, G+1)` exists (`Wo.woVE`, gate 1), so the frontier moves to `skFE = ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`
(`skLocE`, `skHypIffE`; road `Wo.woRoad`, `Wo.woRoad_hyp_iff`).

Round 118 (leaf reg3, modules `R2.Wp*`; the PROVED nodes below can be checked only after the merge): the (A2)
coherence `SkCohWG` relates packages by the old `Hn.HnkExt` (via `SkExt`), vacuous across a gate drop, and gate drops
occur between (A2) levels (`skGateDropG`); the old leaves `skStepPowWG`, `skStepCoefLimWG`, `skStepExpLimWG` are
REPLACED (with `skStepWG`, `skFamWG`).  The (A2) induction now runs on the CORRECTED coherence `SkCohWG2`
(= `Wp.WpCoh`: entries `Wn.WnAt`, relation `Wm.WmExtE`), `SkCohWG2 ⇒ SkCohWG` (`skCohWG2_old`).  On it base,
successor, every level with a gated `ω`-sequence (`Wp.WpFs`), every coefficient limit (UNCONDITIONAL, by the gate
lemma `Wp.wp_glG_coef`) and every cofinal level `glBn n` are PROVED; (A2) is REDUCED to the one leaf `skStepOm1WG2`
(`Wp.WpOm1Step G`, the levels with no gated `ω`-sequence); `skSysAllG` keeps its statement.  Non-vacuity:
`skFamSqG` (the corrected family on `[Ω₁, Ω₁²)`, no hypothesis).

Round 119 (leaf gam44, modules `R2.Ws*`; the new nodes below import `R2.WsTop`, so they can be checked only after the
merge): the family over raw data of `R2.Wo` is now written ONCE for a CODE INTERFACE `Ws.WsC` (bound, reading, gate,
low field and their facts); the `Ω₁`-cofinal step is generic (`skStepOm1Ws`); the (A1) instance `Ws.wsA1` reproves
`Wo.woStep_om1` and `Wo.woSysA1` (`skA1Check`, `skA1SysCheck`); the (A2) instance `Ws.wsA2` uses the gate
`Ws.gh = max 1 glG`.  REFUTE FIRST: `ε_{Ω₁+1}` lies in the remaining case of `Wp.WpOm1Step G` and has neither a
`Wp.WpFs` sequence nor an `Ω₁`-sequence (`skGlGNoFsE`), so no classification with the gate `glG` exists; with `gh`
the towers `Ω₁^{…}` serve.  ONE induction on the base-`e` normal form (`Ws.ws_br`) reduces the whole (A2)
classification to the `ε`-number codes (`skBaseA2`), proved for every code of Veblen level 1, i.e. up to
`ζ_{Ω₁+1}` (`skBaseZ`, from the classification of the index); OPEN: the Veblen nodes `e ∈ (ζ_{Ω₁+1}, G)`
(`skBaseA2Hi`).  `skStepOm1WG2` (arbitrary coherent families) is REPLACED (not proved, not needed), with
`skStepWG2`, `skFamWG2`, and `skSysAllG` (gate `≤ glG ℓ`; replaced by `skSysAllG2`, gate `≤ gh ℓ`, only `< K` is used).
The frontier moves to `skFW = ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)` (`skSysWV`, `skLocW`, `skHypIffW`; road `Ws.wsRoad`) and then
to `skFZ = ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)` (`skSysZV`, `skLocZ`, `skHypIffZ`; road `Ws.wsRoadZ`).

Round 119 (leaf reg4, modules `R2.Wt*`; the PROVED nodes below can be checked only after the merge): the (A3) level
data below `t₀`.  Every (A3) level `G < L < t₀`, `Ω₁ ∣ L` has a `Wn.WnLv3` (`skA3DatumAll`: codes of the hereditary
step `Go.goGl.step`, reading `G ↦ Γ_{x+1}`, gate from `Go.GoD.code_gate` via `Wt.wt_cl_head`); the towers
`G^{⋯^G}` give the `ω`-sequence of (A3) level data of gate `0` below `Wn.wnLv3T0` with readings `+x`-increasing and
cofinal (`skA3Tow`); a step at an (A3) level contains the steps of every lower level at the same pseudo-base, (A1)
and (A2) included (`skA3StepLow`), so `skSysA3Lev0W` needs (A2) closed (done in round 120, `skClsA2`).  Route: neither a copy of
the `Hn` package stack nor the `Wo` family can be written for `Wn.WnLv3` without copying the `Hn` stack, because the
pseudo-base / package / successor / limit machinery (`Hn.HnVQ` … `Hn.HnWP`, `Wm.WmPkL`, `Wm.WmExt`, `Ho.hoOU`) is
typed by `Hn.HnLv`, whose fields `L < G`, `ℓ(x) < Γ_{x+1}` exclude every (A3) level; the stack itself uses neither
field (only `Ω₁ ≤ L` and `ℓ(x) + ν < Γ_{x+2}`).  Shortest road: WIDEN `Hn.HnLv` to `L < Γ(1)`, `ℓ(x) < Γ_{x+2}`
(a repo refactor), then every `Wn.WnLv3` is an `Hn.HnLv` and the `Wo` family form applies over (A3) raw data.

Round 120 (leaf gam45, modules `R2.Wx*`; the nodes below that use `Wx.*` import `R2.WxTop`, so they can be checked
only after the merge): REGION (A2) IS CLOSED WITH NO HYPOTHESIS.  `skBaseA2Hi` is PROVED (`Wx.wx_baseA2Hi`) by ONE
proof generic in the Veblen level `α` of `e = glPsi α η = φ(α, Λ_α(η))`: a limit argument (`η` a limit, `¬ glFw α η`)
takes the sequence of `η` (continuity `Wx.wx_psi_cont`, gate-cofinality by the recursion `Wx.wx_rec` through the
bracket of `b`, comparing `α_b` with `α`); a successor or zero argument has a predecessor `f` (`Wx.wx_pkg`) and
takes the towers over `f` (`α = 1`), the iterates of `φ(α', ·)` over `f + 1` (`α = α'+1 ≥ 2`), or `φ(α_k, f+1)` /
`φ(s μ, f+1)` from the sequence of `α` (`α` a limit).  REFUTE FIRST at the first codes past level 1,
`φ(1, ζ_{Ω₁+1}+1)` and `φ(2, Ω₁+2)`: no evidence, both proved (`skRefuteA2Hi`).  Hence `skBaseA2`, `skClsA2`,
`skSysAllG2`, `skSysA2Lev` are PROVED, and the frontier moves to the END OF (A2): `WxPast S λ` (`ι(Γ(B)·ω) ≤ λ` for
every `B < φ(G, 1)`; `F_{A2} = sup_n ι(Γ(φ(glBn n, G+1))·ω) ≤ ι(Γ(φ(G, 1)))`; `skSysA2V`, `skLocA2`, `skHypIffA2`;
road `Wx.wxRoadA2`).  (A3) (`skSysA3Lev0W`, `skSysA3StepW`) no longer waits for (A2).

Round 120 (leaf reg5, module `R2.WyLv`; repo DEFINITIONS CHANGED: `Hn.HnLv` widened to `L < Γ(1)`,
`ℓ(x) < Γ_{x+2}`, the old bounds are the predicate `Hn.HnLvG`; `Hn.HnNB`, `Wh.WhNB` also ask `L < G`; `Wn.wnGW`
asks `Wn.WnNB` and `Wn.WnAt` carries it; `Ws.WsC` asks `Bd < Γ(1)`, `R < Γ_{x+2}`, the facts of `G` as a base are
`Ws.WsCG`).  `skA3NoBand` is restated with `Hn.HnLvG` (its old first half is REFUTED: `skA3NoBandOld`).  Every
(A3) datum is a band datum (`skA3Band`), (A3) pseudo-bases / specifications / packages are those of the `Hn` stack,
the target `Wn.WnEnt3 S 0` is equivalent to its `Hn` form (`skA3EntHn`), and `skSysA3Lev0W` is REDUCED to the
packages at the tower levels `G^{⋯^G}` extending each other (`skA3TowPk`, the `Ws` family over (A3) raw data; (A2)
enters only there, through `skBaseA2Hi`) and the pseudo-base `φ(t₀, G)` with a start (`skA3QT0`); the `ω`-limit at
`t₀` is `Wy.wySeqT0` / `Wy.wyPkT0` (`Wm.wmPkL` along `Wt.wtTowSeq`).

Round 121 (leaf reg6, modules `R2.Xc*`; the PROVED nodes below can be checked only after the merge): the (A3) code
interface `Xc.xcA3 : Ws.WsC` (bound `t₀`, reading `Wt.wtD.R`, gate `max 1 wtD.g`), its classification
`Ws.WsCls Xc.xcA3 t₀` with NO hypothesis (`skA3Cls`: one induction on `G^j·d + r`, the one base `G` has an
`ω`-sequence of gate-`0` (A2) codes, below `G` the (A2) classification), the family at every (A3) level below `t₀`,
the tower packages extending each other (`skA3TowPk1`, gate `1`; it REPLACES `skA3TowPk`, whose gate-`0` data are not
the data of any `Ws` family, `Xc.xc_lv_ne`), and the (A3) package at `t₀` on a gate-`1` datum (`skA3PkT0`).  A
pseudo-base over `Wn.wnLv3T0` raised to the gate `max 1 γ` is started by the same systems (`Xc.xc_start_raise`), so
`skSysA3Lev0W` needs ONLY `skA3QT0` (`Xc.xcEnt3_of`).  The pseudo-base `φ(t₀, G)` itself is built (`skA3T0Q`, reading
`ϑˣ(Ω₁·ε_{Γ_{x+1}+1} + Γ_{x+1})`), so `skA3QT0` is REDUCED to its start `skA3T0Start`, a system with bound
`φ(t₀, G)` (`Xc.xc_start_iff`, `Xc.xc_start_B`); it lies above `φ(ℓ, G+1)` for every `ℓ < t₀`
(`Xc.xc_start_cover`), so it is the whole of region (A3) below `φ(t₀, G)` (all (A3) levels, all offsets).

Round 122 (leaf reg7, modules `R2.Xf*`; the PROVED nodes below can be checked only after the merge): THE FIRST (A3)
LEVEL `G` FROM THE BOTTOM.  `φ(G, 0) = G`, so the offsets of the level `G` start at `0`, not at a base `F + 1`
(`Hn.HnVRec`), and the family `Ws.wsF` does not apply at the level `G` over the datum `G` (`Ws.WsGood` asks
`R G x < Γ_{x+1}`).  The system at `φ(G, 1)` is the gated `ω`-chain union of the (A2) systems over `G` at the
`ω`-sequence of gate-`0` (A2) levels cofinal in `G` (`skA3G1`, `Xf.xfV1`); it starts the pseudo-base `φ(G, 1)` of the
level `G`.  One recursion (`Xf.xfV`: the package of the (A3) family at `G` at successors, gated `ω`-chain unions at
limits) gives a start of `φ(G, ν)` for every constant offset `1 ≤ ν < Γ₀` (gate `ν`; `skA3GOff`), the reading
`ϑˣ(Ω₁·Γ_{x+1} + t) = φ(Γ_{x+1}, 1+t)` (`Xf.xf_glA_veb`) giving Lemma EXACT.  Every `B < φ(G, Γ₀)` lies below the
bound of a system with gate `< K` (`skSysA3G`, used in `skSysA2`), and the frontier moves past `φ(G, 1)` to
`F_G = sup_{ν<Γ₀} ι(Γ(φ(G, ν))·ω) ≤ ι(Γ(φ(G, Γ₀)))` (`skPastG`, `skLocG`, `skFGWhere`, `skHypIffG`; road
`Xf.xfRoad`, `Xf.xfRoadZ`, hypotheses equivalent to those of `Xb.xbRoadZ`: `Xf.xfRoad_hyp_iff`).  `skA3T0Start`
stays OPEN: next are the offsets of `G` read by codes (gates `≥ Γ₀`, `Ω₁`-cofinal unions) up to `φ(G+1, 0)`, then
the levels above `G`.

Round 123 (leaf reg8, modules `R2.Xl*`; the PROVED nodes below can be checked only after the merge): THE LEVEL `G`
IS COMPLETE.  The offsets of `G` start at `0` (`φ(G, 0) = G`), so `Hn.HnVRec` (offsets `F + 1 + λ` over a fixed
point `F`) is ported with the base `0` (`Xl.XlBot`, `Xl.XlLv`, `Xl.XlRec`, `Xl.XlTop`): the stage at the offset `λ`
is `φ(G, 1 + λ)`, read `ϑˣ(Ω₁·Γ_{x+1} + λ(x)) = φ(Γ_{x+1}, 1 + λ(x))` (`Xl.xl_glA`, every `λ(x) < φ(Γ_{x+1}+1, 0)`),
EVERY OFFSET IS READ BY THE SYSTEM BUILT SO FAR, and its gate is `max(1, g(λ))` with `g(λ)` the code gate of `λ` in
that system (`Xl.xlV_γ_iff`; no bound by `Γ₀`: a code over `Z` in `[φ(G, 1+λ), φ(G, 2+λ))` forces `g(λ) < Z`,
`Xl.xl_gate`; stages with `g(λ) ≥ K` are not located, but they need not be).  One recursion over every `λ < φ(G+1, 0)`
(successor: the package `Xf.xfPk`; limit: the union along all earlier stages, any cofinality) and the tower union give
the system at `φ(G+1, 0)` with gate `1` (`skA3GTop`, `Xl.xlTop`), extending `Xf.xfV1` and `Hg.hgU`.  The frontier moves
from `F_G` to `ι(Γ(φ(G+1, 0))·ω)` (`skPastGT`, `skLocGT`, `skFGTWhere`, `skHypIffGT`; road `Xl.xlRoad`, its four
hypotheses equivalent to those of `Xf.xfRoad`: `Xl.xlRoad_hyp_iff`).  `skSysA2` is now PROVED (its range ends below
`φ(G, G+1) < φ(G+1, 0)`, `Xl.xl_GG1_lt`).  `skA3T0Start` stays OPEN: next is the level step `G+κ → G+κ+1` (the same
bottom recursion at the level `G + κ`, whose offsets start at `φ(G+κ, 0)`), the unions at limit `κ`, the levels
`L + κ` of the (A3) code interface, and the level `t₀` up to the offset `G`.
The same round goes on (modules `Xl.XlK`, `Xl.XlKRec`, `Xl.XlKFr`, `Xl.XlW`): the bottom recursion is generic in the
level datum (`Xl.XlB`: shift `e = 1` at the strongly critical level `G`, `e = 0` at `G + κ`, `κ ≥ 1`, where the
offsets start at `φ(G+κ, 0)` itself); ONE recursion on the constant level `κ < Ω₁` (`Xl.xlK`: successor = the bottom
recursion of `G + κ + 1` with the step `Hn.hnVLS xfPk.St0 (κ+1)`, started at the top of `G + κ`; limit = the gated
`ω`-chain union, gate `λ`, then the bottom recursion of `G + λ`) gives the top of every level `G + κ` (`skA3GK`), and
the `Ω₁`-union of all of them (`Ho.hoOU`, SMALL from `Xl.xlT_high`) the system at `φ(G + Ω₁, 0)` with gate `1`
(`skA3GW`).  The frontier moves to `ι(Γ(φ(G + Ω₁, 0))·ω)` (`skPastGW`, `skLocGW`, `skFGWWhere`, `skHypIffGW`; road
`Xl.xlwRoad`, hypotheses equivalent to those of `Xl.xlkRoad` / `Xl.xlRoad` / `Xf.xfRoad`).

Round 122 (leaf regb1, modules `R2.Xh*`; the nodes below that use `Xh.*` import `R2.XhLev`, so they can be checked
only after the merge): REGION (B) IS DECOMPOSED INTO CELLS (base, offset type).  Every region-(B) name is a base
`β ∈ {0} ∪ {Ω₂·q} ∪ {b_k} ∪ {b_ω}` plus an offset `ζ < Ω₂` with `e(η) = e(ζ)` and code `-1 + e(ζ)` (`skBhiName`,
`skWinOff`); every offset is of type (A) or in a name layer `c ≥ 1` (`Xh.xhNm_split`).  (B-lo) = base `0`: its
LAYERS `c` (`Xh.XhLay`: past every `ι(Γ(B)·ω)`, `B < Γ(c)`, not past every one with `B < Γ(c+1)`; `skLayExists`)
are region (A) again over the base `Γ(c)`: `skLayLevCof` (levels `ℓ < Γ(c)` reach exactly `φ(Γ(c), 1)`, generic in
`c`) splits each layer into `skLayLo` (old levels over the base `Γ(c)`) and `skLayHi` (levels with the atom `Γ(c)`);
the base atom is EXACT (`skLayExact` = `Gb.gq_pi`); the first missing ingredient is IMG below `Γ_{ρ+3}`
(`skL1Img`).  (B-hi) is REDUCED to the cells `skBhiA` / `skBhiL`, `skWinB` to `skWinL`, `skTopB` to `skTopL`.
Non-vacuity: `skBhiNonempty`, `skWinNonempty`.  The closed region (A2) bounds `ν_C` from below (`skNuA2`).

Round 123 (leaf regb2, modules `R2.Xk*`; the nodes below that use `Xk.*` import `R2.XkLay`, so they can be checked
only after the merge): `skL1Img` PROVED (`Xk.xkL1Img`): Lemma IMG past a base atom is proved directly (no level
induction, `Xk.xkImg_step`), so Lemma IMG holds below `gq c ρ = Γ_{ρ+1+c}` for every constant `1 ≤ c < ε₀`
(`skLayImgCst`); the base atoms `gq c x` are the strongly critical numbers below `gq (c+1) x` (`skLayBaseSC`).  The
interfaces take the base atom index `k` (`Xk.XkVD k`, `Xk.XkC k`, `Xk.XkCG`, `Xk.XkRS k`; instance `k = 0` = the old
`Hg.HgVD`, `Ws.WsC`, `Ws.WsCG`, `Gs.GsRS`: `skLayIface`).  `skLayLo` is REDUCED (`Xk.xkLayLo_of`) to `skLaySys` (the
systems over `Γ(k)`) and `skLayFront` (the frontier lemma over `Γ(k)`) for the indices `k + 1 < ε₀`, and
`skLayLoBig` for the rest; both are theorems at `k = 0` (`skLaySys0`, `skLayFront0`).  `skLayFront k` (`k ≥ 1`)
contains all of region (A) (the open `skA3T0Start` included): the layers come after (A3).

Round 124 (leaf reg9, modules `R2.Xp*`; the nodes below that use `Xp.*` import `R2.XpFr`, so they can be checked
only after the merge): REGION (A3) BELOW `φ(t₀, G+1)` IS CLOSED.  The band step is generic (`Xp.XpBd`: a package
whose level `L > G` has a reading below `ε_{Γ_{x+1}+1}` that is not strongly critical; `Xp.xpBK`, `Xp.XpAt`,
`Xp.xpK` (the bottoms `φ(L + κ, 0)`, ONE recursion on `κ < Ω₁`), `Xp.xpW` (the `Ω₁`-union `φ(L + Ω₁, 0)`):
`skA3BandStep`).  ONE well-founded recursion along the (A3) code interface `Xc.xcA3` over every band level
`G < ℓ < t₀` (`Ω₁ ∣ ℓ`; `G + Ω₁` from `Xl.xlW`, successors by the band step, limits by `ω`-chains or `Ω₁`-unions
from `Xc.xc_br`, SMALL carried in level form) gives the system at every bottom `φ(ℓ, 0)` (`skA3Bands`); the tower
union gives `φ(t₀, 0)` with gate `1` (`skA3T0Bot`); the bottom recursion of the level `t₀` (step of `Xc.xcPkT0`)
reaches the offset `G` (`skA3T0G`), and `skSysA3Lev0W` (`Wn.WnEnt3 S 0`) is PROVED directly (`Xp.xpEnt3`), with the
pseudo-base `φ(t₀, G)` over `Xc.xcLvT0` (gate `1`), not through `skA3QT0` / `skA3T0Start` (which ask the gate-`0`
pseudo-base `Xc.xcQT0` and the reading `Γ_{x+1}` of the code `G`; both stay OPEN, OFF THE ROAD).  The frontier moves
to `ι(Γ(φ(t₀, G+1))·ω)` (`skPastT0`, `skLocT0`, `skFT0Where`, `skHypIffT0`; `Xp.xpT0Hyp_iff`: the hypotheses past it
are equivalent to those of `Xl.xlwRoadZ`; the road `Xp.xpT0RoadZ` is VACUOUS, `Xp.xpT0Road_vac`, like `Xb.xbRoad`).
Next: `skSysA3StepW` (an (A3) code interface for the levels in `(t_n, t_{n+1})`, `t_{n+1} = φ(t_n, 0)`).

Round 125 (leaf reg10, modules `R2.Xu*`; the new nodes import `R2.XuStart`, so they are checkable only after the
merge): REGION (A3) IS CLOSED (every `B < Γ(1)`).  THE (A3) CODE INTERFACE UP TO `Γ(1)`, written once: every code
`c < Γ(1)` is read (`Xu.xuR`, gate `Xu.xuG`): below `t₀` as `Wt.wtD`, above `t₀` in the bracket of
`e = guE c = xuPsi α η` as `ϑˣ(Ω₁·α(x) + η(x))^{j(x)}·d(x) + r(x)` (`Xu.xuPsi` shifts the count at the strongly
critical level `G`, where `glPsi G 0 = G`).  Monotonicity, cofinality, Lemma EXACT, gates, hull membership and the
code gate by one induction each (`Xu.xu_mono_top`, `Xu.xuR_cof`, `Xu.xu_pi`, `Xu.xu_code_gate`, `Xu.xu_mem`); the
interface `Xu.xuC B` for EVERY `ε`-number bound `t₀ ≤ B < Γ(1)` (`skA3CodeAll`) with the classification
`WsCls (xuC B) B` (`Xu.xuCls`, `skA3ClsAll`), so the `Ws` family has a package at every (A3) level, in particular
at every `t_n` (`skA3PkAll`, gate `1`).  The band recursion of `Xp` made generic in the bound `T` (`Xu.XuqBd`, low
field `Xu.xuqZ T`, `Xu.xuqBandStep`, `Xu.xuqStep_all`; `skA3BandsAll`) with `T = t_{n+1}` gives the bottom
`φ(t_n, 0)` and, by the bottom recursion of `t_n`, the pseudo-base `φ(t_n, G)` with a start (`skA3QStart`), so
`Wn.WnEnt3 S n` holds for every `n` (`Xu.xuEnt3`) and `skSysA3StepW` is PROVED.  (A3) ends exactly at
`Γ(1) = sup_n t_n`, the least strongly critical ordinal above `G` (`skA3End`).

Round 125 (leaf regb3, modules `R2.Xx*`; the nodes below that use `Xx.*` import `R2.XxLay`, so they can be checked
only after the merge): `skLayFront` PROVED (`Xx.xxLayFront`, every `k + 1 < ε₀`; `k = 0` reproves `skLayFront0`,
`Xx.xxLayFront_zero`).  The frontier stack needed exactly: `Gm.GmGq` (the offset facts, now for every bound
`ϑˣ(Ω₁·Ω₁ + W)`, `W < ε₀`: `Xx.XxGq`), `Gm.GmU` (the union layer: `Xx.XxU`), `Gs.gsmU_codes` and `Gs.GsqRS` (the
layer of every code and the uniformity theorem: `Xx.XxRS`), `Gs.GsLoc` (`Xx.XxLoc`); the generic frontier lemma
`Gs.gsB1_eq`, `Gs.gsUniTh`, `Gq.gqLayP`, `Gh.ghEB` are used as they are (stated for every `Gs.GsCS`).  The hereditary
step `Hg.HgVD.step` (`Hg.HgVHC` … `Hg.HgVStep`) is NOT needed: the codes `B + n` (reading `b(x) + n`, gate `γ`) put
`B` into a reading system (`Xx.xxVRS`, `skLayLocVD`).  `skLayLo` (`c + 1 < ε₀`) now needs only `skLaySys`
(`Xx.xxLayLo_of_sys`).  `skLaySys` stays OPEN: every system over `Γ(k)` locates everything below `ι(Γ(Γ(k))·ω)`
(`skLaySysBase`, `Xx.xxLaySys_base`), so `skLaySys 1` contains the location of all of region (A), the (A3) part above
`t₀` (`skSysA3StepW`) included; and it needs the system recursion over `Γ(k)` (`Ws.wsSysAll` with `Ws.wsFam`,
`Wo.woStep_om1`, `Wm.wmStep_fs`, `Wh.whSucc_at`, the base system `Hg.hgU` and the systems `φ(α, G+1)`, `α < Ω₁`, of
`Gn` … `Hf`, the bands `Hn` / `Ho`: about 126k lines in 402 modules hard-wired to `G`).
Round 126 (leaf regb4, modules `R2.Yc*`; the nodes below that use `Yc.*` import `R2.YcDirect`, so they can be checked
only after the merge): `skLaySys` IS REFUTED (`skLaySys_false`, `Yc.ycLaySys_false_eps`): `Xk.XkVD k` is EMPTY for
`1 ≤ k ≤ G` (`skLayEmpty`, `Yc.ycVD_empty`): its hull fields `ix_mem`, `mem` (copied from `Hg.HgVD`) ask membership
in every `Cl(a, b)` with `0 < a`, but `Cl(1, b) ∩ Ω₂ ⊆ ψ_{Ω₂}(1) = Γ(1)` (`Yc.ycCl1_lt`) while the index of the bound
is `≥ Γ(k)`.  So `skLayFront` (`Xx.xxLayFront`), `skLaySysBase`, `skLayLocVD` are VACUOUS for `k ≥ 1`.  The repair
asks `k < a` in the three hull fields (`Yc.YcVD k`, `Yc.YcC k`; at `k = 0` the old interfaces, `rfl` round trips); the
frontier lemma over `Γ(k)` holds for the repaired systems (`skLayFrontY`, `Yc.ycLayFront`, every `k + 1 < ε₀`, the
construction of `Xx.xxVRS` with the two hull spots re-proved), and `skLayLo` is re-REDUCED to the repaired
`skLaySysY` (`Yc.ycLayLo_of`).  ROUTES (`skLayNoTransfer`): (a) the generic family is no instance — its output
`Hg.HgVD` and every raw datum it accepts lie below `Γ(1)` (`Yc.ycHg_noLay`, `Yc.ycGood_F_lt`); (b) no relabelling of
codes keeping the codes below `G` and sending `G ↦ Γ(k)` reaches the codes `[G, Γ(k))` or the mixed code `Γ(k) + G`,
which every system over `Γ(k)` has (`Yc.ycRelab_gap`, `Yc.ycRelab_mixed`, `Yc.ycVD_codes`).  What (a) needs from
`Γ(k)` is proved: the raw datum `Γ(k)` with every field of `Ws.WsGood` (`skLayGood`, `Yc.ycGood_base`; the hull fields
for `k < a`), the outer low field `Yc.ycZo k`, and at `k = 1` the level side (every `Ws.WsC` is a `Yc.YcC 1`, the (A3)
interfaces cover every level `< Γ(1)`: `skLayLevAll1`, `Yc.ycLevAll1`), so `skLaySysY 1` ⇐ `skLaySysAll1`
(`Yc.YcSysAll 1`: the family statement over `Γ(1)`, whose instance `k = 0` IS `Ws.wsSysAll`, `skLaySysAll0`).  (c) A
THIRD ROUTE skips the systems: direct readings of the layer (`Yc.YcDirect S c Γ(c+1)`: reading systems `Xx.XxRS c`
cofinal below `Γ(c+1)`) give `skLayLo` AND `skLayHi` at once (`skLayLoD`, `Yc.ycLay_of_direct`); non-vacuity at
`c = 0` below `φ(G, 1)` (`skLayDirectA2`); `skLayHi` is REDUCED to `skLayDirect` (`c + 1 < ε₀`) and `skLayHiBig`.

Round 133 (leaf regb11, modules `R2.Zm*`; this file imports `R2.ZmCd`, so it can be checked only after the merge):
THE GENERIC HEREDITARY STEP PAST `B_Γ`.  A digit system `Zm.ZmDS` at an `ε`-number base `E = φ(1, E_i) ≥ B_Γ`
(offsets `o < E`, reading `R(o)(x) < V(x)`, gates, order, successor, limits, cofinality, Lemma EXACT, the digit lemma,
`TlCl Z o ⇔ gate < Z`, `ε_{V(x)+1} = ϑˣ(Ω₁ + W(x))`) gives a reading system `Zb.ZbRS` of the indices `B_Γ + 1 + o`
and `ZbDirect S E` (`Zm.ZmDS.toRS`, `Zm.ZmDS.direct`); the `Yr` codes below `B_Γ` are one (`Zm.zmYr`, `V = D`).
ONE generic step `Zm.ZmDS.step`: the codes `E^k·d + r < ε_{E+1}` (`k = log_E o < o`, `Zm.zm_log_lt`) read
`V^{R(k)}·R(d) + R(r)`, gate `max`; order and top bound (`Zm.ZmDS.sR_main`), successors and limits
(`Zm.ZmDS.sR_succ`, `Zm.ZmDS.sR_lim`), cofinality (`Zm.ZmDS.sR_cof`), Lemma EXACT for `R(o)` and `V·R(o)` through
`Te.te_opow_pi` at the pseudo-base `V` (`Zm.ZmDS.sR_pi`), the digit lemma one level up (`Zm.ZmDS.sR_dig`), the
`TlCl` inversion by division by `ω^a` (`Zm.zm_cl_divOp`, `Zm.ZmDS.sG_gate`), the tower cofinal in `ε_{E+1}`
(`Zm.zmTw_cof`).  zgBw / zgSq are its first two cases.  Iterated (`Zm.zmCh`): `Zm.zmDirectW : ZbDirect S ε_{B_Γ+ω}`;
with the global reading (`Zm.zmGR`: bracket of `φ(1, B_Γ+ν)`, base reading `φ(1, D(x)+ν)`, `Zm.zm_glA_veb`:
`ϑˣ(Ω₁ + D(x) + t) = φ(1, D(x)+1+t)`) and the union at limit indices (`Zm.zmU`), ONE transfinite induction over
every constant index `ν < ε₀` (`Zm.zmGood_all`) gives `Zm.zmDirectE0 : ZbDirect S ε_{B_Γ+ε₀}` (node `skZmDirectE0`)
and UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+B}·ω)` for every `B < ε_{B_Γ+ε₀}` (`Zm.zmUVE0`, node `skZmFrontE0`),
unconditional.  PAST THE INDEX `ε₀`: the interface carries a base gate (`Zm.ZmDS.Eg`; the base fields only above it;
every nonzero code's gate at least it, `Zm.ZmDS.sG_Eg`; `Zm.ZmDS.raise`; the field "cofinally many small gates"
moved to `Zm.ZmDS.Gc0`, which the step always has, `Zm.ZmDS.step_gc0`); the global reading with code indices
(`Zm.zmHR`, `Zm.zmHG`: the index `n < o` of the bracket of `o` read too, `Zm.zm_bracket`, `Zm.zm_noFix`: no fixed
point of `φ(1, ·)` in `(B_Γ, ζ_{B_Γ+1})`); `Zm.zm_glA_veb2` (`ϑˣ(Ω₁ + D + t) = φ(1, D+1+t)` below `ζ_{D+1}`); the
`TlCl` inversions at `ε`-numbers (`Zm.zm_cl_eps`, `Zm.zm_cl_veb1`) and the global gate bound (`Zm.zmHG_gate`); ONE
transfinite induction over every code index `c < ζ_{B_Γ+1}` (`Zm.zmGood2_all`: the step raised by the gate of
`c+1`, `Zm.zmGood2_succ`; the union `Zm.zmCU` with the member at the bracket index, `Zm.zmGood2_lim`), so
`Zm.zmDirectZ : ZbDirect S ζ_{B_Γ+1}` (node `skZmDirectZ`) and UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+B}·ω)` for
every `B < ζ_{B_Γ+1}` (`Zm.zmUVZ`, node `skZmFrontZ`), unconditional.  REFUTE FIRST at the offset `B_Γ²·2 + 1` (reading `D(x)²·2 + 1`, gate `2`, no fixed point) and at
the code `ε_{B_Γ+1}` (reading `ε_{D(x)+1} = ϑˣ(Ω₁ + D(x))`, no fixed point): NO EVIDENCE (node `skZmRef`).
`skZbDirect` is REDUCED to `skZbDirectX` (`ZbDirect S X`, OPEN).  ASSEMBLY FIRST for the layers past `X`:
`Zb.zbUV` is generic in the atom system, so `skLayLoFixX` and `skLayHiFixX` are REDUCED to the one new leaf
`skLayPastX` (`Zm.ZmPastAt S c`: one atom system `A : Zb.ZbAS` with a layer `Zm.ZmLayA A S B` for every
`B < Γ(c+1)`, `X ≤ c < Ω₂`; `Zm.zmLay_of_past`).  The interface `Zm.ZmDS` carries a base gate (`Zm.ZmDS.Eg`,
`Zm.ZmDS.raise`) for the code indices to come.  The next wall: `ζ_{B_Γ+1}` (a fixed point of `φ(1, ·)`;
the codes past it need the brackets `φ(1, P + n)` over the pseudo-bases `P = φ(2, b)`, read `φ(2, D(x) + b(x))`):
next Lean statement a level-generic `Zm.ZmGood2` (the level `α` of `φ(α, ·)` a parameter, induction on `α`).

Round 132 (leaf regb10, modules `R2.Zg*`; this file imports `R2.ZgSq`, so it can be checked only after the merge):
THE OFFSETS PAST `B_Γ` UP TO `B_Γ·B_Γ`.  (1′) every `Yr` code `o < B_Γ` with gate `Yr.yrG o < Z` is a code of
`Tl.TlCl Z` (`Zg.zgYr`, the `TlCl` versions of `Gf.gfW_mem`, `Gi.gw_mulOm_mem`, `Gl.gl_mem`, `Yr.yr_mem`; node
`skZgTl`), so the atom `Γ_{Ω₁+1+(B_Γ+1+o)}` is an atom of `Zb.zbU` (`Zg.zgAtom`); conversely an atom of `zbU` with
index `B_Γ + 1 + o` gives `TlCl Z o` (`Zg.zgInv`, `Zg.zgInvW`).  (2′) the reading system `Zg.zgB2 : Zb.ZbRS` (index
`B_Γ + 1 + o`, `o < B_Γ`, reading `D(x) + Yr.yrR o x`, gate `Yr.yrG o`; every admissible reading is below `D(x)`,
`Zg.zgN_lt_D`), and its extension `Zg.zgBw : Zb.ZbRS` (indices `B_Γ + 1 + (B_Γ·n + r)`, `n < ω`, `r < B_Γ`, reading
`D(x)·(1+n) + Yr.yrR r x`; at `B_Γ·(n+1)` the cofinality of the tower readings in `D(x)`, `Zg.zgCofD`), with the
gated cover (`Zg.zgCoverW`).  Gates of every countable size occur; `Zb.ZbDirect` asks gates below `K` only through a
larger index of gate `0` (`Yr.yrTw`, `Zg.zbLayAt_mono`).  PROVED with no hypothesis: `Zg.zgDirectW : ZbDirect S
(B_Γ·ω)` (node `skZgDirectW`) and UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+B}·ω)` for every `B < B_Γ·ω` (`Zg.zgUVW`,
node `skZgFrontW`).  REFUTE FIRST at the offsets `1`, `ω` (the readings `D(x)+1`, `D(x)+ω` agree with `Zb.zbE0`)
and at the offset `B_Γ` (index `B_Γ·2`, reading `D(x)·2`, not a fixed point, Lemma EXACT): NO EVIDENCE
(`Zg.zgRef1`, `Zg.zgRefW`, `Zg.zgRef2`, `Zg.zgRef2_nonfix`; node `skZgRef`).  The offsets `B_Γ·q + r` with `Yr`
codes `q, r < B_Γ`: the digits of a code `B_Γ·q + r` are codes (`Zg.zgDivE`: `TlCl Z` is closed under division by an
`ε`-number code; `Zg.zgDig`), Lemma EXACT for `ω^{D(ρ)+β}` (`Zg.zgVtD`: `ϑˣ(D(x)+γ) = ω^{D(x)+1+γ}`; `Zg.zgOpowD`),
so `D·y = ω^D·y` is EXACT through `Yr.yr_dig`; the reading system `Zg.zgSq : Zb.ZbRS` (reading
`D(x)·(1 + yrR q x) + yrR r x`, gate `max (yrG q) (yrG r)`).  PROVED with no hypothesis: `Zg.zgDirectSq : ZbDirect S
(B_Γ·B_Γ)` (node `skZgDirectSq`), UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+B}·ω)` for every `B < B_Γ·B_Γ` (`Zg.zgUVSq`,
node `skZgFrontSq`).  `skZbDirect` stays OPEN: missing are the offsets `≥ B_Γ²` (hereditary Cantor normal form in
base `B_Γ` with `Yr` digits, `B_Γ ↦ D(x)`: next Lean statement a reading system for `B_Γ^k·q + r`, `k < ω`, read
`D(x)^{1+k}·(1+yrR q x) + R_k(r)`, needing Lemma EXACT for `ω^{D(ρ)·k+β}`), the φ-codes `ε_{B_Γ+1}, …` below
`Γ_{B_Γ+1}`, then the atoms of kind `β ≥ 1`.

Round 131 (leaf regb9, modules `R2.Zb*`; this file imports `R2.ZbE0`, so it can be checked only after the merge):
PAST `B_Γ` WITH AN ABSTRACT ATOM SYSTEM.  NO-GO: every `Gs.GsCS` has its bound below `B_Γ` (`Zb.zbGsCS_lt_BG`,
node `skZbGsNoGo`): its law `ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for `c ≤ B` meets the plateau `ψ_{Ω₂} = B_Γ` on `[B_Γ, Ω₂]`; so
the step "a code system `Gs.GsCS` whose bound passes `B_Γ`" of round 130 is impossible and so is every `Yr.YrRS` code
`≥ B_Γ`.  REFUTE FIRST at the code of kind `1`, index `0` and at the code of kind `ω`, index `0`: NO EVIDENCE
(`Zb.zbKind1`, `Zb.zbKindW`, `Zb.zbKindW_pi`, node `skZbKind`).  The hull calculus, Theorem UNI and the gated
frontier lemma hold for every abstract atom system `Zb.ZbAS` (`Zb.zbUni2`, `Zb.zbB1_eq`, `Zb.zbUV`; every `GsCS` is
one, `Zb.ZbAS.ofGs`); the instance `Zb.zbU` has all codes of `Tl.TlCl` below `X` as atoms (`F_β`-values, `B_Γ`
included; hull lemma `Tz.tz_diglev`, membership `Tw.tw_mem_CSet`) plus the atoms of `Yr`, agreeing with `Yr.yrKN`
below `B_Γ` (`Zb.zb_th_yr`).  The ladder (`Zb.zbLad_top`, `Zb.zbLad_poly`) and the union with any target
(`Zb.zbUnion_codes`) read their top codes with any atom system; `Zb.ZbRS` (a reading system past `B_Γ`) builds the
layer of every code with its reading in one recursion (`Zb.ZbRS.lay`) and gives `Zb.ZbDirect` (`Zb.ZbRS.direct`);
`Zb.zbLay_of_direct`: `ZbDirect S Γ(c+1)` gives the conclusions of `skLayLoFix` and `skLayHiFix` at `c`.  PROVED with
no hypothesis: the code `B_Γ` (`Zb.zbBG_UV`), the codes `B_Γ + 1 + n` (`Zb.zbBGn_UV`), and THE INDICES
`B_Γ + 1 + o`, `o < ε₀` (`Zb.zbE0`, `Zb.zbDirect_e0 : ZbDirect S (B_Γ + ε₀)`, node `skZbDirectE0`): UPPER ∧ LOWER ∧
CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)` for every `B < B_Γ + ε₀` (node `skZbFront`).  `skLayLoFix` and
`skLayHiFix` are REDUCED to the new leaf `skZbDirect` (`ZbDirect S Γ(c+1)` for `B_Γ ≤ c < X`) and the new leaves
`skLayLoFixX`, `skLayHiFixX` (the layers `X ≤ c < Ω₂`, outside the atom system `zbU`).

Round 130 (leaf regb8, modules `R2.Yw*`; this file imports `R2.YwLad`, so it can be checked only after the merge):
THE ATOM KINDS PAST `B_Γ`.  At an `ε`-number base `x` the point of level `β` is `ϑˣ(Ω₁·(Ω₁+β) + σ)` (`Yw.ywV`; level
`0` is `gq`); the atoms of kind `β` (values of `F_β` that are not fixed points) are EXACTLY the points of level `β`
(`Yw.ywKind`, one proof for every kind), and the least fixed point of `ν ↦ Γ_{x+1+ν}` above `x` (the reading of
`B_Γ`) is `ϑˣ(Ω₁·Ω₁ + Ω₁)` (`Yw.ywBG`).  REFUTED: the reading `ϑˣ(Ω₁·Ω₁·2 + ν)` proposed for the fixed points of `Γ`
(`ϑˣ(Ω₁·Ω₁·2)` is not the least closed point: `Yw.ywFirstFix_ref`, node `skFixReadX_false`).  NO-GO for the
interface of `Yr.YrRS`: no admissible reading has a fixed point of `Γ` as layer top (`Yw.ywNoGo_GqSt`).  PROVED with
no hypothesis: Lemma IMG below `X^ρ = ϑᵖ(Ω₁·Ω₁·2)` — every point of every level and every `ε`-number between
(`Yw.ywImg`, the separation `Yw.ywSep` generic in the level); the top witness of every layer whose top is below `X^ρ`
from Lemma IMG (`Yw.ywTopWit`); the union step at any top below `X^x`, closed tops included (`Yw.ywLimB`); the ladder
with `e(x) ≤ E_K(x)` (`Yw.ywLadB`); THE LAYERS OF THE CODES `B_Γ` AND `B_Γ + 1` (`Yw.ywBGB`, `Yw.ywBG1B`, node
`skFixLayBG`).  Left in `skLayLoFix` / `skLayHiFix`: a reading system for the codes `B_Γ ≤ c < X` (a code of kind `b`,
index `c` read `ϑˣ(Ω₁·(Ω₁+b(x)) + c(x))`) with its recursion, gates, EXACT, cofinality and the frontier lemma for the
atoms `ψ_{Ω₂}(Ω₂^b·…)`; then the codes `X ≤ c < Ω₂`.

Round 129 (leaf regb7, modules `R2.Yr*`; this file imports `R2.YrDir`, so it can be checked only after the merge):
READ ATOM INDICES.  The constant index of `Yh.yhR` is replaced by a read index: `Γ(i)` reads `Γ_{x+1+i(x)}`
(`Yr.yrR_atom`), a recursion on the code since `i < Γ(i)` below `B_Γ = Tf.tfBG` (the least fixed point of `Γ`).  The
facts bound to `c + 1 < ε₀` are generalized: `Xx.XxGq` to every admissible offset (`Yr.YrN`, `Yr.YrGq`), the union
step, the layer construction and the frontier lemma to reading systems with admissible readings (`Yr.YrU`,
`Yr.YrRS`, `Yr.YrLoc`), Lemma IMG at every base atom `ϑᵖ(Ω₁·Ω₁ + ν)` and below every admissible read bound
(`Yr.yrI_atom`, `Yr.yrImg`), the hull lemma through `ψ_{Ω₂}(i) = Γ(i)` (`Yr.yr_mem`); then ONE theorem
`Yr.yrDirect : YrDirect S B_Γ` (the tower `G, Γ(G), Γ(Γ(G)), …` with gate `0` is cofinal in `B_Γ`) gives the layers
`c < B_Γ` whole (`Yr.yrLayAll`, node `skLayBelowBG`), the layers `ε₀ ≤ c + 1` included.  `skLayLoBig`, `skLayHiBig`
are REDUCED to `skLayBelowBG` (PROVED) and the new leaves `skLayLoFix`, `skLayHiFix` (the layers `B_Γ ≤ c < Ω₂`, whose
atoms `Γ(c)` have indices at or past a fixed point of `Γ`).

Round 127 (leaf regb5, modules `R2.Yh*`; this file imports `R2.YhRS`, `R2.YhDir`, so it can be checked only after the
merge): ROUTE (c) IS PROVED.  `skLayDirect` = `Yh.yhDirect` (`Yc.YcDirect S c Γ(c+1)` for EVERY `c` with
`c + 1 < ε₀`, one theorem): the reading `Yh.yhR` of every code over all base atoms (`Γ(i)` read `Γ_{x+1+i}`, the
shifted count `Yh.yhPsi` at every atom level), its order, cofinality (`Yh.yh_atomCof`), Lemma EXACT, gates, hulls and
limit data, proved once; the tower `Γ(c), yhPsi Γ(c) 0, …` with gate `0` cofinal in `Γ(c+1)`.  `skLayLo` now uses
`skLayLoD`, so `skLaySysY`, `skLaySysAll1`, `skLaySysYHi` are OFF THE ROAD; the layer `0` is located whole
(`skLayDirect0`).  Left in the layer branch: `skLayLoBig`, `skLayHiBig` (`ε₀ ≤ c + 1`).

Round 126 (leaf regw1, modules `R2.Yf*`; this file imports `R2.YfWin`, so it can be checked only after the merge):
THE TRANSPORT along a cell.  `Yf.yfStretch_UV` (`skCellUV`): for every restart index `λ₀` with the BASE DATA
(`Good O` at every block boundary up to `λ₀ + ω²` and `O(λ₀) < δ_{λ₀}`) and every `B` with no fixed point of `υ`
in `(λ₀, B)`, every restart `λ₀ < λ < B` with a name has code `-1 + e(λ)`, `r(λ) = δ_λ + (-1 + e(λ))` and
UPPER ∧ LOWER ∧ CapV (relative block induction `R2.YfRel`; on the cell only constant terms occur).  One theorem
for every base of the grid (`Yf.yfGrid_UV`: names `β + ζ`, `0 < ζ < P(β)`).  `skBhiA` is REDUCED to
`skBhiAcell` (PROVED: the base `Ω₂·q` good, a restart index, with the base data; `ζ < P(Ω₂·q)`) and `skBhiAfar`
(OPEN: the rest).  REFUTE FIRST: the base data force a short reach at the base (`Yf.yfBase_short`) and no
crossing of `υ_{λ₀+ω²}`; so under `L(k) ≤₁ L(k+1)` / `L(ω) ≤₁ L(ω+1)` no restart of a window carries them
(`skWinNoBase`, `skTopNoBase`): the cell transport is VACUOUS in the windows; `skWinA` / `skWinL` / `skTopA` /
`skTopL` need a block induction relative to the long reach of `L(k)`.

Round 127 (leaf regw2, module `R2.YiWin`; this file imports it, so it can be checked only after the merge):
REFUTE FIRST for the window induction.  The proposed hypothesis "the block structure measured above `L(k)`, only
the long `≤₁` of `L(k)` allowed, short offsets `O(λ) < δ_λ` at the restarts above `L(k)`" is REFUTED by the leaf's
own conclusion: the supply `Rx.rxSupAt` puts range restarts `μ` cofinally in every window `W_n` with
`υ_{μ+ω²} ≤ r(μ)` (`Yi.yiLong_win`, unconditional); LOWER at `μ` then gives `ρ_μ ≤₁ υ_{μ+ω²}` and excludes every
relative block induction `Yf.YfSpec O λ₀ B` with `λ₀ < μ < B` and the base data at `μ` (`skWinShortRef`).  The same
holds cofinally below `L(0)` (`skMShortRef`; so `skBhiAfar` cannot be closed by cells near `L(0)`).  The window
induction must allow NESTED long reaches: corrected crossing clause `Yi.YiCross` (a crossing starts at a point
`≤ L(k)` or at a restart `ρ_μ` and stays `≤ r(μ)`); its restart part is exactly UPPER (`skWinCross`).  Its step needs
a restart context without the field `RstK.below` (false at every window restart under `L(k) ≤₁ L(k+1)`).

Round 129 (leaf regw4, modules `R2.Ys*`; this file imports `R2.YsRsAll`, so it can be checked only after the
merge): THE WINDOW INDUCTION WITH CROSSINGS.  The repo's block machinery is redone without `below`:
`Ys.YsRstK` (restart context, `below` replaced by the pair field `nostr`; Lemma C″ (a), B″4, the pair, `capδ`,
Lemma TOP `top_gen` unchanged), `Ys.YsPairCtx`, `Ys.YsBlkCtx` ((T3) only above a crossing bound `x₀`; the
crossing points reach through each block), the chain `Ys.ysCtxA`, the relative block structure `Ys.YsGood a O l`
of `(a, υ_l)` (crossing clause = `Yi.YiCross` with the bound `δ_μ + O(μ)`), its step `Ys.ysGood_step` (ordinary
restarts with a short offset term AND supply restarts with a long reach: the chain then starts at `δ_μ` with
`x₀ = ρ_μ`), the limit step, and the induction `Ys.ysGood_all` from any restart `l₀` (`Ys.YsSpec`; no base
data, only the landing blocks below `ρ_{l₀}`); Lemma RS with crossings (`Ys.ysRs_gen`, `Ys.ysRs_all`).  The
window leaves `skWinA`, `skWinL`, `skTopA`, `skTopL` are REDUCED (`skWinUL`, `skTopUL`) to the new leaves
`skWinSpec` / `skTopSpec` (the relative specification on `[ι(L(k)), ι(L(k+1)))` with the bound
`O = r − δ`), `skWinRsIn` / `skTopRsIn` (the RS input at the limit restarts) and `skWinCapV` / `skTopCapV`.
The same specification on the top window gives `Rg.RgLwPair` (`skTopPair`) and so `L(ω+1) ≤ ν_C` with the
road's hU / hV / hVt (`skTopNu`).  Non-vacuity: `skWinSpecOld` (the specification holds for `c*` below `Ξ_ω`).
REFUTE FIRST: at the restart after a supply restart the short input with a crossing bound below the supply
restart is impossible (`skWinShortX`): the supply restarts take the given-TOP input (`Ys.ysGiven_of_supply`).

Round 130 (leaf regw5, modules `R2.Yx*`; this file imports `R2.YxInd`, so it can be checked only after the merge):
THE PAIR FIELDS OF THE WINDOW INDUCTION ARE THEOREMS.  REFUTE FIRST: the pair field `nostr` of `Ys.YsSpec O l₀ B`
excludes `ν_C` from `[ρ_{l₀}, υ_B)` (`Yx.yxSpec_nu`, skWinSpecNu), so the old leaves skWinSpec / skTopSpec contained
`ν_C ∉ W_k` / `W_ω`.  Strict NU-LOW″ at every height (`Yx.yxNu_gt`, skNuGt: CAP-0 and CAP-1 below `X ≤ L(ω)` give
`X < ν_C`); every pair field holds at a restart below `ν_C` (`Yx.yxNostr_of_lt`, `Yx.yxChainNostr_of_lt`); the
least-counterexample theorem `Yx.yxSpec_caps` (a pair-free `Yx.YxSpec`, the caps below the base and CapV in the
window give `υ_B ≤ ν_C` and `Ys.YsSpec`; Lemma TOP inside the window supplies the caps up to `ν_C`).  The windows
are now ONE INDUCTION ON `k` (skWinAll = `Yx.yxWins`; the landing blocks below `L(k)` from `L(k) < ν_C`,
`R2.land_C`), the top window after them (skTopAll = `Yx.yxTopAll`, with `Yx.yxNu_gtTop`).  skWinSpec, skTopSpec
REDUCED (statements unchanged) to the new leaves skWinIn / skTopIn (pair-free inputs, `Yx.YxIn`) and skTopLwNo2
(`ν_C < L(ω+1) → ¬ L(ω) <₂ ν_C`: as strong as `L(ω+1) ≤ ν_C` given the rest, `Yx.yxLwNo2_iff`).  The window
section was moved after skRegC (it now uses skBelowL0 = regions A, B-lo, B-hi, C).

Round 131 (leaf regw6, modules `R2.Zc*`; this file imports `R2.ZcSup`, so it can be checked only after the merge):
THE BASE REACH DATUM AND THE RS STEP ARE THEOREMS.  (1) The base part of `Yx.YxIn` (`Ys.YsReachIn ι(L(k)) 0 L(k)`)
is proved INSIDE the window induction (`Zc.zcBaseIn`, skWinBase): `L(k) ≤₁ υ_{ι(L(k))+ω²}` by the realizer maps of
the shift (`Zc.zcReal_shift` = `Lr.lrReal_shift` without its hypothesis `Cx.CxStdPairTop`, which is needed only for
standard pairs below `L(k) < ν_C`, `R2.pair_std`; `Zc.zcLe1_of_real` = `Lr.lrLe1_of_real` with LOWER only below
`L(k)`), the supply `Rx.rxSupAt` (at `L(ω)`: `Rc.rcSupAt_Lw_of`), LOWER below `L(k)` from the earlier windows, and
`L(k) < ν_C` from the caps.  skWinIn / skTopIn are REPLACED by skWinInR / skTopInR (`Zc.ZcInR`: the inputs at the
restarts strictly inside the window only).  (2) Lemma RS with crossings for every offset term (`Zc.zcRs_rstT`, the
port of `R2.rs_rstT` to `Ys.YsRstK`; the pairs up to `δ + t(ρ)` from `ρ < ν_C`, `Zc.zcNostr_of_nu`), so the RS
input is a statement on the predicted reaches alone (`Zc.ZcRsIn`, `Zc.ZcRsTerm`; `Zc.zcRs_all`): skWinRsIn /
skTopRsIn are REPLACED by skWinRsT / skTopRsT.  skWinAll = `Zc.zcWins2`, skTopAll = `Zc.zcTopAll2` (statements
unchanged).  NO-GO (skRsLongNoGo, `Zc.zcRsTerm_long_false`): at a supply restart (`υ_{λ+ω²} ≤ r(λ)`) the term input
is false, so there the RS input is LOWER itself (`Zc.zcRsIn_long_lower`).  The given input at a restart follows
from UPPER there and `ρ_λ ≤₁ υ_{λ+ω²}` (`Zc.zcGiven_of_up`), the latter from the supply below `ρ_λ`
(`Zc.zcGiven_of_sup`).

Round 132 (leaf regw7, modules `R2.Zh*`; this file imports `R2.ZhSup`, so it can be checked only after the merge):
LOWER AT THE SUPPLY RESTARTS FROM THE SUPPLY ALONE.  (1) NO-GO for short realizer targets (skSupBeta,
`Zh.zhSup_beta2`): a supply restart covers the reach of its inner restart `λ+ω²` (`r(λ)` is a closed point,
`Zh.zhR_lh`), so `r(λ) ≤ υ_{λ+β}` needs `β ≥ ω²+ω+1` (`β > ω²+ω+1` once `ρ_{λ+ω²} ≤₁ δ_{λ+ω²}+1`): the case `β = ω²+1`
of REFUTE FIRST is empty, and every realizer for LOWER at a supply restart must carry inner restarts.  (2) The
realizer maps for EVERY target `υ_{λ+β}` (skRealGen, `Zh.zhReal_gen`): the FRAG move of `Zc.zcReal_shift` with the
blocks and standard pairs of every inner restart `λ+γ` and the carry `Zh.ZhCarry` of the inner reaches (the segment
bases and small offsets are added to the configuration).  (3) Below `ν_C` the points `δ_λ + x` (`x < δ_λ`) are
closed (skDense, `Zh.zhDense`, from the blocks 0 and 1 and `R2.le1R_lim_P`), so every restart `λ` with
`ρ_λ < ν_C` and `m_λ ≤ ρ_λ` has `r(λ) = δ_λ + m_λ` (skShortAll, `Zh.zhR_short_all`) and a supply restart has
`m_λ > ρ_λ` (skLongCode).  (4) The carry is a THEOREM for `β ≤ ρ_μ` (skCarryAuto, `Zh.zhCarry_auto`: the inner
names `η_λ+γ`, `η_μ+γ` have the same code `-1+e(γ)`, `Cp.cpCode_add`).  (5) Lemma RS with the supply input
(`Zh.zhRs_all`; LOWER at the inner restarts `μ+γ` from the induction): skWinRsT / skTopRsT are REPLACED by the
weaker skWinRsS / skTopRsS (`Zc.ZcRsIn ∨ Zh.ZhSupInB`: at a supply restart the supply `Zh.ZhSupB` for one target
`β ≤ ρ_μ`, no LOWER); skWinAll = `Zh.zhWins5`, skTopAll = `Zh.zhTopAll5` (statements unchanged).  (6) CapV at
the restarts with a short last exponent `2 ≤ e(η_λ) < ρ_λ` is a THEOREM below `ν_C` (skCapVShort,
`Zh.zhCapV_short`; the cap is `P(η_λ+ω^e) = υ_{λ+ω^e}`), and the least-counterexample argument reads CapV only below
`ν_C` (`Zh.zhSpec_capsV`): skWinCapV / skTopCapV are REPLACED by the long-exponent leaves skWinCapVL / skTopCapVL
and the theorems skWinCapVAll / skTopCapVAll (from skWinAll / skTopAll).  (7) EVERY RESTART `ω² < λ < υ_λ` HAS
NAME `η_{λ₀} + z`, `z < ρ_{λ₀}`, and code `m_λ = cL λ` (`Zh.zh_code_cL`); below `ν_C` its reach is `δ_λ + cL λ`
(skRNonfix), its RS input is a theorem (skRsNonfix, `Zh.zhRsIn_nonfix`), so is CapV (skCapVNonfix), and every supply
restart is a `υ`-fixed point (skSupFix).  The leaves skWinRsS / skTopRsS / skWinCapVL / skTopCapVL ask only the
`υ`-fixed restarts of the windows (`Zh.zhWins6`, `Zh.zhTopAll6`).

Round 133 (leaf regw8, modules `R2.Zn*`; the PROVED nodes below can be checked only after the merge): (1) LEMMA RS
WITH A VALUE (skValRS, `Zn.znRs_rstV`): the offset term of `Zc.zcRs_rstT` is used only through its value
`v < υ_{λ+1}`, whose FRAG image is `π_{ρ_μ,ρ_λ}(v)`; so the RS input may be the value input `Zn.ZnRsVal`
(skRsAllVal, `Zn.znRs_all`; the term input gives it, skValOfTerm).  The term input is FALSE once an `ε`-number lies
in `(ρ_λ, O(λ))` (skTermEpsNoGo), the value input once `υ_{λ+1} < O(λ)`.  (2) At a `υ`-fixed restart
`c(λ) = λ` and `Θ_λ(m_λ) ≥ ρ_λ`; if `Θ_λ(m_λ) ≤ ρ_λ` the RS input is a THEOREM below `ν_C` (skRsFixShort,
`Zn.znRsIn_fixShort`, constant terms); if `Θ_λ(m_λ) < δ_λ·ω` CapV is a THEOREM below `ν_C` (skCapVFixW,
`Zn.znCapV_fixThW`: `r = δ + Θ < δ·ω ≤ υ_{λ+ω+2} ≤ P(η_λ+ω^e)`).  (3) REFUTE FIRST at the first `υ`-fixed restart
of `W₁` (isolated from fixed restarts below): the supply branch `Zh.ZhSupInB` is FALSE for every `β` (skSupIsoNoGo;
`β = ω²+ω+1` included), so are the term and value branches when `ρ_λ < Θ_λ(m_λ)` (skTermIsoNoGo, skValIsoNoGo):
there the RS input is LOWER (skIsoLower); with the code statement `Θ_λ(m_λ) ≤ ρ_λ` (true below `cpB1`,
`Cp.cpFix_code`) it is a theorem.  CapV there holds when `Θ_λ(m_λ) < δ_λ·ω`.  (4) skWinRsS / skTopRsS /
skWinCapVL / skTopCapVL are REPLACED by skWinRsF / skTopRsF (fixed, `ρ_λ < Θ_λ(m_λ)`, given `υ_{B} ≤ ν_C`; value
branch allowed) and skWinCapVF / skTopCapVF (fixed, `δ_λ·ω ≤ Θ_λ(m_λ)`, below `ν_C`); skWinAll = `Zn.znWins`,
skTopAll = `Zn.znTopAll` (statements unchanged).  skWinRsF / skTopRsF are REDUCED (`Zn.znRsF_of_parts2`) to the code
statement at the isolated fixed restarts (skWinIsoCode / skTopIsoCode), the code continuity `Zn.ZnThCont` where
`ρ_λ < Θ_λ(m_λ) ≤ υ_{λ+1}` (skWinCont / skTopCont, no `≤₁`) and LOWER or the supply where `υ_{λ+1} < Θ_λ(m_λ)`
(skWinBig / skTopBig; there `ZcRsIn` is LOWER, skBigLower), both only at fixed restarts that are limits of fixed
restarts.  (5) Off the road: at a non-fixed restart below `ν_C` the short window input is a theorem from the
separated chain reach datum (skShortInNonfix, `Zn.znShortIn_of_sep`).
Round 133 (leaf regc1, modules `R2.Zo*`; this file imports `R2.ZoBC`, so it can be checked only after the merge):
(B-hi) AND (C) BY ONE RELATIVE BLOCK INDUCTION.  Every (B-hi) restart (names `Ω₂·q + ζ`, cells and far offsets
alike, layer cells included) and every (C) restart lies in `[ι(Ω₂), ι(Ω_ω))`; every range restart below `ι(Ω₂)` is in
(A) or (B-lo) (skBCLow).  The window induction runs on `[l₀, ι(Ω_ω))`, `l₀ = Zo.zoBase S` the least restart index
`≥ ι(Ω₂)` (`Zo.zoBC`), WITHOUT CAP-0: below `m*` the caps below the current height place every point below `ν_C`
(`Zo.zoNu_gt0`).  skBhiAfar, skBhiL, skLongPre are PROVED from skBC, which is REDUCED to the leaves skBCBaseUV
(UV at `l₀`), skBCReach (the base chain datum with a chain start `o ≤ r − δ`; with `o = 0` it is REFUTED at
short-reach bases, skReach0Ref), skBCInR, skBCCapVH (CapV at fixed long-exponent restarts with high codes; the low
codes are `Zo.zoCapV_low`), skBCRsS.  Bonus: skNuL0 (`L(0) ≤ ν_C`) from the same leaves.  Non-vacuity: skBCVac.
The block (skBhiAfar … skLongTop) is moved after skRegA (it now uses skSplit, skRegA, skRegBlo).
-/

set_option autoImplicit false

namespace R2Skel.SkF

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-! ## Abbreviations -/

/-- ENUM-REACH (UPPER and LOWER) and CapV at the restart index `l`. -/
def SkUV (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l

/-- The frontier of `Ho.hoUf`: `ι(Γ(φ(Ω₁³, G+1))·ω)`. -/
noncomputable def skFHo (S : InaccSeq.{0}) : Ordinal.{0} := Bt.iota S (Gc.gcG Ho.hoUf.B * ω)

/-- The frontier of `Wo.woVE` (round 118): `ι(Γ(φ(ε_{Ω₁+1}, G+1))·ω)`. -/
noncomputable def skFE (S : InaccSeq.{0}) : Ordinal.{0} := Bt.iota S (Gc.gcG Wo.woVE.B * ω)

/-- The level codes of the generic induction: `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < ε_{Ω₁+1}`. -/
def SkLev (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < Gf.gfE

/-- An entry of the induction: the package at a level (steps at every pseudo-base) and the system over `G`. -/
abbrev SkEnt : Type 1 := Hn.HnPk × ULift.{1} Hg.HgVD

/-- The entry `E` sits at the level `ℓ`: package level `ℓ` read `rdc ℓ x` above its gate; system
`B = φ(ℓ, G+1)` with gate `≤ gtc ℓ`. -/
def SkAt (ℓ : Ordinal.{0}) (E : SkEnt) : Prop :=
  E.1.Λ.L = ℓ ∧ (∀ x, InE x → x < Om1 → E.1.Λ.g < x → E.1.Λ.l x = Gf.rdc ℓ x) ∧
    E.2.down.B = veblen ℓ (Gc.gcG 0 + 1) ∧ E.2.down.γ ≤ Gf.gtc ℓ

/-- `E` extends `E'`: the packages extend (`Hn.HnkExt`), the system bound grows, readings and gates agree below. -/
def SkExt (E' E : SkEnt) : Prop :=
  Hn.HnkExt E'.1 E.1 ∧ E'.2.down.B < E.2.down.B ∧
    ∀ c x, c < E'.2.down.B → E.2.down.R c x = E'.2.down.R c x ∧ E.2.down.g c = E'.2.down.g c

/-- A coherent family below `ℓ`. -/
def SkCoh (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkAt ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLev ℓ'' → SkLev ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

/-- The step at `ℓ`: every coherent family below `ℓ` has an entry at `ℓ` extending all of it. -/
def SkStepAt (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCoh ℓ f → ∃ E, SkAt ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkExt (f ℓ' h) E

/-- Shape: successor level `ℓ = ℓ' + Ω₁`. -/
def ShSucc (ℓ : Ordinal.{0}) : Prop := ∃ ℓ', SkLev ℓ' ∧ ℓ = ℓ' + Om1

/-- Shape: `ℓ = P + Ω₁^{e+1}`, `e ≥ 1` (union over the prefixes `P + Ω₁^e·v`, `v < Ω₁`). -/
def ShPow (ℓ : Ordinal.{0}) : Prop := ∃ P e : Ordinal.{0}, 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)

/-- Shape: `ℓ = P + Ω₁^e`, `e` a limit (transfinite exponent). -/
def ShExpLim (ℓ : Ordinal.{0}) : Prop := ∃ P e : Ordinal.{0}, IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e

/-- Shape: `ℓ = P + Ω₁^e·c`, `c < Ω₁` a limit (an `ω`-chain union). -/
def ShCoefLim (ℓ : Ordinal.{0}) : Prop :=
  ∃ P e c : Ordinal.{0}, 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ e * c

/-- REFUTED form (round 115 as elaborated): `ShPow` with `e : ℕ`. -/
def ShPowN (ℓ : Ordinal.{0}) : Prop := ∃ P e, 1 ≤ e ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ (e + 1)

/-- REFUTED form (round 115 as elaborated): `ShExpLim` with `e : ℕ`. -/
def ShExpLimN (ℓ : Ordinal.{0}) : Prop := ∃ P e, IsSuccLimit e ∧ Om1 ^ e ∣ P ∧ ℓ = P + Om1 ^ e

/-- REFUTED form (round 115 as elaborated): `ShCoefLim` with `e : ℕ`. -/
def ShCoefLimN (ℓ : Ordinal.{0}) : Prop :=
  ∃ P e c, 1 ≤ e ∧ IsSuccLimit c ∧ c < Om1 ∧ Om1 ^ (e + 1) ∣ P ∧ ℓ = P + Om1 ^ e * c

/-- The corrected entry predicate (round 116): `Wh.WhAt` (the entry of `SkAt`, the gate `≤ gtc ℓ`, every
`ε`-number above the gate is above `gtc ℓ`, the system is a start over `G` at the package). -/
def SkAtW (ℓ : Ordinal.{0}) (E : SkEnt) : Prop := Wh.WhAt ℓ E.1 E.2.down

/-- A coherent family below `ℓ` (for `SkAtW`). -/
def SkCohW (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkAtW ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLev ℓ'' → SkLev ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

/-- The step at `ℓ` (for `SkAtW`). -/
def SkStepAtW (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCohW ℓ f → ∃ E, SkAtW ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLev ℓ' → SkExt (f ℓ' h) E

/-- The transfinite digit gate: every hereditary `Ω₁`-digit of a code over `Z` (below `ε_{Ω₁+1}`) is `< Z`. -/
def SkDigitGate : Prop :=
  ∀ Z, SC Z → Z ≤ Om 1 → ∀ y, Mx.GxCl Z {Gc.gcG 0} y → y < Gf.gfE → Gf.gtc y < Z

/-- EXACT of the reading `rdc ℓ` above the gate `gtc ℓ`. -/
def SkReadExact : Prop :=
  ∀ ℓ σ ρ, SkLev ℓ → Bases σ ρ → Gf.gtc ℓ < σ → Gf.rdc ℓ ρ ∈ TB ρ σ ∧ pi σ ρ (Gf.rdc ℓ ρ) = Gf.rdc ℓ σ

/-- The level datum for a general `ℓ`: an `Hn.HnLv` with `L = ℓ`, gate `≤ gtc ℓ`, reading `rdc ℓ`. -/
def SkLvDatumAll : Prop :=
  ∀ ℓ, SkLev ℓ → ∃ Λ : Hn.HnLv, Λ.L = ℓ ∧ Λ.g ≤ Gf.gtc ℓ ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = Gf.rdc ℓ x

/-! ## PROVED nodes (repo) -/

/-- STATUS: PROVED (Hg.hgV_locD_enum, Hg.hgV_locD_capV)
SIZE: S
∀ system V, γ_V < K: ∀ range λ < ι(Γ(B_V)·ω), UPPER ∧ LOWER ∧ CapV. -/
theorem skLocOfSys (S : InaccSeq.{0}) (V : Hg.HgVD) (hγ : V.γ < Td.tdK S) :
    ∀ l, Cd.CdRange S l → l < Bt.iota S (Gc.gcG V.B * ω) → SkUV S l := fun _ hr hl =>
  ⟨(Hg.hgV_locD_enum V S hγ hr hl).1, (Hg.hgV_locD_enum V S hγ hr hl).2,
    Hg.hgV_locD_capV V S hγ hr hl⟩

/-- STATUS: PROVED (Ho.hoUf_enum, Ho.hoUf_capV)
SIZE: S
∀ range λ < ι(Γ(φ(Ω₁³, G+1))·ω): UPPER ∧ LOWER ∧ CapV. -/
theorem skLocHo (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → l < skFHo S → SkUV S l := fun _ hr hl =>
  ⟨(Ho.hoUf_enum S hr hl).1, (Ho.hoUf_enum S hr hl).2, Ho.hoUf_capV S hr hl⟩

/-- STATUS: PROVED (Ho.hoUf_B, Ho.hoUf_γ)
SIZE: S
the G-system at ℓ = Ω₁³: B = φ(Ω₁³, G+1), gate 0. -/
theorem skSysHo : ∃ V : Hg.HgVD, V.B = veblen (Om1 * Om1 * Om1) (Gc.gcG 0 + 1) ∧ V.γ = 0 :=
  ⟨Ho.hoUf, Ho.hoUf_B, Ho.hoUf_γ⟩

/-- STATUS: PROVED (Ho.hoSg_B, Ho.hoSg_γ)
SIZE: S
∀ ν < Ω₁: the G-system at ℓ = Ω₁²·(1+ν): B = φ(Ω₁²·(1+ν), G+1), gate max(0, hlGt(1+ν)). -/
theorem skSysHoSg {ν : Ordinal.{0}} (hν : ν < Om1) :
    ∃ V : Hg.HgVD, V.B = veblen (Om1 * Om1 * (1 + ν)) (Gc.gcG 0 + 1) ∧ V.γ = max 0 (Hl.hlGt (1 + ν)) :=
  ⟨Ho.hoSg ν, Ho.hoSg_B hν, Ho.hoSg_γ hν⟩

/-- STATUS: PROVED (Gf.rdc_pi)
SIZE: S
∀ ℓ < ε_{Ω₁+1}, gtc ℓ < σ: rdc ℓ ρ ∈ Tᵖ[σ] ∧ π(rdc ℓ ρ) = rdc ℓ σ. -/
theorem skReadExact : SkReadExact := fun _ _ _ hℓ hB hg => Gf.rdc_pi hB hℓ.2.2 hg

/-- STATUS: PROVED (Ho.hoWaRoad_hyp_iff)
SIZE: S
the four hypotheses from ι(Γ(φ(Ω₁², G+1))·ω) on ⇔ the four from F_Ho = ι(Γ(φ(Ω₁³, G+1))·ω) on. -/
theorem skHypIff (S : InaccSeq.{0})
    (h : ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l) :
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l) ∧
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l) ∧
    (∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ∧
    (∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) := by
  obtain ⟨h1, h2, h3, h4⟩ := Ho.hoWaRoad_hyp_iff S
  exact ⟨h1.2 fun l hr hl => (h l hr hl).1, h2.2 fun l hr hl => (h l hr hl).2.1,
    h3.2 fun l hr _ hl => (h l hr hl).2.2, h4.2 fun l hr _ hl => (h l hr hl).2.2⟩

/-! ## Leaves of the level-code induction (round 116) -/

/-- STATUS: PROVED (Wh.whShape; round 116, statement corrected: `e : Ordinal` in `ShPow`, `ShExpLim`, `ShCoefLim`)
SIZE: S
∀ ℓ: Ω₁ ≤ ℓ, Ω₁ ∣ ℓ, ℓ < ε_{Ω₁+1} ⇒ ℓ = Ω₁ ∨ succ ∨ pow ∨ exp-limit ∨ coefficient-limit (Cantor normal form). -/
theorem skShape : ∀ ℓ, SkLev ℓ → ℓ = Om1 ∨ ShSucc ℓ ∨ ShPow ℓ ∨ ShExpLim ℓ ∨ ShCoefLim ℓ :=
  fun ℓ h => Wh.whShape ℓ h.1 h.2.1 h.2.2

/-- STATUS: REFUTED (Wh.whShapeNat_false; witness Ω₁^ω)
SIZE: S
the round-115 form of skShape, with `e : ℕ` in the last three shapes, is FALSE. -/
theorem skShapeNat_false : ¬ ∀ ℓ, SkLev ℓ → ℓ = Om1 ∨ ShSucc ℓ ∨ ShPowN ℓ ∨ ShExpLimN ℓ ∨ ShCoefLimN ℓ :=
  Wh.whShapeNat_false

/-- STATUS: PROVED (Wh.whDigitGate)
SIZE: M
SC Z ≤ Ω₁, y code over Z (atom G), y < ε_{Ω₁+1} ⇒ gtc y < Z (transfinite digit gate). -/
theorem skDigitGate : SkDigitGate := Wh.whDigitGate

/-- STATUS: PROVED (Wh.whLvDatumAll; the level datum Wh.whLv ℓ, gate = gtc ℓ; the hypotheses are not needed)
SIZE: S
digit gate ∧ EXACT ⇒ ∀ ℓ ∃ HnLv: L = ℓ, l x = rdc ℓ x above g ≤ gtc ℓ. -/
theorem skLvOfGate : SkDigitGate → SkReadExact → SkLvDatumAll := fun _ _ => Wh.whLvDatumAll

/-- STATUS: PROVED (Wh.whStepBase)
SIZE: S
the entry at ℓ = Ω₁: package Hn.hnPk1 (read x) and the G-system Hg.hgU at φ(Ω₁, G+1). -/
theorem skStepBase : SkStepAt Om1 := fun _ _ =>
  ⟨(Hn.hnPk1, ULift.up Hg.hgU), Wh.whStepBase, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- STATUS: REPLACED (by skStepSuccW: SkAt has no start condition of the system over G at the package, so the step
would have to extend an ARBITRARY digit system at φ(ℓ', G+1); no generic construction does that; NO EVIDENCE against)
SIZE: M
ℓ = ℓ' + Ω₁ (for SkAt). -/
theorem skStepSucc (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepPowW; same reason as skStepSucc)
SIZE: M
ℓ = P + Ω₁^{e+1} (for SkAt). -/
theorem skStepPow (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShPow ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepExpLimW; same reason as skStepSucc; in round 115 it was vacuous, `e : ℕ`)
SIZE: M
ℓ = P + Ω₁^e, e limit (for SkAt). -/
theorem skStepExpLim (hLv : SkLvDatumAll) (hG : SkDigitGate) : ∀ ℓ, SkLev ℓ → ShExpLim ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepCoefLimW; same reason as skStepSucc)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit (for SkAt). -/
theorem skStepCoefLim (hLv : SkLvDatumAll) : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAt ℓ := by
  sorry

/-- STATUS: PROVED (Wh.whAt_base)
SIZE: S
the entry at ℓ = Ω₁ for SkAtW: Hn.hnPk1 and Hg.hgU (Hg.hgU is a start over G, Wh.whU_shape). -/
theorem skStepBaseW : SkStepAtW Om1 := fun _ _ =>
  ⟨(Hn.hnPk1, ULift.up Hg.hgU), Wh.whAt_base, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- STATUS: PROVED (Wh.whSucc_at, Wh.whSucc_ext, Wh.whSucc_ext_lt)
SIZE: M
ℓ = ℓ' + Ω₁: package Hn.HnPk.succ, G-system = the union over G (Wh.whGW) started at the system at ℓ'. -/
theorem skStepSuccW : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAtW ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩ f ⟨hat, hext⟩
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ Wh.wh_Om1_pos
  have hat' := hat ℓ' hlt hℓ'
  refine ⟨((f ℓ' hlt).1.succ, ULift.up (Wh.whSuccV hat')), Wh.whSucc_at hℓ'.2.1 hℓ.2.2 hat', fun ℓ'' h'' hℓ'' => ?_⟩
  have hle : ℓ'' ≤ ℓ' := not_lt.1 fun h => absurd h'' (not_lt.2 (Wh.wh_lev_succ_le hℓ'.2.1 hℓ''.2.1 h))
  rcases hle.lt_or_eq with hl | rfl
  · exact Wh.whSucc_ext_lt hℓ'.2.1 hℓ.2.2 hat' hl hℓ''.2.1 (hat ℓ'' h'' hℓ'') (hext ℓ'' ℓ' h'' hlt hl hℓ'' hℓ')
  · exact Wh.whSucc_ext hat'

/-- STATUS: REPLACED (round 117: by skStepOm1W2 on the corrected coherence SkCohW2; on SkCohW the package relation
HnkExt is vacuous across a gate drop, so the union cannot be shown to extend every member)
SIZE: M
ℓ = P + Ω₁^{e+1} (e ≥ 1, cf Ω₁), for SkAtW: package = at every pseudo-base Q the union over the systems over Q at
the levels P + Ω₁^e·v (v < Ω₁) and everything between (a recursion of systems over a base datum, generic in the level;
Ho.HoBR / Ho.HoStep are P = 0, e = 2 with the band levels only); G-system = the same recursion over G and Ho.hoOU. -/
theorem skStepPowW : ∀ ℓ, SkLev ℓ → ShPow ℓ → SkStepAtW ℓ := by
  sorry

/-- STATUS: REPLACED (round 117: cf(e) = ω by skStepExpLimFsW2 (PROVED), cf(e) = Ω₁ by skStepOm1W2, both on
SkCohW2; same reason as skStepPowW)
SIZE: M
ℓ = P + Ω₁^e, e limit, for SkAtW: cf(e) = ω: as skStepCoefLimW along e_k → e; cf(e) = Ω₁: as skStepPowW. -/
theorem skStepExpLimW : ∀ ℓ, SkLev ℓ → ShExpLim ℓ → SkStepAtW ℓ := by
  sorry

/-- STATUS: REPLACED (round 117: by skStepCoefLimW2 (PROVED) on SkCohW2; same reason as skStepPowW)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit, for SkAtW: package Ho.hoPkL of an Ho.HoSeq along c_k → c (needs gates non-decreasing
along the sequence: SkAtW gives only g ≤ gtc ℓ; take a non-decreasing subsequence, or make the gate a function of ℓ);
G-system = the gated ω-chain union (Ho.hoGCh generalized to abstract levels) with its start condition at the limit. -/
theorem skStepCoefLimW : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAtW ℓ := by
  sorry

/-- STATUS: PROVED (Wh.whCofLev; ℓ = a member of the tower Gf.gfTw)
SIZE: S
∀ B < φ(ε_{Ω₁+1}, G+1) ∃ ℓ (SkLev ℓ, gtc ℓ < K, B ≤ φ(ℓ, G+1)). -/
theorem skCofLev (S : InaccSeq.{0}) : ∀ B, B < veblen Gf.gfE (Gc.gcG 0 + 1) →
    ∃ ℓ, SkLev ℓ ∧ Gf.gtc ℓ < Td.tdK S ∧ B ≤ veblen ℓ (Gc.gcG 0 + 1) := Wh.whCofLev S

/-! ## Round 117: the corrected coherence (leaf gam42, modules `R2.Wm*`) -/

/-- The corrected extension of entries: packages by `Wm.WmExt` (lowering by the pseudo-base gate). -/
def SkExtW2 (E' E : SkEnt) : Prop := Wm.WmExtE E' E

/-- The corrected coherence of a family below `ℓ` (`SkAtW` entries, `SkExtW2` between levels). -/
def SkCohW2 (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop := Wm.WmCoh ℓ f

/-- The step at `ℓ` on the corrected coherence. -/
def SkStepAtW2 (ℓ : Ordinal.{0}) : Prop := Wm.WmStepAt ℓ

/-- STATUS: PROVED (Wm.wm_old_vacuous, Wm.wm_gate_drop)
SIZE: S
the old package relation HnkExt K' K holds whenever K.g < K'.g (it says nothing across a gate drop), and gate drops
occur between levels: Ω₁·ω < Ω₁², gtc(Ω₁²) = 2 < ω = gtc(Ω₁·ω). -/
theorem skOldVacuous : (∀ K' K : Hn.HnPk, K.Λ.g < K'.Λ.g → Hn.HnkExt K' K) ∧
    SkLev (Om1 * ω) ∧ SkLev (Om1 * Om1) ∧ Om1 * ω < Om1 * Om1 ∧ Gf.gtc (Om1 * Om1) < Gf.gtc (Om1 * ω) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Wm.wm_gate_drop
  refine ⟨fun _ _ h => Wm.wm_old_vacuous h, h1, h2, h3, ?_⟩
  rw [h4, h5]; exact natCast_lt_omega0 2

/-- STATUS: PROVED (Wm.wmExtE_old)
SIZE: S
SkExtW2 ⇒ SkExt (the corrected extension is stronger). -/
theorem skExtW2_old {E' E : SkEnt} (h : SkExtW2 E' E) : SkExt E' E := Wm.wmExtE_old h

/-- STATUS: PROVED (Wm.wmExtE_old)
SIZE: S
SkCohW2 ⇒ SkCohW. -/
theorem skCohW2_old {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt} (h : SkCohW2 ℓ f) : SkCohW ℓ f :=
  ⟨h.1, fun a b ha hb hab h1 h2 => Wm.wmExtE_old (h.2 a b ha hb hab h1 h2)⟩

/-- STATUS: PROVED (Wm.wmStep_base)
SIZE: S
the entry at Ω₁ (Hn.hnPk1, Hg.hgU) on SkCohW2. -/
theorem skStepBaseW2 : SkStepAtW2 Om1 := Wm.wmStep_base

/-- STATUS: PROVED (Wm.wmStep_succ: Wm.wmSucc_ext, Wm.wmSucc_ext_lt, Wh.whSucc_at, Wh.whSucc_ext_lt)
SIZE: M
ℓ = ℓ' + Ω₁ on SkCohW2. -/
theorem skStepSuccW2 : ∀ ℓ, SkLev ℓ → ShSucc ℓ → SkStepAtW2 ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩
  exact Wm.wmStep_succ hℓ' hℓ.2.2

/-- STATUS: PROVED (Wm.wmStep_fs: Wm.WmLim — the limit package Wm.wmPkL of a Wm.WmSeq and the gated ω-chain union
of the systems over G, Wm.WmLim.at_lim, Wm.WmLim.ext_below)
SIZE: M
every level with an ω-sequence of levels (strictly increasing, cofinal with room for +1, gates ≤ gtc ℓ), on
SkCohW2. -/
theorem skStepFsW2 : ∀ ℓ, SkLev ℓ → Wm.WmFs ℓ → SkStepAtW2 ℓ := fun _ hℓ h => Wm.wmStep_fs hℓ h

/-- STATUS: PROVED (Wm.wmStep_coef, Wm.wmFs_coef: ℓ_k = P + Ω₁^e·(c_k + 1), c_k = He.heFs c k)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit, on SkCohW2. -/
theorem skStepCoefLimW2 : ∀ ℓ, SkLev ℓ → ShCoefLim ℓ → SkStepAtW2 ℓ := by
  rintro ℓ hℓ ⟨P, e, c, he, hc, hcO, hP, rfl⟩
  exact Wm.wmStep_coef he hc hcO hP hℓ

/-- STATUS: PROVED (Wm.wmStep_exp, Wm.wmFs_exp: ℓ_k = P + Ω₁^{e_k}; Wm.wmExpFs_digit / Wm.wmExpFs_lim supply the
ω-sequence of e when its last digit is a countable limit, or e = E + Ω₁^f·d' + Ω₁^f with f having one)
SIZE: M
ℓ = P + Ω₁^e, e limit with an ω-sequence of exponents (gates ≤ gtc e), on SkCohW2. -/
theorem skStepExpLimFsW2 : ∀ ℓ P e, SkLev ℓ → IsSuccLimit e → Om1 ^ e ∣ P → ℓ = P + Om1 ^ e → Wm.WmExpFs e →
    SkStepAtW2 ℓ := by
  rintro ℓ P e hℓ he hP rfl hE
  exact Wm.wmStep_exp he hP hE hℓ

/-- STATUS: REPLACED (round 118: by skStepAllWo / skFamW2 — the family over all raw data, Wo.woStep_all,
Wo.woFamW2; not used.  REFUTE FIRST: NO EVIDENCE against; for an ARBITRARY coherent family it is not proved: at a
pseudo-base Q with gate γ the members at Ω₁·x, x an ε-number > γ, have gate ≥ x (Wo.wo_gate_ge) and give no step at Q)
SIZE: L
THE ONE REMAINING STEP OF A1: every level ℓ < ε_{Ω₁+1} that is not Ω₁, not ℓ' + Ω₁ and has no ω-sequence (cofinality
Ω₁: P + Ω₁^{e+1}, and P + Ω₁^e with e of cofinality Ω₁), on SkCohW2.  Needed: for the members ℓ_v = P + Ω₁^e·v
(v < Ω₁; for an exponent limit, along e's own Ω₁-sequence), at every base datum (a pseudo-base Q of level ℓ for the
package, G for the system), a recursion of systems over the base through ALL levels in [P, ℓ) (successor: Hn.hnwU over
the base with the family's package at the level; ω-limits: the chain of WmSys over the base; Ω₁-limits: recursively
this step), then Ho.hoOU with SMALL (the gate of a member forces its index below σ); Ho.HoBR / Ho.HoStep are the case
P = 0, e = 1 with the band packages.  REFUTE FIRST: NO EVIDENCE against (no no-go result mentions systems over G or
pseudo-bases; the case ℓ = Ω₁²·(1+ν) is realised by the Ho stack with its own family). -/
theorem skStepOm1W2 : Wm.WmOm1Step Gf.gfE := by
  sorry

/-- STATUS: REPLACED (round 118: by skStepAllWo; not used)
SIZE: M
the step at every level on SkCohW2. -/
theorem skStepW2 : ∀ ℓ, SkLev ℓ → SkStepAtW2 ℓ := fun ℓ hℓ => Wm.wmStep_all skStepOm1W2 ℓ hℓ hℓ.2.2

/-- STATUS: PROVED (Wm.wmFam_sq, Wm.wmOm1Step_sq: below Ω₁² every level is Ω₁, a successor or has an ω-sequence)
SIZE: M
NON-VACUITY of SkCohW2: a family on all levels below Ω₁², every entry SkAtW, every pair SkExtW2, with no hypothesis. -/
theorem skFamSq : ∃ F : Ordinal.{0} → SkEnt, ∀ ℓ, SkLev ℓ → ℓ < Om1 * Om1 →
    SkAtW ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLev ℓ' → SkExtW2 (F ℓ') (F ℓ) :=
  ⟨Wm.wmF _ Wm.wmOm1Step_sq, Wm.wmFam_sq⟩

/-- STATUS: PROVED (Wo.wo_fs1, Wo.wo_seq_exp, Wo.wo_seq_term, Wo.wo_seq_pow)
SIZE: M
every level of the remaining case of Wm.WmOm1Step has an Ω₁-sequence of levels (gate-cofinal). -/
theorem skFs1 : ∀ ℓ, SkLev ℓ → ℓ ≠ Om1 → (¬ ∃ ℓ', Wm.WmLev ℓ' ∧ ℓ = ℓ' + Om1) → ¬ Wm.WmFs ℓ →
    ∃ s, Wo.WoFs1 ℓ s := fun _ hℓ h1 h2 h3 => Wo.wo_fs1 hℓ h1 h2 h3

/-- STATUS: PROVED (Wo.woStep_om1: Wo.woFamO, Ho.hoOU)
SIZE: L
the step at every level with an Ω₁-sequence of levels, on families over all raw data. -/
theorem skStepOm1Wo : ∀ ℓ s, Wo.WoFs1 ℓ s → Wo.WoStepAt ℓ := fun _ _ hs => Wo.woStep_om1 hs

/-- STATUS: PROVED (Wo.woStep_all: Wo.woStep_base, Wo.woStep_succ, Wo.woStep_fs, skFs1, skStepOm1Wo)
SIZE: M
the step at every level, on families over all raw data (no remaining case). -/
theorem skStepAllWo : ∀ ℓ, SkLev ℓ → Wo.WoStepAt ℓ := fun ℓ hℓ => Wo.woStep_all ℓ hℓ

/-- STATUS: PROVED (Wo.woFamW2: Wo.woFam, Wo.woEnt_at, Wo.woEnt_ext)
SIZE: M
the family on ALL levels below ε_{Ω₁+1}: every entry SkAtW, every pair SkExtW2 (the conclusion of Wm.wmFam at
ε_{Ω₁+1}, with no hypothesis). -/
theorem skFamW2 : ∃ F : Ordinal.{0} → SkEnt, ∀ ℓ, SkLev ℓ →
    SkAtW ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLev ℓ' → SkExtW2 (F ℓ') (F ℓ) :=
  ⟨Wo.woEnt, Wo.woFamW2⟩

/-- STATUS: PROVED (Wo.woVE_B, Wo.woVE_γ: the ω-chain Wo.woChE of the systems at Ω₁, Ω₁^{Ω₁}, …)
SIZE: M
the system over G at φ(ε_{Ω₁+1}, G+1), gate 1. -/
theorem skSysE : ∃ V : Hg.HgVD, V.B = veblen Gf.gfE (Gc.gcG 0 + 1) ∧ V.γ = 1 := ⟨Wo.woVE, rfl, rfl⟩

/-- STATUS: PROVED (Wo.woE_enum, Wo.woE_capV)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below skFE. -/
theorem skLocE (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → l < skFE S → SkUV S l := fun _ hr hl =>
  ⟨(Wo.woE_enum S hr hl).1, (Wo.woE_enum S hr hl).2, Wo.woE_capV S hr hl⟩

/-- STATUS: PROVED (Wo.woE_fr_order, skLocE)
SIZE: S
THE FRONTIER MOVES: the restarts in [skFHo, skFE) are settled, so UPPER / LOWER / CapV above skFE suffice. -/
theorem skHypIffE (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skFE S ≤ l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  rcases lt_or_ge l (skFE S) with h' | h'
  · exact skLocE S l hr h'
  · exact h l hr h'

/-- The frontier of round 119: `ι(Γ(φ(ε_{Ω₁+ω}, G+1))·ω)`. -/
noncomputable def skFW (S : InaccSeq.{0}) : Ordinal.{0} := Bt.iota S (Gc.gcG Ws.wsVw.B * ω)

/-- STATUS: PROVED (Ws.wsVw_B, Ws.wsVw_γK: the system of the generic (A2) family at the level ε_{Ω₁+ω})
SIZE: M
the system over G at φ(ε_{Ω₁+ω}, G+1), gate < K. -/
theorem skSysWV (S : InaccSeq.{0}) : ∃ V : Hg.HgVD, V.B = veblen Ws.wsLw (Gc.gcG 0 + 1) ∧ V.γ < Td.tdK S :=
  ⟨Ws.wsVw, Ws.wsVw_B, Ws.wsVw_γK S⟩

/-- STATUS: PROVED (Ws.wsW_enum, Ws.wsW_capV)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below skFW. -/
theorem skLocW (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → l < skFW S → SkUV S l := fun _ hr hl =>
  ⟨(Ws.wsW_enum S hr hl).1, (Ws.wsW_enum S hr hl).2, Ws.wsW_capV S hr hl⟩

/-- STATUS: PROVED (Ws.wsW_fr_order, skLocW, skHypIffE)
SIZE: S
THE FRONTIER MOVES: the restarts in [skFHo, skFW) are settled, so UPPER / LOWER / CapV above skFW suffice. -/
theorem skHypIffW (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skFW S ≤ l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  rcases lt_or_ge l (skFW S) with h' | h'
  · exact skLocW S l hr h'
  · exact h l hr h'

/-- The frontier of round 119 (leaf gam44, final): `ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)`. -/
noncomputable def skFZ (S : InaccSeq.{0}) : Ordinal.{0} := Bt.iota S (Gc.gcG Ws.wsVz.B * ω)

/-- STATUS: PROVED (Ws.wsVz_B, Ws.wsVz_γK: the system of the generic (A2) family at the level ζ_{Ω₁+1}, gate ≤ 1)
SIZE: M
the system over G at φ(ζ_{Ω₁+1}, G+1), gate < K. -/
theorem skSysZV (S : InaccSeq.{0}) : ∃ V : Hg.HgVD, V.B = veblen Ws.wsZ (Gc.gcG 0 + 1) ∧ V.γ < Td.tdK S :=
  ⟨Ws.wsVz, Ws.wsVz_B, Ws.wsVz_γK S⟩

/-- STATUS: PROVED (Ws.wsZ_enum, Ws.wsZ_capV)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below skFZ. -/
theorem skLocZ (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → l < skFZ S → SkUV S l := fun _ hr hl =>
  ⟨(Ws.wsZ_enum S hr hl).1, (Ws.wsZ_enum S hr hl).2, Ws.wsZ_capV S hr hl⟩

/-- STATUS: PROVED (Ws.wsZ_fr_order, skLocZ)
SIZE: S
THE FRONTIER MOVES: the restarts in [skFHo, skFZ) are settled, so UPPER / LOWER / CapV above skFZ suffice. -/
theorem skHypIffZ (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skFZ S ≤ l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  rcases lt_or_ge l (skFZ S) with h' | h'
  · exact skLocZ S l hr h'
  · exact h l hr h'

/-- The frontier of round 120 (leaf gam45): THE END OF (A2), `λ` past `ι(Γ(B)·ω)` for every `B < φ(G, 1)`. -/
def skPastA2 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Wx.WxPast S l

/-- STATUS: PROVED (Wx.wxSysA2 = Ws.wsSysA2_baseI S Wx.wx_baseI)
SIZE: M
REGION (A2), UNCONDITIONAL: every B < φ(G, 1) is ≤ the bound of a system over G with gate < K. -/
theorem skSysA2V (S : InaccSeq.{0}) : ∀ B, B < veblen (Gc.gcG 0) 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S :=
  Wx.wxSysA2 S

/-- STATUS: PROVED (Wx.wxA2_enum, Wx.wxA2_capV)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below the end of (A2). -/
theorem skLocA2 (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → ¬ skPastA2 S l → SkUV S l := fun _ hr hl => by
  have h := (not_congr (Wx.wx_past_iff S)).1 hl
  rw [not_not] at h
  exact ⟨(Wx.wxA2_enum S hr h).1, (Wx.wxA2_enum S hr h).2, Wx.wxA2_capV S hr h⟩

/-- STATUS: PROVED (Wx.wxFA2_cof, Wx.wxFA2_le)
SIZE: S
WHERE THE FRONTIER IS: past the end of (A2) ⇔ past every ι(Γ(φ(glBn n, G+1))·ω); each ι(Γ(B)·ω), B < φ(G, 1), is
≤ ι(Γ(φ(G, 1))). -/
theorem skFA2Where (S : InaccSeq.{0}) :
    (∀ l, skPastA2 S l ↔ ∀ n : ℕ, Bt.iota S (Gc.gcG (veblen (Gl.glBn n) (Gc.gcG 0 + 1)) * ω) ≤ l) ∧
    ∀ B, B < veblen (Gc.gcG 0) 1 → Bt.iota S (Gc.gcG B * ω) ≤ Bt.iota S (Gc.gcG (veblen (Gc.gcG 0) 1)) :=
  ⟨fun _ => Wx.wxFA2_cof S, fun _ hB => Wx.wxFA2_le S hB⟩

/-- STATUS: PROVED (skLocA2)
SIZE: S
THE FRONTIER MOVES TO THE END OF (A2): the restarts in [skFHo, F_{A2}) are settled, so UPPER / LOWER / CapV past
the end of (A2) suffice (road Wx.wxRoadA2, hypotheses equivalent to Ws.wsRoadZ's: Wx.wxRoadA2_hyp_iff). -/
theorem skHypIffA2 (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skPastA2 S l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  by_cases h' : skPastA2 S l
  · exact h l hr h'
  · exact skLocA2 S l hr h'

/-- The frontier of round 122 (leaf reg7): `λ` past `ι(Γ(φ(G, 1+ν))·ω)` for every `ν < Γ₀`. -/
def skPastG (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Xf.XfPast S l

/-- STATUS: PROVED (Xf.xf_notPast; round 122)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(φ(G, 1+ν))·ω)` for some `ν < Γ₀` (the systems `Xf.xfV ν`,
gate `≤ 1+ν < Γ₀ ≤ K`, located by `Hg.hgV_locD`). -/
theorem skLocG (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → ¬ skPastG S l → SkUV S l := fun _ hr h =>
  Xf.xf_notPast S hr h

/-- STATUS: PROVED (Xf.xf_past_A2, Xf.xf_FG_le; round 122)
SIZE: S
WHERE THE FRONTIER IS: past `F_G` ⇒ past the end of (A2); each `ι(Γ(φ(G, 1+ν))·ω)`, `ν < Γ₀`, is
`≤ ι(Γ(φ(G, Γ₀)))`. -/
theorem skFGWhere (S : InaccSeq.{0}) :
    (∀ l, skPastG S l → skPastA2 S l) ∧
    ∀ ν, ν < gamma 0 → Bt.iota S (Gc.gcG (veblen (Gc.gcG 0) (1 + ν)) * ω) ≤
      Bt.iota S (Gc.gcG (veblen (Gc.gcG 0) (gamma 0))) :=
  ⟨fun _ h => Xf.xf_past_A2 S h, fun _ hν => Xf.xf_FG_le S hν⟩

/-- STATUS: PROVED (skLocG; round 122)
SIZE: S
THE FRONTIER MOVES PAST `φ(G, 1)`: UPPER / LOWER / CapV past `F_G` suffice (road `Xf.xfRoad`, hypotheses equivalent
to those of `Xb.xbRoadZ`: `Xf.xfRoad_hyp_iff`). -/
theorem skHypIffG (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skPastG S l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  by_cases h' : skPastG S l
  · exact h l hr h'
  · exact skLocG S l hr h'

/-- The frontier of round 123 (leaf reg8): `λ` past `ι(Γ(φ(G+1, 0))·ω)` (the top of the level `G`). -/
def skPastGT (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Xl.XlPast S l

/-- STATUS: PROVED (Xl.xl_notPast; round 123)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(φ(G+1, 0))·ω)` (the system `Xl.xlTop`, gate `1 < K`,
located by `Hg.hgV_locD`). -/
theorem skLocGT (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → ¬ skPastGT S l → SkUV S l := fun _ hr h =>
  Xl.xl_notPast S hr h

/-- STATUS: PROVED (Xl.xl_past_xf, Xl.xl_loc; round 123)
SIZE: S
WHERE THE FRONTIER IS: past `ι(Γ(φ(G+1, 0))·ω)` ⇒ past `F_G`; `ι(Γ(φ(G+1, 0))·ω)` is itself the located `Λ⁺` of a
system, with `P(…) < L(0)`. -/
theorem skFGTWhere (S : InaccSeq.{0}) :
    (∀ l, skPastGT S l → skPastG S l) ∧
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = Bt.iota S (Gc.gcG (veblen (Gc.gcG 0 + 1) 0) * ω) ∧
      Nm.Pv S (Gc.gcG (veblen (Gc.gcG 0 + 1) 0) * ω) < Nc.ncL S 0 := by
  refine ⟨fun _ h => Xl.xl_past_xf S h, ?_⟩
  obtain ⟨X, h1, h2, -, h4⟩ := Xl.xl_loc S
  exact ⟨X, h1, h2, h4⟩

/-- STATUS: PROVED (skLocGT; round 123)
SIZE: S
THE FRONTIER MOVES TO `ι(Γ(φ(G+1, 0))·ω)`: UPPER / LOWER / CapV past it suffice (road `Xl.xlRoad`, hypotheses
equivalent to those of `Xf.xfRoad`: `Xl.xlRoad_hyp_iff`). -/
theorem skHypIffGT (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skPastGT S l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  by_cases h' : skPastGT S l
  · exact h l hr h'
  · exact skLocGT S l hr h'

/-- The frontier of round 123 after the level `G + Ω₁`: `λ` past `ι(Γ(φ(G + Ω₁, 0))·ω)`. -/
def skPastGW (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Xl.XlWPast S l

/-- STATUS: PROVED (Xl.xlw_notPast; round 123)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(φ(G + Ω₁, 0))·ω)` (the system `Xl.xlW`, gate `1 < K`). -/
theorem skLocGW (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → ¬ skPastGW S l → SkUV S l := fun _ hr h =>
  Xl.xlw_notPast S hr h

/-- STATUS: PROVED (Xl.xlw_past_k, Xl.xlk_past_xl, Xl.xlw_loc; round 123)
SIZE: S
WHERE THE FRONTIER IS: past `ι(Γ(φ(G + Ω₁, 0))·ω)` ⇒ past `ι(Γ(φ(G+1, 0))·ω)` ⇒ past `F_G`; the new frontier is the
located `Λ⁺` of a system, with `P(…) < L(0)`. -/
theorem skFGWWhere (S : InaccSeq.{0}) :
    (∀ l, skPastGW S l → skPastGT S l) ∧
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = Bt.iota S (Gc.gcG (veblen (Gc.gcG 0 + Om1) 0) * ω) ∧
      Nm.Pv S (Gc.gcG (veblen (Gc.gcG 0 + Om1) 0) * ω) < Nc.ncL S 0 := by
  refine ⟨fun _ h => Xl.xlk_past_xl S (Xl.xlw_past_k S h), ?_⟩
  obtain ⟨X, h1, h2, -, h4⟩ := Xl.xlw_loc S
  exact ⟨X, h1, h2, h4⟩

/-- STATUS: PROVED (skLocGW; round 123)
SIZE: S
THE FRONTIER MOVES TO `ι(Γ(φ(G + Ω₁, 0))·ω)`: UPPER / LOWER / CapV past it suffice (road `Xl.xlwRoad`, hypotheses
equivalent to those of `Xf.xfRoad`: `Xl.xlwRoad_hyp_iff`, `Xl.xlkRoad_hyp_iff`, `Xl.xlRoad_hyp_iff`). -/
theorem skHypIffGW (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skPastGW S l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  by_cases h' : skPastGW S l
  · exact h l hr h'
  · exact skLocGW S l hr h'

/-- STATUS: PROVED (definition; round 124)
SIZE: S
`l` lies past the frontier `ι(Γ(φ(t₀, G+1))·ω)` (`Xp.XpT0Past`, `t₀ = ε_{G+1}`). -/
def skPastT0 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := Xp.XpT0Past S l

/-- STATUS: PROVED (Xp.xpT0_notPast; round 124)
SIZE: S
UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(φ(t₀, G+1))·ω)` (the system `Xp.xpV1`, gate `1 < K`). -/
theorem skLocT0 (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → ¬ skPastT0 S l → SkUV S l := fun _ hr h =>
  Xp.xpT0_notPast S hr h

/-- STATUS: PROVED (Xp.xpT0_past_W, Xp.xpT0_loc; round 124)
SIZE: S
WHERE THE FRONTIER IS: past `ι(Γ(φ(t₀, G+1))·ω)` ⇒ past `ι(Γ(φ(G + Ω₁, 0))·ω)`; the new frontier is the located
`Λ⁺` of a system, with `P(…) < L(0)`. -/
theorem skFT0Where (S : InaccSeq.{0}) :
    (∀ l, skPastT0 S l → skPastGW S l) ∧
    ∃ X : Xt.XtSys, Xt.XtTopPkg X ∧ Xt.xtB1 X = Bt.iota S (Gc.gcG (veblen (Wj.wjT 0) (Gc.gcG 0 + 1)) * ω) ∧
      Nm.Pv S (Gc.gcG (veblen (Wj.wjT 0) (Gc.gcG 0 + 1)) * ω) < Nc.ncL S 0 := by
  refine ⟨fun _ h => Xp.xpT0_past_W S h, ?_⟩
  obtain ⟨X, h1, h2, -, h4⟩ := Xp.xpT0_loc S
  exact ⟨X, h1, h2, h4⟩

/-- STATUS: PROVED (skLocT0; round 124)
SIZE: S
THE FRONTIER MOVES TO `ι(Γ(φ(t₀, G+1))·ω)`: UPPER / LOWER / CapV past it suffice (`Xp.xpT0Hyp_iff`: equivalent to
the hypotheses of `Xl.xlwRoadZ`). -/
theorem skHypIffT0 (S : InaccSeq.{0}) (h : ∀ l, Cd.CdRange S l → skPastT0 S l → SkUV S l) :
    ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := fun l hr _ => by
  by_cases h' : skPastT0 S l
  · exact h l hr h'
  · exact skLocT0 S l hr h'


/-! ## (A2) and (A3): the level codes past `ε_{Ω₁+1}` (round 116, leaf reg1)

The old cut `φ(G, G+1)` between (A2) and (A3) is not where the level codes change: the levels `ℓ < G` give
`sup_{ℓ<G} φ(ℓ, G+1) = φ(G, 1)` (`Wj.wjA2Cof`), so (A2) is `[φ(E, G+1), φ(G, 1))` and the levels `ℓ > G`
(`Wj.wjT n`, cofinal in `Γ(1)`, `Wj.wjA3Cof`) cover everything from `φ(G, 1)` to `Γ(1)`.

(A2) LEVEL-CODE TYPE: `ℓ = Ω₁^{e₁}·c₁ + … + Ω₁^{e_k}·c_k` (`Ω₁ ∣ ℓ`, `Ω₁ ≤ ℓ < G`), coefficients `0 < cᵢ < Ω₁`,
exponents `eᵢ < G` codes of the same kind, an exponent `≥ ε_{Ω₁+1}` being a Veblen node `φ(a, b)` (then
`Ω₁^{φ(a,b)} = φ(a, b)`), all hereditary countable leaves below the gate `Gl.glG ℓ`; reading `Gl.glR ℓ x`
(`Ω₁ ↦ x`, `= Gf.rdc ℓ x` below `ε_{Ω₁+1}`).  The gam41 induction extends verbatim with `(SkLev, rdc, gtc)`
replaced by `(SkLevG, glR, glG)`; on `ℓ < ε_{Ω₁+1}` the two agree (`skAtG_iff`).
(A3) LEVEL-CODE TYPE: the same normal forms with exponents over the atoms `{Ω₁, G}` (`G ↦ Γ_{x+1}`); readings
reach `ε_{Γ_{x+1}+1} > Γ_{x+1}`, so `Hn.HnLv` (field `l_lt : l x < Γ_{x+1}`) cannot carry them. -/

/-- The level codes of (A2): `Ω₁ ≤ ℓ`, `Ω₁ ∣ ℓ`, `ℓ < G`. -/
def SkLevG (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < Gc.gcG 0

/-- The entry `E` sits at the level `ℓ` (reading `Gl.glR`, gate `Gl.glG`). -/
def SkAtG (ℓ : Ordinal.{0}) (E : SkEnt) : Prop :=
  E.1.Λ.L = ℓ ∧ (∀ x, InE x → x < Om1 → E.1.Λ.g < x → E.1.Λ.l x = Gl.glR ℓ x) ∧
    E.2.down.B = veblen ℓ (Gc.gcG 0 + 1) ∧ E.2.down.γ ≤ Gl.glG ℓ

def SkCohG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkAtG ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLevG ℓ'' → SkLevG ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

def SkStepAtG (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCohG ℓ f → ∃ E, SkAtG ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkExt (f ℓ' h) E

def ShSuccG (ℓ : Ordinal.{0}) : Prop := ∃ ℓ', SkLevG ℓ' ∧ ℓ = ℓ' + Om1

def SkDigitGateG : Prop :=
  ∀ Z, SC Z → Z ≤ Om 1 → ∀ y, Mx.GxCl Z {Gc.gcG 0} y → y < Gc.gcG 0 → Gl.glG y < Z

def SkReadExactG : Prop :=
  ∀ ℓ σ ρ, SkLevG ℓ → Bases σ ρ → Gl.glG ℓ < σ → Gl.glR ℓ ρ ∈ TB ρ σ ∧ pi σ ρ (Gl.glR ℓ ρ) = Gl.glR ℓ σ

def SkLvDatumAllG : Prop :=
  ∀ ℓ, SkLevG ℓ → ∃ Λ : Hn.HnLv, Λ.L = ℓ ∧ Λ.g ≤ Gl.glG ℓ ∧
    ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = Gl.glR ℓ x

/-- STATUS: PROVED (Gl.glR_low, Gl.glG_low)
SIZE: S
ℓ < ε_{Ω₁+1}: SkAtG ℓ E ⇔ SkAt ℓ E (the A2 family restricts to the A1 family). -/
theorem skAtG_iff {ℓ : Ordinal.{0}} (hℓ : ℓ < Gf.gfE) (E : SkEnt) : SkAtG ℓ E ↔ SkAt ℓ E := by
  unfold SkAtG SkAt
  rw [Gl.glG_low hℓ]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun x a b c => by rw [h2 x a b c, Gl.glR_low hℓ], h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun x a b c => by rw [h2 x a b c, Gl.glR_low hℓ], h3, h4⟩

/-- STATUS: PROVED (Wj.wjDigitGateG)
SIZE: S
SC Z ≤ Ω₁, y < G a code over Z with the atom G ⇒ glG y < Z (digit gate on all of [0, G)). -/
theorem skDigitGateG : SkDigitGateG := Wj.wjDigitGateG

/-- STATUS: PROVED (Wj.wjReadExactG)
SIZE: S
∀ ℓ < G, glG ℓ < σ: glR ℓ ρ ∈ Tᵖ[σ] ∧ π(glR ℓ ρ) = glR ℓ σ. -/
theorem skReadExactG : SkReadExactG := fun ℓ _ _ hℓ hB hg => Wj.wjReadExactG ℓ _ _ hℓ.2.2 hB hg

/-- STATUS: PROVED (Wn.wnLvDatumAll; the level datum Wn.wnLv ℓ, gate = glG ℓ; the hypotheses are not needed)
SIZE: S
digit gate ∧ EXACT ⇒ level datum at every A2 level (port of skLvOfGate: (rdc, gtc) ↦ (glR, glG); HnLv allows
L < G, l x < Γ_{x+1}). -/
theorem skLvOfGateG : SkDigitGateG → SkReadExactG → SkLvDatumAllG := fun _ _ => Wn.wnLvDatumAll

/-- STATUS: PROVED (skLvOfGateG, skDigitGateG, skReadExactG)
SIZE: S -/
theorem skLvDatumG : SkLvDatumAllG := skLvOfGateG skDigitGateG skReadExactG

/-- STATUS: PROVED (Wn.wnShape)
SIZE: S
Cantor normal form in base Ω₁ (no use of the bound): ℓ = Ω₁ ∨ succ ∨ pow ∨ exp-limit ∨ coefficient-limit. -/
theorem skShapeG : ∀ ℓ, SkLevG ℓ → ℓ = Om1 ∨ ShSuccG ℓ ∨ ShPow ℓ ∨ ShExpLim ℓ ∨ ShCoefLim ℓ :=
  fun ℓ h => Wn.wnShape ℓ h.1 h.2.1 h.2.2

/-- STATUS: REDUCED (skStepBase)
SIZE: S
the entry at ℓ = Ω₁ (both families are vacuous below Ω₁; skAtG_iff at Ω₁). -/
theorem skStepBaseG : SkStepAtG Om1 := by
  intro f _
  have hOE : (Om1 : Ordinal.{0}) < Gf.gfE := Gf.Om1_lt_eW
  have hf' : SkCoh Om1 (fun ℓ' h => f ℓ' h) :=
    ⟨fun _ h h' => absurd h'.1 (not_le.2 h), fun _ _ _ h' _ _ h2 => absurd h2.1 (not_le.2 h')⟩
  obtain ⟨E, hE, -⟩ := skStepBase _ hf'
  exact ⟨E, (skAtG_iff hOE E).2 hE, fun _ h h' => absurd h'.1 (not_le.2 h)⟩

/-- STATUS: REPLACED (by skStepSuccWG: SkAtG, like SkAt, has no start condition of the system over G at the package,
so the step would have to extend an ARBITRARY digit system; NO EVIDENCE against)
SIZE: M
ℓ = ℓ' + Ω₁ (skStepSucc's proof with (rdc, gtc, ε_{Ω₁+1}) ↦ (glR, glG, G)). -/
theorem skStepSuccG (hLv : SkLvDatumAllG) : ∀ ℓ, SkLevG ℓ → ShSuccG ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepPowWG; same reason as skStepSuccG)
SIZE: M
ℓ = P + Ω₁^{e+1} (skStepPow's proof, same substitution). -/
theorem skStepPowG (hLv : SkLvDatumAllG) : ∀ ℓ, SkLevG ℓ → ShPow ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepCoefLimWG; same reason as skStepSuccG)
SIZE: M
ℓ = P + Ω₁^e·c, c < Ω₁ limit (skStepCoefLim's proof, same substitution). -/
theorem skStepCoefLimG (hLv : SkLvDatumAllG) : ∀ ℓ, SkLevG ℓ → ShCoefLim ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepExpLimWG; same reason as skStepSuccG)
SIZE: M
ℓ = P + Ω₁^e, e limit; NEW cases e = φ(a, b) ≥ ε_{Ω₁+1} (Ω₁^e = e): the union along the Veblen fundamental
sequence read by glR (b limit: over b' < b; b = b'+1 or 0 with a = a'+1: ω-chain of φ(a', ·)-iterates;
a limit: over a' < a; cofinality ω or Ω₁; codes Gl.glCfn). -/
theorem skStepExpLimG (hLv : SkLvDatumAllG) (hG : SkDigitGateG) : ∀ ℓ, SkLevG ℓ → ShExpLim ℓ → SkStepAtG ℓ := by
  sorry

/-- STATUS: REPLACED (by skStepWG; it rests on the REPLACED SkAtG steps)
SIZE: M -/
theorem skStepG : ∀ ℓ, SkLevG ℓ → SkStepAtG ℓ := by
  intro ℓ hℓ
  rcases skShapeG ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBaseG
  · exact skStepSuccG skLvDatumG ℓ hℓ h
  · exact skStepPowG skLvDatumG ℓ hℓ h
  · exact skStepExpLimG skLvDatumG skDigitGateG ℓ hℓ h
  · exact skStepCoefLimG skLvDatumG ℓ hℓ h

noncomputable def skGG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : SkEnt := by
  classical
  exact if h : SkLevG ℓ ∧ SkCohG ℓ f then Classical.choose (skStepG ℓ h.1 f h.2) else (Hn.hnPk1, ULift.up Ho.hoUf)

noncomputable def skFG : Ordinal.{0} → SkEnt := Ordinal.lt_wf.fix skGG

/-- STATUS: REPLACED (by skFamWG; it rests on skStepG)
SIZE: M
one generic induction over every level ℓ < G (gam41's skFam with SkLev ↦ SkLevG). -/
theorem skFamG : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLevG ℓ → SkAtG ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLevG ℓ' → SkExt (F ℓ') (F ℓ) := by
  refine ⟨skFG, fun ℓ => ?_⟩
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : SkCohG ℓ (fun ℓ' _ => skFG ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : skFG ℓ = skGG ℓ (fun ℓ' _ => skFG ℓ') := Ordinal.lt_wf.fix_eq skGG ℓ
    have hsp := Classical.choose_spec (skStepG ℓ hℓ (fun ℓ' _ => skFG ℓ') hcoh)
    have hG : skGG ℓ (fun ℓ' _ => skFG ℓ') = Classical.choose (skStepG ℓ hℓ (fun ℓ' _ => skFG ℓ') hcoh) := by
      unfold skGG; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-! ### The (A2) induction on the corrected entry predicate `SkAtWG` (round 117, leaf reg2) -/

/-- The corrected (A2) entry predicate: `Wn.WnAt` (package at `ℓ` read `glR ℓ x`, gate `≤ glG ℓ`, every
`ε`-number above the gate is above `glG ℓ`, the system is a start over `G` at the package for the base `Wn.wnGW`). -/
def SkAtWG (ℓ : Ordinal.{0}) (E : SkEnt) : Prop := Wn.WnAt ℓ E.1 E.2.down

def SkCohWG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop :=
  (∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkAtWG ℓ' (f ℓ' h)) ∧
    ∀ ℓ'' ℓ' (h'' : ℓ'' < ℓ) (h' : ℓ' < ℓ), ℓ'' < ℓ' → SkLevG ℓ'' → SkLevG ℓ' → SkExt (f ℓ'' h'') (f ℓ' h')

def SkStepAtWG (ℓ : Ordinal.{0}) : Prop :=
  ∀ f, SkCohWG ℓ f → ∃ E, SkAtWG ℓ E ∧ ∀ ℓ' (h : ℓ' < ℓ), SkLevG ℓ' → SkExt (f ℓ' h) E

/-- STATUS: PROVED (definitions)
SIZE: S
SkAtWG ℓ E ⇒ SkAtG ℓ E (the corrected entry is an entry of reg1's family). -/
theorem skAtWG_G {ℓ : Ordinal.{0}} {E : SkEnt} (h : SkAtWG ℓ E) : SkAtG ℓ E :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- STATUS: PROVED (Wn.wnAt_base)
SIZE: S
the entry at ℓ = Ω₁ for SkAtWG: Hn.hnPk1 and Hg.hgU (Hg.hgU is a start over Wn.wnGW Hn.hnL1, Wn.wnU_shape). -/
theorem skStepBaseWG : SkStepAtWG Om1 := fun _ _ =>
  ⟨(Hn.hnPk1, ULift.up Hg.hgU), Wn.wnAt_base, fun _ h hl => absurd hl.1 (not_le.2 h)⟩

/-- STATUS: PROVED (Wn.wnSucc_at, Wn.wnSucc_ext, Wn.wnSucc_ext_lt)
SIZE: M
ℓ = ℓ' + Ω₁ < G: package Hn.HnPk.succ, G-system = the union over G (Wn.wnGW) started at the system at ℓ'. -/
theorem skStepSuccWG : ∀ ℓ, SkLevG ℓ → ShSuccG ℓ → SkStepAtWG ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩ f ⟨hat, hext⟩
  have hlt : ℓ' < ℓ' + Om1 := lt_add_of_pos_right _ Wh.wh_Om1_pos
  have hat' := hat ℓ' hlt hℓ'
  refine ⟨((f ℓ' hlt).1.succ, ULift.up (Wn.wnSuccV hat')), Wn.wnSucc_at hℓ'.2.1 hℓ'.2.2 hat',
    fun ℓ'' h'' hℓ'' => ?_⟩
  have hle : ℓ'' ≤ ℓ' := not_lt.1 fun h => absurd h'' (not_lt.2 (Wh.wh_lev_succ_le hℓ'.2.1 hℓ''.2.1 h))
  rcases hle.lt_or_eq with hl | rfl
  · exact Wn.wnSucc_ext_lt hℓ'.2.1 hℓ'.2.2 hat' hl hℓ''.2.1 (hat ℓ'' h'' hℓ'') (hext ℓ'' ℓ' h'' hlt hl hℓ'' hℓ')
  · exact Wn.wnSucc_ext hat'

/-- STATUS: REPLACED (round 118: by skStepOm1WG2 on the corrected coherence SkCohWG2; on SkCohWG the package relation
Hn.HnkExt is vacuous across a gate drop (skGateDropG), so a union cannot be shown to extend every member)
SIZE: M
ℓ = P + Ω₁^{e+1} < G, for SkAtWG (gam41's skStepPowW with (rdc, gtc, whGW) ↦ (glR, glG, wnGW); the union over
the prefixes P + Ω₁^e·v, v < Ω₁, uses the gate-lowering extension of leaf gam42 (round 117)). -/
theorem skStepPowWG : ∀ ℓ, SkLevG ℓ → ShPow ℓ → SkStepAtWG ℓ := by
  sorry

/-- STATUS: REPLACED (round 118: by skStepCoefLimWG2, PROVED on SkCohWG2; same reason as skStepPowWG)
SIZE: M
ℓ = P + Ω₁^e·c < G, c < Ω₁ limit, for SkAtWG (gam41's skStepCoefLimW, same substitution; gam42's extension). -/
theorem skStepCoefLimWG : ∀ ℓ, SkLevG ℓ → ShCoefLim ℓ → SkStepAtWG ℓ := by
  sorry

/-- STATUS: REPLACED (round 118: by skStepExpLimFsWG2 (PROVED, gated ω-sequence) and skStepOm1WG2 on SkCohWG2)
SIZE: M
ℓ = P + Ω₁^e < G, e limit, for SkAtWG; besides gam41's cases the exponents e = φ(a, b) ≥ ε_{Ω₁+1} (Ω₁^e = e):
the union along the Veblen fundamental sequence read by glR (cofinality ω or Ω₁; codes Gl.glCfn). -/
theorem skStepExpLimWG : ∀ ℓ, SkLevG ℓ → ShExpLim ℓ → SkStepAtWG ℓ := by
  sorry

/-- STATUS: REPLACED (round 118: by skStepWG2; it rests on the REPLACED SkCohWG leaves)
SIZE: M -/
theorem skStepWG : ∀ ℓ, SkLevG ℓ → SkStepAtWG ℓ := by
  intro ℓ hℓ
  rcases skShapeG ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBaseWG
  · exact skStepSuccWG ℓ hℓ h
  · exact skStepPowWG ℓ hℓ h
  · exact skStepExpLimWG ℓ hℓ h
  · exact skStepCoefLimWG ℓ hℓ h

noncomputable def skGWG (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : SkEnt := by
  classical
  exact if h : SkLevG ℓ ∧ SkCohWG ℓ f then Classical.choose (skStepWG ℓ h.1 f h.2) else (Hn.hnPk1, ULift.up Ho.hoUf)

noncomputable def skFWG : Ordinal.{0} → SkEnt := Ordinal.lt_wf.fix skGWG

/-- STATUS: REPLACED (round 118: by skFamWG2 on SkCohWG2; it rests on skStepWG)
SIZE: M
one generic induction over every level ℓ < G on SkAtWG. -/
theorem skFamWG : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLevG ℓ → SkAtWG ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLevG ℓ' → SkExt (F ℓ') (F ℓ) := by
  refine ⟨skFWG, fun ℓ => ?_⟩
  induction ℓ using WellFoundedLT.induction with
  | _ ℓ ih =>
    intro hℓ
    have hcoh : SkCohWG ℓ (fun ℓ' _ => skFWG ℓ') :=
      ⟨fun ℓ' h h' => (ih ℓ' h h').1, fun ℓ'' ℓ' _ h' hlt h1 h2 => (ih ℓ' h' h2).2 ℓ'' hlt h1⟩
    have heq : skFWG ℓ = skGWG ℓ (fun ℓ' _ => skFWG ℓ') := Ordinal.lt_wf.fix_eq skGWG ℓ
    have hsp := Classical.choose_spec (skStepWG ℓ hℓ (fun ℓ' _ => skFWG ℓ') hcoh)
    have hG : skGWG ℓ (fun ℓ' _ => skFWG ℓ') = Classical.choose (skStepWG ℓ hℓ (fun ℓ' _ => skFWG ℓ') hcoh) := by
      unfold skGWG; rw [dif_pos ⟨hℓ, hcoh⟩]
    rw [heq, hG]
    exact ⟨hsp.1, fun ℓ' h h' => hsp.2 ℓ' h h'⟩

/-! ### (A2) on the corrected coherence (round 118, leaf reg3, modules `R2.Wp*`) -/

/-- The corrected (A2) coherence: entries `Wn.WnAt`, relation `Wm.WmExtE` (= `Wp.WpCoh`). -/
def SkCohWG2 (ℓ : Ordinal.{0}) (f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt) : Prop := Wp.WpCoh ℓ f

/-- The (A2) step at `ℓ` on the corrected coherence (= `Wp.WpStepAt`). -/
def SkStepAtWG2 (ℓ : Ordinal.{0}) : Prop := Wp.WpStepAt ℓ

/-- STATUS: PROVED (Wp.wp_gate_drop)
SIZE: S
REFUTE-FIRST of the old (A2) leaves: a gate drop between (A2) levels: Ω₁·ω < Ω₁², glG(Ω₁²) = 2 < ω = glG(Ω₁·ω)
(so Hn.HnkExt, hence SkCohWG, says nothing between them: Wm.wm_old_vacuous). -/
theorem skGateDropG : SkLevG (Om1 * ω) ∧ SkLevG (Om1 * Om1) ∧ Om1 * ω < Om1 * Om1 ∧
    Gl.glG (Om1 * Om1) < Gl.glG (Om1 * ω) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Wp.wp_gate_drop
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4, h5]; exact natCast_lt_omega0 2

/-- STATUS: PROVED (Wp.wpCoh_old, Wm.wmExtE_old)
SIZE: S
SkCohWG2 ⇒ SkCohWG (the corrected coherence is stronger). -/
theorem skCohWG2_old {ℓ : Ordinal.{0}} {f : ∀ ℓ' : Ordinal.{0}, ℓ' < ℓ → SkEnt} (h : SkCohWG2 ℓ f) :
    SkCohWG ℓ f :=
  ⟨h.1, fun a b ha hb hab h1 h2 => Wm.wmExtE_old (h.2 a b ha hb hab h1 h2)⟩

/-- STATUS: PROVED (Wp.wpStep_base: Wn.wnAt_base)
SIZE: S -/
theorem skStepBaseWG2 : SkStepAtWG2 Om1 := Wp.wpStep_base

/-- STATUS: PROVED (Wp.wpStep_succ: Wn.wnSucc_at, Wn.wnSucc_ext(_lt), Wp.wpSucc_ext_lt, Wm.wmSucc_ext)
SIZE: M
ℓ = ℓ' + Ω₁ < G on SkCohWG2. -/
theorem skStepSuccWG2 : ∀ ℓ, SkLevG ℓ → ShSuccG ℓ → SkStepAtWG2 ℓ := by
  rintro ℓ hℓ ⟨ℓ', hℓ', rfl⟩
  exact Wp.wpStep_succ hℓ' hℓ.2.2

/-- STATUS: PROVED (Wp.wpStep_fs: Wp.WpLim — the limit package Wm.wmPkL of the sequence below Wn.wnLv ℓ and the gated
ω-chain union of the systems over G for the base Wn.wnGW; Wp.WpLim.at_lim, Wp.WpLim.ext_below)
SIZE: M
every (A2) level with an ω-sequence of levels (cofinal with room for +1, gates glG ℓ_k ≤ glG ℓ), on SkCohWG2. -/
theorem skStepFsWG2 : ∀ ℓ, SkLevG ℓ → Wp.WpFs ℓ → SkStepAtWG2 ℓ := fun _ hℓ h => Wp.wpStep_fs hℓ h

/-- STATUS: PROVED (Wp.wpStep_coef, Wp.wpFs_coef, Wp.wp_glG_coef: glG(A + Ω₁^e·c') ≤ glG(A + Ω₁^e·c) for
0 < c' ≤ c < Ω₁, Ω₁^{e+1} ∣ A, through Gl.glG_cnf)
SIZE: M
ℓ = P + Ω₁^e·c < G, c < Ω₁ limit, on SkCohWG2, UNCONDITIONAL. -/
theorem skStepCoefLimWG2 : ∀ ℓ, SkLevG ℓ → ShCoefLim ℓ → SkStepAtWG2 ℓ := by
  rintro ℓ hℓ ⟨P, e, c, he, hc, hcO, hP, rfl⟩
  exact Wp.wpStep_coef he hc hcO hP hℓ

/-- STATUS: PROVED (Wp.wpStep_fs; below ε_{Ω₁+1} the sequence comes from Wm.wmFs_exp via Wp.wpFs_of_wm)
SIZE: S
ℓ = P + Ω₁^e < G, e limit, with a gated ω-sequence of levels, on SkCohWG2. -/
theorem skStepExpLimFsWG2 : ∀ ℓ, SkLevG ℓ → ShExpLim ℓ → Wp.WpFs ℓ → SkStepAtWG2 ℓ :=
  fun _ hℓ _ h => Wp.wpStep_fs hℓ h

/-- STATUS: PROVED (Wp.wpStep_Bn, Wp.wpFs_Bn: the codes Gl.glCfn n k, gate 0)
SIZE: S
the step at every cofinal level glBn n of (A2), on SkCohWG2. -/
theorem skStepBnWG2 : ∀ n : ℕ, SkStepAtWG2 (Gl.glBn n) := Wp.wpStep_Bn

/-- STATUS: REPLACED (round 119: by the family over raw data for the code interface Ws.wsA2 (Ws.wsFam), whose only
remaining hypothesis is the arithmetic leaf skBaseA2; this node asks the step for ARBITRARY coherent families, and its
remaining case contains ε_{Ω₁+1}, which has no gated sequence at all (skGlGNoFsE); not proved, not needed)
SIZE: L
THE ONE REMAINING STEP OF (A2): every level ℓ < G that is not Ω₁, not ℓ' + Ω₁ and has no gated ω-sequence
(cofinality Ω₁: P + Ω₁^{e+1}, P + Ω₁^e with e of cofinality Ω₁, incl. the (A1) levels of skStepOm1W2), on SkCohWG2.
The same generic recursion as skStepOm1W2 with (rdc, gtc, whGW) ↦ (glR, glG, wnGW).  REFUTE FIRST: NO EVIDENCE
(no no-go result mentions packages, pseudo-bases or systems over G); non-vacuous: empty below Ω₁² (Wp.wpOm1Step_sq). -/
theorem skStepOm1WG2 : Wp.WpOm1Step (Gc.gcG 0) := by
  sorry

/-- STATUS: REPLACED (round 119: rests on the REPLACED skStepOm1WG2; not used)
SIZE: M
the step at every (A2) level on SkCohWG2. -/
theorem skStepWG2 : ∀ ℓ, SkLevG ℓ → SkStepAtWG2 ℓ := fun ℓ hℓ => Wp.wpStep_all skStepOm1WG2 ℓ hℓ hℓ.2.2

/-- STATUS: REPLACED (round 119: rests on the REPLACED skStepOm1WG2; the generic family Ws.wsFam replaces it)
SIZE: M
one generic induction over every level ℓ < G on SkCohWG2. -/
theorem skFamWG2 : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLevG ℓ → SkAtWG ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLevG ℓ' → SkExtW2 (F ℓ') (F ℓ) :=
  ⟨Wp.wpF _ skStepOm1WG2, fun ℓ hℓ => Wp.wpFam skStepOm1WG2 ℓ hℓ hℓ.2.2⟩

/-- STATUS: PROVED (Wp.wpFam_sq, Wp.wpOm1Step_sq)
SIZE: M
NON-VACUITY of SkCohWG2: a family on all (A2) levels below Ω₁², every entry SkAtWG, every pair SkExtW2, with no
hypothesis. -/
theorem skFamSqG : ∃ F : Ordinal.{0} → SkEnt, ∀ ℓ, SkLevG ℓ → ℓ < Om1 * Om1 →
    SkAtWG ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLevG ℓ' → SkExtW2 (F ℓ') (F ℓ) :=
  ⟨Wp.wpF _ Wp.wpOm1Step_sq, Wp.wpFam_sq⟩

/-- STATUS: REPLACED (round 119: by skSysAllG2, gate ≤ Ws.gh ℓ = max 1 (glG ℓ); at ℓ = ε_{Ω₁+1} the families give
gate 1 > glG ℓ = 0; only γ < K is used downstream)
SIZE: M -/
theorem skSysAllG : ∀ ℓ, SkLevG ℓ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Gl.glG ℓ := by
  intro ℓ hℓ
  obtain ⟨F, hF⟩ := skFamWG2
  exact ⟨(F ℓ).2.down, (hF ℓ hℓ).1.2.2.1, (hF ℓ hℓ).1.2.2.2.1⟩

/-- STATUS: PROVED (Gl.glBn_spec, Gf.Om1_lt_eW, Rj.rj_Om1_inE)
SIZE: S
the cofinal levels glBn n (glBn 0 = φ(ω, Ω₁+1), glBn (n+1) = φ(glBn n, 0)) are A2 level codes. -/
theorem skLevG_Bn (n : ℕ) : SkLevG (Gl.glBn n) := by
  obtain ⟨hlt, hE, hInE, -⟩ := Gl.glBn_spec n
  have hO : (Om1 : Ordinal.{0}) ≤ Gl.glBn n := (Gf.Om1_lt_eW.trans hE).le
  refine ⟨hO, ?_, hlt⟩
  have h := opow_dvd_opow ω hO
  rwa [Rj.rj_Om1_inE, hInE] at h

/-- STATUS: PROVED (Wn.wnGateBnK: glBn n is a code over Γ₀ with the atom G, so glG (glBn n) < Γ₀ ≤ K)
SIZE: S
the gate of the cofinal levels is small: glG (glBn n) < K. -/
theorem skGateBn (S : InaccSeq.{0}) : ∀ n, Gl.glG (Gl.glBn n) < Td.tdK S := Wn.wnGateBnK S

/-- STATUS: PROVED (Ws.wsStep_om1: the Ho.hoOU union of the entries at an Ω₁-sequence of levels, for EVERY code
interface Ws.WsC; R2.Wo's step with surjectivity of rdc replaced by cofinality of the reading)
SIZE: L
THE Ω₁-COFINAL STEP, GENERIC in the level and in the code interface. -/
theorem skStepOm1Ws : ∀ (C : Ws.WsC) (ℓ : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}), C.Fs1 ℓ s →
    Ws.WsStepAt C ℓ := fun _ _ _ hs => Ws.wsStep_om1 hs

/-- STATUS: PROVED (Ws.wsA1_step_om1: the (A1) instance Ws.wsA1 of the interface)
SIZE: S
CHECK: Wo.woStep_om1 reproved from the generic step. -/
theorem skA1Check : ∀ ℓ s, Wo.WoFs1 ℓ s → Wo.WoStepAt ℓ := fun _ _ hs => Ws.wsA1_step_om1 hs

/-- STATUS: PROVED (Ws.wsA1_sysA1: the generic family Ws.wsF of Ws.wsA1, Wh.whCofLev)
SIZE: S
CHECK: Wo.woSysA1 (region A1) reproved from the generic family. -/
theorem skA1SysCheck (S : InaccSeq.{0}) : ∀ B, B < veblen Gf.gfE (Gc.gcG 0 + 1) →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := Ws.wsA1_sysA1 S

/-- STATUS: PROVED (Ws.ws_glG_E_noFs)
SIZE: S
REFUTE FIRST on skStepOm1WG2: ε_{Ω₁+1} is an (A2) level of its remaining case (not Ω₁, not a successor, no
Wp.WpFs: every level below has glG ≥ 1 > 0 = glG ε_{Ω₁+1}) and it has no Ω₁-sequence (cofinality ω). -/
theorem skGlGNoFsE : Wp.WpLev Gf.gfE ∧ Gf.gfE ≠ Om1 ∧ (¬ ∃ ℓ', Wp.WpLev ℓ' ∧ Gf.gfE = ℓ' + Om1) ∧
    ¬ Wp.WpFs Gf.gfE ∧ ¬ ∃ s, Ws.wsA2.Seq1 Gf.gfE s := Ws.ws_glG_E_noFs

/-- STATUS: PROVED (Ws.ws_baseI_Z: Ws.ws_base_one — η = 0: towers Ω₁^{…}; η' + 1: towers over glPsi 1 η';
η a limit: from the sequence of η, continuity Ws.ws_psi1_cont, gate-cofinality through the bracket of b — and
Ws.ws_base_Z: the iterates φ(1, ·)^{k+1}(Ω₁+1))
SIZE: M
THE VEBLEN NODES OF LEVEL 1: every ε-number code e ∈ [ε_{Ω₁+1}, ζ_{Ω₁+1}] has a sequence of levels, given the
sequences of the smaller limit codes. -/
theorem skBaseZ : Ws.WsBaseI (Ws.wsZ + 1) := Ws.ws_baseI_Z

/-- STATUS: PROVED (Ws.wsCls_Z)
SIZE: M
the (A2) classification up to ζ_{Ω₁+1}, unconditional. -/
theorem skClsZ : Ws.WsCls Ws.wsA2 (Ws.wsZ + 1) := Ws.wsCls_Z

/-- STATUS: PROVED (Ws.wsSysZ)
SIZE: M
the systems over G at every (A2) level ℓ ≤ ζ_{Ω₁+1}, unconditional. -/
theorem skSysZ : ∀ ℓ, SkLevG ℓ → ℓ ≤ Ws.wsZ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Ws.gh ℓ :=
  Ws.wsSysZ

/-- STATUS: PROVED (Wx.wx_baseA2Hi = Wx.wx_base_hi: ONE proof for every Veblen level α of e = glPsi α η; was OPEN L)
SIZE: L
THE VEBLEN NODES OF LEVEL ≥ 2: every ε-number code e ∈ (ζ_{Ω₁+1}, G) (e = glPsi α η, α ≥ 2 or the level-1 codes
above the first ζ) has an ω- or Ω₁-sequence of levels (gate gh = max 1 glG), given the sequences of the smaller
limit codes.  Cases (Wx.wx_base_I, Wx.wx_pkg, Wx.wx_base_one, Wx.wx_base_succ, Wx.wx_base_lim): η a limit not in
F_α (from η; gate-cofinality by Wx.wx_rec through Gl.glPsi_lt_lev / glPsi_lt_lev'); otherwise the predecessor f
(e = φ(α, y+1), f = φ(α, y), or e = φ(α, 0), f = Ω₁) and α = 1 (towers over f), α = α'+1 ≥ 2 (iterates of
φ(α', ·) over f+1), α a limit (φ(α_k, f+1) / φ(s μ, f+1) from the sequence of α).  REFUTE FIRST: NO EVIDENCE
(skRefuteA2Hi). -/
theorem skBaseA2Hi : ∀ e, InE e → Ws.wsZ < e → e < Gc.gcG 0 →
    (∀ c, c < e → IsSuccLimit c → Ws.BCls (fun _ => True) c) → Ws.BCls Ws.ML e :=
  Wx.wx_baseA2Hi

/-- STATUS: PROVED (Wx.wx_refute)
SIZE: S
REFUTE FIRST on skBaseA2Hi at the first codes past level 1: φ(1, ζ_{Ω₁+1}+1) and φ(2, Ω₁+2) have sequences of
levels. -/
theorem skRefuteA2Hi : Ws.BCls Ws.ML (veblen 1 (Ws.wsZ + 1)) ∧ Ws.BCls Ws.ML (veblen 2 (Om1 + 1 + 1)) :=
  Wx.wx_refute

/-- STATUS: PROVED (skBaseA2Hi, skBaseZ; Ws.wsBaseI_of_hi; was REDUCED)
SIZE: L
THE VEBLEN NODES OF (A2): every ε-number code e ∈ [ε_{Ω₁+1}, G) has an ω- or Ω₁-sequence of levels (gate
gh = max 1 glG), given the sequences of the smaller limit codes. -/
theorem skBaseA2 : Ws.WsBaseI (Gc.gcG 0) := Ws.wsBaseI_of_hi skBaseA2Hi

/-- STATUS: PROVED (skBaseA2; Ws.wsCls_of_baseI: ONE well-founded induction Ws.ws_br on the base-e normal form —
rest, digit, power, base)
SIZE: M
THE (A2) CLASSIFICATION: every (A2) level that is not Ω₁ and not a successor has an ω-sequence (Ws.wsA2.Fs) or an
Ω₁-sequence (Ws.wsA2.Fs1). -/
theorem skClsA2 : Ws.WsCls Ws.wsA2 (Gc.gcG 0) := Ws.wsCls_of_baseI le_rfl skBaseA2

/-- STATUS: PROVED (Ws.ws_base_w: Ws.ws_base_E (towers Ω₁^{…}), Ws.ws_base_succ (towers e^{…}), Ws.ws_base_top)
SIZE: M
non-vacuity of skBaseA2: every ε-number code in [ε_{Ω₁+1}, ε_{Ω₁+ω}] has a sequence of levels. -/
theorem skBaseW : Ws.WsBase (Ws.wsLw + 1) := Ws.ws_base_w

/-- STATUS: PROVED (Ws.wsCls_w)
SIZE: M
the (A2) classification up to ε_{Ω₁+ω}, unconditional. -/
theorem skClsW : Ws.WsCls Ws.wsA2 (Ws.wsLw + 1) := Ws.wsCls_w

/-- STATUS: PROVED (skClsA2; Ws.wsA2_sysAll: the generic family Ws.wsF of Ws.wsA2; was REDUCED)
SIZE: M
the systems over G at every (A2) level: B = φ(ℓ, G+1), gate ≤ gh ℓ. -/
theorem skSysAllG2 : ∀ ℓ, SkLevG ℓ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Ws.gh ℓ :=
  Ws.wsA2_sysAll skClsA2

/-- STATUS: PROVED (Ws.wsSysW)
SIZE: M
the systems over G at every (A2) level ℓ ≤ ε_{Ω₁+ω}, unconditional. -/
theorem skSysW : ∀ ℓ, SkLevG ℓ → ℓ ≤ Ws.wsLw → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Ws.gh ℓ :=
  Ws.wsSysW

/-- STATUS: PROVED (skBaseA2; Ws.wsSysA2Lev_baseI; was REDUCED (skBaseA2), before (skSysAllG, skLevG_Bn, skGateBn))
SIZE: M
∀ n ∃ system V: B_V = φ(glBn n, G+1), γ_V < K. -/
theorem skSysA2Lev (S : InaccSeq.{0}) : ∀ n, ∃ V : Hg.HgVD, V.B = veblen (Gl.glBn n) (Gc.gcG 0 + 1) ∧
    V.γ < Td.tdK S := Ws.wsSysA2Lev_baseI S skBaseA2

/-- A3 package at the ladder level `t_n` (only the system; see skSysA3Step). -/
def SkPk3 (S : InaccSeq.{0}) (n : ℕ) : Prop :=
  ∃ V : Hg.HgVD, V.B = veblen (Wj.wjT n) (Gc.gcG 0 + 1) ∧ V.γ < Td.tdK S

/-! ### (A3) on the new level datum (round 117, leaf reg2) -/

/-- STATUS: PROVED (Wn.wnHnLv_lt_T0, Wn.wnHnLv_noRead; RESTATED round 120: `Hn.HnLv` was widened, the old datum is
`Hn.HnLvG`; the old first half is REFUTED, skA3NoBandOld)
SIZE: S
REFUTE-FIRST of the old datum: every Hn.HnLv with the (A1)/(A2) bounds lies below t₀ and never reads
ε_{Γ_{x+1}+1}. -/
theorem skA3NoBand : (∀ Λ : Hn.HnLv, Hn.HnLvG Λ → Λ.L < Wj.wjT 0) ∧
    ∀ (Λ : Hn.HnLv) (x : Ordinal.{0}), Hn.HnLvG Λ → InE x → x < Om1 → Λ.l x ≠ eN (lgG x) :=
  ⟨Wn.wnHnLv_lt_T0, fun Λ _ hG hx hx1 => Wn.wnHnLv_noRead Λ hG hx hx1⟩

/-- STATUS: PROVED (Wy.wyNoBand_false; REFUTES the round-117 first half of skA3NoBand for the widened datum)
SIZE: S
NOT every band level datum lies below t₀ (the datum of t₀ is one). -/
theorem skA3NoBandOld : ¬ (∀ Λ : Hn.HnLv, Λ.L < Wj.wjT 0) := Wy.wyNoBand_false

/-- STATUS: PROVED (Wy.wyLv)
SIZE: S
every (A3) level datum is a band level datum (same level, gate, reading). -/
theorem skA3Band : ∀ Λ : Wn.WnLv3, ∃ Λ' : Hn.HnLv, Λ'.L = Λ.L ∧ Λ'.g = Λ.g ∧ ∀ x, Λ'.l x = Λ.l x :=
  fun Λ => ⟨Wy.wyLv Λ, rfl, rfl, fun _ => rfl⟩

/-- STATUS: PROVED (Wn.wnG_notRange, Wn.wnA3_bound)
SIZE: S
at L > G: G ∉ range φ(L, ·) (no start over G as in (A1)/(A2)); φ(L, G+1) = hdNx L (φ(L, G)). -/
theorem skA3NoGBase : ∀ L, Gc.gcG 0 < L →
    ¬ Lu.LuP L (Gc.gcG 0) ∧ veblen L (Gc.gcG 0 + 1) = Hd.hdNx L (veblen L (Gc.gcG 0)) :=
  fun L hL => ⟨Wn.wnG_notRange hL, Wn.wnA3_bound L⟩

/-- STATUS: PROVED (Wn.wnLv3T0)
SIZE: S
NON-VACUITY of the (A3) datum: ∃ Λ : WnLv3, L = t₀, gate 0, reading ε_{Γ_{x+1}+1}. -/
theorem skA3Datum0 : ∃ Λ : Wn.WnLv3, Λ.L = Wj.wjT 0 ∧ Λ.g = 0 ∧
    ∀ x, InE x → x < Om1 → Λ.l x = eN (lgG x) :=
  ⟨Wn.wnLv3T0, rfl, rfl, fun _ hx hx1 => Wn.wnLv3T0_l hx hx1⟩

/-- STATUS: PROVED (Wt.wtLv3DatumAll)
SIZE: M
every (A3) level below t₀ has an (A3) level datum: G < L < t₀, Ω₁ ∣ L ⇒ ∃ Λ : WnLv3, L_Λ = L, gate g(L) of the
hereditary step Go.goGl.step, reading its reading R(L, x) above the gate. -/
theorem skA3DatumAll : ∀ L, Gc.gcG 0 < L → Om1 ∣ L → L < Wj.wjT 0 → ∃ Λ : Wn.WnLv3, Λ.L = L ∧
    Λ.g = Wt.wtD.g L ∧ ∀ x, InE x → x < Om1 → Λ.g < x → Λ.l x = Wt.wtD.R L x :=
  Wt.wtLv3DatumAll

/-- STATUS: PROVED (Wt.wtTowSeq)
SIZE: M
the ω-sequence of (A3) level data below t₀ (towers G^{⋯^G}, gate 0): levels +Ω₁-increasing and cofinal in t₀,
readings +x-increasing, below and cofinal in ε_{Γ_{x+1}+1} (the data of the limit step at t₀, Wm.WmSeq-style). -/
theorem skA3Tow :
    (∀ n, (Wt.wtTwLv n).g ≤ Wn.wnLv3T0.g) ∧
    (∀ n, (Wt.wtTwLv n).L + Om1 ≤ (Wt.wtTwLv (n + 1)).L ∧ (Wt.wtTwLv n).L + Om1 ≤ Wn.wnLv3T0.L) ∧
    (∀ y, y < Wn.wnLv3T0.L → ∃ n, y < (Wt.wtTwLv n).L) ∧
    (∀ x, InE x → x < Om1 → ∀ n,
      (Wt.wtTwLv n).l x + x ≤ (Wt.wtTwLv (n + 1)).l x ∧ (Wt.wtTwLv n).l x + x ≤ Wn.wnLv3T0.l x) ∧
    (∀ x, InE x → x < Om1 → ∀ ν, ν < Wn.wnLv3T0.l x → ∃ n, ν < (Wt.wtTwLv n).l x) :=
  Wt.wtTowSeq

/-- STATUS: PROVED (Wt.wt_Q3_low)
SIZE: S
an (A3) pseudo-base F of level L is in range φ(μ, ·) and hdNx μ F < hdNx L F for every μ < L: the step at an (A3)
level contains the steps of all lower levels ((A1), (A2) included) at F, so skSysA3Lev0W needs (A2) closed. -/
theorem skA3StepLow : ∀ (Λ : Wn.WnLv3) (Q : Wn.WnQ3 Λ 0) (μ : Ordinal.{0}), μ < Λ.L →
    veblen μ Q.F = Q.F ∧ Hd.hdNx μ Q.F < Hd.hdNx Λ.L Q.F :=
  fun _ Q _ hμ => Wt.wt_Q3_low Q hμ

/-- The (A3) invariant at `t_n` with the FULL package (`Wn.WnEnt3`). -/
def SkPk3W (S : InaccSeq.{0}) (n : ℕ) : Prop := Wn.WnEnt3 S n

/-- STATUS: PROVED (Wn.wnEnt3_sys)
SIZE: S
the full invariant gives the old one: SkPk3W S n ⇒ SkPk3 S n. -/
theorem skPk3_of_W (S : InaccSeq.{0}) (n : ℕ) (h : SkPk3W S n) : SkPk3 S n := Wn.wnEnt3_sys h

/-- STATUS: PROVED (Wy.wyEnt3_iff)
SIZE: S
the (A3) target at t₀ in Hn form: WnEnt3 S 0 ⇔ some (A3) datum Λ of level t₀, gate < K, carries an Hn package
and a pseudo-base of wyLv Λ at φ(t₀, G) with gate < K and a start. -/
theorem skA3EntHn (S : InaccSeq.{0}) : SkPk3W S 0 ↔
    ∃ Λ : Wn.WnLv3, Λ.L = Wj.wjT 0 ∧ Λ.g < Td.tdK S ∧
      (∃ K : Hn.HnPk, K.Λ = Wy.wyLv Λ) ∧ ∃ (Q : Hn.HnVQ (Wy.wyLv Λ) 0) (U : Hg.HgVD) (_ : Hg.HgSStart (Hn.hnVPB Q) U),
        Q.F = veblen (Wj.wjT 0) (Gc.gcG 0) ∧ Q.γ < Td.tdK S := Wy.wyEnt3_iff S

/-- STATUS: REPLACED (round 121: by skA3TowPk1; the data `Wy.wyLv (Wt.wtTwLv n)` have gate `0`, the data of the
`Ws` family have gate `max 1 g = 1` (`Xc.xc_lv_ne`), and the target needs no gate-`0` datum: `Xc.xcEnt3_of` uses the
gate-`1` datum `Xc.xcLvT0`.  REFUTE FIRST: NO EVIDENCE against the gate-`0` statement; it is no longer needed)
SIZE: L
the packages at the tower levels G^{⋯^G} (as band data, Wy.wyLv (Wt.wtTwLv n)) extending each other (Wm.WmExt). -/
theorem skA3TowPk (S : InaccSeq.{0}) : ∃ K : ℕ → Hn.HnPk, (∀ n, (K n).Λ = Wy.wyLv (Wt.wtTwLv n)) ∧
    ∀ n, Wm.WmExt (K n) (K (n + 1)) := by
  sorry

/-- STATUS: PROVED (Xc.xcCls; round 121)
SIZE: L
THE (A3) CLASSIFICATION, unconditional: every level `ℓ < t₀` of the (A3) code interface `Xc.xcA3` that is not `Ω₁`, not
a successor level and has no `ω`-sequence has an `Ω₁`-sequence of levels (one induction on `G^j·d + r`; the base `G`
has the `ω`-sequence `Gl.glCfn k k`; below `G` the (A2) classification `Ws.ws_br`, `Wx.wx_baseI`). -/
theorem skA3Cls : Ws.WsCls Xc.xcA3 (Wj.wjT 0) := Xc.xcCls

/-- STATUS: PROVED (Xc.xcTowPk; round 121, replaces skA3TowPk)
SIZE: L
the packages of the (A3) family at the tower levels `G^{⋯^G}` (data `Xc.xcA3.lv (wtTw n)`, gate `1`) extend each
other (`Wm.WmExt`, from `Ws.WsExt` by `Xc.xc_wmExt`). -/
theorem skA3TowPk1 : ∃ K : ℕ → Hn.HnPk, (∀ n, (K n).Λ = Xc.xcA3.lv (Wt.wtTw n) (Xc.xc_lev_tw n)) ∧
    ∀ n, Wm.WmExt (K n) (K (n + 1)) := Xc.xcTowPk

/-- STATUS: PROVED (Xc.xcPkT0; round 121)
SIZE: M
THE (A3) PACKAGE AT `t₀`, unconditional: the `ω`-limit (`Wm.wmPkL`) of skA3TowPk1 on the datum `Xc.xcLvT0` (level `t₀`,
reading `ε_{Γ_{x+1}+1}`, gate `1`). -/
theorem skA3PkT0 : ∃ K : Wn.WnPk3, K.Λ.L = Wj.wjT 0 ∧ K.Λ.g = 1 := ⟨Xc.xcPkT0, rfl, rfl⟩

/-- STATUS: PROVED (Xc.xcQT0; round 121)
SIZE: M
the pseudo-base of level `t₀` at `φ(t₀, G)` over `Wn.wnLv3T0`, gate `0`, reading `ϑˣ(Ω₁·ε_{Γ_{x+1}+1} + Γ_{x+1})`. -/
theorem skA3T0Q : Xc.xcQT0.F = veblen (Wj.wjT 0) (Gc.gcG 0) ∧ Xc.xcQT0.γ = 0 := ⟨rfl, rfl⟩

/-- STATUS: PROVED (Xf.xfV1, Xf.xf_start1; round 122)
SIZE: M
THE LEVEL `G` OVER THE RAW DATUM `G` (`φ(G, 0) = G`): a system with bound `φ(G, 1)`, gate `1`, starting the
pseudo-base `φ(G, 1)` of the level `G` (`Xf.xfQ`): the gated `ω`-chain union of the (A2) systems over `G` at the
gate-`0` (A2) levels `Xc.xcCf k` cofinal in `G` (`φ(G, 1) = sup_k φ(ℓ_k, G+1)`). -/
theorem skA3G1 : ∃ U : Hg.HgVD, U.B = veblen (Gc.gcG 0) 1 ∧ U.γ = 1 ∧
    Hg.HgSStart (Hn.hnVPB (Xf.xfQ 1 le_rfl Xf.xf_one_lt_gam0)) U := ⟨Xf.xfV1, rfl, rfl, Xf.xf_start1⟩

/-- STATUS: PROVED (Xf.xfV_start, Xf.xfV_B, Xf.xfV_γ; round 122)
SIZE: L
THE CONSTANT OFFSETS OF THE LEVEL `G`: for every `ν < Γ₀` a system starting the pseudo-base `φ(G, 1+ν)` (gate
`1+ν`), by one recursion `Xf.xfV` (successor: the package `Xf.xfPk` of the (A3) family at `G`; limit: the gated
`ω`-chain union, gate `λ`); later systems extend earlier ones (`Xf.xfV_ext`). -/
theorem skA3GOff : ∀ ν (hν : ν < gamma 0), ∃ U : Hg.HgVD, U.B = veblen (Gc.gcG 0) (1 + ν) ∧ U.γ ≤ 1 + ν ∧
    Hg.HgSStart (Hn.hnVPB (Xf.xfQ (1 + ν) le_self_add (Xf.xf_one_add_lt hν))) U := fun _ hν =>
  ⟨Xf.xfV _, Xf.xfV_B hν, Xf.xfV_γ hν, Xf.xfV_start hν⟩

/-- STATUS: PROVED (Xf.xf_sysG; round 122)
SIZE: S
every `B < φ(G, Γ₀)` lies below the bound of a system with gate `< K` (the systems of skA3GOff). -/
theorem skSysA3G (S : InaccSeq.{0}) : ∀ B, B < veblen (Gc.gcG 0) (gamma 0) →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := Xf.xf_sysG S

/-- STATUS: PROVED (Xl.xlV_B, Xl.xlV_γ_iff, Xl.xlV_b; round 123)
SIZE: L
EVERY OFFSET OF THE LEVEL `G`: for every `λ < φ(G+1, 0)` a system with bound `φ(G, 1+λ)` starting the stage at the
offset `λ` (`Xl.xlV_start`), its gate below a base `x` iff `max(1, g(λ)) < x` (`g(λ)` the code gate of `λ` in the
system itself), its base reading `φ(Γ_{x+1}, 1 + λ(x))`; one recursion `Xl.xlV` (port of `Hn.HnVRec` with the base
`0`), later systems extend earlier ones (`Xl.xlV_ext`). -/
theorem skA3GAll : ∀ l, l < veblen (Gc.gcG 0 + 1) 0 → ∃ U : Hg.HgVD, U.B = veblen (Gc.gcG 0) (1 + l) ∧
    ∀ x, InE x → x < Om1 → (U.γ < x ↔ max 1 (U.g l) < x) := fun _ hl => by
  rw [← Xl.xlN_eq] at hl
  exact ⟨Xl.xlV _, Xl.xlV_B hl, fun _ hx hx1 => Xl.xlV_γ_iff hl hx hx1⟩

/-- STATUS: PROVED (Xl.xlTop, Xl.xlTop_hgU; round 123)
SIZE: L
THE TOP OF THE LEVEL `G`: a system with bound `φ(G+1, 0)` (the first fixed point of `φ(G, ·)`), gate `1`, base
reading `φ(Γ_{x+1}+1, 0)`, extending `Hg.hgU` (and `Xf.xfV1` and every `Xl.xlV λ`). -/
theorem skA3GTop : ∃ U : Hg.HgVD, U.B = veblen (Gc.gcG 0 + 1) 0 ∧ U.γ = 1 ∧
    ∀ c x, c < Hg.hgU.B → U.R c x = Hg.hgU.R c x ∧ U.g c = Hg.hgU.g c :=
  ⟨Xl.xlTop, Xl.xlTop_B, Xl.xlTop_γ, fun _ x hc => Xl.xlTop_hgU hc x⟩

/-- STATUS: PROVED (Xl.xl_sysG; round 123)
SIZE: S
every `B ≤ φ(G+1, 0)` lies below the bound of a system with gate `< K` (skA3GTop). -/
theorem skSysA3Gall (S : InaccSeq.{0}) : ∀ B, B ≤ veblen (Gc.gcG 0 + 1) 0 →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := Xl.xl_sysG S

/-- STATUS: PROVED (Xl.xlK_at, Xl.xlK_γ, Xl.xlK_ext; round 123)
SIZE: L
EVERY CONSTANT LEVEL `G + κ`, `κ < Ω₁`: a system with bound `φ(G + κ + 1, 0)` (the top of the level `G + κ`), gate
`≤ κ + 1`; one recursion on `κ` (`Xl.xlK`); later systems extend earlier ones. -/
theorem skA3GK : ∀ κ, κ < Om1 → ∃ U : Hg.HgVD, U.B = veblen (Gc.gcG 0 + (κ + 1)) 0 ∧ U.γ ≤ κ + 1 :=
  fun _ hκ => ⟨Xl.xlK _, Xl.xlK_B hκ, Xl.xlK_γ hκ⟩

/-- STATUS: PROVED (Xl.xlW, Xl.xlW_hgU; round 123)
SIZE: M
THE LEVEL `G + Ω₁` FROM THE BOTTOM: a system with bound `φ(G + Ω₁, 0)`, gate `1`, base reading
`φ(Γ_{x+1} + x, 0)`, extending `Hg.hgU`: the `Ω₁`-union `Ho.hoOU` of all `Xl.xlK κ` (SMALL: `Xl.xlK_small`). -/
theorem skA3GW : ∃ U : Hg.HgVD, U.B = veblen (Gc.gcG 0 + Om1) 0 ∧ U.γ = 1 ∧
    ∀ c x, c < Hg.hgU.B → U.R c x = Hg.hgU.R c x ∧ U.g c = Hg.hgU.g c :=
  ⟨Xl.xlW, Xl.xlW_B, Xl.xlW_γ, fun _ x hc => Xl.xlW_hgU hc x⟩

/-- STATUS: PROVED (Xl.xlw_sysG; round 123)
SIZE: S
every `B ≤ φ(G + Ω₁, 0)` lies below the bound of a system with gate `< K` (skA3GW). -/
theorem skSysA3GW (S : InaccSeq.{0}) : ∀ B, B ≤ veblen (Gc.gcG 0 + Om1) 0 →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := Xl.xlw_sysG S

/-- STATUS: PROVED (Xp.xpBandStep; round 124)
SIZE: L
THE GENERIC BAND STEP: for every band datum `B` (`Xp.XpBd`: a package at a level `L > G` with reading below
`ε_{Γ_{x+1}+1}`, not strongly critical) a system at the bottom `φ(L, 0)` (`Xp.XpAt`) gives a system at the bottom
`φ(L + Ω₁, 0)` of the next band, gate `g`, extending it (the levels `L + κ`: `Xp.xpK`, the `Ω₁`-union: `Xp.xpW`). -/
theorem skA3BandStep (B : Xp.XpBd) (U0 : Hg.HgVD) (hU0 : Xp.XpAt B.K.Λ 0 U0) :
    ∃ V : Hg.HgVD, Xp.XpAt B.succ.K.Λ 0 V ∧ V.γ = B.K.Λ.g ∧
      ∀ c x, c < U0.B → V.R c x = U0.R c x ∧ V.g c = U0.g c :=
  Xp.xpBandStep B U0 hU0

/-- STATUS: PROVED (Xp.xpFam, Xp.xpSys_B, Xp.xpSys_γ, Xp.xpSys_hgU; round 124)
SIZE: L
EVERY (A3) BAND LEVEL: for every `G < ℓ < t₀` with `Ω₁ ∣ ℓ` a system with bound `φ(ℓ, 0)`, gate `≤ xg ℓ`, at the
bottom of the datum `Xc.xcA3.lv ℓ`, extending `Hg.hgU`; one well-founded recursion along `Xc.xcA3` (later members
extend earlier ones). -/
theorem skA3Bands : ∀ ℓ, Gc.gcG 0 < ℓ → Om1 ∣ ℓ → ℓ < Wj.wjT 0 → ∃ U : Hg.HgVD, U.B = veblen ℓ 0 ∧ U.γ ≤ Xc.xg ℓ ∧
    ∀ c x, c < Hg.hgU.B → U.R c x = Hg.hgU.R c x ∧ U.g c = Hg.hgU.g c := fun ℓ h1 h2 h3 =>
  ⟨Xp.xpSys ℓ, Xp.xpSys_B ⟨h1, h2, h3⟩, Xp.xpSys_γ ⟨h1, h2, h3⟩, fun _ x hc => Xp.xpSys_hgU ⟨h1, h2, h3⟩ hc x⟩

/-- STATUS: PROVED (Xp.xpV0, Xp.xp_at_t0; round 124)
SIZE: M
THE BOTTOM `φ(t₀, 0)`: the union of the tower bands, a system with bound `φ(t₀, 0)`, gate `1`, at the bottom of the
datum `Xc.xcLvT0` of `t₀`. -/
theorem skA3T0Bot : ∃ U : Hg.HgVD, U.B = veblen (Wj.wjT 0) 0 ∧ U.γ = 1 ∧ Xp.XpAt Xp.xpBT0.K.Λ 0 U :=
  ⟨Xp.xpV0, Xp.xpV0_B, Xp.xpV0_γ, Xp.xp_at_t0⟩

/-- STATUS: PROVED (Xp.xpQG, Xp.xpQG_start; round 124)
SIZE: L
THE LEVEL `t₀` UP TO THE OFFSET `G`: a pseudo-base of level `t₀ + 0` at `φ(t₀, G)` over the datum `Xc.xcLvT0`
(gate `1`) and a system starting it (the stage `G` of the bottom recursion of `t₀`). -/
theorem skA3T0G : ∃ (Q : Hn.HnVQ (Wy.wyLv Xc.xcLvT0) 0) (U : Hg.HgVD) (_ : Hg.HgSStart (Hn.hnVPB Q) U),
    Q.F = veblen (Wj.wjT 0) (Gc.gcG 0) ∧ Q.γ = 1 :=
  ⟨Xp.xpQG, Xp.xpVT (Gc.gcG 0), Xp.xpQG_start, Xp.xpQG_F, Xp.xpQG_γ⟩

/-- STATUS: PROVED (Xp.xpT0_sysG; round 124)
SIZE: S
every `B ≤ φ(t₀, G+1)` lies below the bound of a system with gate `< K` (the step of `Xc.xcPkT0` at skA3T0G). -/
theorem skSysA3T0G (S : InaccSeq.{0}) : ∀ B, B ≤ veblen (Wj.wjT 0) (Gc.gcG 0 + 1) →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := Xp.xpT0_sysG S

/-- STATUS: OPEN
SIZE: L
a system starting the pseudo-base `φ(t₀, G)` (round 121).  By `Xc.xc_start_iff`: `U.ix = φ(t₀, G)` (so
`U.B = φ(t₀, G)`, `Xc.xc_start_B`), `U.γ` below every `ε`-number, `U.b x = ϑˣ(Ω₁·ε_{Γ_{x+1}+1} + Γ_{x+1})`,
`U.Z x = ζ` of it.  `U.B > φ(ℓ, G+1)` for every `ℓ < t₀` (`Xc.xc_start_cover`): U is region (A3) below `φ(t₀, G)`, a
recursion over the (A3) levels `ℓ ≤ t₀` and the offsets `ν` of the pseudo-bases `φ(ℓ, ν)` (the (A3) family
`Xc.xcFam` gives the step of every level `ℓ < t₀` at every raw datum; the pseudo-bases `φ(ℓ, ν)`, `ℓ > G`, and their
starts are what is missing).  REFUTE FIRST: NO EVIDENCE (the fields of the start are consistent: `xcQT0` exists).
Round 122: REFUTE FIRST again NO EVIDENCE (no known no-go result mentions starts, pseudo-bases or packages; the
pieces built so far are unconditional).  First steps PROVED: the level `G` from the bottom, `φ(G, ν)` for every
constant `1 ≤ ν < Γ₀` (skA3G1, skA3GOff).  Next, in order: the offsets of `G` read by (A2) codes and past them
(pseudo-bases `φ(G, ν)` with a code gate `≥ Γ₀`: a code of `[φ(G, ν), φ(G, ν+1))` over `Z` must force the gate of
`ν` below `Z`; unions at `Ω₁`-cofinal offsets as `Ho.hoOU`; the gated frontier lemma `Gr.GrUni` at gates `≥ Γ₀`) up
to `φ(G+1, 0)`; then every level `G < ℓ ≤ t₀` with its pseudo-bases `φ(ℓ, ν)` from the bottom `φ(ℓ, 0)`.
Round 123: REFUTE FIRST again NO EVIDENCE (tested against every listed no-go result; none mentions starts,
pseudo-bases, packages or offsets; the new pieces are unconditional).  PROVED: the whole level `G` (skA3GAll,
skA3GTop: every offset `λ < φ(G+1, 0)`, read by the system itself, gate `max(1, g(λ))`; the system at `φ(G+1, 0)`,
gate `1`).  Next, in order: (1) the bottom recursion at the level `G + κ` (`Xl.XlRec` with the base `0` and the
offset `λ` at `φ(G+κ, λ)`, reading `ϑˣ(Ω₁·(Γ_{x+1}+κ) + λ(x)) = φ(Γ_{x+1}+κ, λ(x))` since `G+κ` is not strongly
critical for `κ ≥ 1`), started at the top of the level `G+κ'` (`κ = κ'+1`, the stage `0` is `φ(G+κ, 0)`) with the
step `Hn.hnVLS xfPk.St0 κ`; (2) unions at limit `κ < Ω₁` and at `Ω₁` (`Ho.hoOU`); (3) the levels `L + κ` along the
(A3) code interface `Xc.xcA3`, with the packages of `Xc.xcFam`; (4) the level `t₀` from `φ(t₀, 0)` to the offset
`G` with `Xc.xcPkT0`.  Later in round 123 (1) and (2) are DONE for the band `L = G` (skA3GK, skA3GW: every level
`G + κ`, `κ < Ω₁`, and the `Ω₁`-union at `φ(G + Ω₁, 0)`).  Left, in order: the same for every band `L` of the (A3) code
interface (the band `G + Ω₁` is `Hn.HnLv.succ xfLv` with the package `HnPk.succ xfPk`; the bottom base `Xl.XlB` and
the transfer `Xl.xl_start_of_at` / `Xl.xl_at_top` must be made generic in the band, `Xl.XlK*` / `Xl.XlW` are written
for `xfLv`), the limits of bands (`Ω₁`-cofinal and `ω`-cofinal band codes, the packages of `Xc.xcFam`), the level
`t₀`, and the offsets `ν ≤ G` at `t₀`.
Round 124: REFUTE FIRST again NO EVIDENCE.  All of that is DONE (skA3BandStep, skA3Bands, skA3T0Bot, skA3T0G), but
for the pseudo-base over `Xc.xcLvT0` (gate `1`) and with the reading `R_U(G)` of the code `G` in the system itself;
`skSysA3Lev0W` is PROVED from it directly (`Xp.xpEnt3`), so this node is OFF THE ROAD.  What it still asks beyond
skA3T0G: `U.R G x = Γ_{x+1}` in the systems (no Lean lemma tracks the readings of the codes below `G` through the
chain `Hg.hgU ← Hf ← … ← Gw.gw0`; `Gw.gw0` has base reading `Γ_{x+1}` at the bound `G`). -/
theorem skA3T0Start : ∃ U : Hg.HgVD, Hg.HgSStart (Hn.hnVPB Xc.xcQT0) U := by
  sorry

/-- STATUS: REDUCED (skA3T0Start, Xc.xcQT0_of_start; round 121, was OPEN L; OFF THE ROAD since round 124:
skSysA3Lev0W is PROVED by Xp.xpEnt3 over the datum Xc.xcLvT0)
SIZE: L
the pseudo-base φ(t₀, G) of level t₀ over the datum of t₀ (bound fields: Wn.wnQ3_bounds) with gate < K, and a
system starting it.  REFUTE FIRST: NO EVIDENCE; it is the second half of the target in Hn form (skA3EntHn) at
Λ = Wn.wnLv3T0. -/
theorem skA3QT0 (S : InaccSeq.{0}) : ∃ (Q : Hn.HnVQ (Wy.wyLv Wn.wnLv3T0) 0) (U : Hg.HgVD)
    (_ : Hg.HgSStart (Hn.hnVPB Q) U), Q.F = veblen (Wj.wjT 0) (Gc.gcG 0) ∧ Q.γ < Td.tdK S := by
  obtain ⟨U, hU⟩ := skA3T0Start
  exact Xc.xcQT0_of_start S U hU

/-- STATUS: PROVED (Xp.xpEnt3; round 124; was REDUCED (skA3QT0 only, by Xc.xcEnt3_of))
SIZE: L
the (A3) package at t₀ = ε_{G+1} (Xc.xcPkT0: the ω-limit of the (A3) family at the towers, datum Xc.xcLvT0 of gate 1)
and the pseudo-base φ(t₀, G) of level t₀ with gate < K and a system starting it: the pseudo-base and the system of
skA3T0G (gate 1), no longer through skA3QT0. -/
theorem skSysA3Lev0W (S : InaccSeq.{0}) : SkPk3W S 0 := Xp.xpEnt3 S

/-- STATUS: PROVED (Xu.xuC, Xu.xuC_Bd, Xu.xuC_R, Xu.xuC_low; round 125)
SIZE: L
THE (A3) CODE INTERFACE BELOW EVERY `ε`-NUMBER BOUND `B ∈ [t₀, Γ(1))`: a `Ws.WsC` with bound `B`, reading `Xu.xuR`
(every code `c < Γ(1)`: `ϑˣ(Ω₁·α(x)+η(x))^{j(x)}·d(x)+r(x)` in the bracket of `xuPsi α η`), equal to `Xc.xcA3` below
`t₀` (same reading and gate). -/
theorem skA3CodeAll : ∀ B (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < Gc.gcG 1),
    (Xu.xuC B hBE hBt hB1).Bd = B ∧ (Xu.xuC B hBE hBt hB1).R = Xu.xuR ∧
      ∀ c, c < Wj.wjT 0 → (Xu.xuC B hBE hBt hB1).R c = Xc.xcA3.R c ∧ (Xu.xuC B hBE hBt hB1).g c = Xc.xcA3.g c :=
  fun _ hBE hBt hB1 => ⟨rfl, rfl, fun _ hc => Xu.xuC_low hBE hBt hB1 hc⟩

/-- STATUS: PROVED (Xu.xuClsN, Xu.xuCls, Xu.xu_br, Xu.xu_base; round 125)
SIZE: L
THE (A3) CLASSIFICATION BELOW EVERY `t_n`, unconditional: every level `ℓ < t_n` of `Xu.xuCn n` that is not `Ω₁`, not a
successor level and has no `ω`-sequence has an `Ω₁`-sequence (one induction on `e^j·d + r`; the `ε`-number codes
`e ∈ [t₀, Γ(1))` by one proof for every Veblen level, `Xu.xu_base`). -/
theorem skA3ClsAll : ∀ n, Ws.WsCls (Xu.xuCn n) (Wj.wjT n) := Xu.xuClsN

/-- STATUS: PROVED (Xu.xu_A3_end; round 125)
SIZE: S
WHERE (A3) ENDS: `G < t_n < Γ(1)` for every `n`, the `t_n` are cofinal in `Γ(1)`, and `Γ(1)` is the least strongly
critical ordinal above `G`. -/
theorem skA3End : (∀ n, Gc.gcG 0 < Wj.wjT n ∧ Wj.wjT n < Gc.gcG 1) ∧ (∀ y, y < Gc.gcG 1 → ∃ n, y < Wj.wjT n) ∧
    ∀ b, SC b → Gc.gcG 0 < b → Gc.gcG 1 ≤ b := Xu.xu_A3_end

/-- STATUS: PROVED (Xu.xuPk3_ent, Xu.xuPk3, Xu.xuLv3; round 125)
SIZE: M
THE (A3) PACKAGE AT EVERY `t_n`: level `t_n`, gate `1 < K` (the package of the `Ws` family of `Xu.xuCn (n+1)` at its
level `t_n`, as a `Wn.WnPk3` over the datum `Xu.xuLv3`). -/
theorem skA3PkAll (S : InaccSeq.{0}) : ∀ n, ∃ K : Wn.WnPk3, K.Λ.L = Wj.wjT n ∧ K.Λ.g < Td.tdK S :=
  Xu.xuPk3_ent S

/-- STATUS: PROVED (Xu.xuQStart, Xu.xuQB, Xu.xuVT, Xu.xuqSys; round 125)
SIZE: L
the pseudo-base `φ(t_n, G)` over the datum of the package `Xu.xuPk3 n` (gate `1 < K`) and a system starting it, for
every `n`.  REFUTE FIRST (round 125): NO EVIDENCE.  Proof: the band recursion of `Xp` made generic in the bound
(`Xu.XuqBd T`, low field `Xu.xuqZ T = N_{T(x)}(0)`, `Xu.xuqBandStep`, `Xu.xuqStep_all`, `Xu.xuqSys`) with `T = t_{n+1}`
(`Xu.xuT_t`) gives the system at the bottom `φ(t_n, 0)` of the ordinary band level `t_n`; the bottom recursion
`Xl.xlU` of `t_n` reaches the offset `G` (`Xu.xuVT`), and the stage `φ(t_n, G)` starts the pseudo-base `Xu.xuQB n`. -/
theorem skA3QStart (S : InaccSeq.{0}) : ∀ n, ∃ (Q : Wn.WnQ3 (Xu.xuPk3 n).Λ 0) (U : Hg.HgVD)
    (_ : Hg.HgSStart (Hg.hgdPB Q.toP) U), Q.F = veblen (Wj.wjT n) (Gc.gcG 0) ∧ Q.γ < Td.tdK S :=
  Xu.xuQStart S

/-- STATUS: PROVED (Xu.xuqFam, Xu.xuqSys_B, Xu.xuqStep_all; round 125)
SIZE: L
EVERY (A3) BAND BELOW EVERY `t_{n+1}`: for every band level `G < ℓ < t_{n+1}` (`Ω₁ ∣ ℓ`) a system at the bottom
`φ(ℓ, 0)` (one well-founded recursion along the interface `Xu.xuCn (n+1)`, the band step `Xu.xuqBandStep` generic in
the bound). -/
theorem skA3BandsAll : ∀ n ℓ (_h : Xu.XuqLv (Wj.wjT (n + 1)) ℓ),
    (Xu.xuqSys (Xu.xuT_t (n + 1)) ℓ).B = veblen ℓ 0 :=
  fun n _ h => Xu.xuqSys_B (Xu.xuT_t (n + 1)) h

/-- STATUS: PROVED (skA3PkAll, skA3QStart; Xu.xuEnt3_step; round 125, was OPEN L)
SIZE: L
t_n ↦ t_{n+1} = φ(t_n, 0) with the full package as invariant: the package at `t_{n+1}` is `Xu.xuPk3 (n+1)` (the
(A3) code interface `Xu.xuCn (n+2)` and its classification), the pseudo-base and its start are `skA3QStart`; the
hypothesis `SkPk3W S n` is not used (`Xu.xuEnt3`: `Wn.WnEnt3 S n` for every `n`).  Round 124: REFUTE FIRST: NO
EVIDENCE.  Round 125: REFUTE FIRST again NO EVIDENCE. -/
theorem skSysA3StepW (S : InaccSeq.{0}) : ∀ n, SkPk3W S n → SkPk3W S (n + 1) := by
  intro n _
  obtain ⟨Q, U, hU, hF, hγ⟩ := skA3QStart S (n + 1)
  exact ⟨Xu.xuPk3 (n + 1), rfl, by rw [Xu.xuPk3_g]; exact Xc.xc_one_lt_SC Td.tdK_SC, Q, U, hU, hF, hγ⟩

/-- STATUS: PROVED (skSysA3Lev0W, skSysA3StepW; round 125, was REDUCED)
SIZE: L -/
theorem skSysA3LevW (S : InaccSeq.{0}) : ∀ n, SkPk3W S n := by
  intro n
  induction n with
  | zero => exact skSysA3Lev0W S
  | succ n ih => exact skSysA3StepW S n ih

/-- STATUS: PROVED (skSysA3Lev0W, skPk3_of_W; was OPEN L, then REDUCED)
SIZE: L
the first level above G: t₀ = ε_{G+1}; system φ(ε_{G+1}, G+1). -/
theorem skSysA3Lev0 (S : InaccSeq.{0}) : SkPk3 S 0 := skPk3_of_W S 0 (skSysA3Lev0W S)

/-- STATUS: REPLACED (by skSysA3StepW; SUSPECT CONFIRMED: the invariant SkPk3 carries no level datum, so the
hypothesis gives nothing toward the package at t_{n+1}; Lean fact behind it: skA3NoGBase, the (A3) system is the step
of the level package at the pseudo-base φ(t_n, G), which SkPk3 does not hold.  NO EVIDENCE that it is false)
SIZE: M
t_n ↦ t_{n+1} = φ(t_n, 0): the Veblen-exponent union (skStepExpLimG one level up, atoms {Ω₁, G}). -/
theorem skSysA3Step (S : InaccSeq.{0}) : ∀ n, SkPk3 S n → SkPk3 S (n + 1) := by
  sorry

/-- STATUS: PROVED (skSysA3LevW, skPk3_of_W; round 125, was REDUCED)
SIZE: L -/
theorem skSysA3Lev (S : InaccSeq.{0}) : ∀ n, SkPk3 S n := fun n => skPk3_of_W S n (skSysA3LevW S n)

/-- STATUS: PROVED (Wj.wjA3Cof, skSysA3Lev; round 125, was REDUCED)
SIZE: L
∀ B < Γ(1) ∃ system V: B ≤ B_V, γ_V < K. -/
theorem skSysA3All (S : InaccSeq.{0}) : ∀ B, B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨n, hn⟩ := Wj.wjA3Cof hB
  obtain ⟨V, hVB, hγ⟩ := skSysA3Lev S n
  exact ⟨V, hVB ▸ hn.le, hγ⟩

/-- STATUS: PROVED (Wj.wjA2Cof, skSysA2Lev, skSysA3Gall, Xl.xl_GG1_lt; round 123, was REDUCED (Wj.wjA2Cof,
skSysA2Lev, skSysA3All))
SIZE: S
(A2) ∀ B ∈ [φ(ε_{Ω₁+1}, G+1), φ(G, G+1)) ∃ system V, B ≤ B_V, γ_V < K: below φ(G, 1) by the A2 levels glBn n,
on [φ(G, 1), φ(G, G+1)) by the top of the level G (skSysA3Gall, round 123; φ(G, G+1) < φ(G+1, 0)). -/
theorem skSysA2 (S : InaccSeq.{0}) : ∀ B, veblen Gf.gfE (Gc.gcG 0 + 1) ≤ B →
    B < veblen (Gc.gcG 0) (Gc.gcG 0 + 1) → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B _ hB
  rcases lt_or_ge B (veblen (Gc.gcG 0) 1) with h | _
  · obtain ⟨n, hn⟩ := Wj.wjA2Cof h
    obtain ⟨V, hVB, hγ⟩ := skSysA2Lev S n
    exact ⟨V, hVB ▸ hn.le, hγ⟩
  · exact skSysA3Gall S B (hB.trans Xl.xl_GG1_lt).le

/-- STATUS: PROVED (skSysA3All; round 125; was OPEN L, then REDUCED)
SIZE: L
(A3) levels above G: ∀ B ∈ [φ(G, G+1), Γ(1)) ∃ system V, B ≤ B_V, γ_V < K. -/
theorem skSysA3 (S : InaccSeq.{0}) : ∀ B, veblen (Gc.gcG 0) (Gc.gcG 0 + 1) ≤ B →
    B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := fun B _ hB => skSysA3All S B hB

/-! ## (B) ∪ (C): the re-split by the windows `[L(k), L(k+1))` (round 116, leaf reg1)

`Wj.wjSplit`: every range restart is in exactly one of (A), (B-lo), (B-hi), (C), `W_k` (`k < ω`), `W_ω`.
Above `L(0)` every name is `Ω_ω + β`, `0 < β < P′·(ω+1) < Ω₂`, so `e(η) < Ω₂` and the code is the offset code
(`Wj.wjWin_props`); hence (C) lies below `L(0)` (`Wj.wjExpHi_low`) and `skLongMid`, `skLongTop` are vacuous. -/

/-- The window offset `ζ = η_λ - b_ξ` is a copy of a region-(A) name. -/
def SkOffA (S : InaccSeq.{0}) (ξ l : Ordinal.{0}) : Prop :=
  ∃ B, B < Gc.gcG 1 ∧ Cd.cdEta S l - Wj.wjBase S ξ < Gc.gcG B * ω

/-! ### Region (B) after round 122 (leaf regb1, modules `R2.Xh*`)

Every region-(B) name is a base plus an offset `ζ < Ω₂` (`Xh.xhBhi_off`, `Xh.xhWin_off`), the code is `-1 + e(ζ)`;
the offsets are of type (A) (`Xh.XhNmA`) or in a layer `c ≥ 1` (`Xh.XhNmLay`, `Xh.xhNm_split`).  (B-lo) is the base
`0`: its layers `c` (`Xh.XhLay`, `Xh.xhLay_exists`) are region (A) again over the base `Γ(c)`: the levels
`ℓ < Γ(c)` reach `φ(Γ(c), 1)` (`Xh.xhLevCof`), the levels `Γ(c) ≤ ℓ < Γ(c+1)` contain the atom `Γ(c)`. -/

/-- STATUS: PROVED (Xh.xhBlo_iff)
SIZE: S
(B-lo) on names: η_λ < Ω₂ and Γ(B)·ω ≤ η_λ for every B < Γ(1). -/
theorem skBloName (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      l < Bt.iota S (Om (1 + 1))) ↔
    (Cd.cdEta S l < Om (1 + 1) ∧ ∀ B, B < Gc.gcG 1 → Gc.gcG B * ω ≤ Cd.cdEta S l) :=
  Xh.xhBlo_iff hr

/-- STATUS: PROVED (Xh.xhLay_exists, Xh.xhLay_unique)
SIZE: S
every (B-lo) restart lies in exactly one layer c, 1 ≤ c < Ω₂. -/
theorem skLayExists (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : Cd.CdRange S l) (hN : Wj.WjNotA S l)
    (hι : l < Bt.iota S (Om (1 + 1))) : ∃ c, 1 ≤ c ∧ c < Om (1 + 1) ∧ Xh.XhLay S c l :=
  Xh.xhLay_exists hr hN hι

/-- STATUS: PROVED (Xh.xhLevCof)
SIZE: S
in the layer c the levels ℓ < Γ(c) reach exactly φ(Γ(c), 1) (c = 0 is Wj.wjA2Cof). -/
theorem skLayLevCof (c : Ordinal.{0}) {B : Ordinal.{0}} (hB : B < veblen (Gc.gcG c) 1) :
    ∃ ℓ, ℓ < Gc.gcG c ∧ B < veblen ℓ (Gc.gcG c + 1) := Xh.xhLevCof c hB

/-- STATUS: PROVED (Gb.gq_pi)
SIZE: S
EXACT for the base atom of the layer c (c a constant, read Γ_{x+1+c} = gq c x): π_{σ,ρ}(gq c ρ) = gq c σ. -/
theorem skLayExact {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < σ) :
    Gb.gq c ρ ∈ TB ρ σ ∧ pi σ ρ (Gb.gq c ρ) = Gb.gq c σ := Gb.gq_pi hB hc

/-- STATUS: PROVED (Xk.xkL1Img; round 123)
SIZE: M
INGREDIENT of skLayLo 1 / skLayHi 1: Lemma IMG below Γ_{ρ+3} = gq 2 ρ (He.he_img_G1 is the case gq 1 ρ). -/
theorem skL1Img {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) : ∀ v, v < Gb.gq 2 ρ → Gn.GnI ρ δ v :=
  Xk.xkL1Img h

/-- STATUS: PROVED (Xk.xkImg_cst: Xk.xkImg_step, Xk.xkI_atom, Gc.gc_lt_lim_iff; round 123)
SIZE: S
Lemma IMG below the base atom gq c ρ = Γ_{ρ+1+c} for every constant 1 ≤ c < ε₀ (IMG for the layers c < ε₀). -/
theorem skLayImgCst {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) :
    ∀ c, 1 ≤ c → c < ε₀ → ∀ v, v < Gb.gq c ρ → Gn.GnI ρ δ v :=
  Xk.xkImg_cst h

/-- STATUS: PROVED (Xk.xk_sc_iff; round 123)
SIZE: S
the base atoms: the strongly critical v ∈ (x, gq (c+1) x) with c < v are exactly gq c' x, c' ≤ c (c ∈ Tˣ ∩ Ω₁). -/
theorem skLayBaseSC {x c v : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hcT : c ∈ Tset x) (hc1 : c < Om1)
    (hxv : x < v) (hcv : c < v) (hv : v < Gb.gq (c + 1) x) :
    veblen v 0 = v ↔ ∃ c', c' ≤ c ∧ Gb.gq c' x = v :=
  Xk.xk_sc_iff hx hx1 hcT hc1 hxv hcv hv

/-- STATUS: PROVED (Xk.xkVD_round, Xk.xkC_round, Xk.xkRS_round, Xk.xkCG_zero_iff; round 123)
SIZE: S
the interfaces over the base atom Γ(k) (Xk.XkVD k, Xk.XkC k, Xk.XkRS k, Xk.XkCG): their instance k = 0 is the old
interface (Hg.HgVD, Ws.WsC, Gs.GsRS, Ws.WsCG). -/
theorem skLayIface : (∀ D : Hg.HgVD, Xk.XkVD.toHg (Xk.XkVD.ofHg D) = D) ∧
    (∀ C : Ws.WsC, Xk.XkC.toWs (Xk.XkC.ofWs C) = C) ∧ (∀ RS : Gs.GsRS, Xk.XkRS.toGs (Xk.XkRS.ofGs RS) = RS) ∧
    (∀ C : Ws.WsC, Xk.XkCG (Xk.XkC.ofWs C) ↔ Ws.WsCG C) :=
  ⟨Xk.xkVD_round, Xk.xkC_round, Xk.xkRS_round, Xk.xkCG_zero_iff⟩

/-- STATUS: PROVED (Xk.xkLayFront_zero; round 123)
SIZE: S
the frontier lemma over Γ(0) = G (instance k = 0 of skLayFront). -/
theorem skLayFront0 (S : InaccSeq.{0}) : Xk.XkLayFront S 0 := Xk.xkLayFront_zero S

/-- STATUS: PROVED (Xk.xkLaySys_zero; round 123)
SIZE: S
the systems of the old levels over G (instance k = 0 of skLaySys; region A2). -/
theorem skLaySys0 (S : InaccSeq.{0}) : Xk.XkLaySys S 0 := Xk.xkLaySys_zero S

/-- STATUS: PROVED (Xx.xxVD_loc, Xx.xxVD_enum, Xx.xxVD_capV; round 125, new node; round 126: VACUOUS for k ≥ 1,
Xk.XkVD k is empty, skLayEmpty; repaired form Yc.ycVD_loc)
SIZE: M
the bound of every system over Γ(k) (k + 1 < ε₀) with gate below K is located: Λ⁺ = ι(Γ(B)·ω), P(Γ(B)·ω) < L(0),
through the reading system Xx.xxVRS D of the codes below B + ω (codes B + n read b(x) + n, gate γ; no hereditary
step). -/
theorem skLayLocVD (S : InaccSeq.{0}) {k : Ordinal.{0}} (hk : k + 1 < ε₀) (D : Xk.XkVD k) (hγ : D.γ < Td.tdK S) :
    Nm.Pv S (Gc.gcG D.B * ω) < Nc.ncL S 0 := (Xx.xxVD_loc D hk S hγ).2.2

/-- STATUS: PROVED (Xx.xxLayFront: Xx.XxGq, Xx.XxU, Xx.XxRS, Xx.XxLoc, Xx.XxStep; round 125, was OPEN L; round 126:
VACUOUS for 1 ≤ k: Xk.XkVD k is empty, skLayEmpty, Yc.ycLayFront_vac; replaced on the road by skLayFrontY)
SIZE: L
THE FRONTIER LEMMA OVER Γ(k): for every system D : Xk.XkVD k with gate below K, UPPER ∧ LOWER ∧ CapV at every range
restart below ι(Γ(B_D)·ω) (k = 0: skLayFront0, reproved by Xx.xxLayFront_zero).  REFUTE FIRST (round 125): NO
EVIDENCE (now a theorem).  It is a statement about every system over Γ(k); for k ≥ 1 no such system is known yet
(skLaySys), so it does not locate region (A3) by itself. -/
theorem skLayFront (S : InaccSeq.{0}) : ∀ k, 1 ≤ k → k + 1 < ε₀ → Xk.XkLayFront S k :=
  fun _ _ hk => Xx.xxLayFront S hk

/-- STATUS: PROVED (Xx.xxLaySys_base; round 125, new node; round 126: VACUOUS for k ≥ 1, its hypothesis
Xk.XkLaySys S k is false, skLaySys_false)
SIZE: S
DEPENDENCY of skLaySys: the systems over Γ(k) (k + 1 < ε₀) give UPPER ∧ LOWER ∧ CapV at every range restart below
ι(Γ(Γ(k))·ω); for k = 1 that is every range restart of region (A), the (A3) part above t₀ (skSysA3StepW) included. -/
theorem skLaySysBase (S : InaccSeq.{0}) : ∀ k, k + 1 < ε₀ → Xk.XkLaySys S k → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG (Gc.gcG k) * ω) → SkUV S l :=
  fun _ hk hS l hr hl => Xx.xxLaySys_base hk hS l hr hl

/-- STATUS: REFUTED (Yc.ycLaySys_false_eps, Yc.ycVD_empty; round 126, was OPEN L)
SIZE: S
the round-123 statement `∀ k, 1 ≤ k → k + 1 < ε₀ → Xk.XkLaySys S k` is FALSE at every such k: Xk.XkVD k is empty
(field ix_mem at a = 1, b = γ + 1: Cl(1, b) ∩ Ω₂ ⊆ Γ(1), Yc.ycCl1_lt).  Replaced by skLaySysY (repaired interface). -/
theorem skLaySys_false (S : InaccSeq.{0}) : ∀ k, 1 ≤ k → k + 1 < ε₀ → ¬ Xk.XkLaySys S k :=
  fun _ hk hke => Yc.ycLaySys_false_eps S hk hke

/-- STATUS: PROVED (Yc.ycVD_empty, Yc.ycC_empty; round 126, new node)
SIZE: S
NO-GO: no Xk.XkVD k exists for 1 ≤ k, k + 1 ≤ G; no Xk.XkC k has a bound above Γ(1) (k arbitrary). -/
theorem skLayEmpty (S : InaccSeq.{0}) :
    (∀ k, 1 ≤ k → k + 1 ≤ Gc.gcG 0 → Xk.XkVD k → False) ∧ (∀ k (C : Xk.XkC k), Gc.gcG 1 < C.Bd → False) :=
  ⟨fun _ hk hkG D => Yc.ycVD_empty S hk hkG D, fun _ C h => Yc.ycC_empty S C h⟩

/-- STATUS: PROVED (Yc.ycHg_noLay, Yc.ycGood_F_lt, Yc.ycRelab_gap, Yc.ycRelab_mixed, Yc.ycVD_codes; round 126, new)
SIZE: S
ROUTES (a) and (b) are no transfers: (a) no Hg.HgVD (the output of Ws.wsSysAll) has bound ≥ φ(ℓ, Γ(k)+1), k ≥ 1, and
every raw datum good for Ws.wsFam is below Γ(1); (b) an order-preserving map keeping the codes below G and sending
G ↦ Γ(k) has no value in [G, Γ(k)) and (moving sums) misses Γ(k) + G, while every repaired system of the layer has
both kinds of codes below its bound. -/
theorem skLayNoTransfer :
    (∀ (V : Hg.HgVD) k ℓ, 1 ≤ k → ¬ veblen ℓ (Gc.gcG k + 1) ≤ V.B) ∧
    (∀ (C : Ws.WsC) (r : Wo.WoR) ℓ, Ws.WsGood C r ℓ → r.F < Gc.gcG 1) ∧
    (∀ s : Ordinal.{0} → Ordinal.{0}, StrictMono s → (∀ c, c < Gc.gcG 0 → s c = c) → ∀ k, 1 ≤ k →
      s (Gc.gcG 0) = Gc.gcG k → (∀ c, ¬ (Gc.gcG 0 ≤ s c ∧ s c < Gc.gcG k)) ∧
      ((∀ d, s (Gc.gcG 0 + d) = Gc.gcG k + s d) → ∀ c, s c ≠ Gc.gcG k + Gc.gcG 0)) :=
  ⟨fun V _ _ hk => Yc.ycHg_noLay V hk, fun _ _ _ h => Yc.ycGood_F_lt h,
    fun _ hs hlow _ hk hG => ⟨Yc.ycRelab_gap hs hlow hG, fun hadd => Yc.ycRelab_mixed hs hlow hk hG hadd⟩⟩

/-- STATUS: PROVED (Yc.ycLayFront: the construction of Xx.xxVRS for Yc.YcVD; round 126, new node)
SIZE: L
THE REPAIRED FRONTIER LEMMA OVER Γ(k): for every repaired system D : Yc.YcVD k (hull fields for k < a) with gate below
K, UPPER ∧ LOWER ∧ CapV below ι(Γ(B_D)·ω); every k + 1 < ε₀ (k = 0: Yc.ycLayFront_zero, region A2). -/
theorem skLayFrontY (S : InaccSeq.{0}) : ∀ k, k + 1 < ε₀ → Yc.YcLayFront S k :=
  fun _ hk => Yc.ycLayFront S hk

/-- STATUS: PROVED (Yc.ycGood_base; round 126, new node)
SIZE: M
THE G-SPECIFIC FACTS OF THE FAMILY, OVER Γ(k): the raw datum Γ(k) (reading Γ_{x+1+k}, gate 0, outer low field of C)
has every field of Ws.WsGood with Γ(k), Γ(k+1), Γ_{x+2+k}, the atoms {Γ(k') : k' ≤ k} and the hull fields for k < a,
up to every level of every repaired code interface over Γ(k) with the base facts of Γ(k). -/
theorem skLayGood : ∀ k (C : Yc.YcC k), Yc.YcCG C → k + 1 < ε₀ → ∀ ℓ, Yc.YcLev C ℓ → Yc.YcGood C (Yc.ycRk C) ℓ :=
  fun _ _ hG hk _ hℓ => Yc.ycGood_base hG hk hℓ

/-- STATUS: PROVED (Yc.ycSysAll_zero = Ws.wsSysAll; round 126, new node)
SIZE: S
the family statement over Γ(0) = G (instance k = 0 of skLaySysAll1's statement). -/
theorem skLaySysAll0 : Yc.YcSysAll 0 := Yc.ycSysAll_zero

/-- STATUS: PROVED (Yc.ycLevAll1: Yc.ycC1, Yc.ycCG1, Yc.ycCls1, Xu.xuCn, Xu.xuClsN, Xu.xu_t_lev, Xu.xuGg_t; round 126)
SIZE: M
THE LEVEL SIDE AT k = 1: for every ℓ < Γ(1) a repaired code interface over Γ(1) (an (A3) interface Xu.xuCn (n+1) with
the outer low field Yc.ycZo 1), its classification, and a level t_n ≥ ℓ of gate 1 < K. -/
theorem skLayLevAll1 (S : InaccSeq.{0}) : Yc.YcLevAll S 1 := Yc.ycLevAll1 S

/-- STATUS: OPEN, OFF THE ROAD (round 127: skLayLo uses skLayLoD; round 126, new node; REFUTE FIRST: NO EVIDENCE)
SIZE: L
THE FAMILY STATEMENT OVER Γ(1) (Ws.wsSysAll with the raw datum Γ(1), the output Yc.YcVD 1): for every repaired code
interface over Γ(1) with the base facts of Γ(1) and a classification below L, a repaired system with bound φ(ℓ, Γ(1)+1)
and gate ≤ g ℓ at every level ℓ < L.  Its inputs over Γ(1) are proved (skLayGood, Xk.XkVD.pkg / Yc.YcVD.pkg for IMG,
Gb.gq_pi, Xx.XxGq); what is missing is the system recursion itself with the output type over Γ(1) (the Hn / Ho / Hg /
Wm / Wh / Wo / Ws stacks have Γ(1), Γ_{x+2}, {G} and 0 < a built into their types).  Non-vacuity: the hypotheses hold
for every Ws.WsC (Yc.ycC1, Yc.ycCG1, Yc.ycCls1); the instance k = 0 is skLaySysAll0. -/
theorem skLaySysAll1 : Yc.YcSysAll 1 := by
  sorry

/-- STATUS: OPEN, OFF THE ROAD (round 127: skLayLo uses skLayLoD; round 126, new node)
SIZE: L
k ≥ 2: the family statement over Γ(k) and the level side over Γ(k) (code interfaces for the levels in [Γ(1), Γ(k)),
i.e. the readings of the codes of the layers 1 … k−1). -/
theorem skLaySysYHi (S : InaccSeq.{0}) : ∀ k, 1 ≤ k → k ≠ 1 → k + 1 < ε₀ → Yc.YcSysAll k ∧ Yc.YcLevAll S k := by
  sorry

/-- STATUS: REDUCED, OFF THE ROAD (round 127: skLayLo uses skLayLoD) (Yc.ycLaySys1_of, Yc.ycLaySys_of, skLaySysAll1,
skLayLevAll1, skLaySysYHi; round 126, new node)
SIZE: L
THE REPAIRED skLaySys: for every ℓ < Γ(k) a repaired system D : Yc.YcVD k with φ(ℓ, Γ(k)+1) ≤ B_D and gate below K
(k = 0: Yc.ycLaySys_zero). -/
theorem skLaySysY (S : InaccSeq.{0}) : ∀ k, 1 ≤ k → k + 1 < ε₀ → Yc.YcLaySys S k := by
  intro k hk1 hk
  rcases eq_or_ne k 1 with rfl | hne
  · exact Yc.ycLaySys1_of S skLaySysAll1
  · obtain ⟨hA, hL⟩ := skLaySysYHi S k hk1 hne hk
    exact Yc.ycLaySys_of hA hL

/-- STATUS: PROVED (Yh.yhDirect; round 127, was OPEN L; REFUTE FIRST: NO EVIDENCE)
SIZE: L
ROUTE (c), DIRECT READINGS OF THE LAYER c: reading systems Xx.XxRS c (codes, gates, readings below Γ_{x+2+c}, EXACT,
limit data with IMG) whose codes with gate below K are cofinal below Γ(c+1).  Proved for every c with c + 1 < ε₀ by
ONE theorem: the reading Yh.yhR over all base atoms (Γ(i) read Γ_{x+1+i}, the shifted count Yh.yhPsi at every atom
level), with order, cofinality, Lemma EXACT, gates, hulls and limit data proved once (Yh.yhRSN), and the tower
Γ(c), yhPsi Γ(c) 0, … (gate 0) cofinal in Γ(c+1) (Yh.yhTw_cof).  Imports the round-127 modules: checkable after the
merge.  Non-vacuity: c = 0 gives Yc.ycDirect_A2 again (Yh.yhDirect_A2) and the whole layer 0 (Yh.yhDirect0). -/
theorem skLayDirect (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c + 1 < ε₀ → Yc.YcDirect S c (Gc.gcG (c + 1)) :=
  fun c _ hce => Yh.yhDirect S c hce

/-- STATUS: PROVED (Yh.yhDirect0, Yh.yhDirect; round 127, new node)
SIZE: M
route (c) at c = 0 for the WHOLE layer 0 (every B < Γ(1)), from the Xu reading (Yh.yhRS) and from the generic
reading (Yh.yhDirect). -/
theorem skLayDirect0 (S : InaccSeq.{0}) : Yc.YcDirect S 0 (Gc.gcG 1) := Yh.yhDirect0 S

/-- STATUS: PROVED (Yc.ycDirect_A2; round 126, new node; round 127: also the instance c = 0 of Yh.yhDirect,
Yh.yhDirect_A2)
SIZE: S
non-vacuity of route (c): direct readings below φ(G, 1) over G (region A2, through Xx.xxVRS). -/
theorem skLayDirectA2 (S : InaccSeq.{0}) : Yc.YcDirect S 0 (veblen (Gc.gcG 0) 1) := Yc.ycDirect_A2 S

/-- STATUS: PROVED (Yc.ycLay_of_direct, skLayDirect; round 126, new node; round 127: on the road of skLayLo)
SIZE: S
route (c) for the OLD levels: skLayDirect gives the conclusion of skLayLo at every c with c + 1 < ε₀ (an alternative
to skLaySysY + skLayFrontY). -/
theorem skLayLoD (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c + 1 < ε₀ → ∀ l, Cd.CdRange S l →
    (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  rintro c hc1 hce l hr ⟨ℓ, hℓ, hl⟩
  exact Yc.ycLay_of_direct (skLayDirect S c hc1 hce) l hr ⟨ℓ, hℓ.trans (Gc.gcG_lt (lt_add_one c)), hl⟩

/-- STATUS: PROVED (Yr.yrLayAll; round 129, new node; REFUTE FIRST at c = ε₀, ε₀ + 1: NO EVIDENCE)
SIZE: L
EVERY LAYER c BELOW B_Γ (c + 1 < ε₀ or not), old and new levels at once: UPPER ∧ LOWER ∧ CapV at every range
restart below ι(Γ(φ(ℓ, Γ(c)+1))·ω), ℓ < Γ(c+1).  One theorem Yr.yrDirect (YrDirect S B_Γ): the reading Yr.yrR with
read atom indices (Γ(i) read Γ_{x+1+i(x)}), admissible readings (Yr.YrN), Lemma IMG at every read bound (Yr.yrImg),
order, cofinality, Lemma EXACT, gates, hulls and limit data below B_Γ, and the tower G, Γ(G), … (gate 0) cofinal in
B_Γ.  Imports the round-129 modules: checkable after the merge.  Non-vacuity: c = ε₀ (Yr.yrDirect_eps0). -/
theorem skLayBelowBG (S : InaccSeq.{0}) : ∀ c, c < Tf.tfBG → ∀ l, Cd.CdRange S l →
    (∃ ℓ, ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l :=
  fun _ hc l hr hex => Yr.yrLayAll S hc l hr hex

/-- STATUS: OPEN (round 133, new node; REFUTE FIRST at the offset B_Γ²·2 + 1 and at the code ε_{B_Γ+1}: NO EVIDENCE,
skZmRef)
SIZE: L
DIRECT READINGS FOR EVERY ATOM INDEX B_Γ ≤ B < X (X = Tl.tlX).  PROVED below ζ_{B_Γ+1} = φ(2, B_Γ+1)
(skZmDirectZ: the generic hereditary step Zm.ZmDS.step, the gated interface (base gate Zm.ZmDS.Eg, Zm.ZmDS.raise),
the global reading with code indices Zm.zmHR, and one transfinite induction over every code index c < ζ_{B_Γ+1},
Zm.zmGood2_all: step at successors, union Zm.zmCU at limits).  Next Lean statement: the same chain over any
pseudo-base P = φ(2, b) read φ(2, D(x) + b(x)) (codes in [P, φ(2, b+1)) are the brackets φ(1, P + n)), i.e. a
level-generic version of Zm.ZmGood2 with the level α of φ(α, ·) a parameter, by induction on α up to the next
fixed point of Γ (closes the layer c = B_Γ), then the atoms of kind β ≥ 1 (Yw.ywV). -/
theorem skZbDirectX (S : InaccSeq.{0}) : Zb.ZbDirect S Tl.tlX := by
  sorry

/-- STATUS: PROVED (Zm.ZmDS.direct, Zm.ZmDS.step; round 133, new node)
SIZE: M
THE GENERIC HEREDITARY STEP: for a digit system Zm.ZmDS at a base E > B_Γ with base gate below K, the step to the
base ε_{E+1} is again a digit system (codes E^k·d + r read V^{R(k)}·R(d) + R(r)) with the same base gate, and it
gives ZbDirect S ε_{E+1} (its tower has small gates, Zm.ZmDS.step_gc0). -/
theorem skZmStep (S : InaccSeq.{0}) : ∀ M : Zm.ZmDS, Tf.tfBG < M.E → M.Eg < Td.tdK S →
    M.step.E = eN M.E ∧ Zb.ZbDirect S M.step.E :=
  fun M h hK => ⟨rfl, M.step.direct S (h.trans (lt_eN _)) hK M.step_gc0⟩

/-- STATUS: PROVED (Zm.zmDirectZ; round 133, new node)
SIZE: L
DIRECT READINGS FOR EVERY INDEX B_Γ ≤ B < ζ_{B_Γ+1} = φ(2, B_Γ+1): one transfinite induction over the code indices
c < ζ_{B_Γ+1} (Zm.zmGood2_all; base φ(1, B_Γ + c) read φ(1, D(x) + R(c)(x)), gate of c raised into the system),
the tower Zm.zmIt of small-gate indices cofinal in ζ_{B_Γ+1}. -/
theorem skZmDirectZ (S : InaccSeq.{0}) : Zb.ZbDirect S (veblen 2 (Tf.tfBG + 1)) := Zm.zmDirectZ S

/-- STATUS: PROVED (Zm.zmUVZ; round 133, new node)
SIZE: L
UPPER ∧ LOWER ∧ CapV at every range restart below ι(Γ_{Ω₁+1+B}·ω) for every B < ζ_{B_Γ+1} (frontier
ι(Γ_{ζ_{B_Γ+1}})). -/
theorem skZmFrontZ (S : InaccSeq.{0}) : ∀ B, B < veblen 2 (Tf.tfBG + 1) → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG B * ω) → SkUV S l :=
  fun _ hB _ hr hl => Zm.zmUVZ S hB hr hl

/-- STATUS: PROVED (Zm.zmDirectW; round 133, new node)
SIZE: L
DIRECT READINGS FOR EVERY INDEX B_Γ ≤ B < ε_{B_Γ+ω}: the chain Zm.zmCh n of digit systems at the bases ε_{B_Γ+n}. -/
theorem skZmDirectW (S : InaccSeq.{0}) : Zb.ZbDirect S (veblen 1 (Tf.tfBG + ω)) := Zm.zmDirectW S

/-- STATUS: PROVED (Zm.zmDirectE0; round 133, new node)
SIZE: L
DIRECT READINGS FOR EVERY INDEX B_Γ ≤ B < ε_{B_Γ+ε₀}: one transfinite induction over the constant indices ν < ε₀
(Zm.zmGood_all: step at successors, union Zm.zmU at limits, global reading Zm.zmGR). -/
theorem skZmDirectE0 (S : InaccSeq.{0}) : Zb.ZbDirect S (veblen 1 (Tf.tfBG + ε₀)) := Zm.zmDirectE0 S

/-- STATUS: PROVED (Zm.zmUVE0; round 133, new node)
SIZE: L
UPPER ∧ LOWER ∧ CapV at every range restart below ι(Γ_{Ω₁+1+B}·ω) for every B < ε_{B_Γ+ε₀} (frontier
ι(Γ_{ε_{B_Γ+ε₀}})). -/
theorem skZmFrontE0 (S : InaccSeq.{0}) : ∀ B, B < veblen 1 (Tf.tfBG + ε₀) → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG B * ω) → SkUV S l :=
  fun _ hB _ hr hl => Zm.zmUVE0 S hB hr hl

/-- STATUS: PROVED (Zm.zmRef1, Zm.zmRef1_nonfix, Zm.zmRef2, Zm.zmRef2_nonfix; round 133, new node)
SIZE: S
REFUTE FIRST for the generic step: the offset B_Γ²·2 + 1 reads D(x)²·2 + 1 with gate 2 and its index is no fixed
point of Γ; the code ε_{B_Γ+1} reads ε_{D(x)+1} = ϑˣ(Ω₁ + D(x)) and its index is no fixed point of Γ: NO
EVIDENCE. -/
theorem skZmRef : (∀ x, (Zm.zmCh 1).R (Tf.tfBG ^ (2 : Ordinal.{0}) * 2 + 1) x =
      Yw.ywV 1 0 x ^ (2 : Ordinal.{0}) * 2 + 1) ∧
    (∀ x, InE x → x < Om1 → (Zm.zmCh 2).R (eN Tf.tfBG) x = Gl.glA 1 (Yw.ywV 1 0 x) x) ∧
    Om1 + 1 + (Tf.tfBG + 1 + eN Tf.tfBG) < gamma (Om1 + 1 + (Tf.tfBG + 1 + eN Tf.tfBG)) :=
  ⟨fun x => (Zm.zmRef1 x).1, fun _ hx hx1 => (Zm.zmRef2 hx hx1).2.1, Zm.zmRef2_nonfix⟩

/-- STATUS: REDUCED (round 133: skZbDirectX, Zb.zbDirect_mono; was OPEN L, round 131; REFUTE FIRST at c = B_Γ and
against Zb.zbGsCS_lt_BG: NO EVIDENCE; round 132: every index below B_Γ·B_Γ PROVED; round 133: every index below
ε_{B_Γ+ε₀} PROVED, skZmDirectE0)
SIZE: L
DIRECT READINGS PAST B_Γ BELOW X: for every layer B_Γ ≤ c < X, a layer (gate below K) for every atom index
B_Γ ≤ B < Γ(c+1) whose top reads a code T ≥ Γ_{Ω₁+1+B} with the atoms of Zb.zbU, with terms below it.  Since
Γ(c+1) < X for c < X, it is the statement ZbDirect S X (skZbDirectX). -/
theorem skZbDirect (S : InaccSeq.{0}) : ∀ c, Tf.tfBG ≤ c → c < Tl.tlX → Zb.ZbDirect S (Gc.gcG (c + 1)) := by
  intro c _ hc B hB1 hB2
  have hc1 : c + 1 < Tl.tlX :=
    (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC Tl.tlX_SC)).add_one_lt hc
  exact skZbDirectX S B hB1 (hB2.trans (Zb.ZbRS.gcG_lt_X hc1))

/-- STATUS: OPEN (round 133, new node; REFUTE FIRST: NO EVIDENCE — the shape is satisfiable below X: Zm.ZmLayA
Zb.zbU S B holds for every B_Γ ≤ B < ε_{B_Γ+ε₀}, skZmDirectE0)
SIZE: L
THE LAYERS PAST X FROM ONE ATOM SYSTEM: for every layer X ≤ c < Ω₂ an abstract atom system A : Zb.ZbAS with a layer
(gate below K, top code read with the atoms of A, terms below it) for every atom index B < Γ(c+1) (Zm.ZmPastAt S c).
Needs an atom system past X (atoms ψ_{Ω₂}(e), e ≥ Ω₂^{Ω₂}; hull lemma below θ, Uf.uf_key / Vd.vd_nf_ex). -/
theorem skLayPastX (S : InaccSeq.{0}) : ∀ c, Tl.tlX ≤ c → c < Om (1 + 1) → Zm.ZmPastAt S c := by
  sorry

/-- STATUS: REDUCED (round 133: Zm.zmLay_of_past, skLayPastX; was OPEN L, round 131; REFUTE FIRST: NO EVIDENCE)
SIZE: L
skLayLoFix for the layers X ≤ c < Ω₂ (X = Tl.tlX = ψ_{Ω₂}(Ω₂^{Ω₂})): the atom system zbU has the bound X; past X
the atoms ψ_{Ω₂}(e) with e ≥ Ω₂^{Ω₂} (levels Ω₁²·γ + …, H_γ, Uc.ucDat) need another atom system with its hull
lemma (Uf.uf_key / Vd.vd_nf_ex below θ): skLayPastX. -/
theorem skLayLoFixX (S : InaccSeq.{0}) : ∀ c, Tl.tlX ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  intro c hc1 hc2 l hr _ hex
  obtain ⟨ℓ, hℓ, hl⟩ := hex
  exact Zm.zmLay_of_past (skLayPastX S c hc1 hc2) l hr ⟨ℓ, hℓ.trans (Gc.gcG_lt (lt_add_one c)), hl⟩

/-- STATUS: REDUCED (round 131: Zb.zbLay_of_direct, skZbDirect, skLayLoFixX; round 129, was OPEN L; round 130:
REFUTE FIRST at c = B_Γ and at the second fixed point of Γ: NO EVIDENCE — the base atoms Γ(B_Γ) = B_Γ, Γ(B₂) = B₂
read ϑˣ(Ω₁·Ω₁+Ω₁+ν(x)) (level 1, Yw.ywBG, Yw.ywKind); the reading ϑˣ(Ω₁·Ω₁·2 + ν) is REFUTED (skFixReadX_false))
SIZE: L
the old levels of the layers B_Γ ≤ c < Ω₂ (the index c of the atom Γ(c) is at or past the least fixed point B_Γ of
Γ, so the recursion i < Γ(i) of Yr.yrR stops; the fixed points of Γ are atoms of kind 1, read as the points of
level 1, ϑˣ(Ω₁·(Ω₁+1) + σ)).  c < X: direct readings past B_Γ (skZbDirect, Zb.zbLay_of_direct); X ≤ c: skLayLoFixX. -/
theorem skLayLoFix (S : InaccSeq.{0}) : ∀ c, Tf.tfBG ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  intro c hc1 hc2 l hr hP hex
  by_cases hcX : c < Tl.tlX
  · obtain ⟨ℓ, hℓ, hl⟩ := hex
    exact Zb.zbLay_of_direct (skZbDirect S c hc1 hcX) l hr ⟨ℓ, hℓ.trans (Gc.gcG_lt (lt_add_one c)), hl⟩
  · exact skLayLoFixX S c (not_lt.1 hcX) hc2 l hr hP hex

/-- STATUS: REDUCED (skLayBelowBG (PROVED round 129), skLayLoFix; round 123, was OPEN L; REFUTE FIRST at c = ε₀,
ε₀ + 1: NO EVIDENCE)
SIZE: L
the old levels of the layers c with ε₀ ≤ c + 1 (base atoms Γ(c) that are not constants below ε₀). -/
theorem skLayLoBig (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ε₀ ≤ c + 1 → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  intro c _ hc2 _ l hr hP hex
  by_cases hcB : c < Tf.tfBG
  · obtain ⟨ℓ, hℓ, hl⟩ := hex
    exact skLayBelowBG S c hcB l hr ⟨ℓ, hℓ.trans (Gc.gcG_lt (lt_add_one c)), hl⟩
  · exact skLayLoFix S c (not_lt.1 hcB) hc2 l hr hP hex

/-- STATUS: REDUCED (skLayLoD, skLayLoBig; round 127: the branch c + 1 < ε₀ now goes through the PROVED route (c)
skLayDirect, so skLaySysY, skLaySysAll1, skLaySysYHi are OFF THE ROAD; round 126: Yc.ycLayLo_of, skLaySysY)
SIZE: L
the layer c, OLD levels ℓ < Γ(c) over the base Γ(c) (system bounds φ(ℓ, Γ(c)+1); for c = 1 the levels of
(A1) ∪ (A2) ∪ (A3) again, now over Γ(1) read Γ_{x+2}; needs: a code interface like Ws.WsC with the base fields of
Γ(c) in place of Ws.WsCG and readings < gq (c+1) x, IMG below gq (c+1) ρ (skL1Img), the gated frontier lemma
(Gs.gsEnum / Gs.gsCapV) with the atom set {Γ(c') : c' ≤ c}, and the Ws.wsFam recursion over the levels). -/
theorem skLayLo (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Xh.XhPast S c l →
    (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  intro c hc1 hc2 l hr hP hex
  by_cases hce : c + 1 < ε₀
  · exact skLayLoD S c hc1 hce l hr hex
  · exact skLayLoBig S c hc1 hc2 (not_lt.1 hce) l hr hP hex

/-- STATUS: REDUCED (round 133: Zm.zmLay_of_past, skLayPastX; was OPEN L, round 131; REFUTE FIRST: NO EVIDENCE)
SIZE: L
skLayHiFix for the layers X ≤ c < Ω₂ (see skLayLoFixX): skLayPastX. -/
theorem skLayHiFixX (S : InaccSeq.{0}) : ∀ c, Tl.tlX ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∀ ℓ, ℓ < Gc.gcG c → Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω) ≤ l) →
    (∃ ℓ, Gc.gcG c ≤ ℓ ∧ ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) →
    SkUV S l := by
  intro c hc1 hc2 l hr _ _ hex
  obtain ⟨ℓ, -, hℓ, hl⟩ := hex
  exact Zm.zmLay_of_past (skLayPastX S c hc1 hc2) l hr ⟨ℓ, hℓ, hl⟩

/-- STATUS: REDUCED (round 131: Zb.zbLay_of_direct, skZbDirect, skLayHiFixX; round 129, was OPEN L; round 130:
REFUTE FIRST at c = B_Γ and at the second fixed point of Γ: NO EVIDENCE, see skLayLoFix)
SIZE: L
skLayHi for the layers B_Γ ≤ c < Ω₂ (see skLayLoFix). -/
theorem skLayHiFix (S : InaccSeq.{0}) : ∀ c, Tf.tfBG ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∀ ℓ, ℓ < Gc.gcG c → Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω) ≤ l) →
    (∃ ℓ, Gc.gcG c ≤ ℓ ∧ ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) →
    SkUV S l := by
  intro c hc1 hc2 l hr hP hlo hex
  by_cases hcX : c < Tl.tlX
  · obtain ⟨ℓ, -, hℓ, hl⟩ := hex
    exact Zb.zbLay_of_direct (skZbDirect S c hc1 hcX) l hr ⟨ℓ, hℓ, hl⟩
  · exact skLayHiFixX S c (not_lt.1 hcX) hc2 l hr hP hlo hex

/-- STATUS: PROVED (Zb.zbGsCS_lt_BG; round 131, new node)
SIZE: S
NO-GO for the round-130 next step "a code system Gs.GsCS whose bound passes B_Γ": every Gs.GsCS has its bound below
B_Γ (its law ψ_{Ω₂}(c) = Γ_{Ω₁+1+c} for c ≤ B meets the plateau ψ_{Ω₂} = B_Γ on [B_Γ, Ω₂]); so no Yr.YrRS has a code
≥ B_Γ. -/
theorem skZbGsNoGo (S : InaccSeq.{0}) (K : Gs.GsCS) : K.B < Tf.tfBG := Zb.zbGsCS_lt_BG S K

/-- STATUS: PROVED (Zb.zbKind1, Zb.zbKindW, Zb.zbKindW_pi; round 131, new node)
SIZE: S
REFUTE FIRST for the reading "a code atom of kind b, index c reads ϑˣ(Ω₁·(Ω₁+b(x))+c(x))" at kind 1, index 0 (B_Γ)
and at kind ω, index 0: both readings are the least points of their kinds above x, not closed under their own level,
and (kind ω) above every point of finite level below it, with Lemma EXACT: NO EVIDENCE. -/
theorem skZbKind : ∀ x, InE x → x < Om1 →
    (x < Yw.ywV 1 0 x ∧ Yw.YwC x 1 (Yw.ywV 1 0 x) ∧ (∀ p, x < p → Yw.YwC x 1 p → Yw.ywV 1 0 x ≤ p) ∧
      ¬ Yw.YwC x (1 + 1) (Yw.ywV 1 0 x)) ∧
    (x < Yw.ywV ω 0 x ∧ Yw.YwC x ω (Yw.ywV ω 0 x) ∧ (∀ p, x < p → Yw.YwC x ω p → Yw.ywV ω 0 x ≤ p) ∧
      ¬ Yw.YwC x (ω + 1) (Yw.ywV ω 0 x)) :=
  fun _ hx hx1 => ⟨Zb.zbKind1 hx hx1, (Zb.zbKindW hx hx1).1, (Zb.zbKindW hx hx1).2.1, (Zb.zbKindW hx hx1).2.2.1,
    (Zb.zbKindW hx hx1).2.2.2.1⟩

/-- STATUS: PROVED (Zb.zbDirect_e0; round 131, new node)
SIZE: L
NON-VACUITY of skZbDirect: direct readings for every atom index B_Γ ≤ B < B_Γ + ε₀ (the code B_Γ: Yw.ywBGB; the
indices B_Γ + 1 + o, o < ε₀: the reading system Zb.zbE0, top ϑˣ(Ω₁·Ω₁ + D(x) + o)). -/
theorem skZbDirectE0 (S : InaccSeq.{0}) : Zb.ZbDirect S (Tf.tfBG + ε₀) := Zb.zbDirect_e0 S

/-- STATUS: PROVED (Zb.zbUV_e0; round 131, new node)
SIZE: L
THE FIRST FRONTIERS PAST B_Γ: UPPER ∧ LOWER ∧ CapV at every range restart below ι(Γ_{Ω₁+1+B}·ω) for every
B < B_Γ + ε₀ (the frontier ι(Γ_{B_Γ+ε₀}); Yr.yrLayAll stops below ι(B_Γ)). -/
theorem skZbFront (S : InaccSeq.{0}) : ∀ B, B < Tf.tfBG + ε₀ → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG B * ω) → SkUV S l :=
  fun _ hB _ hr hl => Zb.zbUV_e0 S hB hr hl

/-- STATUS: PROVED (Zg.zgYr; round 132, new node)
SIZE: S
(1′) EVERY Yr CODE o < B_Γ WITH GATE BELOW Z IS A CODE OF TlCl Z (the TlCl versions of Gf.gfW_mem, Gi.gw_mulOm_mem,
Gl.gl_mem, Yr.yr_mem), so the atom Γ_{Ω₁+1+(B_Γ+1+o)} is an atom of Zb.zbU over Z (Zg.zgAtom). -/
theorem skZgTl : ∀ Z o, 0 < Z → o < Tf.tfBG → Yr.yrG o < Z → Tl.TlCl Z o :=
  fun _ o hZ ho hg => (Zg.zgYr hZ o ho hg).1

/-- STATUS: PROVED (Zg.zgDirectW; round 132, new node)
SIZE: L
DIRECT READINGS FOR EVERY INDEX B_Γ ≤ B < B_Γ·ω: the reading systems Zg.zgB2 (offsets o < B_Γ, reading
D(x) + Yr.yrR o x) and Zg.zgBw (offsets B_Γ·n + r, reading D(x)·(1+n) + Yr.yrR r x), gates through Yr.yrTw. -/
theorem skZgDirectW (S : InaccSeq.{0}) : Zb.ZbDirect S (Tf.tfBG * ω) := Zg.zgDirectW S

/-- STATUS: PROVED (Zg.zgDirectSq; round 132, new node)
SIZE: L
DIRECT READINGS FOR EVERY INDEX B_Γ ≤ B < B_Γ·B_Γ: the reading system Zg.zgSq (offsets B_Γ·q + r, q, r < B_Γ Yr
codes, reading D(x)·(1 + Yr.yrR q x) + Yr.yrR r x; EXACT by Zg.zgOpowD and Yr.yr_dig, cover inversion Zg.zgDig). -/
theorem skZgDirectSq (S : InaccSeq.{0}) : Zb.ZbDirect S (Tf.tfBG * Tf.tfBG) := Zg.zgDirectSq S

/-- STATUS: PROVED (Zg.zgUVSq; round 132, new node)
SIZE: L
UPPER ∧ LOWER ∧ CapV at every range restart below ι(Γ_{Ω₁+1+B}·ω) for every B < B_Γ·B_Γ (frontier ι(Γ_{B_Γ²})). -/
theorem skZgFrontSq (S : InaccSeq.{0}) : ∀ B, B < Tf.tfBG * Tf.tfBG → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG B * ω) → SkUV S l :=
  fun _ hB _ hr hl => Zg.zgUVSq S hB hr hl

/-- STATUS: PROVED (Zg.zgUVW; round 132, new node)
SIZE: L
UPPER ∧ LOWER ∧ CapV at every range restart below ι(Γ_{Ω₁+1+B}·ω) for every B < B_Γ·ω (frontier ι(Γ_{B_Γ·ω})). -/
theorem skZgFrontW (S : InaccSeq.{0}) : ∀ B, B < Tf.tfBG * ω → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG B * ω) → SkUV S l :=
  fun _ hB _ hr hl => Zg.zgUVW S hB hr hl

/-- STATUS: PROVED (Zg.zgRef1, Zg.zgRefW, Zg.zgRef2, Zg.zgRef2_nonfix; round 132, new node)
SIZE: S
REFUTE FIRST for the readings past B_Γ: at the offsets 1 and ω the reading D(x) + yrR o x agrees with Zb.zbE0, at the
offset B_Γ (index B_Γ·2) the reading is D(x)·2 and the index is no fixed point of Γ: NO EVIDENCE. -/
theorem skZgRef : (∀ x, Zg.zgR2 (Tf.tfBG + 1 + 1) x = Zb.zbR0 (Tf.tfBG + 1 + 1) x) ∧
    (∀ x, Zg.zgR2 (Tf.tfBG + 1 + ω) x = Zb.zbR0 (Tf.tfBG + 1 + ω) x) ∧
    (∀ x, Zg.zgRw (Tf.tfBG + Tf.tfBG) x = Yw.ywV 1 0 x * 2) :=
  ⟨fun x => (Zg.zgRef1 x).2, fun x => (Zg.zgRefW x).2, Zg.zgRef2⟩

/-- STATUS: REFUTED (Yw.ywFirstFix_ref; round 130, new node)
SIZE: S
the reading `B_Γ ↦ ϑˣ(Ω₁·Ω₁·2)` (the fixed points of Γ read `ϑˣ(Ω₁·Ω₁·2 + ν(x))`) is FALSE: at every ε-number base
x < Ω₁, `ϑˣ(Ω₁·Ω₁·2)` is not the least closed point of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` above x (`ϑˣ(Ω₁·Ω₁ + Ω₁)` is a smaller
one). -/
theorem skFixReadX_false : ∀ x, InE x → x < Om1 →
    ¬ ∀ p, x < p → Yw.YwClosed x p → vt x (Om1 * (Om1 * 2 + 0) + 0) ≤ p :=
  fun _ hx hx1 => Yw.ywFirstFix_ref hx hx1

/-- STATUS: PROVED (Yw.ywBG, Yw.ywKind; round 130, new node)
SIZE: M
THE READINGS OF THE ATOM KINDS: the least closed point of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` above x is `ϑˣ(Ω₁·Ω₁ + Ω₁)` (the
reading of B_Γ), and for every kind 1 ≤ β ∈ Tˣ ∩ Ω₁ the β-closed, not (β+1)-closed points of Tˣ ∩ (x, X^x) are
exactly the points `ϑˣ(Ω₁·(Ω₁+β) + σ)`. -/
theorem skFixKind : ∀ x, InE x → x < Om1 →
    (x < Yw.ywV 1 0 x ∧ Yw.YwClosed x (Yw.ywV 1 0 x) ∧ ∀ p, x < p → Yw.YwClosed x p → Yw.ywV 1 0 x ≤ p) ∧
    ∀ β p, 1 ≤ β → β ∈ Tset x → β < Om1 → p ∈ Tset x → x < p → p < Yw.ywX x →
      ((Yw.YwC x β p ∧ ¬ Yw.YwC x (β + 1) p) ↔ ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ Yw.ywV β σ x = p) :=
  fun _ hx hx1 => ⟨Yw.ywBG hx hx1, fun _ _ hβ1 hβT hβΩ hpT hxp hpX => Yw.ywKind hx hx1 hβ1 hβT hβΩ hpT hxp hpX⟩

/-- STATUS: PROVED (Yw.ywImg; round 130, new node)
SIZE: L
LEMMA IMG BELOW `X^ρ = ϑᵖ(Ω₁·Ω₁·2)` (every point of every level, the fixed points of Γ included, and every ε-number
between), at every restart triple. -/
theorem skFixImg : ∀ ρ τ δ, RstK ρ τ δ → ∀ v, v < Yw.ywX ρ → Gn.GnI ρ δ v :=
  fun _ _ _ h => Yw.ywImg h

/-- STATUS: PROVED (Yw.ywBGB, Yw.ywBG1B; round 130, new node)
SIZE: M
THE LAYERS OF THE CODES B_Γ AND B_Γ + 1: gated layers with gate 0 and tops `ϑˣ(Ω₁·Ω₁ + Ω₁)` (the union of the tower
layers, top witness from Lemma IMG) and `ϑˣ(Ω₁·Ω₁ + ϑˣ(Ω₁·Ω₁ + Ω₁))` (the ladder over it). -/
theorem skFixLayBG : ∃ B B' : Gd.GdB, B.g = 0 ∧ B'.g = 0 ∧ (∀ x, B.K.E x = Yw.ywV 1 0 x) ∧
    ∀ x, B'.K.E x = Gb.gq (Yw.ywV 1 0 x) x :=
  ⟨Yw.ywBGB, Yw.ywBG1B, Yw.ywBGB_g, Yw.ywBG1B_g, Yw.ywBGB_E, Yw.ywBG1B_E⟩

/-- STATUS: PROVED (Yw.ywNoGo_GqSt; round 130, new node)
SIZE: S
NO-GO for the interface of Yr.YrRS past B_Γ: no admissible offset ν (Yr.YrN) has `ϑˣ(Ω₁·Ω₁ + ν)` equal to a point of
level β ≥ 1, so no reading system with layer tops `gq (R c x) x` reads a fixed point of Γ. -/
theorem skFixNoGo : ∀ x ν β η, InE x → x < Om1 → Yr.YrN x ν → 0 < β → β ∈ Tset x → β < Om1 → η ∈ Tset x →
    η < Om1 → Gb.gq ν x ≠ Yw.ywV β η x :=
  fun _ _ _ _ hx hx1 hν hβ0 hβ hβΩ hη hηΩ => Yw.ywNoGo_GqSt hx hx1 hν hβ0 hβ hβΩ hη hηΩ

/-- STATUS: REDUCED (skLayBelowBG (PROVED round 129), skLayHiFix; round 126, was OPEN L; REFUTE FIRST at c = ε₀,
ε₀ + 1: NO EVIDENCE)
SIZE: L
skLayHi for the layers c with ε₀ ≤ c + 1. -/
theorem skLayHiBig (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ε₀ ≤ c + 1 → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∀ ℓ, ℓ < Gc.gcG c → Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω) ≤ l) →
    (∃ ℓ, Gc.gcG c ≤ ℓ ∧ ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) →
    SkUV S l := by
  intro c _ hc2 _ l hr hP hlo hex
  by_cases hcB : c < Tf.tfBG
  · obtain ⟨ℓ, -, hℓ, hl⟩ := hex
    exact skLayBelowBG S c hcB l hr ⟨ℓ, hℓ, hl⟩
  · exact skLayHiFix S c (not_lt.1 hcB) hc2 l hr hP hlo hex

/-- STATUS: REDUCED (Yc.ycLay_of_direct, skLayDirect (PROVED round 127), skLayHiBig; round 126, was OPEN L)
SIZE: L
the layer c, NEW levels Γ(c) ≤ ℓ < Γ(c+1) (levels containing the atom Γ(c); for c = 1 the analog of (A3) with the
atom Γ(1)). -/
theorem skLayHi (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Xh.XhPast S c l →
    (∀ ℓ, ℓ < Gc.gcG c → Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω) ≤ l) →
    (∃ ℓ, Gc.gcG c ≤ ℓ ∧ ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) →
    SkUV S l := by
  intro c hc1 hc2 l hr hP hlo hex
  by_cases hce : c + 1 < ε₀
  · obtain ⟨ℓ, -, hℓ, hl⟩ := hex
    exact Yc.ycLay_of_direct (skLayDirect S c hc1 hce) l hr ⟨ℓ, hℓ, hl⟩
  · exact skLayHiBig S c hc1 hc2 (not_lt.1 hce) l hr hP hlo hex

/-- STATUS: REDUCED (Xh.xhLay_red, skLayLo, skLayHi)
SIZE: L
every layer c ≥ 1 of (B-lo). -/
theorem skLay (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Xh.XhLay S c l →
    l < Bt.iota S (Om (1 + 1)) → SkUV S l := by
  intro c hc1 hc2 l hr hL _
  exact Xh.xhLay_red (S := S) (SkUV S) c (skLayLo S c hc1 hc2) (skLayHi S c hc1 hc2) l hr hL

/-- STATUS: REDUCED (Xh.xhRegBlo_of_lay, skLay; was OPEN L)
SIZE: L
(B-lo) the intended region (B): past (A), υ_λ < L(0), e(η) < Ω₂, λ < ι(Ω₂) (codes with atoms Γ(c), c ≥ 1;
names η < Ω₂). -/
theorem skRegBlo (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjNotA S l → upsilon l < Nc.ncL S 0 →
    Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → l < Bt.iota S (Om (1 + 1)) → SkUV S l :=
  Xh.xhRegBlo_of_lay (S := S) (SkUV S) (skLay S)

/-- STATUS: PROVED (Xh.xhBhi_iff, Xh.xhBhi_off)
SIZE: S
(B-hi) on names: Ω₂ ≤ η < Ω_ω, e(η) < Ω₂; η = Ω₂·q + ζ, 1 ≤ q, 0 < ζ < Ω₂, e(η) = e(ζ), code -1 + e(ζ). -/
theorem skBhiName (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      Bt.iota S (Om (1 + 1)) ≤ l) ↔
    (Om (1 + 1) ≤ Cd.cdEta S l ∧ Cd.cdEta S l < Om ω ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1)) :=
  Xh.xhBhi_iff hr

/-- STATUS: PROVED (Xh.xhBhi_nonempty)
SIZE: S
non-vacuity: (B-hi) contains range restarts. -/
theorem skBhiNonempty (S : InaccSeq.{0}) : ∃ l, Cd.CdRange S l ∧ Wj.WjNotA S l ∧
    upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧ Bt.iota S (Om (1 + 1)) ≤ l :=
  Xh.xhBhi_nonempty S

/-- The base data of the cell transport at `λ₀` (`R2.YfRel`): `Good O` at every block boundary up to
`λ₀ + ω²` and `O(λ₀) < δ_{λ₀}`. -/
def SkBase (O : Ordinal.{0} → Ordinal.{0}) (l0 : Ordinal.{0}) : Prop :=
  (∀ η, ω * ω * η ≤ l0 + ω * ω → Good O (ω * ω * η)) ∧ O l0 < upsilon (l0 + ω + 1)

/-- The cell condition at a (B-hi) restart named `Ω₂·q + ζ`. -/
def SkBhiCell (S : InaccSeq.{0}) (q ζ : Ordinal.{0}) : Prop :=
  ζ < Nm.Pv S (Om (1 + 1) * q) ∧ Bt.Good S (Om (1 + 1) * q) ∧ IsRestartIdx (Bt.iota S (Om (1 + 1) * q)) ∧
    (∃ η1, upsilon (Bt.iota S (Om (1 + 1) * q)) < Nm.Pv S η1) ∧
    ∃ O : Ordinal.{0} → Ordinal.{0}, SkBase O (Bt.iota S (Om (1 + 1) * q))

/-- STATUS: PROVED (Yf.yfStretch_UV; round 126, new; checked only after the merge)
SIZE: L
THE TRANSPORT THEOREM: base data at a restart index `λ₀`, no fixed point of `υ` in `(λ₀, B)` (`ω² ∣ B < Ω₁`) ⇒
every restart `λ₀ < λ < B` with a name has code `-1 + e(λ)`, `r(λ) = δ_λ + (-1 + e(λ))`, UPPER ∧ LOWER ∧ CapV. -/
theorem skCellUV (S : InaccSeq.{0}) {O : Ordinal.{0} → Ordinal.{0}} {l0 B l η1 : Ordinal.{0}}
    (hl0 : IsRestartIdx l0) (hB : ω * ω ∣ B) (hB1 : B < Om1) (hlB0 : l0 < B) (hb : SkBase O l0)
    (hfix : ∀ l, IsRestartIdx l → l0 < l → l < B → l < upsilon l)
    (hl : IsRestartIdx l) (h1 : l0 < l) (h2 : l < B) (hn : upsilon l < Nm.Pv S η1) :
    Cd.cdCode S l = Cd.cdOff (Cd.cdExp l) ∧ Cd.cdR S l = Cd.cdDelta l + Cd.cdOff (Cd.cdExp l) ∧ SkUV S l := by
  obtain ⟨hm, hR, hU, hL, hV⟩ := Yf.yfStretch_UV S hl0 hB hB1 hlB0 hb.1 hb.2 hfix hl h1 h2 hn
  exact ⟨hm, hR, hU, hL, hV⟩

/-- STATUS: PROVED (Yf.yfBase_wit; round 126, new)
SIZE: S
non-vacuity of the base data: they hold at `λ₀ = Λ_B` with `O = VzOrec`, and `Λ_B` has a name. -/
theorem skBaseWit (S : InaccSeq.{0}) :
    IsRestartIdx VzLam ∧ upsilon VzLam < Nm.Pv S (Om ω + Nc.ncPp S * 0) ∧ SkBase VzOrec VzLam :=
  ⟨(Yf.yfBase_wit S).1, (Yf.yfBase_wit S).2.1, (Yf.yfBase_wit S).2.2.1, (Yf.yfBase_wit S).2.2.2⟩

/-- STATUS: PROVED (Yf.yfGrid_UV; round 126, new; checked only after the merge)
SIZE: M
(B-hi, A-type cell, offsets below the base) the cell condition at `Ω₂·q` (`Ω₂·q` good, `ι(Ω₂·q)` a restart index
with a name and the base data, `ζ < P(Ω₂·q)`) ⇒ UPPER ∧ LOWER ∧ CapV at the range restart named `Ω₂·q + ζ`. -/
theorem skBhiAcell (S : InaccSeq.{0}) : ∀ l q ζ, Cd.CdRange S l → Cd.cdEta S l = Om (1 + 1) * q + ζ →
    ζ ≠ 0 → SkBhiCell S q ζ → SkUV S l := by
  rintro l q ζ hr he hζ0 ⟨hζ, hg, hri, ⟨η1, hn⟩, O, hb⟩
  have hX : upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := Lw.lw_L_eq S (ω + 1) ▸ hr.2.2.1
  have hι : Bt.iota S (Cd.cdEta S l) = l := (Cd.cdEta_pv_spec (S := S) hr.1.1 hX).2.1
  obtain ⟨-, -, hU, hL, hV⟩ := Yf.yfGrid_UV S hg hri hn hb.1 hb.2 hr.1 hι he hζ0 hζ
  exact ⟨hU, hL, hV⟩


/-- STATUS: PROVED (Wj.wjSplit, Wj.wjSplit_excl, Wj.wjWin_disj, Wj.wjWin_props, Wj.wjC_props)
SIZE: S
THE SPLIT: every range restart is in (A) ∨ (B-lo) ∨ (B-hi) ∨ (C) ∨ ∃k W_k ∨ W_ω, the pieces exclusive. -/
theorem skSplit (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : Cd.CdRange S l) :
    (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) ∨
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      l < Bt.iota S (Om (1 + 1))) ∨
    (Wj.WjNotA S l ∧ upsilon l < Nc.ncL S 0 ∧ Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) ∧
      Bt.iota S (Om (1 + 1)) ≤ l) ∨
    (upsilon l < Nc.ncL S 0 ∧ Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) ∨
    (∃ k : ℕ, Wj.WjWin S k l) ∨ Wj.WjTop S l :=
  Wj.wjSplit hr

/-- STATUS: PROVED (Wj.wjWin_nonempty)
SIZE: S
non-vacuity: every window W_k contains range restarts. -/
theorem skWinNonempty (S : InaccSeq.{0}) (k : ℕ) : ∃ l, Cd.CdRange S l ∧ Wj.WjWin S k l :=
  Wj.wjWin_nonempty k

/-! ## REDUCED nodes -/

/-- STATUS: PROVED (skLvOfGate, skDigitGate, skReadExact)
SIZE: M
∀ ℓ (Ω₁ ≤ ℓ, Ω₁ ∣ ℓ, ℓ < ε_{Ω₁+1}) ∃ level datum Λ: L = ℓ, l(x) = rdc ℓ x above g ≤ gtc ℓ. -/
theorem skLvDatum : SkLvDatumAll := skLvOfGate skDigitGate skReadExact

/-- STATUS: REPLACED (round 117: by skStepW2 on SkCohW2; its leaves skStepPowW / skStepExpLimW / skStepCoefLimW are
REPLACED; not used)
SIZE: M
∀ ℓ: the step at ℓ for SkAtW (every coherent family below ℓ extends to ℓ). -/
theorem skStep : ∀ ℓ, SkLev ℓ → SkStepAtW ℓ := by
  intro ℓ hℓ
  rcases skShape ℓ hℓ with h | h | h | h | h
  · subst h; exact skStepBaseW
  · exact skStepSuccW ℓ hℓ h
  · exact skStepPowW ℓ hℓ h
  · exact skStepExpLimW ℓ hℓ h
  · exact skStepCoefLimW ℓ hℓ h

/-- STATUS: PROVED (round 118: skFamW2, Wm.wmExtE_old; statement unchanged)
SIZE: M
∃ F: ∀ ℓ (SkLev): F ℓ at ℓ (SkAtW) ∧ ∀ ℓ' < ℓ (SkLev): F ℓ extends F ℓ'  (one generic induction over ℓ). -/
theorem skFam : ∃ F : Ordinal.{0} → SkEnt,
    ∀ ℓ, SkLev ℓ → SkAtW ℓ (F ℓ) ∧ ∀ ℓ', ℓ' < ℓ → SkLev ℓ' → SkExt (F ℓ') (F ℓ) :=
  ⟨Wo.woEnt, fun ℓ hℓ => ⟨(Wo.woFamW2 ℓ hℓ).1,
    fun ℓ' h h' => Wm.wmExtE_old ((Wo.woFamW2 ℓ hℓ).2 ℓ' h h')⟩⟩

/-- STATUS: PROVED (round 118: skFam; also Wo.woSysAll directly)
SIZE: M
∀ ℓ (SkLev) ∃ system V over G: B_V = φ(ℓ, G+1), γ_V ≤ gtc ℓ. -/
theorem skSysAll : ∀ ℓ, SkLev ℓ → ∃ V : Hg.HgVD, V.B = veblen ℓ (Gc.gcG 0 + 1) ∧ V.γ ≤ Gf.gtc ℓ := by
  intro ℓ hℓ
  obtain ⟨F, hF⟩ := skFam
  exact ⟨(F ℓ).2.down, (hF ℓ hℓ).1.2.2.1, (hF ℓ hℓ).1.2.2.2.1⟩

/-- STATUS: PROVED (round 118: skSysAll, skCofLev; Wo.woSysA1)
SIZE: M
(A1) ∀ B < φ(ε_{Ω₁+1}, G+1) ∃ system V: B ≤ B_V, γ_V < K. -/
theorem skSysA1 (S : InaccSeq.{0}) : ∀ B, B < veblen Gf.gfE (Gc.gcG 0 + 1) →
    ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  obtain ⟨ℓ, hℓ, hg, hBl⟩ := skCofLev S B hB
  obtain ⟨V, hVB, hVg⟩ := skSysAll ℓ hℓ
  exact ⟨V, hVB ▸ hBl, hVg.trans_lt hg⟩

/-- STATUS: PROVED (skSysA1, skSysA2, skSysA3; round 125, was REDUCED)
SIZE: L
∀ B < Γ(1) ∃ system V: B ≤ B_V, γ_V < K (REGION (A) CLOSED). -/
theorem skSysCof (S : InaccSeq.{0}) : ∀ B, B < Gc.gcG 1 → ∃ V : Hg.HgVD, B ≤ V.B ∧ V.γ < Td.tdK S := by
  intro B hB
  rcases lt_or_ge B (veblen Gf.gfE (Gc.gcG 0 + 1)) with h1 | h1
  · exact skSysA1 S B h1
  rcases lt_or_ge B (veblen (Gc.gcG 0) (Gc.gcG 0 + 1)) with h2 | h2
  · exact skSysA2 S B h1 h2
  · exact skSysA3 S B h2 hB

/-- STATUS: REDUCED (skSysCof, skLocOfSys)
SIZE: L
(A) ∀ range λ with λ < ι(Γ(B)·ω) for some B < Γ(1): UPPER ∧ LOWER ∧ CapV. -/
theorem skRegA (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l →
    (∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)) → SkUV S l := by
  rintro l hr ⟨B, hB, hl⟩
  obtain ⟨V, hBV, hγ⟩ := skSysCof S B hB
  refine skLocOfSys S V hγ l hr (hl.trans_le ?_)
  exact Bt.iota_mono (S := S) _ _ (mul_le_mul_left (Gc.gcG_le hBV) ω)

/-- STATUS: PROVED (skSplit, skRegA, skRegBlo, Wj.wjC_props; round 133, new; checked only after the merge)
SIZE: S
EVERY RANGE RESTART BELOW `ι(Ω₂)` IS IN (A) OR (B-lo): UPPER ∧ LOWER ∧ CapV there. -/
theorem skBCLow (S : InaccSeq.{0}) : ∀ μ, Cd.CdRange S μ → μ < Bt.iota S (Om (1 + 1)) → SkUV S μ := by
  intro μ hr hι
  have hP : upsilon μ < Nc.ncL S 0 :=
    (upsilon_normal.strictMono hι).trans_le ((Bt.ups_iota S _).trans_le (Ga.ga_Pv_lt_L0 S le_rfl).le)
  rcases skSplit S hr with hA | ⟨hn, hu, he, hi⟩ | ⟨-, -, -, hi⟩ | ⟨-, he⟩ | ⟨k, hw⟩ | hw
  · exact skRegA S μ hr hA
  · exact skRegBlo S μ hr hn hu he hi
  · exact absurd hi (not_le.2 hι)
  · exact absurd (Wj.wjC_props hr he).2.1 (not_le.2 hι)
  · exact absurd (hw.1.trans hP) (not_lt.2 (Pp.ppL_mono (S := S) zero_le))
  · exact absurd (hw.1.trans hP) (not_lt.2 (Pp.ppL_mono (S := S) zero_le))

/-- STATUS: OPEN (round 134, new leaf; the UPPER ∧ LOWER part of skBCBaseUV; round 135: SIZE M → L, a BIG reading)
SIZE: L
UPPER ∧ LOWER AT THE BASE `l₀ = Zo.zoBase S = ι(Ω₂)` (`Zr.zrBase_eq`): `ρ = P(Ω₂)`, the name `Ω₂`, the code
`π_{Ω₂}`, the predicted reach `r(l₀) = δ_{l₀} + Θ_{l₀}(π_{Ω₂})` with `Θ_{l₀}(π_{Ω₂}) ≤ ψ_{Ω₁}(A + θ + Ω₁) < δ_{l₀}`,
`A = Ω_ω + Ω₂` (`Zr.zrTh_Om2`, `Zr.zrBCThPos`; the points `δ + x` are closed, `Zh.zhDense`): a short reach, inside
the first block `(δ, υ_{l₀+ω·2+1})`.  LOWER asks `P(Ω₂) ≤₁ δ + Θ(π)`, UPPER asks not `P(Ω₂) ≤₁ δ + Θ(π) + 1`.  No
point below `ρ` is `≤₁` a point `≥ ρ` (`Zr.zrNoCross`).  REFUTE FIRST: NO EVIDENCE (part of the natural target).
Round 135 (skBCBaseBig): `l₀` is `υ`-fixed and its reading is BIG, `υ_{l₀+1} = Θ_{l₀}(θ) < Θ_{l₀}(π_{Ω₂})`
(`Zs.zsBig`), the case of skWinBig: the term, value and successor branches of the RS input give only LOWER itself
(`Zs.zsBaseRs_lower`) and the supply branch is false (`Zs.zsSup_false`: every restart below `l₀` reads short,
`Zs.zsShortLow`).  LOWER needs Lemma RS with a value `v ∈ [υ_{l₀+1}, δ_{l₀})` (the FRAG image of `v` on the
segment of `υ_{l₀+1}`; `Zn.znRs_rstV` takes values below `υ_{l₀+1}` only) and the code continuity at `l₀` for
these values; UPPER is Lemma TOP at a big reading (the short input of Lemma TOP takes only offsets `ρ·m + k`). -/
theorem skBCBaseUL (S : InaccSeq.{0}) : Cd.CdUpper S (Zo.zoBase S) ∧ Cd.CdLower S (Zo.zoBase S) := by
  sorry

/-- STATUS: PROVED (Zs.zsFix, Zs.zsBig, Zs.zsBaseRs_lower, Zs.zsSup_false; round 135, new node)
SIZE: S
REFUTE FIRST for skBCBaseUL as a known RS case: `l₀ = ι(Ω₂)` is `υ`-fixed with the BIG reading
`υ_{l₀+1} = ψ_{Ω₁}(A + θ) = Θ_{l₀}(θ) < Θ_{l₀}(π_{Ω₂})` (`θ = ψ_{Ω₂}(Ω_ω)` lies in the hull below `Ω₂`); the RS
inputs `ZcRsIn ∨ ZnRsVal` give only LOWER itself, and the supply branch is false (given the region below `ι(Ω₂)`,
skBCLow: the restarts below `l₀` read short, so none reaches `υ_{μ+ω+2}`). -/
theorem skBCBaseBig (S : InaccSeq.{0}) :
    upsilon (Zo.zoBase S) = Zo.zoBase S ∧
      upsilon (Order.succ (Zo.zoBase S)) < Cd.cdTheta S (Zo.zoBase S) (Cd.cdCode S (Zo.zoBase S)) ∧
      (Zc.ZcRsIn (Ys.ysO S) (Zo.zoBase S) ∨ Zn.ZnRsVal (Ys.ysO S) (Zo.zoBase S) →
        Cd.CdLower S (Zo.zoBase S)) ∧
      ∀ B, ¬ Zh.ZhSupInB S (Zo.zoBase S) B :=
  ⟨Zs.zsFix, Zs.zsBig, Zs.zsBaseRs_lower, Zs.zsSup_false fun μ hr h => skBCLow S μ hr h⟩

/-- STATUS: REDUCED (round 134: skBCBaseUL, and CapV PROVED, Zr.zrBaseCapV; was OPEN M, round 133)
SIZE: M
UPPER ∧ LOWER ∧ CapV AT THE BASE `l₀ = Zo.zoBase S = ι(Ω₂)`.  CapV: `r(l₀) = δ + Θ(π_{Ω₂}) < P(Ω₂ + Ω₂) ≤ cap(l₀)`
(`Zr.zrBaseCapV`, given UPPER ∧ LOWER ∧ CapV below `ι(Ω₂)`, skBCLow). -/
theorem skBCBaseUV (S : InaccSeq.{0}) : SkUV S (Zo.zoBase S) :=
  ⟨(skBCBaseUL S).1, (skBCBaseUL S).2, Zr.zrBaseCapV fun μ hr h => skBCLow S μ hr h⟩

/-- STATUS: PROVED (round 134, Zr.zrBCThPos, the short branch; new leaf of round 134, the reading part of skBCReach)
SIZE: M
THE READING OF THE BASE CODE (notation only, no `≤₁`): `Θ_{l₀}(m_{l₀}) < δ_{l₀}` (short reach) or
`υ_{l₀+ω²} ≤ Θ_{l₀}(m_{l₀})` (long reach).  Round 134: `l₀ = Zo.zoBase S = ι(Ω₂)` (`Zr.zrBase_eq`: `P(Ω₂)` is a
`Γ`-point, `Zr.zrGP_Om2`, by the plateau `ψ_{Ω₂}(Ω_ω + Ω₂) = sup_j K_j`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + K_j)`), its name is
`Ω₂`, `A = Ω_ω + Ω₂`, its code is `π_{Ω₂}` and `Θ(π) = Θ(Ω₂)` (`Zr.zrBase_theta`); with `g(x) = ψ_{Ω₁}(A + θ + x)`,
`F_0 = ρ`, `F_{j+1} = g(F_j)`: every atom `ψ_{Ω₂}(Ω_ω + c)` with `c < K_j` reads at most `g(Θ(c))`
(`Zr.zrInner`), `Θ(K_j) ≤ F_j` (`Zr.zrOuter`), so `Θ(Ω₂) ≤ ψ_{Ω₁}(A + θ + Ω₁) < ψ_{Ω₁}(A + θ·(ω+1)) = δ_{l₀}`
(`Zr.zrTh_Om2`, `Zr.zrY_lt`); the first branch holds.  No hypothesis. -/
theorem skBCThPos (S : InaccSeq.{0}) :
    Cd.cdTheta S (Zo.zoBase S) (Cd.cdCode S (Zo.zoBase S)) < Cd.cdDelta (Zo.zoBase S) ∨
      upsilon (Zo.zoBase S + ω * ω) ≤ Cd.cdTheta S (Zo.zoBase S) (Cd.cdCode S (Zo.zoBase S)) :=
  Or.inl Zr.zrBCThPos

/-- STATUS: REDUCED (round 134, Zr.zrBCReach2: skBCLow, skBCBaseUV, skBCThPos; was OPEN M, round 133)
SIZE: M
THE CHAIN REACH DATUM AT THE BASE `l₀`, with a chain start `o ≤ r(l₀) − δ_{l₀}` (`o < δ_{l₀}`).  The form with
`o = 0` (the base datum of the windows) is FALSE at a short-reach base `δ < r < top₁` under UPPER ∧ LOWER
(skReach0Ref).  Round 134: no point below `ρ_{l₀}` is `≤₁` any point `≥ ρ_{l₀}` (`Zr.zrNoCross`: the
`<₁`-predecessors of a restart below `ν_C` are restarts, `R2.pred_restart_C`; every restart `μ < l₀` stays below
`ρ_{l₀}`, `Zr.zrCapBelow`: below `B₀` by its exact reach `δ_μ + O(μ)`, from `B₀` on by UPPER and CapV with the cap
`P(η_μ + ω^{e(η_μ)}) ≤ P(Ω₂)`; `ρ_{l₀} < ν_C`, `Zr.zrNu`).  So with UPPER at `l₀` the datum holds with
`o = r − δ = Θ_{l₀}(m_{l₀})` when `Θ_{l₀}(m_{l₀}) < δ_{l₀}` (the closed points `δ + x`, `Zh.zhDense`, give
`r = δ + Θ_{l₀}(m_{l₀})`; `Zr.zrReach`), and with LOWER at `l₀` and `o = 0` when `υ_{l₀+ω²} ≤ Θ_{l₀}(m_{l₀})`
(`Zr.zrReach_long`).  REDUCED to skBCBaseUV (the notation leaf skBCThPos is PROVED, `Zr.zrBCThPos`). -/
theorem skBCReach (S : InaccSeq.{0}) : ∃ o, o < upsilon (Zo.zoBase S + ω + 1) ∧ o ≤ Ys.ysO S (Zo.zoBase S) ∧
    Ys.YsReachIn (Zo.zoBase S) o (upsilon (Zo.zoBase S)) :=
  Zr.zrBCReach2 (fun μ hr h => skBCLow S μ hr h) (skBCBaseUV S).1 (skBCBaseUV S).2.1 (skBCThPos S)

/-- STATUS: PROVED (Zo.zoGiven_of, skBCBaseUV, skBCReach; round 133, new; checked only after the merge)
SIZE: S
THE GIVEN INPUT AT THE BASE: Lemma TOP at `r(l₀)` is UPPER at `l₀`. -/
theorem skBCGiven (S : InaccSeq.{0}) : Yx.YxGivenIn (Ys.ysO S) (Zo.zoBase S) := by
  obtain ⟨o, h1, h2, h3⟩ := skBCReach S
  exact Zo.zoGiven_of (skBCBaseUV S).1 h1 h2 h3

/-- STATUS: OPEN (round 133, new leaf, regc1)
SIZE: L
THE PAIR-FREE INPUT AT THE RESTARTS STRICTLY INSIDE `(l₀, ι(Ω_ω))` (`Zc.ZcInR`, as skWinInR for the windows): at
every restart `λ` the short input `Yx.YxShortIn ρ_{l₀} (ysO S) λ` or the given input `Yx.YxGivenIn (ysO S) λ`.
REFUTE FIRST: NO EVIDENCE.  At a supply restart (cofinal below `L(0)`, `Rx.rxSupAt`) the given input follows from
UPPER at `λ` and the supply below `ρ_λ` (`Zc.zcGiven_of_sup`); the short input after a supply restart is impossible
(`Ys.ysShortX_ref`), the given input is not; `Yf.yfNoBase_cross`, `Yi.yiMShort_ref` concern the cell base data and
short-only inputs, which are not asked.  Non-vacuity: `Zo.zoBC_of_target`. -/
theorem skBCInR (S : InaccSeq.{0}) : Zc.ZcInR S (Zo.zoBase S) (Zo.zoTop S) := by
  sorry

/-- STATUS: OPEN (round 138: one leaf for every range restart above `l₀`, replaces skBCCapVH, skWinCapVF,
skTopCapVF; round 133, regc1, regw8)
SIZE: L
CAPV AT THE `υ`-FIXED RANGE RESTARTS ABOVE `l₀ = ι(Ω₂)` (the (B-hi)/(C) block and the windows up to `L(ω+1)`)
BELOW `ν_C` WITH A FAR READING `δ_λ·ω ≤ Θ_λ(m_λ)`.  At the other fixed restarts below `ν_C` CapV is a theorem
(`Zn.znCapV_fixThW`; codes `≤ K_ω` read short, `Zs.zsShortK`; non-fixed: `Zh.zhCapV_nonfix`).  A far reading puts
`r(λ) = k_λ(Θ_λ(m_λ))` past `δ_λ·ω`, so CapV needs the closed points of `(δ_λ, cap)`, which depend on the reaches
of the points above `ρ_λ`.  REFUTE FIRST (at the first fixed restart of `W₁`): CapV holds there when
`Θ_λ(m_λ) < δ_λ·ω`; NO EVIDENCE against the leaf. -/
theorem skFixCapVF (S : InaccSeq.{0}) : ∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → upsilon μ = μ →
    upsilon μ < nuC → Cd.cdDelta μ * ω ≤ Cd.cdTheta S μ (Cd.cdCode S μ) → Cd.CdCapV S μ := by
  sorry

/-- STATUS: PROVED (round 138, from skFixCapVF; was OPEN L: round 133, new leaf, regc1; round 135: narrowed to the
codes `m_λ > K_ω`; round 137: and to the far readings `δ_λ·ω ≤ Θ_λ(m_λ)`, as skWinCapVF)
SIZE: L
CAPV AT THE `υ`-FIXED RANGE RESTARTS OF `(l₀, ι(Ω_ω))` below `ν_C` with neither a short last exponent nor a LOW code:
`2 ≤ e(η_λ)` only together with `m_λ > θ·ω` (at `m_λ ≤ θ·ω`, `e ≥ 2` CapV is the theorem `Zo.zoCapV_low`; at
`2 ≤ e < ρ_λ` it is `Zh.zhCapV_short`).  Contains every (C) restart below `ν_C` (codes `π_η > θ`, all `υ`-fixed:
skCFix).  REFUTE FIRST: NO EVIDENCE.  Round 135: only the codes `m_λ > K_ω = ψ_{Ω₂}(Ω_ω + Ω₂)` are asked (at
`m_λ ≤ K_ω` the reading is short, `Θ_λ(m_λ) ≤ ψ_{Ω₁}(A + θ + Ω₁) < δ_λ`, and CapV is the theorem `Zs.zsCapV_K`,
skBCCapVK); every (C) restart above `l₀` has `π_η > K_ω`.  There the hull below `m_λ` has atoms `ψ_{Ω₂}(Ω_ω + y)`
with `y ≥ Ω₂`, whose readings are not bounded by the plateau iterates.  Round 137: at `Θ_λ(m_λ) < δ_λ·ω` CapV is the
theorem `Zn.znCapV_fixThW`, so only the far readings are asked. -/
theorem skBCCapVH (S : InaccSeq.{0}) : ∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → μ < Zo.zoTop S →
    upsilon μ = μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ →
    (ω ^ 2 ≤ ω ^ Cd.cdExp (Cd.cdEta S μ) → ConjT.th S * ω < Cd.cdCode S μ) →
    S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) < Cd.cdCode S μ →
    Cd.cdDelta μ * ω ≤ Cd.cdTheta S μ (Cd.cdCode S μ) → Cd.CdCapV S μ :=
  fun μ hr h0 _ hfix hν _ _ _ hfar => skFixCapVF S μ hr h0 hfix hν hfar

/-- STATUS: PROVED (Zs.zsCapV_K, Zs.zsEta_ne_above; round 135, new node)
SIZE: S
CAPV AT THE `υ`-FIXED RANGE RESTARTS OF `(l₀, ι(Ω_ω))` below `ν_C` WITH A CODE `m_λ ≤ K_ω = ψ_{Ω₂}(Ω_ω + Ω₂)`: every
atom of the hull below `K_ω` lies below a plateau iterate `K_j`, so `Θ_λ(m_λ) ≤ Θ_λ(K_ω) ≤ ψ_{Ω₁}(A + θ + Ω₁) < δ_λ`
(`Zr.zrTh_K`, `Zs.zsShortK`), and the short reading gives CapV (`Zn.znCapV_fixTh`). -/
theorem skBCCapVK (S : InaccSeq.{0}) : ∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → μ < Zo.zoTop S →
    upsilon μ = μ → upsilon μ < nuC →
    Cd.cdCode S μ ≤ S.psi (Om ω + Om (1 + 1)) (Om (1 + 1)) → Cd.CdCapV S μ := by
  intro μ hr h0 h1 hfix hν hc
  have hm : upsilon μ < Cd.cdMstar S := by
    rw [← Zo.zoTop_ups (S := S)]; exact upsilon_normal.strictMono h1
  exact Zs.zsCapV_K hr hfix hν hm (Zs.zsEta_ne_above hr h0 hm) hc

/-- STATUS: PROVED (skBCCapVH, skBCCapVK, Zo.zoCapV_low, Zn.znCapV_fixThW; round 133, new; round 135: + skBCCapVK; round 137: + znCapV_fixThW)
SIZE: S
CapV at the `υ`-fixed long-exponent range restarts of `(l₀, ι(Ω_ω))` below `ν_C`. -/
theorem skBCCapVL (S : InaccSeq.{0}) : ∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → μ < Zo.zoTop S →
    upsilon μ = μ → upsilon μ < nuC → ¬ Zh.ZhShortExp S μ → Cd.CdCapV S μ := by
  intro μ hr h0 h1 hfix hν hns
  by_cases hc : ω ^ 2 ≤ ω ^ Cd.cdExp (Cd.cdEta S μ) ∧ Cd.cdCode S μ ≤ ConjT.th S * ω
  · have hm : upsilon μ < Cd.cdMstar S := by
      rw [← Zo.zoTop_ups (S := S)]; exact upsilon_normal.strictMono h1
    exact Zo.zoCapV_low (η1 := Om ω) hr.1 hm hν (hm.trans_le (Cd.cdMstar_le_L S ω)) hc.2 hc.1
  · by_cases hK : Cd.cdCode S μ ≤ S.psi (Om ω + Om (1 + 1)) (Om (1 + 1))
    · exact skBCCapVK S μ hr h0 h1 hfix hν hK
    · by_cases hW : Cd.cdTheta S μ (Cd.cdCode S μ) < Cd.cdDelta μ * ω
      · have hm : upsilon μ < Cd.cdMstar S := by
          rw [← Zo.zoTop_ups (S := S)]; exact upsilon_normal.strictMono h1
        exact Zn.znCapV_fixThW (η1 := Om ω) hr.1 hfix hν hm hW
      · exact skBCCapVH S μ hr h0 h1 hfix hν hns (fun h2 => not_le.1 fun h3 => hc ⟨h2, h3⟩) (not_le.1 hK)
          (not_lt.1 hW)

/-- STATUS: OPEN (round 137: skBCRsS without its short-reading part; round 133, new leaf, regc1)
SIZE: L
THE RS INPUT AT THE `υ`-FIXED RESTARTS OF `(l₀, ι(Ω_ω))` WITH `ρ_λ < Θ_λ(m_λ)` WHEN `ρ_λ < ν_C`, WITH THE SUPPLY (as
skWinRsS): the old input `Zc.ZcRsIn` (LOWER, the successor case or the term input) or the supply input `Zh.ZhSupInB`
to the top `ι(Ω_ω)`.  At the non-fixed restarts it is a theorem (`Zh.zhRsIn_nonfix`); at a fixed restart below
`ν_C` with `Θ_λ(m_λ) ≤ ρ_λ` it is a theorem (`Zn.znRsIn_fixShort`; every isolated fixed restart is of this kind,
`Zt.ztIsoCode`); at a supply restart the old input is LOWER itself (`Zc.zcRsIn_long_lower`), the supply branch needs
only the supply.  REFUTE FIRST: NO EVIDENCE.  Non-vacuity: LOWER gives it (`Zh.zhIn4_of_lower`,
`Zo.zoBC_of_target`). -/
theorem skBCRsSH (S : InaccSeq.{0}) : ∀ l, IsRestartIdx l → Zo.zoBase S < l → l < Zo.zoTop S → upsilon l = l →
    (upsilon l < nuC → upsilon l < Cd.cdTheta S l (Cd.cdCode S l)) →
    Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Zo.zoTop S) := by
  sorry

/-- STATUS: REDUCED (round 137: skBCRsSH, Zn.znRsIn_fixShort; was OPEN L, round 133, new leaf, regc1)
SIZE: L
THE RS INPUT AT THE `υ`-FIXED RESTARTS OF `(l₀, ι(Ω_ω))`, WITH THE SUPPLY (as skWinRsS).  Below `ν_C` at a short
reading `Θ_λ(m_λ) ≤ ρ_λ` it is the theorem `Zn.znRsIn_fixShort` (the term input with the constant terms `w < ρ_λ`);
the rest is skBCRsSH. -/
theorem skBCRsS (S : InaccSeq.{0}) : ∀ l, IsRestartIdx l → Zo.zoBase S < l → l < Zo.zoTop S → upsilon l = l →
    Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Zo.zoTop S) := by
  intro l hl h0 h1 hfix
  by_cases hs : upsilon l < nuC ∧ Cd.cdTheta S l (Cd.cdCode S l) ≤ upsilon l
  · have hm : upsilon l < Cd.cdMstar S := by
      rw [← Zo.zoTop_ups (S := S)]; exact upsilon_normal.strictMono h1
    exact Or.inl (Zn.znRsIn_fixShort (η1 := Om ω) hl hfix hs.1 hm hs.2)
  · exact skBCRsSH S l hl h0 h1 hfix fun hν => not_le.1 fun hθ => hs ⟨hν, hθ⟩

/-- STATUS: REDUCED (Zo.zoBC; skBCLow, skBCBaseUV, skBCGiven, skBCInR, skBCCapVL, skBCRsS; round 133, new; checked
only after the merge)
SIZE: L
REGIONS (B-hi) AND (C) BY ONE RELATIVE BLOCK INDUCTION ON `[l₀, ι(Ω_ω))`, `l₀ = Zo.zoBase S`: UPPER ∧ LOWER ∧
CapV at every range restart `λ ≥ ι(Ω₂)` with `ρ_λ < m* = L(0)`.  No CAP-0 (`Zo.zoNu_gt0`: the caps below the
current height suffice below `m*`). -/
theorem skBC (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Bt.iota S (Om (1 + 1)) ≤ l →
    upsilon l < Cd.cdMstar S → SkUV S l :=
  (Zo.zoBC (skBCLow S) (skBCBaseUV S) (skBCGiven S) (skBCInR S) (skBCCapVL S) (skBCRsS S)).2

/-- STATUS: REDUCED (Zo.zoBC_nu; the leaves of skBC; round 133, new; checked only after the merge)
SIZE: S
`L(0) ≤ ν_C` (the induction interval is not empty, `Zo.zoBC_nonempty0`). -/
theorem skNuL0 (S : InaccSeq.{0}) : Nc.ncL S 0 ≤ nuC :=
  Zo.zoBC_nu (skBCLow S) (skBCBaseUV S) (skBCGiven S) (skBCInR S) (skBCCapVL S) (skBCRsS S)

/-- STATUS: PROVED (Zo.zoBC_of_target; round 133, new; checked only after the merge)
SIZE: S
NON-VACUITY of skBCGiven, skBCInR, skBCCapVL, skBCRsS: they follow from UPPER, LOWER, CapV at the range restarts
of `[l₀, ι(Ω_ω))` and the chain reach data (chain start `0`) there. -/
theorem skBCVac (S : InaccSeq.{0})
    (hU : ∀ μ, Cd.CdRange S μ → Zo.zoBase S ≤ μ → μ < Zo.zoTop S → Cd.CdUpper S μ)
    (hL : ∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → μ < Zo.zoTop S → Cd.CdLower S μ)
    (hV : ∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → μ < Zo.zoTop S → Cd.CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → Zo.zoBase S ≤ l → l < Zo.zoTop S → Ys.YsReachIn l 0 (upsilon l)) :
    Yx.YxGivenIn (Ys.ysO S) (Zo.zoBase S) ∧ Zc.ZcInR S (Zo.zoBase S) (Zo.zoTop S) ∧
      (∀ μ, Cd.CdRange S μ → Zo.zoBase S < μ → μ < Zo.zoTop S → upsilon μ = μ → upsilon μ < nuC →
        ¬ Zh.ZhShortExp S μ → Cd.CdCapV S μ) ∧
      (∀ l, IsRestartIdx l → Zo.zoBase S < l → l < Zo.zoTop S → upsilon l = l →
        Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Zo.zoTop S)) :=
  Zo.zoBC_of_target Zo.zoBase_lt_top hU hL hV hR

/-- STATUS: PROVED (Zo.zoReach0_ref; round 133, new; checked only after the merge)
SIZE: S
REFUTE FIRST for a base datum with chain start `0` at a range base: false at a short-reach restart. -/
theorem skReach0Ref (S : InaccSeq.{0}) {l : Ordinal.{0}} (hU : Cd.CdUpper S l) (hL : Cd.CdLower S l)
    (h1 : upsilon (l + ω + 1) < Cd.cdR S l)
    (h2 : Cd.cdR S l < topA (l + ω) (upsilon (l + ω + 1) + 0) 1) : ¬ Ys.YsReachIn l 0 (upsilon l) :=
  Zo.zoReach0_ref hU hL h1 h2

/-- STATUS: PROVED (Zo.zoC_fix; round 133, new; checked only after the merge)
SIZE: S
REFUTE FIRST for skLongPre: every (C) range restart is a `υ`-fixed point (so no short-exponent theorem applies). -/
theorem skCFix (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : Cd.CdRange S l)
    (he : Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l)) (h0 : upsilon l < Nc.ncL S 0) : upsilon l = l :=
  Zo.zoC_fix hr he h0

/-- STATUS: PROVED (skBC, Zo.zoNameB; round 133, regc1: was OPEN L; checked only after the merge; round 126: was the
whole of skBhiA; the cell part is skBhiAcell)
SIZE: L
(B-hi, A-type cell, the rest) offsets `ζ` of type (A) where the cell condition fails: `ζ ≥ P(Ω₂·q)` (past the
first fixed points of `υ` above the base), or no base data at `ι(Ω₂·q)`.  REFUTE FIRST: NO EVIDENCE.  The base
data at `ι(Ω₂·q)` are consistent with every proved result for small `q`; for large `q` (names with collapsible
`ψ_{Ω₂}`-arguments `≥ Ω_ω + θ₂`, cf. `Ls.lsNames_M`) a restart with a long reach below `ι(Ω₂·q)` would remove them
(`Yf.yfNoBase_cross`), so this leaf must not assume them.  Round 127: under LOWER below `L(0)` the supply restarts
of `Rx.rxSupAt` (cofinal below `L(0)`, `υ_{μ+γ} ≤ r(μ)`) are covered by no relative block induction (`skMShortRef`):
past the first fixed points the cells must be joined by the same induction with nested long reaches as the windows.
Round 129: that induction now exists for any base restart `l₀` (`Ys.ysGood_all`, `Ys.YsSpec`).  Round 133: APPLIED
(skBC): one relative block induction on `[l₀, ι(Ω_ω))` (`l₀` the least restart index `≥ ι(Ω₂)`) covers every
(B-hi) and (C) restart, cells and far offsets alike; the leaf is REDUCED to the leaves of skBC. -/
theorem skBhiAfar (S : InaccSeq.{0}) : ∀ l q ζ, Cd.CdRange S l → Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q →
    ζ ≠ 0 → ζ < Om (1 + 1) → Cd.cdEta S l < Om ω → Xh.XhNmA ζ → ¬ SkBhiCell S q ζ → SkUV S l := by
  intro l q ζ hr he hq _ _ hη _ _
  obtain ⟨hι, hm⟩ := Zo.zoNameB hr he hq hη
  exact skBC S l hr hι hm

/-- STATUS: REDUCED (skBhiAcell, skBhiAfar; round 126, was OPEN L)
SIZE: L
(B-hi, A-type cell) base Ω₂·q, offset ζ of type (A): transport of region (A) along ζ ↦ Ω₂·q + ζ. -/
theorem skBhiA (S : InaccSeq.{0}) : ∀ l q ζ, Cd.CdRange S l → Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q →
    ζ ≠ 0 → ζ < Om (1 + 1) → Cd.cdEta S l < Om ω → Xh.XhNmA ζ → SkUV S l := by
  intro l q ζ hr he hq hζ0 hζ hη hA
  by_cases hc : SkBhiCell S q ζ
  · exact skBhiAcell S l q ζ hr he hζ0 hc
  · exact skBhiAfar S l q ζ hr he hq hζ0 hζ hη hA hc

/-- STATUS: PROVED (skBC, Zo.zoNameB; round 133, regc1: was OPEN L; checked only after the merge)
SIZE: L
(B-hi, layer cells) base Ω₂·q, offset ζ in the name layer c ≥ 1.  Round 133: no transport of the layer results is
needed: the relative block induction of skBC covers these restarts directly (REDUCED to the leaves of skBC). -/
theorem skBhiL (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l q ζ, Cd.CdRange S l →
    Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q → ζ ≠ 0 → ζ < Om (1 + 1) → Cd.cdEta S l < Om ω →
    Xh.XhNmLay c ζ → SkUV S l := by
  intro _ _ _ l q ζ hr he hq _ _ hη _
  obtain ⟨hι, hm⟩ := Zo.zoNameB hr he hq hη
  exact skBC S l hr hι hm

/-- STATUS: REDUCED (Xh.xhBhi_red, skBhiA, skBhiL; was OPEN L)
SIZE: L
(B-hi) names Ω₂ ≤ η < Ω_ω with last exponent < Ω₂ (offset codes), υ_λ < L(0). -/
theorem skRegBhi (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjNotA S l → upsilon l < Nc.ncL S 0 →
    Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → Bt.iota S (Om (1 + 1)) ≤ l → SkUV S l :=
  Xh.xhBhi_red (S := S) (SkUV S) (skBhiA S) (skBhiL S)

/-- STATUS: PROVED (Xh.xhWin_off, Xh.xhWin_cap, Xh.xhWin_capV)
SIZE: S
a name in (b_ξ, b_{ξ+1}) is b_ξ + ζ, 0 < ζ < P′, e(η) = e(ζ), code -1 + e(ζ); its cap is ≤ L(ξ+1), so CapV
gives r(λ) < L(ξ+1). -/
theorem skWinOff (S : InaccSeq.{0}) {ξ l : Ordinal.{0}} (hr : Cd.CdRange S l) (h1 : Nc.ncL S ξ < upsilon l)
    (h2 : upsilon l < Nc.ncL S (ξ + 1)) :
    (∃ ζ, Cd.cdEta S l = Wj.wjBase S ξ + ζ ∧ ζ ≠ 0 ∧ ζ < Nc.ncPp S ∧
      Cd.cdExp (Cd.cdEta S l) = Cd.cdExp ζ ∧ Cd.cdCode S l = Cd.cdOff (Cd.cdExp ζ)) ∧
    Cd.cdCapB S l ≤ Nc.ncL S (ξ + 1) :=
  ⟨Xh.xhWin_off hr h1 h2, Xh.xhWin_cap hr h1 h2⟩

/-- STATUS: PROVED (Xh.xhNu_A2)
SIZE: S
the closed region (A2) bounds ν_C from below: υ(ι(Γ(B)·ω)) ≤ ν_C for every B < φ(G, 1) (no hypothesis). -/
theorem skNuA2 (S : InaccSeq.{0}) {B : Ordinal.{0}} (hB : B < veblen (Gc.gcG 0) 1) :
    upsilon (Bt.iota S (Gc.gcG B * ω)) ≤ nuC := Xh.xhNu_A2 S hB

/-- STATUS: PROVED (skBC, Zo.zoNameC; round 133, regc1: was OPEN L; checked only after the merge)
SIZE: L
(C) = (C1): names with e(η_λ) ≥ Ω₂ (code π_η, ι(Ω₂) ≤ λ, Wj.wjC_props); all of (C) lies below L(0)
(Wj.wjExpHi_low).  Round 122: REFUTE FIRST, NO EVIDENCE (codes π_η > Γ_{Ω₁+ε₀}, Gc.gc_code_ge, outside every
frontier lemma, Gc.gcFr_code; no L(k) inside).  Round 133: REFUTE FIRST at the first name with
e(η_λ) = Ω₂: NO EVIDENCE; every (C) restart is υ-fixed (skCFix), so CapV there is asked by skBCCapVH; REDUCED to
the leaves of skBC (the same induction as (B-hi)). -/
theorem skLongPre (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    upsilon l < Nc.ncL S 0 → SkUV S l := by
  intro l hr he h0
  obtain ⟨hι, hm⟩ := Zo.zoNameC hr he h0
  exact skBC S l hr hι hm

/-- STATUS: PROVED (Wj.wjLongMid: VACUOUS, no such restart)
SIZE: S
(C2) range λ with e(η_λ) ≥ Ω₂ and L(0) ≤ υ_λ ≤ L(ω). -/
theorem skLongMid (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S 0 ≤ upsilon l → upsilon l ≤ Nc.ncL S ω → SkUV S l :=
  Wj.wjLongMid (SkUV S)

/-- STATUS: PROVED (Wj.wjLongTop: VACUOUS, no such restart)
SIZE: S
(C3) range λ with e(η_λ) ≥ Ω₂ and L(ω) < υ_λ. -/
theorem skLongTop (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    Nc.ncL S ω < upsilon l → SkUV S l :=
  Wj.wjLongTop (SkUV S)

/-- STATUS: REDUCED (skLongPre, skLongMid, skLongTop)
SIZE: L
(C) ∀ range λ with e(η_λ) ≥ Ω₂: UPPER ∧ LOWER ∧ CapV. -/
theorem skRegC (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) → SkUV S l := by
  intro l hr he
  rcases lt_or_ge (upsilon l) (Nc.ncL S 0) with h0 | h0
  · exact skLongPre S l hr he h0
  rcases le_or_gt (upsilon l) (Nc.ncL S ω) with hw | hw
  · exact skLongMid S l hr he h0 hw
  · exact skLongTop S l hr he hw

/-- STATUS: REPLACED (round 131, regw6: by skWinInR; its base part, the reach datum of the base chain, is
proved inside the window induction, skWinBase = `Zc.zcBaseIn`; not used; was OPEN L)
SIZE: L
THE WINDOW INPUT `Yx.YxIn` on `W_k`: the reach datum of the base chain (`Ys.YsReachIn ι(L(k)) 0 L(k)`: a point
`c ≤ L(k)` that is `≤₁` a point inside a chain block after `δ_{ι(L(k))}` is `≤₁` its top) and at every restart of
the window a pair-free input with the bound `r − δ`: `Yx.YxShortIn` (an offset term for `r(λ) − δ_λ < δ_λ`, a
crossing bound `x₀ ∈ [L(k), ρ_λ)` above which no restart realizes the term, the chain reach datum) or
`Yx.YxGivenIn` (Lemma TOP at `r(λ)` = UPPER, the chain reach datum; at a supply restart it follows from UPPER,
LOWER and `υ_{λ+ω²} ≤ r(λ)`: `Yx.yxGiven_of_supply`).  REFUTE FIRST: NO EVIDENCE.  At the first supply restart
above `L(0)` (`Ls.lsNames_L`, `Cv.cvM_restart`, `Rl.rlM_lt_L1`) the given input asks only UPPER, LOWER and the
long reach (no pair datum any more); the short input with `x₀` below a supply restart is impossible after it
(skWinShortX), the given input is not; no forms, tops or supply roads are used (Vo.voNoGo, Vn.vnTop_Om3,
Ww.wwRoad_false, Xj.xbRoad_false, Yf.yfNoBase_win, Yi.yiWinShort_ref do not apply).  Non-vacuity of the shape:
`Yx.yxSpec_old` (`Yx.YxSpec` below `Ξ_ω`); every old `Ys.YsSpec` is a `Yx.YxSpec` (`Ys.YsSpec.toYx`). -/
theorem skWinIn (S : InaccSeq.{0}) (k : ℕ) :
    Yx.YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  sorry

/-- STATUS: REPLACED (round 131, regw6: by skTopInR; the base part is proved inside `Zc.zcTopAll2`; not used;
was OPEN L)
SIZE: L
THE WINDOW INPUT `Yx.YxIn` on `W_ω` (as skWinIn).  REFUTE FIRST: NO EVIDENCE. -/
theorem skTopIn (S : InaccSeq.{0}) :
    Yx.YxIn S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  sorry

/-- STATUS: OPEN (round 131, new leaf, regw6; skWinIn without its base part)
SIZE: L
THE WINDOW INPUT AT THE RESTARTS STRICTLY INSIDE `W_k` (`Zc.ZcInR`): at every restart `λ` of
`(ι(L(k)), ι(L(k+1)))` the short input `Yx.YxShortIn L(k) (ysO S) λ` or the given input `Yx.YxGivenIn (ysO S) λ`.
REFUTE FIRST: NO EVIDENCE.  At a supply restart the given input follows from UPPER at `λ` and the supply below
`ρ_λ` (`Zc.zcGiven_of_sup`; no LOWER at `λ`, no long reach needed); non-vacuity: `Zc.zcWins_of_target`. -/
theorem skWinInR (S : InaccSeq.{0}) (k : ℕ) :
    Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  sorry

/-- STATUS: OPEN (round 131, new leaf, regw6; skTopIn without its base part)
SIZE: L
THE WINDOW INPUT AT THE RESTARTS STRICTLY INSIDE `W_ω` (as skWinInR).  REFUTE FIRST: NO EVIDENCE. -/
theorem skTopInR (S : InaccSeq.{0}) :
    Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  sorry

/-- STATUS: REPLACED (round 132, regw7: by skWinRsS, whose supply branch replaces LOWER at the supply restarts by
the supply `Zh.ZhSupB`; not used; was OPEN L, round 131, new leaf, regw6; replaces skWinRsIn)
SIZE: L
THE RS INPUT IN `W_k` ON THE PREDICTED REACHES (`Zc.ZcRsIn`): at every restart `λ` of the window LOWER, or a
successor index with `O(λ) = 1`, or a limit index with `1 ≤ O(λ)` and the term input `Zc.ZcRsTerm`: every
`z < O(λ) = r(λ) − δ_λ` is below `t(ρ_λ)` for an offset term `t` with constants below `ρ_λ` with `t(ρ_μ) ≤ O(μ)`
at restarts `μ` cofinal below `λ` (no `≤₁` in it: the RS step is `Zc.zcRs_rstT`).  REFUTE FIRST: the term input is
FALSE at every supply restart (skRsLongNoGo), so there the leaf asks LOWER itself (skRsLongLower); elsewhere NO
EVIDENCE.  Non-vacuity: LOWER gives it (`Zc.zcRsIn_of_lower`, `Zc.zcWins2_of_target`). -/
theorem skWinRsT (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → Zc.ZcRsIn (Ys.ysO S) l := by
  sorry

/-- STATUS: REPLACED (round 132, regw7: by skTopRsS; not used; was OPEN L, round 131, new leaf, regw6;
replaces skTopRsIn)
SIZE: L
THE RS INPUT IN `W_ω` ON THE PREDICTED REACHES (as skWinRsT). -/
theorem skTopRsT (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → Zc.ZcRsIn (Ys.ysO S) l := by
  sorry

/-- STATUS: REPLACED (round 133, regw8: by skWinRsF, asked only where `ρ_λ < Θ_λ(m_λ)`, given `υ_{B_k} ≤ ν_C`,
with the value branch `Zn.ZnRsVal`; not used; was OPEN L, round 132, new leaf, regw7; replaces skWinRsT)
SIZE: L
THE RS INPUT IN `W_k` AT THE `υ`-FIXED RESTARTS (`υ_λ = λ`), WITH THE SUPPLY: at every such restart `λ` the old input `Zc.ZcRsIn` (LOWER, the
successor case, or the term input) or the supply input `Zh.ZhSupInB` (a target `υ_{λ+β} ≥ r(λ)` with
`λ + β ≤ ι(L(k+1))` and Range restarts `μ` cofinal below `ρ_λ` with `μ + β ≤ λ`, `β ≤ ρ_μ`, `υ_{μ+β} ≤ r(μ)`).
At a supply restart the old input is LOWER itself (skRsLongLower); the new branch needs only the supply (the
carry is `Zh.zhCarry_auto`, LOWER at the inner restarts comes from the induction, `Zh.zhRs_all`).
REFUTE FIRST: NO EVIDENCE.  The case `β = ω² + 1` is empty (skSupBeta: a supply restart needs `β ≥ ω²+ω+1`); no
form, top or term-input statement is used (Vo.voNoGo, Vn.vnTop_Om3, Zc.zcRsTerm_long_false do not apply); the
supply branch at targets `β > ρ_μ` is not covered (the inner codes are then read by `Θ`; the general carry form
`Zh.ZhSupIn` with `Zh.ZhCarry` remains available).  At the restarts with `λ < υ_λ` the input is a THEOREM
(skRsNonfix, `Zh.zhRsIn_nonfix`), and every supply restart is a fixed point (skSupFix).  Non-vacuity: skWinRsT (and
LOWER) gives it (skWinRsSVac). -/
theorem skWinRsS (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨
        Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  sorry

/-- STATUS: REPLACED (round 133, regw8: by skTopRsF; not used; was OPEN L, round 132, new leaf, regw7; replaces
skTopRsT)
SIZE: L
THE RS INPUT IN `W_ω` AT THE `υ`-FIXED RESTARTS, WITH THE SUPPLY (as skWinRsS). -/
theorem skTopRsS (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  sorry

/-- STATUS: PROVED (Zh.zhIn4_of_lower; round 132, new; checked only after the merge)
SIZE: S
NON-VACUITY of skWinRsS / skTopRsS: the old input (skWinRsT, in particular LOWER) gives the new one. -/
theorem skWinRsSVac {S : InaccSeq.{0}} {l B : Ordinal.{0}} (h : Zc.ZcRsIn (Ys.ysO S) l) :
    Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B := Or.inl h

/-- STATUS: PROVED (Zh.zhSup_beta2; round 132, new; checked only after the merge)
SIZE: S
REFUTE FIRST for the short realizer targets: a supply restart (`υ_{λ+ω²} ≤ r(λ) < Ω₁`) with
`ρ_{λ+ω²} ≤₁ δ_{λ+ω²} + 1` has no target `r(λ) ≤ υ_{λ+β}` with `β ≤ ω²+ω+1`. -/
theorem skSupBeta {S : InaccSeq.{0}} {l β : Ordinal.{0}} (hr1 : Cd.cdR S l < Om1)
    (hin : upsilon (l + ω ^ 2) ≤ Cd.cdR S l)
    (h1 : le1 (upsilon (l + ω ^ 2)) (upsilon (l + ω ^ 2 + ω + 1) + 1))
    (hβ : Cd.cdR S l ≤ upsilon (l + β)) : ω ^ 2 + ω + 1 < β :=
  Zh.zhSup_beta2 hr1 hin h1 hβ

/-- STATUS: PROVED (Zh.zhReal_gen; round 132, new; checked only after the merge)
SIZE: L
THE REALIZER MAPS FOR EVERY TARGET `t ≤ υ_{λ+β}` with UPPER at the inner restarts and the supply with the carry. -/
theorem skRealGen {S : InaccSeq.{0}} {l β t : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hνl : upsilon l < nuC) (hν : upsilon (l + β) ≤ nuC) (ht : t ≤ upsilon (l + β))
    (hU : Zh.ZhUpIn S l β) (hsup : Zh.ZhSupAt S l β) : Lr.LrReal S (upsilon l) t :=
  Zh.zhReal_gen hl hl1 hνl hν ht hU hsup

/-- STATUS: PROVED (Zh.zhDense, Zh.zhR_short_all; round 132, new; checked only after the merge)
SIZE: S
THE SHORT VALUE BELOW `ν_C`: a restart with `ρ_λ < ν_C` and code `m_λ ≤ ρ_λ` has `r(λ) = δ_λ + m_λ`. -/
theorem skShortAll {S : InaccSeq.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hc : Cd.cdCode S l ≤ upsilon l) : Cd.cdR S l = Cd.cdDelta l + Cd.cdCode S l :=
  Zh.zhR_short_all hl hν hc

/-- STATUS: PROVED (Zh.zhLong_code; round 132, new; checked only after the merge)
SIZE: S
A SUPPLY RESTART HAS A LONG CODE: `υ_{λ+ω²} ≤ r(λ)`, `ρ_λ < ν_C` ⇒ `ρ_λ < m_λ`. -/
theorem skLongCode {S : InaccSeq.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hlong : upsilon (l + ω ^ 2) ≤ Cd.cdR S l) : upsilon l < Cd.cdCode S l :=
  Zh.zhLong_code hl hν hlong

/-- STATUS: PROVED (Zh.zhCarry_auto; round 132, new; checked only after the merge)
SIZE: S
THE CARRY OF THE INNER REACHES BELOW `ρ_μ`. -/
theorem skCarryAuto {S : InaccSeq.{0}} {l μ β η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hμ : IsRestartIdx μ)
    (hn : upsilon l < Nm.Pv S η1) (hνβ : upsilon (l + β) ≤ nuC) (hβμ : β ≤ upsilon μ)
    (hμl : upsilon μ < upsilon l) : Zh.ZhCarry S l μ β :=
  Zh.zhCarry_auto hl hμ hn hνβ hβμ hμl

/-- STATUS: PROVED (Zh.zhSupB_of_ra; round 132, new; checked only after the merge)
SIZE: S
The supply for one target from `Ra.RaSupAt S ρ_λ` when the target fits above the restarts close below `λ`. -/
theorem skSupOfRa {S : InaccSeq.{0}} {l β x0 : Ordinal.{0}} (hsup : Ra.RaSupAt S (upsilon l))
    (hβ : β < upsilon l) (hx0 : x0 < upsilon l)
    (hfit : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ + β ≤ l) : Zh.ZhSupB S l β :=
  Zh.zhSupB_of_ra hsup hβ hx0 hfit

/-- STATUS: PROVED (Zc.zcBaseIn; round 131, new; checked only after the merge)
SIZE: S
THE BASE REACH DATUM OF `W_k` (the part of `Yx.YxIn` at the base) from LOWER and the caps below `L(k)`:
`L(k) ≤₁ υ_{ι(L(k))+ω²}` by the realizer maps of the shift with the supply `Rx.rxSupAt`. -/
theorem skWinBase (S : InaccSeq.{0}) (k : ℕ) (h0 : Cd.CdCAP0 S)
    (hb : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → Cd.CdCapAt S μ)
    (hL : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S (k : Ordinal.{0}) → Cd.CdLower S μ) :
    Ys.YsReachIn (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) 0
      (upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))) :=
  Zc.zcBaseIn k h0 hb hL

/-- STATUS: PROVED (Zc.zcRsTerm_long_false; round 131, new; checked only after the merge)
SIZE: S
NO-GO: at a restart whose bound reaches `υ_{λ+ω²}` the term input of Lemma RS is false. -/
theorem skRsLongNoGo {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlong : upsilon (l + ω * ω) ≤ upsilon (l + ω + 1) + O l) : ¬ Zc.ZcRsTerm O l :=
  Zc.zcRsTerm_long_false hl hlong

/-- STATUS: PROVED (Zc.zcRsIn_long_lower; round 131, new; checked only after the merge)
SIZE: S
At a supply restart the RS input is LOWER. -/
theorem skRsLongLower (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlong : upsilon (l + ω * ω) ≤ Cd.cdR S l) (h : Zc.ZcRsIn (Ys.ysO S) l) : Cd.CdLower S l :=
  Zc.zcRsIn_long_lower hl hlong h

/-- STATUS: PROVED (Zc.zcGiven_of_up; round 131, new; checked only after the merge)
SIZE: S
The given input at a restart from UPPER there and `ρ_λ ≤₁ υ_{λ+ω²}`. -/
theorem skGivenOfUp (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hU : Cd.CdUpper S l)
    (hE : le1 (upsilon l) (upsilon (l + ω * ω))) : Yx.YxGivenIn (Ys.ysO S) l :=
  Zc.zcGiven_of_up hl hU hE

/-- STATUS: PROVED (Zc.zcWins2_of_target; round 131, new; checked only after the merge)
SIZE: S
NON-VACUITY of the new window leaves skWinInR and skWinRsT: they follow from UPPER, LOWER, CapV at the Range
restarts below `L(ω)` and the chain reach data. -/
theorem skWinInRVac (S : InaccSeq.{0})
    (hU : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S ω → Cd.CdUpper S μ)
    (hL : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S ω → Cd.CdLower S μ)
    (hV : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S ω → Cd.CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → upsilon l < Nc.ncL S ω → Ys.YsReachIn l 0 (upsilon l)) :
    (∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) ∧
    (∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → Zc.ZcRsIn (Ys.ysO S) l) :=
  ⟨(Zc.zcWins2_of_target hU hL hV hR).1, (Zc.zcWins2_of_target hU hL hV hR).2.2.2⟩

/-- STATUS: OPEN (round 130, new leaf, regw5; the pair part of the old skTopSpec)
SIZE: L
THE PAIR HYPOTHESIS AT `L(ω)`: if `ν_C < L(ω+1)` then not `L(ω) <₂ ν_C`.  REFUTE FIRST: SUSPECT as a leaf (not
refuted): it follows from the target `L(ω+1) ≤ ν_C` (`Yx.yxLwNo2_of_nu`) and, with the pair-free specification on
`W_ω` and the caps below `L(ω+1)`, implies it (`Yx.yxLwNo2_iff`): it is the whole pair content of the top window
(the old skTopSpec contained it, cf. `Rg.rgNu_iff_pair`).  Its negation would put the left end of the first
non-standard pair at `L(ω)` with `≤₁`-predecessors that may all be points `L(k)` (code `P'`, no cap below `ν_C`),
so the cap argument `Yx.yxNu_gt` cannot close it; it needs the `≤₂`-copies of `[L(ω), ν_C)` below `L(ω)`.
Round 131 REFUTE FIRST: NO EVIDENCE (its negation contradicts the road's conclusion `L(ω+1) ≤ ν_C`; the clause-1
copies of `L(ω) <₂ ν_C` map the pairs of `[L(ω), ν_C)` to pairs below `L(ω)`, all standard there, so they give no
contradiction by themselves; the clause-2 (cofinal covering) transfer is the open part). -/
theorem skTopLwNo2 (S : InaccSeq.{0}) : Yx.YxLwNo2 S := by
  sorry

/-- STATUS: REPLACED (round 131, regw6: by skWinRsT, the RS step being a theorem for offset terms,
`Zc.zcRs_rstT`; not used; was OPEN L)
SIZE: L
THE RS INPUT IN `W_k`: at every restart of the window LOWER itself, or a successor index with `O = 1`, or a limit
index with the relative RS input `Ys.YsRsIn` (terms with a relative RS step `Ys.YsRsStep`, realized cofinally).
REFUTE FIRST: NO EVIDENCE (the successor branch is a theorem, `Ys.ysRs_succ`; non-vacuity below `Ξ_ω`:
`Ys.ysRsIn_old`). -/
theorem skWinRsIn (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l) := by
  sorry

/-- STATUS: PROVED (definitions; round 129, new)
SIZE: S
the RS input depends on the bound only at and below the restart: the input with `ysO` is the input with any `O`
that equals `ysO` above the base. -/
theorem skRsInCongr {l0 : Ordinal.{0}} {O O' : Ordinal.{0} → Ordinal.{0}} (h : ∀ μ, l0 < μ → O μ = O' μ)
    {l : Ordinal.{0}} (hl : l0 < l)
    (hin : le1 (upsilon l) (upsilon (l + ω + 1) + O' l) ∨ (cL l < 2 ∧ O' l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O' l ∧ Ys.YsRsIn O' l)) :
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) ∨ (cL l < 2 ∧ O l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ O l ∧ Ys.YsRsIn O l) := by
  rw [h l hl]
  rcases hin with h1 | h1 | ⟨h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · refine Or.inr (Or.inr ⟨h2, h3, fun z hz => ?_⟩)
    have hz' : z < O' l := by rw [← h l hl]; exact hz
    obtain ⟨T, hT1, hT2, hT3⟩ := h4 z hz'
    refine ⟨T, hT1, hT2, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, hνμ, hμl, hTμ⟩ := hT3 (max ν l0) (max_lt hν hl)
    exact ⟨μ, hμ, (le_max_left _ _).trans_lt hνμ, hμl, by
      rw [h μ ((le_max_right _ _).trans_lt hνμ)]; exact hTμ⟩

/-- STATUS: REPLACED (round 132, regw7: by skWinCapVAll, proved from skWinAll and the long-exponent leaf
skWinCapVL; not used; was OPEN L, round 129, new leaf, regw4; the CapV part of the old skWinA / skWinL)
SIZE: L
CapV at every range restart of `W_k`. -/
theorem skWinCapV (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, Cd.CdRange S l → Wj.WjWin S k l → Cd.CdCapV S l := by
  sorry

/-- STATUS: REPLACED (round 133, regw8: by skWinCapVF, asked only below `ν_C` where `δ_λ·ω ≤ Θ_λ(m_λ)`; not used;
was OPEN L, round 132, new leaf, regw7; the part of skWinCapV that is not a theorem)
SIZE: L
CapV at the `υ`-FIXED range restarts of `W_k` WITHOUT a short last exponent (`Zh.ZhShortExp`: `2 ≤ e(η_λ) < ρ_λ`;
every restart with `λ < υ_λ` has one, `Zh.zh_short_of_nonfix`, so CapV there is skCapVNonfix).  At the
short exponents CapV is a THEOREM below `ν_C` (`Zh.zhCapV_short`: `r(λ) = δ_λ + (-1+e) < υ_{λ+ω^e} = P(η_λ+ω^e)`),
and the window induction reads CapV only below `ν_C` (`Zh.zhSpec_capsV`).  REFUTE FIRST at the first range restart
of `W₁` (name `Ω_ω + P' + ω²`, `e = 2`): it has a short exponent, so CapV holds there (skCapVShort); NO EVIDENCE
against the leaf. -/
theorem skWinCapVL (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, Cd.CdRange S l → Wj.WjWin S k l → upsilon l = l → ¬ Zh.ZhShortExp S l → Cd.CdCapV S l := by
  sorry

/-- STATUS: REPLACED (round 131, regw6: by skTopRsT; not used; was OPEN L)
SIZE: L
THE RS INPUT IN `W_ω` (as skWinRsIn). -/
theorem skTopRsIn (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      le1 (upsilon l) (upsilon (l + ω + 1) + Ys.ysO S l) ∨ (cL l < 2 ∧ Ys.ysO S l = 1) ∨
        (2 ≤ cL l ∧ 1 ≤ Ys.ysO S l ∧ Ys.YsRsIn (Ys.ysO S) l) := by
  sorry

/-- STATUS: REPLACED (round 132, regw7: by skTopCapVAll, proved from skTopAll and the long-exponent leaf
skTopCapVL; not used; was OPEN L, round 129, new leaf, regw4; the CapV part of the old skTopA / skTopL; hVt of the
road)
SIZE: L
CapV at every range restart of `W_ω`. -/
theorem skTopCapV (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → Cd.CdCapV S l := by
  sorry

/-- STATUS: REPLACED (round 133, regw8: by skTopCapVF; not used; was OPEN L, round 132, new leaf, regw7; the part
of skTopCapV that is not a theorem)
SIZE: L
CapV at the range restarts of `W_ω` without a short last exponent (as skWinCapVL). -/
theorem skTopCapVL (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Wj.WjTop S l → upsilon l = l → ¬ Zh.ZhShortExp S l → Cd.CdCapV S l := by
  sorry

/-- STATUS: PROVED (Zh.zhCapV_short; round 132, new; checked only after the merge)
SIZE: S
CAPV AT A SHORT LAST EXPONENT below `ν_C` (REFUTE FIRST for skWinCapV at the first range restart of `W₁`). -/
theorem skCapVShort {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (he2 : ω ^ 2 ≤ ω ^ Cd.cdExp (Cd.cdEta S l))
    (heρ : Cd.cdExp (Cd.cdEta S l) < upsilon l) : Cd.CdCapV S l :=
  Zh.zhCapV_short hl hν hn he2 heρ

/-- STATUS: PROVED (Zh.zhR_nonfix; round 132, new; checked only after the merge)
SIZE: S
THE PREDICTED REACH OF A NON-FIXED RESTART below `ν_C`: `ω² < λ < υ_λ` ⇒ `m_λ = cL λ`, `r(λ) = δ_λ + cL λ`. -/
theorem skRNonfix {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) :
    Cd.cdR S l = Cd.cdDelta l + cL l :=
  Zh.zhR_nonfix hl hww hfix hν hn

/-- STATUS: PROVED (Zh.zhSup_fix; round 132, new; checked only after the merge)
SIZE: S
EVERY SUPPLY RESTART BELOW `ν_C` IS A `υ`-FIXED POINT. -/
theorem skSupFix {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) (hlong : upsilon (l + ω ^ 2) ≤ Cd.cdR S l) :
    upsilon l = l :=
  Zh.zhSup_fix hl hww hν hn hlong

/-- STATUS: PROVED (Zh.zhRsIn_nonfix; round 132, new; checked only after the merge)
SIZE: M
THE RS INPUT AT EVERY NON-FIXED RESTART BELOW `ν_C` (the term input at the ordinary limit restarts: constant
terms `w < cL λ`, realized by `R2.cL_dense`; the successor case `O = 1`). -/
theorem skRsNonfix {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) :
    Zc.ZcRsIn (Ys.ysO S) l :=
  Zh.zhRsIn_nonfix hl hww hfix hν hn

/-- STATUS: PROVED (Zh.zhCapV_nonfix; round 132, new; checked only after the merge)
SIZE: S
CAPV AT EVERY NON-FIXED RESTART BELOW `ν_C`. -/
theorem skCapVNonfix {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1) : Cd.CdCapV S l :=
  Zh.zhCapV_nonfix hl hww hfix hν hn

/-- STATUS: PROVED (round 136, Zt.ztIsoCode from Fx.fxIso_theta; was OPEN L, round 133, new leaf, regw8; part of
skWinRsF)
SIZE: L
THE CODE STATEMENT AT THE ISOLATED FIXED RESTARTS OF `W_k` (`Zn.ZnIsoCode`): at every `υ`-fixed restart `λ` of the
window with `Cp.CpIso λ` (no fixed restart in some `(ν, λ)`), `Θ_λ(m_λ) ≤ ρ_λ` (it follows from `m_λ ≤ Ω₁`,
`Zn.zn_theta_le_of_code`; below `cpB1` the isolated fixed points have this form, `Cp.cpFix_code`).  A statement on
the names and codes only (no `≤₁`).  REFUTE FIRST: NO EVIDENCE; it is NEEDED for the road as built: at an isolated
fixed restart with `ρ_λ < Θ_λ(m_λ)` the supply, term, value and successor branches are all false (skSupIsoNoGo,
skTermIsoNoGo, skValIsoNoGo), so the RS input is LOWER itself there (skIsoLower).  Round 136: at an isolated
fixed restart with a name the name is `η₁ + Ω₁`, the code is `Ω₁` and `Θ_λ(m_λ) = λ = ρ_λ` (`Fx.fxIso_eta`,
`Fx.fxIso_code`, `Fx.fxIso_theta`, no range bound), and every restart below `ι(η)` has a name: `Zt.ztIsoCode`. -/
theorem skWinIsoCode (S : InaccSeq.{0}) (k : ℕ) : Zn.ZnIsoCode S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
  Zt.ztIsoCode _ _

/-- STATUS: PROVED (round 136, Zt.ztIsoCode; was OPEN L, round 133, new leaf, regw8; part of skTopRsF)
SIZE: L
THE CODE STATEMENT AT THE ISOLATED FIXED RESTARTS OF `W_ω` (as skWinIsoCode). -/
theorem skTopIsoCode (S : InaccSeq.{0}) : Zn.ZnIsoCode S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) :=
  Zt.ztIsoCode _ _

/-- STATUS: OPEN (round 138: one leaf for every window, replaces skWinCont and skTopCont; round 133, regw8)
SIZE: L
THE CODE CONTINUITY AT THE NON-ISOLATED FIXED RESTARTS OF THE WINDOWS `(ι(L(0)), ι(L(ω+1)))` WITH A READING IN
`(ρ_λ, υ_{λ+1}]` (`Zn.ZnThCont`; the same statement in every window `W_k` and in `W_ω`, and no `≤₁`, so no `ν_C`
hypothesis): every `z < Θ_λ(m_λ)` is below a value `v < υ_{λ+1}` with `π_{ρ_μ,ρ_λ}(v) ≤ Θ_μ(m_μ)` at restarts
`μ` cofinal below `λ`.  It follows from the hull form `Zn.znThCont_of_code` (for every hull code `c < m_λ`,
cofinally `π(Θ_λ(c)) ≤ Θ_μ(m_μ)`, e.g. from `π(Θ_λ(c)) = Θ_μ(c)` and `c ≤ m_μ`).  Round 137 analysis: the codes
are in `(Ω₁, θ]`; the missing link is `π` on the readings (no lemma computes `π` of a value `ψ_{Ω₁}(A + x)`;
`vt_rep` gives `Θ_λ(c) = ϑ^{ρ_λ}(ξ)` for a principal reading, the map `c ↦ ξ` is not formalized).  Round 138: the
layer reading systems prove such a link (`Zm.ZmDS`: Lemma EXACT for explicit readings `R(o)(x)`) for their codes;
codes below `θ` past them (e.g. `ψ_{Ω₂}(ψ_{Ω₃}(Ω_ω·2))` at a window, where `A ≥ Ω_ω·2`) are the content of
skZbDirectX, skLayPastX.  REFUTE FIRST: NO EVIDENCE (at a limit of fixed restarts with `Θ_λ(m_λ) = ρ_λ+1` it
holds with `v = ρ_λ`, `π(ρ_λ) = ρ_μ`, `Cl.pi_base`, at the fixed `μ`). -/
theorem skFixCont (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω) < l → l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l →
      ¬ Cp.CpIso l → upsilon l < Cd.cdTheta S l (Cd.cdCode S l) →
      Cd.cdTheta S l (Cd.cdCode S l) ≤ upsilon (Order.succ l) → Zn.ZnThCont S l := by
  sorry

/-- STATUS: PROVED (round 138, from skFixCont; was OPEN L, round 133, new leaf, regw8; part of skWinRsF)
SIZE: L
THE CODE CONTINUITY AT THE NON-ISOLATED FIXED RESTARTS OF `W_k` WITH A READING IN `(ρ_λ, υ_{λ+1}]`
(`Zn.ZnThCont`): every `z < Θ_λ(m_λ)` is below a value `v < υ_{λ+1}` with `π_{ρ_μ,ρ_λ}(v) ≤ Θ_μ(m_μ)` at restarts
`μ` cofinal below `λ`.  A statement on the readings and the base change only (no `≤₁`); it follows from the hull
form `Zn.znThCont_of_code` (for every hull code `c < m_λ`, cofinally `π(Θ_λ(c)) ≤ Θ_μ(m_μ)`, e.g. from
`π(Θ_λ(c)) = Θ_μ(c)` and `c ≤ m_μ`).  REFUTE FIRST: NO EVIDENCE (at a limit of fixed restarts with `Θ_λ(m_λ) = ρ_λ+1`
it holds with `v = ρ_λ`, `π(ρ_λ) = ρ_μ`, `Cl.pi_base`, at the fixed `μ`). -/
theorem skWinCont (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l → l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l → ¬ Cp.CpIso l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      upsilon l < Cd.cdTheta S l (Cd.cdCode S l) → Cd.cdTheta S l (Cd.cdCode S l) ≤ upsilon (Order.succ l) →
      Zn.ZnThCont S l := by
  intro l hl h1 h2 hfix hiso _ hθ1 hθ2
  refine skFixCont S l hl ((Bt.iota_mono (S := S) _ _ le_self_add).trans_lt h1)
    (h2.trans_le (Bt.iota_mono (S := S) _ _ (add_le_add le_rfl (mul_le_mul_left' ?_ _)))) hfix hiso hθ1 hθ2
  exact_mod_cast (show ((k + 1 : ℕ) : Ordinal.{0}) ≤ ω + 1 from
    (Ordinal.natCast_lt_omega0 (k + 1)).le.trans le_self_add)

/-- STATUS: PROVED (round 138, from skFixCont; was OPEN L, round 133, new leaf, regw8; part of skTopRsF)
SIZE: L
THE CODE CONTINUITY IN `W_ω` (as skWinCont). -/
theorem skTopCont (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l → l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l → ¬ Cp.CpIso l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC →
      upsilon l < Cd.cdTheta S l (Cd.cdCode S l) → Cd.cdTheta S l (Cd.cdCode S l) ≤ upsilon (Order.succ l) →
      Zn.ZnThCont S l := by
  intro l hl h1 h2 hfix hiso _ hθ1 hθ2
  exact skFixCont S l hl ((Bt.iota_mono (S := S) _ _ le_self_add).trans_lt h1) h2 hfix hiso hθ1 hθ2

/-- STATUS: OPEN (round 133, new leaf, regw8; part of skWinRsF)
SIZE: L
LOWER OR THE SUPPLY AT THE NON-ISOLATED FIXED RESTARTS OF `W_k` WITH `υ_{λ+1} < Θ_λ(m_λ)`: there the term, value
and successor branches are false (skBigLower), so the RS input is LOWER or the supply `Zh.ZhSupInB`.  REFUTE
FIRST: NO EVIDENCE (the supply branch needs supply restarts cofinal below `λ`, which are fixed, `Zh.zhSup_fix`). -/
theorem skWinBig (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l → l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l → ¬ Cp.CpIso l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      upsilon (Order.succ l) < Cd.cdTheta S l (Cd.cdCode S l) →
      Cd.CdLower S l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) := by
  sorry

/-- STATUS: OPEN (round 133, new leaf, regw8; part of skTopRsF)
SIZE: L
LOWER OR THE SUPPLY IN `W_ω` (as skWinBig). -/
theorem skTopBig (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l → l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l → ¬ Cp.CpIso l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC →
      upsilon (Order.succ l) < Cd.cdTheta S l (Cd.cdCode S l) →
      Cd.CdLower S l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) := by
  sorry

/-- STATUS: REDUCED (Zn.znRsF_of_parts2; skWinIsoCode, skWinCont, skWinBig; round 133, new, regw8; replaces
skWinRsS; checked only after the merge)
SIZE: L
THE RS INPUT IN `W_k` AT THE `υ`-FIXED RESTARTS WITH `ρ_λ < Θ_λ(m_λ)`, given `υ_{B_k} ≤ ν_C`: `ZcRsIn`, the supply
`Zh.ZhSupInB` or the value input `Zn.ZnRsVal`.  At the other restarts the input is a theorem (`Zh.zhRsIn_nonfix`,
`Zn.znRsIn_fixShort`). -/
theorem skWinRsF (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l → l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC →
      upsilon l < Cd.cdTheta S l (Cd.cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨ Zn.ZnRsVal (Ys.ysO S) l :=
  Zn.znRsF_of_parts2 (skWinIsoCode S k) (skWinCont S k) (skWinBig S k)

/-- STATUS: REDUCED (Zn.znRsF_of_parts2; skTopIsoCode, skTopCont, skTopBig; round 133, new, regw8; replaces
skTopRsS; checked only after the merge)
SIZE: L
THE RS INPUT IN `W_ω` AT THE `υ`-FIXED RESTARTS WITH `ρ_λ < Θ_λ(m_λ)` (as skWinRsF). -/
theorem skTopRsF (S : InaccSeq.{0}) :
    ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l → l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ≤ nuC →
      upsilon l < Cd.cdTheta S l (Cd.cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∨ Zn.ZnRsVal (Ys.ysO S) l :=
  Zn.znRsF_of_parts2 (skTopIsoCode S) (skTopCont S) (skTopBig S)

/-- STATUS: PROVED (round 138, from skFixCapVF; was OPEN L, round 133, new leaf, regw8; replaces skWinCapVL)
SIZE: L
CAPV AT THE `υ`-FIXED RANGE RESTARTS OF `W_k` WITH A FAR READING `δ_λ·ω ≤ Θ_λ(m_λ)`, below `ν_C`.  At the other
restarts CapV is a theorem below `ν_C` (`Zh.zhCapV_nonfix`, `Zh.zhCapV_short`, `Zn.znCapV_fixThW`).  REFUTE FIRST
(at the first fixed restart of `W₁`): CapV holds there when `Θ_λ(m_λ) < δ_λ·ω`; NO EVIDENCE against the leaf. -/
theorem skWinCapVF (S : InaccSeq.{0}) (k : ℕ) :
    ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → upsilon μ < nuC →
      Cd.cdDelta μ * ω ≤ Cd.cdTheta S μ (Cd.cdCode S μ) → Cd.CdCapV S μ := by
  intro μ hr hw hfix hν hfar
  refine skFixCapVF S μ hr ?_ hfix hν hfar
  refine upsilon_normal.strictMono.lt_iff_lt.1 (Zs.zsLt_L0.trans_le ?_ |>.trans hw.1)
  exact Pp.ppL_mono (S := S) zero_le

/-- STATUS: PROVED (round 138, from skFixCapVF; was OPEN L, round 133, new leaf, regw8; replaces skTopCapVL)
SIZE: L
CAPV AT THE `υ`-FIXED RANGE RESTARTS OF `W_ω` WITH A FAR READING (as skWinCapVF). -/
theorem skTopCapVF (S : InaccSeq.{0}) :
    ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → upsilon μ = μ → upsilon μ < nuC →
      Cd.cdDelta μ * ω ≤ Cd.cdTheta S μ (Cd.cdCode S μ) → Cd.CdCapV S μ := by
  intro μ hr hw hfix hν hfar
  refine skFixCapVF S μ hr ?_ hfix hν hfar
  refine upsilon_normal.strictMono.lt_iff_lt.1 (Zs.zsLt_L0.trans_le ?_ |>.trans hw.1)
  exact Pp.ppL_mono (S := S) zero_le

/-- STATUS: PROVED (Zn.znRs_rstV; round 133, new; checked only after the merge)
SIZE: L
LEMMA RS WITH A VALUE: `v < υ_{r+1}`, no pair from a point `≤ ρ` into `[ρ, δ+v]`, and restarts `μ` cofinal below
`ρ` with `ρ_μ ≤₁ g` for `g ≤ δ_μ + π_{ρ_μ,ρ}(v)` give `ρ ≤₁ δ + v + 1`. -/
theorem skValRS {r v : Ordinal.{0}} (h : Ys.YsRstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    (hv : v < upsilon (Order.succ r))
    (hnostr : ∀ c d, c < d → c ≤ upsilon r → upsilon r ≤ d → d ≤ upsilon (r + ω + 1) + v → ¬ le2 c d)
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      Ys.YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + pi (upsilon μ) (upsilon r) v → le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + v + 1) :=
  Zn.znRs_rstV h hv hnostr htarget

/-- STATUS: PROVED (Zn.znVal_of_term; round 133, new; checked only after the merge)
SIZE: S
The term input gives the value input. -/
theorem skValOfTerm {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl1 : upsilon l < Om1) (h : Zc.ZcRsTerm O l) : Zn.ZnRsVal O l :=
  Zn.znVal_of_term hl hl1 h

/-- STATUS: PROVED (Zn.znRsTerm_false; round 133, new; checked only after the merge)
SIZE: S
NO-GO for the term input: an `ε`-number in `(ρ_λ, O(λ))` refutes it. -/
theorem skTermEpsNoGo {O : Ordinal.{0} → Ordinal.{0}} {l E : Ordinal.{0}} (hE : InE E) (hρE : upsilon l < E)
    (hEO : E < O l) : ¬ Zc.ZcRsTerm O l :=
  Zn.znRsTerm_false hE hρE hEO

/-- STATUS: PROVED (Zn.znRsIn_fixShort; round 133, new; checked only after the merge)
SIZE: M
THE RS INPUT AT A FIXED RESTART WITH `Θ_λ(m_λ) ≤ ρ_λ` (below `ν_C`). -/
theorem skRsFixShort {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : Cd.cdTheta S l (Cd.cdCode S l) ≤ upsilon l) : Zc.ZcRsIn (Ys.ysO S) l :=
  Zn.znRsIn_fixShort hl hfix hν hn hθ

/-- STATUS: PROVED (Zn.znCapV_fixThW; round 133, new; checked only after the merge)
SIZE: S
CAPV AT A FIXED RESTART WITH `Θ_λ(m_λ) < δ_λ·ω` (below `ν_C`). -/
theorem skCapVFixW {S : InaccSeq.{0}} {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : Cd.cdTheta S l (Cd.cdCode S l) < Cd.cdDelta l * ω) : Cd.CdCapV S l :=
  Zn.znCapV_fixThW hl hfix hν hn hθ

/-- STATUS: PROVED (Zn.znSupInB_false; round 133, new; checked only after the merge)
SIZE: S
REFUTE FIRST (a): THE SUPPLY BRANCH IS FALSE AT AN ISOLATED FIXED RESTART (every `β`, `β = ω²+ω+1` included). -/
theorem skSupIsoNoGo {S : InaccSeq.{0}} {l B x0 η1 : Ordinal.{0}} (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hpos : 0 < Cd.cdTheta S l (Cd.cdCode S l)) (hx0 : upsilon (ω * ω) ≤ x0)
    (hx0l : x0 < upsilon l)
    (hiso : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ) :
    ¬ Zh.ZhSupInB S l B :=
  Zn.znSupInB_false hν hn hpos hx0 hx0l hiso

/-- STATUS: PROVED (Zn.znRsTerm_iso_false; round 133, new; checked only after the merge)
SIZE: S
NO-GO for the term branch at an isolated fixed restart with `ρ_λ < O(λ)`. -/
theorem skTermIsoNoGo {S : InaccSeq.{0}} {l x0 η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hx0 : upsilon (ω * ω) ≤ x0) (hx0l : x0 < upsilon l)
    (hiso : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ)
    (hlong : upsilon l < Ys.ysO S l) : ¬ Zc.ZcRsTerm (Ys.ysO S) l :=
  Zn.znRsTerm_iso_false hl hν hn hx0 hx0l hiso hlong

/-- STATUS: PROVED (Zn.znRsVal_iso_false; round 133, new; checked only after the merge)
SIZE: S
NO-GO for the value branch at an isolated fixed restart with `ρ_λ < O(λ)`. -/
theorem skValIsoNoGo {S : InaccSeq.{0}} {l x0 η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (hx0 : upsilon (ω * ω) ≤ x0) (hx0l : x0 < upsilon l)
    (hiso : ∀ μ, IsRestartIdx μ → x0 < upsilon μ → upsilon μ < upsilon l → μ < upsilon μ)
    (hlong : upsilon l < Ys.ysO S l) : ¬ Zn.ZnRsVal (Ys.ysO S) l :=
  Zn.znRsVal_iso_false hl hν hn hx0 hx0l hiso hlong

/-- STATUS: PROVED (Zn.znIn_iso_lower; round 133, new; checked only after the merge)
SIZE: S
AT AN ISOLATED FIXED RESTART WITH `ρ_λ < Θ_λ(m_λ)` THE RS INPUT IS LOWER. -/
theorem skIsoLower {S : InaccSeq.{0}} {l B η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hiso : Cp.CpIso l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (hθ : upsilon l < Cd.cdTheta S l (Cd.cdCode S l))
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l B ∨ Zn.ZnRsVal (Ys.ysO S) l) : Cd.CdLower S l :=
  Zn.znIn_iso_lower hl hfix hiso hν hn hθ h

/-- STATUS: PROVED (Zn.znRsIn_big_lower; round 133, new; checked only after the merge)
SIZE: S
AT A FIXED RESTART WITH `υ_{λ+1} < Θ_λ(m_λ)` THE INPUT `ZcRsIn ∨ ZnRsVal` IS LOWER. -/
theorem skBigLower {S : InaccSeq.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l = l)
    (hbig : upsilon (Order.succ l) < Cd.cdTheta S l (Cd.cdCode S l))
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ Zn.ZnRsVal (Ys.ysO S) l) : Cd.CdLower S l :=
  Zn.znRsIn_big_lower hl hfix hbig h

/-- STATUS: PROVED (Zn.znInputs_of_zh; round 133, new; checked only after the merge)
SIZE: S
NON-VACUITY of skWinCapVF / skWinRsF: the round-132 inputs (skWinCapVL, skWinRsS) give them. -/
theorem skInputsVac {S : InaccSeq.{0}}
    (hVF : ∀ k : ℕ, ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → ¬ Zh.ZhShortExp S μ → Cd.CdCapV S μ)
    (hrsF : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l → l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    (∀ k : ℕ, ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → upsilon μ = μ → upsilon μ < nuC →
      Cd.cdDelta μ * ω ≤ Cd.cdTheta S μ (Cd.cdCode S μ) → Cd.CdCapV S μ) ∧
    (∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l → l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) → upsilon l = l →
      upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ≤ nuC → upsilon l < Cd.cdTheta S l (Cd.cdCode S l) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ Zh.ZhSupInB S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∨ Zn.ZnRsVal (Ys.ysO S) l) :=
  Zn.znInputs_of_zh hVF hrsF

/-- STATUS: PROVED, OFF THE ROAD (Zn.znShortIn_of_sep, Zn.znSep_exists; round 133, new; checked only after the merge)
SIZE: M
THE SHORT WINDOW INPUT AT A NON-FIXED RESTART BELOW `ν_C` (the part of skWinInR / skTopInR at the non-fixed
restarts): `Yx.YxShortIn` with `m = 0`, `k = c(λ)` from the separated chain reach datum `Zn.ZnSepReach`; the
separation itself exists (`Zn.znSep_exists`), so only `Ys.YsReachIn λ c(λ) x₀` at one separated `x₀` is left.  Off
the road because skWinInR is asked without `ρ_λ < ν_C`. -/
theorem skShortInNonfix {S : InaccSeq.{0}} {a l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hww : ω * ω < l)
    (hfix : l < upsilon l) (hν : upsilon l < nuC) (hn : upsilon l < Nm.Pv S η1)
    (h : Zn.ZnSepReach a l) : Yx.YxShortIn a (Ys.ysO S) l :=
  Zn.znShortIn_of_sep hl hww hfix hν hn h

/-- STATUS: REDUCED (skSplit, skRegA, skRegBlo, skRegBhi, skLongPre; round 130, new)
SIZE: S
ENUM-REACH and CapV at every range restart below `L(0)` (the windows lie above `L(0)`). -/
theorem skBelowL0 (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S 0 → SkUV S l := by
  intro l hr h0
  rcases skSplit S hr with hA | ⟨hn, hu, he, hi⟩ | ⟨hn, hu, he, hi⟩ | ⟨hu, he⟩ | ⟨k, hw⟩ | hw
  · exact skRegA S l hr hA
  · exact skRegBlo S l hr hn hu he hi
  · exact skRegBhi S l hr hn hu he hi
  · exact skLongPre S l hr he hu
  · exact absurd (hw.1.trans h0) (not_lt.2 (Pp.ppL_mono (S := S) zero_le))
  · exact absurd (hw.1.trans h0) (not_lt.2 (Pp.ppL_mono (S := S) zero_le))

/-- STATUS: REDUCED (Zn.znWins; skWinInR, skBelowL0, skWinCapVF, skWinRsF; round 133: was Zh.zhWins6 with skWinCapVL,
skWinRsS; round 132: was Zc.zcWins2 with skWinRsT,
skWinCapV;
round 131: was Yx.yxWins with
skWinIn, skWinRsIn; round 130, new; checked only after the merge)
SIZE: L
ALL WINDOWS BY ONE INDUCTION ON `k`: for every `k`, `L(k+1) ≤ ν_C`, the relative block specification `Ys.YsSpec` on
`W_k` (bound `Yx.yxO`) and UPPER ∧ LOWER at every range restart of `W_k`.  The pair fields come from the caps
below `L(k)` (skBelowL0 and the windows `W_j`, `j < k`, with skWinCapV) by `Yx.yxSpec_caps`; the landing blocks
below `L(k)` from `L(k) < ν_C` (`R2.land_C`). -/
theorem skWinAll (S : InaccSeq.{0}) : ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
    Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
      (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
    ∀ μ, Cd.CdRange S μ → Wj.WjWin S k μ → Cd.CdUpper S μ ∧ Cd.CdLower S μ :=
  Zn.znWins (skWinInR S) (skBelowL0 S) (skWinCapVF S) (skWinRsF S)

/-- STATUS: REDUCED (Zn.znTopAll; skWinAll's leaves, skTopInR, skTopCapVF, skTopRsF, skTopLwNo2; round 133: was
Zh.zhTopAll6 with skTopCapVL, skTopRsS; round 132: was
Zc.zcTopAll2 with skTopRsT, skTopCapV; round 131: was
Yx.yxTopAll with skWinIn, skTopIn, skWinRsIn, skTopRsIn; round 130, new;
checked only after the merge)
SIZE: L
THE TOP WINDOW: `L(ω+1) ≤ ν_C`, `Ys.YsSpec` on `W_ω` and UPPER ∧ LOWER at every range restart of `W_ω`. -/
theorem skTopAll (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC ∧
    Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
      (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
    ∀ μ, Cd.CdRange S μ → Wj.WjTop S μ → Cd.CdUpper S μ ∧ Cd.CdLower S μ :=
  Zn.znTopAll (skWinInR S) (skBelowL0 S) (skWinCapVF S) (skWinRsF S)
    (skTopInR S) (skTopCapVF S) (skTopRsF S) (skTopLwNo2 S)

/-- STATUS: PROVED (Zn.znWinCapV_all, Zn.znVL_of_fixW; round 133: was Zh.zhWinCapV_all with skWinCapVL; round 132,
new; checked only after the merge)
SIZE: S
CAPV AT EVERY RANGE RESTART OF `W_k` (replaces skWinCapV): the long exponents from skWinCapVL, the short ones
from `Zh.zhCapV_short` with `L(k+1) ≤ ν_C` (skWinAll). -/
theorem skWinCapVAll (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, Cd.CdRange S l → Wj.WjWin S k l → Cd.CdCapV S l :=
  Zn.znWinCapV_all k (skWinAll S k).1 (Zn.znVL_of_fixW k (skWinCapVF S k))

/-- STATUS: PROVED (Zn.znTopCapV_all, Zn.znVLT_of_fixW; round 133: was Zh.zhTopCapV_all with skTopCapVL; round
132, new; checked only after the merge)
SIZE: S
CAPV AT EVERY RANGE RESTART OF `W_ω` (replaces skTopCapV). -/
theorem skTopCapVAll (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → Cd.CdCapV S l :=
  Zn.znTopCapV_all (skTopAll S).1 (Zn.znVLT_of_fixW (skTopCapVF S))

/-- STATUS: PROVED (Yx.yxSpec_nu; round 130, new)
SIZE: S
REFUTE FIRST for the old window leaves: the pair field of `Ys.YsSpec O l₀ B` excludes `ν_C` from `[ρ_{l₀}, υ_B)`
(at the index of `ν_C` the first non-standard pair breaks `nostr`), so the old skWinSpec / skTopSpec contained
`ν_C ∉ W_k` / `ν_C ∉ W_ω`. -/
theorem skWinSpecNu {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B) :
    ¬ (upsilon l0 ≤ nuC ∧ nuC < upsilon B) := Yx.yxSpec_nu Sp

/-- STATUS: PROVED (Yx.yxNu_gt; round 130, new)
SIZE: S
STRICT NU-LOW″ at every height `X ≤ L(ω)`: CAP-0 and CAP-1 below `X` give `X < ν_C`. -/
theorem skNuGt (S : InaccSeq.{0}) {X : Ordinal.{0}} (hX : X ≤ Nc.ncL S ω) (h0 : Cd.CdCAP0 S)
    (h1 : Cd.CdCAP1 S X) : X < nuC := Yx.yxNu_gt hX h0 h1

/-- STATUS: PROVED (Yx.yxWins_of_target; round 130, new; checked only after the merge)
SIZE: S
NON-VACUITY of skWinAll: its hypotheses (skWinIn, the part of skBelowL0 it uses, skWinCapV, skWinRsIn) follow from
UPPER, LOWER, CapV at the range restarts below `L(ω)` and the chain reach data `Ys.YsReachIn l 0 ρ_l`. -/
theorem skWinAllVac (S : InaccSeq.{0})
    (hU : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S ω → Cd.CdUpper S μ)
    (hL : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S ω → Cd.CdLower S μ)
    (hV : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S ω → Cd.CdCapV S μ)
    (hR : ∀ l, IsRestartIdx l → upsilon l < Nc.ncL S ω → Ys.YsReachIn l 0 (upsilon l)) :
    ∀ k : ℕ, Yx.YxIn S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
  (Yx.yxWins_of_target hU hL hV hR).1

/-- STATUS: REDUCED (skWinAll; round 130, regw5: was OPEN L; statement unchanged; checked only after the merge)
SIZE: L
THE RELATIVE BLOCK SPECIFICATION ON THE WINDOW `W_k`: `Ys.YsSpec` on `[ι(Ω_ω + P′·k), ι(Ω_ω + P′·(k+1)))` with the
bound `O = r − δ` above the base.  Round 130: its three pair fields (`nostr` and the chain datum `Ys.YsNostrIn` in
both inputs) are no longer asked: they contain `ν_C ∉ [L(k), L(k+1))` (`Yx.yxSpec_nu`), and they follow from
`υ_B ≤ ν_C` (`Yx.YxSpec.toYs`), which the least-counterexample argument `Yx.yxSpec_caps` gets from the caps below
the window (Lemma TOP inside the window, `Yx.yxNu_gt`).  The bound at the base is `ν_C` (`Yx.yxO`; Lemma TOP there
is `nuC_cap`).  The landing blocks below `L(k)` follow from `L(k) < ν_C` (`R2.land_C`).  The rest is the pair-free leaf
skWinIn. -/
theorem skWinSpec (S : InaccSeq.{0}) (k : ℕ) :
    ∃ O : Ordinal.{0} → Ordinal.{0}, (∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ →
      O μ = Ys.ysO S μ) ∧
    Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
  ⟨_, fun _ h => Yx.yxO_above h, (skWinAll S k).2.1⟩

/-- STATUS: PROVED (skWinAll = Yx.yxWins; round 130: by the induction on k; checked only after the merge)
SIZE: S
UPPER ∧ LOWER at every range restart of `W_k` from the relative block induction (`Ys.ysGood_all`, Lemma TOP
`Ys.ysTop_short` / given, Lemma RS with crossings `Ys.ysRs_all`), the pair fields from the caps below `L(k)`. -/
theorem skWinUL (S : InaccSeq.{0}) (k : ℕ) :
    ∀ l, Cd.CdRange S l → Wj.WjWin S k l → Cd.CdUpper S l ∧ Cd.CdLower S l := (skWinAll S k).2.2

/-- STATUS: REDUCED (skWinUL, skWinSpec, skWinRsIn, skWinCapV; round 129: was OPEN L — as strong as: ν_C is in no
window W_k, Wj.wjUV_ne_nuC; round 126: the cell transport is vacuous here, skWinNoBase; round 127: a window
induction allowing only the long ≤₁ of L(k) with short inner offsets is REFUTED, skWinShortRef; round 129: the
induction with nested long reaches is built, Ys.ysGood_all)
SIZE: L
(W_k, A-type) L(k) < υ_λ < L(k+1), offset ζ = η - (Ω_ω + P′·k) a copy of a region-(A) name. -/
theorem skWinA (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → SkOffA S k l →
    SkUV S l := by
  intro k l hr hw _
  exact ⟨(skWinUL S k l hr hw).1, (skWinUL S k l hr hw).2, skWinCapVAll S k l hr hw⟩

/-- STATUS: PROVED (Yf.yfNoBase_win; round 126, new)
SIZE: S
REFUTE FIRST for the cell transport in the windows: if `L(k) ≤₁ L(k+1)`, no restart index `λ₀` with
`L(k) ≤ ρ_{λ₀} < L(k+1)` carries the base data (a long `≤₁` from below crosses `υ_{λ₀+ω²}`). -/
theorem skWinNoBase (S : InaccSeq.{0}) (k : ℕ)
    (hx : le1 (Nc.ncL S (k : Ordinal.{0})) (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))) {l0 : Ordinal.{0}}
    (hl0 : IsRestartIdx l0) (h1 : Nc.ncL S (k : Ordinal.{0}) ≤ upsilon l0)
    (h2 : upsilon l0 < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (O : Ordinal.{0} → Ordinal.{0}) :
    ¬ SkBase O l0 := fun hb => Yf.yfNoBase_win S k hx hl0 h1 h2 O hb.1

/-- STATUS: PROVED (Yf.yfNoBase_top; round 126, new)
SIZE: S
the same in the top window under `L(ω) ≤₁ L(ω+1)`. -/
theorem skTopNoBase (S : InaccSeq.{0}) (hx : le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1))) {l0 : Ordinal.{0}}
    (hl0 : IsRestartIdx l0) (h1 : Nc.ncL S ω ≤ upsilon l0) (h2 : upsilon l0 < Nc.ncL S (ω + 1))
    (O : Ordinal.{0} → Ordinal.{0}) : ¬ SkBase O l0 := fun hb => Yf.yfNoBase_top S hx hl0 h1 h2 O hb.1

/-- STATUS: PROVED (Yi.yiWinShort_ref; round 127, new; checked only after the merge)
SIZE: S
REFUTE FIRST for the window induction with short inner offsets: under LOWER at the range restarts of `W_n`
(part of skWinA's conclusion), cofinally in `W_n` there are range restarts `μ` above `L(n)` with
`ρ_μ ≤₁ υ_{μ+ω²}`, no base data at `μ` and no relative block induction `Yf.YfSpec O λ₀ B` with `λ₀ < μ < B`. -/
theorem skWinShortRef (S : InaccSeq.{0}) (n : ℕ)
    (hL : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) → Cd.CdLower S μ) :
    ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧
      Nc.ncL S (n : Ordinal.{0}) < upsilon μ ∧ upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      le1 (upsilon μ) (upsilon (μ + ω * ω)) ∧
      (∀ O : Ordinal.{0} → Ordinal.{0}, ¬ ∀ η, ω * ω * η ≤ μ + ω * ω → Good O (ω * ω * η)) ∧
      (∀ (O : Ordinal.{0} → Ordinal.{0}) l0 B, Yf.YfSpec O l0 B → l0 < μ → μ < B → False) :=
  Yi.yiWinShort_ref n hL

/-- STATUS: PROVED (Yi.yiMShort_ref; round 127, new; checked only after the merge)
SIZE: S
the same cofinally below `L(0)`: under LOWER there, cofinally below `L(0)` there are range restarts that no
relative block induction covers (so the cells of skBhiAcell do not reach them). -/
theorem skMShortRef (S : InaccSeq.{0})
    (hL : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S 0 → Cd.CdLower S μ) :
    ∀ γ < Nc.ncL S 0, ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < Nc.ncL S 0 ∧
      (∀ (O : Ordinal.{0} → Ordinal.{0}) l0 B, Yf.YfSpec O l0 B → l0 < μ → μ < B → False) :=
  Yi.yiMShort_ref hL

/-- STATUS: PROVED (Yi.yiCross_of_upper; round 127, new; checked only after the merge)
SIZE: S
the corrected crossing clause `Yi.YiCross S a l` of a window induction follows when every crossing below `υ_l`
starts at a point `≤ a` or at `ρ_μ` with UPPER at `μ` (the restart part of the clause is exactly UPPER). -/
theorem skWinCross (S : InaccSeq.{0}) {a l : Ordinal.{0}}
    (h : ∀ c < upsilon l, ∀ g, upsilon l ≤ g → le1 c g →
      c ≤ a ∨ ∃ μ, IsRestartIdx μ ∧ c = upsilon μ ∧ Cd.CdUpper S μ) : Yi.YiCross S a l :=
  Yi.yiCross_of_upper h

/-- STATUS: PROVED (Ys.ysSpec_old; round 129, new; checked only after the merge)
SIZE: S
NON-VACUITY of the relative block specification: the repo's offsets `c*` satisfy `Ys.YsSpec` from `l₀ = ω²` up to
`Ξ_ω + ω²` (the base with TOP given, the others with the short input). -/
theorem skWinSpecOld : Ys.YsSpec off (ω * ω) (XiW + ω * ω) := Ys.ysSpec_old

/-- STATUS: PROVED (Ys.ysShortX_ref; round 129, new; checked only after the merge)
SIZE: S
REFUTE FIRST for the crossing bound: under LOWER and TOP in `W_n`, cofinally in `W_n` there are range restarts `μ`
such that at the restart `μ + ω²` no short input with a crossing bound `x₀ < ρ_μ` exists. -/
theorem skWinShortX (S : InaccSeq.{0}) (n : ℕ) (O : Ordinal.{0} → Ordinal.{0})
    (hL : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) → Cd.CdLower S μ)
    (hT : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) →
      ∀ g, upsilon (μ + ω + 1) + O μ < g → ¬ le1 (upsilon μ) g) :
    ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧
      Nc.ncL S (n : Ordinal.{0}) < upsilon μ ∧ upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      ∀ (m : ℕ) (k x0 : Ordinal.{0}), x0 < upsilon μ → k < upsilon (μ + ω * ω) →
        ¬ ∀ ν, IsRestartIdx ν → ν < μ + ω * ω → x0 < upsilon ν → O ν < tm m k (upsilon ν) :=
  Ys.ysShortX_ref (S := S) n O hL hT

/-- STATUS: PROVED (Ys.ysGood_step; round 129, new; checked only after the merge)
SIZE: M
THE WINDOW STEP: the relative block structure `(a, υ_l)` ⇒ `(a, υ_{l+ω²})` at a restart `l`, for a short offset and
for a long reach (chain start `δ_l + o`, crossing bound `a ≤ x₀ ≤ ρ_l`, closedness above `x₀`, chain data). -/
theorem skWinStep {a : Ordinal.{0}} {O : Ordinal.{0} → Ordinal.{0}} {l o x0 : Ordinal.{0}}
    (hl : IsRestartIdx l) (G : Ys.YsGood a O l) (hal : a ≤ upsilon l)
    (R : Ys.YsRstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)))
    (htop : ∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g)
    (ho : o < upsilon (l + ω + 1)) (hoO : o ≤ O l) (hax : a ≤ x0) (hxl : x0 ≤ upsilon l)
    (hT3 : ∀ c, x0 < c → c ≤ upsilon (l + ω + 1) + o → ∀ g, upsilon (l + ω + 1) + o < g → ¬ le1 c g)
    (hch : Ys.YsChainIn l o x0) (hcnt : l + ω * ω < Om1) : Ys.YsGood a O (l + ω * ω) :=
  Ys.ysGood_step hl G hal R htop ho hoO hax hxl hT3 hch.1 hch.2 hcnt

/-- STATUS: PROVED (Ys.ysGood_all; round 129, new; checked only after the merge)
SIZE: M
THE RELATIVE BLOCK INDUCTION from any restart `l₀`: `Ys.YsSpec O l₀ B` ⇒ `Ys.YsGood (ρ_{l₀}) O B`. -/
theorem skWinInd {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B) :
    Ys.YsGood (upsilon l0) O B := Ys.ysGood_B Sp

/-- STATUS: REDUCED (skWinUL, skWinCapV; round 129: was OPEN L — as strong as: ν_C is in no window W_k; the
relative block induction covers every range restart of the window, A-type and layer cells alike)
SIZE: L
(W_k, layer cells) offset ζ = η - b_k in the name layer c ≥ 1 (ζ < P′). -/
theorem skWinL (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l →
    Wj.WjWin S k l → Xh.XhNmLay c (Cd.cdEta S l - Wj.wjBase S k) → SkUV S l := by
  intro k _ _ _ l hr hw _
  exact ⟨(skWinUL S k l hr hw).1, (skWinUL S k l hr hw).2, skWinCapVAll S k l hr hw⟩

theorem skRegbCast (k : ℕ) : ((k + 1 : ℕ) : Ordinal.{0}) = (k : Ordinal.{0}) + 1 := by push_cast; rfl

/-- STATUS: REDUCED (Xh.xhWinB_red, skWinL; was OPEN L)
SIZE: L
(W_k, B-type) L(k) < υ_λ < L(k+1), offset past every copy of a region-(A) frontier (ζ < P′). -/
theorem skWinB (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → ¬ SkOffA S k l →
    SkUV S l := by
  intro k l hr hw hn
  refine Xh.xhWinB_red (S := S) (SkUV S) (k : Ordinal.{0}) (fun c hc1 hc2 l hr h1 h2 hL => ?_) l hr hw.1
    (skRegbCast k ▸ hw.2) hn
  exact skWinL S k c hc1 hc2 l hr ⟨h1, skRegbCast k ▸ h2⟩ hL

/-- STATUS: REDUCED (skTopAll; round 130, regw5: was OPEN L; statement unchanged; checked only after the merge)
SIZE: L
THE RELATIVE BLOCK SPECIFICATION ON THE TOP WINDOW `W_ω` (as skWinSpec, on `[ι(Ω_ω + P′·ω), ι(Ω_ω + P′·(ω+1)))`).
Round 130: the pair fields are dropped as in skWinSpec (`Yx.yxSpec_capsTop`); above `L(ω)` the name window of the
left end of the first non-standard pair lies in `W_ω` (`Yx.yxNu_gtTop`), so the only pair content left is the
leaf skTopLwNo2 at `L(ω)` itself; the landing blocks below `L(ω)` from `L(ω) < ν_C` (`R2.land_C`). -/
theorem skTopSpec (S : InaccSeq.{0}) :
    ∃ O : Ordinal.{0} → Ordinal.{0}, (∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ) ∧
    Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) :=
  ⟨_, fun _ h => Yx.yxO_above h, (skTopAll S).2.1⟩

/-- STATUS: PROVED (skTopAll = Yx.yxTopAll; round 130; checked only after the merge)
SIZE: S
UPPER ∧ LOWER at every range restart of `W_ω` from the relative block induction. -/
theorem skTopUL (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Wj.WjTop S l → Cd.CdUpper S l ∧ Cd.CdLower S l := (skTopAll S).2.2

/-- STATUS: PROVED (Ys.ysLwPair; round 129, new; checked only after the merge)
SIZE: S
the relative block specification on `W_ω` (any bound) gives `Rg.RgLwPair` (no `L(ω) <₂ d` with
`d ∈ (L(ω), L(ω+1))`, `Ys.ysNoPair_base`). -/
theorem skTopPair (S : InaccSeq.{0}) {O : Ordinal.{0} → Ordinal.{0}}
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)))) :
    Rg.RgLwPair S := Ys.ysLwPair Sp

/-- STATUS: PROVED (Ys.ysNu = Rg.rgNu with skTopPair; round 129, new; checked only after the merge)
SIZE: S
`L(ω+1) ≤ ν_C` from skTopSpec and the road's UPPER / CapV hypotheses. -/
theorem skTopNu (S : InaccSeq.{0})
    (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hVt : ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Cd.CdCapV S l) :
    Nc.ncL S (ω + 1) ≤ nuC := by
  obtain ⟨O, -, Sp⟩ := skTopSpec S
  exact Ys.ysNu Sp hU hV hVt

/-- STATUS: REDUCED (skTopUL, skTopCapV; round 129: was OPEN L — as strong as: ν_C ∉ (L(ω), L(ω+1)); with skWin*
and Sh.shNu this is L(ω+1) ≤ ν_C; round 126: the cell transport is vacuous here, skTopNoBase)
SIZE: L
(W_ω, A-type) L(ω) < υ_λ < L(ω+1), offset a copy of a region-(A) name (hVt lives here). -/
theorem skTopA (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → SkOffA S ω l → SkUV S l := by
  intro l hr hw _
  exact ⟨(skTopUL S l hr hw).1, (skTopUL S l hr hw).2, skTopCapVAll S l hr hw⟩

/-- STATUS: REDUCED (skTopUL, skTopCapV; round 129: was OPEN L — as strong as: ν_C ∉ (L(ω), L(ω+1)))
SIZE: L
(W_ω, layer cells) offset ζ = η - b_ω in the name layer c ≥ 1. -/
theorem skTopL (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Wj.WjTop S l →
    Xh.XhNmLay c (Cd.cdEta S l - Wj.wjBase S ω) → SkUV S l := by
  intro _ _ _ l hr hw _
  exact ⟨(skTopUL S l hr hw).1, (skTopUL S l hr hw).2, skTopCapVAll S l hr hw⟩

/-- STATUS: REDUCED (Xh.xhWinB_red, skTopL; was OPEN L)
SIZE: L
(W_ω, B-type). -/
theorem skTopB (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → ¬ SkOffA S ω l → SkUV S l := by
  intro l hr hw hn
  exact Xh.xhWinB_red (S := S) (SkUV S) ω (fun c hc1 hc2 l hr h1 h2 hL => skTopL S c hc1 hc2 l hr ⟨h1, h2⟩ hL)
    l hr hw.1 hw.2 hn

/-- STATUS: REDUCED (skWinA, skWinB)
SIZE: L
every window W_k. -/
theorem skWin (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → SkUV S l := by
  intro k l hr hw
  by_cases h : SkOffA S k l
  · exact skWinA S k l hr hw h
  · exact skWinB S k l hr hw h

/-- STATUS: REDUCED (skTopA, skTopB)
SIZE: L
the top window W_ω. -/
theorem skTop (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → SkUV S l := by
  intro l hr hw
  by_cases h : SkOffA S ω l
  · exact skTopA S l hr hw h
  · exact skTopB S l hr hw h

/-- STATUS: REDUCED (Wj.wjRegB_iff, skRegBlo, skRegBhi, skWin, skTop; was SUSPECT, mis-scoped)
SIZE: L
(B) as stated in round 115 = (B-lo) ∪ (B-hi) ∪ every window ∪ the top window (exactly, Wj.wjRegB_iff). -/
theorem skRegB (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l →
    (∀ B, B < Gc.gcG 1 → Bt.iota S (Gc.gcG B * ω) ≤ l) → Cd.cdExp (Cd.cdEta S l) < Om (1 + 1) → SkUV S l :=
  (Wj.wjRegB_iff (S := S) (SkUV S)).2 ⟨skRegBlo S, skRegBhi S, skWin S, skTop S⟩

/-- STATUS: REDUCED (skRegA, skRegB, skRegC)
SIZE: L
∀ range λ ≥ F_Ho: UPPER ∧ LOWER ∧ CapV (ENUM-REACH and CapV at every range restart above the frontier). -/
theorem skAbove (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → skFHo S ≤ l → SkUV S l := by
  intro l hr _
  by_cases hA : ∃ B, B < Gc.gcG 1 ∧ l < Bt.iota S (Gc.gcG B * ω)
  · exact skRegA S l hr hA
  push Not at hA
  rcases lt_or_ge (Cd.cdExp (Cd.cdEta S l)) (Om (1 + 1)) with he | he
  · exact skRegB S l hr hA he
  · exact skRegC S l hr he

/-- STATUS: REDUCED (skHypIff, skAbove)
SIZE: L
hUH ∧ hLH ∧ hVH ∧ hVt of Wd.wdRoadL (from ι(Γ(φ(Ω₁², G+1))·ω) on). -/
theorem skFront (S : InaccSeq.{0}) :
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l) ∧
    (∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l) ∧
    (∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) ∧
    (∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l →
      Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l) :=
  skHypIff S (skAbove S)

/-- STATUS: REDUCED (skFront)
SIZE: L
hUH of Wd.wdRoadL. -/
theorem skFrontU (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdUpper S l := (skFront S).1

/-- STATUS: REDUCED (skFront)
SIZE: L
hLH of Wd.wdRoadL. -/
theorem skFrontL (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdLower S l := (skFront S).2.1

/-- STATUS: REDUCED (skFront)
SIZE: L
hVH of Wd.wdRoadL. -/
theorem skFrontV (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l :=
  (skFront S).2.2.1

/-- STATUS: REDUCED (skFront)
SIZE: L
hVt of Wd.wdRoadL. -/
theorem skFrontVt (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → Nc.ncL S ω < upsilon l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → Cd.CdCapV S l :=
  (skFront S).2.2.2

/-- STATUS: REDUCED (skFrontU, skFrontL, skFrontV, skFrontVt, Wd.wdRoadL)
SIZE: L
integration check: Wd.wdRoadL applied to the four top nodes; ν_C = L(ω+1) etc. from hT, hF, h0, hn only. -/
theorem skRoad (S : InaccSeq.{0})
    (hT : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S)
    (hF : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdEQfar S)
    (h0 : ∀ l, IsRestartIdx l → Nc.ncL S 0 = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Te.teW (Nc.ncL S 0))))
    (hn : ∀ n : ℕ, ∀ l, IsRestartIdx l → Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = upsilon l →
      Vr.VrVisGen S l (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Te.teW (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S (k + 1)) (Nc.ncL S (ω + 1)) :=
  Wd.wdRoadL (skFrontU S) (skFrontL S) (skFrontV S) (skFrontVt S) hT hF h0 hn

end R2Skel.SkF
