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

/-- STATUS: PROVED (Xx.xxVD_loc, Xx.xxVD_enum, Xx.xxVD_capV; round 125, new node)
SIZE: M
the bound of every system over Γ(k) (k + 1 < ε₀) with gate below K is located: Λ⁺ = ι(Γ(B)·ω), P(Γ(B)·ω) < L(0),
through the reading system Xx.xxVRS D of the codes below B + ω (codes B + n read b(x) + n, gate γ; no hereditary
step). -/
theorem skLayLocVD (S : InaccSeq.{0}) {k : Ordinal.{0}} (hk : k + 1 < ε₀) (D : Xk.XkVD k) (hγ : D.γ < Td.tdK S) :
    Nm.Pv S (Gc.gcG D.B * ω) < Nc.ncL S 0 := (Xx.xxVD_loc D hk S hγ).2.2

/-- STATUS: PROVED (Xx.xxLayFront: Xx.XxGq, Xx.XxU, Xx.XxRS, Xx.XxLoc, Xx.XxStep; round 125, was OPEN L)
SIZE: L
THE FRONTIER LEMMA OVER Γ(k): for every system D : Xk.XkVD k with gate below K, UPPER ∧ LOWER ∧ CapV at every range
restart below ι(Γ(B_D)·ω) (k = 0: skLayFront0, reproved by Xx.xxLayFront_zero).  REFUTE FIRST (round 125): NO
EVIDENCE (now a theorem).  It is a statement about every system over Γ(k); for k ≥ 1 no such system is known yet
(skLaySys), so it does not locate region (A3) by itself. -/
theorem skLayFront (S : InaccSeq.{0}) : ∀ k, 1 ≤ k → k + 1 < ε₀ → Xk.XkLayFront S k :=
  fun _ _ hk => Xx.xxLayFront S hk

/-- STATUS: PROVED (Xx.xxLaySys_base; round 125, new node)
SIZE: S
DEPENDENCY of skLaySys: the systems over Γ(k) (k + 1 < ε₀) give UPPER ∧ LOWER ∧ CapV at every range restart below
ι(Γ(Γ(k))·ω); for k = 1 that is every range restart of region (A), the (A3) part above t₀ (skSysA3StepW) included. -/
theorem skLaySysBase (S : InaccSeq.{0}) : ∀ k, k + 1 < ε₀ → Xk.XkLaySys S k → ∀ l, Cd.CdRange S l →
    l < Bt.iota S (Gc.gcG (Gc.gcG k) * ω) → SkUV S l :=
  fun _ hk hS l hr hl => Xx.xxLaySys_base hk hS l hr hl

/-- STATUS: OPEN (round 123; round 125: REFUTE FIRST NO EVIDENCE, not proved)
SIZE: L
THE SYSTEMS OVER Γ(k): for every ℓ < Γ(k) a system D : Xk.XkVD k with φ(ℓ, Γ(k)+1) ≤ B_D and gate below K (k = 0:
skLaySys0).  Every such system carries the readings of every code below B_D ≥ Γ(k), and skLaySysBase: skLaySys 1
locates all of region (A) (the (A3) part above t₀, skSysA3StepW, included), so skLaySys k (k ≥ 1) comes after
region (A).  The system recursion it needs (round 125): Ws.wsSysAll over Xk.XkC k with Xk.XkCG (Ws.wsFam,
Ws.wsStep_all, Wo.woStep_om1, Wm.wmStep_fs, Wh.whSucc_at, Wh.whAt_base), the base system at φ(Ω₁, Γ(k)+1)
(Hg.hgU from Hf.hfGL) and the systems φ(α, Γ(k)+1), α < Ω₁ (the Gn … Hf chain), the bands Hn / Ho: about 126k lines
in 402 modules hard-wired to G; none of it is generic in the base atom. -/
theorem skLaySys (S : InaccSeq.{0}) : ∀ k, 1 ≤ k → k + 1 < ε₀ → Xk.XkLaySys S k := by
  sorry

/-- STATUS: OPEN (round 123)
SIZE: L
the old levels of the layers c with ε₀ ≤ c + 1 (base atoms Γ(c) that are not constants below ε₀). -/
theorem skLayLoBig (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ε₀ ≤ c + 1 → ∀ l, Cd.CdRange S l →
    Xh.XhPast S c l → (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  sorry

/-- STATUS: REDUCED (Xk.xkLayLo_of, skLaySys, skLayFront (PROVED round 125), skLayLoBig; round 123, was OPEN L;
round 125: for c + 1 < ε₀ only skLaySys is open, Xx.xxLayLo_of_sys)
SIZE: L
the layer c, OLD levels ℓ < Γ(c) over the base Γ(c) (system bounds φ(ℓ, Γ(c)+1); for c = 1 the levels of
(A1) ∪ (A2) ∪ (A3) again, now over Γ(1) read Γ_{x+2}; needs: a code interface like Ws.WsC with the base fields of
Γ(c) in place of Ws.WsCG and readings < gq (c+1) x, IMG below gq (c+1) ρ (skL1Img), the gated frontier lemma
(Gs.gsEnum / Gs.gsCapV) with the atom set {Γ(c') : c' ≤ c}, and the Ws.wsFam recursion over the levels). -/
theorem skLayLo (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Xh.XhPast S c l →
    (∃ ℓ, ℓ < Gc.gcG c ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) → SkUV S l := by
  intro c hc1 hc2 l hr hP hex
  by_cases hce : c + 1 < ε₀
  · exact Xk.xkLayLo_of (skLaySys S c hc1 hce) (skLayFront S c hc1 hce) l hr hex
  · exact skLayLoBig S c hc1 hc2 (not_lt.1 hce) l hr hP hex

/-- STATUS: OPEN
SIZE: L
the layer c, NEW levels Γ(c) ≤ ℓ < Γ(c+1) (levels containing the atom Γ(c); for c = 1 the analog of (A3) with the
atom Γ(1)). -/
theorem skLayHi (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Xh.XhPast S c l →
    (∀ ℓ, ℓ < Gc.gcG c → Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω) ≤ l) →
    (∃ ℓ, Gc.gcG c ≤ ℓ ∧ ℓ < Gc.gcG (c + 1) ∧ l < Bt.iota S (Gc.gcG (veblen ℓ (Gc.gcG c + 1)) * ω)) →
    SkUV S l := by
  sorry

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

/-- STATUS: OPEN
SIZE: L
(B-hi, A-type cell) base Ω₂·q, offset ζ of type (A): transport of region (A) along ζ ↦ Ω₂·q + ζ. -/
theorem skBhiA (S : InaccSeq.{0}) : ∀ l q ζ, Cd.CdRange S l → Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q →
    ζ ≠ 0 → ζ < Om (1 + 1) → Cd.cdEta S l < Om ω → Xh.XhNmA ζ → SkUV S l := by
  sorry

/-- STATUS: OPEN
SIZE: L
(B-hi, layer cells) base Ω₂·q, offset ζ in the name layer c ≥ 1: transport of skLay c along ζ ↦ Ω₂·q + ζ. -/
theorem skBhiL (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l q ζ, Cd.CdRange S l →
    Cd.cdEta S l = Om (1 + 1) * q + ζ → 1 ≤ q → ζ ≠ 0 → ζ < Om (1 + 1) → Cd.cdEta S l < Om ω →
    Xh.XhNmLay c ζ → SkUV S l := by
  sorry

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

/-- STATUS: OPEN (as strong as: ν_C is in no window W_k, Wj.wjUV_ne_nuC)
SIZE: L
(W_k, A-type) L(k) < υ_λ < L(k+1), offset ζ = η - (Ω_ω + P′·k) a copy of a region-(A) name. -/
theorem skWinA (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ l, Cd.CdRange S l → Wj.WjWin S k l → SkOffA S k l →
    SkUV S l := by
  sorry

/-- STATUS: OPEN (as strong as: ν_C is in no window W_k)
SIZE: L
(W_k, layer cells) offset ζ = η - b_k in the name layer c ≥ 1 (ζ < P′). -/
theorem skWinL (S : InaccSeq.{0}) : ∀ k : ℕ, ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l →
    Wj.WjWin S k l → Xh.XhNmLay c (Cd.cdEta S l - Wj.wjBase S k) → SkUV S l := by
  sorry

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

/-- STATUS: OPEN (as strong as: ν_C ∉ (L(ω), L(ω+1)); with skWin* and Sh.shNu this is L(ω+1) ≤ ν_C)
SIZE: L
(W_ω, A-type) L(ω) < υ_λ < L(ω+1), offset a copy of a region-(A) name (hVt lives here). -/
theorem skTopA (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Wj.WjTop S l → SkOffA S ω l → SkUV S l := by
  sorry

/-- STATUS: OPEN (as strong as: ν_C ∉ (L(ω), L(ω+1)))
SIZE: L
(W_ω, layer cells) offset ζ = η - b_ω in the name layer c ≥ 1. -/
theorem skTopL (S : InaccSeq.{0}) : ∀ c, 1 ≤ c → c < Om (1 + 1) → ∀ l, Cd.CdRange S l → Wj.WjTop S l →
    Xh.XhNmLay c (Cd.cdEta S l - Wj.wjBase S ω) → SkUV S l := by
  sorry

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

/-- STATUS: OPEN
SIZE: L
(C) = (C1): names with e(η_λ) ≥ Ω₂ (code π_η, ι(Ω₂) ≤ λ, Wj.wjC_props); all of (C) lies below L(0)
(Wj.wjExpHi_low).  Round 122: REFUTE FIRST, NO EVIDENCE (codes π_η > Γ_{Ω₁+ε₀}, Gc.gc_code_ge, outside every
frontier lemma, Gc.gcFr_code; no L(k) inside); unchanged. -/
theorem skLongPre (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l → Om (1 + 1) ≤ Cd.cdExp (Cd.cdEta S l) →
    upsilon l < Nc.ncL S 0 → SkUV S l := by
  sorry

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
