import Googology.Trans.PoR.InaccPsi.R2.WdRoad
import Googology.Trans.PoR.InaccPsi.R2.WbNoGo
import Googology.Trans.PoR.InaccPsi.R2.VxDyn
import Googology.Trans.PoR.InaccPsi.R2.VtDynTop
import Googology.Trans.PoR.InaccPsi.R2.RyNF
import Googology.Trans.PoR.InaccPsi.R2.RxLv
import Googology.Trans.PoR.InaccPsi.R2.RoW
import Googology.Trans.PoR.InaccPsi.R2.WgFam
import Googology.Trans.PoR.InaccPsi.R2.WgTh
import Googology.Trans.PoR.InaccPsi.R2.WlLow
import Googology.Trans.PoR.InaccPsi.R2.WrMid
import Googology.Trans.PoR.InaccPsi.R2.WvImg
import Googology.Trans.PoR.InaccPsi.R2.WzUp
import Googology.Trans.PoR.InaccPsi.R2.XdLaw1
import Googology.Trans.PoR.InaccPsi.R2.XiRef
import Googology.Trans.PoR.InaccPsi.R2.XmLim
import Googology.Trans.PoR.InaccPsi.R2.XqTop
import Googology.Trans.PoR.InaccPsi.R2.XsTop
import Googology.Trans.PoR.InaccPsi.R2.XvTop0
import Googology.Trans.PoR.InaccPsi.R2.YdMoveB
import Googology.Trans.PoR.InaccPsi.R2.YjTop
import Googology.Trans.PoR.InaccPsi.R2.YtTest
import Googology.Trans.PoR.InaccPsi.R2.YtSubB
import Googology.Trans.PoR.InaccPsi.R2.YyTest
import Googology.Trans.PoR.InaccPsi.R2.YyOm2B
import Googology.Trans.PoR.InaccPsi.R2.ZdTest
import Googology.Trans.PoR.InaccPsi.R2.ZdChainR
import Googology.Trans.PoR.InaccPsi.R2.ZiTop
import Googology.Trans.PoR.InaccPsi.R2.ZpWall
import Googology.Trans.PoR.InaccPsi.R2Skel.SkE

/-!
# Skeleton, part "readings": the reading move `hν → Wd.WdThLow S`

Top node `skRead S : L(ω+1) ≤ ν_C → Wd.WdThLow S` (the hypothesis `hT` of `Wd.wdRoadL`).

`Θ_λ = gxTh ρ_λ (ldAtR λ)`, `m_λ = cdCode`, `θ = ψ_{Ω₂}(Ω_ω)`, `A = A_{η_λ} = Ω_ω + θ·η_λ`, `θ⁺ = Lj.ljThP`,
`M_W = Rn.rnMW = ψ_{Ω₂}(Ω_ω+Ω₂)`, `Y₃ = Ug.ugY`, `Γ = ggGam` (least strongly critical above `Ω₁`),
`hν := L(ω+1) ≤ ν_C`, "window" = the hypotheses of `Wd.WdThLow` up to `ρ_λ < m_λ`.

Every node's docstring starts with STATUS, SIZE, one line of math.  `sorry` only as the whole proof of an OPEN leaf
or of a REFUTED node kept for the record.

Round 110 (leaf read40): the refuted one-image top `skTopDyn` is replaced by the family law `skTopFam`
(`Wg.WgTopFamAll`: one image `X̂_e(β)` per exponent `e` and base `β`); `skWallBase`, `skWallStep` take it as their
hypothesis; `skThVal` is REDUCED to its lower half `skThLow` (the upper half `skThUp` is `Wg.wgTheta_le`).
Round 111 (leaf read41): `skThLow` is PROVED (`Wl.wlThLow`: the lift of `Rx.rxBlkTh` taken at the base `Ω_{k+2}`
for the offsets `ζ < ψ_{Ω₂}(Ω_{k+1})`, `Wl.wlBlk0`), so `skThVal`, `skBlkLaw`, `skWallTh` are PROVED (all their
children are proved).
Round 112 (leaf read42): `Wd.WdAtWall` is stated only at windows with `F_W ≤ m_λ < θ⁺`, but `Rn.RnThMoveM` asks
windows with `m_λ ≥ θ⁺`, so `skMidAssemble` cannot use its wall hypothesis (SUSPECT, REPLACED).  The wall is
restated without code hypotheses (`Wr.WrWallCF`; `WallBelow` lost its code hypotheses), `skWallCF` gives it, `skWall`
follows (`Wr.wrWall_of_cf`), and `skMidCF` (`Wr.wrMid`: `WrWallCF ⇒ RnThMoveM`) is PROVED.  This file imports the
new module `R2.WrMid`: it can be checked only after the merge.
Round 113 (leaf read43): REFUTE FIRST on the images of `skTopFam`.  Every image of the law at the base `0` has
`Ω^{X̂} < θ` (`Wv.wvImg_lt_th`, from `Θ_λ(θ) = ψ₁(A+θ)`), so the naive intrinsic image `X̂ = T(Y(0)) = Y_{k+2}` is
REFUTED at every `k ≥ 1` (`Wv.wvNoT`; `Wb.wbNoY_ge1` gave only some `k`).  New candidate `X̂⁰_k(β) = ψ₂(T β + Ω_{k+2})`
(`Wv.wvX0`; equal to `T(ψ₃(β+Ω₃))` at `k = 0`) passes every Lean test (`skX0Tests`); its law at every base is the new
OPEN node `skX0Law`.  This file imports the new module `R2.WvImg`: it can be checked only after the merge.
Round 114 (leaf read44): REFUTE FIRST on the candidate at `k = 1, β = 0` and `k = 0, β = Ω₃`: NO EVIDENCE (new lower tests
`Wz.wzImg1_gt`: every image at `Ω₄`, base `0`, has `X̂ < Ω^Z` with `X̂ = ψ₂(Ω₂·2)`; `Wz.wzImg0_ge`: every image at `Ω₃`,
base `Ω₃`, has `X̂ ≤ Ω^Z`; the candidates `ψ₂(Ω₃)`, `ψ₂(Ω₂·2)` pass).  The lift of `Rx.rxBlkTh` at the base `Ω₃` for
the offsets `ζ < ψ₂(Ω₂·2)` (`Wz.wzLift`; `ζ < ψ₂(Ω₂ + ζ)`, `Wz.wzLtPsi`; level bound `L = Ω₂ + ζ`, `Wz.wzL_memL`)
gives the lower half of the law at `k = 0, β = Ω₃` (`skX0LowOm3`), and the law there is equivalent to its upper half
(`skX0Om3Iff`).  New OPEN node `skUpU` (`Wz.WzUpU`: `Θ(ψ₂(a)) ≤ ψ₁(A + 1 + ψ₂(T a))` for normal `a ∈ D`; tight at
`a = Ω₃`, `Ω₃·2`, `θ`); `skX0Om3` (the law at `k = 0, β = Ω₃`) is REDUCED to it.  This file imports the new module
`R2.WzUp`: it can be checked only after the merge.
Round 121 (leaf read45): `skUpU` is PROVED (`Xd.xdUpU`: one induction on the atom, with the transfer `Xd.xdT_cl` /
`Xd.xdTr`: `x ∈ Cl(a, ψ₂(a)) ⇒ T x ∈ Cl(T a, ψ₂(T a))`), so `skX0Om3` is PROVED.  REFUTE FIRST on `skX0Law`: REFUTED
(`Xd.xdX0Law_false`): `T = Vb.vbT` is `0` off its domain, so at `β = Ω_ω` (allowed by `Ro.RoBaseE` at the restart of
`m*`) the image is `Y₂`, while the lift at the base `Ω_ω` (`Xd.xdLift`) gives readings above `ψ₁(A + θ + Y₂)` below
`ψ₂(Ω_ω + Ω₃)`.  Replaced by `skX0LawDK` (the same law for bases `β ∈ D`, OPEN), with the parts `skX0LawD` (k = 0, every
`β ∈ D`, PROVED, `Xd.xdLaw0D`) and `skX0Law1` (k = 1, β = 0, PROVED, `Xd.xdLaw1`).  This file imports the new module
`R2.XdLaw1`: it can be checked only after the merge.
Round 122 (leaf read46): `skX0LawDK` is PROVED (`Xi.xiLawDK`: the lower half by one induction on `k`, `Xi.xiLow`; the
step uses the law at `k` on the bases `β + u_n`, `u_{n+1} = ψ_{Ω_{k+4}}(β + u_n)`, `T u_n = z_n`,
`z_{n+1} = ψ_{Ω_{k+3}}(T β + z_n)`, and the base-relative cofinality `ψ₂(b + Ω_{s+1}) ≤ sup_n ψ₂(b + z_n)`,
`Xi.xiCof`).  REFUTE FIRST on `skTopFam`: REFUTED (`Xi.xiTopFam_false`): at `k = 0`, `β = 0`, `e = ω` the reading is
`Θ(ψ₂(W^{Ω₃+ω})) = ψ₁(A + P*)`, `P* = ψ₂(Ω^{Ω₂+ω})` strongly critical (`Xi.xiReadOm`), and no `ψ₁(A + 1 + Ω^{X̂+ω})`
equals it (`Xi.xiShape`, `Xi.xiFamOm_false`).  Replaced by `skTopUp` (`Xi.XiTopUp`: the `Wz.WzUpU` bound is attained at
every top atom `ψ₂(β + W^{Ω_{k+3}+e})`, `β ∈ D`; OPEN, proved at `e = 0` and at `(k, e, β) = (0, ω, 0)`);
`skWallBase`, `skWallStep` now take `Xi.XiTopUp` (with the refuted `Wg.WgTopFamAll` they were vacuous).  This file
imports the new module `R2.XiRef`: it can be checked only after the merge.
Round 123 (leaf read47): `skTopUp` is PROVED (`Xm.xmTopUp`): one induction on the code `e`; successors by the plateau
lemma `skPlat` (`Xm.xmPlat`: `ψ₁(B + ψ₂(b + ω^m·Ω₁)) ≤ sup_n x_n`, `x_{n+1} = ψ₁(B + ψ₂(b + ω^m·x_n))`) over the
sub-bases `β + W^{X+e}·u_n` (`skTopUpSucc`), limits by continuity over the codes `e' < e` (`skTopUpLim`, generalizing
`Xi.xiReadOm`).  REFUTE FIRST at `e = 1` and `e = ω + 1` (`k = 0`, `β = 0`): both hold (`skTopUpTests`).
`skWallBase`, `skWallStep` keep their statements (hypothesis `Xi.XiTopUp`, now a theorem) and stay OPEN.  This file
imports the new module `R2.XmLim`: it can be checked only after the merge.
Round 124 (leaf read48): REFUTE FIRST on the `ψ₂(T a)` form off the top atoms: REFUTED at `a = Ω₃ + 1`
(`skWallRefNonTop`, `Xq.xqRef_wit`: `Θ(ψ₂(Ω₃ + 1)) = ψ₁(A + 1 + ψ₂(Ω₂) + 1) < ψ₁(A + 1 + ψ₂(T(Ω₃ + 1)))`).  New PROVED
nodes for the missing pieces of `skWallBase` / `skWallStep`: (1) the block law above every top atom with the proved
top value (`skTopBlk`, `Xq.xqTopBlk`: `Θ(ψ₂(t + c)) = ψ₁(A + 1 + ψ₂(T t) + Θ c)` for codes `c < ψ₂(t + Ω₂)`, and
`Θ(ψ₂(t + Ω₂)) = ψ₁(A + 1 + ψ₂(T t) + Ω₁)`); (2) the move of `T` at every wall atom from the moves of the codes below
it (`skTMove`, `Xq.xqTMove`: `T_{λ'}(B_n x) = B_n(T_λ x)` for `x ∈ D ∩ Cl(a, ψ₂ a)`), and `B_n` through `σ`
(`skSigMove`, `Xq.xqSigMove`); (3) every top atom moves once its base data move (`skTopMove`, `Xq.xqTopMove`).
`skWallBase`, `skWallStep` keep their statements and stay OPEN.  This file imports the new module `R2.XqTop`: it can
be checked only after the merge.
Round 124 (leaf far1): the readings past `M_W` on `[M_W, K_ω)` (`K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + Ω₂·K_j)`,
`K_1 = M_W`): `Θ(ψ_{Ω₂}(Ω_ω + Ω₂·γ)) = ψ_{Ω₁}(A + θ + Ω₁·Θ γ)` (`skXsBase` = `Xs.xsBase`, one induction on the code `γ`)
and the blocks above them (`skXsBlk` = `Xs.xsBlk`), and their move (`skXsMove` = `Xs.xsMove`: every window code
`θ⁺ ≤ m_λ < K_{J+1}` moves, given the code-free wall).  `skThFar` (FarLowMove) is REDUCED to `skWallCF` and the new
shared leaf `skTopK` (`Xs.XsTopK`: the move at every window code `≥ K_ω`; shared with SkE).  REFUTE FIRST:
the level-down reading `ψ_{Ω₁}(A + θ + T d)` is REFUTED at `d = Ω_{k+1}`, `k ≥ 2` (`Xs.xsRefK`, record in SkE
`skXsRef`).  This file imports the new module `R2.XsTop`: it can be checked only after the merge.
Round 125 (leaf read49): REFUTE FIRST on the BASE-DATA MOVE and on `skTopK`: NO EVIDENCE (no Lean refutation; the
base-data move is a THEOREM at the base `0` for the exponents `e < ψ₂(Ω_{k+3})`; `skTopK` follows from the target,
`Xs.xsTopK_of_target`).  New PROVED nodes: `skBaseMove0` (`Xv.xvBaseMove0`: at every window, under the moves of the
codes below `ψ₂(W^{X+e})`, a code `e < ψ₂(X)` of `λ` gives the top base `(B_n e, 0)` of `λ'` and
`B_n(W^{X+e}) = W^{X+B_n e}`; the own clause holds at EVERY restart below `ψ₂(X)`, `Xv.xvBase0`) and `skTop0Move`
(`Xv.xvTop0Move`: every such top atom `ψ₂(W^{X+e})` moves; the bound `Θ(ψ₂ t) < c_{n+1}` of `skTopMove` is now
derived, `Lj.ljTheta_lt_delta`).  `skWallBase`, `skWallStep` keep their statements and stay OPEN.  This file imports
the new module `R2.XvTop0`: it can be checked only after the merge.
Round 126 (leaf read50): REFUTE FIRST on the INVERSE CORRESPONDENCE (every code of `λ'` below `B_n(ψ₂ t)` is `B_n` of a
code of `λ`): REFUTED (`skInvRef`, `Yd.ydInvRef`): at every window and level `k` the atom `F = ψ₂(Ω_{k+3} + c_n)` of
`λ'` lies just above `B_n(ψ₂(W^X)) = ψ₂(X)` (below `ψ₂(W^{X+1})`) and is `B_n y` for NO `y ∈ MvD`.  It is not needed:
the PLATEAU at `Ω₂` (`skPlatB`, `Yd.ydTopB_eq`: `ψ₂(β + W^{X+Ω₂}) = sup_m e_m`, `e_{m+1} = ψ₂(β + W^{X+e_m})`, for every
normal base `β`) gives the own clause of `Ro.RoBaseE` for EVERY ordinal below `ψ₂(β + W^{X+Ω₂})`, and `B_n` maps the
iterates over `β` to those over `B_n β` (`skOwnMove`, `Yd.ydOwnMoveB`).  New PROVED nodes: `skBaseMoveAll0`
(`Yd.ydBaseMove`: the base-data move for EVERY top base `(e, 0)`; `RoBaseE λ X e 0 ⇔ e < ψ₂(W^{X+Ω₂})`,
`Yd.ydBaseE_iff`), `skTopMoveAll0` (`Yd.ydTopMove`: every top atom over the base `0` moves).  New OPEN node
`skBaseFactsB` (M): the two base facts at `λ'` for `β ≠ 0` (`W^{X+B_n e} ∣ B_n β`, `B_n β ∈ D_{λ'}`); new REDUCED node
`skTopMoveAllB` (`Yd.ydTopMoveB` + `skBaseFactsB`: every top atom `ψ₂(β + W^{X+e})` moves).  `skWallBase`,
`skWallStep` keep their statements and stay OPEN (they do not yet use `skTopMoveAllB`, so the road count is
unchanged).  This file imports the new module `R2.YdMoveB`: it can be checked only after the merge.
Round 127 (leaf read51): REFUTE FIRST on `skBaseFactsB` at `β = Ω₃·2` and `β = Ω₃ + Ω₃·ω = Ω₃·ω`: NO EVIDENCE (both are
top bases `(0, β)` in `D` at every `λ`, `Yj.yjNonvac`, `Yj.yjNonvacW`); then `skBaseFactsB` PROVED (`Yj.yjBaseFacts`:
the divisibility moves by one induction on the Cantor normal form of `β`, `Yj.yjDvd`; `B_n β = κ_{λ'}(B_n(T_λ β))` gives
`B_n β ∈ D_{λ'}`, `Yj.yjD`), so `skTopMoveAllB` is PROVED: EVERY top atom `ψ₂(β + W^{Ω_{k+3}+e})` moves under the
premise of WallBelow at it, with no further hypothesis.  New PROVED nodes: `skBlkMove` (`Yj.yjBlkMove`: above every base
with a law at both ends, `Yj.YjBase`, every atom of the block `ψ₂(a + c)`, `c < F^a`, moves), `skBlkNext`
(`Yj.yjBlkNext`: `F^a` moves and `a + Ω₂` is again such a base), `skTopBase` (`Yj.yjTopBase`: every top atom is such
a base), `skTopBlkFin` (`Yj.yjTopBlk`: every atom `ψ₂(t + Ω₂·m + c)`, `m < ω`, above every top atom `t` moves).
`skWallBase`, `skWallStep` keep their statements and stay OPEN (still missing: the bases `t + Ω₂·γ` at `γ ≥ ω` and the
larger offsets `δ < W^X` above `t`, the sub-bases `β + W^{X+e}·γ`, the ψ₃-atoms in the exponents, the assembly).  This
file imports the new module `R2.YjTop`: it can be checked only after the merge.
Round 129 (leaf read53): REFUTE FIRST on (a) at `γ = ω`, `γ = ω + 1` and (b) at `δ = Ω₂²` over `t = W^{Ω₃}`
(`β = 0`, `k = 0`): NO EVIDENCE; the three laws hold there (`skRefTests`: `Yt.ytTestOm`, `Yt.ytTestSq`).  Then PROVED,
generic in `k`: above EVERY top atom `t = β + W^{Ω_{k+3}+e}` every atom `ψ₂(t) ≤ s < ψ₂(t + Y₃)` moves
(`skTopMoveY`, `Yt.ytTopMoveY`; this covers (a), the bases `t + Ω₂·γ` (`Yt.ytLaw`, `Yt.ytBaseG`), and (b) for every
offset `δ < Y₃`: `Le.LeOwnH` / `Rw.RwOwn` own arguments over the base `t`, `Yt.ytRep`, `Yt.ytRepU`, read by the
base-generic `Le.leOwnRead` / `Uu.uuOwnRead` and moved by `Le.leDigMoveE` / `Uu.uuDigMove`); at EVERY sub-base
`a = β + W^{X+e}·γ` with a limit code `γ` the law `Θ(ψ₂ a) = ψ₁(A + 1 + ψ₂(T a))` holds (`skSubLawLim`,
`Yt.ytSubLaw`), `a` is a base with a law at both ends (`skSubBaseLim`, `Yt.ytSubBase`), and every atom
`ψ₂(a) ≤ s < ψ₂(a + Y₃)` moves (`skSubMoveY`, `Yt.ytSubMove`).  New OPEN node `skPsi3Off` (L): the offsets
`Y₃ ≤ δ < Ω₃` (the ψ₃-atoms) above every base with a law at both ends.  `skWallBase`, `skWallStep` keep their
statements and stay OPEN (docstrings list the exact remaining pieces).  This file imports the new modules `R2.YtTest`,
`R2.YtSubB`: it can be checked only after the merge.
Round 130 (leaf read54): REFUTE FIRST on skPsi3Off at `δ = Y₃`, `δ = Y₃·2` and `δ = ψ₃(0)·2` over `t = W^{Ω₃} = Ω₃`, and on
the top law (2') at the first non-code exponent `E = Ω₂` (`β = 0`): NO EVIDENCE; all hold (`skRefTests130`:
`Yy.yyTestY3`, `Yy.yyTestY3two`, `Yy.yyTestG3`, `Yy.yyTestOm2`, `Yy.yyTestOm2_wit`; `ψ₃(0)·2 < Y₃`, `Yy.yyG3_two_lt`, so
that point is inside the old region of `skTopMoveY`).  Then PROVED, generic in `k`: (2') at `E = Ω₂` for every base:
`Θ(ψ₂(β + W^{X+Ω₂})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+Ω₂})))` (`skTopLawOm2`, `Yy.yyLawOm2`, via the plateau in the exponent
`skPlatExp`, `Yy.yyPlat`), the atom moves (`Yy.yyTopMoveOm2`), it is a base with a law at both ends and every atom of
`[ψ₂ t, ψ₂(t + W^{Y₃+1}))` above it moves (`skTopMoveOm2Y`, `Yy.yyTopBaseOm2`, `Yy.yyTopMoveOm2Y`); (1') skPsi3Off is
REDUCED: for bases `a < Ω₃` it holds (the only such base is `0`, the region is empty: `skPsi3OffLow`,
`Yy.yyPsi3OffLow`); for `a ≥ Ω₃` the new OPEN leaf `skPsi3OffHi`, of which the part `s < ψ₂(a + W^{Y₃+1})` is PROVED
when `W^{Y₃+1} ∣ a`, `W^{Y₃+1} ∣ B_n a` (`skY3MoveW`, `Yy.yyY3MoveW`: the bases `a + Y₃·γ`, `γ < T^a`, are bases with
a law at both ends, `Yy.yyBaseY3G`, from the base-relative shift `(Y₃, Y₂)` of `Vq`), in particular above every top
atom (`skTopMoveY3W`, `Yy.yyTopMoveY3W`, supersedes `skTopMoveY`).  `skWallBase`, `skWallStep` keep their statements
and stay OPEN.  This file imports the new modules `R2.YyTest`, `R2.YyOm2B`: it can be checked only after the merge.
Round 131 (leaf read55): REFUTE FIRST on (a) at `δ = W^{Y₃+1}·2` over the base `a = Ω₃ + Y₃` (`Y₃ ∣ a`, `W^{Y₃+1} ∤ a`)
and on (b) at `E = Ω₂ + 1` (`β = 0`, `k = 0`): NO EVIDENCE; both hold (`skRefTests131`: `Zd.zdTestOm2p1`,
`Zd.zdTestPsi3W2`; `a + δ = Ω₃ + W^{Y₃+1}·2`, an atom above the top atom `Ω₃`).  Then PROVED, generic in `k`:
(b) the top law at EVERY exponent `X_ξ + e = Ω_{k+3} + Ω₂·ξ + e`, `ξ < ε₀`, `e` a code (`skTopLawChain`, `Zd.zdChain`:
`Xm.xmSucc` / `Xm.xmLim` / `Yy.yyLawOm2` written once for any shift in every closure, `Zd.zdSucc`, `Zd.zdLim`,
`Zd.zdLawW`, and the limit of the shifts `Zd.zdLimSh`), the move and the both-ends base data of every such top atom
(`skTopMoveChain`, `skTopBaseChain`: `Zd.zdTopMove`, `Zd.zdTopBase`, the Yd/Yj base-data move generic in the shift);
(a) the ψ₃-offsets below `W^{Y₃+Ω₂·ε₀}` above every base `a ≥ Ω₃` with a law at both ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`
(`skPsi3OffE0`, `Zd.zdPsi3OffE0`: the plateau with membership above the base, `Zd.zdOwnBr_iff`; the sub-bases
`a + W^{X+e}·γ` of every relative shift `X` of `Zd.ZdRS`, `Zd.zdBaseXE`; the induction on the exponent `Zd.zdXUp`;
the chain of relative shifts `(Y₃ + Ω₂·ξ, Y₂ + Ω₁·ξ)`, `ξ < ε₀`, `Zd.zdRS_chain`, `Zd.zdBot_chain`), in particular
above every top atom of `Ω_{k+3}` and of every `X_ξ` (`skTopMoveY3E0`, `skTopMoveChainY3E0`).  New REDUCED node
`skPsi3OffD` (the ψ₃-offsets `[ψ₂(a), ψ₂(a + Ω₃))` over `Ω₃`-divisible bases, the form the assembly needs), new OPEN leaf
`skPsi3OffRest` (the offsets `W^{Y₃+Ω₂·ε₀} ≤ δ < Ω₃`).  `skWallBase`, `skWallStep` keep their statements and stay OPEN.
This file imports the new modules `R2.ZdTest`, `R2.ZdChainR`: it can be checked only after the merge.
Round 133 (leaf read57): THE WALL ASSEMBLY.  REFUTE FIRST on the assembly: NOT REFUTED, it is PROVED that every atom
`ψ₂(Y₃) ≤ s < θ` of `λ` is `ψ₂(d)` with `d` normal in `D_λ` and `d = b + δ`, `b = Ω₃·(d/Ω₃)` normal, in `D_λ`,
`Ω₃ ∣ b`, `Ω₃ ≤ b`, `δ < Ω₃`, `ψ₂ b ≤ s < ψ₂(b + Ω₃)` (`skDecomp`, `Zp.zpDecomp`; the prefix of a normal argument is
normal, `Zp.zpPre_norm`, by a gap argument on the closures); the test points `ψ₂(Ω₃·2 + Ω₃)` (`b = Ω₃·3`, `δ = 0`)
and `ψ₂(W^{Ω₃+1} + Y₃·2)` (`b = Ω₃·Ω₂`, `δ = Y₃·2`) (`skRefTests133`).  Every such `b` is a base with a law at both
ends (`Zp.zpYjBase`: the base data move for EVERY normal `b ∈ D`, `Zp.zpBaseD`, `Zp.zpDvd3`) once the top law holds
at `b` and at `B_n b`.  ASSEMBLY: `skWallTh` (the wall below `θ`) ⇐ `skTopLawAll` (NEW OPEN leaf: the top law
`Θ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T b))` at every normal `Ω₃`-divisible `b ∈ D`, `b ≥ Ω₃`, one restart at a time) ∧
`skPsi3OffD` (REDUCED to `skPsi3OffRest2`); so `skWallBase`, `skWallStep` are REDUCED (statements unchanged) and the
SkR road leaves are `skTopLawAll`, `skPsi3OffRest2`.  Non-vacuity: `ZpPsi3OffAll` follows from the wall itself
(`Zp.zpOff_of_wall`), `ZpTopLawAll` holds at every top atom with a code exponent (`Zp.zpLaw_top`, `Xm.xmTopUp`) and
its premises are met at every restart (`Zp.zpLaw_wit`).  This file imports the new module `R2.ZpWall`: it can be
checked only after the merge.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2Skel.SkR

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Gg

/-! ## Statement names (hypothesis shapes only) -/

/-- The reading move at the window codes with `e(η_λ) ≤ Γ` and `Θ_λ(m_λ) < δ_λ·ω`. -/
def LowExpMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    cdExp (cdEta S l) ≤ ggGam → cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The reading move at the window codes with `e(η_λ) > Γ` and `m_λ < θ⁺`. -/
def MidMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    ggGam < cdExp (cdEta S l) → cdCode S l < Lj.ljThP S →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- The reading move at the window codes `m_λ > M_W` read below `δ_λ·ω`. -/
def FarLowMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Rn.rnMW S < cdCode S l → cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- `Wr.WrWallCF` (the wall with no code hypothesis) with the atom bound `s < b` in place of `s ≤ θ`
(round 112: the code hypotheses `ρ_λ < m_λ`, `F_W ≤ m_λ < θ⁺` are dropped). -/
def WallBelow (S : InaccSeq.{0}) (b : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s → s < b →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- `Wd.WdAtWall` at the single atom `s = θ`. -/
def WallAtTheta (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    Le.leFWW S ≤ cdCode S l → cdCode S l < Lj.ljThP S →
    ConjT.th S ∈ ldAtR S l →
      MvD S (ConjT.th S) ∧ Bc.bcB S n (ConjT.th S) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (ConjT.th S)) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (ConjT.th S))

/-- The level bound `ψ_{Ω₂}(Ω_{k+4})`. -/
noncomputable def lev (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} :=
  S.psi (Om ((k + 4 : ℕ) : Ordinal.{0})) (Om (1 + 1))

/-- The dynamic tops at `X = Ω_{k+3}` over every base `β ≥ 0`, one image `X̂(β)` per sub-base. -/
def TopDynAll (S : InaccSeq.{0}) : Prop :=
  ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
    ∃ Xh : Ordinal.{0} → Ordinal.{0}, ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
      Vt.VtTopDyn S l 0 (Om ((k + 3 : ℕ) : Ordinal.{0})) Xh e

/-- The block law at the base `Ω_ω` at every restart where `θ` is an atom. -/
def BlkLaw (S : InaccSeq.{0}) : Prop :=
  ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
    A ∈ S.CSet A (S.psi A (Om 1)) → A = ConjT.Aη S (cdEta S l) → ConjT.th S ∈ ldAtR S l →
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < Rn.rnMW S → Om ω + c < A →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + c) (Om (1 + 1))) =
        S.psi (A + ConjT.th S + gxTh (upsilon l) (ldAtR S l) c) (Om 1)

/-! ## Leaves and reductions -/

/-- STATUS: PROVED (Mw.mwEQlong_gam, Mx.mxEQ_gam, Wd.wdk_move, Cd.cdk_inj)
SIZE: S
`e(η_λ) ≤ Γ ∧ Θ_λ(m_λ) < δ_λ·ω ⇒ B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` (EQ there is unconditional; `k_{λ'}` injective). -/
theorem skLowExp (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → LowExpMove S := by
  intro hν n l l' hR h1 hr hl' hB hm he hw
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hE : Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) := by
    rcases he.lt_or_eq with he | he
    · exact Mw.mwEQlong_gam hν hR h1 hr hl' hB hm he
    · exact mxEQ_gam hν hR h1 hr hl' hB he
  rw [← Wd.wdk_move hν hR.1 hl' h1 hδr hB hw] at hE
  exact (cdk_inj l').1 hE

/-- STATUS: PROVED (Wd.wdAtMove26_of_wall, Wa.waLjAt_of_ux, Lj.ljLeThMoveU_of_at, Le.leThMoveT_of_U,
Le.leThMoveS_of_T, Ld.ldThMoveR_of_S, Ld.ldThMoveQ_of_R, Ld.ldThMoveW_of_Q, Mx.mxThMove_of_W, Lj.ljThMoveQ_of_at)
SIZE: S
`WdAtWall ⇒ ∀ window λ, Γ < e(η_λ), m_λ < θ⁺ : B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})`. -/
theorem skBelowThP (S : InaccSeq.{0}) : Wd.WdAtWall S → MidMove S := by
  intro h n l l' hR h1 hr hl' hB hm he hP
  have hat : Lj.LjAtMove S := Wa.waLjAt_of_ux (Wd.wdAtMove26_of_wall h)
  have hRm : LdThMoveR S :=
    ldThMoveR_of_S (Le.leThMoveS_of_T (Le.leThMoveT_of_U (Lj.ljLeThMoveU_of_at hat)))
  have hmv : MxThMove S := mxThMove_of_W (ldThMoveW_of_Q (ldThMoveQ_of_R hRm))
  by_cases hθ : cdCode S l ≤ ConjT.th S
  · exact hmv n l l' hR h1 hr hl' hB hm he hθ
  · by_cases hw : cdCode S l ≤ ConjT.th S * ω
    · exact hRm n l l' hR h1 hr hl' hB hm (ldFw_lt_th.trans (not_le.1 hθ)).le hw
    · exact Lj.ljThMoveQ_of_at hat n l l' hR h1 hr hl' hB hm (not_le.1 hw) hP

/-- STATUS: PROVED (Ry.ryTh_nf, Rx.rxOmW_nat, psi_mono, CSet_mono, psi_lt_psi_of_mem)
SIZE: S
`∀ b, ψ₂(b) < θ ⇒ ∃ k < ω, ψ₂(b) < ψ₂(Ω_{k+4})`. -/
theorem skThCof (S : InaccSeq.{0}) :
    ∀ b, S.psi b (Om (1 + 1)) < ConjT.th S → ∃ k : ℕ, S.psi b (Om (1 + 1)) < lev S k := by
  intro b hb
  obtain ⟨d, hdW, hdeq, hdown, -⟩ := Ry.ryTh_nf hb
  obtain ⟨k, hk⟩ := Rx.rxOmW_nat hdW
  refine ⟨k, ?_⟩
  have hlt : d < Om ((k + 4 : ℕ) : Ordinal.{0}) :=
    hk.trans (Om_lt_Om.2 (by exact_mod_cast (show k < k + 4 by omega)))
  have hle := psi_mono (S := S) (InR_Om_succ 1) hlt.le
  have hmem : d ∈ S.CSet (Om ((k + 4 : ℕ) : Ordinal.{0}))
      (S.psi (Om ((k + 4 : ℕ) : Ordinal.{0})) (Om (1 + 1))) := hle.2 hdown
  rw [← hdeq]
  exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt hmem

/-- STATUS: REFUTED (SkRX.skrxTopDynAll_false: one image X̂ for e = 0 and e = 1 at k = 0 is impossible, SkRX.skrxDyn01);
REPLACED by skTopFam (no node uses it any more)
SIZE: M
`∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ : ∃ X̂ : base ↦ image, ∀ e < Ω₂ in H_λ, ∀ β ≥ 0 :
Θ(ψ₂(β + Ω₂^{Ω_{k+3}+e})) = ψ₁(Â_β + Ω₁^{X̂(β) + Θ e})` (one image per sub-base; Vx.vxNoCompat forbids a constant
X̂; known only at X = Y₃, b = Ω₃: Vt.vtTopY3_all_piecewise). -/
theorem skTopDyn (S : InaccSeq.{0}) : TopDynAll S := by
  sorry

/-- STATUS: REFUTED (Xi.xiTopFam_false, from Xi.xiReadOm, Xi.xiShape, Xi.xiFamOm_false; round 122; REPLACED by skTopUp;
kept for the record, no node uses it): at the restart of m* = L(0), k = 0, β = 0, e = ω (a code, Θ ω = ω):
Θ(ψ₂(W^{Ω₃+ω})) = ψ₁(A + P*), P* = ψ₂(Ω^{Ω₂+ω}) strongly critical (upper half Xd.xdUp_at, lower half the law at k = 0
on the bases W^{Ω₃+n}); the law asks ψ₁(A + 1 + Q), Q = Ω^{X̂(0)+ω} ≠ P*; Q < P* is below an own argument A + p_n
with ψ₁(A + p_n) < Θ, Q > P* is above the own A + P* + 1.
SIZE: M
`∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ, ∀ code e < Ω₂ : ∃ X̂_e : base ↦ image, ∀ base β :
Θ(ψ₂(β + Ω₂^{Ω_{k+3}+e})) = ψ₁(Â_β + Ω₁^{X̂_e(β) + Θ e})` (`Wg.WgTopFamAll`; per base by `Wg.wgDyn_iff_pt`).
REFUTE FIRST: NO EVIDENCE.  `SkRX.skrxDyn01` does not apply (`Wg.wgSep01`: X̂₀(0) ≤ Y₂ < X̂₀(Ω₃) ≤ X̂₁(0) is
consistent; the contradiction is the case X̂₁ = X̂₀); `Vx.vxDyn_le0` / `vxDyn_gtOm3` / `vxDyn_nonconst` / `vxNoCompat`
constrain X̂₀ only; `Vn.vnTop_Om3`, `Vq.vqNoTop_Om3` refute constant images only; `Wb.wbNoY` / `wbNoIt` refute the
image Y_{k+2} at β = 0, not every image.  Proved part: e = 0 at β = 0 (`skTopFam0`).  Open: every other base
(β = Ω₃·γ, γ ≥ 1, at e = 0: no Lean value of Θ(ψ₂(Ω₃·γ + Ω₃))) and e ≥ 1 (β = 0, e = 1: no value of Θ(ψ₂(Ω₃·Ω₂))).
Round 113: every image at the base 0 has Ω^{X̂} < θ (skImgLtTh), the naive image T(Y(β)) is REFUTED at every k ≥ 1
(skNaiveT); the e = 0 part with the candidate image X̂⁰_k(β) = ψ₂(T β + Ω_{k+2}) is the node skX0Law (OPEN, all
Lean tests passed, skX0Tests).  Expected at e = 1, β = 0 (not in Lean): X̂₁(0) = ψ₂(Ω₂·Θ(t₁)), t₁ = ψ₂(Ω₃·Ω₂), i.e. the
level map T taken relative to the hull of the atom (Ω₂ ↦ Θ(t₁)), the image of ψ₃(Ω₃·Ω₂). -/
theorem skTopFam (S : InaccSeq.{0}) : Wg.WgTopFamAll S := by
  sorry

/-- STATUS: PROVED (Xi.xiTopFam_false, from Xi.xiReadOm, Xi.xiPstar_cof, Xi.xiShape, Xi.xiFamOm_false; NEW round 122;
a REFUTE-FIRST record, no node uses it)
SIZE: S
`¬ skTopFam`: `¬ Wg.WgTopFamAll S` (fails at k = 0, e = ω, β = 0, the restart of m* = L(0)). -/
theorem skTopFamRef (S : InaccSeq.{0}) : ¬ Wg.WgTopFamAll S := Xi.xiTopFam_false S

/-- STATUS: PROVED (Xm.xmTopUp, from Xm.xmSucc, Xm.xmLim, Xm.xmPlat, Xi.xiTopUp0; round 123: was OPEN; checkable only
after the merge)
SIZE: L
`Xi.XiTopUp`: `∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ, ∀ code e < Ω₂, ∀ β ∈ D, RoBaseE λ Ω_{k+3} e β :
Θ(ψ₂(β + W^{Ω_{k+3}+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+e})))` (the Wz.WzUpU bound, Xd.xdUp_at, is attained at
every top atom).  One induction on e: e = 0 (skTopUp0), successor (skTopUpSucc, with the plateau lemma skPlat),
limit (skTopUpLim).  REFUTE FIRST (round 123) at e = 1 and e = ω + 1 (k = 0, β = 0): both hold (skTopUpTests). -/
theorem skTopUp (S : InaccSeq.{0}) : Xi.XiTopUp S := Xm.xmTopUp S

/-- STATUS: PROVED (Xm.xmPlat, from Xm.xmKey, Xm.xmR2, Xm.xmR3, Xm.xmStep; NEW round 123; checkable only after the merge)
SIZE: M
THE PLATEAU LEMMA: `x_0 ≤ x_1, x_0 < Ω₁, b ∈ Cl(b, ψ₂ b), m ∈ Cl(a, ψ₂ a) ∀ a, m ∈ Cl(a_n, x_{n+1}) ∀ n ⇒
ψ₁(B + ψ₂(b + ω^m·Ω₁)) ≤ sup_n x_n`, `x_{n+1} = ψ₁(a_n)`, `a_n = B + ψ₂(b + ω^m·x_n)`. -/
theorem skPlat (S : InaccSeq.{0}) : ∀ {B b m x0 : Ordinal.{0}}, b ∈ S.CSet b (S.psi b (Om (1 + 1))) →
    (∀ a : Ordinal.{0}, m ∈ S.CSet a (S.psi a (Om (1 + 1)))) → x0 ≤ Xm.xmX S B b m x0 1 → x0 < Om 1 →
    (∀ n, m ∈ S.CSet (Xm.xmA S B b m x0 n) (Xm.xmX S B b m x0 (n + 1))) →
    S.psi (B + S.psi (b + ω ^ m * Om 1) (Om (1 + 1))) (Om 1) ≤ ⨆ n : ℕ, Xm.xmX S B b m x0 n :=
  fun hb hm2 h0 hx0 hm => Xm.xmPlat hb hm2 h0 hx0 hm

/-- STATUS: PROVED (Xm.xmSucc, from Xm.xmPlat, Xm.xmU_it, Xd.xdUp_at, Xd.xdTr, Vh.vhT_cnfW; NEW round 123; checkable only
after the merge)
SIZE: M
Successor step of skTopUp: `(the law at e on every base of exponent e) ∧ RoBaseE λ Ω_{k+3} (e+1) β ⇒ the law at e + 1`
(sub-bases β + W^{X+e}·u_n, u_{n+1} = ψ₂(β + W^{X+e}·u_n + W^{X+e}); T(β + W^{X+e+1}) = Tβ + Ω^{T(X+e)}·Ω₁). -/
theorem skTopUpSucc (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A e β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → GxCl (upsilon l) (ldAtR S l) e →
      Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β →
      (∀ β', Vb.VbD S l β' → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β' →
        gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) β') =
          S.psi (A + 1 + S.psi (Vb.vbT S l (β' + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1)))
            (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + (e + 1)) β) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + (e + 1))))
          (Om (1 + 1))) (Om 1) :=
  fun k _ _ _ _ _ hl hX hA hρ hec hβD hB IH => Xm.xmSucc hl hX hA hρ k hec hβD hB IH

/-- STATUS: PROVED (Xm.xmLim, from Xm.xmCofL, Xm.xmTh_lim, Xd.xdUp_at, Lw.lw_psi_limit; NEW round 123; generalizes
Xi.xiReadOm; checkable only after the merge)
SIZE: M
Limit step of skTopUp: `e a limit code, RoBaseE λ Ω_{k+3} e β, the law at every code e' < e over β ⇒ the law at e`. -/
theorem skTopUpLim (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A e β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → GxCl (upsilon l) (ldAtR S l) e →
      Order.IsSuccLimit e → Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      (∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e →
        gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e') β) =
          S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e'))) (Om (1 + 1)))
            (Om 1)) →
      gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) β) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1)))
          (Om 1) :=
  fun k _ _ _ _ _ hl hX hA hρ hec hlim hβD hB IH => Xm.xmLim hl hX hA hρ k hec hlim hβD hB IH

/-- STATUS: PROVED (Xm.xmTest1, Xm.xmTestW1, Xm.xmRB0; NEW round 123; the REFUTE-FIRST points of skTopUp and its
non-vacuity; checkable only after the merge)
SIZE: S
At the restart of m* = L(0) with its own A: the law at (k, e, β) = (0, 1, 0) and (0, ω + 1, 0). -/
theorem skTopUpTests (S : InaccSeq.{0}) :
    (∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Nm.Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 1) 0) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 1))) (Om (1 + 1)))
          (Om 1)) ∧
    (∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Nm.Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + (ω + 1)) 0) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + (ω + 1))))
          (Om (1 + 1))) (Om 1)) :=
  ⟨Xm.xmTest1 S, Xm.xmTestW1 S⟩

/-- STATUS: PROVED (Xi.xiTopUp0, from Xi.xiLow, Xi.xiLaw_of_low, Xd.xdUp_at; NEW round 122; checkable only after the merge)
SIZE: S
skTopUp at e = 0: `restart λ, A own, ψ₁(A) = ρ_λ, β ∈ D, RoBaseE λ Ω_{k+3} 0 β ⇒
Θ(ψ₂(β + W^{Ω_{k+3}+0})) = ψ₁(A + 1 + ψ₂(T(β + W^{Ω_{k+3}+0})))`. -/
theorem skTopUp0 (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0) β) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)))
          (Om 1) :=
  fun k _ _ _ _ hl hX hA hρ hβD hB => Xi.xiTopUp0 hl hX hA hρ k hβD hB

/-- STATUS: PROVED (Xi.xiTopUpOm, Xi.xiReadOm; NEW round 122; checkable only after the merge)
SIZE: S
skTopUp at k = 0, e = ω, β = 0 (non-vacuity of skTopUp past e = 0): `Θ(ψ₂(W^{Ω₃+ω})) = ψ₁(A + 1 + ψ₂(Ω^{Ω₂+ω}))`. -/
theorem skTopUpOm (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + ω) 0) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + ω)))
          (Om (1 + 1))) (Om 1) :=
  fun _ _ _ hl hX hA hρ => Xi.xiTopUpOm hl hX hA hρ

/-- STATUS: PROVED (Wg.wgTop0_base0, Wg.wgTop0_base0_wit)
SIZE: S
Non-vacuity of skTopFam at k = 0, e = 0, β = 0: `Θ(ψ₂(Ω₃)) = ψ₁(A+1+Ω₁^{Y₂})` (image X̂₀(0) = Y₂), at every restart
with an own A, in particular at the witness restart of SkRX.skrxTopDynAll_false (the restart of m* = L(0)). -/
theorem skTopFam0 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (1 + 1 + 1)) (S.psi (Om (1 + 1)) (Om (1 + 1))) 0 0 :=
  fun _ _ _ hl hX hA hρ => Wg.wgTop0_base0 hl hX hA hρ

/-- STATUS: PROVED (Wg.wgSep01)
SIZE: S
REFUTE-FIRST record for skTopFam: `VtTopDyn λ 0 Ω₃ X̂₀ 0 ∧ VtTopDyn λ 0 Ω₃ X̂₁ 1 ⇒ X̂₀(0) ≤ Y₂ < X̂₀(Ω₃) ≤ X̂₁(0)`
(so the image must depend on e; SkRX.skrxDyn01 is the case X̂₁ = X̂₀). -/
theorem skTopSep (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ∀ X0 X1 : Ordinal.{0} → Ordinal.{0}, Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X0 0 →
        Vt.VtTopDyn S l 0 (Om (1 + 1 + 1)) X1 1 →
        X0 0 ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) ∧ S.psi (Om (1 + 1)) (Om (1 + 1)) < X0 (Om (1 + 1 + 1)) ∧
          X0 (Om (1 + 1 + 1)) ≤ X1 0 :=
  fun _ _ _ hl hX hA hρ _ _ h0 h1 => Wg.wgSep01 hl hX hA hρ h0 h1

/-- STATUS: PROVED (Wv.wvImg_lt_th, from Wl.wlThVal, Wv.wvRead_lt_th; NEW round 113)
SIZE: S
REFUTE-FIRST record for skTopFam: `restart λ, A own, ψ₁(A) = ρ_λ, WgTopAt λ Ω_{k+3} Z 0 0 ⇒ Ω^Z < θ` (every image of
the law at the base 0 is below θ, at every level k). -/
theorem skImgLtTh (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A Z : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) Z 0 0 → Le.leOe Z < ConjT.th S :=
  fun k _ _ _ _ hl hX hA hρ hT => Wv.wvImg_lt_th hl hX hA hρ k hT

/-- STATUS: PROVED (Wv.wvNoT, Wv.wvT_Y, Wv.wvNoBig; NEW round 113; a NO-GO record, no node uses it)
SIZE: S
`∀ k ≥ 1 : ¬ WgTopAt λ Ω_{k+3} (T(Y_{k+3})) 0 0`: the naive intrinsic image X̂ = T(ψ_{Ω_{k+3}}(β + Ω_{k+3})) (the moved
shift read one level down, `T = Vb.vbT`) is REFUTED at β = 0 for every k ≥ 1 (T(Y_{k+3}) = Y_{k+2} ≥ Ω₂ > θ). -/
theorem skNaiveT (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A : Ordinal.{0}), 1 ≤ k → IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ¬ Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Vb.vbT S l (Uj.ujY S ((k : Ordinal.{0}) + 1))) 0 0 :=
  fun k _ _ _ hk hl hX hA hρ => Wv.wvNoT hl hX hA hρ k hk

/-- STATUS: PROVED (Wv.wvImg1_gt, from Vq.vqRead_Om3Y3; NEW round 113)
SIZE: S
`WgTopAt λ Ω₄ Z 0 0 ⇒ Y₂ + Y₂ < Ω^Z` (lower test at k = 1; with skImgLtTh: Y₂ + Y₂ < Ω^Z < θ). -/
theorem skImg1Gt (S : InaccSeq.{0}) :
    ∀ (l ηx A Z : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (1 + 1 + 1 + 1)) Z 0 0 →
        S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1)) (Om (1 + 1)) < Le.leOe Z :=
  fun _ _ _ _ hl hX hA hρ hT => Wv.wvImg1_gt hl hX hA hρ hT

/-- STATUS: PROVED (Wv.wvX0_law00, Wv.wvX0_sep, Wv.wvX0_lt_th, Wv.wvX0_one_in; NEW round 113)
SIZE: S
REFUTE-FIRST tests of the candidate X̂⁰_k(β) = ψ₂(T β + Ω_{k+2}) (`Wv.wvX0`): the law holds at k = 0, β = 0
(image Y₂, Wg.wgTop0_base0); Ω^{X̂⁰_0(0)} ≤ Y₂ < Ω^{X̂⁰_0(Ω₃)} (Vx.vxDyn_le0, Vx.vxDyn_gtOm3, Wg.wgSep01; not constant:
Vx.vxDyn_nonconst, Vq.vqNoTop_Om3, Vn.vnTop_Om3); Ω^{X̂⁰_k(0)} < θ at every k (skImgLtTh; so Wb.wbNoY, skNaiveT do not
apply); Y₂ + Y₂ < Ω^{X̂⁰_1(0)} (skImg1Gt). -/
theorem skX0Tests (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 0) 0 0 ∧
      Le.leOe (Wv.wvX0 S l 0 0) ≤ S.psi (Om (1 + 1)) (Om (1 + 1)) ∧
      S.psi (Om (1 + 1)) (Om (1 + 1)) < Le.leOe (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) ∧
      (∀ k : ℕ, Le.leOe (Wv.wvX0 S l k 0) < ConjT.th S) ∧
      S.psi (Om (1 + 1)) (Om (1 + 1)) + S.psi (Om (1 + 1)) (Om (1 + 1)) < Le.leOe (Wv.wvX0 S l 1 0) :=
  fun _ _ _ hl hX hA hρ =>
    ⟨Wv.wvX0_law00 hl hX hA hρ, (Wv.wvX0_sep hl hX).1, (Wv.wvX0_sep hl hX).2.2.2,
      Wv.wvX0_lt_th hl hX, (Wv.wvX0_one_in hl hX).1⟩

/-- STATUS: REFUTED (Xd.xdX0Law_false, from Xd.xdRef; round 121; REPLACED by skX0LawDK; kept for the record, no node
uses it): at the restart of m* = L(0), β = Ω_ω satisfies Ro.RoBaseE at Ω₃ (A > Ω_ω + Ω₃, Xd.xdA_big), T Ω_ω = 0
(Xd.xdT_OmW: Vb.vbT is 0 off its domain), so the image is X̂⁰_0(Ω_ω) = Y₂; the law would give Θ(ψ₂(Ω_ω + Ω₃)) =
ψ₁(A + θ + Y₂), but the lift at the base Ω_ω (Xd.xdLift, Â = A + θ, L(ζ) = Ω₂ + ζ) gives ψ₁(A + θ + z₂) ≤ Θ(ψ₂(Ω_ω + κ z₂))
with z₂ = ψ₂(Ω₂ + Y₂) > Y₂.
SIZE: L
`∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ, ∀ base β of Ω_{k+3} (exponent 0) : Θ(ψ₂(β + Ω_{k+3})) = ψ₁(Â_β + Ω^{X̂⁰_k(β)})`,
X̂⁰_k(β) = ψ₂(T β + Ω_{k+2}) (the e = 0 part of skTopFam with an explicit image).  Proved: k = 0, β = 0 (skX0Tests).
REFUTE FIRST: NO EVIDENCE (skX0Tests: every Lean constraint holds).  Open: β = Ω₃ at k = 0 (image ψ₂(Ω₂·2): the atom
ψ₂(Ω₃·2) = ψ₂(Ω₃ + ψ₃(Ω₃·2)) is the limit of ψ₂(Ω₃ + x_n), x_{n+1} = ψ₃(Ω₃ + x_n), whose shifts x_n ≥ Y₃ for n ≥ 1
are past the Y₃ wall: no level system there) and k = 1 at β = 0 (image ψ₂(Ω₃); needs offsets up to ψ₂(Ω₃) lifted
at the base 0, where the Rx lift fails).  L: same missing level system as skWallBase.
Round 114: at k = 0, β = Ω₃ the lower half is PROVED (skX0LowOm3) and the law is REDUCED to skUpU (skX0Om3).
Route: skUpU gives the upper half at every (k, β) whose base image is absorbed (Â_β < A + 1 + X̂⁰_k(β), itself from
skUpU at β); the lower half at k = 0 and every base β ≥ Ω₃ is the lift of Wz.wzLift at the base β with the level
bound L = T β + ζ (needs ζ < ψ₂(T β + ζ) below ψ₂(T β + Ω₂), the analogue of Wz.wzLtPsi); at k ≥ 1 the lift by κ
reaches only offsets ζ < ψ₂(T β + Ω₂) (κ ζ < Ω₃): the lower half needs atoms ψ₂(β + y), y ∈ [Ω₃, Ω_{k+3}). -/
theorem skX0Law (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k β) 0 β := by
  sorry

/-- STATUS: PROVED (Xd.xdRef, Xd.xdX0Law_false; NEW round 121; a REFUTE-FIRST record, no node uses it)
SIZE: S
`¬ skX0Law`: the statement of skX0Law fails at k = 0, β = Ω_ω, the restart of m* = L(0). -/
theorem skX0Ref (S : InaccSeq.{0}) :
    ¬ ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k β) 0 β :=
  Xd.xdX0Law_false S

/-- STATUS: PROVED (Xi.xiLawDK, from Xi.xiLow, Xi.xiLowStep, Xi.xiCof, Xi.xiT_mod, Xi.xiLaw_of_low, Xd.xdLow0,
Xd.xdUp_at; round 122; checkable only after the merge; was OPEN L, NEW round 121, replacing the REFUTED skX0Law)
SIZE: L
`∀ k, ∀ restart λ, A own, ψ₁(A) = ρ_λ, ∀ β ∈ D (Vb.VbD), RoBaseE λ Ω_{k+3} 0 β : Θ(ψ₂(β + Ω_{k+3})) =
ψ₁(Â_β + Ω^{X̂⁰_k(β)})`, X̂⁰_k(β) = ψ₂(T β + Ω_{k+2}).  PROVED parts: k = 0, every β ∈ D (skX0LawD); k = 1, β = 0
(skX0Law1).  REFUTE FIRST: NO EVIDENCE (the upper half holds at every (k, β), Xd.xdUp_at; equality at (0, β ∈ D),
(1, 0); Xd.xdX0Law_false needs β ∉ D).  Route at k = 1, β ∈ D: the lower half from skX0LawD at the bases β + u, u
cofinal ψ_{Ω₄}-iterates over β (T(β + u_n) = T β + y_n), with ψ₂(T β + Ω₃) = sup_n ψ₂(T β + y_n) (the base-relative
Vn.vnPsi2_eq / Uu.uuY_le_sup); then k + 1 from k at every base the same way (induction on k with the law at all
bases).  L: a base-relative version of Vn.vnPsi2_eq and of the ψ_{Ω_{k+3}}-iterates over a base. -/
theorem skX0LawDK (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) 0 β →
      Wg.WgTopAt S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l k β) 0 β :=
  Xi.xiLawDK S

/-- STATUS: PROVED (Xi.xiLaw_1_Om4, Xi.xiLaw_2_0, Xi.xiLawDK_wit; NEW round 122; a REFUTE-FIRST record and the
non-vacuity of skX0LawDK, no node uses it)
SIZE: S
The two REFUTE-FIRST test points of skX0LawDK hold: k = 1, β = Ω₄ (Θ(ψ₂(Ω₄·2)) = ψ₁(Â + ψ₂(Ω₃·2))) and k = 2, β = 0
(Θ(ψ₂(Ω₅)) = ψ₁(A + 1 + ψ₂(Ω₄))), at every restart with an own A (all hypotheses hold at the restart of m*). -/
theorem skX0Tests3 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1))
        (Wv.wvX0 S l 1 (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1))) 0 (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) ∧
      Wg.WgTopAt S l (Om (((2 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l 2 0) 0 0 :=
  fun _ _ _ hl hX hA hρ => ⟨Xi.xiLaw_1_Om4 hl hX hA hρ, Xi.xiLaw_2_0 hl hX hA hρ⟩

/-- STATUS: PROVED (Xd.xdLaw0D, from Xd.xdUp_at, Xd.xdLow0, Xd.xdLift, Xd.xdLtPsi, Xd.xdX_le_sup, Xd.xdT_mod,
Xd.xdT_leaf, Xd.xdTr; NEW round 121; checkable only after the merge)
SIZE: M
skX0LawDK at k = 0: `restart λ, A own, ψ₁(A) = ρ_λ, β ∈ D, RoBaseE λ Ω₃ 0 β ⇒ WgTopAt λ Ω₃ (X̂⁰_0(β)) 0 β`
(Θ(ψ₂(β + Ω₃)) = ψ₁(A + ψ₂(T β + Ω₂))).  Non-vacuity: Xd.xdLaw0D_wit (β = Ω₃ at the restart of m*). -/
theorem skX0LawD (S : InaccSeq.{0}) :
    ∀ (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → Vb.VbD S l β →
      Ro.RoBaseE S l (Om (1 + 1 + 1)) 0 β →
      Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 β) 0 β :=
  fun _ _ _ _ hl hX hA hρ hβ hB => Xd.xdLaw0D hl hX hA hρ hβ hB

/-- STATUS: PROVED (Xd.xdLaw1, Xd.xdLaw1_val, from Xd.xdUp_at, Xd.xdLow0 at the bases u_n = ψ_{Ω₄}^n(0), Xd.xdU_T,
Xd.xdPsi3_cof; NEW round 121; checkable only after the merge)
SIZE: M
skX0LawDK at k = 1, β = 0: `restart λ, A own, ψ₁(A) = ρ_λ ⇒ WgTopAt λ Ω₄ (X̂⁰_1(0)) 0 0`
(Θ(ψ₂(Ω₄)) = ψ₁(A + 1 + ψ₂(Ω₃)); the image ψ₂(Ω₃) passes skImgLtTh, skImg1Gt, skX0Tests2). -/
theorem skX0Law1 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (((1 : ℕ) : Ordinal.{0}) + 1 + 1 + 1)) (Wv.wvX0 S l 1 0) 0 0 :=
  fun _ _ _ hl hX hA hρ => Xd.xdLaw1 hl hX hA hρ

/-- STATUS: PROVED (Wz.wzLawLow, from Wz.wzLowAll, Wz.wzLift, Wz.wzL_memL, Wz.wzLtPsi, Wz.wzX_le_sup, Rx.rxLift,
Lw.lw_psi_limit; NEW round 114; checkable only after the merge)
SIZE: M
Lower half of skX0Law at k = 0, β = Ω₃: `restart λ, A own, ψ₁(A) = ρ_λ, ∀ own Â with Θ(ψ₂(Ω₃)) = ψ₁(Â) :
ψ₁(Â + Ω^{X̂⁰_0(Ω₃) + Θ 0}) ≤ Θ(T_{Ω₃}(Ω₃))` (X̂⁰_0(Ω₃) = ψ₂(Ω₂·2), Â = A + 1 + Y₂: the bound is ψ₁(A + ψ₂(Ω₂·2))). -/
theorem skX0LowOm3 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ∀ Â, Â ∈ S.CSet Â (S.psi Â (Om 1)) →
        gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) = S.psi Â (Om 1) →
        S.psi (Â + Le.leOe (Wv.wvX0 S l 0 (Om (1 + 1 + 1)) + gxTh (upsilon l) (ldAtR S l) 0)) (Om 1) ≤
          gxTh (upsilon l) (ldAtR S l) (Le.leTe S (Om (1 + 1 + 1) + 0) (Om (1 + 1 + 1))) :=
  fun _ _ _ hl hX hA hρ => Wz.wzLawLow hl hX hA hρ

/-- STATUS: PROVED (Wz.wzLaw_iff, Wz.wzRHS, Wz.wzHat_eq, Wz.wzBase; NEW round 114; checkable only after the merge)
SIZE: S
`restart λ, A own, ψ₁(A) = ρ_λ : WgTopAt λ Ω₃ (X̂⁰_0(Ω₃)) 0 Ω₃ ⇔ Θ(ψ₂(Ω₃ + Ω₃)) ≤ ψ₁(A_{η_λ} + ψ₂(Ω₂ + Ω₂))`
(the law at k = 0, β = Ω₃ is exactly its upper half). -/
theorem skX0Om3Iff (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      (Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) 0 (Om (1 + 1 + 1)) ↔
        gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Om (1 + 1 + 1)) (Om (1 + 1))) ≤
          S.psi (ConjT.Aη S (cdEta S l) + S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1))) (Om 1)) :=
  fun _ _ _ hl hX hA hρ => Wz.wzLaw_iff hl hX hA hρ

/-- STATUS: PROVED (Xd.xdUpU, from Xd.xdUp_at, Xd.xdT_cl, Xd.xdTr, Xd.xdT_psi_lt, Ld.ldAtom_le, Mx.mxGx_bound; round 121;
checkable only after the merge; was OPEN L)
SIZE: L
`Wz.WzUpU`: `∀ restart λ, A own, ψ₁(A) = ρ_λ, ∀ a ∈ D (Vb.VbD), a ∈ Cl(a, ψ₂(a)) : Θ(ψ₂(a)) ≤ ψ₁(A + 1 + ψ₂(T a))`
(T = Vb.vbT).  REFUTE FIRST: NO EVIDENCE: equality at a = Ω₃ (Wz.wzU_Om3), tight at a = Ω₃·2 (Wz.wzU_Om33_low) and
at θ (Wl.wlThVal: ψ₁(A + θ) = ψ₁(A + 1 + ψ₂(T Ω_ω))), loose at a = 0, Ω₃ + Y₃ (Vq.vqRead_Om3Y3), y_n (Vq.vqTop_it),
consistent with every lift lower bound (Wz.wzU_lift, Wl.wlBlk0) and with Wv.wvImg_lt_th, Wb.wbNoY.
Plan: induction on the atom (Ld.ldAtom_le); for atoms t' = ψ₂(a') < t = ψ₂(a) (normal a', a): a' ∈ Cl(a, ψ₂(a)) ⇒
T a' ∈ Cl(T a, ψ₂(T a)) (codes of a' are below ψ₂(a), T maps them to countable Θ-values), the leaves of T a' are
below Θ(t') ≤ ψ₁(A + 1 + ψ₂(T a')) (so A + 1 + ψ₂(T a') is own), hence ψ₁(A+1+ψ₂(T a')) < ψ₁(A+1+ψ₂(T a)).
L: the transfer of ψ₂-closure through T and the leaf bound are not in Lean. -/
theorem skUpU (S : InaccSeq.{0}) : Wz.WzUpU S := Xd.xdUpU

/-- STATUS: PROVED (skUpU; Wz.wzLaw_of_U, Wz.wzUp_Om3_of, Wz.wzT_Om33, Wz.wzLaw_iff; NEW round 114; round 121: all
children proved; = skX0LawD at β = Ω₃)
SIZE: S
skX0Law at k = 0, β = Ω₃: `restart λ, A own, ψ₁(A) = ρ_λ ⇒ WgTopAt λ Ω₃ (X̂⁰_0(Ω₃)) 0 Ω₃`
(Θ(ψ₂(Ω₃·2)) = ψ₁(A + 1 + Y₂ + ψ₂(Ω₂·2))). -/
theorem skX0Om3 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      Wg.WgTopAt S l (Om (1 + 1 + 1)) (Wv.wvX0 S l 0 (Om (1 + 1 + 1))) 0 (Om (1 + 1 + 1)) :=
  fun _ _ _ hl hX hA hρ => Wz.wzLaw_of_U hl hX (skUpU S) hA hρ

/-- STATUS: PROVED (Wz.wzImg0_ge, Wz.wzImg1_gt, Wz.wzU_Om3; NEW round 114; a REFUTE-FIRST record, no node uses it)
SIZE: S
`WgTopAt λ Ω₃ Z 0 Ω₃ ⇒ ψ₂(Ω₂·2) ≤ Ω^Z` and `WgTopAt λ Ω₄ Z 0 0 ⇒ ψ₂(Ω₂·2) < Ω^Z` (lower tests at k = 0, β = Ω₃ and
k = 1, β = 0; the candidates X̂⁰_0(Ω₃) = ψ₂(Ω₂·2), X̂⁰_1(0) = ψ₂(Ω₃) pass; sharpens skImg1Gt), and the skUpU bound is
an equality at a = Ω₃. -/
theorem skX0Tests2 (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      (∀ Z, Wg.WgTopAt S l (Om (1 + 1 + 1)) Z 0 (Om (1 + 1 + 1)) →
        S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) ≤ Le.leOe Z) ∧
      (∀ Z, Wg.WgTopAt S l (Om (1 + 1 + 1 + 1)) Z 0 0 →
        S.psi (Om (1 + 1) + Om (1 + 1)) (Om (1 + 1)) < Le.leOe Z) ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1)) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (Om (1 + 1 + 1))) (Om (1 + 1))) (Om 1) :=
  fun _ _ _ hl hX hA hρ =>
    ⟨fun _ hT => Wz.wzImg0_ge hl hX hA hρ hT, fun _ hT => Wz.wzImg1_gt hl hX hA hρ hT, Wz.wzU_Om3 hl hX hA hρ⟩

/-- STATUS: PROVED (Xq.xqRef_wit, from Xq.xqRef, Xq.xqBlk, Wz.wzBase, Vh.vhT_add, Vb.vbT_Om; NEW round 124; the
REFUTE-FIRST record for the non-top atoms; checkable only after the merge)
SIZE: S
At the restart of m* = L(0) with its own A, the normal member a = Ω₃ + 1 ∈ D has
`Θ(ψ₂ a) ≠ ψ₁(A + 1 + ψ₂(T a))` (the value is `ψ₁(A + 1 + ψ₂(Ω₂) + 1)`, the block law over the top Ω₃). -/
theorem skWallRefNonTop (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Nm.Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧ Vb.VbD S l (Om (1 + 1 + 1) + 1) ∧
      Om (1 + 1 + 1) + 1 ∈ S.CSet (Om (1 + 1 + 1) + 1) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + 1) (Om (1 + 1))) ≠
        S.psi (A + 1 + S.psi (Vb.vbT S l (Om (1 + 1 + 1) + 1)) (Om (1 + 1))) (Om 1) :=
  Xq.xqRef_wit S

/-- STATUS: PROVED (Xq.xqTopBlk, from Xq.xqBlk, Xq.xqOwn, Xm.xmTopUp, Ld.ldBlk_step, Ld.ldBlk_next; NEW round 124;
checkable only after the merge)
SIZE: M
The block law with the proved top value, above every top atom `t = β + W^{Ω_{k+3}+e}`:
`Θ(ψ₂(t + c)) = ψ₁(A + 1 + ψ₂(T t) + Θ c)` (codes `c < ψ₂(t + Ω₂)`), `Θ(ψ₂(t + Ω₂)) = ψ₁(A + 1 + ψ₂(T t) + Ω₁)`. -/
theorem skTopBlk (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A e β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      (∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) →
        gxTh (upsilon l) (ldAtR S l) (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + c) (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1)) +
            gxTh (upsilon l) (ldAtR S l) c) (Om 1)) ∧
      gxTh (upsilon l) (ldAtR S l) (ldTop S (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1)) + Om 1)
          (Om 1) :=
  fun k _ _ _ _ _ hl hX hA hρ hec he2 hβD hB => Xq.xqTopBlk hl hX hA hρ k hec he2 hβD hB

/-- STATUS: PROVED (Xq.xqTMove, from Xq.xqTE, Xq.xqN_cl, Xq.xqLeaf, Vb.vbLeaf_of_codes, Vb.vbT_move, Xd.xdT_cl;
NEW round 124; checkable only after the merge)
SIZE: M
The move of `T` at a wall atom `ψ₂ a` (`a ∈ D` normal) from the moves of the codes below it (the premise of
WallBelow): `T_{λ'}(B_n x) = B_n(T_λ x)` for every `x ∈ D ∩ Cl(a, ψ₂ a)`. -/
theorem skTMove (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' ηx ηx' A a : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      IsRestartIdx l' → upsilon l' < Nm.Pv S ηx' →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      ∀ x, Vb.VbD S l x → x ∈ S.CSet a (S.psi a (Om (1 + 1))) →
        MvD S x ∧ MvD S (Vb.vbT S l x) ∧ Vb.vbT S l' (Bc.bcB S n x) = Bc.bcB S n (Vb.vbT S l x) :=
  fun _ _ _ _ _ _ _ hl hX hl' hX' hA hρ IH => Xq.xqTMove hl hX hl' hX' hA hρ IH

/-- STATUS: PROVED (Xq.xqSigMove, from Xq.xqOwn, Xq.xqTnorm, Ld.ldB_psi_add, Ug.ugB_psiS, Mx.mxPsi_inj; NEW round 124;
checkable only after the merge)
SIZE: S
`B_n` through `σ`: at a window (`c_n ≤ ρ_λ`, `B_n ρ_λ = ρ_{λ'}`), `B_n(ψ₁(A + 1 + ψ₂(T a))) = ψ₁(A' + 1 + ψ₂(B_n(T a)))`
for every normal `a ∈ D` with `T a ∈ MvD` and `ψ₁(A + 1 + ψ₂(T a)) < c_{n+1}`. -/
theorem skSigMove (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' ηx A A' a : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      Bc.bcC S n ≤ upsilon l → Bc.bcB S n (upsilon l) = upsilon l' → Vb.VbD S l a →
      a ∈ S.CSet a (S.psi a (Om (1 + 1))) → MvD S (Vb.vbT S l a) →
      S.psi (A + 1 + S.psi (Vb.vbT S l a) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1) →
      Bc.bcB S n (S.psi (A + 1 + S.psi (Vb.vbT S l a) (Om (1 + 1))) (Om 1)) =
        S.psi (A' + 1 + S.psi (Bc.bcB S n (Vb.vbT S l a)) (Om (1 + 1))) (Om 1) :=
  fun _ _ _ _ _ _ _ hl hX hA hρ hA' hρ' hlo hB ha han hDT hhi =>
    (Xq.xqSigMove hl hX hA hρ hA' hρ' hlo hB ha han hDT hhi).2.2

/-- STATUS: PROVED (Xq.xqTopMove, from Xq.xqTopD, Xq.xqLawMove, Xq.xqTMove, Xq.xqSigMove, Xm.xmTopUp at λ and λ';
NEW round 124; checkable only after the merge)
SIZE: M
Every top atom `ψ₂(t)`, `t = β + W^{Ω_{k+3}+e}`, moves under the premise of WallBelow once its BASE DATA move
(`B_n t = β' + W^{Ω_{k+3}+e'}` with `(e', β')` a top base of `λ'`) and `Θ(ψ₂ t) < c_{n+1}`. -/
theorem skTopMove (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' ηx ηx' A A' e β e' β' : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      IsRestartIdx l' → upsilon l' < Nm.Pv S ηx' →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      Bc.bcC S n ≤ upsilon l → Bc.bcB S n (upsilon l) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      GxCl (upsilon l') (ldAtR S l') e' → e' < Om (1 + 1) → Vb.VbD S l' β' →
      Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e' β' →
      Bc.bcB S n (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
        β' + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e') →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) <
        Bc.bcC S (n + 1) →
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) :=
  fun _ k _ _ _ _ _ _ _ _ _ _ hl hX hl' hX' hA hρ hA' hρ' hlo hB hec he2 hβD hBE hec' he2' hβD' hBE' hmv IH hhi =>
    (Xq.xqTopMove hl hX hl' hX' hA hρ hA' hρ' hlo hB k hec he2 hβD hBE hec' he2' hβD' hBE' hmv IH hhi).2.2

/-- STATUS: PROVED (Xv.xvBaseMove0, from Xv.xvBase0, Xv.xvShB, Ro.roB_We, Mx.mxB_atom, Vs.vsW_D; NEW round 125;
checkable only after the merge)
SIZE: S
THE BASE-DATA MOVE at the base `0` for the small exponents: at every window, under the moves of the codes below
`ψ₂(W^{Ω_{k+3}+e})`, every code `e < ψ₂(Ω_{k+3})` of `λ` has `B_n e` a code of `λ'` below `ψ₂(Ω_{k+3})`,
`(B_n e, 0)` a top base of `λ'` (`Ro.RoBaseE`), and `B_n(0 + W^{Ω_{k+3}+e}) = 0 + W^{Ω_{k+3}+B_n e}`. -/
theorem skBaseMove0 (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n e) ∧
        Bc.bcB S n e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) ∧
        Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Bc.bcB S n e) 0 ∧
        Bc.bcB S n (0 + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
          0 + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) :=
  fun _ k _ _ _ hR h1 hr hl' hB hec heY IH => by
    obtain ⟨-, hBec, -, hBeY, hb', -, hmv⟩ := Xv.xvBaseMove0 hR h1 hr hl' hB k hec heY IH
    exact ⟨hBec, hBeY, hb', hmv⟩

/-- STATUS: PROVED (Xv.xvTop0Move, from Xv.xvBaseMove0, Xv.xvWin, Xq.xqTopMove, Lj.ljTheta_lt_delta, Ld.ldTheta;
NEW round 125; checkable only after the merge)
SIZE: M
Every top atom `s = ψ₂(W^{Ω_{k+3}+e})` with a code `e < ψ₂(Ω_{k+3})` moves at every window under the premise of
WallBelow at `s`: `MvD s`, `B_n s = ψ₂(W^{Ω_{k+3}+B_n e}) ∈ At_{λ'}`, `Θ_{λ'}(B_n s) = B_n Θ_λ(s)` (no base-data or bound
hypothesis left). -/
theorem skTop0Move (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → e < S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
        Bc.bcB S n (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l')
            (Bc.bcB S n (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
            (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) :=
  fun _ k _ _ _ hR h1 hr hl' hB hec heY IH => by
    obtain ⟨hD, -, hat, hmv⟩ := Xv.xvTop0Move hR h1 hr hl' hB k hec heY IH
    exact ⟨hD, hat, hmv⟩

/-- STATUS: PROVED (Yd.ydInvRef, from Yd.ydAtC, Lw.lw_psi_limit, Bc.bcB_base, Bc.bcB_fix', mvB_lt_iff; NEW round 126;
a REFUTE-FIRST record, no node uses it; checkable only after the merge)
SIZE: S
REFUTED: the inverse correspondence.  At every window and `k`, `F = ψ₂(Ω_{k+3} + c_n)` is an atom of `λ'`,
`B_n(ψ₂(W^X)) = ψ₂(X) < F < ψ₂(W^{X+1})`, and `F ≠ B_n y` for every `y ∈ MvD`. -/
theorem skInvRef (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) ∈ ldAtR S l' ∧
        S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Om (1 + 1)) <
          S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) ∧
        ∀ y, MvD S y → Bc.bcB S n y ≠ S.psi (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcC S n) (Om (1 + 1)) :=
  fun _ k _ _ hR h1 hr hl' hB => by
    obtain ⟨hat, -, hlow, -, hno⟩ := Yd.ydInvRef hR h1 hr hl' hB k
    exact ⟨hat, hlow, hno⟩

/-- STATUS: PROVED (Yd.ydTopB_eq, Yd.ydOwnB_iff, from Yd.ydKeyB, Yd.ydR3B, Yd.ydR3c; NEW round 126; checkable only after
the merge)
SIZE: S
THE PLATEAU AT `Ω₂` over a normal base `β`: `ψ₂(β + W^{X+Ω₂}) = sup_m e_m` (`e_0 = 0`, `e_{m+1} = ψ₂(β + W^{X+e_m})`), and
for EVERY ordinal `e`: `(∀ e' ≤ e, e' < ψ₂(β + W^{X+e'})) ⇔ e < ψ₂(β + W^{X+Ω₂})`. -/
theorem skPlatB (S : InaccSeq.{0}) :
    ∀ (X β : Ordinal.{0}), (∀ a b : Ordinal.{0}, X ∈ S.CSet a b) → β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
      S.psi (β + Le.leWe (X + Om (1 + 1))) (Om (1 + 1)) = ⨆ m : ℕ, Yd.ydEB S X β m ∧
        ∀ e, (∀ e', e' ≤ e → e' < S.psi (β + Le.leWe (X + e')) (Om (1 + 1))) ↔
          e < S.psi (β + Le.leWe (X + Om (1 + 1))) (Om (1 + 1)) :=
  fun _ _ hX hβ => ⟨Yd.ydTopB_eq (fun a b _ => hX a b) hβ, Yd.ydOwnB_iff (fun a b _ => hX a b) hβ⟩

/-- STATUS: PROVED (Yd.ydOwnMoveB, from Yd.ydFixB, Yd.ydNormB, Ug.ugB_fix, Ro.roB_We, Mx.mxB_atom; NEW round 126;
checkable only after the merge)
SIZE: S
THE OWN CLAUSE MOVES: `β` normal in `MvD`, `e ∈ MvD`, `e < ψ₂(β + W^{X+Ω₂})` ⇒ `B_n e < ψ₂(B_n β + W^{X+Ω₂})` and every
ordinal `e'' ≤ B_n e` has `e'' < ψ₂(B_n β + W^{X+e''})` (`X = Ω_{k+3}`; no inverse correspondence). -/
theorem skOwnMove (S : InaccSeq.{0}) :
    ∀ (k n : ℕ) (β e : Ordinal.{0}), MvD S β → β ∈ S.CSet β (S.psi β (Om (1 + 1))) → MvD S e →
      e < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) →
      Bc.bcB S n e <
          S.psi (Bc.bcB S n β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ∧
        ∀ e'', e'' ≤ Bc.bcB S n e →
          e'' < S.psi (Bc.bcB S n β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e'')) (Om (1 + 1)) :=
  fun k n _ _ hDβ hβ hDe he => Yd.ydOwnMoveB k n hDβ hβ hDe he

/-- STATUS: PROVED (Yd.ydBaseMove, from Yd.ydBaseE_iff, Yd.ydLt_top, Yd.ydOwn, Yd.ydFix, Ro.roB_We; NEW round 126;
generalizes skBaseMove0; checkable only after the merge)
SIZE: M
THE BASE-DATA MOVE at the base `0` for EVERY top base `(e, 0)` (`RoBaseE λ X e 0 ⇔ e < ψ₂(W^{X+Ω₂})`): at every window,
under the moves of the codes below `ψ₂(W^{X+e})`, `B_n e` is a code of `λ'`, `(B_n e, 0)` is a top base of `λ'`, and
`B_n(0 + W^{X+e}) = 0 + W^{X+B_n e}`. -/
theorem skBaseMoveAll0 (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e 0 →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n e) ∧
        Ro.RoBaseE S l' (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (Bc.bcB S n e) 0 ∧
        Bc.bcB S n (0 + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) =
          0 + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) :=
  fun _ k _ _ _ hR h1 hr hl' hB hec hb IH => by
    obtain ⟨-, hBec, -, hb', -, hmv⟩ := Yd.ydBaseMove hR h1 hr hl' hB k hec hb IH
    exact ⟨hBec, hb', hmv⟩

/-- STATUS: PROVED (Yd.ydTopMove, from Yd.ydBaseMove, Xv.xvWin, Xq.xqTopMove, Lj.ljTheta_lt_delta; NEW round 126;
generalizes skTop0Move; checkable only after the merge)
SIZE: M
EVERY top atom `s = ψ₂(W^{Ω_{k+3}+e})` over the base `0` (every top base `(e, 0)`) moves at every window under the
premise of WallBelow at `s`: `MvD s`, `B_n s ∈ At_{λ'}`, `Θ_{λ'}(B_n s) = B_n Θ_λ(s)`. -/
theorem skTopMoveAll0 (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e 0 →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
        Bc.bcB S n (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l')
            (Bc.bcB S n (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
            (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) :=
  fun _ k _ _ _ hR h1 hr hl' hB hec hb IH => by
    obtain ⟨hD, -, hat, hmv⟩ := Yd.ydTopMove hR h1 hr hl' hB k hec hb IH
    exact ⟨hD, hat, hmv⟩

/-- The premise of WallBelow at the top atom `ψ₂(β + W^{Ω_{k+3}+e})`, with a top base `(e, β)`, `β ∈ D`, at a window. -/
def TopPrem (S : InaccSeq.{0}) (n k : ℕ) (l l' e β : Ordinal.{0}) : Prop :=
  CdRange S l ∧ Bc.bcC S n < upsilon l ∧ cdR S l < Bc.bcC S (n + 1) ∧
    IsRestartIdx l' ∧ Bc.bcB S n (upsilon l) = upsilon l' ∧
    GxCl (upsilon l) (ldAtR S l) e ∧ Vb.VbD S l β ∧ Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β ∧
    ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)

/-- STATUS: PROVED (Yj.yjBaseFacts, from Yj.yjDvd, Yj.yjD, Yj.yjParts, Ro.roB_We, Ld.ldB_opow, Vb.vbT_move, Rx.rxL_memH,
Rx.rxL_lt_OmW, Yd.ydNormB; round 127: was OPEN; checkable only after the merge.  REFUTE FIRST (round 127) at
`β = Ω₃·2`, `β = Ω₃·ω`: NO EVIDENCE, both are top bases in `D` (Yj.yjNonvac, Yj.yjNonvacW).  Round 126: holds at `β = 0` (`B_n 0 = 0`, `Xi.xiD_zero`) and at
`(e, β) = (0, Ω_{k+3})` at every window (`Yd.ydNonvacW`); none of the no-go results speaks of it.  Off the road: no
node on the road uses it until skWallBase is reduced)
SIZE: M
THE TWO BASE FACTS at `λ'` for a top base `(e, β)`, `β ∈ D`, under the premise of WallBelow at `ψ₂(β + W^{X+e})`:
`W^{X+B_n e} ∣ B_n β` and `B_n β ∈ D_{λ'}`.  Expected route: `β = W^{X+e}·γ` with the move of the Cantor normal form
of `β` (exponents `≥ Ω₂·(X+e)` move to exponents `≥ Ω₂·(X+B_n e)`, `Ld.ldB_opow`, `mvB_add`), and `B_n β = vbK_{λ'}(B_n(T β))`
(`Vb.vbT_move` at `β` with `T = Θ(ψ₂ t)`) with `Rx.rxL_memH` for the hull `Cl(A_{η_λ'}, ρ_λ')` and for `Cl(Ω_ω, θ)`. -/
theorem skBaseFactsB (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β : Ordinal.{0}), TopPrem S n k l l' e β →
      Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Bc.bcB S n e) ∣ Bc.bcB S n β ∧ Vb.VbD S l' (Bc.bcB S n β) := by
  intro n k l l' e β hP
  obtain ⟨hR, h1, hr, hl', hB, hec, hβD, hb, IH⟩ := hP
  exact Yj.yjBaseFacts hR h1 hr hl' hB k hec hβD hb IH

/-- STATUS: PROVED (round 127: was REDUCED; skBaseFactsB now PROVED; = Yj.yjTopMove; Yd.ydTopMoveB, from Yd.ydBaseMoveB, Yd.ydOwnMoveB, Yd.ydNormB, Yd.ydBaseE_lt,
Xq.xqTMove, Xq.xqTopMove; NEW round 126; non-vacuous: Yd.ydNonvacB / ydNonvacW give every hypothesis at
`(e, β) = (0, Ω_{k+3})`; checkable only after the merge)
SIZE: M
EVERY top atom `ψ₂(β + W^{Ω_{k+3}+e})` (every top base `(e, β)`, `β ∈ D`) moves at every window under the premise of
WallBelow at it: `MvD s`, `B_n s = ψ₂(B_n β + W^{X+B_n e}) ∈ At_{λ'}`, `Θ_{λ'}(B_n s) = B_n Θ_λ(s)`. -/
theorem skTopMoveAllB (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β : Ordinal.{0}), TopPrem S n k l l' e β →
      MvD S (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∧
        Bc.bcB S n (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l')
            (Bc.bcB S n (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
            (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)))) :=
  fun n k l l' e β hP => by
    obtain ⟨hdiv', hD'⟩ := skBaseFactsB S n k l l' e β hP
    obtain ⟨hR, h1, hr, hl', hB, hec, hβD, hb, IH⟩ := hP
    obtain ⟨hD, -, hat, hmv⟩ := Yd.ydTopMoveB hR h1 hr hl' hB k hec hβD hb IH hdiv' hD'
    exact ⟨hD, hat, hmv⟩

/-- STATUS: PROVED (Yj.yjBlkMove, from Ld.ldBlk_step at λ and λ', Ld.ldB_psi_add, Ug.ugB_psiS, Mv.mvB_add,
Lj.ljTheta_lt_delta; NEW round 127; checkable only after the merge; non-vacuous: skTopBase gives its hypothesis at
every top atom)
SIZE: M
THE BLOCK MOVE above every base `a` with a law at both ends (`Yj.YjBase`: `Θ(ψ₂ a) = ψ₁(A + D)`, `Θ'(ψ₂(B_n a)) =
ψ₁(A' + B_n D)`, both own): every atom `ψ₂(a + c)`, `c < F^a` a code, moves under the moves of the codes below it. -/
theorem skBlkMove (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D c : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → A' ∈ S.CSet A' (S.psi A' (Om 1)) →
      S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      GxCl (upsilon l) (ldAtR S l) c → c < ldTop S a →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + c) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S (S.psi (a + c) (Om (1 + 1))) ∧ Bc.bcB S n (S.psi (a + c) (Om (1 + 1))) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (a + c) (Om (1 + 1)))) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (a + c) (Om (1 + 1)))) :=
  fun _ _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hb hc hcF IH => by
    obtain ⟨hD, -, hat, hmv⟩ := Yj.yjBlkMove hR h1 hr hl' hB hA' hρ' hb hc hcF IH
    exact ⟨hD, hat, hmv⟩

/-- STATUS: PROVED (Yj.yjBlkNext, from Ld.ldBlk_next at λ and λ', Yj.yjPsi1, Ug.ugB_psiS; NEW round 127; checkable
only after the merge)
SIZE: S
THE NEXT BASE: for a base `a` with a law at both ends (`a + Ω₂ < Ω_ω`), `F^a = ψ₂(a + Ω₂)` moves (no move of lower codes
needed) and `a + Ω₂` is again a base with a law at both ends, image `D + Ω₁`, `B_n(a + Ω₂) = B_n a + Ω₂`. -/
theorem skBlkNext (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → A' ∈ S.CSet A' (S.psi A' (Om 1)) →
      S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D → a + Om (1 + 1) < Om ω →
      MvD S (ldTop S a) ∧ Bc.bcB S n (ldTop S a) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (ldTop S a)) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (ldTop S a)) ∧
        Yj.YjBase S n l l' A' (a + Om (1 + 1)) (D + Om 1) :=
  fun _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hb hW => by
    obtain ⟨hD, -, hat, hmv, hb', -⟩ := Yj.yjBlkNext hR h1 hr hl' hB hA' hρ' hb hW
    exact ⟨hD, hat, hmv, hb'⟩

/-- STATUS: PROVED (Yj.yjTopBase, from Yj.yjBaseFacts, Yd.ydBaseMoveB, Xq.xqTopD, Xq.xqTMove, Xq.xqSigMove, Xq.xqOwn,
Xm.xmTopUp at λ and λ'; NEW round 127; checkable only after the merge)
SIZE: M
EVERY TOP ATOM IS A BASE WITH A LAW AT BOTH ENDS: under the premise of WallBelow at `ψ₂ t`, `t = β + W^{Ω_{k+3}+e}`,
`Yj.YjBase λ λ' A' t (1 + ψ₂(T t))` and `B_n t = B_n β + W^{X+B_n e}`. -/
theorem skTopBase (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β A' : Ordinal.{0}), TopPrem S n k l l' e β → A' ∈ S.CSet A' (S.psi A' (Om 1)) →
      S.psi A' (Om 1) = upsilon l' →
      Yj.YjBase S n l l' A' (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))
        (1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) :=
  fun _ k _ _ _ _ _ hP hA' hρ' => by
    obtain ⟨hR, h1, hr, hl', hB, hec, hβD, hb, IH⟩ := hP
    exact (Yj.yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hb IH).1

/-- STATUS: PROVED (Yj.yjTopBlk, from Yj.yjTopBase, Yj.yjBlkFin, Yj.yjBlkBase, Yj.yjBlkNext, Yj.yjBlkMove; NEW round 127;
checkable only after the merge; non-vacuous: the λ-side hypotheses hold at `(e, β) = (0, Ω_{k+3}·j)`, Yj.yjNonvac)
SIZE: M
THE NON-TOP ATOMS OF THE FIRST ω BLOCKS above every top atom `t = β + W^{Ω_{k+3}+e}` move: every atom
`ψ₂(t + Ω₂·m + c)`, `m < ω`, `c < F^{t+Ω₂·m}` a code of `λ`, at a window, under the moves of the codes below it. -/
theorem skTopBlkFin (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β A' : Ordinal.{0}) (m : ℕ) (c : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      GxCl (upsilon l) (ldAtR S l) c →
      c < ldTop S (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0})) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
          (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
          (Om (1 + 1))) ∧
        Bc.bcB S n (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
          (Om (1 + 1))) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n
            (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
              (Om (1 + 1)))) =
          Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
            (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Om (1 + 1) * (m : Ordinal.{0}) + c)
              (Om (1 + 1)))) :=
  fun _ k _ _ _ _ _ m _ hR h1 hr hl' hB hA' hρ' hec hβD hb hc hcF IH =>
    Yj.yjTopBlk hR h1 hr hl' hB hA' hρ' k hec hβD hb m hc hcF IH

/-- STATUS: PROVED (Yt.ytTestOm, Yt.ytTestSq, from Yt.ytTestBase, Yt.ytLaw, Le.leOwnRead, Yt.ytBaseE, Xi.xiTopUp0;
NEW round 129; a REFUTE-FIRST record, no node uses it; checkable only after the merge)
SIZE: S
At every restart `λ` and own `A` with `ψ₁(A) = ρ_λ`, `t = W^{Ω₃}`, `Â = A + 1 + ψ₂(T t)`:
`Θ(ψ₂(t + Ω₂·ω)) = ψ₁(Â + Ω₁·ω)`, `Θ(ψ₂(t + Ω₂·(ω+1))) = ψ₁(Â + Ω₁·(ω+1))`, `Θ(ψ₂(t + W^2)) = ψ₁(Â + Ω^2)`. -/
theorem skRefTests (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx → A ∈ S.CSet A (S.psi A (Om 1)) →
      S.psi A (Om 1) = upsilon l →
      gxTh (upsilon l) (ldAtR S l)
          (S.psi (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + Om (1 + 1) * ω) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) +
          Om 1 * ω) (Om 1) ∧
      gxTh (upsilon l) (ldAtR S l)
          (S.psi (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0) + (Le.leWe (1 + 1) * 1 + 0))
            (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (0 + Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 0))) (Om (1 + 1)) +
          (Le.leOe (1 + 1) * 1 + 0)) (Om 1) :=
  fun _ _ _ hl hX hA hρ => ⟨(Yt.ytTestOm hl hX hA hρ).1, Yt.ytTestSq hl hX hA hρ⟩

/-- STATUS: PROVED (Yt.ytTopMoveY, from Yt.ytUxMove, Yt.ytRepU, Ux.uxClsLev_all, Uu.uuOwnRead, Uu.uuDigMove,
Ux.uxShG_B, Uu.uuBase_lower, Yj.yjTopBase, Yj.yjBaseFacts, Yj.yjBlkMove, Yj.yjPsi1; NEW round 129; replaces the
open items (a) and (b) for every offset below `Y₃`; supersedes Yt.ytTopMoveG (`s < ψ₂(t + Ω₂²)`) and Yt.ytTopMoveW
(`s < ψ₂(t + W^{Ω₂})`); non-vacuous: the λ-side hypotheses hold at `(e, β) = (0, Ω_{k+3}·j)` (Yj.yjNonvac);
checkable only after the merge)
SIZE: M
EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + Y₃)` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` (top base `(e, β)`, `β ∈ D`, every `k`)
moves at every window under the premise of WallBelow at `s`. -/
theorem skTopMoveY (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β A' s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      s ∈ ldAtR S l → S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s →
      s < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Ug.ugY S) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ k _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hec hβD hb hs hst hsY IH =>
    Yt.ytTopMoveY hR h1 hr hl' hB hA' hρ' k hec hβD hb hs hst hsY IH

/-- STATUS: PROVED (Yt.ytSubLaw, from Xm.xmTopUp at the sub-bases Yt.ytBaseSub, Yt.ytT_sub, Xd.xdUp_at, Lw.lw_psi_limit,
Xm.xmTh_lim; the layer bound Yt.ytKe_sup through Vk.vkPsi2_le, Vk.vkA_mod, Vk.vkA_boundY; NEW round 129; checkable
only after the merge)
SIZE: M
THE LAW AT A SUB-BASE WITH A LIMIT COEFFICIENT: `Θ(ψ₂(β + W^{X+e}·γ)) = ψ₁(A + 1 + ψ₂(T(β + W^{X+e}·γ)))` for every
base `(e + 1, β)`, `β ∈ D`, every limit code `γ < T_{X+e+1}(β)`, `X = Ω_{k+3}`. -/
theorem skSubLawLim (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A e β γ : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β →
      GxCl (upsilon l) (ldAtR S l) γ → γ < Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β →
      IsSuccLimit γ →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ)) (Om (1 + 1)))
          (Om 1) :=
  fun k _ _ _ _ _ _ hl hX hA hρ hec hβD hb hγ hγT hlim => Yt.ytSubLaw hl hX hA hρ k hec hβD hb hγ hγT hlim

/-- STATUS: PROVED (Yt.ytSubBase, from Yt.ytSubLaw at λ and λ', Yt.ytDvdE, Yt.ytB_lim, Yt.ytBaseSub, Yd.ydBaseMoveB,
Yj.yjBaseFacts, Xq.xqTMove, Xq.xqSigMove, Xq.xqOwn, Ro.roB_We; NEW round 129; checkable only after the merge)
SIZE: M
EVERY SUB-BASE `a = β + W^{X+e}·γ` WITH A LIMIT CODE `γ` IS A BASE WITH A LAW AT BOTH ENDS (`Yj.YjBase λ λ' A' a
(1 + ψ₂(T a))`, `B_n a = B_n β + W^{X+B_n e}·B_n γ`) under the premise of WallBelow at `ψ₂(a)`. -/
theorem skSubBaseLim (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β γ A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β →
      GxCl (upsilon l) (ldAtR S l) γ → γ < Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β →
      IsSuccLimit γ →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x →
        x < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      Yj.YjBase S n l l' A' (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ)
        (1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ)) (Om (1 + 1))) :=
  fun _ k _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hec hβD hb hγ hγT hlim IH =>
    (Yt.ytSubBase hR h1 hr hl' hB hA' hρ' k hec hβD hb hγ hγT hlim IH).1

/-- STATUS: PROVED (Yt.ytSubMove, from Yt.ytSubBase, Yt.ytUxMove; NEW round 129; checkable only after the merge)
SIZE: M
EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Y₃)` ABOVE EVERY SUB-BASE `a = β + W^{X+e}·γ` (`γ` a limit code) MOVES at every
window under the premise of WallBelow at `s`. -/
theorem skSubMoveY (S : InaccSeq.{0}) :
    ∀ (n k : ℕ) (l l' e β γ A' s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β → Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β →
      GxCl (upsilon l) (ldAtR S l) γ → γ < Le.leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β →
      IsSuccLimit γ → s ∈ ldAtR S l →
      S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1)) ≤ s →
      s < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ + Ug.ugY S) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ k _ _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hec hβD hb hγ hγT hlim hs hsa hsY IH =>
    Yt.ytSubMove hR h1 hr hl' hB hA' hρ' k hec hβD hb hγ hγT hlim hs hsa hsY IH

/-- STATUS: PROVED (Yy.yyTestY3, Yy.yyTestY3two, Yy.yyTestG3, Yy.yyTestOm2_wit, Yy.yyG3_two_lt, from Yy.yyTopMoveY3W,
Yy.yyLawOm2; NEW round 130; checkable only after the merge)
SIZE: S
REFUTE-FIRST records: `ψ₃(0)·2 < Y₃`, and at `m* = L(0)` with its own `A`: `Θ(ψ₂(W^{Ω_{k+3}+Ω₂})) =
ψ₁(A + 1 + ψ₂(Ω^{Ω_{k+2}+Ω₁}))` (the law (2') at `E = Ω₂`, `β = 0`); the moves at `δ = Y₃`, `Y₃·2`, `ψ₃(0)·2` over `Ω₃`
are `Yy.yyTestY3`, `Yy.yyTestY3two`, `Yy.yyTestG3` (window hypotheses, not restated here). -/
theorem skRefTests130 (S : InaccSeq.{0}) :
    S.psi 0 (Om (1 + 1 + 1)) * 2 < Ug.ugY S ∧
      ∀ k : ℕ, ∃ l A : Ordinal.{0}, IsRestartIdx l ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧ S.psi A (Om 1) = upsilon l ∧
        gxTh (upsilon l) (ldAtR S l)
            (S.psi (Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (Le.leOe (Om ((k : Ordinal.{0}) + 1 + 1) + Om 1)) (Om (1 + 1))) (Om 1) :=
  ⟨Yy.yyG3_two_lt, fun k => Yy.yyTestOm2_wit S k⟩

/-- STATUS: PROVED (Yy.yyPlat, from Yy.yyKey, Yy.yyR2, Yy.yyR3, Yy.yyStep; NEW round 130; checkable only after the merge)
SIZE: M
THE PLATEAU IN THE EXPONENT: `ψ₁(B + ψ₂(b + Ω^{K+Ω₁})) ≤ sup_n x_n`, `x_{n+1} = ψ₁(B + ψ₂(b + Ω^{K+x_n}))`, for `b`
normal at `Ω₂`, `K` in every closure, `x_0 ≤ x_1`, `x_0 < Ω₁`. -/
theorem skPlatExp (S : InaccSeq.{0}) {B b K x0 : Ordinal.{0}} (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1))))
    (hK : ∀ a c : Ordinal.{0}, K ∈ S.CSet a c) (h0 : x0 ≤ Yy.yyX S B b K x0 1) (hx0 : x0 < Om 1) :
    S.psi (B + S.psi (b + Le.leOe (K + Om 1)) (Om (1 + 1))) (Om 1) ≤ ⨆ n : ℕ, Yy.yyX S B b K x0 n :=
  Yy.yyPlat hb (fun _ => hK _ _) h0 hx0 (fun _ => hK _ _)

/-- STATUS: PROVED (Yy.yyLawOm2, from Yy.yyItBase, Xm.xmTopUp at the iterates `e^β_m`, Yt.ytT_sub, Yy.yyPlat, Yy.yyTW,
Xd.xdUp_at; NEW round 130; checkable only after the merge)
SIZE: M
(2') AT THE FIRST NON-CODE EXPONENT: `restart λ, A own, ψ₁(A) = ρ_λ, β ∈ D normal, ∀ m, W^{X+e^β_m} ∣ β ⇒
Θ(ψ₂(β + W^{X+Ω₂})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+Ω₂})))`, and `T(β + W^{X+Ω₂}) = T β + Ω^{Ω_{k+2}+Ω₁}`. -/
theorem skTopLawOm2 (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A β : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → Vb.VbD S l β →
      β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
      (∀ m, Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Yd.ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Vb.vbT S l (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))))
          (Om (1 + 1))) (Om 1) :=
  fun k _ _ _ _ hl hX hA hρ hβD hβn hdv => Yy.yyLawOm2 hl hX hA hρ k hβD hβn hdv

/-- STATUS: PROVED (Yy.yyTopMoveOm2Y, from Yy.yyTopBaseOm2 (law at both ends: Yy.yyLawOm2 at λ and λ', base data at
λ' from Yj.yjBaseFacts at the iterates and Yd.ydFixB), Yy.yyY3MoveW; also Yy.yyTopMoveOm2 (the atom itself); NEW round
130; checkable only after the merge)
SIZE: M
every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+1})` above the first non-code top `t = β + W^{X+Ω₂}` moves at every window under
the premise of WallBelow at `s` (`β ∈ D` normal, `W^{X+e^β_m} ∣ β`). -/
theorem skTopMoveOm2Y (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (β s : Ordinal.{0}), Vb.VbD S l β → β ∈ S.CSet β (S.psi β (Om (1 + 1))) →
      (∀ m, Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Yd.ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β) →
      s ∈ ldAtR S l →
      S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ≤ s →
      s < Le.leTe S (Ug.ugY S + 1) (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ hβD hβn hdv hs hst hsT IH =>
    Yy.yyTopMoveOm2Y hR h1 hr hl' hB hA' hρ' k hβD hβn hdv hs hst hsT IH

/-- STATUS: PROVED (Yy.yyY3MoveW, from Yy.yyBaseY3G (Vq.vqSh_Y3_rst, Vq.vqTopY3, Vq.vqStepA at λ and λ', Vk.vkTe_gt,
Ld.ldB_mulK, Mx.mxB_atom), Yy.yyT_le, Yt.ytUxMove; NEW round 130; checkable only after the merge)
SIZE: M
THE ψ₃-OFFSETS BELOW `W^{Y₃+1} = Y₃·Ω₂`: above every base `a ≥ Ω₃` with a law at both ends, `W^{Y₃+1} ∣ a`,
`W^{Y₃+1} ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+1})` moves under the premise of WallBelow at `s`. -/
theorem skY3MoveW (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (a D s : Ordinal.{0}), Yj.YjBase S n l l' A' a D → Le.leWe (Ug.ugY S + 1) ∣ a →
      Le.leWe (Ug.ugY S + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi a (Om (1 + 1)) ≤ s → s < Le.leTe S (Ug.ugY S + 1) a →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' _ _ _ hb hd hd' h3 hs hsa hsT IH =>
    Yy.yyY3MoveW hR h1 hr hl' hB hA' hρ' hb hd hd' h3 hs hsa hsT IH

/-- STATUS: PROVED (Yy.yyTopMoveY3W, from Yj.yjTopBase, Yj.yjBaseFacts, Yy.yyY3MoveW; NEW round 130; supersedes
skTopMoveY; checkable only after the merge)
SIZE: S
above every top atom `t = β + W^{Ω_{k+3}+e}` every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+1})` moves under the premise of
WallBelow at `s`. -/
theorem skTopMoveY3W (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (e β s : Ordinal.{0}), GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β → s ∈ ldAtR S l →
      S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s →
      s < Le.leTe S (Ug.ugY S + 1) (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ _ hec hβD hbe hs hst hsT IH =>
    Yy.yyTopMoveY3W hR h1 hr hl' hB hA' hρ' k hec hβD hbe hs hst hsT IH

/-- STATUS: PROVED (Yy.yyPsi3OffLow, from Yy.yyBaseSmall (Vn.vnNoSelf), Vn.vnPsi2_eq; NEW round 130; checkable only after
the merge)
SIZE: S
skPsi3Off below `Ω₃`: a base `a < Ω₃` normal at `Ω₂` with `Y₃ ∣ a` is `0`, and `[ψ₂(Y₃), ψ₂(Ω₃))` is empty. -/
theorem skPsi3OffLow (S : InaccSeq.{0}) :
    ∀ (a s : Ordinal.{0}), a ∈ S.CSet a (S.psi a (Om (1 + 1))) → Ug.ugY S ∣ a → a < Om (1 + 1 + 1) →
      S.psi (a + Ug.ugY S) (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) → False :=
  fun _ _ ha hY ha3 hs1 hs2 => Yy.yyPsi3OffLow ha hY ha3 hs1 hs2

/-- STATUS: OPEN (NEW round 130; REFUTE FIRST: NO EVIDENCE — the points `δ = Y₃`, `Y₃·2` over `Ω₃` hold (skRefTests130);
the part `s < ψ₂(a + Y₃·ω)` is PROVED for every such base (Yy.yyY3Move, from the step Yy.yyY3Step: `a + Y₃` is
again a base with a law at both ends, image `D + Y₂`), the part `s < ψ₂(a + W^{Y₃+1})` when `W^{Y₃+1} ∣ a`,
`W^{Y₃+1} ∣ B_n a` (skY3MoveW))
SIZE: L
skPsi3Off at the bases `a ≥ Ω₃`.  Still missing, in order: (i) the bases `a` with `Y₃ ∣ a` but `W^{Y₃+1} ∤ a` (the
classification of `a` by its last `W`-exponent, as `Yt.ytRepU` does below `Y₃`), (ii) the offsets
`W^{Y₃+1} ≤ δ < W^{Y₃+Ω₂}`: the sub-bases `a + W^{Y₃+e}·γ` for every code `e` (`Vq.vqTopY3E`, `Vq.vqStepA` at `e`;
the λ'-side needs `RoBaseE λ' Y₃ (B_n e + 1) (B_n a)`, i.e. the own-clause move of `Yd.ydOwnMoveB` for the shift `Y₃`,
whose `Yd.ydKeyB` asks `X` in EVERY closure, false for `Y₃`), (iii) the offsets `δ ≥ W^{Y₃+Ω₂}` (`Vq.vqTopY3W`, then
shifts `X ∈ (Y₃ + Ω₂, Ω₃)`: no Lean shift past `Y₃ + Ω₂` exists; `Vq.vqNoSh`: no self-relative shift in `[Y₃, Ω₃)`).
(round 131: for `Ω₃`-divisible bases (the case the assembly needs) the part `s < ψ₂(a + W^{Y₃+Ω₂·ε₀})` is PROVED
(skPsi3OffE0), and for every base with `W^{Y₃+e} ∣ a`, `W^{Y₃+B_n e} ∣ B_n a` the part `s < ψ₂(a + W^{Y₃+e})`
(`Zd.zdY3Up`); the parts (ii), (iii) up to `Y₃ + Ω₂·ε₀` are done; (i) — bases with only `Y₃ ∣ a` — is not needed by
skPsi3OffD and stays OPEN with the rest of (iii).) -/
theorem skPsi3OffHi (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Ug.ugY S ∣ a → Ug.ugY S ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi (a + Ug.ugY S) (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  sorry

/-- STATUS: REDUCED (skPsi3OffLow, skPsi3OffHi; round 130: was OPEN; REFUTE FIRST: NO EVIDENCE, skRefTests130)
SIZE: L
THE ψ₃-ATOM OFFSETS: above every base `a` with a law at both ends (`Yj.YjBase`) with `Y₃ ∣ a` and `Y₃ ∣ B_n a`, every
atom `ψ₂(a + Y₃) ≤ s < ψ₂(a + Ω₃)` moves at every window under the premise of WallBelow at `s`.  Statement unchanged.
Proof: `a < Ω₃` is impossible unless the region is empty (skPsi3OffLow); `a ≥ Ω₃` is skPsi3OffHi. -/
theorem skPsi3Off (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Ug.ugY S ∣ a → Ug.ugY S ∣ Bc.bcB S n a → s ∈ ldAtR S l →
      S.psi (a + Ug.ugY S) (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hY hY' hs hs1 hs2 IH
  rcases lt_or_ge a (Om (1 + 1 + 1)) with ha | ha
  · have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
    exact (skPsi3OffLow S a s han hY ha hs1 hs2).elim
  · exact skPsi3OffHi S n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hY hY' ha hs hs1 hs2 IH

/-- STATUS: PROVED (Zd.zdTestOm2p1, Zd.zdTestPsi3W2, from Zd.zdTestNV, Zd.zdChain, Zd.zdTopMoveY3E0; NEW round 131; the
REFUTE-FIRST records of (a) and (b); checkable only after the merge)
SIZE: S
(b) at `E = Ω₂ + 1`: `Θ(ψ₂(W^{Ω₃+Ω₂+1})) = ψ₁(A + 1 + ψ₂(Ω^{Ω₂+Ω₁+1}))` at the restart of `m*`; (a) at `δ = W^{Y₃+1}·2`
over `a = Ω₃ + Y₃`: `W^{Y₃+1} ∤ a`, `a + δ = Ω₃ + W^{Y₃+1}·2`, and that atom moves at every window under IH. -/
theorem skRefTests131 (S : InaccSeq.{0}) :
    (∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Nm.Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l)
          (S.psi (Le.leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1) + 1)) (Om (1 + 1))) =
        S.psi (A + 1 + S.psi (Le.leOe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1) + Om 1 + 1)) (Om (1 + 1))) (Om 1)) ∧
    (∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ¬ Le.leWe (Ug.ugY S + 1) ∣ Om (1 + 1 + 1) + Ug.ugY S ∧
        Om (1 + 1 + 1) + Ug.ugY S + Le.leWe (Ug.ugY S + 1) * 2 = Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2 ∧
        (S.psi (Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2) (Om (1 + 1)) ∈ ldAtR S l →
          (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
          MvD S (S.psi (Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2) (Om (1 + 1))) ∧
            Bc.bcB S n (S.psi (Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2) (Om (1 + 1))) ∈ ldAtR S l' ∧
            gxTh (upsilon l') (ldAtR S l')
                (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2) (Om (1 + 1)))) =
              Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
                (S.psi (Om (1 + 1 + 1) + Le.leWe (Ug.ugY S + 1) * 2) (Om (1 + 1)))))) :=
  ⟨Zd.zdTestOm2p1 S, fun _ _ _ _ hR h1 hr hl' hB hA' hρ' => Zd.zdTestPsi3W2 hR h1 hr hl' hB hA' hρ'⟩

/-- STATUS: PROVED (Zd.zdChain, from Zd.zdSucc, Zd.zdLim, Zd.zdTopUp, Zd.zdLawW, Zd.zdNext, Zd.zdLimSh, Zd.zdSh_chain,
Xm.xmTopUp, Yy.yyPlat; NEW round 131; checkable only after the merge)
SIZE: M
(b) THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`, `ξ < ε₀`, `e` a code: at every restart with own `A`, for every
base `β ∈ D` of exponent `e` of the shift `X_ξ = Ω_{k+3} + Ω₂·ξ`:
`Θ(ψ₂(β + W^{X_ξ+e})) = ψ₁(A + 1 + ψ₂(T(β + W^{X_ξ+e})))` (and `T(β + W^{X_ξ+e}) = T β + Ω^{Ω_{k+2}+Ω₁·ξ+Θe}`,
`Zd.zdT_top`).  `ξ = 0` is skTopUp, `ξ = 1`, `e = 0` is skTopLawOm2. -/
theorem skTopLawChain (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ∀ ξ, ξ < ε₀ → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, Vb.VbD S l β →
        Ro.RoBaseE S l (Zd.zdX k ξ) e β → Zd.ZdLaw S l A (Zd.zdX k ξ) e β :=
  fun k _ _ _ hl hX hA hρ => Zd.zdChain hl hX hA hρ k

/-- STATUS: PROVED (Zd.zdTopBase, from Zd.zdBaseFacts, Zd.zdBaseMoveB, Zd.zdTopD, Zd.zdOwnMoveB, Zd.zdFixB, Zd.zdDvd,
Zd.zdD, Xq.xqTMove, Xq.xqSigMove, Xq.xqOwn, Zd.zdMv_chain, Zd.zdHL_chain; NEW round 131; checkable only after the merge)
SIZE: M
Every top atom `t = β + W^{X_ξ+e}` (`ξ < ε₀`) is a base with a law at both ends: `Yj.YjBase λ λ' A' t (1 + ψ₂(T t))`,
`B_n t = B_n β + W^{X_ξ+B_n e}`, at every window under IH below `ψ₂ t`. -/
theorem skTopBaseChain (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (ξ e β : Ordinal.{0}), ξ < ε₀ → GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Zd.zdX k ξ) e β →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      Yj.YjBase S n l l' A' (β + Le.leWe (Zd.zdX k ξ + e))
          (1 + S.psi (Vb.vbT S l (β + Le.leWe (Zd.zdX k ξ + e))) (Om (1 + 1))) ∧
        Bc.bcB S n (β + Le.leWe (Zd.zdX k ξ + e)) = Bc.bcB S n β + Le.leWe (Zd.zdX k ξ + Bc.bcB S n e) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ _ hξ hec hβD hbe IH =>
    Zd.zdTopBase (Zd.zdMv_chain k hξ) hR h1 hr hl' hB (Zd.zdHL_chain k hξ) hA' hρ' hec hβD hbe IH

/-- STATUS: PROVED (Zd.zdTopMove, from Zd.zdBaseMoveB, Zd.zdTopD, Xq.xqLawMove, Zd.zdChain at λ and λ'; NEW round 131;
checkable only after the merge)
SIZE: M
Every top atom `ψ₂(β + W^{X_ξ+e})` (`ξ < ε₀`) MOVES at every window under IH below it (no further hypothesis). -/
theorem skTopMoveChain (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      ∀ (k : ℕ) (ξ e β : Ordinal.{0}), ξ < ε₀ → GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Zd.zdX k ξ) e β →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1)) → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S (S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1))) ∧ Bc.bcB S n (S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1))) = S.psi (Bc.bcB S n β + Le.leWe (Zd.zdX k ξ + Bc.bcB S n e)) (Om (1 + 1)) ∧
        Bc.bcB S n (S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1))) ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1)))) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1)))) :=
  fun _ _ _ hR h1 hr hl' hB k _ _ _ hξ hec hβD hbe IH =>
    Zd.zdTopMove (Zd.zdMv_chain k hξ) hR h1 hr hl' hB (Zd.zdHL_chain k hξ) hec hβD hbe IH

/-- STATUS: PROVED (Zd.zdPsi3OffE0, from Zd.zdBot_chain, Zd.zdXUp, Zd.zdBaseXE, Zd.zdRS_chain, Zd.zdTop_chainR,
Zd.zdVqSh_chain, Zd.zdOwnBr_iff, Zd.zdOwnMoveBr, Vq.vqStepA, Vq.vqTopW, Vq.vqTopLimSh, Vq.vqTopE, Vb.vbReach,
Yt.ytUxMove; NEW round 131; checkable only after the merge)
SIZE: M
(a) THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·ε₀}`: above every base `a ≥ Ω₃` with a law at both ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, every
atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·ε₀})` moves at every window under IH(s). -/
theorem skPsi3OffE0 (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Om (1 + 1 + 1) ∣ a → Om (1 + 1 + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa hsT IH =>
    Zd.zdPsi3OffE0 hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa hsT IH

/-- STATUS: PROVED (Zd.zdTopMoveY3E0, from Yj.yjTopBase, Yj.yjBaseFacts, Zd.zdPsi3OffE0; NEW round 131; supersedes
skTopMoveY3W; checkable only after the merge)
SIZE: M
Every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·ε₀})` above every top atom `t = β + W^{Ω_{k+3}+e}` moves (window, IH(s)). -/
theorem skTopMoveY3E0 (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (e β s : Ordinal.{0}), GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β → s ∈ ldAtR S l →
      S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s →
      s < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ _ hec hβD hbe hs hst hsT IH =>
    Zd.zdTopMoveY3E0 hR h1 hr hl' hB hA' hρ' k hec hβD hbe hs hst hsT IH

/-- STATUS: PROVED (Zd.zdTopMoveChainY3E0, from Zd.zdTopBase, Zd.zdBaseFacts, Zd.zdPsi3OffE0; NEW round 131; checkable
only after the merge)
SIZE: M
Every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·ε₀})` above every top atom `t = β + W^{X_ξ+e}` (`ξ < ε₀`) moves. -/
theorem skTopMoveChainY3E0 (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (ξ e β s : Ordinal.{0}), ξ < ε₀ → GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Zd.zdX k ξ) e β → s ∈ ldAtR S l → S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1)) ≤ s →
      s < S.psi (β + Le.leWe (Zd.zdX k ξ + e) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ _ _ hξ hec hβD hbe hs hst hsT IH =>
    Zd.zdTopMoveChainY3E0 hR h1 hr hl' hB hA' hρ' k hξ hec hβD hbe hs hst hsT IH

/-- STATUS: PROVED (Zi.ziTestE0, Zi.ziTestY3two, Zi.ziTestOm3, from Zi.ziRS_cst, Zi.ziTopMoveWK, Zi.ziPlat3,
Zi.ziU_one_Om3, Zi.ziY3_gt_chain; NEW round 132; the REFUTE-FIRST records of (a) and (b); checkable only after the merge)
SIZE: S
(a) at `Y₃·2`: `Y₃·2 = Y₃ + Ω₂·Ω₂·Y₃`, past `W^{Y₃+Ω₂·Ω₂·Ω₂}` and past `W^{Y₃+Ω₂·Ω₂·K₃}`, `B_n` fixes `Y₃`;
(b) at `E = Ω₃`: `ψ₂(W^{Ω₃+Ω₃}) = sup_m ψ₂(W^{Ω₃+u_m})` with `u_m ∈ [Y₃, Ω₃)` above every chain exponent
`Ω₂·ξ + e`; (a) at `Y₃ + Ω₂·ε₀`: a fixed relative shift with image `Y₂ + Ω₁·ε₀`, and the atom `ψ₂(Ω₃ + W^{Y₃+Ω₂·ε₀})`
moves at every window under IH. -/
theorem skRefTests132 (S : InaccSeq.{0}) :
    (Ug.ugY S * 2 = Zi.ziPP S (Ug.ugY S) ∧ Zi.ziPP S (Om (1 + 1)) ≤ Ug.ugY S * 2 ∧
      Zi.ziPP S (Zi.ziK3 S) < Ug.ugY S * 2 ∧ ∀ n : ℕ, Bc.bcB S n (Ug.ugY S) = Ug.ugY S) ∧
    (S.psi (Le.leWe (Om (1 + 1 + 1) + Om (1 + 1 + 1))) (Om (1 + 1)) =
        ⨆ m : ℕ, S.psi (Le.leWe (Om (1 + 1 + 1) + Zi.ziU S (Om (1 + 1 + 1)) 0 m)) (Om (1 + 1)) ∧
      (∀ m : ℕ, Ug.ugY S ≤ Zi.ziU S (Om (1 + 1 + 1)) 0 (m + 1) ∧ Zi.ziU S (Om (1 + 1 + 1)) 0 (m + 1) < Om (1 + 1 + 1)) ∧
      ∀ ξ e : Ordinal.{0}, ξ < Om (1 + 1) → e < Om (1 + 1) → Om (1 + 1) * ξ + e < Ug.ugY S) ∧
    (Zd.ZdRS S (Zd.zdXr S ε₀) (Zd.zdXhr S ε₀) ∧
      ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      (S.psi (Om (1 + 1 + 1) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)) ∈ ldAtR S l →
        (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (Om (1 + 1 + 1) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)) → MvD S x ∧
          GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
          gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
        MvD S (S.psi (Om (1 + 1 + 1) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1))) ∧ Bc.bcB S n (S.psi (Om (1 + 1 + 1) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1))) ∈ ldAtR S l' ∧
          gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (Om (1 + 1 + 1) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)))) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (Om (1 + 1 + 1) + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)))))) :=
  ⟨Zi.ziTestY3two, Zi.ziTestOm3, Zi.ziRS_cst (Zi.ziEps0_lt_G.trans_le Zi.ziG_le_K3),
    fun _ _ _ _ hR h1 hr hl' hB hA' hρ' => (Zi.ziTestE0 hR h1 hr hl' hB hA' hρ').2⟩

/-- STATUS: PROVED (Zi.ziPlat3, from Zi.ziKeyU, Zi.ziR3U; NEW round 132; checkable only after the merge)
SIZE: S
THE LEVEL-3 PLATEAU: `ψ₂(β + W^{X+Ω₃}) = sup_m ψ₂(β + W^{X+u_m})`, `u_0 = 0`, `u_{m+1} = ψ₃(β + W^{X+u_m})`, for
every `β`, `X` (the top atoms at exponents `E ≥ Ω₃` reduce to exponents below `Ω₃`). -/
theorem skPlat3 (S : InaccSeq.{0}) :
    ∀ X β : Ordinal.{0}, S.psi (β + Le.leWe (X + Om (1 + 1 + 1))) (Om (1 + 1)) =
      ⨆ m : ℕ, S.psi (β + Le.leWe (X + Zi.ziU S X β m)) (Om (1 + 1)) :=
  fun X β => Zi.ziPlat3 X β

/-- STATUS: PROVED (Zi.ziRSPlat, from Zi.ziStepTop0, Zi.ziStepVqSh, Zi.ziStepShB, Zi.ziPlatO, Zi.ziPlatC, Zi.ziTopC,
Vq.vqTopE; NEW round 132; checkable only after the merge)
SIZE: M
THE PLATEAU SHIFT IS A FIXED RELATIVE SHIFT: `(P, P̂)` a fixed relative shift ⇒ `(P + Ω₂·Ω₂, P̂ + Ω₁·Ω₁)` is one; in
particular `Θ(ψ₂(β + W^{P+Ω₂·Ω₂})) = ψ₁(Â + Ω^{P̂+Ω₁·Ω₁})` at every base `β ≥ Ω₃` of exponent `0`. -/
theorem skRSPlat (S : InaccSeq.{0}) :
    ∀ P Pt : Ordinal.{0}, Zd.ZdRS S P Pt → Zd.ZdRS S (Zi.ziXp P (Om (1 + 1))) (Zi.ziXhp Pt (Om 1)) :=
  fun _ _ hP => Zi.ziRSPlat hP

/-- STATUS: PROVED (Zi.ziBotPlat, from Zi.ziBotC, Zi.ziRSC, Zi.ziXUpM, Zi.ziBaseXM, Zi.ziTopC, Zi.ziOwnC_iff,
Zi.ziTC_move; NEW round 132; checkable only after the merge)
SIZE: M
THE MOVES BELOW THE PLATEAU SHIFT: for a fixed relative shift `P`, the moves below `P` give the moves below
`P + Ω₂·Ω₂` (over every base `a ≥ Ω₃` with `W^{P+Ω₂·Ω₂} ∣ a`, `W^{P+Ω₂·Ω₂} ∣ B_n a`); the code coefficients `ξ` of
`P + Ω₂·ξ` move under `B_n`. -/
theorem skBotPlat (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ P Pt : Ordinal.{0}, Zd.ZdRS S P Pt → Zd.ZdBot S n l l' A' P → Zd.ZdBot S n l l' A' (Zi.ziXp P (Om (1 + 1))) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' _ _ hP HB => Zi.ziBotPlat hR h1 hr hl' hB hA' hρ' hP HB

/-- STATUS: PROVED (Zi.ziChain, from Zi.ziSh_cst, Zi.ziLimSh, Zd.zdNext, Zd.zdTopUp, Xm.xmTopUp; NEW round 132;
checkable only after the merge)
SIZE: M
(b) THE TOP LAW AT EVERY EXPONENT `Ω_{k+3} + Ω₂·ξ + e`, `ξ < ψ_{Ω₁}(0)` (contains skTopLawChain). -/
theorem skTopLawCst (S : InaccSeq.{0}) :
    ∀ (k : ℕ) (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ∀ ξ, ξ < Zi.ziG S → ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, Vb.VbD S l β →
        Ro.RoBaseE S l (Zd.zdX k ξ) e β → Zd.ZdLaw S l A (Zd.zdX k ξ) e β :=
  fun k _ _ _ hl hX hA hρ => Zi.ziChain hl hX hA hρ k

/-- STATUS: PROVED (Zi.ziTopMoveWK, from Yj.yjTopBase, Yj.yjBaseFacts, Zi.ziPsi3OffWK; NEW round 132; supersedes
skTopMoveY3E0; checkable only after the merge)
SIZE: M
Every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·Ω₂·K₃})` above every top atom `t = β + W^{Ω_{k+3}+e}` moves (window, IH(s)). -/
theorem skTopMoveWK (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (e β s : Ordinal.{0}), GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β → s ∈ ldAtR S l →
      S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s →
      s < S.psi (β + Le.leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + Le.leWe (Zi.ziPP S (Zi.ziK3 S))) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ _ hec hβD hbe hs hst hsT IH =>
    Zi.ziTopMoveWK hR h1 hr hl' hB hA' hρ' k hec hβD hbe hs hst hsT IH

/-- STATUS: PROVED (Zi.ziTopMoveCstWK, from Zd.zdTopBase, Zd.zdBaseFacts, Zi.ziMv_cst, Zi.ziHL_cst, Zi.ziPsi3OffWK;
NEW round 132; supersedes skTopMoveChainY3E0; checkable only after the merge)
SIZE: M
Every atom `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂·Ω₂·K₃})` above every top atom `t = β + W^{X_ξ+e}`, `X_ξ = Ω_{k+3} + Ω₂·ξ`,
`ξ < ψ_{Ω₁}(0)`, moves (window, IH(s)). -/
theorem skTopMoveCstWK (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' →
      ∀ (k : ℕ) (ξ e β s : Ordinal.{0}), ξ < Zi.ziG S → GxCl (upsilon l) (ldAtR S l) e → Vb.VbD S l β →
      Ro.RoBaseE S l (Zd.zdX k ξ) e β → s ∈ ldAtR S l → S.psi (β + Le.leWe (Zd.zdX k ξ + e)) (Om (1 + 1)) ≤ s →
      s < S.psi (β + Le.leWe (Zd.zdX k ξ + e) + Le.leWe (Zi.ziPP S (Zi.ziK3 S))) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ hR h1 hr hl' hB hA' hρ' k _ _ _ _ hξ hec hβD hbe hs hst hsT IH =>
    Zi.ziTopMoveCstWK hR h1 hr hl' hB hA' hρ' k hξ hec hβD hbe hs hst hsT IH

/-- STATUS: PROVED (Zi.ziPsi3OffWK, from Zi.ziBot_tow, Zi.ziRS_tow, Zi.ziBotPlat, Zi.ziRSPlat, Zi.ziStepTop0,
Zi.ziPlatO, Zi.ziPlatC, Zi.ziOwnC_iff, Zi.ziBotC, Zi.ziRSC, Zi.ziTopC, Zi.ziVqShC, Zi.ziXUpM, Zi.ziBaseXM,
Zi.ziOwnMoveBr, Zi.ziB_We, Zi.ziB_Oe, Zi.ziTopE_ge; NEW round 132; checkable only after the merge)
SIZE: M
(a) THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂·Ω₂·K₃}`, `K₃ = ψ_{Ω₁}(Ω₃ + 1)` (contains skPsi3OffE0): above every base `a ≥ Ω₃`
with a law at both ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂·Ω₂·K₃})` moves under IH(s). -/
theorem skPsi3OffWK (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Om (1 + 1 + 1) ∣ a → Om (1 + 1 + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + Le.leWe (Zi.ziPP S (Zi.ziK3 S))) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  fun _ _ _ _ _ _ _ hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa hsT IH =>
    Zi.ziPsi3OffWK hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa hsT IH

/-- STATUS: OPEN (NEW round 132; REFUTE FIRST: NO EVIDENCE — every point below `W^{Y₃+Ω₂·Ω₂·K₃}` holds
(skPsi3OffWK); the point `Y₃·2 = Y₃ + Ω₂·Ω₂·Y₃` lies in this range (Zi.ziTestY3two); no known no-go speaks of it)
SIZE: L
The ψ₃-offsets `W^{Y₃+Ω₂·Ω₂·K₃} ≤ δ < Ω₃` above every `Ω₃`-divisible base with a law at both ends.  Missing, in order:
(i) the tower coefficient `η` of `Y₃ + Ω₂·Ω₂·η + Ω₂·ξ` as a CODE (`η ≥ K₃`): the prefix `Y₃ + Ω₂·Ω₂·η` then moves under
`B_n` (`Zi.ziTopC`, `Zi.ziRSC`, `Zi.ziBotC`, `Zi.ziRSPlat` take a FIXED prefix `Zd.ZdRS`; redo them over a moving
prefix `Zi.ZiRS` — the single-restart parts `Zi.ziTopC`, `Zi.ziStepTop0` only use the fields of the prefix at one
restart), giving `W^{Y₃+Ω₂·Ω₂·Ω₂}`; (ii) the higher powers `Y₃ + Ω₂^j·…` (`j ≥ 3`, then `j` a code): the same plateau
step one power up (`Zi.ziStepTop0` with the iterates of the coefficient of `Ω₂^j`); (iii) the shifts not below
`Y₃ + Ω₂^{Ω₂}` (`Y₃·2`, `ψ₃(Ω₃+1)`, …): a level-3 hierarchy of fixed shifts (a constant shift has a constant
image, `Zi.ziRSPlat`). -/
theorem skPsi3OffRest2 (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Om (1 + 1 + 1) ∣ a → Om (1 + 1 + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi (a + Le.leWe (Zi.ziPP S (Zi.ziK3 S))) (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  sorry

/-- STATUS: REDUCED (skPsi3OffWK, skPsi3OffRest2; round 132: was OPEN; REFUTE FIRST: NO EVIDENCE — `Y₃ + Ω₂·ε₀`
holds (skRefTests132), `Y₃·2` lies in the range of skPsi3OffRest2 (Zi.ziTestY3two); no known no-go speaks of these
atoms: Vq.vqNoSh concerns self-relative shifts)
SIZE: L
The ψ₃-offsets `W^{Y₃+Ω₂·ε₀} ≤ δ < Ω₃` above every `Ω₃`-divisible base with a law at both ends (statement unchanged).
Proof: below `W^{Y₃+Ω₂·Ω₂·K₃}` skPsi3OffWK, above it skPsi3OffRest2. -/
theorem skPsi3OffRest (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Om (1 + 1 + 1) ∣ a → Om (1 + 1 + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi (a + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa hsT IH
  rcases lt_or_ge s (S.psi (a + Le.leWe (Zi.ziPP S (Zi.ziK3 S))) (Om (1 + 1))) with h | h
  · exact skPsi3OffWK S n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs
      ((psi_mono (InR_Om_succ 1) (le_self_add : a ≤ a + Le.leWe (Zd.zdXr S ε₀))).1.trans hsa) h IH
  · exact skPsi3OffRest2 S n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs h hsT IH

/-- STATUS: REDUCED (skPsi3OffE0, skPsi3OffRest; NEW round 131)
SIZE: L
THE ψ₃-OFFSETS OVER `Ω₃`-DIVISIBLE BASES (the form the assembly of skWallBase needs: every base it meets is a top atom
or below one with `Ω₃ ∣ t`, `Ω₃ ∣ B_n t`): every atom `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` moves.  skPsi3OffHi (bases with only
`Y₃ ∣ a`) is not needed for it. -/
theorem skPsi3OffD (S : InaccSeq.{0}) :
    ∀ (n : ℕ) (l l' A' a D s : Ordinal.{0}), CdRange S l → Bc.bcC S n < upsilon l →
      cdR S l < Bc.bcC S (n + 1) → IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      A' ∈ S.CSet A' (S.psi A' (Om 1)) → S.psi A' (Om 1) = upsilon l' → Yj.YjBase S n l l' A' a D →
      Om (1 + 1 + 1) ∣ a → Om (1 + 1 + 1) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a → s ∈ ldAtR S l →
      S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)) →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  intro n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa hsT IH
  rcases lt_or_ge s (S.psi (a + Le.leWe (Zd.zdXr S ε₀)) (Om (1 + 1))) with h | h
  · exact skPsi3OffE0 S n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs hsa h IH
  · exact skPsi3OffRest S n l l' A' a D s hR h1 hr hl' hB hA' hρ' hb hd hd' ha3 hs h hsT IH

/-- STATUS: PROVED (Zp.zpTest1, Zp.zpTest2, Zp.zpDecomp; NEW round 133; the REFUTE-FIRST record of the assembly;
checkable only after the merge)
SIZE: S
`Ω₃·((Ω₃·2+Ω₃)/Ω₃) = Ω₃·3`, `W^{Ω₃+1} = Ω₃·Ω₂`, `Y₃·2 < Ω₃`, `Ω₃·((W^{Ω₃+1}+Y₃·2)/Ω₃) = W^{Ω₃+1}`. -/
theorem skRefTests133 (S : InaccSeq.{0}) :
    (Om (1 + 1 + 1) * ((Om (1 + 1 + 1) * 2 + Om (1 + 1 + 1)) / Om (1 + 1 + 1)) = Om (1 + 1 + 1 : Ordinal.{0}) * 3 ∧
      Om (1 + 1 + 1) * 2 + Om (1 + 1 + 1) = Om (1 + 1 + 1 : Ordinal.{0}) * 3) ∧
    (Le.leWe (Om (1 + 1 + 1) + 1) = Om (1 + 1 + 1 : Ordinal.{0}) * Om (1 + 1) ∧
      Ug.ugY S * 2 < Om (1 + 1 + 1) ∧
      Om (1 + 1 + 1) * ((Le.leWe (Om (1 + 1 + 1) + 1) + Ug.ugY S * 2) / Om (1 + 1 + 1)) =
        Le.leWe (Om (1 + 1 + 1 : Ordinal.{0}) + 1)) :=
  ⟨Zp.zpTest1, Zp.zpTest2⟩

/-- STATUS: PROVED (Zp.zpDecomp, from Zp.zpPre3_norm, Zp.zpPre_norm, Zp.zpGap_psi, Zp.zpGap_sub, Zp.zpPre_mem,
Vb.vbReach, Zp.zpPsi_Om3 (Vn.vnPsi2_eq); NEW round 133; checkable only after the merge)
SIZE: M
EVERY ATOM BELOW THE WALL IS `ψ₂(b + δ)`: `s ∈ At_λ`, `ψ₂(Y₃) ≤ s < θ` ⇒ `s = ψ₂ d`, `d ∈ D_λ` normal,
`b = Ω₃·(d/Ω₃)` normal, `b ∈ D_λ`, `Ω₃ ≤ b`, `d < b + Ω₃`, `ψ₂ b ≤ s < ψ₂(b + Ω₃)`. -/
theorem skDecomp (S : InaccSeq.{0}) {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l) (hsY : S.psi (Ug.ugY S) (Om (1 + 1)) ≤ s) (hsθ : s < ConjT.th S) :
    ∃ d, Vb.VbD S l d ∧ S.psi d (Om (1 + 1)) = s ∧ d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧
      Vb.VbD S l (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) ∧
      Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ∈ S.CSet (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)))
        (S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (Om (1 + 1))) ∧
      Om (1 + 1 + 1) ≤ Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ∧
      d < Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) + Om (1 + 1 + 1) ∧
      S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (Om (1 + 1)) ≤ s ∧
      s < S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) + Om (1 + 1 + 1)) (Om (1 + 1)) :=
  Zp.zpDecomp hl hX hs hsY hsθ

/-- STATUS: PROVED (Zp.zpYjBase, from Zp.zpBaseD, Zp.zpDvd3, Zp.zpB3_le, Xq.xqTMove, Xq.xqSigMove, Xq.xqOwn,
Vb.vbT_move, Rx.rxL_memH, Yd.ydNormB, Yj.yjTh_hi; NEW round 133; checkable only after the merge)
SIZE: M
THE BASE: at a window, `ZpTopLawAll`, `b ∈ D_λ` normal, `Ω₃ ∣ b`, `Ω₃ ≤ b`, IH(ψ₂ b) ⇒
`Yj.YjBase λ λ' A' b (1 + ψ₂(T b))` ∧ `Ω₃ ∣ B_n b`. -/
theorem skBaseOfLaw (S : InaccSeq.{0}) {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1)))
    (hρ' : S.psi A' (Om 1) = upsilon l') (hLaw : Zp.ZpTopLawAll S) {b : Ordinal.{0}} (hbD : Vb.VbD S l b)
    (hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (hdv : Om (1 + 1 + 1) ∣ b) (h3 : Om (1 + 1 + 1) ≤ b)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi b (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    Yj.YjBase S n l l' A' b (1 + S.psi (Vb.vbT S l b) (Om (1 + 1))) ∧ Om (1 + 1 + 1) ∣ Bc.bcB S n b :=
  Zp.zpYjBase hR h1 hr hl' hB hA' hρ' hLaw hbD hbn hdv h3 IH

/-- STATUS: OPEN (NEW round 133; REFUTE FIRST: NO EVIDENCE — it holds at every top atom `β + W^{Ω_{k+3}+e}`, `e` a
code (Zp.zpLaw_top from Xm.xmTopUp), at the limit sub-bases of Yt.ytSubLaw, at the chain exponents of Zd.zdChain,
Zi.ziChain, Yy.yyLawOm2 (all are instances of this form); at `W^{Ω₃+ω}` it is Xi.xiReadOm (`1 + P* = P*`);
the refuted forms speak of other points or other images: Xq.xqRef_wit (`Ω₃+1`, not `Ω₃`-divisible), Xd.xdX0Law_false
(`β = Ω_ω ∉ D`), Vn.vnTop_Om3 / Vq.vqNoTop_Om3 (a constant image), Wb.wbNoY (the image `Y_{k+2}` in place of
`ψ₂(T Y_{k+3})`), Xi.xiTopFam_false (the family law); its premises are met at every restart (Zp.zpLaw_wit))
SIZE: L
THE TOP LAW AT EVERY EXPONENT: at every restart `λ` (`ρ_λ < P(η)`, `A` own, `ψ₁(A) = ρ_λ`), every normal `b ∈ D_λ`
with `Ω₃ ∣ b`, `Ω₃ ≤ b` has `Θ_λ(ψ₂ b) = ψ₁(A + 1 + ψ₂(T_λ b))`.  Missing: the exponents of the top atoms past
those of Xi.XiTopUp / Zd.zdChain / Zi.ziChain / Zv.zvChain / Zw.zwChain (`b = β + W^E`; round 141: every
`E = Ω_{k+3} + Ω₂·ξ + e` with a CODE coefficient `ξ < θ` is done, `Zw.zwChain`, from the threshold shift data
`Zd.ZdShQ`, on the bases with `Zw.ZwQ` (every code `ξ' ≤ ξ` below `ψ₂(β + W^{Ω_{k+3}+Ω₂·ξ'})`); round 142: THE
JUMP `X → X + W^{h+1}` for every shift `X` and exponent `h ∈ D` (`Zx.zxLawJ`, plateau of the two-level tower
`Tβ + ω^{Ω₁·TX + ω^{Ω₁+Ω₁·Th}·x}`, `Zx.zxPlat_tower`), and its first instance `E = Ω_{k+3} + Ω₂·Ω₂ + e`
(`Zx.zxLaw2All`); left: (i) `ZwQ` from the normality of `b`, (ii) the induction over the shifts `X + W^h·u` (the
coefficient chain over any shift, the limit exponents `h` — continuity of `T`, or deeper towers when `T` jumps at
`h` — and the `W`-fixed exponents `E ≥ Ω₃·2`, `ψ_{k+4}`-terms), and the limit sub-bases `β + W^E·γ` at those
exponents (continuity, as Yt.ytSubLaw). -/
theorem skTopLawAll (S : InaccSeq.{0}) : Zp.ZpTopLawAll S := by
  sorry

/-- STATUS: REDUCED (skTopLawAll, skPsi3OffD; Zp.zpWall, from Zp.zpDecomp, Zp.zpYjBase; NEW round 133;
checkable only after the merge)
SIZE: L
THE WALL BELOW `θ`: every atom `ψ₂(Y₃) ≤ s < θ` moves under IH(s) (`Zp.ZpWallTh`). -/
theorem skWallTh133 (S : InaccSeq.{0}) : Zp.ZpWallTh S :=
  Zp.zpWall (skTopLawAll S) (skPsi3OffD S)

/-- STATUS: PROVED (Zp.zpOff_of_wall, Zp.zpLaw_wit; NEW round 133; the NON-VACUITY record of the two leaves)
SIZE: S
`ZpWallTh ⇒ ZpPsi3OffAll` (the ψ₃-offset leaf follows from the target), and at every restart some `b = Ω₃` meets
the premises of `ZpTopLawAll` with its conclusion. -/
theorem skWallNonVac (S : InaccSeq.{0}) :
    (Zp.ZpWallTh S → Zp.ZpPsi3OffAll S) ∧
    ∀ {l ηx A : Ordinal.{0}}, IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      ∃ b, Vb.VbD S l b ∧ b ∈ S.CSet b (S.psi b (Om (1 + 1))) ∧ Om (1 + 1 + 1) ∣ b ∧ Om (1 + 1 + 1) ≤ b ∧
        gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
          S.psi (A + 1 + S.psi (Vb.vbT S l b) (Om (1 + 1))) (Om 1) :=
  ⟨Zp.zpOff_of_wall, fun hl hX hA hρ => Zp.zpLaw_wit hl hX hA hρ⟩

/-- STATUS: PROVED (psi_mono; NEW round 133)
SIZE: S
`lev S k ≤ θ`. -/
theorem skLev_le_th (S : InaccSeq.{0}) (k : ℕ) : lev S k ≤ ConjT.th S :=
  (psi_mono (InR_Om_succ 1) (Om_le_Om.2 (Ordinal.natCast_lt_omega0 (k + 4)).le)).1

/-- STATUS: PROVED (NEW round 133)
SIZE: S
The wall below any bound `b ≤ θ` from the wall below `θ`. -/
theorem skWallOfTh (S : InaccSeq.{0}) (b : Ordinal.{0}) (hb : b ≤ ConjT.th S) (hW : Zp.ZpWallTh S) :
    WallBelow S b := by
  intro n l l' hR h1 hr hl' hB s hs hsY hsb IH
  exact hW n l l' hR h1 hr hl' hB s hs hsY (hsb.trans_le hb) IH

/-- STATUS: REDUCED (round 133: was OPEN; skWallTh133 ⇐ skTopLawAll, skPsi3OffD; statement unchanged; the hypotheses
`Xi.XiTopUp`, `hν` are not used; the RISK below is gone: the B_n-move of the image is the law at both ends, taken
from skTopLawAll at λ and at λ' with the base data moved by Zp.zpBaseD; checkable only after the merge)
(was OPEN: RISK: the family law fixes no B_n-move of the images X̂_e; the step will likely need, in addition,
`B_n X̂^λ_e(β) = X̂^{λ'}_{B_n e}(B_n β)`, which is itself a move statement; round 112: for own images that move IS the
atom move at T_{X+e}(β), Wr.wrImgMove_iff, so it cannot be added as a hypothesis without assuming the conclusion)
(round 112: CHANGED to the code-free WallBelow)
(round 122: hypothesis CHANGED from the REFUTED Wg.WgTopFamAll (with it the node was vacuous) to Xi.XiTopUp)
(round 126: REFUTE FIRST on the inverse correspondence: REFUTED (skInvRef).  Replaced by the plateau (skPlatB) and the
move of the own clause (skOwnMove): EVERY top atom over the base 0 moves (skTopMoveAll0, no hypothesis), and every top
atom over a base β ∈ D moves given the two base facts at λ' (skTopMoveAllB ⇐ skBaseFactsB, OPEN M).  Still missing for
this node: skBaseFactsB, the non-top atoms past the first block above each top (offsets δ < W^X over t, the sub-bases
β + W^{X+e}·γ at limit γ, the ψ₃-atoms inside the exponents), and the assembly of WallBelow from them.)
(round 127: skBaseFactsB PROVED, so every top atom moves (skTopMoveAllB PROVED); the generic block move skBlkMove /
skBlkNext and skTopBase give every atom ψ₂(t + Ω₂·m + c), m < ω, above every top atom t (skTopBlkFin).  Still missing:
the bases t + Ω₂·γ for γ ≥ ω (the port of Ld.ldG2_base / ldG2_cls / ldG2_supp to a base t with image D), the offsets
δ ≥ Ω₂·Ω₂ below W^X over t (the port of the base-0 chain up to Ux.uxAtMoveTop to the base t), the sub-bases
β + W^{X+e}·γ at limit γ, the ψ₃-atoms inside the exponents, the assembly of WallBelow.)
(round 125: REFUTE FIRST on the BASE-DATA MOVE: NO EVIDENCE; it is PROVED at the base 0 for the exponents
e < ψ₂(Ω_{k+3}) (skBaseMove0), and those top atoms move with no extra hypothesis (skTop0Move; the bound
Θ(ψ₂ t) < c_{n+1} is derived).  Still missing for the general top base (e, β): the OWN CLAUSE of RoBaseE at λ' for the
codes e'' ≤ B_n e of λ' with e'' ≥ ψ₂(B_n β + W^X) (needs a pullback: every code of λ' below B_n(ψ₂ t) is B_n of a code
of λ; a failing e'' yields the failing atom code F = ψ₂(B_n β + W^{X+e''}) ≤ e'', so it suffices for atoms), and for
β ≠ 0 the divisibility W^{X+B_n e} | B_n β, the normality of B_n β, and B_n β ∈ D' (vbT_move + Rx.rxL_memH).)
(round 132: (1) the ψ₃-offsets below `W^{Y₃+Ω₂·Ω₂·K₃}`, `K₃ = ψ_{Ω₁}(Ω₃+1)`, PROVED (skPsi3OffWK; above every top
atom skTopMoveWK, skTopMoveCstWK), the rest is skPsi3OffRest2 (via skPsi3OffRest, skPsi3OffD); the coefficients of the
shifts `P + Ω₂·ξ` are now any CODE (moving shifts, skBotPlat), and every plateau shift `P + Ω₂·Ω₂` of a fixed shift is
again a fixed shift with constant image (skRSPlat); (2) the top law at every `X + Ω₂·ξ + e`, `ξ < ψ_{Ω₁}(0)`
(skTopLawCst); the exponents `E ≥ Ω₃` reduce to `E ∈ [Y₃, Ω₃)` (skPlat3); still missing for (2): the coefficients
`ξ ≥ ψ_{Ω₁}(0)` (codes: `Zd.ZdSh` asks membership in every closure; redo `Zd.zdSucc` / `Zd.zdLim` / `Zd.zdLawW` with the
relative membership `Zi.ZiMemR` and the move of `Zd.ZdMv` as in `Zi.ZiShB`), the plateau `X + Ω₂·Ω₂` (as `Zi.ziStepTop0`
for the T-form), the exponents in `[Ω₂·Ω₂, Ω₃)`; (3) the assembly: unchanged.)
(round 131: (1) for `Ω₃`-divisible bases the ψ₃-offsets below `W^{Y₃+Ω₂·ε₀}` PROVED (skPsi3OffE0; above every top
atom skTopMoveY3E0, skTopMoveChainY3E0), the rest is skPsi3OffRest (via skPsi3OffD); (2) the top law and the move at
EVERY exponent `X + Ω₂·ξ + e`, `ξ < ε₀` (skTopLawChain, skTopMoveChain, skTopBaseChain); still missing for (2): the
exponents `X + Ω₂·ξ` with `ξ ≥ ε₀` a code (own clause of `ξ` instead of membership in every closure), the
`Ω₂`-cofinal limit `X + Ω₂²` (plateau over `ξ`), and `E ≥ Ω₃`; (3) the assembly: unchanged.)
(round 130: (1) REDUCED to skPsi3OffHi (bases `a ≥ Ω₃`), its part below `ψ₂(a + W^{Y₃+1})` PROVED (skY3MoveW, above
every top atom skTopMoveY3W); (2) PROVED at `E = Ω₂` (skTopLawOm2, the atom and the block above it move, skTopMoveOm2Y);
still missing for (2): `E = Ω₂ + e` for codes `e` (Xm.xmSucc / Xm.xmLim with the shift `X + Ω₂` in place of
`Ω_{k+3}`: both are written for `X = Ω_{k+3}` only), `E ≥ Ω₂·2`, and the non-code `E ≥ Ω₃` (`W^{Ω₃·2}`, `T = Ω^{Ω₂·2}`):
a level system for the exponent past `Ω₂` at the shift `Ω₃`; (3) unchanged.)
(round 129: (a) and (b) below `Y₃` PROVED at every top atom (skTopMoveY), (c) for limit coefficients PROVED
(skSubLawLim, skSubBaseLim, skSubMoveY); still missing, in order: (1) skPsi3Off (offsets `Y₃ ≤ δ < Ω₃` above every
base); (2) the top law and its move for the NON-CODE exponents `X + E`, `Ω₂ ≤ E` (e.g. `ψ₂(W^{Ω₃·2})`,
`T = Ω^{Ω₂·2}`): `Xi.XiTopUp` / `Xm.xmTopUp` only cover codes `e < Ω₂` (needs the level chain past `Ω₂` for the
shift `X = Ω₃`); (3) the assembly: every atom `ψ₂(Y₃) ≤ s < ψ₂(Ω₄)` is `ψ₂(b + δ)` with `b` a top base or a
limit sub-base of `X = Ω₃` (base data `Ro.RoBaseE`, `β ∈ D`) and `δ < Ω₃`, the premise at `b` from the premise at `s`.)
(round 124: REFUTE FIRST: the ψ₂(T a) form fails off the top atoms (skWallRefNonTop, a = Ω₃ + 1); (i) is PROVED in the
first block above every top (skTopBlk), (ii) is PROVED (skTMove, skSigMove), and every top atom moves once its base
data move (skTopMove).  Still missing: the BASE-DATA MOVE (B_n of a top base β + W^{X+e} is a top base β' + W^{X+e'}
of λ', with RoBaseE at λ'), the bound Θ(ψ₂ t) < c_{n+1}, and the non-top atoms past the first block: offsets
δ < W^X over a base t (the region [ψ₂(t), ψ₂(t + Y₃)] relative to t, i.e. Ux.uxAtMoveTop redone at every base t with
the base image A + 1 + ψ₂(T t)), the sub-bases β + W^{X+e}·γ at limit γ (continuity, as in Xm.xmLim, once
RoBaseE holds at the sub-bases), and the ψ₃-atoms inside the exponents.)
(round 123: the hypothesis Xi.XiTopUp is now a theorem (skTopUp), so the node is not vacuous; still OPEN.  Missing:
(i) the readings of the non-top atoms ψ₂(β + W^{X+e}·γ + δ) (block laws in the style of Ro.roStepA with the image
ψ₁(A + 1 + ψ₂(T ·)) in place of a constant image; skTopUp gives only the tops), (ii) the B_n move of T = Vb.vbT and of
A_η (B_n (T_λ x) = T_{λ'}(B_n x); Vb.vbT_move needs Vb.vbLeaf_of_codes), so that B_n maps ψ₁(A_λ + 1 + ψ₂(T_λ a)) to
ψ₁(A_{λ'} + 1 + ψ₂(T_{λ'}(B_n a))).)
SIZE: L
`TopUp ∧ hν ⇒ every atom ψ₂(Y₃) ≤ s < ψ₂(Ω₄) moves: MvD s, B_n s ∈ At_{λ'}, Θ_{λ'}(B_n s) = B_n Θ_λ(s)`
(was SUSPECT with the refuted TopDynAll; then with the family law Wg.WgTopFamAll, itself REFUTED in round 122)
(first block past the Y₃ wall; needs the Uq prefixes / Uu level system with the bound as a field and the image
Vb.vbT, and vqStepA ported to VtTopDyn).  L: no Lean statement of the level system past Y₃ exists yet. -/
theorem skWallBase (S : InaccSeq.{0}) : Xi.XiTopUp S → Nc.ncL S (ω + 1) ≤ nuC → WallBelow S (lev S 0) :=
  fun _ _ => skWallOfTh S (lev S 0) (skLev_le_th S 0) (skWallTh133 S)

/-- STATUS: REDUCED (round 133: was OPEN; skWallTh133 ⇐ skTopLawAll, skPsi3OffD, for every k at once: the
decomposition Zp.zpDecomp needs no recursion over the levels; statement unchanged; checkable only after the merge)
(was OPEN: RISK as skWallBase: no B_n-move of the images in the hypothesis; Wr.wrImgMove_iff)
(round 112: CHANGED to the code-free WallBelow)
(round 122: hypothesis CHANGED from the REFUTED Wg.WgTopFamAll (with it the node was vacuous) to Xi.XiTopUp)
(round 123: Xi.XiTopUp is now a theorem (skTopUp); still OPEN, same missing pieces (i), (ii) as skWallBase, generic in k)
(round 124: skTopBlk, skTMove, skSigMove, skTopMove are generic in k; the same pieces as skWallBase are missing)
(round 125: skBaseMove0, skTop0Move are generic in k; the same pieces as skWallBase are missing)
(round 126: skTopMoveAll0, skOwnMove, skTopMoveAllB are generic in k; the same pieces as skWallBase are missing)
(round 127: skBaseFactsB, skTopMoveAllB, skTopBase, skTopBlkFin are generic in k; the same pieces as skWallBase are
missing)
(round 132: skTopLawCst, skTopMoveWK, skTopMoveCstWK, skBotPlat, skRSPlat, skPsi3OffWK are generic in k; missing
the same as skWallBase)
(round 131: skTopLawChain, skTopBaseChain, skTopMoveChain, skPsi3OffE0, skTopMoveY3E0, skTopMoveChainY3E0 are generic
in k; missing the same as skWallBase)
(round 130: skTopLawOm2, skTopMoveOm2Y, skY3MoveW, skTopMoveY3W are generic in k; missing the same as skWallBase)
(round 129: skTopMoveY, skSubLawLim, skSubBaseLim, skSubMoveY are generic in k; missing the same (1)–(3) as
skWallBase, with (3) recursive: below `ψ₂(Ω_{k+4})` an atom is `ψ₂(b + δ)` with `b` a base of some level `j ≤ k`
and `δ < Ω₃` after removing every part divisible by `Ω₃`)
SIZE: L
`TopUp ∧ hν ⇒ ∀ k, (atoms < ψ₂(Ω_{k+4}) move) ⇒ (atoms < ψ₂(Ω_{k+5}) move)` (one level up; the step
Ω_{k+3} → Ω_{k+4} of the readings with sub-base images; Wb.wbKe_sup_it / wbTe_gt_Om give the layer facts).
L: same missing level system as skWallBase, generic in k. -/
theorem skWallStep (S : InaccSeq.{0}) : Xi.XiTopUp S → Nc.ncL S (ω + 1) ≤ nuC →
    ∀ k : ℕ, WallBelow S (lev S k) → WallBelow S (lev S (k + 1)) :=
  fun _ _ k _ => skWallOfTh S (lev S (k + 1)) (skLev_le_th S (k + 1)) (skWallTh133 S)

/-- STATUS: REDUCED (skTopUp, skWallBase, skWallStep; round 122: skTopUp in place of the REFUTED skTopFam; round 123:
skTopUp PROVED, so only skWallBase, skWallStep are open below it)
SIZE: L
`hν ⇒ ∀ k < ω, every atom ψ₂(Y₃) ≤ s < ψ₂(Ω_{k+4}) moves` (induction on k). -/
theorem skWallLevAll (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → ∀ k : ℕ, WallBelow S (lev S k) := by
  intro hν k
  induction k with
  | zero => exact skWallBase S (skTopUp S) hν
  | succ k IH => exact skWallStep S (skTopUp S) hν k IH

/-- STATUS: REDUCED (skThCof, skWallLevAll)
SIZE: L
`hν ⇒ every atom ψ₂(Y₃) ≤ s < θ moves at every window` (round 112: statement `Wr.WrWallLowCF`, no code hypothesis). -/
theorem skWallLow (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wr.WrWallLowCF S := by
  intro hν n l l' hR h1 hr hl' hB s hs hsY hsθ IH
  obtain ⟨a, ha1, ha2, rfl⟩ := hs
  obtain ⟨k, hk⟩ := skThCof S a hsθ
  exact skWallLevAll S hν k n l l' hR h1 hr hl' hB _ ⟨a, ha1, ha2, rfl⟩ hsY hk IH

/-- STATUS: PROVED (Wg.wgTheta_le, from Ld.ldTheta_le_psi, Wg.wgOwnEta)
SIZE: S
Upper half of skThVal: `restart λ, A own, ψ₁(A) = ρ_λ ⇒ Θ_λ(θ) ≤ ψ₁(A + θ)` (sharpens Wb.wbTheta_lt: A + θ + 1). -/
theorem skThUp (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l →
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) ≤ S.psi (A + ConjT.th S) (Om 1) :=
  fun _ _ _ hl hX hA hρ => Wg.wgTheta_le hl hX hA hρ

/-- STATUS: PROVED (Wl.wlThLow, from Wl.wlBlk0, Wl.wlL_memB, Wl.wlCof, Rx.rxLift, Wg.wgLow_of_all; round 111)
SIZE: L
Lower half of skThVal: `restart λ, A own, ψ₁(A) = ρ_λ, θ ∈ At_λ ⇒ ψ₁(A_{η_λ} + θ) ≤ Θ_λ(θ)` (`Wg.WgThLow`;
sufficient: ψ₁(A+ζ) < Θ_λ(θ) for every ζ < θ, Wg.wgLow_of_all).  REFUTE FIRST: NO EVIDENCE (the known readings below θ,
Vn.vnRead_Y3, Vq.vqRead_Om3Y3, Ro.roTheta_th_gt, are far below ψ₁(A+θ) and do not decide it).  Blocker: the lift of
Rx.rxBlkTh at the base 0 fails (Rx.rxL_memH needs Ω_ω ≤ a).  Proof (round 111): for ζ < θ pick a member w ≥ ζ over 2
(Rx.rxCofTh) and k with w < B_k = ψ₂(Ω_{k+1}) (Wl.wlCof); lift at the base Ω_{k+2}: ψ₁(A + w) ≤ Θ(ψ₂(Ω_{k+2} + κ w))
(Rx.rxLift on the members below B_k; the transfer κ(e − A) ∈ Cl(Ω_{k+2} + κ w, ·) is Wl.wlL_memB, every collapse
argument of a member of Cl(Ω_{k+1}, B_k) is below Ω_{k+1}), and ψ₂(Ω_{k+2} + κ w) ≤ ψ₂(Ω_{k+3}) < θ.  The hypotheses
"A own", "ψ₁(A) = ρ_λ", "θ ∈ At_λ" are not used. -/
theorem skThLow (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → ConjT.th S ∈ ldAtR S l →
      Wg.WgThLow S l :=
  fun _ _ _ hl hX _ _ _ => Wl.wlThLow hl hX

/-- STATUS: PROVED (skThUp, skThLow; Wg.wgThVal_of_low; = Wl.wlThVal, which needs no θ ∈ At_λ; round 111)
SIZE: S
`restart λ, A own, ψ₁(A) = ρ_λ, θ ∈ At_λ ⇒ Θ_λ(θ) = ψ₁(A + θ)` (the candidate TRUE value; consistent with
Wb.wbTheta_lt and Ro.roTheta_th_gt; ψ₁(A+1+Ω_ω) is refuted by Wb.wbTheta_ne).  Statement unchanged. -/
theorem skThVal (S : InaccSeq.{0}) :
    ∀ (l ηx A : Ordinal.{0}), IsRestartIdx l → upsilon l < Nm.Pv S ηx →
      A ∈ S.CSet A (S.psi A (Om 1)) → S.psi A (Om 1) = upsilon l → ConjT.th S ∈ ldAtR S l →
      gxTh (upsilon l) (ldAtR S l) (ConjT.th S) = S.psi (A + ConjT.th S) (Om 1) := by
  intro l ηx A hl hX hA hρ hθ
  exact Wg.wgThVal_of_low hl hX hA hρ (skThLow S l ηx A hl hX hA hρ hθ)

/-- STATUS: PROVED (Cd.cdEta_pv_spec, Bc.bcB_bound', Bc.bcB_fix', Bc.bcB_mono', Gv.gvK_eq, Td.tdK_lt_L)
SIZE: S
`window λ → λ' ⇒ θ ∈ At_{λ'}` (i.e. η_{λ'} ≠ 0, so Ω_ω < A_{λ'}; ρ_{λ'} = B_n ρ_λ > ψ₁(Ω_ω)). -/
theorem skThAtom (S : InaccSeq.{0}) :
    ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → ConjT.th S ∈ ldAtR S l' := by
  intro n l l' hR h1 hr hl' hB
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  obtain ⟨-, -, -, hpv'⟩ := cdEta_pv_spec (S := S) hl'.1 hX'
  have hη0 : cdEta S l' ≠ 0 := by
    intro h0
    rw [h0] at hpv'
    have hK : Nm.Pv S 0 < Bc.bcC S n := by
      rw [← Gv.gvK_eq S]; exact Td.tdK_lt_L _
    have hfix := Bc.bcB_fix' (S := S) n _ hK
    have hlt := Bc.bcB_mono' (S := S) n (show Nm.Pv S 0 ∈ Set.Iio (Bc.bcC S (n + 1)) from (hK.trans h1).trans h2)
      (show upsilon l ∈ Set.Iio (Bc.bcC S (n + 1)) from h2) (hK.trans h1)
    rw [hfix, hB, ← hpv'] at hlt
    exact lt_irrefl _ hlt
  refine ⟨Om ω, ConjT.OmW_mem (S := S) _ _, ?_, rfl⟩
  show Om ω < Om ω + ConjT.th S * cdEta S l'
  exact lt_add_of_pos_right _ (mul_pos (Sf.sfTh_pos S) (pos_iff_ne_zero.2 hη0))

/-- STATUS: PROVED (skThVal, skThAtom; round 111: all children proved; with Lj.ljB_th, Ld.ldOwnA, Cd.cdEta_pv_spec, Mx.mxUps_succ,
Ld.ldB_psi_add, Bc.bcB_bound')
SIZE: M
`θ atom: MvD θ, B_n θ = θ ∈ At_{λ'}, Θ_{λ'}(θ) = ψ₁(A'+θ) = B_n ψ₁(A+θ) = B_n Θ_λ(θ)`. -/
theorem skWallTh (S : InaccSeq.{0}) : WallAtTheta S := by
  intro n l l' hR h1 hr hl' hB hm _ _ hs
  obtain ⟨hDθ, hBθ⟩ := Lj.ljB_th (S := S) (n := n)
  refine ⟨hDθ, by rw [hBθ]; exact skThAtom S n l l' hR h1 hr hl' hB, ?_⟩
  rw [hBθ]
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hρA : S.psi A (Om 1) = upsilon l := hpv
  have hΘ := skThVal S l _ A hl hX hown hρA hs
  have hθ0 : 0 < ConjT.th S := Sf.sfTh_pos S
  have hWA : Om ω < A + ConjT.th S := by
    rw [hA_def]; unfold ConjT.Aη
    exact lt_of_le_of_lt le_self_add (lt_add_of_pos_right _ hθ0)
  have hownθ : A + ConjT.th S ∈ S.CSet (A + ConjT.th S) (S.psi (A + ConjT.th S) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown) (ConjT.th_mem (S := S) hWA)
  have hu1 : upsilon (l + 1) < cdDelta l :=
    upsilon_normal.strictMono (by
      calc l + 1 < l + ω := (add_lt_add_iff_left l).2 one_lt_omega0
        _ < l + ω + 1 := lt_add_one _)
  have hbX : S.psi (A + ConjT.th S) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← mxUps_succ hl hX]; exact hu1.trans hδr
  obtain ⟨A', hA', hBP, hBd⟩ := ldB_psi_add (n := n) hg (hpv ▸ h1.le) hDθ hownθ hbX
  have hρA' : S.psi A' (Om 1) = upsilon l' := by rw [← hBP, hpv, hB]
  have hX' : upsilon l' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hB]; exact Bc.bcB_bound' S n _ h2
  have hΘ' := skThVal S l' _ A' hl' hX' hA' hρA' (skThAtom S n l l' hR h1 hr hl' hB)
  rw [hΘ', hΘ, hBd, hBθ]

/-- STATUS: REDUCED (skWallLow; Wr.wrWallCF_of_low, Wr.wrAtTh; NEW round 112)
SIZE: L
`hν ⇒ Wr.WrWallCF`: the code-free wall, atoms ψ₂(Y₃) ≤ s < θ (skWallLow) and the atom θ (Wr.wrAtTh, code-free
form of skWallTh). -/
theorem skWallCF (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wr.WrWallCF S :=
  fun hν => Wr.wrWallCF_of_low (skWallLow S hν)

/-- STATUS: REDUCED (skWallCF; Wr.wrWall_of_cf; round 112: was REDUCED to skWallLow, skWallTh)
SIZE: L
`hν ⇒ WdAtWall` (⇔ Ux.UxAtMove26 by Wd.wdWall_iff): the code-free wall restricted to F_W ≤ m_λ < θ⁺. -/
theorem skWall (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S :=
  fun hν => Wr.wrWall_of_cf (skWallCF S hν)

/-- STATUS: PROVED (skThVal; Cd.cdEta_pv, Ro.roThW_A; round 111: skThVal proved)
SIZE: S
`Θ_λ(ψ₂(Ω_ω + c)) = ψ₁(A + θ + Θ_λ(c))` for codes c < M_W with Ω_ω + c < A. -/
theorem skBlkLaw (S : InaccSeq.{0}) : BlkLaw S := by
  intro l ηx A hl hX hA hAη hθ
  have hρ : S.psi A (Om 1) = upsilon l := by rw [hAη]; exact cdEta_pv hl.1 hX
  exact Ro.roThW_A hl hX hA hAη (skThVal S l ηx A hl hX hA hρ hθ)

/-- STATUS: SUSPECT (round 112: its hypothesis `hν ⇒ WdAtWall` is stated only at windows with F_W ≤ m_λ < θ⁺,
while RnThMoveM asks windows with m_λ ≥ θ⁺, so the atoms ≤ θ at those windows are not covered; REPLACED by skMidCF,
which takes the code-free wall Wr.WrWallCF; no node uses it)
SIZE: M
`BlkLaw ∧ (hν ⇒ WdAtWall) ∧ hν ⇒ RnThMoveM`: codes θ⁺ ≤ m ≤ M_W are read through the atoms ψ₂(Ω_ω + c) (block
law at λ and λ') and the atoms ≤ θ (WdAtWall); B_n ψ₁(A+θ+x) = ψ₁(A'+θ+B_n x) by Ld.ldB_psi_add (MvD, own).
Needs the gx-recursion of Ld.ldGxStepRec past θ⁺ (atoms up to M_W).  Round 111: the hypothesis BlkLaw is
proved (skBlkLaw PROVED), so this node needs only (hν ⇒ WdAtWall). -/
theorem skMidAssemble (S : InaccSeq.{0}) : BlkLaw S → (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S) →
    Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S := by
  sorry

/-- STATUS: PROVED (Wr.wrMid, from Wr.wrAtLow, Wr.wrAtBlk, Wr.wrThMW, Ld.ldGxStepRec; NEW round 112, replaces
skMidAssemble)
SIZE: M
`(hν ⇒ Wr.WrWallCF) ∧ hν ⇒ RnThMoveM`: at a window with θ⁺ ≤ m_λ ≤ M_W the code is e = e(η_λ) (cdPi ≤ M_W is
impossible above P(Ω₂)); atoms < θ⁺ move (Le.leAtMove_FWW, Ux.uxAtMoveTop, the wall), atoms ψ₂(Ω_ω + c) move by the
block law at λ and λ' (skBlkLaw's content, Ro.roThW_A with Wl.wlThVal), all codes < M_W move (Ld.ldGxStepRec), and
Θ_λ(M_W) = ψ₁(A + θ + Ω₁) (Wr.wrThMW) moves by Ld.ldB_psi_add.  Checkable only after the merge (imports R2.WrMid). -/
theorem skMidCF (S : InaccSeq.{0}) : (Nc.ncL S (ω + 1) ≤ nuC → Wr.WrWallCF S) →
    Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S :=
  fun h hν => Wr.wrMid (h hν)

/-- STATUS: REDUCED (skMidCF, skWallCF; round 112: was skBlkLaw, skWall, skMidAssemble)
SIZE: M
`hν ⇒ RnThMoveM`: the reading move at codes θ⁺ ≤ m_λ ≤ M_W. -/
theorem skThMid (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S :=
  skMidCF S (skWallCF S)

/-- STATUS: REDUCED (SkE.skTopK, skWallCF; round 124: the shared leaf, one copy kept in SkE; round 132: SkE.skTopK takes
the code-free wall `SkE.SkWall S`, given here by `skWallCF`)
SIZE: S
`hν ⇒ ∀ window λ → λ', (∀ j, K_j ≤ m_λ) ⇒ B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})`  (statement Xs.XsTopK S; the OPEN leaf is
`R2Skel.SkE.skTopK`). -/
theorem skTopK (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Xs.XsTopK S :=
  fun hν => _root_.R2Skel.SkE.skTopK (skWallCF S) hν

/-- STATUS: REDUCED (round 124; was OPEN: skWallCF, skTopK; Xs.xsFarLow, Xs.xsMove)
SIZE: M
`hν ⇒ ∀ window λ, m_λ > M_W, Θ_λ(m_λ) < δ_λ·ω : B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})`: the codes `M_W < m_λ < K_ω` move by
`Xs.xsMove` (block readings `Xs.xsBlk` at λ and λ', `Ld.ldB_psi_add`, `Ld.ldGxStepRec` with the bound `K_{J+1}`;
atoms below `θ⁺` by the wall), the codes `m_λ ≥ K_ω` by `skTopK`.  Checkable only after the merge. -/
theorem skThFar (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → FarLowMove S :=
  fun hν => Xs.xsFarLow (skWallCF S hν) (Xs.xsFarHi_of_top (skTopK S hν))

/-- STATUS: REDUCED (skThMid, skThFar)
SIZE: L
`hν ⇒ WdThHi`: codes θ⁺ ≤ m ≤ M_W (RnThMoveM) and m > M_W read below δ_λ·ω. -/
theorem skThHi (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThHi S := by
  intro hν n l l' hR h1 hr hl' hB hm hP hw
  by_cases hM : cdCode S l ≤ Rn.rnMW S
  · exact skThMid S hν n l l' hR h1 hr hl' hB hm hP hM
  · exact skThFar S hν n l l' hR h1 hr hl' hB hm (not_le.1 hM) hw

/-- STATUS: REDUCED (skLowExp, skBelowThP, skWall, skThHi)
SIZE: L
**Top node** `hν ⇒ Wd.WdThLow`: `B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` at every window code read below `δ_λ·ω`
(split: e(η_λ) ≤ Γ | m_λ < θ⁺ | m_λ ≥ θ⁺).  This is the hypothesis `hT` of `Wd.wdRoadL`. -/
theorem skRead (S : InaccSeq.{0}) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S := by
  intro hν n l l' hR h1 hr hl' hB hm hw
  by_cases he : cdExp (cdEta S l) ≤ ggGam
  · exact skLowExp S hν n l l' hR h1 hr hl' hB hm he hw
  · by_cases hP : cdCode S l < Lj.ljThP S
    · exact skBelowThP S (skWall S hν) n l l' hR h1 hr hl' hB hm (not_le.1 he) hP
    · exact skThHi S hν n l l' hR h1 hr hl' hB hm (not_lt.1 hP) hw

/-- STATUS: PROVED (Wd.wdRoadL_hyps)
SIZE: S
Non-vacuity: `CdEQ ⇒ (hν ⇒ WdThLow)` (the top node follows from the road's own conclusion). -/
theorem skRead_of_EQ (S : InaccSeq.{0}) (hEQ : Cd.CdEQ S) : Nc.ncL S (ω + 1) ≤ nuC → Wd.WdThLow S :=
  (Wd.wdRoadL_hyps hEQ).1

/-- STATUS: PROVED (Wd.wdRoad_hyps, Wd.wdRn_of, Wd.wdRoadL_hyps)
SIZE: S
Non-vacuity of the OPEN conclusions: `CdEQ ∧ (hν ⇒ UdAtMove25) ⇒ (hν ⇒ WdAtWall) ∧ (hν ⇒ RnThMoveM) ∧ (hν ⇒ FarLowMove)`
(the natural target implies the conclusions of skWall, skMidAssemble, skThFar; no node asks more than the road). -/
theorem skNonVac (S : InaccSeq.{0}) (hEQ : Cd.CdEQ S) (hat : Nc.ncL S (ω + 1) ≤ nuC → Ud.UdAtMove25 S) :
    (Nc.ncL S (ω + 1) ≤ nuC → Wd.WdAtWall S) ∧ (Nc.ncL S (ω + 1) ≤ nuC → Rn.RnThMoveM S) ∧
      (Nc.ncL S (ω + 1) ≤ nuC → FarLowMove S) := by
  obtain ⟨hW, hH, hF⟩ := Wd.wdRoad_hyps hEQ hat
  refine ⟨hW, fun hν => (Wd.wdRn_of hν (hH hν) (hF hν)).1, fun hν => ?_⟩
  intro n l l' hR h1 hr hl' hB hm _ hw
  exact (Wd.wdRoadL_hyps hEQ).1 hν n l l' hR h1 hr hl' hB hm hw

/-! ## Round 124 (leaf far1): the readings past `M_W` -/

/-- STATUS: PROVED (Xs.xsBase, from Wl.wlThVal, Ld.ldBlk_next, Ld.ldAtom_le, Ld.ldPsi1_le, Le.leDivOp_mem; NEW round 124;
checkable only after the merge)
SIZE: L
`restart λ, A_{η_λ} own, Ω_ω + Ω₂·Ω₂ ≤ A, γ < Ω₂ a code whose codes γ' ≤ γ satisfy γ' < ψ₂(Ω_ω + Ω₂·γ') ⇒
Θ(ψ₂(Ω_ω + Ω₂·γ)) = ψ₁(A + θ + Ω₁·Θ γ)` (successors by the next base, limits by cofinality). -/
theorem skXsBase (S : InaccSeq.{0}) {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (hAb : Om ω + Om (1 + 1) * Om (1 + 1) ≤ ConjT.Aη S (cdEta S l)) :
    ∀ γ, GxCl (upsilon l) (ldAtR S l) γ → γ < Om (1 + 1) →
      (∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' ≤ γ → Xs.XsOwn S γ') →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Xs.xsB γ) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ) (Om 1) :=
  Xs.xsBase hl hX hown hAb

/-- STATUS: PROVED (Xs.xsBlk, from skXsBase, Ld.ldBlk_step; NEW round 124; checkable only after the merge)
SIZE: S
the block law above every own base: `Θ(ψ₂(Ω_ω + Ω₂·γ + c)) = ψ₁(A + θ + Ω₁·Θ γ + Θ c)` for codes `c < ψ₂(Ω_ω + Ω₂·(γ+1))`. -/
theorem skXsBlk (S : InaccSeq.{0}) {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
    (hown : ConjT.Aη S (cdEta S l) ∈
      S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
    (hAb : Om ω + Om (1 + 1) * Om (1 + 1) ≤ ConjT.Aη S (cdEta S l)) {γ : Ordinal.{0}}
    (hγ : GxCl (upsilon l) (ldAtR S l) γ) (hγ2 : γ < Om (1 + 1))
    (hown' : ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' ≤ γ → Xs.XsOwn S γ') :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S (Xs.xsB γ) →
      gxTh (upsilon l) (ldAtR S l) (S.psi (Xs.xsB γ + c) (Om (1 + 1))) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1 * gxTh (upsilon l) (ldAtR S l) γ +
          gxTh (upsilon l) (ldAtR S l) c) (Om 1) :=
  Xs.xsBlk hl hX hown hAb hγ hγ2 hown'

/-- STATUS: PROVED (Xs.xsMove, from Xs.xsAtMove, Xs.xsAt_cls, Wr.wrAtLow, Ld.ldGxStepRec; NEW round 124; checkable only
after the merge)
SIZE: M
`Wr.WrWallCF ⇒ ∀ J, ∀ window, θ⁺ ≤ m_λ < K_{J+1} ⇒ B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})`. -/
theorem skXsMove (S : InaccSeq.{0}) (hW : Wr.WrWallCF S) (J : ℕ) :
    ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
      Lj.ljThP S ≤ cdCode S l → cdCode S l < Xs.xsK S (J + 1) →
      Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') :=
  Xs.xsMove hW J

end Googology.Trans.PoR.InaccPsi.R2Skel.SkR
