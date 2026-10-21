import Googology.Trans.PoR.InaccPsi.R2.LqPP
import Googology.Trans.PoR.InaccPsi.R2.PhLy
import Googology.Trans.PoR.InaccPsi.R2.FpLev

/-!
# Exponents in `x` over `Γ`: the layer `lyBig lgLay` (terms `Σ ω^{Γ(x) + dᵢ(x)}·kᵢ + s(x)`, top `Γ(x)·B(x)`)

`lqBig = Ly.lyBig lgLay` (`R2.LyBig` with the layer `lgLay` of `R2.LgLay`, `E(x) = Γ(x)`; the exponent terms `dᵢ` are
the `VzTm` terms, `φ(n, ·)`-terms below `B(x) = VzB x`): top `ω^{Γ(x) + B(x)} = Γ(x)·B(x)`, codes below
`ω^{Γ_{Ω₁+1} + phB}` (`phB = φ(ω, Ω₁ + 1)`, `Θ_y(phB) = B(y)`).  It contains every `lqPP n` of `R2.LqPP`
(`x^{x·(n+1)} = ω^{x·x·(n+1)}`, `x·x·(n+1) < B(x)`).

* `lqBig_EB` (**`B(x) ≤ Γ(x)`**, by `lgVt_lt_low`: every `ϑˣ(Ω₁·N) < ϑˣ(Ω₁·Ω₁) = Γ(x)`);
* `lqVzTm`, `lqGt_of_ref` (the order of two `VzTm` exponents at one `υ`-point base above their constants is their
  order at every such base, `uniVz_lt`), `lqCNFVz` (**the Cantor normal form of a code `g < ω^{phB}` as a `VzTm`
  exponent list**: `ω^{Γ(y)}·Θ_y(g) = Σ ω^{Γ(y) + dᵢ(y)}·kᵢ`, as `Ph.phCNFTm`);
* `lqBigPoly`, `lqBigTop` (**`LgPoly (lyBig K) (ω^{e + phB})`** for every layer `K` with `LgPoly K (ω^e)` and
  `E_K = Θ'(e)`: `c = ω^e·g + r`, the list of `g` and the `K` term of `r`; top `Θ'_y(ω^{e + phB})`), `lqBig_poly`,
  `lqBig_top` (`K = lgLay`, `e = Γ_{Ω₁+1}`: top `Γ(y)·B(y) = Θ'_y(ω^{Γ_{Ω₁+1} + phB})`);
* `lqBig_loc` (**`Λ⁺(lqBig) = ι(ω^{ω^{Γ_{Ω₁+1} + phB}}·ω)`, `ρ` of it `= P(…) < L(0)`**), `lqBigT_fix`, `lqBigEnum`
  (**ENUM-REACH at every restart of the range below `Λ⁺(lqBig)`**, fixed points included), `lqBig_capV`,
  `lqBig_blk`, `lqBigRoadPh`, `lqFamP_le_Big` (`sup_n Λ⁺(lqPP n) ≤ Λ⁺(lqBig)`), `lqBig_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Nm

/-! ## The layer -/

/-- **`B(x) ≤ Γ(x)`**: every `ϑˣ(Ω₁·N) < ϑˣ(Ω₁·Ω₁) = Γ(x)`. -/
theorem lqBig_EB : ∀ x, InE x → x < Om1 → VzB x ≤ lgLay.E x := by
  intro x hx hx1
  show (⨆ N : ℕ, vt x (Om1 * (N : Ordinal.{0}) + 0)) ≤ lgG x
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have hG : vt x (Om1 * Om1 + 0) = lgG x := by rw [add_zero, ← lgV_eq hx hx1]; rfl
  have hGE := lgG_inE x hx hx1
  refine Ordinal.iSup_le fun N => ?_
  have hNx : (N : Ordinal.{0}) < x := (natCast_lt_omega0 N).trans (omega0_lt_inE hx)
  have hNT : (N : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 hNx.le
  have hN1 : (N : Ordinal.{0}) < Om1 := hNx.trans hx1
  have hNG : (N : Ordinal.{0}) < vt x (Om1 * Om1 + 0) := by
    rw [hG]; exact (natCast_lt_omega0 N).trans (omega0_lt_inE hGE)
  have h0G : (0 : Ordinal.{0}) < vt x (Om1 * Om1 + 0) := by rw [hG]; exact hGE.pos
  have := lgVt_lt_low hx hx1 hNT hN1 h0T h0Ω h0T h0Ω hNG h0G
  rw [hG] at this
  exact this.le

/-- **The layer `lyBig lgLay`** (top `Γ(x)·B(x) = ω^{Γ(x) + B(x)}`). -/
noncomputable def lqBig : XtLay := lyBig lgLay lqBig_EB

theorem lqBig_top_eq (x : Ordinal.{0}) : lqBig.sys.top x = ω ^ (lgG x + VzB x) := rfl

/-! ## Codes -/

variable {Z : Ordinal.{0}}

theorem lqVzTm (_hZ : SC Z) {d : Ordinal.{0}} (hd : GgCl Z d) (hdB : d < phB) :
    ∃ t : VzTm, ∀ y, SC y → y < Om 1 → Z ≤ y → t.CBt y ∧ t.val y = ggTh y d :=
  phPoly_vz Z d hd hdB

/-- **The order of two exponent terms at one `υ`-point base above their constants is their order at every `υ`-point
base above their constants** (`uniVz_lt`). -/
theorem lqGt_of_ref {t u : VzTm} {k k' ρ : Ordinal.{0}} (hρU : UpsPt ρ) (hρ1 : ρ < Om1) (ht : t.CBt ρ)
    (hu : u.CBt ρ) (hlt : u.val ρ < t.val ρ) : Ly.LyGt (t, k) (u, k') := by
  intro y hyU hy1 hct hcu
  have hty : t.CBt y := VzTm.cbt_iff t ρ y ht hct
  have huy : u.CBt y := VzTm.cbt_iff u ρ y hu hcu
  rcases lt_trichotomy y ρ with h | rfl | h
  · exact (uniVz_lt hyU hρU ⟨upsPt_inE hyU, upsPt_inE hρU, h, hρ1⟩ huy hty).1 hlt
  · exact hlt
  · exact (uniVz_lt hρU hyU ⟨upsPt_inE hρU, upsPt_inE hyU, h, hy1⟩ hu ht).2 hlt

/-- **The Cantor normal form of a code `g < ω^U` (`U ≤ phB`) as a `VzTm` exponent list.** -/
theorem lqCNFVz (K : XtLay) (hZ : SC Z) {ρ : Ordinal.{0}} (hρU : UpsPt ρ) (hρS : SC ρ) (hρ1 : ρ < Om 1) (hZρ : Z ≤ ρ) :
    ∀ g, GgCl Z g → ∀ U, U ≤ phB → g < ω ^ U →
      ∃ ps : List (VzTm × Ordinal.{0}), ps.Pairwise Ly.LyGt ∧
        (∀ q ∈ ps, (∃ d, GgCl Z d ∧ d < U ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → q.1.CBt y ∧ q.1.val y = ggTh y d) ∧
          0 < q.2 ∧ q.2 < ω) ∧
        ∀ y, SC y → y < Om 1 → Z ≤ y → Ly.lbSum K y ps = ω ^ K.E y * ggTh y g := by
  have hρ1' : ρ < Om1 := by rw [ph_Om1_eq]; exact hρ1
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg U hU hgU
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨[], List.Pairwise.nil, fun q hq => absurd hq (List.not_mem_nil), fun y _ _ _ => by
      rw [phTh_zero, mul_zero]; rfl⟩
  obtain ⟨hsub, hlog⟩ := ggDec hZ g hg
  set L := log ω g with hLdef
  have hLU : L < U := (lt_opow_iff_log_lt one_lt_omega0 hg0).1 hgU
  have hT0 : ω ^ L ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hk : g / ω ^ L < ω := by
    refine (Ordinal.lt_mul_iff_div_lt hT0).1 ?_
    have := lt_opow_succ_log_self one_lt_omega0 g
    rwa [opow_succ] at this
  obtain ⟨n, hn⟩ := lt_omega0.1 hk
  have hn0 : 0 < n := by
    have h1 : (1 : Ordinal.{0}) ≤ g / ω ^ L :=
      (Ordinal.mul_le_iff_le_div hT0).1 (by rw [mul_one]; exact opow_log_le_self ω hg0)
    rw [hn] at h1; exact_mod_cast h1
  have hgdec : ω ^ L * n + g % ω ^ L = g := by rw [← hn]; exact div_add_mod g _
  have hwn : GgCl Z (ω ^ L * n) := GgCl.mul_nat hZ.1 (GgCl.opow hZ.1 hlog) n
  have hr : GgCl Z (g % ω ^ L) := by
    have := hsub _ hwn (by rw [← hgdec]; exact le_self_add)
    rwa [Ordinal.sub_eq_of_add_eq hgdec] at this
  have hrL : g % ω ^ L < ω ^ L := mod_lt g hT0
  have hrg : g % ω ^ L < g := hrL.trans_le (opow_log_le_self ω hg0)
  obtain ⟨ps, hpw, hps, hsum⟩ := IH _ hrg hr L (hLU.le.trans hU) hrL
  obtain ⟨t, ht⟩ := lqVzTm hZ hlog (hLU.trans_le hU)
  obtain ⟨htρ, htv⟩ := ht ρ hρS hρ1 hZρ
  refine ⟨(t, (n : Ordinal.{0})) :: ps, List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩, fun q hq => ?_,
    fun y hy hy1 hZy => ?_⟩
  · obtain ⟨⟨d, hd, hdL, hdv⟩, -⟩ := hps q hq
    obtain ⟨hqρ, hqv⟩ := hdv ρ hρS hρ1 hZρ
    refine lqGt_of_ref hρU hρ1' htρ hqρ ?_
    rw [hqv, htv]; exact ggTh_lt (hd.mono hZρ) hdL
  · rcases List.mem_cons.1 hq with rfl | hq'
    · exact ⟨⟨L, hlog, hLU, ht⟩, show (0 : Ordinal.{0}) < (n : Ordinal.{0}) by exact_mod_cast hn0,
        natCast_lt_omega0 n⟩
    · obtain ⟨⟨d, hd, hdL, hdv⟩, h2⟩ := hps q hq'
      exact ⟨⟨d, hd, hdL.trans hLU, hdv⟩, h2⟩
  · obtain ⟨-, htv'⟩ := ht y hy hy1 hZy
    have hly := hlog.mono hZy
    rw [Ly.lbSum_cons, hsum y hy hy1 hZy]
    show ω ^ (K.E y + t.val y) * (n : Ordinal.{0}) + ω ^ K.E y * ggTh y (g % ω ^ L) = ω ^ K.E y * ggTh y g
    conv_rhs => rw [← hgdec]
    rw [ggTh_add hy (hwn.mono hZy), phTh_opow_mul hy hly _ (ph_cl_nat hy n), phTh_nat hy, htv', mul_add,
      opow_add, mul_assoc]

theorem lq_B_lt_Gam : phB < ggGam := ph_lt_Gam (ph_cl_B ph_SC_Om1)

/-- The exponent `Γ_{Ω₁+1} + phB` of the top code of `lqBig`. -/
noncomputable def lqBe : Ordinal.{0} := ggGam + phB

theorem lq_cl_Be {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z lqBe := LgCl.add LgCl.gam (lgCl_of_GgCl (ph_cl_B hZ))

theorem lqLay_poly : LgPoly lgLay.sys (ω ^ ggGam) := by
  have h0 := lgPoly_LL 0
  have e0 : lgLLe 0 = ggGam := by rw [lgLLe, Nat.cast_zero, mul_zero, add_zero]
  rw [e0] at h0
  exact h0.1

/-- **`lyBig K` has terms for every code below `ω^{e + phB}`** when `K` has terms for the codes below `ω^e`, `E_K(y) =
Θ'_y(e)` and `e` is a code over every strongly critical `Z`. -/
theorem lqBigPoly (K : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ K.E x) {e : Ordinal.{0}}
    (he : ∀ Z, SC Z → LgCl Z e) (hE : ∀ y, SC y → y < Om 1 → K.E y = lgTh y e) (hP : LgPoly K.sys (ω ^ e)) :
    LgPoly (lyBig K hEB).sys (ω ^ (e + phB)) := by
  refine lgPoly_of_SC fun Z hZ hZ1 c hc hcE => ?_
  obtain ⟨ρ, hρU, hρS, hρ1, hZρ⟩ := Fp.fpRef hZ1
  obtain ⟨g, r, hg, hr, hre, hcgr⟩ := lgDivCode hZ (he Z hZ) c hc
  have hgw : g < ω ^ phB := by
    have h1 : ω ^ e * g < ω ^ e * ω ^ phB := by
      calc ω ^ e * g ≤ c := by rw [hcgr]; exact le_self_add
        _ < ω ^ (e + phB) := hcE
        _ = ω ^ e * ω ^ phB := by rw [opow_add]
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 h1
  have hgB : g < ggGam := by rw [ph_B_eps] at hgw; exact hgw.trans lq_B_lt_Gam
  have hgG : GgCl Z g := lgCl_lt_Gam hg hgB
  obtain ⟨ps, hpw, hps, hsum⟩ := lqCNFVz K hZ hρU hρS hρ1 hZρ g hgG phB le_rfl hgw
  obtain ⟨s, hs⟩ := hP Z r hr hre
  refine ⟨(ps, s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨hpw, fun q hq => ⟨((hps q hq).1.choose_spec.2.2 y hy hy1 hZy).1, (hps q hq).2⟩, h1⟩, ?_⟩
  show Ly.lbVal K (ps, s) y = lgTh y c
  unfold Ly.lbVal
  have hgy := hg.mono hZy
  have hey := he y hy
  rw [hsum y hy hy1 hZy, show K.sys.val s y = lgTh y r from h2, hcgr,
    lgTh_add hy (lg_cl_opow_mul hy hey g hgy), lgTh_opow_mul hy hey g hgy, ← hE y hy hy1,
    lgTh_eq_ggTh hgB.le]

/-- The top of `lyBig K`: `ω^{E_K(y) + B(y)} = Θ'_y(ω^{e + phB})`. -/
theorem lqBigTop (K : XtLay) (hEB : ∀ x, InE x → x < Om1 → VzB x ≤ K.E x) {e : Ordinal.{0}}
    (he : ∀ Z, SC Z → LgCl Z e) (hE : ∀ y, SC y → y < Om 1 → K.E y = lgTh y e) :
    ∀ y, SC y → y < Om 1 → (lyBig K hEB).sys.top y = lgTh y (ω ^ (e + phB)) := by
  intro y hy hy1
  rw [lyBig_top, lgTh_opow hy (LgCl.add (he y hy) (lgCl_of_GgCl (ph_cl_B hy))), lgTh_add hy (he y hy),
    ← hE y hy hy1, lgTh_eq_ggTh lq_B_lt_Gam.le, phTh_B hy hy1]

/-- **`lqBig` has terms for every code below `ω^{Γ_{Ω₁+1} + phB}`.** -/
theorem lqBig_poly : LgPoly lqBig.sys (ω ^ lqBe) :=
  lqBigPoly lgLay lqBig_EB (fun _ _ => LgCl.gam) (fun y hy hy1 => (lgTh_Gam hy hy1).symm) lqLay_poly

/-- The top of `lqBig`: `Γ(y)·B(y) = Θ'_y(ω^{Γ_{Ω₁+1} + phB})`. -/
theorem lqBig_top : ∀ y, SC y → y < Om 1 → lqBig.sys.top y = lgTh y (ω ^ lqBe) :=
  lqBigTop lgLay lqBig_EB (fun _ _ => LgCl.gam) (fun y hy hy1 => (lgTh_Gam hy hy1).symm)

theorem lq_cl_Big {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ lqBe) := LgCl.opow hZ.1 (lq_cl_Be hZ)

theorem lq_Om1_le_Big : Om 1 ≤ ω ^ lqBe :=
  ggGam_spec.2.le.trans (lg_Gam_eps.symm.le.trans (opow_le_opow_right omega0_pos le_self_add))

theorem lqBig_topE (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < lqBig.sys.top x := by
  rw [lqBig_top_eq]
  have hGE : ω ^ lgG x = lgG x := lgG_inE x hx hx1
  refine (gT_lt_lgG hx hx1 0).trans_le ?_
  calc lgG x = ω ^ lgG x := hGE.symm
    _ ≤ ω ^ (lgG x + VzB x) := opow_le_opow_right omega0_pos le_self_add

variable {S : InaccSeq.{0}}

theorem lq_Big_le_Gam' (S : InaccSeq.{0}) : ω ^ lqBe ≤ lgGam' := (lgCl_lt_Gam' S (lq_cl_Big ph_SC_Om1)).le

/-- **`Λ⁺(lqBig) = ι(ω^{ω^{Γ_{Ω₁+1} + phB}}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lqBig_loc : xtB1 lqBig.sys = iota S (ω ^ ω ^ lqBe * ω) ∧
    upsilon (xtB1 lqBig.sys) = Pv S (ω ^ ω ^ lqBe * ω) ∧ Pv S (ω ^ ω ^ lqBe * ω) < Nc.ncL S 0 :=
  lgB1_eq2 (lq_Big_le_Gam' S) lqBig_poly lqBig_top (fun _ hZ => lq_cl_Big hZ) lq_Om1_le_Big lqBig_topE
    lqBig.topPkg

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lqBig)`.** -/
theorem lqBigT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lqBig.sys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lqBig.sys l := by
  have hlt : l < iota S (ω ^ ω ^ lqBe * ω) := by rw [← (lqBig_loc (S := S)).1]; exact hlB
  exact lgUniTh (lq_Big_le_Gam' S) lqBig_poly hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem lqBig_nonfix : XtNonfix (xtOrec lqBig.sys) (xtB1 lqBig.sys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lqBig.topPkg))

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lqBig)`**, fixed points of `υ` included. -/
theorem lqBigEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lqBig.sys) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 lqBig.topPkg) lqBig_nonfix hr hl hnf
  · exact (xtExact_iff (xtSpec1 lqBig.topPkg) hr.1 hl).2 (lqBigT_fix hr hl hfx.symm)

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lqBig)`.** -/
theorem lqBig_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lqBig.sys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lqBig.topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1) (lqBig_nonfix l hr.1 hww hfix hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(lqBig)}`** in `R₂^C`. -/
theorem lqBig_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lqBig.sys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lqBig.sys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lqBig.sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lqBig.sys l)) ∧
    (∀ α < upsilon (xtB1 lqBig.sys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lqBig.topPkg

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lqBig)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lqBigRoadPh (hU : ∀ l, CdRange S l → xtB1 lqBig.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lqBig.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lqBig.sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lqBig.topPkg) lqBig_nonfix hU hL (fun _ hr hlB hfix => lqBigT_fix hr hlB hfix) hV hC hEQ hrest hB2

/-- `Γ_{Ω₁+1} + Ω₁·Ω₁·ω < Γ_{Ω₁+1} + phB`. -/
theorem lq_PPw_lt_Be : lqPPw < lqBe := by
  unfold lqPPw lqBe
  refine (add_lt_add_iff_left _).2 ?_
  have hBE : ω ^ phB = phB := ph_B_eps
  have hO : Om 1 < phB := (lt_add_one (Om 1)).trans_le (right_le_veblen _ _)
  have hBI : Indec phB := inE_indec hBE
  have h3 : Om 1 + Om 1 + 1 < phB :=
    hBI.add_lt (hBI.add_lt hO hO) ((one_lt_omega0.trans (omega0_lt_inE hBE)))
  rw [show Om 1 * Om 1 * ω = ω ^ (Om 1 + Om 1 + 1) by rw [opow_add, opow_add, opow_one, Om1_opow]]
  rw [← hBE]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 h3

/-- **`sup_n Λ⁺(lqPP n) ≤ Λ⁺(lqBig)`.** -/
theorem lqFamP_le_Big (S : InaccSeq.{0}) : lqFamP.famSup ≤ xtB1 lqBig.sys := by
  rw [(lqFamP_loc (S := S)).1, (lqBig_loc (S := S)).1]
  refine iota_mono _ _ ?_
  have h1 : ω ^ lqPPw ≤ ω ^ lqBe := opow_le_opow_right omega0_pos lq_PPw_lt_Be.le
  calc ω ^ ω ^ lqPPw ≤ ω ^ ω ^ lqBe := opow_le_opow_right omega0_pos h1
    _ ≤ ω ^ ω ^ lqBe * ω := le_mul_of_one_le_right zero_le one_lt_omega0.le

/-- **Where `Λ⁺(lqBig)` lies**: `ρ(sup_n Λ⁺(lqPP n)) ≤ ρ(Λ⁺(lqBig)) = P(ω^{ω^{Γ_{Ω₁+1}+phB}}·ω) < L(0) = m* ≤ L(k+1) <
L(ω) < L(ω+1)`, and `Λ⁺(lqBig) < L(ω+1)`, unconditionally. -/
theorem lqBig_fr_order (k : ℕ) :
    upsilon lqFamP.famSup ≤ upsilon (xtB1 lqBig.sys) ∧ upsilon (xtB1 lqBig.sys) < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lqBig.sys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lqBig_loc (S := S)
  have hU : upsilon (xtB1 lqBig.sys) < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono.monotone (lqFamP_le_Big S), hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
