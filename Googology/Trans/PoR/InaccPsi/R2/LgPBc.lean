import Googology.Trans.PoR.InaccPsi.R2.LgPB

/-!
# Terms for the codes of the layer of all constant exponents, and `Λ⁺(lgPB) = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·Ω₁}}·ω)`

For a layer `L` (`R2.XtLay`) with terms for the codes below `ω^e` and top `Θ'_y(ω^e)` (`R2.LgPh`), the layer
`lyPoly L` (`R2.LyPoly`: terms `T(x)·Σ x^{aᵢ}·γᵢ + s(x)`, top `T(x)·x^x`) has terms for the codes below
`ω^{e + Ω₁·Ω₁}`:

* `lgTh_Om1_mul` (`Θ'_y(Ω₁·a) = y·a`), `lgTh_Om1_pow` (`Θ'_y(ω^{Ω₁·a}·γ) = y^a·γ` for constants `a, γ < y`);
* `lgCNF` (**the base-`Ω₁` normal form of a code `g < ω^{Ω₁·b}` as an exponent list**: `Θ'_y(g) = Σ y^{aᵢ}·γᵢ`, the
  `aᵢ, γᵢ` constants below `Z`, exponents decreasing and `< b`);
* `lgPoly_poly`, `lgTop_poly` (**`LgPoly (lyPoly L).sys (ω^{e + Ω₁·Ω₁})`**, top `Θ'_y(ω^{e + Ω₁·Ω₁})`);
* the instance `lgPB`: `lgPB_loc` (**`Λ⁺(lgPB) = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·Ω₁}}·ω)`, `ρ` of it `< L(0)`**), `lgPBT_fix`
  (**the notation hypothesis at every fixed point of the range below `Λ⁺(lgPB)`**), `lgPBEnum` (**ENUM-REACH at every
  restart of the range below `Λ⁺(lgPB)`**), `lgPBRoadPh` (**the road with UPPER/LOWER asked only at `λ ≥ Λ⁺(lgPB)`**),
  `lgPB_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Ly
  Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Nm

variable {Z y : Ordinal.{0}}

theorem lg_Om1_code_eq : ω ^ Om (1 : Ordinal.{0}) = Om 1 := Om1_opow

/-- `Θ'_y(Ω₁·a) = y·a` for a code `a`. -/
theorem lgTh_Om1_mul (hy : SC y) (hy1 : y < Om 1) {a : Ordinal.{0}} (ha : LgCl y a) :
    lgTh y (Om 1 * a) = y * lgTh y a := by
  have h := lgTh_opow_mul hy LgCl.om a ha
  rwa [lg_Om1_code_eq, lgTh_Om1 hy hy1, gg_SC_eps hy] at h

theorem lg_cl_Om1_mul {a : Ordinal.{0}} (hZ : SC Z) (ha : LgCl Z a) : LgCl Z (Om 1 * a) := by
  have h := lg_cl_opow_mul hZ LgCl.om a ha
  rwa [lg_Om1_code_eq] at h

/-- `Θ'_y(ω^{Ω₁·a}·γ) = y^a·γ` for constants `a, γ < y`. -/
theorem lgTh_Om1_pow (hy : SC y) (hy1 : y < Om 1) {a γ : Ordinal.{0}} (ha : a < y) (hγ : γ < y) :
    lgTh y (ω ^ (Om 1 * a) * γ) = y ^ a * γ := by
  have hac : LgCl y a := LgCl.small ha
  rw [lgTh_opow_mul hy (lg_cl_Om1_mul hy hac) γ (LgCl.small hγ), lgTh_Om1_mul hy hy1 hac, lgTh_small ha.le,
    lgTh_small hγ.le, opow_mul, gg_SC_eps hy]

/-- **The base-`Ω₁` normal form of a code** `g < ω^{Ω₁·b}` (`b ≤ Ω₁`) over a strongly critical `Z < Ω₁`. -/
theorem lgCNF (hZ : SC Z) (hZ1 : Z < Om 1) : ∀ g, LgCl Z g → ∀ b, b ≤ Om 1 → g < ω ^ (Om 1 * b) →
    ∃ ps : List (Ordinal.{0} × Ordinal.{0}), LyNF ps ∧ (∀ p ∈ ps, p.1 < Z ∧ p.2 < Z) ∧ (∀ p ∈ ps, p.1 < b) ∧
      ∀ y, SC y → y < Om 1 → Z ≤ y → lyPv y ps = lgTh y g := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg b hb hgb
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨[], ⟨List.Pairwise.nil, by simp⟩, by simp, by simp, fun y _ _ _ => by rw [lyPv_nil, lgTh_zero]⟩
  -- the leading exponent
  obtain ⟨-, hL⟩ := lgDec hZ g hg
  set L := log ω g with hLdef
  obtain ⟨a, r', ha, hr', hr'1, hLe⟩ := lgDivCode hZ LgCl.om L hL
  rw [lg_Om1_code_eq] at hr'1 hLe
  have hLb : L < Om 1 * b := (lt_opow_iff_log_lt one_lt_omega0 hg0).1 hgb
  have hab : a < b := by
    have : Om 1 * a < Om 1 * b := (le_self_add.trans_eq hLe.symm).trans_lt hLb
    exact (mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).1 this
  have haZ : a < Z := ha.lt_of_lt_Om1 hZ (hab.trans_le hb)
  -- divide `g` by `ω^{Ω₁·a}`
  have hea : LgCl Z (Om 1 * a) := lg_cl_Om1_mul hZ ha
  obtain ⟨γ, g', hγ, hg', hg'a, hge⟩ := lgDivCode hZ hea g hg
  have hle : ω ^ (Om 1 * a) ≤ g := by
    calc ω ^ (Om 1 * a) ≤ ω ^ L := opow_le_opow_right omega0_pos (by rw [hLe]; exact le_self_add)
      _ ≤ g := opow_log_le_self ω hg0
  have hgw : g < ω ^ (Om 1 * a) * Om 1 := by
    calc g < ω ^ Order.succ L := lt_opow_succ_log_self one_lt_omega0 g
      _ ≤ ω ^ (Om 1 * a + Om 1) := opow_le_opow_right omega0_pos (by
          rw [Order.succ_eq_add_one, hLe, add_assoc]
          exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hr'1))
      _ = ω ^ (Om 1 * a) * Om 1 := by rw [opow_add, lg_Om1_code_eq]
  have hγ1 : γ < Om 1 := by
    have : ω ^ (Om 1 * a) * γ < ω ^ (Om 1 * a) * Om 1 := (le_self_add.trans_eq hge.symm).trans_lt hgw
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 this
  have hγZ : γ < Z := hγ.lt_of_lt_Om1 hZ hγ1
  have hγ0 : 0 < γ := by
    rcases eq_or_ne γ 0 with h0 | h0
    · exfalso
      rw [h0, mul_zero, zero_add] at hge
      exact absurd hle (not_le.2 (hge ▸ hg'a))
    · exact pos_iff_ne_zero.2 h0
  have hg'g : g' < g := hg'a.trans_le hle
  obtain ⟨ps, hN, hB, hlt, hv⟩ := IH g' hg'g hg' a (hab.le.trans hb) hg'a
  refine ⟨(a, γ) :: ps, ⟨List.pairwise_cons.2 ⟨fun q hq => hlt q hq, hN.1⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hγ0
    · exact hN.2 q hq
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨haZ, hγZ⟩
    · exact hB q hq
  · intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hab
    · exact (hlt q hq).trans hab
  · intro y hy hy1 hZy
    rw [lyPv_cons, hv y hy hy1 hZy, hge, lgTh_add hy (lg_cl_opow_mul hy (hea.mono hZy) γ (hγ.mono hZy)),
      lgTh_Om1_pow hy hy1 (haZ.trans_le hZy) (hγZ.trans_le hZy)]

/-- **The layer of all constant exponents has terms for every code below `ω^{e + Ω₁·Ω₁}`.** -/
theorem lgPoly_poly (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) (hP : LgPoly L.sys (ω ^ e)) :
    LgPoly (lyPoly L).sys (ω ^ (e + Om 1 * Om 1)) := by
  refine lgPoly_of_SC fun Z hZ hZ1 c hc hcE => ?_
  obtain ⟨g, r, hg, hr, hre, hcgr⟩ := lgDivCode hZ (he Z hZ) c hc
  have hgw : g < ω ^ (Om 1 * Om 1) := by
    have h1 : ω ^ e * g < ω ^ e * ω ^ (Om 1 * Om 1) := by
      calc ω ^ e * g ≤ c := by rw [hcgr]; exact le_self_add
        _ < ω ^ (e + Om 1 * Om 1) := hcE
        _ = ω ^ e * ω ^ (Om 1 * Om 1) := by rw [opow_add]
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 h1
  obtain ⟨ps, hN, hB, -, hv⟩ := lgCNF hZ hZ1 g hg (Om 1) le_rfl hgw
  obtain ⟨s, hs⟩ := hP Z r hr hre
  refine ⟨(ps, s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨hN, fun p hp => ⟨(hB p hp).1.trans_le hZy, (hB p hp).2.trans_le hZy⟩, h1⟩, ?_⟩
  show L.sys.top y * lyPv y ps + L.sys.val s y = lgTh y c
  have hey := he y hy
  have hgy := hg.mono hZy
  rw [h2, htop y hy hy1, hv y hy hy1 hZy, hcgr, lgTh_add hy (lg_cl_opow_mul hy hey g hgy),
    lgTh_opow_mul hy hey g hgy, lgTh_opow hy hey]

/-- The top of the layer of all constant exponents: `T(y)·y^y = Θ'_y(ω^{e + Ω₁·Ω₁})`. -/
theorem lgTop_poly (L : XtLay) {e : Ordinal.{0}} (he : ∀ Z, SC Z → LgCl Z e)
    (htop : ∀ y, SC y → y < Om 1 → L.sys.top y = lgTh y (ω ^ e)) :
    ∀ y, SC y → y < Om 1 → (lyPoly L).sys.top y = lgTh y (ω ^ (e + Om 1 * Om 1)) := by
  intro y hy hy1
  show L.sys.top y * y ^ y = _
  have hOO : LgCl y (Om 1 * Om 1) := lg_cl_Om1_mul hy LgCl.om
  rw [htop y hy hy1, lgTh_opow hy (LgCl.add (he y hy) hOO), lgTh_add hy (he y hy), lgTh_Om1_mul hy hy1 LgCl.om,
    lgTh_Om1 hy hy1, opow_add, lgTh_opow hy (he y hy), opow_mul, gg_SC_eps hy]

/-! ## The instance `lgPB` -/

/-- The top code `ω^{Γ_{Ω₁+1} + Ω₁·Ω₁}` of `lgPB` (top `Γ(x)·x^x`). -/
noncomputable def lgPBe : Ordinal.{0} := ω ^ (ggGam + Om 1 * Om 1)

theorem lg_cl_PBe {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z lgPBe :=
  LgCl.opow hZ.1 (LgCl.add LgCl.gam (lg_cl_Om1_mul hZ LgCl.om))

theorem lgPB_poly : LgPoly lgPB.sys lgPBe ∧ ∀ y, SC y → y < Om 1 → lgPB.sys.top y = lgTh y lgPBe := by
  have h0 := lgPoly_LL 0
  have e0 : lgLLe 0 = ggGam := by rw [lgLLe, Nat.cast_zero, mul_zero, add_zero]
  rw [e0] at h0
  exact ⟨lgPoly_poly lgLay (fun _ _ => LgCl.gam) h0.2 h0.1, lgTop_poly lgLay (fun _ _ => LgCl.gam) h0.2⟩

theorem lg_Om1_le_PBe : Om 1 ≤ lgPBe :=
  ggGam_spec.2.le.trans (lg_Gam_eps.symm.le.trans (opow_le_opow_right omega0_pos le_self_add))

theorem lgPB_topE (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) : eN x < lgPB.sys.top x := by
  show eN x < lgG x * x ^ x
  exact (gT_lt_lgG hx hx1 0).trans_le (le_mul_of_one_le_right zero_le (one_le_iff_pos.2 (opow_pos _ hx.pos)))

variable {S : InaccSeq.{0}}

/-- **`Λ⁺(lgPB) = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·Ω₁}}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lgPB_loc : xtB1 lgPB.sys = iota S (ω ^ lgPBe * ω) ∧ upsilon (xtB1 lgPB.sys) = Pv S (ω ^ lgPBe * ω) ∧
    Pv S (ω ^ lgPBe * ω) < Nc.ncL S 0 :=
  lgB1_eq2 (lgCl_lt_Gam' S (lg_cl_PBe ph_SC_Om1)).le lgPB_poly.1 lgPB_poly.2 (fun _ hZ => lg_cl_PBe hZ)
    lg_Om1_le_PBe lgPB_topE lgPB.topPkg

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lgPB)`.** -/
theorem lgPBT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lgPB.sys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lgPB.sys l := by
  have hlt : l < iota S (ω ^ lgPBe * ω) := by rw [← (lgPB_loc (S := S)).1]; exact hlB
  exact lgUniTh (lgCl_lt_Gam' S (lg_cl_PBe ph_SC_Om1)).le lgPB_poly.1 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `Λ⁺(lgPB)`**, fixed points of `υ` (among them `Λ^Γ_{ω²}`)
included. -/
theorem lgPBEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lgPB.sys) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lgPB_init hr hl hnf
  · exact (lgPB_iff hr.1 hl).2 (lgPBT_fix hr hl hfx.symm)

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lgPB)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lgPBRoadPh (hU : ∀ l, CdRange S l → xtB1 lgPB.sys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lgPB.sys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lgPB.sys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lgPB.topPkg) lgPB_nonfix hU hL (fun _ hr hlB hfix => lgPBT_fix hr hlB hfix) hV hC hEQ hrest
    hB2

/-- **Where `Λ⁺(lgPB)` lies**: `ρ(Λ^Γ_{ω²}) < ρ(Λ⁺(lgPB)) = P(ω^{ω^{Γ_{Ω₁+1} + Ω₁·Ω₁}}·ω) < L(0) = m* ≤ L(k+1) < L(ω) <
L(ω+1)`, and `Λ⁺(lgPB) < L(ω+1)`, unconditionally. -/
theorem lgPB_fr_order (k : ℕ) :
    upsilon lgFamW2.famSup < upsilon (xtB1 lgPB.sys) ∧ upsilon (xtB1 lgPB.sys) < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lgPB.sys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lgPB_loc (S := S)
  have hU : upsilon (xtB1 lgPB.sys) < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono lgW2_lt_PB, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
