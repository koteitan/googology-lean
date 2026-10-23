import Googology.Trans.PoR.InaccPsi.R2.GdDFr

/-!
# The ladder over the diagonal: `Λ⁺(lpSys gdDB n) = ι(cQ(Γ_{Ω₁·2}) n·ω)` and `Λ^{gdDB} = ι(Γ_{Ω₁·2+1})`

The ladder `Lp.lpSys gdDB n` over the diagonal layer (stages `ϑˣ(Ω₁·…Γ_{x+x})`) reads the stage codes
`cQ(Γ_{Ω₁·2}) n` (`φ`-iterates of `Γ_{Ω₁·2}`); the terms for the codes come from the gated ladder of `R2.GdLd` over the
diagonal gated at `0`, read as terms of `Lp.LpT` (`gdToLp`, same values, constants, side conditions and stages):

* `gdToLp`, `gdToLp_val`, `gdToLp_noB`, `gdToLp_cbt`, `gdToLp_stage`, `gdP_ofLp` (**the gated ladder at gate `0` is the
  ladder of `R2.LpTm`**);
* `gdDL_poly` (**`GdPoly (lpSys gdDB n) (cQ(Γ_{Ω₁·2}) n)`**), `gdDL_top` (**`gP gdDB n y = Θ_y(cQ(Γ_{Ω₁·2}) n)`**);
* `gdDL_loc` (**`Λ⁺(lpSys gdDB n) = ι(cQ(Γ_{Ω₁·2}) n·ω)`, `ρ` of it `= P(…) < L(0)`**), `gdDL_fix`, `gdDL_enum`,
  `gdDL_capV` (**ENUM-REACH and CapV at every range restart below `Λ^{gdDB}`, fixed points included**),
  `gdDL_fam` (**`Λ^{gdDB} = sup_n Λ⁺(lpSys gdDB n) = ι(Γ_{Ω₁·2+1})`, `υ` of it `= P(Γ_{Ω₁·2+1}) < L(0)`**),
  `gdDL_road` (**the road with UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁·2+1})`**), `gdDL_order`.

No new axiom.  New definition: `gdToLp`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc

/-! ## The gated ladder at an ungated base is the ladder of `R2.LpTm` -/

/-- The terms of the gated ladder over an ungated base, read as terms of `Lp.LpT`. -/
def gdToLp {B : LpB} {g : Ordinal.{0}} : GdT (GdB.ofLp B g) → LpT B
  | .cst a => .cst a
  | .bs => .bs
  | .ak k => .ak k
  | .tp => .tp
  | .th0 b t => .th0 b (gdToLp t)
  | .tl l t => .tl (gdToLp l) (gdToLp t)
  | .sm a b => .sm (gdToLp a) (gdToLp b)
  | .pw t => .pw (gdToLp t)

variable {B : LpB} {g : Ordinal.{0}}

theorem gdToLp_val : ∀ (t : GdT (GdB.ofLp B g)) (x : Ordinal.{0}), LpT.val (gdToLp t) x = GdT.val t x
  | .cst _, _ => rfl
  | .bs, _ => rfl
  | .ak _, _ => rfl
  | .tp, _ => rfl
  | .th0 b t, x => by simp only [gdToLp, LpT.val_th0, GdT.val_th0, gdToLp_val t x]
  | .tl l t, x => by simp only [gdToLp, LpT.val_tl, GdT.val_tl, gdToLp_val l x, gdToLp_val t x]
  | .sm a b, x => by simp only [gdToLp, LpT.val_sm, GdT.val_sm, gdToLp_val a x, gdToLp_val b x]
  | .pw t, x => by simp only [gdToLp, LpT.val_pw, GdT.val_pw, gdToLp_val t x]

theorem gdToLp_noB : ∀ t : GdT (GdB.ofLp B g), LpT.noB (gdToLp t) ↔ GdT.noB t
  | .cst _ => Iff.rfl
  | .bs => Iff.rfl
  | .ak _ => Iff.rfl
  | .tp => Iff.rfl
  | .th0 _ _ => Iff.rfl
  | .tl _ _ => Iff.rfl
  | .sm a b => by
    show LpT.noB (gdToLp a) ∧ LpT.noB (gdToLp b) ↔ GdT.noB a ∧ GdT.noB b
    rw [gdToLp_noB a, gdToLp_noB b]
  | .pw t => by
    show LpT.noB (gdToLp t) ↔ GdT.noB t
    exact gdToLp_noB t

theorem gdToLp_cbt : ∀ (t : GdT (GdB.ofLp B g)) (x : Ordinal.{0}), LpT.CBt (gdToLp t) x ↔ GdT.CBt t x
  | .cst _, _ => Iff.rfl
  | .bs, _ => Iff.rfl
  | .ak _, _ => Iff.rfl
  | .tp, _ => Iff.rfl
  | .th0 b t, x => by
    show 1 ≤ b ∧ b < x ∧ LpT.CBt (gdToLp t) x ↔ 1 ≤ b ∧ b < x ∧ GdT.CBt t x
    rw [gdToLp_cbt t x]
  | .tl l t, x => by
    show ¬ LpT.noB (gdToLp l) ∧ LpT.CBt (gdToLp l) x ∧ LpT.CBt (gdToLp t) x ↔
      ¬ GdT.noB l ∧ GdT.CBt l x ∧ GdT.CBt t x
    rw [gdToLp_noB l, gdToLp_cbt l x, gdToLp_cbt t x]
  | .sm a b, x => by
    show LpT.CBt (gdToLp a) x ∧ LpT.CBt (gdToLp b) x ↔ GdT.CBt a x ∧ GdT.CBt b x
    rw [gdToLp_cbt a x, gdToLp_cbt b x]
  | .pw t, x => by
    show LpT.CBt (gdToLp t) x ↔ GdT.CBt t x
    exact gdToLp_cbt t x

theorem gdToLp_stage : ∀ t : GdT (GdB.ofLp B g), LpT.stage (gdToLp t) = GdT.stage t
  | .cst _ => rfl
  | .bs => rfl
  | .ak _ => rfl
  | .tp => rfl
  | .th0 b t => by simp only [gdToLp, LpT.stage, GdT.stage, gdToLp_stage t]
  | .tl l t => by simp only [gdToLp, LpT.stage, GdT.stage, gdToLp_stage l, gdToLp_stage t]
  | .sm a b => by simp only [gdToLp, LpT.stage, GdT.stage, gdToLp_stage a, gdToLp_stage b]
  | .pw t => by simp only [gdToLp, LpT.stage, GdT.stage, gdToLp_stage t]

theorem gdP_ofLp : ∀ (n : ℕ) (x : Ordinal.{0}), gdP (GdB.ofLp B g) n x = gP B n x
  | 0, _ => rfl
  | n + 1, x => by
    show vt x (Om1 * gdP (GdB.ofLp B g) n x) = vt x (Om1 * gP B n x)
    rw [gdP_ofLp n x]

/-! ## The ladder over the diagonal -/

variable (S : InaccSeq.{0})

theorem gdDL_hc : ∀ Z, SC Z → (GdB.ofLp gdDB 0).g < Z → GxCl Z (gdAt Z) (gcG (Om 1)) :=
  fun Z _ _ => GxCl.atom (gdD_atom Z)

include S in
theorem gdDL_hKE : ∀ y, SC y → y < Om 1 → (GdB.ofLp gdDB 0).g < y →
    (GdB.ofLp gdDB 0).K.E y = gxTh y (gdAt y) (gcG (Om 1)) :=
  fun y hy hy1 _ => gdD_top_th S hy hy1

include S in
theorem gdDL_hKP : GdPolyG (GdB.ofLp gdDB 0).K.sys (gcG (Om 1)) :=
  fun Z c _ hc hcE => gdD_poly S Z c hc hcE

include S in
/-- **The ladder over the diagonal has terms for every code below `cQ(Γ_{Ω₁·2}) n`.** -/
theorem gdDL_poly (n : ℕ) : GdPoly (lpSys gdDB n) (cQ (gcG (Om 1)) n) := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, -, h3⟩ := hmem
    set Z' := sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} with hZ'
    obtain ⟨s, hs⟩ := gdPoly (gdDL_hc) (gcG_Om1_lt _).le (gdDL_hKE S) (gdDL_hKP S) n Z' c h1.1
      (gdCl_mono h3 hc) hcE
    refine ⟨gdToLp s, fun y hy hy1 hZy => ?_⟩
    obtain ⟨⟨hcb, hst⟩, hv⟩ := hs y hy hy1 (csInf_le' ⟨hy, hy1, hZy⟩)
    refine ⟨⟨(gdToLp_cbt s y).2 hcb, by rw [gdToLp_stage]; exact hst⟩, ?_⟩
    show LpT.val (gdToLp s) y = _
    rw [gdToLp_val]; exact hv
  · push Not at hex
    exact ⟨LpT.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

include S in
/-- **`gP gdDB n y = Θ_y(cQ(Γ_{Ω₁·2}) n)`.** -/
theorem gdDL_top (n : ℕ) {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    (lpSys gdDB n).top y = gxTh y (gdAt y) (cQ (gcG (Om 1)) n) := by
  rw [lpSys_top, ← gdP_ofLp (g := 0)]
  exact gdTop_th (gdDL_hc) (gdDL_hKE S) n y hy hy1 hy.1

theorem gdDL_cQ_le (n : ℕ) : cQ (gcG (Om 1)) n ≤ gdV := by
  have h := cQ_lt_cQs (gcG (Om 1)) n
  rw [gc_cQs] at h
  exact h.le

/-- **`Λ⁺(lpSys gdDB n) = ι(cQ(Γ_{Ω₁·2}) n·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem gdDL_loc (n : ℕ) : xtB1 (lpSys gdDB n) = iota S (cQ (gcG (Om 1)) n * ω) ∧
    upsilon (xtB1 (lpSys gdDB n)) = Pv S (cQ (gcG (Om 1)) n * ω) ∧ Pv S (cQ (gcG (Om 1)) n * ω) < Nc.ncL S 0 := by
  have h := gdB1_eq (S := S) (gdDL_cQ_le n) (gdDL_poly S n) (fun y hy hy1 => gdDL_top S n hy hy1)
    (fun Z hZ => gdcQ_cl (gdDL_hc) hZ hZ.1 n) (cQ_Om1_le (gcG_Om1_lt _).le n)
    (fun x hx hx1 => (gdD_topE hx hx1).trans_le (E_le_gP gdDB hx hx1 n)) (lpSys_topPkg n)
  rwa [cQ_eps gdD_TE n] at h

/-- **`Θ_F(m_F) = O_n(F)` at every fixed range restart below `Λ⁺(lpSys gdDB n)`.** -/
theorem gdDL_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lpSys gdDB n))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lpSys gdDB n) l := by
  have hlt : l < iota S (ω ^ cQ (gcG (Om 1)) n * ω) := by
    rw [cQ_eps gdD_TE n, ← (gdDL_loc S n).1]; exact hlB
  exact gdUniTh (gdDL_cQ_le n) (gdDL_poly S n) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every range restart below `Λ^{gdDB}`**, fixed points included. -/
theorem gdDL_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gdDB).famSup) :
    CdUpper S l ∧ CdLower S l :=
  lpFamEnum gdDB (fun n _ hr hln hfix => gdDL_fix S n hr hln hfix) hr hl

/-- **CapV at every range restart below `Λ^{gdDB}`**, fixed points included. -/
theorem gdDL_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam gdDB).famSup) : CdCapV S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact (lpFam gdDB).famCapV hr hl hnf
  · obtain ⟨n, hn⟩ := (lpFam gdDB).famLt hl
    exact Lk.lkCapV_fix (lpSys_topPkg n) hr hn hfx.symm (gdDL_enum S hr hl)

/-- **`Λ^{gdDB} = ι(Γ_{Ω₁·2+1})`, `υ` of it `= P(Γ_{Ω₁·2+1}) < L(0)`**: the ladder over the diagonal ends at the
next strongly critical ordinal. -/
theorem gdDL_fam : (lpFam gdDB).famSup = iota S gdV ∧ upsilon (lpFam gdDB).famSup = Pv S gdV ∧
    Pv S gdV < Nc.ncL S 0 := by
  have hQ : cQs (gcG (Om 1)) = gdV := gc_cQs _
  have hSC := cQs_SC (gcG (Om 1))
  have hlim : IsSuccLimit (cQs (gcG (Om 1))) := hSC.isSuccLimit
  have hEs : ω ^ cQs (gcG (Om 1)) = cQs (gcG (Om 1)) := Low.opow_eq_self_of_SC hSC
  have hstep : ∀ n : ℕ, cQ (gcG (Om 1)) n * ω < cQs (gcG (Om 1)) := fun n =>
    InE.mul_lt hEs (cQ_lt_cQs _ n) (omega0_lt_inE hEs)
  have heq : (lpFam gdDB).famSup = iota S (cQs (gcG (Om 1))) := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show lpLam gdDB n ≤ _
      rw [lpLam, (gdDL_loc S n).1]
      exact iota_mono _ _ (hstep n).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      obtain ⟨n, hn⟩ := cQs_lt e.2
      have h1 : e.1 < cQ (gcG (Om 1)) n * ω := hn.trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (cQ (gcG (Om 1)) n * ω) := iota_mono _ _ h1.le
        _ = lpLam gdDB n := (gdDL_loc S n).1.symm
        _ ≤ (lpFam gdDB).famSup := ((lpFam gdDB).famBd_lt n).le
  rw [hQ] at heq
  have hups : upsilon (lpFam gdDB).famSup = Pv S gdV := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gdV_lt_Om2 S).le⟩

/-- **The road over the diagonal's ladder**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁·2+1})`, (CL), EQ,
TCrest, (EMB₂). -/
theorem gdDL_road (hU : ∀ l, CdRange S l → iota S gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gdV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hF := (gdDL_fam S).1
  refine lpFamRoad3 gdDB (fun l hr h => hU l hr (hF ▸ h)) (fun l hr h => hL l hr (hF ▸ h))
    (fun n _ hr hln hfix => gdDL_fix S n hr hln hfix) (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (lpFam gdDB).famSup l with h | h
  · exact hV l hr hlω (hF ▸ h)
  · exact gdDL_capV S hr h

/-- **The order of the new frontiers**: `ι(Γ_{Ω₁+ε₀}) < Λ⁺(gdDSys) = ι(Γ_{Ω₁·2}·ω) < Λ⁺(lpSys gdDB (n+1)) <
Λ^{gdDB} = ι(Γ_{Ω₁·2+1}) < ι(Ω₂)`, and `P(Γ_{Ω₁·2+1}) < L(0)`. -/
theorem gdDL_order (n : ℕ) :
    iota S gcV < xtB1 gdDSys ∧ xtB1 gdDSys < xtB1 (lpSys gdDB (n + 1)) ∧
      xtB1 (lpSys gdDB (n + 1)) < (lpFam gdDB).famSup ∧ (lpFam gdDB).famSup = iota S gdV ∧
      iota S gdV < iota S (Om (1 + 1)) ∧ Pv S gdV < Nc.ncL S 0 := by
  obtain ⟨h1, -, -, -, -, hB⟩ := gdD_fr_order S
  have hgV : Bt.Good S gdV := by
    show gdV ∈ S.CSet (ConjT.Aη S gdV + 1) (S.psi (ConjT.Aη S gdV) (Om 1))
    have hlt : Om 1 + 1 < ConjT.Aη S gdV + 1 :=
      (Order.add_one_le_of_lt (gd_Om1_lt_A _)).trans_lt (lt_add_one _)
    have := CSet.psi_mem (S := S) (b := S.psi (ConjT.Aη S gdV) (Om 1)) hlt (InR_Om_succ 1) (ga_Om2_mem _ _)
      (CSet.succ_mem (CSet.Om_mem (CSet.one_mem _ _)))
    rwa [gdV_psi S] at this
  obtain ⟨hF, -, hP⟩ := gdDL_fam S
  have hn : xtB1 (lpSys gdDB (n + 1)) < (lpFam gdDB).famSup := (lpFam gdDB).famBd_lt (n + 1)
  refine ⟨hB ▸ h1, ?_, hn, hF, cd_iota_lt_of_good hgV (gdV_lt_Om2 S), hP⟩
  exact (gdD_ladder n).2.2

end Googology.Trans.PoR.InaccPsi.R2.Gd
