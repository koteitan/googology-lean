import Googology.Trans.PoR.InaccPsi.R2.GdUnif
import Googology.Trans.PoR.InaccPsi.R2.GdDLoc
import Googology.Trans.PoR.InaccPsi.R2.GaEnd

/-!
# WHERE THE DIAGONAL FRONTIER LIES: `Λ⁺(gdDSys) = ι(Γ_{Ω₁·2}·ω)`, below `L(0)`

The diagonal layer `gdDSys` (top `Γ_{x+x}`, `R2.GdDiag`) reads the code `Γ_{Ω₁+1+Ω₁} = Γ_{Ω₁·2}` and has terms for
every code below it (from the gated uniformity theorem `R2.GdUnif.gdB_codes`); so the frontier lemma with the atoms over
the base (`R2.GdFr`) locates its frontier:

* `gdD_top_th` (**`Γ_{y+y} = Θ_y(Γ_{Ω₁·2})`** at every strongly critical `y < Ω₁`: the hull below `Γ_{Ω₁·2}` is the hull
  below `Γ_{Ω₁+1+y}`, and `sup_{b<y} Γ_{y+1+b} = Γ_{y+y}`);
* `gdD_poly` (**every code below `Γ_{Ω₁·2}` over `Z` is read by a term `(β, t)`**, `t` a term of `gdB β`, `β < Z`);
* `gdD_loc` (**`Λ⁺(gdDSys) = ι(Γ_{Ω₁·2}·ω)`, `ρ_{Λ⁺} = P(Γ_{Ω₁·2}·ω) < L(0)`**, unconditional);
* `gdD_fix` (**`Θ_F(m_F) = O_D(F)` at every fixed range restart below `Λ⁺(gdDSys)`**, THEOREM UNI), `gdD_enum`
  (**ENUM-REACH at every range restart below `ι(Γ_{Ω₁·2}·ω)`, fixed points included**), `gdD_capVAll` (**CapV there**);
* `gdD_road2` (**THE ROAD past the diagonal**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁·2}·ω)`, (CL), EQ,
  TCrest, (EMB₂));
* `gdD_fr_order` (**`ι(Γ_{Ω₁+ε₀}) < ι(Γ_{Ω₁·2}·ω) < ι(Ω₂) < ι(Ω_ω)`, `P(Γ_{Ω₁·2}·ω) < P(Ω₂) < L(0)`**);
* `gdEnd_front` (**every frontier located with the atoms over the base lies below `ι(Ω₂)`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc

variable (S : InaccSeq.{0})

include S in
/-- **`Γ_{y+y} = Θ_y(Γ_{Ω₁·2})`** at every strongly critical `y < Ω₁`. -/
theorem gdD_top_th {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    gdDSys.top y = gxTh y (gdAt y) (gcG (Om 1)) := by
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  have hyl : IsSuccLimit y := hy.isSuccLimit
  rw [gdDSys_top, gdTh_G_ge hy hy1 (hy1.le) le_rfl, gdTh_Gy hy]
  have hRd : ∀ b, b < y → gxTh y (gdAt y) (gcG (1 + b)) = gq (1 + b) y := fun b hb => by
    rw [← (gdB_codes S b).1 y hy hy1 hb, gdB_E hyE hy1' hb]
  haveI : Nonempty (Iio y) := ⟨⟨0, hy.1⟩⟩
  have hbdd : BddAbove (range fun b : Iio y => gxTh y (gdAt y) (gcG b.1)) := Ordinal.bddAbove_of_small
  refine le_antisymm (le_of_forall_lt fun v hv => ?_) (ciSup_le' fun b => ?_)
  · obtain ⟨ν, hν, hvν⟩ := gcD_lt_iff hyE hy1' v hv
    have h1 : 1 + ν < y := gc_one_add_lt hyl hν
    calc v < gq ν y := hvν
      _ ≤ gq (1 + ν) y := gq_mono hyE hy1' h1 le_add_self
      _ = gxTh y (gdAt y) (gcG (1 + ν)) := (hRd ν hν).symm
      _ ≤ ⨆ b : Iio y, gxTh y (gdAt y) (gcG b.1) := le_ciSup hbdd ⟨1 + ν, h1⟩
  · calc gxTh y (gdAt y) (gcG b.1) ≤ gxTh y (gdAt y) (gcG (1 + b.1)) := gxTh_mono (gcG_le le_add_self)
      _ = gq (1 + b.1) y := hRd b.1 b.2
      _ ≤ gq y y := (gd_gq_lt_D hyE hy1' (gc_one_add_lt hyl b.2)).le

include S in
/-- **The diagonal has terms for every code below `Γ_{Ω₁·2}`.** -/
theorem gdD_poly : GdPoly gdDSys (gcG (Om 1)) := by
  intro Z c hc hcE
  by_cases hex : ∃ y, SC y ∧ y < Om 1 ∧ Z ≤ y
  · have hmem : sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} ∈ {y | SC y ∧ y < Om 1 ∧ Z ≤ y} := csInf_mem hex
    obtain ⟨h1, h2, h3⟩ := hmem
    set Z' := sInf {y | SC y ∧ y < Om 1 ∧ Z ≤ y} with hZ'
    have hc' := gdCl_mono h3 hc
    obtain ⟨β, hβ, hcβ⟩ := gdCl_lt_G h1 h2 hc' hcE
    have hgβ : (gdB β).g < Z' := by rw [gdB_g]; exact hβ
    obtain ⟨s, hs⟩ := (gdB_codes S β).2 Z' c hgβ hc' (hcβ.trans_le (gcG_le le_add_self))
    refine ⟨⟨β, s⟩, fun y hy hy1 hZy => ?_⟩
    have hZ'y : Z' ≤ y := csInf_le' ⟨hy, hy1, hZy⟩
    obtain ⟨hcb, hv⟩ := hs y hy hy1 hZ'y
    exact ⟨⟨hβ.trans_le hZ'y, hcb⟩, hv⟩
  · push Not at hex
    exact ⟨gdDSys.cst 0, fun y hy hy1 hZy => absurd hZy (not_le.2 (hex y hy hy1))⟩

theorem gdD_TE : ω ^ gcG (Om 1) = gcG (Om 1) := gg_SC_eps (gcG_SC _)

theorem gdD_topE {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < gdDSys.top x := by
  rw [gdDSys_top]
  have h1 : gk 1 x = gq 1 x := by rw [← gq_nat, Nat.cast_one]
  refine (ga_eN_lt_gk 1 hx hx1).trans_le ?_
  rw [h1]
  exact (gd_gq_lt_D hx hx1 (Lu.lu_one_lt_E hx)).le

/-- **WHERE THE DIAGONAL FRONTIER LIES**: `Λ⁺(gdDSys) = ι(Γ_{Ω₁·2}·ω)`, `ρ_{Λ⁺} = P(Γ_{Ω₁·2}·ω) < L(0)`. -/
theorem gdD_loc : xtB1 gdDSys = iota S (gcG (Om 1) * ω) ∧ upsilon (xtB1 gdDSys) = Pv S (gcG (Om 1) * ω) ∧
    Pv S (gcG (Om 1) * ω) < Nc.ncL S 0 := by
  have h := gdB1_eq (S := S) gdD_lt_V.le (gdD_poly S) (fun y hy hy1 => gdD_top_th S hy hy1)
    (fun Z _ => GxCl.atom (gdD_atom Z)) (gcG_Om1_lt _).le (fun x hx hx1 => gdD_topE hx hx1) gdD_topPkg
  rw [gdD_TE] at h
  exact h

/-- **`Θ_F(m_F) = O_D(F)` at every fixed range restart below `Λ⁺(gdDSys)`.** -/
theorem gdD_fix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 gdDSys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec gdDSys l := by
  have hlt : l < iota S (ω ^ gcG (Om 1) * ω) := by rw [gdD_TE, ← (gdD_loc S).1]; exact hl
  exact gdUniTh gdD_lt_V.le (gdD_poly S) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁·2}·ω)`, fixed points included.** -/
theorem gdD_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (Om 1) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (gdD_loc S).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact gdD_init hr hl hnf
  · exact (xtExact_iff gdD_spec hr.1 hl).2 (gdD_fix S hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁·2}·ω)`, fixed points included.** -/
theorem gdD_capVAll {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (Om 1) * ω)) : CdCapV S l := by
  have hl' := hl
  rw [← (gdD_loc S).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact gdD_capV hr hl' hnf
  · exact Lk.lkCapV_fix gdD_topPkg hr hl' hfx.symm (gdD_enum S hr hl)

/-- **THE ROAD past the diagonal**: UPPER, LOWER and CapV asked only at the range restarts `λ ≥ ι(Γ_{Ω₁·2}·ω)`, (CL),
EQ, TCrest, (EMB₂). -/
theorem gdD_road2 (hU : ∀ l, CdRange S l → iota S (gcG (Om 1) * ω) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (Om 1) * ω) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (Om 1) * ω) ≤ l → CdCapV S l)
    (hC : CdCL S) (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hB := (gdD_loc S).1
  refine xtRoad3 gdD_spec gdD_nonfix (fun l hr h => hU l hr (hB ▸ h)) (fun l hr h => hL l hr (hB ▸ h))
    (fun l hr hlB hfix => gdD_fix S hr hlB hfix) (fun l hr hX _ => ?_) hC hEQ hrest hB2
  rcases lt_or_ge l (iota S (gcG (Om 1) * ω)) with h | h
  · exact gdD_capVAll S hr h
  · exact hV l hr hX h

/-- **Where the diagonal frontier lies, against the earlier ones and `L(0)`.** -/
theorem gdD_fr_order :
    iota S gcV < iota S (gcG (Om 1) * ω) ∧ iota S (gcG (Om 1) * ω) < iota S (Om (1 + 1)) ∧
      iota S (Om (1 + 1)) < iota S (Om ω) ∧ Pv S (gcG (Om 1) * ω) < Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 ∧ xtB1 gdDSys = iota S (gcG (Om 1) * ω) := by
  have hcl : ∀ Z, SC Z → GxCl Z (gdAt Z) (gcG (Om 1) * ω) := fun Z hZ => by
    have e : gcG (Om 1) * ω = ω ^ (gcG (Om 1) + 1) := by
      rw [opow_add, opow_one, gdD_TE]
    rw [e]; exact GxCl.opow hZ.1 (GxCl.add (GxCl.atom (gdD_atom Z)) (GxCl.small (gg_one_lt_of_SC hZ)))
  have hg : Bt.Good S (gcG (Om 1) * ω) := gd_good hcl
  have hgV : Bt.Good S gcV := gd_good fun Z hZ => GxCl.atom (gdG_atom (gd_eps0_lt hZ))
  have hDw : gcG (Om 1) < gcG (Om 1) * ω := lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0
  have h1 : iota S gcV < iota S (gcG (Om 1) * ω) :=
    cd_iota_lt_of_good hgV ((gcG_le gc_eps0_le_Om1).trans_lt hDw)
  have hE2 : InE (Om (1 + 1 : Ordinal.{0})) := Low.opow_eq_self_of_SC (SC_Om gc_two_ne)
  have h2 : iota S (gcG (Om 1) * ω) < iota S (Om (1 + 1)) :=
    cd_iota_lt_of_good hg (InE.mul_lt hE2 (gdD_lt_V.trans (gdV_lt_Om2 S)) (omega0_lt_inE hE2))
  obtain ⟨-, h3, -, h5⟩ := Ga.gaEnd_Om2 (S := S) (le_rfl : Om (1 + 1 : Ordinal.{0}) ≤ Om (1 + 1))
  have h4 : Pv S (gcG (Om 1) * ω) < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h2
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h1, h2, h3, h4, h5, (gdD_loc S).1⟩

/-- **How far the frontier method goes, with the atoms over the base**: every frontier located by `gdB1_eq` (a top
code `T ≤ Γ_{Ω₁+1+Ω₁+1}`) lies below `ι(Ω₂)`, with `υ` below `P(Ω₂) < L(0)`. -/
theorem gdEnd_front {X : XtSys} {T : Ordinal.{0}} (hT : T ≤ gdV) (hP : GdPoly X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = gxTh y (gdAt y) T) (hTcl : ∀ Z, SC Z → GxCl Z (gdAt Z) T)
    (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    xtB1 X < iota S (Om (1 + 1)) ∧ upsilon (xtB1 X) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  obtain ⟨h1, h2, -⟩ := gdB1_eq (S := S) hT hP htop hTcl hTO htopE hPk
  have hS2 := gg_SC_Om2
  have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Low.opow_eq_self_of_SC hS2
  have hT2 : T < Om (1 + 1) := hT.trans_lt (gdV_lt_Om2 S)
  have hlt : ω ^ T * ω < Om (1 + 1) :=
    InE.mul_lt hE2 (hE2 ▸ (opow_lt_opow_iff_right one_lt_omega0).2 hT2) (omega0_lt_inE hE2)
  have hcl : ∀ Z, SC Z → GxCl Z (gdAt Z) (ω ^ T * ω) := fun Z hZ => by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact GxCl.opow hZ.1 (GxCl.add (hTcl Z hZ) (GxCl.small (gg_one_lt_of_SC hZ)))
  have hι : iota S (ω ^ T * ω) < iota S (Om (1 + 1)) := cd_iota_lt_of_good (gd_good hcl) hlt
  refine ⟨h1 ▸ hι, ?_, ga_Pv_lt_L0 S le_rfl⟩
  rw [h2, show Pv S (Om (1 + 1)) = upsilon (iota S (Om (1 + 1))) from (ups_iota S _).symm,
    show Pv S (ω ^ T * ω) = upsilon (iota S (ω ^ T * ω)) from (ups_iota S _).symm]
  exact upsilon_normal.strictMono hι

end Googology.Trans.PoR.InaccPsi.R2.Gd
