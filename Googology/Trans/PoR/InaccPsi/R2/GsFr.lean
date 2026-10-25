import Googology.Trans.PoR.InaccPsi.R2.GsLoc

/-!
# THE FRONTIER `ι(Γ(ε_{G+K}))`, `K = ψ_{Ω₁}(Ω_ω)`

Port of `R2.GrFr` to `GsD` and the code systems `GsCS` (`R2.GsmAt`, gated `B_mem`).  A `GsD` gives a code system
`GsD.toK` with `κ = γ` (the bound `B` lies in every hull `C(a, b)` with `B < a` and `γ < b`) and a reading system
`GsD.toRS : GsRS` (`lt0`, `count` from the ungated `R_lt_Z`); the family of its cofinal codes is located when the base
gate is below `K` (`GsD.gsFam_sup`).  For every `ν < K` the system `gsD ν` has base gate `≤ ν < K`, so its frontier
`ι(Γ(ε_{G+ν}))` is located, the code `ε_{G+ν}` itself too (`gs_loc_B`), and the supremum over `ν < K` is
`ι(Γ(ε_{G+K}))` (`gsE_cof`).

* `GsD.count`, `GsD.toK`, `GsD.toLD`, `GsD.toRS`, `GsD.cf_g'`, `GsD.gsXk`, `GsD.gsFam`, `GsD.gsFam_sup`,
  `GsD.gsFam_enum`, `GsD.gsFam_capV`, `GsD.gsFam_blk`;
* `gs_supE`, `gs_enum`, `gs_capV`, `gs_blk`, `gs_loc_B` (every `ν < K`), `gs_loc` (every code with gate `< K`);
* `gsE S = ε_{G+K}`, `gsE_codes`, `gsE_cof`, `gsE_enum`, `gsE_capV`, `gsE_road` (**THE ROAD**), `gsE_lt_G1`,
  `gsE_le_Om2`, `gsE_P`, `gsE_fr_order`, `gsE_past_grE` (**past the round-89 frontier `ι(Γ(ε_{G+ζ_{Γ₀+1}}))`**).

No new axiom.  New definitions: `GsD.toK`, `GsD.toRS`, `GsD.gsXk`, `GsD.gsFam`, `gsE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gs

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GsD

variable (D : GsD)

/-- The codes below `c ≤ B` with gate below `y < Ω₁` are countably many. -/
theorem count {c y : Ordinal.{0}} (hc : c ≤ D.B) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // D.g b.1 < y} := by
  have hq1 : gq 1 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gm1_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // D.g b.1 < y} → Iio (gq 1 y) := fun b =>
    ⟨D.R b.1.1 y, D.R_lt_gq hy hy1 (lt_of_lt_of_le b.1.2 hc) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : D.R b.1.1 y = D.R b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (D.mono y hy hy1 _ (lt_of_lt_of_le b'.1.2 hc) _ h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (D.mono y hy hy1 _ (lt_of_lt_of_le b.1.2 hc) _ h b.2 b'.2).ne'

/-- **The code system of a gated digit system**: bound `B`, gate `D.g`. -/
noncomputable def toK : GsCS where
  B := D.B
  gt := D.g
  B_V := D.B_V
  gt_zero := D.g_zero
  gt_lt := D.g_lt
  gt_succ := fun b Z hZ hb hg => D.g_succ Z hZ b hb hg
  mem := fun S _ _ c hc hca hg => (D.mem S _ _ (lt_of_le_of_lt zero_le hca) c hc hg).1
  κ := D.γ
  κ_lt := D.γ_lt
  B_mem := fun _ _ _ ha hγb => D.B_mem (lt_of_le_of_lt zero_le ha) hγb
  code_gate := fun Z hZ1 hZ0 hZa hZp c hc hcB => D.code_gate Z hZ1 hZ0 hZa hZp _ (by
    rintro s ⟨c', hc', -, rfl⟩
    rcases eq_or_ne c' 0 with rfl | h0
    · exact Or.inl rfl
    · exact Or.inr (D.B_lt1.le.trans (gcG_le (Order.one_le_iff_ne_zero.2 h0)))) c hc hcB
  count := fun _ _ hc hy hy1 => D.count hc hy hy1

theorem cofE {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < D.B) (hEc : gfE < c) (hg : D.g c < x)
    {ν : Ordinal.{0}} (hν : ν < D.R c x) : ∃ b, gfE ≤ b ∧ b < c ∧ D.g b < x ∧ ν ≤ D.R b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := D.cof x hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [D.g_E]; exact hx.pos, ?_⟩
    exact hνb.trans (D.mono x hx hx1 gfE D.E_lt_B b hbE (by rw [D.g_E]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

theorem toLD : ∀ c, IsSuccLimit c → gfE < c → c < D.B → Nonempty (GsmLD D.toK D.R c) := by
  intro c hl hEc hc
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := D.ld c hl hc
  have hlg : ∀ x, InE x → x < Om1 → D.g c < x → lg (D.R c x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEc
  · show D.g _ ≤ D.g c
    split_ifs with h
    · exact hgcp
    · rw [D.g_E]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    show D.R c x = _ ∧ _
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      exact e4.trans (D.mono x hx hx1 gfE D.E_lt_B cp h (by rw [D.g_E]; exact hx.pos)
        (hgcp.trans_lt hg)).le
  · intro ρ τ δ h hg
    show GhPkg (D.g c) ρ δ (fun y => lg (D.R c y))
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < evZ (lgG ρ) := by
      have h1 : T ρ ≤ D.R c ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (D.R_lt_Z ρ hρE h.ρ1 c hc hg)
    have hP := gnPkg_of_exZ h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM of a gated digit system** (no cofinal sequence asked). -/
noncomputable def toRS : GsRS where
  K := D.toK
  R := D.R
  E_lt := D.E_lt_B
  B_lim := D.B_lim
  gt_E := D.g_E
  gt_lowE := D.g_lowE
  R_E := fun x _ _ => D.R_E x
  lt0 := fun c x hx hx1 hc hg => D.R_lt_gq hx hx1 hc hg
  mono := fun b c x hx hx1 hc hbc hgb hgc => D.mono x hx hx1 c hc b hbc hgc hgb
  succ := fun b x _ => D.R_succ b x
  gt_le_succ := D.g_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => D.cofE hx hx1 hc hEc hg hν
  ex := fun σ ρ c hB hc hg => D.ex σ ρ hB c hc hg
  ld := D.toLD

theorem toRS_V : D.toRS.K.V = gcG D.B := rfl

theorem toRS_gt : D.toRS.K.gt = D.g := rfl

/-! ## The family of the cofinal codes -/

theorem cf_g' (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) (k : ℕ) : D.g (D.cf k) < Td.tdK S :=
  (D.cf_g k).trans_lt (max_lt hγK
    ((gq_eps0_lt_gam.trans gam0_lt_grK).trans (grK_lt_tdK S)))

/-- The `k`-th member of the cofinal family: the code `D.cf k`. -/
noncomputable def gsXk (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) (k : ℕ) : XtSys :=
  gsX D.toRS (D.cf k) (D.cf_ge k) (D.cf_lt k) S (D.cf_g' S hγK k)

theorem gsXk_loc (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) (k : ℕ) :
    xtB1 (D.gsXk S hγK k) = iota S (gcG (D.cf k) * ω) :=
  (gsLoc D.toRS _ _ _ S _).1

/-- **The family of the layers of the cofinal codes.** -/
noncomputable def gsFam (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) : XtFam where
  bd := fun k => xtB1 (D.gsXk S hγK k)
  off := fun k => xtOrec (D.gsXk S hγK k)
  spec := fun k => xtSpec1 (gsX_pkg D.toRS _ _ _ S _)
  mono := fun k => by
    show xtB1 (D.gsXk S hγK k) < xtB1 (D.gsXk S hγK (k + 1))
    rw [D.gsXk_loc S hγK, D.gsXk_loc S hγK]
    refine cd_iota_lt_of_good (gsGood_mul D.toRS (D.cf_lt k) S (D.cf_g' S hγK k)) ?_
    have hE := geG_E (D.cf (k + 1))
    exact (InE.mul_lt hE (gcG_lt (D.cf_mono k)) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => gsX_nonfix D.toRS _ _ _ S _

/-- **`sup_k Λ⁺(gqXk k) = ι(Γ(B))`, `υ` of it `= P(Γ(B)) < L(0)`.** -/
theorem gsFam_sup (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) : (D.gsFam S hγK).famSup = iota S (gcG D.B) ∧
    upsilon (D.gsFam S hγK).famSup = Pv S (gcG D.B) ∧ Pv S (gcG D.B) < Nc.ncL S 0 := by
  have hVS : SC D.toRS.K.V := gsmV_SC
  have hVE : ω ^ D.toRS.K.V = D.toRS.K.V := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < D.B → gcG c * ω < D.toRS.K.V := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (D.gsFam S hγK).famSup = iota S D.toRS.K.V := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (D.gsXk S hγK k) ≤ _
      rw [D.gsXk_loc S hγK k]
      exact iota_mono _ _ (hstep _ (D.cf_lt k)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit D.B_lim e.2
      obtain ⟨n, hn⟩ := D.cf_cof c hc
      have h1 : e.1 < gcG (D.cf n) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (D.cf n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (D.gsXk S hγK n) := (D.gsXk_loc S hγK n).symm
        _ ≤ (D.gsFam S hγK).famSup := ((D.gsFam S hγK).famBd_lt n).le
  have hups : upsilon (D.gsFam S hγK).famSup = Pv S D.toRS.K.V := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gsmV_lt_Om2 D.toRS.K S).le⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(B))`, fixed points included.** -/
theorem gsFam_enum (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG D.B)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (D.gsFam_sup S hγK).1] at hl
  obtain ⟨k, hk⟩ := (D.gsFam S hγK).famLt hl
  have hk' : l < iota S (gcG (D.cf k) * ω) := by rw [← D.gsXk_loc S hγK k]; exact hk
  exact gsEnum D.toRS _ (D.cf_ge k) (D.cf_lt k) S (D.cf_g' S hγK k) hr hk'

/-- **CapV at every range restart below `ι(Γ(B))`, fixed points included.** -/
theorem gsFam_capV (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG D.B)) :
    CdCapV S l := by
  rw [← (D.gsFam_sup S hγK).1] at hl
  obtain ⟨k, hk⟩ := (D.gsFam S hγK).famLt hl
  have hk' : l < iota S (gcG (D.cf k) * ω) := by rw [← D.gsXk_loc S hγK k]; exact hk
  exact gsCapV D.toRS _ (D.cf_ge k) (D.cf_lt k) S (D.cf_g' S hγK k) hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ(B))} = P(Γ(B))`**, with the exact reaches. -/
theorem gsFam_blk (S : InaccSeq.{0}) (hγK : D.γ < Td.tdK S) :
    (∀ c d, c < d → d < upsilon (D.gsFam S hγK).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (D.gsFam S hγK).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (D.gsFam S hγK).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (D.gsFam S hγK).off k l)) ∧
    (∀ α < upsilon (D.gsFam S hγK).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (D.gsFam S hγK).famBlk

end GsD

/-! ## Each `gsD ν`, `ν < K = ψ_{Ω₁}(Ω_ω)` -/

theorem gs_lt_Om1 {S : InaccSeq.{0}} {ν : Ordinal.{0}} (hν : ν < Td.tdK S) : ν < Om1 := by
  rw [Br.Om1_eq]; exact hν.trans Td.tdK_lt_Om1

section Each

variable {S : InaccSeq.{0}} {ν : Ordinal.{0}} (hν : ν < Td.tdK S)
include hν

/-- The base gate of `gsD ν` is below `K`. -/
theorem gs_γK : (gsD ν).γ < Td.tdK S := (gsD_γ (gs_lt_Om1 hν)).trans_lt hν

/-- **`sup = ι(Γ(ε_{G+ν}))`, `υ` of it `= P(Γ(ε_{G+ν})) < L(0)`** for every `ν < K`. -/
theorem gs_supE : ((gsD ν).gsFam S (gs_γK hν)).famSup = iota S (gcG (veblen 1 (gcG 0 + ν))) ∧
    upsilon ((gsD ν).gsFam S (gs_γK hν)).famSup = Pv S (gcG (veblen 1 (gcG 0 + ν))) ∧
    Pv S (gcG (veblen 1 (gcG 0 + ν))) < Nc.ncL S 0 := by
  rw [← gsD_B (gs_lt_Om1 hν)]; exact (gsD ν).gsFam_sup S (gs_γK hν)

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+ν}))`, fixed points included** (`ν < K`). -/
theorem gs_enum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) :
    CdUpper S l ∧ CdLower S l :=
  (gsD ν).gsFam_enum S (gs_γK hν) hr (by rw [gsD_B (gs_lt_Om1 hν)]; exact hl)

/-- **CapV at every range restart below `ι(Γ(ε_{G+ν}))`** (`ν < K`). -/
theorem gs_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) :
    CdCapV S l :=
  (gsD ν).gsFam_capV S (gs_γK hν) hr (by rw [gsD_B (gs_lt_Om1 hν)]; exact hl)

/-- **Theorem BLK^O below `P(Γ(ε_{G+ν}))`** with the exact reaches (`ν < K`). -/
theorem gs_blk :
    (∀ c d, c < d → d < upsilon ((gsD ν).gsFam S (gs_γK hν)).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ((gsD ν).gsFam S (gs_γK hν)).famSup ∧
        c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < ((gsD ν).gsFam S (gs_γK hν)).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + ((gsD ν).gsFam S (gs_γK hν)).off k l)) ∧
    (∀ α < upsilon ((gsD ν).gsFam S (gs_γK hν)).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (gsD ν).gsFam_blk S (gs_γK hν)

/-- **THE CODE `ε_{G+ν}` IS LOCATED** for every `ν < K` (gate `≤ ν`, a code of `gsD (ν+1)`): `Λ⁺ = ι(Γ(ε_{G+ν})·ω)`,
`P(Γ(ε_{G+ν})·ω) < L(0)`. -/
theorem gs_loc_B : ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gcG 0 + ν)) * ω) ∧
    Pv S (gcG (veblen 1 (gcG 0 + ν)) * ω) < Nc.ncL S 0 := by
  have h0 : ν < Om1 := gs_lt_Om1 hν
  have h1 : ν + 1 < Om1 := by
    have hS : SC (Om1 : Ordinal.{0}) := by rw [Ph.ph_Om1_eq]; exact ph_SC_Om1
    exact hS.add_one_lt h0
  set D := gsD (ν + 1) with hD
  have hB : (gsD ν).B < D.B := gsD_B_lt (lt_add_one _) h1
  have hg : D.g (gsD ν).B < Td.tdK S := by
    rw [hD, gsD_succ, GsD.step_g_B]
    exact gs_γK hν
  have hE : gfE ≤ (gsD ν).B := (gsD ν).E_lt_B.le
  obtain ⟨l1, -, l3⟩ := gsLoc D.toRS _ hE hB S hg
  refine ⟨gsX D.toRS _ hE hB S hg, gsX_pkg D.toRS _ hE hB S hg, ?_, ?_⟩
  · rw [l1, gsD_B h0]
  · rw [← gsD_B h0]; exact l3

end Each

/-- **Every code `c ∈ [ε_{Ω₁+1}, ε_{G+ν})` of `gsD ν` (`ν < Ω₁`) with gate below `K = ψ_{Ω₁}(Ω_ω)` is located**:
`Λ⁺ = ι(Γ(c)·ω)`, `P(Γ(c)·ω) < L(0)`. -/
theorem gs_loc {ν : Ordinal.{0}} (hν : ν < Om1) {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < veblen 1 (gcG 0 + ν))
    (S : InaccSeq.{0}) (hg : (gsD ν).g c < Td.tdK S) :
    xtB1 (gsX (gsD ν).toRS c h (by show c < (gsD ν).B; rw [gsD_B hν]; exact hc) S hg) = iota S (gcG c * ω) ∧
    Pv S (gcG c * ω) < Nc.ncL S 0 :=
  let h' := gsLoc (gsD ν).toRS c h (by show c < (gsD ν).B; rw [gsD_B hν]; exact hc) S hg
  ⟨h'.1, h'.2.2⟩

/-! ## The whole recursion below `K`: the bound `ε_{G+K}` -/

theorem gs_tdK_lim (S : InaccSeq.{0}) : IsSuccLimit (Td.tdK S) := Td.tdK_SC.isSuccLimit

/-- **The bound of the recursion below `K`**: `ε_{G+K} = φ(1, G + ψ_{Ω₁}(Ω_ω))`. -/
noncomputable def gsE (S : InaccSeq.{0}) : Ordinal.{0} := veblen 1 (gcG 0 + Td.tdK S)

theorem gsE_lim (S : InaccSeq.{0}) : IsSuccLimit (gsE S) := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

/-- **Every code below `ε_{G+K}` is a code of some `gsD ν`, `ν < K`.** -/
theorem gsE_codes {S : InaccSeq.{0}} {c : Ordinal.{0}} (hc : c < gsE S) :
    ∃ ν, ν < Td.tdK S ∧ c < (gsD ν).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ (gs_tdK_lim S))).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff (gs_tdK_lim S).bot_lt.ne').1 ht
  exact ⟨d, hd, by rw [gsD_B (gs_lt_Om1 hd)]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

theorem gsD_B_lt_E {S : InaccSeq.{0}} {ν : Ordinal.{0}} (hν : ν < Td.tdK S) : (gsD ν).B < gsE S := by
  rw [gsD_B (gs_lt_Om1 hν)]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hν)

/-- **`ι(Γ(ε_{G+K})) = sup_{ν<K} ι(Γ(ε_{G+ν}))`**. -/
theorem gsE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG (gsE S))) :
    ∃ ν, ∃ hν : ν < Td.tdK S, l < iota S (gcG (gsD ν).B) := by
  have hlim : IsSuccLimit (gcG (gsE S)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG (gsE S))) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit (gsE_lim S) e.2
  obtain ⟨ν, hν, hβν⟩ := gsE_codes hβ
  exact ⟨ν, hν, he.trans_le (iota_mono _ _ (heβ.trans (gcG_lt hβν)).le)⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+K}))`, fixed points included.** -/
theorem gsE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gsE S))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, hν, h⟩ := gsE_cof S hl
  exact (gsD ν).gsFam_enum S (gs_γK hν) hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+K}))`.** -/
theorem gsE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gsE S))) :
    CdCapV S l := by
  obtain ⟨ν, hν, h⟩ := gsE_cof S hl
  exact (gsD ν).gsFam_capV S (gs_γK hν) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+K}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gsE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG (gsE S)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (gsE S)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (gsE S)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < iota S (gcG (gsE S))
    · exact (gsE_enum S hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG (gsE S))
    · exact (gsE_enum S hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG (gsE S))
    · exact gsE_capV S hr h
    · exact hV l hr hω (not_lt.1 h)

/-! ## The place of the frontier -/

theorem gsE_lt_G1 (S : InaccSeq.{0}) : gsE S < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have hK : Td.tdK S < gcG 1 := (by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1 : Td.tdK S < Om1).trans gs_Om1_lt_gcG1
  have h1 : gcG 0 + Td.tdK S < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) hK
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+K}) < Ω₂`.** -/
theorem gsE_le_Om2 (S : InaccSeq.{0}) : gcG (gsE S) < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG (gsE S) < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) ((gsE_lt_G1 S).trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+K})) < L(0)`.** -/
theorem gsE_P (S : InaccSeq.{0}) : Pv S (gcG (gsE S)) < Nc.ncL S 0 := ga_Pv_lt_L0 S (gsE_le_Om2 S).le

/-- **The order of the frontiers**: for every `ν < K`, `ι(Γ(ε_{G+ν})) < ι(Γ(ε_{G+ν})·ω) < ι(Γ(ε_{G+ν+1})) ≤
ι(Γ(ε_{G+K})) ≤ ι(Ω₂)`; the round-89 frontier `ι(Γ(ε_{G+ζ_{Γ₀+1}}))` lies below `ι(Γ(ε_{G+ζ_{Γ₀+1}})·ω)`; and
`P(Γ(ε_{G+K})) ≤ P(Ω₂) < L(0)`. -/
theorem gsE_fr_order (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < Td.tdK S) :
    iota S (gcG (gsD ν).B) < iota S (gcG (gsD ν).B * ω) ∧
      iota S (gcG (gsD ν).B * ω) < iota S (gcG (gsD (ν + 1)).B) ∧
      iota S (gcG (gsD ν).B) ≤ iota S (gcG (gsE S)) ∧
      iota S (gcG (gsE S)) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG (gsE S)) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have h0 : ν < Om1 := gs_lt_Om1 hν
  have h1 : ν + 1 < Om1 := by
    have hS : SC (Om1 : Ordinal.{0}) := by rw [Ph.ph_Om1_eq]; exact ph_SC_Om1
    exact hS.add_one_lt h0
  have hB : (gsD ν).B < (gsD (ν + 1)).B := gsD_B_lt (lt_add_one _) h1
  have hgE : (gsD (ν + 1)).g (gsD ν).B < Td.tdK S := by
    rw [gsD_succ, GsD.step_g_B]; exact gs_γK hν
  have hG : InE (gcG (gsD ν).B) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hgood := gsGood_mul (gsD (ν + 1)).toRS (c := (gsD ν).B) hB S hgE
  have hgood0 : Bt.Good S (gcG (gsD ν).B) := by
    refine gs_good (K := (gsD (ν + 1)).toRS.K) fun Z _ hKZ => ?_
    exact GxCl.atom (gsmG_atom (K := (gsD (ν + 1)).toRS.K) hB (hgE.trans_le hKZ))
  refine ⟨cd_iota_lt_of_good hgood0 (lt_mul_of_one_lt_right hG.pos one_lt_omega0), ?_,
    iota_mono _ _ (gcG_lt (gsD_B_lt_E hν)).le, iota_mono _ _ (gsE_le_Om2 S).le, Nm.Pv_mono (gsE_le_Om2 S).le,
    ga_Pv_lt_L0 S le_rfl⟩
  have hV : InE (gcG (gsD (ν + 1)).B) := Low.opow_eq_self_of_SC (gcG_SC _)
  exact cd_iota_lt_of_good hgood (InE.mul_lt hV (gcG_lt hB) (omega0_lt_inE hV))

/-- **The new frontier passes the round-89 frontier**: `ε_{G+ζ_{Γ₀+1}} < ε_{G+K}`, so
`ι(Γ(ε_{G+ζ_{Γ₀+1}})) < ι(Γ(ε_{G+ζ_{Γ₀+1}})·ω) < ι(Γ(ε_{G+K}))`. -/
theorem gsE_past_grE (S : InaccSeq.{0}) :
    Gr.grE < gsE S ∧ iota S (gcG Gr.grE) < iota S (gcG Gr.grE * ω) ∧
      iota S (gcG Gr.grE * ω) < iota S (gcG (gsE S)) := by
  have hK := grK_lt_tdK S
  have e : Gr.grE = (gsD grK).B := (gsD_B grK_lt_Om1).symm
  have h1 : Gr.grE < gsE S := by rw [e]; exact gsD_B_lt_E hK
  obtain ⟨a1, a2, a3, -⟩ := gsE_fr_order S hK
  refine ⟨h1, by rw [e]; exact a1, ?_⟩
  rw [e]
  have hK1 : grK + 1 < Td.tdK S := (gs_tdK_lim S).add_one_lt hK
  exact a2.trans_le (iota_mono _ _ (gcG_lt (gsD_B_lt_E hK1)).le)

end Googology.Trans.PoR.InaccPsi.R2.Gs
