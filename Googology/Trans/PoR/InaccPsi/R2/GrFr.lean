import Googology.Trans.PoR.InaccPsi.R2.GrRec
import Googology.Trans.PoR.InaccPsi.R2.GrLoc

/-!
# THE FRONTIERS PAST `Γ₀`: `ι(Γ(ε_{G+ν}))` for every constant index `ν < ζ_{Γ₀+1}`, the sup `ι(Γ(ε_{G+ζ_{Γ₀+1}}))`

`G = Γ_{Ω₁+1}`, `Γ(c) = Γ_{Ω₁+1+c}`, `K = ψ_{Ω₁}(Ω_ω)`.  A gated digit system `D : GrD` (`R2.GrD`) is a reading system
`D.toRS : Gq.GqRS` (the proofs of `R2.GqFr`; its code-gate condition is the field of `GrD`); its cofinal codes have
gates `≤ max γ ε₀ < ζ_{Γ₀+1} < K`, so each is located by the location theorem with gate below `K` (`R2.GrLoc`), and
their layers form a family with supremum `ι(Γ(B))`.  For the recursion `grD ν` (`R2.GrRec`):

* `GrD.toK`, `GrD.toRS`, `GrD.grFam`, `GrD.grFam_sup` (**`sup = ι(Γ(B))`, `P(Γ(B)) < L(0)`**), `GrD.grFam_enum`,
  `GrD.grFam_capV`, `GrD.grFam_blk`;
* `gr_supE`, `gr_enum`, `gr_capV`, `gr_blk` (**every `ν < ζ_{Γ₀+1}`**: BLK^O, exact reaches, ENUM-REACH, CapV below
  `ι(Γ(ε_{G+ν}))`), `gr_loc` (**every code of `grD ν` with gate below `K` located**), `gr_loc_gam0` (**the code
  `ε_{G+Γ₀}` itself, gate `Γ₀`: `Λ⁺ = ι(Γ(ε_{G+Γ₀})·ω)`**, past the round-88 frontier `ι(Γ(ε_{G+Γ₀}))`);
* `grE = φ(1, G + ζ_{Γ₀+1})`, `grE_cof`, `grE_enum`, `grE_capV`, `grE_road` (**THE ROAD with UPPER, LOWER, CapV asked
  only at `λ ≥ ι(Γ(ε_{G+ζ_{Γ₀+1}}))`**), `grE_le_Om2`, `grE_P`, `grE_fr_order` (**`ι(Γ(ε_{G+Γ₀})) <
  ι(Γ(ε_{G+Γ₀})·ω) < ι(Γ(ε_{G+Γ₀+1})) ≤ ι(Γ(ε_{G+ζ_{Γ₀+1}})) ≤ ι(Ω₂)`**).

No new axiom.  New definitions: `GrD.toK`, `GrD.toRS`, `GrD.grXk`, `GrD.grFam`, `grE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

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

namespace GrD

variable (D : GrD)

/-- The codes below `c ≤ B` with gate below `y < Ω₁` are countably many. -/
theorem count {c y : Ordinal.{0}} (hc : c ≤ D.B) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // D.g b.1 < y} := by
  have hq1 : gq 1 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gm1_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // D.g b.1 < y} → Iio (gq 1 y) := fun b =>
    ⟨D.R b.1.1 y, (D.R_lt_b y hy hy1 _ (lt_of_lt_of_le b.1.2 hc) b.2).trans (D.b_lt1 hy hy1)⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : D.R b.1.1 y = D.R b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (D.mono y hy hy1 _ (lt_of_lt_of_le b'.1.2 hc) _ h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (D.mono y hy hy1 _ (lt_of_lt_of_le b.1.2 hc) _ h b.2 b'.2).ne'

/-- **The code system of a gated digit system**: bound `B`, gate `D.g`. -/
noncomputable def toK : GmCS where
  B := D.B
  gt := D.g
  B_V := D.B_V
  gt_zero := D.g_zero
  gt_lt := D.g_lt
  gt_succ := fun b Z hZ hb hg => D.g_succ Z hZ b hb hg
  mem := fun S _ _ c hc hca hg => (D.mem S _ _ (lt_of_le_of_lt zero_le hca) c hc hg).1
  B_mem := fun _ _ _ ha => D.B_mem (lt_of_le_of_lt zero_le ha)
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

theorem toLD : ∀ c, IsSuccLimit c → gfE < c → c < D.B → Nonempty (GmLD D.toK D.R c) := by
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
      exact h1.trans_lt ((D.R_lt_eNb hρE h.ρ1 hc hg).trans (D.b_Z ρ hρE h.ρ1))
    have hP := gnPkg_of_exZ h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM of a gated digit system** (no cofinal sequence asked). -/
noncomputable def toRS : GqRS where
  K := D.toK
  R := D.R
  E_lt := D.E_lt_B
  B_lim := D.B_lim
  gt_E := D.g_E
  gt_lowE := D.g_lowE
  R_E := fun x _ _ => D.R_E x
  lt0 := fun c x hx hx1 hc hg => (D.R_lt_b x hx hx1 c hc hg).trans (D.b_lt1 hx hx1)
  mono := fun b c x hx hx1 hc hbc hgb hgc => D.mono x hx hx1 c hc b hbc hgc hgb
  succ := fun b x _ => D.R_succ b x
  gt_le_succ := D.g_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => D.cofE hx hx1 hc hEc hg hν
  ex := fun σ ρ c hB hc hg => D.ex σ ρ hB c hc hg
  ld := D.toLD

theorem toRS_V : D.toRS.K.V = gcG D.B := rfl

theorem toRS_gt : D.toRS.K.gt = D.g := rfl

/-! ## The family of the cofinal codes -/

theorem cf_g' (S : InaccSeq.{0}) (k : ℕ) : D.g (D.cf k) < Td.tdK S :=
  (D.cf_g k).trans_lt (max_lt (D.γ_lt.trans (grK_lt_tdK S))
    ((gq_eps0_lt_gam.trans gam0_lt_grK).trans (grK_lt_tdK S)))

/-- The `k`-th member of the cofinal family: the code `D.cf k`. -/
noncomputable def grXk (S : InaccSeq.{0}) (k : ℕ) : XtSys :=
  grX D.toRS (D.cf k) (D.cf_ge k) (D.cf_lt k) S (D.cf_g' S k)

theorem grXk_loc (S : InaccSeq.{0}) (k : ℕ) : xtB1 (D.grXk S k) = iota S (gcG (D.cf k) * ω) :=
  (grLoc D.toRS _ _ _ S _).1

/-- **The family of the layers of the cofinal codes.** -/
noncomputable def grFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (D.grXk S k)
  off := fun k => xtOrec (D.grXk S k)
  spec := fun k => xtSpec1 (grX_pkg D.toRS _ _ _ S _)
  mono := fun k => by
    show xtB1 (D.grXk S k) < xtB1 (D.grXk S (k + 1))
    rw [D.grXk_loc S, D.grXk_loc S]
    refine cd_iota_lt_of_good (grGood_mul D.toRS (D.cf_lt k) S (D.cf_g' S k)) ?_
    have hE := geG_E (D.cf (k + 1))
    exact (InE.mul_lt hE (gcG_lt (D.cf_mono k)) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => grX_nonfix D.toRS _ _ _ S _

/-- **`sup_k Λ⁺(gqXk k) = ι(Γ(B))`, `υ` of it `= P(Γ(B)) < L(0)`.** -/
theorem grFam_sup (S : InaccSeq.{0}) : (D.grFam S).famSup = iota S (gcG D.B) ∧
    upsilon (D.grFam S).famSup = Pv S (gcG D.B) ∧ Pv S (gcG D.B) < Nc.ncL S 0 := by
  have hVS : SC D.toRS.K.V := gmV_SC
  have hVE : ω ^ D.toRS.K.V = D.toRS.K.V := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < D.B → gcG c * ω < D.toRS.K.V := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (D.grFam S).famSup = iota S D.toRS.K.V := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (D.grXk S k) ≤ _
      rw [D.grXk_loc S k]
      exact iota_mono _ _ (hstep _ (D.cf_lt k)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit D.B_lim e.2
      obtain ⟨n, hn⟩ := D.cf_cof c hc
      have h1 : e.1 < gcG (D.cf n) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (D.cf n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (D.grXk S n) := (D.grXk_loc S n).symm
        _ ≤ (D.grFam S).famSup := ((D.grFam S).famBd_lt n).le
  have hups : upsilon (D.grFam S).famSup = Pv S D.toRS.K.V := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gmV_lt_Om2 D.toRS.K S).le⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(B))`, fixed points included.** -/
theorem grFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (D.grFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (D.grFam S).famLt hl
  have hk' : l < iota S (gcG (D.cf k) * ω) := by rw [← D.grXk_loc S k]; exact hk
  exact grEnum D.toRS _ (D.cf_ge k) (D.cf_lt k) S (D.cf_g' S k) hr hk'

/-- **CapV at every range restart below `ι(Γ(B))`, fixed points included.** -/
theorem grFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B)) :
    CdCapV S l := by
  rw [← (D.grFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (D.grFam S).famLt hl
  have hk' : l < iota S (gcG (D.cf k) * ω) := by rw [← D.grXk_loc S k]; exact hk
  exact grCapV D.toRS _ (D.cf_ge k) (D.cf_lt k) S (D.cf_g' S k) hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ(B))} = P(Γ(B))`**, with the exact reaches. -/
theorem grFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (D.grFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (D.grFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (D.grFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (D.grFam S).off k l)) ∧
    (∀ α < upsilon (D.grFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (D.grFam S).famBlk

end GrD

/-! ## Each `grD ν`, `ν < ζ_{Γ₀+1}` -/

section Each

variable {ν : Ordinal.{0}} (hν : ν < grK)
include hν

/-- **`sup = ι(Γ(ε_{G+ν}))`, `υ` of it `= P(Γ(ε_{G+ν})) < L(0)`.** -/
theorem gr_supE (S : InaccSeq.{0}) : ((grD ν).grFam S).famSup = iota S (gcG (veblen 1 (gcG 0 + ν))) ∧
    upsilon ((grD ν).grFam S).famSup = Pv S (gcG (veblen 1 (gcG 0 + ν))) ∧
    Pv S (gcG (veblen 1 (gcG 0 + ν))) < Nc.ncL S 0 := by
  rw [← grD_B hν]; exact (grD ν).grFam_sup S

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+ν}))`, fixed points included.** -/
theorem gr_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) : CdUpper S l ∧ CdLower S l :=
  (grD ν).grFam_enum S hr (by rw [grD_B hν]; exact hl)

/-- **CapV at every range restart below `ι(Γ(ε_{G+ν}))`.** -/
theorem gr_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) : CdCapV S l :=
  (grD ν).grFam_capV S hr (by rw [grD_B hν]; exact hl)

/-- **Every code `c ∈ [ε_{Ω₁+1}, ε_{G+ν})` of `grD ν` with gate below `K = ψ_{Ω₁}(Ω_ω)` located**: `Λ⁺ = ι(Γ(c)·ω)`,
`P(Γ(c)·ω) < L(0)`. -/
theorem gr_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < veblen 1 (gcG 0 + ν)) (S : InaccSeq.{0})
    (hg : (grD ν).g c < Td.tdK S) :
    xtB1 (grX (grD ν).toRS c h (by show c < (grD ν).B; rw [grD_B hν]; exact hc) S hg) = iota S (gcG c * ω) ∧
    Pv S (gcG c * ω) < Nc.ncL S 0 :=
  let h' := grLoc (grD ν).toRS c h (by show c < (grD ν).B; rw [grD_B hν]; exact hc) S hg
  ⟨h'.1, h'.2.2⟩

end Each

/-- **Theorem BLK^O below `P(Γ(ε_{G+ν}))`** (the supremum of `grD ν`, `gr_supE`), with the exact reaches. -/
theorem gr_blk (ν : Ordinal.{0}) (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon ((grD ν).grFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ((grD ν).grFam S).famSup ∧
        c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < ((grD ν).grFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + ((grD ν).grFam S).off k l)) ∧
    (∀ α < upsilon ((grD ν).grFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (grD ν).grFam_blk S

theorem grK_lim : IsSuccLimit grK := ev_isSuccLimit_of_inE (evZ_E _)

/-- **THE CODE `ε_{G+Γ₀}` IS LOCATED** (gate `≤ Γ₀`, a code of `grD (Γ₀+1)`): `Λ⁺ = ι(Γ(ε_{G+Γ₀})·ω)`,
`P(Γ(ε_{G+Γ₀})·ω) < L(0)`.  (`Gq.gq_wall`: no gated system of `R2.GqD` has this code.) -/
theorem gr_loc_gam0 (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gcG 0 + gamma 0)) * ω) ∧
      Pv S (gcG (veblen 1 (gcG 0 + gamma 0)) * ω) < Nc.ncL S 0 := by
  have h0 : gamma 0 < grK := gam0_lt_grK
  have h1 : gamma 0 + 1 < grK := grK_lim.add_one_lt h0
  set D := grD (gamma 0 + 1) with hD
  have hB : (grD (gamma 0)).B < D.B := grD_B_lt (lt_add_one _) h1
  have hg : D.g (grD (gamma 0)).B < Td.tdK S := by
    rw [hD, grD_succ, GrD.step_g_B]
    exact (grD_γ h0).trans_lt (gr_gam0_lt_tdK S)
  have hE : gfE ≤ (grD (gamma 0)).B := (grD (gamma 0)).E_lt_B.le
  obtain ⟨l1, -, l3⟩ := grLoc D.toRS _ hE hB S hg
  refine ⟨grX D.toRS _ hE hB S hg, grX_pkg D.toRS _ hE hB S hg, ?_, ?_⟩
  · rw [l1, grD_B h0]
  · rw [← grD_B h0]; exact l3

/-! ## The whole recursion: the bound `ε_{G+ζ_{Γ₀+1}}` -/

/-- **The bound of the whole recursion**: `ε_{G+ζ_{Γ₀+1}} = φ(1, G + ζ_{Γ₀+1})`. -/
noncomputable def grE : Ordinal.{0} := veblen 1 (gcG 0 + grK)

theorem grE_lim : IsSuccLimit grE := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

/-- **Every code below `ε_{G+ζ_{Γ₀+1}}` is a code of some `grD ν`, `ν < ζ_{Γ₀+1}`.** -/
theorem grE_codes {c : Ordinal.{0}} (hc : c < grE) : ∃ ν, ν < grK ∧ c < (grD ν).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ grK_lim)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff grK_lim.bot_lt.ne').1 ht
  exact ⟨d, hd, by rw [grD_B hd]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

theorem grD_B_lt_E {ν : Ordinal.{0}} (hν : ν < grK) : (grD ν).B < grE := by
  rw [grD_B hν]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hν)

/-- **`ι(Γ(ε_{G+ζ_{Γ₀+1}})) = sup_{ν<ζ_{Γ₀+1}} ι(Γ(ε_{G+ν}))`**. -/
theorem grE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG grE)) :
    ∃ ν, ν < grK ∧ l < iota S (gcG (grD ν).B) := by
  have hlim : IsSuccLimit (gcG grE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG grE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit grE_lim e.2
  obtain ⟨ν, hν, hβν⟩ := grE_codes hβ
  exact ⟨ν, hν, he.trans_le (iota_mono _ _ (heβ.trans (gcG_lt hβν)).le)⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+ζ_{Γ₀+1}}))`, fixed points included.** -/
theorem grE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG grE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, -, h⟩ := grE_cof S hl
  exact (grD ν).grFam_enum S hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+ζ_{Γ₀+1}}))`.** -/
theorem grE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG grE)) :
    CdCapV S l := by
  obtain ⟨ν, -, h⟩ := grE_cof S hl
  exact (grD ν).grFam_capV S hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+ζ_{Γ₀+1}}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem grE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG grE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG grE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG grE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < iota S (gcG grE)
    · exact (grE_enum S hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG grE)
    · exact (grE_enum S hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG grE)
    · exact grE_capV S hr h
    · exact hV l hr hω (not_lt.1 h)

/-! ## The place of the frontier -/

theorem grE_lt_G1 : grE < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : gcG 0 + grK < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) grK_lt_gcG1
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+ζ_{Γ₀+1}}) < Ω₂`.** -/
theorem grE_le_Om2 : gcG grE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG grE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (grE_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+ζ_{Γ₀+1}})) < L(0)`.** -/
theorem grE_P (S : InaccSeq.{0}) : Pv S (gcG grE) < Nc.ncL S 0 := ga_Pv_lt_L0 S grE_le_Om2.le

/-- **The order of the frontiers**: the round-88 frontier `ι(Γ(ε_{G+Γ₀}))` lies below `ι(Γ(ε_{G+Γ₀})·ω)` (the frontier
of the code `ε_{G+Γ₀}`, `gr_loc_gam0`), which lies below `ι(Γ(ε_{G+Γ₀+1}))`; every `ι(Γ(ε_{G+ν}))`, `ν < ζ_{Γ₀+1}`,
lies below `ι(Γ(ε_{G+ζ_{Γ₀+1}})) ≤ ι(Ω₂)`, and `P(Γ(ε_{G+ζ_{Γ₀+1}})) ≤ P(Ω₂) < L(0)`. -/
theorem grE_fr_order (S : InaccSeq.{0}) :
    iota S (gcG gqE) < iota S (gcG gqE * ω) ∧
      iota S (gcG gqE * ω) < iota S (gcG (grD (gamma 0 + 1)).B) ∧
      (∀ ν, ν < grK → iota S (gcG (grD ν).B) ≤ iota S (gcG grE)) ∧
      iota S (gcG grE) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG grE) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have h0 : gamma 0 < grK := gam0_lt_grK
  have h1 : gamma 0 + 1 < grK := grK_lim.add_one_lt h0
  have e : gqE = (grD (gamma 0)).B := (grD_B h0).symm
  have hB : gqE < (grD (gamma 0 + 1)).B := by
    rw [e]; exact grD_B_lt (lt_add_one _) h1
  have hgE : (grD (gamma 0 + 1)).g gqE < Td.tdK S := by
    rw [e, grD_succ, GrD.step_g_B]
    exact (grD_γ h0).trans_lt (gr_gam0_lt_tdK S)
  have hG : InE (gcG gqE) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hgood := grGood_mul (grD (gamma 0 + 1)).toRS (c := gqE) hB S hgE
  have hgood0 : Bt.Good S (gcG gqE) := by
    refine gr_good (K := (grD (gamma 0 + 1)).toRS.K) fun Z _ hKZ => ?_
    exact GxCl.atom (gmG_atom (K := (grD (gamma 0 + 1)).toRS.K) hB (hgE.trans_le hKZ))
  refine ⟨cd_iota_lt_of_good hgood0 (lt_mul_of_one_lt_right hG.pos one_lt_omega0), ?_, fun ν hν =>
    iota_mono _ _ (gcG_lt (grD_B_lt_E hν)).le, iota_mono _ _ grE_le_Om2.le, Nm.Pv_mono grE_le_Om2.le,
    ga_Pv_lt_L0 S le_rfl⟩
  have hV : InE (gcG (grD (gamma 0 + 1)).B) := Low.opow_eq_self_of_SC (gcG_SC _)
  exact cd_iota_lt_of_good hgood (InE.mul_lt hV (gcG_lt hB) (omega0_lt_inE hV))

end Googology.Trans.PoR.InaccPsi.R2.Gr
