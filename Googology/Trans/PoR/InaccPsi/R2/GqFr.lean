import Googology.Trans.PoR.InaccPsi.R2.GqLoc
import Googology.Trans.PoR.InaccPsi.R2.GpFr

/-!
# THE FRONTIERS OF THE GATED DIGIT SYSTEMS: `ι(Γ(ε_{G+ν}))` for every `ν < Γ₀`, the sup `ι(Γ(ε_{G+Γ₀}))`

`G = Γ_{Ω₁+1}`, `Γ(c) = Γ_{Ω₁+1+c}`.  A gated digit system `D : GqD` (`R2.GqD`) is a reading system `D.toRS : GqRS`
(`R2.GqRS`; the proofs of `R2.GoRS`); its cofinal codes have gates `≤ max γ ε₀ < Γ₀`, so each is located by the
gated location theorem (`R2.GqLoc`), and their layers form a family with supremum `ι(Γ(B))`.  For the recursion
`gqD ν` (`R2.GqRec`):

* `GqD.toK`, `GqD.toRS`, `GqD.gqFam`, `GqD.gqFam_sup` (**`sup = ι(Γ(B))`, `P(Γ(B)) < L(0)`**), `GqD.gqFam_enum`,
  `GqD.gqFam_capV`, `GqD.gqFam_blk`;
* `gq_supE`, `gq_enum`, `gq_capV`, `gq_blk` (**every `ν < Γ₀`**: BLK^O, exact reaches, ENUM-REACH, CapV below
  `ι(Γ(ε_{G+ν}))`), `gq_loc` (**every code of `gqD ν` with gate below `Γ₀` located**), `gq_loc_eps0` (**the code
  `ε_{G+ε₀}` itself, gate `ε₀`: `Λ⁺ = ι(Γ(ε_{G+ε₀})·ω)`**, past the round-87 frontier `ι(Γ(ε_{G+ε₀}))`);
* `gqE = φ(1, G + Γ₀)`, `gqE_cof`, `gqE_enum`, `gqE_capV`, `gqE_road` (**THE ROAD with UPPER, LOWER, CapV asked only
  at `λ ≥ ι(Γ(ε_{G+Γ₀}))`**), `gqE_le_Om2`, `gqE_P`, `gqE_fr_order` (**`ι(Γ(ε_{G+ε₀})) < ι(Γ(ε_{G+ε₀})·ω) <
  ι(Γ(ε_{G+Γ₀})) ≤ ι(Ω₂)`**), `gq_wall` (**the first failing index `Γ₀`**: a base gate `γ` is admissible iff
  `γ < Γ₀`).

No new axiom.  New definitions: `GqD.toK`, `GqD.toRS`, `GqD.gqXk`, `GqD.gqFam`, `gqE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gq

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GqD

variable (D : GqD)

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

theorem cf_g' (k : ℕ) : D.g (D.cf k) < gamma 0 :=
  (D.cf_g k).trans_lt (max_lt D.γ_lt gq_eps0_lt_gam)

/-- The `k`-th member of the cofinal family: the code `D.cf k`. -/
noncomputable def gqXk (S : InaccSeq.{0}) (k : ℕ) : XtSys :=
  D.toRS.gqX (D.cf k) (D.cf_ge k) (D.cf_lt k) (D.cf_g' k) S

theorem gqXk_loc (S : InaccSeq.{0}) (k : ℕ) : xtB1 (D.gqXk S k) = iota S (gcG (D.cf k) * ω) :=
  (D.toRS.gqLoc _ _ _ _ S).1

/-- **The family of the layers of the cofinal codes.** -/
noncomputable def gqFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (D.gqXk S k)
  off := fun k => xtOrec (D.gqXk S k)
  spec := fun k => xtSpec1 (D.toRS.gqX_pkg _ _ _ _ S)
  mono := fun k => by
    show xtB1 (D.gqXk S k) < xtB1 (D.gqXk S (k + 1))
    rw [D.gqXk_loc S, D.gqXk_loc S]
    refine cd_iota_lt_of_good (D.toRS.gqGood_mul (D.cf_lt k) (D.cf_g' k) S) ?_
    have hE := geG_E (D.cf (k + 1))
    exact (InE.mul_lt hE (gcG_lt (D.cf_mono k)) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => D.toRS.gqX_nonfix _ _ _ _ S

/-- **`sup_k Λ⁺(gqXk k) = ι(Γ(B))`, `υ` of it `= P(Γ(B)) < L(0)`.** -/
theorem gqFam_sup (S : InaccSeq.{0}) : (D.gqFam S).famSup = iota S (gcG D.B) ∧
    upsilon (D.gqFam S).famSup = Pv S (gcG D.B) ∧ Pv S (gcG D.B) < Nc.ncL S 0 := by
  have hVS : SC D.toRS.K.V := gmV_SC
  have hVE : ω ^ D.toRS.K.V = D.toRS.K.V := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < D.B → gcG c * ω < D.toRS.K.V := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (D.gqFam S).famSup = iota S D.toRS.K.V := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (D.gqXk S k) ≤ _
      rw [D.gqXk_loc S k]
      exact iota_mono _ _ (hstep _ (D.cf_lt k)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit D.B_lim e.2
      obtain ⟨n, hn⟩ := D.cf_cof c hc
      have h1 : e.1 < gcG (D.cf n) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (D.cf n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (D.gqXk S n) := (D.gqXk_loc S n).symm
        _ ≤ (D.gqFam S).famSup := ((D.gqFam S).famBd_lt n).le
  have hups : upsilon (D.gqFam S).famSup = Pv S D.toRS.K.V := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gmV_lt_Om2 D.toRS.K S).le⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(B))`, fixed points included.** -/
theorem gqFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (D.gqFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (D.gqFam S).famLt hl
  have hk' : l < iota S (gcG (D.cf k) * ω) := by rw [← D.gqXk_loc S k]; exact hk
  exact D.toRS.gqEnum _ (D.cf_ge k) (D.cf_lt k) (D.cf_g' k) S hr hk'

/-- **CapV at every range restart below `ι(Γ(B))`, fixed points included.** -/
theorem gqFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B)) :
    CdCapV S l := by
  rw [← (D.gqFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (D.gqFam S).famLt hl
  have hk' : l < iota S (gcG (D.cf k) * ω) := by rw [← D.gqXk_loc S k]; exact hk
  exact D.toRS.gqCapV _ (D.cf_ge k) (D.cf_lt k) (D.cf_g' k) S hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ(B))} = P(Γ(B))`**, with the exact reaches. -/
theorem gqFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (D.gqFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (D.gqFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (D.gqFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (D.gqFam S).off k l)) ∧
    (∀ α < upsilon (D.gqFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (D.gqFam S).famBlk

end GqD

/-! ## Each `gqD ν`, `ν < Γ₀` -/

section Each

variable {ν : Ordinal.{0}} (hν : ν < gqK)
include hν

/-- **`sup = ι(Γ(ε_{G+ν}))`, `υ` of it `= P(Γ(ε_{G+ν})) < L(0)`.** -/
theorem gq_supE (S : InaccSeq.{0}) : ((gqD ν).gqFam S).famSup = iota S (gcG (veblen 1 (gcG 0 + ν))) ∧
    upsilon ((gqD ν).gqFam S).famSup = Pv S (gcG (veblen 1 (gcG 0 + ν))) ∧
    Pv S (gcG (veblen 1 (gcG 0 + ν))) < Nc.ncL S 0 := by
  rw [← gqD_B hν]; exact (gqD ν).gqFam_sup S

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+ν}))`, fixed points included.** -/
theorem gq_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) : CdUpper S l ∧ CdLower S l :=
  (gqD ν).gqFam_enum S hr (by rw [gqD_B hν]; exact hl)

/-- **CapV at every range restart below `ι(Γ(ε_{G+ν}))`.** -/
theorem gq_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (veblen 1 (gcG 0 + ν)))) : CdCapV S l :=
  (gqD ν).gqFam_capV S hr (by rw [gqD_B hν]; exact hl)

/-- **Every code `c ∈ [ε_{Ω₁+1}, ε_{G+ν})` of `gqD ν` with gate below `Γ₀` located**: `Λ⁺ = ι(Γ(c)·ω)`,
`P(Γ(c)·ω) < L(0)`. -/
theorem gq_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < veblen 1 (gcG 0 + ν)) (hg : (gqD ν).g c < gamma 0)
    (S : InaccSeq.{0}) :
    xtB1 ((gqD ν).toRS.gqX c h (by show c < (gqD ν).B; rw [gqD_B hν]; exact hc) hg S) = iota S (gcG c * ω) ∧
    Pv S (gcG c * ω) < Nc.ncL S 0 :=
  let h' := (gqD ν).toRS.gqLoc c h (by show c < (gqD ν).B; rw [gqD_B hν]; exact hc) hg S
  ⟨h'.1, h'.2.2⟩

end Each

/-- **Theorem BLK^O below `P(Γ(ε_{G+ν}))`** (the supremum of `gqD ν`, `gq_supE`), with the exact reaches. -/
theorem gq_blk (ν : Ordinal.{0}) (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon ((gqD ν).gqFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < ((gqD ν).gqFam S).famSup ∧
        c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < ((gqD ν).gqFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + ((gqD ν).gqFam S).off k l)) ∧
    (∀ α < upsilon ((gqD ν).gqFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (gqD ν).gqFam_blk S

theorem gq_eps0_lt_K : (ε₀ : Ordinal.{0}) < gqK := gq_eps0_lt_gam

theorem gqK_lim : IsSuccLimit gqK := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (Lq.lq_gamma_SC 0))

/-- **THE CODE `ε_{G+ε₀}` ITSELF IS LOCATED** (gate `≤ ε₀`, a code of `gqD (ε₀+1)`): `Λ⁺ = ι(Γ(ε_{G+ε₀})·ω)`,
`P(Γ(ε_{G+ε₀})·ω) < L(0)`. -/
theorem gq_loc_eps0 (S : InaccSeq.{0}) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (veblen 1 (gcG 0 + ε₀)) * ω) ∧
      Pv S (gcG (veblen 1 (gcG 0 + ε₀)) * ω) < Nc.ncL S 0 := by
  have h1 : ε₀ + 1 < gqK := gqK_lim.add_one_lt gq_eps0_lt_K
  set D := gqD (ε₀ + 1) with hD
  have hB : (gqD ε₀).B < D.B := gqD_B_lt (lt_add_one _) h1
  have hg : D.g (gqD ε₀).B < gamma 0 := by
    rw [hD, gqD_succ, GqD.step_g_B]
    exact (gqD_γ gq_eps0_lt_K).trans_lt gq_eps0_lt_gam
  have hE : gfE ≤ (gqD ε₀).B := (gqD ε₀).E_lt_B.le
  obtain ⟨l1, -, l3⟩ := D.toRS.gqLoc _ hE hB hg S
  refine ⟨D.toRS.gqX _ hE hB hg S, D.toRS.gqX_pkg _ hE hB hg S, ?_, ?_⟩
  · rw [l1, gqD_B gq_eps0_lt_K]
  · rw [← gqD_B gq_eps0_lt_K]; exact l3

/-! ## The whole recursion: the bound `ε_{G+Γ₀}` -/

/-- **The bound of the whole recursion**: `ε_{G+Γ₀} = φ(1, G + Γ₀)`. -/
noncomputable def gqE : Ordinal.{0} := veblen 1 (gcG 0 + gqK)

theorem gqE_lim : IsSuccLimit gqE := ev_isSuccLimit_of_inE (omega0_opow_epsilon _)

/-- **Every code below `ε_{G+Γ₀}` is a code of some `gqD ν`, `ν < Γ₀`.** -/
theorem gqE_codes {c : Ordinal.{0}} (hc : c < gqE) : ∃ ν, ν < gqK ∧ c < (gqD ν).B := by
  obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ gqK_lim)).1 hc
  obtain ⟨d, hd, htd⟩ := (lt_add_iff gqK_lim.bot_lt.ne').1 ht
  exact ⟨d, hd, by rw [gqD_B hd]; exact hct.trans_le ((isNormal_veblen 1).monotone htd)⟩

theorem gqD_B_lt_E {ν : Ordinal.{0}} (hν : ν < gqK) : (gqD ν).B < gqE := by
  rw [gqD_B hν]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 hν)

/-- **`ι(Γ(ε_{G+Γ₀})) = sup_{ν<Γ₀} ι(Γ(ε_{G+ν}))`**. -/
theorem gqE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG gqE)) :
    ∃ ν, ν < gqK ∧ l < iota S (gcG (gqD ν).B) := by
  have hlim : IsSuccLimit (gcG gqE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG gqE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gqE_lim e.2
  obtain ⟨ν, hν, hβν⟩ := gqE_codes hβ
  exact ⟨ν, hν, he.trans_le (iota_mono _ _ (heβ.trans (gcG_lt hβν)).le)⟩

/-- **ENUM-REACH at every range restart below `ι(Γ(ε_{G+Γ₀}))`, fixed points included.** -/
theorem gqE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gqE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, -, h⟩ := gqE_cof S hl
  exact (gqD ν).gqFam_enum S hr h

/-- **CapV at every range restart below `ι(Γ(ε_{G+Γ₀}))`.** -/
theorem gqE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG gqE)) :
    CdCapV S l := by
  obtain ⟨ν, -, h⟩ := gqE_cof S hl
  exact (gqD ν).gqFam_capV S hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(ε_{G+Γ₀}))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gqE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG gqE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG gqE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG gqE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  refine goGl.go_road S (fun l hr _ => ?_) (fun l hr _ => ?_) (fun l hr hω _ => ?_) hC hEQ hrest hB2
  · by_cases h : l < iota S (gcG gqE)
    · exact (gqE_enum S hr h).1
    · exact hU l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gqE)
    · exact (gqE_enum S hr h).2
    · exact hL l hr (not_lt.1 h)
  · by_cases h : l < iota S (gcG gqE)
    · exact gqE_capV S hr h
    · exact hV l hr hω (not_lt.1 h)

/-! ## The place of the frontier -/

theorem gqE_lt_G1 : gqE < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : gcG 0 + gqK < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) gqK_lt_gcG1
  exact (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE hE)) _ h1

/-- **`Γ(ε_{G+Γ₀}) < Ω₂`.** -/
theorem gqE_le_Om2 : gcG gqE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG gqE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (gqE_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(ε_{G+Γ₀})) < L(0)`.** -/
theorem gqE_P (S : InaccSeq.{0}) : Pv S (gcG gqE) < Nc.ncL S 0 := ga_Pv_lt_L0 S gqE_le_Om2.le

/-- **The order of the frontiers**: the round-87 frontier `ι(Γ(ε_{G+ε₀}))` lies below `ι(Γ(ε_{G+ε₀})·ω)` (the frontier
of the code `ε_{G+ε₀}`, `gq_loc_eps0`), which lies below `ι(Γ(ε_{G+ε₀+1}))`; every `ι(Γ(ε_{G+ν}))`, `ν < Γ₀`, lies
below `ι(Γ(ε_{G+Γ₀})) ≤ ι(Ω₂)`, and `P(Γ(ε_{G+Γ₀})) ≤ P(Ω₂) < L(0)`. -/
theorem gqE_fr_order (S : InaccSeq.{0}) :
    iota S (gcG gpE) < iota S (gcG gpE * ω) ∧
      iota S (gcG gpE * ω) < iota S (gcG (gqD (ε₀ + 1)).B) ∧
      (∀ ν, ν < gqK → iota S (gcG (gqD ν).B) ≤ iota S (gcG gqE)) ∧
      iota S (gcG gqE) ≤ iota S (Om (1 + 1)) ∧ Pv S (gcG gqE) ≤ Pv S (Om (1 + 1)) ∧
      Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have h1 : ε₀ + 1 < gqK := gqK_lim.add_one_lt gq_eps0_lt_K
  have hB : gpE < (gqD (ε₀ + 1)).B := by
    rw [gqD_B h1]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one _))
  have hgE : (gqD (ε₀ + 1)).g gpE < gamma 0 := by
    have e : gpE = (gqD ε₀).B := (gqD_B gq_eps0_lt_K).symm
    rw [e, gqD_succ, GqD.step_g_B]
    exact (gqD_γ gq_eps0_lt_K).trans_lt gq_eps0_lt_gam
  have hG : InE (gcG gpE) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hgood := (gqD (ε₀ + 1)).toRS.gqGood_mul (c := gpE) hB hgE S
  have hgood0 : Bt.Good S (gcG gpE) := by
    refine gm_good (K := (gqD (ε₀ + 1)).toRS.K) fun Z hZ => ?_
    exact GxCl.atom (gmG_atom (K := (gqD (ε₀ + 1)).toRS.K) hB (hgE.trans_le (Ta.taGam_le_SC hZ)))
  refine ⟨cd_iota_lt_of_good hgood0 (lt_mul_of_one_lt_right hG.pos one_lt_omega0), ?_, fun ν hν =>
    iota_mono _ _ (gcG_lt (gqD_B_lt_E hν)).le, iota_mono _ _ gqE_le_Om2.le, Nm.Pv_mono gqE_le_Om2.le,
    ga_Pv_lt_L0 S le_rfl⟩
  have hV : InE (gcG (gqD (ε₀ + 1)).B) := Low.opow_eq_self_of_SC (gcG_SC _)
  exact cd_iota_lt_of_good hgood (InE.mul_lt hV (gcG_lt hB) (omega0_lt_inE hV))

/-- **THE FIRST FAILING INDEX `Γ₀`**: the codes of the step above a base with gate `γ` have gates `≥ γ`; the field
`code_gate` asks them below every `Z ≤ Ω₁` closed under `+` and `φ`, and that holds iff `γ < Γ₀` (`Z = Γ₀` is such a
closure).  So the constant index `ν = Γ₀` (base reading `φ(1, Γ_{x+1}-index + Γ₀)`, exact only above `Γ₀`) is the first
index the gated recursion cannot take; the frontier lemma `Gm.gmB1_eq` (codes over every strongly critical `Z`) stops
at the same point. -/
theorem gq_wall (γ : Ordinal.{0}) :
    (∀ Z : Ordinal.{0}, Z ≤ Om1 → 0 < Z → (∀ u v, u < Z → v < Z → u + v < Z) →
      (∀ u v, u < Z → v < Z → veblen u v < Z) → γ < Z) ↔ γ < gamma 0 := by
  refine ⟨fun h => ?_, fun h Z _ hZ0 _ hZp => h.trans_le (gq_gam_le hZ0 hZp)⟩
  have hS := Lq.lq_gamma_SC 0
  have hE : InE (gamma 0) := Low.opow_eq_self_of_SC hS
  exact h _ gq_gam_lt_Om1.le hS.1 (fun u v hu hv => (inE_indec hE).add_lt hu hv)
    (fun u v hu hv => hS.2 u hu v hv)

end Googology.Trans.PoR.InaccPsi.R2.Gq
