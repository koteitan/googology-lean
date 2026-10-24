import Googology.Trans.PoR.InaccPsi.R2.GoHL

/-!
# EVERY DIGIT SYSTEM IS A READING SYSTEM: layers, frontiers and the road below `ι(Γ_{Ω₁+1+B})`

A digit system `D : GoD` (`R2.GoD`) is a code system `D.toK : Gm.GmCS` (bound `B = D.B`, gate `D.g`) and a reading
system `D.toRS : Gm.GmRS` (reading `D.R`): the last term of a limit code comes from `D.ld`, and Lemma IMG for its
logend `T` from `R2.GnZ` (`gnPkg_of_exZ`: `T` has Lemma EXACT and `T(ρ) ≤ c(ρ) < b(ρ) < ε_{b(ρ)+1} < ζ_{Γ_{ρ+1}+1}`).
The generic results of `R2.GmRS`, `R2.GmLoc` then give, for every code `c ∈ [ε_{Ω₁+1}, B)`:

* `GoD.go_spec` (**the gated layer of `c`**: gate `D.g c`, top `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}`);
* `GoD.go_loc` (every code with gate below `ε₀` located: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`);
* `GoD.go_sup` (**`sup = ι(Γ_{Ω₁+1+B})`, `P(Γ_{Ω₁+1+B}) < L(0)`**), `GoD.go_blk` (BLK^O and the exact reaches),
  `GoD.go_enum` (ENUM-REACH, fixed points included), `GoD.go_capV` (CapV) below it, `GoD.go_road` (the road with UPPER,
  LOWER, CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+B})`), `GoD.go_fr_order`.

No new axiom.  New definitions: `GoD.toK`, `GoD.toRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Go

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GoD

variable (D : GoD)

/-- **The codes below `c ≤ B` with gate below `y < Ω₁` are countably many** (the reading is injective). -/
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

/-- **The code system of a digit system**: bound `B`, gate `D.g`. -/
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

theorem toK_B : D.toK.B = D.B := rfl

theorem toK_gt : D.toK.gt = D.g := rfl

/-- **Cofinality above `ε_{Ω₁+1}`** (the field `cof` of a reading system). -/
theorem cofE {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < D.B) (hEc : gfE < c) (hg : D.g c < x)
    {ν : Ordinal.{0}} (hν : ν < D.R c x) : ∃ b, gfE ≤ b ∧ b < c ∧ D.g b < x ∧ ν ≤ D.R b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := D.cof x hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [D.g_E]; exact hx.pos, ?_⟩
    exact hνb.trans (D.mono x hx hx1 gfE D.E_lt_B b hbE (by rw [D.g_E]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

/-- **The data of the union at a limit code** (`Gm.GmLD`): the last term from `D.ld`, Lemma IMG for the logend from
`R2.GnZ`. -/
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

/-- **THE READING SYSTEM of a digit system.** -/
noncomputable def toRS : GmRS where
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
  cf := D.cf
  cf_ge := D.cf_ge
  cf_lt := D.cf_lt
  cf_g := D.cf_g
  cf_mono := D.cf_mono
  cf_cof := D.cf_cof

theorem toRS_V : D.toRS.K.V = gcG D.B := rfl

/-- **THE GENERIC THEOREM for every code `c ∈ [ε_{Ω₁+1}, B)` of a digit system**: a gated base package with gate
`D.g c` whose top is `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}` at every `ε`-number base `x < Ω₁` above the gate. -/
theorem go_spec : ∀ c, gfE ≤ c → c < D.B → ∃ B : GdB, B.g = D.g c ∧
    ∀ x, InE x → x < Om1 → D.g c < x → B.K.E x = gq (D.R c x) x ∧ B.K.sys.top x = gq (D.R c x) x :=
  fun c h hc => ⟨D.toRS.gmL c h hc, D.toRS.gmL_g h hc, fun _ hx hx1 hg =>
    ⟨D.toRS.gmL_E h hc hx hx1 hg, D.toRS.gmL_top h hc hx hx1 hg⟩⟩

/-- **Every code with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `υ` of it `= P(⋯) < L(0)`. -/
theorem go_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < D.B) (hg : D.g c < ε₀) (S : InaccSeq.{0}) :
    xtB1 (D.toRS.gmX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (D.toRS.gmX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  D.toRS.gmLoc c h hc hg S

/-- **`sup = ι(Γ_{Ω₁+1+B})`, `υ` of it `= P(Γ_{Ω₁+1+B}) < L(0)`.** -/
theorem go_sup (S : InaccSeq.{0}) : (D.toRS.gmFam S).famSup = iota S (gcG D.B) ∧
    upsilon (D.toRS.gmFam S).famSup = Pv S (gcG D.B) ∧ Pv S (gcG D.B) < Nc.ncL S 0 := D.toRS.gmFam_sup S

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+1+B})} = P(Γ_{Ω₁+1+B})`**, with the exact reaches. -/
theorem go_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (D.toRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (D.toRS.gmFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (D.toRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (D.toRS.gmFam S).off k l)) ∧
    (∀ α < upsilon (D.toRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  D.toRS.gmFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+B})`, fixed points included.** -/
theorem go_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B)) :
    CdUpper S l ∧ CdLower S l := D.toRS.gmFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+B})`.** -/
theorem go_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG D.B)) :
    CdCapV S l := D.toRS.gmFam_capV S hr hl

/-- **THE ROAD past every code of a digit system**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+B})` (CapV also
`υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem go_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG D.B) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG D.B) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG D.B) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  D.toRS.gmFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+B}) < ι(Ω₂)`, `P(Γ_{Ω₁+1+B}) < P(Ω₂) < L(0)`. -/
theorem go_fr_order {c : Ordinal.{0}} (hc : c < D.B) (hg : D.g c < ε₀) (S : InaccSeq.{0}) :
    iota S (gcG c * ω) < iota S (gcG D.B) ∧ iota S (gcG D.B) < iota S (Om (1 + 1)) ∧
      Pv S (gcG D.B) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 :=
  D.toRS.gm_fr_order hc hg S

end GoD

end Googology.Trans.PoR.InaccPsi.R2.Go
