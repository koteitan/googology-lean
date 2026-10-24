import Googology.Trans.PoR.InaccPsi.R2.GmQ2

/-!
# THE READING SYSTEM BELOW `Γ_{Ω₁+1}²` AND ITS FRONTIERS: `sup = ι(Γ_{Γ_{Ω₁+1}²})`

* `gmV_good` (**`Γ_{Ω₁+1+B}` is good** for every code system), `mqRS` (**THE READING SYSTEM** of the codes below
  `Γ_{Ω₁+1}²`: code system `mqCS`, reading `mqR`, last terms `mqLD`, cofinal codes `Γ_{Ω₁+1}·c_k`, gate `0`);
* `mq_spec` (**the gated layer of every code `c = Γ_{Ω₁+1}·γ + c'`**: gate `mqG c`, top
  `ϑˣ(Ω₁·Ω₁ + Γ_{x+1}·γ(x) + c'(x))`), `mq_loc` (**every such code with gate below `ε₀` located**:
  `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`);
* `mqW_sup` (**`sup = ι(Γ_{Γ_{Ω₁+1}²})`, `P(Γ_{Γ_{Ω₁+1}²}) < L(0)`**), `mqFam_blk`, `mqFam_enum`, `mqFam_capV`,
  `mqFam_road`, `mq_fr_order` (**`ι(Γ_{Γ_{Ω₁+1}·ω}) < ι(Γ_{Γ_{Ω₁+1}²}) < ι(Ω₂)`**).

No new axiom.  New definition: `mqRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **`Γ_{Ω₁+1+B}` is good** (it lies in the hull of its own `A`), for every code system. -/
theorem gmV_good (K : GmCS) (S : InaccSeq.{0}) : Bt.Good S K.V := by
  show K.V ∈ S.CSet (ConjT.Aη S K.V + 1) (S.psi (ConjT.Aη S K.V) (Om 1))
  have := CSet.psi_mem (S := S) (a := ConjT.Aη S K.V + 1) (b := S.psi (ConjT.Aη S K.V) (Om 1))
    (gm_B_lt_A1 (S := S) K K.V) (InR_Om_succ 1) (ga_Om2_mem _ _) (K.B_mem S _ _ (gm_B_lt_A1 (S := S) K K.V))
  rwa [gmV_psi K S] at this

theorem mqG_mulC (n : ℕ) : mqG (gcG 0 * gmC n) = 0 := by
  have hω : ω ≤ gmC n := omega_lt_Om1.le.trans (Om1_lt_eW.le.trans (gmC_spec n).1)
  have := mqG_split (gmC n) gl_G0_E.pos
  rw [add_zero] at this
  rw [this, glG_zero, max_eq_left zero_le, mq_glQ_inf hω, (gmC_spec n).2.2]

/-- **THE READING SYSTEM of the codes below `Γ_{Ω₁+1}²`.** -/
noncomputable def mqRS : GmRS where
  K := mqCS
  R := mqR
  E_lt := mq_E_lt_B
  B_lim := mqB_lim
  gt_E := mqG_E
  gt_lowE := fun _ hc => mqG_lowE hc
  R_E := fun x _ _ => mqR_E x
  lt0 := fun _ _ hx hx1 hc hg => mqR_lt1 hx hx1 hc hg
  mono := fun _ _ _ hx hx1 hc hbc hgb hgc => mqR_mono hx hx1 hc hbc hgb hgc
  succ := fun b x _ => mqR_succ b x
  gt_le_succ := mqG_le_succ
  cof := fun _ _ hx hx1 hc hEc hg _ hν => mqR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ _ hB hc hg => mqR_pi hB hc hg
  ld := mqLD
  cf := fun k => gcG 0 * gmC k
  cf_ge := fun k => gfE_lt_G0.le.trans (le_mul_of_one_le_right'
    (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le (Om1_lt_eW.trans_le (gmC_spec k).1))))
  cf_lt := fun k => (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (gmC_lt_G0 k)
  cf_g := fun k => by show mqG _ < ε₀; rw [mqG_mulC]; exact epsilon_pos 0
  cf_mono := fun k => (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (gmC_mono k)
  cf_cof := fun c hc => by
    obtain ⟨γ, c', hγ, hc', rfl⟩ := mq_split hc
    obtain ⟨n, hn⟩ := gmC_cof hγ
    refine ⟨n, ?_⟩
    show gcG 0 * γ + c' < gcG 0 * gmC n
    calc gcG 0 * γ + c' < gcG 0 * (γ + 1) := by rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hc'
      _ ≤ gcG 0 * gmC n := mul_le_mul_left' (Order.add_one_le_of_lt hn) _

theorem mqRS_V : mqRS.K.V = gcG mqB := rfl

/-- **THE GATED LAYER OF EVERY CODE `c ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1}²)`**: gate `mqG c`, top `ϑˣ(Ω₁·Ω₁ + c(x))` at every
`ε`-number base `x < Ω₁` above the gate, `c(x) = Γ_{x+1}·γ(x) + c'(x)` for `c = Γ_{Ω₁+1}·γ + c'`. -/
theorem mq_spec : ∀ c, gfE ≤ c → c < mqB → ∃ B : GdB, B.g = mqG c ∧
    ∀ x, InE x → x < Om1 → mqG c < x → B.K.E x = gq (mqR c x) x ∧ B.K.sys.top x = gq (mqR c x) x :=
  fun c h hc => ⟨mqRS.gmL c h hc, mqRS.gmL_g h hc, fun _ hx hx1 hg =>
    ⟨mqRS.gmL_E h hc hx hx1 hg, mqRS.gmL_top h hc hx hx1 hg⟩⟩

/-- **Every code `c ∈ [ε_{Ω₁+1}, Γ_{Ω₁+1}²)` with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`,
`υ` of it `= P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem mq_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < mqB) (hg : mqG c < ε₀) (S : InaccSeq.{0}) :
    xtB1 (mqRS.gmX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (mqRS.gmX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  mqRS.gmLoc c h hc hg S

/-- **`sup = ι(Γ_{Γ_{Ω₁+1}²})`, `υ` of it `= P(Γ_{Γ_{Ω₁+1}²}) < L(0)`.** -/
theorem mqW_sup (S : InaccSeq.{0}) : (mqRS.gmFam S).famSup = iota S (gcG mqB) ∧
    upsilon (mqRS.gmFam S).famSup = Pv S (gcG mqB) ∧ Pv S (gcG mqB) < Nc.ncL S 0 :=
  mqRS.gmFam_sup S

/-- **Theorem BLK^O below `υ_{ι(Γ_{Γ_{Ω₁+1}²})} = P(Γ_{Γ_{Ω₁+1}²})`**, with the exact reaches. -/
theorem mqFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (mqRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (mqRS.gmFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (mqRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (mqRS.gmFam S).off k l)) ∧
    (∀ α < upsilon (mqRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  mqRS.gmFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{Γ_{Ω₁+1}²})`, fixed points included.** -/
theorem mqFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG mqB)) :
    CdUpper S l ∧ CdLower S l := mqRS.gmFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{Γ_{Ω₁+1}²})`.** -/
theorem mqFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG mqB)) :
    CdCapV S l := mqRS.gmFam_capV S hr hl

/-- **THE ROAD past every code below `Γ_{Ω₁+1}²`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Γ_{Ω₁+1}²})`
(CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the
reaches. -/
theorem mqFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG mqB) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG mqB) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG mqB) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mqRS.gmFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{Γ_{Ω₁+1}·ω}) < ι(Γ_{Γ_{Ω₁+1}²}) < ι(Ω₂)`, and
`P(Γ_{Γ_{Ω₁+1}²}) < P(Ω₂) < L(0)`. -/
theorem mq_fr_order (S : InaccSeq.{0}) :
    iota S (gcG mgB) < iota S (gcG mqB) ∧ iota S (gcG mqB) < iota S (Om (1 + 1)) ∧
      Pv S (gcG mqB) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hBB : mgB < mqB := (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (omega0_lt_inE gl_G0_E)
  have h1 : iota S (gcG mgB) < iota S (gcG mqB) := cd_iota_lt_of_good (gmV_good mgCS S) (gcG_lt hBB)
  have h3 : iota S (gcG mqB) < iota S (Om (1 + 1)) := cd_iota_lt_of_good (gmV_good mqCS S) (gmV_lt_Om2 mqCS S)
  have h4 : Pv S (gcG mqB) < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h3
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h1, h3, h4, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gm
