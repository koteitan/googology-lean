import Googology.Trans.PoR.InaccPsi.R2.GkU8

/-!
# CODES BELOW `ζ_{Ω₁+1}` AS ONE READING SYSTEM: layers, frontiers and the road up to `ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})`

The code system `guK` (every pseudo-base `ε_{Ω₁+ν}`, `ν < ζ_{Ω₁+1}`), the reading `guR` (`ε_{Ω₁+ν} ↦ ε_{x+ν(x)}`,
`Ω₁ ↦ x`) and the last terms `gu_ld` form a reading system `guRS` (`R2.GiRS`) with the cofinal codes
`ε_{Ω₁+1}, ε_{Ω₁+ε_{Ω₁+1}}, …` (gate `0`).  The generic theorems of `R2.GiRS`, `R2.GiLoc` then give:

* `gu_GiLD` (the field `ld`), `guCf` (the cofinal codes), `guRS`;
* `gu_spec` (**the gated layer of every code `c < ζ_{Ω₁+1}`**: top `Γ_{x+1+c(x)}`), `gu_loc` (**every code with gate
  below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`), `gu_eNNw_loc` (**the code `ε_{Ω₁+2}·ω`, where round 81
  stopped**), `gu_eAw_loc` (the code `ε_{Ω₁+ω}`);
* `guW_sup` (**`sup = ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})`, `P(Γ_{Ω₁+1+ζ_{Ω₁+1}}) < L(0)`**), `guFam_enum` (**ENUM-REACH**),
  `guFam_capV` (**CapV**), `guFam_blk` (**BLK^O and the exact reaches**), `guFam_road` (**THE ROAD**),
  `gu_fr_order`.

No new axiom.  New definitions: `guCf`, `guRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The field `ld`**: the last term of every limit code `c ∈ (ε_{Ω₁+1}, ζ_{Ω₁+1})`, with Lemma IMG for its logend
(`gkPkg_of_ex`, from Lemma EXACT of the logend). -/
theorem gu_GiLD : ∀ c, IsSuccLimit c → gfE < c → c < guB → Nonempty (GiLD guK guR c) := by
  intro c hl hEc hc
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := gu_ld c hl hc
  have hlg : ∀ x, InE x → x < Om1 → guG c < x → lg (guR c x) = T x := fun x hx hx1 hg => by
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
  · show guG _ ≤ guG c
    split_ifs with h
    · exact hgcp
    · rw [guG_E]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      have hgcp' : gtc cp < x := by rw [← guG_low h]; exact hgcp.trans_lt hg
      rw [guR_E]
      exact e4.trans ((by rw [guR_low h]; exact rdc_lt_eN hx cp hgcp' : guR cp x < eN x)).le
  · intro ρ τ δ h hg
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < evZ ρ := by
      have h1 : T ρ ≤ guR c ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (guR_lt_evZ hρE c hc hg)
    have hP := gkPkg_of_ex h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **The cofinal codes**: `ε_{Ω₁+1}`, `ε_{Ω₁+ε_{Ω₁+1}}`, `ε_{Ω₁+ε_{Ω₁+ε_{Ω₁+1}}}`, … -/
noncomputable def guCf : ℕ → Ordinal.{0}
  | 0 => gfE
  | k + 1 => evA Om1 (guCf k)

theorem guCf_spec : ∀ k : ℕ, gfE ≤ guCf k ∧ guCf k < guB ∧ guG (guCf k) = 0
  | 0 => ⟨le_rfl, gfE_lt_guB, guG_E⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := guCf_spec k
    have hk1 : 1 ≤ guCf k := (one_le_iff_pos.2 eW_E.pos).trans h1
    refine ⟨?_, gu_evA_lt h2, ?_⟩
    · show gfE ≤ evA Om1 (guCf k)
      rw [← gu_evA_one]; exact evA_le_iff.2 hk1
    · show guG (evA Om1 (guCf k)) = 0
      rw [guG_base hk1 h2]
      unfold guQ; split_ifs
      · rfl
      · exact h3

theorem guCf_mono (k : ℕ) : guCf k < guCf (k + 1) :=
  lt_evA_self gu_Om1_E (guCf_spec k).2.1

theorem guCf_cof {c : Ordinal.{0}} (hc : c < guB) : ∃ k : ℕ, c < guCf k := by
  have hle : ∀ i : ℕ, Ordinal.epsilon^[i] (Om1 + 1) ≤ guCf i := by
    intro i
    induction i with
    | zero => exact ((ev_isSuccLimit_of_inE eW_E).add_one_lt Om1_lt_eW).le
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      show Ordinal.epsilon _ ≤ evA Om1 (guCf i)
      rw [gu_evA_eq]
      exact (veblen_le_veblen_iff_right).2 (ih.trans le_add_self)
  obtain ⟨i, hi⟩ := lt_nfp_iff.1 hc
  exact ⟨i, hi.trans_le (hle i)⟩

/-- **THE READING SYSTEM of the codes below `ζ_{Ω₁+1}`** (every pseudo-base `ε_{Ω₁+ν}`). -/
noncomputable def guRS : GiRS where
  K := guK
  R := guR
  E_lt := gfE_lt_guB
  B_lim := guB_lim
  gt_E := guG_E
  gt_lowE := fun _ hc => guG_low hc
  R_E := guR_E
  lt0 := fun _ _ hx hx1 hc hg => guR_lt0 hx hx1 hc hg
  mono := fun _ _ _ hx hc hbc hgb hgc => guR_mono hx hc hbc hgc hgb
  succ := guR_succ_all
  gt_le_succ := guG_le_succ_all
  cof := fun _ _ hx hx1 hc hEc hg _ hν => guR_cofE hx hx1 hc hEc hg hν
  ex := fun _ _ c hB hc hg => gu_pi hB c hc hg
  ld := gu_GiLD
  cf := guCf
  cf_ge := fun k => (guCf_spec k).1
  cf_lt := fun k => (guCf_spec k).2.1
  cf_g := fun k => by rw [show guK.gt = guG from rfl, (guCf_spec k).2.2]; exact epsilon_pos 0
  cf_mono := guCf_mono
  cf_cof := fun _ hc => guCf_cof hc

theorem guRS_V : guRS.K.V = gcG guB := rfl

/-- **THE GENERIC THEOREM for every code `c ∈ [ε_{Ω₁+1}, ζ_{Ω₁+1})`**: a gated base package with gate `guG c` whose
top is `ϑˣ(Ω₁·Ω₁ + c(x)) = Γ_{x+1+c(x)}` at every `ε`-number base `x < Ω₁` above the gate. -/
theorem gu_spec : ∀ c, gfE ≤ c → c < guB → ∃ B : GdB, B.g = guG c ∧
    ∀ x, InE x → x < Om1 → guG c < x → B.K.E x = gq (guR c x) x ∧ B.K.sys.top x = gq (guR c x) x :=
  fun c h hc => ⟨guRS.giL c h hc, guRS.giL_g h hc, fun x hx hx1 hg =>
    ⟨guRS.giL_E h hc hx hx1 hg, guRS.giL_top h hc hx hx1 hg⟩⟩

/-- **Every code `c ∈ [ε_{Ω₁+1}, ζ_{Ω₁+1})` with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`,
`υ` of it `= P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem gu_loc {c : Ordinal.{0}} (h : gfE ≤ c) (hc : c < guB) (hg : guG c < ε₀) (S : InaccSeq.{0}) :
    xtB1 (guRS.giX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (guRS.giX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 :=
  guRS.giLoc c h hc hg S

theorem gu_two_le : (1 : Ordinal.{0}) ≤ 2 := by norm_num

theorem gu_eNN : evA Om1 2 = eN (eN Om1) := by
  rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, evA_eK gu_Om1_E]; rfl

/-- The code `ε_{Ω₁+2}·ω` (where round 81 stopped): a code with gate at most `ω` and reading `ε_{x+2}·ω`. -/
theorem gu_eNNw_facts : gfE ≤ evA Om1 2 * ω ∧ evA Om1 2 * ω < guB ∧ guG (evA Om1 2 * ω) < ε₀ ∧
    ∀ x, InE x → guR (evA Om1 2 * ω) x = evA x 2 * ω := by
  have h2B : (2 : Ordinal.{0}) < guB := ((nat_lt_omega0 2).trans omega_lt_Om1).trans (lt_evZ Om1)
  have hωN : ω < eN (evA Om1 2) :=
    (omega0_lt_inE (evA_E Om1 2)).trans (lt_eN _)
  obtain ⟨-, hB, hg, hR⟩ := gu_mulE gu_two_le h2B ω omega0_ne_zero hωN
  have hωE : ω < gfE := omega_lt_Om1.trans Om1_lt_eW
  refine ⟨?_, hB, ?_, fun x hx => ?_⟩
  · calc gfE = evA Om1 1 := gu_evA_one.symm
      _ ≤ evA Om1 2 := evA_le_iff.2 gu_two_le
      _ ≤ evA Om1 2 * ω := le_mul_of_one_le_right' (one_lt_omega0.le)
  · refine hg.trans_lt (max_lt ?_ ?_)
    · rw [show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num, guQ_nat]; exact epsilon_pos 0
    · rw [guG_low hωE, (rdc_const omega_lt_Om1 0).2]; exact omega0_lt_epsilon 0
  · rw [hR x hx, guR_low hωE, (rdc_const omega_lt_Om1 x).1, show (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by
      norm_num, guR_nat, guA_eq hx (by norm_num)]

/-- **THE CODE `ε_{Ω₁+2}·ω` LOCATED** (round 81 stopped here: its logend `ε_{y+2}+1`): `Λ⁺ = ι(Γ_{Ω₁+1+ε_{Ω₁+2}·ω}·ω)`,
`P(⋯) < L(0)`. -/
theorem gu_eNNw_loc (S : InaccSeq.{0}) :
    xtB1 (guRS.giX _ gu_eNNw_facts.1 gu_eNNw_facts.2.1 gu_eNNw_facts.2.2.1) =
      iota S (gcG (evA Om1 2 * ω) * ω) ∧
    Pv S (gcG (evA Om1 2 * ω) * ω) < Nc.ncL S 0 := by
  obtain ⟨h1, -, h3⟩ := gu_loc gu_eNNw_facts.1 gu_eNNw_facts.2.1 gu_eNNw_facts.2.2.1 S
  exact ⟨h1, h3⟩

/-- The code `ε_{Ω₁+ω}` (the first pseudo-base with a limit index): gate `ω`, reading `ε_{x+ω}`, located. -/
theorem gu_eAw_loc (S : InaccSeq.{0}) :
    ∃ (h1 : gfE ≤ evA Om1 ω) (h2 : evA Om1 ω < guB) (h3 : guG (evA Om1 ω) < ε₀),
      (∀ x, InE x → guR (evA Om1 ω) x = evA x ω) ∧
      xtB1 (guRS.giX _ h1 h2 h3) = iota S (gcG (evA Om1 ω) * ω) ∧
      Pv S (gcG (evA Om1 ω) * ω) < Nc.ncL S 0 := by
  have hωB : ω < guB := omega_lt_Om1.trans (lt_evZ Om1)
  have hω1 : (1 : Ordinal.{0}) ≤ ω := one_lt_omega0.le
  have hωE : ω < gfE := omega_lt_Om1.trans Om1_lt_eW
  have h1 : gfE ≤ evA Om1 ω := by rw [← gu_evA_one]; exact evA_le_iff.2 hω1
  have h2 : evA Om1 ω < guB := gu_evA_lt hωB
  have h3 : guG (evA Om1 ω) < ε₀ := by
    rw [guG_base hω1 hωB]
    unfold guQ
    rw [if_neg (lt_irrefl ω), guG_low hωE, (rdc_const omega_lt_Om1 0).2]
    exact omega0_lt_epsilon 0
  obtain ⟨l1, -, l3⟩ := gu_loc h1 h2 h3 S
  refine ⟨h1, h2, h3, fun x hx => ?_, l1, l3⟩
  rw [guR_base hω1 hωB, guR_low hωE, (rdc_const omega_lt_Om1 x).1, guA_eq hx hω1]

/-- **`sup = ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})`, `υ` of it `= P(Γ_{Ω₁+1+ζ_{Ω₁+1}}) < L(0)`.** -/
theorem guW_sup (S : InaccSeq.{0}) : (guRS.giFam S).famSup = iota S (gcG guB) ∧
    upsilon (guRS.giFam S).famSup = Pv S (gcG guB) ∧ Pv S (gcG guB) < Nc.ncL S 0 := guRS.giFam_sup S

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})} = P(Γ_{Ω₁+1+ζ_{Ω₁+1}})`**, with the exact reaches (the generic
`GiRS.giFam_blk` at `guRS`). -/
theorem guFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (guRS.giFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (guRS.giFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (guRS.giFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (guRS.giFam S).off k l)) ∧
    (∀ α < upsilon (guRS.giFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := guRS.giFam_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})`, fixed points included.** -/
theorem guFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG guB)) :
    CdUpper S l ∧ CdLower S l := guRS.giFam_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})`.** -/
theorem guFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG guB)) :
    CdCapV S l := guRS.giFam_capV S hr hl

/-- **THE ROAD past every code below `ζ_{Ω₁+1}`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+ζ_{Ω₁+1}})`
(CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the
reaches. -/
theorem guFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG guB) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG guB) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG guB) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  guRS.giFam_road S hU hL hV hC hEQ hrest hB2

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+ζ_{Ω₁+1}}) < ι(Ω₂)` for every code `c < ζ_{Ω₁+1}`
with gate below `ε₀`, and `P(Γ_{Ω₁+1+ζ_{Ω₁+1}}) < P(Ω₂) < L(0)`. -/
theorem gu_fr_order {c : Ordinal.{0}} (hc : c < guB) (hg : guG c < ε₀) (S : InaccSeq.{0}) :
    iota S (gcG c * ω) < iota S (gcG guB) ∧ iota S (gcG guB) < iota S (Om (1 + 1)) ∧
      Pv S (gcG guB) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 :=
  guRS.gi_fr_order hc hg S

end Googology.Trans.PoR.InaccPsi.R2.Gk
