import Googology.Trans.PoR.InaccPsi.R2.GoOps

/-!
# THE STEP ITERATED: digit systems at the bases `ε_{Γ+α}`, `α < ω^{ω^ω}`; the frontier `ι(Γ_{ε_{Γ+ω^{ω^ω}}})`

`G = Γ_{Ω₁+1}`.  The first digit system is `goGl` (codes below `G`, `R2.GoGl`).  The generic step `stepOp`
(`R2.GoStep`, `R2.GoOps`) and the generic limits (`GoOp.U`, `GoOpSeq.diag`) give:

* `goIt n = stepOp^n(goGl)`: the hereditary codes at the bases `G, ε_{G+1}, …, ε_{G+n-1}` (bound `ε_{G+n}`;
  `goIt 1` is the system of `R2.Gn`, `goIt 2` the one at the base `ε_{G+1}` where round 85 stopped);
* `GoFn` (a uniform way to add `ω^j` to the exponent of an operation), `goFn n` (`j = n`, by `GoFn.up`),
  `goOpW` (**the diagonal of `goFn n` applied to the step: exponent `ω^ω`**), `goTop = goOpW(goGl)` (**bound
  `ε_{G+ω^{ω^ω}} = φ(1, G + ω^{ω^ω})`**);
* `goTop_ext_It` (**`goTop` extends every `goIt n`**: same readings and gates);
* `goTop_sup` (**`sup = ι(Γ_{ε_{G+ω^{ω^ω}}})`, `P(⋯) < L(0)`**), `goTop_blk`, `goTop_enum`, `goTop_capV`, `goTop_road`,
  `goTop_fr_order`, `goTop_loc_E1w` (**the code `ε_{G+1}·ω`, where round 85 stopped, located**).

No new axiom.  New definitions: `goIt`, `GoOp.useq`, `GoFn`, `GoFn.seq`, `GoFn.up`, `goFn`, `goFnSeq`, `goOpW`,
`goTop`.
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

/-! ## Extension is transitive -/

theorem goExt_trans {O1 O2 O3 : GoOp} (h12 : GoExt O1 O2) (h23 : GoExt O2 O3) : GoExt O1 O3 := by
  intro D
  obtain ⟨b1, r1, g1, c1⟩ := h12 D
  obtain ⟨b2, r2, g2, c2⟩ := h23 D
  refine ⟨b1.trans b2, fun c x hc => by rw [r2 c x (hc.trans b1), r1 c x hc], fun c hc => by
    rw [g2 c (hc.trans b1), g1 c hc], ?_⟩
  rw [g2 _ b1]; exact c1

/-! ## The iterates of the step -/

/-- **`goIt n = stepOp^n(goGl)`**: the hereditary codes below `ε_{G+n}` (bound `φ(1, G + n)`). -/
noncomputable def goIt (n : ℕ) : GoD := stepOp.F^[n] goGl

theorem goIt_succ (n : ℕ) : goIt (n + 1) = (goIt n).step := by
  unfold goIt; rw [Function.iterate_succ_apply']; rfl

theorem goIt_B (n : ℕ) : (goIt n).B = veblen 1 (gcG 0 + n) := by
  rw [(goIt n).B_ix]
  unfold goIt
  rw [stepOp.it_ix goGl n]
  show veblen 1 (gcG 0 + ω ^ (0 : Ordinal.{0}) * n) = _
  rw [opow_zero, one_mul]

/-- `goIt 1` reads like `R2.Gn` (`gnR`) and `goIt 2` is the system at the base `ε_{G+1}`. -/
theorem goIt_one_B : (goIt 1).B = eN (gcG 0) := by rw [goIt_succ]; rfl

/-! ## Adding `ω^j` to the exponent of an operation -/

/-- The iterates `U^k(O)`. -/
noncomputable def GoOp.useq (O : GoOp) (k : ℕ) : GoOp := GoOp.U^[k] O

/-- **A uniform way to add `ω^j` to the exponent** of every operation, extending. -/
structure GoFn where
  Φ : GoOp → GoOp
  j : Ordinal.{0}
  j_lt : j < ε₀
  j_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → j ∈ S.CSet a b
  ej : ∀ O, (Φ O).e = O.e + ω ^ j
  ext : ∀ O, GoExt O (Φ O)

namespace GoFn

variable (Φ : GoFn)

theorem it_e (O : GoOp) : ∀ k : ℕ, (Φ.Φ^[k] O).e = O.e + ω ^ Φ.j * k
  | 0 => by rw [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, add_zero]
  | k + 1 => by rw [Function.iterate_succ_apply', Φ.ej, it_e O k, Nat.cast_succ, mul_add_one, add_assoc]

/-- The sequence `Φ^k(O)`. -/
noncomputable def seq (O : GoOp) : GoOpSeq where
  O := fun k => Φ.Φ^[k] O
  einf := O.e + ω ^ (Φ.j + 1)
  ext := fun k => by rw [Function.iterate_succ_apply']; exact Φ.ext _
  e_mono := fun k => by
    rw [Φ.it_e, Φ.it_e]
    exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2
      (by exact_mod_cast Nat.lt_succ_self k))
  e_lt := fun k => by
    rw [Φ.it_e]; exact (add_lt_add_iff_left _).2 (omega0_opow_mul_nat_lt (lt_add_one _) k)
  e_cof := fun t ht => by
    refine go_lt_add_sup (δ := fun k => ω ^ Φ.j * k) (opow_ne_zero _ omega0_ne_zero) (fun t' ht' => ?_) ht
      |>.imp fun k hk => by rw [Φ.it_e]; exact hk
    obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow (by simp)).1 ht'
    exact ⟨n, hn.trans_le (mul_le_mul_right' (opow_le_opow_right omega0_pos (Order.lt_add_one_iff.1 hc)) _)⟩
  einf_lt := (inE_indec go_eps0_E).add_lt O.e_lt (go_opow_lt_eps0 (go_eps0_lim.add_one_lt Φ.j_lt))
  einf_mem := fun S a b ha => CSet.add_mem (O.e_mem S a b ha) (go_opow_mem (CSet.succ_mem (Φ.j_mem S a b ha)))

/-- **`Φ ↦ Φ^ω`**: adds `ω^{j+1}`. -/
noncomputable def up : GoFn where
  Φ := fun O => (Φ.seq O).diag
  j := Φ.j + 1
  j_lt := go_eps0_lim.add_one_lt Φ.j_lt
  j_mem := fun S a b ha => CSet.succ_mem (Φ.j_mem S a b ha)
  ej := fun _ => rfl
  ext := fun O => by
    have h := (Φ.seq O).ext_diag 0
    exact h

end GoFn

/-- `U` adds `ω^0 = 1`. -/
noncomputable def goFnU : GoFn where
  Φ := GoOp.U
  j := 0
  j_lt := epsilon_pos 0
  j_mem := fun _ _ _ _ => CSet.zero_mem _ _
  ej := fun O => by rw [opow_zero]; rfl
  ext := GoOp.ext_U

/-- **`goFn n` adds `ω^n`.** -/
noncomputable def goFn : ℕ → GoFn
  | 0 => goFnU
  | n + 1 => (goFn n).up

theorem goFn_j : ∀ n : ℕ, (goFn n).j = n
  | 0 => rfl
  | n + 1 => by
    show (goFn n).j + 1 = ((n + 1 : ℕ) : Ordinal.{0})
    rw [goFn_j n, Nat.cast_succ]

/-- The sequence `goFn n (step)`, exponents `ω^n`. -/
noncomputable def goFnSeq : GoOpSeq where
  O := fun n => (goFn n).Φ stepOp
  einf := ω ^ ω
  ext := fun n => by
    show GoExt ((goFn n).Φ stepOp) ((goFn n).up.Φ stepOp)
    have h := ((goFn n).seq stepOp).ext_diag 1
    simp only [GoFn.seq, Function.iterate_one] at h
    exact h
  e_mono := fun n => by
    show ((goFn n).Φ stepOp).e < ((goFn (n + 1)).Φ stepOp).e
    rw [(goFn n).ej, (goFn (n + 1)).ej, goFn_j, goFn_j]
    exact (add_lt_add_iff_left _).2 ((opow_lt_opow_iff_right one_lt_omega0).2 (by exact_mod_cast Nat.lt_succ_self n))
  e_lt := fun n => by
    show ((goFn n).Φ stepOp).e < ω ^ ω
    rw [(goFn n).ej, goFn_j]
    show 0 + ω ^ (n : Ordinal.{0}) < ω ^ ω
    rw [zero_add]; exact (opow_lt_opow_iff_right one_lt_omega0).2 (natCast_lt_omega0 n)
  e_cof := fun t ht => by
    obtain ⟨c, hc, n, hn⟩ := (lt_omega0_opow omega0_ne_zero).1 ht
    obtain ⟨m, rfl⟩ := lt_omega0.1 hc
    refine ⟨m + 1, ?_⟩
    show t < ((goFn (m + 1)).Φ stepOp).e
    rw [(goFn (m + 1)).ej, goFn_j]
    show t < 0 + ω ^ ((m + 1 : ℕ) : Ordinal.{0})
    rw [zero_add]
    exact hn.trans (omega0_opow_mul_nat_lt (by exact_mod_cast Nat.lt_succ_self m) n)
  einf_lt := go_opow_lt_eps0 (omega0_lt_epsilon 0)
  einf_mem := fun S a b _ => by
    have h1 : (1 : Ordinal.{0}) ∈ S.CSet a b := CSet.one_mem _ _
    have hω := go_opow_mem h1
    rw [opow_one] at hω
    exact go_opow_mem hω

/-- **THE OPERATION WITH EXPONENT `ω^ω`**: the diagonal of `goFn n (step)`. -/
noncomputable def goOpW : GoOp := goFnSeq.diag

theorem goOpW_e : goOpW.e = ω ^ ω := rfl

/-- **THE DIGIT SYSTEM BELOW `ε_{G+ω^{ω^ω}}`**: `goOpW(goGl)`. -/
noncomputable def goTop : GoD := goOpW.F goGl

theorem goTop_B : goTop.B = veblen 1 (gcG 0 + ω ^ ω ^ ω) := by
  unfold goTop; rw [goOpW.F_B]; rfl

/-! ## `goTop` extends every `goIt n` -/

theorem goU_ext_It (n : ℕ) : (∀ c x, c < (goIt n).B → (stepOp.U.F goGl).R c x = (goIt n).R c x) ∧
    (∀ c, c < (goIt n).B → (stepOp.U.F goGl).g c = (goIt n).g c) := by
  refine ⟨fun c x hc => ?_, fun c hc => ?_⟩
  · exact (stepOp.seq goGl).toCh.lim_R (n := n) hc x
  · exact (stepOp.seq goGl).toCh.lim_g (n := n) hc

theorem goTop_ext_U : GoExt stepOp.U goOpW := by
  have h := goFnSeq.ext_diag 0
  exact h

/-- **`goTop` extends every `goIt n`** (same readings and gates below `ε_{G+n}`). -/
theorem goTop_ext_It (n : ℕ) : (∀ c x, c < (goIt n).B → goTop.R c x = (goIt n).R c x) ∧
    (∀ c, c < (goIt n).B → goTop.g c = (goIt n).g c) := by
  obtain ⟨hb, hr, hg, -⟩ := goTop_ext_U goGl
  obtain ⟨r2, g2⟩ := goU_ext_It n
  have hlt : (goIt n).B < (stepOp.U.F goGl).B := (stepOp.seq goGl).toCh.B_lt n
  exact ⟨fun c x hc => by rw [show goTop = goOpW.F goGl from rfl, hr c x (hc.trans hlt), r2 c x hc],
    fun c hc => by rw [show goTop = goOpW.F goGl from rfl, hg c (hc.trans hlt), g2 c hc]⟩

/-! ## The frontier and the road -/

/-- **`sup = ι(Γ_{Ω₁+1+ε_{G+ω^{ω^ω}}}) = ι(Γ_{ε_{G+ω^{ω^ω}}})`, `υ` of it `= P(⋯) < L(0)`.** -/
theorem goTop_sup (S : InaccSeq.{0}) : (goTop.toRS.gmFam S).famSup = iota S (gcG goTop.B) ∧
    upsilon (goTop.toRS.gmFam S).famSup = Pv S (gcG goTop.B) ∧ Pv S (gcG goTop.B) < Nc.ncL S 0 :=
  goTop.go_sup S

/-- **Theorem BLK^O below `P(Γ_{ε_{G+ω^{ω^ω}}})`**, with the exact reaches. -/
theorem goTop_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (goTop.toRS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (goTop.toRS.gmFam S).famSup ∧
        c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (goTop.toRS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (goTop.toRS.gmFam S).off k l)) ∧
    (∀ α < upsilon (goTop.toRS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  goTop.go_blk S

/-- **ENUM-REACH at every range restart below `ι(Γ_{ε_{G+ω^{ω^ω}}})`, fixed points included.** -/
theorem goTop_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG goTop.B)) :
    CdUpper S l ∧ CdLower S l := goTop.go_enum S hr hl

/-- **CapV at every range restart below `ι(Γ_{ε_{G+ω^{ω^ω}}})`.** -/
theorem goTop_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG goTop.B)) :
    CdCapV S l := goTop.go_capV S hr hl

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{ε_{G+ω^{ω^ω}}})`. -/
theorem goTop_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG goTop.B) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG goTop.B) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG goTop.B) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  goTop.go_road S hU hL hV hC hEQ hrest hB2

/-! ## The code `ε_{G+1}·ω` (where round 85 stopped) -/

theorem go_E1_eq : (goIt 1).B = gnB := goIt_one_B

theorem go_E1w_lt : gnB * ω < (goIt 2).B := by
  rw [goIt_succ, GoD.step_B, ← go_E1_eq]
  exact InE.mul_lt (eN_E _) (lt_eN _) (omega0_lt_inE (eN_E _))

theorem go_E1w_g : (goIt 2).g (gnB * ω) = ω := by
  rw [goIt_succ, GoD.step_g, ← go_E1_eq]
  have e : (goIt 1).B * ω = (goIt 1).B ^ (1 : Ordinal.{0}) * ω + 0 := by rw [opow_one, add_zero]
  have hB : (goIt 1).B ^ (1 : Ordinal.{0}) * ω + 0 < (goIt 1).NB := by
    rw [← e]; exact InE.mul_lt (eN_E _) (lt_eN _) (omega0_lt_inE (eN_E _))
  rw [e, (goIt 1).hG_cnf one_ne_zero omega0_ne_zero (goIt 1).omega_lt_B (opow_pos _ (goIt 1).B_pos) hB,
    (goIt 1).hG_zero, max_eq_left zero_le, (goIt 1).Q_inf le_rfl]
  have h1 : (goIt 1).hQ 1 = 0 := by exact_mod_cast (goIt 1).hQ_nat 1
  rw [h1, max_eq_right zero_le, goIt_succ, GoD.step_g]
  show goGl.hG ω = ω
  rw [goGl.hG_low (omega_lt_Om1.trans gl_Om1_lt_G0)]
  show glG ω = ω
  rw [glG_low (omega_lt_Om1.trans Om1_lt_eW), (rdc_const omega_lt_Om1 0).2]

theorem goTop_E1w_lt : gnB * ω < goTop.B := by
  have h := (goTop_ext_U goGl).1
  exact go_E1w_lt.trans (((stepOp.seq goGl).toCh.B_lt 2).trans h)

theorem goTop_E1w_g : goTop.g (gnB * ω) < ε₀ := by
  rw [(goTop_ext_It 2).2 _ go_E1w_lt, go_E1w_g]; exact omega0_lt_epsilon 0

theorem go_E1w_ge : gfE ≤ gnB * ω :=
  (gfE_lt_G0.trans gn_G0_lt_B).le.trans (le_mul_of_one_le_right' one_lt_omega0.le)

/-- **THE CODE `ε_{G+1}·ω` LOCATED** (round 85 stopped there): its layer has gate `ω`, top
`Γ_{x+1+ε_{Γ_{x+1}+1}·ω}`, `Λ⁺ = ι(Γ_{Ω₁+1+ε_{G+1}·ω}·ω)`, `P(⋯) < L(0)`. -/
theorem goTop_loc_E1w (S : InaccSeq.{0}) :
    xtB1 (goTop.toRS.gmX (gnB * ω) go_E1w_ge goTop_E1w_lt goTop_E1w_g) = iota S (gcG (gnB * ω) * ω) ∧
    Pv S (gcG (gnB * ω) * ω) < Nc.ncL S 0 :=
  let h := goTop.go_loc go_E1w_ge goTop_E1w_lt goTop_E1w_g S
  ⟨h.1, h.2.2⟩

/-- **The order of the frontiers**: `ι(Γ_{ε_{G+1}}) < ι(Γ_{Ω₁+1+ε_{G+1}·ω}·ω) < ι(Γ_{ε_{G+ω^{ω^ω}}}) < ι(Ω₂)`,
`P(Γ_{ε_{G+ω^{ω^ω}}}) < P(Ω₂) < L(0)`. -/
theorem goTop_fr_order (S : InaccSeq.{0}) :
    iota S (gcG (gnB * ω) * ω) < iota S (gcG goTop.B) ∧ iota S (gcG goTop.B) < iota S (Om (1 + 1)) ∧
      Pv S (gcG goTop.B) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 :=
  goTop.go_fr_order goTop_E1w_lt goTop_E1w_g S

end Googology.Trans.PoR.InaccPsi.R2.Go
