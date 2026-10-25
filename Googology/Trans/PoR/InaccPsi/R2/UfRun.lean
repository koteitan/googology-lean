import Googology.Trans.PoR.InaccPsi.R2.UfW
import Googology.Trans.PoR.InaccPsi.R2.TwHull

/-!
# The runs of an atom `H_γ(y)` below `B₂`: its own argument `B + Ω₂^γ·D`

`ψ = ψ_{Ω₂} = S.psi · Ω₂`, `H_γ = Uc.ucH γ` (`γ < E₂ = ε_{Ω₂+1}`), `B₂ = Uc.ucB = ψ(E₂)`, `UcCl Z` the codes over `Z`
with the atoms `H_γ(y)` (`R2.UcCl`).  An argument `B` is *own* when `B ∈ Cl(B, ψ(B))`.

* `uf_cl_lt_B` (**codes over `Z ≤ Ω₁` are below `B₂`**), `uf_SC_code` (a strongly critical point below a code lies
  below a strongly critical code), `uf_fix_code` (**a fixed point `q > Ω₁` of `H_γ` below a code `y` lies below a fixed
  point `p ≤ y` of `H_γ` that is a code**);
* `uf_last`, `uf_dvd_of_range` (**an own `V < E₂` whose collapse is fixed by every `H_j`, `j < γ`, `ucC j < ψ(V)`, is
  divisible by `Ω₂^γ`**), `uf_H0` (`H_0(0) = ψ(0)`);
* `uf_least` (**the first value**: for `1 ≤ γ < E₂`, an own `K < E₂` with `ψ(K) ≤ m` or `K = 0`, `m < ψ(K + 1)`,
  `ucC γ ≤ m`: `ψ(K + Ω₂^γ)` is the least value of `H_γ` above `m`, and `K + Ω₂^γ` is own);
* `uf_valid` (validity from `D < ψ(B + Ω₂^γ·D)`), `ufRun_eq` (**`ψ(B + Ω₂^γ·D) = H_γ(c + D)`, `B + Ω₂^γ·D` own**),
  `ufRun` (**the run of an atom**: `y = c + D` with `H_γ(c) = ψ(B)`, `B` own, `Ω₂^γ ∣ B`, `D` valid, `c`, `D` codes;
  `c = 0`, or `c > Ω₁` is the largest fixed point of `H_γ` in `(Ω₁, y]` and `Ω₂^{γ+1} ∣ B`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

theorem uf_Om1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1

theorem uf_H_le_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : ucH γ a ≤ ucH γ b ↔ a ≤ b :=
  ucG_le_iff (d := ucC) (L := Om1) γ

/-! ## Codes below `B₂` -/

/-- **Codes over `Z ≤ Ω₁` are below `B₂`.** -/
theorem uf_cl_lt_B {Z : Ordinal.{0}} (hZ : Z ≤ Om1) {x : Ordinal.{0}} (hx : UcCl Z x) : x < ucB := by
  induction hx with
  | small h => exact (h.trans_le hZ).trans ucB_gt
  | om => exact ucB_gt
  | add _ _ ihx ihy => exact uc_B_indec.add_lt ihx ihy
  | phi _ _ ihx ihy => exact ucB_SC.2 _ ihx _ ihy
  | tl h => exact (uc_tl_lt_X hZ h).trans uc_X_lt_B
  | @hatom γ y hγ _ _ _ ihc ihy =>
    have hc : ucC γ < ucB := (ucC_lt_iff ucB_SC.1 γ).2 ihc
    have := (ucH_lt_iff γ).2 ihy
    rwa [ucB_spec hγ hc] at this

theorem uf_cl_lt_Om2 {Z : Ordinal.{0}} (hZ : Z ≤ Om1) {x : Ordinal.{0}} (hx : UcCl Z x) : x < OmTwo :=
  (uf_cl_lt_B hZ hx).trans ucB_lt_Om2

/-- A strongly critical `s > Ω₁` below a code `y` lies below a strongly critical code `t ≤ y`. -/
theorem uf_SC_code {Z : Ordinal.{0}} (hZ : Z ≤ Om1) :
    ∀ y, UcCl Z y → ∀ s, SC s → Om1 < s → s ≤ y → ∃ t, UcCl Z t ∧ SC t ∧ s ≤ t ∧ t ≤ y := by
  intro y hy
  induction hy with
  | small h => exact fun s _ hs hsy => absurd ((hsy.trans_lt h).trans_le hZ) (not_lt.2 hs.le)
  | om => exact fun s _ hs hsy => absurd hs (not_lt.2 hsy)
  | @add x y _ _ ihx ihy =>
    intro s hS hs hsy
    by_cases hxs : s ≤ x
    · obtain ⟨t, a, b, c, d⟩ := ihx s hS hs hxs; exact ⟨t, a, b, c, d.trans le_self_add⟩
    by_cases hys : s ≤ y
    · obtain ⟨t, a, b, c, d⟩ := ihy s hS hs hys; exact ⟨t, a, b, c, d.trans le_add_self⟩
    exact absurd (tl_SC_prin hS (not_le.1 hxs) (not_le.1 hys)) (not_lt.2 hsy)
  | @phi x y _ _ ihx ihy =>
    intro s hS hs hsy
    by_cases hxs : s ≤ x
    · obtain ⟨t, a, b, c, d⟩ := ihx s hS hs hxs; exact ⟨t, a, b, c, d.trans (left_le_veblen x y)⟩
    by_cases hys : s ≤ y
    · obtain ⟨t, a, b, c, d⟩ := ihy s hS hs hys; exact ⟨t, a, b, c, d.trans (right_le_veblen x y)⟩
    exact absurd (hS.2 _ (not_le.1 hxs) _ (not_le.1 hys)) (not_lt.2 hsy)
  | @tl x hx =>
    intro s hS hs hsy
    obtain ⟨t, a, b, c, d⟩ := Tw.tw_SC_code hZ x hx s hS hs hsy
    exact ⟨t, UcCl.tl a, b, c, d⟩
  | @hatom γ y hγ hc hy hX _ _ =>
    exact fun s _ _ hsy => ⟨_, UcCl.hatom hγ hc hy hX, ucH_SC γ y, hsy, le_rfl⟩

/-- A fixed point of `H_γ` (`γ ≥ Ω₂`) is `≥ X`. -/
theorem uf_fix_ge_X {γ q : Ordinal.{0}} (hγ2 : OmTwo ≤ γ) (hq : ucH γ q = q) : tlX ≤ q := by
  have hr : q ∈ range (ucH γ) := ⟨q, hq⟩
  rcases hγ2.lt_or_eq with hlt | heq
  · have h1 : ucC OmTwo < q := by rw [ucC_Om2]; exact Tf.tf_one_lt_Om1.trans (ucH_gt γ q |>.trans_eq hq)
    have hf : ucH OmTwo q = q := ucG_fix_lower hlt hr h1
    exact uc_X_le_H ⟨q, hf⟩
  · subst heq; exact uc_X_le_H hr

/-- **A fixed point `q > Ω₁` of `H_γ` below a code `y` lies below a fixed point `p ≤ y` of `H_γ` that is a code.** -/
theorem uf_fix_code {Z : Ordinal.{0}} (hZ : Z ≤ Om1) {γ : Ordinal.{0}} (hγ : γ < ucE) :
    ∀ y, UcCl Z y → ∀ q, ucH γ q = q → Om1 < q → q ≤ y →
      ∃ p, UcCl Z p ∧ ucH γ p = p ∧ q ≤ p ∧ p ≤ y := by
  intro y hy
  induction hy with
  | small h => exact fun q _ hq hqy => absurd ((hqy.trans_lt h).trans_le hZ) (not_lt.2 hq.le)
  | om => exact fun q _ hq hqy => absurd hq (not_lt.2 hqy)
  | @add x y _ _ ihx ihy =>
    intro q hfix hq hqy
    have hqS : SC q := by rw [← hfix]; exact ucH_SC γ q
    by_cases hxq : q ≤ x
    · obtain ⟨p, a, b, c, d⟩ := ihx q hfix hq hxq; exact ⟨p, a, b, c, d.trans le_self_add⟩
    by_cases hyq : q ≤ y
    · obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hyq; exact ⟨p, a, b, c, d.trans le_add_self⟩
    exact absurd (tl_SC_prin hqS (not_le.1 hxq) (not_le.1 hyq)) (not_lt.2 hqy)
  | @phi x y _ _ ihx ihy =>
    intro q hfix hq hqy
    have hqS : SC q := by rw [← hfix]; exact ucH_SC γ q
    by_cases hxq : q ≤ x
    · obtain ⟨p, a, b, c, d⟩ := ihx q hfix hq hxq; exact ⟨p, a, b, c, d.trans (left_le_veblen x y)⟩
    by_cases hyq : q ≤ y
    · obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hyq; exact ⟨p, a, b, c, d.trans (right_le_veblen x y)⟩
    exact absurd (hqS.2 _ (not_le.1 hxq) _ (not_le.1 hyq)) (not_lt.2 hqy)
  | @tl x hx =>
    intro q hfix hq hqx
    have hxX := uc_tl_lt_X hZ hx
    have hCq : ucC γ < q := by rw [← hfix]; exact ucH_C_lt γ q
    rcases lt_or_ge γ OmTwo with hγ2 | hγ2
    · rw [ucC_small hγ2] at hCq
      have hF : rhF γ q = q := (ucH_fix_iff_F hγ2 (max_lt hq hCq)).1 hfix
      obtain ⟨p, a, b, c, d⟩ := Tw.tw_fix_code hZ γ x hx q hF hq hqx
      exact ⟨p, UcCl.tl a, (ucH_fix_iff_F hγ2 (max_lt (hq.trans_le c) (hCq.trans_le c))).2 b, c, d⟩
    · exact absurd ((uf_fix_ge_X hγ2 hfix).trans hqx) (not_le.2 hxX)
  | @hatom γ' y' hγ' hc hy' hX ihc ihy =>
    intro q hfix hq hqz
    have hA : UcCl Z (ucH γ' y') := UcCl.hatom hγ' hc hy' hX
    by_cases hF : ucH γ (ucH γ' y') = ucH γ' y'
    · exact ⟨_, hA, hF, hqz, le_rfl⟩
    have hCq : ucC γ < q := by rw [← hfix]; exact ucH_C_lt γ q
    rcases eq_or_lt_of_le (ucH_le_self γ' y') with heq | hyz
    · rw [← heq] at hqz ⊢
      obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hqz
      exact ⟨p, a, b, c, d⟩
    obtain ⟨hl, -⟩ := ucLev_H hγ' hyz
    have hmem : γ ∈ ucLevSet (ucH γ' y') := ⟨hγ, hCq.trans_le hqz, hF⟩
    have hγ'γ : γ' ≤ γ := by rw [← hl]; exact csInf_le' hmem
    by_cases hbig : ∃ c ∈ ucComps γ', q ≤ c
    · obtain ⟨c, hcm, hqc⟩ := hbig
      obtain ⟨p, a, b, d, e⟩ := ihc c hcm q hfix hq hqc
      exact ⟨p, a, b, d, e.trans ((le_ucC hcm).trans (ucH_C_lt γ' y').le)⟩
    push Not at hbig
    have hC' : ucC γ' < q := (ucC_lt_iff (zero_le.trans_lt hq) γ').2 hbig
    have hq' : ucH γ' q = q := ucG_fix_mono hγ'γ hfix hC'
    have hqlt : q < ucH γ' y' := lt_of_le_of_ne hqz fun e => hF (by rw [← e]; exact hfix)
    have hqy : q < y' := by rw [← hq'] at hqlt; exact (ucH_lt_iff γ').1 hqlt
    obtain ⟨p, a, b, c, d⟩ := ihy q hfix hq hqy.le
    exact ⟨p, a, b, c, d.trans (ucH_le_self γ' y')⟩

/-! ## Divisibility from the range -/

/-- `ψ(e) < ψ(e')` for own `e`, `e'` gives `e < e'`. -/
theorem uf_own_lt {e e' : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (1 + 1))))
    (hown' : e' ∈ S.CSet e' (S.psi e' (Om (1 + 1)))) (h : S.psi e (Om (1 + 1)) < S.psi e' (Om (1 + 1))) :
    e < e' := by
  have hc := compare_psi (InR_Om_succ 1) hown hown'
  rw [compare_lt_iff_lt.2 h] at hc
  exact compare_lt_iff_lt.1 hc.symm

/-- An own `e` with `ψ(e) < B₂` is below `E₂`. -/
theorem uf_own_lt_E {e : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (1 + 1))))
    (h : S.psi e (Om (1 + 1)) < ucB) : e < ucE := by
  rw [← uc_psiE_eq_B (S := S)] at h
  exact uf_own_lt hown (uc_E_mem _ _) h

/-- **The last exponent**: a nonzero `V < E₂` with every component below `q` has a `k < E₂`, every component below
`q`, with `Ω₂^k ∣ V` and not `Ω₂^{k+1} ∣ V`. -/
theorem uf_last {q : Ordinal.{0}} (hq : 0 < q) : ∀ V, V < ucE → V ≠ 0 → UcLt q V →
    ∃ k, k < ucE ∧ OmTwo ^ k ∣ V ∧ ¬ OmTwo ^ (k + 1) ∣ V ∧ UcLt q k := by
  intro V
  induction V using WellFoundedLT.induction with
  | ind V IH =>
  intro hVE hV0 hVq
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  by_cases h1 : V < OmTwo
  · refine ⟨0, h0E, by rw [opow_zero]; exact one_dvd _, fun hd => ?_, ucLt_zero hq⟩
    rw [zero_add, opow_one] at hd
    exact absurd (Ordinal.le_of_dvd hV0 hd) (not_le.2 h1)
  have hγ2 : OmTwo ≤ V := not_lt.1 h1
  set e := log OmTwo V with he
  set d := V / OmTwo ^ e with hd
  set r := V % OmTwo ^ e with hr
  have hel : e < V := uc_log_lt hγ2 hVE
  have hrl : r < V := uc_mod_lt hγ2
  have hd2 : d < OmTwo := uc_div_lt V
  have hd0 : 0 < d := uc_div_pos hγ2
  have hrW : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have he1 : 1 ≤ e := by
    by_contra h0
    rw [not_le, Order.lt_one_iff] at h0
    have : V < OmTwo := by
      calc V < OmTwo ^ (log OmTwo V + 1) := lt_opow_succ_log_self uc_one_lt_Om2 V
        _ = OmTwo := by rw [← he, h0, zero_add, opow_one]
    exact h1 this
  have hdec : OmTwo ^ e * d + r = V := uc_cnf_eq V
  have hcnf := ucLt_cnf (q := q) he1 hd0.ne' hd2 hrW (by rw [hdec]; exact hVE)
  rw [hdec] at hcnf
  obtain ⟨hqe, -, hqr⟩ := hcnf.1 hVq
  rcases eq_or_ne r 0 with hr0 | hr0
  · refine ⟨e, hel.trans hVE, ?_, fun hdv => ?_, hqe⟩
    · rw [← hdec, hr0, add_zero]; exact dvd_mul_right _ _
    · have hpos : V ≠ 0 := hV0
      have hle := Ordinal.le_of_dvd hpos hdv
      have hlt : V < OmTwo ^ (e + 1) := by
        rw [← hdec, hr0, add_zero, uc_W_succ]
        exact (mul_lt_mul_iff_right₀ (uc_W_pos e)).2 hd2
      exact absurd hlt (not_lt.2 hle)
  obtain ⟨k, hkE, hk1, hk2, hkq⟩ := IH r hrl (hrl.trans hVE) hr0 hqr
  have hke : k < e := by
    by_contra hc
    push Not at hc
    have h1' := Ordinal.le_of_dvd hr0 hk1
    exact absurd ((opow_le_opow_right uc_SC_Om2.1 hc).trans h1') (not_le.2 hrW)
  have hk1e : OmTwo ^ (k + 1) ∣ OmTwo ^ e * d :=
    (opow_dvd_opow _ (Order.add_one_le_of_lt hke)).trans (dvd_mul_right _ _)
  have hke' : OmTwo ^ k ∣ OmTwo ^ e * d :=
    (opow_dvd_opow _ (le_self_add.trans (Order.add_one_le_of_lt hke))).trans (dvd_mul_right _ _)
  refine ⟨k, hkE, ?_, fun hdv => ?_, hkq⟩
  · rw [← hdec]; exact dvd_add hke' hk1
  · rw [← hdec] at hdv; exact hk2 ((Ordinal.dvd_add_iff hk1e).1 hdv)

/-- **Divisibility from the range**: an own `V < E₂` whose collapse is fixed by every `H_j`, `j < γ`, with
`ucC j < ψ(V)`, is divisible by `Ω₂^γ`. -/
theorem uf_dvd_of_range {γ V : Ordinal.{0}} (hown : V ∈ S.CSet V (S.psi V (Om (1 + 1)))) (hVE : V < ucE)
    (hfix : ∀ j < γ, ucC j < S.psi V (Om (1 + 1)) → ucH j (S.psi V (Om (1 + 1))) = S.psi V (Om (1 + 1))) :
    OmTwo ^ γ ∣ V := by
  rcases eq_or_ne V 0 with rfl | hV0
  · exact dvd_zero _
  by_contra hnd
  have hq : 0 < S.psi V (Om (1 + 1)) := (Ts.ts_psi_SC V).1
  obtain ⟨k, hkE, hk1, hk2, hkq⟩ := uf_last hq V hVE hV0 (uc_own_comps hown hVE)
  have hkγ : k < γ := by
    by_contra hc
    push Not at hc
    exact hnd ((opow_dvd_opow _ hc).trans hk1)
  have hCk : ucC k < S.psi V (Om (1 + 1)) := (ucC_lt_iff hq k).2 hkq
  exact hk2 ((uc_fwd_conv (S := S) k hkE).2 V hown hVE (hfix k hkγ hCk))

/-- **`H_0(0) = ψ(0)`.** -/
theorem uf_H0 : ucH 0 0 = S.psi 0 (Om (1 + 1)) := by
  have hψ : S.psi 0 (Om (1 + 1)) = gamma (Om1 + 1) := by rw [Tf.tf_psi S 0 zero_le, add_zero]
  apply le_antisymm
  · have hr : S.psi 0 (Om (1 + 1)) ∈ range (ucH 0) := by
      refine ucG_range (Ts.ts_psi_SC 0) (by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi 0) ?_ fun j hj => ?_
      · rw [ucC_small uc_SC_Om2.1]; exact (Ts.ts_psi_SC 0).1
      · exact absurd hj (not_lt.2 zero_le)
    obtain ⟨e, he⟩ := hr
    rw [← he]; exact (uf_H_le_iff 0).2 zero_le
  · rw [ucH_eq_F uc_SC_Om2.1, add_zero, rhF_zero, hψ]
    have hs := ucS_spec 0
    rw [rhF_zero, max_eq_left zero_le] at hs
    have hF0 : gamma (Om1 : Ordinal.{0}) = Om1 := by
      have := Tl.tl_rhF_Om1 (β := 0) Rj.rj_Om1_pos; rwa [rhF_zero] at this
    have hle : Om1 + 1 ≤ ucS 0 := by
      refine Order.add_one_le_of_lt (not_le.1 fun h => ?_)
      have := (gamma_le_gamma.2 h)
      rw [hF0] at this
      exact absurd hs (not_lt.2 this)
    exact gamma_le_gamma.2 hle

/-! ## The first value of `H_γ` above `m` -/

/-- **The first value of `H_γ` above `m`**: for `1 ≤ γ < E₂`, an own `K < E₂` with `ψ(K) ≤ m` or `K = 0`,
`m < ψ(K + 1)`, `ucC γ ≤ m`: `ψ(K + Ω₂^γ)` is a value of `H_γ` above `m`, below every value of `H_γ` above `m`;
`K + Ω₂^γ` is own and below `E₂`. -/
theorem uf_least {γ K m : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγE : γ < ucE)
    (hown : K ∈ S.CSet K (S.psi K (Om (1 + 1)))) (hKE : K < ucE)
    (hK : S.psi K (Om (1 + 1)) ≤ m ∨ K = 0) (hm1 : m < S.psi (K + 1) (Om (1 + 1))) (hcm : ucC γ ≤ m) :
    S.psi (K + OmTwo ^ γ) (Om (1 + 1)) ∈ range (ucH γ) ∧ m < S.psi (K + OmTwo ^ γ) (Om (1 + 1)) ∧
      (∀ v ∈ range (ucH γ), m < v → S.psi (K + OmTwo ^ γ) (Om (1 + 1)) ≤ v) ∧
      K + OmTwo ^ γ ∈ S.CSet (K + OmTwo ^ γ) (S.psi (K + OmTwo ^ γ) (Om (1 + 1))) ∧ K + OmTwo ^ γ < ucE := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  set u := OmTwo ^ γ with hudef
  set E := K + u with hEdef
  have hu0 : u ≠ 0 := (uc_W_pos γ).ne'
  have h1u : (1 : Ordinal.{0}) ≤ u := one_le_iff_ne_zero.2 hu0
  have hEE : E < ucE := uc_E_indec hKE (uc_W_lt_E hγE)
  have hmE : m < S.psi E (Om (1 + 1)) := hm1.trans_le (psi_mono (S := S) hκ (add_le_add_right h1u K)).1
  have hCE : ucC γ < S.psi E (Om (1 + 1)) := hcm.trans_lt hmE
  have hγv : UcLt (S.psi E (Om (1 + 1))) γ := (ucC_lt_iff (zero_le.trans_lt hCE) γ).1 hCE
  have hownE : E ∈ S.CSet E (S.psi E (Om (1 + 1))) := by
    have h1v : (1 : Ordinal.{0}) < S.psi E (Om (1 + 1)) := uc_one_lt_SC (Ts.ts_psi_SC E)
    have := uc_W_mem (S := S) (a := E) hγE hγv h1v
    rw [mul_one] at this
    exact CSet.add_mem ((psi_mono (S := S) hκ le_self_add).2 hown) this
  -- `E = T + u` with `u ∣ T`
  set T := u * (K / u) with hTdef
  have hTK : T ≤ K := Ordinal.mul_div_le K u
  have hET : E = T + u := by
    rw [hEdef, hTdef]
    calc K + u = u * (K / u) + (K % u + u) := by rw [← add_assoc, Ordinal.div_add_mod]
      _ = u * (K / u) + u := by
          have := Rd.rdk_absorb (uc_W_indec γ) (Ordinal.mod_lt K hu0) (le_refl (1 : Ordinal.{0}))
          rw [mul_one] at this; rw [this]
  have hTd : u ∣ T := dvd_mul_right _ _
  have hE0 : E ≠ 0 := (lt_of_lt_of_le (uc_W_pos γ) le_add_self).ne'
  have hfixE : ∀ j < γ, ucC j < S.psi E (Om (1 + 1)) →
      ucH j (S.psi E (Om (1 + 1))) = S.psi E (Om (1 + 1)) := fun j hj hd => by
    have hdv : OmTwo ^ (j + 1) ∣ E := by
      rw [hET]; exact (opow_dvd_opow _ (Order.add_one_le_of_lt hj)).trans (dvd_add hTd dvd_rfl)
    exact (uc_fwd_conv (S := S) j (hj.trans hγE)).1 E hownE hdv hE0 hd
  have hval : S.psi E (Om (1 + 1)) ∈ range (ucH γ) :=
    ucG_range (Ts.ts_psi_SC E) (by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi E) hCE hfixE
  have hnone : ∀ v, m < v → v < S.psi E (Om (1 + 1)) → v ∈ range (ucH γ) → False := by
    intro v hmv hvE hvR
    have hvSC : SC v := by obtain ⟨o, ho⟩ := hvR; rw [← ho]; exact ucH_SC γ o
    have hv1 : Om 1 < v := by obtain ⟨o, ho⟩ := hvR; rw [← ho, ← uf_Om1]; exact ucH_gt γ o
    have hEB : S.psi E (Om (1 + 1)) < ucB := by
      rw [← uc_psiE_eq_B (S := S)]; exact Ts.ts_psi_lt_of_own hownE hEE
    obtain ⟨V, hownV, hVE2, hV⟩ := uc_own_of_SC (S := S) hvSC hv1 (hvE.trans hEB)
    have hvF : ∀ j < γ, ucC j < S.psi V (Om (1 + 1)) →
        ucH j (S.psi V (Om (1 + 1))) = S.psi V (Om (1 + 1)) := fun j hj hd => by
      rw [hV] at hd ⊢; exact ucG_fix_lower hj hvR hd
    have hdvdV : u ∣ V := uf_dvd_of_range hownV hVE2 hvF
    have hVE : V < E := uf_own_lt hownV hownE (by rw [hV]; exact hvE)
    rcases hK with hKm | hK0
    · have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om (1 + 1))) :=
        CSet.add_mem ((psi_mono (S := S) hκ le_self_add).2 hown) (CSet.one_mem _ _)
      have hBV : K < V := uf_own_lt hown hownV (by rw [hV]; exact hKm.trans_lt hmv)
      have hTV : T ≤ V := hTK.trans hBV.le
      have hVT : V = T + (V - T) := (Ordinal.add_sub_cancel_of_le hTV).symm
      have hdd : u ∣ V - T := by
        have := hdvdV
        rw [hVT] at this
        exact (Ordinal.dvd_add_iff hTd).1 this
      have hlt : V - T < u := by
        have := hVE
        rw [hET, hVT] at this
        exact (add_lt_add_iff_left T).1 this
      have h0 : V - T = 0 := by
        by_contra hne
        exact absurd (Ordinal.le_of_dvd hne hdd) (not_le.2 hlt)
      rw [h0, add_zero] at hVT
      exact absurd (hVT ▸ hTK) (not_le.2 hBV)
    · -- `K = 0`: `V < u`, `u ∣ V`, so `V = 0` and `v = ψ(0) = H_0(0)`, not a fixed point of `H_0`
      have hTz : T = 0 := by rw [hTdef, hK0, Ordinal.zero_div, mul_zero]
      rw [hET, hTz, zero_add] at hVE
      have hV0 : V = 0 := by
        by_contra hne
        exact absurd (Ordinal.le_of_dvd hne hdvdV) (not_le.2 hVE)
      rw [hV0] at hV
      have h0γ : (0 : Ordinal.{0}) < γ := lt_of_lt_of_le zero_lt_one hγ1
      have hfix0 : ucH 0 v = v := ucG_fix_lower h0γ hvR (by rw [ucC_small uc_SC_Om2.1]; exact hvSC.1)
      rw [← hV, ← uf_H0 (S := S)] at hfix0
      have h1 : ucH 0 0 < ucH 0 (ucH 0 0) := (ucH_lt_iff 0).2 (ucH_SC 0 0).1
      rw [hfix0] at h1
      exact lt_irrefl _ h1
  exact ⟨hval, hmE, fun v hv hmv => not_lt.1 fun hlt => hnone v hmv hlt hv, hownE, hEE⟩

/-- **`H_γ(0) = ψ(K + Ω₂^γ)`** under the hypotheses of `uf_least` with `m = ucC γ`. -/
theorem uf_least0 {γ K : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγE : γ < ucE)
    (hown : K ∈ S.CSet K (S.psi K (Om (1 + 1)))) (hKE : K < ucE)
    (hK : S.psi K (Om (1 + 1)) ≤ ucC γ ∨ K = 0) (hm1 : ucC γ < S.psi (K + 1) (Om (1 + 1))) :
    ucH γ 0 = S.psi (K + OmTwo ^ γ) (Om (1 + 1)) ∧
      K + OmTwo ^ γ ∈ S.CSet (K + OmTwo ^ γ) (S.psi (K + OmTwo ^ γ) (Om (1 + 1))) ∧ K + OmTwo ^ γ < ucE := by
  obtain ⟨⟨o, ho⟩, -, hmin, hownE, hEE⟩ := uf_least (S := S) hγ1 hγE hown hKE hK hm1 le_rfl
  refine ⟨le_antisymm ?_ (hmin _ ⟨0, rfl⟩ (ucH_C_lt γ 0)), hownE, hEE⟩
  rw [← ho]; exact (uf_H_le_iff γ).2 zero_le

/-! ## The run -/

/-- **Validity from `D < ψ(B + Ω₂^γ·D)`** (`Ω₂^γ ∣ B < E₂`, `H_γ(c) = ψ(B)`). -/
theorem uf_valid {γ B c D : Ordinal.{0}} (hγ : γ < ucE) (hB : OmTwo ^ γ ∣ B) (hBE : B < ucE)
    (hc : ucH γ c = S.psi B (Om (1 + 1))) (hv : D < S.psi (B + OmTwo ^ γ * D) (Om (1 + 1))) :
    ∀ d, d ≤ D → d < ucH γ (c + d) := by
  intro d hd
  by_contra hle
  push Not at hle
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd hle (not_le.2 (ucH_SC _ _).1)
  have hDΩ : D ≤ OmTwo := by
    refine hv.le.trans (le_of_lt ?_); rw [uf_Om2]; exact Ts.ts_psi_lt _
  have hcl : ∀ j < γ, ucC j < ucH γ (c + d) → ∀ z < ucH γ (c + d), ucH j z < ucH γ (c + d) :=
    fun j hj hcj z hz => by
      have hf : ucH j (ucH γ (c + d)) = ucH γ (c + d) := ucG_fix_lower hj ⟨c + d, rfl⟩ hcj
      have := (ucH_lt_iff j).2 hz
      rwa [hf] at this
  have hprev : ∀ d'', d'' < D → d'' < ucH γ (c + d) →
      S.psi (B + OmTwo ^ γ * d'') (Om (1 + 1)) < ucH γ (c + d) := fun d'' hd'' hq =>
    (ucUB (S := S) hγ B c d'' hB hBE hc.ge (hd''.le.trans hDΩ)).trans_lt
      ((ucH_lt_iff γ).2 ((add_lt_add_iff_left c).2 (hq.trans_le hle)))
  have h := ucInv (S := S) hγ hB hBE (ucH_SC γ (c + d)) hcl
    (by rw [← hc]; exact (ucH_lt_iff γ).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))) hDΩ hprev
  exact absurd ((h.trans hle).trans hd) (not_le.2 hv)

/-- **The own argument of an atom from its run**: `ψ(B + Ω₂^γ·D) = H_γ(c + D)`, `D` below it, and `B + Ω₂^γ·D` is
own and below `E₂`. -/
theorem ufRun_eq {γ B c D : Ordinal.{0}} (hγ : γ < ucE) (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1))))
    (hBE : B < ucE) (hB : OmTwo ^ γ ∣ B) (hc : ucH γ c = S.psi B (Om (1 + 1))) (hD : D < OmTwo)
    (hval : ∀ d, d ≤ D → d < ucH γ (c + d)) :
    S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) = ucH γ (c + D) ∧ D < S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) ∧
      B + OmTwo ^ γ * D ∈ S.CSet (B + OmTwo ^ γ * D) (S.psi (B + OmTwo ^ γ * D) (Om (1 + 1))) ∧
      B + OmTwo ^ γ * D < ucE := by
  obtain ⟨hDψ, heq⟩ := uc_eq_all hγ hown hB hBE hc hD hval
  have hCv : ucC γ < S.psi (B + OmTwo ^ γ * D) (Om (1 + 1)) := by rw [heq]; exact ucH_C_lt γ _
  have hγv := (ucC_lt_iff (zero_le.trans_lt hCv) γ).1 hCv
  refine ⟨heq, hDψ, CSet.add_mem ((psi_mono (InR_Om_succ 1) le_self_add).2 hown) (uc_W_mem hγ hγv hDψ),
    uc_lt_E_add hγ hBE hD.le⟩

/-- **The run of an atom `H_γ(y) < B₂`** (`y < H_γ(y)`, `y` a code over a countable strongly critical `Z`):
`y = c + D` with `H_γ(c) = ψ(B)`, `B < E₂` own, `Ω₂^γ ∣ B`, `D < Ω₂` valid, `c` and `D` codes; either `c = 0`, or
`c > Ω₁` is the largest fixed point of `H_γ` in `(Ω₁, y]` and `Ω₂^{γ+1} ∣ B`. -/
theorem ufRun {Z : Ordinal.{0}} (hZS : SC Z) (hZ : Z ≤ Om1) {γ y : Ordinal.{0}} (hγ : γ < ucE)
    (hy : UcCl Z y) (hyz : y < ucH γ y) (hzB : ucH γ y < ucB) :
    ∃ B c D, B ∈ S.CSet B (S.psi B (Om (1 + 1))) ∧ B < ucE ∧ OmTwo ^ γ ∣ B ∧
      ucH γ c = S.psi B (Om (1 + 1)) ∧ c + D = y ∧ D < OmTwo ∧ (∀ d, d ≤ D → d < ucH γ (c + d)) ∧
      UcCl Z c ∧ UcCl Z D ∧
      (c = 0 ∨ (Om1 < c ∧ ucH γ c = c ∧ OmTwo ^ (γ + 1) ∣ B ∧ ∀ q, ucH γ q = q → Om1 < q → q ≤ y → q ≤ c)) := by
  have hyW : y < OmTwo := uf_cl_lt_Om2 hZ hy
  by_cases hA : ∃ q, ucH γ q = q ∧ Om1 < q ∧ q ≤ y
  · obtain ⟨q, hqf, hq1, hqy⟩ := hA
    have hne : ucH γ (y + 1) ≠ y + 1 := SC.ne_add_one (ucH_SC γ (y + 1)) y
    obtain ⟨p, hpb, hpy, hmax⟩ := rh_base_below (ucH_normal γ) (hq1.trans_le (hqy.trans (le_self_add : y ≤ y + 1)))
      hne
    have hqp : q ≤ p := hmax q hqf hq1 (Order.lt_add_one_iff.2 hqy)
    have hp1 : Om1 < p := hq1.trans_le hqp
    have hpf : ucH γ p = p := by
      rcases hpb with e | ⟨-, hf⟩
      · exact absurd e hp1.ne'
      · exact hf
    have hpy' : p ≤ y := Order.lt_add_one_iff.1 hpy
    obtain ⟨p', hp'c, hp'f, hpp', hp'y⟩ := uf_fix_code hZ hγ y hy p hpf hp1 hpy'
    have hpe : p' = p := le_antisymm (hmax p' hp'f (hp1.trans_le hpp') (Order.lt_add_one_iff.2 hp'y)) hpp'
    rw [hpe] at hp'c
    have hpz : p < ucB := hpy'.trans_lt (hyz.trans hzB)
    have hpSC : SC p := by rw [← hpf]; exact ucH_SC γ p
    obtain ⟨Bp, hown, hBpE, hBp⟩ := uc_own_of_SC (S := S) hpSC (by rw [← uf_Om1]; exact hp1) hpz
    have hdvd1 : OmTwo ^ (γ + 1) ∣ Bp := (uc_fwd_conv (S := S) γ hγ).2 Bp hown hBpE (by rw [hBp]; exact hpf)
    have hDc : UcCl Z (y - p) := (ucDec hZS hZ y hy).1 p hp'c hpy'
    refine ⟨Bp, p, y - p, hown, hBpE, (opow_dvd_opow _ le_self_add).trans hdvd1, by rw [hBp, hpf],
      Ordinal.add_sub_cancel_of_le hpy', (Ordinal.sub_le_self y p).trans_lt hyW, fun d hd => ?_, hp'c, hDc,
      Or.inr ⟨hp1, hpf, hdvd1, fun q' hq'f hq'1 hq'y => hmax q' hq'f hq'1 (Order.lt_add_one_iff.2 hq'y)⟩⟩
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero, hpf]; exact lt_of_le_of_lt zero_le hp1
    have hpd : p < p + d := lt_add_of_pos_right p (pos_iff_ne_zero.2 hd0)
    have hdy : p + d ≤ y := by
      calc p + d ≤ p + (y - p) := add_le_add_right hd p
        _ = y := Ordinal.add_sub_cancel_of_le hpy'
    have hnf : ucH γ (p + d) ≠ p + d := fun hf =>
      absurd (hmax (p + d) hf (hp1.trans hpd) (Order.lt_add_one_iff.2 hdy)) (not_le.2 hpd)
    exact le_add_self.trans_lt (lt_of_le_of_ne (ucH_le_self γ _) hnf.symm)
  push Not at hA
  have h0B : ucH γ 0 < ucB := ((uf_H_le_iff γ).2 zero_le).trans_lt hzB
  obtain ⟨e0, hown, he0E, he0⟩ := uc_own_of_SC (S := S) (ucH_SC γ 0) (by rw [← uf_Om1]; exact ucH_gt γ 0) h0B
  have hdvd : OmTwo ^ γ ∣ e0 := uf_dvd_of_range hown he0E fun j hj hd => by
    rw [he0] at hd ⊢; exact ucG_fix_lower hj ⟨0, rfl⟩ hd
  refine ⟨e0, 0, y, hown, he0E, hdvd, he0.symm, zero_add y, hyW, fun d hd => ?_, UcCl.zero hZS.1, hy, Or.inl rfl⟩
  rw [zero_add]
  have hnf : ucH γ d ≠ d := fun hf => by
    have h1 : Om1 < d := by rw [← hf]; exact ucH_gt γ d
    exact absurd hd (not_le.2 (hA d hf h1))
  exact lt_of_le_of_ne (ucH_le_self γ _) hnf.symm

end Googology.Trans.PoR.InaccPsi.R2.Uf
