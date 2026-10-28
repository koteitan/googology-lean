import Googology.Trans.PoR.InaccPsi.R2.UfUnc
import Googology.Trans.PoR.InaccPsi.R2.UoB
import Googology.Trans.PoR.InaccPsi.R2.VgCode

/-!
# The domain of `B_n` is closed under the Cantor normal form, and `B_n` moves `ω^K·x`, `Ω₁^μ·D` with no bound

`B_n = Bc.bcB S n`, `MvD S` its normal-form domain, `nf = Bc.bcNf S`, `uiDat` the largest countable leaf of the
normal form (subscripts included), `L(ω) = Nc.ncL S ω`, `θ = ConjT.th S`.  The level moves of `R2.UfW` / `R2.UfB` asked
for a class of components closed under `log_ω` and the tail; here that class is `MvD` itself:

* `vjD_prin` (**a principal normal form denotes `ω^g` with `g` in the domain**), `vjD_parts` (**`x ∈ MvD`, `x ≠ 0`:
  `log_ω x` and `x − ω^{log_ω x}` are in `MvD`**);
* `vjB_mulOp` (**`B_n(ω^K·x) = ω^{B_n K}·B_n x` for all `K, x ∈ MvD`**), `vjB_Om1mul` (`B_n(Ω₁·μ) = Ω₁·B_n μ`),
  `vjB_Wpow` (**`B_n(Ω₁^μ·D) = Ω₁^{B_n μ}·B_n D`**), `vjB_Oe` (`B_n(u_μ) = u_{B_n μ}`, `u_μ = Le.leOe μ`);
* `vjD_of_dat` (**an ordinal of the notation whose countable leaves lie below `L(ω)` is in `MvD`**), `vjK_notA`
  (**`K⁽⁰⁾_q ⊆` the notation for `q ≤ ψ_{Ω₁}(A)`**), `vjD_lev` (**a level `μ` with `d(μ) < q`, `q ≤ L(ω)` strongly
  critical, is in `MvD`**, `d = Ul.ulD S 0`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-! ## The domain is closed under the Cantor normal form -/

/-- **A principal normal form in the domain denotes `ω^g` with `g` in the domain.** -/
theorem vjD_prin {t : Term} (hD : bcD S t) (hp : t.isPrin = true) : ∃ g, val S t = ω ^ g ∧ MvD S g := by
  have hN := hD.1
  have hfix : SC (val S t) → ∃ g, val S t = ω ^ g ∧ MvD S g := fun h =>
    ⟨val S t, (Low.opow_eq_self_of_SC h).symm, mvD_of_term hD⟩
  cases t with
  | phi c d =>
    have hNc : NF c := hN.1
    have hNd : NF d := hN.2.1
    have hA : bcArgsLt S (bcAlphaW S) c ∧ bcArgsLt S (bcAlphaW S) d := hD.2
    by_cases hc : c = Term.zero
    · subst hc
      refine ⟨val S d, ?_, mvD_of_term ⟨hNd, hA.2⟩⟩
      show veblen (val S Term.zero) (val S d) = ω ^ val S d
      rw [show val S Term.zero = 0 from rfl, veblen_zero_apply]
    · have hc0 : val S c ≠ 0 := val_ne_zero (S := S) hNc hc
      refine ⟨val S (phi c d), ?_, mvD_of_term hD⟩
      show veblen (val S c) (val S d) = ω ^ veblen (val S c) (val S d)
      rw [← veblen_zero_apply, veblen_veblen_of_lt (pos_iff_ne_zero.2 hc0)]
  | zero => exact absurd hp (by simp [isPrin, isSC])
  | add _ _ => exact absurd hp (by simp [isPrin, isSC])
  | inacc _ => exact hfix (SC_val (S := S) hN rfl)
  | inaccW => exact hfix (SC_val (S := S) hN rfl)
  | om _ => exact hfix (SC_val (S := S) hN rfl)
  | psiS _ _ => exact hfix (SC_val (S := S) hN rfl)
  | psiI _ _ => exact hfix (SC_val (S := S) hN rfl)

/-- **`x ∈ MvD`, `x ≠ 0`: `log_ω x` and `x − ω^{log_ω x}` are in `MvD`.** -/
theorem vjD_parts {x : Ordinal.{0}} (hx : MvD S x) (hx0 : x ≠ 0) :
    MvD S (log ω x) ∧ MvD S (x - ω ^ log ω x) := by
  have hv := mvD_val hx
  have hD : bcD S (bcNf S x) := hx.2
  generalize ht : bcNf S x = t at hv hD
  subst hv
  cases t with
  | zero => exact absurd rfl hx0
  | add a b =>
    have hN := hD.1
    have hNa : NF a := hN.1
    have hNb : NF b := hN.2.1
    have hpa : a.isPrin = true := hN.2.2.1
    have hhb : cmp (head b) a ≠ .gt := hN.2.2.2.2
    have hA : bcArgsLt S (bcAlphaW S) a ∧ bcArgsLt S (bcAlphaW S) b := hD.2
    obtain ⟨g, hg, hDg⟩ := vjD_prin ⟨hNa, hA.1⟩ hpa
    have hle : val S (head b) ≤ val S a := by
      have e := cmp_eq_compare (S := S) hNb.head hNa
      rw [e] at hhb
      exact not_lt.1 fun h => hhb (compare_gt_iff_gt.2 h)
    have hbl : val S b < ω ^ (g + 1) :=
      val_lt_of_head_lt (exact_all _) le_rfl hNb (sem_of_NF hNb) (isPrincipal_add_omega0_opow _)
        (hle.trans_lt (by rw [hg]; exact opow_lt_opow_add_one g))
    have hval : val S (add a b) = ω ^ g + val S b := by
      show val S a + val S b = _; rw [hg]
    rw [hval, log_opow_add hbl]
    refine ⟨hDg, ?_⟩
    have := tail_opow_add hbl
    unfold tail lead at this
    rw [log_opow_add hbl] at this
    rw [this]
    exact mvD_of_term ⟨hNb, hA.2⟩
  | phi c d =>
    obtain ⟨g, hg, hDg⟩ := vjD_prin hD rfl
    rw [hg, Ordinal.log_opow one_lt_omega0, Ordinal.sub_self]; exact ⟨hDg, mvD_of_lt ((Lw.lw_L_SC S ω).1)⟩
  | inacc n =>
    obtain ⟨g, hg, hDg⟩ := vjD_prin hD rfl
    rw [hg, Ordinal.log_opow one_lt_omega0, Ordinal.sub_self]; exact ⟨hDg, mvD_of_lt ((Lw.lw_L_SC S ω).1)⟩
  | inaccW =>
    obtain ⟨g, hg, hDg⟩ := vjD_prin hD rfl
    rw [hg, Ordinal.log_opow one_lt_omega0, Ordinal.sub_self]; exact ⟨hDg, mvD_of_lt ((Lw.lw_L_SC S ω).1)⟩
  | om a =>
    obtain ⟨g, hg, hDg⟩ := vjD_prin hD rfl
    rw [hg, Ordinal.log_opow one_lt_omega0, Ordinal.sub_self]; exact ⟨hDg, mvD_of_lt ((Lw.lw_L_SC S ω).1)⟩
  | psiS s a =>
    obtain ⟨g, hg, hDg⟩ := vjD_prin hD rfl
    rw [hg, Ordinal.log_opow one_lt_omega0, Ordinal.sub_self]; exact ⟨hDg, mvD_of_lt ((Lw.lw_L_SC S ω).1)⟩
  | psiI n a =>
    obtain ⟨g, hg, hDg⟩ := vjD_prin hD rfl
    rw [hg, Ordinal.log_opow one_lt_omega0, Ordinal.sub_self]; exact ⟨hDg, mvD_of_lt ((Lw.lw_L_SC S ω).1)⟩

/-! ## `B_n` on `ω^K·x` -/

/-- **`B_n(ω^K·x) = ω^{B_n K}·B_n x`** for all `K, x ∈ MvD`. -/
theorem vjB_mulOp {n : ℕ} {K : Ordinal.{0}} (hDK : MvD S K) :
    ∀ x, MvD S x → MvD S (ω ^ K * x) ∧ Bc.bcB S n (ω ^ K * x) = ω ^ Bc.bcB S n K * Bc.bcB S n x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hDx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨by rw [mul_zero]; exact hDx, by rw [mul_zero, Bc.bcB_zero, mul_zero]⟩
  obtain ⟨hDg, hDr⟩ := vjD_parts hDx hx0
  set g := log ω x with hg
  have hlead : ω ^ g ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ g + (x - ω ^ g) = x := Ordinal.add_sub_cancel_of_le hlead
  have hrx : x - ω ^ g < x := tail_lt hx0
  obtain ⟨hDκr, hBκr⟩ := IH _ hrx hDr
  obtain ⟨hDog, hBog⟩ := Ld.ldB_opow (n := n) hDg
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDog hDr
  rw [hdec] at hBx
  obtain ⟨hDKg, hBKg⟩ := mvB_add (k := n) hDK hDg
  obtain ⟨hDe, hBe⟩ := Ld.ldB_opow (n := n) hDKg
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDe hDκr
  have e : ω ^ K * x = ω ^ (K + g) + ω ^ K * (x - ω ^ g) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add]
  rw [e]
  refine ⟨hDs, ?_⟩
  rw [hBs, hBe, hBKg, hBκr, hBx, hBog, opow_add, mul_add]

/-- **`B_n(Ω₁·μ) = Ω₁·B_n μ`** for `μ ∈ MvD`. -/
theorem vjB_Om1mul {n : ℕ} {μ : Ordinal.{0}} (hμ : MvD S μ) :
    MvD S (Om 1 * μ) ∧ Bc.bcB S n (Om 1 * μ) = Om 1 * Bc.bcB S n μ := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hO : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have h := vjB_mulOp (n := n) hDO μ hμ
  rw [hO, hBO, hO] at h
  exact h

/-- **`B_n(Ω₁^μ·D) = Ω₁^{B_n μ}·B_n D`** for `μ, D ∈ MvD`. -/
theorem vjB_Wpow {n : ℕ} {μ D : Ordinal.{0}} (hμ : MvD S μ) (hD : MvD S D) :
    MvD S (Om 1 ^ μ * D) ∧ Bc.bcB S n (Om 1 ^ μ * D) = Om 1 ^ Bc.bcB S n μ * Bc.bcB S n D := by
  have hO : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
  have hp : ∀ z : Ordinal.{0}, Om 1 ^ z = ω ^ (Om 1 * z) := fun z => by
    conv_lhs => rw [← hO]
    rw [← opow_mul]
  obtain ⟨hDm, hBm⟩ := vjB_Om1mul (n := n) hμ
  have h := vjB_mulOp (n := n) hDm D hD
  rw [hBm, ← hp, ← hp] at h
  exact h

/-- **`B_n(u_μ) = u_{B_n μ}`** (`u_μ = ω^{Ω₁·μ}`) for `μ ∈ MvD`. -/
theorem vjB_Oe {n : ℕ} {μ : Ordinal.{0}} (hμ : MvD S μ) :
    MvD S (Le.leOe μ) ∧ Bc.bcB S n (Le.leOe μ) = Le.leOe (Bc.bcB S n μ) := by
  obtain ⟨hDK, hBK⟩ := vjB_Om1mul (n := n) hμ
  obtain ⟨hD, hB⟩ := Ld.ldB_opow (n := n) hDK
  unfold Le.leOe; rw [hB, hBK]; exact ⟨hD, rfl⟩

/-! ## Membership in the domain from the countable leaves -/

theorem vj_argsLt_of_dat {A : Ordinal.{0}} :
    ∀ t : Term, NF t → Ui.uiDatT S t < S.psi A (Om 1) → bcArgsLt S A t := by
  intro t
  induction t with
  | zero => intro _ _; trivial
  | inacc n => intro _ _; trivial
  | inaccW => intro _ _; trivial
  | add a b iha ihb =>
    intro hN hd
    by_cases h : val S (add a b) < Om 1
    · rw [Ui.uiDatT_small h] at hd; exact bcArgsLt_of_lt S hN hd
    simp only [Ui.uiDatT, if_neg h] at hd
    exact ⟨iha hN.1 (lt_of_le_of_lt (le_max_left _ _) hd), ihb hN.2.1 (lt_of_le_of_lt (le_max_right _ _) hd)⟩
  | phi a b iha ihb =>
    intro hN hd
    by_cases h : val S (phi a b) < Om 1
    · rw [Ui.uiDatT_small h] at hd; exact bcArgsLt_of_lt S hN hd
    simp only [Ui.uiDatT, if_neg h] at hd
    exact ⟨iha hN.1 (lt_of_le_of_lt (le_max_left _ _) hd), ihb hN.2.1 (lt_of_le_of_lt (le_max_right _ _) hd)⟩
  | om a iha =>
    intro hN hd
    by_cases h : val S (om a) < Om 1
    · rw [Ui.uiDatT_small h] at hd; exact bcArgsLt_of_lt S hN hd
    simp only [Ui.uiDatT, if_neg h] at hd
    exact iha hN.1 hd
  | psiS s a ihs iha =>
    intro hN hd
    by_cases h : val S (psiS s a) < Om 1
    · rw [Ui.uiDatT_small h] at hd; exact bcArgsLt_of_lt S hN hd
    simp only [Ui.uiDatT, if_neg h] at hd
    refine ⟨ihs hN.1 (lt_of_le_of_lt (le_max_left _ _) hd), iha hN.2.1 (lt_of_le_of_lt (le_max_right _ _) hd),
      fun hs0 => ?_⟩
    subst hs0
    exfalso; apply h
    show S.psi (val S a) (Om (val S Term.zero + 1)) < Om 1
    rw [show val S Term.zero = 0 from rfl, zero_add]
    exact psi_lt Low.InR_Om_one _
  | psiI n a iha =>
    intro hN hd
    by_cases h : val S (psiI n a) < Om 1
    · rw [Ui.uiDatT_small h] at hd; exact bcArgsLt_of_lt S hN hd
    simp only [Ui.uiDatT, if_neg h] at hd
    exact iha hN.1 hd

/-- **An ordinal of the notation whose countable leaves lie below `L(ω)` is in `MvD`.** -/
theorem vjD_of_dat {x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (hd : Ui.uiDat S x < Nc.ncL S ω) : MvD S x :=
  ⟨hx, (bcNf_spec S hx).1, vj_argsLt_of_dat _ (bcNf_spec S hx).1 (by rw [← ncL_omega_eq]; exact hd)⟩

/-- **`K⁽⁰⁾_q` lies in the notation** for `q ≤ ψ_{Ω₁}(A)`. -/
theorem vjK_notA {q A : Ordinal.{0}} (hq : q ≤ S.psi A (Om 1)) {x : Ordinal.{0}} (hx : Ul.UlK S 0 q x) :
    x ∈ ⋃ a, S.CSet a 0 := by
  have hjoin : ∀ {x y : Ordinal.{0}}, x ∈ ⋃ a, S.CSet a 0 → y ∈ ⋃ a, S.CSet a 0 →
      ∃ c, x ∈ S.CSet c 0 ∧ y ∈ S.CSet c 0 := fun hx hy => by
    obtain ⟨a, ha⟩ := mem_iUnion.1 hx
    obtain ⟨b, hb⟩ := mem_iUnion.1 hy
    exact ⟨max a b, CSet_mono (le_max_left a b) le_rfl ha, CSet_mono (le_max_right a b) le_rfl hb⟩
  induction hx with
  | @small y h => exact mem_of_lt_psi S (h.trans_le hq)
  | zero => exact mem_iUnion.2 ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact mem_iUnion.2 ⟨0, CSet.I_mem _ _ n⟩
  | inaccW => exact mem_iUnion.2 ⟨0, CSet.Iw_mem _ _⟩
  | add _ _ ihx ihy =>
    obtain ⟨c, h1, h2⟩ := hjoin ihx ihy; exact mem_iUnion.2 ⟨c, CSet.add_mem h1 h2⟩
  | phi _ _ ihx ihy =>
    obtain ⟨c, h1, h2⟩ := hjoin ihx ihy; exact mem_iUnion.2 ⟨c, CSet.phi_mem h1 h2⟩
  | om _ ihx =>
    obtain ⟨c, h1⟩ := mem_iUnion.1 ihx; exact mem_iUnion.2 ⟨c, CSet.Om_mem h1⟩
  | @coll π e hπ _ _ _ ihπ ihe =>
    obtain ⟨c, h1, h2⟩ := hjoin ihπ ihe
    exact mem_iUnion.2 ⟨max c (e + 1), CSet.psi_mem ((lt_add_one e).trans_le (le_max_right _ _)) hπ
      (CSet_mono (le_max_left _ _) le_rfl h1) (CSet_mono (le_max_left _ _) le_rfl h2)⟩

/-- **A level `μ` with `d(μ) < q` (`q ≤ L(ω)` strongly critical) is in the notation, has its countable leaves below
`q`, and is in `MvD`.** -/
theorem vjD_lev {q μ : Ordinal.{0}} (hq : SC q) (hqL : q ≤ Nc.ncL S ω) (hd : Ul.ulD S 0 μ < q) :
    μ ∈ ⋃ a, S.CSet a 0 ∧ Ui.uiDat S μ < q ∧ MvD S μ := by
  have hK : Ul.UlK S 0 q μ := (Ul.ul_vis hq).1 hd
  have hN := vjK_notA (A := bcAlphaW S) (by rw [← ncL_omega_eq]; exact hqL) hK
  have hq1 : q ≤ Om 1 := hqL.trans (by rw [ncL_omega_eq]; exact (psi_lt Low.InR_Om_one _).le)
  have hdu : Ui.uiDat S μ < q := by
    rw [← Vd.vd_dat_ui hN hq hq1, Vd.vdD_eq]; exact hd
  exact ⟨hN, hdu, vjD_of_dat hN (hdu.trans_le hqL)⟩

/-- **`B_n` fixes an ordinal of the notation whose countable leaves lie below `c_n`.** -/
theorem vjB_fix_dat {n : ℕ} {x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (hd : Ui.uiDat S x < Bc.bcC S n) :
    Bc.bcB S n x = x := by
  have hN := (bcNf_spec S hx).1
  have hA : bcArgsLt S (bcAlpha S (n + 1)) (bcNf S x) :=
    vj_argsLt_of_dat _ hN (by rw [← Bc.ncL_nat_eq]; exact hd)
  unfold Bc.bcB
  rw [bcSig_id hN hA]; exact (bcNf_spec S hx).2

end Googology.Trans.PoR.InaccPsi.R2.Vj
