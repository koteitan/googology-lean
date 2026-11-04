import Googology.Trans.PoR.InaccPsi.R2.XmPlat

/-!
# THE PLATEAU LEMMA IN THE EXPONENT: `ψ₁(B + ψ₂(b + Ω^{K+Ω₁})) ≤ sup_n x_n`

`Ω^x = leOe x = ω^{Ω₁·x}`, `x_0` given (`x_0 ≤ x_1`, `x_0 < Ω₁`), `x_{n+1} = ψ₁(a_n)`, `a_n = B + ψ₂(b + Ω^{K+x_n})`
(`yyX`, `yyA`).  No hypothesis on `B`; `b` is normal at the level `Ω₂` and `K` lies in every closure of the form
`Cl(a, ψ₂ a)` and in every stage.  This is `Xm.xmPlat` with the iterate in the exponent (`Xm.xmPlat` has it as a
coefficient `b + ω^m·x_n`); it is the lower half of the top law at the first non-code exponent `X + Ω₂`.

* `yyR3` (**a member `e ∈ Cl(a_n, x_{n+1})` below `b + Ω^{K+Ω₁}` is below `b + Ω^{K+(q+1)}` for some `q < x_{n+1}`**:
  the leading exponent of `e − b` is `Ω₁·K + r` with `r < Ω₁·Ω₁`, and `r / Ω₁` is a countable member);
* `yyStep`, `yyR2` (**a member below `ψ₂(b + Ω^{K+Ω₁})` is below `ψ₂(b + Ω^{K+x_{n+1}})`**),
* `yyKey` (every member of `Cl(B + ψ₂(b + Ω^{K+Ω₁}), sup_n x_n)` lies in some stage),
* `yyPlat` (**THE PLATEAU**), `yyX_le` (domination).

No new axiom.  New definitions: `yyX`, `yyA` (the iterates; auxiliary, no repo statement depends on them).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Uu
  Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- The iterates `x_0` (a start), `x_{n+1} = ψ₁(B + ψ₂(b + Ω^{K+x_n}))`. -/
noncomputable def yyX (S : InaccSeq.{0}) (B b K x0 : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => x0
  | n + 1 => S.psi (B + S.psi (b + leOe (K + yyX S B b K x0 n)) (Om (1 + 1))) (Om 1)

/-- The stage arguments `a_n = B + ψ₂(b + Ω^{K+x_n})`. -/
noncomputable def yyA (S : InaccSeq.{0}) (B b K x0 : Ordinal.{0}) (n : ℕ) : Ordinal.{0} :=
  B + S.psi (b + leOe (K + yyX S B b K x0 n)) (Om (1 + 1))

theorem yyX_zero (B b K x0 : Ordinal.{0}) : yyX S B b K x0 0 = x0 := rfl

theorem yyX_succ (B b K x0 : Ordinal.{0}) (n : ℕ) : yyX S B b K x0 (n + 1) = S.psi (yyA S B b K x0 n) (Om 1) := rfl

theorem yyOe_mono {x y : Ordinal.{0}} (h : x ≤ y) : leOe x ≤ leOe y := by
  unfold leOe; exact opow_le_opow_right omega0_pos (mul_le_mul_right h _)

theorem yyOe_lt {x y : Ordinal.{0}} (h : x < y) : leOe x < leOe y := by
  unfold leOe
  exact (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 h)

section Gen

variable {B b K x0 : Ordinal.{0}}

theorem yyX_mono (h0 : x0 ≤ yyX S B b K x0 1) : ∀ n : ℕ, yyX S B b K x0 n ≤ yyX S B b K x0 (n + 1) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [yyX_succ, yyX_succ]
    unfold yyA
    exact (psi_mono Low.InR_Om_one (add_le_add le_rfl
      (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (yyOe_mono (add_le_add le_rfl ih)))).1)).1

theorem yyX_monotone (h0 : x0 ≤ yyX S B b K x0 1) : Monotone (yyX S B b K x0) :=
  monotone_nat_of_le_succ (yyX_mono h0)

theorem yyA_mono (h0 : x0 ≤ yyX S B b K x0 1) {i j : ℕ} (h : i ≤ j) : yyA S B b K x0 i ≤ yyA S B b K x0 j := by
  unfold yyA
  exact add_le_add le_rfl (psi_mono (InR_Om_succ 1) (add_le_add le_rfl
    (yyOe_mono (add_le_add le_rfl (yyX_monotone h0 h))))).1

theorem yyX_lt (hx0 : x0 < Om 1) (n : ℕ) : yyX S B b K x0 n < Om 1 := by
  cases n with
  | zero => exact hx0
  | succ n => rw [yyX_succ]; exact psi_lt Low.InR_Om_one _

theorem yyX_SC (n : ℕ) : SC (yyX S B b K x0 (n + 1)) := by rw [yyX_succ]; exact SC_psi Low.InR_Om_one _

theorem yyStage_mono (h0 : x0 ≤ yyX S B b K x0 1) {i j : ℕ} (h : i ≤ j) :
    S.CSet (yyA S B b K x0 i) (yyX S B b K x0 (i + 1)) ⊆ S.CSet (yyA S B b K x0 j) (yyX S B b K x0 (j + 1)) := by
  rw [yyX_succ, yyX_succ]; exact (psi_mono Low.InR_Om_one (yyA_mono h0 h)).2

/-- `Ω₁ = ω^{Ω₁}`. -/
theorem yyOm1_eps : (ω : Ordinal.{0}) ^ Om 1 = Om 1 := gg_SC_eps Ph.ph_SC_Om1

/-- **A member below `b + Ω^{K+Ω₁}` is below `b + Ω^{K+(q+1)}` for a countable member `q < x_{n+1}`.** -/
theorem yyR3 (n : ℕ) (hK : K ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1))) {e : Ordinal.{0}}
    (he : e ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1))) (hlt : e < b + leOe (K + Om 1)) :
    ∃ q, q < yyX S B b K x0 (n + 1) ∧ e < b + leOe (K + (q + 1)) := by
  set C := S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1)) with hCdef
  have hxS := yyX_SC (S := S) (B := B) (b := b) (K := K) (x0 := x0) n
  have hpos : ∀ y, 0 < leOe y := leOe_pos
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hxS.1, h1.trans_le le_self_add⟩
  have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
  set d := e - b with hd
  have hdC : d ∈ C := Ta.taSub_mem e he b
  have hdlt : d < leOe (K + Om 1) := Ry.rySub_lt h1 hlt
  rcases eq_or_ne d 0 with hd0 | hd0
  · refine ⟨0, hxS.1, ?_⟩
    rw [e1, hd0, add_zero]; exact lt_add_of_pos_right _ (hpos _)
  set p := log ω d with hp
  have hpC : p ∈ C := (Rx.rxCDec d hdC).2
  have hdp : d < ω ^ (p + 1) := lt_opow_succ_log_self one_lt_omega0 d
  have hpe : p < Om 1 * (K + Om 1) := by
    have h := (Ordinal.lt_opow_iff_log_lt one_lt_omega0 hd0).1 hdlt
    exact h
  set m := Om 1 * K with hm
  have hmC : m ∈ C := Ld.ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) hK
  rw [mul_add] at hpe
  rcases lt_or_ge p m with hpm | hpm
  · refine ⟨0, hxS.1, ?_⟩
    rw [e1]
    refine (add_lt_add_iff_left b).2 (hdp.trans_le ?_)
    unfold leOe
    refine opow_le_opow_right omega0_pos ?_
    rw [zero_add, mul_add, mul_one]
    exact (Order.add_one_le_of_lt hpm).trans le_self_add
  set r := p - m with hr
  have hrC : r ∈ C := Ta.taSub_mem p hpC m
  have hrlt : r < Om 1 * Om 1 := Ry.rySub_lt hpm hpe
  set q := r / Om 1 with hq
  have hqC : q ∈ C := by
    have h := (Vh.vhC_div r hrC (Om 1)).2.2 (CSet.Om_mem (CSet.one_mem _ _))
    rwa [yyOm1_eps] at h
  have hΩ0 : Om 1 ≠ 0 := (Om_pos one_ne_zero).ne'
  have hq1 : q < Om 1 := (Ordinal.div_lt hΩ0).2 hrlt
  have hqx : q < yyX S B b K x0 (n + 1) := by
    have hqC' : q ∈ S.CSet (yyA S B b K x0 n) (S.psi (yyA S B b K x0 n) (Om 1)) := hqC
    rw [yyX_succ]; exact lt_psi_of_mem Low.InR_Om_one hqC' hq1
  refine ⟨q, hqx, ?_⟩
  have hrq : r < Om 1 * (q + 1) := Ordinal.lt_mul_succ_div _ hΩ0
  have hpq : p < Om 1 * (K + (q + 1)) := by
    have ep : p = m + r := (Ordinal.add_sub_cancel_of_le hpm).symm
    rw [ep, mul_add]; exact (add_lt_add_iff_left m).2 hrq
  rw [e1]
  refine (add_lt_add_iff_left b).2 (hdp.trans_le ?_)
  unfold leOe
  exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hpq)

variable (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (hK2 : ∀ a : Ordinal.{0}, K ∈ S.CSet a (S.psi a (Om (1 + 1))))
include hb hK2

/-- `ψ₂(b + Ω^{K+(q+1)}) < ψ₂(b + Ω^{K+x})` for `q < x`, `x` strongly critical and countable. -/
theorem yyStep {q x : Ordinal.{0}} (hx : SC x) (hx1 : x < Om 1) (hq : q < x) :
    S.psi (b + leOe (K + (q + 1))) (Om (1 + 1)) < S.psi (b + leOe (K + x)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hq1x : q + 1 < x := hx.isSuccLimit.add_one_lt hq
  have hlt : b + leOe (K + (q + 1)) < b + leOe (K + x) :=
    (add_lt_add_iff_left b).2 (yyOe_lt ((add_lt_add_iff_left K).2 hq1x))
  refine psi_lt_psi_of_mem hκ2 hlt (CSet.add_mem ((psi_mono hκ2 le_self_add).2 hb) (leOe_mem ?_))
  exact CSet.add_mem (hK2 _) (CSet.of_lt ((hq1x.trans hx1).trans (psiS_bounds (S := S) _ 1).1))

/-- **A member of a stage below `ψ₂(b + Ω^{K+Ω₁})` is below `ψ₂(b + Ω^{K+x_{n+1}})`.** -/
theorem yyR2 (n : ℕ) (hK : K ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1))) :
    ∀ y ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1)),
      y < S.psi (b + leOe (K + Om 1)) (Om (1 + 1)) →
        y < S.psi (b + leOe (K + yyX S B b K x0 (n + 1))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hs1 : (1 : Ordinal.{0}) + 1 < Om 1 := lt_of_lt_of_le (by
    rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2)
    (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le
  have hx := yyX_SC (S := S) (B := B) (b := b) (K := K) (x0 := x0) n
  have hx1 : yyX S B b K x0 (n + 1) < Om 1 := by rw [yyX_succ]; exact psi_lt Low.InR_Om_one _
  set P := S.psi (b + leOe (K + yyX S B b K x0 (n + 1))) (Om (1 + 1)) with hP
  have hPS : SC P := SC_psi hκ2 _
  have h1P : Om 1 < P := (psiS_bounds (S := S) _ 1).1
  intro y hy
  induction hy with
  | small h => exact fun _ => h.trans (hx1.trans h1P)
  | zero => exact fun _ => hPS.1
  | inacc j => exact fun h => absurd ((uuOm_le_I hs1 j).trans_lt h) (not_lt.2 (psi_lt hκ2 _).le)
  | inaccW =>
    exact fun h => absurd (((uuOm_le_I hs1 0).trans (S.I_le_Iw 0)).trans_lt h) (not_lt.2 (psi_lt hκ2 _).le)
  | add _ _ ihp ihq =>
    exact fun h => hPS.isPrincipal (ihp ((le_self_add).trans_lt h)) (ihq ((le_add_self).trans_lt h))
  | phi _ _ ihp ihq =>
    exact fun h => hPS.2 _ (ihp ((left_le_veblen _ _).trans_lt h)) _ (ihq ((right_le_veblen _ _).trans_lt h))
  | @om a _ _ =>
    intro h
    have h2 : Om a < Om (1 + 1) := h.trans (psi_lt hκ2 _)
    have ha : a ≤ 1 := Order.lt_add_one_iff.1 (Om_lt_Om.1 h2)
    exact (Om_le_Om.2 ha).trans_lt h1P
  | @coll π e hπ _ heC _ _ =>
    intro h
    rcases lt_trichotomy π (Om (1 + 1)) with hlt | heq | hgt
    · exact (psi_lt hπ _).trans_le ((uuInR_lt hs1 hπ hlt).trans h1P.le)
    · subst heq
      have he : e.1 < b + leOe (K + Om 1) := by
        by_contra hc; push Not at hc
        exact absurd ((psi_mono hκ2 hc).1.trans_lt h) (lt_irrefl _)
      obtain ⟨q, hq, hqe⟩ := yyR3 n hK heC he
      exact (psi_mono hκ2 hqe.le).1.trans_lt (yyStep hb hK2 hx hx1 hq)
    · exact absurd ((uuInR_gt hs1 hπ hgt e.1).trans_lt h) (not_lt.2 (psi_lt hκ2 _).le)

/-- **Every member of `Cl(B + ψ₂(b + Ω^{K+Ω₁}), sup_n x_n)` lies in a stage.** -/
theorem yyKey (h0 : x0 ≤ yyX S B b K x0 1) (hx0 : x0 < Om 1)
    (hK : ∀ n, K ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1))) :
    ∀ y ∈ S.CSet (B + S.psi (b + leOe (K + Om 1)) (Om (1 + 1))) (⨆ n : ℕ, yyX S B b K x0 n),
      ∃ n, y ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1)) := by
  have hbdd : BddAbove (range (yyX S B b K x0)) := ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (yyX_lt hx0 n).le⟩
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, CSet.of_lt (hn.trans_le (yyX_mono h0 n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (yyStage_mono h0 (le_max_left i j) hi) (yyStage_mono h0 (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (yyStage_mono h0 (le_max_left i j) hi) (yyStage_mono h0 (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < yyA S B b K x0 (k + 1) := by
      unfold yyA
      rcases lt_or_ge e.1 B with h1 | h1
      · exact h1.trans_le le_self_add
      · have hw : e.1 - B < S.psi (b + leOe (K + Om 1)) (Om (1 + 1)) := Ry.rySub_lt h1 e.2
        have h3 := yyR2 hb hK2 k (hK k) _ (Ta.taSub_mem e.1 hk B) hw
        have ee : e.1 = B + (e.1 - B) := (Ordinal.add_sub_cancel_of_le h1).symm
        rw [ee]; exact (add_lt_add_iff_left B).2 h3
    set N := max (k + 1) i with hN
    have hltN : e.1 < yyA S B b K x0 N := hlt.trans_le (yyA_mono h0 (le_max_left (k + 1) i))
    have heN := yyStage_mono (S := S) (B := B) (b := b) (K := K) (x0 := x0) h0
      ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := yyStage_mono (S := S) (B := B) (b := b) (K := K) (x0 := x0) h0 (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU LEMMA IN THE EXPONENT**: `ψ₁(B + ψ₂(b + Ω^{K+Ω₁})) ≤ sup_n x_n`. -/
theorem yyPlat (h0 : x0 ≤ yyX S B b K x0 1) (hx0 : x0 < Om 1)
    (hK : ∀ n, K ∈ S.CSet (yyA S B b K x0 n) (yyX S B b K x0 (n + 1))) :
    S.psi (B + S.psi (b + leOe (K + Om 1)) (Om (1 + 1))) (Om 1) ≤ ⨆ n : ℕ, yyX S B b K x0 n := by
  have hbdd : BddAbove (range (yyX S B b K x0)) := ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (yyX_lt hx0 n).le⟩
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun y hy hy1 => ?_
  obtain ⟨n, hn⟩ := yyKey hb hK2 h0 hx0 hK y hy
  rw [yyX_succ] at hn
  have h := lt_psi_of_mem Low.InR_Om_one hn hy1
  rw [← yyX_succ] at h
  exact h.trans_le (le_ciSup hbdd (n + 1))

end Gen

/-- **Domination**: a sequence `y` with `ψ₁(B + ψ₂(b + Ω^{K+y_n})) ≤ y_{n+1}` is above `x`. -/
theorem yyX_le {B b K x0 : Ordinal.{0}} {y : ℕ → Ordinal.{0}} (h0 : x0 ≤ y 0)
    (hy : ∀ n, S.psi (B + S.psi (b + leOe (K + y n)) (Om (1 + 1))) (Om 1) ≤ y (n + 1)) :
    ∀ n, yyX S B b K x0 n ≤ y n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [yyX_succ]
    unfold yyA
    exact (psi_mono Low.InR_Om_one (add_le_add le_rfl
      (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (yyOe_mono (add_le_add le_rfl ih)))).1)).1.trans (hy n)

end Googology.Trans.PoR.InaccPsi.R2.Yy
