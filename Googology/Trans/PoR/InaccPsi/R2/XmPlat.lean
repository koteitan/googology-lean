import Googology.Trans.PoR.InaccPsi.R2.XiRef
import Googology.Trans.PoR.InaccPsi.R2.VhDiv
import Googology.Trans.PoR.InaccPsi.R2.TaVeb
import Googology.Trans.PoR.InaccPsi.R2.UuPsi

/-!
# THE PLATEAU LEMMA: `ψ₁(B + ψ₂(b + ω^m·Ω₁)) ≤ sup_n x_n`

`x_0` given (`x_0 ≤ x_1`, `x_0 < Ω₁`), `x_{n+1} = ψ₁(a_n)`, `a_n = B + ψ₂(b + ω^m·x_n)` (`xmX`, `xmA`).  No hypothesis on `B`; `b` is normal at
the level `Ω₂` (`b ∈ Cl(b, ψ₂(b))`) and the exponent `m` is in the stage closures.

* `xmX_mono` (the `x_n` increase), `xmR3` (**a member `e ∈ Cl(a_n, x_{n+1})` below `b + ω^m·Ω₁` is below
  `b + ω^m·x_{n+1}`**: its `ω^m`-quotient over `b` is a countable member, so below `x_{n+1} = ψ₁(a_n)`),
  `xmR2` (**a member below `ψ₂(b + ω^m·Ω₁)` is below `ψ₂(b + ω^m·x_{n+1})`**: induction on the closure, the
  only real case is a collapse `ψ₂(e)`, with `xmR3`),
  `xmKey` (every member of `Cl(B + ψ₂(b + ω^m·Ω₁), sup_n x_n)` is in some stage `Cl(a_n, x_{n+1})`),
  `xmPlat` (**THE PLATEAU**: `ψ₁(B + ψ₂(b + ω^m·Ω₁)) ≤ sup_n x_n`), `xmX_le` (any sequence `y` with
  `ψ₁(B + ψ₂(b + ω^m·y_n)) ≤ y_{n+1}` dominates `x`).

No new axiom.  New definitions: `xmX`, `xmA` (the iterates; auxiliary, no repo statement depends on them).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Uu

variable {S : InaccSeq.{0}}

/-- The iterates `x_0` (a start), `x_{n+1} = ψ₁(B + ψ₂(b + ω^m·x_n))`. -/
noncomputable def xmX (S : InaccSeq.{0}) (B b m x0 : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => x0
  | n + 1 => S.psi (B + S.psi (b + ω ^ m * xmX S B b m x0 n) (Om (1 + 1))) (Om 1)

/-- The stage arguments `a_n = B + ψ₂(b + ω^m·x_n)`. -/
noncomputable def xmA (S : InaccSeq.{0}) (B b m x0 : Ordinal.{0}) (n : ℕ) : Ordinal.{0} :=
  B + S.psi (b + ω ^ m * xmX S B b m x0 n) (Om (1 + 1))

theorem xmX_zero (B b m x0 : Ordinal.{0}) : xmX S B b m x0 0 = x0 := rfl

theorem xmX_succ (B b m x0 : Ordinal.{0}) (n : ℕ) : xmX S B b m x0 (n + 1) = S.psi (xmA S B b m x0 n) (Om 1) := rfl

section Gen

variable {B b m x0 : Ordinal.{0}}

theorem xmX_mono (h0 : x0 ≤ xmX S B b m x0 1) : ∀ n : ℕ, xmX S B b m x0 n ≤ xmX S B b m x0 (n + 1) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [xmX_succ, xmX_succ]
    unfold xmA
    exact (psi_mono Low.InR_Om_one (add_le_add le_rfl
      (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (mul_le_mul_right ih _))).1)).1

theorem xmX_monotone (h0 : x0 ≤ xmX S B b m x0 1) : Monotone (xmX S B b m x0) := monotone_nat_of_le_succ (xmX_mono h0)

theorem xmA_mono (h0 : x0 ≤ xmX S B b m x0 1) {i j : ℕ} (h : i ≤ j) : xmA S B b m x0 i ≤ xmA S B b m x0 j := by
  unfold xmA
  exact add_le_add le_rfl (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (mul_le_mul_right (xmX_monotone h0 h) _))).1

theorem xmX_lt (hx0 : x0 < Om 1) (n : ℕ) : xmX S B b m x0 n < Om 1 := by
  cases n with
  | zero => exact hx0
  | succ n => rw [xmX_succ]; exact psi_lt Low.InR_Om_one _

theorem xmX_SC (n : ℕ) : SC (xmX S B b m x0 (n + 1)) := by rw [xmX_succ]; exact SC_psi Low.InR_Om_one _

theorem xmStage_mono (h0 : x0 ≤ xmX S B b m x0 1) {i j : ℕ} (h : i ≤ j) :
    S.CSet (xmA S B b m x0 i) (xmX S B b m x0 (i + 1)) ⊆ S.CSet (xmA S B b m x0 j) (xmX S B b m x0 (j + 1)) := by
  rw [xmX_succ, xmX_succ]; exact (psi_mono Low.InR_Om_one (xmA_mono h0 h)).2

/-- **A member below `b + ω^m·Ω₁` is below `b + ω^m·x_{n+1}`.** -/
theorem xmR3 (n : ℕ) (hm : m ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1))) {e : Ordinal.{0}}
    (he : e ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1))) (hlt : e < b + ω ^ m * Om 1) :
    ∃ q, q < xmX S B b m x0 (n + 1) ∧ e < b + ω ^ m * (q + 1) := by
  have hM0 : ω ^ m ≠ 0 := (opow_pos _ omega0_pos).ne'
  rcases lt_or_ge e b with h1 | h1
  · refine ⟨0, (xmX_SC n).1, h1.trans_le le_self_add⟩
  · have hsub : e - b < ω ^ m * Om 1 := Ry.rySub_lt h1 hlt
    set q := (e - b) / ω ^ m with hq
    have hqC : q ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1)) :=
      (Vh.vhC_div _ (Ta.taSub_mem e he b) m).2.2 hm
    have hq1 : q < Om 1 := (Ordinal.div_lt hM0).2 hsub
    have hqx : q < xmX S B b m x0 (n + 1) := by
      rw [xmX_succ] at hqC ⊢; exact lt_psi_of_mem Low.InR_Om_one hqC hq1
    refine ⟨q, hqx, ?_⟩
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rw [e1]
    exact (add_lt_add_iff_left b).2 (Ordinal.lt_mul_succ_div _ hM0)

variable (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (hm2 : ∀ a : Ordinal.{0}, m ∈ S.CSet a (S.psi a (Om (1 + 1))))
include hb hm2

/-- `ψ₂(b + ω^m·(q+1)) < ψ₂(b + ω^m·x)` for `q < x`, `x` strongly critical and countable. -/
theorem xmStep {q x : Ordinal.{0}} (hx : SC x) (hx1 : x < Om 1) (hq : q < x) :
    S.psi (b + ω ^ m * (q + 1)) (Om (1 + 1)) < S.psi (b + ω ^ m * x) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hxε : ω ^ x = x := gg_SC_eps hx
  have hq1x : q + 1 < x := hx.isSuccLimit.add_one_lt hq
  set E := b + ω ^ (m + (q + 1)) with hE
  have hle : b + ω ^ m * (q + 1) ≤ E := by
    rw [hE, opow_add]
    exact add_le_add le_rfl (mul_le_mul_right (Ordinal.right_le_opow _ one_lt_omega0) _)
  have hEx : E < b + ω ^ m * x := by
    rw [hE]
    conv_rhs => rw [← hxε, ← opow_add]
    exact (add_lt_add_iff_left b).2 ((opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left m).2 hq1x))
  have hEC : E ∈ S.CSet (b + ω ^ m * x) (S.psi (b + ω ^ m * x) (Om (1 + 1))) := by
    refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hb) ?_
    have h1 : m + (q + 1) ∈ S.CSet (b + ω ^ m * x) (S.psi (b + ω ^ m * x) (Om (1 + 1))) :=
      CSet.add_mem (hm2 _) (CSet.of_lt ((hq1x.trans hx1).trans (psiS_bounds (S := S) _ 1).1))
    have h2 := CSet.phi_mem (CSet.zero_mem (S := S) _ _) h1
    rwa [veblen_zero_apply] at h2
  exact (psi_mono hκ2 hle).1.trans_lt (psi_lt_psi_of_mem hκ2 hEx hEC)

/-- **A member of a stage below `ψ₂(b + ω^m·Ω₁)` is below `ψ₂(b + ω^m·x_{n+1})`.** -/
theorem xmR2 (n : ℕ) (hm : m ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1))) :
    ∀ y ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1)),
      y < S.psi (b + ω ^ m * Om 1) (Om (1 + 1)) → y < S.psi (b + ω ^ m * xmX S B b m x0 (n + 1)) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hs1 : (1 : Ordinal.{0}) + 1 < Om 1 := lt_of_lt_of_le (by
    rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2)
    (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le
  have hx := xmX_SC (S := S) (B := B) (b := b) (m := m) (x0 := x0) n
  have hx1 : xmX S B b m x0 (n + 1) < Om 1 := by rw [xmX_succ]; exact psi_lt Low.InR_Om_one _
  set P := S.psi (b + ω ^ m * xmX S B b m x0 (n + 1)) (Om (1 + 1)) with hP
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
      have he : e.1 < b + ω ^ m * Om 1 := by
        by_contra hc; push Not at hc
        exact absurd ((psi_mono hκ2 hc).1.trans_lt h) (lt_irrefl _)
      obtain ⟨q, hq, hqe⟩ := xmR3 n hm heC he
      exact (psi_mono hκ2 hqe.le).1.trans_lt (xmStep hb hm2 hx hx1 hq)
    · exact absurd ((uuInR_gt hs1 hπ hgt e.1).trans_lt h) (not_lt.2 (psi_lt hκ2 _).le)

/-- **Every member of `Cl(B + ψ₂(b + ω^m·Ω₁), sup_n x_n)` lies in a stage.** -/
theorem xmKey (h0 : x0 ≤ xmX S B b m x0 1) (hx0 : x0 < Om 1) (hm : ∀ n, m ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1))) :
    ∀ y ∈ S.CSet (B + S.psi (b + ω ^ m * Om 1) (Om (1 + 1))) (⨆ n : ℕ, xmX S B b m x0 n),
      ∃ n, y ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1)) := by
  have hbdd : BddAbove (range (xmX S B b m x0)) := ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (xmX_lt hx0 n).le⟩
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, CSet.of_lt (hn.trans_le (xmX_mono h0 n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (xmStage_mono h0 (le_max_left i j) hi) (xmStage_mono h0 (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (xmStage_mono h0 (le_max_left i j) hi) (xmStage_mono h0 (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < xmA S B b m x0 (k + 1) := by
      unfold xmA
      rcases lt_or_ge e.1 B with h1 | h1
      · exact h1.trans_le le_self_add
      · have hw : e.1 - B < S.psi (b + ω ^ m * Om 1) (Om (1 + 1)) := Ry.rySub_lt h1 e.2
        have h3 := xmR2 hb hm2 k (hm k) _ (Ta.taSub_mem e.1 hk B) hw
        have ee : e.1 = B + (e.1 - B) := (Ordinal.add_sub_cancel_of_le h1).symm
        rw [ee]; exact (add_lt_add_iff_left B).2 h3
    set N := max (k + 1) i with hN
    have hltN : e.1 < xmA S B b m x0 N := hlt.trans_le (xmA_mono h0 (le_max_left (k + 1) i))
    have heN := xmStage_mono (S := S) (B := B) (b := b) (m := m) (x0 := x0) h0 ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := xmStage_mono (S := S) (B := B) (b := b) (m := m) (x0 := x0) h0 (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU LEMMA**: `ψ₁(B + ψ₂(b + ω^m·Ω₁)) ≤ sup_n x_n`. -/
theorem xmPlat (h0 : x0 ≤ xmX S B b m x0 1) (hx0 : x0 < Om 1) (hm : ∀ n, m ∈ S.CSet (xmA S B b m x0 n) (xmX S B b m x0 (n + 1))) :
    S.psi (B + S.psi (b + ω ^ m * Om 1) (Om (1 + 1))) (Om 1) ≤ ⨆ n : ℕ, xmX S B b m x0 n := by
  have hbdd : BddAbove (range (xmX S B b m x0)) := ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (xmX_lt hx0 n).le⟩
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun y hy hy1 => ?_
  obtain ⟨n, hn⟩ := xmKey hb hm2 h0 hx0 hm y hy
  rw [xmX_succ] at hn
  have h := lt_psi_of_mem Low.InR_Om_one hn hy1
  rw [← xmX_succ] at h
  exact h.trans_le (le_ciSup hbdd (n + 1))

end Gen

/-- **Domination**: a sequence `y` with `ψ₁(B + ψ₂(b + ω^m·y_n)) ≤ y_{n+1}` is above `x`. -/
theorem xmX_le {B b m x0 : Ordinal.{0}} {y : ℕ → Ordinal.{0}} (h0 : x0 ≤ y 0)
    (hy : ∀ n, S.psi (B + S.psi (b + ω ^ m * y n) (Om (1 + 1))) (Om 1) ≤ y (n + 1)) :
    ∀ n, xmX S B b m x0 n ≤ y n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [xmX_succ]
    unfold xmA
    exact (psi_mono Low.InR_Om_one (add_le_add le_rfl
      (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (mul_le_mul_right ih _))).1)).1.trans (hy n)

end Googology.Trans.PoR.InaccPsi.R2.Xm

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmR3
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmR2
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmKey
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmPlat
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmX_le
