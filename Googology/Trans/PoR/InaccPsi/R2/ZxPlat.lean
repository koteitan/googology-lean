import Googology.Trans.PoR.InaccPsi.R2.XmPlat

/-!
# Zx: THE PLATEAU LEMMA FOR ANY ARGUMENT `L`: `ψ₁(B + ψ₂(L(Ω₁))) ≤ sup_n x_n`

`x_0` given (`x_0 ≤ x_1`, `x_0 < Ω₁`), `x_{n+1} = ψ₁(a_n)`, `a_n = B + ψ₂(L(x_n))` (`zxX`, `zxA`), `L` monotone.
`Xm.xmPlat` is the case `L(x) = b + ω^m·x`, `Yy.yyPlat` the case `L(x) = b + Ω^{K+x}`.  Two properties of `L`
replace the computations there:

* the GAP `ZxGap L C x` (a member `e ∈ C` below `L(Ω₁)` is below `L(q + 1)` for some `q < x`), asked at every stage
  `C = Cl(a_n, x_{n+1})`, `x = x_{n+1}`;
* the STEP `ZxStep S L` (`ψ₂(L(q + 1)) < ψ₂(L(x))` for `q < x`, `x` strongly critical and countable).

* `zxR2` (**a member of a stage below `ψ₂(L(Ω₁))` is below `ψ₂(L(x_{n+1}))`**), `zxKey`, `zxPlat` (**THE PLATEAU**),
  `zxX_le` (domination);
* `zxGap_mul` (**the gap of `b + ω^m·x`** at `Cl(a, ψ₁ a)` once `m` is a member), `zxGap_opow` (**the gap passes to
  `b + ω^{L(x)}`**: the logarithm of a member is a member), so every tower `b₁ + ω^{b₂ + ω^{… + ω^m·x}}` has the gap;
* `zxStep_tower` (**the step of `b + ω^{c + ω^m·x}`** for a normal `b` and `c`, `m` in the closures over `b + ω^c`),
  `zxPlat_tower` (**THE PLATEAU OF THE TWO-LEVEL TOWER**: `ψ₁(B + ψ₂(b + ω^{c + ω^m·Ω₁})) ≤ sup_n x_n`).  The jump
  `X → X + W^{h+1}` of the top law reads `T(β + W^{X + W^h·u}) = Tβ + ω^{Ω₁·TX + ω^{Ω₁ + Ω₁·Th}·Θu}`, a two-level tower.

No new axiom.  New definitions: `zxX`, `zxA` (the iterates), `ZxGap`, `ZxStep` (the two properties).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Uu

variable {S : InaccSeq.{0}}

/-- The iterates `x_0` (a start), `x_{n+1} = ψ₁(B + ψ₂(L(x_n)))`. -/
noncomputable def zxX (S : InaccSeq.{0}) (B : Ordinal.{0}) (L : Ordinal.{0} → Ordinal.{0}) (x0 : Ordinal.{0}) :
    ℕ → Ordinal.{0}
  | 0 => x0
  | n + 1 => S.psi (B + S.psi (L (zxX S B L x0 n)) (Om (1 + 1))) (Om 1)

/-- The stage arguments `a_n = B + ψ₂(L(x_n))`. -/
noncomputable def zxA (S : InaccSeq.{0}) (B : Ordinal.{0}) (L : Ordinal.{0} → Ordinal.{0}) (x0 : Ordinal.{0})
    (n : ℕ) : Ordinal.{0} :=
  B + S.psi (L (zxX S B L x0 n)) (Om (1 + 1))

/-- **The gap of `L` on `C` with bound `x`.** -/
def ZxGap (L : Ordinal.{0} → Ordinal.{0}) (C : Set Ordinal.{0}) (x : Ordinal.{0}) : Prop :=
  ∀ e ∈ C, e < L (Om 1) → ∃ q, q < x ∧ e < L (q + 1)

/-- **The step of `L`**: `ψ₂(L(q + 1)) < ψ₂(L(x))` for `q < x`, `x` strongly critical and countable. -/
def ZxStep (S : InaccSeq.{0}) (L : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ q x : Ordinal.{0}, SC x → x < Om 1 → q < x → S.psi (L (q + 1)) (Om (1 + 1)) < S.psi (L x) (Om (1 + 1))

section It

variable {B x0 : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}}

theorem zxX_zero : zxX S B L x0 0 = x0 := rfl

theorem zxX_succ (n : ℕ) : zxX S B L x0 (n + 1) = S.psi (zxA S B L x0 n) (Om 1) := rfl

theorem zxX_lt (hx0 : x0 < Om 1) (n : ℕ) : zxX S B L x0 n < Om 1 := by
  cases n with
  | zero => exact hx0
  | succ n => rw [zxX_succ]; exact psi_lt Low.InR_Om_one _

theorem zxX_SC (n : ℕ) : SC (zxX S B L x0 (n + 1)) := by rw [zxX_succ]; exact SC_psi Low.InR_Om_one _

variable (hL : Monotone L)
include hL

theorem zxX_mono (h0 : x0 ≤ zxX S B L x0 1) : ∀ n : ℕ, zxX S B L x0 n ≤ zxX S B L x0 (n + 1) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [zxX_succ, zxX_succ]
    unfold zxA
    exact (psi_mono Low.InR_Om_one (add_le_add le_rfl (psi_mono (InR_Om_succ 1) (hL ih)).1)).1

theorem zxX_monotone (h0 : x0 ≤ zxX S B L x0 1) : Monotone (zxX S B L x0) :=
  monotone_nat_of_le_succ (zxX_mono hL h0)

theorem zxA_mono (h0 : x0 ≤ zxX S B L x0 1) {i j : ℕ} (h : i ≤ j) : zxA S B L x0 i ≤ zxA S B L x0 j := by
  unfold zxA
  exact add_le_add le_rfl (psi_mono (InR_Om_succ 1) (hL (zxX_monotone hL h0 h))).1

theorem zxStage_mono (h0 : x0 ≤ zxX S B L x0 1) {i j : ℕ} (h : i ≤ j) :
    S.CSet (zxA S B L x0 i) (zxX S B L x0 (i + 1)) ⊆ S.CSet (zxA S B L x0 j) (zxX S B L x0 (j + 1)) := by
  rw [zxX_succ, zxX_succ]; exact (psi_mono Low.InR_Om_one (zxA_mono hL h0 h)).2

end It

/-- **A member of a stage below `ψ₂(L(Ω₁))` is below `ψ₂(L(x_{n+1}))`.** -/
theorem zxR2 {B x0 : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (n : ℕ)
    (hg : ZxGap L (S.CSet (zxA S B L x0 n) (zxX S B L x0 (n + 1))) (zxX S B L x0 (n + 1))) (hs : ZxStep S L) :
    ∀ y ∈ S.CSet (zxA S B L x0 n) (zxX S B L x0 (n + 1)),
      y < S.psi (L (Om 1)) (Om (1 + 1)) → y < S.psi (L (zxX S B L x0 (n + 1))) (Om (1 + 1)) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hs1 : (1 : Ordinal.{0}) + 1 < Om 1 := lt_of_lt_of_le (by
    rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2)
    (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le
  have hx := zxX_SC (S := S) (B := B) (L := L) (x0 := x0) n
  have hx1 : zxX S B L x0 (n + 1) < Om 1 := by rw [zxX_succ]; exact psi_lt Low.InR_Om_one _
  set P := S.psi (L (zxX S B L x0 (n + 1))) (Om (1 + 1)) with hP
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
      have he : e.1 < L (Om 1) := by
        by_contra hc; push Not at hc
        exact absurd ((psi_mono hκ2 hc).1.trans_lt h) (lt_irrefl _)
      obtain ⟨q, hq, hqe⟩ := hg _ heC he
      exact (psi_mono hκ2 hqe.le).1.trans_lt (hs q _ hx hx1 hq)
    · exact absurd ((uuInR_gt hs1 hπ hgt e.1).trans_lt h) (not_lt.2 (psi_lt hκ2 _).le)

section Plat

variable {B x0 : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (hL : Monotone L) (h0 : x0 ≤ zxX S B L x0 1)
  (hx0 : x0 < Om 1)
  (hg : ∀ n, ZxGap L (S.CSet (zxA S B L x0 n) (zxX S B L x0 (n + 1))) (zxX S B L x0 (n + 1)))
  (hs : ZxStep S L)

include hL h0 hx0 hg hs

/-- **Every member of `Cl(B + ψ₂(L(Ω₁)), sup_n x_n)` lies in a stage.** -/
theorem zxKey : ∀ y ∈ S.CSet (B + S.psi (L (Om 1)) (Om (1 + 1))) (⨆ n : ℕ, zxX S B L x0 n),
    ∃ n, y ∈ S.CSet (zxA S B L x0 n) (zxX S B L x0 (n + 1)) := by
  have hbdd : BddAbove (range (zxX S B L x0)) := ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (zxX_lt hx0 n).le⟩
  intro y hy
  induction hy with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, CSet.of_lt (hn.trans_le (zxX_mono hL h0 n))⟩
  | zero => exact ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact ⟨0, Clos.inacc n⟩
  | inaccW => exact ⟨0, Clos.inaccW⟩
  | add _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, CSet.add_mem (zxStage_mono hL h0 (le_max_left i j) hi)
      (zxStage_mono hL h0 (le_max_right i j) hj)⟩
  | phi _ _ ihp ihq =>
    obtain ⟨i, hi⟩ := ihp
    obtain ⟨j, hj⟩ := ihq
    exact ⟨max i j, Clos.phi (zxStage_mono hL h0 (le_max_left i j) hi) (zxStage_mono hL h0 (le_max_right i j) hj)⟩
  | om _ ih =>
    obtain ⟨i, hi⟩ := ih
    exact ⟨i, CSet.Om_mem hi⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨i, hi⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    have hlt : e.1 < zxA S B L x0 (k + 1) := by
      unfold zxA
      rcases lt_or_ge e.1 B with h1 | h1
      · exact h1.trans_le le_self_add
      · have hw : e.1 - B < S.psi (L (Om 1)) (Om (1 + 1)) := Ry.rySub_lt h1 e.2
        have h3 := zxR2 k (hg k) hs _ (Ta.taSub_mem e.1 hk B) hw
        have ee : e.1 = B + (e.1 - B) := (Ordinal.add_sub_cancel_of_le h1).symm
        rw [ee]; exact (add_lt_add_iff_left B).2 h3
    set N := max (k + 1) i with hN
    have hltN : e.1 < zxA S B L x0 N := hlt.trans_le (zxA_mono hL h0 (le_max_left (k + 1) i))
    have heN := zxStage_mono (S := S) (B := B) (L := L) (x0 := x0) hL h0
      ((Nat.le_succ k).trans (le_max_left (k + 1) i)) hk
    have hπN := zxStage_mono (S := S) (B := B) (L := L) (x0 := x0) hL h0 (le_max_right (k + 1) i) hi
    exact ⟨N, Clos.coll (e := ⟨e.1, hltN⟩) hπ hπN heN⟩

/-- **THE PLATEAU LEMMA FOR ANY ARGUMENT `L`**: `ψ₁(B + ψ₂(L(Ω₁))) ≤ sup_n x_n`. -/
theorem zxPlat : S.psi (B + S.psi (L (Om 1)) (Om (1 + 1))) (Om 1) ≤ ⨆ n : ℕ, zxX S B L x0 n := by
  have hbdd : BddAbove (range (zxX S B L x0)) := ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (zxX_lt hx0 n).le⟩
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun y hy hy1 => ?_
  obtain ⟨n, hn⟩ := zxKey hL h0 hx0 hg hs y hy
  rw [zxX_succ] at hn
  have h := lt_psi_of_mem Low.InR_Om_one hn hy1
  rw [← zxX_succ] at h
  exact h.trans_le (le_ciSup hbdd (n + 1))

end Plat

/-- **Domination**: a sequence `y` with `ψ₁(B + ψ₂(L(y_n))) ≤ y_{n+1}` is above `x`. -/
theorem zxX_le {B x0 : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}} (hL : Monotone L) {y : ℕ → Ordinal.{0}}
    (h0 : x0 ≤ y 0) (hy : ∀ n, S.psi (B + S.psi (L (y n)) (Om (1 + 1))) (Om 1) ≤ y (n + 1)) :
    ∀ n, zxX S B L x0 n ≤ y n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [zxX_succ]
    unfold zxA
    exact (psi_mono Low.InR_Om_one (add_le_add le_rfl (psi_mono (InR_Om_succ 1) (hL ih)).1)).1.trans (hy n)

/-! ## The gap and the step of the towers -/

/-- **The gap of `b + ω^m·x`** at `Cl(a, ψ₁ a)` once `m` is a member. -/
theorem zxGap_mul {a b m : Ordinal.{0}} (hm : m ∈ S.CSet a (S.psi a (Om 1))) :
    ZxGap (fun x => b + ω ^ m * x) (S.CSet a (S.psi a (Om 1))) (S.psi a (Om 1)) := by
  intro e he hlt
  have hM0 : ω ^ m ≠ 0 := (opow_pos _ omega0_pos).ne'
  rcases lt_or_ge e b with h1 | h1
  · refine ⟨0, (SC_psi Low.InR_Om_one a).1, ?_⟩
    show e < b + ω ^ m * (0 + 1)
    rw [zero_add, mul_one]; exact h1.trans_le le_self_add
  · have hsub : e - b < ω ^ m * Om 1 := Ry.rySub_lt h1 hlt
    set q := (e - b) / ω ^ m with hq
    have hqC : q ∈ S.CSet a (S.psi a (Om 1)) := (Vh.vhC_div _ (Ta.taSub_mem e he b) m).2.2 hm
    have hq1 : q < Om 1 := (Ordinal.lt_mul_iff_div_lt hM0).1 hsub
    refine ⟨q, lt_psi_of_mem Low.InR_Om_one hqC hq1, ?_⟩
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    show e < b + ω ^ m * (q + 1)
    rw [e1]
    have := Ordinal.lt_mul_succ_div (e - b) hM0
    rw [Order.succ_eq_add_one] at this
    exact (add_lt_add_iff_left b).2 this

/-- **The gap passes to `b + ω^{L(x)}`** (the logarithm of a member is a member). -/
theorem zxGap_opow {a b : Ordinal.{0}} {L : Ordinal.{0} → Ordinal.{0}}
    (hg : ZxGap L (S.CSet a (S.psi a (Om 1))) (S.psi a (Om 1))) :
    ZxGap (fun x => b + ω ^ L x) (S.CSet a (S.psi a (Om 1))) (S.psi a (Om 1)) := by
  intro e he hlt
  have hpos : (0 : Ordinal.{0}) < S.psi a (Om 1) := (SC_psi Low.InR_Om_one a).1
  rcases lt_or_ge e b with h1 | h1
  · exact ⟨0, hpos, h1.trans_le le_self_add⟩
  · have hd : e - b < ω ^ L (Om 1) := Ry.rySub_lt h1 hlt
    have hdC : e - b ∈ S.CSet a (S.psi a (Om 1)) := Ta.taSub_mem e he b
    have e1 : e = b + (e - b) := (Ordinal.add_sub_cancel_of_le h1).symm
    rcases eq_or_ne (e - b) 0 with h0 | h0
    · refine ⟨0, hpos, ?_⟩
      show e < b + ω ^ L (0 + 1)
      rw [e1, h0, add_zero]
      exact lt_add_of_pos_right b (opow_pos _ omega0_pos)
    · have hlog : log ω (e - b) < L (Om 1) := (lt_opow_iff_log_lt one_lt_omega0 h0).1 hd
      obtain ⟨q, hq, hqe⟩ := hg _ (Le.leLog_mem hdC) hlog
      refine ⟨q, hq, ?_⟩
      show e < b + ω ^ L (q + 1)
      rw [e1]
      exact (add_lt_add_iff_left b).2 ((lt_opow_iff_log_lt one_lt_omega0 h0).2 hqe)

/-- The two-level tower is monotone. -/
theorem zxTower_mono (b c m : Ordinal.{0}) : Monotone fun x : Ordinal.{0} => b + ω ^ (c + ω ^ m * x) :=
  fun _ _ h => add_le_add le_rfl (opow_le_opow_right omega0_pos (add_le_add le_rfl (mul_le_mul_right h _)))

/-- **The step of the two-level tower `b + ω^{c + ω^m·x}`** for a normal `b` and `c`, `m` in the closures
`Cl(a, ψ₂ a)` over `b + ω^c`. -/
theorem zxStep_tower {b c m : Ordinal.{0}} (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1))))
    (hc : ∀ a, b + ω ^ c ≤ a → c ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hm : ∀ a, b + ω ^ c ≤ a → m ∈ S.CSet a (S.psi a (Om (1 + 1)))) :
    ZxStep S fun x => b + ω ^ (c + ω ^ m * x) := by
  intro q x hx hx1 hq
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hxε : ω ^ x = x := gg_SC_eps hx
  have hq1x : q + 1 < x := hx.isSuccLimit.add_one_lt hq
  set Lx := b + ω ^ (c + ω ^ m * x) with hLx
  set E := b + ω ^ (c + ω ^ (m + (q + 1))) with hE
  have hle : b + ω ^ (c + ω ^ m * (q + 1)) ≤ E := by
    rw [hE, opow_add ω m (q + 1)]
    exact add_le_add le_rfl (opow_le_opow_right omega0_pos (add_le_add le_rfl
      (mul_le_mul_right (Ordinal.right_le_opow _ one_lt_omega0) _)))
  have hEx : E < Lx := by
    rw [hE, hLx]
    conv_rhs => rw [← hxε, ← opow_add]
    exact (add_lt_add_iff_left b).2 ((opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left c).2
      ((opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left m).2 hq1x))))
  have hcx : b + ω ^ c ≤ Lx :=
    add_le_add le_rfl (opow_le_opow_right omega0_pos le_self_add)
  have hEC : E ∈ S.CSet Lx (S.psi Lx (Om (1 + 1))) := by
    refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hb) ?_
    have h1 : m + (q + 1) ∈ S.CSet Lx (S.psi Lx (Om (1 + 1))) :=
      CSet.add_mem (hm _ hcx) (CSet.of_lt ((hq1x.trans hx1).trans (psiS_bounds (S := S) _ 1).1))
    have h2 := CSet.phi_mem (CSet.zero_mem (S := S) _ _) h1
    rw [veblen_zero_apply] at h2
    have h3 := CSet.phi_mem (CSet.zero_mem (S := S) _ _) (CSet.add_mem (hc _ hcx) h2)
    rwa [veblen_zero_apply] at h3
  exact (psi_mono hκ2 hle).1.trans_lt (psi_lt_psi_of_mem hκ2 hEx hEC)

/-- **THE PLATEAU OF THE TWO-LEVEL TOWER**: `ψ₁(B + ψ₂(b + ω^{c + ω^m·Ω₁})) ≤ sup_n x_n`, `x_{n+1} =
ψ₁(B + ψ₂(b + ω^{c + ω^m·x_n}))`, once `m` is a member of every stage. -/
theorem zxPlat_tower {B b c m x0 : Ordinal.{0}} (hb : b ∈ S.CSet b (S.psi b (Om (1 + 1))))
    (hc : ∀ a, b + ω ^ c ≤ a → c ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hm2 : ∀ a, b + ω ^ c ≤ a → m ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (h0 : x0 ≤ zxX S B (fun x => b + ω ^ (c + ω ^ m * x)) x0 1) (hx0 : x0 < Om 1)
    (hm : ∀ n, m ∈ S.CSet (zxA S B (fun x => b + ω ^ (c + ω ^ m * x)) x0 n)
      (zxX S B (fun x => b + ω ^ (c + ω ^ m * x)) x0 (n + 1))) :
    S.psi (B + S.psi (b + ω ^ (c + ω ^ m * Om 1)) (Om (1 + 1))) (Om 1) ≤
      ⨆ n : ℕ, zxX S B (fun x => b + ω ^ (c + ω ^ m * x)) x0 n := by
  refine zxPlat (L := fun x => b + ω ^ (c + ω ^ m * x)) (zxTower_mono b c m) h0 hx0 (fun n => ?_)
    (zxStep_tower hb hc hm2)
  have hmn := hm n
  rw [zxX_succ] at hmn ⊢
  exact zxGap_opow (L := fun x => c + ω ^ m * x) (zxGap_mul hmn)

end Googology.Trans.PoR.InaccPsi.R2.Zx

#print axioms Googology.Trans.PoR.InaccPsi.R2.Zx.zxPlat
#print axioms Googology.Trans.PoR.InaccPsi.R2.Zx.zxPlat_tower
