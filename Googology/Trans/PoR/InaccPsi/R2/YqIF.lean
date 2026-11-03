import Googology.Trans.PoR.InaccPsi.R2.YgUc
import Googology.Trans.PoR.InaccPsi.R2.VjD
import Googology.Trans.PoR.InaccPsi.R2.VdDat
import Googology.Trans.PoR.InaccPsi.R2.UiArgs

/-!
# `YbIF` on the notation: every level `M < θ` of the notation with datum below `q` is inacc-free

`θ = ConjT.th S = ψ_{Ω₂}(Ω_ω)`, `d(x) = Vd.vdD S 0 x` (the `K⁽⁰⁾`-datum), `nf = Bc.bcNf S`, `uiDatT` the largest
countable leaf of a term (subscripts included), `uiArgsT A t` (every collapse argument of an uncountable subterm is
below `A`), `YgK S q` the inacc-free closure (`Yg.YgK`).

The inaccessibles are eliminated along the normal form, not along a `K⁽⁰⁾`-derivation: on the normal form of an
ordinal below `θ` every collapse argument is below `Ω_ω` (`Ui.ui_args_th`), so an uncountable subterm whose value is
below `Ω_ω` contains no `I_n` (an `I_n`, `I_ω`, a `ψ_{I_n}`-value and a `ψ_{Ω_{s+1}}`-value with `s ≥ ω` are all
`≥ Ω_ω`), and the countable subterms are leaves below `q`:

* `yqOmW_lt_psiI` (`Ω_ω < ψ_{I_n}(a)`), `yqOmW_le_psiS` (`s ≥ ω ⇒ Ω_ω ≤ ψ_{Ω_{s+1}}(a)`), `yqOmW_le_I`;
* `yqTermK` (**a term `t` with `uiDatT t < q`, `uiArgsT Ω_ω t` and `val t < Ω_ω` has `val t ∈ YgK S q`**);
* `yqNotK` (**`z` of the notation, `z < θ`, `d(z) < q` (`q` strongly critical, `q ≤ Ω₁`) ⇒ `z ∈ YgK S q`**);
* `yqNot_of_dat` (**`d(z) < ψ_{Ω₁}(A)` ⇒ `z` is of the notation**);
* `yqIF_le` (**`YgIFTh` for every `q ≤ ψ_{Ω₁}(A)`**, any `A`), `yqIF_dat` (**for every level whose datum is below
  some `ψ_{Ω₁}(A)`**);
* `YqIFHuge S` (**the part of `YgIFTh` left**: the levels whose datum is above every value of `ψ_{Ω₁}`, i.e. above
  the countable part of the notation), `yqIF_of_huge` (**`YqIFHuge S ⇒ YgIFTh S`**), `yqHuge_iff`
  (**`YgIFTh S ↔ YqIFHuge S`**).

No new axiom.  New definitions: `YqIFHuge` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Yg
  Googology.Trans.PoR.InaccPsi.R2.Ui

variable {S : InaccSeq.{0}}

/-! ## Values that are at least `Ω_ω` -/

theorem yq_omega_lt_I (n : ℕ) : (ω : Ordinal.{0}) < S.I n := by
  rw [S.I_eq_ord n, ← Cardinal.ord_aleph0]
  exact Cardinal.ord_lt_ord.2 (S.uncountable n)

theorem yqOmW_le_I (n : ℕ) : Om (ω : Ordinal.{0}) ≤ S.I n := by
  have h := Om_lt_Om.2 (yq_omega_lt_I (S := S) n)
  rw [S.fix n] at h; exact h.le

theorem yqOmW_le_Iw : Om (ω : Ordinal.{0}) ≤ S.Iw := (yqOmW_le_I 0).trans (S.I_le_Iw 0)

/-- `Ω_ω < ψ_{I_n}(a)`. -/
theorem yqOmW_lt_psiI (a : Ordinal.{0}) (n : ℕ) : Om (ω : Ordinal.{0}) < S.psi a (S.I n) := by
  have h1 : (ω : Ordinal.{0}) < S.psi a (S.I n) :=
    (omega0_lt_Om one_ne_zero).trans (Om_one_lt_psiI a n)
  have h := Om_lt_Om.2 h1
  rwa [Om_psiI] at h

/-- `ψ_{Ω_{s+1}}(a) < Ω_ω ⇒ s < ω`. -/
theorem yq_sub_lt (a s : Ordinal.{0}) (h : S.psi a (Om (s + 1)) < Om ω) : s < ω :=
  (Om_psiS_lt_Om a s).1 h

/-! ## The term induction -/

theorem yq_one_K {q : Ordinal.{0}} : YgK S q 1 := by
  have h := YgK.phi (S := S) (q := q) YgK.zero YgK.zero
  rwa [veblen_zero_apply, opow_zero] at h

/-- **A term with countable leaves below `q`, collapse arguments below `Ω_ω` and value below `Ω_ω` has its value in
the inacc-free closure.** -/
theorem yqTermK {q : Ordinal.{0}} :
    ∀ t : Term, uiDatT S t < q → uiArgsT S (Om ω) t → val S t < Om ω → YgK S q (val S t) := by
  intro t
  induction t with
  | zero => intro _ _ _; exact YgK.zero
  | inacc n => intro _ _ hv; exact absurd (yqOmW_le_I (S := S) n) (not_le.2 hv)
  | inaccW => intro _ _ hv; exact absurd (yqOmW_le_Iw (S := S)) (not_le.2 hv)
  | add a b iha ihb =>
    intro hd ha hv
    by_cases h : val S (add a b) < Om 1
    · rw [uiDatT_small h] at hd; exact YgK.small hd
    simp only [uiDatT, if_neg h] at hd
    have ha' := ha.resolve_left h
    have hv' : val S a + val S b < Om ω := hv
    exact YgK.add (iha (lt_of_le_of_lt (le_max_left _ _) hd) ha'.1 (le_self_add.trans_lt hv'))
      (ihb (lt_of_le_of_lt (le_max_right _ _) hd) ha'.2 (le_add_self.trans_lt hv'))
  | phi a b iha ihb =>
    intro hd ha hv
    by_cases h : val S (phi a b) < Om 1
    · rw [uiDatT_small h] at hd; exact YgK.small hd
    simp only [uiDatT, if_neg h] at hd
    have ha' := ha.resolve_left h
    have hv' : veblen (val S a) (val S b) < Om ω := hv
    exact YgK.phi (iha (lt_of_le_of_lt (le_max_left _ _) hd) ha'.1 ((left_le_veblen _ _).trans_lt hv'))
      (ihb (lt_of_le_of_lt (le_max_right _ _) hd) ha'.2 ((right_le_veblen _ _).trans_lt hv'))
  | om a iha =>
    intro hd ha hv
    by_cases h : val S (om a) < Om 1
    · rw [uiDatT_small h] at hd; exact YgK.small hd
    simp only [uiDatT, if_neg h] at hd
    have hv' : Om (val S a) < Om ω := hv
    exact YgK.om (iha hd (ha.resolve_left h) ((le_Om _).trans_lt hv'))
  | psiS s a ihs iha =>
    intro hd ha hv
    by_cases h : val S (psiS s a) < Om 1
    · rw [uiDatT_small h] at hd; exact YgK.small hd
    simp only [uiDatT, if_neg h] at hd
    obtain ⟨hlt, has, haa⟩ := ha.resolve_left h
    have hv' : S.psi (val S a) (Om (val S s + 1)) < Om ω := hv
    have hsω := yq_sub_lt (val S a) (val S s) hv'
    have hs0 : val S s ≠ 0 := by
      intro h0
      apply h
      show S.psi (val S a) (Om (val S s + 1)) < Om 1
      rw [h0, zero_add]; exact psi_lt Low.InR_Om_one _
    have hπ : Om (val S s + 1) ≠ Om 1 := by
      intro e
      have e' : val S s + 1 = 1 := Om_inj.1 e
      apply hs0
      have : Order.succ (val S s) = Order.succ 0 := by
        rw [Order.succ_eq_add_one, Order.succ_eq_add_one, zero_add, e']
      exact Order.succ_injective this
    have hsK := ihs (lt_of_le_of_lt (le_max_left _ _) hd) has
      (hsω.trans_le (le_Om _))
    have haK := iha (lt_of_le_of_lt (le_max_right _ _) hd) haa hlt
    exact YgK.coll (InR_Om_succ _) hπ (YgK.om (YgK.add hsK yq_one_K)) haK
  | psiI n a _ =>
    intro _ _ hv
    exact absurd (yqOmW_lt_psiI (S := S) (val S a) n) (not_lt.2 hv.le)

/-! ## The notation below `θ` -/

theorem yq_th_lt_OmW : ConjT.th S < Om ω := by
  have h1 := Vj.vj_th_lt_Om2 (S := S)
  have h2 : (OmTwo : Ordinal.{0}) = Om (1 + 1) := Uf.uf_Om2
  rw [h2] at h1
  refine h1.trans (Om_lt_Om.2 ?_)
  exact (lt_add_one (1 + 1 : Ordinal.{0})).trans yg_fin_lt_omega

/-- **On the notation below `θ`: `d(z) < q ⇒ z ∈ YgK S q`** (`q` strongly critical, `q ≤ Ω₁`). -/
theorem yqNotK {z q : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hzθ : z < ConjT.th S) (hq : SC q)
    (hq1 : q ≤ Om 1) (hd : Vd.vdD S 0 z < q) : YgK S q z := by
  obtain ⟨-, hv⟩ := Bc.bcNf_spec S hz
  have hd' : uiDat S z < q := (Vd.vd_dat_ui hz hq hq1).1 hd
  have ha : uiArgs S (Om ω) z := ui_args_th z hz hzθ
  have h := yqTermK (S := S) (q := q) (Bc.bcNf S z) hd' ha (by rw [hv]; exact hzθ.trans yq_th_lt_OmW)
  rwa [hv] at h

/-- **A datum below some `ψ_{Ω₁}(A)` gives an ordinal of the notation.** -/
theorem yqNot_of_dat {z A : Ordinal.{0}} (hd : Vd.vdD S 0 z < S.psi A (Om 1)) : z ∈ ⋃ a, S.CSet a 0 := by
  have hq : SC (S.psi A (Om 1)) := SC_psi Low.InR_Om_one A
  exact Vj.vjK_notA le_rfl ((Vg.vg_code_iffK hq).1 hd)

/-! ## `YgIFTh` up to the levels beyond the notation -/

/-- **`YgIFTh` at every level whose datum is below some value of `ψ_{Ω₁}`.** -/
theorem yqIF_dat {M q A : Ordinal.{0}} (hMθ : M < ConjT.th S) (hq : SC q) (hq1 : q ≤ Om1)
    (hd : Vd.vdD S 0 M < q) (hA : Vd.vdD S 0 M < S.psi A (Om 1)) : Yb.YbK S q M := by
  have hq1' : q ≤ Om 1 := by rw [← Tw.tw_Om1_eq]; exact hq1
  exact (yqNotK (yqNot_of_dat hA) hMθ hq hq1' hd).toYb hq.1

/-- **`YgIFTh` for every threshold `q ≤ ψ_{Ω₁}(A)`.** -/
theorem yqIF_le {M q A : Ordinal.{0}} (hMθ : M < ConjT.th S) (hq : SC q) (hq1 : q ≤ Om1)
    (hqA : q ≤ S.psi A (Om 1)) (hd : Vd.vdD S 0 M < q) : Yb.YbK S q M :=
  yqIF_dat hMθ hq hq1 hd (hd.trans_le hqA)

/-- **The part of `YgIFTh` left**: the levels `B₂ ≤ M < θ` whose datum is above every value of `ψ_{Ω₁}` (above the
countable part of the notation). -/
def YqIFHuge (S : InaccSeq.{0}) : Prop :=
  ∀ M q : Ordinal.{0}, Uc.ucB ≤ M → M < ConjT.th S → SC q → q ≤ Om1 → Vd.vdD S 0 M < q →
    (∀ A, S.psi A (Om 1) ≤ Vd.vdD S 0 M) → Yb.YbK S q M

/-- **`YqIFHuge S ⇒ YgIFTh S`.** -/
theorem yqIF_of_huge (H : YqIFHuge S) : YgIFTh S := by
  intro M q hB hMθ hq hq1 hd
  by_cases hA : ∃ A, Vd.vdD S 0 M < S.psi A (Om 1)
  · obtain ⟨A, hA⟩ := hA; exact yqIF_dat hMθ hq hq1 hd hA
  · push Not at hA; exact H M q hB hMθ hq hq1 hd hA

/-- **`YgIFTh S ↔ YqIFHuge S`.** -/
theorem yqHuge_iff : YgIFTh S ↔ YqIFHuge S :=
  ⟨fun H M q hB hMθ hq hq1 hd _ => H M q hB hMθ hq hq1 hd, yqIF_of_huge⟩

/-! ## `YbIF` on the notation range and the covering lemma there -/

/-- **`YbIF` below a value `ψ_{Ω₁}(A)`**: the thresholds `q ≤ ψ_{Ω₁}(A)`. -/
def YqIFN (S : InaccSeq.{0}) (A : Ordinal.{0}) : Prop :=
  ∀ M q : Ordinal.{0}, Om1 ≤ M → M < ConjT.th S → SC q → q ≤ Om1 → q ≤ S.psi A (Om 1) →
    (M < Uc.ucB → Uc.ucDat M < q) → (Uc.ucB ≤ M → Vd.vdD S 0 M < q) → Yb.YbK S q M

/-- **`YbIF` holds on the notation range, with no hypothesis.** -/
theorem yqIFN (A : Ordinal.{0}) : YqIFN S A := by
  intro M q _ hMθ hq hq1 hqA h1 h2
  rcases lt_or_ge M Uc.ucB with hMB | hMB
  · exact ygIF_lowB hq hq1 hMB (h1 hMB)
  · exact yqIF_le hMθ hq hq1 hqA (h2 hMB)

end Googology.Trans.PoR.InaccPsi.R2.Yq
