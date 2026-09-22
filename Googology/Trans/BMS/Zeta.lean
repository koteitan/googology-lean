import Googology.Trans.BMS.EpsBig

/-!
# `val` is onto the ordinals below `ζ₀`

`EpsBig.lean` stops at `ε_{ε₀}`, because `exists_argTerm` reads the exponents
of `μ` off Cantor normal form and asks for all-nil terms for them.  Above `ε₀`
an exponent can be an ε-number, whose term is not all-nil and is built at a
level above the exponent's own index.  So the argument terms and the values
have to be built by **one** induction rather than one after the other, and
that is what this file does.

`exists_arg_and_OT` carries both at level `δ`: a standard form naming
`Ω·(1+δ)`, and a standard form for every ordinal below `ε_{δ+1}`.  The
invariant is the ordinal one — `G_0` of the term stays below `Ω·(1+δ)` plus
its value — which `OT_of_mem_G` turns back into the term comparison the
standard-form condition asks for.

The index of an ε-number comes from `Ord.exists_eps_index`, and
`Ord.eps_index_lt` says it is smaller, which is what makes the induction go
through at an exponent that is its own logarithm.
-/

namespace Googology.Trans.BMS

open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

theorem one_lt_Omega_one : (1 : Ordinal) < Ord.Omega 1 := by
  rw [Ord.Omega_of_ne_zero one_ne_zero]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)

theorem one_add_succ_le {e δ : Ordinal} (h : e < δ) (hω : (ω : Ordinal) ≤ δ) :
    1 + e + 1 ≤ δ := by
  rcases lt_or_ge e (ω : Ordinal) with hf | hi
  · refine le_trans (le_of_lt ?_) hω
    exact Ordinal.isPrincipal_add_omega0
      (Ordinal.isPrincipal_add_omega0 Ordinal.one_lt_omega0 hf) Ordinal.one_lt_omega0
  · rw [Ordinal.one_add_of_omega0_le hi, ← Order.succ_eq_add_one]
    exact Order.succ_le_of_lt h

/-- `Ω·(1+γ) + c < Ω·δ` when `1+γ+1 ≤ δ` and `c` is countable. -/
theorem Omega_mul_add_lt {γ δ c : Ordinal} (hγ : 1 + γ + 1 ≤ δ) (hc : c < Ord.Omega 1) :
    Ord.Omega 1 * (1 + γ) + c < Ord.Omega 1 * δ := by
  refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr hc) ?_
  rw [← mul_add_one]
  exact mul_le_mul_right hγ _

theorem term_lt_of_val_lt {X y : Term} {x : Term} (hX : OT X) (hy : OT y)
    (hx : x ∈ G nil X) (h : val x < val y) : x < y :=
  lt_of_val_lt (OT_of_mem_G nil X hX x hx) hy h

/-- **The argument term and the values, at every level below `ζ₀`.** -/
theorem exists_arg_and_OT : ∀ δ : Ordinal.{0}, δ < Ord.zeta0 →
    (∃ W : Term, OT W ∧ val W = Ord.Omega 1 * (1 + δ) ∧ AllBig W ∧
        ∀ x ∈ G nil W, val x < Ord.Omega 1 * (1 + δ)) ∧
      (∀ α : Ordinal.{0}, α < Ord.eps (δ + 1) →
        ∃ X : Term, OT X ∧ val X = α ∧
          ∀ x ∈ G nil X, val x < Ord.Omega 1 * (1 + δ) + α) := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | _ δ IH =>
    intro hδ
    have hδΩ : δ < Ord.Omega 1 := lt_of_lt_of_le hδ Ord.zeta0_le_Omega_one
    have h1δΩ : (1 : Ordinal) + δ < Ord.Omega 1 :=
      Ord.isPrincipal_add_Omega 1 one_lt_Omega_one hδΩ
    have hδ1 : δ + 1 < Ord.zeta0 := Ord.succ_lt_zeta0 hδ
    have hepsΩ : Ord.eps (δ + 1) < Ord.Omega 1 :=
      Ord.eps_lt_Omega_one (lt_of_lt_of_le hδ1 Ord.zeta0_le_Omega_one)
    have hPartA : ∃ W : Term, OT W ∧ val W = Ord.Omega 1 * (1 + δ) ∧ AllBig W ∧
        ∀ x ∈ G nil W, val x < Ord.Omega 1 * (1 + δ) := by
      refine exists_argTerm_gen (1 + δ) h1δΩ (Ord.Omega 1 * (1 + δ)) (le_refl _) ?_
      intro e he
      rcases eq_or_ne e 0 with rfl | he0
      · refine ⟨nil, rfl, rfl, fun x hx => ?_⟩
        rw [G_nil] at hx
        exact absurd hx (by simp)
      · have h1e : (1 : Ordinal) ≤ e := Order.one_le_iff_ne_zero.mpr he0
        have hne : (1 : Ordinal) + δ ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (self_le_add_right _ _))
        have hωle : (ω : Ordinal) ≤ 1 + δ := by
          refine le_trans ?_ (Ordinal.opow_log_le_self (ω : Ordinal) hne)
          conv_lhs => rw [← Ordinal.opow_one (ω : Ordinal)]
          exact Ordinal.opow_le_opow_right omega0_pos (le_trans h1e he)
        have hωδ : (ω : Ordinal) ≤ δ := by
          by_contra hcon
          exact absurd hωle (not_le.mpr
            (Ordinal.isPrincipal_add_omega0 Ordinal.one_lt_omega0 (not_le.mp hcon)))
        have hδeq : (1 : Ordinal) + δ = δ := Ordinal.one_add_of_omega0_le hωδ
        rw [hδeq] at he ⊢
        have heδ : e ≤ δ := le_trans he (Ordinal.log_le_self _ _)
        rcases eq_or_lt_of_le heδ with heq | hlt
        · have hlogδ : Ordinal.log (ω : Ordinal) δ = δ :=
            le_antisymm (Ordinal.log_le_self _ _) (heq ▸ he)
          have hfp : (ω : Ordinal) ^ δ = δ := by
            refine le_antisymm ?_ (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
            conv_lhs => rw [← hlogδ]
            exact Ordinal.opow_log_le_self _ (ne_of_gt (lt_of_lt_of_le omega0_pos hωδ))
          obtain ⟨γ', hγ'⟩ := Ord.exists_eps_index hfp
          have hγ'lt : γ' < δ := by
            rw [← hγ']
            exact Ord.eps_index_lt (by rw [hγ']; exact hδ)
          obtain ⟨-, hval⟩ := IH γ' hγ'lt (_root_.lt_trans hγ'lt hδ)
          obtain ⟨E, hOTE, hvE, hinvE⟩ := hval δ (by rw [← hγ']; exact Ord.eps_strictMono (by simp))
          refine ⟨E, hOTE, by rw [hvE]; exact heq.symm, fun x hx => ?_⟩
          refine _root_.lt_trans (hinvE x hx) ?_
          exact Omega_mul_add_lt (one_add_succ_le hγ'lt hωδ) hδΩ
        · obtain ⟨-, hval⟩ := IH e hlt (_root_.lt_trans hlt hδ)
          obtain ⟨E, hOTE, hvE, hinvE⟩ := hval e
            (lt_of_le_of_lt (Ord.self_le_eps e) (Ord.eps_strictMono (by simp)))
          refine ⟨E, hOTE, hvE, fun x hx => ?_⟩
          refine _root_.lt_trans (hinvE x hx) ?_
          exact Omega_mul_add_lt (one_add_succ_le hlt hωδ) (lt_of_le_of_lt heδ hδΩ)
    refine ⟨hPartA, ?_⟩
    obtain ⟨W, hOTW, hvW, hbigW, hGWval⟩ := hPartA
    have hGW : ∀ x ∈ G nil W, x < W := fun x hx =>
      term_lt_of_val_lt hOTW hOTW hx (by rw [hvW]; exact hGWval x hx)
    intro α
    induction α using WellFoundedLT.induction with
    | _ α IHα =>
      intro hα
      have hαΩ : α < Ord.Omega 1 := _root_.lt_trans hα hepsΩ
      rcases lt_or_ge α (Ord.eps δ) with hsmall | hbig
      · rcases Ordinal.zero_or_succ_or_isSuccLimit δ with rfl | ⟨δ', hδeq⟩ | hlim
        · rw [Ord.eps_zero] at hsmall
          obtain ⟨X, hAX, hDX, hvX⟩ := exists_desc_of_lt_eps0 α hsmall
          refine ⟨X, OT_of_desc X hAX hDX, hvX, fun x hx => ?_⟩
          have hxX : x < X := G_lt_of_desc X hAX hDX x hx
          refine lt_of_lt_of_le ?_ (self_le_add_left _ _)
          rw [← hvX]
          exact val_lt_val (OT_of_mem_G nil X (OT_of_desc X hAX hDX) x hx)
            (OT_of_desc X hAX hDX) hxX
        · subst hδeq
          rw [Order.succ_eq_add_one] at hsmall hδ ⊢
          have hlt' : δ' < δ' + 1 := by simp
          obtain ⟨-, hval⟩ := IH δ' hlt' (_root_.lt_trans hlt' hδ)
          obtain ⟨X, hOTX, hvX, hinv⟩ := hval α hsmall
          refine ⟨X, hOTX, hvX, fun x hx => ?_⟩
          refine lt_of_lt_of_le (hinv x hx) ?_
          exact add_le_add (mul_le_mul_right ((add_le_add_iff_left 1).mpr hlt'.le) _) (le_refl α)
        · haveI : Small.{0} {a : Ordinal.{0} // a < δ} := Ordinal.small_Iio δ
          rw [Ord.eps_limit hlim] at hsmall
          obtain ⟨⟨δ', hδ'⟩, hxδ⟩ := Ordinal.lt_iSup_iff.mp hsmall
          obtain ⟨-, hval⟩ := IH δ' hδ' (_root_.lt_trans hδ' hδ)
          obtain ⟨X, hOTX, hvX, hinv⟩ := hval α
            (lt_of_lt_of_le hxδ (Ord.eps_mono (by simp)))
          refine ⟨X, hOTX, hvX, fun x hx => ?_⟩
          refine lt_of_lt_of_le (hinv x hx) ?_
          exact add_le_add (mul_le_mul_right ((add_le_add_iff_left 1).mpr hδ'.le) _) (le_refl α)
      · have hpsiW : Ord.psi (val W) 0 = Ord.eps δ := by
          rw [hvW]
          exact Ord.psi_Omega_mul_eps hδ
        have hαpos : (0 : Ordinal) < α := lt_of_lt_of_le (Ord.eps_pos δ) hbig
        rcases eq_or_lt_of_le hbig with heq | hlt
        · have hnilB : ∀ x ∈ G nil (nil : Term), x < addT W nil := by
            intro x hx
            rw [G_nil] at hx
            exact absurd hx (by simp)
          have hOTX : OT (psi nil W) := by
            have h := OT_psi_arg hOTW hbigW hGW (B := nil) rfl
              (by rw [val_nil]; exact le_of_lt (Ord.Omega_pos 1)) hnilB
            rwa [addT_nil_right] at h
          have hvX : val (psi nil W) = α := by
            rw [val_psi, val_nil, hpsiW, heq]
          refine ⟨psi nil W, hOTX, hvX, fun x hx => ?_⟩
          rw [show psi nil W = cons nil W nil from rfl, G_cons_nil] at hx
          rcases List.mem_cons.mp hx with rfl | h1
          · rw [hvW]
            conv_lhs => rw [← add_zero (Ord.Omega 1 * (1 + δ))]
            rw [add_lt_add_iff_left]
            exact hαpos
          · rcases List.mem_append.mp h1 with h2 | h2
            · exact _root_.lt_trans (hGWval x h2) (by
                conv_lhs => rw [← add_zero (Ord.Omega 1 * (1 + δ))]
                rw [add_lt_add_iff_left]
                exact hαpos)
            · rw [G_nil] at h2
              exact absurd h2 (by simp)
        · have hpos : (0 : Ordinal) < Ord.eps δ := Ord.eps_pos δ
          have hdm : Ord.eps δ * (α / Ord.eps δ) + α % Ord.eps δ = α :=
            Ordinal.div_add_mod α (Ord.eps δ)
          have hyle : α / Ord.eps δ ≤ α := by
            refine le_trans (Ordinal.le_mul_right (α / Ord.eps δ) hpos) ?_
            exact le_trans (self_le_add_right _ _) (le_of_eq hdm)
          have hy0 : α / Ord.eps δ ≠ 0 := by
            intro h
            rw [h, mul_zero, zero_add] at hdm
            have hmod := Ordinal.mod_lt α (ne_of_gt hpos)
            rw [hdm] at hmod
            exact absurd hmod (not_lt.mpr hbig)
          have hlog : (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ) ≤ α / Ord.eps δ :=
            Ordinal.opow_log_le_self ω hy0
          have he : Ordinal.log (ω : Ordinal) (α / Ord.eps δ) < α := by
            rcases lt_or_ge (α / Ord.eps δ) α with h | h
            · exact lt_of_le_of_lt (Ordinal.log_le_self _ _) h
            · rw [le_antisymm hyle h]
              exact Ord.log_lt_self_of_lt_eps_succ hlt hα
          obtain ⟨B, hOTB, hvB, hinvB⟩ := IHα _ he (_root_.lt_trans he hα)
          have hBΩ : val B < Ord.Omega 1 := by
            rw [hvB]
            exact _root_.lt_trans he hαΩ
          have hjoinB : OT (addT W B) := OT_addT_of_allBig W hOTW hbigW B hOTB hBΩ.le
          have hGB : ∀ x ∈ G nil B, x < addT W B := by
            intro x hx
            refine term_lt_of_val_lt hOTB hjoinB hx ?_
            rw [val_addT, hvW, hvB]
            exact hinvB x hx
          have hP : Ord.psi (val (addT W B)) 0
              = Ord.eps δ * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ) := by
            rw [val_addT, hvW, hvB]
            exact Ord.psi_Omega_mul_add_eps hδ (_root_.lt_trans he hα)
          obtain ⟨k, hk⟩ := Ordinal.lt_omega0.mp
            (Ordinal.div_opow_log_lt (α / Ord.eps δ) Ordinal.one_lt_omega0)
          have hsplit : (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ) * (k : Ordinal)
              + (α / Ord.eps δ) % (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ)
                = α / Ord.eps δ := by
            have h := Ordinal.div_add_mod (α / Ord.eps δ)
              ((ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ))
            rwa [hk] at h
          have hstep : Ord.eps δ * ((α / Ord.eps δ) % (ω : Ordinal) ^
              Ordinal.log ω (α / Ord.eps δ)) + α % Ord.eps δ
                < Ord.eps δ * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ) := by
            refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr
              (Ordinal.mod_lt α (ne_of_gt hpos))) ?_
            rw [← mul_add_one]
            refine mul_le_mul_right ?_ _
            rw [← Order.succ_eq_add_one]
            exact Order.succ_le_of_lt (Ordinal.mod_lt _
              (ne_of_gt (Ordinal.opow_pos _ omega0_pos)))
          have hr : Ord.eps δ * ((α / Ord.eps δ) % (ω : Ordinal) ^
              Ordinal.log ω (α / Ord.eps δ)) + α % Ord.eps δ < α := by
            refine lt_of_lt_of_le hstep ?_
            refine le_trans (mul_le_mul_right hlog (Ord.eps δ)) ?_
            exact le_trans (self_le_add_right _ _) (le_of_eq hdm)
          obtain ⟨T, hOTT, hvT, hinvT⟩ := IHα _ hr (_root_.lt_trans hr hα)
          have hTΩ : val T < Ord.Omega 1 := by
            rw [hvT]
            exact _root_.lt_trans hr hαΩ
          have hOTpsi : OT (psi nil (addT W B)) := OT_psi_arg hOTW hbigW hGW hOTB hBΩ.le hGB
          have hdesc : descHead nil (addT W B) T = true := by
            refine descHead_of_val_lt hOTT hOTpsi ?_
            rw [hvT, val_psi, val_nil, hP]
            exact hstep
          have hOTX : OT (repCons (addT W B) k T) :=
            OT_repCons_arg hOTW hbigW hGW hOTB hBΩ.le hGB hOTT hdesc k
          have hvX : val (repCons (addT W B) k T) = α := by
            rw [val_repCons, hP, hvT, mul_assoc, ← add_assoc, ← mul_add, hsplit, hdm]
          refine ⟨repCons (addT W B) k T, hOTX, hvX, fun x hx => ?_⟩
          rcases G_repCons_mem hx with rfl | h | h
          · rw [val_addT, hvW, hvB]
            exact (add_lt_add_iff_left _).mpr he
          · rw [G_addT] at h
            rcases List.mem_append.mp h with h2 | h2
            · refine _root_.lt_trans (hGWval x h2) ?_
              conv_lhs => rw [← add_zero (Ord.Omega 1 * (1 + δ))]
              rw [add_lt_add_iff_left]
              exact hαpos
            · refine lt_of_lt_of_le (hinvB x h2) ?_
              rw [add_le_add_iff_left]
              exact he.le
          · refine lt_of_lt_of_le (hinvT x h) ?_
            rw [add_le_add_iff_left]
            exact hr.le

/-! ### `val` is onto below `ζ₀` -/

/-- **Every ordinal below `ζ₀` is the value of a standard form.**  `ζ₀` is
`ψ_0(Ω·ζ₀)` — `Ord.psi_Omega_mul_zeta0` — which is where this construction
stops; `val_tzeta0` below shows the terms themselves go further. -/
theorem exists_OT_of_lt_zeta0 {α : Ordinal.{0}} (h : α < Ord.zeta0) :
    ∃ X : Term, OT X ∧ val X = α := by
  obtain ⟨-, hval⟩ := exists_arg_and_OT α h
  obtain ⟨X, hOTX, hvX, -⟩ := hval α
    (lt_of_lt_of_le (Ord.lt_eps_self h) (Ord.eps_mono (by simp)))
  exact ⟨X, hOTX, hvX⟩

/-- **And by exactly one standard form.** -/
theorem existsUnique_OT_of_lt_zeta0 {α : Ordinal.{0}} (h : α < Ord.zeta0) :
    ∃! X : Term, OT X ∧ val X = α := by
  obtain ⟨X, hOTX, hvX⟩ := exists_OT_of_lt_zeta0 h
  refine ⟨X, ⟨hOTX, hvX⟩, fun Y hY => ?_⟩
  exact val_inj_of_OT hY.1 hOTX (by rw [hY.2, hvX])

/-! ### The bound is not tight

`ζ₀` is where **this construction** stops, not where the terms stop: `ζ₀`
itself is the value of a standard form, because `ψ_1(ψ_1(0))` is `Ω²` and
`Ord.psi_Omega_sq` says `ψ_0(Ω²) = ζ₀`.  What the terms with subscripts `0`
and `1` reach is `ψ_0(Ω_2)`, and the gap between `ζ₀` and it is the arguments
of `ψ_1` that this file does not build. -/

/-- The term `ψ_0(ψ_1(ψ_1(0)))`, that is `ψ_0(Ω²)`. -/
abbrev tzeta0 : Term := psi nil (psi t1 (psi t1 nil))

theorem OT_tzeta0 : OT tzeta0 := by decide

/-- **`ψ_0(Ω²)` names `ζ₀`**, so `ζ₀` is itself the value of a standard form
and `exists_OT_of_lt_zeta0` is a lower bound on what the terms reach, not a
description of it. -/
theorem val_tzeta0 : val tzeta0 = Ord.zeta0 := by
  rw [show tzeta0 = psi nil (psi t1 (psi t1 nil)) from rfl, val_psi, val_nil, val_psi, val_t1,
    val_psi, val_t1, val_nil, Ord.psi_zero_arg,
    Ord.psi_one_eq (Ord.Omega_lt_fpOmega 1), Ord.opow_Omega_one, Ord.psi_Omega_sq]

end Googology.Trans.BMS
