import Googology.Trans.BMS.Arg

/-!
# `val` is onto the ordinals below `ε_γ`, for every `γ < ε₀`

`EpsN.lean` carries the construction to every `ε_n` and to `ε_ω`, with `Ω·n`
written as `n` copies of `Ω`.  This file replaces that argument by an
arbitrary standard form naming `Ω·(1+γ)` — `Arg.lean` builds one for every
`γ < ε₀` — and carries the same construction to every `ε_γ` with `γ < ε₀`,
hence onto the ordinals below `ε_{ε₀} = ψ_0(Ω·ε₀)`.

The invariant is quantified over the argument term: a term `X` built at level
`γ` satisfies `G_0 X < W + X` for **every** `W` naming at least `Ω·(1+γ)`.
That is what makes the pieces compose — the terms for the exponent and for
the remainder are built at the same level or below, and their invariants are
instantiated at the `W` in hand.
-/

namespace Googology.Trans.BMS

open Ordinal
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ### The leading term over an argument -/

theorem le_addT_left {W B : Term} (hW : OT W)
    (hjoin : OT (addT W B)) : W ≤ addT W B := by
  refine le_of_val_le hW hjoin ?_
  rw [val_addT]
  exact self_le_add_right _ _

/-- **`ψ_0(W + B)` in front of `t` is a standard form.**  `W` is an argument
term: all of its parts name at least `Ω` and its `G_0` stays below it. -/
theorem OT_cons_arg {W B t : Term} (hW : OT W) (hbig : AllBig W)
    (hGW : ∀ x ∈ G nil W, x < W) (hB : OT B) (hBval : val B ≤ Ord.Omega 1)
    (hGB : ∀ x ∈ G nil B, x < addT W B) (ht : OT t)
    (hdesc : descHead nil (addT W B) t = true) : OT (cons nil (addT W B) t) := by
  have hjoin : OT (addT W B) := OT_addT_of_allBig W hW hbig B hB hBval
  show isOT (cons nil (addT W B) t) = true
  rw [isOT]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨rfl, hjoin⟩, ?_⟩, ht⟩, hdesc⟩
  refine List.all_eq_true.mpr (fun x hx => decide_eq_true ?_)
  rw [G_addT] at hx
  rcases List.mem_append.mp hx with h | h
  · exact lt_of_lt_of_le' (hGW x h) (le_addT_left hW hjoin)
  · exact hGB x h

theorem OT_psi_arg {W B : Term} (hW : OT W) (hbig : AllBig W)
    (hGW : ∀ x ∈ G nil W, x < W) (hB : OT B) (hBval : val B ≤ Ord.Omega 1)
    (hGB : ∀ x ∈ G nil B, x < addT W B) : OT (psi nil (addT W B)) :=
  OT_cons_arg hW hbig hGW hB hBval hGB rfl rfl

theorem OT_repCons_arg {W B t : Term} (hW : OT W) (hbig : AllBig W)
    (hGW : ∀ x ∈ G nil W, x < W) (hB : OT B) (hBval : val B ≤ Ord.Omega 1)
    (hGB : ∀ x ∈ G nil B, x < addT W B) (ht : OT t)
    (hdesc : descHead nil (addT W B) t = true) :
    ∀ n : Nat, OT (repCons (addT W B) n t) := by
  intro n
  induction n with
  | zero => exact ht
  | succ m ih => exact OT_cons_arg hW hbig hGW hB hBval hGB ih (descHead_repCons hdesc m)

/-! ### The induction -/

/-- **Every ordinal below `ε_{δ+1}` is the value of a standard form**, with
`G_0` of it below `W` plus it for every argument term `W` naming at least
`Ω·(1+δ)`.  The induction is on `δ`, with the value inside it: below `ε_δ`
the previous level answers, and above it the leading term is
`ψ_0(Ω·(1+δ) + B)`, whose value `Ord.psi_Omega_mul_add_eps` computes. -/
theorem exists_OT_of_lt_eps : ∀ δ : Ordinal.{0}, δ < Ord.eps0 →
    ∀ α : Ordinal.{0}, α < Ord.eps (δ + 1) →
      ∃ X : Term, OT X ∧ val X = α ∧
        ∀ W : Term, OT W → AllBig W → Ord.Omega 1 * (1 + δ) ≤ val W →
          ∀ x ∈ G nil X, x < addT W X := by
  intro δ
  induction δ using WellFoundedLT.induction with
  | _ δ IHδ =>
    intro hδ α
    induction α using WellFoundedLT.induction with
    | _ α IHα =>
      intro hα
      have hδ1 : δ + 1 < Ord.eps0 := Ord.isPrincipal_add_eps0 hδ Ord.one_lt_eps0
      have hepsΩ : Ord.eps (δ + 1) < Ord.Omega 1 :=
        Ord.eps_lt_Omega_one (lt_trans hδ1 Ord.eps0_lt_Omega_one)
      rcases lt_or_ge α (Ord.eps δ) with hsmall | hbig
      · rcases Ordinal.zero_or_succ_or_isSuccLimit δ with rfl | ⟨δ', hδeq⟩ | hlim
        · rw [Ord.eps_zero] at hsmall
          obtain ⟨X, hAX, hDX, hvX⟩ := exists_desc_of_lt_eps0 α hsmall
          have hOTX : OT X := OT_of_desc X hAX hDX
          refine ⟨X, hOTX, hvX, fun W hW hbigW _ x hx => ?_⟩
          have hXΩ : val X < Ord.Omega 1 := by
            rw [hvX]
            exact lt_trans hsmall Ord.eps0_lt_Omega_one
          have hjoin : OT (addT W X) := OT_addT_of_allBig W hW hbigW X hOTX hXΩ.le
          refine lt_of_lt_of_le' (G_lt_of_desc X hAX hDX x hx) (le_of_val_le hOTX hjoin ?_)
          rw [val_addT]
          exact self_le_add_left _ _
        · subst hδeq
          rw [Order.succ_eq_add_one] at hsmall hδ ⊢
          have hlt' : δ' < δ' + 1 := by simp
          obtain ⟨X, hOTX, hvX, hinv⟩ := IHδ δ' hlt' (lt_trans hlt' hδ) α hsmall
          refine ⟨X, hOTX, hvX, fun W hW hbigW hWval => hinv W hW hbigW (le_trans ?_ hWval)⟩
          exact mul_le_mul_right ((add_le_add_iff_left 1).mpr hlt'.le) _
        · haveI : Small.{0} {a : Ordinal.{0} // a < δ} := Ordinal.small_Iio δ
          rw [Ord.eps_limit hlim] at hsmall
          obtain ⟨⟨δ', hδ'⟩, hxδ⟩ := Ordinal.lt_iSup_iff.mp hsmall
          obtain ⟨X, hOTX, hvX, hinv⟩ := IHδ δ' hδ' (lt_trans hδ' hδ) α
            (lt_of_lt_of_le hxδ (Ord.eps_mono (by simp)))
          refine ⟨X, hOTX, hvX, fun W hW hbigW hWval => hinv W hW hbigW (le_trans ?_ hWval)⟩
          exact mul_le_mul_right ((add_le_add_iff_left 1).mpr hδ'.le) _
      · have hδz : δ < Ord.zeta0 := lt_of_lt_of_le hδ Ord.eps0_le_zeta0
        have h1δ : 1 + δ < Ord.eps0 := Ord.isPrincipal_add_eps0 Ord.one_lt_eps0 hδ
        obtain ⟨Wd, hOTWd, hvWd, hbigWd, hGWd⟩ := exists_argTerm (1 + δ) h1δ
        have hpsiWd : Ord.psi (val Wd) 0 = Ord.eps δ := by
          rw [hvWd]
          exact Ord.psi_Omega_mul_eps hδz
        have hαpos : (0 : Ordinal) < α := lt_of_lt_of_le (Ord.eps_pos δ) hbig
        have hαΩ : α < Ord.Omega 1 := lt_trans hα hepsΩ
        rcases eq_or_lt_of_le hbig with heq | hlt
        · have hnilB : ∀ x ∈ G nil (nil : Term), x < addT Wd nil := by
            intro x hx
            rw [G_nil] at hx
            exact absurd hx (by simp)
          have hOTX : OT (psi nil Wd) := by
            have h := OT_psi_arg hOTWd hbigWd hGWd (B := nil) rfl
              (by rw [show val (nil : Term) = 0 from rfl]; exact le_of_lt (Ord.Omega_pos 1)) hnilB
            rwa [addT_nil_right] at h
          have hvX : val (psi nil Wd) = α := by
            rw [val_psi, show val (nil : Term) = 0 from rfl, hpsiWd, heq]
          refine ⟨psi nil Wd, hOTX, hvX, fun W hW hbigW hWval x hx => ?_⟩
          have hXΩ : val (psi nil Wd) < Ord.Omega 1 := by rw [hvX]; exact hαΩ
          have hjoin : OT (addT W (psi nil Wd)) := OT_addT_of_allBig W hW hbigW _ hOTX hXΩ.le
          have hWdlt : Wd < addT W (psi nil Wd) := by
            refine lt_of_val_lt hOTWd hjoin ?_
            rw [val_addT, hvWd, hvX]
            refine lt_of_le_of_lt hWval ?_
            conv_lhs => rw [← add_zero (val W)]
            rw [add_lt_add_iff_left]
            exact hαpos
          rw [show psi nil Wd = cons nil Wd nil from rfl, G_cons_nil] at hx
          rcases List.mem_cons.mp hx with rfl | h1
          · exact hWdlt
          · rcases List.mem_append.mp h1 with h2 | h2
            · exact lt_trans (hGWd x h2) hWdlt
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
          obtain ⟨B, hOTB, hvB, hinvB⟩ := IHα _ he (lt_trans he hα)
          have hBΩ : val B < Ord.Omega 1 := by
            rw [hvB]
            exact lt_trans he hαΩ
          have hGB : ∀ x ∈ G nil B, x < addT Wd B :=
            hinvB Wd hOTWd hbigWd (le_of_eq hvWd.symm)
          have hP : Ord.psi (val (addT Wd B)) 0
              = Ord.eps δ * (ω : Ordinal) ^ Ordinal.log ω (α / Ord.eps δ) := by
            rw [val_addT, hvWd, hvB]
            exact Ord.psi_Omega_mul_add_eps hδz (lt_trans he hα)
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
          obtain ⟨T, hOTT, hvT, hinvT⟩ := IHα _ hr (lt_trans hr hα)
          have hTΩ : val T < Ord.Omega 1 := by
            rw [hvT]
            exact lt_trans hr hαΩ
          have hOTpsi : OT (psi nil (addT Wd B)) :=
            OT_psi_arg hOTWd hbigWd hGWd hOTB hBΩ.le hGB
          have hdesc : descHead nil (addT Wd B) T = true := by
            refine descHead_of_val_lt hOTT hOTpsi ?_
            rw [hvT, val_psi, show val (nil : Term) = 0 from rfl, hP]
            exact hstep
          have hOTX : OT (repCons (addT Wd B) k T) :=
            OT_repCons_arg hOTWd hbigWd hGWd hOTB hBΩ.le hGB hOTT hdesc k
          have hvX : val (repCons (addT Wd B) k T) = α := by
            rw [val_repCons, hP, hvT, mul_assoc, ← add_assoc, ← mul_add, hsplit, hdm]
          refine ⟨repCons (addT Wd B) k T, hOTX, hvX, fun W hW hbigW hWval x hx => ?_⟩
          have hXΩ : val (repCons (addT Wd B) k T) < Ord.Omega 1 := by rw [hvX]; exact hαΩ
          have hjoin : OT (addT W (repCons (addT Wd B) k T)) :=
            OT_addT_of_allBig W hW hbigW _ hOTX hXΩ.le
          have hWdle : Wd < addT W (repCons (addT Wd B) k T) := by
            refine lt_of_val_lt hOTWd hjoin ?_
            rw [val_addT, hvWd, hvX]
            refine lt_of_le_of_lt hWval ?_
            conv_lhs => rw [← add_zero (val W)]
            rw [add_lt_add_iff_left]
            exact hαpos
          rcases G_repCons_mem hx with rfl | h | h
          · refine lt_of_val_lt (OT_addT_of_allBig Wd hOTWd hbigWd B hOTB hBΩ.le) hjoin ?_
            rw [val_addT, val_addT, hvWd, hvB, hvX]
            exact add_lt_add_of_le_of_lt hWval he
          · rw [G_addT] at h
            rcases List.mem_append.mp h with h2 | h2
            · exact lt_trans (hGWd x h2) hWdle
            · refine lt_of_lt_of_le' (hinvB W hW hbigW hWval x h2) ?_
              refine le_of_val_le (OT_addT_of_allBig W hW hbigW B hOTB hBΩ.le) hjoin ?_
              rw [val_addT, val_addT, hvB, hvX, add_le_add_iff_left]
              exact he.le
          · refine lt_of_lt_of_le' (hinvT W hW hbigW hWval x h) ?_
            refine le_of_val_le (OT_addT_of_allBig W hW hbigW T hOTT hTΩ.le) hjoin ?_
            rw [val_addT, val_addT, hvT, hvX, add_le_add_iff_left]
            exact hr.le

/-! ### The ceiling -/

/-- **Every ordinal below `ε_{ε₀}` is the value of a standard form.** -/
theorem exists_OT_of_lt_epsE0 {α : Ordinal.{0}} (h : α < Ord.eps Ord.eps0) :
    ∃ X : Term, OT X ∧ val X = α := by
  haveI : Small.{0} {a : Ordinal.{0} // a < Ord.eps0} := Ordinal.small_Iio _
  rw [Ord.eps_limit Ord.isSuccLimit_eps0] at h
  obtain ⟨⟨δ, hδ⟩, hxδ⟩ := Ordinal.lt_iSup_iff.mp h
  obtain ⟨X, hOTX, hvX, _⟩ :=
    exists_OT_of_lt_eps δ hδ α (lt_of_lt_of_le hxδ (Ord.eps_mono (by simp)))
  exact ⟨X, hOTX, hvX⟩

/-- The term `ψ_0(ψ_1(ψ_0(Ω)))`, that is `ψ_0(Ω·ε₀)`. -/
abbrev teE : Term := psi nil (psi t1 te0)

theorem OT_teE : OT teE := by decide

/-- **`ψ_0(Ω·ε₀)` names `ε_{ε₀}`.** -/
theorem val_teE : val teE = Ord.eps Ord.eps0 := by
  rw [show teE = psi nil (psi t1 te0) from rfl, val_psi, val_psi, val_nil, val_t1, val_te0,
    Ord.psi_one_eq (lt_of_lt_of_le Ord.eps0_lt_Omega_one (Ord.Omega_le_fpOmega 1)),
    Ord.opow_eps0, show Ord.Omega 1 * Ord.eps0 = Ord.Omega 1 * (1 + Ord.eps0) from by
      rw [Ord.one_add_eps0]]
  exact Ord.psi_Omega_mul_eps Ord.eps0_lt_zeta0

/-- **The standard forms below `ψ_0(Ω·ε₀)` name exactly the ordinals below
`ε_{ε₀}`.** -/
theorem exists_OT_lt_teE {α : Ordinal.{0}} (h : α < Ord.eps Ord.eps0) :
    ∃ X : Term, OT X ∧ X < teE ∧ val X = α := by
  obtain ⟨X, hOT, hv⟩ := exists_OT_of_lt_epsE0 h
  exact ⟨X, hOT, lt_of_val_lt hOT OT_teE (by rw [hv, val_teE]; exact h), hv⟩

/-- **Below `ε_{ε₀}`, `val` is a bijection from the standard forms onto the
ordinals.** -/
theorem existsUnique_OT_lt_teE {α : Ordinal.{0}} (h : α < Ord.eps Ord.eps0) :
    ∃! X : Term, OT X ∧ X < teE ∧ val X = α := by
  obtain ⟨X, hOT, hlt, hv⟩ := exists_OT_lt_teE h
  refine ⟨X, ⟨hOT, hlt, hv⟩, fun Y hY => ?_⟩
  exact val_inj_of_OT hY.1 hOT (by rw [hY.2.2, hv])

theorem val_lt_epsE0_of_lt_teE {X : Term} (hOT : OT X) (h : X < teE) :
    val X < Ord.eps Ord.eps0 := by
  rw [← val_teE]
  exact val_lt_val hOT OT_teE h

end Googology.Trans.BMS
