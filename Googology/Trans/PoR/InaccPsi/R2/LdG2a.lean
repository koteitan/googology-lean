import Googology.Trans.PoR.InaccPsi.R2.LdAlg

/-!
# The bases `Ω₂·γ` below `G₂ = ψ_{Ω₂}(Ω₂·Ω₂)`: own arguments, the layers, and the atoms

`κ₂ = Ω₂`, `H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ = gxTh ρ_λ (ldAtR λ)`, `F^β = ψ_{Ω₂}(β + Ω₂)`
(`ldTop`), `G₂ = ψ_{Ω₂}(Ω₂·Ω₂)` (`ldG2`), `L_0 = Ω₁`, `L_{j+1} = ψ_{Ω₂}(Ω₂·L_j)` (`ldLg`).

* `ldPsi2_le2` (`ψ_{Ω₂}(a) ≤ T` from the two base-`Ω₂` digits `(e/Ω₂) % Ω₂`, `e % Ω₂`);
* `ldLg_gt` (`γ < ψ_{Ω₂}(Ω₂·γ)` below every `L_j`), `ldLg_sup` (**`G₂ = sup_j L_j`**), `ldG2_ge`, `ldG2_gt`
  (**`γ < ψ_{Ω₂}(Ω₂·γ)` for every `γ < G₂`**);
* `ldG2_own`, `ldG2_H`, `ldG2_A` (**`Ω₂·γ` is a base** for every `γ ∈ H_λ`, `γ < G₂`);
* `ldG2_cls` (**every atom of `H_λ` below `ψ_{Ω₂}(Ω₂·γ)` is `ψ_{Ω₂}(Ω₂·γ'' + c)` with `c < F^{Ω₂·γ''}`, or
  `F^{Ω₂·γ''}`, for a code `γ'' < γ`**), `ldG2_clsAll` (**every atom of `H_λ` below `G₂` is `ψ_{Ω₂}(Ω₂·γ + c)` with
  `γ < G₂`, `c < F^{Ω₂·γ}` codes**), `ldG2_supp` (**finite support** at a limit `γ`).

No new axiom.  New definitions: `ldLg`, `ldG2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-! ## A bound for `ψ_{Ω₂}` from two digits -/

theorem ldOpow_lt_SC {T z : Ordinal.{0}} (hT : SC T) (hz : z < T) : ω ^ z < T := by
  have := hT.2 0 hT.1 z hz; rwa [veblen_zero_apply] at this

/-- `ψ_{Ω₂}(a) ≤ T` for a strongly critical `T > Ω₁`, if `ψ_{Ω₂}(e) < T` for every `e < a` whose digits
`(e/Ω₂) % Ω₂` and `e % Ω₂` are below `T`. -/
theorem ldPsi2_le2 {a T : Ordinal.{0}} (hT : SC T) (hΩT : Om 1 < T)
    (hcoll : ∀ e, e < a → e / Om (1 + 1) % Om (1 + 1) < T → e % Om (1 + 1) < T →
      S.psi e (Om (1 + 1)) < T) : S.psi a (Om (1 + 1)) ≤ T := by
  have hκ := ldOm2_SC
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := hκ.1.ne'
  -- a principal `p`, with the needed facts on its pieces
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < Om (1 + 1) → p < T) →
      (Om (1 + 1) ≤ p → ω ^ (log ω p - Om (1 + 1)) < Om (1 + 1) → ω ^ (log ω p - Om (1 + 1)) < T) →
      p / Om (1 + 1) % Om (1 + 1) < T ∧ p % Om (1 + 1) < T := by
    intro p hp h1 h2
    rcases lt_or_ge p (Om (1 + 1)) with hp1 | hp1
    · rw [Ordinal.div_eq_zero_of_lt hp1, Ordinal.zero_mod, Ordinal.mod_eq_of_lt hp1]
      exact ⟨hT.1, h1 hp1⟩
    · obtain ⟨e, -, -⟩ := ldDivK_prin hκ hp hp1
      rw [Ordinal.mod_eq_zero_of_dvd (ldDvdK_of_prin hκ hp hp1), e]
      refine ⟨?_, hT.1⟩
      rcases ldModK_prin hκ (isPrincipal_add_omega0_opow (log ω p - Om (1 + 1))) with ⟨hlt, e2⟩ | e2
      · rw [e2]; exact h2 hp1 hlt
      · rw [e2]; exact hT.1
  -- a principal `p` with `ω^p = p`
  have fix : ∀ {p : Ordinal.{0}}, ω ^ p = p → (p < Om (1 + 1) → p < T) →
      p / Om (1 + 1) % Om (1 + 1) < T ∧ p % Om (1 + 1) < T := by
    intro p hpE h1
    have hp : IsPrincipal (· + ·) p := by rw [← hpE]; exact isPrincipal_add_omega0_opow _
    refine prin hp h1 fun hp1 hlt => ?_
    have hlog : log ω p = p := by conv_lhs => rw [← hpE]; exact log_opow one_lt_omega0 _
    rw [hlog] at hlt ⊢
    rcases gg_sub_prin hp hp1 with e | e
    · rw [e, hpE] at hlt; exact absurd hp1 (not_le.2 hlt)
    · rw [e, opow_zero]; exact gg_one_lt_of_SC hT
  have key : ∀ x ∈ S.CSet a T, x / Om (1 + 1) % Om (1 + 1) < T ∧ x % Om (1 + 1) < T := by
    intro x hx
    induction hx with
    | @small x h =>
      have h1 : x / Om (1 + 1) ≤ x := Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ hκ.1)
      exact ⟨((Ordinal.mod_le _ _).trans h1).trans_lt h, (Ordinal.mod_le _ _).trans_lt h⟩
    | zero => rw [Ordinal.zero_div, Ordinal.zero_mod]; exact ⟨hT.1, hT.1⟩
    | inacc n =>
      exact fix (Low.opow_eq_self_of_SC (SC_I (S := S) n)) fun h => absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW =>
      exact fix (Low.opow_eq_self_of_SC (SC_Iw (S := S))) fun h => absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y _ _ ihx ihy =>
      rcases lt_or_ge y (Om (1 + 1)) with hy | hy
      · rw [ldDivK_add_lt hκ x hy, ldModK_add_lt hκ x hy]
        have hyT : y < T := by have := ihy.2; rwa [Ordinal.mod_eq_of_lt hy] at this
        exact ⟨ihx.1, hT.isPrincipal ihx.2 hyT⟩
      · rw [ldDivK_add_ge hκ x hy, ldModK_add_ge hκ x hy]
        refine ⟨?_, ihy.2⟩
        rcases lt_or_ge (y / Om (1 + 1)) (Om (1 + 1)) with hq | hq
        · rw [ldModK_add_lt hκ _ hq]
          have hqT : y / Om (1 + 1) < T := by have := ihy.1; rwa [Ordinal.mod_eq_of_lt hq] at this
          exact hT.isPrincipal ihx.1 hqT
        · rw [ldModK_add_ge hκ _ hq]; exact ihy.1
    | @phi x y _ _ ihx ihy =>
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply]
        refine prin (isPrincipal_add_omega0_opow y) (fun h => ?_) (fun hp1 hlt => ?_)
        · have hy1 : y < Om (1 + 1) := (right_le_opow y one_lt_omega0).trans_lt h
          have hyT : y < T := by have := ihy.2; rwa [Ordinal.mod_eq_of_lt hy1] at this
          exact ldOpow_lt_SC hT hyT
        · rw [log_opow one_lt_omega0] at hlt ⊢
          have hκy : Om (1 + 1) ≤ y := by
            rw [← Low.opow_eq_self_of_SC hκ] at hp1; exact (opow_le_opow_iff_right one_lt_omega0).1 hp1
          have hr : y - Om (1 + 1) < Om (1 + 1) := (right_le_opow _ one_lt_omega0).trans_lt hlt
          have hym : y % Om (1 + 1) = y - Om (1 + 1) := by
            conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hκy]
            rw [ldModK_add_lt hκ _ hr, Ordinal.mod_self, zero_add]
          have := ihy.2
          rw [hym] at this
          exact ldOpow_lt_SC hT this
      · refine fix (gg_veblen_eps hx0) fun h => ?_
        have hx1 : x < Om (1 + 1) := lt_of_le_of_lt (left_le_veblen x y) h
        have hy1 : y < Om (1 + 1) := lt_of_le_of_lt (right_le_veblen x y) h
        have hxT : x < T := by have := ihx.2; rwa [Ordinal.mod_eq_of_lt hx1] at this
        have hyT : y < T := by have := ihy.2; rwa [Ordinal.mod_eq_of_lt hy1] at this
        exact hT.2 x hxT y hyT
    | @om x _ _ =>
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [Om_zero, Ordinal.zero_div, Ordinal.zero_mod]; exact ⟨hT.1, hT.1⟩
      · refine fix (Low.opow_eq_self_of_SC (SC_Om hx0)) fun h => ?_
        have h2 : x < 1 + 1 := Om_lt_Om.1 h
        rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
        · exact absurd (Order.lt_one_iff.1 h0) hx0
        · rw [h1]; exact hΩT
    | @coll π e hπ _ _ _ ihe =>
      refine fix (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) fun h => ?_
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans h) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add]; exact (psi_lt Low.InR_Om_one _).trans hΩT
      rcases eq_or_ne s 1 with rfl | hs1
      · exact hcoll e.1 e.2 ihe.1 ihe.2
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans h) (lt_irrefl _)
  refine psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => ?_
  have := (key x hx).2
  rwa [Ordinal.mod_eq_of_lt hx2] at this

/-! ## The layers `L_j` and `G₂` -/

/-- `L_0 = Ω₁`, `L_{j+1} = ψ_{Ω₂}(Ω₂·L_j)`. -/
noncomputable def ldLg (S : InaccSeq.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (Om (1 + 1) * ldLg S j) (Om (1 + 1))

/-- `G₂ = ψ_{Ω₂}(Ω₂·Ω₂)`. -/
noncomputable def ldG2 (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1) * Om (1 + 1)) (Om (1 + 1))

theorem ldLg_succ (j : ℕ) : ldLg S (j + 1) = S.psi (Om (1 + 1) * ldLg S j) (Om (1 + 1)) := rfl

theorem ldLg_lt_Om2 : ∀ j, ldLg S j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem ldLg_SC : ∀ j, SC (ldLg S j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem ldG2_SC : SC (ldG2 S) := SC_psi (InR_Om_succ 1) _
theorem ldG2_lt_Om2 : ldG2 S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem ldOm1_lt_G2 : Om (1 : Ordinal.{0}) < ldG2 S := (psiS_bounds (S := S) _ 1).1

theorem ldOm2_mul_mono {x y : Ordinal.{0}} (h : x ≤ y) : Om (1 + 1 : Ordinal.{0}) * x ≤ Om (1 + 1) * y :=
  mul_le_mul_right h _

theorem ldOm2_mul_lt {x y : Ordinal.{0}} (h : x < y) : Om (1 + 1 : Ordinal.{0}) * x < Om (1 + 1) * y :=
  (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 h

theorem ldLg_lt_succ : ∀ j, ldLg S j < ldLg S (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := ldLg_lt_succ j
    have hle : ldLg S (j + 1) ≤ ldLg S (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) (ldOm2_mul_mono IH.le)).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) (ldOm2_mul_lt IH) ?_
    exact ldMulK_small ldOm2_SC (mxOm2_mem _ _) _ (IH.trans_le hle)

theorem ldLg_mono {j j' : ℕ} (h : j ≤ j') : ldLg S j ≤ ldLg S j' :=
  (strictMono_nat_of_lt_succ (fun k => ldLg_lt_succ (S := S) k)).monotone h

/-- `γ < ψ_{Ω₂}(Ω₂·γ)` below every `L_j`. -/
theorem ldLg_gt : ∀ j γ, γ < ldLg S j → γ < S.psi (Om (1 + 1) * γ) (Om (1 + 1))
  | 0, γ, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, γ, h => by
    rcases lt_or_ge γ (ldLg S j) with h' | h'
    · exact ldLg_gt j γ h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) (ldOm2_mul_mono h')).1

theorem ldLg_le_G2 : ∀ j, ldLg S j ≤ ldG2 S
  | 0 => ldOm1_lt_G2.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (ldOm2_mul_mono (ldLg_lt_Om2 j).le)).1

/-- **`G₂ = sup_j L_j`.** -/
theorem ldLg_sup {x : Ordinal.{0}} (hx : x < ldG2 S) : ∃ j, x < ldLg S j := by
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hbdd : BddAbove (Set.range (ldLg S)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, ldLg S j ↔ ∃ j, y < ldLg S j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, ldLg S j < ⨆ j, ldLg S j := fun j => (hlt _).2 ⟨j + 1, ldLg_lt_succ j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, ldLg S j := hKQ 0
  have hQSC : SC (⨆ j, ldLg S j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨k, hk⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (ldLg_mono (S := S) (le_max_left i k))
    have hk' := hk.trans_le (ldLg_mono (S := S) (le_max_right i k))
    exact ((ldLg_SC (max i k)).2 _ hi' _ hk').trans (hKQ _)
  have hFQ : ldG2 S ≤ ⨆ j, ldLg S j := by
    refine ldPsi2_le2 hQSC hΩQ fun e he hq _ => ?_
    have hq2 : e / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hκ0).1 he
    rw [Ordinal.mod_eq_of_lt hq2] at hq
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have he' : e < Om (1 + 1) * ldLg S j := by
      calc e < Om (1 + 1) * (e / Om (1 + 1) + 1) := by
            rw [mul_add_one]
            conv_lhs => rw [← Ordinal.div_add_mod e (Om (1 + 1))]
            exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt e hκ0)
        _ ≤ Om (1 + 1) * ldLg S j := ldOm2_mul_mono (Order.add_one_le_of_lt hj)
    have := hKQ (j + 1)
    rw [ldLg_succ] at this
    exact ((psi_mono (S := S) (InR_Om_succ 1) he'.le).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(Ω₂·γ) ≥ G₂` for `γ ≥ G₂`. -/
theorem ldG2_ge {γ : Ordinal.{0}} (hγ : ldG2 S ≤ γ) : ldG2 S ≤ S.psi (Om (1 + 1) * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := ldLg_sup h
  have h1 : ldLg S (j + 1) ≤ S.psi (Om (1 + 1) * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) (ldOm2_mul_mono ((ldLg_le_G2 j).trans hγ))).1
  exact absurd (hj.trans_le ((ldLg_lt_succ j).le.trans h1)) (lt_irrefl _)

/-- **`γ < ψ_{Ω₂}(Ω₂·γ)` for every `γ < G₂`.** -/
theorem ldG2_gt {γ : Ordinal.{0}} (hγ : γ < ldG2 S) : γ < S.psi (Om (1 + 1) * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := ldLg_sup hγ
  exact ldLg_gt j γ hj

/-! ## `Ω₂·γ` is a base -/

theorem ldG2_own {γ : Ordinal.{0}} (hγ : γ < ldG2 S) :
    ∀ d, d ≤ Om (1 + 1) → Om (1 + 1) * γ ∈
      S.CSet (Om (1 + 1) * γ + d) (S.psi (Om (1 + 1) * γ + d) (Om (1 + 1))) :=
  fun _ _ => ldMulK_small ldOm2_SC (mxOm2_mem _ _) γ
    ((ldG2_gt hγ).trans_le (psi_mono (S := S) (InR_Om_succ 1) le_self_add).1)

theorem ldG2_H {l γ : Ordinal.{0}} (hγ : γ ∈ cdHull S l) : Om (1 + 1) * γ ∈ cdHull S l :=
  ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hγ

theorem ldOm2sq_eq : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) = ω ^ (Om (1 + 1) + Om (1 + 1)) := by
  rw [opow_add, Low.opow_eq_self_of_SC ldOm2_SC]

theorem ldOm2sq_lt_OmW : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < Om ω := by
  rw [ldOm2sq_eq, ← Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)]
  exact (opow_lt_opow_iff_right one_lt_omega0).2
    ((Om_isPrincipal omega0_ne_zero) ldOm2_lt_OmW ldOm2_lt_OmW)

theorem ldG2_A (l : Ordinal.{0}) {γ : Ordinal.{0}} (hγ2 : γ < Om (1 + 1)) :
    Om (1 + 1) * γ + Om (1 + 1) < ConjT.Aη S (cdEta S l) := by
  rw [← mul_add_one]
  exact ((ldOm2_mul_lt (ldOm2_SC.isSuccLimit.succ_lt hγ2)).trans ldOm2sq_lt_OmW).trans_le le_self_add

theorem ldG2_lt_th : ldG2 S < ConjT.th S :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ldOm2sq_lt_OmW (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _))

theorem ldTop_mono {β β' : Ordinal.{0}} (h : β ≤ β') : ldTop S β ≤ ldTop S β' :=
  (psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left h _)).1

theorem ldTop_mul (γ : Ordinal.{0}) :
    ldTop S (Om (1 + 1) * γ) = S.psi (Om (1 + 1) * (γ + 1)) (Om (1 + 1)) := by
  unfold ldTop; rw [mul_add_one]

/-! ## The atoms below `ψ_{Ω₂}(Ω₂·γ)` -/

/-- **Every atom of `H_λ` below `ψ_{Ω₂}(Ω₂·γ)` (`γ ≤ G₂`) is in the block of a code `γ'' < γ`.** -/
theorem ldG2_cls {l ηx γ t : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hγG : γ ≤ ldG2 S) (ht : t ∈ ldAtR S l) (htγ : t < S.psi (Om (1 + 1) * γ) (Om (1 + 1))) :
    ∃ γ'', GxCl (upsilon l) (ldAtR S l) γ'' ∧ γ'' < γ ∧
      ((∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S (Om (1 + 1) * γ'') ∧
        t = S.psi (Om (1 + 1) * γ'' + c) (Om (1 + 1))) ∨ t = ldTop S (Om (1 + 1) * γ'')) := by
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨a, ha, -, rfl⟩ := ht
  have haγ : a < Om (1 + 1) * γ := by
    by_contra h
    push Not at h
    exact absurd htγ (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  have hγ'' : a / Om (1 + 1) < γ := (Ordinal.lt_mul_iff_div_lt hκ0).1 haγ
  have hγ''G : a / Om (1 + 1) < ldG2 S := hγ''.trans_le hγG
  have hγ''2 : a / Om (1 + 1) < Om (1 + 1) := hγ''G.trans ldG2_lt_Om2
  have hγ''H : a / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC ha
  have hcH : a % Om (1 + 1) ∈ cdHull S l := ldModK_mem ldOm2_SC ha
  have hc2 : a % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt a hκ0
  have hdec : a = Om (1 + 1) * (a / Om (1 + 1)) + a % Om (1 + 1) := (Ordinal.div_add_mod a _).symm
  refine ⟨a / Om (1 + 1), (ldHull_iff hl hX hγ''2).1 hγ''H, hγ'', ?_⟩
  rcases lt_or_ge (a % Om (1 + 1)) (ldTop S (Om (1 + 1) * (a / Om (1 + 1)))) with hcF | hcF
  · exact Or.inl ⟨_, (ldHull_iff hl hX hc2).1 hcH, hcF, by rw [← hdec]⟩
  · refine Or.inr (le_antisymm ?_ ?_)
    · conv_lhs => rw [hdec]
      exact (psi_mono (S := S) (InR_Om_succ 1) (add_le_add_right hc2.le _)).1
    · conv_rhs => rw [hdec]
      exact ldTop_ge (ldG2_own hγ''G) (dvd_mul_right _ _) hcF

/-- **Every atom of `H_λ` below `G₂` is `ψ_{Ω₂}(Ω₂·γ + c)`** with codes `γ < G₂`, `c < F^{Ω₂·γ}`. -/
theorem ldG2_clsAll {l ηx t : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (ht : t ∈ ldAtR S l) (htG : t < ldG2 S) :
    ∃ γ, GxCl (upsilon l) (ldAtR S l) γ ∧ γ < ldG2 S ∧ ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧
      c < ldTop S (Om (1 + 1) * γ) ∧ t = S.psi (Om (1 + 1) * γ + c) (Om (1 + 1)) := by
  have hκ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨a, ha, -, rfl⟩ := ht
  have ha2 : a < Om (1 + 1) * Om (1 + 1) := by
    by_contra h
    push Not at h
    exact absurd htG (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) h).1)
  have hdec : a = Om (1 + 1) * (a / Om (1 + 1)) + a % Om (1 + 1) := (Ordinal.div_add_mod a _).symm
  have hγG : a / Om (1 + 1) < ldG2 S := by
    by_contra h
    push Not at h
    have h1 := ldG2_ge (S := S) h
    have h2 : S.psi (Om (1 + 1) * (a / Om (1 + 1))) (Om (1 + 1)) ≤ S.psi a (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) (Ordinal.mul_div_le a _)).1
    exact absurd htG (not_lt.2 (h1.trans h2))
  have hγ2 : a / Om (1 + 1) < Om (1 + 1) := hγG.trans ldG2_lt_Om2
  have hγH : a / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC ha
  have hcH : a % Om (1 + 1) ∈ cdHull S l := ldModK_mem ldOm2_SC ha
  have hc2 : a % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt a hκ0
  rcases lt_or_ge (a % Om (1 + 1)) (ldTop S (Om (1 + 1) * (a / Om (1 + 1)))) with hcF | hcF
  · exact ⟨_, (ldHull_iff hl hX hγ2).1 hγH, hγG, _, (ldHull_iff hl hX hc2).1 hcH, hcF, by rw [← hdec]⟩
  · have hγ1G : a / Om (1 + 1) + 1 < ldG2 S := ldG2_SC.isSuccLimit.succ_lt hγG
    have hγ12 : a / Om (1 + 1) + 1 < Om (1 + 1) := hγ1G.trans ldG2_lt_Om2
    refine ⟨_, (ldHull_iff hl hX hγ12).1 (CSet.succ_mem hγH), hγ1G, 0, GxCl.zero (mvUps_pos hl),
      (Om_pos one_ne_zero).trans (ldOm1_lt_Top _), ?_⟩
    rw [add_zero, ← ldTop_mul]
    refine le_antisymm ?_ ?_
    · conv_lhs => rw [hdec]
      exact (psi_mono (S := S) (InR_Om_succ 1) (add_le_add_right hc2.le _)).1
    · conv_rhs => rw [hdec]
      exact ldTop_ge (ldG2_own hγG) (dvd_mul_right _ _) hcF

/-- **Finite support at a limit `γ`**: a code below `ψ_{Ω₂}(Ω₂·γ)` is below `F^{Ω₂·γ*}` for a code `γ* < γ`
above any given code `γ' < γ`. -/
theorem ldG2_supp {l ηx γ : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hγG : γ ≤ ldG2 S) (hlim : IsSuccLimit γ) :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < S.psi (Om (1 + 1) * γ) (Om (1 + 1)) →
      ∀ γ', GxCl (upsilon l) (ldAtR S l) γ' → γ' < γ → ∃ γs, GxCl (upsilon l) (ldAtR S l) γs ∧
        γ' ≤ γs ∧ γs < γ ∧ c < ldTop S (Om (1 + 1) * γs) := by
  intro c hc
  induction hc with
  | @small x h =>
    intro _ γ' hγ' hγ'γ
    have hρ1 : upsilon l < Om 1 := by
      have hpv := cdEta_pv (S := S) hl.1 hX
      rw [← hpv]; exact psi_lt Low.InR_Om_one _
    exact ⟨γ', hγ', le_rfl, hγ'γ, ((h.trans hρ1).trans (ldOm1_lt_Top _))⟩
  | om => exact fun _ γ' hγ' hγ'γ => ⟨γ', hγ', le_rfl, hγ'γ, ldOm1_lt_Top _⟩
  | @atom s hs =>
    intro hsγ γ' hγ' hγ'γ
    obtain ⟨γ'', hγ''c, hγ''γ, hcase⟩ := ldG2_cls hl hX hγG hs hsγ
    have hsle : s ≤ ldTop S (Om (1 + 1) * γ'') := by
      rcases hcase with ⟨c, -, hcF, rfl⟩ | rfl
      · exact (ldTop_lt (ldG2_own (hγ''γ.trans_le hγG)) hcF).le
      · exact le_rfl
    have hγ1 : γ'' + 1 < γ := hlim.succ_lt hγ''γ
    have hγ1G : γ'' + 1 < ldG2 S := hγ1.trans_le hγG
    have hγ1c : GxCl (upsilon l) (ldAtR S l) (γ'' + 1) := by
      have h2 : γ'' + 1 < Om (1 + 1) := hγ1G.trans ldG2_lt_Om2
      exact (ldHull_iff hl hX h2).1 (CSet.succ_mem ((ldHull_iff hl hX ((lt_add_one _).trans h2)).2 hγ''c))
    have hs1 : s < ldTop S (Om (1 + 1) * (γ'' + 1)) := by
      refine hsle.trans_lt ?_
      rw [ldTop_mul]
      exact ldBase_lt_top (ldG2_own hγ1G)
    rcases le_total γ' (γ'' + 1) with h | h
    · exact ⟨γ'' + 1, hγ1c, h, hγ1, hs1⟩
    · exact ⟨γ', hγ', le_rfl, hγ'γ, hs1.trans_le (ldTop_mono (ldOm2_mul_mono h))⟩
  | @add x y _ _ ihx ihy =>
    intro hxy γ' hγ' hγ'γ
    obtain ⟨γ1, hγ1, h1, h1γ, hx1⟩ := ihx (lt_of_le_of_lt le_self_add hxy) γ' hγ' hγ'γ
    obtain ⟨γ2, hγ2, h2, h2γ, hy2⟩ := ihy (lt_of_le_of_lt le_add_self hxy) γ1 hγ1 h1γ
    exact ⟨γ2, hγ2, h1.trans h2, h2γ, (ldTop_SC _).isPrincipal
      (hx1.trans_le (ldTop_mono (ldOm2_mul_mono h2))) hy2⟩
  | @phi x y _ _ ihx ihy =>
    intro hxy γ' hγ' hγ'γ
    obtain ⟨γ1, hγ1, h1, h1γ, hx1⟩ := ihx (lt_of_le_of_lt (left_le_veblen x y) hxy) γ' hγ' hγ'γ
    obtain ⟨γ2, hγ2, h2, h2γ, hy2⟩ := ihy (lt_of_le_of_lt (right_le_veblen x y) hxy) γ1 hγ1 h1γ
    exact ⟨γ2, hγ2, h1.trans h2, h2γ, (ldTop_SC _).2 _
      (hx1.trans_le (ldTop_mono (ldOm2_mul_mono h2))) _ hy2⟩

end Googology.Trans.PoR.InaccPsi.R2.Ld
