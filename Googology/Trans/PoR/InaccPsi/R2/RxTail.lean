import Googology.Trans.PoR.InaccPsi.R2.RxK

/-!
# The members of the hull below `ψ_{Ω₂}(Ω₂)` are codes with normal `ψ_{Ω₂}`-atoms

`P₂ = ψ_{Ω₂}(Ω₂)` (`rxP2`), `ψ₂ = ψ_{Ω₂}`, `HCl = Bt.HCl` (`Cl` without the countable collapses), `RxC S T` the codes
over `T` with normal `ψ₂`-atoms (`Rx.RxC`), `θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`.

* `rxP2_fix` (**`ψ₂(P₂) = P₂`**: `Cl(Ω₂, ψ₂(P₂)) ⊆ Cl(P₂, ψ₂(P₂))`), so `ψ₂(e) ≥ P₂` for every `e ≥ P₂`;
* `rxN` (**a code `x ≤ α` over `T ≤ ψ₂(α)` lies in `Cl(α, ψ₂(α))`**), `rxNorm` (`e < ψ₂(e)` for a code `e < Ω₂`
  over `T ≤ Ω₁`: every code is a normal argument);
* `rxHCl` (**a member of `HCl S a T` below `Ω₂` is a code over `T` or `≥ P₂`**, for `0 < T ≤ Ω₁`), `rxLt_P2` (the
  codes over `T ≤ Ω₁` are below `P₂`);
* `rxTail` (**the tail of a member of the hull**: for `P₂ ∣ Â` and `Â ≤ e < Â + y ≤ Â + P₂`, `e − Â` is a code
  over `T`), `rxDvd` (`P₂ ∣ A_η + θ·x`);
* `rxCof` (**the codes over `2` are cofinal in `P₂`**).

No new axiom.  New definition: `rxP2`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Ru

/-- `P₂ = ψ_{Ω₂}(Ω₂)`. -/
noncomputable def rxP2 (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1)) (Om (1 + 1))

variable {S : InaccSeq.{0}}

theorem rxP2_lt : rxP2 S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem rxP2_gt : Om 1 < rxP2 S := (psiS_bounds (S := S) _ 1).1

theorem rxP2_SC : SC (rxP2 S) := SC_psi (InR_Om_succ 1) _

/-- **`ψ₂(P₂) = P₂`.** -/
theorem rxP2_fix : S.psi (rxP2 S) (Om (1 + 1)) = rxP2 S := by
  have hle : S.psi (rxP2 S) (Om (1 + 1)) ≤ rxP2 S := (psi_mono (InR_Om_succ 1) rxP2_lt.le).1
  refine le_antisymm hle ?_
  have hsub : S.CSet (Om (1 + 1)) (S.psi (rxP2 S) (Om (1 + 1))) ⊆
      S.CSet (rxP2 S) (S.psi (rxP2 S) (Om (1 + 1))) := by
    intro x hx
    induction hx with
    | small h => exact CSet.of_lt h
    | zero => exact CSet.zero_mem _ _
    | inacc n => exact CSet.I_mem _ _ n
    | inaccW => exact CSet.Iw_mem _ _
    | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
    | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy
    | om _ ih => exact CSet.Om_mem ih
    | @coll π y hπ _ _ ihπ ihy =>
      have hy : y.1 < rxP2 S := (lt_psi_of_mem (InR_Om_succ 1) ihy y.2).trans_le hle
      exact CSet.psi_mem hy hπ ihπ ihy
  exact psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => lt_psi_of_mem (InR_Om_succ 1) (hsub hx) hx2

/-- `ψ₂(e) ≥ P₂` for `e ≥ P₂`. -/
theorem rxP2_le_psi {e : Ordinal.{0}} (he : rxP2 S ≤ e) : rxP2 S ≤ S.psi e (Om (1 + 1)) := by
  have := (psi_mono (S := S) (InR_Om_succ 1) he).1
  rwa [rxP2_fix] at this

/-- A strongly critical ordinal is not below `2`. -/
theorem rxSC_not_lt_two {x : Ordinal.{0}} (hS : SC x) : ¬ x < 1 + 1 := fun h => by
  have h2 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  exact absurd ((Lw.lw_omega_lt_SC hS).trans (h.trans h2)) (lt_irrefl _)

/-- A strongly critical fixed point of `Ω` is not below `Ω₂`. -/
theorem rxFix_not_lt {x : Ordinal.{0}} (hS : SC x) (hfix : Om x = x) : ¬ x < Om (1 + 1) := fun h => by
  rw [← hfix] at h
  exact rxSC_not_lt_two hS (Om_lt_Om.1 h)

/-- A subscript `Ω_{s+1} ≠ Ω₁` with `ψ_{Ω_{s+1}}(e) < Ω₂` is `Ω₂`. -/
theorem rxSub_two {s e : Ordinal.{0}} (hs1 : Om (s + 1) ≠ Om 1)
    (h : S.psi e (Om (s + 1)) < Om (1 + 1)) : s = 1 := by
  have h1 : s < 1 + 1 := Om_lt_Om.1 ((psiS_bounds (S := S) e s).1.trans h)
  have h2 : s ≤ 1 := Order.lt_add_one_iff.1 h1
  have h0 : s ≠ 0 := fun h0 => hs1 (by rw [h0, zero_add])
  exact le_antisymm h2 (Order.one_le_iff_ne_zero.2 h0)

/-- **A code `x ≤ α` over `T ≤ ψ₂(α)` lies in `Cl(α, ψ₂(α))`.** -/
theorem rxN {T : Ordinal.{0}} {x : Ordinal.{0}} (hx : RxC S T x) :
    ∀ α, x ≤ α → T ≤ S.psi α (Om (1 + 1)) → x ∈ S.CSet α (S.psi α (Om (1 + 1))) := by
  induction hx with
  | small h => exact fun α _ hT => CSet.of_lt (h.trans_le hT)
  | om => exact fun α _ _ => CSet.Om_mem (CSet.one_mem _ _)
  | @psi d _ hlt ih =>
    intro α hx hT
    have hdα : d < α := hlt.trans_le hx
    exact CSet.psi_mem hdα (InR_Om_succ 1) (mxOm2_mem _ _) (ih α hdα.le hT)
  | add _ _ ihx ihy =>
    exact fun α hx hT => CSet.add_mem (ihx α (le_self_add.trans hx) hT) (ihy α (le_add_self.trans hx) hT)
  | phi _ _ ihx ihy =>
    exact fun α hx hT => CSet.phi_mem (ihx α ((left_le_veblen _ _).trans hx) hT)
      (ihy α ((right_le_veblen _ _).trans hx) hT)

/-- **Every code `e < Ω₂` over `T ≤ Ω₁` is a normal argument**: `e < ψ₂(e)`. -/
theorem rxNorm {T e : Ordinal.{0}} (he : RxC S T e) (he2 : e < Om (1 + 1)) (hT : T ≤ Om 1) :
    e < S.psi e (Om (1 + 1)) :=
  lt_psi_of_mem (InR_Om_succ 1) (rxN he e le_rfl (hT.trans (psiS_bounds (S := S) e 1).1.le)) he2

/-- **The codes over `T ≤ Ω₁` are below `P₂`.** -/
theorem rxLt_P2 {T x : Ordinal.{0}} (hT : T ≤ Om 1) (hx : RxC S T x) : x < rxP2 S := by
  have hP := rxP2_SC (S := S)
  induction hx with
  | small h => exact (h.trans_le hT).trans rxP2_gt
  | om => exact rxP2_gt
  | @psi d _ _ ih =>
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (ih.trans rxP2_lt) (CSet.of_lt ih)
  | add _ _ ihx ihy => exact hP.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hP.2 _ ihx _ ihy

/-- **A member of `HCl S a T` below `Ω₂` is a code over `T`, or `≥ P₂`.** -/
theorem rxHCl {a T x : Ordinal.{0}} (hT0 : 0 < T) (hT1 : T ≤ Om 1) (hx : HCl S a T x) :
    x < Om (1 + 1) → RxC S T x ∨ rxP2 S ≤ x := by
  induction hx with
  | small h => exact fun _ => Or.inl (RxC.small h)
  | zero => exact fun _ => Or.inl (RxC.zero hT0)
  | inacc n => exact fun h => absurd h (rxFix_not_lt (SC_I (S := S) n) (Om_I n))
  | inaccW => exact fun h => absurd h (rxFix_not_lt (SC_Iw (S := S)) S.Om_Iw)
  | @add u v _ _ ihu ihv =>
    intro h
    rcases ihu (lt_of_le_of_lt le_self_add h) with hu | hu
    · rcases ihv (lt_of_le_of_lt le_add_self h) with hv | hv
      · exact Or.inl (RxC.add hu hv)
      · exact Or.inr (hv.trans le_add_self)
    · exact Or.inr (hu.trans le_self_add)
  | @phi u v _ _ ihu ihv =>
    intro h
    rcases ihu (lt_of_le_of_lt (left_le_veblen u v) h) with hu | hu
    · rcases ihv (lt_of_le_of_lt (right_le_veblen u v) h) with hv | hv
      · exact Or.inl (RxC.phi hu hv)
      · exact Or.inr (hv.trans (right_le_veblen u v))
    · exact Or.inr (hu.trans (left_le_veblen u v))
  | @om y _ _ =>
    intro h
    have h2 : y < 1 + 1 := Om_lt_Om.1 h
    rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff] at h0; rw [h0, Om_zero]; exact Or.inl (RxC.zero hT0)
    · rw [h1]; exact Or.inl RxC.om
  | @coll π e hπ hπ1 _ _ _ _ ihe =>
    intro h
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · exact absurd h (rxFix_not_lt (SC_psi (InR_I n) e) (Om_psiI e n))
    · obtain rfl := rxSub_two hπ1 h
      by_cases he2 : Om (1 + 1) ≤ e
      · have := (psi_mono (S := S) (InR_Om_succ 1) he2).1
        exact Or.inr this
      · have he2' : e < Om (1 + 1) := not_le.1 he2
        rcases ihe he2' with hR | hP
        · exact Or.inl (RxC.psi hR (rxNorm hR he2' hT1))
        · exact Or.inr (rxP2_le_psi hP)

/-- **The tail of a member of the hull**: for `P₂ ∣ Â` and `Â ≤ e < Â + y ≤ Â + P₂`, `e − Â` is a code over `T`. -/
theorem rxTail {a T Â y e : Ordinal.{0}} (hT0 : 0 < T) (hT1 : T ≤ Om 1) (hdvd : rxP2 S ∣ Â)
    (hy : y ≤ rxP2 S) (he : HCl S a T e) (h1 : Â ≤ e) (h2 : e < Â + y) :
    RxC S T (e - Â) ∧ e - Â < y := by
  have hG := rxP2_SC (S := S)
  have e1 : e = Â + (e - Â) := (Ordinal.add_sub_cancel_of_le h1).symm
  have hlt : e - Â < y := by
    rw [e1] at h2; exact (add_lt_add_iff_left _).1 h2
  have hm : e % rxP2 S = e - Â := by
    conv_lhs => rw [e1]
    rw [ldModK_add_lt hG Â (hlt.trans_le hy), Ordinal.mod_eq_zero_of_dvd hdvd, zero_add]
  refine ⟨?_, hlt⟩
  have hmod := ruHCl_modK hG he
  have hlt2 : e % rxP2 S < rxP2 S := Ordinal.mod_lt e hG.1.ne'
  rw [← hm]
  rcases rxHCl hT0 hT1 hmod (hlt2.trans rxP2_lt) with h | h
  · exact h
  · exact absurd hlt2 (not_lt.2 h)

/-- `P₂ ∣ A_η + θ·x`. -/
theorem rxDvd (η x : Ordinal.{0}) : rxP2 S ∣ ConjT.Aη S η + ConjT.th S * x := by
  have hG := rxP2_SC (S := S)
  have hW2 : Om (1 + 1 : Ordinal.{0}) ≤ Om ω := by
    refine (Om_lt_Om.2 ?_).le
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  have hθ : rxP2 S ∣ ConjT.th S := by
    rw [← gg_SC_eps hG, ← gg_SC_eps (ConjT.SC_th S)]
    exact opow_dvd_opow ω (psi_mono (S := S) (InR_Om_succ 1) hW2).1
  have hW : rxP2 S ∣ Om ω := by
    rw [← gg_SC_eps hG, ← gg_SC_eps (SC_Om (omega0_ne_zero : (ω : Ordinal.{0}) ≠ 0))]
    exact opow_dvd_opow ω (rxP2_lt.le.trans hW2)
  unfold ConjT.Aη
  exact dvd_add (dvd_add hW (hθ.mul_right _)) (hθ.mul_right _)

/-- **The codes over `2` are cofinal in `P₂`.** -/
theorem rxCof {ζ : Ordinal.{0}} (h : ζ < rxP2 S) : ∃ w, RxC S 2 w ∧ ζ ≤ w ∧ w < rxP2 S := by
  have h2 : (2 : Ordinal.{0}) ≤ Om 1 := ruTwo_le Ph.ph_SC_Om1
  have hcl : ∀ w, RxC S 2 w → w < rxP2 S := fun w hw => rxLt_P2 h2 hw
  by_contra hno
  push Not at hno
  have hall : ∀ w, RxC S 2 w → w < ζ := fun w hw => by
    by_contra hc
    push Not at hc
    exact absurd (hcl w hw) (not_lt.2 (hno w hw hc))
  have hne : ({w | RxC S 2 w} : Set Ordinal.{0}).Nonempty := ⟨0, RxC.zero two_pos⟩
  have hbdd : BddAbove ({w | RxC S 2 w} : Set Ordinal.{0}) := ⟨ζ, fun w hw => (hall w hw).le⟩
  set σ := sSup {w | RxC S (2 : Ordinal.{0}) w} with hσ
  have hsζ : σ ≤ ζ := csSup_le hne fun w hw => (hall w hw).le
  have hcode : ∀ x ∈ S.CSet (Om (1 + 1)) σ, x < Om (1 + 1) → ∃ w, RxC S 2 w ∧ x ≤ w := by
    intro x hx
    induction hx with
    | small h =>
      intro _
      obtain ⟨w, hw, hxw⟩ := exists_lt_of_lt_csSup hne h
      exact ⟨w, hw, hxw.le⟩
    | zero => exact fun _ => ⟨0, RxC.zero two_pos, le_rfl⟩
    | inacc n => exact fun h => absurd h (rxFix_not_lt (SC_I (S := S) n) (Om_I n))
    | inaccW => exact fun h => absurd h (rxFix_not_lt (SC_Iw (S := S)) S.Om_Iw)
    | @add u v _ _ ihu ihv =>
      intro h
      obtain ⟨w1, hw1, hu⟩ := ihu (lt_of_le_of_lt le_self_add h)
      obtain ⟨w2, hw2, hv⟩ := ihv (lt_of_le_of_lt le_add_self h)
      exact ⟨w1 + w2, RxC.add hw1 hw2, add_le_add hu hv⟩
    | @phi u v _ _ ihu ihv =>
      intro h
      obtain ⟨w1, hw1, hu⟩ := ihu (lt_of_le_of_lt (left_le_veblen u v) h)
      obtain ⟨w2, hw2, hv⟩ := ihv (lt_of_le_of_lt (right_le_veblen u v) h)
      refine ⟨veblen w1 w2, RxC.phi hw1 hw2, ?_⟩
      exact (veblen_left_monotone v hu).trans (veblen_le_veblen_iff_right.2 hv)
    | @om y _ _ =>
      intro h
      have hy : y ≤ 1 := Order.lt_add_one_iff.1 (Om_lt_Om.1 h)
      exact ⟨Om 1, RxC.om, not_lt.1 fun h' => absurd (Om_lt_Om.1 h') (not_lt.2 hy)⟩
    | @coll π y hπ _ _ _ ihy =>
      intro h
      show ∃ w, RxC S 2 w ∧ S.psi y.1 π ≤ w
      change S.psi y.1 π < Om (1 + 1) at h
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exact absurd h (rxFix_not_lt (SC_psi (InR_I n) _) (Om_psiI _ n))
      · rcases eq_or_ne s 0 with rfl | hs0
        · refine ⟨Om 1, RxC.om, ?_⟩
          exact (psi_lt (S := S) (InR_Om_succ 0) y.1).le.trans_eq (by rw [zero_add])
        · have hs1 : Om (s + 1) ≠ Om 1 := fun e => hs0 (by
            have h' : s < 1 := (Om_inj.1 e) ▸ lt_add_one s
            exact Order.lt_one_iff.1 h')
          obtain rfl := rxSub_two hs1 h
          obtain ⟨w, hw, hyw⟩ := ihy y.2
          have hw2 : w < Om (1 + 1) := (hcl w hw).trans rxP2_lt
          exact ⟨_, RxC.psi hw (rxNorm hw hw2 h2), (psi_mono (S := S) (InR_Om_succ 1) hyw).1⟩
  have hP : rxP2 S ≤ σ := by
    refine psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => ?_
    obtain ⟨w, hw, hxw⟩ := hcode x hx hx2
    have hw1 : RxC S 2 (w + 1) := RxC.add hw (RxC.small one_lt_two)
    exact hxw.trans_lt ((lt_add_one w).trans_le (le_csSup hbdd hw1))
  exact absurd (hP.trans hsζ) (not_le.2 h)

end Googology.Trans.PoR.InaccPsi.R2.Rx
