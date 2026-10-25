import Googology.Trans.PoR.InaccPsi.R2.UiBd

/-!
# `B_{s+1} = ψ_{Ω_{s+1}}(ε_{Ω_{s+1}+1})`, and every strongly critical `v ∈ (Ω_s, B_{s+1})` is `ψ_{Ω_{s+1}}(e)`, `e < E`

`ψ = S.psi · W`, `W = Ω_{s+1}`, `L = Ω_s`, `E = uiE s = ε_{W+1}`, `B = uiB s`.  This is `R2.UcBH` (`s = 1`) for every
`s < ω`:

* `ui_E_eq_veblen` (**`E = φ(1, W + 1)`**), `ui_E_mem` (`E` lies in every hull), `ui_E_dvd`, `ui_psi0_le_SC`
  (**`ψ(0)` is at most every strongly critical point above `L`**), `ui_psi0_lt_B`, `ui_psi_lt_B` (**`ψ(e) < B` for
  every `e < E` with all components below `B`**);
* `ui_psiE_eq_B` (**`ψ(E) = B`**), `ui_own_of_SC_B` (**every strongly critical `v ∈ (L, B)` is `ψ(e)` for an own
  `e < E`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **`E = φ(1, W + 1)`.** -/
theorem ui_E_eq_veblen (s : Ordinal.{0}) : uiE s = veblen 1 ((Om (s + 1)) + 1) := by
  have hfix : ω ^ veblen 1 ((Om (s + 1)) + 1) = veblen 1 ((Om (s + 1)) + 1) := Tp.tpVeblen_fix zero_lt_one
  have hgt : (Om (s + 1)) < veblen 1 ((Om (s + 1)) + 1) := by
    have h1 : veblen 1 (Om (s + 1)) = Om (s + 1) := SC.veblen_right (ui_SC_W s) (ui_one_lt_W s)
    calc ((Om (s + 1)) : Ordinal.{0}) = veblen 1 (Om (s + 1)) := h1.symm
      _ < veblen 1 ((Om (s + 1)) + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  refine le_antisymm (uiE_le hfix hgt) ?_
  have hmem : uiE s ∈ range (veblen 1) := (mem_range_veblen one_ne_zero).2 fun b hb => by
    rw [Order.lt_one_iff] at hb; rw [hb, veblen_zero_apply]; exact (uiE_fix s)
  obtain ⟨k, hk⟩ := hmem
  have hk2 : (Om (s + 1)) < k := by
    by_contra h
    have h1 : veblen 1 k ≤ veblen 1 (Om (s + 1)) := (veblen_le_veblen_iff_right).2 (not_lt.1 h)
    rw [SC.veblen_right (ui_SC_W s) (ui_one_lt_W s), hk] at h1
    exact absurd (uiE_gt s) (not_lt.2 h1)
  rw [← hk]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hk2)

/-- **`E` lies in every hull.** -/
theorem ui_E_mem (hs : s < ω) (a b : Ordinal.{0}) : uiE s ∈ S.CSet a b := by
  rw [ui_E_eq_veblen s]
  exact CSet.phi_mem (CSet.one_mem _ _) (CSet.add_mem (ui_W_mem hs _ _) (CSet.one_mem _ _))

theorem ui_E_dvd {γ : Ordinal.{0}} (hγ : γ < uiE s) : Om (s + 1) ^ (γ + 1) ∣ uiE s := by
  have h1 : γ + 1 < uiE s := (ui_E_indec s) hγ ((ui_one_lt_W s).trans (uiE_gt s))
  rw [(ui_W_eq s)]
  conv_rhs => rw [← (uiE_fix s)]
  exact opow_dvd_opow _ ((ui_E_mulPrin s) (uiE_gt s) h1).le

theorem ui_psi0_le_SC (hs : s < ω) {v : Ordinal.{0}} (hv : SC v) (hLv : Om s < v) : S.psi 0 (Om (s + 1)) ≤ v := by
  refine psi_le_of_good (ui_W_mem hs _ _) fun x hx => ?_
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => hv.1
  | inacc n => exact fun h => absurd (h.trans (ui_W_lt_I hs n)) (lt_irrefl _)
  | inaccW => exact fun h => absurd (h.trans (ui_W_lt_Iw hs)) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro h
    exact hv.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihz (lt_of_le_of_lt le_add_self h))
  | @phi x z _ _ ihx ihz =>
    intro h
    exact hv.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x z) h)) _ (ihz (lt_of_le_of_lt (right_le_veblen x z) h))
  | @om x _ _ =>
    intro h
    exact (Om_le_Om.2 (Order.lt_add_one_iff.1 (Om_lt_Om.1 h))).trans_lt hLv
  | @coll π e _ _ _ _ _ => exact absurd (show e.1 < 0 from e.2) (not_lt.2 zero_le)

theorem ui_psi0_lt_B (hs : s < ω) : S.psi 0 (Om (s + 1)) < uiB s := by
  have h0 : (0 : Ordinal.{0}) < uiE s := (ui_SC_W s).1.trans (uiE_gt s)
  have hfix : uiH s 0 (uiB s) = uiB s := uiB_spec h0 (by rw [uiC_small (ui_SC_W s).1]; exact (uiB_SC s).1)
  have h1 : S.psi 0 (Om (s + 1)) ≤ uiH s 0 0 := ui_psi0_le_SC hs (uiH_SC (s := s) 0 0) (uiH_gt (s := s) 0 0)
  have h := h1.trans_lt ((uiH_lt_iff (s := s) 0).2 (uiB_SC s).1)
  rwa [hfix] at h

/-- **`ψ(e) < B` for every `e < E` with all components below `B`.** -/
theorem ui_psi_lt_B (hs : s < ω) {e : Ordinal.{0}} (he : e < uiE s) (hc : UiLt s (uiB s) e) : S.psi e (Om (s + 1)) <
    uiB s := by
  have he1 : e + 1 < uiE s := (ui_E_indec s) he ((ui_one_lt_W s).trans (uiE_gt s))
  have hW : e < Om (s + 1) ^ (e + 1) :=
    ((isNormal_opow (ui_one_lt_W s)).strictMono.le_apply).trans_lt
      ((opow_lt_opow_iff_right (ui_one_lt_W s)).2 (lt_add_one e))
  have hcl : ∀ j < e + 1, uiC s j < uiB s → ∀ z < uiB s, uiH s j z < uiB s := fun j hj hcj z hz => by
    have hjE : j < uiE s := hj.trans he1
    have := (uiH_lt_iff (s := s) j).2 hz
    rwa [uiB_spec hjE hcj] at this
  have h := (uiCL_UB (S := S) hs (e + 1) he1).1 0 e (uiB s) (dvd_zero _) ((ui_SC_W s).1.trans (uiE_gt s)) (uiB_SC s) hcl
    (ui_psi0_lt_B hs) hW hc
  rwa [zero_add] at h

/-- **`ψ_{W}(ε_{W+1}) = B`.** -/
theorem ui_psiE_eq_B (hs : s < ω) : S.psi (uiE s) (Om (s + 1)) = uiB s := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hB1 : (Om s) < uiB s := uiB_gt s
  apply le_antisymm
  · refine psi_le_of_good (ui_W_mem hs _ _) fun x hx hx2 => ?_
    have hcoll : ∀ e, e < uiE s → e ∈ S.CSet (uiE s) (uiB s) → UiLt s (uiB s) e → S.psi e (Om (s + 1)) < uiB s :=
      fun e he _ hc => ui_psi_lt_B hs he hc
    have h := ui_hull (S := S) hs (uiB_SC s) hB1 (uiB_lt_W s) le_rfl hcoll x hx
    exact (uiLt_small hx2).1 h
  · refine uiB_le ⟨ui_psi_SC _, ui_L_lt_psi _, ?_⟩
    rintro ⟨γ, hγ, hc, hne⟩
    have hown : uiE s ∈ S.CSet (uiE s) (S.psi (uiE s) (Om (s + 1))) := ui_E_mem hs _ _
    have hE0 : uiE s ≠ 0 := ((ui_SC_W s).1.trans (uiE_gt s)).ne'
    exact hne ((ui_fwd_conv (S := S) hs γ hγ).1 (uiE s) hown (ui_E_dvd hγ) hE0 hc)

/-- **Every strongly critical `v ∈ (L, B)` is `ψ(e)` for an own `e < E`.** -/
theorem ui_own_of_SC_B (hs : s < ω) {v : Ordinal.{0}} (hv : SC v) (hv1 : (Om s) < v) (hvB : v < uiB s) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) ∧ e < uiE s ∧ S.psi e (Om (s + 1)) = v := by
  rw [← ui_psiE_eq_B (S := S) hs] at hvB
  obtain ⟨e, hown, he⟩ := ui_own_of_SC hs hv hv1 hvB
  have hownE : uiE s ∈ S.CSet (uiE s) (S.psi (uiE s) (Om (s + 1))) := ui_E_mem hs _ _
  have h := compare_psi (InR_Om_succ s) hown hownE
  rw [he, compare_lt_iff_lt.2 hvB] at h
  exact ⟨e, hown, compare_lt_iff_lt.1 h.symm, he⟩

end Googology.Trans.PoR.InaccPsi.R2.Ui
