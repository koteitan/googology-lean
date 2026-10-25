import Googology.Trans.PoR.InaccPsi.R2.GqFr

/-!
# The codes of a closure that contain a base: the tools for a code gate at and past `Γ₀`

`G = Γ_{Ω₁+1} = gcG 0`, `GxCl Z {G}` the closure of the ordinals below `Z`, `Ω₁` and the atom `G` under `+` and `φ`.

* `grK = ζ_{Γ₀+1} = evZ Γ₀` (**the new bound of the constant indices**), `gam0_lt_grK`, `grK_lt_gam1`, `grK_lt_Om1`,
  `grK_le_evZ`, `grK_lt_gq1` (**`grK ≤ ζ_{Γ_{x+1}+1} < gq 1 x` at every `ε`-number base `x`**), `gr_gam0_lt_tdK`,
  `grK_lt_tdK` (**`grK < K = ψ_{Ω₁}(Ω_ω)`**), `gr_tdK_le_ups` (**`K ≤ u` for every `υ`-point `u`**);
* `gr_psi0` (**`ψ_{Ω₁}(0) = Γ₀`**), `gr_cst_mem` (**every `α < Γ₁` lies in every hull `C(a, b)` with `0 < a`**);
* the inversions of the closure: `gr_cl_succ` (`s + 1` a code ⇒ `s` a code), `gr_cl_veb1` (`φ(1, t)` a code,
  `Ω₁ < t < φ(1, t)` ⇒ `t` a code), `gr_cl_Gl` (**`G + l` a code over `Z` ⇒ `l < Z`**), `gr_cl_restrict` (codes below
  `N` use no atom `≥ N`), `gr_cl_B` (**a code in `[B, ε_{B+1})` has `B` as a code**), `gr_cl_Bl` (**`φ(1, G + l)` a
  code over `Z`, `l` a limit ⇒ `l < Z`**), `gr_cl_NB` (**`φ(1, ix + 1)` a code ⇒ `φ(1, ix)` a code**).

No new axiom.  New definition: `grK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gp Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd

/-! ## The bound `ζ_{Γ₀+1}` -/

/-- **The bound of the constant indices**: `ζ_{Γ₀+1}`, the least fixed point of `ε` above `Γ₀`. -/
noncomputable def grK : Ordinal.{0} := evZ (gamma 0)

theorem gam0_lt_grK : gamma 0 < grK := lt_evZ _

theorem gr_veb_prin (a b : Ordinal.{0}) : IsPrincipal (· + ·) (veblen a b) := by
  obtain ⟨c, hc⟩ := veblen_mem_range_opow a b
  rw [← hc]; exact isPrincipal_add_omega0_opow c

theorem gr_gam1_fix : veblen 1 (gamma 1 : Ordinal.{0}) = gamma 1 :=
  (Lq.lq_gamma_SC 1).veblen_right (one_lt_omega0.trans (omega0_lt_gamma 1))

/-- `Γ₀ < ψ_{Ω₁}(Ω_ω)`-type bound: `ζ_{Γ₀+1} < Γ₁`. -/
theorem grK_lt_gam1 : grK < gamma 1 := by
  have h2 : (2 : Ordinal.{0}) < gamma 0 := by
    have : ((2 : ℕ) : Ordinal.{0}) < gamma 0 := natCast_lt_gamma 2
    exact_mod_cast this
  have hfix0 : veblen 2 (gamma 0) = gamma 0 := (Lq.lq_gamma_SC 0).veblen_right h2
  have h21 : (2 : Ordinal.{0}) < gamma 1 := h2.trans (gamma_lt_gamma.2 zero_lt_one)
  have hfix1 : veblen 2 (gamma 1) = gamma 1 := (Lq.lq_gamma_SC 1).veblen_right h21
  have hlt : gamma 0 < veblen 2 (gamma 0 + 1) := by
    conv_lhs => rw [← hfix0]
    exact (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  have hE : Ordinal.epsilon (veblen 2 (gamma 0 + 1)) = veblen 2 (gamma 0 + 1) :=
    veblen_veblen_of_lt one_lt_two _
  have h1 : grK ≤ veblen 2 (gamma 0 + 1) := evZ_le hlt hE
  refine h1.trans_lt ?_
  conv_rhs => rw [← hfix1]
  refine (veblen_lt_veblen_iff_right).2 ?_
  exact (Lq.lq_gamma_SC 1).add_one_lt (gamma_lt_gamma.2 zero_lt_one)

theorem gr_gam1_lt_Om1 : gamma 1 < Om1 := by
  have hS : SC (Om1) := by rw [Ph.ph_Om1_eq]; exact ph_SC_Om1
  have h0 : Order.succ (gamma 0) < Om1 := by
    rw [Order.succ_eq_add_one]; exact hS.add_one_lt gq_gam_lt_Om1
  have hit : ∀ n : ℕ, (fun a : Ordinal.{0} => veblen a 0)^[n] (Order.succ (gamma 0)) < Om1 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => rw [Function.iterate_succ_apply']; exact hS.2 _ ih 0 hS.1
  have e1 : (1 : Ordinal.{0}) = Order.succ 0 := by rw [Order.succ_eq_add_one, zero_add]
  rw [e1, gamma_succ_eq_nfp, ← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_lt_omega_one hit

theorem grK_lt_Om1 : grK < Om1 := grK_lt_gam1.trans gr_gam1_lt_Om1

theorem grK_lt_Om1' : grK < Om 1 := by rw [← Br.Om1_eq]; exact grK_lt_Om1

theorem grK_le_evZ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : grK ≤ evZ (lgG x) :=
  evZ_le ((gqK_le_lgG hx hx1).trans_lt (lt_evZ _)) (epsilon_evZ _)

/-- **`ζ_{Γ₀+1} < gq 1 x`** at every `ε`-number base `x`. -/
theorem grK_lt_gq1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : grK < gq 1 x :=
  (grK_le_evZ hx hx1).trans_lt (gn_evZG_lt1 hx hx1)

theorem gr_gam1_le_SC {s : Ordinal.{0}} (hs : SC s) (h0 : gamma 0 < s) : gamma 1 ≤ s := by
  obtain ⟨o, rfl⟩ := Lq.lq_SC_gamma hs
  have ho : 0 < o := gamma_lt_gamma.1 h0
  exact gamma_le_gamma.2 (Order.one_le_iff_pos.2 ho)

/-- **`ψ_{Ω₁}(0) = Γ₀`.** -/
theorem gr_psi0 (S : InaccSeq.{0}) : S.psi 0 (Om 1) = gamma 0 :=
  le_antisymm (Bt.psi_le_of_key (Lq.lq_gamma_SC 0) fun _ _ he => absurd he (not_lt.2 zero_le))
    (Ta.taGam_le_SC (SC_psi Low.InR_Om_one 0))

/-- `Γ₀ < K = ψ_{Ω₁}(Ω_ω)`. -/
theorem gr_gam0_lt_tdK (S : InaccSeq.{0}) : gamma 0 < Td.tdK S := by
  rw [← gr_psi0 S]
  exact psi_lt_psi_of_mem Low.InR_Om_one (Om_pos omega0_ne_zero) (CSet.zero_mem _ _)

/-- **`ζ_{Γ₀+1} < K`.** -/
theorem grK_lt_tdK (S : InaccSeq.{0}) : grK < Td.tdK S :=
  grK_lt_gam1.trans_le (gr_gam1_le_SC Td.tdK_SC (gr_gam0_lt_tdK S))

/-- **`K ≤ u` for every `υ`-point `u`**: a `υ`-point below `P(Ω_ω)` is `P(η) ≥ ψ_{Ω₁}(Ω_ω)`. -/
theorem gr_tdK_le_ups (S : InaccSeq.{0}) {u : Ordinal.{0}} (hu : UpsPt u) : Td.tdK S ≤ u := by
  obtain ⟨ι, hι, rfl⟩ := upsPt_iff_upsilon.1 hu
  have hK : ∀ η, Td.tdK S ≤ Pv S η := fun η =>
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : Om ω ≤ Om ω + ConjT.th S * η)).1
  rcases lt_or_ge (upsilon ι) (Pv S (Om ω)) with h | h
  · rw [← Cd.cdEta_pv (S := S) hι.ne' h]; exact hK _
  · exact (hK _).trans h

theorem gr_tdK_le_Pv (S : InaccSeq.{0}) (η : Ordinal.{0}) : Td.tdK S ≤ Pv S η :=
  (psi_mono (S := S) Low.InR_Om_one (le_self_add : Om ω ≤ Om ω + ConjT.th S * η)).1

/-- **Every `α < Γ₁` lies in every hull `C(a, b)` with `0 < a`** (built from `0` and `Γ₀ = ψ_{Ω₁}(0)` by `+`, `φ`). -/
theorem gr_cst_mem {S : InaccSeq.{0}} {a : Ordinal.{0}} (ha : 0 < a) (b : Ordinal.{0}) :
    ∀ α : Ordinal.{0}, α < gamma 1 → α ∈ S.CSet a b := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  rcases eq_or_ne α 0 with rfl | h0
  · exact CSet.zero_mem _ _
  by_cases hE : ω ^ α = α
  · by_cases hng : α ∈ range gamma
    · obtain ⟨o, rfl⟩ := hng
      have ho : o < 1 := gamma_lt_gamma.1 hα
      rw [Order.lt_one_iff] at ho
      rw [show o = 0 from ho, ← gr_psi0 S]
      exact CSet.psi_mem ha Low.InR_Om_one (CSet.Om_mem (CSet.one_mem _ _)) (CSet.zero_mem _ _)
    have h1 : invVeblen₁ α < α := invVeblen₁_lt_iff.2 ⟨h0, hng⟩
    have h2 : invVeblen₂ α < α := by have := invVeblen₂_lt α; rwa [hE] at this
    have e := veblen_invVeblen₁_invVeblen₂ α
    rw [hE] at e
    rw [← e]
    exact CSet.phi_mem (IH _ h1 (h1.trans hα)) (IH _ h2 (h2.trans hα))
  · have hL : log ω α < α := by
      refine lt_of_le_of_ne (log_le_self ω α) fun e => hE ?_
      have h1 : ω ^ α ≤ α := by have := opow_log_le_self ω h0; rwa [e] at this
      exact le_antisymm h1 (right_le_opow α one_lt_omega0)
    have hw : ω ^ log ω α ∈ S.CSet a b := by
      have := CSet.phi_mem (CSet.zero_mem (S := S) a b) (IH _ hL (hL.trans hα))
      rwa [veblen_zero_apply] at this
    have hwd : ω ^ log ω α ≤ α := opow_log_le_self ω h0
    have hdr : ω ^ log ω α + (α - ω ^ log ω α) = α := Ordinal.add_sub_cancel_of_le hwd
    rcases (Ordinal.sub_le_self α (ω ^ log ω α)).lt_or_eq with hrd | hrd
    · rw [← hdr]; exact CSet.add_mem hw (IH _ hrd (hrd.trans hα))
    · exfalso
      have h1 : ω ^ log ω α + α = α := by
        conv_rhs => rw [← hdr]
        rw [hrd]
      have h2 := add_eq_right_iff_mul_omega0_le.1 h1
      rw [← opow_succ] at h2
      exact absurd (lt_opow_succ_log_self one_lt_omega0 α) (not_lt.2 h2)

theorem gr_cst_mem_K {S : InaccSeq.{0}} {a : Ordinal.{0}} (ha : 0 < a) (b : Ordinal.{0}) {α : Ordinal.{0}}
    (hα : α < grK) : α ∈ S.CSet a b := gr_cst_mem ha b α (hα.trans grK_lt_gam1)

/-! ## Inversions of the closure -/

section Inv

variable {Z : Ordinal.{0}}

theorem gr_G_inE : InE (gcG 0) := Low.opow_eq_self_of_SC (gcG_SC 0)

theorem gr_G_prin : IsPrincipal (· + ·) (gcG 0) := (gcG_SC 0).isPrincipal

theorem gr_GxAt : GxAt ({gcG 0} : Set Ordinal.{0}) := by
  intro s hs
  rw [Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨gcG_SC 0, gcG_Om1_lt 0⟩

/-- A principal `G + l` with `l < Ω₁` has `l = 0`. -/
theorem gr_Gl_prin {l : Ordinal.{0}} (hl : l < Om 1) (h : IsPrincipal (· + ·) (gcG 0 + l)) : l = 0 := by
  by_contra h0
  have hGl : gcG 0 < gcG 0 + l := lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0)
  have h2 : gcG 0 + gcG 0 < gcG 0 + l := h hGl hGl
  have h3 : gcG 0 < l := (add_lt_add_iff_left _).1 h2
  exact absurd (h3.trans hl) (not_lt.2 (gcG_Om1_lt 0).le)

/-- **`s + 1` a code ⇒ `s` a code.** -/
theorem gr_cl_succ (hZ : SC Z) {s : Ordinal.{0}} (h : GxCl Z {gcG 0} (s + 1)) : GxCl Z {gcG 0} s := by
  suffices H : ∀ y, GxCl Z {gcG 0} y → ∀ s, y = s + 1 → GxCl Z {gcG 0} s from H _ h s rfl
  intro y hy
  induction hy with
  | small h =>
    intro s e
    rw [e] at h
    exact GxCl.small ((lt_add_one s).trans h)
  | om => intro s e; exact absurd e (Om_ne_add_one 1 s)
  | atom hs =>
    intro s e
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at e
    exact absurd e ((gcG_SC 0).ne_add_one s)
  | @add x y hx hy ihx ihy =>
    intro s e
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at e; exact ihx s e
    · obtain ⟨t, rfl, rfl⟩ := add_eq_add_one e hy0
      exact GxCl.add hx (ihy t rfl)
  | phi _ _ _ _ =>
    intro s e
    rw [veblen_eq_add_one e]
    exact GxCl.zero hZ.1

/-- **`φ(1, t)` a code with `Ω₁ < t < φ(1, t)` ⇒ `t` a code.** -/
theorem gr_cl_veb1 (hZ1 : Z ≤ Om 1) {t : Ordinal.{0}} (hOt : Om 1 < t) (ht : t < veblen 1 t)
    (h : GxCl Z {gcG 0} (veblen 1 t)) : GxCl Z {gcG 0} t := by
  have hP : IsPrincipal (· + ·) (veblen 1 t) := gr_veb_prin 1 t
  have hPE : InE (veblen 1 t) := gg_veblen_eps one_ne_zero
  have hnot : veblen 1 (veblen 1 t) ≠ veblen 1 t := fun e =>
    absurd ((veblen_inj).1 e) (ne_of_gt ht)
  suffices H : ∀ y, GxCl Z {gcG 0} y → y = veblen 1 t → GxCl Z {gcG 0} t from H _ h rfl
  intro y hy
  induction hy with
  | small h =>
    intro e
    rw [e] at h
    exact absurd ((hOt.trans_le (right_le_veblen 1 t)).trans (h.trans_le hZ1)) (lt_irrefl _)
  | om =>
    intro e
    exact absurd (hOt.trans_le (right_le_veblen 1 t)) (by rw [← e]; exact lt_irrefl _)
  | atom hs =>
    intro e
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at e
    have hfix : veblen 1 (gcG 0) = gcG 0 :=
      (gcG_SC 0).veblen_right (one_lt_omega0.trans (omega0_lt_inE gr_G_inE))
    rw [e] at hfix
    exact absurd hfix hnot
  | @add x y _ _ ihx ihy =>
    intro e
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at e; exact ihx e
    · rcases (show y ≤ veblen 1 t from e ▸ le_add_self).lt_or_eq with hyl | hyl
      · exfalso
        rcases (show x ≤ veblen 1 t from e ▸ le_self_add).lt_or_eq with hxl | hxl
        · exact absurd e (hP hxl hyl).ne
        · rw [hxl] at e
          have : veblen 1 t < veblen 1 t + y := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hy0)
          rw [e] at this
          exact lt_irrefl _ this
      · exact ihy hyl
  | @phi a b _ hb _ ihb =>
    intro e
    rcases lt_trichotomy a 1 with ha | rfl | ha
    · rw [Order.lt_one_iff] at ha
      subst ha
      rw [veblen_zero_apply] at e
      have e2 : ω ^ b = ω ^ veblen 1 t := by rw [e, hPE]
      have e3 : b = veblen 1 t := le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 e2.le)
        ((opow_le_opow_iff_right one_lt_omega0).1 e2.ge)
      exact ihb e3
    · rw [(veblen_inj).1 e] at hb; exact hb
    · exfalso
      have := veblen_veblen_of_lt ha b
      rw [e] at this
      exact hnot this

/-- **`G + l` a code over a strongly critical `Z ≤ Ω₁`, `l < Ω₁` ⇒ `l < Z`.** -/
theorem gr_cl_Gl (hZ : SC Z) (hZ1 : Z ≤ Om 1) {l : Ordinal.{0}} (hl : l < Om 1)
    (h : GxCl Z {gcG 0} (gcG 0 + l)) : l < Z := by
  have hGO := gcG_Om1_lt 0
  suffices H : ∀ y, GxCl Z {gcG 0} y → ∀ l, l < Om 1 → y = gcG 0 + l → l < Z from H _ h l hl rfl
  intro y hy
  induction hy with
  | small h =>
    intro l _ e
    rw [e] at h
    exact absurd ((hGO.trans_le le_self_add).trans (h.trans_le hZ1)) (lt_irrefl _)
  | om =>
    intro l _ e
    exact absurd (hGO.trans_le le_self_add) (by rw [← e]; exact lt_irrefl _)
  | atom hs =>
    intro l _ e
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at e
    have : l = 0 := by
      have e' : gcG 0 + l = gcG 0 + 0 := by rw [← e, add_zero]
      exact (add_left_cancel_iff).1 e'
    rw [this]; exact hZ.1
  | @add x y hx hy ihx ihy =>
    intro l hl e
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at e; exact ihx l hl e
    rcases lt_or_ge y (gcG 0) with hyG | hyG
    · -- `x = G + l₁`, `l = l₁ + y`
      have hxG : gcG 0 ≤ x := by
        by_contra hxG
        push Not at hxG
        have : x + y < gcG 0 := gr_G_prin hxG hyG
        rw [e] at this
        exact absurd (this.trans_le le_self_add) (lt_irrefl _)
      obtain ⟨l1, rfl⟩ := exists_add_of_le hxG
      rw [add_assoc] at e
      have e' : l1 + y = l := (add_left_cancel_iff).1 e
      have hl1 : l1 < Om 1 := lt_of_le_of_lt (e' ▸ le_self_add) hl
      have h1 := ihx l1 hl1 rfl
      have hyl : y < Om 1 := lt_of_le_of_lt (e' ▸ le_add_self) hl
      have h2 : y < Z := GxCl.lt_of_lt_Om1 hZ gr_GxAt hy hyl
      rw [← e']; exact hZ.isPrincipal h1 h2
    · -- `x < G`, `y = G + l`
      have hxG : x < gcG 0 := by
        by_contra hxG
        push Not at hxG
        have h1 : gcG 0 + gcG 0 ≤ x + y := add_le_add hxG hyG
        rw [e] at h1
        have h2 : gcG 0 + l < gcG 0 + gcG 0 := (add_lt_add_iff_left _).2 (hl.trans hGO)
        exact absurd (h1.trans_lt h2) (lt_irrefl _)
      obtain ⟨l2, rfl⟩ := exists_add_of_le hyG
      have hxG' : x + gcG 0 = gcG 0 := gr_G_prin.add_eq_right hxG
      rw [← add_assoc, hxG'] at e
      have e' : l2 = l := (add_left_cancel_iff).1 e
      rw [← e']; exact ihy l2 (e' ▸ hl) rfl
  | @phi a b _ _ _ _ =>
    intro l hl e
    have h0 : l = 0 := gr_Gl_prin hl (e ▸ gr_veb_prin a b)
    rw [h0]; exact hZ.1

/-- **Codes below `N` use no atom `≥ N`.** -/
theorem gr_cl_restrict {At : Set Ordinal.{0}} {N y : Ordinal.{0}} (hAt : ∀ s ∈ At, s = gcG 0 ∨ N ≤ s)
    (h : GxCl Z At y) (hy : y < N) : GxCl Z {gcG 0} y := by
  induction h with
  | small h => exact GxCl.small h
  | om => exact GxCl.om
  | @atom s hs =>
    rcases hAt s hs with e | e
    · exact GxCl.atom (Set.mem_singleton_iff.2 e)
    · exact absurd (hy.trans_le e) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact GxCl.add (ihx (lt_of_le_of_lt le_self_add hy)) (ihy (lt_of_le_of_lt le_add_self hy))
  | @phi x y _ _ ihx ihy =>
    exact GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) hy)) (ihy (lt_of_le_of_lt (right_le_veblen x y) hy))

/-- **A code in `[B, ε_{B+1})` has `B` as a code** (`B ≥ G` an `ε`-number). -/
theorem gr_cl_B (hZ1 : Z ≤ Om 1) {B : Ordinal.{0}} (hB : InE B) (hGB : gcG 0 ≤ B) {y : Ordinal.{0}}
    (h : GxCl Z {gcG 0} y) (hBy : B ≤ y) (hyN : y < eN B) : GxCl Z {gcG 0} B := by
  have hGO := gcG_Om1_lt 0
  have hBp : IsPrincipal (· + ·) B := by
    have := isPrincipal_add_omega0_opow B
    rwa [hB] at this
  induction h with
  | small h => exact absurd ((hGO.trans_le hGB).trans_le hBy) (not_lt.2 (h.le.trans hZ1))
  | om => exact absurd (hGO.trans_le hGB) (not_lt.2 hBy)
  | @atom s hs =>
    rw [Set.mem_singleton_iff] at hs
    rw [hs] at hBy
    rw [le_antisymm hBy hGB]
    exact GxCl.atom (Set.mem_singleton_iff.2 rfl)
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y B with hyB | hyB
    · rcases lt_or_ge x B with hxB | hxB
      · exact absurd (hBp hxB hyB) (not_lt.2 hBy)
      · exact ihx hxB (lt_of_le_of_lt le_self_add hyN)
    · exact ihy hyB (lt_of_le_of_lt le_add_self hyN)
  | @phi a b _ hb _ ihb =>
    rcases eq_or_ne a 0 with rfl | ha
    · rw [veblen_zero_apply] at hBy hyN
      rcases lt_or_ge b B with hbB | hbB
      · exfalso
        have : ω ^ b < ω ^ B := (opow_lt_opow_iff_right one_lt_omega0).2 hbB
        rw [hB] at this
        exact absurd hBy (not_le.2 this)
      · exact ihb hbB ((right_le_opow b one_lt_omega0).trans_lt hyN)
    · have hE : InE (veblen a b) := gg_veblen_eps ha
      rcases hBy.lt_or_eq with hlt | heq
      · exact absurd hyN (not_lt.2 (eN_le hlt hE))
      · rw [heq]; exact GxCl.phi ‹_› hb

/-- **`φ(1, G + l)` a code over `Z`, `0 < l < Ω₁` ⇒ `l < Z`.** -/
theorem gr_cl_Bl (hZ : SC Z) (hZ1 : Z ≤ Om 1) {l : Ordinal.{0}} (hl0 : l ≠ 0) (hl : l < Om 1)
    (h : GxCl Z {gcG 0} (veblen 1 (gcG 0 + l))) : l < Z := by
  have hOt : Om 1 < gcG 0 + l := (gcG_Om1_lt 0).trans_le le_self_add
  have ht : gcG 0 + l < veblen 1 (gcG 0 + l) := by
    rcases (right_le_veblen 1 (gcG 0 + l)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hp := gr_veb_prin 1 (gcG 0 + l)
      rw [← h1] at hp
      exact hl0 (gr_Gl_prin hl hp)
  exact gr_cl_Gl hZ hZ1 hl (gr_cl_veb1 hZ1 hOt ht h)

/-- **`φ(1, ix + 1)` a code ⇒ `φ(1, ix)` a code** (`Ω₁ ≤ ix`). -/
theorem gr_cl_NB (hZ : SC Z) (hZ1 : Z ≤ Om 1) {ix : Ordinal.{0}} (hix : Om 1 ≤ ix)
    (h : GxCl Z {gcG 0} (veblen 1 (ix + 1))) : GxCl Z {gcG 0} (veblen 1 ix) := by
  have hOt : Om 1 < ix + 1 := hix.trans_lt (lt_add_one ix)
  have ht : ix + 1 < veblen 1 (ix + 1) := by
    rcases (right_le_veblen 1 (ix + 1)).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hE : InE (veblen 1 (ix + 1)) := gg_veblen_eps one_ne_zero
      rw [← h1] at hE
      exact lt_irrefl _ ((ev_isSuccLimit_of_inE hE).add_one_lt (lt_add_one ix))
  have h1 := gr_cl_succ hZ (gr_cl_veb1 hZ1 hOt ht h)
  have h0 : GxCl Z {gcG 0} 1 := by
    have := GxCl.phi (GxCl.zero (At := {gcG 0}) hZ.1) (GxCl.zero (At := {gcG 0}) hZ.1)
    rwa [veblen_zero_apply, opow_zero] at this
  exact GxCl.phi h0 h1

/-- An index `ix` with `G ≤ φ(1, ix)` is at least `Ω₁`. -/
theorem gr_Om1_le_ix {ix : Ordinal.{0}} (h : gcG 0 ≤ veblen 1 ix) : Om 1 ≤ ix := by
  by_contra hlt
  push Not at hlt
  have hS : SC (Om (1 : Ordinal.{0})) := ph_SC_Om1
  have h1 : veblen 1 ix < Om 1 := hS.2 1 (one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC hS))) ix hlt
  exact absurd ((gcG_Om1_lt 0).trans_le h) (not_lt.2 h1.le)

end Inv

/-- The closure conditions on `Z` give `SC Z`. -/
theorem gr_SC_of {Z : Ordinal.{0}} (hZ0 : 0 < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z) : SC Z :=
  ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩

end Googology.Trans.PoR.InaccPsi.R2.Gr
