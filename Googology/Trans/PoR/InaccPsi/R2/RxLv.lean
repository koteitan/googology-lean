import Googology.Trans.PoR.InaccPsi.R2.RxLE

/-!
# The levels of the shift and its normal forms

`RxE S T` the domain, `rxL S Z At T` the level shift `κ` (`Rx.rxL`), `rxH` the least stage, `rxMs` the measure,
`W = rxW Z At = min(Θ(Ω₂), Ω₁)` (`Θ = gxTh Z At`), `κ = rxL S Z At W`.

* `rxOmW_nat` (`x < Ω_ω ⇒ x < Ω_n` for some `n < ω`), `rxLevel` (**every member `≥ Ω₁` lies in some
  `[Ω_k, Ω_{k+1})`, `1 ≤ k < ω`**), `rxMs_ind` (induction along the measure), `rxNs_lead` (`ω^{log_ω x}` stays at the
  stage of `x`);
* `rxL_small` (`κ x = ruInv x < Ω₂` below `Ω₁`), `rxL_step_lt` (**a bound from the parts**), `rxL_lt_lev`
  (**`x < Ω_{k+1} ⇒ κ x < Ω_{k+2}`**), `rxL_ge_lev` (**`Ω_k ≤ x ⇒ Ω_{k+1} ≤ κ x`**, `k ≥ 1`), `rxL_ne_zero`,
  `rxL_SC`, `rxL_eps`;
* `rxLDecK`, `rxLDecV` (**`κ` on the Cantor and the Veblen normal form**, with the parts in the domain at stages
  not above that of `x`), `rxL_opow` (`κ(ω^ℓ) = ω^{κ ℓ}`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

theorem rxOmW_nat {x : Ordinal.{0}} (h : x < Om ω) : ∃ n : ℕ, x < Om (n : Ordinal.{0}) := by
  by_contra hc
  push Not at hc
  have : Om ω ≤ x := by
    rw [Om_of_ne_zero omega0_ne_zero]
    rw [(Ordinal.isNormal_omega).le_iff_forall_le isSuccLimit_omega0]
    intro b hb
    obtain ⟨n, rfl⟩ := lt_omega0.1 hb
    have h1 := hc (n + 1)
    rw [Om_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)] at h1
    exact (Ordinal.isNormal_omega.strictMono.le_iff_le.2 (by exact_mod_cast Nat.le_succ n)).trans h1
  exact absurd h (not_lt.2 this)

/-- **The level of a member `≥ Ω₁`.** -/
theorem rxLevel {x : Ordinal.{0}} (h1 : Om 1 ≤ x) (hW : x < Om ω) :
    ∃ k : ℕ, 1 ≤ k ∧ Om (k : Ordinal.{0}) ≤ x ∧ x < Om ((k : Ordinal.{0}) + 1) := by
  classical
  have hex := rxOmW_nat hW
  set n0 := Nat.find hex with hn0
  have hspec : x < Om (n0 : Ordinal.{0}) := Nat.find_spec hex
  have hmin : ∀ m < n0, ¬ x < Om (m : Ordinal.{0}) := fun m hm => Nat.find_min hex hm
  have hn0' : 2 ≤ n0 := by
    by_contra h
    push Not at h
    interval_cases n0
    · rw [Nat.cast_zero, Om_zero] at hspec; exact absurd hspec (not_lt.2 zero_le)
    · rw [Nat.cast_one] at hspec; exact absurd hspec (not_lt.2 h1)
  obtain ⟨k, hk⟩ : ∃ k, n0 = k + 1 := ⟨n0 - 1, by omega⟩
  refine ⟨k, by omega, not_lt.1 (hmin k (by omega)), ?_⟩
  rw [hk, Nat.cast_succ] at hspec
  exact hspec

/-- **Induction along the measure.** -/
theorem rxMs_ind {T : Ordinal.{0}} {P : Ordinal.{0} → Prop}
    (h : ∀ x, (∀ y, rxMs S T y < rxMs S T x → P y) → P x) : ∀ x, P x :=
  fun x => (InvImage.wf (rxMs S T) wellFounded_lt).induction x h

/-- **`ω^{log_ω x}` stays at the stage of `x`.** -/
theorem rxNs_lead {T : Ordinal.{0}} {n : ℕ} {x : Ordinal.{0}} (hx : RxNs S T n x) (h0 : x ≠ 0) :
    RxNs S T n (ω ^ log ω x) := by
  have prin : ∀ {m : ℕ} {y : Ordinal.{0}}, RxNs S T m y → ω ^ y = y → RxNs S T m (ω ^ log ω y) := by
    intro m y hy hε
    have e : log ω y = y := by
      conv_lhs => rw [← hε]
      exact log_opow one_lt_omega0 _
    rw [e, hε]; exact hy
  induction hx with
  | @small _ y h => exact RxNs.small ((opow_log_le_self ω h0).trans_lt h)
  | zero => exact absurd rfl h0
  | inacc k => exact prin (RxNs.inacc k) (gg_SC_eps (SC_I k))
  | inaccW => exact prin RxNs.inaccW (gg_SC_eps SC_Iw)
  | omn k =>
    rcases eq_or_ne (k : Ordinal.{0}) 0 with e | e
    · rw [e, Om_zero] at h0; exact absurd rfl h0
    · exact prin (RxNs.omn k) (gg_SC_eps (SC_Om e))
  | @add m u v hu hv ihu ihv =>
    rcases ggLog_add u v with e | e
    · rcases eq_or_ne u 0 with hu0 | hu0
      · have hv0 : v ≠ 0 := by rintro rfl; rw [hu0, add_zero] at h0; exact h0 rfl
        have e' : log ω (u + v) = log ω v := by rw [hu0, zero_add]
        rw [e']; exact RxNs.up (ihv hv0)
      · rw [e]; exact RxNs.up (ihu hu0)
    · rcases eq_or_ne v 0 with hv0 | hv0
      · have e' : log ω (u + v) = log ω u := by rw [hv0, add_zero]
        have hu0 : u ≠ 0 := by rintro rfl; rw [hv0, add_zero] at h0; exact h0 rfl
        rw [e']; exact RxNs.up (ihu hu0)
      · rw [e]; exact RxNs.up (ihv hv0)
  | @phi m a b ha hb _ _ =>
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply, log_opow one_lt_omega0]
      have := RxNs.phi (RxNs.zero (S := S) (T := T) (n := m)) hb
      rwa [veblen_zero_apply] at this
    · exact prin (RxNs.phi ha hb) (gg_veblen_eps ha0)
  | @om m p hp _ =>
    rcases eq_or_ne p 0 with rfl | e
    · rw [Om_zero] at h0; exact absurd rfl h0
    · exact prin (RxNs.om hp) (gg_SC_eps (SC_Om e))
  | @psiN m d k hk hd hdn _ =>
    exact prin (RxNs.psiN k hk hd hdn) (gg_SC_eps (SC_psi (InR_Om_succ _) d))
  | @psiG m π d hπ hπ1 hπN hdN hdn _ _ =>
    exact prin (RxNs.psiG hπ hπ1 hπN hdN hdn) (gg_SC_eps (SC_psi hπ d))
  | up _ ih => exact RxNs.up (ih h0)

/-- `ω^{log_ω x}` of a member is a member at a stage not above that of `x`. -/
theorem rxE_lead {T x : Ordinal.{0}} (hx : RxE S T x) (h0 : x ≠ 0) :
    RxE S T (ω ^ log ω x) ∧ rxH S T (ω ^ log ω x) ≤ rxH S T x := by
  have hs := rxNs_lead (rxH_spec hx.1) h0
  have hl := (rxCDec x hx.2.1).2
  have hop : ω ^ log ω x ∈ S.CSet (Om ω) (ConjT.th S) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hl; rwa [veblen_zero_apply] at this
  exact ⟨⟨rxN_iff_stage.2 ⟨_, hs⟩, hop, (opow_log_le_self ω h0).trans_lt hx.2.2⟩, rxH_le hs⟩

theorem rxE_zero {T : Ordinal.{0}} : RxE S T 0 :=
  ⟨RxN.zero, CSet.zero_mem _ _, (Om_pos omega0_ne_zero)⟩

theorem rxH_zero {T : Ordinal.{0}} : rxH S T 0 = 0 := Nat.le_zero.1 (rxH_le (RxNs.zero (n := 0)))

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)

theorem rxW_le_Om1 : rxW Z At ≤ Om 1 := min_le_right _ _

theorem rxOm_succ_SC (k : ℕ) : SC (Om ((k : Ordinal.{0}) + 1)) :=
  SC_Om (by exact (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne')

include hZ hZ1 hAt

omit hZ1 hAt in
theorem rxL_zero : rxL S Z At (rxW Z At) 0 = 0 := by
  rw [rxL_lt_Om1 (Om_pos one_ne_zero), ruInv_zero hZ.1]

/-- **Below `Ω₁`**: `κ x = ruInv x < Ω₂`. -/
theorem rxL_small {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h : x < Om 1) :
    rxL S Z At (rxW Z At) x = ruInv Z At x ∧ ruInv Z At x < Om (1 + 1) ∧
      x < gxTh Z At (Om (1 + 1)) := by
  have hW := rxW_SC hZ hZ1 hAt
  have hlt : x < gxTh Z At (Om (1 + 1)) := (rxE_lt_T hW hx h).trans_le (min_le_left _ _)
  exact ⟨rxL_lt_Om1 h, (ruInv_spec hlt).2.1, hlt⟩

omit hZ hZ1 hAt in
/-- **A bound from the parts.** -/
theorem rxL_step_lt {X x : Ordinal.{0}} (hX : SC X) (hx : RxE S (rxW Z At) x) (h1 : Om 1 < x)
    (hS : ¬ SC x)
    (IH : ∀ y, RxE S (rxW Z At) y → rxMs S (rxW Z At) y < rxMs S (rxW Z At) x → y < x →
      rxL S Z At (rxW Z At) y < X) :
    rxL S Z At (rxW Z At) x < X := by
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha, hb⟩ := rxVeb h1 hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := rxE_veb hx hv hb
    rw [rxL_veb hx h1 hε hS]
    exact hX.2 _ (IH _ haE (rxMs_lt_val hha ha) ha) _ (IH _ hbE (rxMs_lt_val hhb hb) hb)
  have hlt := ruLog_lt h1 hε
  have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne'
  obtain ⟨hlE, hlh⟩ := rxE_log hx
  obtain ⟨hrE, hrh⟩ := rxE_rem hx
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  rw [rxL_gt hx h1 hlt, hn]
  have h1m := IH _ hlE (rxMs_lt_val hlh hlt) hlt
  have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) < X := by
    rw [← gg_SC_eps hX]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h1m
  exact hX.isPrincipal (ldMul_lt_SC hX hop ((natCast_lt_omega0 n).trans (Lw.lw_omega_lt_SC hX)))
    (IH _ hrE (rxMs_lt_val hrh hrlt) hrlt)

/-- **The upper level bound**: `x < Ω_{k+1} ⇒ κ x < Ω_{k+2}`. -/
theorem rxL_lt_lev : ∀ x, RxE S (rxW Z At) x → ∀ k : ℕ, x < Om ((k : Ordinal.{0}) + 1) →
    rxL S Z At (rxW Z At) x < Om ((k : Ordinal.{0}) + 1 + 1) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx k hk => ?_
  rcases lt_or_ge x (Om 1) with h1 | h1
  · obtain ⟨e, h2, -⟩ := rxL_small hZ hZ1 hAt hx h1
    rw [e]; exact h2.trans_le (Om_le_Om.2 (add_le_add (le_add_self : (1 : Ordinal.{0}) ≤ k + 1) le_rfl))
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]
    have hjk : (j : Ordinal.{0}) < k + 1 := Om_lt_Om.1 hk
    exact Om_lt_Om.2 ((Order.add_one_le_of_lt hjk).trans_lt (lt_add_one _))
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := rxE_atom hW1 hx hS h1' hΩ
    rw [rxL_atom hj hdn (rxE_lt_Lam hdE) hdh]
    have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
    have hjk : (j : Ordinal.{0}) < k + 1 := Om_lt_Om.1 (hb.1.trans hk)
    exact (psi_lt (InR_Om_succ _) _).trans_le (Om_le_Om.2 (add_le_add (Order.add_one_le_of_lt hjk) le_rfl))
  · exact rxL_step_lt (SC_Om (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne') hx h1' hS
      fun y hyE hym hyx => IH y hym hyE k (hyx.trans hk)

omit hZ hZ1 hAt in
/-- **The lower level bound**: `Ω_k ≤ x ⇒ Ω_{k+1} ≤ κ x` (`k ≥ 1`). -/
theorem rxL_ge_lev : ∀ x, RxE S (rxW Z At) x → ∀ k : ℕ, 1 ≤ k → Om (k : Ordinal.{0}) ≤ x →
    Om ((k : Ordinal.{0}) + 1) ≤ rxL S Z At (rxW Z At) x := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx k hk hkx => ?_
  have h1 : Om 1 ≤ x := (rxOm1_le_nat hk).trans hkx
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hkj : (k : Ordinal.{0}) ≤ j := Om_le_Om.1 hkx
    have hj : 1 ≤ j := by exact_mod_cast (show (1 : Ordinal.{0}) ≤ j from
      (show (1 : Ordinal.{0}) ≤ k by exact_mod_cast hk).trans hkj)
    rw [rxL_Om hj]
    exact Om_le_Om.2 (add_le_add hkj le_rfl)
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := rxE_atom hW1 hx hS h1' hΩ
    rw [rxL_atom hj hdn (rxE_lt_Lam hdE) hdh]
    have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
    have hkj : (k : Ordinal.{0}) ≤ j := by
      by_contra hc
      have : (j : Ordinal.{0}) + 1 ≤ k := Order.add_one_le_of_lt (not_le.1 hc)
      exact absurd ((Om_le_Om.2 this).trans hkx) (not_le.2 hb.2)
    exact (Om_le_Om.2 (add_le_add hkj le_rfl)).trans (psiS_bounds (S := S) _ _).1.le
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha, hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := rxE_veb hx hv hb
    rw [rxL_veb hx h1' hε hS]
    by_cases hka : Om (k : Ordinal.{0}) ≤ invVeblen₁ x
    · exact (IH _ (rxMs_lt_val hha ha) haE k hk hka).trans (left_le_veblen _ _)
    · by_cases hkb : Om (k : Ordinal.{0}) ≤ invVeblen₂ x
      · exact (IH _ (rxMs_lt_val hhb hb) hbE k hk hkb).trans (right_le_veblen _ _)
      · push Not at hka hkb
        have := (rxOm_nat_SC hk).2 _ hka _ hkb
        rw [hv] at this
        exact absurd hkx (not_le.2 this)
  · have hlt := ruLog_lt h1' hε
    obtain ⟨hlE, hlh⟩ := rxE_log hx
    have hkl : Om (k : Ordinal.{0}) ≤ log ω x :=
      le_log_of_opow_le one_lt_omega0 (by rw [gg_SC_eps (rxOm_nat_SC hk)]; exact hkx)
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
        have hlt' : x < ω ^ log ω x * 1 :=
          (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
        rw [mul_one] at hlt'
        exact absurd (opow_log_le_self ω ((Om_pos one_ne_zero).trans h1').ne') (not_le.2 hlt')
      · exact h
    rw [rxL_gt hx h1' hlt, hn]
    have hS1 := rxOm_succ_SC k
    calc Om ((k : Ordinal.{0}) + 1) = ω ^ Om ((k : Ordinal.{0}) + 1) := (gg_SC_eps hS1).symm
      _ ≤ ω ^ rxL S Z At (rxW Z At) (log ω x) :=
          opow_le_opow_right omega0_pos (IH _ (rxMs_lt_val hlh hlt) hlE k hk hkl)
      _ ≤ ω ^ rxL S Z At (rxW Z At) (log ω x) * n := le_mul_left _ (by exact_mod_cast hn1)
      _ ≤ _ := le_self_add

theorem rxL_ne_zero {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h0 : x ≠ 0) :
    rxL S Z At (rxW Z At) x ≠ 0 := by
  rcases lt_or_ge x (Om 1) with h1 | h1
  · obtain ⟨e, -, hlt⟩ := rxL_small hZ hZ1 hAt hx h1
    rw [e]
    intro e0
    obtain ⟨-, -, he⟩ := ruInv_spec hlt
    rw [e0, gxTh_zero] at he
    exact h0 he.symm
  · have := rxL_ge_lev x hx 1 le_rfl (by rw [Nat.cast_one]; exact h1)
    exact ((Om_pos (by norm_num)).trans_le this).ne'

theorem rxL_pos {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h0 : x ≠ 0) :
    0 < rxL S Z At (rxW Z At) x :=
  pos_iff_ne_zero.2 (rxL_ne_zero hZ hZ1 hAt hx h0)

omit hZ hZ1 hAt in
/-- **`κ` keeps the strongly critical members `≥ Ω₁`.** -/
theorem rxL_SC {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h1 : Om 1 ≤ x) (hS : SC x) :
    SC (rxL S Z At (rxW Z At) x) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact rxOm_succ_SC j
  · have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
    obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := rxE_atom hW1 hx hS h1' hΩ
    rw [rxL_atom hj hdn (rxE_lt_Lam hdE) hdh]
    exact SC_psi (InR_Om_succ _) _

/-- **`κ` keeps the `ε`-numbers `≥ Ω₁`.** -/
theorem rxL_eps {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h1 : Om 1 ≤ x) (hε : ω ^ x = x) :
    ω ^ rxL S Z At (rxW Z At) x = rxL S Z At (rxW Z At) x := by
  by_cases hS : SC x
  · exact gg_SC_eps (rxL_SC hx h1 hS)
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hS (e ▸ Ph.ph_SC_Om1)
  obtain ⟨hv, ha0, ha, hb⟩ := rxVeb h1' hε hS
  obtain ⟨haE, -, -, -⟩ := rxE_veb hx hv hb
  rw [rxL_veb hx h1' hε hS]
  exact gg_veblen_eps (rxL_ne_zero hZ hZ1 hAt haE ha0.ne')

/-- **`κ` on the Cantor normal form** of a member `≥ Ω₁`. -/
theorem rxLDecK {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h1 : Om 1 ≤ x) :
    ∃ n : ℕ, 1 ≤ n ∧ x = ω ^ log ω x * n + x % ω ^ log ω x ∧
      rxL S Z At (rxW Z At) x = ω ^ rxL S Z At (rxW Z At) (log ω x) * n +
        rxL S Z At (rxW Z At) (x % ω ^ log ω x) ∧
      RxE S (rxW Z At) (log ω x) ∧ RxE S (rxW Z At) (x % ω ^ log ω x) ∧
      RxE S (rxW Z At) (ω ^ log ω x) ∧
      x % ω ^ log ω x < ω ^ log ω x ∧ ω ^ log ω x ≤ x ∧ Om 1 ≤ log ω x ∧
      (ω ^ x = x ∨ log ω x < x) ∧ rxH S (rxW Z At) (log ω x) ≤ rxH S (rxW Z At) x ∧
      rxH S (rxW Z At) (x % ω ^ log ω x) ≤ rxH S (rxW Z At) x ∧
      rxH S (rxW Z At) (ω ^ log ω x) ≤ rxH S (rxW Z At) x := by
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans_le h1).ne'
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
  have hopx : ω ^ log ω x ≤ x := opow_log_le_self ω h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : x < ω ^ log ω x * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd hopx (not_le.2 hlt)
    · exact h
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have hℓ1 : Om 1 ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [Om1_opow]; exact h1)
  obtain ⟨hlE, hlh⟩ := rxE_log hx
  obtain ⟨hrE, hrh⟩ := rxE_rem hx
  obtain ⟨hoE, hoh⟩ := rxE_lead hx h0
  have hrlt : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos.ne'
  by_cases hε : ω ^ x = x
  · have hl := ruLog_eps hε
    have en : (n : Ordinal.{0}) = 1 := by
      rw [← hn, hl, hε, Ordinal.div_self h0]
    refine ⟨n, hn1, hdm, ?_, hlE, hrE, hoE, hrlt, hopx, hℓ1, Or.inl hε, hlh, hrh, hoh⟩
    rw [en, hl, hε, Ordinal.mod_self, rxL_zero hZ, add_zero, mul_one, rxL_eps hZ hZ1 hAt hx h1 hε]
  · have hgt : Om 1 < x := lt_of_le_of_ne h1 fun e => hε (by rw [← e]; exact Om1_opow)
    refine ⟨n, hn1, hdm, ?_, hlE, hrE, hoE, hrlt, hopx, hℓ1, Or.inr (ruLog_lt hgt hε), hlh, hrh, hoh⟩
    rw [← hn]; exact rxL_gt hx hgt (ruLog_lt hgt hε)

omit hZ1 hAt in
/-- **`κ` on the Veblen normal form** of an `ε`-number `≥ Ω₁` of the domain. -/
theorem rxLDecV {x : Ordinal.{0}} (hx : RxE S (rxW Z At) x) (h1 : Om 1 ≤ x) (hε : ω ^ x = x) :
    ∃ a b, veblen a b = x ∧ b < x ∧ a ≤ x ∧ RxE S (rxW Z At) a ∧ RxE S (rxW Z At) b ∧
      rxL S Z At (rxW Z At) x = veblen (rxL S Z At (rxW Z At) a) (rxL S Z At (rxW Z At) b) ∧
      (¬ SC x → a < x) ∧ rxH S (rxW Z At) a ≤ rxH S (rxW Z At) x ∧
      rxH S (rxW Z At) b ≤ rxH S (rxW Z At) x := by
  by_cases hS : SC x
  · have hK := rxL_SC hx h1 hS
    refine ⟨x, 0, hS.veblen_zero, hS.1, le_rfl, hx, rxE_zero, ?_, fun h => absurd hS h, le_rfl, ?_⟩
    · rw [rxL_zero hZ, hK.veblen_zero]
    · rw [rxH_zero]; exact Nat.zero_le _
  · have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hS (e ▸ Ph.ph_SC_Om1)
    obtain ⟨hv, -, ha, hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := rxE_veb hx hv hb
    exact ⟨_, _, hv, hb, ha.le, haE, hbE, rxL_veb hx h1' hε hS, fun _ => ha, hha, hhb⟩

/-- **`κ(ω^ℓ) = ω^{κ ℓ}`** for `ℓ ≥ Ω₁`. -/
theorem rxL_opow {ℓ : Ordinal.{0}} (hℓ : RxE S (rxW Z At) ℓ) (hop : RxE S (rxW Z At) (ω ^ ℓ))
    (h1 : Om 1 ≤ ℓ) : rxL S Z At (rxW Z At) (ω ^ ℓ) = ω ^ rxL S Z At (rxW Z At) ℓ := by
  by_cases hε : ω ^ ω ^ ℓ = ω ^ ℓ
  · have e : ω ^ ℓ = ℓ := (opow_right_inj one_lt_omega0).1 hε
    rw [e]; exact (rxL_eps hZ hZ1 hAt hℓ h1 e).symm
  · have hgt : Om 1 < ω ^ ℓ := lt_of_le_of_ne (h1.trans (right_le_opow ℓ one_lt_omega0))
      fun e => hε (by rw [← e]; exact Om1_opow)
    have hlog : log ω (ω ^ ℓ) = ℓ := log_opow one_lt_omega0 ℓ
    rw [rxL_gt hop hgt (ruLog_lt hgt hε), hlog, Ordinal.div_self (opow_pos ℓ omega0_pos).ne',
      Ordinal.mod_self, rxL_zero hZ, add_zero, mul_one]

end K

end Googology.Trans.PoR.InaccPsi.R2.Rx
