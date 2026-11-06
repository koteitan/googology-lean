import Googology.Trans.PoR.InaccPsi.R2.KzDom

/-!
# Kz: THE LEVELS OF THE SHIFT BELOW A BOUND `K` (`Rx.RxLv` on `RxEK`)

`κ = Rx.rxL S Z At W`, `W = rxW Z At`, a bound `K` (`Kz.KzB`).  The level facts of `Rx.RxLv` on `RxEK S W K`, with
the new strongly critical member `Ω_ω` (`κ Ω_ω = Ω_ω`).

* `kzNe` (a member that is no `Ω_k` and not `Ω_ω` is no cardinal), `kzL_small`, `kzL_step_lt`, `kzL_lt_lev`
  (`x < Ω_{k+1} ⇒ κ x < Ω_{k+2}`), `kzL_ge_lev` (`Ω_k ≤ x ⇒ Ω_{k+1} ≤ κ x`), `kzL_ltW` (`x < Ω_ω ⇒ κ x < Ω_ω`),
  `kzL_geW` (`Ω_ω ≤ x ⇒ Ω_ω ≤ κ x`), `kzL_ne_zero`, `kzL_pos`, `kzL_SC`, `kzL_eps`, `kzLDecK`, `kzLDecV`,
  `kzL_opow`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem kzE_zero {T K : Ordinal.{0}} (hK : KzB S K) : RxEK S T K 0 :=
  ⟨RxN.zero, CSet.zero_mem _ _, hK.sc.1⟩

/-- A member that is no `Ω_k` and not `Ω_ω` is no cardinal. -/
theorem kzNe {T K x : Ordinal.{0}} (hK : KzB S K) (hx : RxEK S T K x) (hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}))
    (hW : x ≠ Om ω) : ∀ σ, x ≠ Om σ := fun σ e => by
  rcases kzCard hK (e ▸ hx.2.2) with ⟨j, hj⟩ | hj
  · exact hΩ ⟨j, by rw [e, hj]⟩
  · exact hW (by rw [e, hj])

/-- `ω^{log_ω x}` of a member is a member at a stage not above that of `x`. -/
theorem kzE_lead {T K x : Ordinal.{0}} (hx : RxEK S T K x) (h0 : x ≠ 0) :
    RxEK S T K (ω ^ log ω x) ∧ rxH S T (ω ^ log ω x) ≤ rxH S T x := by
  have hs := rxNs_lead (rxH_spec hx.1) h0
  have hl := (rxCDec x hx.2.1).2
  have hop : ω ^ log ω x ∈ S.CSet K (S.psi K (Om (1 + 1))) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hl; rwa [veblen_zero_apply] at this
  exact ⟨⟨rxN_iff_stage.2 ⟨_, hs⟩, hop, (opow_log_le_self ω h0).trans_lt hx.2.2⟩, rxH_le hs⟩

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)
  {K : Ordinal.{0}} (hK : KzB S K)

include hZ hZ1 hAt

omit hK in
/-- **Below `Ω₁`**: `κ x = ruInv x < Ω₂`. -/
theorem kzL_small {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h : x < Om 1) :
    rxL S Z At (rxW Z At) x = ruInv Z At x ∧ ruInv Z At x < Om (1 + 1) ∧
      x < gxTh Z At (Om (1 + 1)) := by
  have hW := rxW_SC hZ hZ1 hAt
  have hlt : x < gxTh Z At (Om (1 + 1)) := (rxNs_lt_T hW (rxH_spec hx.1) h).trans_le (min_le_left _ _)
  exact ⟨rxL_lt_Om1 h, (ruInv_spec hlt).2.1, hlt⟩

omit hZ hZ1 hAt hK in
/-- **A bound from the parts.** -/
theorem kzL_step_lt {X x : Ordinal.{0}} (hX : SC X) (hx : RxEK S (rxW Z At) K x) (h1 : Om 1 < x)
    (hS : ¬ SC x)
    (IH : ∀ y, RxEK S (rxW Z At) K y → rxMs S (rxW Z At) y < rxMs S (rxW Z At) x → y < x →
      rxL S Z At (rxW Z At) y < X) :
    rxL S Z At (rxW Z At) x < X := by
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha, hb⟩ := rxVeb h1 hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hx hv hb
    rw [kzL_veb hx h1 hε hS]
    exact hX.2 _ (IH _ haE (rxMs_lt_val hha ha) ha) _ (IH _ hbE (rxMs_lt_val hhb hb) hb)
  have hlt := ruLog_lt h1 hε
  have hrlt : x % ω ^ log ω x < x := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne'
  obtain ⟨hlE, hlh⟩ := kzE_log hx
  obtain ⟨hrE, hrh⟩ := kzE_rem hx
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  rw [kzL_gt hx h1 hlt, hn]
  have h1m := IH _ hlE (rxMs_lt_val hlh hlt) hlt
  have hop : ω ^ rxL S Z At (rxW Z At) (log ω x) < X := by
    rw [← gg_SC_eps hX]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h1m
  exact hX.isPrincipal (ldMul_lt_SC hX hop ((natCast_lt_omega0 n).trans (Lw.lw_omega_lt_SC hX)))
    (IH _ hrE (rxMs_lt_val hrh hrlt) hrlt)

include hK in
/-- **The upper level bound**: `x < Ω_{k+1} ⇒ κ x < Ω_{k+2}`. -/
theorem kzL_lt_lev : ∀ x, RxEK S (rxW Z At) K x → ∀ k : ℕ, x < Om ((k : Ordinal.{0}) + 1) →
    rxL S Z At (rxW Z At) x < Om ((k : Ordinal.{0}) + 1 + 1) := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx k hk => ?_
  rcases lt_or_ge x (Om 1) with h1 | h1
  · obtain ⟨e, h2, -⟩ := kzL_small hZ hZ1 hAt hx h1
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
  have hxW : x ≠ Om ω := fun e => by
    rw [e] at hk
    exact absurd (Om_lt_Om.1 hk) (not_lt.2 (by exact_mod_cast (natCast_lt_omega0 (k + 1)).le))
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := kzE_atom hK hW1 hx hS h1' (kzNe hK hx hΩ hxW)
    rw [rxL_atom hj hdn (kzE_lt_Lam hK hdE) hdh]
    have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
    have hjk : (j : Ordinal.{0}) < k + 1 := Om_lt_Om.1 (hb.1.trans hk)
    exact (psi_lt (InR_Om_succ _) _).trans_le (Om_le_Om.2 (add_le_add (Order.add_one_le_of_lt hjk) le_rfl))
  · exact kzL_step_lt (SC_Om (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne') hx h1' hS
      fun y hyE hym hyx => IH y hym hyE k (hyx.trans hk)

include hK in
/-- **The lower level bound**: `Ω_k ≤ x ⇒ Ω_{k+1} ≤ κ x` (`k ≥ 1`). -/
theorem kzL_ge_lev : ∀ x, RxEK S (rxW Z At) K x → ∀ k : ℕ, 1 ≤ k → Om (k : Ordinal.{0}) ≤ x →
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
  by_cases hxW : x = Om ω
  · rw [hxW, kzL_OmW]
    exact Om_le_Om.2 (by exact_mod_cast (natCast_lt_omega0 (k + 1)).le)
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := kzE_atom hK hW1 hx hS h1' (kzNe hK hx hΩ hxW)
    rw [rxL_atom hj hdn (kzE_lt_Lam hK hdE) hdh]
    have hb := psiS_bounds (S := S) d (j : Ordinal.{0})
    have hkj : (k : Ordinal.{0}) ≤ j := by
      by_contra hc
      have : (j : Ordinal.{0}) + 1 ≤ k := Order.add_one_le_of_lt (not_le.1 hc)
      exact absurd ((Om_le_Om.2 this).trans hkx) (not_le.2 hb.2)
    exact (Om_le_Om.2 (add_le_add hkj le_rfl)).trans (psiS_bounds (S := S) _ _).1.le
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha, hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hx hv hb
    rw [kzL_veb hx h1' hε hS]
    by_cases hka : Om (k : Ordinal.{0}) ≤ invVeblen₁ x
    · exact (IH _ (rxMs_lt_val hha ha) haE k hk hka).trans (left_le_veblen _ _)
    · by_cases hkb : Om (k : Ordinal.{0}) ≤ invVeblen₂ x
      · exact (IH _ (rxMs_lt_val hhb hb) hbE k hk hkb).trans (right_le_veblen _ _)
      · push Not at hka hkb
        have := (rxOm_nat_SC hk).2 _ hka _ hkb
        rw [hv] at this
        exact absurd hkx (not_le.2 this)
  · have hlt := ruLog_lt h1' hε
    obtain ⟨hlE, hlh⟩ := kzE_log hx
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
    rw [kzL_gt hx h1' hlt, hn]
    have hS1 := rxOm_succ_SC k
    calc Om ((k : Ordinal.{0}) + 1) = ω ^ Om ((k : Ordinal.{0}) + 1) := (gg_SC_eps hS1).symm
      _ ≤ ω ^ rxL S Z At (rxW Z At) (log ω x) :=
          opow_le_opow_right omega0_pos (IH _ (rxMs_lt_val hlh hlt) hlE k hk hkl)
      _ ≤ ω ^ rxL S Z At (rxW Z At) (log ω x) * n := le_mul_left _ (by exact_mod_cast hn1)
      _ ≤ _ := le_self_add

include hK in
/-- **Below `Ω_ω` the shift stays below `Ω_ω`.** -/
theorem kzL_ltW {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h : x < Om ω) :
    rxL S Z At (rxW Z At) x < Om ω := by
  obtain ⟨n, hn⟩ := rxOmW_nat h
  have h1 : x < Om ((n : Ordinal.{0}) + 1) := hn.trans (Om_lt_Om.2 (lt_add_one _))
  refine (kzL_lt_lev hZ hZ1 hAt hK x hx n h1).trans (Om_lt_Om.2 ?_)
  exact_mod_cast (show ((n + 1 + 1 : ℕ) : Ordinal.{0}) < ω from natCast_lt_omega0 _)

include hK in
/-- **At or above `Ω_ω` the shift stays at or above `Ω_ω`.** -/
theorem kzL_geW : ∀ x, RxEK S (rxW Z At) K x → Om ω ≤ x → Om ω ≤ rxL S Z At (rxW Z At) x := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  have hWSC : SC (Om ω : Ordinal.{0}) := SC_Om omega0_ne_zero
  refine rxMs_ind (S := S) (T := rxW Z At) fun x IH hx hWx => ?_
  have h1' : Om 1 < x := (Om_lt_Om.2 one_lt_omega0).trans_le hWx
  by_cases hxW : x = Om ω
  · rw [hxW, kzL_OmW]
  have hWx' : Om ω < x := lt_of_le_of_ne hWx (Ne.symm hxW)
  have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := fun ⟨j, e⟩ => by
    rw [e] at hWx'; exact absurd (Om_lt_Om.1 hWx') (not_lt.2 (natCast_lt_omega0 j).le)
  by_cases hS : SC x
  · exfalso
    obtain ⟨j, -, d, -, -, rfl, -⟩ := kzE_atom hK hW1 hx hS h1' (kzNe hK hx hΩ hxW)
    have hb := (psiS_bounds (S := S) d (j : Ordinal.{0})).2
    exact absurd (hb.trans (Om_lt_Om.2 (by exact_mod_cast natCast_lt_omega0 (j + 1)))) (not_lt.2 hWx)
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, -, ha, hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hx hv hb
    rw [kzL_veb hx h1' hε hS]
    by_cases hka : Om ω ≤ invVeblen₁ x
    · exact (IH _ (rxMs_lt_val hha ha) haE hka).trans (left_le_veblen _ _)
    · by_cases hkb : Om ω ≤ invVeblen₂ x
      · exact (IH _ (rxMs_lt_val hhb hb) hbE hkb).trans (right_le_veblen _ _)
      · push Not at hka hkb
        have := hWSC.2 _ hka _ hkb
        rw [hv] at this
        exact absurd hWx (not_le.2 this)
  · have hlt := ruLog_lt h1' hε
    obtain ⟨hlE, hlh⟩ := kzE_log hx
    have hkl : Om ω ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [gg_SC_eps hWSC]; exact hWx)
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
    rw [kzL_gt hx h1' hlt, hn]
    calc Om ω = ω ^ Om ω := (gg_SC_eps hWSC).symm
      _ ≤ ω ^ rxL S Z At (rxW Z At) (log ω x) :=
          opow_le_opow_right omega0_pos (IH _ (rxMs_lt_val hlh hlt) hlE hkl)
      _ ≤ ω ^ rxL S Z At (rxW Z At) (log ω x) * n := le_mul_left _ (by exact_mod_cast hn1)
      _ ≤ _ := le_self_add

include hK in
theorem kzL_ne_zero {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h0 : x ≠ 0) :
    rxL S Z At (rxW Z At) x ≠ 0 := by
  rcases lt_or_ge x (Om 1) with h1 | h1
  · obtain ⟨e, -, hlt⟩ := kzL_small hZ hZ1 hAt hx h1
    rw [e]
    intro e0
    obtain ⟨-, -, he⟩ := ruInv_spec hlt
    rw [e0, gxTh_zero] at he
    exact h0 he.symm
  · have := kzL_ge_lev hZ hZ1 hAt hK x hx 1 le_rfl (by rw [Nat.cast_one]; exact h1)
    exact ((Om_pos (by norm_num)).trans_le this).ne'

include hK in
theorem kzL_pos {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h0 : x ≠ 0) :
    0 < rxL S Z At (rxW Z At) x :=
  pos_iff_ne_zero.2 (kzL_ne_zero hZ hZ1 hAt hK hx h0)

omit hZ hZ1 hAt in
include hK in
/-- **`κ` keeps the strongly critical members `≥ Ω₁`.** -/
theorem kzL_SC {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h1 : Om 1 ≤ x) (hS : SC x) :
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
  by_cases hxW : x = Om ω
  · rw [hxW, kzL_OmW]; exact SC_Om omega0_ne_zero
  · have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
    obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := kzE_atom hK hW1 hx hS h1' (kzNe hK hx hΩ hxW)
    rw [rxL_atom hj hdn (kzE_lt_Lam hK hdE) hdh]
    exact SC_psi (InR_Om_succ _) _

include hK in
/-- **`κ` keeps the `ε`-numbers `≥ Ω₁`.** -/
theorem kzL_eps {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h1 : Om 1 ≤ x) (hε : ω ^ x = x) :
    ω ^ rxL S Z At (rxW Z At) x = rxL S Z At (rxW Z At) x := by
  by_cases hS : SC x
  · exact gg_SC_eps (kzL_SC hK hx h1 hS)
  have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hS (e ▸ Ph.ph_SC_Om1)
  obtain ⟨hv, ha0, ha, hb⟩ := rxVeb h1' hε hS
  obtain ⟨haE, -, -, -⟩ := kzE_veb hx hv hb
  rw [kzL_veb hx h1' hε hS]
  exact gg_veblen_eps (kzL_ne_zero hZ hZ1 hAt hK haE ha0.ne')

include hK in
/-- **`κ` on the Cantor normal form** of a member `≥ Ω₁`. -/
theorem kzLDecK {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h1 : Om 1 ≤ x) :
    ∃ n : ℕ, 1 ≤ n ∧ x = ω ^ log ω x * n + x % ω ^ log ω x ∧
      rxL S Z At (rxW Z At) x = ω ^ rxL S Z At (rxW Z At) (log ω x) * n +
        rxL S Z At (rxW Z At) (x % ω ^ log ω x) ∧
      RxEK S (rxW Z At) K (log ω x) ∧ RxEK S (rxW Z At) K (x % ω ^ log ω x) ∧
      RxEK S (rxW Z At) K (ω ^ log ω x) ∧
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
  obtain ⟨hlE, hlh⟩ := kzE_log hx
  obtain ⟨hrE, hrh⟩ := kzE_rem hx
  obtain ⟨hoE, hoh⟩ := kzE_lead hx h0
  have hrlt : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos.ne'
  by_cases hε : ω ^ x = x
  · have hl := ruLog_eps hε
    have en : (n : Ordinal.{0}) = 1 := by
      rw [← hn, hl, hε, Ordinal.div_self h0]
    refine ⟨n, hn1, hdm, ?_, hlE, hrE, hoE, hrlt, hopx, hℓ1, Or.inl hε, hlh, hrh, hoh⟩
    rw [en, hl, hε, Ordinal.mod_self, rxL_zero hZ, add_zero, mul_one, kzL_eps hZ hZ1 hAt hK hx h1 hε]
  · have hgt : Om 1 < x := lt_of_le_of_ne h1 fun e => hε (by rw [← e]; exact Om1_opow)
    refine ⟨n, hn1, hdm, ?_, hlE, hrE, hoE, hrlt, hopx, hℓ1, Or.inr (ruLog_lt hgt hε), hlh, hrh, hoh⟩
    rw [← hn]; exact kzL_gt hx hgt (ruLog_lt hgt hε)

omit hZ1 hAt in
include hK in
/-- **`κ` on the Veblen normal form** of an `ε`-number `≥ Ω₁` of the domain. -/
theorem kzLDecV {x : Ordinal.{0}} (hx : RxEK S (rxW Z At) K x) (h1 : Om 1 ≤ x) (hε : ω ^ x = x) :
    ∃ a b, veblen a b = x ∧ b < x ∧ a ≤ x ∧ RxEK S (rxW Z At) K a ∧ RxEK S (rxW Z At) K b ∧
      rxL S Z At (rxW Z At) x = veblen (rxL S Z At (rxW Z At) a) (rxL S Z At (rxW Z At) b) ∧
      (¬ SC x → a < x) ∧ rxH S (rxW Z At) a ≤ rxH S (rxW Z At) x ∧
      rxH S (rxW Z At) b ≤ rxH S (rxW Z At) x := by
  by_cases hS : SC x
  · have hK' := kzL_SC hK hx h1 hS
    refine ⟨x, 0, hS.veblen_zero, hS.1, le_rfl, hx, kzE_zero hK, ?_, fun h => absurd hS h, le_rfl, ?_⟩
    · rw [rxL_zero hZ, hK'.veblen_zero]
    · rw [rxH_zero]; exact Nat.zero_le _
  · have h1' : Om 1 < x := lt_of_le_of_ne h1 fun e => hS (e ▸ Ph.ph_SC_Om1)
    obtain ⟨hv, -, ha, hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hx hv hb
    exact ⟨_, _, hv, hb, ha.le, haE, hbE, kzL_veb hx h1' hε hS, fun _ => ha, hha, hhb⟩

include hK in
/-- **`κ(ω^ℓ) = ω^{κ ℓ}`** for `ℓ ≥ Ω₁`. -/
theorem kzL_opow {ℓ : Ordinal.{0}} (hℓ : RxEK S (rxW Z At) K ℓ) (hop : RxEK S (rxW Z At) K (ω ^ ℓ))
    (h1 : Om 1 ≤ ℓ) : rxL S Z At (rxW Z At) (ω ^ ℓ) = ω ^ rxL S Z At (rxW Z At) ℓ := by
  by_cases hε : ω ^ ω ^ ℓ = ω ^ ℓ
  · have e : ω ^ ℓ = ℓ := (opow_right_inj one_lt_omega0).1 hε
    rw [e]; exact (kzL_eps hZ hZ1 hAt hK hℓ h1 e).symm
  · have hgt : Om 1 < ω ^ ℓ := lt_of_le_of_ne (h1.trans (right_le_opow ℓ one_lt_omega0))
      fun e => hε (by rw [← e]; exact Om1_opow)
    have hlog : log ω (ω ^ ℓ) = ℓ := log_opow one_lt_omega0 ℓ
    rw [kzL_gt hop hgt (ruLog_lt hgt hε), hlog, Ordinal.div_self (opow_pos ℓ omega0_pos).ne',
      Ordinal.mod_self, rxL_zero hZ, add_zero, mul_one]

include hK in
/-- **`κ y ≥ y`** on the domain below `K`. -/
theorem kzL_ge_self : ∀ y, RxEK S (rxW Z At) K y → y ≤ rxL S Z At (rxW Z At) y := by
  have hW1 := rxW_le_Om1 (Z := Z) (At := At)
  refine rxMs_ind (S := S) (T := rxW Z At) fun y IH hy => ?_
  rcases lt_or_ge y (Om 1) with h1 | h1
  · obtain ⟨e, -, hlt⟩ := kzL_small hZ hZ1 hAt hy h1
    rw [e]
    obtain ⟨-, -, h3⟩ := ruInv_spec hlt
    conv_lhs => rw [← h3]
    exact cdOtp_le_self _ _
  by_cases hΩ : ∃ j : ℕ, y = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    have hj : 1 ≤ j := by
      by_contra h0
      have : j = 0 := by omega
      subst this
      rw [Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_le.2 (Om_pos one_ne_zero))
    rw [rxL_Om hj]; exact Om_le_Om.2 (le_add_of_nonneg_right zero_le)
  by_cases hyW : y = Om ω
  · rw [hyW, kzL_OmW]
  have h1' : Om 1 < y := lt_of_le_of_ne h1 fun e => hΩ ⟨1, by rw [Nat.cast_one]; exact e.symm⟩
  by_cases hS : SC y
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hdh⟩ := kzE_atom hK hW1 hy hS h1' (kzNe hK hy hΩ hyW)
    rw [rxL_atom hj hdn (kzE_lt_Lam hK hdE) hdh]
    exact (psiS_bounds (S := S) d (j : Ordinal.{0})).2.le.trans (psiS_bounds (S := S) _ _).1.le
  by_cases hε : ω ^ y = y
  · obtain ⟨hv, -, ha, hb⟩ := rxVeb h1' hε hS
    obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hy hv hb
    rw [kzL_veb hy h1' hε hS]
    conv_lhs => rw [← hv]
    exact (veblen_left_monotone _ (IH _ (rxMs_lt_val hha ha) haE)).trans
      ((isNormal_veblen _).monotone (IH _ (rxMs_lt_val hhb hb) hbE))
  · have hlt := ruLog_lt h1' hε
    have hrlt : y % ω ^ log ω y < y := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1').ne'
    obtain ⟨hlE, hlh⟩ := kzE_log hy
    obtain ⟨hrE, hrh⟩ := kzE_rem hy
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
    rw [kzL_gt hy h1' hlt, hn]
    have hdm : y = ω ^ log ω y * n + y % ω ^ log ω y := by
      rw [← hn]; exact (Ordinal.div_add_mod y _).symm
    conv_lhs => rw [hdm]
    exact add_le_add (mul_le_mul_left (opow_le_opow_right omega0_pos (IH _ (rxMs_lt_val hlh hlt) hlE)) _)
      (IH _ (rxMs_lt_val hrh hrlt) hrE)

end K

end Googology.Trans.PoR.InaccPsi.R2.Kz
