import Googology.Trans.PoR.InaccPsi.R2.KyMove

/-!
# Kz: THE DOMAIN OF THE LEVEL SHIFT BELOW A BOUND `K ≥ Ω_ω` (first step of the shift `T⁺` past `Ω_ω`)

`κ = Rx.rxL S Z At T` (since round 177 `κ Ω_ω = Ω_ω`, so `κ(Ω_ω + y) = Ω_ω + κ y` by the Cantor normal form),
`ψ_k = ψ_{Ω_k}`.  A bound `K` (`KzB`): strongly critical, `Ω_ω ≤ K ≤ ψ_{Ω_{ω+1}}(0)`, every `z < K` below a
closed term `w < K` (in every `Cl(a, b)`)
(`K = Ω_ω` is a bound).  `RxEK S T K`: the normal hull over `T`, `Cl(K, ψ₂ K)`, below `K`
(`Rx.RxE` is `K = Ω_ω`).  Below `K` the only cardinals are the `Ω_k` and `Ω_ω`, and the strongly critical members
`> Ω₁` that are not cardinals are the atoms `ψ_{k+1}(d)` of finite levels.

* `KzB`, `kzB_OmW`, `kzKW` (**`Γ_{Ω_ω+1}`, the least strongly critical ordinal above `Ω_ω`**), `kzB_KW`, `RxEK`,
  `rxEK_of_E`;
* `kzE_log`, `kzE_rem`, `kzE_veb` (**the parts of a member are members**), `kzE_card` (**a cardinal member is `Ω_k`,
  `k < ω`, or `Ω_ω`**), `kzE_atom` (**a strongly critical member `> Ω₁`, not a cardinal, is `ψ_{k+1}(d)`, `1 ≤ k < ω`,
  `d` a normal argument in the domain at a smaller stage**);
* `kzL_OmW` (**`κ Ω_ω = Ω_ω`**), `kzL_psiE` (**`κ ψ_{k+1}(d) = ψ_{k+2}(κ d)`**), `kzL_gt` (the Cantor normal
  form), `kzL_veb` (the Veblen normal form) on `RxEK`.

No new axiom.  New definitions: `KzB`, `kzKW`, `RxEK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **A bound of the domain.** -/
structure KzB (S : InaccSeq.{0}) (K : Ordinal.{0}) : Prop where
  sc : SC K
  ge : Om ω ≤ K
  le : K ≤ S.psi 0 (Om (ω + 1))
  fin : ∀ z, z < K → ∃ w, z ≤ w ∧ w < K ∧ ∀ a b, w ∈ S.CSet a b

/-- **The domain below `K`.** -/
def RxEK (S : InaccSeq.{0}) (T K x : Ordinal.{0}) : Prop :=
  RxN S T x ∧ x ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧ x < K

theorem kzW1_InR : S.InR (Om (ω + 1) : Ordinal.{0}) := InR_Om_succ ω

theorem kzOmW_lt_psiW1 : Om ω < S.psi 0 (Om (ω + 1)) := (psiS_bounds (S := S) 0 ω).1

theorem kzOmega_mem (a b : Ordinal.{0}) : (ω : Ordinal.{0}) ∈ S.CSet a b := by
  have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (CSet.one_mem a b)
  rwa [veblen_zero_apply, opow_one] at this

theorem kzB_OmW : KzB S (Om ω) where
  sc := SC_Om omega0_ne_zero
  ge := le_rfl
  le := kzOmW_lt_psiW1.le
  fin := fun z hz => by
    obtain ⟨n, hn⟩ := rxOmW_nat hz
    exact ⟨Om (n : Ordinal.{0}), hn.le, Om_lt_Om.2 (natCast_lt_omega0 n), fun a b => rxC_Om_nat a b n⟩

/-- A fixed point of `x ↦ φ(x, 0)` is strongly critical. -/
theorem kzSC_of_fix {γ : Ordinal.{0}} (h0 : 0 < γ) (h : veblen γ 0 = γ) : SC γ :=
  ⟨h0, fun x hx y hy => by
    have e := veblen_veblen_of_lt hx 0
    rw [h] at e
    exact e ▸ veblen_right_strictMono x hy⟩

/-- **`Γ_{Ω_ω+1}`**: the least strongly critical ordinal above `Ω_ω`. -/
noncomputable def kzKW : Ordinal.{0} := nfp (fun x => veblen x 0) (Om ω + 1)

theorem kzKW_fix : veblen kzKW 0 = kzKW := nfp_fp isNormal_veblen_zero _

theorem kzKW_gt : Om ω < kzKW := (lt_add_one _).trans_le (le_nfp _ _)

theorem kzKW_SC : SC kzKW := kzSC_of_fix ((Om_pos omega0_ne_zero).trans kzKW_gt) kzKW_fix

theorem kzKW_it_mem (a b : Ordinal.{0}) :
    ∀ n : ℕ, (fun x => veblen x 0)^[n] (Om ω + 1) ∈ S.CSet a b
  | 0 => CSet.succ_mem (CSet.Om_mem (kzOmega_mem a b))
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact CSet.phi_mem (kzKW_it_mem a b n) (CSet.zero_mem a b)

theorem kzKW_step : (Om ω + 1 : Ordinal.{0}) < veblen (Om ω + 1) 0 := by
  refine lt_of_le_of_ne (left_le_veblen _ _) fun e => ?_
  obtain ⟨c, hc⟩ := veblen_mem_range_opow (Om ω + 1) 0
  have hp : IsPrincipal (· + ·) (Om ω + 1) := by rw [e, ← hc]; exact isPrincipal_add_omega0_opow c
  have h1 : (1 : Ordinal.{0}) < Om ω + 1 := (Order.one_le_iff_pos.2 (Om_pos omega0_ne_zero)).trans_lt (lt_add_one _)
  exact (hp (lt_add_one (Om ω)) h1).ne rfl

theorem kzKW_it_lt (n : ℕ) : (fun x => veblen x 0)^[n] (Om ω + 1) < kzKW := by
  have hs : ∀ m : ℕ, (fun x => veblen x 0)^[m] (Om ω + 1) < (fun x => veblen x 0)^[m + 1] (Om ω + 1) := by
    intro m
    induction m with
    | zero => exact kzKW_step
    | succ m ih =>
      have e1 : (fun x => veblen x 0)^[m + 1 + 1] (Om ω + 1) =
          veblen ((fun x => veblen x 0)^[m + 1] (Om ω + 1)) 0 := Function.iterate_succ_apply' _ _ _
      have e0 : (fun x => veblen x 0)^[m + 1] (Om ω + 1) =
          veblen ((fun x => veblen x 0)^[m] (Om ω + 1)) 0 := Function.iterate_succ_apply' _ _ _
      calc _ = veblen ((fun x => veblen x 0)^[m] (Om ω + 1)) 0 := e0
        _ < veblen ((fun x => veblen x 0)^[m + 1] (Om ω + 1)) 0 := veblen_zero_strictMono ih
        _ = _ := e1.symm
  exact (hs n).trans_le (iterate_le_nfp _ _ _)

theorem kzB_KW : KzB S kzKW where
  sc := kzKW_SC
  ge := kzKW_gt.le
  le := nfp_le_fp isNormal_veblen_zero.strictMono.monotone (Order.add_one_le_of_lt kzOmW_lt_psiW1)
    (SC_psi kzW1_InR 0).veblen_zero.le
  fin := fun z hz => by
    obtain ⟨n, hn⟩ := lt_nfp_iff.1 hz
    exact ⟨_, hn.le, kzKW_it_lt n, fun a b => kzKW_it_mem a b n⟩

theorem kzK_lt_Lam {K : Ordinal.{0}} (hK : KzB S K) : K < S.Lam :=
  hK.le.trans_lt ((psi_lt kzW1_InR 0).trans
    (lt_Lam_of_mem zero_le (CSet.Om_mem (CSet.succ_mem (kzOmega_mem (S := S) 0 0)))))

section Dom

variable {T K : Ordinal.{0}} (hK : KzB S K)

include hK in
theorem kzE_lt_Lam {x : Ordinal.{0}} (hx : RxEK S T K x) : x < S.Lam := hx.2.2.trans (kzK_lt_Lam hK)

theorem rxEK_of_E {x : Ordinal.{0}} (hx : RxE S T x) (hKW : Om ω ≤ K) (hKψ : S.psi (Om ω) (Om (1 + 1)) ≤ S.psi K (Om (1 + 1))) :
    RxEK S T K x :=
  ⟨hx.1, CSet_mono hKW hKψ hx.2.1, hx.2.2.trans_le hKW⟩

omit hK in
/-- **The logarithm of a member.** -/
theorem kzE_log {x : Ordinal.{0}} (hx : RxEK S T K x) :
    RxEK S T K (log ω x) ∧ rxH S T (log ω x) ≤ rxH S T x := by
  have hs := (rxNsDec x (rxH S T x) (rxH_spec hx.1)).2
  exact ⟨⟨rxN_iff_stage.2 ⟨_, hs⟩, (rxCDec x hx.2.1).2, (log_le_self ω x).trans_lt hx.2.2⟩, rxH_le hs⟩

omit hK in
/-- **The rest of the Cantor normal form of a member.** -/
theorem kzE_rem {x : Ordinal.{0}} (hx : RxEK S T K x) :
    RxEK S T K (x % ω ^ log ω x) ∧ rxH S T (x % ω ^ log ω x) ≤ rxH S T x := by
  have hlog := kzE_log hx
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have e : x - ω ^ log ω x * n = x % ω ^ log ω x := by
    have e0 := Ordinal.add_sub_cancel (ω ^ log ω x * n) (x % ω ^ log ω x)
    rwa [← hdm] at e0
  have hle : ω ^ log ω x * n ≤ x := le_self_add.trans_eq hdm.symm
  have hmN : RxN S T (ω ^ log ω x * n) := RxN.mul_nat (RxN.opow hlog.1.1) n
  have hop : ω ^ log ω x ∈ S.CSet K (S.psi K (Om (1 + 1))) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hlog.1.2.1; rwa [veblen_zero_apply] at this
  have hmC : ω ^ log ω x * n ∈ S.CSet K (S.psi K (Om (1 + 1))) := ConjT.mul_nat_mem S hop n
  have hs := (rxNsDec x (rxH S T x) (rxH_spec hx.1)).1 _ hmN hle
  rw [e] at hs
  have hC := (rxCDec x hx.2.1).1 _ hmC hle
  rw [e] at hC
  exact ⟨⟨rxN_iff_stage.2 ⟨_, hs⟩, hC, (Ordinal.mod_le x _).trans_lt hx.2.2⟩, rxH_le hs⟩

omit hK in
/-- **The Veblen parts of a member.** -/
theorem kzE_veb {x a b : Ordinal.{0}} (hx : RxEK S T K x) (e : veblen a b = x) (hb : b < x) :
    RxEK S T K a ∧ RxEK S T K b ∧ rxH S T a ≤ rxH S T x ∧ rxH S T b ≤ rxH S T x := by
  obtain ⟨ha, hb'⟩ := rxNsDecV (rxH_spec hx.1) a b e hb
  obtain ⟨haC, hbC⟩ := rxCDecV hx.2.1 a b e hb
  exact ⟨⟨rxN_iff_stage.2 ⟨_, ha⟩, haC, ((e ▸ left_le_veblen a b).trans_lt hx.2.2)⟩,
    ⟨rxN_iff_stage.2 ⟨_, hb'⟩, hbC, hb.trans hx.2.2⟩, rxH_le ha, rxH_le hb'⟩

include hK in
/-- **The cardinals below `K`**: `Ω_k`, `k < ω`, or `Ω_ω`. -/
theorem kzCard {σ : Ordinal.{0}} (h : Om σ < K) : (∃ k : ℕ, σ = k) ∨ σ = ω := by
  have h1 : Om σ < Om (ω + 1) := h.trans_le (hK.le.trans (psi_lt kzW1_InR 0).le)
  have h2 : σ < ω + 1 := Om_lt_Om.1 h1
  rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h3 | h3
  · exact Or.inl (lt_omega0.1 h3)
  · exact Or.inr h3

include hK in
/-- **An atom of the domain below `K`.** -/
theorem kzE_atom (hT1 : T ≤ Om 1) {x : Ordinal.{0}} (hx : RxEK S T K x) (hS : SC x) (h1 : Om 1 < x)
    (hne : ∀ σ, x ≠ Om σ) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ d, RxEK S T K d ∧ d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1))) ∧
      x = S.psi d (Om ((k : Ordinal.{0}) + 1)) ∧ rxH S T d < rxH S T x := by
  obtain ⟨m, hm, π, d, hπ, hπ1, hdm, hdn, rfl⟩ := rxNsSC hT1 (rxH_spec hx.1) hS h1 hne
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact absurd (Om_psiI d n).symm (hne _)
  have hsK : Om s < K := (psiS_bounds (S := S) d s).1.trans hx.2.2
  rcases kzCard hK hsK with ⟨k, rfl⟩ | rfl
  swap
  · exfalso
    have h0 : S.psi 0 (Om (ω + 1)) ≤ S.psi d (Om (ω + 1)) := (psi_mono kzW1_InR zero_le).1
    exact absurd (hK.le.trans h0) (not_le.2 hx.2.2)
  have hk : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    exact hπ1 (by simp)
  have hdr : rxH S T d < rxH S T (S.psi d (Om ((k : Ordinal.{0}) + 1))) := (rxH_le hdm).trans_lt hm
  have hκ : S.InR (Om ((k : Ordinal.{0}) + 1)) := InR_Om_succ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hθL : S.psi K (Om (1 + 1)) ≤ S.Lam := ((psi_lt hκ2 _).trans
    (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0))).le
  have hdE : d ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧ d < K := by
    rcases le_or_gt (S.psi K (Om (1 + 1))) (S.psi d (Om ((k : Ordinal.{0}) + 1))) with hθ | hθ
    · exact arg_mem_of_psi_mem hκ hx.2.1 hθ hθL hdn
    · have hk1 : k = 1 := by
        have h2 : S.psi d (Om ((k : Ordinal.{0}) + 1)) < Om (1 + 1) := hθ.trans (psi_lt hκ2 _)
        have := Om_lt_Om.1 ((psiS_bounds (S := S) d (k : Ordinal.{0})).1.trans h2)
        have h3 : (k : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at this
        have h4 : k < 2 := by exact_mod_cast h3
        omega
      subst hk1
      have hdn' : d ∈ S.CSet d (S.psi d (Om (1 + 1))) := by simpa using hdn
      have hθ' : S.psi d (Om (1 + 1)) < S.psi K (Om (1 + 1)) := by simpa using hθ
      have hdW : d < K := by
        by_contra hc; push Not at hc; exact absurd hθ' (not_lt.2 (psi_mono hκ2 hc).1)
      exact ⟨CSet_mono hdW.le hθ'.le hdn', hdW⟩
  exact ⟨k, hk, d, ⟨rxN_iff_stage.2 ⟨m, hdm⟩, hdE.1, hdE.2⟩, hdn, rfl, hdr⟩

end Dom

section Eqn

variable {T Z : Ordinal.{0}} {At : Set Ordinal.{0}}

/-- **`κ Ω_ω = Ω_ω`.** -/
theorem kzL_OmW : rxL S Z At T (Om ω) = Om ω := by
  have h1 : ¬ Om ω < Om 1 := not_lt.2 (Om_le_Om.2 one_lt_omega0.le)
  have hΩ : ¬ ∃ k : ℕ, Om ω = Om (k : Ordinal.{0}) := fun ⟨k, e⟩ =>
    absurd (Om_inj.1 e) (natCast_lt_omega0 k).ne'
  rw [rxL, dif_neg h1, dif_neg hΩ, dif_pos rfl]

/-- **The Cantor normal form** on `RxEK`. -/
theorem kzL_gt {K x : Ordinal.{0}} (hx : RxEK S T K x) (h1 : Om 1 < x) (h3 : log ω x < x) :
    rxL S Z At T x = ω ^ rxL S Z At T (log ω x) * (x / ω ^ log ω x) + rxL S Z At T (x % ω ^ log ω x) := by
  have hc1 : ¬ x < Om 1 := not_lt.2 h1.le
  have hnε : ω ^ x ≠ x := fun h => by rw [ruLog_eps h] at h3; exact lt_irrefl _ h3
  have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
    rintro ⟨j, e⟩
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · rw [e, h0, Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    · exact hnε (by rw [e]; exact gg_SC_eps (rxOm_nat_SC hj))
  have hW : ¬ x = Om ω := fun e => hnε (by rw [e]; exact gg_SC_eps (SC_Om omega0_ne_zero))
  have hA : ¬ ∃ j : ℕ, 1 ≤ j ∧ SC x ∧ Om (j : Ordinal.{0}) < x ∧ x < Om ((j : Ordinal.{0}) + 1) :=
    fun ⟨_, _, hS, _⟩ => hnε (gg_SC_eps hS)
  have hl := kzE_log hx
  have hr := kzE_rem hx
  have g5 : rxMs S T (log ω x) < rxMs S T x := rxMs_lt_val hl.2 h3
  have g6 : rxMs S T (x % ω ^ log ω x) < rxMs S T x :=
    rxMs_lt_val hr.2 (mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne')
  rw [rxL, dif_neg hc1, dif_neg hΩ, dif_neg hW, dif_neg hA, dif_pos h3, dif_pos g5, dif_pos g6]

/-- **The Veblen normal form** on `RxEK`. -/
theorem kzL_veb {K x : Ordinal.{0}} (hx : RxEK S T K x) (h1 : Om 1 < x) (hε : ω ^ x = x) (hS : ¬ SC x) :
    rxL S Z At T x = veblen (rxL S Z At T (invVeblen₁ x)) (rxL S Z At T (invVeblen₂ x)) := by
  have hc1 : ¬ x < Om 1 := not_lt.2 h1.le
  have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
    rintro ⟨j, e⟩
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · rw [e, h0, Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    · exact hS (e ▸ rxOm_nat_SC hj)
  have hW : ¬ x = Om ω := fun e => hS (e ▸ SC_Om omega0_ne_zero)
  have hA : ¬ ∃ j : ℕ, 1 ≤ j ∧ SC x ∧ Om (j : Ordinal.{0}) < x ∧ x < Om ((j : Ordinal.{0}) + 1) :=
    fun ⟨_, _, hS', _⟩ => hS hS'
  have h3 : ¬ log ω x < x := by rw [ruLog_eps hε]; exact lt_irrefl _
  obtain ⟨hv, -, ha, hb⟩ := rxVeb h1 hε hS
  obtain ⟨-, -, hha, hhb⟩ := kzE_veb hx hv hb
  have g7 : rxMs S T (invVeblen₁ x) < rxMs S T x := rxMs_lt_val hha ha
  have g8 : rxMs S T (invVeblen₂ x) < rxMs S T x := rxMs_lt_val hhb hb
  rw [rxL, dif_neg hc1, dif_neg hΩ, dif_neg hW, dif_neg hA, dif_neg h3, dif_pos ⟨ha, hb⟩, dif_pos g7, dif_pos g8]

end Eqn

end Googology.Trans.PoR.InaccPsi.R2.Kz
