import Googology.Trans.PoR.InaccPsi.R2.RxL

/-!
# The domain of the level shift and its equations

`RxE S T` the domain (`Rx.RxE`: normal hull over `T`, `Cl(Ω_ω, θ)`, below `Ω_ω`), `rxH` the least stage, `rxMs` the
measure, `rxL` the level shift (`Rx.rxL`), `ψ_k = ψ_{Ω_k}`.  `T` is strongly critical with `T ≤ Ω₁`.

* `rxE_lt_T` (countable members are below `T`), `rxE_log`, `rxE_rem`, `rxE_veb` (**the parts of a member are
  members, at a stage not above its stage**), `rxE_atom` (**a strongly critical member `> Ω₁` that is not a cardinal
  is `ψ_{k+1}(d)`, `1 ≤ k < ω`, with `d` a normal argument in the domain at a smaller stage**), `rxE_card`;
* `rxL_lt_Om1` (`κ x = ruInv x` below `Ω₁`), `rxL_Om` (`κ Ω_k = Ω_{k+1}`), `rxL_atom` (**`κ ψ_{k+1}(d) =
  ψ_{k+2}(κ d)`**), `rxL_gt` (the Cantor normal form), `rxL_veb` (the Veblen normal form).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}} {T : Ordinal.{0}}

theorem RxN.opow {c : Ordinal.{0}} (h : RxN S T c) : RxN S T (ω ^ c) := by
  have := RxN.phi RxN.zero h; rwa [veblen_zero_apply] at this

theorem RxN.mul_nat {x : Ordinal.{0}} (h : RxN S T x) : ∀ n : ℕ, RxN S T (x * n)
  | 0 => by simpa using RxN.zero (S := S) (T := T)
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact RxN.add (RxN.mul_nat h n) h

theorem rxOm_nat_SC {k : ℕ} (hk : 1 ≤ k) : SC (Om (k : Ordinal.{0})) :=
  SC_Om (by have : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
            exact (zero_lt_one.trans_le this).ne')

theorem rxOm1_le_nat {k : ℕ} (hk : 1 ≤ k) : Om (1 : Ordinal.{0}) ≤ Om (k : Ordinal.{0}) :=
  Om_le_Om.2 (by exact_mod_cast hk)

section Dom

variable (hT : SC T) (hT1 : T ≤ Om 1)
include hT hT1

omit hT1 in
theorem rxE_lt_T {x : Ordinal.{0}} (hx : RxE S T x) (h : x < Om 1) : x < T :=
  rxNs_lt_T hT (rxH_spec hx.1) h

omit hT hT1 in
/-- **The logarithm of a member.** -/
theorem rxE_log {x : Ordinal.{0}} (hx : RxE S T x) :
    RxE S T (log ω x) ∧ rxH S T (log ω x) ≤ rxH S T x := by
  have hs := (rxNsDec x (rxH S T x) (rxH_spec hx.1)).2
  refine ⟨⟨rxN_iff_stage.2 ⟨_, hs⟩, (rxCDec x hx.2.1).2, (log_le_self ω x).trans_lt hx.2.2⟩, rxH_le hs⟩

omit hT hT1 in
/-- **The rest of the Cantor normal form of a member.** -/
theorem rxE_rem {x : Ordinal.{0}} (hx : RxE S T x) :
    RxE S T (x % ω ^ log ω x) ∧ rxH S T (x % ω ^ log ω x) ≤ rxH S T x := by
  have hlog := rxE_log hx
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
    rw [← hn]; exact (Ordinal.div_add_mod x _).symm
  have e : x - ω ^ log ω x * n = x % ω ^ log ω x := by
    have e0 := Ordinal.add_sub_cancel (ω ^ log ω x * n) (x % ω ^ log ω x)
    rwa [← hdm] at e0
  have hle : ω ^ log ω x * n ≤ x := le_self_add.trans_eq hdm.symm
  have hmN : RxN S T (ω ^ log ω x * n) := RxN.mul_nat (RxN.opow hlog.1.1) n
  have hop : ω ^ log ω x ∈ S.CSet (Om ω) (ConjT.th S) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hlog.1.2.1; rwa [veblen_zero_apply] at this
  have hmC : ω ^ log ω x * n ∈ S.CSet (Om ω) (ConjT.th S) := ConjT.mul_nat_mem S hop n
  have hs := (rxNsDec x (rxH S T x) (rxH_spec hx.1)).1 _ hmN hle
  rw [e] at hs
  have hC := (rxCDec x hx.2.1).1 _ hmC hle
  rw [e] at hC
  exact ⟨⟨rxN_iff_stage.2 ⟨_, hs⟩, hC, (Ordinal.mod_le x _).trans_lt hx.2.2⟩, rxH_le hs⟩

omit hT hT1 in
/-- **The Veblen parts of a member.** -/
theorem rxE_veb {x a b : Ordinal.{0}} (hx : RxE S T x) (e : veblen a b = x) (hb : b < x) :
    RxE S T a ∧ RxE S T b ∧ rxH S T a ≤ rxH S T x ∧ rxH S T b ≤ rxH S T x := by
  obtain ⟨ha, hb'⟩ := rxNsDecV (rxH_spec hx.1) a b e hb
  obtain ⟨haC, hbC⟩ := rxCDecV hx.2.1 a b e hb
  exact ⟨⟨rxN_iff_stage.2 ⟨_, ha⟩, haC, ((e ▸ left_le_veblen a b).trans_lt hx.2.2)⟩,
    ⟨rxN_iff_stage.2 ⟨_, hb'⟩, hbC, hb.trans hx.2.2⟩, rxH_le ha, rxH_le hb'⟩

omit hT hT1 in
/-- **The cardinals of the domain.** -/
theorem rxE_card {x σ : Ordinal.{0}} (hx : RxE S T x) (e : x = Om σ) : ∃ k : ℕ, x = Om (k : Ordinal.{0}) := by
  obtain ⟨k, hk⟩ := rxCard_nat (e ▸ hx.2.2)
  exact ⟨k, by rw [e, hk]⟩

omit hT in
/-- **An atom of the domain.** -/
theorem rxE_atom {x : Ordinal.{0}} (hx : RxE S T x) (hS : SC x) (h1 : Om 1 < x)
    (hne : ¬ ∃ k : ℕ, x = Om (k : Ordinal.{0})) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ d, RxE S T d ∧ d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1))) ∧
      x = S.psi d (Om ((k : Ordinal.{0}) + 1)) ∧ rxH S T d < rxH S T x := by
  have hne' : ∀ σ, x ≠ Om σ := fun σ e => hne (rxE_card hx e)
  obtain ⟨m, hm, π, d, hπ, hπ1, hdm, hdn, rfl⟩ := rxNsSC hT1 (rxH_spec hx.1) hS h1 hne'
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact absurd (Om_psiI d n).symm (hne' _)
  obtain ⟨k, rfl⟩ := lt_omega0.1 (Om_lt_Om.1 ((psiS_bounds (S := S) d s).1.trans hx.2.2))
  have hk : 1 ≤ k := by
    by_contra h0
    have : k = 0 := by omega
    subst this
    exact hπ1 (by simp)
  have hdr : rxH S T d < rxH S T (S.psi d (Om ((k : Ordinal.{0}) + 1))) :=
    (rxH_le hdm).trans_lt hm
  have hκ : S.InR (Om ((k : Ordinal.{0}) + 1)) := InR_Om_succ _
  have hθL : ConjT.th S ≤ S.Lam := ((psi_lt (InR_Om_succ 1) _).trans
    (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0))).le
  have hdE : d ∈ S.CSet (Om ω) (ConjT.th S) ∧ d < Om ω := by
    rcases le_or_gt (ConjT.th S) (S.psi d (Om ((k : Ordinal.{0}) + 1))) with hθ | hθ
    · exact arg_mem_of_psi_mem hκ hx.2.1 hθ hθL hdn
    · have hk1 : k = 1 := by
        have h2 : S.psi d (Om ((k : Ordinal.{0}) + 1)) < Om (1 + 1) :=
          hθ.trans (psi_lt (InR_Om_succ 1) _)
        have := Om_lt_Om.1 ((psiS_bounds (S := S) d (k : Ordinal.{0})).1.trans h2)
        have h3 : (k : Ordinal.{0}) < 2 := by rwa [one_add_one_eq_two] at this
        have h4 : k < 2 := by exact_mod_cast h3
        omega
      subst hk1
      have hW : Om ω ∈ S.CSet (Om ω) (S.psi (Om ω) (Om (1 + 1))) := ConjT.OmW_mem S _ _
      have hdn' : d ∈ S.CSet d (S.psi d (Om (1 + 1))) := by simpa using hdn
      have hθ' : S.psi d (Om (1 + 1)) < S.psi (Om ω) (Om (1 + 1)) := by simpa using hθ
      have hdW : d < Om ω := lt_of_psi_lt (InR_Om_succ 1) hdn' hW hθ'
      refine ⟨CSet_mono hdW.le hθ'.le hdn', hdW⟩
  exact ⟨k, hk, d, ⟨rxN_iff_stage.2 ⟨m, hdm⟩, hdE.1, hdE.2⟩, hdn, rfl, hdr⟩

end Dom

section Eqn

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}}

theorem rxL_lt_Om1 {x : Ordinal.{0}} (h : x < Om 1) : rxL S Z At T x = ruInv Z At x := by
  rw [rxL, dif_pos h]

theorem rxLvO_eq (k : ℕ) : rxLvO (Om (k : Ordinal.{0})) = k := by
  have h : ∃ j : ℕ, Om (k : Ordinal.{0}) = Om (j : Ordinal.{0}) := ⟨k, rfl⟩
  classical
  rw [rxLvO, dif_pos h]
  exact rxOm_nat_inj (Nat.find_spec h).symm

theorem rxLvA_eq {x : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hS : SC x) (h1 : Om (k : Ordinal.{0}) < x)
    (h2 : x < Om ((k : Ordinal.{0}) + 1)) : rxLvA x = k := by
  have h : ∃ j : ℕ, 1 ≤ j ∧ SC x ∧ Om (j : Ordinal.{0}) < x ∧ x < Om ((j : Ordinal.{0}) + 1) :=
    ⟨k, hk, hS, h1, h2⟩
  classical
  rw [rxLvA, dif_pos h]
  obtain ⟨-, -, h3, h4⟩ := Nat.find_spec h
  exact rxLev_unique h3 h4 h1 h2

/-- **`κ Ω_k = Ω_{k+1}`.** -/
theorem rxL_Om {k : ℕ} (hk : 1 ≤ k) :
    rxL S Z At T (Om (k : Ordinal.{0})) = Om ((k : Ordinal.{0}) + 1) := by
  have h1 : ¬ Om (k : Ordinal.{0}) < Om 1 := not_lt.2 (rxOm1_le_nat hk)
  rw [rxL, dif_neg h1, dif_pos ⟨k, rfl⟩, rxLvO_eq]

/-- **`κ ψ_{k+1}(d) = ψ_{k+2}(κ d)`** at a normal argument `d` of a smaller stage. -/
theorem rxL_atom {d : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k)
    (hd : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1)))) (hdL : d < S.Lam)
    (hst : rxH S T d < rxH S T (S.psi d (Om ((k : Ordinal.{0}) + 1)))) :
    rxL S Z At T (S.psi d (Om ((k : Ordinal.{0}) + 1))) =
      S.psi (rxL S Z At T d) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
  set x := S.psi d (Om ((k : Ordinal.{0}) + 1)) with hxdef
  have hb := psiS_bounds (S := S) d (k : Ordinal.{0})
  have h1 : ¬ x < Om 1 := not_lt.2 ((rxOm1_le_nat hk).trans hb.1.le)
  have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := fun ⟨j, e⟩ =>
    not_Om_of_between hb.1 hb.2 (j : Ordinal.{0}) e
  have hS : SC x := SC_psi (InR_Om_succ _) d
  have hA : ∃ j : ℕ, 1 ≤ j ∧ SC x ∧ Om (j : Ordinal.{0}) < x ∧ x < Om ((j : Ordinal.{0}) + 1) :=
    ⟨k, hk, hS, hb.1, hb.2⟩
  have hlv : rxLvA x = k := rxLvA_eq hk hS hb.1 hb.2
  have hDn : rxDn S (Om ((k : Ordinal.{0}) + 1)) x = d := rxDn_eq (InR_Om_succ _) hd
  have hg : rxMs S T (rxDn S (Om ((rxLvA x : Ordinal.{0}) + 1)) x) < rxMs S T x := by
    rw [hlv, hDn]; exact rxMs_lt_stage hdL hst
  rw [rxL, dif_neg h1, dif_neg hΩ, dif_pos hA, dif_pos hg, hlv, hDn]

/-- **The Cantor normal form**: `κ x = ω^{κ ℓ}·n + κ r` (`ℓ = log_ω x < x`, `n = x / ω^ℓ`, `r = x mod ω^ℓ`). -/
theorem rxL_gt {x : Ordinal.{0}} (hx : RxE S T x) (h1 : Om 1 < x)
    (h3 : log ω x < x) :
    rxL S Z At T x = ω ^ rxL S Z At T (log ω x) * (x / ω ^ log ω x) +
      rxL S Z At T (x % ω ^ log ω x) := by
  have hc1 : ¬ x < Om 1 := not_lt.2 h1.le
  have hnε : ω ^ x ≠ x := fun h => by rw [ruLog_eps h] at h3; exact lt_irrefl _ h3
  have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
    rintro ⟨j, e⟩
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · rw [e, h0, Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    · exact hnε (by rw [e]; exact gg_SC_eps (rxOm_nat_SC hj))
  have hA : ¬ ∃ j : ℕ, 1 ≤ j ∧ SC x ∧ Om (j : Ordinal.{0}) < x ∧ x < Om ((j : Ordinal.{0}) + 1) :=
    fun ⟨_, _, hS, _⟩ => hnε (gg_SC_eps hS)
  have hl := rxE_log hx
  have hr := rxE_rem hx
  have g5 : rxMs S T (log ω x) < rxMs S T x := rxMs_lt_val hl.2 h3
  have g6 : rxMs S T (x % ω ^ log ω x) < rxMs S T x :=
    rxMs_lt_val hr.2 (mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne')
  rw [rxL, dif_neg hc1, dif_neg hΩ, dif_neg hA, dif_pos h3, dif_pos g5, dif_pos g6]

/-- **The Veblen normal form** of a non-strongly-critical `ε`-number of the domain above `Ω₁`. -/
theorem rxL_veb {x : Ordinal.{0}} (hx : RxE S T x) (h1 : Om 1 < x)
    (hε : ω ^ x = x) (hS : ¬ SC x) :
    rxL S Z At T x = veblen (rxL S Z At T (invVeblen₁ x)) (rxL S Z At T (invVeblen₂ x)) := by
  have hc1 : ¬ x < Om 1 := not_lt.2 h1.le
  have hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := by
    rintro ⟨j, e⟩
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · rw [e, h0, Nat.cast_zero, Om_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    · exact hS (e ▸ rxOm_nat_SC hj)
  have hA : ¬ ∃ j : ℕ, 1 ≤ j ∧ SC x ∧ Om (j : Ordinal.{0}) < x ∧ x < Om ((j : Ordinal.{0}) + 1) :=
    fun ⟨_, _, hS', _⟩ => hS hS'
  have h3 : ¬ log ω x < x := by rw [ruLog_eps hε]; exact lt_irrefl _
  obtain ⟨hv, -, ha, hb⟩ := rxVeb h1 hε hS
  obtain ⟨-, -, hha, hhb⟩ := rxE_veb hx hv hb
  have g7 : rxMs S T (invVeblen₁ x) < rxMs S T x := rxMs_lt_val hha ha
  have g8 : rxMs S T (invVeblen₂ x) < rxMs S T x := rxMs_lt_val hhb hb
  rw [rxL, dif_neg hc1, dif_neg hΩ, dif_neg hA, dif_neg h3, dif_pos ⟨ha, hb⟩, dif_pos g7, dif_pos g8]

end Eqn

end Googology.Trans.PoR.InaccPsi.R2.Rx
