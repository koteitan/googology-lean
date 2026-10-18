import Googology.Trans.PoR.InaccPsi.R2.TpRoad

/-!
# The normal form of `P(η)` at a good `η`, and the base change `B_n` on it

`θ = ψ_{Ω₂}(Ω_ω)` (`ConjT.th`), `A_η = Ω_ω + θ·η`, `P(η) = ψ_{Ω₁}(A_η)` (`Nm.Pv`),
`α_k = Ω_ω·2 + P'·k`, `α_ω = Ω_ω·2 + P'·ω`, `σ = bcSig (bcPre (n+1)) bcPreW`, `B_n = Bc.bcB S n`.
A collapse argument `d` is *in its own closure* when `d ∈ Cl(d, ψ_{Ω₁}(d))`.

* `sfPeel` (**θ-peeling**): if `y + ε ∈ Cl(a, b)`, `θ ∣ y` and `ε < θ`, then `y ∈ Cl(a, b)`
  (strip the Cantor summands of `y + ε` one by one; the summands of `y` are `≥ θ > ε`);
* `sfOwn` (**the argument of `P(η)` at a good `η`**): for good `η`, `A_η` is in its own closure.
  (`M(A_η) = min(Cl(A_η, P(η)) ∩ [A_η, ∞))` has `ψ_{Ω₁}(M(A_η)) = P(η)`; goodness gives
  `M(A_η) < A_η + θ`; peeling gives `A_η ∈ Cl(M(A_η), P(η))`, so `M(A_η) = A_η` by F5.)
  `sfOwn_th`: then also `A_η + θ = A_{η+1}` is in its own closure;
* `sfNf_psi`: the normal form of `ψ_{Ω₁}(d)` with `d` in its own closure is `ψ^S_0(a)`, `|a| = d`;
* `sfB_psi`: `B_n(ψ_{Ω₁}(|a|)) = ψ_{Ω₁}(α_ω + |σ(ρ)|)` for a normal `ψ^S_0(a)` with
  `α_{n+1} ≤ |a| < α_ω`, `ρ` the rest of `a` after the prefix `Ω_ω, Ω_ω, P'^{(n+1)}`;
* `sfSig_dvd` (**σ keeps `θ`-divisibility**): `θ ∣ |ρ|` gives `θ ∣ |σ(ρ)|` (every summand of `ρ` is
  `≥ θ`, `σ` fixes the term of `θ` and keeps `cmp`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## `θ` -/

theorem sfTh_opow (S : InaccSeq.{0}) : ω ^ ConjT.th S = ConjT.th S :=
  Low.opow_eq_self_of_SC (ConjT.SC_th S)

theorem sfTh_pos (S : InaccSeq.{0}) : 0 < ConjT.th S := (ConjT.SC_th S).1

theorem sfTh_lt_OmW (S : InaccSeq.{0}) : ConjT.th S < Om ω :=
  (psi_lt (InR_Om_succ 1) _).trans (Om_lt_Om.2 (by
    rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]
    exact natCast_lt_omega0 2))

/-- `θ ∣ ω^g` for `g ≥ θ`. -/
theorem sfTh_dvd_opow {g : Ordinal.{0}} (h : ConjT.th S ≤ g) : ConjT.th S ∣ ω ^ g := by
  rw [← sfTh_opow S]
  exact opow_dvd_opow ω h

/-- A nonzero principal `x ≥ θ` is a left multiple of `θ`. -/
theorem sfTh_dvd_prin {x : Ordinal.{0}} (hP : IsPrincipal (· + ·) x) (hx0 : x ≠ 0)
    (h : ConjT.th S ≤ x) : ConjT.th S ∣ x := by
  obtain ⟨g, rfl⟩ := exists_opow_of_principal hP hx0
  refine sfTh_dvd_opow ?_
  have h' : ω ^ ConjT.th S ≤ ω ^ g := by rwa [sfTh_opow S]
  exact (opow_le_opow_iff_right one_lt_omega0).1 h'

/-- `θ ∣ A_η`. -/
theorem sfTh_dvd_A (S : InaccSeq.{0}) (η : Ordinal.{0}) : ConjT.th S ∣ ConjT.Aη S η := by
  unfold ConjT.Aη
  refine dvd_add ?_ (dvd_mul_right _ _)
  have e : ω ^ Om ω = Om ω := Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)
  rw [← e]
  exact sfTh_dvd_opow (sfTh_lt_OmW S).le

/-! ## θ-peeling -/

/-- **θ-peeling**: `y + ε ∈ Cl(a, b)`, `θ ∣ y`, `ε < θ` give `y ∈ Cl(a, b)`. -/
theorem sfPeel {a b : Ordinal.{0}} (x : Ordinal.{0}) : x ∈ S.CSet a b → ∀ y ε : Ordinal.{0},
    ConjT.th S ∣ y → ε < ConjT.th S → x = y + ε → y ∈ S.CSet a b := by
  induction x using WellFoundedLT.induction with
  | _ x ih =>
  intro hx y ε hy hε e
  rcases eq_or_ne y 0 with rfl | hy0
  · exact CSet.zero_mem a b
  have hθy : ConjT.th S ≤ y := Ordinal.le_of_dvd hy0 hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hy0 (le_antisymm (e ▸ le_self_add) zero_le)
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlogy : ConjT.th S ≤ Ordinal.log ω y := by
    refine (opow_le_iff_le_log one_lt_omega0 hy0).1 ?_
    rwa [sfTh_opow S]
  have hlog : Ordinal.log ω x = Ordinal.log ω y := by
    rw [e]
    refine log_add_of_le hy0 ?_
    rcases eq_or_ne ε 0 with rfl | hε0
    · simp
    · have h1 : Ordinal.log ω ε < ConjT.th S :=
        (lt_opow_iff_log_lt one_lt_omega0 hε0).1 (by rwa [sfTh_opow S])
      exact (h1.trans_le hlogy).le
  have hlead : lead x = lead y := by unfold lead; rw [hlog]
  have htail : tail x = tail y + ε := by
    have h1 := lead_add_tail hx0
    have h2 := lead_add_tail hy0
    rw [hlead] at h1
    have : lead y + tail x = lead y + (tail y + ε) := by
      rw [h1, ← add_assoc, h2, e]
    exact add_left_cancel this
  have hdl : ConjT.th S ∣ lead y := sfTh_dvd_opow hlogy
  have hdt : ConjT.th S ∣ tail y := by
    have h2 := lead_add_tail hy0
    rw [← h2] at hy
    exact (dvd_add_iff hdl).1 hy
  have hty : tail y ∈ S.CSet a b := ih (tail x) (tail_lt hx0) ht (tail y) ε hdt hε htail
  rw [← lead_add_tail hy0]
  exact CSet.add_mem (hlead ▸ hl) hty

/-! ## The argument of `P(η)` at a good `η` -/

/-- **At a good `η`, `A_η` is in its own closure.** -/
theorem sfOwn {η : Ordinal.{0}} (hg : Bt.Good S η) (hL : ConjT.Aη S η < S.Lam) :
    ConjT.Aη S η ∈ S.CSet (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)) := by
  have hψ := psi_M_eq (S := S) Low.InR_Om_one hL
  have hself := M_mem_self (S := S) Low.InR_Om_one hL
  have hAd := (M_spec (S := S) (e := ConjT.Aη S η) (g := S.psi (ConjT.Aη S η) (Om 1)) hL).2
  generalize S.M (ConjT.Aη S η) (S.psi (ConjT.Aη S η) (Om 1)) (ConjT.Aη S η) = d at hψ hself hAd
  have hdlt : d < ConjT.Aη S η + ConjT.th S := by
    by_contra hge
    push Not at hge
    have h1 := (psi_mono (S := S) Low.InR_Om_one hge).1
    have h2 : Pv S η < Pv S (η + 1) := Pv_lt_succ hg
    rw [hψ, ConjT.A_succ] at h1
    exact absurd h2 (not_lt.2 h1)
  obtain ⟨ε, hε⟩ := exists_add_of_le hAd
  have hεθ : ε < ConjT.th S := by
    rw [hε] at hdlt; exact (add_lt_add_iff_left _).1 hdlt
  have hmem : ConjT.Aη S η ∈ S.CSet d (S.psi d (Om 1)) :=
    sfPeel d hself _ ε (sfTh_dvd_A S η) hεθ hε
  rcases eq_or_lt_of_le hAd with e | hlt
  · rw [e]; exact hself
  · exfalso
    have := psi_lt_psi_of_mem Low.InR_Om_one hlt hmem
    rw [hψ] at this
    exact lt_irrefl _ this

/-- **`A + θ` is in its own closure** when `A ≥ Ω_ω` is. -/
theorem sfOwn_th {A : Ordinal.{0}} (h : A ∈ S.CSet A (S.psi A (Om 1))) (hA : Om ω ≤ A) :
    A + ConjT.th S ∈ S.CSet (A + ConjT.th S) (S.psi (A + ConjT.th S) (Om 1)) := by
  have h1 := (psi_mono (S := S) Low.InR_Om_one (le_self_add : A ≤ A + ConjT.th S)).2 h
  refine CSet.add_mem h1 (ConjT.th_mem S ?_)
  exact lt_of_le_of_lt hA (lt_add_of_pos_right _ (sfTh_pos S))

/-- Arguments in their own closure compare as their collapses. -/
theorem sfArg_le {a b : Ordinal.{0}} (ha : a ∈ S.CSet a (S.psi a (Om 1)))
    (hb : b ∈ S.CSet b (S.psi b (Om 1))) (h : S.psi a (Om 1) ≤ S.psi b (Om 1)) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have hc := compare_psi Low.InR_Om_one hb ha
  rw [compare_lt_iff_lt.2 hlt] at hc
  exact absurd h (not_le.2 (compare_lt_iff_lt.1 hc))

/-- `α_{k+1}` is in its own closure. -/
theorem sfOwn_alpha (S : InaccSeq.{0}) (k : ℕ) :
    bcAlpha S (k + 1) ∈ S.CSet (bcAlpha S (k + 1)) (S.psi (bcAlpha S (k + 1)) (Om 1)) := by
  have h : Sem S (psiS Term.zero (bcApp (bcPre (k + 1)) Term.zero)) := sem_of_NF (NF_bcLt S k)
  have h2 := h.2.2
  rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
    val_pre] at h2
  exact h2

/-! ## The normal form of a collapse with an argument in its own closure -/

/-- The normal form of `ψ_{Ω₁}(d)`, `d` in its own closure, is `ψ^S_0(a)` with `|a| = d`. -/
theorem sfNf_psi {d : Ordinal.{0}} (hd : d ∈ S.CSet d (S.psi d (Om 1))) {t : Term} (ht : NF t)
    (hv : val S t = S.psi d (Om 1)) : ∃ a, t = psiS Term.zero a ∧ val S a = d := by
  have hSC : SC (val S t) := hv ▸ SC_psi Low.InR_Om_one d
  have hlt : val S t < Om 1 := hv ▸ psi_lt Low.InR_Om_one d
  have hsc := isSC_of_SC (S := S) ht hSC
  cases t with
  | psiS s a =>
    by_cases hs : s = Term.zero
    · subst hs
      refine ⟨a, rfl, ?_⟩
      have h : Sem S (psiS Term.zero a) := sem_of_NF ht
      have hsem := h.2.2
      rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add]] at hsem
      have hc := compare_psi Low.InR_Om_one hsem hd
      rw [← val_psiS_zero, hv, compare_eq_iff_eq.2 rfl] at hc
      exact compare_eq_iff_eq.1 hc.symm
    · exfalso
      have := Om_one_lt_val_psiS (S := S) (a := a) ht.1 hs
      exact absurd hlt (not_lt.2 this.le)
  | om a =>
    exfalso
    exact absurd hlt (not_lt.2 (Om_one_le_val_om (S := S) ht))
  | psiI n a =>
    exfalso
    have h2 := Om_two_le_psiI (S := S) n a
    have h12 : Om (1 : Ordinal.{0}) < Om 2 := Om_lt_Om.2 one_lt_two
    exact absurd hlt (not_lt.2 (h12.trans_le h2).le)
  | inacc n =>
    exfalso
    exact absurd hlt (not_lt.2 (Low.Om_one_le_I n))
  | inaccW =>
    exfalso
    exact absurd hlt (not_lt.2 ((Low.Om_one_le_I 0).trans (S.I_le_Iw 0)))
  | zero => exact absurd hsc (by simp [isSC])
  | add _ _ => exact absurd hsc (by simp [isSC])
  | phi _ _ => exact absurd hsc (by simp [isSC])

/-! ## `B_n` at a prefixed collapse -/

theorem sfPre_len (n : ℕ) : (bcPre (n + 1)).length = n + 3 := by simp [bcPre]

/-- **`B_n` at a prefixed collapse.** -/
theorem sfB_psi {n : ℕ} {a : Term} (hN : NF (psiS Term.zero a)) (hlo : bcAlpha S (n + 1) ≤ val S a)
    (hhi : val S a < bcAlphaW S) :
    bcB S n (S.psi (val S a) (Om 1)) =
      S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a))) (Om 1) := by
  unfold bcB
  rw [← val_psiS_zero, bcNf_val S hN, bcSig_psiS_zero,
    bcArg_of_pre ((bc_pre_iff S hN.2.1 hhi).2 hlo), val_psiS_zero, val_bcApp_preW, sfPre_len]

/-! ## σ keeps `θ`-divisibility -/

/-- The term of `θ`. -/
def sfThT : Term := psiS tOne tW

theorem sfThT_NF : NF sfThT := ⟨NF_tOne, NF_tW, KLt_tW _ _⟩

theorem sfThT_free : bcFree sfThT := ⟨tOne_ne_zero, bcFree_tOne, bcFree_tW⟩

theorem sfThT_val (S : InaccSeq.{0}) : val S sfThT = ConjT.th S := by
  show S.psi (val S tW) (Om (val S tOne + 1)) = S.psi (Om ω) (Om (1 + 1))
  rw [val_tW, val_tOne]

theorem sfThT_D : bcD S sfThT := bcD_free sfThT_NF sfThT_free

/-- A principal summand: `θ ∣ |p|` gives `θ ∣ |σ(p)|`. -/
theorem sfSig_dvd_prin (n : ℕ) {p : Term} (hD : bcD S p) (hP : p.isPrin = true)
    (h : ConjT.th S ∣ val S p) :
    ConjT.th S ∣ val S (bcSig (bcPre (n + 1)) bcPreW p) := by
  have hp0 : p ≠ Term.zero := NF.ne_zero_of_isPrin hP
  have hv0 : val S p ≠ 0 := val_ne_zero S hD.1 hp0
  have hθ : ConjT.th S ≤ val S p := Ordinal.le_of_dvd hv0 h
  have hN := bc_NF (k := n) hD
  have hσ : ConjT.th S ≤ val S (bcSig (bcPre (n + 1)) bcPreW p) := by
    have := (bc_lt_iff (k := n) hD sfThT_D).not.2 (not_lt.2 (by rw [sfThT_val]; exact hθ))
    rw [not_lt, bcSig_free sfThT_free, sfThT_val] at this
    exact this
  refine sfTh_dvd_prin (isPrincipal_val S hN (by rw [isPrin_bcSig]; exact hP)) ?_ hσ
  exact (lt_of_lt_of_le (sfTh_pos S) hσ).ne'

/-- **σ keeps `θ`-divisibility.** -/
theorem sfSig_dvd (n : ℕ) : ∀ {r : Term}, bcD S r → ConjT.th S ∣ val S r →
    ConjT.th S ∣ val S (bcSig (bcPre (n + 1)) bcPreW r)
  | Term.zero, _, _ => by rw [bcSig_zero]; exact dvd_zero _
  | Term.add p r, hD, h => by
    have hN := hD.1
    have hDp : bcD S p := bcD_sub hD (sub_add_l p r)
    have hDr : bcD S r := bcD_sub hD (sub_add_r p r)
    have hp : ConjT.th S ∣ val S p := by
      have hP : p.isPrin = true := hN.2.2.1
      have hp0 : val S p ≠ 0 := val_ne_zero S hN.1 (NF.ne_zero_of_isPrin hP)
      refine sfTh_dvd_prin (isPrincipal_val S hN.1 hP) hp0 ?_
      by_contra hlt
      push Not at hlt
      obtain ⟨g, hg⟩ := exists_opow_of_principal (isPrincipal_val S hN.1 hP) hp0
      have hgθ : g < ConjT.th S := by
        rw [hg, ← sfTh_opow S] at hlt
        exact (opow_lt_opow_iff_right one_lt_omega0).1 hlt
      have hb : val S (Term.add p r) < val S p * ω := by
        have := val_lt_head_mul (S := S) hN (by simp)
        simpa [head] using this
      have hle : val S p * ω ≤ ConjT.th S := by
        rw [hg, ← opow_succ, ← sfTh_opow S]
        exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgθ)
      have hne : val S (Term.add p r) ≠ 0 := val_ne_zero S hN (by simp)
      have := Ordinal.le_of_dvd hne h
      exact absurd (hb.trans_le hle) (not_lt.2 this)
    have hr : ConjT.th S ∣ val S r := (dvd_add_iff hp).1 h
    rw [bcSig_add]
    exact dvd_add (sfSig_dvd_prin n hDp hN.2.2.1 hp) (sfSig_dvd n hDr hr)
  | Term.inacc m, hD, h => sfSig_dvd_prin n hD rfl h
  | Term.inaccW, hD, h => sfSig_dvd_prin n hD rfl h
  | Term.phi a b, hD, h => sfSig_dvd_prin n hD rfl h
  | Term.om a, hD, h => sfSig_dvd_prin n hD rfl h
  | Term.psiS s a, hD, h => sfSig_dvd_prin n hD rfl h
  | Term.psiI m a, hD, h => sfSig_dvd_prin n hD rfl h

end Googology.Trans.PoR.InaccPsi.R2.Sf
