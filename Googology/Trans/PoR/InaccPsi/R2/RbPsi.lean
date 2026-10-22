import Googology.Trans.PoR.InaccPsi.R2.LqMove

/-!
# `B_n` at `ψ_{Ω₁}(B + d)` for every own base `B`, and the fixed points of `Γ_` among the collapses

`ψ = S.psi`, `Γ_ = Ordinal.gamma`, `B_n = Bc.bcB S n`, `σ = bcSig (bcPre (n+1)) bcPreW` (`B_n = val ∘ σ ∘ nf`),
`α_k = Ω_ω·2 + P'·k` (`bcAlpha`), `α_ω = Ω_ω·2 + ω^{P'+1}` (`bcAlphaW`).  An argument `B` is *own* when `B ∈ Cl(B,
ψ_{Ω₁}(B))`.

* `rb_own_of_SC` (**a strongly critical `p < ψ_{Ω₁}(B)` is `ψ_{Ω₁}(B_p)` for an own `B_p`**, its normal form);
* `rbB_psi_base` (**`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')` and `B_n(ψ_{Ω₁}(B + d)) = ψ_{Ω₁}(B' + B_n d)`** for every own `B`
  and own `B + d` in the window, `d < L(ω)`, with `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|` own; the base `B` may contain
  `Ω₁`-multiples: `Mx.mxB_psi_add` is the case `B = A_η`, `d < Ω₁`);
* `rbLast` (the last summand of a chain), `rb_dvd_prin` (**`Ω₁ ∣ x + y ↔ Ω₁ ≤ y`** for an additive principal `y`),
  `rb_dvd_iff_last`, `rb_dvd_sig` (**`σ` keeps `Ω₁ ∣ |r|`** on the domain of `σ`), `rb_dvd_alpha`, `rb_dvd_alphaW`,
  `rbB_dvd` (**`Ω₁ ∣ B` gives `Ω₁ ∣ B'`**);
* `rb_add_lt_of_dvd` (`b < B`, `Ω₁ ∣ B`, `D < Ω₁` give `b + D < B`), `rb_mod_mem` (**`Cl(a, b)` contains `x mod Ω₁` and
  `Ω₁·(x / Ω₁)` with `x`**);
* `rb_base_below` (**below a strongly critical `x > τ` that is not a fixed point of `Γ_` there is a largest point
  `p < x` that is `τ` or a fixed point above `τ`**);
* `rbFix_of_dvd` (**`ψ_{Ω₁}(B)` is a fixed point of `Γ_` for every own `B` with `Ω₁ ∣ B`** above some own `A₀`: else
  `ψ_{Ω₁}(B) = Γ_{c+D} = ψ_{Ω₁}(B_p + D)` with `B_p + D < B` in `Cl(B, ψ_{Ω₁}(B))`), `rbDvd_of_fix` (**the converse**:
  `ψ_{Ω₁}(B₀ + D₀) ≤ Γ_{c₀+D₀}` with `c₀, D₀ < ψ_{Ω₁}(B)` for `D₀ = B mod Ω₁ ≠ 0`).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Sf Googology.Trans.PoR.InaccPsi.R2.Lq

variable {S : InaccSeq.{0}}

/-! ## Normal forms of strongly critical points -/

/-- **A strongly critical `p < ψ_{Ω₁}(B)` is `ψ_{Ω₁}(B_p)` for an own `B_p`.** -/
theorem rb_own_of_SC {p B : Ordinal.{0}} (hp : SC p) (hpB : p < S.psi B (Om 1)) :
    ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p := by
  have hsp := bcNf_spec S (mem_of_lt_psi S hpB)
  have hlt : p < Om 1 := hpB.trans (psi_lt Low.InR_Om_one B)
  obtain ⟨hN, hv⟩ := hsp
  have hsc := isSC_of_SC (S := S) hN (by rw [hv]; exact hp)
  revert hN hv hsc
  generalize bcNf S p = t
  intro hN hv hsc
  cases t with
  | psiS s a =>
    by_cases hs : s = Term.zero
    · subst hs
      have h : Sem S (psiS Term.zero a) := sem_of_NF hN
      have hsem := h.2.2
      rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add]] at hsem
      exact ⟨val S a, hsem, by rw [← val_psiS_zero, hv]⟩
    · exfalso
      have := Om_one_lt_val_psiS (S := S) (a := a) hN.1 hs
      rw [hv] at this
      exact absurd hlt (not_lt.2 this.le)
  | om a =>
    exfalso
    have := Om_one_le_val_om (S := S) hN
    rw [hv] at this
    exact absurd hlt (not_lt.2 this)
  | psiI n a =>
    exfalso
    have h2 := Om_two_le_psiI (S := S) n a
    have h12 : Om (1 : Ordinal.{0}) < Om 2 := Om_lt_Om.2 one_lt_two
    rw [hv] at h2
    exact absurd hlt (not_lt.2 (h12.trans_le h2).le)
  | inacc n =>
    exfalso
    have := Low.Om_one_le_I (S := S) n
    rw [show S.I n = val S (inacc n) from rfl, hv] at this
    exact absurd hlt (not_lt.2 this)
  | inaccW =>
    exfalso
    have := (Low.Om_one_le_I (S := S) 0).trans (S.I_le_Iw 0)
    rw [show S.Iw = val S inaccW from rfl, hv] at this
    exact absurd hlt (not_lt.2 this)
  | zero => exact absurd hsc (by simp [isSC])
  | add _ _ => exact absurd hsc (by simp [isSC])
  | phi _ _ => exact absurd hsc (by simp [isSC])

/-! ## `B_n` at a collapse over an own base -/

/-- **`B_n(ψ_{Ω₁}(B)) = ψ_{Ω₁}(B')`, `B_n(ψ_{Ω₁}(B + d)) = ψ_{Ω₁}(B' + B_n d)`** for every own `B` and own
`B + d` in the window, with `B = α_{n+1} + |r|` and `B' = α_ω + |σ r|` own. -/
theorem rbB_psi_base {n : ℕ} {B d : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hlo : Bc.bcC S n ≤ S.psi B (Om 1)) (hown1 : B + d ∈ S.CSet (B + d) (S.psi (B + d) (Om 1)))
    (hhi : S.psi (B + d) (Om 1) < Bc.bcC S (n + 1)) (hdL : d < Nc.ncL S ω) :
    ∃ r : Term, bcD S r ∧ B = bcAlpha S (n + 1) + val S r ∧
      bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) ∈
        S.CSet (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r))
          (S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1)) ∧
      Bc.bcB S n (S.psi B (Om 1)) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r)) (Om 1) ∧
      Bc.bcB S n (S.psi (B + d) (Om 1)) =
        S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) + Bc.bcB S n d) (Om 1) := by
  have hP1 : S.psi B (Om 1) ≤ S.psi (B + d) (Om 1) :=
    (psi_mono (S := S) Low.InR_Om_one (le_self_add : B ≤ B + d)).1
  have hαA : bcAlpha S (n + 1) ≤ B := sfArg_le (sfOwn_alpha S n) hown hlo
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : S.psi B (Om 1) < Nc.ncL S ω := (hP1.trans_lt hhi).trans hLw
  have hx1 : S.psi (B + d) (Om 1) < Nc.ncL S ω := hhi.trans hLw
  have hDe : bcD S (bcNf S d) := bcD_nf S hdL
  have hve : val S (bcNf S d) = d := val_nf S hdL
  obtain ⟨a, ha, hva⟩ := sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  obtain ⟨a1, ha1, hva1⟩ := sfNf_psi hown1 (bcD_nf S hx1).1 (val_nf S hx1)
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hD1 : bcD S (psiS Term.zero a1) := ha1 ▸ bcD_nf S hx1
  have hN := hD.1
  have hN1 := hD1.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hA1W : val S a1 < bcAlphaW S := hD1.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hlo1 : bcAlpha S (n + 1) ≤ val S a1 := by rw [hva1]; exact hαA.trans le_self_add
  have hB0 := sfB_psi (n := n) hN hlo0 hAW
  have hB1 := sfB_psi (n := n) hN1 hlo1 hA1W
  rw [hva] at hB0
  rw [hva1] at hB1
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hpre1 := (bc_pre_iff S hN1.2.1 hA1W).2 hlo1
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [sfPre_len] at this
  have hvρ1 : val S a1 = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) := by
    have := val_of_pre S hN1.2.1 hpre1; rwa [sfPre_len] at this
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  have hDρ : bcD S (bcDrop (n + 3) a) := bcD_drop hDa (n + 3)
  have hvr1 : val S (bcDrop (n + 3) a1) = val S (bcDrop (n + 3) a) + d := by
    have e1 : bcAlpha S (n + 1) + val S (bcDrop (n + 3) a1) =
        bcAlpha S (n + 1) + (val S (bcDrop (n + 3) a) + d) := by
      rw [← hvρ1, hva1, ← hva, hvρ, add_assoc]
    exact add_left_cancel e1
  have hNρ1 : NF (bcDrop (n + 3) a1) := NF_bcDrop _ hN1.2.1
  obtain ⟨hNadd, hvadd, -⟩ := addNF_spec (S := S) hDρ.1 hDe.1
  have hρ1 : bcDrop (n + 3) a1 = addNF (bcDrop (n + 3) a) (bcNf S d) :=
    eq_of_val_eq S hNρ1 hNadd (by rw [hvadd, hve, hvr1])
  have hσ1 : val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a1)) =
      val S (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)) + Bc.bcB S n d := by
    rw [hρ1, bcSig_addNF (k := n) hDρ hDe,
      (addNF_spec (S := S) (bc_NF (k := n) hDρ) (bc_NF (k := n) hDe)).2.1]
    rfl
  refine ⟨bcDrop (n + 3) a, hDρ, by rw [← hva, hvρ], ?_, hB0, ?_⟩
  · have hσN : NF (bcSig (bcPre (n + 1)) bcPreW (psiS Term.zero a)) := bc_NF (k := n) hD
    rw [bcSig_psiS_zero, bcArg_of_pre hpre, sfPre_len] at hσN
    have hsem : Sem S (psiS Term.zero (bcApp bcPreW
        (bcSig (bcPre (n + 1)) bcPreW (bcDrop (n + 3) a)))) := sem_of_NF hσN
    have h2 := hsem.2.2
    rw [show Om (val S Term.zero + 1) = Om 1 by rw [show val S Term.zero = 0 from rfl, zero_add],
      val_bcApp_preW] at h2
    exact h2
  · rw [hB1, hσ1, add_assoc]

/-! ## Multiples of `Ω₁` under `σ` -/

/-- The last summand of a chain. -/
def rbLast : Term → Term
  | Term.add _ b => rbLast b
  | t => t

theorem rbLast_val (t : Term) : ∃ x, val S t = x + val S (rbLast t) := by
  induction t with
  | add a b _ ihb =>
    obtain ⟨x, hx⟩ := ihb
    refine ⟨val S a + x, ?_⟩
    show val S a + val S b = val S a + x + val S (rbLast b)
    rw [hx, add_assoc]
  | zero => exact ⟨0, by rw [zero_add]; rfl⟩
  | inacc _ => exact ⟨0, by rw [zero_add]; rfl⟩
  | inaccW => exact ⟨0, by rw [zero_add]; rfl⟩
  | phi _ _ _ _ => exact ⟨0, by rw [zero_add]; rfl⟩
  | om _ _ => exact ⟨0, by rw [zero_add]; rfl⟩
  | psiS _ _ _ _ => exact ⟨0, by rw [zero_add]; rfl⟩
  | psiI _ _ _ => exact ⟨0, by rw [zero_add]; rfl⟩

theorem rbLast_NF : ∀ {t : Term}, NF t → t ≠ Term.zero →
    NF (rbLast t) ∧ rbLast t ≠ Term.zero ∧ (rbLast t).isPrin = true
  | Term.add _ b, h, _ => rbLast_NF (t := b) h.2.1 h.2.2.2.1
  | Term.zero, _, h0 => absurd rfl h0
  | Term.inacc _, h, _ => ⟨h, by simp [rbLast], rfl⟩
  | Term.inaccW, h, _ => ⟨h, by simp [rbLast], rfl⟩
  | Term.phi _ _, h, _ => ⟨h, by simp [rbLast], rfl⟩
  | Term.om _, h, _ => ⟨h, by simp [rbLast], rfl⟩
  | Term.psiS _ _, h, _ => ⟨h, by simp [rbLast], rfl⟩
  | Term.psiI _ _, h, _ => ⟨h, by simp [rbLast], rfl⟩

theorem rbLast_D : ∀ {t : Term}, bcD S t → bcD S (rbLast t)
  | Term.add a b, h => rbLast_D (t := b) (bcD_sub h (sub_add_r a b))
  | Term.zero, h => h
  | Term.inacc _, h => h
  | Term.inaccW, h => h
  | Term.phi _ _, h => h
  | Term.om _, h => h
  | Term.psiS _ _, h => h
  | Term.psiI _ _, h => h

theorem rbLast_sig {Ps Pt : List Term} : ∀ t : Term, rbLast (bcSig Ps Pt t) = bcSig Ps Pt (rbLast t)
  | Term.add a b => by rw [bcSig_add]; exact rbLast_sig b
  | Term.zero => by simp [rbLast]
  | Term.inacc _ => by simp [rbLast]
  | Term.inaccW => by simp [rbLast]
  | Term.phi _ _ => by simp [rbLast]
  | Term.om _ => by simp [rbLast]
  | Term.psiS s a => by
    show rbLast (bcSig Ps Pt (Term.psiS s a)) = bcSig Ps Pt (Term.psiS s a)
    rw [bcSig_psiS]
    split_ifs <;> rfl
  | Term.psiI _ _ => by simp [rbLast]

theorem rb_Om1_indec : Indec (Om (1 : Ordinal.{0})) := lq_Om1_indec

/-- **`Ω₁ ∣ x + y ↔ Ω₁ ≤ y`** for an additive principal `y`. -/
theorem rb_dvd_prin {x y : Ordinal.{0}} (hy : Indec y) : Om 1 ∣ x + y ↔ Om 1 ≤ y := by
  have h0 : (Om 1 : Ordinal.{0}) ≠ 0 := rb_Om1_indec.ne_zero
  have hdec : x + y = Om 1 * (x / Om 1) + (x % Om 1 + y) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  constructor
  · intro hd
    by_contra hlt
    push Not at hlt
    have hr : x % Om 1 + y < Om 1 := rb_Om1_indec.add_lt (Ordinal.mod_lt _ h0) hlt
    have hm := Ordinal.mod_eq_zero_of_dvd hd
    rw [hdec, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr] at hm
    exact hy.ne_zero (le_antisymm (hm ▸ le_add_self) zero_le)
  · intro h1
    have hdy : Om 1 ∣ y := lq_dvd_of_indec hy h1
    have hab : x % Om 1 + y = y := hy.add_eq ((Ordinal.mod_lt _ h0).trans_le h1)
    rw [hdec, hab]
    exact dvd_add (dvd_mul_right _ _) hdy

/-- **`Ω₁ ∣ |t|` iff the last summand of the normal form `t ≠ 0` is at least `Ω₁`.** -/
theorem rb_dvd_iff_last {t : Term} (ht : NF t) (h0 : t ≠ Term.zero) :
    Om 1 ∣ val S t ↔ Om 1 ≤ val S (rbLast t) := by
  obtain ⟨x, hx⟩ := rbLast_val (S := S) t
  obtain ⟨hN, hl0, hP⟩ := rbLast_NF ht h0
  have hI : Indec (val S (rbLast t)) :=
    indec_iff.2 ⟨val_ne_zero S hN hl0, isPrincipal_val S hN hP⟩
  rw [hx]
  exact rb_dvd_prin hI

/-- The term `Ω₁ = om 1`. -/
def rbTOm1 : Term := Term.om tOne

theorem rb_NF_tOm1 : NF rbTOm1 := ⟨NF_tOne, by simp [tOne], rfl⟩

theorem rb_val_tOm1 : val S rbTOm1 = Om 1 := by
  show Om (val S tOne) = Om 1
  rw [val_tOne]

theorem rb_D_tOm1 : bcD S rbTOm1 := ⟨rb_NF_tOm1, by simp [rbTOm1, tOne, bcArgsLt]⟩

theorem rb_sig_tOm1 {Ps Pt : List Term} : bcSig Ps Pt rbTOm1 = rbTOm1 := by
  simp [rbTOm1, tOne]

/-- **`σ` keeps `Ω₁ ≤ |u|`** on its domain. -/
theorem rb_Om1_le_sig {n : ℕ} {u : Term} (hu : bcD S u) (h : Om 1 ≤ val S u) :
    Om 1 ≤ val S (bcSig (bcPre (n + 1)) bcPreW u) := by
  have hc := bc_cmp' (k := n) hu rb_D_tOm1
  rw [rb_sig_tOm1, cmp_eq_compare S (bc_NF (k := n) hu) rb_NF_tOm1,
    cmp_eq_compare S hu.1 rb_NF_tOm1, rb_val_tOm1] at hc
  rw [← not_lt, ← compare_lt_iff_lt, hc, compare_lt_iff_lt, not_lt]
  exact h

/-- **`σ` keeps `Ω₁ ∣ |r|`** on its domain. -/
theorem rb_dvd_sig {n : ℕ} {r : Term} (hr : bcD S r) (h : Om 1 ∣ val S r) :
    Om 1 ∣ val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  by_cases h0 : r = Term.zero
  · subst h0; rw [bcSig_zero]; exact dvd_zero _
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  rw [rb_dvd_iff_last hN' h0', rbLast_sig]
  exact rb_Om1_le_sig (rbLast_D hr) ((rb_dvd_iff_last hr.1 h0).1 h)

theorem rb_dvd_OmW : Om 1 ∣ Om (ω : Ordinal.{0}) :=
  lq_dvd_of_indec (lq_SC_indec (SC_Om omega0_pos.ne')) (Om_le_Om.2 one_lt_omega0.le)

theorem rb_Om1_lt_Pp : Om 1 < Nc.ncPp S := by
  have h := InaccSeq.Om_lt_psiS (S := S) (Om Ordinal.omega0 + Om Ordinal.omega0) 1 (τ := 1)
  exact h.2 le_rfl

theorem rb_dvd_Pp : Om 1 ∣ Nc.ncPp S :=
  lq_dvd_of_indec (lq_SC_indec (Nc.ncPp_SC S)) rb_Om1_lt_Pp.le

theorem rb_dvd_alpha (k : ℕ) : Om 1 ∣ bcAlpha S k :=
  dvd_add (dvd_add rb_dvd_OmW rb_dvd_OmW) (dvd_mul_of_dvd_left rb_dvd_Pp _)

theorem rb_dvd_alphaW : Om 1 ∣ bcAlphaW S := by
  refine dvd_add (dvd_add rb_dvd_OmW rb_dvd_OmW) (lq_dvd_of_indec ?_ ?_)
  · exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
  · rw [← Bt.Om1_opow]
    exact opow_le_opow_right omega0_pos (rb_Om1_lt_Pp.le.trans le_self_add)

/-- `Ω₁ ∣ a + v ↔ Ω₁ ∣ v` when `Ω₁ ∣ a`. -/
theorem rb_dvd_add_left {a v : Ordinal.{0}} (ha : Om 1 ∣ a) : Om 1 ∣ a + v ↔ Om 1 ∣ v := by
  obtain ⟨k, rfl⟩ := ha
  rw [Ordinal.dvd_iff_mod_eq_zero, Ordinal.dvd_iff_mod_eq_zero, Ordinal.mul_add_mod_self]

/-- **`Ω₁ ∣ B` gives `Ω₁ ∣ B'`** for `B = α_{n+1} + |r|`, `B' = α_ω + |σ r|`. -/
theorem rbB_dvd {n : ℕ} {B : Ordinal.{0}} {r : Term} (hr : bcD S r) (hB : B = bcAlpha S (n + 1) + val S r)
    (h : Om 1 ∣ B) : Om 1 ∣ bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) := by
  rw [hB, rb_dvd_add_left (rb_dvd_alpha _)] at h
  rw [rb_dvd_add_left rb_dvd_alphaW]
  exact rb_dvd_sig hr h

/-! ## Membership and order -/

/-- `b < B`, `Ω₁ ∣ B`, `D < Ω₁` give `b + D < B`. -/
theorem rb_add_lt_of_dvd {B b D : Ordinal.{0}} (hB : Om 1 ∣ B) (hb : b < B) (hD : D < Om 1) : b + D < B := by
  have h0 : (Om 1 : Ordinal.{0}) ≠ 0 := rb_Om1_indec.ne_zero
  obtain ⟨k, rfl⟩ := hB
  have hdiv : b / Om 1 < k := (Ordinal.lt_mul_iff_div_lt h0).1 hb
  have hq : b / Om 1 + 1 ≤ k := Order.add_one_le_of_lt hdiv
  have hr : b % Om 1 + D < Om 1 := rb_Om1_indec.add_lt (Ordinal.mod_lt _ h0) hD
  calc b + D = Om 1 * (b / Om 1) + (b % Om 1 + D) := by rw [← add_assoc, Ordinal.div_add_mod]
    _ < Om 1 * (b / Om 1) + Om 1 := (add_lt_add_iff_left _).2 hr
    _ = Om 1 * (b / Om 1 + 1) := by rw [mul_add, mul_one]
    _ ≤ Om 1 * k := mul_le_mul_left' hq _

/-- **`Cl(a, b)` contains `x mod Ω₁` and `Ω₁·(x / Ω₁)` with `x`.** -/
theorem rb_mod_mem {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → x % Om 1 ∈ S.CSet a b ∧ Om 1 * (x / Om 1) ∈ S.CSet a b := by
  have h0 : (Om 1 : Ordinal.{0}) ≠ 0 := rb_Om1_indec.ne_zero
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_mod, Ordinal.zero_div, mul_zero]
    exact ⟨CSet.zero_mem _ _, CSet.zero_mem _ _⟩
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlt := lead_add_tail hx0
  rcases le_or_gt (Om 1) (lead x) with h1 | h1
  · have hI : Indec (lead x) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    obtain ⟨k, hk⟩ := lq_dvd_of_indec hI h1
    obtain ⟨ih1, ih2⟩ := IH (tail x) (tail_lt hx0) ht
    have e1 : x % Om 1 = tail x % Om 1 := by
      conv_lhs => rw [← hlt, hk]
      rw [Ordinal.mul_add_mod_self]
    have e2 : Om 1 * (x / Om 1) = lead x + Om 1 * (tail x / Om 1) := by
      conv_lhs => rw [← hlt, hk]
      rw [Ordinal.mul_add_div _ h0, mul_add, hk]
    rw [e1, e2]
    exact ⟨ih1, CSet.add_mem hl ih2⟩
  · have hlog : Ordinal.log ω x < Om 1 := by
      have := h1
      unfold lead at this
      rw [← Bt.Om1_opow] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hlog1 : Ordinal.log ω x + 1 < Om 1 :=
      (Om_isSuccLimit one_ne_zero).add_one_lt hlog
    have hxO : x < Om 1 := by
      refine (lt_opow_log_add_one x).trans ?_
      rw [← Bt.Om1_opow]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 hlog1
    rw [Ordinal.mod_eq_of_lt hxO, Ordinal.div_eq_zero_of_lt hxO, mul_zero]
    exact ⟨hx, CSet.zero_mem _ _⟩

/-! ## The fixed points of `Γ_` -/

/-- **Below a strongly critical `x > τ` that is not a fixed point of `Γ_`, there is a largest `p < x` that is `τ` or a
fixed point above `τ`.** -/
theorem rb_base_below {τ x : Ordinal.{0}} (hτx : τ < x) (hnf : gamma x ≠ x) :
    ∃ p, (p = τ ∨ (τ < p ∧ gamma p = p)) ∧ p < x ∧ ∀ q, gamma q = q → τ < q → q < x → q ≤ p := by
  set P : Set Ordinal.{0} := {q | q < x ∧ (q = τ ∨ (τ < q ∧ gamma q = q))} with hPdef
  have hτP : τ ∈ P := ⟨hτx, Or.inl rfl⟩
  have hPne : P.Nonempty := ⟨τ, hτP⟩
  have hPb : BddAbove P := ⟨x, fun q hq => hq.1.le⟩
  set p := sSup P with hpdef
  have hpx : p ≤ x := csSup_le hPne fun q hq => hq.1.le
  have hτp : τ ≤ p := le_csSup hPb hτP
  have hmax : ∀ q, gamma q = q → τ < q → q < x → q ≤ p := fun q hq hτq hqx =>
    le_csSup hPb ⟨hqx, Or.inr ⟨hτq, hq⟩⟩
  have hbase : p = τ ∨ (τ < p ∧ gamma p = p) := by
    by_cases hmem : p ∈ P
    · exact hmem.2
    right
    have hτp' : τ < p := lt_of_le_of_ne hτp fun e => hmem (e ▸ hτP)
    refine ⟨hτp', ?_⟩
    have hcof : ∀ a < p, ∃ f, a < f ∧ f < p ∧ τ < f ∧ gamma f = f := by
      intro a ha
      obtain ⟨f, hfP, hf⟩ := exists_lt_of_lt_csSup hPne (max_lt ha hτp')
      have hfp : f < p := lt_of_le_of_ne (le_csSup hPb hfP) fun e => hmem (e ▸ hfP)
      have hτf : τ < f := (le_max_right a τ).trans_lt hf
      rcases hfP.2 with e | ⟨-, hff⟩
      · exact absurd e hτf.ne'
      · exact ⟨f, (le_max_left a τ).trans_lt hf, hfp, hτf, hff⟩
    have hlim : IsSuccLimit p := by
      refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le hτp').ne', ?_⟩
      refine isSuccPrelimit_of_succ_lt fun a ha => ?_
      obtain ⟨f, haf, hfp, -⟩ := hcof a ha
      exact (Order.succ_le_of_lt haf).trans_lt hfp
    refine le_antisymm (not_lt.1 fun hlt => ?_) (lq_le_gamma p)
    obtain ⟨b, hb, hpb⟩ := (isNormal_gamma.lt_iff_exists_lt hlim).1 hlt
    obtain ⟨f, hbf, hfp, -, hff⟩ := hcof b hb
    have : gamma b < f := by rw [← hff]; exact gamma_lt_gamma.2 hbf
    exact absurd (hpb.trans (this.trans hfp)) (lt_irrefl _)
  have hpx' : p < x := by
    refine lt_of_le_of_ne hpx fun e => ?_
    rcases hbase with h | ⟨-, h⟩
    · exact hτx.ne (h ▸ e)
    · exact hnf (e ▸ h)
  exact ⟨p, hbase, hpx', hmax⟩

/-- **`ψ_{Ω₁}(B)` is a fixed point of `Γ_`** for every own `B` with `Ω₁ ∣ B` and `ψ_{Ω₁}(A₀) < ψ_{Ω₁}(B)` for an own
`A₀`. -/
theorem rbFix_of_dvd {A0 B : Ordinal.{0}} (hown0 : A0 ∈ S.CSet A0 (S.psi A0 (Om 1)))
    (hown : B ∈ S.CSet B (S.psi B (Om 1))) (hdvd : Om 1 ∣ B) (hlt : S.psi A0 (Om 1) < S.psi B (Om 1)) :
    gamma (S.psi B (Om 1)) = S.psi B (Om 1) := by
  set x := S.psi B (Om 1) with hxdef
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  by_contra hnf
  obtain ⟨y, hy⟩ := lq_SC_gamma hxSC
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ lq_le_gamma y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rb_base_below hlt hnf
  have hpSC : SC p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact SC_psi Low.InR_Om_one A0
    · rw [← h]; exact lq_gamma_SC p
  obtain ⟨c, hc⟩ := lq_SC_gamma hpSC
  obtain ⟨Bp, hownp, hBp⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p := by
    rcases hbase with e | -
    · exact ⟨A0, hown0, e.symm⟩
    · exact rb_own_of_SC hpSC hpx
  have hcy : c < y := gamma_lt_gamma.1 (by rw [hc, hy]; exact hpx)
  set D := y - c with hDdef
  have hcD : c + D = y := Ordinal.add_sub_cancel_of_le hcy.le
  have hcond : ∀ d, d ≤ D → d < gamma (c + d) := by
    intro d hd
    by_contra hle
    push Not at hle
    have hz : gamma (c + d) = c + d :=
      le_antisymm (hle.trans le_add_self) (lq_le_gamma _)
    have hdz : d = c + d := le_antisymm le_add_self (hz ▸ hle)
    have hzy : c + d ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c).2 hd
    have hpz : p ≤ c + d := by rw [← hc, ← hz]; exact gamma_le_gamma.2 le_self_add
    rcases hpz.lt_or_eq with hpz | hpz
    · have hτz : S.psi A0 (Om 1) < c + d := by
        rcases hbase with e | ⟨h, -⟩
        · rw [← e]; exact hpz
        · exact h.trans hpz
      exact absurd (hmax _ hz hτz (hzy.trans_lt hyx)) (not_le.2 hpz)
    · -- `c + d = p`: then `p` is a fixed point, `c = p`, `d = 0`
      have hpp : gamma p = p := by rw [hpz]; exact hz
      have hcp : c = p := isNormal_gamma.strictMono.injective (hc.trans hpp.symm)
      have hd0 : d = 0 := by
        have : c + d = c + 0 := by rw [add_zero, ← hpz, hcp]
        exact add_left_cancel this
      rw [hd0, add_zero] at hle
      exact absurd hle (not_le.2 gamma_pos)
  obtain ⟨hval, hψ⟩ := lq_psi_gamma_of hownp (hc.trans hBp.symm) D hcond
  have hψx : S.psi (Bp + D) (Om 1) = x := by rw [hψ, hcD, hy]
  have hBpB : Bp < B := by
    have h := compare_psi Low.InR_Om_one hownp hown
    rw [hBp, compare_lt_iff_lt.2 hpx] at h
    exact compare_lt_iff_lt.1 h.symm
  have hDx : D < x := (Ordinal.sub_le_self y c).trans_lt hyx
  have hlt2 : Bp + D < B := rb_add_lt_of_dvd hdvd hBpB (hDx.trans hx1)
  have hmem : Bp + D ∈ S.CSet B x :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one hBpB.le).2 hownp) (CSet.of_lt hDx)
  have hψmem : S.psi (Bp + D) (Om 1) ∈ S.CSet B x :=
    CSet.psi_mem hlt2 Low.InR_Om_one (mem_CSet_psi Low.InR_Om_one B) hmem
  have := lt_psi_of_mem Low.InR_Om_one hψmem (psi_lt Low.InR_Om_one _)
  rw [hψx] at this
  exact lt_irrefl _ this

/-- **`Ω₁ ∣ B` for every own `B` with `ψ_{Ω₁}(B)` a fixed point of `Γ_`.** -/
theorem rbDvd_of_fix {B : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : gamma (S.psi B (Om 1)) = S.psi B (Om 1)) : Om 1 ∣ B := by
  have h0 : (Om 1 : Ordinal.{0}) ≠ 0 := rb_Om1_indec.ne_zero
  set p := S.psi B (Om 1) with hpdef
  have hpSC : SC p := SC_psi Low.InR_Om_one B
  by_contra hnd
  set D0 := B % Om 1 with hD0
  set B0 := Om 1 * (B / Om 1) with hB0
  have hD00 : D0 ≠ 0 := fun e => hnd (Ordinal.dvd_of_mod_eq_zero e)
  have hBe : B0 + D0 = B := Ordinal.div_add_mod B (Om 1)
  obtain ⟨hD0m, hB0m⟩ := rb_mod_mem (S := S) B hown
  have hD0p : D0 < p := lt_psi_of_mem Low.InR_Om_one hD0m (Ordinal.mod_lt _ h0)
  have hB0B : B0 < B := by
    rw [← hBe]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD00)
  have hB0p : S.psi B0 (Om 1) < p := psi_lt_psi_of_mem Low.InR_Om_one hB0B hB0m
  obtain ⟨c0, hc0⟩ := lq_SC_gamma (SC_psi Low.InR_Om_one B0)
  have hbound : ∀ d, S.psi (B0 + d) (Om 1) ≤ gamma (c0 + d) := by
    intro d
    induction d using WellFoundedLT.induction with
    | ind d IH =>
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero, add_zero, hc0]
    refine lq_psi_le (lq_gamma_SC _) ?_ fun d' hd' => ?_
    · rw [← hc0]; exact gamma_lt_gamma.2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0))
    · exact (IH d' hd').trans_lt (gamma_lt_gamma.2 ((add_lt_add_iff_left _).2 hd'))
  have hple : p ≤ gamma (c0 + D0) := by rw [hpdef, ← hBe]; exact hbound D0
  have hpc : p ≤ c0 + D0 := by
    rw [← hfix] at hple; exact gamma_le_gamma.1 hple
  have hc0p : c0 < p := (lq_le_gamma c0).trans_lt (hc0 ▸ hB0p)
  have := (lq_SC_indec hpSC).add_lt hc0p hD0p
  exact absurd hpc (not_le.2 this)

end Googology.Trans.PoR.InaccPsi.R2.Rb
