import Googology.Trans.PoR.InaccPsi.R2.VmTop
import Googology.Trans.PoR.InaccPsi.R2.UoB
import Googology.Trans.PoR.InaccPsi.R2.VjD

/-!
# The `B_n` move one cardinal up: the datum below `Ω₂`, `K⁽¹⁾`, powers of `Ω₂`, divisibility

`W = Ω₂ = Om (1 + 1)`, `B_n = Bc.bcB S n = val ∘ σ ∘ nf`, `MvD` its normal-form domain, `ulDatT S κ t` the largest
leaf of `t` below `κ` (subscripts included), `ulDat S κ x = ulDatT S κ (nf x)`, `K⁽¹⁾_q = Ul.UlK S 1 q`.  The port of
`Uo.uoDatT_sig` / `Uo.uoDat_B` / `Uo.uo_K_B` from the threshold `Ω₁` to every threshold `κ ≥ Ω₁` fixed by `B_n`, and
of `Vj.vjB_Wpow` from `Ω₁` to `Ω₂`:

* `vpDatT_sig` (**`ulDatT κ (σ t) = B_n (ulDatT κ t)`** on the domain of `σ`, for `Ω₁ ≤ κ ∈ MvD`, `B_n κ = κ`),
  `vpDat_B` (**`ulDat κ (B_n x) = B_n (ulDat κ x)`** for `x ∈ MvD`), `vpDatW_B` (the case `κ = Ω₂`);
* `vpK1_B` (**`B_n x ∈ K⁽¹⁾_{B_n q} ↔ x ∈ K⁽¹⁾_q`** for `x, q ∈ MvD`, `q` and `B_n q` strongly critical in `(Ω₁, Ω₂]`);
* `vp_W_eq`, `vp_W_indec`, `vpB_W` (**`B_n(Ω₂^γ·D) = Ω₂^{B_n γ}·B_n D`** for `γ, D ∈ MvD`), `vpB_Wpow`;
* `vp_dvd_B_iff`, `vp_dvd_B` (**`B_n u ∣ B_n x ↔ u ∣ x`** for indecomposable `u`, `B_n u`), `vp_add_le_of_dvd` (**`u ∣ B`, `K < B`
  give `K + u ≤ B`** for indecomposable `u`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-! ## The datum below a fixed threshold -/

/-- **`ulDatT κ (σ t) = B_n (ulDatT κ t)`** on the domain `bcD` of `σ`, for a threshold `Ω₁ ≤ κ` in the domain with
`B_n κ = κ`; the datum is in `MvD`. -/
theorem vpDatT_sig {n : ℕ} {κ : Ordinal.{0}} (hκ1 : Om 1 ≤ κ) (hDκ : MvD S κ) (hBκ : Bc.bcB S n κ = κ) :
    ∀ t : Term, bcD S t →
      MvD S (ulDatT S κ t) ∧ ulDatT S κ (bcSig (bcPre (n + 1)) bcPreW t) = Bc.bcB S n (ulDatT S κ t) := by
  have hD0 : MvD S 0 := mvD_of_term (S := S) bcD_zero
  have hsmall : ∀ t : Term, bcD S t → (val S (bcSig (bcPre (n + 1)) bcPreW t) < κ ↔ val S t < κ) :=
    fun t hD => by
      have h := mvB_lt_iff (k := n) (mvD_of_term hD) hDκ
      rw [hBκ, mvB_term hD] at h
      exact h
  have hsm : ∀ t : Term, bcD S t → val S t < κ →
      MvD S (ulDatT S κ t) ∧ ulDatT S κ (bcSig (bcPre (n + 1)) bcPreW t) = Bc.bcB S n (ulDatT S κ t) :=
    fun t hD h => by
      have h' := (hsmall _ hD).2 h
      rw [ulDatT_small h, ulDatT_small h', ← mvB_term (k := n) hD]; exact ⟨mvD_of_term hD, rfl⟩
  intro t
  induction t with
  | zero => intro _; exact ⟨hD0, by rw [bcSig_zero]; exact (Bc.bcB_zero n).symm⟩
  | inacc m =>
    intro hD
    by_cases h : val S (inacc m) < κ
    · exact hsm _ hD h
    · have e : ulDatT S κ (inacc m) = 0 := by simp only [ulDatT, if_neg h]
      rw [bcSig_inacc, e, Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | inaccW =>
    intro hD
    by_cases h : val S inaccW < κ
    · exact hsm _ hD h
    · have e : ulDatT S κ inaccW = 0 := by simp only [ulDatT, if_neg h]
      rw [bcSig_inaccW, e, Bc.bcB_zero]; exact ⟨hD0, rfl⟩
  | add a b iha ihb =>
    intro hD
    by_cases h : val S (add a b) < κ
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (add a b)) < κ := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_add] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDb, hσb⟩ := ihb ⟨hD.1.2.1, hD.2.2⟩
      simp only [ulDatT, if_neg h, if_neg h']
      rw [hσa, hσb, Ti.tiB_max hDa hDb]
      exact ⟨Ti.tiMvD_max hDa hDb, rfl⟩
  | phi a b iha ihb =>
    intro hD
    by_cases h : val S (phi a b) < κ
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (phi a b)) < κ := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_phi] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDb, hσb⟩ := ihb ⟨hD.1.2.1, hD.2.2⟩
      simp only [ulDatT, if_neg h, if_neg h']
      rw [hσa, hσb, Ti.tiB_max hDa hDb]
      exact ⟨Ti.tiMvD_max hDa hDb, rfl⟩
  | om a iha =>
    intro hD
    by_cases h : val S (om a) < κ
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (om a)) < κ := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_om] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2⟩
      simp only [ulDatT, if_neg h, if_neg h']
      exact ⟨hDa, hσa⟩
  | psiS σ a ihs iha =>
    intro hD
    by_cases h : val S (psiS σ a) < κ
    · exact hsm _ hD h
    · have hs : σ ≠ Term.zero := by
        rintro rfl
        apply h
        show S.psi (val S a) (Om (val S Term.zero + 1)) < κ
        have e : val S Term.zero + 1 = 1 := by simp [val]
        rw [e]; exact (psi_lt Low.InR_Om_one _).trans_le hκ1
      have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (psiS σ a)) < κ := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_psiS_ne hs] at h' ⊢
      obtain ⟨hDs, hσs⟩ := ihs ⟨hD.1.1, hD.2.1⟩
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.2.1, hD.2.2.1⟩
      simp only [ulDatT, if_neg h, if_neg h']
      rw [hσs, hσa, Ti.tiB_max hDs hDa]
      exact ⟨Ti.tiMvD_max hDs hDa, rfl⟩
  | psiI m a iha =>
    intro hD
    by_cases h : val S (psiI m a) < κ
    · exact hsm _ hD h
    · have h' : ¬ val S (bcSig (bcPre (n + 1)) bcPreW (psiI m a)) < κ := fun h'' => h ((hsmall _ hD).1 h'')
      rw [bcSig_psiI] at h' ⊢
      obtain ⟨hDa, hσa⟩ := iha ⟨hD.1.1, hD.2⟩
      simp only [ulDatT, if_neg h, if_neg h']
      exact ⟨hDa, hσa⟩

/-- **`ulDat κ (B_n x) = B_n (ulDat κ x)`** for every `x ∈ MvD` (`Ω₁ ≤ κ ∈ MvD`, `B_n κ = κ`). -/
theorem vpDat_B {n : ℕ} {κ x : Ordinal.{0}} (hκ1 : Om 1 ≤ κ) (hDκ : MvD S κ) (hBκ : Bc.bcB S n κ = κ)
    (hx : MvD S x) : MvD S (ulDat S κ x) ∧ ulDat S κ (Bc.bcB S n x) = Bc.bcB S n (ulDat S κ x) := by
  have hN : NF (bcSig (bcPre (n + 1)) bcPreW (bcNf S x)) := bc_NF hx.2
  have e : bcNf S (Bc.bcB S n x) = bcSig (bcPre (n + 1)) bcPreW (bcNf S x) := by
    unfold Bc.bcB; exact bcNf_val S hN
  unfold ulDat
  rw [e]
  exact vpDatT_sig hκ1 hDκ hBκ _ hx.2

theorem vp_Om1_le_W : (Om 1 : Ordinal.{0}) ≤ Om (1 + 1) := Om_le_Om.2 le_self_add

/-- **`ulDat Ω₂ (B_n x) = B_n (ulDat Ω₂ x)`** for `x ∈ MvD`. -/
theorem vpDatW_B {n : ℕ} {x : Ordinal.{0}} (hx : MvD S x) :
    MvD S (ulDat S (Om (1 + 1)) x) ∧ ulDat S (Om (1 + 1)) (Bc.bcB S n x) = Bc.bcB S n (ulDat S (Om (1 + 1)) x) :=
  vpDat_B vp_Om1_le_W (Ld.ldOm2_D (S := S) (k := n)).1 (Ld.ldOm2_D (S := S) (k := n)).2 hx

theorem vp_one_lt_omega : (1 : Ordinal.{0}) < ω := one_lt_omega0

/-- **`B_n x ∈ K⁽¹⁾_{B_n q} ↔ x ∈ K⁽¹⁾_q`** for `x, q ∈ MvD`, `q` and `B_n q` strongly critical in `(Ω₁, Ω₂]`. -/
theorem vpK1_B {n : ℕ} {x q : Ordinal.{0}} (hx : MvD S x) (hqD : MvD S q) (hq : SC q) (h1q : Om 1 < q)
    (hq2 : q ≤ Om (1 + 1)) (hBq : SC (Bc.bcB S n q)) (h1Bq : Om 1 < Bc.bcB S n q)
    (hBq2 : Bc.bcB S n q ≤ Om (1 + 1)) :
    UlK S 1 (Bc.bcB S n q) (Bc.bcB S n x) ↔ UlK S 1 q x := by
  have hBx : Bc.bcB S n x ∈ ⋃ a, S.CSet a 0 := by
    unfold Bc.bcB; exact mem_iUnion.2 (Term.exists_mem_CSet S _)
  rw [Uo.uo_K_iff_dat vp_one_lt_omega hBq h1Bq hBq2 hBx, Uo.uo_K_iff_dat vp_one_lt_omega hq h1q hq2 hx.1]
  obtain ⟨hDd, hB⟩ := vpDatW_B (n := n) hx
  rw [hB]
  exact mvB_lt_iff hDd hqD

/-- `B_n` keeps `≤` on its domain. -/
theorem vpB_le {n : ℕ} {a b : Ordinal.{0}} (ha : MvD S a) (hb : MvD S b) (h : a ≤ b) :
    Bc.bcB S n a ≤ Bc.bcB S n b := by
  rcases h.lt_or_eq with h' | h'
  · exact ((mvB_lt_iff ha hb).2 h').le
  · rw [h']

/-! ## Powers of `Ω₂` -/

theorem vp_W_eq (j : Ordinal.{0}) : Om (1 + 1) ^ j = ω ^ (Om (1 + 1) * j) := Ui.ui_W_eq 1 j

theorem vp_W_indec (j : Ordinal.{0}) : Indec (Om (1 + 1) ^ j) := by rw [vp_W_eq]; exact indec_opow _

/-- **`B_n(Ω₂^γ·D) = Ω₂^{B_n γ}·B_n D`** for `γ, D ∈ MvD`. -/
theorem vpB_W {n : ℕ} {γ D : Ordinal.{0}} (hγ : MvD S γ) (hD : MvD S D) :
    MvD S (Om (1 + 1) ^ γ * D) ∧
      Bc.bcB S n (Om (1 + 1) ^ γ * D) = Om (1 + 1) ^ Bc.bcB S n γ * Bc.bcB S n D := by
  obtain ⟨hDO, hBO⟩ := Ld.ldOm2_D (S := S) (k := n)
  have hO : ω ^ (Om (1 + 1) : Ordinal.{0}) = Om (1 + 1) := Ui.ui_W_opow 1
  obtain ⟨hDm, hBm⟩ := Vj.vjB_mulOp (n := n) hDO γ hγ
  rw [hO] at hDm
  rw [hO, hBO, hO] at hBm
  have h := Vj.vjB_mulOp (n := n) hDm D hD
  rw [hBm, ← vp_W_eq, ← vp_W_eq] at h
  exact h

/-- **`B_n(Ω₂^γ) = Ω₂^{B_n γ}`** for `γ ∈ MvD`. -/
theorem vpB_Wpow {n : ℕ} {γ : Ordinal.{0}} (hγ : MvD S γ) :
    MvD S (Om (1 + 1) ^ γ) ∧ Bc.bcB S n (Om (1 + 1) ^ γ) = Om (1 + 1) ^ Bc.bcB S n γ := by
  have h := vpB_W (n := n) hγ (Rk.rk_one_D (S := S))
  rw [mul_one, Mw.mwB_one, mul_one] at h
  exact h

/-! ## Divisibility -/

/-- **`B_n u ∣ B_n x ↔ u ∣ x`** for `u, x ∈ MvD` with `u` and `B_n u` indecomposable. -/
theorem vp_dvd_B_iff {n : ℕ} {u x : Ordinal.{0}} (hDu : MvD S u) (hI : Indec u) (hI' : Indec (Bc.bcB S n u))
    (hx : MvD S x) : Bc.bcB S n u ∣ Bc.bcB S n x ↔ u ∣ x := by
  set r := bcNf S x with hrdef
  have hr : bcD S r := hx.2
  have hBx : Bc.bcB S n x = val S (bcSig (bcPre (n + 1)) bcPreW r) := by
    conv_lhs => rw [← mvD_val hx]
    exact mvB_term hr
  have hxr : x = val S r := (mvD_val hx).symm
  rw [hBx]
  by_cases h0 : r = Term.zero
  · rw [h0, bcSig_zero, hxr, h0]; exact ⟨fun _ => dvd_zero _, fun _ => dvd_zero _⟩
  have hN' := bc_NF (k := n) hr
  have h0' : bcSig (bcPre (n + 1)) bcPreW r ≠ Term.zero := bcSig_ne_zero h0
  have hDl : bcD S (Rb.rbLast r) := Rb.rbLast_D hr
  have hDv := mvD_of_term hDl
  rw [Rd.rd_dvd_iff_last hI' hN' h0', Rb.rbLast_sig, hxr, Rd.rd_dvd_iff_last hI hr.1 h0, ← mvB_term (k := n) hDl]
  constructor
  · intro h; exact not_lt.1 fun hlt => absurd ((mvB_lt_iff hDv hDu).2 hlt) (not_lt.2 h)
  · intro h; exact not_lt.1 fun hlt => absurd ((mvB_lt_iff hDv hDu).1 hlt) (not_lt.2 h)

/-- **`u ∣ x ⇒ B_n u ∣ B_n x`** for `u, x ∈ MvD` with `u` and `B_n u` indecomposable. -/
theorem vp_dvd_B {n : ℕ} {u x : Ordinal.{0}} (hDu : MvD S u) (hI : Indec u) (hI' : Indec (Bc.bcB S n u))
    (hx : MvD S x) (h : u ∣ x) : Bc.bcB S n u ∣ Bc.bcB S n x := (vp_dvd_B_iff hDu hI hI' hx).2 h

/-- **`u ∣ B` and `K < B` give `K + u ≤ B`** for an indecomposable `u`. -/
theorem vp_add_le_of_dvd {u K B : Ordinal.{0}} (hu : Indec u) (hdvd : u ∣ B) (hKB : K < B) : K + u ≤ B := by
  have hu0 : u ≠ 0 := hu.ne_zero
  obtain ⟨b, rfl⟩ := hdvd
  have hK : K = u * (K / u) + K % u := (Ordinal.div_add_mod K u).symm
  have habs : K % u + u = u := hu.add_eq (Ordinal.mod_lt K hu0)
  have e : K + u = u * (K / u + 1) := by
    conv_lhs => rw [hK]
    rw [add_assoc, habs, mul_add_one]
  rw [e]
  have ht : K / u < b := by
    by_contra hc
    push Not at hc
    have h1 : u * b ≤ u * (K / u) := mul_le_mul_right hc u
    have h2 : u * (K / u) ≤ K := Ordinal.mul_div_le K u
    exact absurd (h1.trans h2) (not_le.2 hKB)
  exact mul_le_mul_right (Order.add_one_le_of_lt ht) u

end Googology.Trans.PoR.InaccPsi.R2.Vp
