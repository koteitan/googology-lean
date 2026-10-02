import Googology.Notation.InaccPsi.CNF

/-!
# The shape of the members of `Cl(α, β)`

Facts about the closure that the completeness proof needs.

* `Lam S`, the least fixed point of `Ω` above `I_ω`: every member of `Cl(α, β)` with
  `β ≤ Λ` is below `Λ` (`lt_Lam_of_mem`), and below `Λ` the `ψ`-free part of every closure
  is unbounded (`exists_mem_ge`).
* `exists_Om_between`: every ordinal lies in some `[Ω_σ, Ω_{σ+1})`.
* `Om_mem_of_between` (Pohlers's (172)): if `Cl(α, β)` meets `[Ω_σ, Ω_{σ+1})`, then
  `Ω_σ ∈ Cl(α, β)`.
* `mem_of_veblen_mem`: `φ(x, y) ∈ Cl(α, β)` with `x, y < φ(x, y)` gives `x, y ∈ Cl(α, β)`.
* `prin_mem_cases`: an additively principal member `z ≥ β` of `Cl(α, β)` is a constant,
  `φ(p, q)` with `p, q < z` in the closure, `Ω_p` with `p < z` in the closure, or a collapse
  `ψ_π(e)` with `π, e` in the closure and `e < α`.
* `lead_tail_mem`: the leading summand and the rest of a member are members.
* `sub_eq_of_psi_eq`: the value of `ψ_π(e)` determines `π`.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Set

universe u

/-! ## Levels of `Ω` -/

theorem le_of_Om_lt_Om_succ {a b : Ordinal.{u}} (h : Om a < Om (b + 1)) : a ≤ b :=
  Order.lt_add_one_iff.1 (Om_lt_Om.1 h)

theorem eq_of_Om_between {σ τ : Ordinal.{u}} (h1 : Om σ ≤ Om τ) (h2 : Om τ < Om (σ + 1)) :
    τ = σ :=
  le_antisymm (le_of_Om_lt_Om_succ h2) (Om_le_Om.1 h1)

/-- An ordinal strictly between `Ω_s` and `Ω_{s+1}` is not a value of `Ω`. -/
theorem not_Om_of_between {s z : Ordinal.{u}} (h1 : Om s < z) (h2 : z < Om (s + 1))
    (τ : Ordinal.{u}) : z ≠ Om τ := by
  rintro rfl
  exact absurd (Om_lt_Om.1 h1) (not_lt.2 (le_of_Om_lt_Om_succ h2))

theorem between_unique {s t z : Ordinal.{u}} (h1 : Om s < z) (h2 : z < Om (s + 1))
    (h3 : Om t < z) (h4 : z < Om (t + 1)) : s = t :=
  le_antisymm (le_of_Om_lt_Om_succ (h1.trans h4)) (le_of_Om_lt_Om_succ (h3.trans h2))

/-- Every ordinal lies in some `[Ω_σ, Ω_{σ+1})`. -/
theorem exists_Om_between (z : Ordinal.{u}) : ∃ σ, Om σ ≤ z ∧ z < Om (σ + 1) := by
  have hT : {τ : Ordinal.{u} | z < Om τ}.Nonempty :=
    ⟨z + 1, lt_of_le_of_lt (le_Om z) (Om_lt_Om.2 (lt_add_one z))⟩
  set τ := sInf {τ : Ordinal.{u} | z < Om τ} with hτ
  have hτmem : z < Om τ := csInf_mem hT
  have hbelow : ∀ τ' < τ, Om τ' ≤ z := fun τ' h' =>
    not_lt.1 (notMem_of_lt_csInf' (s := {τ : Ordinal.{u} | z < Om τ}) h')
  rcases zero_or_succ_or_isSuccLimit τ with h0 | ⟨σ, hσ⟩ | hl
  · rw [h0, Om_zero] at hτmem
    exact absurd hτmem (not_lt.2 zero_le)
  · refine ⟨σ, hbelow σ (by rw [← hσ]; exact Order.lt_succ σ), ?_⟩
    rw [← Order.succ_eq_add_one, hσ]; exact hτmem
  · exfalso
    have hτ0 : τ ≠ 0 := hl.ne_bot
    have h1 : (1 : Ordinal.{u}) < τ := by
      have := hl.succ_lt (pos_iff_ne_zero.2 hτ0)
      rwa [Order.succ_eq_add_one, zero_add] at this
    have : Om τ ≤ z := by
      rw [Om_of_ne_zero hτ0, isNormal_omega.le_iff_forall_le hl]
      intro τ' hτ'
      by_cases h0' : τ' = 0
      · rw [h0', omega_zero]
        have h2 := hbelow 1 h1
        rw [Om_of_ne_zero one_ne_zero] at h2
        exact le_trans (omega0_le_omega 1) h2
      · rw [← Om_of_ne_zero h0']; exact hbelow τ' hτ'
    exact absurd hτmem (not_lt.2 this)

namespace InaccSeq

variable {S : InaccSeq.{u}}

theorem SC_I (n : ℕ) : SC (S.I n) := (InR_I n).SC S

theorem SC_Iw : SC S.Iw := by rw [← S.Om_Iw]; exact SC_Om S.Iw_ne_zero

/-! ## The bound `Λ` -/

variable (S) in
/-- `Λ`, the least fixed point of `Ω` above `I_ω`. -/
noncomputable def Lam : Ordinal.{u} := nfp Om (S.Iw + 1)

theorem iter_ne_zero (n : ℕ) : Om^[n] (S.Iw + 1) ≠ 0 := by
  induction n with
  | zero => exact (add_pos_of_right zero_lt_one _).ne'
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (Om_pos ih).ne'

theorem iter_mono {n m : ℕ} (h : n ≤ m) : Om^[n] (S.Iw + 1) ≤ Om^[m] (S.Iw + 1) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_Om _)

theorem iter_mem (n : ℕ) (a b : Ordinal.{u}) : Om^[n] (S.Iw + 1) ∈ S.CSet a b := by
  induction n with
  | zero => exact CSet.succ_mem (CSet.Iw_mem a b)
  | succ n ih => rw [Function.iterate_succ_apply']; exact CSet.Om_mem ih

theorem lt_Lam_iff {x : Ordinal.{u}} : x < S.Lam ↔ ∃ n, x < Om^[n] (S.Iw + 1) := lt_nfp_iff

theorem exists_iter_two {x y : Ordinal.{u}} (hx : x < S.Lam) (hy : y < S.Lam) :
    ∃ n, x < Om^[n] (S.Iw + 1) ∧ y < Om^[n] (S.Iw + 1) := by
  obtain ⟨n, hn⟩ := lt_Lam_iff.1 hx
  obtain ⟨m, hm⟩ := lt_Lam_iff.1 hy
  exact ⟨max n m, lt_of_lt_of_le hn (iter_mono (le_max_left n m)),
    lt_of_lt_of_le hm (iter_mono (le_max_right n m))⟩

theorem Om_lt_Lam {x : Ordinal.{u}} (hx : x < S.Lam) : Om x < S.Lam := by
  obtain ⟨n, hn⟩ := lt_Lam_iff.1 hx
  refine lt_Lam_iff.2 ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact Om_lt_Om.2 hn

theorem add_lt_Lam {x y : Ordinal.{u}} (hx : x < S.Lam) (hy : y < S.Lam) : x + y < S.Lam := by
  obtain ⟨n, hn, hm⟩ := exists_iter_two hx hy
  refine lt_Lam_iff.2 ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact (SC_Om (iter_ne_zero n)).isPrincipal (lt_of_lt_of_le hn (le_Om _))
    (lt_of_lt_of_le hm (le_Om _))

theorem veblen_lt_Lam {x y : Ordinal.{u}} (hx : x < S.Lam) (hy : y < S.Lam) :
    veblen x y < S.Lam := by
  obtain ⟨n, hn, hm⟩ := exists_iter_two hx hy
  refine lt_Lam_iff.2 ⟨n + 1, ?_⟩
  rw [Function.iterate_succ_apply']
  exact (SC_Om (iter_ne_zero n)).2 _ (lt_of_lt_of_le hn (le_Om _)) _
    (lt_of_lt_of_le hm (le_Om _))

theorem Iw_lt_Lam : S.Iw < S.Lam :=
  lt_Lam_iff.2 ⟨0, lt_add_one _⟩

theorem I_lt_Lam (n : ℕ) : S.I n < S.Lam := (S.I_lt_Iw n).trans Iw_lt_Lam

theorem one_lt_Lam : (1 : Ordinal.{u}) < S.Lam :=
  lt_of_le_of_lt (Order.one_le_iff_ne_zero.2 S.Iw_ne_zero) Iw_lt_Lam

theorem add_one_lt_Lam {x : Ordinal.{u}} (hx : x < S.Lam) : x + 1 < S.Lam :=
  add_lt_Lam hx one_lt_Lam

/-- **Below `Λ`, the closures stay below `Λ`.** -/
theorem lt_Lam_of_mem {a b x : Ordinal.{u}} (hb : b ≤ S.Lam) (hx : x ∈ S.CSet a b) :
    x < S.Lam := by
  induction hx with
  | small h => exact lt_of_lt_of_le h hb
  | zero => exact lt_of_le_of_lt zero_le Iw_lt_Lam
  | inacc n => exact I_lt_Lam n
  | inaccW => exact Iw_lt_Lam
  | add _ _ ihx ihy => exact add_lt_Lam ihx ihy
  | phi _ _ ihx ihy => exact veblen_lt_Lam ihx ihy
  | om _ ih => exact Om_lt_Lam ih
  | @coll π e hπ _ _ ihπ _ => exact lt_trans (psi_lt hπ e.1) ihπ

/-- **Below `Λ`, every closure has a member above.** -/
theorem exists_mem_ge {x : Ordinal.{u}} (hx : x < S.Lam) (a b : Ordinal.{u}) :
    ∃ z ∈ S.CSet a b, x ≤ z := by
  obtain ⟨n, hn⟩ := lt_Lam_iff.1 hx
  exact ⟨_, iter_mem n a b, hn.le⟩

/-! ## Pohlers's (172) -/

/-- **(172)** If `Cl(α, β)` meets `[Ω_σ, Ω_{σ+1})`, then `Ω_σ ∈ Cl(α, β)`. -/
theorem Om_mem_of_between {a b z σ : Ordinal.{u}} (hz : z ∈ S.CSet a b) (h1 : Om σ ≤ z)
    (h2 : z < Om (σ + 1)) : Om σ ∈ S.CSet a b := by
  by_cases hσ0 : σ = 0
  · rw [hσ0, Om_zero]; exact CSet.zero_mem a b
  have hP : IsPrincipal (· + ·) (Om σ) := (SC_Om hσ0).isPrincipal
  revert h1 h2
  induction hz with
  | small h => intro h1 _; exact CSet.of_lt (lt_of_le_of_lt h1 h)
  | zero => intro h1 _; exact absurd (lt_of_lt_of_le (Om_pos hσ0) h1) (lt_irrefl _)
  | inacc n =>
    intro h1 h2
    rw [← Om_I n] at h1 h2
    rw [← eq_of_Om_between h1 h2, Om_I]
    exact CSet.I_mem a b n
  | inaccW =>
    intro h1 h2
    rw [← S.Om_Iw] at h1 h2
    rw [← eq_of_Om_between h1 h2, S.Om_Iw]
    exact CSet.Iw_mem a b
  | @add x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxσ : Om σ ≤ x
    · exact ihx hxσ (lt_of_le_of_lt le_self_add h2)
    · have hyσ : Om σ ≤ y := by
        by_contra hy
        exact absurd h1 (not_le.2 (hP (not_le.1 hxσ) (not_le.1 hy)))
      exact ihy hyσ (lt_of_le_of_lt le_add_self h2)
  | @phi x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxσ : Om σ ≤ x
    · exact ihx hxσ (lt_of_le_of_lt (left_le_veblen x y) h2)
    · by_cases hyσ : Om σ ≤ y
      · exact ihy hyσ (lt_of_le_of_lt (right_le_veblen x y) h2)
      · exact absurd h1 (not_le.2 ((SC_Om hσ0).2 _ (not_le.1 hxσ) _ (not_le.1 hyσ)))
  | @om x hx _ =>
    intro h1 h2
    rw [← eq_of_Om_between h1 h2]
    exact CSet.Om_mem hx
  | @coll π e hπ hπC heC _ _ =>
    intro h1 h2
    rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
    · have hf := Om_psiI (S := S) e.1 n
      have h1' : Om σ ≤ Om (S.psi e.1 (S.I n)) := by rw [hf]; exact h1
      have h2' : Om (S.psi e.1 (S.I n)) < Om (σ + 1) := by rw [hf]; exact h2
      rw [← eq_of_Om_between h1' h2', hf]
      exact Clos.coll (InR_I n) hπC heC
    · have hb := psiS_bounds (S := S) e.1 s
      have hσs : σ = s := le_antisymm (le_of_Om_lt_Om_succ (lt_of_le_of_lt h1 hb.2))
        (le_of_Om_lt_Om_succ (lt_trans hb.1 h2))
      rw [hσs]
      exact CSet.Om_mem (mem_of_add_one_mem (mem_of_Om_mem hπC))

/-! ## Reading members of the closure -/

/-- **`φ(x, y) ∈ Cl(α, β)` with `x, y < φ(x, y)` gives `x, y ∈ Cl(α, β)`.** -/
theorem mem_of_veblen_mem {a b x y : Ordinal.{u}} (h : veblen x y ∈ S.CSet a b)
    (hx : x < veblen x y) (hy : y < veblen x y) : x ∈ S.CSet a b ∧ y ∈ S.CSet a b := by
  suffices H : ∀ z ∈ S.CSet a b, ∀ x y, z = veblen x y → x < z → y < z →
      x ∈ S.CSet a b ∧ y ∈ S.CSet a b from H _ h x y rfl hx hy
  intro z hz
  induction hz with
  | small h => intro x y _ hx hy; exact ⟨CSet.of_lt (hx.trans h), CSet.of_lt (hy.trans h)⟩
  | zero => intro x y e _ _; exact absurd e veblen_pos.ne
  | inacc n => intro x y e hx hy; exact absurd e.symm ((SC_I n).not_veblen_lt hx hy)
  | inaccW => intro x y e hx hy; exact absurd e.symm (SC_Iw.not_veblen_lt hx hy)
  | @add p q _ _ ihp ihq =>
    intro x y e hx hy
    have hP : IsPrincipal (· + ·) (p + q) := by rw [e]; exact veblen_isPrincipal x y
    by_cases hq0 : q = 0
    · subst hq0
      simp only [add_zero] at e hx hy
      exact ihp x y e hx hy
    · have hpz : p < p + q := lt_add_of_pos_right p (pos_iff_ne_zero.2 hq0)
      have hqz : q = p + q :=
        le_antisymm le_add_self (not_lt.1 fun h => lt_irrefl _ (hP hpz h))
      rw [← hqz] at e hx hy
      exact ihq x y e hx hy
  | @phi p q hp hq ihp ihq =>
    intro x y e hx hy
    by_cases hpz : p = veblen p q
    · rw [← hpz] at e hx hy; exact ihp x y e hx hy
    by_cases hqz : q = veblen p q
    · rw [← hqz] at e hx hy; exact ihq x y e hx hy
    have hpl : p < veblen p q := lt_of_le_of_ne (left_le_veblen p q) hpz
    have hql : q < veblen p q := lt_of_le_of_ne (right_le_veblen p q) hqz
    rcases veblen_eq_veblen_iff.1 e with ⟨rfl, rfl⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact ⟨hp, hq⟩
    · rw [e, ← h] at hql; exact absurd hql (lt_irrefl _)
    · rw [h] at hy; exact absurd hy (lt_irrefl _)
  | @om p _ _ =>
    intro x y e hx hy
    by_cases hp0 : p = 0
    · rw [hp0, Om_zero] at e; exact absurd e veblen_pos.ne
    · exact absurd e.symm ((SC_Om hp0).not_veblen_lt hx hy)
  | @coll π e hπ _ _ _ _ =>
    intro x y ex hx hy
    exact absurd ex.symm ((SC_psi hπ e.1).not_veblen_lt hx hy)

/-- **The principal members of `Cl(α, β)` at or above `β`.** -/
theorem prin_mem_cases {a b z : Ordinal.{u}} (hz : z ∈ S.CSet a b) (hbz : b ≤ z)
    (hP : IsPrincipal (· + ·) z) (hz0 : z ≠ 0) :
    (∃ n, z = S.I n) ∨ z = S.Iw ∨
    (∃ p q, p ∈ S.CSet a b ∧ q ∈ S.CSet a b ∧ p < z ∧ q < z ∧ z = veblen p q) ∨
    (∃ p, p ∈ S.CSet a b ∧ p < z ∧ z = Om p) ∨
    (∃ π e, S.InR π ∧ π ∈ S.CSet a b ∧ e ∈ S.CSet a b ∧ e < a ∧ z = S.psi e π) := by
  revert hbz hP hz0
  induction hz with
  | small h => intro hbz _ _; exact absurd (lt_of_lt_of_le h hbz) (lt_irrefl _)
  | zero => intro _ _ hz0; exact absurd rfl hz0
  | inacc n => intro _ _ _; exact Or.inl ⟨n, rfl⟩
  | inaccW => intro _ _ _; exact Or.inr (Or.inl rfl)
  | @add p q _ _ ihp ihq =>
    intro hbz hP hz0
    by_cases hq0 : q = 0
    · subst hq0
      simp only [add_zero] at hbz hP hz0 ⊢
      exact ihp hbz hP hz0
    · have hpz : p < p + q := lt_add_of_pos_right p (pos_iff_ne_zero.2 hq0)
      have hqz : q = p + q :=
        le_antisymm le_add_self (not_lt.1 fun h => lt_irrefl _ (hP hpz h))
      rw [← hqz] at hbz hP hz0 ⊢
      exact ihq hbz hP hz0
  | @phi p q hp hq ihp ihq =>
    intro hbz hP hz0
    by_cases hpz : p = veblen p q
    · rw [← hpz] at hbz hP hz0 ⊢; exact ihp hbz hP hz0
    by_cases hqz : q = veblen p q
    · rw [← hqz] at hbz hP hz0 ⊢; exact ihq hbz hP hz0
    exact Or.inr (Or.inr (Or.inl ⟨p, q, hp, hq, lt_of_le_of_ne (left_le_veblen p q) hpz,
      lt_of_le_of_ne (right_le_veblen p q) hqz, rfl⟩))
  | @om p hp ihp =>
    intro hbz hP hz0
    rcases (le_Om p).lt_or_eq with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp, h, rfl⟩)))
    · rw [← h] at hbz hP hz0 ⊢; exact ihp hbz hP hz0
  | @coll π e hπ hπC heC _ _ =>
    intro _ _ _
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨π, e.1, hπ, hπC, heC, e.2, rfl⟩)))

/-- **The leading summand and the rest of a member are members.** -/
theorem lead_tail_mem {a b x : Ordinal.{u}} (hx : x ∈ S.CSet a b) (h0 : x ≠ 0) :
    lead x ∈ S.CSet a b ∧ tail x ∈ S.CSet a b := by
  have prin : ∀ {y}, y ∈ S.CSet a b → IsPrincipal (· + ·) y → y ≠ 0 →
      lead y ∈ S.CSet a b ∧ tail y ∈ S.CSet a b := fun hy hP h0 => by
    obtain ⟨h1, h2⟩ := lead_tail_of_principal hP h0
    rw [h1, h2]; exact ⟨hy, CSet.zero_mem a b⟩
  revert h0
  induction hx with
  | @small y h =>
    intro h0
    exact ⟨CSet.of_lt (lt_of_le_of_lt (lead_le h0) h), CSet.of_lt (lt_of_le_of_lt (tail_le y) h)⟩
  | zero => intro h0; exact absurd rfl h0
  | inacc n => intro h0; exact prin (CSet.I_mem a b n) (SC_I n).isPrincipal h0
  | inaccW => intro h0; exact prin (CSet.Iw_mem a b) SC_Iw.isPrincipal h0
  | @add p q hp hq ihp ihq =>
    intro h0
    by_cases hq0 : q = 0
    · subst hq0; simp only [add_zero] at h0 ⊢; exact ihp h0
    by_cases hp0 : p = 0
    · subst hp0; simp only [zero_add] at h0 ⊢; exact ihq h0
    rcases lead_tail_add hp0 hq0 with habs | ⟨hl, ht⟩
    · rw [habs]; exact ihq hq0
    · rw [hl, ht]; exact ⟨(ihp hp0).1, CSet.add_mem (ihp hp0).2 hq⟩
  | @phi p q hp hq _ _ =>
    intro h0; exact prin (CSet.phi_mem hp hq) (veblen_isPrincipal p q) h0
  | @om p hp _ =>
    intro h0
    have hp0 : p ≠ 0 := by rintro rfl; exact h0 Om_zero
    exact prin (CSet.Om_mem hp) (SC_Om hp0).isPrincipal h0
  | @coll π e hπ hπC heC _ _ =>
    intro h0; exact prin (CSet.psi_mem e.2 hπ hπC heC) (SC_psi hπ e.1).isPrincipal h0

theorem mul_nat_mem {a b p : Ordinal.{u}} (hp : p ∈ S.CSet a b) :
    ∀ n : ℕ, p * n ∈ S.CSet a b := by
  intro n
  induction n with
  | zero => rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem a b
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih hp

/-- **The value of `ψ_π(e)` determines the subscript `π`.** -/
theorem sub_eq_of_psi_eq {π κ e d : Ordinal.{u}} (hπ : S.InR π) (hκ : S.InR κ)
    (h : S.psi e π = S.psi d κ) : π = κ := by
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩ <;> rcases hκ with ⟨m, rfl⟩ | ⟨t, rfl⟩
  · rcases lt_trichotomy n m with hnm | rfl | hnm
    · have := lt_trans (psi_lt (S := S) (InR_I n) e) (I_lt_psiI_of_lt d hnm)
      rw [h] at this; exact absurd this (lt_irrefl _)
    · rfl
    · have := lt_trans (psi_lt (S := S) (InR_I m) d) (I_lt_psiI_of_lt e hnm)
      rw [h] at this; exact absurd this (lt_irrefl _)
  · have hf := Om_psiI (S := S) e n
    rw [h] at hf
    exact absurd hf.symm (not_Om_of_between (psiS_bounds d t).1 (psiS_bounds d t).2 _)
  · have hf := Om_psiI (S := S) d m
    rw [← h] at hf
    exact absurd hf.symm (not_Om_of_between (psiS_bounds e s).1 (psiS_bounds e s).2 _)
  · rw [between_unique (psiS_bounds e s).1 (psiS_bounds e s).2
      (h ▸ (psiS_bounds d t).1) (h ▸ (psiS_bounds d t).2)]

end InaccSeq

end Googology.Notation.InaccPsi
