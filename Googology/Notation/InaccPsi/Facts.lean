import Googology.Notation.InaccPsi.Ord

/-!
# Facts F5–F12 about `ψ`

The facts of the README that the comparison of terms needs:

* F5  `α₀ < α`, `α₀ ∈ Cl(α, ψ_κ α)` ⟹ `ψ_κ α₀ < ψ_κ α`;
* F6  `ψ_κ α` is strongly critical;
* F7  `Ω_σ ∈ Cl(α, β)` ⟹ `σ ∈ Cl(α, β)`;
* F8  `s + 1 ∈ Cl(α, β)` ⟹ `s ∈ Cl(α, β)`;
* F9  `Ω_s < ψ_{Ω_{s+1}} α < Ω_{s+1}`;
* F10 `ψ_{I_n} α` is a fixed point of `Ω`, above `I_{n-1}` (and above `Ω_1`);
* F11 `ξ ≤ α` ⟹ `ψ_κ ξ ≤ ψ_κ α` and `Cl(ξ, ψ_κ ξ) ⊆ Cl(α, ψ_κ α)`;
* F12 `α₀ < α` and `α₀ ∈ Cl(α₀, ψ_κ α₀)` ⟹ `ψ_κ α₀ < ψ_κ α`.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Cardinal Set

universe u

/-! ## Strongly critical ordinals and successors -/

theorem SC.add_one_lt {γ x : Ordinal.{u}} (h : SC γ) (hx : x < γ) : x + 1 < γ := by
  have h1 : x + 1 ≤ veblen x x := by
    rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt (lt_veblen x)
  exact lt_of_le_of_lt h1 (h.2 x hx x hx)

theorem SC.ne_add_one {γ : Ordinal.{u}} (h : SC γ) (s : Ordinal.{u}) : γ ≠ s + 1 := by
  intro e
  have hs : s < γ := by rw [e, ← Order.succ_eq_add_one]; exact Order.lt_succ s
  exact lt_irrefl _ (e ▸ h.add_one_lt hs)

/-- A strongly critical value of `veblen` is one of its arguments. -/
theorem SC.eq_of_veblen_eq {γ x y : Ordinal.{u}} (h : SC γ) (e : veblen x y = γ) :
    x = γ ∨ y = γ := by
  rcases lt_trichotomy x γ with hx | hx | hx
  · rcases lt_trichotomy y γ with hy | hy | hy
    · exact absurd e (h.2 x hx y hy).ne
    · exact Or.inr hy
    · exact absurd e (lt_of_lt_of_le hy (right_le_veblen x y)).ne'
  · exact Or.inl hx
  · exact absurd e (lt_of_lt_of_le hx (left_le_veblen x y)).ne'

/-- A value of `veblen` that is a successor is `1`. -/
theorem veblen_eq_add_one {x y s : Ordinal.{u}} (e : veblen x y = s + 1) : s = 0 := by
  obtain ⟨c, hc⟩ := veblen_mem_range_opow x y
  have hp : Ordinal.IsPrincipal (· + ·) (s + 1) := by
    rw [← e, ← hc]; exact isPrincipal_add_omega0_opow c
  by_contra hs
  have h1 : s < s + 1 := by rw [← Order.succ_eq_add_one]; exact Order.lt_succ s
  have h2 : (1 : Ordinal.{u}) < s + 1 := by
    have : (1 : Ordinal.{u}) ≤ s := Ordinal.one_le_iff_ne_zero.2 hs
    rw [← Order.succ_eq_add_one]; exact Order.lt_succ_iff.2 this
  exact lt_irrefl _ (hp h1 h2)

theorem Om_ne_add_one (v s : Ordinal.{u}) : Om v ≠ s + 1 := by
  by_cases hv : v = 0
  · rw [hv, Om_zero]; exact (Ordinal.add_one_ne_zero s).symm
  · exact (SC_Om hv).ne_add_one s

/-- `x + y = s + 1` with `y ≠ 0` forces `y = t + 1` and `s = x + t`. -/
theorem add_eq_add_one {x y s : Ordinal.{u}} (e : x + y = s + 1) (hy : y ≠ 0) :
    ∃ t, y = t + 1 ∧ s = x + t := by
  rcases zero_or_succ_or_isSuccLimit y with h | ⟨t, rfl⟩ | h
  · exact absurd h hy
  · refine ⟨t, (Order.succ_eq_add_one t), ?_⟩
    rw [Order.succ_eq_add_one, ← add_assoc] at e
    exact (Order.succ_injective (by rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact e)).symm
  · have hl := isSuccLimit_add x h
    rw [e, ← Order.succ_eq_add_one] at hl
    exact absurd hl (Order.not_isSuccLimit_succ s)

/-- Between two consecutive cardinals, the comparison with any `Ω_τ` is decided by `s`. -/
theorem lt_Om_iff_of_between {s x τ : Ordinal.{u}} (h1 : Om s < x) (h2 : x < Om (s + 1)) :
    x < Om τ ↔ s < τ := by
  constructor
  · intro h
    by_contra hτ
    exact lt_asymm h (lt_of_le_of_lt (Om_le_Om.2 (not_lt.1 hτ)) h1)
  · intro h
    have : s + 1 ≤ τ := by rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h
    exact lt_of_lt_of_le h2 (Om_le_Om.2 this)

theorem Om_lt_iff_of_between {s x τ : Ordinal.{u}} (h1 : Om s < x) (h2 : x < Om (s + 1)) :
    Om τ < x ↔ τ ≤ s := by
  constructor
  · intro h
    by_contra hτ
    have : s + 1 ≤ τ := by rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt (not_le.1 hτ)
    exact lt_asymm h (lt_of_lt_of_le h2 (Om_le_Om.2 this))
  · intro h
    exact lt_of_le_of_lt (Om_le_Om.2 h) h1

namespace InaccSeq

variable {S : InaccSeq.{u}}

theorem Om_I (n : ℕ) : Om (S.I n) = S.I n := S.fix n

theorem I_isSuccLimit (n : ℕ) : Order.IsSuccLimit (S.I n) := by
  rw [← S.fix n]; exact Om_isSuccLimit (S.I_ne_zero n)

/-! ## F5, F6 -/

/-- **F5.** -/
theorem psi_lt_psi_of_mem {κ a₀ a : Ordinal.{u}} (hκ : S.InR κ) (h : a₀ < a)
    (hmem : a₀ ∈ S.CSet a (S.psi a κ)) : S.psi a₀ κ < S.psi a κ :=
  lt_psi_of_mem hκ (CSet.psi_mem h hκ (mem_CSet_psi hκ a) hmem) (psi_lt hκ a₀)

/-- **F6.** `ψ_κ(a)` is strongly critical. -/
theorem SC_psi {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) : SC (S.psi a κ) := by
  have hSC := hκ.SC S
  refine ⟨lt_psi_of_mem hκ (CSet.zero_mem a _) hSC.1, fun x hx y hy => ?_⟩
  have hxκ := hx.trans (psi_lt hκ a)
  have hyκ := hy.trans (psi_lt hκ a)
  exact lt_psi_of_mem hκ (CSet.phi_mem (CSet.of_lt hx) (CSet.of_lt hy)) (hSC.2 x hxκ y hyκ)

/-! ## F7, F8 -/

/-- **F7.** `Ω_σ ∈ Cl(a, b)` ⟹ `σ ∈ Cl(a, b)`. -/
theorem mem_of_Om_mem {a b σ : Ordinal.{u}} (h : Om σ ∈ S.CSet a b) : σ ∈ S.CSet a b := by
  by_cases hσ0 : σ = 0
  · rw [hσ0]; exact CSet.zero_mem a b
  suffices H : ∀ x ∈ S.CSet a b, x = Om σ → σ ∈ S.CSet a b from H _ h rfl
  intro x hx
  induction hx with
  | @small x hxb =>
    intro e
    exact CSet.of_lt (lt_of_le_of_lt (le_Om σ) (e ▸ hxb))
  | zero =>
    intro e
    exact absurd e.symm (Om_pos hσ0).ne'
  | inacc n =>
    intro e
    rw [← Om_I n, Om_inj] at e
    rw [← e]; exact CSet.I_mem a b n
  | inaccW =>
    intro e
    rw [← S.Om_Iw, Om_inj] at e
    rw [← e]; exact CSet.Iw_mem a b
  | @add x y hx hy ihx ihy =>
    intro e
    by_cases hy0 : y = 0
    · rw [hy0, add_zero] at e; exact ihx e
    · have hxlt : x < Om σ := by
        by_contra hxge
        have : x < x + y := lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)
        exact absurd e (lt_of_le_of_lt (not_lt.1 hxge) this).ne'
      rcases lt_or_ge y (Om σ) with hylt | hyge
      · have hp : Ordinal.IsPrincipal (· + ·) (Om σ) := by
          rw [Om_eq_ord hσ0]; exact isPrincipal_add_ord (aleph0_le_aleph σ)
        exact absurd e (hp hxlt hylt).ne
      · exact ihy (le_antisymm (e ▸ (le_add_left (le_refl y) : y ≤ x + y)) hyge)
  | @phi x y hx hy ihx ihy =>
    intro e
    rcases (SC_Om hσ0).eq_of_veblen_eq e with h' | h'
    · exact ihx h'
    · exact ihy h'
  | @om x hx ihx =>
    intro e
    rw [Om_inj] at e
    rw [← e]; exact hx
  | @coll π e hπ hπC heC _ _ =>
    intro ex
    by_cases hfix : Om σ = σ
    · rw [← hfix, ← ex]; exact Clos.coll hπ hπC heC
    · -- `σ < Ω_σ = ψ_π(e) =: γ`, so `Ω_σ ∈ Cl(e, γ) ∩ π ⊆ γ`
      exfalso
      have hσlt : σ < S.psi e.1 π := by
        rw [(show S.psi e.1 π = Om σ from ex)]
        exact lt_of_le_of_ne (le_Om σ) (Ne.symm hfix)
      have hmem : Om σ ∈ S.CSet e.1 (S.psi e.1 π) := CSet.Om_mem (CSet.of_lt hσlt)
      have hlt : Om σ < π := by
        rw [← (show S.psi e.1 π = Om σ from ex)]; exact psi_lt hπ e.1
      have := lt_psi_of_mem hπ hmem hlt
      rw [show S.psi e.1 π = Om σ from ex] at this
      exact lt_irrefl _ this

/-- **F8.** `s + 1 ∈ Cl(a, b)` ⟹ `s ∈ Cl(a, b)`. -/
theorem mem_of_add_one_mem {a b s : Ordinal.{u}} (h : s + 1 ∈ S.CSet a b) : s ∈ S.CSet a b := by
  suffices H : ∀ x ∈ S.CSet a b, ∀ s, x = s + 1 → s ∈ S.CSet a b from H _ h s rfl
  intro x hx
  induction hx with
  | @small x hxb =>
    intro s e
    have : s < x := by rw [e, ← Order.succ_eq_add_one]; exact Order.lt_succ s
    exact CSet.of_lt (this.trans hxb)
  | zero =>
    intro s e
    exact absurd e.symm (Ordinal.add_one_ne_zero s)
  | inacc n =>
    intro s e
    rw [← Om_I n] at e
    exact absurd e (Om_ne_add_one _ s)
  | inaccW =>
    intro s e
    rw [← S.Om_Iw] at e
    exact absurd e (Om_ne_add_one _ s)
  | @add x y hx hy ihx ihy =>
    intro s e
    by_cases hy0 : y = 0
    · rw [hy0, add_zero] at e; exact ihx s e
    · obtain ⟨t, rfl, rfl⟩ := add_eq_add_one e.symm.symm hy0
      exact CSet.add_mem hx (ihy t rfl)
  | @phi x y hx hy _ _ =>
    intro s e
    rw [veblen_eq_add_one e.symm.symm]; exact CSet.zero_mem a b
  | @om x hx _ =>
    intro s e
    exact absurd e (Om_ne_add_one x s)
  | @coll π e hπ _ _ _ _ =>
    intro s ex
    exact absurd ex ((SC_psi hπ e.1).ne_add_one s)

/-! ## F9, F10 -/

theorem InR_Om_succ (s : Ordinal.{u}) : S.InR (Om (s + 1)) := Or.inr ⟨s, rfl⟩

theorem InR_I (n : ℕ) : S.InR (S.I n) := Or.inl ⟨n, rfl⟩

/-- **F9.** `Ω_s < ψ_{Ω_{s+1}}(a) < Ω_{s+1}`. -/
theorem psiS_bounds (a s : Ordinal.{u}) :
    Om s < S.psi a (Om (s + 1)) ∧ S.psi a (Om (s + 1)) < Om (s + 1) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  refine ⟨?_, psi_lt hκ a⟩
  have h1 : s ∈ S.CSet a (S.psi a (Om (s + 1))) :=
    mem_of_add_one_mem (mem_of_Om_mem (mem_CSet_psi hκ a))
  have h2 : Om s < Om (s + 1) := Om_lt_Om.2 (by
    rw [← Order.succ_eq_add_one]; exact Order.lt_succ s)
  exact lt_psi_of_mem hκ (CSet.Om_mem h1) h2

theorem lt_psiS (a s : Ordinal.{u}) : s < S.psi a (Om (s + 1)) :=
  lt_of_le_of_lt (le_Om s) (psiS_bounds a s).1

/-- **F10.** `ψ_{I_n}(a)` is a fixed point of `Ω`. -/
theorem Om_psiI (a : Ordinal.{u}) (n : ℕ) : Om (S.psi a (S.I n)) = S.psi a (S.I n) := by
  set γ := S.psi a (S.I n) with hγ
  have hκ : S.InR (S.I n) := InR_I n
  have hγI : γ < S.I n := psi_lt hκ a
  by_contra hne
  have hlt : γ < Om γ := lt_of_le_of_ne (le_Om γ) (Ne.symm hne)
  -- the least `τ` with `γ < Ω_τ`
  have hT : {τ : Ordinal.{u} | γ < Om τ}.Nonempty := ⟨γ, hlt⟩
  set τ := sInf {τ : Ordinal.{u} | γ < Om τ} with hτ
  have hτmem : γ < Om τ := csInf_mem hT
  have hbelow : ∀ τ' < τ, Om τ' ≤ γ := fun τ' h' => by
    have := notMem_of_lt_csInf' (s := {τ : Ordinal.{u} | γ < Om τ}) h'
    exact not_lt.1 this
  rcases zero_or_succ_or_isSuccLimit τ with h0 | ⟨σ, hσ⟩ | hl
  · rw [h0, Om_zero] at hτmem
    exact absurd hτmem (not_lt.2 (zero_le))
  · -- `τ = σ + 1`, `Ω_σ ≤ γ < Ω_{σ+1}`
    have hσlt : σ < τ := by rw [← hσ]; exact Order.lt_succ σ
    have hOσ : Om σ ≤ γ := hbelow σ hσlt
    have hσI : σ < S.I n := by
      rw [← Om_I n] at hγI
      exact Om_lt_Om.1 (lt_of_le_of_lt hOσ hγI)
    have hσ1I : Om (σ + 1) < S.I n := by
      conv_rhs => rw [← Om_I n]
      rw [Om_lt_Om, ← Order.succ_eq_add_one]
      exact (I_isSuccLimit n).succ_lt hσI
    have hnot : σ ∉ S.CSet a γ := by
      intro hmem
      have := lt_psi_of_mem hκ (CSet.Om_mem (CSet.succ_mem hmem)) hσ1I
      rw [← hγ, ← Order.succ_eq_add_one, hσ] at this
      exact lt_asymm this hτmem
    have hγσ : γ ≤ σ := not_lt.1 (fun h => hnot (CSet.of_lt h))
    have heq : σ = γ := le_antisymm ((le_Om σ).trans hOσ) hγσ
    have : Om γ ≤ γ := heq ▸ hOσ
    exact absurd hlt (not_lt.2 this)
  · -- `τ` limit: `Ω_τ = sup_{τ'<τ} Ω_τ' ≤ γ`
    have hτ0 : τ ≠ 0 := hl.ne_bot
    have h1 : (1 : Ordinal.{u}) < τ := by
      have := hl.succ_lt (pos_iff_ne_zero.2 hτ0)
      rwa [Order.succ_eq_add_one, zero_add] at this
    have : Om τ ≤ γ := by
      rw [Om_of_ne_zero hτ0, isNormal_omega.le_iff_forall_le hl]
      intro τ' hτ'
      by_cases h0' : τ' = 0
      · rw [h0', omega_zero]
        have h2 := hbelow 1 h1
        rw [Om_of_ne_zero one_ne_zero] at h2
        exact le_trans (omega0_le_omega 1) h2
      · rw [← Om_of_ne_zero h0']; exact hbelow τ' hτ'
    exact absurd hτmem (not_lt.2 this)

/-- **F10.** `I_m < ψ_{I_{m+1}}(a)`. -/
theorem I_lt_psiI (a : Ordinal.{u}) (m : ℕ) : S.I m < S.psi a (S.I (m + 1)) :=
  lt_psi_of_mem (InR_I (m + 1)) (CSet.I_mem a _ m) (S.strictMono (Nat.lt_succ_self m))

/-- **F10.** `Ω_1 < ψ_{I_n}(a)`. -/
theorem Om_one_lt_psiI (a : Ordinal.{u}) (n : ℕ) : Om 1 < S.psi a (S.I n) := by
  refine lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.one_mem a _)) ?_
  rw [← Om_I n, Om_lt_Om]
  have h := (S.uncountable n)
  by_contra hle
  have h1 : S.I n ≤ 1 := not_lt.1 hle
  have : (S.I n).card ≤ 1 := by
    have := Ordinal.card_le_card h1
    rwa [card_one] at this
  exact absurd (lt_of_lt_of_le h this) (not_lt.2 (one_le_aleph0))

/-! ## F11, F12 -/

/-- `κ ∈ Cl(ξ, ψ_κ(a))` for every `ξ`. -/
theorem mem_CSet_psi_any {κ : Ordinal.{u}} (hκ : S.InR κ) (ξ a : Ordinal.{u}) :
    κ ∈ S.CSet ξ (S.psi a κ) := by
  rcases hκ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact CSet.I_mem ξ _ n
  · exact CSet.Om_mem (CSet.succ_mem (CSet.of_lt (lt_psiS a s)))

/-- **F11.** -/
theorem psi_mono {κ ξ a : Ordinal.{u}} (hκ : S.InR κ) (h : ξ ≤ a) :
    S.psi ξ κ ≤ S.psi a κ ∧ S.CSet ξ (S.psi ξ κ) ⊆ S.CSet a (S.psi a κ) := by
  have hle : S.psi ξ κ ≤ S.psi a κ :=
    psi_le_of_good (mem_CSet_psi_any hκ ξ a) fun x hx hxκ =>
      lt_psi_of_mem hκ (CSet_mono h le_rfl hx) hxκ
  exact ⟨hle, CSet_mono h hle⟩

/-- **F12.** At an argument in its own closure, `ψ_κ` is strictly increasing. -/
theorem psi_lt_psi {κ a₀ a : Ordinal.{u}} (hκ : S.InR κ) (h : a₀ < a)
    (hnf : a₀ ∈ S.CSet a₀ (S.psi a₀ κ)) : S.psi a₀ κ < S.psi a κ :=
  psi_lt_psi_of_mem hκ h ((psi_mono hκ h.le).2 hnf)

end InaccSeq

end Googology.Notation.InaccPsi
