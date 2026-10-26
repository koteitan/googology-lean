import Googology.Trans.PoR.InaccPsi.R2.VcSub

/-!
# `ϑ`-nodes at levels `Ω₁·M < B₂` with parameter leaves

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B₂ = Uc.ucB`, `π = pi σ τ`, `vcSub`, `VcLv` of `R2.VcSub`; `α = Dl τ n = ϑᵗ(Δₙ)`, `α⁺ = Dp τ n`.  A level
`Γ = Ω₁·M` (`1 ≤ M`, `Γ < B₂`) is now allowed to carry **parameter leaves** (countable leaves of its canonical
decomposition that move under base changes): its membership, its base change and the choice between the two
translations of [W07a] Def 6.2 are all decided by the leaves.

* `vc_dat_P` (**the data is a leaf up to finite ones**: a predicate holding at every leaf and at every finite ordinal
  holds at `ucDat z`), `vc_dat_TB` (`ucDat z ∈ Tᵗ` when every leaf is);
* `vc_arg_mem` (**`Ω₁·M + η ∈ Tᵗ` from the leaves of `M`**, `R2.ucArg_mem`), `vc_level_lt` (**`ucDat M`, `η` and
  every leaf of `M` lie below `ϑᵗ(Ω₁·M + η)`**, `R2.ucLevel_lt`, `R2.vt_E_iff`);
* `vc_node_pi` (**the base change of a node: `π(ϑᵗ(Γ + ρ)) = ϑ^σ(vcSub π Γ + π ρ)`** for a level `Γ < B₂` whose
  leaves lie in `Tᵗ[σ]` and `ρ ∈ Tᵗ[σ] ∩ Ω₁`; `R2.pi_vt_two`, `R2.pi_add`, `Vc.vc_pi`);
* `vc_node_trL`, `vc_node_trH` (**the two translations decided by the leaves**: every leaf of `Γ`
  below `α` ⇒ the subcase `Γ^* < α` of `R2.uvVt_trL` (`ρ ↦ α + ρ`); some leaf `≥ α` ⇒ the subcase `Γ^* ≥ α` of
  `R2.uvVt_trH` (`ρ` kept)), `vc_uvIns` (the offset inserted by `R2.uvVt_tr` read off the leaves), `vc_uyLev_iff`
  (**`Uy.UyLev κ M` ⇔ every leaf of `Ω₁·M` below `κ`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh

/-- `ucFold f γ` is `0` or the value of `f` at a component of `γ`. -/
theorem vc_fold_mem (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, ucFold f γ = 0 ∨ ∃ x ∈ ucComps γ, ucFold f γ = f x := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < OmTwo
  · exact Or.inr ⟨γ, by rw [ucComps_small h1]; exact mem_singleton _, ucFold_small f h1⟩
  by_cases h2 : γ < ucE
  · have h1' := not_lt.1 h1
    have hc := ucComps_big h1' h2
    rw [ucFold_big f h1' h2]
    rcases max_choice (ucFold f (log OmTwo γ))
        (max (f (γ / OmTwo ^ log OmTwo γ)) (ucFold f (γ % OmTwo ^ log OmTwo γ))) with e | e <;> rw [e]
    · rcases IH _ (uc_log_lt h1' h2) with h0 | ⟨x, hx, hxe⟩
      · exact Or.inl h0
      · exact Or.inr ⟨x, by rw [hc]; exact Or.inl hx, hxe⟩
    · rcases max_choice (f (γ / OmTwo ^ log OmTwo γ)) (ucFold f (γ % OmTwo ^ log OmTwo γ)) with e' | e' <;>
        rw [e']
      · exact Or.inr ⟨_, by rw [hc]; exact Or.inr (Or.inl rfl), rfl⟩
      · rcases IH _ (uc_mod_lt h1') with h0 | ⟨x, hx, hxe⟩
        · exact Or.inl h0
        · exact Or.inr ⟨x, by rw [hc]; exact Or.inr (Or.inr hx), hxe⟩
  · exact Or.inl (ucFold_out f (not_lt.1 h2))

/-- **The data is a leaf up to finite ones**: if `P` holds at every finite ordinal and at every leaf of a code
`z < B₂`, then `P (ucDat z)`. -/
theorem vc_dat_P {P : Ordinal.{0} → Prop} (hfin : ∀ n : ℕ, P n) :
    ∀ z, z < ucB → VcLv P z → P (ucDat z) := by
  have h0 : P 0 := by simpa using hfin 0
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB hL
  rcases lt_or_ge z Om1 with hz | hz
  · rw [ucDat_small hz]; exact (VcLv_small P hz).1 hL
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, ucDat_Om1]; exact h0
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · rw [VcLv_phi P h1 hB hE hI] at hL
      have hcz := Tf.tf_inv2_lt hE
      rw [Uy.uy_dat_phi h1 hB hE hI]
      rcases max_choice (ucDat (invVeblen₁ z)) (ucDat (invVeblen₂ z)) with e | e <;> rw [e]
      · exact IH _ hI (hI.trans hB) hL.1
      · exact IH _ hcz (hcz.trans hB) hL.2
    have hplt := vc_parts_lt h1 hB hI
    rw [VcLv_atom P h1 hB hE hI] at hL
    have hpart : ∀ x ∈ ucParts z, P (ucDat x) := fun x hx =>
      IH x (hplt x hx) ((hplt x hx).trans hB) (hL x hx (hplt x hx))
    have hSC : SC z := tl_SC_of h1 hI
    by_cases hX : z < tlX
    · rw [ucDat_lt_X hX]
      have hparts : ucParts z = {tlLev z, tlI (tlLev z) z} := by rw [ucParts, if_pos hX]
      by_cases hl0 : tlLev z = 0
      · rw [tlDat_atom0 h1 hX hE hI hl0]
        set ν := Tf.tfIdx z with hνdef
        have hνP : ν ∈ ucParts z := by rw [hparts, hl0, tlI_zero]; exact mem_insert_of_mem _ rfl
        have hνz : ν < z := hplt ν hνP
        have hgz : gamma ν = z := Tf.tf_SC_gamma h1 hI
        have hν1 : Om1 < ν := Tf.tf_Om1_lt_gamma.1 (by rw [hgz]; exact h1)
        have hdX : ν - (Om1 + 1) < tlX := ((Ordinal.sub_le_self _ _).trans_lt hνz).trans hX
        rw [← ucDat_lt_X hdX, ← Ordinal.sub_sub]
        have hPν := hpart ν hνP
        rw [← vc_dat_sub hν1.le (hνz.trans hB)] at hPν
        set c := ν - Om1 with hcdef
        have hc0 : c ≠ 0 := by
          intro e
          have : Om1 + c = ν := Ordinal.add_sub_cancel_of_le hν1.le
          rw [e, add_zero] at this; exact absurd this hν1.ne
        rcases lt_or_ge c ω with hcω | hcω
        · have hd : c - 1 < ω := (Ordinal.sub_le_self _ _).trans_lt hcω
          obtain ⟨m, hm⟩ := Ordinal.lt_omega0.1 hd
          rw [ucDat_small (hd.trans (omega0_lt_inE Rj.rj_Om1_inE)), hm]; exact hfin m
        · have h1c : 1 + (c - 1) = c := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hc0)
          have hdω : ω ≤ c - 1 := by
            by_contra hlt
            push Not at hlt
            have : 1 + (c - 1) < ω := isPrincipal_add_omega0 one_lt_omega0 hlt
            rw [h1c] at this; exact absurd hcω (not_le.2 this)
          rw [Ordinal.one_add_of_omega0_le hdω] at h1c
          rw [h1c]; exact hPν
      · rw [tlDat_atomF h1 hX hE hI hl0]
        obtain ⟨-, hyz, hlz⟩ := tl_nf hSC h1 hX
        rw [← ucDat_lt_X (hlz.trans hX), ← ucDat_lt_X (hyz.trans hX)]
        rcases max_choice (ucDat (tlLev z)) (ucDat (tlI (tlLev z) z)) with e | e <;> rw [e]
        · exact hpart _ (by rw [hparts]; exact mem_insert _ _)
        · exact hpart _ (by rw [hparts]; exact mem_insert_of_mem _ rfl)
    · have hparts : ucParts z = ucComps (ucLev z) ∪ {ucI (ucLev z) z} := by rw [ucParts, if_neg hX]
      rw [ucDat_atom (not_lt.1 hX) hB hE hI]
      rcases max_choice (ucFold ucDat (ucLev z)) (ucDat (ucI (ucLev z) z)) with e | e <;> rw [e]
      · rcases vc_fold_mem ucDat (ucLev z) with e0 | ⟨x, hx, hxe⟩
        · rw [e0]; exact h0
        · rw [hxe]; exact hpart x (by rw [hparts]; exact mem_union_left _ hx)
      · exact hpart _ (by rw [hparts]; exact mem_union_right _ (mem_singleton _))
  · rw [VcLv_cnf P h1 hB hE] at hL
    have hlz := Tf.tf_log_lt h1 hE
    have hrz := Rj.rj_mod_lt (Rj.rj_Om1_pos.trans h1).ne'
    rw [Uy.uy_dat_cnf h1 hB hE]
    rcases max_choice (ucDat (log ω z)) (ucDat (z % ω ^ log ω z)) with e | e <;> rw [e]
    · have hL1 := hL.1
      by_cases hl : ω ^ log ω z = log ω z
      · rw [if_pos hl] at hL1; exact IH _ hlz (hlz.trans hB) hL1
      · rw [if_neg hl] at hL1
        have hbz : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hlz
        have := IH _ hbz (hbz.trans hB) hL1
        rwa [vc_dat_sub (Si.si_Om1_le_log h1.le) (hlz.trans hB)] at this
    · exact IH _ hrz (hrz.trans hB) hL.2

/-- **`ucDat z ∈ Tᵗ` when every leaf of `z` is.** -/
theorem vc_dat_T {τ z : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hB : z < ucB) (hL : VcLv (· ∈ Tset τ) z) :
    ucDat z ∈ Tset τ := by
  refine vc_dat_P (P := (· ∈ Tset τ)) (fun n => Uh.uh_T_le hτ hτ1 ?_) z hB hL
  exact ((natCast_lt_omega0 n).le.trans (omega0_lt_inE hτ).le)

/-- `Ω₁·M < B₂` and `Ω₁·M + η < Ω₂` for `M < B₂`, `η < Ω₁` (`B₂`, `Ω₂` are `ε`-numbers, so closed under `·`). -/
theorem vc_arg_lt {M η : Ordinal.{0}} (hMB : M < ucB) (hηΩ : η < Om1) :
    Om1 * M < ucB ∧ Om1 * M + η < OmTwo := by
  have hBE : ω ^ ucB = ucB := (uc_SC_facts ucB_SC).1
  have hP : IsPrincipal (· * ·) ucB := by
    have := isPrincipal_mul_omega0_opow_opow ucB
    rwa [hBE, hBE] at this
  have hΩB : Om1 < ucB := Rj.rj_Om1_lt_E.trans Uv.uv_E_lt_B
  have h1 : Om1 * M < ucB := hP hΩB hMB
  exact ⟨h1, (Lq.lq_SC_indec uc_SC_Om2).add_lt (h1.trans ucB_lt_Om2) (hηΩ.trans uc_Om1_lt_Om2)⟩

/-- **Membership of the argument from the leaves of the level**: `Ω₁ ≤ M < B₂`, every leaf of `M` in `Tᵗ`,
`η ∈ Tᵗ ∩ Ω₁` ⇒ `Ω₁·M + η ∈ Tᵗ` (`R2.ucArg_mem`). -/
theorem vc_arg_mem {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < ucB)
    (hL : VcLv (· ∈ Tset τ) M) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * M + η ∈ Tset τ :=
  ucArg_mem hτ hτ1 hM1 hMB (vc_dat_T hτ hτ1 hMB hL) hη hηΩ

/-- **`ucDat M`, `η` and every leaf of `M` lie below `ϑᵗ(Ω₁·M + η)`** for `Ω₁ ≤ M < B₂` with every leaf of `M` in
`Tᵗ` and `η ∈ Tᵗ ∩ Ω₁` (`R2.ucLevel_lt`; the value is an `ε`-number by `R2.vt_E_iff`). -/
theorem vc_level_lt {τ M η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : Om1 ≤ M) (hMB : M < ucB)
    (hL : VcLv (· ∈ Tset τ) M) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ucDat M < vt τ (Om1 * M + η) ∧ η < vt τ (Om1 * M + η) ∧ VcLv (· < vt τ (Om1 * M + η)) M := by
  obtain ⟨h1, h2⟩ := ucLevel_lt hτ hτ1 hM1 hMB (vc_dat_T hτ hτ1 hMB hL) hη hηΩ
  have hT := vc_arg_mem hτ hτ1 hM1 hMB hL hη hηΩ
  have hξ2 : Om1 * M + η < OmTwo := (vc_arg_lt hMB hηΩ).2
  have hE : InE (vt τ (Om1 * M + η)) :=
    ((vt_E_iff hτ hτ1 hT hξ2).2 ((le_mul_left Om1 (Rj.rj_Om1_pos.trans_le hM1)).trans le_self_add)).2
  exact ⟨h1, h2, (vc_dat_lt hE M hMB).2 h1⟩

/-! ## The base change of a node -/

/-- **The base change of a `ϑ`-node at a level with parameter leaves**: for bases `σ < τ`, a level `Γ < B₂` whose
leaves lie in `Tᵗ[σ]` and `ρ ∈ Tᵗ[σ] ∩ Ω₁`: `Γ + ρ, ϑᵗ(Γ + ρ) ∈ Tᵗ[σ]` and
`π(ϑᵗ(Γ + ρ)) = ϑ^σ(vcSub π Γ + π ρ)` (the leaves of the level are moved by `π`). -/
theorem vc_node_pi {σ τ Γ ρ : Ordinal.{0}} (h : Bases σ τ) (hΓB : Γ < ucB) (hL : VcLv (· ∈ TB τ σ) Γ)
    (hρ : ρ ∈ TB τ σ) (hρ1 : ρ < Om1) :
    Γ + ρ ∈ TB τ σ ∧ vt τ (Γ + ρ) ∈ TB τ σ ∧
      pi σ τ (vt τ (Γ + ρ)) = vt σ (vcSub (pi σ τ) Γ + pi σ τ ρ) := by
  obtain ⟨hΓT, hΓπ⟩ := vc_pi h Γ hΓB hL
  obtain ⟨c1, c2⟩ := pi_add h hΓT hρ
  have hξ2 : Γ + ρ < OmTwo :=
    (Lq.lq_SC_indec uc_SC_Om2).add_lt (hΓB.trans ucB_lt_Om2) (hρ1.trans uc_Om1_lt_Om2)
  obtain ⟨v1, -, -, -, v5⟩ := vt_memTwo h.2.1 h.2.2.2 c1.1 hξ2
  refine ⟨c1, ⟨v1, by rw [v5]; exact c1.2⟩, ?_⟩
  rw [pi_vt_two h c1 hξ2, c2, hΓπ]

/-! ## The two translations decided by the leaves -/

/-- **Every leaf of the level below `α = ϑᵗ(Δₙ)`**: the subcase `Γ^* < α` of [W07a] Def 6.2 (`R2.uvVt_trL`). -/
theorem vc_node_trL {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hMB : Om1 * M < ucB) (hρ1 : ρ < Om1) (hL : VcLv (· < Dl τ n) (Om1 * M)) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + (Dl τ n + ρ))) ∧
    (Om1 * M + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * M + (Dl τ n + ρ)) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * M + ρ)) :=
  uvVt_trL hτ hτ1 hn hM1 hMB ((vc_dat_lt (Dl_E hτ hτ1 hn).2.1 _ hMB).1 hL) hρ1

/-- **Some leaf of the level `≥ α = ϑᵗ(Δₙ)`**: the subcase `Γ^* ≥ α` of [W07a] Def 6.2 (`R2.uvVt_trH`). -/
theorem vc_node_trH {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 1 ≤ n) {M ρ : Ordinal.{0}}
    (hM1 : 1 ≤ M) (hMB : Om1 * M < ucB) (hρ1 : ρ < Om1) (hL : ¬ VcLv (· < Dl τ n) (Om1 * M)) :
    (Om1 * M + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * M + ρ) = vt τ (Om1 * M + ρ)) ∧
    (Om1 * M + ρ ∈ Tset τ → vt τ (Om1 * M + ρ) < Dp τ n →
      Om1 * M + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * M + ρ) = vt (Dl τ n) (Om1 * M + ρ)) :=
  uvVt_trH hτ hτ1 hn hM1 hMB
    (not_lt.1 fun hd => hL ((vc_dat_lt (Dl_E hτ hτ1 hn).2.1 _ hMB).2 hd)) hρ1

/-- **The inserted offset of `R2.uvVt_tr` is decided by the leaves**: `uvIns α Γ ρ = α + ρ` if every leaf of `Γ` is
below the `ε`-number `α`, and `= ρ` otherwise. -/
theorem vc_uvIns {α Γ ρ : Ordinal.{0}} (hα : InE α) (hΓB : Γ < ucB) :
    (VcLv (· < α) Γ → Uv.uvIns α Γ ρ = α + ρ) ∧ (¬ VcLv (· < α) Γ → Uv.uvIns α Γ ρ = ρ) :=
  ⟨fun hL => Uv.uvIns_low ((vc_dat_lt hα Γ hΓB).1 hL),
    fun hL => Uv.uvIns_high (not_lt.1 fun hd => hL ((vc_dat_lt hα Γ hΓB).2 hd))⟩

/-- **The old levels are the levels whose leaves are all below `κ`**: for an `ε`-number `κ`, `Uy.UyLev κ M` iff
`1 ≤ M`, `Ω₁·M < B₂` and every leaf of `Ω₁·M` is below `κ`. -/
theorem vc_uyLev_iff {κ M : Ordinal.{0}} (hκ : InE κ) :
    Uy.UyLev κ M ↔ 1 ≤ M ∧ Om1 * M < ucB ∧ VcLv (· < κ) (Om1 * M) := by
  rw [Uy.uyLev_iff hκ]
  exact ⟨fun h => ⟨h.1, h.2.1, (vc_dat_lt hκ _ h.2.1).2 h.2.2⟩,
    fun h => ⟨h.1, h.2.1, (vc_dat_lt hκ _ h.2.1).1 h.2.2⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Vc
