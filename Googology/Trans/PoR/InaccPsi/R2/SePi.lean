import Googology.Trans.PoR.InaccPsi.R2.RtPi

/-!
# `B_n` commutes with Wilken's base change `π` on every countable term, given that it commutes with `ϑ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n` (the base change of the `InaccPsi` normal forms, `L(n+1) ↦ L(ω)`), `c_n = L(n+1) = Bc.bcC S n`,
`π_{σ,τ} = pi σ τ` ([W07a] Def 5.1), `Tᵗ[σ] = TB τ σ`, `ϑᵗ = vt τ`, `σ' = B_n σ`, `τ' = B_n τ`.

[W07a] Def 5.1 defines `π_{σ,τ}` by recursion on the term: `π(ξ) = ξ` for `ξ < σ`, `π(ξ₁ + ξ₂) = π(ξ₁) + π(ξ₂)`,
`π(ϑ_k(η)) = ϑ_k(π(η))` (`k > 0`), `π(ϑᵗ(η)) = ϑᵟ(π(η))`.  `B_n` is `+`-additive and strictly increasing on
`[0, L(ω))` (`Bc.bcB_add`, `Bc.bcB_lt_iff`).  This module runs the induction on the countable terms of `Tᵗ[σ]`
(parameters `< σ`, sums, `ϑᵗ`-terms, by `R2.vt_rep`, `R2.Par_comps`, `R2.TB_sub`, `R2.pi_add`, `R2.pi_vt_two`):

* `se_wbar_ge`, `se_wbar_gt` (`ω^δ ≤ ω̄_δ`, `δ < ω̄_δ`), `seVt_gt` (**`ξ < ϑᵗ(ξ)` for `ξ ∈ Tᵗ ∩ Ω₁`**);
* `SeComm S n σ τ z` (a statement name): `B_n z ∈ T^{τ'}[σ']` and `π_{σ',τ'}(B_n z) = B_n(π_{σ,τ}(z))`;
* the three hypothesis names, which isolate what the induction cannot see (the `ψ_{Ω₁} ↔ ϑ` link):
  `SeVtT S n σ τ` (**`B_n(ϑᵗ(ξ)) = ϑ^{τ'}(B_n ξ)`** for `ξ ∈ Tᵗ[σ] ∩ Ω₂`), `SeVtS S n σ τ` (**`B_n(ϑᵟ(π ξ)) =
  ϑ^{σ'}(B_n(π ξ))`**), `SeUnc S n σ τ` (**`SeComm` at the uncountable arguments `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`**);
* `seComm_all` (**THE INDUCTION: under `SeVtT`, `SeVtS`, `SeUnc`, `SeComm` holds at every `z ∈ Tᵗ[σ] ∩ Ω₁`**), and
  `seRtComm` (`Rt.RtComm S n σ τ σ' τ' b` for every `b ≤ L(n+2)`);
* `seBases` (**for every `x ∈ [c_n, c_{n+1})` that is not a `υ`-point: `τ = υ_ξ < x < υ_{ξ+1}`, an `ε`-number
  `σ < τ` above `Parᵗ(x)`, `x ∈ Tᵗ[σ]`**, unconditionally);
* `SePiHom S` (a hypothesis name: such `σ, τ` with `SeVtT`, `SeVtS`, `SeUnc`), `sePiComm` (**`SePiHom ⇒ Rt.RtPiComm`**),
  `seLhTopE` (**`SePiHom ⇒ Rk.RkLhTopE`**), `seLhEps` (`SePiHom ⇒ Tp.TpLhEps`);
* `SeVtHom S n β` (a hypothesis name: **`B_n(ϑ^β(η)) = ϑ^{B_n β}(B_n η)` on `T^β ∩ Ω₂`**), `SePiHom2 S` (`SePiHom` with
  `SeVtHom` at `τ` and at `σ` in place of `SeVtT`, `SeVtS`), `sePiHom_of` (**`SePiHom2 ⇒ SePiHom`**), `seLhTopE2`.

No new axiom.  New definitions: the statement name `SeComm` and the hypothesis names `SeVtT`, `SeVtS`, `SeUnc`,
`SePiHom`, `SeVtHom`, `SePiHom2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Se

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-! ## `ξ < ϑᵗ(ξ)` below `Ω₁` -/

/-- `ω^δ ≤ ω̄_δ`. -/
theorem se_wbar_ge (δ : Ordinal.{0}) : ω ^ δ ≤ wbar δ := by
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  have hw : wbar δ ∈ NonEAP := enumOrd_mem nonEAP_unbounded δ
  obtain ⟨c, hc⟩ := indec_eq_opow hw.1
  have hmono := enumOrd_strictMono nonEAP_unbounded
  have hδc : δ ≤ c := by
    refine le_of_forall_lt fun d hd => ?_
    have h1 : ω ^ d < ω ^ c := by
      rw [← hc]; exact (IH d hd).trans_lt (hmono hd)
    exact (opow_lt_opow_iff_right one_lt_omega0).1 h1
  rw [hc]
  exact (opow_le_opow_iff_right one_lt_omega0).2 hδc

/-- `δ < ω̄_δ`: `ω̄` has no fixed point. -/
theorem se_wbar_gt (δ : Ordinal.{0}) : δ < wbar δ := by
  have hw : wbar δ ∈ NonEAP := enumOrd_mem nonEAP_unbounded δ
  by_contra hle
  push Not at hle
  have h1 : ω ^ δ ≤ δ := (se_wbar_ge δ).trans hle
  have hE : ω ^ δ = δ := le_antisymm h1 (right_le_opow δ one_lt_omega0)
  have he : wbar δ = δ := le_antisymm hle ((le_of_eq hE.symm).trans (se_wbar_ge δ))
  exact hw.2 (by rw [he]; exact hE)

/-- **`ξ < ϑᵗ(ξ)` for `ξ ∈ Tᵗ ∩ Ω₁`** (`τ ≤ ϑᵗ(ξ)`, and `ϑᵗ(1 + ξ) = ω̄_{τ+ξ}`, [W07a] Lemma 4.2). -/
theorem seVt_gt {τ ξ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hξ : ξ ∈ Tset τ) (hξ1 : ξ < Om1) :
    ξ < vt τ ξ := by
  rcases lt_or_ge ξ τ with hξτ | hτξ
  · exact hξτ.trans_le (vt_memTwo hτ hτ1 hξ (hξ1.trans tqc_Om1_lt_OmTwo)).2.1
  · have hω : ω ≤ ξ := (omega0_le_inE hτ).trans hτξ
    rw [← one_add_of_omega0_le hω, vt_wbar hτ hτ1 hξ1, one_add_of_omega0_le hω]
    exact (le_add_self : ξ ≤ τ + ξ).trans_lt (se_wbar_gt _)

/-! ## The commutation and its hypotheses -/

/-- **`B_n` commutes with the base changes at `z`** (a statement name): `B_n z ∈ T^{τ'}[σ']` and
`π_{σ',τ'}(B_n z) = B_n(π_{σ,τ}(z))`, `σ' = B_n σ`, `τ' = B_n τ`. -/
def SeComm (S : InaccSeq.{0}) (n : ℕ) (σ τ z : Ordinal.{0}) : Prop :=
  Bc.bcB S n z ∈ TB (Bc.bcB S n τ) (Bc.bcB S n σ) ∧
    pi (Bc.bcB S n σ) (Bc.bcB S n τ) (Bc.bcB S n z) = Bc.bcB S n (pi σ τ z)

/-- **`B_n` commutes with `ϑᵗ`** on the arguments of `Tᵗ[σ] ∩ Ω₂` (a hypothesis name). -/
def SeVtT (S : InaccSeq.{0}) (n : ℕ) (σ τ : Ordinal.{0}) : Prop :=
  ∀ ξ ∈ TB τ σ, ξ < OmTwo → Bc.bcB S n (vt τ ξ) = vt (Bc.bcB S n τ) (Bc.bcB S n ξ)

/-- **`B_n` commutes with `ϑᵟ`** on the arguments `π_{σ,τ}(ξ)`, `ξ ∈ Tᵗ[σ] ∩ Ω₂` (a hypothesis name). -/
def SeVtS (S : InaccSeq.{0}) (n : ℕ) (σ τ : Ordinal.{0}) : Prop :=
  ∀ ξ ∈ TB τ σ, ξ < OmTwo →
    Bc.bcB S n (vt σ (pi σ τ ξ)) = vt (Bc.bcB S n σ) (Bc.bcB S n (pi σ τ ξ))

/-- **`B_n` commutes with the base changes on the uncountable arguments `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`**, and `B_n ξ`,
`π_{σ,τ}(ξ)` stay below `Ω₂` (a hypothesis name). -/
def SeUnc (S : InaccSeq.{0}) (n : ℕ) (σ τ : Ordinal.{0}) : Prop :=
  ∀ ξ ∈ TB τ σ, Om1 ≤ ξ → ξ < OmTwo →
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ SeComm S n σ τ ξ

/-- `B_n` keeps `ε`-numbers below `L(ω)`. -/
theorem seB_E {n : ℕ} {e : Ordinal.{0}} (he : InE e) (heL : e < Nc.ncL S ω) : InE (Bc.bcB S n e) := by
  have h : ω ^ e < Nc.ncL S ω := by rw [show ω ^ e = e from he]; exact heL
  have := Tp.tpOpowB (S := S) (n := n) h
  rw [show ω ^ e = e from he] at this
  exact this.symm

/-- `L(n+2) < L(ω)`. -/
theorem seC_lt_L (n : ℕ) : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)

/-- **The images of the bases are bases**: `σ' = B_n σ < τ' = B_n τ`, both `ε`-numbers below `Ω₁`. -/
theorem seBases_img {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1)) :
    Bases (Bc.bcB S n σ) (Bc.bcB S n τ) := by
  have hτL : τ < Nc.ncL S ω := hτc.trans (seC_lt_L n)
  have hσL : σ < Nc.ncL S ω := hB.2.2.1.trans hτL
  exact ⟨seB_E hB.1 hσL, seB_E hB.2.1 hτL, (Bc.bcB_lt_iff hσL hτL).2 hB.2.2.1, (Rt.rt_lt_Om1 hτc).2⟩

/-- **THE INDUCTION ON THE COUNTABLE TERMS OF `Tᵗ[σ]`**: if `B_n` commutes with `ϑᵗ` and `ϑᵟ` and with the base
changes on the uncountable arguments, then `SeComm` holds at every `z ∈ Tᵗ[σ] ∩ Ω₁`.  Cases: a parameter `z < σ`
(`π`, `π'` fix it, `B_n z < σ'`); a sum (the leading component `L` and `z - L` are in `Tᵗ[σ]`, both sides are
additive); a `ϑᵗ`-term `z = ϑᵗ(ξ)` (`ξ ∈ Tᵗ[σ]` by `Parᵗ(ϑᵗ(ξ)) = Parᵗ(ξ)`; `ξ < z` when `ξ < Ω₁`). -/
theorem seComm_all {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτL : LtInf1 τ)
    (hτc : τ < Bc.bcC S (n + 1)) (hVT : SeVtT S n σ τ) (hVS : SeVtS S n σ τ) (hU : SeUnc S n σ τ) :
    ∀ z ∈ TB τ σ, z < Om1 → SeComm S n σ τ z := by
  obtain ⟨hσE, hτE, hστ, hτ1⟩ := hB
  have hB0 : Bases σ τ := ⟨hσE, hτE, hστ, hτ1⟩
  have hB' := seBases_img hB0 hτc
  have hLc : Bc.bcC S (n + 1) < Nc.ncL S ω := seC_lt_L n
  -- the countable elements of `Tᵗ` lie below `L(n+2)`, the values of `π` below `τ`
  obtain ⟨m, -, -, hmin, hmT, -⟩ := T_next (Or.inr hτE) hτ1
  have hmc : m ≤ Bc.bcC S (n + 1) := hmin _ hτc (Rt.rt_c_inf (n + 1))
  have hTL : ∀ w ∈ TB τ σ, w < Om1 → w < Nc.ncL S ω := fun w hw hw1 =>
    (((hmT w hw1).1 hw.1).trans_le hmc).trans hLc
  obtain ⟨ms, -, -, hmins, hmTs, -⟩ := T_next (Or.inr hσE) (hστ.trans hτ1)
  have hmsτ : ms ≤ τ := hmins τ hστ hτL
  have hπL : ∀ w ∈ TB τ σ, w < Om1 → pi σ τ w < Nc.ncL S ω := fun w hw hw1 => by
    have h1 : pi σ τ w < Om1 := down_lt_Om1 hB0 hw hw1
    have h2 : pi σ τ w ∈ Tset σ := (pi_bijOn hB0).1.mapsTo hw
    exact ((((hmTs _ h1).1 h2).trans_le hmsτ).trans hτc).trans hLc
  have hσL : σ < Nc.ncL S ω := (hστ.trans hτc).trans hLc
  have hτLω : τ < Nc.ncL S ω := hτc.trans hLc
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hz1
  have hzL : z < Nc.ncL S ω := hTL z hz hz1
  rcases lt_or_ge z τ with hzτ | hτz
  · -- a parameter `z < σ`
    have hzσ : z < σ := (TB_inter_lt hB0 hzτ).1 hz
    have hBz : Bc.bcB S n z < Bc.bcB S n σ := (Bc.bcB_lt_iff hzL hσL).2 hzσ
    refine ⟨mem_TB_of_lt hB' hBz, ?_⟩
    rw [pi_lt hB' hBz, pi_lt hB0 hzσ]
  by_cases hI : Indec z
  · -- a `ϑᵗ`-term
    obtain ⟨ξ, hξT, hξ2, hvz⟩ := vt_rep hτE hτ1 hz.1 hτz hz1 hI
    have hvm := vt_memTwo hτE hτ1 hξT hξ2
    have hξTB : ξ ∈ TB τ σ := ⟨hξT, by rw [← hvm.2.2.2.2, hvz]; exact hz.2⟩
    -- the commutation at the argument `ξ`
    have hξc : Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ SeComm S n σ τ ξ := by
      rcases lt_or_ge ξ Om1 with hξ1 | hξ1
      · have hξz : ξ < z := by rw [← hvz]; exact seVt_gt hτE hτ1 hξT hξ1
        refine ⟨?_, (down_lt_Om1 hB0 hξTB hξ1).trans tqc_Om1_lt_OmTwo, IH ξ hξz hξTB hξ1⟩
        exact (Rt.rt_lt_Om1 (lt_of_lt_of_le ((hmT ξ hξ1).1 hξT) hmc)).2.trans tqc_Om1_lt_OmTwo
      · exact hU ξ hξTB hξ1 hξ2
    obtain ⟨hBξ2, hπξ2, hξTB', hξπ⟩ := hξc
    have hBz : Bc.bcB S n z = vt (Bc.bcB S n τ) (Bc.bcB S n ξ) := by rw [← hvz]; exact hVT ξ hξTB hξ2
    have hvm' := vt_memTwo hB'.2.1 hB'.2.2.2 hξTB'.1 hBξ2
    refine ⟨⟨by rw [hBz]; exact hvm'.1, by rw [hBz, hvm'.2.2.2.2]; exact hξTB'.2⟩, ?_⟩
    rw [hBz, pi_vt_two hB' hξTB' hBξ2, hξπ, ← hvz, pi_vt_two hB0 hξTB hξ2]
    exact (hVS ξ hξTB hξ2).symm
  · -- a sum: the leading component and the rest
    have hz0 : z ≠ 0 := (lt_of_lt_of_le (InE.pos hτE) hτz).ne'
    obtain ⟨L, hLc', hLz, hLzz⟩ := exists_comp_absorb hz0 hI
    have hLTB : L ∈ TB τ σ := by
      have hPc := Par_comps hτE hτ1 hz.1 hτz hz1 hLc'
      rcases lt_or_ge L τ with hLτ | hτL'
      · have hLσ : L < σ := hz.2 (hPc.1 hLτ)
        exact mem_TB_of_lt hB0 hLσ
      · obtain ⟨hLT, hLP⟩ := hPc.2 hτL'
        exact ⟨hLT, fun q hq => hz.2 (hLP hq)⟩
    obtain ⟨hqTB, hπq⟩ := TB_sub hB0 hLTB hz hLz.le hz1
    set q := z - L with hqdef
    have hzLq : L + q = z := Ordinal.add_sub_cancel_of_le hLz.le
    have hqz : q < z := by
      refine lt_of_le_of_ne (sub_le_self _ _) fun e => hLzz ?_
      conv_rhs => rw [← hzLq]
      rw [e]
    have hL1 : L < Om1 := hLz.trans hz1
    have hq1 : q < Om1 := hqz.trans hz1
    obtain ⟨hLTB', hLπ⟩ := IH L hLz hLTB hL1
    obtain ⟨hqTB', hqπ⟩ := IH q hqz hqTB hq1
    have hBz : Bc.bcB S n z = Bc.bcB S n L + Bc.bcB S n q := by
      rw [← hzLq]; exact Bc.bcB_add (hTL L hLTB hL1) (hTL q hqTB hq1)
    obtain ⟨hsumTB, hsumπ⟩ := pi_add hB' hLTB' hqTB'
    refine ⟨by rw [hBz]; exact hsumTB, ?_⟩
    rw [hBz, hsumπ, hLπ, hqπ, ← Bc.bcB_add (hπL L hLTB hL1) (hπL q hqTB hq1), ← hzLq,
      (pi_add hB0 hLTB hqTB).2]

/-- **`Rt.RtComm` from the induction**, on every window `[τ, b)` with `b ≤ L(n+2)`. -/
theorem seRtComm {n : ℕ} {σ τ b : Ordinal.{0}} (hB : Bases σ τ) (hτL : LtInf1 τ)
    (hτc : τ < Bc.bcC S (n + 1)) (hb : b ≤ Bc.bcC S (n + 1)) (hVT : SeVtT S n σ τ) (hVS : SeVtS S n σ τ)
    (hU : SeUnc S n σ τ) : Rt.RtComm S n σ τ (Bc.bcB S n σ) (Bc.bcB S n τ) b := fun z hz _ hzb =>
  seComm_all hB hτL hτc hVT hVS hU z hz (Rt.rt_lt_Om1 (hzb.trans_le hb)).1

/-! ## The bases of a point, and the hypothesis -/

/-- **The bases of a non-`υ` point `x ∈ [c_n, c_{n+1})`**: `τ = υ_ξ` (the largest `υ`-point below `x`) has
`τ <₁ ∞`, `τ < x`, and an `ε`-number `σ = ε_{max Parᵗ(x) + 1} < τ` has `x ∈ Tᵗ[σ]`; unconditionally. -/
theorem seBases {n : ℕ} {x : Ordinal.{0}} (hc : Bc.bcC S n ≤ x) (hx : x < Bc.bcC S (n + 1))
    (hU : ¬ UpsPt x) : ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ τ < x ∧ x ∈ TB τ σ := by
  obtain ⟨ξ, h1, h2⟩ := Lh.lhBracket x
  have hcpos : (0 : Ordinal.{0}) < Bc.bcC S n := lt_of_le_of_lt zero_le (Rt.rtD_lt_c (S := S) n)
  -- `ξ ≠ 0`: `c_n = υ_ι ≤ x < υ_{ξ+1}` with `ι > 0`
  obtain ⟨ι, hι0, hι⟩ := upsPt_iff_upsilon.1 (⟨hcpos, Rt.rt_c_inf n⟩ : UpsPt (Bc.bcC S n))
  have hιξ : ι < ξ + 1 := Tp.tpUps_lt_iff.1 (by rw [← hι]; exact hc.trans_lt h2)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_add] at hιξ
    exact hι0.ne' (Order.lt_one_iff.1 hιξ)
  have hξpos : 0 < ξ := pos_iff_ne_zero.2 hξ0
  have hτx : upsilon ξ < x := lt_of_le_of_ne h1 fun e => hU (e ▸ upsPt_upsilon hξpos)
  have hx1 : x < Om1 := (Rt.rt_lt_Om1 hx).1
  -- `υ_{ξ+1} ≤ c_{n+1}`
  obtain ⟨ι', hι'0, hι'⟩ :=
    upsPt_iff_upsilon.1 (⟨hcpos.trans (Cx.cxC_lt n), Rt.rt_c_inf (n + 1)⟩ : UpsPt (Bc.bcC S (n + 1)))
  have hξι' : ξ < ι' := by
    have : upsilon ξ < upsilon ι' := by rw [← hι']; exact hτx.trans hx
    exact Tp.tpUps_lt_iff.1 this
  have hu1le : upsilon (ξ + 1) ≤ Bc.bcC S (n + 1) := by
    rw [hι']; exact Tp.tpUps_le_iff.2 (Order.add_one_le_of_lt hξι')
  have hcO : Bc.bcC S (n + 1) < Om1 := by
    rw [Br.Om1_eq]
    exact (Bc.bcC_lt S (n + 1)).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hu1 : upsilon (ξ + 1) < Om1 := hu1le.trans_lt hcO
  have hxT : x ∈ Tset (upsilon ξ) := by
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) x hx1
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact h2)
  have hτU : UpsPt (upsilon ξ) := upsPt_upsilon hξpos
  have hτE : InE (upsilon ξ) := upsPt_inE hτU
  have hτ1 : upsilon ξ < Om1 := hτx.trans hx1
  -- `τ` is strongly critical
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by
    rw [← Lw.lw_L_eq S]; exact ((hτx.trans hx).trans (seC_lt_L n))
  have hτSC : SC (upsilon ξ) := Mv.mvUps_SC hξ0 hτL0
  -- `σ = ε_{m+1}`, `m = max Parᵗ(x)`
  set P := Par (upsilon ξ) x with hP
  have hPsub : ↑P ⊆ Set.Iio (upsilon ξ) := Par_sub hτE hτ1 hxT
  set m := P.sup id with hm
  have hmτ : m < upsilon ξ := by
    rw [hm, Finset.sup_lt_iff (InE.pos hτE)]
    intro b hb; exact hPsub hb
  have hm1 : m + 1 < upsilon ξ := hτSC.add_one_lt hmτ
  have h1τ : (1 : Ordinal.{0}) < upsilon ξ := one_lt_omega0.trans (omega0_lt_inE hτE)
  refine ⟨veblen 1 (m + 1), upsilon ξ, ⟨?_, hτE, ?_, hτ1⟩, hτU.2, hτx, hxT, fun b hb => ?_⟩
  · show ω ^ veblen 1 (m + 1) = veblen 1 (m + 1)
    rw [← veblen_zero_apply]; exact veblen_veblen_of_lt zero_lt_one _
  · calc veblen 1 (m + 1) < veblen 1 (upsilon ξ) := veblen_lt_veblen_iff_right.2 hm1
      _ = upsilon ξ := hτSC.veblen_right h1τ
  · have hbm : b ≤ m := Finset.le_sup (f := id) hb
    exact (hbm.trans_lt (lt_add_one m)).trans_le (right_le_veblen 1 (m + 1))

/-- **`B_n` commutes with `ϑ` at the bases of every non-`υ` point** (a hypothesis name): every `x ∈ [c_n, c_{n+1})`
that is not a `υ`-point has bases `σ < τ` as in `seBases` with `SeVtT`, `SeVtS` and `SeUnc`. -/
def SePiHom (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SeVtT S n σ τ ∧ SeVtS S n σ τ ∧ SeUnc S n σ τ

/-- **`SePiHom` gives `Rt.RtPiComm`** (`σ' = B_n σ`, `τ' = B_n τ`, `b = L(n+2)`). -/
theorem sePiComm (h : SePiHom S) : Rt.RtPiComm S := by
  intro n x hc hx hU
  obtain ⟨σ, τ, hB, hτL, hτx, hxT, hVT, hVS, hUn⟩ := h n x hc hx hU
  have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
  have hLc : Bc.bcC S (n + 1) < Nc.ncL S ω := seC_lt_L n
  refine ⟨σ, τ, Bc.bcB S n σ, Bc.bcB S n τ, Bc.bcC S (n + 1), hB, hτL, hτx, hx, Rt.rt_c_inf (n + 1), hxT,
    seBases_img hB hτc, (Bc.bcB_lt_iff (hτc.trans hLc) (hx.trans hLc)).2 hτx,
    seRtComm hB hτL hτc le_rfl hVT hVS hUn⟩

/-- **`SePiHom` gives `Rk.RkLhTopE`.** -/
theorem seLhTopE (h : SePiHom S) : Rk.RkLhTopE S := Rt.rtLhTopE (sePiComm h)

/-- **`SePiHom` gives `Tp.TpLhEps`** (the lh move at every non-`υ` point below `c_{n+1}`). -/
theorem seLhEps (h : SePiHom S) : Tp.TpLhEps S := Rt.rtLhEps (sePiComm h)

/-! ## One commutation statement per base -/

/-- **`B_n` commutes with `ϑ^β` on `T^β ∩ Ω₂`** (a hypothesis name, one base `β`). -/
def SeVtHom (S : InaccSeq.{0}) (n : ℕ) (β : Ordinal.{0}) : Prop :=
  ∀ η ∈ Tset β, η < OmTwo → Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η)

/-- `SeVtHom` at `τ` gives `SeVtT`. -/
theorem seVtT_of {n : ℕ} {σ τ : Ordinal.{0}} (h : SeVtHom S n τ) : SeVtT S n σ τ :=
  fun ξ hξ hξ2 => h ξ hξ.1 hξ2

/-- `SeVtHom` at `σ` and `SeUnc` give `SeVtS` (`π_{σ,τ}(ξ) ∈ Tᵟ`, below `Ω₂`). -/
theorem seVtS_of {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (h : SeVtHom S n σ) (hU : SeUnc S n σ τ) :
    SeVtS S n σ τ := fun ξ hξ hξ2 => by
  refine h _ ((pi_bijOn hB).1.mapsTo hξ) ?_
  rcases lt_or_ge ξ Om1 with hξ1 | hξ1
  · exact (down_lt_Om1 hB hξ hξ1).trans tqc_Om1_lt_OmTwo
  · exact (hU ξ hξ hξ1 hξ2).2.1

/-- **The hypothesis with one commutation statement per base** (a hypothesis name): every non-`υ` point
`x ∈ [c_n, c_{n+1})` has bases `σ < τ` as in `seBases` such that `B_n` commutes with `ϑᵗ` and `ϑᵟ` on `T ∩ Ω₂` and
with the base changes on `Tᵗ[σ] ∩ [Ω₁, Ω₂)`. -/
def SePiHom2 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SeVtHom S n τ ∧ SeVtHom S n σ ∧ SeUnc S n σ τ

/-- **`SePiHom2` gives `SePiHom`.** -/
theorem sePiHom_of (h : SePiHom2 S) : SePiHom S := fun n x hc hx hU => by
  obtain ⟨σ, τ, hB, hτL, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
  exact ⟨σ, τ, hB, hτL, hτx, hxT, seVtT_of hT, seVtS_of hB hS hUn, hUn⟩

/-- **`SePiHom2` gives `Rk.RkLhTopE`.** -/
theorem seLhTopE2 (h : SePiHom2 S) : Rk.RkLhTopE S := seLhTopE (sePiHom_of h)

end Googology.Trans.PoR.InaccPsi.R2.Se
