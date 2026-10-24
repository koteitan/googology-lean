import Googology.Trans.PoR.InaccPsi.R2.SpVt

/-!
# The bases of a non-`υ` point with a level-closed `σ`: the hypothesis asks `ϑ` only from `ε_{Ω₁+1}` on

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^β = vt β`, `ε_{Ω₁+1} = Gg.ggE`, `SpLC` the level-closed ordinals,
`Sm.SmVtTop S n β`: `B_n(ϑ^β(η)) = ϑ^{B_n β}(B_n η)` on `T^β ∩ [ε_{Ω₁+1}, Ω₂)`, `Si.SiUncHE S n σ τ`: `B_n` commutes
with the base change `π_{σ,τ}` on `Tᵗ[σ] ∩ [ε_{Ω₁+1}, Ω₂)`.

* `spBases` (**every non-`υ` point `x ∈ [c_n, c_{n+1})` has bases `σ < τ` with `τ = υ_ξ <₁ ∞`, `c_n ≤ τ < x`,
  `x ∈ Tᵗ[σ]` and `σ`, `τ` level-closed**: `σ` from `Sp.spLC_exists` above `max Parᵗ(x)`; this replaces the base
  `ε_{max Par(x)+1}` of `Se.seBases`, which is neither strongly critical nor level-closed);
* `SpPiHom S` (a hypothesis name): **every non-`υ` `x ∈ [c_n, c_{n+1})` has such bases with `Sm.SmVtTop` at `τ`
  and at `σ` and `Si.SiUncHE`**; `spPiHom_sm` (**`SpPiHom ⇒ Sm.SmPiHom`**: at `σ` the clause `Si.SiVtU` of
  `Sm.SmVtB` is `Sp.spVtU_all`), `spPiHom_iff` (**`SpPiHom` is exactly `Se.SePiHom2` with `c_n ≤ τ` and `σ`
  level-closed**);
* `SpVtTopAll S` (`Sm.SmVtTop` at every level-closed base below `c_{n+1}`), `SpUncAll S` (`Si.SiUncHE` at every pair
  of bases `σ < τ` with `σ` level-closed, `τ <₁ ∞`, `c_n ≤ τ < c_{n+1}`), `spPiHom_of_all` (**they give `SpPiHom`**);
* `spPiComm`, `spLhTopE`, `spLhEps` (**`SpPiHom` gives `Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps`**), `spRoadE_nu`
  (**the road `Sm.smRoadE_nu` with `SpPiHom` in place of `Sm.SmPiHom`**), `spRoadE_all` (the same with
  `SpVtTopAll` and `SpUncAll`).

No new axiom.  New definitions: the hypothesis names `SpPiHom`, `SpVtTopAll`, `SpUncAll`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-- **The bases of a non-`υ` point `x ∈ [c_n, c_{n+1})` with a level-closed `σ`**: `τ = υ_ξ` the largest `υ`-point
below `x` and `σ` a level-closed point above `max Parᵗ(x)` (`spLC_exists`); unconditionally. -/
theorem spBases {n : ℕ} {x : Ordinal.{0}} (hc : Bc.bcC S n ≤ x) (hx : x < Bc.bcC S (n + 1)) (hU : ¬ UpsPt x) :
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ Bc.bcC S n ≤ τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SpLC σ ∧ SpLC τ := by
  obtain ⟨ξ, h1, h2⟩ := Lh.lhBracket x
  have hcpos : (0 : Ordinal.{0}) < Bc.bcC S n := lt_of_le_of_lt zero_le (Rt.rtD_lt_c (S := S) n)
  obtain ⟨ι, hι0, hι⟩ := upsPt_iff_upsilon.1 (⟨hcpos, Rt.rt_c_inf n⟩ : UpsPt (Bc.bcC S n))
  have hιξ : ι ≤ ξ := Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 (by rw [← hι]; exact hc.trans_lt h2))
  have hcτ : Bc.bcC S n ≤ upsilon ξ := by rw [hι]; exact Tp.tpUps_le_iff.2 hιξ
  have hξpos : 0 < ξ := hι0.trans_le hιξ
  have hτx : upsilon ξ < x := lt_of_le_of_ne h1 fun e => hU (e ▸ upsPt_upsilon hξpos)
  have hτc : upsilon ξ < Bc.bcC S (n + 1) := hτx.trans hx
  have hτU : UpsPt (upsilon ξ) := upsPt_upsilon hξpos
  have hτE : InE (upsilon ξ) := upsPt_inE hτU
  have hx1 : x < Om1 := (Rt.rt_lt_Om1 hx).1
  have hτ1 : upsilon ξ < Om1 := hτx.trans hx1
  obtain ⟨-, hz1c, -⟩ := Sm.smPrem hcτ hτc
  have hu1 : upsilon (ξ + 1) < Om1 := (Rt.rt_lt_Om1 hz1c).1
  have hxT : x ∈ Tset (upsilon ξ) := by
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) x hx1
    rw [if_neg hξpos.ne'] at h
    exact h.2 (by rw [succ_eq_add_one]; exact h2)
  set P := Par (upsilon ξ) x with hP
  have hPsub : ↑P ⊆ Set.Iio (upsilon ξ) := Par_sub hτE hτ1 hxT
  set m := P.sup id with hm
  have hmτ : m < upsilon ξ := by
    rw [hm, Finset.sup_lt_iff (InE.pos hτE)]
    intro b hb; exact hPsub hb
  obtain ⟨σ, hσ, hmσ, hστ⟩ := spLC_exists hξpos.ne' hτc hmτ
  refine ⟨σ, upsilon ξ, ⟨gg_SC_eps hσ.1, hτE, hστ, hτ1⟩, hτU.2, hcτ, hτx, ⟨hxT, fun b hb => ?_⟩, hσ,
    spLC_ups hξpos.ne' hτc⟩
  exact (Finset.le_sup (f := id) hb).trans_lt hmσ

/-- **The commutation hypothesis with a level-closed `σ`** (a hypothesis name): every non-`υ` point
`x ∈ [c_n, c_{n+1})` has bases `σ < τ` (`τ <₁ ∞`, `c_n ≤ τ < x`, `x ∈ Tᵗ[σ]`, `σ` level-closed) with `Sm.SmVtTop` at
`τ` and at `σ` and `Si.SiUncHE`. -/
def SpPiHom (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ Bc.bcC S n ≤ τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SpLC σ ∧
      Sm.SmVtTop S n τ ∧ Sm.SmVtTop S n σ ∧ Si.SiUncHE S n σ τ

/-- **`SpPiHom` gives `Sm.SmPiHom`**: at the level-closed `σ` the clause `Si.SiVtU` of `Sm.SmVtB` is `spVtU_all`. -/
theorem spPiHom_sm (h : SpPiHom S) : Sm.SmPiHom S := by
  intro n x hc hx hU
  obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, hT, hS, hUn⟩ := h n x hc hx hU
  have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans (hτx.trans hx)
  exact ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hT, Or.inr (spVtU_all hσ hσc hS), hUn⟩

/-- **`SpPiHom` is exactly `Se.SePiHom2` with `c_n ≤ τ` and `σ` level-closed.** -/
theorem spPiHom_iff : SpPiHom S ↔
    ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
      ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ Bc.bcC S n ≤ τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SpLC σ ∧
        Se.SeVtHom S n τ ∧ Se.SeVtHom S n σ ∧ Se.SeUnc S n σ τ := by
  constructor
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, hT, hS, hUn⟩ := h n x hc hx hU
    have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
    have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
    have hτU : UpsPt τ := ⟨Si.si_inE_pos hB.2.1, hτL⟩
    have hVT := Sm.smVtU_ups hτU hcτ hτc hT
    have hVS := spVtU_all hσ hσc hS
    exact ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, Si.siVtHom_of hB.2.1 hτc hVT, Si.siVtHom_of hB.1 hσc hVS,
      Si.siUnc_ofE hB hτc (Si.siComm_allE hB hτc hVT hVS hUn) hUn⟩
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, hT, hS, hUn⟩ := h n x hc hx hU
    exact ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, fun η hη _ hη2 => hT η hη hη2, fun η hη _ hη2 => hS η hη hη2,
      fun ξ hξ hξ1 hξ2 => hUn ξ hξ (Rj.rj_Om1_lt_E.le.trans hξ1) hξ2⟩

/-- **`B_n` commutes with `ϑ^β` from `ε_{Ω₁+1}` on at every level-closed base `β < c_{n+1}`** (a hypothesis name). -/
def SpVtTopAll (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ β, SpLC β → β < Bc.bcC S (n + 1) → Sm.SmVtTop S n β

/-- **`B_n` commutes with `π_{σ,τ}` on `Tᵗ[σ] ∩ [ε_{Ω₁+1}, Ω₂)` at every pair of bases `σ < τ` with `σ`
level-closed, `τ <₁ ∞`, `c_n ≤ τ < c_{n+1}`** (a hypothesis name). -/
def SpUncAll (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ σ τ, Bases σ τ → SpLC σ → LtInf1 τ → Bc.bcC S n ≤ τ → τ < Bc.bcC S (n + 1) →
    Si.SiUncHE S n σ τ

/-- **`SpVtTopAll` and `SpUncAll` give `SpPiHom`** (the bases of `spBases`). -/
theorem spPiHom_of_all (hV : SpVtTopAll S) (hU : SpUncAll S) : SpPiHom S := by
  intro n x hc hx hUx
  obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, hτ⟩ := spBases hc hx hUx
  have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
  exact ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, hV n τ hτ hτc, hV n σ hσ (hB.2.2.1.trans hτc),
    hU n σ τ hB hσ hτL hcτ hτc⟩

/-- **`SpPiHom` gives `Rt.RtPiComm`.** -/
theorem spPiComm (h : SpPiHom S) : Rt.RtPiComm S := Sm.smPiComm (spPiHom_sm h)

/-- **`SpPiHom` gives `Rk.RkLhTopE`.** -/
theorem spLhTopE (h : SpPiHom S) : Rk.RkLhTopE S := Sm.smLhTopE (spPiHom_sm h)

/-- **`SpPiHom` gives `Tp.TpLhEps`.** -/
theorem spLhEps (h : SpPiHom S) : Tp.TpLhEps S := Sm.smLhEps (spPiHom_sm h)

/-- **The road `Sm.smRoadE_nu` with `SpPiHom` in place of `Sm.SmPiHom`.** -/
theorem spRoadE_nu (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : SpPiHom S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sm.smRoadE_nu hU hL hV hEQ hν (spPiHom_sm hpi) hT hcl

/-- **The road with `SpVtTopAll` and `SpUncAll`.** -/
theorem spRoadE_all (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hVt : SpVtTopAll S) (hUn : SpUncAll S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  spRoadE_nu hU hL hV hEQ hν (spPiHom_of_all hVt hUn) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Sp
