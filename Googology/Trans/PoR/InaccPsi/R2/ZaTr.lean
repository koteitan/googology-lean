import Googology.Trans.PoR.InaccPsi.R2.ZaUp

/-!
# The translations of [W07a] Def 6.2 at a moving level `B₂ ≤ q`, the subcase read off the leaves of `Ω₁·q`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`α = Dl τ n = ϑᵗ(Δₙ)`, `α⁺ = Dp τ n`, `θ = ConjT.th S`, `B₂ = Uc.ucB`, `d_S = Vd.vdD S 0`.  `Yv.yv_node_tr` gives both
translations at a level `Ω₁·M`, `B₂ ≤ M < θ`, with the subcase decided by the leaves of `M`, when `α` is strongly
critical.  The data are read only at strongly critical points (◇R of `R2.CitedVd`); `α = ϑᵗ(Δₙ)` is strongly critical
for `n ≥ 2` by the argument written in the non-vacuity paragraph of `R2.CitedXo` (`Δₙ ≥ ε_{Ω₁+1}`), but `Dl` is a
constant without definition, so this is no Lean theorem.  It is the statement **`ZaDlSC`** below, carried as a
hypothesis.

* `ZaDlSC` (**`Dl τ n` strongly critical for `n ≥ 2`**, a statement);
* `za_lv_mul` (**`YvLv (· < α) q ⇔ YvLv (· < α) (Ω₁·q)`** for strongly critical `α ≤ Ω₁`: the data of `q` and of
  `Ω₁·q` agree below `α`, `Xe.xe_Om1_mul_dat` and `Ul.ulK_div`);
* `za_node_tr` (**both translations at `Ω₁·q`, the subcase read off the leaves of the level `Ω₁·q`**);
* `za_dat_mem`, `za_lt_vt` (**`ρ < ϑᵗ(Ω₁·q + ρ)`** when `Ω₁·q + ρ ∈ Tᵗ`, from `R2.vdArg_dat`, `R2.vdLevel_lt`);
* `za_ups_SC` (a `υ`-point below `P(η₀)` is strongly critical: it is a value of `ψ_{Ω₁}`).

No new axiom.  New definition: `ZaDlSC` (a statement).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **`ϑᵗ(Δₙ)` is strongly critical for `n ≥ 2`** (a statement; [W07a] Lemma 3.3 (a), 3.30, 4.2: the argument of the
non-vacuity paragraph of `R2.CitedXo`). -/
def ZaDlSC : Prop := ∀ τ : Ordinal.{0}, InE τ → τ < Om1 → ∀ n : ℕ, 2 ≤ n → SC (Dl τ n)

/-- **The leaves of `q` and of `Ω₁·q` agree below a strongly critical `α ≤ Ω₁`.** -/
theorem za_lv_mul {α q : Ordinal.{0}} (hα : SC α) (hα1 : α ≤ Om1) (hqθ : Om1 * q < ConjT.th S) :
    YvLv S (· < α) q ↔ YvLv S (· < α) (Om1 * q) := by
  have hq : q < ConjT.th S := (Xe.xe_le_mul q).trans_lt hqθ
  rw [← yv_dat_iff hα hα1 hq, ← yv_dat_iff hα hα1 hqθ]
  refine ⟨fun h => Xe.xe_Om1_mul_dat hα h, fun h => ?_⟩
  have hK : Ul.UlK S 0 α (Om1 * q) := (Vg.vg_code_iffK hα).1 h
  have hO : Ul.UlK S 0 α Om1 := by rw [Rj.rj_Om1]; exact yv_K_Om (by exact one_lt_omega0)
  have hd := Ul.ulK_div hα _ hK _ hO
  rw [Rj.rj_Om1_opow, Ordinal.mul_div_cancel q Rj.rj_Om1_pos.ne'] at hd
  exact (Vg.vg_code_iffK hα).2 hd

/-- **Both translations at a moving level `Ω₁·q` (`B₂ ≤ q`), the subcase read off the leaves of `Ω₁·q`** (under
`ZaDlSC`, `n ≥ 2`): every leaf below `α` ⇒ the argument is shifted by `α` (`R2.xeVt_trL`); otherwise it is kept
(`R2.xoVt_trH`). -/
theorem za_node_tr (hDl : ZaDlSC) {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {n : ℕ} (hn : 2 ≤ n)
    {q ρ : Ordinal.{0}} (hqB : ucB ≤ q) (hqθ : Om1 * q < ConjT.th S) (hρ1 : ρ < Om1) :
    (YvLv S (· < Dl τ n) (Om1 * q) →
      (Om1 * q + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * q + ρ) < Dp τ n →
        Om1 * q + (Dl τ n + ρ) ∈ Tset τ ∧ vt (Dl τ n) (Om1 * q + ρ) = vt τ (Om1 * q + (Dl τ n + ρ))) ∧
      (Om1 * q + (Dl τ n + ρ) ∈ Tset τ → vt τ (Om1 * q + (Dl τ n + ρ)) < Dp τ n →
        Om1 * q + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * q + (Dl τ n + ρ)) = vt (Dl τ n) (Om1 * q + ρ))) ∧
    (¬ YvLv S (· < Dl τ n) (Om1 * q) →
      (Om1 * q + ρ ∈ Tset (Dl τ n) → vt (Dl τ n) (Om1 * q + ρ) < Dp τ n →
        Om1 * q + ρ ∈ Tset τ ∧ vt (Dl τ n) (Om1 * q + ρ) = vt τ (Om1 * q + ρ)) ∧
      (Om1 * q + ρ ∈ Tset τ → vt τ (Om1 * q + ρ) < Dp τ n →
        Om1 * q + ρ ∈ Tset (Dl τ n) ∧ vt τ (Om1 * q + ρ) = vt (Dl τ n) (Om1 * q + ρ))) := by
  have hα := hDl τ hτ hτ1 n hn
  have hα1 : Dl τ n ≤ Om1 := (Dl_spec hτ hτ1 n).2.1.le
  have hq : q < ConjT.th S := (Xe.xe_le_mul q).trans_lt hqθ
  have e := za_lv_mul (S := S) hα hα1 hqθ
  obtain ⟨hL, hH⟩ := yv_node_tr (S := S) hτ hτ1 (by omega : 1 ≤ n) hqB hq hα hρ1
  exact ⟨fun h => hL (e.2 h), fun h => hH (fun h' => h (e.1 h'))⟩

/-- **The data of a moving level from the membership of the argument** (`R2.vdArg_dat`). -/
theorem za_dat_mem {τ q ρ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hqB : ucB ≤ q)
    (hqθ : Om1 * q < ConjT.th S) (hρ1 : ρ < Om1) (h : Om1 * q + ρ ∈ Tset τ) :
    Vd.VdDatIn (· ∈ Tset τ) q := by
  have hq : q < ConjT.th S := (Xe.xe_le_mul q).trans_lt hqθ
  have hM1 : Om1 ≤ q := (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B.le : Om1 ≤ ucB).trans hqB
  exact Vd.vdDatIn_th hqB hq ((vdArg_dat hτ hτ1 hM1 hρ1 h).2 S hqB hq)

/-- **The countable part is below the value** at a moving level: `ρ < ϑᵗ(Ω₁·q + ρ)` for `Ω₁·q + ρ ∈ Tᵗ`,
`ρ ∈ Tᵗ ∩ Ω₁`. -/
theorem za_lt_vt {τ q ρ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hqB : ucB ≤ q)
    (hqθ : Om1 * q < ConjT.th S) (hρ : ρ ∈ Tset τ) (hρ1 : ρ < Om1) (h : Om1 * q + ρ ∈ Tset τ) :
    ρ < vt τ (Om1 * q + ρ) := by
  have hM1 : Om1 ≤ q := (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B.le : Om1 ≤ ucB).trans hqB
  exact (vdLevel_lt hτ hτ1 hM1 (za_dat_mem (S := S) hτ hτ1 hqB hqθ hρ1 h) hρ hρ1).2

/-- **A `υ`-point below `P(η₀)` is strongly critical** (it is `P(η)`, a value of `ψ_{Ω₁}`). -/
theorem za_ups_SC (S : InaccSeq.{0}) {u η0 : Ordinal.{0}} (hu : UpsPt u) (hlt : u < Nm.Pv S η0) : SC u := by
  obtain ⟨ι, hι, rfl⟩ := upsPt_iff_upsilon.1 hu
  rw [← Cd.cdEta_pv (S := S) hι.ne' hlt]
  exact SC_psi Low.InR_Om_one _

end Googology.Trans.PoR.InaccPsi.R2.Za
