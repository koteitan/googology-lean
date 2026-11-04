import Googology.Trans.PoR.InaccPsi.R2.YwLev
import Googology.Trans.PoR.InaccPsi.R2.GsmAt
import Googology.Trans.PoR.InaccPsi.R2.TiPast
import Googology.Trans.PoR.InaccPsi.R2.YrDir

/-!
# ZbNo: REFUTE FIRST FOR THE READING OF CODES WITH ATOMS OF EVERY KIND

The proposed reading: a code atom of kind `b` (a value of `F_b` that is not a fixed point of `F_b`, `F_0 = Γ`) with
index `c` reads `ϑˣ(Ω₁·(Ω₁ + b(x)) + c(x)) = Yw.ywV (b(x)) (c(x)) x`.

* `zbGsCS_lt_BG` (**NO-GO: every code system `Gs.GsCS` has its bound below `B_Γ`**: the field `B_V` and the law
  `Gs.gsm_psi` give `ψ_{Ω₂}(B) = Γ_{Ω₁+1+B} > B`, while `ψ_{Ω₂}` is constant `= B_Γ` on `[B_Γ, Ω₂]`), so the frontier
  lemma `Gs.gsB1_eq` and the reading systems `Yr.YrRS` can never carry a code `≥ B_Γ`: past `B_Γ` a new code system
  (with other atoms than `Γ_{Ω₁+1+c}`, `c < B`) is needed; `zbYrRS_lt_BG`;
* the reading at the code of kind `1` and index `0` (`B_Γ`): `zbKind1` (the least point of `Tˣ ∩ (x, X^x)` closed
  under level `0` is `ywV 1 0 x`, and it is not closed under level `1`); NO EVIDENCE against it;
* the reading at the code of kind `ω` and index `0`: `zbKindW` (the least point closed under every finite level is
  `ywV ω 0 x`, it is above every point `ywV n σ x` with `σ` below it, it is not closed under level `ω`, Lemma EXACT
  `π_{σ,ρ}(ywV ω 0 ρ) = ywV ω 0 σ`); NO EVIDENCE against it.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Tf

/-- **NO-GO: the bound of every code system `Gs.GsCS` is below `B_Γ`.** -/
theorem zbGsCS_lt_BG (S : InaccSeq.{0}) (K : GsCS) : K.B < tfBG := by
  by_contra h
  push Not at h
  have hpsi := gsm_psi K S K.B le_rfl
  have hV := gsmV_lt_Om2 K S
  have hB2 : K.B ≤ Om (1 + 1) := (K.B_V.trans hV).le
  rw [Ti.ti_psi_plateau S h hB2] at hpsi
  have hlt : K.B < gcG K.B := K.B_V
  rw [← hpsi] at hlt
  exact absurd h (not_le.2 hlt)

/-- **No reading system `Yr.YrRS` has a code `≥ B_Γ`.** -/
theorem zbYrRS_lt_BG (S : InaccSeq.{0}) (RS : Yr.YrRS) {c : Ordinal.{0}} (hc : c < RS.K.B) : c < tfBG :=
  hc.trans (zbGsCS_lt_BG S RS.K)

/-- **The atom of kind `1` and index `0` (`B_Γ`) at the base `x`**: `ywV 1 0 x` is the least point above `x` closed
under level `0`, and it is not closed under level `1` (it is a point of level `1`). -/
theorem zbKind1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    x < ywV 1 0 x ∧ YwC x 1 (ywV 1 0 x) ∧ (∀ p, x < p → YwC x 1 p → ywV 1 0 x ≤ p) ∧ ¬ YwC x (1 + 1) (ywV 1 0 x) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨hXT, hxX, -, -⟩ := ywX_facts hx hx1
  have h1X : (1 : Ordinal.{0}) < ywX x := (lu_one_lt_E hx).trans hxX
  obtain ⟨a, b, c⟩ := ywLeast hx hx1 le_rfl h1T h1Ω h1X
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hvT, hxv, -, -, -, -, -⟩ := ywV_facts hx hx1 h1T h1Ω h0T h0Ω
  have hvX : ywV 1 0 x < ywX x := ywV_lt_X hx hx1 h1T h1Ω h0T h0Ω h1X (hx.pos.trans hxX)
  have hK := (ywKind hx hx1 le_rfl h1T h1Ω hvT hxv hvX).2 ⟨0, h0T, h0Ω, rfl⟩
  exact ⟨a, b, c, hK.2⟩

/-- **The atom of kind `ω` and index `0` at the base `x`**: `ywV ω 0 x` is the least point above `x` closed under every
finite level, it lies above every point `ywV n σ x` (`n < ω`, `σ` below it), it is not closed under level `ω`, and
Lemma EXACT holds for it. -/
theorem zbKindW {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    x < ywV ω 0 x ∧ YwC x ω (ywV ω 0 x) ∧ (∀ p, x < p → YwC x ω p → ywV ω 0 x ≤ p) ∧
      ¬ YwC x (ω + 1) (ywV ω 0 x) ∧
      (∀ n : ℕ, ∀ σ, σ ∈ Tset x → σ < Om1 → σ < ywV ω 0 x → ywV (n : Ordinal.{0}) σ x < ywV ω 0 x) := by
  have hωx : ω < x := omega0_lt_inE hx
  have hωT : ω ∈ Tset x := mem_T_of_le hx hx1 hωx.le
  have hωΩ : ω < Om1 := hωx.trans hx1
  obtain ⟨hXT, hxX, -, -⟩ := ywX_facts hx hx1
  have hωX : ω < ywX x := hωx.trans hxX
  obtain ⟨a, b, c⟩ := ywLeast hx hx1 one_lt_omega0.le hωT hωΩ hωX
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hvT, hxv, -, -, -, -, -⟩ := ywV_facts hx hx1 hωT hωΩ h0T h0Ω
  have hvX : ywV ω 0 x < ywX x := ywV_lt_X hx hx1 hωT hωΩ h0T h0Ω hωX (hx.pos.trans hxX)
  have hK := (ywKind hx hx1 one_lt_omega0.le hωT hωΩ hvT hxv hvX).2 ⟨0, h0T, h0Ω, rfl⟩
  refine ⟨a, b, c, hK.2, fun n σ hσT hσΩ hσ => ?_⟩
  have hnx : (n : Ordinal.{0}) < x := (natCast_lt_omega0 n).trans hωx
  exact ywV_lt_lower hx hx1 (mem_T_of_le hx hx1 hnx.le) (hnx.trans hx1) hσT hσΩ hωT hωΩ h0T h0Ω
    (natCast_lt_omega0 n) hσ

/-- **Lemma EXACT at the atom of kind `ω` and index `0`.** -/
theorem zbKindW_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    ywV ω 0 ρ ∈ TB ρ σ ∧ pi σ ρ (ywV ω 0 ρ) = ywV ω 0 σ := by
  have hωσ : ω < σ := omega0_lt_inE hB.1
  have hωρ : ω < Om1 := (hωσ.trans hB.2.2.1).trans hB.2.2.2
  have h0σ : (0 : Ordinal.{0}) < σ := hB.1.pos
  have h := ywV_pi hB (mem_TB_of_lt hB hωσ) hωρ (mem_TB_of_lt hB h0σ) (hB.2.1.pos.trans hB.2.2.2)
  rw [pi_lt hB hωσ, pi_lt hB h0σ] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Zb
