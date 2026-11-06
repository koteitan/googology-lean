import Googology.Trans.PoR.InaccPsi.R2.QcImgB

/-!
# QcUps: EVERY COUNTABLE `υ`-POINT ABOVE AN `ε`-NUMBER IS STRONGLY CRITICAL; THE BASE OF A RESTART CONTEXT IS

`Za.za_ups_SC` shows it for a `υ`-point below `P(η₀)` (a value of `ψ_{Ω₁}`), through a sequence `S`.  Lemma IMG at a
generic level (`Qc.qc_img`) asks a strongly critical base; here, with no `S`:

* `qc_m_SC` (**`Tˣ ∩ Ω₁ = m` is strongly critical** for an `ε`-number `x < Ω₁`: `φ(0, b) = ω^b < m` as `m` is an
  `ε`-number, and `φ(a, b) ≤ ϑˣ(Ω₁·a + b) ∈ Tˣ ∩ Ω₁` for `a ≥ 1`, `Gl.glA_veb_le`; [W07a] Theorem 3.23 with
  [W07b] Corollary 5.10 through `vz_next`);
* `qc_ups_SC` (**a `υ`-point `u < Ω₁` above an `ε`-number is strongly critical**: by induction on `u`; the supremum
  `p` of the `υ`-points of `(x₀, u)` is strongly critical (`Rk.rk_SC_sSup`); `p = u`, or `u` is the next `<₁ ∞` point
  after `p`, i.e. `Tᵖ ∩ Ω₁`; without such points `u` is the next one after `x₀`);
* `qc_rstK_SC` (**the base `ρ` of a restart context `RstK ρ τ δ` is strongly critical**: a `υ`-point lies below
  it, `RstK.land`), `qc_img_rst` (**Lemma IMG below `ϑᵖ(Ω₁·N)`** with no strong-criticality hypothesis).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gg

/-- **`Tˣ ∩ Ω₁ = m` is strongly critical.** -/
theorem qc_m_SC {x m : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxm : x < m)
    (hTm : ∀ a, a < Om1 → (a ∈ Tset x ↔ a < m)) (hm1 : m < Om1) (hmE : InE m) : SC m := by
  refine ⟨lt_of_le_of_lt zero_le hxm, fun a ha b hb => ?_⟩
  have ha1 : a < Om1 := ha.trans hm1
  have hb1 : b < Om1 := hb.trans hm1
  have haT : a ∈ Tset x := (hTm a ha1).2 ha
  have hbT : b ∈ Tset x := (hTm b hb1).2 hb
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply]; exact hmE.opow_lt hb
  · have h1a : 1 ≤ a := Order.one_le_iff_ne_zero.2 ha0
    obtain ⟨hgT, -, hg1, -, -, -⟩ := glA_facts hx hx1 h1a haT ha1 hbT hb1
    exact (glA_veb_le hx hx1 h1a haT ha1 hbT hb1).trans_lt ((hTm _ hg1).1 hgT)

/-- **A `υ`-point `u < Ω₁` above an `ε`-number `x₀` is strongly critical.** -/
theorem qc_ups_SC : ∀ u, UpsPt u → u < Om1 → ∀ x₀, InE x₀ → x₀ < u → SC u := by
  intro u
  induction u using WellFoundedLT.induction with
  | ind u IH =>
  intro hu hu1 x₀ hx₀ hx₀u
  have huE : InE u := upsPt_inE hu
  set S' := {v | UpsPt v ∧ x₀ < v ∧ v < u} with hS'
  have hS'SC : ∀ v ∈ S', SC v := fun v hv => IH v hv.2.2 hv.1 (hv.2.2.trans hu1) x₀ hx₀ hv.2.1
  have hbd : BddAbove S' := ⟨u, fun v hv => hv.2.2.le⟩
  -- the next `<₁ ∞` point after a base `b ∈ [x₀, u)` with no `υ`-point in `(b, u)` is `u`
  have hnext : ∀ b, InE b → x₀ ≤ b → b < u → (∀ v ∈ S', v ≤ b) → SC u := fun b hb hx₀b hbu hmax => by
    obtain ⟨m, hbm, hm, hmin, hTm, hm1, hmE⟩ := vz_next hb (hbu.trans hu1)
    have hmu : m ≤ u := hmin u hbu hu.2
    have hum : u ≤ m := by
      by_contra hlt
      push Not at hlt
      have hmS : m ∈ S' := ⟨⟨lt_of_le_of_lt zero_le hbm, hm⟩, lt_of_le_of_lt hx₀b hbm, hlt⟩
      exact absurd (hmax m hmS) (not_le.2 hbm)
    rw [← le_antisymm hmu hum]
    exact qc_m_SC hb (hbu.trans hu1) hbm hTm hm1 hmE
  rcases S'.eq_empty_or_nonempty with he | hne
  · exact hnext x₀ hx₀ le_rfl hx₀u fun v hv => absurd hv (by rw [he]; exact Set.notMem_empty _)
  · have hpS : SC (sSup S') := Rk.rk_SC_sSup hS'SC hne hbd
    have hpu : sSup S' ≤ u := csSup_le hne fun v hv => hv.2.2.le
    rcases hpu.lt_or_eq with hlt | heq
    · obtain ⟨v0, hv0⟩ := hne
      have hx₀p : x₀ ≤ sSup S' := hv0.2.1.le.trans (le_csSup hbd hv0)
      exact hnext _ (Low.opow_eq_self_of_SC hpS) hx₀p hlt fun v hv => le_csSup hbd hv
    · rw [← heq]; exact hpS

/-- **The base of a restart context is strongly critical.** -/
theorem qc_rstK_SC {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) : SC ρ := by
  obtain ⟨σ, σ', hσ, -, hσσ', hσ'ρ, -⟩ := h.land 0 h.ρU.1
  exact qc_ups_SC ρ h.ρU h.ρ1 σ (upsPt_inE hσ) (hσσ'.1.trans hσ'ρ)

/-- **LEMMA IMG BELOW `ϑᵖ(Ω₁·N)`** in every restart context, for every level `Ω₁ ≤ N < ε_{Ω₁+1}` with
`rjDat N < ρ`. -/
theorem qc_img_rst {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) {N : Ordinal.{0}} (hN1 : Om1 ≤ N) (hNE : N < ggE)
    (hNρ : Rj.rjDat N < ρ) : ∀ v, v < vt ρ (Om1 * N) → GnI ρ δ v :=
  qc_img h (qc_rstK_SC h) hN1 hNE hNρ

end Googology.Trans.PoR.InaccPsi.R2.Qc
