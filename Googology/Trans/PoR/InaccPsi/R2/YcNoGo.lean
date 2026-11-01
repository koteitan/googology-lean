import Googology.Trans.PoR.InaccPsi.R2.XkLay
import Googology.Trans.PoR.InaccPsi.R2.WsAll

/-!
# YcNoGo: NEITHER THE CODE INTERFACE NOR A RELABELLING TRANSFERS THE REGION-(A) SYSTEMS TO THE BASE `Γ(k)`, `k ≥ 1`

Two routes to `Xk.XkLaySys S k` (`k ≥ 1`) without re-proving the system recursion were tested.

**(a) An instance of the generic family.**  `Ws.wsStep_om1`, `Ws.wsFam`, `Ws.wsSysAll` are generic in the code
interface `Ws.WsC` and in the raw datum `Wo.WoR`, but their OUTPUT is a `Hg.HgVD`, whose bound is below `Γ(1)`
(field `B_lt1`), and every raw datum they accept lies below `Γ(1)` (`Ws.WsGood.S_lt1`).  A system of
`XkLaySys S k` has bound `≥ φ(ℓ, Γ(k)+1) ≥ Γ(1)`:

* `yc_G1_le_veb` (**`Γ(1) ≤ φ(ℓ, Γ(k)+1)` for `k ≥ 1`**), `ycHg_noLay` (**no `Hg.HgVD` has bound `≥ φ(ℓ, Γ(k)+1)`**),
  `ycWs_noLay` (so `Ws.wsSysAll` never gives a system of `XkLaySys S k`), `ycGood_F_lt` (**every raw datum good for
  the family lies below `Γ(1)`**), `ycGood_noBase` (`Γ(k)` is never such a datum), `ycWsC_noLev` (a `Ws.WsC` has no
  level `≥ Γ(1)`, so the levels in `[Γ(1), Γ(k))` of `XkLaySys S k`, `k ≥ 2`, have no code interface).

**(b) A relabelling of codes.**  An order-preserving map `s` that keeps the codes below `G` and sends `G` to `Γ(k)`
misses every code in `[G, Γ(k))` (`ycRelab_gap`), and, if it moves sums `G + d ↦ Γ(k) + s d`, it misses the mixed
code `Γ(k) + G` (`ycRelab_mixed`); every system of `XkLaySys S k` has both kinds of codes below its bound
(`ycVD_codes`: `G < Γ(k)` and `Γ(k) + G < φ(ℓ, Γ(k)+1) ≤ B`), so its readings cannot come from a relabelled
system over `G`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Hd

/-- **`Γ(1) ≤ φ(ℓ, Γ(k)+1)`** for every `k ≥ 1` and every `ℓ`. -/
theorem yc_G1_le_veb {k ℓ : Ordinal.{0}} (hk : 1 ≤ k) : gcG 1 ≤ veblen ℓ (gcG k + 1) :=
  (gcG_le hk).trans ((le_self_add).trans (right_le_veblen ℓ _))

/-- **NO-GO (a), output**: no `Hg.HgVD` has a bound `≥ φ(ℓ, Γ(k)+1)`, `k ≥ 1`. -/
theorem ycHg_noLay (V : Hg.HgVD) {k ℓ : Ordinal.{0}} (hk : 1 ≤ k) : ¬ veblen ℓ (gcG k + 1) ≤ V.B :=
  fun h => absurd V.B_lt1 (not_lt.2 ((yc_G1_le_veb hk).trans h))

/-- **NO-GO (a), the family**: the systems of `Ws.wsSysAll` (any code interface, any classification) never have a
bound `≥ φ(ℓ', Γ(k)+1)`, `k ≥ 1`. -/
theorem ycWs_noLay {C : Ws.WsC} {L : Ordinal.{0}} (hc : Ws.WsCls C L) (ℓ : Ordinal.{0}) {k ℓ' : Ordinal.{0}}
    (hk : 1 ≤ k) : ¬ veblen ℓ' (gcG k + 1) ≤ (Ws.wsV hc ℓ).B :=
  ycHg_noLay _ hk

/-- **NO-GO (a), the raw datum**: every datum good for the family lies below `Γ(1)`. -/
theorem ycGood_F_lt {C : Ws.WsC} {r : Wo.WoR} {ℓ : Ordinal.{0}} (h : Ws.WsGood C r ℓ) : r.F < gcG 1 :=
  (hdNx_gt ℓ r.F).trans h.S_lt1

/-- **`Γ(k)`, `k ≥ 1`, is never a raw datum of the family.** -/
theorem ycGood_noBase {C : Ws.WsC} {r : Wo.WoR} {ℓ k : Ordinal.{0}} (h : Ws.WsGood C r ℓ) (hk : 1 ≤ k) :
    r.F ≠ gcG k := fun e => absurd (ycGood_F_lt h) (not_lt.2 (e ▸ gcG_le hk))

/-- **A code interface `Ws.WsC` has no level `≥ Γ(1)`.** -/
theorem ycWsC_noLev (C : Ws.WsC) {ℓ : Ordinal.{0}} (hℓ : gcG 1 ≤ ℓ) : ¬ C.Lev ℓ :=
  fun h => absurd (h.2.2.trans C.Bd_lt1) (not_lt.2 hℓ)

/-- **NO-GO (b), the gap**: an order-preserving map keeping the codes below `G` and sending `G` to `Γ(k)`, `k ≥ 1`,
has no value in `[G, Γ(k))`. -/
theorem ycRelab_gap {s : Ordinal.{0} → Ordinal.{0}} (hs : StrictMono s) (hlow : ∀ c, c < gcG 0 → s c = c)
    {k : Ordinal.{0}} (hG : s (gcG 0) = gcG k) (c : Ordinal.{0}) : ¬ (gcG 0 ≤ s c ∧ s c < gcG k) := by
  rintro ⟨h1, h2⟩
  rcases lt_or_ge c (gcG 0) with hc | hc
  · rw [hlow c hc] at h1; exact absurd hc (not_lt.2 h1)
  · have := hs.monotone hc
    rw [hG] at this
    exact absurd h2 (not_lt.2 this)

/-- **NO-GO (b), the mixed codes**: if moreover `s (G + d) = Γ(k) + s d`, the code `Γ(k) + G` is not a value. -/
theorem ycRelab_mixed {s : Ordinal.{0} → Ordinal.{0}} (hs : StrictMono s) (hlow : ∀ c, c < gcG 0 → s c = c)
    {k : Ordinal.{0}} (hk : 1 ≤ k) (hG : s (gcG 0) = gcG k) (hadd : ∀ d, s (gcG 0 + d) = gcG k + s d)
    (c : Ordinal.{0}) : s c ≠ gcG k + gcG 0 := by
  have hGk : gcG 0 < gcG k := gcG_lt (zero_lt_one.trans_le hk)
  intro e
  rcases lt_or_ge c (gcG 0) with hc | hc
  · rw [hlow c hc] at e
    exact absurd (e ▸ hc) (not_lt.2 le_add_self)
  · have hdec : gcG 0 + (c - gcG 0) = c := Ordinal.add_sub_cancel_of_le hc
    rw [← hdec, hadd] at e
    have e' : s (c - gcG 0) = gcG 0 := (add_left_cancel e)
    rcases lt_or_ge (c - gcG 0) (gcG 0) with hd | hd
    · rw [hlow _ hd] at e'; exact absurd (e' ▸ hd) (lt_irrefl _)
    · have := hs.monotone hd
      rw [hG, e'] at this
      exact absurd hGk (not_lt.2 this)

/-- **Every system of `XkLaySys S k` (`k ≥ 1`) has the codes `[G, Γ(k))` and the mixed code `Γ(k) + G` below its
bound** (so its readings there cannot come from a relabelled system over `G`). -/
theorem ycVD_codes {k ℓ : Ordinal.{0}} (hk : 1 ≤ k) (D : Xk.XkVD k) (hD : veblen ℓ (gcG k + 1) ≤ D.B) :
    gcG 0 < gcG k ∧ gcG k ≤ D.B ∧ gcG k + gcG 0 < D.B := by
  have hGk : gcG 0 < gcG k := gcG_lt (zero_lt_one.trans_le hk)
  refine ⟨hGk, D.G_le, ?_⟩
  have hP := isPrincipal_add_omega0_opow (gcG k + 1)
  have hE : InE (gcG k) := Low.opow_eq_self_of_SC (gcG_SC k)
  have h1 : gcG k < ω ^ (gcG k + 1) := (lt_add_one _).trans_le (right_le_opow _ one_lt_omega0)
  have h2 : gcG k + gcG 0 < ω ^ (gcG k + 1) := hP h1 (hGk.trans h1)
  have h3 : ω ^ (gcG k + 1) ≤ veblen ℓ (gcG k + 1) := by
    rw [← veblen_zero_apply]; exact veblen_left_monotone _ zero_le
  exact h2.trans_le (h3.trans hD)

end Googology.Trans.PoR.InaccPsi.R2.Yc
