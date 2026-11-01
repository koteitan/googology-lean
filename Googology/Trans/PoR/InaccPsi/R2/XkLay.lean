import Googology.Trans.PoR.InaccPsi.R2.XkCode
import Googology.Trans.PoR.InaccPsi.R2.WxTop

/-!
# XkLay: THE OLD LEVELS OF THE LAYER `k` FROM TWO STATEMENTS ON `Xk.XkVD k`, AND THEIR INSTANCE `k = 0`

The old-level part of the layer `k` (`skLayLo`: range restarts below `ι(Γ(φ(ℓ, Γ(k)+1))·ω)` for some `ℓ < Γ(k)`)
follows from two statements about the systems over the base atom `Γ(k)`:

* `XkLaySys S k` (**the systems**: for every level `ℓ < Γ(k)` an `XkVD k` with bound `≥ φ(ℓ, Γ(k)+1)` and gate below
  `K = Td.tdK S`);
* `XkLayFront S k` (**the frontier lemma over `Γ(k)`**: UPPER, LOWER and CapV at every range restart below
  `ι(Γ(B)·ω)` for every `XkVD k` with gate below `K`).

`xkLayLo_of` is the reduction (one proof for every `k`).  At `k = 0` both statements are THEOREMS of the repo
(`xkLayFront_zero` from `Hg.hgV_locD_enum` / `Hg.hgV_locD_capV` through `Xk.XkVD.toHg`; `xkLaySys_zero` from the
closed region (A2), `Wx.wxSysA2`, through `Xk.XkVD.ofHg`), and `xkLayLo_zero` is the region-(A2) location again
(non-vacuity of the reduction).  For `k ≥ 1`, `XkLayFront S k` covers every range restart below the system bound,
hence all of region (A) (the open (A3) leaf `skA3T0Start` included), and `XkLaySys S k` needs the readings of every
code below `Γ(k)`.

* `xk_veb_lt` (**`φ(ℓ, Γ(k)+1) < φ(Γ(k), 1)` for `ℓ < Γ(k)`**), `XkLaySys`, `XkLayFront`, `xkLayLo_of`,
  `xkLayFront_zero`, `xkLaySys_zero`, `xkLayLo_zero`.

No new axiom.  New definitions: `XkLaySys`, `XkLayFront`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xk

open Googology.Trans.PoR.InaccPsi.R2.Hg Googology.Trans.PoR.InaccPsi.R2.Gc
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **`φ(ℓ, Γ(k)+1) < φ(Γ(k), 1)`** for every `ℓ < Γ(k)`. -/
theorem xk_veb_lt {k ℓ : Ordinal.{0}} (hℓ : ℓ < gcG k) : veblen ℓ (gcG k + 1) < veblen (gcG k) 1 := by
  have hG0 : gcG k ≠ 0 := (lt_of_le_of_lt zero_le hℓ).ne'
  have h1 : veblen ℓ (veblen (gcG k) 1) = veblen (gcG k) 1 := veblen_veblen_of_lt hℓ 1
  have hlt : gcG k < veblen (gcG k) 1 :=
    (left_le_veblen (gcG k) 0).trans_lt ((isNormal_veblen _).strictMono zero_lt_one)
  have hE : InE (veblen (gcG k) 1) := Gg.gg_veblen_eps hG0
  have h2 : gcG k + 1 < veblen (gcG k) 1 := (ev_isSuccLimit_of_inE hE).add_one_lt hlt
  have h3 := (isNormal_veblen ℓ).strictMono h2
  rwa [h1] at h3

/-- **The systems of the old levels of the layer `k`**: for every `ℓ < Γ(k)` a system over `Γ(k)` with bound at least
`φ(ℓ, Γ(k)+1)` and gate below `K`. -/
def XkLaySys (S : InaccSeq.{0}) (k : Ordinal.{0}) : Prop :=
  ∀ ℓ, ℓ < gcG k → ∃ D : XkVD k, veblen ℓ (gcG k + 1) ≤ D.B ∧ D.γ < Td.tdK S

/-- **The frontier lemma over `Γ(k)`**: UPPER, LOWER and CapV at every range restart below `ι(Γ(B)·ω)`, for every
system over `Γ(k)` with gate below `K`. -/
def XkLayFront (S : InaccSeq.{0}) (k : Ordinal.{0}) : Prop :=
  ∀ D : XkVD k, D.γ < Td.tdK S → ∀ l, Cd.CdRange S l → l < Bt.iota S (gcG D.B * ω) →
    Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l

/-- **THE REDUCTION** (every `k`): the systems and the frontier lemma over `Γ(k)` give UPPER, LOWER and CapV at every
range restart below `ι(Γ(φ(ℓ, Γ(k)+1))·ω)` for some `ℓ < Γ(k)`. -/
theorem xkLayLo_of {S : InaccSeq.{0}} {k : Ordinal.{0}} (hS : XkLaySys S k) (hF : XkLayFront S k) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG k ∧ l < Bt.iota S (gcG (veblen ℓ (gcG k + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l := by
  rintro l hr ⟨ℓ, hℓ, hl⟩
  obtain ⟨D, hB, hγ⟩ := hS ℓ hℓ
  refine hF D hγ l hr (hl.trans_le (Bt.iota_mono (S := S) _ _ ?_))
  exact mul_le_mul_left (gcG_le hB) ω

/-- **The frontier lemma over `Γ(0) = G` is a theorem** (`Hg.hgV_locD_enum`, `Hg.hgV_locD_capV`). -/
theorem xkLayFront_zero (S : InaccSeq.{0}) : XkLayFront S 0 := fun D hγ _ hr hl =>
  ⟨(hgV_locD_enum D.toHg S hγ hr hl).1, (hgV_locD_enum D.toHg S hγ hr hl).2, hgV_locD_capV D.toHg S hγ hr hl⟩

/-- **The systems over `G` of the old levels are a theorem** (the closed region (A2), `Wx.wxSysA2`). -/
theorem xkLaySys_zero (S : InaccSeq.{0}) : XkLaySys S 0 := fun ℓ hℓ => by
  obtain ⟨V, hB, hγ⟩ := Wx.wxSysA2 S _ (xk_veb_lt hℓ)
  exact ⟨XkVD.ofHg V, hB, hγ⟩

/-- **Non-vacuity of the reduction**: at `k = 0` it gives the region-(A2) location. -/
theorem xkLayLo_zero (S : InaccSeq.{0}) :
    ∀ l, Cd.CdRange S l → (∃ ℓ, ℓ < gcG 0 ∧ l < Bt.iota S (gcG (veblen ℓ (gcG 0 + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l :=
  xkLayLo_of (xkLaySys_zero S) (xkLayFront_zero S)

end Googology.Trans.PoR.InaccPsi.R2.Xk
