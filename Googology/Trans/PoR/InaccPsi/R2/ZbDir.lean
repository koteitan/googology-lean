import Googology.Trans.PoR.InaccPsi.R2.ZbLad

/-!
# ZbDir: DIRECT READINGS PAST `B_Γ` — THE LAYERS `c ≥ B_Γ` FROM ONE STATEMENT, AND ITS FIRST INSTANCE

`Yr.YrDirect S B₀` (codes below `B₀` in admissible reading systems `Yr.YrRS`) cannot pass `B_Γ` (`Zb.zbYrRS_lt_BG`).
Past `B_Γ` the statement is `ZbDirect S B₀`: every atom index `B_Γ ≤ B < B₀` has a gated layer (gate below
`K = ψ_{Ω₁}(Ω_ω)`) whose top reads a top code `T ≥ Γ_{Ω₁+1+B}` with the atoms of `Zb.zbU`, with terms for every code
below `T` (`ZbLayAt S B`).  Then UPPER ∧ LOWER ∧ CapV hold below `ι(Γ_{Ω₁+1+B}·ω)` for every `B < B₀` (the indices
below `B_Γ` by `Yr.yrDirect`), so `ZbDirect S Γ(c+1)` gives the conclusions of `skLayLoFix` and `skLayHiFix` at `c`.

* `ZbLayAt`, `ZbDirect`, `zbUV_of_lay`, `zbUV_of_direct`, `zbLay_of_direct` (**`ZbDirect S Γ(c+1)` ⇒ UPPER ∧ LOWER ∧
  CapV at every range restart below `ι(Γ(φ(ℓ, Γ(c)+1))·ω)`, `ℓ < Γ(c+1)`**);
* `zbLayAt_BG`, `zbLayAt_BGn`, `zbDirect_w` (**`ZbDirect S (B_Γ + ω)`, UNCONDITIONAL**: the non-vacuity of the
  statement), `zbUV_w` (**UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+(B_Γ+n)}·ω)` for every `n`**).

No new axiom.  New definitions: `ZbLayAt`, `ZbDirect`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **A layer for the atom index `B`**: a gated layer (gate below `K`) whose top reads a top code
`Γ_{Ω₁+1+B} ≤ T ≤ X` with the atoms of `zbU`, with terms for every code below `T`, `T` a code over every strongly
critical base `≥ K`, and the top above `ε_{x+1}`. -/
def ZbLayAt (S : InaccSeq.{0}) (B : Ordinal.{0}) : Prop :=
  ∃ L : GdB, ∃ T : Ordinal.{0}, gcG B ≤ T ∧ L.g < Td.tdK S ∧ T ≤ tlX ∧ Om 1 ≤ T ∧ ω ^ T = T ∧
    (∀ y, SC y → y < Om 1 → L.g < y → L.K.E y = gxTh y (zbU.At y) T) ∧ ZbPolyG zbU L.K.sys T ∧
    (∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (zbU.At Z) T) ∧ (∀ x, InE x → x < Om1 → L.g < x → eN x < L.K.E x)

/-- **DIRECT READINGS PAST `B_Γ`**: a layer for every atom index `B_Γ ≤ B < B₀`. -/
def ZbDirect (S : InaccSeq.{0}) (B₀ : Ordinal.{0}) : Prop := ∀ B, tfBG ≤ B → B < B₀ → ZbLayAt S B

/-- **UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+B}·ω)` from a layer for `B`.** -/
theorem zbUV_of_lay {S : InaccSeq.{0}} {B : Ordinal.{0}} (h : ZbLayAt S B) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  obtain ⟨L, T, hBT, hg, hT, hTO, hTE, htop, hP, hcl, htopE⟩ := h
  have hl' : l < iota S (ω ^ T * ω) := by
    rw [hTE]; exact hl.trans_le (iota_mono (S := S) _ _ (mul_le_mul_left hBT ω))
  exact zbUV zbU L S hg T hT htop hP hcl htopE hTO hr hl'

/-- **UPPER ∧ LOWER ∧ CapV below `ι(Γ_{Ω₁+1+B}·ω)` for every `B < B₀`** (`B < B_Γ` by `Yr.yrDirect`). -/
theorem zbUV_of_direct {S : InaccSeq.{0}} {B₀ : Ordinal.{0}} (h : ZbDirect S B₀) :
    ∀ l, CdRange S l → ∀ B, B < B₀ → l < iota S (gcG B * ω) → CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  intro l hr B hB hl
  by_cases hBG : B < tfBG
  · exact yrUV_of_direct (yrDirect S) l hr B hBG hl
  · exact zbUV_of_lay (h B (not_lt.1 hBG) hB) hr hl

/-- **THE WHOLE LAYER `c` FROM DIRECT READINGS BELOW `Γ(c+1)`**: the conclusions of `skLayLoFix` (levels `ℓ < Γ(c)`)
and of `skLayHiFix` (levels `Γ(c) ≤ ℓ < Γ(c+1)`) at `c`. -/
theorem zbLay_of_direct {S : InaccSeq.{0}} {c : Ordinal.{0}} (h : ZbDirect S (gcG (c + 1))) :
    ∀ l, CdRange S l → (∃ ℓ, ℓ < gcG (c + 1) ∧ l < iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  rintro l hr ⟨ℓ, hℓ, hl⟩
  exact zbUV_of_direct h l hr _ (Yc.yc_veb_lt_next hℓ) hl

/-- **The layer for the index `B_Γ`** (`Yw.ywBGB`, top code `B_Γ = Γ_{Ω₁+1+B_Γ}`). -/
theorem zbLayAt_BG (S : InaccSeq.{0}) : ZbLayAt S tfBG :=
  ⟨ywBGB, tfBG, zb_gcG_BG.le, zbBG_g S, tl_BG_lt_X.le, by rw [← Br.Om1_eq]; exact tfBG_gt.le,
    Low.opow_eq_self_of_SC tfBG_SC, fun y hy hy1 _ => zbBG_top S hy hy1, zbBG_poly S, fun Z hZ _ => zbBG_cl hZ,
    zbBG_topE⟩

/-- **The layer for the index `B_Γ + (n+1)`** (`Zb.zbBGn n`). -/
theorem zbLayAt_BGn (S : InaccSeq.{0}) (n : ℕ) : ZbLayAt S (tfBG + ((n + 1 : ℕ) : Ordinal.{0})) :=
  ⟨(zbBGn n).1, zbT n, le_rfl, zbBGn_gK S n, (zbT_lt_X n).le, (gcG_Om1_lt _).le, Low.opow_eq_self_of_SC (zbT_SC n),
    (zbBGn_codes S n).1, (zbBGn_codes S n).2, fun Z hZ _ => zbT_cl n hZ, zbBGn_topE n⟩

/-- **`ZbDirect S (B_Γ + ω)`, UNCONDITIONAL** (the non-vacuity of `ZbDirect`). -/
theorem zbDirect_w (S : InaccSeq.{0}) : ZbDirect S (tfBG + ω) := by
  intro B hB1 hB2
  obtain ⟨d, rfl⟩ := exists_add_of_le hB1
  have hd : d < ω := (add_lt_add_iff_left _).1 hB2
  obtain ⟨n, rfl⟩ := lt_omega0.1 hd
  cases n with
  | zero => rw [Nat.cast_zero, add_zero]; exact zbLayAt_BG S
  | succ k => exact zbLayAt_BGn S k

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+(B_Γ+n)}·ω)`, every `n`** (UNCONDITIONAL). -/
theorem zbUV_w (S : InaccSeq.{0}) (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l)
    (hl : l < iota S (gcG (tfBG + (n : Ordinal.{0})) * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (zbDirect_w S) l hr _ ((add_lt_add_iff_left _).2 (natCast_lt_omega0 n)) hl

end Googology.Trans.PoR.InaccPsi.R2.Zb
