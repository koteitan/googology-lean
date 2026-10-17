import Googology.Trans.PoR.InaccPsi.R2.XtW
import Googology.Trans.PoR.InaccPsi.R2.XtLim

/-!
# The limit layers: up to `Λ_{ω²} = sup_k Λ⁺(lim^k)`, tops `B(x)·x^{ω·k+n}`

`xtLL k = lim^k vzLay` (`R2.XtLim`): the `k`-th limit layer, top `B(x)·x^{ω·k}` (`xtLL_top`); its next layers
`(xtLL k).iter n` have tops `B(x)·x^{ω·k+n}` (`xtLL_iter_top`).  With `Λ⁺_k = xtLamK k = xtB1 (xtLL k).sys`:

* `xtLamK_zero` (`Λ⁺_0 = cpB1`), `xtLamK_lt` (**`Λ⁺_k < Λ⁺_{k+1}`**: `Λ⁺_k < Λ(lim) < Λ⁺(lim)`), `xtLL_eq`
  (`O_{LL m} = O_{LL k}` below `Λ⁺_k`, `k ≤ m`);
* `xtFamW2 : XtFam` (bounds `Λ⁺_k`, offsets `O_{LL k}`), so every theorem of `R2.XtFam` holds with
  `Λ = Λ_{ω²} = xtFamW2.famSup`: **Theorem BLK^O below `υ_{Λ_{ω²}}`**, CORE-C, `υ_{Λ_{ω²}} ≤ ρ_L < ν_C`, UPPER and LOWER
  at every non-fixed restart of the range below `Λ_{ω²}`, the caps, the roads with the rest asked only outside
  `Λ_{ω²}`; `xtW2_of_cp` (the hypotheses of `xtFamW2.famRoad3` from those of `cpRoad3`), `xtFamW2_iso`;
* the instances written out: `xtW2_blk`, `xtW2_nuC`, `xtW2_init`, `xtW2Road3`, `xtW2Road`, `xtW2Road_cap`,
  `xtW2Road2`;
* the values: `xtLL_reachLam` (**`lh(ρ) = δ + B(ρ)·ρ^{ω·k}` at the frontier of `xtLL k`**), `xtLL_reachB1`
  (**`lh(ρ) = δ + B(ρ)·ρ^{ω·k+n} + 1` at `Λ⁺((xtLL k).iter n)`**), `xtW_lt_W2` (`Λ_ω < Λ_{ω²}`).

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

/-- **The `k`-th limit layer** `lim^k vzLay`. -/
noncomputable def xtLL : ℕ → XtLay
  | 0 => vzLay
  | k + 1 => (xtLL k).xtLim

theorem xtLL_top (k : ℕ) (x : Ordinal.{0}) : (xtLL k).sys.top x = VzB x * x ^ (ω * (k : Ordinal.{0})) := by
  induction k with
  | zero => show VzB x = _; rw [Nat.cast_zero, mul_zero, opow_zero, mul_one]
  | succ k ih =>
    show (xtLL k).sys.top x * x ^ ω = _
    rw [ih, Nat.cast_succ, mul_add_one, opow_add, mul_assoc]

theorem xtLL_iter_top (k n : ℕ) (x : Ordinal.{0}) :
    ((xtLL k).iter n).sys.top x = VzB x * x ^ (ω * (k : Ordinal.{0}) + (n : Ordinal.{0})) := by
  rw [XtLay.iter_top, xtLL_top, opow_add, mul_assoc]

/-- `Λ⁺_k`: the first limit of the frontiers of the `k`-th limit layer. -/
noncomputable def xtLamK (k : ℕ) : Ordinal.{0} := xtB1 (xtLL k).sys

theorem xtLamK_zero : xtLamK 0 = Cp.cpB1 := xtVz_B1

theorem xtLamK_lt (k : ℕ) : xtLamK k < xtLamK (k + 1) :=
  ((xtLL k).lim_gt 0).trans (xtLL k).xtLim.xtLamLt

theorem xtLamK_lt_Om1 (k : ℕ) : xtLamK k < Om1 := xtB1_lt_Om1 (xtLL k).topPkg

theorem xtLamK_strictMono : StrictMono xtLamK := strictMono_nat_of_lt_succ xtLamK_lt

/-- `O_{LL m} = O_{LL k}` below `Λ⁺_k` for `k ≤ m`. -/
theorem xtLL_eq {k m : ℕ} (h : k ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμk : μ < xtLamK k) :
    xtOrec (xtLL m).sys μ = xtOrec (xtLL k).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    rw [← ih]
    exact (xtLL m).lim_eq 0 hμ (hμk.trans_le (xtLamK_strictMono.monotone hkm))

/-- **The family of the limit layers**: bounds `Λ⁺_k`, offsets `O_{LL k}`. -/
noncomputable def xtFamW2 : XtFam where
  bd := xtLamK
  off := fun k => xtOrec (xtLL k).sys
  spec := fun k => xtSpec1 (xtLL k).topPkg
  mono := xtLamK_lt
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtLamK_lt_Om1 k))

theorem xtFamW2_sup : xtFamW2.famSup = ⨆ k : ℕ, xtLamK k := rfl

theorem xtFamW2_iso : xtFamW2.famIsoOff := fun k _ hl hlk hfix hiso =>
  xtIso hl hfix (hlk.trans (xtLamK_lt_Om1 k)) hiso (X := (xtLL k).sys)

/-- **The reach at the frontier of `xtLL k`**: `lh(ρ) = δ + B(ρ)·ρ^{ω·k}`. -/
theorem xtLL_reachLam (k : ℕ) :
    IsReach R2C (upsilon (xtLam (xtLL k).sys))
      (upsilon (xtLam (xtLL k).sys + ω + 1) +
        VzB (upsilon (xtLam (xtLL k).sys)) * upsilon (xtLam (xtLL k).sys) ^ (ω * (k : Ordinal.{0}))) := by
  rw [← xtLL_top, ← xtOrec_Lam]
  exact xtReach1 (xtLL k).topPkg xtLam_ri (xtLL k).xtLamLt

/-- **The reach at `Λ⁺((xtLL k).iter n)`**: `lh(ρ) = δ + B(ρ)·ρ^{ω·k+n} + 1`. -/
theorem xtLL_reachB1 (k n : ℕ) :
    IsReach R2C (upsilon (xtB1 ((xtLL k).iter n).sys))
      (upsilon (xtB1 ((xtLL k).iter n).sys + ω + 1) +
        (VzB (upsilon (xtB1 ((xtLL k).iter n).sys)) *
          upsilon (xtB1 ((xtLL k).iter n).sys) ^ (ω * (k : Ordinal.{0}) + (n : Ordinal.{0})) + 1)) := by
  rw [← xtLL_iter_top]; exact ((xtLL k).iter n).reachB1

/-- `xtLayN n` is the `n`-th next layer of `vzLay`. -/
theorem xtLayN_eq_iter : ∀ n, xtLayN n = vzLay.iter n
  | 0 => rfl
  | n + 1 => by
    show (xtLayN n).xtNext = (vzLay.iter n).xtNext
    rw [xtLayN_eq_iter n]

/-- **`Λ_ω < Λ_{ω²}`.** -/
theorem xtW_lt_W2 : xtFamW.famSup < xtFamW2.famSup := by
  refine lt_of_le_of_lt (Ordinal.iSup_le fun n => ?_) (xtFamW2.famBd_lt 1)
  show xtLamN n ≤ xtLamK 1
  have h := (xtLL 0).lim_gt n
  have e : xtLamN n = xtB1 ((xtLL 0).iter n).sys := by
    show xtB1 (xtLayN n).sys = xtB1 (vzLay.iter n).sys
    rw [xtLayN_eq_iter]
  rw [e]
  exact (h.trans (xtLL 0).xtLim.xtLamLt).le

variable {S : InaccSeq.{0}}

/-- **The hypotheses of `xtFamW2.famRoad3` follow from those of `cpRoad3`.** -/
theorem xtW2_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdLower S l) ∧ xtFamW2.famTHfix S := by
  have hc0 : Cp.cpB1 ≤ xtFamW2.famSup := by
    have := xtFamW2.famBd_lt 0
    exact (show xtLamK 0 < xtFamW2.famSup from this).le.trans_eq' xtLamK_zero.symm
  refine xtFamW2.famOf_cp hc0 (fun k μ hμ h1 _ => ?_) hU hL hT
  have h0 : μ < xtLamK 0 := xtLamK_zero ▸ h1
  show xtOrec (xtLL k).sys μ = VzOrec μ
  rw [xtLL_eq (Nat.zero_le k) hμ h0]
  show xtOrec vzSys μ = VzOrec μ
  rw [xtVz_orec]

/-! ## The instances of `R2.XtFam` for `Λ_{ω²}` -/

/-- **Theorem BLK^O below `υ_{Λ_{ω²}}`** in `R₂^C`. -/
theorem xtW2_blk :
    (∀ c d, c < d → d < upsilon xtFamW2.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtFamW2.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtLamK k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (xtLL k).sys l)) ∧
    (∀ α < upsilon xtFamW2.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtFamW2.famBlk

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ω²} ≤ L < ξ`. -/
theorem xtW2_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ xtFamW2.famSup ≤ L ∧ L < ξ ∧
    upsilon xtFamW2.famSup ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC :=
  xtFamW2.famNuC

/-- **UPPER and LOWER at every restart of the range below `Λ_{ω²}` that is not a fixed point of `υ`.** -/
theorem xtW2_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtFamW2.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtFamW2.famInit hr hl hfix

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ_{ω²}`**, `Θ_F(m_F) = O_{LL k}(F)` at the fixed points
`F < Λ⁺_k` of the range, the cap of the values outside `Λ_{ω²}`, (CL), EQ, TCrest, (EMB₂). -/
theorem xtW2Road3 (hU : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtFamW2.famSup ≤ l → CdLower S l) (hT : xtFamW2.famTHfix S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut xtFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtFamW2.famRoad3 hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ_{ω²}`.** -/
theorem xtW2Road (hU : ∀ l, CdRange S l → XtOut xtFamW2.famSup l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut xtFamW2.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut xtFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtFamW2.famRoad hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ_{ω²}`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem xtW2Road_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut xtFamW2.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut xtFamW2.famSup l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtFamW2.famRoad_cap h0 h1 hC hTC hB2

/-- **The road with UPPER asked only at `λ ≥ Λ_{ω²}` and at the non-isolated fixed points** (the code `F ≤ m_F` at
the isolated fixed points below `Λ_{ω²}`), LOWER and the cap of the values outside, (CL), EQ, TCrest, (EMB₂). -/
theorem xtW2Road2 (hU : ∀ l, CdRange S l → (xtFamW2.famSup ≤ l ∨ (upsilon l = l ∧ ¬ CpIso l)) → CdUpper S l)
    (hc : ∀ l, CdRange S l → l < xtFamW2.famSup → upsilon l = l → CpIso l → l ≤ cdCode S l)
    (hL : ∀ l, CdRange S l → XtOut xtFamW2.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut xtFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtFamW2.famRoad2 xtFamW2_iso hU hc hL hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Xt
