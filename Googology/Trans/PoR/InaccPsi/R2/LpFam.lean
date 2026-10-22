import Googology.Trans.PoR.InaccPsi.R2.LpSys

/-!
# The whole tower over the base: the family `lpSys B n`, `n < ω`, and its supremum `Λ^B = sup_n Λ⁺(lpSys B n)`

For every base package `B` (a layer `K` with an `ε`-number top `E_K(x) ∈ Tˣ`) the stage systems `lpSys B n` of
`R2.LpSys` (tops `gP B n`: `E_K`, `ϑˣ(Ω₁·E_K)`, `ϑˣ(Ω₁·ϑˣ(Ω₁·E_K))`, …) form an increasing family of offset
specifications (`R2.XtFam`):

* `lpLam B n = Λ⁺(lpSys B n)`, `lpLam_lt`, `lp_eq_le` (**`O_m = O_n` below `Λ⁺(lpSys B n)` for `n ≤ m`**),
  `lpFam B : XtFam`, `lpFam_gt_K` (**`Λ⁺(K) < Λ^B`**);
* `lpFam_blk` (**Theorem BLK^O below `υ_{Λ^B}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O_n(λ)`), `lpFam_init`
  (**ENUM-REACH at every non-fixed restart of the range below `Λ^B`**), `lpFam_capV` (**CapV there**),
  `lpFamEnum` (**ENUM-REACH at every restart of the range below `Λ^B`, fixed points included, given the notation
  hypothesis `Θ_F(m_F) = O(F)` at the fixed points**), `lpFamRoad3` (the successor road: UPPER/LOWER asked only at
  `λ ≥ Λ^B`, the notation hypothesis only at the fixed points below `Λ^B`, CapV only at the outer restarts).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

variable (B : LpB)

/-- `Λ⁺(lpSys B n)`. -/
noncomputable def lpLam (n : ℕ) : Ordinal.{0} := xtB1 (lpSys B n)

theorem lpLam_lt (n : ℕ) : lpLam B n < lpLam B (n + 1) :=
  (lpLam_gt n).trans (lp_lamLtB1 (n + 1))

theorem lpLam_strictMono : StrictMono (lpLam B) := strictMono_nat_of_lt_succ (lpLam_lt B)

/-- `O_{lpSys B m} = O_{lpSys B n}` below `Λ⁺(lpSys B n)` for `n ≤ m`. -/
theorem lp_eq_le {n m : ℕ} (h : n ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμn : μ < lpLam B n) :
    xtOrec (lpSys B m) μ = xtOrec (lpSys B n) μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact lp_eq m hμ (hμn.trans_le ((lpLam_strictMono B).monotone hnm))

/-- **The family of the stage systems over the base**: bounds `Λ⁺(lpSys B n)`, offsets `O_{lpSys B n}`. -/
noncomputable def lpFam : XtFam where
  bd := lpLam B
  off := fun n => xtOrec (lpSys B n)
  spec := fun n => xtSpec1 (lpSys_topPkg n)
  mono := lpLam_lt B
  nonfix := fun n => lp_nonfix n

/-- **`Λ⁺(K) < Λ^B`.** -/
theorem lpFam_gt_K : xtB1 B.K.sys < (lpFam B).famSup :=
  (lpB1_gt_K (B := B) 0).trans ((lpFam B).famBd_lt 1)

/-- **Theorem BLK^O below `υ_{Λ^B}`** in `R₂^C`, with the exact reaches. -/
theorem lpFam_blk :
    (∀ c d, c < d → d < upsilon (lpFam B).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (lpFam B).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lpLam B k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lpSys B k) l)) ∧
    (∀ α < upsilon (lpFam B).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  (lpFam B).famBlk

variable {S : InaccSeq.{0}}

/-- **ENUM-REACH at every non-fixed restart of the range below `Λ^B`.** -/
theorem lpFam_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  (lpFam B).famInit hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ^B`.** -/
theorem lpFam_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  (lpFam B).famCapV hr hl hfix

/-- **ENUM-REACH at every restart of the range below `Λ^B`**, fixed points included, given the notation hypothesis
`Θ_F(m_F) = O_n(F)` at the fixed points below each `Λ⁺(lpSys B n)`. -/
theorem lpFamEnum (hT : ∀ n l, CdRange S l → l < lpLam B n → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l)
    {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < (lpFam B).famSup) : CdUpper S l ∧ CdLower S l := by
  obtain ⟨n, hn⟩ := (lpFam B).famLt hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hfix | hfix
  · exact lp_init n hr hn hfix
  · exact (lp_iff n hr.1 hn).2 (hT n l hr hn hfix.symm)

/-- **The successor road over the base**: UPPER and LOWER asked only at `λ ≥ Λ^B`, the notation hypothesis only at
the fixed points below `Λ^B`, the cap of the values only at the outer restarts, (CL), EQ, TCrest, (EMB₂). -/
theorem lpFamRoad3 (hU : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → (lpFam B).famSup ≤ l → CdLower S l)
    (hT : ∀ n l, CdRange S l → l < lpLam B n → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lpSys B n) l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (lpFam B).famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  (lpFam B).famRoad3 hU hL (fun n _ hr hln hfix => hT n _ hr hln hfix) hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2.Lp
