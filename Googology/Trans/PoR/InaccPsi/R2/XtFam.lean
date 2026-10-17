import Googology.Trans.PoR.InaccPsi.R2.XtEnum

/-!
# An increasing family of offset specifications: BLK^O and the road below the supremum

A family `F : XtFam` is a sequence of bounds `Λ_k` (strictly increasing) with general offset specifications
`OffSpecGen (O_k) (Λ_k)` (`R2.BlkGen`) and `O_k(μ) = -1 + e(μ)` off the fixed points of `υ` (`XtNonfix`).  With
`Λ = sup_k Λ_k` (`F.famSup`):

* `F.famBlk` (**Theorem BLK^O below `υ_Λ`**: the `<₂`-pairs, the blocks and the exact reaches `lh(ρ_λ) = δ_λ + O_k(λ)`
  for `λ < Λ_k`, `≤₁` of `R₁⁺` off the `υ`-points), `F.famCore`, `F.famNuC` (`υ_Λ ≤ ρ_L < ν_C`), `F.famSup_lt_Om1`;
* `F.famInit` (**UPPER and LOWER at every restart of the range below `Λ` that is not a fixed point of `υ`**),
  `F.famCapV`, `F.famCapAt`, `F.famIff` (below `Λ_k`, ENUM-REACH is `Θ_λ(m_λ) = O_k(λ)`);
* the roads of `R2.CdNu` with the rest asked only outside `Λ` (`Λ ≤ λ` or `υ_λ = λ`): `F.famRoad`, `F.famRoad_cap`,
  `F.famLow`, `F.famRoad3` (UPPER, LOWER at `λ ≥ Λ` and `Θ_F(m_F) = O_k(F)` at the fixed points `F < Λ_k`), `F.famRoad2`
  (the code `F ≤ m_F` at the isolated fixed points), `F.famOf_cp` (the hypotheses of `F.famRoad3` from those of
  `cpRoad3`, when `O_k = VzOrec` below `cpB1 ≤ Λ`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

/-- **An increasing family of offset specifications.** -/
structure XtFam where
  bd : ℕ → Ordinal.{0}
  off : ℕ → Ordinal.{0} → Ordinal.{0}
  spec : ∀ k, OffSpecGen (off k) (bd k)
  mono : ∀ k, bd k < bd (k + 1)
  nonfix : ∀ k, XtNonfix (off k) (bd k)

namespace XtFam

variable (F : XtFam)

/-- The supremum of the bounds. -/
noncomputable def famSup : Ordinal.{0} := ⨆ k : ℕ, F.bd k

theorem famBd_lt (k : ℕ) : F.bd k < F.famSup := (F.mono k).trans_le (Ordinal.le_iSup _ (k + 1))

theorem famSup_lt_Om1 : F.famSup < Om1 := Ordinal.iSup_lt_omega_one (fun k => (F.spec k).cnt)

theorem famLt {l : Ordinal.{0}} (h : l < F.famSup) : ∃ k, l < F.bd k := Ordinal.lt_iSup_iff.1 h

theorem famSup_limit : IsSuccLimit F.famSup := by
  refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le (F.famBd_lt 0)).ne', ?_⟩
  refine isSuccPrelimit_of_succ_lt (fun a ha => ?_)
  obtain ⟨k, hk⟩ := F.famLt ha
  exact (Order.succ_le_of_lt hk).trans_lt (F.famBd_lt k)

theorem famUps_lt {d : Ordinal.{0}} (hd : d < upsilon F.famSup) : ∃ k, d < upsilon (F.bd k) := by
  obtain ⟨_, ⟨ν, hν, rfl⟩, hdν⟩ := (lt_isLUB_iff (upsilon_limit F.famSup_limit)).1 hd
  obtain ⟨k, hk⟩ := F.famLt hν
  exact ⟨k, hdν.trans (upsilon_normal.strictMono hk)⟩

/-- **Theorem BLK^O below `υ_Λ`**, `Λ = sup_k Λ_k`. -/
theorem famBlk :
    (∀ c d, c < d → d < upsilon F.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < F.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < F.bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + F.off k l)) ∧
    (∀ α < upsilon F.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  refine ⟨fun c d hcd hd => ?_, fun l hl k hlk => (blk_genGen (F.spec k)).2.1 l hl hlk,
    fun α hα hU γ => ?_⟩
  · obtain ⟨k, hk⟩ := F.famUps_lt hd
    rw [(blk_genGen (F.spec k)).1 c d hcd hk]
    constructor
    · rintro ⟨μ, j, h1, h2, h3, h4⟩
      exact ⟨μ, j, h1, h2.trans (F.famBd_lt k), h3, h4⟩
    · rintro ⟨μ, j, h1, -, h3, h4⟩
      refine ⟨μ, j, h1, ?_, h3, h4⟩
      have : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < F.bd k :=
        upsilon_normal.strictMono.lt_iff_lt.1 (h4 ▸ hk)
      exact lt_of_le_of_lt (le_self_add.trans le_self_add) this
  · obtain ⟨k, hk⟩ := F.famUps_lt hα
    exact (blk_genGen (F.spec k)).2.2 α hk hU γ

theorem famCore : Set.Iio (upsilon F.famSup) ⊆ Core R2C := fun x hx => by
  obtain ⟨k, hk⟩ := F.famUps_lt hx
  exact core_genGen (F.spec k) hk

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ ≤ L < ξ` restart indices. -/
theorem famNuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ F.famSup ≤ L ∧ L < ξ ∧
    upsilon F.famSup ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle : F.famSup ≤ L := Ordinal.iSup_le (fun k => left_ge_of_spec (F.spec k) hL hLν h2)
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, h2⟩

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ` that is not a fixed point of `υ`.** -/
theorem famInit {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < F.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, hk⟩ := F.famLt hl
  exact xtInit (F.spec k) (F.nonfix k) hr hk hfix

theorem famCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < F.famSup) (hfix : l < upsilon l) :
    CdCapV S l := by
  obtain ⟨k, hk⟩ := F.famLt hl
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (F.spec k) hr.1 hww hfix hk (cp_name_L hr.2.2.1) (F.nonfix k l hr.1 hww hfix hk)

theorem famCapAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < F.famSup)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  obtain ⟨k, hk⟩ := F.famLt hlΛ
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (F.spec k) hl hww hfix hk hname (F.nonfix k l hl hww hfix hk)

/-- **Below `Λ_k`, ENUM-REACH is the equation `Θ_λ(m_λ) = O_k(λ)`.** -/
theorem famIff (k : ℕ) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlk : l < F.bd k) :
    (CdUpper S l ↔ F.off k l ≤ cdTheta S l (cdCode S l)) ∧
      (CdLower S l ↔ cdTheta S l (cdCode S l) ≤ F.off k l) ∧
      (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = F.off k l) :=
  ⟨xtUpper_iff (F.spec k) hl hlk, xtLower_iff (F.spec k) hl hlk, xtExact_iff (F.spec k) hl hlk⟩

theorem famUPPER (hU : ∀ l, CdRange S l → XtOut F.famSup l → CdUpper S l) : CdUPPER S := fun l hr => by
  rcases xtOut_or F.famSup l with h | ⟨hl, hfix⟩
  · exact hU l hr h
  · exact (F.famInit hr hl hfix).1

theorem famLOWER (hL : ∀ l, CdRange S l → XtOut F.famSup l → CdLower S l) : CdLOWER S := fun l hr => by
  rcases xtOut_or F.famSup l with h | ⟨hl, hfix⟩
  · exact hL l hr h
  · exact (F.famInit hr hl hfix).2

theorem famCapVAll (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut F.famSup l → CdCapV S l) :
    ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → CdCapV S l := fun l hr hX => by
  rcases xtOut_or F.famSup l with h | ⟨hl, hfix⟩
  · exact hV l hr hX h
  · exact F.famCapV hr hl hfix

theorem famCAP0 (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut F.famSup l → CdCapAt S l) :
    CdCAP0 S := fun l hl hB hlev => by
  rcases xtOut_or F.famSup l with h | ⟨hlΛ, hfix⟩
  · exact h0 l hl hB hlev h
  · exact F.famCapAt hl hB hlΛ hfix hlev

theorem famCAP1 (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut F.famSup l → CdCapAt S l) :
    CdCAP1 S (Nc.ncL S ω) := fun l hl hB hlev hX hc => by
  rcases xtOut_or F.famSup l with h | ⟨hlΛ, hfix⟩
  · exact h1 l hl hB hlev hX hc h
  · exact F.famCapAt hl hB hlΛ hfix (Lw.lw_L_eq S ω ▸ hX)

/-- **NU-LOW″ from the caps outside `Λ`**: `L(ω) ≤ ν_C`. -/
theorem famLow (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut F.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut F.famSup l → CdCapAt S l) : Nc.ncL S ω ≤ nuC :=
  cdLow (F.famCAP0 h0) (F.famCAP1 h1)

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ`.** -/
theorem famRoad (hU : ∀ l, CdRange S l → XtOut F.famSup l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut F.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut F.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (F.famUPPER hU) (F.famLOWER hL) (F.famCapVAll hV) hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ`**: CAP-0, CAP-1 outside `Λ`, (CL), (TC), (EMB₂). -/
theorem famRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut F.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut F.famSup l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad_cap (F.famCAP0 h0) (F.famCAP1 h1) hC hTC hB2

/-- The notation at the fixed points below `Λ`: `Θ_F(m_F) = O_k(F)` for `F < Λ_k`. -/
def famTHfix (S : InaccSeq.{0}) : Prop :=
  ∀ k : ℕ, ∀ l, CdRange S l → l < F.bd k → upsilon l = l → cdTheta S l (cdCode S l) = F.off k l

theorem famUPPER3 (hU : ∀ l, CdRange S l → F.famSup ≤ l → CdUpper S l) (hT : F.famTHfix S) : CdUPPER S :=
  fun l hr => by
  rcases le_or_gt F.famSup l with hB | hl
  · exact hU l hr hB
  · rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hfix | hfix
    · exact (F.famInit hr hl hfix).1
    · obtain ⟨k, hk⟩ := F.famLt hl
      exact ((F.famIff k hr.1 hk).2.2.2 (hT k l hr hk hfix.symm)).1

theorem famLOWER3 (hL : ∀ l, CdRange S l → F.famSup ≤ l → CdLower S l) (hT : F.famTHfix S) : CdLOWER S :=
  fun l hr => by
  rcases le_or_gt F.famSup l with hB | hl
  · exact hL l hr hB
  · rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hfix | hfix
    · exact (F.famInit hr hl hfix).2
    · obtain ⟨k, hk⟩ := F.famLt hl
      exact ((F.famIff k hr.1 hk).2.2.2 (hT k l hr hk hfix.symm)).2

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ`** and `Θ_F(m_F) = O_k(F)` at the fixed points `F < Λ_k`,
the cap of the values outside `Λ`, (CL), EQ, TCrest, (EMB₂). -/
theorem famRoad3 (hU : ∀ l, CdRange S l → F.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → F.famSup ≤ l → CdLower S l) (hT : F.famTHfix S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut F.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (F.famUPPER3 hU hT) (F.famLOWER3 hL hT) (F.famCapVAll hV) hC hEQ hrest hB2

/-- The offset at an isolated fixed point is `F` in every member of the family whose bound is above `F`. -/
def famIsoOff : Prop :=
  ∀ k l, IsRestartIdx l → l < F.bd k → upsilon l = l → CpIso l → F.off k l = l

theorem famUPPER2 (hI : F.famIsoOff)
    (hU : ∀ l, CdRange S l → (F.famSup ≤ l ∨ (upsilon l = l ∧ ¬ CpIso l)) → CdUpper S l)
    (hc : ∀ l, CdRange S l → l < F.famSup → upsilon l = l → CpIso l → l ≤ cdCode S l) : CdUPPER S :=
  fun l hr => by
  rcases xtOut_or F.famSup l with (h | h) | ⟨hl, hfix⟩
  · exact hU l hr (Or.inl h)
  · by_cases hiso : CpIso l
    · rcases le_or_gt F.famSup l with hB | hl
      · exact hU l hr (Or.inl hB)
      · obtain ⟨k, hk⟩ := F.famLt hl
        exact (xtFix_code (F.spec k) hr.1 h hk (hI k l hr.1 hk h hiso) (cp_name_L hr.2.2.1)).1
          (hc l hr hl h hiso)
    · exact hU l hr (Or.inr ⟨h, hiso⟩)
  · exact (F.famInit hr hl hfix).1

/-- **The road with UPPER asked only at `λ ≥ Λ` and at the non-isolated fixed points** (the code at the isolated
fixed points below `Λ`), LOWER and the cap of the values outside `Λ`, (CL), EQ, TCrest, (EMB₂). -/
theorem famRoad2 (hI : F.famIsoOff)
    (hU : ∀ l, CdRange S l → (F.famSup ≤ l ∨ (upsilon l = l ∧ ¬ CpIso l)) → CdUpper S l)
    (hc : ∀ l, CdRange S l → l < F.famSup → upsilon l = l → CpIso l → l ≤ cdCode S l)
    (hL : ∀ l, CdRange S l → XtOut F.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut F.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  cdRoad (F.famUPPER2 hI hU hc) (F.famLOWER hL) (F.famCapVAll hV) hC hEQ hrest hB2

/-- **The hypotheses of `F.famRoad3` from those of `cpRoad3`**, when `cpB1 ≤ Λ` and `O_k = VzOrec` below `cpB1`. -/
theorem famOf_cp (hcp : Cp.cpB1 ≤ F.famSup)
    (heq : ∀ k μ, IsRestartIdx μ → μ < Cp.cpB1 → μ < F.bd k → F.off k μ = VzOrec μ)
    (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → F.famSup ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → F.famSup ≤ l → CdLower S l) ∧
      F.famTHfix S := by
  refine ⟨fun l hr h => hU l hr (hcp.trans h), fun l hr h => hL l hr (hcp.trans h),
    fun k l hr hlk hfix => ?_⟩
  rcases lt_or_ge l Cp.cpB1 with h | h
  · rw [heq k l hr.1 h hlk]; exact hT l hr h hfix
  · exact (F.famIff k hr.1 hlk).2.2.1 ⟨hU l hr h, hL l hr h⟩

end XtFam

end Googology.Trans.PoR.InaccPsi.R2.Xt
