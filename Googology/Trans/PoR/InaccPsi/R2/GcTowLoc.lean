import Googology.Trans.PoR.InaccPsi.R2.GcTow

/-!
# The transfinite tower located against `L(0)`: every constant offset at once, up to `ι(Γ_{Ω₁+ε₀})`

With THE UNIFORMITY THEOREM `gcB_codes` (`R2.GcTow`), THEOREM UNI `gcUniTh` (`R2.GcUni`) and the frontier lemma
`gcB1_eq` (`R2.GcFr`), for every `α` with `1 + α < ε₀` (`c_α := gcG (1 + α) = Γ_{Ω₁+2+α}`):

* `gcB_loc` (**`Λ⁺(gcB α) = ι(c_α·ω)`, `ρ` of it `= P(c_α·ω) < L(0)`**), `gcLad_loc` (**`Λ⁺(lpSys (gcB α) n) =
  ι(cQ c_α n·ω)`**), `gcBFam_loc` (**`Λ^{gcB α} = ι(c_{α+1})`**), `gcLimSup_loc` (**at a limit `α ≤ ε₀`:
  `sup_{β<α} Λ⁺(gcB β) = ι(gcG α) = ι(Γ_{Ω₁+α})`**);
* `gcSeq` (`ω^ω^…^0`, cofinal in `ε₀`), `gcFam : XtFam` (bounds `Λ⁺(gcB (gcSeq n))`), `gcFamSup`
  (**`sup = ι(Γ_{Ω₁+ε₀})`, `υ` of it `= P(Γ_{Ω₁+ε₀}) < L(0)`**);
* `gcBT_fix` (**the notation hypothesis `Θ_F(m_F) = O(F)` at every fixed point of the range below `Λ⁺(gcB α)`**),
  `gcBlk` (**BLK^O and the exact reaches below `P(Γ_{Ω₁+ε₀})`**), `gcEnum` / `gcCapV` (**ENUM-REACH and CapV at every
  restart of the range below `ι(Γ_{Ω₁+ε₀})`, fixed points included**), `gcRoad` (UPPER, LOWER, CapV asked only at
  `λ ≥ ι(Γ_{Ω₁+ε₀})`), `gc_fr_order` (**the order of the new frontiers and of `L(0) = m* ≤ L(k+1) < L(ω) <
  L(ω+1)`**), `gc_beyond_gb` (**`ι(Γ_{Ω₁+ω·2}) < ι(Γ_{Ω₁+ε₀})`**: past the frontier of `R2.GbWLoc`).

No new axiom.  New definitions: `gcSeq`, `gcFam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga

variable {S : InaccSeq.{0}}

/-! ## One base -/

section One

variable (S) {α : Ordinal.{0}} (h : 1 + α < ε₀)
include S h

theorem gcB_hc : ∀ Z, SC Z → GxCl Z gcAt (gcG (1 + α)) := fun _ _ => GxCl.atom (gcG_atom h)

theorem gcB_hcO : Om 1 ≤ gcG (1 + α) := (gcG_Om1_lt _).le

theorem gcB_hcE : ω ^ gcG (1 + α) = gcG (1 + α) := gg_SC_eps (gcG_SC _)

theorem gcB_htop {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) :
    (gcB α).K.sys.top y = gxTh y gcAt (gcG (1 + α)) := by
  rw [gcB_top h (gg_SC_eps hy) (lp_y1 hy1), ← gcB_E h (gg_SC_eps hy) (lp_y1 hy1)]
  exact (gcB_codes S α h).1 y hy hy1

/-- **`Λ⁺(gcB α) = ι(Γ_{Ω₁+2+α}·ω)`, `ρ` of it `= P(Γ_{Ω₁+2+α}·ω) < L(0)`.** -/
theorem gcB_loc : xtB1 (gcB α).K.sys = iota S (gcG (1 + α) * ω) ∧
    upsilon (xtB1 (gcB α).K.sys) = Pv S (gcG (1 + α) * ω) ∧ Pv S (gcG (1 + α) * ω) < Nc.ncL S 0 := by
  have e := gcB1_eq (S := S) (X := (gcB α).K.sys) (T := gcG (1 + α)) (gc_one_add_le_eps h)
    (gcB_codes S α h).2 (fun y hy hy1 => gcB_htop S h hy hy1) (gcB_hc S h) (gcB_hcO S h)
    (fun x hx hx1 => by rw [(gcB α).K.top_eq x hx hx1, (gcB α).ek x hx hx1]; exact gcB_eN h hx hx1)
    (XtLay.topPkg (gcB α).K)
  rwa [gcB_hcE S h] at e

/-- **`Λ⁺(lpSys (gcB α) n) = ι(cQ (Γ_{Ω₁+2+α}) n·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem gcLad_loc (n : ℕ) : xtB1 (lpSys (gcB α) n) = iota S (cQ (gcG (1 + α)) n * ω) ∧
    upsilon (xtB1 (lpSys (gcB α) n)) = Pv S (cQ (gcG (1 + α)) n * ω) ∧
    Pv S (cQ (gcG (1 + α)) n * ω) < Nc.ncL S 0 :=
  gcB1_loc S (B := gcB α) (gcB_hc S h) (gcB_hcO S h) (gcB_hcE S h) (gcB_codes S α h).1 (gcB_codes S α h).2
    (fun _ hx hx1 => gcB_eN h hx hx1) n

/-- **`Λ^{gcB α} = sup_n Λ⁺(lpSys (gcB α) n) = ι(Γ_{Ω₁+2+α+1})`, `υ` of it `= P(…) < L(0)`.** -/
theorem gcBFam_loc : (lpFam (gcB α)).famSup = iota S (gcG (1 + α + 1)) ∧
    upsilon (lpFam (gcB α)).famSup = Pv S (gcG (1 + α + 1)) ∧ Pv S (gcG (1 + α + 1)) < Nc.ncL S 0 := by
  have e := gcFam_loc S (B := gcB α) (gcB_hc S h) (gcB_hcO S h) (gcB_hcE S h) (gcB_codes S α h).1
    (gcB_codes S α h).2 (fun _ hx hx1 => gcB_eN h hx hx1)
  rwa [gc_cQs] at e

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(gcB α)`** (THEOREM UNI). -/
theorem gcBT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (gcB α).K.sys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (gcB α).K.sys l := by
  have hlt : l < iota S (ω ^ gcG (1 + α) * ω) := by
    rw [gcB_hcE S h, ← (gcB_loc S h).1]; exact hl
  exact gcUniTh (gc_one_add_le_eps h) (gcB_codes S α h).2 hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

end One

/-- **At a limit `α ≤ ε₀`: `sup_{β<α} Λ⁺(gcB β) = ι(Γ_{Ω₁+α})`.** -/
theorem gcLimSup_loc {α : Ordinal.{0}} (hα : IsSuccLimit α) (hαε : α ≤ ε₀) :
    (⨆ β : Iio α, xtB1 (gcB β.1).K.sys) = iota S (gcG α) := by
  have hβε : ∀ β < α, 1 + β < ε₀ := fun β hβ => (gc_one_add_lt hα hβ).trans_le hαε
  have hSC := gcG_SC α
  have hEs : ω ^ gcG α = gcG α := gg_SC_eps hSC
  have hstep : ∀ β < α, gcG (1 + β) * ω < gcG α := fun β hβ =>
    InE.mul_lt hEs (gcG_lt (gc_one_add_lt hα hβ)) (omega0_lt_inE hEs)
  have hbdd : BddAbove (range fun β : Iio α => xtB1 (gcB β.1).K.sys) := Ordinal.bddAbove_of_small
  refine le_antisymm (ciSup_le' fun β => ?_) ?_
  · rw [(gcB_loc S (hβε β.1 β.2)).1]
    exact iota_mono _ _ (hstep β.1 β.2).le
  · rw [iota_limit hSC.isSuccLimit]
    refine ciSup_le' fun e => ?_
    obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hα e.2
    have h1 : e.1 < gcG (1 + β) * ω :=
      (heβ.trans_le (gcG_le le_add_self)).trans_le (le_mul_of_one_le_right zero_le one_lt_omega0.le)
    calc iota S e.1 ≤ iota S (gcG (1 + β) * ω) := iota_mono _ _ h1.le
      _ = xtB1 (gcB β).K.sys := (gcB_loc S (hβε β hβ)).1.symm
      _ ≤ ⨆ β : Iio α, xtB1 (gcB β.1).K.sys := le_ciSup hbdd ⟨β, hβ⟩

/-! ## The whole tower as a family -/

/-- `ω^ω^…^0` (`n + 1` exponentials): cofinal in `ε₀`. -/
noncomputable def gcSeq (n : ℕ) : Ordinal.{0} := (fun a : Ordinal.{0} => ω ^ a)^[n + 1] 0

theorem gcSeq_lt (n : ℕ) : gcSeq n < ε₀ := iterate_omega0_opow_lt_epsilon_zero (n + 1)

theorem gcSeq_one_add (n : ℕ) : 1 + gcSeq n < ε₀ := (gc_one_add_lt gc_eps0_lim (gcSeq_lt n))

theorem gc_lt_opow_of_lt_eps {a : Ordinal.{0}} (h : a < ε₀) : a < ω ^ a :=
  lt_of_le_of_ne (right_le_opow _ one_lt_omega0) fun e =>
    absurd (epsilon_zero_le_of_omega0_opow_le e.symm.le) (not_le.2 h)

theorem gcSeq_succ (n : ℕ) : gcSeq (n + 1) = ω ^ gcSeq n := by
  unfold gcSeq
  rw [Function.iterate_succ_apply']

theorem gcSeq_lt_succ (n : ℕ) : gcSeq n < gcSeq (n + 1) := by
  rw [gcSeq_succ]; exact gc_lt_opow_of_lt_eps (gcSeq_lt n)

theorem gcSeq_mono : StrictMono gcSeq := strictMono_nat_of_lt_succ gcSeq_lt_succ

theorem gc_iter_le (n : ℕ) : (fun a : Ordinal.{0} => ω ^ a)^[n] 0 ≤ gcSeq n := by
  unfold gcSeq
  rw [Function.iterate_succ_apply']
  exact right_le_opow _ one_lt_omega0

theorem gcSeq_cof {β : Ordinal.{0}} (h : β < ε₀) : ∃ n, β < gcSeq n := by
  obtain ⟨n, hn⟩ := lt_epsilon_zero.1 h
  exact ⟨n, hn.trans_le (gc_iter_le n)⟩

/-- **The whole tower as a family**: bounds `Λ⁺(gcB (gcSeq n))`. -/
noncomputable def gcFam : XtFam where
  bd := fun n => xtB1 (gcB (gcSeq n)).K.sys
  off := fun n => xtOrec (gcB (gcSeq n)).K.sys
  spec := fun n => xtSpec1 (XtLay.topPkg (gcB (gcSeq n)).K)
  mono := fun n => gcB1_lt (gcSeq_one_add (n + 1)) (gcSeq_lt_succ n)
  nonfix := fun n _ hμ hww hfix hμB =>
    xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (XtLay.topPkg (gcB (gcSeq n)).K)))

/-- **`sup_n Λ⁺(gcB (gcSeq n)) = ι(Γ_{Ω₁+ε₀})`, `υ` of it `= P(Γ_{Ω₁+ε₀}) < L(0)`.** -/
theorem gcFamSup : gcFam.famSup = iota S gcV ∧ upsilon gcFam.famSup = Pv S gcV ∧ Pv S gcV < Nc.ncL S 0 := by
  have hSC := gcV_SC
  have hEs : ω ^ gcV = gcV := gg_SC_eps hSC
  have heq : gcFam.famSup = iota S gcV := by
    refine le_antisymm (Ordinal.iSup_le fun n => ?_) ?_
    · show xtB1 (gcB (gcSeq n)).K.sys ≤ _
      rw [(gcB_loc S (gcSeq_one_add n)).1]
      exact iota_mono _ _ (InE.mul_lt hEs (gcG_lt_V (gcSeq_one_add n)) (omega0_lt_inE hEs)).le
    · rw [iota_limit hSC.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit gc_eps0_lim e.2
      obtain ⟨n, hn⟩ := gcSeq_cof hβ
      have h1 : e.1 < gcG (1 + gcSeq n) * ω :=
        ((heβ.trans (gcG_lt hn)).trans_le (gcG_le le_add_self)).trans_le
          (le_mul_of_one_le_right zero_le one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (1 + gcSeq n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (gcB (gcSeq n)).K.sys := (gcB_loc S (gcSeq_one_add n)).1.symm
        _ ≤ gcFam.famSup := (gcFam.famBd_lt n).le
  have hups : upsilon gcFam.famSup = Pv S gcV := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gcV_lt_Om2 S).le⟩

/-- **Every `Λ⁺(gcB α)` (`1 + α < ε₀`) is below `ι(Γ_{Ω₁+ε₀})`.** -/
theorem gcB1_lt_sup {α : Ordinal.{0}} (h : 1 + α < ε₀) : xtB1 (gcB α).K.sys < iota S gcV := by
  have hEs : ω ^ gcV = gcV := gg_SC_eps gcV_SC
  rw [(gcB_loc S h).1]
  refine cd_iota_lt_of_good (gc_good fun Z hZ => ?_) (InE.mul_lt hEs (gcG_lt_V h) (omega0_lt_inE hEs))
  have e : gcG (1 + α) * ω = ω ^ (gcG (1 + α) + 1) := by
    rw [opow_add, opow_one, gcB_hcE S h]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (gcB_hc S h Z hZ) (GxCl.small (gg_one_lt_of_SC hZ)))

/-- **Theorem BLK^O below `υ(ι(Γ_{Ω₁+ε₀})) = P(Γ_{Ω₁+ε₀})`** in `R₂^C`, with the exact reaches. -/
theorem gcBlk :
    (∀ c d, c < d → d < upsilon gcFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < gcFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtB1 (gcB (gcSeq k)).K.sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (gcB (gcSeq k)).K.sys l)) ∧
    (∀ α < upsilon gcFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  gcFam.famBlk

/-- **The exact reach at every restart below `Λ⁺(gcB α)`**, for every `α` with `1 + α < ε₀`:
`lh(ρ_λ) = δ_λ + O_{gcB α}(λ)`. -/
theorem gcReach {α : Ordinal.{0}} (h : 1 + α < ε₀) {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hlα : l < xtB1 (gcB α).K.sys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (gcB α).K.sys l) := by
  obtain ⟨n, hn⟩ := gcSeq_cof (lt_of_le_of_lt le_add_self h)
  have hαn : α ≤ gcSeq n := hn.le
  have hln : l < xtB1 (gcB (gcSeq n)).K.sys := by
    rcases hαn.lt_or_eq with hlt | heq
    · exact hlα.trans (gcB1_lt (gcSeq_one_add n) hlt)
    · rw [← heq]; exact hlα
  have e := gcB_eq (gcSeq_one_add n) hαn hl hlα
  rw [← e]
  exact ((gcBlk.2.1 l hl n hln).2.2)

/-- **ENUM-REACH at every restart of the range below `ι(Γ_{Ω₁+ε₀})`**, fixed points included. -/
theorem gcEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gcV) : CdUpper S l ∧ CdLower S l := by
  rw [← (gcFamSup (S := S)).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact gcFam.famInit hr hl hnf
  · obtain ⟨k, hk⟩ := gcFam.famLt hl
    exact (gcFam.famIff k hr.1 hk).2.2.2 (gcBT_fix S (gcSeq_one_add k) hr hk hfx.symm)

/-- **CapV at every restart of the range below `ι(Γ_{Ω₁+ε₀})`**, fixed points included. -/
theorem gcCapV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gcV) : CdCapV S l := by
  have hl' := hl
  rw [← (gcFamSup (S := S)).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact gcFam.famCapV hr hl' hnf
  · obtain ⟨k, hk⟩ := gcFam.famLt hl'
    exact Lk.lkCapV_fix (XtLay.topPkg (gcB (gcSeq k)).K) hr hk hfx.symm (gcEnum hr hl)

/-- **The successor road past every constant offset**: UPPER, LOWER and CapV asked only at the range restarts
`λ ≥ ι(Γ_{Ω₁+ε₀})`, (CL), EQ, TCrest, (EMB₂). -/
theorem gcRoad (hU : ∀ l, CdRange S l → iota S gcV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gcV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gcV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hs := (gcFamSup (S := S)).1
  refine gcFam.famRoad3 (fun l hr h => hU l hr (hs ▸ h)) (fun l hr h => hL l hr (hs ▸ h))
    (fun k l hr hlk hfix => gcBT_fix S (gcSeq_one_add k) hr hlk hfix) (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (iota S gcV) l with h | h
  · exact hV l hr hlω h
  · exact gcCapV hr h

/-- **Past the frontier of `R2.GbWLoc`**: `ι(Γ_{Ω₁+ω·2}) < ι(Γ_{Ω₁+ε₀})`. -/
theorem gc_beyond_gb : iota S gbV < iota S gcV := by
  have hE : InE (ε₀ : Ordinal.{0}) := omega0_opow_epsilon 0
  have hω := omega0_lt_epsilon 0
  have h2 : (ω : Ordinal.{0}) * 2 < ε₀ := by rw [mul_two_eq]; exact (inE_indec hE).add_lt hω hω
  have e : gbV = gcG (ω * 2) := by rw [← (gbV_psi S).1, gc_psi S _ h2.le]
  rw [e]
  exact cd_iota_lt_of_good (gc_good fun _ _ => GxCl.atom (gcG_atom h2)) (gcG_lt h2)

/-- **Where the new frontiers lie** (unconditional): for every `α` with `1 + α < ε₀`, `Λ⁺(gcB α) = ι(Γ_{Ω₁+2+α}·ω)`,
`Λ^{gcB α} = ι(Γ_{Ω₁+2+α+1})`, every one below `ι(Γ_{Ω₁+ε₀}) = sup_n Λ⁺(gcB (gcSeq n))`, `υ(ι(Γ_{Ω₁+ε₀})) =
P(Γ_{Ω₁+ε₀}) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and `ι(Γ_{Ω₁+ε₀}) < L(ω+1)`. -/
theorem gc_fr_order {α : Ordinal.{0}} (h : 1 + α < ε₀) (k : ℕ) :
    xtB1 (gcB α).K.sys = iota S (gcG (1 + α) * ω) ∧ (lpFam (gcB α)).famSup = iota S (gcG (1 + α + 1)) ∧
    xtB1 (gcB α).K.sys < iota S gcV ∧ gcFam.famSup = iota S gcV ∧
    upsilon (iota S gcV) = Pv S gcV ∧ Pv S gcV < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    iota S gcV < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨hs, hups, hlt⟩ := gcFamSup (S := S)
  have hU : upsilon (iota S gcV) = Pv S gcV := by rw [← hs, hups]
  refine ⟨(gcB_loc S h).1, (gcBFam_loc S h).1, gcB1_lt_sup h, hs, hU, hlt, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt ((((hU.trans_lt hlt).trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2.Gc
