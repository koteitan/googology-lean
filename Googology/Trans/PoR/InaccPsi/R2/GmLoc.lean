import Googology.Trans.PoR.InaccPsi.R2.GmCodes

/-!
# WHERE THE FRONTIERS LIE, for every code `c` of a reading system with gate below `ε₀`: `Λ⁺(gmL c) = ι(Γ_{Ω₁+1+c}·ω)`,
and the supremum `ι(Γ_{Ω₁+1+B})`

Port of `R2.GiLoc` to the code systems `GmCS` of `R2.GmAt`, whose bound may pass `Γ_{Ω₁+1}` (codes may contain
atoms), and, for the layers, to offsets below `Γ_{x+2}` (`R2.GmGq`, `R2.GmU`); the proofs are those of `R2.GiLoc`.

For a reading system `RS : GmRS` and a code `c ∈ [ε_{Ω₁+1}, B)` with gate below `ε₀`, the gated layer `RS.gmL c`
(`R2.GmRS`) is an ungated layer `RS.gmLX c` (`Ge.geLayX`); its top reads the atom `Γ_{Ω₁+1+c}` and it has terms for
every code below it (`R2.GiCodes`), so the generic frontier lemma `R2.GiFr.gmB1_eq` locates its frontier:

* `GmRS.gmLX`, `GmRS.gmX`, `GmRS.gmLoc` (**`Λ⁺(gmX c) = ι(Γ_{Ω₁+1+c}·ω)`, `ρ` of it `= P(…) < L(0)`**), `GmRS.gmFix`
  (THEOREM UNI at the fixed range restarts below it), `GmRS.gmEnum` (**ENUM-REACH at every range restart below it,
  fixed points included**), `GmRS.gmCapV`, `GmRS.gmBlk` (**BLK^O and the exact reaches below `υ` of it**);
* `GmRS.gmXk k` (the cofinal codes `RS.cf k`), `GmRS.gmFam`, `GmRS.gmFam_sup` (**`sup_k Λ⁺(gmXk k) = ι(Γ_{Ω₁+1+B})`,
  `υ` of it `= P(Γ_{Ω₁+1+B}) < L(0)`**), `GmRS.gmFam_enum`, `GmRS.gmFam_capV`, `GmRS.gmFam_blk`, `GmRS.gmFam_road`
  (**THE ROAD with UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+B})`**), `GmRS.gm_fr_order`.

No new axiom.  New definitions: `GmRS.gmLX`, `GmRS.gmX`, `GmRS.gmXk`, `GmRS.gmFam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GmRS

variable (RS : GmRS)

/-! ## The layer of a code with small digits -/

/-- **The layer of the code `c`** (gate below `ε₀`), ungated. -/
noncomputable def gmLX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < ε₀) : XtLay :=
  geLayX (RS.gmL c h hc).K (by rw [RS.gmL_g]; exact hg)

/-- Its term system. -/
noncomputable def gmX (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < ε₀) : XtSys :=
  (RS.gmLX c h hc hg).sys

section Code

variable (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) (hg : RS.K.gt c < ε₀)
include h hc hg

theorem gmX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : (RS.gmX c h hc hg).top x = gq (RS.R c x) x :=
  RS.gmL_top h hc hx hx1 (ge_gx hg hx)

theorem gmX_pkg : XtTopPkg (RS.gmX c h hc hg) := XtLay.topPkg (RS.gmLX c h hc hg)

theorem gmT_le : gcG c ≤ RS.K.V := (gcG_lt hc).le

theorem gmX_cl : ∀ Z, SC Z → GxCl Z (RS.K.At Z) (gcG c) := fun Z hZ =>
  RS.gmL_atom hc (ge_gx hg (gg_SC_eps hZ))

theorem gmX_poly (S : InaccSeq.{0}) : GmPoly RS.K (RS.gmX c h hc hg) (gcG c) := by
  intro Z d hd hdE
  obtain ⟨s, hs⟩ := (RS.gmL_codes S c h hc).2 (max Z ε₀) d (by rw [RS.gmL_g]; exact hg.trans_le (le_max_right _ _))
    (gmCl_mono (le_max_left _ _) hd) hdE
  exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (max_le hZy (gc_eps0_le (gg_SC_eps hy)))⟩

theorem gmX_topth (S : InaccSeq.{0}) : ∀ y, SC y → y < Om 1 →
    (RS.gmX c h hc hg).top y = gxTh y (RS.K.At y) (gcG c) := by
  intro y hy hy1
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  rw [RS.gmX_top c h hc hg hyE hy1', ← RS.gmL_E h hc hyE hy1' (ge_gx hg hyE)]
  exact (RS.gmL_codes S c h hc).1 y hy hy1 (ge_gx hg hyE)

theorem gmX_topE : ∀ x, InE x → x < Om1 → eN x < (RS.gmX c h hc hg).top x := by
  intro x hx hx1
  rw [RS.gmX_top c h hc hg hx hx1]
  obtain ⟨hT, h1⟩ := gm1_T hx hx1 (RS.R_lt0' hx hx1 hc (ge_gx hg hx))
  exact gmq_eN_lt hx hx1 hT h1

/-- **WHERE THE FRONTIER OF THE CODE `c = ε_{Ω₁+1}·γ + a` LIES**: `Λ⁺(RS.gmX c) = ι(Γ_{Ω₁+1+c}·ω)`,
`ρ` of it `= P(Γ_{Ω₁+1+c}·ω) < L(0)`. -/
theorem gmLoc (S : InaccSeq.{0}) :
    xtB1 (RS.gmX c h hc hg) = iota S (gcG c * ω) ∧
    upsilon (xtB1 (RS.gmX c h hc hg)) = Pv S (gcG c * ω) ∧ Pv S (gcG c * ω) < Nc.ncL S 0 := by
  have h' := gmB1_eq (S := S) (RS.gmT_le c h hc hg) (RS.gmX_poly c h hc hg S) (RS.gmX_topth c h hc hg S)
    (RS.gmX_cl c h hc hg)
    (gcG_Om1_lt _).le (RS.gmX_topE c h hc hg) (RS.gmX_pkg c h hc hg)
  rwa [geG_E] at h'

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(RS.gmX c)`** (THEOREM UNI). -/
theorem gmFix (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (RS.gmX c h hc hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (RS.gmX c h hc hg) l := by
  have hlt : l < iota S (ω ^ gcG c * ω) := by rw [geG_E, ← (RS.gmLoc c h hc hg S).1]; exact hl
  exact gmUniTh (RS.gmT_le c h hc hg) (RS.gmX_poly c h hc hg S) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem gmX_nonfix : XtNonfix (xtOrec (RS.gmX c h hc hg)) (xtB1 (RS.gmX c h hc hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (RS.gmX_pkg c h hc hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem gmEnum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (RS.gmLoc c h hc hg S).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (RS.gmX_pkg c h hc hg)) (RS.gmX_nonfix c h hc hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (RS.gmX_pkg c h hc hg)) hr.1 hl).2 (RS.gmFix c h hc hg S hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+c}·ω)`, fixed points included.** -/
theorem gmCapV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG c * ω)) :
    CdCapV S l := by
  have hl' := hl
  rw [← (RS.gmLoc c h hc hg S).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (RS.gmX_pkg c h hc hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (RS.gmX_nonfix c h hc hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (RS.gmX_pkg c h hc hg) hr hl' hfx.symm (RS.gmEnum c h hc hg S hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(RS.gmX c)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem gmBlk :
    (∀ c' d, c' < d → d < upsilon (xtB1 (RS.gmX c h hc hg)) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (RS.gmX c h hc hg) ∧ c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (RS.gmX c h hc hg) →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (RS.gmX c h hc hg) l)) ∧
    (∀ α < upsilon (xtB1 (RS.gmX c h hc hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (RS.gmX_pkg c h hc hg)

end Code

/-! ## The supremum `ι(Γ_{Ω₁+1+B})` -/

/-- The `k`-th member of the cofinal family: the code `RS.cf k`. -/
noncomputable def gmXk (k : ℕ) : XtSys := RS.gmX (RS.cf k) (RS.cf_ge k) (RS.cf_lt k) (RS.cf_g k)

theorem gmGood_mul {c : Ordinal.{0}} (hc : c < RS.K.B) (hgc : RS.K.gt c < ε₀) (S : InaccSeq.{0}) :
    Bt.Good S (gcG c * ω) := by
  refine gm_good (K := RS.K) fun Z hZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (RS.gmL_atom hc (ge_gx hgc (gg_SC_eps hZ))) (GxCl.small (gg_one_lt_of_SC hZ)))

theorem gmXk_loc (S : InaccSeq.{0}) (k : ℕ) : xtB1 (RS.gmXk k) = iota S (gcG (RS.cf k) * ω) := by
  unfold GmRS.gmXk; rw [(RS.gmLoc _ _ _ _ S).1]

/-- **The family of the layers of the cofinal codes.** -/
noncomputable def gmFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (RS.gmXk k)
  off := fun k => xtOrec (RS.gmXk k)
  spec := fun k => xtSpec1 (RS.gmX_pkg _ _ _ _)
  mono := fun k => by
    show xtB1 (RS.gmXk k) < xtB1 (RS.gmXk (k + 1))
    rw [RS.gmXk_loc S, RS.gmXk_loc S]
    refine cd_iota_lt_of_good (RS.gmGood_mul (RS.cf_lt k) (RS.cf_g k) S) ?_
    have hE := geG_E (RS.cf (k + 1))
    exact (InE.mul_lt hE (gcG_lt (RS.cf_mono k)) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => RS.gmX_nonfix _ _ _ _

/-- **`sup_k Λ⁺(gmXk k) = ι(Γ_{Ω₁+1+B})`, `υ` of it `= P(Γ_{Ω₁+1+B}) < L(0)`.** -/
theorem gmFam_sup (S : InaccSeq.{0}) : (RS.gmFam S).famSup = iota S RS.K.V ∧
    upsilon (RS.gmFam S).famSup = Pv S RS.K.V ∧ Pv S RS.K.V < Nc.ncL S 0 := by
  have hVS : SC RS.K.V := gmV_SC
  have hVE : ω ^ RS.K.V = RS.K.V := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < RS.K.B → gcG c * ω < RS.K.V := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (RS.gmFam S).famSup = iota S RS.K.V := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (RS.gmXk k) ≤ _
      rw [RS.gmXk_loc S k]
      exact iota_mono _ _ (hstep _ (RS.cf_lt k)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit RS.B_lim e.2
      obtain ⟨n, hn⟩ := RS.cf_cof c hc
      have h1 : e.1 < gcG (RS.cf n) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (RS.cf n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (RS.gmXk n) := (RS.gmXk_loc S n).symm
        _ ≤ (RS.gmFam S).famSup := ((RS.gmFam S).famBd_lt n).le
  have hups : upsilon (RS.gmFam S).famSup = Pv S RS.K.V := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gmV_lt_Om2 RS.K S).le⟩

theorem gmFam_fix (S : InaccSeq.{0}) : (RS.gmFam S).famTHfix S :=
  fun k _ hr hlk hfix => RS.gmFix _ _ _ _ S hr hlk hfix

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+B})`, fixed points included.** -/
theorem gmFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S RS.K.V) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (RS.gmFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (RS.gmFam S).famLt hl
  have hk' : l < iota S (gcG (RS.cf k) * ω) := by rw [← RS.gmXk_loc S k]; exact hk
  exact RS.gmEnum _ (RS.cf_ge k) (RS.cf_lt k) (RS.cf_g k) S hr hk'

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+B})`, fixed points included.** -/
theorem gmFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S RS.K.V) :
    CdCapV S l := by
  rw [← (RS.gmFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (RS.gmFam S).famLt hl
  have hk' : l < iota S (gcG (RS.cf k) * ω) := by rw [← RS.gmXk_loc S k]; exact hk
  exact RS.gmCapV _ (RS.cf_ge k) (RS.cf_lt k) (RS.cf_g k) S hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+1+B})} = P(Γ_{Ω₁+1+B})`**, with the exact reaches. -/
theorem gmFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (RS.gmFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (RS.gmFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (RS.gmFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (RS.gmFam S).off k l)) ∧
    (∀ α < upsilon (RS.gmFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (RS.gmFam S).famBlk

/-- **THE ROAD past every code below `B`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+B})` (CapV also
`υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gmFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S RS.K.V ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S RS.K.V ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S RS.K.V ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hF := (RS.gmFam_sup S).1
  refine (RS.gmFam S).famRoad3 (fun l hr h => hU l hr (hF ▸ h)) (fun l hr h => hL l hr (hF ▸ h)) (RS.gmFam_fix S)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (RS.gmFam S).famSup l with h | h
  · exact hV l hr hlω (hF ▸ h)
  · exact RS.gmFam_capV S hr (hF ▸ h)

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+c}·ω) < ι(Γ_{Ω₁+1+B}) < ι(Ω₂)` for every code `c < B` with gate below
`ε₀`, and `P(Γ_{Ω₁+1+B}) < P(Ω₂) < L(0)`. -/
theorem gm_fr_order {c : Ordinal.{0}} (hc : c < RS.K.B) (hg : RS.K.gt c < ε₀) (S : InaccSeq.{0}) :
    iota S (gcG c * ω) < iota S RS.K.V ∧ iota S RS.K.V < iota S (Om (1 + 1)) ∧
      Pv S RS.K.V < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hVE : ω ^ RS.K.V = RS.K.V := Low.opow_eq_self_of_SC gmV_SC
  have hgiV : Bt.Good S RS.K.V := by
    show RS.K.V ∈ S.CSet (ConjT.Aη S RS.K.V + 1) (S.psi (ConjT.Aη S RS.K.V) (Om 1))
    have := CSet.psi_mem (S := S) (a := ConjT.Aη S RS.K.V + 1) (b := S.psi (ConjT.Aη S RS.K.V) (Om 1))
      (gm_B_lt_A1 (S := S) RS.K RS.K.V) (InR_Om_succ 1) (ga_Om2_mem _ _)
      (RS.K.B_mem S _ _ (gm_B_lt_A1 (S := S) RS.K RS.K.V))
    rwa [gmV_psi RS.K S] at this
  have h2 : iota S (gcG c * ω) < iota S RS.K.V :=
    cd_iota_lt_of_good (RS.gmGood_mul hc hg S) (InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE))
  have h3 : iota S RS.K.V < iota S (Om (1 + 1)) := cd_iota_lt_of_good hgiV (gmV_lt_Om2 RS.K S)
  have h4 : Pv S RS.K.V < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h3
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h2, h3, h4, ga_Pv_lt_L0 S le_rfl⟩

end GmRS

end Googology.Trans.PoR.InaccPsi.R2.Gm
