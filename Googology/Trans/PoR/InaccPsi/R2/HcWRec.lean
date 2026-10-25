import Googology.Trans.PoR.InaccPsi.R2.HcWB

/-!
# HcWRec: THE RECURSION ON THE OFFSET OF LEVEL `ω`; EVERY `φ(ω, G+1+ν)`, `ν < ε₀`, IS LOCATED

The recursion `hcWV ν` (`Ordinal.limitRecOn`): `hcWV 0 = Hc.hcWU` (the system at `φ(ω, G+1)`), `hcWV (ν+1)` the
`ω`-step `Hc.hcWStep` at `F_ν` started at `hcWV ν`, `hcWV λ` (limit `λ < ε₀`) the union of `hcWV (gpFs λ k)`
(`hcWLimCh`, an `ω`-chain).  The invariant (`hcW_inv`): every `hcWV ν`, `ν < ε₀`, has base gate `0`, starts the
stage at `F_ν = φ(ω, G+1+ν)` (so its bound is `F_ν`), and extends every `hcWV μ`, `μ ≤ ν`.  Hence every
`φ(ω, G+1+ν)`, `ν < ε₀`, is located (`hcWV_loc`), and ENUM-REACH, CapV hold at every range restart below
`ι(Γ(φ(ω, G+ε₀)))` (`hcWE_enum`, `hcWE_capV`), unconditionally.

* `hcWLimCh`, `HcWLimC.congr`, `hcWSt`, `hcWExt`, `hcWLimD`, `hcWV`, `hcWV_zero`, `hcWV_succ`, `hcWV_limit`,
  `hcWSt_eq`, `hcWV_lim_eq`, `hcW_inv` (**THE INVARIANT**), `hcWV_B`, `hcWV_γ`, `hcWV_loc` (**`φ(ω, G+1+ν)` IS
  LOCATED, EVERY `ν < ε₀`**), `hcWF_eps0`, `hcWE_cof`, `hcWE_enum`, `hcWE_capV`, `hcWE_road` (**THE ROAD**),
  `hcWE_lt_Om2`, `hcWE_P`, `hcWE_fr_order`.

No new axiom.  New definitions: `hcWLimCh`, `hcWSt`, `hcWExt`, `hcWLimD`, `hcWV`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb Googology.Trans.PoR.InaccPsi.R2.Gp
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The union along a fundamental sequence -/

/-- **The `ω`-chain along `gpFs λ`**: union bound `F_λ`, union base reading `F_λ(x)`. -/
noncomputable def hcWLimCh {l : Ordinal.{0}} {V : Ordinal.{0} → HcVD} (H : HcWLimC l V) : HcCh where
  D := fun k => V (gpFs l k)
  B := hcWF l
  b := hcWFr l
  γ0 := fun k => (H.2.2.1 _ (hcWLim_fs H k)).1
  B_mono := fun k => by
    rw [hcWLim_B H (hcWLim_fs H k), hcWLim_B H (hcWLim_fs H (k + 1))]
    exact hcWF_mono' (gpFs_mono H.2.1 H.1 k).le
  B_lt := fun k => by rw [hcWLim_B H (hcWLim_fs H k)]; exact hcWF_mono (hcWLim_fs H k)
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hcWLim_cofF H hc
    exact ⟨k, by rw [hcWLim_B H (hcWLim_fs H k)]; exact hk⟩
  R_ext := fun k c x hc => (H.2.2.2 _ _ (gpFs_mono H.2.1 H.1 k).le (hcWLim_fs H (k + 1)) c hc).1 x
  g_ext := fun k c hc => (H.2.2.2 _ _ (gpFs_mono H.2.1 H.1 k).le (hcWLim_fs H (k + 1)) c hc).2
  B_lt1 := hcWF_lt_G1 H.1
  B_fix := by have := hcWF_fix 1 l; rwa [Nat.cast_one] at this
  B_mem := fun S _ _ ha _ => hcWF_mem H.1 S ha
  b_ge := fun k x hx hx1 => by rw [hcWLim_b H (hcWLim_fs H k) hx hx1]; exact (hcWFr_mono (hcWLim_fs H k)).le
  b_cof := fun x hx hx1 μ hμ => by
    obtain ⟨k, hk⟩ := hcWLim_cofFr H hμ
    exact ⟨k, by rw [hcWLim_b H (hcWLim_fs H k) hx hx1]; exact hk⟩
  b_fix := fun x _ _ => by have := hcWFr_fix 1 l x; rwa [Nat.cast_one] at this
  b_gt := fun x hx hx1 => hcWFr_gt hx hx1 _
  b_lt := fun x hx hx1 => hcWFr_lt_BR hx hx1 H.1
  b_pi := fun _ _ hB => hcWFr_pi hB H.1

/-- The condition at a limit depends only on the values below the limit. -/
theorem HcWLimC.congr {l : Ordinal.{0}} {V V' : Ordinal.{0} → HcVD} (H : HcWLimC l V)
    (hVV : ∀ β, β < l → V' β = V β) : HcWLimC l V' := by
  refine ⟨H.1, H.2.1, fun μ hμ => by rw [hVV μ hμ]; exact H.2.2.1 μ hμ, fun μ μ' h h' c hc => ?_⟩
  rw [hVV μ (lt_of_le_of_lt h h')] at hc ⊢
  rw [hVV μ' h']
  exact H.2.2.2 μ μ' h h' c hc

/-- **The union along `gpFs λ` starts the stage at `F_λ`.** -/
theorem hcWLim_start {l : Ordinal.{0}} {V : Ordinal.{0} → HcVD} (H : HcWLimC l V) :
    HcSStart (hcXPB (hcWX l H.1 0)) (hcWLimCh H).U where
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  Z := fun x hx _ => by rw [HcPB.Zst_eq _ hx.pos]; rfl

/-! ## The recursion on the offset -/

open Classical in
/-- The successor step: the `ω`-step at `F_μ` when `U` starts the stage there. -/
noncomputable def hcWSt (μ : Ordinal.{0}) (U : HcVD) : HcVD :=
  if h : ∃ hμ : μ < ε₀, HcSStart (hcXPB (hcWX μ hμ 0)) U then hcWStep μ h.choose U h.choose_spec else U

open Classical in
/-- The earlier values, extended by `Hc.hcWU`. -/
noncomputable def hcWExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HcVD) (β : Ordinal.{0}) : HcVD :=
  if h : β < l then IH β h else hcWU

open Classical in
/-- The limit step: the union along `gpFs λ` when the condition holds. -/
noncomputable def hcWLimD (l : Ordinal.{0}) (_hl : IsSuccLimit l) (IH : ∀ β, β < l → HcVD) : HcVD :=
  if H : HcWLimC l (hcWExt l IH) then (hcWLimCh H).U else hcWU

/-- **THE RECURSION ON THE OFFSET OF LEVEL `ω`.** -/
noncomputable def hcWV (ν : Ordinal.{0}) : HcVD :=
  Ordinal.limitRecOn (motive := fun _ => HcVD) ν hcWU hcWSt hcWLimD

theorem hcWV_zero : hcWV 0 = hcWU := by unfold hcWV; rw [Ordinal.limitRecOn_zero]

theorem hcWV_succ (ν : Ordinal.{0}) : hcWV (ν + 1) = hcWSt ν (hcWV ν) := by
  unfold hcWV; rw [Ordinal.limitRecOn_add_one]

theorem hcWV_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hcWV l = hcWLimD l hl (fun β _ => hcWV β) := by
  unfold hcWV; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hcWSt_eq {μ : Ordinal.{0}} (hμ : μ < ε₀) {U : HcVD} (hU : HcSStart (hcXPB (hcWX μ hμ 0)) U) :
    hcWSt μ U = hcWStep μ hμ U hU := by
  unfold hcWSt; rw [dif_pos ⟨hμ, hU⟩]

theorem hcWExt_eq {l β : Ordinal.{0}} (h : β < l) : hcWExt l (fun β _ => hcWV β) β = hcWV β := by
  unfold hcWExt; rw [dif_pos h]

theorem hcWV_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (H : HcWLimC l hcWV) :
    hcWV l = (hcWLimCh (H.congr fun β h => hcWExt_eq h)).U := by
  rw [hcWV_limit hl]; unfold hcWLimD; rw [dif_pos (H.congr fun β h => hcWExt_eq h)]

/-- **THE INVARIANT**: every `hcWV ν`, `ν < ε₀`, has base gate `0`, starts the stage at `F_ν`, and extends every
`hcWV μ`, `μ ≤ ν`. -/
theorem hcW_inv : ∀ ν, ν < ε₀ → (hcWV ν).γ = 0 ∧ (∃ hν : ν < ε₀, HcSStart (hcXPB (hcWX ν hν 0)) (hcWV ν)) ∧
    ∀ μ, μ ≤ ν → ∀ c, c < (hcWV μ).B → (∀ x, (hcWV ν).R c x = (hcWV μ).R c x) ∧ (hcWV ν).g c = (hcWV μ).g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  have hB : ∀ μ, μ < ν → (hcWV μ).B = hcWF μ := fun μ hμ => by
    obtain ⟨-, ⟨hμ', hst⟩, -⟩ := IH μ hμ (hμ.trans hν)
    exact hc_B_of_start hst
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hcWV_zero]
    refine ⟨rfl, ⟨hν, hcWU_start⟩, fun μ hμ c _ => ?_⟩
    rw [Ordinal.le_zero.1 hμ, hcWV_zero]
    exact ⟨fun _ => rfl, rfl⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < ε₀ := (lt_add_one μ).trans hν
    obtain ⟨hγ, ⟨hμ'', hst⟩, hcoh⟩ := IH μ (lt_add_one μ) hμε
    have e : hcWV (μ + 1) = hcWStep μ hμε (hcWV μ) hst := by rw [hcWV_succ, hcWSt_eq hμε hst]
    rw [e]
    refine ⟨rfl, ⟨hν, hcWStep_start μ hμε (hcWV μ) hst hν⟩, fun μ' hμ' c hc => ?_⟩
    rcases hμ'.lt_or_eq with hlt | heq
    · have hle : μ' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hcWV μ).B := by
        rw [hc_B_of_start hst]
        rw [hB μ' hlt] at hc
        exact hc.trans_le (hcWF_mono' hle)
      obtain ⟨h1, h2⟩ := hcWStep_ext μ hμε (hcWV μ) hst hcμ
      obtain ⟨h3, h4⟩ := hcoh μ' hle c hc
      exact ⟨fun x => (h1 x).trans (h3 x), h2.trans h4⟩
    · subst heq; rw [e]; exact ⟨fun _ => rfl, rfl⟩
  · -- the limit: the union along `gpFs ν`
    have H : HcWLimC ν hcWV := ⟨hν, hlim, fun μ hμ => by
      obtain ⟨hγ, hst, -⟩ := IH μ hμ (hμ.trans hν); exact ⟨hγ, hst⟩,
      fun μ μ' h h' c hc => (IH μ' h' (h'.trans hν)).2.2 μ h c hc⟩
    have e := hcWV_lim_eq hlim H
    set H' := H.congr fun β h => hcWExt_eq h with hH'
    rw [e]
    refine ⟨rfl, ⟨hν, hcWLim_start H'⟩, fun μ hμ c hc => ?_⟩
    rcases hμ.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := gpFs_cof hlim hν μ hlt
      have hkl := hcWLim_fs H k
      have hck : c < (hcWV (gpFs ν k)).B := by
        rw [hB _ hkl]; rw [hB μ hlt] at hc; exact hc.trans (hcWF_mono hk)
      have hck' : c < ((hcWLimCh H').D k).B := by
        show c < (hcWExt ν (fun β _ => hcWV β) (gpFs ν k)).B
        rw [hcWExt_eq hkl]; exact hck
      obtain ⟨h3, h4⟩ := (IH _ hkl (hkl.trans hν)).2.2 μ hk.le c hc
      refine ⟨fun x => ?_, ?_⟩
      · rw [(hcWLimCh H').U_R hck' x]
        show (hcWExt ν (fun β _ => hcWV β) (gpFs ν k)).R c x = _
        rw [hcWExt_eq hkl]; exact h3 x
      · rw [(hcWLimCh H').U_g hck']
        show (hcWExt ν (fun β _ => hcWV β) (gpFs ν k)).g c = _
        rw [hcWExt_eq hkl]; exact h4
    · subst heq; rw [e]; exact ⟨fun _ => rfl, rfl⟩

theorem hcWV_B {ν : Ordinal.{0}} (hν : ν < ε₀) : (hcWV ν).B = hcWF ν := by
  obtain ⟨-, ⟨_, hst⟩, -⟩ := hcW_inv ν hν
  exact hc_B_of_start hst

theorem hcWV_γ {ν : Ordinal.{0}} (hν : ν < ε₀) : (hcWV ν).γ = 0 := (hcW_inv ν hν).1

/-- **`φ(ω, G+1+ν)` IS LOCATED, EVERY `ν < ε₀`**: `Λ⁺ = ι(Γ(φ(ω, G+1+ν))·ω)`, `P(Γ(φ(ω, G+1+ν))·ω) < L(0)`. -/
theorem hcWV_loc (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hcWF ν) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hcWF ν) * ω) ∧ Pv S (gcG (hcWF ν) * ω) < Nc.ncL S 0 := by
  rw [← hcWV_B hν]; exact hcV_locD (hcWV ν) S (by rw [hcWV_γ hν]; exact Td.tdK_SC.1)

/-! ## The frontier `ι(Γ(φ(ω, G+ε₀)))` -/

/-- **`F_{ε₀} = φ(ω, G+ε₀)`.** -/
theorem hcWF_eps0 : hcWF ε₀ = veblen ω (gcG 0 + ε₀) := by
  unfold hcWF; rw [add_assoc, one_add_of_omega0_le (omega0_lt_inE hc_eps0_E).le]

theorem hcWE_lim : IsSuccLimit (hcWF ε₀) := ev_isSuccLimit_of_inE (hcWF_E _)

/-- Every ordinal below `F_{ε₀}` lies below some `F_ν`, `ν < ε₀`. -/
theorem hcWE_cofF {β : Ordinal.{0}} (hβ : β < hcWF ε₀) : ∃ ν, ν < ε₀ ∧ β < hcWF ν := by
  obtain ⟨a, ha, hca⟩ := ((isNormal_veblen ω).lt_iff_exists_lt (isSuccLimit_add _ hc_eps0_lim)).1 hβ
  obtain ⟨t, ht, hat⟩ := (lt_add_iff hc_eps0_lim.bot_lt.ne').1 ha
  refine ⟨t + 1, hc_eps0_lim.add_one_lt ht, hca.trans_le (((isNormal_veblen ω).monotone hat).trans ?_)⟩
  exact (hcWF_mono (lt_add_one t)).le

/-- **The located bounds `ι(Γ(F_ν)·ω)`, `ν < ε₀`, are cofinal below `ι(Γ(φ(ω, G+ε₀)))`.** -/
theorem hcWE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG (hcWF ε₀))) :
    ∃ ν, ν < ε₀ ∧ l < iota S (gcG (hcWF ν) * ω) := by
  have hlim : IsSuccLimit (gcG (hcWF ε₀)) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG (hcWF ε₀))) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hcWE_lim e.2
  obtain ⟨ν, hν, hβν⟩ := hcWE_cofF hβ
  refine ⟨ν, hν, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβν)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(ω, G+ε₀)))`, fixed points included** (UNCONDITIONAL). -/
theorem hcWE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hcWF ε₀))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, hν, h⟩ := hcWE_cof S hl
  rw [← hcWV_B hν] at h
  exact hcV_locD_enum (hcWV ν) S (by rw [hcWV_γ hν]; exact Td.tdK_SC.1) hr h

/-- **CapV at every range restart below `ι(Γ(φ(ω, G+ε₀)))`** (UNCONDITIONAL). -/
theorem hcWE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (hcWF ε₀))) :
    CdCapV S l := by
  obtain ⟨ν, hν, h⟩ := hcWE_cof S hl
  rw [← hcWV_B hν] at h
  exact hcV_locD_capV (hcWV ν) S (by rw [hcWV_γ hν]; exact Td.tdK_SC.1) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(ω, G+ε₀)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hcWE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG (hcWF ε₀)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (hcWF ε₀)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (hcWF ε₀)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hcWE_enum S hr h) (fun _ hr h => hcWE_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- `φ(ω, G+ε₀) < Γ_{Ω₁+2}`. -/
theorem hcWE_lt_G1 : hcWF ε₀ < gcG 1 := by
  have hG1 := gcG_SC 1
  have hfix : veblen ω (gcG 1) = gcG 1 := gn_veb_fix hG1 (omega0_lt_inE (Low.opow_eq_self_of_SC hG1))
  have hNE := hcNw_E (gcG 0)
  have hε : (ε₀ : Ordinal.{0}) < hcNw (gcG 0) := (gc_eps0_le_Om1.trans_lt (gcG_Om1_lt 0)).trans (hcNw_gt _)
  have h1 : gcG 0 + 1 + ε₀ < hcNw (gcG 0) := (inE_indec hNE).add_lt ((hcNw_lim _).add_one_lt (hcNw_gt _)) hε
  have := (isNormal_veblen ω).strictMono h1
  rw [hcNw_fix] at this
  exact this.trans_le (hcNw_le hfix (gcG_lt zero_lt_one))

/-- **`Γ(φ(ω, G+ε₀)) < Ω₂`.** -/
theorem hcWE_lt_Om2 : gcG (hcWF ε₀) < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG (hcWF ε₀) < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hcWE_lt_G1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(ω, G+ε₀))) < L(0)`.** -/
theorem hcWE_P (S : InaccSeq.{0}) : Pv S (gcG (hcWF ε₀)) < Nc.ncL S 0 := ga_Pv_lt_L0 S hcWE_lt_Om2.le

/-- **The order of the frontiers**: `ι(Γ(φ(ω, G+1))) ≤ ι(Γ(φ(ω, G+1))·ω) ≤ ι(Γ(φ(ω, G+1+ν))·ω) ≤
ι(Γ(φ(ω, G+ε₀))) ≤ ι(Ω₂)` for every `ν < ε₀`, and `P(Γ(φ(ω, G+ε₀))) ≤ P(Ω₂) < L(0)`. -/
theorem hcWE_fr_order (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    iota S (gcG hbTw) ≤ iota S (gcG hbTw * ω) ∧ iota S (gcG hbTw * ω) ≤ iota S (gcG (hcWF ν) * ω) ∧
      iota S (gcG (hcWF ν) * ω) ≤ iota S (gcG (hcWF ε₀)) ∧ iota S (gcG (hcWF ε₀)) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG (hcWF ε₀)) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG (hcWF ε₀)) := Low.opow_eq_self_of_SC (gcG_SC _)
  refine ⟨iota_mono _ _ (le_mul_of_one_le_right' one_lt_omega0.le), iota_mono _ _ ?_,
    iota_mono _ _ (InE.mul_lt hV (gcG_lt (hcWF_mono hν)) (omega0_lt_inE hV)).le,
    iota_mono _ _ hcWE_lt_Om2.le, Nm.Pv_mono hcWE_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩
  rw [← hcWF_zero]
  exact mul_le_mul_left (gcG_le (hcWF_mono' zero_le)) _

end Googology.Trans.PoR.InaccPsi.R2.Hc
