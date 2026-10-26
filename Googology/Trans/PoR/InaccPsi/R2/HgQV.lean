import Googology.Trans.PoR.InaccPsi.R2.HgQR

/-!
# HgQV: THE RECURSION ON THE OFFSET OF THE LEVEL `Ω₁`; EVERY `φ(Ω₁, G+1+ν)`, `ν < ε₀`, IS LOCATED

The recursion `hgFV ν` (`Ordinal.limitRecOn`): `hgFV 0 = Hg.hgU` (the system at `φ(Ω₁, G+1)`), `hgFV (ν+1)` the union
over all levels over `Q_ν` (`Hg.hgQU (Hg.hgFB ν)`, bound `Q_{ν+1}`), `hgFV λ` (limit `λ < ε₀`) the union of the
`ω`-chain `hgFV (Gp.gpFs λ k)` (`Hg.HgCh`).  The invariant (`hgF_inv`): every `hgFV ν`, `ν < ε₀`, has base gate `0`,
starts the stage at `Q_ν = φ(Ω₁, G+1+ν)`, and extends every `hgFV μ`, `μ ≤ ν`.  Hence every `φ(Ω₁, G+1+ν)`,
`ν < ε₀`, is located (`hgFV_loc`), and ENUM-REACH, CapV hold at every range restart below `ι(Γ(φ(Ω₁, G+ε₀)))`
(`hgFE_enum`, `hgFE_capV`), unconditionally.

* `HgFLimC`, `hgFLimCh`, `HgFLimC.congr`, `hgFLim_start`, `hgFSt`, `hgFExt`, `hgFLimD`, `hgFV`, `hgF_inv` (**THE
  INVARIANT**), `hgFV_B`, `hgFV_γ`, `hgFV_loc` (**`φ(Ω₁, G+1+ν)` IS LOCATED, EVERY `ν < ε₀`**), `hgFV_enum`, `hgFE`,
  `hgFE_eq`, `hgFE_cof`, `hgFE_enum`, `hgFE_capV`, `hgFE_road` (**THE ROAD**), `hgFE_lt_Om2`, `hgFE_P`,
  `hgFE_fr_order`.

No new axiom.  New definitions: `HgFLimC`, `hgFLimCh`, `hgFSt`, `hgFExt`, `hgFLimD`, `hgFV`, `hgFE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv Googology.Trans.PoR.InaccPsi.R2.Gp
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The limit step: the union along a fundamental sequence -/

/-- **The condition at a limit `λ < ε₀`**: every earlier value has base gate `0`, starts the stage at its offset,
and later values extend earlier ones. -/
def HgFLimC (l : Ordinal.{0}) (V : Ordinal.{0} → HgVD) : Prop :=
  l < ε₀ ∧ IsSuccLimit l ∧ (∀ μ, μ < l → (V μ).γ = 0 ∧ ∃ hμ : μ < ε₀, HgQStart (hgFB μ hμ) (V μ)) ∧
    ∀ μ μ', μ ≤ μ' → μ' < l → ∀ c, c < (V μ).B → (∀ x, (V μ').R c x = (V μ).R c x) ∧ (V μ').g c = (V μ).g c

section Lim

variable {l : Ordinal.{0}} {V : Ordinal.{0} → HgVD} (H : HgFLimC l V)
include H

theorem hgFLim_B {μ : Ordinal.{0}} (hμ : μ < l) : (V μ).B = hgFQ μ := by
  obtain ⟨-, hst⟩ := H.2.2.1 μ hμ
  exact hg_B_of_start hst.choose_spec

theorem hgFLim_b {μ x : Ordinal.{0}} (hμ : μ < l) (hx : InE x) (hx1 : x < Om1) : (V μ).b x = hgFP μ x := by
  obtain ⟨-, hst⟩ := H.2.2.1 μ hμ
  exact hst.choose_spec.b x hx hx1 hx.pos

theorem hgFLim_fs (k : ℕ) : gpFs l k < l := gpFs_lt H.2.1 H.1 k

/-- `c < Q_λ` lies below some `Q_{λ_k}`. -/
theorem hgFLim_cofF {c : Ordinal.{0}} (hc : c < hgFQ l) : ∃ k, c < hgFQ (gpFs l k) := by
  obtain ⟨a, ha, hca⟩ := ((isNormal_veblen Om1).lt_iff_exists_lt (isSuccLimit_add _ H.2.1)).1 hc
  obtain ⟨t, ht, hat⟩ := (lt_add_iff H.2.1.bot_lt.ne').1 ha
  obtain ⟨k, hk⟩ := gpFs_cof H.2.1 H.1 t ht
  exact ⟨k, hca.trans_le (((isNormal_veblen Om1).monotone hat).trans
    ((isNormal_veblen Om1).strictMono ((add_lt_add_iff_left _).2 hk)).le)⟩

theorem hgFLim_cofFr {μ x : Ordinal.{0}} (hμ : μ < hgFP l x) : ∃ k, μ < hgFP (gpFs l k) x := by
  obtain ⟨a, ha, hca⟩ := ((isNormal_veblen x).lt_iff_exists_lt (isSuccLimit_add _ H.2.1)).1 hμ
  obtain ⟨t, ht, hat⟩ := (lt_add_iff H.2.1.bot_lt.ne').1 ha
  obtain ⟨k, hk⟩ := gpFs_cof H.2.1 H.1 t ht
  exact ⟨k, hca.trans_le (((isNormal_veblen x).monotone hat).trans
    ((isNormal_veblen x).strictMono ((add_lt_add_iff_left _).2 hk)).le)⟩

end Lim

/-- **The `ω`-chain along `gpFs λ`**: union bound `Q_λ`, union base reading `P_λ(x)`. -/
noncomputable def hgFLimCh {l : Ordinal.{0}} {V : Ordinal.{0} → HgVD} (H : HgFLimC l V) : HgCh where
  D := fun k => V (gpFs l k)
  B := hgFQ l
  b := hgFP l
  γ0 := fun k => (H.2.2.1 _ (hgFLim_fs H k)).1
  B_mono := fun k => by
    rw [hgFLim_B H (hgFLim_fs H k), hgFLim_B H (hgFLim_fs H (k + 1))]
    exact hgFQ_mono' (gpFs_mono H.2.1 H.1 k).le
  B_lt := fun k => by rw [hgFLim_B H (hgFLim_fs H k)]; exact hgFQ_mono (hgFLim_fs H k)
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hgFLim_cofF H hc
    exact ⟨k, by rw [hgFLim_B H (hgFLim_fs H k)]; exact hk⟩
  R_ext := fun k c x hc => (H.2.2.2 _ _ (gpFs_mono H.2.1 H.1 k).le (hgFLim_fs H (k + 1)) c hc).1 x
  g_ext := fun k c hc => (H.2.2.2 _ _ (gpFs_mono H.2.1 H.1 k).le (hgFLim_fs H (k + 1)) c hc).2
  B_lt1 := hgFQ_lt1 H.1
  B_fix := veblen_veblen_of_lt hg_one_lt_Om1 _
  B_mem := fun S _ _ ha _ => hgFQ_mem H.1 S ha
  b_ge := fun k x hx hx1 => by rw [hgFLim_b H (hgFLim_fs H k) hx hx1]; exact (hgFP_mono (hgFLim_fs H k)).le
  b_cof := fun x hx hx1 μ hμ => by
    obtain ⟨k, hk⟩ := hgFLim_cofFr H hμ
    exact ⟨k, by rw [hgFLim_b H (hgFLim_fs H k) hx hx1]; exact hk⟩
  b_fix := fun x hx _ => veblen_veblen_of_lt (one_lt_omega0.trans (omega0_lt_inE hx)) _
  b_gt := fun x hx hx1 => hgFP_gt hx hx1 _
  b_lt := fun x hx hx1 => hgFP_lt hx hx1 H.1
  b_pi := fun _ _ hB => hgFP_pi hB H.1

/-- The condition at a limit depends only on the values below the limit. -/
theorem HgFLimC.congr {l : Ordinal.{0}} {V V' : Ordinal.{0} → HgVD} (H : HgFLimC l V)
    (hVV : ∀ β, β < l → V' β = V β) : HgFLimC l V' := by
  refine ⟨H.1, H.2.1, fun μ hμ => by rw [hVV μ hμ]; exact H.2.2.1 μ hμ, fun μ μ' h h' c hc => ?_⟩
  rw [hVV μ (lt_of_le_of_lt h h')] at hc ⊢
  rw [hVV μ' h']
  exact H.2.2.2 μ μ' h h' c hc

/-- **The union along `gpFs λ` starts the stage at `Q_λ`.** -/
theorem hgFLim_start {l : Ordinal.{0}} {V : Ordinal.{0} → HgVD} (H : HgFLimC l V) :
    HgQStart (hgFB l H.1) (hgFLimCh H).U where
  ix := rfl
  γ := fun _ _ _ => Iff.rfl
  b := fun _ _ _ _ => rfl
  Z := fun x hx _ => by rw [HgPB.Zst_eq _ hx.pos]; rfl

/-! ## The recursion on the offset -/

open Classical in
/-- The successor step: the union over all levels over `Q_μ` when `U` starts the stage there. -/
noncomputable def hgFSt (μ : Ordinal.{0}) (U : HgVD) : HgVD :=
  if h : ∃ hμ : μ < ε₀, HgQStart (hgFB μ hμ) U then hgQU (hgFB μ h.choose) U h.choose_spec else U

open Classical in
/-- The earlier values, extended by `Hg.hgU`. -/
noncomputable def hgFExt (l : Ordinal.{0}) (IH : ∀ β, β < l → HgVD) (β : Ordinal.{0}) : HgVD :=
  if h : β < l then IH β h else hgU

open Classical in
/-- The limit step: the union along `gpFs λ` when the condition holds. -/
noncomputable def hgFLimD (l : Ordinal.{0}) (_hl : IsSuccLimit l) (IH : ∀ β, β < l → HgVD) : HgVD :=
  if H : HgFLimC l (hgFExt l IH) then (hgFLimCh H).U else hgU

/-- **THE RECURSION ON THE OFFSET OF THE LEVEL `Ω₁`.** -/
noncomputable def hgFV (ν : Ordinal.{0}) : HgVD :=
  Ordinal.limitRecOn (motive := fun _ => HgVD) ν hgU hgFSt hgFLimD

theorem hgFV_zero : hgFV 0 = hgU := by unfold hgFV; rw [Ordinal.limitRecOn_zero]

theorem hgFV_succ (ν : Ordinal.{0}) : hgFV (ν + 1) = hgFSt ν (hgFV ν) := by
  unfold hgFV; rw [Ordinal.limitRecOn_add_one]

theorem hgFV_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hgFV l = hgFLimD l hl (fun β _ => hgFV β) := by
  unfold hgFV; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hgFSt_eq {μ : Ordinal.{0}} (hμ : μ < ε₀) {U : HgVD} (hU : HgQStart (hgFB μ hμ) U) :
    hgFSt μ U = hgQU (hgFB μ hμ) U hU := by
  unfold hgFSt; rw [dif_pos ⟨hμ, hU⟩]

theorem hgFExt_eq {l β : Ordinal.{0}} (h : β < l) : hgFExt l (fun β _ => hgFV β) β = hgFV β := by
  unfold hgFExt; rw [dif_pos h]

theorem hgFV_lim_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) (H : HgFLimC l hgFV) :
    hgFV l = (hgFLimCh (H.congr fun β h => hgFExt_eq h)).U := by
  rw [hgFV_limit hl]; unfold hgFLimD; rw [dif_pos (H.congr fun β h => hgFExt_eq h)]

/-- **THE INVARIANT**: every `hgFV ν`, `ν < ε₀`, has base gate `0`, starts the stage at `Q_ν`, and extends every
`hgFV μ`, `μ ≤ ν`. -/
theorem hgF_inv : ∀ ν, ν < ε₀ → (hgFV ν).γ = 0 ∧ (∃ hν : ν < ε₀, HgQStart (hgFB ν hν) (hgFV ν)) ∧
    ∀ μ, μ ≤ ν → ∀ c, c < (hgFV μ).B → (∀ x, (hgFV ν).R c x = (hgFV μ).R c x) ∧ (hgFV ν).g c = (hgFV μ).g c := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  have hB : ∀ μ, μ < ν → (hgFV μ).B = hgFQ μ := fun μ hμ => by
    obtain ⟨-, ⟨hμ', hst⟩, -⟩ := IH μ hμ (hμ.trans hν)
    exact hg_B_of_start hst
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hgFV_zero]
    refine ⟨rfl, ⟨hν, hgU_startF⟩, fun μ hμ c _ => ?_⟩
    rw [Ordinal.le_zero.1 hμ, hgFV_zero]
    exact ⟨fun _ => rfl, rfl⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμε : μ < ε₀ := (lt_add_one μ).trans hν
    obtain ⟨hγ, ⟨hμ'', hst⟩, hcoh⟩ := IH μ (lt_add_one μ) hμε
    have e : hgFV (μ + 1) = hgQU (hgFB μ hμε) (hgFV μ) hst := by rw [hgFV_succ, hgFSt_eq hμε hst]
    rw [e]
    refine ⟨rfl, ⟨hν, hgQU_startF hμε hν (hgFV μ) hst⟩, fun μ' hμ' c hc => ?_⟩
    rcases hμ'.lt_or_eq with hlt | heq
    · have hle : μ' ≤ μ := Order.lt_add_one_iff.1 hlt
      have hcμ : c < (hgFV μ).B := by
        rw [hg_B_of_start hst]
        rw [hB μ' hlt] at hc
        exact hc.trans_le (hgFQ_mono' hle)
      obtain ⟨h1, h2⟩ := hgQU_ext (hgFB μ hμε) (hgFV μ) hst hcμ
      obtain ⟨h3, h4⟩ := hcoh μ' hle c hc
      exact ⟨fun x => (h1 x).trans (h3 x), h2.trans h4⟩
    · subst heq; rw [e]; exact ⟨fun _ => rfl, rfl⟩
  · have H : HgFLimC ν hgFV := ⟨hν, hlim, fun μ hμ => by
      obtain ⟨hγ, hst, -⟩ := IH μ hμ (hμ.trans hν); exact ⟨hγ, hst⟩,
      fun μ μ' h h' c hc => (IH μ' h' (h'.trans hν)).2.2 μ h c hc⟩
    have e := hgFV_lim_eq hlim H
    set H' := H.congr fun β h => hgFExt_eq h with hH'
    rw [e]
    refine ⟨rfl, ⟨hν, hgFLim_start H'⟩, fun μ hμ c hc => ?_⟩
    rcases hμ.lt_or_eq with hlt | heq
    · obtain ⟨k, hk⟩ := gpFs_cof hlim hν μ hlt
      have hkl := hgFLim_fs H k
      have hck : c < (hgFV (gpFs ν k)).B := by
        rw [hB _ hkl]; rw [hB μ hlt] at hc; exact hc.trans (hgFQ_mono hk)
      have hck' : c < ((hgFLimCh H').D k).B := by
        show c < (hgFExt ν (fun β _ => hgFV β) (gpFs ν k)).B
        rw [hgFExt_eq hkl]; exact hck
      obtain ⟨h3, h4⟩ := (IH _ hkl (hkl.trans hν)).2.2 μ hk.le c hc
      refine ⟨fun x => ?_, ?_⟩
      · rw [(hgFLimCh H').U_R hck' x]
        show (hgFExt ν (fun β _ => hgFV β) (gpFs ν k)).R c x = _
        rw [hgFExt_eq hkl]; exact h3 x
      · rw [(hgFLimCh H').U_g hck']
        show (hgFExt ν (fun β _ => hgFV β) (gpFs ν k)).g c = _
        rw [hgFExt_eq hkl]; exact h4
    · subst heq; rw [e]; exact ⟨fun _ => rfl, rfl⟩

theorem hgFV_B {ν : Ordinal.{0}} (hν : ν < ε₀) : (hgFV ν).B = hgFQ ν := by
  obtain ⟨-, ⟨_, hst⟩, -⟩ := hgF_inv ν hν
  exact hg_B_of_start hst

theorem hgFV_γ {ν : Ordinal.{0}} (hν : ν < ε₀) : (hgFV ν).γ = 0 := (hgF_inv ν hν).1

theorem hgFV_γK (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) : (hgFV ν).γ < Td.tdK S := by
  rw [hgFV_γ hν]; exact hg_K_pos S

/-- **`φ(Ω₁, G+1+ν)` IS LOCATED, EVERY `ν < ε₀`**: `Λ⁺ = ι(Γ(φ(Ω₁, G+1+ν))·ω)`, `P(Γ(φ(Ω₁, G+1+ν))·ω) < L(0)`
(UNCONDITIONAL). -/
theorem hgFV_loc (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    ∃ X : XtSys, XtTopPkg X ∧ xtB1 X = iota S (gcG (hgFQ ν) * ω) ∧
      upsilon (xtB1 X) = Pv S (gcG (hgFQ ν) * ω) ∧ Pv S (gcG (hgFQ ν) * ω) < Nc.ncL S 0 := by
  rw [← hgFV_B hν]; exact hgV_locD (hgFV ν) S (hgFV_γK S hν)

/-- **Theorem BLK^O below `P(Γ(φ(Ω₁, G+1+ν))·ω)`, with the exact reaches**, every `ν < ε₀` (UNCONDITIONAL). -/
theorem hgFV_blk (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    let X := gsX (hgFV ν).step.toRS _ (hgFV ν).E_lt_B.le (hgFV ν).B_lt_NB S (hgV_locD_g (hgFV ν) S (hgFV_γK S hν))
    (∀ c' d, c' < d → d < upsilon (xtB1 X) → (le2 c' d ↔ ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 X ∧
        c' = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧ d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 X →
      (∀ c' < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c' g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec X l)) ∧
    (∀ α < upsilon (xtB1 X), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  hgV_locD_blk (hgFV ν) S (hgFV_γK S hν)

/-! ## The frontier `ι(Γ(φ(Ω₁, G+ε₀)))` -/

/-- **`φ(Ω₁, G+ε₀)`.** -/
noncomputable def hgFE : Ordinal.{0} := veblen Om1 (gcG 0 + ε₀)

theorem hgFE_eq : hgFQ ε₀ = hgFE := by
  unfold hgFQ hgFE; rw [add_assoc, one_add_of_omega0_le (omega0_lt_inE hc_eps0_E).le]

theorem hgFE_lim : IsSuccLimit hgFE := ev_isSuccLimit_of_inE (gg_veblen_eps gv_Om1_pos.ne')

/-- Every ordinal below `φ(Ω₁, G+ε₀)` lies below some `Q_ν`, `ν < ε₀`. -/
theorem hgFE_cofF {β : Ordinal.{0}} (hβ : β < hgFE) : ∃ ν, ν < ε₀ ∧ β < hgFQ ν := by
  rw [← hgFE_eq] at hβ
  obtain ⟨a, ha, hca⟩ := ((isNormal_veblen Om1).lt_iff_exists_lt (isSuccLimit_add _ hc_eps0_lim)).1 hβ
  obtain ⟨t, ht, hat⟩ := (lt_add_iff hc_eps0_lim.bot_lt.ne').1 ha
  refine ⟨t + 1, hc_eps0_lim.add_one_lt ht, hca.trans_le (((isNormal_veblen Om1).monotone hat).trans ?_)⟩
  exact (hgFQ_mono (lt_add_one t)).le

/-- **The located bounds `ι(Γ(Q_ν)·ω)`, `ν < ε₀`, are cofinal below `ι(Γ(φ(Ω₁, G+ε₀)))`.** -/
theorem hgFE_cof (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : l < iota S (gcG hgFE)) :
    ∃ ν, ν < ε₀ ∧ l < iota S (gcG (hgFQ ν) * ω) := by
  have hlim : IsSuccLimit (gcG hgFE) := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (gcG_SC _))
  rw [iota_limit hlim] at hl
  haveI : Nonempty (Iio (gcG hgFE)) := ⟨⟨0, hlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hl
  obtain ⟨β, hβ, heβ⟩ := gcG_lt_of_lt_limit hgFE_lim e.2
  obtain ⟨ν, hν, hβν⟩ := hgFE_cofF hβ
  refine ⟨ν, hν, he.trans_le (iota_mono _ _ ((heβ.trans (gcG_lt hβν)).trans_le ?_).le)⟩
  exact le_mul_of_one_le_right' one_lt_omega0.le

/-- **ENUM-REACH at every range restart below `ι(Γ(φ(Ω₁, G+ε₀)))`, fixed points included** (UNCONDITIONAL). -/
theorem hgFE_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hgFE)) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨ν, hν, h⟩ := hgFE_cof S hl
  rw [← hgFV_B hν] at h
  exact hgV_locD_enum (hgFV ν) S (hgFV_γK S hν) hr h

/-- **CapV at every range restart below `ι(Γ(φ(Ω₁, G+ε₀)))`** (UNCONDITIONAL). -/
theorem hgFE_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG hgFE)) :
    CdCapV S l := by
  obtain ⟨ν, hν, h⟩ := hgFE_cof S hl
  rw [← hgFV_B hν] at h
  exact hgV_locD_capV (hgFV ν) S (hgFV_γK S hν) hr h

/-- **THE ROAD**: UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ(φ(Ω₁, G+ε₀)))` (CapV also `υ_λ < L(ω)`), (CL), EQ,
TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem hgFE_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG hgFE) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG hgFE) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG hgFE) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  gv_road_of S _ (fun _ hr h => hgFE_enum S hr h) (fun _ hr h => hgFE_capV S hr h) hU hL hV hC hEQ hrest hB2

/-- `φ(Ω₁, G+ε₀) < Γ_{Ω₁+2}`. -/
theorem hgFE_lt1 : hgFE < gcG 1 := by
  have hG1 := gcG_SC 1
  have hE := Low.opow_eq_self_of_SC hG1
  have hfix : veblen Om1 (gcG 1) = gcG 1 := gn_veb_fix hG1 (hg_Om1_lt_G 1)
  have h1 : gcG 0 + ε₀ < gcG 1 := (inE_indec hE).add_lt (gcG_lt zero_lt_one) hgF_eps0_lt_G1
  have h2 := (isNormal_veblen Om1).strictMono h1
  rwa [hfix] at h2

/-- **`Γ(φ(Ω₁, G+ε₀)) < Ω₂`.** -/
theorem hgFE_lt_Om2 : gcG hgFE < Om (1 + 1) := by
  have hBE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hO : (Om1 : Ordinal.{0}) < Tf.tfBG := Tf.tfBG_gt
  have h1 : (1 : Ordinal.{0}) < Tf.tfBG := one_lt_omega0.trans (omega0_lt_inE hBE)
  have hG1 : gcG 1 < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) h1)
  have h2 : gcG hgFE < Tf.tfBG := by
    rw [Tf.tf_gcG, ← Tf.tfBG_fix]
    exact gamma_lt_gamma.2 ((inE_indec hBE).add_lt ((inE_indec hBE).add_lt hO h1) (hgFE_lt1.trans hG1))
  exact h2.trans Tf.tfBG_lt_Om2

/-- **`P(Γ(φ(Ω₁, G+ε₀))) < L(0)`.** -/
theorem hgFE_P (S : InaccSeq.{0}) : Pv S (gcG hgFE) < Nc.ncL S 0 := ga_Pv_lt_L0 S hgFE_lt_Om2.le

/-- **The order of the frontiers**: `Γ(φ(K, G+1)) < Γ(φ(Ω₁, G+1)) ≤ Γ(φ(Ω₁, G+1+ν))`,
`ι(Γ(φ(Ω₁, G+1+ν))·ω) ≤ ι(Γ(φ(Ω₁, G+ε₀))) ≤ ι(Ω₂)` for every `ν < ε₀`, and `P(Γ(φ(Ω₁, G+ε₀))) ≤ P(Ω₂) < L(0)`. -/
theorem hgFE_fr_order (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    gcG (hfGE S) < gcG hgB ∧ gcG hgB ≤ gcG (hgFQ ν) ∧
      iota S (gcG (hgFQ ν) * ω) ≤ iota S (gcG hgFE) ∧ iota S (gcG hgFE) ≤ iota S (Om (1 + 1)) ∧
      Pv S (gcG hgFE) ≤ Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hV : InE (gcG hgFE) := Low.opow_eq_self_of_SC (gcG_SC _)
  have hlt : hgFQ ν < hgFE := by rw [← hgFE_eq]; exact hgFQ_mono hν
  refine ⟨(hgU_fr_order S).1, gcG_le (by rw [← hgFQ_zero]; exact hgFQ_mono' zero_le),
    iota_mono _ _ (InE.mul_lt hV (gcG_lt hlt) (omega0_lt_inE hV)).le,
    iota_mono _ _ hgFE_lt_Om2.le, Nm.Pv_mono hgFE_lt_Om2.le, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Hg
