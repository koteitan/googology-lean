import Googology.Trans.PoR.InaccPsi.R2.LgFr2
import Googology.Trans.PoR.InaccPsi.R2.LyW2

/-!
# The limit of the layers over `Γ`: `Λ^Γ_{ω²}` is a restart with `lh(ρ) = δ + Γ(ρ)·ρ^{ω²}`

`lgPB = lyPoly lgLay` (`R2.LyPoly`, generic in the layer): the terms `Γ(x)·Σ x^{aᵢ}·γᵢ + s(x)` (`s` a term of
`lgUSys`, `aᵢ, γᵢ` constants), top `Γ(x)·x^x`.  It contains the tops `Γ(x)·x^{ω·k}` of all limit layers `lgLL k`, so
(`R2.LyCmp`, the proof of `R2.LyW2` with `B` replaced by `Γ`):

* `lgPBW2_lt` (**`Λ⁺(lgLL k) < Λ(lgPB)`**), `lgPBW2_eq` (`O_{lgPB} = O_{LL k}` below `Λ⁺(lgLL k)`), `lgPBW2_le`;
* `lgW2_ri` (**`Λ^Γ_{ω²}` is a restart index**), `lgW2_at` (**`O_{lgPB}(Λ^Γ_{ω²}) = Γ(ρ)·ρ^{ω²}`**), `lgPBW2_lt_Lam`
  (**`Λ^Γ_{ω²} < Λ(lgPB)`**), `lgW2_reach` (**`lh(ρ_{Λ^Γ_{ω²}}) = δ + Γ(ρ)·ρ^{ω²}`**);
* `lgPB_reachT` (**`lh(ρ) = δ + Γ(ρ)·ρ^a` at the frontier of every constant exponent `a`**), `lgPB_reachLam`
  (`lh(ρ) = δ + Γ(ρ)·ρ^ρ` at `Λ(lgPB)`); `lgPB_blk` (**Theorem BLK^O below `υ_{Λ⁺(lgPB)}`**), `lgPB_reach1`,
  `lgPB_init` (**UPPER and LOWER at every non-fixed restart of the range below `Λ⁺(lgPB)`**), `lgPB_capV`.

No new axiom beyond `R2.CitedLg` and `R2.CitedXt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

/-- **The layer of all constant exponents over `B`**: top `B(x)·x^x`. -/
noncomputable def lgPB : XtLay := lyPoly lgLay

theorem lgPB_top (x : Ordinal.{0}) : lgPB.sys.top x = lgG x * x ^ x := rfl

theorem lgPB_powv (a x : Ordinal.{0}) : lgPB.sys.val (lyPowTm lgLay a) x = lgG x * x ^ a :=
  lyPowTm_val lgLay a x

/-- `lgPB` contains the top `B(x)·x^{ω·k}` of `lgLL k`. -/
theorem lgPBW2_topIn (k : ℕ) : LyTopIn lgPB.sys (lgLL k).sys := by
  refine ⟨lyPowTm lgLay (ω * (k : Ordinal.{0})), fun x hx _ => ⟨lyPowTm_cb lgLay hx (ly_wk_lt (upsPt_inE hx) k), ?_⟩,
    fun l hl hl1 => ?_⟩
  · rw [lgPB_powv, lgLL_top]
  · have hρE := ups_inE hl
    rw [lgLL_top, lgPB_top]
    exact lyGap lgLay hρE (ups_lt_Om1 l hl1) (ly_wk_lt hρE k)

/-- **`Λ⁺_k < Λ(lgPB)`.** -/
theorem lgPBW2_lt (k : ℕ) : lgLamK k < xtLam lgPB.sys := lyLamGt (lgLL k).topPkg (lgPBW2_topIn k)

/-- `O_{lgPB} = O_{LL k}` below `Λ⁺_k`. -/
theorem lgPBW2_eq (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < lgLamK k) :
    xtOrec lgPB.sys μ = xtOrec (lgLL k).sys μ := lyEq (lgLL k).topPkg (lgPBW2_topIn k) hμ h

/-- **`Λ_{ω²} ≤ Λ(lgPB)`.** -/
theorem lgPBW2_le : lgFamW2.famSup ≤ xtLam lgPB.sys := Ordinal.iSup_le fun k => (lgPBW2_lt k).le

/-- **`Λ_{ω²}` is a restart index.** -/
theorem lgW2_ri : IsRestartIdx lgFamW2.famSup := by
  refine ri_iff.2 ⟨(lt_of_le_of_lt zero_le (lgFamW2.famBd_lt 0)).ne', xt_ww_dvd_of_cof fun ν hν => ?_⟩
  obtain ⟨k, hk⟩ := lgFamW2.famLt hν
  exact ⟨lgLamK k, xtB1_mult (lgLL k).topPkg, hk, lgFamW2.famBd_lt k⟩

theorem lgLL_lam_gt (m : ℕ) : lgLamK m < xtLam (lgLL (m + 1)).sys := (lgLL m).lim_gt 0

/-- **`O_{lgPB}(Λ_{ω²}) = B(ρ)·ρ^{ω²}`** for `ρ = ρ_{Λ_{ω²}}`. -/
theorem lgW2_at :
    xtOrec lgPB.sys lgFamW2.famSup =
      lgG (upsilon lgFamW2.famSup) * upsilon lgFamW2.famSup ^ (ω * ω) := by
  set l := lgFamW2.famSup with hl
  have hlr := lgW2_ri
  have hl1 : l < Om1 := lgFamW2.famSup_lt_Om1
  have hρE := ups_inE hlr
  set ρ := upsilon l with hρ
  have h1ρ : 1 < ρ := one_lt_omega0.trans (omega0_lt_inE hρE)
  have hB0 : 0 < lgG ρ := hρE.pos.trans (lgG_facts hρE (ups_lt_Om1 l hl1)).2.1
  set t : ℕ → lgPB.sys.Tm := fun k => lyPowTm lgLay (ω * (k : Ordinal.{0})) with ht
  have htv : ∀ k x, lgPB.sys.val (t k) x = lgG x * x ^ (ω * (k : Ordinal.{0})) := fun k x =>
    lgPB_powv _ x
  have htc : ∀ k {x}, UpsPt x → lgPB.sys.CB (t k) x := fun k x hx =>
    lyPowTm_cb lgLay hx (ly_wk_lt (upsPt_inE hx) k)
  -- every `B(ρ)·ρ^{ω·k}` lies below the offset
  have hlow : ∀ k : ℕ, lgG ρ * ρ ^ (ω * (k : Ordinal.{0})) < xtOrec lgPB.sys l := by
    intro k
    have hc : XtCof lgPB.sys (xtOrec lgPB.sys) l (t k) := by
      intro ν hν
      obtain ⟨j, hj⟩ := lgFamW2.famLt hν
      set m := max j k with hm
      have h1 : ν < xtLam (lgLL (m + 1)).sys :=
        hj.trans_le ((lgLamK_strictMono.monotone (le_max_left j k)).trans (lgLL_lam_gt m).le)
      have h2 : xtLam (lgLL (m + 1)).sys < lgLamK (m + 1) := (lgLL (m + 1)).xtLamLt
      have hμ : IsRestartIdx (xtLam (lgLL (m + 1)).sys) := xtLam_ri
      refine ⟨_, hμ, h1, h2.trans (lgFamW2.famBd_lt (m + 1)), htc k (ups_ri hμ), ?_⟩
      rw [htv, lgPBW2_eq (m + 1) hμ h2, xtOrec_Lam, lgLL_top]
      have hμE := ups_inE hμ
      refine mul_le_mul_right (opow_le_opow_right hμE.pos ?_) _
      exact mul_le_mul_right (by exact_mod_cast (le_max_right j k).trans (Nat.le_succ m)) _
    have := lt_xtOrec_of_cof hlr hl1 (htc k (ups_ri hlr)) hc
    rwa [htv] at this
  refine le_antisymm ?_ ?_
  · -- the upper bound
    refine xtOrec_le_of ((one_le_iff_pos.2 hB0).trans (le_mul_left _ (opow_pos _ hρE.pos)))
      (fun s hCB hcs => ?_)
    obtain ⟨μ, hμ, -, hμl, hCBμ, hsμ⟩ := hcs 0 (pos_iff_ne_zero.2 hlr.1)
    obtain ⟨k, hk⟩ := lgFamW2.famLt hμl
    have hle : lgPB.sys.val s (upsilon μ) ≤ lgPB.sys.val (t k) (upsilon μ) := by
      refine hsμ.trans ?_
      rw [lgPBW2_eq k hμ hk, htv, ← lgLL_top]
      exact xtOrec_le_top hμ (hk.trans (lgLamK_lt_Om1 k))
    have h2 := (lgPB.sys.uni_le _ _ (ups_ri hμ) (ups_ri hlr) (bases_ri hμ hlr hμl hl1) s (t k) hCBμ
      (htc k (ups_ri hμ))).2 hle
    rw [htv] at h2
    refine h2.trans_lt ((mul_lt_mul_iff_right₀ hB0).2 ((opow_lt_opow_iff_right h1ρ).2 (ly_wk_lt_ww k)))
  · -- the lower bound
    by_contra hlt
    push Not at hlt
    set O := xtOrec lgPB.sys l with hO
    have hq : O / lgG ρ < ρ ^ (ω * ω) := (Ordinal.lt_mul_iff_div_lt hB0.ne').1 hlt
    obtain ⟨c, hc, hqc⟩ := (lt_opow_of_isSuccLimit hρE.pos.ne'
      (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)).1 hq
    have hcω : c / ω < ω := (Ordinal.lt_mul_iff_div_lt omega0_pos.ne').1 hc
    obtain ⟨n, hn⟩ := lt_omega0.1 hcω
    have hcn : c < ω * ((n + 1 : ℕ) : Ordinal.{0}) := by
      have := lt_mul_succ_div c omega0_pos.ne'
      rwa [hn, succ_eq_add_one, show ((n : Ordinal.{0}) + 1) = ((n + 1 : ℕ) : Ordinal.{0}) by push_cast; rfl]
        at this
    have hq2 : O / lgG ρ < ρ ^ (ω * ((n + 1 : ℕ) : Ordinal.{0})) :=
      hqc.trans ((opow_lt_opow_iff_right h1ρ).2 hcn)
    have hO2 : O < lgG ρ * ρ ^ (ω * ((n + 1 : ℕ) : Ordinal.{0})) :=
      calc O = lgG ρ * (O / lgG ρ) + O % lgG ρ := (div_add_mod O _).symm
        _ < lgG ρ * (O / lgG ρ) + lgG ρ := (add_lt_add_iff_left _).2 (mod_lt O hB0.ne')
        _ = lgG ρ * (O / lgG ρ + 1) := (mul_add_one _ _).symm
        _ ≤ lgG ρ * ρ ^ (ω * ((n + 1 : ℕ) : Ordinal.{0})) := mul_le_mul_right (Order.add_one_le_of_lt hq2) _
    exact absurd (hlow (n + 1)) (not_lt.2 hO2.le)

/-- **`Λ_{ω²} < Λ(lgPB)`.** -/
theorem lgPBW2_lt_Lam : lgFamW2.famSup < xtLam lgPB.sys := by
  refine lgPBW2_le.lt_of_ne fun e => ?_
  have h := lgW2_at
  rw [e, xtOrec_Lam, lgPB_top] at h
  have hρE := ups_inE (xtLam_ri (X := lgPB.sys))
  have hρ1 := ups_lt_Om1 _ (xtLam_lt_Om1 (X := lgPB.sys))
  have hB0 : 0 < lgG (upsilon (xtLam lgPB.sys)) := hρE.pos.trans (lgG_facts hρE hρ1).2.1
  have h1ρ : 1 < upsilon (xtLam lgPB.sys) := one_lt_omega0.trans (omega0_lt_inE hρE)
  have := (mul_lt_mul_iff_right₀ hB0).2 ((opow_lt_opow_iff_right h1ρ).2 (ly_ww_lt hρE))
  rw [h] at this
  exact lt_irrefl _ this

/-- **The reach at the limit `Λ_{ω²}` of the family `lgLL k`**: `lh(ρ) = δ + B(ρ)·ρ^{ω²}`. -/
theorem lgW2_reach :
    IsReach R2C (upsilon lgFamW2.famSup)
      (upsilon (lgFamW2.famSup + ω + 1) + lgG (upsilon lgFamW2.famSup) * upsilon lgFamW2.famSup ^ (ω * ω)) := by
  rw [← lgW2_at]
  exact xtReach lgW2_ri lgPBW2_lt_Lam

/-- **The reach at the frontier of every constant exponent `a`**: `lh(ρ) = δ + B(ρ)·ρ^a` at
`Λ_a = xtLamT lgPB (B·x^a)`, for every constant `a < ρ_{Λ(lgPB)}`. -/
theorem lgPB_reachT {a : Ordinal.{0}} (ha : a < upsilon (xtLam lgPB.sys)) :
    IsReach R2C (upsilon (xtLamT lgPB.sys (lyPowTm lgLay a)))
      (upsilon (xtLamT lgPB.sys (lyPowTm lgLay a) + ω + 1) +
        lgG (upsilon (xtLamT lgPB.sys (lyPowTm lgLay a))) *
          upsilon (xtLamT lgPB.sys (lyPowTm lgLay a)) ^ a) := by
  have hU := ups_ri (xtLam_ri (X := lgPB.sys))
  have hCB := lyPowTm_cb lgLay hU ha
  have h1 : 1 ≤ lgPB.sys.val (lyPowTm lgLay a) (upsilon (xtLam lgPB.sys)) := by
    rw [lgPB_powv]
    have hρE := upsPt_inE hU
    exact (one_le_iff_pos.2 (hρE.pos.trans (lgG_facts hρE (ups_lt_Om1 _ xtLam_lt_Om1)).2.1)).trans
      (le_mul_left _ (opow_pos _ hρE.pos))
  have := xtReach_LamT hCB h1
  rw [lyPowTm_val] at this
  exact this

/-- **The reach at the frontier of `lgPB`**: `lh(ρ) = δ + B(ρ)·ρ^ρ`. -/
theorem lgPB_reachLam :
    IsReach R2C (upsilon (xtLam lgPB.sys))
      (upsilon (xtLam lgPB.sys + ω + 1) + lgG (upsilon (xtLam lgPB.sys)) * upsilon (xtLam lgPB.sys) ^
        upsilon (xtLam lgPB.sys)) := by
  rw [← lgPB_top, ← xtOrec_Lam]
  exact xtReach1 lgPB.topPkg xtLam_ri lgPB.xtLamLt

/-! ## Up to `Λ⁺(lgPB)` -/

/-- **Theorem BLK^O below `υ_{Λ⁺(lgPB)}`** in `R₂^C`. -/
theorem lgPB_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lgPB.sys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lgPB.sys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lgPB.sys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lgPB.sys l)) ∧
    (∀ α < upsilon (xtB1 lgPB.sys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lgPB.topPkg

/-- **The exact reach of every restart below `Λ⁺(lgPB)`**. -/
theorem lgPB_reach1 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lgPB.sys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lgPB.sys l) :=
  xtReach1 lgPB.topPkg hl hlB

theorem lgPB_nonfix : XtNonfix (xtOrec lgPB.sys) (xtB1 lgPB.sys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lgPB.topPkg))

theorem lgW2_lt_PB : lgFamW2.famSup < xtB1 lgPB.sys := lgPBW2_lt_Lam.trans lgPB.xtLamLt

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every non-fixed restart of the range below `Λ⁺(lgPB)`.** -/
theorem lgPB_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lgPB.sys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lgPB.topPkg) lgPB_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lgPB)`.** -/
theorem lgPB_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lgPB.sys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lgPB.topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1) (lgPB_nonfix l hr.1 hww hfix hl)

/-- **Below `Λ⁺(lgPB)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O_{lgPB}(λ)`.** -/
theorem lgPB_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lgPB.sys) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lgPB.sys l) :=
  xtExact_iff (xtSpec1 lgPB.topPkg) hl hlB

end Googology.Trans.PoR.InaccPsi.R2
