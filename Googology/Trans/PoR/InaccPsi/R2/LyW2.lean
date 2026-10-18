import Googology.Trans.PoR.InaccPsi.R2.XtW2
import Googology.Trans.PoR.InaccPsi.R2.LyPoly
import Googology.Trans.PoR.InaccPsi.R2.LyCmp

/-!
# The limit of the family `xtLL k`: `Λ_{ω²}` is a restart with `lh(ρ) = δ + B(ρ)·ρ^{ω²}`

`lyPB = lyPoly vzLay` (`R2.LyPoly`): the terms `B(x)·Σ x^{aᵢ}·γᵢ + s(x)` (`s` a `φ(n, ·)`-term, `aᵢ, γᵢ` constants),
top `B(x)·x^x`.  It contains the tops `B(x)·x^{ω·k}` of all limit layers `xtLL k` (`R2.XtW2`) as terms, so
(`R2.LyCmp`):

* `lyW2_lt` (**`Λ⁺_k < Λ(lyPB)`**), `lyW2_eq` (`O_{lyPB} = O_{LL k}` below `Λ⁺_k`), `lyW2_le` (`Λ_{ω²} ≤ Λ(lyPB)`);
* `lyW2_ri` (**`Λ_{ω²}` is a restart index**), `lyW2_at` (**`O_{lyPB}(Λ_{ω²}) = B(ρ)·ρ^{ω²}`**, `ρ = ρ_{Λ_{ω²}}`: the
  terms realized cofinally below are bounded by `B(x)·x^{ω·k}`, and `B(x)·x^{ω·k}` is realized at the frontiers of
  `xtLL (k+1)`), `lyW2_lt_Lam` (**`Λ_{ω²} < Λ(lyPB)`**), `lyW2_reach` (**`lh(ρ_{Λ_{ω²}}) = δ + B(ρ)·ρ^{ω²}`**);
* `lyPB_reachT` (**the reach at the frontier of every constant exponent `a`**: `lh(ρ) = δ + B(ρ)·ρ^a` at
  `Λ_a = xtLamT lyPB (B·x^a)`), `lyPB_reachLam` (`lh(ρ) = δ + B(ρ)·ρ^ρ` at `Λ(lyPB)`), `lyPB_reachB1`.

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **The layer of all constant exponents over `B`**: top `B(x)·x^x`. -/
noncomputable def lyPB : XtLay := lyPoly vzLay

theorem vzLay_top (x : Ordinal.{0}) : vzLay.sys.top x = VzB x := rfl

theorem lyPB_top (x : Ordinal.{0}) : lyPB.sys.top x = VzB x * x ^ x := rfl

theorem lyPB_powv (a x : Ordinal.{0}) : lyPB.sys.val (lyPowTm vzLay a) x = VzB x * x ^ a :=
  lyPowTm_val vzLay a x

theorem ly_wk_lt {x : Ordinal.{0}} (hx : InE x) (k : ℕ) : ω * (k : Ordinal.{0}) < x :=
  hx.mul_lt (omega0_lt_inE hx) ((natCast_lt_omega0 k).trans (omega0_lt_inE hx))

theorem ly_wk_lt_ww (k : ℕ) : ω * (k : Ordinal.{0}) < ω * ω :=
  (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 k)

theorem ly_ww_lt {x : Ordinal.{0}} (hx : InE x) : ω * ω < x :=
  hx.mul_lt (omega0_lt_inE hx) (omega0_lt_inE hx)

/-- `lyPB` contains the top `B(x)·x^{ω·k}` of `xtLL k`. -/
theorem lyW2_topIn (k : ℕ) : LyTopIn lyPB.sys (xtLL k).sys := by
  refine ⟨lyPowTm vzLay (ω * (k : Ordinal.{0})), fun x hx _ => ⟨lyPowTm_cb vzLay hx (ly_wk_lt (upsPt_inE hx) k), ?_⟩,
    fun l hl hl1 => ?_⟩
  · rw [lyPB_powv, xtLL_top]
  · have hρE := ups_inE hl
    rw [xtLL_top, lyPB_top]
    exact lyGap vzLay hρE (ups_lt_Om1 l hl1) (ly_wk_lt hρE k)

/-- **`Λ⁺_k < Λ(lyPB)`.** -/
theorem lyW2_lt (k : ℕ) : xtLamK k < xtLam lyPB.sys := lyLamGt (xtLL k).topPkg (lyW2_topIn k)

/-- `O_{lyPB} = O_{LL k}` below `Λ⁺_k`. -/
theorem lyW2_eq (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtLamK k) :
    xtOrec lyPB.sys μ = xtOrec (xtLL k).sys μ := lyEq (xtLL k).topPkg (lyW2_topIn k) hμ h

/-- **`Λ_{ω²} ≤ Λ(lyPB)`.** -/
theorem lyW2_le : xtFamW2.famSup ≤ xtLam lyPB.sys := Ordinal.iSup_le fun k => (lyW2_lt k).le

/-- **`Λ_{ω²}` is a restart index.** -/
theorem lyW2_ri : IsRestartIdx xtFamW2.famSup := by
  refine ri_iff.2 ⟨(lt_of_le_of_lt zero_le (xtFamW2.famBd_lt 0)).ne', xt_ww_dvd_of_cof fun ν hν => ?_⟩
  obtain ⟨k, hk⟩ := xtFamW2.famLt hν
  exact ⟨xtLamK k, xtB1_mult (xtLL k).topPkg, hk, xtFamW2.famBd_lt k⟩

theorem lyLL_lam_gt (m : ℕ) : xtLamK m < xtLam (xtLL (m + 1)).sys := (xtLL m).lim_gt 0

/-- **`O_{lyPB}(Λ_{ω²}) = B(ρ)·ρ^{ω²}`** for `ρ = ρ_{Λ_{ω²}}`. -/
theorem lyW2_at :
    xtOrec lyPB.sys xtFamW2.famSup =
      VzB (upsilon xtFamW2.famSup) * upsilon xtFamW2.famSup ^ (ω * ω) := by
  set l := xtFamW2.famSup with hl
  have hlr := lyW2_ri
  have hl1 : l < Om1 := xtFamW2.famSup_lt_Om1
  have hρE := ups_inE hlr
  set ρ := upsilon l with hρ
  have h1ρ : 1 < ρ := one_lt_omega0.trans (omega0_lt_inE hρE)
  have hB0 : 0 < VzB ρ := hρE.pos.trans (vzB_omega hρE (ups_lt_Om1 l hl1)).2.1
  set t : ℕ → lyPB.sys.Tm := fun k => lyPowTm vzLay (ω * (k : Ordinal.{0})) with ht
  have htv : ∀ k x, lyPB.sys.val (t k) x = VzB x * x ^ (ω * (k : Ordinal.{0})) := fun k x =>
    lyPB_powv _ x
  have htc : ∀ k {x}, UpsPt x → lyPB.sys.CB (t k) x := fun k x hx =>
    lyPowTm_cb vzLay hx (ly_wk_lt (upsPt_inE hx) k)
  -- every `B(ρ)·ρ^{ω·k}` lies below the offset
  have hlow : ∀ k : ℕ, VzB ρ * ρ ^ (ω * (k : Ordinal.{0})) < xtOrec lyPB.sys l := by
    intro k
    have hc : XtCof lyPB.sys (xtOrec lyPB.sys) l (t k) := by
      intro ν hν
      obtain ⟨j, hj⟩ := xtFamW2.famLt hν
      set m := max j k with hm
      have h1 : ν < xtLam (xtLL (m + 1)).sys :=
        hj.trans_le ((xtLamK_strictMono.monotone (le_max_left j k)).trans (lyLL_lam_gt m).le)
      have h2 : xtLam (xtLL (m + 1)).sys < xtLamK (m + 1) := (xtLL (m + 1)).xtLamLt
      have hμ : IsRestartIdx (xtLam (xtLL (m + 1)).sys) := xtLam_ri
      refine ⟨_, hμ, h1, h2.trans (xtFamW2.famBd_lt (m + 1)), htc k (ups_ri hμ), ?_⟩
      rw [htv, lyW2_eq (m + 1) hμ h2, xtOrec_Lam, xtLL_top]
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
    obtain ⟨k, hk⟩ := xtFamW2.famLt hμl
    have hle : lyPB.sys.val s (upsilon μ) ≤ lyPB.sys.val (t k) (upsilon μ) := by
      refine hsμ.trans ?_
      rw [lyW2_eq k hμ hk, htv, ← xtLL_top]
      exact xtOrec_le_top hμ (hk.trans (xtLamK_lt_Om1 k))
    have h2 := (lyPB.sys.uni_le _ _ (ups_ri hμ) (ups_ri hlr) (bases_ri hμ hlr hμl hl1) s (t k) hCBμ
      (htc k (ups_ri hμ))).2 hle
    rw [htv] at h2
    refine h2.trans_lt ((mul_lt_mul_iff_right₀ hB0).2 ((opow_lt_opow_iff_right h1ρ).2 (ly_wk_lt_ww k)))
  · -- the lower bound
    by_contra hlt
    push Not at hlt
    set O := xtOrec lyPB.sys l with hO
    have hq : O / VzB ρ < ρ ^ (ω * ω) := (Ordinal.lt_mul_iff_div_lt hB0.ne').1 hlt
    obtain ⟨c, hc, hqc⟩ := (lt_opow_of_isSuccLimit hρE.pos.ne'
      (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)).1 hq
    have hcω : c / ω < ω := (Ordinal.lt_mul_iff_div_lt omega0_pos.ne').1 hc
    obtain ⟨n, hn⟩ := lt_omega0.1 hcω
    have hcn : c < ω * ((n + 1 : ℕ) : Ordinal.{0}) := by
      have := lt_mul_succ_div c omega0_pos.ne'
      rwa [hn, succ_eq_add_one, show ((n : Ordinal.{0}) + 1) = ((n + 1 : ℕ) : Ordinal.{0}) by push_cast; rfl]
        at this
    have hq2 : O / VzB ρ < ρ ^ (ω * ((n + 1 : ℕ) : Ordinal.{0})) :=
      hqc.trans ((opow_lt_opow_iff_right h1ρ).2 hcn)
    have hO2 : O < VzB ρ * ρ ^ (ω * ((n + 1 : ℕ) : Ordinal.{0})) :=
      calc O = VzB ρ * (O / VzB ρ) + O % VzB ρ := (div_add_mod O _).symm
        _ < VzB ρ * (O / VzB ρ) + VzB ρ := (add_lt_add_iff_left _).2 (mod_lt O hB0.ne')
        _ = VzB ρ * (O / VzB ρ + 1) := (mul_add_one _ _).symm
        _ ≤ VzB ρ * ρ ^ (ω * ((n + 1 : ℕ) : Ordinal.{0})) := mul_le_mul_right (Order.add_one_le_of_lt hq2) _
    exact absurd (hlow (n + 1)) (not_lt.2 hO2.le)

/-- **`Λ_{ω²} < Λ(lyPB)`.** -/
theorem lyW2_lt_Lam : xtFamW2.famSup < xtLam lyPB.sys := by
  refine lyW2_le.lt_of_ne fun e => ?_
  have h := lyW2_at
  rw [e, xtOrec_Lam, lyPB_top] at h
  have hρE := ups_inE (xtLam_ri (X := lyPB.sys))
  have hρ1 := ups_lt_Om1 _ (xtLam_lt_Om1 (X := lyPB.sys))
  have hB0 : 0 < VzB (upsilon (xtLam lyPB.sys)) := hρE.pos.trans (vzB_omega hρE hρ1).2.1
  have h1ρ : 1 < upsilon (xtLam lyPB.sys) := one_lt_omega0.trans (omega0_lt_inE hρE)
  have := (mul_lt_mul_iff_right₀ hB0).2 ((opow_lt_opow_iff_right h1ρ).2 (ly_ww_lt hρE))
  rw [h] at this
  exact lt_irrefl _ this

/-- **The reach at the limit `Λ_{ω²}` of the family `xtLL k`**: `lh(ρ) = δ + B(ρ)·ρ^{ω²}`. -/
theorem lyW2_reach :
    IsReach R2C (upsilon xtFamW2.famSup)
      (upsilon (xtFamW2.famSup + ω + 1) + VzB (upsilon xtFamW2.famSup) * upsilon xtFamW2.famSup ^ (ω * ω)) := by
  rw [← lyW2_at]
  exact xtReach lyW2_ri lyW2_lt_Lam

/-- **The reach at the frontier of every constant exponent `a`**: `lh(ρ) = δ + B(ρ)·ρ^a` at
`Λ_a = xtLamT lyPB (B·x^a)`, for every constant `a < ρ_{Λ(lyPB)}`. -/
theorem lyPB_reachT {a : Ordinal.{0}} (ha : a < upsilon (xtLam lyPB.sys)) :
    IsReach R2C (upsilon (xtLamT lyPB.sys (lyPowTm vzLay a)))
      (upsilon (xtLamT lyPB.sys (lyPowTm vzLay a) + ω + 1) +
        VzB (upsilon (xtLamT lyPB.sys (lyPowTm vzLay a))) *
          upsilon (xtLamT lyPB.sys (lyPowTm vzLay a)) ^ a) := by
  have hU := ups_ri (xtLam_ri (X := lyPB.sys))
  have hCB := lyPowTm_cb vzLay hU ha
  have h1 : 1 ≤ lyPB.sys.val (lyPowTm vzLay a) (upsilon (xtLam lyPB.sys)) := by
    rw [lyPB_powv]
    have hρE := upsPt_inE hU
    exact (one_le_iff_pos.2 (hρE.pos.trans (vzB_omega hρE (ups_lt_Om1 _ xtLam_lt_Om1)).2.1)).trans
      (le_mul_left _ (opow_pos _ hρE.pos))
  have := xtReach_LamT hCB h1
  rw [lyPowTm_val, vzLay_top] at this
  exact this

/-- **The reach at the frontier of `lyPB`**: `lh(ρ) = δ + B(ρ)·ρ^ρ`. -/
theorem lyPB_reachLam :
    IsReach R2C (upsilon (xtLam lyPB.sys))
      (upsilon (xtLam lyPB.sys + ω + 1) + VzB (upsilon (xtLam lyPB.sys)) * upsilon (xtLam lyPB.sys) ^
        upsilon (xtLam lyPB.sys)) := by
  rw [← lyPB_top, ← xtOrec_Lam]
  exact xtReach1 lyPB.topPkg xtLam_ri lyPB.xtLamLt

end Googology.Trans.PoR.InaccPsi.R2.Ly
