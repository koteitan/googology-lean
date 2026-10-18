import Googology.Trans.PoR.InaccPsi.R2.XtFam
import Googology.Trans.PoR.InaccPsi.R2.LyCmp

/-!
# The offset at the limit of a chain of term systems

For term systems `Y k` (`R2.XtGen`) whose tops have IMG packages, with `Λ⁺(Y k) < Λ(Y (k+1))`, the tops increasing,
and a term system `X` containing every top `top_k` as a term `t k` (`R2.LyCmp`), let `λ = sup_k Λ⁺(Y k)` and `G` with
`top_k(x) < G(x)` and every `v < G(x)` below some `top_k(x)`.  Then (`lyLimAt`) **`λ` is a restart index and
`O_X(λ) = G(ρ_λ)`**: the terms realized cofinally below `λ` are bounded by some `top_k`, and every `top_k` is
realized at the frontiers `Λ(Y m)`, `m > k`.  With `G(ρ_λ) < top_X(ρ_λ)`: `λ < Λ(X)` and
**`lh(ρ_λ) = δ_λ + G(ρ_λ)`** (`lyLimReach`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **A chain of term systems inside `X`.** -/
structure LyChain (X : XtSys) where
  Y : ℕ → XtSys
  pkg : ∀ k, XtTopPkg (Y k)
  inX : ∀ k, LyTopIn X (Y k)
  next : ∀ k, xtB1 (Y k) < xtLam (Y (k + 1))
  topMono : ∀ k x, InE x → x < Om1 → (Y k).top x ≤ (Y (k + 1)).top x

namespace LyChain

variable {X : XtSys} (C : LyChain X)

theorem bd_lt (k : ℕ) : xtB1 (C.Y k) < xtB1 (C.Y (k + 1)) := (C.next k).trans (lyLamLtB1 (C.pkg (k + 1)))

/-- The chain as a family of offset specifications (`R2.XtFam`). -/
noncomputable def fam : XtFam where
  bd := fun k => xtB1 (C.Y k)
  off := fun k => xtOrec (C.Y k)
  spec := fun k => xtSpec1 (C.pkg k)
  mono := C.bd_lt
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (C.pkg k)))

theorem bd_strictMono : StrictMono fun k => xtB1 (C.Y k) := strictMono_nat_of_lt_succ C.bd_lt

theorem top_mono {k m : ℕ} (h : k ≤ m) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (C.Y k).top x ≤ (C.Y m).top x := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (C.topMono m x hx hx1)

/-- **The supremum is a restart index.** -/
theorem sup_ri : IsRestartIdx C.fam.famSup := by
  refine ri_iff.2 ⟨(lt_of_le_of_lt zero_le (C.fam.famBd_lt 0)).ne', xt_ww_dvd_of_cof fun ν hν => ?_⟩
  obtain ⟨k, hk⟩ := C.fam.famLt hν
  exact ⟨xtB1 (C.Y k), xtB1_mult (C.pkg k), hk, C.fam.famBd_lt k⟩

theorem sup_le : C.fam.famSup ≤ xtLam X :=
  Ordinal.iSup_le fun k => (lyLamGt (C.pkg k) (C.inX k)).le

/-- **The offset at the limit**: `O_X(λ) = G(ρ_λ)`. -/
theorem lyLimAt (G : Ordinal.{0} → Ordinal.{0})
    (hG : ∀ k x, InE x → x < Om1 → (C.Y k).top x < G x)
    (hG' : ∀ x, InE x → x < Om1 → ∀ v, v < G x → ∃ k, v < (C.Y k).top x) :
    xtOrec X C.fam.famSup = G (upsilon C.fam.famSup) := by
  classical
  set l := C.fam.famSup with hl
  have hlr := C.sup_ri
  have hl1 : l < Om1 := C.fam.famSup_lt_Om1
  have hρE := ups_inE hlr
  have hρ1 := ups_lt_Om1 l hl1
  choose t ht using fun k => (C.inX k)
  have htc : ∀ k {x}, UpsPt x → x < Om1 → X.CB (t k) x := fun k x hx hx1 => ((ht k).1 x hx hx1).1
  have htv : ∀ k {x}, UpsPt x → x < Om1 → X.val (t k) x = (C.Y k).top x := fun k x hx hx1 =>
    ((ht k).1 x hx hx1).2
  have heq : ∀ k {μ}, IsRestartIdx μ → μ < xtB1 (C.Y k) → xtOrec X μ = xtOrec (C.Y k) μ :=
    fun k μ hμ h => lyEq (C.pkg k) (C.inX k) hμ h
  -- every top lies below the offset
  have hlow : ∀ k : ℕ, (C.Y k).top (upsilon l) < xtOrec X l := by
    intro k
    have hc : XtCof X (xtOrec X) l (t k) := by
      intro ν hν
      obtain ⟨j, hj⟩ := C.fam.famLt hν
      set m := max j k with hm
      have hμ : IsRestartIdx (xtLam (C.Y (m + 1))) := xtLam_ri
      have h1 : ν < xtLam (C.Y (m + 1)) :=
        hj.trans_le ((C.bd_strictMono.monotone (le_max_left j k)).trans (C.next m).le)
      have h2 : xtLam (C.Y (m + 1)) < xtB1 (C.Y (m + 1)) := lyLamLtB1 (C.pkg (m + 1))
      have hμ1 : upsilon (xtLam (C.Y (m + 1))) < Om1 := ups_lt_Om1 _ xtLam_lt_Om1
      refine ⟨_, hμ, h1, h2.trans (C.fam.famBd_lt (m + 1)), htc k (ups_ri hμ) hμ1, ?_⟩
      rw [htv k (ups_ri hμ) hμ1, heq (m + 1) hμ h2, xtOrec_Lam]
      exact C.top_mono ((le_max_right j k).trans (Nat.le_succ m)) (ups_inE hμ) hμ1
    have := lt_xtOrec_of_cof hlr hl1 (htc k (ups_ri hlr) hρ1) hc
    rwa [htv k (ups_ri hlr) hρ1] at this
  refine le_antisymm ?_ ?_
  · refine xtOrec_le_of ((one_le_iff_pos.2 (lt_of_le_of_lt zero_le (hG 0 _ hρE hρ1)))) (fun s hCB hcs => ?_)
    obtain ⟨μ, hμ, -, hμl, hCBμ, hsμ⟩ := hcs 0 (pos_iff_ne_zero.2 hlr.1)
    obtain ⟨k, hk⟩ := C.fam.famLt hμl
    have hμ1 : upsilon μ < Om1 := ups_lt_Om1 μ (hμl.trans hl1)
    have hle : X.val s (upsilon μ) ≤ X.val (t k) (upsilon μ) := by
      refine hsμ.trans ?_
      rw [heq k hμ hk, htv k (ups_ri hμ) hμ1]
      exact xtOrec_le_top hμ (hk.trans (xtB1_lt_Om1 (C.pkg k)))
    have h2 := (X.uni_le _ _ (ups_ri hμ) (ups_ri hlr) (bases_ri hμ hlr hμl hl1) s (t k) hCBμ
      (htc k (ups_ri hμ) hμ1)).2 hle
    rw [htv k (ups_ri hlr) hρ1] at h2
    exact h2.trans_lt (hG k _ hρE hρ1)
  · by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ := hG' _ hρE hρ1 _ hlt
    exact absurd (hlow k) (not_lt.2 hk.le)

/-- **The limit is below the frontier of `X`, and its reach**: `lh(ρ_λ) = δ_λ + G(ρ_λ)`. -/
theorem lyLimReach (G : Ordinal.{0} → Ordinal.{0})
    (hG : ∀ k x, InE x → x < Om1 → (C.Y k).top x < G x)
    (hG' : ∀ x, InE x → x < Om1 → ∀ v, v < G x → ∃ k, v < (C.Y k).top x)
    (hGX : ∀ x, InE x → x < Om1 → G x < X.top x) :
    C.fam.famSup < xtLam X ∧
      IsReach R2C (upsilon C.fam.famSup) (upsilon (C.fam.famSup + ω + 1) + G (upsilon C.fam.famSup)) := by
  have hat := C.lyLimAt G hG hG'
  have hlt : C.fam.famSup < xtLam X := by
    refine C.sup_le.lt_of_ne fun e => ?_
    have h := hat
    rw [e, xtOrec_Lam] at h
    have hρE := ups_inE (xtLam_ri (X := X))
    have hρ1 := ups_lt_Om1 _ (xtLam_lt_Om1 (X := X))
    exact absurd h (hGX _ hρE hρ1).ne'
  refine ⟨hlt, ?_⟩
  rw [← hat]
  exact xtReach C.sup_ri hlt

end LyChain

end Googology.Trans.PoR.InaccPsi.R2.Ly
