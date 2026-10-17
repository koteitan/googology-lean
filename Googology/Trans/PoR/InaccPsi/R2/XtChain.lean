import Googology.Trans.PoR.InaccPsi.R2.XtLay

/-!
# The chain of layers past `cpB1 = Λ_B⁺`: `Λ_n⁺ < Λ_{n+1}⁺`, the offsets and reaches at the new restarts

For a layer `L` (`R2.XtLay`) with top `T`, offset `O = xtOrec L.sys`, frontier `Λ = xtLam L.sys` (the least `λ` with
`O(λ) = T(ρ_λ)`) and first limit of frontiers `Λ⁺ = xtB1 L.sys`, and the next layer `L.xtNext` (terms `T(x)·γ + s`,
offset `O'`):

* `XtLay.topPkg` (the top has an IMG package), `XtLay.xtLamLt` (**`Λ < Λ⁺`**);
* `XtLay.xtEq` (**`O' = O` below `Λ⁺`**), `XtLay.xtLtNext` (**`Λ⁺ < Λ'`**, the frontier of the next layer),
  `XtLay.atB1` (**`O'(Λ⁺) = T(ρ) + 1`**), `XtLay.reachB1` (**`lh(ρ_{Λ⁺}) = δ + T(ρ) + 1`**), `XtLay.B1_lt`.

For the layers `xtLayN n` (top `B(x)·x^n`), `Λ_n⁺ = xtLamN n`, `O_n = xtOrec (xtLayN n).sys`:

* `xtLamN_zero` (**`Λ_0⁺ = cpB1`**), `xtLamN_lt` (**`Λ_n⁺ < Λ_{n+1}⁺`**), `xtLayN_eq` (`O_m = O_n` below `Λ_n⁺`,
  `n ≤ m`);
* `xtLayN_atB1` (**`O_{n+1}(Λ_n⁺) = B(ρ)·ρ^n + 1`**, `ρ = ρ_{Λ_n⁺}`), `xtLayN_reachB1` (the reach there),
  `xtCp_reach` (**`lh(ρ_{cpB1}) = δ + B(ρ) + 1`**), `xtLayN_reachLam` (**`lh(ρ_{Λ_{n}}) = δ + B(ρ)·ρ^n`** at the
  frontier of the `n`-th layer);

No new axiom beyond `R2.CitedXt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

namespace XtLay

variable (L : XtLay)

/-- **The top of a layer has an IMG package.** -/
theorem topPkg : XtTopPkg L.sys := fun _ _ _ R => by
  obtain ⟨W, Z, hw, hTW, hI⟩ := L.top_wit _ _ _ R
  have hρE := R.ρE
  have hρ1 := R.ρ1
  exact ⟨(one_le_iff_pos.2 hρE.pos).trans (L.top_gt _ hρE hρ1).le,
    L.top_lt_ups _ _ hρE hρ1 R.ρδ R.next.2.1, W, Z, hw, Finset.mem_union_left _ hTW,
    fun A f hW hZ C => (hI A f hW hZ C).2⟩

/-- **`Λ < Λ⁺`.** -/
theorem xtLamLt : xtLam L.sys < xtB1 L.sys := by
  obtain ⟨h0, hc⟩ := xtB1_spec L.topPkg
  obtain ⟨μ, ⟨hμ, hfr⟩, -, hμB⟩ := hc 0 h0
  exact (xtLam_le hμ hfr).trans_lt hμB

theorem B1_ri : IsRestartIdx (xtB1 L.sys) :=
  ri_iff.2 ⟨(xtB1_spec L.topPkg).1.ne', xtB1_mult L.topPkg⟩

/-- The term `T(x)` of the next layer. -/
def xtTTop : L.xtNext.sys.Tm := ((1 : Ordinal.{0}), L.sys.cst 0)

theorem val_xtTTop (x : Ordinal.{0}) : L.xtNext.sys.val L.xtTTop x = L.sys.top x := by
  show L.nval (1, L.sys.cst 0) x = _
  simp [nval, L.sys.val_cst]

theorem cb_xtTTop {x : Ordinal.{0}} (hx : UpsPt x) : L.xtNext.sys.CB L.xtTTop x :=
  (⟨one_lt_of_upsPt hx, L.sys.cb_cstI 0 x hx.1⟩ : L.nCB (1, L.sys.cst 0) x)

theorem next_top (x : Ordinal.{0}) : L.xtNext.sys.top x = L.sys.top x * x := rfl

/-- The offset of the next layer is at most `T(ρ) + 1` when it is at most `T(ρ_μ)` below. -/
theorem xtLeSucc {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hbd : ∀ μ, IsRestartIdx μ → μ < l → xtOrec L.xtNext.sys μ ≤ L.sys.top (upsilon μ)) :
    xtOrec L.xtNext.sys l ≤ L.sys.top (upsilon l) + 1 := by
  refine xtOrec_le_of le_add_self (fun s hCB hc => ?_)
  obtain ⟨μ, hμ, -, hμl, hCBμ, hsμ⟩ := hc 0 (pos_iff_ne_zero.2 hl.1)
  have h1 : L.xtNext.sys.val s (upsilon μ) ≤ L.xtNext.sys.val L.xtTTop (upsilon μ) := by
    rw [val_xtTTop]; exact hsμ.trans (hbd μ hμ hμl)
  have h2 := (L.xtNext.sys.uni_le _ _ (ups_ri hμ) (ups_ri hl) (bases_ri hμ hl hμl hl1) s L.xtTTop hCBμ
    (L.cb_xtTTop (ups_ri hμ))).2 h1
  rw [val_xtTTop] at h2
  exact Order.lt_add_one_iff.2 h2

theorem eq_min {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < xtB1 L.sys)
    (h2 : μ < xtLam L.xtNext.sys) : xtOrec L.xtNext.sys μ = xtOrec L.sys μ :=
  xt_off_eq xtSpecLam (xtSpec1 L.topPkg) hμ h2 h1

/-- **`Λ⁺ < Λ'`**: the first limit of frontiers lies below the frontier of the next layer. -/
theorem xtLtNext : xtB1 L.sys < xtLam L.xtNext.sys := by
  by_contra hle
  push Not at hle
  have hL := xtLam_ri (X := L.xtNext.sys)
  have hL1 := xtLam_lt_Om1 (X := L.xtNext.sys)
  set Λ' := xtLam L.xtNext.sys with hΛ'
  have hbd : ∀ μ, IsRestartIdx μ → μ < Λ' → xtOrec L.xtNext.sys μ ≤ L.sys.top (upsilon μ) :=
    fun μ hμ hμL => by
      rw [L.eq_min hμ (hμL.trans_le hle) hμL]
      exact xtOrec_le_top hμ (hμL.trans hL1)
  have h1 := L.xtLeSucc hL hL1 hbd
  have h2 : xtOrec L.xtNext.sys Λ' = L.sys.top (upsilon Λ') * upsilon Λ' := xtOrec_Lam
  have hρE := ups_inE hL
  have hρ1 := ups_lt_Om1 Λ' hL1
  have hρT := L.top_gt _ hρE hρ1
  have h1T : (1 : Ordinal.{0}) < L.sys.top (upsilon Λ') := (one_lt_of_upsPt (ups_ri hL)).trans hρT
  have h2ρ : (2 : Ordinal.{0}) ≤ upsilon Λ' := by
    have := Order.add_one_le_of_lt (one_lt_of_upsPt (ups_ri hL)); rwa [one_add_one_eq_two] at this
  have h3 : L.sys.top (upsilon Λ') + 1 < L.sys.top (upsilon Λ') * upsilon Λ' :=
    calc L.sys.top (upsilon Λ') + 1 < L.sys.top (upsilon Λ') + L.sys.top (upsilon Λ') :=
          (add_lt_add_iff_left _).2 h1T
      _ = L.sys.top (upsilon Λ') * 2 := (Ordinal.mul_two _).symm
      _ ≤ L.sys.top (upsilon Λ') * upsilon Λ' := mul_le_mul_right h2ρ _
  rw [h2] at h1
  exact absurd h1 (not_le.2 h3)

/-- **`O' = O` below `Λ⁺`.** -/
theorem xtEq {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h1 : μ < xtB1 L.sys) :
    xtOrec L.xtNext.sys μ = xtOrec L.sys μ :=
  L.eq_min hμ h1 (h1.trans L.xtLtNext)

/-- **`O'(Λ⁺) = T(ρ) + 1`.** -/
theorem atB1 : xtOrec L.xtNext.sys (xtB1 L.sys) = L.sys.top (upsilon (xtB1 L.sys)) + 1 := by
  have hl := L.B1_ri
  have hl1 := xtB1_lt_Om1 L.topPkg
  refine le_antisymm (L.xtLeSucc hl hl1 fun μ hμ hμl => ?_) ?_
  · rw [L.xtEq hμ hμl]; exact xtOrec_le_top hμ (hμl.trans hl1)
  · have hc : XtCof L.xtNext.sys (xtOrec L.xtNext.sys) (xtB1 L.sys) L.xtTTop := by
      intro ν hν
      obtain ⟨μ, ⟨hμ, hfr⟩, h1, h2⟩ := (xtB1_spec L.topPkg).2 ν hν
      refine ⟨μ, hμ, h1, h2, L.cb_xtTTop (ups_ri hμ), ?_⟩
      rw [val_xtTTop, L.xtEq hμ h2, hfr]
    have := lt_xtOrec_of_cof hl hl1 (L.cb_xtTTop (ups_ri hl)) hc
    rw [val_xtTTop] at this
    exact Order.add_one_le_of_lt this

/-- **`Λ⁺ < Λ'⁺`.** -/
theorem B1_lt : xtB1 L.sys < xtB1 L.xtNext.sys := L.xtLtNext.trans L.xtNext.xtLamLt

/-- **The reach at `Λ⁺`**: `lh(ρ) = δ + T(ρ) + 1`. -/
theorem reachB1 :
    IsReach R2C (upsilon (xtB1 L.sys))
      (upsilon (xtB1 L.sys + ω + 1) + (L.sys.top (upsilon (xtB1 L.sys)) + 1)) := by
  rw [← L.atB1]
  exact xtReach1 L.xtNext.topPkg L.B1_ri L.B1_lt

end XtLay

/-! ## The layers `xtLayN n` -/

/-- `Λ_n⁺`: the first limit of the frontiers of the `n`-th layer. -/
noncomputable def xtLamN (n : ℕ) : Ordinal.{0} := xtB1 (xtLayN n).sys

/-- **`Λ_0⁺ = cpB1`** (`Λ_B⁺`). -/
theorem xtLamN_zero : xtLamN 0 = Cp.cpB1 := xtVz_B1

theorem xtLamN_lt (n : ℕ) : xtLamN n < xtLamN (n + 1) := (xtLayN n).B1_lt

theorem xtLamN_strictMono : StrictMono xtLamN := strictMono_nat_of_lt_succ xtLamN_lt

theorem xtLamN_spec (n : ℕ) : OffSpecGen (xtOrec (xtLayN n).sys) (xtLamN n) := xtSpec1 (xtLayN n).topPkg

theorem xtLamN_ri (n : ℕ) : IsRestartIdx (xtLamN n) := (xtLayN n).B1_ri

/-- `O_m = O_n` below `Λ_n⁺` for `n ≤ m`. -/
theorem xtLayN_eq {n m : ℕ} (h : n ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμn : μ < xtLamN n) :
    xtOrec (xtLayN m).sys μ = xtOrec (xtLayN n).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    rw [← ih]
    exact (xtLayN m).xtEq hμ (hμn.trans_le (xtLamN_strictMono.monotone hnm))

/-- **`O_{n+1}(Λ_n⁺) = B(ρ)·ρ^n + 1`** for `ρ = ρ_{Λ_n⁺}`. -/
theorem xtLayN_atB1 (n : ℕ) :
    xtOrec (xtLayN (n + 1)).sys (xtLamN n) =
      VzB (upsilon (xtLamN n)) * upsilon (xtLamN n) ^ (n : Ordinal.{0}) + 1 := by
  rw [← xtLayN_top]; exact (xtLayN n).atB1

/-- **The reach at `Λ_n⁺`**: `lh(ρ) = δ + B(ρ)·ρ^n + 1`. -/
theorem xtLayN_reachB1 (n : ℕ) :
    IsReach R2C (upsilon (xtLamN n))
      (upsilon (xtLamN n + ω + 1) + (VzB (upsilon (xtLamN n)) * upsilon (xtLamN n) ^ (n : Ordinal.{0}) + 1)) := by
  rw [← xtLayN_top]; exact (xtLayN n).reachB1

/-- **The reach at `Λ_B⁺ = cpB1`**: `lh(ρ) = δ + B(ρ) + 1`. -/
theorem xtCp_reach :
    IsReach R2C (upsilon Cp.cpB1) (upsilon (Cp.cpB1 + ω + 1) + (VzB (upsilon Cp.cpB1) + 1)) := by
  have h := xtLayN_reachB1 0
  rw [xtLamN_zero] at h
  simpa using h

/-- **The reach at the frontier `Λ_n` of the `n`-th layer**: `lh(ρ) = δ + B(ρ)·ρ^n`. -/
theorem xtLayN_reachLam (n : ℕ) :
    IsReach R2C (upsilon (xtLam (xtLayN n).sys))
      (upsilon (xtLam (xtLayN n).sys + ω + 1) +
        VzB (upsilon (xtLam (xtLayN n).sys)) * upsilon (xtLam (xtLayN n).sys) ^ (n : Ordinal.{0})) := by
  rw [← xtLayN_top, ← xtOrec_Lam]
  exact xtReach1 (xtLayN n).topPkg xtLam_ri (xtLayN n).xtLamLt

end Googology.Trans.PoR.InaccPsi.R2.Xt
