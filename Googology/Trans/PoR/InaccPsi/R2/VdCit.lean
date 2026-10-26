import Googology.Trans.PoR.InaccPsi.R2.VdDat
import Googology.Trans.PoR.InaccPsi.R2.CitedVd
import Googology.Trans.PoR.InaccPsi.R2.UlAgree

/-!
# The [W07a] packages at the bound `θ = ψ_{Ω₂}(Ω_ω)` for a fixed `S`, from `R2.CitedVd`

`B₂ = Uc.ucB`, `θ = ConjT.th S`, `Hˡ_γ = Ul.ulH S 1 γ`, `d(x) = vdD S 0 x` (the `K⁽⁰⁾`-datum, `R2.VdDat`).  For a fixed
`S` the data of a level `M < θ` is read by one function, `vdDat S M` (`ucDat M` below `B₂`, `d(M)` from `B₂` on), and
the eight axioms of `R2.CitedVd` become the packages:

* `vdDat`, `vdDat_lt` (**below `B₂` it is `ucDat`**), `vdDat_ge`, `vdDatIn_of`, `vdDat_of_all`, `vd_dat_test` (**for
  every strongly critical `q ≤ Ω₁`: `vdDat S M < q ↔ d(M) < q`**, `M < θ`);
* `VdLtS`, `VdLeS` (**the data of `M` below `v`**: `ucDat M < v` below `B₂`, from `B₂` on `d(M)` below a strongly
  critical `q ≤ v`, resp. below every strongly critical `q ≥ v`), `vd_lt_SC` (**at a strongly critical `q ≤ Ω₁` both are
  `d(M) < q`**);
* `VdCit S` (**the five Lemma 3.30 facts at every level `Ω₁ ≤ M < θ` with the data `vdDat S`, `VdLtS`, `VdLeS`**),
  `vdCit`;
* `VdCitPi S` (**an atom `Hˡ_γ(y) ∈ [B₂, θ)` in normal form is in `Tᵗ[σ]` iff `γ` and `y` are, and then `π(Hˡ_γ(y))
  = Hˡ_{π γ}(π y)`; `φ(a, c)` and `ω^g` below `θ` as in `Uc.UcCitPi`**), `vdCitPi`, `vdAtom_nf` (the same at the
  normal form `vdLev`, `vdI` of a strongly critical `z ∈ [B₂, θ)`).

No new axiom (uses `R2.CitedVd`).  New definitions: `vdDat`, `VdLtS`, `VdLeS`, `VdCit`, `VdCitPi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}}

/-- **The data of a level `M < θ` for a fixed `S`**: `ucDat M` below `B₂`, the `K⁽⁰⁾`-datum from `B₂` on. -/
noncomputable def vdDat (S : InaccSeq.{0}) (M : Ordinal.{0}) : Ordinal.{0} :=
  if M < ucB then ucDat M else vdD S 0 M

theorem vdDat_lt {M : Ordinal.{0}} (h : M < ucB) : vdDat S M = ucDat M := if_pos h

theorem vdDat_ge {M : Ordinal.{0}} (h : ucB ≤ M) : vdDat S M = vdD S 0 M := if_neg (not_lt.2 h)

theorem vdDatIn_of {P : Ordinal.{0} → Prop} {M : Ordinal.{0}} (hM : M < ConjT.th S) (h : P (vdDat S M)) :
    VdDatIn P M := by
  rcases lt_or_ge M ucB with hB | hB
  · rw [vdDat_lt hB] at h; exact vdDatIn_uc hB h
  · rw [vdDat_ge hB] at h; exact vdDatIn_th hB hM h

theorem vdDat_of_all {P : Ordinal.{0} → Prop} {M : Ordinal.{0}} (hM : M < ConjT.th S) (h : VdDatAll P M) :
    P (vdDat S M) := by
  rcases lt_or_ge M ucB with hB | hB
  · rw [vdDat_lt hB]; exact h.1 hB
  · rw [vdDat_ge hB]; exact h.2 S hB hM

/-- **One reading**: `vdDat S M < q ↔ d(M) < q` for every strongly critical `q ≤ Ω₁` (`M < θ`). -/
theorem vd_dat_test {M q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) : vdDat S M < q ↔ vdD S 0 M < q := by
  rcases lt_or_ge M ucB with hB | hB
  · rw [vdDat_lt hB]; exact vd_dat_uc hB hq hq1
  · rw [vdDat_ge hB]

/-- **The data of `M` below `v` for a fixed `S`**: `ucDat M < v` below `B₂`; from `B₂` on, `d(M)` below a strongly
critical `q ≤ v`. -/
def VdLtS (S : InaccSeq.{0}) (M v : Ordinal.{0}) : Prop :=
  if M < ucB then ucDat M < v else ∃ q, SC q ∧ q ≤ v ∧ vdD S 0 M < q

/-- **The data of `M` below `v`, read at the strongly critical points `q ≥ v`** (from `B₂` on). -/
def VdLeS (S : InaccSeq.{0}) (M v : Ordinal.{0}) : Prop :=
  if M < ucB then ucDat M < v else ∀ q, SC q → v ≤ q → vdD S 0 M < q

theorem vdLtIn_of {M v : Ordinal.{0}} (hM : M < ConjT.th S) (h : VdLtS S M v) : VdLtIn M v := by
  unfold VdLtS at h
  rcases lt_or_ge M ucB with hB | hB
  · rw [if_pos hB] at h; exact Or.inl ⟨hB, h⟩
  · rw [if_neg (not_lt.2 hB)] at h; exact Or.inr ⟨S, hB, hM, h⟩

theorem vdLe_of_all {M v : Ordinal.{0}} (hM : M < ConjT.th S) (h : VdLtAll M v) : VdLeS S M v := by
  unfold VdLeS
  rcases lt_or_ge M ucB with hB | hB
  · rw [if_pos hB]; exact h.1 hB
  · rw [if_neg (not_lt.2 hB)]; exact h.2 S hB hM

/-- **At a strongly critical `q ≤ Ω₁` both comparisons are `d(M) < q`.** -/
theorem vd_lt_SC {M q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) :
    (VdLtS S M q ↔ vdD S 0 M < q) ∧ (VdLeS S M q ↔ vdD S 0 M < q) := by
  unfold VdLtS VdLeS
  rcases lt_or_ge M ucB with hB | hB
  · rw [if_pos hB, if_pos hB]; exact ⟨vd_dat_uc hB hq hq1, vd_dat_uc hB hq hq1⟩
  · rw [if_neg (not_lt.2 hB), if_neg (not_lt.2 hB)]
    exact ⟨⟨fun ⟨q', _, hq', h⟩ => h.trans_le hq', fun h => ⟨q, hq, le_rfl, h⟩⟩,
      ⟨fun h => h q hq le_rfl, fun h q' _ hq' => h.trans_le hq'⟩⟩

theorem vd_Om1_lt_B : (Om 1 : Ordinal.{0}) < ucB := by
  have h := Ui.uiB_gt (s := 1); rwa [Ui.ui_one_B] at h

theorem vd_B_lt_th : (ucB : Ordinal.{0}) < ConjT.th S := ul_B_lt_th

/-! ## The five facts -/

/-- **The five Lemma 3.30 facts at every level `Ω₁ ≤ M < θ`** with the data `vdDat S`. -/
structure VdCit (S : InaccSeq.{0}) : Prop where
  mem : ∀ {τ M η : Ordinal.{0}}, InE τ → τ < Om1 → Om1 ≤ M → M < ConjT.th S → vdDat S M ∈ Tset τ →
    η ∈ Tset τ → η < Om1 → Om1 * M + η ∈ Tset τ
  dat : ∀ {τ M η : Ordinal.{0}}, InE τ → τ < Om1 → Om1 ≤ M → M < ConjT.th S → η < Om1 →
    Om1 * M + η ∈ Tset τ → vdDat S M ∈ Tset τ
  vt_lt : ∀ {τ M' η' M η : Ordinal.{0}}, InE τ → τ < Om1 → Om1 ≤ M → M < ConjT.th S → M' ≤ M →
    vdDat S M' ∈ Tset τ → η' ∈ Tset τ → η' < Om1 → vdDat S M ∈ Tset τ → η ∈ Tset τ → η < Om1 →
    Om1 * M' + η' < Om1 * M + η → VdLtS S M' (vt τ (Om1 * M + η)) → η' < vt τ (Om1 * M + η) →
    vt τ (Om1 * M' + η') < vt τ (Om1 * M + η)
  lt_of : ∀ {τ ξ M η : Ordinal.{0}}, InE τ → τ < Om1 → Om1 ≤ M → M < ConjT.th S → ξ ∈ Tset τ → ξ < OmTwo →
    vdDat S M ∈ Tset τ → η ∈ Tset τ → η < Om1 → VdLtS S M (vt τ ξ) → η < vt τ ξ →
    vt τ ξ < vt τ (Om1 * M + η) → ξ < Om1 * M + η
  level : ∀ {τ M η : Ordinal.{0}}, InE τ → τ < Om1 → Om1 ≤ M → M < ConjT.th S → vdDat S M ∈ Tset τ →
    η ∈ Tset τ → η < Om1 → VdLeS S M (vt τ (Om1 * M + η)) ∧ η < vt τ (Om1 * M + η)

/-- **`VdCit S`**, from `R2.CitedVd`. -/
theorem vdCit : VdCit S where
  mem h1 h2 h3 h4 h5 h6 h7 := vdArg_mem h1 h2 h3 (vdDatIn_of h4 h5) h6 h7
  dat h1 h2 h3 h4 h5 h6 := vdDat_of_all h4 (vdArg_dat h1 h2 h3 h5 h6)
  vt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 :=
    vdVt_lt h1 h2 h3 h5 (vdDatIn_of (h5.trans_lt h4) h6) h7 h8 (vdDatIn_of h4 h9) h10 h11 h12
      (vdLtIn_of (h5.trans_lt h4) h13) h14
  lt_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 :=
    vdLt_of_vt_lt h1 h2 h3 h5 h6 (vdDatIn_of h4 h7) h8 h9 (vdLtIn_of h4 h10) h11 h12
  level h1 h2 h3 h4 h5 h6 h7 :=
    have h := vdLevel_lt h1 h2 h3 (vdDatIn_of h4 h5) h6 h7
    ⟨vdLe_of_all h4 h.1, h.2⟩

/-! ## Atoms, `φ(a, c)`, `ω^g` -/

/-- **The base change facts below `θ`**: atoms `Hˡ_γ(y) ∈ [B₂, θ)` in normal form, `ε`-numbers `φ(a, c)` and powers
`ω^g` below `θ`. -/
structure VdCitPi (S : InaccSeq.{0}) : Prop where
  atom : ∀ {σ τ γ y : Ordinal.{0}}, Bases σ τ → γ < Om (1 + 1 + 1) → y < ulH S 1 γ y → ucB ≤ ulH S 1 γ y →
    ulH S 1 γ y < ConjT.th S →
    (ulH S 1 γ y ∈ TB τ σ ↔ γ ∈ TB τ σ ∧ y ∈ TB τ σ) ∧
      (γ ∈ TB τ σ → y ∈ TB τ σ → pi σ τ (ulH S 1 γ y) = ulH S 1 (pi σ τ γ) (pi σ τ y))
  eps : ∀ {σ τ a c : Ordinal.{0}}, Bases σ τ → 1 ≤ a → a < veblen a c → c < veblen a c → Om1 < veblen a c →
    veblen a c < ConjT.th S → (veblen a c ∈ TB τ σ ↔ a ∈ TB τ σ ∧ c ∈ TB τ σ) ∧
      (a ∈ TB τ σ → c ∈ TB τ σ → pi σ τ (veblen a c) = veblen (pi σ τ a) (pi σ τ c))
  opow : ∀ {σ τ g : Ordinal.{0}}, Bases σ τ → Gg.ggE ≤ g → ω ^ g ≠ g → ω ^ g < ConjT.th S →
    (ω ^ g ∈ TB τ σ ↔ g ∈ TB τ σ) ∧ (g ∈ TB τ σ → pi σ τ (ω ^ g) = ω ^ pi σ τ g)

theorem vd_Om1_lt_H (γ y : Ordinal.{0}) : Om1 < ulH S 1 γ y := by
  rw [Rj.rj_Om1]; exact ulH_gt γ y

/-- **`VdCitPi S`**, from `R2.CitedVd`. -/
theorem vdCitPi : VdCitPi S where
  atom {σ τ γ y} hB hγ hy hBz hz := by
    have h := ((vdAtom_TB hB (ulH_SC γ y) (vd_Om1_lt_H γ y)).2 S hBz hz)
    obtain ⟨hl, hi⟩ := vdLev_H (S := S) hγ hy
    rw [hl, hi, vdH_eq] at h
    exact h
  eps hB h1 h2 h3 h4 h5 := vdPhi_TB hB h1 h2 h3 h4 (Or.inr ⟨S, h5⟩)
  opow hB h1 h2 h3 := vdOpow_TB hB h1 h2 (Or.inr ⟨S, h3⟩)

/-- **The atom fact at the normal form of a strongly critical `z ∈ [B₂, θ)`.** -/
theorem vdAtom_nf {σ τ z : Ordinal.{0}} (hB : Bases σ τ) (hzS : SC z) (hBz : ucB ≤ z) (hz : z < ConjT.th S) :
    ulH S 1 (vdLev S z) (vdI S (vdLev S z) z) = z ∧ vdI S (vdLev S z) z < z ∧ vdLev S z < Om (1 + 1 + 1) ∧
    (z ∈ TB τ σ ↔ vdLev S z ∈ TB τ σ ∧ vdI S (vdLev S z) z ∈ TB τ σ) ∧
      (vdLev S z ∈ TB τ σ → vdI S (vdLev S z) z ∈ TB τ σ →
        pi σ τ z = ulH S 1 (pi σ τ (vdLev S z)) (pi σ τ (vdI S (vdLev S z) z))) := by
  have h1 : Om 1 < z := vd_Om1_lt_B.trans_le hBz
  have hne := vd_nf_ex hzS h1 hz
  obtain ⟨hH, hy⟩ := vd_nf hzS h1 hne
  obtain ⟨hlV, -, -, -, -⟩ := vdLev_spec hzS h1 hne
  have h := (vdAtom_TB hB hzS (by rw [Rj.rj_Om1]; exact h1)).2 S hBz hz
  rw [vdH_eq] at h
  exact ⟨hH, hy, hlV, h⟩

end Googology.Trans.PoR.InaccPsi.R2.Vd
