import Googology.Trans.PoR.InaccPsi.R2.QcAt
import Googology.Trans.PoR.InaccPsi.R2.ZbCnt

/-!
# QcCnt: THE CODES OF `UcCl y` ARE COUNTABLY MANY — `ZbTh qcU`

As `Zb.zbSt`, `Zb.zbTl_cnt`, `Zb.zbU_th` for the codes below `X`:

* `qcLvSt` (the stages of the levels with components in `C`: `Ω₂^e·d + r`), `qcLvSt_cnt`, `qc_lev_mem` (**a level
  `γ < E₂` with all components in `C` is in a stage**);
* `qcSt` (the stages of `UcCl y`: `+`, `φ`, the codes of `TlCl y`, `H_γ(z)`), `qcSt_cnt`, `qc_comps_St` (the
  components of a level in one stage), `qc_mem_St`, `qc_cnt` (**the codes of `UcCl y` are countably many** for
  `y < Ω₁`), `qcU_cnt`, `qcU_th` (**`ZbTh qcU`**).

No new axiom.  New definitions: `qcLvSt`, `qcSt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gc

/-- **The stages of the levels with components in `C`.** -/
def qcLvSt (C : Set Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => C
  | k + 1 => qcLvSt C k ∪ image2 (· + ·) (image2 (fun e d => OmTwo ^ e * d) (qcLvSt C k) C) (qcLvSt C k)

theorem qcLvSt_cnt {C : Set Ordinal.{0}} (hC : C.Countable) : ∀ k, (qcLvSt C k).Countable
  | 0 => hC
  | k + 1 => (qcLvSt_cnt hC k).union (((qcLvSt_cnt hC k).image2 hC _).image2 (qcLvSt_cnt hC k) _)

theorem qcLvSt_mono {C : Set Ordinal.{0}} {k m : ℕ} (h : k ≤ m) : qcLvSt C k ⊆ qcLvSt C m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans fun _ hx => Or.inl hx

/-- **A level `γ < E₂` with every component in `C` lies in a stage.** -/
theorem qc_lev_mem {C : Set Ordinal.{0}} : ∀ γ, γ < ucE → (∀ d ∈ ucComps γ, d ∈ C) → ∃ k, γ ∈ qcLvSt C k := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE hC
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1] at hC
    exact ⟨0, hC γ rfl⟩
  · rw [ucComps_big (not_lt.1 h1) hγE] at hC
    have hlog := uc_log_lt (not_lt.1 h1) hγE
    have hmod := uc_mod_lt (not_lt.1 h1)
    obtain ⟨k1, h1'⟩ := IH _ hlog (hlog.trans hγE) fun d hd => hC d (Or.inl hd)
    obtain ⟨k2, h2'⟩ := IH _ hmod (hmod.trans hγE) fun d hd => hC d (Or.inr (Or.inr hd))
    have hd : γ / OmTwo ^ log OmTwo γ ∈ C := hC _ (Or.inr (Or.inl rfl))
    refine ⟨max k1 k2 + 1, Or.inr ⟨_, ⟨_, qcLvSt_mono (le_max_left _ _) h1', _, hd, rfl⟩, _,
      qcLvSt_mono (le_max_right _ _) h2', ?_⟩⟩
    exact uc_cnf_eq γ

/-- **The stages of the codes of `UcCl y`.** -/
def qcSt (y : Ordinal.{0}) : ℕ → Set Ordinal.{0}
  | 0 => Iio y ∪ {Om1} ∪ {x | TlCl y x}
  | n + 1 => qcSt y n ∪ (image2 (· + ·) (qcSt y n) (qcSt y n) ∪
      (image2 veblen (qcSt y n) (qcSt y n) ∪
        image2 ucH (⋃ k, qcLvSt (qcSt y n) k) (qcSt y n)))

theorem qcSt_cnt {y : Ordinal.{0}} (hy : y < Om 1) : ∀ n, (qcSt y n).Countable
  | 0 => by
    haveI := gc_countable hy
    exact ((Set.countable_coe_iff.1 inferInstance).union (Set.countable_singleton _)).union (zbTl_cnt hy)
  | n + 1 => by
    have h := qcSt_cnt hy n
    exact h.union ((h.image2 h _).union ((h.image2 h _).union
      ((Set.countable_iUnion (qcLvSt_cnt h)).image2 h _)))

theorem qcSt_mono {y : Ordinal.{0}} {n m : ℕ} (h : n ≤ m) : qcSt y n ⊆ qcSt y m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans fun _ hx => Or.inl hx

/-- **The components of a level, each in some stage, are in one stage.** -/
theorem qc_comps_St {y : Ordinal.{0}} :
    ∀ γ, (∀ x ∈ ucComps γ, ∃ n, x ∈ qcSt y n) → ∃ n, ∀ x ∈ ucComps γ, x ∈ qcSt y n := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1] at h ⊢
    obtain ⟨n, hn⟩ := h γ rfl
    exact ⟨n, fun x hx => by rw [mem_singleton_iff.1 hx]; exact hn⟩
  by_cases h2 : γ < ucE
  · rw [ucComps_big (not_lt.1 h1) h2] at h ⊢
    obtain ⟨n1, g1⟩ := IH _ (uc_log_lt (not_lt.1 h1) h2) fun x hx => h x (Or.inl hx)
    obtain ⟨n2, g2⟩ := h (γ / OmTwo ^ log OmTwo γ) (Or.inr (Or.inl rfl))
    obtain ⟨n3, g3⟩ := IH _ (uc_mod_lt (not_lt.1 h1)) fun x hx => h x (Or.inr (Or.inr hx))
    refine ⟨max n1 (max n2 n3), fun x hx => ?_⟩
    rcases hx with hx | rfl | hx
    · exact qcSt_mono (le_max_left _ _) (g1 x hx)
    · exact qcSt_mono ((le_max_left _ _).trans (le_max_right _ _)) g2
    · exact qcSt_mono ((le_max_right _ _).trans (le_max_right _ _)) (g3 x hx)
  · rw [ucComps_out (not_lt.1 h2)]
    exact ⟨0, fun _ hx => absurd hx (Set.notMem_empty _)⟩

/-- **Every code of `UcCl y` lies in a stage.** -/
theorem qc_mem_St {y x : Ordinal.{0}} (hx : UcCl y x) : ∃ n, x ∈ qcSt y n := by
  induction hx with
  | small h => exact ⟨0, Or.inl (Or.inl h)⟩
  | om => exact ⟨0, Or.inl (Or.inr rfl)⟩
  | tl h => exact ⟨0, Or.inr h⟩
  | @add a b _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inl ⟨a, qcSt_mono (le_max_left _ _) h1, b, qcSt_mono (le_max_right _ _) h2,
      rfl⟩)⟩
  | @phi a b _ _ iha ihb =>
    obtain ⟨n1, h1⟩ := iha
    obtain ⟨n2, h2⟩ := ihb
    exact ⟨max n1 n2 + 1, Or.inr (Or.inr (Or.inl ⟨a, qcSt_mono (le_max_left _ _) h1, b,
      qcSt_mono (le_max_right _ _) h2, rfl⟩))⟩
  | @hatom γ z hγ _ _ _ ihc ihz =>
    obtain ⟨n1, h1⟩ := qc_comps_St γ ihc
    obtain ⟨n2, h2⟩ := ihz
    obtain ⟨k, hk⟩ := qc_lev_mem γ hγ h1
    have hk' : γ ∈ ⋃ k, qcLvSt (qcSt y (max n1 n2)) k := by
      refine Set.mem_iUnion.2 ⟨k, ?_⟩
      have hsub : ∀ k', qcLvSt (qcSt y n1) k' ⊆ qcLvSt (qcSt y (max n1 n2)) k' := by
        intro k'
        induction k' with
        | zero => exact qcSt_mono (le_max_left _ _)
        | succ k' ih =>
          rintro w (hw | ⟨a, ⟨e, he, d, hd, rfl⟩, b, hb, rfl⟩)
          · exact Or.inl (ih hw)
          · exact Or.inr ⟨_, ⟨e, ih he, d, qcSt_mono (le_max_left _ _) hd, rfl⟩, b, ih hb, rfl⟩
      exact hsub k hk
    exact ⟨max n1 n2 + 1, Or.inr (Or.inr (Or.inr ⟨γ, hk', z, qcSt_mono (le_max_right _ _) h2, rfl⟩))⟩

/-- **The codes of `UcCl y` are countably many** (`y < Ω₁`). -/
theorem qc_cnt {y : Ordinal.{0}} (hy : y < Om 1) : {x | UcCl y x}.Countable :=
  (Set.countable_iUnion (qcSt_cnt hy)).mono fun _ hx => Set.mem_iUnion.2 (qc_mem_St hx)

/-- **`qcU.At y` is countable** for `y < Ω₁`. -/
theorem qcU_cnt {y : Ordinal.{0}} (hy : y < Om 1) : (qcU.At y).Countable :=
  (qc_cnt hy).mono fun _ hs => hs.2.2.2

/-- **`ZbTh qcU`**: every atom of `qcU` over a countable strongly critical base reads below `Ω₁`. -/
theorem qcU_th : ZbTh qcU := fun y hy hy1 s hs => zb_th_of_cnt hy hy1 (qcU.gxAt y) (qcU_cnt hy1) s hs

end Googology.Trans.PoR.InaccPsi.R2.Qc
