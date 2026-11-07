import Googology.Trans.PoR.InaccPsi.R2.QdFxB

/-!
# QdLvD: THE DATA OF A VEBLEN LEVEL READING BOUNDS THE LEAF READINGS FROM BELOW; THE READING OF `E₂`

The upper bound `ssDat(λ(x)) ≤ max_{d leaf} f d` is in `Qd.qdLv_main`; here the lower bound: **every leaf reading is
at most the data of the reading** (`qdLv_dat_ge`; the `ε` clause keeps `φ(a(x), b(x))` in normal form, the Cantor
clause keeps `ω^{l(x)}·n + r(x)` in normal form, `Qd.qd_dat_cnf`).  So the leaf readings are below every bound of
the data of `Ω₁ + λ(x)` (`qd_comp_lt`, as `Qc.qc_comp_lt`).  The level `E₂ = φ(1, Ω₂+1)` has the single leaf `1` and
reads `φ(1, Ω₁+1) = ε_{Ω₁+1}` (`qdLv_E2`).

* `qdLv_dat_ge` (**`f d ≤ ssDat(λ(x))` for every leaf `d`**), `qd_comp_lt`;
* `qdComps_E2`, `qdLv_E2` (**`E₂(x) = ε_{Ω₁+1}`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

section Dat

variable (f : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → f d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
include hf0 hD0 hfΩ hfm

/-- **Every leaf reading is at most the data of the reading of the level.** -/
theorem qdLv_dat_ge : ∀ z : Ordinal.{0}, z < qdG2 → (∀ d ∈ qdComps z, Dm d) →
    ∀ d ∈ qdComps z, f d ≤ Ss.ssDat (qdLv f z) := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG hzD d hd
  have hmain := qdLv_main f Dm hf0 hD0 hfΩ hfm z hzG hzD
  rcases lt_trichotomy z OmTwo with hz2 | rfl | hz2
  · have hzd : Dm z := hzD z (by rw [qdComps_small hz2]; exact mem_singleton _)
    rw [qdComps_small hz2, mem_singleton_iff] at hd
    subst hd
    rw [qdLv_small f hz2, Ss.ssDat_small (hfΩ _ hzd)]
  · rw [qdComps_Om2] at hd; exact absurd hd (Set.notMem_empty _)
  have hc0 := qd_c0 Dm hD0
  have hOz : Om1 < qdLv f z := by
    have h := hmain.2.2.2.2.2 OmTwo hz2 (by rw [qdComps_Om2]; exact fun _ h => absurd h (Set.notMem_empty _))
    rwa [qdLv_Om2] at h
  have hzGG : qdLv f z < ggGam := hmain.1
  by_cases hE : ω ^ z = z
  · -- an `ε`-number `z = φ(a, b)`
    have hab : veblen (invVeblen₁ z) (invVeblen₂ z) = z := qd_veb_inv hE
    have haz : invVeblen₁ z < z := qd_inv1_lt hz2 hzG
    have hbz : invVeblen₂ z < z := Ss.ss_inv2_lt hE
    have hc := qdComps_phi hz2 hzG hE
    have haD : ∀ d ∈ qdComps (invVeblen₁ z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inl hd)
    have hbD : ∀ d ∈ qdComps (invVeblen₂ z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inr hd)
    have ha0 : invVeblen₁ z ≠ 0 := by
      intro h0
      have hzb : ω ^ invVeblen₂ z = z := by rw [← veblen_zero_apply, ← h0, hab]
      have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 hbz
      rw [hzb, hE] at h1
      exact lt_irrefl _ h1
    have hLa : 0 < qdLv f (invVeblen₁ z) := by
      have h := (qdLv_main f Dm hf0 hD0 hfΩ hfm _ (haz.trans hzG) haD).2.2.2.2.2 0 (pos_iff_ne_zero.2 ha0) hc0
      rwa [qdLv_small f qd_Om2_pos, hf0] at h
    have hLz : qdLv f z = veblen (qdLv f (invVeblen₁ z)) (qdLv f (invVeblen₂ z)) := qdLv_phi f hz2 hzG hE
    have hLb : qdLv f (invVeblen₂ z) < veblen (qdLv f (invVeblen₁ z)) (qdLv f (invVeblen₂ z)) := by
      rw [← hLz]; exact hmain.2.2.2.2.2 _ hbz hbD
    have hLzE : ω ^ qdLv f z = qdLv f z := hmain.2.2.2.2.1 hz2.le hE
    have hdat : Ss.ssDat (qdLv f z) =
        max (Ss.ssDat (qdLv f (invVeblen₁ z))) (Ss.ssDat (qdLv f (invVeblen₂ z))) := by
      rw [Ss.ssDat_eq_phi hOz hzGG hLzE, hLz, invVeblen₁_veblen hLb, invVeblen₂_veblen hLa.ne' hLb]
    rw [hdat]
    rw [hc] at hd
    rcases hd with hd | hd
    · exact (IH _ haz (haz.trans hzG) haD d hd).trans (le_max_left _ _)
    · exact (IH _ hbz (hbz.trans hzG) hbD d hd).trans (le_max_right _ _)
  · -- a non-`ε` level `z = ω^l·n + r`
    obtain ⟨-, -, hn0, hnω, hl2, hlz⟩ := qd_cnf_parts hz2 hE
    have hrz : z % ω ^ log ω z < z := rj_mod_lt (qd_Om2_pos.trans hz2).ne'
    have hc := qdComps_cnf hz2 hzG hE
    have hlD : ∀ d ∈ qdComps (log ω z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inl hd)
    have hrD : ∀ d ∈ qdComps (z % ω ^ log ω z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inr hd)
    have hLz : qdLv f z = ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) + qdLv f (z % ω ^ log ω z) :=
      qdLv_cnf f hz2 hzG hE
    have hOl : Om1 ≤ qdLv f (log ω z) :=
      (qdLv_main f Dm hf0 hD0 hfΩ hfm _ (hlz.trans hzG) hlD).2.2.2.1 hl2
    have hrtop := qdLv_rtop f Dm hf0 hD0 hfΩ hfm hz2 hzG hE hzD
    have hG : ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) + qdLv f (z % ω ^ log ω z) < ggGam := by
      rw [← hLz]; exact hzGG
    obtain ⟨h1, h2⟩ := qd_dat_cnf hOl hn0 hnω hrtop hG
    rw [hLz]
    rw [hc] at hd
    rcases hd with hd | hd
    · exact (IH _ hlz (hlz.trans hzG) hlD d hd).trans h1
    · exact (IH _ hrz (hrz.trans hzG) hrD d hd).trans h2

/-- **The leaf readings are below every bound of the data of `Ω₁ + λ(x)`.** -/
theorem qd_comp_lt {γ V : Ordinal.{0}} (hγG : γ < qdG2) (hγD : ∀ d ∈ qdComps γ, Dm d) (hL1 : 1 ≤ qdLv f γ)
    (hdat : Tf.tfDat (Om1 + qdLv f γ) < V) : ∀ d ∈ qdComps γ, f d < V := by
  intro d hd
  have hLG := (qdLv_main f Dm hf0 hD0 hfΩ hfm γ hγG hγD).1
  rw [Tf.tfDat_eq_ss _ (Tf.tf_Om1_add_lt_gg hLG), qd_ssDat_Om1_add hL1 hLG] at hdat
  exact (qdLv_dat_ge f Dm hf0 hD0 hfΩ hfm γ hγG hγD d hd).trans_lt hdat

end Dat

theorem qd_one_lt_Om2 : (1 : Ordinal.{0}) < OmTwo :=
  (show (1 : Ordinal.{0}) < Om1 by rw [Rj.rj_Om1]; exact Nm.one_lt_Om1).trans Qc.qc_Om1_lt_Om2

theorem qd_O2_one_lt : (OmTwo : Ordinal.{0}) + 1 < veblen 1 (OmTwo + 1) := by
  rw [← uc_E_eq_veblen]
  exact (ev_isSuccLimit_of_inE ucE_fix).add_one_lt ucE_gt

theorem qd_O2_one_eq : (OmTwo : Ordinal.{0}) + 1 = ω ^ OmTwo * 1 + 1 := by
  rw [mul_one, Low.opow_eq_self_of_SC uc_SC_Om2]

theorem qd_O2_one_facts :
    OmTwo ≤ (OmTwo : Ordinal.{0}) ∧ (1 : Ordinal.{0}) ≠ 0 ∧ (1 : Ordinal.{0}) < ω ∧ (1 : Ordinal.{0}) < ω ^ OmTwo ∧
      ω ^ (OmTwo : Ordinal.{0}) * 1 + 1 ≠ OmTwo ∧ ω ^ (OmTwo : Ordinal.{0}) * 1 + 1 < qdG2 := by
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  refine ⟨le_rfl, one_ne_zero, one_lt_omega0, ?_, ?_, ?_⟩
  · rw [hO2E]; exact qd_one_lt_Om2
  · rw [hO2E, mul_one]; exact (lt_add_one _).ne'
  · rw [← qd_O2_one_eq]; exact qd_O2_one_lt.trans (uc_E_eq_veblen ▸ qd_E_lt_G2)

/-- **The single leaf of `E₂` is `1`.** -/
theorem qdComps_E2 : ∀ d ∈ qdComps ucE, d = 1 := by
  obtain ⟨hu, hn0, hn, hr, hne, h2⟩ := qd_O2_one_facts
  have h1 : (1 : Ordinal.{0}) < OmTwo := qd_one_lt_Om2
  intro d hd
  rw [uc_E_eq_veblen, qdComps_veb one_ne_zero qd_O2_one_lt (ucE_gt.trans_eq uc_E_eq_veblen)
    (uc_E_eq_veblen ▸ qd_E_lt_G2), qd_O2_one_eq, qdComps_cnf' hu hn0 hn hr hne h2, qdComps_Om2, qdComps_small h1,
    Set.empty_union, Set.union_self, mem_singleton_iff] at hd
  exact hd

/-- **`E₂ = φ(1, Ω₂+1)` reads `φ(1, Ω₁+1) = ε_{Ω₁+1}`** (with `1` read `1`). -/
theorem qdLv_E2 (f : Ordinal.{0} → Ordinal.{0}) (h1 : f 1 = 1) : qdLv f ucE = ggE := by
  obtain ⟨hu, hn0, hn, hr, hne, h2⟩ := qd_O2_one_facts
  have h1Ω : (1 : Ordinal.{0}) < OmTwo := qd_one_lt_Om2
  rw [uc_E_eq_veblen, qdLv_veb f one_ne_zero qd_O2_one_lt (ucE_gt.trans_eq uc_E_eq_veblen)
    (uc_E_eq_veblen ▸ qd_E_lt_G2), qd_O2_one_eq, qdLv_cnf' f hu hn0 hn hr hne h2, qdLv_Om2, qdLv_small f h1Ω, h1,
    mul_one, rj_Om1_opow, Tf.tf_E_eq]

end Googology.Trans.PoR.InaccPsi.R2.Qd
