import Googology.Trans.PoR.InaccPsi.R2.EvV
import Googology.Trans.PoR.InaccPsi.R2.EvR

/-!
# The IMG package of `ε_{x+c}` for every constant `c`, and Theorem BLK^O at the block of `Λ_{ε_{x+ω}}`

The project's Lemma IMG for the value `ε_{ρ+c}` (`c < ρ` a constant): every covering copy `f` of a set
containing the witness sets has `ε_{f(ρ)+c} ≤ f(ε_{ρ+c})`.  By induction on `c = c' + ω^z` (`z = logend(c)`):
inside the block `ε_{ρ+c} ≤₁ ε_{ρ+c}·2 + z` (`R₁⁺`, `lh_evA`; `z = 0`: `le1R_two_iff`), the copy keeps it,
and a copy that is not a `υ`-point has its `R₁⁺` reach, so it is `≥ ε_{b+ω^z}` above `b = ε_{f(ρ)+c'}`
(`le1R_ge_evA`); a copy that is a `υ`-point is above `ε_{f(ρ)+c}` (`evA_lt_ups`).

For `c = ω` this is the IMG package of `ε_{x+ω}` that the reach recursion needed at `Λ_{ε_{x+ω}}`: Lemma TOP at
`Λ_{ε_{x+ω}}` with the term `eW`, and Theorem BLK^O with `OrecW` below `υ_{Λ_{ε_{x+ω}}+ω²}`.

* `RstK.pkg_evA` (**Lemma IMG for `ε_{x+c}`**), `RstK.pkgA` (its `ImgPkg`), `RstK.pkgEW` (the package of `eW`);
* `topIn_LamW`, `specW2` (`OrecW` is a general offset specification up to `Λ_{ε_{x+ω}} + ω²`), `blkW2`
  (**BLK^O below `υ_{Λ_{ε_{x+ω}}+ω²}`**), `coreW2`, `reach_LamW` (**`lh(ρ_{Λ_{ε_{x+ω}}}) = δ + ε_{ρ+ω}`**),
  `nuC_boundW2` (**`υ_{Λ_{ε_{x+ω}}+ω²} ≤ ρ_L < ν_C`**).

No new axiom (the axioms of `R2.CitedEv` enter through `lh_evA`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem evA_lt_δ {c : Ordinal.{0}} (hc : c ≤ ρ) : evA ρ c < δ :=
  evA_lt_ups h.ρE h.ρ1 hc h.ρδ h.next.2.1

/-- **Lemma IMG for `ε_{x+c}`** (`c < ρ`): witness sets with `ε_{ρ+c}` in them such that every covering copy
`f` has `ε_{f(ρ)+c} ≤ f(ε_{ρ+c})`. -/
theorem pkg_evA : ∀ c, c < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ evA ρ c ∈ W ∪ Z ∧ c ∈ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      evA (f ρ) c ≤ f (evA ρ c) := by
  classical
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcρ
  rcases eq_or_ne c 0 with rfl | hc0
  · refine ⟨{ρ}, {0}, ?_, by simp [evA_zero hρE], by simp, fun A f _ _ C => ?_⟩
    · have := ((WZ.empty (ρ := ρ) (δ := δ)).insZ hρE.pos).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
      simpa using this
    · rw [evA_zero hρE, evA_zero (upsPt_inE C.ups)]
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
  set z := lg c with hz
  obtain ⟨W', Z', w', m', -, i'⟩ := IH c' hc'c (hc'c.trans hcρ)
  set v := evA ρ c with hv
  have hzc : z ≤ c := lg_le hc0
  have hzρ : z < ρ := lt_of_le_of_lt hzc hcρ
  have hρv : ρ < v := lt_evA hρE hc0
  have hvδ : v < δ := h.evA_lt_δ hcρ.le
  have hvE : InE v := evA_E _ _
  have hvv : v + v < δ := hδI.add_lt hvδ hvδ
  have hvvz : v + v + z < δ := hδI.add_lt hvv (hzρ.trans h.ρδ)
  have hv0 : 0 < v := hvE.pos
  -- the source: `v ≤₁ v·2 + z` in `R₁⁺`, hence in the block
  have hsrcR : le1R v (v * 2 + z) := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · rw [hz0, add_zero]; exact (le1R_two_iff hv0).2 hvE
    · have hωc : ω ≤ c := by
        have h1 : ω ^ (1 : Ordinal.{0}) ∣ c := by
          have := (le_lg_iff hc0 1).1 (one_le_iff_ne_zero.2 hz0); exact this
        rw [opow_one] at h1
        exact le_of_dvd hc0 h1
      exact (lh_evA hρE h.ρ1 hωc hcρ.le).1
  have hsrc : le1 v (v + v + z) :=
    (h.lowδ _ _ hρv hvvz.le).2 (by rw [← mul_two_eq]; exact hsrcR)
  -- the witness sets
  have w1 : WZ ρ δ (insert v W') (insert c (insert z Z')) :=
    ((w'.insZ hzρ).insZ hcρ).insW hρv.le hvδ (Or.inl (inE_indec hvE))
  have w2 : WZ ρ δ (insert (v + v) (insert v W')) (insert c (insert z Z')) :=
    w1.insW (hρv.le.trans le_self_add) hvv
      (Or.inr ⟨v, by simp, v, by simp, lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
  have w3 : WZ ρ δ (insert (v + v + z) (insert (v + v) (insert v W'))) (insert c (insert z Z')) := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · have e : v + v + z = v + v := by rw [hz0, add_zero]
      rw [e, Finset.insert_idem]
      exact w2
    · exact w2.insW ((hρv.le.trans le_self_add).trans le_self_add) hvvz
        (Or.inr ⟨v + v, by simp, z, by simp, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          lt_of_lt_of_le (hzρ.trans hρv) (le_self_add.trans le_self_add), rfl⟩)
  refine ⟨_, _, w3, by simp, by simp, ?_⟩
  intro A f hW hZ C
  have hW' : ↑W' ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ' : ↑Z' ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hvA : v ∈ A := hW (by simp)
  have hvvA : v + v ∈ A := hW (by simp)
  have hvvzA : v + v + z ∈ A := hW (by simp)
  have hzA : z ∈ A := hZ (by simp)
  have hcA : c ∈ A := hZ (by simp)
  have hc'A : evA ρ c' ∈ A := mem_A m' hW' hZ'
  have hIH := i' A f hW' hZ' C
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  have hcfρ : c < f ρ := C.above c hcA hcρ
  have hzfρ : z < f ρ := C.above z hzA hzρ
  have hfvv : f v + f v = f (v + v) := C.add v hvA v hvA _ hvvA rfl
  have hfvvz : f (v + v) + f z = f (v + v + z) := C.add _ hvvA z hzA _ hvvzA rfl
  rw [C.fix z hzA hzρ] at hfvvz
  have himg : le1 (f v) (f v + f v + z) := by
    have := C.cov1 v hvA _ hvvzA hsrc
    rwa [← hfvvz, ← hfvv] at this
  by_cases hU : UpsPt (f v)
  · exact (evA_lt_ups hfρE hfρ1 hcfρ.le hfρv hU).le
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    rw [← mul_two_eq] at hR
    set b := evA (f ρ) c' with hb
    have hbv : b < f v := lt_of_le_of_lt hIH (C.mono hc'A hvA (evA_lt_iff.2 hc'c))
    have hzb : z < b := lt_of_lt_of_le hzfρ (le_evA hfρE c')
    have := le1R_ge_evA z (f v) b (evA_E _ _) hbv hzb.le hR
    rwa [hb, evA_add, ← hcs] at this

/-- **The IMG package of `ε_{x+c}`** (`c < ρ`). -/
theorem pkgA {c : Ordinal.{0}} (hc : c < ρ) : ImgPkg ρ δ (fun x => evA x c) := by
  obtain ⟨W, Z, w, m, -, i⟩ := h.pkg_evA c hc
  exact ⟨(one_le_iff_pos.2 h.ρU.1).trans (le_evA h.ρE c), h.evA_lt_δ hc.le, W, Z, w, m, i⟩

/-- **The IMG package of `ε_{x+ω}`** (`eW`). -/
theorem pkgEW : ImgPkg ρ δ eW := by
  obtain ⟨W, Z, w, m, -, i⟩ := h.pkg_evA ω (omega0_lt_inE h.ρE)
  refine ⟨(one_le_eW ρ), ?_, W, Z, w, ?_, fun A f hW hZ C => ?_⟩
  · rw [← evA_eW h.ρE]; exact h.evA_lt_δ (omega0_lt_inE h.ρE).le
  · rw [← evA_eW h.ρE]; exact m
  · have := i A f hW hZ C
    rwa [evA_eW (upsPt_inE C.ups), evA_eW h.ρE] at this

/-- **Lemma IMG for `ε_{x+x}`**: witness sets such that every covering copy `f` has
`ε_{f(ρ)+f(ρ)} ≤ f(ε_{ρ+ρ})` (inside the block `ε_{ρ+ρ} ≤₁ ε_{ρ+ρ}·2 + ρ`, `lh_evA` with `c = ρ`). -/
theorem pkg_evAA : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ evA ρ ρ ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      evA (f ρ) (f ρ) ≤ f (evA ρ ρ) := by
  classical
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  set v := evA ρ ρ with hv
  have hρv : ρ < v := lt_evA hρE hρE.pos.ne'
  have hvδ : v < δ := h.evA_lt_δ le_rfl
  have hvE : InE v := evA_E _ _
  have hv0 : 0 < v := hvE.pos
  have hvv : v + v < δ := hδI.add_lt hvδ hvδ
  have hvvρ : v + v + ρ < δ := hδI.add_lt hvv h.ρδ
  have hlg : lg ρ = ρ := le_antisymm (lg_le hρE.pos.ne')
    ((le_lg_iff hρE.pos.ne' ρ).2 (by rw [show ω ^ ρ = ρ from hρE]))
  have hsrcR : le1R v (v * 2 + ρ) := by
    have := (lh_evA hρE h.ρ1 (omega0_lt_inE hρE).le le_rfl).1
    rwa [hlg] at this
  have hsrc : le1 v (v + v + ρ) :=
    (h.lowδ _ _ hρv hvvρ.le).2 (by rw [← mul_two_eq]; exact hsrcR)
  have w1 : WZ ρ δ {ρ} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
    simpa using this
  have w2 : WZ ρ δ (insert v {ρ}) ∅ := w1.insW hρv.le hvδ (Or.inl (inE_indec hvE))
  have w3 : WZ ρ δ (insert (v + v) (insert v {ρ})) ∅ :=
    w2.insW (hρv.le.trans le_self_add) hvv
      (Or.inr ⟨v, by simp, v, by simp, lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
  have w4 : WZ ρ δ (insert (v + v + ρ) (insert (v + v) (insert v {ρ}))) ∅ :=
    w3.insW ((hρv.le.trans le_self_add).trans le_self_add) hvvρ
      (Or.inr ⟨v + v, by simp, ρ, by simp, lt_add_of_pos_right _ hρE.pos,
        lt_of_lt_of_le hρv (le_self_add.trans le_self_add), rfl⟩)
  refine ⟨_, _, w4, by simp, fun A f hW _ C => ?_⟩
  have hvA : v ∈ A := hW (by simp)
  have hvvA : v + v ∈ A := hW (by simp)
  have hvvρA : v + v + ρ ∈ A := hW (by simp)
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  have hfvv : f v + f v = f (v + v) := C.add v hvA v hvA _ hvvA rfl
  have hfvvρ : f (v + v) + f ρ = f (v + v + ρ) := C.add _ hvvA ρ C.rho _ hvvρA rfl
  have himg : le1 (f v) (f v + f v + f ρ) := by
    have := C.cov1 v hvA _ hvvρA hsrc
    rwa [← hfvvρ, ← hfvv] at this
  by_cases hU : UpsPt (f v)
  · exact (evA_lt_ups hfρE hfρ1 le_rfl hfρv hU).le
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    rw [← mul_two_eq] at hR
    have := le1R_ge_evA (f ρ) (f v) (f ρ) hfρE hfρv le_rfl hR
    rwa [show ω ^ f ρ = f ρ from hfρE] at this

/-- **The IMG package of `ε_{x+x}`**. -/
theorem pkgAA : ImgPkg ρ δ (fun x => evA x x) := by
  obtain ⟨W, Z, w, m, i⟩ := h.pkg_evAA
  exact ⟨(one_le_iff_pos.2 h.ρU.1).trans (le_evA h.ρE ρ), h.evA_lt_δ le_rfl, W, Z, w, m, i⟩

end RstK

/-! ## Theorem BLK^O at the block of `Λ_{ε_{x+ω}}` -/

/-- **The input of Lemma TOP at `Λ_{ε_{x+ω}}`** with the term `eW`. -/
theorem topIn_LamW : TopInH OrecW LamW := by
  refine ⟨eW, 0, OrecW_LamW, (ups_ri LamW_ri).1, fun μ hμ hμl _ => OrecW_lt_top hμ hμl, fun R => R.pkgEW⟩

/-- **`OrecW` is a general offset specification up to `Λ_{ε_{x+ω}} + ω²`.** -/
theorem specW2 : OffSpecGen OrecW (LamW + ω * ω) where
  mult := dvd_add (ri_iff.1 LamW_ri).2 (dvd_refl _)
  cnt := Om1_add_lt LamW_lt_Om1 ww_lt_Om1
  le := fun _ hl hlB => OrecW_lt_δ hl (hlB.trans (Om1_add_lt LamW_lt_Om1 ww_lt_Om1))
  one := fun _ hl _ => one_le_OrecW hl
  top := fun l hl hlB => by
    rcases lt_trichotomy l LamW with hlt | rfl | hgt
    · exact topIn_OrecW hl (OrecW_lt_top hl hlt)
    · exact topIn_LamW
    · exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 LamW_ri).2 (ri_iff.1 hl).2 hgt))
  succ := fun _ hl _ h2 => OrecW_succ hl h2
  rs := fun _ hl _ h2 => rsIn_OrecW hl h2

/-- **Theorem BLK^O with `OrecW` below `υ_{Λ_{ε_{x+ω}}+ω²}`** in `R₂^C` (the block of `ρ_{Λ_{ε_{x+ω}}}`
included). -/
theorem blkW2 :
    (∀ c d, c < d → d < upsilon (LamW + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < LamW + ω * ω ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < LamW + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + OrecW l)) ∧
    (∀ α < upsilon (LamW + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen specW2

/-- **CORE-C up to `υ_{Λ_{ε_{x+ω}}+ω²}`.** -/
theorem coreW2 : Set.Iio (upsilon (LamW + ω * ω)) ⊆ Core R2C := core_genGen specW2

/-- **The reach at `Λ_{ε_{x+ω}}`**: `lh(ρ) = δ + ε_{ρ+ω}` for `ρ = ρ_{Λ_{ε_{x+ω}}}`. -/
theorem reach_LamW : IsReach R2C (upsilon LamW) (upsilon (LamW + ω + 1) + eW (upsilon LamW)) := by
  have := (blkW2.2.1 LamW LamW_ri (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))).2.2
  rwa [OrecW_LamW] at this

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε_{x+ω}} + ω² ≤ L < ξ` restart
indices, `υ_{Λ_{ε_{x+ω}}+ω²} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_boundW2 : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamW + ω * ω ≤ L ∧ L < ξ ∧
    upsilon (LamW + ω * ω) ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec specW2 hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
