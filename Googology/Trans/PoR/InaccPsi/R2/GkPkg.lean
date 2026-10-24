import Googology.Trans.PoR.InaccPsi.R2.GkAtm

/-!
# LEMMA IMG FOR A SPECIFIED FUNCTION BELOW THE NEXT `ε`-FIXED POINT

`Gj.gjPkg_of_ex` gives Lemma IMG (`GhPkg`) for a specified function `T` with Lemma EXACT and `T(ρ) < ε_{ρ+2}`, the
witness being the term of `RstK.imgY`.  With `gkImg` (every value below `evZ ρ`) and Lemma EXACT for every term of
`GkT` (`gkT_pi`) the bound `ε_{ρ+2}` is gone: `T(ρ) < evZ ρ`, i.e. below `ε_{ρ+ν}` for every `ν < evZ ρ`.

* `gkPkg_of_ex` (**Lemma IMG (gated) for every function with Lemma EXACT and value below `evZ ρ`**),
  `gkImgPkg_of_ex` (the ungated package `ImgPkg`);
* `gkT_pkg` (**Lemma IMG for every term of `GkT` itself**: constants below `ρ` suffice), `gkT_imgPkg`;
* `gkAtom_pkg` (the atom `y ↦ ω^{ε_{y+t(y)}+u(y)}` for terms `t, u`), `gk_pkg_eNN1` (the logend `ε_{y+2} + 1` of the
  reading `ω^{ε_{y+2}+1}` of the code `ε_{Ω₁+2}·ω`, where round 81 stopped), `gk_pkg_eAw1` (the logend
  `ε_{y+ω} + 1` of the code `ε_{Ω₁+ω}·ω`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj GkT

theorem gk_wz_consts {ρ δ : Ordinal.{0}} {C : Finset Ordinal.{0}} (hC : ∀ c ∈ C, c < ρ) : WZ ρ δ ∅ C :=
  ⟨by simp, hC, by simp⟩

section Pkg

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (gated), below the next `ε`-fixed point**: if `T` has Lemma EXACT above the
gate `g < ρ` with constants `C < ρ`, and `T ρ < evZ ρ`, then every covering copy `f` that keeps `g` has
`T(f ρ) ≤ f(T ρ)`. -/
theorem gkPkg_of_ex {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < evZ ρ) (hex : GjEx g C T) : GhPkg g ρ δ T := by
  classical
  obtain ⟨W, Z, s, ⟨w, cb, cs', e, m, b⟩, -⟩ := gkImg h (T ρ) hT
  have w' := w.union (gk_wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨W, Z ∪ C, w', ?_, fun A f hW hZ Cx => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have I := Cx.toImgCtx
  have hσU : UpsPt (f ρ) := I.ups
  have hB : Bases (f ρ) ρ := h.img_bases I
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  have hs : CB s (f ρ) := gk_cbImg I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs' c hc)))
  obtain ⟨-, hps⟩ := gkT_pi hσU h.ρU hB s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) ρ hσU h.ρU hB (Cx.lt hgρ) hCσ
  have hTs : T (f ρ) = ev s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (ungated package)**: `1 ≤ T ρ < evZ ρ` and Lemma EXACT at every `υ`-point
pair with the constants below the smaller base give `ImgPkg ρ δ T`. -/
theorem gkImgPkg_of_ex {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hC : ∀ c ∈ C, c < ρ)
    (h1 : 1 ≤ T ρ) (hT : T ρ < evZ ρ)
    (hex : ∀ σ, UpsPt σ → Bases σ ρ → (∀ c ∈ C, c < σ) → T ρ ∈ TB ρ σ ∧ pi σ ρ (T ρ) = T σ) :
    ImgPkg ρ δ T := by
  classical
  obtain ⟨W, Z, s, ⟨w, cb, cs', e, m, b⟩, -⟩ := gkImg h (T ρ) hT
  have w' := w.union (gk_wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨h1, hT.trans (gk_evZ_lt_δ h), W, Z ∪ C, w', ?_, fun A f hW hZ I => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have hσU : UpsPt (f ρ) := I.ups
  have hB : Bases (f ρ) ρ := h.img_bases I
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  have hs : CB s (f ρ) := gk_cbImg I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs' c hc)))
  obtain ⟨-, hps⟩ := gkT_pi hσU h.ρU hB s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) hσU hB hCσ
  have hTs : T (f ρ) = ev s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

/-- **LEMMA IMG FOR EVERY TERM OF `GkT` ITSELF (gated)**: constants below `ρ` are the only condition (the value is
below `evZ ρ` automatically). -/
theorem gkT_pkg {g : Ordinal.{0}} (t : GkT) (hgρ : g < ρ) (hcb : CB t ρ) : GhPkg g ρ δ (ev t) :=
  gkPkg_of_ex h hgρ (fun c hc => hcb c (List.mem_toFinset.1 hc)) (gkT_lt_evZ h.ρE t hcb) (gkT_ex g t)

/-- **LEMMA IMG FOR EVERY TERM OF `GkT` ITSELF (package)**: constants below `ρ`, `1 ≤ t(ρ)`. -/
theorem gkT_imgPkg (t : GkT) (hcb : CB t ρ) (h1 : 1 ≤ ev t ρ) : ImgPkg ρ δ (ev t) :=
  gkImgPkg_of_ex h (fun c hc => hcb c (List.mem_toFinset.1 hc)) h1 (gkT_lt_evZ h.ρE t hcb) fun σ hσ hB hC =>
    gkT_pi hσ h.ρU hB t (fun c hc => hC c (List.mem_toFinset.2 hc))

/-- **The atoms over every pseudo-base**: Lemma IMG for `y ↦ ω^{ε_{y+t(y)}+u(y)}`, for terms `t, u` with constants
below `ρ`. -/
theorem gkAtom_pkg {g : Ordinal.{0}} (t u : GkT) (hgρ : g < ρ) (hct : CB t ρ) (hcu : CB u ρ) :
    GhPkg g ρ δ (fun y => ω ^ (evA y (ev t y) + ev u y)) := by
  have e : (fun y => ω ^ (evA y (ev t y) + ev u y)) = ev (opow (add (ea t) u)) := rfl
  rw [e]
  refine gkT_pkg h _ hgρ (fun c hc => ?_)
  simp only [cs_opow, cs_add, cs_ea, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hct c hc
  · exact hcu c hc

/-- **The logend at the code `ε_{Ω₁+2}·ω`** (where round 81 stopped): the reading `ω^{ε_{y+2}+1}` has logend
`ε_{y+2} + 1`, and Lemma IMG holds for `y ↦ ε_{y+2} + 1` itself, above every gate. -/
theorem gk_pkg_eNN1 {g : Ordinal.{0}} (hgρ : g < ρ) : GhPkg g ρ δ (fun y => eN (eN y) + 1) := by
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have h2ρ : (2 : Ordinal.{0}) < ρ := (nat_lt_omega0 2).trans (omega0_lt_inE h.ρE)
  have hP := gkT_pkg h (add (ea (k 2)) (k 1)) hgρ (g := g) (fun c hc => by
    simp only [cs_add, cs_ea, cs_k, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact h2ρ
    · exact h1ρ)
  refine hP.congr h (fun y hy _ _ => ?_) hgρ
  simp only [ev_add, ev_ea, ev_k]
  have e2 : (2 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) := by norm_num
  rw [e2, evA_eK hy]
  rfl

/-- **The logend at the code `ε_{Ω₁+ω}·ω`**: Lemma IMG for `y ↦ ε_{y+ω} + 1` (a limit index: through the
`R₁⁺`-reach `lh(ε_{ρ+ω}) = ε_{ρ+ω}·2 + 1`). -/
theorem gk_pkg_eAw1 {g : Ordinal.{0}} (hgρ : g < ρ) : GhPkg g ρ δ (fun y => evA y ω + 1) := by
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have hωρ : ω < ρ := omega0_lt_inE h.ρE
  exact gkT_pkg h (add (ea (k ω)) (k 1)) hgρ (fun c hc => by
    simp only [cs_add, cs_ea, cs_k, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact hωρ
    · exact h1ρ)

end Pkg

end Googology.Trans.PoR.InaccPsi.R2.Gk
