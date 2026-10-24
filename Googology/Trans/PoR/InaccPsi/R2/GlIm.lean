import Googology.Trans.PoR.InaccPsi.R2.GlR7

/-!
# LEMMA IMG FOR A SPECIFIED FUNCTION BELOW `Γ_{ρ+1}`

`LvGK.imgLvG` (`R2.LvGJ`) is Lemma IMG for every value below every top `gT n ρ` with a term of `LvGT` (levels
`ϑˣ(Ω₁·l(x) + t)` with term levels `l`), so below `lgG ρ = sup_n gT n ρ = Γ_{ρ+1}`; with Lemma EXACT for the terms
(`LvGT.pi`) the argument of `glPkg_of_ex` gives Lemma IMG for a SPECIFIED function `T` with Lemma EXACT and
`T(ρ) < Γ_{ρ+1}`.  This is the IMG half of the field `ld` for every code below `Γ_{Ω₁+1}` (the logends of the codes
of levels `≥ ω` lie above `φ(ω, ρ+1)`).

* `glPkgG_of_ex` (**Lemma IMG (gated) for every function with Lemma EXACT and value below `Γ_{ρ+1}`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gl

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gk

/-- **LEMMA IMG FOR A SPECIFIED FUNCTION (gated), below `Γ_{ρ+1}`**: if `T` has Lemma EXACT above the gate `g < ρ`
with constants `C < ρ`, and `T ρ < Γ_{ρ+1} = lgG ρ`, then every covering copy `f` that keeps `g` has
`T(f ρ) ≤ f(T ρ)`. -/
theorem glPkgG_of_ex {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) {g : Ordinal.{0}} {C : Finset Ordinal.{0}}
    {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ) (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < lgG ρ)
    (hex : GjEx g C T) : GhPkg g ρ δ T := by
  classical
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 hT
  obtain ⟨⟨W, Z, s, w, cb, cs', e, m, b⟩, -⟩ := LvGK.imgLvG h n (T ρ) hn
  have w' := w.union (gl_wz_consts (δ := δ) hC)
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
  have hs : LvGT.CBt s (f ρ) := LvG.cbt_img I cb (fun c hc => hZ' (Finset.mem_coe.2 (cs' c hc)))
  obtain ⟨-, hps⟩ := LvGT.pi hσU h.ρU hB s hs
  obtain ⟨-, hpT⟩ := hex (f ρ) ρ hσU h.ρU hB (Cx.lt hgρ) hCσ
  have hTs : T (f ρ) = LvGT.val s (f ρ) := by rw [← hpT, ← e, hps]
  rw [hTs]
  exact b A f hW hZ' I

end Googology.Trans.PoR.InaccPsi.R2.Gl
