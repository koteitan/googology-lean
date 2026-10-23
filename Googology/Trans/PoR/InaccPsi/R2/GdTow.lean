import Googology.Trans.PoR.InaccPsi.R2.GdLad

/-!
# THE GATED TOWER: a gated layer with top `Γ_{x+1+1+α} = ϑˣ(Ω₁·Ω₁ + 1 + α)` for EVERY ordinal `α`, valid above `α`

`R2.GcLim` and `R2.GcTow` for every offset, not only the constants below `ε₀`: the offset `α` is a gate.

* `gd_lim_E`, `gd_one_add_lt'`, `gd_succ_lt` (an `ε`-number above `α` is above `1 + α + 1`);
* `GdLimF λ` (**a family of gated layers below a limit `λ`**: gate of `K_β` at most `β`, top `ϑˣ(Ω₁·Ω₁ + 1 + β)` above
  `β`), `gdUSys` (the union, gated at `λ`), `GdLK.gdTopWit` (**THE TOP WITNESS of `Γ_{x+λ}` above `λ`**, from the
  copy of `G ≤₁ G·G + G + logend(λ)` and the witness of `K_{λ'}`), `gdLimL : GdLay λ`, `gdLimB : GdB`;
* the recursion `gdRec` (`Ordinal.limitRecOn`): `gdB 0 = lpTB 1` gated at `0`, `gdB (α+1)` = the limit of the gated
  ladder over `gdB α` raised to the gate `α + 1`, `gdB λ = gdLimB λ`; **`gdB_g`: the gate of `gdB α` is `α`**,
  **`gdB_E`: `E_{gdB α}(x) = ϑˣ(Ω₁·Ω₁ + 1 + α)` at every base `x > α`**, `gdB_succ`, `gdB_lim`;
* `GdLift`, `gdB_lift` (**every term of `gdB γ` is a term of `gdB β` for `γ ≤ β`**), `gdB_topIn` (**the top of
  `gdB γ` is the value of a term of `gdB β` whose side condition holds at every base, for `γ < β`**).

No new axiom.  New definitions: `GdLimF`, `gdUSys`, `gdLimL`, `gdLimB`, `GdSt`, `gdSt0`, `gdStSucc`, `gdF`,
`gdStLim`, `gdRec`, `gdB`, `GdLift`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc

/-! ## Offsets below a base -/

theorem gd_lim_E {x : Ordinal.{0}} (hx : InE x) : IsSuccLimit x := by
  have h := Ph.ph_opow_lim hx.pos.ne'
  rwa [show ω ^ x = x from hx] at h

theorem gd_one_add_lt' {x α : Ordinal.{0}} (hx : InE x) (hα : α < x) : 1 + α < x :=
  gc_one_add_lt (gd_lim_E hx) hα

theorem gd_succ_lt {x α : Ordinal.{0}} (hx : InE x) (hα : α < x) : 1 + α + 1 < x :=
  (gd_lim_E hx).add_one_lt (gd_one_add_lt' hx hα)

/-! ## The union of a family of gated layers below a limit offset -/

/-- **A family of gated layers below a limit `λ`**: for every `β < λ` a gated layer, gate at most `β`, with top
`ϑˣ(Ω₁·Ω₁ + 1 + β)` at every base above `β`. -/
structure GdLimF (l : Ordinal.{0}) where
  K : Iio l → GdB
  g_le : ∀ β, (K β).g ≤ β.1
  E_eq : ∀ β x, InE x → x < Om1 → β.1 < x → (K β).K.E x = gq (1 + β.1) x

section Fam

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (F : GdLimF l)
include hl

omit hl in
theorem gdF_g {β : Iio l} {x : Ordinal.{0}} (hx : l < x) : (F.K β).g < x :=
  (F.g_le β).trans_lt (β.2.trans hx)

omit hl in
/-- The top of the layer `K_β` is `ϑˣ(Ω₁·Ω₁ + 1 + β)` above `λ`. -/
theorem gdF_top (β : Iio l) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hlx : l < x) :
    (F.K β).K.sys.top x = gq (1 + β.1) x := by
  rw [(F.K β).K.top_eq x hx hx1 (gdF_g F hlx), F.E_eq β x hx hx1 (β.2.trans hlx)]
  exact (gq_facts hx hx1 (gd_one_add_lt' hx (β.2.trans hlx))).2.2.2.1

theorem gdLim_val_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hlx : l < x)
    (p : Σ β : Iio l, (F.K β).K.sys.Tm) (h : (F.K p.1).K.sys.CB p.2 x) : (F.K p.1).K.sys.val p.2 x < gq l x := by
  have h1 := (F.K p.1).K.lt_top_E x hx hx1 (gdF_g F hlx) p.2 h
  rw [gdF_top F p.1 hx hx1 hlx] at h1
  exact h1.trans (gq_lt hx hx1 hlx (gc_one_add_lt hl p.1.2))

end Fam

/-- **The union of the gated family**: the terms of every `K_β`, top `ϑˣ(Ω₁·Ω₁ + λ)`, gated at `λ`. -/
noncomputable def gdUSys (l : Ordinal.{0}) (hl : IsSuccLimit l) (F : GdLimF l) : GdSys l where
  Tm := Σ β : Iio l, (F.K β).K.sys.Tm
  val := fun p x => (F.K p.1).K.sys.val p.2 x
  CB := fun p x => (F.K p.1).K.sys.CB p.2 x
  cs := fun p => (F.K p.1).K.sys.cs p.2
  cst := fun c => ⟨⟨0, hl.bot_lt⟩, (F.K ⟨0, hl.bot_lt⟩).K.sys.cst c⟩
  top := gq l
  cb_cst := fun p s h => (F.K p.1).K.sys.cb_cst p.2 s h
  cb_iff := fun p s s' h h' => (F.K p.1).K.sys.cb_iff p.2 s s' h h'
  val_cst := fun c x => (F.K ⟨0, hl.bot_lt⟩).K.sys.val_cst c x
  cb_cstI := fun c x h => (F.K ⟨0, hl.bot_lt⟩).K.sys.cb_cstI c x h
  lt_top := fun _ hr hr1 hg p h => gdLim_val_lt hl F (ups_inE hr) (ups_lt_Om1 _ hr1) hg p h
  one_le_top := fun _ hr hr1 hg => one_le_iff_pos.2 (gq_facts (ups_inE hr) (ups_lt_Om1 _ hr1) hg).2.2.2.1.pos
  rep := fun r hr hr1 hg v hv => by
    obtain ⟨ν, hν, hv'⟩ := gc_lt_lim_iff (ups_inE hr) (ups_lt_Om1 r hr1) hl hg v hv
    have hlt : v < (F.K ⟨ν, hν⟩).K.sys.top (upsilon r) := by
      rw [gdF_top F ⟨ν, hν⟩ (ups_inE hr) (ups_lt_Om1 r hr1) hg]
      exact hv'.trans_le (gq_mono (ups_inE hr) (ups_lt_Om1 r hr1)
        (gd_one_add_lt' (ups_inE hr) (hν.trans hg)) le_add_self)
    obtain ⟨t, ht, et⟩ := (F.K ⟨ν, hν⟩).K.sys.rep r hr hr1 (gdF_g F hg) v hlt
    exact ⟨⟨⟨ν, hν⟩, t⟩, ht, et⟩
  top_lt := fun r hr hr1 hg => by
    have hl0 : 0 < r := pos_iff_ne_zero.2 hr.1
    have h1 : r < r + ω := lt_add_of_pos_right r omega0_pos
    have hτU := upsPt_upsilon (hl0.trans h1)
    exact (gq_lt_next (ups_inE hr) (ups_lt_Om1 r hr1) hg (upsilon_normal.strictMono h1) hτU.2).trans
      (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun r hr hr1 hg p h h1 R => (F.K p.1).K.sys.pkg r hr hr1 (gdF_g F hg) p.2 h h1 R
  rs := fun r hr hr1 hg p h => (F.K p.1).K.sys.rs r hr hr1 (gdF_g F hg) p.2 h
  uni_le := fun σ ρ hσ hρ hB hg p q hp hq =>
    xt_uni_of_exact hB ((F.K p.1).K.exact σ ρ hσ hρ hB (gdF_g F hg) p.2 hp)
      ((F.K q.1).K.exact σ ρ hσ hρ hB (gdF_g F hg) q.2 hq)
  small := fun p => ((F.K p.1).K.sys.small p.2).imp id fun h x hx hx1 hg hc => h x hx hx1 (gdF_g F hg) hc

theorem gdUSys_top (l : Ordinal.{0}) (hl : IsSuccLimit l) (F : GdLimF l) (x : Ordinal.{0}) :
    (gdUSys l hl F).top x = gq l x := rfl

namespace GdLK

variable {l : Ordinal.{0}} (hl : IsSuccLimit l) (F : GdLimF l) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
  (hlρ : l < ρ)
include hl F h hlρ

/-- **THE TOP WITNESS of `Γ_{x+λ}` above `λ`** for a limit `λ = λ' + ω^e` (`e = logend(λ)`): `f(G) ∈ E`, and
`ϑ^{fρ}(Ω₁·Ω₁ + λ) ≤ f(G)` for the copies that keep `λ`, from the copy `f(G) ≤₁ f(G)·f(G) + f(G) + e` of
`G ≤₁ G·G + G + e` (`Lq.lq_lh_sq`), the witness of the layer `K_{λ'}` (its gate kept by the copy) and
`gc_not_le1R_lim`. -/
theorem gdTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq l ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx l ρ A f →
      (∃ e', f (gq l ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq l (f ρ) ≤ f (gq l ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := gq_facts hρE h.ρ1 hlρ
  have hl0 : l ≠ 0 := hl.bot_lt.ne'
  obtain ⟨l', hdec, hdvd, hl'l⟩ := lg_split hl0
  have hζ0 : 0 < lg l := gc_lg_pos hl
  have hLG := gc_lh hρE h.ρ1 hlρ hl.bot_lt
  set G := gq l ρ with hG
  set ζ := lg l with hζ
  have hζρ : ζ < ρ := (lg_le hl0).trans_lt hlρ
  have hGδ : G < δ := (gq_lt_next hρE h.ρ1 hlρ h.ρτ h.τU.2).trans h.τδ
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hPGζδ : G * G + G + ζ < δ := (inE_indec h.δE).add_lt hPGδ (hζρ.trans (h.ρτ.trans h.τδ))
  have hG0 : 0 < G := hGE.pos
  have hGP : G < G * G := lt_mul_of_one_lt_right hG0 (lu_one_lt_E hGE)
  have hPe : G * G = ω ^ (G + G) := by
    conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have hρPG : ρ ≤ G * G + G := (hρG.le.trans hGP.le).trans le_self_add
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {G * G, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {G * G + G, G * G, G + G, G} ∅ := by
    have := w3.insW hρPG hPGδ
      (Or.inr ⟨G * G, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  have w5 : WZ ρ δ {G * G + G + ζ, G * G + G, G * G, G + G, G} {ζ} := by
    have := (w4.insZ hζρ).insW (hρPG.trans le_self_add) hPGζδ
      (Or.inr ⟨G * G + G, by simp, ζ, by simp, lt_add_of_pos_right _ hζ0,
        hζρ.trans_le (hρPG.trans le_self_add), rfl⟩)
    simpa using this
  set K' := F.K ⟨l', hl'l⟩ with hK'
  have hgK : K'.g < ρ := gdF_g F hlρ
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := K'.K.top_wit ρ τ δ h hgK
  have w6 := (w5.union wE).insZ hgK
  refine ⟨{G * G + G + ζ, G * G + G, G * G, G + G, G} ∪ WE, insert K'.g ({ζ} ∪ ZE), w6, by simp,
    fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : G * G ∈ A := hW (by simp)
  have hPGA : G * G + G ∈ A := hW (by simp)
  have hPGζA : G * G + G + ζ ∈ A := hW (by simp)
  have hζA : ζ ∈ A := hZ (by simp)
  have hgA : K'.g ∈ A := hZ (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZE : ↑ZE ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hTA : K'.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C.1 hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C.1
  have hly : l < f ρ := C.lt hlρ
  have hTρ : K'.K.sys.top ρ = gq (1 + l') ρ := gdF_top F ⟨l', hl'l⟩ hρE h.ρ1 hlρ
  have hTy : K'.K.sys.top (f ρ) = gq (1 + l') (f ρ) := gdF_top F ⟨l', hl'l⟩ hyE hy1 hly
  have hEG : gq (1 + l') ρ < G := gq_lt hρE h.ρ1 hlρ (gc_one_add_lt hl hl'l)
  have hfEG : f (K'.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : gq l' (f ρ) < f G := by
    have h1 := (hIE A f hWE hZE ⟨C.1, hgA⟩).2
    rw [hTy] at h1
    exact (gq_mono hyE hy1 (gd_one_add_lt' hyE (hl'l.trans hly)) le_add_self).trans_lt (h1.trans_lt hfEG)
  by_cases hU : UpsPt (f G)
  · exact (gq_lt_next hyE hy1 hly hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + ζ) := (h.lowδ _ _ hρG hPGζδ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPGζA hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hfζ : f ζ = ζ := C.fix ζ hζA hζρ
    have hadd1 : f (G * G + G) + f ζ = f (G * G + G + ζ) := C.add (G * G + G) hPGA ζ hζA _ hPGζA rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + ζ ≤ f (G * G + G + ζ) := by
      rw [← hadd1, hfζ, ← hadd2]
      exact add_le_add_left (add_le_add_left hPge _) _
    have hlo : f G ≤ f G * f G + f G + ζ :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    exact gc_not_le1R_lim hyE hy1 hly hdec hdvd hl'l hfE hEy hlt (le1R_of_le hlo hle hR)

end GdLK

/-- **The gated limit layer**: `gdUSys λ` with top `ϑˣ(Ω₁·Ω₁ + λ)`, gated at `λ`. -/
noncomputable def gdLimL (l : Ordinal.{0}) (hl : IsSuccLimit l) (F : GdLimF l) : GdLay l where
  sys := gdUSys l hl F
  E := gq l
  top_eq := fun x hx hx1 hg => (gq_facts hx hx1 hg).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg => opow_dvd_of_inE (gq_facts hx hx1 hg).2.2.2.1 (gq_facts hx hx1 hg).2.1.le
  exp_lt := fun x hx hx1 hg => (gq_facts hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (gq_facts hx hx1 hg).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu => gq_lt_next hx hx1 hg hxu hu.2
  lt_top_E := fun x hx hx1 hg p h => gdLim_val_lt hl F hx hx1 hg p h
  exact := fun σ ρ hσ hρ hB hg p hp => (F.K p.1).K.exact σ ρ hσ hρ hB (gdF_g F hg) p.2 hp
  exp_pi := fun _ _ _ _ hB hg => gq_pi hB hg
  top_wit := fun _ _ _ h hg => GdLK.gdTopWit hl F h hg

/-- **The gated limit base package** (gate `λ`). -/
noncomputable def gdLimB (l : Ordinal.{0}) (hl : IsSuccLimit l) (F : GdLimF l) : GdB where
  g := l
  K := gdLimL l hl F
  ek := fun x hx hx1 hg => (gq_facts hx hx1 hg).2.2.2.1
  mem := fun x hx hx1 hg => (gq_facts hx hx1 hg).1

/-! ## The recursion -/

/-- The value of the recursion at `α`: a gated base package with gate `α` and top `ϑˣ(Ω₁·Ω₁ + 1 + α)` above `α`. -/
def GdSt (α : Ordinal.{0}) : Type 2 :=
  {B : GdB // B.g = α ∧ ∀ x, InE x → x < Om1 → α < x → B.K.E x = gq (1 + α) x}

/-- The start: `lpTB 1`, top `ϑˣ(Ω₁·Ω₁ + 1)`, gated at `0`. -/
noncomputable def gdSt0 : GdSt 0 :=
  ⟨GdB.ofLp (Lp.lpTB 1) 0, rfl, fun x _ _ _ => by
    show Lp.gk (0 + 1) x = gq (1 + 0) x
    rw [add_zero, zero_add, ← gq_nat, Nat.cast_one]⟩

/-- **The limit hypothesis of the successor step above the gate.** -/
theorem gdH_succ {α : Ordinal.{0}} (s : GdSt α) : GdqH s.1 (1 + α + 1) := by
  refine ⟨fun x hx hg => ?_, fun x hx hx1 hg j hj => ?_, fun x hx hx1 hg => ?_⟩
  · rw [s.2.1] at hg; exact gd_succ_lt hx hg
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact gq_mono hx hx1 (gd_one_add_lt' hx hg) (Order.lt_add_one_iff.1 hj)
  · rw [s.2.1] at hg
    rw [s.2.2 x hx hx1 hg]
    exact gq_lt hx hx1 (gd_succ_lt hx hg) (lt_add_one _)

theorem gd_g_succ {α : Ordinal.{0}} (s : GdSt α) : (gdqLimB s.1 (1 + α + 1) (gdH_succ s)).g ≤ α + 1 := by
  rw [gdqLimB_g, s.2.1]; exact le_self_add

/-- The successor step: the limit of the gated ladder over the base, gate raised to `α + 1`. -/
noncomputable def gdStSucc (α : Ordinal.{0}) (s : GdSt α) : GdSt (α + 1) :=
  ⟨(gdqLimB s.1 (1 + α + 1) (gdH_succ s)).mono (gd_g_succ s), rfl, fun x _ _ _ => by
    show gq (1 + α + 1) x = gq (1 + (α + 1)) x
    rw [add_assoc]⟩

/-- The family of the earlier bases at a limit. -/
noncomputable def gdF {α : Ordinal.{0}} (IH : ∀ β < α, GdSt β) : GdLimF α where
  K := fun β => (IH β.1 β.2).1
  g_le := fun β => (IH β.1 β.2).2.1.le
  E_eq := fun β x hx hx1 hβx => (IH β.1 β.2).2.2 x hx hx1 hβx

/-- The limit step: the gated union with the generic limit witness. -/
noncomputable def gdStLim (α : Ordinal.{0}) (hα : IsSuccLimit α) (IH : ∀ β < α, GdSt β) : GdSt α :=
  ⟨gdLimB α hα (gdF IH), rfl, fun x _ _ _ => by
    show gq α x = gq (1 + α) x
    rw [one_add_of_omega0_le (omega0_le_of_isSuccLimit hα)]⟩

/-- **The recursion.** -/
noncomputable def gdRec (α : Ordinal.{0}) : GdSt α := Ordinal.limitRecOn α gdSt0 gdStSucc gdStLim

/-- **The gated base of the tower at `α`**: gate `α`, top `ϑˣ(Ω₁·Ω₁ + 1 + α)` above `α`. -/
noncomputable def gdB (α : Ordinal.{0}) : GdB := (gdRec α).1

theorem gdB_g (α : Ordinal.{0}) : (gdB α).g = α := (gdRec α).2.1

theorem gdB_E {α x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hαx : α < x) :
    (gdB α).K.E x = gq (1 + α) x := (gdRec α).2.2 x hx hx1 hαx

theorem gdB_gate {α x : Ordinal.{0}} (hαx : α < x) : (gdB α).g < x := by rw [gdB_g]; exact hαx

theorem gdB_top {α x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hαx : α < x) :
    (gdB α).K.sys.top x = gq (1 + α) x := by
  rw [(gdB α).K.top_eq x hx hx1 (gdB_gate hαx), gdB_E hx hx1 hαx]
  exact (gq_facts hx hx1 (gd_one_add_lt' hx hαx)).2.2.2.1

theorem gdRec_succ (α : Ordinal.{0}) : gdRec (α + 1) = gdStSucc α (gdRec α) := by
  unfold gdRec
  rw [Ordinal.limitRecOn_add_one]

theorem gdB_succ (α : Ordinal.{0}) :
    gdB (α + 1) = (gdqLimB (gdB α) (1 + α + 1) (gdH_succ (gdRec α))).mono (gd_g_succ (gdRec α)) := by
  show (gdRec (α + 1)).1 = _
  rw [gdRec_succ]
  rfl

theorem gdRec_lim {α : Ordinal.{0}} (hα : IsSuccLimit α) :
    gdRec α = gdStLim α hα (fun β _ => gdRec β) := by
  unfold gdRec
  rw [Ordinal.limitRecOn_limit _ _ _ _ hα]

theorem gdB_lim {α : Ordinal.{0}} (hα : IsSuccLimit α) :
    gdB α = gdLimB α hα (gdF fun β _ => gdRec β) := by
  show (gdRec α).1 = _
  rw [gdRec_lim hα]
  rfl

/-! ## Lifting terms through the tower -/

/-- **Every term of `Y` is a term of `X`** with the same value and a weaker side condition. -/
def GdLift {g g' : Ordinal.{0}} (X : GdSys g) (Y : GdSys g') : Prop :=
  ∀ s : Y.Tm, ∃ t : X.Tm, ∀ x, (Y.CB s x → X.CB t x) ∧ X.val t x = Y.val s x

theorem gdLift_refl {g : Ordinal.{0}} (X : GdSys g) : GdLift X X := fun s => ⟨s, fun _ => ⟨id, rfl⟩⟩

theorem gdLift_trans {g g' g'' : Ordinal.{0}} {X : GdSys g} {Y : GdSys g'} {W : GdSys g''}
    (h1 : GdLift X Y) (h2 : GdLift Y W) : GdLift X W := fun s => by
  obtain ⟨t, ht⟩ := h2 s
  obtain ⟨u, hu⟩ := h1 t
  exact ⟨u, fun x => ⟨fun h => (hu x).1 ((ht x).1 h), (hu x).2.trans (ht x).2⟩⟩

/-- **Every term of `gdB γ` is a term of `gdB β` for `γ ≤ β`.** -/
theorem gdB_lift : ∀ β : Ordinal.{0}, ∀ γ, γ ≤ β → GdLift (gdB β).K.sys (gdB γ).K.sys := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro γ hγ
  rcases hγ.lt_or_eq with hγ | rfl
  · rcases zero_or_succ_or_isSuccLimit β with rfl | ⟨δ, rfl⟩ | hα
    · exact absurd hγ (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at hγ IH ⊢
      rw [gdB_succ δ]
      refine gdLift_trans (fun s => ⟨GdT.ak s, fun _ => ⟨id, rfl⟩⟩)
        (IH δ (lt_add_one δ) γ (Order.lt_add_one_iff.1 hγ))
    · rw [gdB_lim hα]
      exact fun s => ⟨⟨⟨γ, hγ⟩, s⟩, fun _ => ⟨id, rfl⟩⟩
  · exact gdLift_refl _

/-- **The top of `gdB γ` is the value of a term of `gdB β`** (`γ < β`) whose side condition holds at every base. -/
theorem gdB_topIn {β γ : Ordinal.{0}} (hγβ : γ < β) : ∃ t : (gdB β).K.sys.Tm, ∀ x, (gdB β).K.sys.CB t x ∧
    (InE x → x < Om1 → γ < x → (gdB β).K.sys.val t x = gq (1 + γ) x) := by
  have hL := gdB_lift β (γ + 1) (Order.add_one_le_of_lt hγβ)
  rw [gdB_succ γ] at hL
  obtain ⟨t, ht⟩ := hL (GdT.tp : GdT (gdB γ))
  refine ⟨t, fun x => ⟨(ht x).1 trivial, fun hx hx1 hγx => ?_⟩⟩
  rw [(ht x).2]
  exact gdB_E hx hx1 hγx

end Googology.Trans.PoR.InaccPsi.R2.Gd
