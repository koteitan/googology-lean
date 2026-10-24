import Googology.Trans.PoR.InaccPsi.R2.GmGq

/-!
# THE UNION STEP WITH OFFSETS UP TO `Γ_{x+2}`: a gated layer with top `ϑˣ(Ω₁·Ω₁ + l(x))` for every limit offset
`l(x) < Γ_{x+2}` that is the supremum of the offsets of a family of gated layers

`R2.GhU` with the bound `l(x) < Γ_{x+1}` replaced by `l(x) < Γ_{x+2} = ϑˣ(Ω₁·Ω₁ + 1)` (the facts of `R2.GmGq`): the
offset `Γ_{x+1}` itself (the reading of the code `Γ_{Ω₁+1}`) and every `Γ_{x+1}·k + c(x)` are allowed.

* `GmUF g` (the data), `gmTop`, `gmVal_lt`, `gmUSys` (the union), `GmUK.gmTopWit` (**THE TOP WITNESS**, from
  `gm1_lh` and `gm1_not_le1R_lim`), `gmLimL`, `gmLimB` (**THE GATED LAYER**, top `ϑˣ(Ω₁·Ω₁ + l(x))`).

No new axiom.  New definitions: `GmUF`, `gmUSys`, `gmLimL`, `gmLimB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh

/-- **The data of a union step above the gate `g`**: a family `K_i` (`i : I`) of gated layers with tops
`ϑˣ(Ω₁·Ω₁ + o_i(x))` above the side gates `g_i`; the target offset `l(x)`: a limit below `Γ_{x+1}`, above every
`o_i(x)` and cofinal over them, with Lemma EXACT; its last term `l = l' + ω^{logend(l)}` (`ω^{logend(l)} ∣ l'`),
`l' ≤ o_{i_p}`; Lemma IMG for `logend ∘ l`; a member `i₀` with side gate `0` (for the constants). -/
structure GmUF (g : Ordinal.{0}) where
  I : Type 1
  K : I → GdB
  gi : I → Ordinal.{0}
  o : I → Ordinal.{0} → Ordinal.{0}
  l : Ordinal.{0} → Ordinal.{0}
  lp : Ordinal.{0} → Ordinal.{0}
  i0 : I
  ip : I
  g_le : ∀ i, (K i).g ≤ gi i
  gi0 : gi i0 = 0
  gip : gi ip ≤ g
  E_eq : ∀ i x, InE x → x < Om1 → gi i < x → (K i).K.E x = gq (o i x) x
  o_lt : ∀ i x, InE x → x < Om1 → g < x → gi i < x → o i x < l x
  l_lt : ∀ x, InE x → x < Om1 → g < x → l x < gq 1 x
  lim : ∀ x, InE x → x < Om1 → g < x → IsSuccLimit (l x)
  cof : ∀ x, InE x → x < Om1 → g < x → ∀ ν < l x, ∃ i, gi i < x ∧ ν ≤ o i x
  pi : ∀ σ ρ, UpsPt σ → UpsPt ρ → Bases σ ρ → g < σ → l ρ ∈ TB ρ σ ∧ pi σ ρ (l ρ) = l σ
  dec : ∀ x, InE x → x < Om1 → g < x → l x = lp x + ω ^ lg (l x) ∧ ω ^ lg (l x) ∣ lp x ∧ lp x < l x
  lp_le : ∀ x, InE x → x < Om1 → g < x → lp x ≤ o ip x
  pkg : ∀ ρ τ δ, RstK ρ τ δ → g < ρ → GhPkg g ρ δ (fun y => lg (l y))

namespace GmUF

variable {g : Ordinal.{0}} (F : GmUF g)

theorem l_T {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x) : l F x ∈ Tset x ∧ l F x < Om1 :=
  gm1_T hx hx1 (F.l_lt x hx hx1 hg)

theorem o_lt0 {i : F.I} {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x) (hi : F.gi i < x) :
    F.o i x < gq 1 x := (F.o_lt i x hx hx1 hg hi).trans (F.l_lt x hx hx1 hg)

theorem top_facts {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x) :
    gq (F.l x) x ∈ Tset x ∧ x < gq (F.l x) x ∧ gq (F.l x) x < Om1 ∧ InE (gq (F.l x) x) ∧
      Indec (gq (F.l x) x) :=
  geq_facts hx hx1 (F.l_T hx hx1 hg).1 (F.l_T hx hx1 hg).2

/-- The top of a member: `ϑˣ(Ω₁·Ω₁ + o_i(x))`. -/
theorem gmTop (i : F.I) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x) (hi : F.gi i < x) :
    (F.K i).K.sys.top x = gq (F.o i x) x := by
  rw [(F.K i).K.top_eq x hx hx1 ((F.g_le i).trans_lt hi), F.E_eq i x hx hx1 hi]
  obtain ⟨hT, h1⟩ := gm1_T hx hx1 (F.o_lt0 hx hx1 hg hi)
  exact (geq_facts hx hx1 hT h1).2.2.2.1

theorem gmVal_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hg : g < x)
    (p : Σ i : F.I, (F.K i).K.sys.Tm) (h : F.gi p.1 < x ∧ (F.K p.1).K.sys.CB p.2 x) :
    (F.K p.1).K.sys.val p.2 x < gq (F.l x) x := by
  have h1 := (F.K p.1).K.lt_top_E x hx hx1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  rw [F.gmTop p.1 hx hx1 hg h.1] at h1
  exact h1.trans (gm1_lt hx hx1 (F.l_lt x hx hx1 hg) (F.o_lt p.1 x hx hx1 hg h.1))

end GmUF

/-- **The union of the family**: the pairs `(i, t)`, `t` a term of `K_i`, with the side condition `g_i < x`; top
`ϑˣ(Ω₁·Ω₁ + l(x))`, gated at `g`. -/
noncomputable def gmUSys {g : Ordinal.{0}} (F : GmUF g) : GdSys g where
  Tm := Σ i : F.I, (F.K i).K.sys.Tm
  val := fun p x => (F.K p.1).K.sys.val p.2 x
  CB := fun p x => F.gi p.1 < x ∧ (F.K p.1).K.sys.CB p.2 x
  cs := fun p => F.gi p.1 :: (F.K p.1).K.sys.cs p.2
  cst := fun c => ⟨F.i0, (F.K F.i0).K.sys.cst c⟩
  top := fun x => gq (F.l x) x
  cb_cst := fun p s h c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact (F.K p.1).K.sys.cb_cst p.2 s h.2 c hc
  cb_iff := fun p s s' h h' => ⟨h' _ List.mem_cons_self,
    (F.K p.1).K.sys.cb_iff p.2 s s' h.2 (fun c hc => h' c (List.mem_cons_of_mem _ hc))⟩
  val_cst := fun c x => (F.K F.i0).K.sys.val_cst c x
  cb_cstI := fun c x h => ⟨by rw [F.gi0]; exact lt_of_le_of_lt zero_le h, (F.K F.i0).K.sys.cb_cstI c x h⟩
  lt_top := fun _ hr hr1 hg p h => F.gmVal_lt (ups_inE hr) (ups_lt_Om1 _ hr1) hg p h
  one_le_top := fun _ hr hr1 hg =>
    one_le_iff_pos.2 (F.top_facts (ups_inE hr) (ups_lt_Om1 _ hr1) hg).2.2.2.1.pos
  rep := fun r hr hr1 hg v hv => by
    have hx := ups_inE hr
    have hx1 := ups_lt_Om1 r hr1
    obtain ⟨ν, hν, hvν⟩ := gm1_lt_lim_iff hx hx1 (F.lim _ hx hx1 hg) (F.l_lt _ hx hx1 hg) v hv
    obtain ⟨i, hi, hνi⟩ := F.cof _ hx hx1 hg ν hν
    have hlt : v < (F.K i).K.sys.top (upsilon r) := by
      rw [F.gmTop i hx hx1 hg hi]
      exact hvν.trans_le (gm1_mono hx hx1 (F.o_lt0 hx hx1 hg hi) hνi)
    obtain ⟨t, ht, et⟩ := (F.K i).K.sys.rep r hr hr1 ((F.g_le i).trans_lt hi) v hlt
    exact ⟨⟨i, t⟩, ⟨hi, ht⟩, et⟩
  top_lt := fun r hr hr1 hg => by
    have hl0 : 0 < r := pos_iff_ne_zero.2 hr.1
    have h1 : r < r + ω := lt_add_of_pos_right r omega0_pos
    have hτU := upsPt_upsilon (hl0.trans h1)
    have hx := ups_inE hr
    have hx1 := ups_lt_Om1 r hr1
    exact (geq_lt_next hx hx1 (F.l_T hx hx1 hg).1 (F.l_T hx hx1 hg).2 (upsilon_normal.strictMono h1)
      hτU.2).trans (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun r hr hr1 _ p h h1 R => (F.K p.1).K.sys.pkg r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2 h1 R
  rs := fun r hr hr1 _ p h => (F.K p.1).K.sys.rs r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  uni_le := fun σ ρ hσ hρ hB _ p q hp hq =>
    xt_uni_of_exact hB ((F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2)
      ((F.K q.1).K.exact σ ρ hσ hρ hB ((F.g_le q.1).trans_lt hq.1) q.2 hq.2)
  small := fun p => ((F.K p.1).K.sys.small p.2).imp id fun h x hx hx1 _ hc =>
    h x hx hx1 ((F.g_le p.1).trans_lt hc.1) hc.2

theorem gmUSys_top {g : Ordinal.{0}} (F : GmUF g) (x : Ordinal.{0}) : (gmUSys F).top x = gq (F.l x) x := rfl

namespace GmUK

variable {g : Ordinal.{0}} (F : GmUF g) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hgρ : g < ρ)
include h hgρ

/-- **THE TOP WITNESS of the union**: `f(G) ∈ E` and `ϑ^{fρ}(Ω₁·Ω₁ + l(fρ)) ≤ f(G)`, `G = ϑ^ρ(Ω₁·Ω₁ + l(ρ))`, for the
copies that keep the gate; from the copy of `G ≤₁ G·G + G + ζ`, `ζ = logend(l(ρ))` (`gm1_lh`), Lemma IMG for `ζ`
(`F.pkg`: `logend(l(fρ)) ≤ f(ζ)`), the witness of the member `K_{i_p}` (so `ϑ^{fρ}(Ω₁·Ω₁ + l'(fρ)) < f(G)`) and
`gm1_not_le1R_lim`. -/
theorem gmTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq (F.l ρ) ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx g ρ A f →
      (∃ e', f (gq (F.l ρ) ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ gq (F.l (f ρ)) (f ρ) ≤ f (gq (F.l ρ) ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  have hlG := F.l_lt ρ hρE h.ρ1 hgρ
  obtain ⟨hlT, hl1⟩ := F.l_T hρE h.ρ1 hgρ
  obtain ⟨-, hρG, -, hGE, hGI⟩ := F.top_facts hρE h.ρ1 hgρ
  obtain ⟨e1, e2, e3⟩ := F.dec ρ hρE h.ρ1 hgρ
  have hl0 : 0 < F.l ρ := (F.lim ρ hρE h.ρ1 hgρ).bot_lt
  have hLG := gm1_lh hρE h.ρ1 hlG hl0
  set G := gq (F.l ρ) ρ with hG
  set ζ := lg (F.l ρ) with hζ
  have hζ0 : 0 < ζ := by
    rcases (zero_le : (0 : Ordinal.{0}) ≤ ζ).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      have e1' := e1
      rw [← h0, opow_zero] at e1'
      have := (F.lim ρ hρE h.ρ1 hgρ).add_one_lt e3
      rw [e1'] at this
      exact lt_irrefl _ this
  have hGδ : G < δ := (geq_lt_next hρE h.ρ1 hlT hl1 h.ρτ h.τU.2).trans h.τδ
  have hζG : ζ < G :=
    (lg_le hl0.ne').trans_lt (gmq_gt hρE h.ρ1 hlT hl1)
  have hPδ : G * G < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : G * G + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hPGζδ : G * G + G + ζ < δ := (inE_indec h.δE).add_lt hPGδ (hζG.trans hGδ)
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
  obtain ⟨WL, ZL, wL, hζWZ, hfL⟩ := F.pkg ρ τ δ h hgρ
  have w45 := w4.union wL
  have w5 := w45.insW (hρPG.trans le_self_add) hPGζδ
    (Or.inr ⟨G * G + G, Finset.mem_union_left _ (Finset.mem_union_left _ (by simp)), ζ,
      (by
        rcases Finset.mem_union.1 hζWZ with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ h')),
      lt_add_of_pos_right _ hζ0, hζG.trans_le ((le_mul_left _ hG0).trans le_self_add |>.trans le_self_add),
      rfl⟩)
  set K' := F.K F.ip with hK'
  have hgipρ : F.gi F.ip < ρ := F.gip.trans_lt hgρ
  have hgK : K'.g < ρ := (F.g_le _).trans_lt hgipρ
  obtain ⟨WE, ZE, wE, hTE, hIE⟩ := K'.K.top_wit ρ τ δ h hgK
  have w6 := (w5.union wE).insZ hgK
  refine ⟨insert (G * G + G + ζ) ({G * G + G, G * G, G + G, G} ∪ WL) ∪ WE, insert K'.g ((∅ ∪ ZL) ∪ ZE), w6,
    by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : G * G ∈ A := hW (by simp)
  have hPGA : G * G + G ∈ A := hW (by simp)
  have hPGζA : G * G + G + ζ ∈ A := hW (by simp)
  have hWL : ↑WL ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hζA : ζ ∈ A := by
    rcases Finset.mem_union.1 hζWZ with h' | h'
    · exact hWL (Finset.mem_coe.2 h')
    · exact hZL (Finset.mem_coe.2 h')
  have hgA : K'.g ∈ A := hZ (by simp)
  have hWE : ↑WE ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZE : ↑ZE ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hTA : K'.K.sys.top ρ ∈ A := hWE (Finset.mem_coe.2 hTE)
  obtain ⟨hfE, hPge⟩ := GbK.gbImg h hGE hρG hGδ C.1 hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C.1
  have hgy : g < f ρ := C.lt hgρ
  have hgipy : F.gi F.ip < f ρ := F.gip.trans_lt hgy
  obtain ⟨f1, f2, f3⟩ := F.dec (f ρ) hyE hy1 hgy
  have hTρ : K'.K.sys.top ρ = gq (F.o F.ip ρ) ρ := F.gmTop F.ip hρE h.ρ1 hgρ hgipρ
  have hTy : K'.K.sys.top (f ρ) = gq (F.o F.ip (f ρ)) (f ρ) := F.gmTop F.ip hyE hy1 hgy hgipy
  have hEG : gq (F.o F.ip ρ) ρ < G := gm1_lt hρE h.ρ1 hlG (F.o_lt F.ip ρ hρE h.ρ1 hgρ hgipρ)
  have hfEG : f (K'.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hlGy := F.l_lt (f ρ) hyE hy1 hgy
  have hEy : gq (F.lp (f ρ)) (f ρ) < f G := by
    have h1 := (hIE A f hWE hZE ⟨C.1, hgA⟩).2
    rw [hTy] at h1
    exact (gm1_mono hyE hy1 (F.o_lt0 hyE hy1 hgy hgipy) (F.lp_le (f ρ) hyE hy1 hgy)).trans_lt
      (h1.trans_lt hfEG)
  by_cases hU : UpsPt (f G)
  · exact (geq_lt_next hyE hy1 (F.l_T hyE hy1 hgy).1 (F.l_T hyE hy1 hgy).2 hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + ζ) := (h.lowδ _ _ hρG hPGζδ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPGζA hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hfζ : lg (F.l (f ρ)) ≤ f ζ := hfL A f hWL hZL C
    have hadd1 : f (G * G + G) + f ζ = f (G * G + G + ζ) := C.add (G * G + G) hPGA ζ hζA _ hPGζA rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + lg (F.l (f ρ)) ≤ f (G * G + G + ζ) := by
      rw [← hadd1, ← hadd2]
      exact add_le_add (add_le_add hPge le_rfl) hfζ
    have hlo : f G ≤ f G * f G + f G + lg (F.l (f ρ)) :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    exact gm1_not_le1R_lim hyE hy1 hlGy f1 f2 f3 hfE hEy hlt (le1R_of_le hlo hle hR)

end GmUK

/-- **The gated union layer**: top `ϑˣ(Ω₁·Ω₁ + l(x))`, gated at `g`. -/
noncomputable def gmLimL {g : Ordinal.{0}} (F : GmUF g) : GdLay g where
  sys := gmUSys F
  E := fun x => gq (F.l x) x
  top_eq := fun x hx hx1 hg => (F.top_facts hx hx1 hg).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg => opow_dvd_of_inE (F.top_facts hx hx1 hg).2.2.2.1 (F.top_facts hx hx1 hg).2.1.le
  exp_lt := fun x hx hx1 hg => (F.top_facts hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (F.top_facts hx hx1 hg).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu =>
    geq_lt_next hx hx1 (F.l_T hx hx1 hg).1 (F.l_T hx hx1 hg).2 hxu hu.2
  lt_top_E := fun x hx hx1 hg p h => F.gmVal_lt hx hx1 hg p h
  exact := fun σ ρ hσ hρ hB _ p hp => (F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2
  exp_pi := fun σ ρ hσ hρ hB hg => geq_pi hB (F.pi σ ρ hσ hρ hB hg) (F.l_T hB.2.1 hB.2.2.2 (hg.trans hB.2.2.1)).2
  top_wit := fun _ _ _ h hg => GmUK.gmTopWit F h hg

/-- **The gated union base package**: gate `g`, top `ϑˣ(Ω₁·Ω₁ + l(x)) = Γ_{x+1+l(x)}`. -/
noncomputable def gmLimB {g : Ordinal.{0}} (F : GmUF g) : GdB where
  g := g
  K := gmLimL F
  ek := fun x hx hx1 hg => (F.top_facts hx hx1 hg).2.2.2.1
  mem := fun x hx hx1 hg => (F.top_facts hx hx1 hg).1

theorem gmLimB_E {g : Ordinal.{0}} (F : GmUF g) (x : Ordinal.{0}) : (gmLimB F).K.E x = gq (F.l x) x := rfl

theorem gmLimB_g {g : Ordinal.{0}} (F : GmUF g) : (gmLimB F).g = g := rfl

end Googology.Trans.PoR.InaccPsi.R2.Gm
