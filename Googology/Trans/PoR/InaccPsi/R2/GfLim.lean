import Googology.Trans.PoR.InaccPsi.R2.GfSub

/-!
# THE LIMIT STEP FOR EVERY LIMIT CODE BELOW `ε_{Ω₁+1}`: the union of the layers of the smaller codes

For a limit code `a < ε_{Ω₁+1}` (`R2.GfSub`) and a family of gated layers `K_b`, `b < a`, with tops
`ϑˣ(Ω₁·Ω₁ + 1 + rdc b x)` above `gtc b`, the union of all `K_b` (the pair `(b, t)` with the side condition `gtc b < x`)
is a gated layer with top `ϑˣ(Ω₁·Ω₁ + rdc a x)` above `gtc a`.  The separation lemmas of `R2.GeLim`
(`Ge.ge_lt_lim_iff`, `Ge.ge_not_le1R_lim`) hold for every limit offset; what changes is the top witness: the logend
`ζ = logend(rdc a ρ) = ρ·rdc l ρ + d` (`a = a' + Ω₁^l·ω^d`) is no longer linear in the base.  It is the value of the
term `tlg l d` (constants: digits of `a`), and **Lemma IMG for terms** (`RstK.pkg_ot`) gives
`logend(rdc a (fρ)) = tlg l d (fρ) ≤ f(ζ)` for every covering copy `f`, the direction the separation needs.

* `GfLimF a` (the family), `gfO_lt`, `gfF_top`, `gfF_lt`, `gfO_facts`, `gfO_lt_next`, `gfO_pi` (**EXACT for
  `1 + rdc b x`**), `gfU_val_lt`, `gfUSys` (the union), `GfLK.gfTopWit` (**THE TOP WITNESS for every limit code**),
  `gfLimL`, `gfLimB`.

No new axiom.  New definitions: `GfLimF`, `gfUSys`, `gfLimL`, `gfLimB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ly Lu
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Ge

/-! ## The family of the layers of the smaller codes, and its union -/

/-- **A family of gated layers below a limit code `a`**: for every code `b < a` a gated layer, gtc at most `gtc b`,
with top `ϑˣ(Ω₁·Ω₁ + 1 + rdc b x)` at every base above `gtc b`. -/
structure GfLimF (a : Ordinal.{0}) where
  K : Iio a → GdB
  g_le : ∀ b, (K b).g ≤ gtc b.1
  E_eq : ∀ b x, InE x → x < Om1 → gtc b.1 < x → (K b).K.E x = gq (1 + rdc b.1 x) x

section Fam

variable {a : Ordinal.{0}} (F : GfLimF a)

theorem gfO_lt {b x : Ordinal.{0}} (hb : b < gfE) (hx : InE x) (hg : gtc b < x) : 1 + rdc b x < eN x :=
  (inE_indec (eN_E x)).add_lt (one_lt_omega0.trans (omega0_lt_inE (eN_E x))) (rdc_lt_eN hx b hg)

theorem gfF_top (ha : a < gfE) (b : Iio a) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : gtc b.1 < x) :
    (F.K b).K.sys.top x = gq (1 + rdc b.1 x) x := by
  rw [(F.K b).K.top_eq x hx hx1 ((F.g_le b).trans_lt hgx), F.E_eq b x hx hx1 hgx]
  obtain ⟨hT, h1⟩ := eN_T hx hx1 (gfO_lt (b.2.trans ha) hx hgx)
  exact (geq_facts hx hx1 hT h1).2.2.2.1

theorem gfF_lt (hl : IsSuccLimit a) (ha : a < gfE) {b : Iio a} {x : Ordinal.{0}} (hx : InE x) (hga : gtc a < x)
    (hgb : gtc b.1 < x) :
    1 + rdc b.1 x < rdc a x :=
  by
  obtain ⟨_, _, _, -, -, -, -, -, hF⟩ := rdc_lim_facts hl ha
  exact (Ge.one_add_le_succ _).trans_lt ((hF x hx hga).2.2.2.2.2.add_one_lt (rdc_mono hx ha b.2 hga hgb))

end Fam

theorem gfO_facts {b x : Ordinal.{0}} (hb : b < gfE) (hx : InE x) (hx1 : x < Om1) (hg : gtc b < x) :
    gq (1 + rdc b x) x ∈ Tset x ∧ x < gq (1 + rdc b x) x ∧ gq (1 + rdc b x) x < Om1 ∧ InE (gq (1 + rdc b x) x) ∧
      Indec (gq (1 + rdc b x) x) :=
  geq_facts hx hx1 (eN_T hx hx1 (gfO_lt hb hx hg)).1 (eN_T hx hx1 (gfO_lt hb hx hg)).2

theorem gfO_lt_next {b x : Ordinal.{0}} (hb : b < gfE) (hx : InE x) (hx1 : x < Om1) (hg : gtc b < x)
    {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : gq (1 + rdc b x) x < u :=
  geq_lt_next hx hx1 (eN_T hx hx1 (gfO_lt hb hx hg)).1 (eN_T hx hx1 (gfO_lt hb hx hg)).2 hxu hu

/-- **EXACT for the offset `1 + rdc b x`.** -/
theorem gfO_pi {σ ρ b : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < gfE) (hg : gtc b < σ) :
    1 + rdc b ρ ∈ TB ρ σ ∧ pi σ ρ (1 + rdc b ρ) = 1 + rdc b σ := by
  have h1σ : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
  obtain ⟨h1, h2⟩ := rdc_pi hB hb hg
  obtain ⟨h3, h4⟩ := pi_add hB (mem_TB_of_lt hB h1σ) h1
  exact ⟨h3, by rw [h4, pi_lt hB h1σ, h2]⟩

theorem gfU_val_lt {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) {x : Ordinal.{0}}
    (hx : InE x) (hx1 : x < Om1) (hg : gtc a < x) (p : Σ b : Iio a, (F.K b).K.sys.Tm)
    (h : gtc p.1.1 < x ∧ (F.K p.1).K.sys.CB p.2 x) : (F.K p.1).K.sys.val p.2 x < gq (1 + rdc a x) x := by
  have h1 := (F.K p.1).K.lt_top_E x hx hx1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  rw [gfF_top F ha p.1 hx hx1 h.1] at h1
  exact h1.trans (geq_lt hx hx1 (gfO_lt ha hx hg) ((gfF_lt hl ha hx hg h.1).trans_le le_add_self))

/-- **The union of the family**: the pairs `(b, t)`, `t` a term of `K_b`, with the side condition `gtc b < x`; top
`ϑˣ(Ω₁·Ω₁ + 1 + rdc a x)`, gated at `gtc a`. -/
noncomputable def gfUSys (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) : GdSys (gtc a) where
  Tm := Σ b : Iio a, (F.K b).K.sys.Tm
  val := fun p x => (F.K p.1).K.sys.val p.2 x
  CB := fun p x => gtc p.1.1 < x ∧ (F.K p.1).K.sys.CB p.2 x
  cs := fun p => gtc p.1.1 :: (F.K p.1).K.sys.cs p.2
  cst := fun c => ⟨⟨0, hl.bot_lt⟩, (F.K ⟨0, hl.bot_lt⟩).K.sys.cst c⟩
  top := fun x => gq (1 + rdc a x) x
  cb_cst := fun p s h c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact (F.K p.1).K.sys.cb_cst p.2 s h.2 c hc
  cb_iff := fun p s s' h h' => ⟨h' _ List.mem_cons_self,
    (F.K p.1).K.sys.cb_iff p.2 s s' h.2 (fun c hc => h' c (List.mem_cons_of_mem _ hc))⟩
  val_cst := fun c x => (F.K ⟨0, hl.bot_lt⟩).K.sys.val_cst c x
  cb_cstI := fun c x h => ⟨by rw [gtc_zero]; exact lt_of_le_of_lt zero_le h,
    (F.K ⟨0, hl.bot_lt⟩).K.sys.cb_cstI c x h⟩
  lt_top := fun _ hr hr1 hg p h => gfU_val_lt hl ha F (ups_inE hr) (ups_lt_Om1 _ hr1) hg p h
  one_le_top := fun _ hr hr1 hg => one_le_iff_pos.2 (gfO_facts ha (ups_inE hr) (ups_lt_Om1 _ hr1) hg).2.2.2.1.pos
  rep := fun r hr hr1 hg v hv => by
    have hx := ups_inE hr
    have hx1 := ups_lt_Om1 r hr1
    obtain ⟨_, _, _, -, -, -, -, -, hF⟩ := rdc_lim_facts hl ha
    obtain ⟨-, -, -, -, e5, e6⟩ := hF _ hx hg
    rw [e5] at hv
    obtain ⟨ν, hν, hvν⟩ := Ge.ge_lt_lim_iff hx hx1 e6 (rdc_lt_eN hx a hg) v hv
    obtain ⟨b, hb, hgb, hsb⟩ := rdc_surj hx hx1.le ha hg hν
    have hlt : v < (F.K ⟨b, hb⟩).K.sys.top (upsilon r) := by
      rw [gfF_top F ha ⟨b, hb⟩ hx hx1 hgb]
      refine hvν.trans_le (geq_mono hx hx1 (gfO_lt (hb.trans ha) hx hgb) ?_)
      rw [hsb]; exact le_add_self
    obtain ⟨t, ht, et⟩ := (F.K ⟨b, hb⟩).K.sys.rep r hr hr1 ((F.g_le _).trans_lt hgb) v hlt
    exact ⟨⟨⟨b, hb⟩, t⟩, ⟨hgb, ht⟩, et⟩
  top_lt := fun r hr hr1 hg => by
    have hl0 : 0 < r := pos_iff_ne_zero.2 hr.1
    have h1 : r < r + ω := lt_add_of_pos_right r omega0_pos
    have hτU := upsPt_upsilon (hl0.trans h1)
    exact (gfO_lt_next ha (ups_inE hr) (ups_lt_Om1 r hr1) hg (upsilon_normal.strictMono h1) hτU.2).trans
      (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun r hr hr1 _ p h h1 R => (F.K p.1).K.sys.pkg r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2 h1 R
  rs := fun r hr hr1 _ p h => (F.K p.1).K.sys.rs r hr hr1 ((F.g_le p.1).trans_lt h.1) p.2 h.2
  uni_le := fun σ ρ hσ hρ hB _ p q hp hq =>
    xt_uni_of_exact hB ((F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2)
      ((F.K q.1).K.exact σ ρ hσ hρ hB ((F.g_le q.1).trans_lt hq.1) q.2 hq.2)
  small := fun p => ((F.K p.1).K.sys.small p.2).imp id fun h x hx hx1 _ hc =>
    h x hx hx1 ((F.g_le p.1).trans_lt hc.1) hc.2

theorem gfUSys_top (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) (x : Ordinal.{0}) :
    (gfUSys a hl ha F).top x = gq (1 + rdc a x) x := rfl

namespace GfLK

variable {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
  (hgρ : gtc a < ρ)
include hl ha F h hgρ

/-- **THE TOP WITNESS for a term offset** above `gtc a`: `f(G) ∈ E` and `ϑ^{fρ}(Ω₁·Ω₁ + 1 + rdc a (fρ)) ≤ f(G)`,
`G = ϑ^ρ(Ω₁·Ω₁ + 1 + rdc a ρ)`, for the copies that keep `gtc a`; from the copy of `G ≤₁ G·G + G + ζ`,
`ζ = logend(rdc a ρ) = ρ·rdc l ρ + d` the value of the term `tlg l d`: Lemma IMG for that term (`RstK.pkg_ot`) gives
`logend(rdc a (fρ)) ≤ f(ζ)`; with the witness of the predecessor layer `K_{a'}` and `Ge.ge_not_le1R_lim`. -/
theorem gfTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ gq (1 + rdc a ρ) ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → GdCtx (gtc a) ρ A f →
      (∃ e', f (gq (1 + rdc a ρ) ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧
        gq (1 + rdc a (f ρ)) (f ρ) ≤ f (gq (1 + rdc a ρ) ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨a', l, d, ha'a, hg', hgl, hd, -, hF⟩ := rdc_lim_facts hl ha
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hF ρ hρE hgρ
  rw [e5]
  have hlE := rdc_lt_eN hρE a hgρ
  obtain ⟨hlT, hl1⟩ := eN_T hρE h.ρ1 hlE
  obtain ⟨-, hρG, -, hGE, hGI⟩ := geq_facts hρE h.ρ1 hlT hl1
  have hl0 : 0 < rdc a ρ := lt_of_lt_of_le omega0_pos e4
  have hLG := geq_lh hρE h.ρ1 hlE hl0
  have hdρ : d < ρ := hd.trans_lt hgρ
  set G := gq (rdc a ρ) ρ with hG
  set ζ := lg (rdc a ρ) with hζ
  have hζ0 : 0 < ζ := Gc.gc_lg_pos e6
  have hGδ : G < δ := (geq_lt_next hρE h.ρ1 hlT hl1 h.ρτ h.τU.2).trans h.τδ
  have hρδ : ρ < δ := hρG.trans hGδ
  have hζG : ζ < G :=
    (lg_le hl0.ne').trans_lt (hlE.trans_le (geq_eN_le hρE h.ρ1 hlT hl1))
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
  have hcbL : OT.CB (tlg l d) ρ := cb_tlg hρE.pos (hgl.trans_lt hgρ) hdρ
  obtain ⟨-, -, WL, ZL, wL, hζWZ, hfL⟩ := h.pkg_ot hcbL (by rw [← e3]; exact one_le_iff_pos.2 hζ0)
  rw [← e3] at hζWZ
  have w45 := w4.union wL
  have w5 := w45.insW (hρPG.trans le_self_add) hPGζδ
    (Or.inr ⟨G * G + G, Finset.mem_union_left _ (Finset.mem_union_left _ (by simp)), ζ,
      (by
        rcases Finset.mem_union.1 hζWZ with h' | h'
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h')
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ h')),
      lt_add_of_pos_right _ hζ0, hζG.trans_le ((le_mul_left _ hG0).trans le_self_add |>.trans le_self_add),
      rfl⟩)
  set K' := F.K ⟨a', ha'a⟩ with hK'
  have hga'ρ : gtc a' < ρ := hg'.trans_lt hgρ
  have hgK : K'.g < ρ := (F.g_le _).trans_lt hga'ρ
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
  have hgy : gtc a < f ρ := C.lt hgρ
  have hga'y : gtc a' < f ρ := hg'.trans_lt hgy
  obtain ⟨f1, f2, f3, -, f5, -⟩ := hF (f ρ) hyE hgy
  rw [f5]
  have hTρ : K'.K.sys.top ρ = gq (1 + rdc a' ρ) ρ := gfF_top F ha ⟨a', ha'a⟩ hρE h.ρ1 hga'ρ
  have hTy : K'.K.sys.top (f ρ) = gq (1 + rdc a' (f ρ)) (f ρ) := gfF_top F ha ⟨a', ha'a⟩ hyE hy1 hga'y
  have hEG : gq (1 + rdc a' ρ) ρ < G :=
    geq_lt hρE h.ρ1 hlE (gfF_lt hl ha (b := ⟨a', ha'a⟩) hρE hgρ hga'ρ)
  have hfEG : f (K'.K.sys.top ρ) < f G := C.mono hTA hGA (by rw [hTρ]; exact hEG)
  have hEy : gq (rdc a' (f ρ)) (f ρ) < f G := by
    have h1 := (hIE A f hWE hZE ⟨C.1, hgA⟩).2
    rw [hTy] at h1
    exact (geq_mono hyE hy1 (gfO_lt (ha'a.trans ha) hyE hga'y) le_add_self).trans_lt (h1.trans_lt hfEG)
  have hyl := rdc_lt_eN hyE a hgy
  by_cases hU : UpsPt (f G)
  · exact (geq_lt_next hyE hy1 (eN_T hyE hy1 hyl).1 (eN_T hyE hy1 hyl).2 hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    have hsrc : le1 G (G * G + G + ζ) := (h.lowδ _ _ hρG hPGζδ.le).2 hLG.1
    have himg := C.cov1 G hGA _ hPGζA hsrc
    have hR := (C.sk _ (C.low _ hGA) hU _).1 himg
    have hfζ : lg (rdc a (f ρ)) ≤ f ζ := by
      have := hfL A f hWL hZL C.1
      rw [← e3, ← f3] at this
      exact this
    have hadd1 : f (G * G + G) + f ζ = f (G * G + G + ζ) := C.add (G * G + G) hPGA ζ hζA _ hPGζA rfl
    have hadd2 : f (G * G) + f G = f (G * G + G) := C.add (G * G) hPA G hGA _ hPGA rfl
    have hle : f G * f G + f G + lg (rdc a (f ρ)) ≤ f (G * G + G + ζ) := by
      rw [← hadd1, ← hadd2]
      exact add_le_add (add_le_add hPge le_rfl) hfζ
    have hlo : f G ≤ f G * f G + f G + lg (rdc a (f ρ)) :=
      ((le_mul_left _ hfE.pos).trans le_self_add).trans le_self_add
    have ha'l : rdc a' (f ρ) < rdc a (f ρ) := rdc_mono hyE ha ha'a hgy hga'y
    exact Ge.ge_not_le1R_lim hyE hy1 hyl f1 f2 ha'l hfE hEy hlt (le1R_of_le hlo hle hR)

end GfLK

/-- **The gated limit layer for a limit code `a`**: the union with top `ϑˣ(Ω₁·Ω₁ + 1 + rdc a x)`, gated at `gtc a`. -/
noncomputable def gfLimL (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) : GdLay (gtc a) where
  sys := gfUSys a hl ha F
  E := fun x => gq (1 + rdc a x) x
  top_eq := fun x hx hx1 hg => (gfO_facts ha hx hx1 hg).2.2.2.1.symm
  exp_dvd := fun x hx hx1 hg => opow_dvd_of_inE (gfO_facts ha hx hx1 hg).2.2.2.1 (gfO_facts ha hx hx1 hg).2.1.le
  exp_lt := fun x hx hx1 hg => (gfO_facts ha hx hx1 hg).2.2.1
  top_gt := fun x hx hx1 hg => (gfO_facts ha hx hx1 hg).2.1
  top_lt_ups := fun x u hx hx1 hg hxu hu => gfO_lt_next ha hx hx1 hg hxu hu.2
  lt_top_E := fun x hx hx1 hg p h => gfU_val_lt hl ha F hx hx1 hg p h
  exact := fun σ ρ hσ hρ hB _ p hp => (F.K p.1).K.exact σ ρ hσ hρ hB ((F.g_le p.1).trans_lt hp.1) p.2 hp.2
  exp_pi := fun _ ρ _ _ hB hg => geq_pi hB (gfO_pi hB ha hg)
    (eN_T hB.2.1 hB.2.2.2 (gfO_lt ha hB.2.1 (hg.trans hB.2.2.1))).2
  top_wit := fun _ _ _ h hg => GfLK.gfTopWit hl ha F h hg

/-- **The gated limit base package** (gtc `gtc a`). -/
noncomputable def gfLimB (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) : GdB where
  g := gtc a
  K := gfLimL a hl ha F
  ek := fun x hx hx1 hg => (gfO_facts ha hx hx1 hg).2.2.2.1
  mem := fun x hx hx1 hg => (gfO_facts ha hx hx1 hg).1

theorem gfLimB_E (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) (x : Ordinal.{0}) :
    (gfLimB a hl ha F).K.E x = gq (1 + rdc a x) x := rfl

theorem gfLimB_g (a : Ordinal.{0}) (hl : IsSuccLimit a) (ha : a < gfE) (F : GfLimF a) :
    (gfLimB a hl ha F).g = gtc a := rfl



end Googology.Trans.PoR.InaccPsi.R2.Gf
