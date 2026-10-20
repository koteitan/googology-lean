import Googology.Trans.PoR.InaccPsi.R2.LvGW

/-!
# Lemma IMG for `LvGT`: the theta steps at a level term

* `LvG.lth_facts8`, `LvG.lth_lt`, `LvG.lth_le`, `LvG.lth_lh` (the facts, the monotonicity and the exact reach at a
  level term `l(x)`), `LvG.lgCore` (the core `LvW.gCore` at `β = l(y)`);
* `LvGK.lvgFixTransfer`, `LvGK.lvgImg_th_fixed`, `_succ`, `_limit`, `LvGK.lvgImg_th` (**Lemma IMG at an `ε`-number
  `v = ϑᵖ(Ω₁·l(ρ) + r)`**, from the IMG of the values below `v`: the steps of `R2.LvWI` with the block witness
  `LvGK.lvgWitL`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace LvG

variable {x : Ordinal.{0}} {l : LvGT}

/-- The level facts of a level term. -/
theorem lev_facts (hx : InE x) (hx1 : x < Om1) (hl : ¬ LvGT.noB l) (hlc : LvGT.CBt l x) :
    LvGT.val l x ∈ Tset x ∧ x ≤ LvGT.val l x ∧ LvGT.val l x < Om1 :=
  ⟨(LvGT.lvg_T hx hx1 l hlc).1, LvGT.le_of_not_noB hx hx1 l hlc hl, LvGT.lvg_lt_Om1 hx hx1 l hlc⟩

/-- The facts at a level term. -/
theorem lth_facts8 {η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hl : ¬ LvGT.noB l)
    (hlc : LvGT.CBt l x) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    Om1 * LvGT.val l x + η ∈ Tset x ∧ Om1 * LvGT.val l x + η < OmTwo ∧
    vt x (Om1 * LvGT.val l x + η) ∈ Tset x ∧ x < vt x (Om1 * LvGT.val l x + η) ∧
    vt x (Om1 * LvGT.val l x + η) < Om1 ∧ InE (vt x (Om1 * LvGT.val l x + η)) ∧
    Indec (vt x (Om1 * LvGT.val l x + η)) ∧ η < vt x (Om1 * LvGT.val l x + η) := by
  obtain ⟨hLT, hxL, hL1⟩ := lev_facts hx hx1 hl hlc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := Lv.gen_facts hx hx1 hLT hxL hL1 hη hη1
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h9⟩

/-- A level is below the value. -/
theorem lth_lev_lt {η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hl : ¬ LvGT.noB l)
    (hlc : LvGT.CBt l x) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    LvGT.val l x < vt x (Om1 * LvGT.val l x + η) := by
  obtain ⟨hLT, hxL, hL1⟩ := lev_facts hx hx1 hl hlc
  exact (Lv.gen_facts hx hx1 hLT hxL hL1 hη hη1).2.2.2.2.2.2.2.1

theorem lth_lt {σ η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hl : ¬ LvGT.noB l)
    (hlc : LvGT.CBt l x) (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1) (hση : σ < η) :
    vt x (Om1 * LvGT.val l x + σ) < vt x (Om1 * LvGT.val l x + η) := by
  obtain ⟨hLT, hxL, hL1⟩ := lev_facts hx hx1 hl hlc
  exact ul_eta_lt hx hx1 ((Lu.lu_one_lt_E hx).le.trans hxL) hLT hL1 hσ hη hη1 hση

theorem lth_le {σ η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hl : ¬ LvGT.noB l)
    (hlc : LvGT.CBt l x) (hσ : σ ∈ Tset x) (hη : η ∈ Tset x) (hη1 : η < Om1) (hση : σ ≤ η) :
    vt x (Om1 * LvGT.val l x + σ) ≤ vt x (Om1 * LvGT.val l x + η) := by
  obtain ⟨hLT, hxL, hL1⟩ := lev_facts hx hx1 hl hlc
  exact ul_eta_le hx hx1 ((Lu.lu_one_lt_E hx).le.trans hxL) hLT hL1 hσ hη hη1 hση

/-- The exact reach at a level term. -/
theorem lth_lh {η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hl : ¬ LvGT.noB l)
    (hlc : LvGT.CBt l x) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    IsLh1 (vt x (Om1 * LvGT.val l x + η))
      (Lu.luL (vt x (Om1 * LvGT.val l x + η)) (LvGT.val l x) + luZeta x (LvGT.val l x) η) := by
  obtain ⟨hLT, hxL, hL1⟩ := lev_facts hx hx1 hl hlc
  exact Lv.lv_lh_gen hx hx1 hLT hxL hL1 hη hη1

/-- **The core at a level term** `β = l(y)`, with `β < a`. -/
theorem lgCore {y a r' g : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (hl : ¬ LvGT.noB l)
    (hlc : LvGT.CBt l y) (hβa : LvGT.val l y < a) (hr'T : r' ∈ Tset y) (hr'1 : r' < Om1)
    (haT : a ∈ Tset y) (hya : y < a) (ha1 : a < Om1) (haE : InE a)
    (hr'a : r' < a) (hg : le1R a g) (hLg : Lu.luL a (LvGT.val l y) ≤ g)
    (hlt : a < vt y (Om1 * LvGT.val l y + r')) :
    ∃ s, s ∈ Tset y ∧ s < Om1 ∧ s < r' ∧
      vt y (Om1 * LvGT.val l y + s) = a ∧ g ≤ Lu.luL a (LvGT.val l y) + luZeta y (LvGT.val l y) s := by
  obtain ⟨hLT, hyL, hL1⟩ := lev_facts hy hy1 hl hlc
  exact LvW.gCore hy hy1 ((Lu.lu_one_lt_E hy).le.trans hyL) hLT hL1 hr'T hr'1 haT hya ha1 haE
    hβa hr'a hg hLg hlt

end LvG

namespace LvGK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- Fixed-point transfer for a theta level that follows the changing base. -/
theorem lvgFixTransfer {σ γ : Ordinal.{0}} {l : LvGT} (hσ : UpsPt σ) (hl : ¬ LvGT.noB l)
    (hB : Bases σ ρ) (hlc : LvGT.CBt l σ)
    (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1)
    (hfix : ∀ s, s < γ → vt ρ (Om1 * LvGT.val l ρ + s) ≤ γ) :
    ∀ s, s < pi σ ρ γ → vt σ (Om1 * LvGT.val l σ + s) ≤ pi σ ρ γ := by
  intro s hs
  have hσE := hB.1
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  have hpγT : pi σ ρ γ ∈ Tset σ := (pi_bijOn hB).1.mapsTo hγ
  have hpγ1 := vz_pi_lt_Om1 hB hγ hγ1
  have hsT : s ∈ Tset σ := vz_T_down hσE hσ1 hpγT hpγ1 hs.le
  obtain ⟨s', hs'TB, hs'e⟩ := (pi_bijOn hB).1.surjOn hsT
  have hs'γ : s' < γ := by
    by_contra hge; push Not at hge
    have hh := ((pi_bijOn hB).2.le_iff_le hγ hs'TB).2 hge
    rw [hs'e] at hh
    exact absurd hs (not_lt.2 hh)
  have hs'1 : s' < Om1 := hs'γ.trans hγ1
  have hpl := LvGT.pi hσ h.ρU hB l hlc
  obtain ⟨-, hρL, hL1⟩ := LvG.lev_facts h.ρE h.ρ1 hl (LvGT.CBt.mono hB.2.2.1.le hlc)
  obtain ⟨hvTB, hpv⟩ := LvET.pi_vt_tl hB hpl.1 hρL hL1 hs'TB hs'1
  rw [hpl.2] at hpv
  have hh := ((pi_bijOn hB).2.le_iff_le hvTB hγ).2 (hfix s' hs'γ)
  rwa [hpv, hs'e] at hh

/-- The fixed-point remainder case for a base-dependent theta term. -/
theorem lvgImg_th_fixed {l : LvGT} (hl : ¬ LvGT.noB l) (hlc : LvGT.CBt l ρ)
    {r v : Ordinal.{0}}
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hζ : luZeta ρ (LvGT.val l ρ) r = 0)
    (hfix : ∀ s, s < r → vt ρ (Om1 * LvGT.val l ρ + s) ≤ r)
    (hve : vt ρ (Om1 * LvGT.val l ρ + r) = v) (hvB : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvG.LvGImg ρ δ u W Z s) :
    ∃ W Z s, LvG.LvGImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, hvT, hρv, -, hvE, -, hrTheta⟩ :=
    LvG.lth_facts8 hρE hρ1 hl hlc hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hvT hρv hvE
  have hvδ : v < δ := hvB
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  let L := Lu.luL v (LvGT.val l ρ)
  have hβv' : LvGT.val l ρ < v := by rw [← hve]; exact LvG.lth_lev_lt hρE hρ1 hl hlc hrT hr1
  obtain ⟨WL, ZL, -, wzL, hLW, hcsL, IL, ILb⟩ := lvgWitL h hvE hρv hvδ hl hlc hβv' I1
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (LvGT.val l ρ) r) := by
    have hh := (LvG.lth_lh hρE hρ1 hl hlc hrT hr1).1
    simpa [L, hve] using hh
  have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by simpa [hζ] using hsrcR)
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz := ((w1.union wzL).union wzE).insZ (upsPt_inE h.ρU).pos
  let W : Finset Ordinal := (W1 ∪ WL) ∪ {v, v + v}
  let Z : Finset Ordinal := insert 0 (Z1 ∪ ZL)
  have hwz' : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz
  refine ⟨W, Z, .tl l s1, hwz', ⟨hl, hlc, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvGT.cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_insert_of_mem (by simp [hcsL c hc])
    · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
  · rw [LvGT.val_tl, e1, hve]
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp : v ∈ ({v, v + v} : Finset Ordinal)))
  · intro A f hW hZ C
    obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hWL' : ↑WL ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp [W])
    have hvvA : v + v ∈ A := hW (by simp [W])
    have hLA : L ∈ A := hWL' (Finset.mem_coe.2 hLW)
    have hlcy : LvGT.CBt l (f ρ) := LvG.cbt_img C hlc (fun c hc => hZ (by simp [Z, hcsL c hc]))
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hcb1y := LvG.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvGT.val_tl]
    by_cases hU : UpsPt (f v)
    · exact (LvGT.lvg_lt_ups hyE hy1 (t := .tl l s1) ⟨hl, hlcy, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL' hZL C hfE
    obtain ⟨hs1T, hs1top⟩ := LvGT.lvg_T hyE hy1 s1 hcb1y
    have hs11 : LvGT.val s1 (f ρ) < Om1 := hs1top.trans (gT_facts hyE hy1 _).2.2.1
    obtain ⟨hθT, hθtop⟩ := LvGT.lvg_T hyE hy1 (.tl l s1) ⟨hl, hlcy, hcb1y⟩
    have hθ1 : LvGT.val (.tl l s1) (f ρ) < Om1 := hθtop.trans (gT_facts hyE hy1 _).2.2.1
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT hθ1 hlt.le
    obtain ⟨s, -, -, hsr, hsa, -⟩   :=
      LvG.lgCore hyE hy1 hl hlcy (ILb A f hWL' hZL C) hs1T hs11 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hfL hlt
    have hpi := LvGT.pi C.ups h.ρU hB s1 hcb1y
    have htr := lvgFixTransfer (ρ := ρ) (τ := τ) (δ := δ) h
      (σ := f ρ) (γ := LvGT.val s1 ρ) (l := l) C.ups hl hB hlcy hpi.1 (by rw [e1]; exact hr1)
      (by intro q hq; have hqr : q < r := by simpa [e1] using hq
          calc
            vt ρ (Om1 * LvGT.val l ρ + q) ≤ r := hfix q hqr
            _ = LvGT.val s1 ρ := e1.symm) s
      (by rw [hpi.2]; exact hsr)
    rw [hpi.2, hsa] at htr
    exact (not_lt_of_ge htr) (hb1.trans_lt hfrv)

/-- The successor remainder case for a base-dependent theta term. -/
theorem lvgImg_th_succ {l : LvGT} (hl : ¬ LvGT.noB l) (hlc : LvGT.CBt l ρ)
    {r0 r v : Ordinal.{0}}
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hr0T : r0 ∈ Tset ρ) (hr01 : r0 < Om1)
    (hrs : r = r0 + 1) (hζ : luZeta ρ (LvGT.val l ρ) r = 0)
    (hve : vt ρ (Om1 * LvGT.val l ρ + r) = v) (hvB : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvG.LvGImg ρ δ u W Z s) :
    ∃ W Z s, LvG.LvGImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, hvT, hρv, hv1, hvE, hvI, hrTheta⟩ :=
    LvG.lth_facts8 hρE hρ1 hl hlc hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hvT hρv hv1 hvE hvI
  have hvδ : v < δ := hvB
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  have hr0r : r0 < r := by rw [hrs]; exact lt_add_of_pos_right _ zero_lt_one
  let v0 := vt ρ (Om1 * LvGT.val l ρ + r0)
  have hv0v : v0 < v := by
    rw [← hve]
    exact LvG.lth_lt hρE hρ1 hl hlc hr0T hrT hr1 hr0r
  obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
  obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
  let L := Lu.luL v (LvGT.val l ρ)
  obtain ⟨WL, ZL, -, wzL, hLW, hcsL, IL, ILb⟩ :=
    lvgWitL (ρ := ρ) (τ := τ) (δ := δ) h hvE hρv hvδ hl hlc
      (by rw [← hve]; exact LvG.lth_lev_lt hρE hρ1 hl hlc hrT hr1) I1
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (LvGT.val l ρ) r) := by
    have hh := (LvG.lth_lh hρE hρ1 hl hlc hrT hr1).1
    simpa [L, hve] using hh
  have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by simpa [hζ] using hsrcR)
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz0 := ((((w1.union w2).union w3).union wzL).union wzE).insZ (upsPt_inE h.ρU).pos
  let W : Finset Ordinal := (((W1 ∪ W2) ∪ W3) ∪ WL) ∪ {v, v + v}
  let Z : Finset Ordinal := insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ ZL)
  have hwz : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz0
  refine ⟨W, Z, .tl l s1, hwz, ⟨hl, hlc, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvGT.cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_insert_of_mem (by simp [hcsL c hc])
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (cs1 c hc))))
  · rw [LvGT.val_tl, e1, hve]
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp : v ∈ ({v, v + v} : Finset Ordinal)))
  · intro A f hW hZ C
    obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hW3 : ↑W3 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hWL' : ↑WL ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZ3 : ↑Z3 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp [W])
    have hvvA : v + v ∈ A := hW (by simp [W])
    have hLA : L ∈ A := hWL' (Finset.mem_coe.2 hLW)
    have hlcy : LvGT.CBt l (f ρ) := LvG.cbt_img C hlc (fun c hc => hZ (by simp [Z, hcsL c hc]))
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hv0A : v0 ∈ A := mem_A m2 hW2 hZ2
    have hcb1y := LvG.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hcb2y := LvG.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
    have hcb3y := LvG.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvGT.val_tl]
    by_cases hU : UpsPt (f v)
    · exact (LvGT.lvg_lt_ups hyE hy1 (t := .tl l s1) ⟨hl, hlcy, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL' hZL C hfE
    have hLg : Lu.luL (f v) (LvGT.val l (f ρ)) ≤ f L := by simpa [L] using hfL
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    obtain ⟨hs1T, hs1top⟩ := LvGT.lvg_T hyE hy1 s1 hcb1y
    have hs11 : LvGT.val s1 (f ρ) < Om1 := hs1top.trans (gT_facts hyE hy1 _).2.2.1
    have hθT := LvGT.lvg_T hyE hy1 (.tl l s1) ⟨hl, hlcy, hcb1y⟩
    have hθ1 : LvGT.val (.tl l s1) (f ρ) < Om1 := hθT.2.trans (gT_facts hyE hy1 _).2.2.1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT.1 hθ1 hlt.le
    obtain ⟨s, hsT, hs1, hsr, hsa, -⟩   :=
      LvG.lgCore hyE hy1 hl hlcy (ILb A f hWL' hZL C) hs1T hs11 hfvT hyv hfv1 hfE
        (hb1.trans_lt hfrv) hR hLg hlt
    have hsrcopy : LvGT.val s1 (f ρ) = LvGT.val s3 (f ρ) + 1 := by
      have hc : LvGT.CBt (.sm s3 (.cst 1)) (f ρ) := ⟨hcb3y, one_lt_of_upsPt C.ups⟩
      have hh := (LvGT.uni_eq C.ups h.ρU hB hcb1y hc).1
        (by rw [LvGT.val_sm, LvGT.val_cst, e1, e3, hrs])
      simpa [LvGT.val_sm, LvGT.val_cst] using hh
    have hsle : s ≤ LvGT.val s3 (f ρ) := Order.lt_add_one_iff.1 (by rw [hsrcopy] at hsr; exact hsr)
    have hprev : LvGT.val (.tl l s3) (f ρ) ≤ f v0 := by
      have hh := (LvGT.uni_eq C.ups h.ρU hB (show LvGT.CBt (.tl l s3) (f ρ) from ⟨hl, hlcy, hcb3y⟩) hcb2y).1
        (by simp [LvGT.val_tl, e3, e2, v0])
      change vt (f ρ) (Om1 * LvGT.val l (f ρ) + LvGT.val s3 (f ρ)) ≤ f v0
      rw [← LvGT.val_tl, hh]
      exact hb2
    obtain ⟨hs3T, hs3top⟩ := LvGT.lvg_T hyE hy1 s3 hcb3y
    have hs31 : LvGT.val s3 (f ρ) < Om1 := hs3top.trans (gT_facts hyE hy1 _).2.2.1
    obtain ⟨-, -, -, -, -, -, -, hηθ⟩ := LvG.lth_facts8 hyE hy1 hl hlcy hs3T hs31
    have hmon := LvG.lth_le hyE hy1 hl hlcy hsT hs3T hs31 hsle
    have hltContr : f v ≤ f v0 := by rw [hsa] at hmon; exact hmon.trans hprev
    exact (not_lt_of_ge hltContr) hfv0v

/-- The nonzero limit-remainder case for a base-dependent theta term. -/
theorem lvgImg_th_limit {l : LvGT} (hl : ¬ LvGT.noB l) (hlc : LvGT.CBt l ρ)
    {r0 z r v : Ordinal.{0}}
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hr0T : r0 ∈ Tset ρ)
    (hrs : r = r0 + ω ^ z) (hz : lg r = z) (hz0 : z ≠ 0)
    (hζ : luZeta ρ (LvGT.val l ρ) r = lg r)
    (hve : vt ρ (Om1 * LvGT.val l ρ + r) = v) (hvB : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvG.LvGImg ρ δ u W Z s) :
    ∃ W Z s, LvG.LvGImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, -, hρv, -, hvE, -, hrTheta⟩ :=
    LvG.lth_facts8 hρE hρ1 hl hlc hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hρv hvE
  have hvδ : v < δ := hvB
  have hrpos : 0 < r := by
    rw [hrs]
    exact lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (opow_pos z omega0_pos))
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hzle : z ≤ r := by simpa [hz] using (lg_le hrne)
  have hzv : z < v := hzle.trans_lt hrv
  have hr0r : r0 < r := by rw [hrs]; exact lt_add_of_pos_right _ (opow_pos z omega0_pos)
  let v0 := vt ρ (Om1 * LvGT.val l ρ + r0)
  have hv0v : v0 < v := by
    rw [← hve]
    exact LvG.lth_lt hρE hρ1 hl hlc hr0T hrT hr1 hr0r
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
  obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
  obtain ⟨W4, Z4, sz, w4, cb4, cs4, e4, m4, b4⟩ := I1 z hzv
  let L := Lu.luL v (LvGT.val l ρ)
  have hβv' : LvGT.val l ρ < v := by rw [← hve]; exact LvG.lth_lev_lt hρE hρ1 hl hlc hrT hr1
  obtain ⟨WL, ZL, -, wzL, hLW, hcsL, IL, ILb⟩ := lvgWitL h hvE hρv hvδ hl hlc hβv' I1
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (LvGT.val l ρ) r) := by
    have hh := (LvG.lth_lh hρE hρ1 hl hlc hrT hr1).1
    simpa [L, hve] using hh
  have hLzδ : L + z < δ := (inE_indec h.δE).add_lt hLδ (hzv.trans hvδ)
  have hsrc : le1 v (L + z) := by
    apply (h.lowδ _ _ hρv hLzδ.le).2
    simpa [hζ, hz] using hsrcR
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz0 := (((((w1.union w2).union w3).union w4).union wzL).union wzE).insZ (upsPt_inE h.ρU).pos
  have hW0 : WZ ρ δ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v})
      (insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅)) := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz0
  have hzm : z ∈ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v}) ∪
      insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅) := by
    rcases Finset.mem_union.1 m4 with hm | hm
    · exact Finset.mem_union_left _ (by simp [hm])
    · exact Finset.mem_union_right _ (by simp [hm])
  have hβ1 : 1 ≤ LvGT.val l ρ := (Lu.lu_one_lt_E hρE).le.trans (LvGT.le_of_not_noB hρE hρ1 l hlc hl)
  have hβv : LvGT.val l ρ < v := hβv'
  have hvL : v ≤ L :=
    (Ordinal.le_mul_left v (by norm_num : (0 : Ordinal.{0}) < 2)).trans (Lu.lu_two_le_luL hvE hβ1 hβv)
  have hLm : L ∈ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v}) ∪
      insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅) := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hLW))
  have hwz := hW0.insW (hρv.le.trans (hvL.trans le_self_add)) hLzδ
    (Or.inr ⟨L, hLm, z, hzm,
      lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
      (lt_of_lt_of_le hzv hvL).trans_le le_self_add, rfl⟩)
  let W : Finset Ordinal := insert (L + z) (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v})
  let Z : Finset Ordinal := insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL)
  have hwz' : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz
  refine ⟨W, Z, .tl l s1, hwz', ⟨hl, hlc, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvGT.cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_insert_of_mem (by simp [hcsL c hc])
    · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
  · rw [LvGT.val_tl, e1, hve]
  · simp [W]
  · intro A f hW hZ C
    obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hW3 : ↑W3 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hW4 : ↑W4 ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hWL' : ↑WL ⊆ A := fun x hx => hW (by simp [W, Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZ3 : ↑Z3 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZ4 : ↑Z4 ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Z, Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp [W])
    have hvvA : v + v ∈ A := hW (by simp [W])
    have hLzA : L + z ∈ A := hW (by simp [W])
    have hLA : L ∈ A := hWL' (Finset.mem_coe.2 hLW)
    have hlcy : LvGT.CBt l (f ρ) := LvG.cbt_img C hlc (fun c hc => hZ (by simp [Z, hcsL c hc]))
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hv0A : v0 ∈ A := mem_A m2 hW2 hZ2
    have hzA : z ∈ A := mem_A m4 hW4 hZ4
    have hcb1y := LvG.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hcb2y := LvG.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
    have hcb3y := LvG.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    have hcb4y := LvG.cbt_img C cb4 (fun c hc => hZ4 (Finset.mem_coe.2 (cs4 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hb4 := b4 A f hW4 hZ4 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvGT.val_tl]
    by_cases hU : UpsPt (f v)
    · exact (LvGT.lvg_lt_ups hyE hy1 (t := .tl l s1) ⟨hl, hlcy, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hfLz : f (L + z) = f L + f z := (C.add L hLA z hzA _ hLzA rfl).symm
    have hR : le1R (f v) (f L + f z) := by
      have hh := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA _ hLzA hsrc)
      rwa [hfLz] at hh
    have hfL := IL A f hWL' hZL C hfE
    have hLf : Lu.luL (f v) (LvGT.val l (f ρ)) ≤ f L := by simpa [L] using hfL
    have hLg : Lu.luL (f v) (LvGT.val l (f ρ)) ≤ f L + f z := hLf.trans le_self_add
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    have hsrcopy : LvGT.val s1 (f ρ) = LvGT.val s3 (f ρ) + ω ^ LvGT.val sz (f ρ) := by
      have hc : LvGT.CBt (.sm s3 (.pw sz)) (f ρ) := ⟨hcb3y, hcb4y⟩
      have hh := (LvGT.uni_eq C.ups h.ρU hB hcb1y hc).1
        (by rw [LvGT.val_sm, LvGT.val_pw, e1, e3, e4, hrs])
      simpa [LvGT.val_sm, LvGT.val_pw] using hh
    have hprev : LvGT.val (.tl l s3) (f ρ) ≤ f v0 := by
      have hh := (LvGT.uni_eq C.ups h.ρU hB
        (show LvGT.CBt (.tl l s3) (f ρ) from ⟨hl, hlcy, hcb3y⟩) hcb2y).1
        (by simp [LvGT.val_tl, e3, e2, v0])
      have hh' : vt (f ρ) (Om1 * LvGT.val l (f ρ) + LvGT.val s3 (f ρ)) = s2.val (f ρ) := by
        simpa [LvGT.val_tl] using hh
      change vt (f ρ) (Om1 * LvGT.val l (f ρ) + LvGT.val s3 (f ρ)) ≤ f v0
      rw [hh']
      exact hb2
    obtain ⟨hs1T, hs1top⟩ := LvGT.lvg_T hyE hy1 s1 hcb1y
    have hs11 : LvGT.val s1 (f ρ) < Om1 := hs1top.trans (gT_facts hyE hy1 _).2.2.1
    obtain ⟨hs3T, hs3top⟩ := LvGT.lvg_T hyE hy1 s3 hcb3y
    have hs31 : LvGT.val s3 (f ρ) < Om1 := hs3top.trans (gT_facts hyE hy1 _).2.2.1
    obtain ⟨hθT, hθtop⟩ := LvGT.lvg_T hyE hy1 (.tl l s1) ⟨hl, hlcy, hcb1y⟩
    have hθ1 : LvGT.val (.tl l s1) (f ρ) < Om1 := hθtop.trans (gT_facts hyE hy1 _).2.2.1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT hθ1 hlt.le
    obtain ⟨s, hsT, -, hsr, hsa, hgs⟩   :=
      LvG.lgCore hyE hy1 hl hlcy (ILb A f hWL' hZL C) hs1T hs11 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hLg hlt
    rw [hsrcopy] at hsr
    rcases le_or_gt s (LvGT.val s3 (f ρ)) with hsle | hslt
    · obtain ⟨-, -, -, -, -, -, -, hηθ⟩ := LvG.lth_facts8 hyE hy1 hl hlcy hs3T hs31
      have hm := LvG.lth_le hyE hy1 hl hlcy hsT hs3T hs31 hsle
      rw [hsa] at hm
      exact (not_lt_of_ge (hm.trans hprev)) hfv0v
    · let d := s - LvGT.val s3 (f ρ)
      have hde : LvGT.val s3 (f ρ) + d = s := Ordinal.add_sub_cancel_of_le hslt.le
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0, add_zero] at hde
        exact absurd hde (ne_of_lt hslt)
      have hdz : d < ω ^ LvGT.val sz (f ρ) :=
        (add_lt_add_iff_left _).1 (by rw [hde]; exact hsr)
      have hlgd : lg d < LvGT.val sz (f ρ) :=
        (opow_lt_opow_iff_right one_lt_omega0).1
          (lt_of_le_of_lt (le_of_dvd hd0 (lg_dvd hd0)) hdz)
      have hlgadd : lg s = lg d := by rw [← hde]; exact Lu.lu_lg_add_right hd0
      have hζs : luZeta (f ρ) (LvGT.val l (f ρ)) s ≤ lg s := Lu.lu_zeta_le_lg
      have h1 : Lu.luL (f v) (LvGT.val l (f ρ)) + luZeta (f ρ) (LvGT.val l (f ρ)) s <
          Lu.luL (f v) (LvGT.val l (f ρ)) + f z := by
        apply (add_lt_add_iff_left _).2
        exact lt_of_le_of_lt hζs (by rw [hlgadd]; exact hlgd.trans_le hb4)
      have hLf : Lu.luL (f v) (LvGT.val l (f ρ)) ≤ f L := by simpa [L] using hfL
      have h2 : Lu.luL (f v) (LvGT.val l (f ρ)) + f z ≤ f L + f z := add_le_add hLf le_rfl
      exact absurd (hgs.trans_lt (h1.trans_le h2)) (lt_irrefl _)

/-- The full remainder induction step for a base-dependent theta term. -/
theorem lvgImg_th {l : LvGT} (hl : ¬ LvGT.noB l) (hlc : LvGT.CBt l ρ)
    {r v : Ordinal.{0}}
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1)
    (hve : vt ρ (Om1 * LvGT.val l ρ + r) = v) (hvB : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvG.LvGImg ρ δ u W Z s) :
    ∃ W Z s, LvG.LvGImg ρ δ v W Z s := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hrv⟩ :=
    LvG.lth_facts8 (upsPt_inE h.ρU) h.ρ1 hl hlc hrT hr1
  rw [hve] at hrv
  by_cases hlim : ∃ σ, σ < r ∧ r < vt ρ (Om1 * LvGT.val l ρ + σ)
  · have hr0 : r ≠ 0 := by
      obtain ⟨σ, hσ, -⟩ := hlim
      exact (lt_of_le_of_lt zero_le hσ).ne'
    have hζ : luZeta ρ (LvGT.val l ρ) r = lg r := Lu.lu_zeta_lim hlim
    obtain ⟨r0, hrs, -, hr0r⟩ := lg_split hr0
    let z := lg r
    have hzv : z < v := (lg_le hr0).trans_lt hrv
    have hr0T : r0 ∈ Tset ρ := vz_T_down (upsPt_inE h.ρU) h.ρ1 hrT hr1 hr0r.le
    have hr01 : r0 < Om1 := hr0r.trans hr1
    by_cases hz0 : z = 0
    · have hrs' : r = r0 + 1 := by simpa [z, hz0, opow_zero] using hrs
      have hζ0 : luZeta ρ (LvGT.val l ρ) r = 0 := by simpa [z, hz0] using hζ
      exact lvgImg_th_succ h hl hlc hrT hr1 hr0T hr01 hrs' hζ0 hve hvB I1
    · exact lvgImg_th_limit h hl hlc hrT hr1 hr0T hrs (by rfl) hz0 hζ hve hvB I1
  · have hfix : ∀ σ, σ < r → vt ρ (Om1 * LvGT.val l ρ + σ) ≤ r := by
      intro σ hσ
      by_contra hnot
      exact hlim ⟨σ, hσ, lt_of_not_ge hnot⟩
    have hζ : luZeta ρ (LvGT.val l ρ) r = 0 := Lu.lu_zeta_fix hfix
    exact lvgImg_th_fixed h hl hlc hrT hr1 hζ hfix hve hvB I1



end LvGK

end Googology.Trans.PoR.InaccPsi.R2
