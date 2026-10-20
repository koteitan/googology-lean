import Googology.Trans.PoR.InaccPsi.R2.LvETh

/-!
# Lemma IMG for `LvET`: the invariant and the witnesses of the blocks at a level term

* `LvE.LvEImg` (the IMG statement for one value with a term of `LvET`), `LvE.cbt_img`, `LvE.img_cst`, `LvE.img_bs`;
* `LvEK.lveWitAtom` (**the atom witness with the `ε`-base `v`**: for `e < v` with the IMG of the values below `v`,
  `f(ω^{v+e}) ≥ ω^{f(v) + s(fρ)}` for a term `s` of `e`; by the sources `ω^{v+e} ≤₁ ω^{v+e} + logend(e)` and the copied
  atoms, as `Lu.LuK.luImg_atom` of `R2.LuI`);
* `LvEK.lveWitMul` (`f(v·r) ≥ f(v)·s(fρ)` for `r < v`);
* `LvEK.lveWitL` (**the block witness at a level term `l`**: `f(luL(v, l(ρ))) ≥ luL(f(v), l(fρ))`, with `l(fρ)` read by
  Lemma EXACT from the Cantor normal form of `l(ρ)`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace LvE

/-- The IMG invariant for a represented value of `LvET`. -/
def LvEImg (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : LvET) : Prop :=
  WZ ρ δ W Z ∧ LvET.CBt s ρ ∧ (∀ c ∈ LvET.cs s, c ∈ Z) ∧ LvET.val s ρ = v ∧
    v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}),
      ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f → LvET.val s (f ρ) ≤ f v

/-- Rebase the term side condition along a covering copy. -/
theorem cbt_img {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : LvET} (hs : LvET.CBt s ρ) (hA : ∀ c ∈ LvET.cs s, c ∈ A) :
    LvET.CBt s (f ρ) :=
  LvET.cbt_iff hs (fun c hc => C.above c (hA c hc) (LvET.cbt_cst hs c hc))

/-- A constant below the restart has an IMG witness. -/
theorem img_cst {ρ δ a : Ordinal.{0}} (ha : a < ρ) :
    LvEImg ρ δ a ∅ {a} (.cst a) := by
  refine ⟨WZ.empty.insZ ha, ha, ?_, rfl, by simp, ?_⟩
  · intro c hc
    simp [LvET.cs] at hc
    subst c
    simp
  · intro A f hW hZ C
    have haA : a ∈ A := hZ (by simp)
    rw [LvET.val_cst, C.fix a haA ha]

/-- The current base has an IMG witness as the base term. -/
theorem img_bs {ρ δ : Ordinal.{0}} (hρE : InE ρ) (hρδ : ρ < δ) :
    LvEImg ρ δ ρ {ρ} ∅ .bs := by
  refine ⟨(WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl hρδ
      (Or.inl (inE_indec hρE)), trivial, ?_, rfl, by simp, ?_⟩
  · intro c hc
    simp [LvET.cs] at hc
  · intro A f hW hZ C
    rfl

end LvE

namespace LvEK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The atom witness with the `ε`-base `v`**: `f(ω^{v+e}) ≥ ω^{f(v) + s(fρ)}`. -/
theorem lveWitAtom {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvE.LvEImg ρ δ u W Z s) :
    ∀ e, e < v → ∃ (W Z : Finset Ordinal.{0}) (s : LvET), LvET.CBt s ρ ∧ (∀ c ∈ LvET.cs s, c ∈ Z) ∧
      LvET.val s ρ = e ∧ ω ^ (v + e) ∈ W ∧ v ∈ W ∧ (0 : Ordinal.{0}) ∈ Z ∧ WZ ρ δ W Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        InE (f v) → ω ^ (f v + LvET.val s (f ρ)) ≤ f (ω ^ (v + e)) := by
  classical
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  have hvr : ω ^ v = v := hvE
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hev
  have hpδ : ω ^ (v + e) < δ := h.δE.opow_lt (hδI.add_lt hvδ (hev.trans hvδ))
  have hvp : v ≤ ω ^ (v + e) := by
    calc v = ω ^ v := hvr.symm
      _ ≤ ω ^ (v + e) := (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  have hρp : ρ < ω ^ (v + e) := hρv.trans_le hvp
  rcases eq_or_ne e 0 with rfl | he0
  · refine ⟨{v}, {0}, .cst 0, hρE.pos, by simp [LvET.cs], rfl, by simp [hvr], by simp, by simp,
      (WZ.empty.insZ hρE.pos).insW hρv.le hvδ (Or.inl (inE_indec hvE)), ?_⟩
    intro A f _ _ C hfE
    simp only [LvET.val_cst, add_zero, hvr]
    rw [show ω ^ f v = f v from hfE]
  obtain ⟨e', hgs, hdvd, he'e⟩ := lg_split he0
  set z := lg e with hz
  have hze : z ≤ e := lg_le he0
  have hzv : z < v := hze.trans_lt hev
  obtain ⟨W', Z', s', cb', cs', ev', hp'W, hvW', h0Z', wz', b'⟩ := IH e' he'e (he'e.trans hev)
  obtain ⟨Wz, Zz, sz, wzz, cbz, csz, evz, mz, bz⟩ := I1 z hzv
  have hp'p : ω ^ (v + e') < ω ^ (v + e) :=
    (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left v).2 he'e)
  rcases eq_or_ne z 0 with hz0 | hz0
  · -- `e = e' + 1`
    have hes : e = e' + 1 := by rw [hgs, hz0, opow_zero]
    have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
    refine ⟨insert (ω ^ (v + e)) W', insert 1 Z', .sm s' (.cst 1), ⟨cb', h1ρ⟩, ?_, ?_,
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hvW', Finset.mem_insert_of_mem h0Z',
      (wz'.insZ h1ρ).insW hρp.le hpδ (Or.inl (indec_opow _)), ?_⟩
    · intro c hc
      simp only [LvET.cs, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact Finset.mem_insert_of_mem (cs' c hc)
      · exact Finset.mem_insert_self _ _
    · rw [LvET.val_sm, LvET.val_cst, ev', hes]
    intro A f hW hZ C hfE
    have hW' : ↑W' ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ'A : ↑Z' ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hpA : ω ^ (v + e) ∈ A := hW (by simp)
    have hp'A : ω ^ (v + e') ∈ A := hW' (Finset.mem_coe.2 hp'W)
    have hb := b' A f hW' hZ'A C hfE
    have hlt : f (ω ^ (v + e')) < f (ω ^ (v + e)) := C.mono hp'A hpA hp'p
    obtain ⟨a, ha⟩ := indec_eq_opow (C.indec _ hpA (indec_opow _))
    rw [ha] at hlt ⊢
    have h3 : f v + LvET.val s' (f ρ) < a := (opow_lt_opow_iff_right one_lt_omega0).1 (hb.trans_lt hlt)
    rw [LvET.val_sm, LvET.val_cst, ← add_assoc]
    exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
  -- `z > 0`: the source atom `ω^{v+e} ≤₁ ω^{v+e} + z`
  have hzp : z < ω ^ (v + e) := hzv.trans_le hvp
  have hdve : ω ^ z ∣ v + e := by
    rw [hgs]; exact dvd_add (opow_dvd_of_inE hvE hzv.le) (dvd_add hdvd (dvd_refl _))
  have hve0 : v + e ≠ 0 := (lt_of_lt_of_le hvE.pos le_self_add).ne'
  have hpzδ : ω ^ (v + e) + z < δ := hδI.add_lt hpδ (hzv.trans hvδ)
  have hsrc : le1 (ω ^ (v + e)) (ω ^ (v + e) + z) := h.src_gen hz0 hve0 hdve hzp.le hρp hpzδ.le
  have hzm : z ∈ Wz ∪ Zz := mz
  rcases eq_or_ne e' 0 with he'0 | he'0
  · -- `e = ω^z`
    have hee : e = ω ^ z := by rw [hgs, he'0, zero_add]
    set W0 := W' ∪ Wz with hW0
    set Z0 := insert 0 (Z' ∪ Zz) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := (wz'.union wzz).insZ hρE.pos
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 hzm with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    have wz1 := wz0.insW hρp.le hpδ (Or.inl (indec_opow _))
    have wz2 := wz1.insW (hρp.le.trans le_self_add) hpzδ
      (Or.inr ⟨ω ^ (v + e), Finset.mem_union_left _ (Finset.mem_insert_self _ _), z,
        by rcases Finset.mem_union.1 hzm0 with hx | hx
           · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
           · exact Finset.mem_union_right _ hx,
        lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0), hzp.trans_le le_self_add, rfl⟩)
    refine ⟨insert (ω ^ (v + e) + z) (insert (ω ^ (v + e)) W0), Z0, .pw sz, cbz, ?_, ?_,
      by simp, by simp [hW0, hvW'], by simp [hZ0], wz2, ?_⟩
    · intro c hc
      simp only [LvET.cs] at hc
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (csz c hc))
    · rw [LvET.val_pw, evz, hee]
    intro A f hW hZ C hfE
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hWz : ↑Wz ⊆ A := fun x hx => hW0A (by simp [hW0, Finset.mem_coe.1 hx])
    have hZz : ↑Zz ⊆ A := fun x hx => hZ (by simp [hZ0, Finset.mem_coe.1 hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hZ (by simp [hZ0])
    have hvA : v ∈ A := hW0A (by simp [hW0, hvW'])
    have hpA : ω ^ (v + e) ∈ A := hW (by simp)
    have hpzA : ω ^ (v + e) + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm hWz hZz
    obtain ⟨a, ha, hda⟩ := h.copy_atom C hpA hzA hpzA hz0 hzp.le h0A hsrc
    have hbz : LvET.val sz (f ρ) ≤ f z := bz A f hWz hZz C
    have hvlt : v < ω ^ (v + e) := by
      calc v = ω ^ v := hvr.symm
        _ < ω ^ (v + e) :=
          (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right v (pos_iff_ne_zero.2 he0))
    have hfvp : f v < f (ω ^ (v + e)) := C.mono hvA hpA hvlt
    have hfE' : ω ^ f v = f v := hfE
    rw [ha] at hfvp ⊢
    have h1 : f v < a := by rw [← hfE'] at hfvp; exact (opow_lt_opow_iff_right one_lt_omega0).1 hfvp
    have hfzv : f z ≤ f v := (C.mono.le_iff_le hzA hvA).2 hzv.le
    have h2 := dvd_next hda (opow_dvd_of_inE hfE hfzv) h1
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    rw [LvET.val_pw]
    exact (add_le_add_right ((opow_le_opow_iff_right one_lt_omega0).2 hbz) _).trans h2
  · -- `e' ≠ 0`: the source atom of `ω^{v+e'}` too
    have hve'0 : v + e' ≠ 0 := (lt_of_lt_of_le hvE.pos le_self_add).ne'
    have hvp' : v ≤ ω ^ (v + e') := by
      calc v = ω ^ v := hvr.symm
        _ ≤ ω ^ (v + e') := (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
    have hzp' : z < ω ^ (v + e') := hzv.trans_le hvp'
    have hρp' : ρ < ω ^ (v + e') := hρv.trans_le hvp'
    have hp'δ : ω ^ (v + e') < δ := hp'p.trans hpδ
    have hp'zδ : ω ^ (v + e') + z < δ := hδI.add_lt hp'δ (hzv.trans hvδ)
    have hdve' : ω ^ z ∣ v + e' := dvd_add (opow_dvd_of_inE hvE hzv.le) hdvd
    have hsrc' : le1 (ω ^ (v + e')) (ω ^ (v + e') + z) := h.src_gen hz0 hve'0 hdve' hzp'.le hρp' hp'zδ.le
    set W0 := W' ∪ Wz with hW0
    set Z0 := insert 0 (Z' ∪ Zz) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := (wz'.union wzz).insZ hρE.pos
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 hzm with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    have hp'm0 : ω ^ (v + e') ∈ W0 ∪ Z0 := Finset.mem_union_left _ (Finset.mem_union_left _ hp'W)
    have wz1 := wz0.insW (hρp'.le.trans le_self_add) hp'zδ
      (Or.inr ⟨_, hp'm0, z, hzm0, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0), hzp'.trans_le le_self_add, rfl⟩)
    have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert (ω ^ (v + e)) (insert (ω ^ (v + e') + z) W0) ∪ Z0 := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      · exact Finset.mem_union_right _ hx
    have wz2 := (wz1.insW hρp.le hpδ (Or.inl (indec_opow _))).insW (hρp.le.trans le_self_add) hpzδ
      (Or.inr ⟨ω ^ (v + e), Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm0,
        lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0), hzp.trans_le le_self_add, rfl⟩)
    refine ⟨insert (ω ^ (v + e) + z) (insert (ω ^ (v + e)) (insert (ω ^ (v + e') + z) W0)), Z0,
      .sm s' (.pw sz), ⟨cb', cbz⟩, ?_, ?_, by simp, by simp [hW0, hvW'], by simp [hZ0], wz2, ?_⟩
    · intro c hc
      simp only [LvET.cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (cs' c hc))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (csz c hc))
    · rw [LvET.val_sm, LvET.val_pw, ev', evz, ← hgs]
    intro A f hW hZ C hfE
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hW' : ↑W' ⊆ A := fun x hx => hW0A (by simp [hW0, Finset.mem_coe.1 hx])
    have hWz : ↑Wz ⊆ A := fun x hx => hW0A (by simp [hW0, Finset.mem_coe.1 hx])
    have hZ'A : ↑Z' ⊆ A := fun x hx => hZ (by simp [hZ0, Finset.mem_coe.1 hx])
    have hZz : ↑Zz ⊆ A := fun x hx => hZ (by simp [hZ0, Finset.mem_coe.1 hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hZ (by simp [hZ0])
    have hpA : ω ^ (v + e) ∈ A := hW (by simp)
    have hpzA : ω ^ (v + e) + z ∈ A := hW (by simp)
    have hp'A : ω ^ (v + e') ∈ A := hW' (Finset.mem_coe.2 hp'W)
    have hp'zA : ω ^ (v + e') + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm hWz hZz
    obtain ⟨c, hc, hdc⟩ := h.copy_atom C hp'A hzA hp'zA hz0 hzp'.le h0A hsrc'
    obtain ⟨a, ha, hda⟩ := h.copy_atom C hpA hzA hpzA hz0 hzp.le h0A hsrc
    have hb' := b' A f hW' hZ'A C hfE
    have hbz : LvET.val sz (f ρ) ≤ f z := bz A f hWz hZz C
    have hlt : f (ω ^ (v + e')) < f (ω ^ (v + e)) := C.mono hp'A hpA hp'p
    rw [hc] at hb' hlt
    rw [ha] at hlt ⊢
    have h1 : f v + LvET.val s' (f ρ) ≤ c := (opow_le_opow_iff_right one_lt_omega0).1 hb'
    have hca : c < a := (opow_lt_opow_iff_right one_lt_omega0).1 hlt
    have h2 := dvd_next hda hdc hca
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    rw [LvET.val_sm, LvET.val_pw, ← add_assoc]
    exact (add_le_add h1 ((opow_le_opow_iff_right one_lt_omega0).2 hbz)).trans h2

/-- `f(v·r) ≥ f(v)·s(fρ)` for `r < v` with a term `s` of `r`. -/
theorem lveWitMul {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvE.LvEImg ρ δ u W Z s) :
    ∀ r, r < v → ∃ (W Z : Finset Ordinal.{0}) (s : LvET), LvET.CBt s ρ ∧ (∀ c ∈ LvET.cs s, c ∈ Z) ∧
      LvET.val s ρ = r ∧ v * r ∈ W ∪ Z ∧ v ∈ W ∧ WZ ρ δ W Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        InE (f v) → f v * LvET.val s (f ρ) ≤ f (v * r) := by
  classical
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  have hvr : ω ^ v = v := hvE
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrv
  rcases eq_or_ne r 0 with rfl | hr0
  · refine ⟨{v}, {0}, .cst 0, hρE.pos, by simp [LvET.cs], rfl, by simp, by simp,
      (WZ.empty.insZ hρE.pos).insW hρv.le hvδ (Or.inl (inE_indec hvE)), ?_⟩
    intro A f _ _ _ _
    simp
  obtain ⟨r', hgs, hdvd, hr'r⟩ := lg_split hr0
  set z := lg r with hz
  have hzv : z < v := (lg_le hr0).trans_lt hrv
  obtain ⟨W', Z', s', cb', cs', ev', hm', hvW', wz', b'⟩ := IH r' hr'r (hr'r.trans hrv)
  obtain ⟨Wa, Za, sa, cba, csa, eva, hpa, hvWa, h0a, wza, ba⟩ := lveWitAtom h hvE hρv hvδ I1 z hzv
  have hvz : v * ω ^ z = ω ^ (v + z) := by rw [opow_add, hvr]
  have hvrr : v * r = v * r' + ω ^ (v + z) := by rw [hgs, mul_add, hvz]
  have hpδ : ω ^ (v + z) < δ := h.δE.opow_lt (hδI.add_lt hvδ (hzv.trans hvδ))
  have hvrδ : v * r < δ := h.δE.mul_lt hvδ (hrv.trans hvδ)
  have hvp : v ≤ ω ^ (v + z) := by
    calc v = ω ^ v := hvr.symm
      _ ≤ ω ^ (v + z) := (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hre : r = ω ^ z := by rw [hgs, hr'0, zero_add]
    refine ⟨W' ∪ Wa, Z' ∪ Za, .pw sa, cba, fun c hc => Finset.mem_union_right _ (csa c hc),
      by rw [LvET.val_pw, eva, hre], ?_, Finset.mem_union_left _ hvW', wz'.union wza, ?_⟩
    · rw [hvrr, hr'0, mul_zero, zero_add]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hpa)
    intro A f hW hZ C hfE
    have hWa : ↑Wa ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZa : ↑Za ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hb := ba A f hWa hZa C hfE
    rw [opow_add, show ω ^ f v = f v from hfE] at hb
    rw [hvrr, hr'0, mul_zero, zero_add, LvET.val_pw]
    exact hb
  have hr'z : ω ^ z ≤ r' := le_of_dvd hr'0 hdvd
  have hpr' : ω ^ (v + z) ≤ v * r' := by rw [← hvz]; exact mul_le_mul_right hr'z v
  have hpos : 0 < ω ^ (v + z) := opow_pos _ omega0_pos
  have h1 : v * r' < v * r := by rw [hvrr]; exact lt_add_of_pos_right _ hpos
  have h2 : ω ^ (v + z) < v * r := by
    rw [hvrr]
    calc ω ^ (v + z) < ω ^ (v + z) + ω ^ (v + z) := lt_add_of_pos_right _ hpos
      _ ≤ v * r' + ω ^ (v + z) := add_le_add_left hpr' _
  have hρvr : ρ ≤ v * r := (hρv.le.trans hvp).trans h2.le
  have hm1 : v * r' ∈ (W' ∪ Wa) ∪ (Z' ∪ Za) := by
    rcases Finset.mem_union.1 hm' with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
  have wz := (wz'.union wza).insW hρvr hvrδ
    (Or.inr ⟨v * r', hm1, ω ^ (v + z), Finset.mem_union_left _ (Finset.mem_union_right _ hpa), h1, h2,
      hvrr.symm⟩)
  refine ⟨insert (v * r) (W' ∪ Wa), Z' ∪ Za, .sm s' (.pw sa), ⟨cb', cba⟩, ?_,
    by rw [LvET.val_sm, LvET.val_pw, ev', eva, ← hgs], by simp,
    Finset.mem_insert_of_mem (Finset.mem_union_left _ hvW'), wz, ?_⟩
  · intro c hc
    simp only [LvET.cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_union_left _ (cs' c hc)
    · exact Finset.mem_union_right _ (csa c hc)
  intro A f hW hZ C hfE
  have hW' : ↑W' ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hWa : ↑Wa ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ'A : ↑Z' ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZa : ↑Za ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hvrA : v * r ∈ A := hW (by simp)
  have hvr'A : v * r' ∈ A := mem_A hm' hW' hZ'A
  have hpA : ω ^ (v + z) ∈ A := hWa (Finset.mem_coe.2 hpa)
  have hadd := C.add _ hvr'A _ hpA _ hvrA hvrr.symm
  rw [← hadd, LvET.val_sm, LvET.val_pw, mul_add]
  refine add_le_add (b' A f hW' hZ'A C hfE) ?_
  have hb := ba A f hWa hZa C hfE
  rwa [opow_add, show ω ^ f v = f v from hfE] at hb

omit h in
/-- `log_ω(ω^a + r) = a` and `(ω^a + r) - ω^a = r` for `r < ω^{a+1}`. -/
theorem lve_log_split {a r : Ordinal.{0}} (hr : r < ω ^ (a + 1)) :
    log ω (ω ^ a + r) = a ∧ (ω ^ a + r) - ω ^ a = r := by
  refine ⟨?_, Ordinal.add_sub_cancel _ _⟩
  have h0 : ω ^ a + r ≠ 0 := (lt_of_lt_of_le (opow_pos a omega0_pos) le_self_add).ne'
  refine (log_eq_iff one_lt_omega0 h0 a).2 ⟨le_self_add, ?_⟩
  have hab : ω ^ a < ω ^ (a + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one a)
  exact (isPrincipal_add_omega0_opow (a + 1)) hab hr

/-- **The block witness at a level term**: `f(luL(v, l(ρ))) ≥ luL(f(v), l(fρ))`. -/
theorem lveWitL {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ) {l : LvET}
    (hl : LvET.isLev l) (hlB : LvET.hasB l) (hlc : LvET.CBt l ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvE.LvEImg ρ δ u W Z s) :
    ∃ W Z : Finset Ordinal.{0}, v ∈ W ∧ WZ ρ δ W Z ∧ Lu.luL v (LvET.val l ρ) ∈ W ∧
      (∀ c ∈ LvET.cs l, c ∈ Z) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        InE (f v) → Lu.luL (f v) (LvET.val l (f ρ)) ≤ f (Lu.luL v (LvET.val l ρ)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  have hvr : ω ^ v = v := hvE
  set β := LvET.val l ρ with hβ
  obtain ⟨-, hρβ, hβe, -⟩ := lve_lev_facts hρE hρ1 hl hlB hlc
  have hev : eN ρ ≤ v := eN_le hρv hvE
  have hβv : β < v := hβe.trans_le hev
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le hρE.pos hρβ).ne'
  have hωβ : ω ≤ β := (Lu.lu_omega_lt_E hρE).le.trans hρβ
  set e := log ω β with he
  have heβ : e ≤ β := log_le_self ω β
  have hev' : e < v := heβ.trans_lt hβv
  have hωe : ω ^ e ≤ β := opow_log_le_self ω hβ0
  have hβlt : β < ω ^ (e + 1) := lt_opow_succ_log_self one_lt_omega0 β
  set r := β - ω ^ e with hr
  have hβr : ω ^ e + r = β := Ordinal.add_sub_cancel_of_le hωe
  have hrβ : r ≤ β := Ordinal.sub_le_self _ _
  have hrv : r < v := hrβ.trans_lt hβv
  have hrlt : r < ω ^ (e + 1) := hrβ.trans_lt hβlt
  have he0 : e ≠ 0 := (log_pos one_lt_omega0 hβ0 hωβ).ne'
  set lam := lg e with hlam
  have hlame : lam ≤ e := lg_le he0
  have hlamv : lam < v := hlame.trans_lt hev'
  obtain ⟨e0, hesplit, -, he0e⟩ := lg_split he0
  -- the pieces
  obtain ⟨Wa, Za, sa, cba, csa, eva, hpa, hvWa, h0a, wza, ba⟩ := lveWitAtom h hvE hρv hvδ I1 e hev'
  obtain ⟨Wm, Zm, sm', cbm, csm, evm, hmm, hvWm, wzm, bm⟩ := lveWitMul h hvE hρv hvδ I1 r hrv
  obtain ⟨Wl, Zl, sl, wzl, cbl, csl, evl, ml, bl⟩ := I1 lam hlamv
  obtain ⟨W0, Z0, s0, wz0, cb0, cs0, ev0, -, -⟩ := I1 e0 (he0e.trans hev')
  -- the source `luL(v, β) = (ω^{v+e} + λ) + v·r`
  have hvωe : v * ω ^ e = ω ^ (v + e) := by rw [opow_add, hvr]
  have hLe : Lu.luL v β = (ω ^ (v + e) + lam) + v * r := by
    unfold Lu.luL
    rw [if_neg (not_lt.2 hωβ), ← he, hvωe]
  set P := ω ^ (v + e) with hP
  have hpδ : P < δ := h.δE.opow_lt (hδI.add_lt hvδ (hev'.trans hvδ))
  have hvP : v ≤ P := by
    calc v = ω ^ v := hvr.symm
      _ ≤ ω ^ (v + e) := (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  have hρP : ρ < P := hρv.trans_le hvP
  have hlamP : lam < P := hlamv.trans_le hvP
  have hP2δ : P + lam < δ := hδI.add_lt hpδ (hlamv.trans hvδ)
  have hvrδ : v * r < δ := h.δE.mul_lt hvδ (hrv.trans hvδ)
  have hLδ : P + lam + v * r < δ := hδI.add_lt hP2δ hvrδ
  set Wb := (Wa ∪ Wm) ∪ (Wl ∪ W0) with hWb
  set Zb := (Za ∪ Zm) ∪ ((Zl ∪ Z0) ∪ (LvET.cs l).toFinset) with hZb
  have wzc : WZ ρ δ ∅ (LvET.cs l).toFinset :=
    ⟨by simp, fun c hc => LvET.cbt_cst hlc c (List.mem_toFinset.1 hc), by simp⟩
  have wzb : WZ ρ δ Wb Zb := by
    have := ((wza.union wzm).union ((wzl.union wz0).union wzc))
    simpa [hWb, hZb, Finset.union_assoc] using this
  have hPm : P ∈ Wb ∪ Zb := by simp [hWb, hpa]
  have hlm : lam ∈ Wb ∪ Zb := by
    rcases Finset.mem_union.1 ml with hx | hx
    · simp [hWb, hx]
    · simp [hZb, hx]
  have hvrm : v * r ∈ Wb ∪ Zb := by
    rcases Finset.mem_union.1 hmm with hx | hx
    · simp [hWb, hx]
    · simp [hZb, hx]
  -- insert `P + λ` and the block
  have wz1 : WZ ρ δ (insert (P + lam) Wb) Zb := by
    rcases eq_or_ne lam 0 with hl0 | hl0
    · rw [hl0, add_zero]
      exact wzb.insW hρP.le hpδ (Or.inl (indec_opow _))
    · exact wzb.insW (hρP.le.trans le_self_add) hP2δ
        (Or.inr ⟨P, hPm, lam, hlm, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hl0),
          hlamP.trans_le le_self_add, rfl⟩)
  have hmx : ∀ x ∈ Wb ∪ Zb, x ∈ insert (P + lam) Wb ∪ Zb := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
    · exact Finset.mem_union_right _ hx
  have wz2 : WZ ρ δ (insert (P + lam + v * r) (insert (P + lam) Wb)) Zb := by
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [hr0, mul_zero, add_zero, Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)]
      exact wz1
    · have hvr0 : 0 < v * r := mul_pos hvE.pos (pos_iff_ne_zero.2 hr0)
      have hvrw : v * r < (P + lam) * ω := by
        have h1 : v * r < v * ω ^ (e + 1) := mul_lt_mul_of_pos_left hrlt hvE.pos
        have h2 : v * ω ^ (e + 1) = P * ω := by rw [opow_add, opow_one, ← mul_assoc, hvωe]
        rw [h2] at h1
        exact h1.trans_le (mul_le_mul_left le_self_add ω)
      have hvrP : v * r < P + lam + v * r :=
        lt_of_le_of_ne le_add_self (fun e2 => (not_le.2 hvrw) (add_eq_right_iff_mul_omega0_le.1 e2.symm))
      exact wz1.insW (hρP.le.trans (le_self_add.trans le_self_add)) hLδ
        (Or.inr ⟨P + lam, Finset.mem_union_left _ (Finset.mem_insert_self _ _), v * r, hmx _ hvrm,
          lt_add_of_pos_right _ hvr0, hvrP, rfl⟩)
  refine ⟨insert (P + lam + v * r) (insert (P + lam) Wb), Zb, by simp [hWb, hvWa], wz2,
    by rw [hLe]; simp, fun c hc => by simp [hZb, hc], ?_⟩
  intro A f hW hZ C hfE
  have hWbA : ↑Wb ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hWa' : ↑Wa ⊆ A := fun x hx => hWbA (by simp [hWb, Finset.mem_coe.1 hx])
  have hWm' : ↑Wm ⊆ A := fun x hx => hWbA (by simp [hWb, Finset.mem_coe.1 hx])
  have hWl' : ↑Wl ⊆ A := fun x hx => hWbA (by simp [hWb, Finset.mem_coe.1 hx])
  have hZa' : ↑Za ⊆ A := fun x hx => hZ (by simp [hZb, Finset.mem_coe.1 hx])
  have hZm' : ↑Zm ⊆ A := fun x hx => hZ (by simp [hZb, Finset.mem_coe.1 hx])
  have hZl' : ↑Zl ⊆ A := fun x hx => hZ (by simp [hZb, Finset.mem_coe.1 hx])
  have hZ0' : ↑Z0 ⊆ A := fun x hx => hZ (by simp [hZb, Finset.mem_coe.1 hx])
  have hcsA : ∀ c ∈ LvET.cs l, c ∈ A := fun c hc => hZ (by simp [hZb, hc])
  have hPA : P ∈ A := hWa' (Finset.mem_coe.2 hpa)
  have hlA : lam ∈ A := mem_A ml hWl' hZl'
  have hvrA : v * r ∈ A := mem_A hmm hWm' hZm'
  have hP2A : P + lam ∈ A := hW (by simp)
  have hLA : P + lam + v * r ∈ A := hW (by simp)
  have hadd1 := C.add _ hPA _ hlA _ hP2A rfl
  have hadd2 := C.add _ hP2A _ hvrA _ hLA rfl
  -- the uniform reading of `l(fρ)`
  have hB := h.img_bases C
  have hlcy := LvE.cbt_img C hlc hcsA
  have hcay := LvE.cbt_img C cba (fun c hc => hZa' (Finset.mem_coe.2 (csa c hc)))
  have hcmy := LvE.cbt_img C cbm (fun c hc => hZm' (Finset.mem_coe.2 (csm c hc)))
  have hcly := LvE.cbt_img C cbl (fun c hc => hZl' (Finset.mem_coe.2 (csl c hc)))
  have hc0y := LvE.cbt_img C cb0 (fun c hc => hZ0' (Finset.mem_coe.2 (cs0 c hc)))
  have hU1 : LvET.val l (f ρ) = ω ^ LvET.val sa (f ρ) + LvET.val sm' (f ρ) := by
    have := (LvET.uni_eq C.ups h.ρU hB hlcy (show LvET.CBt (.sm (.pw sa) sm') (f ρ) from ⟨hcay, hcmy⟩)).1
      (by rw [LvET.val_sm, LvET.val_pw, eva, evm, ← hβ, hβr])
    simpa using this
  have hU2 : LvET.val sm' (f ρ) < ω ^ (LvET.val sa (f ρ) + 1) := by
    have := (LvET.uni_lt C.ups h.ρU hB hcmy
      (show LvET.CBt (.pw (.sm sa (.cst 1))) (f ρ) from ⟨hcay, one_lt_of_upsPt C.ups⟩)).1
      (by rw [LvET.val_pw, LvET.val_sm, LvET.val_cst, evm, eva]; exact hrlt)
    simpa using this
  have hU3 : LvET.val sa (f ρ) = LvET.val s0 (f ρ) + ω ^ LvET.val sl (f ρ) := by
    have := (LvET.uni_eq C.ups h.ρU hB hcay (show LvET.CBt (.sm s0 (.pw sl)) (f ρ) from ⟨hc0y, hcly⟩)).1
      (by rw [LvET.val_sm, LvET.val_pw, eva, ev0, evl]; exact hesplit)
    simpa using this
  obtain ⟨hlog, hsub⟩ := lve_log_split hU2
  have hlgy : lg (LvET.val sa (f ρ)) = LvET.val sl (f ρ) := by
    rw [hU3, Lu.lu_lg_add_right (opow_pos _ omega0_pos).ne', LvE.lve_lg_opow]
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  have hωy : ω ≤ LvET.val l (f ρ) :=
    (Lu.lu_omega_lt_E hyE).le.trans (LvET.lev_ge hyE l hl hlB hlcy)
  have hTgt : Lu.luL (f v) (LvET.val l (f ρ)) =
      f v * ω ^ LvET.val sa (f ρ) + LvET.val sl (f ρ) + f v * LvET.val sm' (f ρ) := by
    unfold Lu.luL
    rw [if_neg (not_lt.2 hωy), hU1, hlog, hsub, hlgy]
  rw [hTgt, hLe, ← hadd2, ← hadd1]
  have hba := ba A f hWa' hZa' C hfE
  rw [opow_add, show ω ^ f v = f v from hfE] at hba
  exact add_le_add (add_le_add hba (bl A f hWl' hZl' C)) (bm A f hWm' hZm' C hfE)

end LvEK

end Googology.Trans.PoR.InaccPsi.R2
