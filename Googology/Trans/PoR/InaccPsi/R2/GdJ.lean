import Googology.Trans.PoR.InaccPsi.R2.GdI

/-!
# Lemma IMG for every value below the stage tops over a gated base layer, the IMG packages of the terms and of the tops

At a base `ρ` where the values below `E_K(ρ)` are values of `K` (`LxRep`) with the IMG of `K` (`LxBase`; both hold at
every restart, `lxRep_ri`, `lxBase_ri`), by induction on `v < gdP B N ρ` for every `N` (`GdGK.imgGd`): below
`ε_{E_K(ρ)+1}` by the terms of `R2.GdX` over `K` (`GdGK.gdImg_low`: the IMG of `K`, the witness pair of its top),
above it constants, sums, `ε`-bases (`GdGK.gdImg_E`), atoms (`GdGK.gdImg_atom`), constant levels (`GdGK.gdImg_th0`) and
level terms (`GdGK.gdImg_th`; the level of `ϑᵖ(Ω₁·q + r)`, `ρ ≤ q < gdP B M ρ`, is a term of stage `≤ M` by `gd_rep`,
not base-free at the `υ`-point `ρ`).  `GdGK.pkgGd`: the IMG package of every term; `GdGK.gdTopPkg`: **the IMG package
of every top `gdP B n`** (the top is the value of the term `gdTm n`).

No new axiom beyond the cited facts already in the repo.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gd

open Ordinal Order Lu GdT

namespace GdGK

variable {B : GdB}

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ) (hgB : B.g < ρ)
include h hgB

/-- The tops lie below the next `υ`-point `δ`. -/
theorem gdK_top_lt_δ (N : ℕ) : gdP B N ρ < δ :=
  (GdT.gd_top_lt_next h.ρE h.ρ1 hgB N h.ρτ h.τU.2).trans h.τδ

/-- IMG is closed under ordinal addition when the two summands already have witnesses. -/
theorem gdImg_sm {u1 u2 v : Ordinal.{0}} (hρv : ρ ≤ v) (hvδ : v < δ)
    (hu1 : u1 < v) (hu2 : u2 < v) {W1 Z1 W2 Z2 : Finset Ordinal.{0}}
    {s1 s2 : GdT B} (h1 : GdG.GdGImg ρ δ u1 W1 Z1 s1) (h2 : GdG.GdGImg ρ δ u2 W2 Z2 s2)
    (hsum : u1 + u2 = v) :
    ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ v W Z s := by
  classical
  obtain ⟨w1, c1, cs1, e1, m1, b1⟩ := h1
  obtain ⟨w2, c2, cs2, e2, m2, b2⟩ := h2
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
    · rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine ⟨insert v (W1 ∪ W2), Z1 ∪ Z2, .sm s1 s2, ?_⟩
  refine ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2, hsum⟩),
    ⟨c1, c2⟩, ?_, by simp [e1, e2, hsum], by simp, ?_⟩
  · intro c hc
    simp only [GdT.cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_union_left _ (cs1 c hc)
    · exact Finset.mem_union_right _ (cs2 c hc)
  · intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have hadd := C.add u1 (mem_A m1 hW1 hZ1) u2 (mem_A m2 hW2 hZ2) v hvA hsum
    rw [GdT.val_sm, ← hadd]
    exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- An epsilon value can be represented by an exponential term with the IMG epsilon base. -/
theorem gdImg_E {v : Ordinal.{0}} (hρv : ρ ≤ v) (hvE : InE v) (hvδ : v < δ)
    {W Z : Finset Ordinal.{0}} {s : GdT B} (hI : GdG.GdGImg ρ δ v W Z s) :
    ∃ W' Z', ∃ se s' : GdT B, GdG.GdGImg ρ δ v W' Z' (.pw (.sm se s')) ∧
      InE (GdT.val se ρ) ∧ GdT.val se ρ + GdT.val s' ρ < eN (GdT.val se ρ) := by
  classical
  obtain ⟨w, cb, hcs, e, m, b⟩ := hI
  have hρE := h.ρE
  have hv0 : 0 < v := hvE.pos
  have hvv : v + v < δ := (inE_indec h.δE).add_lt hvδ hvδ
  have hm' : v ∈ W ∪ insert 0 Z := by
    rcases Finset.mem_union.1 m with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
  have wz : WZ ρ δ (insert (v + v) W) (insert 0 Z) :=
    (w.insZ hρE.pos).insW (hρv.trans le_self_add) hvv
      (Or.inr ⟨v, hm', v, hm', lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
  refine ⟨insert (v + v) W, insert 0 Z, s, .cst 0,
    ⟨wz, ⟨cb, hρE.pos⟩, ?_, ?_, ?_, ?_⟩, by rw [e]; exact hvE,
    by rw [e, GdT.val_cst, add_zero]; exact lt_eN v⟩
  · intro c hc
    simp only [GdT.cs, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact Finset.mem_insert_of_mem (hcs c hc)
    · exact Finset.mem_insert_self _ _
  · rw [GdT.val_pw, GdT.val_sm, GdT.val_cst, add_zero, e]
    exact hvE
  · rcases Finset.mem_union.1 m with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
  · intro A f hW hZ C
    have hW0 : ↑W ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := mem_A m hW0 hZ0
    have hbv := b A f hW0 hZ0 C
    have hfE : InE (f v) := by
      rcases eq_or_lt_of_le hρv with rfl | hρv'
      · exact upsPt_inE C.ups
      have hvvA : v + v ∈ A := hW (by simp)
      have hsrc : le1 v (v + v) :=
        (h.lowδ _ _ hρv' hvv.le).2 (by rw [← mul_two_eq]; exact (le1R_two_iff hv0).2 hvE)
      have himg : le1 (f v) (f v + f v) := by
        have hh := C.cov1 v hvA _ hvvA hsrc
        rwa [← C.add v hvA v hvA _ hvvA rfl] at hh
      by_cases hU : UpsPt (f v)
      · exact upsPt_inE hU
      · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
        have h0 : 0 < f v := lt_of_le_of_lt zero_le (C.mono C.rho hvA hρv')
        exact (le1R_two_iff h0).1 (by rw [mul_two_eq]; exact hR)
    rw [GdT.val_pw, GdT.val_sm, GdT.val_cst, add_zero]
    have hh := (opow_le_opow_iff_right one_lt_omega0).2 hbv
    rwa [show ω ^ f v = f v from hfE] at hh

/-- **Lemma IMG at an atom** `v = ω^L ≥ ρ` that is not an `ε`-number, from the IMG of the values below `v` (the
atom form for the indecomposable ones). -/
theorem gdImg_atom {L : Ordinal.{0}} (hρv : ρ ≤ ω ^ L) (hE : ¬ InE (ω ^ L)) (hvB : ω ^ L < δ)
    (I1 : ∀ u, u < ω ^ L → ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ u W Z s)
    (I2 : ∀ u, u < ω ^ L → ρ ≤ u → Indec u → ∃ W Z, ∃ se s' : GdT B, GdG.GdGImg ρ δ u W Z (pw (sm se s')) ∧
      InE (val se ρ) ∧ val se ρ + val s' ρ < eN (val se ρ)) :
    ∃ W Z, ∃ se s' : GdT B, GdG.GdGImg ρ δ (ω ^ L) W Z (pw (sm se s')) ∧ InE (val se ρ) ∧
      val se ρ + val s' ρ < eN (val se ρ) := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρE' : ω ^ ρ = ρ := hρE
  have hvδ : ω ^ L < δ := hvB
  have hρL : ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [hρE']; exact hρv)
  have hLv : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
    (fun h' => hE (by unfold InE; rw [← h']; exact h'.symm))
  obtain ⟨n, -, hn1, hn2⟩ := evA_bracket hρE hρL
    (show L < evA ρ (L + 1) from lt_of_lt_of_le (lt_add_one L) (le_evA_idx ρ _))
  set e := evA ρ n with hedef
  have heE : InE e := evA_E _ _
  have heE' : ω ^ e = e := heE
  have hρe : ρ ≤ e := le_evA hρE n
  have hnext : eN e = evA ρ (n + 1) := by rw [hedef, evA_add_one]
  have hev : e < ω ^ L := lt_of_le_of_lt hn1 hLv
  obtain ⟨We, Ze, se, we, cbe, cse, ee', me, ie⟩ := I1 e hev
  set β := L - e with hβdef
  have heβ : e + β = L := Ordinal.add_sub_cancel_of_le hn1
  have hβn : e + β < eN e := by rw [heβ, hnext]; exact hn2
  rw [← heβ] at hρv hE hvB hvδ I1 I2 hev ⊢
  have hβ0 : β ≠ 0 := by
    intro h0; rw [h0, add_zero] at hE; exact hE (by unfold InE; rw [heE', heE'])
  set v := ω ^ (e + β) with hvdef
  have hβv : e + β < v := exp_lt_atomE hβ0 hβn
  have hρv' : ρ < v := lt_of_le_of_lt (hρe.trans le_self_add) hβv
  have hv1 : v < Om1 := hvδ.trans h.δ1
  obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
  have hzβ : lg β ≤ β := lg_le hβ0
  set v'' := ω ^ (e + β'') with hv''def
  have hv''v : v'' < v :=
    (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
  have hρv'' : ρ ≤ v'' := (hρe.trans le_self_add).trans (right_le_opow _ one_lt_omega0)
  have heβ''n : e + β'' < eN e := lt_of_le_of_lt (add_le_add (le_refl e) hβ''β.le) hβn
  obtain ⟨W1, Z1, t1, s'', ⟨w1, c1, cs1, e1, m1, b1⟩, hE1, hlt1⟩ := I2 v'' hv''v hρv'' (indec_opow _)
  have e1' : val t1 ρ + val s'' ρ = e + β'' := by
    have := e1; rw [val_pw, val_sm] at this; exact opow_inj this
  have hnn : val t1 ρ = e := vz_ebase_unique hE1 heE (by rw [← e1']; exact le_self_add)
    (by rw [← e1']; exact hlt1) le_self_add heβ''n
  rw [hnn] at e1'
  have hs'' : val s'' ρ = β'' := (add_left_cancel_iff).1 e1'
  obtain ⟨ct1, c1⟩ := c1
  have cst1 : ∀ c ∈ cs t1, c ∈ Z1 := fun c hc => cs1 c (by simp [cs, hc])
  have cs1' : ∀ c ∈ cs s'', c ∈ Z1 := fun c hc => cs1 c (by simp [cs, hc])
  have he1 : e < Om1 := hev.trans hv1
  -- the bases of `t1` and `se` agree at every copied base, and are `ε`-numbers there
  have hagree : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Z1 ⊆ A → ↑Ze ⊆ A → GdCtx B.g ρ A f →
      val t1 (f ρ) = val se (f ρ) ∧ InE (val t1 (f ρ)) := by
    intro A f hZ1 hZe C
    have hct1 := GdG.cbt_img C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
    have hcse := GdG.cbt_img C cbe (fun c hc => hZe (Finset.mem_coe.2 (cse c hc)))
    have hB := h.img_bases C.1
    refine ⟨(GdT.uni_eq C.ups h.ρU hB (C.lt hgB) hct1 hcse).1 (by rw [hnn, ee']), ?_⟩
    have hpi := GdT.pi C.ups h.ρU hB (C.lt hgB) t1 hct1
    rw [← hpi.2]
    exact vz_pi_E C.ups h.ρU hB hpi.1 (by rw [hnn]; exact he1) (by rw [hnn]; exact heE)
  rcases eq_or_ne (lg β) 0 with hz0 | hz0
  · -- `β = β'' + 1`
    have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
    have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
    refine ⟨insert v W1, insert 1 Z1, t1, sm s'' (cst 1),
      ⟨(w1.insZ h1ρ).insW hρv'.le hvδ (Or.inl (indec_opow _)), ⟨ct1, c1, h1ρ⟩, ?_, ?_,
      Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩, by rw [hnn]; exact heE,
      by rw [hnn, val_sm, val_cst, hs'', ← hβs]; exact hβn⟩
    · intro c hc
      simp only [cs, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc | rfl
      · exact Finset.mem_insert_of_mem (cst1 c hc)
      · exact Finset.mem_insert_of_mem (cs1' c hc)
      · exact Finset.mem_insert_self _ _
    · rw [val_pw, val_sm, val_sm, val_cst, hs'', hnn, ← hβs]
    intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
    have hb := b1 A f hW1 hZ1 C
    rw [val_pw, val_sm] at hb
    have hlt : f v'' < f v := C.mono h1A hvA hv''v
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
    rw [hc] at hlt
    rw [val_pw, val_sm, val_sm, val_cst, hc, ← add_assoc]
    have h3 : val t1 (f ρ) + val s'' (f ρ) < c :=
      (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
    exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
  -- `β = β'' + ω^z`, `z > 0`
  set z := lg β with hzdef
  have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
  have hzv : z < v := lt_of_le_of_lt (hzβ.trans le_add_self) hβv
  have hzδ : z < δ := hzv.trans hvδ
  have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
  obtain ⟨W3, Z3, sz, w3, c3, cs3, e3, m3, b3⟩ := I1 z hzv
  have hsrc : le1 v (v + z) :=
    h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hβ0 hdβ) hzv.le hρv'
      (hδI.add_lt hvδ hzδ).le
  have hvzδ : v + z < δ := hδI.add_lt hvδ hzδ
  have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
  have hvvz : v < v + z := lt_add_of_pos_right v hz0'
  have hev' : e < v := lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)) hβv.le
  have heδ : e < δ := hev'.trans hvδ
  -- a copy that is a `υ`-point is above every term value at the copied base
  have hups : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), GdCtx B.g ρ A f → v ∈ A →
      UpsPt (f v) → ∀ s' : GdT B, CBt s' (f ρ) → val s' (f ρ) ≤ f v := by
    intro A f C hvA hU s' hs'
    obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C.1
    exact (GdT.gd_lt_ups hyE hy1 (C.lt hgB) hs' (C.mono C.rho hvA hρv') hU).le
  rcases eq_or_ne β'' 0 with hb0 | hb0
  · -- `β = ω^z`
    have hβz : β = ω ^ z := by rw [hgs, hb0, zero_add]
    set W0 := W1 ∪ W3 ∪ We with hW0
    set Z0 := insert 0 (Z1 ∪ Z3 ∪ Ze) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := ((w1.union w3).union we).insZ hρE.pos
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m3 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
    have hem0 : e ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 me with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
    set Wx := if z ≤ e then insert (e + z) W0 else W0 with hWx
    have hW0x : W0 ⊆ Wx := by
      rw [hWx]; split_ifs
      · exact Finset.subset_insert _ _
      · exact subset_refl _
    have wzx : WZ ρ δ Wx Z0 := by
      rw [hWx]; split_ifs with hze
      · exact wz0.insW (hρe.trans le_self_add) (hδI.add_lt heδ hzδ)
          (Or.inr ⟨e, hem0, z, hzm0, lt_add_of_pos_right _ hz0',
            lt_of_le_of_lt hze (lt_add_of_pos_right _ hz0'), rfl⟩)
      · exact wz0
    have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert v Wx ∪ Z0 := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (hW0x hx))
      · exact Finset.mem_union_right _ hx
    have wzf : WZ ρ δ (insert (v + z) (insert v Wx)) Z0 :=
      (wzx.insW hρv'.le hvδ (Or.inl (indec_opow _))).insW (hρv'.le.trans le_self_add) hvzδ
        (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm0, hvvz,
          hzvz, rfl⟩)
    refine ⟨insert (v + z) (insert v Wx), Z0, t1, pw sz, ⟨wzf, ⟨ct1, c3⟩, ?_, ?_,
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩,
      by rw [hnn]; exact heE, by rw [hnn, val_pw, e3, ← hβz]; exact hβn⟩
    · intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_insert_of_mem (by simp [cst1 c hc])
      · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
    · rw [val_pw, val_sm, val_pw, e3, hnn, ← hβz]
    intro A f hW hZ C
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hW0x (Finset.mem_coe.1 hx)))))
    have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
      hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
      hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hWe : ↑We ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hZe : ↑Ze ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm0 hW0A hZ
    have heA : e ∈ A := mem_A hem0 hW0A hZ
    have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
    have hct1 : CBt t1 (f ρ) := GdG.cbt_img C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
    obtain ⟨hag, hE1y⟩ := hagree A f hZ1 hZe C
    have hfe : val t1 (f ρ) ≤ f e := by rw [hag]; exact ie A f hWe hZe C
    have hfev : f e < f v := C.mono heA hvA hev'
    have hCB : CBt sz (f ρ) := GdG.cbt_img C c3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    by_cases hU : UpsPt (f v)
    · exact hups A f C hvA hU (pw (sm t1 (pw sz))) ⟨hct1, hCB⟩
    obtain ⟨a, ha, hda⟩ := h.copy_atom C.1 hvA hzA hvzA hz0 hzv.le h0A hsrc
    rw [val_pw, val_sm, val_pw, ha]
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
    have hE1y' : ω ^ val t1 (f ρ) = val t1 (f ρ) := hE1y
    by_cases hze : z ≤ e
    · have hezA : e + z ∈ A := by
        have : e + z ∈ Wx := by rw [hWx, if_pos hze]; exact Finset.mem_insert_self _ _
        exact hW (by simp [this])
      obtain ⟨c, hc, hdc⟩ : ∃ c, f e = ω ^ c ∧ ω ^ f z ∣ c := by
        rcases eq_or_lt_of_le hρe with he0 | hρe'
        · have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
          refine ⟨f ρ, by rw [← he0, hfE], ?_⟩
          have hzρ : z ≤ ρ := he0 ▸ hze
          exact opow_dvd_of_inE (upsPt_inE C.ups) ((C.mono.le_iff_le hzA C.rho).2 hzρ)
        · have hsrce : le1 e (e + z) := by
            have := h.src_gen (a' := e) hz0 heE.pos.ne' (opow_dvd_of_inE heE hze)
              (by rw [heE']; exact hze) (by rw [heE']; exact hρe')
              (by rw [heE']; exact (hδI.add_lt heδ hzδ).le)
            rwa [heE'] at this
          exact h.copy_atom C.1 heA hzA hezA hz0 hze h0A hsrce
      have hcl : val t1 (f ρ) ≤ c := by
        rw [hc, ← hE1y'] at hfe; exact (opow_le_opow_iff_right one_lt_omega0).1 hfe
      have hca : c < a := by
        have := hfev; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      exact (add_le_add hcl htw).trans (dvd_next hda hdc hca)
    · push Not at hze
      have hfz : f e < f z := C.mono heA hzA hze
      have h1 : val t1 (f ρ) < ω ^ f z :=
        lt_of_le_of_lt hfe (hfz.trans_le (right_le_opow _ one_lt_omega0))
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, opow_zero] at ha
        have : (1 : Ordinal.{0}) < f v :=
          lt_of_le_of_lt (one_le_iff_pos.2 hE1y.pos) (lt_of_le_of_lt hfe hfev)
        rw [ha] at this; exact lt_irrefl _ this
      have h2 : val t1 (f ρ) + ω ^ val sz (f ρ) ≤ ω ^ f z := by
        rcases htw.lt_or_eq with hlt | heq
        · exact (isPrincipal_add_omega0_opow _ h1 hlt).le
        · rw [heq, add_omega0_opow h1]
      exact h2.trans (le_of_dvd ha0 hda)
  · -- `β'' ≠ 0`: the source atom of `v''` too
    have hzb : z ≤ β'' := (right_le_opow z one_lt_omega0).trans (le_of_dvd hb0 hdvd)
    have hzvb : z < v'' := lt_of_le_of_lt (hzb.trans le_add_self) (exp_lt_atomE hb0 heβ''n)
    have hv''zδ : v'' + z < δ := hδI.add_lt (hv''v.trans hvδ) hzδ
    have hρv3 : ρ < v'' := lt_of_le_of_lt (hρe.trans le_self_add) (exp_lt_atomE hb0 heβ''n)
    have hsrc'' : le1 v'' (v'' + z) :=
      h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hb0 hdvd) hzvb.le hρv3 hv''zδ.le
    set W0 := W1 ∪ W3 ∪ We with hW0
    set Z0 := insert 0 (Z1 ∪ Z3 ∪ Ze) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := ((w1.union w3).union we).insZ hρE.pos
    have hv''m : v'' ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m1 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_left _ hx)))
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m3 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
    have wz1 : WZ ρ δ (insert (v'' + z) W0) Z0 :=
      wz0.insW (hρv''.trans le_self_add) hv''zδ
        (Or.inr ⟨v'', hv''m, z, hzm0, lt_add_of_pos_right _ hz0', lt_of_lt_of_le hzvb le_self_add, rfl⟩)
    have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert v (insert (v'' + z) W0) ∪ Z0 := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
      · exact Finset.mem_union_right _ hx
    have wzf : WZ ρ δ (insert (v + z) (insert v (insert (v'' + z) W0))) Z0 :=
      (wz1.insW hρv'.le hvδ (Or.inl (indec_opow _))).insW (hρv'.le.trans le_self_add) hvzδ
        (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm0, hvvz, hzvz, rfl⟩)
    refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, t1, sm s'' (pw sz),
      ⟨wzf, ⟨ct1, c1, c3⟩, ?_, ?_, Finset.mem_union_left _ (Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)), ?_⟩, by rw [hnn]; exact heE,
      by rw [hnn, val_sm, val_pw, hs'', e3, ← hgs]; exact hβn⟩
    · intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc | hc
      · exact Finset.mem_insert_of_mem (by simp [cst1 c hc])
      · exact Finset.mem_insert_of_mem (by simp [cs1' c hc])
      · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
    · rw [val_pw, val_sm, val_sm, val_pw, hs'', e3, hnn, ← hgs]
    intro A f hW hZ C
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))))
    have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
      hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
      hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hv''zA : v'' + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm0 hW0A hZ
    have hv''A : v'' ∈ A := mem_A hv''m hW0A hZ
    have hb'' := b1 A f hW1 hZ1 C
    rw [val_pw, val_sm] at hb''
    have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
    have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
    have hct1 : CBt t1 (f ρ) := GdG.cbt_img C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
    have hcs1 : CBt s'' (f ρ) := GdG.cbt_img C c1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1' c hc)))
    have hcs3 : CBt sz (f ρ) := GdG.cbt_img C c3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    by_cases hU : UpsPt (f v)
    · exact hups A f C hvA hU (pw (sm t1 (sm s'' (pw sz)))) ⟨hct1, hcs1, hcs3⟩
    obtain ⟨c, hc, hdc⟩ := h.copy_atom C.1 hv''A hzA hv''zA hz0 hzvb.le h0A hsrc''
    have hbc : val t1 (f ρ) + val s'' (f ρ) ≤ c := by
      rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
    have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
    obtain ⟨a, ha, hda⟩ := h.copy_atom C.1 hvA hzA hvzA hz0 hzv.le h0A hsrc
    have hca : c < a := by
      have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    rw [val_pw, ha]
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    rw [val_sm, val_sm, val_pw, ← add_assoc]
    exact (add_le_add hbc htw).trans (dvd_next hda hdc hca)

/-- **Lemma IMG at an `ε`-number `v = ϑᵖ(Ω₁·β + r)`** (`1 ≤ β < ρ` a constant level), from the IMG of the values
below `v`. -/
theorem gdImg_th0 {β r v : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβρ : β < ρ) (hrT : r ∈ Tset ρ) (hr1 : r < Om1)
    (hve : vt ρ (Om1 * β + r) = v) (hvB : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ u W Z s) : ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ v W Z s := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  obtain ⟨-, -, hvT, hρv, hv1, hvE, hvI, hrv⟩ := lu_th_facts hρE hρ1 hβ1 hβρ hrT hr1
  rw [hve] at hvT hρv hv1 hvE hvI hrv
  have hvδ : v < δ := hvB
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  obtain ⟨WL, ZL, hLW, -, wzL, IL⟩ := LuK.luWitL h hvE hρv.le hvδ hβ1 hβρ
  set L := luL v β with hL
  have hβv : β < v := hβρ.trans hρv
  have hLδ : L < δ := lu_luL_lt_eps hvE hβ1 hβv h.δE hvδ
  have hvL : v ≤ L := (le_mul_left v (by norm_num : (0 : Ordinal.{0}) < 2)).trans (lu_two_le_luL hvE hβ1 hβv)
  have wzE := LuK.luWZ_E h hvE hρv.le hvδ
  have hsrcR : le1R v (L + luZeta ρ β r) := by
    have := (lu_lh_th hρE hρ1 hβ1 hβρ hrT hr1).1; rwa [hve] at this
  have hvm : v ∈ ({v, v + v} : Finset Ordinal.{0}) := by simp
  have hvvm : v + v ∈ ({v, v + v} : Finset Ordinal.{0}) := by simp
  by_cases hl : ∃ σ, σ < r ∧ r < vt ρ (Om1 * β + σ)
  · -- the limit case: `r = r₀ + ω^z`
    have hr0 : r ≠ 0 := by obtain ⟨σ, hσ, -⟩ := hl; exact (lt_of_le_of_lt zero_le hσ).ne'
    have hζ : luZeta ρ β r = lg r := lu_zeta_lim hl
    obtain ⟨r0, hrs, -, hr0r⟩ := lg_split hr0
    set z := lg r with hz
    have hzr : z ≤ r := lg_le hr0
    have hzv : z < v := lt_of_le_of_lt hzr hrv
    have hr0T : r0 ∈ Tset ρ := vz_T_down hρE hρ1 hrT hr1 hr0r.le
    have hr01 : r0 < Om1 := hr0r.trans hr1
    set v0 := vt ρ (Om1 * β + r0) with hv0
    have hv0v : v0 < v := by rw [← hve]; exact lu_th_lt hρE hρ1 hβ1 hβρ hr0T hrT hr1 hr0r
    obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
    obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
    rcases eq_or_ne z 0 with hz0 | hz0
    · -- `r = r₀ + 1`
      rw [hz0, opow_zero] at hrs
      have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by rw [hζ, hz0, add_zero] at hsrcR; exact hsrcR)
      have wz := ((((w1.union w2).union w3).union wzL).union wzE).insZ hβρ
      refine ⟨_, _, th0 β s1, ⟨wz, ⟨hβ1, hβρ, cb1⟩, fun c hc => ?_, by rw [val_th0, e1, hve],
        Finset.mem_union_left _ (Finset.mem_union_right _ hvm), ?_⟩⟩
      · simp only [cs, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
      intro A f hW hZ C
      obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C.1
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hW3 : ↑W3 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hWL : ↑WL ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZ3 : ↑Z3 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : v ∈ A := hW (by simp)
      have hvvA : v + v ∈ A := hW (by simp)
      have hLA : L ∈ A := hWL (Finset.mem_coe.2 hLW)
      have hβA : β ∈ A := hZ (by simp)
      have hrA : r ∈ A := mem_A m1 hW1 hZ1
      have hv0A : v0 ∈ A := mem_A m2 hW2 hZ2
      have hβy : β < f ρ := C.above β hβA hβρ
      have hcb1y := GdG.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
      have hcb2y := GdG.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
      have hcb3y := GdG.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
      have hb1 := b1 A f hW1 hZ1 C
      have hb2 := b2 A f hW2 hZ2 C
      have hfrv : f r < f v := C.mono hrA hvA hrv
      have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
      have hyv : f ρ < f v := C.mono C.rho hvA hρv
      rw [val_th0]
      by_cases hU : UpsPt (f v)
      · exact (GdT.gd_lt_ups hyE hy1 (C.lt hgB) (t := th0 β s1) ⟨hβ1, hβy, hcb1y⟩ hyv hU).le
      have hfE := LuK.luFE h C.1 hvE hρv.le hvδ hvA hvvA
      have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
      have hfL := IL A f hWL hZL C.1 hfE
      have hs1y : val s1 (f ρ) = val s3 (f ρ) + 1 := by
        have hc : CBt (sm s3 (cst 1)) (f ρ) := ⟨hcb3y, one_lt_of_upsPt C.ups⟩
        have := (GdT.uni_eq C.ups h.ρU hB (C.lt hgB) hcb1y hc).1 (by rw [val_sm, val_cst, e1, e3, hrs])
        rwa [val_sm, val_cst] at this
      have hprev : vt (f ρ) (Om1 * β + val s3 (f ρ)) ≤ f v0 := by
        have := (GdT.uni_eq C.ups h.ρU hB (C.lt hgB) (t := th0 β s3) (u := s2) ⟨hβ1, hβy, hcb3y⟩ hcb2y).1
          (by rw [val_th0, e3, e2])
        rw [val_th0] at this; rw [this]; exact hb2
      obtain ⟨hr'T, hr'top⟩ := GdT.gd_T hyE hy1 (C.lt hgB) s1 hcb1y
      have hr'1 : val s1 (f ρ) < Om1 := hr'top.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
      obtain ⟨hs3T, hs3top⟩ := GdT.gd_T hyE hy1 (C.lt hgB) s3 hcb3y
      have hs31 : val s3 (f ρ) < Om1 := hs3top.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
      obtain ⟨hwT, hwtop⟩ := GdT.gd_T hyE hy1 (C.lt hgB) (th0 β s1) ⟨hβ1, hβy, hcb1y⟩
      have hw1 : val (th0 β s1) (f ρ) < Om1 := hwtop.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
      rw [val_th0] at hwT hw1
      have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
      by_contra hlt
      push Not at hlt
      have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hwT hw1 hlt.le
      obtain ⟨s, hsT, -, hsr, hsa, -⟩ :=
        luCore hyE hy1 hβy hr'T hr'1 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hfL hlt
      rw [hs1y] at hsr
      have hsle : s ≤ val s3 (f ρ) := Order.lt_add_one_iff.1 hsr
      have := (lu_th_le hyE hy1 hβ1 hβy hsT hs3T hs31 hsle).trans hprev
      rw [hsa] at this
      exact lt_irrefl _ (this.trans_lt hfv0v)
    · -- `r = r₀ + ω^z`, `z > 0`
      obtain ⟨W4, Z4, sz, w4, cb4, cs4, e4, m4, b4⟩ := I1 z hzv
      have hLzδ : L + z < δ := hδI.add_lt hLδ (hzv.trans hvδ)
      have hsrc : le1 v (L + z) := (h.lowδ _ _ hρv hLzδ.le).2 (by rw [hζ] at hsrcR; exact hsrcR)
      have wz0 := ((((((w1.union w2).union w3).union w4).union wzL).union wzE)).insZ hβρ
      have hLm : L ∈ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v}) ∪
          insert β (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅) :=
        Finset.mem_union_left _ (by simp [hLW])
      have hzm : z ∈ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v}) ∪
          insert β (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅) := by
        rcases Finset.mem_union.1 m4 with hx | hx
        · exact Finset.mem_union_left _ (by simp [hx])
        · exact Finset.mem_union_right _ (by simp [hx])
      have wz := wz0.insW (hρv.le.trans (hvL.trans le_self_add)) hLzδ
        (Or.inr ⟨L, hLm, z, hzm, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          lt_of_lt_of_le (hzv.trans_le hvL) le_self_add, rfl⟩)
      refine ⟨_, _, th0 β s1, ⟨wz, ⟨hβ1, hβρ, cb1⟩, fun c hc => ?_, by rw [val_th0, e1, hve],
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hvm)), ?_⟩⟩
      · simp only [cs, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
      intro A f hW hZ C
      obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C.1
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hW3 : ↑W3 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hW4 : ↑W4 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hWL : ↑WL ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZ3 : ↑Z3 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZ4 : ↑Z4 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : v ∈ A := hW (by simp)
      have hvvA : v + v ∈ A := hW (by simp)
      have hLzA : L + z ∈ A := hW (by simp)
      have hLA : L ∈ A := hWL (Finset.mem_coe.2 hLW)
      have hβA : β ∈ A := hZ (by simp)
      have hrA : r ∈ A := mem_A m1 hW1 hZ1
      have hv0A : v0 ∈ A := mem_A m2 hW2 hZ2
      have hzA : z ∈ A := mem_A m4 hW4 hZ4
      have hβy : β < f ρ := C.above β hβA hβρ
      have hcb1y := GdG.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
      have hcb2y := GdG.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
      have hcb3y := GdG.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
      have hcb4y := GdG.cbt_img C cb4 (fun c hc => hZ4 (Finset.mem_coe.2 (cs4 c hc)))
      have hb1 := b1 A f hW1 hZ1 C
      have hb2 := b2 A f hW2 hZ2 C
      have hb4 := b4 A f hW4 hZ4 C
      have hfrv : f r < f v := C.mono hrA hvA hrv
      have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
      have hyv : f ρ < f v := C.mono C.rho hvA hρv
      rw [val_th0]
      by_cases hU : UpsPt (f v)
      · exact (GdT.gd_lt_ups hyE hy1 (C.lt hgB) (t := th0 β s1) ⟨hβ1, hβy, hcb1y⟩ hyv hU).le
      have hfE := LuK.luFE h C.1 hvE hρv.le hvδ hvA hvvA
      have hfLz : f (L + z) = f L + f z := (C.add L hLA z hzA _ hLzA rfl).symm
      have hR : le1R (f v) (f L + f z) := by
        have := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA _ hLzA hsrc)
        rwa [hfLz] at this
      have hfL := IL A f hWL hZL C.1 hfE
      have hLg : luL (f v) β ≤ f L + f z := hfL.trans le_self_add
      have hs1y : val s1 (f ρ) = val s3 (f ρ) + ω ^ val sz (f ρ) := by
        have hc : CBt (sm s3 (pw sz)) (f ρ) := ⟨hcb3y, hcb4y⟩
        have := (GdT.uni_eq C.ups h.ρU hB (C.lt hgB) hcb1y hc).1 (by rw [val_sm, val_pw, e1, e3, e4, hrs])
        rwa [val_sm, val_pw] at this
      have hprev : vt (f ρ) (Om1 * β + val s3 (f ρ)) ≤ f v0 := by
        have := (GdT.uni_eq C.ups h.ρU hB (C.lt hgB) (t := th0 β s3) (u := s2) ⟨hβ1, hβy, hcb3y⟩ hcb2y).1
          (by rw [val_th0, e3, e2])
        rw [val_th0] at this; rw [this]; exact hb2
      obtain ⟨hr'T, hr'top⟩ := GdT.gd_T hyE hy1 (C.lt hgB) s1 hcb1y
      have hr'1 : val s1 (f ρ) < Om1 := hr'top.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
      obtain ⟨hs3T, hs3top⟩ := GdT.gd_T hyE hy1 (C.lt hgB) s3 hcb3y
      have hs31 : val s3 (f ρ) < Om1 := hs3top.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
      obtain ⟨hwT, hwtop⟩ := GdT.gd_T hyE hy1 (C.lt hgB) (th0 β s1) ⟨hβ1, hβy, hcb1y⟩
      have hw1 : val (th0 β s1) (f ρ) < Om1 := hwtop.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
      rw [val_th0] at hwT hw1
      have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
      by_contra hlt
      push Not at hlt
      have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hwT hw1 hlt.le
      obtain ⟨s, hsT, -, hsr, hsa, hgs⟩ :=
        luCore hyE hy1 hβy hr'T hr'1 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hLg hlt
      rw [hs1y] at hsr
      rcases le_or_gt s (val s3 (f ρ)) with hsle | hslt
      · have := (lu_th_le hyE hy1 hβ1 hβy hsT hs3T hs31 hsle).trans hprev
        rw [hsa] at this
        exact lt_irrefl _ (this.trans_lt hfv0v)
      · set d := s - val s3 (f ρ) with hd
        have hde : val s3 (f ρ) + d = s := Ordinal.add_sub_cancel_of_le hslt.le
        have hd0 : d ≠ 0 := by
          intro h0; rw [h0, add_zero] at hde; exact absurd hde (ne_of_lt hslt)
        have hdz : d < ω ^ val sz (f ρ) := (add_lt_add_iff_left _).1 (by rw [hde]; exact hsr)
        have hlgs : lg s = lg d := by rw [← hde]; exact lu_lg_add_right hd0
        have hlgd : lg d < val sz (f ρ) :=
          (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt (le_of_dvd hd0 (lg_dvd hd0)) hdz)
        have hζs : luZeta (f ρ) β s ≤ lg s := lu_zeta_le_lg
        have h1 : luL (f v) β + luZeta (f ρ) β s < luL (f v) β + f z :=
          (add_lt_add_iff_left _).2 (lt_of_le_of_lt hζs (by rw [hlgs]; exact hlgd.trans_le hb4))
        have h2 : luL (f v) β + f z ≤ f L + f z := add_le_add hfL le_rfl
        exact absurd (hgs.trans_lt (h1.trans_le h2)) (lt_irrefl _)
  · -- the fixed-point case: `ϑᵖ(Ω₁·β + σ) ≤ r` for every `σ < r`
    push Not at hl
    have hζ0 : luZeta ρ β r = 0 := lu_zeta_fix hl
    have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by rw [hζ0, add_zero] at hsrcR; exact hsrcR)
    have wz := ((w1.union wzL).union wzE).insZ hβρ
    refine ⟨_, _, th0 β s1, ⟨wz, ⟨hβ1, hβρ, cb1⟩, fun c hc => ?_, by rw [val_th0, e1, hve],
      Finset.mem_union_left _ (Finset.mem_union_right _ hvm), ?_⟩⟩
    · simp only [cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
    intro A f hW hZ C
    obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C.1
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hWL : ↑WL ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hZL : ↑ZL ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have hvvA : v + v ∈ A := hW (by simp)
    have hLA : L ∈ A := hWL (Finset.mem_coe.2 hLW)
    have hβA : β ∈ A := hZ (by simp)
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hβy : β < f ρ := C.above β hβA hβρ
    have hcb1y := GdG.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [val_th0]
    by_cases hU : UpsPt (f v)
    · exact (GdT.gd_lt_ups hyE hy1 (C.lt hgB) (t := th0 β s1) ⟨hβ1, hβy, hcb1y⟩ hyv hU).le
    have hfE := LuK.luFE h C.1 hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL hZL C.1 hfE
    obtain ⟨hr'T, hr'top⟩ := GdT.gd_T hyE hy1 (C.lt hgB) s1 hcb1y
    have hr'1 : val s1 (f ρ) < Om1 := hr'top.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
    obtain ⟨hwT, hwtop⟩ := GdT.gd_T hyE hy1 (C.lt hgB) (th0 β s1) ⟨hβ1, hβy, hcb1y⟩
    have hw1 : val (th0 β s1) (f ρ) < Om1 := hwtop.trans (gdP_facts B hyE hy1 (C.lt hgB) _).2.2.1
    rw [val_th0] at hwT hw1
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hwT hw1 hlt.le
    obtain ⟨s, -, -, hsr, hsa, -⟩ :=
      luCore hyE hy1 hβy hr'T hr'1 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hfL hlt
    have hpi := GdT.pi C.ups h.ρU hB (C.lt hgB) s1 hcb1y
    have htr := luFixTransfer hB hβy hpi.1 (by rw [e1]; exact hr1) (by rw [e1]; exact hl) s
      (by rw [hpi.2]; exact hsr)
    rw [hpi.2, hsa] at htr
    exact lt_irrefl _ (htr.trans_lt (hb1.trans_lt hfrv))


/-- **The IMG of the values below `ε_{E_K(ρ)+1}`** by the terms of `R2.GdX` over `K` (Lemma IMG of `K` below
`E_K(ρ)`, `LxBase`, and the witness pair of its top), read as terms here. -/
theorem gdImg_low (hb : GdXBase B ρ δ) :
    ∀ v, v < eN (B.K.E ρ) → ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ v W Z s := by
  intro v hv
  obtain ⟨W, Z, t, w, cb, cs', e, m, b⟩ := gdxt_img h hgB hb v hv
  refine ⟨W, Z, GdT.ofX t, w, GdT.ofX_cbt t ρ cb, fun c hc => cs' c (by rwa [GdT.ofX_cs] at hc),
    by rw [GdT.ofX_val]; exact e, m, fun A f hW hZ C => ?_⟩
  rw [GdT.ofX_val]; exact b A f hW hZ C

/-- **Lemma IMG for every value below `gdP B N ρ`**, at a base where the values below `E_K(ρ)` are values of `K`
(`LxRep`) with the IMG of `K` (`LxBase`). -/
theorem imgGd (hr : GdXRep B ρ) (hb : GdXBase B ρ δ) (N : ℕ) : ∀ v, v < gdP B N ρ →
    (∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ v W Z s) ∧
    (ρ ≤ v → Indec v → ∃ W Z, ∃ se s' : GdT B, GdG.GdGImg ρ δ v W Z (pw (sm se s')) ∧ InE (val se ρ) ∧
      val se ρ + val s' ρ < eN (val se ρ)) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hEρ := gdx_E_gt hρE hρ1 hgB
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans (gdK_top_lt_δ h hgB N)
  have I1 : ∀ u, u < v → ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ u W Z s := fun u hu => (IH u hu (hu.trans hv)).1
  have I2 : ∀ u, u < v → ρ ≤ u → Indec u → ∃ W Z, ∃ se s' : GdT B, GdG.GdGImg ρ δ u W Z (pw (sm se s')) ∧
      InE (val se ρ) ∧ val se ρ + val s' ρ < eN (val se ρ) := fun u hu => (IH u hu (hu.trans hv)).2
  have PE : ρ ≤ v → InE v → ∃ W Z, ∃ s : GdT B, GdG.GdGImg ρ δ v W Z s := by
    intro _ hE
    rcases le_or_gt v (B.K.E ρ) with hvE' | hEv
    · exact gdImg_low h hgB hb v (hvE'.trans_lt (lt_eN _))
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := by
      rcases N with _ | M
      · exact absurd hv (not_lt.2 hEv.le)
      · exact ⟨M, rfl⟩
    have hρv' : ρ < v := hEρ.trans hEv
    obtain ⟨hTT, -, hT1, -⟩ := gdP_facts B hρE hρ1 hgB (M + 1)
    have hv1 : v < Om1 := hv.trans hT1
    have hvT : v ∈ Tset ρ := vz_T_down hρE hρ1 hTT hT1 hv.le
    obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hρE hρ1 hvT hρv'.le hv1 (inE_indec hE)
    have hΩξ : Om1 ≤ ξ := (vt_E_iff hρE hρ1 hξT hξ2).1 ⟨by rw [hξv]; exact hρv', by rw [hξv]; exact hE⟩
    obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hρE hρ1 hξT hξ2 hΩξ
    have hqm : ξ / Om1 < gdP B M ρ :=
      gd_quot hρE hρ1 hgB M ξ hξT hξ2 (by rw [hξv]; exact hρv') (by rw [hξv]; exact hE) (by rw [hξv]; exact hEv)
        (by rw [hξv]; exact hv)
    rcases lt_or_ge (ξ / Om1) ρ with hqρ | hρq
    · exact gdImg_th0 h hgB hq1 hqρ hrT hr1 (by rw [hdec, hξv]) hvδ I1
    · obtain ⟨l, hlc, -, hle⟩ := gd_rep h.ρU hρ1 hgB hr M (ξ / Om1) hqm
      have hl : ¬ GdT.noB l := fun hn => absurd (GdT.noB_lt h.ρU hρ1 hgB l hn hlc) (not_lt.2 (hle ▸ hρq))
      exact gdImg_th h hgB hl hlc hrT hr1 (by rw [hle, hdec, hξv]) hvδ I1
  refine ⟨?_, fun hρv hI => ?_⟩
  · rcases lt_or_ge v ρ with hvρ | hρv
    · exact ⟨∅, {v}, cst v, GdG.img_cst hvρ⟩
    by_cases hI : Indec v
    · by_cases hE : InE v
      · exact PE hρv hE
      · obtain ⟨L, rfl⟩ := indec_eq_opow hI
        obtain ⟨W, Z, se, s', hY, -, -⟩ := gdImg_atom h hgB hρv hE hvδ I1 I2
        exact ⟨W, Z, _, hY⟩
    · have hD : DecompR0 v := not_not.1 hI
      rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
      · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
      obtain ⟨W1, Z1, s1, h1⟩ := I1 u1 hu1
      obtain ⟨W2, Z2, s2, h2⟩ := I1 u2 hu2
      exact gdImg_sm h hgB hρv hvδ hu1 hu2 h1 h2 hsum
  · by_cases hE : InE v
    · obtain ⟨W, Z, s, hY⟩ := PE hρv hE
      exact gdImg_E h hgB hρv hE hvδ hY
    · obtain ⟨L, rfl⟩ := indec_eq_opow hI
      exact gdImg_atom h hgB hρv hE hvδ I1 I2

/-- **The IMG package of a term of `GdT B`** (constants below `ρ`, value `≥ 1`). -/
theorem pkgGd (hr : GdXRep B ρ) (hb : GdXBase B ρ δ) {s : GdT B} (hs : CBt s ρ) (h1 : 1 ≤ val s ρ) :
    ImgPkg ρ δ (val s) := by
  classical
  have hvB := (GdT.gd_T h.ρE h.ρ1 hgB s hs).2
  obtain ⟨⟨W, Z, s0, w, c0, cs0, e0, m0, b0⟩, -⟩ := imgGd h hgB hr hb (stage s) (val s ρ) hvB
  have wzc : WZ ρ δ ∅ (cs s).toFinset :=
    ⟨by simp, fun z hz => GdT.cbt_cst hs z (List.mem_toFinset.1 hz), by simp⟩
  have hw' := w.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨h1, hvB.trans (gdK_top_lt_δ h hgB _), W, insert B.g (Z ∪ (cs s).toFinset), hw'.insZ hgB, ?_, ?_⟩
  · rcases Finset.mem_union.1 m0 with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hm))
  · intro A f hW hZ C0
    have hgA : B.g ∈ A := hZ (by simp)
    have C : GdCtx B.g ρ A f := ⟨C0, hgA⟩
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hcs : ∀ c ∈ cs s, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcs0 : ∀ c ∈ cs s0, c ∈ A := fun c hc => hZ0 (Finset.mem_coe.2 (cs0 c hc))
    have hB := h.img_bases C.1
    have heq := (GdT.uni_eq C.ups h.ρU hB (C.lt hgB) (GdG.cbt_img C hs hcs) (GdG.cbt_img C c0 hcs0)).1 e0.symm
    rw [heq]
    exact b0 A f hW hZ0 C

/-- **The IMG package of every top `gP n`**: the top is the value of the term `gdTm n`. -/
theorem gdTopPkg (hr : GdXRep B ρ) (hb' : GdXBase B ρ δ) (n : ℕ) : ImgPkg ρ δ (gdP B n) := by
  obtain ⟨hc, hv⟩ := gdTm_val (B := B) h.ρE n
  obtain ⟨h1, h2, W, Z, wz, hm, hb⟩ :=
    pkgGd h hgB hr hb' hc (by rw [hv]; exact one_le_iff_pos.2 (gdP_facts B h.ρE h.ρ1 hgB n).2.2.2.pos)
  rw [hv] at h1 h2 hm
  refine ⟨h1, h2, W, Z, wz, hm, fun A f hW hZ C => ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  have := hb A f hW hZ C
  rwa [hv, (gdTm_val (B := B) hyE n).2] at this

end GdGK

end Googology.Trans.PoR.InaccPsi.R2.Gd
