import Googology.Trans.PoR.InaccPsi.R2.LzV

/-!
# Lemma IMG for every value below `B₁(ρ) = sup_N ϑᵖ(Ω₁·N + B(ρ) + 1)`, with a term of `LzV`

By induction on `v < B₁(ρ)` (`lzv_img`):

* `v < B(ρ)`: a term of `R2.VzT` (`RstK.imgVz`); `v = B(ρ)`: the atom `bB` (`xtWitB`);
* an `ε`-number `v = ϑᵖ(Ω₁·q + r)` above `B(ρ)` (`lzv_th_form`, `r < v`): `lzvImg_th`, the argument of
  `RstK.vzImg_th` of `R2.VzI` for terms of `LzV` (the copy keeps `v ≤₁ v·(q+1) + ζ` of `R₁⁺`, [W07b] Thm 5.3 with
  [W07b] Def 4.1 as the axioms `vzLhT_fix`, `vzLhT_lim` of `R2.CitedVz`, which hold for every argument
  `Ω₁·q + r`, `r ∈ Tᵖ ∩ Ω₁`; a copy that is not a `υ`-point lies in `P_q`, and the minimality of `R2.VzL` at the
  base `f(ρ)` gives `ϑ^{f(ρ)}(Ω₁·q + s(f(ρ))) ≤ f(v)`);
* any other `v`: `v = ω^{z' + ω^q}` by one atom step `ω^z ≤₁ ω^z + q` of `R₁⁺` ([W07b] Theorem 2.2, `lyStep2`), or
  `ω^{z'+1}` (the copy of a power is a power), or a sum.

`lzvPkg`: the IMG package of every term of `LzV` with value `≥ 1`.  No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly LzV

/-- **The IMG statement for one value** `v` with a term `s` of `LzV` (`s(ρ) = v`, constants in `Z`). -/
def LzVImg (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : LzV) : Prop :=
  WZ ρ δ W Z ∧ CBt s ρ ∧ (∀ c ∈ cs s, c ∈ Z) ∧ val s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val s (f ρ) ≤ f v

theorem lzv_cbt_img {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : LzV} (hs : CBt s ρ) (hA : ∀ c ∈ cs s, c ∈ A) : CBt s (f ρ) :=
  cbt_iff s ρ (f ρ) hs (fun c hc => C.above c (hA c hc) (cbt_cst s ρ hs c hc))

namespace LzK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG at an `ε`-number `v = ϑᵖ(Ω₁·q + r)`** (`1 ≤ q`, `r` any element of `Tᵖ ∩ Ω₁`), from the IMG of
the values below `v`. -/
theorem lzvImg_th {q : ℕ} (hq : 1 ≤ q) {r v : Ordinal.{0}} (hrT : r ∈ Tset ρ) (hr1 : r < Om1)
    (hve : vt ρ (Om1 * (q : Ordinal.{0}) + r) = v) (hvδ : v < δ)
    (I1 : ∀ u, u < v → ∃ W Z s, LzVImg ρ δ u W Z s) : ∃ W Z s, LzVImg ρ δ v W Z s := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδI := inE_indec h.δE
  obtain ⟨-, -, hvT, hρv, hv1, hvE, hvI, hrv⟩ := vz_th_facts hρE hρ1 hq hrT hr1
  rw [hve] at hvT hρv hv1 hvE hvI hrv
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  have hvq : v * ((q + 1 : ℕ) : Ordinal.{0}) < δ := vz_mul_lt hδI hvδ _
  have hvm : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ vzMulF v q := vz_mulF_mem v q
  have hvm0 : v ∈ vzMulF v q := by have := hvm 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
  by_cases hl : ∃ σ, σ < r ∧ r < vt ρ (Om1 * (q : Ordinal.{0}) + σ)
  · have hr0 : r ≠ 0 := by obtain ⟨σ, hσ, -⟩ := hl; exact (lt_of_le_of_lt zero_le hσ).ne'
    obtain ⟨r', hrs, hdvd, hr'r⟩ := lg_split hr0
    set z := lg r with hz
    have hzr : z ≤ r := lg_le hr0
    have hzv : z < v := lt_of_le_of_lt hzr hrv
    have hr'T : r' ∈ Tset ρ := vz_T_down hρE hρ1 hrT hr1 hr'r.le
    have hr'1 : r' < Om1 := hr'r.trans hr1
    set v' := vt ρ (Om1 * (q : Ordinal.{0}) + r') with hv'
    have hv'v : v' < v := by rw [← hve]; exact vz_th_lt hρE hρ1 hq hr'T hrT hr1 hr'r
    obtain ⟨-, -, -, hρv', -, -, hv'I, -⟩ := vz_th_facts hρE hρ1 hq hr'T hr'1
    obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v' hv'v
    obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r' (hr'r.trans hrv)
    have hv'δ : v' < δ := hv'v.trans hvδ
    have hv'q : v' * ((q + 1 : ℕ) : Ordinal.{0}) < δ := vz_mul_lt hδI hv'δ _
    have hsrc' : le1 v' (v' * ((q + 1 : ℕ) : Ordinal.{0})) :=
      (h.lowδ _ _ hρv' hv'q.le).2 (vz_th_le1R hρE hρ1 hq hr'T hr'1)
    have hv'm : ∀ j : ℕ, j ≤ q → v' * ((j + 1 : ℕ) : Ordinal.{0}) ∈ vzMulF v' q := vz_mulF_mem v' q
    rcases eq_or_ne z 0 with hz0 | hz0
    · -- `r = r' + 1`
      rw [hz0, opow_zero] at hrs
      have hsrc : le1 v (v * ((q + 1 : ℕ) : Ordinal.{0})) :=
        (h.lowδ _ _ hρv hvq.le).2 (by rw [← hve]; exact vz_th_le1R hρE hρ1 hq hrT hr1)
      set W0 := W1 ∪ W2 ∪ W3 with hW0
      set Z0 := Z1 ∪ Z2 ∪ Z3 with hZ0
      have wz : WZ ρ δ (W0 ∪ vzMulF v q) Z0 :=
        vzWZ_mul ((w1.union w2).union w3) hρv.le hvI hδI hvδ q
      refine ⟨W0 ∪ vzMulF v q, Z0, th q s1, ⟨wz, ⟨hq, cb1⟩, fun c hc => ?_, by rw [val_th, e1, hve],
        Finset.mem_union_left _ (Finset.mem_union_right _ hvm0), ?_⟩⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (cs1 c hc))
      intro A f hW hZ C
      obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 ∪ vzMulF v q → ↑S ⊆ A := fun hS x hx =>
        hW (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW2 : ↑W2 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ2 : ↑Z2 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hmulA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
        hW (Finset.mem_coe.2 (Finset.mem_union_right _ (hvm j hj)))
      have hvA : v ∈ A := hW (Finset.mem_coe.2 (Finset.mem_union_right _ hvm0))
      have hrA : r ∈ A := mem_A m1 hW1 hZ1
      have hv'A : v' ∈ A := mem_A m2 hW2 hZ2
      have hcb1y := lzv_cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
      have hcb2y := lzv_cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
      have hcb3y := lzv_cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
      have hb1 := b1 A f hW1 hZ1 C
      have hb2 := b2 A f hW2 hZ2 C
      have hfrv : f r < f v := C.mono hrA hvA hrv
      have hfv'v : f v' < f v := C.mono hv'A hvA hv'v
      have hyv : f ρ < f v := C.mono C.rho hvA hρv
      rw [val_th]
      by_cases hU : UpsPt (f v)
      · exact (lzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv hU).le
      have himg : le1 (f v) (f v * ((q + 1 : ℕ) : Ordinal.{0})) := by
        have := C.cov1 v hvA _ (hmulA q le_rfl) hsrc
        rwa [vz_copy_mul C hmulA q le_rfl] at this
      have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      have hP := vz_le1R_level q hq (f v) (lt_of_le_of_lt zero_le hyv) hR
      have hs1y : val s1 (f ρ) = val s3 (f ρ) + 1 := by
        have hc : CBt (sm s3 (vz (VzTm.cst 1))) (f ρ) := ⟨hcb3y, one_lt_of_upsPt C.ups⟩
        have := (lzv_uni_eq C.ups h.ρU hB hcb1y hc).1 (by rw [val_sm, val_vz, VzTm.val_cst, e1, e3, hrs])
        rwa [val_sm, val_vz, VzTm.val_cst] at this
      have hprev2 : vt (f ρ) (Om1 * (q : Ordinal.{0}) + val s3 (f ρ)) ≤ f v' := by
        have := (lzv_uni_eq C.ups h.ρU hB (t := th q s3) (u := s2) ⟨hq, hcb3y⟩ hcb2y).1
          (by rw [val_th, e3, e2])
        rw [val_th] at this; rw [this]; exact hb2
      obtain ⟨hs1T, hs1_1⟩ := lzv_T hyE hy1 s1 hcb1y
      obtain ⟨hs3T, hs3_1⟩ := lzv_T hyE hy1 s3 hcb3y
      refine vz_th_min hyE hy1 hq hs1T hs1_1 hP hyv (hb1.trans_lt hfrv) (fun σ hσ => ?_)
      rw [hs1y] at hσ
      have hσ' : σ ≤ val s3 (f ρ) := Order.lt_add_one_iff.1 hσ
      have hσT := vz_T_down hyE hy1 hs3T hs3_1 hσ'
      exact ((vz_th_le hyE hy1 hq hσT hs3T hs3_1 hσ').trans hprev2).trans_lt hfv'v
    · -- `r = r' + ω^z`, `z > 0`
      have hsrcR : le1R v (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) := by
        have := (vz_lh_th_lim hρE hρ1 hq hrT hr1 hr0 hl).1; rwa [hve] at this
      have hvqz : v * ((q + 1 : ℕ) : Ordinal.{0}) + z < δ := hδI.add_lt hvq (hzv.trans hvδ)
      have hsrc : le1 v (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) := (h.lowδ _ _ hρv hvqz.le).2 hsrcR
      obtain ⟨W4, Z4, sz, w4, cb4, cs4, e4, m4, b4⟩ := I1 z hzv
      set W0 := W1 ∪ W2 ∪ W3 ∪ W4 with hW0
      set Z0 := insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4) with hZ0
      have wz0 : WZ ρ δ W0 Z0 := ((((w1.union w2).union w3).union w4).insZ hρE.pos)
      have wz1 := vzWZ_mul wz0 hρv.le hvI hδI hvδ q
      have wz2 := vzWZ_mul wz1 hρv'.le hv'I hδI hv'δ q
      set W5 := W0 ∪ vzMulF v q ∪ vzMulF v' q with hW5
      have hvqm : v * ((q + 1 : ℕ) : Ordinal.{0}) ∈ W5 ∪ Z0 :=
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hvm q le_rfl)))
      have hzm : z ∈ W5 ∪ Z0 := by
        rcases Finset.mem_union.1 m4 with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hW0, hx])))
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (by simp [hx]))
      have hvlt : v * ((q + 1 : ℕ) : Ordinal.{0}) < v * ((q + 1 : ℕ) : Ordinal.{0}) + z :=
        lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0)
      have hzlt : z < v * ((q + 1 : ℕ) : Ordinal.{0}) + z :=
        lt_of_lt_of_le hzv ((vz_le_mul (by omega)).trans le_self_add)
      have wz3 : WZ ρ δ (insert (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) W5) Z0 :=
        wz2.insW (hρv.le.trans ((vz_le_mul (by omega)).trans le_self_add)) hvqz
          (Or.inr ⟨_, hvqm, z, hzm, hvlt, hzlt, rfl⟩)
      refine ⟨insert (v * ((q + 1 : ℕ) : Ordinal.{0}) + z) W5, Z0, th q s1, ⟨wz3, ⟨hq, cb1⟩,
        fun c hc => Finset.mem_insert_of_mem (by simp [cs1 c hc]), by rw [val_th, e1, hve],
        Finset.mem_union_left _ (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_union_right _ hvm0))), ?_⟩⟩
      intro A f hW hZ C
      obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
          (hS (Finset.mem_coe.1 hx))))))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW2 : ↑W2 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW4 : ↑W4 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ2 : ↑Z2 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ4 : ↑Z4 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
      have hmulA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_left _
          (Finset.mem_union_right _ (hvm j hj)))))
      have hmul'A : ∀ j : ℕ, j ≤ q → v' * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hv'm j hj))))
      have hvqzA : v * ((q + 1 : ℕ) : Ordinal.{0}) + z ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have hvA : v ∈ A := by have := hmulA 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
      have hv'A : v' ∈ A := by have := hmul'A 0 (by omega); rwa [zero_add, Nat.cast_one, mul_one] at this
      have hrA : r ∈ A := mem_A m1 hW1 hZ1
      have hzA : z ∈ A := mem_A m4 hW4 hZ4
      have hcb1y := lzv_cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
      have hcb2y := lzv_cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
      have hcb3y := lzv_cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
      have hcb4y := lzv_cbt_img C cb4 (fun c hc => hZ4 (Finset.mem_coe.2 (cs4 c hc)))
      have hb1 := b1 A f hW1 hZ1 C
      have hb2 := b2 A f hW2 hZ2 C
      have hb4 := b4 A f hW4 hZ4 C
      have hfrv : f r < f v := C.mono hrA hvA hrv
      have hfv'v : f v' < f v := C.mono hv'A hvA hv'v
      have hyv : f ρ < f v := C.mono C.rho hvA hρv
      have hyv' : f ρ < f v' := C.mono C.rho hv'A hρv'
      rw [val_th]
      by_cases hU : UpsPt (f v)
      · exact (lzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv hU).le
      by_cases hU' : UpsPt (f v')
      · exact ((lzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv' hU').trans hfv'v).le
      have himg : le1 (f v) (f v * ((q + 1 : ℕ) : Ordinal.{0}) + f z) := by
        have := C.cov1 v hvA _ hvqzA hsrc
        rwa [← C.add _ (hmulA q le_rfl) z hzA _ hvqzA rfl, vz_copy_mul C hmulA q le_rfl] at this
      have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      have himg' : le1 (f v') (f v' * ((q + 1 : ℕ) : Ordinal.{0})) := by
        have := C.cov1 v' hv'A _ (hmul'A q le_rfl) hsrc'
        rwa [vz_copy_mul C hmul'A q le_rfl] at this
      have hR' := (C.sk _ (C.low _ hv'A) hU' _).1 himg'
      obtain ⟨i, hi⟩ := vz_le1R_level q hq (f v') (lt_of_le_of_lt zero_le hyv') hR'
      have hfz : f z < f v := C.mono hzA hvA hzv
      have hge := vz_le1R_ge hq (f z) (f v) i hfz (by rw [hi]; exact hfv'v) hR
      have hP := vz_le1R_level q hq (f v) (lt_of_le_of_lt zero_le hyv) (vz_le1R_base hR)
      have hs1y : val s1 (f ρ) = val s3 (f ρ) + ω ^ val sz (f ρ) := by
        have hc : CBt (sm s3 (pw sz)) (f ρ) := ⟨hcb3y, hcb4y⟩
        have := (lzv_uni_eq C.ups h.ρU hB hcb1y hc).1 (by rw [val_sm, val_pw, e1, e3, e4, hrs])
        rwa [val_sm, val_pw] at this
      have hprev2 : vt (f ρ) (Om1 * (q : Ordinal.{0}) + val s3 (f ρ)) ≤ f v' := by
        have := (lzv_uni_eq C.ups h.ρU hB (t := th q s3) (u := s2) ⟨hq, hcb3y⟩ hcb2y).1
          (by rw [val_th, e3, e2])
        rw [val_th] at this; rw [this]; exact hb2
      have hfz0 : f z ≠ 0 := by
        have h1 : f 0 < f z := C.mono h0A hzA (pos_iff_ne_zero.2 hz0)
        rw [C.fix 0 h0A hρE.pos] at h1
        exact h1.ne'
      obtain ⟨hs1T, hs1_1⟩ := lzv_T hyE hy1 s1 hcb1y
      obtain ⟨hs3T, hs3_1⟩ := lzv_T hyE hy1 s3 hcb3y
      refine vz_th_min hyE hy1 hq hs1T hs1_1 hP hyv (hb1.trans_lt hfrv) (fun σ hσ => ?_)
      have hσT := vz_T_down hyE hy1 hs1T hs1_1 hσ.le
      have hσ1 : σ < Om1 := hσ.trans hs1_1
      rw [hs1y] at hσ
      rcases lt_or_ge σ (val s3 (f ρ)) with hσs | hsσ
      · exact ((vz_th_lt hyE hy1 hq hσT hs3T hs3_1 hσs).le.trans hprev2).trans_lt hfv'v
      set d := σ - val s3 (f ρ) with hd
      have hσe : val s3 (f ρ) + d = σ := Ordinal.add_sub_cancel_of_le hsσ
      have hdz : d < ω ^ val sz (f ρ) := (add_lt_add_iff_left _).1 (by rw [hσe]; exact hσ)
      have hsb : val s3 (f ρ) < veblen (q : Ordinal.{0}) i :=
        (vzLt_vt_self hyE hy1 hq hs3T hs3_1).trans_le (by rw [hi]; exact hprev2)
      have hub := vz_th_ub hyE hy1 hq hs3T hs3_1 (by rw [hi]; exact hprev2) hsb d
        (by rw [hσe]; exact hσT) (by rw [hσe]; exact hσ1)
      rw [hσe] at hub
      refine lt_of_le_of_lt hub (lt_of_lt_of_le ((veblen_lt_veblen_iff_right).2 ?_) hge)
      rw [add_assoc]
      refine (add_lt_add_iff_left i).2 ?_
      have hd' : d < ω ^ f z := hdz.trans_le ((opow_le_opow_iff_right one_lt_omega0).2 hb4)
      have h1 : (1 : Ordinal.{0}) < ω ^ f z :=
        one_lt_omega0.trans_le (by
          have := (opow_le_opow_iff_right one_lt_omega0).2 (one_le_iff_ne_zero.2 hfz0)
          rwa [opow_one] at this)
      exact isPrincipal_add_omega0_opow _ hd' h1
  · -- `ϑᵖ(Ω₁·q + σ) ≤ r` for every `σ < r`
    push Not at hl
    have hsrc : le1 v (v * ((q + 1 : ℕ) : Ordinal.{0})) :=
      (h.lowδ _ _ hρv hvq.le).2 (by rw [← hve]; exact vz_th_le1R hρE hρ1 hq hrT hr1)
    have wz : WZ ρ δ (W1 ∪ vzMulF v q) Z1 := vzWZ_mul w1 hρv.le hvI hδI hvδ q
    refine ⟨W1 ∪ vzMulF v q, Z1, th q s1, ⟨wz, ⟨hq, cb1⟩, cs1, by rw [val_th, e1, hve],
      Finset.mem_union_left _ (Finset.mem_union_right _ hvm0), ?_⟩⟩
    intro A f hW hZ C
    obtain ⟨hyE, hy1, hB⟩ := h.vz_img_base C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hmulA : ∀ j : ℕ, j ≤ q → v * ((j + 1 : ℕ) : Ordinal.{0}) ∈ A := fun j hj =>
      hW (Finset.mem_coe.2 (Finset.mem_union_right _ (hvm j hj)))
    have hvA : v ∈ A := hW (Finset.mem_coe.2 (Finset.mem_union_right _ hvm0))
    have hrA : r ∈ A := mem_A m1 hW1 hZ
    have hcb1y := lzv_cbt_img C cb1 (fun c hc => hZ (Finset.mem_coe.2 (cs1 c hc)))
    have hb1 := b1 A f hW1 hZ C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [val_th]
    by_cases hU : UpsPt (f v)
    · exact (lzv_lt_ups hyE hy1 (t := th q s1) ⟨hq, hcb1y⟩ hyv hU).le
    have himg : le1 (f v) (f v * ((q + 1 : ℕ) : Ordinal.{0})) := by
      have := C.cov1 v hvA _ (hmulA q le_rfl) hsrc
      rwa [vz_copy_mul C hmulA q le_rfl] at this
    have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    have hP := vz_le1R_level q hq (f v) (lt_of_le_of_lt zero_le hyv) hR
    obtain ⟨hs1T, hs1_1⟩ := lzv_T hyE hy1 s1 hcb1y
    have hpi := lzv_pi C.ups h.ρU hB s1 hcb1y
    refine vz_th_min hyE hy1 hq hs1T hs1_1 hP hyv (hb1.trans_lt hfrv) (fun σ hσ => ?_)
    have htr := vz_fix_transfer (q := q) hB hpi.1 (by rw [e1]; exact hr1) (by rw [e1]; exact hl) σ
      (by rw [hpi.2]; exact hσ)
    rw [hpi.2] at htr
    exact htr.trans_lt (hb1.trans_lt hfrv)


theorem lzv_val_fρ {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {t u : LzV} (ht : CBt t ρ) (hu : CBt u ρ) (htA : ∀ c ∈ cs t, c ∈ A) (huA : ∀ c ∈ cs u, c ∈ A)
    (htu : val t ρ = val u ρ) : val t (f ρ) = val u (f ρ) :=
  (lzv_uni_eq C.ups h.ρU (h.img_bases C) (lzv_cbt_img C ht htA) (lzv_cbt_img C hu huA)).1 htu

omit h in
theorem lzVImg_sub {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : LzV} (hI : LzVImg ρ δ v W Z t)
    {A : Set Ordinal.{0}} (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : (∀ c ∈ cs t, c ∈ A) ∧ v ∈ A :=
  ⟨fun c hc => hZ (Finset.mem_coe.2 (hI.2.2.1 c hc)), mem_A hI.2.2.2.2.1 hW hZ⟩

/-- **Lemma IMG below `B₁(ρ)`.** -/
theorem lzv_img : ∀ v, v < VzB1 ρ → ∃ W Z t, LzVImg ρ δ v W Z t := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρB : ρ < VzB ρ := (vzB_omega hρE hρ1).2.1
  have hB1δ : VzB1 ρ ≤ δ := lzB1_le_next hρE hρ1 h.ρδ h.next.2.1.2
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans_le hB1δ
  rcases lt_trichotomy v (VzB ρ) with hvB | rfl | hBv
  · obtain ⟨⟨W, Z, s, hw, hc, hcs, hvs, hm, hI⟩, -⟩ := h.imgVz v hvB
    exact ⟨W, Z, vz s, hw, hc, hcs, hvs, hm, hI⟩
  · obtain ⟨hw, hBW, hI⟩ := xtWitB h
    exact ⟨_, _, bB, hw, trivial, by simp [cs], rfl, Finset.mem_union_left _ hBW,
      fun A f hW hZ C => (hI A f hW hZ C).2⟩
  by_cases hvE : InE v
  · obtain ⟨q, hq, r, hrT, hr1, hrv, he⟩ := lzv_th_form hρE hρ1 hvE hBv hv
    exact lzvImg_th h hq hrT hr1 he hvδ (fun u hu => IH u hu (hu.trans hv))
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0' | h0'
  · -- `v = ω^z`, `z = z' + ω^q`
    rw [h0', zero_add] at hvs
    set z := lg v with hz
    have hzv : z < v := by
      have hz' : z ≤ ω ^ z := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz'.trans_eq hvs.symm) fun e => hvE ?_
      show ω ^ v = v
      calc ω ^ v = ω ^ z := by rw [e]
        _ = v := hvs.symm
    have hz0 : z ≠ 0 := by
      intro e; rw [e, opow_zero] at hvs
      exact absurd (hvs ▸ hBv) (not_lt.2 (one_le_iff_pos.2 (xt_B_E hρE hρ1).pos))
    obtain ⟨z', hzs, -, hz'z⟩ := lg_split hz0
    set q := lg z with hq
    have hqz : q ≤ z := lg_le hz0
    have hqv : q < v := hqz.trans_lt hzv
    have hPv : ω ^ z' < v := by
      rw [hvs]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hz'z
    obtain ⟨Wq, Zq, tq, Iq⟩ := IH q hqv (hqv.trans hv)
    obtain ⟨Wp, Zp, tp, Ip⟩ := IH _ hPv (hPv.trans hv)
    obtain ⟨Wz, Zz, tz, Iz⟩ := IH z' (hz'z.trans hzv) ((hz'z.trans hzv).trans hv)
    set t := pw (sm tz (pw tq)) with ht
    have htv : val t ρ = v := by
      rw [ht, val_pw, val_sm, val_pw, Iz.2.2.2.1, Iq.2.2.2.1, ← hzs, ← hvs]
    have hw0 : WZ ρ δ ((Wq ∪ Wp) ∪ Wz) ((Zq ∪ Zp) ∪ Zz) := (Iq.1.union Ip.1).union Iz.1
    have hcsT : ∀ c ∈ cs t, c ∈ (Zq ∪ Zp) ∪ Zz := by
      intro c hc
      simp only [ht, cs, List.mem_append] at hc
      rcases hc with hc | hc
      · simp [Iz.2.2.1 c hc]
      · simp [Iq.2.2.1 c hc]
    have hcbT : CBt t ρ := ⟨Iz.2.1, Iq.2.1⟩
    have hmem : ∀ {x W Z}, x ∈ W ∪ Z → W ⊆ (Wq ∪ Wp) ∪ Wz → Z ⊆ (Zq ∪ Zp) ∪ Zz →
        x ∈ ((Wq ∪ Wp) ∪ Wz) ∪ ((Zq ∪ Zp) ∪ Zz) := fun hx hW hZ =>
      Finset.union_subset_union hW hZ hx
    have hPW0 := hmem Ip.2.2.2.2.1 (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
    have hqW0 := hmem Iq.2.2.2.2.1 (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
    have hcom : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑((Wq ∪ Wp) ∪ Wz) ⊆ A →
        ↑((Zq ∪ Zp) ∪ Zz) ⊆ A → ImgCtx ρ A f → val tq (f ρ) ≤ f q ∧
          ∀ e1, f (ω ^ z') = ω ^ e1 → val tz (f ρ) ≤ e1 := by
      intro A f hW hZ C
      have hWq : ↑Wq ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZq : ↑Zq ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hWp : ↑Wp ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZp : ↑Zp ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZz : ↑Zz ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      refine ⟨Iq.2.2.2.2.2 A f hWq hZq C, fun e1 he1 => ?_⟩
      have hpA := (lzVImg_sub Ip hWp hZp).1
      have hzA : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZz (Finset.mem_coe.2 (Iz.2.2.1 c hc))
      have heq := lzv_val_fρ h C (t := pw tz) (u := tp) Iz.2.1 Ip.2.1 hzA hpA
        (by rw [val_pw, Iz.2.2.2.1, Ip.2.2.2.1])
      have hle := Ip.2.2.2.2.2 A f hWp hZp C
      rw [← heq, val_pw, he1] at hle
      exact (opow_le_opow_iff_right one_lt_omega0).1 hle
    rcases eq_or_ne q 0 with hq0 | hq0
    · -- `z = z' + 1`: the copy of a power is a power
      have hw : WZ ρ δ (insert v ((Wq ∪ Wp) ∪ Wz)) ((Zq ∪ Zp) ∪ Zz) :=
        hw0.insW hρv.le hvδ (Or.inl (hvs ▸ indec_opow _))
      refine ⟨_, _, t, hw, hcbT, hcsT, htv, by simp, fun A f hW hZ C => ?_⟩
      have hW0 : ↑((Wq ∪ Wp) ∪ Wz) ⊆ A := fun x hx =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      obtain ⟨hqf, hzf⟩ := hcom A f hW0 hZ C
      have hvA : v ∈ A := hW (by simp)
      have hPA : ω ^ z' ∈ A := mem_A hPW0 hW0 hZ
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec v hvA (hvs ▸ indec_opow _))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      have h2 : f (ω ^ z') < f v := C.mono hPA hvA hPv
      rw [hc, he1] at h2
      have h3 : e1 < c := (opow_lt_opow_iff_right one_lt_omega0).1 h2
      have htq0 : val tq (f ρ) = 0 := lzv_zero hρE hρ1 tq Iq.2.1 (by rw [Iq.2.2.2.1, hq0]) (f ρ)
      rw [hc, ht, val_pw, val_sm, val_pw, htq0, opow_zero]
      exact opow_le_opow_right omega0_pos ((add_le_add (hzf e1 he1) le_rfl).trans (Order.add_one_le_of_lt h3))
    · -- one atom step
      have hNe : v = ω ^ (z' + ω ^ q) := by rw [hvs, hzs]
      obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ := lyStep2 h (hNe ▸ hρv) (pos_iff_ne_zero.2 hq0)
        (hNe ▸ hqv) (hNe ▸ hvδ) hw0 hPW0 hqW0
      refine ⟨W, Z, t, hw, hcbT, fun c hc => hZZ (hcsT c hc), htv, Finset.mem_union_left _ (hNe ▸ hNW),
        fun A f hW hZ C => ?_⟩
      obtain ⟨hqf, hzf⟩ := hcom A f (fun x hx => hW (hWW (Finset.mem_coe.1 hx)))
        (fun x hx => hZ (hZZ (Finset.mem_coe.1 hx))) C
      obtain ⟨a, ha, -, hnext⟩ := hI A f hW hZ C
      have hPA : ω ^ z' ∈ A := by
        rcases Finset.mem_union.1 hPW0 with h' | h'
        · exact hW (Finset.mem_coe.2 (hWW h'))
        · exact hZ (Finset.mem_coe.2 (hZZ h'))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      rw [hNe, ha, ht, val_pw, val_sm, val_pw]
      exact opow_le_opow_right omega0_pos
        ((add_le_add (hzf e1 he1) (opow_le_opow_right omega0_pos hqf)).trans (hnext e1 he1))
  · -- `v = v' + ω^{lg v}`, `v' ≠ 0`: a sum
    have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0' hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨W1, Z1, t1, I1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨W2, Z2, t2, I2⟩ := IH _ hwv (hwv.trans hv)
    have hw : WZ ρ δ (insert v (W1 ∪ W2)) (Z1 ∪ Z2) := by
      refine (I1.1.union I2.1).insW hρv.le hvδ (Or.inr ⟨v', ?_, ω ^ lg v, ?_, hv'v, hwv, hvs.symm⟩)
      · exact Finset.union_subset_union (Finset.subset_union_left) (Finset.subset_union_left) I1.2.2.2.2.1
      · exact Finset.union_subset_union (Finset.subset_union_right) (Finset.subset_union_right) I2.2.2.2.2.1
    refine ⟨_, _, sm t1 t2, hw, ⟨I1.2.1, I2.2.1⟩, fun c hc => ?_, by rw [val_sm, I1.2.2.2.1, I2.2.2.2.1, ← hvs],
      by simp, fun A f hW hZ C => ?_⟩
    · simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_union_left _ (I1.2.2.1 c hc)
      · exact Finset.mem_union_right _ (I2.2.2.1 c hc)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have h1A := (lzVImg_sub I1 hW1 hZ1).2
    have h2A := (lzVImg_sub I2 hW2 hZ2).2
    have hvA : v ∈ A := hW (by simp)
    rw [val_sm, ← C.add v' h1A _ h2A v hvA hvs.symm]
    exact add_le_add (I1.2.2.2.2.2 A f hW1 hZ1 C) (I2.2.2.2.2.2 A f hW2 hZ2 C)


end LzK

/-- **Lemma IMG for the terms of `LzV`** (the package). -/
theorem lzvPkg {l : Ordinal.{0}} (t : LzV) (hCB : CBt t (upsilon l)) (h1 : 1 ≤ val t (upsilon l))
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val t) := by
  classical
  have hρE := R.ρE
  have hρ1 := R.ρ1
  have htop := lzv_lt_top hρE hρ1 t hCB
  obtain ⟨W, Z, t', I⟩ := LzK.lzv_img R (val t (upsilon l)) htop
  have hwc : WZ (upsilon l) (upsilon (l + ω + 1)) ∅ (cs t).toFinset :=
    ⟨by simp, fun z hz => cbt_cst t _ hCB z (List.mem_toFinset.1 hz), by simp⟩
  have hw := I.1.union hwc
  rw [Finset.union_empty] at hw
  refine ⟨h1, htop.trans_le (lzB1_le_next hρE hρ1 R.ρδ R.next.2.1.2), W, Z ∪ (cs t).toFinset, hw, ?_,
    fun A f hW hZ C => ?_⟩
  · rcases Finset.mem_union.1 I.2.2.2.2.1 with h' | h'
    · exact Finset.mem_union_left _ h'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ h')
  have hZ1 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have htA : ∀ c ∈ cs t, c ∈ A := fun c hc => hZ (by simp [hc])
  have ht'A : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (I.2.2.1 c hc))
  have heq := LzK.lzv_val_fρ R C hCB I.2.1 htA ht'A I.2.2.2.1.symm
  rw [heq]
  exact I.2.2.2.2.2 A f hW hZ1 C

/-- **Lemma RS for the terms of `LzV`.** -/
theorem lzvRs {l : Ordinal.{0}} (t : LzV) (hCB : CBt t (upsilon l)) : RsStep l (val t) := by
  classical
  intro R htg
  have hρE := R.ρE
  have hρ1 := R.ρ1
  by_cases hρs : upsilon l ≤ val t (upsilon l)
  · have hnx := upsilon_isNext l
    have hCs : ∀ σ, (∀ c ∈ (cs t).toFinset, c < σ) → CBt t σ := fun σ hσ =>
      cbt_iff t _ σ hCB (fun c hc => hσ c (List.mem_toFinset.2 hc))
    refine rs_rstF (T := val t) (C := (cs t).toFinset) R
      (fun c hc => cbt_cst t _ hCB c (List.mem_toFinset.1 hc)) hρs ?_ ?_ ?_ htg
    · exact lzv_lt_ups hρE hρ1 hCB hnx.1 hnx.2.1
    · intro σ hσ hB hCσ _
      exact (lzv_pi hσ R.ρU hB t (hCs σ hCσ)).2
    · intro σ hσE hσρ _ hCσ
      exact lzv_lt_ups hσE (hσρ.trans hρ1) (hCs σ hCσ) hσρ R.ρU
  · have hC : LzVC t := by
      by_contra hn
      exact hρs (lzVC_ge hρE hρ1 t hCB hn)
    set c := val t (upsilon l) with hc
    have e : val t = OT.ev (OT.k c) := funext (fun y => by rw [OT.ev_k, hc, lzVC_const t hC y])
    have hcb : OT.CB (OT.k c) (upsilon l) := not_le.1 hρs
    rw [e] at htg
    have := rs_rstT R hcb htg
    rwa [OT.ev_k] at this

end Googology.Trans.PoR.InaccPsi.R2.Lz
