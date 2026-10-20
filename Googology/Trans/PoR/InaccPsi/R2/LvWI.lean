import Googology.Trans.PoR.InaccPsi.R2.LvWTh

/-!
# Lemma IMG for `LvWT`: the general core, the block witness, and the theta steps at the levels `ρ·(k+1) + b`

* `LvW.LvWImg` (the IMG statement for one value with a term of `LvWT`), `LvW.cbt_img`, `LvW.img_cst`, `LvW.img_bs`;
* `LvW.lh_any`, `LvW.gCore` (**the core at every level** `β ∈ Tʸ ∩ Ω₁`, `1 ≤ β`: an `ε`-number `a ∈ Tʸ ∩ (y, Ω₁)` below
  `ϑʸ(Ω₁·β + r')` with `β, r' < a`, `a ≤₁ g` and `luL(a, β) ≤ g` in `R₁⁺` is `ϑʸ(Ω₁·β + s)` for some `s < r'`, from
  the exact reaches and `Lu.lu_luL_lt`), `LvW.gCoreW` (at `β = y·(k+1) + b`);
* `LvWK.lvwWitL` (**the block witness**: `f(ρ, v, L) ≥ L(fρ, fv)` for `L = v·ρ + ρ + v·(ρ·k + b)`, from `luWitSq`,
  `luWitMul` and the chain `v·ρ + ρ + (v·ρ)·j`);
* `LvWK.lvwImg_sm`, `LvWK.lvwImg_E`, `LvWK.lvwFixTransfer`, `LvWK.lvwImg_th_fixed`, `_succ`, `_limit`, `LvWK.lvwImg_th`
  (the steps of `R2.LvI` at the levels `ρ·(k+1) + b`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

namespace LvW

/-- The IMG invariant for a represented value of `LvWT`. -/
def LvWImg (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : LvWT) : Prop :=
  WZ ρ δ W Z ∧ LvWT.CBt s ρ ∧ (∀ c ∈ LvWT.cs s, c ∈ Z) ∧ LvWT.val s ρ = v ∧
    v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}),
      ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f → LvWT.val s (f ρ) ≤ f v

/-- Rebase the term side condition along a covering copy. -/
theorem cbt_img {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : LvWT} (hs : LvWT.CBt s ρ) (hA : ∀ c ∈ LvWT.cs s, c ∈ A) :
    LvWT.CBt s (f ρ) :=
  LvWT.cbt_iff hs (fun c hc => C.above c (hA c hc) (LvWT.cbt_cst hs c hc))

/-- A constant below the restart has an IMG witness. -/
theorem img_cst {ρ δ a : Ordinal.{0}} (ha : a < ρ) :
    LvWImg ρ δ a ∅ {a} (.cst a) := by
  refine ⟨WZ.empty.insZ ha, ha, ?_, rfl, by simp, ?_⟩
  · intro c hc
    simp [LvWT.cs] at hc
    subst c
    simp
  · intro A f hW hZ C
    have haA : a ∈ A := hZ (by simp)
    rw [LvWT.val_cst, C.fix a haA ha]

/-- The current base has an IMG witness as the base term. -/
theorem img_bs {ρ δ : Ordinal.{0}} (hρE : InE ρ) (hρδ : ρ < δ) :
    LvWImg ρ δ ρ {ρ} ∅ .bs := by
  refine ⟨(WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl hρδ
      (Or.inl (inE_indec hρE)), trivial, ?_, rfl, by simp, ?_⟩
  · intro c hc
    simp [LvWT.cs] at hc
  · intro A f hW hZ C
    rfl

/-- The facts at a level `x·(k+1) + b` without the level bound. -/
theorem th_facts8 {x b η : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) (hb : b < x)
    (hη : η ∈ Tset x) (hη1 : η < Om1) :
    Om1 * lvwL x k b + η ∈ Tset x ∧ Om1 * lvwL x k b + η < OmTwo ∧
    vt x (Om1 * lvwL x k b + η) ∈ Tset x ∧ x < vt x (Om1 * lvwL x k b + η) ∧
    vt x (Om1 * lvwL x k b + η) < Om1 ∧ InE (vt x (Om1 * lvwL x k b + η)) ∧
    Indec (vt x (Om1 * lvwL x k b + η)) ∧ η < vt x (Om1 * lvwL x k b + η) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, h9⟩ := th_facts hx hx1 k hb hη hη1
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h9⟩

/-- The `R₁⁺`-reach of `ϑʸ(Ω₁·q + s)` at every level `q ∈ Tʸ ∩ Ω₁`, `1 ≤ q`, with `s` below it. -/
theorem lh_any {y q s : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (hq1 : 1 ≤ q) (hqT : q ∈ Tset y)
    (hqΩ : q < Om1) (hs : s ∈ Tset y) (hs1 : s < Om1) :
    IsLh1 (vt y (Om1 * q + s)) (Lu.luL (vt y (Om1 * q + s)) q + luZeta y q s) ∧
      s < vt y (Om1 * q + s) := by
  rcases lt_or_ge q y with hqy | hyq
  · exact ⟨Lu.lu_lh_th hy hy1 hq1 hqy hs hs1, (Lu.lu_th_facts hy hy1 hq1 hqy hs hs1).2.2.2.2.2.2.2⟩
  · exact ⟨Lv.lv_lh_gen hy hy1 hqT hyq hqΩ hs hs1, (Lv.gen_facts hy hy1 hqT hyq hqΩ hs hs1).2.2.2.2.2.2.2.2⟩

/-- **The core at every level** `β ∈ Tʸ ∩ Ω₁`, `1 ≤ β`. -/
theorem gCore {y a β r' g : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (hβ1 : 1 ≤ β) (hβT : β ∈ Tset y)
    (hβΩ : β < Om1) (hr'T : r' ∈ Tset y) (hr'1 : r' < Om1)
    (haT : a ∈ Tset y) (hya : y < a) (ha1 : a < Om1) (haE : InE a) (hβa : β < a)
    (hr'a : r' < a) (hg : le1R a g) (hLg : Lu.luL a β ≤ g) (hlt : a < vt y (Om1 * β + r')) :
    ∃ s, s ∈ Tset y ∧ s < Om1 ∧ s < r' ∧ vt y (Om1 * β + s) = a ∧ g ≤ Lu.luL a β + luZeta y β s := by
  obtain ⟨ξ, hξT, hξ2, hξa⟩ := vt_rep hy hy1 haT hya.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hy hy1 hξT hξ2).1 ⟨by rw [hξa]; exact hya, by rw [hξa]; exact haE⟩
  have hξlt : ξ < Om1 * β + r' :=
    ul_lt_of_vt_lt hy hy1 hβT hβΩ hξT hξ2 hr'T hr'1 (by rw [hξa]; exact hr'a) (by rw [hξa]; exact hβa)
      (by rw [hξa]; exact hlt)
  obtain ⟨hq1, hsT, hs1, hdec⟩ := Lu.lu_split hy hy1 hξT hξ2 hΩξ
  have hqβ : ξ / Om1 ≤ β := by
    have h1 : Om1 * (ξ / Om1) < Om1 * (β + 1) := by
      calc Om1 * (ξ / Om1) ≤ ξ := mul_div_le ξ Om1
        _ < Om1 * β + r' := hξlt
        _ < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hr'1
        _ = Om1 * (β + 1) := by rw [mul_add_one]
    exact Order.lt_add_one_iff.1 ((mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1)
  obtain ⟨hlh, hsa⟩ := lh_any hy hy1 hq1 (vz_T_down hy hy1 hβT hβΩ hqβ) (hqβ.trans_lt hβΩ) hsT hs1
  rw [hdec, hξa] at hlh hsa
  have hgle := hlh.2 g hg
  rcases hqβ.lt_or_eq with hqβ' | hqβ'
  · exfalso
    have h2 := Lu.lu_luL_lt (ζ := luZeta y (ξ / Om1) (ξ % Om1)) haE hq1 hqβ' hβa (Lu.lu_zeta_le.trans_lt hsa)
    exact absurd (hgle.trans_lt h2) (not_lt.2 hLg)
  · refine ⟨ξ % Om1, hsT, hs1, ?_, by rw [← hqβ', hdec, hξa], by rw [← hqβ']; exact hgle⟩
    have : Om1 * β + ξ % Om1 < Om1 * β + r' := by
      calc Om1 * β + ξ % Om1 = ξ := by rw [← hqβ', hdec]
        _ < Om1 * β + r' := hξlt
    exact (add_lt_add_iff_left _).1 this

/-- A level `x·(k+1) + b` is below every `ε`-number above `x`. -/
theorem lvwL_lt_E {x a : Ordinal.{0}} (hx : InE x) (k : ℕ) {b : Ordinal.{0}} (hb : b < x) (haE : InE a)
    (hxa : x < a) : lvwL x k b < a := by
  have e : x * ω = ω ^ (x + 1) := by rw [opow_add, opow_one, show ω ^ x = x from hx]
  have hw : x * ω < a := by rw [e]; exact haE.opow_lt ((inE_indec haE).add_lt hxa (Lu.lu_one_lt_E haE))
  refine lt_of_lt_of_le ?_ hw.le
  unfold lvwL
  calc x * ((k : Ordinal.{0}) + 1) + b < x * ((k : Ordinal.{0}) + 1) + x := (add_lt_add_iff_left _).2 hb
    _ = x * ((k : Ordinal.{0}) + 1 + 1) := (mul_add_one x _).symm
    _ < x * ω := (mul_lt_mul_iff_right₀ hx.pos).2 (by exact_mod_cast natCast_lt_omega0 (k + 1 + 1))

/-- **The core at the level `y·(k+1) + b`**. -/
theorem gCoreW {y a b r' g : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (k : ℕ) (hb : b < y)
    (hr'T : r' ∈ Tset y) (hr'1 : r' < Om1)
    (haT : a ∈ Tset y) (hya : y < a) (ha1 : a < Om1) (haE : InE a)
    (hr'a : r' < a) (hg : le1R a g) (hLg : L y k b a ≤ g)
    (hlt : a < vt y (Om1 * lvwL y k b + r')) :
    ∃ s, s ∈ Tset y ∧ s < Om1 ∧ s < r' ∧
      vt y (Om1 * lvwL y k b + s) = a ∧ g ≤ L y k b a + luZeta y (lvwL y k b) s := by
  obtain ⟨hLT, hyL, -, hL1⟩ := lvwL_facts hy hy1 (k := k) hb
  have h := gCore hy hy1 ((Lu.lu_one_lt_E hy).le.trans hyL) hLT hL1 hr'T hr'1 haT hya ha1 haE
    (lvwL_lt_E hy k hb haE hya) hr'a hg (by rw [luL_eq hy k hb]; exact hLg) hlt
  rwa [luL_eq hy k hb] at h

end LvW

namespace LvWK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- The chain `v·ρ + ρ + (v·ρ)·j` of witnesses. -/
theorem lvwWitChain {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ) : ∀ j : ℕ,
    ∃ W : Finset Ordinal.{0}, WZ ρ δ W ∅ ∧ ({ρ, v, v * ρ, v * ρ + ρ} : Finset Ordinal.{0}) ⊆ W ∧
      v * ρ + ρ + v * ρ * (j : Ordinal.{0}) ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ImgCtx ρ A f → InE (f v) →
        f v * f ρ + f ρ + f v * f ρ * (j : Ordinal.{0}) ≤ f (v * ρ + ρ + v * ρ * (j : Ordinal.{0})) := by
  classical
  obtain ⟨wzS, IS⟩ := Lu.LuK.luWitSq h hvE hρv hvδ
  have hP0 : 0 < v * ρ := mul_pos hvE.pos h.ρE.pos
  have hPδ : v * ρ < δ := h.δE.mul_lt hvδ h.ρδ
  have hUδ : v * ρ + ρ < δ := (inE_indec h.δE).add_lt hPδ h.ρδ
  have hρU : ρ ≤ v * ρ + ρ := le_add_self
  intro j
  induction j with
  | zero =>
    refine ⟨_, wzS, subset_refl _, by simp, ?_⟩
    intro A f hW C hfE
    have hPA : v * ρ ∈ A := hW (by simp)
    have hUA : v * ρ + ρ ∈ A := hW (by simp)
    have hfU : f (v * ρ) + f ρ = f (v * ρ + ρ) := C.add _ hPA _ C.rho _ hUA rfl
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [← hfU]
    exact add_le_add (IS A f hW C hfE) le_rfl
  | succ j ih =>
    obtain ⟨W, wz, hsub, hmem, hI⟩ := ih
    set Cj := v * ρ + ρ + v * ρ * (j : Ordinal.{0}) with hCj
    have hC1 : v * ρ + ρ + v * ρ * ((j + 1 : ℕ) : Ordinal.{0}) = Cj + v * ρ := by
      rw [Nat.cast_succ, mul_add_one, ← add_assoc]
    have hCδ : Cj + v * ρ < δ :=
      (inE_indec h.δE).add_lt ((inE_indec h.δE).add_lt hUδ (RstK.mul_nat_lt (inE_indec h.δE) hPδ j)) hPδ
    have hPm : v * ρ ∈ W ∪ ∅ := Finset.mem_union_left _ (hsub (by simp))
    have hCjP : Cj < Cj + v * ρ := lt_add_of_pos_right _ hP0
    have hPC : v * ρ < Cj + v * ρ :=
      ((lt_add_of_pos_right _ h.ρE.pos).trans_le le_self_add).trans hCjP
    have wz' := wz.insW (hρU.trans (le_self_add.trans hCjP.le)) hCδ
      (Or.inr ⟨Cj, Finset.mem_union_left _ hmem, v * ρ, hPm, hCjP, hPC, rfl⟩)
    refine ⟨insert (Cj + v * ρ) W, wz', hsub.trans (Finset.subset_insert _ _), by rw [hC1]; simp, ?_⟩
    intro A f hWA C hfE
    have hW0 : ↑W ⊆ A := fun x hx => hWA (by simp [Finset.mem_coe.1 hx])
    have hCjA : Cj ∈ A := hW0 (Finset.mem_coe.2 hmem)
    have hPA : v * ρ ∈ A := hW0 (Finset.mem_coe.2 (hsub (by simp)))
    have hSA : ↑({ρ, v, v * ρ, v * ρ + ρ} : Finset Ordinal.{0}) ⊆ A := fun x hx =>
      hW0 (Finset.mem_coe.2 (hsub (Finset.mem_coe.1 hx)))
    have hCA : Cj + v * ρ ∈ A := hWA (by simp)
    have hadd : f Cj + f (v * ρ) = f (Cj + v * ρ) := C.add _ hCjA _ hPA _ hCA rfl
    rw [hC1, ← hadd, Nat.cast_succ, mul_add_one, ← add_assoc]
    exact add_le_add (hI A f hW0 C hfE) (IS A f hSA C hfE)

/-- **The block witness** for `L = v·ρ + ρ + v·(ρ·k + b)`. -/
theorem lvwWitL {v b : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ) (k : ℕ) (hb : b < ρ) :
    ∃ W Z : Finset Ordinal.{0}, v ∈ W ∧ WZ ρ δ W Z ∧ LvW.L ρ k b v ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → InE (f v) → LvW.L (f ρ) k b (f v) ≤ f (LvW.L ρ k b v) := by
  classical
  obtain ⟨Wc, wzc, hsub, hmem, hIc⟩ := lvwWitChain h hvE hρv hvδ k
  have hvW : v ∈ Wc := hsub (by simp)
  have hLe : LvW.L ρ k b v = (v * ρ + ρ + v * ρ * (k : Ordinal.{0})) + v * b := by
    unfold LvW.L; rw [mul_add, mul_assoc, ← add_assoc]
  have hLf : ∀ y a : Ordinal.{0}, LvW.L y k b a = (a * y + y + a * y * (k : Ordinal.{0})) + a * b := by
    intro y a; unfold LvW.L; rw [mul_add, mul_assoc, ← add_assoc]
  rcases eq_or_ne b 0 with hb0 | hb0
  · refine ⟨Wc, ∅, hvW, wzc, by rw [hLe, hb0, mul_zero, add_zero]; exact hmem, ?_⟩
    intro A f hW _ C hfE
    rw [hLf, hLe, hb0, mul_zero, add_zero, mul_zero, add_zero]
    exact hIc A f hW C hfE
  obtain ⟨Wm, Zm, hVm, -, hWmB, hZmB, hclm, hIm⟩ := Lu.LuK.luWitMul h hvE hρv.le hvδ b hb
  have wzm : WZ ρ δ Wm Zm := ⟨hWmB, hZmB, hclm⟩
  set Ck := v * ρ + ρ + v * ρ * (k : Ordinal.{0}) with hCk
  have hvb0 : 0 < v * b := mul_pos hvE.pos (pos_iff_ne_zero.2 hb0)
  have hPδ : v * ρ < δ := h.δE.mul_lt hvδ h.ρδ
  have hUδ : v * ρ + ρ < δ := (inE_indec h.δE).add_lt hPδ h.ρδ
  have hCkδ : Ck < δ := (inE_indec h.δE).add_lt hUδ (RstK.mul_nat_lt (inE_indec h.δE) hPδ k)
  have hvbδ : v * b < δ := (mul_lt_mul_of_pos_left hb hvE.pos).trans hPδ
  have hLδ : Ck + v * b < δ := (inE_indec h.δE).add_lt hCkδ hvbδ
  have hCkL : Ck < Ck + v * b := lt_add_of_pos_right _ hvb0
  have hvbCk : v * b < Ck :=
    ((mul_lt_mul_of_pos_left hb hvE.pos).trans_le le_self_add).trans_le le_self_add
  have hρCk : ρ ≤ Ck := le_add_self.trans le_self_add
  have wz0 := ((wzc.union wzm).insZ hb)
  have wz := wz0.insW (hρCk.trans hCkL.le) hLδ
    (Or.inr ⟨Ck, by simp [hmem], v * b, by simp [hVm hb0], hCkL, hvbCk.trans hCkL, rfl⟩)
  refine ⟨insert (Ck + v * b) (Wc ∪ Wm), insert b (∅ ∪ Zm), by simp [hvW], wz, by rw [hLe]; simp, ?_⟩
  intro A f hW hZ C hfE
  have hWc : ↑Wc ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hWm : ↑Wm ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZm : ↑Zm ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hbA : b ∈ A := hZ (by simp)
  have hvA : v ∈ A := hWc (Finset.mem_coe.2 hvW)
  have hCkA : Ck ∈ A := hWc (Finset.mem_coe.2 hmem)
  have hvbA : v * b ∈ A := hWm (Finset.mem_coe.2 (hVm hb0))
  have hLA : Ck + v * b ∈ A := hW (by simp)
  have hbfv : b < f v := (C.above b hbA hb).trans (C.mono C.rho hvA hρv)
  have hadd : f Ck + f (v * b) = f (Ck + v * b) := C.add _ hCkA _ hvbA _ hLA rfl
  rw [hLf, hLe, ← hadd]
  exact add_le_add (hIc A f hWc C hfE) (hIm A f hWm hZm C hfE hbfv)

/-- IMG is closed under ordinal addition when the two summands already have witnesses. -/
theorem lvwImg_sm {u1 u2 v : Ordinal.{0}} (hρv : ρ ≤ v) (hvδ : v < δ)
    (hu1 : u1 < v) (hu2 : u2 < v) {W1 Z1 W2 Z2 : Finset Ordinal.{0}}
    {s1 s2 : LvWT} (h1 : LvW.LvWImg ρ δ u1 W1 Z1 s1) (h2 : LvW.LvWImg ρ δ u2 W2 Z2 s2)
    (hsum : u1 + u2 = v) :
    ∃ W Z s, LvW.LvWImg ρ δ v W Z s := by
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
    simp only [LvWT.cs, List.mem_append] at hc
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
    rw [LvWT.val_sm, ← hadd]
    exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- An epsilon value can be represented by an exponential term with the IMG epsilon base. -/
theorem lvwImg_E {v : Ordinal.{0}} (hρv : ρ ≤ v) (hvE : InE v) (hvδ : v < δ)
    {W Z : Finset Ordinal.{0}} {s : LvWT} (hI : LvW.LvWImg ρ δ v W Z s) :
    ∃ W' Z' se s', LvW.LvWImg ρ δ v W' Z' (.pw (.sm se s')) ∧
      InE (LvWT.val se ρ) ∧ LvWT.val se ρ + LvWT.val s' ρ < eN (LvWT.val se ρ) := by
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
    by rw [e, LvWT.val_cst, add_zero]; exact lt_eN v⟩
  · intro c hc
    simp only [LvWT.cs, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact Finset.mem_insert_of_mem (hcs c hc)
    · exact Finset.mem_insert_self _ _
  · rw [LvWT.val_pw, LvWT.val_sm, LvWT.val_cst, add_zero, e]
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
    rw [LvWT.val_pw, LvWT.val_sm, LvWT.val_cst, add_zero]
    have hh := (opow_le_opow_iff_right one_lt_omega0).2 hbv
    rwa [show ω ^ f v = f v from hfE] at hh

/-- Fixed-point transfer for a theta level that follows the changing base. -/
theorem lvwFixTransfer {σ γ b : Ordinal.{0}} (k : ℕ) (hB : Bases σ ρ) (hb : b < σ)
    (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1)
    (hfix : ∀ s, s < γ → vt ρ (Om1 * lvwL ρ k b + s) ≤ γ) :
    ∀ s, s < pi σ ρ γ → vt σ (Om1 * lvwL σ k b + s) ≤ pi σ ρ γ := by
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
  obtain ⟨hvTB, hpv⟩ := LvWT.pi_vt_lvw hB k hb hs'TB hs'1
  have hh := ((pi_bijOn hB).2.le_iff_le hvTB hγ).2 (hfix s' hs'γ)
  rwa [hpv, hs'e] at hh

/-- The fixed-point remainder case for a base-dependent theta term. -/
theorem lvwImg_th_fixed (k : ℕ) {b r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hζ : luZeta ρ (lvwL ρ k b) r = 0)
    (hfix : ∀ s, s < r → vt ρ (Om1 * lvwL ρ k b + s) ≤ r)
    (hve : vt ρ (Om1 * lvwL ρ k b + r) = v) (hvB : v < lvwTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvW.LvWImg ρ δ u W Z s) :
    ∃ W Z s, LvW.LvWImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, hvT, hρv, -, hvE, -, hrTheta⟩ :=
    LvW.th_facts8 hρE hρ1 k hb hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hvT hρv hvE
  have hvδ : v < δ := hvB.trans (LvWT.lvw_top_lt_next (x := ρ) hρE hρ1 h.ρδ h.next.2.1.2)
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  let L := LvW.L ρ k b v
  obtain ⟨WL, ZL, -, wzL, hLW, IL⟩ := lvwWitL h hvE hρv hvδ k hb
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (lvwL ρ k b) r) := by
    have hh := (LvW.lh_th hρE hρ1 k hb hrT hr1).1
    simpa [L, hve] using hh
  have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by simpa [hζ] using hsrcR)
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz := ((w1.union wzL).union wzE).insZ hb
  let W : Finset Ordinal := (W1 ∪ WL) ∪ {v, v + v}
  let Z : Finset Ordinal := insert b (Z1 ∪ ZL)
  have hwz' : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz
  refine ⟨W, Z, .th k b s1, hwz', ⟨hb, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvWT.cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
  · rw [LvWT.val_th, e1, hve]
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
    have hbA : b ∈ A := hZ (by simp [Z])
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hby : b < f ρ := C.above b hbA hb
    have hcb1y := LvW.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvWT.val_th]
    by_cases hU : UpsPt (f v)
    · exact (LvWT.lvw_lt_ups hyE hy1 (t := .th k b s1) ⟨hby, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL' hZL C hfE
    obtain ⟨hs1T, hs1top⟩ := LvWT.lvw_T hyE hy1 s1 hcb1y
    have hs11 : LvWT.val s1 (f ρ) < Om1 := hs1top.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨hθT, hθtop⟩ := LvWT.lvw_T hyE hy1 (.th k b s1) ⟨hby, hcb1y⟩
    have hθ1 : LvWT.val (.th k b s1) (f ρ) < Om1 := hθtop.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT hθ1 hlt.le
    obtain ⟨s, -, -, hsr, hsa, -⟩   :=
      LvW.gCoreW hyE hy1 k hby hs1T hs11 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hfL hlt
    have hpi := LvWT.pi C.ups h.ρU hB s1 hcb1y
    have htr := lvwFixTransfer (ρ := ρ) (τ := τ) (δ := δ) h
      (σ := f ρ) (γ := LvWT.val s1 ρ) (b := b) k hB hby hpi.1 (by rw [e1]; exact hr1)
      (by intro q hq; have hqr : q < r := by simpa [e1] using hq
          calc
            vt ρ (Om1 * lvwL ρ k b + q) ≤ r := hfix q hqr
            _ = LvWT.val s1 ρ := e1.symm) s
      (by rw [hpi.2]; exact hsr)
    rw [hpi.2, hsa] at htr
    exact (not_lt_of_ge htr) (hb1.trans_lt hfrv)

/-- The successor remainder case for a base-dependent theta term. -/
theorem lvwImg_th_succ (k : ℕ) {b r0 r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hr0T : r0 ∈ Tset ρ) (hr01 : r0 < Om1)
    (hrs : r = r0 + 1) (hζ : luZeta ρ (lvwL ρ k b) r = 0)
    (hve : vt ρ (Om1 * lvwL ρ k b + r) = v) (hvB : v < lvwTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvW.LvWImg ρ δ u W Z s) :
    ∃ W Z s, LvW.LvWImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, hvT, hρv, hv1, hvE, hvI, hrTheta⟩ :=
    LvW.th_facts8 hρE hρ1 k hb hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hvT hρv hv1 hvE hvI
  have hvδ : v < δ := hvB.trans (LvWT.lvw_top_lt_next (x := ρ) hρE hρ1 h.ρδ h.next.2.1.2)
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  have hr0r : r0 < r := by rw [hrs]; exact lt_add_of_pos_right _ zero_lt_one
  let v0 := vt ρ (Om1 * lvwL ρ k b + r0)
  have hv0v : v0 < v := by
    rw [← hve]
    exact LvW.th_lt hρE hρ1 k hb hr0T hrT hr1 hr0r
  obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
  obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
  let L := LvW.L ρ k b v
  obtain ⟨WL, ZL, -, wzL, hLW, IL⟩ :=
    lvwWitL (ρ := ρ) (τ := τ) (δ := δ) h hvE hρv hvδ k hb
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (lvwL ρ k b) r) := by
    have hh := (LvW.lh_th hρE hρ1 k hb hrT hr1).1
    simpa [L, hve] using hh
  have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by simpa [hζ] using hsrcR)
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz0 := ((((w1.union w2).union w3).union wzL).union wzE).insZ hb
  let W : Finset Ordinal := (((W1 ∪ W2) ∪ W3) ∪ WL) ∪ {v, v + v}
  let Z : Finset Ordinal := insert b (Z1 ∪ Z2 ∪ Z3 ∪ ZL)
  have hwz : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz0
  refine ⟨W, Z, .th k b s1, hwz, ⟨hb, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvWT.cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (cs1 c hc))))
  · rw [LvWT.val_th, e1, hve]
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
    have hbA : b ∈ A := hZ (by simp [Z])
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hv0A : v0 ∈ A := mem_A m2 hW2 hZ2
    have hby : b < f ρ := C.above b hbA hb
    have hcb1y := LvW.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hcb2y := LvW.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
    have hcb3y := LvW.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvWT.val_th]
    by_cases hU : UpsPt (f v)
    · exact (LvWT.lvw_lt_ups hyE hy1 (t := .th k b s1) ⟨hby, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL' hZL C hfE
    have hLg : LvW.L (f ρ) k b (f v) ≤ f L := by simpa [LvW.L] using hfL
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    obtain ⟨hs1T, hs1top⟩ := LvWT.lvw_T hyE hy1 s1 hcb1y
    have hs11 : LvWT.val s1 (f ρ) < Om1 := hs1top.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    have hθT := LvWT.lvw_T hyE hy1 (.th k b s1) ⟨hby, hcb1y⟩
    have hθ1 : LvWT.val (.th k b s1) (f ρ) < Om1 := hθT.2.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT.1 hθ1 hlt.le
    obtain ⟨s, hsT, hs1, hsr, hsa, -⟩   :=
      LvW.gCoreW hyE hy1 k hby hs1T hs11 hfvT hyv hfv1 hfE
        (hb1.trans_lt hfrv) hR hLg hlt
    have hsrcopy : LvWT.val s1 (f ρ) = LvWT.val s3 (f ρ) + 1 := by
      have hc : LvWT.CBt (.sm s3 (.cst 1)) (f ρ) := ⟨hcb3y, one_lt_of_upsPt C.ups⟩
      have hh := (LvWT.uni_eq C.ups h.ρU hB hcb1y hc).1
        (by rw [LvWT.val_sm, LvWT.val_cst, e1, e3, hrs])
      simpa [LvWT.val_sm, LvWT.val_cst] using hh
    have hsle : s ≤ LvWT.val s3 (f ρ) := Order.lt_add_one_iff.1 (by rw [hsrcopy] at hsr; exact hsr)
    have hprev : LvWT.val (.th k b s3) (f ρ) ≤ f v0 := by
      have hh := (LvWT.uni_eq C.ups h.ρU hB (show LvWT.CBt (.th k b s3) (f ρ) from ⟨hby, hcb3y⟩) hcb2y).1
        (by simp [LvWT.val_th, e3, e2, v0])
      change vt (f ρ) (Om1 * lvwL (f ρ) k b + LvWT.val s3 (f ρ)) ≤ f v0
      rw [← LvWT.val_th, hh]
      exact hb2
    obtain ⟨hs3T, hs3top⟩ := LvWT.lvw_T hyE hy1 s3 hcb3y
    have hs31 : LvWT.val s3 (f ρ) < Om1 := hs3top.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨-, -, -, -, -, -, -, hηθ⟩ := LvW.th_facts8 hyE hy1 k hby hs3T hs31
    have hmon := LvW.th_le hyE hy1 k hby hsT hs3T hs31 hsle
    have hltContr : f v ≤ f v0 := by rw [hsa] at hmon; exact hmon.trans hprev
    exact (not_lt_of_ge hltContr) hfv0v

/-- The nonzero limit-remainder case for a base-dependent theta term. -/
theorem lvwImg_th_limit (k : ℕ) {b r0 z r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hr0T : r0 ∈ Tset ρ)
    (hrs : r = r0 + ω ^ z) (hz : lg r = z) (hz0 : z ≠ 0)
    (hζ : luZeta ρ (lvwL ρ k b) r = lg r)
    (hve : vt ρ (Om1 * lvwL ρ k b + r) = v) (hvB : v < lvwTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvW.LvWImg ρ δ u W Z s) :
    ∃ W Z s, LvW.LvWImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, -, hρv, -, hvE, -, hrTheta⟩ :=
    LvW.th_facts8 hρE hρ1 k hb hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hρv hvE
  have hvδ : v < δ := hvB.trans (LvWT.lvw_top_lt_next (x := ρ) hρE hρ1 h.ρδ h.next.2.1.2)
  have hrpos : 0 < r := by
    rw [hrs]
    exact lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (opow_pos z omega0_pos))
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hzle : z ≤ r := by simpa [hz] using (lg_le hrne)
  have hzv : z < v := hzle.trans_lt hrv
  have hr0r : r0 < r := by rw [hrs]; exact lt_add_of_pos_right _ (opow_pos z omega0_pos)
  let v0 := vt ρ (Om1 * lvwL ρ k b + r0)
  have hv0v : v0 < v := by
    rw [← hve]
    exact LvW.th_lt hρE hρ1 k hb hr0T hrT hr1 hr0r
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
  obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
  obtain ⟨W4, Z4, sz, w4, cb4, cs4, e4, m4, b4⟩ := I1 z hzv
  let L := LvW.L ρ k b v
  obtain ⟨WL, ZL, -, wzL, hLW, IL⟩ := lvwWitL h hvE hρv hvδ k hb
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (lvwL ρ k b) r) := by
    have hh := (LvW.lh_th hρE hρ1 k hb hrT hr1).1
    simpa [L, hve] using hh
  have hLzδ : L + z < δ := (inE_indec h.δE).add_lt hLδ (hzv.trans hvδ)
  have hsrc : le1 v (L + z) := by
    apply (h.lowδ _ _ hρv hLzδ.le).2
    simpa [hζ, hz] using hsrcR
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz0 := (((((w1.union w2).union w3).union w4).union wzL).union wzE).insZ hb
  have hW0 : WZ ρ δ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v})
      (insert b (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅)) := by
    simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz0
  have hzm : z ∈ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v}) ∪
      insert b (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅) := by
    rcases Finset.mem_union.1 m4 with hm | hm
    · exact Finset.mem_union_left _ (by simp [hm])
    · exact Finset.mem_union_right _ (by simp [hm])
  have hvL : v ≤ L := by
    dsimp [L, LvW.L]
    exact (le_mul_left v hρE.pos).trans (le_self_add.trans le_self_add)
  have hLm : L ∈ (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v}) ∪
      insert b (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL ∪ ∅) := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ hLW))
  have hwz := hW0.insW (hρv.le.trans (hvL.trans le_self_add)) hLzδ
    (Or.inr ⟨L, hLm, z, hzm,
      lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
      (lt_of_lt_of_le hzv hvL).trans_le le_self_add, rfl⟩)
  let W : Finset Ordinal := insert (L + z) (W1 ∪ W2 ∪ W3 ∪ W4 ∪ WL ∪ {v, v + v})
  let Z : Finset Ordinal := insert b (Z1 ∪ Z2 ∪ Z3 ∪ Z4 ∪ ZL)
  have hwz' : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz
  refine ⟨W, Z, .th k b s1, hwz', ⟨hb, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvWT.cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
  · rw [LvWT.val_th, e1, hve]
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
    have hbA : b ∈ A := hZ (by simp [Z])
    have hrA : r ∈ A := mem_A m1 hW1 hZ1
    have hv0A : v0 ∈ A := mem_A m2 hW2 hZ2
    have hzA : z ∈ A := mem_A m4 hW4 hZ4
    have hby : b < f ρ := C.above b hbA hb
    have hcb1y := LvW.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hcb2y := LvW.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
    have hcb3y := LvW.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    have hcb4y := LvW.cbt_img C cb4 (fun c hc => hZ4 (Finset.mem_coe.2 (cs4 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hb4 := b4 A f hW4 hZ4 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvWT.val_th]
    by_cases hU : UpsPt (f v)
    · exact (LvWT.lvw_lt_ups hyE hy1 (t := .th k b s1) ⟨hby, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hfLz : f (L + z) = f L + f z := (C.add L hLA z hzA _ hLzA rfl).symm
    have hR : le1R (f v) (f L + f z) := by
      have hh := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA _ hLzA hsrc)
      rwa [hfLz] at hh
    have hfL := IL A f hWL' hZL C hfE
    have hLf : LvW.L (f ρ) k b (f v) ≤ f L := by simpa [L] using hfL
    have hLg : LvW.L (f ρ) k b (f v) ≤ f L + f z := hLf.trans le_self_add
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    have hsrcopy : LvWT.val s1 (f ρ) = LvWT.val s3 (f ρ) + ω ^ LvWT.val sz (f ρ) := by
      have hc : LvWT.CBt (.sm s3 (.pw sz)) (f ρ) := ⟨hcb3y, hcb4y⟩
      have hh := (LvWT.uni_eq C.ups h.ρU hB hcb1y hc).1
        (by rw [LvWT.val_sm, LvWT.val_pw, e1, e3, e4, hrs])
      simpa [LvWT.val_sm, LvWT.val_pw] using hh
    have hprev : LvWT.val (.th k b s3) (f ρ) ≤ f v0 := by
      have hh := (LvWT.uni_eq C.ups h.ρU hB
        (show LvWT.CBt (.th k b s3) (f ρ) from ⟨hby, hcb3y⟩) hcb2y).1
        (by simp [LvWT.val_th, e3, e2, v0])
      have hh' : vt (f ρ) (Om1 * lvwL (f ρ) k b + LvWT.val s3 (f ρ)) = s2.val (f ρ) := by
        simpa [LvWT.val_th] using hh
      change vt (f ρ) (Om1 * lvwL (f ρ) k b + LvWT.val s3 (f ρ)) ≤ f v0
      rw [hh']
      exact hb2
    obtain ⟨hs1T, hs1top⟩ := LvWT.lvw_T hyE hy1 s1 hcb1y
    have hs11 : LvWT.val s1 (f ρ) < Om1 := hs1top.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨hs3T, hs3top⟩ := LvWT.lvw_T hyE hy1 s3 hcb3y
    have hs31 : LvWT.val s3 (f ρ) < Om1 := hs3top.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨hθT, hθtop⟩ := LvWT.lvw_T hyE hy1 (.th k b s1) ⟨hby, hcb1y⟩
    have hθ1 : LvWT.val (.th k b s1) (f ρ) < Om1 := hθtop.trans (lvwTop_facts hyE hy1).2.2.2.2.1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT hθ1 hlt.le
    obtain ⟨s, hsT, -, hsr, hsa, hgs⟩   :=
      LvW.gCoreW hyE hy1 k hby hs1T hs11 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hLg hlt
    rw [hsrcopy] at hsr
    rcases le_or_gt s (LvWT.val s3 (f ρ)) with hsle | hslt
    · obtain ⟨-, -, -, -, -, -, -, hηθ⟩ := LvW.th_facts8 hyE hy1 k hby hs3T hs31
      have hm := LvW.th_le hyE hy1 k hby hsT hs3T hs31 hsle
      rw [hsa] at hm
      exact (not_lt_of_ge (hm.trans hprev)) hfv0v
    · let d := s - LvWT.val s3 (f ρ)
      have hde : LvWT.val s3 (f ρ) + d = s := Ordinal.add_sub_cancel_of_le hslt.le
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0, add_zero] at hde
        exact absurd hde (ne_of_lt hslt)
      have hdz : d < ω ^ LvWT.val sz (f ρ) :=
        (add_lt_add_iff_left _).1 (by rw [hde]; exact hsr)
      have hlgd : lg d < LvWT.val sz (f ρ) :=
        (opow_lt_opow_iff_right one_lt_omega0).1
          (lt_of_le_of_lt (le_of_dvd hd0 (lg_dvd hd0)) hdz)
      have hlgadd : lg s = lg d := by rw [← hde]; exact Lu.lu_lg_add_right hd0
      have hζs : luZeta (f ρ) (lvwL (f ρ) k b) s ≤ lg s := Lu.lu_zeta_le_lg
      have h1 : LvW.L (f ρ) k b (f v) + luZeta (f ρ) (lvwL (f ρ) k b) s <
          LvW.L (f ρ) k b (f v) + f z := by
        apply (add_lt_add_iff_left _).2
        exact lt_of_le_of_lt hζs (by rw [hlgadd]; exact hlgd.trans_le hb4)
      have hLf : LvW.L (f ρ) k b (f v) ≤ f L := by simpa [LvW.L] using hfL
      have h2 : LvW.L (f ρ) k b (f v) + f z ≤ f L + f z := add_le_add hLf le_rfl
      exact absurd (hgs.trans_lt (h1.trans_le h2)) (lt_irrefl _)

/-- The full remainder induction step for a base-dependent theta term. -/
theorem lvwImg_th (k : ℕ) {b r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1)
    (hve : vt ρ (Om1 * lvwL ρ k b + r) = v) (hvB : v < lvwTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, LvW.LvWImg ρ δ u W Z s) :
    ∃ W Z s, LvW.LvWImg ρ δ v W Z s := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hrv⟩ :=
    LvW.th_facts8 (upsPt_inE h.ρU) h.ρ1 k hb hrT hr1
  rw [hve] at hrv
  by_cases hl : ∃ σ, σ < r ∧ r < vt ρ (Om1 * lvwL ρ k b + σ)
  · have hr0 : r ≠ 0 := by
      obtain ⟨σ, hσ, -⟩ := hl
      exact (lt_of_le_of_lt zero_le hσ).ne'
    have hζ : luZeta ρ (lvwL ρ k b) r = lg r := Lu.lu_zeta_lim hl
    obtain ⟨r0, hrs, -, hr0r⟩ := lg_split hr0
    let z := lg r
    have hzv : z < v := (lg_le hr0).trans_lt hrv
    have hr0T : r0 ∈ Tset ρ := vz_T_down (upsPt_inE h.ρU) h.ρ1 hrT hr1 hr0r.le
    have hr01 : r0 < Om1 := hr0r.trans hr1
    by_cases hz0 : z = 0
    · have hrs' : r = r0 + 1 := by simpa [z, hz0, opow_zero] using hrs
      have hζ0 : luZeta ρ (lvwL ρ k b) r = 0 := by simpa [z, hz0] using hζ
      exact lvwImg_th_succ h k hb hrT hr1 hr0T hr01 hrs' hζ0 hve hvB I1
    · exact lvwImg_th_limit h k hb hrT hr1 hr0T hrs (by rfl) hz0 hζ hve hvB I1
  · have hfix : ∀ σ, σ < r → vt ρ (Om1 * lvwL ρ k b + σ) ≤ r := by
      intro σ hσ
      by_contra hnot
      exact hl ⟨σ, hσ, lt_of_not_ge hnot⟩
    have hζ : luZeta ρ (lvwL ρ k b) r = 0 := Lu.lu_zeta_fix hfix
    exact lvwImg_th_fixed h k hb hrT hr1 hζ hfix hve hvB I1


end LvWK

end Googology.Trans.PoR.InaccPsi.R2
