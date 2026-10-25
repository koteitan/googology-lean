import Googology.Trans.PoR.InaccPsi.R2.HaFr

/-!
# HaImg: LEMMA IMG BY THE REACH TEST GOING DOWN, AT EVERY FINITE VEBLEN LEVEL; LEMMA IMG AT `B₃(ρ)`

`Gz.gzI_limZ` proves Lemma IMG at a limit `ε`-fixed point by copying the source `E ≤₁ E·3 + z` and showing that no
`ε`-number `u` between the last checked point `E'` and `E` can have a reach `lh(u) ≥ u·3 + z`.  Here the argument is
stated once for every finite Veblen level `n ≥ 1` (`ha_img_down`): for `E = ϑᵖ(Ω₁·n + t)` (the `t`-th point of exact
Veblen level `n`, reach `E·(n+1) + z`, `z = glZeta ρ n t`, `Gl.gl_lh_th`), Lemma IMG holds at `E` once it holds below
`E` and every `ε`-number `u ∈ (E', E)` has a reach `u·(m+1) + ζ`, `ζ < u`, with `m < n`, or `m = n` and `ζ < z`
(**the reach test going down**).  As the first new case: **Lemma IMG at `B₃(ρ) = φ(3, Γ_{ρ+1}+1)` itself**
(`ha_img_B3`): `B₃(ρ) = ϑᵖ(Ω₁·3 + Γ_{ρ+1})` (`ha_B3_eq`), and every `ε`-number in `(ζ_{Γ_{ρ+1}+1}, B₃(ρ))` has
Veblen level `1` (reach `u·2 + lg d`) or `2` (reach `u·3 + ζ`), `Gz.gz_floor`, `Gk.gk_lh_evA`, `Gz.gz_glA2V`.  So Lemma
IMG holds for every value up to and including `B₃(ρ)` (`ha_img_le_B3`).

* `ha_nat_T`, `ha_mul_lt`, `ha_wz_muls`, `ha_img_muls`, `ha_pi_muls` (the products `E·(k+1)` in the witness sets, in
  the copy and under `π`), `ha_img_down` (**LEMMA IMG BY THE REACH TEST GOING DOWN, GENERIC IN THE LEVEL `n`**);
* `ha_B3_eq` (**`B₃(x) = ϑˣ(Ω₁·3 + Γ_{x+1})`**), `ha_B3_lh`, `ha_img_B3` (**LEMMA IMG AT `B₃(ρ)`**), `ha_img_le_B3`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Products `E·(k+1)` -/

theorem ha_mul_succ (E : Ordinal.{0}) (k : ℕ) :
    E * (((k + 1 : ℕ) : Ordinal.{0}) + 1) = E * ((k : Ordinal.{0}) + 1) + E := by
  push_cast; rw [mul_add_one (a := E) (b := (k : Ordinal.{0}) + 1)]

/-- `E·(k+1) < D` for an indecomposable `D > E`. -/
theorem ha_mul_lt {E D : Ordinal.{0}} (hD : Indec D) (hED : E < D) : ∀ k : ℕ, E * ((k : Ordinal.{0}) + 1) < D
  | 0 => by simpa using hED
  | k + 1 => by rw [ha_mul_succ]; exact hD.add_lt (ha_mul_lt hD hED k) hED

theorem ha_mul_mono {E : Ordinal.{0}} (hE : 0 < E) (k : ℕ) :
    E * ((k : Ordinal.{0}) + 1) < E * (((k + 1 : ℕ) : Ordinal.{0}) + 1) := by
  rw [ha_mul_succ]; exact lt_add_of_pos_right _ hE

theorem ha_mul_le_mul {E : Ordinal.{0}} {j k : ℕ} (hjk : j ≤ k) :
    E * ((j : Ordinal.{0}) + 1) ≤ E * ((k : Ordinal.{0}) + 1) :=
  mul_le_mul_left' (add_le_add (Nat.cast_le.2 hjk) le_rfl) E

/-- **The products `E·(j+1)`, `j ≤ k`, added to witness sets.** -/
theorem ha_wz_muls {ρ δ E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W) (hρE : ρ ≤ E)
    (hE0 : 0 < E) (hδ : ∀ k : ℕ, E * ((k : Ordinal.{0}) + 1) < δ) :
    ∀ k : ℕ, ∃ W' : Finset Ordinal.{0}, WZ ρ δ W' Z ∧ W ⊆ W' ∧ ∀ j : ℕ, j ≤ k → E * ((j : Ordinal.{0}) + 1) ∈ W'
  | 0 => ⟨W, w, subset_refl _, fun j hj => by
      rw [Nat.le_zero.1 hj]; simpa using hEW⟩
  | k + 1 => by
    classical
    obtain ⟨W', w', hWW', hW'⟩ := ha_wz_muls w hEW hρE hE0 hδ k
    have hkW : E * ((k : Ordinal.{0}) + 1) ∈ W' := hW' k le_rfl
    have hEW' : E ∈ W' := hWW' hEW
    have hlt := ha_mul_mono hE0 k
    refine ⟨insert (E * (((k + 1 : ℕ) : Ordinal.{0}) + 1)) W', w'.insW ?_ (hδ (k + 1)) ?_,
      fun x hx => Finset.mem_insert_of_mem (hWW' hx), fun j hj => ?_⟩
    · exact hρE.trans (by simpa using ha_mul_le_mul (E := E) (Nat.zero_le (k + 1)))
    · refine Or.inr ⟨E * ((k : Ordinal.{0}) + 1), Finset.mem_union_left _ hkW, E, Finset.mem_union_left _ hEW',
        hlt, ?_, (ha_mul_succ E k).symm⟩
      exact lt_of_le_of_lt (by simpa using ha_mul_le_mul (E := E) (Nat.zero_le k)) hlt
    · rcases Nat.lt_or_ge j (k + 1) with hj' | hj'
      · exact Finset.mem_insert_of_mem (hW' j (Nat.lt_succ_iff.1 hj'))
      · rw [le_antisymm hj hj']; exact Finset.mem_insert_self _ _

/-- **The copy of `E·(k+1)`**: `f(E·(k+1)) = f(E)·(k+1)` when the products up to `k` lie in the domain. -/
theorem ha_img_muls {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {E : Ordinal.{0}} (m : ℕ) (hA : ∀ k : ℕ, k ≤ m → E * ((k : Ordinal.{0}) + 1) ∈ A) :
    ∀ k : ℕ, k ≤ m → f (E * ((k : Ordinal.{0}) + 1)) = f E * ((k : Ordinal.{0}) + 1)
  | 0, _ => by simp
  | k + 1, hk => by
    have hEA : E ∈ A := by have := hA 0 (Nat.zero_le m); simpa using this
    have h1 := C.add _ (hA k (Nat.le_of_succ_le hk)) _ hEA _ (hA (k + 1) hk) (ha_mul_succ E k).symm
    rw [← h1, ha_img_muls C m hA k (Nat.le_of_succ_le hk), ha_mul_succ]

/-- **`π(u·(k+1)) = π(u)·(k+1)`.** -/
theorem ha_pi_muls {σ ρ u : Ordinal.{0}} (hB : Bases σ ρ) (hu : u ∈ TB ρ σ) (hu1 : u < Om1) :
    ∀ k : ℕ, u * ((k : Ordinal.{0}) + 1) ∈ TB ρ σ ∧
      pi σ ρ (u * ((k : Ordinal.{0}) + 1)) = pi σ ρ u * ((k : Ordinal.{0}) + 1)
  | 0 => by rw [Nat.cast_zero, zero_add, mul_one, mul_one]; exact ⟨hu, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := ha_pi_muls hB hu hu1 k
    obtain ⟨s1, s2⟩ := pi_add hB h1 hu
    rw [ha_mul_succ, ha_mul_succ]
    exact ⟨s1, by rw [s2, h2]⟩

theorem ha_nat_T {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (n : ℕ) :
    (n : Ordinal.{0}) ∈ Tset x ∧ (n : Ordinal.{0}) < Om1 :=
  ⟨mem_T_of_le hx hx1 ((natCast_lt_omega0 n).trans (omega0_lt_inE hx)).le,
    ((natCast_lt_omega0 n).trans (omega0_lt_inE hx)).trans hx1⟩

/-! ## Lemma IMG by the reach test going down -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BY THE REACH TEST GOING DOWN, AT EVERY FINITE VEBLEN LEVEL `n ≥ 1`**: let `E = ϑᵖ(Ω₁·n + t)` (reach
`E·(n+1) + z`, `z = glZeta ρ n t`), `ρ < E' < E`.  If Lemma IMG holds below `E` and every `ε`-number `u ∈ (E', E)`
has a reach `u·(m+1) + ζ` with `ζ < u` and either `m < n` or (`m = n` and `ζ < z`), then Lemma IMG holds at `E`. -/
theorem ha_img_down {n : ℕ} (hn : 1 ≤ n) {t E' : Ordinal.{0}} (htT : t ∈ Tset ρ) (ht1 : t < Om1)
    (hρE' : ρ < E') (hE'E : E' < glA (n : Ordinal.{0}) t ρ)
    (hdown : ∀ u, InE u → E' < u → u < glA (n : Ordinal.{0}) t ρ → ∃ m : ℕ, ∃ ζ, m ≤ n ∧
      IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u ∧ (m = n → ζ < glZeta ρ n t))
    (IH : ∀ u, u < glA (n : Ordinal.{0}) t ρ → GnI ρ δ u) : GnI ρ δ (glA (n : Ordinal.{0}) t ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set E := glA (n : Ordinal.{0}) t ρ with hEdef
  obtain ⟨hnT, hn1⟩ := ha_nat_T hρE hρ1 n
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn
  obtain ⟨hET0, hρEE, hE1, hE, -, htE⟩ := glA_facts hρE hρ1 hn1' hnT hn1 htT ht1
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  set z := glZeta ρ n t with hzdef
  have hzE : z < E := by
    rcases eq_or_ne t 0 with ht0 | ht0
    · have : z = 0 := by rw [hzdef, ht0]; unfold glZeta; rw [if_neg (fun h => h.1 rfl)]
      rw [this]; exact hE.pos
    · exact ((gz_glZeta_le ρ t n).trans (lg_le ht0)).trans_lt htE
  -- the reach `lh(E) = E·(n+1) + z` and the source
  have hL : IsLh1 E (E * ((n : Ordinal.{0}) + 1) + z) := by
    have := gl_lh_th (k := n) hρE hρ1 hn htT ht1
    push_cast at this
    exact this
  have hMδ : ∀ k : ℕ, E * ((k : Ordinal.{0}) + 1) < δ := ha_mul_lt hδI hEδ
  have hTopδ : E * ((n : Ordinal.{0}) + 1) + z < δ := hδI.add_lt (hMδ n) (hzE.trans hEδ)
  have hsrc : le1 E (E * ((n : Ordinal.{0}) + 1) + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  have w3 := (w1.union w2).insW hρEE.le hEδ (Or.inl (inE_indec hE))
  obtain ⟨W4, w4, hW34, hW4⟩ := ha_wz_muls w3 (Finset.mem_insert_self _ _) hρEE.le hE.pos hMδ n
  have hMn : E * ((n : Ordinal.{0}) + 1) ∈ W4 := hW4 n le_rfl
  have hzZ : z ∈ W4 ∪ (Z1 ∪ Z2) := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (hW34 (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
  have hMnz : E * ((n : Ordinal.{0}) + 1) < E * ((n : Ordinal.{0}) + 1) + z ∨ z = 0 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact Or.inr hz0
    · exact Or.inl (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0))
  -- the top `E·(n+1) + z`
  have hEle : E ≤ E * ((n : Ordinal.{0}) + 1) := by simpa using ha_mul_le_mul (E := E) (Nat.zero_le n)
  obtain ⟨W5, w5, hW45, hTop⟩ : ∃ W5 : Finset Ordinal.{0}, WZ ρ δ W5 (Z1 ∪ Z2) ∧ W4 ⊆ W5 ∧
      E * ((n : Ordinal.{0}) + 1) + z ∈ W5 := by
    rcases hMnz with hlt | hz0
    · refine ⟨insert (E * ((n : Ordinal.{0}) + 1) + z) W4, w4.insW ((hρEE.le.trans hEle).trans le_self_add)
        hTopδ (Or.inr ⟨_, Finset.mem_union_left _ hMn, z, hzZ, hlt, hzE.trans_le (hEle.trans le_self_add), rfl⟩),
        Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
    · exact ⟨W4, w4, subset_refl _, by rw [hz0, add_zero]; exact hMn⟩
  refine gnI_mk h w5 (Finset.mem_union_left _ (hW45 (hW34 (Finset.mem_insert_self _ _)))) hET.1 hET.2
    (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (hW45 (hW34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 hx))))))
  have hW2 : ↑W2 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (hW45 (hW34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 hx))))))
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  have hMA : ∀ k : ℕ, k ≤ n → E * ((k : Ordinal.{0}) + 1) ∈ A := fun k hk =>
    hW (Finset.mem_coe.2 (hW45 (hW4 k hk)))
  have hEA : E ∈ A := by have := hMA 0 (Nat.zero_le n); simpa using this
  have hTopA : E * ((n : Ordinal.{0}) + 1) + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have hfM : f (E * ((n : Ordinal.{0}) + 1)) = f E * ((n : Ordinal.{0}) + 1) := ha_img_muls C n hMA n le_rfl
  have himg : le1 (f E) (f E * ((n : Ordinal.{0}) + 1) + f z) := by
    have := C.cov1 _ hEA _ hTopA hsrc
    rwa [← C.add _ (hMA n le_rfl) _ hzA _ hTopA rfl, hfM] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hEEA : E + E ∈ A := by
    have h1 := hMA 1 hn
    rw [show ((1 : ℕ) : Ordinal.{0}) = ((0 + 1 : ℕ) : Ordinal.{0}) from rfl, ha_mul_succ] at h1
    simpa using h1
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨m, ζ, hmn, hlhu, hζu, hmz⟩ := hdown u huI hE'u huE
  have hl' : l = u * ((m : Ordinal.{0}) + 1) + ζ := lkcIsLh1_unique hl hlhu
  have hum1 : u * ((m : Ordinal.{0}) + 1) < Om1 := ha_mul_lt (inE_indec gl_Om1_E) hu1 m
  obtain ⟨hmTB, hmpi⟩ := ha_pi_muls hB huTB hu1 m
  rw [hl'] at hlTB hle0
  have hlg1 : u * ((m : Ordinal.{0}) + 1) + ζ < Om1 := (inE_indec gl_Om1_E).add_lt hum1 (hζu.trans hu1)
  obtain ⟨hζTB, -⟩ := TB_sub hB hmTB hlTB le_self_add hlg1
  rw [Ordinal.add_sub_cancel] at hζTB
  obtain ⟨-, hps⟩ := pi_add hB hmTB hζTB
  rw [hps, hmpi, hpu] at hle0
  have hπζ : pi (f ρ) ρ ζ < f E := by rw [← hpu]; exact (pi_bijOn hB).2 hζTB huTB hζu
  rcases (Nat.lt_or_ge m n) with hmn' | hmn'
  · -- `m < n`: the reach of `u` is too short
    have h1 : f E * ((m : Ordinal.{0}) + 1) + pi (f ρ) ρ ζ < f E * (((m + 1 : ℕ) : Ordinal.{0}) + 1) := by
      rw [ha_mul_succ]; exact (add_lt_add_iff_left _).2 hπζ
    have h2 : f E * (((m + 1 : ℕ) : Ordinal.{0}) + 1) ≤ f E * ((n : Ordinal.{0}) + 1) :=
      ha_mul_le_mul (E := f E) (Nat.succ_le_of_lt hmn')
    exact absurd (hle0.trans_lt (h1.trans_le h2)) (not_lt.2 le_self_add)
  · -- `m = n`: `ζ < z`, but `π(z) ≤ f(z) ≤ π(ζ)`
    have hmeq : m = n := le_antisymm hmn hmn'
    subst hmeq
    have hfz : f z ≤ pi (f ρ) ρ ζ := (add_le_add_iff_left _).1 hle0
    have hzζ : z ≤ ζ := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    exact absurd (hmz rfl) (not_lt.2 hzζ)

end Img

/-! ## Lemma IMG at `B₃(ρ)` -/

theorem ha_two_add_one : (2 : Ordinal.{0}) + 1 = 3 := by
  have : ((2 : ℕ) : Ordinal.{0}) + 1 = ((3 : ℕ) : Ordinal.{0}) := by push_cast; rfl
  exact_mod_cast this

section B3

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

omit hx hx1 in
/-- **`B₃(x)` is a value of `φ(3, ·)`.** -/
theorem ha_B3_LuP3 : LuP 3 (gzB3 x) := by
  unfold LuP
  rw [mem_range_veblen three_ne_zero]
  intro b hb
  rcases lt_or_ge b 2 with hb2 | hb2
  · have h := veblen_veblen_of_lt hb2 (gzB3 x)
    rwa [gzB3_fix] at h
  · have : b = 2 := le_antisymm (Order.lt_add_one_iff.1 (by rw [ha_two_add_one]; exact hb)) hb2
    rw [this]; exact gzB3_fix x

/-- **`B₃(x) = ϑˣ(Ω₁·3 + Γ_{x+1})`.** -/
theorem ha_B3_eq : glA 3 (lgG x) x = gzB3 x := by
  obtain ⟨hGT, hxG, hG1, -, -⟩ := lgG_facts hx hx1
  have hq := (gm1_facts hx hx1).2.2.2
  have h3q : (3 : Ordinal.{0}) < gq 1 x := (natCast_lt_omega0 3).trans (omega0_lt_inE hq)
  obtain ⟨h3T, h31⟩ := gm1_T hx hx1 h3q
  have h13 : (1 : Ordinal.{0}) ≤ 3 := by norm_num
  have h3x : (3 : Ordinal.{0}) < x := by
    have : ((3 : ℕ) : Ordinal.{0}) < x := (natCast_lt_omega0 3).trans (omega0_lt_inE hx)
    exact_mod_cast this
  have hGB : lgG x < gzB3 x := (lt_evZ _).trans (gzZ1_lt_B3 x)
  refine le_antisymm ?_ ?_
  · refine glA_min hx hx1 h13 h3T h31 hGT hG1 ha_B3_LuP3 (hxG.trans hGB) hGB ((h3x.trans hxG).trans hGB)
      (fun σ hσ => (glA_lt_G hx hx1 (h3x.trans hxG) hσ).trans hGB)
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 h13 h3T h31 hGT hG1
    obtain ⟨k, hk⟩ := glA_P hx hx1 h13 h3T h31 hGT hG1
    have hfix2 : veblen 2 (glA 3 (lgG x) x) = glA 3 (lgG x) x := by
      rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
    have hfix1 : Ordinal.epsilon (glA 3 (lgG x) x) = glA 3 (lgG x) x := by
      rw [← hk]; exact veblen_veblen_of_lt (by norm_num) k
    have hZ : evZ (lgG x) ≤ glA 3 (lgG x) x := evZ_le hta hfix1
    have hne : evZ (lgG x) ≠ glA 3 (lgG x) x := fun e => gz_Z1_notfix hx hx1 (by rw [e]; exact hfix2)
    exact gz_fix_ge_B3 hfix2 (lt_of_le_of_ne hZ hne)

/-- **The reach of `B₃(x)`**: `lh(B₃(x)) = B₃(x)·4 + glZeta x 3 Γ_{x+1}`. -/
theorem ha_B3_lh : IsLh1 (gzB3 x) (gzB3 x * ((3 : Ordinal.{0}) + 1) + glZeta x 3 (lgG x)) := by
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
  have hL := gl_lh_th (k := 3) hx hx1 (by norm_num) hGT hG1
  have e : vt x (Om1 * ((3 : ℕ) : Ordinal.{0}) + lgG x) = gzB3 x := by
    rw [Nat.cast_ofNat]; exact ha_B3_eq hx hx1
  rw [e] at hL
  push_cast at hL
  exact hL

end B3

section ImgB3

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The reach test below `B₃(ρ)`**: every `ε`-number `u ∈ (ζ_{Γ_{ρ+1}+1}, B₃(ρ))` has Veblen level `1` (reach
`u·2 + lg d`) or `2` (reach `u·3 + ζ`), with `ζ < u`. -/
theorem ha_down_B3 {u : Ordinal.{0}} (hu : InE u) (hZu : evZ (lgG ρ) < u) (huB : u < gzB3 ρ) :
    ∃ m : ℕ, ∃ ζ, m ≤ 2 ∧ IsLh1 u (u * ((m : Ordinal.{0}) + 1) + ζ) ∧ ζ < u := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hu1 : u < Om1 := (huB.trans (gzB3_lt1 hρE hρ1)).trans (gm1_facts hρE hρ1).2.2.1
  obtain ⟨i0, hi0⟩ := gw_LuP2 (lgG ρ)
  obtain ⟨j, hj1, hj2⟩ := gz_floor (u := u) (j0 := i0) (by rw [hi0]; exact hZu.le)
  have hi0j : i0 ≤ j := by
    have : veblen 2 i0 < veblen 2 (j + 1) := by rw [hi0]; exact hZu.trans hj2
    exact Order.lt_add_one_iff.1 ((isNormal_veblen 2).strictMono.lt_iff_lt.1 this)
  rcases hj1.lt_or_eq with hju | hju
  · -- level `1`: `u = ε_{φ(2,j)+d}`, reach `u·2 + lg d`
    have hZE : InE (veblen 2 j) := gg_veblen_eps two_ne_zero
    have hZ1 : veblen 2 j < Om1 := hju.trans hu1
    obtain ⟨d, hd⟩ := evA_surj hZE hu hju.le
    have hd0 : d ≠ 0 := by rintro rfl; rw [evA_zero hZE] at hd; exact hju.ne hd
    have hdZ : d < evZ (veblen 2 j) := by
      by_contra hge; push Not at hge
      have : evZ (veblen 2 j) ≤ u := hge.trans ((le_evA_idx _ d).trans hd.le)
      rw [gz_evZ_veb2] at this
      exact absurd hj2 (not_lt.2 this)
    have hlhu : IsLh1 u (u * 2 + lg d) := by rw [← hd]; exact gk_lh_evA hZE hZ1 hd0 hdZ
    have hld : lg d < u := (lg_le hd0).trans_lt (by rw [← hd]; exact lt_evA_self hZE hdZ)
    refine ⟨1, lg d, by norm_num, ?_, hld⟩
    rw [Nat.cast_one, one_add_one_eq_two]; exact hlhu
  · -- level `2`: `u = φ(2, i₀ + d) = ϑᵖ(Ω₁·2 + Γ_{ρ+1} + d)`, reach `u·3 + ζ`
    obtain ⟨d, rfl⟩ := exists_add_of_le hi0j
    have hnf : ∀ ν', ν' ≤ d → IsSuccLimit ν' → i0 + ν' < veblen 2 (i0 + ν') := fun ν' h' _ =>
      gz_nofix_B3 hρE hρ1 hi0 le_self_add
        (((isNormal_veblen 2).monotone ((add_le_add_iff_left _).2 h')).trans_lt (hju ▸ huB))
    have hdu : d < u := (le_add_self : d ≤ i0 + d).trans_lt (by
      rw [← hju]; exact gz_nofix_B3 hρE hρ1 hi0 le_self_add (hju ▸ huB))
    have hq : lgG ρ + d < gq 1 ρ :=
      (inE_indec (gm1_facts hρE hρ1).2.2.2).add_lt (mg_lgG_lt_G1 hρE hρ1)
        (hdu.trans (huB.trans (gzB3_lt1 hρE hρ1)))
    obtain ⟨hdT, hd1⟩ := gm1_T hρE hρ1 hq
    have hval : glA 2 (lgG ρ + d) ρ = u := by rw [← hju]; exact gz_glA2V hρE hρ1 hi0 d hq hnf
    have hL := gl_lh_th (k := 2) hρE hρ1 (by norm_num) hdT hd1
    rw [gz_vt2, hval] at hL
    obtain ⟨h2T, h21⟩ := gw_two_T hρE hρ1
    obtain ⟨-, -, -, -, -, htu⟩ := glA_facts hρE hρ1 one_le_two h2T h21 hdT hd1
    rw [hval] at htu
    have hG0 : lgG ρ + d ≠ 0 := ((hρE.pos.trans (lgG_facts hρE hρ1).2.1).trans_le le_self_add).ne'
    have hζ : glZeta ρ 2 (lgG ρ + d) < u := ((gz_glZeta_le ρ _ 2).trans (lg_le hG0)).trans_lt htu
    refine ⟨2, glZeta ρ 2 (lgG ρ + d), le_rfl, ?_, hζ⟩
    push_cast at hL ⊢
    exact hL

/-- **LEMMA IMG AT `B₃(ρ) = φ(3, Γ_{ρ+1}+1)`**, the least fixed point of `φ(2, ·)` above `ζ_{Γ_{ρ+1}+1}`. -/
theorem ha_img_B3 : GnI ρ δ (gzB3 ρ) := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hGT, hρG, hG1, -, -⟩ := lgG_facts hρE hρ1
  have e3 : glA ((3 : ℕ) : Ordinal.{0}) (lgG ρ) ρ = gzB3 ρ := by rw [Nat.cast_ofNat]; exact ha_B3_eq hρE hρ1
  have hZB : evZ (lgG ρ) < glA ((3 : ℕ) : Ordinal.{0}) (lgG ρ) ρ := by rw [e3]; exact gzZ1_lt_B3 ρ
  have H := ha_img_down h (n := 3) (by norm_num) hGT hG1 (hρG.trans (lt_evZ _)) hZB
    (fun u hu hZu huB => by
      rw [e3] at huB
      obtain ⟨m, ζ, hm, hl, hζ⟩ := ha_down_B3 h hu hZu huB
      exact ⟨m, ζ, hm.trans (by norm_num), hl, hζ, fun e => absurd e (by omega)⟩)
    (fun u hu => gzImg_B3 h u (by rw [e3] at hu; exact hu))
  rwa [e3] at H

/-- **LEMMA IMG FOR EVERY VALUE UP TO AND INCLUDING `B₃(ρ)`.** -/
theorem ha_img_le_B3 {v : Ordinal.{0}} (hv : v ≤ gzB3 ρ) : GnI ρ δ v := by
  rcases hv.lt_or_eq with hv | rfl
  · exact gzImg_B3 h v hv
  · exact ha_img_B3 h

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION UP TO `B₃(ρ)`**: Lemma EXACT above the gate `g < ρ` with constants
`C < ρ` and `T(ρ) ≤ B₃(ρ)` give `T(f ρ) ≤ f(T ρ)` for every covering copy `f` that keeps `g`. -/
theorem ha_pkg_le_B3 {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ ≤ gzB3 ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (ha_img_le_B3 h hT) hex

end ImgB3

/-! ## Lemma IMG below `ζ_{B₃(ρ)+ω}` -/

/-- **`Z'₀ = B₃(x)`, `Z'_{n+1} = evZ(Z'_n)`**: `Z'_n = ζ_{B₃(x)+n}`. -/
noncomputable def haZn (x : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => gzB3 x
  | n + 1 => evZ (haZn x n)

section Zn

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem haZn_facts : ∀ n : ℕ, InE (haZn x n) ∧ x < haZn x n ∧ haZn x n < gq 1 x
  | 0 => ⟨gzB3_E x, ((lgG_facts hx hx1).2.1.trans (lt_evZ _)).trans (gzZ1_lt_B3 x), gzB3_lt1 hx hx1⟩
  | n + 1 => by
    obtain ⟨-, h2, h3⟩ := haZn_facts n
    exact ⟨evZ_E _, h2.trans (lt_evZ _), gw_evZ_lt1 hx hx1 h3⟩

end Zn

section ImgZn

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ζ_{B₃(ρ)+n+1} = evZ(Z'_n)`, EVERY `n`**: `B₃(ρ)` by `ha_img_B3`, the
`ε`-numbers between two `Z'` by `Gw.gwI_epsP`, the `ε`-fixed points `Z'_{n+1}` by `Gw.gwI_fixZ`. -/
theorem ha_img_Zn : ∀ (n : ℕ) (v : Ordinal.{0}), v < evZ (haZn ρ n) → GnI ρ δ v
  | 0 => by
    have hρE := h.ρE
    obtain ⟨hPI, hρP, hPq⟩ := haZn_facts hρE h.ρ1 0
    refine gnImg_of_eps h (fun v hv => gm1_T hρE h.ρ1 (hv.trans (gw_evZ_lt1 hρE h.ρ1 hPq)))
      (fun e he _ heB IHe => ?_)
    rcases lt_trichotomy e (gzB3 ρ) with hlt | heq | hgt
    · exact gzImg_B3 h e hlt
    · rw [heq]; exact ha_img_B3 h
    · exact gwI_epsP h hPI hρP hPq he hgt heB IHe
  | n + 1 => by
    have hρE := h.ρE
    obtain ⟨hPI, hρP, hPq⟩ := haZn_facts hρE h.ρ1 (n + 1)
    have IHn := ha_img_Zn n
    refine gnImg_of_eps h (fun v hv => gm1_T hρE h.ρ1 (hv.trans (gw_evZ_lt1 hρE h.ρ1 hPq)))
      (fun e he _ heB IHe => ?_)
    rcases lt_trichotomy e (haZn ρ (n + 1)) with hlt | heq | hgt
    · exact IHn e hlt
    · obtain ⟨hQI, hρQ, hQq⟩ := haZn_facts hρE h.ρ1 n
      rw [heq]
      exact gwI_fixZ h hQI hρQ hQq IHn
    · exact gwI_epsP h hPI hρP hPq he hgt heB IHe

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ζ_{B₃(ρ)+ω}`.** -/
theorem ha_img_Zw {v : Ordinal.{0}} (hv : ∃ n : ℕ, v < haZn ρ n) : GnI ρ δ v := by
  obtain ⟨n, hn⟩ := hv
  exact ha_img_Zn h n v (hn.trans (lt_evZ _))

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `ζ_{B₃(ρ)+ω}`.** -/
theorem ha_pkg_Zn {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (n : ℕ) (hT : T ρ < haZn ρ n) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (ha_img_Zw h ⟨n, hT⟩) hex

end ImgZn

end Googology.Trans.PoR.InaccPsi.R2.Ha
