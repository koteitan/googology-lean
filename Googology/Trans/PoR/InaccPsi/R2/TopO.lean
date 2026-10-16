import Googology.Trans.PoR.InaccPsi.R2.OTerm
import Googology.Trans.PoR.InaccPsi.R2.TopG

/-!
# Lemma IMG for every offset term, and the input packages of Lemma TOP

The project's Lemma IMG ("a covering copy of an offset term is not below the same term at the copied
base", its paper's 2.4) for every ordinal below the next `ε`-number after the restart `ρ`, i.e. for
every term of `OT` (`rep`), and for the term `ε_{x+1}` (`eN`).  The proof is by induction on the value
`v`, following the Cantor normal form: a constant is fixed; a sum is copied by a sum; for
`v = ω^{ρ+β}` with `β = β' + ω^z` (`z = logend(β)`) the source atom `v ≤₁ v + z` of `R₁⁺` ([W07b]
Theorem 2.2, `le1R_thm22`) holds inside the block of `ρ` (`RstK.lowδ`), the copy keeps it, and below
`ρ` the copy is a `υ`-point (an `ε`-number above the copied base) or has its `R₁⁺` reach
(`ImgCtx.sk`), where Theorem 2.2 bounds its exponent from below.  The terms at the copied base
`f(ρ)` are compared with the uniform comparison (`uni_eq`; [W07a] Def 5.1, Lemma 4.2, Lemma 5.3).

* `WZ` (witness sets), `ImgW` (the IMG statement for one value with its term);
* `RstK.img_val` (**Lemma IMG** for every `v` below the next `ε`-number after `ρ`);
* `ImgPkg` (what Lemma TOP needs from a term `T`), `RstK.top_pkg` (**Lemma TOP** from a package),
  `RstK.pkg_ot` (the package of every term of `OT` with value `≥ 1`), `RstK.pkg_eN` (the package
  of `ε_{x+1}`).

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

theorem opow_inj {a b : Ordinal.{0}} (h : ω ^ a = ω ^ b) : a = b :=
  le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 h.le)
    ((opow_le_opow_iff_right one_lt_omega0).1 h.ge)

/-- Witness sets: `W ⊆ [ρ, δ)`, `Z ⊆ [0, ρ)`, and every element of `W` is indecomposable or the sum
of two smaller elements of `W ∪ Z`. -/
def WZ (ρ δ : Ordinal.{0}) (W Z : Finset Ordinal.{0}) : Prop :=
  (∀ w ∈ W, ρ ≤ w ∧ w < δ) ∧ (∀ z ∈ Z, z < ρ) ∧
    (∀ w ∈ W, Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w)

theorem WZ.empty {ρ δ : Ordinal.{0}} : WZ ρ δ ∅ ∅ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem WZ.union {ρ δ : Ordinal.{0}} {W1 Z1 W2 Z2 : Finset Ordinal.{0}} (h1 : WZ ρ δ W1 Z1)
    (h2 : WZ ρ δ W2 Z2) : WZ ρ δ (W1 ∪ W2) (Z1 ∪ Z2) := by
  refine ⟨fun w hw => ?_, fun z hz => ?_, fun w hw => ?_⟩
  · rcases Finset.mem_union.1 hw with hw | hw
    · exact h1.1 w hw
    · exact h2.1 w hw
  · rcases Finset.mem_union.1 hz with hz | hz
    · exact h1.2.1 z hz
    · exact h2.2.1 z hz
  · rcases Finset.mem_union.1 hw with hw | hw
    · exact cl_mono Finset.subset_union_left Finset.subset_union_left (h1.2.2 w hw)
    · exact cl_mono Finset.subset_union_right Finset.subset_union_right (h2.2.2 w hw)

theorem WZ.insZ {ρ δ : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (h : WZ ρ δ W Z) {z : Ordinal.{0}}
    (hz : z < ρ) : WZ ρ δ W (insert z Z) := by
  refine ⟨h.1, fun x hx => ?_, fun w hw => cl_mono (subset_refl W) (Finset.subset_insert _ _) (h.2.2 w hw)⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact hz
  · exact h.2.1 x hx

theorem WZ.insW {ρ δ : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (h : WZ ρ δ W Z) {w : Ordinal.{0}}
    (h1 : ρ ≤ w) (h2 : w < δ)
    (hc : Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w) :
    WZ ρ δ (insert w W) Z := by
  refine ⟨fun x hx => ?_, h.2.1, fun x hx => ?_⟩
  · rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ⟨h1, h2⟩
    · exact h.1 x hx
  · rcases Finset.mem_insert.1 hx with rfl | hx
    · exact cl_mono (Finset.subset_insert _ _) (subset_refl Z) hc
    · exact cl_mono (Finset.subset_insert _ _) (subset_refl Z) (h.2.2 x hx)

/-- **The IMG statement for one value** `v` with a term `t` for it (`t(ρ) = v`, constants in `Z`):
every covering copy `f` of a set containing the witness sets has `t(f(ρ)) ≤ f(v)`. -/
def ImgW (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : OT) : Prop :=
  WZ ρ δ W Z ∧ CB t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ ev t ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      ev t (f ρ) ≤ f v

theorem mem_A {W Z : Finset Ordinal.{0}} {A : Set Ordinal.{0}} {v : Ordinal.{0}} (hv : v ∈ W ∪ Z)
    (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : v ∈ A := by
  rcases Finset.mem_union.1 hv with hv | hv
  · exact hW (Finset.mem_coe.2 hv)
  · exact hZ (Finset.mem_coe.2 hv)

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem eN_lt_δ : eN ρ < δ :=
  lt_of_le_of_lt (eN_le h.ρτ (upsPt_inE h.τU)) h.τδ

/-- The copied base: `f(ρ) < ρ` are `ε`-numbers below `Ω₁`. -/
theorem img_bases {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) :
    Bases (f ρ) ρ :=
  ⟨upsPt_inE C.ups, h.ρE, C.low ρ C.rho, h.ρ1⟩

omit h in
theorem img_cb {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {t : OT}
    (ht : CB t ρ) (hA : ∀ c ∈ cs t, c ∈ A) : CB t (f ρ) :=
  (cb_iff t _).2 (fun c hc => C.above c (hA c hc) ((cb_iff t ρ).1 ht c hc))

/-- Two terms with constants in `A` and the same value at `ρ` have the same value at `f(ρ)`. -/
theorem img_ueq {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {t u : OT} (ht : CB t ρ) (hu : CB u ρ) (htA : ∀ c ∈ cs t, c ∈ A) (huA : ∀ c ∈ cs u, c ∈ A)
    (he : ev t ρ = ev u ρ) : ev t (f ρ) = ev u (f ρ) :=
  (uni_eq (h.img_bases C) (img_cb C ht htA) (img_cb C hu huA)).1 he

theorem img_ult {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {t u : OT} (ht : CB t ρ) (hu : CB u ρ) (htA : ∀ c ∈ cs t, c ∈ A) (huA : ∀ c ∈ cs u, c ∈ A)
    (he : ev t ρ < ev u ρ) : ev t (f ρ) < ev u (f ρ) :=
  (uni_lt (h.img_bases C) (img_cb C ht htA) (img_cb C hu huA)).1 he

omit h in
/-- A value below `ρ`. -/
theorem img_small {v : Ordinal.{0}} (hv : v < ρ) : ImgW ρ δ v ∅ {v} (k v) := by
  refine ⟨WZ.empty.insZ hv, hv, ?_, rfl, by simp, ?_⟩
  · intro c hc; simp [cs] at hc; simp [hc]
  · intro A f _ hZ C
    have hvA : v ∈ A := hZ (by simp)
    simp only [ev_k]; rw [C.fix v hvA hv]

/-- The value `ρ`. -/
theorem img_rho : ImgW ρ δ ρ {ρ} {0} (xw (k 0)) := by
  have hρE := h.ρE
  have hρr : ω ^ ρ = ρ := hρE
  refine ⟨(WZ.empty.insZ hρE.pos).insW le_rfl h.ρδ (Or.inl (inE_indec hρE)), hρE.pos, ?_,
    by simp [hρr], by simp, ?_⟩
  · intro c hc; simp [cs] at hc; simp [hc]
  · intro A f _ _ C
    have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
    simp [hfE]

omit h in
/-- A decomposable value: a sum. -/
theorem img_sum {u1 u2 : Ordinal.{0}} {W1 Z1 W2 Z2 : Finset Ordinal.{0}} {t1 t2 : OT}
    (h1 : ImgW ρ δ u1 W1 Z1 t1) (h2 : ImgW ρ δ u2 W2 Z2 t2) (hu1 : u1 < u1 + u2)
    (hu2 : u2 < u1 + u2) (hρv : ρ ≤ u1 + u2) (hvδ : u1 + u2 < δ) :
    ImgW ρ δ (u1 + u2) (insert (u1 + u2) (W1 ∪ W2)) (Z1 ∪ Z2) (add t1 t2) := by
  obtain ⟨w1, c1, s1, e1, m1, b1⟩ := h1
  obtain ⟨w2, c2, s2, e2, m2, b2⟩ := h2
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2,
    rfl⟩), ⟨c1, c2⟩, ?_, by simp [e1, e2], by simp, ?_⟩
  · intro c hc
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_union_left _ (s1 c hc)
    · exact Finset.mem_union_right _ (s2 c hc)
  · intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : u1 + u2 ∈ A := hW (by simp)
    have := C.add u1 (mem_A m1 hW1 hZ1) u2 (mem_A m2 hW2 hZ2) _ hvA rfl
    simp only [ev_add]
    rw [← this]
    exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- `ω^{ρ+β'+1}`. -/
theorem img_succ {β' : Ordinal.{0}} {W1 Z1 W2 Z2 : Finset Ordinal.{0}} {t' t2 : OT}
    (h1 : ImgW ρ δ β' W1 Z1 t') (h2 : ImgW ρ δ (ω ^ (ρ + β')) W2 Z2 t2)
    (hvδ : ω ^ (ρ + (β' + 1)) < δ) :
    ImgW ρ δ (ω ^ (ρ + (β' + 1))) (insert (ω ^ (ρ + (β' + 1))) (W1 ∪ W2))
      (insert 1 (Z1 ∪ Z2)) (xw (add t' (k 1))) := by
  obtain ⟨w1, c1, s1, e1, m1, b1⟩ := h1
  obtain ⟨w2, c2, s2, e2, m2, b2⟩ := h2
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have hρr : ω ^ ρ = ρ := h.ρE
  set v := ω ^ (ρ + (β' + 1)) with hv
  set v' := ω ^ (ρ + β') with hv'
  have hv'v : v' < v := (opow_lt_opow_iff_right one_lt_omega0).2
    ((add_lt_add_iff_left ρ).2 (lt_add_one β'))
  have hρv : ρ ≤ v := by
    rw [hv]; nth_rewrite 1 [← hρr]
    exact (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  refine ⟨((w1.union w2).insZ h1ρ).insW hρv hvδ (Or.inl (indec_opow _)), ⟨c1, h1ρ⟩, ?_,
    by simp [e1, hv], by simp, ?_⟩
  · intro c hc
    simp only [cs, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (s1 c hc))
    · exact Finset.mem_insert_self _ _
  · intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have hv'A : v' ∈ A := mem_A m2 hW2 hZ2
    have hcs1 : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (s1 c hc))
    have hcs2 : ∀ c ∈ cs t2, c ∈ A := fun c hc => hZ2 (Finset.mem_coe.2 (s2 c hc))
    have hu : ev (xw t') (f ρ) = ev t2 (f ρ) :=
      h.img_ueq C c1 c2 hcs1 hcs2 (by simp [e1, e2, hv'])
    have hb := b2 A f hW2 hZ2 C
    rw [← hu] at hb
    simp only [ev_xw] at hb
    have hlt : f v' < f v := C.mono hv'A hvA hv'v
    obtain ⟨a, ha⟩ := indec_eq_opow (C.indec v hvA (indec_opow _))
    rw [ha] at hlt ⊢
    have h3 : f ρ + ev t' (f ρ) < a :=
      (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
    simp only [ev_xw, ev_add, ev_k]
    rw [← add_assoc]
    exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)

/-- `ω^z ∣ ρ + β` when `ω^z ∣ β ≠ 0` (`ρ` an `ε`-number). -/
theorem dvd_rho_add {z β : Ordinal.{0}} (hβ0 : β ≠ 0) (hd : ω ^ z ∣ β) : ω ^ z ∣ ρ + β := by
  rcases le_or_gt z ρ with hzρ | hρz
  · exact dvd_add (opow_dvd_of_inE h.ρE hzρ) hd
  · have hρr : ω ^ ρ = ρ := h.ρE
    have h1 : ρ < ω ^ z := by
      nth_rewrite 1 [← hρr]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hρz
    rw [add_of_omega0_opow_le h1 (le_of_dvd hβ0 hd)]
    exact hd

/-- The source atom `ω^{ρ+β} ≤₁ ω^{ρ+β} + z` inside the block of `ρ` (`ω^z ∣ β`, `0 < z`). -/
theorem src_atom {z β : Ordinal.{0}} (hz0 : z ≠ 0) (hβ0 : β ≠ 0) (hd : ω ^ z ∣ β)
    (hzv : z ≤ ω ^ (ρ + β)) (hvδ : ω ^ (ρ + β) + z ≤ δ) :
    le1 (ω ^ (ρ + β)) (ω ^ (ρ + β) + z) := by
  have hρr : ω ^ ρ = ρ := h.ρE
  have hρv : ρ < ω ^ (ρ + β) := by
    nth_rewrite 1 [← hρr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hβ0))
  have hne : ρ + β ≠ 0 := (lt_of_lt_of_le h.ρE.pos le_self_add).ne'
  refine (h.lowδ _ _ hρv hvδ).2 ?_
  exact (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzv).2
    ⟨ρ + β, hne, rfl, (le_lg_iff hne z).2 (h.dvd_rho_add hβ0 hd)⟩

/-- The term `tw` for `ω^z`: its value at `f(ρ)` is at most `ω^{f(z)}`. -/
def TwW (ρ δ z : Ordinal.{0}) (W3 Z3 W4 Z4 : Finset Ordinal.{0}) (tw : OT) : Prop :=
  WZ ρ δ W4 Z4 ∧ CB tw ρ ∧ (∀ c ∈ cs tw, c ∈ Z4) ∧ ev tw ρ = ω ^ z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑(W3 ∪ W4) ⊆ A → ↑(Z3 ∪ Z4) ⊆ A →
      ImgCtx ρ A f → ev tw (f ρ) ≤ ω ^ f z

theorem tw_small {z : Ordinal.{0}} {W3 Z3 : Finset Ordinal.{0}} {tz : OT}
    (h3 : ImgW ρ δ z W3 Z3 tz) (hzρ : z < ρ) : TwW ρ δ z W3 Z3 ∅ {ω ^ z} (k (ω ^ z)) := by
  have hρr : ω ^ ρ = ρ := h.ρE
  have hωz : ω ^ z < ρ := by
    conv_rhs => rw [← hρr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 hzρ
  refine ⟨WZ.empty.insZ hωz, hωz, ?_, rfl, ?_⟩
  · intro c hc; simp [cs] at hc; simp [hc]
  · intro A f hW hZ C
    have hzA : z ∈ A := mem_A h3.2.2.2.2.1 (fun x hx => hW (by simp [Finset.mem_coe.1 hx]))
      (fun x hx => hZ (by simp [Finset.mem_coe.1 hx]))
    simp only [ev_k]; rw [C.fix z hzA hzρ]

theorem tw_big {z ζ : Ordinal.{0}} {W3 Z3 W4 Z4 : Finset Ordinal.{0}} {tz tζ : OT}
    (h3 : ImgW ρ δ z W3 Z3 tz) (h4 : ImgW ρ δ ζ W4 Z4 tζ) (hzζ : ρ + ζ = z) :
    TwW ρ δ z W3 Z3 W4 (insert 0 Z4) (xw tζ) := by
  have hρE := h.ρE
  have hρr : ω ^ ρ = ρ := hρE
  obtain ⟨w4, c4, s4, e4, m4, b4⟩ := h4
  obtain ⟨w3, c3, s3, e3, m3, b3⟩ := h3
  refine ⟨w4.insZ hρE.pos, c4, fun c hc => Finset.mem_insert_of_mem (s4 c hc), by simp [e4, hzζ], ?_⟩
  intro A f hW hZ C
  have hW3 : ↑W3 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ3 : ↑Z3 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZ4 : ↑Z4 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have h0A : (0 : Ordinal.{0}) ∈ A := hZ (by simp)
  have hcs3 : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (s3 c hc))
  have hcs4 : ∀ c ∈ cs (add (xw (k 0)) tζ), c ∈ A := by
    intro c hc
    simp only [cs, List.mem_append, List.mem_singleton] at hc
    rcases hc with rfl | hc
    · exact h0A
    · exact hZ4 (Finset.mem_coe.2 (s4 c hc))
  have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
  have hu : ev tz (f ρ) = ev (add (xw (k 0)) tζ) (f ρ) :=
    h.img_ueq C c3 ⟨hρE.pos, c4⟩ hcs3 hcs4 (by simp [e3, e4, hρr, hzζ])
  have hb := b3 A f hW3 hZ3 C
  rw [hu] at hb
  simp only [ev_add, ev_xw, ev_k, add_zero, hfE] at hb
  simp only [ev_xw]
  exact (opow_le_opow_iff_right one_lt_omega0).2 hb

/-- `ω^{ρ+β}` with `β = β' + ω^z`, `z > 0`: the step of Lemma IMG through the atom
`ω^{ρ+β} ≤₁ ω^{ρ+β} + z` and, for `β' > 0`, `ω^{ρ+β'} ≤₁ ω^{ρ+β'} + z`. -/
theorem img_lim {β' z : Ordinal.{0}} {W1 Z1 W2 Z2 W3 Z3 W4 Z4 : Finset Ordinal.{0}}
    {t' t2 tz tw : OT} (hz0 : z ≠ 0) (hd : ω ^ z ∣ β')
    (hvN : ω ^ (ρ + (β' + ω ^ z)) < eN ρ)
    (h1 : ImgW ρ δ β' W1 Z1 t') (h2 : ImgW ρ δ (ω ^ (ρ + β')) W2 Z2 t2)
    (h3 : ImgW ρ δ z W3 Z3 tz) (h4 : TwW ρ δ z W3 Z3 W4 Z4 tw) :
    ∃ W Z, ImgW ρ δ (ω ^ (ρ + (β' + ω ^ z))) W Z (xw (add t' tw)) := by
  classical
  have hρE := h.ρE
  have hρr : ω ^ ρ = ρ := hρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  obtain ⟨w1, c1, s1, e1, m1, b1⟩ := h1
  obtain ⟨w2, c2, s2, e2, m2, b2⟩ := h2
  obtain ⟨w3, c3, s3, e3, m3, b3⟩ := h3
  obtain ⟨w4, c4, s4, e4, b4⟩ := h4
  set β := β' + ω ^ z with hβ
  set v := ω ^ (ρ + β) with hv
  set v' := ω ^ (ρ + β') with hv'
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le (opow_pos z omega0_pos) le_add_self).ne'
  have hvδ : v < δ := hvN.trans h.eN_lt_δ
  have hρv : ρ < v := by
    rw [hv]; nth_rewrite 1 [← hρr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hβ0))
  -- `ρ + β` is not an `ε`-number, so `z ≤ β < ρ + β < v`
  have hLv : ρ + β < v := by
    have hne : ¬ InE (ρ + β) := fun hE => by
      have h1 : eN ρ ≤ ρ + β := eN_le (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hβ0)) hE
      exact absurd (lt_of_lt_of_le hvN h1) (not_lt.2 (right_le_opow _ one_lt_omega0))
    exact lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => hne e.symm)
  have hzβ : z ≤ β := (right_le_opow z one_lt_omega0).trans le_add_self
  have hzv : z < v := lt_of_le_of_lt (hzβ.trans le_add_self) hLv
  have hv'v : v' < v := (opow_lt_opow_iff_right one_lt_omega0).2
    ((add_lt_add_iff_left ρ).2 (lt_add_of_pos_right β' (opow_pos z omega0_pos)))
  have hρv' : ρ ≤ v' := by
    rw [hv']; nth_rewrite 1 [← hρr]; exact (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  have hvz : v + z < δ := hδI.add_lt hvδ (hzv.trans hvδ)
  have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
  have hvvz : v < v + z := lt_add_of_pos_right v (pos_iff_ne_zero.2 hz0)
  -- the witness sets
  set W0 : Finset Ordinal.{0} := W1 ∪ W2 ∪ W3 ∪ W4 with hW0
  set Z0 : Finset Ordinal.{0} := insert 0 (Z1 ∪ Z2 ∪ Z3 ∪ Z4) with hZ0
  have wz0 : WZ ρ δ W0 Z0 := (((w1.union w2).union w3).union w4).insZ hρE.pos
  have hsub : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 ∨ x ∈ W3 ∪ Z3 → x ∈ W0 ∪ Z0 := by
    intro x hx
    rcases hx with hx | hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hW0, hZ0, hx]
  have hv'm : v' ∈ W0 ∪ Z0 := hsub v' (Or.inr (Or.inl m2))
  have hzm : z ∈ W0 ∪ Z0 := hsub z (Or.inr (Or.inr m3))
  -- for `β' ≠ 0`: `z < v'`
  have hzv' : β' ≠ 0 → z < v' := by
    intro hb0
    have hne : ¬ InE (ρ + β') := fun hE => by
      have h1 : eN ρ ≤ ρ + β' := eN_le (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hb0)) hE
      have h2 : ρ + β' < v := lt_of_lt_of_le ((add_lt_add_iff_left ρ).2
        (lt_add_of_pos_right β' (opow_pos z omega0_pos))) hLv.le
      exact absurd (lt_of_lt_of_le hvN h1) (not_lt.2 h2.le)
    have hb'v : ρ + β' < v' := lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => hne e.symm)
    have hzβ' : z ≤ β' := (right_le_opow z one_lt_omega0).trans (le_of_dvd hb0 hd)
    exact lt_of_le_of_lt (hzβ'.trans le_add_self) hb'v
  -- the extra atom point `v' + z` (only for `β' ≠ 0`)
  set Wx : Finset Ordinal.{0} := if β' = 0 then W0 else insert (v' + z) W0 with hWx
  have hW0x : W0 ⊆ Wx := by
    rw [hWx]; split_ifs
    · exact subset_refl _
    · exact Finset.subset_insert _ _
  have wzx : WZ ρ δ Wx Z0 := by
    rw [hWx]; split_ifs with hb0
    · exact wz0
    · have h1 := hzv' hb0
      exact wz0.insW (hρv'.trans le_self_add) (hδI.add_lt (hv'v.trans hvδ) (hzv.trans hvδ))
        (Or.inr ⟨v', hv'm, z, hzm, lt_add_of_pos_right v' (pos_iff_ne_zero.2 hz0),
          lt_of_lt_of_le h1 le_self_add, rfl⟩)
  have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert v Wx ∪ Z0 := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (hW0x hx))
    · exact Finset.mem_union_right _ hx
  have wzf : WZ ρ δ (insert (v + z) (insert v Wx)) Z0 :=
    (wzx.insW hρv.le hvδ (Or.inl (indec_opow _))).insW (hρv.le.trans le_self_add) hvz
      (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm, hvvz, hzvz, rfl⟩)
  refine ⟨insert (v + z) (insert v Wx), Z0, wzf, ⟨c1, c4⟩, ?_, by simp [e1, e4, hv, hβ], by simp, ?_⟩
  · intro c hc
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Finset.mem_insert_of_mem (by simp [s1 c hc])
    · exact Finset.mem_insert_of_mem (by simp [s4 c hc])
  intro A f hW hZ C
  have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (hW0x (Finset.mem_coe.1 hx)))))
  have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
    hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
  have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
    hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
  have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
  have hW2 : ↑W2 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
  have hW34 : ↑(W3 ∪ W4) ⊆ A := hsW (by intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hW0, hx])
  have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
  have hZ2 : ↑Z2 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
  have hZ34 : ↑(Z3 ∪ Z4) ⊆ A := hsZ (by intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hZ0, hx])
  have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
  have hvA : v ∈ A := hW (by simp)
  have hvzA : v + z ∈ A := hW (by simp)
  have hzA : z ∈ A := mem_A hzm hW0A hZ
  have hv'A : v' ∈ A := mem_A hv'm hW0A hZ
  have hcs1 : ∀ c ∈ cs t', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (s1 c hc))
  have hcs2 : ∀ c ∈ cs t2, c ∈ A := fun c hc => hZ2 (Finset.mem_coe.2 (s2 c hc))
  have hcs4 : ∀ c ∈ cs tw, c ∈ A := fun c hc => hZ34 (by simp [s4 c hc])
  have hfE : InE (f ρ) := upsPt_inE C.ups
  have hfr : ω ^ f ρ = f ρ := hfE
  have hb2 : ω ^ (f ρ + ev t' (f ρ)) ≤ f v' := by
    have hu : ev (xw t') (f ρ) = ev t2 (f ρ) := h.img_ueq C c1 c2 hcs1 hcs2 (by simp [e1, e2, hv'])
    have := b2 A f hW2 hZ2 C
    rw [← hu] at this; simpa using this
  have hb4 : ev tw (f ρ) ≤ ω ^ f z := b4 A f hW34 hZ34 C
  have hfz0 : 0 < f z := by
    have h1 : f 0 < f z := C.mono h0A hzA (pos_iff_ne_zero.2 hz0)
    rwa [C.fix 0 h0A hρE.pos] at h1
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  -- the atom `v ≤₁ v + z` and its copy
  have hsrc : le1 v (v + z) := h.src_atom hz0 hβ0 (dvd_add hd (dvd_refl _)) hzv.le hvz.le
  have himg : le1 (f v) (f v + f z) := by
    have := C.cov1 v hvA (v + z) hvzA hsrc
    rwa [← C.add v hvA z hzA (v + z) hvzA rfl] at this
  have hCB : CB (add t' tw) (f ρ) := ⟨img_cb C c1 hcs1, img_cb C c4 hcs4⟩
  simp only [ev_xw, ev_add]
  by_cases hU : UpsPt (f v)
  · have := ev_lt (upsPt_inE hU) hfρv (xw (add t' tw)) (CB_mono hCB hfρv.le)
    simp only [ev_xw, ev_add] at this
    exact this.le
  have hR := (C.sk (f v) (C.low v hvA) hU (f v + f z)).1 himg
  obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfz0 (C.mono hzA hvA hzv).le).1 hR
  have hdiv : ω ^ f z ∣ a := (le_lg_iff ha0 _).1 hza
  rw [hfa]
  refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
  by_cases hb0 : β' = 0
  · have ht'0 : ev t' (f ρ) = 0 := by
      have := h.img_ueq C c1 (t := t') (u := k 0) hρE.pos hcs1 (by simp [cs, h0A]) (by simp [e1, hb0])
      simpa using this
    rw [ht'0, zero_add]
    have hfρa : f ρ < a := by
      have := hfρv; rw [hfa] at this; nth_rewrite 1 [← hfr] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    rcases le_or_gt (f z) (f ρ) with hzr | hrz
    · exact (add_le_add le_rfl hb4).trans (dvd_next hdiv (opow_dvd_of_inE hfE hzr) hfρa)
    · have h1 : f ρ < ω ^ f z := by
        nth_rewrite 1 [← hfr]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hrz
      calc f ρ + ev tw (f ρ) ≤ f ρ + ω ^ f z := add_le_add le_rfl hb4
        _ = ω ^ f z := add_of_omega0_opow_le h1 le_rfl
        _ ≤ a := le_of_dvd ha0 hdiv
  · have hzv'' := hzv' hb0
    have hρv'' : ρ < v' := by
      rw [hv']; nth_rewrite 1 [← hρr]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hb0))
    have hv'zA : v' + z ∈ A := by
      have : v' + z ∈ Wx := by rw [hWx, if_neg hb0]; exact Finset.mem_insert_self _ _
      exact hW (by simp [this])
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec v' hv'A (indec_opow _))
    have hbc : f ρ + ev t' (f ρ) ≤ c := by
      rw [hc] at hb2; exact (opow_le_opow_iff_right one_lt_omega0).1 hb2
    have hca : c < a := by
      have := C.mono hv'A hvA hv'v
      rw [hc, hfa] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hfρv' : f ρ < f v' := C.mono C.rho hv'A hρv''
    by_cases hU' : UpsPt (f v')
    · have hE' := upsPt_inE hU'
      have hce : c = f v' := by
        have h1 : ω ^ (f v') = f v' := hE'
        exact opow_inj (by rw [← hc, h1])
      have hlt : f ρ + (ev t' (f ρ) + ev tw (f ρ)) < f v' :=
        (inE_indec hE').add_lt hfρv' (ev_lt hE' hfρv' (add t' tw) (CB_mono hCB hfρv'.le))
      rw [← hce] at hlt
      exact (hlt.trans hca).le
    · have hsrc' : le1 v' (v' + z) := h.src_atom hz0 hb0 hd hzv''.le
        (hδI.add_lt (hv'v.trans hvδ) (hzv.trans hvδ)).le
      have himg' : le1 (f v') (f v' + f z) := by
        have := C.cov1 v' hv'A (v' + z) hv'zA hsrc'
        rwa [← C.add v' hv'A z hzA (v' + z) hv'zA rfl] at this
      have hR' := (C.sk (f v') (C.low v' hv'A) hU' (f v' + f z)).1 himg'
      obtain ⟨c', hc'0, hfc', hzc'⟩ := (le1R_thm22 hfz0 (C.mono hzA hv'A hzv'').le).1 hR'
      have hcc : c' = c := opow_inj (hfc'.symm.trans hc)
      rw [hcc] at hzc' hc'0
      have hdiv' : ω ^ f z ∣ c := (le_lg_iff hc'0 _).1 hzc'
      calc f ρ + (ev t' (f ρ) + ev tw (f ρ)) = (f ρ + ev t' (f ρ)) + ev tw (f ρ) := (add_assoc _ _ _).symm
        _ ≤ c + ω ^ f z := add_le_add hbc hb4
        _ ≤ a := dvd_next hdiv hdiv' hca

/-- **Lemma IMG** for every value `v` below the next `ε`-number after `ρ`: a term `t` for `v` and
witness sets such that every covering copy `f` (with `f(ρ)` a `υ`-point) of a set containing them has
`t(f(ρ)) ≤ f(v)`. -/
theorem img_val : ∀ v, v < eN ρ → ∃ W Z t, ImgW ρ δ v W Z t := by
  have hρE := h.ρE
  have hρr : ω ^ ρ = ρ := hρE
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans h.eN_lt_δ
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact ⟨∅, {v}, k v, img_small hvρ⟩
  by_cases hI : Indec v
  · obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have hρL : ρ ≤ L := by
      have h1 : ω ^ ρ ≤ ω ^ L := by rw [hρr]; exact hρv
      exact (opow_le_opow_iff_right one_lt_omega0).1 h1
    obtain ⟨β, rfl⟩ : ∃ β, L = ρ + β := ⟨L - ρ, (Ordinal.add_sub_cancel_of_le hρL).symm⟩
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · rw [hβ0, add_zero, hρr]; exact ⟨_, _, _, h.img_rho⟩
    have hne : ¬ InE (ρ + β) := fun hE => by
      have h1 : eN ρ ≤ ρ + β := eN_le (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hβ0)) hE
      exact absurd (lt_of_lt_of_le hv h1) (not_lt.2 (right_le_opow _ one_lt_omega0))
    have hLv : ρ + β < ω ^ (ρ + β) :=
      lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => hne e.symm)
    have hβv : β < ω ^ (ρ + β) := lt_of_le_of_lt le_add_self hLv
    obtain ⟨β', hgs, hdvd, hβ'β⟩ := lg_split hβ0
    have hzβ : lg β ≤ β := lg_le hβ0
    have hβ'v : β' < ω ^ (ρ + β) := hβ'β.trans hβv
    obtain ⟨W1, Z1, t', h1⟩ := IH β' hβ'v (hβ'v.trans hv)
    have hv'v : ω ^ (ρ + β') < ω ^ (ρ + β) :=
      (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left ρ).2 hβ'β)
    obtain ⟨W2, Z2, t2, h2⟩ := IH _ hv'v (hv'v.trans hv)
    have hzv : lg β < ω ^ (ρ + β) := lt_of_le_of_lt hzβ hβv
    rcases eq_or_ne (lg β) 0 with hz0 | hz0
    · have e : ω ^ (ρ + β) = ω ^ (ρ + (β' + 1)) := by
        conv_lhs => rw [hgs, hz0, opow_zero]
      rw [e] at hv ⊢
      exact ⟨_, _, _, h.img_succ h1 h2 (hv.trans h.eN_lt_δ)⟩
    obtain ⟨W3, Z3, tz, h3⟩ := IH (lg β) hzv (hzv.trans hv)
    have htw : ∃ W4 Z4 tw, TwW ρ δ (lg β) W3 Z3 W4 Z4 tw := by
      rcases lt_or_ge (lg β) ρ with hzρ | hρz
      · exact ⟨_, _, _, h.tw_small h3 hzρ⟩
      · have hζv : lg β - ρ < ω ^ (ρ + β) := lt_of_le_of_lt (sub_le_self _ ρ) hzv
        obtain ⟨W4, Z4, tζ, h4⟩ := IH (lg β - ρ) hζv (hζv.trans hv)
        exact ⟨_, _, _, h.tw_big h3 h4 (Ordinal.add_sub_cancel_of_le hρz)⟩
    obtain ⟨W4, Z4, tw, h4⟩ := htw
    have e : ω ^ (ρ + β) = ω ^ (ρ + (β' + ω ^ lg β)) := by
      conv_lhs => rw [hgs]
    rw [e] at hv ⊢
    obtain ⟨W, Z, hW⟩ := h.img_lim hz0 hdvd hv h1 h2 h3 h4
    exact ⟨W, Z, _, hW⟩
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
    obtain ⟨W1, Z1, t1, h1⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨W2, Z2, t2, h2⟩ := IH u2 hu2 (hu2.trans hv)
    subst hsum
    exact ⟨_, _, _, img_sum h1 h2 hu1 hu2 hρv hvδ⟩

end RstK

/-- **The input of Lemma TOP from a term `T`** at the restart `ρ` with first block top `δ`:
`1 ≤ T(ρ) < δ`, and witness sets such that every covering copy `f` has `T(f(ρ)) ≤ f(T(ρ))`. -/
def ImgPkg (ρ δ : Ordinal.{0}) (T : Ordinal.{0} → Ordinal.{0}) : Prop :=
  1 ≤ T ρ ∧ T ρ < δ ∧ ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ T ρ ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      T (f ρ) ≤ f (T ρ)

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma TOP from a package** (FRAG-free): `ρ` is not `≤₁` any `γ > δ + T(ρ)` if no `<₂`-pair above
`x₀` below `ρ` has a point `x ≤₁ d + e'` with `e' ≥ 1`, `e' ≥ T(x)` for `υ`-points `x`. -/
theorem top_pkg {T : Ordinal.{0} → Ordinal.{0}} {x0 : Ordinal.{0}} (hP : ImgPkg ρ δ T)
    (hx0 : x0 < ρ) (hsk : ∀ α < ρ, ¬ UpsPt α → ∀ g, le1 α g ↔ le1R α g)
    (hcap : ∀ c d, x0 < c → c < d → d < ρ → le2 c d → ∀ x, x0 < x → x ≤ c → ∀ e', 1 ≤ e' →
      (UpsPt x → T x ≤ e') → ¬ le1 x (d + e')) :
    ∀ g, δ + T ρ < g → ¬ le1 ρ g := by
  obtain ⟨h1, hδ, W, Z, ⟨hW, hZ, hcl⟩, hm, hI⟩ := hP
  exact h.top_core hx0 h1 hδ hW hZ hcl hm hsk hI hcap

/-- The package of a term of `OT` with constants below `ρ` and value `≥ 1` (Lemma IMG). -/
theorem pkg_ot {t : OT} (ht : CB t ρ) (h1 : 1 ≤ ev t ρ) : ImgPkg ρ δ (ev t) := by
  classical
  obtain ⟨W, Z, t0, hw, c0, s0, e0, m0, b0⟩ := h.img_val (ev t ρ) (ev_lt_eN ht)
  have wzc : WZ ρ δ ∅ (cs t).toFinset := by
    refine ⟨by simp, fun z hz => (cb_iff t ρ).1 ht z (List.mem_toFinset.1 hz), by simp⟩
  have hw' := hw.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨h1, (ev_lt_eN ht).trans h.eN_lt_δ, W, Z ∪ (cs t).toFinset, hw', ?_, ?_⟩
  · rcases Finset.mem_union.1 m0 with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  · intro A f hW hZ C
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hcs : ∀ c ∈ cs t, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcs0 : ∀ c ∈ cs t0, c ∈ A := fun c hc => hZ0 (Finset.mem_coe.2 (s0 c hc))
    rw [h.img_ueq C ht c0 hcs hcs0 e0.symm]
    exact b0 A f hW hZ0 C

/-- The package of `ε_{x+1}` (`eN`): the atom `e ≤₁ e·2` of `R₁⁺` for `e = ε_{ρ+1}` ([W07b], the remark
after Theorem 2.2, `le1R_two_iff`). -/
theorem pkg_eN : ImgPkg ρ δ eN := by
  classical
  have hρe : ρ < eN ρ := lt_eN ρ
  have heE := eN_E ρ
  have heδ := h.eN_lt_δ
  have hδI := inE_indec h.δE
  have hee : eN ρ + eN ρ < δ := hδI.add_lt heδ heδ
  have hepos : 0 < eN ρ := heE.pos
  refine ⟨one_le_iff_pos.2 hepos, heδ, {eN ρ + eN ρ, eN ρ}, ∅, ?_, by simp, ?_⟩
  · have w1 : WZ ρ δ {eN ρ} ∅ := by
      have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρe.le heδ (Or.inl (inE_indec heE))
      simpa using this
    have := w1.insW (hρe.le.trans le_self_add) hee
      (Or.inr ⟨eN ρ, by simp, eN ρ, by simp, lt_add_of_pos_right _ hepos,
        lt_add_of_pos_right _ hepos, rfl⟩)
    simpa using this
  · intro A f hW _ C
    have heA : eN ρ ∈ A := hW (by simp)
    have heeA : eN ρ + eN ρ ∈ A := hW (by simp)
    have hsrc : le1 (eN ρ) (eN ρ + eN ρ) := by
      refine (h.lowδ _ _ hρe hee.le).2 ?_
      rw [← mul_two_eq]; exact (le1R_two_iff hepos).2 heE
    have himg : le1 (f (eN ρ)) (f (eN ρ) + f (eN ρ)) := by
      have := C.cov1 _ heA _ heeA hsrc
      rwa [← C.add _ heA _ heA _ heeA rfl] at this
    have hfρe : f ρ < f (eN ρ) := C.mono C.rho heA hρe
    by_cases hU : UpsPt (f (eN ρ))
    · exact eN_le hfρe (upsPt_inE hU)
    · have hR := (C.sk _ (C.low _ heA) hU _).1 himg
      rw [← mul_two_eq] at hR
      exact eN_le hfρe ((le1R_two_iff (lt_of_le_of_lt zero_le hfρe)).1 hR)

end RstK


end Googology.Trans.PoR.InaccPsi.R2
