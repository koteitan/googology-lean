import Googology.Trans.PoR.InaccPsi.R2.GnA

/-!
# LEMMA IMG IN `π`-FORM, GENERIC: from the `ε`-numbers to every value; every value below `ε_{Γ_{ρ+1}+1}`

The witness terms of the earlier rounds (`OT`, `OTY`, `GkT`, `VzTm`, `LvGT`) are replaced by `π` itself: the
statement `GnI ρ δ v` says that every covering copy `f` (of a set containing the witness sets) has
`π_{f(ρ),ρ}(v) ≤ f(v)`; the parameters of `v` are put into the witness set `Z`, so `v ∈ Tᵖ[f(ρ)]` holds for every
such copy.  `π` is additive and commutes with `ω^·` on `Tᵖ[σ] ∩ Ω₁` at `υ`-points (`pi_add`, `pi_opowZ`), so ONE
well-founded induction on the value reduces Lemma IMG for every value below a bound `B` to Lemma IMG for the
`ε`-numbers in `[ρ, B)`:

* `GnI`, `gnI_TB`, `gnI_small`, `gnI_add` (sums), `gnI_succ` (`ω^{X+1}`), `gnI_lim` (`ω^{X'+ω^z}`, `z > 0`, through
  the source atoms `ω^X ≤₁ ω^X + z` of [W07b] Theorem 2.2 inside the block of `ρ`, as `RstK.img_lim`);
* `gnImg_of_eps` (**THE GENERIC STEP: Lemma IMG for every `ε`-number in `[ρ, B)` gives it for every value below
  `B`**, `B ⊆ Tᵖ ∩ Ω₁`);
* `gnI_lowG` (every value below `Γ_{ρ+1}`, `LvGK.imgLvG` and `LvGT.pi`), `gnI_G` (the value `Γ_{ρ+1}`,
  `LgK.lgTopPkg`, `Gm.mg_lgG_pi`), `gnImg_G` (**Lemma IMG for every value below `ε_{Γ_{ρ+1}+1}`**);
* `gnPkg_of_GnI`, `gnPkg_of_ex` (**Lemma IMG (gated) for a SPECIFIED function `T` with Lemma EXACT and
  `T(ρ) < ε_{Γ_{ρ+1}+1}`**: values above `Γ_{ρ+1}` and sums with `Γ_{ρ+1}` in any position).

No new axiom.  New definition: `GnI`.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **Lemma IMG in `π`-form for one value `v`**: witness sets `W, Z` containing `v`, the parameters of `v` in `Z`, and
every covering copy `f` of a set containing them has `π_{f(ρ),ρ}(v) ≤ f(v)`. -/
def GnI (ρ δ v : Ordinal.{0}) : Prop :=
  ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ v ∈ W ∪ Z ∧ v ∈ Tset ρ ∧ v < Om1 ∧ (∀ p ∈ Par ρ v, p ∈ Z) ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      pi (f ρ) ρ v ≤ f v

/-- A member of `Tᵗ ∩ Ω₁` is below every `υ`-point above `τ`. -/
theorem gn_lt_ups {y a u : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (ha : a ∈ Tset y) (ha1 : a < Om1)
    (hu : UpsPt u) (hyu : y < u) : a < u := by
  obtain ⟨m, -, -, hmin, hT, -⟩ := T_next (Or.inr hy) hy1
  exact ((hT a ha1).1 ha).trans_le (hmin u hyu hu.2)

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem gn_par_lt {v p : Ordinal.{0}} (hv : v ∈ Tset ρ) (hp : p ∈ Par ρ v) : p < ρ :=
  Par_sub h.ρE h.ρ1 hv (Finset.mem_coe.2 hp)

/-- **The membership `v ∈ Tᵖ[f(ρ)]`** from the parameters in the domain of the copy. -/
theorem gnI_TB {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {v : Ordinal.{0}}
    (hv : v ∈ Tset ρ) (hP : ∀ p ∈ Par ρ v, p ∈ A) : v ∈ TB ρ (f ρ) :=
  ⟨hv, fun p hp => C.above p (hP p (Finset.mem_coe.1 hp)) (Par_sub h.ρE h.ρ1 hv hp)⟩

/-- A value of `Tᵖ ∩ Ω₁` lies below `δ`. -/
theorem gn_lt_δ {v : Ordinal.{0}} (hv : v ∈ Tset ρ) (hv1 : v < Om1) : v < δ :=
  (gn_lt_ups h.ρE h.ρ1 hv hv1 h.τU h.ρτ).trans h.τδ

/-- Add the parameters of `v` to `Z`. -/
theorem gn_wz_par {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) {v : Ordinal.{0}} (hv : v ∈ Tset ρ) :
    WZ ρ δ W (Z ∪ Par ρ v) := by
  have := w.union (Gj.wz_consts (δ := δ) (C := Par ρ v) (fun c hc => gn_par_lt h hv hc))
  rwa [Finset.union_empty] at this

/-- **Building `GnI`** from witness sets, with the parameters of `v` added to `Z`. -/
theorem gnI_mk {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hm : v ∈ W ∪ Z) (hv : v ∈ Tset ρ)
    (hv1 : v < Om1)
    (hI : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑(Z ∪ Par ρ v) ⊆ A → ImgCtx ρ A f →
      pi (f ρ) ρ v ≤ f v) : GnI ρ δ v := by
  classical
  refine ⟨W, Z ∪ Par ρ v, gn_wz_par h w hv, ?_, hv, hv1, fun p hp => Finset.mem_union_right _ hp, hI⟩
  rcases Finset.mem_union.1 hm with hm | hm
  · exact Finset.mem_union_left _ hm
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)

/-- **A value below `ρ`.** -/
theorem gnI_small {v : Ordinal.{0}} (hv : v < ρ) : GnI ρ δ v := by
  classical
  have hvT : v ∈ Tset ρ := mem_T_of_le h.ρE h.ρ1 hv.le
  refine gnI_mk h (WZ.empty.insZ hv) (by simp) hvT (hv.trans h.ρ1) (fun A f _ hZ C => ?_)
  have hvA : v ∈ A := hZ (by simp)
  have hvσ : v < f ρ := C.above v hvA hv
  rw [pi_lt (h.img_bases C) hvσ, C.fix v hvA hv]

/-- The pieces of a `GnI` inside a copy. -/
theorem gnI_use {v : Ordinal.{0}} (hI : GnI ρ δ v) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ v ∈ W ∪ Z ∧ v ∈ Tset ρ ∧ v < Om1 ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        v ∈ A ∧ v ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ v ≤ f v := by
  obtain ⟨W, Z, w, m, hv, hv1, hP, b⟩ := hI
  refine ⟨W, Z, w, m, hv, hv1, fun A f hW hZ C => ⟨mem_A m hW hZ, ?_, b A f hW hZ C⟩⟩
  exact gnI_TB h C hv (fun p hp => hZ (Finset.mem_coe.2 (hP p hp)))

/-- **A sum** `v = u₁ + u₂` with `u₁, u₂ < v`. -/
theorem gnI_add {u1 u2 : Ordinal.{0}} (h1 : GnI ρ δ u1) (h2 : GnI ρ δ u2) (hu1 : u1 < u1 + u2)
    (hu2 : u2 < u1 + u2) (hρv : ρ ≤ u1 + u2) (hvT : u1 + u2 ∈ Tset ρ) (hv1 : u1 + u2 < Om1) :
    GnI ρ δ (u1 + u2) := by
  classical
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h h1
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h h2
  have hvδ := gn_lt_δ h hvT hv1
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine gnI_mk h ((w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm _ (Or.inl m1), u2, hm _ (Or.inr m2), hu1, hu2, rfl⟩))
    (by simp) hvT hv1 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨a1, t1, p1⟩ := b1 A f hW1 hZ1 C
  obtain ⟨a2, t2, p2⟩ := b2 A f hW2 hZ2 C
  have hvA : u1 + u2 ∈ A := hW (by simp)
  rw [(pi_add (h.img_bases C) t1 t2).2, ← C.add u1 a1 u2 a2 _ hvA rfl]
  exact add_le_add p1 p2

/-- **`ω^{X+1}`** from `ω^X`. -/
theorem gnI_succ {X : Ordinal.{0}} (hw : GnI ρ δ (ω ^ X)) (hXT : X ∈ Tset ρ) (hX1 : X + 1 < Om1)
    (hρv : ρ ≤ ω ^ (X + 1)) (hvT : ω ^ (X + 1) ∈ Tset ρ) (hv1 : ω ^ (X + 1) < Om1) : GnI ρ δ (ω ^ (X + 1)) := by
  classical
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h hw
  have hvδ := gn_lt_δ h hvT hv1
  have hX1' : X < Om1 := (lt_add_one X).trans hX1
  refine gnI_mk h ((w1.union (gn_wz_par h WZ.empty hXT)).insW hρv hvδ (Or.inl (indec_opow _)))
    (by simp) hvT hv1 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hPX : ∀ p ∈ Par ρ X, p ∈ A := fun p hp => hZ (by simp [hp])
  obtain ⟨aw, -, pw⟩ := b1 A f hW1 hZ1 C
  have hB := h.img_bases C
  have hXTB := gnI_TB h C hXT hPX
  obtain ⟨o1, o2⟩ := one_TB hB
  obtain ⟨s1, s2⟩ := pi_add hB hXTB o1
  rw [o2] at s2
  obtain ⟨-, e1⟩ := pi_opowZ C.ups h.ρU hB hXTB hX1'
  obtain ⟨-, e2⟩ := pi_opowZ C.ups h.ρU hB s1 hX1
  have hvA : ω ^ (X + 1) ∈ A := hW (by simp)
  have hlt : f (ω ^ X) < f (ω ^ (X + 1)) :=
    C.mono aw hvA ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one X))
  obtain ⟨a, ha⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
  rw [e2, s2, ha]
  rw [e1] at pw
  rw [ha] at hlt
  have : pi (f ρ) ρ X < a := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt pw hlt)
  exact (opow_le_opow_iff_right one_lt_omega0).2 (Order.add_one_le_of_lt this)

/-- A source atom `ω^Y ≤₁ ω^Y + z` inside the block of `ρ` (`ω^z ∣ Y`, `0 < z ≤ ω^Y`). -/
theorem gn_src {Y z : Ordinal.{0}} (hY0 : Y ≠ 0) (hz0 : z ≠ 0) (hd : ω ^ z ∣ Y) (hzv : z ≤ ω ^ Y)
    (hρv : ρ < ω ^ Y) (hvδ : ω ^ Y + z ≤ δ) : le1 (ω ^ Y) (ω ^ Y + z) :=
  (h.lowδ _ _ hρv hvδ).2 ((le1R_thm22 (pos_iff_ne_zero.2 hz0) hzv).2 ⟨Y, hY0, rfl, (le_lg_iff hY0 z).2 hd⟩)

/-- The copy of a source atom: `f(ω^Y) = ω^a` with `ω^{f(z)} ∣ a`, unless `f(ω^Y)` is a `υ`-point. -/
theorem gn_src_img {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {Y z : Ordinal.{0}}
    (hsrc : le1 (ω ^ Y) (ω ^ Y + z)) (hvA : ω ^ Y ∈ A) (hzA : z ∈ A) (hvzA : ω ^ Y + z ∈ A) (hzv : z ≤ ω ^ Y)
    (hz0 : z ≠ 0) (h0A : (0 : Ordinal.{0}) ∈ A) (hU : ¬ UpsPt (f (ω ^ Y))) :
    ∃ a, a ≠ 0 ∧ f (ω ^ Y) = ω ^ a ∧ ω ^ f z ∣ a := by
  have himg : le1 (f (ω ^ Y)) (f (ω ^ Y) + f z) := by
    have := C.cov1 _ hvA _ hvzA hsrc
    rwa [← C.add _ hvA z hzA _ hvzA rfl] at this
  have hfz0 : 0 < f z := by
    have h1 : f 0 < f z := C.mono h0A hzA (pos_iff_ne_zero.2 hz0)
    rwa [C.fix 0 h0A h.ρE.pos] at h1
  have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
  have hfzv : f z ≤ f (ω ^ Y) := by
    rcases hzv.lt_or_eq with hlt | heq
    · exact (C.mono hzA hvA hlt).le
    · rw [heq]
  obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfz0 hfzv).1 hR
  exact ⟨a, ha0, hfa, (le_lg_iff ha0 _).1 hza⟩

/-- **`ω^{X'+ω^z}`** (`z > 0`, `ω^z ∣ X'`) from `z` and, for `X' ≠ 0`, from `ω^{X'}`. -/
theorem gnI_lim {X' z : Ordinal.{0}} (hz0 : z ≠ 0) (hd : ω ^ z ∣ X') (hzI : GnI ρ δ z)
    (hwI : X' ≠ 0 → GnI ρ δ (ω ^ X')) (hX'T : X' ∈ Tset ρ) (hzT : z ∈ Tset ρ)
    (hX1 : X' + ω ^ z < Om1) (hXv : X' + ω ^ z < ω ^ (X' + ω ^ z))
    (hρv : ρ < ω ^ (X' + ω ^ z)) (hvT : ω ^ (X' + ω ^ z) ∈ Tset ρ) (hv1 : ω ^ (X' + ω ^ z) < Om1) :
    GnI ρ δ (ω ^ (X' + ω ^ z)) := by
  classical
  set X := X' + ω ^ z with hXdef
  set v := ω ^ X with hvdef
  have hρE := h.ρE
  have hδI := inE_indec h.δE
  have hvδ := gn_lt_δ h hvT hv1
  have hX0 : X ≠ 0 := (lt_of_lt_of_le (opow_pos z omega0_pos) le_add_self).ne'
  have hlgX : lg X = z := Ge.lg_add_opow hd
  have hzX : z ≤ X := by rw [← hlgX]; exact lg_le hX0
  have hzv : z < v := lt_of_le_of_lt hzX hXv
  have hvz : v + z < δ := hδI.add_lt hvδ (hzv.trans hvδ)
  have hdX : ω ^ z ∣ X := by rw [hXdef]; exact dvd_add hd (dvd_refl _)
  have hsrc : le1 v (v + z) := gn_src h hX0 hz0 hdX hzv.le hρv hvz.le
  have hX'1 : X' < Om1 := lt_of_le_of_lt le_self_add hX1
  have hz1 : z < Om1 := hzv.trans hv1
  -- `X' ≥ ρ` when `X' ≠ 0`
  have hX'v' : X' ≠ 0 → ρ ≤ ω ^ X' ∧ z ≤ ω ^ X' ∧ ω ^ X' < v := by
    intro hX'0
    have hzX' : z ≤ X' := (le_lg_iff hX'0 z).2 hd |>.trans (lg_le hX'0)
    have hρX' : ρ ≤ X' := by
      by_contra hlt
      push Not at hlt
      have hwz : ω ^ z ≤ X' := Ordinal.le_of_dvd hX'0 hd
      have hXρ : X < ρ := (inE_indec hρE).add_lt hlt (hwz.trans_lt hlt)
      have : v < ρ := by
        rw [hvdef, ← show ω ^ ρ = ρ from hρE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hXρ
      exact absurd hρv (not_lt.2 this.le)
    refine ⟨?_, hzX'.trans (right_le_opow _ one_lt_omega0), ?_⟩
    · rw [← show ω ^ ρ = ρ from hρE]; exact (opow_le_opow_iff_right one_lt_omega0).2 hρX'
    · exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right X' (opow_pos z omega0_pos))
  obtain ⟨W3, Z3, w3, m3, -, -, b3⟩ := gnI_use h hzI
  -- the witness sets
  have hwz : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (X' ≠ 0 → ω ^ X' ∈ W ∪ Z ∧ ω ^ X' + z ∈ W) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        X' ≠ 0 → ω ^ X' ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ (ω ^ X') ≤ f (ω ^ X') := by
    by_cases hX'0 : X' = 0
    · exact ⟨∅, ∅, WZ.empty, fun h' => absurd hX'0 h', fun _ _ _ _ _ h' => absurd hX'0 h'⟩
    obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (hwI hX'0)
    obtain ⟨hρv', hzv', hv'v⟩ := hX'v' hX'0
    have hv'δ : ω ^ X' < δ := hv'v.trans hvδ
    have hm3 : z ∈ W2 ∪ W3 ∪ (Z2 ∪ Z3) := by
      rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm]
    have hm2 : ω ^ X' ∈ W2 ∪ W3 ∪ (Z2 ∪ Z3) := by
      rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm]
    have hpos : ω ^ X' < ω ^ X' + z := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0)
    refine ⟨insert (ω ^ X' + z) (W2 ∪ W3), Z2 ∪ Z3,
      (w2.union w3).insW (hρv'.trans le_self_add) (hδI.add_lt hv'δ (hzv.trans hvδ))
        (Or.inr ⟨ω ^ X', hm2, z, hm3, hpos, lt_of_le_of_lt hzv' hpos, rfl⟩),
      fun _ => ⟨by
        rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm], by simp⟩, ?_⟩
    intro A f hW hZ C _
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    obtain ⟨-, t2, p2⟩ := b2 A f hW2 hZ2 C
    exact ⟨t2, p2⟩
  obtain ⟨W0, Z0, w0, hm0, b0⟩ := hwz
  have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
  have hvvz : v < v + z := lt_add_of_pos_right v (pos_iff_ne_zero.2 hz0)
  have wb : WZ ρ δ (W0 ∪ W3) (insert 0 (Z0 ∪ Z3)) := (w0.union w3).insZ hρE.pos
  have wb2 := ((wb.union (gn_wz_par h WZ.empty hX'T)).union (gn_wz_par h WZ.empty hzT))
  refine gnI_mk h ((wb2.insW hρv.le hvδ (Or.inl (indec_opow _))).insW (hρv.le.trans le_self_add) hvz
      (Or.inr ⟨v, by simp, z, by
        rcases Finset.mem_union.1 m3 with hm | hm <;> simp [hm], hvvz, hzvz, rfl⟩))
    (by simp) hvT hv1 (fun A f hW hZ C => ?_)
  -- the copy
  have hsub : ∀ x, x ∈ W0 ∨ x ∈ W3 → x ∈ (A : Set Ordinal.{0}) := fun x hx => hW (by
    rcases hx with hx | hx <;> simp [hx])
  have hsubZ : ∀ x, x ∈ Z0 ∨ x ∈ Z3 ∨ x = 0 ∨ x ∈ Par ρ X' ∨ x ∈ Par ρ z → x ∈ A := fun x hx => hZ (by
    rcases hx with hx | hx | hx | hx | hx <;> simp [hx])
  have hW0 : ↑W0 ⊆ A := fun x hx => hsub x (Or.inl (Finset.mem_coe.1 hx))
  have hW3 : ↑W3 ⊆ A := fun x hx => hsub x (Or.inr (Finset.mem_coe.1 hx))
  have hZ0 : ↑Z0 ⊆ A := fun x hx => hsubZ x (Or.inl (Finset.mem_coe.1 hx))
  have hZ3 : ↑Z3 ⊆ A := fun x hx => hsubZ x (Or.inr (Or.inl (Finset.mem_coe.1 hx)))
  have h0A : (0 : Ordinal.{0}) ∈ A := hsubZ 0 (Or.inr (Or.inr (Or.inl rfl)))
  have hvA : v ∈ A := hW (by simp)
  have hvzA : v + z ∈ A := hW (by simp)
  obtain ⟨hzA, hzTB, pz⟩ := b3 A f hW3 hZ3 C
  have hB := h.img_bases C
  have hX'TB : X' ∈ TB ρ (f ρ) := gnI_TB h C hX'T (fun p hp => hsubZ p (by simp [hp]))
  obtain ⟨wz1, wz2⟩ := pi_opowZ C.ups h.ρU hB hzTB hz1
  obtain ⟨sX1, sX2⟩ := pi_add hB hX'TB wz1
  rw [wz2] at sX2
  obtain ⟨-, ev2⟩ := pi_opowZ C.ups h.ρU hB sX1 hX1
  rw [ev2, sX2]
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  have hπX1 : pi (f ρ) ρ X' + ω ^ pi (f ρ) ρ z < Om1 := by rw [← sX2]; exact vz_pi_lt_Om1 hB sX1 hX1
  have hπXT : pi (f ρ) ρ X' + ω ^ pi (f ρ) ρ z ∈ Tset (f ρ) := by
    rw [← sX2]; exact (pi_bijOn hB).1.mapsTo sX1
  have hfE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  by_cases hU : UpsPt (f v)
  · -- `f(v)` a `υ`-point: the value `π(v) ∈ T^{f(ρ)} ∩ Ω₁` lies below it
    have hT' : ω ^ (pi (f ρ) ρ X' + ω ^ pi (f ρ) ρ z) ∈ Tset (f ρ) := by
      rw [← sX2, ← ev2]; exact (pi_bijOn hB).1.mapsTo (pi_opowZ C.ups h.ρU hB sX1 hX1).1
    have hT1 : ω ^ (pi (f ρ) ρ X' + ω ^ pi (f ρ) ρ z) < Om1 := by
      rw [← sX2, ← ev2]; exact vz_pi_lt_Om1 hB (pi_opowZ C.ups h.ρU hB sX1 hX1).1 hv1
    exact (gn_lt_ups hfE hfρ1 hT' hT1 hU hfρv).le
  obtain ⟨a, ha0, hfa, hdiv⟩ := gn_src_img h C hsrc hvA hzA hvzA hzv.le hz0 h0A hU
  rw [hfa]
  refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
  have hπz : ω ^ pi (f ρ) ρ z ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 pz
  by_cases hX'0 : X' = 0
  · have : pi (f ρ) ρ X' = 0 := by rw [hX'0]; exact pi_lt hB hfE.pos
    rw [this, zero_add]
    exact hπz.trans (Ordinal.le_of_dvd ha0 hdiv)
  obtain ⟨hm2, hm2'⟩ := hm0 hX'0
  obtain ⟨hρv', hzv', hv'v⟩ := hX'v' hX'0
  have hv'A : ω ^ X' ∈ A := mem_A hm2 hW0 hZ0
  have hv'zA : ω ^ X' + z ∈ A := hW0 (Finset.mem_coe.2 hm2')
  obtain ⟨t2, p2⟩ := b0 A f hW0 hZ0 C hX'0
  obtain ⟨-, e2⟩ := pi_opowZ C.ups h.ρU hB hX'TB hX'1
  rw [e2] at p2
  obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hv'A (indec_opow _))
  have hbc : pi (f ρ) ρ X' ≤ c := by
    rw [hc] at p2; exact (opow_le_opow_iff_right one_lt_omega0).1 p2
  have hca : c < a := by
    have := C.mono hv'A hvA hv'v
    rw [hc, hfa] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : f ρ ≤ f (ω ^ X') := (C.mono.le_iff_le C.rho hv'A).2 hρv'
    rw [hc, h0, opow_zero] at h1
    exact absurd (one_lt_omega0.trans (omega0_lt_inE hfE)) (not_lt.2 h1)
  have hcdiv : ω ^ f z ∣ c ∨ (InE c ∧ c < ω ^ f z) := by
    by_cases hU' : UpsPt (f (ω ^ X'))
    · have hcE : InE c := by
        have := upsPt_inE hU'
        rw [hc] at this
        exact (inE_opow_iff c).1 this
      rcases le_or_gt (f z) c with hzc | hcz
      · exact Or.inl (opow_dvd_of_inE hcE hzc)
      · exact Or.inr ⟨hcE, by
          rw [← show ω ^ c = c from hcE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hcz⟩
    · have hρv'' : ρ < ω ^ X' := by
        rcases hρv'.lt_or_eq with hlt | heq
        · exact hlt
        · exfalso; rw [← heq] at hU'; exact hU' C.ups
      have hsrc' : le1 (ω ^ X') (ω ^ X' + z) :=
        gn_src h hX'0 hz0 hd hzv' hρv'' (hδI.add_lt (hv'v.trans hvδ) (hzv.trans hvδ)).le
      obtain ⟨c', -, hfc', hdc'⟩ := gn_src_img h C hsrc' hv'A hzA hv'zA hzv' hz0 h0A hU'
      have hcc : c' = c := opow_inj (hfc'.symm.trans hc)
      exact Or.inl (hcc ▸ hdc')
  rcases hcdiv with hcd | ⟨hcE, hcz⟩
  · calc pi (f ρ) ρ X' + ω ^ pi (f ρ) ρ z ≤ c + ω ^ f z := add_le_add hbc hπz
      _ ≤ a := dvd_next hdiv hcd hca
  · calc pi (f ρ) ρ X' + ω ^ pi (f ρ) ρ z ≤ c + ω ^ f z := add_le_add hbc hπz
      _ = ω ^ f z := add_of_omega0_opow_le (by rw [← show ω ^ c = c from hcE] at hcz ⊢; exact hcz) le_rfl
      _ ≤ a := Ordinal.le_of_dvd ha0 hdiv

/-- **THE GENERIC STEP**: if every value below `B` lies in `Tᵖ ∩ Ω₁` and every `ε`-number `e ∈ [ρ, B)` has Lemma IMG
once every value below `e` has it, then every value below `B` has Lemma IMG. -/
theorem gnImg_of_eps {B : Ordinal.{0}} (hB : ∀ v, v < B → v ∈ Tset ρ ∧ v < Om1)
    (hE : ∀ e, InE e → ρ ≤ e → e < B → (∀ u, u < e → GnI ρ δ u) → GnI ρ δ e) : ∀ v, v < B → GnI ρ δ v := by
  have hρE := h.ρE
  have hρr : ω ^ ρ = ρ := hρE
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  obtain ⟨hvT, hv1⟩ := hB v hv
  rcases lt_or_ge v ρ with hvρ | hρv
  · exact gnI_small h hvρ
  by_cases hI : Indec v
  · by_cases hvE : InE v
    · exact hE v hvE hρv hv (fun u hu => IH u hu (hu.trans hv))
    obtain ⟨X, rfl⟩ := indec_eq_opow hI
    have hXv : X < ω ^ X :=
      lt_of_le_of_ne (right_le_opow _ one_lt_omega0) (fun e => hvE ((inE_opow_iff X).2 e.symm))
    have hρX : ρ ≤ X := by
      have h1 : ω ^ ρ ≤ ω ^ X := by rw [hρr]; exact hρv
      exact (opow_le_opow_iff_right one_lt_omega0).1 h1
    have hX0 : X ≠ 0 := (lt_of_lt_of_le hρE.pos hρX).ne'
    have hρv' : ρ < ω ^ X := lt_of_le_of_lt hρX hXv
    obtain ⟨X', hgs, hdvd, hX'X⟩ := lg_split hX0
    have hX'v : X' < ω ^ X := hX'X.trans hXv
    have hw'v : ω ^ X' < ω ^ X := (opow_lt_opow_iff_right one_lt_omega0).2 hX'X
    have hw'B : ω ^ X' < B := hw'v.trans hv
    have hw'I : GnI ρ δ (ω ^ X') := IH _ hw'v hw'B
    have hzX : lg X ≤ X := lg_le hX0
    have hzv : lg X < ω ^ X := lt_of_le_of_lt hzX hXv
    obtain ⟨hXT, hX1⟩ := hB X (hXv.trans hv)
    obtain ⟨hX'T, -⟩ := hB X' (hX'v.trans hv)
    rcases eq_or_ne (lg X) 0 with hz0 | hz0
    · have e : X = X' + 1 := by rw [hgs, hz0, opow_zero]
      have hX1' : X' + 1 < Om1 := by rw [← e]; exact hX1
      rw [e] at hv hvT hv1 hρv ⊢
      exact gnI_succ h hw'I hX'T hX1' hρv hvT hv1
    obtain ⟨hzT, -⟩ := hB (lg X) (hzv.trans hv)
    have e : X = X' + ω ^ lg X := hgs
    have hzI := IH (lg X) hzv (hzv.trans hv)
    have hwI : X' ≠ 0 → GnI ρ δ (ω ^ X') := fun _ => hw'I
    rw [e] at hv hvT hv1 hρv' hXv hX1 ⊢
    exact gnI_lim h hz0 hdvd hzI hwI hX'T hzT hX1 hXv hρv' hvT hv1
  · have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
    subst hsum
    exact gnI_add h (IH u1 hu1 (hu1.trans hv)) (IH u2 hu2 (hu2.trans hv)) hu1 hu2 hρv hvT hv1

/-- **Every value below `Γ_{ρ+1}`** (`LvGK.imgLvG` and `LvGT.pi`). -/
theorem gnI_lowG {v : Ordinal.{0}} (hv : v < lgG ρ) : GnI ρ δ v := by
  classical
  obtain ⟨n, hn⟩ := lt_lgG_iff.1 hv
  obtain ⟨⟨W, Z, s, w, cb, cs', e, m, b⟩, -⟩ := LvGK.imgLvG h n v hn
  obtain ⟨hvT, hv1⟩ := gl_T_of_lt_G h.ρE h.ρ1 hv
  refine gnI_mk h w m hvT hv1 (fun A f hW hZ C => ?_)
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hs : LvGT.CBt s (f ρ) := LvG.cbt_img C cb (fun c hc => hZ' (Finset.mem_coe.2 (cs' c hc)))
  obtain ⟨-, hps⟩ := LvGT.pi C.ups h.ρU (h.img_bases C) s hs
  rw [← e, hps, e]
  exact b A f hW hZ' C

/-- **The value `Γ_{ρ+1}`** (`LgK.lgTopPkg`, `Gm.mg_lgG_pi`). -/
theorem gnI_G : GnI ρ δ (lgG ρ) := by
  classical
  obtain ⟨-, -, W, Z, w, m, b⟩ := LgK.lgTopPkg h
  obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts h.ρE h.ρ1
  refine gnI_mk h w m hGT hG1 (fun A f hW hZ C => ?_)
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  rw [(mg_lgG_pi (h.img_bases C)).2]
  exact b A f hW hZ' C

/-- **LEMMA IMG FOR EVERY VALUE BELOW `ε_{Γ_{ρ+1}+1}`.** -/
theorem gnImg_G : ∀ v, v < eN (lgG ρ) → GnI ρ δ v := by
  refine gnImg_of_eps h (fun v hv => gn_eNG_T h.ρE h.ρ1 hv) (fun e he _ heB _ => ?_)
  rcases lt_trichotomy e (lgG ρ) with hlt | rfl | hgt
  · exact gnI_lowG h hlt
  · exact gnI_G h
  · exact absurd (eN_le hgt he) (not_le.2 heB)

/-- **Lemma IMG (gated) for a function with Lemma EXACT** whose value at `ρ` has Lemma IMG in `π`-form. -/
theorem gnPkg_of_GnI {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hI : GnI ρ δ (T ρ)) (hex : GjEx g C T) : GhPkg g ρ δ T := by
  classical
  obtain ⟨W, Z, w, m, -, -, -, b⟩ := hI
  have w' := w.union (Gj.wz_consts (δ := δ) hC)
  rw [Finset.union_empty] at w'
  refine ⟨W, Z ∪ C, w', ?_, fun A f hW hZ Cx => ?_⟩
  · rcases Finset.mem_union.1 m with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hCA : ∀ c ∈ C, c ∈ A := fun c hc => hZ (by simp [hc])
  have I := Cx.toImgCtx
  have hCσ : ∀ c ∈ C, c < f ρ := fun c hc => I.above c (hCA c hc) (hC c hc)
  obtain ⟨-, hpT⟩ := hex (f ρ) ρ I.ups h.ρU (h.img_bases I) (Cx.lt hgρ) hCσ
  rw [← hpT]
  exact b A f hW hZ' I

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `ε_{Γ_{ρ+1}+1}`**: if `T` has Lemma EXACT above the gate
`g < ρ` with constants `C < ρ`, and `T(ρ) < ε_{Γ_{ρ+1}+1}`, then every covering copy `f` that keeps `g` has
`T(f ρ) ≤ f(T ρ)`. -/
theorem gnPkg_of_ex {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hgρ : g < ρ)
    (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < eN (lgG ρ)) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (gnImg_G h _ hT) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Gn
