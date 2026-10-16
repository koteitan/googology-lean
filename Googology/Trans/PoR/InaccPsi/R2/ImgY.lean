import Googology.Trans.PoR.InaccPsi.R2.EpsY

/-!
# Lemma IMG for every value below `ε_{x+2}`

The project's Lemma IMG ("a covering copy of an offset term is not below the same term at the copied
base") for every ordinal `v < ε_{ρ+2}`, with a term of `OTY`, by induction on `v` as `RstK.img_val` of
`R2.TopO` (which covers `v < ε_{ρ+1}` with terms of `OT`): a value below `ε_{ρ+1}` is `img_val`; a sum is
copied by a sum; `ε_{ρ+1} ≤₁ ε_{ρ+1}·2` (`pkg_eN`); an atom `v = ω^{ε+β}` with `β = β'' + ω^z`, `z > 0`, goes
through the source atoms `v ≤₁ v + z` and `ω^{ε+β''} ≤₁ ω^{ε+β''} + z` (or `ε ≤₁ ε + z`) of `R₁⁺` ([W07b]
Theorem 2.2) inside the block (`RstK.lowδ`); below `ρ` a copy of an atom is a `υ`-point or has its `R₁⁺`
reach, so the copied exponents are multiples of `ω^{f(z)}` (`RstK.copy_atom`), and a term `tw` for `ω^z`
has `tw(f(ρ)) ≤ ω^{f(z)}` (for `z < ε` the term of `R2.TopO`, for `z = ε + ζ` the atom `ω^{ε+ζ}` with
`f(z) = f(ε) + f(ζ) ≥ ε_{f(ρ)+1} + ζ(f(ρ))`).

* `ImgY`, `img_cbY`, `dvdE`, `RstK.eNN_lt_δ`, `RstK.src_atomY`;
* `RstK.imgY` (**Lemma IMG below `ε_{ρ+2}`**), `RstK.pkgY` (the IMG package of a term of `OTY` with value
  `≥ 1`); `exp_lt_atom`, `RstK.src_eps` (the source atom `ε ≤₁ ε + z`, `0 < z ≤ ε`), `RstK.pkg_eNN`
  (the IMG package of `ε_{x+2}`).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT OTY

/-- **The IMG statement for one value** `v` with a term `s` of `OTY` (`s(ρ) = v`, constants in `Z`). -/
def ImgY (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : OTY) : Prop :=
  WZ ρ δ W Z ∧ CBY s ρ ∧ (∀ c ∈ csY s, c ∈ Z) ∧ ev2 s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      ev2 s (f ρ) ≤ f v

theorem img_cbY {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : OTY} (hs : CBY s ρ) (hA : ∀ c ∈ csY s, c ∈ A) : CBY s (f ρ) :=
  (cbY_iff s _).2 (fun c hc => C.above c (hA c hc) ((cbY_iff s ρ).1 hs c hc))

/-- `ω^z ∣ ε + β` when `ω^z ∣ β ≠ 0` (`ε` an `ε`-number). -/
theorem dvdE {e z β : Ordinal.{0}} (he : InE e) (hβ0 : β ≠ 0) (hd : ω ^ z ∣ β) : ω ^ z ∣ e + β := by
  rcases le_or_gt z e with hze | hez
  · exact dvd_add (opow_dvd_of_inE he hze) hd
  · have he' : ω ^ e = e := he
    have h1 : e < ω ^ z := by
      nth_rewrite 1 [← he']; exact (opow_lt_opow_iff_right one_lt_omega0).2 hez
    rw [add_of_omega0_opow_le h1 (le_of_dvd hβ0 hd)]
    exact hd

/-- An atom `ω^{ε+β}` with `0 < β`, below `ε_{ρ+2}`, is not an `ε`-number: `ε + β < ω^{ε+β}`. -/
theorem exp_lt_atom {x β : Ordinal.{0}} (hβ0 : β ≠ 0) (hv : ω ^ (eN x + β) < eN (eN x)) :
    eN x + β < ω ^ (eN x + β) := by
  rcases (right_le_opow (eN x + β) one_lt_omega0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hE : InE (eN x + β) := h.symm
    have h1 : eN x < eN x + β := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)
    exact absurd ((eN_le h1 hE).trans (right_le_opow _ one_lt_omega0)) (not_le.2 hv)

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- `ε_{ρ+2} < δ`. -/
theorem eNN_lt_δ : eN (eN ρ) < δ :=
  (eNN_lt_ups h.ρU h.ρ1 τ h.ρτ h.τU).trans h.τδ

/-- The source atom `ω^{ε+β} ≤₁ ω^{ε+β} + z` inside the block of `ρ` (`ω^z ∣ β ≠ 0`, `z ≤ ω^{ε+β}`, the
atom below `ε_{ρ+2}`). -/
theorem src_atomY {z β : Ordinal.{0}} (hz0 : z ≠ 0) (hβ0 : β ≠ 0) (hd : ω ^ z ∣ β)
    (hzv : z ≤ ω ^ (eN ρ + β)) (hv : ω ^ (eN ρ + β) < eN (eN ρ)) (hzδ : z < δ) :
    le1 (ω ^ (eN ρ + β)) (ω ^ (eN ρ + β) + z) := by
  have hvδ := hv.trans h.eNN_lt_δ
  have hρv : ρ < ω ^ (eN ρ + β) := (lt_eN ρ).trans_le (eN_le_atom ρ β)
  have hne : eN ρ + β ≠ 0 := (lt_of_lt_of_le (eN_E ρ).pos le_self_add).ne'
  refine (h.lowδ _ _ hρv ((inE_indec h.δE).add_lt hvδ hzδ).le).2 ?_
  exact (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzv).2
    ⟨eN ρ + β, hne, rfl, (le_lg_iff hne z).2 (dvdE (eN_E ρ) hβ0 hd)⟩

/-- The source atom `ε ≤₁ ε + z` (`0 < z ≤ ε`). -/
theorem src_eps {z : Ordinal.{0}} (hz0 : z ≠ 0) (hze : z ≤ eN ρ) : le1 (eN ρ) (eN ρ + z) := by
  have heδ := h.eN_lt_δ
  have he' : ω ^ eN ρ = eN ρ := eN_E ρ
  have hne : eN ρ ≠ 0 := (eN_E ρ).pos.ne'
  refine (h.lowδ _ _ (lt_eN ρ) ((inE_indec h.δE).add_lt heδ (lt_of_le_of_lt hze heδ)).le).2 ?_
  refine (le1R_thm22 (pos_iff_ne_zero.2 hz0) hze).2 ⟨eN ρ, hne, he'.symm, ?_⟩
  exact (le_lg_iff hne z).2 (opow_dvd_of_inE (eN_E ρ) hze)

/-- **Lemma IMG below `ε_{ρ+2}`**: every `v < ε_{ρ+2}` has a term `s` of `OTY` and witness sets such that
every covering copy `f` of a set containing them has `s(f(ρ)) ≤ f(v)`; for an indecomposable
`v ≥ ε_{ρ+1}` the term is an atom `ew s'`. -/
theorem imgY : ∀ v, v < eN (eN ρ) → ∃ W Z s, ImgY ρ δ v W Z s ∧
    (eN ρ ≤ v → Indec v → ∃ s', s = ew s') := by
  classical
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρe : ρ < eN ρ := lt_eN ρ
  have heNδ := h.eNN_lt_δ
  have hvδ : v < δ := hv.trans heNδ
  have he' : ω ^ eN ρ = eN ρ := eN_E ρ
  rcases lt_or_ge v (eN ρ) with hve | hev
  · -- below `ε_{ρ+1}`: Lemma IMG of `R2.TopO`
    obtain ⟨W, Z, t, w, c, s, e, m, b⟩ := h.img_val v hve
    exact ⟨W, Z, kk t, ⟨w, c, s, e, m, b⟩, fun h1 => absurd h1 (not_le.2 hve)⟩
  have hρv : ρ ≤ v := hρe.le.trans hev
  by_cases hI : Indec v
  · obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have hL : eN ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [he']; exact hev)
    set β := L - eN ρ with hβdef
    have hLβ : eN ρ + β = L := Ordinal.add_sub_cancel_of_le hL
    rw [← hLβ] at hv hvδ hρv IH ⊢
    -- the atom `v = ω^{ε+β}`
    suffices H : ∃ W Z s', ImgY ρ δ (ω ^ (eN ρ + β)) W Z (ew s') by
      obtain ⟨W, Z, s', hY⟩ := H
      exact ⟨W, Z, ew s', hY, fun _ _ => ⟨s', rfl⟩⟩
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · -- `v = ε`
      obtain ⟨-, -, W, Z, w, m, i⟩ := h.pkg_eN
      have hv0 : ω ^ (eN ρ + β) = eN ρ := by rw [hβ0, add_zero, he']
      refine ⟨W, insert 0 Z, kk (k 0), ⟨w.insZ hρE.pos, hρE.pos, ?_, ?_, ?_, ?_⟩⟩
      · intro c hc; simp [csY, cs] at hc; simp [hc]
      · simp [hβ0]
      · rw [hv0]
        rcases Finset.mem_union.1 m with hm | hm
        · exact Finset.mem_union_left _ hm
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hm)
      · intro A f hW hZ C
        have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        rw [hv0, ev2_ew, ev2_kk, ev_k, add_zero]
        have hfE : ω ^ eN (f ρ) = eN (f ρ) := eN_E (f ρ)
        rw [hfE]
        exact i A f hW hZ' C
    set v := ω ^ (eN ρ + β) with hvdef
    have hρv' : ρ < v := hρe.trans_le (eN_le_atom ρ β)
    have hβv : eN ρ + β < v := exp_lt_atom hβ0 hv
    obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
    have hzβ : lg β ≤ β := lg_le hβ0
    set v'' := ω ^ (eN ρ + β'') with hv''def
    have hv''v : v'' < v :=
      (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
    have hρv'' : ρ < v'' := hρe.trans_le (eN_le_atom ρ β'')
    have hev'' : eN ρ ≤ v'' := eN_le_atom ρ β''
    obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, hat1⟩ := IH v'' hv''v (hv''v.trans hv)
    obtain ⟨s'', rfl⟩ := hat1 hev'' (indec_opow _)
    have e1' : ev2 s'' ρ = β'' := by
      have := e1; rw [ev2_ew] at this
      exact (add_left_cancel_iff).1 (opow_inj this)
    rcases eq_or_ne (lg β) 0 with hz0 | hz0
    · -- `β = β'' + 1`
      have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
      have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
      refine ⟨insert v W1, insert 1 Z1, ad s'' (kk (k 1)),
        ⟨(w1.insZ h1ρ).insW hρv'.le hvδ (Or.inl (indec_opow _)), ⟨c1, h1ρ⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩⟩
      · intro c hc
        simp only [csY, cs, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact Finset.mem_insert_of_mem (cs1 c hc)
        · exact Finset.mem_insert_self _ _
      · rw [ev2_ew, ev2_ad, ev2_kk, ev_k, e1', ← hβs]
      intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : v ∈ A := hW (by simp)
      have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
      have hb := b1 A f hW1 hZ1 C
      rw [ev2_ew] at hb
      have hlt : f v'' < f v := C.mono h1A hvA hv''v
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
      rw [hc] at hlt
      rw [ev2_ew, ev2_ad, ev2_kk, ev_k, hc, ← add_assoc]
      have h3 : eN (f ρ) + ev2 s'' (f ρ) < c :=
        (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
      exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
    -- `β = β'' + ω^z`, `z > 0`
    set z := lg β with hzdef
    have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
    have hzv : z < v := lt_of_le_of_lt (hzβ.trans le_add_self) hβv
    have hzδ : z < δ := hzv.trans hvδ
    have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
    -- the witness sets for `z` and the term `tw` for `ω^z`
    obtain ⟨W3, Z3, W4, Z4, tw, w3, w4, hzm, ctw, cstw, etw, btw⟩ :
        ∃ (W3 Z3 W4 Z4 : Finset Ordinal.{0}) (tw : OTY), WZ ρ δ W3 Z3 ∧ WZ ρ δ W4 Z4 ∧ z ∈ W3 ∪ Z3 ∧ CBY tw ρ ∧
          (∀ c ∈ csY tw, c ∈ Z4) ∧ ev2 tw ρ = ω ^ z ∧
          ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑(W3 ∪ W4) ⊆ A →
            ↑(Z3 ∪ Z4) ⊆ A → ImgCtx ρ A f → ev2 tw (f ρ) ≤ ω ^ f z := by
      rcases lt_or_ge z (eN ρ) with hze | hez
      · obtain ⟨W3, Z3, tz, h3⟩ := h.img_val z hze
        have htw : ∃ W4 Z4 tw, TwW ρ δ z W3 Z3 W4 Z4 tw := by
          rcases lt_or_ge z ρ with hzρ | hρz
          · exact ⟨_, _, _, h.tw_small h3 hzρ⟩
          · have hζe : z - ρ < eN ρ := lt_of_le_of_lt (sub_le_self _ ρ) hze
            obtain ⟨W4, Z4, tζ, h4⟩ := h.img_val (z - ρ) hζe
            exact ⟨_, _, _, h.tw_big h3 h4 (Ordinal.add_sub_cancel_of_le hρz)⟩
        obtain ⟨W4, Z4, tw, w4, c4, s4, e4, b4⟩ := htw
        exact ⟨W3, Z3, W4, Z4, kk tw, h3.1, w4, h3.2.2.2.2.1, c4, s4, e4, b4⟩
      · set ζ := z - eN ρ with hζdef
        have hzζ : eN ρ + ζ = z := Ordinal.add_sub_cancel_of_le hez
        have hζz : ζ ≤ z := by rw [← hzζ]; exact le_add_self
        obtain ⟨W3, Z3, sz, ⟨w3, -, -, -, m3, -⟩, -⟩ := IH z hzv (hzv.trans hv)
        obtain ⟨W5, Z5, sζ, ⟨w5, c5, cs5, e5, m5, b5⟩, -⟩ :=
          IH ζ (lt_of_le_of_lt hζz hzv) ((lt_of_le_of_lt hζz hzv).trans hv)
        obtain ⟨-, -, We, Ze, we, me, ie⟩ := h.pkg_eN
        refine ⟨W3, Z3, W5 ∪ We, Z5 ∪ Ze, ew sζ, w3, w5.union we, m3, c5,
          fun c hc => Finset.mem_union_left _ (cs5 c hc), by rw [ev2_ew, e5, hzζ], ?_⟩
        intro A f hW hZ C
        have hW3 : ↑W3 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
        have hZ3 : ↑Z3 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hW5 : ↑W5 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
        have hZ5 : ↑Z5 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hWe : ↑We ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
        have hZe : ↑Ze ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hzA : z ∈ A := mem_A m3 hW3 hZ3
        have hζA : ζ ∈ A := mem_A m5 hW5 hZ5
        have heA : eN ρ ∈ A := mem_A me hWe hZe
        have hadd := C.add (eN ρ) heA ζ hζA z hzA hzζ
        rw [ev2_ew]
        refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
        rw [← hadd]
        exact add_le_add (ie A f hWe hZe C) (b5 A f hW5 hZ5 C)
    -- the source atom of `v`
    have hsrc : le1 v (v + z) := h.src_atomY hz0 hβ0 hdβ hzv.le hv hzδ
    have hvzδ : v + z < δ := hδI.add_lt hvδ hzδ
    have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
    have hvvz : v < v + z := lt_add_of_pos_right v hz0'
    have hev : eN ρ < v := lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)) hβv.le
    have hzv'' : β'' ≠ 0 → z < v'' := by
      intro hb0
      have hzb : z ≤ β'' := (right_le_opow z one_lt_omega0).trans (le_of_dvd hb0 hdvd)
      exact lt_of_le_of_lt (hzb.trans le_add_self) (exp_lt_atom hb0 (hv''v.trans hv))
    rcases eq_or_ne β'' 0 with hb0 | hb0
    · -- `β = ω^z`
      have hβz : β = ω ^ z := by rw [hgs, hb0, zero_add]
      obtain ⟨-, -, We, Ze, we, me, ie⟩ := h.pkg_eN
      set W0 := W3 ∪ W4 ∪ We with hW0
      set Z0 := insert 0 (Z3 ∪ Z4 ∪ Ze) with hZ0
      have wz0 : WZ ρ δ W0 Z0 := ((w3.union w4).union we).insZ hρE.pos
      have hsub : ∀ x, x ∈ W3 ∪ Z3 ∨ x ∈ We ∪ Ze → x ∈ W0 ∪ Z0 := by
        intro x hx
        rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;>
          simp [hW0, hZ0, hx]
      have hzm0 : z ∈ W0 ∪ Z0 := hsub _ (Or.inl hzm)
      have hem0 : eN ρ ∈ W0 ∪ Z0 := hsub _ (Or.inr me)
      set Wx := if z ≤ eN ρ then insert (eN ρ + z) W0 else W0 with hWx
      have hW0x : W0 ⊆ Wx := by
        rw [hWx]; split_ifs
        · exact Finset.subset_insert _ _
        · exact subset_refl _
      have wzx : WZ ρ δ Wx Z0 := by
        rw [hWx]; split_ifs with hze
        · exact wz0.insW ((lt_eN ρ).le.trans le_self_add)
            (hδI.add_lt h.eN_lt_δ hzδ)
            (Or.inr ⟨eN ρ, hem0, z, hzm0, lt_add_of_pos_right _ hz0',
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
      refine ⟨insert (v + z) (insert v Wx), Z0, tw, ⟨wzf, ctw, ?_, by rw [ev2_ew, etw, ← hβz],
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩⟩
      · intro c hc; exact Finset.mem_insert_of_mem (by simp [cstw c hc])
      intro A f hW hZ C
      have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hW0x (Finset.mem_coe.1 hx)))))
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
        hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW34 : ↑(W3 ∪ W4) ⊆ A := hsW (by
        intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hW0, hx])
      have hZ34 : ↑(Z3 ∪ Z4) ⊆ A := hsZ (by
        intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hZ0, hx])
      have hWe : ↑We ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hZe : ↑Ze ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
      have hvA : v ∈ A := hW (by simp)
      have hvzA : v + z ∈ A := hW (by simp)
      have hzA : z ∈ A := mem_A hzm0 hW0A hZ
      have heA : eN ρ ∈ A := mem_A hem0 hW0A hZ
      have hbtw : ev2 tw (f ρ) ≤ ω ^ f z := btw A f hW34 hZ34 C
      have hfe : eN (f ρ) ≤ f (eN ρ) := ie A f hWe hZe C
      have hfev : f (eN ρ) < f v := C.mono heA hvA hev
      have hcs : ∀ c ∈ csY (ew tw), c ∈ A := fun c hc => hZ34 (by simp [cstw c hc])
      have hCB : CBY (ew tw) (f ρ) := img_cbY C ctw hcs
      by_cases hU : UpsPt (f v)
      · have hE := upsPt_inE hU
        have h1 : eN (eN (f ρ)) ≤ f v := eN_le (lt_of_le_of_lt hfe hfev) hE
        exact (ev2_lt (ew tw) hCB).le.trans h1
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      rw [ev2_ew, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      by_cases hze : z ≤ eN ρ
      · have hezA : eN ρ + z ∈ A := by
          have : eN ρ + z ∈ Wx := by rw [hWx, if_pos hze]; exact Finset.mem_insert_self _ _
          exact hW (by simp [this])
        obtain ⟨c, hc, hdc⟩ := h.copy_atom C heA hzA hezA hz0 hze h0A (h.src_eps hz0 hze)
        have hfE : ω ^ eN (f ρ) = eN (f ρ) := eN_E (f ρ)
        have hcl : eN (f ρ) ≤ c := by
          rw [hc, ← hfE] at hfe; exact (opow_le_opow_iff_right one_lt_omega0).1 hfe
        have hca : c < a := by
          have := hfev; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
        exact (add_le_add hcl hbtw).trans (dvd_next hda hdc hca)
      · push Not at hze
        have hfz : f (eN ρ) < f z := C.mono heA hzA hze
        have h1 : eN (f ρ) < ω ^ f z :=
          lt_of_le_of_lt hfe (hfz.trans_le (right_le_opow _ one_lt_omega0))
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, opow_zero] at ha
          have : (1 : Ordinal.{0}) < f v := lt_of_le_of_lt (one_le_iff_pos.2 (eN_E _).pos)
            (lt_of_le_of_lt hfe hfev)
          rw [ha] at this; exact lt_irrefl _ this
        have h2 : eN (f ρ) + ev2 tw (f ρ) ≤ ω ^ f z := by
          rcases hbtw.lt_or_eq with hlt | heq
          · exact (isPrincipal_add_omega0_opow _ h1 hlt).le
          · rw [heq, add_omega0_opow h1]
        exact h2.trans (le_of_dvd ha0 hda)
    · -- `β'' ≠ 0`: the source atom of `v''` too
      have hzvb := hzv'' hb0
      have hsrc'' : le1 v'' (v'' + z) :=
        h.src_atomY hz0 hb0 hdvd hzvb.le (hv''v.trans hv) hzδ
      set W0 := W1 ∪ W3 ∪ W4 with hW0
      set Z0 := insert 0 (Z1 ∪ Z3 ∪ Z4) with hZ0
      have wz0 : WZ ρ δ W0 Z0 := ((w1.union w3).union w4).insZ hρE.pos
      have hsub : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W3 ∪ Z3 → x ∈ W0 ∪ Z0 := by
        intro x hx
        rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;>
          simp [hW0, hZ0, hx]
      have hv''m : v'' ∈ W0 ∪ Z0 := hsub _ (Or.inl m1)
      have hzm0 : z ∈ W0 ∪ Z0 := hsub _ (Or.inr hzm)
      have hv''zδ : v'' + z < δ := hδI.add_lt (hv''v.trans hvδ) hzδ
      have wz1 : WZ ρ δ (insert (v'' + z) W0) Z0 :=
        wz0.insW (hρv''.le.trans le_self_add) hv''zδ
          (Or.inr ⟨v'', hv''m, z, hzm0, lt_add_of_pos_right _ hz0',
            lt_of_lt_of_le hzvb le_self_add, rfl⟩)
      have hmx : ∀ x ∈ W0 ∪ Z0, x ∈ insert v (insert (v'' + z) W0) ∪ Z0 := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
        · exact Finset.mem_union_right _ hx
      have wzf : WZ ρ δ (insert (v + z) (insert v (insert (v'' + z) W0))) Z0 :=
        (wz1.insW hρv'.le hvδ (Or.inl (indec_opow _))).insW (hρv'.le.trans le_self_add) hvzδ
          (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hmx z hzm0, hvvz,
            hzvz, rfl⟩)
      refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, ad s'' tw, ⟨wzf, ⟨c1, ctw⟩, ?_,
        by rw [ev2_ew, ev2_ad, e1', etw, ← hgs],
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩⟩
      · intro c hc
        simp only [csY, List.mem_append] at hc
        rcases hc with hc | hc
        · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
        · exact Finset.mem_insert_of_mem (by simp [cstw c hc])
      intro A f hW hZ C
      have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))))
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
        hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW34 : ↑(W3 ∪ W4) ⊆ A := hsW (by
        intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hW0, hx])
      have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ34 : ↑(Z3 ∪ Z4) ⊆ A := hsZ (by
        intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hZ0, hx])
      have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
      have hvA : v ∈ A := hW (by simp)
      have hvzA : v + z ∈ A := hW (by simp)
      have hv''zA : v'' + z ∈ A := hW (by simp)
      have hzA : z ∈ A := mem_A hzm0 hW0A hZ
      have hv''A : v'' ∈ A := mem_A hv''m hW0A hZ
      have hb'' := b1 A f hW1 hZ1 C
      rw [ev2_ew] at hb''
      have hbtw : ev2 tw (f ρ) ≤ ω ^ f z := btw A f hW34 hZ34 C
      have hcs : ∀ c ∈ csY (ew (ad s'' tw)), c ∈ A := by
        intro c hc
        simp only [csY, List.mem_append] at hc
        rcases hc with hc | hc
        · exact hZ1 (Finset.mem_coe.2 (cs1 c hc))
        · exact hZ34 (by simp [cstw c hc])
      have hCB : CBY (ew (ad s'' tw)) (f ρ) := img_cbY C ⟨c1, ctw⟩ hcs
      obtain ⟨c, hc, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzvb.le h0A hsrc''
      have hbc : eN (f ρ) + ev2 s'' (f ρ) ≤ c := by
        rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
      have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
      by_cases hU : UpsPt (f v)
      · have hE := upsPt_inE hU
        have heF : eN (f ρ) < f v :=
          lt_of_le_of_lt ((eN_le_atom _ _).trans hb'') hfv''v
        exact (ev2_lt _ hCB).le.trans (eN_le heF hE)
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      have hca : c < a := by
        have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      rw [ev2_ew, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      rw [ev2_ad, ← add_assoc]
      exact (add_le_add hbc hbtw).trans (dvd_next hda hdc hca)
  · -- a decomposable value: a sum
    have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le (eN_E ρ).pos hev).ne'
    obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, -⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨W2, Z2, s2, ⟨w2, c2, cs2, e2, m2, b2⟩, -⟩ := IH u2 hu2 (hu2.trans hv)
    subst hsum
    have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
      intro x hx
      rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
    refine ⟨insert (u1 + u2) (W1 ∪ W2), Z1 ∪ Z2, ad s1 s2,
      ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2,
        rfl⟩), ⟨c1, c2⟩, ?_, by simp [e1, e2], by simp, ?_⟩, fun _ hI' => absurd hI' hI⟩
    · intro c hc
      simp only [csY, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_union_left _ (cs1 c hc)
      · exact Finset.mem_union_right _ (cs2 c hc)
    · intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : u1 + u2 ∈ A := hW (by simp)
      have := C.add u1 (mem_A m1 hW1 hZ1) u2 (mem_A m2 hW2 hZ2) _ hvA rfl
      rw [ev2_ad, ← this]
      exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- **The IMG package of `ε_{x+2}`**: the atom `ε_{ρ+2} ≤₁ ε_{ρ+2}·2` of `R₁⁺` ([W07b], the remark after
Theorem 2.2) inside the block; its copy is an `ε`-number above the copy of `ε_{ρ+1}`, which is at least
`ε_{f(ρ)+1}`. -/
theorem pkg_eNN : ImgPkg ρ δ (fun x => eN (eN x)) := by
  classical
  obtain ⟨-, -, We, Ze, we, me, ie⟩ := h.pkg_eN
  set E := eN (eN ρ) with hEdef
  have hE := eN_E (eN ρ)
  have hEδ := h.eNN_lt_δ
  have hδI := inE_indec h.δE
  have hEE : E + E < δ := hδI.add_lt hEδ hEδ
  have hEpos : 0 < E := hE.pos
  have heE : eN ρ < E := lt_eN _
  have hρE : ρ < E := (lt_eN ρ).trans heE
  have w1 : WZ ρ δ (insert E We) Ze := we.insW hρE.le hEδ (Or.inl (inE_indec hE))
  have w2 : WZ ρ δ (insert (E + E) (insert E We)) Ze :=
    w1.insW (hρE.le.trans le_self_add) hEE
      (Or.inr ⟨E, Finset.mem_union_left _ (Finset.mem_insert_self _ _), E,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _), lt_add_of_pos_right _ hEpos,
        lt_add_of_pos_right _ hEpos, rfl⟩)
  refine ⟨one_le_iff_pos.2 hEpos, hEδ, insert (E + E) (insert E We), Ze, w2,
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩
  intro A f hW hZ C
  have hWe : ↑We ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have heA : eN ρ ∈ A := mem_A me hWe hZ
  have hEA : E ∈ A := hW (by simp)
  have hEEA : E + E ∈ A := hW (by simp)
  have hfe : eN (f ρ) ≤ f (eN ρ) := ie A f hWe hZ C
  have hfeE : f (eN ρ) < f E := C.mono heA hEA heE
  have hsrc : le1 E (E + E) := by
    refine (h.lowδ _ _ hρE hEE.le).2 ?_
    rw [← mul_two_eq]; exact (le1R_two_iff hEpos).2 hE
  have himg : le1 (f E) (f E + f E) := by
    have := C.cov1 _ hEA _ hEEA hsrc
    rwa [← C.add _ hEA _ hEA _ hEEA rfl] at this
  have hfE : InE (f E) := by
    by_cases hU : UpsPt (f E)
    · exact upsPt_inE hU
    · have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
      rw [← mul_two_eq] at hR
      exact (le1R_two_iff (lt_of_le_of_lt zero_le hfeE)).1 hR
  exact eN_le (lt_of_le_of_lt hfe hfeE) hfE

/-- **The IMG package of a term of `OTY`** for every value `1 ≤ v < ε_{ρ+2}`. -/
theorem pkgY {v : Ordinal.{0}} (hv1 : 1 ≤ v) (hv : v < eN (eN ρ)) :
    ∃ s : OTY, CBY s ρ ∧ ev2 s ρ = v ∧ ImgPkg ρ δ (ev2 s) := by
  obtain ⟨W, Z, s, ⟨w, c, cs, e, m, b⟩, -⟩ := h.imgY v hv
  refine ⟨s, c, e, by rw [e]; exact hv1, by rw [e]; exact hv.trans h.eNN_lt_δ, W, Z, w,
    by rw [e]; exact m, fun A f hW hZ C => ?_⟩
  rw [e]; exact b A f hW hZ C

end RstK

end Googology.Trans.PoR.InaccPsi.R2
