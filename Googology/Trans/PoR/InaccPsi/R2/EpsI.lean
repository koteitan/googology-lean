import Googology.Trans.PoR.InaccPsi.R2.EpsT
import Googology.Trans.PoR.InaccPsi.R2.ImgY

/-!
# Lemma IMG for every value below `ε_{ρ+ω}`

The project's Lemma IMG ("a covering copy of an offset term is not below the same term at the copied
base") for every ordinal `v < ε_{ρ+ω}`, with a term of `TW`, by induction on `v`.  The argument of
`RstK.imgY` (`R2.ImgY`) with the pseudo-base `e = ε_{ρ+n}` for every `n` (including `e = ρ`):

* a value below `ρ` is a constant (the copy fixes it);
* `ε_{ρ+n}` itself: `pkg_eK` (`ε_{ρ+n+1} ≤₁ ε_{ρ+n+1}·2` of `R₁⁺`, [W07b] remark after Theorem 2.2,
  inside the block; the copy is an `ε`-number above the copy of `ε_{ρ+n}`);
* an atom `v = ω^{e+β}` (`0 < β`, `e + β < ε_{ρ+n+1}`) with `β = β'' + ω^z`: for `z = 0` the copies of
  `ω^{e+β''} < v` are atoms; for `z > 0` the source atoms `v ≤₁ v + z` and `ω^{e+β''} ≤₁ ω^{e+β''} + z`
  (or `e ≤₁ e + z`) of `R₁⁺` ([W07b] Theorem 2.2) inside the block (`RstK.lowδ`); below `ρ` a copy of
  an atom is a `υ`-point or has its `R₁⁺` reach (`RstK.copy_atom`), so the copied exponents are
  multiples of `ω^{f(z)}`; the term for `ω^z` is `pw` of the term of `z`; a copy that is a `υ`-point is
  an `ε`-number above the copy of `e`, so it is `≥ ε_{f(ρ)+n+1}`, which bounds the term (uniform
  comparison `uniW_lt` between `ρ` and `f(ρ)`);
* a sum is copied by a sum.

* `ImgT`, `img_cbw`, `atw` (the atom term `ω^{ε_{x+n}+s}`), `exp_lt_atomE`, `eK_bracket_eq`,
  `RstK.eK_lt_δ`, `RstK.pkg_eK`, `RstK.src_gen`;
* `RstK.imgT` (**Lemma IMG below `ε_{ρ+ω}`**), `RstK.pkgT` (the IMG package of a term of `TW` with value
  `≥ 1`).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order TW

/-- **The IMG statement for one value** `v` with a term `s` of `TW` (`s(ρ) = v`, constants in `Z`). -/
def ImgT (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : TW) : Prop :=
  WZ ρ δ W Z ∧ CBw s ρ ∧ (∀ c ∈ csw s, c ∈ Z) ∧ val s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val s (f ρ) ≤ f v

theorem img_cbw {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : TW} (hs : CBw s ρ) (hA : ∀ c ∈ csw s, c ∈ A) : CBw s (f ρ) :=
  (cbw_iff s _).2 (fun c hc => C.above c (hA c hc) ((cbw_iff s ρ).1 hs c hc))

/-- The atom term `ω^{ε_{x+n}+s}`. -/
def atw (n : ℕ) (s : TW) : TW := pw (sm (ep n) s)

@[simp] theorem val_atw (n : ℕ) (s : TW) (x : Ordinal.{0}) : val (atw n s) x = ω ^ (eK n x + val s x) :=
  rfl

theorem CBw_atw {n : ℕ} {s : TW} {x : Ordinal.{0}} : CBw (atw n s) x ↔ CBw s x := by
  simp [atw, CBw]

theorem csw_atw (n : ℕ) (s : TW) : csw (atw n s) = csw s := by simp [atw, csw]

/-- An atom `ω^{e+β}` with `0 < β` below the next `ε`-number after the `ε`-number `e` is not an
`ε`-number: `e + β < ω^{e+β}`. -/
theorem exp_lt_atomE {e β : Ordinal.{0}} (hβ0 : β ≠ 0) (hv : e + β < eN e) : e + β < ω ^ (e + β) := by
  rcases (right_le_opow (e + β) one_lt_omega0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hE : InE (e + β) := h.symm
    have h1 : e < e + β := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)
    exact absurd (eN_le h1 hE) (not_le.2 hv)

/-- The bracket `[ε_{x+n}, ε_{x+n+1})` of a point is unique. -/
theorem eK_bracket_eq {x X : Ordinal.{0}} {a b : ℕ} (ha1 : eK a x ≤ X) (ha2 : X < eK (a + 1) x)
    (hb1 : eK b x ≤ X) (hb2 : X < eK (b + 1) x) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd (lt_of_le_of_lt ((eK_le (Nat.succ_le_of_lt hab) x).trans hb1) ha2) (lt_irrefl _)
  · exact hab
  · exact absurd (lt_of_le_of_lt ((eK_le (Nat.succ_le_of_lt hab) x).trans ha1) hb2) (lt_irrefl _)

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- `ε_{ρ+n} < δ`. -/
theorem eK_lt_δ (n : ℕ) : eK n ρ < δ := eK_lt_ups h.ρU h.ρ1 n δ h.ρδ h.next.2.1

/-- **The IMG package of `ε_{x+n}`**: witness sets with `ε_{ρ+n}` in them such that every covering copy
`f` has `ε_{f(ρ)+n} ≤ f(ε_{ρ+n})`. -/
theorem pkg_eK : ∀ n : ℕ, ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ eK n ρ ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      eK n (f ρ) ≤ f (eK n ρ)
  | 0 => by
    refine ⟨{ρ}, ∅, ?_, by simp [eK_zero], fun A f _ _ _ => by simp [eK_zero]⟩
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl h.ρδ (Or.inl (inE_indec h.ρE))
    simpa using this
  | n + 1 => by
    classical
    obtain ⟨W, Z, w, m, i⟩ := pkg_eK n
    set E := eK (n + 1) ρ with hEdef
    have hE : InE E := eK_E_succ n ρ
    have hEδ : E < δ := h.eK_lt_δ (n + 1)
    have hδI := inE_indec h.δE
    have hEE : E + E < δ := hδI.add_lt hEδ hEδ
    have hEpos : 0 < E := hE.pos
    have heE : eK n ρ < E := eK_lt_succ n ρ
    have hρE : ρ < E := lt_of_le_of_lt (le_eK n ρ) heE
    have w1 : WZ ρ δ (insert E W) Z := w.insW hρE.le hEδ (Or.inl (inE_indec hE))
    have w2 : WZ ρ δ (insert (E + E) (insert E W)) Z :=
      w1.insW (hρE.le.trans le_self_add) hEE
        (Or.inr ⟨E, Finset.mem_union_left _ (Finset.mem_insert_self _ _), E,
          Finset.mem_union_left _ (Finset.mem_insert_self _ _), lt_add_of_pos_right _ hEpos,
          lt_add_of_pos_right _ hEpos, rfl⟩)
    refine ⟨insert (E + E) (insert E W), Z, w2,
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩
    intro A f hW hZ C
    have hW' : ↑W ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have heA : eK n ρ ∈ A := mem_A m hW' hZ
    have hEA : E ∈ A := hW (by simp)
    have hEEA : E + E ∈ A := hW (by simp)
    have hfe : eK n (f ρ) ≤ f (eK n ρ) := i A f hW' hZ C
    have hfeE : f (eK n ρ) < f E := C.mono heA hEA heE
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
    rw [eK_succ]
    exact eN_le (lt_of_le_of_lt hfe hfeE) hfE

/-- A source atom `ω^{a'} ≤₁ ω^{a'} + z` inside the block of `ρ` (`ω^z ∣ a' ≠ 0`, `0 < z ≤ ω^{a'}`,
`ρ < ω^{a'}`, `ω^{a'} + z ≤ δ`; [W07b] Theorem 2.2, `RstK.lowδ`). -/
theorem src_gen {a' z : Ordinal.{0}} (hz0 : z ≠ 0) (ha0 : a' ≠ 0) (hd : ω ^ z ∣ a')
    (hza : z ≤ ω ^ a') (hρa : ρ < ω ^ a') (hδ : ω ^ a' + z ≤ δ) : le1 (ω ^ a') (ω ^ a' + z) :=
  (h.lowδ _ _ hρa hδ).2
    ((le1R_thm22 (pos_iff_ne_zero.2 hz0) hza).2 ⟨a', ha0, rfl, (le_lg_iff ha0 z).2 hd⟩)

/-- **Lemma IMG below `ε_{ρ+ω}`**: every `v < ε_{ρ+N+1}` has a term `s` of `TW` and witness sets such
that every covering copy `f` of a set containing them has `s(f(ρ)) ≤ f(v)`; for an indecomposable
`v ≥ ρ` the term is an atom `atw n s'` with `ε_{ρ+n} ≤ ε_{ρ+n} + s'(ρ) < ε_{ρ+n+1}`. -/
theorem imgT (N : ℕ) : ∀ v, v < eK (N + 1) ρ → ∃ W Z s, ImgT ρ δ v W Z s ∧
    (ρ ≤ v → Indec v → ∃ n s', s = atw n s' ∧ eK n ρ + val s' ρ < eK (n + 1) ρ) := by
  classical
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvδ : v < δ := hv.trans (h.eK_lt_δ _)
  have hρE' : ω ^ ρ = ρ := hρE
  rcases lt_or_ge v ρ with hvρ | hρv
  · -- a constant
    refine ⟨∅, {v}, cst v, ⟨WZ.empty.insZ hvρ, hvρ, ?_, rfl, by simp, ?_⟩,
      fun h1 => absurd h1 (not_le.2 hvρ)⟩
    · intro c hc; simp [csw] at hc; simp [hc]
    · intro A f _ hZ C
      have hvA : v ∈ A := hZ (by simp)
      rw [val_cst, C.fix v hvA hvρ]
  by_cases hI : Indec v
  · obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have hρL : ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [hρE']; exact hρv)
    have hLv : L ≤ ω ^ L := right_le_opow _ one_lt_omega0
    obtain ⟨n, -, hn1, hn2⟩ := eK_bracket N hρL (lt_of_le_of_lt hLv hv)
    set e := eK n ρ with hedef
    have heE : InE e := eK_E hρE
    have heE' : ω ^ e = e := heE
    have hρe : ρ ≤ e := le_eK n ρ
    have hnext : eN e = eK (n + 1) ρ := by rw [hedef, eK_succ]
    set β := L - e with hβdef
    have heβ : e + β = L := Ordinal.add_sub_cancel_of_le hn1
    have hβn : e + β < eK (n + 1) ρ := by rw [heβ]; exact hn2
    rw [← heβ] at hv hvδ hρv IH ⊢
    suffices H : ∃ W Z s', ImgT ρ δ (ω ^ (e + β)) W Z (atw n s') ∧ val s' ρ = β by
      obtain ⟨W, Z, s', hY, hs'⟩ := H
      exact ⟨W, Z, atw n s', hY, fun _ _ => ⟨n, s', rfl, by rw [hs']; exact hβn⟩⟩
    obtain ⟨We, Ze, we, me, ie⟩ := h.pkg_eK n
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · -- `v = ε_{ρ+n}`
      have hv0 : ω ^ (e + β) = e := by rw [hβ0, add_zero, heE']
      refine ⟨We, insert 0 Ze, cst 0, ⟨we.insZ hρE.pos, CBw_atw.2 hρE.pos, ?_, ?_, ?_, ?_⟩,
        by rw [val_cst, hβ0]⟩
      · intro c hc; simp [atw, csw] at hc; simp [hc]
      · rw [val_atw, val_cst, hβ0]
      · rw [hv0]
        rcases Finset.mem_union.1 me with hm | hm
        · exact Finset.mem_union_left _ hm
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hm)
      · intro A f hW hZ C
        have hZ' : ↑Ze ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hfE : ω ^ eK n (f ρ) = eK n (f ρ) := eK_E (upsPt_inE C.ups)
        rw [hv0, val_atw, val_cst, add_zero, hfE]
        exact ie A f hW hZ' C
    set v := ω ^ (e + β) with hvdef
    have hβv : e + β < v := exp_lt_atomE hβ0 (by rw [hnext]; exact hβn)
    have hρv' : ρ < v := lt_of_le_of_lt (hρe.trans le_self_add) hβv
    obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
    have hzβ : lg β ≤ β := lg_le hβ0
    set v'' := ω ^ (e + β'') with hv''def
    have hv''v : v'' < v :=
      (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
    have hρv'' : ρ ≤ v'' := (hρe.trans le_self_add).trans (right_le_opow _ one_lt_omega0)
    have heβ''n : e + β'' < eK (n + 1) ρ :=
      lt_of_le_of_lt (add_le_add (le_refl e) hβ''β.le) hβn
    obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, hat1⟩ := IH v'' hv''v (hv''v.trans hv)
    obtain ⟨n1, s'', rfl, hn1'⟩ := hat1 hρv'' (indec_opow _)
    have e1' : eK n1 ρ + val s'' ρ = e + β'' := by
      have := e1; rw [val_atw] at this; exact opow_inj this
    have hnn : n1 = n := eK_bracket_eq (by rw [← e1']; exact le_self_add) (by rw [← e1']; exact hn1')
      le_self_add heβ''n
    subst hnn
    have hs'' : val s'' ρ = β'' := (add_left_cancel_iff).1 e1'
    rw [CBw_atw] at c1
    rw [csw_atw] at cs1
    rcases eq_or_ne (lg β) 0 with hz0 | hz0
    · -- `β = β'' + 1`
      have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
      have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
      refine ⟨insert v W1, insert 1 Z1, sm s'' (cst 1),
        ⟨(w1.insZ h1ρ).insW hρv'.le hvδ (Or.inl (indec_opow _)), CBw_atw.2 ⟨c1, h1ρ⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩, by rw [val_sm, val_cst, hs'', hβs]⟩
      · intro c hc
        rw [csw_atw] at hc
        simp only [csw, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact Finset.mem_insert_of_mem (cs1 c hc)
        · exact Finset.mem_insert_self _ _
      · rw [val_atw, val_sm, val_cst, hs'', ← hβs]
      intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : v ∈ A := hW (by simp)
      have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
      have hb := b1 A f hW1 hZ1 C
      rw [val_atw] at hb
      have hlt : f v'' < f v := C.mono h1A hvA hv''v
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
      rw [hc] at hlt
      rw [val_atw, val_sm, val_cst, hc, ← add_assoc]
      have h3 : eK n1 (f ρ) + val s'' (f ρ) < c :=
        (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
      exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
    -- `β = β'' + ω^z`, `z > 0`
    set z := lg β with hzdef
    have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
    have hzv : z < v := lt_of_le_of_lt (hzβ.trans le_add_self) hβv
    have hzδ : z < δ := hzv.trans hvδ
    have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
    obtain ⟨W3, Z3, sz, ⟨w3, c3, cs3, e3, m3, b3⟩, -⟩ := IH z hzv (hzv.trans hv)
    have hsrc : le1 v (v + z) :=
      h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hβ0 hdβ) hzv.le hρv'
        (hδI.add_lt hvδ hzδ).le
    have hvzδ : v + z < δ := hδI.add_lt hvδ hzδ
    have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
    have hvvz : v < v + z := lt_add_of_pos_right v hz0'
    have hev : e < v := lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)) hβv.le
    -- the bound of a copy that is a `υ`-point
    have hups : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ImgCtx ρ A f → v ∈ A →
        e ∈ A → eK n1 (f ρ) ≤ f e → UpsPt (f v) → ∀ s' : TW, CBw s' (f ρ) →
        val (atw n1 s') ρ < eK (n1 + 1) ρ → val (atw n1 s') (f ρ) ≤ f v := by
      intro A f C hvA heA hfe hU s' hs' hlt
      have hB := h.img_bases C
      have hlt' := (uniW_lt C.ups h.ρU hB (t := atw n1 s') (u := ep (n1 + 1))
        (CBw_atw.2 hs') trivial).1 hlt
      rw [val_ep] at hlt'
      have hfev : f e < f v := C.mono heA hvA hev
      have hge : eK (n1 + 1) (f ρ) ≤ f v := by
        rw [eK_succ]; exact eN_le (lt_of_le_of_lt hfe hfev) (upsPt_inE hU)
      exact (hlt'.trans_le hge).le
    rcases eq_or_ne β'' 0 with hb0 | hb0
    · -- `β = ω^z`
      have hβz : β = ω ^ z := by rw [hgs, hb0, zero_add]
      set W0 := W3 ∪ We with hW0
      set Z0 := insert 0 (Z3 ∪ Ze) with hZ0
      have wz0 : WZ ρ δ W0 Z0 := (w3.union we).insZ hρE.pos
      have hzm0 : z ∈ W0 ∪ Z0 := by
        rcases Finset.mem_union.1 m3 with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
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
        · exact wz0.insW (hρe.trans le_self_add) (hδI.add_lt (h.eK_lt_δ n1) hzδ)
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
      refine ⟨insert (v + z) (insert v Wx), Z0, pw sz, ⟨wzf, CBw_atw.2 c3, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩,
        by rw [val_pw, e3, hβz]⟩
      · intro c hc
        rw [csw_atw] at hc
        simp only [csw] at hc
        exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
      · rw [val_atw, val_pw, e3, ← hβz]
      intro A f hW hZ C
      have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (hW0x (Finset.mem_coe.1 hx)))))
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
        hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
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
      have hfe : eK n1 (f ρ) ≤ f e := ie A f hWe hZe C
      have hfev : f e < f v := C.mono heA hvA hev
      have hcs : ∀ c ∈ csw sz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc))
      have hCB : CBw sz (f ρ) := img_cbw C c3 hcs
      by_cases hU : UpsPt (f v)
      · refine hups A f C hvA heA hfe hU (pw sz) hCB ?_
        rw [val_atw, val_pw, e3, ← hβz]
        have hE2 : ω ^ eN e = eN e := eN_E e
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2
          (show e + β < eN e by rw [hnext]; exact hβn)
        rw [hE2, hnext] at h1
        exact h1
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      rw [val_atw, val_pw, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
      by_cases hze : z ≤ e
      · have hezA : e + z ∈ A := by
          have : e + z ∈ Wx := by rw [hWx, if_pos hze]; exact Finset.mem_insert_self _ _
          exact hW (by simp [this])
        -- the copy of the base `e` is `ω^c` with `ω^{f(z)} ∣ c`
        obtain ⟨c, hc, hdc⟩ : ∃ c, f e = ω ^ c ∧ ω ^ f z ∣ c := by
          rcases Nat.eq_zero_or_pos n1 with hn0 | hnpos
          · have he0 : e = ρ := by rw [hedef, hn0, eK_zero]
            have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
            refine ⟨f ρ, by rw [he0, hfE], ?_⟩
            have hzρ : z ≤ ρ := he0 ▸ hze
            exact opow_dvd_of_inE (upsPt_inE C.ups) ((C.mono.le_iff_le hzA C.rho).2 hzρ)
          · have hρe' : ρ < e := by rw [hedef]; exact eK_lt hnpos ρ
            have hsrce : le1 e (e + z) := by
              have := h.src_gen (a' := e) hz0 heE.pos.ne' (opow_dvd_of_inE heE hze)
                (by rw [heE']; exact hze) (by rw [heE']; exact hρe')
                (by rw [heE']; exact (hδI.add_lt (h.eK_lt_δ n1) hzδ).le)
              rwa [heE'] at this
            exact h.copy_atom C heA hzA hezA hz0 hze h0A hsrce
        have hfE : ω ^ eK n1 (f ρ) = eK n1 (f ρ) := eK_E (upsPt_inE C.ups)
        have hcl : eK n1 (f ρ) ≤ c := by
          rw [hc, ← hfE] at hfe; exact (opow_le_opow_iff_right one_lt_omega0).1 hfe
        have hca : c < a := by
          have := hfev; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
        exact (add_le_add hcl htw).trans (dvd_next hda hdc hca)
      · push Not at hze
        have hfz : f e < f z := C.mono heA hzA hze
        have h1 : eK n1 (f ρ) < ω ^ f z :=
          lt_of_le_of_lt hfe (hfz.trans_le (right_le_opow _ one_lt_omega0))
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, opow_zero] at ha
          have : (1 : Ordinal.{0}) < f v := lt_of_le_of_lt (one_le_iff_pos.2
            (eK_E (upsPt_inE C.ups)).pos) (lt_of_le_of_lt hfe hfev)
          rw [ha] at this; exact lt_irrefl _ this
        have h2 : eK n1 (f ρ) + ω ^ val sz (f ρ) ≤ ω ^ f z := by
          rcases htw.lt_or_eq with hlt | heq
          · exact (isPrincipal_add_omega0_opow _ h1 hlt).le
          · rw [heq, add_omega0_opow h1]
        exact h2.trans (le_of_dvd ha0 hda)
    · -- `β'' ≠ 0`: the source atom of `v''` too
      have hzb : z ≤ β'' := (right_le_opow z one_lt_omega0).trans (le_of_dvd hb0 hdvd)
      have hzvb : z < v'' := lt_of_le_of_lt (hzb.trans le_add_self)
        (exp_lt_atomE hb0 (by rw [hnext]; exact heβ''n))
      have hv''zδ : v'' + z < δ := hδI.add_lt (hv''v.trans hvδ) hzδ
      have hρv''' : ρ < v'' := lt_of_le_of_lt (hρe.trans le_self_add)
        (exp_lt_atomE hb0 (by rw [hnext]; exact heβ''n))
      have hsrc'' : le1 v'' (v'' + z) :=
        h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hb0 hdvd) hzvb.le hρv'''
          hv''zδ.le
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
      have hem0 : e ∈ W0 ∪ Z0 := by
        rcases Finset.mem_union.1 me with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
      have wz1 : WZ ρ δ (insert (v'' + z) W0) Z0 :=
        wz0.insW (hρv''.trans le_self_add) hv''zδ
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
      refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, sm s'' (pw sz),
        ⟨wzf, CBw_atw.2 ⟨c1, c3⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩,
        by rw [val_sm, val_pw, hs'', e3, ← hgs]⟩
      · intro c hc
        rw [csw_atw] at hc
        simp only [csw, List.mem_append] at hc
        rcases hc with hc | hc
        · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
        · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
      · rw [val_atw, val_sm, val_pw, hs'', e3, ← hgs]
      intro A f hW hZ C
      have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))))
      have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
        hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
        hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
      have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hW3 : ↑W3 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hWe : ↑We ⊆ A := hsW (by intro x hx; simp [hW0, hx])
      have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZ3 : ↑Z3 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have hZe : ↑Ze ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
      have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
      have hvA : v ∈ A := hW (by simp)
      have hvzA : v + z ∈ A := hW (by simp)
      have hv''zA : v'' + z ∈ A := hW (by simp)
      have hzA : z ∈ A := mem_A hzm0 hW0A hZ
      have hv''A : v'' ∈ A := mem_A hv''m hW0A hZ
      have heA : e ∈ A := mem_A hem0 hW0A hZ
      have hb'' := b1 A f hW1 hZ1 C
      rw [val_atw] at hb''
      have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
      have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
      have hfe : eK n1 (f ρ) ≤ f e := ie A f hWe hZe C
      have hcs1 : ∀ c ∈ csw s'', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc))
      have hcs3 : ∀ c ∈ csw sz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc))
      have hCB : CBw (sm s'' (pw sz)) (f ρ) := ⟨img_cbw C c1 hcs1, img_cbw C c3 hcs3⟩
      by_cases hU : UpsPt (f v)
      · refine hups A f C hvA heA hfe hU (sm s'' (pw sz)) hCB ?_
        rw [val_atw, val_sm, val_pw, hs'', e3, ← hgs]
        have hE2 : ω ^ eN e = eN e := eN_E e
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2
          (show e + β < eN e by rw [hnext]; exact hβn)
        rw [hE2, hnext] at h1
        exact h1
      obtain ⟨c, hc, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzvb.le h0A hsrc''
      have hbc : eK n1 (f ρ) + val s'' (f ρ) ≤ c := by
        rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
      have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      have hca : c < a := by
        have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      rw [val_atw, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      rw [val_sm, val_pw, ← add_assoc]
      exact (add_le_add hbc htw).trans (dvd_next hda hdc hca)
  · -- a decomposable value: a sum
    have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
    obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, -⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨W2, Z2, s2, ⟨w2, c2, cs2, e2, m2, b2⟩, -⟩ := IH u2 hu2 (hu2.trans hv)
    subst hsum
    have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
      intro x hx
      rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
    refine ⟨insert (u1 + u2) (W1 ∪ W2), Z1 ∪ Z2, sm s1 s2,
      ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2,
        rfl⟩), ⟨c1, c2⟩, ?_, by simp [e1, e2], by simp, ?_⟩, fun _ hI' => absurd hI' hI⟩
    · intro c hc
      simp only [csw, List.mem_append] at hc
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
      rw [val_sm, ← this]
      exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- **The IMG package of a term of `TW`** (constants below `ρ`, value `≥ 1`). -/
theorem pkgT {s : TW} (hs : CBw s ρ) (h1 : 1 ≤ val s ρ) : ImgPkg ρ δ (val s) := by
  classical
  have hvN := val_lt_eK h.ρE s hs
  obtain ⟨W, Z, s0, ⟨w, c0, cs0, e0, m0, b0⟩, -⟩ := h.imgT (lv s) (val s ρ) hvN
  have wzc : WZ ρ δ ∅ (csw s).toFinset :=
    ⟨by simp, fun z hz => (cbw_iff s ρ).1 hs z (List.mem_toFinset.1 hz), by simp⟩
  have hw' := w.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨h1, hvN.trans (h.eK_lt_δ _), W, Z ∪ (csw s).toFinset, hw', ?_, ?_⟩
  · rcases Finset.mem_union.1 m0 with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  · intro A f hW hZ C
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hcs : ∀ c ∈ csw s, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcs0 : ∀ c ∈ csw s0, c ∈ A := fun c hc => hZ0 (Finset.mem_coe.2 (cs0 c hc))
    have hB := h.img_bases C
    have heq := (uniW_eq C.ups h.ρU hB (img_cbw C hs hcs) (img_cbw C c0 hcs0)).1 e0.symm
    rw [heq]
    exact b0 A f hW hZ0 C

end RstK

end Googology.Trans.PoR.InaccPsi.R2
