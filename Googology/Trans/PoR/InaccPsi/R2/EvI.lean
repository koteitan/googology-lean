import Googology.Trans.PoR.InaccPsi.R2.EvT
import Googology.Trans.PoR.InaccPsi.R2.EvW

/-!
# Lemma IMG for every value below `ε_{ρ+ρ}`

The project's Lemma IMG for every ordinal `v < ε_{ρ+ρ}`, with a term of `TEv`, by induction on `v`: the argument
of `RstK.imgT` (`R2.EpsI`) with the pseudo-base `e = ε_{ρ+c}` for every constant `c < ρ`, the IMG package of
`ε_{x+c}` being `RstK.pkg_evA` (`R2.EvW`) instead of the `≤₁`-test `e ≤₁ e·2` alone.

* `ImgV`, `img_cbv`, `atv` (the atom term `ω^{ε_{x+c}+s}`);
* `RstK.imgV` (**Lemma IMG below `ε_{ρ+ρ}`**), `RstK.pkgV` (the IMG package of a term of `TEv` with value `≥ 1`).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order TEv

/-- **The IMG statement for one value** `v` with a term `s` of `TEv` (`s(ρ) = v`, constants in `Z`). -/
def ImgV (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : TEv) : Prop :=
  WZ ρ δ W Z ∧ CBv s ρ ∧ (∀ c ∈ csv s, c ∈ Z) ∧ val s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val s (f ρ) ≤ f v

theorem img_cbv {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : TEv} (hs : CBv s ρ) (hA : ∀ c ∈ csv s, c ∈ A) : CBv s (f ρ) :=
  (cbv_iff s _).2 (fun c hc => C.above c (hA c hc) ((cbv_iff s ρ).1 hs c hc))

/-- The atom term `ω^{ε_{x+c}+s}`. -/
def atv (c : Ordinal.{0}) (s : TEv) : TEv := pw (sm (ec c) s)

@[simp] theorem val_atv (c : Ordinal.{0}) (s : TEv) (x : Ordinal.{0}) :
    val (atv c s) x = ω ^ (evA x c + val s x) := rfl

theorem CBv_atv {c : Ordinal.{0}} {s : TEv} {x : Ordinal.{0}} : CBv (atv c s) x ↔ c < x ∧ CBv s x := by
  simp [atv, CBv]

theorem csv_atv (c : Ordinal.{0}) (s : TEv) : csv (atv c s) = c :: csv s := by simp [atv, csv]

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG below `ε_{ρ+ρ}`**: every `v < ε_{ρ+ρ}` has a term `s` of `TEv` and witness sets such that every
covering copy `f` of a set containing them has `s(f(ρ)) ≤ f(v)`; for an indecomposable `v ≥ ρ` the term is an
atom `atv c s'` with `c < ρ` and `ε_{ρ+c} ≤ ε_{ρ+c} + s'(ρ) < ε_{ρ+c+1}`. -/
theorem imgV : ∀ v, v < evA ρ ρ → ∃ W Z s, ImgV ρ δ v W Z s ∧
    (ρ ≤ v → Indec v → ∃ c s', s = atv c s' ∧ c < ρ ∧ evA ρ c + val s' ρ < evA ρ (c + 1)) := by
  classical
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvδ : v < δ := hv.trans (h.evA_lt_δ le_rfl)
  have hρE' : ω ^ ρ = ρ := hρE
  rcases lt_or_ge v ρ with hvρ | hρv
  · -- a constant
    refine ⟨∅, {v}, cst v, ⟨WZ.empty.insZ hvρ, hvρ, ?_, rfl, by simp, ?_⟩,
      fun h1 => absurd h1 (not_le.2 hvρ)⟩
    · intro c hc; simp [csv] at hc; simp [hc]
    · intro A f _ hZ C
      have hvA : v ∈ A := hZ (by simp)
      rw [val_cst, C.fix v hvA hvρ]
  by_cases hI : Indec v
  · obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have hρL : ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [hρE']; exact hρv)
    have hLv : L ≤ ω ^ L := right_le_opow _ one_lt_omega0
    obtain ⟨n, hnρ, hn1, hn2⟩ := evA_bracket hρE hρL (lt_of_le_of_lt hLv hv)
    set e := evA ρ n with hedef
    have heE : InE e := evA_E _ _
    have heE' : ω ^ e = e := heE
    have hρe : ρ ≤ e := le_evA hρE n
    have hnext : eN e = evA ρ (n + 1) := by rw [hedef, evA_add_one]
    set β := L - e with hβdef
    have heβ : e + β = L := Ordinal.add_sub_cancel_of_le hn1
    have hβn : e + β < evA ρ (n + 1) := by rw [heβ]; exact hn2
    rw [← heβ] at hv hvδ hρv IH ⊢
    suffices H : ∃ W Z s', ImgV ρ δ (ω ^ (e + β)) W Z (atv n s') ∧ val s' ρ = β by
      obtain ⟨W, Z, s', hY, hs'⟩ := H
      exact ⟨W, Z, atv n s', hY, fun _ _ => ⟨n, s', rfl, hnρ, by rw [hs']; exact hβn⟩⟩
    obtain ⟨We, Ze, we, me, hnZe, ie⟩ := h.pkg_evA n hnρ
    have hnfρ : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Ze ⊆ A → ImgCtx ρ A f →
        n < f ρ := fun A f hZ C => C.above n (hZ (Finset.mem_coe.2 hnZe)) hnρ
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · -- `v = ε_{ρ+n}`
      have hv0 : ω ^ (e + β) = e := by rw [hβ0, add_zero, heE']
      refine ⟨We, insert 0 Ze, cst 0, ⟨we.insZ hρE.pos, CBv_atv.2 ⟨hnρ, hρE.pos⟩, ?_, ?_, ?_, ?_⟩,
        by rw [val_cst, hβ0]⟩
      · intro c hc
        rw [csv_atv] at hc
        simp only [csv, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_insert_of_mem hnZe
        · exact Finset.mem_insert_self _ _
      · rw [val_atv, val_cst, hβ0]
      · rw [hv0]
        rcases Finset.mem_union.1 me with hm | hm
        · exact Finset.mem_union_left _ hm
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hm)
      · intro A f hW hZ C
        have hZ' : ↑Ze ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hfE : ω ^ evA (f ρ) n = evA (f ρ) n := evA_E _ _
        rw [hv0, val_atv, val_cst, add_zero, hfE]
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
    have heβ''n : e + β'' < evA ρ (n + 1) :=
      lt_of_le_of_lt (add_le_add (le_refl e) hβ''β.le) hβn
    obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, hat1⟩ := IH v'' hv''v (hv''v.trans hv)
    obtain ⟨n1, s'', rfl, hn1ρ, hn1'⟩ := hat1 hρv'' (indec_opow _)
    have e1' : evA ρ n1 + val s'' ρ = e + β'' := by
      have := e1; rw [val_atv] at this; exact opow_inj this
    have hnn : n1 = n := evA_bracket_eq (by rw [← e1']; exact le_self_add) (by rw [← e1']; exact hn1')
      le_self_add heβ''n
    subst hnn
    have hs'' : val s'' ρ = β'' := (add_left_cancel_iff).1 e1'
    have hnZ1 : n1 ∈ Z1 := cs1 n1 (by rw [csv_atv]; exact List.mem_cons_self)
    rw [CBv_atv] at c1
    obtain ⟨-, c1⟩ := c1
    have cs1' : ∀ c ∈ csv s'', c ∈ Z1 := fun c hc => cs1 c (by rw [csv_atv]; exact List.mem_cons_of_mem _ hc)
    rcases eq_or_ne (lg β) 0 with hz0 | hz0
    · -- `β = β'' + 1`
      have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
      have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
      refine ⟨insert v W1, insert 1 Z1, sm s'' (cst 1),
        ⟨(w1.insZ h1ρ).insW hρv'.le hvδ (Or.inl (indec_opow _)), CBv_atv.2 ⟨hn1ρ, c1, h1ρ⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩, by rw [val_sm, val_cst, hs'', hβs]⟩
      · intro c hc
        rw [csv_atv] at hc
        simp only [csv, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | hc | rfl
        · exact Finset.mem_insert_of_mem hnZ1
        · exact Finset.mem_insert_of_mem (cs1' c hc)
        · exact Finset.mem_insert_self _ _
      · rw [val_atv, val_sm, val_cst, hs'', ← hβs]
      intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : v ∈ A := hW (by simp)
      have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
      have hb := b1 A f hW1 hZ1 C
      rw [val_atv] at hb
      have hlt : f v'' < f v := C.mono h1A hvA hv''v
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
      rw [hc] at hlt
      rw [val_atv, val_sm, val_cst, hc, ← add_assoc]
      have h3 : evA (f ρ) n1 + val s'' (f ρ) < c :=
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
        e ∈ A → evA (f ρ) n1 ≤ f e → UpsPt (f v) → n1 < f ρ → ∀ s' : TEv, CBv s' (f ρ) →
        val (atv n1 s') ρ < evA ρ (n1 + 1) → val (atv n1 s') (f ρ) ≤ f v := by
      intro A f C hvA heA hfe hU hnf s' hs' hlt
      have hB := h.img_bases C
      have hlt' := (uniV_lt C.ups h.ρU hB (t := atv n1 s') (u := ec (n1 + 1))
        (CBv_atv.2 ⟨hnf, hs'⟩) ((ev_isSuccLimit_of_inE (upsPt_inE C.ups)).add_one_lt hnf)).1 hlt
      rw [val_ec] at hlt'
      have hfev : f e < f v := C.mono heA hvA hev
      have hge : evA (f ρ) (n1 + 1) ≤ f v := by
        rw [evA_add_one]; exact eN_le (lt_of_le_of_lt hfe hfev) (upsPt_inE hU)
      exact (hlt'.trans_le hge).le
    rcases eq_or_ne β'' 0 with hb0 | hb0
    · -- `β = ω^z`
      have hβz : β = ω ^ z := by rw [hgs, hb0, zero_add]
      set W0 := W3 ∪ We with hW0
      set Z0 := insert 0 (Z3 ∪ Ze) with hZ0
      have wz0 : WZ ρ δ W0 Z0 := (w3.union we).insZ hρE.pos
      have hnZ0 : n1 ∈ Z0 := Finset.mem_insert_of_mem (Finset.mem_union_right _ hnZe)
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
        · exact wz0.insW (hρe.trans le_self_add) (hδI.add_lt (h.evA_lt_δ hn1ρ.le) hzδ)
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
      refine ⟨insert (v + z) (insert v Wx), Z0, pw sz, ⟨wzf, CBv_atv.2 ⟨hn1ρ, c3⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩,
        by rw [val_pw, e3, hβz]⟩
      · intro c hc
        rw [csv_atv] at hc
        simp only [csv, List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hnZ0
        · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
      · rw [val_atv, val_pw, e3, ← hβz]
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
      have hfe : evA (f ρ) n1 ≤ f e := ie A f hWe hZe C
      have hfev : f e < f v := C.mono heA hvA hev
      have hcs : ∀ c ∈ csv sz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc))
      have hCB : CBv sz (f ρ) := img_cbv C c3 hcs
      by_cases hU : UpsPt (f v)
      · refine hups A f C hvA heA hfe hU (hnfρ A f hZe C) (pw sz) hCB ?_
        rw [val_atv, val_pw, e3, ← hβz]
        have hE2 : ω ^ eN e = eN e := eN_E e
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2
          (show e + β < eN e by rw [hnext]; exact hβn)
        rw [hE2, hnext] at h1
        exact h1
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      rw [val_atv, val_pw, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
      by_cases hze : z ≤ e
      · have hezA : e + z ∈ A := by
          have : e + z ∈ Wx := by rw [hWx, if_pos hze]; exact Finset.mem_insert_self _ _
          exact hW (by simp [this])
        -- the copy of the base `e` is `ω^c` with `ω^{f(z)} ∣ c`
        obtain ⟨c, hc, hdc⟩ : ∃ c, f e = ω ^ c ∧ ω ^ f z ∣ c := by
          rcases eq_or_ne n1 0 with hn0 | hn0'
          · have he0 : e = ρ := by rw [hedef, hn0, evA_zero hρE]
            have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
            refine ⟨f ρ, by rw [he0, hfE], ?_⟩
            have hzρ : z ≤ ρ := he0 ▸ hze
            exact opow_dvd_of_inE (upsPt_inE C.ups) ((C.mono.le_iff_le hzA C.rho).2 hzρ)
          · have hρe' : ρ < e := by rw [hedef]; exact lt_evA hρE hn0'
            have hsrce : le1 e (e + z) := by
              have := h.src_gen (a' := e) hz0 heE.pos.ne' (opow_dvd_of_inE heE hze)
                (by rw [heE']; exact hze) (by rw [heE']; exact hρe')
                (by rw [heE']; exact (hδI.add_lt (h.evA_lt_δ hn1ρ.le) hzδ).le)
              rwa [heE'] at this
            exact h.copy_atom C heA hzA hezA hz0 hze h0A hsrce
        have hfE : ω ^ evA (f ρ) n1 = evA (f ρ) n1 := evA_E _ _
        have hcl : evA (f ρ) n1 ≤ c := by
          rw [hc, ← hfE] at hfe; exact (opow_le_opow_iff_right one_lt_omega0).1 hfe
        have hca : c < a := by
          have := hfev; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
        exact (add_le_add hcl htw).trans (dvd_next hda hdc hca)
      · push Not at hze
        have hfz : f e < f z := C.mono heA hzA hze
        have h1 : evA (f ρ) n1 < ω ^ f z :=
          lt_of_le_of_lt hfe (hfz.trans_le (right_le_opow _ one_lt_omega0))
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, opow_zero] at ha
          have : (1 : Ordinal.{0}) < f v := lt_of_le_of_lt (one_le_iff_pos.2
            (evA_E (f ρ) n1).pos) (lt_of_le_of_lt hfe hfev)
          rw [ha] at this; exact lt_irrefl _ this
        have h2 : evA (f ρ) n1 + ω ^ val sz (f ρ) ≤ ω ^ f z := by
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
      have hnZ0 : n1 ∈ Z0 := Finset.mem_insert_of_mem (Finset.mem_union_right _ hnZe)
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
        ⟨wzf, CBv_atv.2 ⟨hn1ρ, c1, c3⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩,
        by rw [val_sm, val_pw, hs'', e3, ← hgs]⟩
      · intro c hc
        rw [csv_atv] at hc
        simp only [csv, List.mem_cons, List.mem_append] at hc
        rcases hc with rfl | hc | hc
        · exact hnZ0
        · exact Finset.mem_insert_of_mem (by simp [cs1' c hc])
        · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
      · rw [val_atv, val_sm, val_pw, hs'', e3, ← hgs]
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
      rw [val_atv] at hb''
      have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
      have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
      have hfe : evA (f ρ) n1 ≤ f e := ie A f hWe hZe C
      have hcs1 : ∀ c ∈ csv s'', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (cs1' c hc))
      have hcs3 : ∀ c ∈ csv sz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc))
      have hCB : CBv (sm s'' (pw sz)) (f ρ) := ⟨img_cbv C c1 hcs1, img_cbv C c3 hcs3⟩
      by_cases hU : UpsPt (f v)
      · refine hups A f C hvA heA hfe hU (hnfρ A f hZe C) (sm s'' (pw sz)) hCB ?_
        rw [val_atv, val_sm, val_pw, hs'', e3, ← hgs]
        have hE2 : ω ^ eN e = eN e := eN_E e
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2
          (show e + β < eN e by rw [hnext]; exact hβn)
        rw [hE2, hnext] at h1
        exact h1
      obtain ⟨c, hc, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzvb.le h0A hsrc''
      have hbc : evA (f ρ) n1 + val s'' (f ρ) ≤ c := by
        rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
      have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      have hca : c < a := by
        have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      rw [val_atv, ha]
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
      simp only [csv, List.mem_append] at hc
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

/-- **The IMG package of a term of `TEv`** (constants below `ρ`, value `≥ 1`). -/
theorem pkgV {s : TEv} (hs : CBv s ρ) (h1 : 1 ≤ val s ρ) : ImgPkg ρ δ (val s) := by
  classical
  have hvN := valV_lt_AA h.ρE hs
  obtain ⟨W, Z, s0, ⟨w, c0, cs0, e0, m0, b0⟩, -⟩ := h.imgV (val s ρ) hvN
  have wzc : WZ ρ δ ∅ (csv s).toFinset :=
    ⟨by simp, fun z hz => (cbv_iff s ρ).1 hs z (List.mem_toFinset.1 hz), by simp⟩
  have hw' := w.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨h1, hvN.trans (h.evA_lt_δ le_rfl), W, Z ∪ (csv s).toFinset, hw', ?_, ?_⟩
  · rcases Finset.mem_union.1 m0 with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  · intro A f hW hZ C
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hcs : ∀ c ∈ csv s, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcs0 : ∀ c ∈ csv s0, c ∈ A := fun c hc => hZ0 (Finset.mem_coe.2 (cs0 c hc))
    have hB := h.img_bases C
    have heq := (uniV_eq C.ups h.ρU hB (img_cbv C hs hcs) (img_cbv C c0 hcs0)).1 e0.symm
    rw [heq]
    exact b0 A f hW hZ0 C

end RstK

end Googology.Trans.PoR.InaccPsi.R2
