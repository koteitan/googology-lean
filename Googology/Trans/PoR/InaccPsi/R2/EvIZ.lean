import Googology.Trans.PoR.InaccPsi.R2.EvTZ
import Googology.Trans.PoR.InaccPsi.R2.EvW

/-!
# Lemma IMG for every value below the next fixed point of `ε`

The project's Lemma IMG for every ordinal `v < evZ ρ` (`ζ_{ρ+1}`), with a term of `TZ`, by induction on `v`,
together with the IMG package of every `ε`-number `ε_{ρ+c}` below `evZ ρ` with a term for its index `c`:

* an `ε`-number `v = ε_{ρ+c}`, `c = c' + ω^z` (`z = logend(c)`, `c < v`): inside the block `v ≤₁ v·2 + z`
  (`R₁⁺`, `lh_evAZ`; `z = 0`: `le1R_two_iff`), the copy keeps it, and a copy that is not a `υ`-point is
  `≥ ε_{b+ω^{f(z)}}` above `b = ε_{f(ρ)+s'(f(ρ))}` (the package of `ε_{ρ+c'}`), by `le1R_ge_evAg`; the index term
  is `s' + ω^{s_z}` with the IMG term `s_z` of `z`; a copy that is a `υ`-point is above `evZ (f ρ)`;
* an atom `ω^{e+β}` with the `ε`-base `e = ε_{ρ+n}`: the argument of `RstK.imgV` (`R2.EvI`), with the package of
  `e` in place of `RstK.pkg_evA`;
* a sum is copied by a sum.

* `ImgZ`, `EpsZ`, `img_cbz`, `atz`;
* `RstK.imgZ` (**Lemma IMG below `evZ ρ`**, with the packages of the `ε`-numbers), `RstK.pkgZ` (the IMG package
  of a term of `TZ` with value `≥ 1`).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order TZ

/-- **The IMG statement for one value** `v` with a term `s` of `TZ` (`s(ρ) = v`, constants in `Z`). -/
def ImgZ (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : TZ) : Prop :=
  WZ ρ δ W Z ∧ CBz s ρ ∧ (∀ c ∈ csz s, c ∈ Z) ∧ val s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val s (f ρ) ≤ f v

/-- **The IMG package of `ε_{ρ+c}`** with a term `s` for the index (`s(ρ) = c`, constants in `Z`). -/
def EpsZ (ρ δ c : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : TZ) : Prop :=
  WZ ρ δ W Z ∧ CBz s ρ ∧ (∀ c ∈ csz s, c ∈ Z) ∧ val s ρ = c ∧ evA ρ c ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      evA (f ρ) (val s (f ρ)) ≤ f (evA ρ c)

theorem img_cbz {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : TZ} (hs : CBz s ρ) (hA : ∀ c ∈ csz s, c ∈ A) : CBz s (f ρ) :=
  (cbz_iff s _).2 (fun c hc => C.above c (hA c hc) ((cbz_iff s ρ).1 hs c hc))

/-- The atom term `ω^{ε_{x+s}+s'}`. -/
def atz (s s' : TZ) : TZ := pw (sm (ee s) s')

@[simp] theorem val_atz (s s' : TZ) (x : Ordinal.{0}) :
    val (atz s s') x = ω ^ (evA x (val s x) + val s' x) := rfl

theorem CBz_atz {s s' : TZ} {x : Ordinal.{0}} : CBz (atz s s') x ↔ CBz s x ∧ CBz s' x := by
  simp [atz, CBz]

theorem csz_atz (s s' : TZ) : csz (atz s s') = csz s ++ csz s' := by simp [atz, csz]

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem evA_lt_δZ {c : Ordinal.{0}} (hc : c < evZ ρ) : evA ρ c < δ :=
  evA_lt_upsZ h.ρE h.ρ1 hc h.ρδ h.next.2.1

theorem evZ_le_δ : evZ ρ ≤ δ := evZ_le_ups h.ρE h.ρ1 h.ρδ h.next.2.1

/-- **Lemma IMG below `evZ ρ`**, with the IMG packages of the `ε`-numbers below `evZ ρ`. -/
theorem imgZ : ∀ v, v < evZ ρ →
    (∃ W Z s, ImgZ ρ δ v W Z s ∧
      (ρ ≤ v → Indec v → ∃ se s', s = atz se s' ∧ evA ρ (val se ρ) + val s' ρ < evA ρ (val se ρ + 1))) ∧
    (∀ c, evA ρ c = v → ∃ W Z s, EpsZ ρ δ c W Z s) := by
  classical
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvδ : v < δ := lt_of_lt_of_le hv h.evZ_le_δ
  have hρE' : ω ^ ρ = ρ := hρE
  -- Part 2: the package of an `ε`-number `v = ε_{ρ+c}`
  have P2 : ∀ c, evA ρ c = v → ∃ W Z s, EpsZ ρ δ c W Z s := by
    intro c hcv
    have hcZ : c < evZ ρ := lt_of_le_of_lt (hcv ▸ le_evA_idx ρ c) hv
    have hcv' : c < v := hcv ▸ lt_evA_self hρE hcZ
    rcases eq_or_ne c 0 with rfl | hc0
    · refine ⟨{ρ}, {0}, cst 0, ⟨?_, hρE.pos, ?_, rfl, by simp [evA_zero hρE], ?_⟩⟩
      · have := ((WZ.empty (ρ := ρ) (δ := δ)).insZ hρE.pos).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
        simpa using this
      · intro c hc; simp [csz] at hc; simp [hc]
      · intro A f _ _ C
        rw [val_cst, evA_zero hρE, evA_zero (upsPt_inE C.ups)]
    obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
    set z := lg c with hz
    have hzc : z ≤ c := lg_le hc0
    have hzv : z < v := lt_of_le_of_lt hzc hcv'
    have hv'v : evA ρ c' < v := hcv ▸ evA_lt_iff.2 hc'c
    obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, i1⟩ := (IH _ hv'v (hv'v.trans hv)).2 c' rfl
    obtain ⟨⟨W2, Z2, sz, ⟨w2, cb2, cs2, e2, m2, b2⟩, -⟩, -⟩ := IH z hzv (hzv.trans hv)
    have hvE : InE v := hcv ▸ evA_E _ _
    have hρv : ρ < v := hcv ▸ lt_evA hρE hc0
    have hv0 : 0 < v := hvE.pos
    have hvv : v + v < δ := hδI.add_lt hvδ hvδ
    have hvvz : v + v + z < δ := hδI.add_lt hvv (hzv.trans hvδ)
    -- the source: `v ≤₁ v·2 + z` in `R₁⁺`, hence in the block
    have hsrcR : le1R v (v * 2 + z) := by
      rcases eq_or_ne z 0 with hz0 | hz0
      · rw [hz0, add_zero]; exact (le1R_two_iff hv0).2 hvE
      · have hωc : ω ≤ c := by
          have h1 : ω ^ (1 : Ordinal.{0}) ∣ c := (le_lg_iff hc0 1).1 (one_le_iff_ne_zero.2 hz0)
          rw [opow_one] at h1
          exact le_of_dvd hc0 h1
        have := (lh_evAZ hρE h.ρ1 hωc hcZ).1
        rwa [hcv] at this
    have hsrc : le1 v (v + v + z) :=
      (h.lowδ _ _ hρv hvvz.le).2 (by rw [← mul_two_eq]; exact hsrcR)
    -- the witness sets
    have w0 : WZ ρ δ (W1 ∪ W2) (Z1 ∪ Z2) := w1.union w2
    have hzm : z ∈ (W1 ∪ W2) ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m2 with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have wa : WZ ρ δ (insert v (W1 ∪ W2)) (Z1 ∪ Z2) := w0.insW hρv.le hvδ (Or.inl (inE_indec hvE))
    have wb : WZ ρ δ (insert (v + v) (insert v (W1 ∪ W2))) (Z1 ∪ Z2) :=
      wa.insW (hρv.le.trans le_self_add) hvv
        (Or.inr ⟨v, by simp, v, by simp, lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
    have wc : WZ ρ δ (insert (v + v + z) (insert (v + v) (insert v (W1 ∪ W2)))) (Z1 ∪ Z2) := by
      rcases eq_or_ne z 0 with hz0 | hz0
      · have e : v + v + z = v + v := by rw [hz0, add_zero]
        rw [e, Finset.insert_idem]
        exact wb
      · refine wb.insW ((hρv.le.trans le_self_add).trans le_self_add) hvvz
          (Or.inr ⟨v + v, by simp, z, ?_, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
            lt_of_lt_of_le hzv (le_self_add.trans le_self_add), rfl⟩)
        rcases Finset.mem_union.1 hzm with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
        · exact Finset.mem_union_right _ hx
    refine ⟨_, _, sm s1 (pw sz), ⟨wc, ⟨cb1, cb2⟩, ?_, ?_, by rw [hcv]; simp, ?_⟩⟩
    · intro c hc
      simp only [csz, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_union_left _ (cs1 c hc)
      · exact Finset.mem_union_right _ (cs2 c hc)
    · rw [val_sm, val_pw, e1, e2, ← hcs]
    intro A f hW hZ C
    rw [hcv]
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have hvvA : v + v ∈ A := hW (by simp)
    have hvvzA : v + v + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A m2 hW2 hZ2
    have hv'A : evA ρ c' ∈ A := mem_A m1 hW1 hZ1
    have hb1 := i1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hfρE : InE (f ρ) := upsPt_inE C.ups
    have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
    have hfρv : f ρ < f v := C.mono C.rho hvA hρv
    have hfvv : f v + f v = f (v + v) := C.add v hvA v hvA _ hvvA rfl
    have hfvvz : f (v + v) + f z = f (v + v + z) := C.add _ hvvA z hzA _ hvvzA rfl
    have himg : le1 (f v) (f v + f v + f z) := by
      have := C.cov1 v hvA _ hvvzA hsrc
      rwa [← hfvvz, ← hfvv] at this
    have hcs1 : ∀ c ∈ csz s1, c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc))
    have hcs2 : ∀ c ∈ csz sz, c ∈ A := fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc))
    have hCB : CBz (sm s1 (pw sz)) (f ρ) := ⟨img_cbz C cb1 hcs1, img_cbz C cb2 hcs2⟩
    by_cases hU : UpsPt (f v)
    · exact (evA_lt_upsZ hfρE hfρ1 (valZ_lt hfρE _ hCB) hfρv hU).le
    · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
      rw [← mul_two_eq] at hR
      set b := evA (f ρ) (val s1 (f ρ)) with hb
      have hbv : b < f v := lt_of_le_of_lt hb1 (C.mono hv'A hvA hv'v)
      have hzfv : f z < f v := C.mono hzA hvA hzv
      have hge := le1R_ge_evAg (f z) (f v) b (evA_E _ _) hbv hzfv hR
      rw [hb, evA_add] at hge
      refine le_trans ?_ hge
      rw [val_sm, val_pw]
      exact evA_le_iff.2 (add_le_add_right ((opow_le_opow_iff_right one_lt_omega0).2 hb2) _)
  refine ⟨?_, P2⟩
  -- Part 1: IMG for `v`
  rcases lt_or_ge v ρ with hvρ | hρv
  · -- a constant
    refine ⟨∅, {v}, cst v, ⟨WZ.empty.insZ hvρ, hvρ, ?_, rfl, by simp, ?_⟩,
      fun h1 => absurd h1 (not_le.2 hvρ)⟩
    · intro c hc; simp [csz] at hc; simp [hc]
    · intro A f _ hZ C
      have hvA : v ∈ A := hZ (by simp)
      rw [val_cst, C.fix v hvA hvρ]
  by_cases hI : Indec v
  · obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have hρL : ρ ≤ L := (opow_le_opow_iff_right one_lt_omega0).1 (by rw [hρE']; exact hρv)
    have hLv : L ≤ ω ^ L := right_le_opow _ one_lt_omega0
    obtain ⟨n, -, hn1, hn2⟩ := evA_bracket hρE hρL
      (show L < evA ρ (L + 1) from lt_of_lt_of_le (lt_add_one L) (le_evA_idx ρ _))
    set e := evA ρ n with hedef
    have heE : InE e := evA_E _ _
    have heE' : ω ^ e = e := heE
    have hρe : ρ ≤ e := le_evA hρE n
    have hnext : eN e = evA ρ (n + 1) := by rw [hedef, evA_add_one]
    have hev : e ≤ ω ^ L := hn1.trans hLv
    -- the package of the base `e`
    obtain ⟨We, Ze, se, we, cbe, cse, ee', me, ie⟩ : ∃ W Z s, EpsZ ρ δ n W Z s := by
      rcases eq_or_lt_of_le hev with heq | hlt
      · exact P2 n heq
      · exact (IH e hlt (hlt.trans hv)).2 n rfl
    set β := L - e with hβdef
    have heβ : e + β = L := Ordinal.add_sub_cancel_of_le hn1
    have hβn : e + β < evA ρ (n + 1) := by rw [heβ]; exact hn2
    rw [← heβ] at hv hvδ hρv IH P2 hev ⊢
    suffices H : ∃ W Z se' s', ImgZ ρ δ (ω ^ (e + β)) W Z (atz se' s') ∧ val se' ρ = n ∧ val s' ρ = β by
      obtain ⟨W, Z, se', s', hY, hse', hs'⟩ := H
      exact ⟨W, Z, atz se' s', hY, fun _ _ => ⟨se', s', rfl, by rw [hse', hs']; exact hβn⟩⟩
    have hcse : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Ze ⊆ A → ImgCtx ρ A f →
        CBz se (f ρ) := fun A f hZ C => img_cbz C cbe (fun c hc => hZ (Finset.mem_coe.2 (cse c hc)))
    rcases eq_or_ne β 0 with hβ0 | hβ0
    · -- `v = ε_{ρ+n}`
      have hv0 : ω ^ (e + β) = e := by rw [hβ0, add_zero, heE']
      refine ⟨We, insert 0 Ze, se, cst 0, ⟨we.insZ hρE.pos, CBz_atz.2 ⟨cbe, hρE.pos⟩, ?_, ?_, ?_, ?_⟩,
        ee', by rw [val_cst, hβ0]⟩
      · intro c hc
        rw [csz_atz] at hc
        simp only [csz, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact Finset.mem_insert_of_mem (cse c hc)
        · exact Finset.mem_insert_self _ _
      · rw [val_atz, val_cst, hβ0, ee', add_zero, heE']
      · rw [hv0]
        rcases Finset.mem_union.1 me with hm | hm
        · exact Finset.mem_union_left _ hm
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hm)
      · intro A f hW hZ C
        have hZ' : ↑Ze ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
        have hfE : ω ^ evA (f ρ) (val se (f ρ)) = evA (f ρ) (val se (f ρ)) := evA_E _ _
        rw [hv0, val_atz, val_cst, add_zero, hfE]
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
    obtain ⟨⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, hat1⟩, -⟩ := IH v'' hv''v (hv''v.trans hv)
    obtain ⟨t1, s'', rfl, hn1'⟩ := hat1 hρv'' (indec_opow _)
    have e1' : evA ρ (val t1 ρ) + val s'' ρ = e + β'' := by
      have := e1; rw [val_atz] at this; exact opow_inj this
    have hnn : val t1 ρ = n := evA_bracket_eq (by rw [← e1']; exact le_self_add)
      (by rw [← e1']; exact hn1') le_self_add heβ''n
    rw [hnn] at e1'
    have hs'' : val s'' ρ = β'' := (add_left_cancel_iff).1 e1'
    rw [CBz_atz] at c1
    obtain ⟨ct1, c1⟩ := c1
    have cst1 : ∀ c ∈ csz t1, c ∈ Z1 := fun c hc => cs1 c (by rw [csz_atz]; exact List.mem_append_left _ hc)
    have cs1' : ∀ c ∈ csz s'', c ∈ Z1 := fun c hc => cs1 c (by rw [csz_atz]; exact List.mem_append_right _ hc)
    -- the bases of `t1` and `se` agree at every copied base
    have hagree : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Z1 ⊆ A → ↑Ze ⊆ A → ImgCtx ρ A f →
        val t1 (f ρ) = val se (f ρ) := by
      intro A f hZ1 hZe C
      have hct1 := img_cbz C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
      have hcse' := hcse A f hZe C
      exact (uniZ_eq C.ups h.ρU (h.img_bases C) hct1 hcse').1 (by rw [hnn, ee'])
    rcases eq_or_ne (lg β) 0 with hz0 | hz0
    · -- `β = β'' + 1`
      have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
      have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
      refine ⟨insert v W1, insert 1 Z1, t1, sm s'' (cst 1),
        ⟨(w1.insZ h1ρ).insW hρv'.le hvδ (Or.inl (indec_opow _)), CBz_atz.2 ⟨ct1, c1, h1ρ⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩, hnn,
        by rw [val_sm, val_cst, hs'', hβs]⟩
      · intro c hc
        rw [csz_atz] at hc
        simp only [csz, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc | rfl
        · exact Finset.mem_insert_of_mem (cst1 c hc)
        · exact Finset.mem_insert_of_mem (cs1' c hc)
        · exact Finset.mem_insert_self _ _
      · rw [val_atz, val_sm, val_cst, hs'', hnn, ← hβs]
      intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hvA : v ∈ A := hW (by simp)
      have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
      have hb := b1 A f hW1 hZ1 C
      rw [val_atz] at hb
      have hlt : f v'' < f v := C.mono h1A hvA hv''v
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
      rw [hc] at hlt
      rw [val_atz, val_sm, val_cst, hc, ← add_assoc]
      have h3 : evA (f ρ) (val t1 (f ρ)) + val s'' (f ρ) < c :=
        (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
      exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
    -- `β = β'' + ω^z`, `z > 0`
    set z := lg β with hzdef
    have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
    have hzv : z < v := lt_of_le_of_lt (hzβ.trans le_add_self) hβv
    have hzδ : z < δ := hzv.trans hvδ
    have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
    obtain ⟨⟨W3, Z3, sz, ⟨w3, c3, cs3, e3, m3, b3⟩, -⟩, -⟩ := IH z hzv (hzv.trans hv)
    have hsrc : le1 v (v + z) :=
      h.src_gen hz0 (lt_of_lt_of_le heE.pos le_self_add).ne' (dvdE heE hβ0 hdβ) hzv.le hρv'
        (hδI.add_lt hvδ hzδ).le
    have hvzδ : v + z < δ := hδI.add_lt hvδ hzδ
    have hzvz : z < v + z := lt_of_lt_of_le hzv le_self_add
    have hvvz : v < v + z := lt_add_of_pos_right v hz0'
    have hev' : e < v := lt_of_lt_of_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)) hβv.le
    have heδ : e < δ := hev'.trans hvδ
    -- the bound of a copy that is a `υ`-point
    have hups : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ImgCtx ρ A f → v ∈ A →
        e ∈ A → evA (f ρ) (val t1 (f ρ)) ≤ f e → UpsPt (f v) → CBz t1 (f ρ) → ∀ s' : TZ,
        CBz s' (f ρ) → val (atz t1 s') ρ < evA ρ (val t1 ρ + 1) → val (atz t1 s') (f ρ) ≤ f v := by
      intro A f C hvA heA hfe hU hct s' hs' hlt
      have hB := h.img_bases C
      have h1f : (1 : Ordinal.{0}) < f ρ := one_lt_of_upsPt C.ups
      have hlt' := (uniZ_lt C.ups h.ρU hB (t := atz t1 s') (u := ee (sm t1 (cst 1)))
        (CBz_atz.2 ⟨hct, hs'⟩) ⟨hct, h1f⟩).1 (by rw [val_ee, val_sm, val_cst]; exact hlt)
      rw [val_ee, val_sm, val_cst] at hlt'
      have hfev : f e < f v := C.mono heA hvA hev'
      have hge : evA (f ρ) (val t1 (f ρ) + 1) ≤ f v := by
        rw [evA_add_one]; exact eN_le (lt_of_le_of_lt hfe hfev) (upsPt_inE hU)
      exact (hlt'.trans_le hge).le
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
      refine ⟨insert (v + z) (insert v Wx), Z0, t1, pw sz, ⟨wzf, CBz_atz.2 ⟨ct1, c3⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩, hnn,
        by rw [val_pw, e3, hβz]⟩
      · intro c hc
        rw [csz_atz] at hc
        simp only [csz, List.mem_append] at hc
        rcases hc with hc | hc
        · exact Finset.mem_insert_of_mem (by simp [cst1 c hc])
        · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
      · rw [val_atz, val_pw, e3, hnn, ← hβz]
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
      have hct1 : CBz t1 (f ρ) := img_cbz C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
      have hfe : evA (f ρ) (val t1 (f ρ)) ≤ f e := by
        rw [hagree A f hZ1 hZe C]; exact ie A f hWe hZe C
      have hfev : f e < f v := C.mono heA hvA hev'
      have hcs : ∀ c ∈ csz sz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc))
      have hCB : CBz sz (f ρ) := img_cbz C c3 hcs
      by_cases hU : UpsPt (f v)
      · refine hups A f C hvA heA hfe hU hct1 (pw sz) hCB ?_
        rw [val_atz, val_pw, e3, hnn, ← hβz]
        have hE2 : ω ^ eN e = eN e := eN_E e
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2
          (show e + β < eN e by rw [hnext]; exact hβn)
        rw [hE2, hnext] at h1
        exact h1
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      rw [val_atz, val_pw, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
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
            exact h.copy_atom C heA hzA hezA hz0 hze h0A hsrce
        have hfE : ω ^ evA (f ρ) (val t1 (f ρ)) = evA (f ρ) (val t1 (f ρ)) := evA_E _ _
        have hcl : evA (f ρ) (val t1 (f ρ)) ≤ c := by
          rw [hc, ← hfE] at hfe; exact (opow_le_opow_iff_right one_lt_omega0).1 hfe
        have hca : c < a := by
          have := hfev; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
        exact (add_le_add hcl htw).trans (dvd_next hda hdc hca)
      · push Not at hze
        have hfz : f e < f z := C.mono heA hzA hze
        have h1 : evA (f ρ) (val t1 (f ρ)) < ω ^ f z :=
          lt_of_le_of_lt hfe (hfz.trans_le (right_le_opow _ one_lt_omega0))
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, opow_zero] at ha
          have : (1 : Ordinal.{0}) < f v := lt_of_le_of_lt (one_le_iff_pos.2
            (evA_E (f ρ) (val t1 (f ρ))).pos) (lt_of_le_of_lt hfe hfev)
          rw [ha] at this; exact lt_irrefl _ this
        have h2 : evA (f ρ) (val t1 (f ρ)) + ω ^ val sz (f ρ) ≤ ω ^ f z := by
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
      refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, t1, sm s'' (pw sz),
        ⟨wzf, CBz_atz.2 ⟨ct1, c1, c3⟩, ?_, ?_,
        Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩, hnn,
        by rw [val_sm, val_pw, hs'', e3, ← hgs]⟩
      · intro c hc
        rw [csz_atz] at hc
        simp only [csz, List.mem_append] at hc
        rcases hc with hc | hc | hc
        · exact Finset.mem_insert_of_mem (by simp [cst1 c hc])
        · exact Finset.mem_insert_of_mem (by simp [cs1' c hc])
        · exact Finset.mem_insert_of_mem (by simp [cs3 c hc])
      · rw [val_atz, val_sm, val_pw, hs'', e3, hnn, ← hgs]
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
      rw [val_atz] at hb''
      have hbz : val sz (f ρ) ≤ f z := b3 A f hW3 hZ3 C
      have htw : ω ^ val sz (f ρ) ≤ ω ^ f z := (opow_le_opow_iff_right one_lt_omega0).2 hbz
      have hct1 : CBz t1 (f ρ) := img_cbz C ct1 (fun c hc => hZ1 (Finset.mem_coe.2 (cst1 c hc)))
      have hfe : evA (f ρ) (val t1 (f ρ)) ≤ f e := by
        rw [hagree A f hZ1 hZe C]; exact ie A f hWe hZe C
      have hcs1 : ∀ c ∈ csz s'', c ∈ A := fun c hc => hZ1 (Finset.mem_coe.2 (cs1' c hc))
      have hcs3 : ∀ c ∈ csz sz, c ∈ A := fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc))
      have hCB : CBz (sm s'' (pw sz)) (f ρ) := ⟨img_cbz C c1 hcs1, img_cbz C c3 hcs3⟩
      by_cases hU : UpsPt (f v)
      · refine hups A f C hvA heA hfe hU hct1 (sm s'' (pw sz)) hCB ?_
        rw [val_atz, val_sm, val_pw, hs'', e3, hnn, ← hgs]
        have hE2 : ω ^ eN e = eN e := eN_E e
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2
          (show e + β < eN e by rw [hnext]; exact hβn)
        rw [hE2, hnext] at h1
        exact h1
      obtain ⟨c, hc, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzvb.le h0A hsrc''
      have hbc : evA (f ρ) (val t1 (f ρ)) + val s'' (f ρ) ≤ c := by
        rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
      have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
      obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
      have hca : c < a := by
        have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      rw [val_atz, ha]
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      rw [val_sm, val_pw, ← add_assoc]
      exact (add_le_add hbc htw).trans (dvd_next hda hdc hca)
  · -- a decomposable value: a sum
    have hD : DecompR0 v := not_not.1 hI
    rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
    · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
    obtain ⟨⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, -⟩, -⟩ := IH u1 hu1 (hu1.trans hv)
    obtain ⟨⟨W2, Z2, s2, ⟨w2, c2, cs2, e2, m2, b2⟩, -⟩, -⟩ := IH u2 hu2 (hu2.trans hv)
    subst hsum
    have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
      intro x hx
      rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
    refine ⟨insert (u1 + u2) (W1 ∪ W2), Z1 ∪ Z2, sm s1 s2,
      ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2,
        rfl⟩), ⟨c1, c2⟩, ?_, by simp [e1, e2], by simp, ?_⟩, fun _ hI' => absurd hI' hI⟩
    · intro c hc
      simp only [csz, List.mem_append] at hc
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

/-- **The IMG package of a term of `TZ`** (constants below `ρ`, value `≥ 1`). -/
theorem pkgZ {s : TZ} (hs : CBz s ρ) (h1 : 1 ≤ val s ρ) : ImgPkg ρ δ (val s) := by
  classical
  have hvN := valZ_lt h.ρE s hs
  obtain ⟨⟨W, Z, s0, ⟨w, c0, cs0, e0, m0, b0⟩, -⟩, -⟩ := h.imgZ (val s ρ) hvN
  have wzc : WZ ρ δ ∅ (csz s).toFinset :=
    ⟨by simp, fun z hz => (cbz_iff s ρ).1 hs z (List.mem_toFinset.1 hz), by simp⟩
  have hw' := w.union wzc
  rw [Finset.union_empty] at hw'
  refine ⟨h1, hvN.trans_le h.evZ_le_δ, W, Z ∪ (csz s).toFinset, hw', ?_, ?_⟩
  · rcases Finset.mem_union.1 m0 with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  · intro A f hW hZ C
    have hZ0 : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hcs : ∀ c ∈ csz s, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcs0 : ∀ c ∈ csz s0, c ∈ A := fun c hc => hZ0 (Finset.mem_coe.2 (cs0 c hc))
    have hB := h.img_bases C
    have heq := (uniZ_eq C.ups h.ρU hB (img_cbz C hs hcs) (img_cbz C c0 hcs0)).1 e0.symm
    rw [heq]
    exact b0 A f hW hZ0 C

end RstK

end Googology.Trans.PoR.InaccPsi.R2
