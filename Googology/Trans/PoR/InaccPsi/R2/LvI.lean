import Googology.Trans.PoR.InaccPsi.R2.LvTm
import Googology.Trans.PoR.InaccPsi.R2.LvTh
import Googology.Trans.PoR.InaccPsi.R2.LuI

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal

namespace Lv

/-- The IMG invariant for a represented value of `LvT`. -/
def LvImg (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : LvT) : Prop :=
  WZ ρ δ W Z ∧ LvT.CBt s ρ ∧ (∀ c ∈ LvT.cs s, c ∈ Z) ∧ LvT.val s ρ = v ∧
    v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}),
      ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f → LvT.val s (f ρ) ≤ f v

/-- All explicit constants and level parameters in `LvT` are below the base. -/
theorem cbt_cst {ρ : Ordinal.{0}} {s : LvT} (hs : LvT.CBt s ρ) :
    ∀ c ∈ LvT.cs s, c < ρ := by
  induction s with
  | cst a => intro c hc; simp [LvT.cs] at hc; subst c; exact hs
  | bs => intro c hc; simp [LvT.cs] at hc
  | th0 b t ih =>
      intro c hc
      simp only [LvT.cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.2.1
      · exact ih hs.2.2 c hc
  | th b t ih =>
      intro c hc
      simp only [LvT.cs, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hs.1
      · exact ih hs.2 c hc
  | sm a b iha ihb =>
      intro c hc
      simp only [LvT.cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact iha hs.1 c hc
      · exact ihb hs.2 c hc
  | pw t ih => intro c hc; exact ih hs c (by simpa [LvT.cs] using hc)

/-- Rebase the term side condition along a covering copy. -/
theorem cbt_img {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {s : LvT} (hs : LvT.CBt s ρ) (hA : ∀ c ∈ LvT.cs s, c ∈ A) :
    LvT.CBt s (f ρ) := by
  induction s with
  | cst a => exact C.above a (hA a (by simp [LvT.cs])) hs
  | bs => trivial
  | th0 b t ih =>
      refine ⟨hs.1, C.above b (hA b (by simp [LvT.cs])) hs.2.1, ?_⟩
      exact ih hs.2.2 (fun c hc => hA c (by simp [LvT.cs, hc]))
  | th b t ih =>
      refine ⟨C.above b (hA b (by simp [LvT.cs])) hs.1, ?_⟩
      exact ih hs.2 (fun c hc => hA c (by simp [LvT.cs, hc]))
  | sm a b iha ihb =>
      exact ⟨iha hs.1 (fun c hc => hA c (by simp [LvT.cs, hc])),
        ihb hs.2 (fun c hc => hA c (by simp [LvT.cs, hc]))⟩
  | pw t ih => exact ih hs (fun c hc => hA c (by simp [LvT.cs, hc]))

/-- A term with an IMG witness gives the generic package required by `XtSys`. -/
theorem pkg_of_img {ρ δ : Ordinal.{0}} {s : LvT} {W Z : Finset Ordinal.{0}}
    (h : LvImg ρ δ (LvT.val s ρ) W Z s) (h1 : 1 ≤ LvT.val s ρ)
    (hδ : LvT.val s ρ < δ) : ImgPkg ρ δ (LvT.val s) := by
  classical
  rcases h with ⟨hwz, hCB, hcs, hv, hmem, hcopy⟩
  have hwzc : WZ ρ δ ∅ (LvT.cs s).toFinset :=
    ⟨by simp, fun c hc => cbt_cst hCB c (List.mem_toFinset.1 hc), by simp⟩
  have hwz' : WZ ρ δ W (Z ∪ (LvT.cs s).toFinset) := by
    simpa using hwz.union hwzc
  refine ⟨h1, hδ, W, Z ∪ (LvT.cs s).toFinset, hwz', ?_, ?_⟩
  · rcases Finset.mem_union.1 hmem with hm | hm
    · exact Finset.mem_union_left _ hm
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
  · intro A f hW hZ C
    have hZ' : ↑Z ⊆ A := fun z hz => hZ (by simp [Finset.mem_coe.1 hz])
    have hcsA : ∀ c ∈ LvT.cs s, c ∈ A := fun c hc => hZ (by simp [hc])
    have hcopy' := hcopy A f hW hZ' C
    rw [hv]
    exact hcopy'

/-- A constant below the restart has an IMG witness. -/
theorem img_cst {ρ δ a : Ordinal.{0}} (ha : a < ρ) :
    LvImg ρ δ a ∅ {a} (.cst a) := by
  refine ⟨WZ.empty.insZ ha, ha, ?_, rfl, by simp, ?_⟩
  · intro c hc
    simp [LvT.cs] at hc
    subst c
    simp
  · intro A f hW hZ C
    have haA : a ∈ A := hZ (by simp)
    rw [LvT.val_cst, C.fix a haA ha]

/-- The current base has an IMG witness as the base term. -/
theorem img_bs {ρ δ : Ordinal.{0}} (hρE : InE ρ) (hρδ : ρ < δ) :
    LvImg ρ δ ρ {ρ} ∅ .bs := by
  refine ⟨(WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl hρδ
      (Or.inl (inE_indec hρE)), trivial, ?_, rfl, by simp, ?_⟩
  · intro c hc
    simp [LvT.cs] at hc
  · intro A f hW hZ C
    rfl

end Lv

namespace LvK

/-- Split a represented level between `y` and the base-dependent offset. -/
theorem lvLevel_split {y b q : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (hb : b < y)
    (hyq : y ≤ q) (hqb : q ≤ y + b) :
    ∃ c, c = q - y ∧ y + c = q ∧ c ≤ b ∧ c < y ∧ c ∈ Tset y := by
  let c := q - y
  have hrep : y + c = q := Ordinal.add_sub_cancel_of_le hyq
  have hcb : c ≤ b := by
    apply (add_le_add_iff_left y).1
    rw [hrep]
    exact hqb
  have hcy : c < y := hcb.trans_lt hb
  exact ⟨c, rfl, hrep, hcb, hcy, mem_T_of_le hy hy1 hcy.le⟩

/-- A term below a base-dependent theta value cannot have a level above its target level. -/
theorem lvRep_level_le {y a β r : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1)
    (hβ : β ∈ Tset y) (hyβ : y ≤ β) (hβ1 : β < Om1)
    (hr : r ∈ Tset y) (hr1 : r < Om1)
    (haT : a ∈ Tset y) (hya : y < a) (ha1 : a < Om1) (haE : InE a)
    (hβa : β < a) (hr'a : r < a) (hlt : a < vt y (Om1 * β + r)) :
    ∃ q s, 1 ≤ q ∧ q ∈ Tset y ∧ s ∈ Tset y ∧ s < Om1 ∧
      a = vt y (Om1 * q + s) ∧ q ≤ β := by
  obtain ⟨ξ, hξT, hξ2, hξa⟩ := vt_rep hy hy1 haT hya.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hy hy1 hξT hξ2).1
    ⟨by rw [hξa]; exact hya, by rw [hξa]; exact haE⟩
  obtain ⟨hqPos, hsT, hs1, hdec⟩ := Lu.lu_split hy hy1 hξT hξ2 hΩξ
  have hξlt : ξ < Om1 * β + r :=
    lvLt_of_vt_lt hy hy1 hξT hξ2 hβ hyβ hβ1 hr hr1
      (by rw [hξa]; exact hr'a) (by rw [hξa]; exact hβa) (by rw [hξa]; exact hlt)
  have hqβ : ξ / Om1 ≤ β := by
    have hmul : Om1 * (ξ / Om1) < Om1 * (β + 1) := by
      calc
        Om1 * (ξ / Om1) ≤ ξ := mul_div_le ξ Om1
        _ < Om1 * β + r := hξlt
        _ < Om1 * β + Om1 := (add_lt_add_iff_left _).2 hr1
        _ = Om1 * (β + 1) := by rw [mul_add_one]
    exact Order.lt_add_one_iff.1 ((mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 hmul)
  exact ⟨ξ / Om1, ξ % Om1, hqPos, vz_T_down hy hy1 hβ hβ1 hqβ, hsT, hs1, by rw [hdec, hξa], hqβ⟩

/-- The base-dependent analogue of `Lu.luCore` for levels `y+b`, `b<y`. -/
theorem lvCore {y a b r' g : Ordinal.{0}} (hy : InE y) (hy1 : y < Om1) (hb : b < y)
    (hr'T : r' ∈ Tset y) (hr'1 : r' < Om1)
    (haT : a ∈ Tset y) (hya : y < a) (ha1 : a < Om1) (haE : InE a)
    (hr'a : r' < a) (hg : le1R a g) (hLg : Lv.L y b a ≤ g)
    (hlt : a < vt y (Om1 * (y + b) + r')) :
    ∃ s, s ∈ Tset y ∧ s < Om1 ∧ s < r' ∧
      vt y (Om1 * (y + b) + s) = a ∧ g ≤ Lv.L y b a + luZeta y (y + b) s := by
  have hβT : y + b ∈ Tset y := vzT_add hy hy1
    (mem_T_of_le hy hy1 le_rfl) (mem_T_of_le hy hy1 hb.le)
  have hβy : y ≤ y + b := le_self_add
  have hβ1 : y + b < Om1 := Om1_add_lt hy1 (hb.trans hy1)
  obtain ⟨q, s, hq1, hqT, hsT, hs1, hase, hqβ⟩ :=
    lvRep_level_le hy hy1 hβT hβy hβ1 hr'T hr'1 haT hya ha1 haE
      ((inE_indec haE).add_lt hya (hb.trans hya)) hr'a hlt
  have hhs : s < a := by
    rcases lt_or_ge q y with hqy | hyq
    · have h := (Lu.lu_th_facts hy hy1 hq1 hqy hsT hs1).2.2.2.2.2.2.2
      rw [← hase] at h
      simpa using h
    · have hqBound : q < Om1 := lt_of_le_of_lt hqβ hβ1
      have h := lvLevel_lt_vt hy hy1 hqT hyq hqBound hsT hs1
      rw [← hase] at h
      exact h.2
  have hζ : luZeta y q s < a := Lu.lu_zeta_le.trans_lt hhs
  rcases lt_or_ge q y with hqy | hyq
  · have hreach := Lu.lu_lh_th hy hy1 hq1 hqy hsT hs1
    rw [← hase] at hreach
    have hgle := hreach.2 g hg
    have hsmall := Lu.lu_luL_lt_mul haE hy hqy hya hζ
    have hbase : a * y ≤ Lv.L y b a := by
      unfold Lv.L
      exact le_self_add.trans le_self_add
    exfalso
    exact (not_lt_of_ge hLg) (hgle.trans_lt (hsmall.trans_le hbase))
  · obtain ⟨c, -, hqc, hcb, hcy, hcT⟩ := LvK.lvLevel_split hy hy1 hb hyq hqβ
    have hreach := Lv.lh_th_L hy hy1 hcy hsT hs1
    rw [hqc, ← hase] at hreach
    have hgle := hreach.2 g hg
    by_cases hcb' : c < b
    · have hstep : a * c + luZeta y (y + c) s < a * b := by
        calc
          a * c + luZeta y (y + c) s < a * c + a :=
            (add_lt_add_iff_left _).2 (Lu.lu_zeta_le.trans_lt hhs)
          _ = a * (c + 1) := by rw [mul_add, mul_one]
          _ ≤ a * b := mul_le_mul_right (Order.add_one_le_of_lt hcb') a
      have hreachLt : Lv.L y c a + luZeta y (y + c) s < Lv.L y b a := by
        unfold Lv.L
        calc
          (a * y + y) + a * c + luZeta y (y + c) s =
              (a * y + y) + (a * c + luZeta y (y + c) s) := by rw [add_assoc]
          _ < (a * y + y) + a * b := (add_lt_add_iff_left _).2 hstep
      exfalso
      rw [← hqc] at hgle
      exact (not_lt_of_ge hLg) (hgle.trans_lt hreachLt)
    · have hcbEq : c = b := le_antisymm hcb (le_of_not_gt hcb')
      have hqeq : q = y + b := by rw [hcbEq] at hqc; exact hqc.symm
      have hqLt : q < a := by
        have hqBound : q < Om1 := lt_of_le_of_lt hqβ hβ1
        have h := lvLevel_lt_vt hy hy1 hqT hyq hqBound hsT hs1
        rw [← hase] at h
        exact h.1
      have hβa : y + b < a := by rw [← hqeq]; exact hqLt
      have hqBound : q < Om1 := lt_of_le_of_lt hqβ hβ1
      have hargT := lvArg_mem hy hy1 hqT hyq hqBound hsT hs1
      have harg2 := Lu.luOm1_mul_lt hqBound hs1
      have hlt' : vt y (Om1 * q + s) < vt y (Om1 * (y + b) + r') := by
        rw [← hase]
        exact hlt
      have hξlt : Om1 * q + s < Om1 * (y + b) + r' := by
        exact lvLt_of_vt_lt hy hy1 hargT harg2 hβT hβy hβ1 hr'T hr'1
          (by rw [← hase]; exact hr'a) (by rw [← hase]; exact hβa) hlt'
      rw [hqeq] at hξlt
      have hsr : s < r' := (add_lt_add_iff_left _).1 hξlt
      refine ⟨s, hsT, hs1, hsr, ?_, ?_⟩
      · rw [← hqeq, ← hase]
      · rw [hcbEq, hqeq] at hgle
        exact hgle


end LvK

namespace LvK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- Transport an old constant-level IMG witness into the extended syntax. -/
theorem lvImg_of_lu {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : Lu.LuT}
    (hi : Lu.LuImg ρ δ v W Z t) :
    Lv.LvImg ρ δ v W Z (ofLu t) := by
  rcases hi with ⟨hwz, hcb, hcs, hv, hm, hcopy⟩
  refine ⟨hwz, ofLu_cb hcb, ?_, ?_, hm, ?_⟩
  · intro c hc
    rw [ofLu_cs] at hc
    exact hcs c hc
  · rw [ofLu_val, hv]
  · intro A f hW hZ C
    rw [ofLu_val]
    exact hcopy A f hW hZ C

/-- Every value below the old constant-level top keeps its IMG witness in the extended grammar. -/
theorem lvImg_below_luTop {v : Ordinal.{0}} (hv : v < Lu.luTop ρ) :
    ∃ W Z s, Lv.LvImg ρ δ v W Z s := by
  obtain ⟨W, Z, t, hi⟩ := (Lu.LuK.imgLu h v hv).1
  exact ⟨W, Z, ofLu t, lvImg_of_lu h hi⟩

/-- IMG is closed under ordinal addition when the two summands already have witnesses. -/
theorem lvImg_sm {u1 u2 v : Ordinal.{0}} (hρv : ρ ≤ v) (hvδ : v < δ)
    (hu1 : u1 < v) (hu2 : u2 < v) {W1 Z1 W2 Z2 : Finset Ordinal.{0}}
    {s1 s2 : LvT} (h1 : Lv.LvImg ρ δ u1 W1 Z1 s1) (h2 : Lv.LvImg ρ δ u2 W2 Z2 s2)
    (hsum : u1 + u2 = v) :
    ∃ W Z s, Lv.LvImg ρ δ v W Z s := by
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
    simp only [LvT.cs, List.mem_append] at hc
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
    rw [LvT.val_sm, ← hadd]
    exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- An epsilon value can be represented by an exponential term with the IMG epsilon base. -/
theorem lvImg_E {v : Ordinal.{0}} (hρv : ρ ≤ v) (hvE : InE v) (hvδ : v < δ)
    {W Z : Finset Ordinal.{0}} {s : LvT} (hI : Lv.LvImg ρ δ v W Z s) :
    ∃ W' Z' se s', Lv.LvImg ρ δ v W' Z' (.pw (.sm se s')) ∧
      InE (LvT.val se ρ) ∧ LvT.val se ρ + LvT.val s' ρ < eN (LvT.val se ρ) := by
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
    by rw [e, LvT.val_cst, add_zero]; exact lt_eN v⟩
  · intro c hc
    simp only [LvT.cs, List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact Finset.mem_insert_of_mem (hcs c hc)
    · exact Finset.mem_insert_self _ _
  · rw [LvT.val_pw, LvT.val_sm, LvT.val_cst, add_zero, e]
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
    rw [LvT.val_pw, LvT.val_sm, LvT.val_cst, add_zero]
    have hh := (opow_le_opow_iff_right one_lt_omega0).2 hbv
    rwa [show ω ^ f v = f v from hfE] at hh

/-- A witness set for the block `v·(ρ+b)` of a base-dependent level. -/
theorem lvWitL {v b : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ)
    (hb : b < ρ) :
    ∃ W Z : Finset Ordinal.{0}, v * (ρ + b) ∈ W ∧ v ∈ W ∧ WZ ρ δ W Z ∧
      Lv.L ρ b v ∈ W ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → InE (f v) →
          f v * f ρ + f ρ + f v * b ≤ f (Lv.L ρ b v) := by
  classical
  let Ws : Finset Ordinal.{0} := {ρ, v, v * ρ, v * ρ + ρ}
  let Zs : Finset Ordinal.{0} := ∅
  obtain ⟨hWZs, hIs⟩ := Lu.LuK.luWitSq h hvE hρv hvδ
  have hVs : v * ρ ∈ Ws := by simp [Ws]
  have hV : v ∈ Ws := by simp [Ws]
  obtain ⟨Wm, Zm, hVm, hVmV, hWmBounds, hZmBounds, hclm, hIm⟩ :=
    Lu.LuK.luWitMul h hvE hρv.le hvδ b hb
  have hWZm : WZ ρ δ Wm Zm := ⟨hWmBounds, hZmBounds, hclm⟩
  let Z := insert b (insert 0 (Zs ∪ Zm))
  let W0 := Ws ∪ Wm
  have hWZ0 : WZ ρ δ W0 Z := by
    have hw := hWZs.union hWZm
    have hw0 : WZ ρ δ W0 (Zs ∪ Zm) := by
      simpa [W0, Ws, Zs, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hw
    have hwz0 := hw0.insZ h.ρE.pos
    have hwzb := hwz0.insZ hb
    simpa [Z] using hwzb
  have hβδ : ρ + b < δ :=
    (inE_indec h.δE).add_lt h.ρδ (lt_of_lt_of_le hb h.ρδ.le)
  have hPδ : v * (ρ + b) < δ := h.δE.mul_lt hvδ hβδ
  have hvρ : ρ ≤ v * ρ := hρv.le.trans (le_mul_left v h.ρE.pos)
  have hvb : v * b ∈ W0 ∪ Z := by
    by_cases hb0 : b = 0
    · simp [W0, Z, hb0]
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hVm hb0))
  have hsum : v * ρ + v * b = v * (ρ + b) := (mul_add _ _ _).symm
  have hρL : ρ ≤ v * (ρ + b) := by rw [← hsum]; exact hvρ.trans le_self_add
  let U := v * ρ + ρ
  let V := v * b
  have hUρ : ρ ≤ U := hvρ.trans le_self_add
  have hUδ : U < δ := (inE_indec h.δE).add_lt (h.δE.mul_lt hvδ h.ρδ) h.ρδ
  have hVδ : V < δ := by
    by_cases hb0 : b = 0
    · simpa [V, hb0] using h.δE.pos
    · exact (mul_lt_mul_of_pos_left hb hρv.pos).trans
        (h.δE.mul_lt hvδ h.ρδ)
  have hReachδ : Lv.L ρ b v < δ := by
    unfold Lv.L
    exact (inE_indec h.δE).add_lt hUδ hVδ
  have hwzP : WZ ρ δ (insert (v * (ρ + b)) W0) Z := by
    by_cases hb0 : b = 0
    · have hρL0 : ρ ≤ v * ρ := hvρ
      have hInd : Indec (v * ρ) := by
        have hvω : ω ^ v = v := hvE
        have hρω : ω ^ ρ = ρ := h.ρE
        have he : v * ρ = ω ^ (v + ρ) := by rw [opow_add, hvω, hρω]
        rw [he]
        exact indec_opow _
      simpa [hb0] using hWZ0.insW hρL0 (by simpa [hb0] using hPδ) (Or.inl hInd)
    · have hvbpos : 0 < v * b := mul_pos hρv.pos (pos_iff_ne_zero.2 hb0)
      have hvbLt : v * b < v * ρ := mul_lt_mul_of_pos_left hb hρv.pos
      have huLt : v * ρ < v * ρ + v * b := lt_add_of_pos_right _ hvbpos
      have hvLt : v * b < v * ρ + v * b := lt_of_lt_of_le hvbLt le_self_add
      exact hWZ0.insW hρL hPδ
        (Or.inr ⟨v * ρ, Finset.mem_union_left _ (Finset.mem_union_left _ hVs), v * b, hvb,
          by rw [← hsum]; exact huLt, by rw [← hsum]; exact hvLt, hsum⟩)
  have hwzL : WZ ρ δ (insert (Lv.L ρ b v) (insert (v * (ρ + b)) W0)) Z := by
    by_cases hb0 : b = 0
    · have hEq : Lv.L ρ b v = v * ρ + ρ := by simp [Lv.L, hb0]
      have hPmem0 : v * ρ ∈ W0 := by
        change v * ρ ∈ Ws ∪ Wm
        exact Finset.mem_union_left Wm hVs
      have hUmem0 : U ∈ W0 := by simp [U, W0, Ws]
      have hP0 : v * (ρ + b) = v * ρ := by simp [hb0]
      rw [hEq, hP0, Finset.insert_eq_of_mem hPmem0, Finset.insert_eq_of_mem hUmem0]
      exact hWZ0
    · have hVpos : 0 < V := mul_pos hρv.pos (pos_iff_ne_zero.2 hb0)
      have hVle : V < v * ρ := mul_lt_mul_of_pos_left hb hρv.pos
      have hUL : U < Lv.L ρ b v := by
        change U < U + V
        exact lt_add_of_pos_right _ hVpos
      have hVL : V < Lv.L ρ b v := hVle.trans_le (by
        calc
          v * ρ ≤ U := by exact le_self_add
          _ ≤ U + V := le_self_add)
      have hVmemb : V ∈ insert (v * (ρ + b)) W0 ∪ Z := by
        by_cases hVb : V ∈ W0
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hVb)
        · have hVZ : V ∈ Z := by
            rcases Finset.mem_union.1 hvb with h | h
            · exact (hVb h).elim
            · exact h
          exact Finset.mem_union_right _ hVZ
      have hUmem : U ∈ Ws := by simp [U, Ws]
      have hUmemW0 : U ∈ W0 := by change U ∈ Ws ∪ Wm; exact Finset.mem_union_left _ hUmem
      have hUmemP : U ∈ insert (v * (ρ + b)) W0 ∪ Z :=
        Finset.mem_union_left _ (Finset.mem_insert_of_mem hUmemW0)
      exact hwzP.insW (hUρ.trans le_self_add) hReachδ
        (Or.inr ⟨U, hUmemP,
          V, hVmemb, hUL, hVL, by simp [Lv.L, U, V]⟩)
  refine ⟨insert (Lv.L ρ b v) (insert (v * (ρ + b)) W0), Z,
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
    by simp [W0, hV], hwzL,
    Finset.mem_insert_self _ _, ?_⟩
  intro A f hW hZ C hfE
  have hWA : ↑Ws ⊆ A := fun w hw => hW (by simp [W0, hw])
  have hMA : ↑Wm ⊆ A := fun w hw => hW (by simp [W0, hw])
  have hZA : ↑Zm ⊆ A := fun z hz => hZ (by simp [Z, hz])
  have hbA : b ∈ A := hZ (by simp [Z])
  have hvρA : v * ρ ∈ A := hWA hVs
  have hvbA : v * b ∈ A := by
    by_cases hb0 : b = 0
    · simpa [hb0] using hZ (by simp [Z])
    · exact hMA (hVm hb0)
  have hLA : v * (ρ + b) ∈ A := hW (by simp)
  have hLvLA : Lv.L ρ b v ∈ A := hW (by simp)
  have hSq := hIs A f hWA C hfE
  have hvA : v ∈ A := hWA hV
  have hbfv : b < f v := (C.above b hbA hb).trans (C.mono C.rho hvA hρv)
  have hMul := hIm A f hMA hZA C hfE hbfv
  have hsum' : f (v * ρ) + f (v * b) = f (v * (ρ + b)) :=
    C.add (v * ρ) hvρA (v * b) hvbA _ hLA hsum
  have hUA : U ∈ A := hWA (by simp [U, Ws])
  have hVimage : f U + f V ≤ f (Lv.L ρ b v) := by
    have hsumL : U + V = Lv.L ρ b v := by rfl
    have hAdd := C.add U hUA V hvbA _ hLvLA hsumL
    exact hAdd.le
  have hUimage : f v * f ρ + f ρ ≤ f U := by
    have hρA : ρ ∈ A := hWA (by simp [Ws])
    have hadd : v * ρ + ρ = U := rfl
    have hAdd := C.add (v * ρ) hvρA ρ hρA _ hUA hadd
    exact (add_le_add_left hSq (f ρ)).trans_eq hAdd
  calc
    f v * f ρ + f ρ + f v * b ≤ f U + f v * b :=
      add_le_add_left hUimage (f v * b)
    _ ≤ f U + f (v * b) := add_le_add_right hMul (f U)
    _ = f U + f V := by rfl
    _ ≤ f (Lv.L ρ b v) := hVimage


/-- Fixed-point transfer for a theta level that follows the changing base. -/
theorem lvFixTransfer {σ γ b : Ordinal.{0}} (hB : Bases σ ρ) (hb : b < σ)
    (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1)
    (hfix : ∀ s, s < γ → vt ρ (Om1 * (ρ + b) + s) ≤ γ) :
    ∀ s, s < pi σ ρ γ → vt σ (Om1 * (σ + b) + s) ≤ pi σ ρ γ := by
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
  obtain ⟨hvTB, hpv⟩ := LvT.pi_vt_high hB hb hs'TB hs'1
  have hh := ((pi_bijOn hB).2.le_iff_le hvTB hγ).2 (hfix s' hs'γ)
  rwa [hpv, hs'e] at hh

/-- The fixed-point remainder case for a base-dependent theta term. -/
theorem lvImg_th_fixed {b r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hζ : luZeta ρ (ρ + b) r = 0)
    (hfix : ∀ s, s < r → vt ρ (Om1 * (ρ + b) + s) ≤ r)
    (hve : vt ρ (Om1 * (ρ + b) + r) = v) (hvB : v < lvTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, Lv.LvImg ρ δ u W Z s) :
    ∃ W Z s, Lv.LvImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, hvT, hρv, -, hvE, -, hrTheta⟩ :=
    Lv.th_facts (τ := ρ) (b := b) (η := r) hρE hρ1 hb hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hvT hρv hvE
  have hvδ : v < δ := hvB.trans (LvT.lvTop_lt_next (x := ρ) hρE hρ1 h.ρδ h.next.2.1.2)
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  let L := Lv.L ρ b v
  obtain ⟨WL, ZL, -, -, wzL, hLW, IL⟩ := lvWitL h hvE hρv hvδ hb
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (ρ + b) r) := by
    have hh := (Lv.lh_th_L hρE hρ1 hb hrT hr1).1
    simpa [L, hve] using hh
  have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by simpa [hζ] using hsrcR)
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz := ((w1.union wzL).union wzE).insZ hb
  let W : Finset Ordinal := (W1 ∪ WL) ∪ {v, v + v}
  let Z : Finset Ordinal := insert b (Z1 ∪ ZL)
  have hwz' : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz
  refine ⟨W, Z, .th b s1, hwz', ⟨hb, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvT.cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
  · rw [LvT.val_th, e1, hve]
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
    have hcb1y := Lv.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvT.val_th]
    by_cases hU : UpsPt (f v)
    · exact (LvT.lv_lt_ups hyE hy1 (t := .th b s1) ⟨hby, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL' hZL C hfE
    obtain ⟨hs1T, hs1top⟩ := LvT.lv_T hyE hy1 s1 hcb1y
    have hs11 : LvT.val s1 (f ρ) < Om1 := hs1top.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨hθT, hθtop⟩ := LvT.lv_T hyE hy1 (.th b s1) ⟨hby, hcb1y⟩
    have hθ1 : LvT.val (.th b s1) (f ρ) < Om1 := hθtop.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT hθ1 hlt.le
    obtain ⟨s, -, -, hsr, hsa, -⟩ :=
      lvCore hyE hy1 hby hs1T hs11 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hfL hlt
    have hpi := LvT.pi C.ups h.ρU hB s1 hcb1y
    have htr := lvFixTransfer (ρ := ρ) (τ := τ) (δ := δ) h
      (σ := f ρ) (γ := LvT.val s1 ρ) (b := b) hB hby hpi.1 (by rw [e1]; exact hr1)
      (by intro q hq; have hqr : q < r := by simpa [e1] using hq
          calc
            vt ρ (Om1 * (ρ + b) + q) ≤ r := hfix q hqr
            _ = LvT.val s1 ρ := e1.symm) s
      (by rw [hpi.2]; exact hsr)
    rw [hpi.2, hsa] at htr
    exact (not_lt_of_ge htr) (hb1.trans_lt hfrv)

/-- The successor remainder case for a base-dependent theta term. -/
theorem lvImg_th_succ {b r0 r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hr0T : r0 ∈ Tset ρ) (hr01 : r0 < Om1)
    (hrs : r = r0 + 1) (hζ : luZeta ρ (ρ + b) r = 0)
    (hve : vt ρ (Om1 * (ρ + b) + r) = v) (hvB : v < lvTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, Lv.LvImg ρ δ u W Z s) :
    ∃ W Z s, Lv.LvImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, hvT, hρv, hv1, hvE, hvI, hrTheta⟩ :=
    Lv.th_facts (τ := ρ) (b := b) (η := r) hρE hρ1 hb hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hvT hρv hv1 hvE hvI
  have hvδ : v < δ := hvB.trans (LvT.lvTop_lt_next (x := ρ) hρE hρ1 h.ρδ h.next.2.1.2)
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  have hr0r : r0 < r := by rw [hrs]; exact lt_add_of_pos_right _ zero_lt_one
  let v0 := vt ρ (Om1 * (ρ + b) + r0)
  have hv0v : v0 < v := by
    rw [← hve]
    exact Lv.th_lt hρE hρ1 hb hr0T hrT hr1 hr0r hrTheta
  obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
  obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
  let L := Lv.L ρ b v
  obtain ⟨WL, ZL, -, -, wzL, hLW, IL⟩ :=
    lvWitL (ρ := ρ) (τ := τ) (δ := δ) h hvE hρv hvδ hb
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (ρ + b) r) := by
    have hh := (Lv.lh_th_L hρE hρ1 hb hrT hr1).1
    simpa [L, hve] using hh
  have hsrc : le1 v L := (h.lowδ _ _ hρv hLδ.le).2 (by simpa [hζ] using hsrcR)
  have wzE := Lu.LuK.luWZ_E h hvE hρv.le hvδ
  have hwz0 := ((((w1.union w2).union w3).union wzL).union wzE).insZ hb
  let W : Finset Ordinal := (((W1 ∪ W2) ∪ W3) ∪ WL) ∪ {v, v + v}
  let Z : Finset Ordinal := insert b (Z1 ∪ Z2 ∪ Z3 ∪ ZL)
  have hwz : WZ ρ δ W Z := by
    simpa [W, Z, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hwz0
  refine ⟨W, Z, .th b s1, hwz, ⟨hb, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvT.cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (cs1 c hc))))
  · rw [LvT.val_th, e1, hve]
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
    have hcb1y := Lv.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hcb2y := Lv.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
    have hcb3y := Lv.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvT.val_th]
    by_cases hU : UpsPt (f v)
    · exact (LvT.lv_lt_ups hyE hy1 (t := .th b s1) ⟨hby, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hR := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA L hLA hsrc)
    have hfL := IL A f hWL' hZL C hfE
    have hLg : Lv.L (f ρ) b (f v) ≤ f L := by simpa [Lv.L] using hfL
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    obtain ⟨hs1T, hs1top⟩ := LvT.lv_T hyE hy1 s1 hcb1y
    have hs11 : LvT.val s1 (f ρ) < Om1 := hs1top.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    have hθT := LvT.lv_T hyE hy1 (.th b s1) ⟨hby, hcb1y⟩
    have hθ1 : LvT.val (.th b s1) (f ρ) < Om1 := hθT.2.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT.1 hθ1 hlt.le
    obtain ⟨s, hsT, hs1, hsr, hsa, -⟩ :=
      lvCore hyE hy1 hby hs1T hs11 hfvT hyv hfv1 hfE
        (hb1.trans_lt hfrv) hR hLg hlt
    have hsrcopy : LvT.val s1 (f ρ) = LvT.val s3 (f ρ) + 1 := by
      have hc : LvT.CBt (.sm s3 (.cst 1)) (f ρ) := ⟨hcb3y, one_lt_of_upsPt C.ups⟩
      have hh := (LvT.uni_eq C.ups h.ρU hB hcb1y hc).1
        (by rw [LvT.val_sm, LvT.val_cst, e1, e3, hrs])
      simpa [LvT.val_sm, LvT.val_cst] using hh
    have hsle : s ≤ LvT.val s3 (f ρ) := Order.lt_add_one_iff.1 (by rw [hsrcopy] at hsr; exact hsr)
    have hprev : LvT.val (.th b s3) (f ρ) ≤ f v0 := by
      have hh := (LvT.uni_eq C.ups h.ρU hB (show LvT.CBt (.th b s3) (f ρ) from ⟨hby, hcb3y⟩) hcb2y).1
        (by simp [LvT.val_th, e3, e2, v0])
      change vt (f ρ) (Om1 * (f ρ + b) + LvT.val s3 (f ρ)) ≤ f v0
      rw [← LvT.val_th, hh]
      exact hb2
    obtain ⟨hs3T, hs3top⟩ := LvT.lv_T hyE hy1 s3 hcb3y
    have hs31 : LvT.val s3 (f ρ) < Om1 := hs3top.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨-, -, -, -, -, -, -, hηθ⟩ := Lv.th_facts hyE hy1 hby hs3T hs31
    have hmon := Lv.th_le hyE hy1 hby hsT hs3T hs31 hsle hηθ
    have hltContr : f v ≤ f v0 := by rw [hsa] at hmon; exact hmon.trans hprev
    exact (not_lt_of_ge hltContr) hfv0v

/-- The nonzero limit-remainder case for a base-dependent theta term. -/
theorem lvImg_th_limit {b r0 z r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1) (hr0T : r0 ∈ Tset ρ)
    (hrs : r = r0 + ω ^ z) (hz : lg r = z) (hz0 : z ≠ 0)
    (hζ : luZeta ρ (ρ + b) r = lg r)
    (hve : vt ρ (Om1 * (ρ + b) + r) = v) (hvB : v < lvTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, Lv.LvImg ρ δ u W Z s) :
    ∃ W Z s, Lv.LvImg ρ δ v W Z s := by
  classical
  have hρE : InE ρ := upsPt_inE h.ρU
  have hρ1 : ρ < Om1 := h.ρ1
  obtain ⟨-, -, -, hρv, -, hvE, -, hrTheta⟩ :=
    Lv.th_facts (τ := ρ) (b := b) (η := r) hρE hρ1 hb hrT hr1
  have hrv : r < v := by rw [← hve]; exact hrTheta
  rw [hve] at hρv hvE
  have hvδ : v < δ := hvB.trans (LvT.lvTop_lt_next (x := ρ) hρE hρ1 h.ρδ h.next.2.1.2)
  have hrpos : 0 < r := by
    rw [hrs]
    exact lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (opow_pos z omega0_pos))
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hzle : z ≤ r := by simpa [hz] using (lg_le hrne)
  have hzv : z < v := hzle.trans_lt hrv
  have hr0r : r0 < r := by rw [hrs]; exact lt_add_of_pos_right _ (opow_pos z omega0_pos)
  let v0 := vt ρ (Om1 * (ρ + b) + r0)
  have hv0v : v0 < v := by
    rw [← hve]
    exact Lv.th_lt hρE hρ1 hb hr0T hrT hr1 hr0r hrTheta
  obtain ⟨W1, Z1, s1, w1, cb1, cs1, e1, m1, b1⟩ := I1 r hrv
  obtain ⟨W2, Z2, s2, w2, cb2, cs2, e2, m2, b2⟩ := I1 v0 hv0v
  obtain ⟨W3, Z3, s3, w3, cb3, cs3, e3, m3, b3⟩ := I1 r0 (hr0r.trans hrv)
  obtain ⟨W4, Z4, sz, w4, cb4, cs4, e4, m4, b4⟩ := I1 z hzv
  let L := Lv.L ρ b v
  obtain ⟨WL, ZL, -, -, wzL, hLW, IL⟩ := lvWitL h hvE hρv hvδ hb
  have hLδ : L < δ := (wzL.1 L hLW).2
  have hsrcR : le1R v (L + luZeta ρ (ρ + b) r) := by
    have hh := (Lv.lh_th_L hρE hρ1 hb hrT hr1).1
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
    dsimp [L, Lv.L]
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
  refine ⟨W, Z, .th b s1, hwz', ⟨hb, cb1⟩, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [LvT.cs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (by simp [cs1 c hc])
  · rw [LvT.val_th, e1, hve]
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
    have hcb1y := Lv.cbt_img C cb1 (fun c hc => hZ1 (Finset.mem_coe.2 (cs1 c hc)))
    have hcb2y := Lv.cbt_img C cb2 (fun c hc => hZ2 (Finset.mem_coe.2 (cs2 c hc)))
    have hcb3y := Lv.cbt_img C cb3 (fun c hc => hZ3 (Finset.mem_coe.2 (cs3 c hc)))
    have hcb4y := Lv.cbt_img C cb4 (fun c hc => hZ4 (Finset.mem_coe.2 (cs4 c hc)))
    have hb1 := b1 A f hW1 hZ1 C
    have hb2 := b2 A f hW2 hZ2 C
    have hb4 := b4 A f hW4 hZ4 C
    have hfrv : f r < f v := C.mono hrA hvA hrv
    have hfv0v : f v0 < f v := C.mono hv0A hvA hv0v
    have hyv : f ρ < f v := C.mono C.rho hvA hρv
    rw [LvT.val_th]
    by_cases hU : UpsPt (f v)
    · exact (LvT.lv_lt_ups hyE hy1 (t := .th b s1) ⟨hby, hcb1y⟩ hyv hU).le
    have hfE := Lu.LuK.luFE h C hvE hρv.le hvδ hvA hvvA
    have hfLz : f (L + z) = f L + f z := (C.add L hLA z hzA _ hLzA rfl).symm
    have hR : le1R (f v) (f L + f z) := by
      have hh := (C.sk _ (C.low _ hvA) hU _).1 (C.cov1 v hvA _ hLzA hsrc)
      rwa [hfLz] at hh
    have hfL := IL A f hWL' hZL C hfE
    have hLf : Lv.L (f ρ) b (f v) ≤ f L := by simpa [L] using hfL
    have hLg : Lv.L (f ρ) b (f v) ≤ f L + f z := hLf.trans le_self_add
    have hfv1 : f v < Om1 := (C.low v hvA).trans hρ1
    have hsrcopy : LvT.val s1 (f ρ) = LvT.val s3 (f ρ) + ω ^ LvT.val sz (f ρ) := by
      have hc : LvT.CBt (.sm s3 (.pw sz)) (f ρ) := ⟨hcb3y, hcb4y⟩
      have hh := (LvT.uni_eq C.ups h.ρU hB hcb1y hc).1
        (by rw [LvT.val_sm, LvT.val_pw, e1, e3, e4, hrs])
      simpa [LvT.val_sm, LvT.val_pw] using hh
    have hprev : LvT.val (.th b s3) (f ρ) ≤ f v0 := by
      have hh := (LvT.uni_eq C.ups h.ρU hB
        (show LvT.CBt (.th b s3) (f ρ) from ⟨hby, hcb3y⟩) hcb2y).1
        (by simp [LvT.val_th, e3, e2, v0])
      have hh' : vt (f ρ) (Om1 * (f ρ + b) + LvT.val s3 (f ρ)) = s2.val (f ρ) := by
        simpa [LvT.val_th] using hh
      change vt (f ρ) (Om1 * (f ρ + b) + LvT.val s3 (f ρ)) ≤ f v0
      rw [hh']
      exact hb2
    obtain ⟨hs1T, hs1top⟩ := LvT.lv_T hyE hy1 s1 hcb1y
    have hs11 : LvT.val s1 (f ρ) < Om1 := hs1top.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨hs3T, hs3top⟩ := LvT.lv_T hyE hy1 s3 hcb3y
    have hs31 : LvT.val s3 (f ρ) < Om1 := hs3top.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    obtain ⟨hθT, hθtop⟩ := LvT.lv_T hyE hy1 (.th b s1) ⟨hby, hcb1y⟩
    have hθ1 : LvT.val (.th b s1) (f ρ) < Om1 := hθtop.trans (LvT.lvTop_facts hyE hy1).2.2.2.2.1
    by_contra hlt
    push Not at hlt
    have hfvT : f v ∈ Tset (f ρ) := vz_T_down hyE hy1 hθT hθ1 hlt.le
    obtain ⟨s, hsT, -, hsr, hsa, hgs⟩ :=
      lvCore hyE hy1 hby hs1T hs11 hfvT hyv hfv1 hfE (hb1.trans_lt hfrv) hR hLg hlt
    rw [hsrcopy] at hsr
    rcases le_or_gt s (LvT.val s3 (f ρ)) with hsle | hslt
    · obtain ⟨-, -, -, -, -, -, -, hηθ⟩ := Lv.th_facts hyE hy1 hby hs3T hs31
      have hm := Lv.th_le hyE hy1 hby hsT hs3T hs31 hsle hηθ
      rw [hsa] at hm
      exact (not_lt_of_ge (hm.trans hprev)) hfv0v
    · let d := s - LvT.val s3 (f ρ)
      have hde : LvT.val s3 (f ρ) + d = s := Ordinal.add_sub_cancel_of_le hslt.le
      have hd0 : d ≠ 0 := by
        intro h0
        rw [h0, add_zero] at hde
        exact absurd hde (ne_of_lt hslt)
      have hdz : d < ω ^ LvT.val sz (f ρ) :=
        (add_lt_add_iff_left _).1 (by rw [hde]; exact hsr)
      have hlgd : lg d < LvT.val sz (f ρ) :=
        (opow_lt_opow_iff_right one_lt_omega0).1
          (lt_of_le_of_lt (le_of_dvd hd0 (lg_dvd hd0)) hdz)
      have hlgadd : lg s = lg d := by rw [← hde]; exact Lu.lu_lg_add_right hd0
      have hζs : luZeta (f ρ) (f ρ + b) s ≤ lg s := Lu.lu_zeta_le_lg
      have h1 : Lv.L (f ρ) b (f v) + luZeta (f ρ) (f ρ + b) s <
          Lv.L (f ρ) b (f v) + f z := by
        apply (add_lt_add_iff_left _).2
        exact lt_of_le_of_lt hζs (by rw [hlgadd]; exact hlgd.trans_le hb4)
      have hLf : Lv.L (f ρ) b (f v) ≤ f L := by simpa [Lv.L] using hfL
      have h2 : Lv.L (f ρ) b (f v) + f z ≤ f L + f z := add_le_add hLf le_rfl
      exact absurd (hgs.trans_lt (h1.trans_le h2)) (lt_irrefl _)

/-- The full remainder induction step for a base-dependent theta term. -/
theorem lvImg_th {b r v : Ordinal.{0}} (hb : b < ρ)
    (hrT : r ∈ Tset ρ) (hr1 : r < Om1)
    (hve : vt ρ (Om1 * (ρ + b) + r) = v) (hvB : v < lvTop ρ)
    (I1 : ∀ u, u < v → ∃ W Z s, Lv.LvImg ρ δ u W Z s) :
    ∃ W Z s, Lv.LvImg ρ δ v W Z s := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hrv⟩ :=
    Lv.th_facts (τ := ρ) (b := b) (η := r) (upsPt_inE h.ρU) h.ρ1 hb hrT hr1
  rw [hve] at hrv
  by_cases hl : ∃ σ, σ < r ∧ r < vt ρ (Om1 * (ρ + b) + σ)
  · have hr0 : r ≠ 0 := by
      obtain ⟨σ, hσ, -⟩ := hl
      exact (lt_of_le_of_lt zero_le hσ).ne'
    have hζ : luZeta ρ (ρ + b) r = lg r := Lu.lu_zeta_lim hl
    obtain ⟨r0, hrs, -, hr0r⟩ := lg_split hr0
    let z := lg r
    have hzv : z < v := (lg_le hr0).trans_lt hrv
    have hr0T : r0 ∈ Tset ρ := vz_T_down (upsPt_inE h.ρU) h.ρ1 hrT hr1 hr0r.le
    have hr01 : r0 < Om1 := hr0r.trans hr1
    by_cases hz0 : z = 0
    · have hrs' : r = r0 + 1 := by simpa [z, hz0, opow_zero] using hrs
      have hζ0 : luZeta ρ (ρ + b) r = 0 := by simpa [z, hz0] using hζ
      exact lvImg_th_succ h hb hrT hr1 hr0T hr01 hrs' hζ0 hve hvB I1
    · exact lvImg_th_limit h hb hrT hr1 hr0T hrs (by rfl) hz0 hζ hve hvB I1
  · have hfix : ∀ σ, σ < r → vt ρ (Om1 * (ρ + b) + σ) ≤ r := by
      intro σ hσ
      by_contra hnot
      exact hl ⟨σ, hσ, lt_of_not_ge hnot⟩
    have hζ : luZeta ρ (ρ + b) r = 0 := Lu.lu_zeta_fix hfix
    exact lvImg_th_fixed h hb hrT hr1 hζ hfix hve hvB I1


end LvK

end Googology.Trans.PoR.InaccPsi.R2
