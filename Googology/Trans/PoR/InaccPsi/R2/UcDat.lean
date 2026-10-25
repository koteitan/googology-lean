import Googology.Trans.PoR.InaccPsi.R2.UcH

/-!
# Normal forms `z = H_λ(y)` past `X`, the bound `B₂`, and the data `ucDat`

`Ω₂ = OmTwo`, `E₂ = ucE = ε_{Ω₂+1}`, `H_γ = Uc.ucH γ` (`R2.UcH`), `F_β = Rh.rhF β`, `X = Tl.tlX` (the least fixed
point of `β ↦ F_β(0)` above `Ω₁`).  A strongly critical `z > Ω₁` **has a normal form** when some level `γ < E₂` with
all components below `z` does not fix it; the least one is its level `λ = ucLev z`, and `z = H_λ(y)` with `y = ucI λ
z < z`.  **`B₂ = ucB`** is the least strongly critical `z > Ω₁` with no normal form (a common fixed point of every
`H_γ`, `γ < E₂`, with components below it; the Bachmann–Howard ordinal over `Ω₁`).

* `ucLevSet`, `ucLev`, `ucI`, `ucLev_spec`, `uc_nf` (**the normal form**), `ucLev_H` (**`H_γ(y)` with `y < H_γ(y)` has
  level `γ` and index `y`**);
* `ucB`, `ucB_spec`, `ucB_SC`, `ucB_gt`, `uc_nf_of_lt` (**every strongly critical `z ∈ (Ω₁, B₂)` has a normal form**);
* `uc_X_mem`, `ucH_Om2_zero` (**`H_{Ω₂}(0) = X`**), `uc_X_nf`, `uc_nf_lt_X` (the normal form below `X` from the one of
  `R2.TlDat`), `uc_X_lt_B` (**`X < B₂`**);
* `ucDat` (**the data**: `Tl.tlDat` below `X`; on `[X, B₂)` the Cantor clause, the Veblen clause, and for an atom
  `H_λ(y)` the larger of the data of the components of `λ` and of `y`; `0` from `B₂` on), `ucDat_lt_X`, `ucDat_big`,
  `ucDat_cnf`, `ucDat_phi`, `ucDat_atom`, `ucDat_H`, `ucDat_lt_Om1` (**countable**), `ucDat_small`, `ucDat_Om1`.

No new axiom.  New definitions: `ucLevSet`, `ucLev`, `ucI`, `ucB`, `ucDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rj

/-! ## The normal form -/

/-- The levels below `E₂`, with all components below `z`, that do not fix `z`. -/
def ucLevSet (z : Ordinal.{0}) : Set Ordinal.{0} := {γ | γ < ucE ∧ ucC γ < z ∧ ucH γ z ≠ z}

/-- **The level** of `z`. -/
noncomputable def ucLev (z : Ordinal.{0}) : Ordinal.{0} := sInf (ucLevSet z)

/-- **The index** of `z` in `H_γ`. -/
noncomputable def ucI (γ z : Ordinal.{0}) : Ordinal.{0} := sInf {y | ucH γ y = z}

theorem ucI_spec {γ z : Ordinal.{0}} (h : ∃ y, ucH γ y = z) : ucH γ (ucI γ z) = z := csInf_mem h

theorem ucI_H (γ y : Ordinal.{0}) : ucI γ (ucH γ y) = y :=
  (ucH_normal γ).strictMono.injective (ucI_spec ⟨y, rfl⟩)

/-- **The level of a strongly critical `z > Ω₁` with a normal form.** -/
theorem ucLev_spec {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (hne : (ucLevSet z).Nonempty) :
    ucLev z < ucE ∧ ucC (ucLev z) < z ∧ ucH (ucLev z) z ≠ z ∧
      (∀ γ < ucLev z, ucC γ < z → ucH γ z = z) ∧ z ∈ range (ucH (ucLev z)) := by
  have hm : ucLev z ∈ ucLevSet z := csInf_mem hne
  have hlow : ∀ γ < ucLev z, ucC γ < z → ucH γ z = z := fun γ hγ hc => by
    by_contra h
    exact absurd (csInf_le' (show γ ∈ ucLevSet z from ⟨hγ.trans hm.1, hc, h⟩)) (not_le.2 hγ)
  exact ⟨hm.1, hm.2.1, hm.2.2, hlow, ucG_range hSC h1 hm.2.1 hlow⟩

/-- **The normal form**: `z = H_λ(y)` with `λ = ucLev z`, `y = ucI λ z < z`. -/
theorem uc_nf {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (hne : (ucLevSet z).Nonempty) :
    ucH (ucLev z) (ucI (ucLev z) z) = z ∧ ucI (ucLev z) z < z := by
  obtain ⟨-, -, hne', -, hr⟩ := ucLev_spec hSC h1 hne
  have hI := ucI_spec hr
  refine ⟨hI, lt_of_le_of_ne ?_ fun e => ?_⟩
  · calc ucI (ucLev z) z ≤ ucH (ucLev z) (ucI (ucLev z) z) := ucH_le_self _ _
      _ = z := hI
  · rw [e] at hI; exact hne' hI

/-- **`H_γ(y)` with `y < H_γ(y)` has level `γ` and index `y`** (`γ < E₂`). -/
theorem ucLev_H {γ y : Ordinal.{0}} (hγ : γ < ucE) (hy : y < ucH γ y) :
    ucLev (ucH γ y) = γ ∧ ucI γ (ucH γ y) = y := by
  have hne : ucH γ (ucH γ y) ≠ ucH γ y := fun e =>
    absurd ((ucH_normal γ).strictMono.injective e) (ne_of_gt hy)
  have hmem : γ ∈ ucLevSet (ucH γ y) := ⟨hγ, ucH_C_lt γ y, hne⟩
  refine ⟨le_antisymm (csInf_le' hmem) (not_lt.1 fun hlt => ?_), ucI_H γ y⟩
  have hm : ucLev (ucH γ y) ∈ ucLevSet (ucH γ y) := csInf_mem ⟨γ, hmem⟩
  exact hm.2.2 (ucG_fix_lower hlt ⟨y, rfl⟩ hm.2.1)

/-! ## The bound `B₂` -/

/-- The strongly critical `z > Ω₁` with no normal form. -/
def ucNoNF : Set Ordinal.{0} := {z | SC z ∧ Om1 < z ∧ ¬ (ucLevSet z).Nonempty}

theorem ucNoNF_nonempty : ucNoNF.Nonempty := by
  set f : Iio ucE → Ordinal.{0} → Ordinal.{0} := fun j => ucH j.1 with hf
  have hN : ∀ j : Iio ucE, Order.IsNormal (f j) := fun j => ucH_normal j.1
  set v := nfpFamily f (Om1 + 1) with hv
  have hfix : ∀ j : Iio ucE, ucH j.1 v = v := fun j => nfpFamily_fp (hN j) _
  have h0 : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  have hSC : SC v := by rw [← hfix ⟨0, h0⟩]; exact ucH_SC 0 v
  have hno : ¬ (ucLevSet v).Nonempty := fun ⟨γ, hγ, _, hne⟩ => hne (hfix ⟨γ, hγ⟩)
  exact ⟨v, show v ∈ ucNoNF from ⟨hSC, (lt_add_one _).trans_le (le_nfpFamily f _), hno⟩⟩

/-- **`B₂`**: the least strongly critical `z > Ω₁` with no normal form. -/
noncomputable def ucB : Ordinal.{0} := sInf ucNoNF

theorem ucB_mem : ucB ∈ ucNoNF := csInf_mem ucNoNF_nonempty

theorem ucB_SC : SC ucB := ucB_mem.1

theorem ucB_gt : (Om1 : Ordinal.{0}) < ucB := ucB_mem.2.1

/-- **`B₂` is fixed by every `H_γ`, `γ < E₂`, with components below it.** -/
theorem ucB_spec {γ : Ordinal.{0}} (hγ : γ < ucE) (hc : ucC γ < ucB) : ucH γ ucB = ucB := by
  by_contra h; exact ucB_mem.2.2 ⟨γ, hγ, hc, h⟩

theorem ucB_le {z : Ordinal.{0}} (h : z ∈ ucNoNF) : ucB ≤ z := csInf_le' h

/-- **Every strongly critical `z ∈ (Ω₁, B₂)` has a normal form.** -/
theorem uc_nf_of_lt {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (hz : z < ucB) : (ucLevSet z).Nonempty := by
  by_contra h; exact absurd (ucB_le ⟨hSC, h1, h⟩) (not_le.2 hz)

/-! ## `X = H_{Ω₂}(0)` and `X < B₂` -/

theorem uc_Om2_lt_E : (OmTwo : Ordinal.{0}) < ucE := ucE_gt

/-- `F_j(X) = X` for `j < X`. -/
theorem uc_F_X {j : Ordinal.{0}} (hj : j < tlX) : rhF j tlX = tlX := by
  have h := rhF_fix_lower hj 0
  rwa [tlX_rhF] at h

/-- `H_j(X) = X` for `j < X`. -/
theorem uc_H_X {j : Ordinal.{0}} (hj : j < tlX) : ucH j tlX = tlX := by
  have hj2 : j < OmTwo := hj.trans tlX_lt_OmTwo
  exact (ucH_fix_iff_F hj2 (max_lt tlX_gt hj)).2 (uc_F_X hj)

/-- **`X` is a value of `H_{Ω₂}`.** -/
theorem uc_X_mem : tlX ∈ range (ucH OmTwo) := by
  refine ucG_range tlX_SC tlX_gt (by rw [ucC_Om2]; exact (tf_one_lt_Om1).trans tlX_gt) fun j hj hc => ?_
  rw [ucC_small hj] at hc
  exact uc_H_X hc

/-- **Every value of `H_{Ω₂}` is `≥ X`.** -/
theorem uc_X_le_H {v : Ordinal.{0}} (hv : v ∈ range (ucH OmTwo)) : tlX ≤ v := by
  rcases le_or_gt OmTwo v with h | h
  · exact tlX_lt_OmTwo.le.trans h
  have hm : v ∈ ucGC ucC Om1 OmTwo := by unfold ucH at hv; rw [ucG_range_eq] at hv; exact hv
  have hfix : ∀ j < v, rhF j v = v := fun j hj => by
    have hj2 : j < OmTwo := hj.trans h
    refine (ucH_fix_iff_F hj2 (max_lt hm.2.1 hj)).1 (hm.2.2.2 j hj2 ?_)
    rw [ucC_small hj2]; exact hj
  obtain ⟨e, he⟩ := rhF_range hm.1 hfix
  have hG : tlG v = v := by
    refine le_antisymm ?_ (rhF_left_le v 0)
    calc tlG v = rhF v 0 := rfl
      _ ≤ rhF v e := (rhF_le v).2 zero_le
      _ = v := he
  exact tlX_le hG hm.2.1

/-- **`H_{Ω₂}(0) = X`.** -/
theorem ucH_Om2_zero : ucH OmTwo 0 = tlX := by
  obtain ⟨e, he⟩ := uc_X_mem
  refine le_antisymm ?_ (uc_X_le_H ⟨0, rfl⟩)
  rw [← he]; exact (ucG_le_iff (d := ucC) (L := Om1) OmTwo).2 zero_le

/-- **`X` has the normal form `H_{Ω₂}(0)`.** -/
theorem uc_X_nf : OmTwo ∈ ucLevSet tlX := by
  refine ⟨ucE_gt, by rw [ucC_Om2]; exact (tf_one_lt_Om1).trans tlX_gt, fun e => ?_⟩
  have h1 : ucH OmTwo 1 ≤ ucH OmTwo tlX := (ucG_le_iff (d := ucC) (L := Om1) OmTwo).2
    (tf_one_lt_Om1.trans tlX_gt).le
  have h2 : ucH OmTwo 0 < ucH OmTwo 1 := (ucH_lt_iff OmTwo).2 zero_lt_one
  rw [ucH_Om2_zero, e] at *
  exact absurd (h2.trans_le h1) (lt_irrefl _)

/-- **Below `X` the normal form of `R2.TlDat` is one**: a strongly critical `z ∈ (Ω₁, X)` has `tlLev z` in
`ucLevSet z`. -/
theorem uc_nf_lt_X {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (h2 : z < tlX) : tlLev z ∈ ucLevSet z := by
  obtain ⟨hl, hne, -⟩ := tlLev_spec hSC h1 h2
  have hl2 : tlLev z < OmTwo := hl.trans (h2.trans tlX_lt_OmTwo)
  refine ⟨hl2.trans ucE_gt, by rw [ucC_small hl2]; exact hl, fun e => hne ?_⟩
  exact (ucH_fix_iff_F hl2 (max_lt h1 hl)).1 e

/-- **`X < B₂`.** -/
theorem uc_X_lt_B : tlX < ucB := by
  by_contra h
  rcases eq_or_lt_of_le (not_lt.1 h) with e | hlt
  · exact ucB_mem.2.2 (e ▸ ⟨OmTwo, uc_X_nf⟩)
  · exact ucB_mem.2.2 ⟨tlLev ucB, uc_nf_lt_X ucB_SC ucB_gt hlt⟩

/-! ## The data -/

theorem uc_Om1_lt_of_X {z : Ordinal.{0}} (h : tlX ≤ z) : Om1 < z := tlX_gt.trans_le h

theorem uc_atom_lt {z : Ordinal.{0}} (hX : tlX ≤ z) (hB : z < ucB) (hI : ¬ invVeblen₁ z < z) :
    ucI (ucLev z) z < z :=
  (uc_nf (tl_SC_of (uc_Om1_lt_of_X hX) hI) (uc_Om1_lt_of_X hX)
    (uc_nf_of_lt (tl_SC_of (uc_Om1_lt_of_X hX) hI) (uc_Om1_lt_of_X hX) hB)).2

/-- **The data of `z`**: `tlDat z` below `X`; on `[X, B₂)` the Cantor clause, the Veblen clause, and at an atom
`H_λ(y)` the larger of the data of the components of `λ` (all below `z`) and of `y`.  `0` from `B₂` on. -/
noncomputable def ucDat (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : tlX ≤ z ∧ z < ucB then
    if hE : ω ^ z = z then
      if hI : invVeblen₁ z < z then
        have : invVeblen₂ z < z := tf_inv2_lt hE
        max (ucDat (invVeblen₁ z)) (ucDat (invVeblen₂ z))
      else
        have : ucI (ucLev z) z < z := uc_atom_lt hz.1 hz.2 hI
        max (ucFold (fun x => if hx : x < z then ucDat x else 0) (ucLev z)) (ucDat (ucI (ucLev z) z))
    else
      have : log ω z < z := tf_log_lt (uc_Om1_lt_of_X hz.1) hE
      have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans (uc_Om1_lt_of_X hz.1)).ne'
      max (ucDat (log ω z)) (ucDat (z % ω ^ log ω z))
  else tlDat z
termination_by z

theorem ucDat_lt_X {z : Ordinal.{0}} (h : z < tlX) : ucDat z = tlDat z := by
  rw [ucDat, dif_neg (fun hz => absurd hz.1 (not_le.2 h))]

theorem ucDat_big {z : Ordinal.{0}} (h : ucB ≤ z) : ucDat z = 0 := by
  rw [ucDat, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)), tlDat_big (uc_X_lt_B.le.trans h)]

theorem ucDat_cnf {z : Ordinal.{0}} (hX : tlX ≤ z) (hB : z < ucB) (hE : ω ^ z ≠ z) :
    ucDat z = max (ucDat (log ω z)) (ucDat (z % ω ^ log ω z)) := by
  rw [ucDat, dif_pos ⟨hX, hB⟩, dif_neg hE]

theorem ucDat_phi {z : Ordinal.{0}} (hX : tlX ≤ z) (hB : z < ucB) (hE : ω ^ z = z) (hI : invVeblen₁ z < z) :
    ucDat z = max (ucDat (invVeblen₁ z)) (ucDat (invVeblen₂ z)) := by
  rw [ucDat, dif_pos ⟨hX, hB⟩, dif_pos hE, dif_pos hI]

/-- **The atom clause.** -/
theorem ucDat_atom {z : Ordinal.{0}} (hX : tlX ≤ z) (hB : z < ucB) (hE : ω ^ z = z) (hI : ¬ invVeblen₁ z < z) :
    ucDat z = max (ucFold ucDat (ucLev z)) (ucDat (ucI (ucLev z) z)) := by
  rw [ucDat, dif_pos ⟨hX, hB⟩, dif_pos hE, dif_neg hI]
  have hSC := tl_SC_of (uc_Om1_lt_of_X hX) hI
  have hc := (ucLev_spec hSC (uc_Om1_lt_of_X hX) (uc_nf_of_lt hSC (uc_Om1_lt_of_X hX) hB)).2.1
  congr 1
  refine ucFold_congr _ fun x hx => ?_
  have hxz : x < z := (le_ucC hx).trans_lt hc
  simp only [dif_pos hxz]

theorem uc_SC_facts {z : Ordinal.{0}} (hSC : SC z) : ω ^ z = z ∧ ¬ invVeblen₁ z < z := tl_SC_facts hSC

/-- **The atom clause for `H_γ(y)`**: `ucDat (H_γ(y)) = max (ucFold ucDat γ) (ucDat y)` for `γ < E₂`,
`y < H_γ(y)`, `X ≤ H_γ(y) < B₂`. -/
theorem ucDat_H {γ y : Ordinal.{0}} (hγ : γ < ucE) (hy : y < ucH γ y) (hX : tlX ≤ ucH γ y)
    (hB : ucH γ y < ucB) : ucDat (ucH γ y) = max (ucFold ucDat γ) (ucDat y) := by
  obtain ⟨hE, hI⟩ := uc_SC_facts (ucH_SC γ y)
  obtain ⟨hl, hi⟩ := ucLev_H hγ hy
  rw [ucDat_atom hX hB hE hI, hl, hi]

/-- **The data is countable.** -/
theorem ucDat_lt_Om1 : ∀ z : Ordinal.{0}, ucDat z < Om1 := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  by_cases hz : tlX ≤ z ∧ z < ucB
  · have h1 := uc_Om1_lt_of_X hz.1
    by_cases hE : ω ^ z = z
    · by_cases hI : invVeblen₁ z < z
      · rw [ucDat_phi hz.1 hz.2 hE hI]
        exact max_lt (IH _ hI) (IH _ (tf_inv2_lt hE))
      · rw [ucDat_atom hz.1 hz.2 hE hI]
        have hSC := tl_SC_of h1 hI
        have hc := (ucLev_spec hSC h1 (uc_nf_of_lt hSC h1 hz.2)).2.1
        refine max_lt ((ucFold_lt_iff ucDat rj_Om1_pos _).2 fun x hx => IH x ((le_ucC hx).trans_lt hc))
          (IH _ (uc_atom_lt hz.1 hz.2 hI))
    · rw [ucDat_cnf hz.1 hz.2 hE]
      exact max_lt (IH _ (tf_log_lt h1 hE)) (IH _ (rj_mod_lt (rj_Om1_pos.trans h1).ne'))
  · rw [ucDat, dif_neg hz]; exact tlDat_lt_Om1 z

theorem ucDat_small {z : Ordinal.{0}} (h : z < Om1) : ucDat z = z := by
  rw [ucDat_lt_X (h.trans tlX_gt), tlDat_small h]

theorem ucDat_Om1 : ucDat Om1 = 0 := by rw [ucDat_lt_X tlX_gt, tlDat_Om1]

end Googology.Trans.PoR.InaccPsi.R2.Uc
