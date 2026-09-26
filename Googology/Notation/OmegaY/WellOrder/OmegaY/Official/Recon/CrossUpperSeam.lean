/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperSeam.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpper
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0

set_option backward.do.legacy false

/-!
# The seam of block `0`

`SeamLastHolds` (`CrossUpper.lean`) is about a copy `X = x₀ + w·i` of `x₀`, the node `u` of
`X` at the top of the lower part (`row u < τ`) and the node `u⁺` above it, at the bottom of
the upper part. This file proves it for block `0` (`seamLast_block0`), where `X = x₀`:

* In block `0` the lower part of `x₀` is the column `x₀` of `M(s)` below `τ`
  (`JumpLaw.lower_id`), so `u` has the row and the stored left end of the node `t⁻` of
  `M(s)` right below the top `t` of `x₀` (`seam_block0_node`).
* In `M(s)` the stored parent of `t⁻` is the root `r`, the answer of the canonical search
  from `Q t⁻`; so a chain of stored parents runs from `Q t⁻` to `r`, in the columns left of
  `x₀`, where `R` and `M(s)` agree: it is a chain of `R` from `Q u` (`q_transport'`,
  `chain_transport`).
* The node above `r` is the lowest node of `c_r` at a row `≥ τ`, which is copied to `u⁺`.

Hence `SeamLastHolds` reduces to the blocks `i ≥ 1` (`SeamLastPosHolds`,
`seamLastHolds_of_pos`).
-/

namespace OmegaY.Official.Recon.CrossUpper

open Canonical Expansion Geometry Frame Classification
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## Generic facts -/

theorem leftColumn_spec' {cell : Cell} {l : Nat} (h : leftColumn cell = .ok l) :
    ∃ r : Ref, cell.left = some r ∧ r.column = l := by
  cases hc : cell.left with
  | none =>
    simp [leftColumn, Expansion.leftOf, hc, liftE, Except.mapError, bind, Except.bind] at h
  | some r =>
    rw [leftColumn_of hc] at h
    exact ⟨r, rfl, Except.ok.inj h⟩

/-- The candidate of a node with a copied left end: a variant of `q_transport` where the
left end of `U` is given directly. -/
theorem q_transport' {G F : Frame} (hG : G.Ordered) (hF : F.Ordered) {θ : Nat → Row}
    {f : Nat → Nat} {K : Nat} (hC : Copies G F θ f K) {n qM : G.Node} {U : F.Node}
    (hleft : ∀ a, (G.cell n).left = some a →
      ∃ A : Ref, (F.cell U).left = some A ∧ A.column = f a.column)
    (hh : F.height U = G.height n)
    (hq : G.Q n = some qM) (hqD : θ qM.1.val ≤ G.height qM) (hqK : qM.1.val < K) :
    ∃ qF, F.Q U = some qF ∧ Img G F f qM qF := by
  obtain ⟨L, hL, _, _, hqL, _, hqn, hqmax⟩ := Q_spec hG hq
  obtain ⟨Aref, hA, hAc⟩ := hleft (ref L) hL
  obtain ⟨q', hq'⟩ := Q_exists_of_left hF ⟨Aref, hA⟩
  obtain ⟨L', hL', _, _, hq'L', _, hq'U, hq'max⟩ := Q_spec hF hq'
  have hAL' : Aref = ref L' := Option.some.inj (hA.symm.trans hL')
  have Cq := hC _ hqK
  obtain ⟨qF, hqFc, hqFh⟩ := Cq.fwd qM rfl hqD
  have hcol : q'.1 = qF.1 := by
    apply Fin.ext
    rw [hq'L', hqFc]
    have e1 : L'.1.val = Aref.column := by rw [hAL']; rfl
    rw [e1, hAc]
    have e2 : (ref L).column = L.1.val := rfl
    rw [e2, hqL]
  refine ⟨qF, ?_, hqFc, hqFh⟩
  rw [hq']
  congr 1
  apply node_eq_of_index hcol
  apply le_antisymm
  · by_contra hn'
    have hlt : F.height qF < F.height q' := height_lt_of_index hF hcol.symm (by omega)
    obtain ⟨v, hvc, hvh⟩ := Cq.bwd q' (by rw [hcol]; exact hqFc)
      (by rw [hqFh] at hlt; exact hqD.trans hlt.le)
    have hvq : qM.1 = v.1 := Fin.ext hvc.symm
    have hvi := index_lt_of_height_lt hG hvq (by rw [hvh, ← hqFh]; exact hlt)
    have hlen' : G.length v.1 = G.length qM.1 := by rw [hvq]
    have hlen : qM.2.val + 1 < G.length qM.1 := by have := v.2.isLt; omega
    let V : G.Node := ⟨qM.1, ⟨qM.2.val + 1, hlen⟩⟩
    have hV := hqmax V (upper_eq_of_index rfl rfl)
    have hVv : G.height V ≤ G.height v := height_le_of_index hG hvq (by simp [V]; omega)
    rw [hvh] at hVv
    exact absurd (lt_of_lt_of_le hV (hVv.trans (hq'U.trans hh.le))) (lt_irrefl _)
  · by_contra hn'
    have hlen' : F.length qF.1 = F.length q'.1 := by rw [hcol]
    have hlen : q'.2.val + 1 < F.length q'.1 := by have := qF.2.isLt; omega
    let V : F.Node := ⟨q'.1, ⟨q'.2.val + 1, hlen⟩⟩
    have hV := hq'max V (upper_eq_of_index rfl rfl)
    have hVQ : F.height V ≤ F.height qF := height_le_of_index hF hcol (by simp [V]; omega)
    rw [hqFh] at hVQ
    exact absurd (lt_of_lt_of_le hV (hVQ.trans (hqn.trans hh.symm.le))) (lt_irrefl _)

/-- The cells of an assembled column, read in the frame. -/
theorem cells_of_assemble {R : Mountain} {X : Nat} (hX : X < R.size) {ctx : Context}
    {es : List Emit} (hasm : assemble ctx es = .ok R[X]) :
    R[X].size = es.length + 1 ∧
    ∀ v : (Frame.ofMountain R).Node, v.1.val = X → 1 ≤ v.2.val →
      ∃ hk : v.2.val - 1 < es.length,
        ((Frame.ofMountain R).cell v).row = Official.stored es[v.2.val - 1].row ∧
        ∃ ref : Ref, ((Frame.ofMountain R).cell v).left = some ref ∧
          ref.column = Classification.legColumn ctx es[v.2.val - 1] := by
  obtain ⟨hsize, hspec⟩ := Classification.assemble_spec hasm
  refine ⟨hsize, ?_⟩
  intro v hv hv1
  subst hv
  have hvs : v.2.val < R[v.1.val].size := v.2.isLt
  have hk : v.2.val - 1 < es.length := by omega
  refine ⟨hk, ?_⟩
  obtain ⟨cell, hcell, hrow, ref, hl, hrc⟩ := hspec (v.2.val - 1) hk
  rw [show v.2.val - 1 + 1 = v.2.val by omega, Array.getElem?_eq_getElem hvs] at hcell
  have he : cell = (Frame.ofMountain R).cell v := (Option.some.inj hcell).symm
  subst he
  exact ⟨hrow, ref, hl, hrc⟩

theorem stored_zero : Official.stored (0 : Row) = 1 := by
  have := Classification.stored_official (show (1 : Row) ≤ 1 from le_rfl)
  rwa [official_one] at this

/-! ## The seam node of block `0` -/

/-- **The seam node of block `0`.** The top node `u` of the lower part of the column `x₀` of
the output has the row and the stored left end of the highest node of the column `x₀` of
`M(s)` below `τ`. -/
theorem seam_block0_node {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hCI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (Official.official t.row) R)
    {u up : (Frame.ofMountain R).Node} (hu1 : u.1.val = M.size - 1) (hu : Real u)
    (hU : (Frame.ofMountain R).height u < t.row)
    (hup : (Frame.ofMountain R).upper u = some up)
    (hτup : t.row ≤ (Frame.ofMountain R).height up) :
    ∃ pM : (Frame.ofMountain M).Node, pM.1.val = M.size - 1 ∧
      (Frame.ofMountain M).height pM = (Frame.ofMountain R).height u ∧
      ((Frame.ofMountain R).cell u).left = ((Frame.ofMountain M).cell pM).left ∧
      ∀ z : (Frame.ofMountain M).Node, z.1.val = M.size - 1 →
        (Frame.ofMountain M).height z < t.row →
        (Frame.ofMountain M).height z ≤ (Frame.ofMountain M).height pM := by
  have hM := hTop.build
  have hVM := build_valid_of_success hM
  have hFM := hVM.toOrdered
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  obtain ⟨M', hM', hMs, hI, hB⟩ := run_basic hrun
  have hMM : M = M' := Except.ok.inj (hM.symm.trans hM')
  subst hMM
  have hFR := hB.valid.toOrdered
  have hHB := hb_run hrun
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  have hsτ : Official.stored (Official.official t.row) = t.row :=
    Classification.stored_official ht1
  have hcr := hTop.lt
  set w := M.size - 1 - root.column with hw
  have hX : M.size - 1 < R.size := by rw [← hu1]; exact u.1.isLt
  obtain ⟨i', x', _, hx'b, hXeq', hcopy⟩ := hCI.2.2 (M.size - 1) hX le_rfl
  obtain ⟨hx'gt, hx'le⟩ := mem_blockColumns hcr hx'b
  have hi' : i' = 0 := by
    by_contra h
    have : w ≤ w * i' := Nat.le_mul_of_pos_right w (by omega)
    omega
  subst hi'
  have hx' : x' = M.size - 1 := by simp at hXeq'; omega
  subst hx'
  have hctx := runCtx_ctxAt (R := R) hTop hx'b hXeq' hX.le
  obtain ⟨vs, us, hvs, hus, hasm⟩ := RowLaw.copyColumn_parts hcopy
  obtain ⟨hL1, hL2⟩ := JumpLaw.lower_id hctx rfl hvs
  obtain ⟨hU1, _⟩ := JumpLaw.upper_facts hus
  obtain ⟨hsize, hnode⟩ := cells_of_assemble hX hasm
  have hlo : ∀ em ∈ vs.flatten, em.row < Official.official t.row := by
    intro em hem
    obtain ⟨_, _, _, h, _⟩ := hL1 em hem
    exact h
  have hush : ∀ em ∈ us, Official.official t.row ≤ em.row := by
    intro em hem
    obtain ⟨_, _, _, h, _⟩ := hU1 em hem
    exact h
  -- the index of `u`
  obtain ⟨hku, hurow, refu, hul, hulc⟩ := hnode u hu1 hu
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  obtain ⟨hkup, huprow, _⟩ := hnode up (by rw [hup1]; exact hu1) (by omega)
  have hlt1 : u.2.val - 1 < vs.flatten.length := by
    by_contra hn
    have hmem : (vs.flatten ++ us)[u.2.val - 1] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    have := stored_mono (hush _ hmem)
    rw [hsτ, ← hurow] at this
    exact absurd hU (not_lt.mpr this)
  have hlt2 : vs.flatten.length ≤ up.2.val - 1 := by
    by_contra hn
    have hmem : (vs.flatten ++ us)[up.2.val - 1] ∈ vs.flatten := by
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem _
    have := stored_strictMono (hlo _ hmem)
    rw [hsτ, ← huprow] at this
    exact absurd hτup (not_le.mpr this)
  have hmemu : (vs.flatten ++ us)[u.2.val - 1] ∈ vs.flatten := by
    rw [List.getElem_append_left hlt1]
    exact List.getElem_mem _
  obtain ⟨pp, hpp, hprow, _, hpleg⟩ := hL1 _ hmemu
  have hpp' : pp ∈ realNodes M (M.size - 1) := hpp
  obtain ⟨colx, k, hcolx, hk, hpref⟩ := mem_realNodes_iff.mp hpp'
  obtain ⟨hx0lt, hcolxe⟩ := Array.getElem?_eq_some_iff.mp hcolx
  rw [← hcolxe] at hk
  obtain ⟨hk1, hpc⟩ := Array.getElem?_eq_some_iff.mp hk
  let pM : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hx0lt⟩, ⟨k + 1, hk1⟩⟩
  have hpMc : (Frame.ofMountain M).cell pM = pp.2 := hpc
  have hpp1 : (1 : Row) ≤ pp.2.row := realNodes_row_one_le hVM hpp'
  have hhu : (Frame.ofMountain R).height u = pp.2.row := by
    change ((Frame.ofMountain R).cell u).row = _
    rw [hurow, ← hprow, Classification.stored_official hpp1]
  have hhpM : (Frame.ofMountain M).height pM = pp.2.row := by
    change ((Frame.ofMountain M).cell pM).row = _
    rw [hpMc]
  refine ⟨pM, rfl, by rw [hhpM, hhu], ?_, ?_⟩
  · -- the stored left ends
    by_cases h0 : (vs.flatten ++ us)[u.2.val - 1].row = 0
    · -- the bottom row
      have hrow1 : pp.2.row = 1 := by
        have := Classification.stored_official hpp1
        rw [hprow, h0, stored_zero] at this
        exact this.symm
      have hu2 : u.2.val = 1 := by
        by_contra hne
        have hlen : 1 < (Frame.ofMountain R).length u.1 := by have := u.2.isLt; omega
        have hb := hFR.bottom_row u.1 hlen
        have hlt := height_lt_of_index hFR (a := ⟨u.1, ⟨1, hlen⟩⟩) (b := u) rfl
          (by simp; unfold Real at hu; omega)
        have e : (Frame.ofMountain R).height ⟨u.1, ⟨1, hlen⟩⟩ = 1 := hb
        rw [e, hhu, hrow1] at hlt
        exact lt_irrefl _ hlt
      have hk0 : k = 0 := by
        by_contra hne
        have hlen : 1 < (Frame.ofMountain M).length pM.1 := by have := pM.2.isLt; simp [pM] at this ⊢; omega
        have hb := hFM.bottom_row pM.1 hlen
        have hlt := height_lt_of_index hFM (a := ⟨pM.1, ⟨1, hlen⟩⟩) (b := pM) rfl
          (by simp [pM]; omega)
        have e : (Frame.ofMountain M).height ⟨pM.1, ⟨1, hlen⟩⟩ = 1 := hb
        rw [e, hhpM, hrow1] at hlt
        exact lt_irrefl _ hlt
      obtain ⟨bR, hbR, hbRl⟩ := hB.legs (M.size - 1) hX
      obtain ⟨bM, hbM, _, hbMl, _⟩ := bottom_node hM hx0lt
      have hcu : (Frame.ofMountain R).cell u = bR := by
        obtain ⟨⟨uc, huc⟩, ⟨ui, hui⟩⟩ := u
        simp only at hu1 hu2
        subst hu1
        subst hu2
        change R[M.size - 1][1] = bR
        rw [Array.getElem?_eq_getElem hui] at hbR
        exact Option.some.inj hbR
      have hcp : (Frame.ofMountain M).cell pM = bM := by
        change M[M.size - 1][k + 1] = bM
        subst hk0
        rw [Array.getElem?_eq_getElem hk1] at hbM
        exact Option.some.inj hbM
      rw [hcu, hcp, hbRl, hbMl]
    · -- above the bottom row
      obtain ⟨l, hpl, heml⟩ := hpleg h0
      obtain ⟨a, hpa, hal⟩ := leftColumn_spec' hpl
      have hrefu : refu.column = l := by
        rw [hulc]
        unfold Classification.legColumn
        rw [heml]
        simp [Classification.ctxAt]
      have hrow1 : pp.2.row ≠ 1 := by
        intro h1
        apply h0
        rw [← hprow, h1]
        exact official_one
      have hu2 : 2 ≤ u.2.val := by
        by_contra hne
        have hu1' : u.2.val = 1 := by unfold Real at hu; omega
        have hb := hFR.bottom_row u.1 (by have := u.2.isLt; omega)
        apply hrow1
        rw [← hhu]
        change ((Frame.ofMountain R).cells u.1 u.2).row = 1
        rw [show u.2 = ⟨1, by have := u.2.isLt; omega⟩ from Fin.ext hu1']
        exact hb
      have hk2 : 1 ≤ k := by
        by_contra hne
        have hk0 : k = 0 := by omega
        have hb := hFM.bottom_row pM.1 (by have := pM.2.isLt; simp [pM] at this ⊢; omega)
        apply hrow1
        rw [← hhpM]
        change ((Frame.ofMountain M).cells pM.1 pM.2).row = 1
        rw [show pM.2 = ⟨1, by have := pM.2.isLt; simp [pM] at this ⊢; omega⟩ from
          Fin.ext (by simp [pM, hk0])]
        exact hb
      -- the stored parent of the node below `u`
      let um : (Frame.ofMountain R).Node := ⟨u.1, ⟨u.2.val - 1, by have := u.2.isLt; omega⟩⟩
      have humu : (Frame.ofMountain R).upper um = some u := upper_eq_of_index rfl (by simp [um]; omega)
      have humr : Real um := by show 0 < u.2.val - 1; omega
      obtain ⟨A, hAl, hAc, _⟩ := hFR.stored_valid u refu hul
      have hAr : ref A = refu := lookup_spec hAl
      have hrawA : (Frame.ofMountain R).rawParent um = some A :=
        rawParent_eq_of_upper_left humu (by rw [hAr]; exact hul)
      obtain ⟨hA1, hA2⟩ := hHB um humr u A humu hrawA
      -- the stored parent of the node below `pM`
      let pm : (Frame.ofMountain M).Node := ⟨pM.1, ⟨k, Nat.lt_of_succ_lt hk1⟩⟩
      have hpmu : (Frame.ofMountain M).upper pm = some pM := upper_eq_of_index rfl (by simp [pm, pM])
      have hpmr : Real pm := by show 0 < k; omega
      have hpa' : ((Frame.ofMountain M).cell pM).left = some a := by rw [hpMc]; exact hpa
      obtain ⟨aN, haNl, haNc, _⟩ := hFM.stored_valid pM a hpa'
      have haNr : ref aN = a := lookup_spec haNl
      have hrawa : (Frame.ofMountain M).rawParent pm = some aN :=
        rawParent_eq_of_upper_left hpmu (by rw [haNr]; exact hpa')
      obtain ⟨ha1, ha2⟩ := hbAt_of_normal hNM hpmr pM aN hpmu hrawa
      -- the two columns agree
      have hAcol : A.1.val = l := by rw [← hrefu, ← hAr]; rfl
      have haNcol : aN.1.val = l := by rw [← hal, ← haNr]; rfl
      have hlx : l < M.size - 1 := by
        have : aN.1.val < M.size - 1 := haNc
        omega
      have hag := hI.2.1 l hlx
      obtain ⟨A', hA'1, hA'2, hA'c⟩ := twin_of_agree' hag aN haNcol
      obtain ⟨a'', ha''1, ha''2, ha''c⟩ := twin_of_agree hag A hAcol
      have hle1 : A'.2.val ≤ A.2.val := by
        refine hA2 A' (Fin.ext (by rw [hA'1, hAcol])) ?_
        change ((Frame.ofMountain R).cell A').row < _
        rw [hA'c]
        change (Frame.ofMountain M).height aN < _
        rw [hhu, ← hhpM]
        exact ha1
      have hle2 : a''.2.val ≤ aN.2.val := by
        refine ha2 a'' (Fin.ext (by rw [ha''1, haNcol])) ?_
        change ((Frame.ofMountain M).cell a'').row < _
        rw [ha''c]
        change (Frame.ofMountain R).height A < _
        rw [hhpM, ← hhu]
        exact hA1
      have hidx : A.2.val = aN.2.val := by omega
      rw [hul, hpa']
      congr 1
      rw [← hAr, ← haNr]
      change (⟨A.1.val, A.2.val⟩ : Ref) = ⟨aN.1.val, aN.2.val⟩
      rw [hAcol, haNcol, hidx]
  · -- the highest node below `τ`
    intro z hz hzτ
    by_cases hz0 : z.2.val = 0
    · have hph := hFM.phantom z.1 (by have := z.2.isLt; omega)
      have : (Frame.ofMountain M).height z = 0 := by
        change ((Frame.ofMountain M).cells z.1 z.2).row = 0
        rw [show z.2 = ⟨0, by have := z.2.isLt; omega⟩ from Fin.ext hz0, hph]
        rfl
      rw [this]
      exact Row.zero_le _
    · have hzr : Real z := by unfold Real; omega
      have hz1 : (1 : Row) ≤ (Frame.ofMountain M).height z := one_le_height hFM hzr
      obtain ⟨⟨zc, hzc⟩, ⟨zi, hzi⟩⟩ := z
      simp only at hz
      subst hz
      have hmemz : ((⟨M.size - 1, zi⟩ : Ref), M[M.size - 1][zi]) ∈ realNodes M (M.size - 1) := by
        refine mem_realNodes_iff.mpr ⟨M[M.size - 1], zi - 1, Array.getElem?_eq_getElem hzc, ?_, ?_⟩
        · rw [show zi - 1 + 1 = zi by simp at hz0; omega]
          exact Array.getElem?_eq_getElem hzi
        · simp only
          congr 1
          simp at hz0
          omega
      have hoff : Official.official M[M.size - 1][zi].row < Official.official t.row :=
        official_strictMono hz1 hzτ
      obtain ⟨em', hem', hem'row⟩ := hL2 _ hmemz hoff
      obtain ⟨k', hk', hk'e⟩ := List.getElem_of_mem hem'
      have hk'1 : k' + 1 < R[M.size - 1].size := by
        rw [hsize, List.length_append]
        omega
      let Z : (Frame.ofMountain R).Node := ⟨⟨M.size - 1, hX⟩, ⟨k' + 1, hk'1⟩⟩
      obtain ⟨_, hZrow, _⟩ := hnode Z rfl (by simp [Z])
      have hZh : (Frame.ofMountain R).height Z = M[M.size - 1][zi].row := by
        change ((Frame.ofMountain R).cell Z).row = _
        rw [hZrow]
        simp only [Z, Nat.add_sub_cancel]
        rw [List.getElem_append_left hk', hk'e, hem'row]
        exact Classification.stored_official hz1
      have hZu : (Frame.ofMountain R).height Z ≤ (Frame.ofMountain R).height u :=
        height_le_of_index hFR (show Z.1 = u.1 from Fin.ext (by simp [Z, hu1]))
          (by simp [Z]; omega)
      change M[M.size - 1][zi].row ≤ (Frame.ofMountain M).height pM
      rw [← hZh, hhpM, ← hhu]
      exact hZu

/-! ## `SeamLastHolds` in block `0` -/

/-- **The seam of block `0`.** -/
theorem seamLast_block0 {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    {u q up : (Frame.ofMountain R).Node}
    (hu1 : u.1.val = (M.size - 1) + (M.size - 1 - root.column) * 0) (hu : Real u)
    (hU : (Frame.ofMountain R).height u < t.row)
    (hup : (Frame.ofMountain R).upper u = some up)
    (hτup : t.row ≤ (Frame.ofMountain R).height up)
    (hq : (Frame.ofMountain R).Q u = some q) :
    ∃ c cp, RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).upper c = some cp ∧
      cp.1.val = root.column + (M.size - 1 - root.column) * 0 ∧
      (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up := by
  have hM := hTop.build
  have hVM := build_valid_of_success hM
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  have hG := hNM.toOrdered
  have hMs := Canonical.build_size hM
  simp only [Nat.mul_zero, Nat.add_zero] at hu1 ⊢
  obtain ⟨M', hM', _, hI, hB⟩ := run_basic hrun
  have hMM : M = M' := Except.ok.inj (hM.symm.trans hM')
  subst hMM
  have hFR := hB.valid.toOrdered
  have hHB := hb_run hrun
  have hcr := hTop.lt
  -- the columns-invariant of the run
  obtain ⟨M1, col1, t1, root1, hM1, _, _, hTop1, hCI, _⟩ :=
    run_new_column hrun u.1.isLt (by rw [hu1, hMs])
  have hMM1 : M = M1 := Except.ok.inj (hM.symm.trans hM1)
  subst hMM1
  have htt : t = t1 := Option.some.inj (hTop.top.symm.trans hTop1.top)
  subst htt
  have hrr : root = root1 := Option.some.inj (hTop.left.symm.trans hTop1.left)
  subst hrr
  -- the node `pM` of `M(s)` below the top of `x₀`
  obtain ⟨pM, hpM1, hpMh, hpMl, hpMmax⟩ := seam_block0_node hrun hTop hCI hu1 hu hU hup hτup
  have hx0 : M.size - 1 < M.size := by omega
  obtain ⟨colx, hcolx, htop⟩ : ∃ colx, M[M.size - 1]? = some colx ∧ colx.back? = some t := by
    have h := hTop.top
    cases hc : M[M.size - 1]? with
    | none => rw [hc] at h; cases h
    | some colx => rw [hc] at h; exact ⟨colx, rfl, h⟩
  obtain ⟨_, hcolxe⟩ := Array.getElem?_eq_some_iff.mp hcolx
  subst hcolxe
  rw [Array.back?_eq_getElem?] at htop
  obtain ⟨htl, htc⟩ := Array.getElem?_eq_some_iff.mp htop
  let tN : (Frame.ofMountain M).Node := ⟨⟨M.size - 1, hx0⟩, ⟨M[M.size - 1].size - 1, htl⟩⟩
  have htNc : (Frame.ofMountain M).cell tN = t := htc
  have htNh : (Frame.ofMountain M).height tN = t.row := by
    change ((Frame.ofMountain M).cell tN).row = _
    rw [htNc]
  have hpMtN : pM.1 = tN.1 := Fin.ext hpM1
  have hpMlt : pM.2.val < tN.2.val :=
    index_lt_of_height_lt hG hpMtN (by rw [hpMh, htNh]; exact hU)
  have hpMu : (Frame.ofMountain M).upper pM = some tN := by
    apply upper_eq_of_index hpMtN
    by_contra hne
    have hlen : pM.2.val + 1 < (Frame.ofMountain M).length pM.1 := by
      have := tN.2.isLt
      have hl : (Frame.ofMountain M).length tN.1 = (Frame.ofMountain M).length pM.1 := by
        rw [hpMtN]
      omega
    let V : (Frame.ofMountain M).Node := ⟨pM.1, ⟨pM.2.val + 1, hlen⟩⟩
    have h1 : (Frame.ofMountain M).height pM < (Frame.ofMountain M).height V :=
      height_lt_of_index hG rfl (by simp [V])
    have h2 : (Frame.ofMountain M).height V < (Frame.ofMountain M).height tN :=
      height_lt_of_index hG hpMtN (by simp [V]; omega)
    rw [htNh] at h2
    exact absurd (hpMmax V hpM1 h2) (not_le.mpr h1)
  -- the root
  have htl' : ((Frame.ofMountain M).cell tN).left = some root := by rw [htNc]; exact hTop.left
  obtain ⟨rootN, hrl, _, _⟩ := hG.stored_valid tN root htl'
  have hrr : ref rootN = root := lookup_spec hrl
  have hrawp : (Frame.ofMountain M).rawParent pM = some rootN :=
    rawParent_eq_of_upper_left hpMu (by rw [hrr]; exact htl')
  have hpMr : Real pM :=
    real_of_one_le hG (by rw [hpMh]; exact one_le_height hFR hu)
  obtain ⟨hr1, hr2⟩ := hbAt_of_normal hNM hpMr tN rootN hpMu hrawp
  rw [htNh] at hr1
  have hrootc : rootN.1.val = root.column := by rw [← hrr]; rfl
  -- the canonical search from `Q pM`
  have hPp : (Frame.ofMountain M).P pM = some rootN := (hNM.rawParent_eq_P hpMr).symm.trans hrawp
  obtain ⟨qM, hqM, hit⟩ := (P_iff hG).mp hPp
  have hqMr : Real qM := Q_real hG hpMr hqM
  have hpath := hit.parentPath hG (hG.real_positive qM hqMr)
  have hchain := ParentPath.rawChain hNM hpath hqMr
  -- the columns left of `x₀` are shared
  have hCop : Copies (Frame.ofMountain M) (Frame.ofMountain R) (fun _ => 0) id (M.size - 1) :=
    fun y hy => upperCopy_old hVM (hI.2.1 y hy) (fun a _ => rfl)
  have hqK : qM.1.val < M.size - 1 := by
    have := Q_column_lt hG hqM
    rw [hpM1] at this
    exact this
  obtain ⟨qF, hqF, hIq⟩ := q_transport' hG hFR hCop (n := pM) (U := u)
    (fun a ha => ⟨a, by rw [hpMl]; exact ha, rfl⟩) hpMh.symm hqM (Row.zero_le _) hqK
  rw [hq] at hqF
  obtain rfl := Option.some.inj hqF
  obtain ⟨C, hCch, hIC⟩ := chain_transport hNM hFR hCop hHB hchain hqK
    (fun _ _ _ => Row.zero_le _) hqMr hIq
  -- the node of `c_r` copied to `u⁺`
  obtain ⟨i', x', hx'b, hXeq', C0⟩ := upperCopy_new hTop hCI hFR up.1.isLt (by
    obtain ⟨hup1, _⟩ := upper_spec hup
    rw [hup1, hu1])
  obtain ⟨hx'gt, hx'le⟩ := mem_blockColumns hcr hx'b
  have hup1 : up.1.val = M.size - 1 := by rw [(upper_spec hup).1, hu1]
  have hi' : i' = 0 := by
    by_contra h
    have : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i' :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  subst hi'
  have hx' : x' = M.size - 1 := by simp at hXeq'; omega
  have hsrc : srcCol M root x' = root.column := by unfold srcCol; rw [if_pos hx']
  rw [hsrc] at C0
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  obtain ⟨N, hNc, hNh⟩ := C0.bwd up rfl hτup
  -- the node above the root is `N`
  have hNr : rootN.1 = N.1 := Fin.ext (by rw [hrootc, hNc])
  have hrN : rootN.2.val < N.2.val :=
    index_lt_of_height_lt hG hNr (by rw [hNh]; exact lt_of_lt_of_le hr1 hτup)
  have hlenr : rootN.2.val + 1 < (Frame.ofMountain M).length rootN.1 := by
    have := N.2.isLt
    have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length rootN.1 := by
      rw [hNr]
    omega
  let rp : (Frame.ofMountain M).Node := ⟨rootN.1, ⟨rootN.2.val + 1, hlenr⟩⟩
  have hru : (Frame.ofMountain M).upper rootN = some rp := upper_eq_of_index rfl rfl
  have hrpτ : t.row ≤ (Frame.ofMountain M).height rp := by
    by_contra hlt
    have := hr2 rp rfl (by rw [htNh]; exact lt_of_not_ge hlt)
    simp [rp] at this
  have hrpN : (Frame.ofMountain M).height rp = (Frame.ofMountain M).height N := by
    apply le_antisymm
    · exact height_le_of_index hG hNr (by simp [rp]; omega)
    · by_contra hlt
      have hlt' : (Frame.ofMountain M).height rp < (Frame.ofMountain M).height N :=
        lt_of_not_ge hlt
      obtain ⟨Z, hZc, hZh⟩ := C0.fwd rp (by simp [rp, hrootc]) hrpτ
      have hZup : Z.1 = up.1 := Fin.ext (by rw [hZc, hup1])
      have hZi := index_lt_of_height_lt hFR hZup (by rw [hZh, ← hNh]; exact hlt')
      obtain ⟨hupc, hupi⟩ := upper_spec hup
      have hZu : (Frame.ofMountain R).height Z ≤ (Frame.ofMountain R).height u :=
        height_le_of_index hFR (hZup.trans hupc) (by omega)
      rw [hZh] at hZu
      exact absurd (lt_of_le_of_lt (hrpτ.trans hZu) hU) (lt_irrefl _)
  -- the copy of `rp` above `C`
  have Ccr := hCop rootN.1.val (by rw [hrootc]; exact hcr)
  obtain ⟨cp, hCu, hcpc, hcph⟩ := Ccr.upper hG hFR rfl hIC.1 (Row.zero_le _) hIC.2 hru
  refine ⟨C, cp, hCch, hCu, ?_, ?_⟩
  · rw [hcpc]
    exact hrootc
  · rw [hcph, hrpN, hNh]

/-! ## The reduction to the blocks `i ≥ 1` -/

/-- **Open.** `SeamLastHolds` for the blocks `i ≥ 1`. -/
def SeamLastPosHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    M.size - 1 ∈ blockColumns root.column (M.size - 1) n i →
    ∀ u p q up : (Frame.ofMountain R).Node,
      u.1.val = (M.size - 1) + (M.size - 1 - root.column) * i → Real u →
      (Frame.ofMountain R).height u < t.row →
      (Frame.ofMountain R).upper u = some up → t.row ≤ (Frame.ofMountain R).height up →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 →
      ∃ c cp, RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).upper c = some cp ∧
        cp.1.val = root.column + (M.size - 1 - root.column) * i ∧
        (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up

theorem seamLastHolds_of_pos (h : SeamLastPosHolds) : SeamLastHolds := by
  intro s n R M t root i hrun hTop hmem u p q up hu1 hu hU hup hτup hraw hq hcol
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    exact seamLast_block0 hrun hTop hu1 hu hU hup hτup hq
  · exact h s n R M t root i hrun hTop hi hmem u p q up hu1 hu hU hup hτup hraw hq hcol

/-- **`CrossLexFor IsUpper` from the two open statements** (`SeamLastPosHolds` for the seam
of the copies of `x₀` in the blocks `i ≥ 1`, `InnerHolds` for the copies of `x ≠ x₀`). -/
theorem crossLexFor_upper_of_pos (hSP : SeamLastPosHolds) (hIn : InnerHolds) :
    CrossLexFor IsUpper :=
  crossLexFor_upper (seamLastHolds_of_pos hSP) hIn

end OmegaY.Official.Recon.CrossUpper

#print axioms OmegaY.Official.Recon.CrossUpper.seamLast_block0
#print axioms OmegaY.Official.Recon.CrossUpper.crossLexFor_upper_of_pos
