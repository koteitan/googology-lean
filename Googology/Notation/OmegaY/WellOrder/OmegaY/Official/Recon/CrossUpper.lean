/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpper.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperColumns
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossKinds

set_option backward.do.legacy false

/-!
# `CrossLexFor IsUpper`

Let `u⁺` be a node of a new column `X = x + w·i` of the output `R` whose origin is the
upper part (`IsUpper`), `u` the node below it, `p = π(u⁺)`, and `q = Q u` not in the column
of `p`. The upper part of `X` copies the rows `≥ τ` of the column `x'` (`x' = x`, or `c_r`
for `x = x₀`) of `M = M(s)` (`upperCopy_new`). Let `N` be the node of `x'` copied to `u⁺`,
`n` the node below `N` in `M`, `n_p = π_M(n)` and `q_M = Q_M(n)`.

## What is proved

The source mountain `M` is normal, so its cross case holds (`normal_crossLex`): a chain of
stored parents from `q_M` reaches a node `c_M` with `π_M(c_M) = n_p`,
`row c_M⁺ = row N` and `Lex N c_M⁺`. The copy of `c_M⁺` is in the column
`f(col c_M)` of `R`, `f = shiftCol c_r w i`. Two facts carry over to `R` for any node `c`
of `R` below this copy (`finish`):

* `π(c⁺) = p`: both are in the column `f(col n_p)`, and both are the highest nodes of that
  column below the row `row u⁺ = row c⁺` (`hb_run`, `hb_eq`);
* `Lex u⁺ c⁺`: `Lex` of the copies from `Lex N c_M⁺` (`lex_transport`), since the columns
  above both are upper copies with the same column map `f`.

So only the chain of stored parents from `q = Q u` to `c` is left. It is proved when `u`
itself is in the upper part (`row u ≥ τ`, so `u` copies `n`) and every node of the chain
`q_M → … → c_M` is copied (it is left of `c_r`, or at a row `≥ τ`: `ChainCopied`): then
`Q u` is the copy of `q_M` (`q_transport`) and the chain is the copy of the chain of `M`
(`chain_transport`). This covers every node `u` of the upper part in a copy of `x₀`
(the chain is left of `c_r`).

## What is open

* `SeamLastHolds`: `x = x₀` and `row u < τ` (the seam of a copy of `x₀`; `u⁺` copies the
  node of `c_r` above the root). The chain from `q` reaches the node below the copy of
  `u⁺` in the column `c_r + w·i`. Block `0` is proved in `CrossUpperSeam.lean`
  (`seamLast_block0`); the blocks `i ≥ 1` are left open there (`SeamLastPosHolds`).
* `InnerHolds`: `x ≠ x₀`, and `row u < τ` or the chain of `M` is not copied. The chain
  from `q` reaches the node below the copy of `c_M⁺` in the column `f(col c_M)`.

`crossLexFor_upper : SeamLastHolds → InnerHolds → CrossLexFor IsUpper`, and
`crossLexFor_upper_of_pos : SeamLastPosHolds → InnerHolds → CrossLexFor IsUpper`
(`CrossUpperSeam.lean`).

## Numerical check

`reference/official/cross-upper.cjs` checks the open statements, and the chains built by
the proved cases, on every cross node with `u⁺` upper (`n = 1, 2, 3`), with no failure:

| sample | `x = x₀`, `row u ≥ τ` (proved) | seam, block `0` (proved) | `x ≠ x₀`, copied (proved) | `SeamLastPosHolds` | `InnerHolds` |
|---|---:|---:|---:|---:|---:|
| standard S1–S3, S6 | 4578 | 17682 | 5226 | 17682 | 38808 |
| legal, length ≤ 6, entries ≤ 6 | 342 | 5961 | 2202 | 5961 | 12882 |
| random legal (`--random 20000,10,10,7`) | 1266 | 9111 | 7830 | 9111 | 28452 |

The test also checks the two facts the proof derives (`π(c⁺) = p` and `Lex u⁺ c⁺`).
-/

namespace OmegaY.Official.Recon.CrossUpper

open Canonical Expansion Geometry Frame Classification
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## The open statements -/

/-- Every node of the chain from `a` to `b`, except `b`, is copied. -/
def ChainCopied (G : Frame) (θ : Nat → Row) (a b : G.Node) : Prop :=
  ∀ v, RawChain G a v → RawChain G v b → v ≠ b → θ v.1.val ≤ G.height v

/-- **Open.** The seam of a copy of `x₀`: `x = x₀` and `row u < τ`. -/
def SeamLastHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root →
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

/-- **Open.** A copy of `x ≠ x₀` when `row u < τ` or the chain of `M` is not copied: the
chain from `q` reaches the node below the copy of `c_M⁺`. -/
def InnerHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root →
    x ∈ blockColumns root.column (M.size - 1) n i → x ≠ M.size - 1 →
    ∀ (u p q up : (Frame.ofMountain R).Node) (n0 N np qM : (Frame.ofMountain M).Node),
      u.1.val = x + (M.size - 1 - root.column) * i → Real u →
      (Frame.ofMountain R).upper u = some up → t.row ≤ (Frame.ofMountain R).height up →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 →
      N.1.val = x → (Frame.ofMountain M).height N = (Frame.ofMountain R).height up →
      (Frame.ofMountain M).upper n0 = some N → (Frame.ofMountain M).rawParent n0 = some np →
      (Frame.ofMountain M).Q n0 = some qM →
      ((Frame.ofMountain R).height u < t.row ∨
        ¬ ChainCopied (Frame.ofMountain M) (copyRow root t) qM np) →
      ∃ (cM : (Frame.ofMountain M).Node) (c cp : (Frame.ofMountain R).Node),
        RawChain (Frame.ofMountain M) qM cM ∧ (Frame.ofMountain M).rawParent cM = some np ∧
        RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).upper c = some cp ∧
        cp.1.val = shiftCol root.column (M.size - 1 - root.column) i cM.1.val ∧
        (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up

/-! ## The upper origin is at a row `≥ τ` -/

theorem emitsT_upper_ge {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, p.2.isUpper = true → τ ≤ p.1.row := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp hup
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, _, hq⟩ := mem_of_mapM houts hout
          rw [runItemT_not_upper ctx q.1 q.2 out hq p hpo] at hup
          cases hup
      · unfold upperT at hupper
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hupper hp
        have hτq := (List.mem_filter.mp hq).2
        simp only [decide_eq_true_eq] at hτq
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        cases hlc : leftColumn q.2 with
        | error e => rw [hlc] at hqp; cases hqp
        | ok v =>
            rw [hlc] at hqp
            cases hqp
            exact hτq

theorem stored_mono {a b : Row} (h : a ≤ b) : Official.stored a ≤ Official.stored b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (stored_strictMono h).le
  · exact le_rfl

/-- A node of the output with an upper origin is at a row `≥ τ`. -/
theorem originAt_upper_row {s : List Nat} {n : Nat} {R : Mountain}
    {v : (Frame.ofMountain R).Node} {o : Origin} (hv : 1 ≤ v.2.val)
    (ho : OriginAt s n R v.1.val (v.2.val - 1) o) (hK : IsUpper o) :
    ∃ M col t root, Canonical.build s = .ok M ∧ M[M.size - 1]? = some col ∧
      col.back? = some t ∧ t.left = some root ∧
      Official.stored (Official.official t.row) ≤ (Frame.ofMountain R).height v := by
  obtain ⟨r, rfl⟩ := hK
  obtain ⟨M, col, t, root, x, i, es, em, hM, hcolM, ht, hroot, _, _, _, hes,
    ⟨colX, hRX, _, hasm⟩, hj⟩ := ho
  refine ⟨M, col, t, root, hM, hcolM, ht, hroot, ?_⟩
  have hjlt : v.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[v.2.val - 1] = (em, Origin.upper r) := by
    rw [List.getElem?_eq_getElem hjlt] at hj
    exact Option.some.inj hj
  have hge := emitsT_upper_ge hes _ (List.getElem_mem hjlt) (by rw [hej]; rfl)
  rw [hej] at hge
  obtain ⟨_, hcells⟩ := assemble_spec hasm
  obtain ⟨cell, hcell, hrow, _⟩ := hcells (v.2.val - 1) (by simpa using hjlt)
  have hcv : (Frame.ofMountain R).cell v = cell := by
    refine frame_cell_of hRX ?_
    rw [show v.2.val = v.2.val - 1 + 1 by omega]
    exact hcell
  change Official.stored (Official.official t.row) ≤ ((Frame.ofMountain R).cell v).row
  rw [hcv, hrow]
  simp only [List.getElem_map, hej]
  exact stored_mono hge

/-! ## The root column in block `i` -/

/-- The column `c_r + w·i` copies the upper part of `c_r` with the column map of block `i`. -/
theorem upperCopy_root {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root)
    (hCI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (Official.official t.row) R) (hFR : (Frame.ofMountain R).Ordered) {i : Nat}
    (hlt : root.column + (M.size - 1 - root.column) * i < R.size) :
    UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) root.column
      (root.column + (M.size - 1 - root.column) * i) := by
  have hM := hTop.build
  have hVM := build_valid_of_success hM
  have hFM := hVM.toOrdered
  have hcr := hTop.lt
  set w := M.size - 1 - root.column with hw
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.mul_zero, Nat.add_zero]
    exact upperCopy_old hVM (hCI.1 root.column (by omega)).symm
      (fun a ha => shiftCol_of_lt ha)
  · have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi
    obtain ⟨i', x'', hx''b, hYeq, C⟩ := upperCopy_new hTop hCI hFR hlt (by omega)
    rw [← hw] at hYeq C
    obtain ⟨hx''gt, hx''le⟩ := mem_blockColumns hcr hx''b
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have hdec := decomp_eq (w := w) (a := w - 1) (b := x'' - root.column - 1)
      (i := i0) (j := i') (by omega) (by omega) (by
        have e1 : w * (i0 + 1) = w * i0 + w := Nat.mul_succ w i0
        rw [e1] at hYeq
        generalize w * i0 = P at hYeq ⊢
        generalize w * i' = Q at hYeq ⊢
        omega)
    have hx'' : x'' = M.size - 1 := by omega
    have hs : srcCol M root x'' = root.column := by unfold srcCol; rw [if_pos hx'']
    rw [hs] at C
    exact C.congr hFM (fun a ha => by rw [shiftCol_of_lt ha, shiftCol_of_lt ha])

/-! ## The parent and `Lex` from the source -/

/-- **The parent and `Lex` of the copy of `c_M⁺`.** Let `u⁺` copy `N` (in the column `X`,
an upper copy of `x'`), `π_M(N) = n_p`, and let `c_M⁺` be a node of `M` with the parent
`n_p`, the row of `N` and `Lex N c_M⁺`, whose column is copied to `f(col c_M)`. For a
node `c` of `R` below the copy `c⁺` of `c_M⁺`: `π(c⁺) = π(u⁺)` and `Lex u⁺ c⁺`. -/
theorem finish {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hFR : (Frame.ofMountain R).Ordered) {i xa X : Nat}
    (C0 : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) xa X)
    {u up p c cp : (Frame.ofMountain R).Node} {N cM cMp np : (Frame.ofMountain M).Node}
    (hu : Real u) (hup : (Frame.ofMountain R).upper u = some up)
    (hraw : (Frame.ofMountain R).rawParent u = some p) (hupX : up.1.val = X)
    (hN : N.1.val = xa)
    (hNh : (Frame.ofMountain M).height N = (Frame.ofMountain R).height up)
    (hτN : t.row ≤ (Frame.ofMountain M).height N)
    (hNl : ((Frame.ofMountain M).cell N).left = some (Frame.ref np))
    (Ccm : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) cM.1.val
      (shiftCol root.column (M.size - 1 - root.column) i cM.1.val))
    (hcMu : (Frame.ofMountain M).upper cM = some cMp)
    (hcMraw : (Frame.ofMountain M).rawParent cM = some np)
    (hcMh : (Frame.ofMountain M).height cMp = (Frame.ofMountain M).height N)
    (hlex : Lex (Frame.ofMountain M) N cMp)
    (hc : Real c) (hcu : (Frame.ofMountain R).upper c = some cp)
    (hcpc : cp.1.val = shiftCol root.column (M.size - 1 - root.column) i cM.1.val)
    (hcph : (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up) :
    (Frame.ofMountain R).rawParent c = some p ∧ Lex (Frame.ofMountain R) up cp := by
  obtain ⟨M', hM', _, _, hB⟩ := run_basic hrun
  have hMM : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  subst hMM
  have hNM : (Frame.ofMountain M).Normal :=
    build_normal_of_legal (build_success_legal hTop.build) hTop.build
  have hG := hNM.toOrdered
  have hHB := hb_run hrun
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  -- the column of `p`
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  obtain ⟨Aref, hA, hAc⟩ := C0.par N up (Frame.ref np) hN hupX hτN hNh.symm hNl
  have hAp : Aref = Frame.ref p := Option.some.inj (hA.symm.trans hpl)
  have hpcol : p.1.val = shiftCol root.column (M.size - 1 - root.column) i np.1.val := by
    have e : p.1.val = Aref.column := by rw [hAp]; rfl
    rw [e, hAc]
    rfl
  -- the stored parent of `c`
  obtain ⟨cMp', hcMu', hcMl⟩ := rawParent_spec hcMraw
  rw [hcMu] at hcMu'
  obtain rfl := Option.some.inj hcMu'
  obtain ⟨hcM1, hcM2⟩ := upper_spec hcMu
  have hτc : t.row ≤ (Frame.ofMountain M).height cMp := by rw [hcMh]; exact hτN
  obtain ⟨Bref, hBl, hBc⟩ := Ccm.par cMp cp (Frame.ref np) (by rw [hcM1]) hcpc hτc
    (by rw [hcph, hcMh, hNh]) hcMl
  obtain ⟨B, hBlk, _, _⟩ := hFR.stored_valid cp Bref hBl
  have hBr : Frame.ref B = Bref := lookup_spec hBlk
  have hrawc : (Frame.ofMountain R).rawParent c = some B :=
    rawParent_eq_of_upper_left hcu (by rw [hBr]; exact hBl)
  have hBcol : B.1.val = shiftCol root.column (M.size - 1 - root.column) i np.1.val := by
    have e : B.1.val = Bref.column := by rw [← hBr]; rfl
    rw [e, hBc]
    rfl
  have hBp : B = p := hb_eq (hHB c hc) (hHB u hu) hcu hup hcph hrawc hraw
    (Fin.ext (by rw [hBcol, hpcol]))
  subst hBp
  refine ⟨hrawc, ?_⟩
  exact lex_transport hG hFR (shiftCol_strictMono _ _ _) ht1 hHB hlex C0 Ccm hN
    (by rw [hcM1]) hupX hcpc hτN hτc hNh.symm (by rw [hcph, hcMh, hNh])

/-! ## The main theorem -/

/-- **`CrossLexFor IsUpper` from the two open statements.** -/
theorem crossLexFor_upper (hSL : SeamLastHolds) (hIn : InnerHolds) : CrossLexFor IsUpper := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hK
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hx' : s.length - 1 ≤ up.1.val := by rw [hup1]; exact hx
  obtain ⟨M, col, t, root, hM, hcolM, ht, hTop, hCI, _⟩ := run_new_column hrun up.1.isLt hx'
  obtain ⟨M', col', t', _, hM', hcolM', ht', _, hτup⟩ :=
    originAt_upper_row (by omega) ho hK
  have hMM : M = M' := Except.ok.inj (hM.symm.trans hM')
  subst hMM
  have hcc : col = col' := Option.some.inj (hcolM.symm.trans hcolM')
  subst hcc
  have htt : t = t' := Option.some.inj (ht.symm.trans ht')
  subst htt
  have hMs := Canonical.build_size hM
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  have hFR := hB.valid.toOrdered
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  have hG := hNM.toOrdered
  have hHB := hb_run hrun
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  rw [Classification.stored_official ht1] at hτup
  have hcr := hTop.lt
  set w := M.size - 1 - root.column with hw
  -- the column `X` of `u`
  obtain ⟨i, x, hxb, hXeq, C0⟩ := upperCopy_new hTop hCI hFR up.1.isLt (by omega)
  rw [← hw] at hXeq C0
  set f := shiftCol root.column w i with hf
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hxb
  have huX : u.1.val = x + w * i := by rw [← hup1]; exact hXeq
  -- the node `N` of `M` copied to `u⁺`, and the node `n₀` below it
  obtain ⟨N, hNc, hNh⟩ := C0.bwd up rfl hτup
  have ht1' : (1 : Row) < t.row := by
    rcases lt_or_eq_of_le ht1 with h | h
    · exact h
    · exfalso
      apply hTop.real
      rw [← h]
      exact official_one
  have hN2 : 2 ≤ N.2.val := by
    by_contra hn
    have hle : (Frame.ofMountain M).height N ≤ 1 := by
      have hlen : 1 < (Frame.ofMountain M).length N.1 := by
        have := hG.length_ge_two N.1
        omega
      have := height_le_of_index hG (a := N) (b := ⟨N.1, ⟨1, hlen⟩⟩) rfl (by simp; omega)
      rwa [show (Frame.ofMountain M).height ⟨N.1, ⟨1, hlen⟩⟩ = 1 from hG.bottom_row N.1 hlen]
        at this
    rw [hNh] at hle
    exact absurd (lt_of_lt_of_le ht1' (hτup.trans hle)) (lt_irrefl _)
  let n0 : (Frame.ofMountain M).Node := ⟨N.1, ⟨N.2.val - 1, by have := N.2.isLt; omega⟩⟩
  have hn0N : (Frame.ofMountain M).upper n0 = some N := upper_eq_of_index rfl (by simp [n0]; omega)
  have hn0r : Real n0 := by show 0 < N.2.val - 1; omega
  obtain ⟨np, hPn0, _, _, hNl⟩ := hNM.upper_step n0 N hn0r hn0N
  have hn0raw : (Frame.ofMountain M).rawParent n0 = some np := rawParent_eq_of_upper_left hn0N hNl
  obtain ⟨qM, hqM, _⟩ := (P_iff hG).mp hPn0
  have hn0c : n0.1.val = srcCol M root x := hNc
  have hτN : t.row ≤ (Frame.ofMountain M).height N := by rw [hNh]; exact hτup
  -- the column of `p`
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  obtain ⟨Aref, hA, hAc⟩ := C0.par N up (Frame.ref np) hNc rfl hτN hNh.symm hNl
  have hAp : Aref = Frame.ref p := Option.some.inj (hA.symm.trans hpl)
  have hpcol : p.1.val = f np.1.val := by
    have e : p.1.val = Aref.column := by rw [hAp]; rfl
    rw [e, hAc]
    rfl
  have hcol' : q.1.val ≠ p.1.val := fun h => hcol (Fin.ext h)
  have hcopies := copies_run hTop hCI hFR up.1.isLt hxb hXeq
  rw [← hw] at hcopies
  have hqMK : qM.1.val < srcCol M root x := by
    have := Q_column_lt hG hqM
    rw [← hn0c]
    exact this
  -- the finishing step, for a node `c_M` given by the source
  have fin : ∀ (cM cMp : (Frame.ofMountain M).Node) (c cp : (Frame.ofMountain R).Node),
      cM.1.val < srcCol M root x →
      (Frame.ofMountain M).upper cM = some cMp → (Frame.ofMountain M).rawParent cM = some np →
      (Frame.ofMountain M).height cMp = (Frame.ofMountain M).height N →
      Lex (Frame.ofMountain M) N cMp → RawChain (Frame.ofMountain R) q c →
      (Frame.ofMountain R).upper c = some cp → cp.1.val = f cM.1.val →
      (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up →
      ∃ c cp, RawChain (Frame.ofMountain R) q c ∧
        (Frame.ofMountain R).rawParent c = some p ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
        Lex (Frame.ofMountain R) up cp := by
    intro cM cMp c cp hcMK hcMu hcMraw hcMh hlex hch hcu hcpc hcph
    have hqr := Q_real hFR hu hq
    have hcr' : Real c := (hch.value_le hB.valid hB.sums hqr).1
    have Ccm := (hcopies cM.1.val hcMK).mono (show copyRow root t cM.1.val ≤ t.row by
      unfold copyRow; split_ifs
      · exact Row.zero_le _
      · exact le_rfl)
    obtain ⟨h1, h2⟩ := finish hrun hTop hFR C0 hu hup hraw rfl hNc hNh hτN hNl Ccm hcMu hcMraw
      hcMh hlex hcr' hcu hcpc hcph
    exact ⟨c, cp, hch, h1, hcu, hcph.symm, h2⟩
  by_cases hU : t.row ≤ (Frame.ofMountain R).height u
  · -- `u` is in the upper part: it copies `n₀`
    obtain ⟨n', hn'c, hn'h⟩ := C0.bwd u (by rw [← hup1]) hU
    have hn'lt : (Frame.ofMountain M).height n' < (Frame.ofMountain M).height N := by
      rw [hn'h, hNh]
      exact height_lt_of_index hFR hup1.symm (by omega)
    have hn'N : n'.1 = N.1 := Fin.ext (by rw [hn'c, hNc])
    have hi' := index_lt_of_height_lt hG hn'N hn'lt
    have hlen' : n'.2.val + 1 < (Frame.ofMountain M).length n'.1 := by
      have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length n'.1 := by
        rw [hn'N]
      have := N.2.isLt
      omega
    let n'' : (Frame.ofMountain M).Node := ⟨n'.1, ⟨n'.2.val + 1, hlen'⟩⟩
    have hn'u : (Frame.ofMountain M).upper n' = some n'' := upper_eq_of_index rfl rfl
    obtain ⟨Z', hZu, _, hZh⟩ := C0.upper hG hFR hn'c (by rw [← hup1]) (by rw [hn'h]; exact hU)
      hn'h.symm hn'u
    rw [hup] at hZu
    obtain rfl := Option.some.inj hZu
    have hn''N : n'' = N := node_eq_of_height hG hn'N (by rw [← hZh, hNh])
    have hn'n0 : n' = n0 := by
      apply node_eq_of_index (show n'.1 = n0.1 from hn'N)
      have := congrArg (fun z : (Frame.ofMountain M).Node => z.2.val) hn''N
      simp only [n''] at this
      simp only [n0]
      omega
    subst hn'n0
    -- the column of `q`
    obtain ⟨LM, hLM, _, _, hqLM, _⟩ := Q_spec hG hqM
    obtain ⟨L, hL, _, _, hqL, _⟩ := Q_spec hFR hq
    obtain ⟨Bref, hBl, hBc⟩ := C0.par n0 u (Frame.ref LM) hn0c (by rw [← hup1]) (by
      rw [hn'h]; exact hU) hn'h.symm hLM
    have hBL : Bref = Frame.ref L := Option.some.inj (hBl.symm.trans hL)
    have hqcol : q.1.val = f qM.1.val := by
      rw [hqL, hqLM]
      have e : L.1.val = Bref.column := by rw [hBL]; rfl
      rw [e, hBc]
      rfl
    have hne : qM ≠ np := by
      intro h
      apply hcol'
      rw [hqcol, hpcol, h]
    obtain ⟨cM, cMp, hchM, hcMraw, hcMu, hhN, hlexM, _⟩ :=
      normal_crossLex hNM hn0r hn0N hn0raw hqM hne
    by_cases hCC : ChainCopied (Frame.ofMountain M) (copyRow root t) qM np
    · -- the chain of `M` is copied
      have hqD := hCC qM (.here qM) (hchM.snoc hcMraw) hne
      obtain ⟨qF, hqF, hIq⟩ := q_transport hG hFR hcopies C0 hn0c (by rw [← hup1])
        (by rw [hn'h]; exact hU) hn'h.symm hqM hqD hqMK
      rw [hq] at hqF
      obtain rfl := Option.some.inj hqF
      have hqMr : Real qM := Q_real hG hn0r hqM
      obtain ⟨C, hCch, hIC⟩ := chain_transport hNM hFR hcopies hHB hchM hqMK
        (fun v h1 h2 => hCC v h1 (h2.snoc hcMraw) (by
          intro hv
          subst hv
          have := h2.column_le hG
          have := rawParent_column_lt hG hcMraw
          omega)) hqMr hIq
      have hcMK : cM.1.val < srcCol M root x :=
        lt_of_le_of_lt (hchM.column_le hG) hqMK
      have hcMD := hCC cM hchM (.step hcMraw (.here np)) (by
        intro hv
        subst hv
        have := rawParent_column_lt hG hcMraw
        omega)
      obtain ⟨Cp, hCu, hCpc, hCph⟩ := (hcopies cM.1.val hcMK).upper hG hFR rfl hIC.1 hcMD
        hIC.2 hcMu
      exact fin cM cMp C Cp hcMK hcMu hcMraw hhN.symm hlexM hCch hCu hCpc
        (by rw [hCph, ← hhN, hNh])
    · -- open: the chain of `M` leaves the copied nodes, so `x ≠ x₀`
      have hxx0 : x ≠ M.size - 1 := by
        intro hx0
        apply hCC
        intro v hv _ _
        have hs : srcCol M root x = root.column := by unfold srcCol; rw [if_pos hx0]
        have := hv.column_le hG
        unfold copyRow
        rw [if_pos (by omega)]
        exact Row.zero_le _
      obtain ⟨cM', c, cp, h1, h2, h3, h4, h5, h6⟩ := hIn s n R M t root i x hrun hTop hxb hxx0
        u p q up n0 N np qM huX hu hup hτup hraw hq hcol
        (by rw [hNc]; unfold srcCol; rw [if_neg hxx0]) hNh hn0N hn0raw hqM (Or.inr hCC)
      have he : cM' = cM := rawChain_last_unique hG h1 hchM h2 hcMraw
      subst he
      exact fin cM' cMp c cp (lt_of_le_of_lt (h1.column_le hG) hqMK) hcMu hcMraw hhN.symm hlexM
        h3 h4 h5 h6
  · -- `u` is in the lower part
    have hU' : (Frame.ofMountain R).height u < t.row := lt_of_not_ge hU
    by_cases hxx0 : x = M.size - 1
    · -- the seam of a copy of `x₀`
      subst hxx0
      have hs : srcCol M root (M.size - 1) = root.column := by unfold srcCol; rw [if_pos rfl]
      obtain ⟨c, cp, hch, hcu, hcpc, hcph⟩ := hSL s n R M t root i hrun hTop hxb u p q up
        huX hu hU' hup hτup hraw hq hcol
      have hqr := Q_real hFR hu hq
      have hcr' : Real c := (hch.value_le hB.valid hB.sums hqr).1
      have hwi : root.column + w * i < R.size := by
        have := up.1.isLt
        change up.1.val < R.size at this
        omega
      have Croot := upperCopy_root hTop hCI hFR hwi
      rw [← hw] at Croot
      have hNcr : N.1.val = root.column := by rw [hNc, hs]
      have hn0cr : n0.1.val = root.column := hNcr
      have hfcr : f root.column = root.column + w * i := shiftCol_of_le le_rfl
      have Cn0 : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row f n0.1.val
          (f n0.1.val) := by
        rw [hn0cr, hfcr]
        exact Croot
      have hlexN := lex_refl hNM _ N rfl (real_of_upper hn0N)
      obtain ⟨h1, h2⟩ := finish hrun hTop hFR C0 hu hup hraw rfl hNc hNh hτN hNl Cn0 hn0N
        hn0raw rfl hlexN hcr' hcu (by rw [hcpc, hn0cr]; exact (shiftCol_of_le le_rfl).symm) hcph
      exact ⟨c, cp, hch, h1, hcu, hcph.symm, h2⟩
    · -- a copy of `x ≠ x₀`
      obtain ⟨cM, c, cp, h1, h2, h3, h4, h5, h6⟩ := hIn s n R M t root i x hrun hTop hxb hxx0
        u p q up n0 N np qM huX hu hup hτup hraw hq hcol
        (by rw [hNc]; unfold srcCol; rw [if_neg hxx0]) hNh hn0N hn0raw hqM (Or.inl hU')
      have hne : qM ≠ np := by
        intro h
        subst h
        have := h1.column_le hG
        have := rawParent_column_lt hG h2
        omega
      obtain ⟨cM', cMp, hchM, hcMraw, hcMu, hhN, hlexM, _⟩ :=
        normal_crossLex hNM hn0r hn0N hn0raw hqM hne
      have he : cM = cM' := rawChain_last_unique hG h1 hchM h2 hcMraw
      subst he
      exact fin cM cMp c cp (lt_of_le_of_lt (h1.column_le hG) hqMK) hcMu hcMraw hhN.symm hlexM
        h3 h4 h5 h6

/-- **`CrossChainHolds` with the upper kind reduced to the two open statements.** -/
theorem crossChainHolds_of_upper (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hC : CrossLexFor IsClean) (hK : CutPredHolds) (hSL : SeamLastHolds) (hIn : InnerHolds) :
    CrossChainHolds :=
  crossChainHolds_of_three hPB hP hC hK (crossLexFor_upper hSL hIn)

end OmegaY.Official.Recon.CrossUpper

#print axioms OmegaY.Official.Recon.CrossUpper.crossLexFor_upper
#print axioms OmegaY.Official.Recon.CrossUpper.crossChainHolds_of_upper
