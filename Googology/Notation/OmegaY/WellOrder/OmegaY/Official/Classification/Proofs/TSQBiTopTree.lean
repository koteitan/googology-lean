/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQBiTopTree.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQBiTopRows
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBLift
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCKids
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCStep
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCX

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# A copy of `o` at or above the boundary top, in the tree of `X` (`TSQ`, `BiTopLow`)

In the tree of the column `X = x + w·i` (block `i ≥ 1`), take an item `K` whose region has the
root top `ρ = (c_r, row ρ)` (with `x` ascending there) and holds the row `C ≥ row ρ` of a node
`o = (x, C)`, and let `q` be the top of the boundary column `B = c_r + w·i` in the target region
of `K`. Then the lower part of `X` has a copy of `o` at a row at or above `q`.

* `cb_desc`: `K` a plain item with a cut bottom (case 3). With `σ = C_d`, `h_ρ = ρ_d` and
  `h_B = q_d`: if `σ > h_ρ`, the child with source slot `σ` has target slot `σ + h_B - h_ρ > h_B`,
  and the non-gap copy `g` of `o` lies in it; if `σ = h_ρ`, the child `(S[h_ρ], T[h_B])` (a copy
  of the root row at level 2, a cut-bottom plain item above) contains `q`, and we go down.
* `lift_desc`: `K` a first item without a cut bottom (case 2), with `q_d = h_ρ + lift`
  (`bnd_lift`). The same argument with the lifted children.

`locate`: a traced emit whose row is in the target region of an item of the tree lies in one of
its children, with `EmitOK` there.
-/

namespace OmegaY.Official.Recon.TSQ.BTL

open Canonical Classification Classification.Proofs.ChainCorr
open Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC

section Tree

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}

/-- **A traced emit of the target region of an item lies in one of its children.** -/
theorem locate (hNC : NewColumn s n R M t root i x) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root i x) p.1 p.2) = .ok outsT)
    {g : Emit × Origin} (hg : g ∈ outsT.flatten) {d : Nat} {K : Item}
    (hK : InTree (colCtx M R root i x) (official t.row) (d + 2) K)
    (hin : inRegion (d + 2) K.target g.1.row = true) :
    ∃ cs, childItems (colCtx M R root i x) (d + 2) K = .ok cs ∧ ∃ m, ∃ hm : m < cs.length,
      inRegion (d + 1) cs[m].target g.1.row = true ∧
      Inner.EmitOK M root.column (d + 1) cs[m] g := by
  have rX := hNC.runCtx
  obtain ⟨TK, hTK, _, hback, _⟩ := tinTree rX houts hK
  have hgK := hback g hg hin
  obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children hTK
  obtain ⟨L', hL', hgL'⟩ := List.mem_flatten.mp hgK
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
  obtain ⟨hlen, hget⟩ := forall₂_getElem hF
  have hm' : m < cs.length := by omega
  have hcT := LowerLeftProof.inTree_snoc hK hcs (List.getElem_mem hm')
  obtain ⟨hd1, hcOK⟩ := LowerLeftProof.inTree_itemOK rX hcT
  have hreg := runItemT_region rX hd1 hcOK (hget m hm' hm) g hgL'
  exact ⟨cs, hcs, m, hm', hreg, eok_of_tree rX houts hg hcT hreg⟩

/-- Two rows of a region of level `d + 2` compare by their coefficient `d`. -/
theorem lt_of_region_coeff {d : Nat} {T a b : Row} (ha : inRegion (d + 2) T a = true)
    (hb : inRegion (d + 2) T b = true) (h : a.coeff d < b.coeff d) : a < b := by
  refine Row.lt_iff.mpr ⟨d, fun q hq => ?_, h⟩
  rw [inRegion_iff'.mp ha q (by omega), inRegion_iff'.mp hb q (by omega)]

/-- Two rows of a region of level `2` with the same coefficient `0` are equal. -/
theorem eq_of_region2 {T a b : Row} (ha : inRegion 2 T a = true)
    (hb : inRegion 2 T b = true) (h : a.coeff 0 = b.coeff 0) : a = b := by
  apply Row.ext
  intro q
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; exact h
  · rw [inRegion_iff'.mp ha q (by omega), inRegion_iff'.mp hb q (by omega)]

/-- The emit of a level-1 item copying the root row `C` at a node `(x, C)`. -/
theorem levelOne_clean_emit {ctx : Context} {it : Item} {TB : List (Emit × Origin)}
    (h : runItemT ctx 1 it = .ok TB) {oRef : Ref} {cv : Cell} {C : Row}
    (hsrc : nodeAt ctx.source ctx.x it.source = some (oRef, cv)) (hcl : it.clean = some C)
    (hC : nodeAt ctx.source ctx.x C = some (oRef, cv)) :
    ∃ e ∈ TB, e.2.src = oRef ∧ e.1.row = it.target := by
  have h' : levelOneT ctx it = .ok TB := by simpa [runItemT] using h
  unfold levelOneT at h'
  rw [hsrc, hcl] at h'
  simp only [hC, bind, Except.bind, pure, Except.pure] at h'
  split at h'
  · cases h'
  · cases h'
    exact ⟨_, List.mem_singleton_self _, rfl, rfl⟩

/-- **The cut-bottom descent.** -/
theorem cb_desc (hNC : NewColumn s n R M t root i x) (hi0 : i ≠ 0)
    {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root i x) p.1 p.2) = .ok outsT)
    {oRef : Ref} {cv : Cell} (hno : nodeAt M x (official cv.row) = some (oRef, cv))
    {pa : Ref} {pc : Cell} (hasc : ascends (colCtx M R root i x) (some (pa, pc)) = .ok true)
    {g : Emit × Origin} (hg : g ∈ outsT.flatten) (hgsrc : g.2.src = oRef)
    (hgc : Reserve.cell? M oRef = some cv) :
    ∀ d K, InTree (colCtx M R root i x) (official t.row) (d + 2) K → K.clean = none →
      K.cutBottom = true → topIn M root.column (d + 2) K.source = some (pa, pc) →
      inRegion (d + 2) K.source (official cv.row) = true → official pc.row ≤ official cv.row →
      ∀ q, topIn R (root.column + (M.size - 1 - root.column) * i) (d + 2) K.target = some q →
      (official pc.row < official cv.row → inRegion (d + 2) K.target g.1.row = true) →
      ∃ e ∈ outsT.flatten, e.2.src = oRef ∧ official q.2.row ≤ e.1.row := by
  have rX := hNC.runCtx
  have hb : Canonical.build s = .ok M := hNC.top.build
  have hom := (RowLaw.nodeAt_spec hno).1
  have hgc' : Reserve.cell? M g.2.src = some cv := by rw [hgsrc]; exact hgc
  intro d
  induction d with
  | zero =>
    intro K hK hcl hcb hρ hC hρC q hq hstrict
    obtain ⟨TK, hTK, hsubK, _, _⟩ := tinTree rX houts hK
    obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children hTK
    obtain ⟨ar, ac, hax, hσa⟩ := LowerLeftProof.top_ge hb hom hC
    have hbnd := colCtx_bnd hNC (0 + 2) K.target
    obtain ⟨hlen3, hget3⟩ := kids3 hcs hcl hcb hi0 hax hρ hasc
    rw [hbnd, hq] at hlen3 hget3
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    have hρin := topIn_inRegion hρ
    have hqin := topIn_inRegion hq
    have hRσ := coeff_le_of_inRegion hρin hC hρC
    simp only [heightOf, height_eq] at hlen3 hget3
    rcases Nat.lt_or_ge ((official pc.row).coeff 0) ((official cv.row).coeff 0) with hlt | hge
    · -- strict: the non-gap copy
      have hne : official pc.row < official cv.row := lt_of_region_coeff hρin hC hlt
      obtain ⟨cs', hcs', m, hm, hgm, hE⟩ := locate hNC houts hg hK (hstrict hne)
      rw [hcs] at hcs'
      obtain rfl := Except.ok.inj hcs'
      obtain ⟨hsrcm, _⟩ := eok_parts hE hgc'
      rw [hget3 m hm] at hsrcm hgm
      rcases c3_cases (d := 0 + 2) (S := K.source) (T := K.target)
        (hR := (official pc.row).coeff 0) (hB := (official q.2.row).coeff 0)
        (C := official pc.row) (m + (official pc.row).coeff 0) with ⟨_, h2⟩ | ⟨h1, h2⟩
      · rw [h2] at hsrcm
        have := (inRegion_slot_iff.mp hsrcm).2
        omega
      · rw [h2] at hsrcm hgm
        have e1 := (inRegion_slot_iff.mp hsrcm).2
        have e2 := inRegion_slot_iff.mp hgm
        refine ⟨g, hg, hgsrc, (lt_of_region_coeff hqin e2.1 ?_).le⟩
        rw [e2.2]
        simp at h1 e1
        omega
    · -- equal: the copy of the root row at the height of `q`
      have hσ : (official cv.row).coeff 0 = (official pc.row).coeff 0 := by omega
      have hρo : official pc.row = official cv.row := eq_of_region2 hρin hC hσ.symm
      have hσa' : (official cv.row).coeff 0 ≤ (official ac.row).coeff 0 := hσa
      have hk : (official q.2.row).coeff 0 < cs.length := by rw [hlen3]; omega
      have hcT := LowerLeftProof.inTree_snoc hK hcs (List.getElem_mem hk)
      obtain ⟨TB, hTB, hsubB, _, _⟩ := tinTree rX houts hcT
      have hitem := hget3 _ hk
      rcases c3_cases (d := 0 + 2) (S := K.source) (T := K.target)
        (hR := (official pc.row).coeff 0) (hB := (official q.2.row).coeff 0)
        (C := official pc.row) ((official q.2.row).coeff 0 + (official pc.row).coeff 0)
        with ⟨_, h2⟩ | ⟨h1, _⟩
      · rw [h2] at hitem
        have hslot : slot (0 + 2) K.source ((official pc.row).coeff 0) = official cv.row := by
          apply Row.ext
          intro r
          rcases Nat.eq_zero_or_pos r with hr | hr
          · subst hr
            rw [show (0 : Nat) + 2 = 0 + 2 from rfl, slot_coeff_at, hσ]
          · rw [slot_coeff_high hr, inRegion_iff'.mp hC r (by omega)]
        obtain ⟨e, he, hesrc, herow⟩ := levelOne_clean_emit (ctx := colCtx M R root i x)
          (it := cs[(official q.2.row).coeff 0]) hTB (oRef := oRef) (cv := cv)
          (C := official pc.row)
          (by rw [hitem]; show nodeAt M x _ = _; rw [hslot]; exact hno)
          (by rw [hitem])
          (by show nodeAt M x _ = _; rw [hρo]; exact hno)
        refine ⟨e, hsubB e he, hesrc, le_of_eq ?_⟩
        rw [herow, hitem]
        simp only [Nat.add_sub_cancel]
        have hsin : inRegion (0 + 2) K.target (slot (0 + 2) K.target ((official q.2.row).coeff 0)) =
            true := (inRegion_slot_iff.mp (self_inRegion _ _)).1
        exact eq_of_region2 hqin hsin (by rw [slot_coeff_at])
      · simp at h1
  | succ d ih =>
    intro K hK hcl hcb hρ hC hρC q hq hstrict
    obtain ⟨TK, hTK, hsubK, _, _⟩ := tinTree rX houts hK
    obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children hTK
    obtain ⟨ar, ac, hax, hσa⟩ := LowerLeftProof.top_ge hb hom hC
    have hbnd := colCtx_bnd hNC (d + 1 + 2) K.target
    obtain ⟨hlen3, hget3⟩ := kids3 hcs hcl hcb hi0 hax hρ hasc
    rw [hbnd, hq] at hlen3 hget3
    have hρin := topIn_inRegion hρ
    have hqin := topIn_inRegion hq
    have hRσ := coeff_le_of_inRegion hρin hC hρC
    simp only [heightOf, height_eq] at hlen3 hget3
    rcases Nat.lt_or_ge ((official pc.row).coeff (d + 1)) ((official cv.row).coeff (d + 1))
      with hlt | hge
    · -- strict: the non-gap copy
      have hne : official pc.row < official cv.row := lt_of_region_coeff hρin hC hlt
      obtain ⟨cs', hcs', m, hm, hgm, hE⟩ := locate hNC houts hg hK (hstrict hne)
      rw [hcs] at hcs'
      obtain rfl := Except.ok.inj hcs'
      obtain ⟨hsrcm, _⟩ := eok_parts hE hgc'
      rw [hget3 m hm] at hsrcm hgm
      rcases c3_cases (d := d + 1 + 2) (S := K.source) (T := K.target)
        (hR := (official pc.row).coeff (d + 1)) (hB := (official q.2.row).coeff (d + 1))
        (C := official pc.row) (m + (official pc.row).coeff (d + 1)) with ⟨_, h2⟩ | ⟨h1, h2⟩
      · rw [h2] at hsrcm
        have := (inRegion_slot_iff.mp hsrcm).2
        omega
      · rw [h2] at hsrcm hgm
        have e1 := (inRegion_slot_iff.mp hsrcm).2
        have e2 := inRegion_slot_iff.mp hgm
        refine ⟨g, hg, hgsrc, (lt_of_region_coeff hqin e2.1 ?_).le⟩
        rw [e2.2]
        simp at h1 e1
        omega
    · -- equal: go down to the cut-bottom child `(S[h_ρ], T[h_B])`
      have hσ : (official cv.row).coeff (d + 1) = (official pc.row).coeff (d + 1) := by omega
      have hσa' : (official cv.row).coeff (d + 1) ≤ (official ac.row).coeff (d + 1) := hσa
      have hk : (official q.2.row).coeff (d + 1) < cs.length := by rw [hlen3]; omega
      have hcT := LowerLeftProof.inTree_snoc hK hcs (List.getElem_mem hk)
      have hitem := hget3 _ hk
      rcases c3_cases (d := d + 1 + 2) (S := K.source) (T := K.target)
        (hR := (official pc.row).coeff (d + 1)) (hB := (official q.2.row).coeff (d + 1))
        (C := official pc.row)
        ((official q.2.row).coeff (d + 1) + (official pc.row).coeff (d + 1))
        with ⟨h1, _⟩ | ⟨_, h2⟩
      · simp at h1
      · rw [h2] at hitem
        simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left, decide_true] at hitem
        have hK2 := hcT
        rw [hitem] at hK2
        obtain ⟨e, he, hesrc, hle⟩ := ih _ hK2 rfl rfl
          (by
            show topIn M root.column (d + 2) (slot (d + 1 + 2) K.source _) = _
            have := Inner.topIn_slot (d := d + 1) hρ
            exact this)
          (inRegion_slot_iff.mpr ⟨hC, hσ⟩) hρC q
          (by
            show topIn R _ (d + 2) (slot (d + 1 + 2) K.target _) = _
            exact Inner.topIn_slot (d := d + 1) hq)
          (by
            intro hne
            obtain ⟨cs', hcs', m, hm, hgm, hE⟩ := locate hNC houts hg hK (hstrict hne)
            rw [hcs] at hcs'
            obtain rfl := Except.ok.inj hcs'
            obtain ⟨hsrcm, _, hcbC, _⟩ := eok_parts hE hgc'
            have hgm' := hgm
            rw [hget3 m hm] at hsrcm hgm'
            rcases c3_cases (d := d + 1 + 2) (S := K.source) (T := K.target)
              (hR := (official pc.row).coeff (d + 1)) (hB := (official q.2.row).coeff (d + 1))
              (C := official pc.row) (m + (official pc.row).coeff (d + 1)) with ⟨_, h3⟩ | ⟨h4, h3⟩
            · rw [hget3 m hm, h3] at hcbC
              have := (hcbC (official pc.row) rfl rfl).1
              rw [this] at hne
              exact absurd hne (lt_irrefl _)
            · rw [h3] at hsrcm hgm'
              have e1 := (inRegion_slot_iff.mp hsrcm).2
              simp at h4 e1
              have hmq : m = (official q.2.row).coeff (d + 1) := by omega
              subst hmq
              rw [hitem] at hgm
              exact hgm)
        exact ⟨e, he, hesrc, hle⟩

theorem c2_target (d : Nat) (S T : Row) (i hR : Nat) (lift : Int) (C : Row) (j : Nat) :
    (c2 d S T i hR lift C j).target = slot d T j := by
  unfold c2; split_ifs <;> rfl

/-- **The descent from a lifting first item.** -/
theorem lift_desc (hNC : NewColumn s n R M t root i x) (hi0 : i ≠ 0)
    {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM
      (fun p => runItemT (colCtx M R root i x) p.1 p.2) = .ok outsT)
    {oRef : Ref} {cv : Cell} (hno : nodeAt M x (official cv.row) = some (oRef, cv))
    {pa : Ref} {pc : Cell} (hasc : ascends (colCtx M R root i x) (some (pa, pc)) = .ok true)
    {g : Emit × Origin} (hg : g ∈ outsT.flatten) (hgsrc : g.2.src = oRef)
    (hgc : Reserve.cell? M oRef = some cv)
    {d : Nat} {F : Item} (hF : InTree (colCtx M R root i x) (official t.row) (d + 2) F)
    (hcl : F.clean = none) (hcb : F.cutBottom = false)
    (hρ : topIn M root.column (d + 2) F.source = some (pa, pc))
    (hC : inRegion (d + 2) F.source (official cv.row) = true)
    (hρC : official pc.row ≤ official cv.row)
    {hκ : Nat} (hκe : heightOf (d + 2) (topIn M (M.size - 1) (d + 2) F.source) = hκ)
    (hρκ : (official pc.row).coeff d < hκ)
    {q : Ref × Cell}
    (hq : topIn R (root.column + (M.size - 1 - root.column) * i) (d + 2) F.target = some q)
    (hqc : (official q.2.row).coeff d = (official pc.row).coeff d + (hκ - (official pc.row).coeff d) * i)
    (hstrict : official pc.row < official cv.row → inRegion (d + 2) F.target g.1.row = true) :
    ∃ e ∈ outsT.flatten, e.2.src = oRef ∧ official q.2.row ≤ e.1.row := by
  have rX := hNC.runCtx
  have hb : Canonical.build s = .ok M := hNC.top.build
  have hom := (RowLaw.nodeAt_spec hno).1
  have hgc' : Reserve.cell? M g.2.src = some cv := by rw [hgsrc]; exact hgc
  obtain ⟨TK, hTK, hsubK, _, _⟩ := tinTree rX houts hF
  obtain ⟨cs, outs, hcs, hFo, rfl⟩ := runItemT_children hTK
  obtain ⟨ar, ac, hax, hσa⟩ := LowerLeftProof.top_ge hb hom hC
  obtain ⟨hlen2, hget2⟩ := kids2 hcs hcl hcb hax hρ hasc
  simp only [colCtx_source, colCtx_block, colCtx_last] at hlen2 hget2
  rw [hκe] at hlen2 hget2
  have hρin := topIn_inRegion hρ
  have hqin := topIn_inRegion hq
  have hRσ := coeff_le_of_inRegion hρin hC hρC
  have hσa' : (official cv.row).coeff d ≤ (official ac.row).coeff d := hσa
  simp only [height_eq] at hlen2 hget2
  set hR := (official pc.row).coeff d with hhR
  set L := (hκ - hR) * i with hL
  have hlift : (((hκ : Nat) : Int) - ((hR : Nat) : Int)) * ((i : Nat) : Int) = ((L : Nat) : Int) := by
    rw [hL, Nat.cast_mul, Nat.cast_sub hρκ.le]
  rw [hlift] at hlen2 hget2
  rcases Nat.lt_or_ge hR ((official cv.row).coeff d) with hlt | hge
  · -- strict: the non-gap copy lies in the lifted child of its slot
    have hne : official pc.row < official cv.row := lt_of_region_coeff hρin hC hlt
    obtain ⟨cs', hcs', m, hm, hgm, hE⟩ := locate hNC houts hg hF (hstrict hne)
    rw [hcs] at hcs'
    obtain rfl := Except.ok.inj hcs'
    obtain ⟨hsrcm, _⟩ := eok_parts hE hgc'
    rw [hget2 m hm] at hsrcm hgm
    rw [c2_target] at hgm
    have e2 := inRegion_slot_iff.mp hgm
    rcases c2_cases (d := d + 2) (S := F.source) (T := F.target) (i := i) (hR := hR)
      (lift := ((L : Nat) : Int)) (C := official pc.row) m with ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, h1', h2, _, _⟩
    · rw [h2] at hsrcm
      have := (inRegion_slot_iff.mp hsrcm).2
      omega
    · rw [h2] at hsrcm
      have := (inRegion_slot_iff.mp hsrcm).2
      omega
    · rw [h2] at hsrcm
      have e1 := (inRegion_slot_iff.mp hsrcm).2
      refine ⟨g, hg, hgsrc, (lt_of_region_coeff hqin e2.1 ?_).le⟩
      rw [e2.2, hqc]
      omega
  · have hσ : (official cv.row).coeff d = hR := by omega
    have hk : hR + L < cs.length := by rw [hlen2]; omega
    have hcT := LowerLeftProof.inTree_snoc hF hcs (List.getElem_mem hk)
    have hitem := hget2 _ hk
    have hmq : (official q.2.row).coeff d = hR + L := hqc
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · -- level 2: the copy of the root row at the height of `q`
      subst hd0
      obtain ⟨TB, hTB, hsubB, _, _⟩ := tinTree rX houts hcT
      rcases c2_cases (d := 0 + 2) (S := F.source) (T := F.target) (i := i) (hR := hR)
        (lift := ((L : Nat) : Int)) (C := official pc.row) (hR + L)
        with ⟨h1, _⟩ | ⟨_, _, h2⟩ | ⟨_, h1', _⟩
      · omega
      · rw [h2] at hitem
        have hρo : official pc.row = official cv.row := eq_of_region2 hρin hC hσ.symm
        have hslot : slot (0 + 2) F.source hR = official cv.row := by
          apply Row.ext
          intro r
          rcases Nat.eq_zero_or_pos r with hr | hr
          · subst hr
            rw [slot_coeff_at, hσ]
          · rw [slot_coeff_high hr, inRegion_iff'.mp hC r (by omega)]
        obtain ⟨e, he, hesrc, herow⟩ := levelOne_clean_emit (ctx := colCtx M R root i x)
          (it := cs[hR + L]) hTB (oRef := oRef) (cv := cv) (C := official pc.row)
          (by rw [hitem]; show nodeAt M x _ = _; rw [hslot]; exact hno)
          (by rw [hitem])
          (by show nodeAt M x _ = _; rw [hρo]; exact hno)
        refine ⟨e, hsubB e he, hesrc, le_of_eq ?_⟩
        rw [herow, hitem]
        have hsin : inRegion (0 + 2) F.target (slot (0 + 2) F.target (hR + L)) = true :=
          (inRegion_slot_iff.mp (self_inRegion _ _)).1
        exact eq_of_region2 hqin hsin (by rw [slot_coeff_at, hmq])
      · simp at h1'
    · -- above level 2: the cut-bottom child `(S[h_ρ], T[h_ρ + L])`
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rcases c2_cases (d := d' + 1 + 2) (S := F.source) (T := F.target) (i := i) (hR := hR)
        (lift := ((L : Nat) : Int)) (C := official pc.row) (hR + L)
        with ⟨h1, _⟩ | ⟨_, h1', _⟩ | ⟨_, _, hs, hc, hcb2⟩
      · omega
      · simp at h1'
      · have hsrc2 : cs[hR + L].source = slot (d' + 1 + 2) F.source hR := by
          rw [hitem, hs]; congr 1; omega
        have htgt2 : cs[hR + L].target = slot (d' + 1 + 2) F.target (hR + L) := by
          rw [hitem, c2_target]
        have hcl2 : cs[hR + L].clean = none := by rw [hitem]; exact hc
        have hcb2' : cs[hR + L].cutBottom = true := by
          rw [hitem, hcb2]; simp [hi0]
        refine cb_desc hNC hi0 houts hno hasc hg hgsrc hgc d' cs[hR + L] hcT hcl2 hcb2' ?_ ?_
          hρC q ?_ ?_
        · rw [hsrc2]
          have := Inner.topIn_slot (d := d' + 1) hρ
          exact this
        · rw [hsrc2]; exact inRegion_slot_iff.mpr ⟨hC, hσ⟩
        · rw [htgt2, ← hmq]
          exact Inner.topIn_slot (d := d' + 1) hq
        · intro hne
          obtain ⟨cs', hcs', m, hm, hgm, hE⟩ := locate hNC houts hg hF (hstrict hne)
          rw [hcs] at hcs'
          obtain rfl := Except.ok.inj hcs'
          obtain ⟨hsrcm, hclC, hcbC, _⟩ := eok_parts hE hgc'
          have hgm' := hgm
          rw [hget2 m hm, c2_target] at hgm'
          rw [hget2 m hm] at hsrcm hclC hcbC
          rcases c2_cases (d := d' + 1 + 2) (S := F.source) (T := F.target) (i := i) (hR := hR)
            (lift := ((L : Nat) : Int)) (C := official pc.row) m
            with ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ | ⟨h1, h1', h2, _, _⟩
          · rw [h2] at hsrcm
            have := (inRegion_slot_iff.mp hsrcm).2
            omega
          · rw [h2] at hclC hcbC
            cases hb2 : decide (hR < m)
            · rw [hb2] at hclC
              have := (hclC (official pc.row) rfl rfl).1
              exact absurd (lt_of_lt_of_le hne this) (lt_irrefl _)
            · rw [hb2] at hcbC
              have := (hcbC (official pc.row) rfl rfl).1
              rw [this] at hne
              exact absurd hne (lt_irrefl _)
          · rw [h2] at hsrcm
            have e1 := (inRegion_slot_iff.mp hsrcm).2
            have hmm : m = hR + L := by omega
            subst hmm
            rw [htgt2]
            exact hgm'

end Tree

end OmegaY.Official.Recon.TSQ.BTL
