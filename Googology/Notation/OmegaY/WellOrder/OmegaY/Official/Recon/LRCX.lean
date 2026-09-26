/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCX.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCFinal

set_option backward.do.legacy false

/-!
# The column `X`: the origins of `λ` and `θ`

For a lower pair of the column `X` (`LowerPair`), the traced lower part of `X` (`lowerT`) gives
the origins of `λ` and `θ`: nodes of the source column `x`. This file proves the facts about
them that do not depend on the column of the leg:

* `origin_facts`: every traced emit comes from a node of the source column, and its emitted
  leg column is the leg column of that node;
* `eok_of_tree`: every item of the tree whose target region holds the row of a traced emit
  emits it, and `EmitOK` holds;
* `consec`: no node of `x` below `τ` has its row strictly between the origin rows of two
  consecutive emits.
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr Reserve

/-- The origin of an emit is a node of the source column with the emitted leg. -/
def OriginOK (ctx : Context) (p : Emit × Origin) : Prop :=
  ∃ c, (p.2.src, c) ∈ realNodes ctx.source ctx.x ∧
    ∀ v, p.1.leftColumn = some v → leftColumn c = .ok v

theorem levelOneT_origin {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, OriginOK ctx p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
    simp [hsrc, pure, Except.pure] at h
    subst h
    simp
  | some q =>
    obtain ⟨srcRef, src⟩ := q
    obtain ⟨hsm, _⟩ := RowLaw.nodeAt_spec hsrc
    simp only [hsrc] at h
    cases hC : it.clean with
    | some C =>
      simp only [hC] at h
      cases hcs : nodeAt ctx.source ctx.x C with
      | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
      | some q' =>
        obtain ⟨csRef, cs⟩ := q'
        obtain ⟨hcm, _⟩ := RowLaw.nodeAt_spec hcs
        simp only [hcs, bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · rename_i v hv
          cases h
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          refine ⟨cs, hcm, ?_⟩
          intro v' hv'
          simp only [Option.some.injEq] at hv'
          subst hv'; exact hv
    | none =>
      simp only [hC] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨src, hsm, fun v hv => by cases hv⟩
      · simp only [bind, Except.bind, pure, Except.pure] at h
        split at h
        · cases h
        · rename_i v hv
          cases h
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          refine ⟨src, hsm, ?_⟩
          intro v' hv'
          simp only [Option.some.injEq] at hv'
          subst hv'; exact hv

theorem runItemT_origin (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx d it = .ok ps →
      ∀ p ∈ ps, OriginOK ctx p
  | 0, _, ps, h => by
    simp [runItemT, pure, Except.pure] at h
    subst h
    simp
  | 1, it, ps, h => levelOneT_origin (by simpa [runItemT] using h)
  | d + 2, it, ps, h => by
    obtain ⟨cs, outs, _, hF, rfl⟩ := runItemT_children h
    intro p hp
    obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hp
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    exact runItemT_origin ctx (d + 1) cs[m] outs[m] (hget m (by omega) hm) p hpL'

theorem lowerT_origin {ctx : Context} {τ : Row} {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems τ).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT) :
    ∀ p ∈ outsT.flatten, OriginOK ctx p := by
  intro p hp
  obtain ⟨L', hL', hpL'⟩ := List.mem_flatten.mp hp
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
  exact runItemT_origin ctx _ _ _ (hall m (by omega) hm) p hpL'

/-- **An item of the tree whose target holds the row of a traced emit emits it.** -/
theorem eok_of_tree {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT)
    {p : Emit × Origin} (hp : p ∈ outsT.flatten) {d : Nat} {A : Item}
    (hA : InTree ctx (official t.row) d A) (hin : inRegion d A.target p.1.row = true) :
    Inner.EmitOK ctx.source ctx.rootColumn d A p := by
  obtain ⟨TA, hTA, _, hback, hinv⟩ := tinTree hctx houts hA
  exact (Inner.runItemT_order ctx d A TA hTA hinv).2 p (hback p hp hin)

/-- **Consecutive emits have consecutive origins.** No node of the source column below `τ`
has its row strictly between the origin rows of two consecutive traced emits. -/
theorem consec {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : LowerPB.BCtx M R root.column (M.size - 1) i ctx) {es : List (Emit × Origin)}
    (hes : lowerT ctx (official t.row) = .ok es) {k : Nat} (hk : k + 1 < es.length)
    {c1 c2 : Cell} (hc1 : cell? M es[k].2.src = some c1)
    (hc2 : cell? M es[k + 1].2.src = some c2)
    {m : Nat} {c : Cell} (hm : 1 ≤ m) (hc : cell? M ⟨ctx.x, m⟩ = some c)
    (hτ : official c.row < official t.row) :
    ¬ (official c1.row < official c.row ∧ official c.row < official c2.row) := by
  rintro ⟨h1, h2⟩
  obtain ⟨q, hq, _, hqsrc⟩ := Proofs.CopyShape.Found.lowerT_covers hrun hTop hi1 hin hB hes hm hc hτ
  have hsrc : ctx.source = M := hB.source
  have hord := List.pairwise_iff_getElem.mp (Inner.lowerT_order hes)
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hq
  have hcq : cell? ctx.source es[p].2.src = some c := by rw [hqsrc, hsrc]; exact hc
  have hc1' : cell? ctx.source es[k].2.src = some c1 := by rw [hsrc]; exact hc1
  have hc2' : cell? ctx.source es[k + 1].2.src = some c2 := by rw [hsrc]; exact hc2
  rcases Nat.lt_or_ge p (k + 1) with hpk | hpk
  · rcases Nat.lt_or_ge p k with hpk' | hpk'
    · have := hord p k hp (by omega) hpk' c c1 hcq hc1'
      rcases this with h | ⟨h, _⟩
      · exact absurd (h.trans h1) (lt_irrefl _)
      · rw [h] at h1; exact lt_irrefl _ h1
    · have hpk'' : p = k := by omega
      subst hpk''
      have := Option.some.inj (hcq.symm.trans hc1')
      subst this
      exact lt_irrefl _ h1
  · rcases Nat.lt_or_ge (k + 1) p with hpk' | hpk'
    · have := hord (k + 1) p hk hp hpk' c2 c hc2' hcq
      rcases this with h | ⟨h, _⟩
      · exact absurd (h.trans h2) (lt_irrefl _)
      · rw [h] at h2; exact lt_irrefl _ h2
    · have hpk'' : p = k + 1 := by omega
      subst hpk''
      have := Option.some.inj (hcq.symm.trans hc2')
      subst this
      exact lt_irrefl _ h2

/-- A traced output is empty exactly when the untraced one is. -/
theorem runItemT_ne_nil {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {d : Nat} (hd : 1 ≤ d) {A : Item}
    (hA : ItemOK ctx (official t.row) d A) {TA : List (Emit × Origin)}
    (h : runItemT ctx d A = .ok TA) (hH : Has ctx d A.source) : TA ≠ [] := by
  have hgood := runItem_good hctx d hd A hA _ (runItem_of_T h)
  intro hn
  apply hgood.2.mp hH
  rw [hn]; rfl

set_option maxHeartbeats 800000 in
/-- **An item with a cut bottom emits a copy of its root row.** -/
theorem cb_clean {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (hblk : ctx.block ≠ 0) :
    ∀ (d : Nat) (K : Item) (TK : List (Emit × Origin)),
      InTree ctx (official t.row) (d + 2) K → K.clean = none → K.cutBottom = true →
      Has ctx (d + 2) K.source → runItemT ctx (d + 2) K = .ok TK →
      Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) K →
      ∀ r ρc, topIn ctx.source ctx.rootColumn (d + 2) K.source = some (r, ρc) →
        ∃ q ∈ TK, Inner.isCleanO q.2 = true ∧
          ∃ cq, cell? ctx.source q.2.src = some cq ∧ official cq.row = official ρc.row := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro K TK hK hcl hcb hH hTK hinv r ρc hρ
    obtain ⟨_, hKOK⟩ := LowerLeftProof.inTree_itemOK hctx hK
    obtain ⟨cs, outs, hcs, hF, rfl⟩ := runItemT_children hTK
    obtain ⟨hlen, hget⟩ := forall₂_getElem hF
    obtain ⟨ax, hax⟩ : ∃ ax, topIn ctx.source ctx.x (d + 2) K.source = some ax := by
      cases h : topIn ctx.source ctx.x (d + 2) K.source with
      | none => exact absurd h (has_iff_topIn.mp hH)
      | some ax => exact ⟨ax, rfl⟩
    have hasc := asc_true_of_kind hcs hax (Or.inr hcb)
    rw [hρ] at hasc
    obtain ⟨n0, F0, σ0, hcsF, _, _, _, hfirst, _⟩ := childSpec hctx hKOK cs hcs
    obtain ⟨hn0, hH0⟩ := hfirst hH
    have h0 : 0 < cs.length := by rw [hcsF]; simpa using hn0
    have hc0 : cs[0] = F0 0 := by simp [hcsF]
    rw [← hc0] at hH0
    obtain ⟨_, hg3⟩ := kids3 hcs hcl hcb hblk hax hρ hasc
    have hinvc := (Inner.childItems_order hcs hinv).1
    obtain ⟨hc0OK, _⟩ := child_itemOK hctx hKOK hcs 0 h0
    have ho0 : 0 < outs.length := by omega
    have hT0 := hget 0 h0 ho0
    have hK0 : InTree ctx (official t.row) (d + 1) cs[0] :=
      LowerLeftProof.inTree_snoc hK hcs (List.getElem_mem h0)
    have hee := e_val' d
    rcases c3_cases (d := d + 2) (S := K.source) (T := K.target)
      (hR := height (d + 2) (official ρc.row))
      (hB := heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) K.target))
      (C := official ρc.row) (0 + height (d + 2) (official ρc.row)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- a gap copy of `ρ`
      have hcs0 : cs[0] = ⟨slot (d + 2) K.source (height (d + 2) (official ρc.row)),
          slot (d + 2) K.target (0 + height (d + 2) (official ρc.row) -
            height (d + 2) (official ρc.row)), some (official ρc.row), 0, true⟩ := by
        rw [hg3 0 h0, h2]
      have hne := runItemT_ne_nil hctx (by omega) hc0OK hT0 hH0
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
      have hE := (Inner.runItemT_order ctx (d + 1) cs[0] outs[0] hT0
        (hinvc _ (List.getElem_mem h0))).2 q hq
      obtain ⟨_, cq, hcq, _, _, h3, _⟩ := hE
      have := h3 (official ρc.row) (by rw [hcs0]) (by rw [hcs0])
      exact ⟨q, List.mem_flatten.mpr ⟨outs[0], List.getElem_mem ho0, hq⟩, this.2, cq, hcq, this.1⟩
    · -- the lifted slot of `ρ` again (only above level 2)
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := by
        rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
        · rw [he1] at h1; omega
        · exact ⟨d - 1, by omega⟩
      have hcs0 : cs[0] = ⟨slot (d' + 1 + 2) K.source (0 + height (d' + 1 + 2) (official ρc.row) -
          heightOf (d' + 1 + 2) (topIn ctx.result ctx.boundary (d' + 1 + 2) K.target)),
          slot (d' + 1 + 2) K.target (0 + height (d' + 1 + 2) (official ρc.row) -
            height (d' + 1 + 2) (official ρc.row)), none, 0,
          decide (0 + height (d' + 1 + 2) (official ρc.row) =
            heightOf (d' + 1 + 2) (topIn ctx.result ctx.boundary (d' + 1 + 2) K.target) +
              height (d' + 1 + 2) (official ρc.row))⟩ := by
        rw [hg3 0 h0, h2]
      have hB0 : heightOf (d' + 1 + 2) (topIn ctx.result ctx.boundary (d' + 1 + 2) K.target) = 0 := by
        have : ((if d' + 1 + 2 = 2 then (1 : Int) else 0)) = 0 := by rw [if_neg (by omega)]
        rw [this] at h1; omega
      have hs0 : cs[0].source = slot (d' + 1 + 2) K.source ((official ρc.row).coeff (d' + 1)) := by
        rw [hcs0, hB0]; simp; rfl
      have hρ0 : topIn ctx.source ctx.rootColumn (d' + 2) cs[0].source = some (r, ρc) := by
        rw [hs0]; exact Inner.topIn_slot hρ
      obtain ⟨q, hq, hq1, hq2⟩ := ih d' (by omega) cs[0] outs[0] hK0 (by rw [hcs0])
        (by rw [hcs0, hB0]; simp) hH0 hT0 (hinvc _ (List.getElem_mem h0)) r ρc hρ0
      exact ⟨q, List.mem_flatten.mpr ⟨outs[0], List.getElem_mem ho0, hq⟩, hq1, hq2⟩

theorem c4_src_hi {d : Nat} {S T : Row} {hR hB off : Nat} {cb : Bool} {C : Row} {j : Nat}
    (h : hR ≤ j ∨ cb = true) : (c4 d S T hR hB off cb C j).source = slot d S hR := by
  unfold c4
  cases cb with
  | true => simp
  | false =>
    rcases h with h | h
    · simp [show ¬ j < hR by omega]
    · cases h

theorem c4_clean_lo {d : Nat} {S T : Row} {hR hB off : Nat} {cb : Bool} {C : Row} {j : Nat}
    (h : (c4 d S T hR hB off cb C j).clean ≠ none) : hR ≤ j ∨ cb = true := by
  unfold c4 at h
  cases cb with
  | true => right; rfl
  | false =>
    left
    by_contra hn
    simp [show j < hR by omega] at h

/-- **A copy of a root row followed by a sibling of a higher source slot is at level one.** -/
theorem sep1_clean {ctx : Context} (hblk : ctx.block ≠ 0) {d : Nat} {P : Item} {cs : List Item}
    (hcs : childItems ctx (d + 2) P = .ok cs) {ax : Ref × Cell}
    (hax : topIn ctx.source ctx.x (d + 2) P.source = some ax) {j : Nat} (hj : j + 1 < cs.length)
    {b b' : Nat} (hb : (cs[j]'(by omega)).source = slot (d + 2) P.source b)
    (hb' : cs[j + 1].source = slot (d + 2) P.source b') (hbb : b < b')
    (hcl : (cs[j]'(by omega)).clean ≠ none) : d = 0 := by
  have hj0 : j < cs.length := by omega
  have hee := e_val' d
  obtain ⟨bb, hbb'⟩ := childItems_asc hcs hax
  cases bb with
  | false =>
    obtain ⟨_, _, _, hg⟩ := kids1 hcs hax hbb'
    rw [hg j hj0] at hcl
    exact absurd rfl hcl
  | true =>
    cases hρ : topIn ctx.source ctx.rootColumn (d + 2) P.source with
    | none => rw [hρ] at hbb'; cases hbb'
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hbb'
      cases hPcl : P.clean with
      | none =>
        cases hPcb : P.cutBottom with
        | false =>
          obtain ⟨_, hg⟩ := kids2 hcs hPcl hPcb hax hρ hbb'
          rw [hg j hj0] at hcl hb
          rw [hg (j + 1) hj] at hb'
          rcases c2_cases (d := d + 2) (S := P.source) (T := P.target) (i := ctx.block)
            (hR := height (d + 2) (official cl.row))
            (lift := (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) P.source) :
              Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) * (ctx.block : Int))
            (C := official cl.row) j with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · rw [h2] at hcl; exact absurd rfl hcl
          · rw [h3] at hb
            have e1 := LowerLeftProof.slot_inj hb
            rcases c2_cases (d := d + 2) (S := P.source) (T := P.target) (i := ctx.block)
              (hR := height (d + 2) (official cl.row))
              (lift := (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) P.source) :
                Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) *
                  (ctx.block : Int))
              (C := official cl.row) (j + 1) with ⟨g1, _⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
            · omega
            · rw [g3] at hb'
              have e2 := LowerLeftProof.slot_inj hb'
              omega
            · rw [g3.1] at hb'
              have e2 := LowerLeftProof.slot_inj hb'
              rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
              · exact he2
              · rw [he1] at h2 g2; omega
          · rw [h3.2.1] at hcl; exact absurd rfl hcl
        | true =>
          obtain ⟨_, hg⟩ := kids3 hcs hPcl hPcb hblk hax hρ hbb'
          rw [hg j hj0] at hcl hb
          rw [hg (j + 1) hj] at hb'
          rcases c3_cases (d := d + 2) (S := P.source) (T := P.target)
            (hR := height (d + 2) (official cl.row))
            (hB := heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) P.target))
            (C := official cl.row) (j + height (d + 2) (official cl.row)) with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h2] at hb
            have e1 := LowerLeftProof.slot_inj hb
            rcases c3_cases (d := d + 2) (S := P.source) (T := P.target)
              (hR := height (d + 2) (official cl.row))
              (hB := heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) P.target))
              (C := official cl.row) (j + 1 + height (d + 2) (official cl.row)) with
              ⟨g1, g2⟩ | ⟨g1, g2⟩
            · rw [g2] at hb'
              have e2 := LowerLeftProof.slot_inj hb'
              omega
            · rw [g2] at hb'
              have e2 := LowerLeftProof.slot_inj hb'
              rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
              · exact he2
              · rw [he1] at h1 g1; omega
          · rw [h2] at hcl; exact absurd rfl hcl
      | some C =>
        obtain ⟨_, _, _, _, _, _, _, hg⟩ := kids4 hcs hPcl hblk hax hρ hbb'
        rw [hg j hj0] at hcl hb
        rw [hg (j + 1) hj] at hb'
        have h1 := c4_clean_lo hcl
        rw [c4_src_hi h1] at hb
        rw [c4_src_hi (by rcases h1 with h1 | h1 <;> [exact Or.inl (by omega); exact Or.inr h1])]
          at hb'
        have e1 := LowerLeftProof.slot_inj hb
        have e2 := LowerLeftProof.slot_inj hb'
        omega

/-- **A copy of a root row followed by a sibling of a higher source slot has offset `0`.** -/
theorem sep1_clean_off {ctx : Context} (hblk : ctx.block ≠ 0) {d : Nat} {P : Item}
    {cs : List Item} (hcs : childItems ctx (d + 2) P = .ok cs) {ax : Ref × Cell}
    (hax : topIn ctx.source ctx.x (d + 2) P.source = some ax) {j : Nat} (hj : j + 1 < cs.length)
    {b b' : Nat} (hb : (cs[j]'(by omega)).source = slot (d + 2) P.source b)
    (hb' : cs[j + 1].source = slot (d + 2) P.source b') (hbb : b < b')
    (hcl : (cs[j]'(by omega)).clean ≠ none) : (cs[j]'(by omega)).offset = 0 := by
  have hj0 : j < cs.length := by omega
  obtain ⟨bb, hbb'⟩ := childItems_asc hcs hax
  cases bb with
  | false =>
    obtain ⟨_, _, _, hg⟩ := kids1 hcs hax hbb'
    rw [hg j hj0] at hcl
    exact absurd rfl hcl
  | true =>
    cases hρ : topIn ctx.source ctx.rootColumn (d + 2) P.source with
    | none => rw [hρ] at hbb'; cases hbb'
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hbb'
      cases hPcl : P.clean with
      | none =>
        cases hPcb : P.cutBottom with
        | false =>
          obtain ⟨_, hg⟩ := kids2 hcs hPcl hPcb hax hρ hbb'
          rw [hg j hj0] at hcl ⊢
          unfold c2 at hcl ⊢
          split_ifs at hcl ⊢ <;> first | rfl | simp at hcl
        | true =>
          obtain ⟨_, hg⟩ := kids3 hcs hPcl hPcb hblk hax hρ hbb'
          rw [hg j hj0] at hcl ⊢
          unfold c3 at hcl ⊢
          split_ifs at hcl ⊢ <;> first | rfl | simp at hcl
      | some C =>
        obtain ⟨_, _, _, _, _, _, _, hg⟩ := kids4 hcs hPcl hblk hax hρ hbb'
        rw [hg j hj0] at hcl hb
        rw [hg (j + 1) hj] at hb'
        have h1 := c4_clean_lo hcl
        rw [c4_src_hi h1] at hb
        rw [c4_src_hi (by rcases h1 with h1 | h1 <;> [exact Or.inl (by omega); exact Or.inr h1])]
          at hb'
        have e1 := LowerLeftProof.slot_inj hb
        have e2 := LowerLeftProof.slot_inj hb'
        omega

/-- The adjacent case: the origin `a` of `θ` follows the origin `a_λ` of `λ` in the source
column, in the next slot of level `e + 1`. -/
def Adj (M : Mountain) (x : Nat) (τ : Row) (e : Nat) (J : Item) (a : Row) : Prop :=
  ∃ aL : Row, (∃ q ∈ realNodes M x, official q.2.row = aL) ∧ inRegion (e + 1) J.source aL = true ∧
    (∀ q, e < q → a.coeff q = aL.coeff q) ∧ aL.coeff e < a.coeff e ∧
    (1 ≤ e → J.clean = none) ∧ (J.clean ≠ none → J.offset = 0) ∧
    (∀ q ∈ realNodes M x, official q.2.row < τ → ¬ (aL < official q.2.row ∧ official q.2.row < a))

theorem bump_coeff_e (lam : Row) (e : Nat) : (Row.bump lam e).coeff e = lam.coeff e + 1 :=
  bump_coeff_at lam e

theorem bump_coeff_hi {lam : Row} {e q : Nat} (h : e < q) : (Row.bump lam e).coeff q = lam.coeff q :=
  bump_coeff_high h

/-- **The item of `θ` below the parent of `J`, and the classification.** -/
theorem classify_parent {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) (hblk : ctx.block ≠ 0) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT)
    {k : Nat} (hk : k + 1 < outsT.flatten.length) {lam : Row} {e : Nat}
    (hlrow : (outsT.flatten[k]'(by omega)).1.row = lam)
    (htrow : (outsT.flatten[k + 1]).1.row = Row.bump lam e)
    {cL cθ : Cell} (hcL : cell? ctx.source (outsT.flatten[k]'(by omega)).2.src = some cL)
    (hcθ : cell? ctx.source (outsT.flatten[k + 1]).2.src = some cθ)
    {J : Item} (hJ : InTree ctx (official t.row) (e + 1) J)
    (hlamJ : inRegion (e + 1) J.target lam = true)
    {P : Item} (hPt : InTree ctx (official t.row) (e + 2) P) {csP : List Item}
    (hcsP : childItems ctx (e + 2) P = .ok csP) (hJm : J ∈ csP)
    (hcons : ∀ q ∈ realNodes ctx.source ctx.x, official q.2.row < official t.row →
      ¬ (official cL.row < official q.2.row ∧ official q.2.row < official cθ.row))
    (hsort : ∀ p q (hp : p < outsT.flatten.length) (hq : q < outsT.flatten.length), p < q →
      (outsT.flatten[p]).1.row < (outsT.flatten[q]).1.row) :
    J.clean = some (official cθ.row) ∨
      Adj ctx.source ctx.x (official t.row) e J (official cθ.row) := by
  set es := outsT.flatten with hes
  have hk0 : k < es.length := by omega
  obtain ⟨_, hPOK⟩ := LowerLeftProof.inTree_itemOK hctx hPt
  obtain ⟨jJ, hjJ, rfl⟩ := List.getElem_of_mem hJm
  obtain ⟨_, hJtgt⟩ := child_itemOK hctx hPOK hcsP jJ hjJ
  have hlamc : lam.coeff e = jJ := by
    rw [hJtgt] at hlamJ; exact coeff_of_slot hlamJ
  have hlamP : inRegion (e + 2) P.target lam = true := by
    rw [hJtgt] at hlamJ; exact region_of_slot hlamJ
  have hθP : inRegion (e + 2) P.target (Row.bump lam e) = true := by
    rw [inRegion_iff'] at hlamP ⊢
    intro q hq
    rw [bump_coeff_hi (by omega), hlamP q hq]
  -- the traced output of `P`
  obtain ⟨TP, hTP, hsubP, hbackP, hinvP⟩ := tinTree hctx houts hPt
  have hθmem : es[k + 1] ∈ es := List.getElem_mem hk
  have hθTP := hbackP _ hθmem (by rw [htrow]; exact hθP)
  obtain ⟨cs', outs, hcs', hF, rfl⟩ := runItemT_children hTP
  rw [hcsP] at hcs'
  obtain rfl := Except.ok.inj hcs'
  obtain ⟨hlen, hget⟩ := forall₂_getElem hF
  obtain ⟨L', hL', hθL'⟩ := List.mem_flatten.mp hθTP
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
  have hm' : m < csP.length := by omega
  obtain ⟨hmOK, hmtgt⟩ := child_itemOK hctx hPOK hcsP m hm'
  have hθm := runItemT_region hctx (by omega) hmOK (hget m hm' hm) _ hθL'
  rw [hmtgt, htrow] at hθm
  have hmj : m = jJ + 1 := by
    have := coeff_of_slot hθm
    rw [bump_coeff_e] at this
    omega
  subst hmj
  have hinvc := (Inner.childItems_order hcsP hinvP).1
  have hEθ := (Inner.runItemT_order ctx (e + 1) csP[jJ + 1] outs[jJ + 1] (hget _ hm' hm)
    (hinvc _ (List.getElem_mem hm'))).2 _ hθL'
  have hEL := eok_of_tree hctx houts (List.getElem_mem hk0) hJ (by rw [hlrow]; exact hlamJ)
  obtain ⟨haReg, _, hcutθ, hcbθ⟩ := eok_parts hEθ hcθ
  obtain ⟨hlReg, _, _, _⟩ := eok_parts hEL hcL
  have hsep := List.pairwise_iff_getElem.mp (Inner.childItems_order hcsP hinvP).2.1
    jJ (jJ + 1) hjJ hm' (by omega)
  rcases hsep with ⟨b, b', hb, hb', hbb⟩ | ⟨C, hJC, hJ'⟩
  · -- the adjacent case
    right
    obtain ⟨ax, hax⟩ : ∃ ax, topIn ctx.source ctx.x (e + 2) P.source = some ax := by
      cases h : topIn ctx.source ctx.x (e + 2) P.source with
      | none =>
        have := childItems_none hcsP h
        rw [this] at hjJ; simp at hjJ
      | some ax => exact ⟨ax, rfl⟩
    refine ⟨official cL.row, ?_, hlReg, ?_, ?_, ?_, fun hcl => sep1_clean_off hblk hcsP hax hm' hb hb'
      hbb hcl, hcons⟩
    · obtain ⟨c, hc, _⟩ := lowerT_origin houts _ (List.getElem_mem hk0)
      obtain ⟨_, _, hcc⟩ := Classification.mem_realNodes hc
      exact ⟨_, hc, by rw [Option.some.inj (hcc.symm.trans hcL)]⟩
    · intro q hq
      rw [hb'] at haReg; rw [hb] at hlReg
      have h1 := region_of_slot haReg
      have h2 := region_of_slot hlReg
      rw [inRegion_iff'.mp h1 q (by omega), inRegion_iff'.mp h2 q (by omega)]
    · rw [hb'] at haReg; rw [hb] at hlReg
      rw [coeff_of_slot haReg, coeff_of_slot hlReg]; exact hbb
    · intro he
      by_contra hcl
      have := sep1_clean hblk hcsP hax hm' hb hb' hbb hcl
      omega
  · -- `J` copies the root row `C`
    left
    rw [hJC]
    rcases hJ' with ⟨hJ'C, hJ'cb⟩ | ⟨hJ'n, hJ'cb, h1e, r, ρc, hρ, hρC⟩
    · rw [(hcutθ C hJ'C hJ'cb).1]
    · -- a cut bottom: its first emit is a copy of `C`
      obtain ⟨d', rfl⟩ : ∃ d', e = d' + 1 := ⟨e - 1, by omega⟩
      have hJ't : InTree ctx (official t.row) (d' + 2) csP[jJ + 1] :=
        LowerLeftProof.inTree_snoc hPt hcsP (List.getElem_mem hm')
      have hH : Has ctx (d' + 2) csP[jJ + 1].source := by
        obtain ⟨c, hc, _⟩ := lowerT_origin houts _ hθmem
        obtain ⟨_, _, hcc⟩ := Classification.mem_realNodes hc
        have hceq : c = cθ := Option.some.inj (hcc.symm.trans hcθ)
        subst hceq
        exact ⟨_, hc, haReg⟩
      obtain ⟨q, hq, hqcl, cq, hcq, hcqr⟩ := cb_clean hctx hblk d' csP[jJ + 1] outs[jJ + 1] hJ't
        hJ'n hJ'cb hH (hget _ hm' hm) (hinvc _ (List.getElem_mem hm')) r ρc hρ
      rw [hρC] at hcqr
      have hqes : q ∈ es := hsubP q (List.mem_flatten.mpr ⟨_, hL', hq⟩)
      obtain ⟨pq, hpq, rfl⟩ := List.getElem_of_mem hqes
      -- `θ` is the base of the target of its item, so `q` is not below it
      have hqreg := runItemT_region hctx (by omega) hmOK (hget _ hm' hm) _ hq
      rw [hmtgt] at hqreg
      have hθbase : Row.bump lam (d' + 1) = slot (d' + 1 + 2) P.target (jJ + 1) := by
        have h1 := bump_of_inRegion hlamJ
        simp only [show d' + 1 + 1 - 1 = d' + 1 by omega] at h1
        rw [h1, hJtgt, bump_slot]
      have hθle : Row.bump lam (d' + 1) ≤ es[pq].1.row := by
        rw [hθbase]
        exact base_le_of_inRegion (by simpa using slot_zeroBelow (d' + 1) P.target (jJ + 1)) hqreg
      obtain ⟨_, _, _, hcbt⟩ := eok_parts hEθ hcθ
      have hCa := (hcbt hJ'n hJ'cb (by omega) r ρc hρ).1
      rw [hρC] at hCa
      rcases Nat.lt_trichotomy pq (k + 1) with hlt | heq | hgt
      · have := hsort pq (k + 1) hpq hk hlt
        rw [htrow] at this
        exact absurd (lt_of_lt_of_le this hθle) (lt_irrefl _)
      · subst heq
        rw [Option.some.inj (hcq.symm.trans hcθ)] at hcqr
        rw [hcqr]
      · have hord := List.pairwise_iff_getElem.mp (Inner.lowerT_order (ctx := ctx)
          (τ := official t.row) (lower := outsT.flatten) (by unfold lowerT; simp only [houts, bind, Except.bind, pure,
            Except.pure]))
        have := hord (k + 1) pq hk hpq hgt cθ cq hcθ hcq
        rcases this with h | ⟨h, _⟩
        · rw [hcqr] at h; exact absurd (lt_of_lt_of_le h hCa) (lt_irrefl _)
        · rw [h, ← hcqr]

/-- **The classification when `J` is a first item.** -/
theorem classify_first {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {outsT : List (List (Emit × Origin))}
    (houts : (lowerItems (official t.row)).mapM (fun p => runItemT ctx p.1 p.2) = .ok outsT)
    {k : Nat} (hk : k + 1 < outsT.flatten.length) {lam : Row} {e : Nat}
    (hlrow : (outsT.flatten[k]'(by omega)).1.row = lam)
    (htrow : (outsT.flatten[k + 1]).1.row = Row.bump lam e)
    {cL cθ : Cell} (hcL : cell? ctx.source (outsT.flatten[k]'(by omega)).2.src = some cL)
    (hcθ : cell? ctx.source (outsT.flatten[k + 1]).2.src = some cθ)
    {J : Item} (hJF : (e + 1, J) ∈ lowerItems (official t.row))
    (hlamJ : inRegion (e + 1) J.target lam = true)
    (hcons : ∀ q ∈ realNodes ctx.source ctx.x, official q.2.row < official t.row →
      ¬ (official cL.row < official q.2.row ∧ official q.2.row < official cθ.row)) :
    Adj ctx.source ctx.x (official t.row) e J (official cθ.row) := by
  set es := outsT.flatten with hes
  have hk0 : k < es.length := by omega
  have hJt : InTree ctx (official t.row) (e + 1) J := ⟨(e + 1, J), hJF, .refl _ _⟩
  obtain ⟨_, hJst, _, _⟩ := lower_itemOK (ctx := ctx) hJF
  have hEL := eok_of_tree hctx houts (List.getElem_mem hk0) hJt (by rw [hlrow]; exact hlamJ)
  obtain ⟨hlReg, _, _, _⟩ := eok_parts hEL hcL
  -- the first item of `θ`
  have hθmem : es[k + 1] ∈ es := List.getElem_mem hk
  obtain ⟨L', hL', hθL'⟩ := List.mem_flatten.mp hθmem
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
  obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
  have hm' : m < (lowerItems (official t.row)).length := by omega
  obtain ⟨hmOK, hmst, hm1, _⟩ := lower_itemOK (ctx := ctx) (List.getElem_mem hm')
  have hθm := runItemT_region hctx hm1 hmOK (hall m hm' hm) _ hθL'
  rw [htrow] at hθm
  have hmt : InTree ctx (official t.row) (lowerItems (official t.row))[m].1
      (lowerItems (official t.row))[m].2 := ⟨_, List.getElem_mem hm', .refl _ _⟩
  have hEθ := eok_of_tree hctx houts hθmem hmt (by rw [htrow]; exact hθm)
  obtain ⟨haReg, _, _, _⟩ := eok_parts hEθ hcθ
  rw [hmst] at haReg
  obtain ⟨fJ, hfJ, hfJeq⟩ := List.getElem_of_mem hJF
  have hlev : (lowerItems (official t.row))[m].1 ≤ e + 1 := by
    by_contra hn
    have hlm : inRegion (lowerItems (official t.row))[m].1 (lowerItems (official t.row))[m].2.target
        lam = true := by
      rw [inRegion_iff'] at hθm ⊢
      intro q hq
      rw [← hθm q hq, bump_coeff_hi (by omega)]
    have hlJ : inRegion (lowerItems (official t.row))[fJ].1
        (lowerItems (official t.row))[fJ].2.target lam = true := by rw [hfJeq]; exact hlamJ
    have hfm := first_unique ctx hfJ hm' hlJ hlm
    subst hfm
    have hθJ : inRegion (e + 1) J.target (Row.bump lam e) = true := by
      have h := hθm
      simp only [hfJeq] at h
      exact h
    have h1 := inRegion_iff'.mp hθJ e (by omega)
    have h2 := inRegion_iff'.mp hlamJ e (by omega)
    rw [bump_coeff_e] at h1
    omega
  have hagree : ∀ q, e ≤ q → (official cθ.row).coeff q = (Row.bump lam e).coeff q := by
    intro q hq
    rw [inRegion_iff'.mp haReg q (by omega), inRegion_iff'.mp hθm q (by omega)]
  have hagreeL : ∀ q, e ≤ q → (official cL.row).coeff q = lam.coeff q := by
    intro q hq
    rw [hJst] at hlReg
    rw [inRegion_iff'.mp hlReg q (by omega), inRegion_iff'.mp hlamJ q (by omega)]
  have hJn : J.clean = none := by
    obtain ⟨kk, jj, _, _, hkj⟩ := mem_lowerItems hJF
    simp only [Prod.mk.injEq] at hkj
    rw [hkj.2]
  refine ⟨official cL.row, ?_, hlReg, ?_, ?_, ?_, fun h => absurd hJn h, hcons⟩
  · obtain ⟨c, hc, _⟩ := lowerT_origin houts _ (List.getElem_mem hk0)
    obtain ⟨_, _, hcc⟩ := Classification.mem_realNodes hc
    exact ⟨_, hc, by rw [Option.some.inj (hcc.symm.trans hcL)]⟩
  · intro q hq
    rw [hagree q hq.le, hagreeL q hq.le, bump_coeff_hi hq]
  · rw [hagree e le_rfl, hagreeL e le_rfl, bump_coeff_e]; omega
  · intro _
    obtain ⟨kk, jj, _, _, hkj⟩ := mem_lowerItems hJF
    simp only [Prod.mk.injEq] at hkj
    rw [hkj.2]

/-- **The column `X` of a lower pair.** The traced emit of `θ`, its origin node `(x, a)` with the
leg column `l`, and the classification: `J` copies `a` (`F1`), or `a` follows the origin of
`λ` in the next slot (`Adj`). -/
theorem xside {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    {lam θ : Row} {l e : Nat} {J : Item} (hP : LowerPair s n R M t root i x lam θ l e J) :
    ∃ outsT, (lowerItems (official t.row)).mapM
        (fun p => runItemT (colCtx M R root i x) p.1 p.2) = .ok outsT ∧
      ∃ θp ∈ outsT.flatten, θp.1.row = θ ∧ ∃ cθ, (θp.2.src, cθ) ∈ realNodes M x ∧
        cell? M θp.2.src = some cθ ∧ leftColumn cθ = .ok l ∧ official cθ.row < official t.row ∧
        (J.clean = some (official cθ.row) ∨ Adj M x (official t.row) e J (official cθ.row)) := by
  have hNC := hP.nc
  have hctx := hNC.runCtx
  have hBc := colCtx_bctx hNC
  have hblk : (colCtx M R root i x).block ≠ 0 := by
    show i ≠ 0; have := hP.pos; omega
  obtain ⟨vs, us, col, hvs, _, hasm, k, hk, hkL, hlam, hθ, hleft, ⟨LJ, hLJ, hlamJ⟩, hmax⟩ := hP.run
  obtain ⟨outsT, houts, hmap, hlowerT⟩ := lowerT_of_run hvs
  set es := outsT.flatten with hes
  have hesm : es.map Prod.fst = vs.flatten := flatten_map_fst hmap
  have hlen : es.length = vs.flatten.length := by rw [← hesm, List.length_map]
  have hk1 : k + 1 < es.length := by omega
  have hk0 : k < es.length := by omega
  have hget : ∀ q (hq : q < es.length), (es[q]).1 = (vs.flatten ++ us)[q]'(by
      rw [List.length_append]; omega) := by
    intro q hq
    rw [List.getElem_append_left (by omega)]
    have := congrArg (fun L => L[q]?) hesm
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem hq, List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hsorted := assemble_sorted hasm
  have hsort : ∀ p q (hp : p < es.length) (hq : q < es.length), p < q →
      (es[p]).1.row < (es[q]).1.row := by
    intro p q hp hq hpq
    rw [hget p hp, hget q hq]
    have := List.pairwise_iff_getElem.mp hsorted p q (by rw [List.length_map, List.length_append]; omega) (by rw [List.length_map, List.length_append]; omega) hpq
    rw [List.getElem_map, List.getElem_map] at this
    exact this
  have hlrow : (es[k]).1.row = lam := by rw [hget k hk0]; exact hlam
  have htrow : (es[k + 1]).1.row = Row.bump lam e := by
    rw [hget (k + 1) hk1, hθ]; exact hP.bump
  have hleft' : (es[k + 1]).1.leftColumn = some l := by rw [hget (k + 1) hk1]; exact hleft
  obtain ⟨cθ, hcθm, hcθl⟩ := lowerT_origin houts _ (List.getElem_mem hk1)
  obtain ⟨cL, hcLm, _⟩ := lowerT_origin houts _ (List.getElem_mem hk0)
  obtain ⟨_, _, hcθ⟩ := Classification.mem_realNodes hcθm
  obtain ⟨_, _, hcL⟩ := Classification.mem_realNodes hcLm
  have hlT : lowerT (colCtx M R root i x) (official t.row) = .ok es := hlowerT
  have hin : i ≤ n := by have := hNC.block; omega
  have hcons : ∀ q ∈ realNodes (colCtx M R root i x).source (colCtx M R root i x).x,
      official q.2.row < official t.row →
      ¬ (official cL.row < official q.2.row ∧ official q.2.row < official cθ.row) := by
    intro q hq hqτ
    obtain ⟨hqc, hq1, hqcell⟩ := Classification.mem_realNodes hq
    have hqcell' : cell? M ⟨(colCtx M R root i x).x, q.1.index⟩ = some q.2 := by
      rw [← hqc]; exact hqcell
    exact consec hNC.run hNC.top hP.pos hin hBc hlT hk1 hcL hcθ hq1 hqcell' hqτ
  refine ⟨outsT, houts, es[k + 1], List.getElem_mem hk1, by rw [htrow, hP.bump],
    cθ, hcθm, hcθ, hcθl l hleft', ?_, ?_⟩
  · -- the origin of `θ` is below `τ`
    obtain ⟨L', hL', hθL'⟩ := List.mem_flatten.mp (List.getElem_mem hk1)
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hL'
    obtain ⟨hlen2, hall⟩ := mapM_except_spec _ _ _ houts
    have hm' : m < (lowerItems (official t.row)).length := by omega
    obtain ⟨hmOK, _, hm1, _⟩ := lower_itemOK (ctx := colCtx M R root i x) (List.getElem_mem hm')
    have hθm := runItemT_region hctx hm1 hmOK (hall m hm' hm) _ hθL'
    have hmt : InTree (colCtx M R root i x) (official t.row) (lowerItems (official t.row))[m].1
        (lowerItems (official t.row))[m].2 := ⟨_, List.getElem_mem hm', .refl _ _⟩
    have hEθ := eok_of_tree hctx houts (List.getElem_mem hk1) hmt hθm
    obtain ⟨haReg, _, _, _⟩ := eok_parts hEθ hcθ
    exact hmOK.below _ haReg
  · obtain ⟨F, hF, hD⟩ := hP.tree
    have hlev := desc_level_le hD
    rcases Nat.eq_or_lt_of_le hlev with heq | hlt
    · -- `J` is a first item
      right
      obtain ⟨F1, F2⟩ := F
      simp only at heq hD
      subst heq
      have hFJ := desc_eq hD
      subst hFJ
      exact classify_first hctx houts hk1 hlrow htrow hcL hcθ hF hP.region hcons
    · obtain ⟨Pp, csP, hDP, hcsP, hJm⟩ := desc_parent hD hlt
      exact classify_parent hctx hblk houts hk1 hlrow htrow hcL hcθ hP.tree hP.region
        ⟨F, hF, hDP⟩ hcsP hJm hcons hsort

end OmegaY.Official.Recon.LRC
