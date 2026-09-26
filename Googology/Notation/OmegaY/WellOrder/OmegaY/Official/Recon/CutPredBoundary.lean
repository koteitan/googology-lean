/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredBoundary.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredGap
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBase

set_option backward.do.legacy false

/-!
# `BoundaryRootRows`: the root rows reach every boundary column

For a block `i ≥ 1`, the boundary column `B = c_r + w·i` of the output is the copy of the last
column `x₀` in block `i - 1`. Every row `a < τ` of the root column `c_r` is emitted there
(`boundaryRootRowsHolds`), by induction on `i`.

## Proof

The row `a` lies in one first region of the rule (`lowerItems_cover`). Follow the items whose
region contains `a` (`emits_row`); they are plain items, or clean items copying the root row
`C = row ρ` with `a ≤ C`, and their target region equals their source region. In a region `S`
of level `d + 2`, with `h_a` the height of `a`:

* `x₀` has a node at `a` (`Top.root_rows`), so it has a top in `S` of height `≥ h_a`;
* a plain item that does not ascend (case 1) has the child `h_a`, again plain;
* a plain item that ascends (case 2): `h_a ≤ h_ρ ≤ h_κ`, so the lift is `≥ 0`. For
  `h_a < h_ρ` the child is plain. For `h_a = h_ρ` the child is the clean copy of `ρ`: at level
  `2` always, above only if the lift is positive; the lift is positive for `i - 1 ≥ 1` by fact
  MD (`liftPosHolds`), and for `i - 1 = 0` the child is plain;
* a clean item (case 4) has the children up to `h_B + g ≥ h_ρ ≥ h_a` (`CleanGap` of block
  `i - 1`, from the induction hypothesis) or up to `h_κ` (block `0`);
* at level 1 the item copies the node of `x₀` at `a`.
-/

namespace OmegaY.Official.Recon.CutPredMD

open Canonical Official Classification

theorem forall₂_left {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ x ∈ xs, ∃ y ∈ ys, P x y
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hxy⟩ := forall₂_left rest x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem childItems_case1_list {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d it.source = some a)
    (hasc : ascends ctx (topIn ctx.source ctx.rootColumn d it.source) = .ok false) :
    cs = (List.range (height d (official a.2.row) + 1)).map
      (fun j => (⟨slot d it.source j, slot d it.target j, none, 0, false⟩ : Item)) := by
  unfold childItems at h
  simp only [hx, hasc, bind, Except.bind, pure, Except.pure] at h
  simp only [Bool.false_eq_true, not_false_eq_true, if_true] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · exact (Except.ok.inj h).symm

theorem inRegion_slot_own {d : Nat} {S a : Row} (h : inRegion (d + 2) S a = true) :
    inRegion (d + 1) (slot (d + 2) S (a.coeff d)) a = true := by
  rw [Classification.inRegion_iff] at h ⊢
  intro k hk
  by_cases hkd : k = d
  · subst hkd
    rw [coeff_slot_at']
  · rw [coeff_slot_high (by omega) (by omega)]
    exact h k (by omega)

/-- The first regions cover every row below `τ`. -/
theorem lowerItems_cover {τ a : Row} (h : a < τ) :
    ∃ k j, (k + 1, (⟨slot (k + 2) τ j, slot (k + 2) τ j, none, 0, false⟩ : Item)) ∈
      lowerItems τ ∧ inRegion (k + 1) (slot (k + 2) τ j) a = true := by
  obtain ⟨i, hup, hlt⟩ := Row.lt_iff.mp h
  have hil : i < len τ := by
    by_contra hn
    rw [coeff_of_le_len (a := τ) (k := i) (by omega)] at hlt
    omega
  refine ⟨i, a.coeff i, ?_, ?_⟩
  · simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map]
    exact ⟨i, hil, a.coeff i, hlt, rfl⟩
  · rw [Classification.inRegion_iff]
    intro k hk
    by_cases hki : k = i
    · subst hki
      rw [coeff_slot_at']
    · rw [coeff_slot_high (by omega) (by omega)]
      exact hup k (by omega)

/-- The copy of the last column. -/
structure LastCtx (s : List Nat) (M : Mountain) (t : Cell) (root : Ref) (ctx : Context) :
    Prop where
  top : Recon.Top s M t root
  src : ctx.source = M
  rc : ctx.rootColumn = root.column
  xx : ctx.x = M.size - 1
  lc : ctx.lastColumn = M.size - 1

theorem last_root_row {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Recon.Top s M t root) {p : Ref × Cell} (hp : p ∈ realNodes M root.column)
    (hlt : official p.2.row < official t.row) :
    ∃ v ∈ realNodes M (M.size - 1), official v.2.row = official p.2.row := by
  obtain ⟨v, hv, hvr⟩ := h.root_rows hp (row_lt_of_official h.row_one_le hlt)
  exact ⟨v, hv, by rw [hvr]⟩

theorem agree_coeff {d : Nat} {S x y : Row} (hx : inRegion (d + 2) S x = true)
    (hy : inRegion (d + 2) S y = true) (h : x ≤ y) : x.coeff d ≤ y.coeff d :=
  coeff_le_of_le_agree h (fun k hk => by
    rw [(Classification.inRegion_iff _ _ _).mp hx k (by omega),
      (Classification.inRegion_iff _ _ _).mp hy k (by omega)])

/-- **Every row `a < τ` of the root column is emitted by the items whose region contains it.** -/
theorem emits_row {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} {ctx : Context}
    (hL : LastCtx s M t root ctx)
    (HLP : LiftPos ctx (official t.row)) (HCG : ctx.block ≠ 0 → CleanGap ctx (official t.row))
    {a : Row} {p : Ref × Cell} (hp : p ∈ realNodes M root.column) (hpa : official p.2.row = a)
    (haτ : a < official t.row) :
    ∀ (L : Nat) (it : Item) (out : List EO), Reached ctx (official t.row) L it →
      runItemT ctx L it = .ok out → it.cutBottom = false → SameRegion L it →
      inRegion L it.source a = true →
      (it.clean = none ∨ ∃ C, it.clean = some C ∧ RootTop ctx L it C ∧ a ≤ C) →
      ∃ e ∈ out, e.1.row = a
  | 0, _, _, hr, _, _, _, _, _ => absurd hr.pos (by omega)
  | 1, it, out, _, hrun, _, hsame, hin, _ => by
    obtain ⟨v, hv, hva⟩ := last_root_row hL.top hp (hpa ▸ haτ)
    rw [hpa] at hva
    have hsrc : it.source = a := by
      apply row_ext
      intro k
      exact ((Classification.inRegion_iff 1 it.source a).mp hin k (by omega)).symm
    have htgt : it.target = a := by
      rw [← hsrc]
      apply row_ext
      intro k
      exact (hsame k (by omega)).symm
    obtain ⟨q, hq⟩ := RowLaw.nodeAt_of_mem hv
    rw [hva, ← hsrc, ← hL.xx, ← hL.src] at hq
    obtain ⟨srcRef, src⟩ := q
    have h1 : levelOneT ctx it = .ok out := by simpa [runItemT] using hrun
    unfold levelOneT at h1
    rw [hq] at h1
    simp only at h1
    cases hC : it.clean with
    | some C =>
      rw [hC] at h1
      simp only at h1
      cases hcs : nodeAt ctx.source ctx.x C with
      | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h1
      | some q' =>
        obtain ⟨csRef, cs⟩ := q'
        cases hlc : leftColumn cs with
        | error err => simp [hcs, hlc, bind, Except.bind] at h1
        | ok lc =>
          simp only [hcs, hlc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h1
          subst h1
          exact ⟨_, List.mem_singleton_self _, htgt⟩
    | none =>
      rw [hC] at h1
      simp only at h1
      split at h1
      · simp only [pure, Except.pure, Except.ok.injEq] at h1
        subst h1
        exact ⟨_, List.mem_singleton_self _, htgt⟩
      · cases hl : leftColumn src with
        | error _ => simp [hl, bind, Except.bind] at h1
        | ok lc =>
          simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h1
          subst h1
          exact ⟨_, List.mem_singleton_self _, htgt⟩
  | d + 2, it, out, hr, hrun, hcb, hsame, hin, hcl => by
    have hb := hL.top.build
    obtain ⟨cs, outs, hch, hF, rfl⟩ := runItemT_succ_succ hrun
    -- the children that contain `a`
    have key : ∀ c ∈ cs, c.cutBottom = false → SameRegion (d + 1) c →
        inRegion (d + 1) c.source a = true →
        (c.clean = none ∨ ∃ C, c.clean = some C ∧ RootTop ctx (d + 1) c C ∧ a ≤ C) →
        ∃ e ∈ outs.flatten, e.1.row = a := by
      intro c hc hcb' hsame' hin' hcl'
      obtain ⟨o, ho, hco⟩ := forall₂_left hF c hc
      obtain ⟨e, he, her⟩ := emits_row hL HLP HCG hp hpa haτ (d + 1) c o
        (Reached.child hr hch hc) hco hcb' hsame' hin' hcl'
      exact ⟨e, List.mem_flatten.mpr ⟨o, ho, he⟩, her⟩
    have hplain : ∀ j, j = a.coeff d →
        (⟨slot (d + 2) it.source j, slot (d + 2) it.target j, none, 0, false⟩ : Item) ∈ cs →
        ∃ e ∈ outs.flatten, e.1.row = a := by
      intro j hj hmem
      subst hj
      exact key _ hmem rfl (sameRegion_slot hsame rfl rfl) (inRegion_slot_own hin) (Or.inl rfl)
    -- the node of the last column at `a` and the top of the last column in the region
    obtain ⟨v, hv, hva⟩ := last_root_row hL.top hp (hpa ▸ haτ)
    rw [hpa] at hva
    have hvin : inRegion (d + 2) it.source (official v.2.row) = true := by rw [hva]; exact hin
    obtain ⟨a0, ha0⟩ :=
      filter_last_exists (P := fun q => inRegion (d + 2) it.source (official q.2.row)) hv hvin
    have ha0' : topIn M (M.size - 1) (d + 2) it.source = some a0 := ha0
    have hx : topIn ctx.source ctx.x (d + 2) it.source = some a0 := by
      rw [hL.src, hL.xx]
      exact ha0'
    obtain ⟨_, ha0in, _⟩ := RowLaw.topIn_spec ha0'
    have hTopA : a.coeff d ≤ height (d + 2) (official a0.2.row) := by
      have hmax := RowLaw.topIn_row_max hb ha0' hv hvin
      rw [hva] at hmax
      exact agree_coeff hin ha0in hmax
    obtain ⟨bb, hasc⟩ := childItems_asc hch hx
    cases bb with
    | false =>
      have hcs := childItems_case1_list hch hx hasc
      apply hplain _ rfl
      rw [hcs]
      exact List.mem_map.mpr ⟨a.coeff d, List.mem_range.mpr (by omega), rfl⟩
    | true =>
      cases hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source with
      | none =>
        rw [hrho] at hasc
        simp [ascends, pure, Except.pure] at hasc
      | some rc =>
        obtain ⟨r, cl⟩ := rc
        have hasc' := hasc
        rw [hrho] at hasc'
        have hrho' : topIn M root.column (d + 2) it.source = some (r, cl) := by
          rw [← hL.src, ← hL.rc]
          exact hrho
        obtain ⟨hρmem, hρin, _⟩ := RowLaw.topIn_spec hrho'
        have hpin : inRegion (d + 2) it.source (official p.2.row) = true := by
          rw [hpa]; exact hin
        have haρ : a ≤ official cl.row := by
          have := RowLaw.topIn_row_max hb hrho' hp hpin
          rwa [hpa] at this
        have haR : a.coeff d ≤ height (d + 2) (official cl.row) := agree_coeff hin hρin haρ
        have hρτ : official cl.row < official t.row := lt_of_lowerRegion hr.lower hρin
        obtain ⟨v', hv', hv'r⟩ := last_root_row hL.top hρmem hρτ
        have hv'in : inRegion (d + 2) it.source (official v'.2.row) = true := by
          rw [hv'r]; exact hρin
        have hRT : height (d + 2) (official cl.row) ≤ height (d + 2) (official a0.2.row) := by
          have := RowLaw.topIn_row_max hb ha0' hv' hv'in
          rw [hv'r] at this
          exact agree_coeff hρin ha0in this
        have hNd : Nd ctx (official cl.row) := by
          obtain ⟨q, hq⟩ := RowLaw.nodeAt_of_mem hv'
          rw [hv'r] at hq
          exact ⟨q, by rw [hL.src, hL.xx]; exact hq⟩
        have hcut : heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) =
            height (d + 2) (official a0.2.row) := by
          rw [hL.lc, ← hL.xx, hx]
          rfl
        have hroot' : RootTop ctx (d + 1)
            (⟨slot (d + 2) it.source (height (d + 2) (official cl.row)), slot (d + 2) it.target
              (height (d + 2) (official cl.row)), some (official cl.row), 0, false⟩ : Item)
            (official cl.row) := ⟨r, cl, topIn_slot_self hrho (by omega), rfl⟩
        rcases hcl with hcl0 | ⟨C, hC, hrootC, haC⟩
        · -- case 2
          have hcs := childItems_case2 hch hcl0 hcb hx hrho hasc'
          rw [hcut] at hcs
          generalize hT : height (d + 2) (official a0.2.row) = hTt at hcs hTopA hRT
          generalize hR : height (d + 2) (official cl.row) = hRt at hcs haR hRT hroot'
          have hL0 : ctx.block = 0 → ((hTt : Int) - hRt) * (ctx.block : Int) = 0 := by
            intro h0; rw [h0]; simp
          have hLnn : 0 ≤ ((hTt : Int) - hRt) * (ctx.block : Int) :=
            Int.mul_nonneg (by omega) (by omega)
          have hLpos : ctx.block ≠ 0 → d ≠ 0 → 0 < ((hTt : Int) - hRt) * (ctx.block : Int) := by
            intro hb0 hd0
            have hlt := HLP (d + 2) it.source r cl (by omega) hb0 hr.lower hrho hNd hasc'
            rw [hcut] at hlt
            change height (d + 2) (official cl.row) < _ at hlt
            rw [hR, hT] at hlt
            exact Int.mul_pos (by omega) (by omega)
          generalize hLg : ((hTt : Int) - hRt) * (ctx.block : Int) = Lf at hcs hL0 hLnn hLpos
          have hjN : a.coeff d < ((hTt : Int) + Lf + 1).toNat := by omega
          have hmem : c2 (d + 2) it.source it.target ctx.block hRt Lf (official cl.row)
              (a.coeff d) ∈ cs := by
            rw [hcs]
            exact List.mem_map_of_mem (List.mem_range.mpr hjN)
          unfold c2 at hmem
          by_cases hjR : a.coeff d < hRt
          · rw [if_pos hjR] at hmem
            exact hplain _ rfl hmem
          · have hj : a.coeff d = hRt := by omega
            by_cases hcln : d = 0 ∨ ctx.block ≠ 0
            · have h2 : ((a.coeff d : Nat) : Int) < (hRt : Int) + Lf +
                  (if d + 2 = 2 then 1 else 0) := by
                rcases hcln with hd0 | hb0
                · subst hd0; simp; omega
                · by_cases hd0 : d = 0
                  · subst hd0; simp; omega
                  · have := hLpos hb0 hd0
                    simp [hd0]; omega
              rw [if_neg hjR, if_pos h2] at hmem
              refine key _ hmem (by simp [hj]) (sameRegion_slot hsame rfl (by rw [hj]))
                (by rw [← hj]; exact inRegion_slot_own hin) (Or.inr ⟨official cl.row, rfl, ?_, haρ⟩)
              obtain ⟨r', cl', h1, h2⟩ := hroot'
              exact ⟨r', cl', h1, h2⟩
            · have hb0 : ctx.block = 0 := by omega
              have hd0 : d ≠ 0 := by omega
              have hLf : Lf = 0 := hL0 hb0
              have h2 : ¬ ((a.coeff d : Nat) : Int) < (hRt : Int) + Lf +
                  (if d + 2 = 2 then 1 else 0) := by
                simp [hd0, hLf]; omega
              rw [if_neg hjR, if_neg h2] at hmem
              have hsj : (((a.coeff d : Nat) : Int) - Lf).toNat = a.coeff d := by
                rw [hLf]; simp
              have hib : decide (ctx.block ≠ 0 ∧ ((a.coeff d : Nat) : Int) = (hRt : Int) + Lf) =
                  false := by simp [hb0]
              rw [hsj, hib] at hmem
              exact hplain _ rfl hmem
        · -- case 4
          obtain ⟨r2, cl2, hrho2, hC2⟩ := hrootC
          rw [hrho] at hrho2
          have hcleq : cl2 = cl := (Prod.mk.inj (Option.some.inj hrho2)).2.symm
          have hCeq : C = official cl.row := by rw [← hC2, hcleq]
          subst hCeq
          obtain ⟨csRef, csc, g, hnode, hgen, hbd, hcs⟩ := childItems_case4 hch hC hx hrho hasc'
          obtain ⟨hbsome, hoff⟩ := hbd hcb
          rw [hcb, hoff] at hcs
          have hmem : c4 (d + 2) it.source it.target (height (d + 2) (official cl.row))
              (heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target)) 0 false
              (official cl.row) (a.coeff d) ∈ cs := by
            rw [hcs]
            apply List.mem_map_of_mem
            rw [List.mem_range]
            by_cases hb0 : ctx.block = 0
            · rw [if_pos hb0]
              omega
            · rw [if_neg hb0]
              have hgap := HCG hb0 d it (official cl.row) csRef csc g hr hC hcb hb0
                (by rw [hx]; rfl) hbsome hasc hnode hgen
              rw [hrho] at hgap
              change height (d + 2) (official cl.row) ≤ _ at hgap
              omega
          unfold c4 at hmem
          simp only [Bool.false_eq_true, if_false] at hmem
          by_cases hjR : a.coeff d < height (d + 2) (official cl.row)
          · rw [if_pos hjR] at hmem
            exact hplain _ rfl hmem
          · have hj : a.coeff d = height (d + 2) (official cl.row) := by omega
            rw [if_neg hjR] at hmem
            refine key _ hmem (by simp [hj]) (sameRegion_slot hsame rfl (by rw [hj]))
              (by rw [← hj]; exact inRegion_slot_own hin) (Or.inr ⟨official cl.row, rfl, ?_, haρ⟩)
            exact ⟨r, cl, topIn_slot_self hrho (by omega), rfl⟩

/-- **The lower part of the copy of the last column emits every root row below `τ`.** -/
theorem lower_emits_row {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} {ctx : Context}
    (hL : LastCtx s M t root ctx)
    (HLP : LiftPos ctx (official t.row)) (HCG : ctx.block ≠ 0 → CleanGap ctx (official t.row))
    {p : Ref × Cell} (hp : p ∈ realNodes M root.column)
    (hpτ : official p.2.row < official t.row) {es : List EO}
    (hes : emitsT ctx (official t.row) = .ok es) : ∃ e ∈ es, e.1.row = official p.2.row := by
  obtain ⟨outs, u, hF, _, rfl⟩ := emitsT_parts hes
  obtain ⟨k, j, hmem, hinR⟩ := lowerItems_cover hpτ
  obtain ⟨o, ho, hco⟩ := forall₂_left hF _ hmem
  obtain ⟨e, he, her⟩ := emits_row hL HLP HCG hp rfl hpτ (k + 1) _ o (Reached.root hmem) hco rfl
    (fun _ _ => rfl) hinR (Or.inl rfl)
  exact ⟨e, List.mem_append_left _ (List.mem_flatten.mpr ⟨o, ho, he⟩), her⟩

/-! ## The induction on the block -/

theorem boundary_source {cr x0 n i i' x : Nat} (hcr : cr < x0) (hi : 0 < i)
    (hx : x ∈ blockColumns cr x0 n i') (heq : x + (x0 - cr) * i' = cr + (x0 - cr) * i) :
    x = x0 ∧ i' + 1 = i := by
  have hw : 0 < x0 - cr := by omega
  have hxr : cr < x ∧ x ≤ x0 := mem_blockColumns hcr hx
  have h1 : (x0 - cr) * i' < (x0 - cr) * i := by omega
  have h1' : i' < i := Nat.lt_of_mul_lt_mul_left h1
  have h2 : (x0 - cr) * i ≤ (x0 - cr) * (i' + 1) := by rw [Nat.mul_succ]; omega
  have h2' : i ≤ i' + 1 := Nat.le_of_mul_le_mul_left h2 hw
  have hii : i = i' + 1 := by omega
  subst hii
  rw [Nat.mul_succ] at heq
  omega

/-- **`BoundaryRootRows`.** -/
theorem boundaryRootRowsHolds : BoundaryRootRows := by
  intro s n R hrun M col t root hM hcol ht hroot hcr i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hBs p hp hpτ
    have hτ : official t.row ≠ 0 := by
      intro h0
      rw [h0] at hpτ
      exact absurd hpτ (not_lt.mpr (Row.zero_le _))
    have hTop : Recon.Top s M t root := ⟨hM, by simp [hcol, ht], hτ, hroot, hcr⟩
    have hw : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ (by omega)
    -- there are copies
    have hn : n ≠ 0 := by
      rintro rfl
      obtain ⟨M', hM', hc⟩ := Reconstruction.expandDiagram_cases hrun
      obtain rfl : M' = M := Except.ok.inj (hM'.symm.trans hM)
      rcases hc with ⟨hs, rfl⟩ | ⟨_, col', t', _, _, hcase⟩
      · have := Canonical.build_size hM
        rw [hs, List.length_nil] at this
        omega
      · rcases hcase with ⟨_, rfl⟩ | ⟨_, hn0, _⟩
        · simp only [Array.size_pop] at hBs
          omega
        · exact hn0 rfl
    obtain ⟨_, hinv⟩ := expandDiagram_splice hrun hM hcol ht (by tauto) hroot
    obtain ⟨_, _, hall⟩ := hinv
    obtain ⟨i', x, _, hxb, hX, hcopy⟩ := hall _ hBs (by omega)
    obtain ⟨rfl, hii⟩ := boundary_source hcr (by omega) hxb hX.symm
    obtain ⟨es, hes, hasm⟩ := copyColumn_emitsT hcopy
    set ctx := ctxAt M R (M.size - 1) i' root.column (M.size - 1 - root.column) (M.size - 1)
      (root.column + (M.size - 1 - root.column) * i) with hctx
    have hLc : LastCtx s M t root ctx := ⟨hTop, rfl, rfl, rfl, rfl⟩
    have HLP : LiftPos ctx (official t.row) :=
      liftPosHolds s M col t root hM hcol ht hroot hcr ctx rfl rfl rfl (by
        show root.column < M.size - 1; exact hcr) (le_refl _)
    have HCG : ctx.block ≠ 0 → CleanGap ctx (official t.row) := by
      intro _
      have := cleanGap_at (t := t) hrun hM hcr hxb (fun hi1 => ih i' (by omega) hi1)
      rw [← hX] at this
      exact this
    obtain ⟨e, he, her⟩ := lower_emits_row hLc HLP HCG hp hpτ hes
    obtain ⟨k, hk, hek⟩ := List.getElem_of_mem he
    obtain ⟨_, hcells⟩ := assemble_spec hasm
    obtain ⟨cell, hcell, hrow, _⟩ := hcells k (by simpa using hk)
    refine ⟨(⟨root.column + (M.size - 1 - root.column) * i, k + 1⟩, cell),
      mem_realNodes_iff.mpr ⟨_, k, Array.getElem?_eq_getElem hBs, hcell, rfl⟩, ?_⟩
    simp only
    rw [hrow, List.getElem_map, hek, her]
    exact JumpLaw.official_stored _

/-- **`CleanGapHolds`.** -/
theorem cleanGapHolds : CleanGapHolds := cleanGapHolds_of_boundary boundaryRootRowsHolds

/-- **`CutPredHolds`.** In the traced emits of every copied column, a cut emit is immediately
preceded by a clean emit from the same source with the same left column. -/
theorem cutPredHolds : CutPredHolds := cutPredHolds_of_boundaryRootRows boundaryRootRowsHolds

/-- **`CrossLexFor IsCut`.** -/
theorem crossLexFor_cut_holds : CrossLexFor IsCut := crossLexFor_cut cutPredHolds

/-- **`CrossChainHolds` from `ParentBelowHolds` and the three other kinds.** -/
theorem crossChainHolds_of_rest (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hCl : CrossLexFor IsClean) (hU : CrossLexFor IsUpper) : CrossChainHolds :=
  crossChainHolds_of_three hPB hP hCl cutPredHolds hU

/-- **`ChainHolds` from `ParentBelowHolds` and the three other kinds.** -/
theorem chainHolds_of_rest (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hCl : CrossLexFor IsClean) (hU : CrossLexFor IsUpper) : ChainHolds :=
  chainHolds_of_three hPB hP hCl cutPredHolds hU

end OmegaY.Official.Recon.CutPredMD

#print axioms OmegaY.Official.Recon.CutPredMD.boundaryRootRowsHolds
#print axioms OmegaY.Official.Recon.CutPredMD.cleanGapHolds
#print axioms OmegaY.Official.Recon.CutPredMD.cutPredHolds
#print axioms OmegaY.Official.Recon.CutPredMD.crossLexFor_cut_holds
#print axioms OmegaY.Official.Recon.CutPredMD.crossChainHolds_of_rest
#print axioms OmegaY.Official.Recon.CutPredMD.chainHolds_of_rest
