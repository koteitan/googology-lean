/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/Pkg3StepCut.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LowerChain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapFinal

set_option backward.do.legacy false

/-!
# `StepCut` from the shared chain statements (package 3)

`StepCut` (`ChainCorrCut.lean`): for a gap copy `v` (block `i ≥ 1`, inner column) of `m` and a
step `m → m'` of the scale-`k` chain of `M(s)`, the scale-`k` chain of the output from `v` matches
the step over `CutRel` (`Next`), or a higher scale has a strictly smaller root (`Wit`).

The earlier reduction (`CutParts.stepCut_at`) used `StepInner`, which is false, and the lookup
`CutTopLookup` at the top of a run of gap copies. Here:

* **At the top of a run** (the emit above `v` is not a gap copy of `m`), `v` is the top copy of
  `m` (`topNode_of_top`: the emit above is the copy of the node above `m`, `topNext'`, and the
  sources of the emits of a column only go up, `emitsT_mono`). So `TopStep` gives the step
  directly (`next_of_stand`), with no witness.
* **Inside a run**, the raw parent of `v` is `pe` (as in `stepCut_at`), `v` is not a top copy,
  and the argument of `stepCut_at` goes through with `CutStartRootNT` in place of `CutStartRoot`
  and the walk over copies done by `rel_step` (`TopStep`, `NonTopStep`) in place of `StepInner`.

Results:

* `cutStartCopyNT` : `CutStartCopyNT` (**proved**, from `CutParts.cutStartCopy'`).
* `stepCut_of_lower` : `StepCut` from `TopStep`, `NonTopStep` (stage B, shared/package 2),
  `CutStartRootNT` and `CutJump` (package 3).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CutParts ChainCorr.LowerChain

/-- **`CutStartCopyNT` holds.** -/
theorem cutStartCopyNT : CutStartCopyNT :=
  cutStartCopyNT_of_cutStartCopy cutStartCopy'

/-! ## Relations -/

theorem cutRel_of_copyOf {M R : Mountain} {n cr x0 : Nat} {τ : Row} {i : Nat} {v m : Ref}
    (h : CopyOf M R n cr x0 τ i v m) : CutRel M R n cr x0 τ i v m := by
  obtain ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, hsrc⟩ := h
  cases hc : cutOrigin es[j].2
  · exact Or.inl ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, hsrc, Or.inl hc⟩
  · exact Or.inr ⟨y, es, j, h1, h2, h3, h4, h5, h6, hj, hsrc, hc⟩

theorem cutRel_of_rel {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {v m : Ref}
    (h : Rel M R n cr x0 τ θ i v m) : CutRel M R n cr x0 τ i v m := by
  rcases h with h | h
  · exact Or.inl h
  · exact cutRel_of_copyOf h.1

/-! ## The top of a run of gap copies is the top copy -/

/-- **At the top of a run of gap copies of `m`, the node is the top copy of `m`.** -/
theorem topNode_of_top {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X y i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X y i es) (hcy : ρ.cr < y) (hyx : y < ρ.x0)
    {j : Nat} (hj : j < es.length) {m : Ref} (ho : es[j].2 = .clean m true)
    (hnot : ∀ hj' : j + 1 < es.length, es[j + 1].2 ≠ es[j].2)
    {c : Cell} (hc : cell? M (Inner.up m) = some c) :
    TopNode M R n ρ.cr ρ.x0 (official t.row) t.row i ⟨X, j + 1⟩ m := by
  have hV := build_valid_of_success hS.splice.build
  have hsrc : es[j].2.src = m := by rw [ho]; rfl
  have hcut : cutOrigin es[j].2 = true := by rw [ho]; rfl
  have hes : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es :=
    hS.emits
  obtain ⟨_, hm1, cm, hcm, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hsrc] at hm1 hcm
  refine ⟨⟨y, es, j, hcy, hyx, hS.xMem, hS.Xeq, rfl, hes, hj, hsrc⟩, ?_, ?_⟩
  · rintro v' hv'c hv'i ⟨c', _⟩ ⟨y', es', j', _, _, _, hv', hvi', hes', hj', hsrc'⟩
    have hXeq := hS.Xeq
    have hyy : y = y' := by
      simp only at hv'c
      omega
    subst hyy
    rw [hv'c] at hes'
    have hee : es = es' := Except.ok.inj (hes.symm.trans hes')
    subst hee
    have hjj : j < j' := by
      simp only at hv'i
      omega
    have hc0 : cell? M (Inner.up es[j].2.src) = some c := by rw [hsrc]; exact hc
    obtain ⟨hj1, hsrc1, _⟩ := topNext' hS hyx hj hcut hnot hc0
    rw [hsrc] at hsrc1
    rcases Nat.lt_or_ge j' (j + 2) with h | h
    · have hj'1 : j' = j + 1 := by omega
      subst hj'1
      rw [hsrc'] at hsrc1
      have := congrArg Ref.index hsrc1
      simp [Inner.up] at this
    · have hpw := ChainCorr.CopyMonoProof.emitsT_mono
        (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) hV hes
      have hole := List.pairwise_iff_getElem.mp hpw (j + 1) j' hj1 hj' (by omega) c cm
        (by rw [hsrc1]; exact hc) (by rw [hsrc']; exact hcm)
      have hlt : cm.row < c.row := by
        obtain ⟨mc, mi⟩ := m
        exact ChainCorr.cell_row_lt hV hcm hc (by simp)
      exact absurd hole (not_le.mpr (Recon.official_strictMono (one_le_row hV hcm hm1) hlt))
  · intro cm' cv hcm' _ hθ
    exfalso
    obtain ⟨col, hcol, ht⟩ := hS.last
    obtain ⟨root, hTop, _, _⟩ := top_of_splice hS.splice hS.run hcol ht
    obtain ⟨c0, hc0, hlt⟩ := emitsT_lower_below hes es[j] (List.getElem_mem hj)
      (by rw [ho]; rfl)
    change cell? M es[j].2.src = some c0 at hc0
    rw [hsrc, hcm'] at hc0
    cases hc0
    exact absurd (Recon.official_mono hTop.row_one_le hθ) (not_le.mpr hlt)

/-! ## `StepCut` -/

/-- `StepCut` at one scale, by strong induction on the column of the origin. -/
theorem stepCut_lower_at (hTS : TopStep) (hNS : NonTopStep) (hRoot : CutStartRootNT)
    (hJump : CutJump)
    {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain}
    {col : Column} {t : Cell} (hS : Inner.Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {k : Nat} (hkD : k ≤ D) :
    ∀ c v m, m.column = c → CutNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ∀ m', MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CutRel M R n ρ.cr ρ.x0 (official t.row) i) v m' ∨
        Wit R M D k ρ.cr ((ρ.x0 - ρ.cr) * i) v m := by
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  obtain ⟨root, hTop, hcr, hx0⟩ := top_of_splice hS.splice hS.run hS.hcol hS.ht
  have hin : i ≤ n := by omega
  -- a step from a copy that is not a gap copy (`rel_step`)
  have hcopyStep : ∀ v a a', CopyNode M R n ρ.cr ρ.x0 (official t.row) i v a →
      MStep M k a a' →
      Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CutRel M R n ρ.cr ρ.x0 (official t.row) i) v a' := by
    intro v a a' hva hst
    have h' : Rel M R n root.column (M.size - 1) (official t.row) t.row i v a := by
      rw [← hcr, ← hx0]; exact Or.inl hva
    have := rel_step hTS hNS hS.run hTop hi0 hin h' hst
    rw [← hcr, ← hx0] at this
    exact next_mono (fun _ _ h => cutRel_of_rel h) this
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro v m hmc hvm m' hst
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, hsrc, hcut⟩ := hvm
  have hS' := site_of_emits hS hi0 hi hcy hyx hyb hvc hes
  have hv : v = ⟨v.column, j + 1⟩ := ref_mk rfl hvi
  have ho : es[j].2 = .clean m true := by
    revert hsrc hcut
    generalize es[j].2 = o
    intro hsrc hcut
    cases o with
    | clean r b =>
        cases b
        · simp [cutOrigin] at hcut
        · simp only [Origin.src] at hsrc
          rw [hsrc]
    | plain r => simp [cutOrigin] at hcut
    | upper r => simp [cutOrigin] at hcut
  have hvat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean m true) :=
    ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩
  obtain ⟨cu, ref, cv, l, hcu, href, hcv, hl, hrefc⟩ := Inner.copyAt_left hS hi0 hi hvat
  simp only [Origin.src] at hcv
  have hpar := hst.1
  have hsrcm : es[j].2.src = m := by rw [ho]; rfl
  obtain ⟨_, hm1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
  rw [hsrcm] at hm1
  by_cases hrun : ∃ hj' : j + 1 < es.length, es[j + 1].2 = es[j].2
  · -- inside a run: the raw parent of `v` is `pe`, and `v` is not a top copy
    obtain ⟨hj1, hrun⟩ := hrun
    have hntop : ¬ IsTopAt es j := by
      intro htop
      exact htop (j + 1) hj1 hj (by omega) (by rw [hrun])
    have hupat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i (Inner.up v) (.clean m true) :=
      ⟨y, es, j + 1, hcy, hyx, hyb, hvc, by simp [Inner.up, hvi], hes, hj1, by rw [hrun, ho]⟩
    obtain ⟨cu', ref', cv', l', hcu', href', hcv', hl', hrefc'⟩ :=
      Inner.copyAt_left hS hi0 hi hupat
    simp only [Origin.src] at hcv'
    have hcvv : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
    subst cv'
    have hll : l' = l := Option.some.inj (hl'.symm.trans hl)
    subst l'
    have hraw : rawParent R v = some ref' := Inner.rawParent_eq_some.mpr ⟨cu', hcu', href'⟩
    have hv0 : 0 < v.index := by omega
    have hham := Inner.canon_rawParent_hAM hS.canon hv0 hcu hraw
    have hcolr : ref'.column = ref.column := by rw [hrefc, hrefc']
    rw [hcolr] at hham
    obtain ⟨pa, hpa⟩ := hAM_of_left hV hcv hm1 hl
    obtain ⟨_, cpe, hcpe⟩ := highestAtMost_cell hham
    obtain ⟨hpac, cpa, hcpa⟩ := highestAtMost_cell hpa
    have hcu0 : cell? R ⟨v.column, j + 1⟩ = some cu := by rw [← hv]; exact hcu
    have hL : Legs M R v.column j es[j].2 cu cv ref l ref' pa cpe cpa :=
      ⟨hcu0, href, by rw [hsrcm]; exact hcv, hl, hham, hpa, hcpe, hcpa⟩
    have hgen := cutGenReach s n D M out ρ R t v.column y i es hS' hyx j hj (by rw [ho]; rfl) cu
      cv ref l ref' pa cpe cpa hL k m' hkD (by rw [hsrcm]; exact hst)
    have hcrl := cutLeg s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l
      ref' pa cpe cpa hL
    have himg := leg_image hS' hj hL
    by_cases hde : Row.jump cu.row cpe.row ≤ k
    · have hreach : ScaleReach R k v ref' := Inner.reach_one hVR hraw hcu hcpe hde
      rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
      · -- a leg right of `cr`: the walk from the gap copy `pe` of `pa`
        have hcp := cutStartCopy' s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu
          cv ref l ref' pa cpe cpa hL hlt
        have hlm : l.column < m.column := by
          have := left_lt_of_valid hV hcv hl
          omega
        have hw := walk (D := D) hA (le_of_lt hcrx) (CutRel M R n ρ.cr ρ.x0 (official t.row) i)
          (c1 := pa.column)
          (fun v a h => by
            have := cutRel_column h
            rcases h with h | h
            · obtain ⟨y', _, _, hcy', _, _, hvc', _, hes', hj', hsrc', _⟩ := h
              obtain ⟨hsc, _⟩ := emitsT_good hes' _ (List.getElem_mem hj')
              rw [hsrc'] at hsc
              have hne : ¬ y' = ρ.x0 := by omega
              have : a.column = y' := by
                rw [hsc]
                split
                · simp [upperColumn, ctxAt, hne]
                · simp [ctxAt]
              omega
            · obtain ⟨y', _, _, hcy', _, _, hvc', _, hes', hj', hsrc', _⟩ := h
              obtain ⟨hsc, _⟩ := emitsT_good hes' _ (List.getElem_mem hj')
              rw [hsrc'] at hsc
              have hne : ¬ y' = ρ.x0 := by omega
              have : a.column = y' := by
                rw [hsc]
                split
                · simp [upperColumn, ctxAt, hne]
                · simp [ctxAt]
              omega)
          (by
            intro v' a a' hva hac hst'
            rcases hva with hva | hva
            · exact Or.inl (hcopyStep v' a a' hva hst')
            · have hpa' : pa.column = l.column := hpac
              exact ih a.column (by omega) v' a rfl hva a' hst')
          pa hgen ref' (Or.inr hcp) (le_refl _)
        rcases hw with hn | hw
        · exact Or.inl (next_of_reach hreach hn)
        · exact Or.inr (wit_of_meet hreach hst.reach hgen hw)
      · -- the leg is the root column
        have hpacol : pa.column = ρ.cr := by rw [hpac, heq]
        have hpecol : ref'.column = ρ.cr + (ρ.x0 - ρ.cr) * i := by
          rw [hcolr, himg, ← heq, mapColumn_of_ge (le_refl _)]
        have hnext := fun kk m'' (h1 : Row.jump cv.row cpa.row ≤ kk) (h2 : kk ≤ D)
            (h3 : MStep M kk pa m'') =>
          hRoot s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) hntop cu cv ref l
            ref' pa cpe cpa hL heq.symm kk m'' h1 h2 h3
        have hrow := cutPaRow s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref
          l ref' pa cpe cpa hL
        have hda : Row.jump cv.row cpa.row = 0 := by rw [hrow, Row.jump_self]
        left
        cases hgen with
        | refl =>
            exact ⟨fun h => absurd h (by omega),
              fun _ => ⟨ref', hreach, le_of_eq hpecol,
                fun m'' h => hnext k m'' (by omega) hkD h⟩,
              fun h => absurd h (by omega)⟩
        | @step _ p' _ c' cp' hpar' hc' hcp' hj' hlt' hrest =>
            have hst' : MStep M k pa p' := ⟨hpar', c', cp', hc', hcp', hj', hlt'⟩
            have hr2 := hnext k p' (by omega) hkD hst'
            have hr3 := reach_agree hA hrest (by omega)
            have hq := hrest.column_le
            exact ⟨fun _ => ScaleReach.trans hreach (ScaleReach.trans hr2 hr3),
              fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · -- the chain of `v` stops: the witness of `CutJump`
      right
      rcases hJump s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv ref l ref'
        pa cpe cpa hL with hle | ⟨k', h1, _, h3, h4⟩
      · have hrow := cutPaRow s n D M out ρ R t v.column y i es hS' j hj (by rw [ho]; rfl) cu cv
          ref l ref' pa cpe cpa hL
        rw [hrow, Row.jump_self] at hle
        omega
      · refine ⟨k', by omega, h3, ?_⟩
        have hr' : ScaleReach R k' v ref' := Inner.reach_one hVR hraw hcu hcpe h1
        have hk' : k ≤ k' := by omega
        rw [root_of_reach hr', root_of_reach (reach_mono hst.reach hk'),
          ← root_of_reach (reach_mono hgen hk')]
        exact h4
  · -- at the top of a run: `v` is the top copy of `m`, and `TopStep` applies
    have hnot : ∀ hj' : j + 1 < es.length, es[j + 1].2 ≠ es[j].2 := fun hj' h => hrun ⟨hj', h⟩
    obtain ⟨cup, hcup, _⟩ := Inner.rawParent_eq_some.mp hpar
    have htop := topNode_of_top hS' hcy hyx hj ho hnot hcup
    rw [← hv] at htop
    have htop' : TopNode M R n root.column (M.size - 1) (official t.row) t.row i v m := by
      rw [← hcr, ← hx0]; exact htop
    obtain ⟨_, cm, cm', hcm, hcm', hjm, _⟩ := hst
    obtain ⟨A, hvA, hSt⟩ := hTS s n R M t root i hS.run hTop hi0 hin v m htop' m' cm cm' hpar
      hcm hcm'
    have hn := next_of_stand (MStep.mono hvA hjm) hSt
    rw [← hcr, ← hx0] at hn
    exact Or.inl (next_mono (fun _ _ h => cutRel_of_rel h) hn)

/-- **`StepCut` from `TopStep`, `NonTopStep`, `CutStartRootNT` and `CutJump`.** -/
theorem stepCut_of_lower (hTS : TopStep) (hNS : NonTopStep) (hRoot : CutStartRootNT)
    (hJump : CutJump) : StepCut := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hi0 hi v m hvm k m' hkD hst
  exact stepCut_lower_at hTS hNS hRoot hJump ⟨hc, hdeg, hRun, hRb, hcol, ht⟩ hi0 hi hkD
    m.column v m rfl hvm m' hst

end OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutStartCopyNT
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.topNode_of_top
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.stepCut_of_lower
