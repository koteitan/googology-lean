/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsBlock0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `upperT_run`, in the proof passed to `mapM_map_fst`, the goal is beta-reduced before `cases leftColumn p.2`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsCols
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyBlockZero
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawUpper

set_option backward.do.legacy false

/-!
# The emitted list of a column: lower and upper part

`emitsT` is the lower part (the emits of the first items, `lowerT`) followed by the upper
part (`upperT`). This file relates the two parts to `Recon.JumpLaw.LowerRun` and
`Recon.JumpLaw.UpperRun`, the form in which `Recon` proves the covering lemmas
(`Recon.JumpLaw.lower_id` for block `0`, `Recon.JumpLaw.upper_facts`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

theorem emitsT_split {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∃ lo us, lowerT ctx τ = .ok lo ∧ upperT ctx τ = .ok us ∧ es = lo ++ us := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lo hlo
    split at h
    · cases h
    · rename_i us hus
      cases h
      exact ⟨lo, us, hlo, hus, rfl⟩

theorem lowerT_run {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) :
    ∃ vs, Recon.JumpLaw.LowerRun ctx τ vs ∧ vs.flatten = lo.map Prod.fst := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    have hm := mapM_map_fst (fun x : Nat × Item => runItem ctx x.1 x.2)
      (fun p => runItemT ctx p.1 p.2) (List.map Prod.fst) (fun p => runItemT_fst ctx p.1 p.2)
      (lowerItems τ)
    rw [houts] at hm
    refine ⟨outs.map (List.map Prod.fst), hm.symm, ?_⟩
    rw [List.map_flatten]

theorem lowerT_notUpper' {ctx : Context} {τ : Row} {lo : List (Emit × Origin)}
    (h : lowerT ctx τ = .ok lo) : ∀ p ∈ lo, p.2.isUpper = false := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    cases h
    intro p hp
    obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
    obtain ⟨c, _, hc⟩ := mem_of_mapM houts hout
    exact runItemT_not_upper ctx c.1 c.2 out hc p hpo

theorem upperT_run {ctx : Context} {τ : Row} {us : List (Emit × Origin)}
    (h : upperT ctx τ = .ok us) :
    Recon.JumpLaw.UpperRun ctx τ (us.map Prod.fst) ∧ ∀ p ∈ us, p.2.isUpper = true := by
  have hU := mapM_map_fst
    (fun x : Ref × Cell => Except.bind (leftColumn x.2)
      (fun v => Except.ok ({ row := official x.2.row, leftColumn := some v } : Emit)))
    (fun p : Ref × Cell => (do
      return ((⟨official p.2.row, some (← leftColumn p.2)⟩ : Emit), Origin.upper p.1) :
        Result (Emit × Origin)))
    Prod.fst (fun p => by beta_reduce; cases leftColumn p.2 <;> rfl)
    ((realNodes ctx.source (upperColumn ctx)).filter
      (fun p => decide (τ ≤ official p.2.row)))
  have h' : ((realNodes ctx.source (upperColumn ctx)).filter
      (fun p => decide (τ ≤ official p.2.row))).mapM (fun p : Ref × Cell => (do
      return ((⟨official p.2.row, some (← leftColumn p.2)⟩ : Emit), Origin.upper p.1) :
        Result (Emit × Origin))) = .ok us := h
  rw [h'] at hU
  refine ⟨hU.symm, ?_⟩
  intro p hp
  obtain ⟨q, _, hq⟩ := mem_of_mapM h' hp
  simp only [bind, Except.bind, pure, Except.pure] at hq
  split at hq
  · cases hq
  · cases hq
    rfl

/-! ## The top of the last column -/

/-- The top `t` of the splice data is a real top whose left end is in the root column. -/
theorem data_top {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) :
    ∃ root, Recon.Top s M t root ∧ root.column = ρ.cr ∧ ρ.x0 = M.size - 1 := by
  have hV := build_valid_of_success hd.splice.build
  obtain ⟨col, hcol, ht⟩ := hd.last
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hd.run
  rw [hd.splice.build] at hM'
  cases hM'
  have hsz := build_size hd.splice.build
  have hx := (root?_spec hV hd.splice.root).1
  rcases hcases with ⟨he, _⟩ | ⟨col', t', hcol', ht', hbr⟩
  · have : s = [] := List.isEmpty_iff.mp he
    subst this
    simp only [List.length_nil] at hsz
    omega
  · have hcc : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst hcc
    have htt : t' = t := Option.some.inj (ht'.symm.trans ht)
    subst htt
    rcases hbr with ⟨hdel, _⟩ | ⟨hsp, root, htl, hlt, _, _⟩
    · rcases hdel with h0 | h0
      · have hr := hd.splice.root
        rw [root?_none_of_official_zero hV D hcol' ht' h0] at hr
        cases hr
      · exact absurd h0 hd.splice.copies
    · obtain ⟨ρ', hr', hx0, hcr'⟩ :=
        root?_of_official_ne_zero hV D hcol' ht' (fun h0 => hsp (Or.inl h0)) htl
      have hρ : ρ' = ρ := Option.some.inj (hr'.symm.trans hd.splice.root)
      subst hρ
      refine ⟨root, ⟨hd.splice.build, by rw [hcol']; exact ht', fun h0 => hsp (Or.inl h0), htl,
        hlt⟩, hcr'.symm, hx0⟩

/-! ## The profile of the column `x₀` in block `0` -/

/-- **Block `0`.** The copy of `x₀` in block `0` emits every node of `x₀` below `τ` (lower
part) and every node of `cr` at or above `τ` (upper part), each at the official row of its
origin. -/
theorem b0_profile {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) (hn : 0 < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) 0 ρ.x0 = .ok esB) :
    (∀ j (hj : j < esB.length), ∃ cμ, cell? M esB[j].2.src = some cμ ∧
      official cμ.row = esB[j].1.row) ∧
    (∀ j (hj : j < esB.length), esB[j].2.isUpper = false → esB[j].1.row < official t.row) ∧
    (∀ j (hj : j < esB.length), esB[j].2.isUpper = true → official t.row ≤ esB[j].1.row) ∧
    (∀ (p : Ref) (c : Cell), p.column = ρ.x0 → 1 ≤ p.index → cell? M p = some c →
      official c.row < official t.row →
      ∃ j, ∃ hj : j < esB.length, esB[j].2.isUpper = false ∧ esB[j].1.row = official c.row) ∧
    (∀ (p : Ref) (c : Cell), p.column = ρ.cr → 1 ≤ p.index → cell? M p = some c →
      official t.row ≤ official c.row →
      ∃ j, ∃ hj : j < esB.length, esB[j].2.isUpper = true ∧ esB[j].1.row = official c.row) := by
  obtain ⟨root, hTop, hrc, hx0⟩ := data_top hd
  obtain ⟨_, hcrx, _, _⟩ := spliceData_facts hd
  obtain ⟨hXR, _⟩ := bcol hd hn hes
  have hes' : emitsT (bctx M R ρ.cr ρ.x0 0) (official t.row) = .ok esB := hes
  have hctx : Recon.RunCtx s (bctx M R ρ.cr ρ.x0 0) t root := by
    refine ⟨hTop, hx0, hrc.symm, hcrx, le_refl _, ?_⟩
    simp only [bctx, ctxAt, Array.size_extract]
    omega
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := emitsT_split hes'
  obtain ⟨vs, hvs, hvsf⟩ := lowerT_run hlo
  obtain ⟨hU, hUup⟩ := upperT_run hus
  have hLnot := lowerT_notUpper' hlo
  obtain ⟨hE1, hE2⟩ := Recon.JumpLaw.lower_id hctx rfl hvs
  obtain ⟨hU1, hU2⟩ := Recon.JumpLaw.upper_facts hU
  have hup : upperColumn (bctx M R ρ.cr ρ.x0 0) = ρ.cr := by
    simp [upperColumn, bctx, ctxAt]
  rw [hup] at hU1 hU2
  -- positions
  have hpos : ∀ j (hj : j < esB.length), (esB[j].2.isUpper = false → ∃ hj' : j < lo.length,
      esB[j] = lo[j]) ∧ (esB[j].2.isUpper = true → lo.length ≤ j ∧
        ∃ hj' : j - lo.length < us.length, esB[j] = us[j - lo.length]) := by
    intro j hj
    subst hsplit
    by_cases hjl : j < lo.length
    · refine ⟨fun _ => ⟨hjl, List.getElem_append_left hjl⟩, fun hU' => ?_⟩
      have := hLnot lo[j] (List.getElem_mem hjl)
      rw [List.getElem_append_left hjl] at hU'
      rw [this] at hU'
      cases hU'
    · have hjl' : lo.length ≤ j := by omega
      have hj2 : j - lo.length < us.length := by simp at hj; omega
      refine ⟨fun hL' => ?_, fun _ => ⟨hjl', hj2, List.getElem_append_right hjl'⟩⟩
      have := hUup us[j - lo.length] (List.getElem_mem hj2)
      rw [List.getElem_append_right hjl'] at hL'
      rw [this] at hL'
      cases hL'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    cases hju : esB[j].2.isUpper
    · obtain ⟨cv, hcv, hr⟩ := emitsT_block0 (ctx := bctx M R ρ.cr ρ.x0 0) rfl hes' esB[j]
        (List.getElem_mem hj) hju
      exact ⟨cv, hcv, hr⟩
    · obtain ⟨cv, hcv, hr⟩ := emitsT_upper_row hes' esB[j] (List.getElem_mem hj) hju
      exact ⟨cv, hcv, hr.symm⟩
  · intro j hj hju
    obtain ⟨hj', he⟩ := (hpos j hj).1 hju
    have hmem : esB[j].1 ∈ vs.flatten := by
      rw [hvsf, he]; exact List.mem_map_of_mem (List.getElem_mem hj')
    obtain ⟨_, _, _, hlt, _⟩ := hE1 _ hmem
    exact hlt
  · intro j hj hju
    obtain ⟨_, hj', he⟩ := (hpos j hj).2 hju
    have hmem : esB[j].1 ∈ us.map Prod.fst := by
      rw [he]; exact List.mem_map_of_mem (List.getElem_mem hj')
    obtain ⟨_, _, _, hle, _⟩ := hU1 _ hmem
    exact hle
  · intro p c hpc hpi hc hlt
    obtain ⟨col, hcol, hpi', hcp⟩ := cell?_column hc
    have hmem : (p, c) ∈ realNodes (bctx M R ρ.cr ρ.x0 0).source (bctx M R ρ.cr ρ.x0 0).x := by
      refine Recon.mem_realNodes_iff.mpr ⟨col, p.index - 1, ?_, ?_, ?_⟩
      · simp only [bctx, ctxAt]; rw [← hpc]; exact hcol
      · rw [show p.index - 1 + 1 = p.index by omega, ← hcp]
        exact Array.getElem?_eq_getElem hpi'
      · simp only [bctx, ctxAt]
        exact ref_eq_of hpc (by simp; omega)
    obtain ⟨em, hem, hrow⟩ := hE2 _ hmem hlt
    rw [hvsf] at hem
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hem
    simp only [List.length_map] at hj
    have hjB : j < esB.length := by rw [hsplit]; simp; omega
    have he : esB[j] = lo[j] := by
      simp only [hsplit]; exact List.getElem_append_left hj
    refine ⟨j, hjB, ?_, ?_⟩
    · rw [he]; exact hLnot _ (List.getElem_mem hj)
    · rw [he, ← hrow, ← hjeq]; simp
  · intro p c hpc hpi hc hle
    obtain ⟨col, hcol, hpi', hcp⟩ := cell?_column hc
    have hmem : (p, c) ∈ realNodes (bctx M R ρ.cr ρ.x0 0).source ρ.cr := by
      refine Recon.mem_realNodes_iff.mpr ⟨col, p.index - 1, ?_, ?_, ?_⟩
      · simp only [bctx, ctxAt]; rw [← hpc]; exact hcol
      · rw [show p.index - 1 + 1 = p.index by omega, ← hcp]
        exact Array.getElem?_eq_getElem hpi'
      · exact ref_eq_of hpc (by simp; omega)
    obtain ⟨em, hem, hrow⟩ := hU2 _ hmem hle
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hem
    simp only [List.length_map] at hj
    have hjB : lo.length + j < esB.length := by rw [hsplit]; simp; omega
    have he : esB[lo.length + j] = us[j] := by
      simp only [hsplit]
      rw [List.getElem_append_right (by omega)]
      simp
    refine ⟨lo.length + j, hjB, ?_, ?_⟩
    · rw [he]; exact hUup _ (List.getElem_mem hj)
    · rw [he, ← hrow, ← hjeq]; simp

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
