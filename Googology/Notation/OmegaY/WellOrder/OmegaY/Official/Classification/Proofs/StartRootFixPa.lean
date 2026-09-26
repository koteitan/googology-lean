/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootFixPa.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsPa
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootFixCmp
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchBoundary

set_option backward.do.legacy false

/-!
# `PaLookup` and `OriginReach` (proved)

`PaLookup` (`StartRootPartsOriginLower.lean`): for a node `u` of block `i ≥ 1` that is not a
gap copy, with origin `o` (row `σ`) whose leg is the root column `cr`, let `pa` be the highest
node of `cr` at or below `σ` and `pe` the highest node of the boundary column
`B = x₀ + w·(i - 1)` at or below the row of `u`. If the origin `ν` of `pe` is not an upper
origin, then `pa` is also the highest node of `cr` at or below the row of `ν`.

`StartRootPartsPa.lean` derived it from (MA), which is false. Here it is proved from
`SRCmp.rootCmp` (the copies keep their place among the rows of the root column, proved without
(MA)) and `LegJump.boundaryRootRows` (the boundary column has every row of the root column
below `τ`, proved). Write `r_c` for the official row of a node `c`.

1. `r_pa ≤ r_ν`. By `rootCmp` for `u`, `r_pa ≤ σ` gives `r_pa ≤ row u`. If `r_pa ≥ τ`, `B` has an
   upper copy of `pa` at `r_pa`, above the lower `pe` but at or below `u`: impossible. Otherwise
   `B` has a node at `r_pa` (`boundaryRootRows`), at or below `u`, so `row pe ≥ r_pa`; and if
   `r_ν < r_pa`, `rootCmp` for `pe` (copy or gap copy) gives `row pe < r_pa`.
2. No node `c` of `cr` has `σ < r_c ≤ r_ν`: `rootCmp` for `u` gives `row u < r_c`, and for `pe`
   `r_c ≤ row pe` (a copy keeps the side of `r_c`, a gap copy is above every root row at or
   below its origin row); but `row pe ≤ row u`.

With `X0Reach` (proved, `StartRootPartsX0.lean`), this proves `OriginReach` (`originReach`).
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRFixPa

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner ChainCorr.SRParts ChainCorr.SRX0 ChainCorr.SRPa CopyShape

theorem mem_blockColumns_x0 {cr x0 n m : Nat} (hcr : cr < x0) (hm : m < n) :
    x0 ∈ blockColumns cr x0 n m := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    simp [blockColumns]
  · exact x0_mem_blockColumns hcr h0 hm

/-- **`PaLookup` holds.** -/
theorem paLookup : SRParts.PaLookup := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB hesB k hk
    hpek hlow cν hcν
  have hd := hS.data
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  obtain ⟨_, hcrx, _, _⟩ := spliceData_facts hd
  have hipos := hS.iPos
  have hm : i - 1 < n := by have := hS.iLt; omega
  have hesB' : emitsT (bctx M R ρ.cr ρ.x0 (i - 1)) (official t.row) = .ok esB := hesB
  have hblx : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  -- the comparisons with the root rows
  have hCu := SRCmp.rootCmp s n D M out ρ R t hd i hS.iLt x hS.xMem es hblx es[j]
    (List.getElem_mem hj) cv hL.hcv
  have hCB := SRCmp.rootCmp s n D M out ρ R t hd (i - 1) (by omega) ρ.x0
    (mem_blockColumns_x0 hcrx hm) esB hesB esB[k] (List.getElem_mem hk) cν hcν
  -- the row of `u`
  obtain ⟨colX, hRX, hcopy⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopy hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hcu : cu = cellu := Option.some.inj (hL.hcu.symm.trans hcellu)
  subst hcu
  -- `pe` is the node `k + 1` of `B`
  have himg := leg_image hS hj hL
  rw [heq, mapColumn_of_ge (le_refl _), boundary_eq hcrx hipos] at himg
  have hpecol : pe.column = ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) := by
    rw [(highestAtMost_spec hL.hpe).1, himg]
  obtain ⟨_, _, _, _, _, hBc⟩ := bcol hd hm hesB
  have hpe_max : ∀ k' (hk' : k' < esB.length), esB[k'].1.row ≤ es[j].1.row → k' ≤ k := by
    intro k' hk' hle
    obtain ⟨cb, hcb, hcbr, _⟩ := hBc k' hk'
    have := hAM_max hL.hpe (q := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k' + 1⟩) (by rw [himg])
      (by show 0 < k' + 1; omega) hcb (by rw [hcbr, hrowu]; exact stored_mono hle)
    show k' ≤ k
    have h2 : (⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k' + 1⟩ : Ref).index ≤ pe.index := this
    simp only at h2
    omega
  have hpe_le : esB[k].1.row ≤ es[j].1.row := by
    have hpeq : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k + 1⟩ := ref_eq_of hpecol hpek
    obtain ⟨cb, hcb, hcbr, _⟩ := hBc k hk
    have hcpe : cpe = cb := by
      have := hL.hcpe
      rw [hpeq, hcb] at this
      exact (Option.some.inj this).symm
    have := hAM_le hL.hpe hL.hcpe
    rw [hcpe, hcbr, hrowu] at this
    exact stored_le_iff.mp this
  -- the origin `ν` of `pe`
  obtain ⟨_, hν1, _⟩ := bsrc hesB hk
  have hcν1 : (1 : Row) ≤ cν.row := one_le_row hV hcν hν1
  -- facts on `pa` and the origin of `u`
  obtain ⟨hpacol', hpa1, _⟩ := highestAtMost_spec hL.hpa
  have hpacol : pa.column = ρ.cr := by rw [hpacol', heq]
  have hpamem : (pa, cpa) ∈ realNodes M ρ.cr := by
    have := mem_realNodes_of_cell' hL.hcpa hpa1
    rwa [hpacol] at this
  have hpa_le : cpa.row ≤ cv.row := hAM_le hL.hpa hL.hcpa
  obtain ⟨_, hsrc1, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hL.hcv hsrc1
  have hcpa1 : (1 : Row) ≤ cpa.row := one_le_row hV hL.hcpa (by omega)
  have hRpa : SRCmp.RootRow M ρ.cr (official cpa.row) := ⟨(pa, cpa), hpamem, rfl⟩
  -- (a) `row pa ≤ row ν`
  have ha : cpa.row ≤ cν.row := by
    have hoff : official cpa.row ≤ official cv.row := Recon.official_mono hcpa1 hpa_le
    have hle1 : official cpa.row ≤ es[j].1.row := by
      have hc := ((hCu _ hRpa).1 hnc)
      rcases lt_or_eq_of_le hoff with hlt | heq'
      · exact (hc.1 hlt).le
      · exact le_of_eq (hc.2.1 heq').symm
    have hoffν : official cpa.row ≤ official cν.row := by
      by_cases hup : official t.row ≤ official cpa.row
      · exfalso
        obtain ⟨k', hk', hup', hrow'⟩ := upper_cover hesB' pa cpa
          (by simp [upperColumn, bctx, ctxAt, hpacol]) (by omega) hL.hcpa hup
        have h1 := hpe_max k' hk' (by rw [hrow']; exact hle1)
        have h2 := lower_before_upper hesB' hk hk' hlow hup'
        omega
      · obtain ⟨k', hk', hrow'⟩ := ChainCorr.LegJump.boundaryRootRows s n D M out ρ R t hd i
          hipos hS.iLt esB hesB (pa, cpa) hpamem (lt_of_not_ge hup)
        have h1 := hpe_max k' hk' (by rw [hrow']; exact hle1)
        have hrowk : official cpa.row ≤ esB[k].1.row := by
          have := emit_le hd hm hesB hk' hk h1
          rw [hrow'] at this
          exact this
        by_contra hn
        have hlt : official cν.row < official cpa.row := lt_of_not_ge hn
        have hpe_lt : esB[k].1.row < official cpa.row := by
          cases hcut : cutOrigin esB[k].2
          · exact ((hCB _ hRpa).1 hcut).2.2 hlt
          · exact ((hCB _ hRpa).2 hcut).2 hlt
        exact absurd hrowk (not_le.mpr hpe_lt)
    by_contra hn
    exact absurd (Recon.official_strictMono hcν1 (lt_of_not_ge hn)) (not_lt.mpr hoffν)
  -- (b) no node of `cr` strictly between `σ` and `row ν`
  have hbmax : ∀ jj cc, cell? M ⟨ρ.cr, jj⟩ = some cc → 0 < jj → cc.row ≤ cν.row →
      jj ≤ pa.index := by
    intro jj cc hcc hjj hccle
    have hle : cc.row ≤ cv.row := by
      by_contra hn
      have hcc1 : (1 : Row) ≤ cc.row := one_le_row hV hcc (by show 1 ≤ jj; omega)
      have hσ : official cv.row < official cc.row :=
        Recon.official_strictMono hcv1 (lt_of_not_ge hn)
      have hccν : official cc.row ≤ official cν.row := Recon.official_mono hcc1 hccle
      have hRc : SRCmp.RootRow M ρ.cr (official cc.row) :=
        ⟨(⟨ρ.cr, jj⟩, cc), mem_realNodes_of_cell' hcc (by show 1 ≤ jj; omega), rfl⟩
      have hu_lt : es[j].1.row < official cc.row := ((hCu _ hRc).1 hnc).2.2 hσ
      have hpe_ge : official cc.row ≤ esB[k].1.row := by
        cases hcut : cutOrigin esB[k].2
        · have hc := (hCB _ hRc).1 hcut
          rcases lt_or_eq_of_le hccν with hlt | heq'
          · exact (hc.1 hlt).le
          · exact le_of_eq (hc.2.1 heq').symm
        · exact (((hCB _ hRc).2 hcut).1 hccν).le
      exact absurd (lt_of_le_of_lt hpe_ge (lt_of_le_of_lt hpe_le hu_lt)) (lt_irrefl _)
    exact hAM_max hL.hpa (q := ⟨ρ.cr, jj⟩) (by simp [heq]) hjj hcc hle
  exact highestAtMost_of_max hpacol hpa1 hL.hcpa ha hbmax

/-- **`OriginReach` holds.** -/
theorem originReach : OriginReach :=
  originReach_of_lower (originLower_of_parts paLookup x0Reach)

end OmegaY.Official.Classification.Proofs.ChainCorr.SRFixPa

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRFixPa.paLookup
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRFixPa.originReach
