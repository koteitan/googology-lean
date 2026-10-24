import Googology.Trans.PoR.InaccPsi.R2.GmLd

/-!
# THE UNION AND THE LADDER READ THEIR ATOMS, for the codes of a code system `K`

Port of `R2.GiUnif` to the code systems `GmCS` of `R2.GmAt`, whose bound may pass `Γ_{Ω₁+1}` (codes may contain
atoms), and, for the layers, to offsets below `Γ_{x+2}` (`R2.GmGq`, `R2.GmU`); the proofs are those of `R2.GiUnif`.

`R2.GhUnif` (first part) for an arbitrary code system `K : GmCS` (`R2.GmAt`):

* `gmLim_top`, `gmLim_poly` (the term-offset ladder limit `Ge.geqLimB` reads `cQs c`, with terms below it),
  `GmPolyG.mono`;
* `gmU_codes` (**THE UNION READS THE LIMIT ATOM**, for every union step `GmUF` (`R2.GmU`): if the members read atoms
  `Γ_{Ω₁+1+C_i}` below `Γ_{Ω₁+1+c_L}` (`c_L ≤ K.B` a limit) and every smaller atom code with gate below `Z` is at most
  some `C_i` with side gate below `Z`, then the union top reads `Γ_{Ω₁+1+c_L}` and the union has terms for every code
  below it).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Xt Lu
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

variable {K : GmCS}

section Lim

variable {B : GdB} {c : Ordinal.{0}} (hc : ∀ Z, SC Z → B.g < Z → GxCl Z (K.At Z) c) (hcO : Om 1 ≤ c)
  (hKE : ∀ y, SC y → y < Om 1 → B.g < y → B.K.E y = gxTh y (K.At y) c) {e : Ordinal.{0} → Ordinal.{0}}
  (H : GeqH B e)
include hc hKE H

/-- **The term-offset limit top reads the code `cQs c`**: `ϑʸ(Ω₁·Ω₁ + e(y)) = Θ_y(cQs c)` above the gate. -/
theorem gmLim_top {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) (hg : B.g < y) :
    gq (e y) y = gxTh y (K.At y) (cQs c) := by
  rw [geq_sup H (gg_SC_eps hy) (lp_y1 hy1) hg, cQs, gcTh_iSup]
  exact iSup_congr fun n => gmTop_th hc hKE n y hy hy1 hg

include hcO in
/-- **The term-offset limit layer has terms for every code below `cQs c`.** -/
theorem gmLim_poly (hKP : GmPolyG K B.K.sys c) : GmPolyG K (geqUSys B e H) (cQs c) := by
  intro Z d hg hd hdE
  obtain ⟨n, hn⟩ := cQs_lt hdE
  obtain ⟨s, hs⟩ := gmPoly hc hcO hKE hKP n Z d hg hd hn
  exact ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1.1, (hs y hy hy1 hZy).2⟩⟩

end Lim

theorem GmPolyG.mono {g g' E : Ordinal.{0}} {X : GdSys g} (hP : GmPolyG K X E) (h : g ≤ g') :
    GmPolyG K (X.mono h) E := fun Z d hg hd hdE => hP Z d (h.trans_lt hg) hd hdE

/-! ## The union reads the limit atom -/

/-- **THE UNION READS THE LIMIT ATOM**: for a union step `F` whose members read the atoms `Γ_{Ω₁+1+C_i}` (with terms
below them), `C_i < c_L` (`c_L` a limit), and every atom code `b < c_L` with gate below a strongly critical `Z` above
`g` lies below some `C_i` with side gate below `Z`: the union top reads `Γ_{Ω₁+1+c_L}`, with terms below it. -/
theorem gmU_codes {g : Ordinal.{0}} (F : GmUF g) (C : F.I → Ordinal.{0}) {cL : Ordinal.{0}} (hcL : IsSuccLimit cL)
    (hcLB : cL ≤ K.B)
    (hK : ∀ i y, SC y → y < Om 1 → F.gi i < y → (F.K i).K.E y = gxTh y (K.At y) (gcG (C i)))
    (hKP : ∀ i, GmPolyG K (F.K i).K.sys (gcG (C i))) (hCle : ∀ i, C i ≤ cL)
    (hcov : ∀ b, b < cL → ∀ Z, SC Z → g < Z → K.gt b < Z → ∃ i, F.gi i < Z ∧ b ≤ C i) :
    (∀ y, SC y → y < Om 1 → g < y → (gmLimB F).K.E y = gxTh y (K.At y) (gcG cL)) ∧
      GmPolyG K (gmLimB F).K.sys (gcG cL) := by
  refine ⟨fun y hy hy1 hgy => ?_, ?_⟩
  · have hyE := gg_SC_eps hy
    have hy1' := lp_y1 hy1
    show gq (F.l y) y = _
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdlt => ?_)
    · obtain ⟨ν, hν, hvν⟩ := gm1_lt_lim_iff hyE hy1' (F.lim y hyE hy1' hgy) (F.l_lt y hyE hy1' hgy) v hv
      obtain ⟨i, hi, hνi⟩ := F.cof y hyE hy1' hgy ν hν
      calc v < gq ν y := hvν
        _ ≤ gq (F.o i y) y := gm1_mono hyE hy1' (F.o_lt0 hyE hy1' hgy hi) hνi
        _ = (F.K i).K.E y := (F.E_eq i y hyE hy1' hi).symm
        _ = gxTh y (K.At y) (gcG (C i)) := hK i y hy hy1 hi
        _ ≤ gxTh y (K.At y) (gcG cL) := gxTh_mono (gcG_le (hCle i))
    · obtain ⟨b, hb, hgb, hdb⟩ := gmCl_lt_G hy hy1.le hcL hcLB hd hdlt
      obtain ⟨i, hi, hbi⟩ := hcov b hb y hy hgy hgb
      calc gxTh y (K.At y) d < gxTh y (K.At y) (gcG b) := gxTh_lt hd hdb
        _ ≤ gxTh y (K.At y) (gcG (C i)) := gxTh_mono (gcG_le hbi)
        _ = (F.K i).K.E y := (hK i y hy hy1 hi).symm
        _ = gq (F.o i y) y := F.E_eq i y hyE hy1' hi
        _ < gq (F.l y) y := gm1_lt hyE hy1' (F.l_lt y hyE hy1' hgy) (F.o_lt i y hyE hy1' hgy hi)
  · refine gmPoly_of_SC _ _ ((gmUSys F).cst 0) fun Z hZ hZ1 hgZ d hd hdE => ?_
    obtain ⟨b, hb, hgb, hdb⟩ := gmCl_lt_G hZ hZ1.le hcL hcLB hd hdE
    obtain ⟨i, hi, hbi⟩ := hcov b hb Z hZ hgZ hgb
    obtain ⟨s, hs⟩ := hKP i Z d ((F.g_le i).trans_lt hi) hd (hdb.trans_le (gcG_le hbi))
    exact ⟨⟨i, s⟩, fun y hy hy1 hZy => ⟨⟨hi.trans_le hZy, (hs y hy hy1 hZy).1⟩, (hs y hy hy1 hZy).2⟩⟩

/-- **THE UNION READS THE LIMIT ATOM**, for a union step of `R2.GhU` (offsets below `Γ_{x+1}`): for a union step
`F` whose members read the atoms `Γ_{Ω₁+1+C_i}` (with terms
below them), `C_i < c_L` (`c_L` a limit), and every atom code `b < c_L` with gate below a strongly critical `Z` above
`g` lies below some `C_i` with side gate below `Z`: the union top reads `Γ_{Ω₁+1+c_L}`, with terms below it. -/
theorem gmU_codesH {g : Ordinal.{0}} (F : GhUF g) (C : F.I → Ordinal.{0}) {cL : Ordinal.{0}} (hcL : IsSuccLimit cL)
    (hcLB : cL ≤ K.B)
    (hK : ∀ i y, SC y → y < Om 1 → F.gi i < y → (F.K i).K.E y = gxTh y (K.At y) (gcG (C i)))
    (hKP : ∀ i, GmPolyG K (F.K i).K.sys (gcG (C i))) (hCle : ∀ i, C i ≤ cL)
    (hcov : ∀ b, b < cL → ∀ Z, SC Z → g < Z → K.gt b < Z → ∃ i, F.gi i < Z ∧ b ≤ C i) :
    (∀ y, SC y → y < Om 1 → g < y → (ghLimB F).K.E y = gxTh y (K.At y) (gcG cL)) ∧
      GmPolyG K (ghLimB F).K.sys (gcG cL) := by
  refine ⟨fun y hy hy1 hgy => ?_, ?_⟩
  · have hyE := gg_SC_eps hy
    have hy1' := lp_y1 hy1
    show gq (F.l y) y = _
    refine le_antisymm (le_of_forall_lt fun v hv => ?_) (gxTh_le_of fun d hd hdlt => ?_)
    · obtain ⟨ν, hν, hvν⟩ := gf_lt_lim_iff hyE hy1' (F.lim y hyE hy1' hgy) (F.l_lt y hyE hy1' hgy) v hv
      obtain ⟨i, hi, hνi⟩ := F.cof y hyE hy1' hgy ν hν
      calc v < gq ν y := hvν
        _ ≤ gq (F.o i y) y := gfq_mono hyE hy1' (F.o_lt0 hyE hy1' hgy hi) hνi
        _ = (F.K i).K.E y := (F.E_eq i y hyE hy1' hi).symm
        _ = gxTh y (K.At y) (gcG (C i)) := hK i y hy hy1 hi
        _ ≤ gxTh y (K.At y) (gcG cL) := gxTh_mono (gcG_le (hCle i))
    · obtain ⟨b, hb, hgb, hdb⟩ := gmCl_lt_G hy hy1.le hcL hcLB hd hdlt
      obtain ⟨i, hi, hbi⟩ := hcov b hb y hy hgy hgb
      calc gxTh y (K.At y) d < gxTh y (K.At y) (gcG b) := gxTh_lt hd hdb
        _ ≤ gxTh y (K.At y) (gcG (C i)) := gxTh_mono (gcG_le hbi)
        _ = (F.K i).K.E y := (hK i y hy hy1 hi).symm
        _ = gq (F.o i y) y := F.E_eq i y hyE hy1' hi
        _ < gq (F.l y) y := gfq_lt hyE hy1' (F.l_lt y hyE hy1' hgy) (F.o_lt i y hyE hy1' hgy hi)
  · refine gmPoly_of_SC _ _ ((ghUSys F).cst 0) fun Z hZ hZ1 hgZ d hd hdE => ?_
    obtain ⟨b, hb, hgb, hdb⟩ := gmCl_lt_G hZ hZ1.le hcL hcLB hd hdE
    obtain ⟨i, hi, hbi⟩ := hcov b hb Z hZ hgZ hgb
    obtain ⟨s, hs⟩ := hKP i Z d ((F.g_le i).trans_lt hi) hd (hdb.trans_le (gcG_le hbi))
    exact ⟨⟨i, s⟩, fun y hy hy1 hZy => ⟨⟨hi.trans_le hZy, (hs y hy hy1 hZy).1⟩, (hs y hy hy1 hZy).2⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Gm
