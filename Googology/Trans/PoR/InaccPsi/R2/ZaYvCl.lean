import Googology.Trans.PoR.InaccPsi.R2.ZaThCl
import Googology.Trans.PoR.InaccPsi.R2.YvWit

/-!
# The open statement of round 130 (`Yv.YvCl`, skeleton leaf `skYvCl`) from the moving-level FRAG

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Yv.YvCl S κ b c m F Ψ` asks the moving-level hull clause at every level `1 ≤ q`, `Ω₁·q < θ`.  Under `Za.ZaDlSC` the
FRAG map of `Za.zaFragXe` has it: at levels `q ≥ B₂` it is `Za.ZaCl`; at levels `Ω₁·q < B₂` it is the term clause
`Vl.VlCl` at the term `thc q r` of `Un.UnC` (node conditions from `Vl.vl_lv_mem`, `R2.vzT_add`, `Za.za_lt_vt_all`) with
the level clause `Vl.VlLC` (`Ω₁·vq Ψ q = vcSub Ψ (Ω₁·q) = yvSub Ψ (Ω₁·q)`).

* `za_yvCl` (**`ZaDlSC ⇒` FRAG with `Vl.VlFragConcl ∧ Yv.YvCl`**: the skeleton leaf `skYvCl`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tr Googology.Trans.PoR.InaccPsi.R2.Uh
  Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl
open Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Xj Googology.Trans.PoR.InaccPsi.R2.Yv
  Googology.Notation.InaccPsi

variable {S : InaccSeq.{0}}

/-- **`skYvCl` under `ZaDlSC`**: a FRAG map with `Vl.VlFragConcl` and the moving-level hull clause `Yv.YvCl` at every
level `1 ≤ q`, `Ω₁·q < θ`. -/
theorem za_yvCl (hDl : ZaDlSC) {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m)
    (hc : Chain κ c m) (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) :
    ∃ Ψ, VlFragConcl κ b c m F Ψ ∧ YvCl S κ b c m F Ψ := by
  obtain ⟨Ψ, ⟨hV, -⟩, hZ⟩ := zaFragXe (S := S) hDl hb hc F hF
  refine ⟨Ψ, hV, ?_⟩
  obtain ⟨-, hU, hLC, -⟩ := hV
  intro k hk q r hq1 hqθ hlvF hlvT hz hw hρ1 hl hzl hlT hzT hxF hs
  have hbkU := hb.ups k hk
  have hbE : InE (b k) := upsPt_inE hbkU.1
  have hBk : Bases κ (b k) := ⟨hb.kap, hbE, hb.bot k hk, hbkU.2⟩
  rcases lt_or_ge q Uc.ucB with hqB' | hqB'
  · have hqB : Om1 * q < Uc.ucB := Xe.xe_mul_lt_B hqB'
    have hVT : Vc.VcLv (· ∈ Tset (b k)) (Om1 * q) := by
      cases hlvT with
      | low _ hV => exact hV
      | om hs' _ e' => exact absurd hqB (not_lt.2 (e' ▸ yv_Om_ge_B hs'))
      | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
      | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
      | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
    have hVF : Vc.VcLv (fun p => p ∈ F ∨ p < κ) (Om1 * q) := by
      cases hlvF with
      | low _ hV => exact hV
      | om hs' _ e' => exact absurd hqB (not_lt.2 (e' ▸ yv_Om_ge_B hs'))
      | cnf _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
      | veb _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
      | atom _ _ _ _ hB' => exact absurd hqB (not_lt.2 hB')
    have hgm : Om1 * q ∈ Tset (b k) := vl_lv_mem hbE hbkU.2 hq1 hqB hVT
    have hρT : UnT.ev (b k) r ∈ Tset (b k) := viMem hBk r hlT hw hz
    have hmem : Om1 * q + UnT.ev (b k) r ∈ Tset (b k) := vzT_add hbE hbkU.2 hgm hρT
    have hrb := za_lt_vt_all (S := S) hbE hbkU.2 hq1 hqθ hρT hρ1 hmem
    have hZW : ZW (b k) (UnT.thc q r) := ⟨⟨hq1, hqB, hgm, hmem, hrb⟩, hz⟩
    have hWF : WFr (b k) (UnT.thc q r) := ⟨hw, hρ1⟩
    obtain ⟨e1, w1, w2⟩ := hU k hk (UnT.thc q r) hZW hWF hl ⟨hVF, hzl⟩ hlT ⟨hVT, hzT⟩ hxF hs
    obtain ⟨e2, -⟩ := hLC q hq1 hqB hVF
    have hsub : yvSub S Ψ (Om1 * q) = Om1 * vq Ψ q := by rw [yvSub_low Ψ hqB, e2]
    refine ⟨?_, w1.1, w2.2, w1.2⟩
    rw [hsub]; exact e1
  · obtain ⟨q', e1, -, -, -, -, -, -, hnode, w1, w2, w3⟩ :=
      hZ k hk q r hq1 hqB' hqθ hlvF hlvT hz hw hρ1 hl hzl hlT hzT hxF hs
    exact ⟨by rw [e1]; exact hnode, w1, w2, w3⟩

end Googology.Trans.PoR.InaccPsi.R2.Za
