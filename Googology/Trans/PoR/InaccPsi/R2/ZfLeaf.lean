import Googology.Trans.PoR.InaccPsi.R2.ZfInj

/-!
# The leaves of a node level lie in `T^{υ_{λ+h}}` and below the next `υ`-point (a2)

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

For a node `v = ϑᵗ(Ω₁·M + η)` (`1 ≤ M`, `Ω₁·M + η ∈ Tᵗ ∩ Ω₂`): every reading of the data of `M` lies below every
strongly critical `q ≥ v` (`R2.vdLevel_lt` for `M ≥ Ω₁`, the level itself below the value for countable `M`), so the
leaves of `Ω₁·M` lie below `q` (`Yv.yv_dat_iff`, `Za.za_lv_mul`).  With `q = Dl τ N` (strongly critical by
`Zf.zfDlSC`, in `Tᵗ`, above `v`: `Zf.zf_SC_above`) the leaves lie in `Tᵗ ∩ Ω₁`, an initial segment, and so below the
next `υ`-point (`Za.za_lt_next`).

* `zf_lev_lv` (**the leaves of `Ω₁·M` lie below every strongly critical `q ≥ v`, `q ≤ Ω₁`**), `zf_lv_T` (**the
  leaves of `Ω₁·M` lie in `Tᵗ` and below every `υ`-point `u > τ`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Yv

/-- **The leaves of `Ω₁·M` lie below every strongly critical `q ≥ ϑᵗ(Ω₁·M + η)`, `q ≤ Ω₁`.** -/
theorem zf_lev_lv (S : InaccSeq.{0}) {τ M η q : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : 1 ≤ M)
    (hη1 : η < Om1) (h : Om1 * M + η ∈ Tset τ) (h2 : Om1 * M + η < OmTwo) (hq : SC q) (hq1 : q ≤ Om1)
    (hvq : vt τ (Om1 * M + η) ≤ q) : YvLv S (· < q) (Om1 * M) := by
  have hθ : Om1 * M + η < ConjT.th S := uzTBound (S := S) τ hτ hτ1 _ h h2
  have hMθ' : Om1 * M < ConjT.th S := le_self_add.trans_lt hθ
  have hMθ : M < ConjT.th S := (Xe.xe_le_mul M).trans_lt hMθ'
  have hηT : η ∈ Tset τ := vzRem_T hτ hτ1 h h2 rfl (dvd_mul_right Om1 M) hη1
  have hOB : Om1 < Uc.ucB := (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B : Om1 < Uc.ucB)
  have hd : Vd.vdDat S M < q := by
    rcases lt_or_ge M Om1 with hM | hM
    · rw [Vd.vdDat_lt (hM.trans hOB), Uc.ucDat_small hM]
      have hMT := zf_lev_T hτ hτ1 hM hη1 h
      exact (Gl.glA_facts hτ hτ1 hM1 hMT hM hηT hη1).2.2.2.2.1.trans_le hvq
    · have hA := (vdLevel_lt hτ hτ1 hM (zf_dat_in S hτ hτ1 hM hη1 h h2) hηT hη1).1
      rcases lt_or_ge M Uc.ucB with hB | hB
      · rw [Vd.vdDat_lt hB]; exact (hA.1 hB).trans_le hvq
      · rw [Vd.vdDat_ge hB]; exact hA.2 S hB hMθ q hq hvq
  have hd' : Vd.vdD S 0 M < q := (Vd.vd_dat_test hq hq1).1 hd
  exact (Za.za_lv_mul hq hq1 hMθ').1 ((yv_dat_iff hq hq1 hMθ).1 hd')

/-- **The leaves of a node level lie in `Tᵗ` and below every `υ`-point `u > τ`.** -/
theorem zf_lv_T (S : InaccSeq.{0}) {τ M η u : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hM1 : 1 ≤ M)
    (hη1 : η < Om1) (h : Om1 * M + η ∈ Tset τ) (h2 : Om1 * M + η < OmTwo) (hu : UpsPt u) (hτu : τ < u) :
    YvLv S (fun p => p ∈ Tset τ ∧ p < u) (Om1 * M) := by
  obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hτ hτ1 h h2
  obtain ⟨q, hq, hqT, hq1, hvq⟩ := zf_SC_above S hτ hτ1 hvT hv1
  have hL := zf_lev_lv S hτ hτ1 hM1 hη1 h h2 hq hq1.le hvq.le
  refine hL.mono fun p hp => ?_
  have hpT : p ∈ Tset τ := zf_T_init hτ hτ1 hqT hq1 hp.le
  exact ⟨hpT, Za.za_lt_next hτ hτ1 hpT (hp.trans hq1) hτu hu⟩

end Googology.Trans.PoR.InaccPsi.R2.Zf
