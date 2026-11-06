import Googology.Trans.PoR.InaccPsi.R2.VaAt
import Googology.Trans.PoR.InaccPsi.R2.VaDir

/-!
# VaDir2: `ZbDirect S B₂` — EVERY LAYER `c < B₂`, UNCONDITIONAL

`B₂` (the least fixed point of `Γ` above `B_Γ`) is the supremum of the tower `B_Γ + 1, Γ(B_Γ+1), Γ(Γ(B_Γ+1)), …`
(`Ordinal.nfp`), whose members are atoms, codes over `K` (gate below `K`, `Va.va_gate`); the step of the system
`Va.VaGood` at each of them gives `ZbDirect S` up to the next `ε`-number (`Zm.ZmDS.direct`).

* `vaTw2`, `vaTw2_iter`, `vaTw2_lt`, `vaTw2_gt`, `vaTw2_cof`, `vaTw2_cl`;
* `vaDirectB2` (**`ZbDirect S B₂`, UNCONDITIONAL**), `vaUVB2`, `vaLayB2` (**the conclusions of `skLayLoFix` and
  `skLayHiFix` at every layer `c < B₂`**).

No new axiom.  New definition: `vaTw2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

/-- **The tower** `B_Γ + 1, Γ(B_Γ+1), Γ(Γ(B_Γ+1)), …`. -/
noncomputable def vaTw2 : ℕ → Ordinal.{0}
  | 0 => tfBG + 1
  | n + 1 => gamma (vaTw2 n)

theorem vaTw2_iter : ∀ n : ℕ, gamma^[n] (tfBG + 1) = vaTw2 n
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply', vaTw2_iter n]; rfl

theorem vaTw2_lt : ∀ n, vaTw2 n < vaB2
  | 0 => (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC (by
      have := Lq.lq_gamma_SC vaB2; rwa [vaB2_fix] at this))).add_one_lt va_BG_lt_B2
  | n + 1 => by
    show gamma (vaTw2 n) < vaB2
    rw [← vaB2_fix]; exact gamma_lt_gamma.2 (vaTw2_lt n)

theorem vaTw2_gt : ∀ n, tfBG < vaTw2 n
  | 0 => lt_add_one _
  | n + 1 => (vaTw2_gt n).trans_le (isNormal_gamma.strictMono.le_apply)

theorem vaTw2_cof {B : Ordinal.{0}} (hB : B < vaB2) : ∃ n, B < vaTw2 n := by
  unfold vaB2 at hB
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hB
  exact ⟨n, by rw [← vaTw2_iter]; exact hn⟩

theorem vaTw2_cl {Z : Ordinal.{0}} (hZ : 0 < Z) : ∀ n, TlCl Z (vaTw2 n)
  | 0 => TlCl.add (zbBG_tl hZ) (TlCl.one hZ)
  | n + 1 => TlCl.gam hZ (vaTw2_cl hZ n) (tfBG_gt.trans (vaTw2_gt n))

/-- **`ZbDirect S B₂`, UNCONDITIONAL.** -/
theorem vaDirectB2 (S : InaccSeq.{0}) : ZbDirect S vaB2 := by
  intro B hB1 hB2
  obtain ⟨n, hn⟩ := vaTw2_cof hB2
  set e := vaTw2 (n + 1) with hedef
  have hne : vaTw2 n < e := by
    show vaTw2 n < gamma (vaTw2 n)
    refine lt_of_le_of_ne isNormal_gamma.strictMono.le_apply fun h => ?_
    exact absurd (vaTw2_lt n) (not_lt.2 (va_B2_min (vaTw2_gt n) h.symm))
  have heSC : SC e := Lq.lq_gamma_SC _
  have heE : InE e := Low.opow_eq_self_of_SC heSC
  have heB : tfBG ≤ e := (vaTw2_gt (n + 1)).le
  have heU : e < vaB2 := vaTw2_lt (n + 1)
  obtain ⟨M, hE, hEg, -, -, -, hBB, hDD⟩ := vaGood_all2 e heE heB heU
  have hK : SC (Td.tdK S) := Td.tdK_SC
  have hK1 : Td.tdK S ≤ Om1 := by rw [Br.Om1_eq]; exact (Td.tdK_lt_Om1 (S := S)).le
  have hge : yrG e < Td.tdK S := va_gate hK hK1 e (vaTw2_cl hK.1 (n + 1)) heU
  have hgK : M.step.Eg < Td.tdK S := by
    rw [ZmDS.step_Eg, hEg]
    refine max_lt (omega0_lt_inE (Low.opow_eq_self_of_SC hK)) ?_
    rw [← yrG_base heE (va_G_le_BG.trans heB)]; exact hge
  have hBM : B < M.step.E := by
    show B < eN M.E
    rw [hE]; exact (hn.trans hne).trans (lt_eN e)
  have hGM : tfBG < M.step.E := by
    show tfBG < eN M.E
    rw [hE]; exact heB.trans_lt (lt_eN e)
  exact M.step.direct hBB hDD S hGM hgK M.step_gc0 B hB1 hBM

/-- **UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ_{Ω₁+1+B}·ω)`, every `B < B₂`.** -/
theorem vaUVB2 (S : InaccSeq.{0}) {B l : Ordinal.{0}} (hB : B < vaB2) (hr : CdRange S l)
    (hl : l < iota S (gcG B * ω)) : CdUpper S l ∧ CdLower S l ∧ CdCapV S l :=
  zbUV_of_direct (vaDirectB2 S) l hr B hB hl

/-- **EVERY LAYER `c < B₂`**: the conclusions of `skLayLoFix` and `skLayHiFix` at `c`. -/
theorem vaLayB2 (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : c < vaB2) :
    ∀ l, CdRange S l → (∃ ℓ, ℓ < gcG (c + 1) ∧ l < iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      CdUpper S l ∧ CdLower S l ∧ CdCapV S l := by
  have hB2E : InE vaB2 := Low.opow_eq_self_of_SC (by have := Lq.lq_gamma_SC vaB2; rwa [vaB2_fix] at this)
  have hc1 : c + 1 < vaB2 := (ev_isSuccLimit_of_inE hB2E).add_one_lt hc
  have hle : gcG (c + 1) ≤ vaB2 := by
    rw [tf_gcG, ← vaB2_fix]
    refine gamma_le_gamma.2 ?_
    have hOB : Om1 + 1 + vaB2 = vaB2 := gl_absorb hB2E (tfBG_gt.trans va_BG_lt_B2)
    rw [← hOB]; exact (add_le_add_iff_left _).2 hc1.le
  exact zbLay_of_direct (fun B h1 h2 => vaDirectB2 S B h1 (h2.trans_le hle))

end Googology.Trans.PoR.InaccPsi.R2.Va
