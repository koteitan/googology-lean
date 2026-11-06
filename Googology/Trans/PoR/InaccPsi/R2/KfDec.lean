import Googology.Trans.PoR.InaccPsi.R2.KeCtx

/-!
# Kf: THE `W`-NORMAL FORM OF THE MEMBERS OF `D` (leading term and last term)

`W^x = leWe x = ω^{Ω₂·x}`, `Ω^x = leOe x`, `T = Vb.vbT S λ`, `Θ`, `D = Vb.VbD S λ`.  Every closure `Cl(a, b)` is
closed under `log_ω`, the quotient and the remainder by `ω^p` once `p` is a member (`Le.leLog_mem`, `Vh.vhC_div`),
so the `W`-normal form of a member of `D` stays in `D`:

* `kfMem` (the exponent `g = log_ω E / Ω₂`, the coefficient `E / W^g` and the remainder `E % W^g` of a member are
  members),
* `kfDec` (**THE LEADING TERM**: a nonzero `E ∈ D` is `W^g·u + r`, `g, r ∈ D`, `u` a code with `0 < u < Ω₂`,
  `r < W^g`, `g ≤ E`, and `T E = Ω^{T g}·Θu + T r`),
* `kfLast` (**THE LAST TERM**: a nonzero `b ∈ D` is `β + W^E·γ`, `β, E ∈ D`, `γ` a code with `0 < γ < Ω₂`,
  `W^{E+1} ∣ β`, and `T b = T β + Ω^{T E}·Θγ`; induction on `b` through the leading term).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zx

variable {S : InaccSeq.{0}}

/-- **The `W`-leading data of a member are members.** -/
theorem kfMem {a b E : Ordinal.{0}} (hE : E ∈ S.CSet a b) :
    log ω E / Om (1 + 1) ∈ S.CSet a b ∧ E / leWe (log ω E / Om (1 + 1)) ∈ S.CSet a b ∧
      E % leWe (log ω E / Om (1 + 1)) ∈ S.CSet a b := by
  have hlog : log ω E ∈ S.CSet a b := leLog_mem hE
  have hεΩ : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC
  have hg : log ω E / Om (1 + 1) ∈ S.CSet a b := by
    have h := (Vh.vhC_div _ hlog (Om (1 + 1))).2.2 (mxOm2_mem _ _); rwa [hεΩ] at h
  have hp : Om (1 + 1) * (log ω E / Om (1 + 1)) ∈ S.CSet a b := ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hg
  exact ⟨hg, (Vh.vhC_div E hE _).2.2 hp, (Vh.vhC_div E hE _).2.1⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE LEADING TERM** `E = W^g·u + r` of a nonzero member of `D`. -/
theorem kfDec {E : Ordinal.{0}} (hED : VbD S l E) (hE0 : E ≠ 0) :
    ∃ g u r, E = leWe g * u + r ∧ VbD S l g ∧ GxCl (upsilon l) (ldAtR S l) u ∧ 0 < u ∧ u < Om (1 + 1) ∧
      u ∈ S.CSet (Om ω) (ConjT.th S) ∧ VbD S l r ∧ r < leWe g ∧ g ≤ E ∧ leWe g ≤ E ∧
      vbT S l E = leOe (vbT S l g) * gxTh (upsilon l) (ldAtR S l) u + vbT S l r := by
  set g := log ω E / Om (1 + 1) with hgdef
  set u := E / leWe g with hudef
  set r := E % leWe g with hrdef
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have e1 : E = leWe g * u + r := (Ordinal.div_add_mod E (leWe g)).symm
  have hWE : leWe g ≤ E := by
    unfold leWe
    exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le (log ω E) _)).trans (opow_log_le_self ω hE0)
  have hlt : E < leWe g * Om (1 + 1) := by
    rw [← leWe_succ]
    unfold leWe
    refine (lt_opow_succ_log_self one_lt_omega0 E).trans_le (opow_le_opow_right omega0_pos ?_)
    have h := Ordinal.lt_mul_succ_div (log ω E) hΩ0
    rw [Order.succ_eq_add_one] at h ⊢
    exact Order.add_one_le_of_lt h
  have hu2 : u < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlt
  have hu0 : 0 < u := (Ordinal.div_pos hW0).2 hWE
  have hr : r < leWe g := Ordinal.mod_lt E hW0
  have hgE : g ≤ E := by
    refine le_trans ?_ hWE
    unfold leWe
    exact (Ordinal.right_le_opow g one_lt_omega0).trans
      (opow_le_opow_right omega0_pos (Ordinal.le_mul_right g ldOm2_SC.1))
  have hmH := kfMem hED.1
  have hmC := kfMem hED.2.1
  have hgD : VbD S l g := ⟨hmH.1, hmC.1, hgE.trans_lt hED.2.2⟩
  have hrD : VbD S l r := ⟨hmH.2.2, hmC.2.2, (Ordinal.mod_le E _).trans_lt hED.2.2⟩
  have huc : GxCl (upsilon l) (ldAtR S l) u := (ldHull_iff hl hX hu2).1 hmH.2.1
  refine ⟨g, u, r, e1, hgD, huc, hu0, hu2, hmC.2.1, hrD, hr, hgE, hWE, ?_⟩
  conv_lhs => rw [e1]
  exact Vh.vhT_cnfW hl hX hgD hrD hmH.2.1 hu2

/-- **THE LAST TERM** `b = β + W^E·γ` of a nonzero member of `D`, `W^{E+1} ∣ β`. -/
theorem kfLast : ∀ b, VbD S l b → b ≠ 0 →
    ∃ β E γ, b = β + leWe E * γ ∧ VbD S l β ∧ VbD S l E ∧ GxCl (upsilon l) (ldAtR S l) γ ∧ 0 < γ ∧
      γ < Om (1 + 1) ∧ leWe (E + 1) ∣ β ∧
      vbT S l b = vbT S l β + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) γ := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hbD hb0
  obtain ⟨g, u, r, e1, hgD, huc, hu0, hu2, huC, hrD, hr, -, -, -⟩ := kfDec hl hX hbD hb0
  have huH : u ∈ cdHull S l := (ldHull_iff hl hX hu2).2 huc
  have hgu : VbD S l (leWe g * u) :=
    ⟨leMulWe_mem hgD.1 huH, leMulWe_mem hgD.2.1 huC, (le_self_add.trans_eq e1.symm).trans_lt hbD.2.2⟩
  have hTgu : vbT S l (leWe g * u) = leOe (vbT S l g) * gxTh (upsilon l) (ldAtR S l) u := by
    have h := Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) huH hu2
    rwa [add_zero, Vh.vhT_zero hl hX, add_zero] at h
  rcases eq_or_ne r 0 with hr0 | hr0
  · refine ⟨0, g, u, by rw [e1, hr0, add_zero, zero_add], Xi.xiD_zero l, hgD, huc, hu0, hu2, dvd_zero _, ?_⟩
    rw [Vh.vhT_zero hl hX, zero_add]
    conv_lhs => rw [e1, hr0, add_zero]
    exact hTgu
  · have hrb : r < b :=
      hr.trans_le ((Ordinal.le_mul_left (leWe g) hu0).trans (le_self_add.trans_eq e1.symm))
    obtain ⟨β', E, γ, er, hβ'D, hED, hγc, hγ0, hγ2, hdv, hTr⟩ := IH r hrb hrD hr0
    have hEg : E < g := by
      by_contra hc
      push Not at hc
      have h1 : leWe g ≤ r := (leWe_mono hc).trans ((Ordinal.le_mul_left (leWe E) hγ0).trans
        (le_add_self.trans_eq er.symm))
      exact absurd hr (not_lt.2 h1)
    have hdvβ : leWe (E + 1) ∣ leWe g * u + β' :=
      dvd_add ((leWe_dvd (Order.add_one_le_of_lt hEg)).trans (dvd_mul_right _ _)) hdv
    have hβD : VbD S l (leWe g * u + β') :=
      ⟨CSet.add_mem hgu.1 hβ'D.1, CSet.add_mem hgu.2.1 hβ'D.2.1, vkOmW.1.isPrincipal hgu.2.2 hβ'D.2.2⟩
    refine ⟨leWe g * u + β', E, γ, by rw [e1, er, add_assoc], hβD, hED, hγc, hγ0, hγ2, hdvβ, ?_⟩
    calc vbT S l b = vbT S l (leWe g * u + r) := by rw [← e1]
      _ = vbT S l (leWe g * u) + vbT S l r := Vh.vhT_add hl hX hgu hrD
      _ = vbT S l (leWe g * u) + (vbT S l β' + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) γ) := by
        rw [hTr]
      _ = vbT S l (leWe g * u + β') + leOe (vbT S l E) * gxTh (upsilon l) (ldAtR S l) γ := by
        rw [Vh.vhT_add hl hX hgu hβ'D, add_assoc]

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kf

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kf.kfLast
