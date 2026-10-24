import Googology.Trans.PoR.InaccPsi.R2.TfLev
import Googology.Trans.PoR.InaccPsi.R2.TcB
import Googology.Trans.PoR.InaccPsi.R2.MxAtB

/-!
# `B_n` on the codes below `B_Γ`: `B_n(ψ_{Ω₂}(c)) = ψ_{Ω₂}(B_n c)`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ψ_{Ω₂}(c) = S.psi c Ω₂`, `Γ_ν = gamma ν`, `B_Γ = Tf.tfBG` (the
least fixed point of `Γ` above `Ω₁`), `TfCl Z` the codes over `Z` with the atoms `Γ_ν = ψ_{Ω₂}(ν − (Ω₁ + 1))`
(`R2.TfCl`), `tfDat` their data (`R2.TfDat`).

* `tfBG_le_Om2`, `ti_BG_le_Omw`, `ti_BG_le_th`, `ti_BG_le_Pp` (`B_Γ ≤ Ω₂`, `≤ Ω_ω`, `≤ θ`, `≤ P′`),
  `ti_cl_lt` (**every code over `Z ≤ Ω₁` is below `B_Γ`**);
* `tiB_psi2` (**`B_n(ψ_{Ω₂}(c)) = ψ_{Ω₂}(B_n c)` for `c < B_Γ` in the domain of `B_n`**, and `ψ_{Ω₂}(c)` is in the
  domain: `c < ψ_{Ω₂}(c)`, so `c` is own for `ψ_{Ω₂}`, and `Mx.mxB_atom` applies), `tiB_Om1_succ`,
  `tiB_gamma` (**`B_n(Γ_ν) = Γ_{B_n ν}`** for an atom `Γ_ν < B_Γ`);
* `tiB_code` (**for a code `μ` over a strongly critical `x < L(ω)` with `B_n x ≤ Ω₁`: `μ` is in the domain of `B_n`,
  `B_n μ` is a code over `B_n x`, `B_n μ < B_Γ`, and `tfDat (B_n μ) = B_n (tfDat μ)`**), `tiB_cl`, `tiB_lt_BG`,
  `tiB_dat` (the case `x = c_{n+1}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Tf

variable {S : InaccSeq.{0}}

/-- `B_Γ ≤ Ω₂`. -/
theorem tfBG_le_Om2 : (tfBG : Ordinal.{0}) ≤ OmTwo := by
  have h := tfBG_lt_Om2.le
  rw [Om_of_ne_zero (by norm_num), one_add_one_eq_two] at h
  exact h

/-- `B_Γ ≤ Ω_ω`. -/
theorem ti_BG_le_Omw : (tfBG : Ordinal.{0}) ≤ Om ω :=
  tfBG_lt_Om2.le.trans (Om_le_Om.2 (by rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).le))

/-- `B_Γ ≤ θ = ψ_{Ω₂}(Ω_ω)`. -/
theorem ti_BG_le_th (S : InaccSeq.{0}) : (tfBG : Ordinal.{0}) ≤ ConjT.th S := by
  unfold ConjT.th
  rw [← tf_psi_BG S]
  exact (psi_mono (S := S) (InR_Om_succ 1) ti_BG_le_Omw).1

/-- `B_Γ ≤ P′`. -/
theorem ti_BG_le_Pp (S : InaccSeq.{0}) : (tfBG : Ordinal.{0}) ≤ Nc.ncPp S :=
  (ti_BG_le_th S).trans (Nc.ncTh_lt_Pp S).le

/-- **Every code over `Z ≤ Ω₁` is below `B_Γ`.** -/
theorem ti_cl_lt {Z : Ordinal.{0}} (hZ : Z ≤ Om1) {x : Ordinal.{0}} (hx : TfCl Z x) : x < tfBG := by
  induction hx with
  | small h => exact (h.trans_le hZ).trans tfBG_gt
  | om => exact tfBG_gt
  | add _ _ ihx ihy => exact tf_BG_indec.add_lt ihx ihy
  | phi _ _ ihx ihy => exact tfBG_SC.2 _ ihx _ ihy
  | gam _ _ ih => rw [← tfBG_fix]; exact gamma_lt_gamma.2 ih

/-- **`B_n(ψ_{Ω₂}(c)) = ψ_{Ω₂}(B_n c)`** for `c < B_Γ` in the domain of `B_n`; `ψ_{Ω₂}(c)` is in the domain. -/
theorem tiB_psi2 {n : ℕ} {c : Ordinal.{0}} (hD : MvD S c) (hc : c < tfBG) :
    MvD S (S.psi c (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi c (Om (1 + 1))) = S.psi (Bc.bcB S n c) (Om (1 + 1)) := by
  have hlt : c < S.psi c (Om (1 + 1)) := by rw [tf_psi S c hc.le]; exact tf_lt_gamma_shift hc
  exact Mx.mxB_atom hD (CSet.of_lt hlt)

/-- `Ω₁ + 1` is in the domain of `B_n` and fixed. -/
theorem tiB_Om1_succ {n : ℕ} : MvD S (Om1 + 1) ∧ Bc.bcB S n (Om1 + 1) = Om1 + 1 := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hD, hB⟩ := mvB_add (k := n) hDO (Rk.rk_one_D (S := S))
  rw [rj_Om1]
  exact ⟨hD, by rw [hB, hBO, Mw.mwB_one]⟩

/-- **`B_n(Γ_ν) = Γ_{B_n ν}`** for an atom `Γ_ν < B_Γ` (`Ω₁ < ν`) whose index offset `c = ν − (Ω₁ + 1)` is in the
domain of `B_n` with `B_n c < B_Γ`; then `ν` and `Γ_ν` are in the domain. -/
theorem tiB_gamma {n : ℕ} {ν : Ordinal.{0}} (h1 : Om1 < ν) (hB : gamma ν < tfBG)
    (hD : MvD S (ν - (Om1 + 1))) (hBc : Bc.bcB S n (ν - (Om1 + 1)) < tfBG) :
    MvD S ν ∧ MvD S (gamma ν) ∧ Bc.bcB S n ν = Om1 + 1 + Bc.bcB S n (ν - (Om1 + 1)) ∧
      Bc.bcB S n (gamma ν) = gamma (Bc.bcB S n ν) := by
  set c := ν - (Om1 + 1) with hcdef
  have hν : Om1 + 1 + c = ν := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt h1)
  have hνB : ν < tfBG := isNormal_gamma.strictMono.le_apply.trans_lt hB
  have hcB : c < tfBG := (Ordinal.sub_le_self _ _).trans_lt hνB
  obtain ⟨hDO, hBO⟩ := tiB_Om1_succ (S := S) (n := n)
  obtain ⟨hDν, hBν⟩ := mvB_add (k := n) hDO hD
  rw [hν] at hDν hBν
  rw [hBO] at hBν
  obtain ⟨hDψ, hBψ⟩ := tiB_psi2 (n := n) hD hcB
  rw [tf_psi S c hcB.le, hν] at hDψ hBψ
  exact ⟨hDν, hDψ, hBν, by rw [hBψ, tf_psi S _ hBc.le, hBν]⟩

/-- **`B_n` on the codes below `B_Γ`**: for a code `μ` over a strongly critical `x < L(ω)` with `B_n x ≤ Ω₁`, `μ` is
in the domain of `B_n`, `B_n μ` is a code over `B_n x`, `B_n μ < B_Γ`, and `tfDat (B_n μ) = B_n (tfDat μ)`. -/
theorem tiB_code {n : ℕ} {x : Ordinal.{0}} (hxS : SC x) (hxL : x < Nc.ncL S ω) (hBx : Bc.bcB S n x ≤ Om 1) :
    ∀ μ, TfCl x μ → MvD S μ ∧ TfCl (Bc.bcB S n x) (Bc.bcB S n μ) ∧ Bc.bcB S n μ < tfBG ∧
      tfDat (Bc.bcB S n μ) = Bc.bcB S n (tfDat μ) := by
  have hx1 : x ≤ Om1 := by rw [rj_Om1]; exact (hxL.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  have hBx1 : Bc.bcB S n x ≤ Om1 := by rw [rj_Om1]; exact hBx
  have hBxpos : 0 < Bc.bcB S n x := by
    have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hxL) hxL).2 hxS.1
    rwa [Bc.bcB_zero] at this
  have hdL : ∀ w, TfCl x w → tfDat w < Nc.ncL S ω := fun w hw => (tf_cl_dat hxS w hw).trans hxL
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  rw [← rj_Om1] at hDO hBO
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  have hzB := ti_cl_lt hx1 hz
  rcases lt_trichotomy z Om1 with h | rfl | h
  · have hzx : z < x := hz.lt_of_lt_Om1 hxS h
    have hBzx := (Bc.bcB_lt_iff (k := n) (hzx.trans hxL) hxL).2 hzx
    have hBz1 : Bc.bcB S n z < Om1 := hBzx.trans_le hBx1
    exact ⟨mvD_of_lt (hzx.trans hxL), TfCl.small hBzx, hBz1.trans tfBG_gt,
      by rw [tfDat_small h, tfDat_small hBz1]⟩
  · exact ⟨hDO, by rw [hBO]; exact TfCl.om, by rw [hBO]; exact tfBG_gt,
      by rw [hBO, tfDat_Om1, Bc.bcB_zero]⟩
  have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · -- a Veblen normal form `φ(o, b)`
      set o := invVeblen₁ z with ho
      set b := invVeblen₂ z with hb
      have hbz : b < z := tf_inv2_lt hE
      obtain ⟨hco, hcb⟩ := tf_cl_inv hx1 z hz h hE hI
      have hev : veblen o b = z := by rw [ho, hb, veblen_invVeblen₁_invVeblen₂, hE]
      have ho0 : o ≠ 0 := by
        intro e
        rw [e, veblen_zero_apply] at hev
        have : ω ^ b = ω ^ z := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 this) hbz.ne
      obtain ⟨hDo, hCo, hBoB, hdo⟩ := IH o hI hco
      obtain ⟨hDb, hCb, hBbB, hdb⟩ := IH b hbz hcb
      obtain ⟨hDz, hBz⟩ := Mw.mwB_phi (k := n) hDo hDb (by rw [hev]; exact hI) (by rw [hev]; exact hbz)
      rw [hev] at hBz hDz
      have hD0 : MvD S 0 := mvD_of_lt (lt_of_le_of_lt zero_le hxL)
      have hBo0 : Bc.bcB S n o ≠ 0 := by
        intro e
        have h1 := (mvB_lt_iff (k := n) hD0 hDo).2 (pos_iff_ne_zero.2 ho0)
        rw [Bc.bcB_zero, e] at h1
        exact lt_irrefl _ h1
      have hBb : Bc.bcB S n b < veblen (Bc.bcB S n o) (Bc.bcB S n b) := by
        rw [← hBz]; exact (mvB_lt_iff hDb hDz).2 hbz
      have hBo : Bc.bcB S n o < Bc.bcB S n z := (mvB_lt_iff hDo hDz).2 hI
      have hBzB : Bc.bcB S n z < tfBG := by rw [hBz]; exact tfBG_SC.2 _ hBoB _ hBbB
      refine ⟨hDz, by rw [hBz]; exact TfCl.phi hCo hCb, hBzB, ?_⟩
      have hOz : Om1 < Bc.bcB S n z := by
        have := (mvB_lt_iff (k := n) hDO hDz).2 h; rwa [hBO] at this
      have hBE : ω ^ Bc.bcB S n z = Bc.bcB S n z := by rw [hBz]; exact gg_veblen_eps hBo0
      have hBI : invVeblen₁ (Bc.bcB S n z) < Bc.bcB S n z := by
        rw [hBz, invVeblen₁_veblen hBb, ← hBz]; exact hBo
      rw [tfDat_phi hOz hBzB hBE hBI, tfDat_phi h hzB hE hI, hBz, invVeblen₁_veblen hBb,
        invVeblen₂_veblen hBo0 hBb, hdo, hdb]
      rcases le_total (tfDat o) (tfDat b) with hle | hle
      · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL b hcb) hle)]
      · rw [max_eq_left hle, max_eq_left (Ri.riB_mono (hdL o hco) hle)]
    · -- an atom `Γ_ν = ψ_{Ω₂}(c)`
      have hg := tf_SC_gamma h hI
      set ν := tfIdx z with hνdef
      have h1 : Om1 < ν := by rw [← tf_Om1_lt_gamma, hg]; exact h
      have hν : TfCl x ν := tf_cl_atom hx1 z hz ν h1 hg
      have hc : TfCl x (ν - (Om1 + 1)) :=
        (tfDec hxS ν hν).1 _ (TfCl.add TfCl.om (TfCl.one hxS.1)) (Order.add_one_le_of_lt h1)
      have hclt : ν - (Om1 + 1) < z := tf_atom_lt h hzB hI
      obtain ⟨hDc, hCc, hBcB, hdc⟩ := IH _ hclt hc
      obtain ⟨-, hDg, hBν, hBg⟩ := tiB_gamma (n := n) h1 (by rw [hg]; exact hzB) hDc hBcB
      rw [hg] at hDg hBg
      have h1' : Om1 < Om1 + 1 + Bc.bcB S n (ν - (Om1 + 1)) := (lt_add_one _).trans_le le_self_add
      have hνB' : Om1 + 1 + Bc.bcB S n (ν - (Om1 + 1)) < tfBG :=
        tf_BG_indec.add_lt (SC.add_one_lt tfBG_SC tfBG_gt) hBcB
      have hgB' : gamma (Om1 + 1 + Bc.bcB S n (ν - (Om1 + 1))) < tfBG := by
        rw [← tfBG_fix]; exact gamma_lt_gamma.2 hνB'
      rw [hBν] at hBg
      refine ⟨hDg, by rw [hBg]; exact TfCl.gam (TfCl.add (TfCl.add TfCl.om (TfCl.one hBxpos)) hCc) h1',
        by rw [hBg]; exact hgB', ?_⟩
      have e1 := tfDat_gamma h1' hgB'
      rw [Ordinal.add_sub_cancel] at e1
      have e2 := tfDat_gamma h1 (by rw [hg]; exact hzB)
      rw [hg] at e2
      rw [hBg, e1, hdc, e2]
  · -- Cantor normal form
    obtain ⟨hsub, hlog⟩ := tfDec hxS z hz
    set g := log ω z with hgdef
    have hgz : g < z := tf_log_lt h hE
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hk0 : k ≠ 0 := by
      intro e
      have h1 := Ordinal.div_opow_log_pos ω hz0
      rw [hk, e, Nat.cast_zero] at h1
      exact lt_irrefl _ h1
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hrg : z % ω ^ g < ω ^ g := Ordinal.mod_lt z (opow_pos _ omega0_pos).ne'
    have hwk : TfCl x (ω ^ g * k) := TfCl.mul_nat hxS.1 (TfCl.opow hxS.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : TfCl x (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := rj_mod_lt hz0
    obtain ⟨hDg, hCg, hBgB, hdg⟩ := IH g hgz hlog
    obtain ⟨hDr, hCr, hBrB, hdr⟩ := IH _ hrz hr
    obtain ⟨hDw, hBw⟩ := Rk.rkB_opow_nat (n := n) hDg k
    obtain ⟨hDz, hBz⟩ := mvB_add (k := n) hDw hDr
    rw [hdec] at hBz hDz
    obtain ⟨hDog, hBog⟩ := Ld.ldB_opow (n := n) hDg
    have hBr : Bc.bcB S n (z % ω ^ g) < ω ^ Bc.bcB S n g := by
      rw [← hBog]; exact (mvB_lt_iff hDr hDog).2 hrg
    have hwB : ω ^ Bc.bcB S n g < tfBG := by
      rw [← Low.opow_eq_self_of_SC tfBG_SC]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hBgB
    have hkB : (k : Ordinal.{0}) < tfBG := ((natCast_lt_omega0 k).trans_le (omega0_le_omega 1)).trans tfBG_gt
    have hBzB : Bc.bcB S n z < tfBG := by
      rw [hBz, hBw]; exact tf_BG_indec.add_lt (tf_BG_mul_lt hwB hkB) hBrB
    refine ⟨hDz, by rw [hBz, hBw]; exact TfCl.add (TfCl.mul_nat hBxpos (TfCl.opow hBxpos hCg) k) hCr, hBzB, ?_⟩
    have hOz : Om1 < Bc.bcB S n z := by
      have := (mvB_lt_iff (k := n) hDO hDz).2 h; rwa [hBO] at this
    have hlogB : log ω (Bc.bcB S n z) = Bc.bcB S n g := by
      rw [hBz, hBw, log_opow_mul_add one_lt_omega0 (by exact_mod_cast hk0) hBr,
        Ordinal.log_eq_zero (natCast_lt_omega0 k), add_zero]
    have hmodB : Bc.bcB S n z % ω ^ log ω (Bc.bcB S n z) = Bc.bcB S n (z % ω ^ g) := by
      rw [hlogB, hBz, hBw, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hBr]
    have hBE : ω ^ Bc.bcB S n z ≠ Bc.bcB S n z := by
      intro e
      have h1 : log ω (Bc.bcB S n z) = Bc.bcB S n z := by
        conv_lhs => rw [← e]
        exact log_opow one_lt_omega0 _
      rw [hlogB] at h1
      exact absurd h1 ((mvB_lt_iff hDg hDz).2 hgz).ne
    rw [tfDat_cnf hOz hBzB hBE, hmodB, hlogB, hdg, hdr, tfDat_cnf h hzB hE]
    rcases le_total (tfDat g) (tfDat (z % ω ^ g)) with hle' | hle'
    · rw [max_eq_right hle', max_eq_right (Ri.riB_mono (hdL _ hr) hle')]
    · rw [max_eq_left hle', max_eq_left (Ri.riB_mono (hdL g hlog) hle')]

/-- **A code over `c_{n+1}` is in the domain of `B_n`, and its image is a code over `B_n c_{n+1}` below `B_Γ`.** -/
theorem tiB_cl {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) :
    MvD S μ ∧ TfCl (Bc.bcB S n (Bc.bcC S (n + 1))) (Bc.bcB S n μ) ∧ Bc.bcB S n μ < tfBG ∧
      tfDat (Bc.bcB S n μ) = Bc.bcB S n (tfDat μ) :=
  tiB_code (Lw.lw_L_SC S _) (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) μ hμ

/-- **`B_n` keeps the codes below `B_Γ`** over `c_{n+1}`. -/
theorem tiB_lt_BG {n : ℕ} {μ : Ordinal.{0}} (hμ : TfCl (Bc.bcC S (n + 1)) μ) : Bc.bcB S n μ < tfBG :=
  (tiB_cl hμ).2.2.1

/-- **`tfDat (B_n z) = B_n (tfDat z)`** for every code `z` over `c_{n+1}`. -/
theorem tiB_dat {n : ℕ} {z : Ordinal.{0}} (hz : TfCl (Bc.bcC S (n + 1)) z) :
    tfDat (Bc.bcB S n z) = Bc.bcB S n (tfDat z) := (tiB_cl hz).2.2.2

end Googology.Trans.PoR.InaccPsi.R2.Ti
