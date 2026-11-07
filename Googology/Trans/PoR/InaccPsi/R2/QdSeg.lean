import Googology.Trans.PoR.InaccPsi.R2.QdGx
import Googology.Trans.PoR.InaccPsi.R2.QcSeg

/-!
# QdSeg: THE SEGMENTS FROM `B₂` ON — THE INDEX READINGS AND THE GATES

`B₂` is a fixed point of `Γ` (`qd_gamma_B2`), so every code `c ∈ [B₂, B₃)` lies in the segment of a fixed point
`Va.vaFB c ≥ B₂` of `Γ`.  As `Qc.qc_vI`, `Qc.qc_off_gate`, `Qc.qc_FB_gate` with `Qd.qdRI` and `Qd.qdGt`:

* `qd_gamma_B2`, `qd_FB_ge_B2`, `qd_vI` (**an atom index past the segment base reads `F(x) + (j − (F+1))(x)`**);
* `qd_off_gate` (**the offset `j − (F+1)` keeps the gate of `j` up to `ω`**), `qd_FB_gate` (**the segment base keeps the
  gate of the code up to `ω`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Va
  Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **`B₂` is a fixed point of `Γ`.** -/
theorem qd_gamma_B2 : gamma (ucB : Ordinal.{0}) = ucB := by
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  have h0O : (0 : Ordinal.{0}) < OmTwo := uc_SC_Om2.1
  have hH : ucH 0 ucB = ucB := ucB_spec h0E (by rw [ucC_small h0O]; exact ucB_SC.1)
  rw [← Rh.rhF_zero]
  exact (ucH_fix_iff_F h0O (max_lt ucB_gt ucB_SC.1)).1 hH

/-- **From `B₂` on the segment base is at least `B₂`.** -/
theorem qd_FB_ge_B2 {c : Ordinal.{0}} (hX : ucB ≤ c) : ucB ≤ vaFB c :=
  vs_FB_max ((tl_BG_lt_X.trans uc_X_lt_B).le.trans hX) qd_gamma_B2 ucB_gt hX

/-- **An atom index past the segment base reads `F(x) + (j − (F+1))(x)`.** -/
theorem qd_vI {e j : Ordinal.{0}} (hBe : tfBG ≤ e) (h1 : vaFB e < j) (h2 : j ≤ e) (x : Ordinal.{0}) :
    qdRI j x = vD (vaFB e) x + vD (j - (vaFB e + 1)) x := by
  obtain ⟨hF, hp⟩ := vs_fpG_seg hBe h1 h2
  unfold qdRI; rw [if_pos hF, hp]

/-- **The offset `j − (F+1)` keeps the gate of `j` up to `ω`** (`F` an `ε`-number code). -/
theorem qd_off_gate {F j : Ordinal.{0}} (hFE : InE F) (hXF : ucB ≤ F) (hjB : j < qdB) (hj : F < j) :
    qdGt (j - (F + 1)) ≤ max ω (qdGt j) := by
  have hNB : eN F ≤ qdB := eN_le (hj.trans hjB) (Low.opow_eq_self_of_SC qdB_SC)
  have hF0 : F ≠ 0 := hFE.pos.ne'
  rcases le_or_gt (F * ω) j with hbig | hsmall
  · -- the prefix is absorbed
    have e : F + 1 + j = j := by
      rw [add_assoc]
      have h1 : (1 : Ordinal.{0}) + j = j := one_add_of_omega0_le
        ((omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE hFE)).trans ((Ordinal.le_mul_left _ omega0_pos).trans hbig))
      rw [h1]; exact add_eq_right_iff_mul_omega0_le.2 hbig
    rw [Ordinal.sub_eq_of_add_eq e]; exact le_max_right _ _
  -- `j = F·m + r`, `1 ≤ m < ω`, `r < F`
  set m := j / F with hm
  set r := j % F with hr
  have hdec : F * m + r = j := Ordinal.div_add_mod j F
  have hrB : r < F := Ordinal.mod_lt j hF0
  have hmω : m < ω := (Ordinal.lt_mul_iff_div_lt hF0).1 hsmall
  obtain ⟨n, hn⟩ := lt_omega0.1 hmω
  have hm1 : 1 ≤ m := by
    rw [hm, ← Ordinal.mul_le_iff_le_div hF0, mul_one]; exact hj.le
  have hgate : ∀ k : ℕ, 1 ≤ k → qdGt (F * k + r) = max (qdQEt F) (qdGt r) := by
    intro k hk
    have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
    have hkB : (k : Ordinal.{0}) < F := (natCast_lt_omega0 k).trans (omega0_lt_inE hFE)
    have hv : F ^ (1 : Ordinal.{0}) * k + r < eN F := by
      rw [opow_one]
      exact (inE_indec (eN_E F)).add_lt (mul_lt_inE (eN_E F) (lt_eN _) (hkB.trans (lt_eN _)))
        (hrB.trans (lt_eN _))
    have h := qdGt_cnf hFE hXF one_ne_zero hk0 hkB (by rw [opow_one]; exact hrB) hv (hv.trans_le hNB)
    rw [opow_one] at h
    rw [h, qdQt_one, qdQt_nat, max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ qdQEt F),
      max_eq_right (zero_le : (0 : Ordinal.{0}) ≤ qdGt r)]
  have hjr : qdGt j = max (qdQEt F) (qdGt r) := by
    rw [← hdec, hn]; exact hgate n (by exact_mod_cast hn ▸ hm1)
  rw [hjr]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · -- `m = 1`: `j = F + r`, the offset is `r` up to a finite part
    have hn1 : n = 1 := by
      have : 1 ≤ n := by exact_mod_cast hn ▸ hm1
      omega
    rw [hn1, Nat.cast_one] at hn
    have e : j - (F + 1) = r - 1 := by
      rw [← hdec, hn, mul_one, Ordinal.add_sub_add_cancel]
    rw [e]
    rcases lt_or_ge r ω with hrω | hrω
    · obtain ⟨k, hk⟩ := lt_omega0.1 hrω
      rw [hk]
      have : ((k : Ordinal.{0}) - 1) < ω := (Ordinal.sub_le_self _ _).trans_lt (natCast_lt_omega0 k)
      obtain ⟨k', hk'⟩ := lt_omega0.1 this
      rw [hk', qdGt_nat]; exact (natCast_lt_omega0 k').le.trans (le_max_left _ _)
    · have e2 : r - 1 = r := Ordinal.sub_eq_of_add_eq (one_add_of_omega0_le hrω)
      rw [e2]; exact (le_max_right _ _).trans (le_max_right _ _)
  · -- `m ≥ 2`: the offset is `F·(m−1) + r`
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have e : j - (F + 1) = F * ((k + 1 : ℕ) : Ordinal.{0}) + r := by
      refine Ordinal.sub_eq_of_add_eq ?_
      have hω' : ω ≤ F * ((k + 1 : ℕ) : Ordinal.{0}) :=
        (omega0_le_of_isSuccLimit (ev_isSuccLimit_of_inE hFE)).trans
          (Ordinal.le_mul_left _ (by exact_mod_cast Nat.succ_pos k))
      have e2 : (1 : Ordinal.{0}) + ((k + 1 : ℕ) : Ordinal.{0}) = ((k + 2 : ℕ) : Ordinal.{0}) := by
        rw [← Nat.cast_one, ← Nat.cast_add]; congr 1; omega
      calc F + 1 + (F * ((k + 1 : ℕ) : Ordinal.{0}) + r)
          = F + (1 + F * ((k + 1 : ℕ) : Ordinal.{0})) + r := by
            rw [← add_assoc (F + 1), add_assoc F 1]
        _ = F + F * ((k + 1 : ℕ) : Ordinal.{0}) + r := by rw [one_add_of_omega0_le hω']
        _ = F * (1 + ((k + 1 : ℕ) : Ordinal.{0})) + r := by rw [mul_one_add]
        _ = j := by rw [e2, ← hn]; exact hdec
    rw [e, hgate (k + 1) (by omega)]; exact le_max_right _ _

/-- **The segment base keeps the gate of the code up to `ω`.** -/
theorem qd_FB_gate : ∀ c, ucB ≤ c → c < qdB → qdGt (vaFB c) ≤ max ω (qdGt c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hXc hcB
  have hBc : tfBG ≤ c := (tl_BG_lt_X.trans uc_X_lt_B).le.trans hXc
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hBc
  have hXF : ucB ≤ vaFB c := qd_FB_ge_B2 hXc
  have heB : tfBG ≤ guE c := gl_E_max (Low.opow_eq_self_of_SC tfBG_SC) tfBG_gt hBc
  have hec : guE c ≤ c := gl_E_le (yh_gfE_le hGc)
  have hce : c < eN (guE c) := gl_lt_eN (yh_gfE_le hGc)
  have heE := guE_E c
  have hGe : gcG 0 ≤ guE c := va_G_le_BG.trans heB
  -- the segment base of `c` is that of its bracket
  have hFe : vaFB c ≤ guE c := by
    refine csSup_le (vs_FS_ne hBc) fun F hF => ?_
    by_contra h
    push Not at h
    have hFE' : InE F := zm_fix_E (zm_fix_of_gamma hF.1)
    exact absurd (hF.2.2.trans_lt hce) (not_lt.2 (eN_le h hFE'))
  have hFF : vaFB (guE c) = vaFB c := vs_FB_of_le hBc hFe hec
  obtain ⟨hXe, heB2⟩ := qd_guE_B hXc hcB
  have hge : qdGt (guE c) ≤ qdGt c := by
    rw [qdGt_base heE hXe heB2, qdGt_dec hXc hcB]; exact (le_max_left _ _).trans (le_max_left _ _)
  rcases hec.lt_or_eq with hlt | heq
  · rw [← hFF]
    exact (IH _ hlt hXe heB2).trans (max_le_max le_rfl hge)
  have hcE : InE c := by rw [← heq]; exact heE
  rcases vs_atom_cases hBc with hB | ⟨hA, hjB, hjc⟩ | hnA
  · rw [← hB]; exact le_max_right _ _
  · have hjF : vaFB (yhJ c) = vaFB c := vs_FB_of_le hBc hjB.le hjc.le
    have hBj : tfBG ≤ yhJ c := (vs_FB_ge hBc).trans hjB.le
    rw [← hjF]
    refine (IH _ hjc (hXF.trans hjB.le) (hjc.trans hcB)).trans ?_
    rw [qd_maxQ le_rfl (yhJ c), qdGt_base hcE hXc hcB, qdQEt_atom hXc hcB hA hjc]
  · have hGc' : gcG 0 < c := lt_of_le_of_ne hGc fun h => hnA (h ▸ yhAt_gcG 0)
    obtain ⟨-, hkc, hic, hpsi⟩ := va_data hcE hGc' hnA
    have hFSC := vs_FB_SC hBc
    have hOF := vs_FB_gt hBc
    have hcle : vaFB c ≤ yhK c ∨ vaFB c ≤ yhI c := by
      by_contra hcon
      push Not at hcon
      have h := yhPsi_lt_SC hFSC hOF hcon.1 hcon.2
      rw [hpsi] at h
      exact absurd (vs_FB_le hBc) (not_le.2 h)
    have hQ : max ω (qdGt c) = max ω (max (qdQt (yhK c)) (qdQt (yhI c))) := by
      rw [qdGt_base hcE hXc hcB, qdQEt_psi hXc hcB hnA]
    rw [hQ]
    rcases hcle with h | h
    · have hF' : vaFB (yhK c) = vaFB c := vs_FB_of_le hBc h hkc.le
      rw [← hF']
      refine (IH _ hkc (hXF.trans h) (hkc.trans hcB)).trans ?_
      rw [qd_maxQ le_rfl (yhK c)]
      exact max_le_max le_rfl (le_max_left _ _)
    · have hF' : vaFB (yhI c) = vaFB c := vs_FB_of_le hBc h hic.le
      rw [← hF']
      refine (IH _ hic (hXF.trans h) (hic.trans hcB)).trans ?_
      rw [qd_maxQ le_rfl (yhI c)]
      exact max_le_max le_rfl (le_max_right _ _)

end Googology.Trans.PoR.InaccPsi.R2.Qd
