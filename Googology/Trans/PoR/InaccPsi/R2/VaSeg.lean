import Googology.Trans.PoR.InaccPsi.R2.VaCg

/-!
# VaSeg: THE SEGMENT OF A CODE PAST `B_Γ` — THE LARGEST FIXED POINT OF `Γ` BELOW IT

Every code `E ≥ B_Γ` lies in the segment of the largest fixed point `F = vaFB E` of `Γ` in `(Ω₁, E]`.  Inside a
segment the atoms are `F` and the atoms `Γ(j)`, `F < j`; an atom index past `F` reads `F(x) + (j − (F+1))(x)`; the
offset `j − (F+1)` and the base `F` keep the gates.

* `VsFS`, `vaFB`, `vs_FB_fix`, `vs_FB_ge`, `vs_FB_le`, `vs_FB_gt`, `vs_FB_max`, `vs_FB_SC`, `vs_FB_E`, `vs_FB_nfx`
  (**no fixed point of `Γ` in `(vaFB E, E]`**), `vs_FB_eq`, `vs_FB_self`, `vs_FB_B2` (**`B_Γ` below `B₂`**),
  `vs_FB_eN` (**the segment does not change at the next `ε`-number**), `vs_FB_of_le`;
* `vs_gcG_fix`, `vs_atom_cases` (**the atoms of a segment**), `vs_fpG_seg`, `vs_vI`;
* `vs_off_gate` (**the offset `j − (F+1)` keeps the gate of `j` up to `ω`**), `vs_FB_gate` (**the segment base keeps
  the gate of the code up to `ω`**);
* `vs_eN_cl` (**`ε_{p+1} = ϑˣ(Ω₁ + p)` at a closed point `p`**).

No new axiom.  New definitions: `VsFS`, `vaFB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Rh

/-! ## The segment base -/

/-- The fixed points of `Γ` in `(Ω₁, E]`. -/
def VsFS (E : Ordinal.{0}) : Set Ordinal.{0} := {F | gamma F = F ∧ Om1 < F ∧ F ≤ E}

/-- **The segment base of `E`**: the largest fixed point of `Γ` in `(Ω₁, E]`. -/
noncomputable def vaFB (E : Ordinal.{0}) : Ordinal.{0} := sSup (VsFS E)

section FB

variable {E : Ordinal.{0}} (hBE : tfBG ≤ E)
include hBE

theorem vs_FS_ne : (VsFS E).Nonempty := ⟨tfBG, tfBG_fix, tfBG_gt, hBE⟩

theorem vs_FS_bdd : BddAbove (VsFS E) := ⟨E, fun _ h => h.2.2⟩

theorem vs_FB_fix : gamma (vaFB E) = vaFB E := by
  unfold vaFB
  rw [isNormal_gamma.map_sSup (vs_FS_ne hBE) (vs_FS_bdd hBE)]
  congr 1
  ext F
  constructor
  · rintro ⟨F', hF', rfl⟩
    have h1 : gamma F' = F' := hF'.1
    rw [h1]; exact hF'
  · intro hF; exact ⟨F, hF, hF.1⟩

theorem vs_FB_ge : tfBG ≤ vaFB E :=
  le_csSup (vs_FS_bdd hBE) (show tfBG ∈ VsFS E from ⟨tfBG_fix, tfBG_gt, hBE⟩)

theorem vs_FB_le : vaFB E ≤ E := csSup_le (vs_FS_ne hBE) fun _ h => h.2.2

theorem vs_FB_gt : Om1 < vaFB E := tfBG_gt.trans_le (vs_FB_ge hBE)

theorem vs_FB_max {F : Ordinal.{0}} (hF : gamma F = F) (hOF : Om1 < F) (hFE : F ≤ E) : F ≤ vaFB E :=
  le_csSup (vs_FS_bdd hBE) (show F ∈ VsFS E from ⟨hF, hOF, hFE⟩)

theorem vs_FB_SC : SC (vaFB E) := by rw [← vs_FB_fix hBE]; exact Lq.lq_gamma_SC _

theorem vs_FB_E : InE (vaFB E) := Low.opow_eq_self_of_SC (vs_FB_SC hBE)

/-- **No fixed point of `Γ` in `(vaFB E, E]`.** -/
theorem vs_FB_nfx {y : Ordinal.{0}} (h1 : vaFB E < y) (h2 : y ≤ E) : gamma y ≠ y := fun h =>
  absurd (vs_FB_max hBE h ((vs_FB_gt hBE).trans h1) h2) (not_le.2 h1)

end FB

theorem vs_FB_eq {E F : Ordinal.{0}} (hF : gamma F = F) (hOF : Om1 < F) (hFE : F ≤ E)
    (hnf : ∀ y, F < y → y ≤ E → gamma y ≠ y) : vaFB E = F := by
  have hBE : tfBG ≤ E := (tfBG_le hF hOF).trans hFE
  refine le_antisymm ?_ (vs_FB_max hBE hF hOF hFE)
  by_contra h
  push Not at h
  exact hnf _ h (vs_FB_le hBE) (vs_FB_fix hBE)

/-- The segment base of a fixed point is the fixed point. -/
theorem vs_FB_self {F : Ordinal.{0}} (hF : gamma F = F) (hOF : Om1 < F) : vaFB F = F :=
  vs_FB_eq hF hOF le_rfl fun _ h1 h2 => absurd h2 (not_le.2 h1)

/-- **Below `B₂` the segment base is `B_Γ`.** -/
theorem vs_FB_B2 {E : Ordinal.{0}} (hBE : tfBG ≤ E) (hE : E < vaB2) : vaFB E = tfBG :=
  vs_FB_eq tfBG_fix tfBG_gt hBE fun _ h1 h2 hy => absurd (h2.trans_lt hE) (not_lt.2 (va_B2_min h1 hy))

/-- **The segment base does not move at the next `ε`-number.** -/
theorem vs_FB_eN {E : Ordinal.{0}} (hBE : tfBG ≤ E) : vaFB (eN E) = vaFB E := by
  refine vs_FB_eq (vs_FB_fix hBE) (vs_FB_gt hBE) ((vs_FB_le hBE).trans (lt_eN E).le) fun y h1 h2 hy => ?_
  rcases le_or_gt y E with hyE | hyE
  · exact vs_FB_nfx hBE h1 hyE hy
  · have hyE' : InE y := zm_fix_E (zm_fix_of_gamma hy)
    have hy' : y = eN E := le_antisymm h2 (eN_le hyE hyE')
    exact zm_eN_nfix E (by rw [← hy']; exact zm_fix_of_gamma hy)

/-- **Inside a segment the segment base is the same.** -/
theorem vs_FB_of_le {e E : Ordinal.{0}} (hBE : tfBG ≤ E) (h1 : vaFB E ≤ e) (h2 : e ≤ E) : vaFB e = vaFB E := by
  have hBe : tfBG ≤ e := (vs_FB_ge hBE).trans h1
  exact le_antisymm (vs_FB_max hBE (vs_FB_fix hBe) (vs_FB_gt hBe) ((vs_FB_le hBe).trans h2))
    (vs_FB_max hBe (vs_FB_fix hBE) (vs_FB_gt hBE) h1)

/-! ## The atoms of a segment -/

/-- A fixed point of `Γ` above `Ω₁` is the atom `Γ(Ω₁+1+F) = F`. -/
theorem vs_gcG_fix {F : Ordinal.{0}} (hF : gamma F = F) (hOF : Om1 < F) : gcG F = F := by
  have hE : InE F := zm_fix_E (zm_fix_of_gamma hF)
  rw [tf_gcG, gl_absorb hE hOF, hF]

/-- **The atoms of a segment**: the segment base, or `Γ(j)` with `vaFB e < j < Γ(j)`, or not an atom. -/
theorem vs_atom_cases {e : Ordinal.{0}} (hBe : tfBG ≤ e) :
    e = vaFB e ∨ (YhAt e ∧ vaFB e < yhJ e ∧ yhJ e < e) ∨ ¬ YhAt e := by
  by_cases hA : YhAt e
  · by_cases hfix : gamma e = e
    · exact Or.inl (vs_FB_self hfix hA.2).symm
    obtain ⟨j, rfl⟩ := yhAt_iff.1 hA
    refine Or.inr (Or.inl ⟨hA, ?_, ?_⟩) <;> rw [yhJ_gcG]
    · by_contra hjF
      push Not at hjF
      have h1 : gcG j ≤ vaFB (gcG j) := by
        have := gcG_le hjF; rwa [vs_gcG_fix (vs_FB_fix hBe) (vs_FB_gt hBe)] at this
      have h2 : vaFB (gcG j) = gcG j := le_antisymm (vs_FB_le hBe) h1
      apply hfix
      rw [← h2]; exact vs_FB_fix hBe
    · refine lt_of_le_of_ne gcG_strictMono.le_apply fun he => hfix ?_
      have hjE : InE j := by rw [he]; exact Low.opow_eq_self_of_SC (gcG_SC j)
      have hjO : Om1 < j := by rw [he]; exact hA.2
      have h1 : Om1 + 1 + j = j := gl_absorb hjE hjO
      rw [← he]
      conv_rhs => rw [he, tf_gcG, h1]
  · exact Or.inr (Or.inr hA)

/-- **Past the segment base the largest fixed point of `Γ` below an index is the segment base.** -/
theorem vs_fpG_seg {e j : Ordinal.{0}} (hBe : tfBG ≤ e) (h1 : vaFB e < j) (h2 : j ≤ e) :
    VaFixG j ∧ vaFpG j = vaFB e := by
  refine ⟨⟨vaFB e, vs_FB_fix hBe, vs_FB_gt hBe, h1⟩, ?_⟩
  unfold vaFpG
  exact IsGreatest.csSup_eq ⟨⟨vs_FB_fix hBe, vs_FB_gt hBe, h1⟩,
    fun F hF => vs_FB_max hBe hF.1 hF.2.1 (hF.2.2.le.trans h2)⟩

/-- **An atom index past the segment base reads `F(x) + (j − (F+1))(x)`.** -/
theorem vs_vI {e j : Ordinal.{0}} (hBe : tfBG ≤ e) (h1 : vaFB e < j) (h2 : j ≤ e) (x : Ordinal.{0}) :
    vI j x = vR (vaFB e) x + vR (j - (vaFB e + 1)) x := by
  obtain ⟨hF, hp⟩ := vs_fpG_seg hBe h1 h2
  unfold vI; rw [if_pos hF, hp]

/-! ## The gates -/

/-- **The offset `j − (F+1)` keeps the gate of `j` up to `ω`** (`F` an `ε`-number code). -/
theorem vs_off_gate {F j : Ordinal.{0}} (hFE : InE F) (hFG : gcG 0 ≤ F) (hj : F < j) :
    yrG (j - (F + 1)) ≤ max ω (yrG j) := by
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
  have hgate : ∀ k : ℕ, 1 ≤ k → yrG (F * k + r) = max (yrQE F) (yrG r) := by
    intro k hk
    have hk0 : (k : Ordinal.{0}) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hk)
    have hkB : (k : Ordinal.{0}) < F := (natCast_lt_omega0 k).trans (omega0_lt_inE hFE)
    have hv : F ^ (1 : Ordinal.{0}) * k + r < eN F := by
      rw [opow_one]
      exact (inE_indec (eN_E F)).add_lt (mul_lt_inE (eN_E F) (lt_eN _) (hkB.trans (lt_eN _)))
        (hrB.trans (lt_eN _))
    have h := yrG_cnf hFE hFG one_ne_zero hk0 hkB (by rw [opow_one]; exact hrB) hv
    rw [opow_one] at h
    rw [h, yrQ_one, yrQ_nat, max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ yrQE F),
      max_eq_right (zero_le : (0 : Ordinal.{0}) ≤ yrG r)]
  have hjr : yrG j = max (yrQE F) (yrG r) := by
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
      rw [hk', va_nat_gate]; exact (natCast_lt_omega0 k').le.trans (le_max_left _ _)
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
theorem vs_FB_gate : ∀ c, tfBG ≤ c → yrG (vaFB c) ≤ max ω (yrG c) := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hBc
  have hGc : gcG 0 ≤ c := va_G_le_BG.trans hBc
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
  have hge : yrG (guE c) ≤ yrG c := by
    rw [yrG_base heE hGe, yrG_dec hGc]; exact (le_max_left _ _).trans (le_max_left _ _)
  rcases hec.lt_or_eq with hlt | heq
  · rw [← hFF]
    exact (IH _ hlt heB).trans (max_le_max le_rfl hge)
  have hcE : InE c := by rw [← heq]; exact heE
  rcases vs_atom_cases hBc with hB | ⟨hA, hjB, hjc⟩ | hnA
  · rw [← hB]; exact le_max_right _ _
  · have hjF : vaFB (yhJ c) = vaFB c := vs_FB_of_le hBc hjB.le hjc.le
    have hBj : tfBG ≤ yhJ c := (vs_FB_ge hBc).trans hjB.le
    rw [← hjF]
    refine (IH _ hjc hBj).trans ?_
    rw [va_maxQ le_rfl (yhJ c), yrG_base hcE hGc, yrQE_atom hA hjc]
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
    have hQ : max ω (yrG c) = max ω (max (yrQ (yhK c)) (yrQ (yhI c))) := by
      rw [yrG_base hcE hGc, yrQE_psi hnA]
    rw [hQ]
    rcases hcle with h | h
    · have hF' : vaFB (yhK c) = vaFB c := vs_FB_of_le hBc h hkc.le
      rw [← hF']
      refine (IH _ hkc ((vs_FB_ge hBc).trans h)).trans ?_
      rw [va_maxQ le_rfl (yhK c)]
      exact max_le_max le_rfl (le_max_left _ _)
    · have hF' : vaFB (yhI c) = vaFB c := vs_FB_of_le hBc h hic.le
      rw [← hF']
      refine (IH _ hic ((vs_FB_ge hBc).trans h)).trans ?_
      rw [va_maxQ le_rfl (yhI c)]
      exact max_le_max le_rfl (le_max_right _ _)

/-! ## The next `ε`-number at a closed point -/

/-- **`ε_{p+1} = ϑˣ(Ω₁ + p)` at a closed point `p > x`.** -/
theorem vs_eN_cl {x p : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hpT : p ∈ Tset x) (hp1 : p < Om1)
    (hxp : x < p) (hcl : YwClosed x p) : eN p = glA 1 p x := by
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  obtain ⟨-, -, -, haE, -, hta⟩ := glA_facts hx hx1 le_rfl h1T h11 hpT hp1
  refine le_antisymm (eN_le hta haE) ?_
  have hP1 : LuP 1 (eN p) := by
    have h := vzP_one.2 (eN_E p); unfold VzP at h; rwa [Nat.cast_one] at h
  have hpE : InE p := ywC_inE hx hx1 le_rfl hpT hp1 hxp ((ywC_one_iff hx hx1).2 hcl)
  have h1p : (1 : Ordinal.{0}) < p := lu_one_lt_E hpE
  refine glA_min hx hx1 le_rfl h1T h11 hpT hp1 hP1 (hxp.trans (lt_eN _)) (lt_eN _) (h1p.trans (lt_eN _))
    (fun σ hσ => ?_)
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 hpT hp1 hσ.le
  have hσ1 : σ < Om1 := hσ.trans hp1
  obtain ⟨-, -, -, hqE, -⟩ := geq_facts hx hx1 hσT hσ1
  have h1q : (1 : Ordinal.{0}) < gq σ x := lu_one_lt_E hqE
  exact ((xkA_lt hx hx1 hσT hσ1 h1q (gmq_gt hx hx1 hσT hσ1)).trans (hcl σ hσT hσ)).trans (lt_eN _)

end Googology.Trans.PoR.InaccPsi.R2.Va
