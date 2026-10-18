import Googology.Trans.PoR.InaccPsi.R2.FpFr

/-!
# The exact place of the first limit of frontiers: `Λ⁺(X) = ι(ω^T·ω)` for a system with top code `T`

For a term system `X` with `GgPoly X T` (`T < Γ_{Ω₁+1}` a code over every strongly critical base, `Ω₁ ≤ T`), top
`top(y) = Θ_y(T)`, `ε_{x+1} < top(x)` and an IMG package:

* `fpFr_exp` (**a named frontier has `e(η_λ) ≥ T`**: THEOREM UNI and `Θ_λ` strictly increasing on codes);
* `fpFr_mul` (**every frontier `λ ∈ (ω², ι(ω^T·ω))` is `ι(ω^T·k)` for some `k < ω`**: `ω^T` divides `η_λ`);
* `fpB1_ge` (**`ι(ω^T·ω) ≤ Λ⁺(X)`**: the frontiers below `ι(ω^T·j)` are finitely many, so they are not cofinal
  below `Λ⁺(X)`), `fpB1_eq` (**`Λ⁺(X) = ι(ω^T·ω)` and `ρ_{Λ⁺(X)} = P(ω^T·ω)`**, with `Ph.phFrGen`);
* the instances `fpLoc_lzWw`, `fpLoc_ltS`, `fpLoc_ltSw`, `fpLoc_lnS`, `fpLoc_lnSw` (**`Λ⁺(lnSw) =
  ι(φ(ω+1, Ω₁+1)·ω)`, `ρ_{Λ⁺(lnSw)} = P(φ(ω+1, Ω₁+1)·ω) < L(0)`**).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lz
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

section Gen

variable {X : XtSys} {T : Ordinal.{0}} (hT : T < ggGam) (hP : GgPoly X T)
  (htop : ∀ y, SC y → y < Om 1 → X.top y = ggTh y T)
include hT hP htop

/-- **A named frontier has `e(η_λ) ≥ T`.** -/
theorem fpFr_exp {l ηx : Ordinal.{0}} (hl : XtFr X l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) :
    T ≤ cdExp (cdEta S l) := by
  by_contra h
  push Not at h
  have hO := ggUni hT.le hP l ηx hl.1 hfix hX h.le
  have hSC := ggSC_fix hl.1 hfix hX
  have hl1 : l < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have h2 := ggTh_lt (ggExpMem hl.1 hfix hX (h.trans hT)) h
  have h3 := hl.2
  rw [hO, hfix, htop l hSC hl1] at h3
  exact absurd h3 h2.ne

/-- **Every frontier `λ ∈ (ω², ι(ω^T·ω))` is `ι(ω^T·k)`.** -/
theorem fpFr_mul (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) {l : Ordinal.{0}} (hl : XtFr X l)
    (hww : ω * ω < l) (hlt : l < iota S (ω ^ T * ω)) (hl1 : l < Om1) :
    ∃ k : ℕ, l = iota S (ω ^ T * (k : Ordinal.{0})) := by
  have hfix := ggFr_fix htopE hl hl1 hww
  have hX : upsilon l < Pv S (ω ^ T * ω) := by
    have h := upsilon_normal.strictMono hlt
    rw [ups_iota S] at h
    exact h
  have he := fpFr_exp (S := S) hT hP htop hl hfix hX
  obtain ⟨-, hι, hηlt, -⟩ := cdEta_pv_spec (S := S) hl.1.1 hX
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp (gg_name_ne hl.1 hfix hX)
  have hT1 : ω ^ T ∣ ω ^ cdExp (cdEta S l) := opow_dvd_opow ω he
  have hdv : ω ^ T ∣ cdEta S l := by rw [hdec]; exact dvd_add (hT1.trans hd) hT1
  obtain ⟨q, hq⟩ := hdv
  have hqw : q < ω := by
    rw [hq] at hηlt
    exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).1 hηlt
  obtain ⟨k, rfl⟩ := lt_omega0.1 hqw
  exact ⟨k, by rw [← hι, hq]⟩

/-- **`ι(ω^T·ω) ≤ Λ⁺(X)`.** -/
theorem fpB1_ge (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    iota S (ω ^ T * ω) ≤ xtB1 X := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨h0, hcof⟩ := xtB1_spec hPk
  have hb1 : xtB1 X < Om1 := xtB1_lt_Om1 hPk
  obtain ⟨μ1, hμ1, -, hμ1B⟩ := hcof 0 h0
  have hww1 : ω * ω ≤ μ1 := by
    obtain ⟨q, hq⟩ := (ri_iff.1 hμ1.1).2
    rw [hq]
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact (ri_iff.1 hμ1.1).1 hq
    exact le_mul_left _ (pos_iff_ne_zero.2 hq0)
  have hT0 : T ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) hTO).ne'
  have hwlim : IsSuccLimit (ω ^ T * ω) := by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact ph_opow_lim (by simp)
  have hlt' := hlt
  rw [iota_limit hwlim] at hlt'
  haveI : Nonempty (Iio (ω ^ T * ω)) := ⟨⟨0, hwlim.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hlt'
  obtain ⟨m, hm, hem⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 e.2
  obtain ⟨j, rfl⟩ := lt_omega0.1 hm
  have hbj : xtB1 X < iota S (ω ^ T * (j : Ordinal.{0})) := he.trans_le (iota_mono _ _ hem.le)
  let f : ℕ → Ordinal.{0} := fun k =>
    if iota S (ω ^ T * (k : Ordinal.{0})) < xtB1 X then iota S (ω ^ T * (k : Ordinal.{0})) else 0
  have hfb : ∀ k, f k < xtB1 X := fun k => by
    show (if iota S (ω ^ T * (k : Ordinal.{0})) < xtB1 X then iota S (ω ^ T * (k : Ordinal.{0})) else 0) < _
    split_ifs with h
    · exact h
    · exact h0
  have hνb : max (ω * ω) ((Finset.range j).sup f) < xtB1 X :=
    max_lt (hww1.trans_lt hμ1B) ((Finset.sup_lt_iff h0).2 fun k _ => hfb k)
  obtain ⟨μ, hμ, h1, h2⟩ := hcof _ hνb
  have hww : ω * ω < μ := (le_max_left _ _).trans_lt h1
  obtain ⟨k, hk⟩ := fpFr_mul (S := S) hT hP htop htopE hμ hww (h2.trans hlt) (h2.trans hb1)
  have hkj : k < j := by
    by_contra hkj
    push Not at hkj
    have hjk : ω ^ T * (j : Ordinal.{0}) ≤ ω ^ T * (k : Ordinal.{0}) := by gcongr
    have h3 := iota_mono (S := S) _ _ hjk
    rw [← hk] at h3
    exact absurd (h2.trans hbj) (not_lt.2 h3)
  have hfk : f k = μ := by
    show (if iota S (ω ^ T * (k : Ordinal.{0})) < xtB1 X then iota S (ω ^ T * (k : Ordinal.{0})) else 0) = μ
    rw [if_pos (by rw [← hk]; exact h2), hk]
  have h4 : f k ≤ max (ω * ω) ((Finset.range j).sup f) :=
    (Finset.le_sup (f := f) (Finset.mem_range.2 hkj)).trans (le_max_right _ _)
  rw [hfk] at h4
  exact absurd h1 (not_lt.2 h4)

/-- **`Λ⁺(X) = ι(ω^T·ω)` and `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`.** -/
theorem fpB1_eq (hTcl : ∀ Z, SC Z → GgCl Z T) (hTO : Om 1 ≤ T)
    (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    xtB1 X = iota S (ω ^ T * ω) ∧ upsilon (xtB1 X) = Pv S (ω ^ T * ω) ∧ Pv S (ω ^ T * ω) < Nc.ncL S 0 := by
  have hup := (phFrGen (S := S) hT (phPolyR_of hP) htop hTcl hTO).2.2
  have heq : xtB1 X = iota S (ω ^ T * ω) := le_antisymm hup.1 (fpB1_ge hT hP htop hTO htopE hPk)
  have hups : upsilon (xtB1 X) = Pv S (ω ^ T * ω) := by rw [heq, ups_iota S]
  exact ⟨heq, hups, hups ▸ hup.2.2⟩

end Gen

/-! ## The instances -/

theorem fp_eN_lt_B {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN x < lzYw x :=
  (gg_eN_lt_B hx hx1).trans_le (by rw [← lzY_zero hx hx1]; exact lzY_le_w x 0)

/-- **`Λ⁺(lzWw) = ι(ω^{phYw}·ω)`.** -/
theorem fpLoc_lzWw : xtB1 lzWw = iota S (ω ^ phYw * ω) ∧ upsilon (xtB1 lzWw) = Pv S (ω ^ phYw * ω) ∧
    Pv S (ω ^ phYw * ω) < Nc.ncL S 0 :=
  fpB1_eq fp_Yw_lt_Gam fpPoly_lzWw (fun _ hy hy1 => (fpTh_Yw hy hy1).symm) (fun _ hZ => fp_cl_Yw hZ)
    fp_Om1_le_Yw (fun _ hx hx1 => fp_eN_lt_B hx hx1) ltWw_topPkg

/-- **`Λ⁺(ltS K) = ι(ω^{fpTc K}·ω)`.** -/
theorem fpLoc_ltS (K : ℕ) : xtB1 (ltS K) = iota S (ω ^ fpTc K * ω) ∧
    upsilon (xtB1 (ltS K)) = Pv S (ω ^ fpTc K * ω) ∧ Pv S (ω ^ fpTc K * ω) < Nc.ncL S 0 :=
  fpB1_eq (fp_Tc_lt_Gam K) (fpPoly_ltS K) (fun _ hy hy1 => (fpTh_T hy hy1 K).symm) (fun _ hZ => fp_cl_Tc hZ K)
    (fp_Om1_le_Tc K) (fun _ hx hx1 => (fp_eN_lt_B hx hx1).trans (ltYw_lt_T hx hx1 K)) (ltS_topPkg K)

/-- **`Λ⁺(ltSw) = ι(ω^{fpTw}·ω)`.** -/
theorem fpLoc_ltSw : xtB1 ltSw = iota S (ω ^ fpTw * ω) ∧ upsilon (xtB1 ltSw) = Pv S (ω ^ fpTw * ω) ∧
    Pv S (ω ^ fpTw * ω) < Nc.ncL S 0 :=
  fpB1_eq fp_Tw_lt_Gam fpPoly_ltSw (fun _ hy hy1 => (fpTh_Tw hy hy1).symm) (fun _ hZ => fp_cl_Tw hZ)
    fp_Om1_le_Tw (fun x hx hx1 => ((fp_eN_lt_B hx hx1).trans (ltYw_lt_T hx hx1 0)).trans_le (ltT_le_w x 0))
    ltSw_topPkg

/-- **`Λ⁺(lnS K) = ι(ω^{fpCc (K+1)}·ω)`.** -/
theorem fpLoc_lnS (K : ℕ) : xtB1 (lnS K) = iota S (ω ^ fpCc (K + 1) * ω) ∧
    upsilon (xtB1 (lnS K)) = Pv S (ω ^ fpCc (K + 1) * ω) ∧ Pv S (ω ^ fpCc (K + 1) * ω) < Nc.ncL S 0 :=
  fpB1_eq (fp_C_lt_Gam (K + 1)) (fpPoly_lnS K) (fun _ hy hy1 => (fpTh_C hy hy1 (K + 1)).symm)
    (fun _ hZ => fp_cl_C hZ (K + 1)) (fp_Om1_lt_C (K + 1)).le
    (fun _ hx hx1 => (fp_eN_lt_B hx hx1).trans_le (ltC_mono hx hx1 (Nat.zero_le (K + 1)))) (lnS_topPkg K)

/-- **`Λ⁺(lnSw) = ι(φ(ω+1, Ω₁+1)·ω)`, `ρ_{Λ⁺(lnSw)} = P(φ(ω+1, Ω₁+1)·ω) < L(0)`.** -/
theorem fpLoc_lnSw : xtB1 lnSw = iota S (ω ^ fpPc * ω) ∧ upsilon (xtB1 lnSw) = Pv S (ω ^ fpPc * ω) ∧
    Pv S (ω ^ fpPc * ω) < Nc.ncL S 0 :=
  fpB1_eq fp_P_lt_Gam fpPoly_lnSw (fun _ hy hy1 => (fpTh_P hy hy1).symm) (fun _ hZ => fp_cl_P hZ) fp_Om1_le_P
    (fun _ hx hx1 => (fp_eN_lt_B hx hx1).trans (ltC_lt_P hx hx1 0)) lnSw_topPkg

/-- `ω^{φ(ω+1, Ω₁+1)} = φ(ω+1, Ω₁+1)`, so `Λ⁺(lnSw) = ι(φ(ω+1, Ω₁+1)·ω)`. -/
theorem fpLoc_lnSw' : xtB1 lnSw = iota S (fpPc * ω) ∧ upsilon (xtB1 lnSw) = Pv S (fpPc * ω) := by
  have e : ω ^ fpPc = fpPc := gg_veblen_eps (lt_of_le_of_lt zero_le (lt_add_one ω)).ne'
  obtain ⟨h1, h2, -⟩ := fpLoc_lnSw (S := S)
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2.Fp
