import Googology.Trans.PoR.InaccPsi.R2.GiUni

/-!
# THE FRONTIER LEMMA for the codes of a code system `K`: `Λ⁺(X) = ι(ω^T·ω)` for every top code `T ≤ Γ_{Ω₁+1+K.B}`

`R2.GhFr` for an arbitrary code system `K : GiCS` (`R2.GiAt`), the reading `gxTh y (K.At y)` and THEOREM UNI `giUni2`:
`gi_good`, `giIota_lt_L0` (**`ι(η) ≤ P(η) < L(0)`**), `giFrPt`, `giFrGen`, `giFr_exp`, `giFr_mul`, `giB1_ge`,
`giB1_eq` (**`Λ⁺(X) = ι(ω^T·ω)`, `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`**, for every term system `X` with `GiPoly K X T`, top
`Θ_y(T)`, `T` a code over every strongly critical base, `Ω₁ ≤ T ≤ K.V`, top above `ε_{x+1}`).

No new axiom.
-/
set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Gf

open Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}} {K : GiCS}

/-- A code over every strongly critical base is a good name. -/
theorem gi_good {η : Ordinal.{0}} (h : ∀ Z, SC Z → GxCl Z (K.At Z) η) : Bt.Good S η :=
  giCl_mem_CSet (gi_B_lt_A1 (S := S) K _) le_rfl (h _ (Pv_SC S η))

/-- **`ι(η) ≤ P(η) < P(Ω_ω) = L(0)`** for a code `η` over every strongly critical base. -/
theorem giIota_lt_L0 {η : Ordinal.{0}} (h : ∀ Z, SC Z → GxCl Z (K.At Z) η) :
    iota S η < Nc.ncL S 0 ∧ upsilon (iota S η) < Nc.ncL S 0 := by
  have hη : η < Om ω := ((giCl_lt_V le_rfl (h _ ph_SC_Om1)).trans (giV_lt_Om2 K S)).trans ph_Om2_lt_Omw
  have hlt : iota S η < iota S (Om ω) := cd_iota_lt_of_good (gi_good h) hη
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  have h2 : upsilon (iota S η) < Nc.ncL S 0 := by rw [hL0]; exact upsilon_normal.strictMono hlt
  exact ⟨upsilon_normal.strictMono.le_apply.trans_lt h2, h2⟩

/-- **A named frontier point**: `F = ι(η)` with `e(η) = T`. -/
theorem giFrPt {X : XtSys} {T : Ordinal.{0}} (hTG : T ≤ K.V) (hP : GiPoly K X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = gxTh y (K.At y) T) {η : Ordinal.{0}} (hηcl : ∀ Z, SC Z → GxCl Z (K.At Z) η)
    (hηlim : IsSuccLimit η) (hgap : ∀ ζ < η, ζ + Om 1 ≤ η) (he : cdExp η = T) :
    XtFr X (iota S η) ∧ upsilon (iota S η) = iota S η ∧ cdEta S (iota S η) = η ∧
      upsilon (iota S η) < Pv S (η + 1) := by
  have hg : Bt.Good S η := gi_good hηcl
  have hfix := ggFix (S := S) hηlim hgap
  have hF0 : iota S η ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota η)).ne'
  have hri := Fx.fx_ri_of_fix hF0 hfix
  have hEta : cdEta S (iota S η) = η := cdEta_unique hg rfl
  have hX : upsilon (iota S η) < Pv S (η + 1) := by
    show upsilon (iota S η) < S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ups_iota S (η + 1), iota_good hg]
    exact upsilon_normal.strictMono (lt_add_one _)
  have hO := giUni2 hTG hP (iota S η) (η + 1) hri hfix hX (by rw [hEta, he])
  have hSC := ggSC_fix hri hfix hX
  have hF1 := Fx.fx_fix_lt_Om1 hfix hX
  refine ⟨⟨hri, ?_⟩, hfix, hEta, hX⟩
  rw [hO, hEta, he, hfix, htop _ hSC hF1]

/-- **The frontiers of a system with a top code `T ≤ K.V`.** -/
theorem giFrGen {X : XtSys} {T : Ordinal.{0}} (hTG : T ≤ K.V) (hP : GiPoly K X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = gxTh y (K.At y) T) (hTcl : ∀ Z, SC Z → GxCl Z (K.At Z) T)
    (hTO : Om 1 ≤ T) :
    (∀ n : ℕ, XtFr X (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
    xtLam X ≤ iota S (ω ^ T) ∧ xtB1 X ≤ iota S (ω ^ T * ω) ∧
    iota S (ω ^ T * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 X) < Nc.ncL S 0 := by
  have hT0 : T ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) hTO).ne'
  have hcl : ∀ n : ℕ, ∀ Z, SC Z → GxCl Z (K.At Z) (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n Z hZ => by
    have := gx_mul_nat hZ.1 (GxCl.opow hZ.1 (hTcl Z hZ)) (n + 1)
    rwa [Nat.cast_succ] at this
  have hlim : ∀ n : ℕ, IsSuccLimit (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n => by
    rw [mul_add_one]; exact isSuccLimit_add _ (ph_opow_lim hT0)
  have hpt := fun n : ℕ => giFrPt (S := S) hTG hP htop (hcl n) (hlim n) (ph_gap hTO n) (cpExp_mul_succ T n)
  have hwcl : ∀ Z, SC Z → GxCl Z (K.At Z) (ω ^ T * ω) := fun Z hZ => by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact GxCl.opow hZ.1 (GxCl.add (hTcl Z hZ) (GxCl.small (gg_one_lt_of_SC hZ)))
  have hwlim : IsSuccLimit (ω ^ T * ω) := by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact ph_opow_lim (by simp)
  have hB1 : xtB1 X ≤ iota S (ω ^ T * ω) := by
    refine csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨lt_of_lt_of_le zero_lt_one (one_le_iota _),
      fun ν hν => ?_⟩)
    rw [iota_limit hwlim] at hν
    haveI : Nonempty (Iio (ω ^ T * ω)) := ⟨⟨0, hwlim.bot_lt⟩⟩
    obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hν
    obtain ⟨m, hm, hem⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 e.2
    obtain ⟨j, rfl⟩ := lt_omega0.1 hm
    have hj : ω ^ T * (j : Ordinal.{0}) ≤ ω ^ T * ((j : Ordinal.{0}) + 1) := by gcongr; exact le_self_add
    refine ⟨_, (hpt j).1, he.trans_le (iota_mono _ _ (hem.le.trans hj)), ?_⟩
    refine cd_iota_lt_of_good (gi_good (hcl j)) ?_
    refine (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 ?_
    rw [← Nat.cast_succ]; exact natCast_lt_omega0 _
  obtain ⟨hL1, hL2⟩ := giIota_lt_L0 (S := S) hwcl
  refine ⟨fun n => ⟨(hpt n).1, (hpt n).2.1⟩, ?_, hB1, hL1, (ups_mono hB1).trans_lt hL2⟩
  have h0 := (hpt 0).1
  rw [Nat.cast_zero, zero_add, mul_one] at h0
  exact xtLam_le h0.1 h0.2

section Gen

variable {X : XtSys} {T : Ordinal.{0}} (hT : T ≤ K.V) (hP : GiPoly K X T)
  (htop : ∀ y, SC y → y < Om 1 → X.top y = gxTh y (K.At y) T)
include hT hP htop

/-- **A named frontier has `e(η_λ) ≥ T`** (`T ≤ K.V`). -/
theorem giFr_exp {l ηx : Ordinal.{0}} (hl : XtFr X l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) :
    T ≤ cdExp (cdEta S l) := by
  by_contra h
  push Not at h
  have hO := giUni2 hT hP l ηx hl.1 hfix hX h.le
  have hSC := ggSC_fix hl.1 hfix hX
  have hl1 : l < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have h2 := gxTh_lt (giExpMem hl.1 hfix hX (h.trans_le hT)) h
  have h3 := hl.2
  rw [hO, hfix, htop l hSC hl1] at h3
  exact absurd h3 h2.ne

/-- **Every frontier `λ ∈ (ω², ι(ω^T·ω))` is `ι(ω^T·k)`.** -/
theorem giFr_mul (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) {l : Ordinal.{0}} (hl : XtFr X l)
    (hww : ω * ω < l) (hlt : l < iota S (ω ^ T * ω)) (hl1 : l < Om1) :
    ∃ k : ℕ, l = iota S (ω ^ T * (k : Ordinal.{0})) := by
  have hfix := ggFr_fix htopE hl hl1 hww
  have hX : upsilon l < Pv S (ω ^ T * ω) := by
    have h := upsilon_normal.strictMono hlt
    rw [ups_iota S] at h
    exact h
  have he := giFr_exp (S := S) hT hP htop hl hfix hX
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

/-- **`ι(ω^T·ω) ≤ Λ⁺(X)`** (`T ≤ K.V`). -/
theorem giB1_ge (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
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
  obtain ⟨k, hk⟩ := giFr_mul (S := S) hT hP htop htopE hμ hww (h2.trans hlt) (h2.trans hb1)
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

/-- **`Λ⁺(X) = ι(ω^T·ω)` and `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`** (`T ≤ K.V`). -/
theorem giB1_eq (hTcl : ∀ Z, SC Z → GxCl Z (K.At Z) T) (hTO : Om 1 ≤ T)
    (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    xtB1 X = iota S (ω ^ T * ω) ∧ upsilon (xtB1 X) = Pv S (ω ^ T * ω) ∧ Pv S (ω ^ T * ω) < Nc.ncL S 0 := by
  have hup := (giFrGen (S := S) hT hP htop hTcl hTO).2.2
  have heq : xtB1 X = iota S (ω ^ T * ω) := le_antisymm hup.1 (giB1_ge hT hP htop hTO htopE hPk)
  have hups : upsilon (xtB1 X) = Pv S (ω ^ T * ω) := by rw [heq, ups_iota S]
  exact ⟨heq, hups, hups ▸ hup.2.2⟩

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Gi
