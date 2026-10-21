import Googology.Trans.PoR.InaccPsi.R2.LgPh

/-!
# The frontiers of the layers over `Γ`: `Λ⁺ = ι(ω^T·ω)` for every top code `T < Γ'`, and `Λ^Γ_{ω²}`

`R2.PhFr` (`phFrPt`, `phFrGen`) and `R2.FpLoc` (`fpFr_exp`, `fpFr_mul`, `fpB1_ge`, `fpB1_eq`) with the codes `LgCl`,
the reading `Θ' = lgTh` and THEOREM UNI `lgUni2` (`E ≤ Γ'`):

* `lgCl_lt_Gam'` (a code over `Ω₁` is below `Γ'`), `lg_good` (a code over every strongly critical base is a good
  name), `lgIota_lt_L0` (**`ι(η) ≤ P(η) < L(0)`** for such a code);
* `lgFrPt2` (**`ι(η)` with `e(η) = T` a named fixed point and a frontier**), `lgFrGen2` (**every `ι(ω^T·(n+1))` is a
  frontier, `Λ(X) ≤ ι(ω^T)`, `Λ⁺(X) ≤ ι(ω^T·ω) < L(0)`**), `lgFr2_exp`, `lgFr2_mul`, `lgB1_ge2`, `lgB1_eq2`
  (**`Λ⁺(X) = ι(ω^T·ω)`, `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`**);
* the instances: `lgLL_loc` (**`Λ⁺((lgLL k).iter n) = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·(ω·k + n)}}·ω)`**, its `ρ` below `L(0)`),
  `lgW2_loc` (**`Λ^Γ_{ω²} = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·ω·ω}})`**, `ρ` below `L(0)`), `lgW2T_fix` (**the notation hypothesis
  at every fixed point of the range below `Λ^Γ_{ω²}`, proved**), `lgW2EnumAll` (**ENUM-REACH at every restart of the
  range below `Λ^Γ_{ω²}`**), `lgW2RoadPh` (**the road with UPPER/LOWER asked only at `λ ≥ Λ^Γ_{ω²}`**),
  `lgW2_fr_order`.

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cp

variable {S : InaccSeq.{0}}

/-- A code over `Ω₁` is below `Γ'`. -/
theorem lgCl_lt_Gam' (S : InaccSeq.{0}) {c : Ordinal.{0}} (hc : LgCl (Om 1) c) : c < lgGam' := by
  obtain ⟨hSC, hG⟩ := lgGam'_spec S
  induction hc with
  | small h => exact h.trans (ggGam_spec.2.trans hG)
  | om => exact ggGam_spec.2.trans hG
  | gam => exact hG
  | add _ _ ihx ihy => exact hSC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hSC.2 _ ihx _ ihy

/-- A code over every strongly critical base is a good name. -/
theorem lg_good {η : Ordinal.{0}} (h : ∀ Z, SC Z → LgCl Z η) : Bt.Good S η :=
  (h _ (Pv_SC S η)).mem_CSet (lt_of_le_of_lt zero_le (lt_add_one _)) le_rfl

/-- **`ι(η) ≤ P(η) < P(Ω_ω) = L(0)`** for a code `η` over every strongly critical base. -/
theorem lgIota_lt_L0 {η : Ordinal.{0}} (h : ∀ Z, SC Z → LgCl Z η) :
    iota S η < Nc.ncL S 0 ∧ upsilon (iota S η) < Nc.ncL S 0 := by
  have hη : η < Om ω := ((lgCl_lt_Gam' S (h _ ph_SC_Om1)).trans (lgGam'_lt_Om2 S)).trans ph_Om2_lt_Omw
  have hlt : iota S η < iota S (Om ω) := cd_iota_lt_of_good (lg_good h) hη
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  have h2 : upsilon (iota S η) < Nc.ncL S 0 := by rw [hL0]; exact upsilon_normal.strictMono hlt
  exact ⟨upsilon_normal.strictMono.le_apply.trans_lt h2, h2⟩

/-- **A named frontier point**: `F = ι(η)` with `e(η) = T`. -/
theorem lgFrPt2 {X : XtSys} {T : Ordinal.{0}} (hTG : T ≤ lgGam') (hP : LgPoly X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = lgTh y T) {η : Ordinal.{0}} (hηcl : ∀ Z, SC Z → LgCl Z η)
    (hηlim : IsSuccLimit η) (hgap : ∀ ζ < η, ζ + Om 1 ≤ η) (he : cdExp η = T) :
    XtFr X (iota S η) ∧ upsilon (iota S η) = iota S η ∧ cdEta S (iota S η) = η ∧
      upsilon (iota S η) < Pv S (η + 1) := by
  have hg : Bt.Good S η := lg_good hηcl
  have hfix := ggFix (S := S) hηlim hgap
  have hF0 : iota S η ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota η)).ne'
  have hri := Fx.fx_ri_of_fix hF0 hfix
  have hEta : cdEta S (iota S η) = η := cdEta_unique hg rfl
  have hX : upsilon (iota S η) < Pv S (η + 1) := by
    show upsilon (iota S η) < S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ups_iota S (η + 1), iota_good hg]
    exact upsilon_normal.strictMono (lt_add_one _)
  have hO := lgUni2 hTG hP (iota S η) (η + 1) hri hfix hX (by rw [hEta, he])
  have hSC := ggSC_fix hri hfix hX
  have hF1 := Fx.fx_fix_lt_Om1 hfix hX
  refine ⟨⟨hri, ?_⟩, hfix, hEta, hX⟩
  rw [hO, hEta, he, hfix, htop _ hSC hF1]

/-- **The frontiers of a system with a top code `T < Γ'`.** -/
theorem lgFrGen2 {X : XtSys} {T : Ordinal.{0}} (hTG : T ≤ lgGam') (hP : LgPoly X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = lgTh y T) (hTcl : ∀ Z, SC Z → LgCl Z T) (hTO : Om 1 ≤ T) :
    (∀ n : ℕ, XtFr X (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
    xtLam X ≤ iota S (ω ^ T) ∧ xtB1 X ≤ iota S (ω ^ T * ω) ∧
    iota S (ω ^ T * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 X) < Nc.ncL S 0 := by
  have hT0 : T ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) hTO).ne'
  have hcl : ∀ n : ℕ, ∀ Z, SC Z → LgCl Z (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n Z hZ => by
    have := LgCl.mul_nat hZ.1 (LgCl.opow hZ.1 (hTcl Z hZ)) (n + 1)
    rwa [Nat.cast_succ] at this
  have hlim : ∀ n : ℕ, IsSuccLimit (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n => by
    rw [mul_add_one]; exact isSuccLimit_add _ (ph_opow_lim hT0)
  have hpt := fun n : ℕ => lgFrPt2 (S := S) hTG hP htop (hcl n) (hlim n) (ph_gap hTO n) (cpExp_mul_succ T n)
  have hwcl : ∀ Z, SC Z → LgCl Z (ω ^ T * ω) := fun Z hZ => by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact LgCl.opow hZ.1 (LgCl.add (hTcl Z hZ) (LgCl.small (gg_one_lt_of_SC hZ)))
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
    refine cd_iota_lt_of_good (lg_good (hcl j)) ?_
    refine (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 ?_
    rw [← Nat.cast_succ]; exact natCast_lt_omega0 _
  obtain ⟨hL1, hL2⟩ := lgIota_lt_L0 (S := S) hwcl
  refine ⟨fun n => ⟨(hpt n).1, (hpt n).2.1⟩, ?_, hB1, hL1, (ups_mono hB1).trans_lt hL2⟩
  have h0 := (hpt 0).1
  rw [Nat.cast_zero, zero_add, mul_one] at h0
  exact xtLam_le h0.1 h0.2

section Gen

variable {X : XtSys} {T : Ordinal.{0}} (hT : T ≤ lgGam') (hP : LgPoly X T)
  (htop : ∀ y, SC y → y < Om 1 → X.top y = lgTh y T)
include hT hP htop

/-- **A named frontier has `e(η_λ) ≥ T`** (`T ≤ Γ'`). -/
theorem lgFr2_exp {l ηx : Ordinal.{0}} (hl : XtFr X l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) :
    T ≤ cdExp (cdEta S l) := by
  by_contra h
  push Not at h
  have hO := lgUni2 hT hP l ηx hl.1 hfix hX h.le
  have hSC := ggSC_fix hl.1 hfix hX
  have hl1 : l < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have h2 := lgTh_lt (lgExpMem hl.1 hfix hX (h.trans_le hT)) h
  have h3 := hl.2
  rw [hO, hfix, htop l hSC hl1] at h3
  exact absurd h3 h2.ne

/-- **Every frontier `λ ∈ (ω², ι(ω^T·ω))` is `ι(ω^T·k)`.** -/
theorem lgFr2_mul (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) {l : Ordinal.{0}} (hl : XtFr X l)
    (hww : ω * ω < l) (hlt : l < iota S (ω ^ T * ω)) (hl1 : l < Om1) :
    ∃ k : ℕ, l = iota S (ω ^ T * (k : Ordinal.{0})) := by
  have hfix := ggFr_fix htopE hl hl1 hww
  have hX : upsilon l < Pv S (ω ^ T * ω) := by
    have h := upsilon_normal.strictMono hlt
    rw [ups_iota S] at h
    exact h
  have he := lgFr2_exp (S := S) hT hP htop hl hfix hX
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

/-- **`ι(ω^T·ω) ≤ Λ⁺(X)`** (`T ≤ Γ'`). -/
theorem lgB1_ge2 (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
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
  obtain ⟨k, hk⟩ := lgFr2_mul (S := S) hT hP htop htopE hμ hww (h2.trans hlt) (h2.trans hb1)
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

/-- **`Λ⁺(X) = ι(ω^T·ω)` and `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`** (`T ≤ Γ'`). -/
theorem lgB1_eq2 (hTcl : ∀ Z, SC Z → LgCl Z T) (hTO : Om 1 ≤ T)
    (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    xtB1 X = iota S (ω ^ T * ω) ∧ upsilon (xtB1 X) = Pv S (ω ^ T * ω) ∧ Pv S (ω ^ T * ω) < Nc.ncL S 0 := by
  have hup := (lgFrGen2 (S := S) hT hP htop hTcl hTO).2.2
  have heq : xtB1 X = iota S (ω ^ T * ω) := le_antisymm hup.1 (lgB1_ge2 hT hP htop hTO htopE hPk)
  have hups : upsilon (xtB1 X) = Pv S (ω ^ T * ω) := by rw [heq, ups_iota S]
  exact ⟨heq, hups, hups ▸ hup.2.2⟩

end Gen

/-! ## The instances: the layers over `Γ` -/

theorem lg_cl_LLiter (k n : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ (lgLLe k + Om 1 * n)) :=
  LgCl.opow hZ.1 (LgCl.add (lg_cl_LLe k hZ) (LgCl.mul_nat hZ.1 LgCl.om n))

theorem lg_Om1_le_LLiter (k n : ℕ) : Om 1 ≤ ω ^ (lgLLe k + Om 1 * n) := by
  calc Om 1 ≤ ggGam := ggGam_spec.2.le
    _ = ω ^ ggGam := lg_Gam_eps.symm
    _ ≤ ω ^ (lgLLe k + Om 1 * n) := opow_le_opow_right omega0_pos (le_self_add.trans le_self_add)

theorem lg_LLiter_lt (S : InaccSeq.{0}) (k n : ℕ) : ω ^ (lgLLe k + Om 1 * n) ≤ lgGam' :=
  (lgCl_lt_Gam' S (lg_cl_LLiter k n ph_SC_Om1)).le

theorem lgLL_topE (k n : ℕ) (x : Ordinal.{0}) (hx : InE x) (hx1 : x < Om1) :
    eN x < ((lgLL k).iter n).sys.top x := by
  rw [lgLL_iter_top]
  have hG := gT_lt_lgG hx hx1 0
  have h1 : (1 : Ordinal.{0}) ≤ x ^ (ω * (k : Ordinal.{0}) + (n : Ordinal.{0})) :=
    one_le_iff_pos.2 (opow_pos _ hx.pos)
  exact hG.trans_le (le_mul_of_one_le_right zero_le h1)

/-- **`Λ⁺((lgLL k).iter n) = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·ω·k + Ω₁·n}}·ω)`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lgLL_loc (k n : ℕ) :
    xtB1 ((lgLL k).iter n).sys = iota S (ω ^ ω ^ (lgLLe k + Om 1 * n) * ω) ∧
      upsilon (xtB1 ((lgLL k).iter n).sys) = Pv S (ω ^ ω ^ (lgLLe k + Om 1 * n) * ω) ∧
      Pv S (ω ^ ω ^ (lgLLe k + Om 1 * n) * ω) < Nc.ncL S 0 :=
  lgB1_eq2 (lg_LLiter_lt S k n) (lgPoly_LLiter k n).1 (lgPoly_LLiter k n).2 (fun _ hZ => lg_cl_LLiter k n hZ)
    (lg_Om1_le_LLiter k n) (fun x hx hx1 => lgLL_topE k n x hx hx1) ((lgLL k).iter n).topPkg

theorem lgLamK_loc (k : ℕ) : lgLamK k = iota S (ω ^ ω ^ lgLLe k * ω) := by
  have h := (lgLL_loc (S := S) k 0).1
  simp only [Nat.cast_zero, mul_zero, add_zero] at h
  exact h

/-- **The notation hypothesis at every fixed point of the range below `Λ^Γ_{ω²}`**: `Θ_λ(m_λ) = O_{LL k}(λ)`. -/
theorem lgW2T_fix (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlk : l < lgLamK k) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec (lgLL k).sys l := by
  have hP := lgPoly_LLiter k 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hP
  have hlt : l < iota S (ω ^ ω ^ lgLLe k * ω) := by rw [← lgLamK_loc]; exact hlk
  have hT : ω ^ lgLLe k ≤ lgGam' := by
    have := lg_LLiter_lt S k 0; simpa using this
  exact lgUniTh hT (by simpa using hP.1) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **ENUM-REACH at every restart of the range below `Λ^Γ_{ω²}`**, fixed points of `υ` included. -/
theorem lgW2EnumAll {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lgFamW2.famSup) : CdUpper S l ∧ CdLower S l :=
  lgW2Enum (fun k l hr _ hlk hfix => lgW2T_fix k hr hlk hfix) hr hl

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ^Γ_{ω²}`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lgW2RoadPh (hU : ∀ l, CdRange S l → lgFamW2.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lgFamW2.famSup ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lgFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lgW2Road3 hU hL (fun k l hr _ hlk hfix => lgW2T_fix k hr hlk hfix) hV hC hEQ hrest hB2

/-- The exponent `Γ_{Ω₁+1} + Ω₁·ω·ω` of `Λ^Γ_{ω²}`. -/
noncomputable def lgW2e : Ordinal.{0} := ggGam + Om 1 * ω * ω

theorem lg_cl_W2e {Z : Ordinal.{0}} (hZ : SC Z) : LgCl Z (ω ^ ω ^ lgW2e) := by
  have h1 : LgCl Z (Om 1 * ω * ω) := by
    rw [show Om 1 * ω * ω = ω ^ (Om 1 + 1 + 1) by rw [opow_add, opow_add, opow_one, Om1_opow]]
    exact LgCl.opow hZ.1 (LgCl.add (lg_cl_Om1_one hZ) (LgCl.small (gg_one_lt_of_SC hZ)))
  exact LgCl.opow hZ.1 (LgCl.opow hZ.1 (LgCl.add LgCl.gam h1))

/-- **`Λ^Γ_{ω²} = ι(ω^{ω^{Γ_{Ω₁+1} + Ω₁·ω·ω}})`, `ρ` of it `= P(…) < L(0)`.** -/
theorem lgW2_loc : lgFamW2.famSup = iota S (ω ^ ω ^ lgW2e) ∧
    upsilon lgFamW2.famSup = Pv S (ω ^ ω ^ lgW2e) ∧ Pv S (ω ^ ω ^ lgW2e) < Nc.ncL S 0 := by
  have hstep : ∀ k : ℕ, ω ^ ω ^ lgLLe k * ω < ω ^ ω ^ lgW2e := by
    intro k
    have hk : lgLLe k < lgW2e := by
      unfold lgLLe lgW2e
      refine (add_lt_add_iff_left _).2 ?_
      exact (mul_lt_mul_iff_right₀ (mul_pos (Om_pos one_ne_zero) omega0_pos)).2 (natCast_lt_omega0 k)
    have h1 : ω ^ lgLLe k + 1 < ω ^ lgW2e := by
      have hp : ω ^ lgLLe k < ω ^ lgW2e := (opow_lt_opow_iff_right one_lt_omega0).2 hk
      have hlim := ph_opow_lim (c := lgW2e) (lt_of_le_of_lt zero_le hk).ne'
      exact hlim.add_one_lt hp
    rw [show ω ^ ω ^ lgLLe k * ω = ω ^ (ω ^ lgLLe k + 1) by rw [opow_add, opow_one]]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 h1
  have hW0 : lgW2e ≠ 0 := (lt_of_lt_of_le ggGam_spec.1.1 le_self_add).ne'
  have hlim : IsSuccLimit (ω ^ ω ^ lgW2e) := ph_opow_lim (opow_pos _ omega0_pos).ne'
  have heq : lgFamW2.famSup = iota S (ω ^ ω ^ lgW2e) := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show lgLamK k ≤ _
      rw [lgLamK_loc (S := S) k]
      exact iota_mono _ _ (hstep k).le
    · rw [iota_limit hlim]
      refine ciSup_le' fun e => ?_
      -- every `e < ω^{ω^{lgW2e}}` lies below some `ω^{ω^{lgLLe k}}·ω`
      have he := e.2
      rcases eq_or_ne e.1 0 with h0 | h0
      · rw [h0]
        exact (iota_mono _ _ zero_le).trans ((lgLamK_loc (S := S) 0).symm.le.trans (lgFamW2.famBd_lt 0).le)
      have hL : log ω e.1 < ω ^ lgW2e := (lt_opow_iff_log_lt one_lt_omega0 h0).1 he
      have hL2 : ∃ k : ℕ, log ω e.1 < ω ^ lgLLe k := by
        rcases eq_or_ne (log ω e.1) 0 with hl0 | hl0
        · exact ⟨0, by rw [hl0]; exact opow_pos _ omega0_pos⟩
        have hLL : log ω (log ω e.1) < lgW2e := (lt_opow_iff_log_lt one_lt_omega0 hl0).1 hL
        have hm : ∃ k : ℕ, log ω (log ω e.1) < lgLLe k := by
          rcases lt_or_ge (log ω (log ω e.1)) ggGam with h | h
          · exact ⟨0, by unfold lgLLe; rw [Nat.cast_zero, mul_zero, add_zero]; exact h⟩
          · obtain ⟨t, ht⟩ := exists_add_of_le h
            have hLL' := hLL
            unfold lgW2e at hLL'
            rw [ht] at hLL'
            have ht' : t < Om 1 * ω * ω := (add_lt_add_iff_left _).1 hLL'
            obtain ⟨m, hm, htm⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 ht'
            obtain ⟨n, rfl⟩ := lt_omega0.1 hm
            exact ⟨n, by unfold lgLLe; rw [ht]; exact (add_lt_add_iff_left _).2 htm⟩
        obtain ⟨k, hk⟩ := hm
        exact ⟨k, (lt_opow_succ_log_self one_lt_omega0 _).trans_le
          (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hk))⟩
      obtain ⟨k, hk⟩ := hL2
      have h1 : e.1 < ω ^ ω ^ lgLLe k * ω := by
        refine (lt_opow_succ_log_self one_lt_omega0 _).trans_le ?_
        rw [show ω ^ ω ^ lgLLe k * ω = ω ^ (ω ^ lgLLe k + 1) by rw [opow_add, opow_one]]
        exact opow_le_opow_right omega0_pos ((Order.succ_le_of_lt hk).trans le_self_add)
      calc iota S e.1 ≤ iota S (ω ^ ω ^ lgLLe k * ω) := iota_mono _ _ h1.le
        _ = lgLamK k := (lgLamK_loc k).symm
        _ ≤ lgFamW2.famSup := (lgFamW2.famBd_lt k).le
  have hups : upsilon lgFamW2.famSup = Pv S (ω ^ ω ^ lgW2e) := by rw [heq, ups_iota S]
  refine ⟨heq, hups, ?_⟩
  rw [← hups]
  have := (lgIota_lt_L0 (S := S) (fun Z hZ => lg_cl_W2e hZ)).2
  rwa [← heq] at this

/-- **Where `Λ^Γ_{ω²}` lies**: `ρ(Λ⁺(lgUSys)) < ρ(Λ^Γ_{ω²}) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and
`Λ^Γ_{ω²} < L(ω+1)`, unconditionally. -/
theorem lgW2_fr_order (k : ℕ) :
    upsilon (xtB1 lgUSys) < upsilon lgFamW2.famSup ∧ upsilon lgFamW2.famSup < Nc.ncL S 0 ∧
    Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    lgFamW2.famSup < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨-, hups, hlt⟩ := lgW2_loc (S := S)
  have hU : upsilon lgFamW2.famSup < Nc.ncL S 0 := hups ▸ hlt
  refine ⟨upsilon_normal.strictMono lgU_B1_lt_W2, hU, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
