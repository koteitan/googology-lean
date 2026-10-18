import Googology.Trans.PoR.InaccPsi.R2.PhLz
import Googology.Trans.PoR.InaccPsi.R2.GgFront
import Googology.Trans.PoR.InaccPsi.R2.LwName
import Googology.Trans.PoR.InaccPsi.R2.PpIdx
import Googology.Trans.PoR.InaccPsi.R2.QqName

/-!
# The frontiers below `L(0)`: named frontier points `ι(ω^T·(n+1))` and `Λ⁺ ≤ ι(ω^T·ω)`

For a term system `X` with a top code `T` (`Θ_y(T) = top(y)`, `Ω₁ ≤ T < ggGam`, terms for the codes below `T`):

* `phGood` (a code over every strongly critical base is a good name), `phIota_lt_L0` (**a code `η` has
  `ι(η) ≤ υ_{ι(η)} = P(η) < P(Ω_ω) = L(0)`**);
* `phFrPt` (**`F = ι(η)` with `e(η) = T`, `η` a limit with `ζ + Ω₁ ≤ η` below it, is a named fixed point of `υ` with
  `O_X(F) = top(F)`**, by THEOREM UNI);
* `phFrGen` (**every `ι(ω^T·(n+1))` is a frontier of `X`; `Λ(X) ≤ ι(ω^T)`, `Λ⁺(X) ≤ ι(ω^T·ω) < L(0)` and
  `υ_{Λ⁺(X)} < L(0)`**);
* the instances: `phFr_vz` (`Λ_B ≤ ι(phB)`, `cpB1 ≤ ι(phB·ω) < L(0)`; `O(ι(phB)) = B(ρ)` at the named fixed point
  `ι(phB)`, `phB = φ(ω, Ω₁ + 1) < Ω_ω`), `phFr_LL` (`Λ⁺_k ≤ ι(ω^{ω^{phLLe k}}·ω)`), `phFr_W2` (`Λ_{ω²} ≤
  ι(ω^{ω^{phB + Ω₁·ω·ω}}) < L(0)`), `phFr_lyE` (`Λ⁺(lyEB) ≤ ι(phEB·ω) < L(0)`), `phFr_lzZ`, `phFr_lzV`, `phFr_lzW`,
  `phFr_Y` (`Λ⁺_Y = sup_K Λ⁺(lzWs (K+2)) ≤ ι(ω^{φ(ω, Ω₁ + ω)}) < L(0)`);
* `phL_chain` (`L(0) ≤ L(n+1) < L(ω) < L(ω+1)`), `phFr_order` (**every `ρ` of these frontiers is below `L(0)`,
  `L(n+1)`, `L(ω)`, and `cpB1`, `Λ⁺_Y < L(ω+1)`**, unconditionally: no `ν_C ≤ L(ω+1)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Lz

variable {S : InaccSeq.{0}}

/-- A code over every strongly critical base is a good name. -/
theorem phGood {η : Ordinal.{0}} (h : ∀ Z, SC Z → GgCl Z η) : Bt.Good S η :=
  (h _ (Pv_SC S η)).mem_CSet le_rfl

theorem ph_Om2_lt_Omw : Om (1 + 1 : Ordinal.{0}) < Om ω := by
  refine Om_lt_Om.2 ?_
  have : (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) := by norm_num
  rw [this]; exact natCast_lt_omega0 2

theorem ph_Gam_lt_Omw : ggGam < Om ω := ggGam_le_Om2.trans_lt ph_Om2_lt_Omw

/-- **`ι(η) ≤ P(η) < P(Ω_ω) = L(0)`** for a code `η` over every strongly critical base. -/
theorem phIota_lt_L0 {η : Ordinal.{0}} (h : ∀ Z, SC Z → GgCl Z η) :
    iota S η < Nc.ncL S 0 ∧ upsilon (iota S η) < Nc.ncL S 0 := by
  have hη : η < Om ω := (ph_lt_Gam (h _ ph_SC_Om1)).trans ph_Gam_lt_Omw
  have hlt : iota S η < iota S (Om ω) := cd_iota_lt_of_good (phGood h) hη
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  have h2 : upsilon (iota S η) < Nc.ncL S 0 := by rw [hL0]; exact upsilon_normal.strictMono hlt
  exact ⟨upsilon_normal.strictMono.le_apply.trans_lt h2, h2⟩

theorem ph_gap {T : Ordinal.{0}} (hTO : Om 1 ≤ T) (n : ℕ) :
    ∀ ζ < ω ^ T * ((n : Ordinal.{0}) + 1), ζ + Om 1 ≤ ω ^ T * ((n : Ordinal.{0}) + 1) := by
  intro ζ hζ
  have hOm : Om 1 ≤ ω ^ T := by rw [← Om1_opow]; exact opow_le_opow_right omega0_pos hTO
  have hp1 : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
    rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
  rw [mul_add_one] at hζ ⊢
  rcases lt_or_ge ζ (ω ^ T * n) with h | h
  · calc ζ + Om 1 ≤ ω ^ T * n + Om 1 := by gcongr
      _ ≤ ω ^ T * n + ω ^ T := (add_le_add_iff_left _).2 hOm
  · obtain ⟨s, rfl⟩ := exists_add_of_le h
    have hs : s < ω ^ T := (add_lt_add_iff_left _).1 hζ
    rw [add_assoc]
    refine (add_le_add_iff_left _).2 ?_
    rcases hOm.lt_or_eq with hlt | heq
    · exact (isPrincipal_add_omega0_opow T hs hlt).le
    · rw [← heq] at hs ⊢; exact (hp1.add_eq_right hs).le

/-- **A named frontier point**: `F = ι(η)` with `e(η) = T`. -/
theorem phFrPt {X : XtSys} {T : Ordinal.{0}} (hTG : T < ggGam) (hP : PhPolyR X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = ggTh y T) {η : Ordinal.{0}} (hηcl : ∀ Z, SC Z → GgCl Z η)
    (hηlim : IsSuccLimit η) (hgap : ∀ ζ < η, ζ + Om 1 ≤ η) (he : cdExp η = T) :
    XtFr X (iota S η) ∧ upsilon (iota S η) = iota S η ∧ cdEta S (iota S η) = η ∧
      upsilon (iota S η) < Pv S (η + 1) := by
  have hg : Bt.Good S η := phGood hηcl
  have hfix := ggFix (S := S) hηlim hgap
  have hF0 : iota S η ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota η)).ne'
  have hri := Fx.fx_ri_of_fix hF0 hfix
  have hEta : cdEta S (iota S η) = η := cdEta_unique hg rfl
  have hX : upsilon (iota S η) < Pv S (η + 1) := by
    show upsilon (iota S η) < S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ups_iota S (η + 1), iota_good hg]
    exact upsilon_normal.strictMono (lt_add_one _)
  have hO := phUni hTG.le hP (iota S η) (η + 1) hri hfix hX (by rw [hEta, he])
  have hSC := ggSC_fix hri hfix hX
  have hF1 := Fx.fx_fix_lt_Om1 hfix hX
  refine ⟨⟨hri, ?_⟩, hfix, hEta, hX⟩
  rw [hO, hEta, he, hfix, htop _ hSC hF1]

/-- **The frontiers of a system with a top code `T`.** -/
theorem phFrGen {X : XtSys} {T : Ordinal.{0}} (hTG : T < ggGam) (hP : PhPolyR X T)
    (htop : ∀ y, SC y → y < Om 1 → X.top y = ggTh y T) (hTcl : ∀ Z, SC Z → GgCl Z T) (hTO : Om 1 ≤ T) :
    (∀ n : ℕ, XtFr X (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
    xtLam X ≤ iota S (ω ^ T) ∧ xtB1 X ≤ iota S (ω ^ T * ω) ∧
    iota S (ω ^ T * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 X) < Nc.ncL S 0 := by
  have hT0 : T ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) hTO).ne'
  have hcl : ∀ n : ℕ, ∀ Z, SC Z → GgCl Z (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n Z hZ => by
    have := GgCl.mul_nat hZ.1 (GgCl.opow hZ.1 (hTcl Z hZ)) (n + 1)
    rwa [Nat.cast_succ] at this
  have hlim : ∀ n : ℕ, IsSuccLimit (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n => by
    rw [mul_add_one]; exact isSuccLimit_add _ (ph_opow_lim hT0)
  have hpt := fun n : ℕ => phFrPt (S := S) hTG hP htop (hcl n) (hlim n) (ph_gap hTO n) (cpExp_mul_succ T n)
  have hwcl : ∀ Z, SC Z → GgCl Z (ω ^ T * ω) := fun Z hZ => by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact GgCl.opow hZ.1 (GgCl.add (hTcl Z hZ) (GgCl.small (gg_one_lt_of_SC hZ)))
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
    refine cd_iota_lt_of_good (phGood (hcl j)) ?_
    refine (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 ?_
    rw [← Nat.cast_succ]; exact natCast_lt_omega0 _
  obtain ⟨hL1, hL2⟩ := phIota_lt_L0 (S := S) hwcl
  refine ⟨fun n => ⟨(hpt n).1, (hpt n).2.1⟩, ?_, hB1, hL1, (ups_mono hB1).trans_lt hL2⟩
  have h0 := (hpt 0).1
  rw [Nat.cast_zero, zero_add, mul_one] at h0
  exact xtLam_le h0.1 h0.2

/-! ## The instances -/

theorem ph_Om1_le_B : Om 1 ≤ phB := ((lt_add_one _).trans_le (right_le_veblen _ _)).le

/-- The name `η* = phB` of the frontier point `λ* = ι(phB)` is below `Ω_ω`. -/
theorem ph_B_lt_Omw : phB < Om ω := ph_B_lt_Gam.trans ph_Gam_lt_Omw

/-- **`vzSys`**: `ι(phB)` is a named fixed point of `υ` with `VzOrec = B(ρ)` there; `Λ_B ≤ ι(phB)`,
`cpB1 = Λ_B⁺ ≤ ι(phB·ω) < L(0)`, `υ_{cpB1} < L(0)`. -/
theorem phFr_vz : (VzOrec (iota S phB) = VzB (upsilon (iota S phB)) ∧ upsilon (iota S phB) = iota S phB ∧
      cdEta S (iota S phB) = phB ∧ upsilon (iota S phB) < Pv S (phB + 1)) ∧
    VzLam ≤ iota S phB ∧ cpB1 ≤ iota S (phB * ω) ∧ iota S (phB * ω) < Nc.ncL S 0 ∧
    upsilon cpB1 < Nc.ncL S 0 := by
  have htop : ∀ y, SC y → y < Om 1 → vzSys.top y = ggTh y phB := fun y hy hy1 => (phTh_B hy hy1).symm
  obtain ⟨-, hLam, hB1, hL, hups⟩ := phFrGen (S := S) ph_B_lt_Gam (phPolyR_of phPoly_vz) htop
    (fun _ hZ => ph_cl_B hZ) ph_Om1_le_B
  have hlim : IsSuccLimit phB := by rw [← ph_B_eps]; exact ph_opow_lim (by
    intro h; have := ph_Om1_le_B; rw [h] at this; exact absurd this (not_le.2 (Om_pos one_ne_zero)))
  obtain ⟨hfr, hfix, hEta, hX⟩ := phFrPt (S := S) ph_B_lt_Gam (phPolyR_of phPoly_vz) htop
    (fun _ hZ => ph_cl_B hZ) hlim (by
      have := ph_gap ph_Om1_le_B 0
      rwa [Nat.cast_zero, zero_add, mul_one, ph_B_eps] at this) (ggExp_eps ph_B_eps (lt_of_lt_of_le (Om_pos one_ne_zero) ph_Om1_le_B).ne')
  rw [ph_B_eps, xtVz_lam] at hLam
  rw [ph_B_eps, xtVz_B1] at hB1
  rw [ph_B_eps] at hL
  rw [xtVz_B1] at hups
  refine ⟨⟨?_, hfix, hEta, hX⟩, hLam, hB1, hL, hups⟩
  have := hfr.2; rwa [xtVz_orec] at this

theorem ph_cl_LLtop (k : ℕ) {Z : Ordinal.{0}} (hZ : SC Z) : GgCl Z (ω ^ phLLe k) := GgCl.opow hZ.1 (ph_cl_LLe k hZ)

theorem ph_Om1_le_LL (k : ℕ) : Om 1 ≤ ω ^ phLLe k :=
  ph_Om1_le_B.trans ((le_self_add : phB ≤ phLLe k).trans (right_le_opow _ one_lt_omega0))

/-- **`xtLL k`**: `Λ⁺_k ≤ ι(ω^{ω^{phLLe k}}·ω) < L(0)`. -/
theorem phFr_LL (k : ℕ) : xtLamK k ≤ iota S (ω ^ (ω ^ phLLe k) * ω) ∧
    iota S (ω ^ (ω ^ phLLe k) * ω) < Nc.ncL S 0 ∧ upsilon (xtLamK k) < Nc.ncL S 0 := by
  obtain ⟨-, -, hB1, hL, hups⟩ := phFrGen (S := S) (ph_LL_lt_Gam k) (phPolyR_of (phPoly_LL k).1)
    (phPoly_LL k).2 (fun _ hZ => ph_cl_LLtop k hZ) (ph_Om1_le_LL k)
  exact ⟨hB1, hL, hups⟩

/-- The exponent `phB + ω^{Ω₁+2}` bounding all `phLLe k`. -/
noncomputable def phW2e : Ordinal.{0} := phB + ω ^ (Om 1 + 1 + 1)

theorem ph_cl_W2e {Z : Ordinal.{0}} (hZ : SC Z) : GgCl Z phW2e :=
  GgCl.add (ph_cl_B hZ) (GgCl.opow hZ.1 (GgCl.add (ph_cl_Om1_one hZ) (ph_cl_one hZ)))

theorem ph_LLe_lt (k : ℕ) : phLLe k < phW2e := by
  refine (add_lt_add_iff_left _).2 ?_
  have e : Om (1 : Ordinal.{0}) * ω = ω ^ (Om 1 + 1) := by rw [opow_add, opow_one, Om1_opow]
  rw [e, opow_add (a := ω) (Om 1 + 1) 1, opow_one]
  exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (natCast_lt_omega0 k)

theorem ph_opow_succ_le {a a' : Ordinal.{0}} (h : a < a') : ω ^ (ω ^ a) * ω ≤ ω ^ (ω ^ a') := by
  rw [← opow_succ]
  refine opow_le_opow_right omega0_pos (Order.succ_le_of_lt ?_)
  exact (opow_lt_opow_iff_right one_lt_omega0).2 h

/-- **`Λ_{ω²} = sup_k Λ⁺_k ≤ ι(ω^{ω^{phW2e}}) < L(0)`**, `υ_{Λ_{ω²}} < L(0)`. -/
theorem phFr_W2 : xtFamW2.famSup ≤ iota S (ω ^ (ω ^ phW2e)) ∧ iota S (ω ^ (ω ^ phW2e)) < Nc.ncL S 0 ∧
    upsilon xtFamW2.famSup < Nc.ncL S 0 := by
  have hcl : ∀ Z, SC Z → GgCl Z (ω ^ (ω ^ phW2e)) := fun Z hZ => GgCl.opow hZ.1 (GgCl.opow hZ.1 (ph_cl_W2e hZ))
  have hle : xtFamW2.famSup ≤ iota S (ω ^ (ω ^ phW2e)) :=
    Ordinal.iSup_le fun k => (phFr_LL (S := S) k).1.trans (iota_mono _ _ (ph_opow_succ_le (ph_LLe_lt k)))
  obtain ⟨h1, h2⟩ := phIota_lt_L0 (S := S) hcl
  exact ⟨hle, h1, (ups_mono hle).trans_lt h2⟩

theorem ph_Om1_le_EB : Om 1 ≤ phEB := ph_Om1_le_B.trans ph_B_lt_EB.le

/-- **`lyEB`**: `Λ(lyEB) ≤ ι(phEB)`, `Λ⁺(lyEB) ≤ ι(phEB·ω) < L(0)`, `υ_{Λ⁺(lyEB)} < L(0)`. -/
theorem phFr_lyE : xtLam lyEB ≤ iota S phEB ∧ xtB1 lyEB ≤ iota S (phEB * ω) ∧
    iota S (phEB * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 lyEB) < Nc.ncL S 0 := by
  obtain ⟨-, hLam, hB1, hL, hups⟩ := phFrGen (S := S) ph_EB_lt_Gam phPoly_lyEB
    (fun y hy hy1 => (phTh_EB hy hy1).symm) (fun _ hZ => ph_cl_EB hZ) ph_Om1_le_EB
  rw [ph_EB_eps] at hLam hB1 hL
  exact ⟨hLam, hB1, hL, hups⟩

theorem ph_Om1_le_ZT : Om 1 ≤ phZT := ph_Om1_le_EB.trans
  (veblen_le_veblen_iff_right.2 le_self_add)

theorem ph_Om1_le_V : Om 1 ≤ phV := ph_Om1_le_B.trans
  (veblen_le_veblen_iff_right.2 le_self_add)

theorem ph_Om1_le_W (K : ℕ) : Om 1 ≤ phW K := ph_Om1_le_B.trans
  (veblen_le_veblen_iff_right.2 le_self_add)

/-- **`lzZ`**: `Λ⁺(lzZ) ≤ ι(ω^{phZT}·ω) < L(0)`. -/
theorem phFr_lzZ : xtB1 lzZ ≤ iota S (ω ^ phZT * ω) ∧ iota S (ω ^ phZT * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 lzZ) < Nc.ncL S 0 := by
  obtain ⟨-, -, hB1, hL, hups⟩ := phFrGen (S := S) ph_ZT_lt_Gam (phPolyR_of phPoly_lzZ)
    (fun y hy hy1 => (phTh_ZT hy hy1).symm) (fun _ hZ => ph_cl_ZT hZ) ph_Om1_le_ZT
  exact ⟨hB1, hL, hups⟩

/-- **`lzVs`**: `Λ⁺(lzVs) ≤ ι(ω^{phV}·ω) < L(0)`. -/
theorem phFr_lzV : xtB1 lzVs ≤ iota S (ω ^ phV * ω) ∧ iota S (ω ^ phV * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 lzVs) < Nc.ncL S 0 := by
  obtain ⟨-, -, hB1, hL, hups⟩ := phFrGen (S := S) ph_V_lt_Gam (phPolyR_of phPoly_lzV)
    (fun y hy hy1 => (phTh_V hy hy1).symm) (fun _ hZ => ph_cl_V hZ) ph_Om1_le_V
  exact ⟨hB1, hL, hups⟩

/-- **`lzWs K`**: `Λ⁺(lzWs K) ≤ ι(ω^{phW K}·ω) < L(0)`. -/
theorem phFr_lzW (K : ℕ) : xtB1 (lzWs K) ≤ iota S (ω ^ phW K * ω) ∧ iota S (ω ^ phW K * ω) < Nc.ncL S 0 ∧
    upsilon (xtB1 (lzWs K)) < Nc.ncL S 0 := by
  obtain ⟨-, -, hB1, hL, hups⟩ := phFrGen (S := S) (ph_W_lt_Gam K) (phPolyR_of (phPoly_lzW K))
    (fun y hy hy1 => (phTh_W hy hy1 K).symm) (fun _ hZ => ph_cl_W hZ K) (ph_Om1_le_W K)
  exact ⟨hB1, hL, hups⟩

/-- The code `φ(ω, Ω₁ + ω)` bounding every `phW K`. -/
noncomputable def phYw : Ordinal.{0} := veblen ω (Om 1 + ω)

theorem ph_W_lt_Yw (K : ℕ) : phW K + 1 < phYw := by
  have hp : IsPrincipal (· + ·) phYw := ph_veblen_prin _ _
  refine hp (veblen_lt_veblen_iff_right.2 ?_) ?_
  · rw [add_assoc]; exact (add_lt_add_iff_left _).2 (by
      rw [← Nat.cast_one, ← Nat.cast_add]; exact natCast_lt_omega0 _)
  · exact (gg_one_lt_of_SC ph_SC_Om1).trans_le ((le_self_add).trans (right_le_veblen _ _))

/-- **`Λ⁺_Y = sup_K Λ⁺(lzWs (K+2)) ≤ ι(ω^{φ(ω, Ω₁ + ω)}) < L(0)`**, `υ_{Λ⁺_Y} < L(0)`. -/
theorem phFr_Y : lzWFam.famSup ≤ iota S (ω ^ phYw) ∧ iota S (ω ^ phYw) < Nc.ncL S 0 ∧
    upsilon lzWFam.famSup < Nc.ncL S 0 := by
  have hcl : ∀ Z, SC Z → GgCl Z (ω ^ phYw) := fun Z hZ =>
    GgCl.opow hZ.1 (GgCl.phi (GgCl.small (ph_omega_lt hZ)) (GgCl.add GgCl.om (GgCl.small (ph_omega_lt hZ))))
  have hle : lzWFam.famSup ≤ iota S (ω ^ phYw) := by
    refine Ordinal.iSup_le fun k => (phFr_lzW (S := S) (k + 2)).1.trans (iota_mono _ _ ?_)
    rw [← opow_succ]
    exact opow_le_opow_right omega0_pos (Order.succ_le_of_lt ((lt_add_one _).trans (ph_W_lt_Yw (k + 2))))
  obtain ⟨h1, h2⟩ := phIota_lt_L0 (S := S) hcl
  exact ⟨hle, h1, (ups_mono hle).trans_lt h2⟩

/-! ## `L(0) ≤ L(n+1) < L(ω) < L(ω+1)` -/

theorem phL_chain (n : ℕ) : Nc.ncL S 0 ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) :=
  ⟨Pp.ppL_mono zero_le, Pp.ppL_lt_omega n, Qq.qqL_lt_succ S⟩

/-- **The order of the frontiers and the `L(n)`** (unconditional): `υ` of each of `cpB1`, `Λ_{ω²}`, `Λ⁺(lyEB)`,
`Λ⁺_Y` is below `L(0) ≤ L(n+1) < L(ω) < L(ω+1)`. -/
theorem phFr_order (n : ℕ) :
    (upsilon cpB1 < Nc.ncL S 0 ∧ upsilon xtFamW2.famSup < Nc.ncL S 0 ∧ upsilon (xtB1 lyEB) < Nc.ncL S 0 ∧
      upsilon lzWFam.famSup < Nc.ncL S 0) ∧
    (upsilon cpB1 < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ upsilon cpB1 < Nc.ncL S ω ∧
      cpB1 < Nc.ncL S (ω + 1)) ∧
    (upsilon lzWFam.famSup < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ upsilon lzWFam.famSup < Nc.ncL S ω ∧
      lzWFam.famSup < Nc.ncL S (ω + 1)) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) n
  have hB := (phFr_vz (S := S)).2.2.2.2
  have hY := (phFr_Y (S := S)).2.2
  refine ⟨⟨hB, (phFr_W2 (S := S)).2.2, (phFr_lyE (S := S)).2.2.2, hY⟩, ⟨hB.trans_le h0, (hB.trans_le h0).trans h1,
    (upsilon_normal.strictMono.le_apply.trans_lt (((hB.trans_le h0).trans h1).trans h2))⟩,
    ⟨hY.trans_le h0, (hY.trans_le h0).trans h1,
    (upsilon_normal.strictMono.le_apply.trans_lt (((hY.trans_le h0).trans h1).trans h2))⟩⟩

end Googology.Trans.PoR.InaccPsi.R2.Ph
