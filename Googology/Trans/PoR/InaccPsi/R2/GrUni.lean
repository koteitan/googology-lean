import Googology.Trans.PoR.InaccPsi.R2.GrCl

/-!
# THEOREM UNI AND THE FRONTIER LEMMA WITH A GATE: terms and codes asked only at the bases above `K = ψ_{Ω₁}(Ω_ω)`

`Gm.gmUni2` and `Gm.gmB1_eq` ask the terms of a system for every base `y` above the support of a code (`GmPoly`),
the top reading at every strongly critical `y`, and the top code `T` to be a code over EVERY strongly critical `Z`.
A code that contains a constant `ν ≥ Γ₀` is not a code over `Z = Γ₀` (`Gq.gq_wall`).  Every use, however, is at a
named fixed point `F = υ_F` or at `P(η)`, `Ω₁`, all `≥ K` (`Td.tdK_le_rho`, `gr_tdK_le_Pv`).  Here the same proofs
run with every such demand restricted to the bases `≥ K` (terms: above a gate `κ < K`).

* `GrPoly` (**terms above a gate `κ`**), `grUni2`, `grUniTh` (**THEOREM UNI WITH A GATE**);
* `gr_good`, `grIota_lt_L0`, `grFrPt`, `grFrGen`, `grFr_exp`, `grFr_mul`, `grB1_ge`, `grB1_eq` (**THE GATED FRONTIER
  LEMMA**: `Λ⁺(X) = ι(ω^T·ω)`, `P(ω^T·ω) < L(0)`).

No new axiom.  New definition: `GrPoly`.
-/
set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
open Googology.Trans.PoR.InaccPsi.R2.Gf
open Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ph

/-- **Terms for the codes below `E` at the bases above `κ`**: a gated `Gm.GmPoly`. -/
def GrPoly (K : GmCS) (X : Xt.XtSys) (E κ : Ordinal.{0}) : Prop :=
  ∀ Z c, GxCl Z (K.At Z) c → c < E → ∃ s : X.Tm, ∀ y, SC y → y < Om 1 → Z ≤ y → κ < y →
    X.CB s y ∧ X.val s y = gxTh y (K.At y) c

variable {S : InaccSeq.{0}} {K : GmCS}

/-- **THEOREM UNI WITH A GATE**: for every term system `X` with terms for the codes below `E ≤ K.V` at the bases
above `κ < K = ψ_{Ω₁}(Ω_ω)`, every named restart index `F = υ_F` with `e(η_F) ≤ E` has `O_X(F) = Θ^b_F(e(η_F))`
(the named fixed points are `≥ K`, `Td.tdK_le_rho`). -/
theorem grUni2 {X : XtSys} {E κ : Ordinal.{0}} (hκ : κ < Td.tdK S) (hE : E ≤ K.V) (hP : GrPoly K X E κ) :
    ∀ F ηx, IsRestartIdx F → upsilon F = F → upsilon F < Pv S ηx → cdExp (cdEta S F) ≤ E →
      xtOrec X F = gxTh F (K.At F) (cdExp (cdEta S F)) := by
  intro F
  induction F using WellFoundedLT.induction with
  | ind F IH =>
  intro ηx hF hfix hX heE
  have hF1 : F < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have hF1' : F < Om1 := by rw [Br.Om1_eq]; exact hF1
  have hSC : SC F := ggSC_fix hF hfix hX
  have hww := gg_ww_lt hF hfix
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp (gg_name_ne hF hfix hX)
  obtain ⟨hwin0, hwin⟩ := ggWin hF hX hdec hd
  have hFe : F ≤ cdExp (cdEta S F) := Fx.fxExp_fix hF hfix hX
  have hFth : F ≤ gxTh F (K.At F) (cdExp (cdEta S F)) := by
    calc F = gxTh F (K.At F) F := (gxTh_small le_rfl).symm
      _ ≤ _ := gxTh_mono hFe
  -- the named fixed points below `F`
  have hfx : ∀ μ, IsRestartIdx μ → upsilon μ = μ → μ < F →
      upsilon μ < Pv S ηx ∧ SC μ ∧ UpsPt μ := by
    intro μ hμ hfixμ h2
    have hXμ : upsilon μ < Pv S ηx := (upsilon_normal.strictMono h2).trans hX
    refine ⟨hXμ, ggSC_fix hμ hfixμ hXμ, ?_⟩
    have := upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)
    rwa [hfixμ] at this
  have hUF : UpsPt F := by
    have := upsPt_upsilon (pos_iff_ne_zero.2 hF.1)
    rwa [hfix] at this
  apply le_antisymm
  · -- `O_X(F) ≤ Θ_F(e(η_F))`
    refine xtOrec_le_of ((Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le hww)).trans hFth)
      fun s hCB hc => ?_
    have hνF : max (iota S η0) (ω * ω) < F := max_lt hwin0 hww
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc _ hνF
    have hww' : ω * ω < μ := (le_max_right _ _).trans_lt h1
    have hw0 : iota S η0 < μ := (le_max_left _ _).trans_lt h1
    have hμ1 : μ < Om1 := h2.trans hF1'
    rcases (upsilon_normal.strictMono.le_apply : μ ≤ upsilon μ).lt_or_eq with hnf | hfxe
    · have hO := xtNonfix (X := X) hμ hww' hnf hμ1
      have hle : X.val s (upsilon μ) ≤ μ := by
        rw [hO] at hsμ; exact hsμ.trans ((cdOff_le _).trans (cpExp_le hμ.1))
      rw [xt_const_of_small (ups_inE hμ) (ups_lt_Om1 _ hμ1) hCBμ (hle.trans_lt hnf) (upsilon F)]
      exact (hle.trans_lt h2).trans_le hFth
    · have hfixμ : upsilon μ = μ := hfxe.symm
      obtain ⟨hXμ, hSCμ, hUμ⟩ := hfx μ hμ hfixμ h2
      have heμ : cdExp (cdEta S μ) < cdExp (cdEta S F) := hwin μ hμ hw0 h2
      have hOμ := IH μ h2 ηx hμ hfixμ hXμ (heμ.le.trans heE)
      rw [hfixμ] at hCBμ hsμ
      rw [hOμ] at hsμ
      have hmem : GxCl μ (K.At μ) (cdExp (cdEta S μ)) :=
        gmExpMem hμ hfixμ hXμ ((heμ.trans_le heE).trans_le hE)
      obtain ⟨c, hcC, hcle, hcv⟩ := gx_le_onto hmem hsμ
      have hcE : c < E := (hcle.trans_lt heμ).trans_le heE
      obtain ⟨t, ht⟩ := hP μ c hcC hcE
      have hκμ : κ < μ := hκ.trans_le (by rw [← hfixμ]; exact Td.tdK_le_rho hμ hXμ)
      have hκF : κ < F := hκ.trans_le (by rw [← hfix]; exact Td.tdK_le_rho hF hX)
      obtain ⟨htCBμ, htμ⟩ := ht μ hSCμ (h2.trans hF1) le_rfl hκμ
      obtain ⟨-, htF⟩ := ht F hSC hF1 h2.le hκF
      have hB : Bases μ F := ⟨upsPt_inE hUμ, upsPt_inE hUF, h2, hF1'⟩
      have e1 := X.uni_le μ F hUμ hUF hB t s htCBμ hCBμ
      have e2 := X.uni_le μ F hUμ hUF hB s t hCBμ htCBμ
      have hsF : X.val s F = X.val t F :=
        le_antisymm (e2.2 (by rw [htμ, hcv])) (e1.2 (by rw [htμ, hcv]))
      rw [hfix, hsF, htF]
      exact gxTh_lt (gmCl_mono h2.le hcC) (hcle.trans_lt heμ)
  · -- `Θ_F(e(η_F)) ≤ O_X(F)`
    classical
    unfold gxTh
    rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    by_cases hcC : c.1 ∈ gxSet F (K.At F)
    · rw [if_pos hcC]
      refine Order.add_one_le_of_lt ?_
      have hcC' : GxCl F (K.At F) c.1 := hcC
      rcases lt_or_ge c.1 (Om 1) with hcO | hcO
      · have hcF : c.1 < F := GxCl.lt_of_lt_Om1 hSC (gmAt_GxAt F) hcC' hcO
        have h1 := lt_xtOrec_of_cof hF hF1' (X.cb_cstI _ _ (by rw [hfix]; exact hcF))
          (Nn.nn_const_cof (X := X) hF hfix hF1' hcF)
        rw [X.val_cst] at h1
        show gxTh F (K.At F) c.1 < _
        rw [gxTh_small hcF.le]; exact h1
      · obtain ⟨Z, hZF, hcZ⟩ := gm_support hSC hcC'
        obtain ⟨s, hs⟩ := hP Z c.1 hcZ (c.2.trans_le heE)
        have hκF : κ < F := hκ.trans_le (by rw [← hfix]; exact Td.tdK_le_rho hF hX)
        obtain ⟨hsCB, hsv⟩ := hs F hSC hF1 hZF.le hκF
        have hcof : XtCof X (xtOrec X) F s := by
          intro ν hν
          obtain ⟨μ, hμ, hfixμ, h1, h2, hZμ, hexp⟩ := gmCof hF hfix hX hcZ hcO c.2 hZF hν
          obtain ⟨hXμ, hSCμ, -⟩ := hfx μ hμ hfixμ h2
          have hOμ := IH μ h2 ηx hμ hfixμ hXμ (by rw [hexp]; exact c.2.le.trans heE)
          have hκμ : κ < μ := hκ.trans_le (by rw [← hfixμ]; exact Td.tdK_le_rho hμ hXμ)
          obtain ⟨hCBμ, hvμ⟩ := hs μ hSCμ (h2.trans hF1) hZμ hκμ
          refine ⟨μ, hμ, h1, h2, by rw [hfixμ]; exact hCBμ, ?_⟩
          rw [hfixμ, hvμ, hOμ, hexp]
        have h1 := lt_xtOrec_of_cof hF hF1' (by rw [hfix]; exact hsCB) hcof
        rw [hfix, hsv] at h1
        exact h1
    · rw [if_neg hcC]; exact zero_le

/-- **THEOREM UNI with `Θ_F(m_F)`** (terms asked only at the bases above `κ < K`). -/
theorem grUniTh {X : XtSys} {E κ : Ordinal.{0}} (hκ : κ < Td.tdK S) (hE : E ≤ K.V) (hP : GrPoly K X E κ)
    {F ηx : Ordinal.{0}}
    (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ E) :
    cdTheta S F (cdCode S F) = xtOrec X F := by
  rw [gmCode_eq hF hfix hX (he.trans hE), gmTheta_eq hF hfix hX (he.trans hE),
    grUni2 hκ hE hP F ηx hF hfix hX he]


/-- A code over every strongly critical base `≥ K` is a good name. -/
theorem gr_good {η : Ordinal.{0}} (h : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) η) : Bt.Good S η :=
  gmCl_mem_CSet (gm_B_lt_A1 (S := S) K _) le_rfl (h _ (Pv_SC S η) (gr_tdK_le_Pv S η))

/-- **`ι(η) ≤ P(η) < P(Ω_ω) = L(0)`** for a code `η` over every strongly critical base. -/
theorem grIota_lt_L0 {η : Ordinal.{0}} (h : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) η) :
    iota S η < Nc.ncL S 0 ∧ upsilon (iota S η) < Nc.ncL S 0 := by
  have hη : η < Om ω := ((gmCl_lt_V le_rfl (h _ ph_SC_Om1 Td.tdK_lt_Om1.le)).trans (gmV_lt_Om2 K S)).trans ph_Om2_lt_Omw
  have hlt : iota S η < iota S (Om ω) := cd_iota_lt_of_good (gr_good h) hη
  have hL0 : Nc.ncL S 0 = upsilon (iota S (Om ω)) := by
    rw [Lw.lw_L_eq, mul_zero, add_zero]; exact (ups_iota S _).symm
  have h2 : upsilon (iota S η) < Nc.ncL S 0 := by rw [hL0]; exact upsilon_normal.strictMono hlt
  exact ⟨upsilon_normal.strictMono.le_apply.trans_lt h2, h2⟩

/-- **A named frontier point**: `F = ι(η)` with `e(η) = T`. -/
theorem grFrPt {X : XtSys} {T κ : Ordinal.{0}} (hκ : κ < Td.tdK S) (hTG : T ≤ K.V) (hP : GrPoly K X T κ)
    (htop : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y → X.top y = gxTh y (K.At y) T) {η : Ordinal.{0}}
    (hηcl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) η)
    (hηlim : IsSuccLimit η) (hgap : ∀ ζ < η, ζ + Om 1 ≤ η) (he : cdExp η = T) :
    XtFr X (iota S η) ∧ upsilon (iota S η) = iota S η ∧ cdEta S (iota S η) = η ∧
      upsilon (iota S η) < Pv S (η + 1) := by
  have hg : Bt.Good S η := gr_good hηcl
  have hfix := ggFix (S := S) hηlim hgap
  have hF0 : iota S η ≠ 0 := (lt_of_lt_of_le zero_lt_one (one_le_iota η)).ne'
  have hri := Fx.fx_ri_of_fix hF0 hfix
  have hEta : cdEta S (iota S η) = η := cdEta_unique hg rfl
  have hX : upsilon (iota S η) < Pv S (η + 1) := by
    show upsilon (iota S η) < S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ups_iota S (η + 1), iota_good hg]
    exact upsilon_normal.strictMono (lt_add_one _)
  have hO := grUni2 hκ hTG hP (iota S η) (η + 1) hri hfix hX (by rw [hEta, he])
  have hSC := ggSC_fix hri hfix hX
  have hF1 := Fx.fx_fix_lt_Om1 hfix hX
  refine ⟨⟨hri, ?_⟩, hfix, hEta, hX⟩
  rw [hO, hEta, he, hfix, htop _ hSC hF1 (by rw [← hfix]; exact Td.tdK_le_rho hri hX)]

/-- **The frontiers of a system with a top code `T ≤ K.V`.** -/
theorem grFrGen {X : XtSys} {T κ : Ordinal.{0}} (hκ : κ < Td.tdK S) (hTG : T ≤ K.V) (hP : GrPoly K X T κ)
    (htop : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y → X.top y = gxTh y (K.At y) T)
    (hTcl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) T)
    (hTO : Om 1 ≤ T) :
    (∀ n : ℕ, XtFr X (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) = iota S (ω ^ T * ((n : Ordinal.{0}) + 1))) ∧
    xtLam X ≤ iota S (ω ^ T) ∧ xtB1 X ≤ iota S (ω ^ T * ω) ∧
    iota S (ω ^ T * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 X) < Nc.ncL S 0 := by
  have hT0 : T ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans (gg_one_lt_of_SC ph_SC_Om1)) hTO).ne'
  have hcl : ∀ n : ℕ, ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) (ω ^ T * ((n : Ordinal.{0}) + 1)) :=
      fun n Z hZ hKZ => by
    have := gx_mul_nat hZ.1 (GxCl.opow hZ.1 (hTcl Z hZ hKZ)) (n + 1)
    rwa [Nat.cast_succ] at this
  have hlim : ∀ n : ℕ, IsSuccLimit (ω ^ T * ((n : Ordinal.{0}) + 1)) := fun n => by
    rw [mul_add_one]; exact isSuccLimit_add _ (ph_opow_lim hT0)
  have hpt := fun n : ℕ => grFrPt (S := S) hκ hTG hP htop (hcl n) (hlim n) (ph_gap hTO n) (cpExp_mul_succ T n)
  have hwcl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) (ω ^ T * ω) := fun Z hZ hKZ => by
    have e : ω ^ T * ω = ω ^ (T + 1) := by rw [opow_add, opow_one]
    rw [e]; exact GxCl.opow hZ.1 (GxCl.add (hTcl Z hZ hKZ) (GxCl.small (gg_one_lt_of_SC hZ)))
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
    refine cd_iota_lt_of_good (gr_good (hcl j)) ?_
    refine (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 ?_
    rw [← Nat.cast_succ]; exact natCast_lt_omega0 _
  obtain ⟨hL1, hL2⟩ := grIota_lt_L0 (S := S) hwcl
  refine ⟨fun n => ⟨(hpt n).1, (hpt n).2.1⟩, ?_, hB1, hL1, (ups_mono hB1).trans_lt hL2⟩
  have h0 := (hpt 0).1
  rw [Nat.cast_zero, zero_add, mul_one] at h0
  exact xtLam_le h0.1 h0.2

section Gen

variable {X : XtSys} {T κ : Ordinal.{0}} (hκ : κ < Td.tdK S) (hT : T ≤ K.V) (hP : GrPoly K X T κ)
  (htop : ∀ y, SC y → y < Om 1 → Td.tdK S ≤ y → X.top y = gxTh y (K.At y) T)
include hκ hT hP htop

/-- **A named frontier has `e(η_λ) ≥ T`** (`T ≤ K.V`). -/
theorem grFr_exp {l ηx : Ordinal.{0}} (hl : XtFr X l) (hfix : upsilon l = l) (hX : upsilon l < Pv S ηx) :
    T ≤ cdExp (cdEta S l) := by
  by_contra h
  push Not at h
  have hO := grUni2 hκ hT hP l ηx hl.1 hfix hX h.le
  have hSC := ggSC_fix hl.1 hfix hX
  have hl1 : l < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  have h2 := gxTh_lt (gmExpMem hl.1 hfix hX (h.trans_le hT)) h
  have h3 := hl.2
  rw [hO, hfix, htop l hSC hl1 (by rw [← hfix]; exact Td.tdK_le_rho hl.1 hX)] at h3
  exact absurd h3 h2.ne

/-- **Every frontier `λ ∈ (ω², ι(ω^T·ω))` is `ι(ω^T·k)`.** -/
theorem grFr_mul (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) {l : Ordinal.{0}} (hl : XtFr X l)
    (hww : ω * ω < l) (hlt : l < iota S (ω ^ T * ω)) (hl1 : l < Om1) :
    ∃ k : ℕ, l = iota S (ω ^ T * (k : Ordinal.{0})) := by
  have hfix := ggFr_fix htopE hl hl1 hww
  have hX : upsilon l < Pv S (ω ^ T * ω) := by
    have h := upsilon_normal.strictMono hlt
    rw [ups_iota S] at h
    exact h
  have he := grFr_exp (S := S) hκ hT hP htop hl hfix hX
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
theorem grB1_ge (hTO : Om 1 ≤ T) (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
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
  obtain ⟨k, hk⟩ := grFr_mul (S := S) hκ hT hP htop htopE hμ hww (h2.trans hlt) (h2.trans hb1)
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

/-- **THE GATED FRONTIER LEMMA: `Λ⁺(X) = ι(ω^T·ω)` and `ρ_{Λ⁺(X)} = P(ω^T·ω) < L(0)`** (`T ≤ K.V`; terms, the top
reading and `T` as a code asked only at the bases `≥ K`). -/
theorem grB1_eq (hTcl : ∀ Z, SC Z → Td.tdK S ≤ Z → GxCl Z (K.At Z) T) (hTO : Om 1 ≤ T)
    (htopE : ∀ x, InE x → x < Om1 → eN x < X.top x) (hPk : XtTopPkg X) :
    xtB1 X = iota S (ω ^ T * ω) ∧ upsilon (xtB1 X) = Pv S (ω ^ T * ω) ∧ Pv S (ω ^ T * ω) < Nc.ncL S 0 := by
  have hup := (grFrGen (S := S) hκ hT hP htop hTcl hTO).2.2
  have heq : xtB1 X = iota S (ω ^ T * ω) := le_antisymm hup.1 (grB1_ge hκ hT hP htop hTO htopE hPk)
  have hups : upsilon (xtB1 X) = Pv S (ω ^ T * ω) := by rw [heq, ups_iota S]
  exact ⟨heq, hups, hups ▸ hup.2.2⟩

end Gen

end Googology.Trans.PoR.InaccPsi.R2.Gr
