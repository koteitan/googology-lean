import Googology.Trans.PoR.InaccPsi.R2.GiAt

/-!
# THEOREM UNI for the codes of a code system `K`, up to `Γ_{Ω₁+1+B}`

The proofs of `R2.GhUni` for an arbitrary code system `K : GiCS` (`R2.GiAt`: atoms `Γ_{Ω₁+1+c}`, `c < K.B` with
`K.gt c` below the base; the bound `K.V = Γ_{Ω₁+1+K.B}`, `K.B < A_η`):

* `giCof`, `giHull_iff` (**at a named fixed point `F` the hull below `K.V` is the set of codes over `F`**),
  `giTheta_eq`, `giCode_eq` (`m_F = e(η_F)` when `e(η_F) ≤ K.V`), `giExpMem`;
* `giUni2` (**THEOREM UNI**: `O_X(F) = Θ_F(e(η_F))` at every named fixed point `F` with `e(η_F) ≤ E ≤ K.V`, for
  every term system `X` with `GiPoly K X E`), `giUniTh` (the same with `Θ_F(m_F)`).

No new axiom.
-/
set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Gf

open Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc
open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}} {K : GiCS}

theorem giCof {F ηx c Z ν : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hc : GxCl Z (K.At Z) c) (hc1 : Om 1 ≤ c) (hce : c < cdExp (cdEta S F))
    (hZ : Z < F) (hν : ν < F) :
    ∃ μ, IsRestartIdx μ ∧ upsilon μ = μ ∧ ν < μ ∧ μ < F ∧ Z ≤ μ ∧ cdExp (cdEta S μ) = c := by
  have hF1Z : F < Om 1 := Fx.fx_fix_lt_Om1 hfix hX
  obtain ⟨hg, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hFlim : IsSuccLimit F := ri_lim hF
  have hww := (cp_fix_facts hF hfix).2.2
  have hη0 : cdEta S F ≠ 0 := by
    intro h
    rw [h, iota_zero] at hι
    have h1 : (1 : Ordinal.{0}) < ω * ω := lt_of_lt_of_le one_lt_omega0 (le_mul_left _ omega0_pos)
    exact absurd (hι ▸ hww) (not_lt.2 h1.le)
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp hη0
  set e := cdExp (cdEta S F) with he
  set i1 := max ν Z + 1 with hi1
  have hi1F : i1 < F := by
    rw [hi1, ← succ_eq_add_one]; exact hFlim.succ_lt (max_lt hν hZ)
  have h1i1 : 1 ≤ i1 := by rw [hi1]; exact le_add_self
  obtain ⟨hg1, hι1, hlt1⟩ := cdEta_spec (S := S) h1i1 (by rw [hι]; exact hi1F)
  set η1 := cdEta S i1 with hη1
  have hce' : ω ^ c < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 hce
  -- `η₁ + ω^c < η_F`
  have hlt' : η1 + ω ^ c < cdEta S F := by
    rw [hdec]
    rcases lt_or_ge η1 η0 with h | h
    · calc η1 + ω ^ c ≤ η0 + ω ^ c := by gcongr
        _ < η0 + ω ^ e := (add_lt_add_iff_left _).2 hce'
    · obtain ⟨t, ht1⟩ := exists_add_of_le h
      have ht : t < ω ^ e := by
        have := hlt1; rw [hdec, ht1] at this; exact (add_lt_add_iff_left _).1 this
      rw [ht1, add_assoc]
      exact (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e ht hce')
  -- `η₁ + ω^c` is good
  have hP1 : Pv S η1 = upsilon i1 := by rw [← hι1]; exact (ups_iota S η1).symm
  have hZP : Z ≤ Pv S (η1 + ω ^ c) := by
    calc Z ≤ max ν Z := le_max_right _ _
      _ ≤ i1 := le_self_add
      _ ≤ upsilon i1 := upsilon_normal.strictMono.le_apply
      _ = Pv S η1 := hP1.symm
      _ ≤ Pv S (η1 + ω ^ c) := Pv_mono le_self_add
  have hg' : Bt.Good S (η1 + ω ^ c) := by
    refine good_add hg1 ?_
    have hcC : c ∈ S.CSet (ConjT.Aη S (η1 + ω ^ c) + 1) (Pv S (η1 + ω ^ c)) :=
      giCl_mem_CSet (gi_B_lt_A1 (S := S) K _) hZP hc
    have := CSet.phi_mem (CSet.zero_mem _ _) hcC
    rwa [veblen_zero_apply] at this
  -- `ι(η₁ + ω^c)` is a fixed point of `υ`
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans one_lt_Om1) hc1).ne'
  have hOm : Om 1 ≤ ω ^ c := by
    rw [← Om1_opow]; exact opow_le_opow_right omega0_pos hc1
  have hp1 : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
    rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
  have hgap : ∀ ζ < η1 + ω ^ c, ζ + Om 1 ≤ η1 + ω ^ c := by
    intro ζ hζ
    rcases lt_or_ge ζ η1 with h | h
    · calc ζ + Om 1 ≤ η1 + Om 1 := by gcongr
        _ ≤ η1 + ω ^ c := (add_le_add_iff_left _).2 hOm
    · obtain ⟨s, rfl⟩ := exists_add_of_le h
      have hs : s < ω ^ c := (add_lt_add_iff_left _).1 hζ
      rw [add_assoc]
      refine (add_le_add_iff_left _).2 ?_
      rcases hOm.lt_or_eq with hlt | heq
      · exact (isPrincipal_add_omega0_opow c hs hlt).le
      · rw [← heq] at hs ⊢; exact (hp1.add_eq_right hs).le
  have hfx := ggFix (S := S) (isSuccLimit_add η1 (gg_opow_lim hc0)) hgap
  set μ := iota S (η1 + ω ^ c) with hμ
  have hμ1 : 1 ≤ μ := by have := iota_mono (S := S) (η1 + ω ^ c) 0 zero_le; rwa [iota_zero] at this
  have hμ0 : μ ≠ 0 := (lt_of_lt_of_le zero_lt_one hμ1).ne'
  have hi1μ : i1 < μ := by
    rw [← hι1]; exact cd_iota_lt_of_good hg1 (lt_add_of_pos_right _ (opow_pos _ omega0_pos))
  refine ⟨μ, Fx.fx_ri_of_fix hμ0 hfx, hfx, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left ν Z).trans_lt ((lt_add_one _).trans hi1μ)
  · rw [← hι]; exact cd_iota_lt_of_good hg' hlt'
  · exact ((le_max_right ν Z).trans_lt ((lt_add_one _).trans hi1μ)).le
  · rw [cdEta_unique hg' rfl, cpExp_add η1 (Nn.nn_opow_ne c), ggExp_opow]


/-- **At a named fixed point the hull below `K.V` is the set of codes over `F`.** -/
theorem giHull_iff {F ηx x : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hx : x < K.V) : x ∈ cdHull S F ↔ GxCl F (K.At F) x := by
  constructor
  · intro h
    have h0 : 0 < upsilon F := by rw [hfix]; exact pos_iff_ne_zero.2 hF.1
    have := giCl_of_CSet h0 (by rw [hfix]; exact (Fx.fx_fix_lt_Om1 hfix hX).le) (ggKey hF hX) x h hx
    rwa [hfix] at this
  · intro h
    exact giCl_mem_CSet (gi_B_lt_A (S := S) K _) (by rw [hfix]) h

/-- **`Θ_F(m) = Θ^b_F(m)`** (reading with the atoms over `F`) for `m ≤ K.V` at a named fixed point. -/
theorem giTheta_eq {F ηx m : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hm : m ≤ K.V) : cdTheta S F m = gxTh F (K.At F) m :=
  ggOtp_congr m fun _ hx => giHull_iff hF hfix hX (hx.trans_le hm)

/-- **`m_F = e(η_F)`** at a named fixed point with `e(η_F) ≤ K.V`. -/
theorem giCode_eq {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ K.V) : cdCode S F = cdExp (cdEta S F) := by
  have hFe := Fx.fxExp_fix hF hfix hX
  have hω : ω ≤ cdExp (cdEta S F) :=
    ((le_mul_left _ omega0_pos).trans (gg_ww_lt hF hfix).le).trans hFe
  unfold cdCode
  rw [cdCodeOf_of_lt (he.trans_lt (giV_lt_Om2 K S)), cpOff_of_ge hω]

/-- **The last exponent of the name of a named fixed point is a code over it** (when below `K.V`). -/
theorem giExpMem {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) < K.V) : GxCl F (K.At F) (cdExp (cdEta S F)) := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmem : cdExp (cdEta S F) ∈ cdHull S F := by
    unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  exact (giHull_iff hF hfix hX he).1 hmem

/-- **THEOREM UNI**: for every term system `X` with terms for the codes below `E ≤ K.V`, every named restart
index `F = υ_F` with `e(η_F) ≤ E` has `O_X(F) = Θ^b_F(e(η_F))`. -/
theorem giUni2 {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ K.V) (hP : GiPoly K X E) :
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
        giExpMem hμ hfixμ hXμ ((heμ.trans_le heE).trans_le hE)
      obtain ⟨c, hcC, hcle, hcv⟩ := gx_le_onto hmem hsμ
      have hcE : c < E := (hcle.trans_lt heμ).trans_le heE
      obtain ⟨t, ht⟩ := hP μ c hcC hcE
      obtain ⟨htCBμ, htμ⟩ := ht μ hSCμ (h2.trans hF1) le_rfl
      obtain ⟨-, htF⟩ := ht F hSC hF1 h2.le
      have hB : Bases μ F := ⟨upsPt_inE hUμ, upsPt_inE hUF, h2, hF1'⟩
      have e1 := X.uni_le μ F hUμ hUF hB t s htCBμ hCBμ
      have e2 := X.uni_le μ F hUμ hUF hB s t hCBμ htCBμ
      have hsF : X.val s F = X.val t F :=
        le_antisymm (e2.2 (by rw [htμ, hcv])) (e1.2 (by rw [htμ, hcv]))
      rw [hfix, hsF, htF]
      exact gxTh_lt (giCl_mono h2.le hcC) (hcle.trans_lt heμ)
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
      · have hcF : c.1 < F := GxCl.lt_of_lt_Om1 hSC (giAt_GxAt F) hcC' hcO
        have h1 := lt_xtOrec_of_cof hF hF1' (X.cb_cstI _ _ (by rw [hfix]; exact hcF))
          (Nn.nn_const_cof (X := X) hF hfix hF1' hcF)
        rw [X.val_cst] at h1
        show gxTh F (K.At F) c.1 < _
        rw [gxTh_small hcF.le]; exact h1
      · obtain ⟨Z, hZF, hcZ⟩ := gi_support hSC hcC'
        obtain ⟨s, hs⟩ := hP Z c.1 hcZ (c.2.trans_le heE)
        obtain ⟨hsCB, hsv⟩ := hs F hSC hF1 hZF.le
        have hcof : XtCof X (xtOrec X) F s := by
          intro ν hν
          obtain ⟨μ, hμ, hfixμ, h1, h2, hZμ, hexp⟩ := giCof hF hfix hX hcZ hcO c.2 hZF hν
          obtain ⟨hXμ, hSCμ, -⟩ := hfx μ hμ hfixμ h2
          have hOμ := IH μ h2 ηx hμ hfixμ hXμ (by rw [hexp]; exact c.2.le.trans heE)
          obtain ⟨hCBμ, hvμ⟩ := hs μ hSCμ (h2.trans hF1) hZμ
          refine ⟨μ, hμ, h1, h2, by rw [hfixμ]; exact hCBμ, ?_⟩
          rw [hfixμ, hvμ, hOμ, hexp]
        have h1 := lt_xtOrec_of_cof hF hF1' (by rw [hfix]; exact hsCB) hcof
        rw [hfix, hsv] at h1
        exact h1
    · rw [if_neg hcC]; exact zero_le

/-- **THEOREM UNI with `Θ_F(m_F)`.** -/
theorem giUniTh {X : XtSys} {E : Ordinal.{0}} (hE : E ≤ K.V) (hP : GiPoly K X E) {F ηx : Ordinal.{0}}
    (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ E) :
    cdTheta S F (cdCode S F) = xtOrec X F := by
  rw [giCode_eq hF hfix hX (he.trans hE), giTheta_eq hF hfix hX (he.trans hE),
    giUni2 hE hP F ηx hF hfix hX he]

end Googology.Trans.PoR.InaccPsi.R2.Gi
