import Googology.Trans.PoR.InaccPsi.R2.TfPsi

/-!
# The levels `Φ_μ` for every `μ < B_Γ`, and FWD at them

`tfDatL μ = Tf.tfDat (Ω₁ + μ)` (**the data of the level `μ`** on the normal forms over `Ω₁` and the atoms `Γ_ν =
ψ_{Ω₂}(ν − (Ω₁ + 1))`, `R2.TfDat`, `R2.TfPsi`), `B_Γ = Tf.tfBG`, `u_μ = Ω₁^μ = Le.leOe μ`, `ψ = S.psi`.  `Tc.tcP` (the
levels on `Tc.tcDatL`) is correct below `Γ'` only.  The same definition on the data `tfDatL`:

* `tfP μ` (**the `μ`-th level**: the enumeration of the strongly critical `v > tfDatL μ` that are fixed points of
  every `tfP j`, `j < μ`, with `tfDatL j < v`), `tfP_props`, `tfP_SC`, `tfDatL_lt_tfP`, `tfP_fix_lower`, `tfP_range`,
  `tfP_fix_mono`, `tfP_ne_self_of_dat`, `tfDatL_lt_fix`, `tf_clo_val`;
* `tfDatL_eq_tcL` (**`tfDatL μ = Tc.tcDatL μ` for `μ < Γ'`**), `tfP_eq_tcP` (**`tfP μ = Tc.tcP μ` for every `μ < Γ'`**:
  the new hierarchy extends the old one), `tfP_zero_eq`;
* `tf_code_lvl` (**`tfDatL μ < b` makes `μ < B_Γ` a code over the strongly critical `b`**), `tfU_mem`, `tfU_mul_mem`;
* `TfFWD S μ` (the statement name), `tfFwdAll` (**`ψ_{Ω₁}(B)` is a fixed point of `tfP μ` for every own `B ≠ 0`
  with `u_{μ+1} ∣ B` and `tfDatL μ < ψ_{Ω₁}(B)`, at every level `μ < B_Γ`**: the proof of `Tc.tcFwdAll`).

No new axiom.  New definitions: `tfDatL`, `tfP`, `tfC`, the statement name `TfFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **The data of the level `μ`** on Veblen normal forms: `tfDat (Ω₁ + μ)`. -/
noncomputable def tfDatL (μ : Ordinal.{0}) : Ordinal.{0} := tfDat (Om1 + μ)

theorem tfDatL_zero : tfDatL 0 = 0 := by unfold tfDatL; rw [add_zero, tfDat_Om1]

/-- **The `μ`-th level** `Φ_μ`: the enumeration of the strongly critical `v > tfDatL μ` that are fixed points of every
`Φ_j`, `j < μ`, with `tfDatL j < v`. -/
noncomputable def tfP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  enumOrd {v | SC v ∧ tfDatL μ < v ∧ ∀ j : Iio μ, tfDatL j.1 < v → tfP j.1 v = v}
termination_by μ
decreasing_by exact j.2

/-- The set enumerated by `Φ_μ`. -/
def tfC (μ : Ordinal.{0}) : Set Ordinal.{0} :=
  {v | SC v ∧ tfDatL μ < v ∧ ∀ j < μ, tfDatL j < v → tfP j v = v}

theorem tfP_eq (μ : Ordinal.{0}) : tfP μ = enumOrd (tfC μ) := by
  rw [tfP]
  congr 1
  ext v
  simp only [mem_setOf_eq, tfC]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun j hj => c ⟨j, hj⟩⟩, fun ⟨a, b, c⟩ => ⟨a, b, fun j => c j.1 j.2⟩⟩

/-- **`Φ_μ` is normal and its range is `tfC μ`.** -/
theorem tfP_props (μ : Ordinal.{0}) : Order.IsNormal (tfP μ) ∧ range (tfP μ) = tfC μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  -- unbounded
  have hunb : ¬ BddAbove (tfC μ) := by
    rintro ⟨b, hb⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · have hv : gamma (b + 1) ∈ tfC 0 :=
        ⟨lq_gamma_SC _, by rw [tfDatL_zero]; exact gamma_pos, fun j hj => absurd hj (not_lt.2 zero_le)⟩
      exact absurd ((lt_add_one b).trans_le (lq_le_gamma _)) (not_lt.2 (hb hv))
    · have h0 : (0 : Ordinal.{0}) < μ := pos_iff_ne_zero.2 hμ0
      set f : Iio μ → Ordinal.{0} → Ordinal.{0} := fun j => tfP j.1 with hf
      have hN : ∀ j : Iio μ, Order.IsNormal (f j) := fun j => (IH j.1 j.2).1
      set v := nfpFamily f (b + tfDatL μ + 1) with hvdef
      have hfix : ∀ j : Iio μ, tfP j.1 v = v := fun j => nfpFamily_fp (hN j) _
      have hle : b + tfDatL μ + 1 ≤ v := le_nfpFamily f _
      have hv0 : v ∈ range (tfP 0) := ⟨v, hfix ⟨0, h0⟩⟩
      rw [(IH 0 h0).2] at hv0
      have hv : v ∈ tfC μ :=
        ⟨hv0.1, (le_add_self.trans_lt (lt_add_one _)).trans_le hle, fun j hj _ => hfix ⟨j, hj⟩⟩
      exact absurd ((le_self_add.trans_lt (lt_add_one _)).trans_le hle) (not_lt.2 (hb hv))
  -- closed under suprema
  have hcl : ∀ t ⊆ tfC μ, t.Nonempty → BddAbove t → sSup t ∈ tfC μ := by
    intro t ht hne hbd
    by_cases hst : sSup t ∈ t
    · exact ht hst
    obtain ⟨v0, hv0⟩ := hne
    have hlt : ∀ v ∈ t, v < sSup t := fun v hv =>
      lt_of_le_of_ne (le_csSup hbd hv) fun e => hst (e ▸ hv)
    refine ⟨Rk.rk_SC_sSup (fun v hv => (ht hv).1) ⟨v0, hv0⟩ hbd,
      (ht hv0).2.1.trans_le (le_csSup hbd hv0), fun j hj hdj => ?_⟩
    set t' := {v ∈ t | tfDatL j < v} with ht'
    obtain ⟨w0, hw0, hjw0⟩ := (lt_csSup_iff hbd ⟨v0, hv0⟩).1 hdj
    have hne' : t'.Nonempty := ⟨w0, hw0, hjw0⟩
    have hbd' : BddAbove t' := hbd.mono fun v hv => hv.1
    have hsup : sSup t' = sSup t := by
      refine le_antisymm (csSup_le_csSup hbd hne' fun v hv => hv.1) (csSup_le ⟨v0, hv0⟩ fun v hv => ?_)
      obtain ⟨w, hw, hvw⟩ := (lt_csSup_iff hbd ⟨v0, hv0⟩).1 (max_lt (hlt v hv) hdj)
      exact (le_max_left _ _ |>.trans (hvw.le)).trans
        (le_csSup hbd' ⟨hw, (le_max_right _ _).trans_lt hvw⟩)
    have hNj := (IH j hj).1
    rw [← hsup, hNj.map_sSup hne' hbd']
    congr 1
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [(ht hv.1).2.2 j hj hv.2]; exact hv
    · intro hy
      exact ⟨y, hy, (ht hy.1).2.2 j hj hy.2⟩
  rw [tfP_eq]
  exact ⟨isNormal_enumOrd hcl hunb, range_enumOrd hunb⟩

theorem tfP_normal (μ : Ordinal.{0}) : Order.IsNormal (tfP μ) := (tfP_props μ).1

theorem tfP_range_eq (μ : Ordinal.{0}) : range (tfP μ) = tfC μ := (tfP_props μ).2

theorem tfP_mem (μ o : Ordinal.{0}) : tfP μ o ∈ tfC μ := by rw [← tfP_range_eq]; exact ⟨o, rfl⟩

theorem tfP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : tfP μ a < tfP μ b ↔ a < b :=
  (tfP_normal μ).strictMono.lt_iff_lt

theorem tfP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : tfP μ a ≤ tfP μ b ↔ a ≤ b :=
  (tfP_normal μ).strictMono.le_iff_le

theorem tfP_le_self (μ o : Ordinal.{0}) : o ≤ tfP μ o := (tfP_normal μ).strictMono.le_apply

/-- **The values of `Φ_μ` are strongly critical.** -/
theorem tfP_SC (μ o : Ordinal.{0}) : SC (tfP μ o) := (tfP_mem μ o).1

/-- **The values of `Φ_μ` lie above the data of `μ`.** -/
theorem tfDatL_lt_tfP (μ o : Ordinal.{0}) : tfDatL μ < tfP μ o := (tfP_mem μ o).2.1

/-- **A value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j < μ`, with `tfDatL j < v`.** -/
theorem tfP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (tfP μ)) (hj : tfDatL j < v) :
    tfP j v = v := by
  rw [tfP_range_eq] at hv; exact hv.2.2 j h hj

/-- **A value of `Φ_μ`**: a strongly critical `v` with `tfDatL μ < v` that is a fixed point of every `Φ_j`, `j < μ`,
`tfDatL j < v`. -/
theorem tfP_range {μ v : Ordinal.{0}} (hSC : SC v) (hμ : tfDatL μ < v)
    (hfix : ∀ j < μ, tfDatL j < v → tfP j v = v) : ∃ e, tfP μ e = v := by
  have : v ∈ range (tfP μ) := by rw [tfP_range_eq]; exact ⟨hSC, hμ, hfix⟩
  exact this

/-- **A fixed point of `Φ_μ` is a fixed point of every `Φ_j`, `j ≤ μ`, with `tfDatL j < x`.** -/
theorem tfP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : tfP μ x = x) (hj : tfDatL j < x) : tfP j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact tfP_fix_lower hlt ⟨x, hx⟩ hj

/-- **`τ ≤ tfDatL μ` is not a fixed point of `Φ_μ`.** -/
theorem tfP_ne_self_of_dat {μ τ : Ordinal.{0}} (hτ : τ ≤ tfDatL μ) : tfP μ τ ≠ τ := fun h =>
  absurd (hτ.trans_lt (tfDatL_lt_tfP μ τ)) (by rw [h]; exact lt_irrefl _)

/-- A fixed point `p` of `Φ_μ` lies above `tfDatL μ`. -/
theorem tfDatL_lt_fix {μ p : Ordinal.{0}} (hp : tfP μ p = p) : tfDatL μ < p := by
  rw [← hp]; exact tfDatL_lt_tfP μ p

/-- A value of `Φ_μ` is closed under the lower levels. -/
theorem tf_clo_val (μ o : Ordinal.{0}) :
    ∀ j < μ, tfDatL j < tfP μ o → ∀ z < tfP μ o, tfP j z < tfP μ o := fun j hj hd z hz => by
  have h := (tfP_lt_iff j).2 hz
  rwa [tfP_fix_lower hj ⟨o, rfl⟩ hd] at h




/-! ## Agreement with `Tc.tcP` below `Γ'` -/

/-- **`tfDatL μ = tcDatL μ` for `μ < Γ'`.** -/
theorem tfDatL_eq_tcL {μ : Ordinal.{0}} (hμ : μ < lgGam') : tfDatL μ = Tc.tcDatL μ := tfDatL_eq_tc hμ

/-- **`tfP μ = tcP μ` for every `μ < Γ'`.** -/
theorem tfP_eq_tcP : ∀ μ : Ordinal.{0}, μ < lgGam' → tfP μ = Tc.tcP μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rw [tfP_eq, Tc.tcP_eq]
  congr 1
  ext v
  simp only [tfC, Tc.tcC, mem_setOf_eq]
  rw [tfDatL_eq_tcL hμ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    rw [← IH j hj (hj.trans hμ)]; exact h3 j hj (by rw [tfDatL_eq_tcL (hj.trans hμ)]; exact hd)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    rw [IH j hj (hj.trans hμ)]; exact h3 j hj (by rw [← tfDatL_eq_tcL (hj.trans hμ)]; exact hd)

theorem tfP_zero_eq : tfP 0 = gamma := by
  rw [tfP_eq_tcP 0 (lt_of_le_of_lt zero_le Tc.tc_Gam_lt_G'), Tc.tcP_zero_eq]

/-! ## Codes of levels -/

theorem tf_BG_indec : Indec (tfBG : Ordinal.{0}) := lq_SC_indec tfBG_SC

/-- **`tfDatL μ < b` makes `μ < B_Γ` a code over a strongly critical `b`.** -/
theorem tf_code_lvl {μ b : Ordinal.{0}} (hb : SC b) (hμ : μ < tfBG) (hd : tfDatL μ < b) : TfCl b μ := by
  have hO : Om1 + μ < tfBG := tf_BG_indec.add_lt tfBG_gt hμ
  exact (tf_cl_Om1_add hb).1 (tf_code hb.1 (Om1 + μ) hO hd)

theorem tf_Om1_mul_lt {μ : Ordinal.{0}} (hμ : μ < tfBG) : Om1 * μ < tfBG := tf_BG_mul_lt tfBG_gt hμ

theorem tf_U_lt {μ : Ordinal.{0}} (hμ : μ < tfBG) : Le.leOe μ < tfBG := by
  unfold Le.leOe
  rw [← rj_Om1, ← Low.opow_eq_self_of_SC tfBG_SC]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (tf_Om1_mul_lt hμ)

/-- `u_μ ∈ Cl(a, b)` for a code `μ < B_Γ` over a countable strongly critical `b`, `u_μ ≤ a`. -/
theorem tfU_mem {μ a b : Ordinal.{0}} (hb : SC b) (hb1 : b ≤ Om1) (hμB : μ < tfBG) (hμ : TfCl b μ)
    (ha : Le.leOe μ ≤ a) : Le.leOe μ ∈ S.CSet a b := by
  have hc : TfCl b (Le.leOe μ) := by
    unfold Le.leOe; rw [← rj_Om1]; exact TfCl.opow hb.1 (tf_cl_Om1_mul hb hμ)
  exact tf_mem_CSet hb hb1 le_rfl _ hc (tf_U_lt hμB) ha

/-- `u_μ·D ∈ Cl(a, b)` for a code `μ < B_Γ` over a countable strongly critical `b`, `D < b`, `u_μ·D ≤ a`. -/
theorem tfU_mul_mem {μ a b D : Ordinal.{0}} (hb : SC b) (hb1 : b ≤ Om1) (hμB : μ < tfBG) (hμ : TfCl b μ)
    (hD : D < b) (ha : Le.leOe μ * D ≤ a) : Le.leOe μ * D ∈ S.CSet a b := by
  have hc : TfCl b (Le.leOe μ * D) := by
    unfold Le.leOe; rw [← rj_Om1]; exact tf_cl_opow_mul hb (tf_cl_Om1_mul hb hμ) D (TfCl.small hD)
  exact tf_mem_CSet hb hb1 le_rfl _ hc (tf_BG_mul_lt (tf_U_lt hμB) ((hD.trans_le hb1).trans tfBG_gt)) ha

/-! ## FWD -/

/-- **FWD(μ)** for `tfP`: `ψ_{Ω₁}(B)` is a fixed point of `tfP μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B` and
`tfDatL μ < ψ_{Ω₁}(B)`. -/
def TfFWD (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (μ + 1) ∣ B → B ≠ 0 →
    tfDatL μ < S.psi B (Om 1) → tfP μ (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **FWD(μ) at every level `μ < B_Γ` of `tfP`** (the proof of `Tc.tcFwdAll`, codes read by `tf_cl_iff`). -/
theorem tfFwdAll (μ : Ordinal.{0}) : μ < tfBG → TfFWD S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have h0 := rd_Om1_ne
  intro B hown hB hB0 hdx
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [tfP_zero_eq, ← rhF_zero]
    exact rh_fwd 0 B hown hB hB0 (lt_of_le_of_lt zero_le hdx)
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμpos : 0 < μ := pos_iff_ne_zero.2 hμ0
  have hdat0 : tfDatL 0 = 0 := tfDatL_zero
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ μ + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := IH 0 hμpos (hμpos.trans hμ) B hown h1 hB0 (by rw [hdat0]; exact hxSC.1)
    rwa [tfP_zero_eq] at this
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hupos : 0 < u := rhU_pos μ
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, tfP μ z < x := by
    intro z hz
    set a := tfDatL μ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (tfDatL μ + z) e.symm
    have hdp : tfDatL μ < p := (le_self_add.trans_lt (lt_add_one (tfDatL μ + z))).trans hap
    have hz1p : z + 1 < p := by
      refine lt_of_le_of_lt ?_ hap
      rw [hadef, add_assoc]; exact le_add_self
    obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpx
    have hBpB : Bp < B := by
      have h := compare_psi Low.InR_Om_one hownp hown
      rw [hBp, compare_lt_iff_lt.2 hpx] at h
      exact compare_lt_iff_lt.1 h.symm
    set e := u * (Bp / u) + u with hedef
    have hBpe : Bp ≤ e := by
      calc Bp = u * (Bp / u) + Bp % u := (Ordinal.div_add_mod Bp u).symm
        _ ≤ e := add_le_add_right (Ordinal.mod_lt Bp hu0).le _
    have hpe : p ≤ S.psi e (Om 1) := by rw [← hBp]; exact (psi_mono Low.InR_Om_one hBpe).1
    have hde : tfDatL μ < S.psi e (Om 1) := hdp.trans_le hpe
    have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) Bp hBpmem)
        (tfU_mem (SC_psi Low.InR_Om_one _) (by rw [rj_Om1]; exact (psi_lt Low.InR_Om_one e).le) hμ
          (tf_code_lvl (SC_psi Low.InR_Om_one _) hμ hde) le_add_self)
    have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, tfP μ w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (tfU_mul_mem (SC_psi Low.InR_Om_one _) (by rw [rj_Om1]; exact (psi_lt Low.InR_Om_one _).le) hμ
            (tf_code_lvl (SC_psi Low.InR_Om_one _) hμ (hde.trans_le hle)) (hd.trans_le hle) le_add_self)
      refine ⟨hownd, tfP_range (SC_psi Low.InR_Om_one _) (hde.trans_le hle)
        fun j hj hdj => ?_⟩
      exact IH j hj (hj.trans hμ) _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, tfP μ w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : tfP μ w' < tfP μ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((tfP_lt_iff μ).1 h2) (not_lt.2 h1)
    have hz1e : z + 1 < S.psi e (Om 1) := hz1p.trans_le hpe
    obtain ⟨w, hw⟩ := (hed (z + 1) hz1e).2
    have hzw : z < w := (lt_add_one z).trans_le (hcount (z + 1) hz1e w hw)
    have hlt : e + u * (z + 1) < B := by
      have hq : Bp / u < Om 1 * m := by
        rw [hm] at hBpB; exact (Ordinal.lt_mul_iff_div_lt hu0).1 hBpB
      have hc1 : 1 + (z + 1) < Om 1 :=
        rb_Om1_indec.add_lt (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit (Om_isSuccLimit one_ne_zero)))
          ((Om_isSuccLimit one_ne_zero).add_one_lt (hz.trans hx1))
      have e1 : e + u * (z + 1) = u * (Bp / u + (1 + (z + 1))) := by
        simp only [hedef, mul_add, mul_one, add_assoc]
      rw [e1, hm]
      exact (mul_lt_mul_iff_right₀ hupos).2 (rh_add_lt_Om1_mul hq hc1)
    have hψlt : S.psi (e + u * (z + 1)) (Om 1) < x :=
      psi_lt_psi_of_mem Low.InR_Om_one hlt ((psi_mono Low.InR_Om_one hlt.le).2 (hed (z + 1) hz1e).1)
    calc tfP μ z < tfP μ w := (tfP_lt_iff μ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((tfP_normal μ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (tfP_le_self μ x)


end Googology.Trans.PoR.InaccPsi.R2.Tf
