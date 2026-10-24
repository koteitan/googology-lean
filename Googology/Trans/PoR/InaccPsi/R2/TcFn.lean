import Googology.Trans.PoR.InaccPsi.R2.TcDat

/-!
# The levels `Φ_μ` for every `μ < Γ'` (past `Γ_{Ω₁+1}`), and FWD at them

`tcDatL μ = Tc.tcDat (Ω₁ + μ)` (**the data of the level `μ`** on Veblen normal forms over `{0, Ω₁, Γ_{Ω₁+1}}`,
`R2.TcDat`), `Γ' = lgGam'`, `u_μ = Ω₁^μ = Le.leOe μ`, `ψ = S.psi`.  `Ss.ssP` (the levels on `Ss.ssDatL`) is correct
below `Γ_{Ω₁+1}` only (junk data `0` above).  The same definition on the data `tcDatL`:

* `tcP μ` (**the `μ`-th level**: the enumeration of the strongly critical `v > tcDatL μ` that are fixed points of
  every `tcP j`, `j < μ`, with `tcDatL j < v`), `tcP_props`, `tcP_SC`, `tcDatL_lt_tcP`, `tcP_fix_lower`, `tcP_range`,
  `tcP_fix_mono`, `tcP_ne_self_of_dat`, `tcDatL_lt_fix`, `tc_clo_val`;
* `tcDatL_eq_ss` (**`tcDatL μ = Ss.ssDatL μ` for `μ ≤ Γ_{Ω₁+1}`**), `tcP_eq_ssP` (**`tcP μ = Ss.ssP μ` for every
  `μ ≤ Γ_{Ω₁+1}`**: the new hierarchy extends the old one), `tcP_zero_eq`;
* `tc_code_lvl` (**`tcDatL μ < b` makes `μ < Γ'` a code over the strongly critical `b`**), `tcU_mem`, `tcU_mul_mem`;
* `TcFWD S μ` (the statement name), `tcFwdAll` (**`ψ_{Ω₁}(B)` is a fixed point of `tcP μ` for every own `B ≠ 0`
  with `u_{μ+1} ∣ B` and `tcDatL μ < ψ_{Ω₁}(B)`, at every level `μ < Γ'`**: the proof of `Ss.ssFwdAll`).

No new axiom.  New definitions: `tcDatL`, `tcP`, `tcC`, the statement name `TcFWD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **The data of the level `μ`** on Veblen normal forms: `tcDat (Ω₁ + μ)`. -/
noncomputable def tcDatL (μ : Ordinal.{0}) : Ordinal.{0} := tcDat (Om1 + μ)

theorem tcDatL_zero : tcDatL 0 = 0 := by unfold tcDatL; rw [add_zero, tcDat_Om1]

/-- **The `μ`-th level** `Φ_μ`: the enumeration of the strongly critical `v > tcDatL μ` that are fixed points of every
`Φ_j`, `j < μ`, with `tcDatL j < v`. -/
noncomputable def tcP (μ : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} :=
  enumOrd {v | SC v ∧ tcDatL μ < v ∧ ∀ j : Iio μ, tcDatL j.1 < v → tcP j.1 v = v}
termination_by μ
decreasing_by exact j.2

/-- The set enumerated by `Φ_μ`. -/
def tcC (μ : Ordinal.{0}) : Set Ordinal.{0} :=
  {v | SC v ∧ tcDatL μ < v ∧ ∀ j < μ, tcDatL j < v → tcP j v = v}

theorem tcP_eq (μ : Ordinal.{0}) : tcP μ = enumOrd (tcC μ) := by
  rw [tcP]
  congr 1
  ext v
  simp only [mem_setOf_eq, tcC]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, fun j hj => c ⟨j, hj⟩⟩, fun ⟨a, b, c⟩ => ⟨a, b, fun j => c j.1 j.2⟩⟩

/-- **`Φ_μ` is normal and its range is `tcC μ`.** -/
theorem tcP_props (μ : Ordinal.{0}) : Order.IsNormal (tcP μ) ∧ range (tcP μ) = tcC μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  -- unbounded
  have hunb : ¬ BddAbove (tcC μ) := by
    rintro ⟨b, hb⟩
    rcases eq_or_ne μ 0 with rfl | hμ0
    · have hv : gamma (b + 1) ∈ tcC 0 :=
        ⟨lq_gamma_SC _, by rw [tcDatL_zero]; exact gamma_pos, fun j hj => absurd hj (not_lt.2 zero_le)⟩
      exact absurd ((lt_add_one b).trans_le (lq_le_gamma _)) (not_lt.2 (hb hv))
    · have h0 : (0 : Ordinal.{0}) < μ := pos_iff_ne_zero.2 hμ0
      set f : Iio μ → Ordinal.{0} → Ordinal.{0} := fun j => tcP j.1 with hf
      have hN : ∀ j : Iio μ, Order.IsNormal (f j) := fun j => (IH j.1 j.2).1
      set v := nfpFamily f (b + tcDatL μ + 1) with hvdef
      have hfix : ∀ j : Iio μ, tcP j.1 v = v := fun j => nfpFamily_fp (hN j) _
      have hle : b + tcDatL μ + 1 ≤ v := le_nfpFamily f _
      have hv0 : v ∈ range (tcP 0) := ⟨v, hfix ⟨0, h0⟩⟩
      rw [(IH 0 h0).2] at hv0
      have hv : v ∈ tcC μ :=
        ⟨hv0.1, (le_add_self.trans_lt (lt_add_one _)).trans_le hle, fun j hj _ => hfix ⟨j, hj⟩⟩
      exact absurd ((le_self_add.trans_lt (lt_add_one _)).trans_le hle) (not_lt.2 (hb hv))
  -- closed under suprema
  have hcl : ∀ t ⊆ tcC μ, t.Nonempty → BddAbove t → sSup t ∈ tcC μ := by
    intro t ht hne hbd
    by_cases hst : sSup t ∈ t
    · exact ht hst
    obtain ⟨v0, hv0⟩ := hne
    have hlt : ∀ v ∈ t, v < sSup t := fun v hv =>
      lt_of_le_of_ne (le_csSup hbd hv) fun e => hst (e ▸ hv)
    refine ⟨Rk.rk_SC_sSup (fun v hv => (ht hv).1) ⟨v0, hv0⟩ hbd,
      (ht hv0).2.1.trans_le (le_csSup hbd hv0), fun j hj hdj => ?_⟩
    set t' := {v ∈ t | tcDatL j < v} with ht'
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
  rw [tcP_eq]
  exact ⟨isNormal_enumOrd hcl hunb, range_enumOrd hunb⟩

theorem tcP_normal (μ : Ordinal.{0}) : Order.IsNormal (tcP μ) := (tcP_props μ).1

theorem tcP_range_eq (μ : Ordinal.{0}) : range (tcP μ) = tcC μ := (tcP_props μ).2

theorem tcP_mem (μ o : Ordinal.{0}) : tcP μ o ∈ tcC μ := by rw [← tcP_range_eq]; exact ⟨o, rfl⟩

theorem tcP_lt_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : tcP μ a < tcP μ b ↔ a < b :=
  (tcP_normal μ).strictMono.lt_iff_lt

theorem tcP_le_iff (μ : Ordinal.{0}) {a b : Ordinal.{0}} : tcP μ a ≤ tcP μ b ↔ a ≤ b :=
  (tcP_normal μ).strictMono.le_iff_le

theorem tcP_le_self (μ o : Ordinal.{0}) : o ≤ tcP μ o := (tcP_normal μ).strictMono.le_apply

/-- **The values of `Φ_μ` are strongly critical.** -/
theorem tcP_SC (μ o : Ordinal.{0}) : SC (tcP μ o) := (tcP_mem μ o).1

/-- **The values of `Φ_μ` lie above the data of `μ`.** -/
theorem tcDatL_lt_tcP (μ o : Ordinal.{0}) : tcDatL μ < tcP μ o := (tcP_mem μ o).2.1

/-- **A value `v` of `Φ_μ` is a fixed point of every `Φ_j`, `j < μ`, with `tcDatL j < v`.** -/
theorem tcP_fix_lower {j μ v : Ordinal.{0}} (h : j < μ) (hv : v ∈ range (tcP μ)) (hj : tcDatL j < v) :
    tcP j v = v := by
  rw [tcP_range_eq] at hv; exact hv.2.2 j h hj

/-- **A value of `Φ_μ`**: a strongly critical `v` with `tcDatL μ < v` that is a fixed point of every `Φ_j`, `j < μ`,
`tcDatL j < v`. -/
theorem tcP_range {μ v : Ordinal.{0}} (hSC : SC v) (hμ : tcDatL μ < v)
    (hfix : ∀ j < μ, tcDatL j < v → tcP j v = v) : ∃ e, tcP μ e = v := by
  have : v ∈ range (tcP μ) := by rw [tcP_range_eq]; exact ⟨hSC, hμ, hfix⟩
  exact this

/-- **A fixed point of `Φ_μ` is a fixed point of every `Φ_j`, `j ≤ μ`, with `tcDatL j < x`.** -/
theorem tcP_fix_mono {j μ x : Ordinal.{0}} (h : j ≤ μ) (hx : tcP μ x = x) (hj : tcDatL j < x) : tcP j x = x := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hx
  · exact tcP_fix_lower hlt ⟨x, hx⟩ hj

/-- **`τ ≤ tcDatL μ` is not a fixed point of `Φ_μ`.** -/
theorem tcP_ne_self_of_dat {μ τ : Ordinal.{0}} (hτ : τ ≤ tcDatL μ) : tcP μ τ ≠ τ := fun h =>
  absurd (hτ.trans_lt (tcDatL_lt_tcP μ τ)) (by rw [h]; exact lt_irrefl _)

/-- A fixed point `p` of `Φ_μ` lies above `tcDatL μ`. -/
theorem tcDatL_lt_fix {μ p : Ordinal.{0}} (hp : tcP μ p = p) : tcDatL μ < p := by
  rw [← hp]; exact tcDatL_lt_tcP μ p

/-- A value of `Φ_μ` is closed under the lower levels. -/
theorem tc_clo_val (μ o : Ordinal.{0}) :
    ∀ j < μ, tcDatL j < tcP μ o → ∀ z < tcP μ o, tcP j z < tcP μ o := fun j hj hd z hz => by
  have h := (tcP_lt_iff j).2 hz
  rwa [tcP_fix_lower hj ⟨o, rfl⟩ hd] at h




/-! ## Agreement with `Ss.ssP` up to `Γ_{Ω₁+1}` -/

/-- **`tcDatL μ = ssDatL μ` for `μ ≤ Γ_{Ω₁+1}`.** -/
theorem tcDatL_eq_ss {μ : Ordinal.{0}} (hμ : μ ≤ ggGam) : tcDatL μ = Ss.ssDatL μ := by
  unfold tcDatL Ss.ssDatL
  rcases hμ.lt_or_eq with h | rfl
  · exact tcDat_eq_ss _ ((lq_SC_indec ggGam_spec.1).add_lt Ss.ss_Om1_lt_Gam h)
  · rw [Sv.sv_Om1_add_big ggE_le_ggGam]; exact tcDat_le_ss le_rfl

/-- **`tcP μ = ssP μ` for every `μ ≤ Γ_{Ω₁+1}`.** -/
theorem tcP_eq_ssP : ∀ μ : Ordinal.{0}, μ ≤ ggGam → tcP μ = Ss.ssP μ := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rw [tcP_eq, Ss.ssP_eq]
  congr 1
  ext v
  simp only [tcC, Ss.ssC, mem_setOf_eq]
  rw [tcDatL_eq_ss hμ]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    rw [← IH j hj (hj.le.trans hμ)]; exact h3 j hj (by rw [tcDatL_eq_ss (hj.le.trans hμ)]; exact hd)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun j hj hd => ?_⟩
    rw [IH j hj (hj.le.trans hμ)]; exact h3 j hj (by rw [← tcDatL_eq_ss (hj.le.trans hμ)]; exact hd)

theorem tcP_zero_eq : tcP 0 = gamma := by
  rw [tcP_eq_ssP 0 zero_le, Ss.ssP_eq_rkP 0 (InE.pos ggE_spec.1).le, rkP_zero]

/-! ## Codes of levels -/

theorem tc_G'_indec : Indec (lgGam' : Ordinal.{0}) := lq_SC_indec tc_SC_G'

/-- **`tcDatL μ < b` makes `μ < Γ'` a code over a strongly critical `b`.** -/
theorem tc_code_lvl {μ b : Ordinal.{0}} (hb : SC b) (hμ : μ < lgGam') (hd : tcDatL μ < b) : LgCl b μ := by
  have hO : Om1 + μ < lgGam' := tc_G'_indec.add_lt tc_Om1_lt_G' hμ
  have h := tc_code hb.1 (Om1 + μ) hO hd
  have h2 := (lgDec hb _ h).1 (Om 1) LgCl.om (by rw [← Rj.rj_Om1]; exact le_self_add)
  rwa [← Rj.rj_Om1, Ordinal.add_sub_cancel] at h2

/-- `u_μ ∈ Cl(a, b)` for a code `μ` over a strongly critical `b`, `0 < a`. -/
theorem tcU_mem {μ a b : Ordinal.{0}} (ha : 0 < a) (hb : SC b) (hμ : LgCl b μ) : Le.leOe μ ∈ S.CSet a b :=
  (LgCl.opow hb.1 (tc_cl_Om1_mul hb hμ)).mem_CSet ha le_rfl

/-- `u_μ·D ∈ Cl(a, b)` for a code `μ` over a strongly critical `b`, `D < b`, `0 < a`. -/
theorem tcU_mul_mem {μ a b D : Ordinal.{0}} (ha : 0 < a) (hb : SC b) (hμ : LgCl b μ) (hD : D < b) :
    Le.leOe μ * D ∈ S.CSet a b :=
  (tc_cl_opow_mul hb (tc_cl_Om1_mul hb hμ) D (LgCl.small hD)).mem_CSet ha le_rfl

/-! ## FWD -/

/-- **FWD(μ)** for `tcP`: `ψ_{Ω₁}(B)` is a fixed point of `tcP μ` for every own `B ≠ 0` with `u_{μ+1} ∣ B` and
`tcDatL μ < ψ_{Ω₁}(B)`. -/
def TcFWD (S : InaccSeq.{0}) (μ : Ordinal.{0}) : Prop :=
  ∀ B : Ordinal.{0}, B ∈ S.CSet B (S.psi B (Om 1)) → Le.leOe (μ + 1) ∣ B → B ≠ 0 →
    tcDatL μ < S.psi B (Om 1) → tcP μ (S.psi B (Om 1)) = S.psi B (Om 1)

/-- **FWD(μ) at every level `μ < Γ'` of `tcP`** (the proof of `Rk.rk_fwd`, codes read by `ss_cl_iff`). -/
theorem tcFwdAll (μ : Ordinal.{0}) : μ < lgGam' → TcFWD S μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  have h0 := rd_Om1_ne
  intro B hown hB hB0 hdx
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [tcP_zero_eq, ← rhF_zero]
    exact rh_fwd 0 B hown hB hB0 (lt_of_le_of_lt zero_le hdx)
  set x := S.psi B (Om 1) with hxdef
  have hx1 : x < Om 1 := psi_lt Low.InR_Om_one B
  have hxSC : SC x := SC_psi Low.InR_Om_one B
  have hlimx : IsSuccLimit x := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hxSC)
  have hμpos : 0 < μ := pos_iff_ne_zero.2 hμ0
  have hdat0 : tcDatL 0 = 0 := tcDatL_zero
  have hxΓ : gamma x = x := by
    have h1 : Le.leOe (0 + 1) ∣ B :=
      (rhU_dvd (show (0 : Ordinal.{0}) + 1 ≤ μ + 1 by rw [zero_add]; exact le_add_self)).trans hB
    have := IH 0 hμpos (hμpos.trans hμ) B hown h1 hB0 (by rw [hdat0]; exact hxSC.1)
    rwa [tcP_zero_eq] at this
  set u := Le.leOe μ with hudef
  have hu0 : u ≠ 0 := rhU_ne μ
  have hupos : 0 < u := rhU_pos μ
  obtain ⟨m, hm⟩ := hB
  rw [Le.leOe_succ, ← hudef, mul_assoc] at hm
  have key : ∀ z < x, tcP μ z < x := by
    intro z hz
    set a := tcDatL μ + z + 1 with hadef
    have hax : a < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hdx hz)
    set p := gamma a with hpdef
    have hpx : p < x := by rw [← hxΓ]; exact gamma_lt_gamma.2 hax
    have hpSC : SC p := lq_gamma_SC a
    have hap : a < p := lt_of_le_of_ne (lq_le_gamma a) fun e => SC.ne_add_one hpSC (tcDatL μ + z) e.symm
    have hdp : tcDatL μ < p := (le_self_add.trans_lt (lt_add_one (tcDatL μ + z))).trans hap
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
    have hde : tcDatL μ < S.psi e (Om 1) := hdp.trans_le hpe
    have hBpmem : Bp ∈ S.CSet e (S.psi e (Om 1)) := (psi_mono Low.InR_Om_one hBpe).2 hownp
    have howne : e ∈ S.CSet e (S.psi e (Om 1)) :=
      CSet.add_mem (rh_mod_mem (one_le_iff_ne_zero.2 hμ0) Bp hBpmem)
        (tcU_mem (lt_of_lt_of_le (rhU_pos μ) le_add_self) (SC_psi Low.InR_Om_one _)
          (tc_code_lvl (SC_psi Low.InR_Om_one _) hμ hde))
    have hue : u ∣ e := ⟨Bp / u + 1, by rw [hedef, mul_add, mul_one]⟩
    have hue0 : 0 < e := lt_of_lt_of_le hupos le_add_self
    have hed : ∀ d, d < S.psi e (Om 1) →
        e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) ∧
          ∃ w, tcP μ w = S.psi (e + u * d) (Om 1) := by
      intro d hd
      have hle : S.psi e (Om 1) ≤ S.psi (e + u * d) (Om 1) := (psi_mono Low.InR_Om_one le_self_add).1
      have hownd : e + u * d ∈ S.CSet (e + u * d) (S.psi (e + u * d) (Om 1)) :=
        CSet.add_mem ((psi_mono Low.InR_Om_one le_self_add).2 howne)
          (tcU_mul_mem (lt_of_lt_of_le (lt_of_lt_of_le (rhU_pos μ) le_add_self) le_self_add) (SC_psi Low.InR_Om_one _)
            (tc_code_lvl (SC_psi Low.InR_Om_one _) hμ (hde.trans_le hle)) (hd.trans_le hle))
      refine ⟨hownd, tcP_range (SC_psi Low.InR_Om_one _) (hde.trans_le hle)
        fun j hj hdj => ?_⟩
      exact IH j hj (hj.trans hμ) _ hownd ((rhU_dvd_succ hj).trans (dvd_add hue (dvd_mul_right _ _)))
        (lt_of_lt_of_le hue0 le_self_add).ne' hdj
    have hmono : ∀ d d', d < d' → d' < S.psi e (Om 1) →
        S.psi (e + u * d) (Om 1) < S.psi (e + u * d') (Om 1) := fun d d' hdd hd' =>
      rh_psi_lt_of_own (hed d (hdd.trans hd')).1
        ((add_lt_add_iff_left e).2 ((mul_lt_mul_iff_right₀ hupos).2 hdd))
    have hcount : ∀ d, d < S.psi e (Om 1) → ∀ w, tcP μ w = S.psi (e + u * d) (Om 1) → d ≤ w := by
      intro d
      induction d using WellFoundedLT.induction with
      | ind d IHd =>
      intro hd w hw
      by_contra hwd
      push Not at hwd
      obtain ⟨w', hw'⟩ := (hed w (hwd.trans hd)).2
      have h1 := IHd w hwd (hwd.trans hd) w' hw'
      have h2 : tcP μ w' < tcP μ w := by rw [hw', hw]; exact hmono w d hwd hd
      exact absurd ((tcP_lt_iff μ).1 h2) (not_lt.2 h1)
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
    calc tcP μ z < tcP μ w := (tcP_lt_iff μ).2 hzw
      _ = _ := hw
      _ < x := hψlt
  exact le_antisymm (((tcP_normal μ).le_iff_forall_le hlimx).2 fun z hz => (key z hz).le)
    (tcP_le_self μ x)


end Googology.Trans.PoR.InaccPsi.R2.Tc
