import Googology.Trans.PoR.InaccPsi.R2.LsStrict
import Googology.Trans.PoR.InaccPsi.R2.FpB0
import Googology.Trans.PoR.InaccPsi.R2.CvNamed
import Googology.Trans.PoR.InaccPsi.R2.RmNamed
import Googology.Trans.PoR.InaccPsi.R2.RzName

/-!
# Range restarts with the code `G(θ_{k+1}·ω²) + 1`, cofinal below `m*` and below every `L(n+1)`

`G' = G_{k+1} = G(θ_{k+1}·ω²)` (`lsG S (k+1)`), `L(ξ) = Nc.ncL S ξ`, `m* = L(0) = P(Ω_ω)`, `P = Nm.Pv`,
`c_j = ψ_{Ω₂}(Ω_ω + Ω_{j+1})` (`Rm.rmC`, cofinal in `P'`), Range = `CdRange`.  The names are
`η = η₀ + G'·ω = η₀ + ω^{G'+1}` with `η₀ = Ω_j` (below `m*`) or `η₀ = Ω_ω + P'·n + c_j` (below `L(n+1)`):

* `lsTh_mem`, `lsArg_mem`, `lsG_mem` (**`G' ∈ Cl(a, b)` once `Ω_ω < a` and `θ₂·θ_{k+1}·ω² < a − Ω_ω`**),
  `lsArg_lt` (`θ₂·θ_{k+1}·ω² < Ω_{k+3}`), `lsG_lt_ck` (`G' < c_j` for `j ≥ k+2`), `lsG_lt_Pp` (`G' < P'`);
* `lsName` (**the name lemma**): for a good `η₀ ≥ Ω_{k+3}` with `ω^{G'+1} ∣ η₀`, `η = η₀ + G'·ω` is good,
  `μ = ι(η)` is a restart index, `η_μ = η`, the code is `m_μ = G' + 1`, `ρ_μ = P(η)` and `P(η₀) < ρ_μ`
  (the `ι`-values of the good names `η₀ + G'·n` step by `ω²`, `Pp.ppIota_add`, so their supremum is a
  multiple of `ω²`, `Pp.ppDvd_of_add`);
* `lsNames_M` (**cofinal below `m*`**), `lsNames_L` (**cofinal below `L(n+1)`**): for every `γ` below the
  point, a Range restart `μ` with `γ < ρ_μ <` the point and `m_μ = G' + 1`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-! ## `G'` in the hulls -/

theorem lsOmNat_mem (a b : Ordinal.{0}) (j : ℕ) : Om (j : Ordinal.{0}) ∈ S.CSet a b :=
  CSet.Om_mem (Pp.ppNat_mem a b j)

/-- `θ_m ∈ Cl(a, b)` for `Ω_ω < a`. -/
theorem lsTh_mem {a b : Ordinal.{0}} (ha : Om ω < a) (m : ℕ) : Lc.lcTh S m ∈ S.CSet a b := by
  unfold Lc.lcTh
  exact CSet.psi_mem ha (InR_Om_succ _) (CSet.Om_mem (CSet.succ_mem (Pp.ppNat_mem a b m)))
    (ConjT.OmW_mem S a b)

theorem lsTh_SC (m : ℕ) : SC (Lc.lcTh S m) := SC_psi (InR_Om_succ _) _

theorem lsTh_opow (m : ℕ) : ω ^ Lc.lcTh S m = Lc.lcTh S m := Low.opow_eq_self_of_SC (lsTh_SC m)

theorem lsMul_opow {t x : Ordinal.{0}} (ht : ω ^ t = t) : t * ω ^ x = ω ^ (t + x) := by
  rw [opow_add, ht]

theorem lsTw_eq (m : ℕ) : Lc.lcTh S m * ω ^ 2 = ω ^ (Lc.lcTh S m + 2) := by
  have e : (ω : Ordinal.{0}) ^ (2 : ℕ) = ω ^ (2 : Ordinal.{0}) := by rw [← opow_natCast]; norm_num
  rw [e, lsMul_opow (lsTh_opow m)]

theorem lsOpow_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : ω ^ x ∈ S.CSet a b := by
  have := CSet.phi_mem (CSet.zero_mem (S := S) a b) hx; rwa [veblen_zero_apply] at this

/-- The argument `θ₂·(θ_{k+1}·ω²)` of `G'` (after `Ω_ω`). -/
noncomputable abbrev lsX (S : InaccSeq.{0}) (k : ℕ) : Ordinal.{0} := Lc.lcTh S 2 * (Lc.lcTh S (k + 1) * ω ^ 2)

theorem lsX_eq (k : ℕ) : lsX S k = ω ^ (Lc.lcTh S 2 + (Lc.lcTh S (k + 1) + 2)) := by
  unfold lsX; rw [lsTw_eq, lsMul_opow (lsTh_opow 2)]

theorem lsX_mem {a b : Ordinal.{0}} (ha : Om ω < a) (k : ℕ) : lsX S k ∈ S.CSet a b := by
  rw [lsX_eq]
  refine lsOpow_mem (CSet.add_mem (lsTh_mem ha 2) (CSet.add_mem (lsTh_mem ha (k + 1)) ?_))
  exact_mod_cast Pp.ppNat_mem a b 2

theorem lsX_pos (k : ℕ) : 0 < lsX S k := by rw [lsX_eq]; exact opow_pos _ omega0_pos

theorem lsG_eq (k : ℕ) : lsG S (k + 1) = S.psi (Om ω + lsX S k) (Om (1 + 1)) := rfl

/-- **`G' ∈ Cl(a, b)`** when `Ω_ω + θ₂·θ_{k+1}·ω² < a`. -/
theorem lsG_mem {a b : Ordinal.{0}} (k : ℕ) (ha : Om ω + lsX S k < a) : lsG S (k + 1) ∈ S.CSet a b := by
  have hw : Om ω < a := (lt_add_of_pos_right _ (lsX_pos k)).trans ha
  rw [lsG_eq]
  exact CSet.psi_mem ha (InR_Om_succ 1) (mxOm2_mem' a b) (CSet.add_mem (ConjT.OmW_mem S a b) (lsX_mem hw k))
where
  mxOm2_mem' (a b : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) ∈ S.CSet a b := Mx.mxOm2_mem a b

theorem lsOm_SC (j : ℕ) (hj : j ≠ 0) : SC (Om (j : Ordinal.{0})) := SC_Om (by exact_mod_cast hj)

theorem lsOm_mulP {J : Ordinal.{0}} (hJ : J ≠ 0) {x y : Ordinal.{0}} (hx : x < Om J) (hy : y < Om J) :
    x * y < Om J := by
  have hOw : ω ^ Om J = Om J := Low.opow_eq_self_of_SC (SC_Om hJ)
  have hp := isPrincipal_mul_omega0_opow_opow (Om J)
  rw [hOw, hOw] at hp
  exact hp hx hy

theorem lsTh_lt_Om (m : ℕ) : Lc.lcTh S m < Om ((m : Ordinal.{0}) + 1) := psi_lt (InR_Om_succ _) _

/-- `θ₂·θ_{k+1}·ω² < Ω_{k+3}`. -/
theorem lsArg_lt (k : ℕ) : lsX S k < Om ((k + 3 : ℕ) : Ordinal.{0}) := by
  have hJ : ((k + 3 : ℕ) : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show k + 3 ≠ 0 by omega)
  have h2 : Lc.lcTh S 2 < Om ((k + 3 : ℕ) : Ordinal.{0}) := by
    refine (lsTh_lt_Om 2).trans_le (Om_le_Om.2 ?_)
    have : ((2 : ℕ) : Ordinal.{0}) + 1 = ((3 : ℕ) : Ordinal.{0}) := by norm_num
    rw [this]; exact_mod_cast (by omega : 3 ≤ k + 3)
  have hk : Lc.lcTh S (k + 1) < Om ((k + 3 : ℕ) : Ordinal.{0}) := by
    refine (lsTh_lt_Om (k + 1)).trans_le (Om_le_Om.2 ?_)
    have : (((k + 1 : ℕ) : Ordinal.{0}) + 1) = ((k + 2 : ℕ) : Ordinal.{0}) := by norm_cast
    rw [this]; exact_mod_cast (by omega : k + 2 ≤ k + 3)
  have hw : (ω : Ordinal.{0}) ^ 2 < Om ((k + 3 : ℕ) : Ordinal.{0}) := by
    rw [pow_two]
    exact (ppSC_ww' (lsOm_SC (k + 3) (Nat.succ_ne_zero _)))
  exact lsOm_mulP hJ h2 (lsOm_mulP hJ hk hw)
where
  ppSC_ww' {γ : Ordinal.{0}} (h : SC γ) : (ω : Ordinal.{0}) * ω < γ := Pp.ppSC_ww h

theorem lsArg_own (k : ℕ) :
    Om ω + lsX S k ∈ S.CSet (Om ω + lsX S k) (S.psi (Om ω + lsX S k) (Om (1 + 1))) :=
  CSet.add_mem (ConjT.OmW_mem S _ _) (lsX_mem (lt_add_of_pos_right _ (lsX_pos k)) k)

/-- `G' < c_j` for `j ≥ k + 2`. -/
theorem lsG_lt_ck {k j : ℕ} (hj : k + 2 ≤ j) : lsG S (k + 1) < Rm.rmC S j := by
  rw [lsG_eq]
  refine psi_lt_psi (InR_Om_succ 1) ((add_lt_add_iff_left _).2 ((lsArg_lt k).trans_le ?_)) (lsArg_own k)
  exact Om_le_Om.2 (by exact_mod_cast (by omega : k + 3 ≤ j + 1))

theorem lsG_lt_Pp (k : ℕ) : lsG S (k + 1) < Nc.ncPp S :=
  (lsG_lt_ck (S := S) (le_refl (k + 2))).trans (Pp.ppC_lt (k + 2))

theorem lsG_lt_OmW (k : ℕ) : lsG S (k + 1) < Om ω :=
  ((Lc.lcG_lt_Om2 _).trans_le (Om_le_Om.2 (by exact_mod_cast (le_of_lt (nat_lt_omega0 2))))).trans_le le_rfl
where
  nat_lt_omega0 (n : ℕ) : ((n : ℕ) : Ordinal.{0}) < ω := Ordinal.natCast_lt_omega0 n

/-! ## The name lemma -/

theorem lsG_opow (k : ℕ) : ω ^ lsG S (k + 1) = lsG S (k + 1) := Low.opow_eq_self_of_SC (lsG_SC _)

theorem lsG_omega (k : ℕ) : ω ^ (lsG S (k + 1) + 1) = lsG S (k + 1) * ω := by
  rw [opow_add, opow_one, lsG_opow]

theorem lsA_ge (η : Ordinal.{0}) : Om ω + η ≤ ConjT.Aη S η := by
  unfold ConjT.Aη
  exact add_le_add le_rfl (Ordinal.le_mul_right η (SC_psi (InR_Om_succ 1) _).1)

/-- **The name lemma.** -/
theorem lsName {k : ℕ} {η0 : Ordinal.{0}} (hg : Bt.Good S η0)
    (hJ : Om ((k + 3 : ℕ) : Ordinal.{0}) ≤ η0) (hd : ω ^ (lsG S (k + 1) + 1) ∣ η0) :
    Bt.Good S (η0 + lsG S (k + 1) * ω) ∧ IsRestartIdx (iota S (η0 + lsG S (k + 1) * ω)) ∧
      cdEta S (iota S (η0 + lsG S (k + 1) * ω)) = η0 + lsG S (k + 1) * ω ∧
      cdCode S (iota S (η0 + lsG S (k + 1) * ω)) = lsG S (k + 1) + 1 ∧
      upsilon (iota S (η0 + lsG S (k + 1) * ω)) = Nm.Pv S (η0 + lsG S (k + 1) * ω) ∧
      Nm.Pv S η0 < Nm.Pv S (η0 + lsG S (k + 1) * ω) := by
  set G := lsG S (k + 1) with hGdef
  set η := η0 + G * ω with hη
  have hGSC : SC G := lsG_SC _
  have hG0 : 0 < G := hGSC.1
  -- `G` is in every hull of a name `≥ η₀`
  have hGmem : ∀ η', η0 ≤ η' → G ∈ S.CSet (ConjT.Aη S η' + 1) (Nm.Pv S η') := by
    intro η' hη'
    refine lsG_mem k ?_
    refine lt_of_lt_of_le ?_ (le_self_add.trans (add_le_add (lsA_ge η') le_rfl))
    exact (add_lt_add_iff_left _).2 ((lsArg_lt k).trans_le (hJ.trans hη'))
  -- the good names `η₀ + G·n`
  have hxg : ∀ n : ℕ, Bt.Good S (η0 + G * n) := by
    intro n
    induction n with
    | zero => simpa using hg
    | succ n ih =>
      have e : η0 + G * ((n + 1 : ℕ) : Ordinal.{0}) = η0 + G * n + G := by
        rw [Nat.cast_succ, mul_add_one, add_assoc]
      rw [e]
      exact Nm.good_add ih (by rw [← e]; exact hGmem _ (le_self_add))
  have hηg : Bt.Good S η := by
    refine Nm.good_add hg ?_
    rw [← lsG_omega]
    exact lsOpow_mem (CSet.succ_mem (hGmem _ le_self_add))
  have hlim : IsSuccLimit η := isSuccLimit_add _ (isSuccLimit_mul_right hG0 isSuccLimit_omega0)
  have hxη : ∀ n : ℕ, η0 + G * n < η := fun n =>
    (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hG0).2 (Ordinal.natCast_lt_omega0 n))
  -- the restart index
  have hri : IsRestartIdx (iota S η) := by
    refine ri_iff.2 ⟨(lt_of_lt_of_le zero_lt_one (one_le_iota _)).ne', Pp.ppDvd_of_add fun z hz => ?_⟩
    have hz' := hz
    rw [iota_limit hlim] at hz'
    haveI : Nonempty (Iio η) := ⟨⟨0, hlim.bot_lt⟩⟩
    obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hz'
    have hn : ∃ n : ℕ, e.1 ≤ η0 + G * n := by
      rcases lt_or_ge e.1 η0 with h | h
      · exact ⟨0, by simpa using h.le⟩
      · obtain ⟨d, hd'⟩ := exists_add_of_le h
        have hdG : d < G * ω := by
          have := e.2; rw [hd'] at this; exact (add_lt_add_iff_left _).1 this
        obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 hdG
        obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hc
        exact ⟨n, by rw [hd']; exact add_le_add le_rfl hdc.le⟩
    obtain ⟨n, hn⟩ := hn
    have hstep : iota S (η0 + G * n + (ω : Ordinal.{0}) * ω) = iota S (η0 + G * n) + (ω : Ordinal.{0}) * ω :=
      Pp.ppIota_add _ _ fun y hy =>
        Rz.rz_good_shift (hxg n) (hy.trans (Pp.ppSC_ww (Nm.Pv_SC S _)))
    have hle : η0 + G * n + (ω : Ordinal.{0}) * ω ≤ η := by
      refine le_trans ?_ (hxη (n + 1)).le
      rw [Nat.cast_succ, mul_add_one, add_assoc]
      exact add_le_add le_rfl (add_le_add le_rfl (Pp.ppSC_ww hGSC).le)
    calc z + (ω : Ordinal.{0}) * ω ≤ iota S e.1 + (ω : Ordinal.{0}) * ω := add_le_add he.le le_rfl
      _ ≤ iota S (η0 + G * n) + (ω : Ordinal.{0}) * ω := add_le_add (iota_mono _ _ hn) le_rfl
      _ = iota S (η0 + G * n + (ω : Ordinal.{0}) * ω) := hstep.symm
      _ ≤ iota S η := iota_mono _ _ hle
  -- the code
  have hη0' : η ≠ 0 := hlim.ne_bot
  have hexp : cdExp η = G + 1 := by
    refine cdExp_eq hη0' ?_ ?_
    · rw [hη, ← lsG_omega]; exact dvd_add hd (dvd_refl _)
    · rintro ⟨d, hd'⟩
      obtain ⟨q, hq⟩ := hd
      have e1 : η = ω ^ (G + 1) * (q + 1) := by
        rw [hη, ← lsG_omega, hq, mul_add_one]
      have e2 : ω ^ (G + 1 + 1) * d = ω ^ (G + 1) * (ω * d) := by
        rw [opow_add (ω : Ordinal.{0}) (G + 1) 1, opow_one, mul_assoc]
      rw [e1, e2] at hd'
      have hc : q + 1 = ω * d := mul_left_cancel₀ (opow_ne_zero _ omega0_ne_zero) hd'
      have hpre : IsSuccPrelimit (q + 1) := by
        rw [hc]; exact isSuccPrelimit_iff_omega0_dvd.2 (dvd_mul_right _ _)
      exact not_isSuccPrelimit_succ q (by rwa [Order.succ_eq_add_one])
  have hG1 : G + 1 < Om (1 + 1) := (SC_Om (by simp)).add_one_lt (Lc.lcG_lt_Om2 _)
  have hcode : cdCode S (iota S η) = G + 1 := by
    unfold cdCode
    rw [cdEta_unique hηg rfl, cdCodeOf_of_lt (by rw [hexp]; exact hG1), hexp]
    unfold cdOff
    rw [if_neg]
    exact not_lt.2 ((Pp.ppOmega_lt_SC hGSC).le.trans le_self_add)
  refine ⟨hηg, hri, cdEta_unique hηg rfl, hcode, Bt.ups_iota S η, ?_⟩
  have h1 := cd_iota_lt_of_good hg (lt_add_of_pos_right η0 (mul_pos hG0 omega0_pos))
  have h2 := upsilon_normal.strictMono h1
  rwa [Bt.ups_iota, Bt.ups_iota] at h2

/-! ## Cofinal below `m*` and below `L(n+1)` -/

/-- `γ < P(x)` at a restart value `P(x) = υ_{ι(x)}` gives some `e < x` with `γ < P(e)`. -/
theorem lsPv_cof {x γ : Ordinal.{0}} (hx : IsRestartIdx (iota S x)) (hlx : IsSuccLimit x)
    (hγ : γ < Nm.Pv S x) : ∃ e < x, γ < Nm.Pv S e := by
  have eU := Bt.ups_iota S x
  replace hγ : γ < upsilon (iota S x) := by rw [eU]; exact hγ
  obtain ⟨ζ, hζ, hγζ⟩ := (upsilon_normal.lt_iff_exists_lt (ri_lim hx)).1 hγ
  have hζ' := hζ
  rw [iota_limit hlx] at hζ'
  haveI : Nonempty (Iio x) := ⟨⟨0, hlx.bot_lt⟩⟩
  obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd _)).1 hζ'
  refine ⟨e.1, e.2, ?_⟩
  have h3 := hγζ.trans (upsilon_normal.strictMono he)
  rwa [Bt.ups_iota] at h3

theorem lsM_eq : Nc.ncL S 0 = Nm.Pv S (Om ω) := by rw [Lw.lw_L_eq]; simp

theorem lsM_ri : IsRestartIdx (iota S (Om ω)) := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have e2 : upsilon (iota S (Om ω)) = upsilon l := by rw [Bt.ups_iota]; exact lsM_eq.symm.trans e
  rw [upsilon_normal.strictMono.injective e2]; exact hl

theorem lsRange_of {μ : Ordinal.{0}} {k : ℕ} (hri : IsRestartIdx μ) (hB : upsilon cdB0 < upsilon μ)
    (hlt : upsilon μ < Nc.ncL S (ω + 1)) (hc : cdCode S μ = lsG S (k + 1) + 1) : CdRange S μ :=
  ⟨hri, (upsilon_normal.strictMono.lt_iff_lt.1 hB).le, hlt,
    by rw [hc]; exact (Nc.ncPp_SC S).add_one_lt (lsG_lt_Pp k)⟩

/-- **Range restarts with the code `G' + 1`, cofinal below `m*`.** -/
theorem lsNames_M (k : ℕ) : ∀ γ < Nc.ncL S 0, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
    upsilon μ < Nc.ncL S 0 ∧ cdCode S μ = lsG S (k + 1) + 1 := by
  intro γ hγ
  set γ' := max γ (upsilon cdB0)
  have hγ' : γ' < Nm.Pv S (Om ω) := by
    rw [← lsM_eq]; exact max_lt hγ Fp.fpB0_lt_M
  obtain ⟨e, he, hγe⟩ := lsPv_cof lsM_ri (Om_isSuccLimit omega0_ne_zero) hγ'
  obtain ⟨m, hm⟩ := Pp.ppLt_Om_omega he
  set j := max (m + 1) (k + 3) with hjdef
  have hj0 : j ≠ 0 := by omega
  have hjSC := lsOm_SC j hj0
  have hgj : Bt.Good S (Om (j : Ordinal.{0})) := lsOmNat_mem _ _ j
  have hJ : Om ((k + 3 : ℕ) : Ordinal.{0}) ≤ Om (j : Ordinal.{0}) :=
    Om_le_Om.2 (by exact_mod_cast le_max_right _ _)
  have h2j : Om (1 + 1 : Ordinal.{0}) ≤ Om (j : Ordinal.{0}) :=
    Om_le_Om.2 (by rw [one_add_one_eq_two]; exact_mod_cast (by omega : 2 ≤ j))
  have hG1 : lsG S (k + 1) + 1 < Om (j : Ordinal.{0}) :=
    hjSC.add_one_lt ((Lc.lcG_lt_Om2 _).trans_le h2j)
  have hd : ω ^ (lsG S (k + 1) + 1) ∣ Om (j : Ordinal.{0}) := by
    rw [← Low.opow_eq_self_of_SC hjSC]; exact opow_dvd_opow ω hG1.le
  obtain ⟨hηg, hri, -, hcode, hups, hlt⟩ := lsName hgj hJ hd
  set η := Om (j : Ordinal.{0}) + lsG S (k + 1) * ω
  have hηω : η < Om ω := by
    have hOw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
    refine hOw.isPrincipal (Om_lt_Om.2 (Ordinal.natCast_lt_omega0 j)) ?_
    rw [← lsG_omega]
    rw [← Low.opow_eq_self_of_SC hOw]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (hOw.add_one_lt (lsG_lt_OmW k))
  have hup : upsilon (iota S η) < Nc.ncL S 0 := by
    rw [lsM_eq]
    have h3 := upsilon_normal.strictMono (cd_iota_lt_of_good hηg hηω)
    rw [Bt.ups_iota, Bt.ups_iota] at h3
    rw [hups]; exact h3
  have hlow : γ' < upsilon (iota S η) := by
    rw [hups]
    refine hγe.trans_le ((Nm.Pv_mono ?_).trans hlt.le)
    exact hm.le.trans (Om_le_Om.2 (by exact_mod_cast le_max_left _ _))
  refine ⟨iota S η, lsRange_of hri ((le_max_right _ _).trans_lt hlow)
    (hup.trans_le (Pp.ppL_mono zero_le)) hcode, (le_max_left _ _).trans_lt hlow, hup, hcode⟩

/-- **Range restarts with the code `G' + 1`, cofinal below `L(n+1)`.** -/
theorem lsNames_L (n k : ℕ) : ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, CdRange S μ ∧
    γ < upsilon μ ∧ upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ cdCode S μ = lsG S (k + 1) + 1 := by
  intro γ hγ
  set base := Om ω + Nc.ncPp S * (n : Ordinal.{0}) with hbase
  have eL : Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) = Nm.Pv S (base + Nc.ncPp S) := by
    rw [Lw.lw_L_eq, Rm.rm_eta_succ]
  have hri0 : IsRestartIdx (iota S (base + Nc.ncPp S)) := by
    have := Pp.ppIota_succ_restart (S := S) n; rwa [Rm.rm_eta_succ] at this
  have hlim : IsSuccLimit (base + Nc.ncPp S) := isSuccLimit_add _ (Nc.ncPp_SC S).isSuccLimit
  set γ' := max γ (upsilon cdB0)
  have hB : upsilon cdB0 < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) :=
    Fp.fpB0_lt_M.trans_le (Pp.ppL_mono zero_le)
  have hγ' : γ' < Nm.Pv S (base + Nc.ncPp S) := by rw [← eL]; exact max_lt hγ hB
  obtain ⟨e, he, hγe⟩ := lsPv_cof hri0 hlim hγ'
  have hk : ∃ m : ℕ, e ≤ base + Rm.rmC S m := by
    rcases lt_or_ge e base with h | h
    · exact ⟨0, h.le.trans le_self_add⟩
    · obtain ⟨d, hd⟩ := exists_add_of_le h
      have hdP : d < Nc.ncPp S := by rw [hd] at he; exact (add_lt_add_iff_left _).1 he
      obtain ⟨m, hm⟩ := Pp.ppPp_cof d hdP
      exact ⟨m, by rw [hd]; exact add_le_add le_rfl hm.le⟩
  obtain ⟨m, hm⟩ := hk
  set j := max m (k + 2) with hjdef
  have hcSC : SC (Rm.rmC S j) := SC_psi (InR_Om_succ 1) _
  have hgj : Bt.Good S (base + Rm.rmC S j) := by
    have := Pp.ppGood_ck (S := S) n j (y := 0) (mul_pos omega0_pos omega0_pos)
    rwa [add_zero] at this
  have hOwb : Om ω ≤ base := le_self_add
  have hJ : Om ((k + 3 : ℕ) : Ordinal.{0}) ≤ base + Rm.rmC S j :=
    ((Om_le_Om.2 (Ordinal.natCast_lt_omega0 _).le).trans hOwb).trans le_self_add
  have hGc : lsG S (k + 1) < Rm.rmC S j := lsG_lt_ck (le_max_right _ _)
  have hG1c : lsG S (k + 1) + 1 ≤ Rm.rmC S j := Order.add_one_le_of_lt hGc
  have hG1P : lsG S (k + 1) + 1 ≤ Nc.ncPp S := Order.add_one_le_of_lt (lsG_lt_Pp k)
  have hG1W : lsG S (k + 1) + 1 ≤ Om ω :=
    Order.add_one_le_of_lt (lsG_lt_OmW k)
  have hd : ω ^ (lsG S (k + 1) + 1) ∣ base + Rm.rmC S j := by
    refine dvd_add (dvd_add ?_ ?_) ?_
    · rw [← Low.opow_eq_self_of_SC (SC_Om omega0_ne_zero)]; exact opow_dvd_opow ω hG1W
    · rw [← Lw.lw_Pp_opow]; exact (opow_dvd_opow ω hG1P).mul_right _
    · rw [← Low.opow_eq_self_of_SC hcSC]; exact opow_dvd_opow ω hG1c
  obtain ⟨hηg, hri, -, hcode, hups, hlt⟩ := lsName hgj hJ hd
  set η := base + Rm.rmC S j + lsG S (k + 1) * ω
  have hηP : η < base + Nc.ncPp S := by
    show base + Rm.rmC S j + lsG S (k + 1) * ω < base + Nc.ncPp S
    rw [add_assoc base]
    refine (add_lt_add_iff_left _).2 ((Nc.ncPp_SC S).isPrincipal (Pp.ppC_lt j) ?_)
    rw [← lsG_omega, ← Lw.lw_Pp_opow]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 ((Nc.ncPp_SC S).add_one_lt (lsG_lt_Pp k))
  have hup : upsilon (iota S η) < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
    rw [eL]
    have h3 := upsilon_normal.strictMono (cd_iota_lt_of_good hηg hηP)
    rw [Bt.ups_iota, Bt.ups_iota] at h3
    rw [hups]; exact h3
  have hlow : γ' < upsilon (iota S η) := by
    rw [hups]
    refine hγe.trans_le ((Nm.Pv_mono (hm.trans ?_)).trans hlt.le)
    refine add_le_add le_rfl ?_
    unfold Rm.rmC
    refine (psi_mono (InR_Om_succ 1) ?_).1
    exact add_le_add le_rfl (Om_le_Om.2 (by exact_mod_cast (by omega : m + 1 ≤ j + 1)))
  have hupω : upsilon (iota S η) < Nc.ncL S (ω + 1) :=
    hup.trans ((Pp.ppL_lt_omega n).trans_le (Pp.ppL_mono le_self_add))
  exact ⟨iota S η, lsRange_of hri ((le_max_right _ _).trans_lt hlow) hupω hcode,
    (le_max_left _ _).trans_lt hlow, hup, hcode⟩

end Googology.Trans.PoR.InaccPsi.R2.Ls
