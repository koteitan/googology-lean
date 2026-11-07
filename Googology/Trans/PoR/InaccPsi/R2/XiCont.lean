import Googology.Trans.PoR.InaccPsi.R2.XiHull
import Googology.Trans.PoR.InaccPsi.R2.ZnFix
import Googology.Trans.PoR.InaccPsi.R2.RzName
import Googology.Trans.PoR.InaccPsi.R2.PpIdx
import Googology.Trans.PoR.InaccPsi.R2.ORecX
import Googology.Trans.PoR.InaccPsi.R2.ZrRead

/-!
# XiCont: THE CODE CONTINUITY FROM THE DICTIONARY

For a restart `λ < ι(η₀)` with `ρ_λ < Θ_λ(m_λ) ≤ υ_{λ+1}`, every code `c < m_λ` read at `λ` lies below `θ`
(the reading of `θ` is already `υ_{λ+1}`: `R_{ρ_λ}` maps the codes below `θ` onto `T^{ρ_λ} ∩ Ω₁ = υ_{λ+1}`).
So `Θ_λ(c) = R_{ρ_λ}(c)` (`Xi.xi_cdTheta`), and at a restart `μ < λ` with `c` visible at `ρ_μ`,
`π_{ρ_μ,ρ_λ}(Θ_λ(c)) = R_{ρ_μ}(c) = Θ_μ(c)` (`Xi.xiR_pi`).  The restarts with `m_μ ≥ c` are cofinal below `λ`:
for a good name `g` above any given index, `ζ = g + ω^{e'}` (`e' = c + 2` for finite `c`, `e' = c` otherwise,
`e' < e(η_λ)` as `m_λ > ρ_λ` is infinite) is good, `ω² ∣ ζ`, so `μ = ι(ζ)` is a restart with `η_μ = ζ` and
`m_μ = -1 + e' ≥ c`:

* `xi_hull_of_dom` (**a code below `θ` visible at `ρ` lies in every hull `Cl(A, ρ)`, `A ≥ Ω_ω`**);
* `xi_opow_decomp`, `xi_add_opow_le`, `xi_exp_add` (**`e(g + ω^x) = x`**);
* `xi_ri_of_dvd` (**`ι(ζ)` is a restart index for every `ζ ≠ 0` with `ω² ∣ ζ`**);
* `xi_theta_th` (**`υ_{λ+1} ≤ Θ_λ(θ)`**);
* `xi_code_cont` (**`Zn.ZnThCont S λ`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **A code below `θ` visible at `ρ` lies in every hull `Cl(A, ρ)` with `Ω_ω ≤ A`.** -/
theorem xi_hull_of_dom {A ρ : Ordinal.{0}} (hA : Om ω ≤ A) (hρS : SC ρ) (hρ1 : ρ < Om1)
    (hnot : ∀ z < ρ, z ∈ ⋃ e, S.CSet e 0) {c : Ordinal.{0}} (hcθ : c < ConjT.th S) (hc : WDom S ρ c) :
    c ∈ S.CSet A ρ := by
  have hρ1' : ρ ≤ Om 1 := by rw [← Rj.rj_Om1]; exact hρ1.le
  have hc' := (xi_dom_codes hρS hρ1 hcθ).2 hc
  clear hc hcθ
  induction hc' with
  | small h => exact CSet.of_lt h
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact Qt.qt_mem hA hρS hρ1' le_rfl hnot hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-! ## `g + ω^x` -/

/-- `g + ω^x = ω^x·(g / ω^x + 1)`. -/
theorem xi_opow_decomp (g x : Ordinal.{0}) : g + ω ^ x = ω ^ x * (g / ω ^ x + 1) := by
  have hpos : (0 : Ordinal.{0}) < ω ^ x := opow_pos _ omega0_pos
  conv_lhs => rw [← Ordinal.div_add_mod g (ω ^ x)]
  rw [add_assoc, add_omega0_opow (Ordinal.mod_lt g hpos.ne'), mul_add_one]

/-- `g + ω^x ≤ η` for `g < η` and `ω^x ∣ η`. -/
theorem xi_add_opow_le {g η x : Ordinal.{0}} (hd : ω ^ x ∣ η) (hg : g < η) : g + ω ^ x ≤ η := by
  have hpos : (0 : Ordinal.{0}) < ω ^ x := opow_pos _ omega0_pos
  obtain ⟨q, rfl⟩ := hd
  rw [xi_opow_decomp]
  exact mul_le_mul_right (Order.add_one_le_of_lt ((Ordinal.lt_mul_iff_div_lt hpos.ne').1 hg)) _

/-- **`e(g + ω^x) = x`**. -/
theorem xi_exp_add (g x : Ordinal.{0}) : Cd.cdExp (g + ω ^ x) = x := by
  have hpos : (0 : Ordinal.{0}) < ω ^ x := opow_pos _ omega0_pos
  have hne : g + ω ^ x ≠ 0 := (lt_of_lt_of_le hpos le_add_self).ne'
  refine Cd.cdExp_eq hne ⟨_, xi_opow_decomp g x⟩ fun h => ?_
  rw [xi_opow_decomp] at h
  obtain ⟨t, ht⟩ := h
  rw [opow_add, opow_one, mul_assoc] at ht
  have ht' : g / ω ^ x + 1 = ω * t := (isNormal_mul_right hpos).strictMono.injective ht
  have hdiv : ω ∣ succ (g / ω ^ x) := ⟨t, by rw [succ_eq_add_one]; exact ht'⟩
  exact (isSuccPrelimit_iff_omega0_dvd.2 hdiv).succ_ne _ rfl

/-! ## Restart indices -/

theorem xi_ww_eq : (ω : Ordinal.{0}) * ω = ω ^ (2 : Ordinal.{0}) := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, opow_add, opow_one]

/-- **`ι(ζ)` is a restart index for every `ζ ≠ 0` with `ω² ∣ ζ`**: each good name `g < ζ` has the good names
`g + y`, `y < ω²`, above it (`Rz.rz_good_shift`), so `ι(g) + ω² = ι(g + ω²) ≤ ι(ζ)`. -/
theorem xi_ri_of_dvd {ζ : Ordinal.{0}} (h0 : ζ ≠ 0) (hd : ω * ω ∣ ζ) : IsRestartIdx (Bt.iota S ζ) := by
  have hd2 : ω ^ (2 : Ordinal.{0}) ∣ ζ := by rw [← xi_ww_eq]; exact hd
  have hshift : ∀ g, Bt.Good S g → Bt.iota S (g + ω * ω) = Bt.iota S g + ω * ω := fun g hg =>
    Pp.ppIota_add _ _ fun y hy => Rz.rz_good_shift hg
      (hy.trans ((Pp.ppSC_ww (Nm.Pv_SC S g)).trans_le (Nm.Pv_mono le_self_add)))
  refine ri_iff.2 ⟨(lt_of_lt_of_le zero_lt_one (Bt.one_le_iota _)).ne', Pp.ppDvd_of_add fun z hz => ?_⟩
  rcases lt_or_ge z 1 with hz1 | hz1
  · rw [Order.lt_one_iff.1 hz1, zero_add]
    have hle : (ω : Ordinal.{0}) * ω ≤ ζ := by
      have := xi_add_opow_le hd2 (pos_iff_ne_zero.2 h0)
      rwa [zero_add, ← xi_ww_eq] at this
    calc (ω : Ordinal.{0}) * ω ≤ 1 + ω * ω := le_add_self
      _ = Bt.iota S (0 + ω * ω) := by rw [hshift 0 (Nm.good_zero S), Bt.iota_zero]
      _ ≤ Bt.iota S ζ := Bt.iota_mono _ _ (by rw [zero_add]; exact hle)
  · obtain ⟨hg, hι, hgζ⟩ := Cd.cdEta_spec (S := S) hz1 hz
    have hle : Cd.cdEta S z + ω * ω ≤ ζ := by
      have := xi_add_opow_le hd2 hgζ
      rwa [← xi_ww_eq] at this
    calc z + ω * ω = Bt.iota S (Cd.cdEta S z) + ω * ω := by rw [hι]
      _ = Bt.iota S (Cd.cdEta S z + ω * ω) := (hshift _ hg).symm
      _ ≤ Bt.iota S ζ := Bt.iota_mono _ _ hle

/-! ## The reading of `θ` -/

/-- **`υ_{λ+1} ≤ Θ_λ(θ)`** when `ρ_λ = P(η_λ)` and `υ_{λ+1} < Ω₁`. -/
theorem xi_theta_th {l : Ordinal.{0}} (hl0 : l ≠ 0) (hpv : Nm.Pv S (Cd.cdEta S l) = upsilon l)
    (hs1 : upsilon (succ l) < Om1) : upsilon (succ l) ≤ Cd.cdTheta S l (ConjT.th S) := by
  have hρS : SC (upsilon l) := by rw [← hpv]; exact Nm.Pv_SC S _
  have hρ1 : upsilon l < Om1 := (upsilon_normal.strictMono (lt_succ l)).trans hs1
  have hnot : ∀ z < upsilon l, z ∈ ⋃ e, S.CSet e 0 := fun z hz =>
    Zb.zb_Pv_N (Cd.cdEta S l) (by rw [hpv]; exact hz)
  have hθ1 : (Om1 : Ordinal.{0}) < ConjT.th S := by rw [Rj.rj_Om1]; exact Zr.zrTh_gt_Om1
  refine le_of_forall_lt fun v hv => ?_
  have hv1 : v < Om1 := hv.trans hs1
  have hvT : v ∈ Tset (upsilon l) := by
    have h := (upsilon_succ_T l hs1 v hv1).2 hv
    rwa [if_neg hl0] at h
  obtain ⟨d, hd, rfl⟩ := xiR_onto S (Low.opow_eq_self_of_SC hρS) hρ1 v hvT hv1
  have hdθ : d < ConjT.th S := by
    rcases hd with h | ⟨-, h, -⟩
    · exact (h.trans hρ1).trans hθ1
    · exact h
  rw [← xi_cdTheta hpv hρS hρ1 hnot hd hdθ]
  exact Cd.cdOtp_lt_of_mem (xi_hull_of_dom le_self_add hρS hρ1 hnot hdθ hd) hdθ

/-! ## The code continuity -/

/-- **THE CODE CONTINUITY** (`Zn.ZnThCont S λ`) at every restart `λ < ι(η₀)` with
`ρ_λ < Θ_λ(m_λ) ≤ υ_{λ+1}`. -/
theorem xi_code_cont {l η0 : Ordinal.{0}} (hl : IsRestartIdx l) (hlt : l < Bt.iota S η0)
    (hbig : upsilon l < Cd.cdTheta S l (Cd.cdCode S l))
    (hθ : Cd.cdTheta S l (Cd.cdCode S l) ≤ upsilon (succ l)) : Zn.ZnThCont S l := by
  have hPv : ∀ η, Nm.Pv S η = upsilon (Bt.iota S η) := fun η => (Bt.ups_iota S η).symm
  have hl0 : l ≠ 0 := hl.1
  have hlim : IsSuccLimit l := ri_limit hl
  have hX : upsilon l < Nm.Pv S η0 := by rw [hPv]; exact upsilon_normal.strictMono hlt
  have hpv : Nm.Pv S (Cd.cdEta S l) = upsilon l := Cd.cdEta_pv hl0 hX
  obtain ⟨-, hηι, -⟩ := Cd.cdEta_spec (S := S) (one_le_iff_ne_zero.2 hl0) hlt
  have hs1' : upsilon (succ l) < Om 1 := by
    refine lt_of_le_of_lt (upsilon_normal.strictMono.monotone (succ_le_of_lt hlt)) ?_
    rw [← hPv]; exact Nm.Pv_lt_Om1 S η0
  have hs1 : upsilon (succ l) < Om1 := by rw [Rj.rj_Om1]; exact hs1'
  have hρS : SC (upsilon l) := by rw [← hpv]; exact Nm.Pv_SC S _
  have hρE : InE (upsilon l) := Low.opow_eq_self_of_SC hρS
  have hρ1 : upsilon l < Om1 := (upsilon_normal.strictMono (lt_succ l)).trans hs1
  have hnot : ∀ z < upsilon l, z ∈ ⋃ e, S.CSet e 0 := fun z hz =>
    Zb.zb_Pv_N (Cd.cdEta S l) (by rw [hpv]; exact hz)
  have hcnt : ∀ y ∈ Cd.cdHull S l, y < Om 1 → y < upsilon l := fun y hy hy1 => by
    rw [← hpv]
    unfold Cd.cdHull at hy
    rw [← hpv] at hy
    exact lt_psi_of_mem Low.InR_Om_one hy hy1
  have hθth := xi_theta_th hl0 hpv hs1
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  -- the code is infinite
  have hm : upsilon l < Cd.cdCode S l := by
    by_contra h
    push Not at h
    rw [Cd.cdTheta_small S h] at hbig
    exact lt_irrefl _ (hbig.trans_le h)
  have hωρ : (ω : Ordinal.{0}) ≤ upsilon l :=
    (Ordinal.le_mul_right ω omega0_pos).trans (Pp.ppSC_ww hρS).le
  have he : Cd.cdCode S l ≤ Cd.cdExp (Cd.cdEta S l) := Cd.cdCodeOf_le_exp S _
  refine Zn.znThCont_of_code hθ fun c hcH hcm ν hν => ?_
  -- `c < θ`
  have hcθ : c < ConjT.th S := by
    by_contra h
    push Not at h
    have h2 : Cd.cdTheta S l c < Cd.cdTheta S l (Cd.cdCode S l) := Cd.cdOtp_lt_of_mem hcH hcm
    exact lt_irrefl _ (((hθth.trans (Cd.cdTheta_mono S l h)).trans_lt h2).trans_le hθ)
  have hcD : WDom S (upsilon l) c := (xi_hull_iff le_self_add hρS hρ1 hcnt hnot hcθ).1 hcH
  -- a bound for the visibility of `c`
  obtain ⟨b, hb, hbD⟩ : ∃ b < upsilon l, ∀ σ, b < σ → WDom S σ c := by
    rcases hcD with h | ⟨h1, h2, h3⟩
    · exact ⟨c, h, fun σ hσ => Or.inl hσ⟩
    · refine ⟨(wP c).sup id, ?_, fun σ hσ => Or.inr ⟨h1, h2, fun p hp =>
        lt_of_le_of_lt (Finset.le_sup (f := id) hp) hσ⟩⟩
      exact (Finset.sup_lt_iff (show (⊥ : Ordinal.{0}) < upsilon l from hρS.1)).2 h3
  obtain ⟨ν₀, hν₀l, hbν₀⟩ := (upsilon_normal.lt_iff_exists_lt hlim).1 hb
  -- the exponent `e'`
  obtain ⟨e', he'2, he'e, he'Ω, hoff, he'mem⟩ : ∃ e' : Ordinal.{0}, 2 ≤ e' ∧ e' < Cd.cdExp (Cd.cdEta S l) ∧
      e' < Om (1 + 1) ∧ c ≤ Cd.cdOff e' ∧ ∀ a σ, Om ω ≤ a → SC σ → σ < Om1 → b < σ →
        (∀ z < σ, z ∈ ⋃ e, S.CSet e 0) → e' ∈ S.CSet a σ := by
    have hω2 : (ω : Ordinal.{0}) < Om (1 + 1) :=
      ((hωρ.trans_lt hρ1).trans_le (by rw [Rj.rj_Om1])).trans (Zr.zrTh_gt_Om1.trans hθ2)
    rcases lt_or_ge c ω with hcω | hcω
    · obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 hcω
      have hfin : ((n + 2 : ℕ) : Ordinal.{0}) < ω := Ordinal.natCast_lt_omega0 _
      refine ⟨((n + 2 : ℕ) : Ordinal.{0}), ?_, hfin.trans_le (hωρ.trans (hm.le.trans he)), hfin.trans hω2, ?_,
        fun a σ _ _ _ _ _ => Pp.ppNat_mem a σ _⟩
      · exact_mod_cast (show 2 ≤ n + 2 by omega)
      · unfold Cd.cdOff
        rw [if_pos hfin]
        refine Ordinal.le_sub_of_add_le ?_
        exact_mod_cast (show 1 + n ≤ n + 2 by omega)
    · refine ⟨c, ?_, hcm.trans_le he, hcθ.trans hθ2, ?_,
        fun a σ ha hσ hσ1 hbσ hσN => xi_hull_of_dom ha hσ hσ1 hσN hcθ (hbD σ hbσ)⟩
      · exact (Ordinal.natCast_lt_omega0 2).le.trans hcω
      · unfold Cd.cdOff
        rw [if_neg (not_lt.2 hcω)]
  -- a good name `g` above `max ν ν₀`
  obtain ⟨ν', hνν', hν₀ν', hν'l⟩ : ∃ ν', ν ≤ ν' ∧ ν₀ ≤ ν' ∧ ν' < l :=
    ⟨max ν ν₀, le_max_left _ _, le_max_right _ _, max_lt hν hν₀l⟩
  obtain ⟨g, hgg, hgι, hgη⟩ : ∃ g, Bt.Good S g ∧ Bt.iota S g = ν' + 1 ∧ g < Cd.cdEta S l :=
    ⟨_, Cd.cdEta_spec (S := S) le_add_self (by rw [hηι]; exact hlim.add_one_lt hν'l)⟩
  have hbg : b < Nm.Pv S g := by
    rw [hPv, hgι]
    exact hbν₀.trans_le (upsilon_normal.strictMono.monotone (hν₀ν'.trans (lt_add_one ν').le))
  -- the name `ζ = g + ω^{e'}`
  have hζmem : ω ^ e' ∈ S.CSet (ConjT.Aη S (g + ω ^ e') + 1) (Nm.Pv S (g + ω ^ e')) := by
    have hσ1 : Nm.Pv S (g + ω ^ e') < Om1 := by rw [Rj.rj_Om1]; exact Nm.Pv_lt_Om1 S _
    have hA : Om ω ≤ ConjT.Aη S (g + ω ^ e') + 1 :=
      (show Om ω ≤ ConjT.Aη S (g + ω ^ e') from le_self_add).trans le_self_add
    have h := he'mem _ _ hA (Nm.Pv_SC S _) hσ1 (hbg.trans_le (Nm.Pv_mono le_self_add))
      (fun z hz => Zb.zb_Pv_N _ hz)
    have := CSet.phi_mem (CSet.zero_mem (S := S) _ _) h
    rwa [veblen_zero_apply] at this
  have hζg : Bt.Good S (g + ω ^ e') := Nm.good_add hgg hζmem
  have hζdvd : ω * ω ∣ g + ω ^ e' := by
    rw [xi_ww_eq]; exact (opow_dvd_opow ω he'2).trans ⟨_, xi_opow_decomp g e'⟩
  have hζ0 : g + ω ^ e' ≠ 0 :=
    (lt_of_lt_of_le (opow_pos e' omega0_pos) le_add_self).ne'
  have hζη : g + ω ^ e' < Cd.cdEta S l := by
    have hηne : Cd.cdEta S l ≠ 0 := (lt_of_le_of_lt zero_le hgη).ne'
    have hd : ω ^ (e' + 1) ∣ Cd.cdEta S l :=
      (opow_dvd_opow ω (add_one_le_of_lt he'e)).trans (Cd.cdExp_dvd hηne)
    exact lt_of_lt_of_le ((add_lt_add_iff_left g).2
      ((opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one e'))) (xi_add_opow_le hd hgη)
  -- the restart `μ = ι(ζ)`
  have hμri : IsRestartIdx (Bt.iota S (g + ω ^ e')) := xi_ri_of_dvd hζ0 hζdvd
  have hμl : Bt.iota S (g + ω ^ e') < l := by rw [← hηι]; exact Cd.cd_iota_lt_of_good hζg hζη
  have hνμ : ν < Bt.iota S (g + ω ^ e') :=
    calc ν ≤ ν' := hνν'
      _ < ν' + 1 := lt_add_one ν'
      _ = Bt.iota S g := hgι.symm
      _ ≤ _ := Bt.iota_mono _ _ le_self_add
  have hημ : Cd.cdEta S (Bt.iota S (g + ω ^ e')) = g + ω ^ e' := Cd.cdEta_unique hζg rfl
  have hpvμ : Nm.Pv S (Cd.cdEta S (Bt.iota S (g + ω ^ e'))) = upsilon (Bt.iota S (g + ω ^ e')) := by
    rw [hημ, hPv]
  have hcode : c ≤ Cd.cdCode S (Bt.iota S (g + ω ^ e')) := by
    unfold Cd.cdCode
    rw [hημ, Cd.cdCodeOf_of_lt (by rw [xi_exp_add]; exact he'Ω), xi_exp_add]
    exact hoff
  have hμS : SC (upsilon (Bt.iota S (g + ω ^ e'))) := by rw [← hPv]; exact Nm.Pv_SC S _
  have hμ1 : upsilon (Bt.iota S (g + ω ^ e')) < Om1 := (upsilon_normal.strictMono hμl).trans hρ1
  have hμN : ∀ z < upsilon (Bt.iota S (g + ω ^ e')), z ∈ ⋃ e, S.CSet e 0 := fun z hz =>
    Zb.zb_Pv_N (g + ω ^ e') (by rw [hPv]; exact hz)
  have hbμ : b < upsilon (Bt.iota S (g + ω ^ e')) := by
    rw [← hPv]; exact hbg.trans_le (Nm.Pv_mono le_self_add)
  have hcDμ := hbD _ hbμ
  refine ⟨_, hμri, hνμ, hμl, ?_⟩
  rw [xi_cdTheta hpv hρS hρ1 hnot hcD hcθ,
    (xiR_pi (Low.opow_eq_self_of_SC hμS) hρE (upsilon_normal.strictMono hμl) hρ1 c hcDμ).2,
    ← xi_cdTheta hpvμ hμS hμ1 hμN hcDμ hcθ]
  exact Cd.cdTheta_mono S _ hcode

end Googology.Trans.PoR.InaccPsi.R2.Xi
