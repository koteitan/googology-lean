import Googology.Trans.PoR.InaccPsi.R2.NnNameV

/-!
# The reading `Θ_F` below `Ω₁·F`, and the notation statement at the fixed points that are not `Γ`-points

`Θ_λ(m)` = the order type of the codes of `Cl(A_{η_λ}, ρ_λ)` below `m` (`Cd.cdTheta`), `m_λ` the code
(`Cd.cdCode`).  At a fixed point `F = υ_F` with a name:

* `nnHull_mem`: `Ω₁·q + r` is a code read at `F` for `q, r < F`; `nnHull_mod`: every code read at `F` has its
  remainder modulo `Ω₁` below `F` (the hull is `HCl(A_{η_F}, F)`, `Nm.linv0_HCl`);
* `nnOtp_block` (**`Θ_F(x) = F·(x / Ω₁) + min(x mod Ω₁, F)` for `x / Ω₁ < F`**), `nnTheta_lev`:
  `Θ_F(Ω₁·γ + d) = F·γ + d` for `γ, d < F`;
* `nnCode_ng`: `m_F = Ω₁·γ + logend(α)` at a fixed point `F = V_γ(α)` that is not a `Γ`-point (`Nn.nnName_ng`);
* `nnTH_ng` (**THE NOTATION STATEMENT AT THE FIXED POINTS THAT ARE NOT `Γ`-POINTS**): for every term system `X`
  with linear terms, `Θ_F(m_F) = O_X(F)` (both are `F·γ + logend(α)`, Theorem LEVEL); `nnTHfix_ng` (for `VzOrec`
  on the range below `cpB1`), `nnTHfam_ng` (for the layers `xtLL k` below `Λ⁺_k`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Fx Googology.Trans.PoR.InaccPsi.R2.Xt

variable {S : InaccSeq.{0}}

/-- `Ω₁·q + r` is a code read at `F` for `q, r < F` (`ρ_F = F`). -/
theorem nnHull_mem {F q r : Ordinal.{0}} (hfix : upsilon F = F) (hq : q < F) (hr : r < F) :
    Om 1 * q + r ∈ cdHull S F := by
  unfold cdHull
  rw [hfix]
  exact CSet.add_mem (mem_Om1_mul hq) (CSet.of_lt hr)

/-- Every code read at a named fixed point `F` has its remainder modulo `Ω₁` below `F`. -/
theorem nnHull_mod {F ηx y : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hy : y ∈ cdHull S F) : y % Om 1 < F := by
  have hpv0 : Pv S (cdEta S F) = upsilon F := cdEta_pv hF.1 hX
  unfold cdHull at hy
  rw [← hpv0] at hy
  have hpv : Pv S (cdEta S F) = F := hpv0.trans hfix
  have hkey : ∀ e, HCl S (ConjT.Aη S (cdEta S F)) (Pv S (cdEta S F)) e → e < ConjT.Aη S (cdEta S F) →
      S.psi e (Om 1) < Pv S (cdEta S F) := fun e he hea =>
    psi_lt_psi_of_mem Low.InR_Om_one hea he.mem_CSet
  have hH := CSet_sub_HCl hkey y hy
  obtain ⟨q, z, hz, hyq⟩ := linv0_HCl (Pv_SC S _) (Pv_lt_Om1 S _) hH
  have hzΩ : z < Om 1 := hz.trans (Pv_lt_Om1 S _)
  have e1 : Om 1 * (y / Om 1) + y % Om 1 = Om 1 * q + z := by rw [div_add_mod]; exact hyq
  obtain ⟨-, hzz⟩ := div_unique fx_Om1_ne (mod_lt y fx_Om1_ne) hzΩ e1
  rw [hzz, ← hpv]; exact hz

/-- **`Θ_F(x) = F·(x / Ω₁) + min(x mod Ω₁, F)` for `x ≤ Ω₁·F`.** -/
theorem nnOtp_block {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) : ∀ x, x ≤ Om 1 * F →
    cdOtp (cdHull S F) x = F * (x / Om 1) + min (x % Om 1) F := by
  obtain ⟨-, -, -, hlim, -⟩ := nn_fix_facts hF hfix
  have hF0 : F ≠ 0 := hF.1
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxF
  set a := x / Om 1 with ha
  set b := x % Om 1 with hb
  have hxab : x = Om 1 * a + b := (div_add_mod x _).symm
  have haF : a ≤ F := Ordinal.div_le_of_le_mul hxF
  -- the value at a code below `x`
  have hval : ∀ c ∈ cdHull S F, c < x →
      cdOtp (cdHull S F) c = F * (c / Om 1) + c % Om 1 ∧ c / Om 1 ≤ a := by
    intro c hc hcx
    have hca : c / Om 1 ≤ a := Ordinal.div_le_left hcx.le _
    have hmod := nnHull_mod hF hfix hX hc
    rw [IH c hcx (hcx.le.trans hxF), min_eq_left hmod.le]
    exact ⟨rfl, hca⟩
  refine le_antisymm ?_ ?_
  · rw [cdOtp_eq]
    refine ciSup_le' fun c => ?_
    split_ifs with hc
    · obtain ⟨hv, hca⟩ := hval c.1 hc c.2
      have hmod := nnHull_mod hF hfix hX hc
      rw [hv]
      rcases hca.lt_or_eq with hlt | heq
      · calc F * (c.1 / Om 1) + c.1 % Om 1 + 1 ≤ F * (c.1 / Om 1) + F := by
              rw [add_assoc]; exact add_le_add le_rfl (Order.add_one_le_of_lt hmod)
          _ = F * (c.1 / Om 1 + 1) := (mul_add_one _ _).symm
          _ ≤ F * a := mul_le_mul_right (Order.add_one_le_of_lt hlt) F
          _ ≤ _ := le_self_add
      · rw [heq, add_assoc]
        refine add_le_add le_rfl (le_min ?_ (Order.add_one_le_of_lt hmod))
        refine Order.add_one_le_of_lt ?_
        have hc' : c.1 = Om 1 * a + c.1 % Om 1 := by rw [← heq]; exact (div_add_mod _ _).symm
        have : Om 1 * a + c.1 % Om 1 < Om 1 * a + b := by rw [← hc', ← hxab]; exact c.2
        exact (add_lt_add_iff_left _).1 this
    · exact zero_le
  · refine le_of_forall_lt fun v hv => ?_
    by_cases hva : v < F * a
    · set q := v / F with hq
      set r := v % F with hr
      have hvqr : F * q + r = v := div_add_mod v F
      have hqa : q < a := (lt_mul_iff_div_lt hF0).1 hva
      have hrF : r < F := mod_lt v hF0
      have hmem := nnHull_mem (S := S) hfix (hqa.trans_le haF) hrF
      have hrO : r < Om 1 := hrF.trans (fx_fix_lt_Om1 hfix hX)
      have hcx : Om 1 * q + r < x := by
        rw [hxab]
        calc Om 1 * q + r < Om 1 * q + Om 1 := (add_lt_add_iff_left _).2 hrO
          _ = Om 1 * (q + 1) := (mul_add_one _ _).symm
          _ ≤ Om 1 * a := mul_le_mul_right (Order.add_one_le_of_lt hqa) _
          _ ≤ Om 1 * a + b := le_self_add
      have h1 := cdOtp_lt_of_mem hmem hcx
      rw [(hval _ hmem hcx).1, nn_div_eq fx_Om1_ne hrO, show (Om 1 * q + r) % Om 1 = r by
        rw [Ordinal.mul_add_mod_self, mod_eq_of_lt hrO], hvqr] at h1
      exact h1
    · push Not at hva
      set r := v - F * a with hr
      have hvr : F * a + r = v := Ordinal.add_sub_cancel_of_le hva
      have hrlt : r < min b F := (sub_lt_of_le hva).2 hv
      have hrF : r < F := hrlt.trans_le (min_le_right _ _)
      have hrb : r < b := hrlt.trans_le (min_le_left _ _)
      have haF' : a < F := by
        refine lt_of_le_of_ne haF fun e => ?_
        have : Om 1 * F < x := by
          rw [hxab, ← e]; exact lt_add_of_pos_right _ (lt_of_le_of_lt zero_le hrb)
        exact absurd hxF (not_le.2 this)
      have hmem := nnHull_mem (S := S) hfix haF' hrF
      have hrO : r < Om 1 := hrF.trans (fx_fix_lt_Om1 hfix hX)
      have hcx : Om 1 * a + r < x := by rw [hxab]; exact (add_lt_add_iff_left _).2 hrb
      have h1 := cdOtp_lt_of_mem hmem hcx
      rw [(hval _ hmem hcx).1, nn_div_eq fx_Om1_ne hrO, show (Om 1 * a + r) % Om 1 = r by
        rw [Ordinal.mul_add_mod_self, mod_eq_of_lt hrO], hvr] at h1
      exact h1

/-- **`Θ_F(Ω₁·γ + d) = F·γ + d`** for `γ, d < F` at a named fixed point `F`. -/
theorem nnTheta_lev {F ηx γ d : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hγ : γ < F) (hd : d < F) :
    cdTheta S F (Om 1 * γ + d) = F * γ + d := by
  have hdO : d < Om 1 := hd.trans (fx_fix_lt_Om1 hfix hX)
  have h1 : (Om 1 * γ + d) / Om 1 = γ := nn_div_eq fx_Om1_ne hdO
  have h2 : (Om 1 * γ + d) % Om 1 = d := by rw [Ordinal.mul_add_mod_self, mod_eq_of_lt hdO]
  have hle : Om 1 * γ + d ≤ Om 1 * F := by
    calc Om 1 * γ + d ≤ Om 1 * γ + Om 1 := add_le_add le_rfl hdO.le
      _ = Om 1 * (γ + 1) := (mul_add_one _ _).symm
      _ ≤ Om 1 * F := mul_le_mul_right (Order.add_one_le_of_lt hγ) _
  unfold cdTheta
  rw [nnOtp_block hF hfix hX _ hle, h1, h2, min_eq_left hd.le]

/-- **The code of a fixed point that is not a `Γ`-point**: `m_F = Ω₁·γ + logend(α)`. -/
theorem nnCode_ng {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hG : ¬ IsGP F)
    (hX : upsilon F < Pv S ηx) :
    cdCode S F = Om 1 * levG F + lg (invG (levG F) F) := by
  have hname := nnName_ng hF hfix hG hX
  have hF0 : 0 < F := pos_iff_ne_zero.2 hF.1
  obtain ⟨hγ0, hγF, -, hα0, hαF, -, -⟩ := nn_lev_data hfix (nn_ng_of_gp hF0 hG)
  have hFO : F < Om 1 := fx_fix_lt_Om1 hfix hX
  have hlt : cdExp (cdEta S F) < Om (1 + 1) := by
    rw [hname]
    have hE2 : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) :=
      Low.opow_eq_self_of_SC (SC_Om (by rw [one_add_one_eq_two]; exact two_ne_zero))
    have h12 : Om (1 : Ordinal.{0}) < Om (1 + 1) := Om_lt_Om.2 (lt_add_one 1)
    have hm : Om 1 * levG F < Om (1 + 1) := Om1_mul_lt_eps hE2 h12 ((hγF.trans hFO).trans h12)
    have hlgO : lg (invG (levG F) F) < Om (1 + 1) := (((lg_le hα0).trans_lt hαF).trans hFO).trans h12
    exact (SC_Om (by rw [one_add_one_eq_two]; exact two_ne_zero)).isPrincipal hm hlgO
  have hω : ω ≤ cdExp (cdEta S F) := by
    rw [hname]
    refine le_trans ?_ le_self_add
    calc ω ≤ Om (1 : Ordinal.{0}) := (omega0_lt_Om one_ne_zero).le
      _ ≤ Om 1 * levG F := le_mul_left _ (pos_iff_ne_zero.2 hγ0)
  unfold cdCode
  rw [cdCodeOf_of_lt hlt, cpOff_of_ge hω, hname]

/-- **THE NOTATION STATEMENT AT THE FIXED POINTS THAT ARE NOT `Γ`-POINTS**: `Θ_F(m_F) = O_X(F)` for every
term system with linear terms. -/
theorem nnTH_ng {X : XtSys} (hX0 : NnLin X) {F ηx : Ordinal.{0}} (hF : IsRestartIdx F)
    (hfix : upsilon F = F) (hG : ¬ IsGP F) (hX : upsilon F < Pv S ηx) :
    cdTheta S F (cdCode S F) = xtOrec X F := by
  have hF0 : 0 < F := pos_iff_ne_zero.2 hF.1
  obtain ⟨-, hγF, -, hα0, hαF, -, -⟩ := nn_lev_data hfix (nn_ng_of_gp hF0 hG)
  have hFO : F < Om1 := by rw [Om1_eq]; exact fx_fix_lt_Om1 hfix hX
  rw [nnCode_ng hF hfix hG hX, nnTheta_lev hF hfix hX hγF ((lg_le hα0).trans_lt hαF),
    nnLev hX0 F hF hFO hfix hG]

/-- **`Cp.CpTHfix` at the fixed points that are not `Γ`-points** (for `VzOrec`, the range below `cpB1`). -/
theorem nnTHfix_ng {l : Ordinal.{0}} (hr : CdRange S l) (hfix : upsilon l = l) (hG : ¬ IsGP l) :
    cdTheta S l (cdCode S l) = VzOrec l := by
  rw [← xtVz_orec]; exact nnTH_ng nnLin_vz hr.1 hfix hG (cp_name_L hr.2.2.1)

/-- **`famTHfix` of `xtFamW2` at the fixed points that are not `Γ`-points** (the layers `xtLL k`). -/
theorem nnTHfam_ng (k : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hfix : upsilon l = l) (hG : ¬ IsGP l) :
    cdTheta S l (cdCode S l) = xtFamW2.off k l :=
  nnTH_ng (nnLin_LL k) hr.1 hfix hG (cp_name_L hr.2.2.1)

end Googology.Trans.PoR.InaccPsi.R2.Nn
