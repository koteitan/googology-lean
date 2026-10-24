import Googology.Trans.PoR.InaccPsi.R2.SyRoad
import Googology.Trans.PoR.InaccPsi.R2.LgCl
import Googology.Trans.PoR.InaccPsi.R2.MxGam

/-!
# The data of a code past `Γ_{Ω₁+1}`: Veblen normal forms over `{Ω₁, Γ_{Ω₁+1}}`, every code below `Γ'`

`Ω₁ = Om1`, `Γ_{Ω₁+1} = Gg.ggGam = ψ_{Ω₂}(0)`, `Γ' = lgGam'` (the least strongly critical ordinal above
`Γ_{Ω₁+1}`), `LgCl Z` the codes over `Z` with the atom `Γ_{Ω₁+1}` (`R2.LgCl`: generated from `[0, Z)`, `Ω₁` and
`Γ_{Ω₁+1}` by `+` and `φ`), `B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`.  `Ss.ssDat` reads the Veblen normal
form over `{0, Ω₁}` and stops at `Γ_{Ω₁+1}` (junk `0` from there on).  Here the same recursion has the atom
`Γ_{Ω₁+1}` (data `0`): in `(Ω₁, Γ')` the only strongly critical ordinal is `Γ_{Ω₁+1}`, every other `ε`-number `z` is
`φ(a, b)` with `a, b < z` (`tc_inv1_lt`), so the recursion reads every code below `Γ'`, and in particular the whole
first sub-range `[Γ_{Ω₁+1}, ε_{Γ_{Ω₁+1}+1})`, where `Γ_{Ω₁+1}` is the only new atom.

* `tcDat` (**the data of a code**: `z` below `Ω₁`, `0` at `Ω₁` and `Γ_{Ω₁+1}` and from `Γ'` on, the larger data of
  `invVeblen₁ z`, `invVeblen₂ z` at the other `ε`-numbers of `(Ω₁, Γ')`, of `log_ω z`, `z mod ω^{log_ω z}` at the
  non-`ε` ones), `tcDat_eq_ss` (**`tcDat = Ss.ssDat` below `Γ_{Ω₁+1}`**), `tcDat_lt_Om1`;
* `tc_code` (**`z < Γ'` with `tcDat z < a` is a code over `a`**), `tc_cl_inv`, `tc_cl_dat`, `tc_cl_iff` (**for a
  strongly critical `q` and `z < Γ'`: `LgCl q z ↔ tcDat z < q`**; it extends `Ss.ss_cl_iff` from `Γ_{Ω₁+1}` to `Γ'`);
* `tc_cl_div` (`LgCl` is closed under `y ↦ y / Ω₁`), `tc_cl_opow_mul`, `tc_cl_Om1_mul`, `tc_cl_Om1_add`;
* `tc_gam_D` (`Γ_{Ω₁+1}` is in the domain of `B_n`), `tcB_cl` (**a code over `x < L(ω)` is in the domain of `B_n`
  and its image is a code over `B_n x`**), `tcB_lt` (**`B_n` keeps the codes below `Γ'`**), `tcB_dat` (**`tcDat (B_n
  z) = B_n (tcDat z)`** for every code `z < Γ'` over `c_{n+1}`; it extends `Ss.ssB_dat`).

No new axiom.  New definition: `tcDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-! ## The recursion -/

theorem tc_G'_spec : SC (lgGam' : Ordinal.{0}) ∧ ggGam < lgGam' :=
  csInf_mem (s := {b | SC b ∧ ggGam < b})
    ⟨_, Lq.lq_gamma_SC (ggGam + 1), (lt_add_one _).trans_le (Lq.lq_le_gamma _)⟩

theorem tc_Gam_lt_G' : (ggGam : Ordinal.{0}) < lgGam' := tc_G'_spec.2

theorem tc_SC_G' : SC (lgGam' : Ordinal.{0}) := tc_G'_spec.1

theorem tc_Om1_lt_G' : (Om1 : Ordinal.{0}) < lgGam' := ss_Om1_lt_Gam.trans tc_Gam_lt_G'

/-- **An `ε`-number in `(Ω₁, Γ')` other than `Γ_{Ω₁+1}` is not strongly critical**: `invVeblen₁ z < z`. -/
theorem tc_inv1_lt {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < lgGam') (hG : z ≠ ggGam) : invVeblen₁ z < z := by
  refine lt_of_le_of_ne (invVeblen₁_le z) fun e => ?_
  have hfix : ∀ o < z, veblen o z = z := fun o ho => veblen_eq_of_lt_invVeblen₁ (by rw [e]; exact ho)
  have hSC : SC z := ⟨rj_Om1_pos.trans h1, fun a ha b hb => by
    calc veblen a b < veblen a z := veblen_lt_veblen_iff_right.2 hb
      _ = z := hfix a ha⟩
  rcases (ggGam_le hSC (by rw [← rj_Om1]; exact h1)).lt_or_eq with hlt | heq
  · exact absurd (lgGam'_le hSC hlt) (not_le.2 h2)
  · exact hG heq.symm

/-- **The countable data of a code `z < Γ'`** on its Veblen normal form over `{0, Ω₁, Γ_{Ω₁+1}}`. Junk value `0`
from `Γ'` on. -/
noncomputable def tcDat (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < lgGam' ∧ z ≠ ggGam then
    if hE : ω ^ z = z then
      have : invVeblen₁ z < z := tc_inv1_lt hz.1 hz.2.1 hz.2.2
      have : invVeblen₂ z < z := ss_inv2_lt hE
      max (tcDat (invVeblen₁ z)) (tcDat (invVeblen₂ z))
    else
      have : log ω z < z := ss_log_lt (rj_Om1_pos.trans hz.1).ne' hE
      have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans hz.1).ne'
      max (tcDat (log ω z)) (tcDat (z % ω ^ log ω z))
  else if z < Om1 then z else 0
termination_by z

theorem tcDat_small {z : Ordinal.{0}} (h : z < Om1) : tcDat z = z := by
  rw [tcDat, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem tcDat_Om1 : tcDat Om1 = 0 := by
  rw [tcDat, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem tcDat_gam : tcDat ggGam = 0 := by
  rw [tcDat, dif_neg (fun hz => hz.2.2 rfl), if_neg (not_lt.2 ss_Om1_lt_Gam.le)]

theorem tcDat_big {z : Ordinal.{0}} (h : lgGam' ≤ z) : tcDat z = 0 := by
  rw [tcDat, dif_neg (fun hz => absurd hz.2.1 (not_lt.2 h)),
    if_neg (fun h' => absurd (h'.trans tc_Om1_lt_G') (not_lt.2 h))]

/-- The `ε` clause. -/
theorem tcDat_eq_phi {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < lgGam') (hG : z ≠ ggGam) (hE : ω ^ z = z) :
    tcDat z = max (tcDat (invVeblen₁ z)) (tcDat (invVeblen₂ z)) := by
  rw [tcDat, dif_pos ⟨h1, h2, hG⟩, dif_pos hE]

/-- The Cantor clause. -/
theorem tcDat_eq_cnf {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < lgGam') (hE : ω ^ z ≠ z) :
    tcDat z = max (tcDat (log ω z)) (tcDat (z % ω ^ log ω z)) := by
  have hG : z ≠ ggGam := fun e => hE (by rw [e]; exact lg_Gam_eps)
  rw [tcDat, dif_pos ⟨h1, h2, hG⟩, dif_neg hE]

/-- **The data is countable.** -/
theorem tcDat_lt_Om1 : ∀ z : Ordinal.{0}, tcDat z < Om1 := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  by_cases hz : Om1 < z ∧ z < lgGam' ∧ z ≠ ggGam
  · by_cases hE : ω ^ z = z
    · rw [tcDat_eq_phi hz.1 hz.2.1 hz.2.2 hE]
      exact max_lt (IH _ (tc_inv1_lt hz.1 hz.2.1 hz.2.2)) (IH _ (ss_inv2_lt hE))
    · rw [tcDat_eq_cnf hz.1 hz.2.1 hE]
      exact max_lt (IH _ (ss_log_lt (rj_Om1_pos.trans hz.1).ne' hE)) (IH _ (rj_mod_lt (rj_Om1_pos.trans hz.1).ne'))
  · rw [tcDat, dif_neg hz]
    split_ifs with h
    · exact h
    · exact rj_Om1_pos

/-- **`tcDat = ssDat` below `Γ_{Ω₁+1}`.** -/
theorem tcDat_eq_ss : ∀ z : Ordinal.{0}, z < ggGam → tcDat z = ssDat z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tcDat_small h, ssDat_small h]
  · rw [tcDat_Om1, ssDat_Om1]
  have hG' : z < lgGam' := hzG.trans tc_Gam_lt_G'
  by_cases hE : ω ^ z = z
  · have h1 := ss_inv1_lt h hzG
    have h2 := ss_inv2_lt hE
    rw [tcDat_eq_phi h hG' hzG.ne hE, ssDat_eq_phi h hzG hE, IH _ h1 (h1.trans hzG), IH _ h2 (h2.trans hzG)]
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := ss_log_lt hz0 hE
    have hm := rj_mod_lt hz0
    rw [tcDat_eq_cnf h hG' hE, ssDat_eq_cnf h hzG hE, IH _ hl (hl.trans hzG), IH _ hm (hm.trans hzG)]

theorem tcDat_le_ss {z : Ordinal.{0}} (h : z ≤ ggGam) : tcDat z = ssDat z := by
  rcases h.lt_or_eq with h | rfl
  · exact tcDat_eq_ss z h
  · rw [tcDat_gam, ssDat_big le_rfl]

/-! ## Codes and data -/

/-- **A code**: `z < Γ'` with `tcDat z < a` (`0 < a`) is a code over `a`. -/
theorem tc_code {a : Ordinal.{0}} (ha : 0 < a) : ∀ z : Ordinal.{0}, z < lgGam' → tcDat z < a → LgCl a z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG hd
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tcDat_small h] at hd; exact LgCl.small hd
  · rw [rj_Om1]; exact LgCl.om
  by_cases hG : z = ggGam
  · rw [hG]; exact LgCl.gam
  by_cases hE : ω ^ z = z
  · rw [tcDat_eq_phi h hzG hG hE] at hd
    have h1 := tc_inv1_lt h hzG hG
    have h2 := ss_inv2_lt hE
    have e : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
    rw [← e]
    exact LgCl.phi (IH _ h1 (h1.trans hzG) ((le_max_left _ _).trans_lt hd))
      (IH _ h2 (h2.trans hzG) ((le_max_right _ _).trans_lt hd))
  · rw [tcDat_eq_cnf h hzG hE] at hd
    have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    have hl := ss_log_lt hz0 hE
    have hm := rj_mod_lt hz0
    have he := IH _ hl (hl.trans hzG) ((le_max_left _ _).trans_lt hd)
    have hr := IH _ hm (hm.trans hzG) ((le_max_right _ _).trans_lt hd)
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z := Ordinal.div_add_mod z _
    rw [← hdec, hk]
    exact LgCl.add (LgCl.mul_nat ha (LgCl.opow ha he) k) hr

/-- **The codes over a countable `Z` are closed under the inverse Veblen function** at the `ε`-numbers `z > Ω₁`,
`z ≠ Γ_{Ω₁+1}`. -/
theorem tc_cl_inv {Z : Ordinal.{0}} (hZ : Z ≤ Om1) : ∀ z, LgCl Z z → Om1 < z → ω ^ z = z → z ≠ ggGam →
    LgCl Z (invVeblen₁ z) ∧ LgCl Z (invVeblen₂ z) := by
  intro z hz
  induction hz with
  | small h => exact fun h1 _ _ => absurd (h.trans_le hZ) (not_lt.2 h1.le)
  | om => exact fun h1 _ _ => absurd h1 (by rw [rj_Om1]; exact lt_irrefl _)
  | gam => exact fun _ _ hG => absurd rfl hG
  | @add x y _ _ ihx ihy =>
    intro h1 hE hG
    have hI : Indec (x + y) := inE_indec hE
    rcases eq_or_lt_of_le (le_self_add : x ≤ x + y) with ex | hx
    · rw [← ex] at h1 hE hG ⊢; exact ihx h1 hE hG
    rcases eq_or_lt_of_le (le_add_self : y ≤ x + y) with ey | hy
    · rw [← ey] at h1 hE hG ⊢; exact ihy h1 hE hG
    exact absurd (hI.add_lt hx hy) (lt_irrefl _)
  | @phi x y hx hy _ ihy =>
    intro h1 hE hG
    rcases eq_or_lt_of_le (right_le_veblen x y) with ey | hlt
    · rw [← ey] at h1 hE hG ⊢; exact ihy h1 hE hG
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [veblen_zero_apply] at hE hlt
      exact absurd ((opow_right_inj one_lt_omega0).1 hE).symm hlt.ne
    rw [invVeblen₁_veblen hlt, invVeblen₂_veblen hx0 hlt]
    exact ⟨hx, hy⟩

/-- **The data of a code over a strongly critical `q` is below `q`.** -/
theorem tc_cl_dat {q : Ordinal.{0}} (hq : SC q) : ∀ z, LgCl q z → tcDat z < q := by
  rcases lt_or_ge Om1 q with hq1 | hq1
  · exact fun z _ => (tcDat_lt_Om1 z).trans hq1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [tcDat_small h]; exact hz.lt_of_lt_Om1 hq (by rw [← rj_Om1]; exact h)
  · rw [tcDat_Om1]; exact hq.1
  rcases le_or_gt lgGam' z with hG | hzG
  · rw [tcDat_big hG]; exact hq.1
  by_cases hGz : z = ggGam
  · rw [hGz, tcDat_gam]; exact hq.1
  by_cases hE : ω ^ z = z
  · obtain ⟨h1, h2⟩ := tc_cl_inv hq1 z hz h hE hGz
    rw [tcDat_eq_phi h hzG hGz hE]
    exact max_lt (IH _ (tc_inv1_lt h hzG hGz) h1) (IH _ (ss_inv2_lt hE) h2)
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := lgDec hq z hz
    set g := log ω z with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hwk : LgCl q (ω ^ g * k) := LgCl.mul_nat hq.1 (LgCl.opow hq.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : LgCl q (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    rw [tcDat_eq_cnf h hzG hE]
    exact max_lt (IH _ (ss_log_lt hz0 hE) hlog) (IH _ (rj_mod_lt hz0) hr)

/-- **For a strongly critical `q` and `z < Γ'`: `LgCl q z ↔ tcDat z < q`.** -/
theorem tc_cl_iff {q z : Ordinal.{0}} (hq : SC q) (hz : z < lgGam') : LgCl q z ↔ tcDat z < q :=
  ⟨tc_cl_dat hq z, tc_code hq.1 z hz⟩

/-! ## Arithmetic of codes -/

/-- `LgCl y` is closed under `g ↦ ω^e·g` for a code `e`. -/
theorem tc_cl_opow_mul {y e : Ordinal.{0}} (hy : SC y) (he : LgCl y e) :
    ∀ g, LgCl y g → LgCl y (ω ^ e * g) := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero]; exact LgCl.zero hy.1
  obtain ⟨hsub, hlog⟩ := lgDec hy g hg
  have hwg := opow_log_le_self ω hg0
  have hgr := Ordinal.add_sub_cancel_of_le hwg
  rw [← hgr, mul_add, ← opow_add]
  exact LgCl.add (LgCl.opow hy.1 (LgCl.add he hlog))
    (IH _ (Ph.ph_sub_log_lt hg0) (hsub _ (LgCl.opow hy.1 hlog) hwg))

/-- `LgCl Z μ ⇒ LgCl Z (Ω₁·μ)`. -/
theorem tc_cl_Om1_mul {Z μ : Ordinal.{0}} (hZ : SC Z) (hμ : LgCl Z μ) : LgCl Z (Om 1 * μ) := by
  have := tc_cl_opow_mul hZ LgCl.om μ hμ
  rwa [Bt.Om1_opow] at this

/-- `LgCl Z (Ω₁ + μ) ↔ LgCl Z μ`. -/
theorem tc_cl_Om1_add {Z μ : Ordinal.{0}} (hZ : SC Z) : LgCl Z (Om 1 + μ) ↔ LgCl Z μ := by
  refine ⟨fun h => ?_, fun h => LgCl.add LgCl.om h⟩
  have := (lgDec hZ _ h).1 _ LgCl.om le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The codes over a strongly critical `Z` are closed under `y ↦ y / Ω₁`.** -/
theorem tc_cl_div {Z : Ordinal.{0}} (hZ : SC Z) : ∀ y, LgCl Z y → LgCl Z (y / Om 1) := by
  have hO0 : (Om 1 : Ordinal.{0}) ≠ 0 := by rw [← rj_Om1]; exact rj_Om1_pos.ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact LgCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := lgDec hZ y hy
  set g := log ω y with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  have hdec : ω ^ g * (y / ω ^ g) + y % ω ^ g = y := Ordinal.div_add_mod y _
  rw [hk] at hdec
  rcases lt_or_ge g (Om 1) with hgO | hgO
  · have hy1 : y < Om 1 := by
      have h1 : y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
      refine h1.trans_le ?_
      rw [← Bt.Om1_opow]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgO)
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact LgCl.zero hZ.1
  · set g' := g - Om 1 with hg'
    have hge : Om 1 + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : LgCl Z g' := (lgDec hZ g hlog).1 _ LgCl.om hgO
    have hwk : LgCl Z (ω ^ g * k) := LgCl.mul_nat hZ.1 (LgCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : LgCl Z (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := rj_mod_lt hy0
    have e : y = Om 1 * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, Bt.Om1_opow, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hO0]
    exact LgCl.add (LgCl.mul_nat hZ.1 (LgCl.opow hZ.1 hg'C) k) (IH _ hry hr)

/-! ## The base change -/

/-- **`Γ_{Ω₁+1}` is in the domain of `B_n`.** -/
theorem tc_gam_D : MvD S ggGam := by
  refine ⟨Mx.mxGam_mem, ?_⟩
  rw [← Mx.mxGamT_val S, Bc.bcNf_val S Mx.mxGamT_NF]
  exact Bc.bcD_free Mx.mxGamT_NF Mx.mxGamT_free

/-- **A code over `x < L(ω)` is in the domain of `B_n`, and its image is a code over `B_n x`.** -/
theorem tcB_cl {n : ℕ} {x : Ordinal.{0}} (hxL : x < Nc.ncL S ω) :
    ∀ μ, LgCl x μ → MvD S μ ∧ LgCl (Bc.bcB S n x) (Bc.bcB S n μ) := by
  intro μ hμ
  induction hμ with
  | @small a ha =>
    exact ⟨mvD_of_lt (ha.trans hxL), LgCl.small ((Bc.bcB_lt_iff (ha.trans hxL) hxL).2 ha)⟩
  | om =>
    obtain ⟨hD, hB⟩ := mvB_Om1 (S := S) (k := n)
    exact ⟨hD, by rw [hB]; exact LgCl.om⟩
  | gam => exact ⟨tc_gam_D, by rw [Mx.mxB_gam]; exact LgCl.gam⟩
  | @add a b _ _ iha ihb =>
    obtain ⟨hD, hB⟩ := mvB_add (k := n) iha.1 ihb.1
    exact ⟨hD, by rw [hB]; exact LgCl.add iha.2 ihb.2⟩
  | @phi a b _ _ iha ihb =>
    by_cases h : a < veblen a b ∧ b < veblen a b
    · obtain ⟨hD, hB⟩ := Mw.mwB_phi (k := n) iha.1 ihb.1 h.1 h.2
      exact ⟨hD, by rw [hB]; exact LgCl.phi iha.2 ihb.2⟩
    · rcases not_and_or.1 h with h' | h'
      · have e : veblen a b = a := le_antisymm (not_lt.1 h') (left_le_veblen a b)
        rw [e]; exact iha
      · have e : veblen a b = b := le_antisymm (not_lt.1 h') (right_le_veblen a b)
        rw [e]; exact ihb

/-- **`B_n` keeps the codes below `Γ'`**: for a code `z < Γ'` over `x < L(ω)` with `B_n x ≤ Ω₁`, `B_n z < Γ'`. -/
theorem tcB_lt {n : ℕ} {x : Ordinal.{0}} (hxL : x < Nc.ncL S ω) (hBx : Bc.bcB S n x ≤ Om 1) :
    ∀ μ, LgCl x μ → μ < lgGam' → Bc.bcB S n μ < lgGam' := by
  intro μ hμ
  induction hμ with
  | @small a ha =>
    intro _
    have h := (Bc.bcB_lt_iff (k := n) (ha.trans hxL) hxL).2 ha
    exact h.trans_le (hBx.trans (by rw [← rj_Om1]; exact tc_Om1_lt_G'.le))
  | om => intro _; rw [(mvB_Om1 (S := S) (k := n)).2, ← rj_Om1]; exact tc_Om1_lt_G'
  | gam => intro _; rw [Mx.mxB_gam]; exact tc_Gam_lt_G'
  | @add a b ha hb iha ihb =>
    intro h
    have hDa := (tcB_cl (n := n) hxL a ha).1
    have hDb := (tcB_cl (n := n) hxL b hb).1
    rw [(mvB_add (k := n) hDa hDb).2]
    exact (Lq.lq_SC_indec tc_SC_G').add_lt (iha (lt_of_le_of_lt le_self_add h))
      (ihb (lt_of_le_of_lt le_add_self h))
  | @phi a b ha hb iha ihb =>
    intro h
    by_cases h' : a < veblen a b ∧ b < veblen a b
    · have hDa := (tcB_cl (n := n) hxL a ha).1
      have hDb := (tcB_cl (n := n) hxL b hb).1
      rw [(Mw.mwB_phi (k := n) hDa hDb h'.1 h'.2).2]
      exact tc_SC_G'.2 _ (iha (h'.1.trans h)) _ (ihb (h'.2.trans h))
    · rcases not_and_or.1 h' with h'' | h''
      · have e : veblen a b = a := le_antisymm (not_lt.1 h'') (left_le_veblen a b)
        rw [e] at h ⊢; exact iha h
      · have e : veblen a b = b := le_antisymm (not_lt.1 h'') (right_le_veblen a b)
        rw [e] at h ⊢; exact ihb h

/-- `B_n(c_{n+1}) ≤ Ω₁`. -/
theorem tcB_c_le (n : ℕ) : Bc.bcB S n (Bc.bcC S (n + 1)) ≤ Om 1 := (ssB_c_lt n).le

/-- **`B_n` keeps the codes below `Γ'` over `c_{n+1}`.** -/
theorem tcB_lt_G' {n : ℕ} {z : Ordinal.{0}} (hz : LgCl (Bc.bcC S (n + 1)) z) (hzG : z < lgGam') :
    Bc.bcB S n z < lgGam' :=
  tcB_lt (Bc.bcC_lt S (n + 1)) (tcB_c_le n) z hz hzG

/-- **`tcDat (B_n z) = B_n (tcDat z)`** for every code `z < Γ'` over `c_{n+1}`. -/
theorem tcB_dat {n : ℕ} : ∀ z, LgCl (Bc.bcC S (n + 1)) z → z < lgGam' →
    tcDat (Bc.bcB S n z) = Bc.bcB S n (tcDat z) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hc1 : Bc.bcC S (n + 1) ≤ Om1 := by rw [rj_Om1]; exact (hLw.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz hzG
  have hDz := (tcB_cl (n := n) hLw z hz).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hBzG : Bc.bcB S n z < lgGam' := tcB_lt_G' hz hzG
  have hdL : ∀ w, LgCl (Bc.bcC S (n + 1)) w → tcDat w < Nc.ncL S ω := fun w hw =>
    (tc_cl_dat hc w hw).trans hLw
  rcases lt_trichotomy z Om1 with h | rfl | h
  · have hzc : z < Bc.bcC S (n + 1) := hz.lt_of_lt_Om1 hc (by rw [← rj_Om1]; exact h)
    rw [tcDat_small h, tcDat_small (by rw [rj_Om1]; exact Rh.rhB_lt_Om1 hzc)]
  · rw [rj_Om1, hBO, ← rj_Om1, tcDat_Om1, Bc.bcB_zero]
  by_cases hGz : z = ggGam
  · rw [hGz, Mx.mxB_gam, tcDat_gam, Bc.bcB_zero]
  have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
  have hOz : Om1 < Bc.bcB S n z := by
    have := (mvB_lt_iff (k := n) hDO hDz).2 (by rw [← rj_Om1]; exact h)
    rwa [hBO, ← rj_Om1] at this
  have hBG : Bc.bcB S n z ≠ ggGam := by
    intro e
    rw [← Mx.mxB_gam (S := S) n] at e
    exact hGz (by
      rcases lt_trichotomy z ggGam with hl | hl | hl
      · exact absurd e ((mvB_lt_iff (k := n) hDz tc_gam_D).2 hl).ne
      · exact hl
      · exact absurd e ((mvB_lt_iff (k := n) tc_gam_D hDz).2 hl).ne')
  by_cases hE : ω ^ z = z
  · set o := invVeblen₁ z with ho
    set b := invVeblen₂ z with hb
    have hoz : o < z := tc_inv1_lt h hzG hGz
    have hbz : b < z := ss_inv2_lt hE
    obtain ⟨hco, hcb⟩ := tc_cl_inv hc1 z hz h hE hGz
    have hev : veblen o b = z := by rw [ho, hb, veblen_invVeblen₁_invVeblen₂, hE]
    have ho0 : o ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ b = ω ^ z := by rw [hev, hE]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hbz.ne
    have hDo := (tcB_cl (n := n) hLw o hco).1
    have hDb := (tcB_cl (n := n) hLw b hcb).1
    obtain ⟨-, hBz⟩ := Mw.mwB_phi (k := n) hDo hDb (by rw [hev]; exact hoz) (by rw [hev]; exact hbz)
    rw [hev] at hBz
    have hD0 : MvD S 0 := mvD_of_lt (lt_of_le_of_lt zero_le hLw)
    have hBo0 : Bc.bcB S n o ≠ 0 := by
      intro e
      have h1 := (mvB_lt_iff (k := n) hD0 hDo).2 (pos_iff_ne_zero.2 ho0)
      rw [Bc.bcB_zero, e] at h1
      exact lt_irrefl _ h1
    have hBb : Bc.bcB S n b < veblen (Bc.bcB S n o) (Bc.bcB S n b) := by
      rw [← hBz]; exact (mvB_lt_iff hDb hDz).2 hbz
    have hBE : ω ^ Bc.bcB S n z = Bc.bcB S n z := by rw [hBz]; exact gg_veblen_eps hBo0
    rw [tcDat_eq_phi hOz hBzG hBG hBE, tcDat_eq_phi h hzG hGz hE, hBz, invVeblen₁_veblen hBb,
      invVeblen₂_veblen hBo0 hBb, IH o hoz hco (hoz.trans hzG), IH b hbz hcb (hbz.trans hzG)]
    rcases le_total (tcDat o) (tcDat b) with hle | hle
    · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL b hcb) hle)]
    · rw [max_eq_left hle, max_eq_left (Ri.riB_mono (hdL o hco) hle)]
  · obtain ⟨hsub, hlog⟩ := lgDec hc z hz
    set g := log ω z with hg
    have hgz : g < z := ss_log_lt hz0 hE
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hk0 : k ≠ 0 := by
      intro e
      have h1 := Ordinal.div_opow_log_pos ω hz0
      rw [hk, e, Nat.cast_zero] at h1
      exact lt_irrefl _ h1
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hrg : z % ω ^ g < ω ^ g := Ordinal.mod_lt z (opow_pos _ omega0_pos).ne'
    have hwk : LgCl (Bc.bcC S (n + 1)) (ω ^ g * k) := LgCl.mul_nat hc.1 (LgCl.opow hc.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : LgCl (Bc.bcC S (n + 1)) (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := rj_mod_lt hz0
    have hDg := (tcB_cl (n := n) hLw g hlog).1
    have hDr := (tcB_cl (n := n) hLw _ hr).1
    obtain ⟨hDw, hBw⟩ := Rk.rkB_opow_nat (n := n) hDg k
    obtain ⟨-, hBz⟩ := mvB_add (k := n) hDw hDr
    rw [hdec] at hBz
    obtain ⟨hDog, hBog⟩ := Ld.ldB_opow (n := n) hDg
    have hBr : Bc.bcB S n (z % ω ^ g) < ω ^ Bc.bcB S n g := by
      rw [← hBog]; exact (mvB_lt_iff hDr hDog).2 hrg
    have hlogB : log ω (Bc.bcB S n z) = Bc.bcB S n g := by
      rw [hBz, hBw, log_opow_mul_add one_lt_omega0 (by exact_mod_cast hk0) hBr,
        Ordinal.log_eq_zero (natCast_lt_omega0 k), add_zero]
    have hmodB : Bc.bcB S n z % ω ^ log ω (Bc.bcB S n z) = Bc.bcB S n (z % ω ^ g) := by
      rw [hlogB, hBz, hBw, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hBr]
    have hBE : ω ^ Bc.bcB S n z ≠ Bc.bcB S n z := by
      intro e
      have h1 : log ω (Bc.bcB S n z) = Bc.bcB S n z := by
        conv_lhs => rw [← e]
        exact log_opow one_lt_omega0 _
      rw [hlogB] at h1
      exact absurd h1 ((mvB_lt_iff hDg hDz).2 hgz).ne
    rw [tcDat_eq_cnf hOz hBzG hBE, hmodB, hlogB, IH g hgz hlog (hgz.trans hzG), IH _ hrz hr (hrz.trans hzG),
      tcDat_eq_cnf h hzG hE]
    rcases le_total (tcDat g) (tcDat (z % ω ^ g)) with hle' | hle'
    · rw [max_eq_right hle', max_eq_right (Ri.riB_mono (hdL _ hr) hle')]
    · rw [max_eq_left hle', max_eq_left (Ri.riB_mono (hdL g hlog) hle')]

end Googology.Trans.PoR.InaccPsi.R2.Tc
