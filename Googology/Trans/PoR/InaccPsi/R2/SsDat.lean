import Googology.Trans.PoR.InaccPsi.R2.SpRoad

/-!
# The countable data of a code on Veblen normal forms: every code below `Γ_{Ω₁+1}`

`Ω₁ = Om1`, `ε_{Ω₁+1} = Gg.ggE`, `Γ_{Ω₁+1} = Gg.ggGam` (the least strongly critical ordinal above `Ω₁`), `GgCl Z` the
codes over `Z` (`Gg.GgCl`: generated from `[0, Z)` and `Ω₁` by `+` and `φ`), `B_n = Bc.bcB S n`, `c_{n+1} =
Bc.bcC S (n + 1)`.  `Rj.rjDat` reads the leaves of the hereditary Cantor normal form over `{0, Ω₁}` and stops at
`ε_{Ω₁+1}`.  Here the recursion has one more clause, for the `ε`-numbers in `(Ω₁, Γ_{Ω₁+1})`: such a `z` is
`φ(a, b)` with `a = invVeblen₁ z < z` and `b = invVeblen₂ z < z` (Mathlib's inverse of the Veblen function), and its
data is the larger of the data of `a` and `b`.

* `ssDat` (**the data of a code**: `z` for `z < Ω₁`, `0` for `z = Ω₁` and from `Γ_{Ω₁+1}` on, `max(ssDat (log_ω z),
  ssDat (z mod ω^{log_ω z}))` for a non-`ε` `z ∈ (Ω₁, Γ_{Ω₁+1})`, `max(ssDat a, ssDat b)` for an `ε`-number `z =
  φ(a, b)` there), `ssDat_eq_phi`, `ssDat_eq_cnf`, `ssDat_lt_Om1`;
* `ssDat_eq_rj` (**`ssDat = Rj.rjDat` below `ε_{Ω₁+1}`**), `ss_Om1_add_E`, `ss_Om1_mul_E`, `ss_leOe_E`
  (`Ω₁ + E₁ = Ω₁·E₁ = u_{E₁} = E₁` for `E₁ = ε_{Ω₁+1}`);
* `ss_code` (**`z < Γ_{Ω₁+1}` with `ssDat z < a` is a code over `a`**), `ss_cl_inv` (**the codes over a countable
  `Z` are closed under `z ↦ invVeblen₁ z, invVeblen₂ z`**), `ss_cl_dat`, `ss_cl_iff` (**for a strongly critical `q`
  and `z < Γ_{Ω₁+1}`: `GgCl q z ↔ ssDat z < q`**; it extends `Rk.rk_cl_iff` from `ε_{Ω₁+1}` to `Γ_{Ω₁+1}`);
* `ss_cl_lt_Gam` (a code over `Z ≤ Γ_{Ω₁+1}` is below `Γ_{Ω₁+1}`), `ssB_lt_Gam`;
* `ssB_dat` (**`ssDat (B_n z) = B_n (ssDat z)`** for every code `z` over `c_{n+1}`: `B_n` keeps `+`, `ω^·`, `φ` and
  `Ω₁` and moves the leaves; it extends `Rk.rkB_rjDat` from `ε_{Ω₁+1}` to `Γ_{Ω₁+1}`).

No new axiom.  New definition: `ssDat`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Mv

variable {S : InaccSeq.{0}}

/-! ## The recursion -/

theorem ss_Om1_lt_Gam : (Om1 : Ordinal.{0}) < ggGam := by rw [rj_Om1]; exact ggGam_spec.2

/-- An `ε`-number in `(Ω₁, Γ_{Ω₁+1})` is not a fixed point of every `φ(o, ·)`, `o < z`: `invVeblen₁ z < z`. -/
theorem ss_inv1_lt {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggGam) : invVeblen₁ z < z := by
  refine lt_of_le_of_ne (invVeblen₁_le z) fun e => ?_
  have hfix : ∀ o < z, veblen o z = z := fun o ho => veblen_eq_of_lt_invVeblen₁ (by rw [e]; exact ho)
  have hSC : SC z := ⟨rj_Om1_pos.trans h1, fun a ha b hb => by
    calc veblen a b < veblen a z := veblen_lt_veblen_iff_right.2 hb
      _ = z := hfix a ha⟩
  exact absurd (ggGam_le hSC (by rw [← rj_Om1]; exact h1)) (not_le.2 h2)

/-- `invVeblen₂ z < z` for an `ε`-number `z`. -/
theorem ss_inv2_lt {z : Ordinal.{0}} (hE : ω ^ z = z) : invVeblen₂ z < z := by
  have := invVeblen₂_lt z; rwa [hE] at this

/-- `log_ω z < z` for a non-`ε` `z > 0`. -/
theorem ss_log_lt {z : Ordinal.{0}} (h0 : z ≠ 0) (hE : ω ^ z ≠ z) : log ω z < z := by
  refine lt_of_le_of_ne (log_le_self ω z) fun e => hE ?_
  have hle : ω ^ z ≤ z := by have := opow_log_le_self ω h0; rwa [e] at this
  exact le_antisymm hle (right_le_opow z one_lt_omega0)

/-- **The countable data of a code `z < Γ_{Ω₁+1}`** on its Veblen normal form over `{0, Ω₁}`: `z` if `z < Ω₁`; `0`
if `z = Ω₁`; for a non-`ε` `z ∈ (Ω₁, Γ_{Ω₁+1})` the larger data of `log_ω z` and of `z mod ω^{log_ω z}`; for an
`ε`-number `z = φ(a, b) ∈ (Ω₁, Γ_{Ω₁+1})` (`a = invVeblen₁ z`, `b = invVeblen₂ z`) the larger data of `a` and `b`.
Junk value `0` from `Γ_{Ω₁+1}` on. -/
noncomputable def ssDat (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : Om1 < z ∧ z < ggGam then
    if hE : ω ^ z = z then
      have : invVeblen₁ z < z := ss_inv1_lt hz.1 hz.2
      have : invVeblen₂ z < z := ss_inv2_lt hE
      max (ssDat (invVeblen₁ z)) (ssDat (invVeblen₂ z))
    else
      have : log ω z < z := ss_log_lt (rj_Om1_pos.trans hz.1).ne' hE
      have : z % ω ^ log ω z < z := rj_mod_lt (rj_Om1_pos.trans hz.1).ne'
      max (ssDat (log ω z)) (ssDat (z % ω ^ log ω z))
  else if z < Om1 then z else 0
termination_by z

theorem ssDat_small {z : Ordinal.{0}} (h : z < Om1) : ssDat z = z := by
  rw [ssDat, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem ssDat_Om1 : ssDat Om1 = 0 := by
  rw [ssDat, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem ssDat_big {z : Ordinal.{0}} (h : ggGam ≤ z) : ssDat z = 0 := by
  rw [ssDat, dif_neg (fun hz => absurd hz.2 (not_lt.2 h)),
    if_neg (fun h' => absurd (h'.trans ss_Om1_lt_Gam) (not_lt.2 h))]

/-- The `ε` clause. -/
theorem ssDat_eq_phi {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggGam) (hE : ω ^ z = z) :
    ssDat z = max (ssDat (invVeblen₁ z)) (ssDat (invVeblen₂ z)) := by
  rw [ssDat, dif_pos ⟨h1, h2⟩, dif_pos hE]

/-- The Cantor clause. -/
theorem ssDat_eq_cnf {z : Ordinal.{0}} (h1 : Om1 < z) (h2 : z < ggGam) (hE : ω ^ z ≠ z) :
    ssDat z = max (ssDat (log ω z)) (ssDat (z % ω ^ log ω z)) := by
  rw [ssDat, dif_pos ⟨h1, h2⟩, dif_neg hE]

/-- **The data is countable.** -/
theorem ssDat_lt_Om1 : ∀ z : Ordinal.{0}, ssDat z < Om1 := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  by_cases hz : Om1 < z ∧ z < ggGam
  · by_cases hE : ω ^ z = z
    · rw [ssDat_eq_phi hz.1 hz.2 hE]
      exact max_lt (IH _ (ss_inv1_lt hz.1 hz.2)) (IH _ (ss_inv2_lt hE))
    · rw [ssDat_eq_cnf hz.1 hz.2 hE]
      exact max_lt (IH _ (ss_log_lt (rj_Om1_pos.trans hz.1).ne' hE)) (IH _ (rj_mod_lt (rj_Om1_pos.trans hz.1).ne'))
  · rw [ssDat, dif_neg hz]
    split_ifs with h
    · exact h
    · exact rj_Om1_pos

/-- **`ssDat = rjDat` below `ε_{Ω₁+1}`.** -/
theorem ssDat_eq_rj : ∀ z : Ordinal.{0}, z < ggE → ssDat z = rjDat z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzE
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [ssDat_small h, rjDat_small h]
  · rw [ssDat_Om1, rjDat_Om1]
  · have hE : ω ^ z ≠ z := fun e => absurd (ggE_le e (by rw [← rj_Om1]; exact h)) (not_le.2 hzE)
    have hl := rj_log_lt h hzE
    have hm := rj_mod_lt (rj_Om1_pos.trans h).ne'
    rw [ssDat_eq_cnf h (hzE.trans_le ggE_le_ggGam) hE, rjDat_eq h hzE, IH _ hl (hl.trans hzE),
      IH _ hm (hm.trans hzE)]

/-- `Ω₁ + ε_{Ω₁+1} = ε_{Ω₁+1}`. -/
theorem ss_Om1_add_E : Om1 + ggE = ggE := by
  rw [rj_Om1]
  exact Ordinal.add_of_omega0_opow_le (by rw [Rk.rk_E_inE]; exact Rk.rk_Om1_E) Rk.rk_E_inE.le

/-- `Ω₁·ε_{Ω₁+1} = ε_{Ω₁+1}`. -/
theorem ss_Om1_mul_E : Om1 * ggE = ggE := by
  rw [rj_Om1]
  conv_lhs => rw [← Bt.Om1_opow, ← Rk.rk_E_inE]
  rw [← opow_add, ← rj_Om1, ss_Om1_add_E, Rk.rk_E_inE]

/-- `u_{ε_{Ω₁+1}} = ε_{Ω₁+1}`. -/
theorem ss_leOe_E : Le.leOe ggE = ggE := by
  unfold Le.leOe; rw [← rj_Om1, ss_Om1_mul_E, Rk.rk_E_inE]

/-! ## Codes and data -/

/-- **A code**: `z < Γ_{Ω₁+1}` with `ssDat z < a` (`0 < a`) is a code over `a`. -/
theorem ss_code {a : Ordinal.{0}} (ha : 0 < a) : ∀ z : Ordinal.{0}, z < ggGam → ssDat z < a → GgCl a z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG hd
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [ssDat_small h] at hd; exact GgCl.small hd
  · rw [rj_Om1]; exact GgCl.om
  · by_cases hE : ω ^ z = z
    · rw [ssDat_eq_phi h hzG hE] at hd
      have h1 := ss_inv1_lt h hzG
      have h2 := ss_inv2_lt hE
      have e : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by rw [veblen_invVeblen₁_invVeblen₂, hE]
      rw [← e]
      exact GgCl.phi (IH _ h1 (h1.trans hzG) ((le_max_left _ _).trans_lt hd))
        (IH _ h2 (h2.trans hzG) ((le_max_right _ _).trans_lt hd))
    · rw [ssDat_eq_cnf h hzG hE] at hd
      have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
      have hl := ss_log_lt hz0 hE
      have hm := rj_mod_lt hz0
      have he := IH _ hl (hl.trans hzG) ((le_max_left _ _).trans_lt hd)
      have hr := IH _ hm (hm.trans hzG) ((le_max_right _ _).trans_lt hd)
      obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
      have hdec : ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z := Ordinal.div_add_mod z _
      rw [← hdec, hk]
      exact GgCl.add (GgCl.mul_nat ha (GgCl.opow ha he) k) hr

/-- A code over `Z ≤ Γ_{Ω₁+1}` is below `Γ_{Ω₁+1}`. -/
theorem ss_cl_lt_Gam {Z : Ordinal.{0}} (hZ : Z ≤ ggGam) {z : Ordinal.{0}} (hz : GgCl Z z) : z < ggGam := by
  induction hz with
  | small h => exact h.trans_le hZ
  | om => exact ggGam_spec.2
  | add _ _ ihx ihy => exact (Lq.lq_SC_indec ggGam_spec.1).add_lt ihx ihy
  | phi _ _ ihx ihy => exact ggGam_spec.1.2 _ ihx _ ihy

/-- **The codes over a countable `Z` are closed under the inverse Veblen function**: for a code `z` over `Z ≤ Ω₁`
that is an `ε`-number above `Ω₁`, `invVeblen₁ z` and `invVeblen₂ z` are codes over `Z`. -/
theorem ss_cl_inv {Z : Ordinal.{0}} (hZ : Z ≤ Om1) : ∀ z, GgCl Z z → Om1 < z → ω ^ z = z →
    GgCl Z (invVeblen₁ z) ∧ GgCl Z (invVeblen₂ z) := by
  intro z hz
  induction hz with
  | small h => exact fun h1 _ => absurd (h.trans_le hZ) (not_lt.2 h1.le)
  | om => exact fun h1 _ => absurd h1 (by rw [rj_Om1]; exact lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h1 hE
    have hI : Indec (x + y) := inE_indec hE
    rcases eq_or_lt_of_le (le_self_add : x ≤ x + y) with ex | hx
    · rw [← ex] at h1 hE ⊢; exact ihx h1 hE
    rcases eq_or_lt_of_le (le_add_self : y ≤ x + y) with ey | hy
    · rw [← ey] at h1 hE ⊢; exact ihy h1 hE
    exact absurd (hI.add_lt hx hy) (lt_irrefl _)
  | @phi x y hx hy _ ihy =>
    intro h1 hE
    rcases eq_or_lt_of_le (right_le_veblen x y) with ey | hlt
    · rw [← ey] at h1 hE ⊢; exact ihy h1 hE
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [veblen_zero_apply] at hE hlt
      exact absurd ((opow_right_inj one_lt_omega0).1 hE).symm hlt.ne
    rw [invVeblen₁_veblen hlt, invVeblen₂_veblen hx0 hlt]
    exact ⟨hx, hy⟩

/-- **The data of a code over a strongly critical `q` is below `q`.** -/
theorem ss_cl_dat {q : Ordinal.{0}} (hq : SC q) : ∀ z, GgCl q z → ssDat z < q := by
  rcases lt_or_ge Om1 q with hq1 | hq1
  · exact fun z _ => (ssDat_lt_Om1 z).trans hq1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  rcases lt_trichotomy z Om1 with h | rfl | h
  · rw [ssDat_small h]; exact hz.lt_of_lt_Om1 hq (by rw [← rj_Om1]; exact h)
  · rw [ssDat_Om1]; exact hq.1
  rcases le_or_gt ggGam z with hG | hzG
  · rw [ssDat_big hG]; exact hq.1
  by_cases hE : ω ^ z = z
  · obtain ⟨h1, h2⟩ := ss_cl_inv hq1 z hz h hE
    rw [ssDat_eq_phi h hzG hE]
    exact max_lt (IH _ (ss_inv1_lt h hzG) h1) (IH _ (ss_inv2_lt hE) h2)
  · have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
    obtain ⟨hsub, hlog⟩ := ggDec hq z hz
    set g := log ω z with hg
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hwk : GgCl q (ω ^ g * k) := GgCl.mul_nat hq.1 (GgCl.opow hq.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : GgCl q (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    rw [ssDat_eq_cnf h hzG hE]
    exact max_lt (IH _ (ss_log_lt hz0 hE) hlog) (IH _ (rj_mod_lt hz0) hr)

/-- **For a strongly critical `q` and `z < Γ_{Ω₁+1}`: `GgCl q z ↔ ssDat z < q`.** -/
theorem ss_cl_iff {q z : Ordinal.{0}} (hq : SC q) (hz : z < ggGam) : GgCl q z ↔ ssDat z < q :=
  ⟨ss_cl_dat hq z, ss_code hq.1 z hz⟩

/-! ## The base change -/

/-- `B_n(c_{n+1}) = L(ω+1)` is countable. -/
theorem ssB_c_lt (n : ℕ) : Bc.bcB S n (Bc.bcC S (n + 1)) < Om 1 := by
  have e : Bc.bcB S n (Bc.bcC S (n + 1)) = Nc.ncL S (ω + 1) := Bc.bcB_base1 (S := S) n
  rw [e]; exact InaccSeq.psi_lt Low.InR_Om_one _

/-- **`B_n` keeps the codes below `Γ_{Ω₁+1}`**: for a code `z` over `c_{n+1}`, `B_n z < Γ_{Ω₁+1}`. -/
theorem ssB_lt_Gam {n : ℕ} {z : Ordinal.{0}} (hz : GgCl (Bc.bcC S (n + 1)) z) : Bc.bcB S n z < ggGam := by
  have hcl := (Rk.rkB_cl (n := n) (Bc.bcC_lt S (n + 1)) z hz).2
  exact ss_cl_lt_Gam ((ssB_c_lt n).le.trans ggGam_spec.2.le) hcl

/-- **`ssDat (B_n z) = B_n (ssDat z)`** for every code `z` over `c_{n+1}`. -/
theorem ssB_dat {n : ℕ} : ∀ z, GgCl (Bc.bcC S (n + 1)) z → ssDat (Bc.bcB S n z) = Bc.bcB S n (ssDat z) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hc : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hc1 : Bc.bcC S (n + 1) ≤ Om1 := by rw [rj_Om1]; exact (hLw.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  have hDz := (Rk.rkB_cl (n := n) hLw z hz).1
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hzG : z < ggGam := ss_cl_lt_Gam (hc1.trans ss_Om1_lt_Gam.le) hz
  have hBzG : Bc.bcB S n z < ggGam := ssB_lt_Gam hz
  have hdL : ∀ w, GgCl (Bc.bcC S (n + 1)) w → ssDat w < Nc.ncL S ω := fun w hw =>
    (ss_cl_dat hc w hw).trans hLw
  rcases lt_trichotomy z Om1 with h | rfl | h
  · have hzc : z < Bc.bcC S (n + 1) := hz.lt_of_lt_Om1 hc (by rw [← rj_Om1]; exact h)
    rw [ssDat_small h, ssDat_small (by rw [rj_Om1]; exact Rh.rhB_lt_Om1 hzc)]
  · rw [rj_Om1, hBO, ← rj_Om1, ssDat_Om1, Bc.bcB_zero]
  have hz0 : z ≠ 0 := (rj_Om1_pos.trans h).ne'
  have hOz : Om1 < Bc.bcB S n z := by
    have := (mvB_lt_iff (k := n) hDO hDz).2 (by rw [← rj_Om1]; exact h)
    rwa [hBO, ← rj_Om1] at this
  by_cases hE : ω ^ z = z
  · -- `z = φ(o, b)`
    set o := invVeblen₁ z with ho
    set b := invVeblen₂ z with hb
    have hoz : o < z := ss_inv1_lt h hzG
    have hbz : b < z := ss_inv2_lt hE
    obtain ⟨hco, hcb⟩ := ss_cl_inv hc1 z hz h hE
    have hev : veblen o b = z := by rw [ho, hb, veblen_invVeblen₁_invVeblen₂, hE]
    have ho0 : o ≠ 0 := by
      intro e
      rw [e, veblen_zero_apply] at hev
      have : ω ^ b = ω ^ z := by rw [hev, hE]
      exact absurd ((opow_right_inj one_lt_omega0).1 this) hbz.ne
    have hDo := (Rk.rkB_cl (n := n) hLw o hco).1
    have hDb := (Rk.rkB_cl (n := n) hLw b hcb).1
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
    rw [ssDat_eq_phi hOz hBzG hBE, ssDat_eq_phi h hzG hE, hBz, invVeblen₁_veblen hBb,
      invVeblen₂_veblen hBo0 hBb, IH o hoz hco, IH b hbz hcb]
    rcases le_total (ssDat o) (ssDat b) with hle | hle
    · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL b hcb) hle)]
    · rw [max_eq_left hle, max_eq_left (Ri.riB_mono (hdL o hco) hle)]
  · -- `z = ω^g·k + r`
    obtain ⟨hsub, hlog⟩ := ggDec hc z hz
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
    have hwk : GgCl (Bc.bcC S (n + 1)) (ω ^ g * k) := GgCl.mul_nat hc.1 (GgCl.opow hc.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : GgCl (Bc.bcC S (n + 1)) (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := rj_mod_lt hz0
    have hDg := (Rk.rkB_cl (n := n) hLw g hlog).1
    have hDr := (Rk.rkB_cl (n := n) hLw _ hr).1
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
    rw [ssDat_eq_cnf hOz hBzG hBE, hmodB, hlogB, IH g hgz hlog, IH _ hrz hr, ssDat_eq_cnf h hzG hE]
    rcases le_total (ssDat g) (ssDat (z % ω ^ g)) with hle' | hle'
    · rw [max_eq_right hle', max_eq_right (Ri.riB_mono (hdL _ hr) hle')]
    · rw [max_eq_left hle', max_eq_left (Ri.riB_mono (hdL g hlog) hle')]

end Googology.Trans.PoR.InaccPsi.R2.Ss
