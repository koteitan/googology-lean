import Googology.Trans.PoR.InaccPsi.R2.UfKey
import Googology.Trans.PoR.InaccPsi.R2.TzDL

/-!
# The direct hull lemma below `B₂`

`ψ = S.psi`, `B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `E₂ = ε_{Ω₂+1}`, `u_j = Ω₁^j = Le.leOe j`, `ucDatL j = ucDat (Ω₁ + j)`
(the data of the level `j`, `R2.UcCl`), `UcCl q` the codes over `q`, `RiDg q x` (all `Ω₁`-digits of `x` below `q`),
`UfP (UfK q) x` (every hereditary base-`Ω₂` component of `x` is a code over `q` or `≥ B₂`).  The port of
`Tz.tz_diglev` from `X` to `B₂`:

* `UfK`, `UfLev q x` (**every level `j < B₂` of `x` has `ucDatL j < q`**), `uf_cl_div` (codes are closed under
  `y ↦ y / Ω₁`), `uf_dig_opow_lvl`, `uf_lvl_of_cl`, `uf_eps_lev`;
* `uf_diglev` (**every member `x` of `Cl(a, q)` has all its `Ω₁`-digits below `q`, all its levels `j < B₂` with
  `ucDatL j < q`, is a code over `q` when `x < B₂`, and has every component a code or `≥ B₂` when `x < E₂`**, for a
  strongly critical `q ≤ Ω₁`, once every collapse `ψ_{Ω₁}(e)`, `e < a`, of a member `e` with these digits and levels
  is below `q`; a collapse `ψ_{Ω₂}(e) < B₂` is a code by `Uf.uf_key`).

No new axiom.  New definitions: `UfK`, `UfLev`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Ri Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Ts Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}}

/-- The components predicate of the hull lemma: a code over `q`, or `≥ B₂`. -/
def UfK (q z : Ordinal.{0}) : Prop := z < ucB → UcCl q z

/-- The levels condition on `x` below `q`: every level `j < B₂` of `x` has `ucDatL j < q`. -/
def UfLev (q x : Ordinal.{0}) : Prop :=
  ∀ j, j < ucB → x / Le.leOe j % Om 1 ≠ 0 → ucDatL j < q

theorem uf_B_inE : InE (ucB : Ordinal.{0}) := Low.opow_eq_self_of_SC ucB_SC

theorem uf_Om1_lt_B : Om 1 < (ucB : Ordinal.{0}) := by rw [← rj_Om1]; exact ucB_gt

theorem uf_Om1_mul_succ_lt {j : Ordinal.{0}} (hj : j < ucB) : Om 1 * j + Om 1 < ucB := by
  rw [← mul_add_one]
  exact uf_B_inE.mul_lt uf_Om1_lt_B (uf_B_inE.add_lt hj (gg_one_lt_of_SC ucB_SC))

/-- **A level `j < B₂` of `ω^y` is `y / Ω₁`, and `y < B₂`.** -/
theorem uf_dig_opow_lvl {j y : Ordinal.{0}} (hj : j < ucB) (h : ω ^ y / Le.leOe j % Om 1 ≠ 0) :
    y / Om 1 = j ∧ y < ucB := by
  obtain ⟨hlo, hhi⟩ := ri_dig_opow_ne h
  have hye : Om 1 * j + (y - Om 1 * j) = y := Ordinal.add_sub_cancel_of_le hlo
  have hr : y - Om 1 * j < Om 1 := by rw [← hye] at hhi; exact (add_lt_add_iff_left _).1 hhi
  refine ⟨by rw [← hye]; exact (ri_lvl hr).1, hhi.trans (uf_Om1_mul_succ_lt hj)⟩

/-- **The codes over a strongly critical `Z ≤ Ω₁` are closed under `y ↦ y / Ω₁`.** -/
theorem uf_cl_div {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ y, UcCl Z y → UcCl Z (y / Om1) := by
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Ordinal.zero_div]; exact UcCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := ucDec hZ hZ1 y hy
  set g := log ω y with hg
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt y one_lt_omega0)
  have hdec : ω ^ g * (y / ω ^ g) + y % ω ^ g = y := Ordinal.div_add_mod y _
  rw [hk] at hdec
  rcases lt_or_ge g Om1 with hgO | hgO
  · have hy1 : y < Om1 := by
      have h1 : y < ω ^ (g + 1) := lt_opow_succ_log_self one_lt_omega0 y
      refine h1.trans_le ?_
      rw [← rj_Om1_opow]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgO)
    rw [Ordinal.div_eq_zero_of_lt hy1]; exact UcCl.zero hZ.1
  · set g' := g - Om1 with hg'
    have hge : Om1 + g' = g := Ordinal.add_sub_cancel_of_le hgO
    have hg'C : UcCl Z g' := (ucDec hZ hZ1 g hlog).1 _ UcCl.om hgO
    have hwk : UcCl Z (ω ^ g * k) := UcCl.mul_nat hZ.1 (UcCl.opow hZ.1 hlog) k
    have hle : ω ^ g * k ≤ y := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : UcCl Z (y % ω ^ g) := by
      have e : y - ω ^ g * k = y % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hry : y % ω ^ g < y := rj_mod_lt hy0
    have e : y = Om1 * (ω ^ g' * k) + y % ω ^ g := by
      conv_lhs => rw [← hdec]
      rw [← hge, opow_add, rj_Om1_opow, mul_assoc]
    rw [e, Ordinal.mul_add_div _ hO0]
    exact UcCl.add (UcCl.mul_nat hZ.1 (UcCl.opow hZ.1 hg'C) k) (IH _ hry hr)

/-- **`ucDatL (y / Ω₁) < q` for a code `y` over a strongly critical `q ≤ Ω₁`.** -/
theorem uf_lvl_of_cl {q y : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hy : UcCl q y) : ucDatL (y / Om 1) < q := by
  unfold ucDatL
  rw [← rj_Om1]
  exact uc_cl_dat hq _ (UcCl.add UcCl.om (uf_cl_div hq hq1 y hy))

/-- **An `ε`-number `p` that is a code over `q` when `p < B₂` has all its levels below `q`.** -/
theorem uf_eps_lev {q p : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) (hp : ω ^ p = p) (hcl : p < ucB → UcCl q p) :
    UfLev q p := by
  intro j hj hd
  rw [← hp] at hd
  obtain ⟨hjy, hyB⟩ := uf_dig_opow_lvl hj hd
  rw [← hjy]
  exact uf_lvl_of_cl hq hq1 (hcl hyB)

/-- An `ε`-number above `Ω₂` is `≥ E₂`. -/
theorem uf_not_lt_E {p : Ordinal.{0}} (hp : ω ^ p = p) (h2 : Om (1 + 1) < p) : ¬ p < ucE :=
  not_lt.2 (ucE_le hp (by rw [uf_Om2]; exact h2))

/-- **The direct hull lemma below `B₂`.** For a strongly critical `q ≤ Ω₁`, once every collapse `ψ_{Ω₁}(e)`, `e < a`,
of a member `e` of `Cl(a, q)` with all digits and levels below `q` is below `q`: every member `x` of `Cl(a, q)` has
all its `Ω₁`-digits below `q`, all its levels `j < B₂` with `ucDatL j < q`, is a code over `q` when `x < B₂`, and has
every component a code over `q` or `≥ B₂` when `x < E₂`. -/
theorem uf_diglev {a q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om 1)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → RiDg q e → UfLev q e → S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → RiDg q x ∧ UfLev q x ∧ (x < ucB → UcCl q x) ∧
      (x < ucE → UfP (UfK q) x) := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := gg_one_lt_of_SC hq
  have hq1' : q ≤ Om1 := by rw [rj_Om1]; exact hq1
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hqlim : IsSuccLimit q := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hq)
  have hfin : ∀ e : Ordinal.{0}, e < ω → UfK q e := fun e he _ =>
    UcCl.small (he.trans_le (omega0_le_of_isSuccLimit hqlim))
  have hK0 : UfK q 0 := fun _ => UcCl.zero hq.1
  have hK1 : UfK q 1 := fun _ => UcCl.one hq.1
  have hKadd : ∀ a b, UfK q a → UfK q b → UfK q (a + b) := fun a b ha hb h =>
    UcCl.add (ha (le_self_add.trans_lt h)) (hb (le_add_self.trans_lt h))
  have hKop : ∀ δ, δ < OmTwo → UfK q δ → UfK q (ω ^ δ) := fun δ _ hδ h =>
    UcCl.opow hq.1 (hδ (((isNormal_opow one_lt_omega0).strictMono.le_apply).trans_lt h))
  have hq2 : q < Om (1 + 1) := hq1.trans_lt ts_Om1_lt_Om2
  have hsmallD : ∀ v, v < q → RiDg q v := fun v hv j => (rhk_dig_le j v).trans_lt hv
  have hcount : ∀ v, v < Om 1 → UfLev q v := by
    intro v hv j _ h
    rw [ri_dig_count hv h]
    unfold ucDatL; rw [add_zero, ucDat_Om1]; exact hq.1
  have hepsD : ∀ p, ω ^ p = p → Om 1 ≤ p → RiDg q p := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  have hsmall : ∀ v, v < q → RiDg q v ∧ UfLev q v ∧ (v < ucB → UcCl q v) ∧ (v < ucE → UfP (UfK q) v) :=
    fun v hv => ⟨hsmallD v hv, hcount v (hv.trans_le hq1), fun _ => UcCl.small hv,
      fun _ => (ufP_small (hv.trans (by rw [uf_Om2]; exact hq2))).2 fun _ => UcCl.small hv⟩
  have hB2 : (ucB : Ordinal.{0}) < Om (1 + 1) := by rw [← uf_Om2]; exact ucB_lt_Om2
  have hbig : ∀ p, ω ^ p = p → Om (1 + 1) < p → RiDg q p ∧ UfLev q p ∧ (p < ucB → UcCl q p) ∧
      (p < ucE → UfP (UfK q) p) := by
    intro p hp h2
    have hcl : p < ucB → UcCl q p := fun h => absurd (h.trans hB2) (not_lt.2 h2.le)
    exact ⟨hepsD p hp (ts_Om1_lt_Om2.le.trans h2.le), uf_eps_lev hq hq1' hp hcl, hcl,
      fun h => absurd h (uf_not_lt_E hp h2)⟩
  have hSCmid : ∀ p, SC p → Om 1 < p → p < Om (1 + 1) → (p < ucB → UcCl q p) →
      RiDg q p ∧ UfLev q p ∧ (p < ucB → UcCl q p) ∧ (p < ucE → UfP (UfK q) p) := by
    intro p hp h1 h2 hcl
    exact ⟨hepsD p (Low.opow_eq_self_of_SC hp) h1.le, uf_eps_lev hq hq1' (Low.opow_eq_self_of_SC hp) hcl, hcl,
      fun _ => (ufP_small (by rw [uf_Om2]; exact h2)).2 hcl⟩
  have hOm2P : UfP (UfK q) OmTwo := by
    intro c hc
    rw [ucComps_Om2] at hc
    rcases hc with rfl | hc
    · exact hK1
    · rw [mem_singleton_iff] at hc; rw [hc]; exact hK0
  intro x hx
  induction hx with
  | @small x hxb => exact hsmall x hxb
  | zero => exact hsmall 0 hq.1
  | inacc n => exact hbig _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Mx.mxOm2_lt_I n)
  | inaccW => exact hbig _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) Mx.mxOm2_lt_Iw
  | @add x y _ _ ihx ihy =>
    refine ⟨fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx.1 j) (ihy.1 j)), ?_, fun h => ?_, fun h => ?_⟩
    · intro j hj h
      by_cases hx0 : x / Le.leOe j % Om 1 = 0
      · by_cases hy0 : y / Le.leOe j % Om 1 = 0
        · exfalso
          have := rhk_dig_add j x y
          rw [hx0, hy0, add_zero] at this
          exact h (le_antisymm this zero_le)
        · exact ihy.2.1 j hj hy0
      · exact ihx.2.1 j hj hx0
    · exact UcCl.add (ihx.2.2.1 (lt_of_le_of_lt le_self_add h)) (ihy.2.2.1 (lt_of_le_of_lt le_add_self h))
    · exact ufP_add hK0 hKadd h (ihx.2.2.2 (lt_of_le_of_lt le_self_add h)) (ihy.2.2.2 (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    have hcl : veblen x y < ucB → UcCl q (veblen x y) := fun h =>
      UcCl.phi (ihx.2.2.1 ((left_le_veblen x y).trans_lt h)) (ihy.2.2.1 ((right_le_veblen x y).trans_lt h))
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy.1 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq)
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · refine ⟨fun j => ?_, fun j hj h => ?_, hcl, fun h => ?_⟩
        · rw [veblen_zero_apply]
          have hy0 := ihy.1 0
          rw [rhk_dig_zero] at hy0
          exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
        · rw [veblen_zero_apply] at h
          obtain ⟨hjy, hyB⟩ := uf_dig_opow_lvl hj h
          rw [← hjy]
          exact uf_lvl_of_cl hq hq1' (ihy.2.2.1 hyB)
        · rw [veblen_zero_apply] at h ⊢
          have hyE : y < ucE := ((isNormal_opow one_lt_omega0).strictMono.le_apply).trans_lt h
          exact ufP_opow hK0 hfin hKop h (ihy.2.2.2 hyE)
      · have hε : ω ^ veblen x y = veblen x y := Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)
        refine ⟨hepsD _ hε hv, uf_eps_lev hq hq1' hε hcl, hcl, fun h => ?_⟩
        rcases lt_trichotomy (veblen x y) (Om (1 + 1)) with hlt | heq | hgt
        · exact (ufP_small (by rw [uf_Om2]; exact hlt)).2 hcl
        · rw [heq, ← uf_Om2]; exact hOm2P
        · exact absurd h (uf_not_lt_E hε hgt)
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1
    have hε : ω ^ Om x = Om x := Low.opow_eq_self_of_SC (SC_Om hx0)
    rcases lt_trichotomy (Om x) (Om (1 + 1)) with hlt | heq | hgt
    · have hx2 : x < 1 + 1 := Om_lt_Om.1 hlt
      have hx1 : x = 1 := le_antisymm (Order.lt_add_one_iff.1 hx2) (Order.one_le_iff_ne_zero.2 hx0)
      subst hx1
      have hcl : Om 1 < ucB → UcCl q (Om 1) := fun _ => by rw [← rj_Om1]; exact UcCl.om
      exact ⟨hepsD _ hε le_rfl, uf_eps_lev hq hq1' hε hcl, hcl,
        fun _ => (ufP_small (by rw [uf_Om2]; exact ts_Om1_lt_Om2)).2 hcl⟩
    · rw [heq]
      have hcl : Om (1 + 1) < ucB → UcCl q (Om (1 + 1)) := fun h => absurd (h.trans hB2) (lt_irrefl _)
      have hε2 : ω ^ Om (1 + 1) = Om (1 + 1) := ts_Om2_opow
      exact ⟨hepsD _ hε2 ts_Om1_lt_Om2.le, uf_eps_lev hq hq1' hε2 hcl, hcl, fun _ => by rw [← uf_Om2]; exact hOm2P⟩
    · exact hbig _ hε hgt
  | @coll π e hπ _ heC _ ihe =>
    show RiDg q (S.psi e.1 π) ∧ UfLev q (S.psi e.1 π) ∧ (S.psi e.1 π < ucB → UcCl q (S.psi e.1 π)) ∧
      (S.psi e.1 π < ucE → UfP (UfK q) (S.psi e.1 π))
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe.1 ihe.2.1)
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
      have hcl : S.psi e.1 (Om (1 + 1)) < ucB → UcCl q (S.psi e.1 (Om (1 + 1))) := by
        intro h
        have heE : e.1 < ucE := by
          by_contra hc
          push Not at hc
          have := (psi_mono hκ hc).1
          rw [uc_psiE_eq_B] at this
          exact absurd h (not_lt.2 this)
        exact uf_key hq hq1' (ihe.2.2.2 heE) h
      exact hSCmid _ (SC_psi hκ e.1) (ts_Om1_lt_psi _) (ts_psi_lt _) hcl
    · exact hbig _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (ts_Om2_lt_psi hπ hπ1 hπ2)

end Googology.Trans.PoR.InaccPsi.R2.Uf
