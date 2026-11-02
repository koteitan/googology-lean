import Googology.Trans.PoR.InaccPsi.R2.YgIF
import Googology.Trans.PoR.InaccPsi.R2.UoUc

/-!
# The inacc-free closure without fixed atoms, and its arithmetic

`YbK S q` (`Yb.YbK`) has a clause `fix` (levels whose datum is below `Γ₀`, any shape), so it cannot be decomposed
syntactically.  `YgK S q` is the closure of `q ∪ {0}` under `+`, `φ`, `Ω_·` and every collapse `ψ_π`, `π ≠ Ω₁` (no
inaccessible, no fixed atom); it is contained in `YbK S q` (`YgK.toYb`).  Its arithmetic is that of `Ul.UlK` without
the clauses `inacc`, `inaccW` (the proofs are those of `Ul.ulK_dec` … `Ul.ulK_opow_mul`):

* `YgK`, `YgK.toYb`, `YgK.opow`, `YgK.one`, `YgK.nat`, `YgK.mul_nat`;
* `ygK_dec` (**`w − x` and `log_ω w`**), `ygK_split`, `ygK_mod`, `ygK_div`, `ygK_opow_mul` (**`ω^a·b`**);
* `ygW1`, `ygW2`, `ygLeWe`, `ygLeMulWe`, `ygPsi2`, `yg_K_comps` (**`x < E₂` is in `YgK` when its components are**:
  the port of `Uo.uo_K_comps`).

No new axiom.  New definition: `YgK` (an inductive predicate).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

/-- **The inacc-free closure without fixed atoms**: leaves below `q`, `0`, `+`, `φ`, `Ω_·`, `ψ_π` (`π ≠ Ω₁`). -/
inductive YgK (S : InaccSeq.{0}) (q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < q → YgK S q x
  | zero : YgK S q 0
  | add {x y : Ordinal.{0}} : YgK S q x → YgK S q y → YgK S q (x + y)
  | phi {x y : Ordinal.{0}} : YgK S q x → YgK S q y → YgK S q (veblen x y)
  | om {x : Ordinal.{0}} : YgK S q x → YgK S q (Om x)
  | coll {π e : Ordinal.{0}} : S.InR π → π ≠ Om 1 → YgK S q π → YgK S q e → YgK S q (S.psi e π)

variable {S : InaccSeq.{0}} {q : Ordinal.{0}}

/-- **`YgK ⊆ YbK`** (`0 < q`). -/
theorem YgK.toYb (hq0 : 0 < q) {x : Ordinal.{0}} (hx : YgK S q x) : Yb.YbK S q x := by
  induction hx with
  | small h => exact Yb.YbK.small h
  | zero => exact Yb.YbK.small hq0
  | add _ _ ih1 ih2 => exact Yb.YbK.add ih1 ih2
  | phi _ _ ih1 ih2 => exact Yb.YbK.phi ih1 ih2
  | om _ ih => exact Yb.YbK.om ih
  | coll hπ hπ1 _ _ ihπ ihe => exact Yb.YbK.coll hπ hπ1 ihπ ihe

theorem YgK.opow {x : Ordinal.{0}} (h : YgK S q x) : YgK S q (ω ^ x) := by
  have := YgK.phi YgK.zero h; rwa [veblen_zero_apply] at this

theorem YgK.one : YgK S q 1 := by
  have := YgK.opow (S := S) (q := q) YgK.zero; rwa [opow_zero] at this

theorem YgK.nat : ∀ n : ℕ, YgK S q (n : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero]; exact YgK.zero
  | n + 1 => by rw [Nat.cast_succ]; exact YgK.add (YgK.nat n) YgK.one

theorem YgK.mul_nat {x : Ordinal.{0}} (h : YgK S q x) : ∀ n : ℕ, YgK S q (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact YgK.zero
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact YgK.add (YgK.mul_nat h n) h


/-- **Decomposition**: for `w ∈ K_q`, `w − x ∈ K_q` (every `x ∈ K_q`, `x ≤ w`) and `log_ω w ∈ K_q`. -/
theorem ygK_dec (hq : SC q) : ∀ w, YgK S q w →
    (∀ x, YgK S q x → x ≤ w → YgK S q (w - x)) ∧ YgK S q (log ω w) := by
  have hprin : ∀ p, YgK S q p → IsPrincipal (· + ·) p → ω ^ p = p →
      (∀ x, YgK S q x → x ≤ p → YgK S q (p - x)) ∧ YgK S q (log ω p) := fun p hp hP hE => by
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases Gg.gg_sub_prin hP hx with e | e <;> rw [e]
      · exact hp
      · exact YgK.zero
    · have : log ω p = p := by
        conv_lhs => rw [← hE]
        exact log_opow one_lt_omega0 _
      rw [this]; exact hp
  have hzero : (∀ x, YgK S q x → x ≤ 0 → YgK S q (0 - x)) ∧ YgK S q (log ω 0) :=
    ⟨fun x _ _ => YgK.small ((Ordinal.sub_le_self 0 x).trans_lt hq.1),
      YgK.small ((log_le_self ω 0).trans_lt hq.1)⟩
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, YgK S q v → v ≤ w →
      (∀ x, YgK S q x → x ≤ v → YgK S q (v - x)) ∧ YgK S q (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => YgK.small ((Ordinal.sub_le_self v x).trans_lt h),
      YgK.small ((log_le_self ω v).trans_lt h)⟩
  | zero => intro _; exact hzero
  | @om x hx _ =>
    intro _
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hzero
    · exact hprin _ (YgK.om hx) (SC_Om hx0).isPrincipal (Low.opow_eq_self_of_SC (SC_Om hx0))
  | @coll π e hπ hπW hπK heK _ _ =>
    intro _
    exact hprin _ (YgK.coll hπ hπW hπK heK) (SC_psi hπ e).isPrincipal
      (Low.opow_eq_self_of_SC (SC_psi hπ e))
  | @phi a b ha hb _ _ =>
    intro _
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases Gg.gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · exact YgK.opow hb
        · exact YgK.zero
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := Gg.gg_veblen_eps (y := b) ha0
      have hP : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      exact hprin _ (YgK.phi ha hb) hP hE
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact YgK.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : YgK S q (x - u) := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact YgK.zero
    · rcases Gg.ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2

/-- The Cantor split `x = ω^g·k + r` of a member of `K_q`: `g = log_ω x`, `ω^g·k`, `r` in `K_q`. -/
theorem ygK_split (hq : SC q) {x : Ordinal.{0}} (hx : YgK S q x) (hx0 : x ≠ 0) :
    ∃ k : ℕ, ω ^ log ω x * k + x % ω ^ log ω x = x ∧ YgK S q (log ω x) ∧
      YgK S q (x % ω ^ log ω x) ∧ x % ω ^ log ω x < x := by
  obtain ⟨hsub, hlog⟩ := ygK_dec hq x hx
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdec : ω ^ log ω x * k + x % ω ^ log ω x = x := by
    have := Ordinal.div_add_mod x (ω ^ log ω x); rwa [hk] at this
  have hwk : YgK S q (ω ^ log ω x * k) := (YgK.opow hlog).mul_nat k
  have hr : YgK S q (x % ω ^ log ω x) := by
    have e : x - ω ^ log ω x * k = x % ω ^ log ω x := by
      nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
    have hle : ω ^ log ω x * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    rw [← e]; exact hsub _ hwk hle
  exact ⟨k, hdec, hlog, hr, mod_opow_log_lt_self _ hx0⟩

/-- **`x % ω^f ∈ K_q`** for `x ∈ K_q` and every `f`. -/
theorem ygK_mod (hq : SC q) : ∀ x, YgK S q x → ∀ f : Ordinal.{0}, YgK S q (x % ω ^ f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx f
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.mod_eq_of_lt (opow_pos f omega0_pos)]; exact YgK.zero
  obtain ⟨k, hdec, _, hr, hrx⟩ := ygK_split hq hx hx0
  rcases lt_or_ge (log ω x) f with hgf | hfg
  · have hxf : x < ω ^ f := (lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgf))
    rw [Ordinal.mod_eq_of_lt hxf]; exact hx
  · obtain ⟨c, hc⟩ : ω ^ f ∣ ω ^ log ω x * k := (opow_dvd_opow _ hfg).trans (dvd_mul_right _ _)
    have e : x % ω ^ f = x % ω ^ log ω x % ω ^ f := by
      conv_lhs => rw [← hdec, hc, Ordinal.mul_add_mod_self]
    rw [e]; exact IH _ hrx hr f

/-- **`x / ω^f ∈ K_q`** for `x, f ∈ K_q`. -/
theorem ygK_div (hq : SC q) : ∀ x, YgK S q x → ∀ f : Ordinal.{0}, YgK S q f → YgK S q (x / ω ^ f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx f hf
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.div_eq_zero_of_lt (opow_pos f omega0_pos)]; exact YgK.zero
  obtain ⟨k, hdec, hlog, hr, hrx⟩ := ygK_split hq hx hx0
  rcases lt_or_ge (log ω x) f with hgf | hfg
  · have hxf : x < ω ^ f := (lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgf))
    rw [Ordinal.div_eq_zero_of_lt hxf]; exact YgK.zero
  · have hgf' : f + (log ω x - f) = log ω x := Ordinal.add_sub_cancel_of_le hfg
    have e : x = ω ^ f * (ω ^ (log ω x - f) * k) + x % ω ^ log ω x := by
      conv_lhs => rw [← hdec]
      rw [← mul_assoc, ← opow_add, hgf']
    have hdiv : x / ω ^ f = ω ^ (log ω x - f) * k + x % ω ^ log ω x / ω ^ f := by
      conv_lhs => rw [e]
      exact Ordinal.mul_add_div _ (opow_pos f omega0_pos).ne' _
    rw [hdiv]
    exact YgK.add ((YgK.opow ((ygK_dec hq _ hlog).1 f hf hfg)).mul_nat k) (IH _ hrx hr f hf)

/-- **`ω^a·b ∈ K_q`** for `a, b ∈ K_q`. -/
theorem ygK_opow_mul (hq : SC q) {a : Ordinal.{0}} (ha : YgK S q a) :
    ∀ b, YgK S q b → YgK S q (ω ^ a * b) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero]; exact YgK.zero
  obtain ⟨k, hdec, hlog, hr, hrx⟩ := ygK_split hq hb hb0
  have e : ω ^ a * b = ω ^ (a + log ω b) * k + ω ^ a * (b % ω ^ log ω b) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, ← opow_add]
  rw [e]
  exact YgK.add ((YgK.opow (YgK.add ha hlog)).mul_nat k) (IH _ hrx hr)

/-! ## Membership helpers (the ports of `Uo.uoW1` … `Uo.uo_K_comps`) -/

section helpers

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ts

theorem ygW1 : YgK S q (Om 1) := YgK.om YgK.one

theorem ygW2 : YgK S q (Om (1 + 1)) := YgK.om (YgK.add YgK.one YgK.one)

theorem yg_W2_ne1 : (Om (1 + 1) : Ordinal.{0}) ≠ Om 1 := by
  intro h; have e := Om_strictMono.injective h
  exact absurd e (lt_add_of_pos_right (1 : Ordinal.{0}) zero_lt_one).ne'

theorem ygLeWe (hq : SC q) {e : Ordinal.{0}} (he : YgK S q e) : YgK S q (leWe e) := by
  have h := ygK_opow_mul hq (ygW2 (S := S) (q := q)) e he
  rw [ts_Om2_opow] at h
  exact YgK.opow h

theorem ygLeMulWe (hq : SC q) {e x : Ordinal.{0}} (he : YgK S q e) (hx : YgK S q x) :
    YgK S q (leWe e * x) := by
  have h := ygK_opow_mul hq (ygW2 (S := S) (q := q)) e he
  rw [ts_Om2_opow] at h
  exact ygK_opow_mul hq h x hx

theorem ygPsi2 {B : Ordinal.{0}} (hB : YgK S q B) : YgK S q (S.psi B (Om (1 + 1))) :=
  YgK.coll (InR_Om_succ 1) yg_W2_ne1 ygW2 hB

/-- **`x < E₂` is in `YgK` when all its components are.** -/
theorem yg_K_comps (hq : SC q) :
    ∀ x, x < ucE → (∀ c ∈ ucComps x, YgK S q c) → YgK S q x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxE hx
  by_cases hx2 : x < OmTwo
  · exact hx x (by rw [ucComps_small hx2]; rfl)
  have hx2' := not_lt.1 hx2
  have hc := ucComps_big hx2' hxE
  have hel := uc_log_lt hx2' hxE
  have hrl := uc_mod_lt hx2'
  have he := IH _ hel (hel.trans hxE) fun c h => hx c (by rw [hc]; exact Or.inl h)
  have hr := IH _ hrl (hrl.trans hxE) fun c h => hx c (by rw [hc]; exact Or.inr (Or.inr h))
  have hd := hx (x / OmTwo ^ log OmTwo x) (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hW := ygLeMulWe hq he hd
  rw [uc_leWe] at hW
  rw [← uc_cnf_eq x]
  exact YgK.add hW hr

end helpers

end Googology.Trans.PoR.InaccPsi.R2.Yg
