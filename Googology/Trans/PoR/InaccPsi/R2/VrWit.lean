import Googology.Trans.PoR.InaccPsi.R2.VrForm

/-!
# The repaired forms at the inner restarts of `L(k)` with low codes, and at the no-go witness

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

Let `a = L(k)`, `u₁ = υ_{a+1}`, `c = ω^{u₁+1}`, `g = ω^c`.  For an inner restart `a + z` (`0 < z`, `ω² | z`,
`z < υ_{a+2}`) the code is `m = -1 + e(z)` (`Vo.voCode_add`) and `r(a+z) = δ + m` (`Vo.voR_low`), so a repaired form
of `r(a+z)` is `ub (z+ω+1) base + (a decomposition of the CODE m)`.  Every code `m ≤ c` decomposes over `u₁`:
`m < u₁` is a `lo`-node, `m = u₁·n + p` (`1 ≤ n < ω`, `p < u₁`) a `ub 1`-node with `n` bases, `m = c = ϑ^{u₁}(1)` the
`ub 1 (th1 0)`-node.

* `vrR_inner` (**`r(a+z) = υ_{a+(z+ω+1)} + m_{a+z}`**), `vrExp_le` (`z < ω^{c+1} ⇒ -1 + e(z) ≤ c`);
* `vrDec_lo`, `vrDec_mid`, `vrDec_top`, `vrDec_code` (**every code `m ≤ ω^{υ_{λ+1}+1}` has a decomposition over
  `υ_{λ+1}`**);
* `vrTerm_ex` (**every `m < Ω₁` with no `ε`-number in `(u, m]` is a term value over `u`**), `vrDec_eps`,
  `vrForm_code` (**(B') at every inner restart `a + z`, `z < υ_{a+2}`, whose code lies below the next `ε`-number above
  `υ_{a+1}`**);
* `vrForm_inner` (**`VrForm` at every inner restart `a + z` with `z < ω^{c+1}`, `z + ω + 1 < β`**);
* `vrEw`, `vrWit_form` (**the repaired form holds at the no-go witness `g` of `Vo.voNoGo`**: the decomposition
  `vrEw g = ub (g+ω+1) base + ub 1 (th1 0)`), `vrWit_sep` (**at `g` none of the old forms holds, the repaired one
  does**), `vrForms_win` (**at `β₀ = g + ω²·2`, `υ_{a+g+ω²} < υ_{a+β₀} < L(k+1)`, every inner restart below `β₀` has
  a repaired form**);
* `vrEQ_code` (**EQ at a low-code inner restart `⇔` the code moves: `img E ≤ -1 + e(f z)`**),
  `vrImg_wit` (**the image of `vrEw g` under an offset map `f`: `υ_{μ+(f g+ω+1)} + ω^{υ_{μ+1}+1}`**), `vrCode_mu`,
  `vrEQ_wit` (**EQ at the witness holds, with equality, at every restart `μ` with `e(f g) = ω^{υ_{μ+1}+1}`**).

No new axiom, no new definition beyond the decomposition `vrEw` and the term `vrBs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ub

variable {S : InaccSeq.{0}}

/-! ## Codes and reaches above `L(k)` -/

/-- The constants above `a = L(k)`. -/
theorem vr_facts (k : ℕ) :
    0 < Nc.ncL S (k : Ordinal.{0}) ∧ InE (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1)) ∧
      InE (upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) ∧
      upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) ∧
      upsilon (Nc.ncL S (k : Ordinal.{0}) + 2) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
      InE (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ∧ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Om1 ∧
      (∀ x, x < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) → upsilon x < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) ∧
      ω < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
  have hm := upsilon_normal.strictMono
  set l := Nc.ncL S (k : Ordinal.{0})
  set L1 := Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) with hL1def
  have hlfix : upsilon l = l := Te.teUps_L k
  have hL1fix : upsilon L1 = L1 := Te.teUps_L (k + 1)
  have hl0 : 0 < l := pos_iff_ne_zero.2 (Te.teRst_L (S := S) k).1
  have hlL1 : l < L1 := Te.teL_lt_succ k
  have hL1O : L1 < Om1 := by rw [hL1def, Lw.lw_L_eq, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _
  have hL1E : InE L1 := hL1fix ▸ upsPt_inE (upsPt_upsilon (hl0.trans hlL1))
  have hlE : InE l := hlfix ▸ upsPt_inE (upsPt_upsilon hl0)
  have hbelow : ∀ x, x < L1 → upsilon x < L1 := fun x hx => hL1fix ▸ hm hx
  have hωL1 : ω < L1 := (Vo.vo_omega_le hlE hl0).trans_lt hlL1
  have h2 : (2 : Ordinal.{0}) < L1 := (natCast_lt_omega0 2).trans hωL1
  exact ⟨hl0, upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add)),
    upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add)), hm ((add_lt_add_iff_left l).2 one_lt_two),
    hbelow _ (hL1E.add_lt hlL1 h2), hL1E, hL1O, hbelow, hωL1⟩

/-- `ω ≤ z` for `z ≠ 0` with `ω² | z`. -/
theorem vr_omega_le {z : Ordinal.{0}} (hz0 : z ≠ 0) (hzd : ω ^ 2 ∣ z) : ω ≤ z :=
  (calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ ω ^ (2 : Ordinal.{0}) := opow_le_opow_right omega0_pos one_le_two
    _ = ω ^ 2 := Vo.vo_e2.symm).trans (le_of_dvd hz0 hzd)

/-- **The reach of an inner restart of `a = L(k)`**: for `0 < z < υ_{a+2}`, `ω² | z`, and `L(k+1) ≤ ν_C`,
`r(a+z) = υ_{a+(z+ω+1)} + m_{a+z}`. -/
theorem vrR_inner (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {z : Ordinal.{0}} (hz0 : 0 < z)
    (hzd : ω ^ 2 ∣ z) (hzu : z < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) :
    cdR S (Nc.ncL S (k : Ordinal.{0}) + z) =
      upsilon (Nc.ncL S (k : Ordinal.{0}) + (z + ω + 1)) + cdCode S (Nc.ncL S (k : Ordinal.{0}) + z) := by
  have hm := upsilon_normal.strictMono
  obtain ⟨hl0, -, -, -, hu2L1, hL1E, -, hbelow, hωL1⟩ := vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0})
  set L1 := Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})
  have hlR : IsRestartIdx l := Te.teRst_L k
  have hlL1 : l < L1 := Te.teL_lt_succ k
  have hωz := vr_omega_le hz0.ne' hzd
  have hR : IsRestartIdx (l + z) := ⟨(hl0.trans_le le_self_add).ne', dvd_add hlR.2 hzd⟩
  have hlz : l + z < L1 := hL1E.add_lt hlL1 (hzu.trans hu2L1)
  have h1 : (1 : Ordinal.{0}) < L1 := one_lt_omega0.trans hωL1
  have hC : upsilon (l + z + ω + 1) < nuC :=
    (hbelow _ (hL1E.add_lt (hL1E.add_lt hlz hωL1) h1)).trans_le hν
  have hcode : cdCode S (l + z) ≤ upsilon (l + z) := by
    rw [Vo.voCode_add k hωz hzu]
    exact ((cdOff_le _).trans (Cp.cpExp_le hz0.ne')).trans (le_add_self.trans hm.le_apply)
  rw [Vo.voR_low hR hC hcode]
  unfold cdDelta; rw [add_assoc, add_assoc, add_assoc]

/-- **The code bound**: `z < ω^{c+1}` (`z ≠ 0`) gives `-1 + e(z) ≤ c`. -/
theorem vrExp_le {z c : Ordinal.{0}} (hz0 : z ≠ 0) (hz : z < ω ^ (c + 1)) : cdOff (cdExp z) ≤ c := by
  refine (cdOff_le _).trans ?_
  have h1 : ω ^ cdExp z < ω ^ (c + 1) := (le_of_dvd hz0 (cdExp_dvd hz0)).trans_lt hz
  exact Order.lt_add_one_iff.1 ((opow_lt_opow_iff_right one_lt_omega0).1 h1)

/-! ## Decompositions of codes over `υ_{λ+1}` -/

/-- `n` copies of the base: `u·n`. -/
def vrBs : ℕ → UbT
  | 0 => .par 0
  | n + 1 => .add (vrBs n) .base

theorem vrBs_ev (u : Ordinal.{0}) : ∀ n : ℕ, UbT.ev u (vrBs n) = u * n
  | 0 => by simp [vrBs, UbT.ev]
  | n + 1 => by
    show UbT.ev u (vrBs n) + u = _
    rw [vrBs_ev u n, Nat.cast_succ, mul_add_one]

theorem vrBs_ok (u : Ordinal.{0}) (P : Ordinal.{0} → Prop) (hP : P 0) :
    ∀ n : ℕ, UbT.IsA (vrBs n) ∧ UbT.WF u (vrBs n) ∧ UbT.Lv P (vrBs n)
  | 0 => ⟨trivial, trivial, hP⟩
  | n + 1 => ⟨⟨(vrBs_ok u P hP n).1, trivial⟩, ⟨(vrBs_ok u P hP n).2.1, trivial⟩, ⟨(vrBs_ok u P hP n).2.2, trivial⟩⟩

/-- A code `m < υ_{λ+1}` is a `lo`-node. -/
theorem vrDec_lo {l β m : Ordinal.{0}} (hm : m < upsilon (succ l)) : ∃ E : VrE, VrWF l β E ∧ vrVal l E = m :=
  ⟨.lo m, hm, rfl⟩

/-- `0` is a leaf. -/
theorem vrLv_zero (l B : Ordinal.{0}) : vrLv l B 0 :=
  Or.inl (lt_of_le_of_lt zero_le (upsilon_normal.strictMono (lt_succ l) |>.trans_le' zero_le))

/-- A code `υ_{λ+1}·n + p` (`1 ≤ n < ω`, `p < υ_{λ+1}`) is a `ub 1`-node. -/
theorem vrDec_mid {l β m : Ordinal.{0}} (hl0 : 0 < l) (hβ : 1 < β) (hlo : upsilon (l + 1) ≤ m)
    (hhi : m < upsilon (l + 1) * ω) (hm2 : m < upsilon (succ (l + 1))) :
    ∃ E : VrE, VrWF l β E ∧ vrVal l E = m := by
  set u := upsilon (l + 1) with hu
  have hu0 : u ≠ 0 := (upsPt_upsilon (hl0.trans_le le_self_add)).1.ne'
  have hn : m / u < ω := (Ordinal.lt_mul_iff_div_lt hu0).1 hhi
  obtain ⟨n, hn'⟩ := lt_omega0.1 hn
  have hp : m % u < u := Ordinal.mod_lt m hu0
  have hps : m % u < upsilon (succ l) := by rw [succ_eq_add_one]; exact hp
  have he : u * (n : Ordinal.{0}) + m % u = m := by rw [← hn']; exact Ordinal.div_add_mod m u
  obtain ⟨hA, hW, hL⟩ := vrBs_ok u (vrLv l β) (vrLv_zero l β) n
  have hev : UbT.ev (upsilon (l + 1)) (.add (vrBs n) (.par (m % u))) = m := by
    show UbT.ev u (vrBs n) + m % u = m
    rw [vrBs_ev]; exact he
  exact ⟨.ub 1 (.add (vrBs n) (.par (m % u))), ⟨one_pos, hβ, ⟨hA, trivial⟩, ⟨hW, trivial⟩, ⟨hL, Or.inl hps⟩,
    by rw [hev]; exact hlo, by rw [hev]; exact hm2⟩, hev⟩

/-- `ϑ^u(1) = ω^{u+1}` at an `ε`-number `u < Ω₁` ([W07a] via `R2.vt_wbar`, `R2.wbar_eq`). -/
theorem vr_vt_one {u : Ordinal.{0}} (hu : InE u) (hu1 : u < Om1) : vt u (1 + 0) = ω ^ (u + 1) := by
  have hO : (0 : Ordinal.{0}) < Om1 := lt_of_le_of_lt zero_le hu1
  rw [vt_wbar hu hu1 hO]
  have h := wbar_eq hu 0 (fun β h1 h2 hβE => by
    rw [add_zero] at h2
    have e : β = u + 1 := le_antisymm h2 (Order.add_one_le_of_lt h1)
    have h1u : (1 : Ordinal.{0}) < u := one_lt_omega0.trans_le (Vo.vo_omega_le hu (InE.pos hu))
    exact Vo.vo_not_indec_add one_pos h1u (e ▸ inE_indec hβE))
  rw [h, add_zero]

/-- The code `ω^{υ_{λ+1}+1} = ϑ^{υ_{λ+1}}(1)` is the `ub 1 (th1 0)`-node. -/
theorem vrDec_top {l β : Ordinal.{0}} (hl0 : 0 < l) (hβ : 1 < β) (hu1 : upsilon (l + 1) < Om1)
    (hm2 : ω ^ (upsilon (l + 1) + 1) < upsilon (succ (l + 1))) :
    VrWF l β (.ub 1 (.th1 (.par 0))) ∧ vrVal l (.ub 1 (.th1 (.par 0))) = ω ^ (upsilon (l + 1) + 1) := by
  have huE : InE (upsilon (l + 1)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hO : (0 : Ordinal.{0}) < Om1 := lt_of_le_of_lt zero_le hu1
  have hev : UbT.ev (upsilon (l + 1)) (.th1 (.par 0)) = ω ^ (upsilon (l + 1) + 1) := vr_vt_one huE hu1
  refine ⟨⟨one_pos, hβ, trivial, ⟨trivial, hO⟩, vrLv_zero l β, ?_, hev ▸ hm2⟩, hev⟩
  rw [hev]; exact (lt_add_one _).le.trans (right_le_opow _ one_lt_omega0)

/-- **Every code `m ≤ ω^{υ_{λ+1}+1}` has a decomposition over `υ_{λ+1}`.** -/
theorem vrDec_code {l β m : Ordinal.{0}} (hl0 : 0 < l) (hβ : 1 < β) (hu1 : upsilon (l + 1) < Om1)
    (hm : m ≤ ω ^ (upsilon (l + 1) + 1)) : ∃ E : VrE, VrWF l β E ∧ vrVal l E = m := by
  have hmo := upsilon_normal.strictMono
  have huE : InE (upsilon (l + 1)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hu2E : InE (upsilon (succ (l + 1))) := upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ _)))
  have hu12 : upsilon (l + 1) < upsilon (succ (l + 1)) := hmo (lt_succ _)
  have htop : ω ^ (upsilon (l + 1) + 1) < upsilon (succ (l + 1)) :=
    hu2E.opow_lt (hu2E.add_lt hu12 (one_lt_omega0.trans_le (Vo.vo_omega_le huE (InE.pos huE)) |>.trans hu12))
  have hw : ω ^ (upsilon (l + 1) + 1) = upsilon (l + 1) * ω := by rw [opow_add_one, huE]
  rcases eq_or_lt_of_le hm with rfl | hlt
  · exact ⟨_, vrDec_top hl0 hβ hu1 htop⟩
  by_cases hlo : upsilon (l + 1) ≤ m
  · exact vrDec_mid hl0 hβ hlo (hw ▸ hlt) (hlt.trans htop)
  · exact vrDec_lo (by rw [succ_eq_add_one]; exact not_le.1 hlo)

/-- **Every ordinal `m < Ω₁` with no `ε`-number in `(u, m]` is the value over `u` of a countable-argument term with
leaves below `u`** (`u` a countable `ε`-number; `ϑ^u(1+s) = ω^{u+1+s}`, `R2.vt_wbar`, `R2.wbar_eq`; induction on `m`
through `m = ω^e + (m - ω^e)`). -/
theorem vrTerm_ex {u : Ordinal.{0}} (hu : InE u) (hu1 : u < Om1) :
    ∀ m, m < Om1 → (∀ e, u < e → e ≤ m → ¬ InE e) →
      ∃ t : UbT, UbT.IsA t ∧ UbT.WF u t ∧ UbT.Lv (· < u) t ∧ UbT.ev u t = m := by
  intro m
  induction m using WellFoundedLT.induction with
  | ind m IH =>
  intro hm1 hno
  rcases lt_trichotomy m u with hlt | rfl | hgt
  · exact ⟨.par m, trivial, trivial, hlt, rfl⟩
  · exact ⟨.base, trivial, trivial, trivial, rfl⟩
  have hm0 : m ≠ 0 := (lt_of_le_of_lt zero_le hgt).ne'
  set e := log ω m with he
  have hae : ω ^ e ≤ m := opow_log_le_self ω hm0
  have hsucc : m < ω ^ (e + 1) := by
    have := lt_opow_succ_log_self one_lt_omega0 m; rwa [succ_eq_add_one] at this
  set b := m - ω ^ e with hb
  have hab : ω ^ e + b = m := Ordinal.add_sub_cancel_of_le hae
  rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ b) with hb0 | hb0
  · -- `m = ω^e` is additive principal, `e > u`, `e = u + 1 + s`
    have hme : m = ω ^ e := by rw [← hab, ← hb0, add_zero]
    have hue : u < e := by
      have h : ω ^ u < ω ^ e := by rw [hu, ← hme]; exact hgt
      exact (opow_lt_opow_iff_right one_lt_omega0).1 h
    have hem : e ≤ m := hme ▸ right_le_opow e one_lt_omega0
    have heE : ¬ InE e := hno e hue hem
    have hem' : e < m := lt_of_le_of_ne hem fun h => heE (by unfold InE; rw [← hme, h])
    set s := e - (u + 1) with hs
    have hes : u + 1 + s = e := Ordinal.add_sub_cancel_of_le (Order.add_one_le_of_lt hue)
    have hsm : s < m := (le_add_self.trans_eq hes).trans_lt hem'
    obtain ⟨ts, hA, hW, hL, hev⟩ := IH s hsm (hsm.trans hm1) fun e' h1 h2 => hno e' h1 (h2.trans hsm.le)
    have hs1 : s < Om1 := hsm.trans hm1
    refine ⟨.th1 ts, hA, ⟨hW, hev ▸ hs1⟩, hL, ?_⟩
    show vt u (1 + UbT.ev u ts) = m
    rw [hev, vt_wbar hu hu1 hs1, wbar_eq hu s (fun β h1 h2 => hno β h1 (h2.trans (hes.trans_le hem))), hes, hme]
  · -- `m = ω^e + b` with both summands below `m`
    have hb1 : b < m := by
      refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun hbm => ?_
      have h : ω ^ e + m = m := by have h' := hab; rw [hbm] at h'; exact h'
      have h2 : ω ^ e * ω ≤ m := (add_eq_right_iff_mul_omega0_le).1 h
      rw [← opow_add_one] at h2
      exact absurd hsucc (not_lt.2 h2)
    have ha1 : ω ^ e < m := hab ▸ lt_add_of_pos_right _ hb0
    obtain ⟨ta, hAa, hWa, hLa, hea⟩ := IH _ ha1 (ha1.trans hm1) fun e' h1 h2 => hno e' h1 (h2.trans ha1.le)
    obtain ⟨tb, hAb, hWb, hLb, heb⟩ := IH _ hb1 (hb1.trans hm1) fun e' h1 h2 => hno e' h1 (h2.trans hb1.le)
    exact ⟨.add ta tb, ⟨hAa, hAb⟩, ⟨hWa, hWb⟩, ⟨hLa, hLb⟩, by show UbT.ev u ta + UbT.ev u tb = m; rw [hea, heb, hab]⟩

/-- **Every code `m ∈ [υ_{λ+1}, υ_{λ+2})` below the next `ε`-number above `υ_{λ+1}` has a decomposition over
`υ_{λ+1}`** (one `ub 1`-node, `vrTerm_ex`); codes below `υ_{λ+1}` are `lo`-nodes. -/
theorem vrDec_eps {l β m : Ordinal.{0}} (hl0 : 0 < l) (hβ : 1 < β) (hm1 : m < Om1)
    (hm2 : m < upsilon (succ (l + 1))) (hno : ∀ e, upsilon (l + 1) < e → e ≤ m → ¬ InE e) :
    ∃ E : VrE, VrWF l β E ∧ vrVal l E = m := by
  by_cases hlo : upsilon (l + 1) ≤ m
  · have huE : InE (upsilon (l + 1)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
    obtain ⟨t, hA, hW, hL, hev⟩ := vrTerm_ex huE (hlo.trans_lt hm1) m hm1 hno
    have hLv : UbT.Lv (vrLv l β) t := UbT.Lv_mono (fun p hp => Or.inl (by rw [succ_eq_add_one]; exact hp)) t hL
    exact ⟨.ub 1 t, ⟨one_pos, hβ, hA, hW, hLv, by rw [hev]; exact hlo, by rw [hev]; exact hm2⟩, hev⟩
  · exact vrDec_lo (by rw [succ_eq_add_one]; exact not_le.1 hlo)

/-! ## The repaired forms at `L(k)` -/

/-- **`VrForm` at every inner restart `a + z` of `a = L(k)` with `z < ω^{c+1}`** (`c = ω^{υ_{a+1}+1}`),
`z + ω + 1 < β`, given `L(k+1) ≤ ν_C`: `ub (z+ω+1) base + (the decomposition of the code)`. -/
theorem vrForm_inner (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {z β : Ordinal.{0}}
    (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z)
    (hzc : z < ω ^ (ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + 1)) (hzβ : z + ω + 1 < β) :
    VrForm S (Nc.ncL S (k : Ordinal.{0})) β z := by
  obtain ⟨hl0, hu1E, hu2E, hu12, hu2L1, -, hL1O, -, -⟩ := vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0})
  set u1 := upsilon (l + 1)
  have hu1O : u1 < Om1 := (hu12.trans hu2L1).trans hL1O
  have hc2 : ω ^ (u1 + 1) + 1 < upsilon (l + 2) :=
    hu2E.add_lt (hu2E.opow_lt (hu2E.add_lt hu12 (one_lt_omega0.trans_le (Vo.vo_omega_le hu2E (InE.pos hu2E)))))
      (one_lt_omega0.trans_le (Vo.vo_omega_le hu2E (InE.pos hu2E)))
  have hzu : z < upsilon (l + 2) := hzc.trans (hu2E.opow_lt hc2)
  have hβ1 : 1 < β := lt_of_le_of_lt (le_add_self) hzβ
  have hcode : cdCode S (l + z) ≤ ω ^ (u1 + 1) := by
    rw [Vo.voCode_add k (vr_omega_le hz0.ne' hzd) hzu]; exact vrExp_le hz0.ne' hzc
  obtain ⟨E, hW, hv⟩ := vrDec_code (β := β) hl0 hβ1 hu1O hcode
  have hh0 : 0 < z + ω + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  refine ⟨.add (.ub (z + ω + 1) .base) E, ⟨⟨hh0, hzβ, trivial, trivial, trivial, le_rfl,
    upsilon_normal.strictMono (lt_succ _)⟩, hW⟩, ?_⟩
  show upsilon (l + (z + ω + 1)) + vrVal l E = _
  rw [hv, vrR_inner k hν hz0 hzd hzu]

/-- **(B') at the inner restarts with codes below the next `ε`-number above `υ_{a+1}`**: for `0 < z < υ_{a+2}`,
`ω² | z`, `z + ω + 1 < β`, and no `ε`-number in `(υ_{a+1}, m_{a+z}]`, `VrForm S a β z` (given `L(k+1) ≤ ν_C`). -/
theorem vrForm_code (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {z β : Ordinal.{0}}
    (hz0 : 0 < z) (hzd : ω ^ 2 ∣ z) (hzu : z < upsilon (Nc.ncL S (k : Ordinal.{0}) + 2)) (hzβ : z + ω + 1 < β)
    (hno : ∀ e, upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) < e → e ≤ cdCode S (Nc.ncL S (k : Ordinal.{0}) + z) →
      ¬ InE e) :
    VrForm S (Nc.ncL S (k : Ordinal.{0})) β z := by
  obtain ⟨hl0, -, -, -, hu2L1, -, hL1O, -, -⟩ := vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0})
  have hβ1 : 1 < β := lt_of_le_of_lt (le_add_self) hzβ
  have hcz : cdCode S (l + z) ≤ z := by
    rw [Vo.voCode_add k (vr_omega_le hz0.ne' hzd) hzu]; exact (cdOff_le _).trans (Cp.cpExp_le hz0.ne')
  have hm2 : cdCode S (l + z) < upsilon (succ (l + 1)) := by
    rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]; exact hcz.trans_lt hzu
  obtain ⟨E, hW, hv⟩ := vrDec_eps (β := β) hl0 hβ1 (hm2.trans (by
    rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]; exact hu2L1.trans hL1O)) hm2 hno
  have hh0 : 0 < z + ω + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  refine ⟨.add (.ub (z + ω + 1) .base) E, ⟨⟨hh0, hzβ, trivial, trivial, trivial, le_rfl,
    upsilon_normal.strictMono (lt_succ _)⟩, hW⟩, ?_⟩
  show upsilon (l + (z + ω + 1)) + vrVal l E = _
  rw [hv, vrR_inner k hν hz0 hzd hzu]

/-- **The witness decomposition** `ub (g+ω+1) base + ub 1 (th1 0)`. -/
def vrEw (g : Ordinal.{0}) : VrE := .add (.ub (g + ω + 1) .base) (.ub 1 (.th1 (.par 0)))

/-- **The repaired form holds at the no-go witness of `Vo.voNoGo`**: with `g = ω^{ω^{υ_{a+1}+1}}`,
`r(a+g) = val (vrEw g)` and `vrEw g` is well formed for every `β ≥ g + ω + 2`. -/
theorem vrWit_form (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ : ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω + 2 ≤ β) :
    VrWF (Nc.ncL S (k : Ordinal.{0})) β (vrEw (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1))) ∧
      vrVal (Nc.ncL S (k : Ordinal.{0})) (vrEw (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1))) =
        cdR S (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1)) ∧
      cdR S (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1)) =
        upsilon (Nc.ncL S (k : Ordinal.{0}) + (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω + 1)) +
          ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) := by
  obtain ⟨hl0, hu1E, hu2E, hu12, hu2L1, -, hL1O, -, -⟩ := vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0})
  set u1 := upsilon (l + 1)
  set c := ω ^ (u1 + 1) with hc
  set g := ω ^ c with hg
  have hu1O : u1 < Om1 := (hu12.trans hu2L1).trans hL1O
  have hgβ : g + ω + 1 < β := lt_of_lt_of_le (add_lt_add_right one_lt_two (g + ω)) hβ
  have hβ1 : 1 < β := lt_of_le_of_lt le_add_self hgβ
  have hωu2 : ω ≤ upsilon (l + 2) := Vo.vo_omega_le hu2E (InE.pos hu2E)
  have hcu2 : c < upsilon (l + 2) := hu2E.opow_lt (hu2E.add_lt hu12 (one_lt_omega0.trans_le hωu2))
  have hgu2 : g < upsilon (l + 2) := hu2E.opow_lt hcu2
  have hωc : ω ≤ c := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u1))
  have h2c : (2 : Ordinal.{0}) ≤ c := ((natCast_lt_omega0 2).trans_le hωc).le
  have hgd : ω ^ 2 ∣ g := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
  have hg0 : 0 < g := opow_pos c omega0_pos
  have hcode : cdCode S (l + g) = c := by
    rw [Vo.voCode_add k (vr_omega_le hg0.ne' hgd) hgu2]
    have he : cdExp g = c := by have := Sf.sfCdExp_any 0 c; rwa [zero_add] at this
    rw [he]; unfold cdOff; rw [if_neg (not_lt.2 hωc)]
  have htop := vrDec_top (β := β) hl0 hβ1 hu1O (by rw [succ_eq_add_one, add_assoc, one_add_one_eq_two]; exact hcu2)
  have hh0 : 0 < g + ω + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  have hr : cdR S (l + g) = upsilon (l + (g + ω + 1)) + c := by rw [vrR_inner k hν hg0 hgd hgu2, hcode]
  refine ⟨⟨⟨hh0, hgβ, trivial, trivial, trivial, le_rfl, upsilon_normal.strictMono (lt_succ _)⟩, htop.1⟩, ?_, hr⟩
  show upsilon (l + (g + ω + 1)) + vrVal l (.ub 1 (.th1 (.par 0))) = _
  rw [htop.2, hr]

/-- **At the no-go witness the old forms fail and the repaired form holds** (`Vo.voForms_fail`, `vrWit_form`). -/
theorem vrWit_sep (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {β : Ordinal.{0}}
    (hβ : ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω + 2 ≤ β) :
    (¬ UbF3 S (Nc.ncL S (k : Ordinal.{0})) β (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1)) ∧
      ¬ UbForm S (Nc.ncL S (k : Ordinal.{0})) β (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1)) ∧
      ¬ Vl.VlGdForm S (Nc.ncL S (k : Ordinal.{0})) β (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1))) ∧
      VrForm S (Nc.ncL S (k : Ordinal.{0})) β (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1)) := by
  obtain ⟨hl0, hu1E, hu2E, hu12, hu2L1, hL1E, hL1O, hbelow, hωL1⟩ := vr_facts (S := S) k
  set l := Nc.ncL S (k : Ordinal.{0})
  set u1 := upsilon (l + 1)
  set c := ω ^ (u1 + 1) with hc
  set g := ω ^ c with hg
  obtain ⟨hW, hv, hr⟩ := vrWit_form (S := S) k hν hβ
  refine ⟨?_, ⟨_, hW, hv⟩⟩
  have hm := upsilon_normal.strictMono
  have hωu2 : ω ≤ upsilon (l + 2) := Vo.vo_omega_le hu2E (InE.pos hu2E)
  have hcu2 : c < upsilon (l + 2) := hu2E.opow_lt (hu2E.add_lt hu12 (one_lt_omega0.trans_le hωu2))
  have hgu2 : g < upsilon (l + 2) := hu2E.opow_lt hcu2
  have hωc : ω ≤ c := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u1))
  have hcg : c ≤ g := right_le_opow c one_lt_omega0
  have hlL1 : l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := Te.teL_lt_succ k
  have hτ : upsilon (l + 2) ≤ upsilon (l + (g + ω + 1)) :=
    hm.monotone ((add_le_add_iff_left l).2 ((((natCast_lt_omega0 2).trans_le hωc).le.trans hcg).trans
      (le_self_add.trans le_self_add)))
  have hglt : l + (g + ω + 1) < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := by
    rw [← add_assoc, ← add_assoc]
    exact hL1E.add_lt (hL1E.add_lt (hL1E.add_lt hlL1 (hgu2.trans hu2L1)) hωL1)
      (one_lt_omega0.trans hωL1)
  exact Vo.voForms_fail (S := S) hl0 hr (opow_succ_mem u1)
    (by rw [succ_eq_add_one]; exact (lt_add_one _).le.trans (right_le_opow _ one_lt_omega0))
    (hcu2.trans_le hτ) ((hbelow _ hglt).trans hL1O) hβ

/-- `z + ω² ≤ β` for multiples `z < β` of `ω²`. -/
theorem vr_dvd_step {z β : Ordinal.{0}} (hz : ω ^ 2 ∣ z) (hβ : ω ^ 2 ∣ β) (hzβ : z < β) : z + ω ^ 2 ≤ β := by
  obtain ⟨q, rfl⟩ := hz
  obtain ⟨q', rfl⟩ := hβ
  have hp : (0 : Ordinal.{0}) < ω ^ 2 := Vo.vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos
  have hq : q < q' := (mul_lt_mul_iff_right₀ hp).1 hzβ
  rw [← mul_add_one]
  exact (mul_le_mul_iff_right₀ hp).2 (Order.add_one_le_of_lt hq)

/-- **The window of the no-go witness**: at `β₀ = g + ω²·2`, `υ_{a+g+ω²} < υ_{a+β₀} < L(k+1)` and every inner
restart `a + z` (`0 < z < β₀`, `ω² | z`) has a repaired form. -/
theorem vrForms_win (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) :
    upsilon (Nc.ncL S (k : Ordinal.{0}) + ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2) <
      upsilon (Nc.ncL S (k : Ordinal.{0}) +
        (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2)) ∧
    upsilon (Nc.ncL S (k : Ordinal.{0}) + (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2)) <
      Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    ∀ z, 0 < z → z < ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2 → ω ^ 2 ∣ z →
      VrForm S (Nc.ncL S (k : Ordinal.{0})) (ω ^ ω ^ (upsilon (Nc.ncL S (k : Ordinal.{0}) + 1) + 1) + ω ^ 2 * 2) z := by
  obtain ⟨hl0, hu1E, hu2E, hu12, hu2L1, hL1E, hL1O, hbelow, hωL1⟩ := vr_facts (S := S) k
  have hm := upsilon_normal.strictMono
  set l := Nc.ncL S (k : Ordinal.{0})
  set u1 := upsilon (l + 1)
  set c := ω ^ (u1 + 1) with hc
  set g := ω ^ c with hg
  have hp : (0 : Ordinal.{0}) < ω ^ 2 := Vo.vo_e2 ▸ opow_pos (2 : Ordinal.{0}) omega0_pos
  have hωc : ω ≤ c := left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one u1))
  have h2c : (2 : Ordinal.{0}) ≤ c := ((natCast_lt_omega0 2).trans_le hωc).le
  have hgd : ω ^ 2 ∣ g := Vo.vo_e2 ▸ opow_dvd_opow ω h2c
  have hβd : ω ^ 2 ∣ g + ω ^ 2 * 2 := dvd_add hgd (dvd_mul_right _ _)
  have hωu2 : ω ≤ upsilon (l + 2) := Vo.vo_omega_le hu2E (InE.pos hu2E)
  have hcu2 : c < upsilon (l + 2) := hu2E.opow_lt (hu2E.add_lt hu12 (one_lt_omega0.trans_le hωu2))
  have hgu2 : g < upsilon (l + 2) := hu2E.opow_lt hcu2
  -- `ω²·2 < ω^{c+1}` and `g < ω^{c+1}`
  have hP : IsPrincipal (· + ·) (ω ^ (c + 1)) := isPrincipal_add_omega0_opow _
  have hgc1 : g < ω ^ (c + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one c)
  have h22 : ω ^ 2 * 2 < ω ^ (c + 1) := by
    have h3 : ω ^ 2 * 2 < ω ^ (3 : Ordinal.{0}) := by
      rw [show (3 : Ordinal.{0}) = 2 + 1 by norm_num, opow_add_one, Vo.vo_e2]
      exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (natCast_lt_omega0 2)
    refine h3.trans_le (opow_le_opow_right omega0_pos ?_)
    exact (((natCast_lt_omega0 3).trans_le hωc).le).trans le_self_add
  have hβc1 : g + ω ^ 2 * 2 < ω ^ (c + 1) := hP hgc1 h22
  have hc1u2 : ω ^ (c + 1) < upsilon (l + 2) :=
    hu2E.opow_lt (hu2E.add_lt hcu2 (one_lt_omega0.trans_le hωu2))
  have hlL1 : l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := Te.teL_lt_succ k
  refine ⟨hm ?_, hbelow _ (hL1E.add_lt hlL1 ((hβc1.trans hc1u2).trans hu2L1)), fun z hz0 hzβ hzd => ?_⟩
  · rw [add_assoc]
    refine (add_lt_add_iff_left l).2 ((add_lt_add_iff_left g).2 ?_)
    calc ω ^ 2 = ω ^ 2 * 1 := (mul_one _).symm
      _ < ω ^ 2 * 2 := (mul_lt_mul_iff_right₀ hp).2 one_lt_two
  · have hstep := vr_dvd_step hzd hβd hzβ
    have hω1 : ω + 1 < ω ^ 2 := (add_lt_add_right one_lt_two ω).trans Vo.vo_om2
    have hzβ' : z + ω + 1 < g + ω ^ 2 * 2 := by
      rw [add_assoc]; exact ((add_lt_add_iff_left z).2 hω1).trans_le hstep
    exact vrForm_inner k hν hz0 hzd (hzβ.trans hβc1) hzβ'

/-! ## EQ at the witness -/

/-- **The image of the witness decomposition** under an offset map `f` (`Sl.SlOff`): `υ_{μ+(f g+ω+1)} +
ω^{υ_{μ+1}+1}`. -/
theorem vrImg_wit {l μ g B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hB : Bases (upsilon μ) (upsilon l)) (hf : Sl.SlOff f Os B) (hgd : ω ^ 2 ∣ g) (hμ0 : 0 < μ)
    (hμ1 : upsilon (μ + 1) < Om1) :
    vrImg l μ f (vrEw g) = upsilon (μ + (f g + ω + 1)) + ω ^ (upsilon (μ + 1) + 1) := by
  have hf1 : f 1 = 1 := by
    have h1 : (1 : Ordinal.{0}) < ω ^ 2 := one_lt_omega0.trans (le_self_add.trans_lt Vo.vo_om2)
    have := hf.res 0 1 h1
    simpa [hf.zero] using this
  have hfg : f (g + ω + 1) = f g + ω + 1 := by
    obtain ⟨q, rfl⟩ := hgd
    have hr : ω + 1 < ω ^ 2 := (add_lt_add_right one_lt_two ω).trans Vo.vo_om2
    rw [add_assoc, hf.res q _ hr, add_assoc]
  have h0 : vrLf l μ f 0 = 0 := by
    have hs : (0 : Ordinal.{0}) < upsilon (succ l) := lt_of_le_of_lt zero_le
      (upsilon_normal.strictMono (lt_succ l) |>.trans_le' zero_le)
    simp only [vrLf, if_pos hs]
    exact pi_lt hB (InE.pos hB.1)
  have huE : InE (upsilon (μ + 1)) := upsPt_inE (upsPt_upsilon (hμ0.trans_le le_self_add))
  show UbT.ev (upsilon (μ + f (g + ω + 1))) (UbT.map (vrLf l μ f) .base) +
    UbT.ev (upsilon (μ + f 1)) (UbT.map (vrLf l μ f) (.th1 (.par 0))) = _
  simp only [UbT.map, UbT.ev, h0, hf1, hfg]
  rw [vr_vt_one huE hμ1]

/-- **The code of `μ + z`** for a restart `μ` below a name level: `m_{μ+z} = -1 + e(z)` for `ω ≤ z < υ_{μ+2}`
(`Cp.cpCode_add`). -/
theorem vrCode_mu {μ η1 z : Ordinal.{0}} (hμ0 : μ ≠ 0) (hn : upsilon (μ + 2) < Nm.Pv S η1) (hz : ω ≤ z)
    (hzu : z < upsilon (μ + 2)) : cdCode S (μ + z) = cdOff (cdExp z) := by
  have e2 : (2 : Ordinal.{0}) + z = z := by
    have := natCast_add_of_omega0_le hz 2; simpa using this
  have e : μ + z = μ + 2 + z := by rw [add_assoc, e2]
  rw [e]
  exact Cp.cpCode_add (ne_of_gt ((pos_iff_ne_zero.2 hμ0).trans_le le_self_add)) hn hzu
    (omega0_pos.trans_le hz).ne'

/-- **EQ at the witness**: if the offset map sends `g` to an offset `f(g) ∈ [ω, υ_{μ+2})` of last exponent
`ω^{υ_{μ+1}+1}` at a restart `μ` below a name level, with `υ_{μ+f g+ω+1} < ν_C`, then the image of the witness
decomposition is the reach: `vrImg (vrEw g) = r(μ + f(g))`. -/
theorem vrEQ_wit {l μ g B η1 : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hB : Bases (upsilon μ) (upsilon l)) (hf : Sl.SlOff f Os B) (hgd : ω ^ 2 ∣ g) (hμ : IsRestartIdx μ)
    (hμ1 : upsilon (μ + 1) < Om1) (hn : upsilon (μ + 2) < Nm.Pv S η1) (hfd : ω ^ 2 ∣ f g) (hω : ω ≤ f g)
    (hfu : f g < upsilon (μ + 2)) (hexp : cdExp (f g) = ω ^ (upsilon (μ + 1) + 1))
    (hC : upsilon (μ + f g + ω + 1) < nuC) :
    vrImg l μ f (vrEw g) = cdR S (μ + f g) := by
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
  have hm := upsilon_normal.strictMono
  have hcode : cdCode S (μ + f g) = ω ^ (upsilon (μ + 1) + 1) := by
    rw [vrCode_mu hμ.1 hn hω hfu, hexp]; unfold cdOff
    rw [if_neg (not_lt.2 (left_le_opow ω (lt_of_le_of_lt zero_le (lt_add_one _))))]
  have hR : IsRestartIdx (μ + f g) := ⟨(hμ0.trans_le le_self_add).ne', dvd_add hμ.2 hfd⟩
  have hle : cdCode S (μ + f g) ≤ upsilon (μ + f g) := by
    rw [vrCode_mu hμ.1 hn hω hfu]
    exact ((cdOff_le _).trans (Cp.cpExp_le (omega0_pos.trans_le hω).ne')).trans (le_add_self.trans hm.le_apply)
  rw [vrImg_wit hB hf hgd hμ0 hμ1, Vo.voR_low hR hC hle, hcode]
  unfold cdDelta; rw [add_assoc, add_assoc, add_assoc]

/-- **EQ at an inner restart with a low code reduces to moving the code**: for the decomposition
`ub (z+ω+1) base + E` of `r(λ+z)` and an offset map `f` sending `z` to `f(z) ∈ [ω, υ_{μ+2})` at a restart `μ` below
a name level (`υ_{μ+f z+ω+1} < ν_C`), the carry `img ≤ r(μ+f(z))` holds iff `img E ≤ -1 + e(f(z))`. -/
theorem vrEQ_code {l μ z B η1 : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}} (E : VrE)
    (hf : Sl.SlOff f Os B) (hzd : ω ^ 2 ∣ z) (hμ : IsRestartIdx μ) (hn : upsilon (μ + 2) < Nm.Pv S η1)
    (hfd : ω ^ 2 ∣ f z) (hω : ω ≤ f z) (hfu : f z < upsilon (μ + 2)) (hC : upsilon (μ + f z + ω + 1) < nuC) :
    vrImg l μ f (.add (.ub (z + ω + 1) .base) E) ≤ cdR S (μ + f z) ↔ vrImg l μ f E ≤ cdOff (cdExp (f z)) := by
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
  have hm := upsilon_normal.strictMono
  have hfz : f (z + ω + 1) = f z + ω + 1 := by
    obtain ⟨q, rfl⟩ := hzd
    have hr : ω + 1 < ω ^ 2 := (add_lt_add_right one_lt_two ω).trans Vo.vo_om2
    rw [add_assoc, hf.res q _ hr, add_assoc]
  have hcode := vrCode_mu (S := S) hμ.1 hn hω hfu
  have hR : IsRestartIdx (μ + f z) := ⟨(hμ0.trans_le le_self_add).ne', dvd_add hμ.2 hfd⟩
  have hle : cdCode S (μ + f z) ≤ upsilon (μ + f z) := by
    rw [hcode]
    exact ((cdOff_le _).trans (Cp.cpExp_le (omega0_pos.trans_le hω).ne')).trans (le_add_self.trans hm.le_apply)
  have hr : cdR S (μ + f z) = upsilon (μ + (f z + ω + 1)) + cdOff (cdExp (f z)) := by
    rw [Vo.voR_low hR hC hle, hcode]; unfold cdDelta; rw [add_assoc, add_assoc, add_assoc]
  show upsilon (μ + f (z + ω + 1)) + vrImg l μ f E ≤ _ ↔ _
  rw [hfz, hr]
  exact add_le_add_iff_left _

end Googology.Trans.PoR.InaccPsi.R2.Vr
