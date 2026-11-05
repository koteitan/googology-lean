import Googology.Trans.PoR.InaccPsi.R2.ZmPast

/-!
# ZmCx: THE GLOBAL READING WITH CODE INDICES BELOW `ζ_{B_Γ+1}`

The brackets `[φ(1, B_Γ+n), φ(1, B_Γ+n+1))` for every ordinal index `n`; below `ζ_{B_Γ+1} = φ(2, B_Γ+1)` the
index `n` of the bracket of `o ≥ B_Γ` is below `o` (`zmN_lt`), so it is itself read: `o = E^k·d + r` reads
`φ(1, D(x) + R(n)(x))^{R(k)}·R(d) + R(r)`, gate `max (G n) (max (G k) (max (G d) (G r)))`.

* `zmZ` (`φ(2, B_Γ+1)`), `zm_noFix` (**no fixed point of `φ(1, ·)` in `(B_Γ, ζ_{B_Γ+1})`**), `zm_bracket`;
* `zmD_fix2` (`φ(2, D(x)) = D(x)`), `zm_noFixD`, `zm_glA_veb2` (**`ϑˣ(Ω₁ + D(x) + t) = φ(1, D(x)+1+t)` for every `t`
  with `D(x) + t < ζ_{D(x)+1}`**), `zm_zeta_lt_gq`;
* `zmHR`, `zmHG`, `zmHR_lt`, `zmHG_lt`, `zmHR_cnf`, `zmHG_cnf`, `zmHG_idx`, `zmHG_le_succ`, `zmHG_succ_lt`.

No new axiom.  New definitions: `zmZ`, `zmHR`, `zmHG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk

/-! ## The bound `ζ_{B_Γ+1}` and the brackets below it -/

/-- **`ζ_{B_Γ+1} = φ(2, B_Γ+1)`.** -/
noncomputable def zmZ : Ordinal.{0} := veblen 2 (tfBG + 1)

theorem zm_veb2_fix (a : Ordinal.{0}) : veblen 1 (veblen 2 a) = veblen 2 a :=
  veblen_veblen_of_lt one_lt_two a

theorem zm_two_lt_BG : (2 : Ordinal.{0}) < tfBG := by exact_mod_cast zm_nat_lt_BG 2

theorem zm_BG_fix2 : veblen 2 tfBG = tfBG := tfBG_SC.veblen_right zm_two_lt_BG

/-- A fixed point of `φ(1, ·)` is a value of `φ(2, ·)`. -/
theorem zm_fix_range {y : Ordinal.{0}} (hy : veblen 1 y = y) : ∃ b, veblen 2 b = y := by
  have h := (mem_range_veblen (o := 2) (a := y) two_ne_zero).2 fun b hb => by
    have hb' : b < 1 + 1 := by rw [one_add_one_eq_two]; exact hb
    rcases (Order.lt_add_one_iff.1 hb').lt_or_eq with h0 | h1
    · rw [Order.lt_one_iff.1 h0, veblen_zero]; exact zm_fix_E hy
    · rw [h1]; exact hy
  exact h

/-- **No fixed point of `φ(1, ·)` strictly between `P = φ(2, P)` and `φ(2, P+1)`.** -/
theorem zm_noFix_gen {P y : Ordinal.{0}} (hP : veblen 2 P = P) (h1 : P < y) (h2 : y < veblen 2 (P + 1)) :
    veblen 1 y ≠ y := by
  intro hy
  obtain ⟨b, rfl⟩ := zm_fix_range hy
  rw [← hP] at h1
  have hb1 := (isNormal_veblen 2).strictMono.lt_iff_lt.1 h1
  have hb2 := (isNormal_veblen 2).strictMono.lt_iff_lt.1 h2
  exact absurd (Order.add_one_le_of_lt hb1) (not_le.2 hb2)

theorem zm_noFix {y : Ordinal.{0}} (h1 : tfBG < y) (h2 : y < zmZ) : veblen 1 y ≠ y :=
  zm_noFix_gen zm_BG_fix2 h1 h2

theorem zmZ_fix : veblen 1 zmZ = zmZ := zm_veb2_fix _

theorem zmZ_E : InE zmZ := zm_fix_E zmZ_fix

theorem zm_BG_lt_Z : tfBG < zmZ := by
  conv_lhs => rw [← zm_BG_fix2]
  exact (isNormal_veblen 2).strictMono (lt_add_one _)

theorem zmZ_lt_X : zmZ < tlX :=
  tlX_SC.2 2 (zm_two_lt_BG.trans tl_BG_lt_X) _
    ((ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC tlX_SC)).add_one_lt tl_BG_lt_X)

/-- `φ(1, B_Γ + c)` stays below `ζ_{B_Γ+1}` for `c < ζ_{B_Γ+1}`. -/
theorem zm_veb_lt_Z {c : Ordinal.{0}} (hc : c < zmZ) : veblen 1 (tfBG + c) < zmZ := by
  rw [← zmZ_fix]
  exact (isNormal_veblen 1).strictMono ((inE_indec zmZ_E).add_lt zm_BG_lt_Z hc)

/-- **An index below `ζ_{B_Γ+1}` is below its base**: `c < φ(1, B_Γ + c)`. -/
theorem zm_idx_lt {c : Ordinal.{0}} (hc : c < zmZ) : c < veblen 1 (tfBG + c) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, zm_BG_fix]; exact tfBG_SC.1
  refine lt_of_le_of_ne (le_add_self.trans (right_le_veblen _ _)) fun e => ?_
  have h2 : tfBG + c ≤ veblen 1 (tfBG + c) := right_le_veblen _ _
  have e1 : tfBG + c = c := le_antisymm (h2.trans_eq e.symm) le_add_self
  rw [e1] at e
  have hB : tfBG < c := by
    calc tfBG < tfBG + c := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hc0)
      _ = c := e1
  exact zm_noFix hB hc e.symm

/-- **The bracket of a code `B_Γ ≤ o < ζ_{B_Γ+1}`**: `φ(1, B_Γ + n) ≤ o < φ(1, B_Γ + n + 1)` with `n = zmN o < o`. -/
theorem zm_bracket {o : Ordinal.{0}} (h1 : tfBG ≤ o) (h2 : o < zmZ) :
    veblen 1 (tfBG + zmN o) ≤ o ∧ o < veblen 1 (tfBG + (zmN o + 1)) ∧ zmN o < o := by
  have hne : o ∈ {n | o < veblen 1 (tfBG + (n + 1))} :=
    (zm_idx_lt h2).trans ((isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one o)))
  have hmem : o < veblen 1 (tfBG + (zmN o + 1)) := csInf_mem (s := {n | o < veblen 1 (tfBG + (n + 1))}) ⟨o, hne⟩
  have hle : ∀ m, o < veblen 1 (tfBG + (m + 1)) → zmN o ≤ m := fun m hm => csInf_le (OrderBot.bddBelow _) hm
  have hlow : veblen 1 (tfBG + zmN o) ≤ o := by
    by_contra hc
    push Not at hc
    rcases zero_or_succ_or_isSuccLimit (zmN o) with h0 | ⟨m, hm⟩ | hl
    · rw [h0, add_zero, zm_BG_fix] at hc; exact absurd h1 (not_le.2 hc)
    · rw [succ_eq_add_one] at hm
      rw [← hm] at hc
      exact absurd (hle m hc) (not_le.2 (hm ▸ lt_add_one m))
    · obtain ⟨c', hc', hoc'⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
      have hm : ∃ m, m < zmN o ∧ o < veblen 1 (tfBG + (m + 1)) := by
        rcases lt_or_ge c' tfBG with h | h
        · refine ⟨0, hl.bot_lt, hoc'.trans ((isNormal_veblen 1).strictMono ?_)⟩
          exact h.trans_le (le_self_add.trans_eq (by rw [zero_add]))
        · obtain ⟨m, rfl⟩ := exists_add_of_le h
          exact ⟨m, (add_lt_add_iff_left _).1 hc',
            hoc'.trans ((isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one m)))⟩
      obtain ⟨m, hmn, hom⟩ := hm
      exact absurd (hle m hom) (not_le.2 hmn)
  refine ⟨hlow, hmem, ?_⟩
  by_contra hc
  push Not at hc
  have := (isNormal_veblen 1).strictMono.monotone (add_le_add_right hc tfBG)
  exact absurd (hlow.trans_lt' (lt_of_lt_of_le (zm_idx_lt h2) this)) (lt_irrefl _)

/-! ## `D(x)` and `ζ_{D(x)+1}` -/

section DZ

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`D(x)` is a fixed point of `φ(2, ·)`.** -/
theorem zmD_fix2 : veblen 2 (ywV 1 0 x) = ywV 1 0 x := by
  obtain ⟨-, -, hDE⟩ := zgD_T hx hx1
  obtain ⟨-, -, hYC⟩ := ywD_closed hx hx1
  refine le_antisymm (((isNormal_veblen 2).le_iff_forall_le (ev_isSuccLimit_of_inE hDE)).2 fun y hy =>
    le_of_lt ?_) (right_le_veblen _ _)
  obtain ⟨n, hn⟩ := zgCofD hx hx1 hy
  have hN := yrR_N hx hx1 (yrTw_lt_BG n) (by rw [yrTw_g]; exact hx.pos)
  obtain ⟨htT, ht1⟩ := yr_T hN
  set t := yrR (yrTw n) x
  have htD : t < ywV 1 0 x := zgN_lt_D hx hx1 hN
  have htq : t < gq t x := gmq_gt hx hx1 htT ht1
  have h2q : (2 : Ordinal.{0}) < gq t x := by
    have := (natCast_lt_omega0 2).trans (omega0_lt_inE (geq_facts hx hx1 htT ht1).2.2.2.1)
    exact_mod_cast this
  calc veblen 2 y ≤ veblen 2 t := (isNormal_veblen 2).strictMono.monotone hn
    _ < veblen 2 (gq t x) := (isNormal_veblen 2).strictMono htq
    _ = gq t x := xk_fix hx hx1 htT ht1 one_le_two h2q
    _ < ywV 1 0 x := hYC t htT htD

/-- `ζ_{D(x)+1} < gq(D(x)+1)`. -/
theorem zm_zeta_lt_gq : veblen 2 (ywV 1 0 x + 1) < gq (ywV 1 0 x + 1) x := by
  obtain ⟨hDT1, hD11, -⟩ := zbDo_T hx hx1 (o := 1) (one_lt_omega0.trans_le (omega0_le_of_isSuccLimit gc_eps0_lim))
  obtain ⟨hDq, -, -, -, -⟩ := zm_gq_facts hx hx1
  have h2q : (2 : Ordinal.{0}) < gq (ywV 1 0 x + 1) x := by
    have := (natCast_lt_omega0 2).trans (omega0_lt_inE (geq_facts hx hx1 hDT1 hD11).2.2.2.1)
    exact_mod_cast this
  have hfix := xk_fix hx hx1 hDT1 hD11 one_le_two h2q
  calc veblen 2 (ywV 1 0 x + 1) < veblen 2 (gq (ywV 1 0 x + 1) x) :=
        (isNormal_veblen 2).strictMono (gmq_gt hx hx1 hDT1 hD11)
    _ = _ := hfix

theorem zmDZ_T {t : Ordinal.{0}} (ht : ywV 1 0 x + t < veblen 2 (ywV 1 0 x + 1)) :
    ywV 1 0 x + t ∈ Tset x ∧ ywV 1 0 x + t < Om1 := by
  obtain ⟨-, hqT, hq1, -, -⟩ := zm_gq_facts hx hx1
  have h := ht.trans (zm_zeta_lt_gq hx hx1)
  exact ⟨vz_T_down hx hx1 hqT hq1 h.le, h.trans hq1⟩

/-- **`ϑˣ(Ω₁ + D(x) + t) = φ(1, D(x) + 1 + t)`** for every `t` with `D(x) + t < ζ_{D(x)+1}`. -/
theorem zm_glA_veb2 : ∀ t, ywV 1 0 x + t < veblen 2 (ywV 1 0 x + 1) →
    glA 1 (ywV 1 0 x + t) x = veblen 1 (ywV 1 0 x + 1 + t) := by
  obtain ⟨hDT, hxD, hD1, hDE⟩ := zmD_facts hx hx1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  have hDf2 := zmD_fix2 hx hx1
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro ht
  obtain ⟨htT, ht1⟩ := zmDZ_T hx hx1 ht
  rcases zero_or_succ_or_isSuccLimit t with h0 | ⟨s, hs⟩ | hl
  · subst h0
    rw [add_zero, add_zero, ← zmD_eN hx hx1]
    conv_lhs => rw [← zmD_fix hx hx1]
    exact Go.go_eN_veb _
  · rw [succ_eq_add_one] at hs
    subst hs
    have hs : ywV 1 0 x + s < veblen 2 (ywV 1 0 x + 1) :=
      lt_of_le_of_lt (add_le_add_right (lt_add_one s).le _) ht
    obtain ⟨hsT, hs1⟩ := zmDZ_T hx hx1 hs
    rw [← add_assoc, ← glA_eN_one hx hx1 hsT hs1, IH s (lt_add_one s) hs, Go.go_eN_veb, add_assoc,
      add_assoc]
  · have hωt : ω ≤ t := omega0_le_of_isSuccLimit hl
    have e1 : ywV 1 0 x + 1 + t = ywV 1 0 x + t := by rw [add_assoc, one_add_of_omega0_le hωt]
    rw [e1]
    have hnf : ywV 1 0 x + t < veblen 1 (ywV 1 0 x + t) := by
      refine lt_of_le_of_ne (right_le_veblen _ _) fun e => ?_
      exact zm_noFix_gen hDf2 (lt_add_of_pos_right _ hl.bot_lt) ht e.symm
    refine le_antisymm ?_ ?_
    · have hu := luP_veblen 1 (ywV 1 0 x + t)
      have hxu : x < veblen 1 (ywV 1 0 x + t) :=
        (hxD.trans_le le_self_add).trans_le (right_le_veblen _ _)
      have h1u : (1 : Ordinal.{0}) < veblen 1 (ywV 1 0 x + t) :=
        one_lt_omega0.trans (omega0_lt_inE (zm_veb_E _))
      refine glA_min hx hx1 le_rfl h1T h11 htT ht1 hu hxu hnf h1u fun σ hσ => ?_
      have hσT : σ ∈ Tset x := vz_T_down hx hx1 htT ht1 hσ.le
      rcases lt_or_ge σ (ywV 1 0 x) with hσD | hσD
      · have h0 := glA_lt_of hx hx1 le_rfl h1T h11 hσT hDT hD1 hσD
        have e0 := IH 0 hl.bot_lt (lt_of_le_of_lt (add_le_add_right zero_le _) ht)
        rw [add_zero, add_zero] at e0
        rw [e0] at h0
        exact h0.trans_le ((isNormal_veblen 1).strictMono.monotone
          (add_le_add_right (one_le_iff_pos.2 hl.bot_lt) _))
      · obtain ⟨s, rfl⟩ := exists_add_of_le hσD
        have hst : s < t := (add_lt_add_iff_left _).1 hσ
        rw [IH s hst (lt_of_le_of_lt (add_le_add_right hst.le _) ht)]
        exact (isNormal_veblen 1).strictMono (by
          rw [add_assoc]
          exact (add_lt_add_iff_left _).2 (zm_one_add_lt hst hl))
    · refine ((isNormal_veblen 1).le_iff_forall_le (isSuccLimit_add _ hl)).2 fun y hy => ?_
      rcases lt_or_ge y (ywV 1 0 x) with hyD | hyD
      · calc veblen 1 y ≤ veblen 1 (ywV 1 0 x) := (isNormal_veblen 1).strictMono.monotone hyD.le
          _ = ywV 1 0 x := zmD_fix hx hx1
          _ ≤ glA 1 (ywV 1 0 x + t) x :=
              (le_self_add.trans (glA_facts hx hx1 le_rfl h1T h11 htT ht1).2.2.2.2.2.le)
      · obtain ⟨s, rfl⟩ := exists_add_of_le hyD
        have hst : s < t := (add_lt_add_iff_left _).1 hy
        have hs : ywV 1 0 x + s < veblen 2 (ywV 1 0 x + 1) := lt_of_le_of_lt (add_le_add_right hst.le _) ht
        obtain ⟨hsT, hs1⟩ := zmDZ_T hx hx1 hs
        calc veblen 1 (ywV 1 0 x + s) ≤ veblen 1 (ywV 1 0 x + 1 + s) :=
              (isNormal_veblen 1).strictMono.monotone (by rw [add_assoc]; exact add_le_add_right le_add_self _)
          _ = glA 1 (ywV 1 0 x + s) x := (IH s hst hs).symm
          _ ≤ glA 1 (ywV 1 0 x + t) x :=
              (glA_lt_of hx hx1 le_rfl h1T h11 hsT htT ht1 ((add_lt_add_iff_left _).2 hst)).le

end DZ

/-! ## The global reading with code indices -/

open Classical in
/-- **THE GLOBAL READING WITH CODE INDICES**: `Yr` below `B_Γ`; in the bracket of `n` (`n < o`)
`φ(1, D(x) + R(n))^{R(k)}·R(d) + R(r)`. -/
noncomputable def zmHR (o x : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < tfBG then yrR o x
  else if h2 : zmN o < o ∧ log (zmBE o) o < o ∧ o / zmBE o ^ log (zmBE o) o < o ∧
      o % zmBE o ^ log (zmBE o) o < o then
    veblen 1 (ywV 1 0 x + zmHR (zmN o) x) ^ zmHR (log (zmBE o) o) x * zmHR (o / zmBE o ^ log (zmBE o) o) x +
      zmHR (o % zmBE o ^ log (zmBE o) o) x
  else o
termination_by o
decreasing_by
  all_goals first
    | exact h2.1
    | exact h2.2.1
    | exact h2.2.2.1
    | exact h2.2.2.2

open Classical in
/-- **THE GLOBAL GATE WITH CODE INDICES** (the gate of the index included). -/
noncomputable def zmHG (o : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < tfBG then yrG o
  else if h2 : zmN o < o ∧ log (zmBE o) o < o ∧ o / zmBE o ^ log (zmBE o) o < o ∧
      o % zmBE o ^ log (zmBE o) o < o then
    max (zmHG (zmN o)) (max (zmHG (log (zmBE o) o)) (max (zmHG (o / zmBE o ^ log (zmBE o) o))
      (zmHG (o % zmBE o ^ log (zmBE o) o))))
  else 0
termination_by o
decreasing_by
  all_goals first
    | exact h2.1
    | exact h2.2.1
    | exact h2.2.2.1
    | exact h2.2.2.2

theorem zmHR_lt {o : Ordinal.{0}} (h : o < tfBG) (x : Ordinal.{0}) : zmHR o x = yrR o x := by
  rw [zmHR, dif_pos h]

theorem zmHG_lt {o : Ordinal.{0}} (h : o < tfBG) : zmHG o = yrG o := by
  rw [zmHG, dif_pos h]

theorem zm_guards2 {o : Ordinal.{0}} (h1 : tfBG ≤ o) (h2 : o < zmZ) :
    zmBE o = veblen 1 (tfBG + zmN o) ∧ (zmN o < o ∧ log (zmBE o) o < o ∧
      o / zmBE o ^ log (zmBE o) o < o ∧ o % zmBE o ^ log (zmBE o) o < o) := by
  obtain ⟨b1, b2, b3⟩ := zm_bracket h1 h2
  obtain ⟨-, he, -, hg⟩ := zm_guards b1 b2
  exact ⟨he, b3, hg⟩

/-- **The unfolding in the bracket of `n = zmN o`.** -/
theorem zmHR_cnf {o : Ordinal.{0}} (h1 : tfBG ≤ o) (h2 : o < zmZ) (x : Ordinal.{0}) :
    zmHR o x = veblen 1 (ywV 1 0 x + zmHR (zmN o) x) ^ zmHR (log (zmBE o) o) x *
      zmHR (o / zmBE o ^ log (zmBE o) o) x + zmHR (o % zmBE o ^ log (zmBE o) o) x := by
  obtain ⟨-, hg⟩ := zm_guards2 h1 h2
  rw [zmHR, dif_neg (not_lt.2 h1), dif_pos hg]

theorem zmHG_cnf {o : Ordinal.{0}} (h1 : tfBG ≤ o) (h2 : o < zmZ) :
    zmHG o = max (zmHG (zmN o)) (max (zmHG (log (zmBE o) o)) (max (zmHG (o / zmBE o ^ log (zmBE o) o))
      (zmHG (o % zmBE o ^ log (zmBE o) o)))) := by
  obtain ⟨-, hg⟩ := zm_guards2 h1 h2
  rw [zmHG, dif_neg (not_lt.2 h1), dif_pos hg]

/-- **The gate of a code bounds the gate of the index of its bracket.** -/
theorem zmHG_idx {o : Ordinal.{0}} (h1 : tfBG ≤ o) (h2 : o < zmZ) : zmHG (zmN o) ≤ zmHG o := by
  rw [zmHG_cnf h1 h2]; exact le_max_left _ _

/-- The bracket of `o + 1` is that of `o`, with the rest `r + 1`. -/
theorem zm_succ_dec {o : Ordinal.{0}} (h1 : tfBG ≤ o) (h2 : o < zmZ) :
    tfBG ≤ o + 1 ∧ o + 1 < zmZ ∧ zmN (o + 1) = zmN o ∧ zmBE (o + 1) = zmBE o ∧
      log (zmBE o) (o + 1) = log (zmBE o) o ∧
      (o + 1) / zmBE o ^ log (zmBE o) o = o / zmBE o ^ log (zmBE o) o ∧
      (o + 1) % zmBE o ^ log (zmBE o) o = o % zmBE o ^ log (zmBE o) o + 1 ∧
      o % zmBE o ^ log (zmBE o) o < o := by
  obtain ⟨b1, b2, -⟩ := zm_bracket h1 h2
  have hE := zm_veb_E (tfBG + zmN o)
  have hEeq := zmBE_eq b1 b2
  have hEo : zmBE o ≤ o := hEeq ▸ b1
  have hEE : InE (zmBE o) := hEeq ▸ hE
  have hb2' : o + 1 < veblen 1 (tfBG + (zmN o + 1)) := (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt b2
  have hN1 : zmN (o + 1) = zmN o := zmN_eq (b1.trans (lt_add_one o).le) hb2'
  have hZ1 : o + 1 < zmZ := (ev_isSuccLimit_of_inE zmZ_E).add_one_lt h2
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec hEE hEo
  set E := zmBE o
  set k := log E o
  set d := o / E ^ k
  set r := o % E ^ k
  have hr1 : r + 1 < E ^ k := zm_opow_prin hEE k hrk (zm_one_lt_opow hEE hk0)
  obtain ⟨u1, u2, u3⟩ := zm_dec_uniq hEE hd0.ne' hdE hr1
  have e : o + 1 = E ^ k * d + (r + 1) := by rw [← add_assoc, hdec]
  have hBE1 : zmBE (o + 1) = E := by
    show veblen 1 (tfBG + zmN (o + 1)) = E
    rw [hN1]; exact hEeq.symm
  refine ⟨h1.trans (lt_add_one o).le, hZ1, hN1, hBE1, ?_, ?_, ?_, zm_mod_lt hEE hEo⟩
  · rw [e]; exact u1
  · rw [e]; have := u2; rwa [u1] at this
  · rw [e]; have := u3; rwa [u1] at this

theorem zmHG_le_succ : ∀ o, o < zmZ → zmHG o ≤ zmHG (o + 1) := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoZ
  rcases lt_or_ge o tfBG with hoB | hoB
  · rw [zmHG_lt hoB, zmHG_lt (zgBG_lim.add_one_lt hoB)]; exact yrG_le_succ o
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hro⟩ := zm_succ_dec hoB hoZ
  rw [zmHG_cnf hoB hoZ, zmHG_cnf s1 s2, s3, s4, s5, s6, s7]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (IH _ hro (hro.trans hoZ))))

theorem zmHG_succ_lt : ∀ o, o < zmZ → ∀ Z, IsSuccLimit Z → zmHG o < Z → zmHG (o + 1) < Z := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoZ Z hZ hg
  rcases lt_or_ge o tfBG with hoB | hoB
  · rw [zmHG_lt hoB] at hg; rw [zmHG_lt (zgBG_lim.add_one_lt hoB)]; exact yrG_succ hZ o hg
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hro⟩ := zm_succ_dec hoB hoZ
  rw [zmHG_cnf hoB hoZ] at hg
  rw [zmHG_cnf s1 s2, s3, s4, s5, s6, s7]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (max_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt hg))) (IH _ hro (hro.trans hoZ) Z hZ ((le_max_right _ _).trans_lt
        ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))))

theorem zmHR_succ : ∀ o, o < zmZ → ∀ x, zmHR (o + 1) x = zmHR o x + 1 := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoZ x
  rcases lt_or_ge o tfBG with hoB | hoB
  · rw [zmHR_lt hoB, zmHR_lt (zgBG_lim.add_one_lt hoB), yrR_succ]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hro⟩ := zm_succ_dec hoB hoZ
  rw [zmHR_cnf hoB hoZ, zmHR_cnf s1 s2, s3, s4, s5, s6, s7, IH _ hro (hro.trans hoZ), add_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Zm
