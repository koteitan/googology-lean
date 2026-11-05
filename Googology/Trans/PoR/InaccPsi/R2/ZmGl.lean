import Googology.Trans.PoR.InaccPsi.R2.ZmNx

/-!
# ZmGl: THE GLOBAL READING OF THE CODES ABOVE `B_Γ` IN THE BRACKETS `[φ(1, B_Γ+ν), φ(1, B_Γ+ν+1))`

One recursion on the code `o`: below `B_Γ` the `Yr` reading; in the bracket of `ν` (`E = φ(1, B_Γ+ν) ≤ o < ε_{E+1}`)
`o = E^k·d + r` reads `φ(1, D(x)+ν)^{R(k)}·R(d) + R(r)`.  With it the readings of all the digit systems of the
chain agree, so a limit of the chain is a union (`Zm.ZmLm`).

* `zmD_fix` (**`D(x)` is a fixed point of `φ(1, ·)`**), `zm_glA_veb` (**`ϑˣ(Ω₁ + D(x) + t) = φ(1, D(x)+1+t)` for
  every `t < ε₀`**), `zmV` (`φ(1, D(x)+ν)`), `zmV_pi` (**Lemma EXACT for `φ(1, D(ρ)+ν)`, `ν < ε₀`**);
* `zmN`, `zmBE`, `zmN_eq`, `zmGR`, `zmGG`, `zmGR_lt`, `zmGG_lt`, `zmGR_cnf`, `zmGG_cnf`.

No new axiom.  New definitions: `zmV`, `zmN`, `zmBE`, `zmGR`, `zmGG`.
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

/-! ## `D(x)` and the `ε`-numbers above it -/

theorem zm_one_add_lt {s t : Ordinal.{0}} (hst : s < t) (hl : IsSuccLimit t) : 1 + s < t := by
  rcases lt_or_ge s ω with hω | hω
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this]
    exact (natCast_lt_omega0 _).trans_le (omega0_le_of_isSuccLimit hl)
  · rw [one_add_of_omega0_le hω]; exact hst

section DV

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **`D(x)` is a fixed point of `φ(1, ·)`.** -/
theorem zmD_fix : veblen 1 (ywV 1 0 x) = ywV 1 0 x := by
  obtain ⟨-, -, hDE⟩ := zgD_T hx hx1
  obtain ⟨-, -, hYC⟩ := ywD_closed hx hx1
  refine le_antisymm (((isNormal_veblen 1).le_iff_forall_le (ev_isSuccLimit_of_inE hDE)).2 fun y hy =>
    le_of_lt ?_) (right_le_veblen _ _)
  obtain ⟨n, hn⟩ := zgCofD hx hx1 hy
  have hN := yrR_N hx hx1 (yrTw_lt_BG n) (by rw [yrTw_g]; exact hx.pos)
  obtain ⟨htT, ht1⟩ := yr_T hN
  set t := yrR (yrTw n) x
  have htD : t < ywV 1 0 x := zgN_lt_D hx hx1 hN
  have htq : t < gq t x := gmq_gt hx hx1 htT ht1
  have h1q : (1 : Ordinal.{0}) < gq t x :=
    one_lt_omega0.trans (omega0_lt_inE (geq_facts hx hx1 htT ht1).2.2.2.1)
  calc veblen 1 y ≤ veblen 1 t := (isNormal_veblen 1).strictMono.monotone hn
    _ < veblen 1 (gq t x) := (isNormal_veblen 1).strictMono htq
    _ = gq t x := xk_fix hx hx1 htT ht1 le_rfl h1q
    _ < ywV 1 0 x := hYC t htT htD

theorem zmDt_T {t : Ordinal.{0}} (ht : t < ε₀) : ywV 1 0 x + t ∈ Tset x ∧ ywV 1 0 x + t < Om1 :=
  ⟨(zbDo_T hx hx1 ht).1, (zbDo_T hx hx1 ht).2.1⟩

/-- `D(x) + t` is not a fixed point of `φ(1, ·)` for `0 < t < ε₀`. -/
theorem zmDt_lt_veb {t : Ordinal.{0}} (ht0 : 0 < t) (ht : t < ε₀) :
    ywV 1 0 x + t < veblen 1 (ywV 1 0 x + t) := by
  obtain ⟨-, hxD, -, hDE⟩ := zmD_facts hx hx1
  refine lt_of_le_of_ne (right_le_veblen _ _) fun e => ?_
  have hE := zm_fix_E e.symm
  have hDlt : ywV 1 0 x < ywV 1 0 x + t := lt_add_of_pos_right _ ht0
  have h2 : ywV 1 0 x + ywV 1 0 x < ywV 1 0 x + t := (inE_indec hE).add_lt hDlt hDlt
  have htD : t < ywV 1 0 x := ht.trans_le ((gc_eps0_le hx).trans hxD.le)
  exact absurd ((add_lt_add_iff_left _).1 h2) (not_lt.2 htD.le)

/-- **`ϑˣ(Ω₁ + D(x) + t) = φ(1, D(x) + 1 + t)`** for every `t < ε₀`. -/
theorem zm_glA_veb : ∀ t, t < ε₀ → glA 1 (ywV 1 0 x + t) x = veblen 1 (ywV 1 0 x + 1 + t) := by
  obtain ⟨hDT, hxD, hD1, hDE⟩ := zmD_facts hx hx1
  obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro ht
  obtain ⟨htT, ht1⟩ := zmDt_T hx hx1 ht
  rcases zero_or_succ_or_isSuccLimit t with h0 | ⟨s, hs⟩ | hl
  · subst h0
    rw [add_zero, add_zero, ← zmD_eN hx hx1]
    conv_lhs => rw [← zmD_fix hx hx1]
    exact Go.go_eN_veb _
  · rw [succ_eq_add_one] at hs
    subst hs
    have hs : s < ε₀ := (lt_add_one s).trans ht
    obtain ⟨hsT, hs1⟩ := zmDt_T hx hx1 hs
    rw [← add_assoc, ← glA_eN_one hx hx1 hsT hs1, IH s (lt_add_one s) hs, Go.go_eN_veb, add_assoc,
      add_assoc]
  · have hωt : ω ≤ t := omega0_le_of_isSuccLimit hl
    have e1 : ywV 1 0 x + 1 + t = ywV 1 0 x + t := by rw [add_assoc, one_add_of_omega0_le hωt]
    rw [e1]
    refine le_antisymm ?_ ?_
    · have hu := luP_veblen 1 (ywV 1 0 x + t)
      have hxu : x < veblen 1 (ywV 1 0 x + t) :=
        (hxD.trans_le le_self_add).trans_le (right_le_veblen _ _)
      have htu := zmDt_lt_veb hx hx1 hl.bot_lt ht
      have h1u : (1 : Ordinal.{0}) < veblen 1 (ywV 1 0 x + t) :=
        one_lt_omega0.trans (omega0_lt_inE (zm_veb_E _))
      refine glA_min hx hx1 le_rfl h1T h11 htT ht1 hu hxu htu h1u fun σ hσ => ?_
      have hσT : σ ∈ Tset x := vz_T_down hx hx1 htT ht1 hσ.le
      rcases lt_or_ge σ (ywV 1 0 x) with hσD | hσD
      · have h0 := glA_lt_of hx hx1 le_rfl h1T h11 hσT hDT hD1 hσD
        have e0 := IH 0 hl.bot_lt (lt_of_le_of_lt zero_le ht)
        rw [add_zero, add_zero] at e0
        rw [e0] at h0
        exact h0.trans_le ((isNormal_veblen 1).strictMono.monotone
          (add_le_add_right (one_le_iff_pos.2 hl.bot_lt) _))
      · obtain ⟨s, rfl⟩ := exists_add_of_le hσD
        have hst : s < t := (add_lt_add_iff_left _).1 hσ
        rw [IH s hst (hst.trans ht)]
        exact (isNormal_veblen 1).strictMono (by
          rw [add_assoc]
          exact (add_lt_add_iff_left _).2 (zm_one_add_lt hst hl))
    · refine ((isNormal_veblen 1).le_iff_forall_le (isSuccLimit_add _ hl)).2 fun y hy => ?_
      rcases lt_or_ge y (ywV 1 0 x) with hyD | hyD
      · calc veblen 1 y ≤ veblen 1 (ywV 1 0 x) := (isNormal_veblen 1).strictMono.monotone hyD.le
          _ = ywV 1 0 x := zmD_fix hx hx1
          _ ≤ glA 1 (ywV 1 0 x + t) x := (le_self_add.trans (glA_facts hx hx1 le_rfl h1T h11 htT ht1).2.2.2.2.2.le)
      · obtain ⟨s, rfl⟩ := exists_add_of_le hyD
        have hst : s < t := (add_lt_add_iff_left _).1 hy
        obtain ⟨hsT, hs1⟩ := zmDt_T hx hx1 (hst.trans ht)
        calc veblen 1 (ywV 1 0 x + s) ≤ veblen 1 (ywV 1 0 x + 1 + s) :=
              (isNormal_veblen 1).strictMono.monotone (by rw [add_assoc]; exact add_le_add_right le_add_self _)
          _ = glA 1 (ywV 1 0 x + s) x := (IH s hst (hst.trans ht)).symm
          _ ≤ glA 1 (ywV 1 0 x + t) x :=
              (glA_lt_of hx hx1 le_rfl h1T h11 hsT htT ht1 ((add_lt_add_iff_left _).2 hst)).le

end DV

/-- **The reading `φ(1, D(x) + ν)` of the base `φ(1, B_Γ + ν)`.** -/
noncomputable def zmV (ν x : Ordinal.{0}) : Ordinal.{0} := veblen 1 (ywV 1 0 x + ν)

theorem zmV_glA {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {ν : Ordinal.{0}} (hν1 : 1 ≤ ν) (hν : ν < ε₀) :
    zmV ν x = glA 1 (ywV 1 0 x + (ν - 1)) x := by
  have h1 : ν - 1 < ε₀ := (sub_le_self ν 1).trans_lt hν
  rw [zm_glA_veb hx hx1 _ h1, add_assoc, Ordinal.add_sub_cancel_of_le hν1]; rfl

/-- **Lemma EXACT for `φ(1, D(ρ) + ν)`** (`ν < ε₀`). -/
theorem zmV_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) {ν : Ordinal.{0}} (hν : ν < ε₀) :
    zmV ν ρ ∈ TB ρ σ ∧ R2.pi σ ρ (zmV ν ρ) = zmV ν σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  rcases eq_or_ne ν 0 with rfl | hν0
  · unfold zmV
    rw [add_zero, add_zero, zmD_fix hB.2.1 hρ1, zmD_fix hB.1 hσ1]
    exact zmD_pi hB
  have hν1 : 1 ≤ ν := one_le_iff_ne_zero.2 hν0
  rw [zmV_glA hB.2.1 hρ1 hν1 hν, zmV_glA hB.1 hσ1 hν1 hν]
  have hνs : ν - 1 < σ := ((sub_le_self ν 1).trans_lt hν).trans_le (gc_eps0_le hB.1)
  obtain ⟨d1, d2⟩ := zmD_pi hB
  obtain ⟨s1, s2⟩ := pi_add hB d1 (mem_TB_of_lt hB hνs)
  rw [d2, pi_lt hB hνs] at s2
  obtain ⟨o1, o2⟩ := one_TB hB
  have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (zmDt_T hB.2.1 hρ1 ((sub_le_self ν 1).trans_lt hν)).2
  rw [o2, s2] at h
  exact h

/-! ## The bracket of a code and the global reading -/

/-- **The index of the bracket** `[φ(1, B_Γ+ν), φ(1, B_Γ+ν+1))` of `o`. -/
noncomputable def zmN (o : Ordinal.{0}) : Ordinal.{0} := sInf {n | o < veblen 1 (tfBG + (n + 1))}

/-- **The base of the bracket of `o`.** -/
noncomputable def zmBE (o : Ordinal.{0}) : Ordinal.{0} := veblen 1 (tfBG + zmN o)

theorem zmN_eq {o n : Ordinal.{0}} (h1 : veblen 1 (tfBG + n) ≤ o) (h2 : o < veblen 1 (tfBG + (n + 1))) :
    zmN o = n := by
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) h2) (le_csInf ⟨n, h2⟩ fun m hm => ?_)
  by_contra hmn
  push Not at hmn
  have : veblen 1 (tfBG + (m + 1)) ≤ veblen 1 (tfBG + n) :=
    (isNormal_veblen 1).strictMono.monotone (add_le_add_right (add_one_le_of_lt hmn) _)
  exact absurd (lt_of_lt_of_le hm (this.trans h1)) (lt_irrefl _)

theorem zmBE_eq {o n : Ordinal.{0}} (h1 : veblen 1 (tfBG + n) ≤ o) (h2 : o < veblen 1 (tfBG + (n + 1))) :
    zmBE o = veblen 1 (tfBG + n) := by
  unfold zmBE; rw [zmN_eq h1 h2]

open Classical in
/-- **THE GLOBAL READING**: `Yr` below `B_Γ`, `φ(1, D(x)+ν)^{R(k)}·R(d) + R(r)` in the bracket of `ν`. -/
noncomputable def zmGR (o x : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < tfBG then yrR o x
  else if h2 : log (zmBE o) o < o ∧ o / zmBE o ^ log (zmBE o) o < o ∧ o % zmBE o ^ log (zmBE o) o < o then
    zmV (zmN o) x ^ zmGR (log (zmBE o) o) x * zmGR (o / zmBE o ^ log (zmBE o) o) x +
      zmGR (o % zmBE o ^ log (zmBE o) o) x
  else o
termination_by o
decreasing_by
  all_goals first
    | exact h2.1
    | exact h2.2.1
    | exact h2.2.2

open Classical in
/-- **THE GLOBAL GATE.** -/
noncomputable def zmGG (o : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < tfBG then yrG o
  else if h2 : log (zmBE o) o < o ∧ o / zmBE o ^ log (zmBE o) o < o ∧ o % zmBE o ^ log (zmBE o) o < o then
    max (zmGG (log (zmBE o) o)) (max (zmGG (o / zmBE o ^ log (zmBE o) o)) (zmGG (o % zmBE o ^ log (zmBE o) o)))
  else 0
termination_by o
decreasing_by
  all_goals first
    | exact h2.1
    | exact h2.2.1
    | exact h2.2.2

theorem zmGR_lt {o : Ordinal.{0}} (h : o < tfBG) (x : Ordinal.{0}) : zmGR o x = yrR o x := by
  rw [zmGR, dif_pos h]

theorem zmGG_lt {o : Ordinal.{0}} (h : o < tfBG) : zmGG o = yrG o := by
  rw [zmGG, dif_pos h]

/-- The guards in the bracket of `ν`. -/
theorem zm_guards {o n : Ordinal.{0}} (h1 : veblen 1 (tfBG + n) ≤ o) (h2 : o < veblen 1 (tfBG + (n + 1))) :
    tfBG ≤ o ∧ zmBE o = veblen 1 (tfBG + n) ∧ zmN o = n ∧ (log (zmBE o) o < o ∧
      o / zmBE o ^ log (zmBE o) o < o ∧ o % zmBE o ^ log (zmBE o) o < o) := by
  have hE := zm_veb_E (tfBG + n)
  have hB : tfBG ≤ veblen 1 (tfBG + n) := le_self_add.trans (right_le_veblen _ _)
  have he := zmBE_eq h1 h2
  have h2' : o < eN (veblen 1 (tfBG + n)) := by rw [Go.go_eN_veb, add_assoc]; exact h2
  refine ⟨hB.trans h1, he, zmN_eq h1 h2, ?_⟩
  rw [he]
  exact ⟨zm_log_lt hE h1 h2', (div_opow_log_lt o (zm_E1 hE)).trans_le h1, zm_mod_lt hE h1⟩

theorem zmGR_cnf {o n : Ordinal.{0}} (h1 : veblen 1 (tfBG + n) ≤ o) (h2 : o < veblen 1 (tfBG + (n + 1)))
    (x : Ordinal.{0}) :
    zmGR o x = zmV n x ^ zmGR (log (veblen 1 (tfBG + n)) o) x *
      zmGR (o / veblen 1 (tfBG + n) ^ log (veblen 1 (tfBG + n)) o) x +
      zmGR (o % veblen 1 (tfBG + n) ^ log (veblen 1 (tfBG + n)) o) x := by
  obtain ⟨hB, he, hn, hg⟩ := zm_guards h1 h2
  rw [zmGR, dif_neg (not_lt.2 hB), dif_pos hg, he, hn]

theorem zmGG_cnf {o n : Ordinal.{0}} (h1 : veblen 1 (tfBG + n) ≤ o) (h2 : o < veblen 1 (tfBG + (n + 1))) :
    zmGG o = max (zmGG (log (veblen 1 (tfBG + n)) o))
      (max (zmGG (o / veblen 1 (tfBG + n) ^ log (veblen 1 (tfBG + n)) o))
        (zmGG (o % veblen 1 (tfBG + n) ^ log (veblen 1 (tfBG + n)) o))) := by
  obtain ⟨hB, he, hn, hg⟩ := zm_guards h1 h2
  rw [zmGG, dif_neg (not_lt.2 hB), dif_pos hg, he]

end Googology.Trans.PoR.InaccPsi.R2.Zm
