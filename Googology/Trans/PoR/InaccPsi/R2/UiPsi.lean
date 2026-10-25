import Googology.Trans.PoR.InaccPsi.R2.UiH
import Googology.Trans.PoR.InaccPsi.R2.TsRep
import Googology.Trans.PoR.InaccPsi.R2.GaAt

/-!
# The collapse `ψ_{Ω_{s+1}}` for every finite `s`: bounds, hull facts, own arguments

`ψ = S.psi · W`, `W = Ω_{s+1} = Om (s + 1)`, `L = Ω_s`; an argument `e` is *own* when `e ∈ Cl(e, ψ(e))`.  These are
the facts of `R2.TsFn`, `R2.TsOwn`, `R2.TsPsi`, `R2.TsRep` (`s = 1`) used by the hierarchy `H^s`, for every `s < ω`
(`s < ω` keeps `W` below every inaccessible of the sequence):

* `ui_s_mem`, `ui_W_mem` (**`W ∈ Cl(a, b)`**), `ui_W_lt_I`, `ui_W_lt_Iw`, `ui_W_opow`, `ui_W_indec`, `ui_W_mul_mem`
  (`W·β ∈ Cl(a, b)` for `β < b`), `ui_W_pow_mul_mem` (`W^γ·D ∈ Cl(a, b)` for `W·γ ∈ Cl(a, b)`, `D < b`);
* `ui_psi_lt`, `ui_L_lt_psi`, `ui_psi_SC`, `ui_psi_cases` (**every other collapse `ψ_π(e)` is `< L` or `≥ W`**),
  `ui_le_mod_add`, `ui_mod_mem` (**`Cl(a, b)` contains `W^m·(x / W^m)` with `x`**, `m ≥ 1`), `ui_psi_lt_of_own`,
  `ui_psi0_lt`;
* `ui_hull_coll`, `ui_own_below`, `ui_own_below_lt` (**own points below a collapse**), `ui_own_of_SC` (**every
  strongly critical `v ∈ (L, ψ(B))` is `ψ(e)` for an own `e`**), `ui_own_unique`, `ui_own_lt_iff`;
* `ui_base_below` (the largest fixed point of a normal `f` in `[τ, x)`, when `x` is not one).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-! ## `W = Ω_{s+1}` in the hulls -/

theorem ui_s_mem (hs : s < ω) (a b : Ordinal.{0}) : s ∈ S.CSet a b := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hs; exact Ga.ga_nat_mem a b n

/-- **`W ∈ Cl(a, b)`.** -/
theorem ui_W_mem (hs : s < ω) (a b : Ordinal.{0}) : Om (s + 1) ∈ S.CSet a b :=
  CSet.Om_mem (CSet.succ_mem (ui_s_mem hs a b))

theorem ui_s1_lt_omega (hs : s < ω) : s + 1 < ω := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hs
  have := natCast_lt_omega0 (n + 1)
  rwa [Nat.cast_succ] at this

theorem ui_W_lt_I (hs : s < ω) (n : ℕ) : Om (s + 1) < S.I n := by
  have h2 : s + 1 < S.I n := by
    refine (ui_s1_lt_omega hs).trans_le (le_trans (omega0_le_omega 1) ?_)
    have := Low.Om_one_le_I (S := S) n
    rwa [Om_of_ne_zero one_ne_zero] at this
  have h : Om (s + 1) < Om (S.I n) := Om_lt_Om.2 h2
  rwa [S.fix n] at h

theorem ui_W_lt_Iw (hs : s < ω) : Om (s + 1) < S.Iw :=
  (ui_W_lt_I (S := S) hs 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0)

theorem ui_W_opow (s : Ordinal.{0}) : ω ^ Om (s + 1) = Om (s + 1) := Gg.gg_SC_eps (ui_SC_W s)

theorem ui_W_indec' (s : Ordinal.{0}) : Indec (Om (s + 1)) := Lq.lq_SC_indec (ui_SC_W s)

/-- `W·β ∈ Cl(a, b)` for `β < b`. -/
theorem ui_W_mul_mem (hs : s < ω) {β a b : Ordinal.{0}} (hβ : β < b) : Om (s + 1) * β ∈ S.CSet a b := by
  have h := Nm.mem_opow_mul (S := S) (ui_W_mem (S := S) hs a b) hβ
  rwa [ui_W_opow] at h

/-! ## The collapse `ψ_W` -/

theorem ui_psi_lt (e : Ordinal.{0}) : S.psi e (Om (s + 1)) < Om (s + 1) := psi_lt (InR_Om_succ s) e

theorem ui_L_lt_psi (e : Ordinal.{0}) : Om s < S.psi e (Om (s + 1)) := (psiS_bounds e s).1

theorem ui_psi_SC (e : Ordinal.{0}) : SC (S.psi e (Om (s + 1))) := SC_psi (InR_Om_succ s) e

/-- **Every collapse `ψ_π(e)` with `π ≠ W` is below `L = Ω_s` or at least `W`.** -/
theorem ui_psi_cases (hs : s < ω) {π e : Ordinal.{0}} (hπ : S.InR π) (hπW : π ≠ Om (s + 1)) :
    S.psi e π < Om s ∨ Om (s + 1) ≤ S.psi e π := by
  rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
  · exact Or.inr (lt_psi_of_mem (InR_I n) (ui_W_mem hs _ _) (ui_W_lt_I hs n)).le
  · rcases lt_trichotomy t s with hts | hts | hts
    · left
      exact (psi_lt (InR_Om_succ t) e).trans_le (Om_le_Om.2 (Order.add_one_le_of_lt hts))
    · exact absurd (by rw [hts]) hπW
    · right
      exact ((Om_lt_psiS (S := S) e t).2 (Order.add_one_le_of_lt hts)).le

/-- `d ≤ (b + d) mod W` for `d < W`. -/
theorem ui_le_mod_add (b : Ordinal.{0}) {d : Ordinal.{0}} (hd : d < Om (s + 1)) : d ≤ (b + d) % Om (s + 1) := by
  have h0 : Om (s + 1) ≠ 0 := (ui_SC_W s).1.ne'
  have hr : b % Om (s + 1) + d < Om (s + 1) := (ui_W_indec' s).add_lt (Ordinal.mod_lt b h0) hd
  have e : b + d = Om (s + 1) * (b / Om (s + 1)) + (b % Om (s + 1) + d) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  exact le_add_self

/-- An additive principal `p ≥ W^m` is a multiple of `W^m`. -/
theorem ui_dvd_of_indec (m : Ordinal.{0}) {p : Ordinal.{0}} (hp : Indec p) (h : Om (s + 1) ^ m ≤ p) :
    Om (s + 1) ^ m ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  rw [ui_W_eq s m] at h ⊢
  have he : Om (s + 1) * m ≤ e := (opow_le_opow_iff_right one_lt_omega0).1 h
  exact ⟨ω ^ (e - Om (s + 1) * m), by rw [← opow_add, Ordinal.add_sub_cancel_of_le he]⟩

/-- **`Cl(a, b)` contains `W^m·(x / W^m)` with `x`** (`m ≥ 1`). -/
theorem ui_mod_mem {m : Ordinal.{0}} (hm : 1 ≤ m) {a b : Ordinal.{0}} :
    ∀ x, x ∈ S.CSet a b → Om (s + 1) ^ m * (x / Om (s + 1) ^ m) ∈ S.CSet a b := by
  set u := Om (s + 1) ^ m with hudef
  have h0 : u ≠ 0 := (ui_W_pos s m).ne'
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div, mul_zero]
    exact CSet.zero_mem _ _
  obtain ⟨hl, ht⟩ := lead_tail_mem hx hx0
  have hlt := lead_add_tail hx0
  rcases le_or_gt u (lead x) with h1 | h1
  · have hI : Indec (lead x) := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    obtain ⟨k', hk'⟩ := ui_dvd_of_indec m hI h1
    have ih := IH (tail x) (tail_lt hx0) ht
    have e2 : u * (x / u) = lead x + u * (tail x / u) := by
      conv_lhs => rw [← hlt, hk']
      rw [Ordinal.mul_add_div _ h0, mul_add, hk']
    rw [e2]
    exact CSet.add_mem hl ih
  · have hlim : IsSuccLimit (Om (s + 1) * m) :=
      isSuccLimit_mul_left (ui_SC_W s).isSuccLimit (lt_of_lt_of_le zero_lt_one hm)
    have hlog : Ordinal.log ω x < Om (s + 1) * m := by
      have := h1
      unfold lead at this
      rw [hudef, ui_W_eq s m] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have hxu : x < u := by
      refine (lt_opow_log_add_one x).trans ?_
      rw [hudef, ui_W_eq s m]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hlim.add_one_lt hlog)
    rw [Ordinal.div_eq_zero_of_lt hxu, mul_zero]
    exact CSet.zero_mem _ _

/-- `ψ(B) < ψ(B')` for an own `B < B'`. -/
theorem ui_psi_lt_of_own {B B' : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1)))) (h : B < B') :
    S.psi B (Om (s + 1)) < S.psi B' (Om (s + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ s) h ((psi_mono (S := S) (InR_Om_succ s) h.le).2 hown)

/-- `ψ(0) < ψ(B)` for every `B ≠ 0`. -/
theorem ui_psi0_lt {B : Ordinal.{0}} (hB0 : B ≠ 0) : S.psi 0 (Om (s + 1)) < S.psi B (Om (s + 1)) :=
  psi_lt_psi (InR_Om_succ s) (pos_iff_ne_zero.2 hB0) (CSet.zero_mem _ _)

/-! ## Own points below a collapse -/

/-- **A strongly critical `y` with `L < y < ψ(B)` is reached by a collapse**: some `e < B` in `Cl(B, y)` has
`y ≤ ψ(e)`. -/
theorem ui_hull_coll (hs : s < ω) {B y : Ordinal.{0}} (hy : SC y) (hy1 : Om s < y)
    (hyx : y < S.psi B (Om (s + 1))) :
    ∃ e, e < B ∧ e ∈ S.CSet B y ∧ y ≤ S.psi e (Om (s + 1)) := by
  by_contra hno
  push Not at hno
  have hgood : ∀ x ∈ S.CSet B y, x < Om (s + 1) → x < y := by
    intro x hx
    induction hx with
    | small h => exact fun _ => h
    | zero => exact fun _ => hy.1
    | inacc n => exact fun h => absurd (h.trans (ui_W_lt_I hs n)) (lt_irrefl _)
    | inaccW => exact fun h => absurd (h.trans (ui_W_lt_Iw hs)) (lt_irrefl _)
    | @add x z _ _ ihx ihz =>
      intro h
      exact hy.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihz (lt_of_le_of_lt le_add_self h))
    | @phi x z _ _ ihx ihz =>
      intro h
      exact hy.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x z) h)) _
        (ihz (lt_of_le_of_lt (right_le_veblen x z) h))
    | @om x _ _ =>
      intro h
      have hx2 : x < s + 1 := Om_lt_Om.1 h
      exact (Om_le_Om.2 (Order.lt_add_one_iff.1 hx2)).trans_lt hy1
    | @coll π e hπ _ heC _ _ =>
      intro h
      show S.psi e.1 π < y
      by_cases hπW : π = Om (s + 1)
      · subst hπW; exact hno e.1 e.2 heC
      · rcases ui_psi_cases (S := S) (e := e.1) hs hπ hπW with h' | h'
        · exact h'.trans hy1
        · exact absurd h (not_lt.2 h')
  have hle : S.psi B (Om (s + 1)) ≤ y := psi_le_of_good (ui_W_mem hs _ _) hgood
  exact absurd hyx (not_lt.2 hle)

/-- **Own points below a collapse**: for a strongly critical `y` with `L < y < ψ(B)` there is an own `e` with
`y ≤ ψ(e) < ψ(B)`. -/
theorem ui_own_below (hs : s < ω) {B y : Ordinal.{0}} (hy : SC y) (hy1 : Om s < y)
    (hyx : y < S.psi B (Om (s + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) ∧ y ≤ S.psi e (Om (s + 1)) ∧
      S.psi e (Om (s + 1)) < S.psi B (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  obtain ⟨e, heB, heC, hye⟩ := ui_hull_coll hs hy hy1 hyx
  have heC' : e ∈ S.CSet B (S.psi B (Om (s + 1))) := CSet_mono le_rfl hyx.le heC
  have hlt : S.psi e (Om (s + 1)) < S.psi B (Om (s + 1)) :=
    lt_psi_of_mem hκ (CSet.psi_mem heB hκ (mem_CSet_psi hκ B) heC') (psi_lt hκ _)
  obtain ⟨e', -, -, hown, heq⟩ := Ts.ts_norm hκ (Ts.ts_norm_of_lt hκ hlt)
  exact ⟨e', hown, heq ▸ hye, heq ▸ hlt⟩

/-- **Own points below an own collapse**: `e < B` as well. -/
theorem ui_own_below_lt (hs : s < ω) {B y : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (s + 1))))
    (hy : SC y) (hy1 : Om s < y) (hyx : y < S.psi B (Om (s + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) ∧ e < B ∧ y ≤ S.psi e (Om (s + 1)) ∧
      S.psi e (Om (s + 1)) < S.psi B (Om (s + 1)) := by
  obtain ⟨e, hown', hye, hlt⟩ := ui_own_below hs hy hy1 hyx
  refine ⟨e, hown', ?_, hye, hlt⟩
  have h := compare_psi (InR_Om_succ s) hown' hown
  rw [compare_lt_iff_lt.2 hlt] at h
  exact compare_lt_iff_lt.1 h.symm

/-- **A strongly critical `v` with `L < v < ψ(B)` is `ψ(e)` for an own `e`.** -/
theorem ui_own_of_SC (hs : s < ω) {v B : Ordinal.{0}} (hv : SC v) (hv1 : Om s < v)
    (hvB : v < S.psi B (Om (s + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (s + 1))) ∧ S.psi e (Om (s + 1)) = v := by
  set E : Set Ordinal.{0} := {e | e ∈ S.CSet e (S.psi e (Om (s + 1))) ∧ v ≤ S.psi e (Om (s + 1))} with hEdef
  have hne : E.Nonempty := by
    obtain ⟨e, hown, hve, -⟩ := ui_own_below hs hv hv1 hvB
    exact ⟨e, hown, hve⟩
  set e := sInf E with hedef
  have hmem : e ∈ E := csInf_mem hne
  refine ⟨e, hmem.1, le_antisymm (not_lt.1 fun hlt => ?_) hmem.2⟩
  obtain ⟨e', hown', he'e, hve', -⟩ := ui_own_below_lt hs hmem.1 hv hv1 hlt
  exact absurd (csInf_le' ⟨hown', hve'⟩ : e ≤ e') (not_le.2 he'e)

/-- `ψ(e) < ψ(e') ↔ e < e'` for own `e`, `e'`. -/
theorem ui_own_lt_iff {e e' : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (s + 1))))
    (hown' : e' ∈ S.CSet e' (S.psi e' (Om (s + 1)))) :
    S.psi e (Om (s + 1)) < S.psi e' (Om (s + 1)) ↔ e < e' := by
  have h := compare_psi (InR_Om_succ s) hown hown'
  rw [← compare_lt_iff_lt, h, compare_lt_iff_lt]

/-- **Own arguments with the same collapse are equal.** -/
theorem ui_own_unique {e e' : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (s + 1))))
    (hown' : e' ∈ S.CSet e' (S.psi e' (Om (s + 1)))) (h : S.psi e (Om (s + 1)) = S.psi e' (Om (s + 1))) :
    e = e' := by
  have hc := compare_psi (InR_Om_succ s) hown hown'
  rw [h] at hc
  have h2 : compare e e' = .eq := by rw [← hc]; exact compare_eq_iff_eq.2 rfl
  exact compare_eq_iff_eq.1 h2

/-! ## The largest fixed point below -/

/-- **The base below `x`** for a normal `f`: the largest fixed point of `f` in `(τ, x)`, or `τ`, when `x` is not a
fixed point. -/
theorem ui_base_below {f : Ordinal.{0} → Ordinal.{0}} (hf : Order.IsNormal f) {τ x : Ordinal.{0}} (hτx : τ < x)
    (hnf : f x ≠ x) :
    ∃ p, (p = τ ∨ (τ < p ∧ f p = p)) ∧ p < x ∧ ∀ q, f q = q → τ < q → q < x → q ≤ p := by
  set P : Set Ordinal.{0} := {q | q < x ∧ (q = τ ∨ (τ < q ∧ f q = q))} with hPdef
  have hτP : τ ∈ P := ⟨hτx, Or.inl rfl⟩
  have hPne : P.Nonempty := ⟨τ, hτP⟩
  have hPb : BddAbove P := ⟨x, fun q hq => hq.1.le⟩
  set p := sSup P with hpdef
  have hpx : p ≤ x := csSup_le hPne fun q hq => hq.1.le
  have hτp : τ ≤ p := le_csSup hPb hτP
  have hmax : ∀ q, f q = q → τ < q → q < x → q ≤ p := fun q hq hτq hqx =>
    le_csSup hPb ⟨hqx, Or.inr ⟨hτq, hq⟩⟩
  have hbase : p = τ ∨ (τ < p ∧ f p = p) := by
    by_cases hmem : p ∈ P
    · exact hmem.2
    right
    have hτp' : τ < p := lt_of_le_of_ne hτp fun e => hmem (e ▸ hτP)
    refine ⟨hτp', ?_⟩
    have hcof : ∀ a < p, ∃ g, a < g ∧ g < p ∧ τ < g ∧ f g = g := by
      intro a ha
      obtain ⟨g, hgP, hg⟩ := exists_lt_of_lt_csSup hPne (max_lt ha hτp')
      have hgp : g < p := lt_of_le_of_ne (le_csSup hPb hgP) fun e => hmem (e ▸ hgP)
      have hτg : τ < g := (le_max_right a τ).trans_lt hg
      rcases hgP.2 with e | ⟨-, hgg⟩
      · exact absurd e hτg.ne'
      · exact ⟨g, (le_max_left a τ).trans_lt hg, hgp, hτg, hgg⟩
    have hlim : IsSuccLimit p := by
      refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le hτp').ne', ?_⟩
      refine isSuccPrelimit_of_succ_lt fun a ha => ?_
      obtain ⟨g, hag, hgp, -⟩ := hcof a ha
      exact (Order.succ_le_of_lt hag).trans_lt hgp
    refine le_antisymm (not_lt.1 fun hlt => ?_) hf.strictMono.le_apply
    obtain ⟨b, hb, hpb⟩ := (hf.lt_iff_exists_lt hlim).1 hlt
    obtain ⟨g, hbg, hgp, -, hgg⟩ := hcof b hb
    have : f b < g := by rw [← hgg]; exact hf.strictMono hbg
    exact absurd (hpb.trans (this.trans hgp)) (lt_irrefl _)
  have hpx' : p < x := by
    refine lt_of_le_of_ne hpx fun e => ?_
    rcases hbase with h | ⟨-, h⟩
    · exact hτx.ne (h ▸ e)
    · exact hnf (e ▸ h)
  exact ⟨p, hbase, hpx', hmax⟩

end Googology.Trans.PoR.InaccPsi.R2.Ui
