import Googology.Trans.PoR.InaccPsi.R2.GnHC

/-!
# HEREDITARY CODES TO THE BASE `Γ_{Ω₁+1}`: gates and hulls

The port of `R2.GjHG` to the base `G = Γ_{Ω₁+1}` (digits read by `Gl.glR`, gated by `Gl.glG`):

* `gnG_lt_Om1`, `gnG_of_Q`, `gn_add` (**the gate of a sum**), `gn_div` (**`y/G` and `y mod G` keep the gate of a code
  `y ≥ G`**), `gn_parts_g`, `gn_code_gate` (**a code below `ε_{G+1}` over `Z` with the atoms `Γ_{Ω₁+1+c'}`
  (`c' < ε_{G+1}`, gate below `Z`) has its gate below `Z`**: the only atom below `ε_{G+1}` is `G` itself, `ω^y` with
  `y ∈ [G, ε_{G+1})` is `G^{y/G}·ω^{y mod G}`, the only `ε`-number in `[G, ε_{G+1})` is `G`);
* `gnR_pos`, `gn_omega_le_gnR`, `gnR_one_add`, `gn_mulG` (**`G·k` is a code with `(G·k)(x) = Γ_{x+1}·k(x)` and gate
  at most that of `k`**), `gn_mulG_lt_pow`;
* `gn_veb_fix`, `gnB_eq` (`ε_{G+1} = φ(1, G+1)`), `gn_mem` (**every code lies in every hull `Cl(a, b)`, `a > 0`,
  containing its gate**), `gnB_mem`, `gnG_succ`, `gnG_le_succ`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

theorem gnG_lt_Om1 : ∀ c, c < gnB → gnG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE]; exact glG_lt_Om1 c hcE
  obtain ⟨-, -, hdE, -, -, hlc, hrc⟩ := gn_parts hcE hc
  rw [gnG_dec hcE hc]
  exact max_lt (max_lt ((gnQ_le _).trans_lt (IH _ hlc (hlc.trans hc)))
    ((glQ_le _).trans_lt (glG_lt_Om1 _ hdE))) (IH _ hrc (hrc.trans hc))

/-- The gate of a code below `Z > ω` from the gate of it as an exponent. -/
theorem gnG_of_Q {k Z : Ordinal.{0}} (hωZ : ω < Z) (h : gnQ k < Z) : gnG k < Z := by
  unfold gnQ at h
  split_ifs at h with hk
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hk
    rw [gnG_nat]
    exact (natCast_lt_omega0 n).trans hωZ
  · exact h

/-- **The gate of a sum** of codes below `ε_{G+1}`, below every `Z > ω` closed under `+`. -/
theorem gn_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < gnB → gnG x < Z → gnG y < Z → gnG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  have hxB : x < gnB := lt_of_le_of_lt le_self_add hxy
  have hyB : y < gnB := lt_of_le_of_lt le_add_self hxy
  rcases lt_or_ge x (gcG 0) with hxE | hxE
  · rcases lt_or_ge y (gcG 0) with hyE | hyE
    · rw [gnG_low hxE] at hgx
      rw [gnG_low hyE] at hgy
      rw [gnG_low ((inE_indec gl_G0_E).add_lt hxE hyE)]
      exact gl_add hZ hωZ x y ((inE_indec gl_G0_E).add_lt hxE hyE) hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gcG 0) (by rw [geG_E]; exact hxE) (by rw [geG_E]; exact hyE)
      rw [e]; exact hgy
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx⟩ := gn_parts hxE hxB
  set k := log (gcG 0) x with hkdef
  set d := x / gcG 0 ^ k with hddef
  set r := x % gcG 0 ^ k with hrdef
  rw [gnG_dec hxE hxB] at hgx
  have hgk : gnQ k < Z := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hgx)
  have hgd : glG d < Z := glG_of_Q hωZ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hgx))
  have hgr : gnG r < Z := (le_max_right _ _).trans_lt hgx
  rcases lt_or_ge y (gcG 0 ^ k) with hyk | hyk
  · have hry : r + y < gcG 0 ^ k := gn_pow_indec _ _ hr hyk
    have e : x + y = gcG 0 ^ k * d + (r + y) := by rw [← hdec, add_assoc]
    rw [e, gnG_cnf hk hd0 hdE hry (e ▸ hxy)]
    have hrB : r + y < gnB := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    exact max_lt ((le_max_left _ _).trans_lt hgx) (IH r hrx y hrB hgr hgy)
  rcases lt_or_ge y (gcG 0 ^ (k + 1)) with hyk1 | hyk1
  · have hEk : gcG 0 ≤ gcG 0 ^ k := by
      calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ gcG 0 ^ k := opow_le_opow_right gl_G0_E.pos (one_le_iff_ne_zero.2 hk)
    have hyE : gcG 0 ≤ y := hEk.trans hyk
    have hky : log (gcG 0) y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le gn_one_lt hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt gn_one_lt (gn_ne_of_le hyE)).1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -⟩ := gn_parts hyE hyB
    rw [hky] at hd0' hdE' hr' hdec'
    rw [gnG_dec hyE hyB, hky] at hgy
    set d' := y / gcG 0 ^ k with hd'def
    set r' := y % gcG 0 ^ k with hr'def
    have hgd' : glG d' < Z :=
      glG_of_Q hωZ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hgy))
    have hrω : r < ω ^ (gcG 0 * k) := by rw [← gn_pow_eq]; exact hr
    have hab : r + gcG 0 ^ k * d' = gcG 0 ^ k * d' := by
      rw [gn_pow_eq]
      exact add_of_omega0_opow_le hrω (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0'))
    have e : x + y = gcG 0 ^ k * (d + d') + r' := by
      rw [← hdec, ← hdec', add_assoc, ← add_assoc r, hab, ← add_assoc, ← mul_add]
    have hdd : d + d' < gcG 0 := (inE_indec gl_G0_E).add_lt hdE hdE'
    rw [e, gnG_cnf hk (by
      intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' (e ▸ hxy)]
    exact max_lt (max_lt hgk ((glQ_le _).trans_lt (gl_add hZ hωZ d d' hdd hgd hgd')))
      ((le_max_right _ _).trans_lt hgy)
  · have hxk : x < gcG 0 ^ (k + 1) := by
      rw [hkdef]; exact (lt_opow_iff_log_lt gn_one_lt (gn_ne_of_le hxE)).2 (lt_add_one _)
    have e : x + y = y := add_of_omega0_opow_le (b := gcG 0 * (k + 1)) (by rw [← gn_pow_eq]; exact hxk)
      (by rw [← gn_pow_eq]; exact hyk1)
    rw [e]; exact hgy

/-- `G^a = G·G^{a'}` with `1 + a' = a`. -/
theorem gn_pow_split {a : Ordinal.{0}} (ha : a ≠ 0) : gcG 0 ^ a = gcG 0 * gcG 0 ^ (a - 1) ∧ 1 + (a - 1) = a := by
  have e : 1 + (a - 1) = a := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 ha)
  refine ⟨?_, e⟩
  conv_lhs => rw [← e]
  rw [opow_add, opow_one]

/-- **`y/G` and `y mod G` keep the gate** of a code `G ≤ y < ε_{G+1}` (below every `Z > ω`). -/
theorem gn_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, gcG 0 ≤ y → y < gnB → gnG y < Z →
    gnQ (y / gcG 0) < Z ∧ glG (y % gcG 0) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyB hg
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry⟩ := gn_parts hyE hyB
  set a := log (gcG 0) y with hadef
  set d := y / gcG 0 ^ a with hddef
  set r := y % gcG 0 ^ a with hrdef
  rw [gnG_dec hyE hyB] at hg
  have hga : gnQ a < Z := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgd : glQ d < Z := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgr : gnG r < Z := (le_max_right _ _).trans_lt hg
  obtain ⟨hsp, e1⟩ := gn_pow_split ha
  have hy : y = gcG 0 * (gcG 0 ^ (a - 1) * d) + r := by rw [← hdec, hsp, mul_assoc]
  have hrB : r < gnB := hry.trans hyB
  constructor
  · have hdiv : y / gcG 0 = gcG 0 ^ (a - 1) * d + r / gcG 0 := by
      rw [hy, Ordinal.mul_add_div _ mg_G0_ne]
    rcases eq_or_ne (a - 1) 0 with ha1 | ha1
    · have hrE : r < gcG 0 := by
        have := hr; rw [hsp, ha1, opow_zero, mul_one] at this; exact this
      rw [hdiv, ha1, opow_zero, one_mul, Ordinal.div_eq_zero_of_lt hrE, add_zero, gnQ_low hdE]
      exact hgd
    · have hrq : r / gcG 0 < gcG 0 ^ (a - 1) := by
        rw [← Ordinal.lt_mul_iff_div_lt mg_G0_ne, ← hsp]; exact hr
      have hdB : y / gcG 0 < gnB :=
        lt_of_le_of_lt (Ordinal.div_le_of_le_mul (le_mul_right y gl_G0_E.pos)) hyB
      have hEq : gcG 0 ≤ y / gcG 0 := by
        rw [hdiv]
        calc gcG 0 = gcG 0 ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ gcG 0 ^ (a - 1) := opow_le_opow_right gl_G0_E.pos (one_le_iff_ne_zero.2 ha1)
          _ ≤ gcG 0 ^ (a - 1) * d := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)
          _ ≤ _ := le_self_add
      have hQ : gnQ (y / gcG 0) = gnG (y / gcG 0) := by
        unfold gnQ; rw [if_neg (not_lt.2 ((omega0_lt_inE gl_G0_E).le.trans hEq))]
      rw [hQ, hdiv, gnG_cnf ha1 hd0 hdE hrq (hdiv ▸ hdB)]
      refine max_lt (max_lt (by rw [← gnQ_one_add, e1]; exact hga) hgd) ?_
      rcases lt_or_ge r (gcG 0) with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, gnG_zero]; exact (omega0_pos).trans hωZ
      · exact gnG_of_Q hωZ (IH r hry hrE hrB hgr).1
  · have hmod : y % gcG 0 = r % gcG 0 := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r (gcG 0) with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE, ← gnG_low hrE]; exact hgr
    · exact (IH r hry hrE hrB hgr).2

/-- The gates of the parts of a code `G ≤ c < ε_{G+1}`. -/
theorem gn_parts_g {x c : Ordinal.{0}} (hωx : ω < x) (hcE : gcG 0 ≤ c) (hcB : c < gnB) (hg : gnG c < x) :
    gnG (log (gcG 0) c) < x ∧ glG (c / gcG 0 ^ log (gcG 0) c) < x ∧ gnG (c % gcG 0 ^ log (gcG 0) c) < x := by
  rw [gnG_dec hcE hcB] at hg
  exact ⟨gnG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    glG_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    (le_max_right _ _).trans_lt hg⟩

/-- `φ(a, b) = b` for a strongly critical `b` and `a < b`. -/
theorem gn_veb_fix {a b : Ordinal.{0}} (hb : SC b) (ha : a < b) : veblen a b = b := by
  have hl : IsSuccLimit b := ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC hb)
  refine le_antisymm ?_ (right_le_veblen a b)
  exact ((isNormal_veblen a).le_iff_forall_le hl).2 fun c hc => (hb.2 a ha c hc).le

/-- `ε_{G+1} = φ(1, G+1)`. -/
theorem gnB_eq : gnB = veblen 1 (gcG 0 + 1) := by
  have hfix : Ordinal.epsilon (gcG 0) = gcG 0 := gn_veb_fix (gcG_SC 0) gn_one_lt
  have hix : evIx (gcG 0) = gcG 0 := by
    conv_lhs => rw [← hfix]
    exact evIx_epsilon _
  have h := evA_add_one (gcG 0) 0
  rw [evA_zero gl_G0_E, zero_add] at h
  rw [gnB, ← h, evA, hix]

/-- **The gate of a code below `ε_{G+1}`**: a code over `Z` with the atoms `Γ_{Ω₁+1+c'}` (`c' < ε_{G+1}`, gate below
`Z`) has its gate below `Z`. -/
theorem gn_code_gate {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z) {c : Ordinal.{0}}
    (hc : GxCl Z {s | ∃ c', c' < gnB ∧ gnG c' < Z ∧ s = gcG c'} c) : c < gnB → gnG c < Z := by
  set At := {s | ∃ c', c' < gnB ∧ gnG c' < Z ∧ s = gcG c'} with hAtdef
  have hAtG : ∀ s ∈ At, gcG 0 ≤ s := by rintro s ⟨c'', -, -, rfl⟩; exact gcG_le zero_le
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hsmall : ∀ x, GxCl Z At x → x < gcG 0 → gnG x < Z := fun x hx h => by
    rw [gnG_low h]
    exact gl_code_gate le_rfl hZ1 hZ0 hZa hZp (fun s hs => absurd hs (Set.notMem_empty s)) gfE_lt_G0.le
      (mg_noAt hAtG hx h) h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans gl_Om1_lt_G0)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact gl_Om1_lt_G0)
  | @atom s hs =>
    intro h
    obtain ⟨c', -, -, rfl⟩ := hs
    rcases eq_or_ne c' 0 with rfl | hc0
    · rw [gnG_G]; exact hZ0
    · exfalso
      have h1 : gcG 1 ≤ gcG c' := gcG_le (Order.one_le_iff_ne_zero.2 hc0)
      exact absurd (h.trans gnB_lt_G1) (not_lt.2 h1)
  | @add x y hx hy ihx ihy =>
    intro h
    exact gn_add hZa hωZ x y h (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) (gcG 0) with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h hge ⊢
      have hyB : y < gnB := lt_of_le_of_lt (right_le_opow y one_lt_omega0) h
      have hEy : gcG 0 ≤ y := by
        rw [← geG_E 0] at hge
        exact (opow_le_opow_iff_right one_lt_omega0).1 hge
      set m := y / gcG 0 with hm
      set y' := y % gcG 0 with hy'
      have hm0 : m ≠ 0 := ((Ordinal.div_pos mg_G0_ne).2 hEy).ne'
      have hy'E : y' < gcG 0 := Ordinal.mod_lt y mg_G0_ne
      have ew : ω ^ y = gcG 0 ^ m * ω ^ y' + 0 := by
        rw [add_zero, gn_pow_eq]
        conv_lhs => rw [← Ordinal.div_add_mod y (gcG 0)]
        rw [opow_add]
      have hw0 : ω ^ y' ≠ 0 := opow_ne_zero _ omega0_ne_zero
      have hwE : ω ^ y' < gcG 0 := by
        rw [← geG_E 0]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hy'E
      obtain ⟨hgm, hgy'⟩ := gn_div hωZ y hEy hyB (ihy hyB)
      rw [ew, gnG_cnf hm0 hw0 hwE (opow_pos _ gl_G0_E.pos) (ew ▸ h), gnG_zero]
      exact max_lt (max_lt hgm ((glQ_le _).trans_lt (gl_opow_gate hZw hωZ y' hwE hgy'))) hZ0
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have heq : veblen x y = gcG 0 := by
        rcases hge.lt_or_eq with hlt | heq
        · exact absurd ((eN_le hlt hE).trans_lt h) (lt_irrefl _)
        · exact heq.symm
      rw [heq, gnG_G]; exact hZ0

/-! ## The reading: positivity, `1 + a`, `G·k` -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem gnR_pos {c : Ordinal.{0}} (hc0 : c ≠ 0) (hcB : c < gnB) (hg : gnG c < x) : 0 < gnR c x := by
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE] at hg
    rw [gnR_low hcE]; exact glR_pos hx hx1 hc0 hcE hg
  obtain ⟨-, hd0, hdE, -, -, -, -⟩ := gn_parts hcE hcB
  obtain ⟨-, g1, -⟩ := gn_parts_g (omega0_lt_inE hx) hcE hcB hg
  rw [gnR_dec hcE hcB]
  exact lt_of_lt_of_le (mul_pos (opow_pos _ (lgG_facts hx hx1).2.2.2.1.pos) (glR_pos hx hx1 hd0 hdE g1))
    le_self_add

/-- **An infinite code has an infinite reading.** -/
theorem gn_omega_le_gnR {a : Ordinal.{0}} (ha : ω ≤ a) (haB : a < gnB) (hg : gnG a < x) : ω ≤ gnR a x := by
  rcases lt_or_ge a (gcG 0) with haE | haE
  · rw [gnG_low haE] at hg
    rw [gnR_low haE]; exact gl_omega_le hx hx1 ha haE hg
  obtain ⟨hk, hd0, hdE, -, -, hlc, -⟩ := gn_parts haE haB
  obtain ⟨g0, g1, -⟩ := gn_parts_g (omega0_lt_inE hx) haE haB hg
  have hGE := (lgG_facts hx hx1).2.2.2.1
  rw [gnR_dec haE haB]
  calc ω ≤ lgG x := (omega0_lt_inE hGE).le
    _ = lgG x ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ lgG x ^ gnR (log (gcG 0) a) x :=
        opow_le_opow_right hGE.pos (one_le_iff_pos.2 (gnR_pos hx hx1 hk (hlc.trans haB) g0))
    _ ≤ lgG x ^ gnR (log (gcG 0) a) x * glR (a / gcG 0 ^ log (gcG 0) a) x :=
        le_mul_of_one_le_right' (one_le_iff_pos.2 (glR_pos hx hx1 hd0 hdE g1))
    _ ≤ _ := le_self_add

theorem gnR_one_add {a : Ordinal.{0}} (haB : a < gnB) (hg : gnG a < x) : gnR (1 + a) x = 1 + gnR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, gnR_nat, gnR_nat]; push_cast; rfl
  · rw [gn_one_add haω, gn_one_add (gn_omega_le_gnR hx hx1 haω haB hg)]

end Base

/-- **`G·k` as a code**: for a code `1 ≤ k < ε_{G+1}`, `G·k < ε_{G+1}`, its gate is at most that of `k`, and its
reading is `Γ_{x+1}·k(x)` at every base `x` above the gate of `k`. -/
theorem gn_mulG : ∀ k, k ≠ 0 → k < gnB → gcG 0 * k < gnB ∧ gnG (gcG 0 * k) ≤ gnG k ∧
    ∀ x, InE x → x < Om1 → gnG k < x → gnR (gcG 0 * k) x = lgG x * gnR k x := by
  intro k
  induction k using WellFoundedLT.induction with
  | ind k IH =>
  intro hk0 hkB
  have hB : gcG 0 * k < gnB := gnB_E.mul_lt gn_G0_lt_B hkB
  refine ⟨hB, ?_⟩
  rcases lt_or_ge k (gcG 0) with hkE | hkE
  · have e : gcG 0 * k = gcG 0 ^ (1 : Ordinal.{0}) * k + 0 := by rw [opow_one, add_zero]
    have hc := gnG_cnf one_ne_zero hk0 hkE (opow_pos _ gl_G0_E.pos) (e ▸ hB)
    refine ⟨?_, fun x _ _ _ => ?_⟩
    · rw [e, hc, gnG_low hkE, gnG_zero, max_eq_left zero_le]
      have : gnQ 1 = 0 := by exact_mod_cast gnQ_nat 1
      rw [this, max_eq_right zero_le]; exact glQ_le k
    · rw [e, gnR_cnf one_ne_zero hk0 hkE (opow_pos _ gl_G0_E.pos) (e ▸ hB), gnR_one, opow_one, gnR_zero,
        add_zero, gnR_low hkE]
  obtain ⟨ha, hd0, hdE, hr, hdec, hak, hrk⟩ := gn_parts hkE hkB
  set a := log (gcG 0) k with hadef
  set d := k / gcG 0 ^ a with hddef
  set r := k % gcG 0 ^ a with hrdef
  have hrB : r < gnB := hrk.trans hkB
  have h1a : 1 + a ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hEr : gcG 0 * r < gcG 0 ^ (1 + a) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 hr
  have e : gcG 0 * k = gcG 0 ^ (1 + a) * d + gcG 0 * r := by
    rw [← hdec, mul_add, ← mul_assoc, opow_add, opow_one]
  have hc := gnG_cnf h1a hd0 hdE hEr (e ▸ hB)
  have hgEr : gnG (gcG 0 * r) ≤ gnG r := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, mul_zero]
    · exact (IH r hrk h0 hrB).2.1
  refine ⟨?_, fun x hx hx1 hgk => ?_⟩
  · rw [e, hc, gnQ_one_add, gnG_dec hkE hkB]
    exact max_le_max le_rfl hgEr
  · obtain ⟨g0, -, g2⟩ := gn_parts_g (omega0_lt_inE hx) hkE hkB hgk
    rw [e, gnR_cnf h1a hd0 hdE hEr (e ▸ hB), gnR_dec hkE hkB]
    have hRr : gnR (gcG 0 * r) x = lgG x * gnR r x := by
      rcases eq_or_ne r 0 with h0 | h0
      · rw [h0, mul_zero, gnR_zero, mul_zero]
      · exact (IH r hrk h0 hrB).2.2 x hx hx1 g2
    rw [hRr, gnR_one_add hx hx1 (hak.trans hkB) g0, opow_add, opow_one, mul_assoc, ← mul_add]

/-- `G·k < G^k` for every code `2 ≤ k < ε_{G+1}` (`G·k` is not an `ε`-number). -/
theorem gn_mulG_lt_pow {k : Ordinal.{0}} (hk : 1 < k) (hkB : k < gnB) : gcG 0 * k < gcG 0 ^ k := by
  rw [gn_pow_eq]
  rcases (right_le_opow (gcG 0 * k) one_lt_omega0).lt_or_eq with h | h
  · exact h
  exfalso
  have hE : InE (gcG 0 * k) := h.symm
  have hlt : gcG 0 < gcG 0 * k := lt_mul_of_one_lt_right gl_G0_E.pos hk
  exact absurd ((eN_le hlt hE).trans_lt (gnB_E.mul_lt gn_G0_lt_B hkB)) (lt_irrefl _)

/-- **Every code `c < ε_{G+1}` lies in every hull `Cl(a, b)` (`a > 0`) containing its gate.** -/
theorem gn_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) : ∀ c, c < gnB → gnG c < b →
    c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (gcG 0) with hcE | hcE
  · rw [gnG_low hcE] at hg; exact (gl_mem c hcE hg).1
  obtain ⟨hk, hd0, hdE, -, hdec, hkc, hrc⟩ := gn_parts hcE hc
  rw [gnG_dec hcE hc] at hg
  have hr := IH _ hrc (hrc.trans hc) ((le_max_right _ _).trans_lt hg)
  rw [← hdec]
  refine CSet.add_mem ?_ hr
  set k := log (gcG 0) c with hkdef
  have hgk : gnQ k < b := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have heE : gcG 0 * k ∈ S.CSet a b := by
    by_cases hω : k < ω
    · obtain ⟨n, hn⟩ := lt_omega0.1 hω
      rw [hn]; exact mg_G0_mul_mem ha n
    · have hQ : gnQ k = gnG k := by unfold gnQ; rw [if_neg hω]
      have hk1 : 1 < k := lt_of_lt_of_le one_lt_omega0 (not_lt.1 hω)
      have hkB : k < gnB := hkc.trans hc
      obtain ⟨hB, hg', -⟩ := gn_mulG k hk hkB
      have hlt : gcG 0 * k < c := (gn_mulG_lt_pow hk1 hkB).trans_le (by
        rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add)
      exact IH _ hlt hB (hg'.trans_lt (hQ ▸ hgk))
  have hpow : gcG 0 ^ k = ω ^ (gcG 0 * k) := gn_pow_eq _
  have hgd := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  set d := c / gcG 0 ^ k with hd
  rw [hpow]
  by_cases hω : d < ω
  · obtain ⟨m, hm⟩ := lt_omega0.1 hω
    rw [hm]
    have := CSet.phi_mem (CSet.zero_mem (S := S) a b) heE
    rw [veblen_zero_apply] at this
    exact lg_cset_mul_nat this m
  · have h1 : glQ d = glG d := by unfold glQ; rw [if_neg hω]
    exact (gl_mem d hdE (by rw [← h1]; exact hgd)).2 _ heE

theorem gnB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) : gnB ∈ S.CSet a b := by
  rw [gnB_eq]
  exact CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (gmS_G0_mem S ha))

theorem gnG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, b + 1 < gnB → gnG b < Z → gnG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hg
  have hbB : b < gnB := (lt_add_one b).trans hb1
  rcases lt_or_ge b (gcG 0) with hbE | hbE
  · rw [gnG_low hbE] at hg
    have hb1G : b + 1 < gcG 0 := gl_G0_lim.add_one_lt hbE
    rw [gnG_low hb1G]
    exact glG_succ hZ b hb1G hg
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := gn_parts hbE hbB
  obtain ⟨e, hr1⟩ := gn_succ_cnf hbE
  rw [gnG_dec hbE hbB] at hg
  have hr1B : b % gcG 0 ^ log (gcG 0) b + 1 < gnB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, gnG_cnf hk hd0 hdE hr1 (e ▸ hb1)]
  exact max_lt ((le_max_left _ _).trans_lt hg) (IH _ hrb hr1B ((le_max_right _ _).trans_lt hg))

theorem gnG_le_succ : ∀ b, b + 1 < gnB → gnG b ≤ gnG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1
  have hbB : b < gnB := (lt_add_one b).trans hb1
  rcases lt_or_ge b (gcG 0) with hbE | hbE
  · have hb1G : b + 1 < gcG 0 := gl_G0_lim.add_one_lt hbE
    rw [gnG_low hbE, gnG_low hb1G]; exact glG_le_succ_all b
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := gn_parts hbE hbB
  obtain ⟨e, hr1⟩ := gn_succ_cnf hbE
  have hr1B : b % gcG 0 ^ log (gcG 0) b + 1 < gnB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [gnG_dec hbE hbB, e, gnG_cnf hk hd0 hdE hr1 (e ▸ hb1)]
  exact max_le_max le_rfl (IH _ hrb hr1B)

end Googology.Trans.PoR.InaccPsi.R2.Gn
