import Googology.Trans.PoR.InaccPsi.R2.GvHC

/-!
# gates, sums, powers and hulls of the codes over a `GvD`

Textual copy of `R2.GsHG` with `Gs.GsD` replaced by `GvD` (`R2.GvD`: a gated digit system without the cofinal
sequence `cf`); no proof uses `cf`.  Contents: sums, powers, products by `B`, codes over a base, hulls, the code-gate
condition.

No new axiom.  New definitions: none.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gv

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace GvD

variable (D : GvD)

theorem hG_lt_Om1 : ∀ c, c < D.NB → D.hG c < Om1 := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE]; exact D.g_lt c hcE
  obtain ⟨-, -, hdE, -, -, hlc, hrc⟩ := D.parts hcE hc
  rw [D.hG_dec hcE hc]
  exact max_lt (max_lt ((D.hQ_le _).trans_lt (IH _ hlc (hlc.trans hc)))
    ((D.Q_le _).trans_lt (D.g_lt _ hdE))) (IH _ hrc (hrc.trans hc))

/-- The gate of a code below `Z > ω` from the gate of it as an exponent. -/
theorem hG_of_Q {k Z : Ordinal.{0}} (hωZ : ω < Z) (h : D.hQ k < Z) : D.hG k < Z := by
  unfold GvD.hQ at h
  split_ifs at h with hk
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hk
    rw [D.hG_nat]
    exact (D.g_nat n).trans hωZ
  · exact h

/-- **The gate of a sum** of codes below `ε_{B+1}`, below every `Z > ω` closed under `+`. -/
theorem h_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < D.NB → D.hG x < Z → D.hG y < Z → D.hG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  have hxB : x < D.NB := lt_of_le_of_lt le_self_add hxy
  have hyB : y < D.NB := lt_of_le_of_lt le_add_self hxy
  rcases lt_or_ge x (D.B) with hxE | hxE
  · rcases lt_or_ge y (D.B) with hyE | hyE
    · rw [D.hG_low hxE] at hgx
      rw [D.hG_low hyE] at hgy
      rw [D.hG_low ((inE_indec D.B_E).add_lt hxE hyE)]
      exact D.g_add _ hZ hωZ x y ((inE_indec D.B_E).add_lt hxE hyE) hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := D.B) (by rw [D.B_E]; exact hxE) (by rw [D.B_E]; exact hyE)
      rw [e]; exact hgy
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx⟩ := D.parts hxE hxB
  set k := log (D.B) x with hkdef
  set d := x / D.B ^ k with hddef
  set r := x % D.B ^ k with hrdef
  rw [D.hG_dec hxE hxB] at hgx
  have hgk : D.hQ k < Z := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hgx)
  have hgd : D.g d < Z := D.g_of_Q hωZ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hgx))
  have hgr : D.hG r < Z := (le_max_right _ _).trans_lt hgx
  rcases lt_or_ge y (D.B ^ k) with hyk | hyk
  · have hry : r + y < D.B ^ k := D.pow_indec _ _ hr hyk
    have e : x + y = D.B ^ k * d + (r + y) := by rw [← hdec, add_assoc]
    rw [e, D.hG_cnf hk hd0 hdE hry (e ▸ hxy)]
    have hrB : r + y < D.NB := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    exact max_lt ((le_max_left _ _).trans_lt hgx) (IH r hrx y hrB hgr hgy)
  rcases lt_or_ge y (D.B ^ (k + 1)) with hyk1 | hyk1
  · have hEk : D.B ≤ D.B ^ k := by
      calc D.B = D.B ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ D.B ^ k := opow_le_opow_right D.B_E.pos (one_le_iff_ne_zero.2 hk)
    have hyE : D.B ≤ y := hEk.trans hyk
    have hky : log (D.B) y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le D.one_lt_B hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt D.one_lt_B (D.ne_of_le hyE)).1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -⟩ := D.parts hyE hyB
    rw [hky] at hd0' hdE' hr' hdec'
    rw [D.hG_dec hyE hyB, hky] at hgy
    set d' := y / D.B ^ k with hd'def
    set r' := y % D.B ^ k with hr'def
    have hgd' : D.g d' < Z :=
      D.g_of_Q hωZ ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hgy))
    have hrω : r < ω ^ (D.B * k) := by rw [← D.pow_eq]; exact hr
    have hab : r + D.B ^ k * d' = D.B ^ k * d' := by
      rw [D.pow_eq]
      exact add_of_omega0_opow_le hrω (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0'))
    have e : x + y = D.B ^ k * (d + d') + r' := by
      rw [← hdec, ← hdec', add_assoc, ← add_assoc r, hab, ← add_assoc, ← mul_add]
    have hdd : d + d' < D.B := (inE_indec D.B_E).add_lt hdE hdE'
    rw [e, D.hG_cnf hk (by
      intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' (e ▸ hxy)]
    exact max_lt (max_lt hgk ((D.Q_le _).trans_lt (D.g_add _ hZ hωZ d d' hdd hgd hgd')))
      ((le_max_right _ _).trans_lt hgy)
  · have hxk : x < D.B ^ (k + 1) := by
      rw [hkdef]; exact (lt_opow_iff_log_lt D.one_lt_B (D.ne_of_le hxE)).2 (lt_add_one _)
    have e : x + y = y := add_of_omega0_opow_le (b := D.B * (k + 1)) (by rw [← D.pow_eq]; exact hxk)
      (by rw [← D.pow_eq]; exact hyk1)
    rw [e]; exact hgy

/-- `B^a = B·B^{a'}` with `1 + a' = a`. -/
theorem pow_split {a : Ordinal.{0}} (ha : a ≠ 0) : D.B ^ a = D.B * D.B ^ (a - 1) ∧ 1 + (a - 1) = a := by
  have e : 1 + (a - 1) = a := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 ha)
  refine ⟨?_, e⟩
  conv_lhs => rw [← e]
  rw [opow_add, opow_one]

/-- **`y/B` and `y mod B` keep the gate** of a code `B ≤ y < ε_{B+1}` (below every `Z > ω`). -/
theorem hdiv {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, D.B ≤ y → y < D.NB → D.hG y < Z →
    D.hQ (y / D.B) < Z ∧ D.g (y % D.B) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyB hg
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry⟩ := D.parts hyE hyB
  set a := log (D.B) y with hadef
  set d := y / D.B ^ a with hddef
  set r := y % D.B ^ a with hrdef
  rw [D.hG_dec hyE hyB] at hg
  have hga : D.hQ a < Z := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgd : D.Q d < Z := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have hgr : D.hG r < Z := (le_max_right _ _).trans_lt hg
  obtain ⟨hsp, e1⟩ := D.pow_split ha
  have hy : y = D.B * (D.B ^ (a - 1) * d) + r := by rw [← hdec, hsp, mul_assoc]
  have hrB : r < D.NB := hry.trans hyB
  constructor
  · have hdiv : y / D.B = D.B ^ (a - 1) * d + r / D.B := by
      rw [hy, Ordinal.mul_add_div _ D.B_ne]
    rcases eq_or_ne (a - 1) 0 with ha1 | ha1
    · have hrE : r < D.B := by
        have := hr; rw [hsp, ha1, opow_zero, mul_one] at this; exact this
      rw [hdiv, ha1, opow_zero, one_mul, Ordinal.div_eq_zero_of_lt hrE, add_zero, D.hQ_low hdE]
      exact hgd
    · have hrq : r / D.B < D.B ^ (a - 1) := by
        rw [← Ordinal.lt_mul_iff_div_lt D.B_ne, ← hsp]; exact hr
      have hdB : y / D.B < D.NB :=
        lt_of_le_of_lt (Ordinal.div_le_of_le_mul (le_mul_right y D.B_E.pos)) hyB
      have hEq : D.B ≤ y / D.B := by
        rw [hdiv]
        calc D.B = D.B ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ D.B ^ (a - 1) := opow_le_opow_right D.B_E.pos (one_le_iff_ne_zero.2 ha1)
          _ ≤ D.B ^ (a - 1) * d := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)
          _ ≤ _ := le_self_add
      have hQ : D.hQ (y / D.B) = D.hG (y / D.B) := by
        unfold GvD.hQ; rw [if_neg (not_lt.2 ((omega0_lt_inE D.B_E).le.trans hEq))]
      rw [hQ, hdiv, D.hG_cnf ha1 hd0 hdE hrq (hdiv ▸ hdB)]
      refine max_lt (max_lt (by rw [← D.hQ_one_add, e1]; exact hga) hgd) ?_
      rcases lt_or_ge r (D.B) with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, D.hG_zero]; exact (omega0_pos).trans hωZ
      · exact D.hG_of_Q hωZ (IH r hry hrE hrB hgr).1
  · have hmod : y % D.B = r % D.B := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r (D.B) with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE, ← D.hG_low hrE]; exact hgr
    · exact (IH r hry hrE hrB hgr).2

/-- The gates of the parts of a code `B ≤ c < ε_{B+1}`. -/
theorem parts_g {x c : Ordinal.{0}} (hωx : ω < x) (hcE : D.B ≤ c) (hcB : c < D.NB) (hg : D.hG c < x) :
    D.hG (log (D.B) c) < x ∧ D.g (c / D.B ^ log (D.B) c) < x ∧ D.hG (c % D.B ^ log (D.B) c) < x := by
  rw [D.hG_dec hcE hcB] at hg
  exact ⟨D.hG_of_Q hωx ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    D.g_of_Q hωx ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)),
    (le_max_right _ _).trans_lt hg⟩

/-- `ε_{B+1} = φ(1, ix+1)`. -/
theorem NB_eq : D.NB = veblen 1 (D.ix + 1) := by
  rw [GvD.NB, D.B_ix]; exact go_eN_veb D.ix

theorem B_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (hγb : D.γ < b) : D.B ∈ S.CSet a b := by
  rw [D.B_ix]; exact CSet.phi_mem (CSet.one_mem _ _) (D.ix_mem S a b ha hγb)

theorem NB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (hγb : D.γ < b) : D.NB ∈ S.CSet a b := by
  rw [D.NB_eq]; exact CSet.phi_mem (CSet.one_mem _ _) (CSet.succ_mem (D.ix_mem S a b ha hγb))

/-- **The gate of a power `ω^y`** of a code below `ε_{B+1}` (`ω^y = B^{y/B}·ω^{y mod B}` for `y ≥ B`). -/
theorem h_opow {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) (hZ0 : 0 < Z) :
    ∀ y, ω ^ y < D.NB → D.hG y < Z → D.hG (ω ^ y) < Z := by
  intro y h hgy
  have hyB : y < D.NB := lt_of_le_of_lt (right_le_opow y one_lt_omega0) h
  rcases lt_or_ge (ω ^ y) D.B with hlt | hge
  · have hyB' : y < D.B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hlt
    rw [D.hG_low hlt]; rw [D.hG_low hyB'] at hgy
    exact D.g_opow Z hZw hωZ y hlt hgy
  have hEy : D.B ≤ y := by
    rw [← show ω ^ D.B = D.B from D.B_E] at hge
    exact (opow_le_opow_iff_right one_lt_omega0).1 hge
  set m := y / D.B with hm
  set y' := y % D.B with hy'
  have hm0 : m ≠ 0 := ((Ordinal.div_pos D.B_ne).2 hEy).ne'
  have hy'E : y' < D.B := Ordinal.mod_lt y D.B_ne
  have ew : ω ^ y = D.B ^ m * ω ^ y' + 0 := by
    rw [add_zero, D.pow_eq]
    conv_lhs => rw [← Ordinal.div_add_mod y (D.B)]
    rw [opow_add]
  have hw0 : ω ^ y' ≠ 0 := opow_ne_zero _ omega0_ne_zero
  have hwE : ω ^ y' < D.B := by
    rw [← show ω ^ D.B = D.B from D.B_E]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hy'E
  obtain ⟨hgm, hgy'⟩ := D.hdiv hωZ y hEy hyB hgy
  rw [ew, D.hG_cnf hm0 hw0 hwE (opow_pos _ D.B_E.pos) (ew ▸ h), D.hG_zero]
  exact max_lt (max_lt hgm ((D.Q_le _).trans_lt (D.g_opow Z hZw hωZ y' hwE hgy'))) hZ0

/-- **The gate of a code below `ε_{B+1}`**: a code over `Z` with atoms (each `Γ_{Ω₁+1}` or `≥ ε_{B+1}`) has its gate
below `Z`. -/
theorem h_code_gate {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z)
    (hZa : ∀ u v, u < Z → v < Z → u + v < Z) (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z)
    {At : Set Ordinal.{0}} (hAt : ∀ s ∈ At, s = gcG 0 ∨ D.NB ≤ s) {c : Ordinal.{0}}
    (hc : GxCl Z At c) : c < D.NB → D.hG c < Z := by
  have hZw : ∀ u, u < Z → ω ^ u < Z := fun u hu => by
    have := hZp 0 u hZ0 hu; rwa [veblen_zero_apply] at this
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZw 0 hZ0; rwa [opow_zero] at this
  have hωZ : ω < Z := by
    have := hZw 1 h1Z; rwa [opow_one] at this
  have hOB : Om1 < D.B := gl_Om1_lt_G0.trans_le D.G_le
  have hsmall : ∀ x, GxCl Z At x → x < D.B → D.hG x < Z := fun x hx h => by
    rw [D.hG_low h]
    exact D.code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right (fun h' => D.B_lt_NB.le.trans h'))
      x hx h
  induction hc with
  | @small x h => exact fun _ => hsmall _ (GxCl.small h) ((h.trans_le hZ1).trans hOB)
  | om => exact fun _ => hsmall _ GxCl.om (by rw [← Br.Om1_eq]; exact hOB)
  | @atom s hs =>
    intro h
    rcases hAt s hs with rfl | hge
    · rcases D.G_le.lt_or_eq with hlt | heq
      · rw [D.hG_low hlt, D.g_G0 hlt]; exact hZ0
      · rw [heq, D.hG_G]; exact hZ0
    · exact absurd (h.trans_le hge) (lt_irrefl _)
  | @add x y hx hy ihx ihy =>
    intro h
    exact D.h_add hZa hωZ x y h (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y hx hy ihx ihy =>
    intro h
    rcases lt_or_ge (veblen x y) (D.B) with hlt | hge
    · exact hsmall _ (GxCl.phi hx hy) hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply] at h ⊢
      have hyB : y < D.NB := lt_of_le_of_lt (right_le_opow y one_lt_omega0) h
      exact D.h_opow hZw hωZ hZ0 y h (ihy hyB)
    · have hE : ω ^ veblen x y = veblen x y := by
        have := veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
        rwa [veblen_zero_apply] at this
      have heq : veblen x y = D.B := by
        rcases hge.lt_or_eq with hlt | heq
        · exact absurd ((eN_le hlt hE).trans_lt h) (lt_irrefl _)
        · exact heq.symm
      rw [heq, D.hG_G]; exact hZ0

/-! ## The reading: positivity, `1 + a`, `B·k` -/

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγx : D.γ < x)
include hx hx1 hγx

theorem hR_pos {c : Ordinal.{0}} (hc0 : c ≠ 0) (hcB : c < D.NB) (hg : D.hG c < x) : 0 < D.hR c x := by
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg
    rw [D.hR_low hcE]; exact D.R_pos x hx hx1 c hc0 hcE hg
  obtain ⟨-, hd0, hdE, -, -, -, -⟩ := D.parts hcE hcB
  obtain ⟨-, g1, -⟩ := D.parts_g (omega0_lt_inE hx) hcE hcB hg
  rw [D.hR_dec hcE hcB]
  exact lt_of_lt_of_le (mul_pos (opow_pos _ (D.b_E x hx hx1 hγx).pos) (D.R_pos x hx hx1 _ hd0 hdE g1))
    le_self_add

/-- **An infinite code has an infinite reading.** -/
theorem omega_le_hR {a : Ordinal.{0}} (ha : ω ≤ a) (haB : a < D.NB) (hg : D.hG a < x) : ω ≤ D.hR a x := by
  rcases lt_or_ge a (D.B) with haE | haE
  · rw [D.hG_low haE] at hg
    rw [D.hR_low haE]; exact D.R_omega x hx hx1 a ha haE hg
  obtain ⟨hk, hd0, hdE, -, -, hlc, -⟩ := D.parts haE haB
  obtain ⟨g0, g1, -⟩ := D.parts_g (omega0_lt_inE hx) haE haB hg
  have hGE := D.b_E x hx hx1 hγx
  rw [D.hR_dec haE haB]
  calc ω ≤ D.b x := (omega0_lt_inE hGE).le
    _ = D.b x ^ (1 : Ordinal.{0}) := (opow_one _).symm
    _ ≤ D.b x ^ D.hR (log (D.B) a) x :=
        opow_le_opow_right hGE.pos (one_le_iff_pos.2 (D.hR_pos hx hx1 hγx hk (hlc.trans haB) g0))
    _ ≤ D.b x ^ D.hR (log (D.B) a) x * D.R (a / D.B ^ log (D.B) a) x :=
        le_mul_of_one_le_right' (one_le_iff_pos.2 (D.R_pos x hx hx1 _ hd0 hdE g1))
    _ ≤ _ := le_self_add

theorem hR_one_add {a : Ordinal.{0}} (haB : a < D.NB) (hg : D.hG a < x) : D.hR (1 + a) x = 1 + D.hR a x := by
  rcases lt_or_ge a ω with haω | haω
  · obtain ⟨n, hn⟩ := lt_omega0.1 haω
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [hn, this, D.hR_nat, D.hR_nat]; push_cast; rfl
  · rw [one_add_of_omega0_le haω, one_add_of_omega0_le (D.omega_le_hR hx hx1 hγx haω haB hg)]

end Base

/-- **`B·k` as a code**: for a code `1 ≤ k < ε_{B+1}`, `B·k < ε_{B+1}`, its gate is at most that of `k`, and its
reading is `b(x)·k(x)` at every base `x` above the gate of `k`. -/
theorem mulB : ∀ k, k ≠ 0 → k < D.NB → D.B * k < D.NB ∧ D.hG (D.B * k) ≤ D.hG k ∧
    ∀ x, InE x → x < Om1 → D.γ < x → D.hG k < x → D.hR (D.B * k) x = D.b x * D.hR k x := by
  intro k
  induction k using WellFoundedLT.induction with
  | ind k IH =>
  intro hk0 hkB
  have hB : D.B * k < D.NB := D.NB_E.mul_lt D.B_lt_NB hkB
  refine ⟨hB, ?_⟩
  rcases lt_or_ge k (D.B) with hkE | hkE
  · have e : D.B * k = D.B ^ (1 : Ordinal.{0}) * k + 0 := by rw [opow_one, add_zero]
    have hc := D.hG_cnf one_ne_zero hk0 hkE (opow_pos _ D.B_E.pos) (e ▸ hB)
    refine ⟨?_, fun x _ _ _ _ => ?_⟩
    · rw [e, hc, D.hG_low hkE, D.hG_zero, max_eq_left zero_le]
      have : D.hQ 1 = 0 := by exact_mod_cast D.hQ_nat 1
      rw [this, max_eq_right zero_le]; exact D.Q_le k
    · rw [e, D.hR_cnf one_ne_zero hk0 hkE (opow_pos _ D.B_E.pos) (e ▸ hB), D.hR_one, opow_one, D.hR_zero,
        add_zero, D.hR_low hkE]
  obtain ⟨ha, hd0, hdE, hr, hdec, hak, hrk⟩ := D.parts hkE hkB
  set a := log (D.B) k with hadef
  set d := k / D.B ^ a with hddef
  set r := k % D.B ^ a with hrdef
  have hrB : r < D.NB := hrk.trans hkB
  have h1a : 1 + a ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have hEr : D.B * r < D.B ^ (1 + a) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ D.B_E.pos).2 hr
  have e : D.B * k = D.B ^ (1 + a) * d + D.B * r := by
    rw [← hdec, mul_add, ← mul_assoc, opow_add, opow_one]
  have hc := D.hG_cnf h1a hd0 hdE hEr (e ▸ hB)
  have hgEr : D.hG (D.B * r) ≤ D.hG r := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, mul_zero]
    · exact (IH r hrk h0 hrB).2.1
  refine ⟨?_, fun x hx hx1 hγx hgk => ?_⟩
  · rw [e, hc, D.hQ_one_add, D.hG_dec hkE hkB]
    exact max_le_max le_rfl hgEr
  · obtain ⟨g0, -, g2⟩ := D.parts_g (omega0_lt_inE hx) hkE hkB hgk
    rw [e, D.hR_cnf h1a hd0 hdE hEr (e ▸ hB), D.hR_dec hkE hkB]
    have hRr : D.hR (D.B * r) x = D.b x * D.hR r x := by
      rcases eq_or_ne r 0 with h0 | h0
      · rw [h0, mul_zero, D.hR_zero, mul_zero]
      · exact (IH r hrk h0 hrB).2.2 x hx hx1 hγx g2
    rw [hRr, D.hR_one_add hx hx1 hγx (hak.trans hkB) g0, opow_add, opow_one, mul_assoc, ← mul_add]

/-- `B·k < B^k` for every code `2 ≤ k < ε_{B+1}` (`B·k` is not an `ε`-number). -/
theorem mulB_lt_pow {k : Ordinal.{0}} (hk : 1 < k) (hkB : k < D.NB) : D.B * k < D.B ^ k := by
  rw [D.pow_eq]
  rcases (right_le_opow (D.B * k) one_lt_omega0).lt_or_eq with h | h
  · exact h
  exfalso
  have hE : InE (D.B * k) := h.symm
  have hlt : D.B < D.B * k := lt_mul_of_one_lt_right D.B_E.pos hk
  exact absurd ((eN_le hlt hE).trans_lt (D.NB_E.mul_lt D.B_lt_NB hkB)) (lt_irrefl _)

/-- **Every code `c < ε_{B+1}` lies in every hull `Cl(a, b)` (`a > 0`) containing its gate, and so does `ω^e·c`
for every `e ∈ Cl(a, b)`.** -/
theorem hmem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (hγb : D.γ < b) : ∀ c, c < D.NB → D.hG c < b →
    c ∈ S.CSet a b ∧ ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hg
  rcases lt_or_ge c (D.B) with hcE | hcE
  · rw [D.hG_low hcE] at hg; exact D.mem S a b ha c hcE hg
  obtain ⟨hk, hd0, hdE, -, hdec, hkc, hrc⟩ := D.parts hcE hc
  rw [D.hG_dec hcE hc] at hg
  have hr := IH _ hrc (hrc.trans hc) ((le_max_right _ _).trans_lt hg)
  set k := log (D.B) c with hkdef
  have hgk : D.hQ k < b := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  have heE : D.B * k ∈ S.CSet a b := by
    by_cases hω : k < ω
    · obtain ⟨n, hn⟩ := lt_omega0.1 hω
      rw [hn]; exact lg_cset_mul_nat (D.B_mem ha hγb) n
    · have hQ : D.hQ k = D.hG k := by unfold GvD.hQ; rw [if_neg hω]
      have hk1 : 1 < k := lt_of_lt_of_le one_lt_omega0 (not_lt.1 hω)
      have hkB : k < D.NB := hkc.trans hc
      obtain ⟨hB, hg', -⟩ := D.mulB k hk hkB
      have hlt : D.B * k < c := (D.mulB_lt_pow hk1 hkB).trans_le (by
        rw [← hdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add)
      exact (IH _ hlt hB (hg'.trans_lt (hQ ▸ hgk))).1
  have hpow : D.B ^ k = ω ^ (D.B * k) := D.pow_eq _
  have hgd := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hg)
  set d := c / D.B ^ k with hd
  have hall : ∀ e ∈ S.CSet a b, ω ^ e * c ∈ S.CSet a b := by
    intro e he
    have hsplit : ω ^ e * c = ω ^ (e + D.B * k) * d + ω ^ e * (c % D.B ^ k) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, hpow, ← mul_assoc, ← opow_add]
    rw [hsplit]
    refine CSet.add_mem ?_ (hr.2 e he)
    have hek : e + D.B * k ∈ S.CSet a b := CSet.add_mem he heE
    by_cases hω : d < ω
    · obtain ⟨m, hm⟩ := lt_omega0.1 hω
      rw [hm]
      have := CSet.phi_mem (CSet.zero_mem (S := S) a b) hek
      rw [veblen_zero_apply] at this
      exact lg_cset_mul_nat this m
    · have h1 : D.Q d = D.g d := by unfold GvD.Q; rw [if_neg hω]
      exact (D.mem S a b ha d hdE (by rw [← h1]; exact hgd)).2 _ hek
  refine ⟨?_, hall⟩
  have := hall 0 (CSet.zero_mem _ _)
  rwa [opow_zero, one_mul] at this

theorem hG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, b + 1 < D.NB → D.hG b < Z → D.hG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1 hg
  have hbB : b < D.NB := (lt_add_one b).trans hb1
  rcases lt_or_ge b (D.B) with hbE | hbE
  · rw [D.hG_low hbE] at hg
    have hb1G : b + 1 < D.B := D.B_lim.add_one_lt hbE
    rw [D.hG_low hb1G]
    exact D.g_succ _ hZ b hb1G hg
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := D.parts hbE hbB
  obtain ⟨e, hr1⟩ := D.succ_cnf hbE
  rw [D.hG_dec hbE hbB] at hg
  have hr1B : b % D.B ^ log (D.B) b + 1 < D.NB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [e, D.hG_cnf hk hd0 hdE hr1 (e ▸ hb1)]
  exact max_lt ((le_max_left _ _).trans_lt hg) (IH _ hrb hr1B ((le_max_right _ _).trans_lt hg))

theorem hG_le_succ : ∀ b, b + 1 < D.NB → D.hG b ≤ D.hG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb1
  have hbB : b < D.NB := (lt_add_one b).trans hb1
  rcases lt_or_ge b (D.B) with hbE | hbE
  · have hb1G : b + 1 < D.B := D.B_lim.add_one_lt hbE
    rw [D.hG_low hbE, D.hG_low hb1G]; exact D.g_le_succ b
  obtain ⟨hk, hd0, hdE, hr, -, -, hrb⟩ := D.parts hbE hbB
  obtain ⟨e, hr1⟩ := D.succ_cnf hbE
  have hr1B : b % D.B ^ log (D.B) b + 1 < D.NB := lt_of_le_of_lt (by rw [e]; exact le_add_self) hb1
  rw [D.hG_dec hbE hbB, e, D.hG_cnf hk hd0 hdE hr1 (e ▸ hb1)]
  exact max_le_max le_rfl (IH _ hrb hr1B)

end GvD

end Googology.Trans.PoR.InaccPsi.R2.Gv
