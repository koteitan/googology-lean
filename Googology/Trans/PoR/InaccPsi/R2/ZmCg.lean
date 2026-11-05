import Googology.Trans.PoR.InaccPsi.R2.ZmCx

/-!
# ZmCg: THE CHAIN OVER CODE INDICES — THE BASE AND THE SUCCESSOR STEP

`ZmGood2 c`: a digit system at the base `φ(1, B_Γ + c)` with base gate `G(c)` (the global gate of the code `c`),
base reading `φ(1, D(x) + R(c)(x))` above the gate, below `ζ_{D(x)+1}`, the global readings (`Zm.zmHR`) above the
gates and the gates `max (G c) (G c')`.  `ZmGood2 0` is `Zm.zmYr`; `ZmGood2 n ⇒ ZmGood2 (n+1)` is the generic step
raised by the gate of `n + 1`.

* `zm_max4`, `ZmGood2`, `zmGood2_zero`, `ZmDS.sG_glob` (the step's gates are the global gates over the base gate),
  `zmGood2_succ` (**the step at a code index**).

No new axiom.  New definition: `ZmGood2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Zb Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl

theorem zm_max4 (a b c d : Ordinal.{0}) : max (max a b) (max (max a c) d) = max a (max b (max c d)) := by
  rw [max_assoc, max_assoc a c d, max_left_comm b a, ← max_assoc a a, max_self]

theorem zm_max4' (a b c d : Ordinal.{0}) :
    max (max a b) (max (max a c) (max a d)) = max a (max b (max c d)) := by
  rw [max_assoc, max_assoc a c, max_left_comm c a, ← max_assoc a a, max_self, max_left_comm b a,
    ← max_assoc a a, max_self]

/-- **The digit system at the code index `c`.** -/
def ZmGood2 (c : Ordinal.{0}) : Prop :=
  ∃ M : ZmDS, M.E = veblen 1 (tfBG + c) ∧ M.Eg = zmHG c ∧
    (∀ x, InE x → x < Om1 → zmHG c < x → M.V x = veblen 1 (ywV 1 0 x + zmHR c x)) ∧
    (∀ x, InE x → x < Om1 → zmHG c < x → M.V x < veblen 2 (ywV 1 0 x + 1)) ∧
    (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = zmHR c' x) ∧
    (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max (zmHG c) (zmHG c'))

theorem zmHG_zero : zmHG 0 = 0 := by rw [zmHG_lt tfBG_SC.1, yrG_zero]

theorem zmHR_zero (x : Ordinal.{0}) : zmHR 0 x = 0 := by rw [zmHR_lt tfBG_SC.1, yrR_zero]

theorem zmGood2_zero : ZmGood2 0 := by
  refine ⟨zmYr, ?_, zmHG_zero.symm, fun x hx hx1 _ => ?_, fun x hx hx1 _ => ?_,
    fun c hc x _ _ _ => (zmHR_lt hc x).symm, fun c hc _ => ?_⟩
  · show tfBG = _; rw [add_zero, zm_BG_fix]
  · show ywV 1 0 x = _; rw [zmHR_zero, add_zero, zmD_fix hx hx1]
  · show ywV 1 0 x < _
    conv_lhs => rw [← zmD_fix2 hx hx1]
    exact (isNormal_veblen 2).strictMono (lt_add_one _)
  · show yrG c = _; rw [zmHG_zero, zmHG_lt hc, max_eq_right zero_le]

namespace ZmDS

variable (M : ZmDS)

/-- **The step's gates are the global gates over the base gate**, given that the system's gates are. -/
theorem sG_glob {n : Ordinal.{0}} (hn : n + 1 < zmZ) (hE : M.E = veblen 1 (tfBG + n))
    (hG : ∀ c', c' < M.E → c' ≠ 0 → M.G c' = max (zmHG n) (zmHG c')) :
    ∀ c', c' < eN M.E → c' ≠ 0 → M.sG c' = max (zmHG n) (zmHG c') := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc0
  rcases lt_or_ge c M.E with hcE | hcE
  · rw [M.sG_lt hcE]; exact hG c hcE hc0
  have hEN : eN M.E = veblen 1 (tfBG + (n + 1)) := by rw [hE, Go.go_eN_veb, add_assoc]
  have h1 : veblen 1 (tfBG + n) ≤ c := hE ▸ hcE
  have h2 : c < veblen 1 (tfBG + (n + 1)) := hEN ▸ hc
  have hB : tfBG ≤ c := (le_self_add.trans (right_le_veblen _ _)).trans h1
  have hZ : c < zmZ := h2.trans (zm_veb_lt_Z hn)
  have hN : zmN c = n := zmN_eq h1 h2
  have hBE : zmBE c = M.E := by rw [zmBE_eq h1 h2, hE]
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
  obtain ⟨hko, hro⟩ := M.parts_lt hcE hc
  rw [M.sG_cnf hcE hc, zmHG_cnf hB hZ, hN, hBE, IH _ hko (hko.trans hc) hk0.ne', hG _ hdE hd0.ne',
    ← max_assoc (zmHG n) (zmHG n), max_self]
  rcases eq_or_ne (c % M.E ^ log M.E c) 0 with hr0 | hr0
  · rw [hr0, M.sG_zero, zmHG_zero]; exact zm_max4 _ _ _ _
  · rw [IH _ hro (hro.trans hc) hr0]; exact zm_max4' _ _ _ _

end ZmDS

/-- **THE STEP AT A CODE INDEX**: `ZmGood2 n ⇒ ZmGood2 (n+1)` (below `ζ_{B_Γ+1}`). -/
theorem zmGood2_succ {n : Ordinal.{0}} (hn : n + 1 < zmZ) (h : ZmGood2 n) : ZmGood2 (n + 1) := by
  obtain ⟨M, hE, hEg, hV, hVb, hR, hG⟩ := h
  have hnZ : n < zmZ := (lt_add_one n).trans hn
  have hEN : eN M.E = veblen 1 (tfBG + (n + 1)) := by rw [hE, Go.go_eN_veb, add_assoc]
  have hgle : zmHG n ≤ zmHG (n + 1) := zmHG_le_succ n hnZ
  set g := zmHG (n + 1) with hgdef
  refine ⟨M.step.raise g, hEN, ?_, ?_, ?_, ?_, ?_⟩
  · show max M.Eg g = g; rw [hEg]; exact max_eq_right hgle
  · intro x hx hx1 hgx
    show eN (M.V x) = _
    rw [hV x hx hx1 (hgle.trans_lt hgx), Go.go_eN_veb, add_assoc, zmHR_succ n hnZ x]
  · intro x hx hx1 hgx
    show eN (M.V x) < _
    exact zm_eN_lt_fix (hVb x hx hx1 (hgle.trans_lt hgx)) (zm_veb2_fix _)
  · intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc x hx hx1 hgc
    change c < eN M.E at hc
    have hgc' : M.sG c < x := (M.step.G_le_rgt g c).trans_lt hgc
    show M.sR c x = zmHR c x
    rcases lt_or_ge c M.E with hcE | hcE
    · rw [M.sG_lt hcE] at hgc'; rw [M.sR_lt hcE, hR c hcE x hx hx1 hgc']
    have h1 : veblen 1 (tfBG + n) ≤ c := hE ▸ hcE
    have h2 : c < veblen 1 (tfBG + (n + 1)) := hEN ▸ hc
    have hB : tfBG ≤ c := (le_self_add.trans (right_le_veblen _ _)).trans h1
    have hZ : c < zmZ := h2.trans (zm_veb_lt_Z hn)
    have hN : zmN c = n := zmN_eq h1 h2
    have hBE : zmBE c = M.E := by rw [zmBE_eq h1 h2, hE]
    obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
    obtain ⟨hko, hro⟩ := M.parts_lt hcE hc
    obtain ⟨g1, g2, g3⟩ := M.gates hcE hc hgc'
    have hc0 : c ≠ 0 := (M.E_E.pos.trans_le hcE).ne'
    have hgx : g < x := M.step.g_lt_of g hc0 hgc
    have hnx : zmHG n < x := by rw [← hEg]; exact (M.sG_Eg _ hk0.ne').trans_lt g1
    have IH' : ∀ y, y < c → y < eN M.E → M.step.rgt g y < x → M.sR y x = zmHR y x :=
      fun y hy hyN hgy => IH y hy hyN x hx hx1 hgy
    rw [M.sR_cnf hcE hc x, zmHR_cnf hB hZ x, hN, hBE, hV x hx hx1 hnx,
      IH' _ hko (hko.trans hc) (M.step.rgt_lt g hgx g1), IH' _ hro (hro.trans hc) (M.step.rgt_lt g hgx g3),
      hR _ hdE x hx hx1 g2]
  · intro c hc hc0
    change c < eN M.E at hc
    show M.step.rgt g c = _
    rw [M.step.rgt_ne g hc0]
    show max g (M.sG c) = _
    rw [M.sG_glob (n := n) hn hE hG c hc hc0, ← max_assoc, max_eq_left hgle]

end Googology.Trans.PoR.InaccPsi.R2.Zm
