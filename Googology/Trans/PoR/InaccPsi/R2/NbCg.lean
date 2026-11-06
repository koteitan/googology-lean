import Googology.Trans.PoR.InaccPsi.R2.NbCx

/-!
# Nb: THE CHAIN OVER CODE INDICES ABOVE A PSEUDO-BASE — THE BASE AND THE SUCCESSOR STEP (`Zm.ZmCg` over any `P`)

`P = φ(2, p)`, `Z = φ(2, p+1)`, `M₀` a digit system at the base `P` with `V₀(x) = φ(2, b(x))` (`NbBase`); the reading and
gate below `P` are those of `M₀`, `nbHR p M₀.R M₀.V`, `nbHG p M₀.G` the global ones over `P` (`Nb.NbCx`).

* `NbBase` (**the base of the chain**), `NbGood` (**a digit system at the base `φ(1, P + c)`** with base gate
  `max g₀ (G c)`, base reading `φ(1, V₀(x) + R(c)(x))` below `φ(2, b(x)+1)`, readings and gates the global ones);
* `nb_max5`, `nb_max5'`, `nb_sG_glob` (the step's gates are the global gates over the base gate);
* `nbGood_zero` (**`M₀` itself**), `nbGood_succ` (**the step at a code index**: `ZmDS.step` raised by the gate of
  `n + 1`).

No new axiom.  New definitions: `NbBase`, `NbGood`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Nb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Zm

/-- **The base of the chain**: a digit system at `P = φ(2, p)` reading `P` as `φ(2, b(x))`. -/
structure NbBase (M₀ : ZmDS) (p : Ordinal.{0}) (b : Ordinal.{0} → Ordinal.{0}) : Prop where
  E_eq : M₀.E = veblen 2 p
  V_eq : ∀ x, InE x → x < Om1 → M₀.Eg < x → M₀.V x = veblen 2 (b x)

/-- **The digit system at the code index `c` over `P`.** -/
def NbGood (M₀ : ZmDS) (p : Ordinal.{0}) (b : Ordinal.{0} → Ordinal.{0}) (c : Ordinal.{0}) : Prop :=
  ∃ M : ZmDS, M.E = veblen 1 (veblen 2 p + c) ∧ M.Eg = max M₀.Eg (nbHG p M₀.G c) ∧
    (∀ x, InE x → x < Om1 → M.Eg < x → M.V x = veblen 1 (M₀.V x + nbHR p M₀.R M₀.V c x)) ∧
    (∀ x, InE x → x < Om1 → M.Eg < x → M.V x < veblen 2 (b x + 1)) ∧
    (∀ c', c' < M.E → ∀ x, InE x → x < Om1 → M.G c' < x → M.R c' x = nbHR p M₀.R M₀.V c' x) ∧
    (∀ c', c' < M.E → c' ≠ 0 → M.G c' = max M.Eg (nbHG p M₀.G c'))

theorem nb_max5 {e hn hk hd hr : Ordinal.{0}} (h : hn ≤ e) :
    max (max e hk) (max (max e hd) (max e hr)) = max e (max hn (max hk (max hd hr))) := by
  apply le_antisymm
  · refine max_le (max_le (le_max_left _ _) ?_) (max_le (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_))
    · exact (le_max_left hk _).trans ((le_max_right hn _).trans (le_max_right e _))
    · exact (le_max_left hd hr).trans ((le_max_right hk _).trans ((le_max_right hn _).trans (le_max_right e _)))
    · exact (le_max_right hd hr).trans ((le_max_right hk _).trans ((le_max_right hn _).trans (le_max_right e _)))
  · have eL : e ≤ max (max e hk) (max (max e hd) (max e hr)) := (le_max_left e hk).trans (le_max_left _ _)
    refine max_le eL (max_le (h.trans eL) (max_le ?_ (max_le ?_ ?_)))
    · exact (le_max_right e hk).trans (le_max_left _ _)
    · exact (le_max_right e hd).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right e hr).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem nb_max5' {e hn hk hd : Ordinal.{0}} (h : hn ≤ e) :
    max (max e hk) (max (max e hd) 0) = max e (max hn (max hk (max hd 0))) := by
  rw [max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ max e hd), max_eq_left (zero_le : (0 : Ordinal.{0}) ≤ hd)]
  apply le_antisymm
  · refine max_le (max_le (le_max_left _ _) ?_) (max_le (le_max_left _ _) ?_)
    · exact (le_max_left hk _).trans ((le_max_right hn _).trans (le_max_right e _))
    · exact (le_max_right hk hd).trans ((le_max_right hn _).trans (le_max_right e _))
  · have eL : e ≤ max (max e hk) (max e hd) := (le_max_left e hk).trans (le_max_left _ _)
    refine max_le eL (max_le (h.trans eL) (max_le ?_ ?_))
    · exact (le_max_right e hk).trans (le_max_left _ _)
    · exact (le_max_right e hd).trans (le_max_right _ _)

/-- **The step's gates are the global gates over the base gate.** -/
theorem nb_sG_glob (M : ZmDS) {p n e : Ordinal.{0}} {G₀ : Ordinal.{0} → Ordinal.{0}} (hG₀0 : G₀ 0 = 0)
    (hn : n + 1 < veblen 2 (p + 1)) (hE : M.E = veblen 1 (veblen 2 p + n)) (hen : nbHG p G₀ n ≤ e)
    (hG : ∀ c', c' < M.E → c' ≠ 0 → M.G c' = max e (nbHG p G₀ c')) :
    ∀ c', c' < eN M.E → c' ≠ 0 → M.sG c' = max e (nbHG p G₀ c') := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc0
  rcases lt_or_ge c M.E with hcE | hcE
  · rw [M.sG_lt hcE]; exact hG c hcE hc0
  have hEN : eN M.E = veblen 1 (veblen 2 p + (n + 1)) := by rw [hE, Go.go_eN_veb, add_assoc]
  have h1 : veblen 1 (veblen 2 p + n) ≤ c := hE ▸ hcE
  have h2 : c < veblen 1 (veblen 2 p + (n + 1)) := hEN ▸ hc
  have hB : veblen 2 p ≤ c := (le_self_add.trans (right_le_veblen _ _)).trans h1
  have hZ : c < veblen 2 (p + 1) := h2.trans (nb_veb_lt_Z hn)
  have hN : nbN p c = n := nbN_eq h1 h2
  have hBE : nbBE p c = M.E := by rw [nbBE_eq h1 h2, hE]
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
  obtain ⟨hko, hro⟩ := M.parts_lt hcE hc
  rw [M.sG_cnf hcE hc, nbHG_cnf hB hZ, hN, hBE, IH _ hko (hko.trans hc) hk0.ne', hG _ hdE hd0.ne']
  rcases eq_or_ne (c % M.E ^ log M.E c) 0 with hr0 | hr0
  · rw [hr0, M.sG_zero, nbHG_lt (nbP_pos p), hG₀0]; exact nb_max5' hen
  · rw [IH _ hro (hro.trans hc) hr0]; exact nb_max5 hen

section Chain

variable {M₀ : ZmDS} {p : Ordinal.{0}} {b : Ordinal.{0} → Ordinal.{0}} (hM₀ : NbBase M₀ p b)
include hM₀

/-- **The base of the chain is `M₀` itself.** -/
theorem nbGood_zero : NbGood M₀ p b 0 := by
  have hG0 : nbHG p M₀.G 0 = 0 := by rw [nbHG_lt (nbP_pos p), M₀.G0]
  refine ⟨M₀, ?_, ?_, fun x hx hx1 hgx => ?_, fun x hx hx1 hgx => ?_, fun c hc x _ _ _ => ?_,
    fun c hc hc0 => ?_⟩
  · rw [add_zero, nb_fixP]; exact hM₀.E_eq
  · rw [hG0, max_eq_left zero_le]
  · rw [nbHR_lt (nbP_pos p), M₀.R0, add_zero, hM₀.V_eq x hx hx1 hgx, nb_fixP]
  · rw [hM₀.V_eq x hx hx1 hgx]; exact nbP_lt_Z (b x)
  · rw [nbHR_lt (hM₀.E_eq ▸ hc)]
  · rw [nbHG_lt (hM₀.E_eq ▸ hc), max_eq_right (M₀.Eg_le c hc0)]

/-- **THE STEP AT A CODE INDEX ABOVE `P`**: `NbGood n ⇒ NbGood (n+1)` (below `Z`). -/
theorem nbGood_succ {n : Ordinal.{0}} (hn : n + 1 < veblen 2 (p + 1)) (h : NbGood M₀ p b n) :
    NbGood M₀ p b (n + 1) := by
  obtain ⟨M, hE, hEg, hV, hVb, hR, hG⟩ := h
  have hnZ : n < veblen 2 (p + 1) := (lt_add_one n).trans hn
  have hEN : eN M.E = veblen 1 (veblen 2 p + (n + 1)) := by rw [hE, Go.go_eN_veb, add_assoc]
  have hlim0 : ∀ o, o < veblen 2 p → M₀.G o ≤ M₀.G (o + 1) := fun o _ => M₀.g_le o
  have hgle : nbHG p M₀.G n ≤ nbHG p M₀.G (n + 1) := nbHG_le_succ hlim0 n hnZ
  set g := max M₀.Eg (nbHG p M₀.G (n + 1)) with hgdef
  have hEgg : M.Eg ≤ g := by rw [hEg]; exact max_le_max le_rfl hgle
  refine ⟨M.step.raise g, hEN, ?_, ?_, ?_, ?_, ?_⟩
  · show max M.Eg g = g; exact max_eq_right hEgg
  · intro x hx hx1 hgx
    have hgx' : M.Eg < x := hEgg.trans_lt ((le_max_right _ _).trans_lt hgx)
    show eN (M.V x) = _
    rw [hV x hx hx1 hgx', Go.go_eN_veb, add_assoc,
      nbHR_succ (fun o _ x => M₀.succ o x) n hnZ x]
  · intro x hx hx1 hgx
    have hgx' : M.Eg < x := hEgg.trans_lt ((le_max_right _ _).trans_lt hgx)
    show eN (M.V x) < _
    exact zm_eN_lt_fix (hVb x hx hx1 hgx') (nb_fixP _)
  · intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc x hx hx1 hgc
    change c < eN M.E at hc
    have hgc' : M.sG c < x := (M.step.G_le_rgt g c).trans_lt hgc
    show M.sR c x = nbHR p M₀.R M₀.V c x
    rcases lt_or_ge c M.E with hcE | hcE
    · rw [M.sG_lt hcE] at hgc'; rw [M.sR_lt hcE, hR c hcE x hx hx1 hgc']
    have h1 : veblen 1 (veblen 2 p + n) ≤ c := hE ▸ hcE
    have h2 : c < veblen 1 (veblen 2 p + (n + 1)) := hEN ▸ hc
    have hB : veblen 2 p ≤ c := (le_self_add.trans (right_le_veblen _ _)).trans h1
    have hZ : c < veblen 2 (p + 1) := h2.trans (nb_veb_lt_Z hn)
    have hN : nbN p c = n := nbN_eq h1 h2
    have hBE : nbBE p c = M.E := by rw [nbBE_eq h1 h2, hE]
    obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hcE
    obtain ⟨hko, hro⟩ := M.parts_lt hcE hc
    obtain ⟨g1, g2, g3⟩ := M.gates hcE hc hgc'
    have hc0 : c ≠ 0 := (M.E_E.pos.trans_le hcE).ne'
    have hgx : g < x := M.step.g_lt_of g hc0 hgc
    have hMx : M.Eg < x := (M.sG_Eg _ hk0.ne').trans_lt g1
    have IH' : ∀ y, y < c → y < eN M.E → M.step.rgt g y < x → M.sR y x = nbHR p M₀.R M₀.V y x :=
      fun y hy hyN hgy => IH y hy hyN x hx hx1 hgy
    rw [M.sR_cnf hcE hc x, nbHR_cnf hB hZ x, hN, hBE, hV x hx hx1 hMx,
      IH' _ hko (hko.trans hc) (M.step.rgt_lt g hgx g1), IH' _ hro (hro.trans hc) (M.step.rgt_lt g hgx g3),
      hR _ hdE x hx hx1 g2]
  · intro c hc hc0
    change c < eN M.E at hc
    show M.step.rgt g c = _
    rw [M.step.rgt_ne g hc0]
    show max g (M.sG c) = _
    have hen : nbHG p M₀.G n ≤ M.Eg := by rw [hEg]; exact le_max_right _ _
    rw [nb_sG_glob M M₀.G0 hn hE hen (fun c' hc' hc'0 => by rw [hG c' hc' hc'0]) c hc hc0]
    show max g (max M.Eg (nbHG p M₀.G c)) = max (max M.Eg g) (nbHG p M₀.G c)
    rw [max_eq_right hEgg, ← max_assoc, max_eq_left hEgg]

end Chain

end Googology.Trans.PoR.InaccPsi.R2.Nb
