import Googology.Trans.PoR.InaccPsi.R2.ZmRS

/-!
# ZmSt: THE GENERIC HEREDITARY STEP — DEFINITIONS, THE ORDER, SUCCESSORS AND LIMITS

For a digit system `M` at the base `E` the codes `E ≤ o < ε_{E+1}` are `o = E^k·d + r` (`k = log_E o ≥ 1`,
`0 < d < E`, `r < E^k`, `k, r < o`); the reading is `V(x)^{R(k)(x)}·R(d)(x) + R(r)(x)` (one recursion on `o`), the gate
`max (G k) (max (G d) (G r))`.  Every statement is proved once for every digit system.

* `zm_log_lt`, `zm_mod_lt`, `zm_dec`, `zm_dec_uniq`, `zm_lex`, `zm_opow_lt`;
* `sR`, `sG` (the reading and the gate of the codes below `ε_{E+1}`), `sR_lt`, `sR_cnf`, `sR_big`, `sR_eq`, `sG_eq`;
* `sR_main` (**the bound `R(o)(x) < ε_{V(x)+1}`, positivity, the top bound `R(o) < V^{R(k)+1}` and the order, one
  induction**), `sR_succ`, `sG_le_succ`, `sG_succ_lt`, `sR_lim`.

No new axiom.  New definitions: `ZmDS.sR`, `ZmDS.sG`.
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

/-! ## Cantor normal form in an `ε`-number base `E` -/

section Arith

variable {E : Ordinal.{0}} (hE : InE E)
include hE

theorem zm_E1 : (1 : Ordinal.{0}) < E := lu_one_lt_E hE

theorem zm_E0 : E ≠ 0 := hE.pos.ne'

/-- `b^c < u` for `b, c < u` (`u` an `ε`-number). -/
theorem zm_opow_lt {b c : Ordinal.{0}} (hb : b < E) (hc : c < E) : b ^ c < E := by
  have h1 : b ^ c ≤ (ω ^ b) ^ c := opow_le_opow_left c (right_le_opow b one_lt_omega0)
  rw [← opow_mul] at h1
  have h2 : ω ^ (b * c) < ω ^ E := (opow_lt_opow_iff_right one_lt_omega0).2 (mul_lt_inE hE hb hc)
  rw [show ω ^ E = E from hE] at h2
  exact h1.trans_lt h2

/-- **The exponent is below the code**: `log_E o < o` for `E ≤ o < ε_{E+1}`. -/
theorem zm_log_lt {o : Ordinal.{0}} (h1 : E ≤ o) (h2 : o < eN E) : log E o < o := by
  have ho0 : o ≠ 0 := (hE.pos.trans_le h1).ne'
  set k := log E o with hk
  have hk0 : 0 < k := log_pos (zm_E1 hE) ho0 h1
  have hEk : E ^ k ≤ o := opow_log_le_self E ho0
  refine lt_of_lt_of_le ?_ hEk
  have hEω : E ^ k = ω ^ (E * k) := by
    conv_lhs => rw [← (show ω ^ E = E from hE)]
    rw [← opow_mul]
  rw [hEω]
  rcases lt_or_ge k E with hkE | hkE
  · calc k < E := hkE
      _ = ω ^ (E * 1) := by rw [mul_one]; exact hE.symm
      _ ≤ ω ^ (E * k) := opow_le_opow_right omega0_pos (mul_le_mul_right (one_le_iff_pos.2 hk0) E)
  · have hko : k < eN E := (log_le_self E o).trans_lt h2
    have hEk' : E * k < eN E := mul_lt_inE (eN_E E) (lt_eN E) hko
    have hkEk : k ≤ E * k := by
      calc k = 1 * k := (one_mul k).symm
        _ ≤ E * k := mul_le_mul_left (zm_E1 hE).le k
    have hne : ω ^ (E * k) ≠ E * k := by
      intro e
      have hEkE : InE (E * k) := e
      have hgt : E < E * k := by
        calc E = E * 1 := (mul_one E).symm
          _ < E * k := (mul_lt_mul_iff_right₀ hE.pos).2 ((zm_E1 hE).trans_le hkE)
      exact absurd (eN_le hgt hEkE) (not_le.2 hEk')
    exact hkEk.trans_lt (lt_of_le_of_ne (right_le_opow _ one_lt_omega0) hne.symm)

theorem zm_mod_lt {o : Ordinal.{0}} (h1 : E ≤ o) : o % E ^ log E o < o := by
  have ho0 : o ≠ 0 := (hE.pos.trans_le h1).ne'
  exact (Ordinal.mod_lt o (opow_pos _ hE.pos).ne').trans_le (opow_log_le_self E ho0)

/-- **The decomposition** `o = E^k·d + r`, `1 ≤ k`, `0 < d < E`, `r < E^k`. -/
theorem zm_dec {o : Ordinal.{0}} (h1 : E ≤ o) :
    0 < log E o ∧ 0 < o / E ^ log E o ∧ o / E ^ log E o < E ∧ o % E ^ log E o < E ^ log E o ∧
      E ^ log E o * (o / E ^ log E o) + o % E ^ log E o = o := by
  have ho0 : o ≠ 0 := (hE.pos.trans_le h1).ne'
  exact ⟨log_pos (zm_E1 hE) ho0 h1, div_opow_log_pos E ho0, div_opow_log_lt o (zm_E1 hE),
    Ordinal.mod_lt o (opow_pos _ hE.pos).ne', div_add_mod o _⟩

/-- **Uniqueness of the decomposition.** -/
theorem zm_dec_uniq {k d r : Ordinal.{0}} (hd0 : d ≠ 0) (hdE : d < E) (hr : r < E ^ k) :
    log E (E ^ k * d + r) = k ∧ (E ^ k * d + r) / E ^ log E (E ^ k * d + r) = d ∧
      (E ^ k * d + r) % E ^ log E (E ^ k * d + r) = r := by
  have hl : log E (E ^ k * d + r) = k := by
    rw [log_opow_mul_add (zm_E1 hE) hd0 hr]
    have : log E d < 1 := (lt_opow_iff_log_lt (zm_E1 hE) hd0).1 (by rw [opow_one]; exact hdE)
    rw [Order.lt_one_iff.1 this, add_zero]
  have hk0 : E ^ k ≠ 0 := (opow_pos _ hE.pos).ne'
  refine ⟨hl, ?_, ?_⟩
  · rw [hl, Ordinal.mul_add_div d hk0 r, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [hl, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- The value is at least `E`. -/
theorem zm_dec_ge {k d r : Ordinal.{0}} (hk : 0 < k) (hd0 : d ≠ 0) : E ≤ E ^ k * d + r := by
  calc E = E ^ (1 : Ordinal.{0}) := (opow_one E).symm
    _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_pos.2 hk)
    _ = E ^ k * 1 := (mul_one _).symm
    _ ≤ E ^ k * d := mul_le_mul_right (one_le_iff_ne_zero.2 hd0) _
    _ ≤ _ := le_self_add

end Arith

/-- **The lexicographic order** of `P·d + r`, `r < P`. -/
theorem zm_lex {P d₁ d₂ r₁ r₂ : Ordinal.{0}} (hr₂ : r₂ < P)
    (h : P * d₁ + r₁ < P * d₂ + r₂) : d₁ < d₂ ∨ (d₁ = d₂ ∧ r₁ < r₂) := by
  rcases lt_trichotomy d₁ d₂ with hl | he | hg
  · exact Or.inl hl
  · subst he; exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
  · exfalso
    have : P * d₂ + r₂ < P * d₁ + r₁ := by
      calc P * d₂ + r₂ < P * d₂ + P := (add_lt_add_iff_left _).2 hr₂
        _ = P * (d₂ + 1) := (mul_add_one _ _).symm
        _ ≤ P * d₁ := mul_le_mul_right (Order.add_one_le_of_lt hg) _
        _ ≤ P * d₁ + r₁ := le_self_add
    exact absurd h (not_lt.2 this.le)

/-- `P·(d+1) ≤ P·d'` bound: `P·d + r < P·d'` for `d < d'`, `r < P`. -/
theorem zm_lt_next {P d d' r : Ordinal.{0}} (hd : d < d') (hr : r < P) : P * d + r < P * d' := by
  calc P * d + r < P * d + P := (add_lt_add_iff_left _).2 hr
    _ = P * (d + 1) := (mul_add_one _ _).symm
    _ ≤ P * d' := mul_le_mul_right (Order.add_one_le_of_lt hd) _

namespace ZmDS

variable (M : ZmDS)

open Classical in
/-- **The reading of the codes below `ε_{E+1}`**: `R(o)` below `E`, `V^{R(k)}·R(d) + R(r)` above. -/
noncomputable def sR (o x : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < M.E then M.R o x
  else if h2 : o < eN M.E then
    M.V x ^ sR (log M.E o) x * M.R (o / M.E ^ log M.E o) x + sR (o % M.E ^ log M.E o) x
  else o
termination_by o
decreasing_by
  · exact zm_log_lt M.E_E (not_lt.1 h) h2
  · exact zm_mod_lt M.E_E (not_lt.1 h)

open Classical in
/-- **The gate of the codes below `ε_{E+1}`.** -/
noncomputable def sG (o : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < M.E then M.G o
  else if h2 : o < eN M.E then
    max (sG (log M.E o)) (max (M.G (o / M.E ^ log M.E o)) (sG (o % M.E ^ log M.E o)))
  else M.Eg
termination_by o
decreasing_by
  · exact zm_log_lt M.E_E (not_lt.1 h) h2
  · exact zm_mod_lt M.E_E (not_lt.1 h)

theorem sR_lt {o : Ordinal.{0}} (h : o < M.E) (x : Ordinal.{0}) : M.sR o x = M.R o x := by
  rw [sR, dif_pos h]

theorem sG_lt {o : Ordinal.{0}} (h : o < M.E) : M.sG o = M.G o := by
  rw [sG, dif_pos h]

theorem sR_big {o : Ordinal.{0}} (h : eN M.E ≤ o) (x : Ordinal.{0}) : M.sR o x = o := by
  rw [sR, dif_neg (not_lt.2 ((lt_eN _).le.trans h)), dif_neg (not_lt.2 h)]

theorem sG_big {o : Ordinal.{0}} (h : eN M.E ≤ o) : M.sG o = M.Eg := by
  rw [sG, dif_neg (not_lt.2 ((lt_eN _).le.trans h)), dif_neg (not_lt.2 h)]

theorem sR_cnf {o : Ordinal.{0}} (h1 : M.E ≤ o) (h2 : o < eN M.E) (x : Ordinal.{0}) :
    M.sR o x = M.V x ^ M.sR (log M.E o) x * M.R (o / M.E ^ log M.E o) x + M.sR (o % M.E ^ log M.E o) x := by
  rw [sR, dif_neg (not_lt.2 h1), dif_pos h2]

theorem sG_cnf {o : Ordinal.{0}} (h1 : M.E ≤ o) (h2 : o < eN M.E) :
    M.sG o = max (M.sG (log M.E o)) (max (M.G (o / M.E ^ log M.E o)) (M.sG (o % M.E ^ log M.E o))) := by
  rw [sG, dif_neg (not_lt.2 h1), dif_pos h2]

/-- **The reading of `E^k·d + r`** (`1 ≤ k`, `0 < d < E`, `r < E^k`, below `ε_{E+1}`). -/
theorem sR_eq {k d r : Ordinal.{0}} (hk : 0 < k) (hd0 : d ≠ 0) (hdE : d < M.E) (hr : r < M.E ^ k)
    (hv : M.E ^ k * d + r < eN M.E) (x : Ordinal.{0}) :
    M.sR (M.E ^ k * d + r) x = M.V x ^ M.sR k x * M.R d x + M.sR r x := by
  obtain ⟨e1, e2, e3⟩ := zm_dec_uniq M.E_E hd0 hdE hr
  rw [M.sR_cnf (zm_dec_ge M.E_E hk hd0) hv, e2, e3, e1]

theorem sG_eq {k d r : Ordinal.{0}} (hk : 0 < k) (hd0 : d ≠ 0) (hdE : d < M.E) (hr : r < M.E ^ k)
    (hv : M.E ^ k * d + r < eN M.E) :
    M.sG (M.E ^ k * d + r) = max (M.sG k) (max (M.G d) (M.sG r)) := by
  obtain ⟨e1, e2, e3⟩ := zm_dec_uniq M.E_E hd0 hdE hr
  rw [M.sG_cnf (zm_dec_ge M.E_E hk hd0) hv, e2, e3, e1]

theorem sR_zero (x : Ordinal.{0}) : M.sR 0 x = 0 := by rw [M.sR_lt M.E_E.pos, M.R0]

theorem sG_zero : M.sG 0 = 0 := by rw [M.sG_lt M.E_E.pos, M.G0]

/-- The exponent of a code `E ≤ o < ε_{E+1}` is below `ε_{E+1}`, and so are the digits. -/
theorem parts_lt {o : Ordinal.{0}} (h1 : M.E ≤ o) (h2 : o < eN M.E) :
    log M.E o < o ∧ o % M.E ^ log M.E o < o :=
  ⟨zm_log_lt M.E_E h1 h2, zm_mod_lt M.E_E h1⟩

/-- **Every nonzero code has gate at least the base gate.** -/
theorem sG_Eg : ∀ o, o ≠ 0 → M.Eg ≤ M.sG o := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro ho0
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE]; exact M.Eg_le o ho0
  rcases lt_or_ge o (eN M.E) with hoN | hoN
  · obtain ⟨hk0, -, -, -, -⟩ := zm_dec M.E_E hoE
    obtain ⟨hko, -⟩ := M.parts_lt hoE hoN
    rw [M.sG_cnf hoE hoN]
    exact (IH _ hko hk0.ne').trans (le_max_left _ _)
  · rw [M.sG_big hoN]

/-! ## The order, one induction -/

/-- **The order statement** of a code `o < ε_{E+1}` with gate below `x`. -/
def OrdSt (x o : Ordinal.{0}) : Prop :=
  M.sR o x < eN (M.V x) ∧ (o ≠ 0 → 0 < M.sR o x) ∧
    (M.E ≤ o → M.sR o x < M.V x ^ (M.sR (log M.E o) x + 1)) ∧
    (∀ b, b < o → M.sG b < x → M.sR b x < M.sR o x)


section Ord

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem V_facts (hEg : M.Eg < x) : M.V x ∈ Tset x ∧ InE (M.V x) ∧ 0 < M.V x ∧ M.V x < eN (M.V x) := by
  obtain ⟨hT, hE, -, -⟩ := M.V_T x hx hx1 hEg
  exact ⟨hT, hE, hE.pos, lt_eN _⟩

omit hx hx1 in
theorem gates {o : Ordinal.{0}} (h1 : M.E ≤ o) (h2 : o < eN M.E) {Z : Ordinal.{0}} (hg : M.sG o < Z) :
    M.sG (log M.E o) < Z ∧ M.G (o / M.E ^ log M.E o) < Z ∧ M.sG (o % M.E ^ log M.E o) < Z := by
  rw [M.sG_cnf h1 h2] at hg
  exact ⟨(le_max_left _ _).trans_lt hg, ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hg,
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hg⟩

/-- `R(r) < V^{R(k)}` for `r < E^k` from the order statements below. -/
theorem bnd (hEg : M.Eg < x) {k r : Ordinal.{0}} (hk0 : 0 < k) (hk : k < eN M.E) (hgk : M.sG k < x)
    (hr : r < M.E ^ k) (hrN : r < eN M.E) (hgr : M.sG r < x) (hSk : M.OrdSt x k) (hSr : M.OrdSt x r) :
    M.sR r x < M.V x ^ M.sR k x := by
  obtain ⟨-, hVE, hV0, -⟩ := M.V_facts hx hx1 hEg
  have hpk : 0 < M.sR k x := hSk.2.1 hk0.ne'
  have hV1 : M.V x ≤ M.V x ^ M.sR k x := by
    have := opow_le_opow_right hV0 (one_le_iff_pos.2 hpk); rwa [opow_one] at this
  rcases lt_or_ge r M.E with hrE | hrE
  · rw [M.sR_lt hrE]
    rw [M.sG_lt hrE] at hgr
    exact (M.lt r x hx hx1 hrE hgr).trans_le hV1
  · have hr0 : r ≠ 0 := (M.E_E.pos.trans_le hrE).ne'
    have hlk : log M.E r < k := (lt_opow_iff_log_lt (zm_E1 M.E_E) hr0).1 hr
    obtain ⟨g1, -, -⟩ := M.gates hrE hrN hgr
    have hm := hSk.2.2.2 _ hlk g1
    calc M.sR r x < M.V x ^ (M.sR (log M.E r) x + 1) := hSr.2.2.1 hrE
      _ ≤ M.V x ^ M.sR k x := opow_le_opow_right hV0 (Order.add_one_le_of_lt hm)

/-- **THE ORDER, ONE INDUCTION ON THE CODE.** -/
theorem sR_main : ∀ o, o < eN M.E → M.sG o < x → M.OrdSt x o := by
  have hVN : M.V x < eN (M.V x) := lt_eN _
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoN hgo
  rcases lt_or_ge o M.E with hoE | hoE
  · -- below the base
    rw [M.sG_lt hoE] at hgo
    refine ⟨?_, fun h0 => ?_, fun h => absurd h (not_le.2 hoE), fun b hb hgb => ?_⟩
    · rw [M.sR_lt hoE]; exact (M.lt o x hx hx1 hoE hgo).trans hVN
    · rw [M.sR_lt hoE]; exact M.pos o x hx hx1 h0 hoE hgo
    · have hbE := hb.trans hoE
      rw [M.sG_lt hbE] at hgb
      rw [M.sR_lt hoE, M.sR_lt hbE]
      exact M.mono b o x hx hx1 hb hoE hgb hgo
  -- above the base
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨gk, gd, gr⟩ := M.gates hoE hoN hgo
  set k := log M.E o with hkdef
  set d := o / M.E ^ k with hddef
  set r := o % M.E ^ k with hrdef
  have hkN := hko.trans hoN
  have hrN := hro.trans hoN
  have hSk := IH k hko hkN gk
  have hSr := IH r hro hrN gr
  have hEg : M.Eg < x := (M.sG_Eg k hk0.ne').trans_lt gk
  obtain ⟨hVT, hVE, hV0, -⟩ := M.V_facts hx hx1 hEg
  have hval : M.sR o x = M.V x ^ M.sR k x * M.R d x + M.sR r x := M.sR_cnf hoE hoN x
  have hpk : 0 < M.sR k x := hSk.2.1 hk0.ne'
  have hRd0 : 0 < M.R d x := M.pos d x hx hx1 hd0.ne' hdE gd
  have hRdV : M.R d x < M.V x := M.lt d x hx hx1 hdE gd
  have hB := M.bnd hx hx1 hEg hk0 hkN gk hrk hrN gr hSk hSr
  have hVa : M.V x ^ M.sR k x < eN (M.V x) := zm_opow_lt (eN_E _) hVN hSk.1
  have hV1 : M.V x ≤ M.V x ^ M.sR k x := by
    have := opow_le_opow_right hV0 (one_le_iff_pos.2 hpk); rwa [opow_one] at this
  have hVaR : M.V x ^ M.sR k x ≤ M.V x ^ M.sR k x * M.R d x := by
    have := mul_le_mul_right (one_le_iff_pos.2 hRd0) (M.V x ^ M.sR k x); rwa [mul_one] at this
  have htop : M.sR o x < M.V x ^ (M.sR k x + 1) := by
    rw [hval, opow_add, opow_one]
    calc M.V x ^ M.sR k x * M.R d x + M.sR r x < M.V x ^ M.sR k x * M.R d x + M.V x ^ M.sR k x :=
          (add_lt_add_iff_left _).2 hB
      _ = M.V x ^ M.sR k x * (M.R d x + 1) := (mul_add_one _ _).symm
      _ ≤ M.V x ^ M.sR k x * M.V x := mul_le_mul_right (Order.add_one_le_of_lt hRdV) _
  refine ⟨?_, fun _ => ?_, fun _ => htop, fun b hb hgb => ?_⟩
  · rw [hval]
    exact (inE_indec (eN_E _)).add_lt (mul_lt_inE (eN_E _) hVa (hRdV.trans hVN)) (hB.trans hVa)
  · rw [hval]
    exact (mul_pos (opow_pos _ hV0) hRd0).trans_le le_self_add
  · -- the order
    have hbN := hb.trans hoN
    rcases lt_or_ge b M.E with hbE | hbE
    · rw [M.sG_lt hbE] at hgb
      rw [M.sR_lt hbE, hval]
      exact ((M.lt b x hx hx1 hbE hgb).trans_le (hV1.trans hVaR)).trans_le le_self_add
    obtain ⟨hk0', hd0', hdE', hrk', hdec'⟩ := zm_dec M.E_E hbE
    obtain ⟨hko', hro'⟩ := M.parts_lt hbE hbN
    obtain ⟨gk', gd', gr'⟩ := M.gates hbE hbN hgb
    set k' := log M.E b with hk'def
    set d' := b / M.E ^ k' with hd'def
    set r' := b % M.E ^ k' with hr'def
    have hk'N := hko'.trans hbN
    have hr'N := hro'.trans hbN
    have hSk' := IH k' (hko'.trans hb) hk'N gk'
    have hSr' := IH r' (hro'.trans hb) hr'N gr'
    have hval' : M.sR b x = M.V x ^ M.sR k' x * M.R d' x + M.sR r' x := M.sR_cnf hbE hbN x
    have hkk : k' ≤ k := by
      have h1 : M.E ^ k' ≤ b := opow_log_le_self M.E (M.E_E.pos.trans_le hbE).ne'
      have h2 : o < M.E ^ (k + 1) := by
        rw [opow_add, opow_one, ← hdec]
        exact zm_lt_next hdE hrk
      have h3 : M.E ^ k' < M.E ^ (k + 1) := h1.trans_lt (hb.trans h2)
      exact Order.lt_add_one_iff.1 ((opow_lt_opow_iff_right (zm_E1 M.E_E)).1 h3)
    rcases hkk.lt_or_eq with hlt | heq
    · have hm := hSk.2.2.2 k' hlt gk'
      calc M.sR b x < M.V x ^ (M.sR k' x + 1) := (IH b hb hbN hgb).2.2.1 hbE
        _ ≤ M.V x ^ M.sR k x := opow_le_opow_right hV0 (Order.add_one_le_of_lt hm)
        _ ≤ M.sR o x := by rw [hval]; exact hVaR.trans le_self_add
    · -- same exponent
      have hb' : M.E ^ k' * d' + r' < M.E ^ k * d + r := by
        rw [hdec', hdec]; exact hb
      rw [heq] at hb' hrk'
      rcases zm_lex hrk hb' with hdd | ⟨hdd, hrr⟩
      · have hB' := M.bnd hx hx1 hEg hk0 hkN gk hrk' hr'N gr' hSk hSr'
        rw [hval', heq, hval]
        calc M.V x ^ M.sR k x * M.R d' x + M.sR r' x < M.V x ^ M.sR k x * M.R d' x + M.V x ^ M.sR k x :=
              (add_lt_add_iff_left _).2 hB'
          _ = M.V x ^ M.sR k x * (M.R d' x + 1) := (mul_add_one _ _).symm
          _ ≤ M.V x ^ M.sR k x * M.R d x :=
              mul_le_mul_right (Order.add_one_le_of_lt (M.mono d' d x hx hx1 hdd hdE gd' gd)) _
          _ ≤ _ := le_self_add
      · rw [hval', heq, hdd, hval]
        exact (add_lt_add_iff_left _).2 (hSr.2.2.2 r' hrr gr')

end Ord

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
