import Googology.Trans.PoR.InaccPsi.R2.QcTo
import Googology.Trans.PoR.InaccPsi.R2.ZmCo

/-!
# QcSt: THE HEREDITARY STEP OF A DIGIT SYSTEM BELOW `B₂` — READINGS, ORDER, SUCCESSORS, LIMITS, COFINALITY

`Zm.ZmDS.sR`, `Zm.ZmDS.sG` and their facts (`Zm.ZmSt`, `Zm.ZmSu`, `Zm.ZmCo`) for `Qc.QDS`: the codes `E ≤ o < ε_{E+1}`,
`o = E^k·d + r`, read `V(x)^{R(k)(x)}·R(d)(x) + R(r)(x)` with the gate `max (G k) (max (G d) (G r))`.  The proofs are
those of `Zm`: they use only the fields shared by `Zm.ZmDS` and `Qc.QDS`.

* `QDS.sR`, `QDS.sG`, `QDS.sR_lt`, `QDS.sR_cnf`, `QDS.sR_big`, `QDS.sR_eq`, `QDS.sG_eq`, `QDS.parts_lt`, `QDS.sG_Eg`,
  `QDS.OrdSt`, `QDS.V_facts`, `QDS.gates`, `QDS.sR_main` (**the bound, positivity, the top bound and the order**);
* `QDS.sR_succ`, `QDS.sG_le_succ`, `QDS.sG_succ_lt`, `QDS.sR_lim`;
* `QDS.R_one`, `QDS.sR_eqZ`, `QDS.sG_leZ`, `QDS.sR_cof` (**cofinality**).

No new axiom.  New definitions: `QDS.sR`, `QDS.sG`, `QDS.OrdSt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Zm

namespace QDS

/-! ### As `Zm.ZmSt` -/

variable (M : QDS)

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


/-! ### As `Zm.ZmSu` -/

variable (M : QDS)

/-- **`R(o+1) = R(o) + 1` for every `o`.** -/
theorem sR_succ : ∀ o x, M.sR (o + 1) x = M.sR o x + 1 := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro x
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sR_lt hoE, M.sR_lt (M.E_lim.add_one_lt hoE), M.succ]
  rcases lt_or_ge o (eN M.E) with hoN | hoN
  · obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
    obtain ⟨-, hro⟩ := M.parts_lt hoE hoN
    set k := log M.E o
    set d := o / M.E ^ k
    set r := o % M.E ^ k
    have hr1 : r + 1 < M.E ^ k := zm_opow_prin M.E_E k hrk (zm_one_lt_opow M.E_E hk0)
    have hoN1 : o + 1 < eN M.E := (ev_isSuccLimit_of_inE (eN_E _)).add_one_lt hoN
    rw [← hdec] at hoN hoN1 ⊢
    rw [add_assoc, M.sR_eq hk0 hd0.ne' hdE hr1 (by rw [← add_assoc]; exact hoN1),
      M.sR_eq hk0 hd0.ne' hdE hrk hoN, IH r hro x, add_assoc]
  · rw [M.sR_big hoN, M.sR_big (hoN.trans (lt_add_one o).le)]

theorem sG_le_succ : ∀ o, M.sG o ≤ M.sG (o + 1) := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE, M.sG_lt (M.E_lim.add_one_lt hoE)]; exact M.g_le o
  rcases lt_or_ge o (eN M.E) with hoN | hoN
  · obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
    obtain ⟨-, hro⟩ := M.parts_lt hoE hoN
    set k := log M.E o
    set d := o / M.E ^ k
    set r := o % M.E ^ k
    have hr1 : r + 1 < M.E ^ k := zm_opow_prin M.E_E k hrk (zm_one_lt_opow M.E_E hk0)
    have hoN1 : o + 1 < eN M.E := (ev_isSuccLimit_of_inE (eN_E _)).add_one_lt hoN
    rw [← hdec] at hoN hoN1 ⊢
    rw [add_assoc, M.sG_eq hk0 hd0.ne' hdE hr1 (by rw [← add_assoc]; exact hoN1),
      M.sG_eq hk0 hd0.ne' hdE hrk hoN]
    exact max_le_max le_rfl (max_le_max le_rfl (IH r hro))
  · rw [M.sG_big hoN, M.sG_big (hoN.trans (lt_add_one o).le)]

theorem sG_succ_lt : ∀ o Z, IsSuccLimit Z → M.Eg < Z → M.sG o < Z → M.sG (o + 1) < Z := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro Z hZ hEgZ hg
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg; rw [M.sG_lt (M.E_lim.add_one_lt hoE)]; exact M.g_succ o Z hZ hEgZ hg
  rcases lt_or_ge o (eN M.E) with hoN | hoN
  · obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
    obtain ⟨-, hro⟩ := M.parts_lt hoE hoN
    obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
    set k := log M.E o
    set d := o / M.E ^ k
    set r := o % M.E ^ k
    have hr1 : r + 1 < M.E ^ k := zm_opow_prin M.E_E k hrk (zm_one_lt_opow M.E_E hk0)
    have hoN1 : o + 1 < eN M.E := (ev_isSuccLimit_of_inE (eN_E _)).add_one_lt hoN
    rw [← hdec] at hoN1 ⊢
    rw [add_assoc, M.sG_eq hk0 hd0.ne' hdE hr1 (by rw [← add_assoc]; exact hoN1)]
    exact max_lt g1 (max_lt g2 (IH r hro Z hZ hEgZ g3))
  · rw [M.sG_big ((hoN.trans (lt_add_one o).le))]; exact hEgZ

/-- **A limit code reads a limit.** -/
theorem sR_lim : ∀ o x, InE x → x < Om1 → IsSuccLimit o → o < eN M.E → M.sG o < x → IsSuccLimit (M.sR o x) := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro x hx hx1 hl hoN hg
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg; rw [M.sR_lt hoE]; exact M.lim o x hx hx1 hl hoE hg
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
  rw [M.sR_cnf hoE hoN x]
  set k := log M.E o
  set d := o / M.E ^ k
  set r := o % M.E ^ k
  rcases zero_or_succ_or_isSuccLimit r with h0 | ⟨s, hs⟩ | hrl
  · rw [h0, M.sR_zero, add_zero]
    obtain ⟨-, hVE, hV0, -⟩ := M.V_facts hx hx1 ((M.sG_Eg _ hk0.ne').trans_lt g1)
    have hSk := M.sR_main hx hx1 k (hko.trans hoN) g1
    have hpk : 0 < M.sR k x := hSk.2.1 hk0.ne'
    have hRd0 : 0 < M.R d x := M.pos d x hx hx1 hd0.ne' hdE g2
    have hVa : IsSuccLimit (M.V x ^ M.sR k x) :=
      zm_prin_lim (zm_opow_prin hVE _) (zm_one_lt_opow hVE hpk)
    exact isSuccLimit_mul_left hVa hRd0
  · exfalso
    have : o = Order.succ (M.E ^ k * d + s) := by
      rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs, hdec]
    rw [this] at hl
    exact Order.not_isSuccLimit_succ _ hl
  · exact isSuccLimit_add _ (IH r hro x hx hx1 hrl (hro.trans hoN) g3)


/-! ### As `Zm.ZmCo` -/

variable (M : QDS)

theorem R_one (x : Ordinal.{0}) : M.R 1 x = 1 := by
  have := M.succ 0 x; rwa [zero_add, M.R0, zero_add] at this

/-- **The reading of `E^k·d + r`** for every `k`, `d < E`, `r < E^k`. -/
theorem sR_eqZ {k d r : Ordinal.{0}} (hdE : d < M.E) (hr : r < M.E ^ k) (hv : M.E ^ k * d + r < eN M.E)
    (x : Ordinal.{0}) : M.sR (M.E ^ k * d + r) x = M.V x ^ M.sR k x * M.R d x + M.sR r x := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [mul_zero, zero_add, M.R0, mul_zero, zero_add]
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [opow_zero] at hr
    rw [Order.lt_one_iff.1 hr, opow_zero, one_mul, add_zero, M.sR_zero, opow_zero, one_mul, add_zero,
      M.sR_lt hdE]
  · exact M.sR_eq (pos_iff_ne_zero.2 hk0) hd0 hdE hr hv x

theorem sG_leZ {k d r : Ordinal.{0}} (hdE : d < M.E) (hr : r < M.E ^ k) (hv : M.E ^ k * d + r < eN M.E) :
    M.sG (M.E ^ k * d + r) ≤ max (M.sG k) (max (M.G d) (M.sG r)) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [mul_zero, zero_add]; exact (le_max_right _ _).trans (le_max_right _ _)
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [opow_zero] at hr
    rw [Order.lt_one_iff.1 hr, opow_zero, one_mul, add_zero, M.sG_lt hdE]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (M.sG_eq (pos_iff_ne_zero.2 hk0) hd0 hdE hr hv).le

/-- **COFINALITY**: below the reading of a limit code every ordinal is below the reading of a smaller code. -/
theorem sR_cof : ∀ o x, InE x → x < Om1 → IsSuccLimit o → o < eN M.E → M.sG o < x →
    ∀ ν, ν < M.sR o x → ∃ b, b < o ∧ M.sG b < x ∧ ν ≤ M.sR b x := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro x hx hx1 hl hoN hg ν hν
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg
    rw [M.sR_lt hoE] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := M.cof o x hx hx1 hl hoE hg ν hν
    have hbE := hb.trans hoE
    exact ⟨b, hb, by rw [M.sG_lt hbE]; exact hgb, by rw [M.sR_lt hbE]; exact hνb⟩
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
  rw [M.sR_cnf hoE hoN x] at hν
  set k := log M.E o
  set d := o / M.E ^ k
  set r := o % M.E ^ k
  have hEg : M.Eg < x := (M.sG_Eg _ hk0.ne').trans_lt g1
  obtain ⟨-, hVE, hV0, -⟩ := M.V_facts hx hx1 hEg
  have hVl : IsSuccLimit (M.V x) := ev_isSuccLimit_of_inE hVE
  -- the candidate codes `E^k·d' + y` below `o`
  have hcand : ∀ d' y, d' < M.E → y < M.E ^ k → M.E ^ k * d' + y < o → M.G d' < x → M.sG y < x →
      M.sR (M.E ^ k * d' + y) x = M.V x ^ M.sR k x * M.R d' x + M.sR y x ∧
        M.sG (M.E ^ k * d' + y) < x := fun d' y hd'E hy hlt hgd hgy => by
    have hvN := hlt.trans hoN
    exact ⟨M.sR_eqZ hd'E hy hvN x, (M.sG_leZ hd'E hy hvN).trans_lt (max_lt g1 (max_lt hgd hgy))⟩
  have hEk0 : (0 : Ordinal.{0}) < M.E ^ k := opow_pos _ M.E_E.pos
  rcases zero_or_succ_or_isSuccLimit r with hr0 | ⟨s, hs⟩ | hrl
  · -- `o = E^k·d`
    rw [hr0, M.sR_zero, add_zero] at hν
    have hoeq : o = M.E ^ k * d := by rw [← hdec, hr0, add_zero]
    rcases zero_or_succ_or_isSuccLimit d with hd00 | ⟨d₀, hd₀⟩ | hdl
    · exact absurd hd00 hd0.ne'
    · -- a successor digit
      rw [succ_eq_add_one] at hd₀
      have hd₀E : d₀ < M.E := (lt_add_one d₀).trans (hd₀ ▸ hdE)
      have hgd₀ : M.G d₀ < x := (M.g_le d₀).trans_lt (hd₀ ▸ g2)
      rw [← hd₀, M.succ, mul_add_one] at hν
      have hlt0 : ∀ y, y < M.E ^ k → M.E ^ k * d₀ + y < o := fun y hy => by
        rw [hoeq, ← hd₀]; exact zm_lt_next (lt_add_one d₀) hy
      rcases le_or_gt ν (M.V x ^ M.sR k x * M.R d₀ x) with hνD | hDν
      · obtain ⟨e1, e2⟩ := hcand d₀ 0 hd₀E hEk0 (hlt0 0 hEk0) hgd₀ (by rw [M.sG_zero]; exact hx.pos)
        refine ⟨_, hlt0 0 hEk0, e2, ?_⟩
        rw [e1, M.sR_zero, add_zero]; exact hνD
      obtain ⟨ν'', rfl⟩ := exists_add_of_le hDν.le
      have hν'' : ν'' < M.V x ^ M.sR k x := (add_lt_add_iff_left _).1 hν
      rcases zero_or_succ_or_isSuccLimit k with hk00 | ⟨k₀, hk₀⟩ | hkl
      · exact absurd hk00 hk0.ne'
      · -- a successor exponent: the block `V^{R(k₀)}·V`
        rw [succ_eq_add_one] at hk₀
        have hk₀k : k₀ < k := hk₀ ▸ lt_add_one k₀
        have hgk₀ : M.sG k₀ < x := (M.sG_le_succ k₀).trans_lt (hk₀ ▸ g1)
        rw [← hk₀, M.sR_succ, opow_add, opow_one] at hν''
        obtain ⟨u, hu, hνu⟩ := (lt_mul_iff_of_isSuccLimit hVl).1 hν''
        obtain ⟨t, htE, hgt, hut⟩ := M.top x hx hx1 hEg u hu
        have ht0 : t ≠ 0 := by
          rintro rfl
          rw [M.R0] at hut
          rw [le_zero_iff.1 hut, mul_zero] at hνu
          exact absurd hνu (not_lt.2 zero_le)
        have hy : M.E ^ k₀ * t < M.E ^ k := by
          rw [← hk₀, opow_add, opow_one]
          exact (mul_lt_mul_iff_right₀ (opow_pos _ M.E_E.pos)).2 htE
        have hyN : M.E ^ k₀ * t + 0 < eN M.E := by
          rw [add_zero]; exact hy.trans ((opow_le_opow_right M.E_E.pos le_rfl).trans_lt
            ((opow_log_le_self M.E (M.E_E.pos.trans_le hoE).ne').trans_lt hoN))
        have hgy : M.sG (M.E ^ k₀ * t) < x := by
          have h' := M.sG_leZ htE (opow_pos _ M.E_E.pos : (0 : Ordinal.{0}) < M.E ^ k₀) hyN
          rw [add_zero] at h'
          refine h'.trans_lt (max_lt hgk₀ (max_lt hgt (by rw [M.sG_zero]; exact hx.pos)))
        obtain ⟨e1, e2⟩ := hcand d₀ _ hd₀E hy (hlt0 _ hy) hgd₀ hgy
        refine ⟨_, hlt0 _ hy, e2, ?_⟩
        rw [e1]
        have hyv := M.sR_eqZ htE (opow_pos _ M.E_E.pos) hyN x
        rw [add_zero, M.sR_zero, add_zero] at hyv
        rw [hyv]
        refine (add_le_add_iff_left _).2 (hνu.le.trans (mul_le_mul_right hut _))
      · -- a limit exponent
        have hal : IsSuccLimit (M.sR k x) := M.sR_lim k x hx hx1 hkl (hko.trans hoN) g1
        obtain ⟨a', ha', hνa'⟩ := (lt_opow_of_isSuccLimit hV0.ne' hal).1 hν''
        obtain ⟨k', hk', hgk', hak'⟩ := IH k hko x hx hx1 hkl (hko.trans hoN) g1 a' ha'
        have hy : M.E ^ k' < M.E ^ k := (opow_lt_opow_iff_right (zm_E1 M.E_E)).2 hk'
        have hyN : M.E ^ k' * 1 + 0 < eN M.E := by
          rw [mul_one, add_zero]
          exact hy.trans ((opow_log_le_self M.E (M.E_E.pos.trans_le hoE).ne').trans_lt hoN)
        have hg1 : M.G 1 < x := by
          have := M.g_succ 0 x hxl hEg (by rw [M.G0]; exact hx.pos); rwa [zero_add] at this
        have hgy : M.sG (M.E ^ k') < x := by
          have h' := M.sG_leZ M.one_lt_E (opow_pos _ M.E_E.pos) hyN
          rw [mul_one, add_zero] at h'
          exact h'.trans_lt (max_lt hgk' (max_lt hg1 (by rw [M.sG_zero]; exact hx.pos)))
        obtain ⟨e1, e2⟩ := hcand d₀ _ hd₀E hy (hlt0 _ hy) hgd₀ hgy
        refine ⟨_, hlt0 _ hy, e2, ?_⟩
        rw [e1]
        have hyv := M.sR_eqZ M.one_lt_E (opow_pos _ M.E_E.pos) hyN x
        rw [mul_one, add_zero, M.R_one, mul_one, M.sR_zero, add_zero] at hyv
        rw [hyv]
        exact (add_le_add_iff_left _).2 (hνa'.le.trans (opow_le_opow_right hV0 hak'))
    · -- a limit digit
      have hRl : IsSuccLimit (M.R d x) := M.lim d x hx hx1 hdl hdE g2
      obtain ⟨u, hu, hνu⟩ := (lt_mul_iff_of_isSuccLimit hRl).1 hν
      obtain ⟨d', hd', hgd', hud'⟩ := M.cof d x hx hx1 hdl hdE g2 u hu
      have hlt : M.E ^ k * d' + 0 < o := by
        rw [add_zero, hoeq]; exact (mul_lt_mul_iff_right₀ hEk0).2 hd'
      obtain ⟨e1, e2⟩ := hcand d' 0 (hd'.trans hdE) hEk0 hlt hgd' (by rw [M.sG_zero]; exact hx.pos)
      refine ⟨_, hlt, e2, ?_⟩
      rw [e1, M.sR_zero, add_zero]
      exact hνu.le.trans (mul_le_mul_right hud' _)
  · -- a successor rest: impossible
    exfalso
    have : o = Order.succ (M.E ^ k * d + s) := by
      rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs, hdec]
    rw [this] at hl
    exact Order.not_isSuccLimit_succ _ hl
  · -- a limit rest
    have hlt : ∀ y, y < r → M.E ^ k * d + y < o := fun y hy => by
      rw [← hdec]; exact (add_lt_add_iff_left _).2 hy
    rcases le_or_gt ν (M.V x ^ M.sR k x * M.R d x) with hνD | hDν
    · obtain ⟨e1, e2⟩ := hcand d 0 hdE hEk0 (hlt 0 hrl.bot_lt) g2 (by rw [M.sG_zero]; exact hx.pos)
      refine ⟨_, hlt 0 hrl.bot_lt, e2, ?_⟩
      rw [e1, M.sR_zero, add_zero]; exact hνD
    obtain ⟨ν', rfl⟩ := exists_add_of_le hDν.le
    have hν' : ν' < M.sR r x := (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb', hgb', hνb'⟩ := IH r hro x hx hx1 hrl (hro.trans hoN) g3 ν' hν'
    obtain ⟨e1, e2⟩ := hcand d b' hdE (hb'.trans hrk) (hlt b' hb') g2 hgb'
    refine ⟨_, hlt b' hb', e2, ?_⟩
    rw [e1]; exact (add_le_add_iff_left _).2 hνb'


end QDS

end Googology.Trans.PoR.InaccPsi.R2.Qc
