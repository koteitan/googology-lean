import Googology.Trans.PoR.InaccPsi.R2.ZmSt

/-!
# ZmSu: THE GENERIC STEP — SUCCESSORS, THE GATE ON SUCCESSORS, LIMITS

* `zm_opow_eq` (`E^k = ω^{E·k}`), `zm_opow_prin`, `zm_prin_lim`;
* `ZmDS.sR_succ` (**`R(o+1) = R(o) + 1` for every `o`**), `ZmDS.sG_le_succ`, `ZmDS.sG_succ_lt`,
  `ZmDS.sR_lim` (**a limit code reads a limit**).

No new axiom, no new definition.
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

theorem zm_opow_eq {E : Ordinal.{0}} (hE : InE E) (k : Ordinal.{0}) : E ^ k = ω ^ (E * k) := by
  conv_lhs => rw [← (show ω ^ E = E from hE)]
  rw [← opow_mul]

theorem zm_opow_prin {E : Ordinal.{0}} (hE : InE E) (k : Ordinal.{0}) : IsPrincipal (· + ·) (E ^ k) := by
  rw [zm_opow_eq hE]; exact isPrincipal_add_omega0_opow _

theorem zm_one_lt_opow {E k : Ordinal.{0}} (hE : InE E) (hk : 0 < k) : (1 : Ordinal.{0}) < E ^ k :=
  (lu_one_lt_E hE).trans_le (by
    have := opow_le_opow_right hE.pos (one_le_iff_pos.2 hk); rwa [opow_one] at this)

/-- An additively principal ordinal above `1` is a limit. -/
theorem zm_prin_lim {P : Ordinal.{0}} (hP : IsPrincipal (· + ·) P) (h1 : 1 < P) : IsSuccLimit P := by
  rcases zero_or_succ_or_isSuccLimit P with h0 | ⟨s, hs⟩ | hl
  · rw [h0] at h1; exact absurd h1 (not_lt.2 zero_le)
  · exfalso
    have hsP : s < P := by rw [← hs]; exact Order.lt_succ s
    have h2 : s + 1 < P := hP hsP h1
    rw [← succ_eq_add_one, hs] at h2
    exact lt_irrefl _ h2
  · exact hl

namespace ZmDS

variable (M : ZmDS)

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

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
