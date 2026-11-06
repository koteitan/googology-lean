import Googology.Trans.PoR.InaccPsi.R2.ZmCu

/-!
# Nb: THE BRACKETS OVER A PSEUDO-BASE `P = φ(2, p)` AND THE GLOBAL READING ABOVE IT (`Zm.ZmCx` over any `P`)

`P = φ(2, p)`, `Z = φ(2, p+1)` (the next value of `φ(2, ·)`).  The codes `P ≤ o < Z` lie in the brackets
`[φ(1, P+n), φ(1, P+n+1))`, `n < o` (`nb_bracket`); with a reading `R₀` and a gate `G₀` below `P` and the reading `V_P(x)`
of `P`, a code `o = E^k·d + r` of the bracket of `n` (`E = φ(1, P+n)`) reads `φ(1, V_P(x) + R(n))^{R(k)}·R(d) + R(r)`.
For `p = B_Γ` (`φ(2, B_Γ) = B_Γ`), `R₀ = Yr`, `V_P = D` this is `Zm.zmHR`.

* `nb_fixP` (`φ(1, P) = P`), `nb_noFix` (**no fixed point of `φ(1, ·)` in `(P, Z)`**), `nb_veb_lt_Z`, `nb_idx_lt`
  (`c < φ(1, P + c)` for `c < Z`), `nbN`, `nbBE`, `nbN_eq`, `nbBE_eq`, `nb_bracket`, `nb_guards`;
* `nbHR`, `nbHG` (**the global reading and gate over `P`**), `nbHR_lt`, `nbHG_lt`, `nbHR_cnf`, `nbHG_cnf`, `nbHG_idx`,
  `nb_succ_dec`, `nbHG_le_succ`, `nbHG_succ_lt`, `nbHR_succ` (from the same facts below `P`).

No new axiom.  New definitions: `nbN`, `nbBE`, `nbHR`, `nbHG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Nb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Zm

/-! ## The brackets over `P = φ(2, p)` -/

theorem nb_fixP (p : Ordinal.{0}) : veblen 1 (veblen 2 p) = veblen 2 p := veblen_veblen_of_lt one_lt_two p

/-- **No fixed point of `φ(1, ·)` strictly between `φ(2, p)` and `φ(2, p+1)`.** -/
theorem nb_noFix {p y : Ordinal.{0}} (h1 : veblen 2 p < y) (h2 : y < veblen 2 (p + 1)) : veblen 1 y ≠ y := by
  intro hy
  obtain ⟨b, rfl⟩ := zm_fix_range hy
  have hb1 := (isNormal_veblen 2).strictMono.lt_iff_lt.1 h1
  have hb2 := (isNormal_veblen 2).strictMono.lt_iff_lt.1 h2
  exact absurd (Order.add_one_le_of_lt hb1) (not_le.2 hb2)

theorem nbZ_fix (p : Ordinal.{0}) : veblen 1 (veblen 2 (p + 1)) = veblen 2 (p + 1) := nb_fixP (p + 1)

theorem nbP_lt_Z (p : Ordinal.{0}) : veblen 2 p < veblen 2 (p + 1) := (isNormal_veblen 2).strictMono (lt_add_one p)

theorem nbP_pos (p : Ordinal.{0}) : 0 < veblen 2 p := veblen_pos

/-- `φ(1, P + c)` stays below `Z` for `c < Z`. -/
theorem nb_veb_lt_Z {p c : Ordinal.{0}} (hc : c < veblen 2 (p + 1)) :
    veblen 1 (veblen 2 p + c) < veblen 2 (p + 1) := by
  rw [← nbZ_fix p]
  exact (isNormal_veblen 1).strictMono ((inE_indec (zm_fix_E (nbZ_fix p))).add_lt (nbP_lt_Z p) hc)

/-- **An index below `Z` is below its base**: `c < φ(1, P + c)`. -/
theorem nb_idx_lt {p c : Ordinal.{0}} (hc : c < veblen 2 (p + 1)) : c < veblen 1 (veblen 2 p + c) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, nb_fixP]; exact nbP_pos p
  refine lt_of_le_of_ne (le_add_self.trans (right_le_veblen _ _)) fun e => ?_
  have h2 : veblen 2 p + c ≤ veblen 1 (veblen 2 p + c) := right_le_veblen _ _
  have e1 : veblen 2 p + c = c := le_antisymm (h2.trans_eq e.symm) le_add_self
  rw [e1] at e
  have hB : veblen 2 p < c := by
    calc veblen 2 p < veblen 2 p + c := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hc0)
      _ = c := e1
  exact nb_noFix hB hc e.symm

/-- **The index of the bracket** `[φ(1, P+n), φ(1, P+n+1))` of `o`. -/
noncomputable def nbN (p o : Ordinal.{0}) : Ordinal.{0} := sInf {n | o < veblen 1 (veblen 2 p + (n + 1))}

/-- **The base of the bracket of `o`.** -/
noncomputable def nbBE (p o : Ordinal.{0}) : Ordinal.{0} := veblen 1 (veblen 2 p + nbN p o)

theorem nbN_eq {p o n : Ordinal.{0}} (h1 : veblen 1 (veblen 2 p + n) ≤ o)
    (h2 : o < veblen 1 (veblen 2 p + (n + 1))) : nbN p o = n := by
  refine le_antisymm (csInf_le (OrderBot.bddBelow _) h2) (le_csInf ⟨n, h2⟩ fun m hm => ?_)
  by_contra hmn
  push Not at hmn
  have : veblen 1 (veblen 2 p + (m + 1)) ≤ veblen 1 (veblen 2 p + n) :=
    (isNormal_veblen 1).strictMono.monotone (add_le_add le_rfl (add_one_le_of_lt hmn))
  exact absurd (lt_of_lt_of_le hm (this.trans h1)) (lt_irrefl _)

theorem nbBE_eq {p o n : Ordinal.{0}} (h1 : veblen 1 (veblen 2 p + n) ≤ o)
    (h2 : o < veblen 1 (veblen 2 p + (n + 1))) : nbBE p o = veblen 1 (veblen 2 p + n) := by
  unfold nbBE; rw [nbN_eq h1 h2]

/-- **The bracket of a code `P ≤ o < Z`**: `φ(1, P + n) ≤ o < φ(1, P + n + 1)` with `n = nbN p o < o`. -/
theorem nb_bracket {p o : Ordinal.{0}} (h1 : veblen 2 p ≤ o) (h2 : o < veblen 2 (p + 1)) :
    veblen 1 (veblen 2 p + nbN p o) ≤ o ∧ o < veblen 1 (veblen 2 p + (nbN p o + 1)) ∧ nbN p o < o := by
  set P := veblen 2 p with hPdef
  have hne : o ∈ {n | o < veblen 1 (P + (n + 1))} :=
    (nb_idx_lt h2).trans ((isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (lt_add_one o)))
  have hmem : o < veblen 1 (P + (nbN p o + 1)) :=
    csInf_mem (s := {n | o < veblen 1 (P + (n + 1))}) ⟨o, hne⟩
  have hle : ∀ m, o < veblen 1 (P + (m + 1)) → nbN p o ≤ m := fun m hm => csInf_le (OrderBot.bddBelow _) hm
  have hlow : veblen 1 (P + nbN p o) ≤ o := by
    by_contra hc
    push Not at hc
    rcases zero_or_succ_or_isSuccLimit (nbN p o) with h0 | ⟨m, hm⟩ | hl
    · rw [h0, add_zero, nb_fixP] at hc; exact absurd h1 (not_le.2 hc)
    · rw [succ_eq_add_one] at hm
      rw [← hm] at hc
      exact absurd (hle m hc) (not_le.2 (hm ▸ lt_add_one m))
    · obtain ⟨c', hc', hoc'⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ hl)).1 hc
      have hm : ∃ m, m < nbN p o ∧ o < veblen 1 (P + (m + 1)) := by
        rcases lt_or_ge c' P with h | h
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
  have := (isNormal_veblen 1).strictMono.monotone (add_le_add (le_refl P) hc)
  exact absurd (hlow.trans_lt' (lt_of_lt_of_le (nb_idx_lt h2) this)) (lt_irrefl _)

/-- The guards in the bracket of `n`. -/
theorem nb_guards {p o n : Ordinal.{0}} (h1 : veblen 1 (veblen 2 p + n) ≤ o)
    (h2 : o < veblen 1 (veblen 2 p + (n + 1))) :
    veblen 2 p ≤ o ∧ nbBE p o = veblen 1 (veblen 2 p + n) ∧ nbN p o = n ∧ (log (nbBE p o) o < o ∧
      o / nbBE p o ^ log (nbBE p o) o < o ∧ o % nbBE p o ^ log (nbBE p o) o < o) := by
  have hE := zm_veb_E (veblen 2 p + n)
  have hB : veblen 2 p ≤ veblen 1 (veblen 2 p + n) := le_self_add.trans (right_le_veblen _ _)
  have he := nbBE_eq h1 h2
  have h2' : o < eN (veblen 1 (veblen 2 p + n)) := by rw [Go.go_eN_veb, add_assoc]; exact h2
  refine ⟨hB.trans h1, he, nbN_eq h1 h2, ?_⟩
  rw [he]
  exact ⟨zm_log_lt hE h1 h2', (div_opow_log_lt o (zm_E1 hE)).trans_le h1, zm_mod_lt hE h1⟩

theorem nb_guards2 {p o : Ordinal.{0}} (h1 : veblen 2 p ≤ o) (h2 : o < veblen 2 (p + 1)) :
    nbBE p o = veblen 1 (veblen 2 p + nbN p o) ∧ (nbN p o < o ∧ log (nbBE p o) o < o ∧
      o / nbBE p o ^ log (nbBE p o) o < o ∧ o % nbBE p o ^ log (nbBE p o) o < o) := by
  obtain ⟨b1, b2, b3⟩ := nb_bracket h1 h2
  obtain ⟨-, he, -, hg⟩ := nb_guards b1 b2
  exact ⟨he, b3, hg⟩

/-! ## The global reading and gate over `P` -/

open Classical in
/-- **THE GLOBAL READING OVER `P`**: `R₀` below `P`; in the bracket of `n` (`n < o`)
`φ(1, V_P(x) + R(n))^{R(k)}·R(d) + R(r)`. -/
noncomputable def nbHR (p : Ordinal.{0}) (R₀ : Ordinal.{0} → Ordinal.{0} → Ordinal.{0})
    (VP : Ordinal.{0} → Ordinal.{0}) (o x : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < veblen 2 p then R₀ o x
  else if h2 : nbN p o < o ∧ log (nbBE p o) o < o ∧ o / nbBE p o ^ log (nbBE p o) o < o ∧
      o % nbBE p o ^ log (nbBE p o) o < o then
    veblen 1 (VP x + nbHR p R₀ VP (nbN p o) x) ^ nbHR p R₀ VP (log (nbBE p o) o) x *
      nbHR p R₀ VP (o / nbBE p o ^ log (nbBE p o) o) x + nbHR p R₀ VP (o % nbBE p o ^ log (nbBE p o) o) x
  else o
termination_by o
decreasing_by
  all_goals first
    | exact h2.1
    | exact h2.2.1
    | exact h2.2.2.1
    | exact h2.2.2.2

open Classical in
/-- **THE GLOBAL GATE OVER `P`** (the gate of the index included). -/
noncomputable def nbHG (p : Ordinal.{0}) (G₀ : Ordinal.{0} → Ordinal.{0}) (o : Ordinal.{0}) : Ordinal.{0} :=
  if h : o < veblen 2 p then G₀ o
  else if h2 : nbN p o < o ∧ log (nbBE p o) o < o ∧ o / nbBE p o ^ log (nbBE p o) o < o ∧
      o % nbBE p o ^ log (nbBE p o) o < o then
    max (nbHG p G₀ (nbN p o)) (max (nbHG p G₀ (log (nbBE p o) o)) (max (nbHG p G₀ (o / nbBE p o ^ log (nbBE p o) o))
      (nbHG p G₀ (o % nbBE p o ^ log (nbBE p o) o))))
  else 0
termination_by o
decreasing_by
  all_goals first
    | exact h2.1
    | exact h2.2.1
    | exact h2.2.2.1
    | exact h2.2.2.2

section Glob

variable {p : Ordinal.{0}} {R₀ : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}} {VP : Ordinal.{0} → Ordinal.{0}}
  {G₀ : Ordinal.{0} → Ordinal.{0}}

theorem nbHR_lt {o : Ordinal.{0}} (h : o < veblen 2 p) (x : Ordinal.{0}) : nbHR p R₀ VP o x = R₀ o x := by
  rw [nbHR, dif_pos h]

theorem nbHG_lt {o : Ordinal.{0}} (h : o < veblen 2 p) : nbHG p G₀ o = G₀ o := by
  rw [nbHG, dif_pos h]

/-- **The unfolding in the bracket of `n = nbN p o`.** -/
theorem nbHR_cnf {o : Ordinal.{0}} (h1 : veblen 2 p ≤ o) (h2 : o < veblen 2 (p + 1)) (x : Ordinal.{0}) :
    nbHR p R₀ VP o x = veblen 1 (VP x + nbHR p R₀ VP (nbN p o) x) ^ nbHR p R₀ VP (log (nbBE p o) o) x *
      nbHR p R₀ VP (o / nbBE p o ^ log (nbBE p o) o) x + nbHR p R₀ VP (o % nbBE p o ^ log (nbBE p o) o) x := by
  obtain ⟨-, hg⟩ := nb_guards2 h1 h2
  rw [nbHR, dif_neg (not_lt.2 h1), dif_pos hg]

theorem nbHG_cnf {o : Ordinal.{0}} (h1 : veblen 2 p ≤ o) (h2 : o < veblen 2 (p + 1)) :
    nbHG p G₀ o = max (nbHG p G₀ (nbN p o)) (max (nbHG p G₀ (log (nbBE p o) o))
      (max (nbHG p G₀ (o / nbBE p o ^ log (nbBE p o) o)) (nbHG p G₀ (o % nbBE p o ^ log (nbBE p o) o)))) := by
  obtain ⟨-, hg⟩ := nb_guards2 h1 h2
  rw [nbHG, dif_neg (not_lt.2 h1), dif_pos hg]

theorem nbP_lim (p : Ordinal.{0}) : IsSuccLimit (veblen 2 p) := ev_isSuccLimit_of_inE (zm_fix_E (nb_fixP p))

theorem nbZ_E (p : Ordinal.{0}) : InE (veblen 2 (p + 1)) := zm_fix_E (nbZ_fix p)

/-- **The gate of a code bounds the gate of the index of its bracket.** -/
theorem nbHG_idx {o : Ordinal.{0}} (h1 : veblen 2 p ≤ o) (h2 : o < veblen 2 (p + 1)) :
    nbHG p G₀ (nbN p o) ≤ nbHG p G₀ o := by
  rw [nbHG_cnf h1 h2]; exact le_max_left _ _

/-- The bracket of `o + 1` is that of `o`, with the rest `r + 1`. -/
theorem nb_succ_dec {o : Ordinal.{0}} (h1 : veblen 2 p ≤ o) (h2 : o < veblen 2 (p + 1)) :
    veblen 2 p ≤ o + 1 ∧ o + 1 < veblen 2 (p + 1) ∧ nbN p (o + 1) = nbN p o ∧ nbBE p (o + 1) = nbBE p o ∧
      log (nbBE p o) (o + 1) = log (nbBE p o) o ∧
      (o + 1) / nbBE p o ^ log (nbBE p o) o = o / nbBE p o ^ log (nbBE p o) o ∧
      (o + 1) % nbBE p o ^ log (nbBE p o) o = o % nbBE p o ^ log (nbBE p o) o + 1 ∧
      o % nbBE p o ^ log (nbBE p o) o < o := by
  obtain ⟨b1, b2, -⟩ := nb_bracket h1 h2
  have hE := zm_veb_E (veblen 2 p + nbN p o)
  have hEeq := nbBE_eq b1 b2
  have hEo : nbBE p o ≤ o := hEeq ▸ b1
  have hEE : InE (nbBE p o) := hEeq ▸ hE
  have hb2' : o + 1 < veblen 1 (veblen 2 p + (nbN p o + 1)) :=
    (ev_isSuccLimit_of_inE (zm_veb_E _)).add_one_lt b2
  have hN1 : nbN p (o + 1) = nbN p o := nbN_eq (b1.trans (lt_add_one o).le) hb2'
  have hZ1 : o + 1 < veblen 2 (p + 1) := (ev_isSuccLimit_of_inE (nbZ_E p)).add_one_lt h2
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec hEE hEo
  set E := nbBE p o
  set k := log E o
  set d := o / E ^ k
  set r := o % E ^ k
  have hr1 : r + 1 < E ^ k := zm_opow_prin hEE k hrk (zm_one_lt_opow hEE hk0)
  obtain ⟨u1, u2, u3⟩ := zm_dec_uniq hEE hd0.ne' hdE hr1
  have e : o + 1 = E ^ k * d + (r + 1) := by rw [← add_assoc, hdec]
  have hBE1 : nbBE p (o + 1) = E := by
    show veblen 1 (veblen 2 p + nbN p (o + 1)) = E
    rw [hN1]; exact hEeq.symm
  refine ⟨h1.trans (lt_add_one o).le, hZ1, hN1, hBE1, ?_, ?_, ?_, zm_mod_lt hEE hEo⟩
  · rw [e]; exact u1
  · rw [e]; have := u2; rwa [u1] at this
  · rw [e]; have := u3; rwa [u1] at this

theorem nbHG_le_succ (hG₀ : ∀ o, o < veblen 2 p → G₀ o ≤ G₀ (o + 1)) :
    ∀ o, o < veblen 2 (p + 1) → nbHG p G₀ o ≤ nbHG p G₀ (o + 1) := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoZ
  rcases lt_or_ge o (veblen 2 p) with hoB | hoB
  · rw [nbHG_lt hoB, nbHG_lt ((nbP_lim p).add_one_lt hoB)]; exact hG₀ o hoB
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hro⟩ := nb_succ_dec hoB hoZ
  rw [nbHG_cnf hoB hoZ, nbHG_cnf s1 s2, s3, s4, s5, s6, s7]
  exact max_le_max le_rfl (max_le_max le_rfl (max_le_max le_rfl (IH _ hro (hro.trans hoZ))))

theorem nbHG_succ_lt {Z : Ordinal.{0}} (hZ : IsSuccLimit Z)
    (hG₀ : ∀ o, o < veblen 2 p → G₀ o < Z → G₀ (o + 1) < Z) :
    ∀ o, o < veblen 2 (p + 1) → nbHG p G₀ o < Z → nbHG p G₀ (o + 1) < Z := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoZ hg
  rcases lt_or_ge o (veblen 2 p) with hoB | hoB
  · rw [nbHG_lt hoB] at hg; rw [nbHG_lt ((nbP_lim p).add_one_lt hoB)]; exact hG₀ o hoB hg
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hro⟩ := nb_succ_dec hoB hoZ
  rw [nbHG_cnf hoB hoZ] at hg
  rw [nbHG_cnf s1 s2, s3, s4, s5, s6, s7]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (max_lt ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt hg))) (IH _ hro (hro.trans hoZ) ((le_max_right _ _).trans_lt
        ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))))

theorem nbHR_succ (hR₀ : ∀ o, o < veblen 2 p → ∀ x, R₀ (o + 1) x = R₀ o x + 1) :
    ∀ o, o < veblen 2 (p + 1) → ∀ x, nbHR p R₀ VP (o + 1) x = nbHR p R₀ VP o x + 1 := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro hoZ x
  rcases lt_or_ge o (veblen 2 p) with hoB | hoB
  · rw [nbHR_lt hoB, nbHR_lt ((nbP_lim p).add_one_lt hoB), hR₀ o hoB x]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, hro⟩ := nb_succ_dec hoB hoZ
  rw [nbHR_cnf hoB hoZ, nbHR_cnf s1 s2, s3, s4, s5, s6, s7, IH _ hro (hro.trans hoZ), add_assoc]

end Glob

end Googology.Trans.PoR.InaccPsi.R2.Nb
