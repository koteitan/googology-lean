import Googology.Trans.PoR.InaccPsi.R2.GkU4

/-!
# CODES BELOW `ζ_{Ω₁+1}`: the bound, gates of sums, powers and `ε`-numbers, hulls

* `gu_veb2_Om1` (`φ(2, Ω₁) = Ω₁`), `guB_eq` (**`ζ_{Ω₁+1} = φ(2, Ω₁+1)`**), `guB_lt_G0` (`ζ_{Ω₁+1} < Γ_{Ω₁+1}`),
  `guB_mem`, `gu_evA_eq` (`ε_{Ω₁+ν} = φ(1, Ω₁+ν)`);
* `gu_add` (**the gate of a sum**), `guQ_one_add`, `gu_div` (`y/E` and `y mod E` keep the gate), `gu_opow_gate`
  (**the gate of `ω^y`**), `gtc_le_Om1_add`, `gu_code_gate` (**a code over `Z`, atoms above `ζ_{Ω₁+1}`, has its gate
  below `Z`**; `φ(1, Ω₁+ν) = ε_{Ω₁+ν}` has the gate of `ν`, `φ(x, y)` with `x ≥ 2` is below `ε_{Ω₁+1}`);
* `gu_mem` (**every code lies in every hull containing its gate**, jointly with `ω^e·c` for `e` in the hull).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Ga
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq

/-- **`φ(2, Ω₁) = Ω₁`.** -/
theorem gu_veb2_Om1 : veblen 2 Om1 = Om1 := by
  have hlim : IsSuccLimit Om1 := by rw [Br.Om1_eq]; exact InaccSeq.Om_isSuccLimit one_ne_zero
  refine le_antisymm (((isNormal_veblen 2).le_iff_forall_le hlim).2 fun c hc => ?_) (right_le_veblen 2 Om1)
  have h := Ph.ph_SC_Om1.2 2 (by rw [← Br.Om1_eq]; exact (nat_lt_omega0 2).trans omega_lt_Om1) c
    (by rw [← Br.Om1_eq]; exact hc)
  rw [← Br.Om1_eq] at h
  exact h.le

/-- **`ζ_{Ω₁+1} = φ(2, Ω₁+1)`.** -/
theorem guB_eq : guB = veblen 2 (Om1 + 1) := by
  rw [guB, evZ, show (2 : Ordinal.{0}) = 1 + 1 by norm_num, veblen_add_one, deriv_add_one,
    ← veblen_add_one, show (1 : Ordinal.{0}) + 1 = 2 by norm_num, gu_veb2_Om1]

theorem guB_lt_G0 : guB < gcG 0 := by
  rw [guB_eq]
  have hSC := gcG_SC 0
  have hE := gcG_eW_lt 0
  exact hSC.2 2 (((nat_lt_omega0 2).trans omega_lt_Om1).trans (Om1_lt_eW.trans hE)) _
    (((ev_isSuccLimit_of_inE eW_E).add_one_lt Om1_lt_eW).trans hE)

theorem gu_evIx_Om1 : evIx Om1 = Om1 := by
  have h := evIx_epsilon Om1
  rwa [show Ordinal.epsilon Om1 = Om1 from eps_Om1] at h

/-- `ε_{Ω₁+ν} = φ(1, Ω₁+ν)`. -/
theorem gu_evA_eq (ν : Ordinal.{0}) : evA Om1 ν = veblen 1 (Om1 + ν) := by
  rw [evA, gu_evIx_Om1]

theorem guB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} : guB ∈ S.CSet a b := by
  have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
  rw [guB_eq]
  have h2 : (2 : Ordinal.{0}) ∈ S.CSet a b := by
    have := CSet.succ_mem (CSet.one_mem (S := S) a b); rwa [one_add_one_eq_two] at this
  exact CSet.phi_mem h2 (CSet.succ_mem hO)

theorem guQ_one_add (a : Ordinal.{0}) : guQ (1 + a) = guQ a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, guQ_nat, guQ_nat]
  · rw [one_add_of_omega0_le ha]

/-- The bracket of a code above a pseudo-base: `E ≤ y < ε_{E+1}` (`E = ε_{Ω₁+n}`, `n ≥ 1`) gives `guN y = n`. -/
theorem gu_same {n y : Ordinal.{0}} (h1 : evA Om1 n ≤ y) (h2 : y < evA Om1 (n + 1)) (hn : 1 ≤ n) :
    guN y = n ∧ guE y = evA Om1 n ∧ gfE ≤ y :=
  ⟨guN_eq h1 h2, by rw [guE, guN_eq h1 h2], (by rw [← gu_evA_one]; exact evA_le_iff.2 hn : gfE ≤ _).trans h1⟩

/-- **The gate of a sum** of codes below `ζ_{Ω₁+1}`, below every `Z > ω` closed under `+`. -/
theorem gu_add {Z : Ordinal.{0}} (hZ : ∀ u v, u < Z → v < Z → u + v < Z) (hωZ : ω < Z) :
    ∀ x y, x + y < guB → guG x < Z → guG y < Z → guG (x + y) < Z := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro y hxy hgx hgy
  have hxB : x < guB := lt_of_le_of_lt le_self_add hxy
  have hyB : y < guB := lt_of_le_of_lt le_add_self hxy
  rcases lt_or_ge x gfE with hxE | hxE
  · rcases lt_or_ge y gfE with hyE | hyE
    · rw [guG_low hxE] at hgx
      rw [guG_low hyE] at hgy
      rw [guG_low (eW_indec.add_lt hxE hyE)]
      exact gtc_add hZ x y hxE hyE hgx hgy
    · have e : x + y = y := add_of_omega0_opow_le (b := gfE) (by rw [eW_E]; exact hxE) (by rw [eW_E]; exact hyE)
      rw [e]; exact hgy
  obtain ⟨hn1, hnx, hxn, hnB, -⟩ := guN_spec hxE hxB
  obtain ⟨hk, hd0, hdE, hr, hdec, -, hrx, hdx⟩ := gu_parts hxE hxB
  obtain ⟨q0n, q0k, q0d, g0r⟩ := gu_parts_Q hxE hxB hgx
  have hEx : guE x = evA Om1 (guN x) := rfl
  rw [hEx] at hk hd0 hdE hr hdec hrx hdx q0k q0d g0r
  set n := guN x with hndef
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  have hE1 : (1 : Ordinal.{0}) < E := Lu.lu_one_lt_E hE
  set k := log E x with hkdef
  set d := x / E ^ k with hddef
  set r := x % E ^ k with hrdef
  have hxN : x < eN E := by rw [hEdef, ← evA_add_one]; exact hxn
  have hxk1 : x < E ^ (k + 1) := (lt_opow_iff_log_lt hE1 (hE.pos.trans_le hnx).ne').2 (lt_add_one _)
  have hk1N : k + 1 < eN E :=
    (ev_isSuccLimit_of_inE (eN_E E)).add_one_lt ((gu_parts hxE hxB).2.2.2.2.2.1.trans hxN)
  have hk1E : E ^ (k + 1) < evA Om1 (n + 1) := by rw [evA_add_one]; exact gu_pow_lt_eN hE hk1N
  rcases lt_or_ge y (E ^ k) with hyk | hyk
  · have hry : r + y < E ^ k := by
      rw [gu_pow_eq hE] at hr hyk ⊢; exact isPrincipal_add_omega0_opow _ hr hyk
    have e : x + y = E ^ k * d + (r + y) := by rw [← hdec, add_assoc]
    have hrE : r + E ^ k = E ^ k := by
      have := hr; rw [gu_pow_eq hE] at this ⊢; exact add_omega0_opow this
    have hv : E ^ k * d + (r + y) < evA Om1 (n + 1) := by
      rw [← e]
      refine lt_of_lt_of_le ((add_lt_add_iff_left _).2 hyk) (le_trans ?_ hk1E.le)
      rw [← hdec, add_assoc, hrE, opow_add, opow_one, ← mul_add_one]
      exact mul_le_mul_right (add_one_le_of_lt hdE) _
    have hrB : r + y < guB := lt_of_le_of_lt (add_le_add hrx.le le_rfl) hxy
    rw [e, guG_cnf hn1 hk hd0 hdE hry hv (e ▸ hxy)]
    exact max_lt (max_lt q0n q0k) (max_lt q0d (IH r hrx y hrB g0r hgy))
  rcases lt_or_ge y (E ^ (k + 1)) with hyk1 | hyk1
  · have hEk : E ≤ E ^ k := by
      calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ E ^ k := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 hk)
    have hyN : y < evA Om1 (n + 1) := hyk1.trans hk1E
    obtain ⟨hNy, hEy, hyE⟩ := gu_same (hEk.trans hyk) hyN hn1
    have hky : log E y = k := by
      refine le_antisymm ?_ (le_log_of_opow_le hE1 hyk)
      exact Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt hE1 (hE.pos.trans_le (hEk.trans hyk)).ne').1 hyk1)
    obtain ⟨-, hd0', hdE', hr', hdec', -, -, -⟩ := gu_parts hyE hyB
    obtain ⟨-, -, q0d', g0r'⟩ := gu_parts_Q hyE hyB hgy
    rw [hEy, hky] at hd0' hdE' hr' hdec' q0d' g0r'
    set d' := y / E ^ k with hd'def
    set r' := y % E ^ k with hr'def
    have hab : r + E ^ k * d' = E ^ k * d' := by
      rw [gu_pow_eq hE] at hr ⊢
      exact add_of_omega0_opow_le hr (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0'))
    have e : x + y = E ^ k * (d + d') + r' := by
      rw [← hdec, ← hdec', add_assoc, ← add_assoc r, hab, ← add_assoc, ← mul_add]
    have hdd : d + d' < E := (inE_indec hE).add_lt hdE hdE'
    have hv : E ^ k * (d + d') + r' < evA Om1 (n + 1) := by
      rw [← e]
      have h1 : x + y < E ^ (k + 1) := by
        rw [gu_pow_eq hE] at hxk1 hyk1 ⊢; exact isPrincipal_add_omega0_opow _ hxk1 hyk1
      exact h1.trans hk1E
    have hdB : d + d' < guB := hdd.trans (gu_evA_lt hnB)
    have hgdd : guG (d + d') < Z :=
      IH d hdx d' hdB (guG_of_Q hωZ q0d) (guG_of_Q hωZ q0d')
    rw [e, guG_cnf hn1 hk (by intro h0; exact hd0 (Ordinal.add_eq_zero_iff.1 h0).1) hdd hr' hv (e ▸ hxy)]
    exact max_lt (max_lt q0n q0k) (max_lt ((guQ_le _).trans_lt hgdd) g0r')
  · have e : x + y = y := add_of_omega0_opow_le (b := E * (k + 1)) (by rw [← gu_pow_eq hE]; exact hxk1)
      (by rw [← gu_pow_eq hE]; exact hyk1)
    rw [e]; exact hgy

/-- **`y/E` and `y mod E` keep the gate** of a code `y ≥ ε_{Ω₁+1}` (`E = guE y`), below every `Z > ω`. -/
theorem gu_div {Z : Ordinal.{0}} (hωZ : ω < Z) : ∀ y, gfE ≤ y → y < guB → guG y < Z →
    guQ (y / guE y) < Z ∧ guG (y % guE y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyB hg
  obtain ⟨hn1, hny, hyn, hnB, -⟩ := guN_spec hyE hyB
  obtain ⟨ha, hd0, hdE, hr, hdec, -, hry, -⟩ := gu_parts hyE hyB
  obtain ⟨q0n, q0a, q0d, g0r⟩ := gu_parts_Q hyE hyB hg
  have hEy : guE y = evA Om1 (guN y) := rfl
  rw [hEy] at ha hd0 hdE hr hdec hry q0a q0d g0r ⊢
  set n := guN y with hndef
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  have hE0 : E ≠ 0 := hE.pos.ne'
  set a := log E y with hadef
  set d := y / E ^ a with hddef
  set r := y % E ^ a with hrdef
  have e1 : 1 + (a - 1) = a := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 ha)
  have hsp : E ^ a = E * E ^ (a - 1) := by
    calc E ^ a = E ^ (1 + (a - 1)) := by rw [e1]
      _ = E * E ^ (a - 1) := by rw [opow_add, opow_one]
  have hy : y = E * (E ^ (a - 1) * d) + r := by rw [← hdec, hsp, mul_assoc]
  have hrB : r < guB := hry.trans hyB
  have hrN : r < evA Om1 (n + 1) := hry.trans hyn
  constructor
  · have hdiv : y / E = E ^ (a - 1) * d + r / E := by rw [hy, Ordinal.mul_add_div _ hE0]
    rcases eq_or_ne (a - 1) 0 with ha1 | ha1
    · have hrE : r < E := by
        have := hr; rw [hsp, ha1, opow_zero, mul_one] at this; exact this
      rw [hdiv, ha1, opow_zero, one_mul, Ordinal.div_eq_zero_of_lt hrE, add_zero]
      exact q0d
    · have hrq : r / E < E ^ (a - 1) := by
        rw [← Ordinal.lt_mul_iff_div_lt hE0, ← hsp]; exact hr
      have hdB : y / E < evA Om1 (n + 1) :=
        lt_of_le_of_lt (Ordinal.div_le_of_le_mul (le_mul_right y hE.pos)) hyn
      have hEq : E ≤ y / E := by
        rw [hdiv]
        calc E = E ^ (1 : Ordinal.{0}) := (opow_one _).symm
          _ ≤ E ^ (a - 1) := opow_le_opow_right hE.pos (one_le_iff_ne_zero.2 ha1)
          _ ≤ E ^ (a - 1) * d := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)
          _ ≤ _ := le_self_add
      have hQ : guQ (y / E) = guG (y / E) := by
        unfold guQ
        rw [if_neg (not_lt.2 (((omega_lt_Om1.trans Om1_lt_eW).trans_le
          (by rw [← gu_evA_one, hEdef]; exact evA_le_iff.2 hn1)).le.trans hEq))]
      have hdivB : y / E < guB := hdB.trans (gu_evA_lt ((guB_lim).add_one_lt hnB))
      rw [hQ, hdiv, guG_cnf hn1 ha1 hd0 hdE hrq (hdiv ▸ hdB) (hdiv ▸ hdivB)]
      refine max_lt (max_lt q0n (by rw [← guQ_one_add, e1]; exact q0a)) (max_lt q0d ?_)
      rcases lt_or_ge r E with hrE | hrE
      · rw [Ordinal.div_eq_zero_of_lt hrE, guG_zero]; exact (omega0_pos).trans hωZ
      · obtain ⟨-, hEr, hgfr⟩ := gu_same hrE hrN hn1
        have := (IH r hry hgfr hrB g0r).1
        rw [hEr] at this
        exact guG_of_Q hωZ this
  · have hmod : y % E = r % E := by rw [hy, Ordinal.mul_add_mod_self]
    rw [hmod]
    rcases lt_or_ge r E with hrE | hrE
    · rw [Ordinal.mod_eq_of_lt hrE]; exact g0r
    · obtain ⟨-, hEr, hgfr⟩ := gu_same hrE hrN hn1
      have := (IH r hry hgfr hrB g0r).2
      rwa [hEr] at this

/-- **The gate of `ω^y`** for a code `y` with `ω^y < ζ_{Ω₁+1}`, below every `Z > ω` closed under `ω^·`. -/
theorem gu_opow_gate {Z : Ordinal.{0}} (hZw : ∀ u, u < Z → ω ^ u < Z) (hωZ : ω < Z) :
    ∀ y, ω ^ y < guB → guG y < Z → guG (ω ^ y) < Z := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyB hg
  have hyy : y ≤ ω ^ y := right_le_opow y one_lt_omega0
  rcases lt_or_ge (ω ^ y) gfE with hlt | hge
  · have hy : y < gfE := hyy.trans_lt hlt
    rw [guG_low hy] at hg
    rw [guG_low hlt]
    exact gtc_opow hZw hy hg
  obtain ⟨hn1, hnc, hcn, hnB, -⟩ := guN_spec hge hyB
  set n := guN (ω ^ y) with hndef
  set E := evA Om1 n with hEdef
  have hE : InE E := evA_E _ _
  have hEy : E ≤ y := by
    rw [← show ω ^ E = E from hE] at hnc
    exact (opow_le_opow_iff_right one_lt_omega0).1 hnc
  have hyN : y < evA Om1 (n + 1) := hyy.trans_lt hcn
  obtain ⟨hNy, hEy', hyE⟩ := gu_same hEy hyN hn1
  have hyB' : y < guB := hyy.trans_lt hyB
  obtain ⟨g1, g2⟩ := gu_div hωZ y hyE hyB' hg
  rw [hEy'] at g1 g2
  obtain ⟨q0n, -, -, -⟩ := gu_parts_Q hyE hyB' hg
  rw [hNy] at q0n
  set q := y / E with hqdef
  set s := y % E with hsdef
  have hsE : s < E := Ordinal.mod_lt y hE.pos.ne'
  have hq0 : q ≠ 0 := ((Ordinal.div_pos hE.pos.ne').2 hEy).ne'
  have hws : ω ^ s < E := by rw [← show ω ^ E = E from hE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hsE
  have ew : ω ^ y = E ^ q * ω ^ s + 0 := by
    rw [add_zero, gu_pow_eq hE, ← opow_add, Ordinal.div_add_mod]
  have hsy : s < y := hsE.trans_le hEy
  have hgs : guG (ω ^ s) < Z := IH s hsy (hws.trans (gu_evA_lt hnB)) g2
  rw [ew, guG_cnf hn1 hq0 (opow_ne_zero _ omega0_ne_zero) hws (opow_pos _ hE.pos) (ew ▸ hcn) (ew ▸ hyB),
    guG_zero]
  exact max_lt (max_lt q0n g1) (max_lt ((guQ_le _).trans_lt hgs) (lt_of_le_of_lt zero_le (omega0_pos.trans hωZ)))

/-- `gtc ν ≤ gtc (Ω₁ + ν)` for `ν < Ω₁·ω`. -/
theorem gtc_le_Om1_add {ν : Ordinal.{0}} (hν : ν < Om1 * ω) : gtc ν ≤ gtc (Om1 + ν) := by
  have hO1 : (1 : Ordinal.{0}) < Om1 := gf_one_lt_Om1
  have h1W : (1 : Ordinal.{0}) < gfE := gw_one_lt
  rcases lt_or_ge ν Om1 with hνO | hνO
  · have h := (rdc_cnf (l := 1) (q := 1) (r := ν) h1W one_ne_zero hO1 (by rw [opow_one]; exact hνO) 0).2
    rw [opow_one, mul_one] at h
    rw [h]
    exact le_max_right _ _
  · have hν0 : ν ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans hO1) hνO).ne'
    obtain ⟨hq0, hqΩ, hr, hdec, -, -⟩ := parts hν0
    have hl1 : log Om1 ν = 1 := by
      refine le_antisymm ?_ (le_log_of_opow_le hO1 (by rw [opow_one]; exact hνO))
      refine Order.lt_add_one_iff.1 ((lt_opow_iff_log_lt hO1 hν0).1 ?_)
      rw [opow_add, opow_one]
      exact hν.trans ((mul_lt_mul_iff_right₀ (zero_lt_one.trans hO1)).2 omega_lt_Om1)
    rw [hl1, opow_one] at hq0 hqΩ hr hdec
    set m := ν / Om1 with hmdef
    set s := ν % Om1 with hsdef
    have hmω : m < ω := by
      by_contra hc
      push Not at hc
      have : Om1 * ω ≤ ν := by rw [← hdec]; exact (mul_le_mul_right hc _).trans le_self_add
      exact absurd hν (not_lt.2 this)
    have h1 := (rdc_cnf (l := 1) (q := m) (r := s) h1W hq0.ne' hqΩ (by rw [opow_one]; exact hr) 0).2
    have hm1 : 1 + m < Om1 := Om1_add_lt hO1 hqΩ
    have h2 := (rdc_cnf (l := 1) (q := 1 + m) (r := s) h1W (by
      intro h0; exact one_ne_zero (Ordinal.add_eq_zero_iff.1 h0).1) hm1 (by rw [opow_one]; exact hr) 0).2
    rw [opow_one] at h1 h2
    have e : Om1 + ν = Om1 * (1 + m) + s := by rw [← hdec, mul_add, mul_one, add_assoc]
    rw [e, h2, ← hdec, h1]
    exact max_le_max (max_le_max le_rfl le_add_self) le_rfl

end Googology.Trans.PoR.InaccPsi.R2.Gk
