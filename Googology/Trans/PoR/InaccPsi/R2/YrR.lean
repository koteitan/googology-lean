import Googology.Trans.PoR.InaccPsi.R2.YhR

/-!
# YrR: THE READING OF EVERY CODE WITH READ ATOM INDICES — definitions and first laws

`Yh.yhR` reads the base atom `Γ(i)` as `Γ_{x+1+i} = gq i x` with the CONSTANT index `i`; it is the substitution
`Ω₁ ↦ x` only for `i < ε₀`.  Here the index is read too: `Γ(i)` reads `gq (i(x)) x = Γ_{x+1+i(x)}` (`yrR_atom`), a
recursion on the code since `i < Γ(i)` for every `i` below the least fixed point `B_Γ = Tf.tfBG` of `Γ`
(`Tf.tf_lt_gamma_shift`); at a fixed point `Γ(i) = i` the atom is not read (value `0`, no code below `B_Γ` has such
an atom).  The gate of the atom is the gate of its index (`yrG_atom`).  Everything else is `Yh.yhR`: below `G` it
is `Gl.glR`; a code `c ≥ G` lies in the bracket of `e = guE c`, `c = e^j·d + r`, read `e(x)^{j(x)}·d(x) + r(x)`,
`e = yhPsi α η` (not an atom) read `ϑˣ(Ω₁·α(x) + η(x))`.

* `yrR`, `yrG`, `yrQ`, `yrQE`, `yrA` (as `Yh.yhR` …, with the atom case read);
* `yrR_low`, `yrG_low`, `yrR_dec`, `yrG_dec`, `yrR_cnf`, `yrG_cnf`, `yrR_base`, `yrG_base`, `yrA_atom`,
  `yrR_atom` (**`Γ(i)` reads `Γ_{x+1+i(x)}` for `i < Γ(i)`**), `yrG_atom` (**gate `yrQ i`**), `yrA_psi`, `yrR_psi`;
* `yrR_zero`, `yrR_nat`, `yrR_one`, `yrG_zero`, `yrQ_nat`, `yrQ_le`;
* `yrR_succ` (**`(b+1)(x) = b(x) + 1` for every `b`**), `yrG_succ`, `yrG_le_succ`.

No new axiom.  New definitions: `yrR`, `yrG`, `yrQ`, `yrQE`, `yrA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Yh

/-- The index of the bracket atom is below the code when it is below the atom. -/
theorem yr_ix_lt {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hi : yhJ (guE c) < guE c) : yhJ (guE c) < c :=
  hi.trans_le (gl_E_le (yh_gfE_le h))

/-! ## The reading and the gate -/

open Classical in
/-- **The reading** of a code at `x`: `e(x)^{j(x)}·d(x) + r(x)` above `G` (`e = guE c` read `Γ_{x+1+i}` at a base atom
`Γ(i)`, `ϑˣ(Ω₁·α(x) + η(x))` otherwise), `Gl.glR` below `G`. -/
noncomputable def yrR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c then
    (if hA : YhAt (guE c) then (if hi : yhJ (guE c) < guE c then gq (yrR (yhJ (guE c)) x) x else 0)
      else glA (yrR (yhK (guE c)) x) (yrR (yhI (guE c)) x) x) ^ yrR (log (guE c) c) x *
      yrR (c / guE c ^ log (guE c) c) x + yrR (c % guE c ^ log (guE c) c) x
  else glR c x
termination_by c
decreasing_by
  all_goals first
    | exact yr_ix_lt h hi
    | exact yh_lev_lt h hA
    | exact yh_idx_lt h hA
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.1

open Classical in
/-- **The gate** of a code: the gates of the infinite level, index (none at an atom), exponent and digit, and of
the rest; `Gl.glG` below `G`. -/
noncomputable def yrG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c then
    max (max (if hA : YhAt (guE c) then
          (if hi : yhJ (guE c) < guE c then (if yhJ (guE c) < ω then 0 else yrG (yhJ (guE c))) else 0) else
          max (if yhK (guE c) < ω then 0 else yrG (yhK (guE c)))
            (if yhI (guE c) < ω then 0 else yrG (yhI (guE c))))
        (if log (guE c) c < ω then 0 else yrG (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else yrG (c / guE c ^ log (guE c) c))
        (yrG (c % guE c ^ log (guE c) c)))
  else glG c
termination_by c
decreasing_by
  all_goals first
    | exact yr_ix_lt h hi
    | exact yh_lev_lt h hA
    | exact yh_idx_lt h hA
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.1

/-- **The gate of a part**: `0` when finite. -/
noncomputable def yrQ (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else yrG a

/-- **The gate of an `ε`-number code as a base**: `0` at an atom, the gates of the level and the index otherwise. -/
noncomputable def yrQE (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if YhAt e then (if yhJ e < e then yrQ (yhJ e) else 0) else max (yrQ (yhK e)) (yrQ (yhI e))

/-- **The reading of an `ε`-number code as a base.** -/
noncomputable def yrA (e x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if YhAt e then (if yhJ e < e then gq (yrR (yhJ e) x) x else 0) else glA (yrR (yhK e) x) (yrR (yhI e) x) x

theorem yrA_atom {e : Ordinal.{0}} (h : YhAt e) (hi : yhJ e < e) (x : Ordinal.{0}) :
    yrA e x = gq (yrR (yhJ e) x) x := by
  unfold yrA; rw [if_pos h, if_pos hi]

theorem yrA_atom_fix {e : Ordinal.{0}} (h : YhAt e) (hi : ¬ yhJ e < e) (x : Ordinal.{0}) : yrA e x = 0 := by
  unfold yrA; rw [if_pos h, if_neg hi]

theorem yrA_psi {e : Ordinal.{0}} (h : ¬ YhAt e) (x : Ordinal.{0}) :
    yrA e x = glA (yrR (yhK e) x) (yrR (yhI e) x) x := by
  unfold yrA; rw [if_neg h]

theorem yrQE_atom {e : Ordinal.{0}} (h : YhAt e) (hi : yhJ e < e) : yrQE e = yrQ (yhJ e) := by
  unfold yrQE; rw [if_pos h, if_pos hi]

theorem yrQE_atom_fix {e : Ordinal.{0}} (h : YhAt e) (hi : ¬ yhJ e < e) : yrQE e = 0 := by
  unfold yrQE; rw [if_pos h, if_neg hi]

theorem yrQE_psi {e : Ordinal.{0}} (h : ¬ YhAt e) : yrQE e = max (yrQ (yhK e)) (yrQ (yhI e)) := by
  unfold yrQE; rw [if_neg h]

theorem yrR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : yrR c x = glR c x := by
  rw [yrR, dif_neg (not_le.2 hc)]

theorem yrG_low {c : Ordinal.{0}} (hc : c < gcG 0) : yrG c = glG c := by
  rw [yrG, dif_neg (not_le.2 hc)]

theorem yrR_dec {c : Ordinal.{0}} (h : gcG 0 ≤ c) (x : Ordinal.{0}) :
    yrR c x = yrA (guE c) x ^ yrR (log (guE c) c) x * yrR (c / guE c ^ log (guE c) c) x +
      yrR (c % guE c ^ log (guE c) c) x := by
  rw [yrR, dif_pos h]
  by_cases hA : YhAt (guE c)
  · by_cases hi : yhJ (guE c) < guE c
    · rw [dif_pos hA, dif_pos hi, yrA_atom hA hi]
    · rw [dif_pos hA, dif_neg hi, yrA_atom_fix hA hi]
  · rw [dif_neg hA, yrA_psi hA]

theorem yrG_dec {c : Ordinal.{0}} (h : gcG 0 ≤ c) :
    yrG c = max (max (yrQE (guE c)) (yrQ (log (guE c) c)))
      (max (yrQ (c / guE c ^ log (guE c) c)) (yrG (c % guE c ^ log (guE c) c))) := by
  rw [yrG, dif_pos h]
  by_cases hA : YhAt (guE c)
  · by_cases hi : yhJ (guE c) < guE c
    · rw [dif_pos hA, dif_pos hi, yrQE_atom hA hi]; rfl
    · rw [dif_pos hA, dif_neg hi, yrQE_atom_fix hA hi]; rfl
  · rw [dif_neg hA, yrQE_psi hA]; rfl

theorem yrR_zero (x : Ordinal.{0}) : yrR 0 x = 0 := by rw [yrR_low (gcG_SC 0).1, glR_zero]

theorem yrG_zero : yrG 0 = 0 := by rw [yrG_low (gcG_SC 0).1, glG_zero]

theorem yrR_nat (n : ℕ) (x : Ordinal.{0}) : yrR n x = n := by rw [yrR_low (yh_nat_lt_G n), glR_nat]

theorem yrR_one (x : Ordinal.{0}) : yrR 1 x = 1 := by exact_mod_cast yrR_nat 1 x

theorem yrQ_nat (n : ℕ) : yrQ n = 0 := by unfold yrQ; rw [if_pos (natCast_lt_omega0 n)]

theorem yrQ_one : yrQ 1 = 0 := by exact_mod_cast yrQ_nat 1

theorem yrQ_zero : yrQ 0 = 0 := by exact_mod_cast yrQ_nat 0

theorem yrQ_le (a : Ordinal.{0}) : yrQ a ≤ yrG a := by
  unfold yrQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem yrG_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : yrQ a < Z) : yrG a < Z := by
  unfold yrQ at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [yrG_low (yh_nat_lt_G n), glG_nat]; exact (natCast_lt_omega0 n).trans hωZ
  · exact h

/-! ## The bracket form -/

theorem yrR_cnf {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (x : Ordinal.{0}) :
    yrR (e ^ j * d + r) x = yrA e x ^ yrR j x * yrR d x + yrR r x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (gl_Om1_lt_G0.trans_le hGe) hj hd0 hde hr hv
  rw [yrR_dec (yh_G_le_cnf he hGe hj hd0) x, h1, h2, h3, h4]

theorem yrG_cnf {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) :
    yrG (e ^ j * d + r) = max (max (yrQE e) (yrQ j)) (max (yrQ d) (yrG r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (gl_Om1_lt_G0.trans_le hGe) hj hd0 hde hr hv
  rw [yrG_dec (yh_G_le_cnf he hGe hj hd0), h1, h2, h3, h4]

/-- **An `ε`-number code `e ≥ G` reads `yrA e`.** -/
theorem yrR_base {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (x : Ordinal.{0}) : yrR e x = yrA e x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := yrR_cnf he hGe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 x
  rw [← h1] at h
  rw [h, yrR_one, yrR_zero, opow_one, mul_one, add_zero]

theorem yrG_base {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) : yrG e = yrQE e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := yrG_cnf he hGe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
  rw [← h1] at h
  rw [h, yrQ_one, yrG_zero]
  simp

/-- **The base atom `Γ(i)`, `i < Γ(i)`, reads `Γ_{x+1+i(x)}`.** -/
theorem yrR_atom {i : Ordinal.{0}} (hi : i < gcG i) (x : Ordinal.{0}) : yrR (gcG i) x = gq (yrR i x) x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [yrR_base hE (gcG_le zero_le), yrA_atom (yhAt_gcG i) hi', yhJ_gcG]

/-- **The gate of the base atom `Γ(i)`, `i < Γ(i)`, is the gate of its index** (`0` when the index is finite). -/
theorem yrG_atom {i : Ordinal.{0}} (hi : i < gcG i) : yrG (gcG i) = yrQ i := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [yrG_base hE (gcG_le zero_le), yrQE_atom (yhAt_gcG i) hi', yhJ_gcG]

/-- **Below `B_Γ` every index is below its atom.** -/
theorem yr_idx_BG {i : Ordinal.{0}} (hi : i < Tf.tfBG) : i < gcG i := by
  rw [Tf.tf_gcG]; exact Tf.tf_lt_gamma_shift hi

/-- **`G` reads `Γ_{x+1}`, gate `0`.** -/
theorem yrR_G0 (x : Ordinal.{0}) : yrR (gcG 0) x = gq 0 x := by
  rw [yrR_atom (gcG_SC 0).1, yrR_low (gcG_SC 0).1, glR_zero]

theorem yrG_G0 : yrG (gcG 0) = 0 := by
  rw [yrG_atom (gcG_SC 0).1]; unfold yrQ; rw [if_pos omega0_pos]

/-- **A non-atom `ε`-number code `e = yhPsi α η > G` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem yrR_psi {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (x : Ordinal.{0}) :
    yrR (yhPsi α η) x = glA (yrR α x) (yrR η x) x := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [yrR_base (yhPsi_E hα η) hGe.le, yrA_psi (yhPsi_notAt hα), h1, h2]

theorem yrG_psi {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) :
    yrG (yhPsi α η) = max (yrQ α) (yrQ η) := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [yrG_base (yhPsi_E hα η) hGe.le, yrQE_psi (yhPsi_notAt hα), h1, h2]

/-! ## Successors -/

theorem yrR_succ : ∀ b x : Ordinal.{0}, yrR (b + 1) x = yrR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [yrR_low hbG, yrR_low hb1, glR_succ b hb1 x]
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [e, yrR_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv, IH _ hrb x, yrR_dec hbG x, add_assoc]

theorem yrG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, yrG b < Z → yrG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hg
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [yrG_low hbG] at hg
    rw [yrG_low hb1]
    exact glG_succ hZ b hb1 hg
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [yrG_dec hbG] at hg
  rw [e, yrG_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (IH _ hrb ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))

theorem yrG_le_succ : ∀ b, yrG b ≤ yrG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [yrG_low hbG, yrG_low hb1]; exact glG_le_succ b hb1
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [yrG_dec hbG, e, yrG_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv]
  exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb))

end Googology.Trans.PoR.InaccPsi.R2.Yr
