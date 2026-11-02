import Googology.Trans.PoR.InaccPsi.R2.YhVb

/-!
# YhR: THE READING OF EVERY CODE ABOVE `G` OVER ALL BASE ATOMS — definitions and first laws

One reading for every layer at once.  Below `G` it is `Gl.glR`.  A code `c ≥ G` lies in the bracket `[e, ε_{e+1})`
of the `ε`-number `e = guE c ≥ G`, `c = e^j·d + r`; the bracket's `ε`-number is read

* `Γ_{x+1+i} = gq i x` when `e = Γ(i)` is a base atom (`Yh.YhAt`, index `yhJ e`),
* `ϑˣ(Ω₁·α(x) + η(x))` otherwise, `e = yhPsi α η` (`α = yhK e`, `η = yhI e`, both below `e`),

and `c(x) = e(x)^{j(x)}·d(x) + r(x)` (`yhA`).  The gate collects the gates of the infinite parts (an atom has
gate `0`).  At `c = 0` the brackets above `G` below `Γ(1)` are those of `Xu.xuR` (`t₀ ≤ c`) and of the hereditary step
over `G` (`G ≤ c < t₀`).

* `yhJ`, `yhJ_gcG`; `yhR`, `yhG`, `yhQ`, `yhQE`, `yhA`;
* `yhR_low`, `yhG_low` (**below `G` it is `Gl`**), `yhR_dec`, `yhG_dec`, `yhR_cnf`, `yhG_cnf`, `yhR_base`, `yhG_base`
  (**`e` reads `yhA e`**), `yhA_atom`, `yhR_atom` (**`Γ(i)` reads `Γ_{x+1+i}`, gate `0`**), `yhA_psi`;
* `yhR_zero`, `yhR_nat`, `yhR_one`, `yhG_zero`, `yhQ_nat`, `yhQ_le`;
* `yhR_succ` (**`(b+1)(x) = b(x) + 1` for every `b`**), `yhG_succ`, `yhG_le_succ`.

No new axiom.  New definitions: `yhJ`, `yhR`, `yhG`, `yhQ`, `yhQE`, `yhA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu

/-- **The index of a base atom**: `yhJ (Γ(i)) = i`. -/
noncomputable def yhJ (e : Ordinal.{0}) : Ordinal.{0} := sInf {i | gcG i = e}

theorem yhJ_gcG (i : Ordinal.{0}) : yhJ (gcG i) = i := by
  have : {j | gcG j = gcG i} = {i} := by
    ext j; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => gcG_strictMono.injective h, fun h => h ▸ rfl⟩
  unfold yhJ; rw [this, csInf_singleton]

theorem yh_gfE_le {c : Ordinal.{0}} (h : gcG 0 ≤ c) : gfE ≤ c := gfE_lt_G0.le.trans h

theorem yh_G_le_E {c : Ordinal.{0}} (h : gcG 0 ≤ c) : gcG 0 ≤ guE c := gl_E_max gl_G0_E gl_Om1_lt_G0 h

theorem yh_G_lt_E {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hA : ¬ YhAt (guE c)) : gcG 0 < guE c :=
  lt_of_le_of_ne (yh_G_le_E h) (fun e => hA (e ▸ yhAt_gcG 0))

theorem yh_E_data {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hA : ¬ YhAt (guE c)) :
    1 ≤ yhK (guE c) ∧ yhK (guE c) < guE c ∧ yhI (guE c) < guE c ∧ yhPsi (yhK (guE c)) (yhI (guE c)) = guE c :=
  yhData_spec (guE_E c) (yh_G_lt_E h hA) hA

theorem yh_lev_lt {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hA : ¬ YhAt (guE c)) : yhK (guE c) < c :=
  (yh_E_data h hA).2.1.trans_le (gl_E_le (yh_gfE_le h))

theorem yh_idx_lt {c : Ordinal.{0}} (h : gcG 0 ≤ c) (hA : ¬ YhAt (guE c)) : yhI (guE c) < c :=
  (yh_E_data h hA).2.2.1.trans_le (gl_E_le (yh_gfE_le h))

/-! ## The reading and the gate -/

open Classical in
/-- **The reading** of a code at `x`: `e(x)^{j(x)}·d(x) + r(x)` above `G` (`e = guE c` read `Γ_{x+1+i}` at a base atom
`Γ(i)`, `ϑˣ(Ω₁·α(x) + η(x))` otherwise), `Gl.glR` below `G`. -/
noncomputable def yhR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c then
    (if hA : YhAt (guE c) then gq (yhJ (guE c)) x
      else glA (yhR (yhK (guE c)) x) (yhR (yhI (guE c)) x) x) ^ yhR (log (guE c) c) x *
      yhR (c / guE c ^ log (guE c) c) x + yhR (c % guE c ^ log (guE c) c) x
  else glR c x
termination_by c
decreasing_by
  all_goals first
    | exact yh_lev_lt h hA
    | exact yh_idx_lt h hA
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.1

open Classical in
/-- **The gate** of a code: the gates of the infinite level, index (none at an atom), exponent and digit, and of
the rest; `Gl.glG` below `G`. -/
noncomputable def yhG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c then
    max (max (if hA : YhAt (guE c) then 0 else
          max (if yhK (guE c) < ω then 0 else yhG (yhK (guE c)))
            (if yhI (guE c) < ω then 0 else yhG (yhI (guE c))))
        (if log (guE c) c < ω then 0 else yhG (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else yhG (c / guE c ^ log (guE c) c))
        (yhG (c % guE c ^ log (guE c) c)))
  else glG c
termination_by c
decreasing_by
  all_goals first
    | exact yh_lev_lt h hA
    | exact yh_idx_lt h hA
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.1
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.2
    | exact (gl_parts (yh_gfE_le h)).2.2.2.2.2.2.1

/-- **The gate of a part**: `0` when finite. -/
noncomputable def yhQ (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else yhG a

/-- **The gate of an `ε`-number code as a base**: `0` at an atom, the gates of the level and the index otherwise. -/
noncomputable def yhQE (e : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if YhAt e then 0 else max (yhQ (yhK e)) (yhQ (yhI e))

/-- **The reading of an `ε`-number code as a base.** -/
noncomputable def yhA (e x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if YhAt e then gq (yhJ e) x else glA (yhR (yhK e) x) (yhR (yhI e) x) x

theorem yhA_atom {e : Ordinal.{0}} (h : YhAt e) (x : Ordinal.{0}) : yhA e x = gq (yhJ e) x := by
  unfold yhA; rw [if_pos h]

theorem yhA_psi {e : Ordinal.{0}} (h : ¬ YhAt e) (x : Ordinal.{0}) :
    yhA e x = glA (yhR (yhK e) x) (yhR (yhI e) x) x := by
  unfold yhA; rw [if_neg h]

theorem yhQE_atom {e : Ordinal.{0}} (h : YhAt e) : yhQE e = 0 := by unfold yhQE; rw [if_pos h]

theorem yhQE_psi {e : Ordinal.{0}} (h : ¬ YhAt e) : yhQE e = max (yhQ (yhK e)) (yhQ (yhI e)) := by
  unfold yhQE; rw [if_neg h]

theorem yhR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : yhR c x = glR c x := by
  rw [yhR, dif_neg (not_le.2 hc)]

theorem yhG_low {c : Ordinal.{0}} (hc : c < gcG 0) : yhG c = glG c := by
  rw [yhG, dif_neg (not_le.2 hc)]

theorem yhR_dec {c : Ordinal.{0}} (h : gcG 0 ≤ c) (x : Ordinal.{0}) :
    yhR c x = yhA (guE c) x ^ yhR (log (guE c) c) x * yhR (c / guE c ^ log (guE c) c) x +
      yhR (c % guE c ^ log (guE c) c) x := by
  rw [yhR, dif_pos h]
  by_cases hA : YhAt (guE c)
  · rw [dif_pos hA, yhA_atom hA]
  · rw [dif_neg hA, yhA_psi hA]

theorem yhG_dec {c : Ordinal.{0}} (h : gcG 0 ≤ c) :
    yhG c = max (max (yhQE (guE c)) (yhQ (log (guE c) c)))
      (max (yhQ (c / guE c ^ log (guE c) c)) (yhG (c % guE c ^ log (guE c) c))) := by
  rw [yhG, dif_pos h]
  by_cases hA : YhAt (guE c)
  · rw [dif_pos hA, yhQE_atom hA]; rfl
  · rw [dif_neg hA, yhQE_psi hA]; rfl

theorem yhR_zero (x : Ordinal.{0}) : yhR 0 x = 0 := by rw [yhR_low (gcG_SC 0).1, glR_zero]

theorem yhG_zero : yhG 0 = 0 := by rw [yhG_low (gcG_SC 0).1, glG_zero]

theorem yh_nat_lt_G (n : ℕ) : (n : Ordinal.{0}) < gcG 0 :=
  (natCast_lt_omega0 n).trans (omega0_lt_inE gl_G0_E)

theorem yhR_nat (n : ℕ) (x : Ordinal.{0}) : yhR n x = n := by rw [yhR_low (yh_nat_lt_G n), glR_nat]

theorem yhR_one (x : Ordinal.{0}) : yhR 1 x = 1 := by exact_mod_cast yhR_nat 1 x

theorem yhQ_nat (n : ℕ) : yhQ n = 0 := by unfold yhQ; rw [if_pos (natCast_lt_omega0 n)]

theorem yhQ_one : yhQ 1 = 0 := by exact_mod_cast yhQ_nat 1

theorem yhQ_zero : yhQ 0 = 0 := by exact_mod_cast yhQ_nat 0

theorem yhQ_le (a : Ordinal.{0}) : yhQ a ≤ yhG a := by
  unfold yhQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem yhG_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : yhQ a < Z) : yhG a < Z := by
  unfold yhQ at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    rw [yhG_low (yh_nat_lt_G n), glG_nat]; exact (natCast_lt_omega0 n).trans hωZ
  · exact h

/-! ## The bracket form -/

theorem yh_G_le_cnf {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) :
    gcG 0 ≤ e ^ j * d + r := hGe.trans (xu_le_cnf he hj hd0)

theorem yhR_cnf {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (x : Ordinal.{0}) :
    yhR (e ^ j * d + r) x = yhA e x ^ yhR j x * yhR d x + yhR r x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (gl_Om1_lt_G0.trans_le hGe) hj hd0 hde hr hv
  rw [yhR_dec (yh_G_le_cnf he hGe hj hd0) x, h1, h2, h3, h4]

theorem yhG_cnf {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) :
    yhG (e ^ j * d + r) = max (max (yhQE e) (yhQ j)) (max (yhQ d) (yhG r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (gl_Om1_lt_G0.trans_le hGe) hj hd0 hde hr hv
  rw [yhG_dec (yh_G_le_cnf he hGe hj hd0), h1, h2, h3, h4]

/-- **An `ε`-number code `e ≥ G` reads `yhA e`.** -/
theorem yhR_base {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (x : Ordinal.{0}) : yhR e x = yhA e x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := yhR_cnf he hGe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 x
  rw [← h1] at h
  rw [h, yhR_one, yhR_zero, opow_one, mul_one, add_zero]

theorem yhG_base {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) : yhG e = yhQE e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := yhG_cnf he hGe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2
  rw [← h1] at h
  rw [h, yhQ_one, yhG_zero]
  simp

/-- **The base atom `Γ(i)` reads `Γ_{x+1+i}`, gate `0`.** -/
theorem yhR_atom (i x : Ordinal.{0}) : yhR (gcG i) x = gq i x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  rw [yhR_base hE (gcG_le zero_le), yhA_atom (yhAt_gcG i), yhJ_gcG]

theorem yhG_atom (i : Ordinal.{0}) : yhG (gcG i) = 0 := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  rw [yhG_base hE (gcG_le zero_le), yhQE_atom (yhAt_gcG i)]

/-- **A non-atom `ε`-number code `e = yhPsi α η > G` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem yhR_psi {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (x : Ordinal.{0}) :
    yhR (yhPsi α η) x = glA (yhR α x) (yhR η x) x := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [yhR_base (yhPsi_E hα η) hGe.le, yhA_psi (yhPsi_notAt hα), h1, h2]

theorem yhG_psi {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) :
    yhG (yhPsi α η) = max (yhQ α) (yhQ η) := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [yhG_base (yhPsi_E hα η) hGe.le, yhQE_psi (yhPsi_notAt hα), h1, h2]

/-! ## Successors -/

theorem yhR_succ : ∀ b x : Ordinal.{0}, yhR (b + 1) x = yhR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [yhR_low hbG, yhR_low hb1, glR_succ b hb1 x]
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [e, yhR_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv, IH _ hrb x, yhR_dec hbG x, add_assoc]

theorem yhG_succ {Z : Ordinal.{0}} (hZ : IsSuccLimit Z) : ∀ b, yhG b < Z → yhG (b + 1) < Z := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hg
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [yhG_low hbG] at hg
    rw [yhG_low hb1]
    exact glG_succ hZ b hb1 hg
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [yhG_dec hbG] at hg
  rw [e, yhG_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv]
  exact max_lt ((le_max_left _ _).trans_lt hg) (max_lt ((le_max_left _ _).trans_lt
    ((le_max_right _ _).trans_lt hg)) (IH _ hrb ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hg))))

theorem yhG_le_succ : ∀ b, yhG b ≤ yhG (b + 1) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [yhG_low hbG, yhG_low hb1]; exact glG_le_succ b hb1
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [yhG_dec hbG, e, yhG_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv]
  exact max_le_max le_rfl (max_le_max le_rfl (IH _ hrb))

end Googology.Trans.PoR.InaccPsi.R2.Yh
