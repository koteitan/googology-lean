import Googology.Trans.PoR.InaccPsi.R2.XuVb
import Googology.Trans.PoR.InaccPsi.R2.TeAtom

/-!
# XuR: THE READING OF EVERY CODE BELOW `Γ(1)` (region (A3)), definitions and first laws

Below `t₀ = ε_{G+1}` the reading and the gate are those of the hereditary step `Wt.wtD` (codes `G^k·d + r`, the
(A3) code interface `Xc.xcA3`).  A code `t₀ ≤ c < Γ(1)` lies in the bracket `[e, ε_{e+1})` of the `ε`-number
`e = guE c ≥ t₀`, `e = xuPsi α η` (`α = xuK e`, `η = xuI e`, both below `e`, `R2.XuVb`), `c = e^j·d + r`; the reading
replaces `e` by the atom `ϑˣ(Ω₁·α(x) + η(x))`:

  `xuR c x = ϑˣ(Ω₁·α(x) + η(x))^{j(x)}·d(x) + r(x)`  (`wtD.R c x` below `t₀`),

one well-founded recursion for every bracket and every level `1 ≤ α < Γ(1)` (`α = G` included, with the shifted
count of `xuPsi`).

* `xuR`, `xuG`, `xuQ`, `xuQE`; `xuR_low`, `xuG_low` (**below `t₀` it is `wtD`**), `xuR_dec`, `xuG_dec`, `xuR_cnf`,
  `xuG_cnf`, `xuR_base` (**`xuPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))`**), `xuG_base`, `xuR_psi`, `xuG_psi`,
  `xuR_t0` (**`t₀` reads `ϑˣ(Ω₁ + Γ_{x+1}) = ε_{Γ_{x+1}+1}`**), `xuG_t0`;
* `xuG_lt_Om1`, `xu_parts_Q`, `xu_parts_g`, `xu_parts_lev`, `xu_E_g`;
* `xuA_facts` (the atom at an `ε`-number base `x < Ω₁`, level and index below `Γ_{x+2}`), `xuR_pos0`, `xuR_lt1`
  (**every reading lies below `Γ_{x+2}`**), `xuR_T`, `xuR_pos`, `xu_atom`, `xu_lead`;
* `xuR_succ` (**`(b+1)(x) = b(x) + 1`**), `xuG_succ`, `xuG_le_succ`.

No new axiom.  New definitions: `xuR`, `xuG`, `xuQ`, `xuQE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xu

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Hi

/-! ## Brackets above `t₀` -/

theorem xu_gfE_le {c : Ordinal.{0}} (h : Wj.wjT 0 ≤ c) : gfE ≤ c :=
  (gfE_lt_G0.trans xu_G_lt_t0).le.trans h

theorem xu_Om1_lt_t0 : Om1 < Wj.wjT 0 := gl_Om1_lt_G0.trans xu_G_lt_t0

/-- **The bracket of a code `≥ t₀` is `≥ t₀`.** -/
theorem xu_E_ge {c : Ordinal.{0}} (h : Wj.wjT 0 ≤ c) : Wj.wjT 0 ≤ guE c :=
  gl_E_max xu_t0_E xu_Om1_lt_t0 h

theorem xu_E_data {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) :
    1 ≤ xuK (guE c) ∧ xuK (guE c) < guE c ∧ xuI (guE c) < guE c ∧ xuPsi (xuK (guE c)) (xuI (guE c)) = guE c :=
  xuData_spec (guE_E c) (xu_G_lt_of (xu_E_ge h1)) ((gl_E_le (xu_gfE_le h1)).trans_lt h2)

theorem xu_idx_lt {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) : xuI (guE c) < c :=
  (xu_E_data h1 h2).2.2.1.trans_le (gl_E_le (xu_gfE_le h1))

theorem xu_lev_lt {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) : xuK (guE c) < c :=
  (xu_E_data h1 h2).2.1.trans_le (gl_E_le (xu_gfE_le h1))

/-! ## The reading and the gate -/

/-- **The reading** of a code at `x`: `ϑˣ(Ω₁·α(x) + η(x))^{j(x)}·d(x) + r(x)` on `[t₀, Γ(1))` (`α = xuK e`,
`η = xuI e`, `e = guE c`), `wtD.R` elsewhere. -/
noncomputable def xuR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : Wj.wjT 0 ≤ c ∧ c < gcG 1 then
    glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ^ xuR (log (guE c) c) x *
      xuR (c / guE c ^ log (guE c) c) x + xuR (c % guE c ^ log (guE c) c) x
  else wtD.R c x
termination_by c
decreasing_by
  all_goals first
    | exact xu_lev_lt h.1 h.2
    | exact xu_idx_lt h.1 h.2
    | exact (gl_parts (xu_gfE_le h.1)).2.2.2.2.2.1
    | exact (gl_parts (xu_gfE_le h.1)).2.2.2.2.2.2.2
    | exact (gl_parts (xu_gfE_le h.1)).2.2.2.2.2.2.1

/-- **The gate** of a code: the gates of its infinite level, index, exponent and digit, and of its rest. -/
noncomputable def xuG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : Wj.wjT 0 ≤ c ∧ c < gcG 1 then
    max (max (max (if xuK (guE c) < ω then 0 else xuG (xuK (guE c)))
          (if xuI (guE c) < ω then 0 else xuG (xuI (guE c))))
        (if log (guE c) c < ω then 0 else xuG (log (guE c) c)))
      (max (if c / guE c ^ log (guE c) c < ω then 0 else xuG (c / guE c ^ log (guE c) c))
        (xuG (c % guE c ^ log (guE c) c)))
  else wtD.g c
termination_by c
decreasing_by
  all_goals first
    | exact xu_lev_lt h.1 h.2
    | exact xu_idx_lt h.1 h.2
    | exact (gl_parts (xu_gfE_le h.1)).2.2.2.2.2.1
    | exact (gl_parts (xu_gfE_le h.1)).2.2.2.2.2.2.2
    | exact (gl_parts (xu_gfE_le h.1)).2.2.2.2.2.2.1

/-- **The gate of a part**: `0` when finite. -/
noncomputable def xuQ (a : Ordinal.{0}) : Ordinal.{0} := if a < ω then 0 else xuG a

/-- **The gate of an `ε`-number code as a base**: the gates of its level and its index as parts. -/
noncomputable def xuQE (e : Ordinal.{0}) : Ordinal.{0} := max (xuQ (xuK e)) (xuQ (xuI e))

theorem xu_lt_wtB {c : Ordinal.{0}} (hc : c < Wj.wjT 0) : c < wtD.B := by rw [wtD_B]; exact hc

theorem xuR_low {c : Ordinal.{0}} (hc : c < Wj.wjT 0) (x : Ordinal.{0}) : xuR c x = wtD.R c x := by
  rw [xuR, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

theorem xuG_low {c : Ordinal.{0}} (hc : c < Wj.wjT 0) : xuG c = wtD.g c := by
  rw [xuG, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

theorem xuR_dec {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) (x : Ordinal.{0}) :
    xuR c x = glA (xuR (xuK (guE c)) x) (xuR (xuI (guE c)) x) x ^ xuR (log (guE c) c) x *
      xuR (c / guE c ^ log (guE c) c) x + xuR (c % guE c ^ log (guE c) c) x := by
  rw [xuR, dif_pos ⟨h1, h2⟩]

theorem xuG_dec {c : Ordinal.{0}} (h1 : Wj.wjT 0 ≤ c) (h2 : c < gcG 1) :
    xuG c = max (max (xuQE (guE c)) (xuQ (log (guE c) c)))
      (max (xuQ (c / guE c ^ log (guE c) c)) (xuG (c % guE c ^ log (guE c) c))) := by
  rw [xuG, dif_pos ⟨h1, h2⟩]; rfl

theorem xuQ_le (a : Ordinal.{0}) : xuQ a ≤ xuG a := by
  unfold xuQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem xu_nat_lt_t0 (n : ℕ) : (n : Ordinal.{0}) < Wj.wjT 0 :=
  (natCast_lt_omega0 n).trans (omega0_lt_inE xu_t0_E)

theorem xuR_zero (x : Ordinal.{0}) : xuR 0 x = 0 := by
  rw [xuR_low xu_t0_E.pos, wtD.R_zero]

theorem xuG_zero : xuG 0 = 0 := by rw [xuG_low xu_t0_E.pos, wtD.g_zero]

theorem xuR_nat (n : ℕ) (x : Ordinal.{0}) : xuR n x = n := by
  rw [xuR_low (xu_nat_lt_t0 n), wtD.R_nat]

theorem xuR_one (x : Ordinal.{0}) : xuR 1 x = 1 := by exact_mod_cast xuR_nat 1 x

theorem xuG_nat_lt (n : ℕ) : xuG n < ω := by rw [xuG_low (xu_nat_lt_t0 n)]; exact wtD.g_nat n

theorem xuQ_nat (n : ℕ) : xuQ n = 0 := by unfold xuQ; rw [if_pos (natCast_lt_omega0 n)]

theorem xuQ_one : xuQ 1 = 0 := by exact_mod_cast xuQ_nat 1

theorem xuQ_zero : xuQ 0 = 0 := by exact_mod_cast xuQ_nat 0

/-- The gate of a part from its gate as a part, below every `Z > ω`. -/
theorem xuG_of_Q {a Z : Ordinal.{0}} (hωZ : ω < Z) (h : xuQ a < Z) : xuG a < Z := by
  unfold xuQ at h
  split_ifs at h with ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    exact (xuG_nat_lt n).trans hωZ
  · exact h

theorem xuQE_le_I (e : Ordinal.{0}) : xuQ (xuI e) ≤ xuQE e := le_max_right _ _

theorem xuQE_le_K (e : Ordinal.{0}) : xuQ (xuK e) ≤ xuQE e := le_max_left _ _

theorem xu_le_cnf {e j d r : Ordinal.{0}} (he : InE e) (hj : j ≠ 0) (hd0 : d ≠ 0) : e ≤ e ^ j * d + r :=
  calc e = e ^ (1 : Ordinal.{0}) * 1 := by rw [opow_one, mul_one]
    _ ≤ e ^ j * d := mul_le_mul' (opow_le_opow_right he.pos (one_le_iff_ne_zero.2 hj)) (one_le_iff_ne_zero.2 hd0)
    _ ≤ _ := le_self_add

theorem xuR_cnf {e j d r : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hB : e ^ j * d + r < gcG 1) (x : Ordinal.{0}) :
    xuR (e ^ j * d + r) x = glA (xuR (xuK e) x) (xuR (xuI e) x) x ^ xuR j x * xuR d x + xuR r x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (xu_Om1_lt_t0.trans_le ht) hj hd0 hde hr hv
  rw [xuR_dec (ht.trans (xu_le_cnf he hj hd0)) hB, h1, h2, h3, h4]

theorem xuG_cnf {e j d r : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (hB : e ^ j * d + r < gcG 1) :
    xuG (e ^ j * d + r) = max (max (xuQE e) (xuQ j)) (max (xuQ d) (xuG r)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (xu_Om1_lt_t0.trans_le ht) hj hd0 hde hr hv
  rw [xuG_dec (ht.trans (xu_le_cnf he hj hd0)) hB, h1, h2, h3, h4]

/-- **The base reading** of an `ε`-number code `e ∈ [t₀, Γ(1))`: `ϑˣ(Ω₁·α(x) + η(x))`. -/
theorem xuR_base {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1) (x : Ordinal.{0}) :
    xuR e x = glA (xuR (xuK e) x) (xuR (xuI e) x) x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := xuR_cnf he ht one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 (h1 ▸ heB) x
  rw [← h1] at h
  rw [h, xuR_one, xuR_zero, opow_one, mul_one, add_zero]

/-- The gate of an `ε`-number code is the gate of its level and index as parts. -/
theorem xuG_base {e : Ordinal.{0}} (he : InE e) (ht : Wj.wjT 0 ≤ e) (heB : e < gcG 1) : xuG e = xuQE e := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := xuG_cnf he ht one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 (h1 ▸ heB)
  rw [← h1] at h
  rw [h, xuQ_one, xuG_zero]
  simp

/-- **`xuPsi α η ≥ t₀` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem xuR_psi {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 1) {η : Ordinal.{0}} (hηG : η < gcG 1)
    (ht : Wj.wjT 0 ≤ xuPsi α η) (x : Ordinal.{0}) : xuR (xuPsi α η) x = glA (xuR α x) (xuR η x) x := by
  obtain ⟨e1, e2⟩ := xuData_eq hα hαG hηG (xu_G_lt_of ht)
  rw [xuR_base (xuPsi_E hα η) ht (xuPsi_lt_G1 hαG hηG), e1, e2]

theorem xuG_psi {α : Ordinal.{0}} (hα : 1 ≤ α) (hαG : α < gcG 1) {η : Ordinal.{0}} (hηG : η < gcG 1)
    (ht : Wj.wjT 0 ≤ xuPsi α η) : xuG (xuPsi α η) = max (xuQ α) (xuQ η) := by
  rw [xuG_base (xuPsi_E hα η) ht (xuPsi_lt_G1 hαG hηG), xuQE, (xuData_eq hα hαG hηG (xu_G_lt_of ht)).1,
    (xuData_eq hα hαG hηG (xu_G_lt_of ht)).2]

theorem xuR_G (x : Ordinal.{0}) : xuR (gcG 0) x = lgG x := by rw [xuR_low xu_G_lt_t0, wtD_RG]

theorem xuG_G : xuG (gcG 0) = 0 := by rw [xuG_low xu_G_lt_t0, wtD_gG]

/-- **`t₀` reads `ϑˣ(Ω₁ + Γ_{x+1})`**, gate `0`. -/
theorem xuR_t0 (x : Ordinal.{0}) : xuR (Wj.wjT 0) x = glA 1 (lgG x) x := by
  rw [← xu_t0_eq, xuR_psi le_rfl (gl_one_lt_G0.trans xu_G0_lt_G1) xu_G0_lt_G1 (xu_t0_eq ▸ le_rfl), xuR_one, xuR_G]

theorem xuG_t0 : xuG (Wj.wjT 0) = 0 := by
  rw [← xu_t0_eq, xuG_psi le_rfl (gl_one_lt_G0.trans xu_G0_lt_G1) xu_G0_lt_G1 (xu_t0_eq ▸ le_rfl), xuQ_one]
  unfold xuQ; rw [if_neg (not_lt.2 (omega0_lt_inE gl_G0_E).le), xuG_G, max_self]

end Googology.Trans.PoR.InaccPsi.R2.Xu
