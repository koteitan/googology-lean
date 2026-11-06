import Googology.Trans.PoR.InaccPsi.R2.ZmDS

/-!
# VaR: ONE READING OF EVERY CODE PAST `B_Γ` — `Yr.yrR` WITH THE FIXED POINT `B_Γ` READ `D(x)`

`Yr.yrR` reads a base atom `Γ(i)` with `i < Γ(i)` as `Γ_{x+1+i(x)}` and a fixed point `Γ(i) = i` as `0`.  Here the
fixed point is read `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)` (`Yw.ywV 1 0`, the reading of `B_Γ`, `Zm.zmYr`); everything else is as
in `Yr.yrR`: a code `c ≥ G` in the bracket of `e = guE c`, `c = e^j·d + r`, reads `e(x)^{j(x)}·d(x) + r(x)`, a
non-atom `e = yhPsi α η` reads `ϑˣ(Ω₁·α(x) + η(x))`.  Below `B_Γ` it is `Yr.yrR` (`vR_yr`); the gate is `Yr.yrG`.
The only fixed point of `Γ` below `Γ_{B_Γ+1}` is `B_Γ`, so this is the reading of every code below `Γ_{B_Γ+1}`.

* `vR`, `vA` (the reading of an `ε`-number code as a base), `vA_atom`, `vA_atom_fix`, `vA_psi`;
* `vR_low`, `vR_dec`, `vR_cnf`, `vR_base`, `vR_atom`, `vR_BG` (**`B_Γ` reads `D(x)`**), `vR_psi`, `vR_zero`,
  `vR_nat`, `vR_one`, `vR_succ`, `vR_yr` (**`vR = yrR` below `B_Γ`**);
* `va_psi1_fix` (**`yhPsi 1 E = ε_{E+1}` at a fixed point `E > Ω₁` of `φ(1, ·)`**), `va_psi1_succ`
  (**`yhPsi 1 (η+1) = ε_{yhPsi 1 η + 1}`**).

No new axiom.  New definitions: `vR`, `vA`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw

/-! ## The reading -/

open Classical in
/-- **The reading** of a code at `x`: as `Yr.yrR`, with a fixed point `Γ(i) = i` read `D(x)`. -/
noncomputable def vR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : gcG 0 ≤ c then
    (if hA : YhAt (guE c) then (if hi : yhJ (guE c) < guE c then gq (vR (yhJ (guE c)) x) x else ywV 1 0 x)
      else glA (vR (yhK (guE c)) x) (vR (yhI (guE c)) x) x) ^ vR (log (guE c) c) x *
      vR (c / guE c ^ log (guE c) c) x + vR (c % guE c ^ log (guE c) c) x
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

/-- **The reading of an `ε`-number code as a base.** -/
noncomputable def vA (e x : Ordinal.{0}) : Ordinal.{0} := by
  classical
  exact if YhAt e then (if yhJ e < e then gq (vR (yhJ e) x) x else ywV 1 0 x)
    else glA (vR (yhK e) x) (vR (yhI e) x) x

theorem vA_atom {e : Ordinal.{0}} (h : YhAt e) (hi : yhJ e < e) (x : Ordinal.{0}) :
    vA e x = gq (vR (yhJ e) x) x := by
  unfold vA; rw [if_pos h, if_pos hi]

theorem vA_atom_fix {e : Ordinal.{0}} (h : YhAt e) (hi : ¬ yhJ e < e) (x : Ordinal.{0}) : vA e x = ywV 1 0 x := by
  unfold vA; rw [if_pos h, if_neg hi]

theorem vA_psi {e : Ordinal.{0}} (h : ¬ YhAt e) (x : Ordinal.{0}) :
    vA e x = glA (vR (yhK e) x) (vR (yhI e) x) x := by
  unfold vA; rw [if_neg h]

theorem vR_low {c : Ordinal.{0}} (hc : c < gcG 0) (x : Ordinal.{0}) : vR c x = glR c x := by
  rw [vR, dif_neg (not_le.2 hc)]

theorem vR_dec {c : Ordinal.{0}} (h : gcG 0 ≤ c) (x : Ordinal.{0}) :
    vR c x = vA (guE c) x ^ vR (log (guE c) c) x * vR (c / guE c ^ log (guE c) c) x +
      vR (c % guE c ^ log (guE c) c) x := by
  rw [vR, dif_pos h]
  by_cases hA : YhAt (guE c)
  · by_cases hi : yhJ (guE c) < guE c
    · rw [dif_pos hA, dif_pos hi, vA_atom hA hi]
    · rw [dif_pos hA, dif_neg hi, vA_atom_fix hA hi]
  · rw [dif_neg hA, vA_psi hA]

theorem vR_zero (x : Ordinal.{0}) : vR 0 x = 0 := by rw [vR_low (gcG_SC 0).1, glR_zero]

theorem vR_nat (n : ℕ) (x : Ordinal.{0}) : vR n x = n := by rw [vR_low (yh_nat_lt_G n), glR_nat]

theorem vR_one (x : Ordinal.{0}) : vR 1 x = 1 := by exact_mod_cast vR_nat 1 x

theorem vR_cnf {e j d r : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (hj : j ≠ 0) (hd0 : d ≠ 0) (hde : d < e)
    (hr : r < e ^ j) (hv : e ^ j * d + r < eN e) (x : Ordinal.{0}) :
    vR (e ^ j * d + r) x = vA e x ^ vR j x * vR d x + vR r x := by
  obtain ⟨h1, h2, h3, h4, -⟩ := gl_cnf he (gl_Om1_lt_G0.trans_le hGe) hj hd0 hde hr hv
  rw [vR_dec (yh_G_le_cnf he hGe hj hd0) x, h1, h2, h3, h4]

/-- **An `ε`-number code `e ≥ G` reads `vA e`.** -/
theorem vR_base {e : Ordinal.{0}} (he : InE e) (hGe : gcG 0 ≤ e) (x : Ordinal.{0}) : vR e x = vA e x := by
  obtain ⟨h1, h2⟩ := gl_base_nf he
  have hE1 : (1 : Ordinal.{0}) < e := Lu.lu_one_lt_E he
  have h := vR_cnf he hGe one_ne_zero one_ne_zero hE1 (by rw [opow_one]; exact he.pos) h2 x
  rw [← h1] at h
  rw [h, vR_one, vR_zero, opow_one, mul_one, add_zero]

/-- **The base atom `Γ(i)`, `i < Γ(i)`, reads `Γ_{x+1+i(x)}`.** -/
theorem vR_atom {i : Ordinal.{0}} (hi : i < gcG i) (x : Ordinal.{0}) : vR (gcG i) x = gq (vR i x) x := by
  have hE : InE (gcG i) := Low.opow_eq_self_of_SC (gcG_SC i)
  have hi' : yhJ (gcG i) < gcG i := by rw [yhJ_gcG]; exact hi
  rw [vR_base hE (gcG_le zero_le), vA_atom (yhAt_gcG i) hi', yhJ_gcG]

/-- **`B_Γ` reads `D(x) = ϑˣ(Ω₁·Ω₁ + Ω₁)`.** -/
theorem vA_BG (x : Ordinal.{0}) : vA Tf.tfBG x = ywV 1 0 x := by
  have hA : YhAt Tf.tfBG := by rw [← Zb.zb_gcG_BG]; exact yhAt_gcG _
  have hJ : yhJ Tf.tfBG = Tf.tfBG := by
    have h := yhJ_gcG Tf.tfBG; rwa [Zb.zb_gcG_BG] at h
  have hi : ¬ yhJ Tf.tfBG < Tf.tfBG := by rw [hJ]; exact lt_irrefl _
  exact vA_atom_fix hA hi x

theorem vR_BG (x : Ordinal.{0}) : vR Tf.tfBG x = ywV 1 0 x := by
  have hE : InE Tf.tfBG := Low.opow_eq_self_of_SC Tf.tfBG_SC
  have hG : gcG 0 ≤ Tf.tfBG := by rw [← Zb.zb_gcG_BG]; exact gcG_le zero_le
  rw [vR_base hE hG, vA_BG]

/-- **A non-atom `ε`-number code `e = yhPsi α η > G` reads `ϑˣ(Ω₁·α(x) + η(x))`.** -/
theorem vR_psi {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (x : Ordinal.{0}) :
    vR (yhPsi α η) x = glA (vR α x) (vR η x) x := by
  obtain ⟨h1, h2⟩ := yhData_eq hα hGe
  rw [vR_base (yhPsi_E hα η) hGe.le, vA_psi (yhPsi_notAt hα), h1, h2]

theorem vA_psi' {α η : Ordinal.{0}} (hα : 1 ≤ α) (hGe : gcG 0 < yhPsi α η) (x : Ordinal.{0}) :
    vA (yhPsi α η) x = glA (vR α x) (vR η x) x := by
  rw [← vR_base (yhPsi_E hα η) hGe.le]; exact vR_psi hα hGe x

/-! ## Successors -/

theorem vR_succ : ∀ b x : Ordinal.{0}, vR (b + 1) x = vR b x + 1 := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x
  rcases lt_or_ge b (gcG 0) with hbG | hbG
  · have hb1 : b + 1 < gcG 0 := (ev_isSuccLimit_of_inE gl_G0_E).add_one_lt hbG
    rw [vR_low hbG, vR_low hb1, glR_succ b hb1 x]
  have hbE := yh_gfE_le hbG
  obtain ⟨hk, hd0, hdE, -, -, -, hrb, -⟩ := gl_parts hbE
  obtain ⟨e, hr1, hv⟩ := gl_succ_nf hbE
  rw [e, vR_cnf (guE_E b) (yh_G_le_E hbG) hk hd0 hdE hr1 hv, IH _ hrb x, vR_dec hbG x, add_assoc]

/-! ## Below `B_Γ` it is `Yr.yrR` -/

/-- **`vR = yrR` below `B_Γ`.** -/
theorem vR_yr : ∀ c, c < Tf.tfBG → ∀ x, vR c x = yrR c x := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc x
  rcases lt_or_ge c (gcG 0) with hcG | hcG
  · rw [vR_low hcG, yrR_low hcG]
  have hEc : guE c ≤ c := gl_E_le (yh_gfE_le hcG)
  obtain ⟨-, -, -, -, -, hlog, hmod, hdiv⟩ := gl_parts (yh_gfE_le hcG)
  have hA : vA (guE c) x = yrA (guE c) x := by
    by_cases hAt : YhAt (guE c)
    · obtain ⟨i, hi⟩ := yhAt_iff.1 hAt
      obtain ⟨hii, hie⟩ := yr_atom_idx hi (hEc.trans_lt hc)
      have hJ : yhJ (guE c) = i := by rw [hi, yhJ_gcG]
      have hJe : yhJ (guE c) < guE c := by rw [hJ]; exact hie
      rw [vA_atom hAt hJe, yrA_atom hAt hJe, IH _ (hJe.trans_le hEc) ((hJe.trans_le hEc).trans hc)]
    · have hK := yh_lev_lt hcG hAt
      have hI := yh_idx_lt hcG hAt
      rw [vA_psi hAt, yrA_psi hAt, IH _ hK (hK.trans hc), IH _ hI (hI.trans hc)]
  rw [vR_dec hcG, yrR_dec hcG, hA, IH _ hlog (hlog.trans hc), IH _ hdiv (hdiv.trans hc),
    IH _ hmod (hmod.trans hc)]

/-! ## The next `ε`-number on the code side -/

/-- **`yhPsi 1 E = ε_{E+1}` at a fixed point `E > Ω₁` of `φ(1, ·)`.** -/
theorem va_psi1_fix {E : Ordinal.{0}} (hE : veblen 1 E = E) (hOE : Om1 < E) : yhPsi 1 E = eN E := by
  have h1 : ¬ YhAt (1 : Ordinal.{0}) := fun h => absurd h.2 (not_lt.2 (le_of_lt
    (one_lt_omega0.trans omega_lt_Om1)))
  have hF : glFw 1 E := ⟨E, ⟨luP_succ.2 hE, hOE⟩, 0, by rw [Nat.cast_zero, add_zero]⟩
  rw [yhPsi_ne h1, glPsi, glLam_of hF]
  conv_rhs => rw [← hE]
  rw [Go.go_eN_veb]

/-- **`yhPsi 1 (η+1) = ε_{yhPsi 1 η + 1}`.** -/
theorem va_psi1_succ (η : Ordinal.{0}) : yhPsi 1 (η + 1) = eN (yhPsi 1 η) := by
  have h1 : ¬ YhAt (1 : Ordinal.{0}) := fun h => absurd h.2 (not_lt.2 (le_of_lt
    (one_lt_omega0.trans omega_lt_Om1)))
  rw [yhPsi_ne h1, yhPsi_ne h1, glPsi, glPsi, Go.go_eN_veb]
  congr 1
  by_cases hF : glFw 1 η
  · obtain ⟨f, hf, n, hn⟩ := hF
    have hF' : glFw 1 (η + 1) := ⟨f, hf, n + 1, by rw [hn, Nat.cast_succ, add_assoc]⟩
    rw [glLam_of hF', glLam_of ⟨f, hf, n, hn⟩]
  · have hF' : ¬ glFw 1 (η + 1) := by
      rintro ⟨f, hf, m, hm⟩
      rcases m with _ | n
      · rw [Nat.cast_zero, add_zero] at hm
        exact Order.not_isSuccLimit_succ η (by rw [succ_eq_add_one, hm]; exact ev_isSuccLimit_of_inE (glF_E hf))
      · apply hF
        refine ⟨f, hf, n, ?_⟩
        rw [Nat.cast_succ, ← add_assoc, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one] at hm
        exact Order.succ_injective hm
    rw [glLam_of_not hF', glLam_of_not hF, add_assoc]

end Googology.Trans.PoR.InaccPsi.R2.Va
