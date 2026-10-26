import Googology.Trans.PoR.InaccPsi.R2.HgVD

/-!
# HgVHC: TEXTUAL COPY OF `Hc.HcVHC` FOR `Hg.HgVD` (readings below `Γ_{x+2}`)

The declarations of `Hc.HcVHC` with `Hc.HcVD` (bound field `Z(x) ≤ B_x(x)`) replaced by `Hg.HgVD` (bound
field `Z(x) < Γ_{x+2}`); the proofs are unchanged except where the bound enters (`HgVD.R_lt_gq`, the field
`Z_G1`, Lemma IMG in `HgVD.toLD` through `He.he_pkg_G1`).

No new axiom.  New definitions: the copies of the definitions of `Hc.HcVHC` (namespace `HgVD`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha

open Googology.Trans.PoR.InaccPsi.R2.Gw

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

namespace HgVD

variable (D : HgVD)

theorem ne_of_le {c : Ordinal.{0}} (h : D.B ≤ c) : c ≠ 0 := (lt_of_lt_of_le D.B_E.pos h).ne'

theorem pow_eq (k : Ordinal.{0}) : D.B ^ k = ω ^ (D.B * k) := by
  rw [opow_mul, show ω ^ D.B = D.B from D.B_E]

theorem pow_indec {k : Ordinal.{0}} : ∀ u v, u < D.B ^ k → v < D.B ^ k → u + v < D.B ^ k := by
  intro u v hu hv
  rw [D.pow_eq] at hu hv ⊢
  exact isPrincipal_add_omega0_opow _ hu hv

/-- **The normal form** `B^k·d + r`. -/
theorem cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < D.B) (hr : r < D.B ^ k) :
    log (D.B) (D.B ^ k * d + r) = k ∧ (D.B ^ k * d + r) / D.B ^ k = d ∧
      (D.B ^ k * d + r) % D.B ^ k = r ∧ D.B ≤ D.B ^ k * d + r := by
  have hp : D.B ^ k ≠ 0 := opow_ne_zero _ D.B_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [log_opow_mul_add D.one_lt_B hd0 hr, log_eq_zero hdE, add_zero]
  · rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  · calc D.B = D.B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ D.B ^ k := opow_le_opow_right D.B_E.pos (one_le_iff_ne_zero.2 hk)
      _ = D.B ^ k * 1 := (mul_one _).symm
      _ ≤ D.B ^ k * d := mul_le_mul_left' (one_le_iff_ne_zero.2 hd0) _
      _ ≤ _ := le_self_add

/-- **The parts of a code `c ≥ G`.** -/
theorem parts0 {c : Ordinal.{0}} (hc : D.B ≤ c) :
    log (D.B) c ≠ 0 ∧ c / D.B ^ log (D.B) c ≠ 0 ∧ c / D.B ^ log (D.B) c < D.B ∧
      c % D.B ^ log (D.B) c < D.B ^ log (D.B) c ∧
      D.B ^ log (D.B) c * (c / D.B ^ log (D.B) c) + c % D.B ^ log (D.B) c = c := by
  have hc0 := D.ne_of_le hc
  refine ⟨?_, (div_opow_log_pos (D.B) hc0).ne', div_opow_log_lt c D.one_lt_B,
    Ordinal.mod_lt c (opow_ne_zero _ D.B_ne), Ordinal.div_add_mod c _⟩
  have := le_log_of_opow_le D.one_lt_B (show D.B ^ (1 : Ordinal.{0}) ≤ c by rw [opow_one]; exact hc)
  exact (zero_lt_one.trans_le this).ne'

/-! ## The bound `ε_{B+1}` -/

/-- **The bound**: `ε_{B+1}`, the least `ε`-number above `B`. -/
noncomputable def NB : Ordinal.{0} := eN D.B

theorem NB_E : InE D.NB := eN_E (D.B)

theorem B_lt_NB : D.B < D.NB := lt_eN (D.B)

theorem NB_lim : IsSuccLimit D.NB := ev_isSuccLimit_of_inE D.NB_E

/-- **`log_B c < c` for `B ≤ c < ε_{B+1}`**: otherwise `c = B^c` would be an `ε`-number in `(B, ε_{B+1})`. -/
theorem log_lt {c : Ordinal.{0}} (h1 : D.B ≤ c) (h2 : c < D.NB) : log (D.B) c < c := by
  have hc0 := D.ne_of_le h1
  have hle : D.B ^ log (D.B) c ≤ c := opow_log_le_self (D.B) hc0
  have hl1 : 1 ≤ log (D.B) c := le_log_of_opow_le D.one_lt_B (by rw [opow_one]; exact h1)
  rcases (right_le_opow (log (D.B) c) D.one_lt_B).lt_or_eq with h | h
  · exact h.trans_le hle
  exfalso
  set l := log (D.B) c with hl
  have hlE : InE l := by
    refine le_antisymm ?_ (right_le_opow l one_lt_omega0)
    calc ω ^ l ≤ ω ^ (D.B * l) := opow_le_opow_right omega0_pos (le_mul_right l D.B_E.pos)
      _ = D.B ^ l := (D.pow_eq l).symm
      _ = l := h.symm
  have hEl : D.B ≤ l := by
    rw [h]; calc D.B = D.B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ D.B ^ l := opow_le_opow_right D.B_E.pos hl1
  rcases hEl.lt_or_eq with hlt | heq
  · exact absurd ((eN_le hlt hlE).trans_lt ((right_le_opow l D.one_lt_B).trans_lt (hle.trans_lt h2))) (lt_irrefl _)
  · have : D.B ^ (1 : Ordinal.{0}) < D.B ^ D.B := (opow_lt_opow_iff_right D.one_lt_B).2 D.one_lt_B
    rw [opow_one] at this
    rw [← heq] at h
    exact absurd h this.ne

/-! ## The reading and the gate -/

/-- **The reading** of `c = B^k·d + r` at `x`: `b(x)^{k(x)}·d(x) + r(x)`, the exponent read recursively; below
`B` the digit reading `D.R`. -/
noncomputable def hR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if h : D.B ≤ c ∧ c < D.NB then
    D.b x ^ hR (log (D.B) c) x * D.R (c / D.B ^ log (D.B) c) x + hR (c % D.B ^ log (D.B) c) x
  else D.R c x
termination_by c
decreasing_by
  all_goals first
    | exact D.log_lt h.1 h.2
    | exact mod_opow_log_lt_self (D.B) (D.ne_of_le h.1)

/-- **The gate** of `c = B^k·d + r`: the gate of `k` when infinite, of `d` when infinite, and of `r`. -/
noncomputable def hG (c : Ordinal.{0}) : Ordinal.{0} :=
  if h : D.B ≤ c ∧ c < D.NB then
    max (max (if log (D.B) c < ω then 0 else hG (log (D.B) c)) (D.Q (c / D.B ^ log (D.B) c)))
      (hG (c % D.B ^ log (D.B) c))
  else D.g c
termination_by c
decreasing_by
  all_goals first
    | exact D.log_lt h.1 h.2
    | exact mod_opow_log_lt_self (D.B) (D.ne_of_le h.1)

/-- **The gate of an exponent**: `0` when finite. -/
noncomputable def hQ (k : Ordinal.{0}) : Ordinal.{0} := if k < ω then 0 else D.hG k

theorem hR_low {c : Ordinal.{0}} (hc : c < D.B) (x : Ordinal.{0}) : D.hR c x = D.R c x := by
  rw [HgVD.hR, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

theorem hG_low {c : Ordinal.{0}} (hc : c < D.B) : D.hG c = D.g c := by
  rw [HgVD.hG, dif_neg (fun h => absurd h.1 (not_le.2 hc))]

/-- Above the new bound the reading and the gate are those of the digit system. -/
theorem hR_high {c : Ordinal.{0}} (hc : D.NB ≤ c) (x : Ordinal.{0}) : D.hR c x = D.R c x := by
  rw [HgVD.hR, dif_neg (fun h => absurd h.2 (not_lt.2 hc))]

theorem hG_high {c : Ordinal.{0}} (hc : D.NB ≤ c) : D.hG c = D.g c := by
  rw [HgVD.hG, dif_neg (fun h => absurd h.2 (not_lt.2 hc))]

theorem hR_dec {c : Ordinal.{0}} (hc : D.B ≤ c) (hcB : c < D.NB) (x : Ordinal.{0}) :
    D.hR c x = D.b x ^ D.hR (log (D.B) c) x * D.R (c / D.B ^ log (D.B) c) x +
      D.hR (c % D.B ^ log (D.B) c) x := by
  rw [HgVD.hR, dif_pos ⟨hc, hcB⟩]

theorem hG_dec {c : Ordinal.{0}} (hc : D.B ≤ c) (hcB : c < D.NB) :
    D.hG c = max (max (D.hQ (log (D.B) c)) (D.Q (c / D.B ^ log (D.B) c))) (D.hG (c % D.B ^ log (D.B) c)) := by
  rw [HgVD.hG, dif_pos ⟨hc, hcB⟩]; rfl

theorem hQ_le (k : Ordinal.{0}) : D.hQ k ≤ D.hG k := by
  unfold HgVD.hQ; split_ifs
  · exact zero_le
  · exact le_rfl

theorem hQ_low {k : Ordinal.{0}} (hk : k < D.B) : D.hQ k = D.Q k := by
  unfold HgVD.hQ HgVD.Q; rw [D.hG_low hk]

theorem hQ_nat (n : ℕ) : D.hQ n = 0 := by unfold HgVD.hQ; rw [if_pos (natCast_lt_omega0 n)]

theorem hR_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < D.B) (hr : r < D.B ^ k)
    (hB : D.B ^ k * d + r < D.NB) (x : Ordinal.{0}) :
    D.hR (D.B ^ k * d + r) x = D.b x ^ D.hR k x * D.R d x + D.hR r x := by
  obtain ⟨h1, h2, h3, h4⟩ := D.cnf hk hd0 hdE hr
  rw [D.hR_dec h4 hB, h1, h2, h3]

theorem hG_cnf {k d r : Ordinal.{0}} (hk : k ≠ 0) (hd0 : d ≠ 0) (hdE : d < D.B) (hr : r < D.B ^ k)
    (hB : D.B ^ k * d + r < D.NB) : D.hG (D.B ^ k * d + r) = max (max (D.hQ k) (D.Q d)) (D.hG r) := by
  obtain ⟨h1, h2, h3, h4⟩ := D.cnf hk hd0 hdE hr
  rw [D.hG_dec h4 hB, h1, h2, h3]

theorem hG_zero : D.hG 0 = 0 := by rw [D.hG_low D.B_E.pos, D.g_zero]

theorem hR_zero (x : Ordinal.{0}) : D.hR 0 x = 0 := by rw [D.hR_low D.B_E.pos, D.R_zero]

theorem hR_one (x : Ordinal.{0}) : D.hR 1 x = 1 := by rw [D.hR_low D.one_lt_B, D.R_one]

theorem hR_nat (n : ℕ) (x : Ordinal.{0}) : D.hR n x = n := by rw [D.hR_low (D.nat_lt_B n), D.R_nat]

theorem hG_nat (n : ℕ) : D.hG n = D.g n := D.hG_low (D.nat_lt_B n)

theorem NB_gt_pow {k : Ordinal.{0}} (hk : k < D.NB) : D.B ^ k < D.NB := by
  rw [D.pow_eq]; exact D.NB_E.opow_lt (D.NB_E.mul_lt D.B_lt_NB hk)

theorem mul_lt {k d : Ordinal.{0}} (hk : k < D.NB) (hd : d < D.B) : D.B ^ k * d < D.NB :=
  D.NB_E.mul_lt (D.NB_gt_pow hk) (hd.trans D.B_lt_NB)

theorem B_cnf : D.B = D.B ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]

theorem hG_G : D.hG (D.B) = 0 := by
  rw [D.B_cnf, D.hG_cnf one_ne_zero one_ne_zero D.one_lt_B (opow_pos _ D.B_E.pos)
    (by rw [← D.B_cnf]; exact D.B_lt_NB), D.Q_one, D.hG_zero]
  have : D.hQ 1 = 0 := by exact_mod_cast D.hQ_nat 1
  rw [this]; simp

theorem hR_G (x : Ordinal.{0}) : D.hR (D.B) x = D.b x := by
  rw [D.B_cnf, D.hR_cnf one_ne_zero one_ne_zero D.one_lt_B (opow_pos _ D.B_E.pos)
    (by rw [← D.B_cnf]; exact D.B_lt_NB), D.hR_one, opow_one, D.R_one, mul_one, D.hR_zero, add_zero]

/-- The parts of a code `B ≤ c < ε_{B+1}`. -/
theorem parts {c : Ordinal.{0}} (hc : D.B ≤ c) (hcB : c < D.NB) :
    log (D.B) c ≠ 0 ∧ c / D.B ^ log (D.B) c ≠ 0 ∧ c / D.B ^ log (D.B) c < D.B ∧
      c % D.B ^ log (D.B) c < D.B ^ log (D.B) c ∧
      D.B ^ log (D.B) c * (c / D.B ^ log (D.B) c) + c % D.B ^ log (D.B) c = c ∧
      log (D.B) c < c ∧ c % D.B ^ log (D.B) c < c :=
  let ⟨h1, h2, h3, h4, h5⟩ := D.parts0 hc
  ⟨h1, h2, h3, h4, h5, D.log_lt hc hcB, mod_opow_log_lt_self (D.B) (D.ne_of_le hc)⟩

/-- The normal form of `b + 1` for `b ≥ G`. -/
theorem succ_cnf {b : Ordinal.{0}} (hEb : D.B ≤ b) :
    b + 1 = D.B ^ log (D.B) b * (b / D.B ^ log (D.B) b) + (b % D.B ^ log (D.B) b + 1) ∧
      b % D.B ^ log (D.B) b + 1 < D.B ^ log (D.B) b := by
  obtain ⟨hk, -, -, hr, hdec⟩ := D.parts0 hEb
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← hdec]
    rw [add_assoc]
  · rw [D.pow_eq] at hr ⊢
    have hk0 : D.B * log (D.B) b ≠ 0 := mul_ne_zero D.B_ne hk
    exact (Ph.ph_opow_lim hk0).add_one_lt hr

/-! ## `1 + a` -/

theorem hQ_one_add (a : Ordinal.{0}) : D.hQ (1 + a) = D.hQ a := by
  rcases lt_or_ge a ω with ha | ha
  · obtain ⟨n, rfl⟩ := lt_omega0.1 ha
    have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [this, D.hQ_nat, D.hQ_nat]
  · rw [one_add_of_omega0_le ha]

/-! ## The towers `B`, `B^G`, `B^{G^G}`, … -/

/-- The towers: `D.hTw 0 = G`, `D.hTw (n+1) = G^{D.hTw n}`. -/
noncomputable def hTw : ℕ → Ordinal.{0}
  | 0 => D.B
  | n + 1 => D.B ^ hTw n

theorem hTw_lt : ∀ n : ℕ, D.hTw n < D.NB
  | 0 => D.B_lt_NB
  | n + 1 => D.NB_gt_pow (hTw_lt n)

theorem hTw_ge : ∀ n : ℕ, D.B ≤ D.hTw n
  | 0 => le_rfl
  | n + 1 => by
    show D.B ≤ D.B ^ D.hTw n
    calc D.B = D.B ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right D.B_E.pos (D.one_lt_B.le.trans (hTw_ge n))

theorem hTw_strict (n : ℕ) : D.hTw n < D.hTw (n + 1) := by
  show D.hTw n < D.B ^ D.hTw n
  have h1 := D.log_lt (c := D.B ^ D.hTw n) ((D.hTw_ge n).trans (right_le_opow _ D.one_lt_B)) (D.hTw_lt (n + 1))
  rwa [log_opow D.one_lt_B] at h1

theorem hTw_cof {c : Ordinal.{0}} (hc : c < D.NB) : ∃ n : ℕ, c < D.hTw n := by
  have hle : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (D.B + 1) ≤ D.hTw (n + 1) := by
    intro n
    induction n with
    | zero =>
      show D.B + 1 ≤ D.B ^ D.B
      have : D.B ^ (1 : Ordinal.{0}) < D.B ^ D.B := (opow_lt_opow_iff_right D.one_lt_B).2 D.one_lt_B
      rw [opow_one] at this
      exact Order.add_one_le_of_lt this
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      show ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (D.B + 1)) ≤ D.B ^ D.hTw (n + 1)
      calc ω ^ ((fun a : Ordinal.{0} => ω ^ a)^[n] (D.B + 1)) ≤ ω ^ D.hTw (n + 1) :=
            opow_le_opow_right omega0_pos ih
        _ ≤ D.B ^ D.hTw (n + 1) := opow_le_opow_left _ (omega0_lt_inE D.B_E).le
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hc
  exact ⟨n + 1, hn.trans_le (hle n)⟩


/-- `ε_{B+1} < Γ_{Ω₁+2}`. -/
theorem NB_lt1 : D.NB < gcG 1 := go_eN_lt_SC (gcG_SC 1) D.B_lt1

/-- `ε_{B+1} < Γ_{Ω₁+1+ε_{B+1}}` (the bound condition of a code system). -/
theorem NB_V : D.NB < gcG D.NB :=
  D.NB_lt1.trans_le (gcG_le (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le D.B_lt_NB)))

theorem B_V : D.B < gcG D.B :=
  D.B_lt1.trans_le (gcG_le (Order.one_le_iff_pos.2 D.B_pos))

end HgVD

end Googology.Trans.PoR.InaccPsi.R2.Hg
