import Googology.Trans.PoR.InaccPsi.R2.FaAL

/-!
# Fa: THE SHAPE OF A MEMBER OF `D_K` AND OF ITS IMAGE

`T = Kz.vbTK S λ K`, for `x ∈ D_K`, `Ω₂ < x`:

* `fa_shape_cnf` (**a non-`ε` member is `ω^ℓ·n + r`, and `T x` has the parts `T ℓ`, `n`, `T r`**);
* `fa_T_eps_iff` (`ω^x = x ⇔ ω^{T x} = T x`), `fa_shape_veb` (**an `ε` member not strongly critical is `φ(a, b)`, and `T x` has the
  parts `T a`, `T b`**), `fa_T_SC_iff` (`SC x ⇔ SC (T x)`);
* `fa_shape_atom` (**a strongly critical non-cardinal member is `Hˡ⁽ᵏ⁺¹⁾_γ(y)` with `k ≥ 1`**), `fa_T_card` (the cardinals).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- **A non-`ε` member `x ≠ 0` and the parts of `T x`.** -/
theorem fa_shape_cnf {x : Ordinal.{0}} (hx : VbDK S l K x) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ x = ω ^ log ω x * n + x % ω ^ log ω x ∧ VbDK S l K (log ω x) ∧ VbDK S l K (x % ω ^ log ω x) ∧
      x % ω ^ log ω x < ω ^ log ω x ∧
      vbTK S l K x = ω ^ vbTK S l K (log ω x) * n + vbTK S l K (x % ω ^ log ω x) ∧
      vbTK S l K (x % ω ^ log ω x) < ω ^ vbTK S l K (log ω x) ∧ log ω (vbTK S l K x) = vbTK S l K (log ω x) ∧
      vbTK S l K x % ω ^ vbTK S l K (log ω x) = vbTK S l K (x % ω ^ log ω x) ∧
      vbTK S l K x / ω ^ vbTK S l K (log ω x) = n := by
  have hPC := faPC_D (S := S) (l := l) hKB
  obtain ⟨n, hdec, hlD, hrD, -⟩ := hPC.split hx hx0
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω x := opow_pos _ omega0_pos
  have hrlt : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x hpos.ne'
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, Nat.cast_zero, mul_zero, zero_add] at hdec
      exact absurd hdec (mod_opow_log_lt_self ω hx0).ne
    · exact h
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hT := kzT_cnf hl hX hKB n hn1 hlD hrD hrlt
  rw [hdec] at hT
  have hoD : VbDK S l K (ω ^ log ω x) := hPC.opow hlD
  have hTo : vbTK S l K (ω ^ log ω x) = ω ^ vbTK S l K (log ω x) := by
    have h := kzT_cnf hl hX hKB 1 le_rfl hlD hPC.zero hpos
    rwa [Nat.cast_one, mul_one, add_zero, vbTK_zero hl hX hKB, mul_one, add_zero] at h
  have hTr : vbTK S l K (x % ω ^ log ω x) < ω ^ vbTK S l K (log ω x) := by
    rw [← hTo]; exact vbTK_mono hl hX hKB hrD hoD hrlt
  have hO0 : ω ^ vbTK S l K (log ω x) ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨n, hn1, hdec.symm, hlD, hrD, hrlt, hT, hTr, ?_, ?_, ?_⟩
  · rw [hT, log_opow_mul_add one_lt_omega0 hn0 hTr, log_eq_zero (natCast_lt_omega0 n), add_zero]
  · rw [hT, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hTr]
  · rw [hT, Ordinal.mul_add_div _ hO0, Ordinal.div_eq_zero_of_lt hTr, add_zero]

/-- `ω^x = x ⇔ ω^{T x} = T x` for `Ω₂ ≤ x`... and for every member with `x ≠ 0`, `Ω₂ ≤ x`. -/
theorem fa_T_eps_iff {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) ≤ x) :
    ω ^ x = x ↔ ω ^ vbTK S l K x = vbTK S l K x := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hTo : vbTK S l K (ω ^ x) = ω ^ vbTK S l K x := by
    have h := kzT_cnf hl hX hKB 1 le_rfl hx hPC.zero (opow_pos _ omega0_pos)
    rwa [Nat.cast_one, mul_one, add_zero, vbTK_zero hl hX hKB, mul_one, add_zero] at h
  constructor
  · intro h; exact vbTK_eps hl hX hKB hx h2 h
  · intro h
    rcases (right_le_opow x one_lt_omega0).lt_or_eq with hlt | heq
    · exfalso
      have hoK : VbDK S l K (ω ^ x) := hPC.opow hx
      exact absurd (vbTK_inj hl hX hKB hoK hx (by rw [hTo, h])) hlt.ne'
    · exact heq.symm

/-- **An `ε` member above `Ω₂` that is not strongly critical is `φ(a, b)`, and `T x` has the parts `T a`, `T b`.** -/
theorem fa_shape_veb {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) < x) (hε : ω ^ x = x) (hS : ¬ SC x) :
    VbDK S l K (invVeblen₁ x) ∧ VbDK S l K (invVeblen₂ x) ∧ 0 < invVeblen₁ x ∧ invVeblen₁ x < x ∧ invVeblen₂ x < x ∧
      veblen (invVeblen₁ x) (invVeblen₂ x) = x ∧
      invVeblen₁ (vbTK S l K x) = vbTK S l K (invVeblen₁ x) ∧ invVeblen₂ (vbTK S l K x) = vbTK S l K (invVeblen₂ x) ∧
      vbTK S l K x = veblen (vbTK S l K (invVeblen₁ x)) (vbTK S l K (invVeblen₂ x)) := by
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans h2
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hS
  obtain ⟨haD, hbD, -, -, -, -⟩ := vbDK_veb hx hxE hv hb
  have hT := vbTK_veb hl hX hKB hx hv ha0.ne' hb h2.le
  have hTb : vbTK S l K (invVeblen₂ x) < vbTK S l K x := vbTK_mono hl hX hKB hbD hx hb
  have hTa : vbTK S l K (invVeblen₁ x) < vbTK S l K x := vbTK_mono hl hX hKB haD hx ha
  have hTa0 : vbTK S l K (invVeblen₁ x) ≠ 0 := by
    have h := vbTK_mono hl hX hKB (faPC_D (S := S) (l := l) hKB).zero haD ha0
    rw [vbTK_zero hl hX hKB] at h
    exact h.ne'
  have hbv : vbTK S l K (invVeblen₂ x) < veblen (vbTK S l K (invVeblen₁ x)) (vbTK S l K (invVeblen₂ x)) := by
    rw [← hT]; exact hTb
  refine ⟨haD, hbD, ha0, ha, hb, hv, ?_, ?_, hT⟩
  · rw [hT, invVeblen₁_veblen hbv]
  · rw [hT, invVeblen₂_veblen hTa0 hbv]

/-- **`SC x ⇔ SC (T x)`** above `Ω₂`. -/
theorem fa_T_SC_iff {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) < x) : SC x ↔ SC (vbTK S l K x) := by
  refine ⟨fun h => vbTK_SC hl hX hKB hx h2.le h, fun h => ?_⟩
  by_contra hS
  have hx0 : x ≠ 0 := ((Om_pos (by exact (add_pos_of_nonneg_of_pos zero_le zero_lt_one).ne')).trans h2).ne'
  by_cases hε : ω ^ x = x
  · obtain ⟨haD, hbD, -, ha, hb, -, -, -, hT⟩ := fa_shape_veb hl hX hKB hx h2 hε hS
    have hTa := vbTK_mono hl hX hKB haD hx ha
    have hTb := vbTK_mono hl hX hKB hbD hx hb
    have := h.2 _ hTa _ hTb
    rw [← hT] at this
    exact lt_irrefl _ this
  · have hTε : ω ^ vbTK S l K x = vbTK S l K x := gg_SC_eps h
    exact hε ((fa_T_eps_iff hl hX hKB hx h2.le).2 hTε)

/-- **A strongly critical non-cardinal member above `Ω₂` is an atom `Hˡ⁽ᵏ⁺¹⁾_γ(y)`, `k ≥ 1`.** -/
theorem fa_shape_atom {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) < x) (hS : SC x)
    (hΩ : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0})) (hW : x ≠ Om ω) :
    ∃ k : ℕ, 1 ≤ k ∧ Om ((k : Ordinal.{0}) + 1) < x ∧ x < Om ((k : Ordinal.{0}) + 1 + 1) ∧
      ∃ γ y, γ < Om ((k : Ordinal.{0}) + 1 + 1 + 1) ∧ y < x ∧ ulH S ((k : Ordinal.{0}) + 1) γ y = x := by
  have hx1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans h2
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨j, hj, d, -, -, hd, -⟩ := kzE_atom hKB hZ1.le hxE hS hx1 (kzNe hKB hxE hΩ hW)
  have hbd := psiS_bounds (S := S) d (j : Ordinal.{0})
  rw [← hd] at hbd
  have hj2 : 2 ≤ j := by
    by_contra hc
    have hj1 : j = 1 := by omega
    subst hj1
    rw [Nat.cast_one] at hbd
    exact absurd (h2.trans hbd.2) (lt_irrefl _)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  rw [Nat.cast_succ] at hbd
  refine ⟨k, hk, hbd.1, hbd.2, ?_⟩
  have hs := fa_nat1_lt k
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hr : Om (1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1) := by
    have hk1 : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
    exact Om_le_Om.2 (add_le_add hk1 le_rfl)
  have hθ : S.psi K (Om (1 + 1)) ≤ S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    ((psi_lt hκ2 _).le.trans hr).trans (Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) K).le
  have hA : x < S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    lt_psi_of_mem (InR_Om_succ _) (CSet_mono le_rfl hθ hx.2.1) hbd.2
  have hne := Vp.vp_nf_ex (S := S) (s := (k : Ordinal.{0}) + 1) hs hS hbd.1 hA
  obtain ⟨hlV, -, -, -, -⟩ := Vp.vpLev_spec hS hbd.1 hne
  obtain ⟨hI, hIlt⟩ := Vp.vp_nf hS hbd.1 hne
  exact ⟨_, _, hlV, hIlt, hI⟩

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Fa
