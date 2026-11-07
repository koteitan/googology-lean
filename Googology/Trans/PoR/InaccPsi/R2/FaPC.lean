import Googology.Trans.PoR.InaccPsi.R2.FaK
import Googology.Trans.PoR.InaccPsi.R2.VsMove

/-!
# Fa: THE PARTS OF AN ARGUMENT IN A CLOSED SET, THE ARITHMETIC OF `T`

* `FaPC` (a set closed under `0`, `+`, `φ`, `w - x`, `log`): `FaPC.opow`, `FaPC.mul_nat`, `FaPC.split`, `FaPC.mod`,
  `FaPC.div`, `FaPC.opow_mul`, `FaPC.dig_exp`, `FaPC.run` (**`B + W^γ·D ∈ P` gives `γ, D, B ∈ P`**, `W^{γ+1} ∣ B`,
  `0 < D < W`), `faPC_C` (`Cl(a, b)` is closed), `faPC_D` (`D_K` is closed);
* `faT_omul` (**`T(ω^x·y) = ω^{T x}·T y`**), `faT_Wmul` (**`T(W^γ·D) = W'^{T γ}·T D`**), `faT_dvd` (**`ω^e ∣ x ⇔
  ω^{T e} ∣ T x`**), `faT_Wdvd` (the same for `W^γ`);
* `fa_nota` (**a member of `Cl(a, b)` with `b` below a collapse is a closed term**).

No new axiom.  New definition: `FaPC` (a Prop).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

/-- A set closed under `0`, `+`, `φ` and the decompositions `w - x`, `log`. -/
structure FaPC (P : Ordinal.{0} → Prop) : Prop where
  zero : P 0
  add : ∀ {x y}, P x → P y → P (x + y)
  phi : ∀ {x y}, P x → P y → P (veblen x y)
  sub : ∀ {w x}, P w → P x → x ≤ w → P (w - x)
  log : ∀ {w}, P w → P (log ω w)

namespace FaPC

variable {P : Ordinal.{0} → Prop} (h : FaPC P)

include h

theorem opow {x : Ordinal.{0}} (hx : P x) : P (ω ^ x) := by
  have := h.phi h.zero hx; rwa [veblen_zero_apply] at this

theorem one : P 1 := by
  have := h.opow h.zero; rwa [opow_zero] at this

theorem mul_nat {x : Ordinal.{0}} (hx : P x) : ∀ n : ℕ, P (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact h.zero
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact h.add (mul_nat hx n) hx

theorem split {x : Ordinal.{0}} (hx : P x) (hx0 : x ≠ 0) :
    ∃ k : ℕ, ω ^ Ordinal.log ω x * k + x % ω ^ Ordinal.log ω x = x ∧ P (Ordinal.log ω x) ∧ P (x % ω ^ Ordinal.log ω x) ∧ x % ω ^ Ordinal.log ω x < x := by
  have hlog := h.log hx
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdec : ω ^ Ordinal.log ω x * k + x % ω ^ Ordinal.log ω x = x := by
    have := Ordinal.div_add_mod x (ω ^ Ordinal.log ω x); rwa [hk] at this
  have hwk : P (ω ^ Ordinal.log ω x * k) := h.mul_nat (h.opow hlog) k
  have hr : P (x % ω ^ Ordinal.log ω x) := by
    have e : x - ω ^ Ordinal.log ω x * k = x % ω ^ Ordinal.log ω x := by
      nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
    have hle : ω ^ Ordinal.log ω x * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    rw [← e]; exact h.sub hx hwk hle
  exact ⟨k, hdec, hlog, hr, mod_opow_log_lt_self _ hx0⟩

theorem mod : ∀ x, P x → ∀ f : Ordinal.{0}, P (x % ω ^ f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx f
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.mod_eq_of_lt (opow_pos f omega0_pos)]; exact h.zero
  obtain ⟨k, hdec, _, hr, hrx⟩ := h.split hx hx0
  rcases lt_or_ge (Ordinal.log ω x) f with hgf | hfg
  · have hxf : x < ω ^ f := (lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgf))
    rw [Ordinal.mod_eq_of_lt hxf]; exact hx
  · obtain ⟨c, hc⟩ : ω ^ f ∣ ω ^ Ordinal.log ω x * k := (opow_dvd_opow _ hfg).trans (dvd_mul_right _ _)
    have e : x % ω ^ f = x % ω ^ Ordinal.log ω x % ω ^ f := by
      conv_lhs => rw [← hdec, hc, Ordinal.mul_add_mod_self]
    rw [e]; exact IH _ hrx hr f

theorem div : ∀ x, P x → ∀ f : Ordinal.{0}, P f → P (x / ω ^ f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx f hf
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.div_eq_zero_of_lt (opow_pos f omega0_pos)]; exact h.zero
  obtain ⟨k, hdec, hlog, hr, hrx⟩ := h.split hx hx0
  rcases lt_or_ge (Ordinal.log ω x) f with hgf | hfg
  · have hxf : x < ω ^ f := (lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgf))
    rw [Ordinal.div_eq_zero_of_lt hxf]; exact h.zero
  · have hgf' : f + (Ordinal.log ω x - f) = Ordinal.log ω x := Ordinal.add_sub_cancel_of_le hfg
    have e : x = ω ^ f * (ω ^ (Ordinal.log ω x - f) * k) + x % ω ^ Ordinal.log ω x := by
      conv_lhs => rw [← hdec]
      rw [← mul_assoc, ← opow_add, hgf']
    have hdiv : x / ω ^ f = ω ^ (Ordinal.log ω x - f) * k + x % ω ^ Ordinal.log ω x / ω ^ f := by
      conv_lhs => rw [e]
      exact Ordinal.mul_add_div _ (opow_pos f omega0_pos).ne' _
    rw [hdiv]
    exact h.add (h.mul_nat (h.opow (h.sub hlog hf hfg)) k) (IH _ hrx hr f hf)

theorem opow_mul {a : Ordinal.{0}} (ha : P a) : ∀ b, P b → P (ω ^ a * b) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero]; exact h.zero
  obtain ⟨k, hdec, hlog, hr, hrx⟩ := h.split hb hb0
  have e : ω ^ a * b = ω ^ (a + Ordinal.log ω b) * k + ω ^ a * (b % ω ^ Ordinal.log ω b) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, ← opow_add]
  rw [e]
  exact h.add (h.mul_nat (h.opow (h.add ha hlog)) k) (IH _ hrx hr)

/-- The base-`W` exponent of a nonzero digit is in `P`. -/
theorem dig_exp {r : Ordinal.{0}} (hW : P (Om (r + 1))) {x : Ordinal.{0}} (hx : P x) (j : Ordinal.{0})
    (hd : x / Om (r + 1) ^ j % Om (r + 1) ≠ 0) : P j := by
  have hW0 : (Om (r + 1) : Ordinal.{0}) ≠ 0 := (Ui.ui_SC_W r).1.ne'
  have hWj0 : Om (r + 1) ^ j ≠ 0 := (Ui.ui_W_pos r j).ne'
  set y := x % Om (r + 1) ^ (j + 1) with hydef
  have hy : P y := by rw [hydef, Ui.ui_W_eq r]; exact h.mod x hx _
  have hylt : y < Om (r + 1) ^ j * Om (r + 1) := by
    rw [← Ui.ui_W_succ r]; exact Ordinal.mod_lt _ (Ui.ui_W_pos r _).ne'
  have hyd : y / Om (r + 1) ^ j < Om (r + 1) := (Ordinal.lt_mul_iff_div_lt hWj0).1 hylt
  have hid : x / Om (r + 1) ^ j % Om (r + 1) = y / Om (r + 1) ^ j := by
    have e1 : x = Om (r + 1) ^ j * (Om (r + 1) * (x / Om (r + 1) ^ (j + 1))) + y := by
      rw [← mul_assoc, ← Ui.ui_W_succ r, hydef, Ordinal.div_add_mod]
    have e2 : x / Om (r + 1) ^ j = Om (r + 1) * (x / Om (r + 1) ^ (j + 1)) + y / Om (r + 1) ^ j := by
      conv_lhs => rw [e1]
      exact Ordinal.mul_add_div _ hWj0 _
    rw [e2, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyd]
  rw [hid] at hd
  have hjy : Om (r + 1) ^ j ≤ y := by
    by_contra hc; exact hd (Ordinal.div_eq_zero_of_lt (not_le.1 hc))
  have hlog := h.log hy
  have h1 : Om (r + 1) * j ≤ Ordinal.log ω y :=
    le_log_of_opow_le one_lt_omega0 (by rw [← Ui.ui_W_eq r]; exact hjy)
  have h2 : Ordinal.log ω y < Om (r + 1) * (j + 1) := by
    by_contra hc
    have hc0 : Om (r + 1) * (j + 1) ≠ 0 := (mul_pos (Ui.ui_SC_W r).1 (zero_le.trans_lt (lt_add_one j))).ne'
    have := opow_le_of_le_log hc0 (not_lt.1 hc)
    rw [← Ui.ui_W_eq r, Ui.ui_W_succ r] at this
    exact absurd hylt (not_lt.2 this)
  have hgj : Ordinal.log ω y / Om (r + 1) = j := by
    apply le_antisymm
    · have := (Ordinal.lt_mul_iff_div_lt hW0).1 h2
      exact Order.lt_add_one_iff.1 this
    · exact (Ordinal.mul_le_iff_le_div hW0).1 h1
  have := h.div _ hlog _ hW
  rwa [Ui.ui_W_opow r, hgj] at this

/-- **The parts of `B + W^γ·D`** (`W^{γ+1} ∣ B`, `0 < D < W`). -/
theorem run {r B γ D : Ordinal.{0}} (hW : P (Om (r + 1))) (he : P (B + Om (r + 1) ^ γ * D))
    (hB : Om (r + 1) ^ (γ + 1) ∣ B) (hD0 : D ≠ 0) (hD : D < Om (r + 1)) : P γ ∧ P D ∧ P B := by
  set e := B + Om (r + 1) ^ γ * D with hedef
  have hWγ0 : Om (r + 1) ^ γ ≠ 0 := (Ui.ui_W_pos r γ).ne'
  have hdig : e / Om (r + 1) ^ γ % Om (r + 1) = D := by
    obtain ⟨t, ht⟩ := hB
    have e1 : e = Om (r + 1) ^ γ * (Om (r + 1) * t + D) := by
      rw [hedef, ht, Ui.ui_W_succ r, mul_add, mul_assoc]
    rw [e1, Ordinal.mul_div_cancel _ hWγ0, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hD]
  have hγK : P γ := h.dig_exp hW he γ (by rw [hdig]; exact hD0)
  have hWγ : P (Om (r + 1) * γ) := by
    have := h.opow_mul hW γ hγK; rwa [Ui.ui_W_opow r] at this
  have hDK : P D := by
    have h1 : P (e / Om (r + 1) ^ γ) := by rw [Ui.ui_W_eq r]; exact h.div e he _ hWγ
    have h2 := h.mod _ h1 (Om (r + 1))
    rwa [Ui.ui_W_opow r, hdig] at h2
  have hBK : P B := by
    have hγ1 : P (γ + 1) := h.add hγK h.one
    have hWγ1 : P (Om (r + 1) * (γ + 1)) := by
      have := h.opow_mul hW (γ + 1) hγ1; rwa [Ui.ui_W_opow r] at this
    have hBeq : B = Om (r + 1) ^ (γ + 1) * (e / Om (r + 1) ^ (γ + 1)) := by
      obtain ⟨t, ht⟩ := hB
      have hpos : Om (r + 1) ^ (γ + 1) ≠ 0 := (Ui.ui_W_pos r _).ne'
      have hlt : Om (r + 1) ^ γ * D < Om (r + 1) ^ (γ + 1) := by
        rw [Ui.ui_W_succ r]; exact (mul_lt_mul_iff_right₀ (Ui.ui_W_pos r γ)).2 hD
      have : e / Om (r + 1) ^ (γ + 1) = t := by
        rw [hedef, ht, Ordinal.mul_add_div _ hpos, Ordinal.div_eq_zero_of_lt hlt, add_zero]
      rw [this, ht]
    rw [hBeq, Ui.ui_W_eq r]
    exact h.opow_mul hWγ1 _ (h.div e he _ hWγ1)
  exact ⟨hγK, hDK, hBK⟩

end FaPC

/-- `Cl(a, b)` is closed. -/
theorem faPC_C (a b : Ordinal.{0}) : FaPC (· ∈ S.CSet a b) where
  zero := CSet.zero_mem _ _
  add := CSet.add_mem
  phi := CSet.phi_mem
  sub := fun hw hx hle => (rxCDec _ hw).1 _ hx hle
  log := fun hw => (rxCDec _ hw).2

/-- `D_K` is closed. -/
theorem faPC_D {l K : Ordinal.{0}} (hKB : KzB S K) : FaPC (VbDK S l K) where
  zero := ⟨CSet.zero_mem _ _, CSet.zero_mem _ _, hKB.sc.1⟩
  add := fun hx hy => ⟨CSet.add_mem hx.1 hy.1, CSet.add_mem hx.2.1 hy.2.1, hKB.sc.isPrincipal hx.2.2 hy.2.2⟩
  phi := fun hx hy => ⟨CSet.phi_mem hx.1 hy.1, CSet.phi_mem hx.2.1 hy.2.1, hKB.sc.2 _ hx.2.2 _ hy.2.2⟩
  sub := fun {_ _} hw hx hle => ⟨(rxCDec _ hw.1).1 _ hx.1 hle, (rxCDec _ hw.2.1).1 _ hx.2.1 hle,
    (Ordinal.sub_le_self _ _).trans_lt hw.2.2⟩
  log := fun hw => ⟨(rxCDec _ hw.1).2, (rxCDec _ hw.2.1).2, (log_le_self ω _).trans_lt hw.2.2⟩

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- **`T(ω^x·y) = ω^{T x}·T y`.** -/
theorem faT_omul {x y : Ordinal.{0}} (hx : VbDK S l K x) (hy : VbDK S l K y) :
    vbTK S l K (ω ^ x * y) = ω ^ vbTK S l K x * vbTK S l K y := by
  obtain ⟨hxE, hxK⟩ := vbTK_eq hl hX hKB hx
  obtain ⟨hyE, hyK⟩ := vbTK_eq hl hX hKB hy
  have h := kzK_omul hl hX hKB _ hyE _ hxE
  rw [hxK, hyK] at h
  rw [← h]; exact vbTK_K hl hX hKB (kzE_omul hKB _ hyE _ hxE)

/-- **`T(W^γ·D) = W'^{T γ}·T D`** for `W = Ω_{k+2}`, `W' = Ω_{k+1}`. -/
theorem faT_Wmul {k : ℕ} {γ D : Ordinal.{0}} (hγ : VbDK S l K γ) (hD : VbDK S l K D) :
    vbTK S l K (Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D) =
      Om ((k : Ordinal.{0}) + 1) ^ vbTK S l K γ * vbTK S l K D := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hW := fa_Om2_D (S := S) (l := l) hKB k
  have hWγ : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) := by
    have := hPC.opow_mul hW γ hγ; rwa [Ui.ui_W_opow _] at this
  have e1 : vbTK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) = Om ((k : Ordinal.{0}) + 1) * vbTK S l K γ := by
    have h := faT_omul hl hX hKB hW hγ
    rwa [Ui.ui_W_opow _, fa_T_Om2 hl hX hKB, Ui.ui_W_opow _] at h
  rw [Ui.ui_W_eq, faT_omul hl hX hKB hWγ hD, e1, Ui.ui_W_eq]

omit hl hX hKB in
/-- `ω^e ∣ ω^ℓ·n + r ⇔ e ≤ ℓ ∧ ω^e ∣ r` (`r < ω^ℓ`, `n ≥ 1`). -/
theorem fa_dvd_cnf {e L r : Ordinal.{0}} {n : ℕ} (hn : 1 ≤ n) (hr : r < ω ^ L) :
    ω ^ e ∣ ω ^ L * n + r ↔ e ≤ L ∧ ω ^ e ∣ r := by
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  constructor
  · intro h
    have h0 : ω ^ L * n + r ≠ 0 := ((mul_pos (opow_pos _ omega0_pos) (pos_iff_ne_zero.2 hn0)).trans_le le_self_add).ne'
    have hle : ω ^ e ≤ ω ^ L * n + r := Ordinal.le_of_dvd h0 h
    have heL : e ≤ L := by
      by_contra hc
      push Not at hc
      have h1 : ω ^ L * n + r < ω ^ L * ω := by
        have h2 : ω ^ L * n + r < ω ^ L * n + ω ^ L := (add_lt_add_iff_left _).2 hr
        have h3 : ω ^ L * n + ω ^ L = ω ^ L * ((n + 1 : ℕ) : Ordinal.{0}) := by
          rw [Nat.cast_succ, mul_add_one]
        rw [h3] at h2
        exact h2.trans ((mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (natCast_lt_omega0 _))
      have h4 : ω ^ L * ω ≤ ω ^ e := by
        have := opow_le_opow_right (a := ω) omega0_pos (Order.add_one_le_of_lt hc)
        rwa [opow_add, opow_one] at this
      exact absurd hle (not_le.2 (h1.trans_le h4))
    refine ⟨heL, ?_⟩
    have h1 : ω ^ e ∣ ω ^ L * n := Dvd.dvd.mul_right (opow_dvd_opow _ heL) _
    exact (Ordinal.dvd_add_iff h1).1 h
  · rintro ⟨h1, h2⟩
    exact dvd_add (Dvd.dvd.mul_right (opow_dvd_opow _ h1) _) h2

/-- **`ω^e ∣ x ⇔ ω^{T e} ∣ T x`.** -/
theorem faT_dvd {e : Ordinal.{0}} (he : VbDK S l K e) :
    ∀ x, VbDK S l K x → (ω ^ e ∣ x ↔ ω ^ vbTK S l K e ∣ vbTK S l K x) := by
  have hPC := faPC_D (S := S) (l := l) hKB
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [vbTK_zero hl hX hKB]; exact ⟨fun _ => dvd_zero _, fun _ => dvd_zero _⟩
  obtain ⟨n, hdec, hlD, hrD, hrx⟩ := hPC.split hx hx0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, Nat.cast_zero, mul_zero, zero_add] at hdec
      exact absurd hdec hrx.ne
    · exact h
  have hrlt : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
  have hT := kzT_cnf hl hX hKB n hn1 hlD hrD hrlt
  rw [hdec] at hT
  have hoD : VbDK S l K (ω ^ log ω x) := hPC.opow hlD
  have hTo : vbTK S l K (ω ^ log ω x) = ω ^ vbTK S l K (log ω x) := by
    have h := kzT_cnf hl hX hKB 1 le_rfl hlD hPC.zero (opow_pos _ omega0_pos)
    rwa [Nat.cast_one, mul_one, add_zero, vbTK_zero hl hX hKB, mul_one, add_zero] at h
  have hTr : vbTK S l K (x % ω ^ log ω x) < ω ^ vbTK S l K (log ω x) := by
    rw [← hTo]; exact vbTK_mono hl hX hKB hrD hoD hrlt
  conv_lhs => rw [← hdec]
  rw [hT, fa_dvd_cnf hn1 hrlt, fa_dvd_cnf hn1 hTr, IH _ hrx hrD, vbTK_le_iff hl hX hKB he hlD]

/-- **`W^γ ∣ x ⇔ W'^{T γ} ∣ T x`** for `W = Ω_{k+2}`, `W' = Ω_{k+1}`. -/
theorem faT_Wdvd {k : ℕ} {γ x : Ordinal.{0}} (hγ : VbDK S l K γ) (hx : VbDK S l K x) :
    Om ((k : Ordinal.{0}) + 1 + 1) ^ γ ∣ x ↔ Om ((k : Ordinal.{0}) + 1) ^ vbTK S l K γ ∣ vbTK S l K x := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hW := fa_Om2_D (S := S) (l := l) hKB k
  have hWγ : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) := by
    have := hPC.opow_mul hW γ hγ; rwa [Ui.ui_W_opow _] at this
  have e1 : vbTK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) = Om ((k : Ordinal.{0}) + 1) * vbTK S l K γ := by
    have h := faT_omul hl hX hKB hW hγ
    rwa [Ui.ui_W_opow _, fa_T_Om2 hl hX hKB, Ui.ui_W_opow _] at h
  rw [Ui.ui_W_eq, Ui.ui_W_eq, faT_dvd hl hX hKB hWγ x hx, e1]

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Fa
