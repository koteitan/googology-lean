import Googology.Trans.PoR.InaccPsi.R2.GdDFr
import Googology.Trans.PoR.InaccPsi.R2.RjArg

/-!
# Codes below `Ω₁^ω` and their readings at a base: the substitution `Ω₁ ↦ x` on the `Ω₁`-adic digits

A code `a < Ω₁^ω` is a polynomial `Ω₁^{n-1}·c_{n-1} + ⋯ + Ω₁·c₁ + c₀` with digits `cᵢ < Ω₁`.  At a base `x` above
all digits it reads `x^{n-1}·c_{n-1} + ⋯ + c₀`.  Here, on the levels `n` (`a < Ω₁^n`):

* `oP n = Ω₁^n`, `sbN n a x` (**the reading**), `gtN n a` (**the gate**: the largest digit);
* `sbN_lt` (`sbN n a x < x^n`), `sbN_lt_mono` (**the reading is strictly increasing** on codes with digits below
  `x`), `sbN_surj` (**every `ν < x^n` is the reading of a code with digits below `x`**), `sbN_stab` (one more level
  changes nothing), `sbN_one` (`sbN 1 a x = a`), `sbN_succ` (**`sbN n (a+1) x = sbN n a x + 1`**), `sbN_lim`
  (**the last term of a limit code**: `sbN n a x = sbN n a' x + ω^{x·k+d}` with `ω^{x·k+d} ∣ sbN n a' x`, uniformly
  in the base, `d` at most the gate), `sbN_pi` (**Lemma EXACT**: `π_{σ,ρ}(sbN n a ρ) = sbN n a σ`);
* the level-free versions `sbc`, `gate` (`sbc_eq`, `gate_eq`), and `lt_W_iff` (`a < Ω₁^ω` iff `a < Ω₁^n` for some
  `n`).

No new axiom.  New definitions: `oP`, `sbN`, `gtN`, `deg`, `sbc`, `gate`, `geW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ge

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- `Ω₁^n`. -/
noncomputable def oP (n : ℕ) : Ordinal.{0} := Om1 ^ (n : Ordinal.{0})

/-- **The reading at the base `x`** of a code `a < Ω₁^n`. -/
noncomputable def sbN : ℕ → Ordinal.{0} → Ordinal.{0} → Ordinal.{0}
  | 0, _, _ => 0
  | n + 1, a, x => x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x

/-- **The gate** of a code `a < Ω₁^n`: its largest digit. -/
noncomputable def gtN : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0, _ => 0
  | n + 1, a => max (a / oP n) (gtN n (a % oP n))

theorem Om1_ne : Om1 ≠ 0 := (Ordinal.omega_pos 1).ne'

theorem oP_ne (n : ℕ) : oP n ≠ 0 := by
  unfold oP; exact (opow_pos _ (Ordinal.omega_pos 1)).ne'

theorem oP_zero : oP 0 = 1 := by unfold oP; simp

theorem oP_succ (n : ℕ) : oP (n + 1) = oP n * Om1 := by
  unfold oP; rw [Nat.cast_succ, opow_add, opow_one]

theorem oP_eq (n : ℕ) : oP n = ω ^ (Om1 * (n : Ordinal.{0})) := by
  unfold oP
  rw [opow_mul, show ω ^ Om1 = Om1 from Rj.rj_Om1_inE]

theorem oP_indec (n : ℕ) : Indec (oP n) := by rw [oP_eq]; exact indec_opow _

theorem oP_mono {m n : ℕ} (h : m ≤ n) : oP m ≤ oP n := by
  unfold oP
  exact opow_le_opow_right (Ordinal.omega_pos 1) (by exact_mod_cast h)

theorem one_lt_oP {n : ℕ} (hn : 1 ≤ n) : 1 < oP n := by
  have h1 : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E Rj.rj_Om1_inE)
  calc (1 : Ordinal.{0}) < oP 1 := by rw [show oP 1 = Om1 by unfold oP; simp]; exact h1
    _ ≤ oP n := oP_mono hn

theorem oP_succ_lt {n : ℕ} (hn : 1 ≤ n) {r : Ordinal.{0}} (hr : r < oP n) : r + 1 < oP n :=
  (oP_indec n).add_lt hr (one_lt_oP hn)

theorem sbN_zero_code : ∀ (n : ℕ) (x : Ordinal.{0}), sbN n 0 x = 0
  | 0, _ => rfl
  | n + 1, x => by
      simp only [sbN, Ordinal.zero_div, mul_zero, Ordinal.zero_mod, zero_add]
      exact sbN_zero_code n x

theorem gtN_zero_code : ∀ n : ℕ, gtN n 0 = 0
  | 0 => rfl
  | n + 1 => by
      simp only [gtN, Ordinal.zero_div, Ordinal.zero_mod]
      rw [gtN_zero_code n]; simp

/-- A code `oP n · q + r` (`r < oP n`): its leading digit and its rest. -/
theorem dm_eq {n : ℕ} {q r : Ordinal.{0}} (hr : r < oP n) :
    (oP n * q + r) / oP n = q ∧ (oP n * q + r) % oP n = r := by
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div q (oP_ne n) r, Ordinal.div_eq_zero_of_lt hr, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

theorem dm_lt {n : ℕ} {a : Ordinal.{0}} (ha : a < oP (n + 1)) : a / oP n < Om1 := by
  rw [oP_succ] at ha
  exact (Ordinal.div_lt (oP_ne n)).2 ha

/-! ## Size and order -/

/-- **`sbN n a x < x^n`** when every digit is below `x`. -/
theorem sbN_lt {x : Ordinal.{0}} (hx : 0 < x) : ∀ (n : ℕ) (a : Ordinal.{0}), gtN n a < x →
    sbN n a x < x ^ (n : Ordinal.{0})
  | 0, a, _ => by simp [sbN]
  | n + 1, a, h => by
      simp only [gtN, max_lt_iff] at h
      have ih := sbN_lt hx n (a % oP n) h.2
      show x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x < x ^ ((n + 1 : ℕ) : Ordinal.{0})
      calc x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x
          < x ^ (n : Ordinal.{0}) * (a / oP n) + x ^ (n : Ordinal.{0}) := (add_lt_add_iff_left _).2 ih
        _ = x ^ (n : Ordinal.{0}) * (a / oP n + 1) := by rw [mul_add_one]
        _ ≤ x ^ (n : Ordinal.{0}) * x := mul_le_mul_left' (add_one_le_of_lt h.1) _
        _ = x ^ ((n + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, opow_add, opow_one]

theorem div_le_div_of_lt {a b c : Ordinal.{0}} (hc : c ≠ 0) (h : a < b) : a / c ≤ b / c := by
  by_contra hlt
  push Not at hlt
  have h1 := Ordinal.lt_mul_succ_div b hc
  have h2 : c * succ (b / c) ≤ c * (a / c) := mul_le_mul_left' (succ_le_of_lt hlt) _
  have h3 := Ordinal.mul_div_le a c
  exact absurd (h.trans (h1.trans_le (h2.trans h3))) (lt_irrefl _)

/-- **The reading is strictly increasing** on the codes below `oP n` with digits below `x`. -/
theorem sbN_lt_mono {x : Ordinal.{0}} (hx : 0 < x) : ∀ (n : ℕ) (a b : Ordinal.{0}), a < b → b < oP n →
    gtN n a < x → gtN n b < x → sbN n a x < sbN n b x
  | 0, a, b, hab, hb, _, _ => by
      rw [oP_zero, Ordinal.lt_one_iff_zero] at hb
      exact absurd (hb ▸ hab) (not_lt.2 zero_le)
  | n + 1, a, b, hab, _, ha, hb => by
      simp only [gtN, max_lt_iff] at ha hb
      show x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x <
        x ^ (n : Ordinal.{0}) * (b / oP n) + sbN n (b % oP n) x
      have hq := div_le_div_of_lt (oP_ne n) hab
      rcases hq.lt_or_eq with hq | hq
      · calc x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x
            < x ^ (n : Ordinal.{0}) * (a / oP n) + x ^ (n : Ordinal.{0}) :=
              (add_lt_add_iff_left _).2 (sbN_lt hx n _ ha.2)
          _ = x ^ (n : Ordinal.{0}) * (a / oP n + 1) := by rw [mul_add_one]
          _ ≤ x ^ (n : Ordinal.{0}) * (b / oP n) := mul_le_mul_left' (add_one_le_of_lt hq) _
          _ ≤ x ^ (n : Ordinal.{0}) * (b / oP n) + sbN n (b % oP n) x := le_self_add
      · rw [hq]
        refine (add_lt_add_iff_left _).2 (sbN_lt_mono hx n _ _ ?_ (Ordinal.mod_lt b (oP_ne n)) ha.2 hb.2)
        have ea := Ordinal.div_add_mod a (oP n)
        have eb := Ordinal.div_add_mod b (oP n)
        have h2 : oP n * (a / oP n) + a % oP n < oP n * (b / oP n) + b % oP n := by rw [ea, eb]; exact hab
        rw [hq] at h2
        exact (add_lt_add_iff_left _).1 h2

theorem sbN_le_mono {x : Ordinal.{0}} (hx : 0 < x) {n : ℕ} {a b : Ordinal.{0}} (hab : a ≤ b) (hb : b < oP n)
    (ha : gtN n a < x) (hb' : gtN n b < x) : sbN n a x ≤ sbN n b x := by
  rcases hab.lt_or_eq with h | rfl
  · exact (sbN_lt_mono hx n a b h hb ha hb').le
  · exact le_rfl

/-- **The reading reflects the order.** -/
theorem lt_of_sbN_lt {x : Ordinal.{0}} (hx : 0 < x) {n : ℕ} {a b : Ordinal.{0}} (ha : a < oP n)
    (hga : gtN n a < x) (hgb : gtN n b < x) (h : sbN n a x < sbN n b x) : a < b := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.2 (sbN_le_mono hx hle ha hgb hga))

/-- **Every `ν < x^n` is the reading of a code below `oP n` with digits below `x`** (`x ≤ Ω₁`). -/
theorem sbN_surj {x : Ordinal.{0}} (hx : 0 < x) (hx1 : x ≤ Om1) : ∀ (n : ℕ) (ν : Ordinal.{0}),
    ν < x ^ (n : Ordinal.{0}) → ∃ b, b < oP n ∧ gtN n b < x ∧ sbN n b x = ν
  | 0, ν, h => by
      have h0 : ν = 0 := by simpa using h
      exact ⟨0, by rw [oP_zero]; exact zero_lt_one, hx, by rw [h0]; rfl⟩
  | n + 1, ν, h => by
      have hxn : x ^ (n : Ordinal.{0}) ≠ 0 := (opow_pos _ hx).ne'
      set q := ν / x ^ (n : Ordinal.{0}) with hq
      set r := ν % x ^ (n : Ordinal.{0}) with hr
      have hqx : q < x := by
        rw [hq, Ordinal.div_lt hxn]
        rwa [Nat.cast_succ, opow_add, opow_one] at h
      have hrl : r < x ^ (n : Ordinal.{0}) := Ordinal.mod_lt ν hxn
      obtain ⟨b, hb, hgb, hsb⟩ := sbN_surj hx hx1 n r hrl
      obtain ⟨e1, e2⟩ := dm_eq (n := n) (q := q) hb
      refine ⟨oP n * q + b, ?_, ?_, ?_⟩
      · rw [oP_succ]
        calc oP n * q + b < oP n * q + oP n := (add_lt_add_iff_left _).2 hb
          _ = oP n * (q + 1) := by rw [mul_add_one]
          _ ≤ oP n * Om1 := mul_le_mul_left' (add_one_le_of_lt (hqx.trans_le hx1)) _
      · show max ((oP n * q + b) / oP n) (gtN n ((oP n * q + b) % oP n)) < x
        rw [e1, e2]; exact max_lt hqx hgb
      · show x ^ (n : Ordinal.{0}) * ((oP n * q + b) / oP n) + sbN n ((oP n * q + b) % oP n) x = ν
        rw [e1, e2, hsb, hq, hr, Ordinal.div_add_mod]

/-- One more level changes nothing. -/
theorem sbN_stab {n : ℕ} {a : Ordinal.{0}} (ha : a < oP n) (x : Ordinal.{0}) :
    sbN (n + 1) a x = sbN n a x ∧ gtN (n + 1) a = gtN n a := by
  have e1 : a / oP n = 0 := Ordinal.div_eq_zero_of_lt ha
  have e2 : a % oP n = a := Ordinal.mod_eq_of_lt ha
  refine ⟨?_, ?_⟩
  · show x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x = sbN n a x
    rw [e1, e2, mul_zero, zero_add]
  · show max (a / oP n) (gtN n (a % oP n)) = gtN n a
    rw [e1, e2]; exact max_eq_right zero_le

theorem sbN_one (a x : Ordinal.{0}) : sbN 1 a x = a ∧ gtN 1 a = a := by
  refine ⟨?_, ?_⟩
  · show x ^ ((0 : ℕ) : Ordinal.{0}) * (a / oP 0) + sbN 0 (a % oP 0) x = a
    rw [oP_zero, Ordinal.div_one, Ordinal.mod_one]; simp [sbN]
  · show max (a / oP 0) (gtN 0 (a % oP 0)) = a
    rw [oP_zero, Ordinal.div_one]; exact max_eq_left zero_le

/-- **The successor**: `sbN n (a+1) x = sbN n a x + 1`, and the gate moves by at most one. -/
theorem sbN_succ : ∀ (n : ℕ), 1 ≤ n → ∀ (a : Ordinal.{0}), a + 1 < oP n → ∀ x : Ordinal.{0},
    sbN n (a + 1) x = sbN n a x + 1 ∧ gtN n a ≤ gtN n (a + 1) ∧ gtN n (a + 1) ≤ gtN n a + 1
  | 0, h, _, _, _ => absurd h (by norm_num)
  | n + 1, _, a, ha, x => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [(sbN_one (a + 1) x).1, (sbN_one a x).1, (sbN_one (a + 1) x).2, (sbN_one a x).2]
        exact ⟨rfl, le_self_add, le_rfl⟩
      have hal : a < oP (n + 1) := (lt_add_one a).trans ha
      set q := a / oP n with hq
      set r := a % oP n with hr
      have hrl : r < oP n := Ordinal.mod_lt a (oP_ne n)
      have hr1 : r + 1 < oP n := oP_succ_lt hn hrl
      have ea : a = oP n * q + r := (Ordinal.div_add_mod a (oP n)).symm
      have ea1 : a + 1 = oP n * q + (r + 1) := by rw [ea, add_assoc]
      obtain ⟨d1, d2⟩ := dm_eq (n := n) (q := q) hr1
      obtain ⟨ih1, ih2, ih3⟩ := sbN_succ n hn r hr1 x
      refine ⟨?_, ?_, ?_⟩
      · show x ^ (n : Ordinal.{0}) * ((a + 1) / oP n) + sbN n ((a + 1) % oP n) x =
          x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x + 1
        rw [ea1, d1, d2, ih1, ← hq, ← hr, add_assoc]
      · show max (a / oP n) (gtN n (a % oP n)) ≤ max ((a + 1) / oP n) (gtN n ((a + 1) % oP n))
        rw [ea1, d1, d2, ← hq, ← hr]
        exact max_le_max le_rfl ih2
      · show max ((a + 1) / oP n) (gtN n ((a + 1) % oP n)) ≤ max (a / oP n) (gtN n (a % oP n)) + 1
        rw [ea1, d1, d2, ← hq, ← hr]
        exact max_le ((le_max_left _ _).trans le_self_add)
          (ih3.trans (add_le_add (le_max_right _ _) le_rfl))

/-! ## The last term of a limit code -/

theorem dvd_add' {c u v : Ordinal.{0}} (hu : c ∣ u) (hv : c ∣ v) : c ∣ u + v := by
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  exact ⟨u' + v', (mul_add c u' v').symm⟩

theorem pw_eq {x : Ordinal.{0}} (hx : InE x) (n : ℕ) : x ^ (n : Ordinal.{0}) = ω ^ (x * (n : Ordinal.{0})) := by
  rw [opow_mul, show ω ^ x = x from hx]

theorem pw_dvd {x : Ordinal.{0}} (hx : InE x) {k n : ℕ} (hkn : k < n) {d : Ordinal.{0}} (hd : d < x)
    (q : Ordinal.{0}) : ω ^ (x * (k : Ordinal.{0}) + d) ∣ x ^ (n : Ordinal.{0}) * q := by
  rw [pw_eq hx]
  refine dvd_trans (opow_dvd_opow ω ?_) (dvd_mul_right _ _)
  calc x * (k : Ordinal.{0}) + d ≤ x * (k : Ordinal.{0}) + x := add_le_add le_rfl hd.le
    _ = x * ((k + 1 : ℕ) : Ordinal.{0}) := by rw [Nat.cast_succ, mul_add_one]
    _ ≤ x * (n : Ordinal.{0}) := mul_le_mul_left' (by exact_mod_cast hkn) _

/-- **The last term of a limit code**: `a = a' + (last term)`, read uniformly at every base above the gate as
`sbN n a x = sbN n a' x + ω^{x·k+d}` with `ω^{x·k+d} ∣ sbN n a' x`, `k < n`, `d` at most the gate. -/
theorem sbN_lim : ∀ (n : ℕ) (a : Ordinal.{0}), IsSuccLimit a → a < oP n →
    ∃ a' : Ordinal.{0}, ∃ k : ℕ, ∃ d : Ordinal.{0}, a' < a ∧ gtN n a' ≤ gtN n a ∧ d ≤ gtN n a ∧ k < n ∧
        (0 < k ∨ 0 < d) ∧
      ∀ x, InE x → gtN n a < x →
        sbN n a x = sbN n a' x + ω ^ (x * (k : Ordinal.{0}) + d) ∧ ω ^ (x * (k : Ordinal.{0}) + d) ∣ sbN n a' x
  | 0, a, hl, ha => by
      rw [oP_zero, Ordinal.lt_one_iff_zero] at ha
      exact absurd (ha ▸ hl).bot_lt (lt_irrefl _)
  | n + 1, a, hl, ha => by
      set q := a / oP n with hq
      set r := a % oP n with hr
      have hrl : r < oP n := Ordinal.mod_lt a (oP_ne n)
      have ea : a = oP n * q + r := (Ordinal.div_add_mod a (oP n)).symm
      have hq1 : q < Om1 := dm_lt ha
      rcases eq_or_ne r 0 with hr0 | hr0
      · -- `a = Ω₁^n · q`
        have hq0 : q ≠ 0 := by
          rintro h0
          rw [h0, hr0, mul_zero, add_zero] at ea
          exact absurd (ea ▸ hl).bot_lt (lt_irrefl _)
        obtain ⟨q', hdec, hdvd, hq'q⟩ := lg_split hq0
        obtain ⟨e1, e2⟩ := dm_eq (n := n) (q := q') (oP_ne n |> fun h => pos_iff_ne_zero.2 h)
        rw [add_zero] at e1 e2
        have hpos : 0 < n ∨ 0 < lg q := by
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · right
            have hqa : a = q := by rw [ea, hr0, add_zero, oP_zero, one_mul]
            exact Gc.gc_lg_pos (hqa ▸ hl)
          · left; exact_mod_cast hn
        refine ⟨oP n * q', n, lg q, ?_, ?_, ?_, lt_add_one n, hpos, fun x hx hgx => ?_⟩
        · rw [ea, hr0, add_zero]
          exact (mul_lt_mul_iff_right₀ (pos_iff_ne_zero.2 (oP_ne n))).2 hq'q
        · show max ((oP n * q') / oP n) (gtN n ((oP n * q') % oP n)) ≤ max (a / oP n) (gtN n (a % oP n))
          rw [e1, e2, gtN_zero_code, ← hq]
          exact max_le_max hq'q.le zero_le
        · show lg q ≤ max (a / oP n) (gtN n (a % oP n))
          exact (lg_le hq0).trans (le_max_left _ _)
        · show x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x =
              x ^ (n : Ordinal.{0}) * ((oP n * q') / oP n) + sbN n ((oP n * q') % oP n) x +
                ω ^ (x * (n : Ordinal.{0}) + lg q) ∧
            ω ^ (x * (n : Ordinal.{0}) + lg q) ∣
              x ^ (n : Ordinal.{0}) * ((oP n * q') / oP n) + sbN n ((oP n * q') % oP n) x
          rw [e1, e2, ← hq, ← hr, hr0, sbN_zero_code, add_zero, add_zero]
          refine ⟨?_, ?_⟩
          · rw [hdec, mul_add, pw_eq hx, ← opow_add, ← hdec]
          · rw [pw_eq hx, opow_add]
            obtain ⟨m, hm⟩ := hdvd
            rw [hm, ← mul_assoc]
            exact dvd_mul_right _ _
      · -- `a = Ω₁^n · q + r` with a limit `r ≠ 0`
        have hrlim : IsSuccLimit r := by
          rcases zero_or_succ_or_isSuccLimit r with h | ⟨s, hs⟩ | h
          · exact absurd h hr0
          · exfalso
            have hs' : r = s + 1 := by rw [← succ_eq_add_one]; first | exact hs | exact hs.symm
            have e3 : succ (oP n * q + s) = a := by rw [succ_eq_add_one, ea, hs', add_assoc]
            exact hl.isSuccPrelimit.succ_ne _ e3
          · exact h
        obtain ⟨r', k, d, hr'r, hg', hd, hk, hpos, hR⟩ := sbN_lim n r hrlim hrl
        have hr'l : r' < oP n := hr'r.trans hrl
        obtain ⟨e1, e2⟩ := dm_eq (n := n) (q := q) hr'l
        refine ⟨oP n * q + r', k, d, ?_, ?_, ?_, hk.trans (lt_add_one n), hpos, fun x hx hgx => ?_⟩
        · rw [ea]; exact (add_lt_add_iff_left _).2 hr'r
        · show max ((oP n * q + r') / oP n) (gtN n ((oP n * q + r') % oP n)) ≤
            max (a / oP n) (gtN n (a % oP n))
          rw [e1, e2, ← hq, ← hr]
          exact max_le_max le_rfl hg'
        · show d ≤ max (a / oP n) (gtN n (a % oP n))
          exact hd.trans (le_max_right _ _)
        · have hgx' : gtN n r < x := (le_max_right _ _).trans_lt hgx
          have hdx : d < x := hd.trans_lt hgx'
          obtain ⟨h1, h2⟩ := hR x hx hgx'
          show x ^ (n : Ordinal.{0}) * (a / oP n) + sbN n (a % oP n) x =
              x ^ (n : Ordinal.{0}) * ((oP n * q + r') / oP n) + sbN n ((oP n * q + r') % oP n) x +
                ω ^ (x * (k : Ordinal.{0}) + d) ∧
            ω ^ (x * (k : Ordinal.{0}) + d) ∣
              x ^ (n : Ordinal.{0}) * ((oP n * q + r') / oP n) + sbN n ((oP n * q + r') % oP n) x
          rw [e1, e2, ← hq, ← hr, h1, add_assoc]
          exact ⟨rfl, dvd_add' (pw_dvd hx hk hdx q) h2⟩

/-! ## Lemma EXACT -/

theorem ev_x {r : Ordinal.{0}} (hr : InE r) : OT.ev (OT.xw (OT.k 0)) r = r := by
  simp only [OT.ev_xw, OT.ev_k, add_zero]; exact hr

/-- The term `ω^{x·(m+1) + g}`. -/
def pwT (m : ℕ) (g : Ordinal.{0}) : OT := OT.xw (OT.add (OT.nmul (OT.xw (OT.k 0)) m) (OT.k g))

theorem pwT_ev {r : Ordinal.{0}} (hr : InE r) (m : ℕ) (g : Ordinal.{0}) :
    OT.ev (pwT m g) r = ω ^ (r * ((m + 1 : ℕ) : Ordinal.{0}) + g) := by
  unfold pwT
  simp only [OT.ev_xw, OT.ev_add, OT.ev_k, OT.ev_nmul, ev_x hr]
  congr 1
  rw [← add_assoc]
  congr 1
  have e : (1 : Ordinal.{0}) + (m : Ordinal.{0}) = ((m + 1 : ℕ) : Ordinal.{0}) := by
    rw [show ((m + 1 : ℕ) : Ordinal.{0}) = ((1 + m : ℕ) : Ordinal.{0}) by rw [Nat.add_comm]]; push_cast; rfl
  rw [← e, mul_add, mul_one]

theorem pwT_CB {s : Ordinal.{0}} (hs : 0 < s) (m : ℕ) {g : Ordinal.{0}} (hg : g < s) : OT.CB (pwT m g) s :=
  ⟨OT.CB_nmul hs (show OT.CB (OT.xw (OT.k 0)) s from hs) m, hg⟩

/-- **`π_{σ,ρ}(ρ^n · q) = σ^n · q`** for `q < σ`. -/
theorem pi_pw_mul {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (n : ℕ) :
    ∀ q, q < σ → ρ ^ (n : Ordinal.{0}) * q ∈ TB ρ σ ∧ pi σ ρ (ρ ^ (n : Ordinal.{0}) * q) = σ ^
        (n : Ordinal.{0}) * q := by
  have hσE := hB.1
  have hρE := hB.2.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro q hq
    simp only [Nat.cast_zero, opow_zero, one_mul]
    exact ⟨mem_TB_of_lt hB hq, pi_lt hB hq⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases eq_or_ne q 0 with rfl | hq0
  · simp only [mul_zero]
    exact ⟨mem_TB_of_lt hB hσE.pos, pi_lt hB hσE.pos⟩
  set g := log ω q with hg
  set c := q / ω ^ g with hc
  set q' := q % ω ^ g with hq'
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * c + q' = q := Ordinal.div_add_mod q (ω ^ g)
  have hq'lt : q' < ω ^ g := Ordinal.mod_lt q hω0
  have hgle : ω ^ g ≤ q := opow_log_le_self ω hq0
  have hcω : c < ω := div_opow_log_lt q one_lt_omega0
  obtain ⟨j, hj⟩ := lt_omega0.1 hcω
  have hgs : g < σ := lt_of_le_of_lt (log_le_self ω q) hq
  obtain ⟨hPT, hPpi⟩ := pi_ev hB (pwT m g) (pwT_CB hσE.pos m hgs)
  rw [pwT_ev hρE] at hPT
  rw [pwT_ev hρE, pwT_ev hσE] at hPpi
  obtain ⟨hPjT, hPjpi⟩ := pi_mul_nat hB hPT hPpi j
  obtain ⟨hq'T, hq'pi⟩ := IH q' (hq'lt.trans_le hgle) ((hq'lt.trans_le hgle).trans hq)
  have hdecomp : ∀ t : Ordinal.{0}, InE t → t ^ ((m + 1 : ℕ) : Ordinal.{0}) * q =
      ω ^ (t * ((m + 1 : ℕ) : Ordinal.{0}) + g) * (j : Ordinal.{0}) + t ^ ((m + 1 : ℕ) : Ordinal.{0}) * q' := by
    intro t ht
    conv_lhs => rw [← hdm, hj, mul_add, ← mul_assoc]
    rw [pw_eq ht, ← opow_add]
  rw [hdecomp ρ hρE, hdecomp σ hσE]
  obtain ⟨h1, h2⟩ := pi_add hB hPjT hq'T
  exact ⟨h1, by rw [h2, hPjpi, hq'pi]⟩

/-- **Lemma EXACT for the reading**: `π_{σ,ρ}(sbN n a ρ) = sbN n a σ` when every digit is below `σ`. -/
theorem sbN_pi {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : ∀ (n : ℕ) (a : Ordinal.{0}), gtN n a < σ →
    sbN n a ρ ∈ TB ρ σ ∧ pi σ ρ (sbN n a ρ) = sbN n a σ
  | 0, _, _ => ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | n + 1, a, h => by
      simp only [gtN, max_lt_iff] at h
      obtain ⟨h1, h2⟩ := pi_pw_mul hB n (a / oP n) h.1
      obtain ⟨h3, h4⟩ := sbN_pi hB n (a % oP n) h.2
      obtain ⟨h5, h6⟩ := pi_add hB h1 h3
      exact ⟨h5, by show pi σ ρ (_ + _) = _ + _; rw [h6, h2, h4]⟩

/-! ## Level-free codes -/

/-- **The codes**: `Ω₁^ω`. -/
noncomputable def geW : Ordinal.{0} := Om1 ^ ω

theorem lt_W_iff {a : Ordinal.{0}} : a < geW ↔ ∃ n : ℕ, a < oP n := by
  unfold geW oP
  rw [lt_opow_of_isSuccLimit Om1_ne isSuccLimit_omega0]
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨n, rfl⟩ := lt_omega0.1 hc
    exact ⟨n, h⟩
  · rintro ⟨n, h⟩
    exact ⟨n, natCast_lt_omega0 n, h⟩

open Classical in
/-- The least level of a code. -/
noncomputable def deg (a : Ordinal.{0}) : ℕ := if h : ∃ n : ℕ, a < oP n then Nat.find h else 0

/-- **The reading of a code** at the base `x`. -/
noncomputable def sbc (a x : Ordinal.{0}) : Ordinal.{0} := sbN (deg a) a x

/-- **The gate of a code**: its largest digit. -/
noncomputable def gate (a : Ordinal.{0}) : Ordinal.{0} := gtN (deg a) a

theorem sbN_lift {a : Ordinal.{0}} {m : ℕ} (ha : a < oP m) (x : Ordinal.{0}) :
    ∀ j : ℕ, sbN (m + j) a x = sbN m a x ∧ gtN (m + j) a = gtN m a
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
      have hl : a < oP (m + j) := ha.trans_le (oP_mono (Nat.le_add_right m j))
      obtain ⟨e1, e2⟩ := sbN_stab hl x
      obtain ⟨f1, f2⟩ := sbN_lift ha x j
      exact ⟨by rw [← add_assoc, e1, f1], by rw [← add_assoc, e2, f2]⟩

theorem deg_spec {a : Ordinal.{0}} {n : ℕ} (ha : a < oP n) : a < oP (deg a) ∧ deg a ≤ n := by
  classical
  have h : ∃ n : ℕ, a < oP n := ⟨n, ha⟩
  unfold deg
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, Nat.find_min' h ha⟩

theorem sbc_eq {a : Ordinal.{0}} {n : ℕ} (ha : a < oP n) (x : Ordinal.{0}) :
    sbc a x = sbN n a x ∧ gate a = gtN n a := by
  obtain ⟨h1, h2⟩ := deg_spec ha
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨e1, e2⟩ := sbN_lift h1 x j
  unfold sbc gate
  rw [hj, e1, e2]
  exact ⟨rfl, rfl⟩

theorem gate_zero : gate 0 = 0 := by
  have h : (0 : Ordinal.{0}) < oP 0 := by rw [oP_zero]; exact zero_lt_one
  rw [(sbc_eq h 0).2]; exact gtN_zero_code 0

theorem sb_zero (x : Ordinal.{0}) : sbc 0 x = 0 := by
  have h : (0 : Ordinal.{0}) < oP 0 := by rw [oP_zero]; exact zero_lt_one
  rw [(sbc_eq h x).1]; exact sbN_zero_code 0 x

theorem pw_lt_eN {x : Ordinal.{0}} (hx : InE x) (n : ℕ) : x ^ (n : Ordinal.{0}) < eN x := by
  rw [pw_eq hx]
  have hE := eN_E x
  have hxn : x * (n : Ordinal.{0}) < eN x :=
    hE.mul_lt (lt_eN x) ((natCast_lt_omega0 n).trans (omega0_lt_inE hE))
  have := (opow_lt_opow_iff_right one_lt_omega0).2 hxn
  rwa [show ω ^ eN x = eN x from hE] at this

/-- **The reading of a code lies below `ε_{x+1}`.** -/
theorem sb_lt_eN {a x : Ordinal.{0}} (ha : a < geW) (hx : InE x) (hg : gate a < x) : sbc a x < eN x := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  obtain ⟨e1, e2⟩ := sbc_eq hn x
  rw [e1]; rw [e2] at hg
  exact (sbN_lt hx.pos n a hg).trans (pw_lt_eN hx n)

/-- **The reading is strictly increasing.** -/
theorem sb_lt_mono {a b x : Ordinal.{0}} (ha : a < geW) (hx : InE x) (hb : b < a) (hga : gate a < x)
    (hgb : gate b < x) : sbc b x < sbc a x := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  obtain ⟨e1, e2⟩ := sbc_eq hn x
  obtain ⟨f1, f2⟩ := sbc_eq (hb.trans hn) x
  rw [e1, f1]; rw [e2] at hga; rw [f2] at hgb
  exact sbN_lt_mono hx.pos n b a hb hn hgb hga

/-- **Every ordinal below the reading of `a` is the reading of a code below `a`** with digits below `x`. -/
theorem sb_surj {a x : Ordinal.{0}} (ha : a < geW) (hx : InE x) (hx1 : x < Om1) (hg : gate a < x) {ν : Ordinal.{0}}
    (hν : ν < sbc a x) : ∃ b, b < a ∧ gate b < x ∧ sbc b x = ν := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  obtain ⟨e1, e2⟩ := sbc_eq hn x
  rw [e1] at hν; rw [e2] at hg
  obtain ⟨b, hb, hgb, hsb⟩ := sbN_surj hx.pos hx1.le n ν (hν.trans (sbN_lt hx.pos n a hg))
  obtain ⟨f1, f2⟩ := sbc_eq hb x
  have hba : b < a := lt_of_sbN_lt hx.pos hb hgb hg (by rw [hsb]; exact hν)
  exact ⟨b, hba, by rw [f2]; exact hgb, by rw [f1]; exact hsb⟩

/-- **Lemma EXACT for the reading of a code.** -/
theorem sb_pi {σ ρ a : Ordinal.{0}} (hB : Bases σ ρ) (ha : a < geW) (hg : gate a < σ) :
    sbc a ρ ∈ TB ρ σ ∧ pi σ ρ (sbc a ρ) = sbc a σ := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  rw [(sbc_eq hn ρ).1, (sbc_eq hn σ).1]
  rw [(sbc_eq hn σ).2] at hg
  exact sbN_pi hB n a hg

/-- **The successor code.** -/
theorem sb_succ {a : Ordinal.{0}} (ha : a + 1 < geW) (x : Ordinal.{0}) :
    sbc (a + 1) x = sbc a x + 1 ∧ gate a ≤ gate (a + 1) ∧ gate (a + 1) ≤ gate a + 1 := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [oP_zero] at hn
      exact absurd hn (not_lt.2 (le_add_self))
    · exact h
  have hn' : a < oP n := (lt_add_one a).trans hn
  rw [(sbc_eq hn x).1, (sbc_eq hn' x).1, (sbc_eq hn x).2, (sbc_eq hn' x).2]
  exact sbN_succ n hn1 a hn x

/-- **The last term of a limit code**, level-free. -/
theorem sb_lim {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < geW) :
    ∃ a' : Ordinal.{0}, ∃ k : ℕ, ∃ d : Ordinal.{0}, a' < a ∧ gate a' ≤ gate a ∧ d ≤ gate a ∧ (0 < k ∨ 0 < d) ∧
      ∀ x, InE x → gate a < x →
        sbc a x = sbc a' x + ω ^ (x * (k : Ordinal.{0}) + d) ∧ ω ^ (x * (k : Ordinal.{0}) + d) ∣ sbc a' x := by
  obtain ⟨n, hn⟩ := lt_W_iff.1 ha
  obtain ⟨a', k, d, h1, h2, h3, -, h5, h6⟩ := sbN_lim n a hl hn
  have hn' : a' < oP n := h1.trans hn
  refine ⟨a', k, d, h1, ?_, ?_, h5, fun x hx hgx => ?_⟩
  · rw [(sbc_eq hn 0).2, (sbc_eq hn' 0).2]; exact h2
  · rw [(sbc_eq hn 0).2]; exact h3
  · rw [(sbc_eq hn 0).2] at hgx
    rw [(sbc_eq hn x).1, (sbc_eq hn' x).1]
    exact h6 x hx hgx

/-- **`logend(u + ω^e) = e`** for `ω^e ∣ u`. -/
theorem lg_add_opow {u e : Ordinal.{0}} (h : ω ^ e ∣ u) : lg (u + ω ^ e) = e := by
  have hne : u + ω ^ e ≠ 0 := (lt_of_lt_of_le (opow_pos e omega0_pos) le_add_self).ne'
  refine le_antisymm ?_ ((le_lg_iff hne e).2 (dvd_add' h (dvd_refl _)))
  by_contra hlt
  push Not at hlt
  have hd : ω ^ (e + 1) ∣ u + ω ^ e := (le_lg_iff hne _).1 (add_one_le_of_lt hlt)
  obtain ⟨m, rfl⟩ := h
  obtain ⟨c, hc⟩ := hd
  have hpos : ω ^ e ≠ 0 := (opow_pos e omega0_pos).ne'
  rw [opow_add, opow_one, mul_assoc, ← mul_add_one] at hc
  have hc' : m + 1 = ω * c := mul_left_cancel₀ hpos hc
  have hlim : IsSuccPrelimit (m + 1) := by
    rw [hc']; exact isSuccPrelimit_iff_omega0_dvd.2 (dvd_mul_right _ _)
  exact hlim.succ_ne m (succ_eq_add_one m)

/-- **A limit code reads a limit `≥ ω`**, with `logend = x·k + d`. -/
theorem sb_lim_facts {a : Ordinal.{0}} (hl : IsSuccLimit a) (ha : a < geW) :
    ∃ a' : Ordinal.{0}, ∃ k : ℕ, ∃ d : Ordinal.{0}, a' < a ∧ gate a' ≤ gate a ∧ d ≤ gate a ∧
      ∀ x, InE x → gate a < x →
        sbc a x = sbc a' x + ω ^ lg (sbc a x) ∧ ω ^ lg (sbc a x) ∣ sbc a' x ∧ lg (sbc a x) = x * (k : Ordinal.{0}) + d ∧
          ω ≤ sbc a x ∧ 1 + sbc a x = sbc a x ∧ IsSuccLimit (sbc a x) := by
  obtain ⟨a', k, d, h1, h2, h3, h5, h6⟩ := sb_lim hl ha
  refine ⟨a', k, d, h1, h2, h3, fun x hx hgx => ?_⟩
  obtain ⟨e1, e2⟩ := h6 x hx hgx
  have hlg : lg (sbc a x) = x * (k : Ordinal.{0}) + d := by rw [e1]; exact lg_add_opow e2
  have hpos : 0 < x * (k : Ordinal.{0}) + d := by
    rcases h5 with hk | hd
    · exact lt_of_lt_of_le (mul_pos hx.pos (by exact_mod_cast hk)) le_self_add
    · exact lt_of_lt_of_le hd le_add_self
  have hω : ω ≤ sbc a x := by
    rw [e1]
    refine le_trans ?_ le_add_self
    calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ (x * (k : Ordinal.{0}) + d) :=
        opow_le_opow_right omega0_pos (one_le_iff_pos.2 hpos)
  have hdvdω : ω ∣ sbc a x := by
    rw [e1]
    have h1' : ω ∣ ω ^ (x * (k : Ordinal.{0}) + d) := by
      calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ∣ ω ^ (x * (k : Ordinal.{0}) + d) := opow_dvd_opow ω (one_le_iff_pos.2 hpos)
    exact dvd_add' (dvd_trans h1' e2) h1'
  have hne : sbc a x ≠ 0 := (lt_of_lt_of_le omega0_pos hω).ne'
  refine ⟨?_, ?_, hlg, hω, one_add_of_omega0_le hω, ?_⟩
  · rw [hlg]; exact e1
  · rw [hlg]; exact e2
  · exact ⟨not_isMin_iff_ne_bot.2 hne, isSuccPrelimit_iff_omega0_dvd.2 hdvdω⟩

end Googology.Trans.PoR.InaccPsi.R2.Ge
