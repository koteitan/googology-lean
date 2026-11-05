import Googology.Trans.PoR.InaccPsi.R2.ZmSu

/-!
# ZmCo: THE GENERIC STEP — COFINALITY

* `ZmDS.sR_eqZ`, `ZmDS.sG_leZ` (the reading and the gate of `E^k·d + r` for every `k`, `d < E`, `r < E^k`);
* `ZmDS.sR_cof` (**below the reading of a limit code `o` every ordinal is below the reading of a smaller code
  with gate below `x`**: the rest, the digit (`M.cof`), the last block `V^{R(k)}` through `M.top` at a successor
  exponent and through the exponent at a limit exponent).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Yw Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Ge
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Zg Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Xk

namespace ZmDS

variable (M : ZmDS)

theorem R_one (x : Ordinal.{0}) : M.R 1 x = 1 := by
  have := M.succ 0 x; rwa [zero_add, M.R0, zero_add] at this

/-- **The reading of `E^k·d + r`** for every `k`, `d < E`, `r < E^k`. -/
theorem sR_eqZ {k d r : Ordinal.{0}} (hdE : d < M.E) (hr : r < M.E ^ k) (hv : M.E ^ k * d + r < eN M.E)
    (x : Ordinal.{0}) : M.sR (M.E ^ k * d + r) x = M.V x ^ M.sR k x * M.R d x + M.sR r x := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [mul_zero, zero_add, M.R0, mul_zero, zero_add]
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [opow_zero] at hr
    rw [Order.lt_one_iff.1 hr, opow_zero, one_mul, add_zero, M.sR_zero, opow_zero, one_mul, add_zero,
      M.sR_lt hdE]
  · exact M.sR_eq (pos_iff_ne_zero.2 hk0) hd0 hdE hr hv x

theorem sG_leZ {k d r : Ordinal.{0}} (hdE : d < M.E) (hr : r < M.E ^ k) (hv : M.E ^ k * d + r < eN M.E) :
    M.sG (M.E ^ k * d + r) ≤ max (M.sG k) (max (M.G d) (M.sG r)) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [mul_zero, zero_add]; exact (le_max_right _ _).trans (le_max_right _ _)
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [opow_zero] at hr
    rw [Order.lt_one_iff.1 hr, opow_zero, one_mul, add_zero, M.sG_lt hdE]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (M.sG_eq (pos_iff_ne_zero.2 hk0) hd0 hdE hr hv).le

/-- **COFINALITY**: below the reading of a limit code every ordinal is below the reading of a smaller code. -/
theorem sR_cof : ∀ o x, InE x → x < Om1 → IsSuccLimit o → o < eN M.E → M.sG o < x →
    ∀ ν, ν < M.sR o x → ∃ b, b < o ∧ M.sG b < x ∧ ν ≤ M.sR b x := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o IH =>
  intro x hx hx1 hl hoN hg ν hν
  have hxl : IsSuccLimit x := ev_isSuccLimit_of_inE hx
  rcases lt_or_ge o M.E with hoE | hoE
  · rw [M.sG_lt hoE] at hg
    rw [M.sR_lt hoE] at hν
    obtain ⟨b, hb, hgb, hνb⟩ := M.cof o x hx hx1 hl hoE hg ν hν
    have hbE := hb.trans hoE
    exact ⟨b, hb, by rw [M.sG_lt hbE]; exact hgb, by rw [M.sR_lt hbE]; exact hνb⟩
  obtain ⟨hk0, hd0, hdE, hrk, hdec⟩ := zm_dec M.E_E hoE
  obtain ⟨hko, hro⟩ := M.parts_lt hoE hoN
  obtain ⟨g1, g2, g3⟩ := M.gates hoE hoN hg
  rw [M.sR_cnf hoE hoN x] at hν
  set k := log M.E o
  set d := o / M.E ^ k
  set r := o % M.E ^ k
  have hEg : M.Eg < x := (M.sG_Eg _ hk0.ne').trans_lt g1
  obtain ⟨-, hVE, hV0, -⟩ := M.V_facts hx hx1 hEg
  have hVl : IsSuccLimit (M.V x) := ev_isSuccLimit_of_inE hVE
  -- the candidate codes `E^k·d' + y` below `o`
  have hcand : ∀ d' y, d' < M.E → y < M.E ^ k → M.E ^ k * d' + y < o → M.G d' < x → M.sG y < x →
      M.sR (M.E ^ k * d' + y) x = M.V x ^ M.sR k x * M.R d' x + M.sR y x ∧
        M.sG (M.E ^ k * d' + y) < x := fun d' y hd'E hy hlt hgd hgy => by
    have hvN := hlt.trans hoN
    exact ⟨M.sR_eqZ hd'E hy hvN x, (M.sG_leZ hd'E hy hvN).trans_lt (max_lt g1 (max_lt hgd hgy))⟩
  have hEk0 : (0 : Ordinal.{0}) < M.E ^ k := opow_pos _ M.E_E.pos
  rcases zero_or_succ_or_isSuccLimit r with hr0 | ⟨s, hs⟩ | hrl
  · -- `o = E^k·d`
    rw [hr0, M.sR_zero, add_zero] at hν
    have hoeq : o = M.E ^ k * d := by rw [← hdec, hr0, add_zero]
    rcases zero_or_succ_or_isSuccLimit d with hd00 | ⟨d₀, hd₀⟩ | hdl
    · exact absurd hd00 hd0.ne'
    · -- a successor digit
      rw [succ_eq_add_one] at hd₀
      have hd₀E : d₀ < M.E := (lt_add_one d₀).trans (hd₀ ▸ hdE)
      have hgd₀ : M.G d₀ < x := (M.g_le d₀).trans_lt (hd₀ ▸ g2)
      rw [← hd₀, M.succ, mul_add_one] at hν
      have hlt0 : ∀ y, y < M.E ^ k → M.E ^ k * d₀ + y < o := fun y hy => by
        rw [hoeq, ← hd₀]; exact zm_lt_next (lt_add_one d₀) hy
      rcases le_or_gt ν (M.V x ^ M.sR k x * M.R d₀ x) with hνD | hDν
      · obtain ⟨e1, e2⟩ := hcand d₀ 0 hd₀E hEk0 (hlt0 0 hEk0) hgd₀ (by rw [M.sG_zero]; exact hx.pos)
        refine ⟨_, hlt0 0 hEk0, e2, ?_⟩
        rw [e1, M.sR_zero, add_zero]; exact hνD
      obtain ⟨ν'', rfl⟩ := exists_add_of_le hDν.le
      have hν'' : ν'' < M.V x ^ M.sR k x := (add_lt_add_iff_left _).1 hν
      rcases zero_or_succ_or_isSuccLimit k with hk00 | ⟨k₀, hk₀⟩ | hkl
      · exact absurd hk00 hk0.ne'
      · -- a successor exponent: the block `V^{R(k₀)}·V`
        rw [succ_eq_add_one] at hk₀
        have hk₀k : k₀ < k := hk₀ ▸ lt_add_one k₀
        have hgk₀ : M.sG k₀ < x := (M.sG_le_succ k₀).trans_lt (hk₀ ▸ g1)
        rw [← hk₀, M.sR_succ, opow_add, opow_one] at hν''
        obtain ⟨u, hu, hνu⟩ := (lt_mul_iff_of_isSuccLimit hVl).1 hν''
        obtain ⟨t, htE, hgt, hut⟩ := M.top x hx hx1 hEg u hu
        have ht0 : t ≠ 0 := by
          rintro rfl
          rw [M.R0] at hut
          rw [le_zero_iff.1 hut, mul_zero] at hνu
          exact absurd hνu (not_lt.2 zero_le)
        have hy : M.E ^ k₀ * t < M.E ^ k := by
          rw [← hk₀, opow_add, opow_one]
          exact (mul_lt_mul_iff_right₀ (opow_pos _ M.E_E.pos)).2 htE
        have hyN : M.E ^ k₀ * t + 0 < eN M.E := by
          rw [add_zero]; exact hy.trans ((opow_le_opow_right M.E_E.pos le_rfl).trans_lt
            ((opow_log_le_self M.E (M.E_E.pos.trans_le hoE).ne').trans_lt hoN))
        have hgy : M.sG (M.E ^ k₀ * t) < x := by
          have h' := M.sG_leZ htE (opow_pos _ M.E_E.pos : (0 : Ordinal.{0}) < M.E ^ k₀) hyN
          rw [add_zero] at h'
          refine h'.trans_lt (max_lt hgk₀ (max_lt hgt (by rw [M.sG_zero]; exact hx.pos)))
        obtain ⟨e1, e2⟩ := hcand d₀ _ hd₀E hy (hlt0 _ hy) hgd₀ hgy
        refine ⟨_, hlt0 _ hy, e2, ?_⟩
        rw [e1]
        have hyv := M.sR_eqZ htE (opow_pos _ M.E_E.pos) hyN x
        rw [add_zero, M.sR_zero, add_zero] at hyv
        rw [hyv]
        refine (add_le_add_iff_left _).2 (hνu.le.trans (mul_le_mul_right hut _))
      · -- a limit exponent
        have hal : IsSuccLimit (M.sR k x) := M.sR_lim k x hx hx1 hkl (hko.trans hoN) g1
        obtain ⟨a', ha', hνa'⟩ := (lt_opow_of_isSuccLimit hV0.ne' hal).1 hν''
        obtain ⟨k', hk', hgk', hak'⟩ := IH k hko x hx hx1 hkl (hko.trans hoN) g1 a' ha'
        have hy : M.E ^ k' < M.E ^ k := (opow_lt_opow_iff_right (zm_E1 M.E_E)).2 hk'
        have hyN : M.E ^ k' * 1 + 0 < eN M.E := by
          rw [mul_one, add_zero]
          exact hy.trans ((opow_log_le_self M.E (M.E_E.pos.trans_le hoE).ne').trans_lt hoN)
        have hg1 : M.G 1 < x := by
          have := M.g_succ 0 x hxl hEg (by rw [M.G0]; exact hx.pos); rwa [zero_add] at this
        have hgy : M.sG (M.E ^ k') < x := by
          have h' := M.sG_leZ M.one_lt_E (opow_pos _ M.E_E.pos) hyN
          rw [mul_one, add_zero] at h'
          exact h'.trans_lt (max_lt hgk' (max_lt hg1 (by rw [M.sG_zero]; exact hx.pos)))
        obtain ⟨e1, e2⟩ := hcand d₀ _ hd₀E hy (hlt0 _ hy) hgd₀ hgy
        refine ⟨_, hlt0 _ hy, e2, ?_⟩
        rw [e1]
        have hyv := M.sR_eqZ M.one_lt_E (opow_pos _ M.E_E.pos) hyN x
        rw [mul_one, add_zero, M.R_one, mul_one, M.sR_zero, add_zero] at hyv
        rw [hyv]
        exact (add_le_add_iff_left _).2 (hνa'.le.trans (opow_le_opow_right hV0 hak'))
    · -- a limit digit
      have hRl : IsSuccLimit (M.R d x) := M.lim d x hx hx1 hdl hdE g2
      obtain ⟨u, hu, hνu⟩ := (lt_mul_iff_of_isSuccLimit hRl).1 hν
      obtain ⟨d', hd', hgd', hud'⟩ := M.cof d x hx hx1 hdl hdE g2 u hu
      have hlt : M.E ^ k * d' + 0 < o := by
        rw [add_zero, hoeq]; exact (mul_lt_mul_iff_right₀ hEk0).2 hd'
      obtain ⟨e1, e2⟩ := hcand d' 0 (hd'.trans hdE) hEk0 hlt hgd' (by rw [M.sG_zero]; exact hx.pos)
      refine ⟨_, hlt, e2, ?_⟩
      rw [e1, M.sR_zero, add_zero]
      exact hνu.le.trans (mul_le_mul_right hud' _)
  · -- a successor rest: impossible
    exfalso
    have : o = Order.succ (M.E ^ k * d + s) := by
      rw [succ_eq_add_one, add_assoc, ← succ_eq_add_one s, hs, hdec]
    rw [this] at hl
    exact Order.not_isSuccLimit_succ _ hl
  · -- a limit rest
    have hlt : ∀ y, y < r → M.E ^ k * d + y < o := fun y hy => by
      rw [← hdec]; exact (add_lt_add_iff_left _).2 hy
    rcases le_or_gt ν (M.V x ^ M.sR k x * M.R d x) with hνD | hDν
    · obtain ⟨e1, e2⟩ := hcand d 0 hdE hEk0 (hlt 0 hrl.bot_lt) g2 (by rw [M.sG_zero]; exact hx.pos)
      refine ⟨_, hlt 0 hrl.bot_lt, e2, ?_⟩
      rw [e1, M.sR_zero, add_zero]; exact hνD
    obtain ⟨ν', rfl⟩ := exists_add_of_le hDν.le
    have hν' : ν' < M.sR r x := (add_lt_add_iff_left _).1 hν
    obtain ⟨b', hb', hgb', hνb'⟩ := IH r hro x hx hx1 hrl (hro.trans hoN) g3 ν' hν'
    obtain ⟨e1, e2⟩ := hcand d b' hdE (hb'.trans hrk) (hlt b' hb') g2 hgb'
    refine ⟨_, hlt b' hb', e2, ?_⟩
    rw [e1]; exact (add_le_add_iff_left _).2 hνb'

end ZmDS

end Googology.Trans.PoR.InaccPsi.R2.Zm
