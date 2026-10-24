import Googology.Trans.PoR.InaccPsi.R2.TeExp

/-!
# The `ε`-step of an offset code system: the codes `[B, ε_{B+1})` over a system with code bound `B` and top `V`

`K : Tb.TbCS` with readings `K.R` below the code bound `K.B` and the top `K.V(x)`.  When `K.B` is an `ε`-number, a code
`c ∈ [K.B, ε_{K.B+1})` is `K.B` itself (read `V(x)`), or `K.B·n + r` (`0 < n < ω`, `r < K.B`, read `V(x)·n + r(x)`),
or `ω^e·n + r` with `K.B < e = log_ω c < c` (read `ω^{e(x)}·n + r(x)`); its gate is that of `r`, resp. the larger gate
of `e` and `r`.  The readings then fill `[V(x), ε_{V(x)+1})` (next module).

* `TeHyp K` (**the hypotheses of the step**: `K.B` is an `ε`-number lying in every hull `Cl(a, b)` with `0 < a`,
  `ε_{K.B+1} ≤ θ_{k+1}`, `ε_{V(x)+1} ∈ Tˣ ∩ Ω₁`, Lemma EXACT for `V` and for `ε_{V+1}`);
* `te_dec`, `te_parts`, `teR`, `teG` (**the reading and the gate**, one well-founded recursion), the unfolding lemmas,
  `te_mkB`, `te_mkE` (**the normal forms `K.B·n + r`, `ω^e·n + r` and their readings**), `teR_zero`, `teG_zero`,
  `teR_succ`, `teG_succ`.

No new axiom.  New definitions: `TeHyp` (a structure of facts), `teR`, `teG` (ordinal functions).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

/-- **The hypotheses of the `ε`-step** for an offset code system `K`. -/
structure TeHyp (K : Tb.TbCS) : Prop where
  BE : InE K.B
  Bmem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → K.B ∈ S.CSet a b
  Bth : ∀ (S : InaccSeq.{0}) (k : ℕ), eN K.B ≤ Lc.lcTh S (k + 1)
  VT : ∀ x, InE x → x < Om1 → eN (K.V x) ∈ Tset x ∧ eN (K.V x) < Om1
  Vpi : ∀ σ ρ, Bases σ ρ → K.V ρ ∈ TB ρ σ ∧ pi σ ρ (K.V ρ) = K.V σ
  VNpi : ∀ σ ρ, Bases σ ρ → eN (K.V ρ) ∈ TB ρ σ ∧ pi σ ρ (eN (K.V ρ)) = eN (K.V σ)

variable (K : Tb.TbCS)

/-- The recursion decreases: `log_ω c < c` and `c mod ω^{log c} < c` for `K.B < c < ε_{K.B+1}`. -/
theorem te_dec {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) :
    log ω c < c ∧ c % ω ^ log ω c < c := by
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  have hle : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
  have hp : ω ^ log ω c ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨lt_of_le_of_ne (log_le_self ω c) fun he => ?_, (Ordinal.mod_lt c hp).trans_le hle⟩
  have h3 : ω ^ c ≤ c := by
    have := hle
    rwa [he] at this
  have hcE : InE c := le_antisymm h3 (right_le_opow c one_lt_omega0)
  exact absurd h2 (not_lt.2 (eN_le h1 hcE))

/-- **The parts of a code `c ∈ (K.B, ε_{K.B+1})`.** -/
theorem te_parts (hBE : InE K.B) {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) :
    K.B ≤ log ω c ∧ log ω c < c ∧ c / ω ^ log ω c < ω ∧ 0 < c / ω ^ log ω c ∧
      c % ω ^ log ω c < ω ^ log ω c ∧ c % ω ^ log ω c < c ∧
      ω ^ log ω c * (c / ω ^ log ω c) + c % ω ^ log ω c = c := by
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le h1).ne'
  have hp : ω ^ log ω c ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hBe : ω ^ K.B = K.B := hBE
  obtain ⟨d1, d2⟩ := te_dec K h1 h2
  exact ⟨le_log_of_opow_le one_lt_omega0 (by rw [hBe]; exact h1.le), d1, div_opow_log_lt c one_lt_omega0,
    div_opow_log_pos ω hc0, Ordinal.mod_lt c hp, d2, Ordinal.div_add_mod c _⟩

/-- **The reading** of a code over `K`. -/
noncomputable def teR (c x : Ordinal.{0}) : Ordinal.{0} :=
  if _h : K.B < c ∧ c < eN K.B then
    (if log ω c = K.B then K.V x * (c / ω ^ log ω c) + K.R (c % ω ^ log ω c) x
      else ω ^ teR (log ω c) x * (c / ω ^ log ω c) + teR (c % ω ^ log ω c) x)
  else if c = K.B then K.V x else K.R c x
termination_by c
decreasing_by
  all_goals first
    | exact (te_dec K _h.1 _h.2).1
    | exact (te_dec K _h.1 _h.2).2

/-- **The gate** of a code over `K`. -/
noncomputable def teG (c : Ordinal.{0}) : Ordinal.{0} :=
  if _h : K.B < c ∧ c < eN K.B then
    (if log ω c = K.B then K.G (c % ω ^ log ω c)
      else max (teG (log ω c)) (teG (c % ω ^ log ω c)))
  else if c = K.B then 0 else K.G c
termination_by c
decreasing_by
  all_goals first
    | exact (te_dec K _h.1 _h.2).1
    | exact (te_dec K _h.1 _h.2).2

theorem teR_low {c : Ordinal.{0}} (hc : c < K.B) (x : Ordinal.{0}) : teR K c x = K.R c x := by
  rw [teR, dif_neg (fun h => absurd h.1 (not_lt.2 hc.le)), if_neg hc.ne]

theorem teG_low {c : Ordinal.{0}} (hc : c < K.B) : teG K c = K.G c := by
  rw [teG, dif_neg (fun h => absurd h.1 (not_lt.2 hc.le)), if_neg hc.ne]

theorem teR_B (x : Ordinal.{0}) : teR K K.B x = K.V x := by
  rw [teR, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

theorem teG_B : teG K K.B = 0 := by
  rw [teG, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

theorem teR_hiB {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) (he : log ω c = K.B) (x : Ordinal.{0}) :
    teR K c x = K.V x * (c / ω ^ log ω c) + K.R (c % ω ^ log ω c) x := by
  rw [teR, dif_pos ⟨h1, h2⟩, if_pos he]

theorem teG_hiB {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) (he : log ω c = K.B) :
    teG K c = K.G (c % ω ^ log ω c) := by
  rw [teG, dif_pos ⟨h1, h2⟩, if_pos he]

theorem teR_hi {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) (he : log ω c ≠ K.B) (x : Ordinal.{0}) :
    teR K c x = ω ^ teR K (log ω c) x * (c / ω ^ log ω c) + teR K (c % ω ^ log ω c) x := by
  rw [teR, dif_pos ⟨h1, h2⟩, if_neg he]

theorem teG_hi {c : Ordinal.{0}} (h1 : K.B < c) (h2 : c < eN K.B) (he : log ω c ≠ K.B) :
    teG K c = max (teG K (log ω c)) (teG K (c % ω ^ log ω c)) := by
  rw [teG, dif_pos ⟨h1, h2⟩, if_neg he]

theorem teR_zero (x : Ordinal.{0}) : teR K 0 x = 0 := by
  rw [teR_low K K.pos_B, K.zero_R]

theorem teG_zero : teG K 0 = 0 := by rw [teG_low K K.pos_B, K.zero_G]

theorem te_R_one (x : Ordinal.{0}) : K.R 1 x = 1 := by
  have h := K.succ_R 0 x K.pos_B
  rw [zero_add, K.zero_R, zero_add] at h
  exact h

/-! ## The normal forms -/

section NF

variable (hBE : InE K.B)
include hBE

/-- **The normal form `K.B·n + r`** (`0 < n < ω`, `r < K.B`): a code in `[K.B, ε_{K.B+1})` reading `V(x)·n + r(x)`,
with the gate of `r`. -/
theorem te_mkB {n r : Ordinal.{0}} (hn0 : 0 < n) (hn : n < ω) (hr : r < K.B) :
    K.B ≤ K.B * n + r ∧ K.B * n + r < eN K.B ∧
      (∀ x, teR K (K.B * n + r) x = K.V x * n + K.R r x) ∧ teG K (K.B * n + r) = K.G r := by
  have hBe : ω ^ K.B = K.B := hBE
  have hle : K.B ≤ K.B * n + r := (Ordinal.le_mul_left _ hn0).trans le_self_add
  have hlt : K.B * n + r < eN K.B := by
    calc K.B * n + r < K.B * n + K.B := (add_lt_add_iff_left _).2 hr
      _ = K.B * (n + 1) := by rw [mul_add_one]
      _ ≤ K.B * ω := mul_le_mul_right (Order.add_one_le_of_lt hn) _
      _ = ω ^ (K.B + 1) := by rw [opow_add, opow_one, hBe]
      _ < eN K.B := (eN_E K.B).opow_lt ((ev_isSuccLimit_of_inE (eN_E K.B)).add_one_lt (lt_eN _))
  refine ⟨hle, hlt, fun x => ?_, ?_⟩ <;> rcases hle.lt_or_eq with hgt | heq
  · have hl : log ω (K.B * n + r) = K.B := by
      have e0 : K.B * n + r = ω ^ K.B * n + r := by rw [hBe]
      rw [e0, log_opow_mul_add one_lt_omega0 hn0.ne' (by rw [hBe]; exact hr), log_eq_zero hn, add_zero]
    rw [teR_hiB K hgt hlt hl, hl, hBe, Ordinal.mul_add_div _ hBE.pos.ne', Ordinal.div_eq_zero_of_lt hr,
      add_zero, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  · -- the atom: `n = 1`, `r = 0`
    have hr0 : r = 0 := by
      by_contra h0
      have h3 : K.B * n < K.B := lt_of_lt_of_eq (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0)) heq.symm
      exact absurd h3 (not_lt.2 (Ordinal.le_mul_left _ hn0))
    subst hr0
    have hn1 : n = 1 := by
      rw [add_zero] at heq
      by_contra h1
      have h2 : 1 < n := lt_of_le_of_ne (Order.one_le_iff_pos.2 hn0) (Ne.symm h1)
      have : K.B * 1 < K.B * n := (mul_lt_mul_iff_right₀ hBE.pos).2 h2
      rw [mul_one, ← heq] at this
      exact lt_irrefl _ this
    subst hn1
    rw [← heq, teR_B, K.zero_R, mul_one, add_zero]
  · have hl : log ω (K.B * n + r) = K.B := by
      have e0 : K.B * n + r = ω ^ K.B * n + r := by rw [hBe]
      rw [e0, log_opow_mul_add one_lt_omega0 hn0.ne' (by rw [hBe]; exact hr), log_eq_zero hn, add_zero]
    rw [teG_hiB K hgt hlt hl, hl, hBe, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  · have hr0 : r = 0 := by
      by_contra h0
      have h3 : K.B * n < K.B := lt_of_lt_of_eq (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0)) heq.symm
      exact absurd h3 (not_lt.2 (Ordinal.le_mul_left _ hn0))
    subst hr0
    rw [← heq, teG_B, K.zero_G]

/-- **The normal form `ω^e·n + r`** (`K.B < e < ε_{K.B+1}`, `0 < n < ω`, `r < ω^e`): a code in `(K.B, ε_{K.B+1})`
reading `ω^{e(x)}·n + r(x)`, with the larger gate of `e` and `r`. -/
theorem te_mkE {e n r : Ordinal.{0}} (he : K.B < e) (heB : e < eN K.B) (hn0 : 0 < n) (hn : n < ω)
    (hr : r < ω ^ e) :
    K.B < ω ^ e * n + r ∧ ω ^ e * n + r < eN K.B ∧ log ω (ω ^ e * n + r) = e ∧
      (∀ x, teR K (ω ^ e * n + r) x = ω ^ teR K e x * n + teR K r x) ∧
      teG K (ω ^ e * n + r) = max (teG K e) (teG K r) := by
  have hBe : ω ^ K.B = K.B := hBE
  have hp : ω ^ e ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hgt : K.B < ω ^ e * n + r := by
    calc K.B = ω ^ K.B := hBe.symm
      _ < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 he
      _ ≤ ω ^ e * n := Ordinal.le_mul_left _ hn0
      _ ≤ ω ^ e * n + r := le_self_add
  have hlt : ω ^ e * n + r < eN K.B := by
    calc ω ^ e * n + r < ω ^ e * n + ω ^ e := (add_lt_add_iff_left _).2 hr
      _ = ω ^ e * (n + 1) := by rw [mul_add_one]
      _ ≤ ω ^ e * ω := mul_le_mul_right (Order.add_one_le_of_lt hn) _
      _ = ω ^ (e + 1) := by rw [opow_add, opow_one]
      _ < eN K.B := (eN_E K.B).opow_lt ((ev_isSuccLimit_of_inE (eN_E K.B)).add_one_lt heB)
  have hl : log ω (ω ^ e * n + r) = e := by
    rw [log_opow_mul_add one_lt_omega0 hn0.ne' hr, log_eq_zero hn, add_zero]
  have hne : log ω (ω ^ e * n + r) ≠ K.B := by rw [hl]; exact he.ne'
  have hd : (ω ^ e * n + r) / ω ^ e = n := by
    rw [Ordinal.mul_add_div _ hp, Ordinal.div_eq_zero_of_lt hr, add_zero]
  have hm : (ω ^ e * n + r) % ω ^ e = r := by rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  refine ⟨hgt, hlt, hl, fun x => ?_, ?_⟩
  · rw [teR_hi K hgt hlt hne, hl, hd, hm]
  · rw [teG_hi K hgt hlt hne, hl, hm]

/-! ## `+1` -/

/-- **The reading moves by `+1` along `+1`.** -/
theorem teR_succ : ∀ b x, b < eN K.B → teR K (b + 1) x = teR K b x + 1 := by
  have hBe : ω ^ K.B = K.B := hBE
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro x hb
  rcases lt_trichotomy b K.B with hbB | rfl | hbB
  · rw [teR_low K (K.B_lim.add_one_lt hbB), teR_low K hbB, K.succ_R b x hbB]
  · have h1B : (1 : Ordinal.{0}) < K.B := (one_lt_omega0).trans (omega0_lt_inE hBE)
    obtain ⟨-, -, hR, -⟩ := te_mkB K hBE one_pos one_lt_omega0 h1B
    simp only [mul_one] at hR
    rw [hR x, te_R_one, teR_B]
  · obtain ⟨heB, hec, hn, hn0, hr, hrc, hdec⟩ := te_parts K hBE hbB hb
    by_cases he : log ω b = K.B
    · have hrB : b % ω ^ log ω b < K.B := by rw [he, hBe]; rw [he, hBe] at hr; exact hr
      have hr1 : b % ω ^ log ω b + 1 < K.B := K.B_lim.add_one_lt hrB
      obtain ⟨-, -, hR, -⟩ := te_mkB K hBE hn0 hn hr1
      have e1 : K.B * (b / ω ^ log ω b) + (b % ω ^ log ω b + 1) = b + 1 := by
        rw [← add_assoc]; conv_rhs => rw [← hdec]
        rw [he, hBe]
      rw [← e1, hR x, teR_hiB K hbB hb he x, K.succ_R _ x hrB, add_assoc]
    · have heB' : K.B < log ω b := lt_of_le_of_ne heB (Ne.symm he)
      have hlim : IsSuccLimit (ω ^ log ω b) :=
        Ph.ph_opow_lim (pos_iff_ne_zero.1 (lt_of_le_of_lt zero_le heB'))
      have hr1 : b % ω ^ log ω b + 1 < ω ^ log ω b := hlim.add_one_lt hr
      obtain ⟨-, -, -, hR, -⟩ := te_mkE K hBE heB' (hec.trans hb) hn0 hn hr1
      have e1 : ω ^ log ω b * (b / ω ^ log ω b) + (b % ω ^ log ω b + 1) = b + 1 := by
        rw [← add_assoc, hdec]
      rw [← e1, hR x, teR_hi K hbB hb he x, IH _ hrc x (hrc.trans hb), add_assoc]

/-- **The gate moves along `+1`.** -/
theorem teG_succ : ∀ b Z, b < eN K.B → IsSuccLimit Z → teG K b < Z → teG K (b + 1) < Z := by
  have hBe : ω ^ K.B = K.B := hBE
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro Z hb hZ hg
  rcases lt_trichotomy b K.B with hbB | rfl | hbB
  · rw [teG_low K (K.B_lim.add_one_lt hbB)]
    rw [teG_low K hbB] at hg
    exact K.succ_G b Z hbB hZ hg
  · have h1B : (1 : Ordinal.{0}) < K.B := (one_lt_omega0).trans (omega0_lt_inE hBE)
    obtain ⟨-, -, -, hG⟩ := te_mkB K hBE one_pos one_lt_omega0 h1B
    simp only [mul_one] at hG
    rw [hG]
    have h1 := K.succ_G 0 Z K.pos_B hZ (by rw [K.zero_G]; exact hZ.bot_lt)
    rwa [zero_add] at h1
  · obtain ⟨heB, hec, hn, hn0, hr, hrc, hdec⟩ := te_parts K hBE hbB hb
    by_cases he : log ω b = K.B
    · have hrB : b % ω ^ log ω b < K.B := by rw [he, hBe]; rw [he, hBe] at hr; exact hr
      have hr1 : b % ω ^ log ω b + 1 < K.B := K.B_lim.add_one_lt hrB
      obtain ⟨-, -, -, hG⟩ := te_mkB K hBE hn0 hn hr1
      have e1 : K.B * (b / ω ^ log ω b) + (b % ω ^ log ω b + 1) = b + 1 := by
        rw [← add_assoc]; conv_rhs => rw [← hdec]
        rw [he, hBe]
      rw [teG_hiB K hbB hb he] at hg
      rw [← e1, hG]
      exact K.succ_G _ Z hrB hZ hg
    · have heB' : K.B < log ω b := lt_of_le_of_ne heB (Ne.symm he)
      have hlim : IsSuccLimit (ω ^ log ω b) :=
        Ph.ph_opow_lim (pos_iff_ne_zero.1 (lt_of_le_of_lt zero_le heB'))
      have hr1 : b % ω ^ log ω b + 1 < ω ^ log ω b := hlim.add_one_lt hr
      obtain ⟨-, -, -, -, hG⟩ := te_mkE K hBE heB' (hec.trans hb) hn0 hn hr1
      have e1 : ω ^ log ω b * (b / ω ^ log ω b) + (b % ω ^ log ω b + 1) = b + 1 := by
        rw [← add_assoc, hdec]
      rw [teG_hi K hbB hb he] at hg
      rw [← e1, hG]
      exact max_lt (lt_of_le_of_lt (le_max_left _ _) hg)
        (IH _ hrc Z (hrc.trans hb) hZ (lt_of_le_of_lt (le_max_right _ _) hg))

end NF

end Googology.Trans.PoR.InaccPsi.R2.Te
