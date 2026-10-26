import Googology.Trans.PoR.InaccPsi.R2.UzL1

/-!
# The largest fixed point of `φ(a, ·)`, the index of a non-fixed value, and the parts `W·a + c`

`K = Ul.UlK S i q` (`q` strongly critical).  For a normal function `f` whose fixed points are limits, the `c`-th
ordinal that is not a fixed point of `f` is `y = p + 1 + (c − p)` with `p` the largest fixed point `≤ c` (and `y = c`
if there is none); the fixed points in `(p, y]` are none.

* `uz_veb_fc` (**(FC) for `φ(a, ·)`**: the largest fixed point `p ≤ y` of `φ(a, ·)` is in `K` when `y` is; by
  well-founded induction on `y` along its Cantor and Veblen parts, no hypothesis on `a`);
* `uz_idx_K` (**`c ∈ K ↔ p + 1 + (c − p) ∈ K`** for `p ∈ K`, `p ≤ c`), `uz_idx_veb` (the same for the largest fixed
  point `p` of `φ(a, ·)`, from `uz_veb_fc`), `uz_idx_H` (the same for a lifted level `Hˡ_γ`, from (FC) `Uw.uw_fc_max`);
* `uz_parts` (**`W·a + c ∈ K ↔ a ∈ K ∧ c ∈ K`** for `W = Ω_{k+1}`, `c < W`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul
  Googology.Trans.PoR.InaccPsi.R2.Uo Googology.Trans.PoR.InaccPsi.R2.Us
  Googology.Trans.PoR.InaccPsi.R2.Uw

variable {S : InaccSeq.{0}} {s : Ordinal.{0}}

/-- **(FC) for `φ(a, ·)`**: for `y ∈ K_q` and a fixed point `p ≤ y` of `φ(a, ·)` above every fixed point `≤ y`:
`p ∈ K_q`. -/
theorem uz_veb_fc {i q a : Ordinal.{0}} (hq : SC q) :
    ∀ y, UlK S i q y → ∀ p, veblen a p = p → p ≤ y → (∀ p', veblen a p' = p' → p' ≤ y → p' ≤ p) →
      UlK S i q p := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy p hp hpy hmax
  by_cases hfy : veblen a y = y
  · rw [le_antisymm hpy (hmax y hfy le_rfl)]; exact hy
  have hpe : ω ^ p = p := by
    have := veblen_eq_self_of_le (zero_le : (0 : Ordinal.{0}) ≤ a) hp; rwa [veblen_zero_apply] at this
  have hp0 : p ≠ 0 := fun h => by rw [h] at hp; exact veblen_pos.ne' hp
  have hy0 : y ≠ 0 := fun h => hp0 (le_antisymm (h ▸ hpy) zero_le)
  have hpy' : p < y := lt_of_le_of_ne hpy fun h => hfy (h ▸ hp)
  have hpl : p ≤ lead y := by
    have h1 : ω ^ p ≤ y := by rw [hpe]; exact hpy
    have := opow_le_lead h1; rwa [hpe] at this
  by_cases ht : tail y = 0
  · have hlz : lead y = y := by have := lead_add_tail hy0; rwa [ht, add_zero] at this
    have hbK : UlK S i q (log ω y) := (ulK_dec hq y hy).2
    have hyb : ω ^ log ω y = y := hlz
    rcases (log_le_self ω y).lt_or_eq with hlt | heq
    · have hpb : p ≤ log ω y := by
        have h1 : ω ^ p ≤ ω ^ log ω y := by rw [hpe, hyb]; exact hpy
        exact (opow_le_opow_iff_right one_lt_omega0).1 h1
      exact IH _ hlt hbK p hp hpb fun p' hp' hp'b => hmax p' hp' (hp'b.trans hlt.le)
    · have hE : InE y := by
        show ω ^ y = y
        conv_lhs => rw [← heq]
        exact hyb
      by_cases hSC : SC y
      · exfalso
        have hay : y ≤ a := not_lt.1 fun h => hfy (hSC.veblen_right h)
        have hyp : y ≤ p := hay.trans ((left_le_veblen a p).trans hp.le)
        exact absurd hpy' (not_lt.2 hyp)
      · obtain ⟨hdec, ha2, hc2, -⟩ := Mx.mxDec hE (pos_iff_ne_zero.2 hy0) hSC
        have hK := uoK_veb (S := S) (s := i) (q := q) (by rw [hdec]; exact hy) (by rw [hdec]; exact ha2)
          (by rw [hdec]; exact hc2)
        rcases lt_or_ge a (invVeblen₁ y) with haa | haa
        · exfalso
          apply hfy
          conv_lhs => rw [← hdec]
          rw [veblen_veblen_of_lt haa, hdec]
        · have hp2 : veblen (invVeblen₁ y) p = p := veblen_eq_self_of_le haa hp
          have hpc : p < invVeblen₂ y := by
            have h1 : veblen (invVeblen₁ y) p < veblen (invVeblen₁ y) (invVeblen₂ y) := by
              rw [hp2, hdec]; exact hpy'
            exact veblen_lt_veblen_iff_right.1 h1
          exact IH _ hc2 hK.2 p hp hpc.le fun p' hp' hp'c => hmax p' hp' (hp'c.trans hc2.le)
  · have hlz : lead y < y := by
      have e1 := lead_add_tail hy0
      conv_rhs => rw [← e1]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ht)
    have hlK := (uoK_lead_tail hq hy hy0).1
    exact IH _ hlz hlK p hp hpl fun p' hp' hp'l => hmax p' hp' (hp'l.trans hlz.le)

/-- **The index of a non-fixed value**: for `p ∈ K_q`, `p ≤ c`: `c ∈ K_q ↔ p + 1 + (c − p) ∈ K_q`. -/
theorem uz_idx_K {i q p c : Ordinal.{0}} (hq : SC q) (hp : UlK S i q p) (hpc : p ≤ c) :
    UlK S i q c ↔ UlK S i q (p + 1 + (c - p)) := by
  constructor
  · intro hc; exact UlK.add (UlK.add hp UlK.one) ((ulK_dec hq c hc).1 p hp hpc)
  · intro hy
    have h1 : UlK S i q (p + 1) := UlK.add hp UlK.one
    have hd := (ulK_dec hq _ hy).1 _ h1 le_self_add
    rw [Ordinal.add_sub_cancel] at hd
    have := UlK.add hp hd; rwa [Ordinal.add_sub_cancel_of_le hpc] at this

theorem uz_le_idx (p c : Ordinal.{0}) (hpc : p ≤ c) : c ≤ p + 1 + (c - p) := by
  conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hpc]
  rw [add_assoc]; exact add_le_add_right (le_add_self : c - p ≤ 1 + (c - p)) p

/-- **The index for `φ(a, ·)`**: for the largest fixed point `p` of `φ(a, ·)` at or below `y = p + 1 + (c − p)`, with
`p ≤ c`: `c ∈ K_q ↔ y ∈ K_q`. -/
theorem uz_idx_veb {i q a p c : Ordinal.{0}} (hq : SC q) (hp : veblen a p = p) (hpc : p ≤ c)
    (hmax : ∀ p', veblen a p' = p' → p' ≤ p + 1 + (c - p) → p' ≤ p) :
    UlK S i q c ↔ UlK S i q (p + 1 + (c - p)) := by
  have hcy := uz_le_idx p c hpc
  constructor
  · intro hc
    exact (uz_idx_K hq (uz_veb_fc hq c hc p hp hpc fun p' hp' h => hmax p' hp' (h.trans hcy)) hpc).1 hc
  · intro hy
    exact (uz_idx_K hq (uz_veb_fc hq _ hy p hp (hpc.trans hcy) hmax) hpc).2 hy

/-- **The index for a lifted level** (`i < s`, `q` strongly critical, `q ≤ Ω_{i+1}`, `γ < V`): for the largest fixed
point `p` of `Hˡ_γ` at or below `y = p + 1 + (c − p) < W`, with `p ≤ c`: `c ∈ K^{(i)}_q ↔ y ∈ K^{(i)}_q`. -/
theorem uz_idx_H (hs : s < ω) {i q γ p c : Ordinal.{0}} (his : i < s) (hq : SC q) (hqL : q ≤ Om (i + 1))
    (hγV : γ < Om (s + 1 + 1)) (hp : ulH S s γ p = p) (hpc : p ≤ c)
    (hmax : ∀ p', ulH S s γ p' = p' → p' ≤ p + 1 + (c - p) → p' ≤ p) (hyW : p + 1 + (c - p) < Om (s + 1)) :
    UlK S i q c ↔ UlK S i q (p + 1 + (c - p)) := by
  have hcy := uz_le_idx p c hpc
  constructor
  · intro hc
    exact (uz_idx_K hq (uw_fc_max hs his hq hqL hγV hc (hcy.trans_lt hyW) hp hpc
      fun p' hp' h => hmax p' hp' (h.trans hcy)) hpc).1 hc
  · intro hy
    exact (uz_idx_K hq (uw_fc_max hs his hq hqL hγV hy hyW hp (hpc.trans hcy) hmax) hpc).2 hy

/-- **The parts of `W·a + c`** (`W = Ω_{k+1}`, `k` finite, `c < W`): `W·a + c ∈ K_q ↔ a ∈ K_q ∧ c ∈ K_q`. -/
theorem uz_parts {i q k a c : Ordinal.{0}} (hk : k < ω) (hq : SC q) (hc : c < Om (k + 1)) :
    UlK S i q (Om (k + 1) * a + c) ↔ UlK S i q a ∧ UlK S i q c := by
  have hW0 : (Om (k + 1) : Ordinal.{0}) ≠ 0 := (Ui.ui_SC_W k).1.ne'
  have hWK : UlK S i q (Om (k + 1)) := us_K_Om hk
  constructor
  · intro h
    have hd := ulK_div hq _ h _ hWK
    have hm := ulK_mod hq _ h (Om (k + 1))
    rw [Ui.ui_W_opow k] at hd hm
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hc, add_zero] at hd
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc] at hm
    exact ⟨hd, hm⟩
  · rintro ⟨ha, hc'⟩
    have := us_K_Wmul (s := k) hk hq UlK.one ha
    rw [opow_one] at this
    exact UlK.add this hc'

end Googology.Trans.PoR.InaccPsi.R2.Uz
