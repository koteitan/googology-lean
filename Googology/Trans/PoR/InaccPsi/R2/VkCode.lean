import Googology.Trans.PoR.InaccPsi.R2.VhOwn
import Googology.Trans.PoR.InaccPsi.R2.UjCode

/-!
# Codes over every level `≥ k`: the strongly critical ordinals `≥ Ω_k` as atoms

`VkA k Q` (**the codes over `Q` above the level `k`**): generated from the ordinals below `Q` and **every strongly
critical `s ≥ Ω_k`** by `+` and `φ`.  So every `Ω_j` (`j ≥ k`, finite or not) and every atom `ψ_{Ω_{j+1}}(d)`
(`j ≥ k`, any argument `d`) is a code.  The level-`k` codes `Ug.UgC S k Q` are codes (`vkA_of_ugC`, `vkA_of_le`),
and they all lie below `Y₃ = ψ_{Ω₃}(Ω₃)` at `k = 2` (`vkUgC_lt_Y`: the wall of the fixed bound), while `Y₃`, `Ω₃`
and every strongly critical ordinal `≥ Ω₂` are codes here (`vkA_Y`, `vkA_Om`, `vkA_SC`).  Every lemma below is one
proof for every level.

* `VkA.mono`, `VkA.zero`, `VkA.opow`, `VkA.om`, `vkA_lt_om` (**a code below `Ω_k` is below `Q`**);
* `vkA_gen`, `vkDec` (decomposition: `w − x` and `log_ω w` are codes), `vkA_mod`, `vkA_mulOp`, `vkA_mulK`, `vkA_divOp`,
  `vkA_div`, `vkA_mulNat`;
* `vkA_arg`, `vkA_lev` (the Veblen parts of a code are codes), `vkA_cnf` (the base-`Ω₂` normal form at `k = 2`).

No new axiom.  New definition: `VkA`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- **The codes over `Q` above the level `k`**: the ordinals below `Q`, every strongly critical `s ≥ Ω_k`, `+`,
`φ`. -/
inductive VkA (k Q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Q → VkA k Q x
  | big {x : Ordinal.{0}} : Om k ≤ x → SC x → VkA k Q x
  | add {x y : Ordinal.{0}} : VkA k Q x → VkA k Q y → VkA k Q (x + y)
  | phi {x y : Ordinal.{0}} : VkA k Q x → VkA k Q y → VkA k Q (veblen x y)

variable {k Q : Ordinal.{0}}

theorem VkA.mono {Q' x : Ordinal.{0}} (h : Q ≤ Q') (hx : VkA k Q x) : VkA k Q' x := by
  induction hx with
  | small h' => exact VkA.small (h'.trans_le h)
  | big h1 h2 => exact VkA.big h1 h2
  | add _ _ ihx ihy => exact VkA.add ihx ihy
  | phi _ _ ihx ihy => exact VkA.phi ihx ihy

theorem VkA.zero (hQ : 0 < Q) : VkA k Q 0 := VkA.small hQ

theorem VkA.opow (hQ : 0 < Q) {c : Ordinal.{0}} (h : VkA k Q c) : VkA k Q (ω ^ c) := by
  have := VkA.phi (VkA.zero (k := k) hQ) h; rwa [veblen_zero_apply] at this

theorem VkA.om (hQ : 0 < Q) {j : Ordinal.{0}} (hj : k ≤ j) : VkA k Q (Om j) := by
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [Om_zero]; exact VkA.zero hQ
  exact VkA.big (Om_le_Om.2 hj) (SC_Om hj0)

/-- **Every level-`k` code with `ψ_{Ω_{k+1}}`-atoms is a code.** -/
theorem vkA_of_ugC (hQ : 0 < Q) {x : Ordinal.{0}} (hx : UgC S k Q x) : VkA k Q x := by
  induction hx with
  | small h => exact VkA.small h
  | om => exact VkA.om hQ le_rfl
  | add _ _ ihx ihy => exact VkA.add ihx ihy
  | phi _ _ ihx ihy => exact VkA.phi ihx ihy
  | @psi d _ _ _ => exact VkA.big (psiS_bounds (S := S) d k).1.le (SC_psi (InR_Om_succ k) d)

/-- **Every code without atoms is a code.** -/
theorem vkA_of_le (hQ : 0 < Q) {x : Ordinal.{0}} (h : LeCl (Om k) Q x) : VkA k Q x := by
  induction h with
  | small h' => exact VkA.small h'
  | om => exact VkA.om hQ le_rfl
  | add _ _ ihx ihy => exact VkA.add ihx ihy
  | phi _ _ ihx ihy => exact VkA.phi ihx ihy

/-- **The level-2 codes lie below `Y₃`** (for `Q ≤ Y₃`): the wall of the fixed bound. -/
theorem vkUgC_lt_Y (hQY : Q ≤ ugY S) {x : Ordinal.{0}} (hx : UgC S (1 + 1) Q x) : x < ugY S := by
  have hY : SC (ugY S) := Uj.ujY_SC (S := S) 1
  have hκ : S.InR (Om (1 + 1 + 1 : Ordinal.{0})) := InR_Om_succ (1 + 1)
  induction hx with
  | small h => exact h.trans_le hQY
  | om => exact Uj.ujY_gt (S := S) 1
  | add _ _ ihx ihy => exact hY.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact hY.2 _ ihx _ ihy
  | @psi d _ _ ihd =>
    exact psi_lt_psi_of_mem hκ (ihd.trans ugY_lt_Om3) (CSet.of_lt ihd)

/-- **`Y₃` and every strongly critical ordinal `≥ Ω₂` are codes above the level 2.** -/
theorem vkA_SC {x : Ordinal.{0}} (hk : Om k ≤ x) (hx : SC x) : VkA k Q x := VkA.big hk hx

theorem vkA_Y : VkA (1 + 1) Q (ugY S) := VkA.big (Uj.ujY_gt (S := S) 1).le (Uj.ujY_SC 1)

theorem vkA_Om (hQ : 0 < Q) (j : ℕ) : VkA (1 + 1) Q (Om ((j : Ordinal.{0}) + 1 + 1)) :=
  VkA.om hQ (by gcongr; exact le_add_self)

/-- **A code below `Ω_k` is below `Q`.** -/
theorem vkA_lt_om (hQ : SC Q) {x : Ordinal.{0}} (hx : VkA k Q x) : x < Om k → x < Q := by
  induction hx with
  | small h => exact fun _ => h
  | big h1 _ => exact fun h => absurd h (not_lt.2 h1)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hQ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1)) (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hQ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))

section Dec

variable (hQ : SC Q)

include hQ

/-- A strongly critical code `s` has `s − x ∈ {s, 0}` and `log_ω s = s`. -/
theorem vkA_gen {s : Ordinal.{0}} (hs : SC s) (hsC : VkA k Q s) :
    (∀ x, VkA k Q x → x ≤ s → VkA k Q (s - x)) ∧ VkA k Q (log ω s) := by
  have hE : ω ^ s = s := gg_SC_eps hs
  refine ⟨fun x _ hx => ?_, ?_⟩
  · rcases gg_sub_prin hs.isPrincipal hx with e | e <;> rw [e]
    · exact hsC
    · exact VkA.zero hQ.1
  · have : log ω s = s := by
      conv_lhs => rw [← hE]
      exact log_opow one_lt_omega0 _
    rw [this]; exact hsC

/-- **Decomposition**: a code `w` has `w − x` (for every code `x ≤ w`) and `log_ω w` codes. -/
theorem vkDec : ∀ w, VkA k Q w →
    (∀ x, VkA k Q x → x ≤ w → VkA k Q (w - x)) ∧ VkA k Q (log ω w) := by
  have h0 : VkA k Q 0 := VkA.zero hQ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, VkA k Q v → v ≤ w →
      (∀ x, VkA k Q x → x ≤ v → VkA k Q (v - x)) ∧ VkA k Q (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => VkA.small ((Ordinal.sub_le_self v x).trans_lt h),
      VkA.small ((log_le_self ω v).trans_lt h)⟩
  | @big v h1 h2 => intro _; exact vkA_gen hQ h2 (VkA.big h1 h2)
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact VkA.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : VkA k Q (x - u) := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact h0
    · rcases ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2
  | @phi a b ha hb iha ihb =>
    intro hle
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · exact VkA.opow hQ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact VkA.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact VkA.phi ha hb

/-- `ω^c·y` is a code for codes `c`, `y`. -/
theorem vkA_mulOp {c : Ordinal.{0}} (hc : VkA k Q c) : ∀ y, VkA k Q y → VkA k Q (ω ^ c * y) := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]; exact VkA.zero hQ.1
  obtain ⟨hsub, hlog⟩ := vkDec hQ y hy
  have hlead : ω ^ log ω y ≤ y := opow_log_le_self ω hy0
  have hdec : ω ^ log ω y + (y - ω ^ log ω y) = y := Ordinal.add_sub_cancel_of_le hlead
  have e : ω ^ c * y = ω ^ (c + log ω y) + ω ^ c * (y - ω ^ log ω y) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add]
  rw [e]
  exact VkA.add (VkA.opow hQ.1 (VkA.add hc hlog))
    (IH _ (leRest_lt hy0) (hsub _ (VkA.opow hQ.1 hlog) hlead))

/-- **`Ω_k·y` is a code** for every code `y` (`k ≠ 0`). -/
theorem vkA_mulK (hk : k ≠ 0) (y : Ordinal.{0}) (hy : VkA k Q y) : VkA k Q (Om k * y) := by
  have := vkA_mulOp hQ (VkA.om (k := k) hQ.1 le_rfl) y hy
  rwa [gg_SC_eps (SC_Om hk)] at this

/-- **Codes are closed under `x ↦ x % ω^b`.** -/
theorem vkA_mod (b : Ordinal.{0}) {x : Ordinal.{0}} (hx : VkA k Q x) : VkA k Q (x % ω ^ b) := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → VkA k Q p → VkA k Q (p % ω ^ b) := by
    intro p hp h
    rcases leMod_prin hp b with e | e
    · rw [e]; exact h
    · rw [e]; exact VkA.zero hQ.1
  induction hx with
  | small h => exact VkA.small ((Ordinal.mod_le _ _).trans_lt h)
  | big h1 h2 => exact prin h2.isPrincipal (VkA.big h1 h2)
  | @add x y _ hy ihx ihy =>
    rcases lt_or_ge y (ω ^ b) with h | h
    · rw [leMod_add_lt b x h]; exact VkA.add ihx hy
    · rw [leMod_add_ge b x h]; exact ihy
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (VkA.phi hx hy)

/-- **`x / ω^a` is a code** for codes `x`, `a`. -/
theorem vkA_divOp {a : Ordinal.{0}} (ha : VkA k Q a) : ∀ x, VkA k Q x → VkA k Q (x / ω ^ a) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div]; exact VkA.zero hQ.1
  obtain ⟨hsub, hlog⟩ := vkDec hQ x hx
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr : VkA k Q (x - ω ^ log ω x) := hsub _ (VkA.opow hQ.1 hlog) hlead
  have hrlt : x - ω ^ log ω x < x := leRest_lt hx0
  have hP0 : ω ^ a ≠ 0 := (opow_pos a omega0_pos).ne'
  rcases lt_or_ge (log ω x) a with hla | hla
  · have hxa : x < ω ^ a := by
      have h1 := lt_opow_succ_log_self one_lt_omega0 x
      exact h1.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hla))
    rw [Ordinal.div_eq_zero_of_lt hxa]; exact VkA.zero hQ.1
  · have e1 : ω ^ log ω x = ω ^ a * ω ^ (log ω x - a) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hla]
      rw [opow_add]
    have e2 : x / ω ^ a = ω ^ (log ω x - a) + (x - ω ^ log ω x) / ω ^ a :=
      calc x / ω ^ a = (ω ^ a * ω ^ (log ω x - a) + (x - ω ^ log ω x)) / ω ^ a := by rw [← e1, hdec]
        _ = ω ^ (log ω x - a) + (x - ω ^ log ω x) / ω ^ a := Ordinal.mul_add_div _ hP0 _
    rw [e2]
    exact VkA.add (VkA.opow hQ.1 ((vkDec hQ _ hlog).1 a ha hla)) (IH _ hrlt hr)

/-- **`x / Ω_k` is a code** for every code `x` (`k ≠ 0`). -/
theorem vkA_div (hk : k ≠ 0) (x : Ordinal.{0}) (hx : VkA k Q x) : VkA k Q (x / Om k) := by
  have := vkA_divOp hQ (VkA.om (k := k) hQ.1 le_rfl) x hx
  rwa [gg_SC_eps (SC_Om hk)] at this

end Dec

theorem vkA_mulNat (hQ : 0 < Q) {x : Ordinal.{0}} (hx : VkA k Q x) : ∀ n : ℕ, VkA k Q (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact VkA.zero hQ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact VkA.add (vkA_mulNat hQ hx n) hx

/-- **The argument of a code `φ(a, y)` (`y < φ(a, y)`) is a code.** -/
theorem vkA_arg (hQ : SC Q) : ∀ w, VkA k Q w → ∀ a y, w = veblen a y → y < w → VkA k Q y := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro a y he hy
    exact VkA.small (hy.trans hwQ)
  | @big w _ h2 =>
    intro a y he hy
    rw [(ugSC_veb h2 he hy).2]; exact VkA.zero hQ.1
  | @add x z _ _ ihx ihz =>
    intro a y he hy
    by_cases hz : z = x + z
    · exact ihz a y (hz.trans he) (hz ▸ hy)
    · by_cases hx : x = x + z
      · exact ihx a y (hx.trans he) (hx ▸ hy)
      · have hzl : z < x + z := lt_of_le_of_ne le_add_self hz
        have hxl : x < x + z := lt_of_le_of_ne le_self_add hx
        rw [he] at hzl hxl
        have := Ph.ph_veblen_prin a y hxl hzl
        rw [← he] at this; exact absurd this (lt_irrefl _)
  | @phi p q _ hq _ ihq =>
    intro a y he hy
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hfix : veblen p (veblen a y) = veblen a y := veblen_veblen_of_lt hpa y
      have hq' : q = veblen a y := by
        have h2 : veblen p q = veblen p (veblen a y) := by rw [hfix]; exact he
        exact veblen_injective p h2
      exact ihq a y hq' (by rw [hq']; rw [← he]; exact hy)
    · have : q = y := veblen_injective p he
      rw [← this]; exact hq
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      rw [he] at hfix
      have hyy : veblen a y = y := veblen_injective a hfix
      rw [he, hyy] at hy; exact absurd hy (lt_irrefl _)

/-- **The level of a code `φ(a, y)` (`y < φ(a, y)`) is a code.** -/
theorem vkA_lev : ∀ w, VkA k Q w → ∀ a y, w = veblen a y → y < w → VkA k Q a := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro a y he _
    exact VkA.small ((left_le_veblen a y).trans_lt (he ▸ hwQ))
  | @big w h1 h2 =>
    intro a y he hy
    rw [(ugSC_veb h2 he hy).1]; exact VkA.big h1 h2
  | @add x z _ _ ihx ihz =>
    intro a y he hy
    by_cases hz : z = x + z
    · exact ihz a y (hz.trans he) (hz ▸ hy)
    · by_cases hx : x = x + z
      · exact ihx a y (hx.trans he) (hx ▸ hy)
      · have hzl : z < x + z := lt_of_le_of_ne le_add_self hz
        have hxl : x < x + z := lt_of_le_of_ne le_self_add hx
        rw [he] at hzl hxl
        have := Ph.ph_veblen_prin a y hxl hzl
        rw [← he] at this; exact absurd this (lt_irrefl _)
  | @phi p q hp _ _ ihq =>
    intro a y he hy
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hfix : veblen p (veblen a y) = veblen a y := veblen_veblen_of_lt hpa y
      have hq : q = veblen a y := by
        have h2 : veblen p q = veblen p (veblen a y) := by rw [hfix]; exact he
        exact veblen_injective p h2
      exact ihq a y hq (by rw [hq]; rw [← he]; exact hy)
    · exact hp
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      rw [he] at hfix
      have hyy : veblen a y = y := veblen_injective a hfix
      rw [he, hyy] at hy; exact absurd hy (lt_irrefl _)

/-- **The base-`Ω₂` normal form of a code above the level 2**: `log_W x` and `x mod W^{log_W x}` are codes, the
digit is below `Q`. -/
theorem vkA_cnf (hQ : SC Q) {x : Ordinal.{0}} (hx : VkA (1 + 1) Q x) :
    VkA (1 + 1) Q (sgLW x) ∧ VkA (1 + 1) Q (x % leWe (sgLW x)) ∧ x / leWe (sgLW x) < Q := by
  have hk := ugTwo_ne
  have hlog : VkA (1 + 1) Q (log ω x) := (vkDec hQ x hx).2
  have he : VkA (1 + 1) Q (sgLW x) := vkA_div hQ hk _ hlog
  have hq : VkA (1 + 1) Q (x / leWe (sgLW x)) := vkA_divOp hQ (vkA_mulK hQ hk _ he) x hx
  have hqW : x / leWe (sgLW x) < Om (1 + 1) := by
    have hW0 : leWe (sgLW x) ≠ 0 := (leWe_pos _).ne'
    have h2 : x < leWe (sgLW x) * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  exact ⟨he, vkA_mod hQ (Om (1 + 1) * sgLW x) hx, vkA_lt_om hQ hq hqW⟩

end Googology.Trans.PoR.InaccPsi.R2.Vk
