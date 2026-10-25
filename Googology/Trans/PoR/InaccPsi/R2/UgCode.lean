import Googology.Trans.PoR.InaccPsi.R2.UgB

/-!
# Codes with `ψ_{Ω_{k+1}}`-atoms, generic in the level `k`

`UgC S k Q` (**the codes of level `k` over `Q`**): generated from the ordinals below `Q`, `Ω_k`, the atoms
`ψ_{Ω_{k+1}}(d)` with `d` a code and `d < ψ_{Ω_{k+1}}(d)`, by `+` and `φ`.  With no atom these are the codes
`LeCl Ω_k Q` (`UgC.of_le`); at `k = 2` the atoms are the `ψ₃`-atoms that `LeCl Ω₂ Q` lacks (`Ug.ugSnCL_wall`), at
`k = 1` the `ψ₂`-atoms of the images.  Every lemma below is **one proof for every level `k ≠ 0`**.

* `UgC.mono`, `UgC.zero`, `UgC.opow`, `UgC.of_le`, `ugC_lt_om` (a code below `Ω_k` is below `Q`);
* `ugCDec` (**decomposition**: `w − x` and `log_ω w` are codes, `Le.leClDec` with the atoms), `ugC_mod`,
  `ugC_mulOp` (`ω^c·y`), `ugC_mulK` (`Ω_k·y`), `ugC_div` (`x / Ω_k`), `ugC_divOp` (`x / ω^a`);
* `ugC_arg`, `ugC_lev` (**the Veblen parts of a code are codes**, `Ua.uaCl_arg`, `Td.tdCl_lev` with the atoms),
  `ugC_psiArg` (**the argument of a code atom is a code**);
* `ugC_cnf` (**the base-`Ω₂` normal form of a level-2 code**: `log_W x`, `x mod W^{log_W x}` are codes and the digit
  is below `Q`), `ugC_gam` (**`Γ₂ = ψ₃(0)` is a level-2 code**, while no `LeCl Ω₂ Q`-code is `≥ Γ₂`).

No new axiom.  New definition: `UgC`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ug

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **The codes of level `k` over `Q` with the atoms `ψ_{Ω_{k+1}}(d)`.** -/
inductive UgC (S : InaccSeq.{0}) (k Q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Q → UgC S k Q x
  | om : UgC S k Q (Om k)
  | add {x y : Ordinal.{0}} : UgC S k Q x → UgC S k Q y → UgC S k Q (x + y)
  | phi {x y : Ordinal.{0}} : UgC S k Q x → UgC S k Q y → UgC S k Q (veblen x y)
  | psi {d : Ordinal.{0}} : UgC S k Q d → d < S.psi d (Om (k + 1)) → UgC S k Q (S.psi d (Om (k + 1)))

variable {k Q : Ordinal.{0}}

theorem UgC.mono {Q' x : Ordinal.{0}} (h : Q ≤ Q') (hx : UgC S k Q x) : UgC S k Q' x := by
  induction hx with
  | small h' => exact UgC.small (h'.trans_le h)
  | om => exact UgC.om
  | add _ _ ihx ihy => exact UgC.add ihx ihy
  | phi _ _ ihx ihy => exact UgC.phi ihx ihy
  | psi _ hd ih => exact UgC.psi ih hd

theorem UgC.zero (hQ : 0 < Q) : UgC S k Q 0 := UgC.small hQ

theorem UgC.opow (hQ : 0 < Q) {c : Ordinal.{0}} (h : UgC S k Q c) : UgC S k Q (ω ^ c) := by
  have := UgC.phi (UgC.zero (S := S) (k := k) hQ) h; rwa [veblen_zero_apply] at this

/-- **A code without atoms is a code.** -/
theorem UgC.of_le {x : Ordinal.{0}} (h : LeCl (Om k) Q x) : UgC S k Q x := by
  induction h with
  | small h' => exact UgC.small h'
  | om => exact UgC.om
  | add _ _ ihx ihy => exact UgC.add ihx ihy
  | phi _ _ ihx ihy => exact UgC.phi ihx ihy

/-- A code below `Ω_k` is below `Q`. -/
theorem ugC_lt_om (hQ : SC Q) {x : Ordinal.{0}} (hx : UgC S k Q x) : x < Om k → x < Q := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hQ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1)) (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hQ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))
  | @psi d _ _ _ => exact fun h => absurd (psiS_bounds (S := S) d k).1 (not_lt.2 h.le)

section Dec

variable (hQ : SC Q) (hk : k ≠ 0)

include hQ hk

omit hk in
/-- A strongly critical generator `s` has `s − x ∈ {s, 0}` and `log_ω s = s`. -/
theorem ugC_gen {s : Ordinal.{0}} (hs : SC s) (hsC : UgC S k Q s) :
    (∀ x, UgC S k Q x → x ≤ s → UgC S k Q (s - x)) ∧ UgC S k Q (log ω s) := by
  have hE : ω ^ s = s := gg_SC_eps hs
  refine ⟨fun x _ hx => ?_, ?_⟩
  · rcases gg_sub_prin hs.isPrincipal hx with e | e <;> rw [e]
    · exact hsC
    · exact UgC.zero hQ.1
  · have : log ω s = s := by
      conv_lhs => rw [← hE]
      exact log_opow one_lt_omega0 _
    rw [this]; exact hsC

/-- **Decomposition**: a code `w` has `w − x` (for every code `x ≤ w`) and `log_ω w` codes. -/
theorem ugCDec : ∀ w, UgC S k Q w →
    (∀ x, UgC S k Q x → x ≤ w → UgC S k Q (w - x)) ∧ UgC S k Q (log ω w) := by
  have h0 : UgC S k Q 0 := UgC.zero hQ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, UgC S k Q v → v ≤ w →
      (∀ x, UgC S k Q x → x ≤ v → UgC S k Q (v - x)) ∧ UgC S k Q (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => UgC.small ((Ordinal.sub_le_self v x).trans_lt h),
      UgC.small ((log_le_self ω v).trans_lt h)⟩
  | om => intro _; exact ugC_gen hQ (SC_Om hk) UgC.om
  | @psi d hd hdl _ => intro _; exact ugC_gen hQ (SC_psi (InR_Om_succ k) d) (UgC.psi hd hdl)
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact UgC.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : UgC S k Q (x - u) := (IHo x hxw hx).1 u hu hux.le
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
        · exact UgC.opow hQ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact UgC.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact UgC.phi ha hb

/-- `ω^c·y` is a code for codes `c`, `y`. -/
theorem ugC_mulOp {c : Ordinal.{0}} (hc : UgC S k Q c) : ∀ y, UgC S k Q y → UgC S k Q (ω ^ c * y) := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero]; exact UgC.zero hQ.1
  obtain ⟨hsub, hlog⟩ := ugCDec hQ hk y hy
  have hlead : ω ^ log ω y ≤ y := opow_log_le_self ω hy0
  have hdec : ω ^ log ω y + (y - ω ^ log ω y) = y := Ordinal.add_sub_cancel_of_le hlead
  have e : ω ^ c * y = ω ^ (c + log ω y) + ω ^ c * (y - ω ^ log ω y) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add]
  rw [e]
  exact UgC.add (UgC.opow hQ.1 (UgC.add hc hlog))
    (IH _ (leRest_lt hy0) (hsub _ (UgC.opow hQ.1 hlog) hlead))

/-- **`Ω_k·y` is a code** for every code `y`. -/
theorem ugC_mulK (y : Ordinal.{0}) (hy : UgC S k Q y) : UgC S k Q (Om k * y) := by
  have := ugC_mulOp hQ hk (UgC.om (S := S) (k := k) (Q := Q)) y hy
  rwa [gg_SC_eps (SC_Om hk)] at this

/-- **`UgC` is closed under `x ↦ x % ω^b`.** -/
theorem ugC_mod (b : Ordinal.{0}) {x : Ordinal.{0}} (hx : UgC S k Q x) : UgC S k Q (x % ω ^ b) := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → UgC S k Q p → UgC S k Q (p % ω ^ b) := by
    intro p hp h
    rcases leMod_prin hp b with e | e
    · rw [e]; exact h
    · rw [e]; exact UgC.zero hQ.1
  induction hx with
  | small h => exact UgC.small ((Ordinal.mod_le _ _).trans_lt h)
  | om => exact prin (SC_Om hk).isPrincipal UgC.om
  | @psi d hd hdl _ => exact prin (SC_psi (InR_Om_succ k) d).isPrincipal (UgC.psi hd hdl)
  | @add x y _ hy ihx ihy =>
    rcases lt_or_ge y (ω ^ b) with h | h
    · rw [leMod_add_lt b x h]; exact UgC.add ihx hy
    · rw [leMod_add_ge b x h]; exact ihy
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (UgC.phi hx hy)

/-- **`x / ω^a` is a code** for codes `x`, `a`. -/
theorem ugC_divOp {a : Ordinal.{0}} (ha : UgC S k Q a) : ∀ x, UgC S k Q x → UgC S k Q (x / ω ^ a) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div]; exact UgC.zero hQ.1
  obtain ⟨hsub, hlog⟩ := ugCDec hQ hk x hx
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr : UgC S k Q (x - ω ^ log ω x) := hsub _ (UgC.opow hQ.1 hlog) hlead
  have hrlt : x - ω ^ log ω x < x := leRest_lt hx0
  have hP0 : ω ^ a ≠ 0 := (opow_pos a omega0_pos).ne'
  rcases lt_or_ge (log ω x) a with hla | hla
  · have hxa : x < ω ^ a := by
      have h1 := lt_opow_succ_log_self one_lt_omega0 x
      exact h1.trans_le (opow_le_opow_right omega0_pos (Order.succ_le_of_lt hla))
    rw [Ordinal.div_eq_zero_of_lt hxa]; exact UgC.zero hQ.1
  · have e1 : ω ^ log ω x = ω ^ a * ω ^ (log ω x - a) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hla]
      rw [opow_add]
    have e2 : x / ω ^ a = ω ^ (log ω x - a) + (x - ω ^ log ω x) / ω ^ a :=
      calc x / ω ^ a = (ω ^ a * ω ^ (log ω x - a) + (x - ω ^ log ω x)) / ω ^ a := by rw [← e1, hdec]
        _ = ω ^ (log ω x - a) + (x - ω ^ log ω x) / ω ^ a := Ordinal.mul_add_div _ hP0 _
    rw [e2]
    exact UgC.add (UgC.opow hQ.1 ((ugCDec hQ hk _ hlog).1 a ha hla)) (IH _ hrlt hr)

/-- **`x / Ω_k` is a code** for every code `x`. -/
theorem ugC_div (x : Ordinal.{0}) (hx : UgC S k Q x) : UgC S k Q (x / Om k) := by
  have := ugC_divOp hQ hk (UgC.om (S := S) (k := k) (Q := Q)) x hx
  rwa [gg_SC_eps (SC_Om hk)] at this

end Dec

/-- A strongly critical value `w = φ(a, y)` with `y < w` has `a = w`, `y = 0`. -/
theorem ugSC_veb {w a y : Ordinal.{0}} (hw : SC w) (he : w = veblen a y) (hy : y < w) : a = w ∧ y = 0 := by
  rcases lt_or_ge a w with haw | hwa
  · have : veblen a y < w := hw.2 a haw y hy
    rw [← he] at this; exact absurd this (lt_irrefl _)
  · have hle : a ≤ w := by rw [he]; exact left_le_veblen a y
    have ha : a = w := le_antisymm hle hwa
    refine ⟨ha, ?_⟩
    rw [ha] at he
    have h2 : veblen w y = veblen w 0 := by rw [← he, hw.veblen_zero]
    exact veblen_injective w h2

/-- **The argument of a code `φ(a, y)` (`y < φ(a, y)`) is a code.** -/
theorem ugC_arg (hQ : SC Q) : ∀ w, UgC S k Q w → ∀ a y, w = veblen a y → y < w → UgC S k Q y := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro a y he hy
    exact UgC.small (hy.trans hwQ)
  | om =>
    intro a y he hy
    have hk : k ≠ 0 := by
      rintro rfl
      rw [Om_zero] at he hy
      exact absurd hy (not_lt.2 zero_le)
    rw [(ugSC_veb (SC_Om hk) he hy).2]; exact UgC.zero hQ.1
  | @psi d _ _ _ =>
    intro a y he hy
    rw [(ugSC_veb (SC_psi (InR_Om_succ k) d) he hy).2]; exact UgC.zero hQ.1
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
theorem ugC_lev : ∀ w, UgC S k Q w → ∀ a y, w = veblen a y → y < w → UgC S k Q a := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro a y he _
    exact UgC.small ((left_le_veblen a y).trans_lt (he ▸ hwQ))
  | om =>
    intro a y he hy
    have hk : k ≠ 0 := by
      rintro rfl
      rw [Om_zero] at he hy
      exact absurd hy (not_lt.2 zero_le)
    rw [(ugSC_veb (SC_Om hk) he hy).1]; exact UgC.om
  | @psi d hd hdl _ =>
    intro a y he hy
    rw [(ugSC_veb (SC_psi (InR_Om_succ k) d) he hy).1]; exact UgC.psi hd hdl
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

/-- **The argument of a code atom is a code**: `ψ_{Ω_{k+1}}(d)` a code with `d < ψ_{Ω_{k+1}}(d)` gives `d` a code. -/
theorem ugC_psiArg {d : Ordinal.{0}} (hd : d < S.psi d (Om (k + 1))) :
    ∀ w, UgC S k Q w → w = S.psi d (Om (k + 1)) → UgC S k Q d := by
  have hκ : S.InR (Om (k + 1)) := InR_Om_succ k
  have hSC := SC_psi hκ d
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro he
    exact UgC.small (hd.trans (he ▸ hwQ))
  | om =>
    intro he
    have := (psiS_bounds (S := S) d k).1
    rw [← he] at this; exact absurd this (lt_irrefl _)
  | @psi d' hd' hdl' _ =>
    intro he
    have : d' = d := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := psi_lt_psi_of_mem (S := S) hκ h (CSet.of_lt (he ▸ hdl'))
        rw [he] at this; exact absurd this (lt_irrefl _)
      · have := psi_lt_psi_of_mem (S := S) hκ h (CSet.of_lt (he.symm ▸ hd))
        rw [he] at this; exact absurd this (lt_irrefl _)
    rw [← this]; exact hd'
  | @add x z _ _ ihx ihz =>
    intro he
    by_cases hz : z = x + z
    · exact ihz (hz.trans he)
    · by_cases hx : x = x + z
      · exact ihx (hx.trans he)
      · have hzl : z < x + z := lt_of_le_of_ne le_add_self hz
        have hxl : x < x + z := lt_of_le_of_ne le_self_add hx
        rw [he] at hzl hxl
        have := hSC.isPrincipal hxl hzl
        rw [← he] at this; exact absurd this (lt_irrefl _)
  | @phi p q _ _ ihp ihq =>
    intro he
    by_cases hp : p = veblen p q
    · exact ihp (hp.trans he)
    by_cases hq : q = veblen p q
    · exact ihq (hq.trans he)
    have hpl : p < veblen p q := lt_of_le_of_ne (left_le_veblen p q) hp
    have hql : q < veblen p q := lt_of_le_of_ne (right_le_veblen p q) hq
    rw [he] at hpl hql
    have := hSC.2 p hpl q hql
    rw [← he] at this; exact absurd this (lt_irrefl _)

theorem ugTwo_ne : (1 + 1 : Ordinal.{0}) ≠ 0 := by rw [one_add_one_eq_two]; exact two_ne_zero

/-- **The base-`Ω₂` normal form of a level-2 code**: `log_W x` and `x mod W^{log_W x}` are codes, the digit is
below `Q`. -/
theorem ugC_cnf (hQ : SC Q) {x : Ordinal.{0}} (hx : UgC S (1 + 1) Q x) :
    UgC S (1 + 1) Q (sgLW x) ∧ UgC S (1 + 1) Q (x % leWe (sgLW x)) ∧ x / leWe (sgLW x) < Q := by
  have hk := ugTwo_ne
  have hlog : UgC S (1 + 1) Q (log ω x) := (ugCDec hQ hk x hx).2
  have he : UgC S (1 + 1) Q (sgLW x) := ugC_div hQ hk _ hlog
  have hq : UgC S (1 + 1) Q (x / leWe (sgLW x)) := ugC_divOp hQ hk (ugC_mulK hQ hk _ he) x hx
  have hqW : x / leWe (sgLW x) < Om (1 + 1) := by
    have hW0 : leWe (sgLW x) ≠ 0 := (leWe_pos _).ne'
    have h2 : x < leWe (sgLW x) * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  exact ⟨he, ugC_mod hQ hk (Om (1 + 1) * sgLW x) hx, ugC_lt_om hQ hq hqW⟩

/-- **`Γ₂ = ψ₃(0)` is a level-2 code** over every `Q > 0`. -/
theorem ugC_gam (hQ : 0 < Q) : UgC S (1 + 1) Q uaGam := by
  rw [Ud.udGam_eq (S := S)]
  exact UgC.psi (UgC.zero hQ) (SC_psi (InR_Om_succ (1 + 1)) 0).1

end Googology.Trans.PoR.InaccPsi.R2.Ug
