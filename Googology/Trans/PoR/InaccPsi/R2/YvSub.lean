import Googology.Trans.PoR.InaccPsi.R2.XeFix
import Googology.Trans.PoR.InaccPsi.R2.VcSub

/-!
# The leaf substitution on codes below `θ` (every cardinal level), as a relation

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B₂ = Uc.ucB`, `θ = ConjT.th S`, `Hˡ⁽ˢ⁾_γ = Ul.ulH S s γ`, `vcSub` / `VcLv` the leaf substitution and leaf predicate
of `R2.VcSub` (codes below `B₂`).  Above `B₂` a code `z ∈ (Ω_s, Ω_{s+1})` (`s ≥ 1` finite, `z ≥ B₂`) has exactly one
of the three forms of the dictionary `D(s)` (`Vs.vsShape`): `ω^g·k + r` (`g = log_ω z`, not an `ε`-number), an
`ε`-number `φ(a, c)` in normal form (not strongly critical), an atom `Hˡ⁽ˢ⁾_γ(y)` (`γ = Vp.vpLev S s z`, `y =
Vp.vpI S s γ z`); the constants `Ω_s`, `s ≥ 2`, are kept.  This module writes the canonical decomposition as two
inductive predicates:

* `YvLv S P z` (**every leaf of `z` satisfies `P`**: below `B₂` by `Vc.VcLv`, above by the parts);
* `YvR S f z z'` (**`z'` is the leaf substitution of `z` under `f`**: below `B₂` `z' = vcSub f z`, above the parts are
  substituted and the operation is kept), `yvR_unique` (**the substitution is a function**: the clause of a code is
  determined by the code), `yvSub` (the function), `yvSub_eq` (`YvR f z z' ⇒ yvSub f z = z'`);
* `YvLv.mono`, `yvLv_small`, `yvR_small`.

No new axiom.  New definitions: `YvLv`, `YvR` (inductive predicates), `yvSub`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc

/-- **Every leaf of the canonical decomposition of `z` satisfies `P`.** -/
inductive YvLv (S : InaccSeq.{0}) (P : Ordinal.{0} → Prop) : Ordinal.{0} → Prop
  | low {z : Ordinal.{0}} : z < ucB → Vc.VcLv P z → YvLv S P z
  | om {s z : Ordinal.{0}} : 1 < s → s < ω → z = Om s → YvLv S P z
  | cnf {s z : Ordinal.{0}} : 1 ≤ s → s < ω → Om s < z → z < Om (s + 1) → ucB ≤ z → ω ^ z ≠ z →
      YvLv S P (log ω z) → YvLv S P (z % ω ^ log ω z) → YvLv S P z
  | veb {s z : Ordinal.{0}} : 1 ≤ s → s < ω → Om s < z → z < Om (s + 1) → ucB ≤ z → ω ^ z = z → ¬ SC z →
      YvLv S P (invVeblen₁ z) → YvLv S P (invVeblen₂ z) → YvLv S P z
  | atom {s z : Ordinal.{0}} : 1 ≤ s → s < ω → Om s < z → z < Om (s + 1) → ucB ≤ z → SC z →
      YvLv S P (Vp.vpLev S s z) → YvLv S P (Vp.vpI S s (Vp.vpLev S s z) z) → YvLv S P z

/-- **`z'` is the leaf substitution of `z` under `f`.** -/
inductive YvR (S : InaccSeq.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} → Prop
  | low {z : Ordinal.{0}} : z < ucB → YvR S f z (Vc.vcSub f z)
  | om {s z : Ordinal.{0}} : 1 < s → s < ω → z = Om s → YvR S f z z
  | cnf {s z g' r' : Ordinal.{0}} : 1 ≤ s → s < ω → Om s < z → z < Om (s + 1) → ucB ≤ z → ω ^ z ≠ z →
      YvR S f (log ω z) g' → YvR S f (z % ω ^ log ω z) r' →
      YvR S f z ((if ω ^ log ω z = log ω z then g' else ω ^ g') * (z / ω ^ log ω z) + r')
  | veb {s z a' c' : Ordinal.{0}} : 1 ≤ s → s < ω → Om s < z → z < Om (s + 1) → ucB ≤ z → ω ^ z = z → ¬ SC z →
      YvR S f (invVeblen₁ z) a' → YvR S f (invVeblen₂ z) c' → YvR S f z (veblen a' c')
  | atom {s z γ' y' : Ordinal.{0}} : 1 ≤ s → s < ω → Om s < z → z < Om (s + 1) → ucB ≤ z → SC z →
      YvR S f (Vp.vpLev S s z) γ' → YvR S f (Vp.vpI S s (Vp.vpLev S s z) z) y' → YvR S f z (ulH S s γ' y')

variable {S : InaccSeq.{0}}

theorem yv_B_lt_Om2 : (ucB : Ordinal.{0}) < Om (1 + 1) := by
  rw [Ui.ui_one_W]; exact ucB_lt_Om2

/-- `Ω_s` (`1 < s < ω`) is not below `B₂`. -/
theorem yv_Om_ge_B {s : Ordinal.{0}} (hs : 1 < s) : (ucB : Ordinal.{0}) ≤ Om s :=
  yv_B_lt_Om2.le.trans (Om_le_Om.2 (Order.add_one_le_of_lt hs))

/-- **The cardinal interval of a code is unique.** -/
theorem yv_lev_unique {s s' z : Ordinal.{0}} (h1 : Om s < z) (h2 : z < Om (s + 1)) (h1' : Om s' < z)
    (h2' : z < Om (s' + 1)) : s = s' := by
  rcases lt_trichotomy s s' with h | h | h
  · exact absurd ((Om_le_Om.2 (Order.add_one_le_of_lt h)).trans_lt h1') (not_lt.2 h2.le)
  · exact h
  · exact absurd ((Om_le_Om.2 (Order.add_one_le_of_lt h)).trans_lt h1) (not_lt.2 h2'.le)

/-- `Ω_s` is in no open interval `(Ω_t, Ω_{t+1})`. -/
theorem yv_Om_not_in {s t : Ordinal.{0}} (h1 : Om t < Om s) (h2 : Om s < Om (t + 1)) : False := by
  rw [Om_lt_Om] at h1 h2
  exact absurd h2 (not_lt.2 (Order.add_one_le_of_lt h1))

theorem yv_SC_eps {z : Ordinal.{0}} (h : SC z) : ω ^ z = z := Gg.gg_SC_eps h

/-- **The substitution is a function.** -/
theorem yvR_unique {f : Ordinal.{0} → Ordinal.{0}} {z a : Ordinal.{0}} (ha : YvR S f z a) :
    ∀ {b : Ordinal.{0}}, YvR S f z b → a = b := by
  induction ha with
  | low hz =>
    intro b hb
    cases hb with
    | low _ => rfl
    | om hs _ e => exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B hs))
    | cnf _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | veb _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | atom _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | om hs _ e =>
    intro b hb
    subst e
    cases hb with
    | low hz => exact absurd hz (not_lt.2 (yv_Om_ge_B hs))
    | om _ _ _ => rfl
    | cnf _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
    | veb _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
    | atom _ _ h1 h2 => exact (yv_Om_not_in h1 h2).elim
  | cnf _ _ h1 h2 hB hE _ _ ihg ihr =>
    intro b hb
    cases hb with
    | low hz => exact absurd hz (not_lt.2 hB)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ _ hg hr => rw [ihg hg, ihr hr]
    | veb _ _ _ _ _ hE' => exact absurd hE' hE
    | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) hE
  | veb _ _ h1 h2 hB hE hS _ _ iha ihc =>
    intro b hb
    cases hb with
    | low hz => exact absurd hz (not_lt.2 hB)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd hE hE'
    | veb _ _ _ _ _ _ _ ha hc => rw [iha ha, ihc hc]
    | atom _ _ _ _ _ hSC => exact absurd hSC hS
  | atom _ _ h1 h2 hB hSC _ _ ihl ihy =>
    intro b hb
    cases hb with
    | low hz => exact absurd hz (not_lt.2 hB)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd (yv_SC_eps hSC) hE'
    | veb _ _ _ _ _ _ hS => exact absurd hSC hS
    | atom _ _ h1' h2' _ _ hl hy =>
      have e := yv_lev_unique h1 h2 h1' h2'
      subst e
      rw [ihl hl, ihy hy]

/-- **The leaf substitution as a function** (`z` itself when `z` has no canonical decomposition). -/
noncomputable def yvSub (S : InaccSeq.{0}) (f : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) : Ordinal.{0} :=
  open Classical in if h : ∃ z', YvR S f z z' then Classical.choose h else z

theorem yvSub_eq {f : Ordinal.{0} → Ordinal.{0}} {z z' : Ordinal.{0}} (h : YvR S f z z') : yvSub S f z = z' := by
  have he : ∃ z', YvR S f z z' := ⟨z', h⟩
  unfold yvSub
  rw [dif_pos he]
  exact yvR_unique (Classical.choose_spec he) h

theorem yvSub_low (f : Ordinal.{0} → Ordinal.{0}) {z : Ordinal.{0}} (hz : z < ucB) :
    yvSub S f z = Vc.vcSub f z := yvSub_eq (YvR.low hz)

theorem YvLv.mono {P Q : Ordinal.{0} → Prop} (hPQ : ∀ x, P x → Q x) {z : Ordinal.{0}} (h : YvLv S P z) :
    YvLv S Q z := by
  induction h with
  | low hz hL => exact YvLv.low hz (Vc.VcLv_mono (fun x _ hx => hPQ x hx) _ hL)
  | om hs hs' e => exact YvLv.om hs hs' e
  | cnf a b c d e g _ _ ih1 ih2 => exact YvLv.cnf a b c d e g ih1 ih2
  | veb a b c d e g k _ _ ih1 ih2 => exact YvLv.veb a b c d e g k ih1 ih2
  | atom a b c d e g _ _ ih1 ih2 => exact YvLv.atom a b c d e g ih1 ih2

theorem yvLv_and {P Q : Ordinal.{0} → Prop} {z : Ordinal.{0}} (hP : YvLv S P z) (hQ : YvLv S Q z) :
    YvLv S (fun x => P x ∧ Q x) z := by
  induction hP with
  | low hz hL =>
    cases hQ with
    | low _ hL' => exact YvLv.low hz (Vc.VcLv_and _ hL hL')
    | om hs _ e => exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B hs))
    | cnf _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | veb _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
    | atom _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | om hs hs' e => exact YvLv.om hs hs' e
  | cnf a b h1 h2 e g _ _ ih1 ih2 =>
    cases hQ with
    | low hz => exact absurd hz (not_lt.2 e)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ _ q1 q2 => exact YvLv.cnf a b h1 h2 e g (ih1 q1) (ih2 q2)
    | veb _ _ _ _ _ hE' => exact absurd hE' g
    | atom _ _ _ _ _ hSC => exact absurd (yv_SC_eps hSC) g
  | veb a b h1 h2 e g k _ _ ih1 ih2 =>
    cases hQ with
    | low hz => exact absurd hz (not_lt.2 e)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd g hE'
    | veb _ _ _ _ _ _ _ q1 q2 => exact YvLv.veb a b h1 h2 e g k (ih1 q1) (ih2 q2)
    | atom _ _ _ _ _ hSC => exact absurd hSC k
  | atom a b h1 h2 e g _ _ ih1 ih2 =>
    cases hQ with
    | low hz => exact absurd hz (not_lt.2 e)
    | om _ _ e => subst e; exact (yv_Om_not_in h1 h2).elim
    | cnf _ _ _ _ _ hE' => exact absurd (yv_SC_eps g) hE'
    | veb _ _ _ _ _ _ hS => exact absurd g hS
    | atom _ _ h1' h2' _ _ q1 q2 =>
      have e' := yv_lev_unique h1 h2 h1' h2'
      subst e'
      exact YvLv.atom a b h1 h2 e g (ih1 q1) (ih2 q2)

end Googology.Trans.PoR.InaccPsi.R2.Yv
