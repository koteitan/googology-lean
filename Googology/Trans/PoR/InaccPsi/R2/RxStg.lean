import Googology.Trans.PoR.InaccPsi.R2.RxNor

/-!
# The stages of the normal hull

`RxN S T` the normal hull over `T` (`Rx.RxN`).

* `RxNs S T n` (**the `n`-th stage**): the members generated in `n` steps (every finite `Ω_k`, the `I_k`, `I_ω`,
  `0` and the `x < T` at every stage; the collapses `ψ_{Ω_{k+1}}(d)` at finite levels `k ≥ 1` without a stage for the
  subscript); `rxN_iff_stage` (`RxN S T x ⇔ ∃ n, RxNs S T n x`), `rxNs_mono`;
* `rxNs_lt_T` (**a countable member is below `T`**, for `T ≤ Ω₁` strongly critical);
* `rxNsDec` (**the decomposition stays at the stage**: `w − x` for a member `x ≤ w`, and `log_ω w`), `rxNsDecV`
  (the Veblen parts `a, b` of `w = φ(a, b)`, `b < w`), `rxNsSC` (**a strongly critical member `> Ω₁` that is not a
  cardinal is `ψ_π(d)`, `π ≠ Ω₁`, with a normal argument `d` at an earlier stage**);
* `rxH S T x` (**the least stage**), `rxH_spec`, `rxH_le`.

No new axiom.  New definitions: `RxNs`, `rxH`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg

/-- **The stages of the normal hull over `T`.** -/
inductive RxNs (S : InaccSeq.{0}) (T : Ordinal.{0}) : ℕ → Ordinal.{0} → Prop
  | small {n : ℕ} {x : Ordinal.{0}} : x < T → RxNs S T n x
  | zero {n : ℕ} : RxNs S T n 0
  | inacc {n : ℕ} (k : ℕ) : RxNs S T n (S.I k)
  | inaccW {n : ℕ} : RxNs S T n S.Iw
  | omn {n : ℕ} (k : ℕ) : RxNs S T n (Om (k : Ordinal.{0}))
  | add {n : ℕ} {x y : Ordinal.{0}} : RxNs S T n x → RxNs S T n y → RxNs S T (n + 1) (x + y)
  | phi {n : ℕ} {x y : Ordinal.{0}} : RxNs S T n x → RxNs S T n y → RxNs S T (n + 1) (veblen x y)
  | om {n : ℕ} {x : Ordinal.{0}} : RxNs S T n x → RxNs S T (n + 1) (Om x)
  | psiN {n : ℕ} {d : Ordinal.{0}} (k : ℕ) : 1 ≤ k → RxNs S T n d →
      d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1))) →
      RxNs S T (n + 1) (S.psi d (Om ((k : Ordinal.{0}) + 1)))
  | psiG {n : ℕ} {π d : Ordinal.{0}} : S.InR π → π ≠ Om 1 → RxNs S T n π → RxNs S T n d →
      d ∈ S.CSet d (S.psi d π) → RxNs S T (n + 1) (S.psi d π)
  | up {n : ℕ} {x : Ordinal.{0}} : RxNs S T n x → RxNs S T (n + 1) x

variable {S : InaccSeq.{0}} {T : Ordinal.{0}}

theorem rxNs_mono {n m : ℕ} (h : n ≤ m) {x : Ordinal.{0}} (hx : RxNs S T n x) : RxNs S T m x := by
  induction h with
  | refl => exact hx
  | step _ ih => exact RxNs.up ih

theorem rxN_nat (k : ℕ) : RxN S T (k : Ordinal.{0}) := by
  induction k with
  | zero => exact RxN.zero
  | succ k ih => rw [Nat.cast_succ]; exact RxN.succ ih

theorem rxNat_ne_one {k : ℕ} (hk : 1 ≤ k) : Om ((k : Ordinal.{0}) + 1) ≠ Om 1 := by
  intro h
  have h1 : (k : Ordinal.{0}) + 1 = 1 := Om_inj.1 h
  have h2 : (k : Ordinal.{0}) < 1 := h1 ▸ lt_add_one _
  have h3 : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
  exact absurd h2 (not_lt.2 h3)

/-- **`RxN S T x ⇔ ∃ n, RxNs S T n x`.** -/
theorem rxN_iff_stage {x : Ordinal.{0}} : RxN S T x ↔ ∃ n, RxNs S T n x := by
  constructor
  · intro hx
    induction hx with
    | small h => exact ⟨0, RxNs.small h⟩
    | zero => exact ⟨0, RxNs.zero⟩
    | inacc k => exact ⟨0, RxNs.inacc k⟩
    | inaccW => exact ⟨0, RxNs.inaccW⟩
    | add _ _ ihx ihy =>
      obtain ⟨n, hn⟩ := ihx; obtain ⟨m, hm⟩ := ihy
      exact ⟨max n m + 1, RxNs.add (rxNs_mono (le_max_left n m) hn) (rxNs_mono (le_max_right n m) hm)⟩
    | phi _ _ ihx ihy =>
      obtain ⟨n, hn⟩ := ihx; obtain ⟨m, hm⟩ := ihy
      exact ⟨max n m + 1, RxNs.phi (rxNs_mono (le_max_left n m) hn) (rxNs_mono (le_max_right n m) hm)⟩
    | om _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, RxNs.om hn⟩
    | psi hπ hπ1 _ _ hd ihπ ihd =>
      obtain ⟨n, hn⟩ := ihπ; obtain ⟨m, hm⟩ := ihd
      exact ⟨max n m + 1, RxNs.psiG hπ hπ1 (rxNs_mono (le_max_left n m) hn)
        (rxNs_mono (le_max_right n m) hm) hd⟩
  · rintro ⟨n, hn⟩
    induction hn with
    | small h => exact RxN.small h
    | zero => exact RxN.zero
    | inacc k => exact RxN.inacc k
    | inaccW => exact RxN.inaccW
    | omn k => exact RxN.om (rxN_nat k)
    | add _ _ ihx ihy => exact RxN.add ihx ihy
    | phi _ _ ihx ihy => exact RxN.phi ihx ihy
    | om _ ih => exact RxN.om ih
    | psiN k hk _ hd ih =>
      exact RxN.psi (InR_Om_succ _) (rxNat_ne_one hk) (RxN.om (RxN.succ (rxN_nat k))) ih hd
    | psiG hπ hπ1 _ _ hd ihπ ihd => exact RxN.psi hπ hπ1 ihπ ihd hd
    | up _ ih => exact ih

/-- **A countable member is below `T`.** -/
theorem rxNs_lt_T (hT : SC T) {n : ℕ} {x : Ordinal.{0}} (hx : RxNs S T n x) : x < Om 1 → x < T := by
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => hT.1
  | inacc k => exact fun h => absurd h (not_lt.2 (Low.Om_one_le_I k))
  | inaccW => exact fun h => absurd h (not_lt.2 ((Low.Om_one_le_I 0).trans (S.I_lt_Iw 0).le))
  | omn k =>
    intro h
    have hk : (k : Ordinal.{0}) < 1 := Om_lt_Om.1 h
    rw [Order.lt_one_iff] at hk
    rw [hk, Om_zero]; exact hT.1
  | add _ _ ihx ihy =>
    exact fun h => hT.isPrincipal (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi _ x y _ _ ihx ihy =>
    exact fun h => hT.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))
  | @om _ x _ _ =>
    intro h
    have hk : x < 1 := Om_lt_Om.1 h
    rw [Order.lt_one_iff] at hk
    rw [hk, Om_zero]; exact hT.1
  | psiN k hk _ _ _ =>
    exact fun h => absurd h (not_lt.2 (rxOm1_le_psi (InR_Om_succ _) (rxNat_ne_one hk)))
  | psiG hπ hπ1 _ _ _ _ _ => exact fun h => absurd h (not_lt.2 (rxOm1_le_psi hπ hπ1))
  | up _ ih => exact ih

/-- A principal member: `w − x ∈ {w, 0}` and `log_ω w = w` at an `ε`-number. -/
theorem rxNs_prin_dec {n : ℕ} {w : Ordinal.{0}} (hw : RxNs S T n w) (hP : IsPrincipal (· + ·) w)
    (hε : ω ^ w = w) :
    (∀ x, x ≤ w → RxNs S T n (w - x)) ∧ RxNs S T n (log ω w) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases gg_sub_prin hP hx with e | e <;> rw [e]
    · exact hw
    · exact RxNs.zero
  · have : log ω w = w := by conv_lhs => rw [← hε]; exact log_opow one_lt_omega0 _
    rw [this]; exact hw

/-- **The decomposition stays at the stage.** -/
theorem rxNsDec : ∀ w, ∀ n, RxNs S T n w →
    (∀ x, RxN S T x → x ≤ w → RxNs S T n (w - x)) ∧ RxNs S T n (log ω w) := by
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro n hw
  suffices H : ∀ n v, RxNs S T n v → v ≤ w →
      (∀ x, RxN S T x → x ≤ v → RxNs S T n (v - x)) ∧ RxNs S T n (log ω v) from H n w hw le_rfl
  intro n v hv
  induction hv with
  | @small _ v h =>
    intro _
    exact ⟨fun x _ _ => RxNs.small ((Ordinal.sub_le_self v x).trans_lt h),
      RxNs.small ((log_le_self ω v).trans_lt h)⟩
  | zero =>
    intro _
    refine ⟨fun x _ _ => by rw [Ordinal.zero_sub]; exact RxNs.zero, ?_⟩
    rw [Ordinal.log_zero_right]; exact RxNs.zero
  | @inacc m k =>
    intro _
    have hS := SC_I (S := S) k
    have h := rxNs_prin_dec (RxNs.inacc (S := S) (T := T) (n := m) k) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @inaccW m =>
    intro _
    have hS := SC_Iw (S := S)
    have h := rxNs_prin_dec (RxNs.inaccW (S := S) (T := T) (n := m)) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @omn m k =>
    intro _
    rcases eq_or_ne (k : Ordinal.{0}) 0 with h0 | h0
    · rw [h0, Om_zero]
      refine ⟨fun x _ _ => by rw [Ordinal.zero_sub]; exact RxNs.zero, ?_⟩
      rw [Ordinal.log_zero_right]; exact RxNs.zero
    · have hS := SC_Om h0
      have h := rxNs_prin_dec (RxNs.omn (S := S) (T := T) (n := m) k) hS.isPrincipal (gg_SC_eps hS)
      exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @add n u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact RxNs.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          obtain ⟨m, hm⟩ := rxN_iff_stage.1 hx
          have hxu' : RxN S T (x - u) :=
            rxN_iff_stage.2 ⟨m, (IHo x hxw m hm).1 u (rxN_iff_stage.2 ⟨n, hu⟩) hux.le⟩
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact RxNs.up (hv'.1 (x - u) hxu' hxv)
        · rw [heq, Ordinal.sub_self]; exact RxNs.zero
    · rcases ggLog_add u v with e | e <;> rw [e]
      · exact RxNs.up hu'.2
      · exact RxNs.up hv'.2
  | @phi n a b ha hb iha ihb =>
    intro hle
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · have := RxNs.phi (RxNs.zero (S := S) (T := T) (n := n)) hb
          rwa [veblen_zero_apply] at this
        · exact RxNs.zero
      · rw [log_opow one_lt_omega0]; exact RxNs.up hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      have h := rxNs_prin_dec (RxNs.phi ha hb) hp hE
      exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @om n p hp _ =>
    intro _
    rcases eq_or_ne p 0 with rfl | h0
    · rw [Om_zero]
      refine ⟨fun x _ _ => by rw [Ordinal.zero_sub]; exact RxNs.zero, ?_⟩
      rw [Ordinal.log_zero_right]; exact RxNs.zero
    · have hS := SC_Om h0
      have h := rxNs_prin_dec (RxNs.om hp) hS.isPrincipal (gg_SC_eps hS)
      exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @psiN n d k hk hd hdn _ =>
    intro _
    have hS := SC_psi (S := S) (InR_Om_succ (k : Ordinal.{0})) d
    have h := rxNs_prin_dec (RxNs.psiN k hk hd hdn) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @psiG n π d hπ hπ1 hπN hdN hdn _ _ =>
    intro _
    have hS := SC_psi (S := S) hπ d
    have h := rxNs_prin_dec (RxNs.psiG hπ hπ1 hπN hdN hdn) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | up _ ih =>
    intro hle
    obtain ⟨h1, h2⟩ := ih hle
    exact ⟨fun x hx hxv => RxNs.up (h1 x hx hxv), RxNs.up h2⟩

/-- A strongly critical member `x = φ(a, b)` with `b < x` has `a = x`, `b = 0`. -/
theorem rxSC_veb {x a b : Ordinal.{0}} (hS : SC x) (e : veblen a b = x) (hb : b < x) : a = x ∧ b = 0 := by
  have ha : a = x := by
    rcases lt_trichotomy a x with h | h | h
    · exact absurd e (hS.2 a h b hb).ne
    · exact h
    · exact absurd (e ▸ left_le_veblen a b) (not_le.2 h)
  subst ha
  have h1 : veblen a 0 = veblen a b := by rw [hS.veblen_zero, e]
  exact ⟨rfl, (veblen_inj.1 h1).symm⟩

/-- **The Veblen parts stay at the stage.** -/
theorem rxNsDecV {n : ℕ} {x : Ordinal.{0}} (hx : RxNs S T n x) :
    ∀ a b, veblen a b = x → b < x → RxNs S T n a ∧ RxNs S T n b := by
  induction hx with
  | @small _ x h =>
    intro a b e hb
    exact ⟨RxNs.small ((e ▸ left_le_veblen a b).trans_lt h), RxNs.small (hb.trans h)⟩
  | zero => intro a b e _; exact absurd e veblen_pos.ne'
  | inacc k =>
    intro a b e hb
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_I (S := S) k) e hb
    exact ⟨RxNs.inacc k, RxNs.zero⟩
  | inaccW =>
    intro a b e hb
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_Iw (S := S)) e hb
    exact ⟨RxNs.inaccW, RxNs.zero⟩
  | omn k =>
    intro a b e hb
    rcases eq_or_ne (k : Ordinal.{0}) 0 with h0 | h0
    · rw [h0, Om_zero] at e; exact absurd e veblen_pos.ne'
    · obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_Om h0) e hb
      exact ⟨RxNs.omn k, RxNs.zero⟩
  | @add _ u v hu hv ihu ihv =>
    intro a b e hb
    have hp : IsPrincipal (· + ·) (u + v) := e ▸ Ph.ph_veblen_prin a b
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at e hb
      obtain ⟨h1, h2⟩ := ihu a b e hb
      exact ⟨RxNs.up h1, RxNs.up h2⟩
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hp hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at e hb
      obtain ⟨h1, h2⟩ := ihv a b e hb
      exact ⟨RxNs.up h1, RxNs.up h2⟩
  | @phi _ a' b' ha' hb' _ ihb =>
    intro a b e hb
    rcases veblen_eq_veblen_iff.1 e with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h1, h2]; exact ⟨RxNs.up ha', RxNs.up hb'⟩
    · rw [h2] at hb; exact absurd hb (lt_irrefl _)
    · obtain ⟨h3, h4⟩ := ihb a b h2 (by rw [← h2, e]; exact hb)
      exact ⟨RxNs.up h3, RxNs.up h4⟩
  | @om _ p hp _ =>
    intro a b e hb
    rcases eq_or_ne p 0 with rfl | h0
    · rw [Om_zero] at e; exact absurd e veblen_pos.ne'
    · obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_Om h0) e hb
      exact ⟨RxNs.om hp, RxNs.zero⟩
  | @psiN _ d k hk hd hdn _ =>
    intro a b e hb
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_psi (S := S) (InR_Om_succ (k : Ordinal.{0})) d) e hb
    exact ⟨RxNs.psiN k hk hd hdn, RxNs.zero⟩
  | @psiG _ π d hπ hπ1 hπN hdN hdn _ _ =>
    intro a b e hb
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_psi (S := S) hπ d) e hb
    exact ⟨RxNs.psiG hπ hπ1 hπN hdN hdn, RxNs.zero⟩
  | up _ ih =>
    intro a b e hb
    obtain ⟨h1, h2⟩ := ih a b e hb
    exact ⟨RxNs.up h1, RxNs.up h2⟩

/-- **A strongly critical member above `Ω₁` that is not a cardinal is a collapse at an earlier stage.** -/
theorem rxNsSC (hT1 : T ≤ Om 1) {n : ℕ} {x : Ordinal.{0}} (hx : RxNs S T n x) :
    SC x → Om 1 < x → (∀ σ, x ≠ Om σ) →
      ∃ m < n, ∃ π d, S.InR π ∧ π ≠ Om 1 ∧ RxNs S T m d ∧ d ∈ S.CSet d (S.psi d π) ∧ x = S.psi d π := by
  induction hx with
  | small h => exact fun _ h1 _ => absurd ((h.trans_le hT1).trans h1) (lt_irrefl _)
  | zero => exact fun hS _ _ => absurd hS.1 (lt_irrefl _)
  | inacc k => exact fun _ _ hne => absurd (Om_I k).symm (hne _)
  | inaccW => exact fun _ _ hne => absurd S.Om_Iw.symm (hne _)
  | omn k => exact fun _ _ hne => absurd rfl (hne _)
  | @add n u v _ _ ihu ihv =>
    intro hs h1 hne
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at hs h1 hne ⊢
      obtain ⟨m, hm, h⟩ := ihu hs h1 hne
      exact ⟨m, hm.trans (lt_add_one n), h⟩
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hs.isPrincipal hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at hs h1 hne ⊢
      obtain ⟨m, hm, h⟩ := ihv hs h1 hne
      exact ⟨m, hm.trans (lt_add_one n), h⟩
  | @phi n a b _ _ iha ihb =>
    intro hs h1 hne
    by_cases ha : a < veblen a b
    · by_cases hb : b < veblen a b
      · exact absurd (hs.2 a ha b hb) (lt_irrefl _)
      · have e : b = veblen a b := le_antisymm (right_le_veblen _ _) (not_lt.1 hb)
        rw [← e] at hs h1 hne ⊢
        obtain ⟨m, hm, h⟩ := ihb hs h1 hne
        exact ⟨m, hm.trans (lt_add_one n), h⟩
    · have e : a = veblen a b := le_antisymm (left_le_veblen _ _) (not_lt.1 ha)
      rw [← e] at hs h1 hne ⊢
      obtain ⟨m, hm, h⟩ := iha hs h1 hne
      exact ⟨m, hm.trans (lt_add_one n), h⟩
  | om _ _ => exact fun _ _ hne => absurd rfl (hne _)
  | @psiN n d k hk hd hdn _ =>
    exact fun _ _ _ => ⟨n, lt_add_one n, _, d, InR_Om_succ _, rxNat_ne_one hk, hd, hdn, rfl⟩
  | @psiG n π d hπ hπ1 _ hdN hdn _ _ =>
    exact fun _ _ _ => ⟨n, lt_add_one n, π, d, hπ, hπ1, hdN, hdn, rfl⟩
  | @up n _ _ ih =>
    intro hs h1 hne
    obtain ⟨m, hm, h⟩ := ih hs h1 hne
    exact ⟨m, hm.trans (lt_add_one n), h⟩

open Classical in
/-- **The least stage** of a member (`0` off the hull). -/
noncomputable def rxH (S : InaccSeq.{0}) (T x : Ordinal.{0}) : ℕ :=
  if h : ∃ n, RxNs S T n x then Nat.find h else 0

theorem rxH_spec {x : Ordinal.{0}} (hx : RxN S T x) : RxNs S T (rxH S T x) x := by
  have h := rxN_iff_stage.1 hx
  classical
  rw [rxH, dif_pos h]
  exact Nat.find_spec h

theorem rxH_le {n : ℕ} {x : Ordinal.{0}} (hx : RxNs S T n x) : rxH S T x ≤ n := by
  have h : ∃ n, RxNs S T n x := ⟨n, hx⟩
  classical
  rw [rxH, dif_pos h]
  exact Nat.find_min' h hx

end Googology.Trans.PoR.InaccPsi.R2.Rx
