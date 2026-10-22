import Googology.Trans.PoR.InaccPsi.R2.LdG2b

/-!
# The digits of a collapse: `ψ_κ(a) ≤ Q` from the remainders modulo `ψ_{κ⁺}(0)`

`κ = Ω_{s+1}`, `κ⁺ = Ω_{s+2}`, `G = ψ_{κ⁺}(0)` (the least strongly critical ordinal above `κ`), `Q` strongly critical.
`LeCl κ Q` are the codes over `Q` with the one extra generator `κ` (from the ordinals below `Q` and `κ` by `+` and
`φ = veblen`); for `κ = Ω₁` these are the codes `Mx.GxCl Q ∅`.

* `leMod_add_lt`, `leMod_add_ge`, `leMod_prin` (the remainder modulo `ω^b`), `leModP_mem` (**`Cl(a, b)` is closed
  under `x ↦ x % ω^c`**), `leDiv_div` (`x/(a·b) = (x/a)/b`);
* `LeCl.mod` (**`LeCl κ Q` is closed under `x ↦ x % ω^b`**), `leClDec` (decomposition: `w − x` and `log_ω w`),
  `LeCl.lt_of_lt` (a code below `κ` is below `Q`), `leCl_bound` (**a code below `κ^{m+1}` is below `κ^m·Q`**:
  every digit is below `Q`);
* `lePsi_le` (**`ψ_κ(a) ≤ Q` if `ψ_κ(e) < Q` for every `e < a` whose remainder `e % G` is a code `LeCl κ Q`**:
  every member of `Cl(a, Q)` has such a remainder), `lePsi1_le`, `lePsi2_le` (`κ = Ω₁`, `κ = Ω₂`).

No new axiom.  New definition: `LeCl`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

/-! ## The remainder modulo `ω^b` -/

theorem leMod_add_lt (b x : Ordinal.{0}) {y : Ordinal.{0}} (hy : y < ω ^ b) :
    (x + y) % ω ^ b = x % ω ^ b + y := by
  have hP0 : ω ^ b ≠ 0 := (opow_pos b omega0_pos).ne'
  have hr : x % ω ^ b < ω ^ b := Ordinal.mod_lt x hP0
  have e : x + y = ω ^ b * (x / ω ^ b) + (x % ω ^ b + y) := by
    conv_lhs => rw [← Ordinal.div_add_mod x (ω ^ b)]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (isPrincipal_add_omega0_opow b hr hy)]

theorem leMod_add_ge (b x : Ordinal.{0}) {y : Ordinal.{0}} (hy : ω ^ b ≤ y) :
    (x + y) % ω ^ b = y % ω ^ b := by
  have hP0 : ω ^ b ≠ 0 := (opow_pos b omega0_pos).ne'
  set q := y / ω ^ b with hq
  set r' := y % ω ^ b with hr'
  have hy' : y = ω ^ b * q + r' := (Ordinal.div_add_mod y (ω ^ b)).symm
  have hq0 : q ≠ 0 := by
    intro h0
    have : y < ω ^ b := by
      rw [hy', h0, mul_zero, zero_add]; exact Ordinal.mod_lt y hP0
    exact absurd hy (not_le.2 this)
  have habs : x % ω ^ b + ω ^ b * q = ω ^ b * q :=
    Ordinal.add_of_omega0_opow_le (b := b) (Ordinal.mod_lt x hP0)
      (le_mul_left (ω ^ b) (pos_iff_ne_zero.2 hq0))
  have e : x + y = ω ^ b * (x / ω ^ b + q) + r' := by
    conv_lhs => rw [← Ordinal.div_add_mod x (ω ^ b), hy']
    rw [mul_add, add_assoc (ω ^ b * (x / ω ^ b)), ← add_assoc (x % ω ^ b), habs, add_assoc]
  rw [e, Ordinal.mul_add_mod_self]
  exact Ordinal.mod_eq_of_lt (Ordinal.mod_lt y hP0)

/-- The remainder of an additive principal modulo `ω^b` is itself or `0`. -/
theorem leMod_prin {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (b : Ordinal.{0}) :
    p % ω ^ b = p ∨ p % ω ^ b = 0 := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h0 | ⟨c, hc⟩
  · right; rw [h0, Ordinal.zero_mod]
  · rw [← hc]
    rcases lt_or_ge c b with h | h
    · left; exact Ordinal.mod_eq_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 h)
    · right; exact Ordinal.mod_eq_zero_of_dvd (opow_dvd_opow ω h)

/-- **`Cl(a, b)` is closed under `x ↦ x % ω^c`.** -/
theorem leModP_mem {a b x : Ordinal.{0}} (c : Ordinal.{0}) (hx : x ∈ S.CSet a b) :
    x % ω ^ c ∈ S.CSet a b := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → p ∈ S.CSet a b → p % ω ^ c ∈ S.CSet a b := by
    intro p hp hpC
    rcases leMod_prin hp c with e | e
    · rw [e]; exact hpC
    · rw [e]; exact CSet.zero_mem a b
  induction hx with
  | small h => exact CSet.of_lt ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact CSet.zero_mem a b
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal (CSet.I_mem a b n)
  | inaccW => exact prin (SC_Iw (S := S)).isPrincipal (CSet.Iw_mem a b)
  | @add x y _ hy ihx ihy =>
    rcases lt_or_ge y (ω ^ c) with h | h
    · rw [leMod_add_lt c x h]; exact CSet.add_mem ihx hy
    · rw [leMod_add_ge c x h]; exact ihy
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (CSet.phi_mem hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact CSet.zero_mem a b
    · exact prin (Om_isPrincipal hx0) (CSet.Om_mem hx)
  | @coll π e hπ hπC heC _ _ => exact prin (SC_psi hπ e.1).isPrincipal (CSet.psi_mem e.2 hπ hπC heC)

/-- `x / (a·b) = (x/a)/b`. -/
theorem leDiv_div (x : Ordinal.{0}) {a b : Ordinal.{0}} (ha : a ≠ 0) (hb : b ≠ 0) :
    x / (a * b) = x / a / b := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have e1 : x = a * (x / a) + x % a := (Ordinal.div_add_mod x a).symm
  have e2 : x / a = b * (x / a / b) + x / a % b := (Ordinal.div_add_mod (x / a) b).symm
  have hlow : a * (x / a % b) + x % a < a * b := by
    calc a * (x / a % b) + x % a < a * (x / a % b) + a :=
          (add_lt_add_iff_left _).2 (Ordinal.mod_lt x ha)
      _ = a * (x / a % b + 1) := (mul_add_one _ _).symm
      _ ≤ a * b := mul_le_mul_right (Order.add_one_le_of_lt (Ordinal.mod_lt _ hb)) _
  have e : x = a * b * (x / a / b) + (a * (x / a % b) + x % a) := by
    conv_lhs => rw [e1, e2]
    rw [mul_add, mul_assoc, add_assoc]
  conv_lhs => rw [e]
  rw [Ordinal.mul_add_div _ hab, Ordinal.div_eq_zero_of_lt hlow, add_zero]

/-! ## The codes `LeCl κ Q` -/

/-- **The codes over `Q` with the extra generator `κ`.** -/
inductive LeCl (κ Q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < Q → LeCl κ Q x
  | om : LeCl κ Q κ
  | add {x y : Ordinal.{0}} : LeCl κ Q x → LeCl κ Q y → LeCl κ Q (x + y)
  | phi {x y : Ordinal.{0}} : LeCl κ Q x → LeCl κ Q y → LeCl κ Q (veblen x y)

variable {κ Q : Ordinal.{0}}

theorem LeCl.zero (hQ : 0 < Q) : LeCl κ Q 0 := LeCl.small hQ

theorem LeCl.opow (hQ : 0 < Q) {c : Ordinal.{0}} (h : LeCl κ Q c) : LeCl κ Q (ω ^ c) := by
  have := LeCl.phi (LeCl.zero hQ) h; rwa [veblen_zero_apply] at this

theorem LeCl.natMul (hQ : 0 < Q) : ∀ m : ℕ, LeCl κ Q (κ * (m : Ordinal.{0}))
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact LeCl.zero hQ
  | m + 1 => by rw [Nat.cast_succ, mul_add_one]; exact LeCl.add (LeCl.natMul hQ m) LeCl.om

/-- A code below `κ` is below `Q`. -/
theorem LeCl.lt_of_lt (hQ : SC Q) {x : Ordinal.{0}} (hx : LeCl κ Q x) : x < κ → x < Q := by
  induction hx with
  | small h => exact fun _ => h
  | om => exact fun h => absurd h (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h1 => hQ.isPrincipal (ihx (lt_of_le_of_lt le_self_add h1)) (ihy (lt_of_le_of_lt le_add_self h1))
  | @phi x y _ _ ihx ihy =>
    exact fun h1 => hQ.2 _ (ihx (lt_of_le_of_lt (left_le_veblen x y) h1)) _
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h1))

/-- **`LeCl κ Q` is closed under `x ↦ x % ω^b`** (for an additive principal `κ`). -/
theorem LeCl.mod (hQ : 0 < Q) (hκ : IsPrincipal (· + ·) κ) (b : Ordinal.{0}) {x : Ordinal.{0}}
    (hx : LeCl κ Q x) : LeCl κ Q (x % ω ^ b) := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → LeCl κ Q p → LeCl κ Q (p % ω ^ b) := by
    intro p hp h
    rcases leMod_prin hp b with e | e
    · rw [e]; exact h
    · rw [e]; exact LeCl.zero hQ
  induction hx with
  | small h => exact LeCl.small ((Ordinal.mod_le _ _).trans_lt h)
  | om => exact prin hκ LeCl.om
  | @add x y _ hy ihx ihy =>
    rcases lt_or_ge y (ω ^ b) with h | h
    · rw [leMod_add_lt b x h]; exact LeCl.add ihx hy
    · rw [leMod_add_ge b x h]; exact ihy
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (LeCl.phi hx hy)

/-- **Decomposition**: a code `w` has `w − x` (for every code `x ≤ w`) and `log_ω w` codes. -/
theorem leClDec (hQ : SC Q) (hκ : SC κ) : ∀ w, LeCl κ Q w →
    (∀ x, LeCl κ Q x → x ≤ w → LeCl κ Q (w - x)) ∧ LeCl κ Q (log ω w) := by
  have h0 : LeCl κ Q 0 := LeCl.zero hQ.1
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, LeCl κ Q v → v ≤ w →
      (∀ x, LeCl κ Q x → x ≤ v → LeCl κ Q (v - x)) ∧ LeCl κ Q (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => LeCl.small ((Ordinal.sub_le_self v x).trans_lt h),
      LeCl.small ((log_le_self ω v).trans_lt h)⟩
  | om =>
    intro _
    have hE : ω ^ κ = κ := gg_SC_eps hκ
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases gg_sub_prin hκ.isPrincipal hx with e | e <;> rw [e]
      · exact LeCl.om
      · exact h0
    · have : log ω κ = κ := by
        conv_lhs => rw [← hE]
        exact log_opow one_lt_omega0 _
      rw [this]; exact LeCl.om
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact LeCl.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : LeCl κ Q (x - u) := (IHo x hxw hx).1 u hu hux.le
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
        · exact LeCl.opow hQ.1 hb
        · exact h0
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := gg_veblen_eps (y := b) ha0
      have hp : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin hp hx with e | e <;> rw [e]
        · exact LeCl.phi ha hb
        · exact h0
      · have : log ω (veblen a b) = veblen a b := by
          conv_lhs => rw [← hE]
          exact log_opow one_lt_omega0 _
        rw [this]; exact LeCl.phi ha hb

/-- **Every digit of a code is below `Q`**: a code below `κ^{m+1} = ω^{κ·(m+1)}` is below `κ^m·Q`. -/
theorem leCl_bound (hQ : SC Q) (hκ : SC κ) (m : ℕ) :
    ∀ x, LeCl κ Q x → x < ω ^ (κ * ((m + 1 : ℕ) : Ordinal.{0})) → x < ω ^ (κ * (m : Ordinal.{0})) * Q := by
  have eQ : ω ^ (κ * (m : Ordinal.{0})) * Q = ω ^ (κ * (m : Ordinal.{0}) + Q) := by
    rw [opow_add, gg_SC_eps hQ]
  have hpr : IsPrincipal (· + ·) (ω ^ (κ * (m : Ordinal.{0})) * Q) := by
    rw [eQ]; exact isPrincipal_add_omega0_opow _
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hxlt : x < ω ^ a * ω := by
    rw [← opow_succ]; exact lt_opow_succ_log_self one_lt_omega0 x
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hrx : x - ω ^ a < x := by
    refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
    have h' : ω ^ a + x = x := by
      calc ω ^ a + x = ω ^ a + (x - ω ^ a) := by rw [e]
        _ = x := hdec
    have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
    exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
  have hr := IH _ hrx (hsub _ (LeCl.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < κ * ((m + 1 : ℕ) : Ordinal.{0}) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < ω ^ (κ * (m : Ordinal.{0})) * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a (κ * (m : Ordinal.{0})) with h | h
    · exact h.trans_le le_self_add
    · have hc : LeCl κ Q (a - κ * (m : Ordinal.{0})) := (leClDec hQ hκ a hlog).1 _ (LeCl.natMul hQ.1 m) h
      have hdec' : κ * (m : Ordinal.{0}) + (a - κ * (m : Ordinal.{0})) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - κ * (m : Ordinal.{0}) < κ := by
        have : κ * (m : Ordinal.{0}) + (a - κ * (m : Ordinal.{0})) < κ * (m : Ordinal.{0}) + κ := by
          rw [hdec', ← mul_add_one, ← Nat.cast_succ]; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (LeCl.lt_of_lt hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

/-! ## The bound for `ψ_κ` -/

/-- **`ψ_κ(a) ≤ Q`** (`κ = Ω_{s+1}`) for a strongly critical `Q` above `Ω_s`, if `ψ_κ(e) < Q` for every `e < a` whose
remainder modulo `G = ψ_{Ω_{s+2}}(0)` is a code `LeCl κ Q`. -/
theorem lePsi_le {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1 + 1) < S.I n)
    (hcoll : ∀ e, e < a → LeCl (Om (s + 1)) Q (e % S.psi 0 (Om (s + 1 + 1))) →
      S.psi e (Om (s + 1)) < Q) :
    S.psi a (Om (s + 1)) ≤ Q := by
  set κ := Om (s + 1) with hκ_def
  set G := S.psi 0 (Om (s + 1 + 1)) with hG_def
  have hs1 : s + 1 ≠ 0 := by
    exact (add_pos_of_right zero_lt_one s).ne'
  have hκSC : SC κ := SC_Om hs1
  have hGSC : SC G := SC_psi (InR_Om_succ (s + 1)) 0
  have hκG : κ < G := (psiS_bounds (S := S) 0 (s + 1)).1
  have hG2 : G < Om (s + 1 + 1) := psi_lt (InR_Om_succ (s + 1)) 0
  have hQ0 : 0 < Q := hQ.1
  -- a principal `p`
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < G → LeCl κ Q p) → LeCl κ Q (p % G) := by
    intro p hp h
    rcases ldModK_prin hGSC hp with ⟨hpG, e⟩ | e
    · rw [e]; exact h hpG
    · rw [e]; exact LeCl.zero hQ0
  have hIG : ∀ n, G < S.I n := fun n => hG2.trans (hI n)
  have key : ∀ x ∈ S.CSet a Q, LeCl κ Q (x % G) := by
    intro x hx
    induction hx with
    | small h => exact LeCl.small ((Ordinal.mod_le _ _).trans_lt h)
    | zero => rw [Ordinal.zero_mod]; exact LeCl.zero hQ0
    | inacc n => exact prin (SC_I (S := S) n).isPrincipal fun h => absurd (h.trans (hIG n)) (lt_irrefl _)
    | inaccW =>
      exact prin (SC_Iw (S := S)).isPrincipal fun h =>
        absurd (h.trans ((hIG 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0))) (lt_irrefl _)
    | @add x y _ _ ihx ihy =>
      rcases lt_or_ge y G with hy | hy
      · rw [ldModK_add_lt hGSC x hy]
        have hy' : LeCl κ Q y := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
        exact LeCl.add ihx hy'
      · rw [ldModK_add_ge hGSC x hy]; exact ihy
    | @phi x y _ _ ihx ihy =>
      refine prin (Ph.ph_veblen_prin x y) fun h => ?_
      have hx1 : x < G := lt_of_le_of_lt (left_le_veblen x y) h
      have hy1 : y < G := lt_of_le_of_lt (right_le_veblen x y) h
      rw [Ordinal.mod_eq_of_lt hx1] at ihx
      rw [Ordinal.mod_eq_of_lt hy1] at ihy
      exact LeCl.phi ihx ihy
    | @om x _ _ =>
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [Om_zero, Ordinal.zero_mod]; exact LeCl.zero hQ0
      refine prin (Om_isPrincipal hx0) fun h => ?_
      rcases lt_trichotomy x (s + 1) with hx | hx | hx
      · refine LeCl.small (lt_of_le_of_lt (Om_le_Om.2 ?_) hsQ)
        rw [← Order.succ_eq_add_one] at hx; exact Order.lt_succ_iff.1 hx
      · rw [hx]; exact LeCl.om
      · exfalso
        have h2 : s + 1 + 1 ≤ x := by
          rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hx
        exact absurd (h.trans hG2) (not_lt.2 (Om_le_Om.2 h2))
    | @coll π e hπ _ _ _ ihe =>
      refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
      rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
      · exfalso
        have h2 : Om (s + 1 + 1) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (hsC _ _)))) (hI n)
        exact absurd ((h2.trans h).trans hG2) (lt_irrefl _)
      rcases lt_trichotomy t s with hts | hts | hts
      · refine LeCl.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hsQ.le))
        exact Order.add_one_le_of_lt hts
      · subst hts; exact LeCl.small (hcoll e.1 e.2 ihe)
      · exfalso
        rcases (Order.add_one_le_of_lt hts).lt_or_eq with h3 | h3
        · have h4 : Om (s + 1 + 1) < S.psi e.1 (Om (t + 1)) :=
            (Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt h3)
          exact absurd ((h4.trans h).trans hG2) (lt_irrefl _)
        · subst h3
          have h4 : G ≤ S.psi e.1 (Om (s + 1 + 1)) := (psi_mono (S := S) (InR_Om_succ (s + 1)) zero_le).1
          exact absurd (h4.trans_lt h) (lt_irrefl _)
  refine psi_le_of_good (CSet.Om_mem (CSet.succ_mem (hsC _ _))) fun x hx hxκ => ?_
  have := key x hx
  rw [Ordinal.mod_eq_of_lt (hxκ.trans hκG)] at this
  exact LeCl.lt_of_lt hQ this hxκ

theorem leOm3_lt_I (n : ℕ) : Om (1 + 1 + 1 : Ordinal.{0}) < S.I n := by
  have h3 : (1 + 1 + 1 : Ordinal.{0}) < S.I n := by
    have hω : (1 + 1 + 1 : Ordinal.{0}) < ω := by
      have : (1 + 1 + 1 : Ordinal.{0}) = ((3 : ℕ) : Ordinal.{0}) := by norm_num
      rw [this]; exact natCast_lt_omega0 3
    refine hω.trans_le (le_trans (omega0_le_omega 1) ?_)
    have := Low.Om_one_le_I (S := S) n
    rwa [Om_of_ne_zero one_ne_zero] at this
  have h : Om (1 + 1 + 1 : Ordinal.{0}) < Om (S.I n) := Om_lt_Om.2 h3
  rwa [S.fix n] at h

/-- **`ψ_{Ω₁}(a) ≤ T`** for a countable strongly critical `T`, if `ψ_{Ω₁}(e) < T` for every `e < a` whose remainder
modulo `Γ_{Ω₁+1} = ψ_{Ω₂}(0)` is a code `LeCl Ω₁ T`. -/
theorem lePsi1_le {a T : Ordinal.{0}} (hT : SC T)
    (hcoll : ∀ e, e < a → LeCl (Om 1) T (e % S.psi 0 (Om (1 + 1))) → S.psi e (Om 1) < T) :
    S.psi a (Om 1) ≤ T := by
  have h := lePsi_le (S := S) (s := 0) (a := a) hT (by rw [Om_zero]; exact hT.1)
    (fun a b => CSet.zero_mem a b) (fun n => by rw [zero_add]; exact mxOm2_lt_I n)
    (fun e he hc => by rw [zero_add] at hc ⊢; exact hcoll e he hc)
  rwa [zero_add] at h

/-- **`ψ_{Ω₂}(a) ≤ Q`** for a strongly critical `Q > Ω₁`, if `ψ_{Ω₂}(e) < Q` for every `e < a` whose remainder
modulo `ψ_{Ω₃}(0)` is a code `LeCl Ω₂ Q`. -/
theorem lePsi2_le {a Q : Ordinal.{0}} (hQ : SC Q) (hΩQ : Om 1 < Q)
    (hcoll : ∀ e, e < a → LeCl (Om (1 + 1)) Q (e % S.psi 0 (Om (1 + 1 + 1))) → S.psi e (Om (1 + 1)) < Q) :
    S.psi a (Om (1 + 1)) ≤ Q :=
  lePsi_le (S := S) (s := 1) hQ hΩQ (fun a b => CSet.one_mem a b) leOm3_lt_I hcoll

end Googology.Trans.PoR.InaccPsi.R2.Le
