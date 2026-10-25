import Googology.Trans.PoR.InaccPsi.R2.UiUB

/-!
# The visibility closure `K_q` at the threshold `W = Ω_{s+1}`, for every ordinal (parameters included)

`W = Ω_{s+1}`, `L = Ω_s`, `ψ_π = S.psi · π`.  The levels of the hierarchy one cardinal up from `L` are arbitrary
ordinals `γ` (above `ε_{W+1}` their components are atoms `ψ_{Ω_{s+2}}(e)`), and a level is *visible* at a strongly
critical `v ∈ (L, W]` when it is built from leaves below `v` by every operation of the notation except `ψ_W` (the
collapse at the threshold, whose values `≥ v` are invisible at `v`):

* `UlK S s q` (**the closure of `q ∪ {0, I_n, I_ω}` under `+`, `φ`, `Ω_·` and every `ψ_π`, `π ≠ W`**, any argument),
  `UlK.mono`, `UlK.opow`, `UlK.one`, `UlK.nat`, `UlK.mul_nat`, `ulK_W`;
* `ulK_lt_W` (**`K_q ∩ W ⊆ q`** for a strongly critical `q > L`), `ulK_hull` (**`Cl(a, q) ⊆ K_q`** once the
  collapses `ψ_W(e)`, `e < a`, of members of `K_q` are below `q`), `ulK_supp` (finite support);
* `ulD` (**the visibility datum**: the least `m` with the level in `K_{m+1}`), `ul_vis` (**`ulD j < q ↔ j ∈ K_q`**
  for a strongly critical `q`);
* the arithmetic of `K_q` (no bound on the ordinals): `ulK_dec` (**`w − x` and `log_ω w`**), `ulK_mod` (**`x % ω^f`**,
  any `f`), `ulK_div` (**`x / ω^f`** for `f ∈ K_q`), `ulK_opow_mul` (**`ω^a·b`**), `ulK_dig` (**every base-`W` digit
  of `x ∈ K_q` is in `K_q`, and the exponent of a nonzero digit is in `K_q`**), `ulK_modW`.

No new axiom.  New definitions: `UlK`, `ulD`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ul

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

/-- **The visibility closure at the threshold `W = Ω_{s+1}`**: leaves below `q`, and every operation of the notation
except the collapse `ψ_W` (arguments unbounded). -/
inductive UlK (S : InaccSeq.{0}) (s q : Ordinal.{0}) : Ordinal.{0} → Prop
  | small {x : Ordinal.{0}} : x < q → UlK S s q x
  | zero : UlK S s q 0
  | inacc (n : ℕ) : UlK S s q (S.I n)
  | inaccW : UlK S s q S.Iw
  | add {x y : Ordinal.{0}} : UlK S s q x → UlK S s q y → UlK S s q (x + y)
  | phi {x y : Ordinal.{0}} : UlK S s q x → UlK S s q y → UlK S s q (veblen x y)
  | om {x : Ordinal.{0}} : UlK S s q x → UlK S s q (Om x)
  | coll {π e : Ordinal.{0}} : S.InR π → π ≠ Om (s + 1) → UlK S s q π → UlK S s q e →
      UlK S s q (S.psi e π)

variable {S : InaccSeq.{0}} {s q : Ordinal.{0}}

theorem UlK.mono {q' : Ordinal.{0}} (h : q ≤ q') {x : Ordinal.{0}} (hx : UlK S s q x) : UlK S s q' x := by
  induction hx with
  | small h' => exact UlK.small (h'.trans_le h)
  | zero => exact UlK.zero
  | inacc n => exact UlK.inacc n
  | inaccW => exact UlK.inaccW
  | add _ _ ihx ihy => exact UlK.add ihx ihy
  | phi _ _ ihx ihy => exact UlK.phi ihx ihy
  | om _ ih => exact UlK.om ih
  | coll hπ hπW _ _ ihπ ihe => exact UlK.coll hπ hπW ihπ ihe

theorem UlK.opow {x : Ordinal.{0}} (h : UlK S s q x) : UlK S s q (ω ^ x) := by
  have := UlK.phi UlK.zero h; rwa [veblen_zero_apply] at this

theorem UlK.one : UlK S s q 1 := by
  have := UlK.opow (S := S) (s := s) (q := q) UlK.zero; rwa [opow_zero] at this

theorem UlK.nat : ∀ n : ℕ, UlK S s q (n : Ordinal.{0})
  | 0 => by rw [Nat.cast_zero]; exact UlK.zero
  | n + 1 => by rw [Nat.cast_succ]; exact UlK.add (UlK.nat n) UlK.one

theorem UlK.mul_nat {x : Ordinal.{0}} (h : UlK S s q x) : ∀ n : ℕ, UlK S s q (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact UlK.zero
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact UlK.add (UlK.mul_nat h n) h

/-- `W = Ω_{s+1}` is in every `K_q`. -/
theorem ulK_W (hs : s < ω) : UlK S s q (Om (s + 1)) := by
  obtain ⟨n, rfl⟩ := lt_omega0.1 hs
  have h : UlK S (n : Ordinal.{0}) q ((n : Ordinal.{0}) + 1) := by
    have := UlK.nat (S := S) (s := (n : Ordinal.{0})) (q := q) (n + 1); rwa [Nat.cast_succ] at this
  exact UlK.om h

/-! ## `K_q ∩ W ⊆ q`, the hull lemma, finite support -/

/-- **`K_q ∩ W ⊆ q`** for a strongly critical `q > L`. -/
theorem ulK_lt_W (hs : s < ω) (hq : SC q) (hLq : Om s < q) {x : Ordinal.{0}} (hx : UlK S s q x) :
    x < Om (s + 1) → x < q := by
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => hq.1
  | inacc n => exact fun h => absurd (Ui.ui_W_lt_I (S := S) hs n) (not_lt.2 h.le)
  | inaccW => exact fun h => absurd (Ui.ui_W_lt_Iw (S := S) hs) (not_lt.2 h.le)
  | @add x y _ _ ihx ihy =>
    intro h
    exact (Lq.lq_SC_indec hq).add_lt (ihx (le_self_add.trans_lt h)) (ihy (le_add_self.trans_lt h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact hq.2 x (ihx ((left_le_veblen x y).trans_lt h)) y (ihy ((right_le_veblen x y).trans_lt h))
  | @om x _ _ =>
    intro h
    have hx : x < s + 1 := Om_lt_Om.1 h
    exact (Om_le_Om.2 (Order.lt_add_one_iff.1 hx)).trans_lt hLq
  | @coll π e hπ hπW _ _ _ _ =>
    intro h
    rcases Ui.ui_psi_cases (S := S) (e := e) hs hπ hπW with h' | h'
    · exact h'.trans hLq
    · exact absurd h (not_lt.2 h')

/-- **The hull lemma**: `Cl(a, q) ⊆ K_q` once every collapse `ψ_W(e)`, `e < a`, of a member `e ∈ K_q` is below `q`. -/
theorem ulK_hull {a : Ordinal.{0}}
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → UlK S s q e → S.psi e (Om (s + 1)) < q) :
    ∀ x, x ∈ S.CSet a q → UlK S s q x := by
  intro x hx
  induction hx with
  | small h => exact UlK.small h
  | zero => exact UlK.zero
  | inacc n => exact UlK.inacc n
  | inaccW => exact UlK.inaccW
  | add _ _ ihx ihy => exact UlK.add ihx ihy
  | phi _ _ ihx ihy => exact UlK.phi ihx ihy
  | om _ ih => exact UlK.om ih
  | @coll π e hπ _ heC ihπ ihe =>
    show UlK S s q (S.psi e.1 π)
    by_cases hπW : π = Om (s + 1)
    · subst hπW; exact UlK.small (hcoll e.1 e.2 heC ihe)
    · exact UlK.coll hπ hπW ihπ ihe

/-- **Finite support**: a member of `K_q` (`q` strongly critical) lies in `K_{m+1}` for some `m < q`. -/
theorem ulK_supp (hq : SC q) {x : Ordinal.{0}} (hx : UlK S s q x) : ∃ m, m < q ∧ UlK S s (m + 1) x := by
  have hle : ∀ a b : Ordinal.{0}, a + 1 ≤ max a b + 1 := fun a b =>
    Order.add_one_le_of_lt ((le_max_left a b).trans_lt (lt_add_one _))
  have hre : ∀ a b : Ordinal.{0}, b + 1 ≤ max a b + 1 := fun a b =>
    Order.add_one_le_of_lt ((le_max_right a b).trans_lt (lt_add_one _))
  induction hx with
  | @small x h => exact ⟨x, h, UlK.small (lt_add_one x)⟩
  | zero => exact ⟨0, hq.1, UlK.zero⟩
  | inacc n => exact ⟨0, hq.1, UlK.inacc n⟩
  | inaccW => exact ⟨0, hq.1, UlK.inaccW⟩
  | add _ _ ihx ihy =>
    obtain ⟨m1, h1, k1⟩ := ihx
    obtain ⟨m2, h2, k2⟩ := ihy
    exact ⟨max m1 m2, max_lt h1 h2, UlK.add (k1.mono (hle m1 m2)) (k2.mono (hre m1 m2))⟩
  | phi _ _ ihx ihy =>
    obtain ⟨m1, h1, k1⟩ := ihx
    obtain ⟨m2, h2, k2⟩ := ihy
    exact ⟨max m1 m2, max_lt h1 h2, UlK.phi (k1.mono (hle m1 m2)) (k2.mono (hre m1 m2))⟩
  | om _ ih =>
    obtain ⟨m, h, k⟩ := ih
    exact ⟨m, h, UlK.om k⟩
  | coll hπ hπW _ _ ihπ ihe =>
    obtain ⟨m1, h1, k1⟩ := ihπ
    obtain ⟨m2, h2, k2⟩ := ihe
    exact ⟨max m1 m2, max_lt h1 h2, UlK.coll hπ hπW (k1.mono (hle m1 m2)) (k2.mono (hre m1 m2))⟩

/-! ## The visibility datum -/

/-- **The visibility datum of a level `j`**: the least `m` with `j ∈ K_{m+1}`. -/
noncomputable def ulD (S : InaccSeq.{0}) (s j : Ordinal.{0}) : Ordinal.{0} := sInf {m | UlK S s (m + 1) j}

theorem ulD_spec (j : Ordinal.{0}) : UlK S s (ulD S s j + 1) j :=
  csInf_mem (⟨j, UlK.small (lt_add_one j)⟩ : Set.Nonempty {m | UlK S s (m + 1) j})

theorem ulD_le {j m : Ordinal.{0}} (h : UlK S s (m + 1) j) : ulD S s j ≤ m := csInf_le' h

theorem ulD_le_self (j : Ordinal.{0}) : ulD S s j ≤ j := ulD_le (UlK.small (lt_add_one j))

/-- **`ulD j < q ↔ j ∈ K_q`** for a strongly critical `q`. -/
theorem ul_vis (hq : SC q) {j : Ordinal.{0}} : ulD S s j < q ↔ UlK S s q j :=
  ⟨fun h => (ulD_spec j).mono (Order.add_one_le_of_lt h), fun h => by
    obtain ⟨m, hm, hk⟩ := ulK_supp hq h
    exact (ulD_le hk).trans_lt hm⟩

/-! ## Arithmetic -/

/-- **Decomposition**: for `w ∈ K_q`, `w − x ∈ K_q` (every `x ∈ K_q`, `x ≤ w`) and `log_ω w ∈ K_q`. -/
theorem ulK_dec (hq : SC q) : ∀ w, UlK S s q w →
    (∀ x, UlK S s q x → x ≤ w → UlK S s q (w - x)) ∧ UlK S s q (log ω w) := by
  have hprin : ∀ p, UlK S s q p → IsPrincipal (· + ·) p → ω ^ p = p →
      (∀ x, UlK S s q x → x ≤ p → UlK S s q (p - x)) ∧ UlK S s q (log ω p) := fun p hp hP hE => by
    refine ⟨fun x _ hx => ?_, ?_⟩
    · rcases Gg.gg_sub_prin hP hx with e | e <;> rw [e]
      · exact hp
      · exact UlK.zero
    · have : log ω p = p := by
        conv_lhs => rw [← hE]
        exact log_opow one_lt_omega0 _
      rw [this]; exact hp
  have hzero : (∀ x, UlK S s q x → x ≤ 0 → UlK S s q (0 - x)) ∧ UlK S s q (log ω 0) :=
    ⟨fun x _ _ => UlK.small ((Ordinal.sub_le_self 0 x).trans_lt hq.1),
      UlK.small ((log_le_self ω 0).trans_lt hq.1)⟩
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, UlK S s q v → v ≤ w →
      (∀ x, UlK S s q x → x ≤ v → UlK S s q (v - x)) ∧ UlK S s q (log ω v) from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => UlK.small ((Ordinal.sub_le_self v x).trans_lt h),
      UlK.small ((log_le_self ω v).trans_lt h)⟩
  | zero => intro _; exact hzero
  | inacc n =>
    intro _; exact hprin _ (UlK.inacc n) (SC_I n).isPrincipal (Low.opow_eq_self_of_SC (SC_I n))
  | inaccW => intro _; exact hprin _ UlK.inaccW SC_Iw.isPrincipal (Low.opow_eq_self_of_SC SC_Iw)
  | @om x hx _ =>
    intro _
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hzero
    · exact hprin _ (UlK.om hx) (SC_Om hx0).isPrincipal (Low.opow_eq_self_of_SC (SC_Om hx0))
  | @coll π e hπ hπW hπK heK _ _ =>
    intro _
    exact hprin _ (UlK.coll hπ hπW hπK heK) (SC_psi hπ e).isPrincipal
      (Low.opow_eq_self_of_SC (SC_psi hπ e))
  | @phi a b ha hb _ _ =>
    intro _
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply]
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases Gg.gg_sub_prin (isPrincipal_add_omega0_opow b) hx with e | e <;> rw [e]
        · exact UlK.opow hb
        · exact UlK.zero
      · rw [log_opow one_lt_omega0]; exact hb
    · have hE := Gg.gg_veblen_eps (y := b) ha0
      have hP : IsPrincipal (· + ·) (veblen a b) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      exact hprin _ (UlK.phi ha hb) hP hE
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact UlK.add (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : UlK S s q (x - u) := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact UlK.zero
    · rcases Gg.ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2

/-- The Cantor split `x = ω^g·k + r` of a member of `K_q`: `g = log_ω x`, `ω^g·k`, `r` in `K_q`. -/
theorem ulK_split (hq : SC q) {x : Ordinal.{0}} (hx : UlK S s q x) (hx0 : x ≠ 0) :
    ∃ k : ℕ, ω ^ log ω x * k + x % ω ^ log ω x = x ∧ UlK S s q (log ω x) ∧
      UlK S s q (x % ω ^ log ω x) ∧ x % ω ^ log ω x < x := by
  obtain ⟨hsub, hlog⟩ := ulK_dec hq x hx
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdec : ω ^ log ω x * k + x % ω ^ log ω x = x := by
    have := Ordinal.div_add_mod x (ω ^ log ω x); rwa [hk] at this
  have hwk : UlK S s q (ω ^ log ω x * k) := (UlK.opow hlog).mul_nat k
  have hr : UlK S s q (x % ω ^ log ω x) := by
    have e : x - ω ^ log ω x * k = x % ω ^ log ω x := by
      nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
    have hle : ω ^ log ω x * k ≤ x := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    rw [← e]; exact hsub _ hwk hle
  exact ⟨k, hdec, hlog, hr, mod_opow_log_lt_self _ hx0⟩

/-- **`x % ω^f ∈ K_q`** for `x ∈ K_q` and every `f`. -/
theorem ulK_mod (hq : SC q) : ∀ x, UlK S s q x → ∀ f : Ordinal.{0}, UlK S s q (x % ω ^ f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx f
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.mod_eq_of_lt (opow_pos f omega0_pos)]; exact UlK.zero
  obtain ⟨k, hdec, _, hr, hrx⟩ := ulK_split hq hx hx0
  rcases lt_or_ge (log ω x) f with hgf | hfg
  · have hxf : x < ω ^ f := (lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgf))
    rw [Ordinal.mod_eq_of_lt hxf]; exact hx
  · obtain ⟨c, hc⟩ : ω ^ f ∣ ω ^ log ω x * k := (opow_dvd_opow _ hfg).trans (dvd_mul_right _ _)
    have e : x % ω ^ f = x % ω ^ log ω x % ω ^ f := by
      conv_lhs => rw [← hdec, hc, Ordinal.mul_add_mod_self]
    rw [e]; exact IH _ hrx hr f

/-- **`x / ω^f ∈ K_q`** for `x, f ∈ K_q`. -/
theorem ulK_div (hq : SC q) : ∀ x, UlK S s q x → ∀ f : Ordinal.{0}, UlK S s q f → UlK S s q (x / ω ^ f) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx f hf
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.div_eq_zero_of_lt (opow_pos f omega0_pos)]; exact UlK.zero
  obtain ⟨k, hdec, hlog, hr, hrx⟩ := ulK_split hq hx hx0
  rcases lt_or_ge (log ω x) f with hgf | hfg
  · have hxf : x < ω ^ f := (lt_opow_succ_log_self one_lt_omega0 x).trans_le
      (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hgf))
    rw [Ordinal.div_eq_zero_of_lt hxf]; exact UlK.zero
  · have hgf' : f + (log ω x - f) = log ω x := Ordinal.add_sub_cancel_of_le hfg
    have e : x = ω ^ f * (ω ^ (log ω x - f) * k) + x % ω ^ log ω x := by
      conv_lhs => rw [← hdec]
      rw [← mul_assoc, ← opow_add, hgf']
    have hdiv : x / ω ^ f = ω ^ (log ω x - f) * k + x % ω ^ log ω x / ω ^ f := by
      conv_lhs => rw [e]
      exact Ordinal.mul_add_div _ (opow_pos f omega0_pos).ne' _
    rw [hdiv]
    exact UlK.add ((UlK.opow ((ulK_dec hq _ hlog).1 f hf hfg)).mul_nat k) (IH _ hrx hr f hf)

/-- **`ω^a·b ∈ K_q`** for `a, b ∈ K_q`. -/
theorem ulK_opow_mul (hq : SC q) {a : Ordinal.{0}} (ha : UlK S s q a) :
    ∀ b, UlK S s q b → UlK S s q (ω ^ a * b) := by
  intro b
  induction b using WellFoundedLT.induction with
  | ind b IH =>
  intro hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [mul_zero]; exact UlK.zero
  obtain ⟨k, hdec, hlog, hr, hrx⟩ := ulK_split hq hb hb0
  have e : ω ^ a * b = ω ^ (a + log ω b) * k + ω ^ a * (b % ω ^ log ω b) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, ← opow_add]
  rw [e]
  exact UlK.add ((UlK.opow (UlK.add ha hlog)).mul_nat k) (IH _ hrx hr)

/-- **`x % W^j ∈ K_q`** for `x ∈ K_q` and every `j`. -/
theorem ulK_modW (hq : SC q) {x : Ordinal.{0}} (hx : UlK S s q x) (j : Ordinal.{0}) :
    UlK S s q (x % Om (s + 1) ^ j) := by
  rw [Ui.ui_W_eq s]; exact ulK_mod hq x hx _

/-- **The base-`W` digits**: for `x ∈ K_q` every digit `x / W^j % W` is in `K_q`, and the exponent `j` of a nonzero
digit is in `K_q`. -/
theorem ulK_dig (hs : s < ω) (hq : SC q) {x : Ordinal.{0}} (hx : UlK S s q x) (j : Ordinal.{0}) :
    UlK S s q (x / Om (s + 1) ^ j % Om (s + 1)) ∧
      (x / Om (s + 1) ^ j % Om (s + 1) ≠ 0 → UlK S s q j) := by
  have hW0 : (Om (s + 1) : Ordinal.{0}) ≠ 0 := (Ui.ui_SC_W s).1.ne'
  have hWj0 : Om (s + 1) ^ j ≠ 0 := (Ui.ui_W_pos s j).ne'
  set y := x % Om (s + 1) ^ (j + 1) with hydef
  have hy : UlK S s q y := ulK_modW hq hx (j + 1)
  have hylt : y < Om (s + 1) ^ j * Om (s + 1) := by
    rw [← Ui.ui_W_succ s]; exact Ordinal.mod_lt _ (Ui.ui_W_pos s _).ne'
  have hyd : y / Om (s + 1) ^ j < Om (s + 1) := (Ordinal.lt_mul_iff_div_lt hWj0).1 hylt
  have hid : x / Om (s + 1) ^ j % Om (s + 1) = y / Om (s + 1) ^ j := by
    have e1 : x = Om (s + 1) ^ j * (Om (s + 1) * (x / Om (s + 1) ^ (j + 1))) + y := by
      rw [← mul_assoc, ← Ui.ui_W_succ s, hydef, Ordinal.div_add_mod]
    have e2 : x / Om (s + 1) ^ j = Om (s + 1) * (x / Om (s + 1) ^ (j + 1)) + y / Om (s + 1) ^ j := by
      conv_lhs => rw [e1]
      exact Ordinal.mul_add_div _ hWj0 _
    rw [e2, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyd]
  rw [hid]
  by_cases hd : y / Om (s + 1) ^ j = 0
  · rw [hd]; exact ⟨UlK.zero, fun h => absurd rfl h⟩
  have hjy : Om (s + 1) ^ j ≤ y := by
    by_contra h; exact hd (Ordinal.div_eq_zero_of_lt (not_le.1 h))
  have hlog := (ulK_dec hq y hy).2
  have h1 : Om (s + 1) * j ≤ log ω y :=
    le_log_of_opow_le one_lt_omega0 (by rw [← Ui.ui_W_eq s]; exact hjy)
  have h2 : log ω y < Om (s + 1) * (j + 1) := by
    by_contra h
    have hc : Om (s + 1) * (j + 1) ≠ 0 := (mul_pos (Ui.ui_SC_W s).1 (lt_add_one_iff.2 zero_le)).ne'
    have := opow_le_of_le_log hc (not_lt.1 h)
    rw [← Ui.ui_W_eq s, Ui.ui_W_succ s] at this
    exact absurd hylt (not_lt.2 this)
  have hgj : log ω y / Om (s + 1) = j := by
    apply le_antisymm
    · have := (Ordinal.lt_mul_iff_div_lt hW0).1 h2
      exact Order.lt_add_one_iff.1 this
    · exact (Ordinal.mul_le_iff_le_div hW0).1 h1
  have hjK : UlK S s q j := by
    have := ulK_div hq _ hlog _ (ulK_W (S := S) (q := q) hs)
    rwa [Ui.ui_W_opow s, hgj] at this
  have hWj : UlK S s q (Om (s + 1) * j) := by
    have := ulK_opow_mul hq (ulK_W (S := S) (q := q) hs) j hjK
    rwa [Ui.ui_W_opow s] at this
  refine ⟨?_, fun _ => hjK⟩
  have := ulK_div hq y hy _ hWj
  rwa [← Ui.ui_W_eq s] at this

end Googology.Trans.PoR.InaccPsi.R2.Ul
