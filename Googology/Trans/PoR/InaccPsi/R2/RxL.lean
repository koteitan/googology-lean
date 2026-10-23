import Googology.Trans.PoR.InaccPsi.R2.RxStg

/-!
# The level shift at every finite level

`RxN S T` the normal hull over `T`, `RxNs` its stages, `rxH` the least stage (`Rx.RxStg`), `θ = ψ_{Ω₂}(Ω_ω)`,
`Λ = S.Lam`, `ruInv` the inverse reading (`Ru.ruInv`).

* `rxCDec`, `rxCDecV` (**`Cl(a, b)` is closed under `w ↦ w − x`, `log_ω` and the Veblen parts**);
* `RxE S T x` (**the domain**): `x ∈ RxN S T`, `x ∈ Cl(Ω_ω, θ)`, `x < Ω_ω`; `rxE_log`, `rxE_rem`, `rxE_veb`
  (the parts of a member are members at the same or an earlier stage), `rxE_atom` (**a strongly critical member
  above `Ω₁` that is not a cardinal is `ψ_{Ω_{k+1}}(d)`, `1 ≤ k < ω`, with a normal argument `d` of the domain
  at an earlier stage**), `rxE_card` (the cardinals of the domain are the finite `Ω_k`);
* `rxDn S π s` (**the normal argument** at the subscript `π`: the `d ∈ Cl(d, ψ_π(d))` with `ψ_π(d) = s`; unique,
  `rxDn_eq`);
* `rxMs S T x = Λ·rxH(x) + x` (**the measure**), `rxMs_lt_stage`, `rxMs_lt_val`;
* `rxL S Z At T` (**the level shift**): `ruInv` below `Ω₁`, `Ω_k ↦ Ω_{k+1}`, `ψ_{Ω_{k+1}}(d) ↦ ψ_{Ω_{k+2}}(κ d)` at a
  normal argument `d` (`1 ≤ k < ω`), and `κ` commutes with the Cantor normal form and with `φ` at the other
  `ε`-numbers; each recursive call is guarded by the decrease of the measure, which holds on the domain;
* `rxL_lt_Om1`, `rxL_Om`, `rxL_atom`, `rxL_gt`, `rxL_veb` (**the equations on the domain**).

No new axiom.  New definitions: `RxE`, `rxDn`, `rxMs`, `rxLvA`, `rxLvO`, `rxL`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}}

section CDec

variable {a b : Ordinal.{0}}

/-- A principal member: `w − x ∈ {w, 0}` and `log_ω w = w` at an `ε`-number. -/
theorem rxC_prin_dec {w : Ordinal.{0}} (hw : w ∈ S.CSet a b) (hP : IsPrincipal (· + ·) w)
    (hε : ω ^ w = w) : (∀ x, x ≤ w → w - x ∈ S.CSet a b) ∧ log ω w ∈ S.CSet a b := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases gg_sub_prin hP hx with e | e <;> rw [e]
    · exact hw
    · exact CSet.zero_mem a b
  · have : log ω w = w := by conv_lhs => rw [← hε]; exact log_opow one_lt_omega0 _
    rw [this]; exact hw

/-- **`Cl(a, b)` is closed under `w ↦ w − x` (members `x ≤ w`) and `log_ω`.** -/
theorem rxCDec : ∀ w, w ∈ S.CSet a b →
    (∀ x, x ∈ S.CSet a b → x ≤ w → w - x ∈ S.CSet a b) ∧ log ω w ∈ S.CSet a b := by
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IHo =>
  intro hw
  suffices H : ∀ v, v ∈ S.CSet a b → v ≤ w →
      (∀ x, x ∈ S.CSet a b → x ≤ v → v - x ∈ S.CSet a b) ∧ log ω v ∈ S.CSet a b from H w hw le_rfl
  intro v hv
  induction hv with
  | @small v h =>
    intro _
    exact ⟨fun x _ _ => CSet.of_lt ((Ordinal.sub_le_self v x).trans_lt h),
      CSet.of_lt ((log_le_self ω v).trans_lt h)⟩
  | zero =>
    intro _
    refine ⟨fun x _ _ => by rw [Ordinal.zero_sub]; exact CSet.zero_mem a b, ?_⟩
    rw [Ordinal.log_zero_right]; exact CSet.zero_mem a b
  | inacc k =>
    intro _
    have hS := SC_I (S := S) k
    have h := rxC_prin_dec (CSet.I_mem a b k) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | inaccW =>
    intro _
    have hS := SC_Iw (S := S)
    have h := rxC_prin_dec (CSet.Iw_mem a b) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @add u v hu hv ihu ihv =>
    intro hle
    have hu' := ihu (le_self_add.trans hle)
    have hv' := ihv (le_add_self.trans hle)
    refine ⟨fun x hx hxuv => ?_, ?_⟩
    · rcases le_or_gt x u with hxu | hux
      · have e : u + v - x = (u - x) + v := by
          refine Ordinal.sub_eq_of_add_eq ?_
          rw [← add_assoc, Ordinal.add_sub_cancel_of_le hxu]
        rw [e]; exact CSet.add_mem (hu'.1 x hx hxu) hv
      · rcases hxuv.lt_or_eq with hlt | heq
        · have hxw : x < w := hlt.trans_le hle
          have hxu' : x - u ∈ S.CSet a b := (IHo x hxw hx).1 u hu hux.le
          have e1 : x = u + (x - u) := (Ordinal.add_sub_cancel_of_le hux.le).symm
          have hxv : x - u ≤ v := by
            have : u + (x - u) ≤ u + v := by rw [← e1]; exact hxuv
            exact (add_le_add_iff_left _).1 this
          have e : u + v - x = v - (x - u) := by
            conv_lhs => rw [e1]
            rw [← Ordinal.sub_sub, Ordinal.add_sub_cancel]
          rw [e]; exact hv'.1 (x - u) hxu' hxv
        · rw [heq, Ordinal.sub_self]; exact CSet.zero_mem a b
    · rcases ggLog_add u v with e | e <;> rw [e]
      · exact hu'.2
      · exact hv'.2
  | @phi p q hp hq _ _ =>
    intro _
    rcases eq_or_ne p 0 with rfl | hp0
    · rw [veblen_zero_apply]
      have hop : ω ^ q ∈ S.CSet a b := by
        have := CSet.phi_mem (S := S) (CSet.zero_mem a b) hq; rwa [veblen_zero_apply] at this
      refine ⟨fun x _ hx => ?_, ?_⟩
      · rcases gg_sub_prin (isPrincipal_add_omega0_opow q) hx with e | e <;> rw [e]
        · exact hop
        · exact CSet.zero_mem a b
      · rw [log_opow one_lt_omega0]; exact hq
    · have hE := gg_veblen_eps (y := q) hp0
      have hP : IsPrincipal (· + ·) (veblen p q) := by rw [← hE]; exact isPrincipal_add_omega0_opow _
      have h := rxC_prin_dec (CSet.phi_mem hp hq) hP hE
      exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @om p hp _ =>
    intro _
    rcases eq_or_ne p 0 with rfl | h0
    · rw [Om_zero]
      refine ⟨fun x _ _ => by rw [Ordinal.zero_sub]; exact CSet.zero_mem a b, ?_⟩
      rw [Ordinal.log_zero_right]; exact CSet.zero_mem a b
    · have hS := SC_Om h0
      have h := rxC_prin_dec (CSet.Om_mem hp) hS.isPrincipal (gg_SC_eps hS)
      exact ⟨fun x _ hx => h.1 x hx, h.2⟩
  | @coll π e hπ hπC heC _ _ =>
    intro _
    have hS := SC_psi (S := S) hπ e.1
    have h := rxC_prin_dec (CSet.psi_mem e.2 hπ hπC heC) hS.isPrincipal (gg_SC_eps hS)
    exact ⟨fun x _ hx => h.1 x hx, h.2⟩

/-- **The Veblen parts of a member.** -/
theorem rxCDecV {x : Ordinal.{0}} (hx : x ∈ S.CSet a b) :
    ∀ p q, veblen p q = x → q < x → p ∈ S.CSet a b ∧ q ∈ S.CSet a b := by
  induction hx with
  | @small x h =>
    intro p q e hq
    exact ⟨CSet.of_lt ((e ▸ left_le_veblen p q).trans_lt h), CSet.of_lt (hq.trans h)⟩
  | zero => intro p q e _; exact absurd e veblen_pos.ne'
  | inacc k =>
    intro p q e hq
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_I (S := S) k) e hq
    exact ⟨CSet.I_mem a b k, CSet.zero_mem a b⟩
  | inaccW =>
    intro p q e hq
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_Iw (S := S)) e hq
    exact ⟨CSet.Iw_mem a b, CSet.zero_mem a b⟩
  | @add u v hu hv ihu ihv =>
    intro p q e hq
    have hp : IsPrincipal (· + ·) (u + v) := e ▸ Ph.ph_veblen_prin p q
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [add_zero] at e hq; exact ihu p q e hq
    · have hu' : u < u + v := lt_add_of_pos_right u (pos_iff_ne_zero.2 hv0)
      have hvv : v = u + v := by
        rcases (le_add_self : v ≤ u + v).lt_or_eq with h | h
        · exact absurd (hp hu' h) (lt_irrefl _)
        · exact h
      rw [← hvv] at e hq
      exact ihv p q e hq
  | @phi p' q' hp' hq' _ ihq =>
    intro p q e hq
    rcases veblen_eq_veblen_iff.1 e with ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h1, h2]; exact ⟨hp', hq'⟩
    · rw [h2] at hq; exact absurd hq (lt_irrefl _)
    · exact ihq p q h2 (by rw [← h2, e]; exact hq)
  | @om p' hp' _ =>
    intro p q e hq
    rcases eq_or_ne p' 0 with rfl | h0
    · rw [Om_zero] at e; exact absurd e veblen_pos.ne'
    · obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_Om h0) e hq
      exact ⟨CSet.Om_mem hp', CSet.zero_mem a b⟩
  | @coll π e' hπ hπC heC _ _ =>
    intro p q e hq
    obtain ⟨rfl, rfl⟩ := rxSC_veb (SC_psi (S := S) hπ e'.1) e hq
    exact ⟨CSet.psi_mem e'.2 hπ hπC heC, CSet.zero_mem a b⟩

end CDec

/-- **The domain** of the level shift. -/
def RxE (S : InaccSeq.{0}) (T x : Ordinal.{0}) : Prop :=
  RxN S T x ∧ x ∈ S.CSet (Om ω) (ConjT.th S) ∧ x < Om ω

/-- **The normal argument** at the subscript `π`. -/
noncomputable def rxDn (S : InaccSeq.{0}) (π s : Ordinal.{0}) : Ordinal.{0} :=
  sInf {d | d ∈ S.CSet d (S.psi d π) ∧ S.psi d π = s}

/-- **The measure** `Λ·rxH(x) + x`. -/
noncomputable def rxMs (S : InaccSeq.{0}) (T x : Ordinal.{0}) : Ordinal.{0} :=
  S.Lam * (rxH S T x : Ordinal.{0}) + x

open Classical in
/-- The level `k ≥ 1` of a strongly critical `x` with `Ω_k < x < Ω_{k+1}` (`0` otherwise). -/
noncomputable def rxLvA (x : Ordinal.{0}) : ℕ :=
  if h : ∃ k : ℕ, 1 ≤ k ∧ SC x ∧ Om (k : Ordinal.{0}) < x ∧ x < Om ((k : Ordinal.{0}) + 1) then Nat.find h
  else 0

open Classical in
/-- The `k` with `x = Ω_k` (`0` otherwise). -/
noncomputable def rxLvO (x : Ordinal.{0}) : ℕ :=
  if h : ∃ k : ℕ, x = Om (k : Ordinal.{0}) then Nat.find h else 0

open Classical in
/-- **The level shift at every finite level.** -/
noncomputable def rxL (S : InaccSeq.{0}) (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (T x : Ordinal.{0}) :
    Ordinal.{0} :=
  if _h1 : x < Om 1 then ruInv Z At x
  else if _hΩ : ∃ k : ℕ, x = Om (k : Ordinal.{0}) then Om ((rxLvO x : Ordinal.{0}) + 1)
  else if _hA : ∃ k : ℕ, 1 ≤ k ∧ SC x ∧ Om (k : Ordinal.{0}) < x ∧ x < Om ((k : Ordinal.{0}) + 1) then
    if hd : rxMs S T (rxDn S (Om ((rxLvA x : Ordinal.{0}) + 1)) x) < rxMs S T x then
      S.psi (rxL S Z At T (rxDn S (Om ((rxLvA x : Ordinal.{0}) + 1)) x))
        (Om ((rxLvA x : Ordinal.{0}) + 1 + 1))
    else 0
  else if _h3 : log ω x < x then
    (if _h5 : rxMs S T (log ω x) < rxMs S T x then ω ^ rxL S Z At T (log ω x) else 0) *
      (x / ω ^ log ω x) +
    (if _h6 : rxMs S T (x % ω ^ log ω x) < rxMs S T x then rxL S Z At T (x % ω ^ log ω x) else 0)
  else if _h4 : invVeblen₁ x < x ∧ invVeblen₂ x < x then
    veblen (if _h7 : rxMs S T (invVeblen₁ x) < rxMs S T x then rxL S Z At T (invVeblen₁ x) else 0)
      (if _h8 : rxMs S T (invVeblen₂ x) < rxMs S T x then rxL S Z At T (invVeblen₂ x) else 0)
  else 0
termination_by rxMs S T x
decreasing_by
  · exact hd
  · exact _h5
  · exact _h6
  · exact _h7
  · exact _h8

section Measure

variable {T : Ordinal.{0}}

theorem rxMs_lt_stage {p x : Ordinal.{0}} (hp : p < S.Lam) (h : rxH S T p < rxH S T x) :
    rxMs S T p < rxMs S T x := by
  unfold rxMs
  have h1 : (rxH S T p : Ordinal.{0}) + 1 ≤ rxH S T x := by exact_mod_cast h
  calc S.Lam * (rxH S T p : Ordinal.{0}) + p < S.Lam * (rxH S T p : Ordinal.{0}) + S.Lam :=
        (add_lt_add_iff_left _).2 hp
    _ = S.Lam * ((rxH S T p : Ordinal.{0}) + 1) := (mul_add_one _ _).symm
    _ ≤ S.Lam * (rxH S T x : Ordinal.{0}) := by gcongr
    _ ≤ _ := le_self_add

theorem rxMs_lt_val {p x : Ordinal.{0}} (hh : rxH S T p ≤ rxH S T x) (h : p < x) :
    rxMs S T p < rxMs S T x := by
  unfold rxMs
  have hh' : (rxH S T p : Ordinal.{0}) ≤ rxH S T x := by exact_mod_cast hh
  calc S.Lam * (rxH S T p : Ordinal.{0}) + p ≤ S.Lam * (rxH S T x : Ordinal.{0}) + p := by gcongr
    _ < _ := (add_lt_add_iff_left _).2 h

end Measure

/-- **The normal argument is unique.** -/
theorem rxDn_eq {π d : Ordinal.{0}} (hπ : S.InR π) (hd : d ∈ S.CSet d (S.psi d π)) :
    rxDn S π (S.psi d π) = d := by
  refine le_antisymm (csInf_le' ⟨hd, rfl⟩) (le_csInf ⟨d, hd, rfl⟩ fun d' hd' => ?_)
  obtain ⟨h1, h2⟩ := hd'
  have hc := compare_psi hπ h1 hd
  rw [h2, compare_eq_iff_eq.2 rfl] at hc
  exact (compare_eq_iff_eq.1 hc.symm).ge

/-- The level of a strongly critical ordinal between `Ω_k` and `Ω_{k+1}` is unique. -/
theorem rxLev_unique {x : Ordinal.{0}} {j k : ℕ} (hj1 : Om (j : Ordinal.{0}) < x)
    (hj2 : x < Om ((j : Ordinal.{0}) + 1)) (hk1 : Om (k : Ordinal.{0}) < x)
    (hk2 : x < Om ((k : Ordinal.{0}) + 1)) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · have h' : (j : Ordinal.{0}) + 1 ≤ k := by exact_mod_cast h
    exact absurd ((Om_le_Om.2 h').trans_lt hk1) (not_lt.2 hj2.le)
  · exact h
  · have h' : (k : Ordinal.{0}) + 1 ≤ j := by exact_mod_cast h
    exact absurd ((Om_le_Om.2 h').trans_lt hj1) (not_lt.2 hk2.le)

theorem rxOm_nat_inj {j k : ℕ} (h : Om (j : Ordinal.{0}) = Om (k : Ordinal.{0})) : j = k := by
  exact_mod_cast Om_inj.1 h

section Domain

variable {T : Ordinal.{0}}

theorem rxOmW_lt_Lam : Om ω < S.Lam := lt_Lam_of_mem zero_le (ConjT.OmW_mem S 0 0)

theorem rxE_lt_Lam {x : Ordinal.{0}} (hx : RxE S T x) : x < S.Lam := hx.2.2.trans rxOmW_lt_Lam

/-- A cardinal `Ω_σ < Ω_ω` is a finite `Ω_k`. -/
theorem rxCard_nat {σ : Ordinal.{0}} (h : Om σ < Om ω) : ∃ k : ℕ, σ = k := lt_omega0.1 (Om_lt_Om.1 h)

end Domain

end Googology.Trans.PoR.InaccPsi.R2.Rx
