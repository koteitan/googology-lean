import Googology.Trans.PoR.InaccPsi.R2.NmD
import Googology.Trans.PoR.InaccPsi.R2.NcName

/-!
# Fixed points of `υ` and `Γ`-points among the values `P(η)`, by cofinality

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `V_γ = veblenWith υ γ` (`VG`), `W = Ω₁^{Ω₁}`,
`GG` = the enumeration of `{0} ∪ {Γ-points}` (`IsGP`: `0 < l` and `V_γ(l) = l` for every `γ < l`).

* `lw_psi_limit` (**Lemma CONT for every `κ`**): `ψ_κ(a) = sup_{e<a} ψ_κ(e)` at a limit `a`, for every
  `κ` in the range of the notation (the proof of `Bt.psi_limit` with `Ω₁` replaced by `κ`);
* `lw_cof`: below `P(η₀ + X)` (`X` a limit) every `b` lies below some `P(η₀ + c)`, `c < X`;
* `lw_fix_of_cof`: a limit `y` with cofinally many fixed points `z ≤ y` of a normal `F` is a fixed point
  of `F`; `lw_GP_of_cof`: the same for `Γ`-points;
* `lw_GP_Pv` (**the cofinality criterion**): if for every `c < X` some `e` with
  `η₀ + c ≤ e ≤ η₀ + X` has `P(e)` a `Γ`-point, then `P(η₀ + X)` is a `Γ`-point;
* `lw_GP_step`: for a good `η₁` that is a multiple of `W`, `P(η₁ + W)` is a `Γ`-point
  (Theorem START at `W`, `Nm.start_GG`);
* `lw_ups_of_GP`, `lw_iota_of_GP`, `lw_restart_of_SC`, `lw_not_tau_of_GP`: at a `Γ`-point `P(η) = x`:
  `υ_x = x`, `ι(η) = x`, `x` is a restart index, and `x = ρ_x` is not a `τ`-point.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lw

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Nc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- **Lemma CONT for every `κ`**: `ψ_κ(a) = sup_{e<a} ψ_κ(e)` for a limit `a`. -/
theorem lw_psi_limit (S : InaccSeq.{0}) {κ a : Ordinal.{0}} (hκ : S.InR κ) (ha : IsSuccLimit a) :
    S.psi a κ = ⨆ e : Iio a, S.psi e.1 κ := by
  have hbdd : BddAbove (range fun e : Iio a => S.psi e.1 κ) :=
    ⟨κ, by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ _).le⟩
  have ha0 : (0 : Ordinal.{0}) < a := ha.bot_lt
  haveI : Nonempty (Iio a) := ⟨⟨0, ha0⟩⟩
  set σ := ⨆ e : Iio a, S.psi e.1 κ with hσ
  have up : ∀ {y e e' : Ordinal.{0}}, e ≤ e' →
      y ∈ S.CSet e (S.psi e κ) → y ∈ S.CSet e' (S.psi e' κ) :=
    fun h hy => (psi_mono hκ h).2 hy
  have key : ∀ x ∈ S.CSet a σ, ∃ e < a, x ∈ S.CSet e (S.psi e κ) := by
    intro x hx
    induction hx with
    | small h =>
      obtain ⟨e, he⟩ := (lt_ciSup_iff hbdd).1 h
      exact ⟨e.1, e.2, CSet.of_lt he⟩
    | zero => exact ⟨0, ha0, CSet.zero_mem _ _⟩
    | inacc n => exact ⟨0, ha0, CSet.I_mem _ _ n⟩
    | inaccW => exact ⟨0, ha0, CSet.Iw_mem _ _⟩
    | add _ _ ihx ihy =>
      obtain ⟨e1, h1, k1⟩ := ihx
      obtain ⟨e2, h2, k2⟩ := ihy
      exact ⟨max e1 e2, max_lt h1 h2,
        CSet.add_mem (up (le_max_left _ _) k1) (up (le_max_right _ _) k2)⟩
    | phi _ _ ihx ihy =>
      obtain ⟨e1, h1, k1⟩ := ihx
      obtain ⟨e2, h2, k2⟩ := ihy
      exact ⟨max e1 e2, max_lt h1 h2,
        CSet.phi_mem (up (le_max_left _ _) k1) (up (le_max_right _ _) k2)⟩
    | om _ ih =>
      obtain ⟨e1, h1, k1⟩ := ih
      exact ⟨e1, h1, CSet.Om_mem k1⟩
    | @coll π e hπ _ _ ihπ ihe =>
      obtain ⟨e1, h1, k1⟩ := ihπ
      obtain ⟨e2, h2, k2⟩ := ihe
      have hs : e.1 + 1 < a := ha.add_one_lt e.2
      refine ⟨max (e.1 + 1) (max e1 e2), max_lt hs (max_lt h1 h2), ?_⟩
      have he : e.1 < max (e.1 + 1) (max e1 e2) := lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
      exact CSet.psi_mem he hπ
        (up (le_trans (le_max_left _ _) (le_max_right _ _)) k1)
        (up (le_trans (le_max_right _ _) (le_max_right _ _)) k2)
  apply le_antisymm
  · have hκσ : κ ∈ S.CSet a σ :=
      CSet_mono le_rfl (le_ciSup hbdd ⟨0, ha0⟩) (mem_CSet_psi_any hκ a 0)
    refine psi_le_of_good hκσ ?_
    intro x hx hxκ
    obtain ⟨e, he, hN⟩ := key x hx
    exact lt_of_lt_of_le (lt_psi_of_mem hκ hN hxκ) (le_ciSup hbdd ⟨e, he⟩)
  · exact ciSup_le fun e => (psi_mono hκ e.2.le).1

variable {S : InaccSeq.{0}}

/-- Below `P(η₀ + X)`, `X` a limit, every `b` lies below some `P(η₀ + c)` with `c < X`. -/
theorem lw_cof {η0 X b : Ordinal.{0}} (hX : IsSuccLimit X) (hb : b < Pv S (η0 + X)) :
    ∃ c < X, b < Pv S (η0 + c) := by
  by_contra h
  exact absurd (cont_le hX fun c hc => not_lt.1 fun h' => h ⟨c, hc, h'⟩) (not_le.2 hb)

/-- A limit `y` with cofinally many fixed points `z ≤ y` of a normal `F` is a fixed point of `F`. -/
theorem lw_fix_of_cof {F : Ordinal.{0} → Ordinal.{0}} (hF : IsNormal F) {y : Ordinal.{0}}
    (hy : IsSuccLimit y) (h : ∀ b < y, ∃ z, b < z ∧ z ≤ y ∧ F z = z) : F y = y := by
  apply le_antisymm
  · refine (hF.le_iff_forall_le hy).2 fun b hb => ?_
    obtain ⟨z, hbz, hzy, hz⟩ := h b hb
    calc F b ≤ F z := hF.strictMono.monotone hbz.le
      _ = z := hz
      _ ≤ y := hzy
  · exact hF.strictMono.id_le y

/-- A limit `y > 0` with cofinally many `Γ`-points `z ≤ y` is a `Γ`-point. -/
theorem lw_GP_of_cof {y : Ordinal.{0}} (hy0 : 0 < y) (hy : IsSuccLimit y)
    (h : ∀ b < y, ∃ z, b < z ∧ z ≤ y ∧ IsGP z) : IsGP y := by
  refine ⟨hy0, fun g hg => lw_fix_of_cof (VG_normal g) hy fun b hb => ?_⟩
  obtain ⟨z, hz1, hz2, hz3⟩ := h (max b g) (max_lt hb hg)
  exact ⟨z, (le_max_left _ _).trans_lt hz1, hz2, hz3.2 g ((le_max_right _ _).trans_lt hz1)⟩

/-- **The cofinality criterion.**  If for every `c < X` (`X` a limit) some `e` with
`η₀ + c ≤ e ≤ η₀ + X` has `P(e)` a `Γ`-point, then `P(η₀ + X)` is a `Γ`-point. -/
theorem lw_GP_Pv {η0 X : Ordinal.{0}} (hX : IsSuccLimit X)
    (h : ∀ c < X, ∃ e, η0 + c ≤ e ∧ e ≤ η0 + X ∧ IsGP (Pv S e)) : IsGP (Pv S (η0 + X)) := by
  have hSC := Pv_SC S (η0 + X)
  refine lw_GP_of_cof hSC.1 hSC.isSuccLimit fun b hb => ?_
  obtain ⟨c, hc, hbc⟩ := lw_cof hX hb
  obtain ⟨e, he1, he2, he3⟩ := h c hc
  exact ⟨Pv S e, hbc.trans_le (Pv_mono he1), Pv_mono he2, he3⟩

/-- For a good `η₁` that is a multiple of `W = Ω₁^{Ω₁}`, `P(η₁ + W)` is a `Γ`-point. -/
theorem lw_GP_step {η1 : Ordinal.{0}} (hg : Bt.Good S η1) (hdvd : W ∣ η1) :
    IsGP (Pv S (η1 + W)) := by
  rw [start_GG hg hdvd]
  obtain ⟨c, hc⟩ : nxt GG (Pv S η1) ∈ range GG := nxt_mem GG _
  have hxY := lt_nxt GG_normal GG_zero (Pv S η1)
  have hc0 : c ≠ 0 := by
    intro h0; rw [← hc, h0, GG_zero] at hxY; exact absurd hxY (not_lt.2 zero_le)
  rw [← hc]; exact isGP_of_GG hc0

/-- A `Γ`-point is a fixed point of `υ`. -/
theorem lw_ups_of_GP {x : Ordinal.{0}} (h : IsGP x) : upsilon x = x := by
  have := h.2 0 h.1; rwa [VG_zero] at this

/-- At a `Γ`-point `P(η) = x`: `ι(η) = x`. -/
theorem lw_iota_of_GP {η : Ordinal.{0}} (h : IsGP (Pv S η)) : iota S η = Pv S η :=
  iota_of_fix rfl (lw_ups_of_GP h)

/-- A strongly critical ordinal is a restart index (`≠ 0`, a multiple of `ω²`). -/
theorem lw_restart_of_SC {x : Ordinal.{0}} (hx : SC x) : IsRestartIdx x := by
  refine ⟨hx.1.ne', ?_⟩
  have h2 : (2 : Ordinal.{0}) ≤ x := by
    have := Order.add_one_le_of_lt (one_lt_SC hx); rwa [one_add_one_eq_two] at this
  have e := Low.opow_eq_self_of_SC hx
  have e2 : (ω : Ordinal.{0}) ^ (2 : ℕ) = ω ^ (2 : Ordinal.{0}) := by
    rw [← opow_natCast]; norm_num
  rw [e2, ← e, opow_split h2]
  exact dvd_mul_right _ _

/-- A `Γ`-point `P(η)` is the restart `ρ_ι` with `ι = ι(η) = P(η)` a restart index. -/
theorem lw_restart_of_GP {η : Ordinal.{0}} (h : IsGP (Pv S η)) :
    IsRestartIdx (iota S η) ∧ Pv S η = upsilon (iota S η) := by
  rw [lw_iota_of_GP h]
  exact ⟨lw_restart_of_SC (Pv_SC S η), (lw_ups_of_GP h).symm⟩

/-- A `Γ`-point `P(η)` is not a `τ`-point. -/
theorem lw_not_tau_of_GP {η : Ordinal.{0}} (h : IsGP (Pv S η)) : ¬ NcTauPt (Pv S η) := by
  obtain ⟨hr, e⟩ := lw_restart_of_GP h
  rw [e]; exact ncRestart_not_tau hr

end Googology.Trans.PoR.InaccPsi.R2.Lw
