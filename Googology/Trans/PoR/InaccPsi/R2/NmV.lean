import Googology.Trans.PoR.InaccPsi.R2.NmS

/-!
# The InaccPsi names of the Veblen hierarchy over `υ` and of `Λ_Γ`

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Pv`), `V_γ = veblenWith υ γ` (`R2.VG`), `Λ_Γ` the least
`λ > 0` with `V_γ(λ) = λ` for every `γ < λ` (`R2.LamG`).  For every InaccPsi sequence `S : InaccSeq.{0}`:

* `Pv_Om1_pow`: `P(Ω₁^γ) = V_γ(1)` for `1 ≤ γ ≤ Λ_Γ`;
* `V_eq` (**Theorem V**): `V_γ(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^γ·α)` for `1 ≤ γ < Λ_Γ` and `1 ≤ α ≤ V_{γ+1}(1)`;
* `LamG_eq_pow` and `LamG_eq` (**the name of `Λ_Γ`**): `Λ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Λ_Γ})` and
  `Λ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁})`; `ups_LamG_eq`: `υ_{Λ_Γ} = Λ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁})`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nm

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-! ## `V_γ(1)` -/

theorem one_lt_VG_one (g : Ordinal.{0}) : 1 < VG g 1 := by
  have hl := VG_isSuccLimit g one_ne_zero
  have h1 : 1 ≤ VG g 1 := VG_id_le g 1
  refine lt_of_le_of_ne h1 fun e => ?_
  rw [← e] at hl
  have := hl.add_one_lt (zero_lt_one : (0 : Ordinal.{0}) < 1)
  rw [zero_add] at this
  exact lt_irrefl _ this

theorem VG_one_strictMono : StrictMono fun g : Ordinal.{0} => VG g 1 := by
  intro g g' h
  show VG g 1 < VG g' 1
  rw [← VG_VG h 1]
  exact VG_strictMono g (one_lt_VG_one g')

theorem le_VG_one (g : Ordinal.{0}) : g ≤ VG g 1 := VG_one_strictMono.id_le g

/-- `γ < V_γ(1)` for `1 ≤ γ < Λ_Γ`. -/
theorem lt_VG_one {g : Ordinal.{0}} (h1 : 1 ≤ g) (h : g < LamG) : g < VG g 1 := by
  refine lt_of_le_of_ne (le_VG_one g) fun e => ?_
  have hg0 : g ≠ 0 := Order.one_le_iff_ne_zero.1 h1
  have hmem : g ∈ range (VG g) := ⟨1, e.symm⟩
  have hGP : IsGP g := ⟨pos_iff_ne_zero.2 hg0, (mem_range_VG hg0).1 hmem⟩
  exact absurd (LamG_le_GP hGP) (not_le.2 h)

theorem ups_one_lt_VG (S : InaccSeq.{0}) {g : Ordinal.{0}} (hg : 1 ≤ g) : upsilon 1 < VG g 1 := by
  have hg0 : 0 < g := Order.one_le_iff_pos.1 hg
  have hfix : upsilon (VG g 1) = VG g 1 := by rw [← VG_zero]; exact VG_VG hg0 1
  have h1 : upsilon 1 ≤ VG g 1 := by
    rw [← hfix]; exact upsilon_normal.strictMono.monotone (VG_id_le g 1)
  refine lt_of_le_of_ne h1 fun e => ?_
  have h2 : upsilon (upsilon 1) = upsilon 1 := by rw [e]; exact hfix
  have h3 : upsilon 1 = 1 := upsilon_normal.strictMono.injective h2
  exact absurd h3 (ne_of_gt (one_lt_ups_one S))

theorem nxt_VG_Pv0 (S : InaccSeq.{0}) {g : Ordinal.{0}} (hg : 1 ≤ g) :
    nxt (VG g) (Pv S 0) = VG g 1 := by
  rw [Pv_zero]
  obtain ⟨c, h1, -, h2⟩ := nxt_spec (VG_normal g) (VG_at_zero g) (upsilon 1)
  rw [h2]
  have hc : c = 0 := by
    by_contra hc
    have := (VG_strictMono g).monotone (Order.one_le_iff_ne_zero.2 hc)
    exact absurd (ups_one_lt_VG S hg) (not_lt.2 (this.trans h1))
  rw [hc, zero_add]

/-- The condition of Theorem START at `η₁ = 0`. -/
theorem hC_zero (S : InaccSeq.{0}) {γ : Ordinal.{0}} (h : ∀ δ < γ, 1 ≤ δ → δ < VG δ 1) :
    ∀ δ < γ, δ < nxt (VG δ) (Pv S 0) := by
  intro δ hδ
  rcases eq_or_ne δ 0 with rfl | hδ0
  · exact lt_of_le_of_lt zero_le (lt_nxt (VG_normal 0) (VG_at_zero 0) _)
  · rw [nxt_VG_Pv0 S (Order.one_le_iff_ne_zero.2 hδ0)]
    exact h δ hδ (Order.one_le_iff_ne_zero.2 hδ0)

/-- `P(Ω₁^γ) = V_γ(1)` when `δ < V_δ(1)` for every `1 ≤ δ < γ`. -/
theorem Pv_Om1_pow (S : InaccSeq.{0}) {γ : Ordinal.{0}} (hγ : 1 ≤ γ)
    (h : ∀ δ < γ, 1 ≤ δ → δ < VG δ 1) : Pv S (Om 1 ^ γ) = VG γ 1 := by
  have := start_all S γ 0 (good_zero S) (dvd_zero _) (hC_zero S h)
  rwa [zero_add, nxt_VG_Pv0 S hγ] at this

theorem good_Om1_pow (S : InaccSeq.{0}) {γ : Ordinal.{0}} (hγ : γ < Pv S (Om 1 ^ γ)) :
    Bt.Good S (Om 1 ^ γ) := by
  have := good_add (S := S) (good_zero S) (δ := Om 1 ^ γ) (by rw [zero_add]; exact mem_Om1_pow hγ)
  rwa [zero_add] at this

/-- **Theorem V** under its hypothesis: `V_γ(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^γ·α)` for `1 ≤ α ≤ V_{γ+1}(1)`, when
`δ < V_δ(1)` for every `1 ≤ δ ≤ γ`. -/
theorem V_eq_of (S : InaccSeq.{0}) {γ : Ordinal.{0}} (hγ1 : 1 ≤ γ)
    (h : ∀ δ ≤ γ, 1 ≤ δ → δ < VG δ 1) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α ≤ VG (γ + 1) 1) :
    VG γ α = Pv S (Om 1 ^ γ * α) := by
  have h' : ∀ δ < γ, 1 ≤ δ → δ < VG δ 1 := fun δ hδ => h δ hδ.le
  have h'' : ∀ δ < γ + 1, 1 ≤ δ → δ < VG δ 1 := fun δ hδ => h δ (Order.lt_add_one_iff.1 hδ)
  have hx0 := Pv_Om1_pow S hγ1 h'
  have hγP : γ < Pv S (Om 1 ^ γ) := by rw [hx0]; exact h γ le_rfl hγ1
  have hseg := seg_all S γ (Om 1 ^ γ) 1 (good_Om1_pow S hγP) dvd_rfl hγP hx0
  have hZ : Zu S (Om 1 ^ γ) (Om 1 ^ γ) = VG (γ + 1) 1 := by
    have := zu_eq_nxt (S := S) (γ := γ) (good_zero S) (dvd_zero _) (hC_zero S h'')
    rwa [zero_add, nxt_VG_Pv0 S (Order.one_le_iff_ne_zero.2 (by
      exact ne_of_gt (lt_of_le_of_lt zero_le (lt_add_one γ))))] at this
  have e1 : 1 + (α - 1) = α := Ordinal.add_sub_cancel_of_le hα1
  have hb : α - 1 ≤ Zu S (Om 1 ^ γ) (Om 1 ^ γ) := by rw [hZ]; exact (Ordinal.sub_le_self _ _).trans hα
  have := hseg (α - 1) hb
  rw [e1] at this
  rw [← this, ← e1, mul_add, mul_one, e1]

/-- **Theorem V**: `V_γ(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^γ·α)` for `1 ≤ γ < Λ_Γ` and `1 ≤ α ≤ V_{γ+1}(1)`. -/
theorem V_eq (S : InaccSeq.{0}) {γ α : Ordinal.{0}} (hγ1 : 1 ≤ γ) (hγ : γ < LamG)
    (hα1 : 1 ≤ α) (hα : α ≤ VG (γ + 1) 1) :
    VG γ α = S.psi (Om ω + ConjT.th S * (Om 1 ^ γ * α)) (Om 1) :=
  V_eq_of S hγ1 (fun _ hδ h1 => lt_VG_one h1 (hδ.trans_lt hγ)) hα1 hα

/-- `P(Ω₁^{Λ_Γ}) = Λ_Γ`. -/
theorem Pv_Om1_pow_LamG (S : InaccSeq.{0}) : Pv S (Om 1 ^ LamG) = LamG := by
  have h1 : 1 ≤ LamG := Order.one_le_iff_pos.2 LamG_spec.1
  rw [Pv_Om1_pow S h1 fun δ hδ hδ1 => lt_VG_one hδ1 hδ]
  refine le_antisymm ?_ (le_VG_one LamG)
  have hmem : LamG ∈ range (VG LamG) := (mem_range_VG LamG_spec.1.ne').2 LamG_spec.2
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, VG_at_zero] at hc; exact absurd hc LamG_spec.1.ne
  calc VG LamG 1 ≤ VG LamG c := (VG_strictMono _).monotone (Order.one_le_iff_ne_zero.2 hc0)
    _ = LamG := hc

theorem LamG_lt_Om1' : LamG < Om (1 : Ordinal.{0}) := by rw [← Om1_eq]; exact LamG_lt_Om1

/-- **`Λ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Λ_Γ})`**. -/
theorem LamG_eq_pow (S : InaccSeq.{0}) :
    LamG = S.psi (Om ω + ConjT.th S * Om 1 ^ LamG) (Om 1) := (Pv_Om1_pow_LamG S).symm

/-- **The name of `Λ_Γ`**: `Λ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁})`. -/
theorem LamG_eq (S : InaccSeq.{0}) :
    LamG = S.psi (Om ω + ConjT.th S * Om 1 ^ Om (1 : Ordinal.{0})) (Om 1) := by
  have hL := Pv_Om1_pow_LamG S
  have hLSC : SC LamG := by rw [← hL]; exact Pv_SC S _
  have hL1 := LamG_lt_Om1'
  have h1 : (1 : Ordinal.{0}) < LamG := one_lt_SC hLSC
  refine le_antisymm ?_ ?_
  · rw [← hL]; exact Pv_mono (Om1_pow_le_iff.2 hL1.le)
  · show Pv S (Om 1 ^ Om 1) ≤ LamG
    refine psi_le_of_key hLSC fun e he hea => ?_
    rcases lt_or_ge e (Om (ω : Ordinal.{0})) with he1 | he1
    · calc S.psi e (Om 1) ≤ Pv S 0 := by rw [Pv, A_zero]; exact (psi_mono Low.InR_Om_one he1.le).1
        _ = upsilon 1 := Pv_zero S
        _ < VG LamG 1 := ups_one_lt_VG S h1.le
        _ = LamG := by rw [← Pv_Om1_pow S h1.le fun δ hδ hδ1 => lt_VG_one hδ1 hδ, hL]
    obtain ⟨η, hη, k1, k2⟩ := quotA hL1 he he1
    have hψ : S.psi e (Om 1) ≤ Pv S (η + 1) := by
      rw [Pv, ← ConjT.A_succ]; exact (psi_mono Low.InR_Om_one k2.le).1
    have hηW : η < Om 1 ^ Om (1 : Ordinal.{0}) := A_lt_A_iff.1 (k1.trans_lt hea)
    obtain ⟨q, d, δ, hδ, hd, hq⟩ := tinv_HCl hLSC hL1 hη
    have hq0 : q = 0 := by
      by_contra hq0
      have : Om (1 : Ordinal.{0}) ^ Om (1 : Ordinal.{0}) ≤ η := by
        rw [hq]; exact (le_mul_left _ (pos_iff_ne_zero.2 hq0)).trans le_self_add
      exact absurd hηW (not_lt.2 this)
    rw [hq0, mul_zero, zero_add] at hq
    set δ' := max δ 1 with hδ'
    have hδ'L : δ' < LamG := max_lt hδ h1
    have hδ'1 : 1 ≤ δ' := le_max_right _ _
    have hηδ : η + 1 ≤ Om 1 ^ δ' :=
      Order.add_one_le_of_lt (hq ▸ hd.trans_le (Om1_pow_le_iff.2 (le_max_left _ _)))
    calc S.psi e (Om 1) ≤ Pv S (η + 1) := hψ
      _ ≤ Pv S (Om 1 ^ δ') := Pv_mono hηδ
      _ = VG δ' 1 := Pv_Om1_pow S hδ'1 fun δ'' hδ'' hδ''1 => lt_VG_one hδ''1 (hδ''.trans hδ'L)
      _ < VG δ' LamG := VG_strictMono δ' h1
      _ = LamG := LamG_spec.2 δ' hδ'L

/-- `υ_{Λ_Γ} = Λ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁})`. -/
theorem ups_LamG_eq (S : InaccSeq.{0}) :
    upsilon LamG = S.psi (Om ω + ConjT.th S * Om 1 ^ Om (1 : Ordinal.{0})) (Om 1) := by
  rw [LamG_ups]; exact LamG_eq S

end Googology.Trans.PoR.InaccPsi.R2.Nm
