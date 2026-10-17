import Googology.Trans.PoR.InaccPsi.R2.NmV

/-!
# The InaccPsi names of the `Γ`-points over `υ` and of `Φ_Γ`

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Pv`), `W = Ω₁^{Ω₁}`, `GG` the enumeration of
`{0} ∪ Γ`-points (`R2.GG`, `GG 1 = Λ_Γ`), `Φ_Γ` the least `α ≥ 1` with `GG(α) = α` (`R2.PhiG`).

* `lt_nxt_of_lt_nxtGG`: below the least `Γ`-point `Y` above `x`, `δ < nxt V_δ x`;
* `start_GG` (**Theorem START at `W`**): for a good multiple `η₁` of `W`:
  `P(η₁ + W) = nxt GG (P(η₁))`;
* `seg_GG`: `P(η₀ + W·β) = GG(c₀ + β)` for `β ≤ Zu η₀ W` (`η₀` good, a multiple of `W`, `P(η₀) = GG(c₀)`);
* `GG_eq` (**Theorem GG**): `GG(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}·α)` for `1 ≤ α ≤ Φ_Γ`;
* `PhiG_eq_mul`, `PhiG_eq` (**the name of `Φ_Γ`**): `Φ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}·Φ_Γ)` and
  `Φ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1})`; `ups_PhiG_eq`: `υ_{Φ_Γ} = Φ_Γ`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nm

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-- `W = Ω₁^{Ω₁}`. -/
noncomputable abbrev W : Ordinal.{0} := Om (1 : Ordinal.{0}) ^ Om (1 : Ordinal.{0})

theorem W_pos : 0 < W := Om1_pow_pos _

/-- `nxt V_g x < nxt V_{g+1} x`. -/
theorem nxt_lt_nxt_succ (g x : Ordinal.{0}) : nxt (VG g) x < nxt (VG (g + 1)) x := by
  have hw := nxt_mem (VG (g + 1)) x
  have hle : nxt (VG g) x ≤ nxt (VG (g + 1)) x :=
    nxt_le (VG_normal g) (VG_at_zero g) (range_VG_anti (le_self_add) hw)
      (lt_nxt (VG_normal _) (VG_at_zero _) x)
  refine lt_of_le_of_ne hle fun e => ?_
  exact nxt_not_fix g x (by rw [e]; exact mem_range_VG_succ.1 hw)

theorem isGP_of_GG {c : Ordinal.{0}} (hc : c ≠ 0) : IsGP (GG c) := isGP_GG (pos_iff_ne_zero.2 hc)

theorem GP_mem_range {l g : Ordinal.{0}} (hl : IsGP l) (hg : g < l) : l ∈ range (VG g) :=
  ⟨l, hl.2 g hg⟩

/-- Below the next `Γ`-point `Y` above `x`: `δ < nxt V_δ x`. -/
theorem lt_nxt_of_lt_nxtGG {x δ : Ordinal.{0}} (hδ : δ < nxt GG x) : δ < nxt (VG δ) x := by
  rcases le_or_gt δ x with h | h
  · exact h.trans_lt (lt_nxt (VG_normal δ) (VG_at_zero δ) x)
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨c, hc⟩ := nxt_mem (VG δ) x
  have hc0 : c ≠ 0 := by
    intro h0
    have := lt_nxt (VG_normal δ) (VG_at_zero δ) x
    rw [← hc, h0, VG_at_zero] at this
    exact absurd this (not_lt.2 zero_le)
  have hge : δ ≤ nxt (VG δ) x := by
    rw [← hc]
    exact (le_VG_one δ).trans ((VG_strictMono δ).monotone (Order.one_le_iff_ne_zero.2 hc0))
  have e : nxt (VG δ) x = δ := le_antisymm hle hge
  have hδ0 : δ ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le h)
  have hGP : IsGP δ := ⟨pos_iff_ne_zero.2 hδ0, (mem_range_VG hδ0).1 ⟨c, hc.trans e⟩⟩
  obtain ⟨a, ha⟩ := GG_surj hGP
  have := nxt_le GG_normal GG_zero ⟨a, ha⟩ h
  exact absurd hδ (not_lt.2 this)

/-- `Ω₁^δ ∣ W` for `δ ≤ Ω₁`. -/
theorem dvd_W {δ : Ordinal.{0}} (hδ : δ ≤ Om 1) : Om (1 : Ordinal.{0}) ^ δ ∣ W :=
  ⟨Om 1 ^ (Om 1 - δ), by rw [← opow_add, Ordinal.add_sub_cancel_of_le hδ]⟩

theorem nxtGG_lt_Om1 {x : Ordinal.{0}} (hx : x < Om 1) : nxt GG x < Om 1 := by
  obtain ⟨c, h1, -, h2⟩ := nxt_spec GG_normal GG_zero x
  rw [h2, ← Om1_eq]
  refine GG_lt_Om1 _ ?_
  have hc : c < Om1 := by rw [Om1_eq]; exact (GG_strictMono.id_le c).trans_lt (h1.trans_lt hx)
  exact (SC_Om one_ne_zero |> fun h => by rw [Om1_eq] at hc ⊢; exact h.add_one_lt hc)

/-- **Theorem START at `W = Ω₁^{Ω₁}`.** -/
theorem start_GG {η1 : Ordinal.{0}} (hg : Bt.Good S η1) (hdvd : W ∣ η1) :
    Pv S (η1 + W) = nxt GG (Pv S η1) := by
  set x1 := Pv S η1 with hx1
  set Y := nxt GG x1 with hY
  have hxY : x1 < Y := lt_nxt GG_normal GG_zero x1
  have hY1 : Y < Om 1 := nxtGG_lt_Om1 (Pv_lt_Om1 S η1)
  have hYGP : IsGP Y := by
    obtain ⟨c, hc⟩ : Y ∈ range GG := nxt_mem GG x1
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, GG_zero] at hc; rw [← hc] at hxY; exact absurd hxY (not_lt.2 zero_le)
    rw [← hc]; exact isGP_of_GG hc0
  -- the values `n_δ = P(η₁ + Ω₁^δ) = nxt V_δ x₁` for `δ < Y`
  have hval : ∀ δ < Y, Pv S (η1 + Om 1 ^ δ) = nxt (VG δ) x1 := fun δ hδ =>
    start_all S δ η1 hg (dvd_trans (dvd_W (hδ.trans hY1).le) hdvd)
      fun δ' hδ' => lt_nxt_of_lt_nxtGG (hδ'.trans hδ)
  have hnY : ∀ δ < Y, nxt (VG δ) x1 ≤ Y := fun δ hδ =>
    nxt_le (VG_normal δ) (VG_at_zero δ) (GP_mem_range hYGP hδ) hxY
  have hYSC : SC Y := by
    refine ⟨hYGP.1, fun a ha b hb => ?_⟩
    set m := max a b with hm
    have hmY : m < Y := max_lt ha hb
    have hSC := Pv_SC S (η1 + Om 1 ^ m)
    rw [hval m hmY] at hSC
    have hmn := lt_nxt_of_lt_nxtGG hmY
    exact (hSC.2 a ((le_max_left a b).trans_lt hmn) b ((le_max_right a b).trans_lt hmn)).trans_le
      (hnY m hmY)
  apply le_antisymm
  · refine psi_le_of_key hYSC fun e he hea => ?_
    rcases lt_or_ge e (Om (ω : Ordinal.{0})) with he1 | he1
    · calc S.psi e (Om 1) ≤ Pv S 0 := by rw [Pv, A_zero]; exact (psi_mono Low.InR_Om_one he1.le).1
        _ ≤ x1 := Pv_mono zero_le
        _ < Y := hxY
    obtain ⟨η, hη, k1, k2⟩ := quotA hY1 he he1
    have hψ : S.psi e (Om 1) ≤ Pv S (η + 1) := by
      rw [Pv, ← ConjT.A_succ]; exact (psi_mono Low.InR_Om_one k2.le).1
    have hηlt : η < η1 + W := A_lt_A_iff.1 (k1.trans_lt hea)
    rcases lt_or_ge η η1 with hlt | hge
    · exact hψ.trans_lt ((Pv_mono (Order.add_one_le_of_lt hlt)).trans_lt hxY)
    obtain ⟨q, d, δ, hδ, hd, hq⟩ := tinv_HCl hYSC hY1 hη
    obtain ⟨q1, hq1⟩ := hdvd
    have hdW : d < W := hd.trans (Om1_pow_lt_iff.2 (hδ.trans hY1))
    have hq' : q = q1 := quot_eq W_pos.ne' hdW hq (hq1 ▸ hge) (by rw [← hq1]; exact hηlt)
    subst hq'
    rw [← hq1] at hq
    set δ' := max δ 1 with hδ'
    have hδ'Y : δ' < Y := max_lt hδ (one_lt_SC hYSC)
    have hle : η + 1 ≤ η1 + Om 1 ^ δ' := by
      rw [hq, add_assoc]
      exact (add_le_add_iff_left η1).2
        (Order.add_one_le_of_lt (hd.trans_le (Om1_pow_le_iff.2 (le_max_left _ _))))
    calc S.psi e (Om 1) ≤ Pv S (η + 1) := hψ
      _ ≤ Pv S (η1 + Om 1 ^ δ') := Pv_mono hle
      _ = nxt (VG δ') x1 := hval δ' hδ'Y
      _ < nxt (VG (δ' + 1)) x1 := nxt_lt_nxt_succ δ' x1
      _ ≤ Y := hnY _ (hYSC.add_one_lt hδ'Y)
  · refine le_of_forall_lt fun δ hδ => ?_
    calc δ < nxt (VG δ) x1 := lt_nxt_of_lt_nxtGG hδ
      _ = Pv S (η1 + Om 1 ^ δ) := (hval δ hδ).symm
      _ ≤ Pv S (η1 + W) :=
          Pv_mono ((add_le_add_iff_left η1).2 (Om1_pow_le_iff.2 (hδ.trans hY1).le))

/-- **Theorem SEG at `W`.** -/
theorem seg_GG {η0 c0 : Ordinal.{0}} (hg0 : Bt.Good S η0) (hdvd : W ∣ η0)
    (h0 : Pv S η0 = GG c0) : ∀ β ≤ Zu S η0 W, Pv S (η0 + W * β) = GG (c0 + β) := by
  refine aseg GG_normal W_pos h0 fun β' hβ' ih => ?_
  set η1 := η0 + W * β' with hη1
  have hβP : β' < Pv S η1 := lt_Pv_of_lt_Zu hβ'
  have hg1 : Bt.Good S η1 := good_add hg0 (mem_W_mul hβP)
  have hd1 : W ∣ η1 := dvd_add hdvd (dvd_mul_right _ _)
  have := start_GG hg1 hd1
  rw [ih, nxt_apply GG_normal GG_zero] at this
  rw [mul_add_one, ← add_assoc]
  exact this

theorem good_W (S : InaccSeq.{0}) : Bt.Good S W := by
  have h := mem_W_mul (S := S) (a := ConjT.Aη S W + 1) (b := Pv S W) (β := 1)
    (one_lt_SC (Pv_SC S W))
  rwa [mul_one] at h

theorem Pv_W (S : InaccSeq.{0}) : Pv S W = GG 1 := by
  rw [GG_one]; exact (LamG_eq S).symm

theorem omega_le_PhiG : (ω : Ordinal.{0}) ≤ PhiG := (omega_lt_LamG.trans LamG_lt_PhiG).le

/-- `Zu W W = Φ_Γ`. -/
theorem Zu_W (S : InaccSeq.{0}) : Zu S W W = PhiG := by
  have hseg := seg_GG (S := S) (good_W S) dvd_rfl (Pv_W S)
  set Z := Zu S W W with hZ
  have hZSC : SC Z := Zu_SC S W W
  have hfix : Pv S (W + W * Z) = Z := Zu_fix S W W
  have hωZ : (ω : Ordinal.{0}) ≤ Z := by
    have := hZSC.isSuccLimit
    exact Ordinal.omega0_le_of_isSuccLimit this
  have hGZ : GG Z = Z := by
    have := hseg Z le_rfl
    rw [hfix, one_add_of_omega0_le hωZ] at this
    exact this.symm
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have h2 := lt_Pv_of_lt_Zu hlt
    rw [hseg PhiG hlt.le, one_add_of_omega0_le omega_le_PhiG, PhiG_fp] at h2
    exact lt_irrefl _ h2
  · exact nfp_le_fp GG_normal.strictMono.monotone (Order.one_le_iff_pos.2 hZSC.1) hGZ.le

/-- **Theorem GG**: `GG(α) = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}·α)` for `1 ≤ α ≤ Φ_Γ`. -/
theorem GG_eq (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα1 : 1 ≤ α) (hα : α ≤ PhiG) :
    GG α = S.psi (Om ω + ConjT.th S * (Om 1 ^ Om (1 : Ordinal.{0}) * α)) (Om 1) := by
  have hseg := seg_GG (S := S) (good_W S) dvd_rfl (Pv_W S)
  have e1 : 1 + (α - 1) = α := Ordinal.add_sub_cancel_of_le hα1
  have hb : α - 1 ≤ Zu S W W := by rw [Zu_W]; exact (Ordinal.sub_le_self _ _).trans hα
  have := hseg (α - 1) hb
  rw [e1] at this
  show GG α = Pv S (W * α)
  rw [← this, ← e1, mul_add, mul_one, e1]

/-- `Φ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}·Φ_Γ)`. -/
theorem PhiG_eq_mul (S : InaccSeq.{0}) :
    PhiG = S.psi (Om ω + ConjT.th S * (Om 1 ^ Om (1 : Ordinal.{0}) * PhiG)) (Om 1) := by
  rw [← GG_eq S one_le_PhiG le_rfl, PhiG_fp]

/-- **The name of `Φ_Γ`**: `Φ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1})`. -/
theorem PhiG_eq (S : InaccSeq.{0}) :
    PhiG = S.psi (Om ω + ConjT.th S * Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1) := by
  have hP := (PhiG_eq_mul S).symm
  change Pv S (W * PhiG) = PhiG at hP
  have hPSC : SC PhiG := by rw [← hP]; exact Pv_SC S _
  have hP1 : PhiG < Om 1 := by rw [← Om1_eq]; exact PhiG_lt_Om1
  have hWΩ : Om (1 : Ordinal.{0}) ^ (Om (1 : Ordinal.{0}) + 1) = W * Om 1 := by
    rw [opow_add, opow_one]
  change PhiG = Pv S (Om 1 ^ (Om 1 + 1))
  rw [hWΩ]
  refine le_antisymm ?_ ?_
  · have hP1' : PhiG ≤ Om 1 := hP1.le
    calc PhiG = Pv S (W * PhiG) := hP.symm
      _ ≤ Pv S (W * Om 1) := Pv_mono (by gcongr)
  · refine psi_le_of_key hPSC fun e he hea => ?_
    rcases lt_or_ge e (Om (ω : Ordinal.{0})) with he1 | he1
    · calc S.psi e (Om 1) ≤ Pv S 0 := by rw [Pv, A_zero]; exact (psi_mono Low.InR_Om_one he1.le).1
        _ ≤ Pv S W := Pv_mono zero_le
        _ = LamG := by rw [Pv_W, GG_one]
        _ < PhiG := LamG_lt_PhiG
    obtain ⟨η, hη, k1, k2⟩ := quotA hP1 he he1
    have hψ : S.psi e (Om 1) ≤ Pv S (η + 1) := by
      rw [Pv, ← ConjT.A_succ]; exact (psi_mono Low.InR_Om_one k2.le).1
    have hηlt : η < W * Om 1 := A_lt_A_iff.1 (k1.trans_lt hea)
    obtain ⟨q, z, r, hz, hr, hq⟩ := linvG_HCl hPSC hP1 le_rfl hη
    have hq0 : q = 0 := by
      by_contra hq0
      have : W * Om 1 ≤ η := by
        rw [hq, ← hWΩ, add_assoc]
        exact (le_mul_left _ (pos_iff_ne_zero.2 hq0)).trans le_self_add
      exact absurd hηlt (not_lt.2 this)
    rw [hq0, mul_zero, zero_add] at hq
    have hle : η + 1 ≤ W * (z + 1) := by
      rw [hq, add_assoc, mul_add_one]
      exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hr)
    have hz1 : z + 1 < PhiG := hPSC.add_one_lt hz
    calc S.psi e (Om 1) ≤ Pv S (η + 1) := hψ
      _ ≤ Pv S (W * (z + 1)) := Pv_mono hle
      _ = GG (z + 1) := (GG_eq S (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le (lt_add_one z)))
            hz1.le).symm
      _ < GG PhiG := GG_strictMono hz1
      _ = PhiG := PhiG_fp

/-- `υ_{Φ_Γ} = Φ_Γ = ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1})`. -/
theorem ups_PhiG_eq (S : InaccSeq.{0}) :
    upsilon PhiG = S.psi (Om ω + ConjT.th S * Om 1 ^ (Om (1 : Ordinal.{0}) + 1)) (Om 1) := by
  rw [PhiG_ups]; exact PhiG_eq S

end Googology.Trans.PoR.InaccPsi.R2.Nm
