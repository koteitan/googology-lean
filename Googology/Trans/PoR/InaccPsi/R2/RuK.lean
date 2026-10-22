import Googology.Trans.PoR.InaccPsi.R2.RuLift

/-!
# The lift `κ` of the codes over `Θ(Ω₂)` below `Γ_{Ω₁+1}` to codes of level 2

`Θ = gxTh Z At` (codes over a strongly critical `Z < Ω₁` with the atoms `At`), `Z₂ = Θ(Ω₂)`, `ggGam` the least
strongly critical ordinal above `Ω₁` (`= Γ_{Ω₁+1}`), `φ = veblen`.

* `ruInv Z At g` (**the code read as `g`**): for `g < Θ(m)` it is a code `< m` with `Θ(ruInv g) = g`
  (`ruInv_spec`), strictly increasing in `g` (`ruInv_lt`), `ruInv 0 = 0`;
* `ruK Z At ζ` (**the lift**): `ruInv ζ` for `ζ < Ω₁`, `Ω₂` at `Ω₁`, `κ(ω^ℓ·n + r) = ω^{κ ℓ}·n + κ r` (Cantor
  normal form, `ℓ = log_ω ζ < ζ`) and `κ(φ(a, b)) = φ(κ a, κ b)` at an `ε`-number `ζ = φ(a, b)`, `a, b < ζ`
  (`a = invVeblen₁ ζ`, `b = invVeblen₂ ζ`);
* `RuDom Z At ζ` (**the domain**: `ζ < ggGam` is a code over `Z₂`), `ruCNF`, `ruEpsD` (the two normal forms and
  their parts), `ruDec`, `ruDecV` (the lift on them), `ruK_ge` (`Ω₂ ≤ κ ζ` for `ζ ≥ Ω₁`), `ruK_ne_zero`,
  `ruK_eps` (`κ` keeps `ε`-numbers), `ruK_opow` (`κ(ω^ℓ) = ω^{κ ℓ}`),
  `ruK_mono` (**`κ` is strictly increasing on the domain**), `ruK_mem` (**`κ ζ` lies in every `Cl(a, b)` that
  contains the codes `ruInv g`, `g < T`, when `ζ` is a code over `T`**), `ruK_lt` (`κ ζ` is below every strongly
  critical `X > Ω₂`), `ruK_pos`.

No new axiom.  New definitions: `ruInv`, `ruK`, `RuDom`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ru

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ld

variable {S : InaccSeq.{0}}

open Classical in
/-- **The code read as `g`.** -/
noncomputable def ruInv (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (g : Ordinal.{0}) : Ordinal.{0} :=
  if h : ∃ c, GxCl Z At c ∧ gxTh Z At c = g then Classical.choose h else 0

section Inv

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}}

theorem ruCode_inj {c c' : Ordinal.{0}} (hc : GxCl Z At c) (hc' : GxCl Z At c')
    (e : gxTh Z At c = gxTh Z At c') : c = c' := by
  rcases lt_trichotomy c c' with h | h | h
  · exact absurd e (gxTh_lt hc h).ne
  · exact h
  · exact absurd e.symm (gxTh_lt hc' h).ne

theorem ruInv_spec {g m : Ordinal.{0}} (hg : g < gxTh Z At m) :
    GxCl Z At (ruInv Z At g) ∧ ruInv Z At g < m ∧ gxTh Z At (ruInv Z At g) = g := by
  obtain ⟨c, hc, hcm, e⟩ := gxTh_onto hg
  have h : ∃ c, GxCl Z At c ∧ gxTh Z At c = g := ⟨c, hc, e⟩
  have hdef : ruInv Z At g = Classical.choose h := by unfold ruInv; rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  have heq : Classical.choose h = c := ruCode_inj h1 hc (h2.trans e.symm)
  rw [hdef, heq]
  exact ⟨hc, hcm, e⟩

theorem ruInv_lt {g g' m : Ordinal.{0}} (hg : g < gxTh Z At m) (h : g' < g) :
    ruInv Z At g' < ruInv Z At g := by
  obtain ⟨-, -, e⟩ := ruInv_spec hg
  obtain ⟨-, -, e'⟩ := ruInv_spec (h.trans hg)
  by_contra hle
  push Not at hle
  have := gxTh_mono (Z := Z) (At := At) hle
  rw [e, e'] at this
  exact absurd h (not_lt.2 this)

theorem ruInv_zero (hZ : 0 < Z) : ruInv Z At 0 = 0 := by
  have h : ∃ c, GxCl Z At c ∧ gxTh Z At c = 0 := ⟨0, GxCl.zero hZ, gxTh_zero⟩
  unfold ruInv
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  exact ruCode_inj h1 (GxCl.zero hZ) (h2.trans gxTh_zero.symm)

end Inv

/-- **The lift** of a code over `Θ(Ω₂)` below `Γ_{Ω₁+1}` to a code of level 2. -/
noncomputable def ruK (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (ζ : Ordinal.{0}) : Ordinal.{0} :=
  if _h1 : ζ < Om 1 then ruInv Z At ζ
  else if ζ = Om 1 then Om (1 + 1)
  else if _h3 : log ω ζ < ζ then
    ω ^ ruK Z At (log ω ζ) * (ζ / ω ^ log ω ζ) + ruK Z At (ζ % ω ^ log ω ζ)
  else if _h4 : invVeblen₁ ζ < ζ ∧ invVeblen₂ ζ < ζ then
    veblen (ruK Z At (invVeblen₁ ζ)) (ruK Z At (invVeblen₂ ζ))
  else 0
termination_by ζ
decreasing_by
  · exact _h3
  · exact mod_opow_log_lt_self ω (((Om_pos one_ne_zero).trans_le (not_lt.1 _h1)).ne')
  · exact _h4.1
  · exact _h4.2

/-- **The domain** of the lift: the codes over `Θ(Ω₂)` below `Γ_{Ω₁+1}`. -/
def RuDom (Z : Ordinal.{0}) (At : Set Ordinal.{0}) (ζ : Ordinal.{0}) : Prop :=
  GgCl (gxTh Z At (Om (1 + 1))) ζ ∧ ζ < ggGam

section K

variable {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hZ1 : Z < Om 1) (hAt : GxAt At)

theorem ruOm2_eps : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC

theorem ruLog_Om1 : log ω (Om (1 : Ordinal.{0})) = Om 1 := by
  conv_lhs => rw [← Om1_opow]
  exact log_opow one_lt_omega0 _

theorem ruLog_eps {ζ : Ordinal.{0}} (hε : ω ^ ζ = ζ) : log ω ζ = ζ := by
  conv_lhs => rw [← hε]
  exact log_opow one_lt_omega0 _

theorem ruK_lt_Om1 {ζ : Ordinal.{0}} (h : ζ < Om 1) : ruK Z At ζ = ruInv Z At ζ := by
  rw [ruK, dif_pos h]

theorem ruK_Om1 : ruK Z At (Om 1) = Om (1 + 1) := by
  rw [ruK, dif_neg (lt_irrefl _), if_pos rfl]

theorem ruK_zero (hZ0 : 0 < Z) : ruK Z At 0 = 0 := by
  rw [ruK_lt_Om1 (Om_pos one_ne_zero), ruInv_zero hZ0]

theorem ruK_gt {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (h3 : log ω ζ < ζ) :
    ruK Z At ζ = ω ^ ruK Z At (log ω ζ) * (ζ / ω ^ log ω ζ) + ruK Z At (ζ % ω ^ log ω ζ) := by
  rw [ruK, dif_neg (not_lt.2 h1.le), if_neg h1.ne', dif_pos h3]

theorem ruK_veb {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (hε : ω ^ ζ = ζ)
    (h4 : invVeblen₁ ζ < ζ ∧ invVeblen₂ ζ < ζ) :
    ruK Z At ζ = veblen (ruK Z At (invVeblen₁ ζ)) (ruK Z At (invVeblen₂ ζ)) := by
  rw [ruK, dif_neg (not_lt.2 h1.le), if_neg h1.ne', dif_neg (by rw [ruLog_eps hε]; exact lt_irrefl _),
    dif_pos h4]

/-- The logarithm of a `ζ > Ω₁` that is not an `ε`-number is below `ζ`. -/
theorem ruLog_lt {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (hne : ω ^ ζ ≠ ζ) : log ω ζ < ζ := by
  refine lt_of_le_of_ne (log_le_self ω ζ) fun e => hne ?_
  have h0 : ζ ≠ 0 := ((Om_pos one_ne_zero).trans h1).ne'
  have hle : ω ^ ζ ≤ ζ := by
    have := opow_log_le_self ω h0; rwa [e] at this
  exact le_antisymm hle (right_le_opow ζ one_lt_omega0)

/-- `φ(ζ, 0) = ζ` makes `ζ > 0` strongly critical. -/
theorem ruSC_of_veblen {ζ : Ordinal.{0}} (h0 : 0 < ζ) (h : veblen ζ 0 = ζ) : SC ζ := by
  refine ⟨h0, fun x hx y hy => ?_⟩
  have e : veblen x ζ = ζ := by
    have := veblen_veblen_of_lt hx 0; rwa [h] at this
  calc veblen x y < veblen x ζ := veblen_lt_veblen_iff_right.2 hy
    _ = ζ := e

/-- **The Veblen normal form of an `ε`-number in `(Ω₁, ggGam)`**: `ζ = φ(a, b)`, `0 < a < ζ`, `b < ζ`. -/
theorem ruVeb {ζ : Ordinal.{0}} (h1 : Om 1 < ζ) (hG : ζ < ggGam) (hε : ω ^ ζ = ζ) :
    veblen (invVeblen₁ ζ) (invVeblen₂ ζ) = ζ ∧ 0 < invVeblen₁ ζ ∧ invVeblen₁ ζ < ζ ∧
      invVeblen₂ ζ < ζ := by
  have hv : veblen (invVeblen₁ ζ) (invVeblen₂ ζ) = ζ := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ ζ < ζ := by have := invVeblen₂_lt ζ; rwa [hε] at this
  have hpos : 0 < ζ := (Om_pos one_ne_zero).trans h1
  refine ⟨hv, ?_, ?_, hb⟩
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, veblen_zero_apply] at hv
    have : invVeblen₂ ζ = ζ := by
      have h2 : ω ^ invVeblen₂ ζ = ω ^ ζ := hv.trans hε.symm
      exact (opow_right_inj one_lt_omega0).1 h2
    exact absurd this hb.ne
  · refine lt_of_le_of_ne (invVeblen₁_le ζ) fun e => ?_
    rw [e] at hv
    have hle : veblen ζ 0 ≤ ζ := (veblen_le_veblen_iff_right.2 zero_le).trans hv.le
    have hSC := ruSC_of_veblen hpos (le_antisymm hle (left_le_veblen ζ 0))
    exact absurd (ggGam_le hSC h1) (not_le.2 hG)

include hZ hZ1 hAt

theorem ruZ2_SC : SC (gxTh Z At (Om (1 + 1))) :=
  gxTh_SC hZ hAt ldOm2_SC (hZ1.trans gg_Om1_lt_Om2)

/-- **The Cantor normal form of a member of the domain `≥ Ω₁` and its parts.** -/
theorem ruCNF {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h1 : Om 1 ≤ ζ) :
    ∃ n : ℕ, 1 ≤ n ∧ ζ / ω ^ log ω ζ = n ∧ ζ = ω ^ log ω ζ * n + ζ % ω ^ log ω ζ ∧
      RuDom Z At (log ω ζ) ∧ RuDom Z At (ζ % ω ^ log ω ζ) ∧ RuDom Z At (ω ^ log ω ζ) ∧
      ζ % ω ^ log ω ζ < ω ^ log ω ζ ∧ ω ^ log ω ζ ≤ ζ ∧ Om 1 ≤ log ω ζ := by
  have hZ2 := ruZ2_SC hZ hZ1 hAt
  have h0 : ζ ≠ 0 := ((Om_pos one_ne_zero).trans_le h1).ne'
  obtain ⟨hg, hE⟩ := hζ
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt ζ one_lt_omega0)
  have hpos : (0 : Ordinal.{0}) < ω ^ log ω ζ := opow_pos _ omega0_pos
  have hopζ : ω ^ log ω ζ ≤ ζ := opow_log_le_self ω h0
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hlt : ζ < ω ^ log ω ζ * 1 :=
        (Ordinal.lt_mul_iff_div_lt hpos.ne').2 (by rw [hn, h]; exact zero_lt_one)
      rw [mul_one] at hlt
      exact absurd hopζ (not_le.2 hlt)
    · exact h
  have hdm : ζ = ω ^ log ω ζ * n + ζ % ω ^ log ω ζ := by
    rw [← hn]; exact (Ordinal.div_add_mod ζ _).symm
  have hℓ1 : Om 1 ≤ log ω ζ := le_log_of_opow_le one_lt_omega0 (by rw [Om1_opow]; exact h1)
  have hlog : GgCl (gxTh Z At (Om (1 + 1))) (log ω ζ) := (ggDec hZ2 ζ hg).2
  have hopow : GgCl (gxTh Z At (Om (1 + 1))) (ω ^ log ω ζ) := GgCl.opow hZ2.1 hlog
  have hmul : GgCl (gxTh Z At (Om (1 + 1))) (ω ^ log ω ζ * n) := GgCl.mul_nat hZ2.1 hopow n
  have hrem : GgCl (gxTh Z At (Om (1 + 1))) (ζ % ω ^ log ω ζ) := by
    have := (ggDec hZ2 ζ hg).1 _ hmul (le_self_add.trans_eq hdm.symm)
    have e : ζ - ω ^ log ω ζ * n = ζ % ω ^ log ω ζ := by
      have e0 := Ordinal.add_sub_cancel (ω ^ log ω ζ * n) (ζ % ω ^ log ω ζ)
      rwa [← hdm] at e0
    rwa [e] at this
  exact ⟨n, hn1, hn, hdm, ⟨hlog, (log_le_self ω ζ).trans_lt hE⟩,
    ⟨hrem, ((Ordinal.mod_le ζ _).trans_lt hE)⟩, ⟨hopow, hopζ.trans_lt hE⟩,
    Ordinal.mod_lt ζ hpos.ne', hopζ, hℓ1⟩

/-- **The Veblen normal form of an `ε`-number of the domain above `Ω₁` and its parts.** -/
theorem ruEpsD {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h1 : Om 1 < ζ) (hε : ω ^ ζ = ζ) :
    veblen (invVeblen₁ ζ) (invVeblen₂ ζ) = ζ ∧ 0 < invVeblen₁ ζ ∧ invVeblen₁ ζ < ζ ∧
      invVeblen₂ ζ < ζ ∧ RuDom Z At (invVeblen₁ ζ) ∧ RuDom Z At (invVeblen₂ ζ) ∧
      ruK Z At ζ = veblen (ruK Z At (invVeblen₁ ζ)) (ruK Z At (invVeblen₂ ζ)) := by
  obtain ⟨hv, ha0, ha, hb⟩ := ruVeb h1 hζ.2 hε
  obtain ⟨hga, hgb⟩ := Ph.phDec (ruZ2_SC hZ hZ1 hAt).1 hζ.1 _ _ hv hb
  exact ⟨hv, ha0, ha, hb, ⟨hga, ha.trans hζ.2⟩, ⟨hgb, hb.trans hζ.2⟩, ruK_veb h1 hε ⟨ha, hb⟩⟩

/-- **`Ω₂ ≤ κ ζ` for `ζ ≥ Ω₁` in the domain.** -/
theorem ruK_ge : ∀ ζ, RuDom Z At ζ → Om 1 ≤ ζ → Om (1 + 1) ≤ ruK Z At ζ := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ h1
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, ruK_Om1]
  by_cases hε : ω ^ ζ = ζ
  · obtain ⟨hv, -, ha, hb, haD, hbD, hK⟩ := ruEpsD hZ hZ1 hAt hζ h1 hε
    rw [hK]
    by_cases hab : Om 1 ≤ invVeblen₁ ζ
    · exact (IH _ ha haD hab).trans (left_le_veblen _ _)
    · by_cases hbb : Om 1 ≤ invVeblen₂ ζ
      · exact (IH _ hb hbD hbb).trans (right_le_veblen _ _)
      · push Not at hab hbb
        have := Ph.ph_SC_Om1.2 _ hab _ hbb
        rw [hv] at this
        exact absurd h1 (not_lt.2 this.le)
  · obtain ⟨n, hn1, hn, -, hℓ, -, -, -, -, hℓ1⟩ := ruCNF hZ hZ1 hAt hζ h1.le
    have hlt := ruLog_lt h1 hε
    rw [ruK_gt h1 hlt, hn]
    calc Om (1 + 1) = ω ^ Om (1 + 1) := ruOm2_eps.symm
      _ ≤ ω ^ ruK Z At (log ω ζ) := opow_le_opow_right omega0_pos (IH _ hlt hℓ hℓ1)
      _ ≤ ω ^ ruK Z At (log ω ζ) * n := le_mul_left _ (by exact_mod_cast hn1)
      _ ≤ _ := le_self_add

theorem ruK_ne_zero {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h0 : ζ ≠ 0) : ruK Z At ζ ≠ 0 := by
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [ruK_lt_Om1 h1]
    intro e
    obtain ⟨-, -, he⟩ := ruInv_spec (GgCl.lt_of_lt_Om1 (ruZ2_SC hZ hZ1 hAt) hζ.1 h1)
    rw [e, gxTh_zero] at he
    exact h0 he.symm
  · exact ((Om_pos (by norm_num)).trans_le (ruK_ge hZ hZ1 hAt ζ hζ h1)).ne'

/-- **`κ` keeps `ε`-numbers** at and above `Ω₁`. -/
theorem ruK_eps {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h1 : Om 1 ≤ ζ) (hε : ω ^ ζ = ζ) :
    ω ^ ruK Z At ζ = ruK Z At ζ := by
  rcases h1.lt_or_eq with h1 | e
  · obtain ⟨-, ha0, -, -, haD, -, hK⟩ := ruEpsD hZ hZ1 hAt hζ h1 hε
    rw [hK]
    exact gg_veblen_eps (ruK_ne_zero hZ hZ1 hAt haD ha0.ne')
  · rw [← e, ruK_Om1]; exact ruOm2_eps

/-- **The lift on the Cantor normal form** of a member of the domain `≥ Ω₁`. -/
theorem ruDec {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h1 : Om 1 ≤ ζ) :
    ∃ n : ℕ, 1 ≤ n ∧ ζ = ω ^ log ω ζ * n + ζ % ω ^ log ω ζ ∧
      ruK Z At ζ = ω ^ ruK Z At (log ω ζ) * n + ruK Z At (ζ % ω ^ log ω ζ) ∧
      RuDom Z At (log ω ζ) ∧ RuDom Z At (ζ % ω ^ log ω ζ) ∧ RuDom Z At (ω ^ log ω ζ) ∧
      ζ % ω ^ log ω ζ < ω ^ log ω ζ ∧ ω ^ log ω ζ ≤ ζ ∧ Om 1 ≤ log ω ζ ∧
      (ω ^ ζ = ζ ∨ log ω ζ < ζ) := by
  obtain ⟨n, hn1, hn, hdm, hℓ, hr, hop, hrlt, hopζ, hℓ1⟩ := ruCNF hZ hZ1 hAt hζ h1
  by_cases hε : ω ^ ζ = ζ
  · have hl := ruLog_eps hε
    have en : (n : Ordinal.{0}) = 1 := by
      rw [← hn, hl, hε, Ordinal.div_self ((Om_pos one_ne_zero).trans_le h1).ne']
    refine ⟨n, hn1, hdm, ?_, hℓ, hr, hop, hrlt, hopζ, hℓ1, Or.inl hε⟩
    rw [en, hl, hε, Ordinal.mod_self, ruK_zero hZ.1, add_zero, mul_one, ruK_eps hZ hZ1 hAt hζ h1 hε]
  · have hgt : Om 1 < ζ := lt_of_le_of_ne h1 fun e => hε (by rw [← e]; exact Om1_opow)
    refine ⟨n, hn1, hdm, ?_, hℓ, hr, hop, hrlt, hopζ, hℓ1, Or.inr (ruLog_lt hgt hε)⟩
    rw [← hn]; exact ruK_gt hgt (ruLog_lt hgt hε)

/-- **The lift on the Veblen normal form** of an `ε`-number of the domain `≥ Ω₁` (`Ω₁ = φ(Ω₁, 0)`). -/
theorem ruDecV {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h1 : Om 1 ≤ ζ) (hε : ω ^ ζ = ζ) :
    ∃ a b, veblen a b = ζ ∧ b < ζ ∧ a ≤ ζ ∧ RuDom Z At a ∧ RuDom Z At b ∧
      ruK Z At ζ = veblen (ruK Z At a) (ruK Z At b) ∧ (Om 1 < ζ → a < ζ) := by
  rcases h1.lt_or_eq with h1 | e
  · obtain ⟨hv, -, ha, hb, haD, hbD, hK⟩ := ruEpsD hZ hZ1 hAt hζ h1 hε
    exact ⟨_, _, hv, hb, ha.le, haD, hbD, hK, fun _ => ha⟩
  · subst e
    have hD1 : RuDom Z At (Om 1) := ⟨GgCl.om, ggGam_spec.2⟩
    have hD0 : RuDom Z At 0 := ⟨GgCl.zero (ruZ2_SC hZ hZ1 hAt).1, (Om_pos one_ne_zero).trans ggGam_spec.2⟩
    refine ⟨Om 1, 0, Ph.ph_SC_Om1.veblen_zero, Om_pos one_ne_zero, le_rfl, hD1, hD0, ?_,
      fun h => absurd h (lt_irrefl _)⟩
    rw [ruK_Om1, ruK_zero hZ.1, ldOm2_SC.veblen_zero]

/-- **`κ(ω^ℓ) = ω^{κ ℓ}`** for `ℓ ≥ Ω₁` in the domain. -/
theorem ruK_opow {ℓ : Ordinal.{0}} (hℓ : RuDom Z At ℓ) (h1 : Om 1 ≤ ℓ) :
    ruK Z At (ω ^ ℓ) = ω ^ ruK Z At ℓ := by
  by_cases hε : ω ^ ω ^ ℓ = ω ^ ℓ
  · have e : ω ^ ℓ = ℓ := (opow_right_inj one_lt_omega0).1 hε
    rw [e]; exact (ruK_eps hZ hZ1 hAt hℓ h1 e).symm
  · have hgt : Om 1 < ω ^ ℓ := lt_of_le_of_ne (h1.trans (right_le_opow ℓ one_lt_omega0))
      fun e => hε (by rw [← e]; exact Om1_opow)
    have hlog : log ω (ω ^ ℓ) = ℓ := log_opow one_lt_omega0 ℓ
    rw [ruK_gt hgt (ruLog_lt hgt hε), hlog, Ordinal.div_self (opow_pos ℓ omega0_pos).ne',
      Ordinal.mod_self, ruK_zero hZ.1, add_zero, mul_one]

/-- **`κ` is strictly increasing on the domain.** -/
theorem ruK_mono : ∀ ζ, RuDom Z At ζ → ∀ ζ', RuDom Z At ζ' → ζ' < ζ → ruK Z At ζ' < ruK Z At ζ := by
  have hZ2 := ruZ2_SC hZ hZ1 hAt
  have hcnt : ∀ y, RuDom Z At y → y < Om 1 → y < gxTh Z At (Om (1 + 1)) := fun y hy h =>
    GgCl.lt_of_lt_Om1 hZ2 hy.1 h
  have hinvlt : ∀ y, RuDom Z At y → y < Om 1 → ruK Z At y < Om (1 + 1) := fun y hy h => by
    rw [ruK_lt_Om1 h]; exact (ruInv_spec (hcnt y hy h)).2.1
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ ζ'
  induction ζ' using WellFoundedLT.induction with
  | ind ζ' IH' =>
  intro hζ' hlt
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [ruK_lt_Om1 h1, ruK_lt_Om1 (hlt.trans h1)]
    exact ruInv_lt (hcnt ζ hζ h1) hlt
  rcases lt_or_ge ζ' (Om 1) with h1' | h1'
  · exact (hinvlt ζ' hζ' h1').trans_le (ruK_ge hZ hZ1 hAt ζ hζ h1)
  have hζ1 : Om 1 < ζ := h1'.trans_lt hlt
  by_cases hboth : ω ^ ζ = ζ ∧ ω ^ ζ' = ζ'
  · -- two `ε`-numbers: the Veblen comparison
    obtain ⟨a, b, hab, hb, -, haD, hbD, hK, hane⟩ := ruDecV hZ hZ1 hAt hζ h1 hboth.1
    obtain ⟨a', b', hab', hb', ha'le, ha'D, hb'D, hK', -⟩ := ruDecV hZ hZ1 hAt hζ' h1' hboth.2
    have ha : a < ζ := hane hζ1
    rw [hK, hK']
    have hlt' := hlt
    rw [← hab, ← hab'] at hlt'
    rcases veblen_lt_veblen_iff.1 hlt' with ⟨e, h⟩ | ⟨h, h2⟩ | ⟨h, h2⟩
    · rw [e]
      exact veblen_lt_veblen_iff_right.2 (IH b hb hbD b' hb'D h)
    · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨IH a ha haD a' ha'D h, ?_⟩))
      rw [← hK]
      exact IH' b' hb' hb'D (hb'.trans hlt)
    · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inr ⟨IH a' (ha'le.trans_lt hlt) ha'D a haD h, ?_⟩))
      rw [← hK']
      rw [hab'] at h2
      exact IH b hb hbD ζ' hζ' h2
  · -- the Cantor normal form
    obtain ⟨n, hn1, hdm, hK, hℓ, hr, hop, hrlt, hopζ, hℓ1, hcase⟩ := ruDec hZ hZ1 hAt hζ h1
    obtain ⟨n', hn1', hdm', hK', hℓ', hr', hop', hrlt', hopζ', hℓ1', hcase'⟩ := ruDec hZ hZ1 hAt hζ' h1'
    have hℓle : log ω ζ' ≤ log ω ζ := log_mono_right ω hlt.le
    have hrb : ruK Z At (ζ' % ω ^ log ω ζ') < ω ^ ruK Z At (log ω ζ') := by
      rw [← ruK_opow hZ hZ1 hAt hℓ' hℓ1']
      exact IH _ (hopζ'.trans_lt hlt) hop' _ hr' hrlt'
    have hK'lt : ruK Z At ζ' < ω ^ ruK Z At (log ω ζ') * ((n' : Ordinal.{0}) + 1) := by
      rw [hK', mul_add_one]; exact (add_lt_add_iff_left _).2 hrb
    have hKζ : ω ^ ruK Z At (log ω ζ) ≤ ruK Z At ζ := by
      rw [hK]; exact (le_mul_left _ (by exact_mod_cast hn1)).trans le_self_add
    rcases hℓle.lt_or_eq with hℓlt | hℓeq
    · have hKℓ : ruK Z At (log ω ζ') < ruK Z At (log ω ζ) := by
        rcases hcase with hε | hℓζ
        · have hne' : ω ^ ζ' ≠ ζ' := fun h => hboth ⟨hε, h⟩
          have hℓ'ζ' : log ω ζ' < ζ' := by
            rcases hcase' with h | h
            · exact absurd h hne'
            · exact h
          rw [ruLog_eps hε]
          exact IH' _ hℓ'ζ' hℓ' (hℓ'ζ'.trans hlt)
        · exact IH _ hℓζ hℓ _ hℓ' hℓlt
      calc ruK Z At ζ' < ω ^ ruK Z At (log ω ζ') * ((n' : Ordinal.{0}) + 1) := hK'lt
        _ ≤ ω ^ ruK Z At (log ω ζ') * ω := by
            gcongr; exact (Order.add_one_le_of_lt (natCast_lt_omega0 n')).trans_eq (by rfl)
        _ = ω ^ (ruK Z At (log ω ζ') + 1) := (opow_add_one _ _).symm
        _ ≤ ω ^ ruK Z At (log ω ζ) := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hKℓ)
        _ ≤ ruK Z At ζ := hKζ
    · rw [hℓeq] at hK'lt hdm' hrlt' hK'
      have hnle : n' ≤ n := by
        by_contra hc
        push Not at hc
        have h2 : ω ^ log ω ζ * ((n + 1 : ℕ) : Ordinal.{0}) ≤ ζ' := by
          rw [hdm']; exact (mul_le_mul_right (by exact_mod_cast hc) _).trans le_self_add
        have h3 : ζ < ω ^ log ω ζ * ((n + 1 : ℕ) : Ordinal.{0}) := by
          rw [Nat.cast_succ, mul_add_one]
          conv_lhs => rw [hdm]
          exact (add_lt_add_iff_left _).2 hrlt
        exact absurd (h3.trans_le h2) (not_lt.2 hlt.le)
      rcases hnle.lt_or_eq with hnlt | hneq
      · calc ruK Z At ζ' < ω ^ ruK Z At (log ω ζ) * ((n' : Ordinal.{0}) + 1) := hK'lt
          _ ≤ ω ^ ruK Z At (log ω ζ) * n := by
              gcongr; exact_mod_cast Nat.succ_le_of_lt hnlt
          _ ≤ ruK Z At ζ := by rw [hK]; exact le_self_add
      · subst hneq
        have hrr : ζ' % ω ^ log ω ζ < ζ % ω ^ log ω ζ := by
          have h4 := hlt
          rw [hdm, hdm'] at h4
          exact (add_lt_add_iff_left _).1 h4
        rw [hK, hK']
        refine (add_lt_add_iff_left _).2 (IH _ (hrlt.trans_le hopζ) hr _ ?_ hrr)
        rw [← hℓeq]; exact hr'

/-- **`κ ζ` lies in every `Cl(a, b)` containing the codes `ruInv g`, `g < T`**, when `ζ < ggGam` is a code over
`T`. -/
theorem ruK_mem {T a b : Ordinal.{0}} (hT : SC T) (hTZ : T ≤ gxTh Z At (Om (1 + 1)))
    (hinv : ∀ g, g < T → ruInv Z At g ∈ S.CSet a b) :
    ∀ ζ, GgCl T ζ → ζ < ggGam → ruK Z At ζ ∈ S.CSet a b := by
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ hE
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [ruK_lt_Om1 h1]; exact hinv ζ (GgCl.lt_of_lt_Om1 hT hζ h1)
  have hD : RuDom Z At ζ := ⟨hζ.mono hTZ, hE⟩
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, ruK_Om1]; exact mxOm2_mem a b
  by_cases hε : ω ^ ζ = ζ
  · obtain ⟨hv, -, ha, hb, -, -, hK⟩ := ruEpsD hZ hZ1 hAt hD h1 hε
    obtain ⟨hga, hgb⟩ := Ph.phDec hT.1 hζ _ _ hv hb
    rw [hK]
    exact CSet.phi_mem (IH _ ha hga (ha.trans hE)) (IH _ hb hgb (hb.trans hE))
  obtain ⟨n, -, hn, hdm, -, -, -, -, -, -⟩ := ruCNF hZ hZ1 hAt hD h1.le
  have hlt := ruLog_lt h1 hε
  have hlog : GgCl T (log ω ζ) := (ggDec hT ζ hζ).2
  have hmul : GgCl T (ω ^ log ω ζ * n) := GgCl.mul_nat hT.1 (GgCl.opow hT.1 hlog) n
  have hrem : GgCl T (ζ % ω ^ log ω ζ) := by
    have := (ggDec hT ζ hζ).1 _ hmul (le_self_add.trans_eq hdm.symm)
    have e : ζ - ω ^ log ω ζ * n = ζ % ω ^ log ω ζ := by
      have e0 := Ordinal.add_sub_cancel (ω ^ log ω ζ * n) (ζ % ω ^ log ω ζ)
      rwa [← hdm] at e0
    rwa [e] at this
  have hrlt : ζ % ω ^ log ω ζ < ζ := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne'
  rw [ruK_gt h1 hlt, hn]
  have h1m := IH _ hlt hlog ((log_le_self ω ζ).trans_lt hE)
  have h2m := IH _ hrlt hrem (hrlt.trans hE)
  have hop : ω ^ ruK Z At (log ω ζ) ∈ S.CSet a b := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem a b) h1m; rwa [veblen_zero_apply] at this
  exact CSet.add_mem (ConjT.mul_nat_mem S hop n) h2m

/-- **`κ ζ` is below every strongly critical `X > Ω₂`.** -/
theorem ruK_lt {X : Ordinal.{0}} (hX : SC X) (h2X : Om (1 + 1) < X) :
    ∀ ζ, RuDom Z At ζ → ruK Z At ζ < X := by
  have hZ2 := ruZ2_SC hZ hZ1 hAt
  intro ζ
  induction ζ using WellFoundedLT.induction with
  | ind ζ IH =>
  intro hζ
  rcases lt_or_ge ζ (Om 1) with h1 | h1
  · rw [ruK_lt_Om1 h1]
    exact (ruInv_spec (GgCl.lt_of_lt_Om1 hZ2 hζ.1 h1)).2.1.trans h2X
  rcases h1.lt_or_eq with h1 | e
  swap
  · rw [← e, ruK_Om1]; exact h2X
  by_cases hε : ω ^ ζ = ζ
  · obtain ⟨-, -, ha, hb, haD, hbD, hK⟩ := ruEpsD hZ hZ1 hAt hζ h1 hε
    rw [hK]
    exact hX.2 _ (IH _ ha haD) _ (IH _ hb hbD)
  obtain ⟨n, -, hn, -, hℓ, hr, -, -, -, -⟩ := ruCNF hZ hZ1 hAt hζ h1.le
  have hlt := ruLog_lt h1 hε
  have hrlt : ζ % ω ^ log ω ζ < ζ := mod_opow_log_lt_self ω ((Om_pos one_ne_zero).trans h1).ne'
  rw [ruK_gt h1 hlt, hn]
  have h1m := IH _ hlt hℓ
  have hop : ω ^ ruK Z At (log ω ζ) < X := by
    rw [← gg_SC_eps hX]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h1m
  exact hX.isPrincipal (ldMul_lt_SC hX hop ((natCast_lt_omega0 n).trans (Lw.lw_omega_lt_SC hX)))
    (IH _ hrlt hr)

/-- `0 < κ ζ` for `0 < ζ` in the domain. -/
theorem ruK_pos {ζ : Ordinal.{0}} (hζ : RuDom Z At ζ) (h0 : ζ ≠ 0) : 0 < ruK Z At ζ :=
  pos_iff_ne_zero.2 (ruK_ne_zero hZ hZ1 hAt hζ h0)

end K

end Googology.Trans.PoR.InaccPsi.R2.Ru
