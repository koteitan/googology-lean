import Googology.Trans.PoR.InaccPsi.R2.TaRoad

/-!
# The Veblen levels below `K = ψ_{Ω₁}(Ω_ω)`: the common lower bound of all restarts

`φ = veblen`, `W^E = Ω₂^E` (`Le.leWe`), `Ω^x = Ω₁^x` (`Le.leOe`), codes = `Le.LeCl κ Q`, `ρ_λ = υ_λ`,
`Θ = gxTh ρ_λ (ldAtR λ)`, `K = tdK S = ψ_{Ω₁}(Ω_ω) = P(0)`.  Every restart `ρ_λ` of the range is `P(η_λ) =
ψ_{Ω₁}(Ω_ω + θ·η_λ) ≥ K`, so `K` is a lower bound common to all `ρ_λ` (`tdK_le_rho`).  A **level below `K`**
(`TdSm S a`) is `1 ≤ a < K`; it replaces `Ta.TaSm` (`1 ≤ a < Γ₀`): it is a code over every `Q ≥ K`, a member of
every closure whose bound is at least `K`, a member of every hull `H_λ`, fixed by every reading `Θ` (as
`a < ρ_λ`) and by every base change `B_n` (as `a < L(n+1)`).

* `tdK_SC`, `tdK_lt_Om1`, `tdK_le_rho` (**`K ≤ ρ_λ` for every restart of the range**), `tdK_lt_L` (`K < L(ξ)`),
  `tdK_le_psi2` (`K ≤ ψ_{Ω₂}(x)`), `tdGam_le_K` (`Γ₀ ≤ K`);
* `tdSm_lt`, `tdSm_ne0`, `tdSm_lt_Om1`, `tdSm_lt_Om2`, `tdTh_K` (`K ≤ x ⇒ K ≤ Θ x`);
* `tdHull_idx` (**the index of a member of a closure is a member, at EVERY level `a`**: the bound of
  `Ta.taHull_idx` is not needed, since a strongly critical `z ≤ a` with `φ(a, 0) ≤ z` is `φ(a, 0)` itself).

No new axiom.  New definitions: `tdK`, `TdSm`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Td

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ta

variable {S : InaccSeq.{0}}

/-- **The common lower bound of the restarts**: `K = ψ_{Ω₁}(Ω_ω) = P(0)`. -/
noncomputable def tdK (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om ω) (Om 1)

/-- **A level below `K`**: `1 ≤ a < K`. -/
def TdSm (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop := 1 ≤ a ∧ a < tdK S

theorem tdK_SC : SC (tdK S) := SC_psi Low.InR_Om_one _

theorem tdK_lt_Om1 : tdK S < Om 1 := psi_lt Low.InR_Om_one _

theorem tdK_lt_Om2 : tdK S < Om (1 + 1) := tdK_lt_Om1.trans gg_Om1_lt_Om2

/-- `Γ₀ ≤ K`. -/
theorem tdGam_le_K : gamma 0 ≤ tdK S := taGam_le_SC tdK_SC

/-- **`K ≤ ρ_λ` for every restart `λ` of the range** (`ρ_λ = P(η_λ) = ψ_{Ω₁}(Ω_ω + θ·η_λ)`). -/
theorem tdK_le_rho {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    tdK S ≤ upsilon l := by
  rw [← cdEta_pv (S := S) hl.1 hX]
  exact (psi_mono (S := S) Low.InR_Om_one (le_self_add : Om ω ≤ Om ω + ConjT.th S * Cd.cdEta S l)).1

/-- `K < L(ξ)`. -/
theorem tdK_lt_L (ξ : Ordinal.{0}) : tdK S < Nc.ncL S ξ := by
  unfold tdK Nc.ncL
  have hlt : Om ω < Om ω + Om ω + Nc.ncPp S * ξ :=
    (lt_add_of_pos_right _ (Om_pos omega0_ne_zero)).trans_le le_self_add
  have hSC : SC (S.psi (Om ω + Om ω + Nc.ncPp S * ξ) (Om 1)) := SC_psi Low.InR_Om_one _
  have hω : ω ∈ S.CSet (Om ω + Om ω + Nc.ncPp S * ξ) (S.psi (Om ω + Om ω + Nc.ncPp S * ξ) (Om 1)) :=
    CSet.of_lt (Lw.lw_omega_lt_SC hSC)
  exact psi_lt_psi_of_mem Low.InR_Om_one hlt (CSet.Om_mem hω)

/-- `K ≤ ψ_{Ω₂}(x)`. -/
theorem tdK_le_psi2 (x : Ordinal.{0}) : tdK S ≤ S.psi x (Om (1 + 1)) :=
  (tdK_lt_Om1.trans Rw.rwO_lt_G).le.trans (psi_mono (S := S) (InR_Om_succ 1) zero_le).1

theorem tdK_le_G3 : tdK S ≤ S.psi 0 (Om (1 + 1 + 1)) :=
  (tdK_lt_Om2.trans Rw.rwW_lt_G3).le

theorem tdSm_lt {a Q : Ordinal.{0}} (ha : TdSm S a) (hQ : tdK S ≤ Q) : a < Q := ha.2.trans_le hQ

theorem tdSm_ne0 {a : Ordinal.{0}} (ha : TdSm S a) : a ≠ 0 := (zero_lt_one.trans_le ha.1).ne'

theorem tdSm_lt_Om1 {a : Ordinal.{0}} (ha : TdSm S a) : a < Om 1 := ha.2.trans tdK_lt_Om1

theorem tdSm_lt_Om2 {a : Ordinal.{0}} (ha : TdSm S a) : a < Om (1 + 1) := ha.2.trans tdK_lt_Om2

/-- A level below `K` lies in every closure whose bound is at least `K`. -/
theorem tdSm_mem {a A c : Ordinal.{0}} (ha : TdSm S a) (hc : tdK S ≤ c) : a ∈ S.CSet A c :=
  CSet.of_lt (ha.2.trans_le hc)

/-- **`K ≤ Θ x` for `x ≥ K`.** -/
theorem tdTh_K {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {x : Ordinal.{0}}
    (hx : tdK S ≤ x) : tdK S ≤ gxTh (upsilon l) (ldAtR S l) x := by
  have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hx
  rwa [gxTh_small (tdK_le_rho hl hX)] at h

/-- **The index of a member of a closure is a member**, at every level `a`. -/
theorem tdHull_idx {A B a c : Ordinal.{0}} (hc : c ∈ S.CSet A B) (h0 : veblen a 0 ≤ c) :
    ∃ u ∈ S.CSet A B, veblen a u ≤ c ∧ c < veblen a (u + 1) := by
  have hSC : ∀ z, SC z → z ∈ S.CSet A B → veblen a 0 ≤ z →
      ∃ u ∈ S.CSet A B, veblen a u ≤ z ∧ z < veblen a (u + 1) := by
    intro z hz hzm hz0
    rcases lt_or_ge a z with haz | hza
    · exact ⟨z, hzm, taIdx_SC hz haz⟩
    · have he : z = veblen a 0 := le_antisymm (hza.trans (left_le_veblen a 0)) hz0
      refine ⟨0, CSet.zero_mem _ _, hz0, ?_⟩
      rw [he, zero_add]; exact (veblen_lt_veblen_iff_right).2 zero_lt_one
  revert h0
  induction hc with
  | @small x hx =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, CSet.of_lt (((right_le_veblen a u).trans h1).trans_lt hx), h1, h2⟩
  | zero => intro h0; exact absurd h0 (not_le.2 veblen_pos)
  | inacc n => intro h0; exact hSC _ (SC_I n) (Clos.inacc n) h0
  | inaccW => intro h0; exact hSC _ SC_Iw Clos.inaccW h0
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin a 0
    by_cases hxa : veblen a 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin a _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin a _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hq0 : veblen a 0 ≤ q := by
        by_contra hq
        push Not at hq
        have : veblen p q < veblen a 0 := by
          calc veblen p q < veblen p (veblen a 0) := (veblen_lt_veblen_iff_right).2 hq
            _ = veblen a 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen a (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen a (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, Clos.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @om x hx _ =>
    intro h0
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at h0; exact absurd h0 (not_le.2 veblen_pos)
    · exact hSC _ (SC_Om hx0) (Clos.om hx) h0
  | @coll π e hπ hπC heC _ _ =>
    intro h0
    exact hSC _ (SC_psi hπ e.1) (Clos.coll hπ hπC heC) h0

end Googology.Trans.PoR.InaccPsi.R2.Td
