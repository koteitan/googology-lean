import Googology.Trans.PoR.InaccPsi.R2.ZhSup

/-!
# Zh: the short predicted reach and CapV at the restarts with a short last exponent

Below `ν_C` the closed points of `λ` start with the interval `[δ_λ, δ_λ·2)` (`Zh.zhDense`).  So:

* `zhR_short_theta` (**the short value**): `ρ_λ < ν_C` and `Θ_λ(m_λ) < δ_λ` give `r(λ) = δ_λ + Θ_λ(m_λ)`;
* `zhCapB_eq`: for a name `η_λ` with last exponent `e < ρ_λ`, the cap is `P(η_λ + ω^e) = υ_{λ+ω^e}`
  (`Cp.cpIota_add`);
* `zhCapV_short` (**CapV at the restarts with `2 ≤ e(η_λ) < ρ_λ`**): `r(λ) = δ_λ + (-1+e) < υ_{λ+ω^e}`.  This is the
  case of REFUTE FIRST "CapV at the first range restart of `W₁`" (name `Ω_ω + P' + ω²`, `e = 2`): CapV holds
  there as soon as `ρ_λ < ν_C`;
* `zhCapV_win`: the same at every range restart of a window `W_k` with `2 ≤ e < ρ_λ`, given `L(k+1) ≤ ν_C`
  (a conclusion of the window induction).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The short value below `ν_C`**: `Θ_λ(m_λ) < δ_λ` gives `r(λ) = δ_λ + Θ_λ(m_λ)`. -/
theorem zhR_short_theta {l : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hθ : cdTheta S l (cdCode S l) < cdDelta l) :
    cdR S l = cdDelta l + cdTheta S l (cdCode S l) := by
  unfold cdR cdRc
  exact cdk_interval (fun x hx => zhDense hl hν (lt_of_le_of_lt hx hθ)) _ le_rfl

/-- **The cap at a short last exponent**: `P(η_λ + ω^e) = υ_{λ+ω^e}` for `e < ρ_λ`. -/
theorem zhCapB_eq {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hn : upsilon l < Nm.Pv S η1)
    (heρ : cdExp (cdEta S l) < upsilon l) :
    cdCapB S l = upsilon (l + ω ^ cdExp (cdEta S l)) := by
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hn
  have hE : InE (upsilon l) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
  have hωe : ω ^ cdExp (cdEta S l) < upsilon l := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 heρ
    rwa [hE] at this
  unfold cdCapB
  have h := Bt.ups_iota S (cdEta S l + ω ^ cdExp (cdEta S l))
  rw [Cp.cpIota_add hg (hpv ▸ hωe), hι] at h
  exact h.symm

/-- **CapV at a restart with `2 ≤ e(η_λ) < ρ_λ`** (below `ν_C`). -/
theorem zhCapV_short {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hn : upsilon l < Nm.Pv S η1) (he2 : ω ^ 2 ≤ ω ^ cdExp (cdEta S l))
    (heρ : cdExp (cdEta S l) < upsilon l) : CdCapV S l := by
  have hm := upsilon_normal.strictMono
  have h1 : upsilon l < Om (1 + 1) :=
    (hn.trans (Nm.Pv_lt_Om1 S η1)).trans (Om_lt_Om.2 (lt_add_one (1 : Ordinal.{0})))
  have hcode : cdCode S l = cdOff (cdExp (cdEta S l)) := cdCodeOf_of_lt (heρ.trans h1)
  have hcle : cdCode S l ≤ upsilon l := hcode ▸ (cdOff_le _).trans heρ.le
  have hR := zhR_short_all hl hν hcle
  unfold CdCapV
  rw [hR, zhCapB_eq hl hn heρ]
  have hlt : l + ω + 1 < l + ω ^ cdExp (cdEta S l) := by
    rw [add_assoc]
    refine Lr.lr_addL (a := l) (lt_of_lt_of_le ?_ he2)
    simpa using Lr.lr_omega_mul_add_one_lt 1
  have hpos : 0 < l + ω ^ cdExp (cdEta S l) := lt_of_le_of_lt zero_le hlt
  have hI := indec_of_upsPt (upsPt_upsilon hpos)
  have hcl : cdCode S l < upsilon (l + ω ^ cdExp (cdEta S l)) :=
    hcle.trans_lt (hm (lt_add_of_pos_right l (opow_pos _ omega0_pos)))
  exact hI.add_lt (hm hlt) hcl

/-- **CapV at the range restarts of `W_k` with a short last exponent**, given `L(k+1) ≤ ν_C`. -/
theorem zhCapV_win (k : ℕ) (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC) {l : Ordinal.{0}}
    (hr : CdRange S l) (hw : Wj.WjWin S k l) (he2 : ω ^ 2 ≤ ω ^ cdExp (cdEta S l))
    (heρ : cdExp (cdEta S l) < upsilon l) : CdCapV S l := by
  have hlt : upsilon l < Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) := hw.2
  refine zhCapV_short (η1 := Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) hr.1 (hlt.trans_le hν) ?_ he2 heρ
  rw [Lw.lw_L_eq S] at hlt
  exact hlt

end Googology.Trans.PoR.InaccPsi.R2.Zh
