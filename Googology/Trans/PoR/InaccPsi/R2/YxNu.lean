import Googology.Trans.PoR.InaccPsi.R2.YsRsAll
import Googology.Trans.PoR.InaccPsi.R2.CxTop

/-!
# Yx: the first non-standard pair is never below a capped point (strict NU-LOW″ at every height)

`Cd.cdLow` gives `L(ω) ≤ ν_C` from CAP-0 and CAP-1 below `L(ω)`.  Its proof works at every height `X ≤ L(ω)` and
gives the strict bound: if `ν_C ≤ X`, the left end `ρ_λ` of the first non-standard pair (`Lb.lbFirst`) is below
`L(ω)`, its `≤₁`-predecessors `ρ_μ ≤₁ ν_C` are restarts in the name window of `λ` with code `< P'` and cap
`≤ ρ_λ < ν_C`, and `ρ_μ < X`, so CAP-1 below `X` breaks.  Hence

* `yxNu_gt` (**CAP-0 and CAP-1 below `X ≤ L(ω)` give `X < ν_C`**);
* `yxStd_noStraddle`: no standard pair `(c, d)` has `c ≤ ρ_l ≤ d` at a restart `l`;
* `yxNext_le_nuC`: `ρ_l < ν_C ⇒ υ_{l+ω²} ≤ ν_C` (`ν_C` is a restart point);
* `yxNostr_of_lt` / `yxChainNostr_of_lt`: **the pair fields of the relative block induction at a restart `l`
  (`Ys.YsSpec.nostr`, `Ys.YsNostrIn` for every crossing bound `x₀ ≤ ρ_l`) hold as soon as `ρ_l < ν_C`**;
* `yxSpec_nu` (**REFUTE FIRST**): conversely, `Ys.YsSpec O l₀ B` excludes `ν_C` from `[ρ_{l₀}, υ_B)`: at the
  index of `ν_C` its field `nostr` fails with the first non-standard pair.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Strict NU-LOW″ at every height `X ≤ L(ω)`**: CAP-0 and CAP-1 below `X` give `X < ν_C`. -/
theorem yxNu_gt {X : Ordinal.{0}} (hX : X ≤ Nc.ncL S ω) (h0 : CdCAP0 S) (h1 : CdCAP1 S X) : X < nuC := by
  by_contra hlt
  have hνL : nuC ≤ X := not_lt.1 hlt
  obtain ⟨l, hl, -, hlν, -, -, -, hP, hW, -⟩ := Lb.lbFirst
  have hLeq : Nc.ncL S ω = Pv S (Om ω + Nc.ncPp S * ω) := Lw.lw_L_eq S ω
  have hlT : upsilon l < Pv S (Om ω + Nc.ncPp S * ω) := hLeq ▸ (hlν.trans_le (hνL.trans hX))
  have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl.1
  obtain ⟨ηt, -, hηt⟩ := iota_onto (S := S) _ l hl1 (cd_lt_iota hlT).le
  -- the least `η` with `ι(η) = λ`
  have hne : {η | iota S η = l}.Nonempty := ⟨ηt, hηt⟩
  have hηm : iota S (sInf {η | iota S η = l}) = l := csInf_mem hne
  have hmin : ∀ η < sInf {η | iota S η = l}, iota S η ≠ l := fun η h he =>
    (csInf_le' (s := {η | iota S η = l}) he).not_gt h
  generalize sInf {η | iota S η = l} = ηm at hηm hmin
  have hpvm : Pv S ηm = upsilon l := by
    calc Pv S ηm = upsilon (iota S ηm) := (ups_iota S ηm).symm
      _ = upsilon l := by rw [hηm]
  have hηm0 : ηm ≠ 0 := by
    rintro rfl
    rw [iota_zero] at hηm
    exact (ri_lim hl).succ_ne 0 (by rw [succ_eq_add_one, zero_add]; exact hηm)
  obtain ⟨η0, hdec, hdvd⟩ := cdExp_decomp hηm0
  generalize cdExp ηm = e at hdec hdvd
  have hη0m : η0 < ηm := by
    rw [hdec]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  have hν : iota S η0 < l := lt_of_le_of_ne ((iota_mono (S := S) ηm η0 hη0m.le).trans_eq hηm) (hmin η0 hη0m)
  -- a restart witness `ρ_μ ≤₁ ν_C` with `μ ∈ (ι(η₀), λ)`
  obtain ⟨y, hνy, hyl, hy⟩ := hP (upsilon (iota S η0)) (upsilon_normal.strictMono hν)
  obtain ⟨μ, hμ, hBμ, rfl, -⟩ := hW y hyl hy
  have hμν : iota S η0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνy
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 hyl
  obtain ⟨hg, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hμ.1) (hμl.trans_eq hηm.symm)
  have hpvμ : Pv S (cdEta S μ) = upsilon μ := by
    calc Pv S (cdEta S μ) = upsilon (iota S (cdEta S μ)) := (ups_iota S _).symm
      _ = upsilon μ := by rw [hιμ]
  have hx0 : η0 < cdEta S μ := by
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) η0 _ h
    rw [hιμ] at h'
    exact absurd h' (not_le.2 hμν)
  have hxm : cdEta S μ < η0 + ω ^ e := by
    rw [← hdec]
    by_contra h
    push Not at h
    have h' := iota_mono (S := S) (cdEta S μ) ηm h
    rw [hιμ, hηm] at h'
    exact absurd h' (not_le.2 hμl)
  obtain ⟨hxe, hxw⟩ := cdWin hdvd hx0 hxm
  have hμX : upsilon μ < X := (upsilon_normal.strictMono hμl).trans (hlν.trans_le hνL)
  -- the cap of `μ` is at most `ρ_λ`
  have hcapl : cdCapB S μ ≤ upsilon l := by
    unfold cdCapB
    calc Pv S (cdEta S μ + ω ^ cdExp (cdEta S μ)) ≤ Pv S ηm := Pv_mono (hxw.le.trans_eq hdec.symm)
      _ = upsilon l := hpvm
  -- the cap of `μ` applies
  have hcapμ : CdCapAt S μ := by
    rcases lt_or_ge (upsilon μ) (cdMstar S) with hlev | hlev
    · exact h0 μ hμ hBμ hlev
    · refine h1 μ hμ hBμ hlev hμX ?_
      have hx1 : Om ω ≤ cdEta S μ := by
        by_contra h
        push Not at h
        have h1' := Pv_lt_succ hg
        have h2' : Pv S (cdEta S μ + 1) ≤ Pv S (Om ω) := Pv_mono (Order.add_one_le_of_lt h)
        rw [hpvμ] at h1'
        exact absurd (h1'.trans_le h2') (not_lt.2 hlev)
      have htop : η0 + ω ^ e < Om ω + Nc.ncPp S * ω := by
        rw [← hdec]
        by_contra h
        push Not at h
        have h' := Pv_mono (S := S) h
        rw [hpvm] at h'
        exact absurd (hlT.trans_le h') (lt_irrefl _)
      have hxP : cdExp (cdEta S μ) < Nc.ncPp S := by
        by_contra h
        push Not at h
        exact cd_l2_contra hdvd hx1 hxm htop (lt_of_le_of_lt h hxe)
      show cdCodeOf S (cdEta S μ) < Nc.ncPp S
      rw [cdCodeOf_of_lt (hxP.trans (cdPp_lt_Om2 S))]
      exact (cdOff_le _).trans_lt hxP
  exact absurd ((hcapμ nuC hy).trans_le hcapl) (not_lt.2 hlν.le)

/-- **No standard pair straddles a restart point**: not `c ≤ ρ_l ≤ d` for a standard pair `(c, d)`. -/
theorem yxStd_noStraddle {c d l : Ordinal.{0}} (hs : IsStd c d) (hl : IsRestartIdx l)
    (h1 : c ≤ upsilon l) (h2 : upsilon l ≤ d) : False := by
  rcases h1.lt_or_eq with h | h
  · exact Cx.cxStd_straddle hs hl h h2
  · obtain ⟨L, -, hLnd, rfl, -⟩ := hs.parts
    have hL : L = l := upsilon_normal.strictMono.injective h
    exact hLnd (hL ▸ (ri_iff.1 hl).2)

/-- **Above a restart point below `ν_C` the next restart point is `≤ ν_C`.** -/
theorem yxNext_le_nuC {l : Ordinal.{0}} (hl : IsRestartIdx l) (h : upsilon l < nuC) :
    upsilon (l + ω * ω) ≤ nuC := by
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  rw [he] at h ⊢
  have hlξ : l < ξ := upsilon_normal.strictMono.lt_iff_lt.1 h
  exact upsilon_normal.strictMono.monotone (next_mult (ri_iff.1 hl).2 (ri_iff.1 hξ).2 hlξ)

/-- `δ_l < υ_{l+ω²}`. -/
theorem yxDelta_lt_next (l : Ordinal.{0}) : upsilon (l + ω + 1) < upsilon (l + ω * ω) :=
  upsilon_normal.strictMono (by simpa using idx_lt l 0 1)

/-- The chain tops after `δ_l + o` are strictly below `υ_{l+ω²}`. -/
theorem yxTop_lt_next {l : Ordinal.{0}} (hl : IsRestartIdx l) (o : Ordinal.{0}) (j : ℕ) :
    topA (l + ω) (upsilon (l + ω + 1) + o) (j + 1) < upsilon (l + ω * ω) := by
  have hle := Ys.ysTop_lt l o j
  rcases hle.lt_or_eq with h | h
  · exact h
  exfalso
  have hR : IsRestartIdx (l + ω * ω) :=
    ri_iff.2 ⟨(add_pos_of_pos_of_nonneg (pos_iff_ne_zero.2 hl.1) zero_le).ne',
      dvd_add (ri_iff.1 hl).2 (dvd_refl _)⟩
  have h' : upsilon (l + ω + ω * (j : Ordinal.{0}) + ω + 1) = upsilon (l + ω * ω) := h
  have hidx := upsilon_normal.strictMono.injective h'
  exact (ri_lim hR).succ_ne _ (by rw [succ_eq_add_one]; exact hidx)

/-- **The pair field `nostr` of a restart `l` with `ρ_l < ν_C`.** -/
theorem yxNostr_of_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) (h : upsilon l < nuC) :
    ∀ c d, c < d → c ≤ upsilon l → upsilon l ≤ d → d ≤ upsilon (l + ω + 1) → ¬ le2 c d := by
  intro c d hcd hc hd hdδ h2
  have hdν : d < nuC := hdδ.trans_lt ((yxDelta_lt_next l).trans_le (yxNext_le_nuC hl h))
  exact yxStd_noStraddle (std_of_lt_nuC hdν hcd h2) hl hc hd

/-- **The chain pair datum `Ys.YsNostrIn l o x₀` (`x₀ ≤ ρ_l`) at a restart `l` with `ρ_l < ν_C`.** -/
theorem yxChainNostr_of_lt {l o x0 : Ordinal.{0}} (hl : IsRestartIdx l) (h : upsilon l < nuC)
    (hx0 : x0 ≤ upsilon l) : Ys.YsNostrIn l o x0 := by
  intro j c hcx _ d hjd hdj h2
  have hdν : d < nuC := hdj.trans_lt ((yxTop_lt_next hl o j).trans_le (yxNext_le_nuC hl h))
  have hρd : upsilon l ≤ d :=
    ((upsilon_normal.strictMono (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)).le.trans
      (Ys.ysTopA_ge l o j)).trans hjd.le
  exact yxStd_noStraddle (std_of_lt_nuC hdν ((hcx.trans hx0).trans_lt
    (lt_of_lt_of_le (upsilon_normal.strictMono (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos)
      le_self_add)) ((Ys.ysTopA_ge l o j).trans hjd.le))) h2) hl (hcx.trans hx0) hρd

/-- **REFUTE FIRST: the pair field of `Ys.YsSpec` contains `ν_C ∉ [ρ_{l₀}, υ_B)`.** -/
theorem yxSpec_nu {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B) :
    ¬ (upsilon l0 ≤ nuC ∧ nuC < upsilon B) := by
  rintro ⟨h1, h2⟩
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  obtain ⟨⟨L, -, hLν, hL2, -⟩, -⟩ := pairs_cof_nuC
  rw [he] at h1 h2 hLν hL2
  have i0 : l0 ≤ ξ := upsilon_normal.strictMono.le_iff_le.1 h1
  have i1 : ξ < B := upsilon_normal.strictMono.lt_iff_lt.1 h2
  exact Sp.nostr ξ hξ i0 i1 _ _ hLν hLν.le le_rfl
    (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)) hL2

end Googology.Trans.PoR.InaccPsi.R2.Yx
