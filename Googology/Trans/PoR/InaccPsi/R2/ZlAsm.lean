import Googology.Trans.PoR.InaccPsi.R2.ZlSup
import Googology.Trans.PoR.InaccPsi.R2.XoForm

/-!
# The assembly of the supply clause `Xo.XoSup`: LOWER, the long clause and the reach formula discharged

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

At a `υ`-fixed `λ` (`υ_λ = λ`, an `ε`-number) and a supply restart `μ` (`υ_μ = μ`), an inner offset `g` (`0 < g`,
`ω² ∣ g`, `g < β`) is **short** when `λ + g` is not `υ`-fixed (`λ+g < υ_{λ+g}`; `ε`-offsets `X < υ_{λ+X}` included).  At a short `g` the three demands of
`Xo.XoCarry` become:
* the long clause `υ_{λ+β} ≤ r(λ+g) ⇒ …` is VACUOUS: `r(λ+g) = υ_{λ+g+ω+1} + c(g) < υ_{λ+β}` (`Zl.zlR_add`,
  `Zl.zl_short_lt`);
* LOWER at `μ + f g` follows from LOWER at the Range restarts with `RzRest` (the shared leaf of the road) when
  `μ + f g` is short too (it is then a Range restart of code `c(f g) < Ω₁ ≤ P′`);
* the image bound reads `img(E) ≤ υ_{μ+f g+ω+1} + c(f g)` for every restricted decomposition `E` of
  `υ_{λ+g+ω+1} + c(g)` (`ZlEQs`): **EQ under `η_λ + g ↦ η_μ + f g` with both reaches given by the formula**.
At the other offsets (`λ + g` a `υ`-fixed point, `ZlEQf`) the clause is kept as it is.

* `ZlEQs`, `ZlEQf`, `ZlCfg` (statements);
* `zl_add_w2_le`, `zl_code_lt_Pp`, `zl_off_pos`, `zl_off_dvd`;
* `zlCarry_of` (**the carry from the reduced clauses**), `zlSup_of` (**`ZlCfg ⇒ Xo.XoSup`**, given LOWER at the Range
  `RzRest` restarts);
* `zlCfg_of_sup` (**`Xo.XoSup ⇒ ZlCfg`**: the reduction loses nothing, so `ZlCfg` is satisfiable iff `XoSup` is),
  `zlCfg_iff`.

No new axiom.  New definitions: `ZlEQs`, `ZlEQf`, `ZlCfg` (statements).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **EQ at the short offsets** (both reaches by the formula; at a non-short image `μ + f g` the carry is kept). -/
def ZlEQs (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (Os : Finset Ordinal.{0}) :
    Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → ¬ upsilon (l + g) = l + g →
    (¬ upsilon (μ + f g) = μ + f g → ∀ E : Xo.XoE, Xo.XoWF S l β E → Xo.xoVal S l E = cdDelta (l + g) + cL g →
      Xo.XoOs l Os E → Xo.XoR S l μ E → Xo.xoImg S l μ f E ≤ cdDelta (μ + f g) + cL (f g)) ∧
    (upsilon (μ + f g) = μ + f g → CdLower S (μ + f g) ∧ ∀ E : Xo.XoE, Xo.XoWF S l β E →
      Xo.xoVal S l E = cdDelta (l + g) + cL g → Xo.XoOs l Os E → Xo.XoR S l μ E →
        Xo.xoImg S l μ f E ≤ cdR S (μ + f g))

/-- **The carry at the `υ`-fixed offsets** (`υ_{λ+g} = λ + g`), unchanged. -/
def ZlEQf (S : InaccSeq.{0}) (l β μ : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (B : Ordinal.{0})
    (Os : Finset Ordinal.{0}) : Prop :=
  ∀ g ∈ Os, 0 < g → ω ^ 2 ∣ g → upsilon (l + g) = l + g → CdLower S (μ + f g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + B) ≤ cdR S (μ + f g)) ∧
    ∀ E : Xo.XoE, Xo.XoWF S l β E → Xo.xoVal S l E = cdR S (l + g) → Xo.XoOs l Os E → Xo.XoR S l μ E →
      Xo.xoImg S l μ f E ≤ cdR S (μ + f g)

/-- **The reduced supply clause**: `υ`-fixed supply restarts with an offset map, the supply, and EQ. -/
def ZlCfg (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
    ∃ μ f B, CdRange S μ ∧ upsilon μ = μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
      upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ ZlEQs S l β μ f Os ∧ ZlEQf S l β μ f B Os

theorem zl_add_w2_le {g β : Ordinal.{0}} (hgβ : g < β) (hgd : ω ^ 2 ∣ g) (hβd : ω ^ 2 ∣ β) :
    g + ω ^ 2 ≤ β := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hgβ.le
  have hd0 : d ≠ 0 := by rintro rfl; rw [add_zero] at hgβ; exact lt_irrefl _ hgβ
  have hdd : ω ^ 2 ∣ d := (Ordinal.dvd_add_iff hgd).1 hβd
  exact add_le_add_right (le_of_dvd hd0 hdd) g

/-- A countable code is below `P′`. -/
theorem zl_code_lt_Pp {c : Ordinal.{0}} (hc : c < Om 1) : c < Nc.ncPp S := by
  have h0 : Nc.ncPp S ≠ 0 := (Nc.ncPp_SC S).1.ne'
  have hd : Om 1 ∣ Nc.ncPp S := dvd_trans (dvd_mul_right _ _) Rd.rd_dvd2_Pp
  exact hc.trans_le (le_of_dvd h0 hd)

theorem zl_off_pos {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}} {B g : Ordinal.{0}}
    (hoff : Sl.SlOff f Os B) (hg : g ∈ Os) (hg0 : 0 < g) : 0 < f g := by
  have h := hoff.mono (by simp : (0 : Ordinal.{0}) ∈ (↑(insert 0 Os) : Set Ordinal.{0}))
    (by simp [hg] : g ∈ (↑(insert 0 Os) : Set Ordinal.{0})) hg0
  rwa [hoff.zero] at h

theorem zl_off_dvd {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}} {B g : Ordinal.{0}}
    (hoff : Sl.SlOff f Os B) (hgd : ω ^ 2 ∣ g) : ω ^ 2 ∣ f g := by
  obtain ⟨q, rfl⟩ := hgd
  exact hoff.dvd q

theorem zl_lvO_mono {l : Ordinal.{0}} {Os Os' : Finset Ordinal.{0}} (h : Os ⊆ Os') :
    ∀ p, Vr.vrLvO l Os p → Vr.vrLvO l Os' p := by
  rintro p (hp | ⟨h', hh', h0, e⟩)
  · exact Or.inl hp
  · exact Or.inr ⟨h', h hh', h0, e⟩

theorem zl_vrOs_mono {l : Ordinal.{0}} {Os Os' : Finset Ordinal.{0}} (h : Os ⊆ Os') :
    ∀ E : Vr.VrE, Vr.VrOs l Os E → Vr.VrOs l Os' E
  | .lo _, _ => trivial
  | .sg _ _, hE => h hE
  | .ub _ t, ⟨h1, h2⟩ => ⟨h h1, Ub.UbT.Lv_mono (zl_lvO_mono h) t h2⟩
  | .tm _ t _ _, ⟨h1, h2, h3⟩ => ⟨h h1, Un.UnT.Lv_mono (zl_lvO_mono h) t h2, fun p hp => zl_lvO_mono h p (h3 p hp)⟩
  | .add s t, ⟨h1, h2⟩ => ⟨zl_vrOs_mono h s h1, zl_vrOs_mono h t h2⟩

theorem zl_xoOs_mono {l : Ordinal.{0}} {Os Os' : Finset Ordinal.{0}} (h : Os ⊆ Os') :
    ∀ E : Xo.XoE, Xo.XoOs l Os E → Xo.XoOs l Os' E
  | .old E, hE => zl_vrOs_mono h E hE
  | .th _ L e, ⟨h1, h2, h3⟩ => ⟨h h1, zl_xoOs_mono h L h2, zl_xoOs_mono h e h3⟩
  | .add a b, ⟨h1, h2⟩ => ⟨zl_xoOs_mono h a h1, zl_xoOs_mono h b h2⟩
  | .lc _, _ => trivial
  | .phi a b, ⟨h1, h2⟩ => ⟨zl_xoOs_mono h a h1, zl_xoOs_mono h b h2⟩
  | .om a, h1 => zl_xoOs_mono h a h1
  | .coll a b, ⟨h1, h2⟩ => ⟨zl_xoOs_mono h a h1, zl_xoOs_mono h b h2⟩

section Asm

variable {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hfl : upsilon l = l) (hl1 : upsilon l < Om 1)
  (hβd : ω ^ 2 ∣ β) (hβν : upsilon (l + β) ≤ nuC) (hβL : upsilon (l + β) ≤ Nc.ncL S (ω + 1))
include hl hfl hl1 hβd hβν hβL

omit hl1 hβd in
/-- The reach formula on the window side. -/
theorem zl_win_R {g : Ordinal.{0}} (hgβ : g < β) (hg0 : 0 < g) (hgd : ω ^ 2 ∣ g) (hfix : ¬ upsilon (l + g) = l + g) :
    cdR S (l + g) = cdDelta (l + g) + cL g := by
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hE : InE l := by have := upsPt_inE (upsPt_upsilon hl0); rwa [hfl] at this
  have hlt : upsilon (l + g) < upsilon (l + β) := hm ((add_lt_add_iff_left l).2 hgβ)
  refine zlR_addU hl hE hg0 hgd (zl_lt_of_ne hfix) (hlt.trans_le hβν) (η1 := Om ω + Nc.ncPp S * (ω + 1)) ?_
  rw [← Lw.lw_L_eq]; exact hlt.trans_le hβL

/-- **The carry from the reduced clauses** at one configuration. -/
theorem zlCarry_of (hLow : ∀ lam, CdRange S lam → Rz.RzRest lam → CdLower S lam)
    {μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hOs : ∀ d ∈ Os, d < β) (hR : CdRange S μ) (hfμ : upsilon μ = μ) (hμl : upsilon μ < upsilon l)
    (hRz : Rz.rzLam ≤ μ) (hB : μ + B ≤ l) (hoff : Sl.SlOff f Os B)
    (hs : ZlEQs S l β μ f Os) (hf : ZlEQf S l β μ f B Os) : Xo.XoCarry S l β μ f B Os := by
  have hm := upsilon_normal.strictMono
  intro g hg hg0 hgd
  by_cases hfix : upsilon (l + g) = l + g
  · exact hf g hg hg0 hgd hfix
  have hgβ : g < β := hOs g hg
  have hrl := zl_win_R hl hfl hβν hβL hgβ hg0 hgd hfix
  have hfg0 := zl_off_pos hoff hg hg0
  have hfgd := zl_off_dvd hoff hgd
  have hμ0 : 0 < μ := pos_iff_ne_zero.2 hR.1.1
  have hEμ : InE μ := by have := upsPt_inE (upsPt_upsilon hμ0); rwa [hfμ] at this
  have hfgl : μ + f g < l := ((add_lt_add_iff_left μ).2 (hoff.bd g hg)).trans_le hB
  have hυfg : upsilon (μ + f g) < upsilon l := hm hfgl
  have hlβ : upsilon l ≤ upsilon (l + β) := hm.monotone le_self_add
  have hν' : upsilon (μ + f g) < nuC := hυfg.trans_le (hlβ.trans hβν)
  have hL' : upsilon (μ + f g) < Nc.ncL S (ω + 1) := hυfg.trans_le (hlβ.trans hβL)
  have hlong : ¬ upsilon (l + β) ≤ cdR S (l + g) := by
    rw [hrl, ← zl_cL_add (by have := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1)); rwa [hfl] at this)
      hg0.ne']
    exact not_le.2 (zl_short_lt ⟨(hg0.trans_le le_add_self).ne', dvd_add hl.2 hgd⟩ (zl_add_w2_le hgβ hgd hβd))
  by_cases hfixμ : upsilon (μ + f g) = μ + f g
  · obtain ⟨hLo, hEQ⟩ := (hs g hg hg0 hgd hfix).2 hfixμ
    exact ⟨hLo, fun h => absurd h hlong, fun E hW hv hO hR' => hEQ E hW (hv.trans hrl) hO hR'⟩
  have hrμ : cdR S (μ + f g) = cdDelta (μ + f g) + cL (f g) :=
    zlR_addU hR.1 hEμ hfg0 hfgd (zl_lt_of_ne hfixμ) hν' (η1 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hL')
  have hRfg : IsRestartIdx (μ + f g) := ⟨(hfg0.trans_le le_add_self).ne', dvd_add hR.1.2 hfgd⟩
  have hww : ω * ω < μ + f g := Zh.zh_ww_lt hR.1 (lt_add_of_pos_right μ hfg0)
  have hcode : cdCode S (μ + f g) = cL (μ + f g) :=
    Zh.zh_code_cL hRfg hww (zl_lt_of_ne hfixμ)
      (η1 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hL')
  have hcO : cL (μ + f g) < Om 1 := (cL_le_ups hRfg).trans_lt (hυfg.trans hl1)
  have hRng : CdRange S (μ + f g) :=
    ⟨hRfg, hR.2.1.trans le_self_add, hL', by rw [hcode]; exact zl_code_lt_Pp hcO⟩
  refine ⟨hLow _ hRng (Or.inl (hRz.trans le_self_add)), fun h => absurd h hlong, fun E hW hv hO hR' => ?_⟩
  rw [hrμ]
  exact (hs g hg hg0 hgd hfix).1 hfixμ E hW (hv.trans hrl) hO hR'

/-- **`ZlCfg ⇒ Xo.XoSup`** (given LOWER at the Range `RzRest` restarts and `υ_{rzLam} < υ_λ`). -/
theorem zlSup_of (hLow : ∀ lam, CdRange S lam → Rz.RzRest lam → CdLower S lam)
    (hRz : upsilon Rz.rzLam < upsilon l) (hcfg : ZlCfg S l β) : Xo.XoSup S l β := by
  intro γ hγ Os hOs
  obtain ⟨μ, f, B, hR, hfμ, hγμ, hμl, hB, hBd, hsup, hoff, hs, hf⟩ :=
    hcfg (max γ (upsilon Rz.rzLam)) (max_lt hγ hRz) Os hOs
  have hRzμ : Rz.rzLam ≤ μ :=
    (upsilon_normal.strictMono.lt_iff_lt.1 ((le_max_right _ _).trans_lt hγμ)).le
  exact ⟨μ, f, B, hR, (le_max_left _ _).trans_lt hγμ, hμl, hB, hBd, hsup, hoff,
    zlCarry_of hl hfl hl1 hβd hβν hβL hLow hOs hR hfμ hμl hRzμ hB hoff hs hf⟩

omit hl1 hβd in
/-- **`Xo.XoSup ⇒ ZlCfg`** (for `ω² < β`): the reduction loses nothing. -/
theorem zlCfg_of_sup (hβ2 : ω ^ 2 < β) (hsup : Xo.XoSup S l β) : ZlCfg S l β := by
  have hm := upsilon_normal.strictMono
  intro γ hγ Os hOs
  have hOs' : ∀ d ∈ insert (ω ^ 2) Os, d < β := by
    intro d hd
    rcases Finset.mem_insert.1 hd with rfl | h
    · exact hβ2
    · exact hOs d h
  obtain ⟨μ, f, B, hR, hγμ, hμl, hB, hBd, hsB, hoff, hcar⟩ := hsup γ hγ (insert (ω ^ 2) Os) hOs'
  have h2pos : (0 : Ordinal.{0}) < ω ^ 2 := by rw [Vo.vo_e2]; exact opow_pos _ omega0_pos
  have hw2 : ω ^ 2 ≤ B := by
    have h1 := zl_off_pos hoff (Finset.mem_insert_self _ _) h2pos
    have h2 : ω ^ 2 ∣ f (ω ^ 2) := zl_off_dvd hoff dvd_rfl
    exact (le_of_dvd h1.ne' h2).trans (hoff.bd _ (Finset.mem_insert_self _ _)).le
  have hlong : upsilon (μ + ω ^ 2) ≤ cdR S μ :=
    (hm.monotone (add_le_add_right hw2 μ)).trans hsB
  have hlβ : upsilon l ≤ upsilon (l + β) := hm.monotone le_self_add
  have hμν : upsilon μ < nuC := hμl.trans_le (hlβ.trans hβν)
  have hfμ : upsilon μ = μ := Zh.zhSup_fix hR.1 (lt_of_lt_of_le Cp.cp_ww_lt_B0 hR.2.1) hμν
    (η1 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1) hlong
  have hoff' : Sl.SlOff f Os B :=
    ⟨hoff.zero, hoff.res, hoff.dvd,
      hoff.mono.mono (by
        intro x hx
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)),
      fun d hd => hoff.bd d (Finset.mem_insert_of_mem hd)⟩
  have hO' : ∀ E : Xo.XoE, Xo.XoOs l Os E → Xo.XoOs l (insert (ω ^ 2) Os) E := by
    intro E hE
    exact zl_xoOs_mono (Finset.subset_insert _ _) E hE
  refine ⟨μ, f, B, hR, hfμ, hγμ, hμl, hB, hBd, hsB, hoff', fun g hg hg0 hgd hfix => ⟨fun hfixμ E hW hv hO hR' => ?_,
    fun hfixμ => ⟨(hcar g (Finset.mem_insert_of_mem hg) hg0 hgd).1, fun E hW hv hO hR' => ?_⟩⟩,
    fun g hg hg0 hgd hfix => ?_⟩
  · have hgβ : g < β := hOs g hg
    have hrl := zl_win_R hl hfl hβν hβL hgβ hg0 hgd hfix
    have h := (hcar g (Finset.mem_insert_of_mem hg) hg0 hgd).2.2 E hW (hv.trans hrl.symm) (hO' E hO) hR'
    have hfg0 := zl_off_pos hoff (Finset.mem_insert_of_mem hg) hg0
    have hfgd := zl_off_dvd hoff hgd
    have hμ0 : 0 < μ := pos_iff_ne_zero.2 hR.1.1
    have hEμ : InE μ := by have := upsPt_inE (upsPt_upsilon hμ0); rwa [hfμ] at this
    have hfgl : μ + f g < l :=
      ((add_lt_add_iff_left μ).2 (hoff.bd g (Finset.mem_insert_of_mem hg))).trans_le hB
    have hυfg : upsilon (μ + f g) < upsilon l := hm hfgl
    rw [zlR_addU hR.1 hEμ hfg0 hfgd (zl_lt_of_ne hfixμ) (hυfg.trans_le (hlβ.trans hβν))
      (η1 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hυfg.trans_le (hlβ.trans hβL))] at h
    exact h
  · have hgβ : g < β := hOs g hg
    have hrl := zl_win_R hl hfl hβν hβL hgβ hg0 hgd hfix
    exact (hcar g (Finset.mem_insert_of_mem hg) hg0 hgd).2.2 E hW (hv.trans hrl.symm) (hO' E hO) hR'
  · obtain ⟨h1, h2, h3⟩ := hcar g (Finset.mem_insert_of_mem hg) hg0 hgd
    exact ⟨h1, h2, fun E hW hv hO hR' => h3 E hW hv (hO' E hO) hR'⟩

end Asm

end Googology.Trans.PoR.InaccPsi.R2.Zl
