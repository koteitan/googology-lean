import Googology.Trans.PoR.InaccPsi.R2.ZhCar

/-!
# Zh: Lemma RS in the windows with the supply input at the supply restarts

At a supply restart (`υ_{λ+ω²} ≤ r(λ)`) the RS input of `Zc.zcRs_all` is LOWER itself
(`Zc.zcRsIn_long_lower`).  Here LOWER there is proved inside the induction from the realizer maps of
`Zh.zhReal_gen`: Range restarts `μ` cofinal below `ρ_λ` with `μ + β ≤ λ`, `υ_{μ+β} ≤ r(μ)` and the carry
`Zh.ZhCarry S λ μ β` at a target `υ_{λ+β} ≥ r(λ)` inside the window, UPPER at the inner restarts from the
specification (`Ys.ysTop_all`), LOWER at the inner restarts `μ + γ` and at the Range restarts below `ρ_λ` from
the induction (inside the window) and from the hypothesis (below the base).

* `ZhSupIn S λ B`: some `β` with `λ + β ≤ B`, `r(λ) ≤ υ_{λ+β}` and the supply with the carry;
* `ZhSupInC S λ B`, `zhSupIn_of_code`: the same with the carry replaced by the inner codes (`Zh.ZhSupCode`);
* `zhSpec_restr`: a specification restricts to every smaller multiple of `ω²`;
* `zhRs_all` (**Lemma RS with the supply input**): at every restart of `(l₀, B)` the input `ZcRsIn O λ` or
  `ZhSupIn S λ B` gives `ρ_λ ≤₁ δ_λ + O(λ)`;
* `zhWin_UL`, `zhTop_UL`: UPPER ∧ LOWER on `W_k`, `W_ω` with this input;
* `zhWins3`, `zhTopAll3` (**the windows with the input `ZcRsIn ∨ ZhSupIn`**);
* `zhRsIn_of_zc` (non-vacuity: the old input gives the new one).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The supply input at a restart `λ` of a window with top index `B`.** -/
def ZhSupIn (S : InaccSeq.{0}) (l B : Ordinal.{0}) : Prop :=
  ∃ β, l + β ≤ B ∧ cdR S l ≤ upsilon (l + β) ∧
    ∀ x < upsilon l, ∃ μ, CdRange S μ ∧ x < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + β ≤ l ∧
      upsilon (μ + β) ≤ cdR S μ ∧ ZhCarry S l μ β

/-- **The supply input with small inner codes.** -/
def ZhSupInC (S : InaccSeq.{0}) (l B : Ordinal.{0}) : Prop :=
  ∃ β, l + β ≤ B ∧ cdR S l ≤ upsilon (l + β) ∧ ZhSupCode S l β

/-- **The code form gives the carry form** (`Zh.zhCarry_of_codes`). -/
theorem zhSupIn_of_code {l B : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon B ≤ nuC)
    (h : ZhSupInC S l B) : ZhSupIn S l B := by
  obtain ⟨β, hlβ, hr, hc⟩ := h
  refine ⟨β, hlβ, hr, fun x hx => ?_⟩
  obtain ⟨μ, h1, h2, h3, h4, h5, h6⟩ := hc x hx
  exact ⟨μ, h1, h2, h3, h4, h5,
    zhCarry_of_codes hl ((upsilon_normal.strictMono.monotone hlβ).trans hν) h6⟩

/-- A specification restricts to every smaller top. -/
theorem zhSpec_restr {O : Ordinal.{0} → Ordinal.{0}} {l0 B B' : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B)
    (hB' : B' ≤ B) (hm : ω * ω ∣ B') (hlt : l0 < B') : Ys.YsSpec O l0 B' :=
  ⟨Sp.ri, hm, lt_of_le_of_lt hB' Sp.cnt, hlt, Sp.land0,
    fun l h1 h2 h3 => Sp.nostr l h1 h2 (h3.trans_le hB'),
    fun l h1 h2 h3 => Sp.kind l h1 h2 (h3.trans_le hB')⟩

/-- **Lemma RS at every restart of a specification below `ν_C`** with the input `ZcRsIn` or the supply. -/
theorem zhRs_all {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B)
    (hν : upsilon B ≤ nuC) (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hL0 : ∀ μ, CdRange S μ → μ ≤ l0 → CdLower S μ)
    (hin : ∀ l, IsRestartIdx l → l0 < l → l < B → Zc.ZcRsIn O l ∨ ZhSupIn S l B) :
    ∀ l, IsRestartIdx l → l0 < l → l < B → le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  have hm := upsilon_normal.strictMono
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hl0l hlB
  have hRl : upsilon (l + ω + 1) + O l = cdR S l := by rw [hO l hl0l]; exact Ys.ysO_eq S l
  have hlν : upsilon l < nuC := (hm hlB).trans_le hν
  have hBd : ω ^ 2 ∣ B := by rw [pow_two]; exact Sp.mult
  have hlw : l + ω ^ 2 ≤ B := Lr.lr_dvd_add_le hl.2 hBd hlB
  rcases hin l hl hl0l hlB with hzc | ⟨β, hlβB, hrβ, hSup⟩
  · -- the old input: Lemma RS on the restricted specification up to `λ + ω²`
    have hm2 : ω * ω ∣ l + ω ^ 2 := by rw [← pow_two]; exact dvd_add hl.2 (dvd_refl _)
    have hlt2 : l < l + ω ^ 2 := lt_add_of_pos_right l (pow_pos omega0_pos 2)
    have Sp' := zhSpec_restr Sp hlw hm2 (hl0l.trans hlt2)
    refine Zc.zcRs_all Sp' (hm.monotone hlw |>.trans hν) (fun μ hμ h0μ hμB => ?_) l hl hl0l hlt2
    rcases lt_trichotomy μ l with hμl | rfl | hlμ
    · exact Or.inl (IH μ hμl hμ h0μ (hμl.trans hlB))
    · exact hzc
    · exact absurd hμB (not_lt.2 (Lr.lr_dvd_add_le hl.2 hμ.2 hlμ))
  · -- the supply input: LOWER at `λ` by the realizer maps
    rw [hRl]
    have hν' : upsilon (l + β) ≤ nuC := (hm.monotone hlβB).trans hν
    have hl1 : upsilon l < Om1 := hlν.trans_le nuC_le_Om1
    have hU : ZhUpIn S l β := by
      intro γ hγ0 hγd hγβ g hg
      have hγri : IsRestartIdx (l + γ) := zh_ri_add hl hγd
      have h0γ : l0 ≤ l + γ := hl0l.le.trans le_self_add
      have hγB : l + γ < B := lt_of_lt_of_le (Lr.lr_addL (a := l) hγβ) hlβB
      have htop := (Ys.ysTop_all Sp hγri h0γ hγB).2
      have e : upsilon (l + γ + ω + 1) + O (l + γ) = cdR S (l + γ) := by
        rw [hO (l + γ) (hl0l.trans_le le_self_add)]; exact Ys.ysO_eq S _
      by_contra hgt
      exact htop g (by rw [e]; exact not_le.1 hgt) hg
    have hS : ZhSupAt S l β := by
      intro x hx
      obtain ⟨μ, hR, h1, h2, h3, h4, h5⟩ := hSup (max x (upsilon l0)) (max_lt hx (hm hl0l))
      have hμ0 : l0 < μ := hm.lt_iff_lt.1 (lt_of_le_of_lt (le_max_right _ _) h1)
      refine ⟨μ, hR, (le_max_left _ _).trans_lt h1, h2, h3, h4, fun γ hγ0 hγd hγβ => ?_, h5⟩
      have hri := zh_ri_add hR.1 hγd
      have hlt : μ + γ < l := lt_of_lt_of_le (Lr.lr_addL (a := μ) hγβ) h3
      have h0γ : l0 < μ + γ := hμ0.trans_le le_self_add
      have := IH (μ + γ) hlt hri h0γ (hlt.trans hlB)
      rw [hO _ h0γ, Ys.ysO_eq] at this
      exact this
    have hR : Lr.LrReal S (upsilon l) (cdR S l) := zhReal_gen hl hl1 hlν hν' hrβ hU hS
    have hLlow : ∀ μ, CdRange S μ → upsilon μ < upsilon l → CdLower S μ := by
      intro μ hr hμ
      have hμl : μ < l := hm.lt_iff_lt.1 hμ
      rcases le_or_gt μ l0 with h | h
      · exact hL0 μ hr h
      · have := IH μ hμl hr.1 h (hμl.trans hlB)
        unfold CdLower
        rw [hO μ h, Ys.ysO_eq] at this
        exact this
    have hab : upsilon l ≤ cdR S l :=
      (hm (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)).le.trans (cdR_ge S l)
    exact Zc.zcLe1_of_real hLlow hab (Cv.cvNoPair_of_nu hl rfl (hrβ.trans hν')) hR

/-- **UPPER ∧ LOWER at every Range restart of `W_k`** with the input `ZcRsIn ∨ ZhSupIn`. -/
theorem zhWin_UL (k : ℕ) {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < μ → O μ = Ys.ysO S μ)
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hν : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC)
    (hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) → CdLower S μ)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      Zc.ZcRsIn O l ∨ ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hO' : ∀ μ, CdRange S μ → Wj.WjWin S k μ → upsilon (μ + ω + 1) + O μ = cdR S μ := by
    intro μ _ hw
    have h0 := hw.1
    rw [Pp.ppL_eq_ups (S := S)] at h0
    rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
    exact Ys.ysO_eq S μ
  intro μ hr hw
  have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))) < upsilon μ :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.1
  have h1 : upsilon μ < upsilon (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.2
  obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
  refine ⟨Ys.ysWin_upper k (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp hO' μ hr hw, ?_⟩
  unfold CdLower
  rw [← hO' μ hr hw]
  exact zhRs_all Sp (by rw [Yx.yxUps_base]; exact hν) hO hL0 hin μ hr.1 i0 i1

/-- **UPPER ∧ LOWER at every Range restart of `W_ω`** with the input `ZcRsIn ∨ ZhSupIn`. -/
theorem zhTop_UL {O : Ordinal.{0} → Ordinal.{0}}
    (hO : ∀ μ, Bt.iota S (Om ω + Nc.ncPp S * ω) < μ → O μ = Ys.ysO S μ)
    (Sp : Ys.YsSpec O (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * ω) → CdLower S μ)
    (hin : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      Zc.ZcRsIn O l ∨ ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)))) :
    ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have hO' : ∀ μ, CdRange S μ → Wj.WjTop S μ → upsilon (μ + ω + 1) + O μ = cdR S μ := by
    intro μ _ hw
    have h0 := hw.1
    rw [Pp.ppL_eq_ups (S := S)] at h0
    rw [hO μ (upsilon_normal.strictMono.lt_iff_lt.1 h0)]
    exact Ys.ysO_eq S μ
  intro μ hr hw
  have h0 : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < upsilon μ :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.1
  have h1 : upsilon μ < upsilon (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) :=
    (Yx.yxUps_base (S := S) _).symm ▸ hw.2
  obtain ⟨i0, i1⟩ := Ys.ysIdx_win h0 h1
  refine ⟨Ys.ysTop_upper (Pp.ppL_eq_ups (S := S) _) (Pp.ppL_eq_ups (S := S) _) Sp hO' μ hr hw, ?_⟩
  unfold CdLower
  rw [← hO' μ hr hw]
  exact zhRs_all Sp (by rw [Yx.yxUps_base]; exact hν) hO hL0 hin μ hr.1 i0 i1

/-- The input in the bound `yxO`: `ZcRsIn` congruence and `ZhSupIn` (independent of the bound). -/
theorem zhIn_congr {l0 l B : Ordinal.{0}} (hl : l0 < l)
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupIn S l B) :
    Zc.ZcRsIn (Yx.yxO S l0) l ∨ ZhSupIn S l B := by
  rcases h with h | h
  · exact Or.inl (Zc.zcRsIn_congr (fun μ h => Yx.yxO_above h) hl h)
  · exact Or.inr h

/-- **ALL WINDOWS `W_k` BY ONE INDUCTION ON `k`** with the RS input `ZcRsIn ∨ ZhSupIn`. -/
theorem zhWins3
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})))) :
    ∀ k : ℕ, Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0}))))
        (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
        (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))) ∧
      ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdUpper S μ ∧ CdLower S μ := by
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  have hb := Yx.yxCaps_below k hlow' fun j hj μ hr hw =>
    ⟨((IH j hj).2.2 μ hr hw).1, hV j μ hr hw⟩
  have hL := Zc.zcLower_below k (fun μ hr h => (hlow μ hr h).2.1) fun j hj μ hr hw =>
    ((IH j hj).2.2 μ hr hw).2
  obtain ⟨hν, Sp⟩ := Yx.yxWin_full k ⟨Zc.zcBaseIn k h0 hb hL, hin k⟩ h0 hb (hV k)
  have hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) → CdLower S μ := by
    intro μ hr hμ
    rcases hμ.lt_or_eq with hμ | rfl
    · exact hL μ hr (by rw [← Yx.yxUps_base (S := S)]; exact upsilon_normal.strictMono hμ)
    · exact absurd hr (Yx.yxL_notRange k)
  refine ⟨hν, Sp, zhWin_UL k (fun μ h => Yx.yxO_above h) Sp hν hL0 fun l hl h1 h2 =>
    zhIn_congr h1 (hrs k l hl h1 h2)⟩

/-- **THE TOP WINDOW `W_ω`** with the RS input `ZcRsIn ∨ ZhSupIn`. -/
theorem zhTopAll3
    (hin : ∀ k : ℕ, Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})))
      (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hlow : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdLower S μ ∧ CdCapV S μ)
    (hV : ∀ k : ℕ, ∀ μ, CdRange S μ → Wj.WjWin S k μ → CdCapV S μ)
    (hrs : ∀ k : ℕ, ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * (k : Ordinal.{0})) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0})) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * ((k + 1 : ℕ) : Ordinal.{0}))))
    (hinT : Zc.ZcInR S (Bt.iota S (Om ω + Nc.ncPp S * ω)) (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hVT : ∀ μ, CdRange S μ → Wj.WjTop S μ → CdCapV S μ)
    (hrsT : ∀ l, IsRestartIdx l → Bt.iota S (Om ω + Nc.ncPp S * ω) < l →
      l < Bt.iota S (Om ω + Nc.ncPp S * (ω + 1)) →
      Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupIn S l (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))))
    (hLw : Yx.YxLwNo2 S) :
    Nc.ncL S (ω + 1) ≤ nuC ∧
      Ys.YsSpec (Yx.yxO S (Bt.iota S (Om ω + Nc.ncPp S * ω))) (Bt.iota S (Om ω + Nc.ncPp S * ω))
        (Bt.iota S (Om ω + Nc.ncPp S * (ω + 1))) ∧
      ∀ μ, CdRange S μ → Wj.WjTop S μ → CdUpper S μ ∧ CdLower S μ := by
  have W := zhWins3 hin hlow hV hrs
  have hlow' : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S 0 → CdUpper S μ ∧ CdCapV S μ :=
    fun μ hr h => ⟨(hlow μ hr h).1, (hlow μ hr h).2.2⟩
  have h0 : CdCAP0 S := Yx.yxCAP0 fun μ hr h => cdCapAt_of_upper (hlow μ hr h).1 (hlow μ hr h).2.2
  have hb : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdCapAt S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Yx.yxCaps_below (n + 1) hlow' (fun j _ μ hr hw => ⟨((W j).2.2 μ hr hw).1, hV j μ hr hw⟩) μ hr hn
  have hL : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → CdLower S μ := by
    intro μ hr hμ
    obtain ⟨n, hn⟩ := Pp.ppL_cof (S := S) _ hμ
    exact Zc.zcLower_below (n + 1) (fun μ hr h => (hlow μ hr h).2.1)
      (fun j _ μ hr hw => ((W j).2.2 μ hr hw).2) μ hr hn
  have hρ : upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω)) < nuC := by
    rw [Yx.yxUps_base]
    refine Yx.yxNu_gt le_rfl h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (Qq.qqL_lt_succ S), hc⟩ hlX
  have hbase : Ys.YsReachIn (Bt.iota S (Om ω + Nc.ncPp S * ω)) 0
      (upsilon (Bt.iota S (Om ω + Nc.ncPp S * ω))) :=
    Zc.zcBase_reach Yx.yxBaseW_ri (Zc.zcL_cnt _) hρ Zc.zcSupW
      (fun μ hr h => hL μ hr (by rw [Yx.yxUps_base] at h; exact h))
  obtain ⟨hν, Sp⟩ := Yx.yxTop_full ⟨hbase, hinT⟩ h0 hLw hb hVT
  have hL0 : ∀ μ, CdRange S μ → μ ≤ Bt.iota S (Om ω + Nc.ncPp S * ω) → CdLower S μ := by
    intro μ hr hμ
    rcases hμ.lt_or_eq with hμ | rfl
    · exact hL μ hr (by rw [← Yx.yxUps_base (S := S)]; exact upsilon_normal.strictMono hμ)
    · exact absurd hr Yx.yxLw_notRange
  exact ⟨hν, Sp, zhTop_UL (fun μ h => Yx.yxO_above h) Sp hν hL0 fun l hl h1 h2 =>
    zhIn_congr h1 (hrsT l hl h1 h2)⟩

/-- **Non-vacuity: the old RS input gives the new one.** -/
theorem zhRsIn_of_zc {O : Ordinal.{0} → Ordinal.{0}} {l B : Ordinal.{0}} (h : Zc.ZcRsIn O l) :
    Zc.ZcRsIn O l ∨ ZhSupIn S l B := Or.inl h

/-- **At a supply restart the new input is the supply** (the term branch of `ZcRsIn` is refuted there by
`Zc.zcRsTerm_long_false`, the successor branch is impossible): the input `ZcRsIn ysO ∨ ZhSupIn` at a restart with
`υ_{λ+ω²} ≤ r(λ)` is `LOWER ∨ ZhSupIn`. -/
theorem zhIn_long {l B : Ordinal.{0}} (hl : IsRestartIdx l) (hlong : upsilon (l + ω * ω) ≤ cdR S l)
    (h : Zc.ZcRsIn (Ys.ysO S) l ∨ ZhSupIn S l B) : CdLower S l ∨ ZhSupIn S l B := by
  rcases h with h | h
  · exact Or.inl (Zc.zcRsIn_long_lower hl hlong h)
  · exact Or.inr h

end Googology.Trans.PoR.InaccPsi.R2.Zh
