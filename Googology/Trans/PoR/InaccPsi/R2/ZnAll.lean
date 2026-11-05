import Googology.Trans.PoR.InaccPsi.R2.ZnRS

/-!
# Zn: Lemma RS in the windows with the value input

The term input `Zc.ZcRsTerm` of Lemma RS asks, for every `z < O(λ)`, an offset term `t` (constants below
`ρ_λ`) with `z ≤ t(ρ_λ)` and `t(ρ_μ) ≤ O(μ)` at restarts `μ` cofinal below `λ`.  Its values stay below
`ε_{ρ_λ+1}`, so it is FALSE at every restart with `O(λ) > E` for an `ε`-number
`E ∈ (ρ_λ, O(λ))` (`znRsTerm_false`).  With `Zn.znRs_rstV` the term may be replaced by any value
`v < υ_{λ+1}`, its image at `μ` being `π_{ρ_μ, ρ_λ}(v)`:

* `ZnRsVal O λ` (**the value input**): for every `z < O(λ)` a value `v` with `z ≤ v < υ_{λ+1}` and restarts
  `μ` cofinal below `λ` with `π_{ρ_μ, ρ_λ}(v) ≤ O(μ)`;
* `znNostr_v`: no `<₂`-pair from a point `≤ ρ_λ` into `[ρ_λ, δ_λ + v]` when `v < δ_λ`, `ρ_λ < ν_C`;
* `znRs_val` (**Lemma RS at one restart with the value input**, from Lemma RS below it);
* `znRs_all` (**Lemma RS at every restart of a specification below `ν_C`** with the input
  `ZcRsIn ∨ ZhSupIn ∨ ZnRsVal`);
* `znVal_of_term` (**non-vacuity**: the term input gives the value input, Lemma EXACT `OT.pi_ev`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.OT

variable {S : InaccSeq.{0}}

/-- **The value input of Lemma RS at a restart**: a statement on the bound `O` and the base change `π`. -/
def ZnRsVal (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∀ z < O l, ∃ v, z ≤ v ∧ v < upsilon (succ l) ∧
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ pi (upsilon μ) (upsilon l) v ≤ O μ

/-- **No pair from a point `≤ ρ_λ` ends in `[ρ_λ, δ_λ + v]`** when `v < δ_λ` and `ρ_λ < ν_C`. -/
theorem znNostr_v {l v : Ordinal.{0}} (hl : IsRestartIdx l) (hν : upsilon l < nuC)
    (hv : v < upsilon (l + ω + 1)) :
    ∀ c d, c < d → c ≤ upsilon l → upsilon l ≤ d → d ≤ upsilon (l + ω + 1) + v → ¬ le2 c d := by
  intro c d hcd hc hd hdg h2
  have hm := upsilon_normal.strictMono
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hδW : upsilon (l + ω + 1) < upsilon (l + ω * ω) := hm (by simpa using idx_lt l 0 1)
  have hWI := indec_of_upsPt (upsPt_upsilon (show 0 < l + ω * ω from lt_of_lt_of_le hl0 le_self_add))
  have hdW : d < upsilon (l + ω * ω) := lt_of_le_of_lt hdg (hWI.add_lt hδW (hv.trans hδW))
  have hdν : d < nuC := lt_of_lt_of_le hdW (Yx.yxNext_le_nuC hl hν)
  exact Yx.yxStd_noStraddle (std_of_lt_nuC hdν hcd h2) hl hc hd

/-- `υ_{λ+1} ≤ δ_λ`. -/
theorem zn_succ_le_delta (l : Ordinal.{0}) : upsilon (succ l) ≤ upsilon (l + ω + 1) :=
  upsilon_normal.strictMono.monotone
    (Order.succ_le_of_lt (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add))

/-- **Lemma RS at one restart with the value input**, from Lemma RS at the restarts of `(l₀, λ)`. -/
theorem znRs_val {O : Ordinal.{0} → Ordinal.{0}} {l0 B l : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B)
    (hν : upsilon B ≤ nuC) (hl : IsRestartIdx l) (hl0l : l0 < l) (hlB : l < B)
    (hval : ZnRsVal O l)
    (IH : ∀ μ, μ < l → IsRestartIdx μ → l0 < μ → μ < B →
      le1 (upsilon μ) (upsilon (μ + ω + 1) + O μ)) :
    le1 (upsilon l) (upsilon (l + ω + 1) + O l) := by
  have R := (Ys.ysTop_all Sp hl hl0l.le hlB).1
  have hlν : upsilon l < nuC := (upsilon_normal.strictMono hlB).trans_le hν
  have hlim : IsSuccLimit l := by
    obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
    have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
    rw [hq]
    exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
      (pos_iff_ne_zero.2 hq0)
  have hstep : ∀ z < O l, le1 (upsilon l) (upsilon (l + ω + 1) + z + 1) := by
    intro z hz
    obtain ⟨v, hzv, hv, hcof⟩ := hval z hz
    have htg : ∀ κ' < upsilon l, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon l ∧
        Ys.YsRstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
        ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + pi (upsilon μ) (upsilon l) v →
          le1 (upsilon μ) g := by
      intro κ' hκ'
      obtain ⟨_, ⟨ι, hι, rfl⟩, hκι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hκ'
      obtain ⟨μ, hμ, hιμ, hμl, htv⟩ := hcof (max ι l0) (max_lt hι hl0l)
      have hμB : μ < B := hμl.trans hlB
      have hl0μ : l0 < μ := (le_max_right _ _).trans_lt hιμ
      have Rμ := (Ys.ysTop_all Sp hμ hl0μ.le hμB).1
      have hrsμ := IH μ hμl hμ hl0μ hμB
      refine ⟨μ, hκι.trans (upsilon_normal.strictMono ((le_max_left _ _).trans_lt hιμ)), ?_, Rμ,
        fun g hg1 hg2 => le1_of_le_of_le1 hg1 (hg2.trans (add_le_add le_rfl htv)) hrsμ⟩
      exact upsilon_normal.strictMono (lt_of_lt_of_le (by simpa using idx_lt μ 0 1)
        (next_mult (ri_iff.1 hμ).2 (ri_iff.1 hl).2 hμl))
    refine le1_of_le_of_le1 (R.ρδ.le.trans (le_self_add.trans le_self_add))
      (add_le_add (add_le_add le_rfl hzv) le_rfl) ?_
    exact znRs_rstV R hv (znNostr_v hl hlν (hv.trans_le (zn_succ_le_delta l))) htg
  have hρδ := R.ρδ
  have hall : ∀ b', upsilon l ≤ b' → b' < upsilon (l + ω + 1) + O l → le1 (upsilon l) b' := by
    intro b' hb1 hb2
    rcases le_or_gt b' (upsilon (l + ω + 1)) with hbδ | hδb
    · exact R.le1ρδ b' hb1 hbδ
    · have he : upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) = b' :=
        Ordinal.add_sub_cancel_of_le hδb.le
      have hz : b' - upsilon (l + ω + 1) < O l := by
        rw [← he] at hb2; exact (add_lt_add_iff_left _).1 hb2
      have hb'le : b' ≤ upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) + 1 :=
        calc b' = upsilon (l + ω + 1) + (b' - upsilon (l + ω + 1)) := he.symm
          _ ≤ _ := le_self_add
      exact le1_of_le_of_le1 hb1 hb'le (hstep _ hz)
  rcases zero_or_succ_or_isSuccLimit (O l) with h0 | ⟨z0, hz0⟩ | hlimo
  · rw [h0, add_zero]; exact R.le1ρδ _ hρδ.le le_rfl
  · rw [← hz0, succ_eq_add_one, ← add_assoc]
    exact hstep z0 (by rw [← hz0]; exact lt_succ z0)
  · exact le1_limit (isSuccLimit_add _ hlimo)
      (lt_of_lt_of_le hρδ le_self_add) (fun b' hb1 hb2 => hall b' hb1 hb2)

/-- **Lemma RS at every restart of a specification below `ν_C`** with the input
`ZcRsIn ∨ ZhSupIn ∨ ZnRsVal`. -/
theorem znRs_all {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B)
    (hν : upsilon B ≤ nuC) (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hL0 : ∀ μ, CdRange S μ → μ ≤ l0 → CdLower S μ)
    (hin : ∀ l, IsRestartIdx l → l0 < l → l < B →
      Zc.ZcRsIn O l ∨ Zh.ZhSupIn S l B ∨ ZnRsVal O l) :
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
  rcases hin l hl hl0l hlB with hzc | ⟨β, hlβB, hrβ, hSup⟩ | hval
  · -- the old input: Lemma RS on the restricted specification up to `λ + ω²`
    have hm2 : ω * ω ∣ l + ω ^ 2 := by rw [← pow_two]; exact dvd_add hl.2 (dvd_refl _)
    have hlt2 : l < l + ω ^ 2 := lt_add_of_pos_right l (pow_pos omega0_pos 2)
    have Sp' := Zh.zhSpec_restr Sp hlw hm2 (hl0l.trans hlt2)
    refine Zc.zcRs_all Sp' (hm.monotone hlw |>.trans hν) (fun μ hμ h0μ hμB => ?_) l hl hl0l hlt2
    rcases lt_trichotomy μ l with hμl | rfl | hlμ
    · exact Or.inl (IH μ hμl hμ h0μ (hμl.trans hlB))
    · exact hzc
    · exact absurd hμB (not_lt.2 (Lr.lr_dvd_add_le hl.2 hμ.2 hlμ))
  · -- the supply input: LOWER at `λ` by the realizer maps
    rw [hRl]
    have hν' : upsilon (l + β) ≤ nuC := (hm.monotone hlβB).trans hν
    have hl1 : upsilon l < Om1 := hlν.trans_le nuC_le_Om1
    have hU : Zh.ZhUpIn S l β := by
      intro γ hγ0 hγd hγβ g hg
      have hγri : IsRestartIdx (l + γ) := Zh.zh_ri_add hl hγd
      have h0γ : l0 ≤ l + γ := hl0l.le.trans le_self_add
      have hγB : l + γ < B := lt_of_lt_of_le (Lr.lr_addL (a := l) hγβ) hlβB
      have htop := (Ys.ysTop_all Sp hγri h0γ hγB).2
      have e : upsilon (l + γ + ω + 1) + O (l + γ) = cdR S (l + γ) := by
        rw [hO (l + γ) (hl0l.trans_le le_self_add)]; exact Ys.ysO_eq S _
      by_contra hgt
      exact htop g (by rw [e]; exact not_le.1 hgt) hg
    have hS : Zh.ZhSupAt S l β := by
      intro x hx
      obtain ⟨μ, hR, h1, h2, h3, h4, h5⟩ := hSup (max x (upsilon l0)) (max_lt hx (hm hl0l))
      have hμ0 : l0 < μ := hm.lt_iff_lt.1 (lt_of_le_of_lt (le_max_right _ _) h1)
      refine ⟨μ, hR, (le_max_left _ _).trans_lt h1, h2, h3, h4, fun γ hγ0 hγd hγβ => ?_, h5⟩
      have hri := Zh.zh_ri_add hR.1 hγd
      have hlt : μ + γ < l := lt_of_lt_of_le (Lr.lr_addL (a := μ) hγβ) h3
      have h0γ : l0 < μ + γ := hμ0.trans_le le_self_add
      have := IH (μ + γ) hlt hri h0γ (hlt.trans hlB)
      rw [hO _ h0γ, Ys.ysO_eq] at this
      exact this
    have hR : Lr.LrReal S (upsilon l) (cdR S l) := Zh.zhReal_gen hl hl1 hlν hν' hrβ hU hS
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
  · -- the value input: Lemma RS with a value
    exact znRs_val Sp hν hl hl0l hlB hval fun μ hμl hμ h0μ hμB => IH μ hμl hμ h0μ hμB

/-- **The term input gives the value input** (`v = t(ρ_λ)`, Lemma EXACT `OT.pi_ev`; the cofinal restarts
are taken above the constants of `t`). -/
theorem znVal_of_term {O : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}} (hl : IsRestartIdx l)
    (hl1 : upsilon l < Om1) (h : Zc.ZcRsTerm O l) : ZnRsVal O l := by
  have hlim : IsSuccLimit l := by
    obtain ⟨q, hq⟩ := (ri_iff.1 hl).2
    have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hq; exact hl.1 hq
    rw [hq]
    exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
      (pos_iff_ne_zero.2 hq0)
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU : UpsPt (upsilon l) := upsPt_upsilon hl0
  intro z hz
  obtain ⟨t, ht, hzt, hcof⟩ := h z hz
  have hnx := upsilon_isNext l
  refine ⟨ev t (upsilon l), hzt, ev_lt (upsPt_inE hnx.2.1) hnx.1 t (CB_mono ht hnx.1.le), fun ν hν => ?_⟩
  -- a bound below `ρ_λ` for the constants of `t`
  set m : Ordinal.{0} := (insert 0 (cs t).toFinset).sup id with hmdef
  have hmρ : m < upsilon l := by
    rw [hmdef, Finset.sup_lt_iff hρU.1]
    intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hρU.1
    · exact (cb_iff t _).1 ht b (List.mem_toFinset.1 hb)
  obtain ⟨_, ⟨ι, hι, rfl⟩, hmι⟩ := (lt_isLUB_iff (upsilon_limit hlim)).1 hmρ
  obtain ⟨μ, hμ, hνμ, hμl, hle⟩ := hcof (max ν ι) (max_lt hν hι)
  have hιμ : ι < μ := (le_max_right _ _).trans_lt hνμ
  have hμρ : upsilon μ < upsilon l := upsilon_normal.strictMono hμl
  have hμ0 : 0 < μ := lt_of_le_of_lt zero_le hιμ
  have hB : Bases (upsilon μ) (upsilon l) :=
    ⟨upsPt_inE (upsPt_upsilon hμ0), upsPt_inE hρU, hμρ, hl1⟩
  have hCB : CB t (upsilon μ) := (cb_iff t _).2 fun c hc => by
    have hcm : c ≤ m := Finset.le_sup (f := id) (Finset.mem_insert_of_mem (List.mem_toFinset.2 hc))
    exact lt_of_le_of_lt hcm (hmι.trans (upsilon_normal.strictMono hιμ))
  refine ⟨μ, hμ, (le_max_left _ _).trans_lt hνμ, hμl, ?_⟩
  rw [(pi_ev hB t hCB).2]
  exact hle

/-- **NO-GO for the term input**: an `ε`-number `E` with `ρ_λ < E < O(λ)` refutes `Zc.ZcRsTerm O λ` (the values
of offset terms with constants below `ρ_λ` stay below every `ε`-number above `ρ_λ`). -/
theorem znRsTerm_false {O : Ordinal.{0} → Ordinal.{0}} {l E : Ordinal.{0}} (hE : InE E)
    (hρE : upsilon l < E) (hEO : E < O l) : ¬ Zc.ZcRsTerm O l := by
  intro h
  obtain ⟨t, ht, hzt, -⟩ := h E hEO
  exact absurd hzt (not_le.2 (ev_lt hE hρE t (CB_mono ht hρE.le)))

end Googology.Trans.PoR.InaccPsi.R2.Zn
