import Googology.Trans.PoR.InaccPsi.R2.LgB1
import Googology.Trans.PoR.InaccPsi.R2.XtW2

/-!
# The term layers above `Γ`: tops `Γ(x)·x^{ω·k+n}`, up to `Λ^Γ_{ω²} = sup_k Λ⁺(lim^k lgLay)`

`lgUSys` (top `Γ(x) = lgG x = ω^{Γ(x)}`) is a **layer** in the sense of `R2.XtLay` (`lgLay`): EXACT for its terms
(`LvGT.pi`) and for the exponent (`lg_pi`: `π_{σ,ρ}(Γ(ρ)) = Γ(σ)`, from `lgPi_OmOm` and `pi_vt_two`), and the
witness pair of the top (`LgK.lgTopWit`: `f(Γ(ρ)) ∈ E`, `Γ(f ρ) ≤ f(Γ(ρ))`).  So the generic constructions of
`R2.XtLay`, `R2.XtLim`, `R2.XtChain`, `R2.XtFam` apply:

* `lgLL k = lim^k lgLay` (top `Γ(x)·x^{ω·k}`, `lgLL_top`), its next layers `(lgLL k).iter n` (top `Γ(x)·x^{ω·k+n}`);
* `lgLamK k = Λ⁺(lgLL k)`, `lgLamK_zero` (`= Λ⁺(lgUSys)`), `lgLamK_lt`, `lgLL_eq`; `lgFamW2 : XtFam`;
* `lgW2_blk` (**Theorem BLK^O below `υ_{Λ^Γ_{ω²}}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O_{LL k}(λ)`),
  `lgLL_reachLam` (**`lh(ρ) = δ + Γ(ρ)·ρ^{ω·k}` at `Λ(lgLL k)`**), `lgLL_reachB1` (`lh(ρ) = δ + Γ(ρ)·ρ^{ω·k+n} + 1` at
  `Λ⁺((lgLL k).iter n)`);
* `lgW2_init` (**UPPER and LOWER at every non-fixed restart of the range below `Λ^Γ_{ω²}`**), `lgW2_capV` (CapV
  there), `lgW2_THfix` (the notation hypothesis below `Λ^Γ_{ω²}` from the fixed points `≥ Λ⁺(lgUSys)` alone: below
  it is `lgUT_fix`), `lgW2Enum` (ENUM-REACH at every restart of the range below `Λ^Γ_{ω²}` given that hypothesis),
  `lgW2Road3` (**the road with UPPER/LOWER asked only at `λ ≥ Λ^Γ_{ω²}` and the notation hypothesis only at the fixed
  points in `[Λ⁺(lgUSys), Λ^Γ_{ω²})`**).

No new axiom beyond `R2.CitedLg` (`lgPi_OmOm` here) and `R2.CitedXt` (through `R2.XtLim`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

section Base

variable {σ ρ : Ordinal.{0}}

/-- **EXACT for the limit top**: `Γ(ρ) ∈ Tᵖ[σ]` and `π_{σ,ρ}(Γ(ρ)) = Γ(σ)`. -/
theorem lg_pi (hB : Bases σ ρ) : lgG ρ ∈ TB ρ σ ∧ pi σ ρ (lgG ρ) = lgG σ := by
  obtain ⟨hσE, hρE, hσρ, hρ1⟩ := hB
  have hσ1 : σ < Om1 := hσρ.trans hρ1
  have h2 : Om1 * Om1 < OmTwo := by simpa using lg_OmOm_lt (Ordinal.omega_pos 1)
  obtain ⟨hTB, hpi⟩ := lgPi_OmOm ⟨hσE, hρE, hσρ, hρ1⟩
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hρE hρ1 hTB.1 h2
  rw [← lgV_eq hρE hρ1, ← lgV_eq hσE hσ1]
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * Om1))) ⊆ Set.Iio σ
    rw [hPar]; exact hTB.2
  · show pi σ ρ (vt ρ (Om1 * Om1)) = vt σ (Om1 * Om1)
    rw [pi_vt_two ⟨hσE, hρE, hσρ, hρ1⟩ hTB h2, hpi]

end Base

namespace LgK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **The witness pair of the limit top**: `f(Γ(ρ)) = ω^{e'}` with `ω^{f ρ} ∣ e'`, and `Γ(f ρ) ≤ f(Γ(ρ))`. -/
theorem lgTopWit : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lgG ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      (∃ e', f (lgG ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e') ∧ lgG (f ρ) ≤ f (lgG ρ) := by
  classical
  have hρE := upsPt_inE h.ρU
  obtain ⟨-, hρG, -, hGE, hGI⟩ := lgG_facts hρE h.ρ1
  set G := lgG ρ with hG
  set P := G * G with hP
  have hGδ : G < δ := lgG_lt_δ h
  have hPδ : P < δ := h.δE.mul_lt hGδ hGδ
  have hGGδ : G + G < δ := (inE_indec h.δE).add_lt hGδ hGδ
  have hPGδ : P + G < δ := (inE_indec h.δE).add_lt hPδ hGδ
  have hG0 : 0 < G := hGE.pos
  have hGP : G < P := lt_mul_of_one_lt_right hG0 (Lu.lu_one_lt_E hGE)
  have hPe : P = ω ^ (G + G) := by
    rw [hP]; conv_lhs => rw [← show ω ^ G = G from hGE]
    rw [← opow_add]
  have w1 : WZ ρ δ {G} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW hρG.le hGδ (Or.inl hGI)
    simpa using this
  have w2 : WZ ρ δ {G + G, G} ∅ := by
    have := w1.insW (hρG.le.trans le_self_add) hGGδ
      (Or.inr ⟨G, by simp, G, by simp, lt_add_of_pos_right _ hG0, lt_add_of_pos_right _ hG0, rfl⟩)
    simpa using this
  have w3 : WZ ρ δ {P, G + G, G} ∅ := by
    have := w2.insW (hρG.le.trans hGP.le) hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
    simpa using this
  have w4 : WZ ρ δ {P + G, P, G + G, G} ∅ := by
    have := w3.insW ((hρG.le.trans hGP.le).trans le_self_add) hPGδ
      (Or.inr ⟨P, by simp, G, by simp, lt_add_of_pos_right _ hG0, hGP.trans_le le_self_add, rfl⟩)
    simpa using this
  refine ⟨{P + G, P, G + G, G}, ∅, w4, by simp, fun A f hW hZ C => ?_⟩
  have hGA : G ∈ A := hW (by simp)
  have hGGA : G + G ∈ A := hW (by simp)
  have hPA : P ∈ A := hW (by simp)
  have hPGA : P + G ∈ A := hW (by simp)
  obtain ⟨hfE, -⟩ := lgImgP h C hGA hGGA hPA hPGA
  have hyG : f ρ < f G := C.mono C.rho hGA hρG
  refine ⟨⟨f G, hfE.symm, opow_dvd_of_inE hfE hyG.le⟩, ?_⟩
  obtain ⟨hyE, hy1, -⟩ := h.vz_img_base C
  obtain ⟨-, hsq⟩ := lgImgP h C hGA hGGA hPA hPGA
  by_cases hU : UpsPt (f G)
  · exact lgG_le fun n => (LvGT.lvg_top_lt_next hyE hy1 n hyG hU.2).le
  · by_contra hlt
    push Not at hlt
    exact lg_not_le1R_sq hyE hy1 hfE hyG hlt (hsq hU)

end LgK

/-- **`lgUSys` as a layer.** -/
noncomputable def lgLay : XtLay where
  sys := lgUSys
  E := lgG
  top_eq := fun x hx hx1 => (lgG_inE x hx hx1).symm
  exp_dvd := fun x hx hx1 => opow_dvd_of_inE (lgG_inE x hx hx1) (lgG_facts hx hx1).2.1.le
  exp_lt := fun _ hx hx1 => lgG_lt_Om1 hx hx1
  top_gt := fun _ hx hx1 => (lgG_facts hx hx1).2.1
  top_lt_ups := fun x u hx hx1 hxu hu => by
    obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hx) hx1
    obtain ⟨hGT, -, hG1, -, -⟩ := lgG_facts hx hx1
    exact ((hTm _ hG1).1 hGT).trans_le (hmin u hxu hu.2)
  lt_top_E := fun _ hx hx1 t ht => (LvGT.lvg_T hx hx1 t ht).2.trans (gT_lt_lgG hx hx1 _)
  exact := fun _ _ hσ hρ hB t ht => LvGT.pi hσ hρ hB t ht
  exp_pi := fun _ _ _ _ hB => lg_pi hB
  top_wit := fun _ _ _ h => LgK.lgTopWit h

theorem lgLay_sys : lgLay.sys = lgUSys := rfl

/-- **The `k`-th limit layer** `lim^k lgLay` (top `Γ(x)·x^{ω·k}`). -/
noncomputable def lgLL : ℕ → XtLay
  | 0 => lgLay
  | k + 1 => (lgLL k).xtLim

theorem lgLL_top (k : ℕ) (x : Ordinal.{0}) : (lgLL k).sys.top x = lgG x * x ^ (ω * (k : Ordinal.{0})) := by
  induction k with
  | zero => show lgG x = _; rw [Nat.cast_zero, mul_zero, opow_zero, mul_one]
  | succ k ih =>
    show (lgLL k).sys.top x * x ^ ω = _
    rw [ih, Nat.cast_succ, mul_add_one, opow_add, mul_assoc]

theorem lgLL_iter_top (k n : ℕ) (x : Ordinal.{0}) :
    ((lgLL k).iter n).sys.top x = lgG x * x ^ (ω * (k : Ordinal.{0}) + (n : Ordinal.{0})) := by
  rw [XtLay.iter_top, lgLL_top, opow_add, mul_assoc]

/-- `Λ⁺_k(Γ)`: the first limit of the frontiers of the `k`-th limit layer. -/
noncomputable def lgLamK (k : ℕ) : Ordinal.{0} := xtB1 (lgLL k).sys

theorem lgLamK_zero : lgLamK 0 = xtB1 lgUSys := rfl

theorem lgLamK_lt (k : ℕ) : lgLamK k < lgLamK (k + 1) :=
  ((lgLL k).lim_gt 0).trans (lgLL k).xtLim.xtLamLt

theorem lgLamK_lt_Om1 (k : ℕ) : lgLamK k < Om1 := xtB1_lt_Om1 (lgLL k).topPkg

theorem lgLamK_strictMono : StrictMono lgLamK := strictMono_nat_of_lt_succ lgLamK_lt

/-- `O_{LL m} = O_{LL k}` below `Λ⁺_k(Γ)` for `k ≤ m`. -/
theorem lgLL_eq {k m : ℕ} (h : k ≤ m) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμk : μ < lgLamK k) :
    xtOrec (lgLL m).sys μ = xtOrec (lgLL k).sys μ := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    rw [← ih]
    exact (lgLL m).lim_eq 0 hμ (hμk.trans_le (lgLamK_strictMono.monotone hkm))

/-- `O_{LL k} = O_U` below `Λ⁺(lgUSys)`. -/
theorem lgLL_eq_U (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμk : μ < xtB1 lgUSys) :
    xtOrec (lgLL k).sys μ = xtOrec lgUSys μ :=
  lgLL_eq (Nat.zero_le k) hμ hμk

/-- **The family of the limit layers over `Γ`**: bounds `Λ⁺_k(Γ)`, offsets `O_{LL k}`. -/
noncomputable def lgFamW2 : XtFam where
  bd := lgLamK
  off := fun k => xtOrec (lgLL k).sys
  spec := fun k => xtSpec1 (lgLL k).topPkg
  mono := lgLamK_lt
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (lgLamK_lt_Om1 k))

theorem lgFamW2_sup : lgFamW2.famSup = ⨆ k : ℕ, lgLamK k := rfl

theorem lgU_B1_lt_W2 : xtB1 lgUSys < lgFamW2.famSup := lgFamW2.famBd_lt 0

/-- **The reach at the frontier of `lgLL k`**: `lh(ρ) = δ + Γ(ρ)·ρ^{ω·k}`. -/
theorem lgLL_reachLam (k : ℕ) :
    IsReach R2C (upsilon (xtLam (lgLL k).sys))
      (upsilon (xtLam (lgLL k).sys + ω + 1) +
        lgG (upsilon (xtLam (lgLL k).sys)) * upsilon (xtLam (lgLL k).sys) ^ (ω * (k : Ordinal.{0}))) := by
  rw [← lgLL_top, ← xtOrec_Lam]
  exact xtReach1 (lgLL k).topPkg xtLam_ri (lgLL k).xtLamLt

/-- **The reach at `Λ⁺((lgLL k).iter n)`**: `lh(ρ) = δ + Γ(ρ)·ρ^{ω·k+n} + 1`. -/
theorem lgLL_reachB1 (k n : ℕ) :
    IsReach R2C (upsilon (xtB1 ((lgLL k).iter n).sys))
      (upsilon (xtB1 ((lgLL k).iter n).sys + ω + 1) +
        (lgG (upsilon (xtB1 ((lgLL k).iter n).sys)) *
          upsilon (xtB1 ((lgLL k).iter n).sys) ^ (ω * (k : Ordinal.{0}) + (n : Ordinal.{0})) + 1)) := by
  rw [← lgLL_iter_top]; exact ((lgLL k).iter n).reachB1

/-- **Theorem BLK^O below `υ_{Λ^Γ_{ω²}}`** in `R₂^C`. -/
theorem lgW2_blk :
    (∀ c d, c < d → d < upsilon lgFamW2.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lgFamW2.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lgLamK k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lgLL k).sys l)) ∧
    (∀ α < upsilon lgFamW2.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lgFamW2.famBlk

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ^Γ_{ω²}` that is not a fixed point of `υ`.** -/
theorem lgW2_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lgFamW2.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  lgFamW2.famInit hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ^Γ_{ω²}`.** -/
theorem lgW2_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lgFamW2.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lgFamW2.famCapV hr hl hfix

/-- **The notation hypothesis below `Λ^Γ_{ω²}` from the fixed points `≥ Λ⁺(lgUSys)` alone.** -/
theorem lgW2_THfix
    (hT : ∀ k l, CdRange S l → xtB1 lgUSys ≤ l → l < lgLamK k → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lgLL k).sys l) :
    lgFamW2.famTHfix S := by
  intro k l hr hlk hfix
  rcases lt_or_ge l (xtB1 lgUSys) with h | h
  · show cdTheta S l (cdCode S l) = xtOrec (lgLL k).sys l
    rw [lgLL_eq_U k hr.1 h]; exact lgUT_fix hr h hfix
  · exact hT k l hr h hlk hfix

/-- **ENUM-REACH at every restart of the range below `Λ^Γ_{ω²}`**, given the notation hypothesis at the fixed points in
`[Λ⁺(lgUSys), Λ^Γ_{ω²})`. -/
theorem lgW2Enum
    (hT : ∀ k l, CdRange S l → xtB1 lgUSys ≤ l → l < lgLamK k → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lgLL k).sys l)
    {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lgFamW2.famSup) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lgW2_init hr hl hnf
  · obtain ⟨k, hk⟩ := lgFamW2.famLt hl
    exact ((lgFamW2.famIff k hr.1 hk).2.2).2 (lgW2_THfix hT k l hr hk hfx.symm)

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ^Γ_{ω²}`**, the notation hypothesis only at the fixed points in
`[Λ⁺(lgUSys), Λ^Γ_{ω²})`, the cap of the values outside `Λ^Γ_{ω²}`, (CL), EQ, TCrest, (EMB₂). -/
theorem lgW2Road3 (hU : ∀ l, CdRange S l → lgFamW2.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lgFamW2.famSup ≤ l → CdLower S l)
    (hT : ∀ k l, CdRange S l → xtB1 lgUSys ≤ l → l < lgLamK k → upsilon l = l →
      cdTheta S l (cdCode S l) = xtOrec (lgLL k).sys l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lgFamW2.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lgFamW2.famRoad3 hU hL (lgW2_THfix hT) hV hC hEQ hrest hB2

end Googology.Trans.PoR.InaccPsi.R2
