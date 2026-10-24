import Googology.Trans.PoR.InaccPsi.R2.GhUnif

/-!
# WHERE THE FRONTIERS LIE, for every code `ε_{Ω₁+1}·(n+1) + a`: `Λ⁺(ghB n a) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω)` and
the supremum `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`

For a code `a < ε_{Ω₁+1}` with gate below `ε₀`, the gated layer `ghB n a` (`R2.GhTow`) is an ungated layer `ghLX n a`
(`Ge.geLayX`); its top reads the atom `Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}` and it has terms for every code below it
(`R2.GhUnif.ghB_codes`), so the frontier lemma `R2.GhFr.ghB1_eq` locates its frontier:

* `ghLX`, `ghX`, `ghLoc` (**`Λ⁺(ghX n a) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω)`, `ρ` of it `= P(…) < L(0)`**), `ghFix`
  (THEOREM UNI at the fixed range restarts below it), `ghEnum` (**ENUM-REACH at every range restart below it, fixed
  points included**), `ghCapV`, `ghBlk` (**BLK^O and the exact reaches below `υ` of it**);
* `ghXk k` (the code `ε_{Ω₁+1}·(k+1)`), `ghFam`, `ghFam_sup` (**`sup_k Λ⁺(ghXk k) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`, `υ` of
  it `= P(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) < L(0)`**), `ghFam_enum`, `ghFam_capV`, `ghFam_blk`, `ghFam_road` (**THE ROAD with
  UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`**), `gh_fr_order` (**`ι(Γ_{Ω₁+1+ε_{Ω₁+1}}) ≤
  ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) < ι(Ω₂)`, `P(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) < P(Ω₂) < L(0)`**).

No new axiom.  New definitions: `ghLX`, `ghX`, `ghXk`, `ghFam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gh

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The layer of a code with small digits -/

/-- **The layer of the code `ε_{Ω₁+1}·(n+1) + a`** (gate below `ε₀`), ungated. -/
noncomputable def ghLX (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : XtLay :=
  geLayX (ghB n a ha).K (by rw [ghB_g]; exact hg)

/-- Its term system. -/
noncomputable def ghX (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : XtSys := (ghLX n ha hg).sys

section Code

variable (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀)
include ha hg

theorem ghX_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (ghX n ha hg).top x = gq (ghBs n x + rdc a x) x :=
  ghB_top n ha hx hx1 (ge_gx hg hx)

theorem ghX_pkg : XtTopPkg (ghX n ha hg) := XtLay.topPkg (ghLX n ha hg)

theorem ghT_le : gcG (ghC n a) ≤ ghV := (gcG_lt (ghC_lt n ha)).le

theorem ghX_cl : ∀ Z, SC Z → GxCl Z (ghAt Z) (gcG (ghC n a)) := fun Z hZ =>
  ghC_atom n ha (ge_gx hg (gg_SC_eps hZ))

theorem ghX_poly (S : InaccSeq.{0}) : GhPoly (ghX n ha hg) (gcG (ghC n a)) := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := (ghB_codes S n a ha).2 (max Z ε₀) c (by rw [ghB_g]; exact hg.trans_le (le_max_right _ _))
    (ghCl_mono (le_max_left _ _) hc) hcE
  exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (max_le hZy (gc_eps0_le (gg_SC_eps hy)))⟩

theorem ghX_topth (S : InaccSeq.{0}) : ∀ y, SC y → y < Om 1 →
    (ghX n ha hg).top y = gxTh y (ghAt y) (gcG (ghC n a)) := by
  intro y hy hy1
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  rw [ghX_top n ha hg hyE hy1', ← ghB_E n ha hyE hy1' (ge_gx hg hyE)]
  exact (ghB_codes S n a ha).1 y hy hy1 (ge_gx hg hyE)

theorem ghX_topE : ∀ x, InE x → x < Om1 → eN x < (ghX n ha hg).top x := by
  intro x hx hx1
  rw [ghX_top n ha hg hx hx1]
  obtain ⟨hT, h1⟩ := gfq_T hx hx1 (ghO_lt hx hx1 n a (ge_gx hg hx))
  exact (gh_eN_lt_gq0 hx hx1).trans_le (gfq0_le hx hx1 hT h1)

/-- **WHERE THE FRONTIER OF THE CODE `ε_{Ω₁+1}·(n+1) + a` LIES**: `Λ⁺(ghX n a) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω)`,
`ρ` of it `= P(…) < L(0)`. -/
theorem ghLoc (S : InaccSeq.{0}) :
    xtB1 (ghX n ha hg) = iota S (gcG (ghC n a) * ω) ∧
    upsilon (xtB1 (ghX n ha hg)) = Pv S (gcG (ghC n a) * ω) ∧ Pv S (gcG (ghC n a) * ω) < Nc.ncL S 0 := by
  have h := ghB1_eq (S := S) (ghT_le n ha hg) (ghX_poly n ha hg S) (ghX_topth n ha hg S) (ghX_cl n ha hg)
    (gcG_Om1_lt _).le (ghX_topE n ha hg) (ghX_pkg n ha hg)
  rwa [geG_E] at h

/-- **`Θ_F(m_F) = O(F)` at every fixed range restart below `Λ⁺(ghX n a)`** (THEOREM UNI). -/
theorem ghFix (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 (ghX n ha hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (ghX n ha hg) l := by
  have hlt : l < iota S (ω ^ gcG (ghC n a) * ω) := by rw [geG_E, ← (ghLoc n ha hg S).1]; exact hl
  exact ghUniTh (ghT_le n ha hg) (ghX_poly n ha hg S) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem ghX_nonfix : XtNonfix (xtOrec (ghX n ha hg)) (xtB1 (ghX n ha hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (ghX_pkg n ha hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω)`, fixed points included.** -/
theorem ghEnum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (ghC n a) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (ghLoc n ha hg S).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (ghX_pkg n ha hg)) (ghX_nonfix n ha hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (ghX_pkg n ha hg)) hr.1 hl).2 (ghFix n ha hg S hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω)`, fixed points included.** -/
theorem ghCapV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (ghC n a) * ω)) :
    CdCapV S l := by
  have hl' := hl
  rw [← (ghLoc n ha hg S).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (ghX_pkg n ha hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (ghX_nonfix n ha hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (ghX_pkg n ha hg) hr hl' hfx.symm (ghEnum n ha hg S hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(ghX n a)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem ghBlk :
    (∀ c d, c < d → d < upsilon (xtB1 (ghX n ha hg)) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (ghX n ha hg) ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (ghX n ha hg) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (ghX n ha hg) l)) ∧
    (∀ α < upsilon (xtB1 (ghX n ha hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (ghX_pkg n ha hg)

end Code

/-! ## The starts `ε_{Ω₁+1}·(k+1)` and the supremum `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})` -/

theorem gh0_lt : (0 : Ordinal.{0}) < gfE := eW_E.pos

theorem gh0_g : gtc (0 : Ordinal.{0}) < ε₀ := by rw [gtc_zero]; exact epsilon_pos 0

/-- The `k`-th member of the family: the code `ε_{Ω₁+1}·(k+1)`. -/
noncomputable def ghXk (k : ℕ) : XtSys := ghX k gh0_lt gh0_g

theorem ghGood_mul {c : Ordinal.{0}} (hc : c < ghE) (hgc : ghg c < ε₀) (S : InaccSeq.{0}) :
    Bt.Good S (gcG c * ω) := by
  refine gh_good fun Z hZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (GxCl.atom (ghG_atom hc (ge_gx hgc (gg_SC_eps hZ))))
    (GxCl.small (gg_one_lt_of_SC hZ)))

theorem ghC0_g (k : ℕ) : ghg (ghC k 0) < ε₀ := by rw [ghC_g k gh0_lt]; exact gh0_g

theorem ghE_lim : IsSuccLimit ghE := by
  rw [ghE_eq]
  exact ⟨not_isMin_iff_ne_bot.2 (opow_pos _ omega0_pos).ne', isSuccPrelimit_iff_omega0_dvd.2
    (by
      calc ω = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
        _ ∣ ω ^ (gfE + 1) := opow_dvd_opow ω (le_add_self))⟩

/-- **The starts are cofinal in `ε_{Ω₁+1}·ω`.** -/
theorem ghC_cof {c : Ordinal.{0}} (hc : c < ghE) : ∃ k : ℕ, c < ghC k 0 := by
  obtain ⟨m, hm⟩ := gh_div_nat hc
  refine ⟨m, ?_⟩
  rw [ghC, add_zero]
  have := (Ordinal.div_lt gfE_ne).1 (show c / gfE < ((m + 1 : ℕ) : Ordinal.{0}) by
    rw [hm]; exact_mod_cast Nat.lt_succ_self m)
  exact this

/-- **The family of the layers of the starts `ε_{Ω₁+1}·(k+1)`.** -/
noncomputable def ghFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (ghXk k)
  off := fun k => xtOrec (ghXk k)
  spec := fun k => xtSpec1 (ghX_pkg _ _ _)
  mono := fun k => by
    show xtB1 (ghXk k) < xtB1 (ghXk (k + 1))
    unfold ghXk
    rw [(ghLoc _ _ _ S).1, (ghLoc _ _ _ S).1]
    refine cd_iota_lt_of_good (ghGood_mul (ghC_lt k gh0_lt) (ghC0_g k) S) ?_
    have hE := geG_E (ghC (k + 1) 0)
    have hlt : ghC k 0 < ghC (k + 1) 0 := by
      rw [ghC_next]; exact ghC_lt' k eW_E.pos
    exact (InE.mul_lt hE (gcG_lt hlt) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => ghX_nonfix _ _ _

theorem ghXk_loc (S : InaccSeq.{0}) (k : ℕ) : xtB1 (ghXk k) = iota S (gcG (ghC k 0) * ω) := by
  unfold ghXk; rw [(ghLoc _ _ _ S).1]

/-- **`sup_k Λ⁺(ghXk k) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`, `υ` of it `= P(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) < L(0)`.** -/
theorem ghFam_sup (S : InaccSeq.{0}) : (ghFam S).famSup = iota S ghV ∧ upsilon (ghFam S).famSup = Pv S ghV ∧
    Pv S ghV < Nc.ncL S 0 := by
  have hVS := ghV_SC
  have hVE : ω ^ ghV = ghV := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < ghE → gcG c * ω < ghV := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (ghFam S).famSup = iota S ghV := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (ghXk k) ≤ _
      rw [ghXk_loc S k]
      exact iota_mono _ _ (hstep _ (ghC_lt k gh0_lt)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit ghE_lim e.2
      obtain ⟨n, hn⟩ := ghC_cof hc
      have h1 : e.1 < gcG (ghC n 0) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (ghC n 0) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (ghXk n) := (ghXk_loc S n).symm
        _ ≤ (ghFam S).famSup := ((ghFam S).famBd_lt n).le
  have hups : upsilon (ghFam S).famSup = Pv S ghV := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (ghV_lt_Om2 S).le⟩

theorem ghFam_fix (S : InaccSeq.{0}) : (ghFam S).famTHfix S :=
  fun k _ hr hlk hfix => ghFix _ _ _ S hr hlk hfix

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`, fixed points included.** -/
theorem ghFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S ghV) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (ghFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (ghFam S).famLt hl
  have hk' : l < iota S (gcG (ghC k 0) * ω) := by rw [← ghXk_loc S k]; exact hk
  exact ghEnum k gh0_lt gh0_g S hr hk'

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`, fixed points included.** -/
theorem ghFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S ghV) :
    CdCapV S l := by
  rw [← (ghFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (ghFam S).famLt hl
  have hk' : l < iota S (gcG (ghC k 0) * ω) := by rw [← ghXk_loc S k]; exact hk
  exact ghCapV k gh0_lt gh0_g S hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})} = P(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})`**, with the exact reaches. -/
theorem ghFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (ghFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (ghFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (ghFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (ghFam S).off k l)) ∧
    (∀ α < upsilon (ghFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (ghFam S).famBlk

/-- **THE ROAD past every code below `ε_{Ω₁+1}·ω`**: UPPER, LOWER and CapV asked only at
`λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω})` (CapV also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`,
`L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem ghFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S ghV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S ghV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S ghV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hF := (ghFam_sup S).1
  refine (ghFam S).famRoad3 (fun l hr h => hU l hr (hF ▸ h)) (fun l hr h => hL l hr (hF ▸ h)) (ghFam_fix S)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (ghFam S).famSup l with h | h
  · exact hV l hr hlω (hF ▸ h)
  · exact ghFam_capV S hr (hF ▸ h)

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+ε_{Ω₁+1}}) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}·(n+1)+a}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) <
ι(Ω₂)`, and `P(Γ_{Ω₁+1+ε_{Ω₁+1}·ω}) < P(Ω₂) < L(0)`, for every `n` and every code `a < ε_{Ω₁+1}` with digits below
`ε₀` (past the last frontier `ι(Γ_{Ω₁+1+ε_{Ω₁+1}})` of `R2.GfLoc`). -/
theorem gh_fr_order (n : ℕ) {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) :
    iota S gfV < iota S (gcG (ghC n a) * ω) ∧ iota S (gcG (ghC n a) * ω) < iota S ghV ∧
      iota S ghV < iota S (Om (1 + 1)) ∧ Pv S ghV < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hgfE : ghg gfE < ε₀ := by rw [ghg, Ordinal.mod_self, gtc_zero]; exact epsilon_pos 0
  have hgV : Bt.Good S gfV := gh_good fun Z hZ => GxCl.atom (ghG_atom gfE_lt_ghE (ge_gx hgfE (gg_SC_eps hZ)))
  have hc := ghC_lt n ha
  have hg1 : ghg (ghC n a) < ε₀ := by rw [ghC_g n ha]; exact hg
  have hVE : ω ^ ghV = ghV := Low.opow_eq_self_of_SC ghV_SC
  have hghV : Bt.Good S ghV := by
    show ghV ∈ S.CSet (ConjT.Aη S ghV + 1) (S.psi (ConjT.Aη S ghV) (Om 1))
    have := CSet.psi_mem (S := S) (a := ConjT.Aη S ghV + 1) (b := S.psi (ConjT.Aη S ghV) (Om 1))
      (gh_W_lt_A1 (S := S) ghV) (InR_Om_succ 1) (ga_Om2_mem _ _) (ghE_inC (S := S))
    rwa [ghV_psi S] at this
  have hEa : gfE ≤ ghC n a := by
    unfold ghC
    calc gfE = gfE * 1 := (mul_one _).symm
      _ ≤ gfE * ((n + 1 : ℕ) : Ordinal.{0}) := mul_le_mul_left' (by exact_mod_cast Nat.succ_pos n) _
      _ ≤ _ := le_self_add
  have hla : gfV < gcG (ghC n a) * ω :=
    (gcG_le hEa).trans_lt (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  have h1 : iota S gfV < iota S (gcG (ghC n a) * ω) := cd_iota_lt_of_good hgV hla
  have h2 : iota S (gcG (ghC n a) * ω) < iota S ghV :=
    cd_iota_lt_of_good (ghGood_mul hc hg1 S) (InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE))
  have h3 : iota S ghV < iota S (Om (1 + 1)) := cd_iota_lt_of_good hghV (ghV_lt_Om2 S)
  have h4 : Pv S ghV < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h3
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h1, h2, h3, h4, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gh
