import Googology.Trans.PoR.InaccPsi.R2.GfUnif
import Googology.Trans.PoR.InaccPsi.R2.GeLoc

/-!
# WHERE THE FRONTIERS LIE, for every code below `ε_{Ω₁+1}`: `Λ⁺(gfB a) = ι(Γ_{Ω₁+2+a}·ω)` and the supremum
`ι(Γ_{Ω₁+1+ε_{Ω₁+1}})`

For a code `a < ε_{Ω₁+1}` whose gate lies below `ε₀` (so it lies below every base), the gated layer `gfB a`
(`R2.GfTow`) is an ungated layer `gfLX a` (`Ge.geLayX`); its top reads the atom `Γ_{Ω₁+1+(1+a)}` and it has terms
for every code below it (`R2.GfUnif.gfB_codes`), so the frontier lemma `R2.GfFr.gfB1_eq` locates its frontier:

* `gfX a`, `gfLX a`, `gfLoc` (**`Λ⁺(gfX a) = ι(Γ_{Ω₁+2+a}·ω)`, `ρ` of it `= P(…) < L(0)`**), `gfFix` (THEOREM UNI at
  the fixed range restarts below it), `gfEnum` (**ENUM-REACH at every range restart below `ι(Γ_{Ω₁+2+a}·ω)`, fixed
  points included**), `gfCapV` (**CapV there**), `gfBlk` (**BLK^O and the exact reaches below `υ` of it**);
* the tower `gfTw` (`c₀ = Ω₁+1`, `c_{k+1} = ω^{c_k}`, gate below `ε₀`, cofinal in `ε_{Ω₁+1}`), `gfFam` (the family of
  its layers), `gfFam_sup` (**`sup_k Λ⁺(gfX c_k) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}})`, `υ` of it `= P(Γ_{Ω₁+1+ε_{Ω₁+1}}) <
  L(0)`**), `gfFam_enum`, `gfFam_capV`, `gfFam_blk`, `gfFam_road` (**THE ROAD with UPPER, LOWER and CapV asked only
  at `λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}})`**), `gf_fr_order` (**`ι(Γ_{Ω₁+Ω₁^ω}) < ι(Γ_{Ω₁+2+a}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}}) <
  ι(Ω₂)`, `P(Γ_{Ω₁+1+ε_{Ω₁+1}}) < L(0)`** for every code `Ω₁^ω ≤ a`).

No new axiom.  New definitions: `gfX`, `gfLX`, `gfTw`, `gfXk`, `gfFam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gf

open Googology.Trans.PoR.InaccPsi.R2.Ge
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The layer of a code with small digits -/

/-- **The layer of the code `a`** (gate below `ε₀`), ungated. -/
noncomputable def gfLX {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : XtLay := geLayX (gfB a ha).K
    (by rw [gfB_g]; exact hg)

/-- Its term system. -/
noncomputable def gfX {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : XtSys := (gfLX ha hg).sys

theorem gfX_top {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    (gfX ha hg).top x = gq (1 + rdc a x) x :=
  gfB_top ha hx hx1 (ge_gx hg hx)

theorem gfX_pkg {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : XtTopPkg (gfX ha hg) := XtLay.topPkg (gfLX ha hg)

theorem gfT_lt {a : Ordinal.{0}} (ha : a < gfE) : 1 + a < gfE := eW_indec.add_lt
    ((Lu.lu_one_lt_E Rj.rj_Om1_inE).trans Om1_lt_eW) ha

theorem gfT_le {a : Ordinal.{0}} (ha : a < gfE) : gcG (1 + a) ≤ gfV := (gcG_lt (gfT_lt ha)).le

theorem gfX_cl {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : ∀ Z, SC Z → GxCl Z (gfAt Z) (gcG
    (1 + a)) := fun Z hZ => by
  obtain ⟨h1, h2⟩ := gtc_one_add ha hZ.isSuccLimit (ge_gx hg (gg_SC_eps hZ))
  exact GxCl.atom (gfG_atom h1 h2)

theorem gfX_poly {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) : GfPoly (gfX ha hg) (gcG
    (1 + a)) := by
  intro Z c hc hcE
  obtain ⟨s, hs⟩ := (gfB_codes S a ha).2 (max Z ε₀) c (by rw [gfB_g]; exact hg.trans_le (le_max_right _ _))
    (gfCl_mono (le_max_left _ _) hc) hcE
  exact ⟨s, fun y hy hy1 hZy => hs y hy hy1 (max_le hZy (gc_eps0_le (gg_SC_eps hy)))⟩

theorem gfX_topth {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) : ∀ y, SC y → y < Om 1 →
    (gfX ha hg).top y = gxTh y (gfAt y) (gcG (1 + a)) := by
  intro y hy hy1
  have hyE := gg_SC_eps hy
  have hy1' := lp_y1 hy1
  rw [gfX_top ha hg hyE hy1', ← gfB_E ha hyE hy1' (ge_gx hg hyE)]
  exact (gfB_codes S a ha).1 y hy hy1 (ge_gx hg hyE)

theorem gfX_topE {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : ∀ x, InE x → x < Om1 → eN x <
    (gfX ha hg).top x := by
  intro x hx hx1
  rw [gfX_top ha hg hx hx1]
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  refine (geq_eN_le hx hx1 h0T (hx.pos.trans hx1)).trans_lt (geq_lt hx hx1 (gfO_lt ha hx (ge_gx hg hx)) ?_)
  exact lt_of_lt_of_le zero_lt_one le_self_add

/-- **WHERE THE FRONTIER OF THE CODE `a` LIES**: `Λ⁺(gfX a) = ι(Γ_{Ω₁+2+a}·ω)`, `ρ` of it `= P(…) < L(0)`. -/
theorem gfLoc {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) :
    xtB1 (gfX ha hg) = iota S (gcG (1 + a) * ω) ∧
    upsilon (xtB1 (gfX ha hg)) = Pv S (gcG (1 + a) * ω) ∧ Pv S (gcG (1 + a) * ω) < Nc.ncL S 0 := by
  have h := gfB1_eq (S := S) (gfT_le ha) (gfX_poly ha hg S) (gfX_topth ha hg S) (gfX_cl ha hg) (gcG_Om1_lt _).le
    (gfX_topE ha hg) (gfX_pkg ha hg)
  rwa [geG_E] at h

/-- **`Θ_F(m_F) = O_a(F)` at every fixed range restart below `Λ⁺(gfX a)`** (THEOREM UNI). -/
theorem gfFix {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < xtB1 (gfX ha hg))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (gfX ha hg) l := by
  have hlt : l < iota S (ω ^ gcG (1 + a) * ω) := by rw [geG_E, ← (gfLoc ha hg S).1]; exact hl
  exact gfUniTh (gfT_le ha) (gfX_poly ha hg S) hr.1 hfix (cp_name_L hr.2.2.1)
    (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

theorem gfX_nonfix {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) : XtNonfix (xtOrec (gfX ha hg)) (xtB1
    (gfX ha hg)) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (gfX_pkg ha hg)))

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+2+a}·ω)`, fixed points included.** -/
theorem gfEnum {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG (1 + a) * ω)) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (gfLoc ha hg S).1] at hl
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact xtInit (xtSpec1 (gfX_pkg ha hg)) (gfX_nonfix ha hg) hr hl hnf
  · exact (xtExact_iff (xtSpec1 (gfX_pkg ha hg)) hr.1 hl).2 (gfFix ha hg S hr hl hfx.symm)

/-- **CapV at every range restart below `ι(Γ_{Ω₁+2+a}·ω)`, fixed points included.** -/
theorem gfCapV {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) {l : Ordinal.{0}}
    (hr : CdRange S l) (hl : l < iota S (gcG (1 + a) * ω)) :
    CdCapV S l := by
  have hl' := hl
  rw [← (gfLoc ha hg S).1] at hl'
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · have hww := cp_ww_lt_B0.trans_le hr.2.1
    exact xtCapV_nonfix (xtSpec1 (gfX_pkg ha hg)) hr.1 hww hnf hl' (cp_name_L hr.2.2.1)
      (gfX_nonfix ha hg l hr.1 hww hnf hl')
  · exact Lk.lkCapV_fix (gfX_pkg ha hg) hr hl' hfx.symm (gfEnum ha hg S hr hl)

/-- **Theorem BLK^O below `υ_{Λ⁺(gfX a)}`**, with the exact reaches `lh(ρ_λ) = δ_λ + O_a(λ)`. -/
theorem gfBlk {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) :
    (∀ c d, c < d → d < upsilon (xtB1 (gfX ha hg)) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 (gfX ha hg) ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 (gfX ha hg) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (gfX ha hg) l)) ∧
    (∀ α < upsilon (xtB1 (gfX ha hg)), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 (gfX_pkg ha hg)

/-! ## The tower `c₀ = Ω₁ + 1`, `c_{k+1} = ω^{c_k}` and the supremum `ι(Γ_{Ω₁+1+ε_{Ω₁+1}})` -/

/-- **The tower of codes**: `c₀ = Ω₁ + 1`, `c_{k+1} = ω^{c_k}`; its supremum is `ε_{Ω₁+1}`. -/
noncomputable def gfTw (k : ℕ) : Ordinal.{0} := (fun a : Ordinal.{0} => ω ^ a)^[k] (Om1 + 1)

theorem gfTw_succ (k : ℕ) : gfTw (k + 1) = ω ^ gfTw k := Function.iterate_succ_apply' _ _ _

theorem gfTw_lt (k : ℕ) : gfTw k < gfE := by
  induction k with
  | zero => exact succ_lt_eW Om1_lt_eW
  | succ k ih =>
    rw [gfTw_succ]
    have := (opow_lt_opow_iff_right one_lt_omega0).2 ih
    rwa [show ω ^ gfE = gfE from eW_E] at this

theorem gfTw_ge (k : ℕ) : Om1 + 1 ≤ gfTw k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [gfTw_succ]; exact ih.trans (right_le_opow _ one_lt_omega0)

theorem eps0_opow {u : Ordinal.{0}} (hu : u < ε₀) : ω ^ u < ε₀ := by
  have := (opow_lt_opow_iff_right one_lt_omega0).2 hu
  rwa [omega0_opow_epsilon] at this

theorem gfTw_gtc (k : ℕ) : gtc (gfTw k) < ε₀ := by
  induction k with
  | zero =>
    show gtc (Om1 + 1) < ε₀
    refine (rdc_succ Om1 Om1_lt_eW 0).2.2.trans_lt ?_
    rw [(rdc_Om1 0).2]
    exact_mod_cast natCast_lt_epsilon 2 0
  | succ k ih => rw [gfTw_succ]; exact gtc_opow (fun u hu => eps0_opow hu) (gfTw_lt k) ih

theorem gfTw_strictMono : StrictMono gfTw := strictMono_nat_of_lt_succ fun k => by
  rw [gfTw_succ]
  refine lt_of_le_of_ne (right_le_opow _ one_lt_omega0) fun h => ?_
  have hE : InE (gfTw k) := h.symm
  have hO : Om1 < gfTw k := (lt_add_one Om1).trans_le (gfTw_ge k)
  exact absurd (eN_le hO hE) (not_le.2 (gfTw_lt k))

/-- **The tower is cofinal in `ε_{Ω₁+1}`.** -/
theorem gfTw_cof {c : Ordinal.{0}} (hc : c < gfE) : ∃ k, c < gfTw k := lt_nfp_iff.1 hc

theorem gfTw_one_add (k : ℕ) : 1 + gfTw k = gfTw k :=
  one_add_of_omega0_le (omega_lt_Om1.le.trans (le_self_add.trans (gfTw_ge k)))

/-- The `k`-th member of the family: the code `c_k`. -/
noncomputable def gfXk (k : ℕ) : XtSys := gfX (gfTw_lt k) (gfTw_gtc k)

theorem gfGood_mul (c : Ordinal.{0}) (hc : c < gfE) (hgc : gtc c < ε₀) (S : InaccSeq.{0}) :
    Bt.Good S (gcG c * ω) := by
  refine gf_good fun Z hZ => ?_
  have e : gcG c * ω = ω ^ (gcG c + 1) := by rw [opow_add, opow_one, geG_E]
  rw [e]
  exact GxCl.opow hZ.1 (GxCl.add (GxCl.atom (gfG_atom hc (ge_gx hgc (gg_SC_eps hZ))))
    (GxCl.small (gg_one_lt_of_SC hZ)))

theorem eW_lim : IsSuccLimit gfE := by
  have h1 : (1 : Ordinal.{0}) < gfE := gf_one_lt_Om1.trans Om1_lt_eW
  refine Ordinal.isSuccLimit_iff.2 ⟨(zero_lt_one.trans h1).ne', isSuccPrelimit_of_succ_lt fun b hb => ?_⟩
  rw [succ_eq_add_one]; exact succ_lt_eW hb

/-- **The family of the layers of the tower codes `c_k`.** -/
noncomputable def gfFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (gfXk k)
  off := fun k => xtOrec (gfXk k)
  spec := fun k => xtSpec1 (gfX_pkg _ _)
  mono := fun k => by
    show xtB1 (gfXk k) < xtB1 (gfXk (k + 1))
    unfold gfXk
    rw [(gfLoc _ _ S).1, (gfLoc _ _ S).1, gfTw_one_add, gfTw_one_add]
    refine cd_iota_lt_of_good (gfGood_mul _ (gfTw_lt k) (gfTw_gtc k) S) ?_
    have hE := geG_E (gfTw (k + 1))
    exact (InE.mul_lt hE (gcG_lt (gfTw_strictMono (Nat.lt_succ_self k))) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => gfX_nonfix _ _

theorem gfXk_loc (S : InaccSeq.{0}) (k : ℕ) : xtB1 (gfXk k) = iota S (gcG (gfTw k) * ω) := by
  unfold gfXk; rw [(gfLoc _ _ S).1, gfTw_one_add]

/-- **`sup_k Λ⁺(gfX c_k) = ι(Γ_{Ω₁+1+ε_{Ω₁+1}})`, `υ` of it `= P(Γ_{Ω₁+1+ε_{Ω₁+1}}) < L(0)`.** -/
theorem gfFam_sup (S : InaccSeq.{0}) : (gfFam S).famSup = iota S gfV ∧ upsilon (gfFam S).famSup = Pv S gfV ∧
    Pv S gfV < Nc.ncL S 0 := by
  have hVS := gfV_SC
  have hVE : ω ^ gfV = gfV := Low.opow_eq_self_of_SC hVS
  have hstep : ∀ c, c < gfE → gcG c * ω < gfV := fun c hc =>
    InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE)
  have heq : (gfFam S).famSup = iota S gfV := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (gfXk k) ≤ _
      rw [gfXk_loc S k]
      exact iota_mono _ _ (hstep _ (gfTw_lt k)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit eW_lim e.2
      obtain ⟨n, hn⟩ := gfTw_cof hc
      have h1 : e.1 < gcG (gfTw n) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (gfTw n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (gfXk n) := (gfXk_loc S n).symm
        _ ≤ (gfFam S).famSup := ((gfFam S).famBd_lt n).le
  have hups : upsilon (gfFam S).famSup = Pv S gfV := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gfV_lt_Om2 S).le⟩

theorem gfFam_fix (S : InaccSeq.{0}) : (gfFam S).famTHfix S :=
  fun k _ hr hlk hfix => gfFix _ _ S hr hlk hfix

/-- **ENUM-REACH at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+1}})`, fixed points included.** -/
theorem gfFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gfV) :
    CdUpper S l ∧ CdLower S l := by
  rw [← (gfFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (gfFam S).famLt hl
  have hk' : l < iota S (gcG (1 + gfTw k) * ω) := by
    have := (gfLoc (gfTw_lt k) (gfTw_gtc k) S).1
    rw [← this]; exact hk
  exact gfEnum (gfTw_lt k) (gfTw_gtc k) S hr hk'

/-- **CapV at every range restart below `ι(Γ_{Ω₁+1+ε_{Ω₁+1}})`, fixed points included.** -/
theorem gfFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S gfV) :
    CdCapV S l := by
  rw [← (gfFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (gfFam S).famLt hl
  have hk' : l < iota S (gcG (1 + gfTw k) * ω) := by
    have := (gfLoc (gfTw_lt k) (gfTw_gtc k) S).1
    rw [← this]; exact hk
  exact gfCapV (gfTw_lt k) (gfTw_gtc k) S hr hk'

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+1+ε_{Ω₁+1}})} = P(Γ_{Ω₁+1+ε_{Ω₁+1}})`**, with the exact reaches. -/
theorem gfFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (gfFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (gfFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (gfFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (gfFam S).off k l)) ∧
    (∀ α < upsilon (gfFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (gfFam S).famBlk

/-- **THE ROAD past every code below `ε_{Ω₁+1}`**: UPPER, LOWER and CapV asked only at
`λ ≥ ι(Γ_{Ω₁+1+ε_{Ω₁+1}})` (CapV also
`υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gfFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S gfV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S gfV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S gfV ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hF := (gfFam_sup S).1
  refine (gfFam S).famRoad3 (fun l hr h => hU l hr (hF ▸ h)) (fun l hr h => hL l hr (hF ▸ h)) (gfFam_fix S)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (gfFam S).famSup l with h | h
  · exact hV l hr hlω (hF ▸ h)
  · exact gfFam_capV S hr (hF ▸ h)

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+Ω₁^ω}) < ι(Γ_{Ω₁+2+a}·ω) < ι(Γ_{Ω₁+1+ε_{Ω₁+1}}) < ι(Ω₂)`, and
`P(Γ_{Ω₁+1+ε_{Ω₁+1}}) < P(Ω₂) < L(0)`, for every code `Ω₁^ω ≤ a < ε_{Ω₁+1}` with digits below `ε₀` (past the last
frontier of `R2.GeLoc`). -/
theorem gf_fr_order {a : Ordinal.{0}} (ha : a < gfE) (hg : gtc a < ε₀) (S : InaccSeq.{0}) (hWa : geW ≤ a) :
    iota S geV < iota S (gcG (1 + a) * ω) ∧ iota S (gcG (1 + a) * ω) < iota S gfV ∧
      iota S gfV < iota S (Om (1 + 1)) ∧ Pv S gfV < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hWE : geW < gfE := Om1_pow_lt_eW omega_lt_eW
  have hgW : gtc geW < ε₀ := by
    rw [show geW = Om1 ^ ω from rfl, (rdc_pow omega_lt_eW 0).2, (rdc_const omega_lt_Om1 0).2]
    exact max_lt (omega0_lt_epsilon 0) (by exact_mod_cast natCast_lt_epsilon 1 0)
  have hgV : Bt.Good S geV := gf_good fun Z hZ => GxCl.atom (gfG_atom hWE (ge_gx hgW (gg_SC_eps hZ)))
  have hc := gfT_lt ha
  have hg1 : gtc (1 + a) < ε₀ := (gtc_one_add ha gc_eps0_lim hg).2
  have hVE : ω ^ gfV = gfV := Low.opow_eq_self_of_SC gfV_SC
  have hgfV : Bt.Good S gfV := by
    show gfV ∈ S.CSet (ConjT.Aη S gfV + 1) (S.psi (ConjT.Aη S gfV) (Om 1))
    have := CSet.psi_mem (S := S) (a := ConjT.Aη S gfV + 1) (b := S.psi (ConjT.Aη S gfV) (Om 1))
      (gf_W_lt_A1 (S := S) gfV) (InR_Om_succ 1) (ga_Om2_mem _ _) (gfW_inC (S := S))
    rwa [gfV_psi S] at this
  have hla : geV < gcG (1 + a) * ω :=
    (gcG_le (hWa.trans le_add_self)).trans_lt (lt_mul_of_one_lt_right (gcG_SC _).1 one_lt_omega0)
  have h1 : iota S geV < iota S (gcG (1 + a) * ω) := cd_iota_lt_of_good hgV hla
  have h2 : iota S (gcG (1 + a) * ω) < iota S gfV :=
    cd_iota_lt_of_good (gfGood_mul _ hc hg1 S) (InE.mul_lt hVE (gcG_lt hc) (omega0_lt_inE hVE))
  have h3 : iota S gfV < iota S (Om (1 + 1)) := cd_iota_lt_of_good hgfV (gfV_lt_Om2 S)
  have h4 : Pv S gfV < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h3
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h1, h2, h3, h4, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gf
