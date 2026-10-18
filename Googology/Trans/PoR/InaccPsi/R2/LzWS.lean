import Googology.Trans.PoR.InaccPsi.R2.LzWI
import Googology.Trans.PoR.InaccPsi.R2.LzVS

/-!
# The term systems `lzWs K` (top `y_K(x) = ϑˣ(Ω₁·ω + K)`) and their limit `Λ_{B^ω}⁺ = sup_K Λ⁺(lzWs K)`

`lzWs K`: the terms of `R2.LzW` of level `≤ K` (atoms `y_k`, `k < K`), top `y_K(x)`; IMG `lzwPkg`, RS `lzwRs`,
comparison from EXACT `lzw_pi`, representation `lzw_rep`; the top has the IMG package `lzY_pkg`.  `lzWs (K+1)`
contains the top `y_K` of `lzWs K` as the atom `yk K` (`lzW_topIn`), and `lzWs 2` contains the top `y_1 = B₁ = B∘B`
of `lzVs` (`R2.LzVS`) as `yk 1` (`lzW2_topIn_V`).  Then:

* `lzV_lt_W` (**`Λ⁺(lzVs) < Λ(lzWs 2)`**), `lzW_atB1V` (**`O(Λ⁺(lzVs)) = B₁(ρ) + 1`**), `lzReachV1` (**the exact reach at
  `Λ⁺(lzVs)`: `lh(ρ) = δ + B₁(ρ) + 1`**);
* `lzW_reachLam` (**`lh(ρ) = δ + y_K(ρ)` at `Λ(lzWs K)`**), `lzW_reachB1` (**`lh(ρ) = δ + y_K(ρ) + 1` at
  `Λ⁺(lzWs K)`**), `lzW_reachT` (the reach at the frontier of every term);
* `lzWFam` (the family `Λ⁺(lzWs (k+2))`, `R2.XtFam`), `lzW_sup_ri` (**its supremum `Λ_{B^ω}⁺` is a restart
  index**), `lzW_blk` (**BLK^O below `υ_{Λ_{B^ω}⁺}`**), `lzW_nuC`, `lzW_init` (**UPPER and LOWER at every non-fixed
  restart of the range below `Λ_{B^ω}⁺`**), `lzW_capV`, `lzW_capAt`, `lzW_eqV`, `lzW_of_cp`, `lzWRoad3`, `lzWRoad`,
  `lzWRoad_cap` (the roads of `R2.XtFam` with the rest asked only outside `Λ_{B^ω}⁺`).

No new axiom beyond `R2.CitedLz`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm LzW

theorem lzY_lt_next_ups {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (K : ℕ) :
    lzY (upsilon l) K < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  exact (lzY_lt_next (ups_inE hl) (ups_lt_Om1 l hl1) K (upsilon_normal.strictMono h1)
    (upsPt_upsilon (hl0.trans h1)).2).trans (upsilon_normal.strictMono (lt_add_one _))

/-- **The term system `lzWs K`**: the terms of `LzW` of level `≤ K`, top `y_K(x) = ϑˣ(Ω₁·ω + K)`. -/
noncomputable def lzWs (K : ℕ) : XtSys where
  Tm := LzW
  val := LzW.val
  CB := fun t s => CBt t s ∧ lv t ≤ K
  cs := LzW.cs
  cst := fun c => vz (VzTm.cst c)
  top := fun x => lzY x K
  cb_cst := fun t s h => cbt_cst t s h.1
  cb_iff := fun t s s' h h' => ⟨cbt_iff t s s' h.1 h', h.2⟩
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => ⟨h, Nat.zero_le K⟩
  lt_top := fun l hl hl1 t hCB => lzw_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) t hCB.1 hCB.2
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 (lzY_facts (ups_inE hl) (ups_lt_Om1 l hl1) K).2.2.2.1.pos
  rep := fun l hl hl1 v hv => by
    obtain ⟨t, h1, h2, h3⟩ := lzw_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hv
    exact ⟨t, ⟨h1, h2⟩, h3⟩
  top_lt := fun _ hl hl1 => lzY_lt_next_ups hl hl1 K
  pkg := fun _ _ _ t hCB h1 R => lzwPkg t hCB.1 h1 R
  rs := fun _ _ _ t hCB => lzwRs t hCB.1
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lzw_pi hσ hρ hB t ht.1) (lzw_pi hσ hρ hB u hu.1)
  small := fun t => (lzw_small t).imp id fun h x hx hx1 hc => h x hx hx1 hc.1

theorem lzWs_top (K : ℕ) (x : Ordinal.{0}) : (lzWs K).top x = lzY x K := rfl

/-- **The top `y_K` has an IMG package.** -/
theorem lzWs_topPkg (K : ℕ) : XtTopPkg (lzWs K) := fun _ _ _ R => LzK.lzY_pkg R K

theorem lzY_gap {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (K : ℕ) : lzY x K + 1 < lzY x (K + 1) := by
  have hE := (lzY_facts hx hx1 (K + 1)).2.2.2.1
  exact (inE_indec hE).add_lt (lzY_strict hx hx1 (Nat.lt_succ_self K)) (one_lt_omega0.trans (omega0_lt_inE hE))

/-- **`lzWs (K+1)` contains the top `y_K` of `lzWs K`.** -/
theorem lzW_topIn (K : ℕ) : LyTopIn (lzWs (K + 1)) (lzWs K) :=
  ⟨yk K, fun _ _ _ => ⟨⟨trivial, le_rfl⟩, rfl⟩, fun l hl hl1 => lzY_gap (ups_inE hl) (ups_lt_Om1 l hl1) K⟩

/-- **`lzWs 2` contains the top `B₁ = y_1` of `lzVs`.** -/
theorem lzW2_topIn_V : LyTopIn (lzWs 2) lzVs := by
  refine ⟨yk 1, fun x hx hx1 => ⟨⟨trivial, by simp only [lv]; omega⟩, ?_⟩, fun l hl hl1 => ?_⟩
  · show lzY x 1 = VzB1 x
    exact lzY_one (upsPt_inE hx) hx1
  · have hρE := ups_inE hl
    have hρ1 := ups_lt_Om1 l hl1
    rw [lzVs_top, ← lzY_one hρE hρ1]
    exact lzY_gap hρE hρ1 1

/-! ## The exact reach at `Λ⁺(lzVs)` -/

/-- **`Λ⁺(lzVs) < Λ(lzWs 2)`.** -/
theorem lzV_lt_W : xtB1 lzVs < xtLam (lzWs 2) := lyLamGt lzVs_topPkg lzW2_topIn_V

/-- **`O = O_V` below `Λ⁺(lzVs)`** in `lzWs 2`. -/
theorem lzW2_eqV {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 lzVs) :
    xtOrec (lzWs 2) μ = xtOrec lzVs μ :=
  lyEq lzVs_topPkg lzW2_topIn_V hμ h

/-- **`O(Λ⁺(lzVs)) = B₁(ρ) + 1`** in `lzWs 2`. -/
theorem lzW_atB1V : xtOrec (lzWs 2) (xtB1 lzVs) = VzB1 (upsilon (xtB1 lzVs)) + 1 :=
  lyAtB1 lzVs_topPkg lzW2_topIn_V

/-- **The exact reach at `Λ⁺(lzVs)`**: `lh(ρ) = δ + B₁(ρ) + 1`. -/
theorem lzReachV1 :
    IsReach R2C (upsilon (xtB1 lzVs)) (upsilon (xtB1 lzVs + ω + 1) + (VzB1 (upsilon (xtB1 lzVs)) + 1)) :=
  lyReachB1 (lzWs_topPkg 2) lzVs_topPkg lzW2_topIn_V

/-! ## The reaches of the layers `lzWs K` -/

/-- **The reach at the frontier of `lzWs K`**: `lh(ρ) = δ + y_K(ρ)`. -/
theorem lzW_reachLam (K : ℕ) :
    IsReach R2C (upsilon (xtLam (lzWs K))) (upsilon (xtLam (lzWs K) + ω + 1) + lzY (upsilon (xtLam (lzWs K))) K) := by
  rw [← lzWs_top, ← xtOrec_Lam]
  exact xtReach1 (lzWs_topPkg K) xtLam_ri (lyLamLtB1 (lzWs_topPkg K))

/-- **The reach at `Λ⁺(lzWs K)`**: `lh(ρ) = δ + y_K(ρ) + 1`. -/
theorem lzW_reachB1 (K : ℕ) :
    IsReach R2C (upsilon (xtB1 (lzWs K)))
      (upsilon (xtB1 (lzWs K) + ω + 1) + (lzY (upsilon (xtB1 (lzWs K))) K + 1)) :=
  lyReachB1 (lzWs_topPkg (K + 1)) (lzWs_topPkg K) (lzW_topIn K)

/-- **The reach at the frontier of every term `t` of `lzWs K`**: `lh(ρ) = δ + t(ρ)`. -/
theorem lzW_reachT {K : ℕ} {t : LzW} (hCB : CBt t (upsilon (xtLam (lzWs K)))) (hl : lv t ≤ K)
    (h1 : 1 ≤ val t (upsilon (xtLam (lzWs K)))) :
    IsReach R2C (upsilon (xtLamT (lzWs K) t))
      (upsilon (xtLamT (lzWs K) t + ω + 1) + val t (upsilon (xtLamT (lzWs K) t))) :=
  xtReach_LamT (X := lzWs K) (t := t) ⟨hCB, hl⟩ h1

/-! ## The family and its supremum `Λ_{B^ω}⁺` -/

theorem lzW_B1_lt (K : ℕ) : xtB1 (lzWs K) < xtB1 (lzWs (K + 1)) :=
  lyB1_lt (lzWs_topPkg (K + 1)) (lzWs_topPkg K) (lzW_topIn K)

/-- **The family of the layers `lzWs (k+2)`**: bounds `Λ⁺(lzWs (k+2))`. -/
noncomputable def lzWFam : XtFam where
  bd := fun k => xtB1 (lzWs (k + 2))
  off := fun k => xtOrec (lzWs (k + 2))
  spec := fun k => xtSpec1 (lzWs_topPkg (k + 2))
  mono := fun k => lzW_B1_lt (k + 2)
  nonfix := fun k _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 (lzWs_topPkg (k + 2))))

/-- **`Λ_{B^ω}⁺` is a restart index.** -/
theorem lzW_sup_ri : IsRestartIdx lzWFam.famSup := by
  refine ri_iff.2 ⟨(lt_of_le_of_lt zero_le (lzWFam.famBd_lt 0)).ne', xt_ww_dvd_of_cof fun ν hν => ?_⟩
  obtain ⟨k, hk⟩ := lzWFam.famLt hν
  exact ⟨xtB1 (lzWs (k + 2)), xtB1_mult (lzWs_topPkg (k + 2)), hk, lzWFam.famBd_lt k⟩

/-- **`Λ⁺(lzVs) < Λ_{B^ω}⁺`**, and the order of the frontiers. -/
theorem lzW_order : xtB1 lzVs < xtLam (lzWs 2) ∧ xtLam (lzWs 2) < xtB1 (lzWs 2) ∧ xtB1 (lzWs 2) < lzWFam.famSup :=
  ⟨lzV_lt_W, lyLamLtB1 (lzWs_topPkg 2), lzWFam.famBd_lt 0⟩

/-- **The offsets of the family agree with `O_V` below `Λ⁺(lzVs)`.** -/
theorem lzW_eqV : ∀ k : ℕ, ∀ {μ : Ordinal.{0}}, IsRestartIdx μ → μ < xtB1 lzVs →
    xtOrec (lzWs (k + 2)) μ = xtOrec lzVs μ := by
  intro k
  induction k with
  | zero => exact fun hμ h => lzW2_eqV hμ h
  | succ k ih =>
    intro μ hμ h
    have hk : μ < xtB1 (lzWs (k + 2)) := by
      refine h.trans ((lzV_lt_W.trans (lyLamLtB1 (lzWs_topPkg 2))).trans_le ?_)
      have : ∀ j, xtB1 (lzWs 2) ≤ xtB1 (lzWs (j + 2)) := by
        intro j
        induction j with
        | zero => exact le_rfl
        | succ j ihj => exact ihj.trans (lzW_B1_lt (j + 2)).le
      exact this k
    rw [lyEq (lzWs_topPkg (k + 2)) (lzW_topIn (k + 2)) hμ hk]
    exact ih hμ h

/-- **Theorem BLK^O below `υ_{Λ_{B^ω}⁺}`** in `R₂^C`. -/
theorem lzW_blk :
    (∀ c d, c < d → d < upsilon lzWFam.famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < lzWFam.famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < xtB1 (lzWs (k + 2)) →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lzWs (k + 2)) l)) ∧
    (∀ α < upsilon lzWFam.famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  lzWFam.famBlk

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{B^ω}⁺ ≤ L < ξ`. -/
theorem lzW_nuC : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ lzWFam.famSup ≤ L ∧ L < ξ ∧
    upsilon lzWFam.famSup ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC :=
  lzWFam.famNuC

/-! ## The system of all atoms and the offset at `Λ_{B^ω}⁺` -/

/-- `y_ω(x) = sup_k y_k(x)` (the least fixed point of `B` above `x`). -/
noncomputable def lzYw (x : Ordinal.{0}) : Ordinal.{0} := ⨆ k : ℕ, lzY x k

theorem lzY_le_w (x : Ordinal.{0}) (k : ℕ) : lzY x k ≤ lzYw x := Ordinal.le_iSup _ k

theorem lzYw_lt_iff {x v : Ordinal.{0}} : v < lzYw x ↔ ∃ k : ℕ, v < lzY x k := Ordinal.lt_iSup_iff

theorem lzY_lt_w {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) : lzY x k < lzYw x :=
  (lzY_strict hx hx1 (Nat.lt_succ_self k)).trans_le (lzY_le_w x (k + 1))

theorem lzYw_le_next {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : LtInf1 u) :
    lzYw x ≤ u :=
  Ordinal.iSup_le fun k => (lzY_lt_next hx hx1 k hxu hu).le

/-- **The term system `lzWw` of all terms of `LzW`**, top `y_ω(x)` (no IMG package of the top here). -/
noncomputable def lzWw : XtSys where
  Tm := LzW
  val := LzW.val
  CB := CBt
  cs := LzW.cs
  cst := fun c => vz (VzTm.cst c)
  top := lzYw
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB =>
    (lzw_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) (K := lv t) t hCB le_rfl).trans
      (lzY_lt_w (ups_inE hl) (ups_lt_Om1 l hl1) _)
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 ((lzY_facts (ups_inE hl) (ups_lt_Om1 l hl1) 0).2.2.2.1.pos.trans
    (lzY_lt_w (ups_inE hl) (ups_lt_Om1 l hl1) 0))
  rep := fun l hl hl1 v hv => by
    obtain ⟨K, hK⟩ := lzYw_lt_iff.1 hv
    obtain ⟨t, h1, -, h3⟩ := lzw_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hK
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (lzYw_le_next (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1)).2).trans_lt (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun _ _ _ t hCB h1 R => lzwPkg t hCB h1 R
  rs := fun _ _ _ t hCB => lzwRs t hCB
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (lzw_pi hσ hρ hB t ht) (lzw_pi hσ hρ hB u hu)
  small := lzw_small

/-- The chain of the layers `lzWs (k+2)` inside `lzWw`. -/
noncomputable def lzWChain : LyChain lzWw where
  Y := fun k => lzWs (k + 2)
  pkg := fun k => lzWs_topPkg (k + 2)
  inX := fun k => ⟨yk (k + 2), fun _ _ _ => ⟨trivial, rfl⟩, fun l hl hl1 =>
    (lzY_gap (ups_inE hl) (ups_lt_Om1 l hl1) (k + 2)).trans_le (lzY_le_w _ _)⟩
  next := fun k => lyLamGt (lzWs_topPkg (k + 2)) (lzW_topIn (k + 2))
  topMono := fun k _ hx hx1 => lzY_mono hx hx1 (Nat.le_succ (k + 2))

theorem lzWChain_sup : lzWChain.fam.famSup = lzWFam.famSup := rfl

/-- **`O_ω(Λ_{B^ω}⁺) = y_ω(ρ)`**: the offset of `lzWw` at the supremum of the family is its top. -/
theorem lzW_atSup : xtOrec lzWw lzWFam.famSup = lzYw (upsilon lzWFam.famSup) :=
  lzWChain.lyLimAt lzYw (fun k x hx hx1 => lzY_lt_w hx hx1 (k + 2))
    (fun x hx hx1 v hv => by
      obtain ⟨k, hk⟩ := lzYw_lt_iff.1 hv
      exact ⟨k, hk.trans_le (lzY_mono hx hx1 (by omega))⟩)

/-- **`Λ(lzWw) = Λ_{B^ω}⁺`.** -/
theorem lzWw_lam : xtLam lzWw = lzWFam.famSup :=
  le_antisymm (xtLam_le lzW_sup_ri lzW_atSup) lzWChain.sup_le

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ_{B^ω}⁺` that is not a fixed point of `υ`.** -/
theorem lzW_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lzWFam.famSup) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  lzWFam.famInit hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ_{B^ω}⁺`.** -/
theorem lzW_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < lzWFam.famSup) (hfix : l < upsilon l) :
    CdCapV S l :=
  lzWFam.famCapV hr hl hfix

theorem lzW_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < lzWFam.famSup)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l :=
  lzWFam.famCapAt hl hB hlΛ hfix hname

/-- **The hypotheses of `lzWRoad3` from those of `cpRoad3`.** -/
theorem lzW_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → lzWFam.famSup ≤ l → CdUpper S l) ∧
      (∀ l, CdRange S l → lzWFam.famSup ≤ l → CdLower S l) ∧ lzWFam.famTHfix S := by
  obtain ⟨hU', hL', hT'⟩ := lzV_of_cp hU hL hT
  have hcp : Cp.cpB1 ≤ xtB1 lzVs :=
    (((lyB_cp_le.trans lyE_order.2.le).trans lzE_lt_B1.le).trans lzZ_lt_V.le).trans lzV_lam_lt.le
  have hVW : xtB1 lzVs ≤ lzWFam.famSup := (lzW_order.1.trans (lzW_order.2.1.trans lzW_order.2.2)).le
  refine ⟨fun l hr h => hU l hr ((hcp.trans hVW).trans h), fun l hr h => hL l hr ((hcp.trans hVW).trans h),
    fun k l hr hlk hfix => ?_⟩
  rcases lt_or_ge l (xtB1 lzVs) with h | h
  · show cdTheta S l (cdCode S l) = xtOrec (lzWs (k + 2)) l
    rw [lzW_eqV k hr.1 h]; exact hT' l hr h hfix
  · exact (lzWFam.famIff k hr.1 hlk).2.2.1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ_{B^ω}⁺`**, `Θ_F(m_F) = O_k(F)` at the fixed points below
`Λ⁺(lzWs (k+2))`, the cap of the values outside `Λ_{B^ω}⁺`, (CL), EQ, TCrest, (EMB₂). -/
theorem lzWRoad3 (hU : ∀ l, CdRange S l → lzWFam.famSup ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → lzWFam.famSup ≤ l → CdLower S l) (hT : lzWFam.famTHfix S)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lzWFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lzWFam.famRoad3 hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ_{B^ω}⁺`.** -/
theorem lzWRoad (hU : ∀ l, CdRange S l → XtOut lzWFam.famSup l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut lzWFam.famSup l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut lzWFam.famSup l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lzWFam.famRoad hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ_{B^ω}⁺`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem lzWRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut lzWFam.famSup l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut lzWFam.famSup l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  lzWFam.famRoad_cap h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lz
