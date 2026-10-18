import Googology.Trans.PoR.InaccPsi.R2.LtWS

/-!
# The system `ltSw` of all terms of `LtW`, its top `ϑˣ(Ω₁·ω + y_ω(x))`, and BLK^O up to `Λ⁺(ltSw)`

`ltTw x := sup_K T_K(x)`, `T_K(x) = ϑˣ(Ω₁·ω + y_K(x))`; `ltSw`: all terms of `LtW`, top `ltTw`.

* `ltTw_eq` (**`sup_K T_K(x) = ϑˣ(Ω₁·ω + y_ω(x))`**: `<` termwise by [W07a] Lemma 3.30, `≥` by minimality `lt_w_min`),
  `ltTw_lh` (**`lh(ϑˣ(Ω₁·ω + y_ω(x))) = ϑˣ(Ω₁·ω + y_ω(x))·ω + y_ω(x)`**: `ltLhT_w_lim` at `η = y_ω(x)`,
  `logend(y_ω(x)) = y_ω(x)`);
* `LtK.ltWitTw`, `LtK.ltTw_pkg` (**the IMG package of `ltTw`**: a covering copy `f` gives `f(v) ≤₁ f(v)·ω + f(y_ω)`
  for `v = ϑᵖ(Ω₁·ω + y_ω(ρ))`, so `φ_ω(i₀ + ω^{f(y_ω)}) ≤ f(v)` with `φ_ω(i₀) = B(f(ρ))`; every `ϑ^{f(ρ)}(Ω₁·ω + σ)`
  with `σ < y_ω(f(ρ)) ≤ f(y_ω)` is `≤ φ_ω(i₀ + σ + 1) < f(v)` (`lt_w_ub` at `s' = 0`), and `lt_w_min`);
  `ltSw_topPkg`;
* `ltChain` (the layers `ltS k` inside `ltSw`), `lt_atSup` (**`O(Λ_T⁺) = ltTw(ρ)`**), `ltSw_lam` (`Λ(ltSw) = Λ_T⁺`),
  `ltT_lt_B1` (**`Λ_T⁺ < Λ⁺(ltSw)`**), `ltReachT` (**the exact reach at `Λ_T⁺`: `lh(ρ) = δ + ϑᵖ(Ω₁·ω + y_ω(ρ))`**),
  `ltSw_reach`, `ltSw_blk` (**BLK^O below `υ_{Λ⁺(ltSw)}`**), `ltSw_eqS`, `ltSw_init`, `ltSw_capV`, `ltSw_capAt`,
  `ltSw_iff`, `ltSw_iso`, `ltSw_fix_code`, `ltSw_of_cp`, `ltSwRoad3`, `ltSwRoad`, `ltSwRoad_cap`.

New axiom: only `ltLhT_w_lim` of `R2.CitedLt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lz LtW

/-- `ltTw(x) = sup_K T_K(x)`. -/
noncomputable def ltTw (x : Ordinal.{0}) : Ordinal.{0} := ⨆ K : ℕ, ltT x K

theorem ltT_le_w (x : Ordinal.{0}) (K : ℕ) : ltT x K ≤ ltTw x := Ordinal.le_iSup _ K

theorem ltTw_lt_iff {x v : Ordinal.{0}} : v < ltTw x ↔ ∃ K : ℕ, v < ltT x K := Ordinal.lt_iSup_iff

/-- `logend(e) = e` for an `ε`-number `e`. -/
theorem lt_lg_E {e : Ordinal.{0}} (he : InE e) : lg e = e :=
  le_antisymm (lg_le he.pos.ne') (le_csSup (lg_bdd he.pos.ne') (show ω ^ e ∣ e by rw [show ω ^ e = e from he]))

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem ltT_lt_w (K : ℕ) : ltT x K < ltTw x :=
  (ltT_strict hx hx1 (Nat.lt_succ_self K)).trans_le (ltT_le_w x (K + 1))

theorem ltTw_le_next {u : Ordinal.{0}} (hxu : x < u) (hu : LtInf1 u) : ltTw x ≤ u :=
  Ordinal.iSup_le fun K => (ltT_lt_next hx hx1 K hxu hu).le

theorem ltYw_T : lzYw x ∈ Tset x ∧ lzYw x < Om1 := by
  obtain ⟨hT, -, h1, -, -⟩ := ltT_facts hx hx1 0
  have h := ltYw_lt_T hx hx1 0
  exact ⟨vz_T_down hx hx1 hT h1 h.le, h.trans h1⟩

theorem ltYw_E : InE (lzYw x) := vz_omega_E (ltYw_omega hx hx1)

/-- `y_ω(x) < ϑˣ(Ω₁·ω + y_ω(x))`. -/
theorem ltYw_lt_self : lzYw x < vt x (Om1 * ω + lzYw x) := by
  obtain ⟨hyT, hy1⟩ := ltYw_T hx hx1
  have hω := lt_omega_T hx hx1
  have hE := (lt_w_facts hx hx1 hyT hy1).2.2.2.1
  have h := lzVt_lt_ww hx hx1 hω.1 hyT hy1 (omega0_lt_inE (ltYw_E hx hx1)) (omega0_lt_inE hE)
  rwa [← ltYw_eq hx hx1] at h

/-- **`sup_K T_K(x) = ϑˣ(Ω₁·ω + y_ω(x))`.** -/
theorem ltTw_eq : ltTw x = vt x (Om1 * ω + lzYw x) := by
  obtain ⟨hyT, hy1⟩ := ltYw_T hx hx1
  have hself := ltYw_lt_self hx hx1
  refine le_antisymm (Ordinal.iSup_le fun K => ?_) ?_
  · exact (lzVt_lt_ww hx hx1 (lzY_T hx hx1 K).1 hyT hy1 (lzY_lt_w hx hx1 K)
      ((lzY_lt_w hx hx1 K).trans hself)).le
  · have hP : ltTw x ∈ Set.range (veblen ω) :=
      lt_sup_range omega0_ne_zero (ltT x) (fun K => lt_w_omega hx hx1 (lzY_T hx hx1 K).1 (lzY_T hx hx1 K).2)
        (fun K => ltT_strict hx hx1 (Nat.lt_succ_self K))
    have h0 := ltT_le_w x 0
    refine lt_w_min hx hx1 hyT hy1 hP ((ltT_facts hx hx1 0).2.1.trans_le h0)
      ((ltYw_lt_T hx hx1 0).trans_le h0) (fun σ hσ => ?_)
    obtain ⟨K, hK⟩ := lzYw_lt_iff.1 hσ
    have hσT := vz_T_down hx hx1 hyT hy1 hσ.le
    exact (lt_w_mono hx hx1 hσT (lzY_T hx hx1 K).1 (lzY_T hx hx1 K).2 (lzY_lt_w hx hx1 K) hK).trans
      (ltT_lt_w hx hx1 K)

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·ω + y_ω(x))`**: `lh = ϑˣ(Ω₁·ω + y_ω(x))·ω + y_ω(x)`. -/
theorem ltTw_lh : IsLh1 (vt x (Om1 * ω + lzYw x)) (vt x (Om1 * ω + lzYw x) * ω + lzYw x) := by
  obtain ⟨hyT, hy1⟩ := ltYw_T hx hx1
  obtain ⟨hvT, hxv, hv1, -, hvP⟩ := lt_w_facts hx hx1 hyT hy1
  have hyE := ltYw_E hx hx1
  have hω := lt_omega_T hx hx1
  have hω1T : (ω : Ordinal.{0}) + 1 ∈ Tset x := vzT_add hx hx1 hω.1 (by exact_mod_cast (lz_natT hx hx1 1).1)
  have hω1y : (ω : Ordinal.{0}) + 1 < lzYw x :=
    (inE_indec hyE).add_lt (omega0_lt_inE hyE) (one_lt_omega0.trans (omega0_lt_inE hyE))
  have hlim : ∃ σ, σ < lzYw x ∧ lzYw x < vt x (Om1 * ω + σ) := by
    refine ⟨ω + 1, hω1y, ?_⟩
    have hE1 := (lt_w_facts hx hx1 hω1T (hω1y.trans hy1)).2.2.2.1
    have h := lzVt_lt_ww hx hx1 hω.1 hω1T (hω1y.trans hy1) (lt_add_one _) (omega0_lt_inE hE1)
    rwa [← ltYw_eq hx hx1] at h
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  rwa [ltLhT_w_lim hx hx1 hyT hy1 hyE.pos.ne' (ltYw_lt_self hx hx1) hlim, lt_lg_E hyE] at h

end Base

/-! ## The IMG package of the top `ϑ(Ω₁·ω + y_ω)` -/

namespace LtK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem ltTw_lt_δ : ltTw ρ < δ := (ltTw_le_next h.ρE h.ρ1 h.ρτ h.τU.2).trans_lt h.τδ

/-- **The witness sets of `ltTw(ρ)`**: every covering copy `f` has `ltTw(f(ρ)) ≤ f(ltTw(ρ))`. -/
theorem ltWitTw : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ltTw ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      ltTw (f ρ) ≤ f (ltTw ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨W1, Z1, w1, hYW, hI1⟩ := ltWitYw h
  obtain ⟨hw0, hBW, hI0⟩ := xtWitB h
  generalize hW0d : ({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) = W0 at hw0 hBW hI0
  have e := ltTw_eq hρE hρ1
  obtain ⟨hyT, hy1⟩ := ltYw_T hρE hρ1
  obtain ⟨-, -, -, hvE, hvI⟩ := lt_w_facts hρE hρ1 hyT hy1
  rw [← e] at hvE hvI
  have hYv : lzYw ρ < ltTw ρ := by rw [e]; exact ltYw_lt_self hρE hρ1
  have hBY : VzB ρ < lzYw ρ := by rw [← lzY_zero hρE hρ1]; exact lzY_lt_w hρE hρ1 0
  have hρY : ρ < lzYw ρ := (vzB_omega hρE hρ1).2.1.trans hBY
  have hρv : ρ < ltTw ρ := hρY.trans hYv
  have hvδ : ltTw ρ < δ := ltTw_lt_δ h
  have hvwδ : ltTw ρ * ω < δ := vz_mul_omega_lt h.δE hvδ
  have hδI := inE_indec h.δE
  have hvwyδ : ltTw ρ * ω + lzYw ρ < δ := hδI.add_lt hvwδ (hYv.trans hvδ)
  have hvw := lt_le_mul_w (ltTw ρ)
  have hYpos : 0 < lzYw ρ := lt_of_le_of_lt zero_le hρY
  have hvwlt : ltTw ρ * ω < ltTw ρ * ω + lzYw ρ := lt_add_of_pos_right _ hYpos
  have hYlt : lzYw ρ < ltTw ρ * ω + lzYw ρ := lt_of_lt_of_le hYv (hvw.trans le_self_add)
  have hsrc : le1 (ltTw ρ) (ltTw ρ * ω + lzYw ρ) :=
    (h.lowδ _ _ hρv hvwyδ.le).2 (by rw [e]; exact (ltTw_lh hρE hρ1).1)
  have hwI : Indec (ltTw ρ * ω) := by
    have e2 : ltTw ρ * ω = ω ^ (ltTw ρ + 1) := by rw [opow_add, opow_one, show ω ^ ltTw ρ = ltTw ρ from hvE]
    rw [e2]; exact indec_opow _
  have w2 := (w1.union hw0).insW hρv.le hvδ (Or.inl hvI)
  have w3 := w2.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
  have w4 := w3.insW (hρv.le.trans (hvw.trans le_self_add)) hvwyδ
    (Or.inr ⟨ltTw ρ * ω, by simp, lzYw ρ, by simp [hYW], hvwlt, hYlt, rfl⟩)
  refine ⟨_, _, w4, by simp, fun A f hW hZ C => ?_⟩
  have hvA : ltTw ρ ∈ A := hW (by simp)
  have hvwA : ltTw ρ * ω ∈ A := hW (by simp)
  have hvwyA : ltTw ρ * ω + lzYw ρ ∈ A := hW (by simp)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hW0 : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  have hZ0 : ↑(∅ : Finset Ordinal.{0}) ⊆ A := by simp
  have hyA : lzYw ρ ∈ A := hW1 (Finset.mem_coe.2 hYW)
  have hBA : VzB ρ ∈ A := hW0 (Finset.mem_coe.2 hBW)
  have hYf := hI1 A f hW1 hZ1 C
  obtain ⟨-, hBf⟩ := hI0 A f hW0 hZ0 C
  have hyE := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hyv : f ρ < f (ltTw ρ) := C.mono C.rho hvA hρv
  by_cases hU : UpsPt (f (ltTw ρ))
  · exact ltTw_le_next hyE hy1 hyv hU.2
  have himg : le1 (f (ltTw ρ)) (f (ltTw ρ * ω) + f (lzYw ρ)) := by
    have := C.cov1 _ hvA _ hvwyA hsrc
    rwa [← C.add _ hvwA _ hyA _ hvwyA rfl] at this
  have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
  have haddv : f (ltTw ρ) + f (ltTw ρ * ω) = f (ltTw ρ * ω) :=
    C.add _ hvA _ hvwA _ hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : f (ltTw ρ) * ω ≤ f (ltTw ρ * ω) := add_eq_right_iff_mul_omega0_le.1 haddv
  have hR2 : le1R (f (ltTw ρ)) (f (ltTw ρ) * ω + f (lzYw ρ)) :=
    le1R_of_le ((lt_le_mul_w _).trans le_self_add) (add_le_add hge le_rfl) hR
  obtain ⟨i0, hi0⟩ := (vzB_omega hyE hy1).1
  have hBfv : VzB (f ρ) < f (ltTw ρ) := hBf.trans_lt (C.mono hBA hvA (hBY.trans hYv))
  have hfyv : f (lzYw ρ) < f (ltTw ρ) := C.mono hyA hvA hYv
  have hge2 := lt_le1R_ge_w (f (lzYw ρ)) (f (ltTw ρ)) i0 hfyv (by rw [hi0]; exact hBfv) hR2
  have hP := vz_le1R_omega (lt_of_le_of_lt zero_le hyv) (lt_le1R_w_base hR2)
  obtain ⟨hyyT, hyy1⟩ := ltYw_T hyE hy1
  rw [ltTw_eq hyE hy1]
  refine lt_w_min hyE hy1 hyyT hyy1 hP hyv (hYf.trans_lt hfyv) (fun σ hσ => ?_)
  have h0T : (0 : Ordinal.{0}) ∈ Tset (f ρ) := mem_T_of_le hyE hy1 (zero_le : (0 : Ordinal.{0}) ≤ f ρ)
  have hσT : σ ∈ Tset (f ρ) := vz_T_down hyE hy1 hyyT hyy1 hσ.le
  have hb0 : vt (f ρ) (Om1 * ω + 0) ≤ veblen ω i0 := by rw [add_zero, vz_vt_w_eq hyE hy1, hi0]
  have hpos0 : (0 : Ordinal.{0}) < veblen ω i0 := by rw [hi0]; exact (vzB_omega hyE hy1).2.1.trans' hyE.pos
  have hub := lt_w_ub hyE hy1 h0T (Ordinal.omega_pos 1) (lt_of_le_of_lt zero_le hσ) hb0 hpos0 σ
    (by rw [zero_add]; exact hσT) (by rw [zero_add]; exact hσ.trans hyy1)
  rw [zero_add] at hub
  refine lt_of_le_of_lt hub (lt_of_lt_of_le ((veblen_lt_veblen_iff_right).2 ?_) hge2)
  rw [add_assoc]
  refine (add_lt_add_iff_left i0).2 ?_
  have hfy1 : (1 : Ordinal.{0}) ≤ f (lzYw ρ) := one_le_iff_pos.2 (hyE.pos.trans (C.mono C.rho hyA hρY))
  have hd' : σ < ω ^ f (lzYw ρ) := (hσ.trans_le hYf).trans_le (right_le_opow _ one_lt_omega0)
  have h1 : (1 : Ordinal.{0}) < ω ^ f (lzYw ρ) :=
    one_lt_omega0.trans_le (by
      have := (opow_le_opow_iff_right one_lt_omega0).2 hfy1
      rwa [opow_one] at this)
  exact isPrincipal_add_omega0_opow _ hd' h1

/-- **The IMG package of `ltTw`.** -/
theorem ltTw_pkg : ImgPkg ρ δ ltTw := by
  obtain ⟨W, Z, hw, hvW, hI⟩ := ltWitTw h
  have hpos : 0 < ltTw ρ := (ltT_facts h.ρE h.ρ1 0).2.2.2.1.pos.trans_le (ltT_le_w ρ 0)
  exact ⟨one_le_iff_pos.2 hpos, ltTw_lt_δ h, W, Z, hw, Finset.mem_union_left _ hvW, hI⟩

end LtK

/-! ## The system of all terms -/

/-- **The term system `ltSw` of all terms of `LtW`**, top `ltTw(x) = ϑˣ(Ω₁·ω + y_ω(x))`. -/
noncomputable def ltSw : XtSys where
  Tm := LtW
  val := LtW.val
  CB := CBt
  cs := LtW.cs
  cst := fun c => lz (LzW.vz (VzTm.cst c))
  top := ltTw
  cb_cst := cbt_cst
  cb_iff := cbt_iff
  val_cst := fun _ _ => rfl
  cb_cstI := fun _ _ h => h
  lt_top := fun l hl hl1 t hCB =>
    (ltw_lt_top (ups_inE hl) (ups_lt_Om1 l hl1) (K := lw t) t hCB le_rfl).trans
      (ltT_lt_w (ups_inE hl) (ups_lt_Om1 l hl1) _)
  one_le_top := fun l hl hl1 => one_le_iff_pos.2 ((ltT_facts (ups_inE hl) (ups_lt_Om1 l hl1) 0).2.2.2.1.pos.trans
    (ltT_lt_w (ups_inE hl) (ups_lt_Om1 l hl1) 0))
  rep := fun l hl hl1 v hv => by
    obtain ⟨K, hK⟩ := ltTw_lt_iff.1 hv
    obtain ⟨t, h1, -, h3⟩ := ltw_rep (ups_inE hl) (ups_lt_Om1 l hl1) v hK
    exact ⟨t, h1, h3⟩
  top_lt := fun l hl hl1 => by
    have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
    exact (ltTw_le_next (ups_inE hl) (ups_lt_Om1 l hl1) (upsilon_normal.strictMono h1)
      (upsPt_upsilon (hl0.trans h1)).2).trans_lt (upsilon_normal.strictMono (lt_add_one _))
  pkg := fun _ _ _ t hCB h1 R => ltwPkg t hCB h1 R
  rs := fun _ _ _ t hCB => ltwRs t hCB
  uni_le := fun _ _ hσ hρ hB t u ht hu =>
    xt_uni_of_exact hB (ltw_pi hσ hρ hB t ht) (ltw_pi hσ hρ hB u hu)
  small := ltw_small

theorem ltSw_top (x : Ordinal.{0}) : ltSw.top x = ltTw x := rfl

/-- **The top `ϑ(Ω₁·ω + y_ω)` of `ltSw` has an IMG package.** -/
theorem ltSw_topPkg : XtTopPkg ltSw := fun _ _ _ R => LtK.ltTw_pkg R

/-- The chain of the layers `ltS k` inside `ltSw`. -/
noncomputable def ltChain : LyChain ltSw where
  Y := ltS
  pkg := ltS_topPkg
  inX := fun k => ⟨tw (LzW.yk k), fun _ _ _ => ⟨trivial, rfl⟩, fun l hl hl1 =>
    (ltT_gap (ups_inE hl) (ups_lt_Om1 l hl1) k).trans_le (ltT_le_w _ _)⟩
  next := fun k => lyLamGt (ltS_topPkg k) (lt_topIn k)
  topMono := fun k _ hx hx1 => ltT_mono hx hx1 (Nat.le_succ k)

theorem ltChain_sup : ltChain.fam.famSup = ltFam.famSup := rfl

/-- **`O(Λ_T⁺) = ltTw(ρ)`**: the offset of `ltSw` at the supremum of the family is its top. -/
theorem lt_atSup : xtOrec ltSw ltFam.famSup = ltTw (upsilon ltFam.famSup) :=
  ltChain.lyLimAt ltTw (fun k _ hx hx1 => ltT_lt_w hx hx1 k)
    (fun _ _ _ _ hv => ltTw_lt_iff.1 hv)

/-- **`Λ(ltSw) = Λ_T⁺`.** -/
theorem ltSw_lam : xtLam ltSw = ltFam.famSup :=
  le_antisymm (xtLam_le lt_sup_ri lt_atSup) ltChain.sup_le

theorem ltSw_lamLtB1 : xtLam ltSw < xtB1 ltSw := lyLamLtB1 ltSw_topPkg

/-- **`Λ_T⁺ < Λ⁺(ltSw)`.** -/
theorem ltT_lt_B1 : ltFam.famSup < xtB1 ltSw := by
  rw [← ltSw_lam]; exact ltSw_lamLtB1

/-- **The exact reach at `Λ_T⁺`**: `lh(ρ) = δ + ltTw(ρ)`. -/
theorem ltReachT :
    IsReach R2C (upsilon ltFam.famSup) (upsilon (ltFam.famSup + ω + 1) + ltTw (upsilon ltFam.famSup)) := by
  rw [← lt_atSup]
  exact xtReach1 ltSw_topPkg lt_sup_ri ltT_lt_B1

/-- **The exact reach at `Λ_T⁺`** with `ltTw(ρ) = ϑᵖ(Ω₁·ω + y_ω(ρ))`. -/
theorem ltReachT_vt :
    IsReach R2C (upsilon ltFam.famSup)
      (upsilon (ltFam.famSup + ω + 1) + vt (upsilon ltFam.famSup) (Om1 * ω + lzYw (upsilon ltFam.famSup))) := by
  rw [← ltTw_eq (ups_inE lt_sup_ri) (ups_lt_Om1 _ ltFam.famSup_lt_Om1)]
  exact ltReachT

theorem ltSw_nonfix : XtNonfix (xtOrec ltSw) (xtB1 ltSw) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 ltSw_topPkg))

/-- **The exact reach of every restart below `Λ⁺(ltSw)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem ltSw_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 ltSw) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec ltSw l) :=
  xtReach1 ltSw_topPkg hl hlB

/-- **Theorem BLK^O below `υ_{Λ⁺(ltSw)}`** in `R₂^C`. -/
theorem ltSw_blk :
    (∀ c d, c < d → d < upsilon (xtB1 ltSw) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 ltSw ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 ltSw →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec ltSw l)) ∧
    (∀ α < upsilon (xtB1 ltSw), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 ltSw_topPkg

/-- **`O = O_k` below `Λ⁺(ltS k)`.** -/
theorem ltSw_eqS (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (ltS k)) :
    xtOrec ltSw μ = xtOrec (ltS k) μ :=
  lyEq (ltS_topPkg k) (ltChain.inX k) hμ h

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ⁺(ltSw)` that is not a fixed point of `υ`.** -/
theorem ltSw_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 ltSw) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 ltSw_topPkg) ltSw_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(ltSw)`.** -/
theorem ltSw_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 ltSw) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 ltSw_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (ltSw_nonfix l hr.1 hww hfix hl)

theorem ltSw_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 ltSw)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 ltSw_topPkg) hl hww hfix hlΛ hname (ltSw_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(ltSw)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem ltSw_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 ltSw) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec ltSw l) :=
  xtExact_iff (xtSpec1 ltSw_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(ltSw)`**: `O(F) = F`. -/
theorem ltSw_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 ltSw)
    (hiso : CpIso F) : xtOrec ltSw F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 ltSw_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(ltSw)` reduces to the code.** -/
theorem ltSw_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 ltSw)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 ltSw_topPkg) hr.1 hfix hFB (ltSw_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `ltSwRoad3` from those of `cpRoad3`.** -/
theorem ltSw_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtB1 ltSw ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 ltSw ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 ltSw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec ltSw l) := by
  obtain ⟨hU', hL', hT'⟩ := lt_of_cp hU hL hT
  have hle : ltFam.famSup ≤ xtB1 ltSw := ltT_lt_B1.le
  refine ⟨fun l hr h => hU' l hr (hle.trans h), fun l hr h => hL' l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l ltFam.famSup with h | h
  · obtain ⟨k, hk⟩ := ltFam.famLt h
    rw [ltSw_eqS k hr.1 hk]; exact hT' k l hr hk hfix
  · exact (ltSw_iff hr.1 hlB).1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(ltSw)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(ltSw)`, the cap of the values outside `Λ⁺(ltSw)`, (CL), EQ, TCrest, (EMB₂). -/
theorem ltSwRoad3 (hU : ∀ l, CdRange S l → xtB1 ltSw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 ltSw ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 ltSw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec ltSw l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 ltSw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 ltSw_topPkg) ltSw_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(ltSw)`.** -/
theorem ltSwRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 ltSw) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 ltSw) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 ltSw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 ltSw_topPkg) ltSw_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(ltSw)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem ltSwRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 ltSw) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 ltSw) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 ltSw_topPkg) ltSw_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lt
