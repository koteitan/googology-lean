import Googology.Trans.PoR.InaccPsi.R2.LyBig

/-!
# The terms over `B`: `φ(n, ·)`-terms, the atom `B(x)`, sums and `ω`-powers, with values below `ε_{B(x)+1}`

`LyTm`: a term `vz t` of `R2.VzT` (`φ(n, ·)`, `n < ω`, in `x`), the atom `bB` (value `B(x)`, the least `φ(ω, ·)`-value
above `x`), a sum `sm a b`, a power `pw a` (`ω^a`).  For every base `x` (an `ε`-number below `Ω₁`):

* `lyt_lt_eN` (**every value is below `ε_{B(x)+1}`**), `ly_eN_lt` (`ε_{b+1}` lies below every `<₁ ∞`-point above an
  `ε`-number `b < Ω₁`, and below `Ω₁`: [W07b] Corollary 5.10 through `T_next`, as `eN_lt_upsPt`);
* `lyt_pi` (**Lemma EXACT**: `π_{σ,ρ}(t(ρ)) = t(σ)`, from `vzv_pi`, `xtPiB`, `pi_add`, `pi_opowZ`), `lyt_uni_le`,
  `lyt_uni_lt`, `lyt_uni_eq` (comparison at two bases);
* `lyt_rep` (**representation**: every ordinal below `ε_{B(ρ)+1}` is a value with constants below `ρ`);
* `lyt_zero` (a value `0` is the value `0` everywhere);
* `lyStep2` (the atom step of `R2.LyStep` with the previous power in `W ∪ Z`), `lyt_img` (**Lemma IMG below
  `ε_{B(ρ)+1}`**: every value has a term and witness sets with `t(f(ρ)) ≤ f(v)` for every covering copy `f`; below
  `B(ρ)` from `imgVz`, at `B(ρ)` from `xtWitB`, sums by the closure of the witness sets, a power `ω^{z' + ω^q}` by one
  atom step `ω^z ≤₁ ω^z + q` of `R₁⁺` ([W07b] Theorem 2.2) or, for `q = 0`, because the copy of a power is a power).

No new axiom beyond `R2.CitedXt`.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **The terms over `B`**: `φ(n, ·)`-terms, the atom `B(x)`, sums and `ω`-powers. -/
inductive LyTm : Type 1
  | vz : VzTm → LyTm
  | bB : LyTm
  | sm : LyTm → LyTm → LyTm
  | pw : LyTm → LyTm

namespace LyTm

/-- The value at the base `x`. -/
noncomputable def val : LyTm → Ordinal.{0} → Ordinal.{0}
  | vz t, x => t.val x
  | bB, x => VzB x
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`. -/
def CBt : LyTm → Ordinal.{0} → Prop
  | vz t, s => t.CBt s
  | bB, _ => True
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LyTm → List Ordinal.{0}
  | vz t => t.cst'
  | bB => []
  | sm a b => cs a ++ cs b
  | pw a => cs a

@[simp] theorem val_vz (t : VzTm) (x : Ordinal.{0}) : val (vz t) x = t.val x := rfl
@[simp] theorem val_bB (x : Ordinal.{0}) : val bB x = VzB x := rfl
@[simp] theorem val_sm (a b : LyTm) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LyTm) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LyTm) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | vz t, s, s', h, h' => VzTm.cbt_iff t s s' h h'
  | bB, _, _, _, _ => trivial
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LyTm) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | vz t, s, h, c, hc => VzTm.cbt_cst t s h c hc
  | bB, _, _, c, hc => by simp [cs] at hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

end LyTm

open LyTm

/-- `ε_{b+1}` lies below `Ω₁` and below every `<₁ ∞`-point above an `ε`-number `b < Ω₁`. -/
theorem ly_eN_lt {b : Ordinal.{0}} (hbE : InE b) (hb1 : b < Om1) :
    eN b < Om1 ∧ ∀ u, b < u → LtInf1 u → eN b < u := by
  obtain ⟨m, -, -, hmin, hT, hm1⟩ := T_next (Or.inr hbE) hb1
  obtain ⟨hDT, hD1, -⟩ := Dl_spec hbE hb1 1
  obtain ⟨hbD, hDE, -⟩ := Dl_E hbE hb1 (le_refl 1)
  have hDm : Dl b 1 < m := (hT _ hD1).1 hDT
  have hem : eN b < m := lt_of_le_of_lt (eN_le hbD hDE) hDm
  exact ⟨hem.trans hm1, fun u hbu hu => lt_of_lt_of_le hem (hmin u hbu hu)⟩

theorem ly_eNB_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN (VzB x) < Om1 :=
  (ly_eN_lt (xt_B_E hx hx1) (xt_B_lt_Om1 hx hx1)).1

theorem ly_eNB_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    eN (VzB x) < u :=
  (ly_eN_lt (xt_B_E hx hx1) (xt_B_lt_Om1 hx hx1)).2 u (xt_B_lt_ups hx hx1 hxu hu) hu.2

/-- **Every value is below `ε_{B(x)+1}`.** -/
theorem lyt_lt_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LyTm, CBt t x → val t x < eN (VzB x)
  | vz _, h => (vzv_lt_B hx hx1 h).trans (lt_eN _)
  | bB, _ => lt_eN _
  | sm a b, h => (inE_indec (eN_E _)).add_lt (lyt_lt_eN hx hx1 a h.1) (lyt_lt_eN hx hx1 b h.2)
  | pw a, h => (eN_E _).opow_lt (lyt_lt_eN hx hx1 a h)

theorem lyt_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (t : LyTm) (h : CBt t x) : val t x < Om1 :=
  (lyt_lt_eN hx hx1 t h).trans (ly_eNB_lt_Om1 hx hx1)

theorem cbt_mono {t : LyTm} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

/-- **Lemma EXACT for `LyTm`.** -/
theorem lyt_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LyTm, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | vz t, h => vzv_pi hσ hρ hB t h
  | bB, _ => xtPiB hB
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lyt_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lyt_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := lyt_pi hσ hρ hB a h
    have hb := lyt_lt_Om1 hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem lyt_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LyTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lyt_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lyt_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem lyt_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LyTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, lyt_uni_le hσ hρ hB hu ht]

theorem lyt_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LyTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, lyt_uni_le hσ hρ hB ht hu, lyt_uni_le hσ hρ hB hu ht]

/-- **A value `0` is the value `0` everywhere.** -/
theorem lyt_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LyTm, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | vz t, h, h0 => lb_zero_const hx hx1 h h0
  | bB, _, h0 => absurd h0 (xt_B_E hx hx1).pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, lyt_zero hx hx1 a h.1 this.1 y, lyt_zero hx hx1 b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

/-- An `ε`-number strictly between `B(x)` and `ε_{B(x)+1}` does not exist. -/
theorem ly_no_eps {x e : Ordinal.{0}} (hBe : VzB x < e) (he : e < eN (VzB x)) : ¬ InE e :=
  fun hE => absurd (eN_le hBe hE) (not_le.2 he)

/-- **Representation below `ε_{B(ρ)+1}`.** -/
theorem lyt_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) :
    ∀ v, v < eN (VzB ρ) → ∃ t : LyTm, CBt t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_trichotomy v (VzB ρ) with hvB | rfl | hBv
  · obtain ⟨N, hN⟩ := vzB_lt_iff.1 hvB
    obtain ⟨d, hd, hdv⟩ := vzv_rep hρ hρ1 (le_max_right N 1) v (hN.trans_le (vzN_le hρ hρ1 (le_max_left N 1)))
    exact ⟨vz d, hd, hdv⟩
  · exact ⟨bB, trivial, rfl⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0 | h0
  · -- `v = ω^z`
    rw [h0, zero_add] at hvs
    have hzv : lg v < v := by
      have hz : lg v ≤ ω ^ lg v := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz.trans_eq hvs.symm) fun e => ?_
      exact ly_no_eps hBv hv (show ω ^ v = v from
        calc ω ^ v = ω ^ lg v := by rw [e]
          _ = v := hvs.symm)
    obtain ⟨t, ht, htv⟩ := IH _ hzv (hzv.trans hv)
    exact ⟨pw t, ht, by rw [val_pw, htv, ← hvs]⟩
  · have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0 hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨t1, ht1, hv1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨t2, ht2, hv2⟩ := IH _ hwv (hwv.trans hv)
    exact ⟨sm t1 t2, ⟨ht1, ht2⟩, by rw [val_sm, hv1, hv2, ← hvs]⟩

/-! ## Lemma IMG below `ε_{B(ρ)+1}` -/

variable {ρ τ δ : Ordinal.{0}}

/-- **One atom step** (as `lyStep`, with the previous power in `W ∪ Z`). -/
theorem lyStep2 (h : RstK ρ τ δ) {e q : Ordinal.{0}} {W0 Z0 : Finset Ordinal.{0}}
    (hρN : ρ < ω ^ (e + ω ^ q)) (hq0 : 0 < q) (hqN : q < ω ^ (e + ω ^ q)) (hNδ : ω ^ (e + ω ^ q) < δ)
    (hw0 : WZ ρ δ W0 Z0) (hPW : ω ^ e ∈ W0 ∪ Z0) (hqW : q ∈ W0 ∪ Z0) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (e + ω ^ q) ∈ W ∧ W0 ⊆ W ∧ Z0 ⊆ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        ∃ a, f (ω ^ (e + ω ^ q)) = ω ^ a ∧ ω ^ f q ∣ a ∧
          ∀ e', f (ω ^ e) = ω ^ e' → e' + ω ^ f q ≤ a := by
  classical
  have hδI := inE_indec h.δE
  set N := ω ^ (e + ω ^ q) with hN
  have hPN : ω ^ e < N := ly_lt_next e q
  have hNq : N + q < δ := hδI.add_lt hNδ (hqN.trans hNδ)
  have hw : WZ ρ δ (insert (N + q) (insert N W0)) Z0 := by
    have w1 := hw0.insW hρN.le hNδ (Or.inl (indec_opow _))
    refine w1.insW (hρN.le.trans le_self_add) hNq (Or.inr ⟨N, by simp, q, ?_, lt_add_of_pos_right N hq0,
      hqN.trans_le le_self_add, rfl⟩)
    rcases Finset.mem_union.1 hqW with hq | hq
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hq)
    · exact Finset.mem_union_right _ hq
  refine ⟨_, _, hw, by simp, fun x hx => by simp [hx], subset_refl _, fun A f hW hZ C => ?_⟩
  have hNA : N ∈ A := hW (by simp)
  have hNqA : N + q ∈ A := hW (by simp)
  have hmem : ∀ x, x ∈ W0 ∪ Z0 → x ∈ A := fun x hx => by
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hW (by simp [hx])
    · exact hZ (by simp [hx])
  have hPA : ω ^ e ∈ A := hmem _ hPW
  have hqA : q ∈ A := hmem _ hqW
  have hfq0 : 0 < f q := by
    rcases lt_or_ge q ρ with hqρ | hqρ
    · rw [C.fix q hqA hqρ]; exact hq0
    · exact (C.ups.1).trans_le (C.mono.monotoneOn C.rho hqA hqρ)
  have hfPN : f (ω ^ e) < f N := C.mono hPA hNA hPN
  have hfqN : f q < f N := C.mono hqA hNA hqN
  have hne : e + ω ^ q ≠ 0 := (lt_of_lt_of_le (opow_pos q omega0_pos) le_add_self).ne'
  have hsrc : le1 N (N + q) := by
    refine (h.lowδ N (N + q) hρN hNq.le).2 ?_
    refine (le1R_thm22 hq0 hqN.le).2 ⟨e + ω ^ q, hne, rfl, ?_⟩
    refine (le_lg_iff hne q).2 ?_
    rw [Cp.cpAdd_opow]; exact dvd_mul_right _ _
  have himg : le1 (f N) (f N + f q) := by
    have := C.cov1 N hNA (N + q) hNqA hsrc
    rwa [← C.add N hNA q hqA (N + q) hNqA rfl] at this
  by_cases hU : UpsPt (f N)
  · have hE := upsPt_inE hU
    refine ⟨f N, hE.symm, opow_dvd_of_inE hE hfqN.le, fun e' he' => ?_⟩
    have h1 : e' < f N := (right_le_opow e' one_lt_omega0).trans_lt (he' ▸ hfPN)
    exact ((inE_indec hE).add_lt h1 (hE.opow_lt hfqN)).le
  · have hR := (C.sk (f N) (C.low N hNA) hU (f N + f q)).1 himg
    obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfq0 hfqN.le).1 hR
    have hdiv : ω ^ f q ∣ a := (le_lg_iff ha0 _).1 hza
    refine ⟨a, hfa, hdiv, fun e' he' => ?_⟩
    have h3 : e' < a := by
      have := hfPN; rw [hfa, he'] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    exact xt_dvd_next' hdiv h3

/-- **The IMG statement for one value** `v` with a term `t` of `LyTm` (`t(ρ) = v`, constants in `Z`). -/
def LyImg (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : LyTm) : Prop :=
  WZ ρ δ W Z ∧ CBt t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ val t ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val t (f ρ) ≤ f v

theorem lyt_cbt_img {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {t : LyTm}
    (ht : CBt t ρ) (hA : ∀ c ∈ cs t, c ∈ A) : CBt t (f ρ) :=
  cbt_iff t ρ (f ρ) ht (fun c hc => C.above c (hA c hc) (cbt_cst t ρ ht c hc))

theorem lyt_val_fρ (h : RstK ρ τ δ) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {t u : LyTm} (ht : CBt t ρ) (hu : CBt u ρ) (htA : ∀ c ∈ cs t, c ∈ A) (huA : ∀ c ∈ cs u, c ∈ A)
    (htu : val t ρ = val u ρ) : val t (f ρ) = val u (f ρ) :=
  (lyt_uni_eq C.ups h.ρU (h.img_bases C) (lyt_cbt_img C ht htA) (lyt_cbt_img C hu huA)).1 htu

theorem lyImg_sub {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : LyTm} (hI : LyImg ρ δ v W Z t)
    {A : Set Ordinal.{0}} (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : (∀ c ∈ cs t, c ∈ A) ∧ v ∈ A :=
  ⟨fun c hc => hZ (Finset.mem_coe.2 (hI.2.2.1 c hc)), mem_A hI.2.2.2.2.1 hW hZ⟩

/-- **Lemma IMG below `ε_{B(ρ)+1}`.** -/
theorem lyt_img (h : RstK ρ τ δ) : ∀ v, v < eN (VzB ρ) → ∃ W Z t, LyImg ρ δ v W Z t := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hBE := xt_B_E hρE hρ1
  have hρB : ρ < VzB ρ := (vzB_omega hρE hρ1).2.1
  have heδ : eN (VzB ρ) ≤ δ := eN_le h.vz_B_lt_δ hδE
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans_le heδ
  rcases lt_trichotomy v (VzB ρ) with hvB | rfl | hBv
  · obtain ⟨⟨W, Z, s, hw, hc, hcs, hvs, hm, hI⟩, -⟩ := h.imgVz v hvB
    exact ⟨W, Z, vz s, hw, hc, hcs, hvs, hm, hI⟩
  · obtain ⟨hw, hBW, hI⟩ := xtWitB h
    exact ⟨_, _, bB, hw, trivial, by simp [cs], rfl, Finset.mem_union_left _ hBW,
      fun A f hW hZ C => (hI A f hW hZ C).2⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0 | h0
  · -- `v = ω^z`, `z = z' + ω^q`
    rw [h0, zero_add] at hvs
    set z := lg v with hz
    have hzv : z < v := by
      have hz' : z ≤ ω ^ z := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz'.trans_eq hvs.symm) fun e => ?_
      exact ly_no_eps hBv hv (show ω ^ v = v from
        calc ω ^ v = ω ^ z := by rw [e]
          _ = v := hvs.symm)
    have hz0 : z ≠ 0 := by
      intro e; rw [e, opow_zero] at hvs
      exact absurd (hvs ▸ hBv) (not_lt.2 (one_le_iff_pos.2 hBE.pos))
    obtain ⟨z', hzs, -, hz'z⟩ := lg_split hz0
    set q := lg z with hq
    have hqz : q ≤ z := lg_le hz0
    have hqv : q < v := hqz.trans_lt hzv
    have hPv : ω ^ z' < v := by
      rw [hvs]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hz'z
    obtain ⟨Wq, Zq, tq, Iq⟩ := IH q hqv (hqv.trans hv)
    obtain ⟨Wp, Zp, tp, Ip⟩ := IH _ hPv (hPv.trans hv)
    obtain ⟨Wz, Zz, tz, Iz⟩ := IH z' (hz'z.trans hzv) ((hz'z.trans hzv).trans hv)
    set t := pw (sm tz (pw tq)) with ht
    have htv : val t ρ = v := by
      rw [ht, val_pw, val_sm, val_pw, Iz.2.2.2.1, Iq.2.2.2.1, ← hzs, ← hvs]
    have hw0 : WZ ρ δ ((Wq ∪ Wp) ∪ Wz) ((Zq ∪ Zp) ∪ Zz) := (Iq.1.union Ip.1).union Iz.1
    have hcsT : ∀ c ∈ cs t, c ∈ (Zq ∪ Zp) ∪ Zz := by
      intro c hc
      simp only [ht, cs, List.mem_append] at hc
      rcases hc with hc | hc
      · simp [Iz.2.2.1 c hc]
      · simp [Iq.2.2.1 c hc]
    have hcbT : CBt t ρ := ⟨Iz.2.1, Iq.2.1⟩
    have hmem : ∀ {x W Z}, x ∈ W ∪ Z → W ⊆ (Wq ∪ Wp) ∪ Wz → Z ⊆ (Zq ∪ Zp) ∪ Zz →
        x ∈ ((Wq ∪ Wp) ∪ Wz) ∪ ((Zq ∪ Zp) ∪ Zz) := fun hx hW hZ =>
      Finset.union_subset_union hW hZ hx
    have hPW0 := hmem Ip.2.2.2.2.1 (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
    have hqW0 := hmem Iq.2.2.2.2.1 (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
    -- the common bound at the copy: `tz(f ρ) ≤ e1` for `f(ω^{z'}) = ω^{e1}`
    have hcom : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑((Wq ∪ Wp) ∪ Wz) ⊆ A →
        ↑((Zq ∪ Zp) ∪ Zz) ⊆ A → ImgCtx ρ A f → val tq (f ρ) ≤ f q ∧
          ∀ e1, f (ω ^ z') = ω ^ e1 → val tz (f ρ) ≤ e1 := by
      intro A f hW hZ C
      have hWq : ↑Wq ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZq : ↑Zq ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hWp : ↑Wp ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZp : ↑Zp ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      have hZz : ↑Zz ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      refine ⟨Iq.2.2.2.2.2 A f hWq hZq C, fun e1 he1 => ?_⟩
      have hpA := (lyImg_sub Ip hWp hZp).1
      have hzA : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZz (Finset.mem_coe.2 (Iz.2.2.1 c hc))
      have heq := lyt_val_fρ h C (t := pw tz) (u := tp) Iz.2.1 Ip.2.1 hzA hpA
        (by rw [val_pw, Iz.2.2.2.1, Ip.2.2.2.1])
      have hle := Ip.2.2.2.2.2 A f hWp hZp C
      rw [← heq, val_pw, he1] at hle
      exact (opow_le_opow_iff_right one_lt_omega0).1 hle
    rcases eq_or_ne q 0 with hq0 | hq0
    · -- `z = z' + 1`: the copy of a power is a power
      have hw : WZ ρ δ (insert v ((Wq ∪ Wp) ∪ Wz)) ((Zq ∪ Zp) ∪ Zz) :=
        hw0.insW hρv.le hvδ (Or.inl (hvs ▸ indec_opow _))
      refine ⟨_, _, t, hw, hcbT, hcsT, htv, by simp, fun A f hW hZ C => ?_⟩
      have hW0 : ↑((Wq ∪ Wp) ∪ Wz) ⊆ A := fun x hx =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      obtain ⟨hqf, hzf⟩ := hcom A f hW0 hZ C
      have hvA : v ∈ A := hW (by simp)
      have hPA : ω ^ z' ∈ A := mem_A hPW0 hW0 hZ
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec v hvA (hvs ▸ indec_opow _))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      have h2 : f (ω ^ z') < f v := C.mono hPA hvA hPv
      rw [hc, he1] at h2
      have h3 : e1 < c := (opow_lt_opow_iff_right one_lt_omega0).1 h2
      have htq0 : val tq (f ρ) = 0 := lyt_zero hρE hρ1 tq Iq.2.1 (by rw [Iq.2.2.2.1, hq0]) (f ρ)
      rw [hc, ht, val_pw, val_sm, val_pw, htq0, opow_zero]
      exact opow_le_opow_right omega0_pos ((add_le_add (hzf e1 he1) le_rfl).trans (Order.add_one_le_of_lt h3))
    · -- one atom step
      have hNe : v = ω ^ (z' + ω ^ q) := by rw [hvs, hzs]
      obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ := lyStep2 h (hNe ▸ hρv) (pos_iff_ne_zero.2 hq0)
        (hNe ▸ hqv) (hNe ▸ hvδ) hw0 hPW0 hqW0
      refine ⟨W, Z, t, hw, hcbT, fun c hc => hZZ (hcsT c hc), htv, Finset.mem_union_left _ (hNe ▸ hNW),
        fun A f hW hZ C => ?_⟩
      obtain ⟨hqf, hzf⟩ := hcom A f (fun x hx => hW (hWW (Finset.mem_coe.1 hx)))
        (fun x hx => hZ (hZZ (Finset.mem_coe.1 hx))) C
      obtain ⟨a, ha, -, hnext⟩ := hI A f hW hZ C
      have hPA : ω ^ z' ∈ A := by
        rcases Finset.mem_union.1 hPW0 with h' | h'
        · exact hW (Finset.mem_coe.2 (hWW h'))
        · exact hZ (Finset.mem_coe.2 (hZZ h'))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      rw [hNe, ha, ht, val_pw, val_sm, val_pw]
      exact opow_le_opow_right omega0_pos
        ((add_le_add (hzf e1 he1) (opow_le_opow_right omega0_pos hqf)).trans (hnext e1 he1))
  · -- `v = v' + ω^{lg v}`, `v' ≠ 0`: a sum
    have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0 hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨W1, Z1, t1, I1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨W2, Z2, t2, I2⟩ := IH _ hwv (hwv.trans hv)
    have hw : WZ ρ δ (insert v (W1 ∪ W2)) (Z1 ∪ Z2) := by
      refine (I1.1.union I2.1).insW hρv.le hvδ (Or.inr ⟨v', ?_, ω ^ lg v, ?_, hv'v, hwv, hvs.symm⟩)
      · exact Finset.union_subset_union (Finset.subset_union_left) (Finset.subset_union_left) I1.2.2.2.2.1
      · exact Finset.union_subset_union (Finset.subset_union_right) (Finset.subset_union_right) I2.2.2.2.2.1
    refine ⟨_, _, sm t1 t2, hw, ⟨I1.2.1, I2.2.1⟩, fun c hc => ?_, by rw [val_sm, I1.2.2.2.1, I2.2.2.2.1, ← hvs],
      by simp, fun A f hW hZ C => ?_⟩
    · simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_union_left _ (I1.2.2.1 c hc)
      · exact Finset.mem_union_right _ (I2.2.2.1 c hc)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have h1A := (lyImg_sub I1 hW1 hZ1).2
    have h2A := (lyImg_sub I2 hW2 hZ2).2
    have hvA : v ∈ A := hW (by simp)
    rw [val_sm, ← C.add v' h1A _ h2A v hvA hvs.symm]
    exact add_le_add (I1.2.2.2.2.2 A f hW1 hZ1 C) (I2.2.2.2.2.2 A f hW2 hZ2 C)

end Googology.Trans.PoR.InaccPsi.R2.Ly
