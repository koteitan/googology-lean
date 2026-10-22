import Googology.Trans.PoR.InaccPsi.R2.LyEp

/-!
# Exponent terms over a layer with an `ε`-number top: the terms of `K`, the atom `E_K(x)`, sums and `ω`-powers

`R2.LyTm` builds the exponent terms below `ε_{B(x)+1}` from the `φ(n, ·)`-terms (values below `B(x)`), the atom `B(x)`,
sums and `ω`-powers.  Here the same construction is done once for **every layer `K`** (`R2.XtLay`) whose top
`T_K(x) = ω^{E_K(x)}` is an `ε`-number (`LxEK K`: `E_K(x) ∈ E`, so `T_K(x) = E_K(x)`):

* `LxTm K` (**the terms**: `bs t` with `t` a term of `K`, the atom `tp` with value `E_K(x)`, `sm a b`, `pw a`);
* `lxt_lt_eN` (**every value is below `ε_{E_K(x)+1}`**), `lx_eN_lt` (`ε_{E_K(x)+1}` is below `Ω₁` and below every
  `υ`-point above `x`);
* `lxt_pi` (**Lemma EXACT**: `π_{σ,ρ}(t(ρ)) = t(σ)`, from the EXACT of `K`, of `E_K`, `pi_add`, `pi_opowZ`),
  `lxt_uni_le`, `lxt_uni_lt`, `lxt_uni_eq`, `lxt_zero`;
* `LxRep`, `lxRep_ri`, `lxt_rep` (**representation**: every ordinal below `ε_{E_K(ρ)+1}` is a value, at every
  restart `ρ = υ_λ`);
* `LxImg`, `LxBase` (the IMG statement for the values below `E_K(ρ)` by terms of `K`), `lxBase_ri` (**it holds at
  every restart**: the IMG package of the term of `K`, `XtSys.pkg`), `lxt_img` (**Lemma IMG below `ε_{E_K(ρ)+1}`**:
  below `E_K(ρ)` from `LxBase`, at `E_K(ρ)` from the witness pair of the top of `K`, sums by the closure of the witness
  sets, a power by one atom step `ω^z ≤₁ ω^z + q` of `R₁⁺` (`Ly.lyStep2`, [W07b] Theorem 2.2) or, for `q = 0`,
  because the copy of a power is a power).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly

/-- **The exponent terms over a layer `K`**: terms of `K`, the atom `E_K(x)`, sums and `ω`-powers. -/
inductive LxTm (K : XtLay) : Type 1
  | bs : K.sys.Tm → LxTm K
  | tp : LxTm K
  | sm : LxTm K → LxTm K → LxTm K
  | pw : LxTm K → LxTm K

/-- The top of `K` is an `ε`-number: `E_K(x) ∈ E` at every base. -/
def LxEK (K : XtLay) : Prop := ∀ x, InE x → x < Om1 → InE (K.E x)

namespace LxTm

variable {K : XtLay}

/-- The value at the base `x`. -/
noncomputable def val : LxTm K → Ordinal.{0} → Ordinal.{0}
  | bs t, x => K.sys.val t x
  | tp, x => K.E x
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`. -/
def CBt : LxTm K → Ordinal.{0} → Prop
  | bs t, s => K.sys.CB t s
  | tp, _ => True
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LxTm K → List Ordinal.{0}
  | bs t => K.sys.cs t
  | tp => []
  | sm a b => cs a ++ cs b
  | pw a => cs a

@[simp] theorem val_bs (t : K.sys.Tm) (x : Ordinal.{0}) : val (bs t) x = K.sys.val t x := rfl
@[simp] theorem val_tp (x : Ordinal.{0}) : val (tp : LxTm K) x = K.E x := rfl
@[simp] theorem val_sm (a b : LxTm K) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LxTm K) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LxTm K) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | bs t, s, s', h, h' => K.sys.cb_iff t s s' h h'
  | tp, _, _, _, _ => trivial
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LxTm K) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | bs t, s, h, c, hc => K.sys.cb_cst t s h c hc
  | tp, _, _, c, hc => by simp [cs] at hc
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LxTm K} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LxTm

open LxTm

variable {K : XtLay}

/-- The constants of the constant term `0` of a term system are `0`. -/
theorem lx_cs_cst0 (X : XtSys) : ∀ c ∈ X.cs (X.cst 0), c = 0 := fun c hc =>
  Order.lt_one_iff.1 (X.cb_cst _ 1 (X.cb_cstI 0 1 zero_lt_one) c hc)

section Base

variable (hK : LxEK K)
include hK

/-- The top of `K` is `E_K(x)`. -/
theorem lx_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : K.sys.top x = K.E x := by
  rw [K.top_eq x hx hx1]; exact hK x hx hx1

theorem lx_E_gt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x < K.E x := by
  rw [← lx_top hK hx hx1]; exact K.top_gt x hx hx1

/-- **`ε_{E_K(x)+1}` lies below `Ω₁` and below every `υ`-point above `x`.** -/
theorem lx_eN_lt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    eN (K.E x) < Om1 ∧ ∀ u, x < u → UpsPt u → eN (K.E x) < u := by
  have hb := ly_eN_lt (hK x hx hx1) (K.exp_lt x hx hx1)
  exact ⟨hb.1, fun u hxu hu => hb.2 u (by rw [← lx_top hK hx hx1]; exact K.top_lt_ups x u hx hx1 hxu hu) hu.2⟩

/-- **Every value is below `ε_{E_K(x)+1}`.** -/
theorem lxt_lt_eN {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LxTm K, CBt t x → val t x < eN (K.E x)
  | bs t, h => by
    rw [val_bs, ← lx_top hK hx hx1]; exact (K.lt_top_E x hx hx1 t h).trans (lt_eN _)
  | tp, _ => lt_eN _
  | sm a b, h => (inE_indec (eN_E _)).add_lt (lxt_lt_eN hx hx1 a h.1) (lxt_lt_eN hx hx1 b h.2)
  | pw a, h => (eN_E _).opow_lt (lxt_lt_eN hx hx1 a h)

theorem lxt_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (t : LxTm K) (h : CBt t x) :
    val t x < Om1 :=
  (lxt_lt_eN hK hx hx1 t h).trans (lx_eN_lt hK hx hx1).1

/-- **Lemma EXACT for `LxTm K`.** -/
theorem lxt_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LxTm K, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | bs t, h => K.exact σ ρ hσ hρ hB t h
  | tp, _ => K.exp_pi σ ρ hσ hρ hB
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lxt_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lxt_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := lxt_pi hσ hρ hB a h
    have hb := lxt_lt_Om1 hK hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem lxt_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LxTm K}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lxt_pi hK hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lxt_pi hK hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem lxt_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LxTm K}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, lxt_uni_le hK hσ hρ hB hu ht]

theorem lxt_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LxTm K}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, lxt_uni_le hK hσ hρ hB ht hu, lxt_uni_le hK hσ hρ hB hu ht]

/-- **A value `0` is the value `0` everywhere.** -/
theorem lxt_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LxTm K, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | bs t, h, h0 => by
    rcases K.sys.small t with hc | hc
    · intro y; rw [val_bs, hc y x]; exact h0
    · have := hc x hx hx1 h
      rw [val_bs] at h0; rw [h0] at this
      exact absurd this (not_le.2 hx.pos)
  | tp, _, h0 => absurd h0 (hK x hx hx1).pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, lxt_zero hx hx1 a h.1 this.1 y, lxt_zero hx hx1 b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

end Base

/-- An `ε`-number strictly between `E_K(x)` and `ε_{E_K(x)+1}` does not exist. -/
theorem lx_no_eps {x e : Ordinal.{0}} (hBe : K.E x < e) (he : e < eN (K.E x)) : ¬ InE e :=
  fun hE => absurd (eN_le hBe hE) (not_le.2 he)

/-! ## Representation -/

/-- Every value below `E_K(ρ)` is the value of a term of `K`. -/
def LxRep (K : XtLay) (ρ : Ordinal.{0}) : Prop :=
  ∀ v < K.E ρ, ∃ t : K.sys.Tm, K.sys.CB t ρ ∧ K.sys.val t ρ = v

theorem lxRep_ri (hK : LxEK K) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    LxRep K (upsilon l) := fun v hv =>
  K.sys.rep l hl hl1 v (by rw [lx_top hK (ups_inE hl) (ups_lt_Om1 l hl1)]; exact hv)

/-- **Representation below `ε_{E_K(ρ)+1}`.** -/
theorem lxt_rep (hK : LxEK K) {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) (hr : LxRep K ρ) :
    ∀ v, v < eN (K.E ρ) → ∃ t : LxTm K, CBt t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_trichotomy v (K.E ρ) with hvB | rfl | hBv
  · obtain ⟨t, ht, htv⟩ := hr v hvB
    exact ⟨bs t, ht, htv⟩
  · exact ⟨tp, trivial, rfl⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0 | h0
  · rw [h0, zero_add] at hvs
    have hzv : lg v < v := by
      have hz : lg v ≤ ω ^ lg v := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz.trans_eq hvs.symm) fun e => ?_
      exact lx_no_eps hBv hv (show ω ^ v = v from
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

/-! ## Lemma IMG below `ε_{E_K(ρ)+1}` -/

variable {ρ τ δ : Ordinal.{0}}

/-- **The IMG statement for one value** `v` with a term `t` of `LxTm K` (`t(ρ) = v`, constants in `Z`). -/
def LxImg (K : XtLay) (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : LxTm K) : Prop :=
  WZ ρ δ W Z ∧ CBt t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ val t ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val t (f ρ) ≤ f v

/-- **The IMG statement below `E_K(ρ)`**: every value below `E_K(ρ)` has a term and witness sets. -/
def LxBase (K : XtLay) (ρ δ : Ordinal.{0}) : Prop :=
  ∀ v < K.E ρ, ∃ W Z : Finset Ordinal.{0}, ∃ t : LxTm K, LxImg K ρ δ v W Z t

/-- **`LxBase` holds at every restart**: the IMG package of the term of `K` (`XtSys.pkg`). -/
theorem lxBase_ri (hK : LxEK K) {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (R : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1))) :
    LxBase K (upsilon l) (upsilon (l + ω + 1)) := by
  classical
  intro v hv
  have hρE := R.ρE
  have hρ1 := R.ρ1
  rcases eq_or_ne v 0 with rfl | h0
  · refine ⟨∅, insert 0 ∅, bs (K.sys.cst 0), WZ.empty.insZ hρE.pos, K.sys.cb_cstI 0 _ hρE.pos,
      fun c hc => by rw [lx_cs_cst0 K.sys c hc]; exact Finset.mem_insert_self _ _, by
        rw [val_bs, K.sys.val_cst], by simp, fun A f _ _ _ => by rw [val_bs, K.sys.val_cst]; exact zero_le⟩
  · obtain ⟨t, ht, hvt⟩ := K.sys.rep l hl hl1 v (by rw [lx_top hK hρE hρ1]; exact hv)
    obtain ⟨-, -, W, Z, hw, hm, hI⟩ := K.sys.pkg l hl hl1 t ht (by rw [hvt]; exact one_le_iff_ne_zero.2 h0) R
    have hwc : WZ (upsilon l) (upsilon (l + ω + 1)) ∅ (K.sys.cs t).toFinset :=
      ⟨by simp, fun z hz => K.sys.cb_cst t _ ht z (List.mem_toFinset.1 hz), by simp⟩
    have hw2 := hw.union hwc
    rw [Finset.union_empty] at hw2
    refine ⟨W, Z ∪ (K.sys.cs t).toFinset, bs t, hw2, ht,
      fun c hc => Finset.mem_union_right _ (List.mem_toFinset.2 hc), hvt, ?_, fun A f hW hZ C => ?_⟩
    · rw [← hvt]
      rcases Finset.mem_union.1 hm with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    · rw [val_bs, ← hvt]
      exact hI A f hW (fun x hx => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx)))) C

theorem lxt_cbt_img {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {t : LxTm K}
    (ht : CBt t ρ) (hA : ∀ c ∈ cs t, c ∈ A) : CBt t (f ρ) :=
  cbt_iff t ρ (f ρ) ht (fun c hc => C.above c (hA c hc) (cbt_cst t ρ ht c hc))

theorem lxt_val_fρ (hK : LxEK K) (h : RstK ρ τ δ) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {t u : LxTm K} (ht : CBt t ρ) (hu : CBt u ρ) (htA : ∀ c ∈ cs t, c ∈ A)
    (huA : ∀ c ∈ cs u, c ∈ A) (htu : val t ρ = val u ρ) : val t (f ρ) = val u (f ρ) :=
  (lxt_uni_eq hK C.ups h.ρU (h.img_bases C) (lxt_cbt_img C ht htA) (lxt_cbt_img C hu huA)).1 htu

theorem lxImg_sub {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : LxTm K} (hI : LxImg K ρ δ v W Z t)
    {A : Set Ordinal.{0}} (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : (∀ c ∈ cs t, c ∈ A) ∧ v ∈ A :=
  ⟨fun c hc => hZ (Finset.mem_coe.2 (hI.2.2.1 c hc)), mem_A hI.2.2.2.2.1 hW hZ⟩

/-- **Lemma IMG below `ε_{E_K(ρ)+1}`.** -/
theorem lxt_img (hK : LxEK K) (h : RstK ρ τ δ) (hb : LxBase K ρ δ) :
    ∀ v, v < eN (K.E ρ) → ∃ W Z t, LxImg K ρ δ v W Z t := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hBE := hK ρ hρE hρ1
  have hρB : ρ < K.E ρ := lx_E_gt hK hρE hρ1
  have heδ : eN (K.E ρ) ≤ δ := ((lx_eN_lt hK hρE hρ1).2 δ h.ρδ h.next.2.1).le
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans_le heδ
  rcases lt_trichotomy v (K.E ρ) with hvB | rfl | hBv
  · exact hb v hvB
  · obtain ⟨W, Z, hw, hTW, hI⟩ := K.top_wit ρ τ δ h
    rw [lx_top hK hρE hρ1] at hTW
    refine ⟨W, Z, tp, hw, trivial, by simp [cs], rfl, Finset.mem_union_left _ hTW, fun A f hW hZ C => ?_⟩
    have h2 := (hI A f hW hZ C).2
    have hfE := upsPt_inE C.ups
    have hf1 := (C.low ρ C.rho).trans hρ1
    rw [lx_top hK hfE hf1, lx_top hK hρE hρ1] at h2
    exact h2
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
      exact lx_no_eps hBv hv (show ω ^ v = v from
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
    obtain ⟨Wp, Zp, tp', Ip⟩ := IH _ hPv (hPv.trans hv)
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
      have hpA := (lxImg_sub Ip hWp hZp).1
      have hzA : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZz (Finset.mem_coe.2 (Iz.2.2.1 c hc))
      have heq := lxt_val_fρ hK h C (t := pw tz) (u := tp') Iz.2.1 Ip.2.1 hzA hpA
        (by rw [val_pw, Iz.2.2.2.1, Ip.2.2.2.1])
      have hle := Ip.2.2.2.2.2 A f hWp hZp C
      rw [← heq, val_pw, he1] at hle
      exact (opow_le_opow_iff_right one_lt_omega0).1 hle
    rcases eq_or_ne q 0 with hq0 | hq0
    · have hw : WZ ρ δ (insert v ((Wq ∪ Wp) ∪ Wz)) ((Zq ∪ Zp) ∪ Zz) :=
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
      have htq0 : val tq (f ρ) = 0 := lxt_zero hK hρE hρ1 tq Iq.2.1 (by rw [Iq.2.2.2.1, hq0]) (f ρ)
      rw [hc, ht, val_pw, val_sm, val_pw, htq0, opow_zero]
      exact opow_le_opow_right omega0_pos ((add_le_add (hzf e1 he1) le_rfl).trans (Order.add_one_le_of_lt h3))
    · have hNe : v = ω ^ (z' + ω ^ q) := by rw [hvs, hzs]
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
    have h1A := (lxImg_sub I1 hW1 hZ1).2
    have h2A := (lxImg_sub I2 hW2 hZ2).2
    have hvA : v ∈ A := hW (by simp)
    rw [val_sm, ← C.add v' h1A _ h2A v hvA hvs.symm]
    exact add_le_add (I1.2.2.2.2.2 A f hW1 hZ1 C) (I2.2.2.2.2.2 A f hW2 hZ2 C)

end Googology.Trans.PoR.InaccPsi.R2.Lx
