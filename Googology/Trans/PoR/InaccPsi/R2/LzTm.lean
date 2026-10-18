import Googology.Trans.PoR.InaccPsi.R2.LzEps

/-!
# The terms over `B` with the atoms `e_c(x) = ε_{B(x)+1+c}`: values below `e_x(x) = ϑˣ(Ω₁ + B(x) + x)`

`LzTm`: a term `ly t` of `R2.LyTm` (values below `ε_{B(x)+1}`), an atom `ep c` (value `e_c(x) = ϑˣ(Ω₁ + B(x) + c)`,
`c` a constant, `R2.LzEps`), a sum `sm a b`, a power `pw a` (`ω^a`).  For every base `x` (an `ε`-number below `Ω₁`):

* `lzt_lt_top` (**every value is below `e_x(x)`**), `lzt_pi` (**Lemma EXACT**, from `lyt_pi`, `lzE_pi`, `pi_add`,
  `pi_opowZ`), `lzt_uni_le`, `lzt_uni_lt`, `lzt_uni_eq`;
* `lzt_rep` (**representation**: every ordinal below `e_ρ(ρ)` is a value with constants below `ρ`: an `ε`-number in
  `[ε_{B(ρ)+1}, e_ρ(ρ))` is an atom, `lzE_enum`);
* `lzt_zero`, `LzC` and `lzt_small` (a term without the base is constant, any other has value `≥ x`);
* `lzt_img` (**Lemma IMG below `e_ρ(ρ)`**: below `ε_{B(ρ)+1}` from `lyt_img`, at an atom from `lzE_imgAll`, a power
  `ω^{z' + ω^q}` by one atom step `ω^z ≤₁ ω^z + q` of `R₁⁺`, a sum by a sum).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lz

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly

/-- **The terms over `B` with the atoms `e_c`.** -/
inductive LzTm : Type 1
  | ly : LyTm → LzTm
  | ep : Ordinal.{0} → LzTm
  | sm : LzTm → LzTm → LzTm
  | pw : LzTm → LzTm

namespace LzTm

/-- The value at the base `x`. -/
noncomputable def val : LzTm → Ordinal.{0} → Ordinal.{0}
  | ly t, x => t.val x
  | ep c, x => lzE x c
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`. -/
def CBt : LzTm → Ordinal.{0} → Prop
  | ly t, s => t.CBt s
  | ep c, s => c < s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LzTm → List Ordinal.{0}
  | ly t => t.cs
  | ep c => [c]
  | sm a b => cs a ++ cs b
  | pw a => cs a

@[simp] theorem val_ly (t : LyTm) (x : Ordinal.{0}) : val (ly t) x = t.val x := rfl
@[simp] theorem val_ep (c x : Ordinal.{0}) : val (ep c) x = lzE x c := rfl
@[simp] theorem val_sm (a b : LzTm) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LzTm) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LzTm) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | ly t, s, s', h, h' => LyTm.cbt_iff t s s' h h'
  | ep c, _, _, _, h' => h' c (by simp [cs])
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LzTm) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | ly t, s, h, c, hc => LyTm.cbt_cst t s h c hc
  | ep _, _, h, c, hc => by simp [cs] at hc; subst hc; exact h
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LzTm} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LzTm

open LzTm

/-! ## Values, EXACT, comparison -/

theorem lz_e0_lt_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN (VzB x) < lzE x x := by
  rw [← lzE_zero hx hx1]; exact lzE_strict hx hx1 hx.pos le_rfl

/-- **Every value is below `e_x(x)`.** -/
theorem lzt_lt_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LzTm, CBt t x → val t x < lzE x x
  | ly t, h => (lyt_lt_eN hx hx1 t h).trans (lz_e0_lt_top hx hx1)
  | ep _, h => lzE_strict hx hx1 h le_rfl
  | sm a b, h => (inE_indec (lzE_facts hx hx1 le_rfl).2.2.2.2.2.1).add_lt (lzt_lt_top hx hx1 a h.1)
      (lzt_lt_top hx hx1 b h.2)
  | pw a, h => (lzE_facts hx hx1 le_rfl).2.2.2.2.2.1.opow_lt (lzt_lt_top hx hx1 a h)

theorem lzTop_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : lzE x x < Om1 :=
  (lzE_facts hx hx1 le_rfl).2.2.2.2.1

theorem lzt_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (t : LzTm) (h : CBt t x) : val t x < Om1 :=
  (lzt_lt_top hx hx1 t h).trans (lzTop_lt_Om1 hx hx1)

theorem lzTop_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    lzE x x < u :=
  lzE_lt_ups hx hx1 le_rfl hxu hu.2

/-- **Lemma EXACT for `LzTm`.** -/
theorem lzt_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LzTm, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | ly t, h => lyt_pi hσ hρ hB t h
  | ep c, h => lzE_pi hB h
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lzt_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lzt_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := lzt_pi hσ hρ hB a h
    have hb := lzt_lt_Om1 hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem lzt_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lzt_pi hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lzt_pi hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem lzt_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, lzt_uni_le hσ hρ hB hu ht]

theorem lzt_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LzTm}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, lzt_uni_le hσ hρ hB ht hu, lzt_uni_le hσ hρ hB hu ht]

/-- **A value `0` is the value `0` everywhere.** -/
theorem lzt_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LzTm, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | ly t, h, h0 => lyt_zero hx hx1 t h h0
  | ep _, h, h0 => absurd h0 (lzE_facts hx hx1 h.le).2.2.2.2.2.1.pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, lzt_zero hx hx1 a h.1 this.1 y, lzt_zero hx hx1 b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

/-! ## Constant terms -/

/-- A term of `LyTm` without the base, `B` and `ϑ`-terms. -/
def LyC : LyTm → Prop
  | LyTm.vz t => VzTm.noB t
  | LyTm.bB => False
  | LyTm.sm a b => LyC a ∧ LyC b
  | LyTm.pw a => LyC a

/-- A term of `LzTm` without the base (a constant term). -/
def LzC : LzTm → Prop
  | ly t => LyC t
  | ep _ => False
  | sm a b => LzC a ∧ LzC b
  | pw a => LzC a

theorem lyC_const : ∀ t : LyTm, LyC t → ∀ x y, t.val x = t.val y
  | LyTm.vz t, h, x, y => vzv_noB t h x y
  | LyTm.bB, h, _, _ => absurd h id
  | LyTm.sm a b, h, x, y => by simp only [LyTm.val_sm, lyC_const a h.1 x y, lyC_const b h.2 x y]
  | LyTm.pw a, h, x, y => by simp only [LyTm.val_pw, lyC_const a h x y]

theorem lyC_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LyTm, t.CBt x → ¬ LyC t → x ≤ t.val x
  | LyTm.vz t, hc, h => le_vzv_of_not_noB hx hx1 t hc h
  | LyTm.bB, _, _ => (vzB_omega hx hx1).2.1.le
  | LyTm.sm a b, hc, h => by
    simp only [LyC, not_and_or] at h
    rcases h with h | h
    · exact (lyC_ge hx hx1 a hc.1 h).trans le_self_add
    · exact (lyC_ge hx hx1 b hc.2 h).trans le_add_self
  | LyTm.pw a, hc, h => (lyC_ge hx hx1 a hc h).trans (right_le_opow _ one_lt_omega0)

theorem lzC_const : ∀ t : LzTm, LzC t → ∀ x y, val t x = val t y
  | ly t, h, x, y => lyC_const t h x y
  | ep _, h, _, _ => absurd h id
  | sm a b, h, x, y => by simp only [val_sm, lzC_const a h.1 x y, lzC_const b h.2 x y]
  | pw a, h, x, y => by simp only [val_pw, lzC_const a h x y]

theorem lzC_ge {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LzTm, CBt t x → ¬ LzC t → x ≤ val t x
  | ly t, hc, h => lyC_ge hx hx1 t hc h
  | ep _, hc, _ => (lzE_facts hx hx1 hc.le).2.2.2.1.le
  | sm a b, hc, h => by
    simp only [LzC, not_and_or] at h
    rcases h with h | h
    · exact (lzC_ge hx hx1 a hc.1 h).trans le_self_add
    · exact (lzC_ge hx hx1 b hc.2 h).trans le_add_self
  | pw a, hc, h => (lzC_ge hx hx1 a hc h).trans (right_le_opow _ one_lt_omega0)

theorem lzt_small (t : LzTm) :
    (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CBt t x → x ≤ val t x) := by
  by_cases h : LzC t
  · exact Or.inl (lzC_const t h)
  · exact Or.inr fun x hx hx1 hc => lzC_ge hx hx1 t hc h

/-! ## The representation -/

/-- **Representation below `e_ρ(ρ)`.** -/
theorem lzt_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) :
    ∀ v, v < lzE ρ ρ → ∃ t : LzTm, CBt t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v (eN (VzB ρ)) with h0 | h0
  · obtain ⟨t, ht, htv⟩ := lyt_rep hρ hρ1 v h0
    exact ⟨ly t, ht, htv⟩
  have hBv : VzB ρ < v := (lt_eN _).trans_le h0
  by_cases hvE : InE v
  · obtain ⟨c, hc, rfl⟩ := lzE_enum hρ hρ1 le_rfl hvE hBv hv
    exact ⟨ep c, hc, rfl⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0' | h0'
  · rw [h0', zero_add] at hvs
    have hzv : lg v < v := by
      have hz : lg v ≤ ω ^ lg v := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz.trans_eq hvs.symm) fun e => hvE ?_
      show ω ^ v = v
      calc ω ^ v = ω ^ lg v := by rw [e]
        _ = v := hvs.symm
    obtain ⟨t, ht, htv⟩ := IH _ hzv (hzv.trans hv)
    exact ⟨pw t, ht, by rw [val_pw, htv, ← hvs]⟩
  · have hwv : ω ^ lg v < v := by
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0' hdv
      calc ω ^ lg v < ω ^ lg v + ω ^ lg v := lt_add_of_pos_right _ (opow_pos _ omega0_pos)
        _ ≤ v' + ω ^ lg v := add_le_add hle le_rfl
        _ = v := hvs.symm
    obtain ⟨t1, ht1, hv1⟩ := IH v' hv'v (hv'v.trans hv)
    obtain ⟨t2, ht2, hv2⟩ := IH _ hwv (hwv.trans hv)
    exact ⟨sm t1 t2, ⟨ht1, ht2⟩, by rw [val_sm, hv1, hv2, ← hvs]⟩

/-! ## Lemma IMG below `e_ρ(ρ)` -/

variable {ρ τ δ : Ordinal.{0}}

/-- **The IMG statement for one value** `v` with a term `t` of `LzTm` (`t(ρ) = v`, constants in `Z`). -/
def LzImg (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : LzTm) : Prop :=
  WZ ρ δ W Z ∧ CBt t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ val t ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val t (f ρ) ≤ f v

theorem lzt_cbt_img {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {t : LzTm}
    (ht : CBt t ρ) (hA : ∀ c ∈ cs t, c ∈ A) : CBt t (f ρ) :=
  cbt_iff t ρ (f ρ) ht (fun c hc => C.above c (hA c hc) (cbt_cst t ρ ht c hc))

theorem lzt_val_fρ (h : RstK ρ τ δ) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {t u : LzTm} (ht : CBt t ρ) (hu : CBt u ρ) (htA : ∀ c ∈ cs t, c ∈ A) (huA : ∀ c ∈ cs u, c ∈ A)
    (htu : val t ρ = val u ρ) : val t (f ρ) = val u (f ρ) :=
  (lzt_uni_eq C.ups h.ρU (h.img_bases C) (lzt_cbt_img C ht htA) (lzt_cbt_img C hu huA)).1 htu

theorem lzImg_sub {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : LzTm} (hI : LzImg ρ δ v W Z t)
    {A : Set Ordinal.{0}} (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : (∀ c ∈ cs t, c ∈ A) ∧ v ∈ A :=
  ⟨fun c hc => hZ (Finset.mem_coe.2 (hI.2.2.1 c hc)), mem_A hI.2.2.2.2.1 hW hZ⟩

/-- **Lemma IMG below `e_ρ(ρ)`.** -/
theorem lzt_img (h : RstK ρ τ δ) : ∀ v, v < lzE ρ ρ → ∃ W Z t, LzImg ρ δ v W Z t := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρB : ρ < VzB ρ := (vzB_omega hρE hρ1).2.1
  have heδ : lzE ρ ρ < δ := LzK.lzE_lt_δ h le_rfl
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans heδ
  rcases lt_or_ge v (eN (VzB ρ)) with h0 | h0
  · obtain ⟨W, Z, s, hw, hc, hcs, hvs, hm, hI⟩ := lyt_img h v h0
    exact ⟨W, Z, ly s, hw, hc, hcs, hvs, hm, hI⟩
  have hBv : VzB ρ < v := (lt_eN _).trans_le h0
  by_cases hvE : InE v
  · obtain ⟨c, hc, rfl⟩ := lzE_enum hρE hρ1 le_rfl hvE hBv hv
    obtain ⟨W, Z, hw, heW, hcZ, hI⟩ := LzK.lzE_imgAll h c hc
    exact ⟨W, Z, ep c, hw, hc, by simp [cs, hcZ], rfl, Finset.mem_union_left _ heW, hI⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0' | h0'
  · -- `v = ω^z`, `z = z' + ω^q`
    rw [h0', zero_add] at hvs
    set z := lg v with hz
    have hzv : z < v := by
      have hz' : z ≤ ω ^ z := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz'.trans_eq hvs.symm) fun e => hvE ?_
      show ω ^ v = v
      calc ω ^ v = ω ^ z := by rw [e]
        _ = v := hvs.symm
    have hz0 : z ≠ 0 := by
      intro e; rw [e, opow_zero] at hvs
      exact absurd (hvs ▸ hBv) (not_lt.2 (one_le_iff_pos.2 (xt_B_E hρE hρ1).pos))
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
      have hpA := (lzImg_sub Ip hWp hZp).1
      have hzA : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZz (Finset.mem_coe.2 (Iz.2.2.1 c hc))
      have heq := lzt_val_fρ h C (t := pw tz) (u := tp) Iz.2.1 Ip.2.1 hzA hpA
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
      have htq0 : val tq (f ρ) = 0 := lzt_zero hρE hρ1 tq Iq.2.1 (by rw [Iq.2.2.2.1, hq0]) (f ρ)
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
      have hle : ω ^ lg v ≤ v' := Ordinal.le_of_dvd h0' hdv
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
    have h1A := (lzImg_sub I1 hW1 hZ1).2
    have h2A := (lzImg_sub I2 hW2 hZ2).2
    have hvA : v ∈ A := hW (by simp)
    rw [val_sm, ← C.add v' h1A _ h2A v hvA hvs.symm]
    exact add_le_add (I1.2.2.2.2.2 A f hW1 hZ1 C) (I2.2.2.2.2.2 A f hW2 hZ2 C)

end Googology.Trans.PoR.InaccPsi.R2.Lz
