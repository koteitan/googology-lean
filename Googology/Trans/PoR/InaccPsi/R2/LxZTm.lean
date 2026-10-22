import Googology.Trans.PoR.InaccPsi.R2.LxZE

/-!
# The terms below `e^K_x(x) = ϑˣ(Ω₁ + E_K(x) + x)`: exponent terms over `K`, the atoms `e_c`, sums, `ω`-powers

`LxZTm K` (for a layer `K` with `LxZK K`, `R2.LxZE`): a term `ex t` of `LxTm K` (values below `ε_{E_K(x)+1}`,
`R2.LxTm`), an atom `ep c` (value `e_c(x)`, `c` a constant), a sum `sm a b`, a power `pw a`.  This is `Lz.LzTm`
with the atom `B(x)` replaced by the top of any such `K`.  For every base `x`:

* `lxzt_lt_top` (**every value is below `e_x(x)`**), `lxzt_pi` (**Lemma EXACT**), `lxzt_uni_le`, `lxzt_uni_lt`,
  `lxzt_uni_eq`, `lxzt_zero`, `lxt_small`, `lxzt_small` (a term is constant or has value `≥ x`);
* `lxzt_rep` (**representation below `e_ρ(ρ)`** at every restart: an `ε`-number in `[ε_{E_K(ρ)+1}, e_ρ(ρ))` is an
  atom, `lxZE_enum`);
* `lxzt_img` (**Lemma IMG below `e_ρ(ρ)`**: below `ε_{E_K(ρ)+1}` from `lxt_img`, at an atom from `lxZE_imgAll`, a
  power by one atom step of `R₁⁺` (`Ly.lyStep2`, [W07b] Theorem 2.2), a sum by a sum).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly

/-- **The terms below `e_x(x)`**: exponent terms over `K`, the atoms `e_c`, sums and `ω`-powers. -/
inductive LxZTm (K : XtLay) : Type 1
  | ex : LxTm K → LxZTm K
  | ep : Ordinal.{0} → LxZTm K
  | sm : LxZTm K → LxZTm K → LxZTm K
  | pw : LxZTm K → LxZTm K

namespace LxZTm

variable {K : XtLay}

/-- The value at the base `x`. -/
noncomputable def val : LxZTm K → Ordinal.{0} → Ordinal.{0}
  | ex t, x => t.val x
  | ep c, x => lxZE K x c
  | sm a b, x => val a x + val b x
  | pw a, x => ω ^ val a x

/-- All constants below `s`. -/
def CBt : LxZTm K → Ordinal.{0} → Prop
  | ex t, s => t.CBt s
  | ep c, s => c < s
  | sm a b, s => CBt a s ∧ CBt b s
  | pw a, s => CBt a s

/-- The constants. -/
def cs : LxZTm K → List Ordinal.{0}
  | ex t => t.cs
  | ep c => [c]
  | sm a b => cs a ++ cs b
  | pw a => cs a

@[simp] theorem val_ex (t : LxTm K) (x : Ordinal.{0}) : val (ex t) x = t.val x := rfl
@[simp] theorem val_ep (c x : Ordinal.{0}) : val (ep c : LxZTm K) x = lxZE K x c := rfl
@[simp] theorem val_sm (a b : LxZTm K) (x : Ordinal.{0}) : val (sm a b) x = val a x + val b x := rfl
@[simp] theorem val_pw (a : LxZTm K) (x : Ordinal.{0}) : val (pw a) x = ω ^ val a x := rfl

theorem cbt_iff : ∀ (t : LxZTm K) (s s' : Ordinal.{0}), CBt t s → (∀ c ∈ cs t, c < s') → CBt t s'
  | ex t, s, s', h, h' => LxTm.cbt_iff t s s' h h'
  | ep c, _, _, _, h' => h' c (by simp [cs])
  | sm a b, s, s', h, h' => ⟨cbt_iff a s s' h.1 (fun c hc => h' c (by simp [cs, hc])),
      cbt_iff b s s' h.2 (fun c hc => h' c (by simp [cs, hc]))⟩
  | pw a, s, s', h, h' => cbt_iff a s s' h h'

theorem cbt_cst : ∀ (t : LxZTm K) (s : Ordinal.{0}), CBt t s → ∀ c ∈ cs t, c < s
  | ex t, s, h, c, hc => LxTm.cbt_cst t s h c hc
  | ep _, _, h, c, hc => by simp [cs] at hc; subst hc; exact h
  | sm a b, s, h, c, hc => by
    simp only [cs, List.mem_append] at hc
    rcases hc with hc | hc
    · exact cbt_cst a s h.1 c hc
    · exact cbt_cst b s h.2 c hc
  | pw a, s, h, c, hc => cbt_cst a s h c hc

theorem cbt_mono {t : LxZTm K} {s s' : Ordinal.{0}} (h : CBt t s) (hs : s ≤ s') : CBt t s' :=
  cbt_iff t s s' h (fun c hc => (cbt_cst t s h c hc).trans_le hs)

end LxZTm

open LxZTm

variable {K : XtLay}

/-- **A term of `LxTm K` is constant or has value at least the base.** -/
theorem lxt_small (hK : LxEK K) : ∀ t : LxTm K,
    (∀ x y, t.val x = t.val y) ∨ (∀ x, InE x → x < Om1 → t.CBt x → x ≤ t.val x)
  | LxTm.bs s => K.sys.small s
  | LxTm.tp => Or.inr fun x hx hx1 _ => (lx_E_gt hK hx hx1).le
  | LxTm.sm a b => by
    rcases lxt_small hK a with ha | ha
    · rcases lxt_small hK b with hb | hb
      · exact Or.inl fun x y => by rw [LxTm.val_sm, LxTm.val_sm, ha x y, hb x y]
      · exact Or.inr fun x hx hx1 h => (hb x hx hx1 h.2).trans le_add_self
    · exact Or.inr fun x hx hx1 h => (ha x hx hx1 h.1).trans le_self_add
  | LxTm.pw a => by
    rcases lxt_small hK a with ha | ha
    · exact Or.inl fun x y => by rw [LxTm.val_pw, LxTm.val_pw, ha x y]
    · exact Or.inr fun x hx hx1 h => (ha x hx hx1 h).trans (right_le_opow _ one_lt_omega0)

section Base

variable (hZ : LxZK K)
include hZ

theorem lxz_e0_lt_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : eN (K.E x) < lxZE K x x := by
  rw [← lxZE_zero hZ hx hx1]; exact lxZE_strict hZ hx hx1 hx.pos le_rfl

/-- **Every value is below `e_x(x)`.** -/
theorem lxzt_lt_top {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LxZTm K, CBt t x → val t x < lxZE K x x
  | ex t, h => (lxt_lt_eN hZ.ek hx hx1 t h).trans (lxz_e0_lt_top hZ hx hx1)
  | ep _, h => lxZE_strict hZ hx hx1 h le_rfl
  | sm a b, h => (inE_indec (lxZE_facts hZ hx hx1 le_rfl).2.2.2.2.2.1).add_lt (lxzt_lt_top hx hx1 a h.1)
      (lxzt_lt_top hx hx1 b h.2)
  | pw a, h => (lxZE_facts hZ hx hx1 le_rfl).2.2.2.2.2.1.opow_lt (lxzt_lt_top hx hx1 a h)

theorem lxzTop_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : lxZE K x x < Om1 :=
  (lxZE_facts hZ hx hx1 le_rfl).2.2.2.2.1

theorem lxzt_lt_Om1 {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (t : LxZTm K) (h : CBt t x) :
    val t x < Om1 :=
  (lxzt_lt_top hZ hx hx1 t h).trans (lxzTop_lt_Om1 hZ hx hx1)

theorem lxzTop_lt_ups {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) :
    lxZE K x x < u :=
  lxZE_lt_ups hZ hx hx1 le_rfl hxu hu.2

/-- **Lemma EXACT for `LxZTm K`.** -/
theorem lxzt_pi {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ t : LxZTm K, CBt t σ → val t ρ ∈ TB ρ σ ∧ pi σ ρ (val t ρ) = val t σ
  | ex t, h => lxt_pi hZ.ek hσ hρ hB t h
  | ep _, h => lxZE_pi hZ hσ hρ hB h
  | sm a b, h => by
    obtain ⟨h1, h2⟩ := lxzt_pi hσ hρ hB a h.1
    obtain ⟨h3, h4⟩ := lxzt_pi hσ hρ hB b h.2
    obtain ⟨h5, h6⟩ := pi_add hB h1 h3
    simp only [val_sm]
    exact ⟨h5, by rw [h6, h2, h4]⟩
  | pw a, h => by
    obtain ⟨h1, h2⟩ := lxzt_pi hσ hρ hB a h
    have hb := lxzt_lt_Om1 hZ hB.2.1 hB.2.2.2 a (cbt_mono h hB.2.2.1.le)
    obtain ⟨h3, h4⟩ := pi_opowZ hσ hρ hB h1 hb
    simp only [val_pw]
    exact ⟨h3, by rw [h4, h2]⟩

theorem lxzt_uni_le {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LxZTm K}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ ≤ val u ρ ↔ val t σ ≤ val u σ := by
  obtain ⟨h1, h2⟩ := lxzt_pi hZ hσ hρ hB t ht
  obtain ⟨h3, h4⟩ := lxzt_pi hZ hσ hρ hB u hu
  rw [← h2, ← h4]
  exact ((pi_bijOn hB).2.le_iff_le h1 h3).symm

theorem lxzt_uni_lt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LxZTm K}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ < val u ρ ↔ val t σ < val u σ := by
  rw [← not_le, ← not_le, lxzt_uni_le hZ hσ hρ hB hu ht]

theorem lxzt_uni_eq {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t u : LxZTm K}
    (ht : CBt t σ) (hu : CBt u σ) : val t ρ = val u ρ ↔ val t σ = val u σ := by
  rw [le_antisymm_iff, le_antisymm_iff, lxzt_uni_le hZ hσ hρ hB ht hu, lxzt_uni_le hZ hσ hρ hB hu ht]

/-- **A value `0` is the value `0` everywhere.** -/
theorem lxzt_zero {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    ∀ t : LxZTm K, CBt t x → val t x = 0 → ∀ y, val t y = 0
  | ex t, h, h0 => lxt_zero hZ.ek hx hx1 t h h0
  | ep _, h, h0 => absurd h0 (lxZE_facts hZ hx hx1 h.le).2.2.2.2.2.1.pos.ne'
  | sm a b, h, h0 => by
    have := add_eq_zero_iff.1 h0
    intro y
    rw [val_sm, lxzt_zero hx hx1 a h.1 this.1 y, lxzt_zero hx hx1 b h.2 this.2 y, add_zero]
  | pw a, _, h0 => absurd h0 (opow_pos _ omega0_pos).ne'

/-- **A term is constant or has value at least the base.** -/
theorem lxzt_small : ∀ t : LxZTm K,
    (∀ x y, val t x = val t y) ∨ (∀ x, InE x → x < Om1 → CBt t x → x ≤ val t x)
  | ex t => lxt_small hZ.ek t
  | ep _ => Or.inr fun x hx hx1 h => (lxZE_facts hZ hx hx1 h.le).2.2.2.1.le
  | sm a b => by
    rcases lxzt_small a with ha | ha
    · rcases lxzt_small b with hb | hb
      · exact Or.inl fun x y => by rw [val_sm, val_sm, ha x y, hb x y]
      · exact Or.inr fun x hx hx1 h => (hb x hx hx1 h.2).trans le_add_self
    · exact Or.inr fun x hx hx1 h => (ha x hx hx1 h.1).trans le_self_add
  | pw a => by
    rcases lxzt_small a with ha | ha
    · exact Or.inl fun x y => by rw [val_pw, val_pw, ha x y]
    · exact Or.inr fun x hx hx1 h => (ha x hx hx1 h).trans (right_le_opow _ one_lt_omega0)

/-- **Representation below `e_ρ(ρ)`.** -/
theorem lxzt_rep {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) (hr : LxRep K ρ) :
    ∀ v, v < lxZE K ρ ρ → ∃ t : LxZTm K, CBt t ρ ∧ val t ρ = v := by
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  rcases lt_or_ge v (eN (K.E ρ)) with h0 | h0
  · obtain ⟨t, ht, htv⟩ := lxt_rep hZ.ek hρ hρ1 hr v h0
    exact ⟨ex t, ht, htv⟩
  have hBv : K.E ρ < v := (lt_eN _).trans_le h0
  by_cases hvE : InE v
  · obtain ⟨c, hc, rfl⟩ := lxZE_enum hZ hρ hρ1 le_rfl hvE hBv hv
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

end Base

/-! ## Lemma IMG below `e_ρ(ρ)` -/

variable {ρ τ δ : Ordinal.{0}}

/-- **The IMG statement for one value** `v` with a term `t` of `LxZTm K`. -/
def LxZImg (K : XtLay) (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : LxZTm K) : Prop :=
  WZ ρ δ W Z ∧ CBt t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ val t ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      val t (f ρ) ≤ f v

theorem lxzt_cbt_img {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {t : LxZTm K}
    (ht : CBt t ρ) (hA : ∀ c ∈ cs t, c ∈ A) : CBt t (f ρ) :=
  cbt_iff t ρ (f ρ) ht (fun c hc => C.above c (hA c hc) (cbt_cst t ρ ht c hc))

theorem lxzt_val_fρ (hZ : LxZK K) (h : RstK ρ τ δ) {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (C : ImgCtx ρ A f) {t u : LxZTm K} (ht : CBt t ρ) (hu : CBt u ρ) (htA : ∀ c ∈ cs t, c ∈ A)
    (huA : ∀ c ∈ cs u, c ∈ A) (htu : val t ρ = val u ρ) : val t (f ρ) = val u (f ρ) :=
  (lxzt_uni_eq hZ C.ups h.ρU (h.img_bases C) (lxzt_cbt_img C ht htA) (lxzt_cbt_img C hu huA)).1 htu

theorem lxzImg_sub {v : Ordinal.{0}} {W Z : Finset Ordinal.{0}} {t : LxZTm K} (hI : LxZImg K ρ δ v W Z t)
    {A : Set Ordinal.{0}} (hW : ↑W ⊆ A) (hZ : ↑Z ⊆ A) : (∀ c ∈ cs t, c ∈ A) ∧ v ∈ A :=
  ⟨fun c hc => hZ (Finset.mem_coe.2 (hI.2.2.1 c hc)), mem_A hI.2.2.2.2.1 hW hZ⟩

/-- **Lemma IMG below `e_ρ(ρ)`.** -/
theorem lxzt_img (hZ : LxZK K) (h : RstK ρ τ δ) (hb : LxBase K ρ δ) :
    ∀ v, v < lxZE K ρ ρ → ∃ W Z t, LxZImg K ρ δ v W Z t := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρB : ρ < K.E ρ := lx_E_gt hZ.ek hρE hρ1
  have heδ : lxZE K ρ ρ < δ := LxZW.lxZE_lt_δ hZ h le_rfl
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hvδ : v < δ := hv.trans heδ
  rcases lt_or_ge v (eN (K.E ρ)) with h0 | h0
  · obtain ⟨W, Z, s, hw, hc, hcs, hvs, hm, hI⟩ := lxt_img hZ.ek h hb v h0
    exact ⟨W, Z, ex s, hw, hc, hcs, hvs, hm, hI⟩
  have hBv : K.E ρ < v := (lt_eN _).trans_le h0
  by_cases hvE : InE v
  · obtain ⟨c, hc, rfl⟩ := lxZE_enum hZ hρE hρ1 le_rfl hvE hBv hv
    obtain ⟨W, Z, hw, heW, hcZ, hI⟩ := LxZW.lxZE_imgAll hZ h c hc
    exact ⟨W, Z, ep c, hw, hc, by simp [cs, hcZ], rfl, Finset.mem_union_left _ heW, hI⟩
  have hv0 : v ≠ 0 := (lt_of_le_of_lt zero_le hBv).ne'
  have hρv : ρ < v := hρB.trans hBv
  obtain ⟨v', hvs, hdv, hv'v⟩ := lg_split hv0
  rcases eq_or_ne v' 0 with h0' | h0'
  · rw [h0', zero_add] at hvs
    set z := lg v with hz
    have hzv : z < v := by
      have hz' : z ≤ ω ^ z := right_le_opow _ one_lt_omega0
      refine lt_of_le_of_ne (hz'.trans_eq hvs.symm) fun e => hvE ?_
      show ω ^ v = v
      calc ω ^ v = ω ^ z := by rw [e]
        _ = v := hvs.symm
    have hz0 : z ≠ 0 := by
      intro e; rw [e, opow_zero] at hvs
      exact absurd (hvs ▸ hBv) (not_lt.2 (one_le_iff_pos.2 (hZ.ek ρ hρE hρ1).pos))
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
      intro A f hW hZ' C
      have hWq : ↑Wq ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZq : ↑Zq ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
      have hWp : ↑Wp ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
      have hZp : ↑Zp ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
      have hZz : ↑Zz ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
      refine ⟨Iq.2.2.2.2.2 A f hWq hZq C, fun e1 he1 => ?_⟩
      have hpA := (lxzImg_sub Ip hWp hZp).1
      have hzA : ∀ c ∈ cs tz, c ∈ A := fun c hc => hZz (Finset.mem_coe.2 (Iz.2.2.1 c hc))
      have heq := lxzt_val_fρ hZ h C (t := pw tz) (u := tp) Iz.2.1 Ip.2.1 hzA hpA
        (by rw [val_pw, Iz.2.2.2.1, Ip.2.2.2.1])
      have hle := Ip.2.2.2.2.2 A f hWp hZp C
      rw [← heq, val_pw, he1] at hle
      exact (opow_le_opow_iff_right one_lt_omega0).1 hle
    rcases eq_or_ne q 0 with hq0 | hq0
    · have hw : WZ ρ δ (insert v ((Wq ∪ Wp) ∪ Wz)) ((Zq ∪ Zp) ∪ Zz) :=
        hw0.insW hρv.le hvδ (Or.inl (hvs ▸ indec_opow _))
      refine ⟨_, _, t, hw, hcbT, hcsT, htv, by simp, fun A f hW hZ' C => ?_⟩
      have hW0 : ↑((Wq ∪ Wp) ∪ Wz) ⊆ A := fun x hx =>
        hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
      obtain ⟨hqf, hzf⟩ := hcom A f hW0 hZ' C
      have hvA : v ∈ A := hW (by simp)
      have hPA : ω ^ z' ∈ A := mem_A hPW0 hW0 hZ'
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec v hvA (hvs ▸ indec_opow _))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      have h2 : f (ω ^ z') < f v := C.mono hPA hvA hPv
      rw [hc, he1] at h2
      have h3 : e1 < c := (opow_lt_opow_iff_right one_lt_omega0).1 h2
      have htq0 : val tq (f ρ) = 0 := lxzt_zero hZ hρE hρ1 tq Iq.2.1 (by rw [Iq.2.2.2.1, hq0]) (f ρ)
      rw [hc, ht, val_pw, val_sm, val_pw, htq0, opow_zero]
      exact opow_le_opow_right omega0_pos ((add_le_add (hzf e1 he1) le_rfl).trans (Order.add_one_le_of_lt h3))
    · have hNe : v = ω ^ (z' + ω ^ q) := by rw [hvs, hzs]
      obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ := lyStep2 h (hNe ▸ hρv) (pos_iff_ne_zero.2 hq0)
        (hNe ▸ hqv) (hNe ▸ hvδ) hw0 hPW0 hqW0
      refine ⟨W, Z, t, hw, hcbT, fun c hc => hZZ (hcsT c hc), htv, Finset.mem_union_left _ (hNe ▸ hNW),
        fun A f hW hZ' C => ?_⟩
      obtain ⟨hqf, hzf⟩ := hcom A f (fun x hx => hW (hWW (Finset.mem_coe.1 hx)))
        (fun x hx => hZ' (hZZ (Finset.mem_coe.1 hx))) C
      obtain ⟨a, ha, -, hnext⟩ := hI A f hW hZ' C
      have hPA : ω ^ z' ∈ A := by
        rcases Finset.mem_union.1 hPW0 with h' | h'
        · exact hW (Finset.mem_coe.2 (hWW h'))
        · exact hZ' (Finset.mem_coe.2 (hZZ h'))
      obtain ⟨e1, he1⟩ := indec_eq_opow (C.indec _ hPA (indec_opow _))
      rw [hNe, ha, ht, val_pw, val_sm, val_pw]
      exact opow_le_opow_right omega0_pos
        ((add_le_add (hzf e1 he1) (opow_le_opow_right omega0_pos hqf)).trans (hnext e1 he1))
  · have hwv : ω ^ lg v < v := by
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
      by simp, fun A f hW hZ' C => ?_⟩
    · simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_union_left _ (I1.2.2.1 c hc)
      · exact Finset.mem_union_right _ (I2.2.2.1 c hc)
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
    have hW2 : ↑W2 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ2 : ↑Z2 ⊆ A := fun x hx => hZ' (by simp [Finset.mem_coe.1 hx])
    have h1A := (lxzImg_sub I1 hW1 hZ1).2
    have h2A := (lxzImg_sub I2 hW2 hZ2).2
    have hvA : v ∈ A := hW (by simp)
    rw [val_sm, ← C.add v' h1A _ h2A v hvA hvs.symm]
    exact add_le_add (I1.2.2.2.2.2 A f hW1 hZ1 C) (I2.2.2.2.2.2 A f hW2 hZ2 C)

end Googology.Trans.PoR.InaccPsi.R2.Lx
