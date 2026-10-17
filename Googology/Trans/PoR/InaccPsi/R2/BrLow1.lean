import Googology.Trans.PoR.InaccPsi.R2.BrStep

/-!
# Lower bound, part 1: tools on `T̄^τ` and the fixed codes

Tools for the map `E` (InaccPsi normal forms into `T̄¹`) of the paper proof of Theorem LOW-0
(InaccPsi README, Theorem LOW-0):
* `K`-sets of normalized sums, of terms below `Ωᵢ` (`Ki_nil_of_lt`, `Kst_nil_of_lt`, `Ki_le_of_lt`);
* `β < ϑ̄ⱼ(β)` for `β < Ω_{j+1}` (`thb_gt_arg`), every `β < Ω_{j+1}` is in `dom(ϑ̄ⱼ)` (`dom_of_lt`),
  `ϑ̄ⱼ(0) = Ωⱼ` (`thb_zero`);
* the comparison of `ϑ̄ⱼ`-terms from [W25] Prop 2.15 (`thb_lt_of_I`, `thb_lt_of_II`);
* the level `lvl v` of an ordinal `v < Ω_ω` (the least `n` with `v < Ω_{n+1}`);
* the fixed codes over `τ = 1`: `Omk k = ϑ̄ₖ(0) = Ωₖ`, `Pk k = ϑ̄_{k+1}(Ω_{k+1})`, and
  `Fc x = ϑ̄_{m+1}(Ω_{m+1} + Ω_{m+1} + x)` (`m = lvl x`, `Fc x = 0` for `x = 0`), with their normal
  forms, values and order (`Fc_lt`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {τ : Ordinal.{0}}

/-! ## `K`-sets of normalized sums -/

theorem Ki_plus (τ : Ordinal.{0}) (i : ℕ) : ∀ (s t : Tm), Ki i (plus τ s t) ⊆ Ki i s ++ Ki i t
  | .par c, t => by
    cases t with
    | par d => simp [plus, Ki]
    | th j u => simp only [plus]; exact List.subset_append_right _ _
    | add u v => simp only [plus]; exact List.subset_append_right _ _
  | .th j u, t => by
    simp only [plus]
    split_ifs
    · exact List.subset_append_left _ _
    · simp only [Ki]; exact List.Subset.refl _
    · exact List.subset_append_right _ _
  | .add s r, t => by
    simp only [plus]
    split_ifs
    · exact List.subset_append_left _ _
    · simp only [Ki]
      intro x hx
      simp only [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases List.mem_append.1 (Ki_plus τ i r t hx) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · exact List.subset_append_right _ _

theorem Kst_plus (τ : Ordinal.{0}) (i : ℕ) : ∀ (s t : Tm), Kst i (plus τ s t) ⊆ Kst i s ++ Kst i t
  | .par c, t => by
    cases t with
    | par d => simp [plus, Kst]
    | th j u => simp only [plus]; exact List.subset_append_right _ _
    | add u v => simp only [plus]; exact List.subset_append_right _ _
  | .th j u, t => by
    simp only [plus]
    split_ifs
    · exact List.subset_append_left _ _
    · simp only [Kst]; exact List.Subset.refl _
    · exact List.subset_append_right _ _
  | .add s r, t => by
    simp only [plus]
    split_ifs
    · exact List.subset_append_left _ _
    · simp only [Kst]
      intro x hx
      simp only [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · rcases List.mem_append.1 (Kst_plus τ i r t hx) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · exact List.subset_append_right _ _

theorem ev_plus (hτ : Base τ) {s t : Tm} (hs : NF τ s) (ht : NF τ t) :
    ev τ (plus τ s t) = ev τ s + ev τ t := (plus_spec hτ hs ht).2.1

theorem NF_plus (hτ : Base τ) {s t : Tm} (hs : NF τ s) (ht : NF τ t) : NF τ (plus τ s t) :=
  (plus_spec hτ hs ht).1

/-- A normal term below `Ωᵢ` has no parts of level `≥ i`. -/
theorem Ki_nil_of_lt (hτ : Base τ) {i : ℕ} {t : Tm} (ht : NF τ t) (hlt : ev τ t < OmT τ i) :
    Ki i t = [] := by
  induction ht with
  | cpar _ => rfl
  | @cth j u hu hd _ =>
    have h1 := (NF.th_bounds hτ (NF.cth hu hd)).1
    have hji : j < i := by
      by_contra h; exact absurd (lt_of_lt_of_le hlt (OmT_mono hτ (not_lt.1 h))) (not_lt.2 h1)
    simp [Ki, hji]
  | @cadd j u r h1 _ _ _ _ ih2 =>
    have hb := (NF.th_bounds hτ h1).1
    have hji : j < i := by
      by_contra h
      exact absurd (lt_of_lt_of_le hlt ((OmT_mono hτ (not_lt.1 h)).trans (hb.trans le_self_add)))
        (lt_irrefl _)
    simp only [Ki, List.append_eq_nil_iff]
    exact ⟨by simp [hji], ih2 (lt_of_le_of_lt le_add_self hlt)⟩

theorem Kst_nil_of_lt (hτ : Base τ) {L : ℕ} {t : Tm} (ht : NF τ t) (hlt : ev τ t < OmT τ L) :
    Kst L t = [] := by
  induction ht with
  | cpar _ => rfl
  | @cth j u hu hd _ =>
    have h1 := (NF.th_bounds hτ (NF.cth hu hd)).1
    have hji : j < L := by
      by_contra h; exact absurd (lt_of_lt_of_le hlt (OmT_mono hτ (not_lt.1 h))) (not_lt.2 h1)
    simp [Kst, hji]
  | @cadd j u r h1 _ _ _ _ ih2 =>
    have hb := (NF.th_bounds hτ h1).1
    have hji : j < L := by
      by_contra h
      exact absurd (lt_of_lt_of_le hlt ((OmT_mono hτ (not_lt.1 h)).trans (hb.trans le_self_add)))
        (lt_irrefl _)
    simp only [Kst, List.append_eq_nil_iff]
    exact ⟨by simp [hji], ih2 (lt_of_le_of_lt le_add_self hlt)⟩

/-- Below `Ω_{k+1}`, the level-`k` parts are summands, so at most the value. -/
theorem Ki_le_of_lt (hτ : Base τ) {k : ℕ} {t : Tm} (ht : NF τ t) (hlt : ev τ t < OmT τ (k + 1)) :
    ∀ u ∈ Ki k t, ev τ u ≤ ev τ t := by
  induction ht with
  | cpar _ => intro u hu; simp [Ki] at hu
  | @cth j v hv hd _ =>
    intro u hu
    have h1 := (NF.th_bounds hτ (NF.cth hv hd)).1
    have hjk : j ≤ k := by
      by_contra h
      exact absurd (lt_of_lt_of_le hlt (OmT_mono hτ (Nat.succ_le_of_lt (not_le.1 h)))) (not_lt.2 h1)
    simp only [Ki] at hu
    split_ifs at hu with h2 h3
    · simp at hu
    · simp at hu; subst hu; exact le_rfl
    · omega
  | @cadd j v r h1 h2 _ _ ih1 ih2 =>
    intro u hu
    simp only [Ki, List.mem_append] at hu
    rcases hu with hu | hu
    · exact (ih1 (lt_of_le_of_lt le_self_add hlt) u hu).trans le_self_add
    · exact (ih2 (lt_of_le_of_lt le_add_self hlt) u hu).trans le_add_self

/-! ## `ϑ̄ⱼ` on small arguments -/

theorem dom_of_lt (_hτ : Base τ) {j : ℕ} {β : Ordinal.{0}} (h : β < OmT τ (j + 1)) : Dom τ j β :=
  ⟨h.trans (OmT_succ_lt_Om_omega τ j), Mem.small h⟩

/-- `β < ϑ̄ⱼ(β)` for `β ∈ dom(ϑ̄ⱼ)`, `β < Ω_{j+1}`. -/
theorem thb_gt_arg (hτ : Base τ) {j : ℕ} {β : Ordinal.{0}} (hd : Dom τ j β) (h : β < OmT τ (j + 1)) :
    β < thb τ β j :=
  (thb_good hτ hd).2.2 β (thb_good hτ hd).2.1 h

/-- `ϑ̄ⱼ(0) = Ωⱼ`. -/
theorem thb_zero (hτ : Base τ) (j : ℕ) : thb τ 0 j = OmT τ j := by
  have hd : Dom τ j 0 := dom_of_lt hτ (OmT_succ_pos τ j)
  refine le_antisymm ?_ (OmT_le_thb hτ hd)
  have hgood : Good τ (thb τ) 0 j (OmT τ j) := by
    refine ⟨OmT_lt_succ hτ j, Mem.base (OmT_pos hτ j), fun x hx hxk => ?_⟩
    -- `C̄ⱼ(0, Ωⱼ)` is the closure of `Ωⱼ` under `+`
    have hP : IsPrincipal (· + ·) (OmT τ j) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [OmT_zero]; exact hτ.principal
      · rw [OmT_pos_of_ne hj.ne']; exact Om_isPrincipal (by exact_mod_cast hj.ne')
    have key : ∀ {a : Ordinal.{0}} {i : ℕ} {b y : Ordinal.{0}}, Mem τ (thb τ) a i b y → a = 0 → i = j →
        b = OmT τ j → y < OmT τ j := by
      intro a i b y h
      induction h with
      | base h => intro _ hi _; subst hi; exact h
      | small h => intro _ _ hb; subst hb; exact h
      | add _ _ ihx ihy =>
        intro ha hi hb
        exact hP (ihx ha hi hb) (ihy ha hi hb)
      | th _ hξ _ _ _ _ => intro ha; subst ha; exact absurd hξ (not_lt.2 zero_le)
    exact key hx rfl rfl rfl
  rw [thb_eq]
  exact csInf_le' (Or.inl hgood)

/-- **[W25] Prop 2.15, case (I)**: `α < β` and `α^{*j} < ϑ̄ⱼ(β)` give `ϑ̄ⱼ(α) < ϑ̄ⱼ(β)`. -/
theorem thb_lt_of_I (hτ : Base τ) {j : ℕ} {s t : Tm} (hs : NF τ (th j s)) (ht : NF τ (th j t))
    (h1 : ev τ s < ev τ t) (h2 : Tm.star τ j s < ev τ (th j t)) : ev τ (th j s) < ev τ (th j t) :=
  (W25_prop215 hτ (NF.th_arg hs) (NF.th_arg ht) j (NF.th_dom hs) (NF.th_dom ht)).2 (Or.inl ⟨h1, h2⟩)

/-- **[W25] Prop 2.15, case (II)**: `ϑ̄ⱼ(α) ≤ β^{*j}` gives `ϑ̄ⱼ(α) < ϑ̄ⱼ(β)`. -/
theorem thb_lt_of_II (hτ : Base τ) {j : ℕ} {s t : Tm} (hs : NF τ (th j s)) (ht : NF τ (th j t))
    (h : ev τ (th j s) ≤ Tm.star τ j t) : ev τ (th j s) < ev τ (th j t) :=
  (W25_prop215 hτ (NF.th_arg hs) (NF.th_arg ht) j (NF.th_dom hs) (NF.th_dom ht)).2 (Or.inr h)

/-- `Ki` elements bound the star from below. -/
theorem star_le_of (τ : Ordinal.{0}) {i : ℕ} {t : Tm} {Y : Ordinal.{0}}
    (h : ∀ u ∈ Ki i t, ev τ u < Y) (hY : 0 < Y) : Tm.star τ i t < Y := by
  rcases star_cases (τ := τ) i t with h0 | ⟨u, hu, e⟩
  · rw [h0]; exact hY
  · rw [e]; exact h u hu

/-! ## Levels -/

/-- The level of an ordinal: the least `n` with `v < Ω_{n+1}`. -/
noncomputable def lvl (v : Ordinal.{0}) : ℕ := sInf {n : ℕ | v < Om ((n : Ordinal.{0}) + 1)}

theorem lvl_spec {v : Ordinal.{0}} (hv : v < Om (ω : Ordinal.{0})) :
    v < Om ((lvl v : Ordinal.{0}) + 1) ∧ ∀ n : ℕ, v < Om ((n : Ordinal.{0}) + 1) → lvl v ≤ n := by
  have hne : {n : ℕ | v < Om ((n : Ordinal.{0}) + 1)}.Nonempty := by
    rw [Om_of_ne_zero omega0_ne_zero] at hv
    obtain ⟨b, hb, hvb⟩ := (isNormal_omega.lt_iff_exists_lt isSuccLimit_omega0).1 hv
    obtain ⟨n, rfl⟩ := lt_omega0.1 hb
    refine ⟨n, ?_⟩
    show v < Om ((n : Ordinal.{0}) + 1)
    rw [Om_of_ne_zero (natCast_succ_ne_zero n)]
    exact hvb.trans_le (omega_le_omega.2 (by exact_mod_cast (Nat.le_succ n)))
  exact ⟨Nat.sInf_mem hne, fun n hn => Nat.sInf_le hn⟩

theorem lvl_lt {v : Ordinal.{0}} (hv : v < Om (ω : Ordinal.{0})) :
    v < OmT 1 (lvl v + 1) := by
  rw [OmT_succ]; exact (lvl_spec hv).1

theorem lvl_ge {v : Ordinal.{0}} (hv : v < Om (ω : Ordinal.{0})) (h0 : lvl v ≠ 0) :
    OmT 1 (lvl v) ≤ v := by
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h' : v < Om ((n : Ordinal.{0}) + 1) := by
    rw [hn, OmT_succ] at h; exact h
  have := (lvl_spec hv).2 n h'
  omega

theorem lvl_le_of_lt {v : Ordinal.{0}} {n : ℕ} (h : v < OmT 1 (n + 1)) : lvl v ≤ n := by
  have hv : v < Om (ω : Ordinal.{0}) := h.trans (OmT_succ_lt_Om_omega 1 n)
  rw [OmT_succ] at h
  exact (lvl_spec hv).2 n h

theorem lvl_eq {v : Ordinal.{0}} {n : ℕ} (h1 : OmT 1 n ≤ v) (h2 : v < OmT 1 (n + 1)) (_hn : n ≠ 0) :
    lvl v = n := by
  have hv : v < Om (ω : Ordinal.{0}) := h2.trans (OmT_succ_lt_Om_omega 1 n)
  refine le_antisymm (lvl_le_of_lt h2) ?_
  by_contra hlt
  rw [not_le] at hlt
  have := lvl_lt hv
  exact absurd (lt_of_lt_of_le this (OmT_mono base_one (Nat.succ_le_of_lt hlt))) (not_lt.2 h1)

theorem lvl_mono {v w : Ordinal.{0}} (hw : w < Om (ω : Ordinal.{0})) (h : v ≤ w) : lvl v ≤ lvl w :=
  lvl_le_of_lt (lt_of_le_of_lt h (lvl_lt hw))

/-! ## The fixed codes over `τ = 1` -/

/-- `Omk k = ϑ̄ₖ(0) = Ωₖ`. -/
def Omk (k : ℕ) : Tm := th k (par 0)

/-- `Pk k = ϑ̄_{k+1}(Ω_{k+1})`. -/
def Pk (k : ℕ) : Tm := th (k + 1) (Omk (k + 1))

open Classical in
/-- `Fc x = ϑ̄_{m+1}(Ω_{m+1} + Ω_{m+1} + x)`, `m = lvl x` (and `Fc x = 0` for `x = 0`). -/
noncomputable def Fc (x : Tm) : Tm :=
  if ev 1 x = 0 then par 0 else
    th (lvl (ev 1 x) + 1) (plus 1 (Omk (lvl (ev 1 x) + 1)) (plus 1 (Omk (lvl (ev 1 x) + 1)) x))

theorem NF_par0 : NF 1 (par 0) := NF.cpar zero_lt_one

theorem NF_Omk (k : ℕ) : NF 1 (Omk k) :=
  NF.cth NF_par0 (dom_of_lt base_one (OmT_succ_pos 1 k))

theorem ev_Omk (k : ℕ) : ev 1 (Omk k) = OmT 1 k := thb_zero base_one k

theorem NF_Pk (k : ℕ) : NF 1 (Pk k) := by
  refine NF.cth (NF_Omk (k + 1)) (dom_of_lt base_one ?_)
  rw [ev_Omk]; exact OmT_lt_succ base_one _

theorem ev_Pk_bounds (k : ℕ) : OmT 1 (k + 1) < ev 1 (Pk k) ∧ ev 1 (Pk k) < OmT 1 (k + 2) := by
  have hd := NF.th_dom (NF_Pk k)
  have hlt : ev 1 (Omk (k + 1)) < OmT 1 (k + 1 + 1) := by rw [ev_Omk]; exact OmT_lt_succ base_one _
  refine ⟨?_, (NF.th_bounds base_one (NF_Pk k)).2⟩
  have := thb_gt_arg base_one hd hlt
  show OmT 1 (k + 1) < thb 1 (ev 1 (Omk (k + 1))) (k + 1)
  rw [ev_Omk] at this ⊢; exact this

theorem Pk_principal (k : ℕ) : IsPrincipal (· + ·) (ev 1 (Pk k)) := NF.th_principal base_one (NF_Pk k)

/-- The argument of `Fc x`. -/
noncomputable def Farg (m : ℕ) (x : Tm) : Tm := plus 1 (Omk (m + 1)) (plus 1 (Omk (m + 1)) x)

theorem ev_Farg {m : ℕ} {x : Tm} (hx : NF 1 x) :
    ev 1 (Farg m x) = OmT 1 (m + 1) + OmT 1 (m + 1) + ev 1 x := by
  unfold Farg
  rw [ev_plus base_one (NF_Omk _) (NF_plus base_one (NF_Omk _) hx), ev_plus base_one (NF_Omk _) hx,
    ev_Omk, add_assoc]

theorem NF_Farg {m : ℕ} {x : Tm} (hx : NF 1 x) : NF 1 (Farg m x) :=
  NF_plus base_one (NF_Omk _) (NF_plus base_one (NF_Omk _) hx)

theorem Farg_lt {m : ℕ} {x : Tm} (hx : NF 1 x) (hxl : ev 1 x < OmT 1 (m + 1)) :
    ev 1 (Farg m x) < OmT 1 (m + 1 + 1) := by
  rw [ev_Farg hx]
  have hP := OmT_succ_principal 1 (m + 1)
  have h1 := OmT_lt_succ base_one (m + 1)
  exact hP (hP h1 h1) (hxl.trans h1)

theorem Fc_zero {x : Tm} (h : ev 1 x = 0) : Fc x = par 0 := by unfold Fc; rw [if_pos h]

theorem Fc_pos {x : Tm} (h : ev 1 x ≠ 0) : Fc x = th (lvl (ev 1 x) + 1) (Farg (lvl (ev 1 x)) x) := by
  unfold Fc Farg; rw [if_neg h]

theorem NF_Fc {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0})) : NF 1 (Fc x) := by
  by_cases h0 : ev 1 x = 0
  · rw [Fc_zero h0]; exact NF_par0
  · rw [Fc_pos h0]
    exact NF.cth (NF_Farg hx) (dom_of_lt base_one (Farg_lt hx (lvl_lt hxω)))

theorem Farg_ge {m : ℕ} {x : Tm} (hx : NF 1 x) :
    OmT 1 (m + 1) < ev 1 (Farg m x) := by
  rw [ev_Farg hx]
  have hpos : 0 < OmT 1 (m + 1) := OmT_succ_pos 1 m
  calc OmT 1 (m + 1) < OmT 1 (m + 1) + OmT 1 (m + 1) := lt_add_of_pos_right _ hpos
    _ ≤ _ := le_self_add

theorem Ki_Omk_of_gt {k j : ℕ} (h : k < j) : Ki k (Omk j) = [] := by
  simp [Omk, Ki, show ¬ j < k by omega, show j ≠ k by omega]

theorem Ki_Omk_self (k : ℕ) : Ki k (Omk k) = [Omk k] := by simp [Omk, Ki]

theorem Kst_Omk {L j : ℕ} (h : L ≤ j) : Kst L (Omk j) = [(j, par 0)] := by
  simp [Omk, Kst, show ¬ j < L by omega]

theorem Kst_Omk_lt {L j : ℕ} (h : j < L) : Kst L (Omk j) = [] := by simp [Omk, Kst, h]

/-- The level-`(m+1)` star of the argument of `Fc x` is `Ω_{m+1}`. -/
theorem star_Farg {m : ℕ} {x : Tm} (hx : NF 1 x) (hxl : ev 1 x < OmT 1 (m + 1)) :
    ∀ u ∈ Ki (m + 1) (Farg m x), ev 1 u ≤ OmT 1 (m + 1) := by
  intro u hu
  unfold Farg at hu
  have h1 := Ki_plus 1 (m + 1) _ _ hu
  rw [Ki_Omk_self] at h1
  rcases List.mem_append.1 h1 with h | h
  · simp at h; subst h; rw [ev_Omk]
  · have h2 := Ki_plus 1 (m + 1) _ _ h
    rw [Ki_Omk_self, Ki_nil_of_lt base_one hx hxl] at h2
    simp at h2; subst h2; rw [ev_Omk]

theorem ev_Fc_pos {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0})) (h0 : ev 1 x ≠ 0) :
    ev 1 (Farg (lvl (ev 1 x)) x) < ev 1 (Fc x) ∧ OmT 1 (lvl (ev 1 x) + 1) ≤ ev 1 (Fc x) ∧
      ev 1 (Fc x) < OmT 1 (lvl (ev 1 x) + 2) := by
  have hn := NF_Fc hx hxω
  rw [Fc_pos h0] at hn ⊢
  have hb := NF.th_bounds base_one hn
  refine ⟨thb_gt_arg base_one (NF.th_dom hn) (Farg_lt hx (lvl_lt hxω)), hb.1, hb.2⟩

theorem Fc_principal {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0})) (h0 : ev 1 x ≠ 0) :
    IsPrincipal (· + ·) (ev 1 (Fc x)) := by
  have hn := NF_Fc hx hxω
  rw [Fc_pos h0] at hn ⊢
  exact NF.th_principal base_one hn

/-- **`F` is strictly increasing.** -/
theorem Fc_lt {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hyω : ev 1 y < Om (ω : Ordinal.{0}))
    (hxy : ev 1 x < ev 1 y) : ev 1 (Fc x) < ev 1 (Fc y) := by
  have hxω := hxy.trans hyω
  have hy0 : ev 1 y ≠ 0 := (lt_of_le_of_lt zero_le hxy).ne'
  obtain ⟨hy1, hy2, hy3⟩ := ev_Fc_pos hy hyω hy0
  by_cases hx0 : ev 1 x = 0
  · rw [Fc_zero hx0]
    exact lt_of_lt_of_le (OmT_succ_pos 1 _) hy2
  obtain ⟨hx1, hx2, hx3⟩ := ev_Fc_pos hx hxω hx0
  have hm : lvl (ev 1 x) ≤ lvl (ev 1 y) := lvl_mono hyω hxy.le
  rcases lt_or_eq_of_le hm with hlt | heq
  · exact lt_of_lt_of_le hx3 ((OmT_mono base_one (by omega)).trans hy2)
  · have hnx := NF_Fc hx hxω
    have hny := NF_Fc hy hyω
    rw [Fc_pos hx0] at hnx ⊢
    rw [Fc_pos hy0] at hny ⊢
    rw [Fc_pos hy0] at hy1
    rw [heq] at hnx ⊢
    refine thb_lt_of_I base_one hnx hny ?_ ?_
    · rw [ev_Farg hx, ev_Farg hy]; exact add_lt_add_right hxy _
    · refine star_le_of 1 (fun u hu => ?_) (thb_pos base_one (NF.th_dom hny))
      have hxl : ev 1 x < OmT 1 (lvl (ev 1 y) + 1) := heq ▸ lvl_lt hxω
      exact lt_of_le_of_lt (star_Farg hx hxl u hu)
        ((Farg_ge hy).trans (thb_gt_arg base_one (NF.th_dom hny) (Farg_lt hy (lvl_lt hyω))))

/-- The `K*`-elements of `Fc x` above level `L` (for `x ≠ 0`). -/
theorem Kst_Fc {L : ℕ} {x : Tm} (hx0 : ev 1 x ≠ 0) :
    Kst L (Fc x) ⊆ (if lvl (ev 1 x) + 1 < L then [] else
      (lvl (ev 1 x) + 1, Farg (lvl (ev 1 x)) x) :: (Kst L (Omk (lvl (ev 1 x) + 1)) ++
        (Kst L (Omk (lvl (ev 1 x) + 1)) ++ Kst L x))) := by
  rw [Fc_pos hx0]
  simp only [Kst]
  split_ifs with h
  · exact List.Subset.refl _
  · intro p hp
    rcases List.mem_cons.1 hp with hp | hp
    · exact hp ▸ List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      unfold Farg at hp
      have h1 := Kst_plus 1 L _ _ hp
      rcases List.mem_append.1 h1 with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (Kst_plus 1 L _ _ h1)

/-- The level-`k` parts of `Fc x`. -/
theorem Ki_Fc {k : ℕ} {x : Tm} (hx0 : ev 1 x ≠ 0) :
    Ki k (Fc x) ⊆ (if lvl (ev 1 x) + 1 < k then [] else if lvl (ev 1 x) + 1 = k then [Fc x] else
      Ki k x) := by
  have e := Fc_pos hx0
  intro u hu
  rw [e] at hu
  simp only [Ki] at hu
  split_ifs at hu ⊢ with h1 h2
  · exact hu
  · rw [e]; exact hu
  · unfold Farg at hu
    have h3 := Ki_plus 1 k _ _ hu
    rw [Ki_Omk_of_gt (by omega)] at h3
    have h4 := Ki_plus 1 k _ _ (List.mem_append.1 h3 |>.resolve_left (by simp))
    rw [Ki_Omk_of_gt (by omega)] at h4
    simpa using h4

theorem Ki_Pk (k : ℕ) : Ki k (Pk k) = [] := by
  simp [Pk, Omk, Ki]

theorem Kst_Pk {L k : ℕ} (h : L ≤ k + 1) : Kst L (Pk k) = [(k + 1, Omk (k + 1)), (k + 1, par 0)] := by
  simp [Pk, Omk, Kst, show ¬ k + 1 < L by omega]

end Googology.Trans.PoR.InaccPsi.R2.Br
