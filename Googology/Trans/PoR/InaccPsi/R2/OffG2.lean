import Googology.Trans.PoR.InaccPsi.R2.OffG

/-!
# Theorem BLK^O past `Λ_Γ`: the `Γ`-points and the first fixed point of their enumeration

A `Γ`-point is a `λ > 0` with `V_γ(λ) = λ` for every `γ < λ` (`IsGP`; `Λ_Γ` is the least one).  They
form a closed unbounded class; `GG` enumerates `{0} ∪ Γ-points` (`GG 0 = 0`, `GG 1 = Λ_Γ`), and
`Φ_Γ = PhiG` is the least `α ≥ 1` with `GG α = α`.

**The offsets below `Φ_Γ`** (the project's Theorem OFF-V and its continuation to the next layer, the
project's Theorem LAYERS for this layer): at a `Γ`-point `λ = GG(α)`, `O(λ) = ρ·ρ + logend(α)` (`ρ = λ`); at any
other restart index the formula of Theorem OFF-V (`c(λ)` at level `0`, `ρ·γ + logend(α)` at
`λ = V_γ(α)` of level `γ ≥ 1`; the level is `< λ` here).  The terms are `x·γ + e` and `x·x + e`.

* `IsGP`, `isGP_sup`, `exists_GP_above`, `GG` (`GG_normal`, `GG_zero`, `GG_one`, `GG_lt_Om1`),
  `PhiG` (`PhiG_fp`, `lt_GG`, `PhiG_lt_Om1`), `invGG`;
* `offG2`; `topInG2`, `targets_G2`, `targetsGG`, `rsInG2`, `specG2`;
* `blkG2` (**Theorem BLK^O below `Φ_Γ`**), `reach_GG` (`lh(GG(α)) = δ + GG(α)² + logend(α)`),
  `reach_VG2` (OFF-V for every point of level `γ ≥ 1` below `Φ_Γ` that is not a `Γ`-point),
  `coreG2`, `LamG_lt_PhiG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## `Γ`-points -/

/-- `λ` is a `Γ`-point: `λ > 0` and `V_γ(λ) = λ` for every `γ < λ`. -/
def IsGP (l : Ordinal.{0}) : Prop := 0 < l ∧ ∀ g < l, VG g l = l

/-- `{0} ∪ Γ-points`. -/
def GSet : Set Ordinal.{0} := {l | l = 0 ∨ IsGP l}

theorem isGP_sup : ∀ t ⊆ GSet, t.Nonempty → BddAbove t → sSup t ∈ GSet := by
  intro t ht hne hbdd
  set s := sSup t with hs
  rcases eq_or_ne s 0 with h0 | h0
  · exact Or.inl h0
  by_cases hst : s ∈ t
  · exact ht hst
  refine Or.inr ⟨pos_iff_ne_zero.2 h0, fun g hg => ?_⟩
  set t' := {x | x ∈ t ∧ g < x} with ht'
  obtain ⟨x0, hx0t, hgx0⟩ := (lt_csSup_iff hbdd hne).1 hg
  have hne' : t'.Nonempty := ⟨x0, hx0t, hgx0⟩
  have hbdd' : BddAbove t' := hbdd.mono (fun x hx => hx.1)
  have hss : sSup t' = s := by
    refine le_antisymm (csSup_le_csSup hbdd hne' (fun x hx => hx.1)) (csSup_le hne fun x hx => ?_)
    rcases le_or_gt x g with hxg | hgx
    · exact (hxg.trans hgx0.le).trans (le_csSup hbdd' ⟨hx0t, hgx0⟩)
    · exact le_csSup hbdd' ⟨hx, hgx⟩
  have hfix : ∀ x ∈ t', VG g x = x := by
    rintro x ⟨hxt, hgx⟩
    rcases ht hxt with h | h
    · exact absurd (h ▸ hgx) (not_lt.2 zero_le)
    · exact h.2 g hgx
  rw [← hss, (VG_normal g).map_sSup hne' hbdd']
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [hfix x hx]; exact hx
  · intro hy; exact ⟨y, hy, hfix y hy⟩

/-- The sequence `a + 1, V_{a+1}(a + 2), …` whose supremum is a `Γ`-point above `a`. -/
noncomputable def gpSeq (a : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => a + 1
  | n + 1 => VG (gpSeq a n) (gpSeq a n + 1)

theorem gpSeq_mono (a : Ordinal.{0}) : Monotone (gpSeq a) :=
  monotone_nat_of_le_succ (fun _ => (lt_of_lt_of_le (lt_add_one _) (VG_id_le _ _)).le)

theorem gpSeq_lt_Om1 {a : Ordinal.{0}} (ha : a < Om1) : ∀ n, gpSeq a n < Om1
  | 0 => Om1_add_lt ha (lt_trans one_lt_omega0 omega0_lt_omega_one)
  | n + 1 => VG_lt_Om1 _ (gpSeq_lt_Om1 ha n) _ (Om1_add_lt (gpSeq_lt_Om1 ha n)
      (lt_trans one_lt_omega0 omega0_lt_omega_one))

/-- The supremum of `gpSeq a` is a `Γ`-point above `a`. -/
theorem gpSeq_sup (a : Ordinal.{0}) :
    a < (⨆ n, gpSeq a n) ∧ IsGP (⨆ n, gpSeq a n) := by
  have hbdd : BddAbove (Set.range (gpSeq a)) := Ordinal.bddAbove_of_small
  set L := ⨆ n, gpSeq a n with hL
  have hle : ∀ n, gpSeq a n ≤ L := fun n => le_ciSup hbdd n
  have haL : a < L := lt_of_lt_of_le (lt_add_one a) (hle 0)
  refine ⟨haL, lt_of_le_of_lt zero_le haL, fun g hg => ?_⟩
  obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 hg
  have hb : BddAbove (Set.range fun m => gpSeq a (m + n + 1)) := Ordinal.bddAbove_of_small
  have htail : L = ⨆ m, gpSeq a (m + n + 1) := by
    refine le_antisymm (ciSup_le fun k => ?_) (ciSup_le fun m => hle _)
    exact (gpSeq_mono a (show k ≤ k + n + 1 by omega)).trans (le_ciSup hb k)
  rw [htail, (VG_normal g).map_iSup hb]
  congr 1
  funext m
  show VG g (VG (gpSeq a (m + n)) (gpSeq a (m + n) + 1)) = VG (gpSeq a (m + n)) (gpSeq a (m + n) + 1)
  exact VG_VG (lt_of_lt_of_le hn (gpSeq_mono a (by omega))) _

/-- Above every countable `a` there is a countable `Γ`-point. -/
theorem exists_GP_above {a : Ordinal.{0}} (ha : a < Om1) : ∃ l, a < l ∧ l < Om1 ∧ IsGP l :=
  ⟨_, (gpSeq_sup a).1, Ordinal.iSup_lt_omega_one (gpSeq_lt_Om1 ha), (gpSeq_sup a).2⟩

theorem GSet_unbounded : ¬ BddAbove GSet := by
  rintro ⟨b, hb⟩
  exact absurd (hb (Or.inr (gpSeq_sup b).2)) (not_le.2 (gpSeq_sup b).1)

/-! ## The enumeration `GG` and `Φ_Γ` -/

/-- `GG` enumerates `{0} ∪ Γ-points`. -/
noncomputable def GG : Ordinal.{0} → Ordinal.{0} := enumOrd GSet

theorem GG_normal : IsNormal GG := isNormal_enumOrd isGP_sup GSet_unbounded

theorem GG_strictMono : StrictMono GG := GG_normal.strictMono

theorem GG_mem (α : Ordinal.{0}) : GG α ∈ GSet := enumOrd_mem GSet_unbounded α

theorem GG_zero : GG 0 = 0 :=
  le_antisymm (enumOrd_le_of_forall_lt (Or.inl rfl) (fun _ hb => absurd hb (not_lt.2 zero_le)))
    zero_le

theorem GG_pos {α : Ordinal.{0}} (hα : 0 < α) : 0 < GG α := by
  have := GG_strictMono hα; rwa [GG_zero] at this

theorem isGP_GG {α : Ordinal.{0}} (hα : 0 < α) : IsGP (GG α) := by
  rcases GG_mem α with h | h
  · exact absurd h (GG_pos hα).ne'
  · exact h

theorem isGP_LamG : IsGP LamG := LamG_spec

theorem LamG_le_GP {l : Ordinal.{0}} (hl : IsGP l) : LamG ≤ l :=
  csInf_le' (s := {l | 0 < l ∧ ∀ g < l, VG g l = l}) hl

theorem GG_one : GG 1 = LamG := by
  refine le_antisymm (enumOrd_le_of_forall_lt (Or.inr isGP_LamG) (fun b hb => ?_)) ?_
  · show GG b < LamG
    rw [Order.lt_one_iff.1 hb, GG_zero]; exact isGP_LamG.1
  · exact LamG_le_GP (isGP_GG zero_lt_one)

theorem GG_surj {l : Ordinal.{0}} (hl : IsGP l) : ∃ α, GG α = l :=
  enumOrd_surjective GSet_unbounded (Or.inr hl)

theorem GG_lt_Om1 : ∀ α, α < Om1 → GG α < Om1 := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α IH =>
  intro hα
  haveI : Countable (Set.Iio α) := (countable_Iio_of_lt_Om1 hα).to_subtype
  have hs : (⨆ β : Set.Iio α, GG β) < Om1 :=
    Ordinal.iSup_lt_omega_one (fun β => IH β β.2 (β.2.trans hα))
  obtain ⟨l, hsl, hl1, hl⟩ := exists_GP_above hs
  refine lt_of_le_of_lt (enumOrd_le_of_forall_lt (Or.inr hl) (fun b hb => ?_)) hl1
  exact lt_of_le_of_lt (le_ciSup (f := fun β : Set.Iio α => GG β)
    ⟨Om1, by rintro _ ⟨j, rfl⟩; exact (IH j j.2 (j.2.trans hα)).le⟩ ⟨b, hb⟩) hsl

/-- `Φ_Γ`: the least `α ≥ 1` with `GG α = α`. -/
noncomputable def PhiG : Ordinal.{0} := nfp GG 1

theorem PhiG_fp : GG PhiG = PhiG := nfp_fp GG_normal 1

theorem one_le_PhiG : 1 ≤ PhiG := le_nfp _ _

theorem lt_GG {a : Ordinal.{0}} (h1 : 1 ≤ a) (h : a < PhiG) : a < GG a := by
  refine lt_of_le_of_ne (GG_strictMono.id_le a) (fun e => ?_)
  have : PhiG ≤ a := nfp_le_fp GG_strictMono.monotone h1 e.symm.le
  exact absurd h (not_lt.2 this)

theorem PhiG_lt_Om1 : PhiG < Om1 := by
  unfold PhiG
  rw [← iSup_iterate_eq_nfp]
  refine Ordinal.iSup_lt_omega_one (fun k => ?_)
  induction k with
  | zero => exact lt_trans one_lt_omega0 omega0_lt_omega_one
  | succ k ihk => rw [Function.iterate_succ_apply']; exact GG_lt_Om1 _ ihk

theorem isGP_PhiG : IsGP PhiG := by
  have := isGP_GG (lt_of_lt_of_le zero_lt_one one_le_PhiG); rwa [PhiG_fp] at this

theorem PhiG_ri : IsRestartIdx PhiG := by
  have h := isGP_PhiG
  have := h.2 0 h.1; rw [VG_zero] at this
  exact ri_of_fp h.1 this

theorem LamG_lt_PhiG : LamG < PhiG := by
  have h1 : 1 < PhiG := by
    refine lt_of_le_of_ne one_le_PhiG (fun e => ?_)
    have := PhiG_fp; rw [← e, GG_one] at this
    exact absurd this (ne_of_gt (lt_trans one_lt_omega0 omega_lt_LamG))
  have := GG_strictMono h1; rwa [GG_one, PhiG_fp] at this

/-- `invGG a = min{α : GG α = a}`. -/
noncomputable def invGG (a : Ordinal.{0}) : Ordinal.{0} := sInf {o | GG o = a}

theorem invGG_GG (o : Ordinal.{0}) : invGG (GG o) = o :=
  GG_strictMono.injective (csInf_mem (s := {x | GG x = GG o}) ⟨o, rfl⟩)

theorem GP_facts {a : Ordinal.{0}} (hG : IsGP a) (ha : a < PhiG) :
    upsilon a = a ∧ GG (invGG a) = a ∧ invGG a ≠ 0 ∧ invGG a < a ∧ lg (invGG a) < a := by
  obtain ⟨α, rfl⟩ := GG_surj hG
  rw [invGG_GG]
  have hfix : upsilon (GG α) = GG α := by
    have := hG.2 0 hG.1; rwa [VG_zero] at this
  have hα0 : α ≠ 0 := by intro h0; rw [h0, GG_zero] at hG; exact lt_irrefl _ hG.1
  have hαP : α < PhiG := lt_of_le_of_lt (GG_strictMono.id_le α) ha
  have hαa : α < GG α := lt_GG (one_le_iff_ne_zero.2 hα0) hαP
  exact ⟨hfix, rfl, hα0, hαa, lt_of_le_of_lt (lg_le hα0) hαa⟩

/-! ## Levels at points that are not `Γ`-points -/

theorem notGP_moved {a : Ordinal.{0}} (ha0 : 0 < a) (hG : ¬ IsGP a) : ∃ b < a, VG b a ≠ a := by
  by_contra hne
  exact hG ⟨ha0, fun g hg => by by_contra h; exact hne ⟨g, hg, h⟩⟩

theorem levG_lt' {a : Ordinal.{0}} (ha0 : 0 < a) (hG : ¬ IsGP a) : levG a < a := by
  obtain ⟨b, hba, hb⟩ := notGP_moved ha0 hG
  exact lt_of_le_of_lt ((levG_spec ⟨b, hb⟩).2.2 b hb) hba

theorem lev_moved {a : Ordinal.{0}} (ha0 : 0 < a) (hG : ¬ IsGP a) : ∃ b, VG b a ≠ a := by
  obtain ⟨b, -, hb⟩ := notGP_moved ha0 hG; exact ⟨b, hb⟩

theorem levG_facts' {a : Ordinal.{0}} (h : ∃ b, VG b a ≠ a) (ha0 : 0 < a) (hn : levG a ≠ 0) :
    upsilon a = a ∧ VG (levG a) (invG (levG a) a) = a ∧ invG (levG a) a ≠ 0 ∧
      invG (levG a) a < a ∧ lg (invG (levG a) a) < a := by
  have hspec := levG_spec h
  have hr : a ∈ Set.range (VG (levG a)) := (mem_range_VG hn).2 hspec.1
  have hV := invG_spec hr
  have hfix : upsilon a = a := ups_fix_of_VG hn hr
  set α := invG (levG a) a
  have hα0 : α ≠ 0 := by intro h0; rw [h0, VG_at_zero] at hV; rw [← hV] at ha0; exact lt_irrefl _ ha0
  have hαa : α < a := by
    refine lt_of_le_of_ne (by have := VG_id_le (levG a) α; rwa [hV] at this) (fun e => ?_)
    rw [e] at hV; exact hspec.2.1 hV
  exact ⟨hfix, hV, hα0, hαa, lt_of_le_of_lt (lg_le hα0) hαa⟩

/-! ## The offset below `Φ_Γ` -/

open Classical in
/-- **The offset below `Φ_Γ`**: `ρ·ρ + logend(α)` at a `Γ`-point `GG(α)`; `c(λ)` at level `0`;
`ρ·γ + logend(α)` at `λ = V_γ(α)` of level `γ ≥ 1` (not a `Γ`-point). -/
noncomputable def offG2 (a : Ordinal.{0}) : Ordinal.{0} :=
  if IsGP a then upsilon a * upsilon a + lg (invGG a)
  else if levG a = 0 then cL a else upsilon a * levG a + lg (invG (levG a) a)

theorem offG2_GP {a : Ordinal.{0}} (h : IsGP a) : offG2 a = upsilon a * upsilon a + lg (invGG a) := by
  simp [offG2, h]

theorem offG2_zero {a : Ordinal.{0}} (hG : ¬ IsGP a) (h : levG a = 0) : offG2 a = cL a := by
  simp [offG2, hG, h]

theorem offG2_pos {a : Ordinal.{0}} (hG : ¬ IsGP a) (h : levG a ≠ 0) :
    offG2 a = upsilon a * levG a + lg (invG (levG a) a) := by simp [offG2, hG, h]

theorem offG2_lt_succ {a : Ordinal.{0}} (hl : IsRestartIdx a) (hG : ¬ IsGP a) :
    offG2 a < upsilon a * (levG a + 1) := by
  have ha0 : 0 < a := pos_iff_ne_zero.2 hl.1
  have h := lev_moved ha0 hG
  by_cases hn : levG a = 0
  · rw [offG2_zero hG hn, hn, zero_add, mul_one]
    exact cL_lt_ups hl ((levG_eq_zero h).1 hn)
  · obtain ⟨hfix, -, -, -, hlg⟩ := levG_facts' h ha0 hn
    rw [offG2_pos hG hn, mul_add_one]
    exact (add_lt_add_iff_left _).2 (by rw [hfix]; exact hlg)

/-- At a restart that is not a `Γ`-point: `O(μ) < ρ_μ·ρ_μ`. -/
theorem offG2_lt_sq {a : Ordinal.{0}} (hl : IsRestartIdx a) (hG : ¬ IsGP a) :
    offG2 a < upsilon a * upsilon a := by
  have ha0 : 0 < a := pos_iff_ne_zero.2 hl.1
  refine lt_of_lt_of_le (offG2_lt_succ hl hG) (mul_le_mul_right ?_ _)
  exact (add_one_le_of_lt (levG_lt' ha0 hG)).trans (upsilon_normal.strictMono.id_le a)

theorem cL_le_offG2 {a : Ordinal.{0}} (hl : IsRestartIdx a) (ha : a < PhiG) : cL a ≤ offG2 a := by
  have ha0 : 0 < a := pos_iff_ne_zero.2 hl.1
  by_cases hG : IsGP a
  · obtain ⟨hfix, -⟩ := GP_facts hG ha
    rw [offG2_GP hG, cL_fp ha0 hfix, hfix]
    exact (le_mul_left a ha0).trans le_self_add
  by_cases hn : levG a = 0
  · rw [offG2_zero hG hn]
  · obtain ⟨hfix, -⟩ := levG_facts' (lev_moved ha0 hG) ha0 hn
    rw [cL_fp ha0 hfix, offG2_pos hG hn, hfix]
    exact (le_mul_left a (pos_iff_ne_zero.2 hn)).trans le_self_add

theorem offG2_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < PhiG) :
    offG2 l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hU : UpsPt (upsilon (l + ω + 1)) := upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans
    le_self_add))
  have hE := upsPt_inE hU
  have hlt : upsilon l < upsilon (l + ω + 1) := upsilon_normal.strictMono
    (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  by_cases hG : IsGP l
  · obtain ⟨hfix, -, -, -, hlg⟩ := GP_facts hG hlB
    rw [offG2_GP hG]
    exact (inE_indec hE).add_lt (hE.mul_lt hlt hlt) (lt_of_lt_of_le hlg
      (upsilon_normal.strictMono.id_le l) |>.trans hlt)
  · exact (offG2_lt_sq hl hG).trans (hE.mul_lt hlt hlt)

theorem one_le_offG2 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < PhiG) : 1 ≤ offG2 l :=
  (one_le_cL hl).trans (cL_le_offG2 hl hlB)

theorem offG2_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : offG2 l = 1 := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hnf : upsilon l ≠ l := by
    intro hfix
    rw [cL_fp hl0 hfix] at h2
    have := one_lt_of_ups_fp hl0 hfix
    exact absurd h2 (not_lt.2 (by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact add_one_le_of_lt this))
  have hG : ¬ IsGP l := fun h => hnf (by have := h.2 0 h.1; rwa [VG_zero] at this)
  rw [offG2_zero hG ((levG_eq_zero (lev_moved hl0 hG)).2 hnf)]
  exact le_antisymm (lt_succ_iff.1 (by simpa [one_add_one_eq_two] using h2)) (one_le_cL hl)

/-- At `μ = V_q(β)` (`1 ≤ q < μ`, `β > 0`): `ρ_μ·q + logend(β) ≤ O(μ)`. -/
theorem offG2_ge_range {q β : Ordinal.{0}} (hq : q ≠ 0) (hβ0 : 0 < β) (hqμ : q < VG q β) :
    upsilon (VG q β) * q + lg β ≤ offG2 (VG q β) := by
  have hμ0 : 0 < VG q β := VG_pos hβ0
  have hfix : upsilon (VG q β) = VG q β := ups_fix_of_VG hq ⟨β, rfl⟩
  have hlgβ : lg β ≤ VG q β := (lg_le hβ0.ne').trans (VG_id_le q β)
  by_cases hG : IsGP (VG q β)
  · rw [offG2_GP hG, hfix]
    refine le_trans ?_ le_self_add
    refine le_trans ?_ (mul_le_mul_right (add_one_le_of_lt hqμ) _)
    rw [mul_add_one]; exact add_le_add le_rfl hlgβ
  have h := lev_moved hμ0 hG
  have hge := levG_ge h hq ⟨β, rfl⟩
  have hn : levG (VG q β) ≠ 0 := (pos_iff_ne_zero.1 (lt_of_lt_of_le (pos_iff_ne_zero.2 hq) hge))
  rcases eq_or_lt_of_le hge with e | hlt
  · rw [offG2_pos hG hn, ← e, invG_VG]
  · rw [offG2_pos hG hn]
    refine le_trans ?_ le_self_add
    refine le_trans ?_ (mul_le_mul_right (add_one_le_of_lt hlt) _)
    rw [mul_add_one]
    exact add_le_add le_rfl (by rw [hfix]; exact hlgβ)

/-! ## The inputs of Lemmas TOP and RS below `Φ_Γ` -/

/-- **The input of Lemma TOP** at every restart index `λ < Φ_Γ`. -/
theorem topInG2 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < PhiG) : TopInG offG2 l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  by_cases hG : IsGP l
  · -- a `Γ`-point `GG(α)`: the term `x·x + logend(α)`
    obtain ⟨hfix, hGα, hα0, hαl, hlg⟩ := GP_facts hG hlB
    set α := invGG l with hαdef
    obtain ⟨β0, hβ0α, hβ0⟩ := lg_sep hα0
    have hx0 : max (GG β0) α < upsilon l := by
      rw [hfix]; exact max_lt (by rw [← hGα]; exact GG_strictMono hβ0α) hαl
    refine ⟨true, 0, lg α, max (GG β0) α, by rw [offG2_GP hG, tq_true], hρU.1,
      by rw [hfix]; exact hlg, fun h => absurd h (by simp), hx0, fun μ hμ hμl hx0μ => ?_⟩
    rw [tq_true]
    by_cases hGμ : IsGP μ
    · have hμP : μ < PhiG := hμl.trans hlB
      obtain ⟨hμfix, hGβ, -, -, -⟩ := GP_facts hGμ hμP
      rw [offG2_GP hGμ]
      refine (add_lt_add_iff_left _).2 (hβ0 _ ?_ ?_)
      · have : GG β0 < GG (invGG μ) :=
          calc GG β0 ≤ max (GG β0) α := le_max_left _ _
            _ < upsilon μ := hx0μ
            _ = μ := hμfix
            _ = GG (invGG μ) := hGβ.symm
        exact GG_strictMono.lt_iff_lt.1 this
      · have : GG (invGG μ) < GG α := by rw [hGβ, hGα]; exact hμl
        exact GG_strictMono.lt_iff_lt.1 this
    · exact lt_of_lt_of_le (offG2_lt_sq hμ hGμ) le_self_add
  have h := lev_moved hl0 hG
  by_cases hn : levG l = 0
  · -- level `0`: the constant `c(λ)`
    have hfix : upsilon l ≠ l := (levG_eq_zero h).1 hn
    obtain ⟨ν1, hν1l, hν1⟩ := cL_sep hl
    obtain ⟨ν2, hν2l, hν2⟩ := fix_bound_gen hl0 hfix
    refine ⟨false, 0, cL l, upsilon (max ν1 ν2), by rw [offG2_zero hG hn, tq_false, tg, mul_zero,
      zero_add], hρU.1, cL_lt_ups hl hfix, fun _ _ => one_le_cL hl,
      upsilon_normal.strictMono (max_lt hν1l hν2l), fun μ hμ hμl hνμ => ?_⟩
    have hνμ' : max ν1 ν2 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνμ
    have hμf : upsilon μ ≠ μ := fun e =>
      absurd (hν2 μ e hμl) (not_le.2 (lt_of_le_of_lt (le_max_right _ _) hνμ'))
    have hGμ : ¬ IsGP μ := fun hh => hμf (by have := hh.2 0 hh.1; rwa [VG_zero] at this)
    rw [offG2_zero hGμ ((levG_eq_zero (lev_moved (pos_iff_ne_zero.2 hμ.1) hGμ)).2 hμf),
      tq_false, tg, mul_zero, zero_add]
    exact hν1 μ hμ (lt_of_le_of_lt (le_max_left _ _) hνμ') hμl
  · -- level `n ≥ 1`, `λ = V_n(α)`: the term `x·n + logend(α)`
    obtain ⟨hfix, hV, hα0, hαl, hlg⟩ := levG_facts' h hl0 hn
    set n := levG l with hndef
    set α := invG n l with hαdef
    have hnl : n < l := levG_lt' hl0 hG
    obtain ⟨β0, hβ0α, hβ0⟩ := lg_sep hα0
    have hx0 : max (VG n β0) (max α n) < upsilon l := by
      rw [hfix]; exact max_lt (by rw [← hV]; exact VG_strictMono n hβ0α) (max_lt hαl hnl)
    refine ⟨false, n, lg α, max (VG n β0) (max α n), by rw [offG2_pos hG hn, tq_false, tg],
      by rw [hfix]; exact hnl, by rw [hfix]; exact hlg, fun _ h0 => absurd h0 hn, hx0,
      fun μ hμ hμl hx0μ => ?_⟩
    have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    rw [tq_false, tg]
    have hαμ : α < upsilon μ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hx0μ
    have hnμ : n < upsilon μ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hx0μ
    -- a `Γ`-point in `(x₀, λ)` would be a fixed point of `V_n` below `λ = V_n(α)`, so below `α`
    have hnoG : ¬ IsGP μ := by
      intro hh
      have hμfix : upsilon μ = μ := by have := hh.2 0 hh.1; rwa [VG_zero] at this
      rw [hμfix] at hαμ hnμ
      have hfμ : VG n μ = μ := hh.2 n hnμ
      have : μ < α := by
        have h1 : VG n μ < VG n α := by rw [hfμ, hV]; exact hμl
        exact (VG_strictMono n).lt_iff_lt.1 h1
      exact absurd this (not_lt.2 hαμ.le)
    have hμh := lev_moved hμ0 hnoG
    by_cases hm : levG μ = 0
    · rw [offG2_zero hnoG hm]
      refine lt_of_lt_of_le (cL_lt_ups hμ ((levG_eq_zero hμh).1 hm)) (le_trans ?_ le_self_add)
      exact le_mul_left _ (pos_iff_ne_zero.2 hn)
    obtain ⟨hμfix, hVμ, -, -, -⟩ := levG_facts' hμh hμ0 hm
    rcases lt_trichotomy (levG μ) n with hlt' | heq | hgt
    · refine lt_of_lt_of_le (offG2_lt_succ hμ hnoG) (le_trans ?_ le_self_add)
      exact mul_le_mul_right (add_one_le_of_lt hlt') _
    · rw [heq] at hVμ
      rw [offG2_pos hnoG hm, heq]
      refine (add_lt_add_iff_left _).2 (hβ0 _ ?_ ?_)
      · have : VG n β0 < VG n (invG n μ) :=
          calc VG n β0 ≤ max (VG n β0) (max α n) := le_max_left _ _
            _ < upsilon μ := hx0μ
            _ = μ := hμfix
            _ = VG n (invG n μ) := hVμ.symm
        exact (VG_strictMono n).lt_iff_lt.1 this
      · have : VG n (invG n μ) < VG n α := by rw [hVμ, hV]; exact hμl
        exact (VG_strictMono n).lt_iff_lt.1 this
    · exfalso
      have hfμ : VG n μ = μ := (levG_spec hμh).1 n hgt
      have : μ < α := by
        have h1 : VG n μ < VG n α := by rw [hfμ, hV]; exact hμl
        exact (VG_strictMono n).lt_iff_lt.1 h1
      rw [hμfix] at hαμ
      exact absurd this (not_lt.2 hαμ.le)

/-- Restarts `V_q(β)` with `logend(β) ≥ r` are cofinal below `V_q(a) = λ` (`a` a limit,
`r < logend(a)`, `λ < Φ_Γ`). -/
theorem targets_G2 {q a l r : Ordinal.{0}} (hq : q ≠ 0) (hVa : VG q a = l)
    (hlim : IsSuccLimit a) (hr : r < lg a) (hql : q < l) :
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq false q r (upsilon μ) ≤ offG2 μ := by
  intro ν hν
  have hν' : max ν q < l := max_lt hν hql
  rw [← hVa] at hν'
  obtain ⟨_, ⟨β', hβ', rfl⟩, hνβ'⟩ :=
    (lt_isLUB_iff ((VG_normal q).isLUB_image_Iio_of_isSuccLimit hlim)).1 hν'
  have ha0 : a ≠ 0 := hlim.ne_bot
  obtain ⟨β, hβ, hβa, hrβ⟩ := lg_dense ha0 hr (max β' r)
    (max_lt hβ' (lt_of_lt_of_le hr (lg_le ha0)))
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hβ
  have hμ0 : 0 < VG q β := VG_pos hβ0
  have hμl : VG q β < l := by rw [← hVa]; exact VG_strictMono q hβa
  have hfix : upsilon (VG q β) = VG q β := ups_fix_of_VG hq ⟨β, rfl⟩
  have hβ'β : VG q β' < VG q β := VG_strictMono q (lt_of_le_of_lt (le_max_left _ _) hβ)
  have hmax : max ν q < VG q β := hνβ'.trans hβ'β
  refine ⟨VG q β, ri_of_fp hμ0 hfix, lt_of_le_of_lt (le_max_left _ _) hmax, hμl, ?_⟩
  rw [tq_false, tg]
  exact le_trans (add_le_add le_rfl hrβ) (offG2_ge_range hq hβ0
    (lt_of_le_of_lt (le_max_right _ _) hmax))

/-- `Γ`-points `GG(β)` with `logend(β) ≥ r` are cofinal below `GG(α)` (`α` a limit, `r < logend(α)`). -/
theorem targetsGG {α l r : Ordinal.{0}} (hGα : GG α = l)
    (hlim : IsSuccLimit α) (hr : r < lg α) :
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq true 0 r (upsilon μ) ≤ offG2 μ := by
  intro ν hν
  rw [← hGα] at hν
  obtain ⟨_, ⟨β', hβ', rfl⟩, hνβ'⟩ :=
    (lt_isLUB_iff (GG_normal.isLUB_image_Iio_of_isSuccLimit hlim)).1 hν
  have ha0 : α ≠ 0 := hlim.ne_bot
  obtain ⟨β, hβ, hβα, hrβ⟩ := lg_dense ha0 hr (max β' r)
    (max_lt hβ' (lt_of_lt_of_le hr (lg_le ha0)))
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hβ
  have hG := isGP_GG hβ0
  have hfix : upsilon (GG β) = GG β := by have := hG.2 0 hG.1; rwa [VG_zero] at this
  have hμl : GG β < l := by rw [← hGα]; exact GG_strictMono hβα
  refine ⟨GG β, ri_of_fp hG.1 hfix, hνβ'.trans (GG_strictMono (lt_of_le_of_lt (le_max_left _ _) hβ)),
    hμl, ?_⟩
  rw [tq_true, offG2_GP hG, invGG_GG]
  exact add_le_add le_rfl hrβ

/-- **The input of Lemma RS** at every limit restart index `λ < Φ_Γ`. -/
theorem rsInG2 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < PhiG) (h2 : 2 ≤ cL l) :
    RsInG offG2 l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hconst : ∀ z < cL l, ∃ (b : Bool) (γ e : Ordinal.{0}), z = tq b γ e (upsilon l) ∧
      γ < upsilon l ∧ e < upsilon l ∧
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq b γ e (upsilon μ) ≤ offG2 μ := by
    intro z hz
    refine ⟨false, 0, z, by rw [tq_false, tg, mul_zero, zero_add], upsPt_upsilon hl0 |>.1,
      lt_of_lt_of_le hz (cL_le_ups hl), fun ν hν => ?_⟩
    have hz' : max z 1 < cL l := max_lt hz (lt_of_lt_of_le one_lt_two h2)
    obtain ⟨μ, hμ, hνμ, hμl, hzμ⟩ := cL_dense hl (le_max_right z 1) hz' ν hν
    refine ⟨μ, hμ, hνμ, hμl, ?_⟩
    rw [tq_false, tg, mul_zero, zero_add]
    exact ((le_max_left z 1).trans hzμ).trans (cL_le_offG2 hμ (hμl.trans hlB))
  -- `z = λ·q + r` with `1 ≤ q < λ` and `V_q(λ) = λ`
  have hfixcase : upsilon l = l → ∀ q r : Ordinal.{0}, q ≠ 0 → q < l → VG q l = l → r < l →
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq false q r (upsilon μ) ≤ offG2 μ := by
    intro hfix q r hq hql hVq hr
    have hE : InE l := inE_of_fp hl0 hfix
    have hlgl : lg l = l := by
      refine le_antisymm (lg_le hl.1) ((le_lg_iff hl.1 l).2 ?_)
      unfold InE at hE; rw [hE]
    exact targets_G2 hq hVq (ri_isSuccLimit hl) (by rw [hlgl]; exact hr) hql
  intro z hz
  by_cases hG : IsGP l
  · -- a `Γ`-point `GG(α)`
    obtain ⟨hfix, hGα, hα0, hαl, hlg⟩ := GP_facts hG hlB
    set α := invGG l with hαdef
    rw [offG2_GP hG, hfix] at hz
    rcases lt_or_ge z (l * l) with hzl | hzl
    · have hdm : l * (z / l) + z % l = z := div_add_mod z l
      have hr : z % l < l := mod_lt z hl.1
      have hq : z / l < l := (lt_mul_iff_div_lt hl.1).1 hzl
      rcases eq_or_ne (z / l) 0 with hq0 | hq0
      · rw [hq0, mul_zero, zero_add] at hdm
        exact hconst z (by rw [cL_fp hl0 hfix, ← hdm]; exact hr)
      · exact ⟨false, z / l, z % l, by rw [tq_false, tg, hfix, hdm], by rw [hfix]; exact hq,
          by rw [hfix]; exact hr, hfixcase hfix _ _ hq0 hq (hG.2 _ hq) hr⟩
    · -- `z = λ·λ + e'`, `e' < logend(α)`: targets `GG(β)`
      have he : l * l + (z - l * l) = z := Ordinal.add_sub_cancel_of_le hzl
      have he' : z - l * l < lg α := by rw [← he] at hz; exact (add_lt_add_iff_left _).1 hz
      have hαlim : IsSuccLimit α := by
        refine Ordinal.isSuccLimit_iff.2 ⟨hα0, isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
        have := (le_lg_iff hα0 1).1 (one_le_iff_ne_zero.2 (fun h0 => by
          rw [h0] at he'; exact absurd he' (not_lt.2 zero_le)))
        rwa [opow_one] at this
      refine ⟨true, 0, z - l * l, by rw [tq_true, hfix, he], by rw [hfix]; exact hl0,
        by rw [hfix]; exact lt_of_lt_of_le he' (hlg.le), targetsGG hGα hαlim he'⟩
  have h := lev_moved hl0 hG
  by_cases hn : levG l = 0
  · rw [offG2_zero hG hn] at hz; exact hconst z hz
  obtain ⟨hfix, hV, hα0, hαl, hlg⟩ := levG_facts' h hl0 hn
  set n := levG l with hndef
  set α := invG n l with hαdef
  have hnl : n < l := levG_lt' hl0 hG
  rw [offG2_pos hG hn, hfix] at hz
  have hdm : l * (z / l) + z % l = z := div_add_mod z l
  have hr : z % l < l := mod_lt z hl.1
  have hzq : z / l < n + 1 := by
    refine (lt_mul_iff_div_lt hl.1).1 ?_
    rw [mul_add_one]
    exact lt_of_lt_of_le hz (add_le_add le_rfl (le_of_lt hlg))
  have hqn : z / l ≤ n := lt_add_one_iff.1 hzq
  rcases eq_or_ne (z / l) 0 with hq0 | hq0
  · rw [hq0, mul_zero, zero_add] at hdm
    exact hconst z (by rw [cL_fp hl0 hfix, ← hdm]; exact hr)
  refine ⟨false, z / l, z % l, by rw [tq_false, tg, hfix, hdm],
    (by rw [hfix]; exact lt_of_le_of_lt hqn hnl), (by rw [hfix]; exact hr), ?_⟩
  rcases eq_or_lt_of_le hqn with hqe | hqlt
  · have hrα : z % l < lg α := by
      rw [← hdm, hqe] at hz; exact (add_lt_add_iff_left _).1 hz
    have hαlim : IsSuccLimit α := by
      refine Ordinal.isSuccLimit_iff.2 ⟨hα0, isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
      have := (le_lg_iff hα0 1).1 (one_le_iff_ne_zero.2 (fun h0 => by
        rw [h0] at hrα; exact absurd hrα (not_lt.2 zero_le)))
      rwa [opow_one] at this
    rw [hqe]
    exact targets_G2 hn hV hαlim hrα hnl
  · exact hfixcase hfix _ _ hq0 (hqlt.trans hnl) ((levG_spec h).1 _ hqlt) hr

/-- `offG2` is an offset specification up to `Φ_Γ`. -/
theorem specG2 : OffSpecG offG2 PhiG :=
  ⟨(ri_iff.1 PhiG_ri).2, PhiG_lt_Om1, fun _ hl hlB => offG2_lt_δ hl hlB,
    fun _ hl hlB => one_le_offG2 hl hlB, fun _ hl hlB => topInG2 hl hlB,
    fun _ hl _ h2 => offG2_succ hl h2, fun _ hl hlB h2 => rsInG2 hl hlB h2⟩

theorem PhiG_ups : upsilon PhiG = PhiG := by
  have h := isGP_PhiG; have := h.2 0 h.1; rwa [VG_zero] at this

/-- **Theorem BLK^O below `Φ_Γ`** in `R₂^C` (the first fixed point of the enumeration of the
`Γ`-points): (i) for the `<₂`-pairs whose RIGHT end is below `Φ_Γ = υ_{Φ_Γ}`: they are exactly
`(υ_{μ+ω·j}, υ_{μ+ω·j+1})`, `j ≥ 1`, `μ < Φ_Γ` zero or a restart index; (ii) a restart `ρ_λ`
(`λ < Φ_Γ`) has no `<₁`-predecessor and no `<₂`-successor, and its reach is `δ_λ + O(λ)` (`IsReach`;
interval form by `reach_interval`) with `O = offG2`; (iii) for the points below `Φ_Γ` that are NOT
`υ`-points only: they have their `R₁⁺` reach. -/
theorem blkG2 :
    (∀ c d, c < d → d < PhiG → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < PhiG ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < PhiG →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + offG2 l)) ∧
    (∀ α < PhiG, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  have h := blk_genG specG2
  rw [PhiG_ups] at h
  exact h

/-- **The exact reach at a `Γ`-point**: `lh(GG(α)) = δ + GG(α)·GG(α) + logend(α)` (`1 ≤ α`,
`GG(α) < Φ_Γ`). -/
theorem reach_GG {α : Ordinal.{0}} (hα0 : α ≠ 0) (hB : GG α < PhiG) :
    IsReach R2C (GG α) (upsilon (GG α + ω + 1) + (GG α * GG α + lg α)) := by
  have hG := isGP_GG (pos_iff_ne_zero.2 hα0)
  have hfix : upsilon (GG α) = GG α := by have := hG.2 0 hG.1; rwa [VG_zero] at this
  have hR := (blkG2.2.1 _ (ri_of_fp hG.1 hfix) hB).2.2
  rwa [offG2_GP hG, invGG_GG, hfix] at hR

/-- **Theorem OFF-V below `Φ_Γ`**: `lh(V_γ(α)) = δ + V_γ(α)·γ + logend(α)` at every point `V_γ(α)`
(`γ ≥ 1`, `1 ≤ α < V_γ(α)`) below `Φ_Γ` that is not a `Γ`-point. -/
theorem reach_VG2 {g α : Ordinal.{0}} (hg : g ≠ 0) (hα0 : α ≠ 0) (hαV : α < VG g α)
    (hB : VG g α < PhiG) (hG : ¬ IsGP (VG g α)) :
    IsReach R2C (VG g α) (upsilon (VG g α + ω + 1) + (VG g α * g + lg α)) := by
  have h0 : 0 < VG g α := VG_pos (pos_iff_ne_zero.2 hα0)
  have hfix := ups_fix_of_VG hg ⟨α, rfl⟩
  have h := lev_moved h0 hG
  have hlev : levG (VG g α) = g := by
    refine le_antisymm ?_ (levG_ge h hg ⟨α, rfl⟩)
    by_contra hlt
    have hf : VG g (VG g α) = VG g α := (levG_spec h).1 g (not_le.1 hlt)
    exact absurd hf (ne_of_gt (VG_strictMono g hαV))
  have hR := (blkG2.2.1 _ (ri_of_fp h0 hfix) hB).2.2
  rwa [offG2_pos hG (by rw [hlev]; exact hg), hlev, invG_VG, hfix] at hR

/-- `lh(Λ_Γ) = δ + Λ_Γ·Λ_Γ`, again, as the case `α = 1` of `reach_GG`; and the second `Γ`-point. -/
theorem reach_GG2 : IsReach R2C (GG 2) (upsilon (GG 2 + ω + 1) + GG 2 * GG 2) := by
  have hL2 : (2 : Ordinal.{0}) < LamG :=
    lt_trans (by exact_mod_cast natCast_lt_omega0 2) omega_lt_LamG
  have hB : GG 2 < PhiG := by
    have := GG_strictMono (hL2.trans LamG_lt_PhiG); rwa [PhiG_fp] at this
  have h := reach_GG (by norm_num) hB
  have hlg : lg (2 : Ordinal.{0}) = 0 := by exact_mod_cast lg_nat (n := 2) (by norm_num)
  rwa [hlg, add_zero] at h

/-- **CORE-C below `Φ_Γ`**: `[0, Φ_Γ) ⊆ Core(R₂^C)` (FRAG-free; [C09] Theorem 14.14). -/
theorem coreG2 : Set.Iio PhiG ⊆ Core R2C := by
  have := core_genG specG2; rwa [PhiG_ups] at this

end Googology.Trans.PoR.InaccPsi.R2
