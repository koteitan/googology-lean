import Googology.Trans.PoR.InaccPsi.R2.BlkG

/-!
# Theorem BLK^O up to `Λ_Γ` in `R₂^C` (the Veblen hierarchy over `υ` with ordinal levels)

The project's Veblen hierarchy over `υ` with ordinal levels: `VG γ = veblenWith υ γ` (Mathlib), so
`VG 0 = υ`, `VG 1 = Ξ`, `VG (γ+1)` enumerates the fixed points of `VG γ`, and at a limit `γ` `VG γ`
enumerates the common fixed points of the `VG γ'`, `γ' < γ` (`0` included, so `VG γ 1` is the least
nonzero one; `VG ω 1 = V_ω(1)`).  `Λ_Γ` (`LamG`) is the least `λ > 0` with `VG γ λ = λ` for every
`γ < λ`.  The level `γ(λ)` (`levG`) of `λ` is the largest `γ` with `VG γ' λ = λ` for all `γ' < γ`.

**Theorem OFF-V** (closed form, as the project's paper proof): `O(λ) = c(λ)` at level `0`,
`O(V_γ(α)) = ρ·γ + logend(α)` at level `γ ≥ 1` (`λ < Λ_Γ`), and `O(Λ_Γ) = ρ·ρ` (`offG`).  These are the
terms `x·γ + e` and `x·x` of `R2.BlkG`.  The inputs of Lemmas TOP and RS are proved here (`topInG`,
`rsInG`), so `blk_genG` applies with `B = Λ_Γ + ω²`.

* `VG`, `VG_lt_Om1`, `LamG` (`LamG_spec`, `LamG_lt_Om1`), `levG`, `invG`, `offG`;
* `topInG`, `targets_G`, `rsInG`, `specG`;
* `blkG` (**Theorem BLK^O up to `Λ_Γ`**), `reach_VG` (`lh(V_γ(α)) = δ + V_γ(α)·γ + logend(α)`),
  `reach_Vw` (`lh(V_ω(1)) = δ + V_ω(1)·ω`), `reach_LamG` (`lh(Λ_Γ) = δ + Λ_Γ·Λ_Γ`), `coreG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## The hierarchy -/

/-- `V_γ = veblenWith υ γ`. -/
noncomputable def VG (g : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := veblenWith upsilon g

theorem VG_normal (g : Ordinal.{0}) : IsNormal (VG g) := isNormal_veblenWith upsilon_normal g

theorem VG_strictMono (g : Ordinal.{0}) : StrictMono (VG g) := (VG_normal g).strictMono

theorem VG_zero : VG 0 = upsilon := veblenWith_zero upsilon

theorem VG_VG {g1 g2 : Ordinal.{0}} (h : g1 < g2) (a : Ordinal.{0}) : VG g1 (VG g2 a) = VG g2 a :=
  veblenWith_veblenWith_of_lt upsilon_normal h a

theorem mem_range_VG {g a : Ordinal.{0}} (hg : g ≠ 0) :
    a ∈ Set.range (VG g) ↔ ∀ b < g, VG b a = a :=
  mem_range_veblenWith upsilon_normal hg

theorem VG_id_le (g a : Ordinal.{0}) : a ≤ VG g a := (VG_strictMono g).id_le a

theorem VG_at_zero : ∀ g, VG g 0 = 0 := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  rcases eq_or_ne g 0 with rfl | hg
  · rw [VG_zero]; exact upsilon_zero
  · obtain ⟨o, ho⟩ := (mem_range_VG hg).2 (fun b hb => IH b hb)
    refine le_antisymm ?_ zero_le
    calc VG g 0 ≤ VG g o := (VG_strictMono g).monotone zero_le
      _ = 0 := ho

theorem VG_pos {g a : Ordinal.{0}} (ha : 0 < a) : 0 < VG g a := by
  have := VG_strictMono g ha; rwa [VG_at_zero] at this

/-- A fixed point of some `VG g` is a fixed point of `υ`. -/
theorem ups_fix_of_VG {g a : Ordinal.{0}} (hg : g ≠ 0) (h : a ∈ Set.range (VG g)) :
    upsilon a = a := by
  have := (mem_range_VG hg).1 h 0 (pos_iff_ne_zero.2 hg); rwa [VG_zero] at this

theorem VG_lt_Om1 : ∀ g, g < Om1 → ∀ a, a < Om1 → VG g a < Om1 := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [VG_zero]; exact ups_lt_Om1
  have e : VG g = derivFamily fun x : Set.Iio g => VG x.1 := veblenWith_of_ne_zero upsilon hg0
  haveI : Countable (Set.Iio g) := (countable_Iio_of_lt_Om1 hg).to_subtype
  have hfold : ∀ (a : Ordinal.{0}), a < Om1 → ∀ l : List (Set.Iio g),
      List.foldr (fun x : Set.Iio g => VG x.1) a l < Om1 := by
    intro a ha l
    induction l with
    | nil => exact ha
    | cons i l ih => exact IH i.1 i.2 (i.2.trans hg) _ ih
  have hnfp : ∀ a, a < Om1 → nfpFamily (fun x : Set.Iio g => VG x.1) a < Om1 := fun a ha =>
    Ordinal.iSup_lt_omega_one (fun l => hfold a ha l)
  rw [e]
  intro a
  induction a using limitRecOn with
  | zero => intro _; rw [derivFamily_zero]; exact hnfp 0 (omega_pos 1)
  | add_one b hb =>
    intro hb'
    rw [derivFamily_add_one]
    exact hnfp _ (Om1_add_lt (hb ((lt_add_one b).trans hb'))
      (lt_trans one_lt_omega0 omega0_lt_omega_one))
  | limit b hb H =>
    intro hb'
    rw [derivFamily_limit _ hb]
    haveI : Countable (Set.Iio b) := (countable_Iio_of_lt_Om1 hb').to_subtype
    exact Ordinal.iSup_lt_omega_one (fun i => H i.1 i.2 (i.2.trans hb'))

/-! ## `Λ_Γ` -/

/-- `Λ_Γ`: the least `λ > 0` with `V_γ(λ) = λ` for every `γ < λ`. -/
noncomputable def LamG : Ordinal.{0} := sInf {l | 0 < l ∧ ∀ g < l, VG g l = l}

/-- The sequence `1, V_1(2), …` (`λ_{n+1} = V_{λ_n}(λ_n + 1)`) whose supremum is such a `λ`. -/
noncomputable def lamSeq : ℕ → Ordinal.{0}
  | 0 => 1
  | n + 1 => VG (lamSeq n) (lamSeq n + 1)

theorem lamSeq_lt_succ (n : ℕ) : lamSeq n < lamSeq (n + 1) :=
  lt_of_lt_of_le (lt_add_one _) (VG_id_le _ _)

theorem lamSeq_mono : Monotone lamSeq := monotone_nat_of_le_succ (fun n => (lamSeq_lt_succ n).le)

theorem lamSeq_lt_Om1 : ∀ n, lamSeq n < Om1
  | 0 => lt_trans one_lt_omega0 omega0_lt_omega_one
  | n + 1 => VG_lt_Om1 _ (lamSeq_lt_Om1 n) _ (Om1_add_lt (lamSeq_lt_Om1 n)
      (lt_trans one_lt_omega0 omega0_lt_omega_one))

theorem lamSeq_bdd : BddAbove (Set.range lamSeq) :=
  ⟨Om1, by rintro _ ⟨n, rfl⟩; exact (lamSeq_lt_Om1 n).le⟩

theorem exists_LamG_set : ∃ l, l < Om1 ∧ 0 < l ∧ ∀ g < l, VG g l = l := by
  set L := ⨆ n, lamSeq n with hL
  have hLΩ : L < Om1 := Ordinal.iSup_lt_omega_one lamSeq_lt_Om1
  have hle : ∀ n, lamSeq n ≤ L := fun n => le_ciSup lamSeq_bdd n
  refine ⟨L, hLΩ, lt_of_lt_of_le zero_lt_one (hle 0), fun g hg => ?_⟩
  obtain ⟨n, hn⟩ := (lt_ciSup_iff lamSeq_bdd).1 hg
  have htail : L = ⨆ m, lamSeq (m + n + 1) := by
    refine le_antisymm (ciSup_le fun k => ?_) (ciSup_le fun m => hle _)
    have hb : BddAbove (Set.range fun m => lamSeq (m + n + 1)) :=
      ⟨Om1, by rintro _ ⟨m, rfl⟩; exact (lamSeq_lt_Om1 _).le⟩
    exact (lamSeq_mono (show k ≤ k + n + 1 by omega)).trans (le_ciSup hb k)
  have hb : BddAbove (Set.range fun m => lamSeq (m + n + 1)) :=
    ⟨Om1, by rintro _ ⟨m, rfl⟩; exact (lamSeq_lt_Om1 _).le⟩
  rw [htail, (VG_normal g).map_iSup hb]
  congr 1
  funext m
  show VG g (VG (lamSeq (m + n)) (lamSeq (m + n) + 1)) = VG (lamSeq (m + n)) (lamSeq (m + n) + 1)
  exact VG_VG (lt_of_lt_of_le hn (lamSeq_mono (by omega))) _

theorem LamG_spec : 0 < LamG ∧ ∀ g < LamG, VG g LamG = LamG := by
  obtain ⟨l, -, hl⟩ := exists_LamG_set
  exact csInf_mem (s := {l | 0 < l ∧ ∀ g < l, VG g l = l}) ⟨l, hl⟩

theorem LamG_lt_Om1 : LamG < Om1 := by
  obtain ⟨l, hl1, hl⟩ := exists_LamG_set
  exact lt_of_le_of_lt (csInf_le' hl) hl1

theorem LamG_ups : upsilon LamG = LamG := by
  have := LamG_spec.2 0 LamG_spec.1; rwa [VG_zero] at this

theorem LamG_ri : IsRestartIdx LamG := ri_of_fp LamG_spec.1 LamG_ups

/-- Below `Λ_Γ` every positive `a` is moved by some `VG b`, `b < a`. -/
theorem below_LamG {a : Ordinal.{0}} (ha0 : 0 < a) (ha : a < LamG) : ∃ b < a, VG b a ≠ a := by
  by_contra hne
  have hall : ∀ b < a, VG b a = a := fun b hb => by
    by_contra h; exact hne ⟨b, hb, h⟩
  exact absurd (csInf_le' (s := {l | 0 < l ∧ ∀ g < l, VG g l = l}) ⟨ha0, hall⟩) (not_le.2 ha)

/-! ## Levels -/

/-- The level of `a`: the largest `γ` with `VG γ' a = a` for every `γ' < γ`. -/
noncomputable def levG (a : Ordinal.{0}) : Ordinal.{0} := sSup {g | ∀ b < g, VG b a = a}

theorem levG_spec {a : Ordinal.{0}} (h : ∃ b, VG b a ≠ a) :
    (∀ b < levG a, VG b a = a) ∧ VG (levG a) a ≠ a ∧ ∀ b, VG b a ≠ a → levG a ≤ b := by
  obtain ⟨b0, hb0⟩ := h
  set S := {g : Ordinal.{0} | ∀ b < g, VG b a = a} with hS
  have hSb : ∀ b, VG b a ≠ a → ∀ g ∈ S, g ≤ b := fun b hb g hg =>
    not_lt.1 (fun hlt => hb (hg b hlt))
  have hbdd : BddAbove S := ⟨b0, hSb b0 hb0⟩
  have hne : S.Nonempty := ⟨0, fun b hb => absurd hb (not_lt.2 zero_le)⟩
  have h1 : ∀ b < levG a, VG b a = a := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := (lt_csSup_iff hbdd hne).1 hb
    exact hg b hbg
  refine ⟨h1, fun hfix => ?_, fun b hb => csSup_le hne (hSb b hb)⟩
  have hmem : levG a + 1 ∈ S := by
    intro b hb
    rcases lt_or_eq_of_le (lt_add_one_iff.1 hb) with hlt | rfl
    · exact h1 b hlt
    · exact hfix
  exact absurd (le_csSup hbdd hmem) (not_le.2 (lt_add_one _))

/-- `invG γ a = min{o : VG γ o = a}`. -/
noncomputable def invG (g a : Ordinal.{0}) : Ordinal.{0} := sInf {o | VG g o = a}

theorem invG_spec {g a : Ordinal.{0}} (h : a ∈ Set.range (VG g)) : VG g (invG g a) = a :=
  csInf_mem h

theorem invG_VG (g o : Ordinal.{0}) : invG g (VG g o) = o :=
  (VG_strictMono g).injective (invG_spec ⟨o, rfl⟩)

/-- The facts at a positive point below `Λ_Γ`. -/
theorem lev_below {a : Ordinal.{0}} (ha0 : 0 < a) (ha : a < LamG) :
    ∃ b, VG b a ≠ a := by
  obtain ⟨b, -, hb⟩ := below_LamG ha0 ha; exact ⟨b, hb⟩

theorem levG_lt {a : Ordinal.{0}} (ha0 : 0 < a) (ha : a < LamG) : levG a < a := by
  obtain ⟨b, hba, hb⟩ := below_LamG ha0 ha
  exact lt_of_le_of_lt ((levG_spec ⟨b, hb⟩).2.2 b hb) hba

theorem levG_eq_zero {a : Ordinal.{0}} (h : ∃ b, VG b a ≠ a) : levG a = 0 ↔ upsilon a ≠ a := by
  constructor
  · intro h0 hfix
    have := (levG_spec h).2.1; rw [h0, VG_zero] at this; exact this hfix
  · intro hnf
    by_contra hne
    have := (levG_spec h).1 0 (pos_iff_ne_zero.2 hne); rw [VG_zero] at this; exact hnf this

theorem levG_ge {a g : Ordinal.{0}} (h : ∃ b, VG b a ≠ a) (hg : g ≠ 0)
    (ha : a ∈ Set.range (VG g)) : g ≤ levG a := by
  by_contra hlt
  exact (levG_spec h).2.1 ((mem_range_VG hg).1 ha _ (not_le.1 hlt))

/-- At a positive point `a < Λ_Γ` of level `n ≥ 1`: `υ_a = a`, `a = V_n(α)`, `0 < α < a`, `logend(α) < a`. -/
theorem levG_facts {a : Ordinal.{0}} (ha0 : 0 < a) (ha : a < LamG) (hn : levG a ≠ 0) :
    upsilon a = a ∧ VG (levG a) (invG (levG a) a) = a ∧ invG (levG a) a ≠ 0 ∧
      invG (levG a) a < a ∧ lg (invG (levG a) a) < a := by
  have h := lev_below ha0 ha
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

/-! ## The offset -/

/-- **The offset of Theorem OFF-V up to `Λ_Γ`**: `ρ·ρ` at `Λ_Γ`; `c(λ)` at level `0`;
`ρ_λ·γ + logend(α)` at `λ = V_γ(α)` of level `γ ≥ 1`. -/
noncomputable def offG (a : Ordinal.{0}) : Ordinal.{0} :=
  if a = LamG then upsilon a * upsilon a
  else if levG a = 0 then cL a else upsilon a * levG a + lg (invG (levG a) a)

theorem offG_LamG : offG LamG = LamG * LamG := by simp [offG, LamG_ups]

theorem offG_zero {a : Ordinal.{0}} (ha : a ≠ LamG) (h : levG a = 0) : offG a = cL a := by
  simp [offG, ha, h]

theorem offG_pos {a : Ordinal.{0}} (ha : a ≠ LamG) (h : levG a ≠ 0) :
    offG a = upsilon a * levG a + lg (invG (levG a) a) := by simp [offG, ha, h]

/-- Below `Λ_Γ`: `O(μ) < ρ_μ·(γ(μ) + 1)`. -/
theorem offG_lt_succ {a : Ordinal.{0}} (hl : IsRestartIdx a) (ha : a < LamG) :
    offG a < upsilon a * (levG a + 1) := by
  have ha0 : 0 < a := pos_iff_ne_zero.2 hl.1
  have h := lev_below ha0 ha
  by_cases hn : levG a = 0
  · rw [offG_zero ha.ne hn, hn, zero_add, mul_one]
    exact cL_lt_ups hl ((levG_eq_zero h).1 hn)
  · obtain ⟨hfix, -, -, -, hlg⟩ := levG_facts ha0 ha hn
    rw [offG_pos ha.ne hn, mul_add_one]
    exact (add_lt_add_iff_left _).2 (by rw [hfix]; exact hlg)

theorem cL_le_offG {a : Ordinal.{0}} (hl : IsRestartIdx a) (ha : a ≤ LamG) : cL a ≤ offG a := by
  have ha0 : 0 < a := pos_iff_ne_zero.2 hl.1
  rcases eq_or_lt_of_le ha with rfl | hlt
  · rw [offG_LamG, cL_fp ha0 LamG_ups]
    exact le_mul_left _ ha0
  by_cases hn : levG a = 0
  · rw [offG_zero hlt.ne hn]
  · obtain ⟨hfix, -⟩ := levG_facts ha0 hlt hn
    rw [cL_fp ha0 hfix, offG_pos hlt.ne hn, hfix]
    exact (le_mul_left a (pos_iff_ne_zero.2 hn)).trans le_self_add

theorem offG_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l ≤ LamG) :
    offG l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hU : UpsPt (upsilon (l + ω + 1)) := upsPt_upsilon (lt_of_lt_of_le hl0 (le_self_add.trans
    le_self_add))
  have hE := upsPt_inE hU
  have hlt : upsilon l < upsilon (l + ω + 1) := upsilon_normal.strictMono
    (lt_of_lt_of_le (lt_add_of_pos_right l omega0_pos) le_self_add)
  rcases eq_or_lt_of_le hlB with rfl | hlt'
  · rw [offG_LamG]; rw [LamG_ups] at hlt; exact hE.mul_lt hlt hlt
  · refine (offG_lt_succ hl hlt').trans (hE.mul_lt hlt ?_)
    have hlev := levG_lt hl0 hlt'
    exact lt_of_le_of_lt (add_one_le_of_lt hlev) (lt_of_le_of_lt (upsilon_normal.strictMono.id_le l)
      hlt)

theorem one_le_offG {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l ≤ LamG) : 1 ≤ offG l :=
  (one_le_cL hl).trans (cL_le_offG hl hlB)

theorem offG_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l ≤ LamG) (h2 : cL l < 2) :
    offG l = 1 := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hnf : upsilon l ≠ l := by
    intro hfix
    rw [cL_fp hl0 hfix] at h2
    have := one_lt_of_ups_fp hl0 hfix
    exact absurd h2 (not_lt.2 (by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num]; exact add_one_le_of_lt this))
  have hlt : l < LamG := lt_of_le_of_ne hlB (fun e => hnf (e ▸ LamG_ups))
  rw [offG_zero hlt.ne ((levG_eq_zero (lev_below hl0 hlt)).2 hnf)]
  exact le_antisymm (lt_succ_iff.1 (by simpa [one_add_one_eq_two] using h2)) (one_le_cL hl)

/-- At `μ = V_q(β)` (`q ≥ 1`, `β > 0`, `μ < Λ_Γ`): `ρ_μ·q + logend(β) ≤ O(μ)`. -/
theorem offG_ge_range {q β : Ordinal.{0}} (hq : q ≠ 0) (hβ0 : 0 < β) (hB : VG q β < LamG) :
    upsilon (VG q β) * q + lg β ≤ offG (VG q β) := by
  have hμ0 : 0 < VG q β := VG_pos hβ0
  have h := lev_below hμ0 hB
  have hge := levG_ge h hq ⟨β, rfl⟩
  have hn : levG (VG q β) ≠ 0 := (pos_iff_ne_zero.1 (lt_of_lt_of_le (pos_iff_ne_zero.2 hq) hge))
  have hfix : upsilon (VG q β) = VG q β := ups_fix_of_VG hq ⟨β, rfl⟩
  rcases eq_or_lt_of_le hge with e | hlt
  · rw [offG_pos hB.ne hn, ← e, invG_VG]
  · rw [offG_pos hB.ne hn]
    refine le_trans ?_ le_self_add
    refine le_trans ?_ (mul_le_mul_right (add_one_le_of_lt hlt) _)
    rw [mul_add_one]
    refine add_le_add le_rfl ?_
    rw [hfix]; exact (lg_le hβ0.ne').trans (VG_id_le q β)

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** (Theorem OFF-V, upper half) at every restart index `λ ≤ Λ_Γ`. -/
theorem topInG {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l ≤ LamG) : TopInG offG l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  rcases eq_or_lt_of_le hlB with rfl | hlt
  · -- `Λ_Γ`: the term `x·x`
    refine ⟨true, 0, 0, 0, by rw [offG_LamG, tq_true, add_zero, LamG_ups], hρU.1, hρU.1,
      fun h => absurd h (by simp), hρU.1, fun μ hμ hμl _ => ?_⟩
    rw [tq_true, add_zero]
    refine lt_of_lt_of_le (offG_lt_succ hμ hμl) (mul_le_mul_right ?_ _)
    exact (add_one_le_of_lt (levG_lt (pos_iff_ne_zero.2 hμ.1) hμl)).trans
      (upsilon_normal.strictMono.id_le μ)
  have h := lev_below hl0 hlt
  by_cases hn : levG l = 0
  · -- level `0`: the constant `c(λ)`
    have hfix : upsilon l ≠ l := (levG_eq_zero h).1 hn
    obtain ⟨ν1, hν1l, hν1⟩ := cL_sep hl
    obtain ⟨ν2, hν2l, hν2⟩ := fix_bound_gen hl0 hfix
    refine ⟨false, 0, cL l, upsilon (max ν1 ν2), by rw [offG_zero hlt.ne hn, tq_false, tg, mul_zero,
      zero_add], hρU.1, cL_lt_ups hl hfix, fun _ _ => one_le_cL hl,
      upsilon_normal.strictMono (max_lt hν1l hν2l), fun μ hμ hμl hνμ => ?_⟩
    have hνμ' : max ν1 ν2 < μ := upsilon_normal.strictMono.lt_iff_lt.1 hνμ
    have hμf : upsilon μ ≠ μ := fun e =>
      absurd (hν2 μ e hμl) (not_le.2 (lt_of_le_of_lt (le_max_right _ _) hνμ'))
    have hμlt : μ < LamG := hμl.trans hlt
    rw [offG_zero hμlt.ne ((levG_eq_zero (lev_below (pos_iff_ne_zero.2 hμ.1) hμlt)).2 hμf),
      tq_false, tg, mul_zero, zero_add]
    exact hν1 μ hμ (lt_of_le_of_lt (le_max_left _ _) hνμ') hμl
  · -- level `n ≥ 1`, `λ = V_n(α)`: the term `x·n + logend(α)`
    obtain ⟨hfix, hV, hα0, hαl, hlg⟩ := levG_facts hl0 hlt hn
    set n := levG l with hndef
    set α := invG n l with hαdef
    have hnl : n < l := levG_lt hl0 hlt
    obtain ⟨β0, hβ0α, hβ0⟩ := lg_sep hα0
    have hx0 : max (VG n β0) α < upsilon l := by
      rw [hfix]; exact max_lt (by rw [← hV]; exact VG_strictMono n hβ0α) hαl
    refine ⟨false, n, lg α, max (VG n β0) α, by rw [offG_pos hlt.ne hn, tq_false, tg],
      by rw [hfix]; exact hnl, by rw [hfix]; exact hlg, fun _ h0 => absurd h0 hn, hx0,
      fun μ hμ hμl hx0μ => ?_⟩
    have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
    have hμlt : μ < LamG := hμl.trans hlt
    have hμh := lev_below hμ0 hμlt
    rw [tq_false, tg]
    by_cases hm : levG μ = 0
    · rw [offG_zero hμlt.ne hm]
      refine lt_of_lt_of_le (cL_lt_ups hμ ((levG_eq_zero hμh).1 hm)) (le_trans ?_ le_self_add)
      exact le_mul_left _ (pos_iff_ne_zero.2 hn)
    obtain ⟨hμfix, hVμ, -, -, -⟩ := levG_facts hμ0 hμlt hm
    rcases lt_trichotomy (levG μ) n with hlt' | heq | hgt
    · refine lt_of_lt_of_le (offG_lt_succ hμ hμlt) (le_trans ?_ le_self_add)
      exact mul_le_mul_right (add_one_le_of_lt hlt') _
    · rw [heq] at hVμ
      rw [offG_pos hμlt.ne hm, heq]
      refine (add_lt_add_iff_left _).2 (hβ0 _ ?_ ?_)
      · have : VG n β0 < VG n (invG n μ) :=
          calc VG n β0 ≤ max (VG n β0) α := le_max_left _ _
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
      rw [hμfix] at hx0μ
      exact absurd (lt_of_le_of_lt (le_max_right _ _) hx0μ) (not_lt.2 this.le)

/-- Restarts `V_q(β)` with `logend(β) ≥ r` are cofinal below `V_q(a) = λ` (`a` a limit,
`r < logend(a)`). -/
theorem targets_G {q a l r : Ordinal.{0}} (hq : q ≠ 0) (hVa : VG q a = l) (hlB : l ≤ LamG)
    (hlim : IsSuccLimit a) (hr : r < lg a) :
    ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq false q r (upsilon μ) ≤ offG μ := by
  intro ν hν
  rw [← hVa] at hν
  obtain ⟨_, ⟨β', hβ', rfl⟩, hνβ'⟩ :=
    (lt_isLUB_iff ((VG_normal q).isLUB_image_Iio_of_isSuccLimit hlim)).1 hν
  have ha0 : a ≠ 0 := hlim.ne_bot
  obtain ⟨β, hβ, hβa, hrβ⟩ := lg_dense ha0 hr (max β' r)
    (max_lt hβ' (lt_of_lt_of_le hr (lg_le ha0)))
  have hβ0 : 0 < β := lt_of_le_of_lt zero_le hβ
  have hμ0 : 0 < VG q β := VG_pos hβ0
  have hμl : VG q β < l := by rw [← hVa]; exact VG_strictMono q hβa
  have hfix : upsilon (VG q β) = VG q β := ups_fix_of_VG hq ⟨β, rfl⟩
  refine ⟨VG q β, ri_of_fp hμ0 hfix,
    hνβ'.trans (VG_strictMono q (lt_of_le_of_lt (le_max_left _ _) hβ)), hμl, ?_⟩
  rw [tq_false, tg]
  exact le_trans (add_le_add le_rfl hrβ) (offG_ge_range hq hβ0 (lt_of_lt_of_le hμl hlB))

theorem ri_isSuccLimit {l : Ordinal.{0}} (hl : IsRestartIdx l) : IsSuccLimit l := by
  obtain ⟨p, hp⟩ := (ri_iff.1 hl).2
  have hp0 : p ≠ 0 := by intro h0; rw [h0, mul_zero] at hp; exact hl.1 hp
  rw [hp]
  exact isSuccLimit_mul_left (isSuccLimit_mul_right omega0_pos isSuccLimit_omega0)
    (pos_iff_ne_zero.2 hp0)

/-- **The input of Lemma RS** (Theorem OFF-V, lower half) at every limit restart index `λ ≤ Λ_Γ`. -/
theorem rsInG {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l ≤ LamG) (h2 : 2 ≤ cL l) :
    RsInG offG l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  -- the constants `z < c(λ)`
  have hconst : ∀ z < cL l, ∃ (b : Bool) (γ e : Ordinal.{0}), z = tq b γ e (upsilon l) ∧
      γ < upsilon l ∧ e < upsilon l ∧
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq b γ e (upsilon μ) ≤ offG μ := by
    intro z hz
    refine ⟨false, 0, z, by rw [tq_false, tg, mul_zero, zero_add], upsPt_upsilon hl0 |>.1, lt_of_lt_of_le hz
      (cL_le_ups hl), fun ν hν => ?_⟩
    have hz' : max z 1 < cL l := max_lt hz (lt_of_lt_of_le one_lt_two h2)
    obtain ⟨μ, hμ, hνμ, hμl, hzμ⟩ := cL_dense hl (le_max_right z 1) hz' ν hν
    refine ⟨μ, hμ, hνμ, hμl, ?_⟩
    rw [tq_false, tg, mul_zero, zero_add]
    exact ((le_max_left z 1).trans hzμ).trans (cL_le_offG hμ (hμl.le.trans hlB))
  -- `z = λ·q + r` with `1 ≤ q` and `V_q(λ) = λ`: targets `V_q(β)` below `λ`
  have hfixcase : upsilon l = l → ∀ q r : Ordinal.{0}, q ≠ 0 → VG q l = l → r < l →
      ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ tq false q r (upsilon μ) ≤ offG μ := by
    intro hfix q r hq hVq hr
    have hE : InE l := inE_of_fp hl0 hfix
    have hlgl : lg l = l := by
      refine le_antisymm (lg_le hl.1) ((le_lg_iff hl.1 l).2 ?_)
      unfold InE at hE; rw [hE]
    exact targets_G hq hVq hlB (ri_isSuccLimit hl) (by rw [hlgl]; exact hr)
  intro z hz
  rcases eq_or_lt_of_le hlB with rfl | hlt
  · -- `Λ_Γ`
    rw [offG_LamG] at hz
    set l := LamG with hldef
    have hdm : l * (z / l) + z % l = z := div_add_mod z l
    have hr : z % l < l := mod_lt z hl.1
    have hq : z / l < l := (lt_mul_iff_div_lt hl.1).1 hz
    rcases eq_or_ne (z / l) 0 with hq0 | hq0
    · rw [hq0, mul_zero, zero_add] at hdm
      exact hconst z (by rw [cL_fp hl0 LamG_ups, ← hdm]; exact hr)
    · refine ⟨false, z / l, z % l, by rw [tq_false, tg, LamG_ups, hdm], by rw [LamG_ups]; exact hq,
        by rw [LamG_ups]; exact hr, hfixcase LamG_ups _ _ hq0 (LamG_spec.2 _ hq) hr⟩
  have h := lev_below hl0 hlt
  by_cases hn : levG l = 0
  · rw [offG_zero hlt.ne hn] at hz; exact hconst z hz
  obtain ⟨hfix, hV, hα0, hαl, hlg⟩ := levG_facts hl0 hlt hn
  set n := levG l with hndef
  set α := invG n l with hαdef
  rw [offG_pos hlt.ne hn, hfix] at hz
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
    (by rw [hfix]; exact lt_of_le_of_lt hqn (levG_lt hl0 hlt)), (by rw [hfix]; exact hr), ?_⟩
  rcases eq_or_lt_of_le hqn with hqe | hqlt
  · -- `q = n`: targets `V_n(β)` below `V_n(α)`
    have hrα : z % l < lg α := by
      rw [← hdm, hqe] at hz; exact (add_lt_add_iff_left _).1 hz
    have hαlim : IsSuccLimit α := by
      refine Ordinal.isSuccLimit_iff.2 ⟨hα0, isSuccPrelimit_iff_omega0_dvd.2 ?_⟩
      have := (le_lg_iff hα0 1).1 (one_le_iff_ne_zero.2 (fun h0 => by
        rw [h0] at hrα; exact absurd hrα (not_lt.2 zero_le)))
      rwa [opow_one] at this
    rw [hqe]
    exact targets_G hn hV hlB hαlim hrα
  · -- `1 ≤ q < n`: targets `V_q(β)` below `V_q(λ) = λ`
    exact hfixcase hfix _ _ hq0 ((levG_spec h).1 _ hqlt) hr

/-! ## Theorem BLK^O up to `Λ_Γ` -/

theorem le_LamG_of_lt {μ : Ordinal.{0}} (hm : μ = 0 ∨ IsRestartIdx μ) (hμ : μ < LamG + ω * ω) :
    μ ≤ LamG := by
  by_contra hgt
  exact absurd hμ (not_lt.2 (next_mult (ri_iff.1 LamG_ri).2 (mult_of hm) (not_le.1 hgt)))

theorem lt_LamG_add {μ : Ordinal.{0}} (hμ : μ ≤ LamG) : μ < LamG + ω * ω :=
  lt_of_le_of_lt hμ (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))

/-- `offG` is an offset specification up to `Λ_Γ + ω²`. -/
theorem specG : OffSpecG offG (LamG + ω * ω) := by
  have hX : ∀ l, IsRestartIdx l → l < LamG + ω * ω → l ≤ LamG := fun l hl hlt =>
    le_LamG_of_lt (Or.inr hl) hlt
  refine ⟨?_, Om1_add_lt LamG_lt_Om1 ww_lt_Om1, fun l hl hlt => offG_lt_δ hl (hX l hl hlt),
    fun l hl hlt => one_le_offG hl (hX l hl hlt), fun l hl hlt => topInG hl (hX l hl hlt),
    fun l hl hlt h2 => offG_succ hl (hX l hl hlt) h2,
    fun l hl hlt h2 => rsInG hl (hX l hl hlt) h2⟩
  obtain ⟨q, hq⟩ := (ri_iff.1 LamG_ri).2
  exact ⟨q + 1, by rw [mul_add_one, hq]⟩

/-- **Theorem BLK^O up to `Λ_Γ`** in `R₂^C` (the project's Theorem BLK^O with the closed form of
Theorem OFF-V, for every restart index `λ ≤ Λ_Γ`):
(i) for the `<₂`-pairs whose RIGHT end is below `υ_{Λ_Γ+ω²}`: they are exactly `(υ_{μ+ω·j}, υ_{μ+ω·j+1})`,
`j ≥ 1`, `μ ≤ Λ_Γ` zero or a restart index;
(ii) a restart `ρ_λ` (`λ ≤ Λ_Γ`) has no `<₁`-predecessor and no `<₂`-successor, and its reach is
`δ_λ + O(λ)` (`IsReach`: `ρ_λ ≤₁ δ_λ + O(λ)` and every `γ` with `ρ_λ ≤₁ γ` is `≤ δ_λ + O(λ)`; the interval
form `{γ : ρ_λ ≤₁ γ} = [ρ_λ, δ_λ + O(λ)]` follows by `Basic.le1_of_le_of_le1`, see `reach_interval`), with
`O = offG` (Theorem OFF-V: `c(λ)` at level `0`, `ρ_λ·γ + logend(α)` at `λ = V_γ(α)` of level `γ ≥ 1`,
`ρ·ρ` at `Λ_Γ`);
(iii) for the points below `υ_{Λ_Γ+ω²}` that are NOT `υ`-points only: they have their `R₁⁺` reach
(`≤₁` of `R₂^C` = `≤₁` of `R₁⁺` from them). -/
theorem blkG :
    (∀ c d, c < d → d < upsilon (LamG + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ ≤ LamG ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l ≤ LamG →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + offG l)) ∧
    (∀ α < upsilon (LamG + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  obtain ⟨H1, H2, H3⟩ := blk_genG specG
  refine ⟨fun c d hcd hd => ?_, fun l hl hlX => H2 l hl (lt_LamG_add hlX), H3⟩
  rw [H1 c d hcd hd]
  constructor
  · rintro ⟨μ, j, hμ, hμl, h1, h2⟩
    exact ⟨μ, j, hμ, le_LamG_of_lt hμ hμl, h1, h2⟩
  · rintro ⟨μ, j, hμ, hμl, h1, h2⟩
    exact ⟨μ, j, hμ, lt_LamG_add hμl, h1, h2⟩

/-- The interval form of a reach: `{γ : x ≤₁ γ} = [x, r]` (by `Basic.le1_of_le_of_le1`). -/
theorem reach_interval {x r : Ordinal.{0}} (h : IsReach R2C x r) (g : Ordinal.{0}) :
    le1 x g ↔ x ≤ g ∧ g ≤ r :=
  ⟨fun hg => ⟨le1_le hg, h.2 g hg⟩, fun hg => le1_of_le_of_le1 hg.1 hg.2 h.1⟩

/-- **The exact reach at a point of level `γ ≥ 1` below `Λ_Γ`**: `lh(V_γ(α)) = δ + V_γ(α)·γ + logend(α)`
(`α ≥ 1`, `α < V_γ(α)`). -/
theorem reach_VG {g α : Ordinal.{0}} (hg : g ≠ 0) (hα0 : α ≠ 0) (hαV : α < VG g α)
    (hB : VG g α < LamG) :
    IsReach R2C (VG g α) (upsilon (VG g α + ω + 1) + (VG g α * g + lg α)) := by
  have h0 : 0 < VG g α := VG_pos (pos_iff_ne_zero.2 hα0)
  have hfix := ups_fix_of_VG hg ⟨α, rfl⟩
  have h := lev_below h0 hB
  have hlev : levG (VG g α) = g := by
    refine le_antisymm ?_ (levG_ge h hg ⟨α, rfl⟩)
    by_contra hlt
    have hf : VG g (VG g α) = VG g α := (levG_spec h).1 g (not_le.1 hlt)
    exact absurd hf (ne_of_gt (VG_strictMono g hαV))
  have hR := (blkG.2.1 _ (ri_of_fp h0 hfix) hB.le).2.2
  rwa [offG_pos hB.ne (by rw [hlev]; exact hg), hlev, invG_VG, hfix] at hR

/-- **`lh(Λ_Γ) = δ + Λ_Γ·Λ_Γ`** (`= δ + ω^{ρ·2}`). -/
theorem reach_LamG : IsReach R2C LamG (upsilon (LamG + ω + 1) + LamG * LamG) := by
  have hR := (blkG.2.1 _ LamG_ri le_rfl).2.2
  rwa [offG_LamG, LamG_ups] at hR

theorem omega_lt_LamG : (ω : Ordinal.{0}) < LamG := by
  have h1 := one_lt_of_ups_fp LamG_spec.1 LamG_ups
  have hE := inE_of_fp LamG_spec.1 LamG_ups
  have hω : (ω : Ordinal.{0}) ≤ LamG := by
    calc (ω : Ordinal.{0}) = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
      _ ≤ ω ^ LamG := opow_le_opow_right omega0_pos h1.le
      _ = LamG := hE
  refine lt_of_le_of_ne hω (fun e => ?_)
  have h2 : ω ^ (ω : Ordinal.{0}) = ω := by unfold InE at hE; rw [← e] at hE; exact hE
  have h3 : ω ^ (1 : Ordinal.{0}) < ω ^ (ω : Ordinal.{0}) :=
    (opow_lt_opow_iff_right one_lt_omega0).2 one_lt_omega0
  rw [opow_one, h2] at h3
  exact lt_irrefl _ h3

/-- `V_ω(1) < Λ_Γ`. -/
theorem Vw_lt_LamG : VG ω 1 < LamG := by
  have h1 : (1 : Ordinal.{0}) < LamG := lt_trans one_lt_omega0 omega_lt_LamG
  have := VG_strictMono ω h1
  rwa [LamG_spec.2 ω omega_lt_LamG] at this

/-- **`lh(V_ω(1)) = δ + V_ω(1)·ω`** (`= δ + ω^{ρ+1}`), the first offset that is not a term `x·m + k`
with `m` finite. -/
theorem reach_Vw : IsReach R2C (VG ω 1) (upsilon (VG ω 1 + ω + 1) + VG ω 1 * ω) := by
  have hα : (1 : Ordinal.{0}) < VG ω 1 := by
    have h0 := VG_pos (g := ω) (zero_lt_one : (0 : Ordinal.{0}) < 1)
    have hfix := ups_fix_of_VG omega0_pos.ne' ⟨1, rfl⟩
    exact one_lt_of_ups_fp h0 hfix
  have h := reach_VG omega0_pos.ne' one_ne_zero hα Vw_lt_LamG
  have hlg1 : lg (1 : Ordinal.{0}) = 0 := by exact_mod_cast lg_nat (n := 1) one_ne_zero
  rwa [hlg1, add_zero] at h

/-! ## The link with stage 4's `V n` and `V_ω(1)` -/

/-- `VG n = V n` for finite `n` (stage 4's `V 0 = υ`, `V (n+1) = deriv (V n)`). -/
theorem VG_nat : ∀ n : ℕ, VG n = V n
  | 0 => by rw [Nat.cast_zero, VG_zero]; rfl
  | n + 1 => by
    rw [Nat.cast_succ, VG, veblenWith_add_one upsilon_normal, V_succ, ← VG_nat n]; rfl

/-- `V_m(V_ω(1)) = V_ω(1)` for every finite `m`. -/
theorem V_Vw1 (m : ℕ) : V m Vw1 = Vw1 := by
  have hmono : Monotone fun n : ℕ => V (n + 1) 1 := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    have h1 : (1 : Ordinal.{0}) ≤ V (n + 2) 1 := (V_strictMono (n + 2)).id_le 1
    have := (V_strictMono (n + 1)).monotone h1
    rwa [V_fp (n + 1) 1] at this
  have hb : BddAbove (Set.range fun n : ℕ => V (n + m + 1) 1) :=
    ⟨Om1, by rintro _ ⟨n, rfl⟩; exact (V_lt_Om1 _ 1 (lt_trans one_lt_omega0 omega0_lt_omega_one)).le⟩
  have htail : Vw1 = ⨆ n : ℕ, V (n + m + 1) 1 := by
    refine le_antisymm (ciSup_le fun k => ?_) (ciSup_le fun n => V_le_Vw1 _)
    exact (hmono (show k ≤ k + m by omega)).trans (le_ciSup hb k)
  rw [htail, (V_normal m).map_iSup hb]
  congr 1
  funext n
  have hlt : (m : Ordinal.{0}) < ((n + m + 1 : ℕ) : Ordinal.{0}) := by exact_mod_cast (by omega)
  have := VG_VG hlt 1
  rwa [VG_nat, VG_nat] at this

/-- **`V_ω(1) = VG ω 1`**: stage 4's `V_ω(1) = sup_n V_{n+1}(1)` is the least nonzero common fixed point of
the `V_n`. -/
theorem Vw1_eq : Vw1 = VG ω 1 := by
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · -- `VG ω 1` is a nonzero value of `V_{n+1}`
    have hr : VG ω 1 ∈ Set.range (VG ((n + 1 : ℕ) : Ordinal.{0})) := by
      refine (mem_range_VG (by exact_mod_cast Nat.succ_ne_zero n)).2 (fun b hb => ?_)
      exact VG_VG (lt_trans hb (by exact_mod_cast natCast_lt_omega0 (n + 1))) 1
    obtain ⟨o, ho⟩ := hr
    have ho0 : o ≠ 0 := by
      intro h0; rw [h0, VG_at_zero] at ho
      exact (VG_pos (g := ω) zero_lt_one).ne' ho.symm
    rw [← VG_nat, ← ho]
    exact (VG_strictMono _).monotone (one_le_iff_ne_zero.2 ho0)
  · -- `V_ω(1)` is a nonzero common fixed point of the `VG m`
    have hr : Vw1 ∈ Set.range (VG ω) := by
      refine (mem_range_VG omega0_pos.ne').2 (fun b hb => ?_)
      obtain ⟨m, rfl⟩ := lt_omega0.1 hb
      rw [VG_nat]; exact V_Vw1 m
    obtain ⟨o, ho⟩ := hr
    have ho0 : o ≠ 0 := by
      intro h0; rw [h0, VG_at_zero] at ho; exact Vw1_pos.ne' ho.symm
    rw [← ho]
    exact (VG_strictMono _).monotone (one_le_iff_ne_zero.2 ho0)

/-- **`lh(V_ω(1)) = δ + V_ω(1)·ω`** with stage 4's `V_ω(1)` (`Vw1`). -/
theorem reach_Vw1 : IsReach R2C Vw1 (upsilon (Vw1 + ω + 1) + Vw1 * ω) := by
  rw [Vw1_eq]; exact reach_Vw

/-- **CORE-C up to `Λ_Γ`**: every ordinal below `υ_{Λ_Γ+ω²}` (in particular every ordinal `≤ Λ_Γ`)
is in `Core(R₂^C)` (FRAG-free; [C09] Theorem 14.14). -/
theorem coreG : Set.Iio (upsilon (LamG + ω * ω)) ⊆ Core R2C := core_genG specG

theorem coreG_LamG : Set.Iic LamG ⊆ Core R2C := by
  intro x hx
  have : LamG < upsilon (LamG + ω * ω) := by
    conv_lhs => rw [← LamG_ups]
    exact upsilon_normal.strictMono (lt_add_of_pos_right _ (mul_pos omega0_pos omega0_pos))
  exact coreG (lt_of_le_of_lt hx this)

end Googology.Trans.PoR.InaccPsi.R2
