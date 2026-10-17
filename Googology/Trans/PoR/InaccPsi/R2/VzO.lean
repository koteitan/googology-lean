import Googology.Trans.PoR.InaccPsi.R2.VzI
import Googology.Trans.PoR.InaccPsi.R2.VzB

/-!
# The recursive offset over the terms `φ(n, ·)` in `x`, Theorem BLK^O up to `Λ_B`, and the reach at every
frontier

`B(x) = VzB x = sup_N ϑˣ(Ω₁·N)` is the least value of `φ(ω, ·)` above `x` (`vzB_omega`); `Λ_B` is the frontier of
`B`.

The project's recursive offset (its paper's Definition 2.2) over the terms `VzTm` (constants, the base, `ϑˣ(Ω₁·n + t)`
for `1 ≤ n < ω`, sums, `ω^t`; values below `VzB x = sup_N ϑˣ(Ω₁·N)`).  `VzOrec(λ) = sup ({1} ∪ {s(ρ_λ) + 1 : s realized
cofinally below λ, constants below ρ_λ})`.  The proofs are those of `R2.EvOZ` with `VzTm`, `VzB`, `RstK.pkgVz`
(Lemma IMG below `VzB ρ`), `rsStep_Vz` (Lemma RS).

* `vzB_omega` (**`B(x)` is the least value of `φ(ω, ·)` above `x`**), `vz_ups_omega` (every `υ`-point is a value
  of `φ(ω, ·)`), `vzv_repB`, `VzOrec`, `vzOrec_le` (`VzOrec(λ) ≤ VzB(ρ_λ)`), `vzOrec_succ`, `VzLam` (`Λ_B`: the least restart index
  with `VzOrec(λ) = VzB(ρ_λ)`), `vzTopIn`, `vzRsIn`, `vzSpec`;
* `vzBlk` (**BLK^O with `VzOrec` below `υ_B` for every `B ≤ Λ_B`**), `vzCore`, `vzLam_lt_Om1`, `vzReach_Orec`;
* `vzOrec_eq_OrecZ`, `vzLamZ_lt_Lam` (`Λ_{ζ_{x+1}} < Λ_B`), `vzOrec_LamZ`;
* `VzLamT t` (**the frontier of a term `t`**), `vzOrec_LamT'` (**`VzOrec(Λ_t) = t(ρ_{Λ_t})`**), `vzLamT_lt_Lam`,
  `vzReach_LamT` (**the reach at every frontier**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})`), `vzBlk_LamT`, `vzLamT_mono`,
  `vzLamT_strict`;
* the frontiers of `ϑˣ(Ω₁·n)`: `vzLamT_zz` (`Λ` of `ϑˣ(Ω₁·2) = ζ_{x+1}` is `Λ_{ζ_{x+1}}`), `vzReach_LamN`
  (`lh(ρ) = δ + ϑᵖ(Ω₁·n)` at `Λ_{ϑˣ(Ω₁·n)}`), `vzLamN_strict` (`Λ_{ϑˣ(Ω₁·n)} < Λ_{ϑˣ(Ω₁·(n+1))} < Λ_B`);
* `vzNuC_bound` (**`υ_{Λ_B} ≤ ρ_L < ν_C`**).

No new axiom beyond `R2.CitedVz`.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order VzTm

/-- Every ordinal below `VzB ρ` is a term value at `ρ`. -/
theorem vzv_repB {ρ : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) {v : Ordinal.{0}} (hv : v < VzB ρ) :
    ∃ t : VzTm, CBt t ρ ∧ val t ρ = v := by
  obtain ⟨N, hN⟩ := vzB_lt_iff.1 hv
  have hN' : v < vt ρ (Om1 * ((max N 1 : ℕ) : Ordinal.{0}) + 0) :=
    hN.trans_le (vzN_le hρ hρ1 (le_max_left N 1))
  exact vzv_rep hρ hρ1 (le_max_right N 1) v hN'

/-- **`VzB x` is the least value of `φ(ω, ·)` above `x`**: `VzB x = sup_N ϑˣ(Ω₁·N)`, each `ϑˣ(Ω₁·N)` the least
value of `φ_N` above `x` (`vz_th_least`). -/
theorem vzB_omega {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    VzB x ∈ Set.range (veblen ω) ∧ x < VzB x ∧ ∀ u ∈ Set.range (veblen ω), x < u → VzB x ≤ u := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have hfa : ∀ N : ℕ, 1 ≤ N → VzP N (vt x (Om1 * (N : Ordinal.{0}) + 0)) ∧ x < vt x (Om1 * (N : Ordinal.{0}) + 0) :=
    fun N hN => ⟨(vz_th_least hx hx1 hN).1, (vz_th_least hx hx1 hN).2.1⟩
  have hxB : x < VzB x := (hfa 1 le_rfl).2.trans_le (vzN_le_B x 1)
  refine ⟨?_, hxB, fun u hu hxu => Ordinal.iSup_le (fun N => ?_)⟩
  · refine (mem_range_veblen omega0_ne_zero).2 (fun b hb => ?_)
    obtain ⟨k, rfl⟩ := lt_omega0.1 hb
    refine le_antisymm ?_ (right_le_veblen _ _)
    have hlim : IsSuccLimit (VzB x) := by
      refine Ordinal.isSuccLimit_iff.2 ⟨(lt_of_le_of_lt zero_le hxB).ne', ?_⟩
      refine isSuccPrelimit_of_succ_lt (fun a ha => ?_)
      obtain ⟨N, hN⟩ := vzB_lt_iff.1 ha
      have hN' := hN.trans_le (vzN_le hx hx1 (le_max_left N 1))
      have hE := vzP_E (le_max_right N 1) (hfa _ (le_max_right N 1)).1
      exact ((ev_isSuccLimit_of_inE hE).succ_lt hN').trans_le (vzN_le_B x _)
    rw [(isNormal_veblen _).apply_of_isSuccLimit hlim]
    refine Ordinal.iSup_le (fun j => ?_)
    obtain ⟨N, hN⟩ := vzB_lt_iff.1 j.2
    set N' := max N (k + 1) with hN'
    have hjN : j.1 < vt x (Om1 * (N' : Ordinal.{0}) + 0) := hN.trans_le (vzN_le hx hx1 (le_max_left _ _))
    have hP : VzP (k + 1) (vt x (Om1 * (N' : Ordinal.{0}) + 0)) :=
      vzP_mono (by omega) (le_max_right _ _) (hfa N' (by omega)).1
    have hfix := vzP_succ.1 hP
    refine (le_of_lt ?_).trans (vzN_le_B x N')
    have := (veblen_lt_veblen_iff_right (o := (k : Ordinal.{0}))).2 hjN
    rwa [hfix] at this
  · rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine (vzN_le hx hx1 (Nat.zero_le 1)).trans ?_
      have hu1 : VzP 1 u := by
        have := (mem_range_veblen omega0_ne_zero).1 hu 0 omega0_pos
        refine vzP_succ.2 ?_
        simpa using this
      exact (vz_th_least hx hx1 le_rfl).2.2 u hu1 hxu
    · have huN : VzP N u := by
        obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
        refine vzP_succ.2 ?_
        exact (mem_range_veblen omega0_ne_zero).1 hu k (natCast_lt_omega0 k)
      exact (vz_th_least hx hx1 hN).2.2 u huN hxu

/-- **Every `υ`-point is a fixed point of every `φ(n, ·)`, `n < ω`** (`u ≤₁ u·(n+1)` in `R₁⁺`, `vz_le1R_level`). -/
theorem vz_ups_omega {u : Ordinal.{0}} (hu : UpsPt u) : u ∈ Set.range (veblen ω) := by
  refine (mem_range_veblen omega0_ne_zero).2 (fun b hb => ?_)
  obtain ⟨k, rfl⟩ := lt_omega0.1 hb
  have hP : VzP (k + 1) u :=
    vz_le1R_level (k + 1) (by omega) u hu.1 (hu.2 _ (vz_le_mul (by omega)))
  exact vzP_succ.1 hP

/-! ## The recursion -/

/-- `s` is realized cofinally below `λ` by the offsets `O`. -/
def VzCofReal (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (s : VzTm) : Prop :=
  ∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l ∧ CBt s (upsilon μ) ∧ val s (upsilon μ) ≤ O μ

/-- The set whose supremum is `VzOrec(λ)`. -/
def VzOSet (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  insert 1 {w | ∃ s, CBt s (upsilon l) ∧ VzCofReal O l s ∧ w = val s (upsilon l) + 1}

theorem VzOSet_congr {O O' : Ordinal.{0} → Ordinal.{0}} {l : Ordinal.{0}}
    (h : ∀ μ < l, O μ = O' μ) : VzOSet O l = VzOSet O' l := by
  have key : ∀ s, VzCofReal O l s ↔ VzCofReal O' l s := by
    intro s
    constructor
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [← h μ h3]; exact h5⟩
    · intro hc ν hν
      obtain ⟨μ, h1, h2, h3, h4, h5⟩ := hc ν hν
      exact ⟨μ, h1, h2, h3, h4, by rw [h μ h3]; exact h5⟩
  ext w
  simp only [VzOSet, Set.mem_insert_iff, Set.mem_setOf_eq, key]

/-- **The recursive offset over `VzTm`**, by well-founded recursion. -/
noncomputable def VzOrec : Ordinal.{0} → Ordinal.{0} :=
  Ordinal.lt_wf.fix (fun l IH => sSup (VzOSet (fun μ => if h : μ < l then IH μ h else 0) l))

theorem vzOrec_eq (l : Ordinal.{0}) : VzOrec l = sSup (VzOSet VzOrec l) := by
  show Ordinal.lt_wf.fix _ l = _
  rw [WellFounded.fix_eq]
  rw [VzOSet_congr (O' := VzOrec) (fun μ hμ => by simp only [hμ, dite_true]; rfl)]

theorem VzOSet_bdd (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l))
    (hl1 : upsilon l < Om1) : ∀ w ∈ VzOSet O l, w ≤ VzB (upsilon l) := by
  intro w hw
  rcases hw with rfl | ⟨s, hCB, -, rfl⟩
  · exact (one_le_iff_pos.2 hl.pos).trans ((vzv_lt_B hl hl1 (t := bs) trivial).le)
  · exact add_one_le_of_lt (vzv_lt_B hl hl1 hCB)

theorem VzOSet_bddAbove (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) (hl : InE (upsilon l))
    (hl1 : upsilon l < Om1) : BddAbove (VzOSet O l) := ⟨_, VzOSet_bdd O l hl hl1⟩

/-- `VzOrec(λ) ≤ VzB(ρ)`. -/
theorem vzOrec_le {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    VzOrec l ≤ VzB (upsilon l) := by
  rw [vzOrec_eq]
  exact csSup_le ⟨1, Set.mem_insert _ _⟩ (VzOSet_bdd _ l (ups_inE hl) (ups_lt_Om1 l hl1))

theorem one_le_vzOrec {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) : 1 ≤ VzOrec l := by
  rw [vzOrec_eq]
  exact le_csSup (VzOSet_bddAbove _ l (ups_inE hl) (ups_lt_Om1 l hl1)) (Set.mem_insert _ _)

theorem lt_vzOrec_of_cof {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) {s : VzTm}
    (hCB : CBt s (upsilon l)) (hc : VzCofReal VzOrec l s) : val s (upsilon l) < VzOrec l := by
  have h1 : val s (upsilon l) + 1 ≤ VzOrec l := by
    rw [vzOrec_eq]
    exact le_csSup (VzOSet_bddAbove _ l (ups_inE hl) (ups_lt_Om1 l hl1))
      (Set.mem_insert_of_mem _ ⟨s, hCB, hc, rfl⟩)
  exact lt_of_lt_of_le (lt_add_one _) h1

theorem lt_vzOrec {l z : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hz : z < VzOrec l) :
    z = 0 ∨ ∃ s, CBt s (upsilon l) ∧ VzCofReal VzOrec l s ∧ z ≤ val s (upsilon l) := by
  rw [vzOrec_eq] at hz
  obtain ⟨w, hw, hzw⟩ :=
    (lt_csSup_iff (VzOSet_bddAbove _ l (ups_inE hl) (ups_lt_Om1 l hl1)) ⟨1, Set.mem_insert _ _⟩).1 hz
  rcases hw with rfl | ⟨s, hCB, hc, rfl⟩
  · left; exact le_antisymm (Order.lt_add_one_iff.1 (by rw [zero_add]; exact hzw)) zero_le
  · right; exact ⟨s, hCB, hc, Order.lt_add_one_iff.1 hzw⟩

/-- `VzOrec = 1` at a successor restart index. -/
theorem vzOrec_succ {l : Ordinal.{0}} (hl : IsRestartIdx l) (h2 : cL l < 2) : VzOrec l = 1 := by
  obtain ⟨l0, hl0, rfl⟩ := succ_ri hl h2
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hS : VzOSet VzOrec (l0 + ω * ω) = {1} := by
    ext w
    simp only [VzOSet, Set.mem_insert_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro (h | ⟨s, -, hc, -⟩)
      · exact h
      · exfalso
        obtain ⟨μ, hμ, h1, h3, -, -⟩ := hc l0 (lt_add_of_pos_right l0 hww)
        exact absurd h3 (not_lt.2 (next_mult (mult_of hl0) (ri_iff.1 hμ).2 h1))
    · intro h; exact Or.inl h
  rw [vzOrec_eq, hS, csSup_singleton]

/-! ## The frontier `Λ_B` -/

/-- `Λ_B`: the least restart index `λ` with `VzOrec(λ) = VzB(ρ_λ)` (`Ω₁` if there is none). -/
noncomputable def VzLam : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ VzOrec l = VzB (upsilon l)})

theorem vzLam_le_Om1 : VzLam ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

/-- **Below `Λ_B` the value is `< VzB(ρ)`.** -/
theorem vzOrec_lt_top {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < VzLam) :
    VzOrec l < VzB (upsilon l) := by
  rcases (vzOrec_le hl (hlV.trans_le vzLam_le_Om1)).lt_or_eq with h | h
  · exact h
  · exact absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _
      (show l ∈ {l | IsRestartIdx l ∧ VzOrec l = VzB (upsilon l)} from ⟨hl, h⟩)))
      (not_le.2 hlV)

theorem vzLam_spec (h : VzLam < Om1) :
    IsRestartIdx VzLam ∧ VzOrec VzLam = VzB (upsilon VzLam) := by
  rcases csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ VzOrec l = VzB (upsilon l)})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

/-! ## The inputs of Lemmas TOP and RS -/

/-- **The input of Lemma TOP** at a restart index `λ < Ω₁` with `VzOrec(λ) < VzB(ρ)`. -/
theorem vzTopIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1)
    (hlt : VzOrec l < VzB (upsilon l)) : TopInH VzOrec l := by
  classical
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have hρE : InE (upsilon l) := upsPt_inE hρU
  have hone : 1 ≤ VzOrec l := one_le_vzOrec hl hl1
  obtain ⟨s, hCB, hev⟩ := vzv_repB hρE (ups_lt_Om1 l hl1) hlt
  have hpk : RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) →
      ImgPkg (upsilon l) (upsilon (l + ω + 1)) (val s) := fun R =>
    R.pkgVz hCB (by rw [hev]; exact hone)
  have hnot : ¬ VzCofReal VzOrec l s := fun hc =>
    absurd (lt_vzOrec_of_cof hl hl1 hCB hc) (by rw [hev]; exact lt_irrefl _)
  obtain ⟨m0, hm0, hm0c⟩ := list_max (cst' s) _ (cbt_cst s _ hCB) hρU.1
  unfold VzCofReal at hnot
  push Not at hnot
  obtain ⟨ν, hνl, hν⟩ := hnot
  have hνρ : upsilon ν < upsilon l := upsilon_normal.strictMono hνl
  refine ⟨val s, max (upsilon ν) m0, hev.symm, max_lt hνρ hm0, fun μ hμ hμl hx0 => ?_, hpk⟩
  have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (le_max_left _ _) hx0)
  have hCBμ : CBt s (upsilon μ) :=
    cbt_iff s _ _ hCB (fun c hc => lt_of_le_of_lt ((hm0c c hc).trans (le_max_right _ _)) hx0)
  exact hν μ hμ hνμ hμl hCBμ

/-- **The input of Lemma RS at a limit restart index `λ`** for `VzOrec`. -/
theorem vzRsIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (h2 : 2 ≤ cL l) :
    RsInGen VzOrec l := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρ0 : 0 < upsilon l := (upsPt_upsilon hl0).1
  intro z hz
  rcases lt_vzOrec hl hl1 hz with rfl | ⟨s, hCB, hc, hzs⟩
  · refine ⟨OT.ev (OT.k 0), zero_le, fun R htg => rs_rstT R hρ0 htg, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -⟩ := cL_dense hl le_rfl (lt_of_lt_of_le one_lt_two h2) ν hν
    exact ⟨μ, hμ, h1, h3, by rw [OT.ev_k]; exact zero_le⟩
  · refine ⟨val s, hzs, rsStep_Vz hCB, fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h3, -, h5⟩ := hc ν hν
    exact ⟨μ, hμ, h1, h3, h5⟩

theorem vzOrec_lt_δ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) :
    VzOrec l < upsilon (l + ω + 1) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρU := upsPt_upsilon hl0
  have h1 : l < l + ω := lt_add_of_pos_right l omega0_pos
  have hτU := upsPt_upsilon (hl0.trans h1)
  exact lt_of_le_of_lt ((vzOrec_le hl hl1).trans (vzB_le_next (upsPt_inE hρU) (ups_lt_Om1 l hl1)
    (upsilon_normal.strictMono h1) hτU.2)) (upsilon_normal.strictMono (lt_add_one _))

/-- **`VzOrec` is a general offset specification up to `B`** when every restart index below `B` has the input of
Lemma TOP. -/
theorem vzSpec {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1)
    (hB : ∀ l, IsRestartIdx l → l < B → TopInH VzOrec l) : OffSpecGen VzOrec B where
  mult := hm
  cnt := hc
  le := fun _ hl hlB => vzOrec_lt_δ hl (hlB.trans hc)
  one := fun _ hl hlB => one_le_vzOrec hl (hlB.trans hc)
  top := hB
  succ := fun _ hl _ h2 => vzOrec_succ hl h2
  rs := fun _ hl hlB h2 => vzRsIn hl (hlB.trans hc) h2

theorem vzSpec_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ VzLam) :
    OffSpecGen VzOrec B :=
  vzSpec hm hc (fun _ hl hlB => vzTopIn hl (hlB.trans hc) (vzOrec_lt_top hl (lt_of_lt_of_le hlB hB)))

/-! ## Theorem BLK^O up to `Λ_B` -/

/-- **Theorem BLK^O with `VzOrec` below `υ_B` for every `B ≤ Λ_B`** (`ω² ∣ B`, `B < Ω₁`) in `R₂^C`. -/
theorem vzBlk {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ VzLam) :
    (∀ c d, c < d → d < upsilon B → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < B ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < B →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon B, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen (vzSpec_of_le hm hc hB)

/-- **CORE-C up to `Λ_B`**. -/
theorem vzCore {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ VzLam) :
    Set.Iio (upsilon B) ⊆ Core R2C :=
  core_genGen (vzSpec_of_le hm hc hB)

/-- **`Λ_B < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem vzLam_lt_Om1 : VzLam < Om1 := by
  rcases vzLam_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => vzCore hm hc (by rw [h]; exact hc.le))

theorem vzLam_ri : IsRestartIdx VzLam := (vzLam_spec vzLam_lt_Om1).1

/-- **`VzOrec(Λ_B) = VzB(ρ)`**. -/
theorem vzOrec_Lam : VzOrec VzLam = VzB (upsilon VzLam) := (vzLam_spec vzLam_lt_Om1).2

/-- **The exact reach of every restart below `Λ_B`**: `lh(ρ_λ) = δ_λ + VzOrec(λ)`. -/
theorem vzReach_Orec {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < VzLam) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l) :=
  (vzBlk (ri_iff.1 vzLam_ri).2 vzLam_lt_Om1 le_rfl).2.1 l hl hlV |>.2.2

/-! ## Comparing with `OrecZ` -/

/-- **`VzOrec = OrecZ` below both frontiers** (the reach is unique). -/
theorem vzOrec_eq_OrecZ {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlV : l < VzLam) (hlZ : l < LamZ) :
    VzOrec l = OrecZ l :=
  (add_left_cancel_iff).1 (isReach_unique (vzReach_Orec hl hlV) (reach_OrecZ hl hlZ))

/-- The term `ϑˣ(Ω₁·2)` (`= ζ_{x+1}`). -/
def vzZZ : VzTm := th 2 (cst 0)

theorem val_vzZZ {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : val vzZZ x = evZ x := by
  rw [vzZZ, val_th, val_cst, vz_two_cast, vz_vt_two_eq hx hx1]

theorem CBt_vzZZ {x : Ordinal.{0}} (hx : 0 < x) : CBt vzZZ x := ⟨by norm_num, hx⟩

/-- **`Λ_{ζ_{x+1}} < Λ_B`**. -/
theorem vzLamZ_lt_Lam : LamZ < VzLam := by
  by_contra hle
  push Not at hle
  have hl := vzLam_ri
  have hl1 := vzLam_lt_Om1
  have hρU := ups_ri hl
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 _ hl1
  have hz : evZ (upsilon VzLam) < VzOrec VzLam := by
    rw [vzOrec_Lam, ← val_vzZZ hρE hρ1]; exact vzv_lt_B hρE hρ1 (CBt_vzZZ hρU.1)
  rcases lt_vzOrec hl hl1 hz with h0 | ⟨s, hCB, hcs, hzs⟩
  · exact absurd h0 (evZ_E _).pos.ne'
  obtain ⟨μ, hμ, -, hμl, h3, h4⟩ := hcs 0 (pos_iff_ne_zero.2 hl.1)
  have hμZ : μ < LamZ := lt_of_lt_of_le hμl hle
  rw [vzOrec_eq_OrecZ hμ hμl hμZ] at h4
  have hμE := ups_inE hμ
  have hμ1 := ups_lt_Om1 _ (hμl.trans hl1)
  have h5 : val s (upsilon μ) < val vzZZ (upsilon μ) := by
    rw [val_vzZZ hμE hμ1]; exact lt_of_le_of_lt h4 (OrecZ_lt_top hμ hμZ)
  have h6 := (uniVz_lt (t := s) (u := vzZZ) (ups_ri hμ) hρU (bases_ri hμ hl hμl hl1) h3
    (CBt_vzZZ (ups_ri hμ).1)).2 h5
  rw [val_vzZZ hρE hρ1] at h6
  exact absurd hzs (not_le.2 h6)

/-- **`VzOrec(Λ_{ζ_{x+1}}) = ζ_{ρ+1} = OrecZ(Λ_{ζ_{x+1}})`**. -/
theorem vzOrec_LamZ : VzOrec LamZ = evZ (upsilon LamZ) :=
  (add_left_cancel_iff).1 (isReach_unique (vzReach_Orec LamZ_ri vzLamZ_lt_Lam) vz_reach_LamZ)

/-! ## The frontier of a term -/

/-- **The frontier `Λ_t` of a term `t` of `VzTm`**: the least restart index `λ` with constants of `t` below `ρ_λ`
and `t(ρ_λ) ≤ VzOrec(λ)` (`Ω₁` if there is none). -/
noncomputable def VzLamT (t : VzTm) : Ordinal.{0} :=
  sInf (insert Om1 {l | IsRestartIdx l ∧ CBt t (upsilon l) ∧ val t (upsilon l) ≤ VzOrec l})

theorem vzLamT_le {t : VzTm} {l : Ordinal.{0}} (hl : IsRestartIdx l) (hCB : CBt t (upsilon l))
    (hle : val t (upsilon l) ≤ VzOrec l) : VzLamT t ≤ l :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨hl, hCB, hle⟩)

theorem vzLamT_spec {t : VzTm} (h : VzLamT t < Om1) :
    IsRestartIdx (VzLamT t) ∧ CBt t (upsilon (VzLamT t)) ∧ val t (upsilon (VzLamT t)) ≤ VzOrec (VzLamT t) := by
  rcases csInf_mem (s := insert Om1
    {l | IsRestartIdx l ∧ CBt t (upsilon l) ∧ val t (upsilon l) ≤ VzOrec l})
    ⟨Om1, Set.mem_insert _ _⟩ with h' | h'
  · exact absurd (h' ▸ h : Om1 < Om1) (lt_irrefl _)
  · exact h'

theorem lt_vzv_of_lt_LamT {t : VzTm} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμl : μ < VzLamT t)
    (hCB : CBt t (upsilon μ)) : VzOrec μ < val t (upsilon μ) := by
  by_contra hle
  exact absurd (vzLamT_le hμ hCB (not_lt.1 hle)) (not_le.2 hμl)

/-- **`VzOrec(Λ_t) = t(ρ_{Λ_t})`** (for `Λ_t < Ω₁` and `t(ρ_{Λ_t}) ≥ 1`). -/
theorem vzOrec_LamT {t : VzTm} (hlt : VzLamT t < Om1) (h1 : 1 ≤ val t (upsilon (VzLamT t))) :
    VzOrec (VzLamT t) = val t (upsilon (VzLamT t)) := by
  obtain ⟨hl, hCB, hle⟩ := vzLamT_spec hlt
  set l := VzLamT t with hldef
  refine le_antisymm ?_ hle
  have hρU := ups_ri hl
  obtain ⟨m0, hm0, hm0c⟩ := list_max (cst' t) _ (cbt_cst t _ hCB) hρU.1
  obtain ⟨_, ⟨ν, hν, rfl⟩, hm0ν⟩ := (lt_isLUB_iff (upsilon_limit (ri_limit hl))).1 hm0
  rw [vzOrec_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨s, hsCB, hc, rfl⟩)
  · exact h1
  obtain ⟨μ, hμ, hνμ, hμl, hCBμ, hsμ⟩ := hc ν hν
  have hm0μ : m0 < upsilon μ := hm0ν.trans (upsilon_normal.strictMono hνμ)
  have htμ : CBt t (upsilon μ) := cbt_iff t _ _ hCB (fun c hc => lt_of_le_of_lt (hm0c c hc) hm0μ)
  have h2 : val s (upsilon μ) < val t (upsilon μ) :=
    lt_of_le_of_lt hsμ (lt_vzv_of_lt_LamT hμ hμl htμ)
  have h3 := (uniVz_lt (ups_ri hμ) hρU (bases_ri hμ hl hμl hlt) hCBμ htμ).2 h2
  exact add_one_le_of_lt h3

/-- **`Λ_t < Λ_B`** for every term `t` with constants below `ρ_{Λ_B}` and value `≥ 1`. -/
theorem vzLamT_lt_Lam {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    VzLamT t < VzLam := by
  have hρE := ups_inE vzLam_ri
  have hρ1 := ups_lt_Om1 _ vzLam_lt_Om1
  have hle : VzLamT t ≤ VzLam := vzLamT_le vzLam_ri hCB (by
    rw [vzOrec_Lam]; exact (vzv_lt_B hρE hρ1 hCB).le)
  refine lt_of_le_of_ne hle (fun e => ?_)
  have hlt : VzLamT t < Om1 := e ▸ vzLam_lt_Om1
  have h := vzOrec_LamT hlt (by rw [e]; exact h1)
  rw [e, vzOrec_Lam] at h
  exact absurd h (vzv_lt_B hρE hρ1 hCB).ne'

theorem vzLamT_ri {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    IsRestartIdx (VzLamT t) :=
  (vzLamT_spec ((vzLamT_lt_Lam hCB h1).trans vzLam_lt_Om1)).1

theorem one_le_vzv_LamT {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    1 ≤ val t (upsilon (VzLamT t)) := by
  have hlt := vzLamT_lt_Lam hCB h1
  obtain ⟨hl, hCBl, -⟩ := vzLamT_spec (hlt.trans vzLam_lt_Om1)
  have hB := bases_ri hl vzLam_ri hlt vzLam_lt_Om1
  have h1' : (1 : Ordinal.{0}) < upsilon (VzLamT t) := one_lt_of_upsPt (ups_ri hl)
  exact (uniVz_le (t := cst 1) (u := t) (ups_ri hl) (ups_ri vzLam_ri) hB h1' hCBl).1 h1

/-- **`VzOrec(Λ_t) = t(ρ_{Λ_t})`** for every term with constants below `ρ_{Λ_B}` and value `≥ 1`. -/
theorem vzOrec_LamT' {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    VzOrec (VzLamT t) = val t (upsilon (VzLamT t)) :=
  vzOrec_LamT ((vzLamT_lt_Lam hCB h1).trans vzLam_lt_Om1) (one_le_vzv_LamT hCB h1)

/-- **The reach at the frontier of every term**: `lh(ρ_{Λ_t}) = δ + t(ρ_{Λ_t})` in `R₂^C`. -/
theorem vzReach_LamT {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    IsReach R2C (upsilon (VzLamT t)) (upsilon (VzLamT t + ω + 1) + val t (upsilon (VzLamT t))) := by
  rw [← vzOrec_LamT' hCB h1]
  exact vzReach_Orec (vzLamT_ri hCB h1) (vzLamT_lt_Lam hCB h1)

theorem vzLamT_ww_le {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    VzLamT t + ω * ω ≤ VzLam :=
  next_mult (ri_iff.1 (vzLamT_ri hCB h1)).2 (ri_iff.1 vzLam_ri).2 (vzLamT_lt_Lam hCB h1)

/-- **Theorem BLK^O at the frontier of every term**: BLK^O with `VzOrec` below `υ_{Λ_t+ω²}`. -/
theorem vzBlk_LamT {t : VzTm} (hCB : CBt t (upsilon VzLam)) (h1 : 1 ≤ val t (upsilon VzLam)) :
    (∀ c d, c < d → d < upsilon (VzLamT t + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < VzLamT t + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < VzLamT t + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon (VzLamT t + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  vzBlk (dvd_add (ri_iff.1 (vzLamT_ri hCB h1)).2 (dvd_refl _))
    ((vzLamT_ww_le hCB h1).trans_lt vzLam_lt_Om1) (vzLamT_ww_le hCB h1)

/-- **Monotonicity of the frontier**: `t ≤ t'` at `ρ_{Λ_B}` gives `Λ_t ≤ Λ_{t'}`. -/
theorem vzLamT_mono {t t' : VzTm} (hCB' : CBt t' (upsilon VzLam))
    (h1 : 1 ≤ val t (upsilon VzLam)) (hle : val t (upsilon VzLam) ≤ val t' (upsilon VzLam))
    (hc : CBt t (upsilon (VzLamT t'))) : VzLamT t ≤ VzLamT t' := by
  have h1' : 1 ≤ val t' (upsilon VzLam) := h1.trans hle
  have hlt' := vzLamT_lt_Lam hCB' h1'
  obtain ⟨hl', hCBl', hle'⟩ := vzLamT_spec (hlt'.trans vzLam_lt_Om1)
  have hB := bases_ri hl' vzLam_ri hlt' vzLam_lt_Om1
  have hle2 := (uniVz_le (ups_ri hl') (ups_ri vzLam_ri) hB hc hCBl').1 hle
  exact vzLamT_le hl' hc (hle2.trans hle')

/-- `t < t'` at `ρ_{Λ_B}` gives `Λ_t < Λ_{t'}`. -/
theorem vzLamT_strict {t t' : VzTm} (hCB : CBt t (upsilon VzLam)) (hCB' : CBt t' (upsilon VzLam))
    (h1 : 1 ≤ val t (upsilon VzLam)) (hlt : val t (upsilon VzLam) < val t' (upsilon VzLam))
    (hc : CBt t (upsilon (VzLamT t'))) : VzLamT t < VzLamT t' := by
  refine lt_of_le_of_ne (vzLamT_mono hCB' h1 hlt.le hc) (fun e => ?_)
  have h1' : 1 ≤ val t' (upsilon VzLam) := h1.trans hlt.le
  have hl' := vzLamT_lt_Lam hCB' h1'
  obtain ⟨hlr, hCBl', hle'⟩ := vzLamT_spec (hl'.trans vzLam_lt_Om1)
  have hB := bases_ri hlr vzLam_ri hl' vzLam_lt_Om1
  have h2 := (uniVz_lt (ups_ri hlr) (ups_ri vzLam_ri) hB hc hCBl').1 hlt
  have h3 := vzOrec_LamT' hCB h1
  rw [e] at h3
  rw [h3] at hle'
  exact absurd hle' (not_le.2 h2)

/-! ## The frontiers of `ϑˣ(Ω₁·n)` -/

/-- The term `ϑˣ(Ω₁·n)`. -/
def vzN (n : ℕ) : VzTm := th n (cst 0)

theorem CBt_vzN {n : ℕ} (hn : 1 ≤ n) {x : Ordinal.{0}} (hx : 0 < x) : CBt (vzN n) x := ⟨hn, hx⟩

theorem one_le_vzN {n : ℕ} (hn : 1 ≤ n) {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    1 ≤ val (vzN n) x := by
  have h0T := mem_T_of_le hx hx1 (zero_le : (0 : Ordinal.{0}) ≤ x)
  have := (vz_th_facts hx hx1 hn h0T (Ordinal.omega_pos 1)).2.2.2.1
  rw [vzN, val_th, val_cst]
  exact (one_le_iff_pos.2 hx.pos).trans this.le

/-- **`Λ` of `ϑˣ(Ω₁·2) = ζ_{x+1}` is `Λ_{ζ_{x+1}}`.** -/
theorem vzLamT_zz : VzLamT vzZZ = LamZ := by
  have hZ := LamZ_ri
  have hZ1 : LamZ < Om1 := vzLamZ_lt_Lam.trans vzLam_lt_Om1
  refine le_antisymm (vzLamT_le hZ (CBt_vzZZ (ups_ri hZ).1)
    (by rw [val_vzZZ (ups_inE hZ) (ups_lt_Om1 _ hZ1), vzOrec_LamZ])) ?_
  by_contra hlt
  push Not at hlt
  have hV := vzLamT_lt_Lam (t := vzZZ) (CBt_vzZZ (ups_ri vzLam_ri).1)
    (by rw [val_vzZZ (ups_inE vzLam_ri) (ups_lt_Om1 _ vzLam_lt_Om1)]
        exact (one_le_iff_pos.2 (ups_ri vzLam_ri).1).trans (lt_evZ _).le)
  obtain ⟨hl, -, hle⟩ := vzLamT_spec (hV.trans vzLam_lt_Om1)
  have hl1 : VzLamT vzZZ < Om1 := hV.trans vzLam_lt_Om1
  rw [vzOrec_eq_OrecZ hl hV hlt, val_vzZZ (ups_inE hl) (ups_lt_Om1 _ hl1)] at hle
  exact absurd hle (not_le.2 (OrecZ_lt_top hl hlt))

/-- **The reach at the frontier of `ϑˣ(Ω₁·n)`** (`1 ≤ n`): `lh(ρ) = δ + ϑᵖ(Ω₁·n)` for `ρ = ρ_{Λ_{ϑˣ(Ω₁·n)}}`. -/
theorem vzReach_LamN {n : ℕ} (hn : 1 ≤ n) :
    IsReach R2C (upsilon (VzLamT (vzN n)))
      (upsilon (VzLamT (vzN n) + ω + 1) + vt (upsilon (VzLamT (vzN n))) (Om1 * (n : Ordinal.{0}) + 0)) := by
  have h := vzReach_LamT (t := vzN n) (CBt_vzN hn (ups_ri vzLam_ri).1)
    (one_le_vzN hn (ups_inE vzLam_ri) (ups_lt_Om1 _ vzLam_lt_Om1))
  rwa [vzN, val_th, val_cst] at h

/-- **`Λ_{ϑˣ(Ω₁·n)} < Λ_{ϑˣ(Ω₁·(n+1))} < Λ_B`** for `1 ≤ n`. -/
theorem vzLamN_strict {n : ℕ} (hn : 1 ≤ n) :
    VzLamT (vzN n) < VzLamT (vzN (n + 1)) ∧ VzLamT (vzN (n + 1)) < VzLam := by
  have hρE := ups_inE vzLam_ri
  have hρ1 := ups_lt_Om1 _ vzLam_lt_Om1
  have hρ0 := (ups_ri vzLam_ri).1
  have h2 := vzLamT_lt_Lam (t := vzN (n + 1)) (CBt_vzN (by omega) hρ0) (one_le_vzN (by omega) hρE hρ1)
  refine ⟨vzLamT_strict (CBt_vzN hn hρ0) (CBt_vzN (by omega) hρ0) (one_le_vzN hn hρE hρ1) ?_
    (CBt_vzN hn (ups_ri (vzLamT_ri (t := vzN (n + 1)) (CBt_vzN (by omega) hρ0)
      (one_le_vzN (by omega) hρE hρ1))).1), h2⟩
  rw [vzN, vzN, val_th, val_th, val_cst]
  exact vzN_mono hρE hρ1 (Nat.lt_succ_self n)

/-! ## Where the first non-standard pair lies -/

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_B ≤ L < ξ` restart indices,
`υ_{Λ_B} ≤ ρ_L < ν_C < Ω₁`. -/
theorem vzNuC_bound : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ VzLam ≤ L ∧ L < ξ ∧
    upsilon VzLam ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec (vzSpec_of_le (ri_iff.1 vzLam_ri).2 vzLam_lt_Om1 le_rfl) hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
