import Googology.Trans.PoR.InaccPsi.R2.LrCfg
import Googology.Trans.PoR.InaccPsi.R2.LrFragI
import Googology.Trans.PoR.InaccPsi.R2.NuRst

/-!
# Realizer maps past `a^∞`: the FRAG move with shifted `υ`-indices

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`a = υ_λ` is a restart (`λ` a restart index), `a^∞ = υ_{λ+1}`.  `Lc.lcReal_blk` realizes the targets
up to `a^∞` by one base change; `Lc.lcTB_gap` shows that one base change cannot do more.  Here the map
for a configuration `X ∪ Y` (`X < a ≤ Y < t`) is Theorem FRAG (`R2.lrFragI`, with indecomposability)
for the chain of the segment bases of `Y` and of its iterated parameters, `b_k = υ_{λ+γ_k}`, sent to
`c_k = υ_{μ+γ_k}`, where `μ` is a restart of the Range below `a` above `X` and the parameters.  The
shift of the `υ`-indices by the restart offset keeps the blocks of `R₂^C` below `ν_C`
(`R2.block_le1`: in a block of the region of a restart, `≤₁` is `≤₁` of `R₁⁺` capped at the block end),
and keeps the standard pairs.

* `lrReal_shift` (**`LrReal S υ_λ t` for every `t ≤ υ_{λ+β}`, `β ≤ ω²`**), given: Range restarts `μ`
  cofinal below `υ_λ` with `υ_{μ+β} ≤ r(μ)` (the bound clause), `υ_λ < ν_C`, and, when `β > ω+1`,
  `CxStdPairTop` (the images of the standard pairs are `≤₂`-pairs) and `υ_λ ≤ L(ω+1)`;
* `lrReal_shift0` (**`LrReal S υ_λ t` for every `t ≤ υ_{λ+ω+1}`**, from `RmCof S υ_λ` and `υ_λ < ν_C`
  alone: `υ_{μ+ω+1} = δ_μ ≤ r(μ)`, and no `≤₂`-pair of `R₂^C` lies in `(υ_λ, υ_{λ+ω+1})`);
* the arithmetic of restart indices (`lr_dvd_add_le`, `lr_region_eq`), segments (`lr_seg`,
  `lr_inSeg`, `lr_seg_unique`, `lr_ups_seg`), blocks (`lr_block`, `lr_botI`), the transfer of block
  bounds along the shift (`lr_tr_lower`, `lr_tr_upper`), the parameter closure (`lr_pc_one`, `lr_pc`).

No new axiom (the cited facts are those of `R2.Cited`, `R2.CitedL`, `R2.CitedR1`, through FRAG and
`R2.block_le1`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rm

variable {S : InaccSeq.{0}}

/-! ## Restart indices -/

/-- Two multiples of `ω²`: `μ < λ` gives `μ + ω² ≤ λ`. -/
theorem lr_dvd_add_le {μ l : Ordinal.{0}} (hμ : ω ^ 2 ∣ μ) (hl : ω ^ 2 ∣ l) (h : μ < l) :
    μ + ω ^ 2 ≤ l := by
  obtain ⟨p, rfl⟩ := hμ
  obtain ⟨q, rfl⟩ := hl
  have hpq : p < q := by
    by_contra hqp
    exact absurd (mul_le_mul_of_nonneg_left (not_lt.1 hqp) zero_le) (not_le.2 h)
  rw [← mul_add_one]
  exact mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt hpq) zero_le

theorem lr_addL {a b c : Ordinal.{0}} (h : b < c) : a + b < a + c := (add_lt_add_iff_left a).2 h

theorem lr_addLe {a b c : Ordinal.{0}} (h : b ≤ c) : a + b ≤ a + c := add_le_add le_rfl h

theorem lr_omega_mul_lt (n : ℕ) : ω * (n : Ordinal.{0}) < ω ^ 2 := by
  rw [pow_two]; exact (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 n)

theorem lr_omega_mul_add_one_lt (n : ℕ) : ω * (n : Ordinal.{0}) + 1 < ω ^ 2 := by
  refine lt_of_le_of_lt (lr_addLe (a := _) one_lt_omega0.le) ?_
  rw [← mul_add_one]
  have := lr_omega_mul_lt (n + 1)
  rwa [Nat.cast_succ] at this

/-- A restart region `[υ_{μ₀}, υ_{μ₀+ω²})` that meets `(λ, λ + ω²)` at an offset `δ < ω²` is that of `λ`. -/
theorem lr_region_eq {μ0 l δ : Ordinal.{0}} (hμ0 : ω ^ 2 ∣ μ0) (hl : ω ^ 2 ∣ l) (hδ : δ < ω ^ 2)
    (h1 : l < μ0 + δ) (h2 : μ0 + δ < l + ω ^ 2) : μ0 = l := by
  rcases lt_trichotomy μ0 l with h | h | h
  · exact absurd h1 (not_lt.2 ((lr_addL (a := μ0) hδ).trans_le (lr_dvd_add_le hμ0 hl h)).le)
  · exact h
  · exact absurd (h2.trans_le ((lr_dvd_add_le hl hμ0 h).trans le_self_add)) (lt_irrefl _)

theorem lr_ri_add {l : Ordinal.{0}} (hl : IsRestartIdx l) : IsRestartIdx (l + ω ^ 2) :=
  ⟨fun h => (pow_pos omega0_pos 2).ne' (le_antisymm (h ▸ le_add_self) zero_le),
    dvd_add hl.2 (dvd_refl _)⟩

theorem lr_succ_add (μ γ : Ordinal.{0}) : succ (μ + γ) = μ + succ γ := by
  rw [Order.succ_eq_add_one, Order.succ_eq_add_one, add_assoc]

/-! ## Segments -/

/-- A point `y ≥ a` (`a` a `υ`-point) lies in the segment of a `υ`-point: `υ_ζ ≤ y < υ_{ζ+1}`, `ζ > 0`. -/
theorem lr_seg {a y : Ordinal.{0}} (ha : UpsPt a) (hay : a ≤ y) :
    ∃ ζ, 0 < ζ ∧ upsilon ζ ≤ y ∧ y < upsilon (succ ζ) := by
  set s := {ι | y < upsilon ι} with hs
  have hne : s.Nonempty := ⟨succ y, lt_of_lt_of_le (lt_succ y) upsilon_normal.strictMono.le_apply⟩
  have hmem : sInf s ∈ s := csInf_mem hne
  have hbelow : ∀ ι < sInf s, upsilon ι ≤ y := by
    intro ι hι
    have h := notMem_of_lt_csInf hι (OrderBot.bddBelow s)
    exact not_lt.1 h
  obtain ⟨ι0, hι0, rfl⟩ := upsPt_iff_upsilon.1 ha
  rcases zero_or_succ_or_isSuccLimit (sInf s) with h0 | ⟨ζ, hζ⟩ | hlim
  · have h : y < upsilon (sInf s) := hmem
    rw [h0, upsilon_zero] at h
    exact absurd h (not_lt.2 zero_le)
  · have hζs : ζ < sInf s := hζ ▸ lt_succ ζ
    have h2 : y < upsilon (succ ζ) := by rw [hζ]; exact hmem
    refine ⟨ζ, pos_iff_ne_zero.2 fun e => ?_, hbelow ζ hζs, h2⟩
    rw [e] at h2
    have : ι0 < succ 0 := upsilon_normal.strictMono.lt_iff_lt.1 (lt_of_le_of_lt hay h2)
    exact absurd (Order.lt_succ_iff.1 this) (not_le.2 hι0)
  · have hle : upsilon (sInf s) ≤ y :=
      (upsilon_limit hlim).2 (by rintro _ ⟨ι, hι, rfl⟩; exact hbelow ι hι)
    exact absurd hmem (not_lt.2 hle)

theorem lr_inSeg {ζ y : Ordinal.{0}} (h1 : upsilon ζ ≤ y) (h2 : y < upsilon (succ ζ))
    (hy : y < Om1) : InSeg (upsilon ζ) y :=
  ⟨h1, hy, fun u hu hu' => lt_of_lt_of_le h2 ((upsilon_isNext ζ).2.2 u hu hu')⟩

theorem lr_seg_unique {ζ ζ' y : Ordinal.{0}} (h1 : upsilon ζ ≤ y) (h2 : y < upsilon (succ ζ))
    (h1' : upsilon ζ' ≤ y) (h2' : y < upsilon (succ ζ')) : ζ = ζ' := by
  have hm := upsilon_normal.strictMono
  rcases lt_trichotomy ζ ζ' with h | h | h
  · exact absurd (lt_of_lt_of_le h2 ((hm.monotone (Order.succ_le_of_lt h)).trans h1')) (lt_irrefl _)
  · exact h
  · exact absurd (lt_of_lt_of_le h2' ((hm.monotone (Order.succ_le_of_lt h)).trans h1)) (lt_irrefl _)

/-- A `υ`-point in the segment of `υ_ζ` is `υ_ζ`. -/
theorem lr_ups_seg {ζ z : Ordinal.{0}} (hz : UpsPt z) (h1 : upsilon ζ ≤ z)
    (h2 : z < upsilon (succ ζ)) : z = upsilon ζ := by
  obtain ⟨ι, -, rfl⟩ := upsPt_iff_upsilon.1 hz
  have hm := upsilon_normal.strictMono
  have hle : ζ ≤ ι := hm.le_iff_le.1 h1
  have hlt : ι < succ ζ := hm.lt_iff_lt.1 h2
  rw [le_antisymm (Order.lt_succ_iff.1 hlt) hle]

/-- The index of a `υ`-point. -/
noncomputable def lrIx (u : Ordinal.{0}) : Ordinal.{0} := sInf {ι | upsilon ι = u}

theorem lrIx_up (ζ : Ordinal.{0}) : lrIx (upsilon ζ) = ζ := by
  have e : {ι | upsilon ι = upsilon ζ} = {ζ} := by
    ext ι
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact upsilon_normal.strictMono.injective.eq_iff
  unfold lrIx; rw [e, csInf_singleton]

/-! ## Blocks -/

theorem lr_botI (μ : Ordinal.{0}) (j : ℕ) : botI μ j = μ + botI 0 j := by
  cases j with
  | zero => simp [botI]
  | succ j => simp only [botI, zero_add, add_assoc]

/-- A point of `(υ_λ, υ_{λ+ω²})` lies in a block `j` of the region of `λ`. -/
theorem lr_block {l y : Ordinal.{0}} (hl : IsRestartIdx l) (h1 : upsilon l < y)
    (h2 : y < upsilon (l + ω ^ 2)) :
    ∃ j : ℕ, upsilon (botI l j) < y ∧ y ≤ upsilon (l + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
  classical
  have hm := upsilon_normal.strictMono
  have hlim : IsSuccLimit (l + ω ^ 2) := ri_lim (lr_ri_add hl)
  obtain ⟨_, ⟨ι, hι, rfl⟩, hyι, -⟩ := (upsilon_limit hlim).exists_between h2
  have hlι : l ≤ ι := by
    by_contra h
    exact absurd (h1.trans hyι) (not_lt.2 (hm.monotone (not_le.1 h).le))
  have hδ : ι - l < ω * ω := by
    rw [← pow_two]
    have : l + (ι - l) < l + ω ^ 2 := by rw [Ordinal.add_sub_cancel_of_le hlι]; exact hι
    exact (add_lt_add_iff_left l).1 this
  have hdiv : (ι - l) / ω < ω := (Ordinal.lt_mul_iff_div_lt omega0_ne_zero).1 hδ
  obtain ⟨k, hk⟩ := lt_omega0.1 hdiv
  have hex : ∃ n : ℕ, y ≤ upsilon (l + ω * ((n + 1 : ℕ) : Ordinal.{0}) + 1) := by
    refine ⟨k, hyι.le.trans (hm.monotone ?_)⟩
    have h3 : ι - l < ω * ((k + 1 : ℕ) : Ordinal.{0}) := by
      have := lt_mul_succ_div (ι - l) omega0_ne_zero
      rw [hk, Order.succ_eq_add_one, ← Nat.cast_succ] at this
      exact this
    calc ι = l + (ι - l) := (Ordinal.add_sub_cancel_of_le hlι).symm
      _ ≤ l + ω * ((k + 1 : ℕ) : Ordinal.{0}) := lr_addLe (a := l) h3.le
      _ ≤ l + ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1 := le_self_add
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases hj : Nat.find hex with _ | j
  · simpa [botI] using h1
  · have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
    simp only [botI]
    exact not_le.1 hmin

/-- **The lower block bound along the shift**: `υ_{λ+o} < y` gives `υ_{μ+o} < z`. -/
theorem lr_tr_lower {l μ γ o y z : Ordinal.{0}} (hy2 : y < upsilon (succ (l + γ)))
    (hz1 : upsilon (μ + γ) ≤ z) (heq : y = upsilon (l + γ) ↔ z = upsilon (μ + γ))
    (h : upsilon (l + o) < y) : upsilon (μ + o) < z := by
  have hm := upsilon_normal.strictMono
  have hoγ : o ≤ γ := by
    by_contra hlt
    have : succ (l + γ) ≤ l + o := Order.succ_le_of_lt (lr_addL (a := l) (not_le.1 hlt))
    exact absurd (hy2.trans_le (hm.monotone this)) (not_lt.2 h.le)
  rcases eq_or_lt_of_le hoγ with rfl | hlt
  · have hzne : z ≠ upsilon (μ + o) := fun e => h.ne' (heq.2 e)
    exact lt_of_le_of_ne hz1 (Ne.symm hzne)
  · exact (hm (lr_addL (a := μ) hlt)).trans_le hz1

/-- **The upper block bound along the shift**: `y ≤ υ_{λ+K}` gives `z ≤ υ_{μ+K}`. -/
theorem lr_tr_upper {l μ γ K y z : Ordinal.{0}} (hy1 : upsilon (l + γ) ≤ y)
    (hz2 : z < upsilon (succ (μ + γ))) (heq : y = upsilon (l + γ) ↔ z = upsilon (μ + γ))
    (h : y ≤ upsilon (l + K)) : z ≤ upsilon (μ + K) := by
  have hm := upsilon_normal.strictMono
  have hγK : γ ≤ K := by
    by_contra hlt
    exact absurd (lt_of_lt_of_le (hm (lr_addL (a := l) (not_le.1 hlt))) hy1) (not_lt.2 h)
  rcases eq_or_lt_of_le hγK with rfl | hlt
  · exact (heq.1 (le_antisymm h hy1)).le
  · exact (lt_of_lt_of_le hz2 (hm.monotone (Order.succ_le_of_lt (lr_addL (a := μ) hlt)))).le

/-! ## The parameter closure -/

/-- **The parameters of `y`, iterated, at their own segment bases** form a finite set. -/
theorem lr_pc_one {a : Ordinal.{0}} {sb : Ordinal.{0} → Ordinal.{0}}
    (hsb : ∀ z, a ≤ z → z < Om1 → ∀ p ∈ Par (sb z) z, p < z) :
    ∀ y, a ≤ y → y < Om1 → ∃ P : Finset Ordinal.{0}, y ∈ P ∧ (∀ z ∈ P, a ≤ z ∧ z ≤ y) ∧
      ∀ z ∈ P, ∀ p ∈ Par (sb z) z, a ≤ p → p ∈ P := by
  classical
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hay hy1
  set Q := (Par (sb y) y).filter (a ≤ ·) with hQdef
  have hQ : ∀ p ∈ Q, ∃ P : Finset Ordinal.{0}, p ∈ P ∧ (∀ z ∈ P, a ≤ z ∧ z ≤ p) ∧
      ∀ z ∈ P, ∀ q ∈ Par (sb z) z, a ≤ q → q ∈ P := by
    intro p hp
    obtain ⟨hpP, hap⟩ := Finset.mem_filter.1 hp
    have hpy := hsb y hay hy1 p hpP
    exact IH p hpy hap (hpy.trans hy1)
  choose! g hg1 hg2 hg3 using hQ
  refine ⟨insert y (Q.biUnion g), Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨hay, le_rfl⟩
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.1 hz
      have h := hg2 p hp z hzp
      exact ⟨h.1, h.2.trans (hsb y hay hy1 p (Finset.mem_filter.1 hp).1).le⟩
  · intro z hz q hq haq
    rcases Finset.mem_insert.1 hz with rfl | hz
    · have hqQ : q ∈ Q := Finset.mem_filter.2 ⟨hq, haq⟩
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨q, hqQ, hg1 q hqQ⟩)
    · obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.1 hz
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨p, hp, hg3 p hp z hzp q hq haq⟩)

theorem lr_pc {a : Ordinal.{0}} {sb : Ordinal.{0} → Ordinal.{0}}
    (hsb : ∀ z, a ≤ z → z < Om1 → ∀ p ∈ Par (sb z) z, p < z) (Y : Finset Ordinal.{0})
    (hY : ∀ y ∈ Y, a ≤ y ∧ y < Om1) :
    ∃ P : Finset Ordinal.{0}, Y ⊆ P ∧ (∀ z ∈ P, a ≤ z ∧ ∃ y ∈ Y, z ≤ y) ∧
      ∀ z ∈ P, ∀ p ∈ Par (sb z) z, a ≤ p → p ∈ P := by
  classical
  have h := fun y (hy : y ∈ Y) => lr_pc_one hsb y (hY y hy).1 (hY y hy).2
  choose! g hg1 hg2 hg3 using h
  refine ⟨Y.biUnion g, fun y hy => Finset.mem_biUnion.2 ⟨y, hy, hg1 y hy⟩, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.1 hz
    exact ⟨(hg2 y hy z hzy).1, y, hy, (hg2 y hy z hzy).2⟩
  · intro z hz p hp hap
    obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.1 hz
    exact Finset.mem_biUnion.2 ⟨y, hy, hg3 y hy z hzy p hp hap⟩

/-! ## The shift realizer -/

/-- **Realizer maps for the targets `t ≤ υ_{λ+β}` (`β ≤ ω²`) at the restart `υ_λ`**: the FRAG move
with the segment bases `υ_{λ+γ}` sent to `υ_{μ+γ}`. -/
theorem lrReal_shift {l β t : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hβ : β ≤ ω ^ 2) (ht : t ≤ upsilon (l + β))
    (hsup : ∀ γ < upsilon l, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
      upsilon (μ + β) ≤ cdR S μ)
    (hstd : β ≤ ω + 1 ∨ (Cx.CxStdPairTop S ∧ upsilon l ≤ Nc.ncL S (ω + 1))) :
    LrReal S (upsilon l) t := by
  classical
  intro X Y hX hY hXY
  have hm := upsilon_normal.strictMono
  have ha : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  -- `ν_C` is a restart above `υ_λ`, so `υ_{λ+ω²} ≤ ν_C`
  obtain ⟨ξ, hξ, hνe⟩ := nuC_restart
  have hlξ : l < ξ := hm.lt_iff_lt.1 (hνe ▸ hν)
  have hνbig : upsilon (l + ω ^ 2) ≤ nuC := by
    rw [hνe]; exact hm.monotone (lr_dvd_add_le hl.2 hξ.2 hlξ)
  have htν : t ≤ upsilon (l + ω ^ 2) := ht.trans (hm.monotone (lr_addLe (a := l) hβ))
  have hY1 : ∀ y ∈ Y, y < Om1 := fun y hy =>
    lt_of_lt_of_le (hY y hy).2 ((htν.trans hνbig).trans nuC_le_Om1)
  -- the segment of a point `y ≥ υ_λ`
  choose! ζf hζ0 hζ1 hζ2 using fun y (hy : upsilon l ≤ y) => lr_seg ha hy
  set sb : Ordinal.{0} → Ordinal.{0} := fun z => upsilon (ζf z) with hsbdef
  have sbU : ∀ z, upsilon l ≤ z → UpsPt (sb z) := fun z h => upsPt_upsilon (hζ0 z h)
  have sb1 : ∀ z, upsilon l ≤ z → z < Om1 → sb z < Om1 := fun z h h1 => (hζ1 z h).trans_lt h1
  have sbSeg : ∀ z, upsilon l ≤ z → z < Om1 → InSeg (sb z) z := fun z h h1 =>
    lr_inSeg (hζ1 z h) (hζ2 z h) h1
  have sbT : ∀ z, upsilon l ≤ z → z < Om1 → z ∈ Tset (sb z) := fun z h h1 =>
    ((inSeg_iff (sbU z h) (sb1 z h h1)).1 (sbSeg z h h1)).2.2
  have sbPar : ∀ z, upsilon l ≤ z → z < Om1 → ∀ p ∈ Par (sb z) z, p < sb z := fun z h h1 p hp =>
    Par_sub (upsPt_inE (sbU z h)) (sb1 z h h1) (sbT z h h1) (Finset.mem_coe.2 hp)
  have sbge : ∀ z, upsilon l ≤ z → l ≤ ζf z := by
    intro z h
    by_contra hlt
    have h' : sb z < upsilon l := hm (not_le.1 hlt)
    have := (upsilon_isNext (ζf z)).2.2 _ h' ha
    exact absurd (lt_of_lt_of_le (hζ2 z h) this) (not_lt.2 h)
  -- the parameter closure of `Y`
  obtain ⟨PC, hYPC, hPCb, hPCc⟩ := lr_pc (a := upsilon l) (sb := sb)
    (fun z h h1 p hp => lt_of_lt_of_le (sbPar z h h1 p hp) (hζ1 z h)) Y
    (fun y hy => ⟨(hY y hy).1, hY1 y hy⟩)
  have hPCa : ∀ z ∈ PC, upsilon l ≤ z := fun z hz => (hPCb z hz).1
  have hPCt : ∀ z ∈ PC, z < t := fun z hz => by
    obtain ⟨-, y, hy, hzy⟩ := hPCb z hz
    exact lt_of_le_of_lt hzy (hY y hy).2
  have hPC1 : ∀ z ∈ PC, z < Om1 := fun z hz => by
    obtain ⟨-, y, hy, hzy⟩ := hPCb z hz
    exact lt_of_le_of_lt hzy (hY1 y hy)
  -- the base `κ` above `X` and the low parameters
  set PL := PC.biUnion (fun z => (Par (sb z) z).filter (· < upsilon l)) with hPL
  set M := (X ∪ PL).sup id with hMdef
  have hMa : M < upsilon l := by
    refine (Finset.sup_lt_iff ha.1).2 fun x hx => ?_
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    · obtain ⟨z, -, hxz⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxz).2
  have hMle : ∀ x ∈ X ∪ PL, x ≤ M := fun x hx => Finset.le_sup (f := id) hx
  obtain ⟨_, ⟨ι, hιl, rfl⟩, hMι, -⟩ := (upsilon_limit (ri_lim hl)).exists_between hMa
  set κ := upsilon (succ ι) with hκdef
  have hκU : UpsPt κ := upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι))
  have hMκ : M < κ := hMι.trans (hm (lt_succ ι))
  have hκa : κ < upsilon l := hm ((ri_lim hl).succ_lt hιl)
  have hκ1 : κ < Om1 := hκa.trans hl1
  obtain ⟨μ, hμR, hκμ, hμa, hμβ⟩ := hsup κ hκa
  have hμri : IsRestartIdx μ := hμR.1
  have hμl : μ < l := hm.lt_iff_lt.1 hμa
  have hμ2 : μ + ω ^ 2 ≤ l := lr_dvd_add_le hμri.2 hl.2 hμl
  -- the chain `b` of segment bases, sorted
  set B := PC.image sb with hBdef
  set m := B.card with hmdef
  set e := B.orderEmbOfFin rfl with hedef
  set b : ℕ → Ordinal.{0} := fun k => if h : k < m then e ⟨k, h⟩ else 0 with hbdef
  have hbB : ∀ k, k < m → b k ∈ B := by
    intro k hk
    have : e ⟨k, hk⟩ ∈ Set.range e := ⟨_, rfl⟩
    rw [Finset.range_orderEmbOfFin] at this
    simpa only [hbdef, dif_pos hk] using this
  have hBb : ∀ u ∈ B, ∃ k, k < m ∧ b k = u := by
    intro u hu
    have : u ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hu
    obtain ⟨⟨k, hk⟩, rfl⟩ := this
    exact ⟨k, hk, by simp only [hbdef]; exact dif_pos hk⟩
  have hbmono : ∀ j k, j < k → k < m → b j < b k := by
    intro j k hjk hk
    simp only [hbdef, dif_pos (hjk.trans hk), dif_pos hk]
    exact e.strictMono (show (⟨j, hjk.trans hk⟩ : Fin m) < ⟨k, hk⟩ from hjk)
  have hbrefl : ∀ j k, j < m → k < m → b j < b k → j < k := by
    intro j k hj hk hjk
    by_contra hkj
    rcases eq_or_lt_of_le (not_lt.1 hkj) with e' | hlt
    · rw [e'] at hjk; exact lt_irrefl _ hjk
    · exact absurd (hbmono k j hlt hj) (not_lt.2 hjk.le)
  have hbz : ∀ k, k < m → ∃ z ∈ PC, b k = sb z := by
    intro k hk
    obtain ⟨z, hz, e'⟩ := Finset.mem_image.1 (hbB k hk)
    exact ⟨z, hz, e'.symm⟩
  -- the images `c_k = υ_{μ + (ι(b_k) - λ)}`
  set c : ℕ → Ordinal.{0} := fun k => upsilon (μ + (lrIx (b k) - l)) with hcdef
  have hzβ : ∀ z ∈ PC, ζf z - l < β := by
    intro z hz
    have h1 : upsilon (ζf z) < upsilon (l + β) := lt_of_le_of_lt (hζ1 z (hPCa z hz))
      (lt_of_lt_of_le (hPCt z hz) ht)
    have h2 := hm.lt_iff_lt.1 h1
    rw [← Ordinal.add_sub_cancel_of_le (sbge z (hPCa z hz))] at h2
    exact (add_lt_add_iff_left l).1 h2
  have hck : ∀ k, k < m → ∀ z ∈ PC, b k = sb z → c k = upsilon (μ + (ζf z - l)) := by
    intro k _ z _ e'
    simp only [hcdef, e', hsbdef, lrIx_up]
  have hbC : Chain κ b m := by
    refine ⟨hκU, hκ1, fun k hk => ?_, hbmono, fun k hk => ?_⟩
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [e']; exact ⟨sbU z (hPCa z hz), sb1 z (hPCa z hz) (hPC1 z hz)⟩
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [e']
      exact hκa.trans_le (hm.monotone (sbge z (hPCa z hz)))
  have hcC : Chain κ c m := by
    refine ⟨hκU, hκ1, fun k hk => ?_, fun j k hjk hk => ?_, fun k hk => ?_⟩
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [hck k hk z hz e']
      refine ⟨upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hμri.1) le_self_add), ?_⟩
      refine lt_of_lt_of_le (hm ?_) (hm.monotone hμ2) |>.trans hl1
      exact lr_addL (a := μ) ((hzβ z hz).trans_le hβ)
    · obtain ⟨z, hz, e'⟩ := hbz j (hjk.trans hk)
      obtain ⟨z', hz', e''⟩ := hbz k hk
      rw [hck j (hjk.trans hk) z hz e', hck k hk z' hz' e'']
      have hlt : b j < b k := hbmono j k hjk hk
      rw [e', e''] at hlt
      have h1 := hm.lt_iff_lt.1 hlt
      rw [← Ordinal.add_sub_cancel_of_le (sbge z (hPCa z hz)),
        ← Ordinal.add_sub_cancel_of_le (sbge z' (hPCa z' hz'))] at h1
      exact hm (lr_addL (a := μ) ((add_lt_add_iff_left l).1 h1))
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [hck k hk z hz e']
      exact hκμ.trans_le (hm.monotone le_self_add)
  -- the configuration lies in the FRAG domain
  have hDDz : ∀ z, z ∈ PC → ∃ k, k < m ∧ b k = sb z ∧ z ∈ DD κ b (k + 1) := by
    intro z
    induction z using WellFoundedLT.induction with
    | ind z IH =>
    intro hz
    have hza := hPCa z hz
    have hz1 := hPC1 z hz
    obtain ⟨k, hk, hbk⟩ := hBb (sb z) (Finset.mem_image_of_mem sb hz)
    refine ⟨k, hk, hbk, Or.inr ⟨hbk ▸ sbSeg z hza hz1, hbk ▸ sbT z hza hz1, ?_⟩⟩
    rw [hbk]
    intro p hp
    have hpz : p < sb z := sbPar z hza hz1 p (Finset.mem_coe.1 hp)
    by_cases hap : upsilon l ≤ p
    · have hpPC : p ∈ PC := hPCc z hz p (Finset.mem_coe.1 hp) hap
      obtain ⟨j, hj, hbj, hpD⟩ := IH p (lt_of_lt_of_le hpz (hζ1 z hza)) hpPC
      have hjk : j < k := hbrefl j k hj hk (by
        rw [hbj, hbk]; exact lt_of_le_of_lt (hζ1 p hap) hpz)
      exact ClS.sub _ (DD_mono (show j + 1 ≤ k by omega) hpD)
    · have hpPL : p ∈ PL := Finset.mem_biUnion.2 ⟨z, hz, Finset.mem_filter.2
        ⟨Finset.mem_coe.1 hp, not_le.1 hap⟩⟩
      exact ClS.sub _ (Iio_sub_DD k (lt_of_le_of_lt (hMle p (Finset.mem_union_right _ hpPL)) hMκ))
  set F := X ∪ PC with hFdef
  have hF : ↑F ⊆ DD κ b m := by
    intro x hx
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
    · exact Iio_sub_DD m (lt_of_le_of_lt (hMle x (Finset.mem_union_left _ hx)) hMκ)
    · obtain ⟨k, hk, -, hxD⟩ := hDDz x hx
      exact DD_mono (show k + 1 ≤ m by omega) hxD
  obtain ⟨Ψ, ⟨Q1, Q2, Q3, Q4, Q5, Q6, -⟩, Q8⟩ := lrFragI hbC hcC F hF
  have hXF : ∀ x ∈ X, x ∈ F := fun x hx => Finset.mem_union_left _ hx
  have hPCF : ∀ z ∈ PC, z ∈ F := fun z hz => Finset.mem_union_right _ hz
  -- the transfer along the move
  have TR : ∀ z ∈ PC, upsilon (l + (ζf z - l)) ≤ z ∧ z < upsilon (succ (l + (ζf z - l))) ∧
      upsilon (μ + (ζf z - l)) ≤ Ψ z ∧ Ψ z < upsilon (succ (μ + (ζf z - l))) ∧
      (z = upsilon (l + (ζf z - l)) ↔ Ψ z = upsilon (μ + (ζf z - l))) := by
    intro z hz
    have hza := hPCa z hz
    have hz1 := hPC1 z hz
    have hlz := Ordinal.add_sub_cancel_of_le (sbge z hza)
    obtain ⟨k, hk, hbk⟩ := hBb (sb z) (Finset.mem_image_of_mem sb hz)
    have hseg := Q2 k hk z (hPCF z hz) (hbk ▸ sbSeg z hza hz1)
    rw [hck k hk z hz hbk] at hseg
    have hcU : UpsPt (upsilon (succ (μ + (ζf z - l)))) :=
      upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ _))
    refine ⟨by rw [hlz]; exact hζ1 z hza, by rw [hlz]; exact hζ2 z hza, hseg.1,
      hseg.2.2 _ (hm (lt_succ _)) hcU, ⟨fun hze => ?_, fun hΨe => ?_⟩⟩
    · rw [hlz] at hze
      have hsz : sb z = z := hze.symm
      have hbF : b k ∈ F := by rw [hbk, hsz]; exact hPCF z hz
      have h3 := Q3 k hk hbF
      rw [hbk, hck k hk z hz hbk, hsz] at h3
      exact h3
    · have hU : UpsPt (Ψ z) := by
        rw [hΨe]; exact upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hμri.1) le_self_add)
      have hzU : UpsPt z := (Q6 z (hPCF z hz)).1 hU
      rw [hlz]; exact lr_ups_seg hzU (hζ1 z hza) (hζ2 z hza)
  refine ⟨Ψ, μ, ⟨fun x hx => Q1 x (hXF x hx) (lt_of_le_of_lt
      (hMle x (Finset.mem_union_left _ hx)) hMκ), ?_, ?_, fun y hy hI => Q8 y (hPCF y (hYPC hy)) hI,
    ?_, ?_, hμR, ?_, ?_, ?_, ?_⟩⟩
  · -- increasing
    refine Q4.2.1.mono ?_
    intro u hu
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
    · exact Finset.mem_coe.2 (hXF u hu)
    · exact Finset.mem_coe.2 (hPCF u (hYPC hu))
  · -- `+`
    have hsub : ∀ u ∈ X ∪ Y, u ∈ F := by
      intro u hu
      rcases Finset.mem_union.1 hu with hu | hu
      · exact hXF u hu
      · exact hPCF u (hYPC hu)
    intro x hx y hy z hz
    exact Q4.2.2 x (hsub x hx) y (hsub y hy) z (hsub z hz)
  · -- above `X`
    intro y hy x hx
    obtain ⟨-, -, h3, -, -⟩ := TR y (hYPC hy)
    exact (lt_of_le_of_lt (hMle x (Finset.mem_union_left _ hx)) hMκ).trans
      (hκμ.trans_le ((hm.monotone le_self_add).trans h3))
  · -- below `a`
    intro y hy
    obtain ⟨-, -, -, h4, -⟩ := TR y (hYPC hy)
    refine lt_of_lt_of_le h4 (hm.monotone ?_)
    rw [lr_succ_add]
    exact (lr_addLe (a := μ) (Order.succ_le_of_lt ((hzβ y (hYPC hy)).trans_le hβ))).trans hμ2
  · -- the base
    intro haY
    obtain ⟨-, -, -, -, h5⟩ := TR _ (hYPC haY)
    have hζa : ζf (upsilon l) = l :=
      lr_seg_unique (hζ1 _ le_rfl) (hζ2 _ le_rfl) le_rfl (hm (lt_succ l))
    rw [hζa, Ordinal.sub_self, add_zero, add_zero] at h5
    exact h5.1 rfl
  · -- the bound
    intro y hy
    obtain ⟨-, -, -, h4, -⟩ := TR y (hYPC hy)
    refine (lt_of_lt_of_le h4 (hm.monotone ?_)).le.trans hμβ
    rw [lr_succ_add]
    exact lr_addLe (a := μ) (Order.succ_le_of_lt (hzβ y (hYPC hy)))
  · -- `≤₁` on the pairs above `a`: blocks of `R₂^C` below `ν_C`
    intro y hy y' hy' hay hyy h1
    have hy2 : y < upsilon (l + ω ^ 2) := lt_of_lt_of_le (hY y hy).2 htν
    obtain ⟨j, hj1, hj2⟩ := lr_block hl hay hy2
    have hK : l + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l + ω ^ 2 := by
      rw [add_assoc]; exact lr_addL (a := l) (lr_omega_mul_add_one_lt (j + 1))
    have hC : upsilon (l + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := (hm hK).trans_le hνbig
    obtain ⟨hcap, hR⟩ := (block_le1 (Or.inr hl) j hC hj1 hj2 y').1 h1
    obtain ⟨h1y, h2y, h3y, h4y, h5y⟩ := TR y (hYPC hy)
    obtain ⟨h1y', h2y', h3y', h4y', h5y'⟩ := TR y' (hYPC hy')
    have hKμ : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l := by
      rw [add_assoc]
      exact lt_of_lt_of_le (lr_addL (a := μ) (lr_omega_mul_add_one_lt (j + 1))) hμ2
    have hCμ : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := (hm hKμ).trans hν
    have hlow : upsilon (botI μ j) < Ψ y := by
      rw [lr_botI l j] at hj1
      rw [lr_botI μ j]
      exact lr_tr_lower h2y h3y h5y hj1
    have hup : ∀ {w : Ordinal.{0}}, w ∈ Y → w ≤ upsilon (l + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) →
        Ψ w ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
      intro w hw hwK
      obtain ⟨h1w, -, -, h4w, h5w⟩ := TR w (hYPC hw)
      rw [add_assoc] at hwK ⊢
      exact lr_tr_upper h1w h4w h5w hwK
    exact (block_le1 (Or.inr hμri) j hCμ hlow (hup hy hj2) (Ψ y')).2
      ⟨hup hy' hcap, (Q5 y (hPCF y (hYPC hy)) y' (hPCF y' (hYPC hy'))).1 hR⟩
  · -- `≤₂` on the pairs above `a`: standard pairs go to standard pairs
    intro y hy y' hy' hay hyy h2
    have hy'ν : y' < nuC := lt_of_lt_of_le (hY y' hy').2 (htν.trans hνbig)
    obtain ⟨μ0, j, hμ0, rfl, rfl⟩ := std_of_lt_nuC hy'ν hyy h2
    have hμ0d : ω ^ 2 ∣ μ0 := by
      rcases hμ0 with h | h
      · rw [h]; exact dvd_zero _
      · exact h.2
    have hy'lt : μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l + β :=
      hm.lt_iff_lt.1 (lt_of_lt_of_le (hY _ hy').2 ht)
    have h1' : l < μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) := hm.lt_iff_lt.1 hay
    have h2' : μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) < l + ω ^ 2 :=
      (lt_of_le_of_lt le_self_add hy'lt).trans_le (lr_addLe (a := l) hβ)
    have hμ0l : μ0 = l := lr_region_eq hμ0d hl.2 (lr_omega_mul_lt (j + 1)) h1' h2'
    subst hμ0l
    rcases hstd with hβ1 | ⟨hstd, hlL⟩
    · exfalso
      have h3 : μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < μ0 + (ω + 1) :=
        hy'lt.trans_le (lr_addLe (a := μ0) hβ1)
      rw [add_assoc] at h3
      have h4 := (add_lt_add_iff_left μ0).1 h3
      have h5 : ω ≤ ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
        Ordinal.le_mul_left ω (by exact_mod_cast Nat.succ_pos j)
      exact absurd h4 (not_lt.2 (add_le_add h5 le_rfl))
    · obtain ⟨-, -, -, -, h5y⟩ := TR _ (hYPC hy)
      obtain ⟨-, -, -, -, h5y'⟩ := TR _ (hYPC hy')
      have hζy : ζf (upsilon (μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}))) =
          μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
        lr_seg_unique (hζ1 _ hay.le) (hζ2 _ hay.le) le_rfl (hm (lt_succ _))
      have hζy' : ζf (upsilon (μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) =
          μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 :=
        lr_seg_unique (hζ1 _ (hay.trans hyy).le) (hζ2 _ (hay.trans hyy).le) le_rfl (hm (lt_succ _))
      rw [hζy, Ordinal.add_sub_cancel] at h5y
      rw [hζy', add_assoc μ0, Ordinal.add_sub_cancel] at h5y'
      have e1 : Ψ (upsilon (μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}))) =
          upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) := h5y.1 rfl
      have e2 : Ψ (upsilon (μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) =
          upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
        rw [add_assoc, add_assoc]; exact h5y'.1 rfl
      rw [e1, e2]
      have hKμ : μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < μ0 := by
        rw [add_assoc]
        exact lt_of_lt_of_le (lr_addL (a := μ) (lr_omega_mul_add_one_lt (j + 1))) hμ2
      exact Cx.cxStdPair_of_top hstd _ _ (hm (lt_add_one _)) ((hm hKμ).trans_le hlL)
        ⟨μ, j, Or.inr hμri, rfl, rfl⟩

/-- **Realizer maps for the targets `t ≤ υ_{λ+ω+1}`** at a restart `υ_λ` with Range restarts cofinal
below it and `υ_λ < ν_C`: no supply and no `≤₂` hypothesis (`υ_{μ+ω+1} = δ_μ ≤ r(μ)`). -/
theorem lrReal_shift0 {l t : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hc : RmCof S (upsilon l)) (ht : t ≤ upsilon (l + ω + 1)) :
    LrReal S (upsilon l) t := by
  have hβ : ω + 1 ≤ ω ^ 2 := by
    have h := lr_omega_mul_add_one_lt 1
    rw [Nat.cast_one, mul_one] at h
    exact h.le
  refine lrReal_shift (β := ω + 1) hl hl1 hν hβ (by rw [← add_assoc]; exact ht) ?_ (Or.inl le_rfl)
  intro γ hγ
  obtain ⟨μ, hμR, h1, h2⟩ := hc γ hγ
  exact ⟨μ, hμR, h1, h2, by rw [← add_assoc]; exact cdR_ge S μ⟩

end Googology.Trans.PoR.InaccPsi.R2.Lr
