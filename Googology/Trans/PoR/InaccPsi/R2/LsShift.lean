import Googology.Trans.PoR.InaccPsi.R2.LrShift

/-!
# The FRAG shift past the first restart: realizers up to `υ_{λ+β}` for every `β`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`a = υ_λ` is a restart, `λ` a restart index.  `Lr.lrReal_shift` builds the realizer of a configuration
`X ∪ Y` (`X < a ≤ Y < υ_{λ+β}`) by Theorem FRAG (`R2.lrFragI`) on the segment bases `υ_{λ+γ} ↦ υ_{μ+γ}`, for
`β ≤ ω²`.  Past the first restart `υ_{λ+ω²}` the configuration can contain restarts `υ_{λ+g}`
(`ω² ∣ g`, `g > 0`), whose `≤₁`-successors are given by their reach, not by a block.  Here:

* `LsMapW S λ X Y D μ`: the clauses of `Lr.LrMap` with `≤₁` asked only at the left ends `y` that are not
  restarts `υ_{λ+g}`, `0 < g`, `ω² ∣ g`;
* `lsShiftCore` (**the FRAG shift for every `β`**): given Range restarts `μ` cofinal below `υ_λ` with
  `μ + β ≤ λ`, `υ_{μ+β} ≤ r(μ)` and any side condition `Q μ γ` (`γ` the lower bound asked), `υ_λ < ν_C`,
  `υ_{λ+β} ≤ ν_C` and the `≤₂` clause (`β ≤ ω + 1`, or `CxStdPairTop` and `υ_λ ≤ L(ω+1)`), every configuration
  has a map `D` with `LsMapW`, `D(υ_{λ+g}) = υ_{μ+g}`, `D < υ_{μ+β}` on `Y`, and `Q μ γ` for a `γ` above `X`
  (the blocks of every region `λ + ω²·q` are moved by `R2.block_le1`, the standard pairs of every region by
  `CxStdPairTop`);
* `LsCarry S λ β μ γ` (**the carry of the inner reaches**): at every inner offset `g` (`0 < g < β`,
  `ω² ∣ g`), LOWER at `μ + g`, and `r(μ + g)` covers the image of `r(λ + g)`: `υ_{μ+β} ≤ r(μ+g)` when
  `υ_{λ+β} ≤ r(λ+g)`, and `υ_{μ+h} + p ≤ r(μ+g)` when `r(λ+g) = υ_{λ+h} + p` with `p < γ`;
* `lsReal_shiftR` (**`LrReal S υ_λ υ_{λ+β}`**) from UPPER at the inner restarts `λ + g`, the form of their
  reaches (`υ_{λ+β} ≤ r(λ+g)` or `r(λ+g) = υ_{λ+h} + p` with `h < β`, `p < υ_λ`) and Range restarts with the
  carry: the configuration is enlarged by `υ_{λ+h}`, `υ_{λ+h} + p` and `p`, so that FRAG moves
  `r(λ+g) = υ_{λ+h} + p` to `υ_{μ+h} + p` (it keeps `+` and fixes `p`), and UPPER at `λ + g`, LOWER at `μ + g`
  give the `≤₁`-pairs at the restart `υ_{λ+g}`.

No new axiom (the cited facts are those of `R2.Cited`, `R2.CitedL`, `R2.CitedR1` through FRAG and
`R2.block_le1`).  New definitions: `LsMapW`, `LsCarry`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ls

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- The clauses of `Lr.LrMap` for `a = υ_λ`, with `≤₁` asked only at the left ends that are not restarts
`υ_{λ+g}` (`0 < g`, `ω² ∣ g`). -/
structure LsMapW (S : InaccSeq.{0}) (l : Ordinal.{0}) (X Y : Finset Ordinal.{0})
    (D : Ordinal.{0} → Ordinal.{0}) (μ : Ordinal.{0}) : Prop where
  fix : ∀ x ∈ X, D x = x
  mono : StrictMonoOn D ↑(X ∪ Y)
  add : ∀ x ∈ X ∪ Y, ∀ y ∈ X ∪ Y, ∀ z ∈ X ∪ Y, (x + y = z ↔ D x + D y = D z)
  indec : ∀ y ∈ Y, Indec y → Indec (D y)
  above : ∀ y ∈ Y, ∀ x ∈ X, x < D y
  below : ∀ y ∈ Y, D y < upsilon l
  rng : CdRange S μ
  base : upsilon l ∈ Y → D (upsilon l) = upsilon μ
  bd : ∀ y ∈ Y, D y ≤ cdR S μ
  pair1 : ∀ y ∈ Y, ∀ y' ∈ Y, upsilon l < y → y < y' →
    (∀ g, 0 < g → ω ^ 2 ∣ g → y ≠ upsilon (l + g)) → le1 y y' → le1 (D y) (D y')
  pair2 : ∀ y ∈ Y, ∀ y' ∈ Y, upsilon l < y → y < y' → le2 y y' → le2 (D y) (D y')

/-- **The FRAG shift for every `β`.** -/
theorem lsShiftCore {l β : Ordinal.{0}} {Q : Ordinal.{0} → Ordinal.{0} → Prop}
    (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hνβ : upsilon (l + β) ≤ nuC)
    (hsup : ∀ γ < upsilon l, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + β ≤ l ∧
      upsilon (μ + β) ≤ cdR S μ ∧ Q μ γ)
    (hstd : β ≤ ω + 1 ∨ (Cx.CxStdPairTop S ∧ upsilon l ≤ Nc.ncL S (ω + 1)))
    (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < upsilon l)
    (hY : ∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) :
    ∃ D μ γ, Q μ γ ∧ (∀ x ∈ X, x < γ) ∧ γ < upsilon μ ∧ LsMapW S l X Y D μ ∧
      (∀ g, upsilon (l + g) ∈ Y → D (upsilon (l + g)) = upsilon (μ + g)) ∧
      (∀ y ∈ Y, D y < upsilon (μ + β)) := by
  classical
  have hm := upsilon_normal.strictMono
  have ha : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  obtain ⟨ξ, hξ, hνe⟩ := nuC_restart
  have hY1 : ∀ y ∈ Y, y < Om1 := fun y hy =>
    lt_of_lt_of_le (hY y hy).2 (hνβ.trans nuC_le_Om1)
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
  have hPCt : ∀ z ∈ PC, z < upsilon (l + β) := fun z hz => by
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
  obtain ⟨μ, hμR, hκμ, hμa, hμβl, hμβ, hQ⟩ := hsup κ hκa
  have hμri : IsRestartIdx μ := hμR.1
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
    have h1 : upsilon (ζf z) < upsilon (l + β) := lt_of_le_of_lt (hζ1 z (hPCa z hz)) (hPCt z hz)
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
      exact ((hm (lr_addL (a := μ) (hzβ z hz))).trans_le (hm.monotone hμβl)).trans hl1
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
  -- the images lie below `υ_{μ+β}`
  have himg : ∀ y ∈ Y, Ψ y < upsilon (μ + β) := by
    intro y hy
    obtain ⟨-, -, -, h4, -⟩ := TR y (hYPC hy)
    refine lt_of_lt_of_le h4 (hm.monotone ?_)
    rw [lr_succ_add]
    exact lr_addLe (a := μ) (Order.succ_le_of_lt (hzβ y (hYPC hy)))
  -- the restarts and the `υ`-points of the regions move by the shift
  have hres : ∀ g, upsilon (l + g) ∈ Y → Ψ (upsilon (l + g)) = upsilon (μ + g) := by
    intro g hg
    obtain ⟨-, -, -, -, h5⟩ := TR _ (hYPC hg)
    have hlg : upsilon l ≤ upsilon (l + g) := (hY _ hg).1
    have hζ : ζf (upsilon (l + g)) = l + g :=
      lr_seg_unique (hζ1 _ hlg) (hζ2 _ hlg) le_rfl (hm (lt_succ _))
    rw [hζ, Ordinal.add_sub_cancel] at h5
    exact h5.1 rfl
  refine ⟨Ψ, μ, κ, hQ, fun x hx => (hMle x (Finset.mem_union_left _ hx)).trans_lt hMκ, hκμ,
    ⟨fun x hx => Q1 x (hXF x hx) (lt_of_le_of_lt
      (hMle x (Finset.mem_union_left _ hx)) hMκ), ?_, ?_, fun y hy hI => Q8 y (hPCF y (hYPC hy)) hI,
    ?_, fun y hy => (himg y hy).trans_le (hm.monotone hμβl), hμR, ?_,
    fun y hy => (himg y hy).le.trans hμβ, ?_, ?_⟩, hres, himg⟩
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
  · -- the base
    intro haY
    have := hres 0 (by rw [add_zero]; exact haY)
    rwa [add_zero, add_zero] at this
  · -- `≤₁` at the left ends that are not restarts: the blocks of the regions `λ + ω²·q`
    intro y hy y' hy' hay hyy hnr h1
    have hyl : upsilon l ≤ y := hay.le
    set W : Ordinal.{0} := ω ^ 2 with hWdef
    have hW0 : W ≠ 0 := pow_ne_zero 2 omega0_ne_zero
    set d := ζf y - l with hddef
    have hlz : l + d = ζf y := Ordinal.add_sub_cancel_of_le (sbge y hyl)
    have hdm := Ordinal.div_add_mod d W
    set q := d / W
    set r := d % W
    have hrW : r < W := Ordinal.mod_lt d hW0
    set l' := l + W * q with hl'def
    have hl' : IsRestartIdx l' :=
      ⟨fun h => hl.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hl.2 (dvd_mul_right W q)⟩
    have hζ : ζf y = l' + r := by rw [← hlz, ← hdm, add_assoc]
    have hl'y : upsilon l' ≤ y :=
      (hm.monotone (show l' ≤ ζf y by rw [hζ]; exact le_self_add)).trans (hζ1 y hyl)
    have hy1' : upsilon l' < y := by
      rcases eq_or_ne (W * q) 0 with h0 | h0
      · rw [hl'def, h0, add_zero]; exact hay
      · exact lt_of_le_of_ne hl'y fun e => hnr (W * q) (pos_iff_ne_zero.2 h0) (dvd_mul_right W q) e.symm
    have hy2' : y < upsilon (l' + W) := by
      refine (hζ2 y hyl).trans_le (hm.monotone ?_)
      rw [hζ, lr_succ_add]
      exact lr_addLe (a := l') (Order.succ_le_of_lt hrW)
    obtain ⟨j, hj1, hj2⟩ := lr_block hl' hy1' hy2'
    have hKs : l' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l' + W := by
      rw [add_assoc]; exact lr_addL (a := l') (lr_omega_mul_add_one_lt (j + 1))
    have hl'ξ : l' < ξ := by
      have h3 : ζf y < ξ := hm.lt_iff_lt.1 (lt_of_le_of_lt (hζ1 y hyl)
        (lt_of_lt_of_le (hY y hy).2 (hνe ▸ hνβ)))
      exact lt_of_le_of_lt (show l' ≤ ζf y by rw [hζ]; exact le_self_add) h3
    have hC : upsilon (l' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
      rw [hνe]; exact hm (hKs.trans_le (lr_dvd_add_le hl'.2 hξ.2 hl'ξ))
    obtain ⟨hcap, hR⟩ := (block_le1 (Or.inr hl') j hC hj1 hj2 y').1 h1
    obtain ⟨-, h2y, h3y, -, h5y⟩ := TR y (hYPC hy)
    set μ' := μ + W * q with hμ'def
    have hμ' : IsRestartIdx μ' :=
      ⟨fun h => hμri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hμri.2 (dvd_mul_right W q)⟩
    have hdβ : d < β := hzβ y (hYPC hy)
    have hμ'l : μ' < l := by
      have h3 : W * q ≤ d := by rw [← hdm]; exact le_self_add
      exact lt_of_le_of_lt (lr_addLe (a := μ) h3) ((lr_addL (a := μ) hdβ).trans_le hμβl)
    have hKμ : μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l := by
      rw [add_assoc]
      exact lt_of_lt_of_le (lr_addL (a := μ') (lr_omega_mul_add_one_lt (j + 1)))
        (lr_dvd_add_le hμ'.2 hl.2 hμ'l)
    have hCμ : upsilon (μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := (hm hKμ).trans hν
    have e3 : ∀ (x z : Ordinal.{0}), x + W * q + z = x + (W * q + z) := fun x z => add_assoc _ _ _
    have hlow : upsilon (botI μ' j) < Ψ y := by
      rw [lr_botI l' j, hl'def, e3] at hj1
      rw [lr_botI μ' j, hμ'def, e3]
      exact lr_tr_lower h2y h3y h5y hj1
    have hup : ∀ {w : Ordinal.{0}}, w ∈ Y →
        w ≤ upsilon (l' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) →
        Ψ w ≤ upsilon (μ' + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
      intro w hw hwK
      obtain ⟨h1w, -, -, h4w, h5w⟩ := TR w (hYPC hw)
      rw [hl'def, e3, add_assoc l] at hwK
      rw [hμ'def, e3, add_assoc μ]
      exact lr_tr_upper h1w h4w h5w hwK
    exact (block_le1 (Or.inr hμ') j hCμ hlow (hup hy hj2) (Ψ y')).2
      ⟨hup hy' hcap, (Q5 y (hPCF y (hYPC hy)) y' (hPCF y' (hYPC hy'))).1 hR⟩
  · -- `≤₂` on the pairs above `a`: standard pairs of every region go to standard pairs
    intro y hy y' hy' hay hyy h2
    have hy'ν : y' < nuC := lt_of_lt_of_le (hY y' hy').2 hνβ
    obtain ⟨μ0, j, hμ0, rfl, rfl⟩ := std_of_lt_nuC hy'ν hyy h2
    have hμ0d : ω ^ 2 ∣ μ0 := by
      rcases hμ0 with h | h
      · rw [h]; exact dvd_zero _
      · exact h.2
    have hy'lt : μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l + β :=
      hm.lt_iff_lt.1 (hY _ hy').2
    have h1' : l < μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) := hm.lt_iff_lt.1 hay
    have hlμ0 : l ≤ μ0 := by
      by_contra hlt
      have h3 := lr_dvd_add_le hμ0d hl.2 (not_le.1 hlt)
      exact absurd h1' (not_lt.2 ((lr_addL (a := μ0) (lr_omega_mul_lt (j + 1))).le.trans h3))
    obtain ⟨g, rfl⟩ := exists_add_of_le hlμ0
    have hg : ω ^ 2 ∣ g := (dvd_add_iff hl.2).1 hμ0d
    have hgβ : g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < β := by
      rw [add_assoc, add_assoc] at hy'lt
      have := (add_lt_add_iff_left l).1 hy'lt
      rwa [← add_assoc] at this
    rcases hstd with hβ1 | ⟨hstd, hlL⟩
    · exfalso
      have h4 : g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω + 1 := hgβ.trans_le hβ1
      have h5 : ω ≤ g + ω * ((j + 1 : ℕ) : Ordinal.{0}) :=
        (Ordinal.le_mul_left ω (by exact_mod_cast Nat.succ_pos j)).trans le_add_self
      exact absurd h4 (not_lt.2 (add_le_add h5 le_rfl))
    · have e1 : Ψ (upsilon (l + g + ω * ((j + 1 : ℕ) : Ordinal.{0}))) =
          upsilon (μ + g + ω * ((j + 1 : ℕ) : Ordinal.{0})) := by
        have := hres (g + ω * ((j + 1 : ℕ) : Ordinal.{0})) (by rw [← add_assoc]; exact hy)
        rwa [← add_assoc, ← add_assoc] at this
      have e2 : Ψ (upsilon (l + g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) =
          upsilon (μ + g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
        have := hres (g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)
          (by rw [← add_assoc, ← add_assoc]; exact hy')
        rwa [← add_assoc, ← add_assoc, ← add_assoc, ← add_assoc] at this
      rw [e1, e2]
      have hμg : IsRestartIdx (μ + g) :=
        ⟨fun h => hμri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hμri.2 hg⟩
      have hKμ : μ + g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l := by
        have h3 : μ + (g + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < μ + β := lr_addL (a := μ) hgβ
        rw [← add_assoc, ← add_assoc] at h3
        exact h3.trans_le hμβl
      exact Cx.cxStdPair_of_top hstd _ _ (hm (lt_add_one _)) ((hm hKμ).trans_le hlL)
        ⟨μ + g, j, Or.inr hμg, rfl, rfl⟩

/-! ## The carry of the inner reaches -/

/-- **The carry**: at every inner offset `g`, LOWER at `μ + g`, and `r(μ + g)` covers the image of
`r(λ + g)` under the shift (`υ_{λ+h} + p ↦ υ_{μ+h} + p` for `p < γ`). -/
def LsCarry (S : InaccSeq.{0}) (l β μ γ : Ordinal.{0}) : Prop :=
  ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdLower S (μ + g) ∧
    (upsilon (l + β) ≤ cdR S (l + g) → upsilon (μ + β) ≤ cdR S (μ + g)) ∧
    ∀ h p, p < γ → cdR S (l + g) = upsilon (l + h) + p → upsilon (μ + h) + p ≤ cdR S (μ + g)

theorem lsUps_add_lt {ζ p : Ordinal.{0}} (hp : p < upsilon ζ) : upsilon ζ + p < upsilon (succ ζ) :=
  (upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ζ)))).add_lt
    (upsilon_normal.strictMono (lt_succ ζ)) (hp.trans (upsilon_normal.strictMono (lt_succ ζ)))

/-- **Realizer maps up to `υ_{λ+β}`, past the first restart.** -/
theorem lsReal_shiftR {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hνβ : upsilon (l + β) ≤ nuC)
    (hU : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → CdUpper S (l + g))
    (hform : ∀ g, 0 < g → g < β → ω ^ 2 ∣ g → upsilon (l + β) ≤ cdR S (l + g) ∨
      ∃ h p, h < β ∧ p < upsilon l ∧ cdR S (l + g) = upsilon (l + h) + p)
    (hsup : ∀ γ < upsilon l, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + β ≤ l ∧
      upsilon (μ + β) ≤ cdR S μ ∧ LsCarry S l β μ γ)
    (hstd : β ≤ ω + 1 ∨ (Cx.CxStdPairTop S ∧ upsilon l ≤ Nc.ncL S (ω + 1))) :
    LrReal S (upsilon l) (upsilon (l + β)) := by
  classical
  intro X Y hX hY _
  have hm := upsilon_normal.strictMono
  -- the inner restarts of `Y` whose reach has the form `υ_{λ+h} + p`
  set rp : Ordinal.{0} → Prop := fun y => ∃ g, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
    ∃ h p, h < β ∧ p < upsilon l ∧ cdR S (l + g) = upsilon (l + h) + p with hrpdef
  have hch : ∀ y, rp y → ∃ g h p, (0 < g ∧ g < β ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)) ∧
      h < β ∧ p < upsilon l ∧ cdR S (l + g) = upsilon (l + h) + p := by
    rintro y ⟨g, hg, h, p, h1, h2, h3⟩
    exact ⟨g, h, p, hg, h1, h2, h3⟩
  choose! gf hf pf hgf hhf hpf hrf using hch
  set T := Y.filter rp with hTdef
  set Y' := Y ∪ T.image (fun y => upsilon (l + hf y)) ∪ T.image (fun y => upsilon (l + hf y) + pf y)
    with hY'def
  set X' := X ∪ T.image pf with hX'def
  have hX' : ∀ x ∈ X', x < upsilon l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hX x hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact hpf y (Finset.mem_filter.1 hy).2
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · rcases Finset.mem_union.1 hy with hy | hy
      · exact ⟨(hY y hy).1, (hY y hy).2⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
        have hr := (Finset.mem_filter.1 hu).2
        exact ⟨hm.monotone le_self_add, hm (lr_addL (a := l) (hhf u hr))⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
      have hr := (Finset.mem_filter.1 hu).2
      refine ⟨(hm.monotone le_self_add).trans le_self_add, ?_⟩
      refine (lsUps_add_lt ((hpf u hr).trans_le (hm.monotone le_self_add))).trans_le (hm.monotone ?_)
      rw [lr_succ_add]
      exact lr_addLe (a := l) (Order.succ_le_of_lt (hhf u hr))
  obtain ⟨D, μ, γ, hQ, hXγ, -, hW, hres, himg⟩ :=
    lsShiftCore (Q := LsCarry S l β) hl hl1 hν hνβ hsup hstd X' Y' hX' hY'
  have hXX : ∀ x ∈ X, x ∈ X' := fun x hx => Finset.mem_union_left _ hx
  have hYY : ∀ y ∈ Y, y ∈ Y' := fun y hy => Finset.mem_union_left _ (Finset.mem_union_left _ hy)
  have hsub : ∀ u ∈ X ∪ Y, u ∈ X' ∪ Y' := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact Finset.mem_union_left _ (hXX u hu)
    · exact Finset.mem_union_right _ (hYY u hu)
  refine ⟨D, μ, ⟨fun x hx => hW.fix x (hXX x hx), hW.mono.mono fun u hu => hsub u hu,
    fun x hx y hy z hz => hW.add x (hsub x hx) y (hsub y hy) z (hsub z hz),
    fun y hy => hW.indec y (hYY y hy), fun y hy x hx => hW.above y (hYY y hy) x (hXX x hx),
    fun y hy => hW.below y (hYY y hy), hW.rng, fun ha => hW.base (hYY _ ha),
    fun y hy => hW.bd y (hYY y hy), ?_,
    fun y hy y' hy' => hW.pair2 y (hYY y hy) y' (hYY y' hy')⟩⟩
  intro y hy y' hy' hay hyy h1
  by_cases hr : ∃ g, 0 < g ∧ ω ^ 2 ∣ g ∧ y = upsilon (l + g)
  · obtain ⟨g, hg0, hgd, rfl⟩ := hr
    have hgβ : g < β := (add_lt_add_iff_left l).1 (hm.lt_iff_lt.1 (hY _ hy).2)
    have hyr : y' ≤ cdR S (l + g) := cdUpper_iff.1 (hU g hg0 hgβ hgd) y' h1
    obtain ⟨hLow, hbig, hfrm⟩ := hQ g hg0 hgβ hgd
    have hDy : D (upsilon (l + g)) = upsilon (μ + g) := hres g (hYY _ hy)
    have hmono : ∀ u ∈ X' ∪ Y', ∀ v ∈ X' ∪ Y', u ≤ v → D u ≤ D v := fun u hu v hv huv =>
      (hW.mono.le_iff_le (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv)).2 huv
    have hle : D y' ≤ cdR S (μ + g) := by
      rcases hform g hg0 hgβ hgd with hb | ⟨h, p, hh, hp, hrr⟩
      · exact (himg y' (hYY y' hy')).le.trans (hbig hb)
      · have hrp : rp (upsilon (l + g)) := ⟨g, ⟨hg0, hgβ, hgd, rfl⟩, h, p, hh, hp, hrr⟩
        have hT : upsilon (l + g) ∈ T := Finset.mem_filter.2 ⟨hy, hrp⟩
        have hgg : gf (upsilon (l + g)) = g := by
          have e := (hgf _ hrp).2.2.2
          exact (add_left_cancel (hm.injective e)).symm
        have hr' := hrf _ hrp
        rw [hgg] at hr'
        set H := hf (upsilon (l + g))
        set P := pf (upsilon (l + g))
        have hHm : upsilon (l + H) ∈ Y' :=
          Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hT))
        have hSm : upsilon (l + H) + P ∈ Y' :=
          Finset.mem_union_right _ (Finset.mem_image_of_mem
            (fun y => upsilon (l + hf y) + pf y) hT)
        have hPm : P ∈ X' := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hT)
        have hDH : D (upsilon (l + H)) = upsilon (μ + H) := hres H hHm
        have hDP : D P = P := hW.fix P hPm
        have hDS : D (upsilon (l + H) + P) = upsilon (μ + H) + P := by
          have := (hW.add _ (Finset.mem_union_right _ hHm) _ (Finset.mem_union_left _ hPm) _
            (Finset.mem_union_right _ hSm)).1 rfl
          rw [hDH, hDP] at this; exact this.symm
        have h3 : D y' ≤ D (upsilon (l + H) + P) :=
          hmono y' (Finset.mem_union_right _ (hYY y' hy')) _ (Finset.mem_union_right _ hSm)
            (hr' ▸ hyr)
        rw [hDS] at h3
        exact h3.trans (hfrm H P (hXγ P hPm) hr')
    have hge : upsilon (μ + g) ≤ D y' := by
      rw [← hDy]
      exact (hW.mono (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy)))
        (Finset.mem_coe.2 (Finset.mem_union_right _ (hYY _ hy'))) hyy).le
    rw [hDy]
    exact le1_of_le_of_le1 hge hle hLow
  · push Not at hr
    exact hW.pair1 y (hYY y hy) y' (hYY y' hy') hay hyy (fun g hg hgd e => hr g hg hgd e) h1

end Googology.Trans.PoR.InaccPsi.R2.Ls
