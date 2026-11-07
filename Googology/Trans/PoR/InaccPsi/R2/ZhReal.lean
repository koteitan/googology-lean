import Googology.Trans.PoR.InaccPsi.R2.ZhInner

/-!
# Zh: the realizer maps of the shift for every target `υ_{λ+β}` (generic in `β`), with the carry of the inner
reaches

`Zc.zcReal_shift` gives realizer maps (`Lr.LrReal S υ_λ t`) only for `t ≤ υ_{λ+β}` with `β ≤ ω²`: below
`υ_{λ+ω²}` every point above `υ_λ` lies in a block of `λ`, whose `≤₁` and `≤₂` are those of `R₂^C` below `ν_C`
(`R2.block_le1`, `R2.std_of_lt_nuC`).  For `β > ω²` the interval `[υ_λ, υ_{λ+β})` contains the inner restarts
`υ_{λ+γ}` (`0 < γ < β`, `ω² ∣ γ`); their points other than the bases are again in blocks (of `λ + γ`), but the
bases `υ_{λ+γ}` have their own long reaches, and the map must carry them.  Here:

* `ZhCarry S λ μ β` (**the carry of the inner reaches**): for every inner `γ`, either the inner reach
  `r(λ+γ)` covers the target and then `r(μ+γ)` covers the image target `υ_{μ+β}`, or it has the form
  `υ_{λ+σ} + w` with a small offset `w < ρ_λ` and then `υ_{μ+σ} + w ≤ r(μ+γ)`;
* `ZhUpIn S λ β` (UPPER at the inner restarts of `λ`, as `lh(ρ_{λ+γ}) ≤ r(λ+γ)`);
* `ZhSupAt S λ β` (**the supply**): Range restarts `μ` cofinal below `ρ_λ` with `μ + β ≤ λ`, `υ_{μ+β} ≤ r(μ)`,
  LOWER at the inner restarts `μ + γ` and the carry from `λ` to `μ`;
* `zhReal_gen` (**realizer maps for every `t ≤ υ_{λ+β}`**): from `ρ_λ < ν_C`, `υ_{λ+β} ≤ ν_C`, `ZhUpIn`,
  `ZhSupAt`.  The map is the FRAG move of `Zc.zcReal_shift` with the segment bases of the configuration and
  the small offsets added to the domain (`Ψ(υ_{λ+σ} + w') = υ_{μ+σ} + w'`);
* `zhReal_gen_low`: for `β ≤ ω²` the inner hypotheses are empty (`Zc.zcReal_shift` is the case `β ≤ ω²`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rm
  Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Rl Googology.Trans.PoR.InaccPsi.R2.Cx
  Googology.Trans.PoR.InaccPsi.R2.Cv

variable {S : InaccSeq.{0}}

/-- **The carry of the inner reaches from `λ` to `μ`** below the target `υ_{λ+β}`. -/
def ZhCarry (S : InaccSeq.{0}) (l μ β : Ordinal.{0}) : Prop :=
  ∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β →
    (upsilon (l + β) ≤ cdR S (l + γ) → upsilon (μ + β) ≤ cdR S (μ + γ)) ∧
    (cdR S (l + γ) < upsilon (l + β) → ∃ σ w, w < upsilon l ∧ cdR S (l + γ) = upsilon (l + σ) + w ∧
      upsilon (μ + σ) + w ≤ cdR S (μ + γ))

/-- **UPPER at the inner restarts** `λ + γ` (`0 < γ < β`, `ω² ∣ γ`): `lh(ρ_{λ+γ}) ≤ r(λ+γ)`. -/
def ZhUpIn (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β → ∀ g, le1 (upsilon (l + γ)) g → g ≤ cdR S (l + γ)

/-- **The supply at `ρ_λ` for the target `υ_{λ+β}`**: Range restarts `μ` cofinal below `ρ_λ` with
`μ + β ≤ λ`, `υ_{μ+β} ≤ r(μ)`, LOWER at their inner restarts and the carry from `λ` to `μ`. -/
def ZhSupAt (S : InaccSeq.{0}) (l β : Ordinal.{0}) : Prop :=
  ∀ x < upsilon l, ∃ μ, CdRange S μ ∧ x < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + β ≤ l ∧
    upsilon (μ + β) ≤ cdR S μ ∧
    (∀ γ, 0 < γ → ω ^ 2 ∣ γ → γ < β → le1 (upsilon (μ + γ)) (cdR S (μ + γ))) ∧ ZhCarry S l μ β

/-- The region of a segment index `ζ ≥ λ`: `λ + γ ≤ ζ < λ + γ + ω²` with `ω² ∣ γ`. -/
theorem zh_region {l ζ : Ordinal.{0}} (h : l ≤ ζ) :
    ∃ γ, ω ^ 2 ∣ γ ∧ l + γ ≤ ζ ∧ ζ < l + γ + ω ^ 2 := by
  have hw : (ω ^ 2 : Ordinal.{0}) ≠ 0 := (pow_pos omega0_pos 2).ne'
  refine ⟨ω ^ 2 * ((ζ - l) / ω ^ 2), dvd_mul_right _ _, ?_, ?_⟩
  · calc l + ω ^ 2 * ((ζ - l) / ω ^ 2) ≤ l + (ζ - l) := add_le_add le_rfl (Ordinal.mul_div_le _ _)
      _ = ζ := Ordinal.add_sub_cancel_of_le h
  · have e : ζ = l + ω ^ 2 * ((ζ - l) / ω ^ 2) + (ζ - l) % ω ^ 2 := by
      rw [add_assoc, Ordinal.div_add_mod, Ordinal.add_sub_cancel_of_le h]
    calc ζ = _ := e
      _ < _ := (add_lt_add_iff_left _).2 (Ordinal.mod_lt _ hw)

theorem zh_ri_add {l γ : Ordinal.{0}} (hl : IsRestartIdx l) (hγ : ω ^ 2 ∣ γ) : IsRestartIdx (l + γ) :=
  ⟨fun h => hl.1 (le_antisymm (by rw [← h]; exact le_self_add) zero_le), dvd_add hl.2 hγ⟩

/-- **Realizer maps for every target `t ≤ υ_{λ+β}`** with the carry of the inner reaches. -/
theorem zhReal_gen {l β t : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hνl : upsilon l < nuC) (hν : upsilon (l + β) ≤ nuC) (ht : t ≤ upsilon (l + β))
    (hU : ZhUpIn S l β) (hsup : ZhSupAt S l β) :
    LrReal S (upsilon l) t := by
  classical
  intro X Y hX hY hXY
  have hm := upsilon_normal.strictMono
  have ha : UpsPt (upsilon l) := upsPt_upsilon (pos_iff_ne_zero.2 hl.1)
  obtain ⟨ξ, hξ, hνe⟩ := nuC_restart
  have htν : t ≤ nuC := ht.trans hν
  have hY1 : ∀ y ∈ Y, y < Om1 := fun y hy =>
    lt_of_lt_of_le (hY y hy).2 (htν.trans nuC_le_Om1)
  -- the blocks of a restart region below `ν_C` lie below `ν_C`
  have hblk : ∀ L, IsRestartIdx L → upsilon L < nuC → ∀ j : ℕ,
      upsilon (L + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
    intro L hL hLν j
    rw [hνe] at hLν ⊢
    have hLξ := hm.lt_iff_lt.1 hLν
    have h2 := lr_dvd_add_le hL.2 hξ.2 hLξ
    refine hm (lt_of_lt_of_le ?_ h2)
    rw [add_assoc]; exact lr_addL (a := L) (lr_omega_mul_add_one_lt (j + 1))
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
  -- the configuration with the segment bases of `Y`
  set Y' := Y ∪ Y.image sb with hY'def
  have hY' : ∀ y ∈ Y', upsilon l ≤ y ∧ y < Om1 ∧ ∃ y0 ∈ Y, y ≤ y0 := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact ⟨(hY y hy).1, hY1 y hy, y, hy, le_rfl⟩
    · obtain ⟨y0, hy0, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨hm.monotone (sbge y0 (hY y0 hy0).1), (hζ1 y0 (hY y0 hy0).1).trans_lt (hY1 y0 hy0), y0, hy0,
        hζ1 y0 (hY y0 hy0).1⟩
  have hYY' : ∀ y ∈ Y, y ∈ Y' := fun y hy => Finset.mem_union_left _ hy
  have hsbY' : ∀ y ∈ Y, sb y ∈ Y' := fun y hy => Finset.mem_union_right _ (Finset.mem_image_of_mem sb hy)
  -- the parameter closure of `Y'`
  obtain ⟨PC, hYPC, hPCb, hPCc⟩ := lr_pc (a := upsilon l) (sb := sb)
    (fun z h h1 p hp => lt_of_lt_of_le (sbPar z h h1 p hp) (hζ1 z h)) Y'
    (fun y hy => ⟨(hY' y hy).1, (hY' y hy).2.1⟩)
  have hPCa : ∀ z ∈ PC, upsilon l ≤ z := fun z hz => (hPCb z hz).1
  have hPCt : ∀ z ∈ PC, z < t := fun z hz => by
    obtain ⟨-, y, hy, hzy⟩ := hPCb z hz
    obtain ⟨-, -, y0, hy0, hyy0⟩ := hY' y hy
    exact lt_of_le_of_lt (hzy.trans hyy0) (hY y0 hy0).2
  have hPC1 : ∀ z ∈ PC, z < Om1 := fun z hz => by
    obtain ⟨-, y, hy, hzy⟩ := hPCb z hz
    exact lt_of_le_of_lt hzy (hY' y hy).2.1
  -- the small offsets of `Y` over their segment bases
  set W := (Y.image (fun y => y - sb y)).filter (· < upsilon l) with hWdef
  -- the base `κ` above `X`, the offsets and the low parameters
  set PL := PC.biUnion (fun z => (Par (sb z) z).filter (· < upsilon l)) with hPL
  set M := ((X ∪ W) ∪ PL).sup id with hMdef
  have hMa : M < upsilon l := by
    refine (Finset.sup_lt_iff ha.1).2 fun x hx => ?_
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 hx with hx | hx
      · exact hX x hx
      · exact (Finset.mem_filter.1 hx).2
    · obtain ⟨z, -, hxz⟩ := Finset.mem_biUnion.1 hx
      exact (Finset.mem_filter.1 hxz).2
  have hMle : ∀ x ∈ (X ∪ W) ∪ PL, x ≤ M := fun x hx => Finset.le_sup (f := id) hx
  obtain ⟨_, ⟨ι, hιl, rfl⟩, hMι, -⟩ := (upsilon_limit (ri_lim hl)).exists_between hMa
  set κ := upsilon (succ ι) with hκdef
  have hκU : UpsPt κ := upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ ι))
  have hMκ : M < κ := hMι.trans (hm (lt_succ ι))
  have hκa : κ < upsilon l := hm ((ri_lim hl).succ_lt hιl)
  have hκ1 : κ < Om1 := hκa.trans hl1
  obtain ⟨μ, hμR, hκμ, hμa, hμβl, hμβ, hLin, hcar⟩ := hsup κ hκa
  have hμri : IsRestartIdx μ := hμR.1
  have hμl : μ < l := hm.lt_iff_lt.1 hμa
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
    refine ⟨upsPt_inE hκU, hκ1, fun k hk => ?_, hbmono, fun k hk => ?_⟩
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [e']; exact ⟨sbU z (hPCa z hz), sb1 z (hPCa z hz) (hPC1 z hz)⟩
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [e']
      exact hκa.trans_le (hm.monotone (sbge z (hPCa z hz)))
  have hcC : Chain κ c m := by
    refine ⟨upsPt_inE hκU, hκ1, fun k hk => ?_, fun j k hjk hk => ?_, fun k hk => ?_⟩
    · obtain ⟨z, hz, e'⟩ := hbz k hk
      rw [hck k hk z hz e']
      refine ⟨upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hμri.1) le_self_add), ?_⟩
      refine lt_of_lt_of_le (hm ?_) (hm.monotone hμβl) |>.trans hl1
      exact lr_addL (a := μ) (hzβ z hz)
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
  set F := (X ∪ W) ∪ PC with hFdef
  have hF : ↑F ⊆ DD κ b m := by
    intro x hx
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
    · exact Iio_sub_DD m (lt_of_le_of_lt (hMle x (Finset.mem_union_left _ hx)) hMκ)
    · obtain ⟨k, hk, -, hxD⟩ := hDDz x hx
      exact DD_mono (show k + 1 ≤ m by omega) hxD
  obtain ⟨Ψ, ⟨Q1, Q2, Q3, Q4, Q5, Q6, -⟩, Q8⟩ := lrFragI hbC hcC F hF
  have hXF : ∀ x ∈ X, x ∈ F := fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hWF : ∀ x ∈ W, x ∈ F := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hPCF : ∀ z ∈ PC, z ∈ F := fun z hz => Finset.mem_union_right _ hz
  have hYF : ∀ y ∈ Y, y ∈ F := fun y hy => hPCF y (hYPC (hYY' y hy))
  have hYPC' : ∀ y ∈ Y, y ∈ PC := fun y hy => hYPC (hYY' y hy)
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
    · have hU' : UpsPt (Ψ z) := by
        rw [hΨe]; exact upsPt_upsilon (lt_of_lt_of_le (pos_iff_ne_zero.2 hμri.1) le_self_add)
      have hzU : UpsPt z := (Q6 z (hPCF z hz)).1 hU'
      rw [hlz]; exact lr_ups_seg hzU (hζ1 z hza) (hζ2 z hza)
  -- images stay below `υ_{μ+β}`
  have hImg : ∀ z ∈ PC, Ψ z < upsilon (μ + β) := by
    intro z hz
    obtain ⟨-, -, -, h4, -⟩ := TR z hz
    refine lt_of_lt_of_le h4 (hm.monotone ?_)
    rw [lr_succ_add]
    exact lr_addLe (a := μ) (Order.succ_le_of_lt (hzβ z hz))
  -- the image of a segment base `υ_{λ+σ}`
  have hBase : ∀ z ∈ PC, ∀ σ, z = upsilon (l + σ) → Ψ z = upsilon (μ + σ) := by
    intro z hz σ hzσ
    obtain ⟨-, -, -, -, h5⟩ := TR z hz
    have hζz : ζf z = l + σ :=
      lr_seg_unique (hζ1 z (hPCa z hz)) (hζ2 z (hPCa z hz)) hzσ.symm.le (hzσ ▸ hm (lt_succ _))
    rw [hζz, Ordinal.add_sub_cancel] at h5
    exact h5.1 hzσ
  refine ⟨Ψ, μ, ⟨fun x hx => Q1 x (hXF x hx) (lt_of_le_of_lt
      (hMle x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))) hMκ), ?_, ?_,
    fun y hy hI => Q8 y (hYF y hy) hI, ?_, ?_, hμR, ?_, ?_, ?_, ?_⟩⟩
  · -- increasing
    refine Q4.2.1.mono ?_
    intro u hu
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
    · exact Finset.mem_coe.2 (hXF u hu)
    · exact Finset.mem_coe.2 (hYF u hu)
  · -- `+`
    have hsub : ∀ u ∈ X ∪ Y, u ∈ F := by
      intro u hu
      rcases Finset.mem_union.1 hu with hu | hu
      · exact hXF u hu
      · exact hYF u hu
    intro x hx y hy z hz
    exact Q4.2.2 x (hsub x hx) y (hsub y hy) z (hsub z hz)
  · -- above `X`
    intro y hy x hx
    obtain ⟨-, -, h3, -, -⟩ := TR y (hYPC' y hy)
    exact (lt_of_le_of_lt (hMle x (Finset.mem_union_left _ (Finset.mem_union_left _ hx))) hMκ).trans
      (hκμ.trans_le ((hm.monotone le_self_add).trans h3))
  · -- below `a`
    intro y hy
    exact (hImg y (hYPC' y hy)).trans_le (hm.monotone hμβl)
  · -- the base
    intro haY
    obtain ⟨-, -, -, -, h5⟩ := TR _ (hYPC' _ haY)
    have hζa : ζf (upsilon l) = l :=
      lr_seg_unique (hζ1 _ le_rfl) (hζ2 _ le_rfl) le_rfl (hm (lt_succ l))
    rw [hζa, Ordinal.sub_self, add_zero, add_zero] at h5
    exact h5.1 rfl
  · -- the bound
    intro y hy
    exact (hImg y (hYPC' y hy)).le.trans hμβ
  · -- `≤₁` on the pairs above `a`
    intro y hy y' hy' hay hyy h1
    have hyF := hYF y hy
    have hy'F := hYF y' hy'
    have hyPC := hYPC' y hy
    have hy'PC := hYPC' y' hy'
    have hΨyy' : Ψ y < Ψ y' := Q4.2.1 (Finset.mem_coe.2 hyF) (Finset.mem_coe.2 hy'F) hyy
    obtain ⟨γ, hγd, hγ1, hγ2⟩ := zh_region (sbge y hay.le)
    have hγβ : γ < β := by
      have h1' : l + γ < l + β := lt_of_le_of_lt hγ1 (by
        have := hzβ y hyPC
        rw [← Ordinal.add_sub_cancel_of_le (sbge y hay.le)]
        exact lr_addL (a := l) this)
      exact (add_lt_add_iff_left l).1 h1'
    have hLri : IsRestartIdx (l + γ) := zh_ri_add hl hγd
    have hLy : upsilon (l + γ) ≤ y := (hm.monotone hγ1).trans (hζ1 y hay.le)
    have hLν : upsilon (l + γ) < nuC := lt_of_le_of_lt hLy (lt_of_lt_of_le (hY y hy).2 htν)
    by_cases hyb : y = upsilon (l + γ)
    · -- an inner base `ρ_{λ+γ}`
      have hγ0 : 0 < γ := by
        rcases eq_or_lt_of_le (zero_le : (0 : Ordinal.{0}) ≤ γ) with h0 | h0
        · rw [← h0, add_zero] at hyb; exact absurd hyb hay.ne'
        · exact h0
      have hy'R : y' ≤ cdR S (l + γ) := hU γ hγ0 hγd hγβ y' (hyb ▸ h1)
      have hΨy : Ψ y = upsilon (μ + γ) := hBase y hyPC γ hyb
      have hLμ := hLin γ hγ0 hγd hγβ
      suffices hs : Ψ y' ≤ cdR S (μ + γ) by
        rw [hΨy] at hΨyy' ⊢
        exact le1_of_le_of_le1 hΨyy'.le hs hLμ
      obtain ⟨hc1, hc2⟩ := hcar γ hγ0 hγd hγβ
      rcases le_or_gt (upsilon (l + β)) (cdR S (l + γ)) with hbig | hsmall
      · exact (hImg y' hy'PC).le.trans (hc1 hbig)
      · obtain ⟨σ, w, hw, hRe, hRμ⟩ := hc2 hsmall
        have hy'a : upsilon l ≤ y' := (hY y' hy').1
        rcases lt_or_ge y' (upsilon (l + σ)) with hlo | hhi
        · have hζ' : ζf y' < l + σ := hm.lt_iff_lt.1 (lt_of_le_of_lt (hζ1 y' hy'a) hlo)
          have hd : ζf y' - l < σ := by
            rw [← Ordinal.add_sub_cancel_of_le (sbge y' hy'a)] at hζ'
            exact (add_lt_add_iff_left l).1 hζ'
          obtain ⟨-, -, -, h4, -⟩ := TR y' hy'PC
          refine (lt_of_lt_of_le h4 (hm.monotone ?_)).le.trans (le_self_add.trans hRμ)
          rw [lr_succ_add]
          exact lr_addLe (a := μ) (Order.succ_le_of_lt hd)
        · have hy'le : y' ≤ upsilon (l + σ) + w := hRe ▸ hy'R
          have hseg2 : y' < upsilon (succ (l + σ)) := by
            have hI := indec_of_upsPt (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_succ (l + σ))))
            have hσs : upsilon (l + σ) < upsilon (succ (l + σ)) := hm (lt_succ _)
            have hwσ : w < upsilon (succ (l + σ)) :=
              hw.trans_le (hm.monotone ((le_self_add).trans (le_succ _)))
            exact lt_of_le_of_lt hy'le (hI.add_lt hσs hwσ)
          have hζy' : ζf y' = l + σ :=
            lr_seg_unique (hζ1 y' hy'a) (hζ2 y' hy'a) hhi hseg2
          have hsb : sb y' = upsilon (l + σ) := by simp only [hsbdef, hζy']
          have hw'le : y' - sb y' ≤ w := by
            rw [hsb]; exact Ordinal.sub_le.2 hy'le
          have hw'W : y' - sb y' ∈ W :=
            Finset.mem_filter.2 ⟨Finset.mem_image_of_mem (fun y => y - sb y) hy', hw'le.trans_lt hw⟩
          have hsbPC : sb y' ∈ PC := hYPC (hsbY' y' hy')
          have hΨw : Ψ (y' - sb y') = y' - sb y' :=
            Q1 _ (hWF _ hw'W) (lt_of_le_of_lt
              (hMle _ (Finset.mem_union_left _ (Finset.mem_union_right _ hw'W))) hMκ)
          have hΨsb : Ψ (sb y') = upsilon (μ + σ) := hBase _ hsbPC σ hsb
          have hadd : sb y' + (y' - sb y') = y' := Ordinal.add_sub_cancel_of_le (hsb ▸ hhi)
          have hΨ := (Q4.2.2 _ (hPCF _ hsbPC) _ (hWF _ hw'W) _ hy'F).1 hadd
          rw [hΨsb, hΨw] at hΨ
          rw [← hΨ]
          exact (add_le_add le_rfl hw'le).trans hRμ
    · -- a point of a block of the region of `λ + γ`
      have hlt : upsilon (l + γ) < y := lt_of_le_of_ne hLy (Ne.symm hyb)
      have hy2 : y < upsilon (l + γ + ω ^ 2) :=
        lt_of_lt_of_le (hζ2 y hay.le) (hm.monotone (Order.succ_le_of_lt hγ2))
      obtain ⟨j, hj1, hj2⟩ := lr_block hLri hlt hy2
      have hC := hblk (l + γ) hLri hLν j
      obtain ⟨hcap, hR⟩ := (block_le1 (Or.inr hLri) j hC hj1 hj2 y').1 h1
      obtain ⟨h1y, h2y, h3y, h4y, h5y⟩ := TR y hyPC
      have hμγl : μ + γ < l := lt_of_lt_of_le (lr_addL (a := μ) hγβ) hμβl
      have hμγri : IsRestartIdx (μ + γ) := zh_ri_add hμri hγd
      have hKμ : μ + γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l := by
        rw [add_assoc (μ + γ)]
        refine lt_of_lt_of_le (lr_addL (a := μ + γ) (lr_omega_mul_add_one_lt (j + 1))) ?_
        exact lr_dvd_add_le hμγri.2 hl.2 hμγl
      have hCμ : upsilon (μ + γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := (hm hKμ).trans hνl
      have hlow : upsilon (botI (μ + γ) j) < Ψ y := by
        rw [lr_botI (l + γ) j, add_assoc] at hj1
        rw [lr_botI (μ + γ) j, add_assoc]
        exact lr_tr_lower h2y h3y h5y hj1
      have hup : ∀ {w : Ordinal.{0}}, w ∈ PC →
          w ≤ upsilon (l + γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) →
          Ψ w ≤ upsilon (μ + γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
        intro w hw hwK
        obtain ⟨h1w, -, -, h4w, h5w⟩ := TR w hw
        have e1 : l + γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 =
            l + (γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by simp only [add_assoc]
        have e2 : μ + γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 =
            μ + (γ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by simp only [add_assoc]
        rw [e1] at hwK
        rw [e2]
        exact lr_tr_upper h1w h4w h5w hwK
      exact (block_le1 (Or.inr hμγri) j hCμ hlow (hup hyPC hj2) (Ψ y')).2
        ⟨hup hy'PC hcap, (Q5 y hyF y' hy'F).1 hR⟩
  · -- `≤₂` on the pairs above `a`: standard pairs go to standard pairs
    intro y hy y' hy' hay hyy h2
    have hy'ν : y' < nuC := lt_of_lt_of_le (hY y' hy').2 htν
    have hyPC := hYPC' y hy
    have hy'PC := hYPC' y' hy'
    obtain ⟨μ0, j, hμ0, rfl, rfl⟩ := std_of_lt_nuC hy'ν hyy h2
    have hμ0d : ω ^ 2 ∣ μ0 := by
      rcases hμ0 with h | h
      · rw [h]; exact dvd_zero _
      · exact h.2
    have h1' : l < μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) := hm.lt_iff_lt.1 hay
    have hlμ0 : l ≤ μ0 := by
      by_contra hlt
      have h3 := lr_dvd_add_le hμ0d hl.2 (not_le.1 hlt)
      exact absurd (lt_of_lt_of_le (lr_addL (a := μ0) (lr_omega_mul_lt (j + 1))) h3) (not_lt.2 h1'.le)
    obtain ⟨γ0, rfl⟩ : ∃ γ0, μ0 = l + γ0 := ⟨μ0 - l, (Ordinal.add_sub_cancel_of_le hlμ0).symm⟩
    have hγ0d : ω ^ 2 ∣ γ0 := (dvd_add_iff hl.2 (c := γ0)).1 hμ0d
    have hy'lt : l + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l + β :=
      hm.lt_iff_lt.1 (lt_of_lt_of_le (hY _ hy').2 ht)
    have hoff : γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < β := by
      have e : l + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 =
          l + (γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by simp only [add_assoc]
      rw [e] at hy'lt
      exact (add_lt_add_iff_left l).1 hy'lt
    have e1 : Ψ (upsilon (l + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}))) =
        upsilon (μ + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0})) := by
      have e : l + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) = l + (γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0})) :=
        add_assoc _ _ _
      have := hBase _ hyPC (γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0})) (by rw [e])
      rw [this, add_assoc]
    have e2 : Ψ (upsilon (l + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) =
        upsilon (μ + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
      have e : l + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 =
          l + (γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by simp only [add_assoc]
      have := hBase _ hy'PC (γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) (by rw [e])
      rw [this]; simp only [add_assoc]
    rw [e1, e2]
    have hKμ : μ + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l := by
      have e : μ + γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 =
          μ + (γ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by simp only [add_assoc]
      rw [e]
      exact lt_of_lt_of_le (lr_addL (a := μ) hoff) hμβl
    have hri : μ + γ0 = 0 ∨ IsRestartIdx (μ + γ0) := Or.inr (zh_ri_add hμri hγ0d)
    exact pair_std hri j ((hm hKμ).trans hνl)

/-- **For `β ≤ ω²` the inner hypotheses are empty**: no `γ` with `0 < γ < β` is a multiple of `ω²`. -/
theorem zh_noInner {β γ : Ordinal.{0}} (hβ : β ≤ ω ^ 2) (hγ0 : 0 < γ) (hγd : ω ^ 2 ∣ γ) : ¬ γ < β := by
  intro hγβ
  obtain ⟨q, rfl⟩ := hγd
  have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at hγ0; exact lt_irrefl _ hγ0
  have : ω ^ 2 ≤ ω ^ 2 * q := le_mul_of_one_le_right zero_le (Order.one_le_iff_ne_zero.2 hq)
  exact absurd (lt_of_lt_of_le hγβ hβ) (not_lt.2 this)

/-- **Non-vacuity: the case `β ≤ ω²`** (the hypotheses of `Zc.zcReal_shift` give those of `zhReal_gen`, the
inner ones being empty). -/
theorem zhSupAt_low {l β : Ordinal.{0}} (hl : IsRestartIdx l) (hβ : β ≤ ω ^ 2)
    (hsup : ∀ x < upsilon l, ∃ μ, CdRange S μ ∧ x < upsilon μ ∧ upsilon μ < upsilon l ∧
      upsilon (μ + β) ≤ cdR S μ) : ZhSupAt S l β ∧ ZhUpIn S l β := by
  refine ⟨fun x hx => ?_, fun γ hγ0 hγd hγβ => absurd hγβ (zh_noInner hβ hγ0 hγd)⟩
  obtain ⟨μ, hR, h1, h2, h3⟩ := hsup x hx
  have hμl : μ < l := upsilon_normal.strictMono.lt_iff_lt.1 h2
  refine ⟨μ, hR, h1, h2, (add_le_add le_rfl hβ).trans (lr_dvd_add_le hR.1.2 hl.2 hμl), h3,
    fun γ hγ0 hγd hγβ => absurd hγβ (zh_noInner hβ hγ0 hγd),
    fun γ hγ0 hγd hγβ => absurd hγβ (zh_noInner hβ hγ0 hγd)⟩

/-- **`zhReal_gen` contains `Zc.zcReal_shift`**: for `β ≤ ω²`. -/
theorem zhReal_gen_low {l β t : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hνl : upsilon l < nuC) (hβ : β ≤ ω ^ 2) (ht : t ≤ upsilon (l + β))
    (hsup : ∀ x < upsilon l, ∃ μ, CdRange S μ ∧ x < upsilon μ ∧ upsilon μ < upsilon l ∧
      upsilon (μ + β) ≤ cdR S μ) : LrReal S (upsilon l) t := by
  have hm := upsilon_normal.strictMono
  obtain ⟨ξ, hξ, hνe⟩ := nuC_restart
  have hν : upsilon (l + β) ≤ nuC := by
    rw [hνe] at hνl ⊢
    exact hm.monotone ((add_le_add le_rfl hβ).trans (lr_dvd_add_le hl.2 hξ.2 (hm.lt_iff_lt.1 hνl)))
  exact zhReal_gen hl hl1 hνl hν ht (zhSupAt_low hl hβ hsup).2 (zhSupAt_low hl hβ hsup).1

end Googology.Trans.PoR.InaccPsi.R2.Zh
