import Googology.Trans.PoR.InaccPsi.R2.LrShift
import Googology.Trans.PoR.InaccPsi.R2.YxInd

/-!
# Zc: the realizer maps of the shift with no hypothesis on the standard pairs, and the base reach datum

`Lr.lrReal_shift` asks, for a target `υ_{λ+β}` with `β > ω+1`, the global hypothesis `Cx.CxStdPairTop S`
(every standard pair below `L(ω+1)` is a `≤₂`-pair).  Its proof uses it only for the images of the standard
pairs `υ_{λ+ω·(j+1)} <₂ υ_{λ+ω·(j+1)+1}`, which are the standard pairs `υ_{μ+ω·(j+1)} <₂ υ_{μ+ω·(j+1)+1}` of a
Range restart `μ` below `λ`; these lie below `υ_λ < ν_C`, where every standard pair is a `≤₂`-pair
(`R2.pair_std`).  So:

* `zcReal_shift` (**`LrReal S υ_λ t` for every `t ≤ υ_{λ+β}`, `β ≤ ω²`**): Range restarts `μ` cofinal below
  `υ_λ` with `υ_{μ+β} ≤ r(μ)` and `υ_λ < ν_C`, nothing else (the proof of `Lr.lrReal_shift` with the last
  step replaced by `R2.pair_std`);
* `zcLe1_of_real` (**`a ≤₁ b` from realizers with LOWER only below `a`**): `Lr.lrLe1_of_real` reads LOWER
  only at the restarts `μ` of the realizer maps, and `ρ_μ = D(a) < a`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rm
  Googology.Trans.PoR.InaccPsi.R2.Lr Googology.Trans.PoR.InaccPsi.R2.Rl Googology.Trans.PoR.InaccPsi.R2.Cx
  Googology.Trans.PoR.InaccPsi.R2.Cv

variable {S : InaccSeq.{0}}

/-- **Realizer maps for the targets `t ≤ υ_{λ+β}` (`β ≤ ω²`) at the restart `υ_λ`**, with no hypothesis
on the standard pairs (they are needed only below `υ_λ < ν_C`). -/
theorem zcReal_shift {l β t : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1)
    (hν : upsilon l < nuC) (hβ : β ≤ ω ^ 2) (ht : t ≤ upsilon (l + β))
    (hsup : ∀ γ < upsilon l, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
      upsilon (μ + β) ≤ cdR S μ) :
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
    obtain ⟨-, -, -, -, h5y⟩ := TR _ (hYPC hy)
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
    exact pair_std (Or.inr hμri) j ((hm hKμ).trans hν)

/-- **`a ≤₁ b` from realizer maps with LOWER only at the Range restarts below `a`.** -/
theorem zcLe1_of_real {a b : Ordinal.{0}} (hL : ∀ μ, CdRange S μ → upsilon μ < a → CdLower S μ)
    (hab : a ≤ b) (hP : CvNoPair a b) (hR : LrReal S a b) : le1 a b := by
  classical
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  obtain ⟨D, μ, hD⟩ := hR X Y hX hY hXY
  have himg := Qq.qqImage_fix (Y := Y) hD.fix
  have hiso : ArithIso ↑(X ∪ Y) (D '' ↑(X ∪ Y)) D :=
    ⟨hD.mono.injOn.bijOn_image, hD.mono, fun x hx y hy z hz => hD.add x hx y hy z hz⟩
  have hcl : Closed (D '' ↑(X ∪ Y)) := by
    rintro z ⟨s, hs, rfl⟩ hdz
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hs) with hsX | hsY
    · rw [hD.fix s hsX] at hdz ⊢
      rcases hXY s hs hdz with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact Or.inl h0
      · have hlow : ∀ u ∈ (↑(X ∪ Y) : Set Ordinal.{0}), u < s → u ∈ X := by
          intro u hu hus
          rcases Finset.mem_union.1 (Finset.mem_coe.1 hu) with hu | hu
          · exact hu
          · exact absurd (hus.trans (hX s hsX)) (not_lt.2 (hY u hu).1)
        exact Or.inr ⟨p, ⟨p, hp, hD.fix p (hlow p hp hps)⟩, q, ⟨q, hq, hD.fix q (hlow q hq hqs)⟩,
          hps, hqs, hpq⟩
    · have hdec : DecompR0 s := by
        by_contra hnd
        exact hD.indec s hsY hnd hdz
      have ha0 : (0 : Ordinal.{0}) < a := lt_of_le_of_lt zero_le (hD.below s hsY)
      rcases hXY s hs hdec with h0 | ⟨p, hp, q, hq, hps, hqs, hpq⟩
      · exact absurd (h0 ▸ (hY s hsY).1) (not_le.2 ha0)
      · exact Or.inr ⟨D p, ⟨p, hp, rfl⟩, D q, ⟨q, hq, rfl⟩, hD.mono hp hs hps, hD.mono hq hs hqs,
          (hD.add p hp q hq s hs).1 hpq⟩
  have hYt : ∀ y ∈ Y.image D, y < a := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hD.below y hy
  have hXYt : ∀ x ∈ X, ∀ y ∈ Y.image D, x < y := by
    intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact hD.above y hy x hx
  refine ⟨Y.image D, hYt, hXYt, by rw [himg]; exact hcl, D, ?_⟩
  rw [← himg] at hiso
  have hYmem : ∀ y ∈ Y, y ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := fun y hy =>
    Finset.mem_coe.2 (Finset.mem_union_right _ hy)
  refine cvCov_inner hX (fun y hy => (hY y hy).1) hYt hXYt hiso ?_ ?_ ?_
  · intro y hy y' hy' h1
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · rcases eq_or_lt_of_le (hY y hy).1 with hya | hay
      · subst hya
        have hρa : upsilon μ < a := by rw [← hD.base hy]; exact hD.below _ hy
        have hlow : le1 (upsilon μ) (cdR S μ) := hL _ hD.rng hρa
        have hmono : D a < D y' := hD.mono (hYmem a hy) (hYmem y' hy') hlt
        rw [hD.base hy] at hmono ⊢
        exact le1_of_le_of_le1 hmono.le (hD.bd y' hy') hlow
      · exact hD.pair1 y hy y' hy' hay hlt h1
    · exact le1_refl _
    · exact absurd (le1_le h1) (not_le.2 hgt)
  · intro y hy y' hy' h2
    rcases lt_trichotomy y y' with hlt | rfl | hgt
    · rcases eq_or_lt_of_le (hY y hy).1 with hya | hay
      · subst hya
        exact absurd h2 (hP.2 y' hlt (hY y' hy').2)
      · exact hD.pair2 y hy y' hy' hay hlt h2
    · exact le2_refl _
    · exact absurd (le2_le h2) (not_le.2 hgt)
  · intro x hx y hy h2
    exact absurd h2 (hP.1 x y (hX x hx) (hY y hy).1 (hY y hy).2)


/-- `ω² < υ_λ` at every restart index. -/
theorem zcWW_lt {l : Ordinal.{0}} (hl : IsRestartIdx l) : ω * ω < upsilon l := by
  have hE := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hl.1))
  have hω := omega0_lt_inE hE
  have h2 : ((2 : ℕ) : Ordinal.{0}) < upsilon l := (natCast_lt_omega0 2).trans hω
  have := (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 h2
  rw [hE, Ordinal.opow_natCast, pow_two] at this
  exact this

/-- **The base `≤₁` of a window**: at a restart `υ_λ < ν_C` with the supply `Ra.RaSupAt S υ_λ` and LOWER at
the Range restarts below `υ_λ`, `υ_λ ≤₁ υ_{λ+ω²}`. -/
theorem zcBase_le1 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hsup : Ra.RaSupAt S (upsilon l)) (hL : ∀ μ, CdRange S μ → upsilon μ < upsilon l → CdLower S μ) :
    le1 (upsilon l) (upsilon (l + ω * ω)) := by
  have hm := upsilon_normal.strictMono
  have hsup' : ∀ γ < upsilon l, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧
      upsilon (μ + ω ^ 2) ≤ cdR S μ := by
    intro γ hγ
    obtain ⟨μ, hr, h1, h2, -, h4⟩ := hsup (max γ (ω * ω)) (max_lt hγ (zcWW_lt hl))
    refine ⟨μ, hr, (le_max_left _ _).trans_lt h1, h2, le_trans ?_ h4⟩
    rw [pow_two]
    exact hm.monotone (add_le_add le_rfl (le_max_right _ _))
  have hR : LrReal S (upsilon l) (upsilon (l + ω * ω)) :=
    zcReal_shift (β := ω ^ 2) hl hl1 hν le_rfl (by rw [pow_two]) hsup'
  exact zcLe1_of_real hL (hm.monotone le_self_add) (cvNoPair_of_nu hl rfl (Yx.yxNext_le_nuC hl hν)) hR

/-- **The base reach datum of a window** (`Ys.YsReachIn λ 0 ρ_λ`) from the base `≤₁`. -/
theorem zcBase_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hsup : Ra.RaSupAt S (upsilon l)) (hL : ∀ μ, CdRange S μ → upsilon μ < upsilon l → CdLower S μ) :
    Ys.YsReachIn l 0 (upsilon l) :=
  Ys.ysReach_long (zcBase_le1 hl hl1 hν hsup hL)

end Googology.Trans.PoR.InaccPsi.R2.Zc
