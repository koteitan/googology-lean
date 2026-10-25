import Googology.Trans.PoR.InaccPsi.R2.TvShift
import Googology.Trans.PoR.InaccPsi.R2.UbFrag

/-!
# The FRAG shift along an offset map, with the hull isomorphism on every segment

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Tv.tvShiftCore` with `Ub.ubFragV` (FRAG with the hull isomorphism) in place of `Tv.tvFrag`.  One more clause:

* `ubShiftCore` (**`Tv.tvShiftCore` and, for every `y` of the configuration in `seg(υ_{λ+g})` that is the value
  `t[υ_{λ+g}; p]` of a countable-argument term with the argument bounds whose leaves lie in `X ∪ Y`,
  `D y = t[υ_{μ+f(g)}; D p]`**).  The leaves may lie in lower segments `seg(υ_{λ+h})`, `h < g`, i.e. the parameters
  of `y` over `υ_{λ+g}` need not lie below `υ_λ` (non-pure points).

No new axiom (beyond `R2.tvSeg_pi`, through `Ub.ubFragV`).  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ub

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **The FRAG shift along an offset map, with the hull isomorphism on every segment**: the conclusion of
`Tv.tvShiftCore` and, for every countable-argument term `t` with the argument bounds over `υ_{λ+g}`, leaves in
`X ∪ Y` and value `y ∈ Y ∩ seg(υ_{λ+g})`, `D y = t[υ_{μ+f(g)}; D p]` (the image term has the argument bounds). -/
theorem ubShiftCore {l β : Ordinal.{0}}
    {Q : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0} → Prop}
    (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hνβ : upsilon (l + β) ≤ nuC)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ cdR S μ ∧ Sl.SlOff f Os B ∧ Q μ f B γ Os)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1))
    (X Y : Finset Ordinal.{0}) (hX : ∀ x ∈ X, x < upsilon l)
    (hY : ∀ y ∈ Y, upsilon l ≤ y ∧ y < upsilon (l + β)) :
    ∃ D μ f B γ Os, Q μ f B γ Os ∧ (∀ x ∈ X, x < γ) ∧ γ < upsilon μ ∧ Ls.LsMapW S l X Y D μ ∧
      (∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ D (upsilon (l + g)) = upsilon (μ + f g)) ∧
      (∀ y ∈ Y, D y < upsilon (μ + B)) ∧
      (upsilon μ < upsilon l ∧ ∀ y ∈ Y, y < upsilon (succ l) → D y = pi (upsilon μ) (upsilon l) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
        (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) → D y = mv (upsilon (l + g)) (upsilon (μ + f g)) y) ∧
      (∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UbT, UbT.IsA t →
        UbT.WF (upsilon (l + g)) t → UbT.Lv (· ∈ X ∪ Y) t → UbT.ev (upsilon (l + g)) t = y →
        D y = UbT.ev (upsilon (μ + f g)) (t.map D) ∧ UbT.WF (upsilon (μ + f g)) (t.map D)) := by
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
  have hzβ : ∀ z ∈ PC, ζf z - l < β := by
    intro z hz
    have h1 : upsilon (ζf z) < upsilon (l + β) := lt_of_le_of_lt (hζ1 z (hPCa z hz)) (hPCt z hz)
    have h2 := hm.lt_iff_lt.1 h1
    rw [← Ordinal.add_sub_cancel_of_le (sbge z (hPCa z hz))] at h2
    exact (add_lt_add_iff_left l).1 h2
  -- the offsets of the configuration
  set Os : Finset Ordinal.{0} := PC.image (fun z => ζf z - l) with hOsdef
  have hOsβ : ∀ d ∈ Os, d < β := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hd
    exact hzβ z hz
  have hOsm : ∀ z ∈ PC, ζf z - l ∈ insert 0 Os := fun z hz =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)
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
  obtain ⟨μ, f, B, hμR, hκμ, hμa, hμBl, hWB, hμB, hf, hQ⟩ := hsup κ hκa Os hOsβ
  have hμri : IsRestartIdx μ := hμR.1
  have hfB : ∀ z ∈ PC, f (ζf z - l) < B := fun z hz => hf.bd _ (Finset.mem_image_of_mem _ hz)
  have hμf : ∀ z ∈ PC, μ + f (ζf z - l) < l := fun z hz =>
    (lr_addL (a := μ) (hfB z hz)).trans_le hμBl
  -- the chain `b` of segment bases, sorted
  set Bs := PC.image sb with hBdef
  set m := Bs.card with hmdef
  set e := Bs.orderEmbOfFin rfl with hedef
  set b : ℕ → Ordinal.{0} := fun k => if h : k < m then e ⟨k, h⟩ else 0 with hbdef
  have hbB : ∀ k, k < m → b k ∈ Bs := by
    intro k hk
    have : e ⟨k, hk⟩ ∈ Set.range e := ⟨_, rfl⟩
    rw [Finset.range_orderEmbOfFin] at this
    simpa only [hbdef, dif_pos hk] using this
  have hBb : ∀ u ∈ Bs, ∃ k, k < m ∧ b k = u := by
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
  -- the images `c_k = υ_{μ + f(ι(b_k) - λ)}`
  set c : ℕ → Ordinal.{0} := fun k => upsilon (μ + f (lrIx (b k) - l)) with hcdef
  have hck : ∀ k, k < m → ∀ z ∈ PC, b k = sb z → c k = upsilon (μ + f (ζf z - l)) := by
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
      exact (hm (hμf z hz)).trans hl1
    · obtain ⟨z, hz, e'⟩ := hbz j (hjk.trans hk)
      obtain ⟨z', hz', e''⟩ := hbz k hk
      rw [hck j (hjk.trans hk) z hz e', hck k hk z' hz' e'']
      have hlt : b j < b k := hbmono j k hjk hk
      rw [e', e''] at hlt
      have h1 := hm.lt_iff_lt.1 hlt
      rw [← Ordinal.add_sub_cancel_of_le (sbge z (hPCa z hz)),
        ← Ordinal.add_sub_cancel_of_le (sbge z' (hPCa z' hz'))] at h1
      have h2 := (add_lt_add_iff_left l).1 h1
      exact hm (lr_addL (a := μ) (hf.mono (Finset.mem_coe.2 (hOsm z hz))
        (Finset.mem_coe.2 (hOsm z' hz')) h2))
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
  obtain ⟨Ψ, ⟨⟨⟨⟨Q1, Q2, Q3, Q4, Q5, Q6, -⟩, Q8⟩, Q9⟩, Q10⟩, Q11⟩ := ubFragV hbC hcC F hF
  have hXF : ∀ x ∈ X, x ∈ F := fun x hx => Finset.mem_union_left _ hx
  have hPCF : ∀ z ∈ PC, z ∈ F := fun z hz => Finset.mem_union_right _ hz
  -- the transfer along the move
  have TR : ∀ z ∈ PC, upsilon (l + (ζf z - l)) ≤ z ∧ z < upsilon (succ (l + (ζf z - l))) ∧
      upsilon (μ + f (ζf z - l)) ≤ Ψ z ∧ Ψ z < upsilon (succ (μ + f (ζf z - l))) ∧
      (z = upsilon (l + (ζf z - l)) ↔ Ψ z = upsilon (μ + f (ζf z - l))) := by
    intro z hz
    have hza := hPCa z hz
    have hz1 := hPC1 z hz
    have hlz := Ordinal.add_sub_cancel_of_le (sbge z hza)
    obtain ⟨k, hk, hbk⟩ := hBb (sb z) (Finset.mem_image_of_mem sb hz)
    have hseg := Q2 k hk z (hPCF z hz) (hbk ▸ sbSeg z hza hz1)
    rw [hck k hk z hz hbk] at hseg
    have hcU : UpsPt (upsilon (succ (μ + f (ζf z - l)))) :=
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
  -- the images lie below `υ_{μ+B}`
  have himg : ∀ y ∈ Y, Ψ y < upsilon (μ + B) := by
    intro y hy
    obtain ⟨-, -, -, h4, -⟩ := TR y (hYPC hy)
    refine lt_of_lt_of_le h4 (hm.monotone ?_)
    rw [lr_succ_add]
    exact lr_addLe (a := μ) (Order.succ_le_of_lt (hfB y (hYPC hy)))
  -- the `υ`-points of the configuration move along `f`
  have hres : ∀ g, upsilon (l + g) ∈ Y → g ∈ Os ∧ Ψ (upsilon (l + g)) = upsilon (μ + f g) := by
    intro g hg
    obtain ⟨-, -, -, -, h5⟩ := TR _ (hYPC hg)
    have hlg : upsilon l ≤ upsilon (l + g) := (hY _ hg).1
    have hζ : ζf (upsilon (l + g)) = l + g :=
      lr_seg_unique (hζ1 _ hlg) (hζ2 _ hlg) le_rfl (hm (lt_succ _))
    have hOs : ζf (upsilon (l + g)) - l ∈ Os := Finset.mem_image_of_mem _ (hYPC hg)
    rw [hζ, Ordinal.add_sub_cancel] at h5 hOs
    exact ⟨hOs, h5.1 rfl⟩
  -- the lowest segment: `Ψ` is the base change `π_{υ_μ, υ_λ}` there
  have hpi : ∀ y ∈ Y, y < upsilon (succ l) → Ψ y = pi (upsilon μ) (upsilon l) y := by
    intro y hy hys
    have hyl : upsilon l ≤ y := (hY y hy).1
    have hζ : ζf y = l := lr_seg_unique (hζ1 y hyl) (hζ2 y hyl) hyl hys
    obtain ⟨k, hk, hbk, hyD⟩ := hDDz y (hYPC hy)
    have hsb : sb y = upsilon l := by show upsilon (ζf y) = upsilon l; rw [hζ]
    have hk0 : k = 0 := by
      by_contra hk0
      have h0 : b 0 < b k := hbmono 0 k (Nat.pos_of_ne_zero hk0) hk
      obtain ⟨z, hz, e'⟩ := hbz 0 (lt_of_le_of_lt (Nat.zero_le k) hk)
      have h1 : upsilon l ≤ b 0 := by rw [e']; exact hm.monotone (sbge z (hPCa z hz))
      rw [hbk, hsb] at h0
      exact absurd (h1.trans_lt h0) (lt_irrefl _)
    subst hk0
    have hb0 : b 0 = upsilon l := hbk.trans hsb
    have hc0 : c 0 = upsilon μ := by
      show upsilon (μ + f (lrIx (b 0) - l)) = upsilon μ
      rw [hb0, lrIx_up, Ordinal.sub_self, hf.zero, add_zero]
    have hyD1 : y ∈ DD κ b 1 := by simpa using hyD
    rw [Q9 (by omega) y (hPCF y (hYPC hy)) hyD1, hb0, hc0]
    simp only [mv, if_pos hμa]
  -- every segment: `Ψ` is the segment move on the points with parameters below `υ_λ`
  have hmvAll : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) →
      (∀ p ∈ Par (upsilon (l + g)) y, p < upsilon l) →
      Ψ y = mv (upsilon (l + g)) (upsilon (μ + f g)) y := by
    intro y hy g h1 h2 hpar
    have hyl : upsilon l ≤ y := (hY y hy).1
    have hζ : ζf y = l + g := lr_seg_unique (hζ1 y hyl) (hζ2 y hyl) h1 h2
    obtain ⟨k, hk, hbk⟩ := hBb (sb y) (Finset.mem_image_of_mem sb (hYPC hy))
    have hsb : sb y = upsilon (l + g) := by show upsilon (ζf y) = upsilon (l + g); rw [hζ]
    have hck' := hck k hk y (hYPC hy) hbk
    rw [hζ, Ordinal.add_sub_cancel] at hck'
    have hseg : InSeg (b k) y := hbk ▸ sbSeg y hyl (hY1 y hy)
    have hTB : y ∈ TB (b k) κ := by
      refine ⟨hbk ▸ sbT y hyl (hY1 y hy), ?_⟩
      intro p hp
      have hp' : p ∈ Par (sb y) y := by rw [← hbk]; exact Finset.mem_coe.1 hp
      have hpl : p < upsilon l := hpar p (by rw [← hsb]; exact hp')
      have hpPL : p ∈ PL := Finset.mem_biUnion.2 ⟨y, hYPC hy, Finset.mem_filter.2 ⟨hp', hpl⟩⟩
      exact lt_of_le_of_lt (hMle p (Finset.mem_union_right _ hpPL)) hMκ
    rw [Q10 k hk y (hPCF y (hYPC hy)) hseg hTB, hbk, hsb, hck']
  -- every segment: the hull isomorphism on countable-argument terms with leaves in `X ∪ Y`
  have hubAll : ∀ y ∈ Y, ∀ g, upsilon (l + g) ≤ y → y < upsilon (succ (l + g)) → ∀ t : UbT, UbT.IsA t →
      UbT.WF (upsilon (l + g)) t → UbT.Lv (· ∈ X ∪ Y) t → UbT.ev (upsilon (l + g)) t = y →
      Ψ y = UbT.ev (upsilon (μ + f g)) (t.map Ψ) ∧ UbT.WF (upsilon (μ + f g)) (t.map Ψ) := by
    intro y hy g h1 h2 t hA hw hl hev
    have hyl : upsilon l ≤ y := (hY y hy).1
    have hζ : ζf y = l + g := lr_seg_unique (hζ1 y hyl) (hζ2 y hyl) h1 h2
    obtain ⟨k, hk, hbk⟩ := hBb (sb y) (Finset.mem_image_of_mem sb (hYPC hy))
    have hsb : sb y = upsilon (l + g) := by show upsilon (ζf y) = upsilon (l + g); rw [hζ]
    have hck' := hck k hk y (hYPC hy) hbk
    rw [hζ, Ordinal.add_sub_cancel] at hck'
    have hseg : InSeg (b k) y := hbk ▸ sbSeg y hyl (hY1 y hy)
    have hbk' : b k = upsilon (l + g) := hbk.trans hsb
    have hlF : UbT.Lv (· ∈ F) t := UbT.Lv_mono (fun p hp => by
      rcases Finset.mem_union.1 hp with hp | hp
      · exact hXF p hp
      · exact hPCF p (hYPC hp)) t hl
    have hw' : UbT.WF (b k) t := by rw [hbk']; exact hw
    have hev' : UbT.ev (b k) t = y := by rw [hbk']; exact hev
    have e := Q11 k hk t hA hw' hlF (by rw [hev']; exact hPCF y (hYPC hy)) (by rw [hev']; exact hseg)
    rw [hev', hck'] at e
    exact e
  refine ⟨Ψ, μ, f, B, κ, Os, hQ, fun x hx => (hMle x (Finset.mem_union_left _ hx)).trans_lt hMκ, hκμ,
    ⟨fun x hx => Q1 x (hXF x hx) (lt_of_le_of_lt
      (hMle x (Finset.mem_union_left _ hx)) hMκ), ?_, ?_, fun y hy hI => Q8 y (hPCF y (hYPC hy)) hI,
    ?_, fun y hy => (himg y hy).trans_le (hm.monotone hμBl), hμR, ?_,
    fun y hy => (himg y hy).le.trans hμB, ?_, ?_⟩, hres, himg, ⟨hμa, hpi⟩, hmvAll, hubAll⟩
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
    have := (hres 0 (by rw [add_zero]; exact haY)).2
    rwa [add_zero, hf.zero, add_zero] at this
  · -- `≤₁` at the left ends that are not restarts: the blocks of the regions `λ + ω²·q`
    intro y hy y' hy' hay hyy hnr h1
    have hyl : upsilon l ≤ y := hay.le
    have hW0 : (ω ^ 2 : Ordinal.{0}) ≠ 0 := pow_ne_zero 2 omega0_ne_zero
    obtain ⟨d, hd⟩ : ∃ d, ζf y - l = d := ⟨_, rfl⟩
    have hlz : l + d = ζf y := by rw [← hd]; exact Ordinal.add_sub_cancel_of_le (sbge y hyl)
    obtain ⟨q, r, hdm, hrW⟩ : ∃ q r, ω ^ 2 * q + r = d ∧ r < ω ^ 2 :=
      ⟨d / ω ^ 2, d % ω ^ 2, Ordinal.div_add_mod d _, Ordinal.mod_lt d hW0⟩
    have hl' : IsRestartIdx (l + ω ^ 2 * q) :=
      ⟨fun h => hl.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hl.2 (dvd_mul_right _ q)⟩
    have hζ : ζf y = l + ω ^ 2 * q + r := by rw [← hlz, ← hdm, add_assoc]
    have hl'y : upsilon (l + ω ^ 2 * q) ≤ y :=
      (hm.monotone (show l + ω ^ 2 * q ≤ ζf y by rw [hζ]; exact le_self_add)).trans (hζ1 y hyl)
    have hy1' : upsilon (l + ω ^ 2 * q) < y := by
      rcases eq_or_ne (ω ^ 2 * q) 0 with h0 | h0
      · rw [h0, add_zero]; exact hay
      · exact lt_of_le_of_ne hl'y fun e =>
          hnr (ω ^ 2 * q) (pos_iff_ne_zero.2 h0) (dvd_mul_right _ q) e.symm
    have hy2' : y < upsilon (l + ω ^ 2 * q + ω ^ 2) := by
      refine (hζ2 y hyl).trans_le (hm.monotone ?_)
      rw [hζ, lr_succ_add]
      exact lr_addLe (a := l + ω ^ 2 * q) (Order.succ_le_of_lt hrW)
    obtain ⟨j, hj1, hj2⟩ := lr_block hl' hy1' hy2'
    have hKW : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω ^ 2 := lr_omega_mul_add_one_lt (j + 1)
    have hl'ξ : l + ω ^ 2 * q < ξ := by
      have h3 : ζf y < ξ := hm.lt_iff_lt.1 (lt_of_le_of_lt (hζ1 y hyl)
        (lt_of_lt_of_le (hY y hy).2 (hνe ▸ hνβ)))
      exact lt_of_le_of_lt (show l + ω ^ 2 * q ≤ ζf y by rw [hζ]; exact le_self_add) h3
    have hC : upsilon (l + ω ^ 2 * q + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
      rw [hνe, add_assoc (l + ω ^ 2 * q)]
      exact hm ((lr_addL (a := l + ω ^ 2 * q) hKW).trans_le (lr_dvd_add_le hl'.2 hξ.2 hl'ξ))
    obtain ⟨hcap, hR⟩ := (block_le1 (Or.inr hl') j hC hj1 hj2 y').1 h1
    obtain ⟨-, h2y, h3y, -, h5y⟩ := TR y (hYPC hy)
    rw [hd] at h2y h3y h5y
    -- the renamed region `μ + f(ω²·q)`
    have hfd : f d = f (ω ^ 2 * q) + r := by rw [← hdm]; exact hf.res q r hrW
    have hμ' : IsRestartIdx (μ + f (ω ^ 2 * q)) :=
      ⟨fun h => hμri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hμri.2 (hf.dvd q)⟩
    have hdOs : d ∈ insert 0 Os := by rw [← hd]; exact hOsm y (hYPC hy)
    have hfdB : f d < B := by rw [← hd]; exact hfB y (hYPC hy)
    have hfqB : f (ω ^ 2 * q) + ω ^ 2 ≤ B :=
      lr_dvd_add_le (hf.dvd q) hWB
        ((show f (ω ^ 2 * q) ≤ f d by rw [hfd]; exact le_self_add).trans_lt hfdB)
    have hKμ : μ + f (ω ^ 2 * q) + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < l := by
      refine (lr_addL (a := μ + f (ω ^ 2 * q)) hKW).trans_le ?_
      rw [add_assoc]; exact (lr_addLe (a := μ) hfqB).trans hμBl
    have hCμ : upsilon (μ + f (ω ^ 2 * q) + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by
      rw [add_assoc (μ + f (ω ^ 2 * q))]; exact (hm hKμ).trans hν
    have eL : l + d = l + ω ^ 2 * q + r := by rw [← hdm, add_assoc]
    have eM : μ + f d = μ + f (ω ^ 2 * q) + r := by rw [hfd, add_assoc]
    rw [eL] at h2y h5y
    rw [eM] at h3y h5y
    have hlow : upsilon (botI (μ + f (ω ^ 2 * q)) j) < Ψ y := by
      rw [lr_botI (l + ω ^ 2 * q) j] at hj1
      rw [lr_botI (μ + f (ω ^ 2 * q)) j]
      exact lr_tr_lower h2y h3y h5y hj1
    have hrK : r ≤ ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 := by
      by_contra hlt
      have h4 : upsilon (l + ω ^ 2 * q + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) <
          upsilon (l + ω ^ 2 * q + r) := hm (lr_addL (a := l + ω ^ 2 * q) (not_le.1 hlt))
      have h5 : upsilon (l + ω ^ 2 * q + r) ≤ y := by rw [← hζ]; exact hζ1 y hyl
      rw [← add_assoc] at h4
      exact absurd (h4.trans_le h5) (not_lt.2 hj2)
    have hup : ∀ {w : Ordinal.{0}}, w ∈ Y →
        w ≤ upsilon (l + ω ^ 2 * q + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) →
        Ψ w ≤ upsilon (μ + f (ω ^ 2 * q) + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
      intro w hw hwK
      rw [add_assoc (l + ω ^ 2 * q)] at hwK
      rw [add_assoc (μ + f (ω ^ 2 * q))]
      obtain ⟨h1w, -, -, h4w, h5w⟩ := TR w (hYPC hw)
      obtain ⟨dw, hdw⟩ : ∃ dw, ζf w - l = dw := ⟨_, rfl⟩
      rw [hdw] at h1w h4w h5w
      by_cases hdq : ω ^ 2 * q ≤ dw
      · -- the same region: `dw = ω²·q + rw'`
        obtain ⟨rw', hrw'⟩ := exists_add_of_le hdq
        have hdwK : dw ≤ ω ^ 2 * q + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
          by_contra hlt
          have h4 := hm (lr_addL (a := l) (not_le.1 hlt))
          rw [← add_assoc] at h4
          exact absurd (h4.trans_le h1w) (not_lt.2 hwK)
        have hrwK : rw' ≤ ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 := by
          rw [hrw'] at hdwK; exact (add_le_add_iff_left _).1 hdwK
        have hfw : f dw = f (ω ^ 2 * q) + rw' := by
          rw [hrw']; exact hf.res q rw' (hrwK.trans_lt hKW)
        have e1 : l + dw = l + ω ^ 2 * q + rw' := by rw [hrw', ← add_assoc]
        have e2 : μ + f dw = μ + f (ω ^ 2 * q) + rw' := by rw [hfw, add_assoc]
        rw [e1] at h1w h5w
        rw [e2] at h4w h5w
        exact lr_tr_upper h1w h4w h5w hwK
      · -- an earlier region: `f(dw) < f(d) = f(ω²·q) + r ≤ f(ω²·q) + K`
        have hdwd : dw < d := (not_le.1 hdq).trans_le (by rw [← hdm]; exact le_self_add)
        have hdwO : dw ∈ insert 0 Os := by rw [← hdw]; exact hOsm w (hYPC hw)
        have hflt : f dw < f d := hf.mono (Finset.mem_coe.2 hdwO) (Finset.mem_coe.2 hdOs) hdwd
        have hle : succ (μ + f dw) ≤ μ + f (ω ^ 2 * q) + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
          rw [lr_succ_add, add_assoc]
          exact lr_addLe (a := μ) (Order.succ_le_of_lt
            ((hflt.trans_eq hfd).trans_le (add_le_add le_rfl hrK)))
        exact (h4w.trans_le (hm.monotone hle)).le
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
    have h1' : l < μ0 + ω * ((j + 1 : ℕ) : Ordinal.{0}) := hm.lt_iff_lt.1 hay
    have hlμ0 : l ≤ μ0 := by
      by_contra hlt
      have h3 := lr_dvd_add_le hμ0d hl.2 (not_le.1 hlt)
      exact absurd h1' (not_lt.2 ((lr_addL (a := μ0) (lr_omega_mul_lt (j + 1))).le.trans h3))
    obtain ⟨g, rfl⟩ := exists_add_of_le hlμ0
    have hg : ω ^ 2 ∣ g := (dvd_add_iff hl.2).1 hμ0d
    obtain ⟨qg, rfl⟩ := hg
    have hω1 : ω * ((j + 1 : ℕ) : Ordinal.{0}) < ω ^ 2 := lr_omega_mul_lt (j + 1)
    have hω2 : ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < ω ^ 2 := lr_omega_mul_add_one_lt (j + 1)
    obtain ⟨-, e1⟩ := hres (ω ^ 2 * qg + ω * ((j + 1 : ℕ) : Ordinal.{0})) (by rw [← add_assoc]; exact hy)
    obtain ⟨hO2, e2⟩ := hres (ω ^ 2 * qg + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)
      (by rw [← add_assoc, ← add_assoc]; exact hy')
    rw [← add_assoc] at e1
    rw [← add_assoc, ← add_assoc] at e2
    rw [e1, e2, hf.res qg _ hω1, add_assoc (ω ^ 2 * qg), hf.res qg _ hω2]
    have hμg : IsRestartIdx (μ + f (ω ^ 2 * qg)) :=
      ⟨fun h => hμri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hμri.2 (hf.dvd qg)⟩
    have hb2 := hf.bd _ hO2
    rw [add_assoc (ω ^ 2 * qg), hf.res qg _ hω2] at hb2
    have hKμ : μ + f (ω ^ 2 * qg) + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 < l := by
      have h3 : μ + (f (ω ^ 2 * qg) + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) < μ + B :=
        lr_addL (a := μ) hb2
      rw [← add_assoc, ← add_assoc] at h3
      exact h3.trans_le hμBl
    have e3 : μ + (f (ω ^ 2 * qg) + ω * ((j + 1 : ℕ) : Ordinal.{0})) =
        μ + f (ω ^ 2 * qg) + ω * ((j + 1 : ℕ) : Ordinal.{0}) := (add_assoc _ _ _).symm
    have e4 : μ + (f (ω ^ 2 * qg) + (ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) =
        μ + f (ω ^ 2 * qg) + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1 := by
      rw [← add_assoc, ← add_assoc]
    rw [e3, e4]
    exact Cx.cxStdPair_of_top hstd _ _ (hm (lt_add_one _)) ((hm hKμ).trans_le hlL)
      ⟨μ + f (ω ^ 2 * qg), j, Or.inr hμg, rfl, rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Ub
