import Googology.Trans.PoR.InaccPsi.R2.YcDirect
import Googology.Trans.PoR.InaccPsi.R2.YhLD

/-!
# YhRS: THE DIRECT READING OF THE LAYER `0` — EVERY CODE BELOW `Γ(1)` IS READ BY A READING SYSTEM `Xx.XxRS 0`

The reading `Xu.xuR` of every code `c < Γ(1)` (gate `Xu.xuG`) is a reading system over the base atom `Γ(0) = G`
(`Xx.XxRS 0`) below every `ε`-number bound `B ∈ [t₀, Γ(1))`: code system `yhK0 B` (hulls `Xu.xu_mem`, code gate
`Xu.xu_code_gate` after dropping the atoms `Γ(c') ≥ Γ(1)`, countability through the readings below `Γ_{x+2}`), the
limit data from `Yh.yh_ld` with Lemma IMG by `He.he_pkg_G1` (`yh_ldGs`).  So the route (c) of `Yc.YcDirect` holds
at `c = 0` for the WHOLE layer:

* `yhxR_succ`, `yhxG_le_succ` (the successor laws at every code, also above `Γ(1)`), `yhCl_restrict`;
* `yhK0 B`, `yhRS B` (**THE READING SYSTEM OF THE CODES BELOW `B`**);
* `yhDirect0` (**`YcDirect S 0 Γ(1)`, UNCONDITIONAL**; `Yc.ycDirect_A2` was `YcDirect S 0 φ(G, 1)`), `yhLay0`
  (**UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(φ(ℓ, G+1))·ω)` for every `ℓ < Γ(1)`**).

No new axiom.  New definitions: `yhK0`, `yhRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Wt Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu Googology.Trans.PoR.InaccPsi.R2.Gs
  Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Mx

theorem xuR_hi {c : Ordinal.{0}} (hc : gcG 1 ≤ c) (x : Ordinal.{0}) : xuR c x = wtD.R c x := by
  rw [xuR, dif_neg (fun h => absurd h.2 (not_lt.2 hc))]

theorem xuG_hi {c : Ordinal.{0}} (hc : gcG 1 ≤ c) : xuG c = wtD.g c := by
  rw [xuG, dif_neg (fun h => absurd h.2 (not_lt.2 hc))]

/-- **`(b+1)(x) = b(x) + 1` at every code** (above `Γ(1)` the default reading `Wt.wtD.R`). -/
theorem yhxR_succ (b x : Ordinal.{0}) : xuR (b + 1) x = xuR b x + 1 := by
  rcases lt_or_ge (b + 1) (gcG 1) with h | h
  · exact xuR_succ b h x
  · have hb : gcG 1 ≤ b := by
      by_contra hb; push Not at hb; exact absurd (xu_G1_lim.add_one_lt hb) (not_lt.2 h)
    rw [xuR_hi h, xuR_hi hb, wtD.R_succ]

theorem yhxG_le_succ (b : Ordinal.{0}) : xuG b ≤ xuG (b + 1) := by
  rcases lt_or_ge (b + 1) (gcG 1) with h | h
  · exact xuG_le_succ b h
  · have hb : gcG 1 ≤ b := by
      by_contra hb; push Not at hb; exact absurd (xu_G1_lim.add_one_lt hb) (not_lt.2 h)
    rw [xuG_hi h, xuG_hi hb]; exact wtD.g_le_succ b

/-- **A code below `Γ(1)` needs no atom `≥ Γ(1)`**: the closure with any atoms that are `G` or `≥ Γ(1)` gives, below
`Γ(1)`, the closure with the atom `G` alone. -/
theorem yhCl_restrict {Z : Ordinal.{0}} {A : Set Ordinal.{0}} (hA : ∀ s ∈ A, s = gcG 0 ∨ gcG 1 ≤ s) :
    ∀ c, GxCl Z A c → c < gcG 1 → GxCl Z {gcG 0} c := by
  intro c hc
  induction hc with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    rcases hA s hs with e | e
    · exact GxCl.atom e
    · exact absurd h (not_lt.2 e)
  | @add x y _ _ ihx ihy =>
    intro h
    exact GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    intro h
    exact GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h)) (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

section RS

theorem yh_count (B : Ordinal.{0}) (hB1 : B < gcG 1) {c y : Ordinal.{0}} (hc : c ≤ B) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // xuG b.1 < y} := by
  have hq1 : gq 1 y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (gm1_facts hy hy1).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // xuG b.1 < y} → Iio (gq 1 y) := fun b =>
    ⟨xuR b.1.1 y, xuR_lt1 hy hy1 ((lt_of_lt_of_le b.1.2 hc).trans hB1) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : xuR b.1.1 y = xuR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (xuR_mono hy hy1 ((lt_of_lt_of_le b'.1.2 hc).trans hB1) h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (xuR_mono hy hy1 ((lt_of_lt_of_le b.1.2 hc).trans hB1) h b.2 b'.2).ne'

/-- **The code system of the codes below `B`**: gate `xuG`, atoms `Γ(c)`. -/
noncomputable def yhK0 (B : Ordinal.{0}) (hBE : InE B) (hB1 : B < gcG 1) : GsCS where
  B := B
  gt := xuG
  B_V := hB1.trans_le (gcG_le (xu_one_lt_inE hBE).le)
  gt_zero := xuG_zero
  gt_lt := fun c hc => xuG_lt_Om1 c (hc.trans hB1)
  gt_succ := fun b Z hZ hb hg => xuG_succ hZ b (hb.trans hB1) hg
  mem := fun _ a _ c hc hca hg => (xu_mem (lt_of_le_of_lt zero_le hca) c (hc.trans hB1) hg).1
  κ := xuG B
  κ_lt := xuG_lt_Om1 B hB1
  B_mem := fun _ a _ ha hκ => (xu_mem (lt_of_le_of_lt zero_le ha) B hB1 hκ).1
  code_gate := fun Z hZ1 hZ0 _ hZp c hc hcB => by
    have hSC : SC Z := ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩
    have hZ1' : Z ≤ Om1 := hZ1
    refine xu_code_gate hSC hZ1' c (yhCl_restrict ?_ c hc (hcB.trans hB1)) (hcB.trans hB1)
    rintro s ⟨c', -, -, rfl⟩
    rcases eq_or_ne c' 0 with rfl | h0
    · exact Or.inl rfl
    · exact Or.inr (gcG_le (Order.one_le_iff_ne_zero.2 h0))
  count := fun _ _ hc hy hy1 => yh_count B hB1 hc hy hy1

theorem yhK0_B (B : Ordinal.{0}) (hBE : InE B) (hB1 : B < gcG 1) : (yhK0 B hBE hB1).B = B := rfl

theorem yhK0_gt (B : Ordinal.{0}) (hBE : InE B) (hB1 : B < gcG 1) : (yhK0 B hBE hB1).gt = xuG := rfl

theorem yh_gE : xuG gfE = 0 := by
  rw [xuG_low (gfE_lt_G0.trans xu_G_lt_t0)]; exact wtD.g_E

theorem yh_cofE {x c : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hc : c < gcG 1) (hEc : gfE < c)
    (hg : xuG c < x) {ν : Ordinal.{0}} (hν : ν < xuR c x) :
    ∃ b, gfE ≤ b ∧ b < c ∧ xuG b < x ∧ ν ≤ xuR b x := by
  obtain ⟨b, hbc, hgb, hνb⟩ := xuR_cof hx hx1 c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [yh_gE]; exact hx.pos, ?_⟩
    exact hνb.trans (xuR_mono hx hx1 (hEc.trans hc) hbE (by rw [yh_gE]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

/-- **The limit data with Lemma IMG** at every limit code `ε_{Ω₁+1} < c < B`. -/
theorem yh_ldGs (B : Ordinal.{0}) (hBE : InE B) (hB1 : B < gcG 1) : ∀ c, IsSuccLimit c → gfE < c → c < B → Nonempty (GsmLD (yhK0 B hBE hB1) xuR c) := by
  intro c hl hEc hc
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := yh_ld c hl (hc.trans hB1)
  have hlg : ∀ x, InE x → x < Om1 → xuG c < x → lg (xuR c x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEc
  · show xuG _ ≤ xuG c
    split_ifs with h
    · exact hgcp
    · rw [yh_gE]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    show xuR c x = _ ∧ _
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      exact e4.trans (xuR_mono hx hx1 (hEc.trans (hc.trans hB1)) h (by rw [yh_gE]; exact hx.pos)
        (hgcp.trans_lt hg)).le
  · intro ρ τ δ h hg
    show GhPkg (xuG c) ρ δ (fun y => lg (xuR c y))
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < gq 1 ρ := by
      have h1 : T ρ ≤ xuR c ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (xuR_lt1 hρE h.ρ1 (hc.trans hB1) hg)
    have hP := He.he_pkg_G1 h (C := ∅) hg (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM OF THE CODES BELOW `B`** over the base atom `Γ(0) = G`. -/
noncomputable def yhRS (B : Ordinal.{0}) (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) : XxRS 0 where
  K := yhK0 B hBE hB1
  R := xuR
  E_lt := (gfE_lt_G0.trans xu_G_lt_t0).trans_le hBt
  B_lim := ev_isSuccLimit_of_inE hBE
  gt_E := yh_gE
  gt_lowE := fun c hc => by
    show xuG c = gtc c
    rw [xuG_low ((hc.trans gfE_lt_G0).trans xu_G_lt_t0)]; exact wtD.g_lowE c hc
  R_E := fun x _ _ => by rw [xuR_low (gfE_lt_G0.trans xu_G_lt_t0)]; exact wtD.R_E x
  lt0 := fun c x hx hx1 hc hg => by rw [zero_add]; exact xuR_lt1 hx hx1 (hc.trans hB1) hg
  mono := fun b c x hx hx1 hc hbc hgb hgc => xuR_mono hx hx1 (hc.trans hB1) hbc hgc hgb
  succ := fun b x _ => yhxR_succ b x
  gt_le_succ := yhxG_le_succ
  cof := fun c x hx hx1 hc hEc hg ν hν => yh_cofE hx hx1 (hc.trans hB1) hEc hg hν
  ex := fun σ ρ c hB hc hg => xu_pi hB c (hc.trans hB1) hg
  ld := yh_ldGs B hBE hB1
  W_lt := by rw [zero_add]; exact one_lt_omega0.trans (omega0_lt_epsilon 0)

theorem yhRS_B (B : Ordinal.{0}) (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) : (yhRS B hBE hBt hB1).K.B = B := rfl

theorem yhRS_gt (B : Ordinal.{0}) (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) : (yhRS B hBE hBt hB1).K.gt = xuG := rfl

theorem yhRS_R (B : Ordinal.{0}) (hBE : InE B) (hBt : Wj.wjT 0 ≤ B) (hB1 : B < gcG 1) : (yhRS B hBE hBt hB1).R = xuR := rfl

end RS

/-- **ROUTE (c) AT `c = 0` FOR THE WHOLE LAYER: `YcDirect S 0 Γ(1)`, UNCONDITIONAL** (`Yc.ycDirect_A2` was the part
below `φ(G, 1)`): every `B < Γ(1)` lies below `t_n`, a code of `yhRS t_{n+1}` with gate at most `1`. -/
theorem yhDirect0 (S : InaccSeq.{0}) : Yc.YcDirect S 0 (gcG 1) := by
  intro B hB
  obtain ⟨n, hn⟩ := xu_A3_end.2.1 B hB
  have hE := (Wj.wjT_spec (n + 1)).2.2.1
  have ht := Wj.wjT_mono (Nat.zero_le (n + 1))
  have h1 := (Wj.wjT_spec (n + 1)).2.1
  refine ⟨yhRS (Wj.wjT (n + 1)) hE ht h1, Wj.wjT n, hn.le, xu_gfE_le (Wj.wjT_mono (Nat.zero_le n)),
    xu_t_lt n, ?_⟩
  show xuG (Wj.wjT n) < Td.tdK S
  have hg : xuG (Wj.wjT n) ≤ 1 := by rw [← xuGg_t n]; exact le_max_right _ _
  exact hg.trans_lt (Xc.xc_one_lt_SC Td.tdK_SC)

/-- **THE WHOLE LAYER `0` FROM THE DIRECT READING**: UPPER ∧ LOWER ∧ CapV at every range restart
`l < ι(Γ(φ(ℓ, G+1))·ω)`, `ℓ < Γ(1)`. -/
theorem yhLay0 (S : InaccSeq.{0}) : ∀ l, Cd.CdRange S l →
    (∃ ℓ, ℓ < gcG (0 + 1) ∧ l < Bt.iota S (gcG (veblen ℓ (gcG 0 + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l :=
  Yc.ycLay_of_direct (by rw [zero_add]; exact yhDirect0 S)

end Googology.Trans.PoR.InaccPsi.R2.Yh
