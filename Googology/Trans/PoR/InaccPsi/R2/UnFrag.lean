import Googology.Trans.PoR.InaccPsi.R2.TvInner
import Googology.Trans.PoR.InaccPsi.R2.UnTerm
import Googology.Trans.PoR.InaccPsi.R2.UkFrag

/-!
# Theorem FRAG with the hull isomorphism on terms with nested level terms in two modes

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`Uk.ukFrag` for the terms `Un.UnT` (level terms whose leaves are again terms, to any depth; the head mode of
`Uk.UkT` and the normal-form mode with a high leaf anywhere).  The proof is that of `Uk.ukFrag` with `Un.unDown`,
`Un.unTrA`, `Un.unTrB`, `Un.unUp_eq`, `Un.unMv`, `Un.unLe`; the syntactic mode conditions over `γ = Ψ'(β)` asked by
`Un.unTrB` come, as in `Uk`, from `Ψ'` increasing on `F'` with `Ψ'(β) = γ` (`UnT.HdA_map`), and the parameters over
`γ` lie in `T^γ` (asked by `Un.unTrB` for the decision `Γ^{*γ} ≥ γ` at `ϑ`-heads of leaves).
The clause carried through the induction (**the hull isomorphism**):
for every `k < m` and every such term `t` with the argument bounds over `b_k` whose leaves lie in `F ∩ T^{b_k}`
(they may lie in lower segments), if `t[b_k] ∈ F ∩ seg(b_k)` then `Ψ(t[b_k; p]) = t[c_k; Ψ p]`.

* `UnCl`, `UnFragConcl` (**`Tr.TrFragConcl` and the hull isomorphism**);
* `unFrag_one`, `unFrag_step`, `unFrag_aux`, `unFrag` (**FRAG with the hull isomorphism, under `Tr.TrInnerAll`**),
  `unFragV` (**the same with `Tv.tvInnerAll`, i.e. from `R2.tvSeg_pi`**).

New definitions: `UnCl`, `UnFragConcl` (statements).  No new axiom (uses `R2.ukVt_tr3`, `R2.uhVt_tr`, `R2.ueDp_pi`,
`R2.tvSeg_pi`).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Un

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tr Googology.Trans.PoR.InaccPsi.R2.Uh

/-- **The hull isomorphism on terms with uncountable arguments at code levels**: `Ψ(t[b_k; p]) = t[c_k; Ψ p]` for
every term with levels over `κ`, the argument bounds over `b_k`, leaves in `F ∩ T^{b_k}` and value in
`F ∩ seg(b_k)`. -/
def UnCl (κ : Ordinal.{0}) (b c : ℕ → Ordinal.{0}) (m : ℕ) (F : Finset Ordinal.{0})
    (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop :=
  ∀ k, k < m → ∀ t : UnC, UnT.Qs κ t → UnT.WF (b k) t → UnT.Lv (· ∈ F) t → UnT.Lv (· ∈ Tset (b k)) t →
    UnT.ev (b k) t ∈ F → InSeg (b k) (UnT.ev (b k) t) →
      Ψ (UnT.ev (b k) t) = UnT.ev (c k) (t.map Ψ) ∧ UnT.WF (c k) (t.map Ψ)

/-- The conclusion of `Tr.trFrag` and the hull isomorphism. -/
def UnFragConcl (κ : Ordinal.{0}) (b c : ℕ → Ordinal.{0}) (m : ℕ) (F : Finset Ordinal.{0})
    (Ψ : Ordinal.{0} → Ordinal.{0}) : Prop :=
  TrFragConcl κ b c m F Ψ ∧ UnCl κ b c m F Ψ

theorem unFrag_one {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b 1) (hc : Chain κ c 1)
    {F : Finset Ordinal.{0}} (hF : ↑F ⊆ DD κ b 1) (hbF : ∀ k, k < 1 → b k ∈ F) :
    ∃ Ψ, UnFragConcl κ b c 1 F Ψ := by
  obtain ⟨Ψ, h1, h2⟩ := trFrag_one hb hc hF hbF
  refine ⟨Ψ, ⟨h1, h2⟩, fun k hk t hq hw hl _ hxF _ => ?_⟩
  obtain rfl : k = 0 := by omega
  have hκE := upsPt_inE hb.kap
  have hb0 := hb.ups 0 (by omega)
  have hc0 := hc.ups 0 (by omega)
  have hκb := hb.bot 0 (by omega)
  have hκc := hc.bot 0 (by omega)
  have hBk : Bases κ (b 0) := ⟨hκE, upsPt_inE hb0.1, hκb, hb0.2⟩
  -- every point of `F` is in `T^{b_0}[κ]` and is moved by `mv b_0 c_0`
  have hFTB : ∀ x ∈ F, x ∈ TB (b 0) κ := by
    intro x hx
    rcases hF hx with hx | ⟨_, hT, hP⟩
    · exact (TB_inter_lt hBk (hx.trans hκb)).2 hx
    · exact ⟨hT, hP.trans (ClS.lt_of_E hκE le_rfl)⟩
  have hmv : ∀ x ∈ F, Ψ x = mv (b 0) (c 0) x := fun x hx => h1.2 le_rfl x hx (hF hx)
  obtain ⟨e1, e2⟩ := unMv (upsPt_inE hb0.1) hb0.2 (upsPt_inE hc0.1) hc0.2 hκb.le hκc.le t hq hw
    (UnT.Lv_mono (fun p hp => hFTB p hp) t hl)
  have hmap : t.map Ψ = t.map (mv (b 0) (c 0)) := UnT.map_congr t (UnT.Lv_mono (fun p hp => hmv p hp) t hl)
  rw [hmv _ hxF, hmap]
  exact ⟨e1, e2⟩

theorem unFrag_step {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {n : ℕ}
    (IH : ∀ F : Finset Ordinal.{0}, ↑F ⊆ DD κ b (n + 1) → (∀ k, k < n + 1 → b k ∈ F) →
      ∃ Ψ, UnFragConcl κ b c (n + 1) F Ψ) (hI : TrInnerAll κ b c (n + 2))
    (hb : Chain κ b (n + 2)) (hc : Chain κ c (n + 2))
    {F : Finset Ordinal.{0}} (hF : ↑F ⊆ DD κ b (n + 2)) (hbF : ∀ k, k < n + 2 → b k ∈ F) :
    ∃ Ψ, UnFragConcl κ b c (n + 2) F Ψ := by
  classical
  have hb1 : Chain κ b (n + 1) := hb.of_succ
  have hb0 : Chain κ b n := hb1.of_succ
  have htU := hb.ups (n + 1) (by omega)
  have hb'U := hb.ups n (by omega)
  have ht'U := hc.ups (n + 1) (by omega)
  have hb't : b n < b (n + 1) := hb.mono n (n + 1) (by omega) (by omega)
  have hc't' : c n < c (n + 1) := hc.mono n (n + 1) (by omega) (by omega)
  have hb'E := upsPt_inE hb'U.1
  have htE := upsPt_inE htU.1
  have hκ0 : (0 : Ordinal.{0}) < κ := hb.kap.1
  have h0Dn : (0 : Ordinal.{0}) ∈ DD κ b n := Iio_sub_DD n hκ0
  -- the top part and the low part of `F`
  have hlt_t : ∀ x ∈ DD κ b (n + 1), x < b (n + 1) := fun x hx =>
    DD_lt_ups hb1 hx (b (n + 1)) hb't htU.1
  have htop : ∀ x ∈ F, b (n + 1) ≤ x → InSeg (b (n + 1)) x ∧ x ∈ Tset (b (n + 1)) ∧
      ↑(Par (b (n + 1)) x) ⊆ ClS (DD κ b (n + 1)) := by
    intro x hx htx
    rcases hF hx with h | h
    · exact absurd (hlt_t x h) (not_lt.2 htx)
    · exact h
  have hlow : ∀ x ∈ F, x < b (n + 1) → x ∈ DD κ b (n + 1) := by
    intro x hx hxt
    rcases hF hx with h | h
    · exact h
    · exact absurd h.1.1 (not_le.2 hxt)
  -- top part of `D_{n+1}`: the points `≥ b_n`
  have hDtop : ∀ x ∈ DD κ b (n + 1), b n ≤ x → InSeg (b n) x ∧ x ∈ Tset (b n) ∧
      ↑(Par (b n) x) ⊆ ClS (DD κ b n) := by
    intro x hx hbx
    rcases hx with h | h
    · exact absurd (DD_lt_b hb1 h) (not_lt.2 hbx)
    · exact h
  set Ftop := F.filter (fun x => b (n + 1) ≤ x) with hFtop
  set Flow := F.filter (fun x => x < b (n + 1)) with hFlow
  set S := Ftop.biUnion (fun u => Par (b (n + 1)) u) ∪ Flow with hS
  have hSCl : ∀ s ∈ S, s ∈ ClS (DD κ b (n + 1)) := by
    intro s hs
    rcases Finset.mem_union.1 hs with hs | hs
    · obtain ⟨u, hu, hsu⟩ := Finset.mem_biUnion.1 hs
      obtain ⟨huF, htu⟩ := Finset.mem_filter.1 hu
      exact (htop u huF htu).2.2 hsu
    · obtain ⟨hsF, hst⟩ := Finset.mem_filter.1 hs
      exact ClS.sub _ (hlow s hsF hst)
  -- the height bound `M` and the base `β = ϑ^{b_n}(Δ_M)`
  let nS : Ordinal.{0} → ℕ := fun s => if h : ∃ k, s < Dl (b n) k then Nat.find h else 0
  have hnS : ∀ s ∈ S, b n ≤ s → s < Dl (b n) (nS s) := by
    intro s hs hbs
    obtain ⟨hs1, hs2⟩ := ClS_DD_bound hb1 (hSCl s hs)
    have hsT : s ∈ Tset (b n) :=
      ((inSeg_iff hb'U.1 hb'U.2).1 ⟨hbs, hs1, hs2⟩).2.2
    have hex := (ht_spec hb'E hb'U.2 hsT hs1).1
    simp only [nS, dif_pos hex]
    exact Nat.find_spec hex
  set M := 1 + S.sup nS + Ftop.sup (fun u => ht (b (n + 1)) u) with hM
  have hM1 : 1 ≤ M := by omega
  have hMS : ∀ s ∈ S, nS s ≤ M := fun s hs => by
    have := Finset.le_sup (f := nS) hs; omega
  have hMh : ∀ u ∈ Ftop, ht (b (n + 1)) u ≤ M := fun u hu => by
    have := Finset.le_sup (f := fun u => ht (b (n + 1)) u) hu
    simp only at this; omega
  set β := Dl (b n) M with hβdef
  obtain ⟨hb'β, hβE, hβP⟩ := Dl_E hb'E hb'U.2 hM1
  obtain ⟨hβT, hβ1, -⟩ := Dl_spec hb'E hb'U.2 M
  have hβseg : InSeg (b n) β := (inSeg_iff hb'U.1 hb'U.2).2 ⟨hb'β.le, hβ1, hβT⟩
  have hβt : β < b (n + 1) := hβseg.2.2 _ hb't htU.1
  have hBβ : Bases β (b (n + 1)) := ⟨hβE, htE, hβt, htU.2⟩
  have hSβ : ∀ s ∈ S, s < β := by
    intro s hs
    by_cases hbs : b n ≤ s
    · exact lt_of_lt_of_le (hnS s hs hbs) ((Dl_strictMono hb'E hb'U.2).monotone (hMS s hs))
    · exact (not_le.1 hbs).trans hb'β
  have hFlowS : ∀ x ∈ F, x < b (n + 1) → x ∈ S := fun x hx hxt =>
    Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hx, hxt⟩)
  have hFTB : ∀ x ∈ F, x ∈ TB (b (n + 1)) β := by
    intro x hx
    by_cases hxt : b (n + 1) ≤ x
    · refine ⟨(htop x hx hxt).2.1, fun p hp => hSβ p ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_biUnion.2
        ⟨x, Finset.mem_filter.2 ⟨hx, hxt⟩, Finset.mem_coe.1 hp⟩)
    · exact (TB_inter_lt hBβ (not_le.1 hxt)).2 (hSβ x (hFlowS x hx (not_le.1 hxt)))
  have hFTB' : (↑F : Set Ordinal.{0}) ⊆ TB (b (n + 1)) β := fun x hx => hFTB x hx
  have hCfix : ∀ x ∈ F, x < b (n + 1) → pi β (b (n + 1)) x = x := fun x hx hxt =>
    pi_lt hBβ (hSβ x (hFlowS x hx hxt))
  -- `β⁺ = ϑ^{b_n}(Δ_M + 1)` lies in `seg(b_n)`
  obtain ⟨hDpT, hDp1, hDpeq⟩ := Dp_spec hb'E hb'U.2 hM1
  have hβDp : β < Dp (b n) M := by
    rw [hDpeq]; exact (Dl_E hβE hβ1 hM1).1
  have hDpseg : InSeg (b n) (Dp (b n) M) :=
    (inSeg_iff hb'U.1 hb'U.2).2 ⟨(hb'β.trans hβDp).le, hDp1, hDpT⟩
  -- Lemma COMP (a), (b): the compressed points
  have hCtop : ∀ u ∈ F, b (n + 1) ≤ u → InSeg (b n) (pi β (b (n + 1)) u) ∧
      β ≤ pi β (b (n + 1)) u ∧ pi β (b (n + 1)) u ∈ Tset β ∧
      pi β (b (n + 1)) u < Dp (b n) M := by
    intro u hu htu
    have huT := hFTB u hu
    have hCuT : pi β (b (n + 1)) u ∈ Tset β := (pi_bijOn hBβ).1.mapsTo huT
    have hβCu : β ≤ pi β (b (n + 1)) u := down_ge hBβ huT htu
    have hCu1 : pi β (b (n + 1)) u < Om1 := down_lt_Om1 hBβ huT (htop u hu htu).1.2.1
    have hht : ht β (pi β (b (n + 1)) u) ≤ M := by
      rw [(pi_ht_Par hBβ huT).1]; exact hMh u (Finset.mem_filter.2 ⟨hu, htu⟩)
    have hCuDp : pi β (b (n + 1)) u < Dp (b n) M := by
      rw [hDpeq]; exact lt_Dl_of_ht hβE hβ1 hCuT hCu1 hht
    exact ⟨⟨hb'β.le.trans hβCu, hCu1, fun v hv hv' => hCuDp.trans (hDpseg.2.2 v hv hv')⟩,
      hβCu, hCuT, hCuDp⟩
  -- the parameter set `X` of Lemma COMP (c)
  let gen1 : Ordinal.{0} → Finset Ordinal.{0} := fun p =>
    if h : p ∈ ClS (DD κ b (n + 1)) then Classical.choose (ClS.gen h) else ∅
  have gen1_spec : ∀ p, p ∈ ClS (DD κ b (n + 1)) → ↑(gen1 p) ⊆ DD κ b (n + 1) ∧
      (∀ g ∈ gen1 p, g ≤ p) ∧ p ∈ ClS ↑(gen1 p) := by
    intro p hp
    simp only [gen1, dif_pos hp]
    exact Classical.choose_spec (ClS.gen hp)
  let gen2 : Ordinal.{0} → Finset Ordinal.{0} := fun p =>
    if h : p ∈ ClS (DD κ b n) then Classical.choose (ClS.gen h) else ∅
  have gen2_spec : ∀ p, p ∈ ClS (DD κ b n) → ↑(gen2 p) ⊆ DD κ b n ∧
      (∀ g ∈ gen2 p, g ≤ p) ∧ p ∈ ClS ↑(gen2 p) := by
    intro p hp
    simp only [gen2, dif_pos hp]
    exact Classical.choose_spec (ClS.gen hp)
  have gen2_sub : ∀ p g, g ∈ gen2 p → g ∈ DD κ b n := by
    intro p g hg
    by_cases hp : p ∈ ClS (DD κ b n)
    · exact (gen2_spec p hp).1 hg
    · simp [gen2, dif_neg hp] at hg
  set G0 := Ftop.biUnion (fun u => (Par (b (n + 1)) u).biUnion gen1) with hG0
  set XaF := G0 ∪ G0.biUnion (fun g => (comps g).toFinset) with hXaF
  set G1 := (XaF.filter (fun ξ => b n ≤ ξ)).biUnion
    (fun ξ => (Par (b n) ξ).biUnion gen2) with hG1
  set XF := insert (0 : Ordinal.{0}) (XaF ∪ G1 ∪ G1.biUnion (fun g => (comps g).toFinset))
    with hXF
  -- (k1) generators of the top parameters
  have k1 : ∀ g ∈ G0, g ∈ DD κ b (n + 1) ∧ g < β := by
    intro g hg
    obtain ⟨u, hu, hg⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨p, hp, hg⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨huF, htu⟩ := Finset.mem_filter.1 hu
    have hpCl := (htop u huF htu).2.2 (Finset.mem_coe.2 hp)
    have hs := gen1_spec p hpCl
    have hpS : p ∈ S := Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨u, hu, hp⟩)
    exact ⟨hs.1 hg, lt_of_le_of_lt (hs.2.1 g hg) (hSβ p hpS)⟩
  have mem_XaF : ∀ ξ ∈ XaF, ξ ∈ G0 ∨ ∃ g ∈ G0, ξ ∈ comps g := by
    intro ξ hξ
    rcases Finset.mem_union.1 hξ with h | h
    · exact Or.inl h
    · obtain ⟨g, hg, hξg⟩ := Finset.mem_biUnion.1 h
      exact Or.inr ⟨g, hg, List.mem_toFinset.1 hξg⟩
  -- (k2) the points of `XaF` in `seg(b_n)`
  have k2 : ∀ ξ ∈ XaF, b n ≤ ξ → InSeg (b n) ξ ∧ ξ ∈ Tset (b n) ∧
      ↑(Par (b n) ξ) ⊆ ClS (DD κ b n) := by
    intro ξ hξ hbξ
    rcases mem_XaF ξ hξ with hg | ⟨g, hg, hξg⟩
    · exact hDtop ξ (k1 ξ hg).1 hbξ
    · have hξle := le_of_mem_comps hξg
      obtain ⟨hgs, hgT, hgP⟩ := hDtop g (k1 g hg).1 (hbξ.trans hξle)
      have hc := (Par_comps hb'E hb'U.2 hgT hgs.1 hgs.2.1 hξg).2 hbξ
      exact ⟨⟨hbξ, lt_of_le_of_lt hξle hgs.2.1, fun v hv hv' => lt_of_le_of_lt hξle
        (hgs.2.2 v hv hv')⟩, hc.1, (Finset.coe_subset.2 hc.2).trans hgP⟩
  -- (k3) `XaF < β`
  have k3 : ∀ ξ ∈ XaF, ξ < β := by
    intro ξ hξ
    rcases mem_XaF ξ hξ with hg | ⟨g, hg, hξg⟩
    · exact (k1 ξ hg).2
    · exact lt_of_le_of_lt (le_of_mem_comps hξg) (k1 g hg).2
  -- (k4) the points of `XaF` below `b_n` are in `Cl(D_n)`
  have k4 : ∀ ξ ∈ XaF, ξ < b n → ξ ∈ ClS (DD κ b n) := by
    intro ξ hξ hξb
    rcases mem_XaF ξ hξ with hg | ⟨g, hg, hξg⟩
    · rcases (k1 ξ hg).1 with h | h
      · exact ClS.sub _ h
      · exact absurd h.1.1 (not_le.2 hξb)
    · rcases (k1 g hg).1 with h | h
      · exact comps_DD hb0 h hξg
      · exact h.2.2 ((Par_comps hb'E hb'U.2 h.2.1 h.1.1 h.1.2.1 hξg).1 hξb)
  have mem_XF : ∀ ξ ∈ XF, ξ = 0 ∨ ξ ∈ XaF ∨ ξ ∈ G1 ∨ ∃ g ∈ G1, ξ ∈ comps g := by
    intro ξ hξ
    rcases Finset.mem_insert.1 hξ with h | h
    · exact Or.inl h
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨g, hg, hξg⟩ := Finset.mem_biUnion.1 h
      exact Or.inr (Or.inr (Or.inr ⟨g, hg, List.mem_toFinset.1 hξg⟩))
  have k5 : ∀ g ∈ G1, g ∈ DD κ b n := by
    intro g hg
    obtain ⟨ξ, -, hg⟩ := Finset.mem_biUnion.1 hg
    obtain ⟨p, -, hg⟩ := Finset.mem_biUnion.1 hg
    exact gen2_sub p g hg
  -- (k6) `X ∩ b_n ⊆ Cl(D_n)`
  have k6 : ∀ ξ ∈ XF, ξ < b n → ξ ∈ ClS (DD κ b n) := by
    intro ξ hξ hξb
    rcases mem_XF ξ hξ with h | h | h | ⟨g, hg, hξg⟩
    · subst h; exact ClS.sub _ h0Dn
    · exact k4 ξ h hξb
    · exact ClS.sub _ (k5 ξ h)
    · exact comps_DD hb0 (k5 g hg) hξg
  -- (k7) `X ⊆ β`
  have k7 : ∀ ξ ∈ XF, ξ < β := by
    intro ξ hξ
    rcases mem_XF ξ hξ with h | h | h | ⟨g, hg, hξg⟩
    · subst h; exact lt_of_le_of_lt (by simp) hb'β
    · exact k3 ξ h
    · exact (DD_lt_b hb1 (k5 ξ h)).trans hb'β
    · exact lt_of_le_of_lt (le_of_mem_comps hξg) ((DD_lt_b hb1 (k5 g hg)).trans hb'β)
  -- (k8) `X` is closed under additive decomposition
  have k8 : DC ↑XF := by
    intro ξ hξ p hp
    rcases mem_XF ξ hξ with h | h | h | ⟨g, hg, hξg⟩
    · subst h; simp [comps] at hp
    · rcases mem_XaF ξ h with hg | ⟨g, hg, hξg⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨ξ, hg, List.mem_toFinset.2 hp⟩))))
      · rw [comps_of_mem_comps hξg, List.mem_singleton] at hp
        subst hp; exact hξ
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨ξ, h, List.mem_toFinset.2 hp⟩))
    · rw [comps_of_mem_comps hξg, List.mem_singleton] at hp
      subst hp; exact hξ
  have hXlow : (↑XF ∩ Set.Iio (b n) : Set Ordinal.{0}) ⊆ ClS (DD κ b n) :=
    fun ξ hξ => k6 ξ hξ.1 hξ.2
  -- (k9) the parameters of `X` at the base `b_n`
  have k9 : ∀ ξ ∈ (↑XF : Set Ordinal.{0}), ↑(Par (b n) ξ) ⊆ ClS (↑XF ∩ Set.Iio (b n)) := by
    intro ξ hξ
    by_cases hξb : ξ < b n
    · rw [Par_lt hb'E hb'U.2 hξb, Finset.coe_singleton, Set.singleton_subset_iff]
      exact ClS.sub _ ⟨hξ, hξb⟩
    · have hξXa : ξ ∈ XaF := by
        rcases mem_XF ξ hξ with h | h | h | ⟨g, hg, hξg⟩
        · subst h; exact absurd hb'U.1.1 hξb
        · exact h
        · exact absurd (DD_lt_b hb1 (k5 ξ h)) hξb
        · exact absurd (lt_of_le_of_lt (le_of_mem_comps hξg) (DD_lt_b hb1 (k5 g hg))) hξb
      intro p hp
      have hpCl : p ∈ ClS (DD κ b n) := (k2 ξ hξXa (not_lt.1 hξb)).2.2 hp
      have hs := gen2_spec p hpCl
      refine ClS.mono ?_ hs.2.2
      intro g hg
      refine ⟨?_, DD_lt_b hb1 (hs.1 hg)⟩
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨ξ, Finset.mem_filter.2 ⟨hξXa, not_lt.1 hξb⟩,
          Finset.mem_biUnion.2 ⟨p, Finset.mem_coe.1 hp, hg⟩⟩)))
  have h0X : (0 : Ordinal.{0}) ∈ (↑XF : Set Ordinal.{0}) := Finset.mem_insert_self _ _
  have k10 : ↑(Par (b n) β) ⊆ ClS (↑XF ∩ Set.Iio (b n)) := by
    refine hβP.trans ?_
    rw [Set.singleton_subset_iff]
    exact ClS.sub _ ⟨h0X, hb'U.1.1⟩
  -- Lemma COMP (c): the parameters of a compressed point
  have hCpar : ∀ u ∈ F, b (n + 1) ≤ u →
      ↑(Par (b n) (pi β (b (n + 1)) u)) ⊆ ClS (DD κ b n) := by
    intro u hu htu
    obtain ⟨-, hβCu, hCuT, hCuDp⟩ := hCtop u hu htu
    have hPx : ↑(Par β (pi β (b (n + 1)) u)) ⊆ ClS ↑XF := by
      rw [(pi_ht_Par hBβ (hFTB u hu)).2]
      intro p hp
      have hpCl := (htop u hu htu).2.2 hp
      have hs := gen1_spec p hpCl
      refine ClS.mono ?_ hs.2.2
      intro g hg
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨u, Finset.mem_filter.2 ⟨hu, htu⟩,
          Finset.mem_biUnion.2 ⟨p, Finset.mem_coe.1 hp, hg⟩⟩))))
    have := par_track hb'E hb'U.2 hM1 hCuT hβCu hCuDp (fun ξ hξ => k7 ξ hξ) h0X k8 k9 k10 hPx
    exact this.trans (ClS.sub_of hXlow)
  have hCD : ∀ u ∈ F, b (n + 1) ≤ u → pi β (b (n + 1)) u ∈ DD κ b (n + 1) := by
    intro u hu htu
    have hs := (hCtop u hu htu).1
    exact Or.inr ⟨hs, ((inSeg_iff hb'U.1 hb'U.2).1 hs).2.2, hCpar u hu htu⟩
  have hβD : β ∈ DD κ b (n + 1) := by
    refine Or.inr ⟨hβseg, hβT, hβP.trans ?_⟩
    rw [Set.singleton_subset_iff]; exact ClS.sub _ h0Dn
  -- `β⁺ = Dp b_n M` is a low-parameter point of `seg(b_n)` (`R2.ueDp_pi`)
  have hκE' : InE κ := upsPt_inE hb.kap
  have hκbn : κ < b n := hb.bot n (by omega)
  have hBκb : Bases κ (b n) := ⟨hκE', hb'E, hκbn, hb'U.2⟩
  have hDpTB : Dp (b n) M ∈ TB (b n) κ := (ueDp_pi hBκb hM1).1
  have hDpD : Dp (b n) M ∈ DD κ b (n + 1) :=
    Or.inr ⟨hDpseg, hDpTB.1, fun p hp => ClS.sub _ (Iio_sub_DD n (hDpTB.2 hp))⟩
  -- the compressed set (with `β`, `β⁺`) and the induction hypothesis
  set F' := insert (Dp (b n) M) (insert β (Flow ∪ Ftop.image (pi β (b (n + 1))))) with hF'def
  have hCF' : ∀ x ∈ F, pi β (b (n + 1)) x ∈ F' := by
    intro x hx
    by_cases hxt : b (n + 1) ≤ x
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx, hxt⟩))))
    · rw [hCfix x hx (not_le.1 hxt)]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_filter.2 ⟨hx, not_le.1 hxt⟩)))
  have hF'D : ↑F' ⊆ DD κ b (n + 1) := by
    intro x hx
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hx) with h | h
    · subst h; exact hDpD
    rcases Finset.mem_insert.1 h with h | h
    · subst h; exact hβD
    rcases Finset.mem_union.1 h with h | h
    · obtain ⟨hxF, hxt⟩ := Finset.mem_filter.1 h
      exact hlow x hxF hxt
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨huF, htu⟩ := Finset.mem_filter.1 hu
      exact hCD u huF htu
  have hbk_t : ∀ k, k < n + 1 → b k < b (n + 1) := fun k hk => hb.mono k (n + 1) hk (by omega)
  have hbF' : ∀ k, k < n + 1 → b k ∈ F' := by
    intro k hk
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hbF k (by omega), hbk_t k hk⟩)))
  have hβF' : β ∈ F' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hDpF' : Dp (b n) M ∈ F' := Finset.mem_insert_self _ _
  have hb'F' : b n ∈ F' := hbF' n (by omega)
  obtain ⟨Ψ', ⟨⟨⟨⟨P1, P2, P3, P4, P5, P6, P7⟩, P8⟩, P9⟩, P10⟩, P11⟩ := IH F' hF'D hbF'
  -- `γ = Ψ'(β) = ϑ^{c_n}(Δ_M)` and `Ψ'(β⁺) = γ⁺` (`P10`: `Ψ' = mv b_n c_n` on low-parameter points)
  have hβlow' : β ∈ TB (b n) κ := ⟨hβT, fun p hp => by
    have := hβP hp
    rw [Set.mem_singleton_iff] at this
    rw [this]; exact InE.pos hκE'⟩
  have hγeq : Ψ' β = Dl (c n) M := by
    rw [P10 n (by omega) β hβF' hβseg hβlow']
    exact trMv_Dl hb'U.1 hb'U.2 (hc.ups n (by omega)).1 (hc.ups n (by omega)).2 hM1
  have hDpΨ : Ψ' (Dp (b n) M) = Dp (c n) M := by
    rw [P10 n (by omega) _ hDpF' hDpseg hDpTB]
    exact Ue.ueMv_Dp hb'U.1 hb'U.2 (hc.ups n (by omega)).1 (hc.ups n (by omega)).2 hM1
  -- every point of `F'` lies in `T^{b_n}`
  have hF'T : ∀ x ∈ F', x ∈ Tset (b n) := by
    intro x hx
    rcases mem_DD (hF'D hx) with h | ⟨k, hk, hs, hT, -⟩
    · exact uh_T_le hb'E hb'U.2 (h.trans hκbn).le
    · rcases Nat.lt_or_ge k n with hkn | hkn
      · exact uh_T_le hb'E hb'U.2 (hs.2.2 (b n) (hb.mono k n hkn (by omega)) hb'U.1).le
      · have hkn' : k = n := by omega
        exact hkn' ▸ hT
  -- the expansion `π_{γ, c_{n+1}}⁻¹`, `γ = Ψ'(β)`
  have hγseg : InSeg (c n) (Ψ' β) := P2 n (by omega) β hβF' hβseg
  have hγE : InE (Ψ' β) := P7 β hβF' hβE
  have hc'γ : c n < Ψ' β := by
    rw [← P3 n (by omega) hb'F']; exact P4.2.1 hb'F' hβF' hb'β
  have hγt' : Ψ' β < c (n + 1) := hγseg.2.2 _ hc't' ht'U.1
  have hBγ : Bases (Ψ' β) (c (n + 1)) := ⟨hγE, upsPt_inE ht'U.1, hγt', ht'U.2⟩
  have hΨ'b : ∀ x ∈ F', Ψ' x < Om1 ∧ ∀ v, c n < v → UpsPt v → Ψ' x < v := by
    intro x hx
    rcases mem_DD (hF'D hx) with h | ⟨k, hk, hs, -, -⟩
    · rw [P1 x hx h]
      have hκc : κ < c n := hc.bot n (by omega)
      exact ⟨h.trans hb.kap1, fun v hv _ => (h.trans hκc).trans hv⟩
    · have hs' := P2 k hk x hx hs
      refine ⟨hs'.2.1, fun v hv hv' => ?_⟩
      rcases Nat.lt_or_ge k n with hkn | hkn
      · exact (hs'.2.2 (c n) (hc.mono k n hkn (by omega)) (hc.ups n (by omega)).1).trans hv
      · have : k = n := by omega
        subst this; exact hs'.2.2 v hv hv'
  have hΨ'T : ∀ x ∈ F', Ψ' x ∈ Tset (Ψ' β) := fun x hx =>
    T_of_inSeg_E hγE hγseg (hΨ'b x hx).1 (hΨ'b x hx).2
  -- the low points stay below `γ`
  have hlowγ : ∀ x ∈ F, x < b (n + 1) → Ψ' x < Ψ' β := by
    intro x hx hxt
    have hxF' : x ∈ F' := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hx, hxt⟩)))
    exact P4.2.1 hxF' hβF' (hSβ x (hFlowS x hx hxt))
  have hlowF' : ∀ x ∈ F, x < b (n + 1) → x ∈ F' := fun x hx hxt =>
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hx, hxt⟩)))
  have hEfix : ∀ x ∈ F, x < b (n + 1) →
      up (Ψ' β) (c (n + 1)) (Ψ' (pi β (b (n + 1)) x)) = Ψ' x := by
    intro x hx hxt
    rw [hCfix x hx hxt]; exact up_lt hBγ (hlowγ x hx hxt)
  have hseg_low : ∀ k, k < n + 1 → ∀ x, InSeg (b k) x → x < b (n + 1) := fun k hk x hs =>
    hs.2.2 _ (hbk_t k hk) htU.1
  refine ⟨fun x => up (Ψ' β) (c (n + 1)) (Ψ' (pi β (b (n + 1)) x)),
    ⟨⟨⟨concl_of hb hc hF hbF ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- (F-a)
    intro x hx hxk
    have hxt : x < b (n + 1) := hxk.trans (hb.bot (n + 1) (by omega))
    show up _ _ (Ψ' (pi β (b (n + 1)) x)) = x
    rw [hEfix x hx hxt, P1 x (hlowF' x hx hxt) hxk]
  · -- (F-b), segments
    intro k hk x hx hs
    show InSeg (c k) (up _ _ (Ψ' (pi β (b (n + 1)) x)))
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hxt := hseg_low k hk' x hs
      rw [hEfix x hx hxt]
      exact P2 k hk' x (hlowF' x hx hxt) hs
    · have : k = n + 1 := by omega
      subst this
      have hxF' := hCF' x hx
      have hγle : Ψ' β ≤ Ψ' (pi β (b (n + 1)) x) := by
        rcases eq_or_lt_of_le (hCtop x hx hs.1).2.1 with h | h
        · exact le_of_eq (congrArg Ψ' h)
        · exact (P4.2.1 hβF' hxF' h).le
      have hT := hΨ'T _ hxF'
      exact (inSeg_iff ht'U.1 ht'U.2).2 ⟨up_ge hBγ hT hγle, up_lt_Om1 hBγ hT (hΨ'b _ hxF').1,
        (up_spec hBγ hT).1.1⟩
  · -- (F-b), bases
    intro k hk
    show up _ _ (Ψ' (pi β (b (n + 1)) (b k))) = c k
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · rw [hEfix (b k) (hbF k hk) (hbk_t k hk'), P3 k hk' (hbF' k hk')]
    · have : k = n + 1 := by omega
      subst this
      rw [(pi_base hBβ).2, up_base hBγ]
  · -- order
    intro x hx y hy hxy
    have h1 := down_mono hBβ hFTB' hx hy hxy
    have h2 := P4.2.1 (hCF' x hx) (hCF' y hy) h1
    exact up_mono hBγ (S := Tset (Ψ' β)) le_rfl (hΨ'T _ (hCF' x hx)) (hΨ'T _ (hCF' y hy)) h2
  · -- `+`
    intro x hx y hy z hz
    rw [down_add hBβ hFTB' x hx y hy z hz,
      P4.2.2 _ (hCF' x hx) _ (hCF' y hy) _ (hCF' z hz),
      up_add hBγ (S := Tset (Ψ' β)) le_rfl _ (hΨ'T _ (hCF' x hx)) _ (hΨ'T _ (hCF' y hy)) _
        (hΨ'T _ (hCF' z hz))]
  · -- `≤₁` inside a segment
    intro k hk x hx y hy hsx hsy hbx
    show le1R x y ↔ le1R (up _ _ (Ψ' (pi β (b (n + 1)) x))) (up _ _ (Ψ' (pi β (b (n + 1)) y)))
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hxt := hseg_low k hk' x hsx
      have hyt := hseg_low k hk' y hsy
      rw [hEfix x hx hxt, hEfix y hy hyt]
      exact P5 x (hlowF' x hx hxt) y (hlowF' y hy hyt)
    · have : k = n + 1 := by omega
      subst this
      have hxF' := hCF' x hx
      have hyF' := hCF' y hy
      have hβCx : β < pi β (b (n + 1)) x := down_gt hBβ (hFTB x hx) hbx
      rw [st_le1 hBβ (hFTB x hx) hbx hsx.2.1 (hFTB y hy), P5 _ hxF' _ hyF']
      exact up_le1 hBγ (hΨ'T _ hxF') (P4.2.1 hβF' hxF' hβCx) (hΨ'b _ hxF').1 (hΨ'T _ hyF')
  · -- `ε`-numbers
    intro k hk x hx hs hbx hE
    show InE (up _ _ (Ψ' (pi β (b (n + 1)) x)))
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hxt := hseg_low k hk' x hs
      rw [hEfix x hx hxt]
      exact P7 x (hlowF' x hx hxt) hE
    · have : k = n + 1 := by omega
      subst this
      have hxF' := hCF' x hx
      have hβCx : β < pi β (b (n + 1)) x := down_gt hBβ (hFTB x hx) hbx
      have hE1 := (down_E hBβ (hFTB x hx) hbx hs.2.1).1 hE
      have hE2 := P7 _ hxF' hE1
      exact (up_E hBγ (hΨ'T _ hxF') (P4.2.1 hβF' hxF' hβCx) (hΨ'b _ hxF').1).1 hE2
  · -- indecomposability: `π`, the induction hypothesis, `π⁻¹`
    intro x hx hI
    show Indec (up _ _ (Ψ' (pi β (b (n + 1)) x)))
    have hxF' := hCF' x hx
    have h1 := down_indec hBβ (hFTB x hx) (DD_lt_Om1 hb (hF hx)) hI
    exact up_indec hBγ (hΨ'T _ hxF') (hΨ'b _ hxF').1 (P8 _ hxF' h1)
  · -- the clause on `D_1`: `Ψ = Ψ'` there, and `Ψ' = mv` by induction
    intro _ x hx hxD
    have hxt : x < b (n + 1) := hlt_t x (DD_mono (show 1 ≤ n + 1 by omega) hxD)
    show up _ _ (Ψ' (pi β (b (n + 1)) x)) = mv (b 0) (c 0) x
    rw [hEfix x hx hxt]
    exact P9 (by omega) x (hlowF' x hx hxt) hxD
  · -- the clause on every segment: below `b_{n+1}` from the induction hypothesis, on `seg(b_{n+1})` by
    -- `TrInner` at `(b_n, c_n, M)` (`Tr.trCarry_of_inner`)
    intro k hk x hx hs hT
    show up _ _ (Ψ' (pi β (b (n + 1)) x)) = mv (b k) (c k) x
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hxt := hseg_low k hk' x hs
      rw [hEfix x hx hxt]
      exact P10 k hk' x (hlowF' x hx hxt) hs hT
    · have : k = n + 1 := by omega
      subst this
      have hκE : InE κ := upsPt_inE hb.kap
      have hκb' : κ < b n := hb.bot n (by omega)
      have hκc' : κ < c n := hc.bot n (by omega)
      have hβlow : β ∈ TB (b n) κ := ⟨hβT, fun p hp => by
        have := hβP hp
        rw [Set.mem_singleton_iff] at this
        rw [this]; exact InE.pos hκE⟩
      have hγeq : Ψ' β = Dl (c n) M := by
        rw [P10 n (by omega) β hβF' hβseg hβlow]
        exact trMv_Dl hb'U.1 hb'U.2 (hc.ups n (by omega)).1 (hc.ups n (by omega)).2 hM1
      have hxTop : x ∈ TrTop (b (n + 1)) κ M :=
        ⟨hT, hs.1, hs.2.1, hMh x (Finset.mem_filter.2 ⟨hx, hs.1⟩)⟩
      have hyTop : pi β (b (n + 1)) x ∈ TrTop β κ M :=
        (trPi_image_ht hBβ (hκb'.trans hb'β).le M) ▸ ⟨x, hxTop, rfl⟩
      have hyD := trParDown hκE hb'U.1 hb'U.2 hκb' hM1 hyTop
      rw [P10 n (by omega) _ (hCF' x hx) hyD.2 hyD.1.1, hγeq]
      exact (trCarry_of_inner hκE htU.1 htU.2 ht'U.1 ht'U.2 hb'U.1 (hc.ups n (by omega)).1 hb't hc't'
        hκb' hκc' hM1 (hI n (by omega) M hM1) hxTop).1
  · -- the term clause: below `b_{n+1}` from the induction hypothesis; on `seg(b_{n+1})` by the compression
    -- `π_{β,b_{n+1}}` (`unDown`), the translation `t^β_{b_n}` (`unTrA`), the induction hypothesis at `b_n`, the
    -- translation `t^{c_n}_γ` back (`unTrB`, with every `thc`-value below `γ⁺ = Ψ'(β⁺)`) and `π_{γ,c_{n+1}}⁻¹`
    -- (`unUp_eq`)
    intro k hk t hq hw hl hlT hxF hs
    rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
    · have hxt := hseg_low k hk' _ hs
      have hbkU := hb.ups k (by omega)
      have hBk : Bases κ (b k) := ⟨hκE', upsPt_inE hbkU.1, hb.bot k (by omega), hbkU.2⟩
      have hle := (unLe hBk t hlT hw hq).1
      have hpt : ∀ p, p ∈ F ∧ p ≤ UnT.ev (b k) t → p < b (n + 1) := fun p hp => lt_of_le_of_lt hp.2 hxt
      have hlF' : UnT.Lv (· ∈ F') t := UnT.Lv_mono (fun p hp => hlowF' p hp.1 (hpt p hp)) t
        (UnT.Lv_and t hl hle)
      obtain ⟨e1, e2⟩ := P11 k hk' t hq hw hlF' hlT (hlowF' _ hxF hxt) hs
      have hmap : t.map (fun x => up (Ψ' β) (c (n + 1)) (Ψ' (pi β (b (n + 1)) x))) = t.map Ψ' :=
        UnT.map_congr t (UnT.Lv_mono (fun p hp => hEfix p hp.1 (hpt p hp)) t (UnT.Lv_and t hl hle))
      show up (Ψ' β) (c (n + 1)) (Ψ' (pi β (b (n + 1)) (UnT.ev (b k) t))) = _ ∧ _
      rw [hEfix _ hxF hxt, hmap]
      exact ⟨e1, e2⟩
    · have : k = n + 1 := by omega
      subst this
      have hxt : b (n + 1) ≤ UnT.ev (b (n + 1)) t := hs.1
      have hlTB : UnT.Lv (· ∈ TB (b (n + 1)) β) t := UnT.Lv_mono (fun p hp => hFTB p hp) t hl
      have hκβ : κ ≤ β := (hκbn.trans hb'β).le
      obtain ⟨-, d2, d3⟩ := unDown hBβ hκβ t hw hlTB hq
      set T' := t.map (pi β (b (n + 1))) with hT'
      have hqT' : UnT.Qs κ T' := UnT.Qs_map _ t hq
      have hBκβ : Bases κ β := ⟨hκE', hβE, hκbn.trans hb'β, hβ1⟩
      have hlT'β : UnT.Lv (· ∈ Tset β) T' :=
        UnT.Lv_map t (UnT.Lv_mono (fun p hp => (pi_bijOn hBβ).1.mapsTo (hFTB p hp)) t hl)
      have hev' : UnT.ev β T' = pi β (b (n + 1)) (UnT.ev (b (n + 1)) t) := d2.symm
      have hyDp : UnT.ev β T' < Dp (b n) M := by rw [hev']; exact (hCtop _ hxF hxt).2.2.2
      have hNdβ : UnT.Nd β (· < Dp (b n) M) T' :=
        UnT.Nd_mono (fun p hp => lt_of_le_of_lt hp hyDp) T' (unLe hBκβ T' hlT'β d3 hqT').2
      obtain ⟨tr1, tr2⟩ := unTrA hBκb hM1 T' hqT' hlT'β d3 hNdβ
      have tr1' : UnT.WF (b n) (UnT.tr β T') := tr1
      have tr2' : UnT.ev (b n) (UnT.tr β T') = UnT.ev β T' := tr2
      have hl' : UnT.Lv (· ∈ F') (UnT.tr β T') :=
        UnT.Lv_tr hβF' _ (UnT.Lv_map t (UnT.Lv_mono (fun p hp => hCF' p hp) t hl))
      have hlT' : UnT.Lv (· ∈ Tset (b n)) (UnT.tr β T') := UnT.Lv_mono (fun p hp => hF'T p hp) _ hl'
      have hval : UnT.ev (b n) (UnT.tr β T') = pi β (b (n + 1)) (UnT.ev (b (n + 1)) t) := by
        rw [tr2', hev']
      obtain ⟨e1, e2⟩ := P11 n (by omega) _ (UnT.Qs_tr _ _ hqT') tr1' hl' hlT'
        (by rw [hval]; exact hCF' _ hxF) (by rw [hval]; exact (hCtop _ hxF hxt).1)
      rw [hval, UnT.tr_map, hγeq] at e1
      rw [UnT.tr_map, hγeq] at e2
      set Y := T'.map Ψ' with hY
      have hcnU := hc.ups n (by omega)
      have hBκc : Bases κ (c n) := ⟨hκE', upsPt_inE hcnU.1, hc.bot n (by omega), hcnU.2⟩
      have hΨ'Tc : ∀ x ∈ F', Ψ' x ∈ Tset (c n) := fun x hx =>
        T_of_inSeg_E (upsPt_inE hcnU.1) (InSeg.self hcnU.2) (hΨ'b x hx).1 (hΨ'b x hx).2
      have hqY : UnT.Qs κ Y := UnT.Qs_map _ T' hqT'
      have hlYc : UnT.Lv (· ∈ Tset (c n)) (UnT.tr (Dl (c n) M) Y) :=
        UnT.Lv_tr (Dl_spec (upsPt_inE hcnU.1) hcnU.2 M).1 Y
          (UnT.Lv_map T' (UnT.Lv_map t (UnT.Lv_mono (fun p hp => hΨ'Tc _ (hCF' p hp)) t hl)))
      have hyDpc : UnT.ev (c n) (UnT.tr (Dl (c n) M) Y) < Dp (c n) M := by
        rw [← e1, ← hDpΨ]
        exact P4.2.1 (hCF' _ hxF) hDpF' (hCtop _ hxF hxt).2.2.2
      have hNdc : UnT.Nd (c n) (· < Dp (c n) M) (UnT.tr (Dl (c n) M) Y) :=
        UnT.Nd_mono (fun p hp => lt_of_le_of_lt hp hyDpc) _
          (unLe hBκc _ hlYc e2 (UnT.Qs_tr _ _ hqY)).2
      -- the decision `Γ^* ≥ γ` at `γ = Ψ'(β)`: the high heads over `β` go to high heads over `γ` (`Ψ'` is
      -- increasing on `F'` and `β ∈ F'`)
      have hlF'T' : UnT.Lv (· ∈ F') T' := UnT.Lv_map t (UnT.Lv_mono (fun p hp => hCF' p hp) t hl)
      have hHdY : UnT.HdA (Dl (c n) M) Y := by
        rw [← hγeq]
        refine UnT.HdA_map T' (UnT.Lv_mono (fun p hp hβp => ?_) T' hlF'T') (UnT.WF_HdA T' d3)
        rcases hβp.lt_or_eq with hlt | heq
        · exact (P4.2.1 hβF' hp hlt).le
        · rw [heq]
      have hlYγ : UnT.Lv (· ∈ Tset (Dl (c n) M)) Y :=
        UnT.Lv_map T' (UnT.Lv_map t (UnT.Lv_mono (fun p hp => hγeq ▸ hΨ'T _ (hCF' p hp)) t hl))
      obtain ⟨hWγ, hevγ⟩ := unTrB hBκc hM1 Y hqY hlYc e2 hNdc hHdY hlYγ
      have hBγ' : Bases (Dl (c n) M) (c (n + 1)) := hγeq ▸ hBγ
      have hκγ : κ ≤ Dl (c n) M := (hc.bot n (by omega)).le.trans (hγeq ▸ hc'γ).le
      obtain ⟨u1, u2⟩ := unUp_eq hBγ' hκγ Y hWγ hlYγ hqY
      have hmm : Y.map (up (Dl (c n) M) (c (n + 1))) =
          t.map (fun x => up (Dl (c n) M) (c (n + 1)) (Ψ' (pi β (b (n + 1)) x))) := by
        rw [hY, hT', UnT.map_map, UnT.map_map]; rfl
      rw [hmm] at u1 u2
      show up (Ψ' β) (c (n + 1)) (Ψ' (pi β (b (n + 1)) (UnT.ev (b (n + 1)) t))) = _ ∧ _
      rw [hγeq, e1, hevγ]
      exact ⟨u1, u2⟩

theorem unFrag_aux (m : ℕ) : ∀ {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}}, Chain κ b m →
    Chain κ c m → TrInnerAll κ b c m → ∀ F : Finset Ordinal.{0}, ↑F ⊆ DD κ b m →
    (∀ k, k < m → b k ∈ F) → ∃ Ψ, UnFragConcl κ b c m F Ψ := by
  induction m with
  | zero =>
    intro κ b c hb hc hI F hF hbF
    obtain ⟨Ψ, hΨ⟩ := trFrag_aux 0 hb hc hI F hF hbF
    exact ⟨Ψ, hΨ, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ m ih =>
    intro κ b c hb hc hI F hF hbF
    rcases m with _ | n
    · exact unFrag_one hb hc hF hbF
    · exact unFrag_step (fun F' hF' hbF' => ih hb.of_succ hc.of_succ hI.of_succ F' hF' hbF') hI hb hc hF hbF

/-- **Theorem FRAG with the hull isomorphism on terms with uncountable arguments at code levels**, under
`Tr.TrInnerAll κ b c m`: the conclusion of `Tr.trFrag` and, for every `k < m`, `Ψ(t[b_k; p]) = t[c_k; Ψ p]` for
terms with levels over `κ`, leaves in `F ∩ T^{b_k}` and value in `F ∩ seg(b_k)`. -/
theorem unFrag {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m)
    (hc : Chain κ c m) (hI : TrInnerAll κ b c m) (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) :
    ∃ Ψ, UnFragConcl κ b c m F Ψ := by
  classical
  set F₁ := F ∪ (Finset.range m).image b with hF₁
  have hbD : ∀ k, k < m → b k ∈ DD κ b m := by
    intro k hk
    have hbk := hb.ups k hk
    have hBk : Bases κ (b k) := ⟨upsPt_inE hb.kap, upsPt_inE hbk.1, hb.bot k hk, hbk.2⟩
    refine DD_mono (show k + 1 ≤ m by omega) (Or.inr ⟨InSeg.self hbk.2, (pi_base hBk).1.1, ?_⟩)
    exact (pi_base hBk).1.2.trans ((Iio_sub_DD k).trans (ClS.sub _))
  have hF₁ : ↑F₁ ⊆ DD κ b m := by
    intro x hx
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with h | h
    · exact hF h
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      exact hbD k (Finset.mem_range.1 hk)
  have hbF₁ : ∀ k, k < m → b k ∈ F₁ := fun k hk =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hk))
  obtain ⟨Ψ, hT, hU⟩ := unFrag_aux m hb hc hI F₁ hF₁ hbF₁
  have hsub : F ⊆ F₁ := Finset.subset_union_left
  refine ⟨Ψ, ?_, fun k hk t hq hw hl hlT hxF hs =>
    hU k hk t hq hw (UnT.Lv_mono (fun p hp => hsub hp) t hl) hlT (hsub hxF) hs⟩
  have hsub' : (↑F : Set Ordinal.{0}) ⊆ ↑F₁ := Finset.coe_subset.2 hsub
  obtain ⟨⟨⟨⟨Q1, Q2, Q3, Q4, Q5, Q6, Q7⟩, Q8⟩, Q9⟩, Q10⟩ := hT
  refine ⟨⟨⟨⟨fun x hx => Q1 x (hsub hx), fun k hk x hx => Q2 k hk x (hsub hx),
    fun k hk _ => Q3 k hk (hbF₁ k hk), ⟨(Q4.2.1.mono hsub').injOn.bijOn_image,
      Q4.2.1.mono hsub', fun x hx y hy z hz => Q4.2.2 x (hsub hx) y (hsub hy) z (hsub hz)⟩,
    fun x hx y hy => Q5 x (hsub hx) y (hsub hy), fun x hx => Q6 x (hsub hx),
    fun x hx => Q7 x (hsub hx)⟩, fun x hx hI => Q8 x (hsub hx) hI⟩,
    fun hm x hx hxD => Q9 hm x (hsub hx) hxD⟩, fun k hk x hx hs hT => Q10 k hk x (hsub hx) hs hT⟩

/-- **FRAG with the hull isomorphism, unconditionally on the chains** (`Tv.tvInnerAll`, i.e. from
`R2.tvSeg_pi`). -/
theorem unFragV {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m) (hc : Chain κ c m)
    (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) : ∃ Ψ, UnFragConcl κ b c m F Ψ :=
  unFrag hb hc (Tv.tvInnerAll hb hc) F hF

end Googology.Trans.PoR.InaccPsi.R2.Un
