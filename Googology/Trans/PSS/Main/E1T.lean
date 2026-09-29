import Googology.Trans.PSS.Main.E1TAux2

/-!
# `E1_T` (`proof/PROOF-2.md` §12.5)

For a standard epsilon root `N` with `α = 𝒯(N) = ϑ_0(Δ + η)` and fold inputs
`Y_1, …, Y_n`:

```
val J(Δ) + ζ_α = o(N) + o(Y_1) + ⋯ + o(Y_n),
```

where `J = t^α_τ ∘ ι_{τ,α}` (`Main/TIota.lean`).  With `lam_eq_jS` this is E1.  The proof
uses CI (`Main/CI.lean`) and NS (`lemmaNS`, `Main/BarEps.lean`).

With `W = (1, B)` the last child of `N`, `log_ω 𝒯_1(W) = Δ + ρ_W`, and `ζ_α = ρ_W`
(`zeta_eq_rho`, `Main/E1TAux.lean`), so the left side is `val J(log_ω 𝒯_1(W))`:

* `W = (1)` or `W` epsilon: `log_ω 𝒯_1(W) = 𝒯_1(W)`, and CI gives `o(Coll_A(W)) = o(Y_p)`,
  which absorbs `o(N)` and the earlier D-inputs (`dpart`, `Main/E1TAux2.lean`).
* otherwise `log_ω 𝒯_1(W) = Z`, the sum with absorption of `𝒯_1(1, B_1 … B_p)` and the
  `𝒯(E_j)`; on these items `J` and `o ∘ Coll_A` agree (CI) and keep the order (Mono\*,
  Lemma 10), so the absorption of `Z` is the absorption of the ordinal sum
  (`valS_jS_addAll`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- `log_ω 𝒯_1(W) = (𝒯_1(W))` when `𝒯_1(W)` is an epsilon number. -/
theorem logOmega_eq_self {w : WP} (hw : NFP w) (h : ω ^ w.val = w.val) : logOmega w = [w] := by
  obtain ⟨h1, h2, -⟩ := logOmega_spec hw
  refine eq_of_valS_eq h1 (NFS.single hw) ?_
  rw [valS_single]
  exact opow_inj (h2.trans h.symm)

/-- **`E1_T`** for `N = (0, H)`. -/
theorem e1T_node {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) :
    WP.valS (jS (trTm (.node 0 H)) (argD (trTm (.node 0 H)).arg)) + zetaT (trTm (.node 0 H)) =
      ordOf [.node 0 H] + ((foldInputs (.node 0 H)).map fun Y => ordOf [Y]).sum := by
  obtain ⟨hne, hall, hT⟩ := trTm_root_eps hN he
  obtain ⟨B, hW, hv, hg, hr⟩ := lastChild_spec hN he hne
  have hl : (H.getLast hne).y = 0 + 1 := hall _ (List.getLast_mem hne)
  have hΔ : argD (trTm (.node 0 H)).arg = dOf 0 (.node 1 B) := by
    rw [hT, WP.arg_th, (argD_eps hne hl).1, deltaOf_eq_last hne, hW]
  rw [hΔ, zeta_eq_rho hN he hne, hW]
  have hρ0 : ∀ q ∈ rhoOf 0 (.node 1 B), q.lvl = 0 := fun q hq => by
    have := (monOf_spec 0 (.node 1 B)).2.2.2.2 q hq; omega
  rw [← valS_jS_level0 (trTm (.node 0 H)) hρ0, ← valS_jS_append, ← (monOf_spec 0 _).1]
  -- the fold inputs
  have hlk : lastKids (.node 0 H) = B := by
    simp [lastKids, List.getLast?_eq_some_getLast hne, hW]
  have hpB : (B.takeWhile (fun c => decide (c.y = 1 + 1))).length ≤ B.length :=
    (List.takeWhile_sublist _).length_le
  obtain ⟨hhi, hhi'⟩ := hi_eq_take hv
  generalize hp : (B.takeWhile (fun c => decide (c.y = 1 + 1))).length = p at hhi hhi' hpB
  have hfold : ((foldInputs (.node 0 H)).map fun Y => ordOf [Y]).sum =
      ((List.range p).map
        (fun i => ordOf [.node 0 (addT H (collSum H (B.take (i + 1))))])).sum +
      ((B.filter (fun s => decide (s.y ≤ 1))).map fun c => ordOf [coll H c]).sum := by
    simp only [foldInputs, Tm.cs_node, hlk, hhi, List.length_take, min_eq_left hpB,
      List.map_append, List.sum_append, List.map_map]
    congr 2
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp, List.take_take, min_eq_left (show i + 1 ≤ p by omega)]
  rw [hfold, ← add_assoc, dpart hN hv hg hr p hpB]
  by_cases hB : B = []
  · -- `W = (1)`
    subst hB
    have hw : logOmega (trTm (.node 1 [])) = [trTm (.node 1 [])] := by
      refine logOmega_eq_self (trTm_nfp _) ?_
      rw [val_trTm_leaf]; exact opow_Om_succ 0
    rw [hw, valS_jS_cons, jS_nil, WP.valS_nil, add_zero]
    have := (item_take hN he hne hW hv hg hr 0).2.2.2
    simpa using this
  by_cases hl2 : (B.getLast hB).y = 1 + 1
  · -- `W` epsilon: all children have `y = 2`
    have hall2 := hv.eps_all hB hl2
    have hpl : p = B.length := by
      rw [← hp, List.takeWhile_eq_self_iff.mpr (fun c hc => by simp [hall2 c hc])]
    have hlo : B.filter (fun s => decide (s.y ≤ 1)) = [] :=
      List.filter_eq_nil_iff.mpr (fun c hc => by simp [hall2 c hc])
    have hw : logOmega (trTm (.node 1 B)) = [trTm (.node 1 B)] :=
      logOmega_eq_self (trTm_nfp _) (trTm_eps_isEps hB hl2).2
    rw [hw, valS_jS_cons, jS_nil, WP.valS_nil, add_zero, hlo, List.map_nil, List.sum_nil,
      add_zero, hpl, List.take_length]
    have := (item_take hN he hne hW hv hg hr B.length).2.2.2
    rwa [List.take_length] at this
  · -- `W` not epsilon: `log_ω 𝒯_1(W) = Z`
    have hZ : logOmega (trTm (.node 1 B)) = zOf 1 B := by
      obtain ⟨h1, h2, -⟩ := logOmega_spec (trTm_nfp (.node 1 B))
      refine eq_of_valS_eq h1 (zOf_spec 1 B).1 (opow_inj ?_)
      rw [h2, val_trTm_noneps hB hl2]
    have hhead : headPart 1 B = [[trTm (.node 1 (B.take p))]] := by
      unfold headPart
      rw [hhi']
      split_ifs with h
      · rfl
      · push Not at h; rw [h, trTm_leaf]
      · omega
    set lo := B.filter (fun c => decide (c.y ≤ 1)) with hlo
    set S := Tm.node 1 (B.take p) :: lo with hS
    have hitem : ∀ s ∈ S, Item (H := H) s := by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact item_take hN he hne hW hv hg hr p
      · obtain ⟨hsB, hs1⟩ := List.mem_filter.mp hs
        exact item_child hN he hne hW hv hg hr hsB (by simpa using hs1)
    have hzS : zOf 1 B = TR.addAll ((S.map trTm).map fun q => [q]) := by
      rw [zOf, hhead, hS, hlo]
      simp only [List.map_cons, List.map_map, List.cons_append, List.nil_append]
      rfl
    rw [hZ, hzS, valS_jS_addAll]
    · rw [List.map_map, hS, List.map_cons, List.sum_cons]
      congr 1
      · exact (hitem _ List.mem_cons_self).2.2.2
      · apply congrArg
        apply List.map_congr_left
        intro c hc
        exact (hitem c (by rw [hS]; exact List.mem_cons_of_mem _ hc)).2.2.2
    · intro q hq
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp hq
      exact trTm_nfp s
    · intro q hq ℓ hℓ hlt
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
      obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hℓ
      rw [(hitem s hs).2.2.2, (hitem s' hs').2.2.2]
      exact item_mono hN (hitem s hs) (hitem s' hs') hlt
    · intro ℓ hℓ
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hℓ
      rw [(hitem s hs).2.2.2]
      exact pr_ordOf_single (hitem s hs).2.2.1

/-- **`E1_T`** (`proof/PROOF-2.md` §12.5). -/
theorem e1T {N : Tm} (hN : Std N) (heps : isEps N = true) :
    WP.valS (jS (trTm N) (argD (trTm N).arg)) + zetaT (trTm N) =
      ordOf [N] + ((foldInputs N).map fun Y => ordOf [Y]).sum := by
  have hNeq := std_node_y hN
  have hN' : Std (.node 0 N.cs) := by rw [← hNeq]; exact hN
  have he' : isEps (.node 0 N.cs) = true := by rw [← hNeq]; exact heps
  have := e1T_node hN' he'
  rwa [← hNeq] at this

end Googology.Trans.PSS.Main
