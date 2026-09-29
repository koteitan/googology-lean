import Googology.Trans.PSS.Main.Fold
import Googology.Trans.PSS.Main.PLAux2

/-!
# Lemma PL (`proof/PROOF-3.md` §14.3)

For a standard epsilon root `N` with `α = o(N)`, a fold input `Y` after the prefix `pre`,
`ξ = α + o(pre)` and `K = lh(κ^α_ξ)`, if `Y` is a jump (`o(Y) > lead(K)`), then every element
`γ` of the localization of `𝒯(Y)` other than `𝒯(Y)` itself is at most `K`.

`pl` follows from the syntactic form `plSyn`: every such `γ` is at most `o(N)` or at most an
earlier fold input (the jump hypothesis is not needed for it).  Proof of `plSyn`: `γ` is a
suffix maximum below `𝒯(Y)` (`mem_loc_dropLast`), so its level exceeds that of `𝒯(Y)`
(`level_gt_of_sufMax`, [W07a] Lemma 4.9 read on `T¹`) and `γ = 𝒯(z)` for a standard epsilon
root `z < Y` (`root_of_eps_term`).  KEY (for epsilon `Y`) or `eps_root_le_hi'` (otherwise)
puts `z` below `(0, X)` for a proper prefix `X` of the children of `Y`, and `pl_core`
(`Main/PLAux2.lean`: the fold inputs, Lemma 10 and G\* for `E < W`) bounds `(0, X)` by `N`
or an earlier input.  This replaces S-run, LV and the case analysis of the paper.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- **PL, syntactic form**: the intermediate elements of the localization of `𝒯(Y)` are at most
`o(N)` or at most an earlier fold input. -/
theorem plSyn {N : Tm} (hN : Std N) (heps : isEps N = true) (pre : List Tm) (Y : Tm)
    (post : List Tm) (hsplit : foldInputs N = pre ++ Y :: post) (K : Ordinal.{0})
    (_hK : IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K)
    (_hY : lead K < ordOf [Y]) :
    ∀ γ ∈ (loc (trTm Y)).dropLast, γ.val ≤ ordOf [N] ∨ ∃ Y' ∈ pre, γ.val ≤ ordOf [Y'] := by
  intro γ hγ
  have hNeq := std_node_y hN
  have hN' : Std (.node 0 N.cs) := by rw [← hNeq]; exact hN
  have he' : isEps (.node 0 N.cs) = true := by rw [← hNeq]; exact heps
  have hsplit' : foldInputs (.node 0 N.cs) = pre ++ Y :: post := by rw [← hNeq]; exact hsplit
  have hYmem : Y ∈ foldInputs N := by rw [hsplit]; simp
  have hYstd : Std Y := std_foldInputs hN heps Y hYmem
  have hYeq := std_node_y hYstd
  set b := trTm Y with hbdef
  have hbv : b.val = ordOf [Y] := val_trTm_root hYstd
  have hbn : NFP b := trTm_nfp Y
  have hb0 : b.lvl = 0 := by rw [hbdef, trTm_lvl, hYeq]; rfl
  have h1 := one_lt_ordOf_eps hN heps
  have hbeq : b = .th 0 (argD b.arg ++ argE b.arg) := by
    rw [argD_append_argE, ← hb0, WP.eta]
  rcases le_or_gt b.val (ordOf [N]) with hbα | hαb
  · left
    have hsub := mem_loc_sub0 (List.dropLast_subset _ hγ)
    have hbn' : NFP (.th 0 (argD b.arg ++ argE b.arg)) := by rw [← hbeq]; exact hbn
    rw [hbeq] at hsub
    have := val_le_of_mem_sub0 hbn' hsub
    rw [← hbeq] at this
    exact le_trans this hbα
  obtain ⟨hsuf, hγlt⟩ := mem_loc_dropLast hbn hb0 (lt_trans h1 hαb) hγ
  by_cases hγα : γ.val ≤ ordOf [N]
  · exact Or.inl hγα
  push Not at hγα
  have hlev : WP.valS (argD b.arg) < WP.valS (argD γ.arg) :=
    level_gt_of_sufMax (Δ := argD b.arg) (η := argE b.arg) (by rw [← hbeq]; exact hbn)
      (by rw [argD_append_argE]) (by rw [argD_append_argE]) (by rw [← hbeq]; exact hsuf)
      (by rw [← hbeq]; exact hγlt)
  obtain ⟨hγn, hγ0⟩ := sub0_spec hbn hsuf.1
  have hγD : argD γ.arg ≠ [] := by
    intro h; rw [h, WP.valS_nil] at hlev; exact absurd hlev (not_lt.mpr zero_le)
  have hγe := isEpsLevel_of_argD hγ0 hγD
  obtain ⟨z, hz, hze, hTz, hzY, hΔz⟩ :=
    root_of_eps_term hγn hγe hYstd (by rw [← hbv]; exact hγlt.le)
  have hzv : ordOf [z] = γ.val := by rw [← val_trTm_root hz, hTz]
  have hzY' : z < Y := lt_of_le_of_ne hzY (fun e => by
    rw [e, ← hbdef] at hTz; rw [hTz] at hγlt; exact lt_irrefl _ hγlt)
  -- a proper prefix `X` of the children of `Y` with `z ≤ (0, X)`
  obtain ⟨X, hX, hXl, hXy, hzX⟩ : ∃ X, X <+: Y.cs ∧ X.length < Y.cs.length ∧
      (∀ x ∈ X, 1 ≤ x.y) ∧ z ≤ .node 0 X := by
    by_cases hYe : isEps Y = true
    · have hYs' : Std (.node 0 Y.cs) := by rw [← hYeq]; exact hYstd
      have hYe' : isEps (.node 0 Y.cs) = true := by rw [← hYeq]; exact hYe
      obtain ⟨hne, hall, hT⟩ := trTm_root_eps hYs' hYe'
      have hl : (Y.cs.getLast hne).y = 0 + 1 := by rw [hall _ (List.getLast_mem hne)]
      have hbD : argD b.arg = deltaOf 0 Y.cs := by
        rw [hbdef, hYeq, hT, WP.arg_th]; exact (argD_eps hne hl).1
      rcases key_eps_root hYs' hYe' hz hze (by rw [← hYeq]; exact hzY') with hle | hle
      · exfalso; rw [← hΔz, ← hbD] at hle; exact absurd hlev (not_lt.mpr hle)
      · refine ⟨Y.cs.take (jOf 0 Y.cs), List.take_prefix _ _, ?_, ?_, hle⟩
        · have := runStart_lt (ds := Y.cs.map (dOf 0)) (by simpa using hne)
          rw [List.length_map] at this
          rw [List.length_take, jOf]; omega
        · intro x hx; rw [y_of_eps_child hYstd hYe (List.mem_of_mem_take hx)]
    · have hYne : isEps Y = false := by simpa using hYe
      have hYc : Y.cs ≠ [] := by
        intro h
        have hY1 : Y = .node 0 [] := by rw [hYeq, h]
        rw [hY1, ordOf_leaf'] at hbv
        exact absurd (lt_trans h1 hαb) (by rw [hbv]; exact lt_irrefl _)
      obtain ⟨-, hzh⟩ := eps_root_le_hi' hYstd hYne hYc hz hze hzY
      obtain ⟨C, hC⟩ : ∃ C, Y.cs.getLast? = some C := by
        cases h' : Y.cs.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h') hYc
        | some C => exact ⟨C, rfl⟩
      obtain ⟨-, hCl, -⟩ := last_child_of_noneps hYstd hYne hC
      have hsp := cs_eq_hi_append_lo hYstd
      refine ⟨hiOf Y, ⟨loOf Y, hsp.symm⟩, ?_, ?_, hzh⟩
      · rw [hsp, List.length_append]; have := List.length_pos_of_mem hCl; omega
      · intro x hx; simpa using (List.mem_filter.mp hx).2
  rcases pl_core hN' he' pre Y post hsplit' hX hXl hXy with h | ⟨Y', hY', h⟩
  · left; rw [← hzv]; exact ordOf_single_le hz hN (by rw [hNeq]; exact le_trans hzX h)
  · right
    refine ⟨Y', hY', ?_⟩
    have hY's : Std Y' := std_foldInputs hN heps Y' (by rw [hsplit]; simp [hY'])
    rw [← hzv]; exact ordOf_single_le hz hY's (le_trans hzX h)

theorem le_sum_of_mem (pre : List Tm) {Y' : Tm} (h : Y' ∈ pre) :
    ordOf [Y'] ≤ (pre.map fun Y => ordOf [Y]).sum := by
  induction pre with
  | nil => simp at h
  | cons Z pre ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_self_add
    · exact le_trans (ih h) le_add_self

/-- **PL** (`proof/PROOF-3.md` §14.3). -/
theorem pl {N : Tm} (hN : Std N) (heps : isEps N = true) (pre : List Tm) (Y : Tm)
    (post : List Tm) (hsplit : foldInputs N = pre ++ Y :: post) (K : Ordinal.{0})
    (hK : IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K)
    (hY : lead K < ordOf [Y]) : ∀ γ ∈ (loc (trTm Y)).dropLast, γ.val ≤ K := by
  intro γ hγ
  have hξK := le_trans (le_kap _ _) hK.le
  rcases plSyn hN heps pre Y post hsplit K hK hY γ hγ with h | ⟨Y', hY', h⟩
  · exact le_trans h (le_trans le_self_add hξK)
  · exact le_trans h (le_trans (le_sum_of_mem pre hY') (le_trans le_add_self hξK))

end Googology.Trans.PSS.Main
