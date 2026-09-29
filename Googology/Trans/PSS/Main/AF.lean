import Googology.Trans.PSS.Main.BarNonEps
import Googology.Trans.PSS.Main.Good

/-!
# Lemma AF for non-epsilon roots (`proof/PROOF-4.md` §15.1)

* `barO_anchor`: for a non-epsilon root `N` whose `log` has at least two roots,
  `bar(o(N)) = o(anchor N)` (Fact BAR).
* **Lemma G** (`lemmaG`, absorption shape): if the first `y = 0` child `u` of a
  non-epsilon `Z` absorbs `(0, hi)`, then `ch(u) = hi ++ R` with `R ≠ ()` of `y = 0`.
* **Lemma H** (`lemmaH`, for `B = hi(Z)`): in a good set `F`, `o(Z) ∈ F` gives
  `o((0, hi(Z))) ∈ F`.  (The paper's Case 1, `Z` epsilon, is only needed for proper
  initial segments `B` of `hi(Z)`, which Lemma AF does not use.)
* **Lemma AF, non-epsilon case** (`lemmaAF_noneps`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

theorem barO_anchor {N : Tm} (hN : Std N) (hne : isEps N = false) (hcs : N.cs ≠ [])
    (h2 : 2 ≤ (bigL N).length) :
    ∃ a, anchor N = some a ∧ barO (ordOf [N]) = ordOf [a] := by
  obtain ⟨hlen, hdrop⟩ := bigL_dropLast hN hne hcs h2
  set a := Tm.node 0 N.cs.dropLast with ha
  have hanc : anchor N = some a := by
    have := anchor_node hlen
    rw [← std_node_y hN] at this; exact this
  have has : Std a := std_anchor hN hanc
  refine ⟨a, hanc, ?_⟩
  set F := bigL N
  have hFstd : StdOrd F := stdOrd_bigL hN
  have hl : ANF (anfOf F) := anf_anfOf hFstd
  have hk : 2 ≤ (anfOf F).length := by simp [anfOf]; exact h2
  have hsum : (anfOf F).sum = ordOf F := sum_anfOf hFstd
  have htF : ordOf [N] = ω ^ (anfOf F).sum := by rw [hsum, ordOf_single_eq_opow hN]
  have hT : ω ^ (anfOf F).sum < T1bound := htF ▸ ordOf_lt_T1bound (stdOrd_single hN)
  rw [htF, factBar hl hk hT, ordOf_single_eq_opow has, ← hdrop]
  congr 1
  rw [show (anfOf F).dropLast = anfOf F.dropLast by simp [anfOf, List.map_dropLast],
    sum_anfOf (hdrop ▸ stdOrd_bigL has)]

/-- Good sets are closed under bar at roots. -/
theorem Good.bar_root {F : Set Ordinal.{0}} (hF : Good F) {N : Tm} (hN : Std N) (hcs : N.cs ≠ [])
    (hNF : ordOf [N] ∈ F) : barO (ordOf [N]) ∈ F :=
  hF.2.2.2.2 _ hNF (pr_ordOf_single hN) (one_lt_ordOf_of_cs hN hcs)
    (ordOf_lt_T1bound (stdOrd_single hN))

/-- **Lemma G** (absorption shape, `proof/PROOF-4.md` §15.1). -/
theorem lemmaG {Z u : Tm} (hZ : Std Z) (hu : (loOf Z).head? = some u)
    (habs : Tm.node 0 (hiOf Z) < u) :
    ∃ R, u.cs = hiOf Z ++ R ∧ R ≠ [] ∧ ∀ r ∈ R, r.y = 0 := by
  have hulo : u ∈ loOf Z := List.mem_of_mem_head? hu
  have hu0 : u.y = 0 := y_of_mem_lo hulo
  have huZ : u < Z := lt_of_mem_lo hZ hulo
  have hus : Std u := std_of_tgood_y0 (tgood_child hZ (List.mem_of_mem_filter hulo)) hu0
  have h1 : u.cs < hiOf Z ++ loOf Z := by
    rw [← cs_eq_hi_append_lo hZ]
    exact (Tm.lt_iff_cs_lt (by rw [hu0, std_node_y hZ]; rfl)).mp huZ
  have h2 : hiOf Z < u.cs := by
    have := habs
    rw [std_node_y hus] at this
    exact (Tm.lt_iff_cs_lt (s := Tm.node 0 (hiOf Z)) (t := Tm.node 0 u.cs) rfl).mp this
  obtain ⟨R, hR, hRlt⟩ := eq_append_of_between (Or.inr h2) h1
  refine ⟨R, hR, fun h => ?_, fun r hr => ?_⟩
  · rw [h, List.append_nil] at hR; rw [hR] at h2; exact lt_irrefl _ h2
  · have hdR : Desc R := by
      have := desc_cs_of_std hus
      rw [hR] at this
      exact (List.pairwise_append.mp this).2.1
    have := head_le_of_lt (desc_lo hZ) hdR hRlt r hr u hu
    have := Tm.y_le_of_le this
    omega

/-- The prefix nodes of a non-epsilon `Z` from `(0, hi ++ [lo_1])` up to `Z` lie in a good
set containing `o(Z)`. -/
theorem prefix_in_good {F : Set Ordinal.{0}} (hF : Good F) {Z : Tm} (hZ : Std Z)
    (hZF : ordOf [Z] ∈ F) :
    ∀ k j, (hiOf Z).length + 1 ≤ j → j ≤ Z.cs.length → Z.cs.length - j = k →
      ordOf [Tm.node 0 (Z.cs.take j)] ∈ F := by
  have hZs : Std (Tm.node 0 Z.cs) := by rw [← std_node_y hZ]; exact hZ
  have hsplit := cs_eq_hi_append_lo hZ
  intro k
  induction k with
  | zero =>
    intro j h1 h2 h3
    rw [List.take_of_length_le (by omega), ← std_node_y hZ]; exact hZF
  | succ k ih =>
    intro j h1 h2 h3
    have hN' := ih (j + 1) (by omega) (by omega) (by omega)
    set N' := Tm.node 0 (Z.cs.take (j + 1)) with hN'def
    have hN's : Std N' := std_take hZs _
    have hcs' : N'.cs = (hiOf Z) ++ (loOf Z).take (j + 1 - (hiOf Z).length) := by
      rw [hN'def, Tm.cs_node, hsplit, List.take_append]
      rw [List.take_of_length_le (by omega)]
    -- `N'` is not epsilon and its `log` has at least two roots
    have hlo' : loOf N' = (loOf Z).take (j + 1 - (hiOf Z).length) := by
      show N'.cs.filter _ = _
      rw [hcs', List.filter_append]
      obtain ⟨-, -, h3, -⟩ := filter_hi_lo_of_std hZ
      rw [h3, List.nil_append, List.filter_eq_self]
      intro s hs; simp [y_of_mem_lo (List.mem_of_mem_take hs)]
    have hlolen : 2 ≤ (loOf N').length := by
      rw [hlo', List.length_take]
      have : Z.cs.length = (hiOf Z).length + (loOf Z).length := by rw [hsplit, List.length_append]
      omega
    have hlone : loOf N' ≠ [] := by
      intro h; rw [h] at hlolen; simp at hlolen
    have hN'cs : N'.cs ≠ [] := by
      intro h; apply hlone; show N'.cs.filter _ = []; rw [h]; rfl
    have hN'e : isEps N' = false := by
      have hlast : (N'.cs).getLast? = ((loOf Z).take (j + 1 - (hiOf Z).length)).getLast? := by
        rw [hcs', List.getLast?_append_of_ne_nil _ (by rw [← hlo']; exact hlone)]
      obtain ⟨x, hx⟩ : ∃ x, ((loOf Z).take (j + 1 - (hiOf Z).length)).getLast? = some x := by
        cases h : ((loOf Z).take (j + 1 - (hiOf Z).length)).getLast? with
        | none => rw [List.getLast?_eq_none_iff] at h; rw [hlo', h] at hlone; exact absurd rfl hlone
        | some x => exact ⟨x, rfl⟩
      have hx0 : x.y = 0 := y_of_mem_lo (List.mem_of_mem_take (List.mem_of_getLast? hx))
      rw [hN'def]; simp only [isEps]
      rw [show (Z.cs.take (j + 1)).getLast? = some x from by rw [← hx, ← hlast, hN'def]; rfl]
      simp [hx0]
    have hbig : 2 ≤ (bigL N').length := by
      rw [bigL_eq hN's]
      obtain ⟨b0, B, hb⟩ := List.exists_cons_of_ne_nil hlone
      have hdA : Desc (ancL N') := by unfold ancL; split_ifs <;> simp [Desc]
      rw [hb, addT_cons hdA, List.length_append]
      rw [hb] at hlolen
      simp at hlolen ⊢; omega
    obtain ⟨a, ha, hbar⟩ := barO_anchor hN's hN'e hN'cs hbig
    have hadef : a = Tm.node 0 (Z.cs.take j) := by
      rw [hN'def, anchor_node (by simp; omega)] at ha
      simp only [Option.some.injEq] at ha
      rw [← ha, List.dropLast_eq_take, List.take_take]
      congr 2; simp; omega
    rw [← hadef, ← hbar]
    exact hF.bar_root hN's hN'cs hN'

/-! ## Lemma H -/

theorem hiOf_loOf_split {y : ℕ} {A B : List Tm} (hA : ∀ a ∈ A, a.y = 1) (hB : ∀ b ∈ B, b.y = 0) :
    hiOf (.node y (A ++ B)) = A ∧ loOf (.node y (A ++ B)) = B := by
  constructor
  · show (A ++ B).filter _ = A
    rw [List.filter_append, List.filter_eq_self.mpr (fun a ha => by simp [hA a ha]),
      List.filter_eq_nil_iff.mpr (fun b hb => by simp [hB b hb]), List.append_nil]
  · show (A ++ B).filter _ = B
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun a ha => by simp [hA a ha]),
      List.filter_eq_self.mpr (fun b hb => by simp [hB b hb]), List.nil_append]

theorem isEps_false_of_last {cs : List Tm} {x : Tm} (h : cs.getLast? = some x) (hx : x.y = 0) :
    isEps (.node 0 cs) = false := by
  simp [isEps, h, hx]

theorem roots_in_good {F : Set Ordinal.{0}} (hF : Good F) {S : List Tm} (hS : StdOrd S)
    (hSF : ordOf S ∈ F) : ∀ t ∈ S, ordOf [t] ∈ F := by
  intro t ht
  have := (hF.2.2.1 (anfOf S) (anf_anfOf hS) (by rw [sum_anfOf hS]; exact hSF)).1
  exact this _ (List.mem_map.mpr ⟨t, ht, rfl⟩)

/-- **Lemma H** (`proof/PROOF-4.md` §15.1), for `B = hi(Z)`. -/
theorem lemmaH {F : Set Ordinal.{0}} (hF : Good F) : ∀ (n : ℕ) {Z : Tm}, Z.size ≤ n → Std Z →
    isEps Z = false → hiOf Z ≠ [] → ordOf [Z] ∈ F → ordOf [Tm.node 0 (hiOf Z)] ∈ F
  | 0, Z, hs, _, _, _, _ => absurd hs (by have := TR.Tm.size_pos Z; omega)
  | n + 1, Z, hs, hZ, hZe, hhi, hZF => by
    have hsplit := cs_eq_hi_append_lo hZ
    have hcs : Z.cs ≠ [] := by rw [hsplit]; simp [hhi]
    obtain ⟨C, hC⟩ : ∃ C, Z.cs.getLast? = some C := by
      cases h' : Z.cs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h') hcs
      | some C => exact ⟨C, rfl⟩
    obtain ⟨-, hCl, -⟩ := last_child_of_noneps hZ hZe hC
    have hlo : loOf Z ≠ [] := List.ne_nil_of_mem hCl
    obtain ⟨u, lo', hlo_eq⟩ := List.exists_cons_of_ne_nil hlo
    have hu_head : (loOf Z).head? = some u := by rw [hlo_eq]; rfl
    have hulo : u ∈ loOf Z := by rw [hlo_eq]; simp
    have hu0 : u.y = 0 := y_of_mem_lo hulo
    have hus : Std u := std_of_tgood_y0 (tgood_child hZ (List.mem_of_mem_filter hulo)) hu0
    have hhi1 : ∀ a ∈ hiOf Z, a.y = 1 := fun a ha => y_of_mem_hi hZ ha
    set H0 := Tm.node 0 (hiOf Z) with hH0
    -- `Z1 = (0, hi ++ [u])` is in `F`
    have hZ1take : Z.cs.take ((hiOf Z).length + 1) = hiOf Z ++ [u] := by
      rw [hsplit, List.take_append, List.take_of_length_le (by omega), hlo_eq]; simp
    have hlenZ : (hiOf Z).length + 1 ≤ Z.cs.length := by
      rw [hsplit, List.length_append, hlo_eq]; simp
    have hZ1F := prefix_in_good hF hZ hZF _ ((hiOf Z).length + 1) le_rfl hlenZ rfl
    rw [hZ1take] at hZ1F
    set Z1 := Tm.node 0 (hiOf Z ++ [u]) with hZ1
    have hZs : Std (Tm.node 0 Z.cs) := by rw [← std_node_y hZ]; exact hZ
    have hZ1s : Std Z1 := by rw [hZ1, ← hZ1take]; exact std_take hZs _
    have hZ1last : Z1.cs.getLast? = some u := by simp [hZ1]
    have hZ1e : isEps Z1 = false := isEps_false_of_last hZ1last hu0
    obtain ⟨hhiZ1, hloZ1⟩ := hiOf_loOf_split (y := 0) (A := hiOf Z) (B := [u]) hhi1
      (by simp [hu0])
    have hZ1cs : Z1.cs ≠ [] := by simp [hZ1]
    have hdA : ∀ N : Tm, Desc (ancL N) := fun N => by unfold ancL; split_ifs <;> simp [Desc]
    have hancZ1 : ancL Z1 = [H0] := by unfold ancL; rw [hhiZ1]; simp [hhi, hH0]
    by_cases habs : H0 < u
    · -- (2c) `(0, hi)` is absorbed by `u`: follow `lh(Z1)`
      obtain ⟨R, huR, hRne, hR0⟩ := lemmaG hZ hu_head habs
      have hu_eq : u = Tm.node 0 (hiOf Z ++ R) := by rw [std_node_y hus, huR]
      obtain ⟨hhiu, hlou⟩ := hiOf_loOf_split (y := 0) hhi1 hR0
      rw [← hu_eq] at hhiu hlou
      have hancu : ancL u = [H0] := by unfold ancL; rw [hhiu]; simp [hhi, hH0]
      have hbigu : bigL u = addT [H0] R := by rw [bigL_eq hus, hancu, hlou]
      -- the roots of `lh(Z1)` are in `F`
      have hL := lemmaL hZ1s
      have hlhF : ordOf (lh Z1) ∈ F :=
        hF.2.2.2.1 _ hZ1F (one_lt_ordOf_of_cs hZ1s hZ1cs) (ordOf_lt_T1bound (stdOrd_single hZ1s))
          _ hL
      have hlh : lh Z1 = addT [Z1] (bigL u) := by
        rw [lh_eq_of_noneps hZ1s hZ1e, lam_eq_bigL hZ1last]
      have hroot : ∀ t ∈ bigL u, ordOf [t] ∈ F := by
        intro t ht
        refine roots_in_good hF (stdOrd_lh hZ1s) hlhF t ?_
        rw [hlh]; exact mem_addT_right (by simp [Desc]) ht
      obtain ⟨R1, R', hR1⟩ := List.exists_cons_of_ne_nil hRne
      by_cases habs2 : H0 < R1
      · -- recurse on `R1`
        have hR1mem : R1 ∈ bigL u := by
          rw [hbigu, hR1, addT_cons (by simp [Desc])]; simp
        have hR1F := hroot R1 hR1mem
        have hR1u : R1 ∈ u.cs := by rw [huR, hR1]; simp
        have hR10 : R1.y = 0 := hR0 R1 (by rw [hR1]; simp)
        have hR1s : Std R1 := std_of_tgood_y0 (tgood_child hus hR1u) hR10
        have hR1head : (loOf u).head? = some R1 := by rw [hlou, hR1]; rfl
        obtain ⟨R'', hR1R, hR''ne, hR''0⟩ := lemmaG hus hR1head (by rw [hhiu]; exact habs2)
        rw [hhiu] at hR1R
        obtain ⟨R2, R2', hR2⟩ := List.exists_cons_of_ne_nil hR''ne
        have hR1eq : R1 = Tm.node 0 (hiOf Z ++ R'') := by rw [std_node_y hR1s, hR1R]
        have hR1e : isEps R1 = false := by
          rw [hR1eq]
          refine isEps_false_of_last (x := (R2 :: R2').getLast (by simp)) ?_ ?_
          · rw [hR2, List.getLast?_append_of_ne_nil _ (by simp),
              List.getLast?_eq_some_getLast (by simp)]
          · exact hR''0 _ (by rw [hR2]; exact List.getLast_mem _)
        obtain ⟨hhiR1, -⟩ := hiOf_loOf_split (y := 0) hhi1 hR''0
        rw [← hR1eq] at hhiR1
        have hsize : R1.size ≤ n := by
          have h1 : R1.size < u.size := by rw [std_node_y hus]; exact Tm.size_lt_of_mem hR1u
          have h2 : u.size < Z.size := by
            rw [std_node_y hZ]; exact Tm.size_lt_of_mem (List.mem_of_mem_filter hulo)
          omega
        have := lemmaH hF n hsize hR1s hR1e (by rw [hhiR1]; exact hhi) hR1F
        rwa [hhiR1] at this
      · -- `(0, hi)` survives in `log u`
        have hH0mem : H0 ∈ bigL u := by
          rw [hbigu, hR1, addT_cons (by simp [Desc])]
          simp [habs2]
        exact hroot H0 hH0mem
    · -- (2b) `log(Z1) = ((0, hi), u)`: Fact BAR
      have hbig : 2 ≤ (bigL Z1).length := by
        rw [bigL_eq hZ1s, hancZ1, hloZ1, addT_cons (by simp [Desc])]
        simp [habs]
      obtain ⟨a, ha, hbar⟩ := barO_anchor hZ1s hZ1e hZ1cs hbig
      have haeq : a = H0 := by
        rw [hZ1, anchor_node (by simp; exact List.length_pos_of_ne_nil hhi)] at ha
        simp only [Option.some.injEq] at ha
        rw [← ha]; simp [hH0]
      rw [← haeq, ← hbar]
      exact hF.bar_root hZ1s hZ1cs hZ1F

/-- **Lemma AF, non-epsilon case** (`proof/PROOF-4.md` §15.1 (ii), (iii)). -/
theorem lemmaAF_noneps {F : Set Ordinal.{0}} (hF : Good F) {N a : Tm} (hN : Std N)
    (hne : isEps N = false) (ha : anchor N = some a) (hNF : ordOf [N] ∈ F) : ordOf [a] ∈ F := by
  have hNcs : 2 ≤ N.cs.length := by
    rw [std_node_y hN] at ha; simp only [anchor] at ha; split_ifs at ha with h; exact h
  have hcs : N.cs ≠ [] := by intro h; rw [h] at hNcs; simp at hNcs
  have haeq : a = Tm.node 0 N.cs.dropLast := by
    rw [std_node_y hN, anchor_node hNcs] at ha; simpa using ha.symm
  by_cases h2 : 2 ≤ (bigL N).length
  · obtain ⟨a', ha', hbar⟩ := barO_anchor hN hne hcs h2
    rw [ha] at ha'; cases ha'
    rw [← hbar]; exact hF.bar_root hN hcs hNF
  · -- `log N = (C_k)`: the anchor is `(0, hi)`
    push Not at h2
    obtain ⟨C, hC⟩ : ∃ C, N.cs.getLast? = some C := by
      cases h' : N.cs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h') hcs
      | some C => exact ⟨C, rfl⟩
    obtain ⟨-, hCl, -⟩ := last_child_of_noneps hN hne hC
    have hlo : loOf N ≠ [] := List.ne_nil_of_mem hCl
    have hdA : Desc (ancL N) := by unfold ancL; split_ifs <;> simp [Desc]
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hlo
    have hbig : bigL N = (ancL N).takeWhile (fun a => !decide (a < x)) ++ x :: xs := by
      rw [bigL_eq hN, hx, addT_cons hdA]
    have hxs : xs = [] := by
      rw [hbig, List.length_append] at h2; simp at h2
      exact List.length_eq_zero_iff.mp (by omega)
    subst hxs
    have hsplit := cs_eq_hi_append_lo hN
    have hhi : hiOf N ≠ [] := by
      intro h
      rw [hsplit, h, hx] at hNcs; simp at hNcs
    have hd : N.cs.dropLast = hiOf N := by rw [hsplit, hx]; simp
    rw [haeq, hd]
    exact lemmaH hF _ le_rfl hN hne hhi hNF

end Googology.Trans.PSS.Main
