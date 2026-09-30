import Googology.Trans.BMS.PoR.PSS.TR.Ops

/-!
# Unfolding the translation

`trTm s = trF (size s) s` does not depend on the fuel once it is at least the
size (`trF_eq_trTm`), so `trTm` satisfies the equations of `proof/PROOF-2.md`
§12.1 (`trTm_leaf`, `trTm_eps`, `trTm_noneps`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## Sizes -/

theorem sizeList_eq_sum : ∀ l : List Tm, Tm.sizeList l = (l.map Tm.size).sum
  | [] => by simp [Tm.sizeList]
  | c :: l => by rw [Tm.sizeList, sizeList_eq_sum l]; simp

theorem sizeList_le_of_sublist {l l' : List Tm} (h : l.Sublist l') :
    Tm.sizeList l ≤ Tm.sizeList l' := by
  rw [sizeList_eq_sum, sizeList_eq_sum]
  exact (h.map _).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem sizeList_dropLast_add {l : List Tm} (h : l ≠ []) :
    Tm.sizeList l.dropLast + (l.getLast h).size = Tm.sizeList l := by
  rw [sizeList_eq_sum, sizeList_eq_sum]
  conv_rhs => rw [← List.dropLast_append_getLast h]
  simp

theorem Tm.size_pos (t : Tm) : 0 < t.size := by
  obtain ⟨y, cs⟩ := t; rw [Tm.size]; omega

@[simp] theorem Tm.size_node (y : ℕ) (cs : List Tm) : (Tm.node y cs).size = Tm.sizeList cs + 1 := by
  rw [Tm.size]

/-- A sublist of all the children but the last is smaller by the last child. -/
theorem size_lt_of_sublist_dropLast {k : ℕ} {ch l : List Tm} (hne : ch ≠ [])
    (h : l.Sublist ch.dropLast) : (Tm.node k l).size < (Tm.node k ch).size := by
  have h1 := sizeList_le_of_sublist h
  have h2 := sizeList_dropLast_add hne
  have h3 := Tm.size_pos (ch.getLast hne)
  simp only [Tm.size_node]; omega

theorem size_le_of_mem {k : ℕ} {ch : List Tm} {c : Tm} (hc : c ∈ ch) :
    c.size + 1 ≤ (Tm.node k ch).size := by
  have := Tm.size_lt_of_mem (y := k) hc; omega

theorem take_sublist_dropLast {l : List Tm} {j : ℕ} (hj : j < l.length) :
    (l.take j).Sublist l.dropLast := by
  rw [List.dropLast_eq_take]
  exact (List.take_sublist_take_left (by omega))

theorem filter_sublist_dropLast {l : List Tm} (hne : l ≠ []) (p : Tm → Bool)
    (hp : p (l.getLast hne) = false) : (l.filter p).Sublist l.dropLast := by
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [List.filter_append, List.filter_singleton, hp]
  simp only [cond_false, List.append_nil]
  exact List.filter_sublist

/-! ## The fuel is enough -/

theorem runStart_lt {ds : List (List WP)} (h : ds ≠ []) : runStart ds < ds.length := by
  rw [runStart, List.getLast?_eq_some_getLast h]
  have hr : ds.reverse = ds.getLast h :: ds.dropLast.reverse := by
    conv_lhs => rw [← List.dropLast_append_getLast h]
    simp
  simp only
  rw [hr, List.dropWhile_cons_of_pos (by simp)]
  have h1 := (List.dropWhile_sublist (fun e => e == ds.getLast h) (l := ds.dropLast.reverse)).length_le
  have h2 : ds.dropLast.length + 1 = ds.length := by
    rw [List.length_dropLast]; have := List.length_pos_of_ne_nil h; omega
  simp only [List.length_reverse] at h1
  omega

theorem runStart_nil : runStart [] = 0 := rfl

/-- `epsImg` uses the prefix images only below the number of children. -/
theorem epsImg_congr {k : ℕ} {vs : List WP} {pre pre' : ℕ → WP}
    (h : ∀ j < vs.length, pre j = pre' j) : epsImg k vs pre = epsImg k vs pre' := by
  unfold epsImg
  dsimp only
  set j := runStart ((vs.map (fun v => splitLevel (logOmega v) (k + 1))).map Prod.fst) with hj
  by_cases h1 : 0 < j
  · have hne : vs ≠ [] := by
      rintro rfl
      simp [hj, runStart_nil] at h1
    have hlt := runStart_lt (ds := (vs.map (fun v => splitLevel (logOmega v) (k + 1))).map
      Prod.fst) (by simpa using hne)
    simp only [List.length_map, ← hj] at hlt
    rw [if_pos h1, if_pos h1, h j hlt]
  · rw [if_neg h1, if_neg h1]

theorem trF_eq : ∀ (f g : ℕ) (s : Tm), s.size ≤ f → s.size ≤ g → trF f s = trF g s
  | 0, _, s, hf, _ => absurd hf (by have := Tm.size_pos s; omega)
  | _ + 1, 0, s, _, hg => absurd hg (by have := Tm.size_pos s; omega)
  | f + 1, g + 1, .node k ch, hf, hg => by
    unfold trF
    split
    · rfl
    · rename_i last hlast
      have hne : ch ≠ [] := by rintro rfl; simp at hlast
      have hlast' : ch.getLast hne = last := by
        rw [List.getLast?_eq_some_getLast hne] at hlast; exact Option.some.inj hlast
      have hmem : ∀ c ∈ ch, trF f c = trF g c := fun c hc =>
        trF_eq f g c (by have := size_le_of_mem (k := k) hc; omega)
          (by have := size_le_of_mem (k := k) hc; omega)
      by_cases hy : last.y = k + 1
      · simp only [hy, ↓reduceIte]
        rw [List.map_congr_left hmem]
        refine epsImg_congr (fun j hj => ?_)
        simp only [List.length_map] at hj
        have := size_lt_of_sublist_dropLast (k := k) hne (take_sublist_dropLast hj)
        exact trF_eq f g _ (by omega) (by omega)
      · simp only [hy, ↓reduceIte]
        have hhi : (Tm.node k (ch.filter (fun c => decide (c.y = k + 1)))).size <
            (Tm.node k ch).size :=
          size_lt_of_sublist_dropLast hne (filter_sublist_dropLast hne _ (by simp [hlast', hy]))
        rw [trF_eq f g (.node k (ch.filter (fun c => decide (c.y = k + 1)))) (by omega)
          (by omega)]
        rw [List.map_congr_left (l := ch.filter (fun c => decide (c.y ≤ k)))
          (fun c hc => by rw [hmem c (List.mem_filter.mp hc).1])]

theorem trF_eq_trTm {f : ℕ} {s : Tm} (h : s.size ≤ f) : trF f s = trTm s :=
  trF_eq f s.size s h le_rfl

/-! ## The equations of `𝒯` -/

theorem trTm_leaf (k : ℕ) : trTm (.node k []) = .th k [] := by
  rw [trTm, Tm.size_node]
  simp [trF]

/-- **The epsilon case**: the last child has `y = k + 1`. -/
theorem trTm_eps {k : ℕ} {ch : List Tm} (hne : ch ≠ []) (hl : (ch.getLast hne).y = k + 1) :
    trTm (.node k ch) = epsImg k (ch.map trTm) (fun j => trTm (.node k (ch.take j))) := by
  rw [trTm, Tm.size_node]
  unfold trF
  rw [List.getLast?_eq_some_getLast hne]
  simp only [hl, ↓reduceIte]
  rw [List.map_congr_left (fun c hc => trF_eq_trTm (by
    have := size_le_of_mem (k := k) hc; simp only [Tm.size_node] at this; omega))]
  refine epsImg_congr (fun j hj => ?_)
  simp only [List.length_map] at hj
  have := size_lt_of_sublist_dropLast (k := k) hne (take_sublist_dropLast hj)
  simp only [Tm.size_node] at this
  exact trF_eq_trTm (by simp only [Tm.size_node]; omega)

/-- The head of `Z` in the non-epsilon case: `𝒯_k((k, hi))`, or `Ω_k`, or nothing. -/
def headPart (k : ℕ) (ch : List Tm) : List (List WP) :=
  if ch.filter (fun c => decide (c.y = k + 1)) ≠ [] then
    [[trTm (.node k (ch.filter (fun c => decide (c.y = k + 1))))]]
  else if 1 ≤ k then [[.th k []]] else []

/-- The exponent `Z` of the non-epsilon case. -/
def zOf (k : ℕ) (ch : List Tm) : List WP :=
  addAll (headPart k ch ++ (ch.filter (fun c => decide (c.y ≤ k))).map (fun c => [trTm c]))

/-- **The non-epsilon case**: the last child does not have `y = k + 1`. -/
theorem trTm_noneps {k : ℕ} {ch : List Tm} (hne : ch ≠ []) (hl : (ch.getLast hne).y ≠ k + 1) :
    trTm (.node k ch) = omegaExp (zOf k ch) k := by
  rw [trTm, Tm.size_node]
  unfold trF
  rw [List.getLast?_eq_some_getLast hne]
  simp only [hl, ↓reduceIte, zOf, headPart]
  have hhi : (Tm.node k (ch.filter (fun c => decide (c.y = k + 1)))).size <
      (Tm.node k ch).size :=
    size_lt_of_sublist_dropLast hne (filter_sublist_dropLast hne _ (by simp [hl]))
  simp only [Tm.size_node] at hhi
  rw [trF_eq_trTm (s := .node k (ch.filter (fun c => decide (c.y = k + 1))))
    (by simp only [Tm.size_node]; omega)]
  have hlo : ∀ c ∈ ch.filter (fun c => decide (c.y ≤ k)), [trF (Tm.sizeList ch) c] = [trTm c] :=
    fun c hc => by
      have h1 := size_le_of_mem (k := k) (List.mem_filter.mp hc).1
      simp only [Tm.size_node] at h1
      rw [trF_eq_trTm (s := c) (by omega)]
  rw [List.map_congr_left hlo]

/-! ## Levels and the least value -/

theorem trTm_lvl (s : Tm) : (trTm s).lvl = s.y := (trTm_nf s).2

theorem trTm_nfp (s : Tm) : NFP (trTm s) := (trTm_nf s).1

theorem val_trTm_leaf (k : ℕ) : (trTm (.node k [])).val = Om k := by
  rw [trTm_leaf, WP.val_th, WP.valS_nil, vartheta_zero]

theorem Om_le_val_trTm (s : Tm) : Om s.y ≤ (trTm s).val := by
  have := (val_level (trTm_nfp s)).1
  rwa [trTm_lvl] at this

theorem val_trTm_lt_Om (s : Tm) : (trTm s).val < Om (s.y + 1) := by
  have := (val_level (trTm_nfp s)).2
  rwa [trTm_lvl] at this

/-- Terms of lower `y` have smaller images. -/
theorem val_trTm_lt_of_y_lt {s t : Tm} (h : s.y < t.y) : (trTm s).val < (trTm t).val :=
  val_lt_of_lvl_lt (trTm_nfp s) (trTm_nfp t) (by rw [trTm_lvl, trTm_lvl]; exact h)

end Googology.Trans.PSS.TR
