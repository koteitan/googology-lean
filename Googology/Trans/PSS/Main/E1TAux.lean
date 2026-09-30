import Googology.Trans.PSS.Main.CI
import Googology.Trans.PSS.Main.BarEps

/-!
# Tools for `E1_T`: sums of values of `J`

* `valS_jS_append`, `valS_jS_level0`: `val J(x)` is additive, and `J` is the identity on
  sums of level `0`.
* `valS_jS_addAll`: for a list `L` of principal terms on which `q ↦ val J(q)` is strictly
  monotone with additive principal values, `val J(addAll L) = Σ_{q ∈ L} val J(q)`: the
  absorption in `addAll` is matched by the absorption of the ordinal sum.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

theorem jS_append (a : WP) (x y : List WP) : jS a (x ++ y) = jS a x ++ jS a y := by
  simp [jS, jL_eq_map, List.flatten_append]

theorem valS_jS_append (a : WP) (x y : List WP) :
    WP.valS (jS a (x ++ y)) = WP.valS (jS a x) + WP.valS (jS a y) := by
  rw [jS_append, valS_append]

@[simp] theorem jS_nil (a : WP) : jS a [] = [] := by simp [jS]

theorem valS_jS_cons (a q : WP) (x : List WP) :
    WP.valS (jS a (q :: x)) = WP.valS (jP a q) + WP.valS (jS a x) := by
  rw [show q :: x = [q] ++ x from rfl, valS_jS_append]
  simp [jS]

theorem valS_jS_eq_sum (a : WP) : ∀ x : List WP,
    WP.valS (jS a x) = (x.map fun q => WP.valS (jP a q)).sum
  | [] => by simp
  | q :: x => by rw [valS_jS_cons, valS_jS_eq_sum a x]; simp

theorem jP_lvl0 (a : WP) {q : WP} (h : q.lvl = 0) : jP a q = [q] := by
  obtain ⟨m, b⟩ := q
  simp only [WP.lvl_th] at h; subst h
  exact jP_zero a b

theorem valS_jS_level0 (a : WP) : ∀ {x : List WP}, (∀ q ∈ x, q.lvl = 0) →
    WP.valS (jS a x) = WP.valS x
  | [], _ => by simp
  | q :: x, h => by
    rw [valS_jS_cons, jP_lvl0 a (h q (by simp)), valS_single,
      valS_jS_level0 a (fun r hr => h r (by simp [hr])), WP.valS_cons]

/-- A sum of ordinals each below an additive principal `θ` is below `θ`. -/
theorem sum_lt_pr {θ : Ordinal.{0}} (hθ : Pr θ) : ∀ l : List Ordinal.{0}, (∀ x ∈ l, x < θ) →
    l.sum < θ
  | [], _ => by simpa using hθ.pos
  | x :: l, h => by
    rw [List.sum_cons]
    exact hθ.add_lt (h x (by simp)) (sum_lt_pr hθ l (fun y hy => h y (by simp [hy])))

/-- **The absorption of `addAll` is the absorption of the ordinal sum**, for `J`. -/
theorem valS_jS_addAll (a : WP) : ∀ {L : List WP}, (∀ q ∈ L, NFP q) →
    (∀ q ∈ L, ∀ ℓ ∈ L, q.val < ℓ.val → WP.valS (jP a q) < WP.valS (jP a ℓ)) →
    (∀ ℓ ∈ L, Pr (WP.valS (jP a ℓ))) →
    WP.valS (jS a (TR.addAll (L.map fun q => [q]))) = (L.map fun q => WP.valS (jP a q)).sum := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro _ _ _; simp [TR.addAll]
  | append_singleton L ℓ ih =>
    intro hn hm hp
    have hn' : ∀ q ∈ L, NFP q := fun q hq => hn q (by simp [hq])
    have hm' : ∀ q ∈ L, ∀ ℓ' ∈ L, q.val < ℓ'.val → WP.valS (jP a q) < WP.valS (jP a ℓ') :=
      fun q hq ℓ' hℓ' => hm q (by simp [hq]) ℓ' (by simp [hℓ'])
    have hp' : ∀ ℓ' ∈ L, Pr (WP.valS (jP a ℓ')) := fun ℓ' hℓ' => hp ℓ' (by simp [hℓ'])
    have ihL := ih hn' hm' hp'
    set x := TR.addAll (L.map fun q => [q]) with hx
    have hxL : ∀ d ∈ x, d ∈ L := by
      intro d hd
      obtain ⟨y, hy, hdy⟩ := mem_addAll hd
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_singleton.mp hdy]; exact hq
    have hℓn : NFP ℓ := hn ℓ (by simp)
    have hℓp : Pr (WP.valS (jP a ℓ)) := hp ℓ (by simp)
    rw [List.map_append, List.map_singleton, addAll_append_single]
    set P : WP → Bool := fun p => cmpP p ℓ == .lt with hP
    have hsplit : x = (x.reverse.dropWhile P).reverse ++ (x.reverse.takeWhile P).reverse := by
      rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
    have hadd : addS x [ℓ] = (x.reverse.dropWhile P).reverse ++ [ℓ] := rfl
    rw [hadd, valS_jS_append, List.map_append, List.sum_append, ← ihL]
    conv_rhs => rw [hsplit, valS_jS_append]
    rw [add_assoc]
    congr 1
    have hdrop : WP.valS (jS a (x.reverse.takeWhile P).reverse) < WP.valS (jP a ℓ) := by
      rw [valS_jS_eq_sum]
      apply sum_lt_pr hℓp
      intro v hv
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      have hd' : d ∈ x.reverse.takeWhile P := List.mem_reverse.mp hd
      have hdP := List.mem_takeWhile_imp hd'
      have hdx : d ∈ x := List.mem_reverse.mp ((List.takeWhile_sublist _).subset hd')
      have hdL := hxL d hdx
      simp only [hP, beq_iff_eq] at hdP
      rw [cmpP_lt_iff (hn d (by simp [hdL])) hℓn] at hdP
      exact hm d (by simp [hdL]) ℓ (by simp) hdP
    simp only [List.map_singleton, List.sum_singleton]
    rw [valS_jS_cons, jS_nil, WP.valS_nil, add_zero, hℓp.add_eq hdrop]

/-! ## `ζ_α = ρ_W` -/

theorem isEps_node0 {L : List Tm} (hL : L ≠ []) (h : ∀ c ∈ L, c.y = 1) :
    isEps (.node 0 L) = true := by
  simp [isEps, List.getLast?_eq_some_getLast hL, h _ (List.getLast_mem hL)]

theorem getLast?_minusOnePlus {x : List WP} (h : minusOnePlus x ≠ []) :
    (minusOnePlus x).getLast? = x.getLast? := by
  cases x with
  | nil => simp [minusOnePlus] at h
  | cons p r =>
    simp only [minusOnePlus] at h ⊢
    by_cases hp : p = TR.one
    · rw [if_pos hp] at h ⊢
      obtain ⟨q, r', rfl⟩ := List.exists_cons_of_ne_nil h
      simp [List.getLast?_cons_cons]
    · rw [if_neg hp]

theorem dvd_valS_of_ge {γ : Ordinal.{0}} : ∀ {x : List WP}, (∀ e ∈ x, NFP e) →
    (∀ e ∈ x, ω ^ γ ≤ e.val) → ω ^ γ ∣ WP.valS x
  | [], _, _ => by simp
  | e :: x, hn, hge => by
    rw [WP.valS_cons]
    refine opow_dvd_add ?_ (dvd_valS_of_ge (fun e' he' => hn e' (by simp [he']))
      (fun e' he' => hge e' (by simp [he'])))
    obtain ⟨y, hy⟩ := pr_iff.mp (pr_val (hn e (by simp)))
    have h1 := hge e (by simp)
    rw [hy] at h1 ⊢
    exact opow_dvd_opow ω ((opow_le_opow_iff_right one_lt_omega0).mp h1)

/-- **`ζ_α = ρ_W`** (`proof/PROOF-2.md` §12.5, with NS). -/
theorem zeta_eq_rho {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true)
    (hne : H ≠ []) : zetaT (trTm (.node 0 H)) = WP.valS (rhoOf 0 (H.getLast hne)) := by
  obtain ⟨-, hall, hT⟩ := trTm_root_eps hN he
  have hl : (H.getLast hne).y = 0 + 1 := hall _ (List.getLast_mem hne)
  rw [zetaT, hT, WP.arg_th, (argD_eps hne hl).1, (argD_eps hne hl).2]
  set w := wOf 0 (H.getLast hne) with hw
  have hwv : w.val = ω ^ WP.valS (rhoOf 0 (H.getLast hne)) := (wOf_spec 0 _).2.2.2
  have hc := cOf_getLast hne
  have hρ0 : w = TR.one → WP.valS (rhoOf 0 (H.getLast hne)) = 0 := by
    intro h1
    rw [h1, val_one] at hwv
    exact opow_inj (by rw [← hwv, opow_zero])
  by_cases hη : etaOf 0 H = []
  · have hc1 : cOf 0 H = [TR.one] := eq_one_of_minusOnePlus_nil (cOf_ne_nil hne) hη
    rw [hc1] at hc
    have hw1 : w = TR.one := by simp at hc; exact hc.symm
    rw [hρ0 hw1]
    rw [if_neg]
    rintro ⟨hne', hns⟩
    apply hns
    unfold eta'Of at hne' ⊢
    split_ifs at hne' ⊢ with hins
    · rw [hη]
      refine ⟨epOf 0 H, rfl, epOf_lvl 0 H, ?_, hins.2⟩
      have hj := hins.1
      have htne : H.take (jOf 0 H) ≠ [] := by
        intro h; rcases List.take_eq_nil_iff.mp h with h | h
        · omega
        · exact hne h
      have hts : Std (.node 0 (H.take (jOf 0 H))) := std_take hN _
      have hall' : ∀ c ∈ H.take (jOf 0 H), c.y = 1 :=
        fun c hc' => hall c (List.mem_of_mem_take hc')
      have hte := isEps_node0 htne hall'
      obtain ⟨-, -, hT'⟩ := trTm_root_eps hts hte
      have hl' : ((H.take (jOf 0 H)).getLast htne).y = 0 + 1 := hall' _ (List.getLast_mem htne)
      rw [epOf, hT', WP.arg_th, (argD_eps htne hl').1]
      exact level_prefix_gt hN hne hj
    · exact absurd hη hne'
  · have hηl : (etaOf 0 H).getLast? = some w := by
      unfold etaOf at hη ⊢; rw [getLast?_minusOnePlus hη, hc]
    have hη'l : (eta'Of 0 H).getLast? = some w := by
      unfold eta'Of
      split_ifs
      · obtain ⟨y0, y', hy⟩ := List.exists_cons_of_ne_nil hη
        rw [hy] at hηl ⊢
        simp only [addS]
        rw [List.getLast?_append_of_ne_nil _ (by simp)]
        exact hηl
      · exact hηl
    have hη'ne : eta'Of 0 H ≠ [] := by intro h; rw [h] at hη'l; simp at hη'l
    by_cases hsup : supPt (deltaOf 0 H) (eta'Of 0 H)
    · rw [if_neg (fun h => h.2 hsup), hρ0 (lemmaNS hN he hne hsup)]
    · rw [if_pos ⟨hη'ne, hsup⟩]
      have hsplit : eta'Of 0 H = (eta'Of 0 H).dropLast ++ [w] := by
        conv_lhs => rw [← List.dropLast_append_getLast? w hη'l]
      have hnf := (eta'Of_spec 0 H).1
      rw [hsplit] at hnf
      rw [hsplit, valS_append, valS_single, hwv]
      apply logend_add_opow
      apply dvd_valS_of_ge (fun e he' => hnf.1 e (by simp [he']))
      intro e he'
      rw [← hwv]
      exact (List.pairwise_append.mp hnf.2).2.2 e he' w (by simp)

end Googology.Trans.PSS.Main
