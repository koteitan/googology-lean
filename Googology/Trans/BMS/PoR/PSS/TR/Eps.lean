import Googology.Trans.BMS.PoR.PSS.TR.Valid

/-!
# The two cases of `𝒯`, by values

* Non-epsilon (`trTm_noneps`): `𝒯_k(s) = ω^Z`, and `val Z` is the sum of the
  values of its parts (`val_zOf`).
* Epsilon: the parts of `proof/PROOF-2.md` §12.1 as functions of the children
  `H` (`dOf`, `rhoOf`, `jOf`, `deltaOf`, `cOf`, `etaOf`, `epOf`, `insOf`,
  `eta'Of`, `argOf`), and `trTm (k, H) = ϑ_k(argOf k H)` (`trTm_eps'`).
  `argOf k H = Δ ++ η'` with no absorption (`argOf_eq`).
* `minusOnePlus`: `1 + (-1 + x) = x` for `x ≠ 0`.
* The `D + ρ` split is monotone (`split_mono`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## Sums without absorption -/

theorem addS_eq_append {x y : List WP} (hx : NFS x) (hy : NFS y)
    (h : ∀ p ∈ x, ∀ q ∈ y.head?, q.val ≤ p.val) : addS x y = x ++ y := by
  cases y with
  | nil => simp [addS]
  | cons y0 y' =>
    have hdw : x.reverse.dropWhile (fun p => cmpP p y0 == .lt) = x.reverse := by
      cases e : x.reverse with
      | nil => rfl
      | cons a r =>
        have ha : a ∈ x := by rw [← List.mem_reverse, e]; simp
        rw [List.dropWhile_cons_of_neg]
        simp only [beq_iff_eq, cmpP_lt_iff (hx.1 a ha) hy.head, not_lt]
        exact h a ha y0 (by simp)
    rw [addS, hdw, List.reverse_reverse]

theorem addS_append_right {x y z : List WP} (hy : y ≠ []) : addS x (y ++ z) = addS x y ++ z := by
  obtain ⟨y0, y', rfl⟩ := List.exists_cons_of_ne_nil hy
  simp [addS]

theorem addAll_append_single (xs : List (List WP)) (x : List WP) :
    addAll (xs ++ [x]) = addS (addAll xs) x := by
  simp [addAll, List.foldl_append]

/-! ## `-1 + x` -/

theorem one_add_minusOnePlus {x : List WP} (hx : NFS x) (hne : x ≠ []) :
    1 + WP.valS (minusOnePlus x) = WP.valS x := by
  obtain ⟨p, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [minusOnePlus]
  split_ifs with h
  · subst h; rw [WP.valS_cons, val_one]
  · have hp : 1 < p.val := lt_of_le_of_ne (one_le_val hx.head) (fun e =>
      h (eq_of_val_eq nfp_one hx.head (by rw [val_one, e])).symm)
    have hω : ω ≤ p.val := by
      rcases (isPrincipal_add_iff_zero_or_omega0_opow).mp (val_isPrincipal hx.head) with h0 | ⟨b, hb⟩
      · exact absurd h0 (val_pos hx.head).ne'
      · simp only at hb
        rw [← hb]
        have : b ≠ 0 := fun e => by rw [e, opow_zero] at hb; rw [← hb] at hp; exact lt_irrefl _ hp
        calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
          _ ≤ ω ^ b := opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.mpr this)
    rw [WP.valS_cons, ← add_assoc, Ordinal.one_add_of_omega0_le hω]

theorem minusOnePlus_sublist' (x : List WP) : (minusOnePlus x).Sublist x := minusOnePlus_sublist x

theorem minusOnePlus_append {x : List WP} (hx : x ≠ []) (z : List WP) :
    minusOnePlus (x ++ z) = minusOnePlus x ++ z := by
  obtain ⟨p, r, rfl⟩ := List.exists_cons_of_ne_nil hx
  simp only [List.cons_append, minusOnePlus]
  split_ifs <;> rfl

/-! ## The non-epsilon case -/

theorem headPart_spec (k : ℕ) (ch : List Tm) :
    (∀ x ∈ headPart k ch, NFS x ∧ ∀ q ∈ x, q.lvl = k) ∧
      ((headPart k ch).map WP.valS).sum =
        if ch.filter (fun c => decide (c.y = k + 1)) ≠ [] then
          (trTm (.node k (ch.filter (fun c => decide (c.y = k + 1))))).val
        else if 1 ≤ k then Om k else 0 := by
  unfold headPart
  split_ifs with h1 h2
  · refine ⟨fun x hx => ?_, by simp⟩
    rw [List.mem_singleton.mp hx]
    exact ⟨NFS.single (trTm_nfp _), fun q hq => by rw [List.mem_singleton.mp hq, trTm_lvl]; rfl⟩
  · refine ⟨fun x hx => ?_, by simp [vartheta_zero]⟩
    rw [List.mem_singleton.mp hx]
    exact ⟨NFS.single (nfp_th_nil k), fun q hq => by rw [List.mem_singleton.mp hq]; rfl⟩
  · exact ⟨by simp, by simp⟩

/-- The exponent `Z` of the non-epsilon case: a sum of `T¹` of level `≤ k` whose
value is the sum of the values of the parts. -/
theorem zOf_spec (k : ℕ) (ch : List Tm) :
    NFS (zOf k ch) ∧ (∀ q ∈ zOf k ch, q.lvl ≤ k) ∧
      WP.valS (zOf k ch) = ((headPart k ch).map WP.valS).sum +
        ((ch.filter (fun c => decide (c.y ≤ k))).map (fun c => (trTm c).val)).sum := by
  have hparts : ∀ x ∈ headPart k ch ++ (ch.filter (fun c => decide (c.y ≤ k))).map
      (fun c => [trTm c]), NFS x ∧ ∀ q ∈ x, q.lvl ≤ k := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨h1, h2⟩ := (headPart_spec k ch).1 x hx
      exact ⟨h1, fun q hq => le_of_eq (h2 q hq)⟩
    · rw [List.mem_map] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨NFS.single (trTm_nfp c), fun q hq => ?_⟩
      rw [List.mem_singleton.mp hq, trTm_lvl]
      simpa using (List.mem_filter.mp hc).2
  obtain ⟨h1, h2⟩ := addAll_spec (fun x hx => (hparts x hx).1)
  refine ⟨h1, fun q hq => ?_, ?_⟩
  · obtain ⟨x, hx, hqx⟩ := mem_addAll hq
    exact (hparts x hx).2 q hqx
  · rw [zOf, h2, List.map_append, List.sum_append, List.map_map]
    congr 2
    apply List.map_congr_left
    intro c _
    simp

theorem Om_le_valS_zOf {k : ℕ} {ch : List Tm} (hk : 1 ≤ k) : Om k ≤ WP.valS (zOf k ch) := by
  rw [(zOf_spec k ch).2.2, (headPart_spec k ch).2]
  refine le_trans ?_ le_self_add
  split_ifs with h1
  · have := Om_le_val_trTm (.node k (ch.filter (fun c => decide (c.y = k + 1))))
    simpa using this
  · exact le_rfl

/-- **The value in the non-epsilon case**: `val 𝒯_k(s) = ω^{val Z}`. -/
theorem val_trTm_noneps {k : ℕ} {ch : List Tm} (hne : ch ≠ []) (hl : (ch.getLast hne).y ≠ k + 1) :
    (trTm (.node k ch)).val = ω ^ WP.valS (zOf k ch) := by
  rw [trTm_noneps hne hl]
  exact (omegaExp_spec (zOf_spec k ch).1 (zOf_spec k ch).2.1 (fun hk => Om_le_valS_zOf hk)).2.2

/-! ## The epsilon case -/

/-- `D_h + ρ_h = log_ω 𝒯_{k+1}(h)`. -/
def monOf (k : ℕ) (h : Tm) : List WP × List WP := splitLevel (logOmega (trTm h)) (k + 1)

/-- `D_h`: the part of `log_ω 𝒯(h)` of level `≥ k + 1`. -/
def dOf (k : ℕ) (h : Tm) : List WP := (monOf k h).1

/-- `ρ_h`: the rest. -/
def rhoOf (k : ℕ) (h : Tm) : List WP := (monOf k h).2

/-- The start `j` of the final run. -/
def jOf (k : ℕ) (H : List Tm) : ℕ := runStart (H.map (dOf k))

/-- `Δ = D_r`. -/
def deltaOf (k : ℕ) (H : List Tm) : List WP := (H.getLast?.map (dOf k)).getD []

/-- `ω^ρ` at the level of `ρ`. -/
def wOf (k : ℕ) (h : Tm) : WP := omegaExp (rhoOf k h) (expLvl (rhoOf k h))

/-- `c = ω^{ρ_{j+1}} ⊕ ⋯ ⊕ ω^{ρ_r}`. -/
def cOf (k : ℕ) (H : List Tm) : List WP := addAll ((H.drop (jOf k H)).map (fun h => [wOf k h]))

/-- `η = -1 + c`. -/
def etaOf (k : ℕ) (H : List Tm) : List WP := minusOnePlus (cOf k H)

/-- `e_p = 𝒯_k((k, H_1..H_j))`. -/
def epOf (k : ℕ) (H : List Tm) : WP := trTm (.node k (H.take (jOf k H)))

/-- `e_p` is inserted: `j > 0` and `e_p` is above every `ϑ_k`-subterm of `Δ`. -/
def insOf (k : ℕ) (H : List Tm) : Prop :=
  0 < jOf k H ∧ ∀ q ∈ starS k (deltaOf k H), q.val < (epOf k H).val

noncomputable instance (k : ℕ) (H : List Tm) : Decidable (insOf k H) := by
  unfold insOf; infer_instance

/-- `η' = e_p ⊕ η` if `e_p` is inserted, else `η`. -/
noncomputable def eta'Of (k : ℕ) (H : List Tm) : List WP :=
  if insOf k H then addS [epOf k H] (etaOf k H) else etaOf k H

/-- The argument `Δ ⊕ η'`. -/
noncomputable def argOf (k : ℕ) (H : List Tm) : List WP := addS (deltaOf k H) (eta'Of k H)

theorem monOf_spec (k : ℕ) (h : Tm) :
    logOmega (trTm h) = dOf k h ++ rhoOf k h ∧ NFS (dOf k h) ∧ NFS (rhoOf k h) ∧
      (∀ q ∈ dOf k h, k + 1 ≤ q.lvl ∧ q.lvl ≤ h.y) ∧ (∀ q ∈ rhoOf k h, q.lvl ≤ k) := by
  obtain ⟨hl1, -, hl3⟩ := logOmega_spec (trTm_nfp h)
  obtain ⟨h1, h2, h3, h4, h5⟩ := splitLevel_spec hl1 (k + 1)
  refine ⟨h1, h2, h3, fun q hq => ⟨h4 q hq, ?_⟩, fun q hq => Nat.lt_succ_iff.mp (h5 q hq)⟩
  have := hl3 q (by rw [h1]; exact List.mem_append_left _ hq)
  rwa [trTm_lvl] at this

theorem val_log_trTm (h : Tm) : ω ^ WP.valS (logOmega (trTm h)) = (trTm h).val :=
  (logOmega_spec (trTm_nfp h)).2.1

theorem valS_log_eq (k : ℕ) (h : Tm) :
    WP.valS (logOmega (trTm h)) = WP.valS (dOf k h) + WP.valS (rhoOf k h) := by
  rw [(monOf_spec k h).1, valS_append]

theorem wOf_spec (k : ℕ) (h : Tm) :
    NFP (wOf k h) ∧ (wOf k h).lvl = expLvl (rhoOf k h) ∧ (wOf k h).lvl ≤ k ∧
      (wOf k h).val = ω ^ WP.valS (rhoOf k h) := by
  obtain ⟨h1, h2, h3⟩ := omegaExp_expLvl_spec (monOf_spec k h).2.2.1
  exact ⟨h1, h2, h2 ▸ expLvl_le (monOf_spec k h).2.2.2.2, h3⟩

theorem cOf_spec (k : ℕ) (H : List Tm) :
    NFS (cOf k H) ∧ (∀ q ∈ cOf k H, q.lvl ≤ k) ∧
      WP.valS (cOf k H) = ((H.drop (jOf k H)).map (fun h => (wOf k h).val)).sum := by
  have hparts : ∀ x ∈ (H.drop (jOf k H)).map (fun h => [wOf k h]), NFS x ∧ ∀ q ∈ x, q.lvl ≤ k := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨h, -, rfl⟩ := hx
    exact ⟨NFS.single (wOf_spec k h).1, fun q hq => by
      rw [List.mem_singleton.mp hq]; exact (wOf_spec k h).2.2.1⟩
  obtain ⟨h1, h2⟩ := addAll_spec (fun x hx => (hparts x hx).1)
  refine ⟨h1, fun q hq => ?_, ?_⟩
  · obtain ⟨x, hx, hqx⟩ := mem_addAll hq
    exact (hparts x hx).2 q hqx
  · rw [cOf, h2, List.map_map]
    congr 1
    apply List.map_congr_left
    intro h _
    simp

theorem etaOf_spec (k : ℕ) (H : List Tm) :
    NFS (etaOf k H) ∧ ∀ q ∈ etaOf k H, q.lvl ≤ k := by
  obtain ⟨h1, h2, -⟩ := cOf_spec k H
  exact ⟨h1.sublist (minusOnePlus_sublist _),
    fun q hq => h2 q ((minusOnePlus_sublist _).subset hq)⟩

theorem epOf_lvl (k : ℕ) (H : List Tm) : (epOf k H).lvl = k := by
  rw [epOf, trTm_lvl]; rfl

theorem eta'Of_spec (k : ℕ) (H : List Tm) :
    NFS (eta'Of k H) ∧ (∀ q ∈ eta'Of k H, q.lvl ≤ k) := by
  obtain ⟨h1, h2⟩ := etaOf_spec k H
  unfold eta'Of
  split_ifs
  · refine ⟨(addS_spec (NFS.single (trTm_nfp _)) h1).1, fun q hq => ?_⟩
    rcases mem_addS hq with hq | hq
    · rw [List.mem_singleton.mp hq, epOf_lvl]
    · exact h2 q hq
  · exact ⟨h1, h2⟩

theorem val_eta'Of (k : ℕ) (H : List Tm) :
    WP.valS (eta'Of k H) =
      (if insOf k H then (epOf k H).val else 0) + WP.valS (etaOf k H) := by
  unfold eta'Of
  split_ifs
  · rw [(addS_spec (x := [epOf k H]) (NFS.single (trTm_nfp _)) (etaOf_spec k H).1).2,
      valS_single]
  · rw [zero_add]

theorem deltaOf_spec {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    NFS (deltaOf k H) ∧ (∀ q ∈ deltaOf k H, q.lvl = k + 1) ∧ deltaOf k H ≠ [] := by
  have hd : deltaOf k H = dOf k (H.getLast hne) := by
    rw [deltaOf, List.getLast?_eq_some_getLast hne]; rfl
  obtain ⟨-, h2, -, h4, -⟩ := monOf_spec k (H.getLast hne)
  rw [hd]
  refine ⟨h2, fun q hq => le_antisymm (hl ▸ (h4 q hq).2) (h4 q hq).1, ?_⟩
  -- `log 𝒯(H_r)` is at least `Ω_{k+1}`, so it starts with a summand of level `≥ k + 1`
  intro he
  have hv := val_log_trTm (H.getLast hne)
  have hge := Om_le_val_trTm (H.getLast hne)
  rw [hl] at hge
  obtain ⟨-, h2', h3', -, h5'⟩ := monOf_spec k (H.getLast hne)
  rw [valS_log_eq k, he, WP.valS_nil, zero_add] at hv
  have hlt := valS_lt_Om h3' h5'
  have := opow_lt_Om_succ hlt
  rw [hv] at this
  exact absurd hge (not_le.mpr this)

/-- **`argOf = Δ ++ η'`**: the summands of `η'` have level `≤ k`, those of `Δ`
level `k + 1`, so nothing is absorbed. -/
theorem argOf_eq {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    argOf k H = deltaOf k H ++ eta'Of k H := by
  obtain ⟨h1, h2, -⟩ := deltaOf_spec hne hl
  obtain ⟨h3, h4⟩ := eta'Of_spec k H
  refine addS_eq_append h1 h3 (fun p hp q hq => ?_)
  have hq' : q ∈ eta'Of k H := List.mem_of_mem_head? hq
  exact (val_lt_of_lvl_lt (h3.1 q hq') (h1.1 p hp) (by rw [h2 p hp]; have := h4 q hq'; omega)).le

theorem argOf_spec {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    NFS (argOf k H) ∧ (∀ q ∈ argOf k H, q.lvl ≤ k + 1) ∧
      WP.valS (argOf k H) = WP.valS (deltaOf k H) + WP.valS (eta'Of k H) := by
  obtain ⟨h1, h2, -⟩ := deltaOf_spec hne hl
  obtain ⟨h3, h4⟩ := eta'Of_spec k H
  obtain ⟨h5, h6⟩ := addS_spec h1 h3
  refine ⟨h5, fun q hq => ?_, h6⟩
  rcases mem_addS hq with hq | hq
  · exact le_of_eq (h2 q hq)
  · exact Nat.le_succ_of_le (h4 q hq)

/-- **The epsilon case**: `𝒯_k(k, H) = ϑ_k(Δ ⊕ η')`. -/
theorem trTm_eps' {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    trTm (.node k H) = .th k (argOf k H) := by
  rw [trTm_eps hne hl, epsImg]
  have hm : (H.map trTm).map (fun v => splitLevel (logOmega v) (k + 1)) = H.map (monOf k) := by
    rw [List.map_map]; rfl
  have hj : runStart ((H.map (monOf k)).map Prod.fst) = jOf k H := by
    rw [List.map_map]; rfl
  have hΔ : ((H.map (monOf k)).getLast?.map Prod.fst).getD [] = deltaOf k H := by
    rw [List.getLast?_map, Option.map_map]; rfl
  have hc : addAll (((H.map (monOf k)).drop (jOf k H)).map
      (fun m => [omegaExp m.2 (expLvl m.2)])) = cOf k H := by
    rw [← List.map_drop, List.map_map, cOf]; rfl
  dsimp only
  rw [hm, hj, hΔ, hc, argOf]
  congr 1
  unfold eta'Of insOf etaOf epOf
  by_cases h0 : 0 < jOf k H
  · simp only [h0, ↓reduceIte, true_and]
    by_cases hany : ((starS k (deltaOf k H)).any fun q =>
        cmpP (trTm (Tm.node k (List.take (jOf k H) H))) q != Ordering.gt) = true
    · rw [if_pos hany, if_neg]
      intro hall
      obtain ⟨q, hq, hq'⟩ := List.any_eq_true.mp hany
      have hqn := ((starS_spec k _ (deltaOf_spec hne hl).1) q hq).1
      rw [bne_iff_ne, ne_eq, cmpP_eq (trTm_nfp _) hqn, compare_gt_iff_gt, not_lt] at hq'
      exact absurd (hall q hq) (not_lt.mpr hq')
    · rw [if_neg hany, if_pos]
      intro q hq
      have hqn := ((starS_spec k _ (deltaOf_spec hne hl).1) q hq).1
      by_contra hc'
      apply hany
      refine List.any_eq_true.mpr ⟨q, hq, ?_⟩
      rw [bne_iff_ne, ne_eq, cmpP_eq (trTm_nfp _) hqn, compare_gt_iff_gt]
      exact hc'
  · simp only [h0, ↓reduceIte, false_and]

theorem val_trTm_eps {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    (trTm (.node k H)).val = vartheta k (WP.valS (argOf k H)) := by
  rw [trTm_eps' hne hl, WP.val_th]

/-- In the epsilon case the image is an epsilon number above `Ω_k` (E). -/
theorem trTm_eps_isEps {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    Om k < (trTm (.node k H)).val ∧ ω ^ (trTm (.node k H)).val = (trTm (.node k H)).val := by
  have hn := trTm_nfp (.node k H)
  rw [trTm_eps' hne hl] at hn ⊢
  refine (eps_iff hn).mp ?_
  rw [argOf_eq hne hl]
  obtain ⟨-, h2, h3⟩ := deltaOf_spec hne hl
  obtain ⟨q, r, hqr⟩ := List.exists_cons_of_ne_nil h3
  exact ⟨q, by rw [hqr]; simp, by rw [h2 q (by rw [hqr]; simp)]⟩

/-! ## The split `D + ρ` is monotone -/

/-- A sum of terms of level `≥ m` that is below another is below it by at least
`Ω_m`. -/
theorem gap_of_lt {m : ℕ} :
    ∀ {D D' : List WP}, NFS D → NFS D' → (∀ q ∈ D, m ≤ q.lvl) → (∀ q ∈ D', m ≤ q.lvl) →
      WP.valS D' < WP.valS D → WP.valS D' + Om m ≤ WP.valS D
  | [], _, _, _, _, _, h => absurd h (by simp)
  | p :: D, [], hD, _, hl, _, _ => by
    rw [WP.valS_nil, zero_add]
    exact le_trans (Om_le_val_of_le_lvl hD.head (hl p (by simp))) le_valS_head
  | p :: D, p' :: D', hD, hD', hl, hl', h => by
    rcases lt_trichotomy p'.val p.val with hlt | heq | hgt
    · have h1 : WP.valS (p' :: D') < p.val := valS_lt_of_head_lt hD' hD.head hlt
      have h2 : Om m ≤ p.val := Om_le_val_of_le_lvl hD.head (hl p (by simp))
      rcases h2.lt_or_eq with h2 | h2
      · exact le_trans (val_isPrincipal hD.head h1 h2).le le_valS_head
      · -- `p = Ω_m` would make `p' < Ω_m`, below level `m`
        exfalso
        have := Om_le_val_of_le_lvl hD'.head (hl' p' (by simp))
        rw [h2] at this
        exact absurd hlt (not_lt.mpr this)
    · have hpp := eq_of_val_eq hD'.head hD.head heq
      subst hpp
      rw [WP.valS_cons, WP.valS_cons] at h ⊢
      rw [add_assoc]
      exact (add_le_add_iff_left _).mpr (gap_of_lt hD.of_cons hD'.of_cons
        (fun q hq => hl q (by simp [hq])) (fun q hq => hl' q (by simp [hq]))
        ((add_lt_add_iff_left _).mp h))
    · exact absurd h (not_lt.mpr (le_trans (valS_lt_of_head_lt hD hD'.head hgt).le le_valS_head))

/-- **The split is monotone**: if `D + ρ ≤ D' + ρ'` (with `D, D'` of level
`≥ m` and `ρ, ρ'` below `Ω_m`), then `D ≤ D'`, and `ρ ≤ ρ'` when `D = D'`. -/
theorem split_mono {m : ℕ} {D ρ D' ρ' : List WP} (hD : NFS D) (hD' : NFS D')
    (hl : ∀ q ∈ D, m ≤ q.lvl) (hl' : ∀ q ∈ D', m ≤ q.lvl)
    (hρ' : WP.valS ρ' < Om m) (h : WP.valS D + WP.valS ρ ≤ WP.valS D' + WP.valS ρ') :
    WP.valS D ≤ WP.valS D' ∧ (WP.valS D = WP.valS D' → WP.valS ρ ≤ WP.valS ρ') := by
  refine ⟨?_, fun e => by rw [e] at h; exact (add_le_add_iff_left _).mp h⟩
  by_contra hc
  rw [not_le] at hc
  have := gap_of_lt hD hD' hl hl' hc
  have h2 : WP.valS D' + WP.valS ρ' < WP.valS D' + Om m := (add_lt_add_iff_left _).mpr hρ'
  exact absurd h (not_le.mpr (lt_of_lt_of_le h2 (le_trans this le_self_add)))

theorem valS_rho_lt (k : ℕ) (h : Tm) : WP.valS (rhoOf k h) < Om (k + 1) :=
  valS_lt_Om (monOf_spec k h).2.2.1 (monOf_spec k h).2.2.2.2

/-- The logs of `𝒯(h) ≤ 𝒯(h')` compare as `D`, then `ρ`. -/
theorem d_rho_mono {k : ℕ} {h h' : Tm}
    (hle : (trTm h).val ≤ (trTm h').val) :
    WP.valS (dOf k h) ≤ WP.valS (dOf k h') ∧
      (WP.valS (dOf k h) = WP.valS (dOf k h') → WP.valS (rhoOf k h) ≤ WP.valS (rhoOf k h')) := by
  have hX : WP.valS (logOmega (trTm h)) ≤ WP.valS (logOmega (trTm h')) := by
    rw [← val_log_trTm h, ← val_log_trTm h'] at hle
    exact (opow_le_opow_iff_right one_lt_omega0).mp hle
  rw [valS_log_eq k, valS_log_eq k] at hX
  obtain ⟨-, a1, -, a3, -⟩ := monOf_spec k h
  obtain ⟨-, b1, -, b3, -⟩ := monOf_spec k h'
  exact split_mono a1 b1 (fun q hq => (a3 q hq).1) (fun q hq => (b3 q hq).1)
    (valS_rho_lt k h') hX

end Googology.Trans.PSS.TR
