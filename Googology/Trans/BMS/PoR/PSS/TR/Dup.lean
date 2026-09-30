import Googology.Trans.BMS.PoR.PSS.TR.BaseC1

/-!
# The base `(B dup)`: the case `i₁ = 0`

`proof/TR-2.md` §4b.3, (Bdup).  `j₀ = (y_j, cs ++ [(0, ())])` has the leaf `ℓ`
of `y = 0` as its last child, `j₀⁻ = (y_j, cs)`, and `M[n]` has `n` copies of
`j₀⁻` in place of `j₀`.

* `val_trTm_dup`: `𝒯(j₀) = 𝒯(j₀⁻)·ω` (Exp).
* `val_trTm_rep`: with `r` copies of `x` as the last children,
  `𝒯 = ω^{W + 𝒯(x)·r}`.
* `prefix_split_gen`: the prefix split below `K + δ` for `δ` below every
  principal term above `w` (e.g. `δ = w·ω`).
* `mu_eventually`: the ordinal step of the epsilon case.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## Values -/

theorem zPre_eq_zOf (k : ℕ) (cs : List Tm) : zPre k cs = zOf k cs := rfl

/-- The value of a valid term is `ω^{val W}` with `W = zPre`. -/
theorem val_trTm_eq_opow_zPre {k : ℕ} {cs : List Tm} (hv : Valid (.node k cs)) :
    (trTm (.node k cs)).val = ω ^ WP.valS (zPre k cs) := by
  rcases eq_or_ne cs [] with rfl | hne
  · rw [val_trTm_leaf]
    cases k with
    | zero => simp [zPre, headPart, addAll, Om_zero]
    | succ k' =>
      have : zPre (k' + 1) [] = [.th (k' + 1) []] := by simp [zPre, headPart, addAll, addS]
      rw [this, valS_single, WP.val_th, WP.valS_nil, vartheta_zero, opow_Om_succ]
  by_cases hl : (cs.getLast hne).y = k + 1
  · -- epsilon: `W = [𝒯]`
    have hall := hv.eps_all hne hl
    have hf1 : cs.filter (fun c => decide (c.y = k + 1)) = cs := by
      rw [List.filter_eq_self]; intro c hc; simpa using hall c hc
    have hf2 : cs.filter (fun c => decide (c.y ≤ k)) = [] := by
      rw [List.filter_eq_nil_iff]; intro c hc; simp [hall c hc]
    have hW : zPre k cs = [trTm (.node k cs)] := by
      rw [zPre, headPart, hf1, if_pos hne, hf2]
      simp [addAll, addS]
    rw [hW, valS_single, (trTm_eps_isEps hne hl).2]
  · rw [val_trTm_noneps hne hl, zPre_eq_zOf]

/-- **`𝒯(j₀) = 𝒯(j₀⁻)·ω`.** -/
theorem val_trTm_dup {k : ℕ} {cs : List Tm} (hv : Valid (.node k (cs ++ [.node 0 []]))) :
    (trTm (.node k (cs ++ [.node 0 []]))).val = (trTm (.node k cs)).val * ω := by
  have hv' : Valid (.node k cs) := by
    have := hv.take cs.length; rwa [List.take_left] at this
  rw [val_trTm_append_lo (Nat.zero_le k), val_trTm_leaf, Om_zero, val_trTm_eq_opow_zPre hv',
    opow_add, opow_one]

theorem sum_replicate_ord (r : ℕ) (v : Ordinal.{0}) : (List.replicate r v).sum = v * r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.sum_cons, ih]
    push_cast
    rw [show ((r : Ordinal) + 1) = 1 + r by
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm], mul_add, mul_one]

/-- With `r` copies of `x` (level `≤ k`) as the last children:
`𝒯 = ω^{W + 𝒯(x)·r}`. -/
theorem val_trTm_rep {k : ℕ} {cs : List Tm} {x : Tm} (hx : x.y ≤ k) {r : ℕ} (hr : 0 < r) :
    (trTm (.node k (cs ++ List.replicate r x))).val =
      ω ^ (WP.valS (zPre k cs) + (trTm x).val * r) := by
  have hne : cs ++ List.replicate r x ≠ [] := by
    intro e; rw [List.append_eq_nil_iff, List.replicate_eq_nil_iff] at e; omega
  have hlast : (cs ++ List.replicate r x).getLast hne = x := by
    rw [List.getLast_append_of_ne_nil _ (by simp; omega)]
    exact List.getLast_replicate _
  rw [val_trTm_noneps hne (by rw [hlast]; omega), (zOf_spec k _).2.2]
  have hf1 : (List.replicate r x).filter (fun c => decide (c.y = k + 1)) = [] :=
    List.filter_eq_nil_iff.mpr (fun c hc => by rw [List.eq_of_mem_replicate hc]; simp; omega)
  have hf2 : (List.replicate r x).filter (fun c => decide (c.y ≤ k)) = List.replicate r x :=
    List.filter_eq_self.mpr (fun c hc => by rw [List.eq_of_mem_replicate hc]; simpa using hx)
  have hhp : headPart k (cs ++ List.replicate r x) = headPart k cs := by
    unfold headPart; rw [List.filter_append, hf1, List.append_nil]
  have hlo : (cs ++ List.replicate r x).filter (fun c => decide (c.y ≤ k)) =
      cs.filter (fun c => decide (c.y ≤ k)) ++ List.replicate r x := by
    rw [List.filter_append, hf2]
  have hzp : WP.valS (zPre k cs) = ((headPart k cs).map WP.valS).sum +
      ((cs.filter (fun c => decide (c.y ≤ k))).map (fun c => (trTm c).val)).sum := by
    rw [zPre, (addAll_spec (fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact ((headPart_spec k cs).1 y hy).1
      · rw [List.mem_map] at hy
        obtain ⟨c, -, rfl⟩ := hy
        exact NFS.single (trTm_nfp c))).2, List.map_append, List.sum_append, List.map_map]
    congr 2
    apply List.map_congr_left
    intro c _
    simp
  rw [hhp, hlo, List.map_append, List.sum_append, List.map_replicate, sum_replicate_ord,
    ← add_assoc, hzp]

/-! ## The prefix split below `K + δ` -/

/-- The prefix split with a bound `δ` that is below every principal term above the
summands' lower bound `w`. -/
theorem prefix_split_gen {w : WP} {δ : Ordinal.{0}}
    (hδ : ∀ x : WP, NFP x → w.val < x.val → δ ≤ x.val) :
    ∀ {K ξ : List WP}, NFS K → NFS ξ → (∀ p ∈ K, w.val ≤ p.val) → WP.valS K ≤ WP.valS ξ →
      WP.valS ξ < WP.valS K + δ → ∃ ξ', ξ = K ++ ξ' ∧ NFS ξ' ∧ WP.valS ξ' < δ
  | [], ξ, _, hξ, _, _, h2 => ⟨ξ, rfl, hξ, by simpa using h2⟩
  | k0 :: K, [], hK, _, _, h1, _ => by
    exfalso
    simp only [WP.valS_nil] at h1
    exact absurd (valS_pos (l := K) hK.head) (not_lt.mpr h1)
  | k0 :: K, x0 :: ξ, hK, hξ, hKw, h1, h2 => by
    rcases lt_trichotomy x0.val k0.val with hlt | heq | hgt
    · exact absurd h1 (not_le.mpr (lt_of_lt_of_le (valS_lt_of_head_lt hξ hK.head hlt)
        le_valS_head))
    · have hx := eq_of_val_eq hξ.head hK.head heq
      subst hx
      rw [WP.valS_cons, WP.valS_cons] at h1 h2
      rw [add_assoc] at h2
      obtain ⟨ξ', rfl, h3, h4⟩ := prefix_split_gen hδ hK.of_cons hξ.of_cons
        (fun p hp => hKw p (by simp [hp])) ((add_le_add_iff_left _).mp h1)
        ((add_lt_add_iff_left _).mp h2)
      exact ⟨ξ', rfl, h3, h4⟩
    · exfalso
      have hp := val_isPrincipal hξ.head
      have hKs : WP.valS (k0 :: K) < x0.val :=
        valS_lt_of_head_lt hK hξ.head hgt
      have hδx : δ ≤ x0.val := hδ x0 hξ.head (lt_of_le_of_lt (hKw k0 (by simp)) hgt)
      have : WP.valS (k0 :: K) + δ ≤ x0.val := by
        rcases hδx.lt_or_eq with h | h
        · exact (hp hKs h).le
        · rw [h]; exact (hp.add_eq_right hKs).le
      exact absurd h2 (not_lt.mpr (le_trans this le_valS_head))

theorem lt_mul_omega0' {a v : Ordinal.{0}} (h : a < v * ω) : ∃ n : ℕ, a < v * n := by
  obtain ⟨c, hc, h'⟩ := (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h
  obtain ⟨n, rfl⟩ := lt_omega0.1 hc
  exact ⟨n, h'⟩

theorem mul_omega0_le_of_principal {v x : Ordinal.{0}} (hx : IsPrincipal (· + ·) x) (hvx : v < x) :
    v * ω ≤ x := by
  refine le_of_forall_lt fun b hb => ?_
  obtain ⟨n, hn⟩ := lt_mul_omega0' hb
  exact lt_trans hn (hx.mul_natCast_lt hvx n)

/-! ## The ordinal step of the epsilon case -/

theorem one_add_le_add_one (a : Ordinal.{0}) : 1 + a ≤ a + 1 := by
  rcases lt_or_ge a ω with h | h
  · obtain ⟨n, rfl⟩ := lt_omega0.mp h
    rw [show (1 : Ordinal) + n = n + 1 by norm_cast; omega]
  · rw [Ordinal.one_add_of_omega0_le h]; exact le_self_add

/-- If `1 + μ = C + ω^{ρ+1}`, `1 + μ_n = C + ω^ρ·(n+2)` and `σ < e + μ`, then
`σ < e + μ_n` for all large `n`. -/
theorem mu_eventually {C ρ e σ μ : Ordinal.{0}} {μn : ℕ → Ordinal.{0}}
    (hμ : 1 + μ = C + ω ^ (ρ + 1)) (hμn : ∀ n, 1 + μn n = C + ω ^ ρ * ((n : Ordinal) + 2))
    (hσ : σ < e + μ) : ∃ N, ∀ n ≥ N, σ < e + μn n := by
  -- `a < μ_n` whenever `a + 1 + 1 ≤ 1 + μ_n`
  have hge : ∀ (n : ℕ) (a : Ordinal.{0}), a + 1 + 1 ≤ C + ω ^ ρ * ((n : Ordinal) + 2) → a < μn n := by
    intro n a h
    by_contra hc
    rw [not_lt] at hc
    have h1 : 1 + μn n ≤ 1 + a := (add_le_add_iff_left 1).mpr hc
    have h2 := lt_of_le_of_lt (le_trans h1 (one_add_le_add_one a)) (Order.lt_add_one_iff.mpr le_rfl)
    rw [hμn n] at h2
    exact absurd h (not_le.mpr h2)
  have hω : ω ≤ C + ω ^ (ρ + 1) := le_trans (by
    calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
      _ ≤ ω ^ (ρ + 1) := opow_le_opow_right omega0_pos le_add_self) le_add_self
  have hμω : ω ≤ μ := by
    by_contra h
    rw [not_le] at h
    have : 1 + μ < ω := isPrincipal_add_omega0 one_lt_omega0 h
    rw [hμ] at this
    exact absurd hω (not_le.mpr this)
  have hμ' : μ = C + ω ^ (ρ + 1) := by rw [← hμ, Ordinal.one_add_of_omega0_le hμω]
  have hpos : 1 ≤ ω ^ ρ := Order.one_le_iff_ne_zero.mpr (Ordinal.opow_pos _ omega0_pos).ne'
  rcases lt_or_ge σ e with hσe | hσe
  · exact ⟨0, fun n _ => lt_of_lt_of_le hσe le_self_add⟩
  obtain ⟨σ1, rfl⟩ : ∃ σ1, σ = e + σ1 := ⟨σ - e, (Ordinal.add_sub_cancel_of_le hσe).symm⟩
  rw [add_lt_add_iff_left, hμ'] at hσ
  suffices H : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → σ1 + 1 + 1 ≤ C + ω ^ ρ * ((n : Ordinal) + 2) by
    obtain ⟨N, hN⟩ := H
    exact ⟨N, fun n hn => (add_lt_add_iff_left e).mpr (hge n σ1 (hN n hn))⟩
  have hm : ∀ n : ℕ, ω ^ ρ ≤ ω ^ ρ * ((n : Ordinal) + 2) := fun n =>
    le_mul_of_one_le_right' (by
      calc (1 : Ordinal) ≤ 2 := by norm_num
        _ ≤ (n : Ordinal) + 2 := le_add_self)
  rcases lt_or_ge σ1 C with hσC | hσC
  · refine ⟨0, fun n _ => ?_⟩
    calc σ1 + 1 + 1 ≤ C + 1 := add_le_add_left (Order.add_one_le_of_lt hσC) 1
      _ ≤ C + ω ^ ρ * ((n : Ordinal) + 2) :=
          (add_le_add_iff_left C).mpr (le_trans hpos (hm n))
  obtain ⟨a2, rfl⟩ : ∃ a2, σ1 = C + a2 := ⟨σ1 - C, (Ordinal.add_sub_cancel_of_le hσC).symm⟩
  rw [add_lt_add_iff_left, opow_add, opow_one] at hσ
  obtain ⟨N, hN⟩ := lt_mul_omega0' hσ
  refine ⟨N, fun n hn => ?_⟩
  rw [add_assoc, add_assoc]
  refine (add_le_add_iff_left C).mpr ?_
  calc a2 + (1 + 1) = (a2 + 1) + 1 := (add_assoc _ _ _).symm
    _ ≤ ω ^ ρ * N + 1 := add_le_add_left (Order.add_one_le_of_lt hN) 1
    _ ≤ ω ^ ρ * N + ω ^ ρ := (add_le_add_iff_left _).mpr hpos
    _ = ω ^ ρ * ((N : Ordinal) + 1) := by rw [mul_add, mul_one]
    _ ≤ ω ^ ρ * ((n : Ordinal) + 2) := by
        refine mul_le_mul_right ?_ _
        have : ((N : ℕ) : Ordinal) + 1 = ((N + 1 : ℕ) : Ordinal) := by push_cast; rfl
        have h2 : ((n : ℕ) : Ordinal) + 2 = ((n + 2 : ℕ) : Ordinal) := by push_cast; rfl
        rw [this, h2]
        exact_mod_cast (by omega : N + 1 ≤ n + 2)

/-! ## (B dup), the parent not epsilon -/

theorem mul_omega0_eq_add (v : Ordinal.{0}) : v * ω = v + v * ω := by
  conv_lhs => rw [← Ordinal.one_add_omega0, mul_add, mul_one]

/-- **(B dup)** for a parent `p` that is not epsilon: `p = (k, cs ++ [j₀])` and
`p⟨n⟩ = (k, cs ++ (j₀⁻)^{n+2})`. -/
theorem bdup_lo {k yj : ℕ} {csp csj : List Tm} (hyj : yj ≤ k)
    (hvj : Valid (.node yj (csj ++ [.node 0 []]))) :
    LC 0 (fun _ => True) (.node k (csp ++ [.node yj (csj ++ [.node 0 []])]))
      (fun n => .node k (csp ++ List.replicate (n + 2) (.node yj csj))) := by
  intro γ hγ hγlt hB
  set W := zPre k csp
  have hWn : NFS W := zPre_nfs k csp
  set v := (trTm (.node yj csj)).val
  have hval : (trTm (.node k (csp ++ [.node yj (csj ++ [.node 0 []])]))).val = ω ^ (WP.valS W + v * ω) := by
    rw [val_trTm_append_lo (show (Tm.node yj _).y ≤ k from hyj), val_trTm_dup hvj]
  have hvaln : ∀ n, (trTm (.node k (csp ++ List.replicate (n + 2) (.node yj csj)))).val =
      ω ^ (WP.valS W + v * ((n + 2 : ℕ) : Ordinal)) := fun n =>
    val_trTm_rep (x := .node yj csj) hyj (by omega)
  rw [hval] at hγlt
  cases γ with
  | nil => exact ⟨0, fun n _ => by simpa using val_pos (trTm_nfp _)⟩
  | cons g γ' =>
    have hg := hγ.head
    by_cases hgl : g.lvl < k
    · refine ⟨0, fun n _ => ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine lt_of_lt_of_le (valS_lt_Om hγ (hγ.lvl_le_of_head (m := k') (by omega))) ?_
      exact Om_le_val_trTm (.node (k' + 1) _)
    obtain ⟨hξn, hξv, -⟩ := logOmega_spec hg
    set ξ := logOmega g
    have hξlt : WP.valS ξ < WP.valS W + v * ω := by
      refine (opow_lt_opow_iff_right one_lt_omega0).mp ?_
      rw [hξv]
      exact lt_of_le_of_lt le_valS_head hγlt
    suffices H : ∃ n0, ∀ n ≥ n0, WP.valS ξ + 1 ≤ WP.valS W + v * ((n + 2 : ℕ) : Ordinal) by
      obtain ⟨n0, hn0⟩ := H
      refine ⟨n0, fun n hn => ?_⟩
      rw [hvaln n]
      exact lt_of_lt_of_le (valS_lt_opow_succ hγ hξv.symm)
        ((opow_le_opow_iff_right one_lt_omega0).mpr (hn0 n hn))
    by_cases hξW : WP.valS ξ < WP.valS W
    · exact ⟨0, fun n _ => le_trans (Order.add_one_le_of_lt hξW) le_self_add⟩
    obtain ⟨K, hKW, hKn, hKv, hKeq⟩ := absorb_prefix hWn (trTm_nfp (.node yj csj))
    have hKeq' : WP.valS K + v * ω = WP.valS W + v * ω := by
      rw [mul_omega0_eq_add v, ← add_assoc, ← add_assoc, hKeq]
    have h1 : WP.valS K ≤ WP.valS ξ := le_trans (valS_le_of_prefix hKW) (not_lt.mp hξW)
    have h2 : WP.valS ξ < WP.valS K + v * ω := hKeq' ▸ hξlt
    obtain ⟨ξ', hξe, hξ'n, hξ'v⟩ := prefix_split_gen (w := trTm (.node yj csj))
      (fun x hx hlt => mul_omega0_le_of_principal (val_isPrincipal hx) hlt) hKn hξn hKv h1 h2
    obtain ⟨N, hN⟩ := lt_mul_omega0' hξ'v
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨R, hR⟩ := hKW
    rw [hξe, valS_append, add_assoc, ← hR, valS_append, add_assoc]
    refine (add_le_add_iff_left _).mpr (le_trans (Order.add_one_le_of_lt hN) ?_)
    refine le_trans ?_ le_add_self
    exact mul_le_mul_right (by exact_mod_cast (by omega : N ≤ n + 2)) _

/-! ## (B dup), the parent epsilon -/

theorem log_dup {yj : ℕ} {csj : List Tm} (hvj : Valid (.node yj (csj ++ [.node 0 []]))) :
    WP.valS (logOmega (trTm (.node yj (csj ++ [.node 0 []])))) =
      WP.valS (logOmega (trTm (.node yj csj))) + 1 := by
  have h1 := val_log_trTm (.node yj (csj ++ [.node 0 []]))
  have h2 : (trTm (.node yj csj)).val * ω = ω ^ (WP.valS (logOmega (trTm (.node yj csj))) + 1) := by
    rw [opow_add, opow_one, val_log_trTm]
  rw [val_trTm_dup hvj, h2] at h1
  have := le_antisymm ((opow_le_opow_iff_right one_lt_omega0).mp h1.le)
    ((opow_le_opow_iff_right one_lt_omega0).mp h1.ge)
  rw [this]

theorem dup_d_rho {k : ℕ} {csj : List Tm} (hvj : Valid (.node (k + 1) (csj ++ [.node 0 []]))) :
    dOf k (.node (k + 1) (csj ++ [.node 0 []])) = dOf k (.node (k + 1) csj) ∧
      WP.valS (rhoOf k (.node (k + 1) (csj ++ [.node 0 []]))) =
        WP.valS (rhoOf k (.node (k + 1) csj)) + 1 := by
  have hl := log_dup hvj
  rw [valS_log_eq k, valS_log_eq k, add_assoc] at hl
  obtain ⟨-, a1, -, a3, -⟩ := monOf_spec k (.node (k + 1) (csj ++ [.node 0 []]))
  obtain ⟨-, b1, -, b3, -⟩ := monOf_spec k (.node (k + 1) csj)
  have hD := d_eq_of_split a1 b1 (fun q hq => (a3 q hq).1) (fun q hq => (b3 q hq).1)
    (valS_rho_lt k _) ((Om_isPrincipal (k + 1)) (valS_rho_lt k _)
      (lt_trans one_lt_omega0 (omega0_lt_Om_succ k))) hl
  refine ⟨hD, ?_⟩
  rw [hD] at hl
  exact add_left_cancel hl

theorem addAll_rep_val (P : List (List WP)) (hP : ∀ x ∈ P, NFS x) (w : WP) (hw : NFP w) (r : ℕ) :
    WP.valS (addAll (P ++ List.replicate r [w])) = WP.valS (addAll P) + w.val * r := by
  rw [(addAll_spec (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hP x hx
      · rw [List.eq_of_mem_replicate hx]; exact NFS.single hw)).2, (addAll_spec hP).2,
    List.map_append, List.sum_append, List.map_replicate, valS_single, sum_replicate_ord]

/-- **(B dup)** for an epsilon parent `p = (k, H ++ [j₀])`, `y(j₀) = k + 1`, with
`p⟨n⟩ = (k, H ++ (j₀⁻)^{n+2})`. -/
theorem bdup_hi {k : ℕ} {H csj : List Tm}
    (hv : Valid (.node k (H ++ [.node (k + 1) (csj ++ [.node 0 []])])))
    (hwit : ∀ n, ∀ z ∈ starS k (argOf k (H ++ [.node (k + 1) (csj ++ [.node 0 []])])),
      z.val < (trTm (.node k (H ++ List.replicate (n + 2) (.node (k + 1) csj)))).val) :
    LC 0 (fun _ => True) (.node k (H ++ [.node (k + 1) (csj ++ [.node 0 []])]))
      (fun n => .node k (H ++ List.replicate (n + 2) (.node (k + 1) csj))) := by
  set j0 : Tm := .node (k + 1) (csj ++ [.node 0 []]) with hj0
  set j0m : Tm := .node (k + 1) csj with hj0m
  have hA : H ++ [j0] ≠ [] := by simp
  have hlA : ((H ++ [j0]).getLast hA).y = k + 1 := by simp [hj0]
  have hLn : ∀ n, H ++ List.replicate (n + 2) j0m ≠ [] := fun n => by simp
  have hlast : ∀ n, (H ++ List.replicate (n + 2) j0m).getLast (hLn n) = j0m := fun n => by
    rw [List.getLast_append_of_ne_nil _ (by simp)]; exact List.getLast_replicate _
  have hlLn : ∀ n, ((H ++ List.replicate (n + 2) j0m).getLast (hLn n)).y = k + 1 := fun n => by
    rw [hlast n]; rfl
  have hvj : Valid j0 := hv.child (by simp)
  obtain ⟨hD, hρ⟩ := dup_d_rho hvj
  have hna := nfp_trTm_eps hA hlA
  have hnL : ∀ n, NFP (WP.th k (argOf k (H ++ List.replicate (n + 2) j0m))) :=
    fun n => nfp_trTm_eps (hLn n) (hlLn n)
  have hE : ∀ n, (trTm (.node k (H ++ List.replicate (n + 2) j0m))).val =
      (WP.th k (argOf k (H ++ List.replicate (n + 2) j0m))).val := fun n => by
    rw [trTm_eps' (hLn n) (hlLn n)]
  intro γ hγ hlt hB
  rw [trTm_eps' hA hlA] at hlt
  refine lc_skeleton (Nat.zero_le k) hna (fun n => val_isPrincipal (trTm_nfp _))
    (fun n => (trTm_eps_isEps (hLn n) (hlLn n)).1) hwit (fun β hβn hβlt _ hsIH => ?_) γ hγ hlt hB
  suffices hsuf : ∃ n0, ∀ n ≥ n0,
      WP.valS β < WP.valS (argOf k (H ++ List.replicate (n + 2) j0m)) by
    obtain ⟨n0, h0⟩ := hsuf
    obtain ⟨n1, h1⟩ := eventually_forall _ hsIH
    refine ⟨max n0 n1, fun n hn => ?_⟩
    rw [hE n, val_lt_val_iff hβn (hnL n)]
    left
    exact ⟨h0 n (le_trans (le_max_left _ _) hn), fun s hs => by
      rw [← hE n]; exact h1 n (le_trans (le_max_right _ _) hn) s hs⟩
  have hΔ : deltaOf k (H ++ [j0]) = dOf k j0m := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp), ← hD]; rfl
  have hΔL : ∀ n, deltaOf k (H ++ List.replicate (n + 2) j0m) = dOf k j0m := fun n => by
    rw [deltaOf, List.getLast?_eq_some_getLast (hLn n), hlast n]; rfl
  obtain ⟨hsplit, hΓn, hσn, hΓl, hσl⟩ := splitLevel_spec hβn.nfs (k + 1)
  set Γ := (splitLevel β (k + 1)).1
  set σ := (splitLevel β (k + 1)).2
  have hσl' : ∀ q ∈ σ, q.lvl ≤ k := fun q hq => Nat.lt_succ_iff.mp (hσl q hq)
  have hβv : WP.valS β = WP.valS Γ + WP.valS σ := by rw [hsplit, valS_append]
  obtain ⟨hΔn', hΔl', -⟩ := deltaOf_spec hA hlA
  have hargA := (argOf_spec hA hlA).2.2
  have hargL : ∀ n, WP.valS (argOf k (H ++ List.replicate (n + 2) j0m)) =
      WP.valS (deltaOf k (H ++ [j0])) + WP.valS (eta'Of k (H ++ List.replicate (n + 2) j0m)) :=
    fun n => by rw [(argOf_spec (hLn n) (hlLn n)).2.2, hΔL n, hΔ]
  have hΓle : WP.valS Γ ≤ WP.valS (deltaOf k (H ++ [j0])) := by
    refine (split_mono (ρ := σ) hΓn hΔn' hΓl (fun q hq => (hΔl' q hq).ge)
      (val_eps_lt_Om (H := H ++ [j0])) ?_).1
    rw [← hβv, ← hargA]; exact hβlt.le
  rcases hΓle.lt_or_eq with hΓlt | hΓeq
  · refine ⟨0, fun n _ => ?_⟩
    rw [hβv, hargL n]
    refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr (valS_lt_Om hσn hσl'))
      (le_trans ?_ le_self_add)
    exact gap_of_lt hΔn' hΓn (fun q hq => (hΔl' q hq).ge) hΓl hΓlt
  -- `Γ = Δ`: the runs
  have hση : WP.valS σ < WP.valS (eta'Of k (H ++ [j0])) := by
    rw [hβv, hΓeq, hargA] at hβlt
    exact (add_lt_add_iff_left _).mp hβlt
  have hmapA : (H ++ [j0]).map (dOf k) = H.map (dOf k) ++ [dOf k j0m] := by
    rw [List.map_append, List.map_singleton, show dOf k j0 = dOf k j0m from hD]
  have hmapL : ∀ n, (H ++ List.replicate (n + 2) j0m).map (dOf k) =
      H.map (dOf k) ++ List.replicate (n + 2) (dOf k j0m) := fun n => by simp
  have hj : ∀ n, jOf k (H ++ List.replicate (n + 2) j0m) = jOf k (H ++ [j0]) := fun n => by
    rw [jOf, jOf, hmapL n, hmapA]
    exact runStart_append_const (by simp) (fun e he => List.eq_of_mem_replicate he)
  set j := jOf k (H ++ [j0]) with hjdef
  have hjle : j ≤ H.length := by
    have := runStart_lt (ds := (H ++ [j0]).map (dOf k)) (by simp)
    simp only [List.length_map, List.length_append, List.length_singleton] at this
    exact Nat.lt_succ_iff.mp this
  have hep : ∀ n, epOf k (H ++ List.replicate (n + 2) j0m) = epOf k (H ++ [j0]) := fun n => by
    rw [epOf, epOf, hj n, List.take_append_of_le_length hjle, List.take_append_of_le_length hjle]
  have hΔeq : ∀ n, deltaOf k (H ++ List.replicate (n + 2) j0m) = deltaOf k (H ++ [j0]) :=
    fun n => by rw [hΔL n, hΔ]
  have hins : ∀ n, insOf k (H ++ List.replicate (n + 2) j0m) ↔ insOf k (H ++ [j0]) := fun n => by
    unfold insOf; rw [hj n, hΔeq n, hep n]
  set P : List (List WP) := (H.drop j).map (fun h => [wOf k h]) with hP
  have hPn : ∀ x ∈ P, NFS x := fun x hx => by
    rw [hP, List.mem_map] at hx; obtain ⟨h, -, rfl⟩ := hx; exact NFS.single (wOf_spec k h).1
  have hcA : cOf k (H ++ [j0]) = addAll (P ++ [[wOf k j0]]) := by
    rw [cOf, ← hjdef, List.drop_append_of_le_length hjle, List.map_append, List.map_singleton]
  have hcL : ∀ n, cOf k (H ++ List.replicate (n + 2) j0m) =
      addAll (P ++ List.replicate (n + 2) [wOf k j0m]) := fun n => by
    rw [cOf, hj n, List.drop_append_of_le_length hjle, List.map_append,
      List.map_replicate]
  have hvcA : WP.valS (cOf k (H ++ [j0])) = WP.valS (addAll P) +
      ω ^ (WP.valS (rhoOf k j0m) + 1) := by
    rw [hcA, addAll_append_single, (addS_spec (addAll_spec hPn).1
      (NFS.single (wOf_spec k j0).1)).2, valS_single, (wOf_spec k j0).2.2.2, hρ]
  have hvcL : ∀ n, WP.valS (cOf k (H ++ List.replicate (n + 2) j0m)) =
      WP.valS (addAll P) + ω ^ WP.valS (rhoOf k j0m) * ((n : Ordinal) + 2) := fun n => by
    rw [hcL n, addAll_rep_val P hPn _ (wOf_spec k j0m).1, (wOf_spec k j0m).2.2.2]
    push_cast; rfl
  set e : Ordinal.{0} := if insOf k (H ++ [j0]) then (epOf k (H ++ [j0])).val else 0 with he
  have hηA : WP.valS (eta'Of k (H ++ [j0])) = e + WP.valS (etaOf k (H ++ [j0])) := by
    rw [val_eta'Of]
  have hηL : ∀ n, WP.valS (eta'Of k (H ++ List.replicate (n + 2) j0m)) =
      e + WP.valS (etaOf k (H ++ List.replicate (n + 2) j0m)) := fun n => by
    rw [val_eta'Of, he]
    by_cases hi : insOf k (H ++ [j0])
    · rw [if_pos ((hins n).mpr hi), if_pos hi, hep n]
    · rw [if_neg (fun h => hi ((hins n).mp h)), if_neg hi]
  have hμA : 1 + WP.valS (etaOf k (H ++ [j0])) = WP.valS (addAll P) +
      ω ^ (WP.valS (rhoOf k j0m) + 1) := by
    rw [etaOf, one_add_minusOnePlus (cOf_spec k _).1 (cOf_ne_nil hA), hvcA]
  have hμL : ∀ n, 1 + WP.valS (etaOf k (H ++ List.replicate (n + 2) j0m)) =
      WP.valS (addAll P) + ω ^ WP.valS (rhoOf k j0m) * ((n : Ordinal) + 2) := fun n => by
    rw [etaOf, one_add_minusOnePlus (cOf_spec k _).1 (cOf_ne_nil (hLn n)), hvcL n]
  rw [hηA] at hση
  obtain ⟨N, hN⟩ := mu_eventually hμA hμL hση
  refine ⟨N, fun n hn => ?_⟩
  rw [hβv, hargL n, hΓeq, hηL n]
  exact (add_lt_add_iff_left _).mpr (hN n hn)

end Googology.Trans.PSS.TR
