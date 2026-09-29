import Googology.Trans.PSS.TR.PLo

/-!
# Lemma P-hi

`proof/TR-2.md` §4b.2.  Let `a = (k, H ++ [c])` be epsilon and `a⟨n⟩ =
(k, H ++ [c⟨n⟩])`, with `c` and every `c⟨n⟩` of level `k + 1`.

* `arg_step`: the case (i) of P-hi.  If `β < Δ + η` (the argument of `𝒯(a)`),
  `B(β)`, and the visible `ϑ_k`-subterms of `β` are eventually below
  `𝒯(a⟨n⟩)`, then `ϑ_k(β)` is eventually below `𝒯(a⟨n⟩)`.  The cases:
  `Γ < Δ` (X-form of `LC_B(c)`); `Γ = Δ` with the same `D` for every `c⟨n⟩`
  (the run is unchanged, split `σ = K ++ σ''` and use the X-form on
  `Δ + log(σ''_1)`); `Γ = Δ` with `ρ_c = 0` (the anchor `(k, H)`: (Inc), or (C)
  against `e_p`).
* `eps_lc`: **Lemma P-hi** in the general form used also for the base
  `(B j₀)`: induction on the size of `γ`, with (C), case (ii) by M4 (the
  hypothesis `hwit`), and case (i) by `arg_step`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

theorem minusOnePlus_addS_ge {C : List WP} (hC : NFS C) {w : WP} (hw : NFP w) :
    WP.valS (minusOnePlus C) ≤ WP.valS (minusOnePlus (addS C [w])) := by
  rcases eq_or_ne C [] with rfl | hne
  · simp [minusOnePlus]
  · have hn := (addS_spec hC (NFS.single hw))
    have hne' : addS C [w] ≠ [] := by rw [addS]; simp
    have e1 := one_add_minusOnePlus hC hne
    have e2 := one_add_minusOnePlus hn.1 hne'
    rw [hn.2, valS_single, ← e1, add_assoc] at e2
    have : 1 + WP.valS (minusOnePlus C) ≤ 1 + WP.valS (minusOnePlus (addS C [w])) := by
      rw [e2]; exact (add_le_add_iff_left 1).mpr le_self_add
    exact (add_le_add_iff_left _).mp this

theorem minusOnePlus_addS_eq {C : List WP} (hC : NFS C) {w : WP} (hw : NFP w) (hw1 : 1 < w.val) :
    WP.valS (minusOnePlus (addS C [w])) = WP.valS (minusOnePlus C) + w.val := by
  have hn := (addS_spec hC (NFS.single hw))
  rcases eq_or_ne C [] with rfl | hne
  · have hw' : w ≠ one := fun e => by rw [e, val_one] at hw1; exact lt_irrefl _ hw1
    simp [addS, minusOnePlus, hw']
  · have hne' : addS C [w] ≠ [] := by rw [addS]; simp
    have e1 := one_add_minusOnePlus hC hne
    have e2 := one_add_minusOnePlus hn.1 hne'
    rw [hn.2, valS_single, ← e1, add_assoc] at e2
    exact add_left_cancel e2

theorem minusOnePlus_addS_eq_of_ne {C : List WP} (hC : NFS C) (hne : C ≠ []) {w : WP}
    (hw : NFP w) :
    WP.valS (minusOnePlus (addS C [w])) = WP.valS (minusOnePlus C) + w.val := by
  have hn := (addS_spec hC (NFS.single hw))
  have hne' : addS C [w] ≠ [] := by rw [addS]; simp
  have e1 := one_add_minusOnePlus hC hne
  have e2 := one_add_minusOnePlus hn.1 hne'
  rw [hn.2, valS_single, ← e1, add_assoc] at e2
  exact add_left_cancel e2

theorem wOf_eq_one {k : ℕ} {h : Tm} (hρ : rhoOf k h = []) : wOf k h = one := by
  rw [wOf, hρ]; rfl

theorem one_lt_wOf {k : ℕ} {h : Tm} (hρ : 0 < WP.valS (rhoOf k h)) : 1 < (wOf k h).val := by
  rw [(wOf_spec k h).2.2.2]
  exact lt_of_lt_of_le (by simpa using (opow_lt_opow_iff_right one_lt_omega0).mpr hρ) le_rfl

theorem eta_ge_rho {η ρ : Ordinal.{0}} (h : ω ^ ρ ≤ 1 + η) : ρ ≤ η := by
  rcases eq_or_ne ρ 0 with rfl | hρ
  · exact zero_le
  · have hω : ω ≤ ω ^ ρ := by
      calc ω = ω ^ (1 : Ordinal) := (opow_one ω).symm
        _ ≤ ω ^ ρ := opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.mpr hρ)
    have hη : ω ≤ η := by
      by_contra hc
      rw [not_le] at hc
      have : 1 + η < ω := isPrincipal_add_omega0 one_lt_omega0 hc
      exact absurd (le_trans hω h) (not_le.mpr this)
    rw [Ordinal.one_add_of_omega0_le hη] at h
    exact le_trans (right_le_opow _ one_lt_omega0) h

/-- `ρ` of the last child is at most `η'`. -/
theorem rho_le_eta' {k : ℕ} (H : List Tm) (x : Tm) :
    WP.valS (rhoOf k x) ≤ WP.valS (eta'Of k (H ++ [x])) := by
  rw [val_eta'Of]
  refine le_trans ?_ le_add_self
  have hne : H ++ [x] ≠ [] := by simp
  have hjlt : jOf k (H ++ [x]) ≤ H.length := by
    have := runStart_lt (ds := (H ++ [x]).map (dOf k)) (by simp)
    simp only [List.length_map, List.length_append, List.length_singleton] at this
    exact Nat.lt_succ_iff.mp this
  have hc := cOf_spec k (H ++ [x])
  have hxmem : x ∈ (H ++ [x]).drop (jOf k (H ++ [x])) := by
    rw [List.drop_append_of_le_length hjlt]; simp
  have hle : ω ^ WP.valS (rhoOf k x) ≤ WP.valS (cOf k (H ++ [x])) := by
    rw [hc.2.2, ← (wOf_spec k x).2.2.2]
    exact le_sum_of_mem (List.mem_map_of_mem hxmem)
  refine eta_ge_rho ?_
  rw [etaOf, one_add_minusOnePlus hc.1 (cOf_ne_nil hne)]
  exact hle

/-- The case (i) of **Lemma P-hi** (`proof/TR-2.md` §4b.2). -/
theorem arg_step {k m : ℕ} {P : WP → Prop} (hP1 : P one) (hPo : P (om m))
    {H : List Tm} {c : Tm} {cn : ℕ → Tm} (hc : c.y = k + 1) (hcn : ∀ n, (cn n).y = k + 1)
    (hHl : ∀ h ∈ H, h.y = k + 1) (hlt : ∀ n, (trTm (cn n)).val < (trTm c).val)
    (hcase : (∀ n, dOf k (cn n) = dOf k c) ∨ rhoOf k c = [])
    (hrc : ∀ hne : H ≠ [], (trTm c).val ≤ (trTm (H.getLast hne)).val)
    (hanc : ∀ n, (trTm (.node k H)).val < (trTm (.node k (H ++ [cn n]))).val)
    (hLCX : LCX m P c cn) {β : List WP} (hβn : NFP (.th k β))
    (hβlt : WP.valS β < WP.valS (argOf k (H ++ [c]))) (hBβ : Bm m P β)
    (hstar : ∃ n1, ∀ n ≥ n1, ∀ s ∈ starS k β, s.val < (trTm (.node k (H ++ [cn n]))).val) :
    ∃ n0, ∀ n ≥ n0, (WP.th k β).val < (trTm (.node k (H ++ [cn n]))).val := by
  have hA : H ++ [c] ≠ [] := by simp
  have hlA : ((H ++ [c]).getLast hA).y = k + 1 := by simpa using hc
  have hAn : ∀ n, H ++ [cn n] ≠ [] := fun n => by simp
  have hlAn : ∀ n, ((H ++ [cn n]).getLast (hAn n)).y = k + 1 := fun n => by simpa using hcn n
  have hΔ : deltaOf k (H ++ [c]) = dOf k c := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  have hΔn : ∀ n, deltaOf k (H ++ [cn n]) = dOf k (cn n) := fun n => by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  have hE : ∀ n, (trTm (.node k (H ++ [cn n]))).val = (WP.th k (argOf k (H ++ [cn n]))).val :=
    fun n => by rw [trTm_eps' (hAn n) (hlAn n)]
  have hnE : ∀ n, NFP (WP.th k (argOf k (H ++ [cn n]))) := fun n => nfp_trTm_eps (hAn n) (hlAn n)
  -- it suffices to get the argument below, or the value below directly
  suffices hsuf : ∃ n0, ∀ n ≥ n0, WP.valS β < WP.valS (argOf k (H ++ [cn n])) ∨
      (WP.th k β).val < (trTm (.node k (H ++ [cn n]))).val by
    obtain ⟨n0, h0⟩ := hsuf
    obtain ⟨n1, h1⟩ := hstar
    refine ⟨max n0 n1, fun n hn => ?_⟩
    rcases h0 n (le_trans (le_max_left _ _) hn) with h | h
    · rw [hE n, val_lt_val_iff hβn (hnE n)]
      left
      exact ⟨h, fun s hs => by rw [← hE n]; exact h1 n (le_trans (le_max_right _ _) hn) s hs⟩
    · exact h
  -- `β = Γ + σ`
  obtain ⟨hsplit, hΓn, hσn, hΓl, hσl⟩ := splitLevel_spec hβn.nfs (k + 1)
  set Γ := (splitLevel β (k + 1)).1
  set σ := (splitLevel β (k + 1)).2
  have hσl' : ∀ q ∈ σ, q.lvl ≤ k := fun q hq => Nat.lt_succ_iff.mp (hσl q hq)
  have hβv : WP.valS β = WP.valS Γ + WP.valS σ := by rw [hsplit, valS_append]
  obtain ⟨hΔn', hΔl', -⟩ := deltaOf_spec hA hlA
  have hargA := (argOf_spec hA hlA).2.2
  have hη'lt : WP.valS (eta'Of k (H ++ [c])) < Om (k + 1) := val_eps_lt_Om
  have hσlt' : WP.valS σ < Om (k + 1) := valS_lt_Om hσn hσl'
  have hΓle : WP.valS Γ ≤ WP.valS (deltaOf k (H ++ [c])) := by
    refine (split_mono (ρ := σ) hΓn hΔn' hΓl (fun q hq => (hΔl' q hq).ge) hη'lt ?_).1
    rw [← hβv, ← hargA]; exact hβlt.le
  rcases hΓle.lt_or_eq with hΓlt | hΓeq
  · -- `Γ < Δ`: the X-form
    have hβX : WP.valS β < WP.valS (logOmega (trTm c)) := by
      rw [hβv, valS_log_eq k c]
      refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr hσlt') (le_trans ?_ le_self_add)
      rw [← hΔ]
      exact gap_of_lt hΔn' hΓn (fun q hq => (hΔl' q hq).ge) hΓl hΓlt
    obtain ⟨n0, h0⟩ := hLCX β hβn.nfs hβX hBβ
    refine ⟨n0, fun n hn => Or.inl ?_⟩
    have := h0 n hn
    rw [valS_log_eq k] at this
    rw [(argOf_spec (hAn n) (hlAn n)).2.2, hΔn n]
    exact lt_of_lt_of_le this ((add_le_add_iff_left _).mpr (rho_le_eta' H (cn n)))
  -- `Γ = Δ`
  have hΓΔ : Γ = deltaOf k (H ++ [c]) := eq_of_valS_eq hΓn hΔn' hΓeq
  have hση : WP.valS σ < WP.valS (eta'Of k (H ++ [c])) := by
    rw [hβv, hΓeq, hargA] at hβlt
    exact (add_lt_add_iff_left _).mp hβlt
  rcases hcase with hD | hρ0
  · -- the run is unchanged
    have hmap : ∀ n, (H ++ [cn n]).map (dOf k) = (H ++ [c]).map (dOf k) := fun n => by
      simp [hD n]
    have hj : ∀ n, jOf k (H ++ [cn n]) = jOf k (H ++ [c]) := fun n => by
      rw [jOf, jOf, hmap n]
    set j := jOf k (H ++ [c]) with hjdef
    have hjle : j ≤ H.length := by
      have := runStart_lt (ds := (H ++ [c]).map (dOf k)) (by simp)
      simp only [List.length_map, List.length_append, List.length_singleton] at this
      exact Nat.lt_succ_iff.mp this
    have hep : ∀ n, epOf k (H ++ [cn n]) = epOf k (H ++ [c]) := fun n => by
      rw [epOf, epOf, hj n, List.take_append_of_le_length hjle,
        List.take_append_of_le_length hjle]
    have hΔeq : ∀ n, deltaOf k (H ++ [cn n]) = deltaOf k (H ++ [c]) := fun n => by
      rw [hΔn, hΔ, hD]
    have hins : ∀ n, insOf k (H ++ [cn n]) ↔ insOf k (H ++ [c]) := fun n => by
      unfold insOf; rw [hj n, hΔeq n, hep n]
    set C := addAll ((H.drop j).map (fun h => [wOf k h])) with hCdef
    have hCn : NFS C := (addAll_spec (fun x hx => by
      rw [List.mem_map] at hx; obtain ⟨h, -, rfl⟩ := hx; exact NFS.single (wOf_spec k h).1)).1
    have hcx : ∀ x : Tm, jOf k (H ++ [x]) = j → cOf k (H ++ [x]) = addS C [wOf k x] := by
      intro x hx
      rw [cOf, hx, List.drop_append_of_le_length hjle, List.map_append, List.map_singleton,
        addAll_append_single]
    set e : Ordinal.{0} := if insOf k (H ++ [c]) then (epOf k (H ++ [c])).val else 0 with hedef
    -- `η'` as a function of the last child
    have hη'x : ∀ x : Tm, jOf k (H ++ [x]) = j → (insOf k (H ++ [x]) ↔ insOf k (H ++ [c])) →
        epOf k (H ++ [x]) = epOf k (H ++ [c]) →
        WP.valS (eta'Of k (H ++ [x])) = e + WP.valS (minusOnePlus (addS C [wOf k x])) := by
      intro x hx hi he
      rw [val_eta'Of, etaOf, hcx x hx, hedef]
      by_cases h : insOf k (H ++ [c])
      · rw [if_pos (hi.mpr h), if_pos h, he]
      · rw [if_neg (fun h' => h (hi.mp h')), if_neg h]
    set Pv := e + WP.valS (minusOnePlus C) with hPvdef
    have hρlt : ∀ n, WP.valS (rhoOf k (cn n)) < WP.valS (rhoOf k c) := by
      intro n
      have hX : WP.valS (logOmega (trTm (cn n))) < WP.valS (logOmega (trTm c)) := by
        have := hlt n
        rw [← val_log_trTm (cn n), ← val_log_trTm c] at this
        exact (opow_lt_opow_iff_right one_lt_omega0).mp this
      rw [valS_log_eq k, valS_log_eq k, hD n] at hX
      exact (add_lt_add_iff_left _).mp hX
    have hρc : 0 < WP.valS (rhoOf k c) := lt_of_le_of_lt zero_le (hρlt 0)
    have hηc : WP.valS (eta'Of k (H ++ [c])) = Pv + (wOf k c).val := by
      rw [hη'x c rfl Iff.rfl rfl, minusOnePlus_addS_eq hCn (wOf_spec k c).1 (one_lt_wOf hρc),
        hPvdef, add_assoc]
    have hηn : ∀ n, 0 < WP.valS (rhoOf k (cn n)) →
        WP.valS (eta'Of k (H ++ [cn n])) = Pv + (wOf k (cn n)).val := by
      intro n hn
      rw [hη'x (cn n) (hj n) (hins n) (hep n),
        minusOnePlus_addS_eq hCn (wOf_spec k _).1 (one_lt_wOf hn), hPvdef, add_assoc]
    have hPvle : ∀ n, Pv ≤ WP.valS (eta'Of k (H ++ [cn n])) := by
      intro n
      rw [hη'x (cn n) (hj n) (hins n) (hep n), hPvdef]
      exact (add_le_add_iff_left _).mpr (minusOnePlus_addS_ge hCn (wOf_spec k _).1)
    have hargn : ∀ n, WP.valS (argOf k (H ++ [cn n])) =
        WP.valS (deltaOf k (H ++ [c])) + WP.valS (eta'Of k (H ++ [cn n])) := fun n => by
      rw [(argOf_spec (hAn n) (hlAn n)).2.2, hΔeq n]
    by_cases hσPv : WP.valS σ < Pv
    · refine ⟨0, fun n _ => Or.inl ?_⟩
      rw [hβv, hargn n, hΓeq]
      exact (add_lt_add_iff_left _).mpr (lt_of_lt_of_le hσPv (hPvle n))
    -- `σ = K ++ σ''` with `σ'' < ω^{ρ_c}`
    set Pvt : List WP := if insOf k (H ++ [c]) then addS [epOf k (H ++ [c])] (minusOnePlus C)
      else minusOnePlus C with hPvtdef
    have hPvtn : NFS Pvt := by
      have h1 : NFS (minusOnePlus C) := hCn.sublist (minusOnePlus_sublist _)
      rw [hPvtdef]; split_ifs
      · exact (addS_spec (NFS.single (trTm_nfp _)) h1).1
      · exact h1
    have hPvtv : WP.valS Pvt = Pv := by
      rw [hPvtdef, hPvdef, hedef]
      split_ifs
      · rw [(addS_spec (x := [epOf k (H ++ [c])]) (NFS.single (trTm_nfp _))
          (hCn.sublist (minusOnePlus_sublist _))).2, valS_single]
      · rw [zero_add]
    obtain ⟨K, hKPv, hKn, hKv, hKeq⟩ := absorb_prefix hPvtn (wOf_spec k c).1
    have h1 : WP.valS K ≤ WP.valS σ :=
      le_trans (valS_le_of_prefix hKPv) (by rw [hPvtv]; exact not_lt.mp hσPv)
    have h2 : WP.valS σ < WP.valS K + (wOf k c).val := by rw [hKeq, hPvtv, ← hηc]; exact hση
    obtain ⟨σ'', hσe, hσ''n, hσ''v⟩ := prefix_split (wOf_spec k c).1 hKn hσn hKv h1 h2
    have hBσ : Bm m P σ := hBβ.sublist (by rw [hsplit]; exact List.sublist_append_right _ _)
    have hBσ'' : Bm m P σ'' := hBσ.sublist (by rw [hσe]; exact List.sublist_append_right _ _)
    -- `ζ = log` of the first summand of `σ''`
    obtain ⟨ζ, hζn, hζl, hζρ, hσ''ζ, hBζ⟩ : ∃ ζ : List WP, NFS ζ ∧ (∀ q ∈ ζ, q.lvl ≤ k) ∧
        WP.valS ζ < WP.valS (rhoOf k c) ∧ WP.valS σ'' < ω ^ (WP.valS ζ + 1) ∧ Bm m P ζ := by
      cases e' : σ'' with
      | nil =>
        exact ⟨[], NFS.nil, by simp, by simpa using hρc, by simp,
          fun s hs => by simp at hs⟩
      | cons q r =>
        rw [e'] at hσ''n hσ''v hBσ''
        have hq := hσ''n.head
        obtain ⟨hl1, hl2, hl3⟩ := logOmega_spec hq
        have hqmem : q ∈ σ := by rw [hσe, e']; simp
        refine ⟨logOmega q, hl1, fun p hp => le_trans (hl3 p hp) (hσl' q hqmem), ?_,
          valS_lt_opow_succ hσ''n hl2.symm, Bm.log hP1 hPo hq (hBσ''.single_of_mem (by simp))⟩
        refine (opow_lt_opow_iff_right one_lt_omega0).mp ?_
        rw [hl2, ← (wOf_spec k c).2.2.2]
        exact lt_of_le_of_lt le_valS_head hσ''v
    have hξn : NFS (deltaOf k (H ++ [c]) ++ ζ) := by
      refine NFS.append_iff.mpr ⟨hΔn', hζn, fun p hp q hq => ?_⟩
      exact (val_lt_of_lvl_lt (hζn.1 q hq) (hΔn'.1 p hp) (by rw [hΔl' p hp]; have := hζl q hq; omega)).le
    have hBξ : Bm m P (deltaOf k (H ++ [c]) ++ ζ) :=
      Bm.append (hBβ.sublist (by rw [hsplit, ← hΓΔ]; exact List.sublist_append_left _ _)) hBζ
    have hξlt : WP.valS (deltaOf k (H ++ [c]) ++ ζ) < WP.valS (logOmega (trTm c)) := by
      rw [valS_append, valS_log_eq k c, hΔ]
      exact (add_lt_add_iff_left _).mpr hζρ
    obtain ⟨n0, h0⟩ := hLCX _ hξn hξlt hBξ
    refine ⟨n0, fun n hn => Or.inl ?_⟩
    have hζn' : WP.valS ζ < WP.valS (rhoOf k (cn n)) := by
      have := h0 n hn
      rw [valS_append, valS_log_eq k (cn n), hΔ, hD n] at this
      exact (add_lt_add_iff_left _).mp this
    rw [hβv, hargn n, hΓeq, hηn n (lt_of_le_of_lt zero_le hζn')]
    refine (add_lt_add_iff_left _).mpr ?_
    rw [hσe, valS_append]
    obtain ⟨R, hR⟩ := hKPv
    calc WP.valS K + WP.valS σ'' < WP.valS K + ω ^ (WP.valS ζ + 1) :=
          (add_lt_add_iff_left _).mpr hσ''ζ
      _ ≤ WP.valS K + (wOf k (cn n)).val := by
          rw [(wOf_spec k (cn n)).2.2.2]
          exact (add_le_add_iff_left _).mpr ((opow_le_opow_iff_right one_lt_omega0).mpr
            (Order.add_one_le_of_lt hζn'))
      _ ≤ Pv + (wOf k (cn n)).val := by
          rw [← hPvtv, ← hR, valS_append, add_assoc]
          exact (add_le_add_iff_left _).mpr (le_add_left le_rfl)
  · -- `ρ_c = 0`: through the anchor `(k, H)`
    have hwc : wOf k c = one := wOf_eq_one hρ0
    rcases eq_or_ne H [] with rfl | hHne
    · exfalso
      have hj0 : jOf k ([] ++ [c]) = 0 := by simp [jOf, runStart]
      have : WP.valS (eta'Of k ([] ++ [c])) = 0 := by
        rw [val_eta'Of, if_neg (by unfold insOf; rw [hj0]; simp), zero_add, etaOf, cOf, hj0]
        simp [hwc, addAll, addS, minusOnePlus]
      rw [this] at hση
      exact absurd hση (not_lt.mpr zero_le)
    have hlH : (H.getLast hHne).y = k + 1 := hHl _ (List.getLast_mem hHne)
    obtain ⟨hDle, -⟩ := d_rho_mono (k := k) (hrc hHne)
    have hdH : deltaOf k H = dOf k (H.getLast hHne) := by
      rw [deltaOf, List.getLast?_eq_some_getLast hHne]; rfl
    have hanc0 := hanc 0
    have hanchor : trTm (.node k H) = .th k (argOf k H) := trTm_eps' hHne hlH
    have hnanc : NFP (WP.th k (argOf k H)) := nfp_trTm_eps hHne hlH
    rcases hDle.lt_or_eq with hDlt | hDeq
    · -- a new run: `e_p = 𝒯(k, H)`
      have hdne : dOf k c ≠ dOf k (H.getLast hHne) := fun e' => by
        rw [e'] at hDlt; exact lt_irrefl _ hDlt
      have hj : jOf k (H ++ [c]) = H.length := by
        rw [jOf, List.map_append, List.map_singleton,
          runStart_append_ne (fun hne2 => by rw [List.getLast_map]; exact hdne)]
        simp
      have hep : epOf k (H ++ [c]) = trTm (.node k H) := by
        rw [epOf, hj, List.take_left]
      have hc1 : cOf k (H ++ [c]) = [one] := by
        rw [cOf, hj, List.drop_left, List.map_singleton, hwc]; rfl
      have hη0 : etaOf k (H ++ [c]) = [] := by rw [etaOf, hc1]; simp [minusOnePlus]
      by_cases hins : insOf k (H ++ [c])
      · have hσep : WP.valS σ < (trTm (.node k H)).val := by
          rw [val_eta'Of, if_pos hins, hη0, WP.valS_nil, add_zero, hep] at hση
          exact hση
        refine ⟨0, fun n _ => Or.inr (lt_trans ?_ (hanc n))⟩
        rw [hanchor, val_lt_val_iff hβn hnanc]
        left
        refine ⟨?_, fun z hz => ?_⟩
        · rw [hβv, hΓeq, hΔ, (argOf_spec hHne hlH).2.2, hdH]
          refine lt_of_lt_of_le ((add_lt_add_iff_left _).mpr hσlt') (le_trans ?_ le_self_add)
          exact gap_of_lt (monOf_spec k _).2.1 (monOf_spec k c).2.1
            (fun q hq => ((monOf_spec k _).2.2.2.1 q hq).1)
            (fun q hq => ((monOf_spec k c).2.2.2.1 q hq).1) hDlt
        · rw [← hanchor]
          rw [hsplit, starS_append, List.mem_append] at hz
          rcases hz with hz | hz
          · rw [hΓΔ] at hz
            rw [← hep]
            exact hins.2 z hz
          · obtain ⟨p, r, hpr, hzp⟩ := star_le_head hσn hσl' hz
            refine lt_of_le_of_lt hzp (lt_of_le_of_lt ?_ hσep)
            rw [hpr]; exact le_valS_head
      · exfalso
        rw [val_eta'Of, if_neg hins, hη0] at hση
        simp at hση
    · -- the same run: `η_a = η_{(k,H)} + 1`
      have hD : dOf k c = dOf k (H.getLast hHne) :=
        eq_of_valS_eq (monOf_spec k c).2.1 (monOf_spec k _).2.1 hDeq
      have hj : jOf k (H ++ [c]) = jOf k H := by
        rw [jOf, jOf, List.map_append, List.map_singleton, hD]
        have := runStart_append_last (ds := H.map (dOf k)) (by simpa using hHne)
        rw [List.getLast_map] at this
        exact this
      have hjle : jOf k H ≤ H.length := by
        have := runStart_le_length (H.map (dOf k)); simpa using this
      have hep : epOf k (H ++ [c]) = epOf k H := by
        rw [epOf, epOf, hj, List.take_append_of_le_length hjle]
      have hΔ' : deltaOf k (H ++ [c]) = deltaOf k H := by rw [hΔ, hdH, hD]
      have hins : insOf k (H ++ [c]) ↔ insOf k H := by
        unfold insOf; rw [hj, hΔ', hep]
      have hcc : cOf k (H ++ [c]) = addS (cOf k H) [one] := by
        rw [cOf, cOf, hj, List.drop_append_of_le_length hjle, List.map_append,
          List.map_singleton, addAll_append_single, hwc]
      have hη1 : WP.valS (etaOf k (H ++ [c])) = WP.valS (etaOf k H) + 1 := by
        rw [etaOf, etaOf, hcc, minusOnePlus_addS_eq_of_ne (cOf_spec k H).1 (cOf_ne_nil hHne)
          nfp_one, val_one]
      have hη'1 : WP.valS (eta'Of k (H ++ [c])) = WP.valS (eta'Of k H) + 1 := by
        rw [val_eta'Of, val_eta'Of, hη1, ← add_assoc]
        by_cases hi : insOf k H
        · rw [if_pos (hins.mpr hi), if_pos hi, hep]
        · rw [if_neg (fun h => hi (hins.mp h)), if_neg hi]
      have hσle : WP.valS σ ≤ WP.valS (eta'Of k H) := by
        rw [hη'1] at hση; exact Order.lt_add_one_iff.mp hση
      have hβe : β = deltaOf k H ++ σ := by rw [hsplit, hΓΔ, hΔ']
      have hn1 : NFP (WP.th k (deltaOf k H ++ σ)) := by rw [← hβe]; exact hβn
      have hn2 : NFP (WP.th k (deltaOf k H ++ eta'Of k H)) := by
        rw [← argOf_eq hHne hlH]; exact hnanc
      refine ⟨0, fun n _ => Or.inr (lt_of_le_of_lt ?_ (hanc n))⟩
      rw [hanchor, hβe, argOf_eq hHne hlH]
      exact inc_le hn1 hn2 hσl' (eta'Of_spec k H).2 hσle

/-- **Lemma P-hi** (`proof/TR-2.md` §4b.2), in the form used also for the base
`(B j₀)`: the bound `B_γ = Bm mγ Pγ` on `γ`, and the bound `B_β = Bm mβ Pβ` on the
arguments, which `hB` provides from `B_γ` and the induction hypothesis. -/
theorem eps_lc {k mγ mβ : ℕ} {Pγ Pβ : WP → Prop} (hPβ1 : Pβ one) (hPβo : Pβ (om mβ))
    (hmγ : mγ ≤ k) {H : List Tm} {c : Tm} {cn : ℕ → Tm} (hc : c.y = k + 1)
    (hcn : ∀ n, (cn n).y = k + 1) (hHl : ∀ h ∈ H, h.y = k + 1)
    (hlt : ∀ n, (trTm (cn n)).val < (trTm c).val)
    (hcase : (∀ n, dOf k (cn n) = dOf k c) ∨ rhoOf k c = [])
    (hrc : ∀ hne : H ≠ [], (trTm c).val ≤ (trTm (H.getLast hne)).val)
    (hanc : ∀ n, (trTm (.node k H)).val < (trTm (.node k (H ++ [cn n]))).val)
    (hLCX : LCX mβ Pβ c cn)
    (hwit : ∀ n, ∀ z ∈ starS k (argOf k (H ++ [c])), z.val < (trTm (.node k (H ++ [cn n]))).val)
    (hB : ∀ β : List WP, NFP (.th k β) → Bm mγ Pγ [.th k β] →
      (∀ s ∈ starS k β, ∃ n0, ∀ n ≥ n0, s.val < (trTm (.node k (H ++ [cn n]))).val) →
      Bm mβ Pβ β) :
    LC mγ Pγ (.node k (H ++ [c])) (fun n => .node k (H ++ [cn n])) := by
  have hA : H ++ [c] ≠ [] := by simp
  have hlA : ((H ++ [c]).getLast hA).y = k + 1 := by simpa using hc
  have hAn : ∀ n, H ++ [cn n] ≠ [] := fun n => by simp
  have hlAn : ∀ n, ((H ++ [cn n]).getLast (hAn n)).y = k + 1 := fun n => by simpa using hcn n
  have hEp : ∀ n, IsPrincipal (· + ·) (trTm (.node k (H ++ [cn n]))).val :=
    fun n => val_isPrincipal (trTm_nfp _)
  have hE0 : ∀ n, 0 < (trTm (.node k (H ++ [cn n]))).val := fun n => val_pos (trTm_nfp _)
  have hEΩ : ∀ n, Om k < (trTm (.node k (H ++ [cn n]))).val :=
    fun n => (trTm_eps_isEps (hAn n) (hlAn n)).1
  have ha : trTm (.node k (H ++ [c])) = .th k (argOf k (H ++ [c])) := trTm_eps' hA hlA
  have hna : NFP (WP.th k (argOf k (H ++ [c]))) := nfp_trTm_eps hA hlA
  suffices H' : ∀ N, ∀ γ : List WP, WP.sizeS γ ≤ N → NFS γ →
      WP.valS γ < (trTm (.node k (H ++ [c]))).val → Bm mγ Pγ γ →
      ∃ n0, ∀ n ≥ n0, WP.valS γ < (trTm (.node k (H ++ [cn n]))).val from
    fun γ hγ hlt' hB' => H' _ γ le_rfl hγ hlt' hB'
  intro N
  induction N with
  | zero =>
    intro γ hsz hγ _ _
    cases γ with
    | nil => exact ⟨0, fun n _ => by simpa using hE0 n⟩
    | cons g γ' => exact absurd hsz (by simp; have := WP.size_pos g; omega)
  | succ N ih =>
    intro γ hsz hγ hlt' hB'
    cases γ with
    | nil => exact ⟨0, fun n _ => by simpa using hE0 n⟩
    | cons g γ' =>
      have hg := hγ.head
      suffices hsg : ∃ n0, ∀ n ≥ n0, g.val < (trTm (.node k (H ++ [cn n]))).val by
        obtain ⟨n0, h0⟩ := hsg
        exact ⟨n0, fun n hn => valS_lt_of_head hγ (hEp n) (hE0 n) (fun p hp => by
          rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hp
          rw [← hp]; exact h0 n hn)⟩
      have hgle : g.val < (trTm (.node k (H ++ [c]))).val := lt_of_le_of_lt le_valS_head hlt'
      have hgl : g.lvl ≤ k := by
        have := lvl_le_of_val_le hg (trTm_nfp _) hgle.le
        rwa [trTm_lvl] at this
      rcases hgl.lt_or_eq with hgl | hgl
      · exact ⟨0, fun n _ => lt_trans (val_lt_Om_of_lvl_lt hg hgl) (hEΩ n)⟩
      obtain ⟨k', β⟩ := g
      simp only [WP.lvl_th] at hgl
      subst hgl
      rw [ha] at hgle
      rcases (val_lt_val_iff hg hna).mp hgle with ⟨hβlt, hβs⟩ | ⟨s, hs, hgs⟩
      · have hBg : Bm mγ Pγ [WP.th k' β] := hB'.single_of_mem (by simp)
        have hsIH : ∀ s ∈ starS k' β, ∃ n0, ∀ n ≥ n0,
            s.val < (trTm (.node k' (H ++ [cn n]))).val := by
          intro s hs
          obtain ⟨hs1, -, hs3⟩ := starS_spec k' β hg.nfs s hs
          have hsz' : WP.sizeS [s] ≤ N := by
            simp only [WP.sizeS_cons, WP.sizeS_nil, add_zero, WP.size_th] at hsz ⊢
            omega
          obtain ⟨n0, h0⟩ := ih [s] hsz' (NFS.single hs1)
            (by rw [valS_single, ha]; exact hβs s hs)
            (Bm.star hmγ hs (Bm.arg (by simp; omega) hBg))
          exact ⟨n0, fun n hn => by simpa using h0 n hn⟩
        exact arg_step hPβ1 hPβo hc hcn hHl hlt hcase hrc hanc hLCX hg hβlt (hB β hg hBg hsIH)
          (eventually_forall _ hsIH)
      · exact ⟨0, fun n _ => lt_of_le_of_lt hgs (hwit n s hs)⟩

end Googology.Trans.PSS.TR
