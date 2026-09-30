import Googology.Trans.BMS.PoR.PSS.Main.CIAux9

/-!
# CI, part 10: epsilon terms of level `1` (the blob)

`ci_eps_one`: for an epsilon region term `s = (1, D_1 … D_n)`,
`jN(𝒯_1(s)) = 𝒯_0((0, A + Coll_A(D_1) + ⋯ + Coll_A(D_n)))`.  The last run of the blob contains
no element of `A` (**S-run**, `proof/PROOF-3.md` §13.2): its level `Δ^J` is below
`𝒯_1(s) ≤ D(W) ≤ D(H_i)` ([W07a] Lemma 7.2 (e) as `jN_lt_th`, Mono\*).  The prefix rule of `𝒯`
matches the cases of [W07a] Def 6.2 (`e_p = α` exactly when the run starts after `A`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

set_option linter.unusedSectionVars false

theorem take_append_len {α : Type*} (l₁ l₂ : List α) (i : ℕ) :
    (l₁ ++ l₂).take (l₁.length + i) = l₁ ++ l₂.take i := by
  rw [List.take_append]; simp

theorem drop_append_len {α : Type*} (l₁ l₂ : List α) (i : ℕ) :
    (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i := by
  rw [List.drop_append]; simp

/-- `jN(ϑ_1(Δ + η'))` for `Δ ≠ 0` of level `2` and `η'` of levels `≤ 1`. -/
theorem jN_one_split {a : WP} {Δ η : List WP} (hΔ : Δ ≠ []) (hΔl : ∀ q ∈ Δ, q.lvl = 2)
    (hηl : ∀ q ∈ η, q.lvl ≤ 1) :
    jN a (.th 1 (Δ ++ η)) = if (starS 1 Δ).isEmpty then .th 0 (Δ.map (jN a) ++ addS [a] (η.map (jN a)))
      else .th 0 ((Δ ++ η).map (jN a)) := by
  have hb : ¬ (Δ ++ η).isEmpty = true := by simp [hΔ]
  have htw : (Δ ++ η).takeWhile (fun q => decide (2 ≤ q.lvl)) = Δ := by
    rw [List.takeWhile_append_of_pos (fun q hq => by simp [hΔl q hq])]
    cases η with
    | nil => simp
    | cons q r => have := hηl q (by simp); simp [List.takeWhile_cons]; omega
  rw [jN_one, jNTop, if_neg hb, htw, if_neg (by simpa using hΔ), jNL_eq_map]
  have ht : (Δ ++ η).take Δ.length = Δ := by simp
  rw [ht, List.map_append, show Δ.length = (Δ.map (jN a)).length by simp, List.take_left,
    List.drop_left]

section EpsOne

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

theorem ci_eps_one {n : ℕ} {ch : List Tm} (ih : CIIH H hne n)
    (hs : (Tm.node 1 ch).size ≤ n + 1) (hR : IsRegT H hne (.node 1 ch))
    (hch : ch ≠ []) (hl : (ch.getLast hch).y = 1 + 1) :
    jN (trTm (.node 0 H)) (trTm (.node 1 ch)) = trTm (coll H (.node 1 ch)) := by
  obtain ⟨ha, h0, ha1, hae, hE, h1⟩ := aFacts hN he hne
  set a := trTm (.node 0 H) with ha_def
  have hv := regT_valid hN he hne hR
  have hIc := ihc hN he hne ih hs hR
  have hdom : ∀ c ∈ ch, DomA a (trTm c) := fun c hc => domA_child hN he hne hR hc
  have hall : ∀ c ∈ ch, c.y = 1 + 1 := hv.eps_all hch hl
  have hlv : ∀ c ∈ ch, (trTm c).lvl = 0 + 2 := fun c hc => by rw [trTm_lvl, hall c hc]
  have hd : ∀ c ∈ ch, dOf 0 (coll H c) = (dOf 1 c).map (jN a) :=
    fun c hc => dOf_coll hN he hne (hdom c hc) (hlv c hc) (hIc c hc)
  have hw : ∀ c ∈ ch, wOf 0 (coll H c) = jN a (wOf 1 c) :=
    fun c hc => wOf_coll hN he hne (hdom c hc) (hlv c hc) (hIc c hc)
  have hH1 : ∀ c ∈ H, c.y = 1 := fun c hc => y_of_eps_child hN he hc
  have hnd := addT_noDrop hN he hne hR rfl
  simp only [Tm.cs_node] at hnd
  rw [coll_regT hN he hne hR, if_pos rfl, hnd]
  simp only [show 1 - 1 = 0 by rfl]
  have hL : H ++ ch.map (coll H) ≠ [] := by simp [hne]
  have hne' : ch.map (coll H) ≠ [] := by simpa using hch
  have hlL : ((H ++ ch.map (coll H)).getLast hL).y = 0 + 1 := by
    rw [List.getLast_append_of_ne_nil hL hne', List.getLast_map, coll_y, hl]
  set L := H ++ ch.map (coll H) with hLdef
  -- the two terms
  obtain ⟨hΔn, hΔl, hΔne⟩ := deltaOf_spec hch hl
  obtain ⟨hη'n, hη'l⟩ := eta'Of_spec 1 ch
  rw [trTm_eps' hch hl, trTm_eps' hL hlL, argOf_eq hch hl, argOf_eq hL hlL,
    jN_one_split hΔne hΔl hη'l]
  set Δ := deltaOf 1 ch with hΔdef
  set J := jOf 1 ch with hJdef
  have hJlt : J < ch.length := by
    have := runStart_lt (ds := ch.map (dOf 1)) (by simpa using hch)
    simpa [hJdef, jOf] using this
  have hΔD : ∀ q ∈ Δ, DomA a q := by
    intro q hq
    have : Δ = dOf 1 (ch.getLast hch) := by
      rw [hΔdef, deltaOf, List.getLast?_eq_some_getLast hch]; rfl
    rw [this] at hq
    exact domA_dOf hN he hne (hdom _ (List.getLast_mem hch)) q hq
  -- `Δ` of the blob
  have hlast : L.getLast hL = coll H (ch.getLast hch) := by
    show (H ++ ch.map (coll H)).getLast hL = _
    rw [List.getLast_append_of_ne_nil hL hne', List.getLast_map]
  have hdL : deltaOf 0 L = Δ.map (jN a) := by
    unfold deltaOf
    rw [List.getLast?_eq_some_getLast hL]
    simp only [Option.map_some, Option.getD_some]
    rw [hlast, hd _ (List.getLast_mem hch), hΔdef, deltaOf, List.getLast?_eq_some_getLast hch]
    rfl
  -- **S-run**
  have hsrun : ∀ x ∈ H, dOf 0 x ≠ Δ.map (jN a) := by
    intro x hx hxe
    have hTs : trTm (.node 1 ch) = .th 1 (argOf 1 ch) := trTm_eps' hch hl
    have hsn : NFP (trTm (.node 1 ch)) := trTm_nfp _
    -- `Δ^J < 𝒯_1(s)`
    have h1' : WP.valS (Δ.map (jN a)) < (trTm (.node 1 ch)).val := by
      refine valS_lt_of_forall (val_isPrincipal hsn) (val_pos hsn) (fun z hz => ?_)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      rw [hTs]
      rw [hTs] at hsn
      refine jN_lt_th ha h0 q.size q le_rfl (hΔD q hq) 1 le_rfl (hΔl q hq) _ hsn ?_
      rw [(argOf_spec hch hl).2.2]
      exact le_trans (val_le_valS_of_mem hq) le_self_add
    -- `𝒯_1(s) ≤ D(W) ≤ D(x)`
    have hW : H.getLast hne ∈ H := List.getLast_mem hne
    have hvW : Valid (H.getLast hne) := valid_of_tgood (tgood_W hN he hne)
    have hvx : Valid x := valid_of_tgood (tgood_child hN (by simpa using hx))
    have h2 : (trTm (.node 1 ch)).val ≤ (trTm (H.getLast hne)).val :=
      mono_le hv hvW (regT_le_W hN he hne hR rfl)
    have h3 : (trTm (H.getLast hne)).val ≤ (trTm x).val :=
      mono_le hvW hvx (getLast_le_of_desc (desc_cs_of_std hN) hne x (by simpa using hx))
    have hds := (d_rho_mono (k := 0) h2).1
    have hdx := (d_rho_mono (k := 0) h3).1
    have hdsv : WP.valS (dOf 0 (.node 1 ch)) = (trTm (.node 1 ch)).val := by
      have hepsl : isEpsLevel (trTm (.node 1 ch)) 1 = true := by
        rw [hTs, argOf_eq hch hl]
        obtain ⟨q, r, hq⟩ := List.exists_cons_of_ne_nil hΔne
        rw [← hΔdef, hq, List.cons_append]
        have := hΔl q (by rw [hq]; simp)
        simp [isEpsLevel, this]
      unfold dOf monOf
      have hlo : logOmega (trTm (.node 1 ch)) = [trTm (.node 1 ch)] := by
        unfold logOmega; rw [if_pos (by rw [trTm_lvl]; exact hepsl)]
      rw [hlo]
      simp [splitLevel, trTm_lvl]
    have := lt_of_lt_of_le h1' (le_trans (hdsv ▸ hds) hdx)
    rw [hxe] at this
    exact lt_irrefl _ this
  have hB : (ch.map (dOf 1)).map (fun d => d.map (jN a)) ≠ [] := by simpa using hch
  have hjL : jOf 0 L = H.length + J := by
    unfold jOf
    rw [hLdef, List.map_append, List.map_map]
    rw [show (ch.map (dOf 0 ∘ coll H)) = (ch.map (dOf 1)).map (fun d => d.map (jN a))
      from by rw [List.map_map]; exact List.map_congr_left (fun c hc => hd c hc)]
    rw [runStart_append hB (fun x hx => ?_), List.length_map]
    · congr 1
      refine runStart_jN ha h0 (fun d hd' p hp => ?_)
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd'
      exact domA_dOf hN he hne (hdom c hc) p hp
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [List.getLast_map, List.getLast_map]
      have : dOf 1 (ch.getLast hch) = Δ := by
        rw [hΔdef, deltaOf, List.getLast?_eq_some_getLast hch]; rfl
      rw [this]
      exact hsrun y hy
  -- `c`, `η`, `e_p` of the blob
  have hcL : cOf 0 L = (cOf 1 ch).map (jN a) := by
    unfold cOf
    rw [hjL, hLdef, drop_append_len, ← List.map_drop, List.map_map, ← hJdef]
    rw [List.map_congr_left (fun c hc => by
      show [wOf 0 (coll H c)] = [jN a (wOf 1 c)]
      rw [hw c (List.mem_of_mem_drop hc)])]
    rw [show ((ch.drop J).map fun c => [jN a (wOf 1 c)]) =
        ((ch.drop J).map fun c => [wOf 1 c]).map (List.map (jN a)) by rw [List.map_map]; rfl]
    refine addAll_jN ha h0 (fun x hx p hp => ?_)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hp]
    exact domA_wOf hN he hne (hdom c (List.mem_of_mem_drop hc))
  have hηL : etaOf 0 L = (etaOf 1 ch).map (jN a) := by
    unfold etaOf
    rw [hcL, minusOnePlus_jN ha h0 (domA_cOf hN he hne hdom) ha1]
  have hRj := (by simpa using regT_take hN he hne hR J :
    IsRegT H hne (.node 1 (ch.take J)))
  have hepL : epOf 0 L = jN a (epOf 1 ch) := by
    unfold epOf
    rw [hjL, hLdef, take_append_len, ← hJdef, iht hN he hne ih hs hR hJlt]
    have hnd' := addT_noDrop hN he hne hRj rfl
    simp only [Tm.cs_node] at hnd'
    rw [coll_regT hN he hne hRj, if_pos rfl, hnd', List.map_take]
  have hepD : DomA a (epOf 1 ch) := domA_trTm hN he hne hRj
  have hepG := g1 ha h0 hepD
  have hepl : (epOf 1 ch).lvl = 1 := by rw [epOf, trTm_lvl]; rfl
  have hαe : a.val ≤ (jN a (epOf 1 ch)).val := hepG.2.1 hepl
  -- `insOf` of the blob
  have hinsL : insOf 0 L ↔ ∀ q ∈ starS 0 (Δ.map (jN a)), q.val < (jN a (epOf 1 ch)).val := by
    unfold insOf
    rw [hjL, hdL, hepL]
    exact ⟨fun h => h.2, fun h => ⟨by have := List.length_pos_of_ne_nil hne; omega, h⟩⟩
  have hη'L : eta'Of 0 L = if insOf 0 L then addS [jN a (epOf 1 ch)] ((etaOf 1 ch).map (jN a))
      else (etaOf 1 ch).map (jN a) := by
    unfold eta'Of; rw [hepL, hηL]
  have hηD := domA_etaOf hN he hne hdom (k := 1)
  rw [hdL, hη'L]
  congr 1
  by_cases hS : (starS 1 Δ).isEmpty = true
  · rw [if_pos hS]
    have hS' : starS 1 Δ = [] := by simpa using hS
    have hins0 : insOf 0 L := by
      rw [hinsL, starS0_map_of_no1 h0 Δ hS']
      intro q hq
      obtain ⟨d, hd', hqd⟩ := exists_of_mem_starS hq
      exact lt_of_lt_of_le ((hΔD d hd').2 q hqd) hαe
    rw [if_pos hins0]
    congr 1
    unfold eta'Of
    by_cases hJ0 : J = 0
    · have hins1 : ¬ insOf 1 ch := by unfold insOf; rw [← hJdef, hJ0]; simp
      rw [if_neg hins1]
      have : epOf 1 ch = .th 1 [] := by rw [epOf, ← hJdef, hJ0, List.take_zero, trTm_leaf]
      rw [this, jN_one_nil]
    · have hins1 : insOf 1 ch := by
        unfold insOf; rw [← hJdef, ← hΔdef, hS']; exact ⟨Nat.pos_of_ne_zero hJ0, by simp⟩
      rw [if_pos hins1, ← addS_jN ha h0 (by simpa using hepD) hηD]
      simp only [List.map_cons, List.map_nil]
      -- `α` is absorbed by `jN(e_p) > α`
      have hne0 : epOf 1 ch ≠ .th 1 [] := by
        intro h
        have h1' : (Tm.node 1 ([] : List Tm)) < .node 1 (ch.take J) :=
          (Tm.lt_iff_cs_lt (s := Tm.node 1 []) (t := Tm.node 1 (ch.take J)) rfl).mpr
            (by
              obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil
                (show ch.take J ≠ [] by simp [hch]; omega)
              rw [hc]; exact List.nil_lt_cons _ _)
        have hv0 : Valid (.node 1 ([] : List Tm)) := by
          have := regT_valid hN he hne (by simpa using regT_take hN he hne hR 0 :
            IsRegT H hne (.node 1 (ch.take 0)))
          simpa using this
        have := mono hv0 (regT_valid hN he hne hRj) h1'
        rw [epOf, ← hJdef] at h
        rw [h, trTm_leaf] at this
        exact lt_irrefl _ this
      have hαlt : a.val < (jN a (epOf 1 ch)).val := hepG.2.2 hepl hne0
      have hXn : ∀ z ∈ addS [jN a (epOf 1 ch)] ((etaOf 1 ch).map (jN a)), NFP z := by
        intro z hz
        rcases mem_addS hz with h | h
        · rw [List.mem_singleton.mp h]; exact nfp_jN ha h0 hepD
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h; exact nfp_jN ha h0 (hηD q hq)
      congr 1
      refine addS_single_absorb ha h0 (by
          cases hη : (etaOf 1 ch).map (jN a) <;> simp [addS]) hXn (fun z hz => ?_)
      have := head_addS_single ha h0 (nfp_jN ha h0 hepD)
        (L := (etaOf 1 ch).map (jN a))
        (fun z hz => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz; exact nfp_jN ha h0 (hηD q hq))
        (fun z _ => le_or_gt _ _) z hz
      exact lt_of_lt_of_le hαlt this
  · rw [if_neg hS, List.map_append]
    congr 1
    obtain ⟨y, hy⟩ : ∃ y, y ∈ starS 1 Δ := by
      cases h : starS 1 Δ with
      | nil => rw [h] at hS; simp at hS
      | cons y _ => exact ⟨y, by simp⟩
    obtain ⟨dy, hdy, hydy⟩ := exists_of_mem_starS hy
    have hyD : DomA a y := (hΔD dy hdy).of_star hydy
    have hyl : y.lvl = 1 := (starS_spec 1 Δ hΔn y hy).2.1
    have hyJ : jN a y ∈ starS 0 (Δ.map (jN a)) := jN_mem_starS0_map h0 hy
    unfold eta'Of
    by_cases hJ0 : J = 0
    · have hins1 : ¬ insOf 1 ch := by unfold insOf; rw [← hJdef, hJ0]; simp
      have : epOf 1 ch = .th 1 [] := by rw [epOf, ← hJdef, hJ0, List.take_zero, trTm_leaf]
      have hins0 : ¬ insOf 0 L := by
        rw [hinsL, this, jN_one_nil]
        intro h
        exact absurd (h _ hyJ) (not_lt.mpr ((g1 ha h0 hyD).2.1 hyl))
      rw [if_neg hins1, if_neg hins0]
    · have hiff : insOf 0 L ↔ insOf 1 ch := by
        rw [hinsL]
        unfold insOf
        rw [← hJdef, ← hΔdef]
        constructor
        · intro h
          refine ⟨Nat.pos_of_ne_zero hJ0, fun q hq => ?_⟩
          obtain ⟨d, hd', hqd⟩ := exists_of_mem_starS hq
          exact (jN_lt_iff ha h0 ((hΔD d hd').of_star hqd) hepD).mp
            (h _ (jN_mem_starS0_map h0 hq))
        · intro h z hz
          obtain ⟨w, hw', hzw⟩ := exists_of_mem_starS hz
          obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hw'
          have hne0 : a.val < (jN a (epOf 1 ch)).val := by
            refine lt_of_le_of_lt ((g1 ha h0 hyD).2.1 hyl) ?_
            exact jN_lt ha h0 hyD hepD (h.2 y hy)
          exact starP0_jN_lt h0 ha hne0 d (hΔD d hd').2 (fun y' hy' =>
            jN_lt ha h0 ((hΔD d hd').of_star hy') hepD (h.2 y' (mem_starS_of_mem hd' hy'))) z hzw
      by_cases hi : insOf 1 ch
      · rw [if_pos hi, if_pos (hiff.mpr hi), ← addS_jN ha h0 (by simpa using hepD) hηD]
        simp
      · rw [if_neg hi, if_neg (fun h => hi (hiff.mp h))]

end EpsOne

end Googology.Trans.PSS.Main
