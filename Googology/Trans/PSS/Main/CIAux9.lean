import Googology.Trans.PSS.Main.CIAux8

/-!
# CI, part 9: epsilon terms of level `≥ 2`

`ci_eps_high`: for an epsilon region term `s` of level `k + 2`, `jN(𝒯(s)) = 𝒯(Coll_A(s))`:
the monomials of the children, the runs, `c`, `η`, `e_p` and the test "`e_p > Δ^*`" all
commute with `jN` (`proof/PROOF-3.md` §13.2, case `m ≥ 2`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

set_option linter.unusedSectionVars false

section Eps

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

/-- The monomials of `Coll_A(h)`: `jN` of those of `h`. -/
theorem monOf_coll {j : ℕ} {h h' : Tm} (hD : DomA (trTm (.node 0 H)) (trTm h))
    (hl : (trTm h).lvl = j + 2) (heq : jN (trTm (.node 0 H)) (trTm h) = trTm h') :
    monOf j h' = ((monOf (j + 1) h).1.map (jN (trTm (.node 0 H))),
      (monOf (j + 1) h).2.map (jN (trTm (.node 0 H)))) := by
  obtain ⟨ha, h0, ha1, -⟩ := aFacts hN he hne
  unfold monOf
  rw [← heq]
  obtain ⟨c, hce⟩ : ∃ c, trTm h = .th (j + 2) c := ⟨(trTm h).arg, by rw [← hl]; exact (WP.eta _).symm⟩
  have hc : ∀ q ∈ c, DomA (trTm (.node 0 H)) q := fun q hq => hD.of_mem (by rw [hce]; exact hq)
  rw [hce, logOmega_jN_high ha h0 j hc ha1, splitLevel_jN ha h0 (m := j + 1) (by omega)]

theorem dOf_coll {j : ℕ} {h h' : Tm} (hD : DomA (trTm (.node 0 H)) (trTm h))
    (hl : (trTm h).lvl = j + 2) (heq : jN (trTm (.node 0 H)) (trTm h) = trTm h') :
    dOf j h' = (dOf (j + 1) h).map (jN (trTm (.node 0 H))) := by
  unfold dOf; rw [monOf_coll hN he hne hD hl heq]

theorem rhoOf_coll {j : ℕ} {h h' : Tm} (hD : DomA (trTm (.node 0 H)) (trTm h))
    (hl : (trTm h).lvl = j + 2) (heq : jN (trTm (.node 0 H)) (trTm h) = trTm h') :
    rhoOf j h' = (rhoOf (j + 1) h).map (jN (trTm (.node 0 H))) := by
  unfold rhoOf; rw [monOf_coll hN he hne hD hl heq]

theorem wOf_coll {j : ℕ} {h h' : Tm} (hD : DomA (trTm (.node 0 H)) (trTm h))
    (hl : (trTm h).lvl = j + 2) (heq : jN (trTm (.node 0 H)) (trTm h) = trTm h') :
    wOf j h' = jN (trTm (.node 0 H)) (wOf (j + 1) h) := by
  obtain ⟨ha, h0, ha1, hae, -⟩ := aFacts hN he hne
  unfold wOf
  rw [rhoOf_coll hN he hne hD hl heq, omegaExp_expLvl_jN ha h0 (monOf_spec (j + 1) h).2.2.1
    (domA_rhoOf hN he hne hD) ha1 hae]

theorem domA_cOf {k : ℕ} {ch : List Tm} (hD : ∀ h ∈ ch, DomA (trTm (.node 0 H)) (trTm h)) :
    ∀ q ∈ cOf k ch, DomA (trTm (.node 0 H)) q := by
  intro q hq
  obtain ⟨x, hx, hqx⟩ := mem_addAll hq
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_singleton.mp hqx]
  exact domA_wOf hN he hne (hD h (List.mem_of_mem_drop hh))

theorem domA_etaOf {k : ℕ} {ch : List Tm} (hD : ∀ h ∈ ch, DomA (trTm (.node 0 H)) (trTm h)) :
    ∀ q ∈ etaOf k ch, DomA (trTm (.node 0 H)) q := fun q hq =>
  domA_cOf hN he hne hD q ((minusOnePlus_sublist _).subset hq)

theorem ci_eps_high {n k : ℕ} {ch : List Tm} (ih : CIIH H hne n)
    (hs : (Tm.node (k + 2) ch).size ≤ n + 1) (hR : IsRegT H hne (.node (k + 2) ch))
    (hch : ch ≠ []) (hl : (ch.getLast hch).y = k + 2 + 1) :
    jN (trTm (.node 0 H)) (trTm (.node (k + 2) ch)) = trTm (coll H (.node (k + 2) ch)) := by
  obtain ⟨ha, h0, ha1, hae, hE, h1⟩ := aFacts hN he hne
  set a := trTm (.node 0 H) with ha_def
  have hv := regT_valid hN he hne hR
  have hIc := ihc hN he hne ih hs hR
  have hdom : ∀ c ∈ ch, DomA a (trTm c) := fun c hc => domA_child hN he hne hR hc
  have hall : ∀ c ∈ ch, c.y = k + 2 + 1 := hv.eps_all hch hl
  have hlv : ∀ c ∈ ch, (trTm c).lvl = (k + 1) + 2 := fun c hc => by rw [trTm_lvl, hall c hc]
  have hd : ∀ c ∈ ch, dOf (k + 1) (coll H c) = (dOf (k + 2) c).map (jN a) :=
    fun c hc => dOf_coll hN he hne (hdom c hc) (hlv c hc) (hIc c hc)
  have hw : ∀ c ∈ ch, wOf (k + 1) (coll H c) = jN a (wOf (k + 2) c) :=
    fun c hc => wOf_coll hN he hne (hdom c hc) (hlv c hc) (hIc c hc)
  rw [coll_regT hN he hne hR, if_neg (by omega)]
  simp only [show k + 2 - 1 = k + 1 by omega]
  have hL : ch.map (coll H) ≠ [] := by simpa using hch
  have hlL : ((ch.map (coll H)).getLast hL).y = k + 1 + 1 := by
    rw [List.getLast_map, coll_y, hl]; omega
  set L := ch.map (coll H) with hLdef
  rw [trTm_eps' hch hl, trTm_eps' hL hlL, jN_add_two, jNL_eq_map]
  congr 1
  -- the runs
  have hj : jOf (k + 1) L = jOf (k + 2) ch := by
    unfold jOf
    rw [hLdef, List.map_map]
    rw [show (ch.map (dOf (k + 1) ∘ coll H)) = (ch.map (dOf (k + 2))).map (fun d => d.map (jN a))
      from by rw [List.map_map]; exact List.map_congr_left (fun c hc => hd c hc)]
    refine runStart_jN ha h0 (fun d hd' p hp => ?_)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd'
    exact domA_dOf hN he hne (hdom c hc) p hp
  have hΔ : deltaOf (k + 1) L = (deltaOf (k + 2) ch).map (jN a) := by
    unfold deltaOf
    rw [hLdef, List.getLast?_map, List.getLast?_eq_some_getLast hch]
    simp only [Option.map_some, Option.getD_some]
    exact hd _ (List.getLast_mem hch)
  have hjlt : jOf (k + 2) ch < ch.length := by
    have := runStart_lt (ds := ch.map (dOf (k + 2))) (by simpa using hch)
    simpa [jOf] using this
  have hc : cOf (k + 1) L = (cOf (k + 2) ch).map (jN a) := by
    unfold cOf
    rw [hj, hLdef, ← List.map_drop, List.map_map]
    rw [List.map_congr_left (fun c hc => by
      show [wOf (k + 1) (coll H c)] = [jN a (wOf (k + 2) c)]
      rw [hw c (List.mem_of_mem_drop hc)])]
    rw [show ((ch.drop (jOf (k + 2) ch)).map fun c => [jN a (wOf (k + 2) c)]) =
        ((ch.drop (jOf (k + 2) ch)).map fun c => [wOf (k + 2) c]).map (List.map (jN a)) by
      rw [List.map_map]; rfl]
    refine addAll_jN ha h0 (fun x hx p hp => ?_)
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hp]
    exact domA_wOf hN he hne (hdom c (List.mem_of_mem_drop hc))
  have hη : etaOf (k + 1) L = (etaOf (k + 2) ch).map (jN a) := by
    unfold etaOf
    rw [hc, minusOnePlus_jN ha h0 (domA_cOf hN he hne hdom) ha1]
  have hRj := (by simpa using regT_take hN he hne hR (jOf (k + 2) ch) :
    IsRegT H hne (.node (k + 2) (ch.take (jOf (k + 2) ch))))
  have hep : epOf (k + 1) L = jN a (epOf (k + 2) ch) := by
    unfold epOf
    rw [hj, iht hN he hne ih hs hR hjlt, coll_regT hN he hne hRj, if_neg (by omega), hLdef,
      List.map_take]
    rfl
  have hepD : DomA a (epOf (k + 2) ch) := domA_trTm hN he hne hRj
  have hΔD : ∀ q ∈ deltaOf (k + 2) ch, DomA a q := by
    intro q hq
    have : deltaOf (k + 2) ch = dOf (k + 2) (ch.getLast hch) := by
      rw [deltaOf, List.getLast?_eq_some_getLast hch]; rfl
    rw [this] at hq
    exact domA_dOf hN he hne (hdom _ (List.getLast_mem hch)) q hq
  have hins : insOf (k + 1) L ↔ insOf (k + 2) ch := by
    unfold insOf
    rw [hj, hΔ, hep, starS_jN h0 (m := k + 1) (by omega)]
    refine and_congr_right (fun _ => ?_)
    constructor
    · intro h q hq
      obtain ⟨d, hd', hqd⟩ := exists_of_mem_starS hq
      exact (jN_lt_iff ha h0 ((hΔD d hd').of_star hqd) hepD).mp (h _ (List.mem_map_of_mem hq))
    · intro h z hz
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
      obtain ⟨d, hd', hqd⟩ := exists_of_mem_starS hq
      exact (jN_lt_iff ha h0 ((hΔD d hd').of_star hqd) hepD).mpr (h q hq)
  have hη' : eta'Of (k + 1) L = (eta'Of (k + 2) ch).map (jN a) := by
    unfold eta'Of
    by_cases hi : insOf (k + 2) ch
    · rw [if_pos (hins.mpr hi), if_pos hi, hep, hη]
      have := addS_jN ha h0 (x := [epOf (k + 2) ch]) (y := etaOf (k + 2) ch)
        (by simpa using hepD) (domA_etaOf hN he hne hdom)
      simpa using this
    · rw [if_neg (fun h => hi (hins.mp h)), if_neg hi, hη]
  unfold argOf
  rw [hΔ, hη']
  refine (addS_jN ha h0 hΔD (fun q hq => ?_)).symm
  unfold eta'Of at hq
  split_ifs at hq
  · rcases mem_addS hq with h | h
    · rw [List.mem_singleton.mp h]; exact hepD
    · exact domA_etaOf hN he hne hdom q h
  · exact domA_etaOf hN he hne hdom q hq

end Eps

end Googology.Trans.PSS.Main
