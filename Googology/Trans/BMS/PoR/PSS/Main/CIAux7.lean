import Googology.Trans.BMS.PoR.PSS.Main.CIAux6

/-!
# CI, part 7: preparations for the induction

For a standard epsilon root `N = (0, H)` with `a = 𝒯(N)`:

* `a` is a level-`0` epsilon term above `1` (`aFacts`);
* the images of region terms and of their constants lie in `T¹_α` (`domA_trTm`, `domA_const`);
* `runStart_append`: the last run of `A ++ B` stays in `B` when no entry of `A` equals the last
  entry of `B` (used for **S-run**).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

set_option linter.unusedSectionVars false

theorem runStart_append {A B : List (List WP)} (hB : B ≠ [])
    (hA : ∀ x ∈ A, x ≠ B.getLast hB) : runStart (A ++ B) = A.length + runStart B := by
  unfold runStart
  rw [List.getLast?_append, List.getLast?_eq_some_getLast hB]
  simp only [Option.some_or]
  rw [List.reverse_append, List.dropWhile_append]
  have hAr : (A.reverse.dropWhile (fun d => d == B.getLast hB)) = A.reverse := by
    cases hr : A.reverse with
    | nil => rfl
    | cons x xs =>
      have hx : x ∈ A := by rw [← List.mem_reverse, hr]; simp
      rw [List.dropWhile_cons, if_neg (by simpa using hA x hx)]
  split_ifs with h
  · rw [hAr, List.length_reverse]
    have : (B.reverse.dropWhile (fun d => d == B.getLast hB)).length = 0 := by
      simpa using h
    rw [this]; simp
  · rw [List.length_append, List.length_reverse]; omega

section Prep

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

theorem aFacts :
    NFP (trTm (.node 0 H)) ∧ (trTm (.node 0 H)).lvl = 0 ∧ trTm (.node 0 H) ≠ TR.one ∧
      isEpsLevel (trTm (.node 0 H)) 0 = true ∧
      ω ^ (trTm (.node 0 H)).val = (trTm (.node 0 H)).val ∧ 1 < (trTm (.node 0 H)).val := by
  obtain ⟨-, hall, hT⟩ := trTm_root_eps hN he
  have hl : (H.getLast hne).y = 0 + 1 := by rw [hall _ (List.getLast_mem hne)]
  obtain ⟨-, h2, h3⟩ := deltaOf_spec hne hl
  have heps := trTm_eps_isEps hne hl
  refine ⟨trTm_nfp _, by rw [trTm_lvl]; rfl, ?_, ?_, heps.2, by simpa using heps.1⟩
  · rw [hT]; intro h; simp [TR.one] at h; exact h3 h.1
  · rw [hT]
    obtain ⟨q, r, hq⟩ := List.exists_cons_of_ne_nil h3
    rw [hq, List.cons_append]
    have := h2 q (by rw [hq]; simp)
    simp [isEpsLevel, this]

theorem domA_one : DomA (trTm (.node 0 H)) TR.one := by
  obtain ⟨-, -, -, -, -, h1⟩ := aFacts hN he hne
  refine ⟨nfp_one, fun z hz => ?_⟩
  rw [TR.one, starP_th] at hz; simp at hz; rw [hz, ← TR.one, val_one]; exact h1

theorem val_const_lt {c : Tm} (hc : Std c) (hcN : c < .node 0 H) :
    (trTm c).val < (trTm (.node 0 H)).val := by
  rw [val_trTm_root hc, val_trTm_root hN]; exact ordOf_single_lt hc hN hcN

theorem domA_const {c : Tm} (hc : Std c) (hcN : c < .node 0 H) : DomA (trTm (.node 0 H)) (trTm c) :=
  ⟨trTm_nfp c, fun z hz => lt_of_le_of_lt (val_le_of_mem_starP (trTm_nfp c) hz)
    (val_const_lt hN he hne hc hcN)⟩

theorem domA_trTm {s : Tm} (hs : IsRegT H hne s) : DomA (trTm (.node 0 H)) (trTm s) := by
  obtain ⟨-, -, -, -, hE, h1⟩ := aFacts hN he hne
  refine ⟨trTm_nfp s, b3 hE h1 s.size s le_rfl (regT_y hN he hne hs) (fun d hd => ?_)⟩
  obtain ⟨hd1, hd2⟩ := regT_cst hN he hne hs hd
  exact val_const_lt hN he hne hd1 hd2

theorem domA_child {s c : Tm} (hs : IsRegT H hne s) (hc : c ∈ s.cs) :
    DomA (trTm (.node 0 H)) (trTm c) := by
  rcases Nat.eq_zero_or_pos c.y with h0 | hpos
  · obtain ⟨h1, h2⟩ := regT_const hN he hne hs hc h0
    exact domA_const hN he hne h1 h2
  · exact domA_trTm hN he hne (regT_child hN he hne hs hc hpos)

theorem domA_logOmega {p : WP} (hp : DomA (trTm (.node 0 H)) p) :
    ∀ q ∈ logOmega p, DomA (trTm (.node 0 H)) q := by
  intro q hq
  obtain ⟨k, c⟩ := p
  simp only [logOmega, WP.lvl_th, WP.arg_th] at hq
  split_ifs at hq with h1 h2 h3
  · rw [List.mem_singleton.mp hq]; exact hp
  · rcases List.mem_append.mp hq with h | h
    · exact hp.of_mem h
    · rw [List.mem_singleton.mp h]; exact domA_one hN he hne
  · exact hp.of_mem hq
  · rcases mem_addS hq with h | h
    · rw [List.mem_singleton.mp h]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact domA_om (a := trTm (.node 0 H)) (aFacts hN he hne).1 (aFacts hN he hne).2.1 k'
    · exact hp.of_mem h

theorem domA_dOf {h : Tm} {k : ℕ} (hh : DomA (trTm (.node 0 H)) (trTm h)) :
    ∀ q ∈ dOf k h, DomA (trTm (.node 0 H)) q := fun q hq =>
  domA_logOmega hN he hne hh q ((List.takeWhile_sublist _).subset hq)

theorem domA_rhoOf {h : Tm} {k : ℕ} (hh : DomA (trTm (.node 0 H)) (trTm h)) :
    ∀ q ∈ rhoOf k h, DomA (trTm (.node 0 H)) q := fun q hq =>
  domA_logOmega hN he hne hh q ((List.dropWhile_sublist _).subset hq)

/-- `ω^ρ` of a part `ρ` of `T¹_α` is in `T¹_α`. -/
theorem domA_wOf {h : Tm} {k : ℕ} (hh : DomA (trTm (.node 0 H)) (trTm h)) :
    DomA (trTm (.node 0 H)) (wOf k h) := by
  obtain ⟨ha, h0, -, -, hE, h1⟩ := aFacts hN he hne
  have hAP : IsPrincipal (· + ·) (trTm (.node 0 H)).val := by
    rw [← hE]; exact isPrincipal_add_omega0_opow _
  have hρ := domA_rhoOf hN he hne hh (k := k)
  refine ⟨(wOf_spec k h).1, fun z hz => ?_⟩
  unfold wOf at hz
  rcases starP0_omegaExp hz with h' | h'
  · rw [h', (omegaExp_expLvl_spec (monOf_spec k h).2.2.1).2.2]
    have hlv : ∀ q ∈ rhoOf k h, q.lvl ≤ expLvl (rhoOf k h) :=
      fun q hq => by
        cases hr : rhoOf k h with
        | nil => rw [hr] at hq; simp at hq
        | cons q0 r =>
          have hn := (monOf_spec k h).2.2.1; rw [hr] at hn hq
          simpa [expLvl] using NFS.lvl_le_of_head hn le_rfl q hq
    rcases Nat.eq_zero_or_pos (expLvl (rhoOf k h)) with he0 | hepos
    · have hv : WP.valS (rhoOf k h) < (trTm (.node 0 H)).val := by
        refine valS_lt_of_forall hAP (lt_trans zero_lt_one h1) (fun q hq => ?_)
        have hq0 : q.lvl = 0 := by have := hlv q hq; omega
        refine (hρ q hq).2 q ?_
        obtain ⟨k', c'⟩ := q; simp only [WP.lvl_th] at hq0; subst hq0
        rw [starP_th]; simp
      calc ω ^ WP.valS (rhoOf k h) < ω ^ (trTm (.node 0 H)).val :=
            (opow_lt_opow_iff_right one_lt_omega0).mpr hv
        _ = _ := hE
    · exfalso
      have hl := (omegaExp_expLvl_spec (monOf_spec k h).2.2.1).2.1
      have hz0 := (starP_spec 0 _ (omegaExp_expLvl_spec (monOf_spec k h).2.2.1).1 z hz).2.1
      rw [h'] at hz0; omega
  · obtain ⟨q, hq, hzq⟩ := exists_of_mem_starS h'
    exact (hρ q hq).2 z hzq

end Prep

end Googology.Trans.PSS.Main
