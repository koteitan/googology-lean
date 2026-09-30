import Googology.Trans.PSS.Main.CIAux3

/-!
# CI, part 4: more facts on `jN`

* `jN_lt_th` ([W07a] Lemma 7.2 (e), `ι(ξ) < ϑ(ξ)`): for `p` of level `j + 1 ≥ 2` and a term
  `ϑ_j(X)` with `p ≤ X`, `jN(p) < ϑ_j(X)`.
* `omegaExp_expLvl_jN`: `jN` commutes with `ω^ρ` formed at the level of `ρ`.
* `starS0_map_of_no1`: without visible `ϑ_1`-subterms, `jN` keeps the `ϑ_0`-subterms.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal

set_option linter.unusedSectionVars false

theorem starS0_map_of_no1 {a : WP} (h0 : a.lvl = 0) :
    ∀ x : List WP, starS 1 x = [] → starS 0 (x.map (jN a)) = starS 0 x := by
  have key : ∀ p : WP, starP 1 p = [] → starP 0 (jN a p) = starP 0 p := by
    intro p
    induction p using WP.ind with
    | h k c ih =>
      intro hp
      have hL : ∀ l : List WP, (∀ q ∈ l, q ∈ c) → starS 1 l = [] →
          starS 0 (l.map (jN a)) = starS 0 l := by
        intro l hl hl1
        induction l with
        | nil => simp
        | cons q l ihl =>
          rw [starS_cons, List.append_eq_nil_iff] at hl1
          rw [List.map_cons, starS_cons, starS_cons, ih q (hl q (by simp)) hl1.1,
            ihl (fun r hr => hl r (by simp [hr])) hl1.2]
      rcases k with _ | _ | k
      · rw [jN_zero]
      · rw [starP_th] at hp; simp at hp
      · rw [starP_th, if_neg (by omega), if_neg (by omega)] at hp
        rw [jN_add_two, jNL_eq_map, starP_th, starP_th, if_neg (by omega), if_neg (by omega),
          if_neg (by omega), if_neg (by omega)]
        exact hL c (fun q hq => hq) hp
  intro x hx
  induction x with
  | nil => simp
  | cons q l ih =>
    rw [starS_cons, List.append_eq_nil_iff] at hx
    rw [List.map_cons, starS_cons, starS_cons, key q hx.1, ih hx.2]

section More

variable {a : WP} (ha : NFP a) (h0 : a.lvl = 0)
include ha h0

/-- **`ι(ξ) < ϑ(ξ)`** ([W07a] Lemma 7.2 (e), Cor 7.3): for `p` of level `j + 1 ≥ 2` in `T¹_α`
and `ϑ_j(X)` of `T¹` with `p ≤ X`: `jN(p) < ϑ_j(X)`. -/
theorem jN_lt_th : ∀ (n : ℕ) (p : WP), p.size ≤ n → DomA a p → ∀ j : ℕ, 1 ≤ j → p.lvl = j + 1 →
    ∀ X : List WP, NFP (.th j X) → p.val ≤ WP.valS X → (jN a p).val < (WP.th j X).val := by
  intro n
  induction n with
  | zero => intro p hp; exact absurd hp (by have := WP.size_pos p; omega)
  | succ n ih =>
    intro p hps hp j hj hpl X hX hpX
    obtain ⟨k, b⟩ := p
    simp only [WP.lvl_th] at hpl
    subst hpl
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hjN := nfp_jN ha h0 hp
    rw [jN_add_two, jNL_eq_map] at hjN ⊢
    have hsb : WP.sizeS b ≤ n := by simp at hps; omega
    refine (val_lt_val_iff hjN hX).mpr (Or.inl ⟨?_, fun z hz => ?_⟩)
    · -- `b^J < p ≤ X`
      refine lt_of_lt_of_le ?_ hpX
      have hpP : IsPrincipal (· + ·) (WP.th (j' + 1 + 1) b).val := val_isPrincipal hp.1
      refine valS_lt_of_forall hpP (val_pos hp.1) (fun z hz => ?_)
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      have hvD : DomA a v := hp.of_mem hv
      have hvl : v.lvl ≤ j' + 3 := hp.1.lvl_le hv
      rcases Nat.lt_or_ge v.lvl (j' + 3) with hlt | hge
      · refine val_lt_of_lvl_lt (nfp_jN ha h0 hvD) hp.1 ?_
        rw [jN_lvl h0]; simp; omega
      · exact ih v (le_trans (WP.size_le_sizeS hv) hsb) hvD (j' + 2) (by omega) (by omega) b
          hp.1 (val_le_valS_of_mem hv)
    · -- the visible `ϑ_{j'+1}`-subterms of `b^J`
      rw [starS_jN h0 (m := j' + 1) (by omega)] at hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hyP : y ∈ starP (j' + 2) (.th (j' + 1 + 1) b) := by rw [starP_th]; simp [hy]
      have hys := starS_spec (j' + 2) b hp.1.nfs y hy
      exact ih y (by omega) (hp.of_star hyP) (j' + 1) (by omega) hys.2.1 X hX
        (le_trans (star_lt_val hp.1 y hy).le hpX)

/-- `jN` commutes with `ω^ρ` at the level of `ρ`. -/
theorem omegaExp_expLvl_jN {ρ : List WP} (hρ : NFS ρ) (hD : ∀ q ∈ ρ, DomA a q)
    (ha1 : a ≠ TR.one) (hae : isEpsLevel a 0 = true) :
    jN a (omegaExp ρ (expLvl ρ)) = omegaExp (ρ.map (jN a)) (expLvl (ρ.map (jN a))) := by
  cases ρ with
  | nil => simp [expLvl, omegaExp, jN_zero]
  | cons q r =>
    have hall : ∀ z ∈ q :: r, z.lvl ≤ q.lvl := NFS.lvl_le_of_head hρ le_rfl
    simp only [expLvl, List.map_cons, jN_lvl h0]
    rcases hq : q.lvl with _ | _ | e
    · -- level `0`: `jN` is the identity
      have hid : ∀ z ∈ q :: r, jN a z = z := fun z hz => by
        have := hall z hz; rw [hq] at this
        obtain ⟨k, c⟩ := z; simp only [WP.lvl_th] at this
        have : k = 0 := by omega
        subst this; rw [jN_zero]
      have hmap : (q :: r).map (jN a) = q :: r := by
        conv_rhs => rw [← List.map_id (q :: r)]
        exact List.map_congr_left hid
      rw [List.map_cons] at hmap
      rw [hmap]
      have hl0 := (omegaExp_spec hρ (m := 0) (fun z hz => by have := hall z hz; omega)
        (by omega)).2.1
      rw [eq_th_of_lvl hl0, jN_zero]
    · simp only [zero_add, Nat.sub_self]
      have := omegaExp_jN_one ha h0 hD hρ (fun z hz => by have := hall z hz; omega)
        (Om_le_val_of_le_lvl hρ.head (by omega) |>.trans le_valS_head) ha1 hae
      rw [List.map_cons] at this
      exact this
    · simp only [show e + 1 + 1 - 1 = e + 1 by omega]
      have := omegaExp_jN_high ha h0 e hD ha1
      rw [List.map_cons] at this
      exact this

theorem addS_single_absorb {L : List WP} (hL : L ≠ []) (hLn : ∀ z ∈ L, NFP z)
    (hhead : ∀ z ∈ L.head?, a.val < z.val) : addS [a] L = L := by
  obtain ⟨y0, ys, rfl⟩ := List.exists_cons_of_ne_nil hL
  exact addS_single_lt ha h0 ((cmpP_lt_iff ha (hLn y0 (by simp))).mpr (hhead y0 (by simp)))

theorem head_addS_single {x : WP} (hx : NFP x) {L : List WP} (hLn : ∀ z ∈ L, NFP z)
    (hLx : ∀ z ∈ L.head?, z.val ≤ x.val ∨ x.val < z.val) :
    ∀ z ∈ (addS [x] L).head?, x.val ≤ z.val := by
  intro z hz
  cases L with
  | nil => simp [addS] at hz; rw [hz]
  | cons y0 ys =>
    by_cases h : cmpP x y0 = .lt
    · have := (cmpP_lt_iff hx (hLn y0 (by simp))).mp h
      simp [addS, h] at hz; rw [← hz]; exact this.le
    · simp [addS, h] at hz; rw [hz]

end More

end Googology.Trans.PSS.Main
