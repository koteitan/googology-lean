import Googology.Trans.PoR.InaccPsi.R2.BrLow2

/-!
# Lower bound, part 3: the map `E` and the bounds of its `K`-sets

The map `E` of the paper proof of Theorem LOW-0 (`τ = 1`), from InaccPsi terms to terms of `T̄¹`:
* `E(0) = 0`, `E(a + b)` = the normal sum of `E(a)` and `E(b)`;
* `E(Ωₖ) = ϑ̄ₖ(0)`;
* `E(φ(a, b)) = ϑ̄ₖ(ϑ̄_{k+1}(E a) + E b)` for `φ(a, b)` of level `k`;
* `E(ψ_{Ω_{k+1}}(a)) = ϑ̄ₖ(Pₖ + F(E a))`, `Pₖ = ϑ̄_{k+1}(Ω_{k+1})`, `F(x) = ϑ̄_{m+1}(Ω_{m+1}·2 + x)`
  (`m` the level of `x`; `F(0) = 0`).

`DI S t` collects the invariants proved by induction (normal form, level, head, sums), and
`QB` (Lemma Q: the `K*_{k+1}`-elements of `E(a)` are below `F(E a)` for a normal `ψ_{Ω_{k+1}}(a)`) and
`KB` (the level-`k` parts of `E(a)` are below a given bound) are the two bounds of the paper proof,
stated with the order (Lemma M) on smaller terms as a hypothesis.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable (S : InaccSeq.{0})

/-- **The map `E`.** -/
noncomputable def E : Term → Tm
  | .zero => par 0
  | .add a b => plus 1 (E a) (E b)
  | .phi a b => th (lvl (Term.val S (.phi a b)))
      (plus 1 (th (lvl (Term.val S (.phi a b)) + 1) (E a)) (E b))
  | .om b => Omk (natOf (Term.val S b))
  | .psiS s a => th (natOf (Term.val S s)) (plus 1 (Pk (natOf (Term.val S s))) (Fc (E a)))
  | _ => par 0

/-- The invariants of `E` on a term. -/
structure DI (t : Term) : Prop where
  nf : NF 1 (E S t)
  lt : ev 1 (E S t) < OmT 1 (lvl (Term.val S t) + 1)
  ne : Term.val S t ≠ 0 → ev 1 (E S t) ≠ 0
  prin : t.isPrin = true → OmT 1 (lvl (Term.val S t)) ≤ ev 1 (E S t) ∧
    ∃ e, E S t = th (lvl (Term.val S t)) e
  hd : t ≠ .zero → hd 1 (E S t) = ev 1 (E S (Term.head t))
  add : ∀ a b, t = .add a b → E S t = Tm.add (E S a) (E S b)
  lv : lvl (ev 1 (E S t)) = lvl (Term.val S t)

variable {S}

/-- `Ωₖ ≤ val r` for a principal `r` of level `k` (and `1 ≤ val r` at level `0`). -/
theorem OmT_lvl_le {r : Term} (hr : Term.NF r) (hc : Cw S r) (hp : r.isPrin = true) :
    OmT 1 (lvl (Term.val S r)) ≤ Term.val S r := by
  have hv := Cw_val_lt hc hr
  rcases Nat.eq_zero_or_pos (lvl (Term.val S r)) with h | h
  · rw [h, OmT_zero]
    exact Order.one_le_iff_ne_zero.2 (Term.val_ne_zero S hr (Term.NF.ne_zero_of_isPrin hp))
  · exact lvl_ge hv h.ne'

/-- The level of `ψ_{Ω_{k+1}}(a)` read from its subscript. -/
theorem natOf_psiS {s a : Term} (hc : Cw S (.psiS s a)) :
    natOf (Term.val S s) = lvl (Term.val S (.psiS s a)) := by
  obtain ⟨⟨k, hk⟩, _, _⟩ := hc
  rw [hk, natOf_nat, lvl_psiS s a hk]

theorem natOf_om {b : Term} (hc : Cw S (.om b)) :
    natOf (Term.val S b) = lvl (Term.val S (.om b)) := by
  obtain ⟨k, hk0, hk⟩ := hc
  rw [hk, natOf_nat, val_om_of_Cw hk, lvl_Om hk0]

/-! ## The `φ`-code -/

theorem ev_codephi {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1)) :
    ev 1 (plus 1 (th (k + 1) x) y) = thb 1 (ev 1 x) (k + 1) + ev 1 y := by
  rw [ev_plus base_one (NF.cth hx (dom_of_lt base_one (hxk.trans (OmT_lt_succ base_one _)))) hy]
  rfl

theorem NF_codephi {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1)) :
    NF 1 (plus 1 (th (k + 1) x) y) :=
  NF_plus base_one (NF.cth hx (dom_of_lt base_one (hxk.trans (OmT_lt_succ base_one _)))) hy

/-- `ϑ̄_{k+1}(x) + y < Pₖ` for `x, y < Ω_{k+1}`. -/
theorem codephi_lt_Pk {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1))
    (hyk : ev 1 y < OmT 1 (k + 1)) : ev 1 (plus 1 (th (k + 1) x) y) < ev 1 (Pk k) := by
  rw [ev_codephi hx hy hxk]
  have hnx : NF 1 (th (k + 1) x) := NF.cth hx (dom_of_lt base_one (hxk.trans (OmT_lt_succ base_one _)))
  have h1 : ev 1 (th (k + 1) x) < ev 1 (Pk k) := by
    refine thb_lt_of_I base_one hnx (NF_Pk k) (by rw [ev_Omk]; exact hxk) ?_
    rw [show Tm.star 1 (k + 1) x = 0 by unfold Tm.star; rw [Ki_nil_of_lt base_one hx hxk]; rfl]
    exact thb_pos base_one (NF.th_dom (NF_Pk k))
  exact Pk_principal k h1 (hyk.trans (ev_Pk_bounds k).1)

theorem Kst_codephi {L k : ℕ} {x y : Tm} (hL : L ≤ k + 1) :
    Kst L (plus 1 (th (k + 1) x) y) ⊆ (k + 1, x) :: (Kst L x ++ Kst L y) := by
  intro p hp
  have h := Kst_plus 1 L _ _ hp
  rcases List.mem_append.1 h with h | h
  · have e : Kst L (th (k + 1) x) = (k + 1, x) :: Kst L x := by
      simp [Kst, show ¬ k + 1 < L by omega]
    rw [e] at h
    rcases List.mem_cons.1 h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)

theorem Kst_codephi_top {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1))
    (hyk : ev 1 y < OmT 1 (k + 1)) :
    Kst (k + 1) (plus 1 (th (k + 1) x) y) ⊆ [(k + 1, x)] := by
  intro p hp
  have := Kst_codephi (x := x) (y := y) (le_refl (k + 1)) hp
  rw [Kst_nil_of_lt base_one hx hxk, Kst_nil_of_lt base_one hy hyk] at this
  simpa using this

/-- The level-`k` parts of a `φ`-code are parts of `x` or `y`, so at most `x` or `y`. -/
theorem Ki_codephi {k : ℕ} {x y : Tm} (hx : NF 1 x) (hy : NF 1 y) (hxk : ev 1 x < OmT 1 (k + 1))
    (hyk : ev 1 y < OmT 1 (k + 1)) :
    ∀ u ∈ Ki k (plus 1 (th (k + 1) x) y), ev 1 u ≤ ev 1 x ∨ ev 1 u ≤ ev 1 y := by
  intro u hu
  have h := Ki_plus 1 k _ _ hu
  simp only [Ki, show ¬ k + 1 < k by omega, show k + 1 ≠ k by omega, if_false,
    List.mem_append] at h
  rcases h with h | h
  · exact Or.inl (Ki_le_of_lt base_one hx hxk u h)
  · exact Or.inr (Ki_le_of_lt base_one hy hyk u h)

/-! ## The `ψ`-code -/

theorem NF_codepsi {k : ℕ} {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0})) :
    NF 1 (plus 1 (Pk k) (Fc x)) := NF_plus base_one (NF_Pk k) (NF_Fc hx hxω)

theorem ev_codepsi {k : ℕ} {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0})) :
    ev 1 (plus 1 (Pk k) (Fc x)) = ev 1 (Pk k) + ev 1 (Fc x) :=
  ev_plus base_one (NF_Pk k) (NF_Fc hx hxω)

/-- `Pⱼ < F(x)` for `j ≤ lvl x`. -/
theorem Pk_lt_Fc {j : ℕ} {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0}))
    (hx0 : ev 1 x ≠ 0) (hj : j ≤ lvl (ev 1 x)) : ev 1 (Pk j) < ev 1 (Fc x) := by
  obtain ⟨h1, h2, h3⟩ := ev_Fc_pos hx hxω hx0
  rcases lt_or_eq_of_le hj with hlt | rfl
  · exact lt_of_lt_of_le (ev_Pk_bounds j).2 ((OmT_mono base_one (by omega)).trans h2)
  · have hn := NF_Fc hx hxω
    rw [Fc_pos hx0] at hn ⊢
    refine thb_lt_of_I base_one (NF_Pk _) hn ?_ ?_
    · rw [ev_Omk]; exact Farg_ge hx
    · refine star_le_of 1 (fun u hu => ?_) (thb_pos base_one (NF.th_dom hn))
      rw [Omk, Ki] at hu
      simp at hu
      subst hu
      have := (Farg_ge (m := lvl (ev 1 x)) hx).trans
        (thb_gt_arg base_one (NF.th_dom hn) (Farg_lt hx (lvl_lt hxω)))
      rwa [← ev_Omk] at this

/-- `Ω_{j+1} < F(x)` for `j ≤ lvl x`. -/
theorem OmT_lt_Fc {j : ℕ} {x : Tm} (hx : NF 1 x) (hxω : ev 1 x < Om (ω : Ordinal.{0}))
    (hx0 : ev 1 x ≠ 0) (hj : j ≤ lvl (ev 1 x)) : OmT 1 (j + 1) < ev 1 (Fc x) :=
  (ev_Pk_bounds j).1.trans (Pk_lt_Fc hx hxω hx0 hj)

/-! ## Lemma Q -/

/-- **Lemma Q** (as a bound on all subterms visited from `μ = ψ_{Ω_{k+1}}(a)`): the `K*_{k+1}`-elements
of `E(u)` are below `F(E a)`, given the invariants on the subterms and Lemma M for the pairs `(c, a)`. -/
theorem QB {s a : Term} (hμ : Term.NF (.psiS s a)) {k : ℕ} (hk : Term.val S s = k)
    (ha : Cw S a) (haω : Term.val S a < Om (ω : Ordinal.{0}))
    (hD : ∀ u : Term, u.size ≤ a.size → Cw S u → Term.NF u → DI S u)
    (hM : ∀ c : Term, c.size < a.size → Cw S c → Term.NF c → Term.val S c < Term.val S a →
      ev 1 (E S c) < ev 1 (E S a))
    (ha0 : ev 1 (E S a) ≠ 0) :
    ∀ u : Term, u.size ≤ a.size → Term.NF u → Cw S u → Term.KLt (.psiS s a) u a →
      Term.val S u ≤ Term.val S a → ∀ p ∈ Kst (k + 1) (E S u), ev 1 p.2 < ev 1 (Fc (E S a)) := by
  have hDa := hD a le_rfl ha hμ.2.1
  have hEaω : ev 1 (E S a) < Om (ω : Ordinal.{0}) :=
    hDa.lt.trans (OmT_succ_lt_Om_omega 1 _)
  set X := ev 1 (Fc (E S a)) with hX
  have hX0 : 0 < X := lt_of_le_of_lt zero_le (OmT_lt_Fc hDa.nf hEaω ha0 (Nat.zero_le _))
  have hXP : IsPrincipal (· + ·) X := Fc_principal hDa.nf hEaω ha0
  -- levels of visited nodes are at most `m = lvl a`
  have hlvX : ∀ j : ℕ, j ≤ lvl (Term.val S a) → ev 1 (Pk j) < X ∧ OmT 1 (j + 1) < X := by
    intro j hj
    rw [← hDa.lv] at hj
    exact ⟨Pk_lt_Fc hDa.nf hEaω ha0 hj, OmT_lt_Fc hDa.nf hEaω ha0 hj⟩
  intro u
  induction u with
  | zero => intro _ _ _ _ _ p hp; simp [E, Kst] at hp
  | inacc _ => intro _ _ hc; exact absurd hc (by simp [Cw])
  | inaccW => intro _ _ hc; exact absurd hc (by simp [Cw])
  | psiI _ _ _ => intro _ _ hc; exact absurd hc (by simp [Cw])
  | add x y ihx ihy =>
    intro hs hn hc hK hv p hp
    have h := Kst_plus 1 (k + 1) _ _ hp
    rcases List.mem_append.1 h with h | h
    · exact ihx (by simp [Term.size] at hs; omega) hn.1 hc.1 hK.1
        ((val_le_add_left x y).trans hv) p h
    · exact ihy (by simp [Term.size] at hs; omega) hn.2.1 hc.2 hK.2
        ((val_le_add_right x y).trans hv) p h
  | om b _ =>
    intro _ _ hc _ _ p hp
    simp only [E, Omk, Kst] at hp
    split_ifs at hp
    · simp at hp
    · simp at hp; subst hp; exact hX0
  | phi x y ihx ihy =>
    intro hs hn hc hK hv p hp
    have hDx := hD x (by simp [Term.size] at hs; omega) hc.1 hn.1
    have hDy := hD y (by simp [Term.size] at hs; omega) hc.2 hn.2.1
    obtain ⟨hx, hy⟩ := NF_phi_lt (S := S) hn
    set j := lvl (Term.val S (.phi x y)) with hjdef
    have hvω := Cw_val_lt hc hn
    have hxk : ev 1 (E S x) < OmT 1 (j + 1) :=
      lt_of_lt_of_le hDx.lt (OmT_mono base_one (by have := lvl_mono hvω hx.le; omega))
    have hyk : ev 1 (E S y) < OmT 1 (j + 1) :=
      lt_of_lt_of_le hDy.lt (OmT_mono base_one (by have := lvl_mono hvω hy.le; omega))
    have hjm : j ≤ lvl (Term.val S a) := lvl_mono haω hv
    simp only [E] at hp
    rw [← hjdef] at hp
    simp only [Kst] at hp
    split_ifs at hp with hjk
    · simp at hp
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp
      exact (codephi_lt_Pk hDx.nf hDy.nf hxk hyk).trans (hlvX j hjm).1
    · rcases List.mem_cons.1 (Kst_codephi (by omega) hp) with h | h
      · subst h; exact hxk.trans_le ((hlvX j hjm).2.le)
      · rcases List.mem_append.1 h with h | h
        · exact ihx (by simp [Term.size] at hs; omega) hn.1 hc.1 hK.1 (hx.le.trans hv) p h
        · exact ihy (by simp [Term.size] at hs; omega) hn.2.1 hc.2 hK.2 (hy.le.trans hv) p h
  | psiS s' c _ ihc =>
    intro hs hn hc hK hv p hp
    obtain ⟨⟨j, hj⟩, hcω, hcc⟩ := hc
    simp only [E] at hp
    rw [hj, natOf_nat] at hp
    simp only [Kst] at hp
    split_ifs at hp with hjk
    · simp at hp
    have hjk' : k + 1 ≤ j := not_lt.1 hjk
    -- visited: `c < a`
    rcases hK with hK | ⟨hca, _, hKc⟩
    · exfalso
      have h1 := (Term.cmp_lt_iff S hn hμ).1 hK
      have h2 := (psiS_bounds_nat s' c hj).1
      have h3 := (psiS_bounds_nat s a hk).2
      have h4 : OmT 1 (k + 1) ≤ Om (j : Ordinal.{0}) := by
        rw [Om_nat_eq_OmT (by omega)]; exact OmT_mono base_one hjk'
      exact absurd h1 (not_lt.2 (h3.le.trans (h4.trans h2.le)))
    have hc_lt : Term.val S c < Term.val S a := (Term.cmp_lt_iff S hn.2.1 hμ.2.1).1 hca
    have hsc : c.size < a.size := by
      by_contra hge
      simp [Term.size] at hs; omega
    have hDc := hD c (le_of_lt hsc) hcc hn.2.1
    have hEc : ev 1 (E S c) < ev 1 (E S a) := hM c hsc hcc hn.2.1 hc_lt
    have hjm : j ≤ lvl (Term.val S a) := by
      have := lvl_mono haω hv; rw [lvl_psiS s' c hj] at this; exact this
    have hFc : ev 1 (Fc (E S c)) < X := Fc_lt hDc.nf hDa.nf hEaω hEc
    rcases List.mem_cons.1 hp with hp | hp
    · subst hp
      rw [ev_codepsi hDc.nf (hEc.trans hEaω)]
      exact hXP (hlvX j hjm).1 hFc
    · rcases List.mem_append.1 (Kst_plus 1 (k + 1) _ _ hp) with h | h
      · rw [Kst_Pk (by omega)] at h
        simp at h
        rcases h with rfl | rfl
        · rw [ev_Omk]; exact (hlvX j hjm).2
        · exact hX0
      · by_cases hc0 : ev 1 (E S c) = 0
        · rw [Fc_zero hc0] at h; simp [Kst] at h
        have h' := Kst_Fc hc0 h
        split_ifs at h' with hl
        · simp at h'
        rcases List.mem_cons.1 h' with h' | h'
        · subst h'
          exact (ev_Fc_pos hDc.nf (hEc.trans hEaω) hc0).1.trans hFc
        · rcases List.mem_append.1 h' with h' | h'
          · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact hX0
          · rcases List.mem_append.1 h' with h' | h'
            · rw [Kst_Omk (by omega)] at h'; simp at h'; subst h'; exact hX0
            · exact ihc (le_of_lt hsc) hn.2.1 hcc hKc hc_lt.le p h'

end Googology.Trans.PoR.InaccPsi.R2.Br
