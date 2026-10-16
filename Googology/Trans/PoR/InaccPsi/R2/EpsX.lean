import Googology.Trans.PoR.InaccPsi.R2.EpsQ

/-!
# The atoms `ω^{ε_{x+1}+t(x)}` with a term exponent, and the offset terms below `ε_{x+1}²`

`R2.EpsQ` has the atoms `ω^{ε_{x+1}+β}` with a constant `β`.  Here the exponent is a term `t` of `OT`
(`t(ρ) < ε_{ρ+1}`), so a finite sum of atoms `Σ ω^{ε_{x+1}+tᵢ(x)}` plus a term `s` of `OT` gives every
ordinal below `ε_{ρ+1}·ε_{ρ+1} = ω^{ε_{ρ+1}·2}` at `x = ρ`.  `ε_{x+1}` is again a pseudo-base: the atom
`ω^{ε+β}` is to `ε` what `ω^{x+β}` is to `x` in `R2.TopO`.

* `evL` (the sum of the atoms of a list of exponent terms, the head being the last summand), `CBL`,
  `evL_lt` (`evL L x < ω^{ε_{x+1}·2}`), `eN_le_evL`;
* `pi_ge`, `pi_eAtomT` (**Lemma EXACT for the atom `ω^{ε_{x+1}+β}`** for every `β ∈ Tᵖ[σ]` below
  `ε_{ρ+1}`: `π(ω^{ε_{ρ+1}+β}) = ω^{ε_{σ+1}+π(β)}`; [W07a] Lemma 4.2 with `wbar_eq` at the pseudo-base,
  Def 3.22/3.28, Def 5.1, Lemma 5.3), `pi_evL`, `eN_TB_of_evL` (`ε_{ρ+1} ∈ Tᵖ[σ]` once a value
  `evL L ρ + s(ρ)` with `L ≠ []` is, through its leading component), `pi_eXt` (**Lemma EXACT for
  `evL L + s`**);
* `ImgA`, `RstK.imgA` (**Lemma IMG for the atom `ω^{ε_{x+1}+β}`, every `β < ε_{ρ+1}`**, by induction on
  `β`, with a term `t` for `β`: `β = 0` is the atom `ε ≤₁ ε·2` (`pkg_eN`); `β = β'' + 1`: the copy of
  `ω^{ε+β''+1}` is an indecomposable above the copy of `ω^{ε+β''}`; `β = β'' + ω^z`, `z > 0`: the
  source atoms `ω^{ε+β} ≤₁ ω^{ε+β} + z` and `ω^{ε+β''} ≤₁ ω^{ε+β''} + z` of `R₁⁺` ([W07b] Theorem 2.2,
  `logend(ε+β) ≥ z`, `logend(ε+β'') ≥ z`) hold inside the block (`RstK.lowδ`) and are kept by the copy;
  below `ρ` a copy is a `υ`-point or has its `R₁⁺` reach, so both copied exponents are multiples of
  `ω^{f(z)}` and the larger is at least the smaller plus `ω^{f(z)}`; the term `tw` for `ω^z` of
  `R2.TopO` (`TwW`) bounds `ω^{z}` at the copied base by `ω^{f(z)}`), `RstK.pkg_atomT`, `RstK.pkgL`
  (**the IMG package of `ε_{x+1}·q` for every `0 < q < ε_{ρ+1}`**, by the Cantor normal form of `q`),
  `RstK.pkgLt`;
* `rs_rstX` (**Lemma RS with the target `evL L + s`**: `rs_rstF` of stage 7 with this `T`).

No new axiom.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## Sums of atoms -/

/-- The sum of the atoms `ω^{ε_{x+1}+t(x)}` of a list (the head is the last summand). -/
noncomputable def evL : List OT → Ordinal.{0} → Ordinal.{0}
  | [], _ => 0
  | t :: L, x => evL L x + ω ^ (eN x + ev t x)

/-- All constants of all exponent terms below `s`. -/
def CBL (L : List OT) (s : Ordinal.{0}) : Prop := ∀ t ∈ L, CB t s

theorem CBL_mono {L : List OT} {s s' : Ordinal.{0}} (h : CBL L s) (hs : s ≤ s') : CBL L s' :=
  fun t ht => CB_mono (h t ht) hs

@[simp] theorem evL_nil (x : Ordinal.{0}) : evL [] x = 0 := rfl

@[simp] theorem evL_cons (t : OT) (L : List OT) (x : Ordinal.{0}) :
    evL (t :: L) x = evL L x + ω ^ (eN x + ev t x) := rfl

/-- An atom with exponent below `ε·2`. -/
theorem atom_lt_sq {x β : Ordinal.{0}} (hβ : β < eN x) :
    ω ^ (eN x + β) < ω ^ (eN x + eN x) :=
  (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ)

theorem evL_lt {x : Ordinal.{0}} : ∀ L, CBL L x → evL L x < ω ^ (eN x + eN x)
  | [], _ => opow_pos _ omega0_pos
  | t :: L, h => by
    rw [evL_cons]
    exact isPrincipal_add_omega0_opow _ (evL_lt L (fun u hu => h u (List.mem_cons_of_mem _ hu)))
      (atom_lt_sq (ev_lt_eN (h t List.mem_cons_self)))

theorem eN_le_atom (x β : Ordinal.{0}) : eN x ≤ ω ^ (eN x + β) :=
  le_self_add.trans (right_le_opow _ one_lt_omega0)

theorem eN_le_evL {x : Ordinal.{0}} {L : List OT} (hL : L ≠ []) : eN x ≤ evL L x := by
  obtain ⟨t, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  rw [evL_cons]
  exact (eN_le_atom x _).trans le_add_self

/-! ## Lemma EXACT -/

/-- `π_{σ,ρ}` does not move a point of `Tᵖ[σ]` that is `≥ σ` below `σ`. -/
theorem pi_ge {σ ρ β : Ordinal.{0}} (hB : Bases σ ρ) (hβ : β ∈ TB ρ σ) (hσβ : σ ≤ β) :
    σ ≤ pi σ ρ β := by
  by_contra h
  push Not at h
  have h1 : pi σ ρ β ∈ TB ρ σ := mem_TB_of_lt hB h
  have h2 : pi σ ρ (pi σ ρ β) = pi σ ρ β := pi_lt hB h
  have := (pi_bijOn hB).1.injOn h1 hβ h2
  rw [this] at h
  exact absurd hσβ (not_le.2 h)

/-- **Lemma EXACT for the atom `ω^{ε_{x+1}+β}`** (`β ∈ Tᵖ[σ]`, `β < ε_{ρ+1}`), once `ε_{ρ+1} ∈ Tᵖ[σ]`. -/
theorem pi_eAtomT {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (heTB : eN ρ ∈ TB ρ σ) {β : Ordinal.{0}} (hβTB : β ∈ TB ρ σ) (hβe : β < eN ρ) :
    ω ^ (eN ρ + β) ∈ TB ρ σ ∧ pi σ ρ (ω ^ (eN ρ + β)) = ω ^ (eN σ + pi σ ρ β) := by
  rcases lt_or_ge β σ with hβσ | hσβ
  · rw [pi_lt hB hβσ]; exact pi_eAtom hσ hρ hB heTB hβσ
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hpe := pi_eN hσ hρ hB heTB
  obtain ⟨he1, -, -⟩ := eN_lt_upsPt hρ hρ1
  obtain ⟨hes1, -, -⟩ := eN_lt_upsPt hσ hσ1
  have hωβ : ω ≤ β := (omega0_lt_inE hB.1).le.trans hσβ
  obtain ⟨hξTB, hpξ⟩ := pi_add hB heTB hβTB
  rw [hpe] at hpξ
  have hξ1 : eN ρ + β < Om1 := Om1_add_lt he1 (hβe.trans he1)
  have hv := vt_eN hB.2.1 hρ1 hβe hξ1
  rw [add_assoc, one_add_of_omega0_le hωβ] at hv
  obtain ⟨hvT, hvP⟩ := vt_mem hB.2.1 hρ1 hξTB.1 hξ1
  refine ⟨by rw [← hv]; exact ⟨hvT, by rw [hvP]; exact hξTB.2⟩, ?_⟩
  have hπβ : pi σ ρ β < eN σ := by
    rw [← hpe]; exact (pi_bijOn hB).2 hβTB heTB hβe
  have hωπ : ω ≤ pi σ ρ β := (omega0_lt_inE hB.1).le.trans (pi_ge hB hβTB hσβ)
  have hv' := vt_eN hB.1 hσ1 hπβ (Om1_add_lt hes1 (hπβ.trans hes1))
  rw [add_assoc, one_add_of_omega0_le hωπ] at hv'
  rw [← hv, pi_vt hB hξTB hξ1, hpξ, hv']

/-- **Lemma EXACT for a sum of atoms** (exponent terms with constants below `σ`), once
`ε_{ρ+1} ∈ Tᵖ[σ]`. -/
theorem pi_evL {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ)
    (heTB : eN ρ ∈ TB ρ σ) : ∀ L, CBL L σ → evL L ρ ∈ TB ρ σ ∧ pi σ ρ (evL L ρ) = evL L σ
  | [], _ => by
    simp only [evL_nil]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | t :: L, h => by
    obtain ⟨h1, h2⟩ := pi_evL hσ hρ hB heTB L (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have ht : CB t σ := h t List.mem_cons_self
    obtain ⟨h3, h4⟩ := pi_ev hB t ht
    obtain ⟨h5, h6⟩ := pi_eAtomT hσ hρ hB heTB h3 (ev_lt_eN (CB_mono ht hB.2.2.1.le))
    rw [h4] at h6
    obtain ⟨h7, h8⟩ := pi_add hB h1 h5
    simp only [evL_cons]
    exact ⟨h7, by rw [h8, h2, h6]⟩

/-- `ε_{ρ+1} ∈ Tᵖ[σ]` once `evL L ρ + s(ρ) ∈ Tᵖ[σ]` with `L ≠ []` (through its leading component). -/
theorem eN_TB_of_evL {σ ρ : Ordinal.{0}} (hρ : UpsPt ρ) (hB : Bases σ ρ) {L : List OT} {s : OT}
    (hL : L ≠ []) (hCL : CBL L ρ) (hs : CB s ρ) (hx : evL L ρ + ev s ρ ∈ TB ρ σ) :
    eN ρ ∈ TB ρ σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨he1, -, -⟩ := eN_lt_upsPt hρ hρ1
  set x := evL L ρ + ev s ρ with hxdef
  have he : ω ^ eN ρ = eN ρ := eN_E ρ
  have hex : eN ρ ≤ x := (eN_le_evL hL).trans le_self_add
  have hx0 : x ≠ 0 := (lt_of_lt_of_le (eN_E ρ).pos hex).ne'
  have hxlt : x < ω ^ (eN ρ + eN ρ) :=
    isPrincipal_add_omega0_opow _ (evL_lt L hCL)
      ((ev_lt_eN hs).trans_le (le_self_add.trans (right_le_opow _ one_lt_omega0)))
  have hlog1 : eN ρ ≤ log ω x := le_log_of_opow_le one_lt_omega0 (by rw [he]; exact hex)
  have hlog2 : log ω x < eN ρ + eN ρ := by
    by_contra hle; push Not at hle
    exact absurd ((opow_le_opow_right omega0_pos hle).trans (opow_log_le_self ω hx0))
      (not_le.2 hxlt)
  set β := log ω x - eN ρ with hβ
  have hlog : log ω x = eN ρ + β := (Ordinal.add_sub_cancel_of_le hlog1).symm
  have hβe : β < eN ρ := by
    rw [hlog] at hlog2; exact (add_lt_add_iff_left _).1 hlog2
  have hx1 : x < Om1 := Om1_add_lt
    ((evL_lt L hCL).trans (Om1_opow_lt (Om1_add_lt he1 he1))) ((ev_lt_eN hs).trans he1)
  have hlead := lead_comp hx0
  rw [hlog] at hlead
  have hc := Par_comps hB.2.1 hρ1 hx.1 ((lt_eN ρ).le.trans hex) hx1 hlead
  obtain ⟨haT, haP⟩ := hc.2 ((lt_eN ρ).le.trans (eN_le_atom ρ β))
  exact eN_TB_of_atom hρ hB hβe
    ⟨haT, fun p hp => hx.2 (Finset.mem_coe.2 (haP (Finset.mem_coe.1 hp)))⟩

/-- **Lemma EXACT for `evL L + s`** (`L ≠ []`, constants below `σ`): if `evL L ρ + s(ρ) ∈ Tᵖ[σ]` then
`π_{σ,ρ}(evL L ρ + s(ρ)) = evL L σ + s(σ)`. -/
theorem pi_eXt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {L : List OT}
    {s : OT} (hL : L ≠ []) (hCL : CBL L σ) (hs : CB s σ) (hx : evL L ρ + ev s ρ ∈ TB ρ σ) :
    pi σ ρ (evL L ρ + ev s ρ) = evL L σ + ev s σ := by
  have heTB := eN_TB_of_evL hρ hB hL (CBL_mono hCL hB.2.2.1.le) (CB_mono hs hB.2.2.1.le) hx
  obtain ⟨h1, h2⟩ := pi_evL hσ hρ hB heTB L hCL
  obtain ⟨h3, h4⟩ := pi_ev hB s hs
  rw [(pi_add hB h1 h3).2, h2, h4]

/-! ## Lemma IMG -/

/-- **The IMG statement for the atom `ω^{ε_{ρ+1}+β}`** with a term `t` for `β` (`t(ρ) = β`, constants in
`Z`): every covering copy `f` of a set containing the witness sets has `ω^{ε_{f(ρ)+1}+t(f(ρ))} ≤ f(atom)`. -/
def ImgA (ρ δ β : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (t : OT) : Prop :=
  WZ ρ δ W Z ∧ CB t ρ ∧ (∀ c ∈ cs t, c ∈ Z) ∧ ev t ρ = β ∧ ω ^ (eN ρ + β) ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      ω ^ (eN (f ρ) + ev t (f ρ)) ≤ f (ω ^ (eN ρ + β))

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- `ω^{ε_{ρ+1}+β} < δ` for `β < ε_{ρ+1}`. -/
theorem atomT_lt_δ {β : Ordinal.{0}} (hβ : β < eN ρ) : ω ^ (eN ρ + β) < δ := by
  have hδE := h.δE
  have heδ := h.eN_lt_δ
  have : eN ρ + β < δ := (inE_indec hδE).add_lt heδ (hβ.trans heδ)
  have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 this
  have hδ' : ω ^ δ = δ := hδE
  rwa [hδ'] at h2

/-- The source atom `ω^{ε+β} ≤₁ ω^{ε+β} + z` inside the block of `ρ` (`ω^z ∣ β`, `0 < z ≤ β < ε`). -/
theorem src_atomE {z β : Ordinal.{0}} (hz0 : z ≠ 0) (hzβ : z < eN ρ) (hd : ω ^ z ∣ β)
    (hβ : β < eN ρ) : le1 (ω ^ (eN ρ + β)) (ω ^ (eN ρ + β) + z) := by
  have hv := h.atomT_lt_δ hβ
  have hρv : ρ < ω ^ (eN ρ + β) := (lt_eN ρ).trans_le (eN_le_atom ρ β)
  have hzv : z < ω ^ (eN ρ + β) := hzβ.trans_le (eN_le_atom ρ β)
  have hne : eN ρ + β ≠ 0 := (lt_of_lt_of_le (eN_E ρ).pos le_self_add).ne'
  refine (h.lowδ _ _ hρv ((inE_indec h.δE).add_lt hv (hzv.trans hv)).le).2 ?_
  exact (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzv.le).2
    ⟨eN ρ + β, hne, rfl, (le_lg_iff hne z).2 (dvd_add (opow_dvd_of_inE (eN_E ρ) hzβ.le) hd)⟩

/-- The copy of a source atom `a ≤₁ a + z` (`a = ω^{ε+β}`) is `ω^c` with `ω^{f(z)} ∣ c`. -/
theorem copy_atom {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {a z : Ordinal.{0}} (ha : a ∈ A) (hz : z ∈ A) (haz : a + z ∈ A) (hz0 : z ≠ 0) (hza : z ≤ a)
    (h0A : (0 : Ordinal.{0}) ∈ A) (hsrc : le1 a (a + z)) :
    ∃ c, f a = ω ^ c ∧ ω ^ f z ∣ c := by
  have hfz0 : 0 < f z := by
    have h1 : f 0 < f z := C.mono h0A hz (pos_iff_ne_zero.2 hz0)
    rwa [C.fix 0 h0A h.ρE.pos] at h1
  have hfza : f z ≤ f a := (C.mono.le_iff_le hz ha).2 hza
  have himg : le1 (f a) (f a + f z) := by
    have := C.cov1 a ha (a + z) haz hsrc
    rwa [← C.add a ha z hz (a + z) haz rfl] at this
  by_cases hU : UpsPt (f a)
  · have hE := upsPt_inE hU
    have hE' : ω ^ f a = f a := hE
    exact ⟨f a, hE'.symm, opow_dvd_of_inE hE hfza⟩
  · have hR := (C.sk (f a) (C.low a ha) hU (f a + f z)).1 himg
    obtain ⟨c, hc0, hfc, hzc⟩ := (le1R_thm22 hfz0 hfza).1 hR
    exact ⟨c, hfc, (le_lg_iff hc0 _).1 hzc⟩

/-- **Lemma IMG for the atom `ω^{ε_{ρ+1}+β}`**, every `β < ε_{ρ+1}`. -/
theorem imgA : ∀ β, β < eN ρ → ∃ W Z t, ImgA ρ δ β W Z t := by
  classical
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβe
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρe : ρ < eN ρ := lt_eN ρ
  have hvδ := h.atomT_lt_δ hβe
  have hρv : ρ < ω ^ (eN ρ + β) := hρe.trans_le (eN_le_atom ρ β)
  rcases eq_or_ne β 0 with rfl | hβ0
  · obtain ⟨-, -, W, Z, w, m, i⟩ := h.pkg_eN
    have he : ω ^ (eN ρ + 0) = eN ρ := by rw [add_zero]; exact eN_E ρ
    refine ⟨W, insert 0 Z, k 0, w.insZ hρE.pos, hρE.pos, ?_, rfl, ?_, ?_⟩
    · intro c hc; simp [cs] at hc; simp [hc]
    · rw [he]
      rcases Finset.mem_union.1 m with hm | hm
      · exact Finset.mem_union_left _ hm
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hm)
    · intro A f hW hZ C
      have hZ' : ↑Z ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
      rw [he, ev_k, add_zero]
      have hfE : ω ^ eN (f ρ) = eN (f ρ) := eN_E (f ρ)
      rw [hfE]
      exact i A f hW hZ' C
  obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
  have hzβ : lg β ≤ β := lg_le hβ0
  obtain ⟨W1, Z1, t'', w1, c1, s1, e1, m1, b1⟩ := IH β'' hβ''β (hβ''β.trans hβe)
  set v := ω ^ (eN ρ + β) with hvdef
  set v'' := ω ^ (eN ρ + β'') with hv''def
  have hv''v : v'' < v :=
    (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
  have hρv'' : ρ < v'' := hρe.trans_le (eN_le_atom ρ β'')
  rcases eq_or_ne (lg β) 0 with hz0 | hz0
  · -- `β = β'' + 1`
    have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
    have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
    refine ⟨insert v W1, insert 1 Z1, add t'' (k 1), (w1.insZ h1ρ).insW hρv.le hvδ (Or.inl (indec_opow _)),
      ⟨c1, h1ρ⟩, ?_, by simp [e1, hβs], Finset.mem_union_left _ (Finset.mem_insert_self _ _), ?_⟩
    · intro c hc
      simp only [cs, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact Finset.mem_insert_of_mem (s1 c hc)
      · exact Finset.mem_insert_self _ _
    intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have hvA : v ∈ A := hW (by simp)
    have h1A : v'' ∈ A := mem_A m1 hW1 hZ1
    have hb := b1 A f hW1 hZ1 C
    have hlt : f v'' < f v := C.mono h1A hvA hv''v
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
    rw [hc] at hlt ⊢
    have h3 : eN (f ρ) + ev t'' (f ρ) < c :=
      (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
    simp only [ev_add, ev_k]
    rw [← add_assoc]
    exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
  · -- `β = β'' + ω^z`, `z > 0`
    set z := lg β with hzdef
    have hze : z < eN ρ := lt_of_le_of_lt hzβ hβe
    obtain ⟨W3, Z3, tz, h3⟩ := h.img_val z hze
    have htw : ∃ W4 Z4 tw, TwW ρ δ z W3 Z3 W4 Z4 tw := by
      rcases lt_or_ge z ρ with hzρ | hρz
      · exact ⟨_, _, _, h.tw_small h3 hzρ⟩
      · have hζe : z - ρ < eN ρ := lt_of_le_of_lt (sub_le_self _ ρ) hze
        obtain ⟨W4, Z4, tζ, h4⟩ := h.img_val (z - ρ) hζe
        exact ⟨_, _, _, h.tw_big h3 h4 (Ordinal.add_sub_cancel_of_le hρz)⟩
    obtain ⟨W4, Z4, tw, w4, c4, s4, e4, b4⟩ := htw
    obtain ⟨w3, c3, s3, e3, m3, b3⟩ := h3
    have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
    have hsrc := h.src_atomE hz0 hze hdβ hβe
    have hsrc'' := h.src_atomE hz0 hze hdvd (hβ''β.trans hβe)
    have hzv : z < v := hze.trans_le (eN_le_atom ρ β)
    have hzv'' : z < v'' := hze.trans_le (eN_le_atom ρ β'')
    have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
    have hv''δ : v'' < δ := hv''v.trans hvδ
    have hvzδ : v + z < δ := hδI.add_lt hvδ (hzv.trans hvδ)
    have hv''zδ : v'' + z < δ := hδI.add_lt hv''δ (hzv.trans hvδ)
    set W0 := W1 ∪ W3 ∪ W4 with hW0
    set Z0 := insert 0 (Z1 ∪ Z3 ∪ Z4) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := ((w1.union w3).union w4).insZ hρE.pos
    have hsub : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W3 ∪ Z3 → x ∈ W0 ∪ Z0 := by
      intro x hx
      rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hW0, hZ0, hx]
    have hv''m : v'' ∈ W0 ∪ Z0 := hsub _ (Or.inl m1)
    have hzm : z ∈ W0 ∪ Z0 := hsub _ (Or.inr m3)
    have wz1 : WZ ρ δ (insert (v'' + z) W0) Z0 :=
      wz0.insW (hρv''.le.trans le_self_add) hv''zδ
        (Or.inr ⟨v'', hv''m, z, hzm, lt_add_of_pos_right _ hz0', lt_of_lt_of_le hzv'' le_self_add,
          rfl⟩)
    have wz2 : WZ ρ δ (insert v (insert (v'' + z) W0)) Z0 :=
      wz1.insW hρv.le hvδ (Or.inl (indec_opow _))
    have hzm2 : z ∈ insert v (insert (v'' + z) W0) ∪ Z0 := by
      rcases Finset.mem_union.1 hzm with hz | hz
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
      · exact Finset.mem_union_right _ hz
    have wzf : WZ ρ δ (insert (v + z) (insert v (insert (v'' + z) W0))) Z0 :=
      wz2.insW (hρv.le.trans le_self_add) hvzδ
        (Or.inr ⟨v, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hzm2,
          lt_add_of_pos_right _ hz0', lt_of_lt_of_le hzv le_self_add, rfl⟩)
    refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, add t'' tw, wzf, ⟨c1, c4⟩, ?_, ?_,
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ?_⟩
    · intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact Finset.mem_insert_of_mem (by simp [s1 c hc])
      · exact Finset.mem_insert_of_mem (by simp [s4 c hc])
    · simp only [ev_add]; rw [e1, e4, ← hgs]
    intro A f hW hZ C
    have hW0A : ↑W0 ⊆ A := fun x hx => hW (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))))
    have hsW : ∀ {S : Finset Ordinal.{0}}, S ⊆ W0 → ↑S ⊆ A := fun hS x hx =>
      hW0A (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hsZ : ∀ {S : Finset Ordinal.{0}}, S ⊆ Z0 → ↑S ⊆ A := fun hS x hx =>
      hZ (Finset.mem_coe.2 (hS (Finset.mem_coe.1 hx)))
    have hW1 : ↑W1 ⊆ A := hsW (by intro x hx; simp [hW0, hx])
    have hW34 : ↑(W3 ∪ W4) ⊆ A := hsW (by
      intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hW0, hx])
    have hZ1 : ↑Z1 ⊆ A := hsZ (by intro x hx; simp [hZ0, hx])
    have hZ34 : ↑(Z3 ∪ Z4) ⊆ A := hsZ (by
      intro x hx; rcases Finset.mem_union.1 hx with hx | hx <;> simp [hZ0, hx])
    have h0A : (0 : Ordinal.{0}) ∈ A := hsZ (S := {0}) (by simp [hZ0]) (by simp)
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hv''zA : v'' + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A hzm hW0A hZ
    have hv''A : v'' ∈ A := mem_A hv''m hW0A hZ
    have hb'' := b1 A f hW1 hZ1 C
    have hb4 : ev tw (f ρ) ≤ ω ^ f z := b4 A f hW34 hZ34 C
    have hcs : ∀ c ∈ cs (add t'' tw), c ∈ A := by
      intro c hc
      simp only [cs, List.mem_append] at hc
      rcases hc with hc | hc
      · exact hZ1 (Finset.mem_coe.2 (s1 c hc))
      · exact hZ34 (by simp [s4 c hc])
    have hCB : CB (add t'' tw) (f ρ) := img_cb C ⟨c1, c4⟩ hcs
    obtain ⟨c, hc, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzv''.le h0A hsrc''
    have hbc : eN (f ρ) + ev t'' (f ρ) ≤ c := by
      rw [hc] at hb''; exact (opow_le_opow_iff_right one_lt_omega0).1 hb''
    have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
    show ω ^ (eN (f ρ) + ev (add t'' tw) (f ρ)) ≤ f v
    by_cases hU : UpsPt (f v)
    · have hE := upsPt_inE hU
      have heF : eN (f ρ) < f v :=
        lt_of_le_of_lt ((eN_le_atom _ _).trans hb'') hfv''v
      have h1 : eN (eN (f ρ)) ≤ f v := eN_le heF hE
      have hEE := eN_E (eN (f ρ))
      have h2 : eN (f ρ) + ev (add t'' tw) (f ρ) < eN (eN (f ρ)) :=
        (inE_indec hEE).add_lt (lt_eN _) ((ev_lt_eN hCB).trans (lt_eN _))
      have h3 := (opow_lt_opow_iff_right one_lt_omega0).2 h2
      have hEE' : ω ^ eN (eN (f ρ)) = eN (eN (f ρ)) := hEE
      rw [hEE'] at h3
      exact (h3.trans_le h1).le
    obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
    have hca : c < a := by
      have := hfv''v; rw [hc, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    rw [ha]
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    simp only [ev_add]
    calc eN (f ρ) + (ev t'' (f ρ) + ev tw (f ρ)) = (eN (f ρ) + ev t'' (f ρ)) + ev tw (f ρ) :=
          (add_assoc _ _ _).symm
      _ ≤ c + ω ^ f z := add_le_add hbc hb4
      _ ≤ a := dvd_next hda hdc hca

/-- The IMG package of the atom `ω^{ε_{x+1}+t(x)}` from `imgA`. -/
theorem pkg_atomT {β : Ordinal.{0}} (hβ : β < eN ρ) :
    ∃ t : OT, CB t ρ ∧ ev t ρ = β ∧ ImgPkg ρ δ (fun x => ω ^ (eN x + ev t x)) := by
  obtain ⟨W, Z, t, w, c, s, e, m, b⟩ := h.imgA β hβ
  refine ⟨t, c, e, one_le_iff_pos.2 (opow_pos _ omega0_pos), ?_, W, Z, w, ?_, ?_⟩
  · show ω ^ (eN ρ + ev t ρ) < δ
    rw [e]; exact h.atomT_lt_δ hβ
  · show ω ^ (eN ρ + ev t ρ) ∈ W ∪ Z
    rw [e]; exact m
  · intro A f hW hZ C
    show ω ^ (eN (f ρ) + ev t (f ρ)) ≤ f (ω ^ (eN ρ + ev t ρ))
    rw [e]; exact b A f hW hZ C

/-- **The IMG package of `ε_{x+1}·q`** for every `0 < q < ε_{ρ+1}`: a list `L` of exponent terms with
`evL L ρ = ε_{ρ+1}·q` (the Cantor normal form of `q`). -/
theorem pkgL : ∀ q, 0 < q → q < eN ρ →
    ∃ L : List OT, L ≠ [] ∧ CBL L ρ ∧ evL L ρ = eN ρ * q ∧ ImgPkg ρ δ (evL L) := by
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq0 hqe
  obtain ⟨q'', hgs, hdvd, hq''⟩ := lg_split hq0.ne'
  have hze : lg q < eN ρ := lt_of_le_of_lt (lg_le hq0.ne') hqe
  obtain ⟨t, ct, et, pt⟩ := h.pkg_atomT hze
  have hval : eN ρ * q = eN ρ * q'' + ω ^ (eN ρ + ev t ρ) := by
    rw [et, ← eN_mul_opow, ← mul_add, ← hgs]
  rcases eq_or_ne q'' 0 with h0 | h0
  · refine ⟨[t], by simp, fun u hu => by simp at hu; rw [hu]; exact ct, ?_, ?_⟩
    · rw [evL_cons, evL_nil, zero_add, hval, h0, mul_zero, zero_add]
    · have e : evL [t] = fun x => ω ^ (eN x + ev t x) := funext fun x => by simp
      rw [e]; exact pt
  obtain ⟨L, hL, cL, eL, pL⟩ := IH q'' hq'' (pos_iff_ne_zero.2 h0) (hq''.trans hqe)
  refine ⟨t :: L, by simp, fun u hu => ?_, ?_, ?_⟩
  · rcases List.mem_cons.1 hu with rfl | hu
    · exact ct
    · exact cL u hu
  · rw [evL_cons, eL, hval]
  · have hapos : 0 < ω ^ (eN ρ + ev t ρ) := opow_pos _ omega0_pos
    have hle : ω ^ (eN ρ + ev t ρ) ≤ evL L ρ := by
      rw [eL, et, ← eN_mul_opow]; exact mul_le_mul_right (le_of_dvd h0 hdvd) _
    have e : evL (t :: L) = fun x => evL L x + ω ^ (eN x + ev t x) := funext fun x => rfl
    rw [e]
    exact ImgPkg.add pL pt (inE_indec h.δE) (lt_add_of_pos_right _ hapos)
      (lt_of_lt_of_le (lt_add_of_pos_right _ hapos) (add_le_add hle le_rfl))
      ((lt_eN ρ).le.trans ((eN_le_evL hL).trans le_self_add))

/-- The IMG package of `evL L + s` (`L ≠ []`, `s(ρ) ≥ 1`) from those of `evL L` and of `s`. -/
theorem pkgLt {L : List OT} (hL : L ≠ []) (pL : ImgPkg ρ δ (evL L)) {s : OT} (hs : CB s ρ)
    (h1 : 1 ≤ ev s ρ) : ImgPkg ρ δ (fun x => evL L x + ev s x) := by
  have hsρ : ev s ρ < eN ρ := ev_lt_eN hs
  exact ImgPkg.add pL (h.pkg_ot hs h1) (inE_indec h.δE)
    (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one h1))
    (lt_of_lt_of_le hsρ ((eN_le_evL hL).trans le_self_add))
    ((lt_eN ρ).le.trans ((eN_le_evL hL).trans le_self_add))

end RstK

/-! ## Lemma RS -/

/-- The constants of `evL L + s`. -/
noncomputable def csX (L : List OT) (s : OT) : Finset Ordinal.{0} :=
  ((s :: L).flatMap cs).toFinset

theorem csX_spec {L : List OT} {s : OT} {σ : Ordinal.{0}} (h : ∀ c ∈ csX L s, c < σ) :
    CBL L σ ∧ CB s σ := by
  refine ⟨fun t ht => (cb_iff t σ).2 fun c hc => h c ?_, (cb_iff s σ).2 fun c hc => h c ?_⟩
  · exact List.mem_toFinset.2 (List.mem_flatMap.2 ⟨t, List.mem_cons_of_mem _ ht, hc⟩)
  · exact List.mem_toFinset.2 (List.mem_flatMap.2 ⟨s, List.mem_cons_self, hc⟩)

theorem csX_lt {L : List OT} {s : OT} {σ : Ordinal.{0}} (hL : CBL L σ) (hs : CB s σ) :
    ∀ c ∈ csX L s, c < σ := by
  intro c hc
  obtain ⟨t, ht, hct⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 hc)
  rcases List.mem_cons.1 ht with rfl | ht
  · exact (cb_iff _ σ).1 hs c hct
  · exact (cb_iff _ σ).1 (hL t ht) c hct

/-- **Lemma RS with the target `evL L + s`** (`L ≠ []`, constants below `ρ`): if restarts `ρ_μ` with
`ρ_μ ≤₁ δ_μ + evL L ρ_μ + s(ρ_μ)` lie above every `κ' < ρ` (with `δ_μ < ρ`), then
`ρ ≤₁ δ + evL L ρ + s(ρ) + 1`. -/
theorem rs_rstX {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    {L : List OT} {s : OT} (hL : L ≠ []) (hCL : CBL L (upsilon r)) (hs : CB s (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + (evL L (upsilon μ) + ev s (upsilon μ)) →
        le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + (evL L (upsilon r) + ev s (upsilon r)) + 1) := by
  classical
  have hnx := upsilon_isNext r
  obtain ⟨-, -, hlt⟩ := eN_lt_upsPt h.ρU h.ρ1
  have hu := hlt _ hnx.1 hnx.2.1
  have hmE := upsPt_inE hnx.2.1
  have hsq : ∀ {x u : Ordinal.{0}}, InE u → eN x < u → ω ^ (eN x + eN x) < u := by
    intro x u huE hxu
    have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 ((inE_indec huE).add_lt hxu hxu)
    have hu' : ω ^ u = u := huE
    rwa [hu'] at h1
  refine rs_rstF (T := fun x => evL L x + ev s x) (C := csX L s) h (csX_lt hCL hs)
    ((lt_eN _).le.trans ((eN_le_evL hL).trans le_self_add))
    ((inE_indec hmE).add_lt ((evL_lt L hCL).trans (hsq hmE hu)) ((ev_lt_eN hs).trans hu)) ?_ ?_ htarget
  · intro σ hσ hB hCσ hTB
    obtain ⟨h1, h2⟩ := csX_spec hCσ
    exact pi_eXt hσ h.ρU hB hL h1 h2 hTB
  · intro σ hσE hσρ heσ hCσ
    obtain ⟨h1, h2⟩ := csX_spec hCσ
    have hρE := h.ρE
    exact (inE_indec hρE).add_lt ((evL_lt L h1).trans (hsq hρE heσ)) ((ev_lt_eN h2).trans heσ)

end Googology.Trans.PoR.InaccPsi.R2
