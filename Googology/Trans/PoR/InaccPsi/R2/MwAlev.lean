import Googology.Trans.PoR.InaccPsi.R2.MwLev

/-!
# The index off the fixed points of `φ_a` moves with `B_n`, for an ordinal level `a`

`B_n = Bc.bcB S n`, `φ_a = veblen a` for an ordinal `a` with `B_n a = a` (the level `ω` is the case used in
`R2.MwOm`; the levels `k < ω` are `R2.MwInd`).  `mwC a y` is the set of the ordinals above `y` that are not fixed
points of `φ_a`, and `mwIx a y β` the order type of `mwC a y ∩ β` (the index of `β`).

* `mwFix_E`, `mwFix_lim`, `mwFix_succ_not`, `mwFix_prin` (a fixed point of `φ_a` is an `ε`-number);
* `mwIx_low`, `mwIx_P`, `mwIx_above` (**`ind(y + 1 + δ) = δ`**, **`ind(p) = p`** for a fixed point `p > y`,
  **`ind(p + 1 + δ) = p + δ`**, with no fixed point in between; as `Ph.phInd_low`, `Ph.phInd_P`, `Ph.phInd_above`);
* `mwB_fixA`, `mwB_veblenA` (**`B_n` keeps the fixed points of `φ_a`, and `B_n(φ_a(y)) = φ_a(B_n y)`** off them);
* `mwLastA`, `mwIterA_B`, `mwGapA_move`, `mwIxA_move` (**`ind_{τ'}(B_n β) = B_n(ind_τ β)`**, as `Mw.mwInd_move`).

No new axiom.  New definitions: `mwC`, `mwIx` (the set and the index of `Ph.phC`, `Ph.phInd` at an ordinal level).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ph

variable {S : InaccSeq.{0}}

/-- The ordinals above `y` that are not fixed points of `φ_a`. -/
def mwC (a y : Ordinal.{0}) : Set Ordinal.{0} := {x | y < x ∧ veblen a x ≠ x}

/-- The index of `β` in `mwC a y`. -/
noncomputable def mwIx (a y β : Ordinal.{0}) : Ordinal.{0} := Cd.cdOtp (mwC a y) β

variable {a : Ordinal.{0}}

theorem mwFix_E {v : Ordinal.{0}} (h : veblen a v = v) : InE v := by
  have := veblen_eq_self_of_le (zero_le : (0 : Ordinal.{0}) ≤ a) h
  rwa [veblen_zero_apply] at this

theorem mwFix_lim {v : Ordinal.{0}} (h : veblen a v = v) : IsSuccLimit v :=
  ev_isSuccLimit_of_inE (mwFix_E h)

theorem mwFix_succ_not (v : Ordinal.{0}) : veblen a (v + 1) ≠ v + 1 := fun h =>
  not_isSuccLimit_succ v (by rw [succ_eq_add_one]; exact mwFix_lim h)

theorem mwFix_prin {v : Ordinal.{0}} (h : veblen a v = v) : IsPrincipal (· + ·) v := by
  have hE : ω ^ v = v := mwFix_E h
  rw [← hE]; exact isPrincipal_add_omega0_opow v

theorem mem_mwC {y x : Ordinal.{0}} : x ∈ mwC a y ↔ y < x ∧ veblen a x ≠ x := Iff.rfl

theorem mwIx_le (a y β : Ordinal.{0}) : mwIx a y β ≤ β := Cd.cdOtp_le_self _ β

/-- **`ind(y + 1 + δ) = δ`** with no fixed point of `φ_a` in `(y, y + 1 + δ)`. -/
theorem mwIx_low {y δ : Ordinal.{0}} (h : ∀ z < δ, veblen a (y + 1 + z) ≠ y + 1 + z) :
    mwIx a y (y + 1 + δ) = δ := by
  unfold mwIx
  rw [phOtp_shift _ _ δ fun z hz => mem_mwC.2 ⟨lt_of_lt_of_le (lt_add_one y) le_self_add, h z hz⟩,
    phOtp_low _ fun c hc => Order.add_one_le_of_lt (mem_mwC.1 hc).1, zero_add]

/-- **`ind(p) = p`** for a fixed point `p > y` of `φ_a`. -/
theorem mwIx_P {y : Ordinal.{0}} : ∀ p, veblen a p = p → y < p → mwIx a y p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hyp
  refine le_antisymm (Cd.cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  by_cases hex : ∃ p', veblen a p' = p' ∧ max α y < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α y).trans_lt hm
      _ = mwIx a y p' := (IH p' hp' hP' ((le_max_right α y).trans_lt hm)).symm
      _ ≤ mwIx a y p := Cd.cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α y < p := max_lt hα hyp
    have hm1 : max α y + 1 < p := by rw [← succ_eq_add_one]; exact (mwFix_lim hP).succ_lt hmp
    have e : max α y + 1 + p = p := (mwFix_prin hP).add_eq_right hm1
    have hsh := phOtp_shift (mwC a y) (max α y + 1) p fun z hz => by
      refine mem_mwC.2 ⟨lt_of_le_of_lt (le_max_right α y) ((lt_add_one _).trans_le le_self_add), fun hz' => ?_⟩
      have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
      have h2 : max α y + 1 + z < max α y + 1 + p := (add_lt_add_iff_left _).2 hz
      rw [e] at h2
      exact absurd h1 (not_le.2 h2)
    rw [e] at hsh
    show α < Cd.cdOtp (mwC a y) p
    rw [hsh]
    exact hα.trans_le le_add_self

/-- **`ind(p + 1 + δ) = p + δ`** for a fixed point `p > y` and no fixed point in `(p, p + 1 + δ)`. -/
theorem mwIx_above {y p δ : Ordinal.{0}} (hP : veblen a p = p) (hyp : y < p)
    (h : ∀ z < δ, veblen a (p + 1 + z) ≠ p + 1 + z) : mwIx a y (p + 1 + δ) = p + δ := by
  have e1 : Cd.cdOtp (mwC a y) p = Cd.cdOtp (mwC a y) (p + 1) :=
    Cd.cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact (mem_mwC.1 hc).2 (hcp' ▸ hP)
  have e2 : Cd.cdOtp (mwC a y) p = p := mwIx_P p hP hyp
  show Cd.cdOtp (mwC a y) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ fun z hz => mem_mwC.2 ⟨hyp.trans ((lt_add_one p).trans_le le_self_add), h z hz⟩,
    ← e1, e2]

/-- **`B_n` keeps the fixed points of `φ_a`** (`B_n a = a`, `a < L(ω)`). -/
theorem mwB_fixA {k : ℕ} (haL : a < Nc.ncL S ω) (hBa : Bc.bcB S k a = a) {y : Ordinal.{0}} (hy : MvD S y)
    (hfix : veblen a y = y) : veblen a (Bc.bcB S k y) = Bc.bcB S k y := by
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hy.1
  have hI : Indec y := by rw [← hfix]; exact mw_veblen_indec _ _
  have hP : (Bc.bcNf S y).isPrin = true := Bc.isPrin_of_indec hN (by rw [hv]; exact hI)
  have hay : a < y := by
    have h1 : a ≤ y := by have := left_le_veblen a y; rwa [hfix] at this
    refine lt_of_le_of_ne h1 fun e => ?_
    have h2 : a < veblen a a := lt_veblen a
    have h3 : veblen a y = y := hfix
    rw [← e] at h3
    rw [h3] at h2
    exact lt_irrefl _ h2
  have hDa : MvD S a := mvD_of_lt haL
  have hBay : a < Bc.bcB S k y := by
    have := (mvB_lt_iff (k := k) hDa hy).2 hay; rwa [hBa] at this
  have key : ∀ t : Term, NF t → Bc.bcD S t → Term.val S t = y → t.isPrin = true →
      veblen a (Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t)) =
        Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t) := by
    intro t hN hD hv hP
    have hBt : Bc.bcB S k y = Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t) := by
      unfold Bc.bcB; rw [← hv, Bc.bcNf_val S hN]
    cases t with
    | zero => simp [Term.isPrin, Term.isSC] at hP
    | add _ _ => simp [Term.isPrin, Term.isSC] at hP
    | phi c d =>
      have hdlt : Term.val S d < Term.val S (Term.phi c d) := (cmp_lt_iff S hN.2.1 hN).1 hN.2.2.2
      have hv' : veblen (Term.val S c) (Term.val S d) = y := hv
      have hmc : a < Term.val S c := by
        have e : veblen a (veblen (Term.val S c) (Term.val S d)) = veblen (Term.val S c) (Term.val S d) := by
          rw [hv']; exact hfix
        rcases veblen_eq_veblen_iff.1 e with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
        · exfalso
          have : Term.val S d = Term.val S (Term.phi c d) := by rw [← h2]; rfl
          exact absurd this hdlt.ne
        · exact h1
        · exfalso
          have : Term.val S d = Term.val S (Term.phi c d) := by rw [← h2, e]; rfl
          exact absurd this hdlt.ne
      have hDc : Bc.bcD S c := ⟨hN.1, hD.2.1⟩
      have hlt := (mvB_lt_iff (k := k) hDa (mvD_of_term hDc)).2 hmc
      rw [hBa, mvB_term hDc] at hlt
      simp only [Bc.bcSig_phi, Term.val]
      exact veblen_veblen_of_lt hlt _
    | _ =>
      have hsc := SC_val S (Bc.bc_NF (k := k) hD) (by rw [Bc.isSC_bcSig]; simpa [Term.isPrin] using hP)
      exact hsc.veblen_right (hBt ▸ hBay)
  unfold Bc.bcB
  exact key _ hN hy.2 hv hP

/-- **`B_n(φ_a(y)) = φ_a(B_n y)`** for `y ∈ MvD`, `a < y`, `φ_a(y) ≠ y`. -/
theorem mwB_veblenA {k : ℕ} (haL : a < Nc.ncL S ω) (hBa : Bc.bcB S k a = a) {y : Ordinal.{0}} (hy : MvD S y)
    (hay : a < y) (hne : veblen a y ≠ y) :
    MvD S (veblen a y) ∧ Bc.bcB S k (veblen a y) = veblen a (Bc.bcB S k y) := by
  have hy' : y < veblen a y := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hne)
  obtain ⟨hD, hB⟩ := mwB_phi (k := k) (mvD_of_lt haL) hy (hay.trans hy') hy'
  exact ⟨hD, by rw [hB, hBa]⟩

/-- **The last fixed point of `φ_a` below `β`.** -/
theorem mwLastA {τ β : Ordinal.{0}} (hτ : veblen a τ = τ) (hτβ : τ < β) (hβ : veblen a β ≠ β) :
    ∃ p, veblen a p = p ∧ τ ≤ p ∧ p < β ∧ ∀ z, p < z → z < β → veblen a z ≠ z := by
  set s : Set Ordinal.{0} := {q | veblen a q = q ∧ τ ≤ q ∧ q < β} with hs
  have hne : s.Nonempty := ⟨τ, hτ, le_rfl, hτβ⟩
  have hbdd : BddAbove s := ⟨β, fun q hq => hq.2.2.le⟩
  have hfix : veblen a (sSup s) = sSup s := by
    rw [(isNormal_veblen a).map_sSup hne hbdd]
    congr 1
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩; rw [hq'.1]; exact hq'
    · intro hq; exact ⟨q, hq, hq.1⟩
  have hle : sSup s ≤ β := csSup_le hne fun q hq => hq.2.2.le
  have hlt : sSup s < β := lt_of_le_of_ne hle fun e => hβ (e ▸ hfix)
  refine ⟨sSup s, hfix, le_csSup hbdd ⟨hτ, le_rfl, hτβ⟩, hlt, fun z hpz hzβ hz => ?_⟩
  have := le_csSup hbdd ⟨hz, (le_csSup hbdd ⟨hτ, le_rfl, hτβ⟩).trans hpz.le, hzβ⟩
  exact absurd hpz (not_lt.2 this)

theorem mwIterA_nfix (p : Ordinal.{0}) :
    ∀ j : ℕ, veblen a ((veblen a)^[j] (p + 1)) ≠ (veblen a)^[j] (p + 1)
  | 0 => mwFix_succ_not (a := a) p
  | j + 1 => by
    intro h
    rw [Function.iterate_succ_apply'] at h
    exact mwIterA_nfix p j ((veblen_injective _) h)

theorem mwIterA_ge (p : Ordinal.{0}) : ∀ j : ℕ, p + 1 ≤ (veblen a)^[j] (p + 1)
  | 0 => le_rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    exact (mwIterA_ge p j).trans (right_le_veblen _ _)

theorem mwIterA_lt {p X : Ordinal.{0}} (hX : veblen a X = X) (hpX : p < X) (j : ℕ) :
    (veblen a)^[j] (p + 1) < X := by
  have hle : (veblen a)^[j] (p + 1) ≤ X :=
    (iterate_le_nfp _ _ j).trans (nfp_le_fp (isNormal_veblen _).strictMono.monotone
      (Order.add_one_le_of_lt hpX) hX.le)
  refine lt_of_le_of_ne hle fun e => mwIterA_nfix (a := a) p j ?_
  rw [e]; exact hX

/-- **`B_n(φ_a^j(p+1)) = φ_a^j(B_n p + 1)`.** -/
theorem mwIterA_B {n : ℕ} (haL : a < Nc.ncL S ω) (hBa : Bc.bcB S n a = a) {p X : Ordinal.{0}}
    (hap : a < p) (hX : veblen a X = X) (hpX : p < X) (hXL : X < Nc.ncL S ω) :
    ∀ j : ℕ, Bc.bcB S n ((veblen a)^[j] (p + 1)) = (veblen a)^[j] (Bc.bcB S n p + 1)
  | 0 => by
    simp only [Function.iterate_zero, id]
    exact mwB_succ (hpX.trans hXL)
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hyX := mwIterA_lt hX hpX j
    have hay : a < (veblen a)^[j] (p + 1) := hap.trans ((lt_add_one p).trans_le (mwIterA_ge p j))
    rw [(mwB_veblenA (k := n) haL hBa (mvD_of_lt (hyX.trans hXL)) hay (mwIterA_nfix (a := a) p j)).2,
      mwIterA_B haL hBa hap hX hpX hXL j]

/-- **The gap moves** (level `a`). -/
theorem mwGapA_move {n : ℕ} (haL : a < Nc.ncL S ω) (hBa : Bc.bcB S n a = a)
    {p δ X : Ordinal.{0}} (hap : a < p) (hX : veblen a X = X) (hβX : p + 1 + δ < X) (hXL : X < Nc.ncL S ω)
    (hgap : ∀ z, z ≤ δ → veblen a (p + 1 + z) ≠ p + 1 + z) :
    ∀ z, z ≤ Bc.bcB S n δ → veblen a (Bc.bcB S n p + 1 + z) ≠ Bc.bcB S n p + 1 + z := by
  set f := veblen a with hf
  have hfm : Monotone f := (isNormal_veblen _).strictMono.monotone
  have hpX : p < X := ((lt_add_one p).trans_le (le_self_add : p + 1 ≤ p + 1 + δ)).trans hβX
  have hδX : δ < X := lt_of_le_of_lt le_add_self hβX
  have hδq : δ < nfp f (p + 1) := by
    by_contra hle
    push Not at hle
    have hqP : veblen a (nfp f (p + 1)) = nfp f (p + 1) := nfp_fp (isNormal_veblen _) _
    have hpq : p + 1 < nfp f (p + 1) :=
      lt_of_le_of_ne (le_nfp _ _) fun e => mwFix_succ_not (a := a) p (by rw [e]; exact hqP)
    have e : p + 1 + nfp f (p + 1) = nfp f (p + 1) := (mwFix_prin hqP).add_eq_right hpq
    exact hgap _ hle (by rw [e]; exact hqP)
  obtain ⟨j, hj⟩ := (lt_nfp_iff (f := f)).1 hδq
  have hjX := mwIterA_lt hX hpX j
  have hBδ : Bc.bcB S n δ < f^[j] (Bc.bcB S n p + 1) := by
    rw [← mwIterA_B (n := n) haL hBa hap hX hpX hXL j]
    exact (Bc.bcB_lt_iff (hδX.trans hXL) (hjX.trans hXL)).2 hj
  intro z hz hP
  set w := Bc.bcB S n p + 1 + z with hw
  have hwq : nfp f (Bc.bcB S n p + 1) ≤ w :=
    nfp_le_fp hfm (by rw [hw]; exact le_self_add) hP.le
  have hzw : z < w :=
    lt_of_le_of_lt hz (hBδ.trans_le ((iterate_le_nfp _ _ j).trans hwq))
  have hpw : Bc.bcB S n p + 1 < w := by
    rcases (le_self_add : Bc.bcB S n p + 1 ≤ w).lt_or_eq with h | h
    · exact h
    · exfalso; exact mwFix_succ_not (a := a) _ (by rw [h]; exact hP)
  have h3 : Bc.bcB S n p + 1 + z < w := mwFix_prin hP hpw hzw
  exact absurd h3 (by rw [← hw]; exact lt_irrefl _)

/-- **`ind_{τ'}(B_n β) = B_n(ind_τ β)`** at the level `a`, with `τ' < B_n β` not a fixed point of `φ_a`. -/
theorem mwIxA_move {n : ℕ} (haL : a < Nc.ncL S ω) (hBa : Bc.bcB S n a = a)
    {τ τ' β X : Ordinal.{0}} (hτ : veblen a τ = τ) (haτ : a < τ)
    (hB : Bc.bcB S n τ = τ') (hτβ : τ < β) (hβ : veblen a β ≠ β) (hX : veblen a X = X) (hβX : β < X)
    (hXL : X < Nc.ncL S ω) :
    τ' < Bc.bcB S n β ∧ veblen a (Bc.bcB S n β) ≠ Bc.bcB S n β ∧
      mwIx a τ' (Bc.bcB S n β) = Bc.bcB S n (mwIx a τ β) := by
  have hL : ∀ {y}, y < X → y < Nc.ncL S ω := fun h => h.trans hXL
  obtain ⟨p, hpP, hτp, hpβ, hmax⟩ := mwLastA hτ hτβ hβ
  obtain ⟨δ, hδ⟩ := exists_add_of_le (Order.add_one_le_of_lt hpβ)
  have hap : a < p := haτ.trans_le hτp
  have hpX : p < X := hpβ.trans hβX
  have hgap : ∀ z, z ≤ δ → veblen a (p + 1 + z) ≠ p + 1 + z := by
    intro z hz
    rcases hz.lt_or_eq with hz | rfl
    · refine hmax _ ((lt_add_one p).trans_le le_self_add) ?_
      rw [hδ]; exact (add_lt_add_iff_left _).2 hz
    · rw [← hδ]; exact hβ
  have hgap' : ∀ z < δ, veblen a (p + 1 + z) ≠ p + 1 + z := fun z hz => hgap z hz.le
  have hβX' : p + 1 + δ < X := hδ ▸ hβX
  have hp1L : p + 1 < Nc.ncL S ω := hL ((le_self_add : p + 1 ≤ p + 1 + δ).trans_lt hβX')
  have hδL : δ < Nc.ncL S ω := hL ((le_add_self : δ ≤ p + 1 + δ).trans_lt hβX')
  have hBβ : Bc.bcB S n β = Bc.bcB S n p + 1 + Bc.bcB S n δ := by
    rw [hδ, Bc.bcB_add hp1L hδL, mwB_succ (hL hpX)]
  have hgapB := mwGapA_move (n := n) haL hBa hap hX hβX' hXL hgap
  have hBP : veblen a (Bc.bcB S n p) = Bc.bcB S n p := mwB_fixA haL hBa (mvD_of_lt (hL hpX)) hpP
  have hτβ' : τ' < Bc.bcB S n β := by
    rw [← hB]; exact (Bc.bcB_lt_iff (hL (hτβ.trans hβX)) (hL hβX)).2 hτβ
  refine ⟨hτβ', by rw [hBβ]; exact hgapB _ le_rfl, ?_⟩
  rcases hτp.lt_or_eq with hlt | heq
  · have hτ'p : τ' < Bc.bcB S n p := by
      rw [← hB]; exact (Bc.bcB_lt_iff (hL (hτp.trans_lt hpβ |>.trans hβX)) (hL hpX)).2 hlt
    rw [hδ, mwIx_above hpP hlt hgap', ← hδ, hBβ, mwIx_above hBP hτ'p fun z hz => hgapB z hz.le,
      Bc.bcB_add (hL hpX) hδL]
  · subst heq
    rw [hδ, mwIx_low hgap', ← hδ, hBβ, hB, mwIx_low fun z hz => by
      have := hgapB z hz.le; rwa [hB] at this]

end Googology.Trans.PoR.InaccPsi.R2.Mw
