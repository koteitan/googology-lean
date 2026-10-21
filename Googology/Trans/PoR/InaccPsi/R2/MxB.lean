import Googology.Trans.PoR.InaccPsi.R2.MwOm

/-!
# `B_n` and the Veblen levels that move: fixed points, iterates, gaps and indices at a level `a ↦ B_n a`

`B_n = Bc.bcB S n` (`σ_n` on normal forms), `φ_a = veblen a`.  `R2.MwAlev` moved the fixed points, the gaps and the
index off the fixed points of `φ_a` for a level with `B_n a = a`; here the level itself moves, `a ↦ B_n a`, and the
start of the index set is any non-fixed `s` (`s = y + 1`, `0` or `1` in the uses).

* `mxB_SC_iff` (**`B_n x` is strongly critical iff `x` is**, on `[0, L(ω))`: the normal form keeps `isSC`);
* `mxB_fix` (**`φ_a(y) = y` gives `φ_{B_n a}(B_n y) = B_n y`**);
* `mxIter_B` (**`B_n(φ_a^j(s)) = φ_{B_n a}^j(B_n s)`** for a non-fixed start `s` with `a < φ_a(s)`), `mxGap_move`
  (**no fixed point of `φ_a` in `[s, s + δ]` gives none of `φ_{B_n a}` in `[B_n s, B_n s + B_n δ]`**);
* `mxC a s = {x | s ≤ x, φ_a(x) ≠ x}`, `mxIx a s b = otp(mxC a s ∩ b)`; `mxIx_low` (**`ind(s + δ) = δ`**), `mxIx_P`
  (**`ind(p) = p`** for a fixed point `p > s`), `mxIx_above` (**`ind(p + 1 + δ) = p + δ`**);
* `mxLast` (the last fixed point in `[s, b)`), `mxIx_move` (**`ind_{B_n a, B_n s}(B_n b) = B_n(ind_{a, s}(b))`**).

No new axiom.  New definitions: `mxC`, `mxIx`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ph Googology.Trans.PoR.InaccPsi.R2.Mw

variable {S : InaccSeq.{0}}

/-- **`B_n x` is strongly critical iff `x` is** (`x < L(ω)`). -/
theorem mxB_SC_iff {k : ℕ} {x : Ordinal.{0}} (hx : x < Nc.ncL S ω) : SC (Bc.bcB S k x) ↔ SC x := by
  have hD := Bc.bcD_nf S hx
  have hv : val S (Bc.bcNf S x) = x := Bc.val_nf S hx
  have hN : NF (Bc.bcNf S x) := hD.1
  have hN' : NF (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW (Bc.bcNf S x)) := Bc.bc_NF (k := k) hD
  have hB : Bc.bcB S k x = val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW (Bc.bcNf S x)) := rfl
  constructor
  · intro h
    rw [hB] at h
    have h1 := isSC_of_SC S hN' h
    rw [Bc.isSC_bcSig] at h1
    have := SC_val S hN h1
    rwa [hv] at this
  · intro h
    rw [hB]
    refine SC_val S hN' ?_
    rw [Bc.isSC_bcSig]
    exact isSC_of_SC S hN (by rw [hv]; exact h)

/-- **`φ_a(y) = y` gives `φ_{B_n a}(B_n y) = B_n y`** (`a < L(ω)`, `y ∈ MvD`). -/
theorem mxB_fix {k : ℕ} {a y : Ordinal.{0}} (haL : a < Nc.ncL S ω) (hy : MvD S y) (hfix : veblen a y = y) :
    veblen (Bc.bcB S k a) (Bc.bcB S k y) = Bc.bcB S k y := by
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
  have hBay : Bc.bcB S k a < Bc.bcB S k y := (mvB_lt_iff (k := k) hDa hy).2 hay
  have key : ∀ t : Term, NF t → Bc.bcD S t → Term.val S t = y → t.isPrin = true →
      veblen (Bc.bcB S k a) (Term.val S (Bc.bcSig (Bc.bcPre (k + 1)) Bc.bcPreW t)) =
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
      rw [mvB_term hDc] at hlt
      simp only [Bc.bcSig_phi, Term.val]
      exact veblen_veblen_of_lt hlt _
    | _ =>
      have hsc := SC_val S (Bc.bc_NF (k := k) hD) (by rw [Bc.isSC_bcSig]; simpa [Term.isPrin] using hP)
      exact hsc.veblen_right (hBt ▸ hBay)
  unfold Bc.bcB
  exact key _ hN hy.2 hv hP

/-- **`B_n(φ_a(y)) = φ_{B_n a}(B_n y)`** for `a, y < L(ω)` with `a, y < φ_a(y)`. -/
theorem mxB_veblen {k : ℕ} {a y : Ordinal.{0}} (haL : a < Nc.ncL S ω) (hyL : y < Nc.ncL S ω)
    (h1 : a < veblen a y) (h2 : y < veblen a y) :
    Bc.bcB S k (veblen a y) = veblen (Bc.bcB S k a) (Bc.bcB S k y) :=
  (mwB_phi (k := k) (mvD_of_lt haL) (mvD_of_lt hyL) h1 h2).2

/-! ## Iterates from a non-fixed start -/

section Iter

variable {a : Ordinal.{0}}

theorem mxIter_nfix {s : Ordinal.{0}} (hs : veblen a s ≠ s) :
    ∀ j : ℕ, veblen a ((veblen a)^[j] s) ≠ (veblen a)^[j] s
  | 0 => hs
  | j + 1 => by
    intro h
    rw [Function.iterate_succ_apply'] at h
    exact mxIter_nfix hs j ((veblen_injective _) h)

theorem mxIter_ge (s : Ordinal.{0}) : ∀ j : ℕ, s ≤ (veblen a)^[j] s
  | 0 => le_rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    exact (mxIter_ge s j).trans (right_le_veblen _ _)

theorem mxIter_lt {s X : Ordinal.{0}} (hs : veblen a s ≠ s) (hX : veblen a X = X) (hsX : s < X) (j : ℕ) :
    (veblen a)^[j] s < X := by
  have hle : (veblen a)^[j] s ≤ X :=
    (iterate_le_nfp _ _ j).trans (nfp_le_fp (isNormal_veblen _).strictMono.monotone hsX.le hX.le)
  refine lt_of_le_of_ne hle fun e => mxIter_nfix hs j ?_
  rw [e]; exact hX

/-- **`B_n(φ_a^j(s)) = φ_{B_n a}^j(B_n s)`** for a non-fixed start `s` with `a < φ_a(s)`, below a fixed point
`X < L(ω)`. -/
theorem mxIter_B {n : ℕ} (haL : a < Nc.ncL S ω) {s X : Ordinal.{0}} (hs : veblen a s ≠ s)
    (has : a < veblen a s) (hX : veblen a X = X) (hsX : s < X) (hXL : X < Nc.ncL S ω) :
    ∀ j : ℕ, Bc.bcB S n ((veblen a)^[j] s) = (veblen (Bc.bcB S n a))^[j] (Bc.bcB S n s)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hyX := mxIter_lt hs hX hsX j
    set y := (veblen a)^[j] s with hy
    have hy1 : a < veblen a y :=
      has.trans_le ((veblen_le_veblen_iff_right).2 (mxIter_ge s j))
    have hy2 : y < veblen a y := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm (mxIter_nfix hs j))
    rw [mxB_veblen (k := n) haL (hyX.trans hXL) hy1 hy2, mxIter_B haL hs has hX hsX hXL j]

/-- **The gap moves**: no fixed point of `φ_a` in `[s, s + δ]` gives none of `φ_{B_n a}` in `[B_n s, B_n s + B_n δ]`. -/
theorem mxGap_move {n : ℕ} (haL : a < Nc.ncL S ω) {s δ X : Ordinal.{0}} (hs : veblen a s ≠ s)
    (hs' : veblen (Bc.bcB S n a) (Bc.bcB S n s) ≠ Bc.bcB S n s) (has : a < veblen a s)
    (hX : veblen a X = X) (hβX : s + δ < X) (hXL : X < Nc.ncL S ω)
    (hgap : ∀ z, z ≤ δ → veblen a (s + z) ≠ s + z) :
    ∀ z, z ≤ Bc.bcB S n δ →
      veblen (Bc.bcB S n a) (Bc.bcB S n s + z) ≠ Bc.bcB S n s + z := by
  set f := veblen a with hf
  set f' := veblen (Bc.bcB S n a) with hf'
  have hfm : Monotone f' := (isNormal_veblen _).strictMono.monotone
  have hsX : s < X := lt_of_le_of_lt le_self_add hβX
  have hδX : δ < X := lt_of_le_of_lt le_add_self hβX
  have hδq : δ < nfp f s := by
    by_contra hle
    push Not at hle
    have hqP : veblen a (nfp f s) = nfp f s := nfp_fp (isNormal_veblen _) _
    have hsq : s < nfp f s := lt_of_le_of_ne (le_nfp _ _) fun e => hs (by rw [e]; exact hqP)
    have e : s + nfp f s = nfp f s := (mwFix_prin hqP).add_eq_right hsq
    exact hgap _ hle (by rw [e]; exact hqP)
  obtain ⟨j, hj⟩ := (lt_nfp_iff (f := f)).1 hδq
  have hjX := mxIter_lt hs hX hsX j
  have hBδ : Bc.bcB S n δ < f'^[j] (Bc.bcB S n s) := by
    rw [← mxIter_B (n := n) haL hs has hX hsX hXL j]
    exact (Bc.bcB_lt_iff (hδX.trans hXL) (hjX.trans hXL)).2 hj
  intro z hz hP
  set w := Bc.bcB S n s + z with hw
  have hwq : nfp f' (Bc.bcB S n s) ≤ w := nfp_le_fp hfm (by rw [hw]; exact le_self_add) hP.le
  have hzw : z < w := lt_of_le_of_lt hz (hBδ.trans_le ((iterate_le_nfp _ _ j).trans hwq))
  have hpw : Bc.bcB S n s < w := by
    rcases (le_self_add : Bc.bcB S n s ≤ w).lt_or_eq with h | h
    · exact h
    · exfalso; exact hs' (by rw [h]; exact hP)
  have h3 : Bc.bcB S n s + z < w := mwFix_prin hP hpw hzw
  exact absurd h3 (by rw [← hw]; exact lt_irrefl _)

end Iter

/-! ## The index of `b` among the non-fixed points of `φ_a` from `s` on -/

/-- The ordinals `x ≥ s` that are not fixed points of `φ_a`. -/
def mxC (a s : Ordinal.{0}) : Set Ordinal.{0} := {x | s ≤ x ∧ veblen a x ≠ x}

/-- The index of `b` in `mxC a s`. -/
noncomputable def mxIx (a s b : Ordinal.{0}) : Ordinal.{0} := Cd.cdOtp (mxC a s) b

section Index

variable {a s : Ordinal.{0}}

theorem mem_mxC {x : Ordinal.{0}} : x ∈ mxC a s ↔ s ≤ x ∧ veblen a x ≠ x := Iff.rfl

theorem mxIx_le (a s b : Ordinal.{0}) : mxIx a s b ≤ b := Cd.cdOtp_le_self _ b

/-- **`ind(s + δ) = δ`** with no fixed point of `φ_a` in `[s, s + δ)`. -/
theorem mxIx_low {δ : Ordinal.{0}} (h : ∀ z < δ, veblen a (s + z) ≠ s + z) : mxIx a s (s + δ) = δ := by
  unfold mxIx
  rw [phOtp_shift _ _ δ fun z hz => mem_mxC.2 ⟨le_self_add, h z hz⟩,
    phOtp_low _ fun c hc => (mem_mxC.1 hc).1, zero_add]

/-- **`ind(p) = p`** for a fixed point `p > s` of `φ_a`. -/
theorem mxIx_P : ∀ p, veblen a p = p → s < p → mxIx a s p = p := by
  intro p
  induction p using WellFoundedLT.induction with
  | ind p IH =>
  intro hP hsp
  refine le_antisymm (Cd.cdOtp_le_self _ p) (le_of_forall_lt fun α hα => ?_)
  by_cases hex : ∃ p', veblen a p' = p' ∧ max α s < p' ∧ p' < p
  · obtain ⟨p', hP', hm, hp'⟩ := hex
    calc α < p' := (le_max_left α s).trans_lt hm
      _ = mxIx a s p' := (IH p' hp' hP' ((le_max_right α s).trans_lt hm)).symm
      _ ≤ mxIx a s p := Cd.cdOtp_mono _ hp'.le
  · push Not at hex
    have hmp : max α s < p := max_lt hα hsp
    have hm1 : max α s + 1 < p := by rw [← succ_eq_add_one]; exact (mwFix_lim hP).succ_lt hmp
    have e : max α s + 1 + p = p := (mwFix_prin hP).add_eq_right hm1
    have hsh := phOtp_shift (mxC a s) (max α s + 1) p fun z hz => by
      refine mem_mxC.2 ⟨(le_max_right α s).trans ((lt_add_one _).le.trans le_self_add), fun hz' => ?_⟩
      have h1 := hex _ hz' ((lt_add_one _).trans_le le_self_add)
      have h2 : max α s + 1 + z < max α s + 1 + p := (add_lt_add_iff_left _).2 hz
      rw [e] at h2
      exact absurd h1 (not_le.2 h2)
    rw [e] at hsh
    show α < Cd.cdOtp (mxC a s) p
    rw [hsh]
    exact hα.trans_le le_add_self

/-- **`ind(p + 1 + δ) = p + δ`** for a fixed point `p > s` and no fixed point in `(p, p + 1 + δ)`. -/
theorem mxIx_above {p δ : Ordinal.{0}} (hP : veblen a p = p) (hsp : s < p)
    (h : ∀ z < δ, veblen a (p + 1 + z) ≠ p + 1 + z) : mxIx a s (p + 1 + δ) = p + δ := by
  have e1 : Cd.cdOtp (mxC a s) p = Cd.cdOtp (mxC a s) (p + 1) :=
    Cd.cdOtp_eq_of_gap _ le_self_add fun c hc hpc hcp => by
      have hcp' : c = p := le_antisymm (Order.lt_add_one_iff.1 hcp) hpc
      exact (mem_mxC.1 hc).2 (hcp' ▸ hP)
  have e2 : Cd.cdOtp (mxC a s) p = p := mxIx_P p hP hsp
  show Cd.cdOtp (mxC a s) (p + 1 + δ) = p + δ
  rw [phOtp_shift _ _ δ fun z hz => mem_mxC.2 ⟨hsp.le.trans ((lt_add_one p).le.trans le_self_add), h z hz⟩,
    ← e1, e2]

/-- **The last fixed point of `φ_a` in `[s, b)`**, when there is one and `b` is not fixed. -/
theorem mxLast {b : Ordinal.{0}} (hb : veblen a b ≠ b) (hex : ∃ q, veblen a q = q ∧ s ≤ q ∧ q < b) :
    ∃ p, veblen a p = p ∧ s ≤ p ∧ p < b ∧ ∀ z, p < z → z < b → veblen a z ≠ z := by
  set T : Set Ordinal.{0} := {q | veblen a q = q ∧ s ≤ q ∧ q < b} with hT
  have hne : T.Nonempty := hex
  have hbdd : BddAbove T := ⟨b, fun q hq => hq.2.2.le⟩
  have hfix : veblen a (sSup T) = sSup T := by
    rw [(isNormal_veblen a).map_sSup hne hbdd]
    congr 1
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩; rw [hq'.1]; exact hq'
    · intro hq; exact ⟨q, hq, hq.1⟩
  obtain ⟨q0, hq0⟩ := hne
  have hle : sSup T ≤ b := csSup_le ⟨q0, hq0⟩ fun q hq => hq.2.2.le
  have hlt : sSup T < b := lt_of_le_of_ne hle fun e => hb (e ▸ hfix)
  refine ⟨sSup T, hfix, hq0.2.1.trans (le_csSup hbdd hq0), hlt, fun z hpz hzb hz => ?_⟩
  have := le_csSup hbdd ⟨hz, (hq0.2.1.trans (le_csSup hbdd hq0)).trans hpz.le, hzb⟩
  exact absurd hpz (not_lt.2 this)

/-- **`ind_{B_n a, B_n s}(B_n b) = B_n(ind_{a, s}(b))`**, with `B_n s ≤ B_n b` and `B_n b` not a fixed point of
`φ_{B_n a}`; for a non-fixed start `s` with `a < φ_a(s)` whose image `B_n s` is not a fixed point of `φ_{B_n a}`, a
non-fixed `b ≥ s` and a fixed point `X` of `φ_a` with `b < X < L(ω)`. -/
theorem mxIx_move {n : ℕ} (haL : a < Nc.ncL S ω) {b X : Ordinal.{0}} (hs : veblen a s ≠ s)
    (hs' : veblen (Bc.bcB S n a) (Bc.bcB S n s) ≠ Bc.bcB S n s) (has : a < veblen a s) (hsb : s ≤ b)
    (hb : veblen a b ≠ b) (hX : veblen a X = X) (hbX : b < X) (hXL : X < Nc.ncL S ω) :
    Bc.bcB S n s ≤ Bc.bcB S n b ∧ veblen (Bc.bcB S n a) (Bc.bcB S n b) ≠ Bc.bcB S n b ∧
      mxIx (Bc.bcB S n a) (Bc.bcB S n s) (Bc.bcB S n b) = Bc.bcB S n (mxIx a s b) := by
  have hL : ∀ {y}, y < X → y < Nc.ncL S ω := fun h => h.trans hXL
  have hsbB : Bc.bcB S n s ≤ Bc.bcB S n b := Tp.tpB_le (hL hbX) hsb
  by_cases hex : ∃ q, veblen a q = q ∧ s ≤ q ∧ q < b
  · obtain ⟨p, hpP, hsp, hpb, hmax⟩ := mxLast hb hex
    have hsp' : s < p := lt_of_le_of_ne hsp fun e => hs (e ▸ hpP)
    obtain ⟨δ, hδ⟩ := exists_add_of_le (Order.add_one_le_of_lt hpb)
    have hpX : p < X := hpb.trans hbX
    have hgap : ∀ z, z ≤ δ → veblen a (p + 1 + z) ≠ p + 1 + z := by
      intro z hz
      rcases hz.lt_or_eq with hz | rfl
      · refine hmax _ ((lt_add_one p).trans_le le_self_add) ?_
        rw [hδ]; exact (add_lt_add_iff_left _).2 hz
      · rw [← hδ]; exact hb
    have hβX' : p + 1 + δ < X := hδ ▸ hbX
    have hp1L : p + 1 < Nc.ncL S ω := hL ((le_self_add : p + 1 ≤ p + 1 + δ).trans_lt hβX')
    have hδL : δ < Nc.ncL S ω := hL ((le_add_self : δ ≤ p + 1 + δ).trans_lt hβX')
    have hBβ : Bc.bcB S n b = Bc.bcB S n p + 1 + Bc.bcB S n δ := by
      rw [hδ, Bc.bcB_add hp1L hδL, mwB_succ (hL hpX)]
    have hap : a ≤ p := by have := left_le_veblen a p; rwa [hpP] at this
    have has1 : a < veblen a (p + 1) := hap.trans_lt (by
      calc p = veblen a p := hpP.symm
        _ < veblen a (p + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one p))
    have hs1' : veblen (Bc.bcB S n a) (Bc.bcB S n (p + 1)) ≠ Bc.bcB S n (p + 1) := by
      rw [mwB_succ (hL hpX)]; exact mwFix_succ_not _
    have hgapB := mxGap_move (n := n) haL (mwFix_succ_not p) hs1' has1 hX hβX' hXL hgap
    rw [mwB_succ (hL hpX)] at hgapB
    have hBP : veblen (Bc.bcB S n a) (Bc.bcB S n p) = Bc.bcB S n p :=
      mxB_fix haL (mvD_of_lt (hL hpX)) hpP
    have hs'p : Bc.bcB S n s < Bc.bcB S n p :=
      (Bc.bcB_lt_iff (hL (hsp.trans_lt hpX)) (hL hpX)).2 hsp'
    refine ⟨hsbB, by rw [hBβ]; exact hgapB _ le_rfl, ?_⟩
    rw [hδ, mxIx_above hpP hsp' fun z hz => hgap z hz.le, ← hδ, hBβ,
      mxIx_above hBP hs'p fun z hz => hgapB z hz.le, Bc.bcB_add (hL hpX) hδL]
  · push Not at hex
    obtain ⟨δ, hδ⟩ := exists_add_of_le hsb
    have hgap : ∀ z, z ≤ δ → veblen a (s + z) ≠ s + z := by
      intro z hz hfz
      rcases hz.lt_or_eq with hz | rfl
      · exact absurd (hδ ▸ (add_lt_add_iff_left s).2 hz) (not_lt.2 (hex _ hfz le_self_add))
      · exact hb (hδ ▸ hfz)
    have hβX' : s + δ < X := hδ ▸ hbX
    have hsL : s < Nc.ncL S ω := hL ((le_self_add : s ≤ s + δ).trans_lt hβX')
    have hδL : δ < Nc.ncL S ω := hL ((le_add_self : δ ≤ s + δ).trans_lt hβX')
    have hBβ : Bc.bcB S n b = Bc.bcB S n s + Bc.bcB S n δ := by rw [hδ, Bc.bcB_add hsL hδL]
    have hgapB := mxGap_move (n := n) haL hs hs' has hX hβX' hXL hgap
    refine ⟨hsbB, by rw [hBβ]; exact hgapB _ le_rfl, ?_⟩
    rw [hδ, mxIx_low fun z hz => hgap z hz.le, ← hδ, hBβ, mxIx_low fun z hz => hgapB z hz.le]

end Index

end Googology.Trans.PoR.InaccPsi.R2.Mx
