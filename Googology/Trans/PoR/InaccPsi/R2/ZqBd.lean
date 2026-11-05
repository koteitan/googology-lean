import Googology.Trans.PoR.InaccPsi.R2.ZqTop
import Googology.Trans.PoR.InaccPsi.R2.ThUp

/-!
# The atom lemma over `Ω_ω` and a narrower leaf

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`,
`P′ = ψ_{Ω₂}(Ω_ω·2)`, `K_Y = ψ_{Ω₂}(Ω_ω + Y₃)`, `G₃ = ψ_{Ω₃}(0)`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

* `zqAtom` (**THE ATOM LEMMA for `θ ≤ s < P′`**: `s = ψ_{Ω₂}(Ω_ω + d)` with `d < Ω_ω`, `Ω_ω + d` in normal form
  and in the hull below `A`, `d ∈ Cl(Ω_ω + d, s)` and in the hull, and every `x ∈ Cl(Ω_ω + d, s)` is a code over
  every strongly critical `Q ≥ s`: `LeCl(Ω₂, Q) x` for `x < G₃`, `UgC₂(Q) x` for `x < Y₃`; the base-`Ω_ω` version
  of `Sn.snCL_atom` / `Ry.ryTh_nf_mem`, which ask `s < θ`);
* `zqB_Pp` (`B_n P′ = P′`), `zqTh_lt_c` (**in a window, every hull element `s < P′` has `Θ_λ(s) < c_{n+1}`**:
  `Th.thTheta_le`);
* `ZqAtHi3 S` (**the narrower leaf**: on the band `K_Y < s < P′` only `B_n s` an atom at `λ'` and the reading
  move are asked), `zqAtHi_of3` (`ZqAtHi3 ⇒ ZqAtHi`), `zqAtHi3_of` (`ZqAtHi ⇒ ZqAtHi3`), `zqTopG3`
  (**`Wr.WrWallCF ∧ ZqAtHi3 ⇒ Zj.ZjTopG`**).

No new axiom.  New definition: the statement name `ZqAtHi3`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Mv
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Zj

variable {S : InaccSeq.{0}}

/-- `W^{Ω_ω} = Ω_ω`. -/
theorem zqWe_OmW : leWe (Om ω) = Om (ω : Ordinal.{0}) := by
  have hW : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hE : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hW
  have hab : Om (1 + 1 : Ordinal.{0}) + Om ω = Om ω := by
    have := Ordinal.add_absorp (a := Om (1 + 1)) (b := Om ω) (c := ω ^ Om ω) (by rw [hE]; exact ldOm2_lt_OmW)
      le_rfl
    rwa [hE] at this
  unfold leWe
  have hm : Om (1 + 1 : Ordinal.{0}) * Om ω = Om ω := by
    rw [← gg_SC_eps ldOm2_SC]
    conv_lhs => rw [← hE]
    rw [← opow_add, hab, hE]
  rw [hm, hE]

/-- **THE ATOM LEMMA FOR `θ ≤ s < P′`.** -/
theorem zqAtom {l ηx s : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hs : s ∈ ldAtR S l) (hθs : ConjT.th S ≤ s) (hsP : s < Nc.ncPp S) :
    ∃ d, d < Om ω ∧ s = S.psi (Om ω + d) (Om (1 + 1)) ∧
      Om ω + d ∈ S.CSet (Om ω + d) (S.psi (Om ω + d) (Om (1 + 1))) ∧
      Om ω + d ∈ cdHull S l ∧ Om ω + d < ConjT.Aη S (cdEta S l) ∧
      d ∈ S.CSet (Om ω + d) s ∧ d ∈ cdHull S l ∧
      (∀ x, x ∈ S.CSet (Om ω + d) s → x < S.psi 0 (Om (1 + 1 + 1)) →
        ∀ Q, SC Q → s ≤ Q → LeCl (Om (1 + 1)) Q x) ∧
      (∀ x, x ∈ S.CSet (Om ω + d) s → x < ugY S → ∀ Q, SC Q → s ≤ Q → UgC S (1 + 1) Q x) := by
  obtain ⟨-, hρ1⟩ := leRho hl hX
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  obtain ⟨D, rfl, hnf, hDH, hDA⟩ := snNf hs hρ1.le
  have hWD : Om ω ≤ D := by
    by_contra h
    push Not at h
    exact absurd hθs (not_le.2 (psi_lt_psi hκ h hnf))
  have hD2 : D < Om ω + Om ω := by
    by_contra h
    push Not at h
    exact absurd hsP (not_lt.2 (psi_mono (S := S) hκ h).1)
  set d := D - Om ω with hd_def
  have hdd : D = Om ω + d := (Ordinal.add_sub_cancel_of_le hWD).symm
  have hdW : d < Om ω := by
    have : Om ω + d < Om ω + Om ω := by rw [← hdd]; exact hD2
    exact (add_lt_add_iff_left _).1 this
  rw [hdd] at hnf hDH hDA ⊢
  have hKd : leWe (Om ω) ∣ Om ω := by rw [zqWe_OmW]
  have hdW' : d < leWe (Om ω) := by rw [zqWe_OmW]; exact hdW
  refine ⟨d, hdW, rfl, hnf, hDH, hDA, snHullRem hnf hKd hdW', snHullRem hDH hKd hdW', ?_, ?_⟩
  · intro x hx hxG Q hQ hsQ
    exact snLeCl_mem hQ hsQ (CSet_mono le_rfl hsQ hx) hxG
  · intro x hx hxY Q hQ hsQ
    exact Uq.uqC_mem hQ hsQ (CSet_mono le_rfl hsQ hx) hxY

/-- `B_n P′ = P′`. -/
theorem zqB_Pp {n : ℕ} : MvD S (Nc.ncPp S) ∧ Bc.bcB S n (Nc.ncPp S) = Nc.ncPp S := by
  obtain ⟨hDW, hBW⟩ := Wr.wrB_OmW (S := S) (n := n)
  obtain ⟨hDa, hBa⟩ := mvB_add (k := n) hDW hDW
  obtain ⟨hDs, hBs⟩ := mxB_atom (n := n) hDa (CSet.add_mem (zjOmW_own _) (ConjT.OmW_mem (S := S) _ _))
  exact ⟨hDs, by unfold Nc.ncPp; rw [hBs, hBa, hBW]⟩

/-- **In a window, every hull element `s < P′` has `Θ_λ(s) < c_{n+1}`.** -/
theorem zqTh_lt_c {n : ℕ} {l s : Ordinal.{0}} (hR : CdRange S l) (hr : cdR S l < Bc.bcC S (n + 1))
    (hsH : s ∈ cdHull S l) (hsP : s < Nc.ncPp S) :
    gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) := by
  have hl := hR.1
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans ((cdR_ge S l).trans_lt hr)
  set E := Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) with hE_def
  have hc2 : Bc.bcC S (n + 1) = Pv S (E + Nc.ncPp S) := by
    show Nc.ncL S ((n + 1 + 1 : ℕ) : Ordinal.{0}) = _
    rw [Lw.lw_L_eq S, Nat.cast_succ (n + 1), mul_add_one, add_assoc]
  have hX : upsilon l < Pv S (E + Nc.ncPp S) := h2.trans_eq hc2
  obtain ⟨-, -, hlt, hpv⟩ := cdEta_pv_spec (S := S) hl.1 hX
  obtain ⟨-, hown⟩ := ldOwnA hl h2
  have hsW : s ≤ Om (1 + 1) := (hsP.trans (psi_lt (InR_Om_succ 1) _)).le
  rw [← ldTheta hl hX hsW]
  set A := ConjT.Aη S (cdEta S l) with hA_def
  have hA : A ∈ S.CSet A (upsilon l) := by rw [← hpv]; exact hown
  refine (Th.thTheta_le hpv hA s).trans_lt ?_
  -- `A + s < A_{E + P′}`
  have hθSC := ConjT.SC_th S
  have hPSC : SC (Nc.ncPp S) := SC_psi (InR_Om_succ 1) _
  have hθP : ConjT.th S < Nc.ncPp S :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (Om_pos omega0_ne_zero)) (zjOmW_own _)
  have hPm : IsPrincipal (· * ·) (Nc.ncPp S) := by
    have e := Low.opow_eq_self_of_SC hPSC
    have h := isPrincipal_mul_omega0_opow_opow (Nc.ncPp S)
    rwa [e, e] at h
  have hθPP : ConjT.th S * Nc.ncPp S = Nc.ncPp S := by
    have eP := Low.opow_eq_self_of_SC hPSC
    have eθ := Low.opow_eq_self_of_SC hθSC
    have hab : ConjT.th S + Nc.ncPp S = Nc.ncPp S := by
      have := Ordinal.add_absorp (a := ConjT.th S) (b := Nc.ncPp S) (c := ω ^ Nc.ncPp S) (by rw [eP]; exact hθP)
        le_rfl
      rwa [eP] at this
    conv_lhs => rw [← eP, ← eθ]
    rw [← opow_add, hab, eP]
  have hkey : ConjT.th S * cdEta S l + s < ConjT.th S * E + Nc.ncPp S := by
    rcases lt_or_ge (cdEta S l) E with hηE | hEη
    · calc ConjT.th S * cdEta S l + s ≤ ConjT.th S * E + s :=
            add_le_add_left ((mul_lt_mul_iff_right₀ hθSC.1).2 hηE).le _
        _ < ConjT.th S * E + Nc.ncPp S := (add_lt_add_iff_left _).2 hsP
    · have hηζ : cdEta S l = E + (cdEta S l - E) := (Ordinal.add_sub_cancel_of_le hEη).symm
      have hζ : cdEta S l - E < Nc.ncPp S := by
        have : E + (cdEta S l - E) < E + Nc.ncPp S := by rw [← hηζ]; exact hlt
        exact (add_lt_add_iff_left _).1 this
      rw [hηζ, mul_add, add_assoc]
      exact (add_lt_add_iff_left _).2 (hPSC.isPrincipal (hPm hθP hζ) hsP)
  have hAlt : A + s < ConjT.Aη S (E + Nc.ncPp S) := by
    show Om ω + ConjT.th S * cdEta S l + s < Om ω + ConjT.th S * (E + Nc.ncPp S)
    rw [add_assoc, mul_add, hθPP]
    exact (add_lt_add_iff_left _).2 hkey
  have hmem : A + s ∈ S.CSet (ConjT.Aη S (E + Nc.ncPp S)) (S.psi (ConjT.Aη S (E + Nc.ncPp S)) (Om 1)) :=
    CSet_mono (le_self_add.trans hAlt.le) hX.le (CSet.add_mem hA hsH)
  rw [hc2]
  exact psi_lt_psi_of_mem Low.InR_Om_one hAlt hmem

/-- **The narrower leaf**: on the band `K_Y < s < P′`, `B_n s` is an atom at `λ'` and the reading moves. -/
def ZqAtHi3 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' →
    ∀ s ∈ ldAtR S l, S.psi (Om ω + ugY S) (Om (1 + 1)) < s → s < Nc.ncPp S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- `ZqAtHi3 ⇒ ZqAtHi` (`B_n s < P′` from `B_n P′ = P′`, `Θ_λ(s) < c_{n+1}` from `zqTh_lt_c`). -/
theorem zqAtHi_of3 (h : ZqAtHi3 S) : ZqAtHi S := by
  intro n l l' hR h1 hr hl' hB s hs hKs hsP IH
  obtain ⟨hDP, hBP⟩ := zqB_Pp (S := S) (n := n)
  obtain ⟨a1, a2, a3⟩ := h n l l' hR h1 hr hl' hB s hs hKs hsP (fun x hx hxs => by
    obtain ⟨b1, b2, -, -, b5⟩ := IH x hx hxs
    exact ⟨b1, b2, b5⟩)
  have hX := (Wr.wrWin hR h1 hr hl' hB).1
  have hsH : s ∈ cdHull S l := (ldHull_iff hR.1 hX (hsP.trans (psi_lt (InR_Om_succ 1) _))).2 (GxCl.atom hs)
  refine ⟨a1, a2, ?_, zqTh_lt_c hR hr hsH hsP, a3⟩
  have := (mvB_lt_iff (k := n) a1 hDP).2 hsP
  rwa [hBP] at this

/-- `ZqAtHi ⇒ ZqAtHi3` (the codes below `s < P′` have `B_n x < P′` and `Θ_λ(x) < c_{n+1}`). -/
theorem zqAtHi3_of (h : ZqAtHi S) : ZqAtHi3 S := by
  intro n l l' hR h1 hr hl' hB s hs hKs hsP IH
  obtain ⟨hDP, hBP⟩ := zqB_Pp (S := S) (n := n)
  have hX := (Wr.wrWin hR h1 hr hl' hB).1
  obtain ⟨a1, a2, -, -, a5⟩ := h n l l' hR h1 hr hl' hB s hs hKs hsP (fun x hx hxs => by
    obtain ⟨b1, b2, b5⟩ := IH x hx hxs
    have hxP := hxs.trans hsP
    have hxH : x ∈ cdHull S l := (ldHull_iff hR.1 hX (hxP.trans (psi_lt (InR_Om_succ 1) _))).2 hx
    refine ⟨b1, b2, ?_, zqTh_lt_c hR hr hxH hxP, b5⟩
    have := (mvB_lt_iff (k := n) b1 hDP).2 hxP
    rwa [hBP] at this)
  exact ⟨a1, a2, a5⟩

theorem zqAtHi3_iff : ZqAtHi3 S ↔ ZjAtK S (Nc.ncPp S) :=
  ⟨fun h => zqAtK_Pp (zqAtHi_of3 h), fun h => zqAtHi3_of (zqAtHi_of h)⟩

/-- **`Wr.WrWallCF ∧ ZqAtHi3 ⇒ Zj.ZjTopG`.** -/
theorem zqTopG3 (hW : Wr.WrWallCF S) (h : ZqAtHi3 S) : ZjTopG S := zqTopG hW (zqAtHi_of3 h)

end Googology.Trans.PoR.InaccPsi.R2.Zq
