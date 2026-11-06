import Googology.Trans.PoR.InaccPsi.R2.KzTr

/-!
# Kz: THE UPPER BOUND BELOW A BOUND `K` (`Xd.xdUp_at` on `D_K`)

* `vbTK_le_self` (**`T_K x ≤ x`**, from `κ y ≥ y`, `Kz.kzL_ge_self`);
* `kzUp_at` (**`Θ(ψ₂ a) ≤ ψ₁(A + 1 + ψ₂(T_K a))` for every `a ∈ D_K` below `A`**: the proof of `Xd.xdUp_at`, the
  arguments `e < a` bounded through `T_K e ≤ e < a < A`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Xd

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- **`T_K x ≤ x`.** -/
theorem vbTK_le_self {x : Ordinal.{0}} (hx : VbDK S l K x) : vbTK S l K x ≤ x := by
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hx
  have h := kzL_ge_self (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _) hKB _ hE
  exact h.trans_eq hK

/-- **THE UPPER BOUND AT EVERY MEMBER OF THE DOMAIN**: `Θ(ψ₂(a)) ≤ ψ₁(A + 1 + ψ₂(T a))`. -/
theorem kzUp_at {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    ∀ a, VbDK S l K a → a < A → gxTh (upsilon l) (ldAtR S l) (S.psi a (Om (1 + 1))) ≤
      S.psi (A + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1) := by
  obtain ⟨-, rfl⟩ := Wg.wgOwnEta hl hX hA hρ
  obtain ⟨hρSC, hρ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAω : Om ω ≤ ConjT.Aη S (cdEta S l) := by unfold ConjT.Aη; exact le_self_add
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IHo =>
  intro ha haA
  have hσSC : SC (S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1)) :=
    SC_psi Low.InR_Om_one _
  have hρσ : upsilon l < S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1) := by
    rw [← hρ]
    exact (mxPsi_succ_gt hA).trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1
  have hTa_lt : ∀ e, VbDK S l K e → e < a →
      vbTK S l K e < ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1)) := fun e he hea =>
    ((vbTK_le_self hl hX hKB he).trans_lt (hea.trans haA)).trans_le (le_self_add.trans le_self_add)
  have hin : ∀ t, t ∈ ldAtR S l → t < S.psi a (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) t <
      S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1) := by
    intro t
    induction t using WellFoundedLT.induction with
    | ind t IHi =>
    intro ht hta
    obtain ⟨a0, ha0C, ha0A, ht0⟩ := ht
    have hth : S.psi a (Om (1 + 1)) < S.psi K (Om (1 + 1)) :=
      psi_lt_psi_of_mem (InR_Om_succ 1) ha.2.2 ha.2.1
    have hb1 := psiS_bounds (S := S) a0 1
    rw [← ht0] at hb1
    have hVt : VbDK S l K t := by
      refine ⟨?_, CSet.of_lt (hta.trans hth),
        (hb1.2.trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))).trans_le hKB.ge⟩
      rw [ht0]; exact CSet.psi_mem ha0A (InR_Om_succ 1) (xdOm2_mem _ _) ha0C
    have hne : ¬ ∃ j : ℕ, t = Om (j : Ordinal.{0}) := fun ⟨j, hj⟩ => not_Om_of_between hb1.1 hb1.2 _ hj
    have htW : t ≠ Om ω := fun e => by
      rw [e] at hb1
      exact absurd (hb1.2.trans (Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0))) (lt_irrefl _)
    obtain ⟨k, hk, d, hdE, hdn, hxd, -⟩ :=
      kzE_atom hKB hρ1.le (vbDK_E hl hX hVt) (ht0 ▸ SC_psi (InR_Om_succ 1) a0) hb1.1
        (kzNe hKB (vbDK_E hl hX hVt) hne htW)
    have hbk := psiS_bounds (S := S) d (k : Ordinal.{0})
    rw [← hxd] at hbk
    have hk1 : (k : Ordinal.{0}) = 1 := between_unique hbk.1 hbk.2 hb1.1 hb1.2
    have hdD : VbDK S l K d := vbDK_atom hl hX (hxd ▸ hVt) hdE hdn hk
    rw [hk1] at hxd hdn
    have hlt : S.psi d (Om (1 + 1)) < S.psi a (Om (1 + 1)) := hxd ▸ hta
    have hda : d < a := by
      by_contra hc
      exact absurd hlt (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) (not_lt.1 hc)).1)
    have hO := IHo d hda hdD (hda.trans haA)
    -- the codes of `d` are read below `σ(a)`
    have hatoms : ∀ s ∈ ldAtR S l, s < S.psi d (Om (1 + 1)) → gxTh (upsilon l) (ldAtR S l) s <
        S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1) :=
      fun s hs hsd => IHi s (hxd ▸ hsd) hs (hsd.trans hlt)
    have hTdC : vbTK S l K d ∈ S.CSet (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1)))
        (S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1)) := by
      refine kzT_cl hl hX hKB (psi_lt (InR_Om_succ 1) d).le (fun e he hed => hTa_lt e he (hed.trans hda))
        (fun c hc hc2 hcC => ?_) d hdD hdn
      rw [vbTK_code hl hX hKB hc2 hc.1]
      exact CSet.of_lt (mxGx_bound hρSC hρ1 hAt hσSC hρσ hatoms c ((ldHull_iff hl hX hc2).1 hc.1)
        (lt_psi_of_mem (InR_Om_succ 1) hcC hc2))
    have hB : ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K d) (Om (1 + 1)) <
        ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1)) :=
      (add_lt_add_iff_left _).2 (kzT_psi_lt hl hX hKB ha hdD hdn hlt)
    have hBm : ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K d) (Om (1 + 1)) ∈
        S.CSet (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1)))
          (S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbTK S l K a) (Om (1 + 1))) (Om 1)) := by
      refine CSet.add_mem (CSet.add_mem ?_ (CSet.one_mem _ _))
        (CSet.psi_mem (hTa_lt d hdD hda) (InR_Om_succ 1) (xdOm2_mem _ _) hTdC)
      exact (psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hA
    rw [hxd]
    exact hO.trans_lt (psi_lt_psi_of_mem Low.InR_Om_one hB hBm)
  exact ldAtom_le hρSC hρ1 hAt hσSC hρσ hin

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Kz
