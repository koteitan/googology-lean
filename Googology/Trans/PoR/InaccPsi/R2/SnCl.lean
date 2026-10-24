import Googology.Trans.PoR.InaccPsi.R2.SjAtX
import Googology.Trans.PoR.InaccPsi.R2.RyNF

/-!
# The closure condition at normal-form atoms: `Cl → LeCl`

`G₃ = ψ_{Ω₃}(0)`, `W^E = Ω₂^E` (`Le.leWe`), codes over `Q` = `Le.LeCl Ω₂ Q`.

* `snKey` (**THE KEY INDUCTION OF `Le.lePsi_le`, RESTATED**: if `ψ_{Ω₂}(e) < Q` for every `e < a` in `Cl(a, Q)`,
  then `x % G₃` is a code over `Q` for every `x ∈ Cl(a, Q)`);
* `snColl` (the collapse hypothesis holds at every strongly critical `Q ≥ ψ_{Ω₂}(a)`), `snLeCl_mem` (**every
  `x ∈ Cl(a, Q)` below `G₃` is a code over `Q`, for every strongly critical `Q ≥ ψ_{Ω₂}(a)`**);
* `snLogLast` (a code `p + ω^c` has a code exponent `c`), `snLogLastW` (a code `p + W^Y` has a code `Y`);
* `snCL_nf` (**THE CLOSURE CONDITION AT A NORMAL-FORM ATOM**: if `a = β + W^{X₀ + W^E}` is in `Cl(a, ψ_{Ω₂}(a))`
  and `X₀ + W^E < G₃`, then `E` and `X₀ + W^E` are codes over every strongly critical `Q ≥ ψ_{Ω₂}(a)`);
* `snCL_atom` (the same for every atom `s < θ` of a hull: `s = ψ_{Ω₂}(d)` with `d` in normal form, in the hull,
  `d < A`, and every member of `Cl(d, s)` below `G₃` is a code over every strongly critical `Q ≥ s`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Sj

variable {S : InaccSeq.{0}}

/-- **The key induction of `Le.lePsi_le` at `κ = Ω₂`, with the collapse hypothesis asked only at members of
`Cl(a, Q)`.** -/
theorem snKey {a Q : Ordinal.{0}} (hQ : SC Q) (hΩQ : Om 1 < Q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a Q → S.psi e (Om (1 + 1)) < Q) :
    ∀ x ∈ S.CSet a Q, LeCl (Om (1 + 1)) Q (x % S.psi 0 (Om (1 + 1 + 1))) := by
  set κ := Om (1 + 1 : Ordinal.{0}) with hκ_def
  set G := S.psi 0 (Om (1 + 1 + 1)) with hG_def
  have hGSC : SC G := SC_psi (InR_Om_succ (1 + 1)) 0
  have hG2 : G < Om (1 + 1 + 1) := psi_lt (InR_Om_succ (1 + 1)) 0
  have hQ0 : 0 < Q := hQ.1
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < G → LeCl κ Q p) → LeCl κ Q (p % G) := by
    intro p hp h
    rcases ldModK_prin hGSC hp with ⟨hpG, e⟩ | e
    · rw [e]; exact h hpG
    · rw [e]; exact LeCl.zero hQ0
  have hIG : ∀ n, G < S.I n := fun n => hG2.trans (leOm3_lt_I n)
  intro x hx
  induction hx with
  | small h => exact LeCl.small ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact LeCl.zero hQ0
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal fun h => absurd (h.trans (hIG n)) (lt_irrefl _)
  | inaccW =>
    exact prin (SC_Iw (S := S)).isPrincipal fun h =>
      absurd (h.trans ((hIG 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0))) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y G with hy | hy
    · rw [ldModK_add_lt hGSC x hy]
      have hy' : LeCl κ Q y := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
      exact LeCl.add ihx hy'
    · rw [ldModK_add_ge hGSC x hy]; exact ihy
  | @phi x y _ _ ihx ihy =>
    refine prin (Ph.ph_veblen_prin x y) fun h => ?_
    have hx1 : x < G := lt_of_le_of_lt (left_le_veblen x y) h
    have hy1 : y < G := lt_of_le_of_lt (right_le_veblen x y) h
    rw [Ordinal.mod_eq_of_lt hx1] at ihx
    rw [Ordinal.mod_eq_of_lt hy1] at ihy
    exact LeCl.phi ihx ihy
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact LeCl.zero hQ0
    refine prin (Om_isPrincipal hx0) fun h => ?_
    rcases lt_trichotomy x (1 + 1) with hx | hx | hx
    · refine LeCl.small (lt_of_le_of_lt (Om_le_Om.2 ?_) hΩQ)
      rw [← Order.succ_eq_add_one] at hx; exact Order.lt_succ_iff.1 hx
    · rw [hx]; exact LeCl.om
    · exfalso
      have h2 : (1 + 1 + 1 : Ordinal.{0}) ≤ x := by
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hx
      exact absurd (h.trans hG2) (not_lt.2 (Om_le_Om.2 h2))
  | @coll π e hπ _ heC _ =>
    refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exfalso
      have h2 : Om (1 + 1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (CSet.one_mem _ _))))
          (leOm3_lt_I n)
      exact absurd ((h2.trans h).trans hG2) (lt_irrefl _)
    rcases lt_trichotomy t 1 with hts | hts | hts
    · refine LeCl.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hΩQ.le))
      exact Order.add_one_le_of_lt hts
    · subst hts; exact LeCl.small (hcoll e.1 e.2 heC)
    · exfalso
      rcases (Order.add_one_le_of_lt hts).lt_or_eq with h3 | h3
      · have h4 : Om (1 + 1 + 1 : Ordinal.{0}) < S.psi e.1 (Om (t + 1)) :=
          (Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt h3)
        exact absurd ((h4.trans h).trans hG2) (lt_irrefl _)
      · subst h3
        have h4 : G ≤ S.psi e.1 (Om (1 + 1 + 1)) := (psi_mono (S := S) (InR_Om_succ (1 + 1)) zero_le).1
        exact absurd (h4.trans_lt h) (lt_irrefl _)

/-- **The collapse hypothesis of `snKey` holds at every `Q ≥ ψ_{Ω₂}(a)`.** -/
theorem snColl {a Q : Ordinal.{0}} (haQ : S.psi a (Om (1 + 1)) ≤ Q) :
    ∀ e, e < a → e ∈ S.CSet a Q → S.psi e (Om (1 + 1)) < Q := by
  intro e hea heC
  rcases haQ.lt_or_eq with hlt | rfl
  · exact (psi_mono (S := S) (InR_Om_succ 1) hea.le).1.trans_lt hlt
  · exact psi_lt_psi_of_mem (InR_Om_succ 1) hea heC

/-- **Every member of `Cl(a, Q)` below `G₃` is a code over `Q`**, for every strongly critical `Q ≥ ψ_{Ω₂}(a)`. -/
theorem snLeCl_mem {a Q x : Ordinal.{0}} (hQ : SC Q) (haQ : S.psi a (Om (1 + 1)) ≤ Q)
    (hx : x ∈ S.CSet a Q) (hxG : x < S.psi 0 (Om (1 + 1 + 1))) : LeCl (Om (1 + 1)) Q x := by
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) a 1).1.trans_le haQ
  have h := snKey hQ hΩQ (snColl haQ) x hx
  rwa [Ordinal.mod_eq_of_lt hxG] at h

/-- A code `p + ω^c` has a code exponent `c`. -/
theorem snLogLast {κ Q p c : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) (h : LeCl κ Q (p + ω ^ c)) : LeCl κ Q c := by
  have hm := LeCl.mod hQ.1 hκ.isPrincipal (c + 1) h
  have hlt : ω ^ c < ω ^ (c + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one c)
  rw [leMod_add_lt (c + 1) p hlt] at hm
  have hr : p % ω ^ (c + 1) < ω ^ (c + 1) := Ordinal.mod_lt p (opow_pos _ omega0_pos).ne'
  have hup : p % ω ^ (c + 1) + ω ^ c < ω ^ (c + 1) := isPrincipal_add_omega0_opow _ hr hlt
  have hlo : ω ^ c ≤ p % ω ^ (c + 1) + ω ^ c := le_add_self
  have hne : p % ω ^ (c + 1) + ω ^ c ≠ 0 := (lt_of_lt_of_le (opow_pos c omega0_pos) hlo).ne'
  have e : log ω (p % ω ^ (c + 1) + ω ^ c) = c := by
    refine le_antisymm ?_ (le_log_of_opow_le one_lt_omega0 hlo)
    have := (lt_opow_iff_log_lt one_lt_omega0 hne).1 hup
    exact Order.lt_add_one_iff.1 this
  have := (leClDec hQ hκ _ hm).2
  rwa [e] at this

/-- A code `p + W^Y` has a code `Y`. -/
theorem snLogLastW {Q p Y : Ordinal.{0}} (hQ : SC Q) (h : LeCl (Om (1 + 1)) Q (p + leWe Y)) :
    LeCl (Om (1 + 1)) Q Y := by
  have h1 : LeCl (Om (1 + 1)) Q (Om (1 + 1) * Y) := snLogLast hQ ldOm2_SC h
  have h2 := sjCl_div hQ ldOm2_SC _ h1
  rwa [Ordinal.mul_div_cancel _ ldOm2_SC.1.ne'] at h2

/-- **THE CLOSURE CONDITION AT A NORMAL-FORM ATOM**: `a = β + W^{X₀ + W^E}` in `Cl(a, ψ_{Ω₂}(a))`,
`X₀ + W^E < G₃` give that `E` and `X₀ + W^E` are codes over every strongly critical `Q ≥ ψ_{Ω₂}(a)`. -/
theorem snCL_nf {β X0 E : Ordinal.{0}}
    (hnf : β + leWe (X0 + leWe E) ∈ S.CSet (β + leWe (X0 + leWe E)) (S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1))))
    (hG3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1))) :
    ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q →
      LeCl (Om (1 + 1)) Q E ∧ LeCl (Om (1 + 1)) Q (X0 + leWe E) := by
  intro Q hQ hsQ
  have hGSC : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) _ 1).1.trans_le hsQ
  have hmem : β + leWe (X0 + leWe E) ∈ S.CSet (β + leWe (X0 + leWe E)) Q := CSet_mono le_rfl hsQ hnf
  have h0 := snKey hQ hΩQ (snColl hsQ) _ hmem
  have hWl : leWe (X0 + leWe E) < S.psi 0 (Om (1 + 1 + 1)) := (leWe_lt_SC hGSC hWG3 hG3).1
  rw [ldModK_add_lt hGSC β hWl] at h0
  have hY := snLogLastW hQ h0
  exact ⟨snLogLastW hQ hY, hY⟩

/-- **Every atom `s < θ` of a hull is `ψ_{Ω₂}(d)`, `d` in normal form, in the hull, below `A` and `Ω_ω`, and every
member of `Cl(d, s)` below `G₃` is a code over every strongly critical `Q ≥ s`.** -/
theorem snCL_atom {A ρ s : Ordinal.{0}} (hs : s ∈ ldAt S A ρ) (hsθ : s < ConjT.th S) (hρs : ρ ≤ s) :
    ∃ d, d < Om ω ∧ d < A ∧ s = S.psi d (Om (1 + 1)) ∧ d ∈ S.CSet A ρ ∧
      d ∈ S.CSet d (S.psi d (Om (1 + 1))) ∧
      ∀ x, x ∈ S.CSet d s → x < S.psi 0 (Om (1 + 1 + 1)) →
        ∀ Q, SC Q → s ≤ Q → LeCl (Om (1 + 1)) Q x := by
  obtain ⟨a, haH, haA, rfl⟩ := hs
  have hmemA : S.psi a (Om (1 + 1)) ∈ S.CSet A ρ := CSet.psi_mem haA (InR_Om_succ 1) (mxOm2_mem _ _) haH
  obtain ⟨d, hdW, hdA, hdeq, hdH, hdnf, -⟩ := Ry.ryTh_nf_mem hsθ hmemA hρs
  refine ⟨d, hdW, hdA, hdeq.symm, hdH, hdnf, fun x hx hxG Q hQ hsQ => ?_⟩
  rw [← hdeq] at hx hsQ
  exact snLeCl_mem hQ hsQ (CSet_mono le_rfl hsQ hx) hxG

end Googology.Trans.PoR.InaccPsi.R2.Sn
