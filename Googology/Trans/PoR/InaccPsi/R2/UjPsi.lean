import Googology.Trans.PoR.InaccPsi.R2.UgRead

/-!
# The collapse bound with level codes: `ψ_{Ω_{s+1}}(a) ≤ Q` modulo `Y_{s+2} = ψ_{Ω_{s+2}}(Ω_{s+2})`

`UgC S k Q` are the codes of level `k` with the atoms `ψ_{Ω_{k+1}}(d)`, `d < ψ_{Ω_{k+1}}(d)` (`Ug.UgC`).
`Le.lePsi_le` bounds `ψ_{Ω_{s+1}}(a)` by `Q` through the codes `LeCl Ω_{s+1} Q` of the remainders modulo
`G = ψ_{Ω_{s+2}}(0)`; it cannot see an exponent `≥ G` (the wall `Γ₂ = ψ_{Ω₃}(0)` at `s = 1`).  Here the remainder is
taken modulo `Y = ψ_{Ω_{s+2}}(Ω_{s+2})` and the codes carry the atoms.

* `ujY`, `ujY_SC`, `ujY_gt`, `ujY_lt`;
* `ujArg_lt` (**below `Y` the argument is below the value**: `ψ_{Ω_{s+2}}(e) < Y ⇒ e < ψ_{Ω_{s+2}}(e)`, from the
  normal argument `Ry.ryNf`);
* `ujKey` (**every element of `Cl(a, Q)` has its remainder modulo `Y` a level-`(s+1)` code**, given the collapse
  hypothesis), `ujPsi_le` (**`ψ_{Ω_{s+1}}(a) ≤ Q`**, one proof for every level `s`), `ujPsi2_le` (`s = 1`, modulo
  `Y₃ = Ug.ugY`), `ujPsi1_le` (`s = 0`, modulo `Y₂ = ψ_{Ω₂}(Ω₂)`);
* `ujC_boundY` (**the digit at position `y` of a level-`k` code is below `Q`**: a code below `ω^{Ω_k·y + Ω_k}` is
  below `ω^{Ω_k·y}·Q`, for every code `y`; `Le.leCl_boundY` with the atoms), `ujC_boundK` (`Le.leCl_boundK` with
  the atoms), `ujY2_gt_G1`.

No new axiom.  New definition: `ujY`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Ry Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

/-- `Y_{s+2} = ψ_{Ω_{s+2}}(Ω_{s+2})`. -/
noncomputable def ujY (S : InaccSeq.{0}) (s : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (Om (s + 1 + 1)) (Om (s + 1 + 1))

theorem ujY_SC (s : Ordinal.{0}) : SC (ujY S s) := SC_psi (InR_Om_succ (s + 1)) _

theorem ujY_gt (s : Ordinal.{0}) : Om (s + 1) < ujY S s := (psiS_bounds (S := S) _ (s + 1)).1

theorem ujY_lt (s : Ordinal.{0}) : ujY S s < Om (s + 1 + 1) := psi_lt (InR_Om_succ (s + 1)) _

theorem ujY_one : ujY S 1 = ugY S := rfl

theorem ujY_zero : ujY S 0 = S.psi (Om (1 + 1)) (Om (1 + 1)) := by unfold ujY; rw [zero_add]

/-- `ψ_{Ω₂}(0) < Y₂`. -/
theorem ujY2_gt_G1 : S.psi 0 (Om (1 + 1)) < ujY S 0 := by
  rw [ujY_zero]
  have hκ : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine psi_lt_psi_of_mem hκ (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)) ?_
  exact CSet.zero_mem _ _

/-- **Below `Y` the argument is below the value**: `ψ_{Ω_{s+2}}(e) < Y_{s+2} ⇒ e < ψ_{Ω_{s+2}}(e)`. -/
theorem ujArg_lt {s e : Ordinal.{0}} (hsC : ∀ a b, s ∈ S.CSet a b)
    (h : S.psi e (Om (s + 1 + 1)) < ujY S s) : e < S.psi e (Om (s + 1 + 1)) := by
  have hκ : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  have hX : ∀ a c, Om (s + 1 + 1) ∈ S.CSet a c :=
    fun a c => CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (hsC a c)))
  by_contra hle
  push Not at hle
  obtain ⟨hdX, heq, hself, -⟩ := ryNf_spec hκ hX h
  set d := ryNf S (Om (s + 1 + 1)) e with hd_def
  have hdb : d < S.psi e (Om (s + 1 + 1)) := by rw [← heq]; exact lt_psi_of_mem hκ hself hdX
  have hde : d < e := hdb.trans_le hle
  have hd' : d ∈ S.CSet e (S.psi e (Om (s + 1 + 1))) := CSet_mono hde.le (by rw [heq]) hself
  have hmem : S.psi d (Om (s + 1 + 1)) ∈ S.CSet e (S.psi e (Om (s + 1 + 1))) :=
    CSet.psi_mem hde hκ (hX _ _) hd'
  rw [heq] at hmem
  exact lt_irrefl _ (lt_psi_of_mem hκ hmem (psi_lt hκ e))

/-- **Every element of `Cl(a, Q)` has its remainder modulo `Y_{s+2}` a level-`(s+1)` code.** -/
theorem ujKey {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1 + 1) < S.I n)
    (hcoll : ∀ e, e < a → UgC S (s + 1) Q (e % ujY S s) → S.psi e (Om (s + 1)) < Q) :
    ∀ x ∈ S.CSet a Q, UgC S (s + 1) Q (x % ujY S s) := by
  set Y := ujY S s with hY_def
  have hYSC : SC Y := ujY_SC s
  have hY3 : Y < Om (s + 1 + 1) := ujY_lt s
  have hQ0 : 0 < Q := hQ.1
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < Y → UgC S (s + 1) Q p) →
      UgC S (s + 1) Q (p % Y) := by
    intro p hp h
    rcases ldModK_prin hYSC hp with ⟨hpY, e⟩ | e
    · rw [e]; exact h hpY
    · rw [e]; exact UgC.zero hQ0
  have hIY : ∀ n, Y < S.I n := fun n => hY3.trans (hI n)
  intro x hx
  induction hx with
  | small h => exact UgC.small ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact UgC.zero hQ0
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal fun h => absurd (h.trans (hIY n)) (lt_irrefl _)
  | inaccW =>
    exact prin (SC_Iw (S := S)).isPrincipal fun h =>
      absurd (h.trans ((hIY 0).trans_le (Ordinal.le_iSup (fun n => S.I n) 0))) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    rcases lt_or_ge y Y with hy | hy
    · rw [ldModK_add_lt hYSC x hy]
      have hy' : UgC S (s + 1) Q y := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
      exact UgC.add ihx hy'
    · rw [ldModK_add_ge hYSC x hy]; exact ihy
  | @phi x y _ _ ihx ihy =>
    refine prin (Ph.ph_veblen_prin x y) fun h => ?_
    have hx1 : x < Y := lt_of_le_of_lt (left_le_veblen x y) h
    have hy1 : y < Y := lt_of_le_of_lt (right_le_veblen x y) h
    rw [Ordinal.mod_eq_of_lt hx1] at ihx
    rw [Ordinal.mod_eq_of_lt hy1] at ihy
    exact UgC.phi ihx ihy
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact UgC.zero hQ0
    refine prin (Om_isPrincipal hx0) fun h => ?_
    rcases lt_trichotomy x (s + 1) with hx | hx | hx
    · refine UgC.small (lt_of_le_of_lt (Om_le_Om.2 ?_) hsQ)
      rw [← Order.succ_eq_add_one] at hx; exact Order.lt_succ_iff.1 hx
    · rw [hx]; exact UgC.om
    · exfalso
      have h2 : s + 1 + 1 ≤ x := by
        rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt hx
      exact absurd (h.trans hY3) (not_lt.2 (Om_le_Om.2 h2))
  | @coll π e hπ _ _ _ ihe =>
    refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
    rcases hπ with ⟨n, rfl⟩ | ⟨t, rfl⟩
    · exfalso
      have h2 : Om (s + 1 + 1) < S.psi e.1 (S.I n) :=
        lt_psi_of_mem (InR_I n) (CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (hsC _ _)))) (hI n)
      exact absurd ((h2.trans h).trans hY3) (lt_irrefl _)
    rcases lt_trichotomy t s with hts | hts | hts
    · refine UgC.small (lt_of_lt_of_le (psi_lt (InR_Om_succ t) _) ((Om_le_Om.2 ?_).trans hsQ.le))
      exact Order.add_one_le_of_lt hts
    · subst hts; exact UgC.small (hcoll e.1 e.2 ihe)
    · rcases (Order.add_one_le_of_lt hts).lt_or_eq with h3 | h3
      · exfalso
        have h4 : Om (s + 1 + 1) < S.psi e.1 (Om (t + 1)) := (Om_lt_psiS e.1 t).2 (Order.add_one_le_of_lt h3)
        exact absurd ((h4.trans h).trans hY3) (lt_irrefl _)
      · subst h3
        have hlt := ujArg_lt hsC h
        have heY : e.1 < Y := hlt.trans h
        rw [Ordinal.mod_eq_of_lt heY] at ihe
        exact UgC.psi ihe hlt

/-- **`ψ_{Ω_{s+1}}(a) ≤ Q`** for a strongly critical `Q > Ω_s`, if `ψ_{Ω_{s+1}}(e) < Q` for every `e < a` whose
remainder modulo `Y_{s+2}` is a level-`(s+1)` code. -/
theorem ujPsi_le {s a Q : Ordinal.{0}} (hQ : SC Q) (hsQ : Om s < Q) (hsC : ∀ a b, s ∈ S.CSet a b)
    (hI : ∀ n, Om (s + 1 + 1) < S.I n)
    (hcoll : ∀ e, e < a → UgC S (s + 1) Q (e % ujY S s) → S.psi e (Om (s + 1)) < Q) :
    S.psi a (Om (s + 1)) ≤ Q := by
  have key := ujKey hQ hsQ hsC hI hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.succ_mem (hsC _ _))) fun x hx hxκ => ?_
  have := key x hx
  rw [Ordinal.mod_eq_of_lt (hxκ.trans (ujY_gt s))] at this
  exact ugC_lt_om hQ this hxκ

/-- **`ψ_{Ω₂}(a) ≤ Q`** through the level-2 codes modulo `Y₃ = ψ_{Ω₃}(Ω₃)`. -/
theorem ujPsi2_le {a Q : Ordinal.{0}} (hQ : SC Q) (hΩQ : Om 1 < Q)
    (hcoll : ∀ e, e < a → UgC S (1 + 1) Q (e % ugY S) → S.psi e (Om (1 + 1)) < Q) :
    S.psi a (Om (1 + 1)) ≤ Q :=
  ujPsi_le (s := 1) hQ hΩQ (fun a b => CSet.one_mem a b) leOm3_lt_I hcoll

/-- **`ψ_{Ω₁}(a) ≤ T`** through the level-1 codes modulo `Y₂ = ψ_{Ω₂}(Ω₂)`. -/
theorem ujPsi1_le {a T : Ordinal.{0}} (hT : SC T)
    (hcoll : ∀ e, e < a → UgC S 1 T (e % ujY S 0) → S.psi e (Om 1) < T) :
    S.psi a (Om 1) ≤ T := by
  have h := ujPsi_le (S := S) (s := 0) (a := a) hT (by rw [Om_zero]; exact hT.1)
    (fun a b => CSet.zero_mem a b) (fun n => by rw [zero_add]; exact Mx.mxOm2_lt_I n)
    (fun e he hc => by rw [zero_add] at hc ⊢; exact hcoll e he hc)
  rwa [zero_add] at h

/-- **The digit at position `y` of a level-`k` code is below `Q`**: a code below `ω^{Ω_k·y + Ω_k}` is below
`ω^{Ω_k·y}·Q`, for every code `y`. -/
theorem ujC_boundY {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0) {y : Ordinal.{0}} (hy : UgC S k Q y) :
    ∀ x, UgC S k Q x → x < ω ^ (Om k * y + Om k) → x < ω ^ (Om k * y) * Q := by
  have eQ : ω ^ (Om k * y) * Q = ω ^ (Om k * y + Q) := by rw [opow_add, gg_SC_eps hQ]
  have hpr : IsPrincipal (· + ·) (ω ^ (Om k * y) * Q) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  have hκy := ugC_mulK hQ hk y hy
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := ugCDec hQ hk x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (UgC.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < Om k * y + Om k := (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < ω ^ (Om k * y) * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a (Om k * y) with h | h
    · exact h.trans_le le_self_add
    · have hc : UgC S k Q (a - Om k * y) := (ugCDec hQ hk a hlog).1 _ hκy h
      have hdec' : Om k * y + (a - Om k * y) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - Om k * y < Om k := by
        have : Om k * y + (a - Om k * y) < Om k * y + Om k := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (ugC_lt_om hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

/-- **The position of the leading digit of a level-`k` code is below `Q`**: a code below `Ω_k·Ω_k` is below
`Ω_k·Q`. -/
theorem ujC_boundK {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0) :
    ∀ x, UgC S k Q x → x < Om k * Om k → x < Om k * Q := by
  have hκ : SC (Om k) := SC_Om hk
  have hE : ω ^ Om k = Om k := gg_SC_eps hκ
  have eQ : Om k * Q = ω ^ (Om k + Q) := by rw [opow_add, hE, gg_SC_eps hQ]
  have eK : Om k * Om k = ω ^ (Om k + Om k) := by rw [opow_add, hE]
  have hpr : IsPrincipal (· + ·) (Om k * Q) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := ugCDec hQ hk x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (UgC.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < Om k + Om k := by
    rw [eK] at hxb; exact (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < Om k * Q := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rcases lt_or_ge a (Om k) with h | h
    · exact h.trans_le le_self_add
    · have hc : UgC S k Q (a - Om k) := (ugCDec hQ hk a hlog).1 _ UgC.om h
      have hdec' : Om k + (a - Om k) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - Om k < Om k := by
        have : Om k + (a - Om k) < Om k + Om k := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (ugC_lt_om hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

end Googology.Trans.PoR.InaccPsi.R2.Uj
