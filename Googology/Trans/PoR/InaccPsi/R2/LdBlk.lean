import Googology.Trans.PoR.InaccPsi.R2.LdMove

/-!
# The blocks of level 2: `Θ_λ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + Θ_λ(c))` above a base `β`

`ψ = S.psi`, `H_λ = Cl(A_{η_λ}, ρ_λ)`, `ldAtR λ` its atoms below `Ω₂`, `Θ = gxTh ρ_λ (ldAtR λ)` (`= Θ_λ` below `Ω₂`,
`R2.LdHull`).  A base is an ordinal `β` with `Ω₂ ∣ β`, `β ∈ H_λ`, `β` in the closures `Cl(β + d, ψ_{Ω₂}(β + d))`
(`d ≤ Ω₂`) and `β + Ω₂ < A_{η_λ}`; its block is `[ψ_{Ω₂}(β), F^β)`, `F^β = ψ_{Ω₂}(β + Ω₂)` (`ldTop`), with the
layers `K^β_0 = Ω₁`, `K^β_{j+1} = ψ_{Ω₂}(β + K^β_j)` (`ldKb`).

* `ldModK_add_lt`, `ldModK_add_ge`, `ldDvdK_of_prin`, `ldModK_prin` (the remainder modulo a strongly critical `κ`),
  `ldModK_mem` (**`Cl(a, b)` is closed under `x ↦ x % κ`**), `ldPsi2_le` (`ψ_{Ω₂}(a) ≤ T` from the remainders
  modulo `Ω₂`);
* `ldKb_gt` (`c < ψ_{Ω₂}(β + c)` below every `K^β_j`), `ldKb_sup` (**`F^β = sup_j K^β_j`**), `ldTop_ge`,
  `ldTop_gt` (**`c < ψ_{Ω₂}(β + c)` for every `c < F^β`**: every argument of the block is own), `ldTop_lt`;
* `ldBlk_cls` (**every atom of `H_λ` below `F^β` is `≤ ψ_{Ω₂}(β)` or is `ψ_{Ω₂}(β + c)` with `c ∈ H_λ`, `c < F^β`**);
* `ldBlk_step` (**THE BLOCK LAW**: if `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, `Â` own, then `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + Θ(c))`
  for every code `c < F^β`), `ldBlk_next` (**the next base**: `Θ(F^β) = ψ_{Ω₁}(Â + Ω₁)`), `ldBlk_zero`
  (`Θ(ψ_{Ω₂}(0)) = ψ_{Ω₁}(A + 1)`);
* `ldGxStepRec` (the hull transport of `Mx.mxGxStep` with an inner induction: an atom may use the moves of the codes
  below it).

No new axiom.  New definitions: `ldKb`, `ldTop`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ld

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Sf
  Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-! ## The remainder modulo a strongly critical `κ` -/

theorem ldModK_add_lt {κ : Ordinal.{0}} (hκ : SC κ) (x : Ordinal.{0}) {y : Ordinal.{0}} (hy : y < κ) :
    (x + y) % κ = x % κ + y := by
  have hr : x % κ < κ := Ordinal.mod_lt x hκ.1.ne'
  have e : x + y = κ * (x / κ) + (x % κ + y) := by
    conv_lhs => rw [← Ordinal.div_add_mod x κ]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (hκ.isPrincipal hr hy)]

theorem ldModK_add_ge {κ : Ordinal.{0}} (hκ : SC κ) (x : Ordinal.{0}) {y : Ordinal.{0}} (hy : κ ≤ y) :
    (x + y) % κ = y % κ := by
  have hκ0 : κ ≠ 0 := hκ.1.ne'
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  set q := y / κ with hq
  set r' := y % κ with hr'
  have hy' : y = κ * q + r' := (Ordinal.div_add_mod y κ).symm
  have hq0 : q ≠ 0 := by
    intro h0
    have : y < κ := by
      rw [hy', h0, mul_zero, zero_add]; exact Ordinal.mod_lt y hκ0
    exact absurd hy (not_le.2 this)
  have habs : x % κ + κ * q = κ * q := by
    refine Ordinal.add_of_omega0_opow_le (b := κ) ?_ ?_
    · rw [hE]; exact Ordinal.mod_lt x hκ0
    · rw [hE]; exact le_mul_left κ (pos_iff_ne_zero.2 hq0)
  have e : x + y = κ * (x / κ + q) + r' := by
    conv_lhs => rw [← Ordinal.div_add_mod x κ, hy']
    rw [mul_add, add_assoc (κ * (x / κ)), ← add_assoc (x % κ), habs, add_assoc]
  rw [e, Ordinal.mul_add_mod_self]
  exact Ordinal.mod_eq_of_lt (Ordinal.mod_lt y hκ0)

theorem ldDvdK_of_prin {κ p : Ordinal.{0}} (hκ : SC κ) (hp : IsPrincipal (· + ·) p) (h1 : κ ≤ p) :
    κ ∣ p := by
  have hE : ω ^ κ = κ := Low.opow_eq_self_of_SC hκ
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h0 | ⟨γ, rfl⟩
  · exact absurd (h0 ▸ h1) (not_le.2 hκ.1)
  · have hγ : κ ≤ γ := by
      rw [← hE] at h1; exact (opow_le_opow_iff_right one_lt_omega0).1 h1
    rw [← hE]; exact opow_dvd_opow ω hγ

theorem ldModK_prin {κ p : Ordinal.{0}} (hκ : SC κ) (hp : IsPrincipal (· + ·) p) :
    (p < κ ∧ p % κ = p) ∨ p % κ = 0 := by
  rcases lt_or_ge p κ with h | h
  · exact Or.inl ⟨h, Ordinal.mod_eq_of_lt h⟩
  · exact Or.inr (Ordinal.mod_eq_zero_of_dvd (ldDvdK_of_prin hκ hp h))

/-- **`Cl(a, b)` is closed under `x ↦ x % κ`** for a strongly critical `κ`. -/
theorem ldModK_mem {κ a b x : Ordinal.{0}} (hκ : SC κ) (hx : x ∈ S.CSet a b) : x % κ ∈ S.CSet a b := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → p ∈ S.CSet a b → p % κ ∈ S.CSet a b := by
    intro p hp hpC
    rcases ldModK_prin hκ hp with ⟨-, e⟩ | e
    · rw [e]; exact hpC
    · rw [e]; exact CSet.zero_mem a b
  induction hx with
  | small h => exact CSet.of_lt ((Ordinal.mod_le _ _).trans_lt h)
  | zero => rw [Ordinal.zero_mod]; exact CSet.zero_mem a b
  | inacc n => exact prin (SC_I (S := S) n).isPrincipal (CSet.I_mem a b n)
  | inaccW => exact prin (SC_Iw (S := S)).isPrincipal (CSet.Iw_mem a b)
  | @add x y _ hy ihx ihy =>
    rcases lt_or_ge y κ with h | h
    · rw [ldModK_add_lt hκ x h]; exact CSet.add_mem ihx hy
    · rw [ldModK_add_ge hκ x h]; exact ihy
  | @phi x y hx hy _ _ => exact prin (Ph.ph_veblen_prin x y) (CSet.phi_mem hx hy)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_mod]; exact CSet.zero_mem a b
    · exact prin (Om_isPrincipal hx0) (CSet.Om_mem hx)
  | @coll π e hπ hπC heC _ _ => exact prin (SC_psi hπ e.1).isPrincipal (CSet.psi_mem e.2 hπ hπC heC)

theorem ldOm2_SC : SC (Om (1 + 1 : Ordinal.{0})) := SC_Om (by
  rw [one_add_one_eq_two]; exact two_ne_zero)

/-- **`ψ_{Ω₂}(a) ≤ T`** for a strongly critical `T > Ω₁`, if `ψ_{Ω₂}(e) < T` for every `e < a` with
`e % Ω₂ < T`. -/
theorem ldPsi2_le {a T : Ordinal.{0}} (hT : SC T) (hΩT : Om 1 < T)
    (hcoll : ∀ e, e < a → e % Om (1 + 1) < T → S.psi e (Om (1 + 1)) < T) : S.psi a (Om (1 + 1)) ≤ T := by
  have prin : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → (p < Om (1 + 1) → p < T) →
      p % Om (1 + 1) < T := by
    intro p hp h
    rcases ldModK_prin ldOm2_SC hp with ⟨hp1, e⟩ | e
    · rw [e]; exact h hp1
    · rw [e]; exact hT.1
  have key : ∀ x ∈ S.CSet a T, x % Om (1 + 1) < T := by
    intro x hx
    induction hx with
    | small h => exact (Ordinal.mod_le _ _).trans_lt h
    | zero => rw [Ordinal.zero_mod]; exact hT.1
    | inacc n => exact prin (SC_I (S := S) n).isPrincipal fun h => absurd (h.trans (mxOm2_lt_I n)) (lt_irrefl _)
    | inaccW => exact prin (SC_Iw (S := S)).isPrincipal fun h => absurd (h.trans mxOm2_lt_Iw) (lt_irrefl _)
    | @add x y _ _ ihx ihy =>
      rcases lt_or_ge y (Om (1 + 1)) with hy | hy
      · rw [ldModK_add_lt ldOm2_SC x hy]
        have hyT : y < T := by rwa [Ordinal.mod_eq_of_lt hy] at ihy
        exact hT.isPrincipal ihx hyT
      · rw [ldModK_add_ge ldOm2_SC x hy]; exact ihy
    | @phi x y _ _ ihx ihy =>
      refine prin (Ph.ph_veblen_prin x y) fun h => ?_
      have hx1 : x < Om (1 + 1) := lt_of_le_of_lt (left_le_veblen x y) h
      have hy1 : y < Om (1 + 1) := lt_of_le_of_lt (right_le_veblen x y) h
      rw [Ordinal.mod_eq_of_lt hx1] at ihx
      rw [Ordinal.mod_eq_of_lt hy1] at ihy
      exact hT.2 x ihx y ihy
    | @om x _ _ =>
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [Om_zero, Ordinal.zero_mod]; exact hT.1
      · refine prin (Om_isPrincipal hx0) fun h => ?_
        have h2 : x < 1 + 1 := Om_lt_Om.1 h
        rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
        · exact absurd (Order.lt_one_iff.1 h0) hx0
        · rw [h1]; exact hΩT
    | @coll π e hπ _ _ _ ihe =>
      refine prin (SC_psi hπ e.1).isPrincipal fun h => ?_
      rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
      · exfalso
        have h2 : Om (1 + 1 : Ordinal.{0}) < S.psi e.1 (S.I n) :=
          lt_psi_of_mem (InR_I n) (mxOm2_mem _ _) (mxOm2_lt_I n)
        exact absurd (h2.trans h) (lt_irrefl _)
      rcases eq_or_ne s 0 with rfl | hs0
      · rw [zero_add]; exact (psi_lt Low.InR_Om_one _).trans hΩT
      rcases eq_or_ne s 1 with rfl | hs1
      · exact hcoll e.1 e.2 ihe
      · exfalso
        have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne
          (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
        have h2 := (Om_lt_psiS (S := S) e.1 s).2 h2s
        exact absurd (h2.trans h) (lt_irrefl _)
  refine psi_le_of_good (mxOm2_mem _ _) fun x hx hx2 => ?_
  have := key x hx
  rwa [Ordinal.mod_eq_of_lt hx2] at this

/-! ## The layers of a block -/

/-- `K^β_0 = Ω₁`, `K^β_{j+1} = ψ_{Ω₂}(β + K^β_j)`. -/
noncomputable def ldKb (S : InaccSeq.{0}) (β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + ldKb S β j) (Om (1 + 1))

/-- The top of the block of `β`: `F^β = ψ_{Ω₂}(β + Ω₂)`. -/
noncomputable def ldTop (S : InaccSeq.{0}) (β : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (β + Om (1 + 1)) (Om (1 + 1))

theorem ldKb_succ (β : Ordinal.{0}) (j : ℕ) : ldKb S β (j + 1) = S.psi (β + ldKb S β j) (Om (1 + 1)) := rfl

theorem ldKb_lt_Om2 (β : Ordinal.{0}) : ∀ j, ldKb S β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem ldKb_SC (β : Ordinal.{0}) : ∀ j, SC (ldKb S β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem ldTop_SC (β : Ordinal.{0}) : SC (ldTop S β) := SC_psi (InR_Om_succ 1) _
theorem ldTop_lt_Om2 (β : Ordinal.{0}) : ldTop S β < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem ldOm1_lt_Top (β : Ordinal.{0}) : Om (1 : Ordinal.{0}) < ldTop S β := (psiS_bounds (S := S) _ 1).1

/-- `c < ψ_{Ω₂}(β + c)` below every `K^β_j`. -/
theorem ldKb_gt (β : Ordinal.{0}) : ∀ j c, c < ldKb S β j → c < S.psi (β + c) (Om (1 + 1))
  | 0, c, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, c, h => by
    rcases lt_or_ge c (ldKb S β j) with h' | h'
    · exact ldKb_gt β j c h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h')).1

theorem ldKb_le_top (β : Ordinal.{0}) : ∀ j, ldKb S β j ≤ ldTop S β
  | 0 => (ldOm1_lt_Top β).le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (ldKb_lt_Om2 β j).le)).1

section Base

variable {β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ Om (1 + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))

include hβown

theorem ldKb_lt_succ : ∀ j, ldKb S β j < ldKb S β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := ldKb_lt_succ j
    have hle : ldKb S β (j + 1) ≤ ldKb S β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 IH.le)).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 IH) ?_
    exact CSet.add_mem (hβown _ (ldKb_lt_Om2 β (j + 1)).le) (CSet.of_lt (IH.trans_le hle))

theorem ldKb_mono {j j' : ℕ} (h : j ≤ j') : ldKb S β j ≤ ldKb S β j' :=
  (strictMono_nat_of_lt_succ (fun k => ldKb_lt_succ hβown k)).monotone h

/-- **`F^β = sup_j K^β_j`** (for `Ω₂ ∣ β`). -/
theorem ldKb_sup (hβd : Om (1 + 1) ∣ β) {x : Ordinal.{0}} (hx : x < ldTop S β) : ∃ j, x < ldKb S β j := by
  have hbdd : BddAbove (Set.range (ldKb S β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, ldKb S β j ↔ ∃ j, y < ldKb S β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, ldKb S β j < ⨆ j, ldKb S β j := fun j => (hlt _).2 ⟨j + 1, ldKb_lt_succ hβown j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, ldKb S β j := hKQ 0
  have hQSC : SC (⨆ j, ldKb S β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨k, hk⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (ldKb_mono hβown (le_max_left i k))
    have hk' := hk.trans_le (ldKb_mono hβown (le_max_right i k))
    exact ((ldKb_SC β (max i k)).2 _ hi' _ hk').trans (hKQ _)
  have hFQ : ldTop S β ≤ ⨆ j, ldKb S β j := by
    refine ldPsi2_le hQSC hΩQ fun e he hmod => ?_
    rcases lt_or_ge e β with heβ | heβ
    · have h1 : S.psi e (Om (1 + 1)) ≤ ldKb S β 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (heβ.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le heβ
      have hd2 : d < Om (1 + 1) := (add_lt_add_iff_left β).1 he
      have hdm : (β + d) % Om (1 + 1) = d := by
        obtain ⟨q, rfl⟩ := hβd
        rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd2]
      rw [hdm] at hmod
      obtain ⟨j, hj⟩ := (hlt _).1 hmod
      have := hKQ (j + 1)
      rw [ldKb_succ] at this
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hj.le)).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + c) ≥ F^β` for `c ≥ F^β`. -/
theorem ldTop_ge (hβd : Om (1 + 1) ∣ β) {c : Ordinal.{0}} (hc : ldTop S β ≤ c) :
    ldTop S β ≤ S.psi (β + c) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := ldKb_sup hβown hβd h
  have h1 : ldKb S β (j + 1) ≤ S.psi (β + c) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ((ldKb_le_top β j).trans hc))).1
  exact absurd (hj.trans_le ((ldKb_lt_succ hβown j).le.trans h1)) (lt_irrefl _)

/-- **Every argument of the block is own**: `c < ψ_{Ω₂}(β + c)` for `c < F^β`. -/
theorem ldTop_gt (hβd : Om (1 + 1) ∣ β) {c : Ordinal.{0}} (hc : c < ldTop S β) :
    c < S.psi (β + c) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := ldKb_sup hβown hβd hc
  exact ldKb_gt β j c hj

theorem ldOwn (hβd : Om (1 + 1) ∣ β) {c : Ordinal.{0}} (hc : c < ldTop S β) :
    β + c ∈ S.CSet (β + c) (S.psi (β + c) (Om (1 + 1))) :=
  CSet.add_mem (hβown c (hc.trans (ldTop_lt_Om2 β)).le) (CSet.of_lt (ldTop_gt hβown hβd hc))

/-- `ψ_{Ω₂}(β + c) < F^β` for `c < F^β`. -/
theorem ldTop_lt {c : Ordinal.{0}} (hc : c < ldTop S β) : S.psi (β + c) (Om (1 + 1)) < ldTop S β :=
  psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (hc.trans (ldTop_lt_Om2 β)))
    (CSet.add_mem (hβown _ le_rfl) (CSet.of_lt hc))

theorem ldBase_lt_top : S.psi β (Om (1 + 1)) < ldTop S β := by
  have h := ldTop_lt hβown (c := 0) ((Om_pos one_ne_zero).trans (ldOm1_lt_Top β))
  rwa [add_zero] at h

/-- `ψ_{Ω₂}(β) < ψ_{Ω₂}(β + c)` for `0 < c < F^β`. -/
theorem ldBase_lt {c : Ordinal.{0}} (hc0 : c ≠ 0) (hc : c < ldTop S β) :
    S.psi β (Om (1 + 1)) < S.psi (β + c) (Om (1 + 1)) :=
  psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (pos_iff_ne_zero.2 hc0))
    (hβown c (hc.trans (ldTop_lt_Om2 β)).le)

end Base

/-! ## The atoms of a block -/

/-- **Every atom of `H_λ` below `F^β` is at most `ψ_{Ω₂}(β)` or is `ψ_{Ω₂}(β + c)`, `c ∈ H_λ`, `c < F^β`.** -/
theorem ldBlk_cls {l ηx β t : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hβown : ∀ d, d ≤ Om (1 + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
    (hβd : Om (1 + 1) ∣ β) (ht : t ∈ ldAtR S l) (htF : t < ldTop S β) :
    t ≤ S.psi β (Om (1 + 1)) ∨
      ∃ c, GxCl (upsilon l) (ldAtR S l) c ∧ c < ldTop S β ∧ t = S.psi (β + c) (Om (1 + 1)) := by
  obtain ⟨a, ha, -, rfl⟩ := ht
  rcases lt_or_ge a β with hab | hab
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) hab.le).1
  rcases lt_or_ge a (β + Om (1 + 1)) with ha2 | ha2
  · obtain ⟨c, rfl⟩ := exists_add_of_le hab
    have hc2 : c < Om (1 + 1) := (add_lt_add_iff_left β).1 ha2
    have hmod : (β + c) % Om (1 + 1) = c := by
      obtain ⟨q, rfl⟩ := hβd
      rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc2]
    have hcH : c ∈ cdHull S l := by
      have := ldModK_mem (S := S) ldOm2_SC ha
      rwa [hmod] at this
    have hcF : c < ldTop S β := by
      by_contra h
      push Not at h
      exact absurd htF (not_lt.2 (ldTop_ge hβown hβd h))
    exact Or.inr ⟨c, (ldHull_iff hl hX hc2).1 hcH, hcF, rfl⟩
  · exact absurd htF (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ha2).1)

/-! ## The block law -/

theorem ldBlk_atom {l ηx β c : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hβH : β ∈ cdHull S l) (hβA : β + Om (1 + 1) < ConjT.Aη S (cdEta S l))
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hcF : c < ldTop S β) :
    S.psi (β + c) (Om (1 + 1)) ∈ ldAtR S l := by
  have hc2 := hcF.trans (ldTop_lt_Om2 β)
  exact ⟨β + c, CSet.add_mem hβH ((ldHull_iff hl hX hc2).2 hc),
    ((add_lt_add_iff_left β).2 hc2).trans hβA, rfl⟩

theorem ldBlk_base_atom {l β : Ordinal.{0}} (hβH : β ∈ cdHull S l)
    (hβA : β + Om (1 + 1) < ConjT.Aη S (cdEta S l)) : S.psi β (Om (1 + 1)) ∈ ldAtR S l :=
  ⟨β, hβH, (le_self_add.trans_lt hβA), rfl⟩

theorem ldBlk_top_atom {l β : Ordinal.{0}} (hβH : β ∈ cdHull S l)
    (hβA : β + Om (1 + 1) < ConjT.Aη S (cdEta S l)) : ldTop S β ∈ ldAtR S l :=
  ⟨β + Om (1 + 1), CSet.add_mem hβH (mxOm2_mem _ _), hβA, rfl⟩

section Blk

variable {l ηx β Â : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hβown : ∀ d, d ≤ Om (1 + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hβd : Om (1 + 1) ∣ β) (hβH : β ∈ cdHull S l) (hβA : β + Om (1 + 1) < ConjT.Aη S (cdEta S l))
  (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
  (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))

include hl hX hβown hβd hβH hβA hÂ hbase

/-- **THE BLOCK LAW**: `Θ(ψ_{Ω₂}(β + c)) = ψ_{Ω₁}(Â + Θ(c))` for every code `c < F^β`. -/
theorem ldBlk_step : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < ldTop S β →
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + c) (Om (1 + 1))) =
      S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρSC : SC (upsilon l) := hpv ▸ SC_psi Low.InR_Om_one _
  have hρ1 : upsilon l < Om 1 := hpv ▸ psi_lt Low.InR_Om_one _
  have hρ0 : 0 < upsilon l := hρSC.1
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hbat := ldBlk_base_atom hβH hβA
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hbat).2.1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcF
  have hc2 : c < Om (1 + 1) := hcF.trans (ldTop_lt_Om2 β)
  have hsat := ldBlk_atom hl hX hβH hβA hc hcF
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [add_zero, gxTh_zero, add_zero]; exact hbase
  have hΘc0 : 0 < gxTh (upsilon l) (ldAtR S l) c := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρ0) (pos_iff_ne_zero.2 hc0)
    rwa [gxTh_zero] at this
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt hsat
  have hβs := ldBase_lt hβown hc0 hcF
  have hÂb : Â ∈ S.CSet (Â + gxTh (upsilon l) (ldAtR S l) c)
      (S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1)) :=
    (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hbaseb : S.psi Â (Om 1) < S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â hΘc0) hÂb
  apply le_antisymm
  · -- `T ≤ b`
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hbaseb) ?_
    intro t ht hts
    rcases ldBlk_cls hl hX hβown hβd ht (hts.trans (ldTop_lt hβown hcF)) with hle | ⟨c', hc'g, hc'F, rfl⟩
    · exact (gxTh_mono hle).trans_lt (by rw [hbase]; exact hbaseb)
    · have hc'c : c' < c := by
        by_contra h
        push Not at h
        exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
      have hIH := IH c' hc'c hc'g hc'F
      rw [hIH]
      have hΘ' : gxTh (upsilon l) (ldAtR S l) c' < gxTh (upsilon l) (ldAtR S l) c := gxTh_lt hc'g hc'c
      have hΘ'b : gxTh (upsilon l) (ldAtR S l) c' < S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
        have h1 := gxTh_lt hc'g (ldTop_gt hβown hβd hc'F)
        rw [hIH] at h1
        exact h1.trans_le (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hΘ'.le)).1
      exact psi_lt_psi_of_mem Low.InR_Om_one ((add_lt_add_iff_left Â).2 hΘ')
        (CSet.add_mem hÂb (CSet.of_lt hΘ'b))
  · -- `b ≤ T`
    refine ldPsi1_le hTSC fun e he _ => ?_
    rcases le_or_gt e Â with heÂ | heÂ
    · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 ?_
      rw [← hbase]; exact hTs _ hbat hβs
    · obtain ⟨d, rfl⟩ := exists_add_of_le heÂ.le
      have hd : d < gxTh (upsilon l) (ldAtR S l) c := (add_lt_add_iff_left Â).1 he
      obtain ⟨c', hc'g, hc'c, rfl⟩ := gxTh_onto hd
      have hc'F := hc'c.trans hcF
      have ht'at := ldBlk_atom hl hX hβH hβA hc'g hc'F
      have ht's : S.psi (β + c') (Om (1 + 1)) < S.psi (β + c) (Om (1 + 1)) :=
        psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hc'c)
          (CSet.add_mem (hβown c hc2.le) (CSet.of_lt (hc'c.trans (ldTop_gt hβown hβd hcF))))
      rw [← IH c' hc'c hc'g hc'F]
      exact hTs _ ht'at ht's

/-- **The next base**: `Θ(F^β) = ψ_{Ω₁}(Â + Ω₁)`. -/
theorem ldBlk_next : gxTh (upsilon l) (ldAtR S l) (ldTop S β) = S.psi (Â + Om 1) (Om 1) := by
  have hpv := cdEta_pv (S := S) hl.1 hX
  have hρSC : SC (upsilon l) := hpv ▸ SC_psi Low.InR_Om_one _
  have hρ1 : upsilon l < Om 1 := hpv ▸ psi_lt Low.InR_Om_one _
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hbat := ldBlk_base_atom hβH hβA
  have htat := ldBlk_top_atom hβH hβA
  have hstep := ldBlk_step hl hX hβown hβd hβH hβA hÂ hbase
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hbat).2.1
  have hÂX : Â ∈ S.CSet (Â + Om 1) (S.psi (Â + Om 1) (Om 1)) :=
    (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < S.psi (Â + Om 1) (Om 1) :=
    psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (Om_pos one_ne_zero)) hÂX
  have hle : gxTh (upsilon l) (ldAtR S l) (ldTop S β) ≤ S.psi (Â + Om 1) (Om 1) := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht htF
    rcases ldBlk_cls hl hX hβown hβd ht htF with hle | ⟨c, hcg, hcF, rfl⟩
    · exact (gxTh_mono hle).trans_lt (by rw [hbase]; exact hÂlt)
    · rw [hstep c hcg hcF]
      have hγ : gxTh (upsilon l) (ldAtR S l) c < S.psi (Â + gxTh (upsilon l) (ldAtR S l) c) (Om 1) := by
        rw [← hstep c hcg hcF]; exact gxTh_lt hcg (ldTop_gt hβown hβd hcF)
      have hγ1 := hγ.trans (psi_lt Low.InR_Om_one _)
      have hlt : Â + gxTh (upsilon l) (ldAtR S l) c < Â + Om 1 := (add_lt_add_iff_left Â).2 hγ1
      have hγX := hγ.trans_le (psi_mono (S := S) Low.InR_Om_one hlt.le).1
      exact psi_lt_psi_of_mem Low.InR_Om_one hlt (CSet.add_mem hÂX (CSet.of_lt hγX))
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htat
  refine le_antisymm hle (ldPsi1_le hTSC ?_)
  intro e he hmod
  rcases le_or_gt e Â with heÂ | heÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one heÂ).1 ?_
    rw [← hbase]; exact hTs _ hbat (ldBase_lt_top hβown)
  · obtain ⟨d, rfl⟩ := exists_add_of_le heÂ.le
    have hd1 : d < Om 1 := (add_lt_add_iff_left Â).1 he
    have hdT : d < gxTh (upsilon l) (ldAtR S l) (ldTop S β) := by
      rw [ldMod_add_lt Â hd1] at hmod; exact le_add_self.trans_lt hmod
    obtain ⟨c, hcg, hcF, rfl⟩ := gxTh_onto hdT
    rw [← hstep c hcg hcF]
    exact hTs _ (ldBlk_atom hl hX hβH hβA hcg hcF) (ldTop_lt hβown hcF)

end Blk

/-- **`Θ(ψ_{Ω₂}(0)) = ψ_{Ω₁}(A + 1)`** for every own `A` with `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem ldBlk_zero {l A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi 0 (Om (1 + 1))) = S.psi (A + 1) (Om 1) := by
  have hρSC : SC (upsilon l) := hρ ▸ SC_psi Low.InR_Om_one A
  have hρ1 : upsilon l < Om 1 := hρ ▸ psi_lt Low.InR_Om_one A
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hat : S.psi 0 (Om (1 + 1)) ∈ ldAtR S l :=
    ⟨0, CSet.zero_mem _ _, (Om_pos omega0_ne_zero).trans_le le_self_add, rfl⟩
  have hle : gxTh (upsilon l) (ldAtR S l) (S.psi 0 (Om (1 + 1))) ≤ S.psi (A + 1) (Om 1) := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρ ▸ mxPsi_succ_gt hA) ?_
    rintro t ⟨a, -, -, rfl⟩ ht
    exact absurd ht (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) zero_le).1)
  obtain ⟨hTSC, hρT, -⟩ := ldAtom_ge hρSC hρ1 hAt hat
  refine le_antisymm hle (ldPsi1_le hTSC fun e he _ => ?_)
  exact lt_of_le_of_lt (hρ ▸ (psi_mono (S := S) Low.InR_Om_one (Order.lt_add_one_iff.1 he)).1) hρT

/-! ## The hull transport with an inner induction -/

/-- **The hull transport with an inner induction**: if every atom `s` below `K` moves once every code below `s`
moves, then every code below `K` moves. -/
theorem ldGxStepRec {n : ℕ} {ρ ρ' X K : Ordinal.{0}} {At At' : Set Ordinal.{0}} (hρSC : SC ρ) (hρ1 : ρ < Om 1)
    (hρ'SC : SC ρ') (hρ'1 : ρ' < Om 1) (hAt : GxAt At) (hAt' : GxAt At') (hB : Bc.bcB S n ρ = ρ')
    (hX : SC X) (hρX : ρ < X) (hXL : X < Nc.ncL S ω) (hK : SC K) (hK1 : Om 1 ≤ K)
    (hatom : ∀ s ∈ At, s < K → (∀ x, GxCl ρ At x → x < s → MvD S x ∧ GxCl ρ' At' (Bc.bcB S n x) ∧
      Bc.bcB S n x < K ∧ gxTh ρ At x < X ∧ gxTh ρ' At' (Bc.bcB S n x) = Bc.bcB S n (gxTh ρ At x)) →
      MvD S s ∧ Bc.bcB S n s ∈ At' ∧ Bc.bcB S n s < K ∧ gxTh ρ At s < X ∧
      gxTh ρ' At' (Bc.bcB S n s) = Bc.bcB S n (gxTh ρ At s)) :
    ∀ x, GxCl ρ At x → x < K → MvD S x ∧ GxCl ρ' At' (Bc.bcB S n x) ∧
      Bc.bcB S n x < K ∧ gxTh ρ At x < X ∧ gxTh ρ' At' (Bc.bcB S n x) = Bc.bcB S n (gxTh ρ At x) := by
  have hρL : ρ < Nc.ncL S ω := hρX.trans hXL
  have hXp : IsPrincipal (· + ·) X := hX.isPrincipal
  have hKp : IsPrincipal (· + ·) K := hK.isPrincipal
  have hKo : ∀ a < K, ω ^ a < K := fun a ha => by
    have := hK.2 0 hK.1 a ha; rwa [veblen_zero_apply] at this
  have hXo : ∀ a < X, ω ^ a < X := fun a ha => by
    have := hX.2 0 hX.1 a ha; rwa [veblen_zero_apply] at this
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxK
  rcases lt_trichotomy x (Om 1) with hx1 | hx1 | hx1
  · have hxρ : x < ρ := GxCl.lt_of_lt_Om1 hρSC hAt hx hx1
    have hxL : x < Nc.ncL S ω := hxρ.trans hρL
    have hBx : Bc.bcB S n x < ρ' := by rw [← hB]; exact (Bc.bcB_lt_iff hxL hρL).2 hxρ
    refine ⟨mvD_of_lt hxL, GxCl.small hBx, (hBx.trans hρ'1).trans_le hK1, ?_, ?_⟩
    · rw [gxTh_small hxρ.le]; exact hxρ.trans hρX
    · rw [gxTh_small hxρ.le, gxTh_small hBx.le]
  · subst hx1
    obtain ⟨hD, hBO⟩ := mvB_Om1 (S := S) (k := n)
    refine ⟨hD, by rw [hBO]; exact GxCl.om, by rw [hBO]; exact hxK, ?_, ?_⟩
    · rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρX
    · rw [hBO, gxTh_Om1 hρSC hρ1 hAt, gxTh_Om1 hρ'SC hρ'1 hAt', hB]
  · have hx0 : x ≠ 0 := (lt_of_le_of_lt zero_le hx1).ne'
    by_cases hSCx : SC x
    · have hs := gxSC_atom hρ1 hx hSCx hx1
      obtain ⟨hD, hBs, hBK, hth, he⟩ := hatom x hs hxK fun y hy hyx => IH y hyx hy (hyx.trans hxK)
      exact ⟨hD, GxCl.atom hBs, hBK, hth, he⟩
    by_cases hE : ω ^ x = x
    · obtain ⟨hdec, hax, hbx, -⟩ := mxDec hE (pos_iff_ne_zero.2 hx0) hSCx
      generalize invVeblen₁ x = a at hdec hax
      generalize invVeblen₂ x = b at hdec hbx
      obtain ⟨hga, hgb⟩ := gxDecV hρSC.1 hAt hx a b hdec hbx
      obtain ⟨hDa, hga', haK, hta, hea⟩ := IH a hax hga (hax.trans hxK)
      obtain ⟨hDb, hgb', hbK, htb, heb⟩ := IH b hbx hgb (hbx.trans hxK)
      have hax' : a < veblen a b := by rw [hdec]; exact hax
      have hbx' : b < veblen a b := by rw [hdec]; exact hbx
      obtain ⟨hDx, hBx⟩ := mwB_phi (k := n) hDa hDb hax' hbx'
      have hth : gxTh ρ At (veblen a b) = veblen (gxTh ρ At a) (gxTh ρ At b) := gxTh_phi hρSC hAt a hga b hgb
      have hta' : gxTh ρ At a < veblen (gxTh ρ At a) (gxTh ρ At b) := by
        rw [← hth]; exact gxTh_lt hga hax'
      have htb' : gxTh ρ At b < veblen (gxTh ρ At a) (gxTh ρ At b) := by
        rw [← hth]; exact gxTh_lt hgb hbx'
      obtain ⟨-, hBt⟩ := mwB_phi (k := n) (mvD_of_lt (hta.trans hXL)) (mvD_of_lt (htb.trans hXL)) hta' htb'
      rw [← hdec]
      refine ⟨hDx, ?_, ?_, ?_, ?_⟩
      · rw [hBx]; exact GxCl.phi hga' hgb'
      · rw [hBx]; exact hK.2 _ haK _ hbK
      · rw [hth]; exact hX.2 _ hta _ htb
      · rw [hBx, gxTh_phi hρ'SC hAt' _ hga' _ hgb', hea, heb, hth, hBt]
    · obtain ⟨a, ha⟩ : ∃ a, a = log ω x := ⟨_, rfl⟩
      have hlead : ω ^ a ≤ x := by rw [ha]; exact opow_log_le_self ω hx0
      have hxlt : x < ω ^ a * ω := by
        rw [← opow_succ, ha]; exact lt_opow_succ_log_self one_lt_omega0 x
      have hga : GxCl ρ At a := by rw [ha]; exact (gxDec hρSC hAt x hx).2
      have hgl : GxCl ρ At (ω ^ a) := GxCl.opow hρSC.1 hga
      have hgr : GxCl ρ At (x - ω ^ a) := (gxDec hρSC hAt x hx).1 _ hgl hlead
      have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
      by_cases hr : x - ω ^ a = 0
      · have hxa : ω ^ a = x := by rw [hr, add_zero] at hdec; exact hdec
        have hax : a < x := by
          rcases (right_le_opow a one_lt_omega0).lt_or_eq with h | h
          · rwa [hxa] at h
          · exfalso; apply hE; rw [← hxa]; exact congrArg (ω ^ ·) h.symm
        obtain ⟨hDa, hga', haK, hta, hea⟩ := IH a hax hga (hax.trans hxK)
        have hne : ω ^ a ≠ a := fun h => hax.ne (h.symm.trans hxa)
        obtain ⟨hDx, hBx⟩ := mvB_opow (k := n) hDa hne
        subst hxa
        have hta' : ω ^ gxTh ρ At a < X := hXo _ hta
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GxCl.opow hρ'SC.1 hga'
        · rw [hBx]; exact hKo _ haK
        · rw [gxTh_opow hρSC hAt hga]; exact hta'
        · rw [hBx, gxTh_opow hρ'SC hAt' hga', hea, gxTh_opow hρSC hAt hga, Tp.tpOpowB (hta'.trans hXL)]
      · obtain ⟨r, hr'⟩ : ∃ r, r = x - ω ^ a := ⟨_, rfl⟩
        rw [← hr'] at hgr hdec hr
        have hlx : ω ^ a < x := by
          rw [← hdec]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
        have hrx : r < x := by
          refine lt_of_le_of_ne (by rw [← hdec]; exact le_add_self) fun e => ?_
          have h' : ω ^ a + x = x := by
            calc ω ^ a + x = ω ^ a + r := by rw [e]
              _ = x := hdec
          have := Ordinal.add_eq_right_iff_mul_omega0_le.1 h'
          exact absurd (lt_of_lt_of_le hxlt this) (lt_irrefl _)
        obtain ⟨hDl, hgl', hlK, htl, hel⟩ := IH _ hlx hgl (hlx.trans hxK)
        obtain ⟨hDr, hgr', hrK, htr, her⟩ := IH r hrx hgr (hrx.trans hxK)
        obtain ⟨hDx, hBx⟩ := mvB_add (k := n) hDl hDr
        have hts : gxTh ρ At (ω ^ a + r) = gxTh ρ At (ω ^ a) + gxTh ρ At r := gxTh_add hρSC hAt hgl r
        rw [← hdec]
        refine ⟨hDx, ?_, ?_, ?_, ?_⟩
        · rw [hBx]; exact GxCl.add hgl' hgr'
        · rw [hBx]; exact hKp hlK hrK
        · rw [hts]; exact hXp htl htr
        · rw [hBx, gxTh_add hρ'SC hAt' hgl', hel, her, hts, Bc.bcB_add (htl.trans hXL) (htr.trans hXL)]


end Googology.Trans.PoR.InaccPsi.R2.Ld
