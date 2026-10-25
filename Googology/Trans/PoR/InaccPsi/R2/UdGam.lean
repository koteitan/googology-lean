import Googology.Trans.PoR.InaccPsi.R2.UdCode

/-!
# `Γ₂ = ψ_{Ω₃}(0)`, the ladder `X_k` up to `Γ₂` fixed by `B_n`, and the continuity of `ψ_{Ω₂}` at `Γ₂`

`Γ₂ = Ua.uaGam` (the least strongly critical ordinal above `Ω₂`), `f(a) = φ(a, 0)`, `B_n = Bc.bcB S n`.

* `udGam_eq` (**`Γ₂ = ψ_{Ω₃}(0)`**: `Cl(0, Γ₂) ∩ Ω₃ ⊆ Γ₂`, so `ψ_{Ω₃}(0) ≤ Γ₂`; `Ua.uaGam_le_G3` is the other half);
* `udGam_nfp` (**`Γ₂ = nfp f (Ω₂ + 1)`**);
* `udX` (`X_k = f^{k+1}(Ω₂ + 1)`; `X_0 = φ(Ω₂ + 1, 0) = Ua.uaX3`), `udX_lt` (`X_k < Γ₂`), `udX_lim`, `udX_cof`
  (**the `X_k` are cofinal in `Γ₂`**), `udX_B` (**`B_n X_k = X_k`**), `udX_mono`;
* `udPsi_Gam` (**`ψ_{Ω₂}(Γ₂) = sup_{e < Γ₂} ψ_{Ω₂}(e)`**: an `s < ψ_{Ω₂}(Γ₂)` is below `ψ_{Ω₂}(W^{W^{X_k}})` for
  some `k`).

No new axiom.  New definition: `udX`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ud

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu
  Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **`Γ₂ = ψ_{Ω₃}(0)`.** -/
theorem udGam_eq : uaGam = S.psi 0 (Om (1 + 1 + 1)) := by
  refine le_antisymm uaGam_le_G3 (psi_le_of_good ?_ ?_)
  · exact CSet.Om_mem (CSet.add_mem (CSet.add_mem (CSet.one_mem _ _) (CSet.one_mem _ _)) (CSet.one_mem _ _))
  have hS := uaGam_spec.1
  have h1 : (1 : Ordinal.{0}) < Om 1 := gg_one_lt_of_SC Ph.ph_SC_Om1
  have h3 : (1 + 1 + 1 : Ordinal.{0}) < Om 1 :=
    Ph.ph_SC_Om1.isPrincipal (Ph.ph_SC_Om1.isPrincipal h1 h1) h1
  have hI : ∀ n, Om (1 + 1 + 1 : Ordinal.{0}) ≤ S.I n := fun n => by
    rw [← S.fix n]; exact Om_le_Om.2 (h3.le.trans (Low.Om_one_le_I (S := S) n))
  intro x hx
  induction hx with
  | small h => exact fun _ => h
  | zero => exact fun _ => hS.1
  | inacc n => exact fun h => absurd h (not_lt.2 (hI n))
  | inaccW => exact fun h => absurd h (not_lt.2 ((hI 0).trans (S.I_le_Iw 0)))
  | add _ _ ihx ihy =>
    exact fun h => hS.isPrincipal (ihx (le_self_add.trans_lt h)) (ihy (le_add_self.trans_lt h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => hS.2 _ (ihx ((left_le_veblen x y).trans_lt h)) _ (ihy ((right_le_veblen x y).trans_lt h))
  | @om x _ _ =>
    intro h
    have hx : x < 1 + 1 + 1 := Om_lt_Om.1 h
    exact (Om_le_Om.2 (Order.lt_add_one_iff.1 hx)).trans_lt uaGam_spec.2
  | @coll π e _ _ _ _ _ => exact absurd (show e.1 < 0 from e.2) (not_lt.2 zero_le)

/-- **`Γ₂ = nfp (φ(·, 0)) (Ω₂ + 1)`.** -/
theorem udGam_nfp : uaGam = nfp (fun a => veblen a 0) (Om (1 + 1 : Ordinal.{0}) + 1) := by
  have hfm : Monotone (fun a : Ordinal.{0} => veblen a 0) := veblen_zero_strictMono.monotone
  have hfp := nfp_fp isNormal_veblen_zero (Om (1 + 1 : Ordinal.{0}) + 1)
  have hgt : Om (1 + 1 : Ordinal.{0}) < nfp (fun a => veblen a 0) (Om (1 + 1) + 1) :=
    (lt_add_one _).trans_le (le_nfp _ _)
  refine le_antisymm (uaGam_le ?_ hgt) (nfp_le_fp hfm (Order.add_one_le_of_lt uaGam_spec.2)
    uaGam_spec.1.veblen_zero.le)
  exact Ru.ruSC_of_veblen ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans hgt) hfp

/-- The iterates `f^k(Ω₂ + 1)`. -/
theorem udIt_lt : ∀ k : ℕ, (fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1) < uaGam ∧
    Om (1 + 1) < (fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1) := by
  intro k
  induction k with
  | zero => exact ⟨uaGam_spec.1.isSuccLimit.add_one_lt uaGam_spec.2, lt_add_one _⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨uaGam_spec.1.2 _ ih.1 _ uaGam_spec.1.1, ih.2.trans_le (left_le_veblen _ _)⟩

/-- A level `Ω₂ < a < Γ₂` has `a < φ(a, 0)`. -/
theorem udLt_veb0 {a : Ordinal.{0}} (h2 : Om (1 + 1) < a) (hG : a < uaGam) : a < veblen a 0 := by
  refine lt_of_le_of_ne (left_le_veblen a 0) fun e => ?_
  have hSC := Ru.ruSC_of_veblen ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans h2) e.symm
  exact absurd (uaGam_le hSC h2) (not_le.2 hG)

/-- **The ladder `X_k = f^{k+1}(Ω₂ + 1)`** (`f(a) = φ(a, 0)`). -/
noncomputable def udX (k : ℕ) : Ordinal.{0} := (fun a : Ordinal.{0} => veblen a 0)^[k + 1] (Om (1 + 1) + 1)

theorem udX_eq (k : ℕ) :
    udX k = veblen ((fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1)) 0 := by
  unfold udX; rw [Function.iterate_succ_apply']

theorem udX_lt (k : ℕ) : udX k < uaGam := (udIt_lt (k + 1)).1

theorem udX_gt (k : ℕ) : Om (1 + 1) < udX k := (udIt_lt (k + 1)).2

theorem udX_lim (k : ℕ) : IsSuccLimit (udX k) := by
  rw [udX_eq]
  exact taVeb_lim ((Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans (udIt_lt k).2).ne'

theorem udX_zero : udX 0 = uaX3 := by rw [udX_eq]; rfl

theorem udX_lt_G3 (k : ℕ) : udX k < S.psi 0 (Om (1 + 1 + 1)) := (udX_lt k).trans_le uaGam_le_G3

/-- **The `X_k` are cofinal in `Γ₂`.** -/
theorem udX_cof {e : Ordinal.{0}} (he : e < uaGam) : ∃ k, e < udX k := by
  rw [udGam_nfp] at he
  obtain ⟨k, hk⟩ := lt_nfp_iff.1 he
  refine ⟨k, hk.trans_le ?_⟩
  rw [udX_eq]; exact left_le_veblen _ _

/-- **`B_n` fixes every `f^k(Ω₂ + 1)`.** -/
theorem udIt_B {n : ℕ} : ∀ k : ℕ, MvD S ((fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1)) ∧
    Bc.bcB S n ((fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1)) =
      (fun a : Ordinal.{0} => veblen a 0)^[k] (Om (1 + 1) + 1) := by
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (Lw.lw_L_SC S ω).1
  intro k
  induction k with
  | zero =>
    obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
    have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
    obtain ⟨hD21, hB21⟩ := mvB_add (k := n) hD2 hD1
    rw [hB2, mwB_one] at hB21
    exact ⟨hD21, hB21⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hDy, hBy⟩ := ih
    obtain ⟨hD, hB⟩ := mwB_phi (k := n) hDy hD0 (udLt_veb0 (udIt_lt k).2 (udIt_lt k).1) veblen_pos
    rw [hBy, Bc.bcB_zero] at hB
    exact ⟨hD, hB⟩

theorem udX_B {n : ℕ} (k : ℕ) : MvD S (udX k) ∧ Bc.bcB S n (udX k) = udX k := udIt_B (k + 1)

theorem udX_mono {j k : ℕ} (h : j ≤ k) : udX j ≤ udX k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    rw [udX_eq (_ + 1)]
    unfold udX
    exact left_le_veblen _ _

/-- **`ψ_{Ω₂}` is continuous at `Γ₂`**: an `s < ψ_{Ω₂}(Γ₂)` is below `ψ_{Ω₂}(W^{W^{X_k}})` for some `k`. -/
theorem udPsi_Gam {s : Ordinal.{0}} (hs : s < S.psi uaGam (Om (1 + 1))) :
    ∃ k, s < S.psi (leWe (leWe (udX k))) (Om (1 + 1)) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  rw [Lw.lw_psi_limit S hκ uaGam_spec.1.isSuccLimit] at hs
  have hbdd : BddAbove (range fun e : Iio uaGam => S.psi e.1 (Om (1 + 1))) :=
    ⟨Om (1 + 1), by rintro _ ⟨e, rfl⟩; exact (psi_lt hκ _).le⟩
  haveI : Nonempty (Iio uaGam) := ⟨⟨0, uaGam_spec.1.1⟩⟩
  obtain ⟨⟨e, he⟩, hse⟩ := (lt_ciSup_iff hbdd).1 hs
  obtain ⟨k, hk⟩ := udX_cof he
  refine ⟨k, hse.trans_le (psi_mono hκ ?_).1⟩
  exact hk.le.trans ((tnLe_We _).trans (tnLe_We _))

end Googology.Trans.PoR.InaccPsi.R2.Ud
