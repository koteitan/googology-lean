import Googology.Trans.PoR.InaccPsi.R2.BtJ
import Googology.Trans.PoR.InaccPsi.R2.OffPhi

/-!
# Theorem GEN below `Φ₁`: the InaccPsi names of all `υ`-points below the first fixed point of `α ↦ Ξ_α`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`, `Ξ_α` the `α`-th fixed point of `υ` (`R2.Xi`), `Φ₁` the least `α ≥ 1`
with `Ξ_α = α` (`R2.Phi1`).

* `seg_upper`, `seg_lower`, `seg_eq` (**Theorem SEG**): if `υ_{ξ₀} = ψ_{Ω₁}(A_{η₀})`, then
  `υ_{ξ₀+ζ} = ψ_{Ω₁}(A_{η₀+ζ})` as long as (HA) holds at every `A_{η₀+ζ'}`, `ζ' < ζ` (and `η₀+ζ < Ω_ω`);
* `HA_seg`: (HA) at `A_{Ω₁·α+ζ}` when `α, ζ < ψ_{Ω₁}(A_{Ω₁·α+ζ})`;
* `Zs α` (the least `ζ` with `ψ_{Ω₁}(A_{Ω₁·α+ζ}) ≤ ζ`), `betaS α = ψ_{Ω₁}(A_{Ω₁·α})`;
  `betaS_succ_eq` (**the jump**): `ψ_{Ω₁}(A_{Ω₁·(α+1)}) = Zs α` (from `psi_le_jump`);
* `gen_fix`, `gen_eq` (**Theorem GEN**): `υ_{ξ₀(α)+ζ} = ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))` for `ζ ≤ Zs α`, where
  `ξ₀(0) = 1`, `ξ₀(α) = ψ_{Ω₁}(A_{Ω₁·α})` (a fixed point of `υ`) for `α ≥ 1`;
* `Xi_eq_betaS`, `Xi_eq_psi`: `Ξ_α = ψ_{Ω₁}(Ω_ω + θ·Ω₁·α)` for `1 ≤ α ≤ Φ₁`; `Zs_eq_Xi`: `Zs α = Ξ_{α+1}`;
  `ups_Xi_add`: `υ_{Ξ_α+ζ} = ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))` for `1 ≤ α < Φ₁`, `ζ ≤ Ξ_{α+1}`;
  `ups_name_lt_Phi1`: every `υ_ξ`, `1 ≤ ξ < Φ₁`, is `ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))` for some `α < Φ₁`, `ζ`;
  `Phi1_eq_psi`: `Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁)`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

theorem A_add (S : InaccSeq.{0}) (η ζ : Ordinal.{0}) :
    ConjT.Aη S (η + ζ) = ConjT.Aη S η + ConjT.th S * ζ := by
  unfold ConjT.Aη; rw [mul_add, add_assoc]

/-! ## Theorem SEG -/

/-- **Theorem SEG, upper half.** -/
theorem seg_upper (S : InaccSeq.{0}) {ξ0 η0 : Ordinal.{0}}
    (h0 : upsilon ξ0 ≤ S.psi (ConjT.Aη S η0) (Om 1)) : ∀ ζ : Ordinal.{0},
    (∀ ζ' < ζ, ConjT.HA S (ConjT.Aη S (η0 + ζ'))) →
      upsilon (ξ0 + ζ) ≤ S.psi (ConjT.Aη S (η0 + ζ)) (Om 1) := by
  intro ζ
  induction ζ using Ordinal.limitRecOn with
  | zero => intro _; simpa using h0
  | add_one ζ ih =>
    intro h
    have h1 := ih (fun ζ' hζ' => h ζ' (hζ'.trans (lt_add_one ζ)))
    have := ups_step S (ξ0 + ζ) (ConjT.Aη S (η0 + ζ)) (ConjT.OmW_le_A S _) (h ζ (lt_add_one ζ)) h1
    rw [← add_assoc, ← add_assoc, ← ConjT.A_succ]
    exact this
  | limit l hl ih =>
    intro h
    refine ups_lim (ξ0 + l) _ (isSuccLimit_add ξ0 hl) fun ι _ hιl => ?_
    rcases le_or_gt ι ξ0 with hι | hι
    · exact (ups_mono hι).trans (h0.trans (psi_A_mono S le_self_add))
    · obtain ⟨ζ', rfl⟩ := exists_add_of_le hι.le
      have hζ' : ζ' < l := (add_lt_add_iff_left _).1 hιl
      exact (ih ζ' hζ' fun ζ'' h'' => h ζ'' (h''.trans hζ')).trans
        (psi_A_mono S (by gcongr))

/-- **Theorem SEG, lower half.** -/
theorem seg_lower (S : InaccSeq.{0}) {ξ0 η0 : Ordinal.{0}}
    (h0 : S.psi (ConjT.Aη S η0) (Om 1) ≤ upsilon ξ0) : ∀ ζ : Ordinal.{0},
    η0 + ζ < Om (ω : Ordinal.{0}) → S.psi (ConjT.Aη S (η0 + ζ)) (Om 1) ≤ upsilon (ξ0 + ζ) := by
  intro ζ
  induction ζ using Ordinal.limitRecOn with
  | zero => intro _; simpa using h0
  | add_one ζ ih =>
    intro h
    have hη : η0 + ζ < Om (ω : Ordinal.{0}) := lt_of_le_of_lt (by gcongr; exact le_self_add) h
    obtain ⟨L, hL, hAL⟩ := exists_goodL S hη
    have h1 := ih hη
    rw [← hAL] at h1
    have := ups_low_step S (ξ0 + ζ) L hL h1
    rw [hAL, ConjT.A_succ] at this
    rw [← add_assoc, ← add_assoc]
    exact this
  | limit l hl ih =>
    intro h
    have hlim : IsSuccLimit (ConjT.Aη S (η0 + l)) := by
      rw [A_add]; exact isSuccLimit_add _ (isSuccLimit_mul_right th_pos hl)
    refine psi_limit_le S hlim fun e he => ?_
    rcases lt_or_ge e (ConjT.Aη S η0) with h1 | h1
    · exact (psi_mono Low.InR_Om_one h1.le).1.trans (h0.trans (ups_mono le_self_add))
    · obtain ⟨d, rfl⟩ := exists_add_of_le h1
      rw [A_add] at he
      have hd : d < ConjT.th S * l := (add_lt_add_iff_left _).1 he
      obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
      have hle : ConjT.Aη S η0 + d ≤ ConjT.Aη S (η0 + c) := by rw [A_add]; gcongr
      have hc' : η0 + c < Om (ω : Ordinal.{0}) := lt_of_le_of_lt (by gcongr) h
      calc S.psi (ConjT.Aη S η0 + d) (Om 1) ≤ S.psi (ConjT.Aη S (η0 + c)) (Om 1) :=
            (psi_mono Low.InR_Om_one hle).1
        _ ≤ upsilon (ξ0 + c) := ih c hc hc'
        _ ≤ upsilon (ξ0 + l) := ups_mono (by gcongr)

/-- **Theorem SEG.** -/
theorem seg_eq (S : InaccSeq.{0}) {ξ0 η0 ζ : Ordinal.{0}}
    (h0 : upsilon ξ0 = S.psi (ConjT.Aη S η0) (Om 1))
    (hHA : ∀ ζ' < ζ, ConjT.HA S (ConjT.Aη S (η0 + ζ'))) (hω : η0 + ζ < Om (ω : Ordinal.{0})) :
    upsilon (ξ0 + ζ) = S.psi (ConjT.Aη S (η0 + ζ)) (Om 1) :=
  le_antisymm (seg_upper S h0.le ζ hHA) (seg_lower S h0.ge ζ hω)

/-! ## (HA) in a segment -/

/-- `θ·ω^b ∈ Cl(A + 1, ψ_{Ω₁}(A))` for `b` in it. -/
theorem th_opow_mem {A b : Ordinal.{0}} (hA : Om (ω : Ordinal.{0}) < A + 1)
    (hb : b ∈ S.CSet (A + 1) (S.psi A (Om 1))) :
    ConjT.th S * ω ^ b ∈ S.CSet (A + 1) (S.psi A (Om 1)) := by
  rw [th_mul_opow, ← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (ConjT.th_mem S hA) hb)

theorem foldr_append (L1 L2 : List Ordinal.{0}) :
    (L1 ++ L2).foldr (· + ·) 0 = L1.foldr (· + ·) 0 + L2.foldr (· + ·) 0 := by
  induction L1 with
  | nil => simp
  | cons x L ih => simp only [List.cons_append, List.foldr_cons, ih, add_assoc]

/-- **(HA)** at `A_{Ω₁·α+ζ}` when `α, ζ < ψ_{Ω₁}(A_{Ω₁·α+ζ})`. -/
theorem HA_seg (S : InaccSeq.{0}) {α ζ : Ordinal.{0}}
    (hα : α < S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1))
    (hζ : ζ < S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1)) :
    ConjT.HA S (ConjT.Aη S (Om 1 * α + ζ)) := by
  set η := Om (1 : Ordinal.{0}) * α + ζ with hη
  obtain ⟨La, ha1, -, ha3⟩ := exists_prin_list α
  obtain ⟨Lz, hz1, -, hz3⟩ := exists_prin_list ζ
  set L := La.map (Om (1 : Ordinal.{0}) * ·) ++ Lz with hLdef
  have hL3 : L.foldr (· + ·) 0 = η := by
    rw [hLdef, foldr_append, foldr_map_mul, ha3, hz3]
  have e : (listA S L).foldr (· + ·) 0 = ConjT.Aη S η := AA_listA S hL3
  have hlt : Om (ω : Ordinal.{0}) < ConjT.Aη S η + 1 :=
    lt_of_le_of_lt (ConjT.OmW_le_A S η) (lt_add_one _)
  unfold ConjT.HA
  suffices h : (listA S L).foldr (· + ·) 0 ∈
      S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η) (Om 1)) by rwa [e] at h
  refine foldr_mem _ fun l hl => ?_
  rcases List.mem_cons.1 hl with rfl | hl
  · exact ConjT.OmW_mem S _ _
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨hp, h0, hle⟩ := ha1 y hy
      obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
      have e2 : Om (1 : Ordinal.{0}) * ω ^ b = ω ^ (Om 1 + b) := by rw [opow_add, Om1_opow]
      rw [e2]
      refine th_opow_mem hlt (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.of_lt ?_))
      exact lt_of_le_of_lt ((Ordinal.right_le_opow b one_lt_omega0).trans hle) hα
    · obtain ⟨hp, h0, hle⟩ := hz1 x hx
      obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
      refine th_opow_mem hlt (CSet.of_lt ?_)
      exact lt_of_le_of_lt ((Ordinal.right_le_opow b one_lt_omega0).trans hle) hζ

/-- Under (HA): `ψ_{Ω₁}(A) < ψ_{Ω₁}(A + θ)`. -/
theorem psi_lt_succ_of_HA {A : Ordinal.{0}} (h : ConjT.HA S A) :
    S.psi A (Om 1) < S.psi (A + ConjT.th S) (Om 1) := by
  have hlt : A < A + ConjT.th S := lt_add_of_pos_right _ th_pos
  refine psi_lt_psi_of_mem Low.InR_Om_one hlt ?_
  have h1 : A + 1 ≤ A + ConjT.th S := by
    gcongr; exact Order.one_le_iff_pos.2 th_pos
  exact CSet_mono h1 (psi_mono Low.InR_Om_one hlt.le).1 h

/-! ## The fixed points `Zs α` -/

/-- `Zs α`: the least `ζ` with `ψ_{Ω₁}(A_{Ω₁·α+ζ}) ≤ ζ`. -/
noncomputable def Zs (S : InaccSeq.{0}) (α : Ordinal.{0}) : Ordinal.{0} :=
  sInf {ζ | S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) ≤ ζ}

/-- `β_α = ψ_{Ω₁}(A_{Ω₁·α})`. -/
noncomputable def betaS (S : InaccSeq.{0}) (α : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (ConjT.Aη S (Om 1 * α)) (Om 1)

theorem Zs_mem (S : InaccSeq.{0}) (α : Ordinal.{0}) :
    S.psi (ConjT.Aη S (Om 1 * α + Zs S α)) (Om 1) ≤ Zs S α :=
  csInf_mem (s := {ζ | S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) ≤ ζ})
    ⟨Om 1, (psi_lt Low.InR_Om_one _).le⟩

theorem lt_psi_of_lt_Zs (S : InaccSeq.{0}) {α ζ : Ordinal.{0}} (h : ζ < Zs S α) :
    ζ < S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) := by
  by_contra hle
  rw [not_lt] at hle
  exact absurd (csInf_le' (s := {ζ | S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) ≤ ζ}) hle) (not_le.2 h)

theorem Zs_fix (S : InaccSeq.{0}) (α : Ordinal.{0}) :
    S.psi (ConjT.Aη S (Om 1 * α + Zs S α)) (Om 1) = Zs S α := by
  refine le_antisymm (Zs_mem S α) ?_
  by_contra hlt
  rw [not_le] at hlt
  have h1 := lt_psi_of_lt_Zs S hlt
  have h2 := psi_A_mono S (show Om 1 * α + S.psi (ConjT.Aη S (Om 1 * α + Zs S α)) (Om 1) ≤
    Om 1 * α + Zs S α by gcongr)
  exact absurd (h1.trans_le h2) (lt_irrefl _)

theorem Zs_SC (S : InaccSeq.{0}) (α : Ordinal.{0}) : SC (Zs S α) := by
  rw [← Zs_fix]; exact SC_psi Low.InR_Om_one _

theorem Zs_lt_Om1 (S : InaccSeq.{0}) (α : Ordinal.{0}) : Zs S α < Om (1 : Ordinal.{0}) := by
  rw [← Zs_fix]; exact psi_lt Low.InR_Om_one _

theorem betaS_mono (S : InaccSeq.{0}) {α α' : Ordinal.{0}} (h : α ≤ α') : betaS S α ≤ betaS S α' :=
  psi_A_mono S (by gcongr)

theorem betaS_le_seg (S : InaccSeq.{0}) (α ζ : Ordinal.{0}) :
    betaS S α ≤ S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) := psi_A_mono S le_self_add

theorem betaS_lt_Om1 (S : InaccSeq.{0}) (α : Ordinal.{0}) : betaS S α < Om (1 : Ordinal.{0}) :=
  psi_lt Low.InR_Om_one _

/-- In the segment of `α` (with `α < β_α`): (HA) at every `A_{Ω₁·α+δ}`, `δ < Zs α`. -/
theorem HA_lt_Zs (S : InaccSeq.{0}) {α δ : Ordinal.{0}} (hα : α < betaS S α) (hδ : δ < Zs S α) :
    ConjT.HA S (ConjT.Aη S (Om 1 * α + δ)) :=
  HA_seg S (hα.trans_le (betaS_le_seg S α δ)) (lt_psi_of_lt_Zs S hδ)

/-- In the segment of `α`: `ψ_{Ω₁}(A_{Ω₁·α+δ}) < Zs α` for `δ < Zs α`. -/
theorem psi_lt_Zs (S : InaccSeq.{0}) {α δ : Ordinal.{0}} (hα : α < betaS S α) (hδ : δ < Zs S α) :
    S.psi (ConjT.Aη S (Om 1 * α + δ)) (Om 1) < Zs S α := by
  have h1 := psi_lt_succ_of_HA (HA_lt_Zs S hα hδ)
  rw [ConjT.A_succ, add_assoc] at h1
  refine h1.trans_le ?_
  rw [← Zs_fix S α]
  exact psi_A_mono S (by gcongr; exact Order.add_one_le_iff.2 hδ)

/-! ## The jump -/

theorem Om_omega_eq_pT_mul : Om (ω : Ordinal.{0}) = pT S * Om ω := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hθΩ : ConjT.th S + Om 1 < Om (ω : Ordinal.{0}) :=
    hSCw.isPrincipal (th_lt_Om_omega S) ((Om_lt_Om.2 one_lt_omega0))
  have e := Low.opow_eq_self_of_SC hSCw
  rw [pT_eq]
  conv_rhs => rw [← e]
  rw [← opow_add, hSCw.isPrincipal.add_eq_right hθΩ, e]

theorem A_Om1_mul (S : InaccSeq.{0}) (α : Ordinal.{0}) :
    ConjT.Aη S (Om 1 * α) = pT S * (Om ω + α) := by
  unfold ConjT.Aη
  rw [mul_add, ← Om_omega_eq_pT_mul, pT, mul_assoc]

/-- **The jump**: `ψ_{Ω₁}(A_{Ω₁·(α+1)}) = Zs α` when `α < β_α`. -/
theorem betaS_succ_eq (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα : α < betaS S α) :
    betaS S (α + 1) = Zs S α := by
  have hZ := Zs_SC S α
  have hZ1 := Zs_lt_Om1 S α
  refine le_antisymm ?_ ?_
  · refine psi_le_jump hZ hZ1 (A_Om1_mul S α) (fun δ hδ => ?_) (le_of_eq ?_)
    · rw [← A_add]; exact psi_lt_Zs S hα hδ
    · rw [mul_add_one, A_add, pT]
  · rw [← Zs_fix S α, betaS, mul_add_one]
    exact psi_A_mono S (by gcongr)

/-! ## Theorem GEN -/

/-- `ξ₀(α)`: `1` for `α = 0`, `β_α` otherwise. -/
noncomputable def xi0 (S : InaccSeq.{0}) (α : Ordinal.{0}) : Ordinal.{0} :=
  if α = 0 then 1 else betaS S α

theorem xi0_le_betaS (S : InaccSeq.{0}) (α : Ordinal.{0}) : xi0 S α ≤ betaS S α := by
  unfold xi0
  split_ifs
  · exact (one_lt_SC (SC_psi Low.InR_Om_one _)).le
  · exact le_rfl

theorem xi0_lt_Zs (S : InaccSeq.{0}) {α : Ordinal.{0}} (hα : α < betaS S α) : xi0 S α < Zs S α := by
  unfold xi0
  split_ifs
  · exact one_lt_SC (Zs_SC S α)
  · have := psi_lt_Zs S hα (Zs_SC S α).1
    rwa [add_zero] at this

theorem lt_Om_omega_seg {α ζ : Ordinal.{0}} (hα : α < Om 1) (hζ : ζ < Om 1) :
    Om 1 * α + ζ < Om (ω : Ordinal.{0}) := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have h1 : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0
  have h2 : Om (1 : Ordinal.{0}) * α < Om ω := by
    have e : Om (1 : Ordinal.{0}) * α ≤ ω ^ (Om 1 + α) := by
      rw [opow_add, Om1_opow]; gcongr; exact Ordinal.right_le_opow _ one_lt_omega0
    have := hSCw.2 0 hSCw.1 _ (hSCw.isPrincipal h1 (hα.trans h1))
    rw [veblen_zero_apply] at this
    exact e.trans_lt this
  exact hSCw.isPrincipal h2 (hζ.trans h1)

/-- The segment of `α`. -/
theorem seg_alpha (S : InaccSeq.{0}) {α ζ : Ordinal.{0}} (hα : α < betaS S α)
    (hfix : upsilon (xi0 S α) = betaS S α) (hζ : ζ ≤ Zs S α) :
    upsilon (xi0 S α + ζ) = S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) := by
  refine seg_eq S (by rw [hfix, betaS]) (fun ζ' hζ' => HA_lt_Zs S hα (hζ'.trans_le hζ)) ?_
  exact lt_Om_omega_seg (hα.trans (betaS_lt_Om1 S α)) (hζ.trans_lt (Zs_lt_Om1 S α))

theorem A_Om1_lim {α : Ordinal.{0}} (hl : IsSuccLimit α) : IsSuccLimit (ConjT.Aη S (Om 1 * α)) := by
  unfold ConjT.Aη
  exact isSuccLimit_add _ (isSuccLimit_mul_right th_pos
    (isSuccLimit_mul_right (Om_pos one_ne_zero) hl))

/-- Below `A_{Ω₁·α}` (`α` a limit) every argument is below some `A_{Ω₁·α'}`, `α' < α`. -/
theorem below_A_lim {α e : Ordinal.{0}} (hl : IsSuccLimit α) (he : e < ConjT.Aη S (Om 1 * α)) :
    ∃ α' < α, e ≤ ConjT.Aη S (Om 1 * α') := by
  rcases lt_or_ge e (Om (ω : Ordinal.{0})) with h1 | h1
  · exact ⟨0, hl.bot_lt, by rw [mul_zero, A_zero]; exact h1.le⟩
  · obtain ⟨d, rfl⟩ := exists_add_of_le h1
    have hd : d < pT S * α := by
      have := (add_lt_add_iff_left _).1 (show Om ω + d < Om ω + ConjT.th S * (Om 1 * α) from he)
      rwa [← mul_assoc] at this
    obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
    refine ⟨c, hc, ?_⟩
    unfold ConjT.Aη
    rw [← mul_assoc]
    gcongr; exact hdc.le

/-- **Theorem GEN, the fixed points**: `υ_{ξ₀(α)} = β_α` (`β_α` a fixed point of `υ` for `α ≥ 1`), for
every `α` with `α' < β_{α'}` for all `α' < α`. -/
theorem gen_fix (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, (∀ α' < α, α' < betaS S α') →
    upsilon (xi0 S α) = betaS S α := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro _
    have h := ups_eq_le_etaS S (zero_le : (0 : Ordinal.{0}) ≤ etaS S)
    rw [add_zero] at h
    rw [xi0, if_pos rfl, h, betaS, mul_zero]
  | add_one α ih =>
    intro h
    have hα : α < betaS S α := h α (lt_add_one α)
    have hfix := ih fun α' h' => h α' (h'.trans (lt_add_one α))
    have hseg := seg_alpha S hα hfix le_rfl
    rw [Zs_fix] at hseg
    have hab : xi0 S α + Zs S α = Zs S α :=
      (Zs_SC S α).isPrincipal.add_eq_right (xi0_lt_Zs S hα)
    rw [hab] at hseg
    rw [xi0, if_neg (add_pos_of_right zero_lt_one α).ne', betaS_succ_eq S hα]
    exact hseg
  | limit α hl ih =>
    intro h
    rw [xi0, if_neg (fun h0 => hl.ne_bot (h0.trans Ordinal.bot_eq_zero.symm))]
    have hSC : SC (betaS S α) := SC_psi Low.InR_Om_one _
    refine le_antisymm ?_ (upsilon_normal.strictMono.id_le _)
    refine ups_lim _ _ hSC.isSuccLimit fun ι _ hι => ?_
    by_contra hgt
    rw [not_le] at hgt
    -- `ι < β_α`: some argument `e < A_{Ω₁·α}` has `ι < ψ_{Ω₁}(e)`
    have : betaS S α ≤ ι := by
      refine psi_limit_le S (A_Om1_lim hl) fun e he => ?_
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨α', hα', hle⟩ := below_A_lim hl he
      have hα1 : α' + 1 < α := hl.add_one_lt hα'
      have hfix := ih (α' + 1) hα1 fun a ha => h a (ha.trans hα1)
      rw [xi0, if_neg (add_pos_of_right zero_lt_one α').ne'] at hfix
      have h1 : ι < betaS S (α' + 1) :=
        hlt.trans_le ((psi_mono Low.InR_Om_one hle).1.trans (betaS_mono S le_self_add))
      have h2 : upsilon ι ≤ betaS S (α' + 1) := (ups_mono h1.le).trans hfix.le
      exact absurd (h2.trans (betaS_mono S hα1.le)) (not_le.2 hgt)
    exact absurd hι (not_lt.2 this)

/-- **Theorem GEN**: `υ_{ξ₀(α)+ζ} = ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))` for `ζ ≤ Zs α`, when `α' < β_{α'}` for every
`α' ≤ α`. -/
theorem gen_eq (S : InaccSeq.{0}) {α ζ : Ordinal.{0}} (h : ∀ α' ≤ α, α' < betaS S α')
    (hζ : ζ ≤ Zs S α) :
    upsilon (xi0 S α + ζ) = S.psi (ConjT.Aη S (Om 1 * α + ζ)) (Om 1) :=
  seg_alpha S (h α le_rfl) (gen_fix S α fun a ha => h a ha.le) hζ

/-! ## The fixed points of `υ` -/

/-- Inside a segment no index is a fixed point of `υ`. -/
theorem not_fix_seg (S : InaccSeq.{0}) {α ζ : Ordinal.{0}} (h : ∀ α' ≤ α, α' < betaS S α')
    (hζ0 : 0 < ζ) (hζ : ζ < Zs S α) : xi0 S α + ζ < upsilon (xi0 S α + ζ) := by
  have hα := h α le_rfl
  rw [gen_eq S h hζ.le]
  have hSC := SC_psi Low.InR_Om_one (ConjT.Aη S (Om 1 * α + ζ)) (S := S)
  refine hSC.isPrincipal ?_ (lt_psi_of_lt_Zs S hζ)
  have h1 := psi_lt_succ_of_HA (HA_lt_Zs S hα (Zs_SC S α).1)
  rw [add_zero, ConjT.A_succ] at h1
  refine (xi0_le_betaS S α).trans_lt (h1.trans_le (psi_A_mono S ?_))
  gcongr; exact Order.one_le_iff_pos.2 hζ0

end Googology.Trans.PoR.InaccPsi.R2.Bt
