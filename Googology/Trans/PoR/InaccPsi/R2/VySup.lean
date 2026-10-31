import Googology.Trans.PoR.InaccPsi.R2.SoSupQ
import Googology.Trans.PoR.InaccPsi.R2.GgOtp

/-!
# The supply reduced to the order type of the code set

`ρ = ρ_μ = υ_μ`, `θ₂ = ψ_{Ω₃}(Ω_ω)`, `θ_{k+1} = Lc.lcTh S (k+1)`.  The block step of `So.soSup_gen` asks of its code
map only: monotone, `c(x+1) = c(x)+1`, values in the code set
`vyC ρ = {c : Ω_ω + θ₂·c ∈ Cl(a, b) for all a > Ω_ω, b ≥ ρ}` below `θ_{k+1}`.  The enumeration of `vyC ρ ∩ θ_{k+1}`
is such a map, so the supply reaches as far as this order type.

* `vyC_succ` (the code set is closed under `+1`), `vyOtp_succ` (`otp(C ∩ (c+1)) = otp(C ∩ c) + 1` for `c ∈ C`),
  `vyEnum_spec`, `vyEnum_lt`, `vyEnum_succ` (the enumeration);
* `vyOtp_of_map` (a strictly increasing map `X → C ∩ m` gives `X ≤ otp(C ∩ m)`);
* `vySup` (**`υ_{μ+X} ≤ Θ_μ(G') ≤ r(μ)` at every Range restart with code `G_{k+1}+1`, for every limit `X ≤ Ω₁`
  with `X ≤ otp(vyC ρ_μ ∩ θ_{k+1})` and `η_μ + y` good for `y < X`**);
* `vySup_rho` (non-vacuity: the order-type hypothesis holds at `X = ρ^ρ`, by the code map of `So.soSupQ`).

New definitions: `vyC` (a set of codes), `vyEnum` (its enumeration).  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The code set over `ρ`**: the `c` with `Ω_ω + θ₂·c ∈ Cl(a, b)` for every `a > Ω_ω`, `b ≥ ρ`. -/
def vyC (S : InaccSeq.{0}) (ρ : Ordinal.{0}) : Set Ordinal.{0} :=
  {c | ∀ a b, Om ω < a → ρ ≤ b → Om ω + Lc.lcTh S 2 * c ∈ S.CSet a b}

theorem vyC_succ {ρ c : Ordinal.{0}} (hc : c ∈ vyC S ρ) : c + 1 ∈ vyC S ρ := by
  intro a b ha hb
  rw [mul_add_one, ← add_assoc]
  exact CSet.add_mem (hc a b ha hb) (Ls.lsTh_mem ha 2)

/-- `otp(C ∩ (c+1)) = otp(C ∩ c) + 1` for `c ∈ C`. -/
theorem vyOtp_succ {C : Set Ordinal.{0}} {c : Ordinal.{0}} (hc : c ∈ C) : cdOtp C (c + 1) = cdOtp C c + 1 := by
  classical
  refine le_antisymm ?_ (Order.add_one_le_of_lt (cdOtp_lt_of_mem hc (lt_add_one c)))
  rw [cdOtp_eq C (c + 1)]
  refine ciSup_le' fun d => ?_
  split_ifs
  · exact add_le_add_left (cdOtp_mono C (Order.lt_add_one_iff.1 d.2)) 1
  · exact zero_le

/-- Two members with the same order type are equal. -/
theorem vyOtp_inj {C : Set Ordinal.{0}} {c c' : Ordinal.{0}} (hc : c ∈ C) (hc' : c' ∈ C)
    (e : cdOtp C c = cdOtp C c') : c = c' := by
  rcases lt_trichotomy c c' with h | h | h
  · exact absurd e (cdOtp_lt_of_mem hc h).ne
  · exact h
  · exact absurd e.symm (cdOtp_lt_of_mem hc' h).ne

open Classical in
/-- **The enumeration of `C ∩ m`**: the member of `C` below `m` of order type `x`. -/
noncomputable def vyEnum (C : Set Ordinal.{0}) (m x : Ordinal.{0}) : Ordinal.{0} :=
  if h : ∃ c ∈ C, c < m ∧ cdOtp C c = x then Classical.choose h else 0

theorem vyEnum_spec {C : Set Ordinal.{0}} {m x : Ordinal.{0}} (hx : x < cdOtp C m) :
    vyEnum C m x ∈ C ∧ vyEnum C m x < m ∧ cdOtp C (vyEnum C m x) = x := by
  have h := Gg.ggOtp_onto C m x hx
  have hd : vyEnum C m x = Classical.choose h := by unfold vyEnum; rw [dif_pos h]
  rw [hd]; exact Classical.choose_spec h

theorem vyEnum_lt {C : Set Ordinal.{0}} {m x y : Ordinal.{0}} (hy : y < cdOtp C m) (hxy : x < y) :
    vyEnum C m x < vyEnum C m y := by
  obtain ⟨-, -, ex⟩ := vyEnum_spec (hxy.trans hy)
  obtain ⟨-, -, ey⟩ := vyEnum_spec hy
  by_contra hle
  push Not at hle
  have := cdOtp_mono C hle
  rw [ex, ey] at this
  exact absurd hxy (not_lt.2 this)

theorem vyEnum_succ {C : Set Ordinal.{0}} (hC : ∀ c ∈ C, c + 1 ∈ C) {m x : Ordinal.{0}}
    (hx : x + 1 < cdOtp C m) : vyEnum C m (x + 1) = vyEnum C m x + 1 := by
  obtain ⟨h1, -, e1⟩ := vyEnum_spec hx
  obtain ⟨h0, -, e0⟩ := vyEnum_spec ((lt_add_one x).trans hx)
  refine vyOtp_inj h1 (hC _ h0) ?_
  rw [e1, vyOtp_succ h0, e0]

/-- **A strictly increasing map into `C ∩ m` bounds the order type from below.** -/
theorem vyOtp_of_map {C : Set Ordinal.{0}} {m X : Ordinal.{0}} (c : Ordinal.{0} → Ordinal.{0})
    (hmem : ∀ x < X, c x ∈ C) (hlt : ∀ x < X, c x < m) (hmono : ∀ y x, y < x → x < X → c y < c x) :
    X ≤ cdOtp C m := by
  have key : ∀ x, x < X → x ≤ cdOtp C (c x) := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x IH =>
    intro hx
    refine le_of_forall_lt fun y hy => ?_
    exact (IH y hy (hy.trans hx)).trans_lt (cdOtp_lt_of_mem (hmem y (hy.trans hx)) (hmono y x hy hx))
  exact le_of_forall_lt fun x hx => (key x hx).trans_lt (cdOtp_lt_of_mem (hmem x hx) (hlt x hx))

/-- **THE SUPPLY FROM THE ORDER TYPE OF THE CODE SET**: at a Range restart `μ` with code `G_{k+1}+1`, every limit
`X ≤ Ω₁` with `η_μ + y` good for `y < X` and `X ≤ otp(vyC ρ_μ ∩ θ_{k+1})` has `υ_{μ+X} ≤ Θ_μ(G') ≤ r(μ)`. -/
theorem vySup (k : ℕ) {μ X : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hXl : IsSuccLimit X) (hgood : ∀ y < X, Bt.Good S (cdEta S μ + y)) (hX1 : X ≤ Om 1)
    (hX : X ≤ cdOtp (vyC S (upsilon μ)) (Lc.lcTh S (k + 1))) :
    upsilon (μ + X) ≤ cdTheta S μ (Ls.lsG S (k + 1)) ∧ upsilon (μ + X) ≤ cdR S μ := by
  set C := vyC S (upsilon μ)
  set m := Lc.lcTh S (k + 1)
  refine So.soSup_gen hR hc hXl hgood hX1 (vyEnum C m) (fun x hx => ?_) (fun y x hyx hx => ?_)
    (fun x hx => (vyEnum_spec (hx.trans_le hX)).1) (fun x hx => (vyEnum_spec (hx.trans_le hX)).2.1)
  · exact vyEnum_succ (fun c hc => vyC_succ hc) (hx.trans_le hX)
  · rcases hyx.lt_or_eq with h | h
    · exact (vyEnum_lt (hx.trans_le hX) h).le
    · rw [h]

/-- **Non-vacuity of the order-type hypothesis**: it holds at `X = ρ^ρ` (the code map `So.soQ` of
`So.soSupQ`), at every Range restart with code `G_{k+1}+1`. -/
theorem vySup_rho (k : ℕ) {μ : Ordinal.{0}} (hR : CdRange S μ) :
    upsilon μ ^ upsilon μ ≤ cdOtp (vyC S (upsilon μ)) (Lc.lcTh S (k + 1)) := by
  obtain ⟨-, -, hpv⟩ := Ra.raName hR
  set ρ := upsilon μ with hρdef
  have hρE : InE ρ := by rw [← hpv]; exact Sl.slPv_E _
  have hρ1 : 1 < ρ := So.soOne_lt_E hρE
  have hρΩ : ρ < Om 1 := So.soRho_lt_Om1 hR
  refine vyOtp_of_map (So.soQ (Om 1) ρ) (fun x hx a b ha hb => ?_) (fun x hx => ?_)
    (fun y x hyx hx => So.soQ_strict hρ1 x y hyx ((So.soMX_lt hρ1 y (hyx.trans hx)).trans hρΩ)
      ((So.soMX_lt hρ1 x hx).trans hρΩ))
  · have h := So.soQMem (S := S) hρ1 hb x hx _ (Ls.lsTh_mem ha 2)
    rw [Ls.lsTh_opow] at h
    exact CSet.add_mem (ConjT.OmW_mem S a b) h
  · have hE : InE (Lc.lcTh S (k + 1)) := Low.opow_eq_self_of_SC (Ls.lsTh_SC (k + 1))
    have hO := Rp.rpOm1_lt_th (S := S) k
    exact (So.soQ_lt (r := Om 1) hρ1 x ρ hx ((So.soMX_lt hρ1 x hx).trans hρΩ)).trans
      (So.soE_opow_lt hE hO (hρΩ.trans hO))

#print axioms vyOtp_succ
#print axioms vyEnum_succ
#print axioms vyOtp_of_map
#print axioms vySup
#print axioms vySup_rho

end Googology.Trans.PoR.InaccPsi.R2.Vy
