import Googology.Trans.PoR.InaccPsi.R2.SwShp

/-!
# Derivations with the ω-limit rule, and the towers below the leaves

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `L_k = ε_{Ω₂+1+k}`, `L̂_k = ε_{Ω₁+1+k}`.

`SwDer S λ Ow E Ê` (**a derivation**): the rules of `Sc.ScDer` (`code`, `succ`, `om`, `lim`, `weaken`) with
members derived in `SwDer`, and
* `wlim` (**the ω-limit rule**): own data `Sc.ScOwP Ow E Ê`, members `e_k < E` with images `ê_k < Ê` derived with
  the same own predicate, `W^{e_k}` cofinal in `W^E` and `Ω^{ê_k}` cofinal in `Ω^Ê` give `E` (`Sq.sqLevLim`).

* `swDer_sound` (**SOUNDNESS: every derivation gives the level statement `Sc.ScLev Ow E Ê` and the own data**);
* the towers below a leaf: `swTwg κ k` (`t_0 = φ(1, κ + k) + 1`, `t_{j+1} = ω^{κ·t_j}`), `swTwg_lt`,
  `swTwg_cof` (**cofinal in `φ(1, κ + (k+1))`**: `φ(1, A + 1) = nfp(ω^·)(φ(1, A) + 1)`), the tower terms
  `swTw k j` with values `swTwg Ω₂ k j` and images `swTwg Ω₁ k j`, own under every evaluation (`swTw_own`);
* `swE_lt_G3`, `swEh_lt_G` (contexts stay below `ψ_{Ω₃}(0)`, `ψ_{Ω₂}(0)`).

No new axiom.  New definitions: `SwDer`, `swTwg`, `swBase`, `swTw`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **A derivation of the exponent `E` (image `Ê`, own predicate `Ow`), with the ω-limit rule.** -/
inductive SwDer (S : InaccSeq.{0}) (l : Ordinal.{0}) :
    (Ordinal.{0} → Ordinal.{0} → Prop) → Ordinal.{0} → Ordinal.{0} → Prop
  | code {E : Ordinal.{0}} : GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < Om (1 + 1) →
      SwDer S l (fun b X0 => ∃ j, E < rwEX S X0 b j) E (gxTh (upsilon l) (ldAtR S l) E)
  | succ {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} :
      SwDer S l Ow E Eh → SwDer S l Ow (E + 1) (Eh + 1)
  | om {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs : Ordinal.{0}} :
      (∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b))) →
      (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      (∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < Om (1 + 1) →
        SwDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ < scSq S (fun z => leWe (g z)) X0 b j) (g ζ)
          (gh (gxTh (upsilon l) (ldAtR S l) ζ))) →
      SwDer S l Ow gs ghs
  | lim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {g gh : Ordinal.{0} → Ordinal.{0}} {gs ghs η : Ordinal.{0}} :
      (∀ b X0, Ow b X0 → ScShp S l g gh gs ghs (leTe S (X0 + leWe (g 1)) b)
        (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe (g 1)) b))) →
      (∀ b β X0 X0', Ow b X0 → b ≤ β → X0 ≤ X0' → Ow β X0') →
      GxCl (upsilon l) (ldAtR S l) η → η < Om (1 + 1) → IsSuccLimit η →
      (∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < η →
        SwDer S l (fun b X0 => Ow b X0 ∧ ∃ j, ζ + 1 < scSq S (fun z => leWe (g z)) X0 b j) (g (ζ + 1))
          (gh (gxTh (upsilon l) (ldAtR S l) (ζ + 1)))) →
      SwDer S l (fun b X0 => Ow b X0 ∧ ∃ j, η < scSq S (fun z => leWe (g z)) X0 b j) (g η)
        (gh (gxTh (upsilon l) (ldAtR S l) η))
  | weaken {Ow Ow' : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} :
      SwDer S l Ow E Eh → (∀ b X0, Ow' b X0 → Ow b X0) →
      (∀ b β X0 X0', Ow' b X0 → b ≤ β → X0 ≤ X0' → Ow' β X0') → SwDer S l Ow' E Eh
  | wlim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} {e eh : ℕ → Ordinal.{0}} :
      ScOwP S l Ow E Eh → E < S.psi 0 (Om (1 + 1 + 1)) → Eh < S.psi 0 (Om (1 + 1)) →
      (∀ k, SwDer S l Ow (e k) (eh k)) → (∀ k, e k < E) → (∀ k, eh k < Eh) →
      (∀ y, y < leWe E → ∃ k, y < leWe (e k)) → (∀ z, z < leOe Eh → ∃ k, z < leOe (eh k)) →
      SwDer S l Ow E Eh

section Sound

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **SOUNDNESS: every derivation gives the level statement and the data of its own predicate.** -/
theorem swDer_sound {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (h : SwDer S l Ow E Eh) :
    ScLev S l Ow E Eh ∧ ScOwP S l Ow E Eh := by
  induction h with
  | code hE h1 hEW => exact ⟨scLev_code_iff.2 (rwLevC_all hl hX _ hE h1 hEW), scOwP_code hl hX h1 hE hEW⟩
  | succ _ IH => exact ⟨scLev_succ hl hX IH.2 IH.1 (fun _ _ h => h), scOwP_succ IH.2⟩
  | om hshp hmono _ IH =>
    exact ⟨scLev_om hl hX hshp (fun b β X0 hO hb => hmono b β X0 X0 hO hb le_rfl)
      (fun ζ hζ h1 hζW => (IH ζ hζ h1 hζW).1), scOwP_om hshp hmono⟩
  | lim hshp hmono hη hηW hlim _ IH =>
    exact ⟨scLev_lim hl hX hshp hmono hη hηW hlim (fun ζ hζ hζη => (IH ζ hζ hζη).1),
      scOwP_mem hshp hmono hη (rvLim_one_lt hlim).le⟩
  | weaken _ himp hmono IH =>
    exact ⟨fun b X0 Xh0 hoff hd hG3 hG hO => IH.1 b X0 Xh0 hoff hd hG3 hG (himp b X0 hO),
      ⟨fun b X0 hO => IH.2.dat b X0 (himp b X0 hO), hmono⟩⟩
  | wlim hP hEG hEhG _ hek hehk hcof hcofh IH =>
    exact ⟨Sq.sqLevLim hl hX hP hEG hEhG (Ow' := fun _ => _) (fun k => (IH k).2) (fun k => (IH k).1)
      (fun _ _ _ h => h) hek hehk hcof hcofh, hP⟩

end Sound

/-! ## Towers below the leaves -/

/-- `φ(1, A + 1) = nfp(ω^·)(φ(1, A) + 1)`. -/
theorem swVeb_succ (A : Ordinal.{0}) : veblen 1 (A + 1) = nfp (fun a : Ordinal.{0} => ω ^ a) (veblen 1 A + 1) := by
  have h1 : ∀ x, veblen 1 x = deriv (fun a : Ordinal.{0} => ω ^ a) x := by
    intro x
    have e : veblen (0 + 1 : Ordinal.{0}) = deriv (veblen 0) := veblen_add_one 0
    rw [zero_add, veblen_zero] at e
    rw [e]
  rw [h1, h1, ← Order.succ_eq_add_one, deriv_succ, Order.succ_eq_add_one]

/-- **The tower below the leaf `φ(1, κ + (k+1))`**: `t_0 = φ(1, κ + k) + 1`, `t_{j+1} = ω^{κ·t_j}`. -/
noncomputable def swTwg (κ : Ordinal.{0}) (k : ℕ) : ℕ → Ordinal.{0}
  | 0 => veblen 1 (κ + (k : Ordinal.{0})) + 1
  | j + 1 => ω ^ (κ * swTwg κ k j)

section Tw

variable {κ : Ordinal.{0}} (hκ : SC κ)

include hκ

/-- `x < φ(1, κ + (k+1))` gives `ω^{κ·x} < φ(1, κ + (k+1))`. -/
theorem swOpow_lt {k : ℕ} {x : Ordinal.{0}} (hx : x < veblen 1 (κ + ((k : Ordinal.{0}) + 1))) :
    ω ^ (κ * x) < veblen 1 (κ + ((k : Ordinal.{0}) + 1)) := by
  set L := veblen 1 (κ + ((k : Ordinal.{0}) + 1))
  have hE : ω ^ L = L := gg_veblen_eps one_ne_zero
  have hp := Ph.ph_veblen_prin (1 : Ordinal.{0}) (κ + ((k : Ordinal.{0}) + 1))
  have hk : κ * x < L := by
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [mul_zero]; exact veblen_pos
    have hlt : κ * x ≤ ω ^ (κ + x) := by
      rw [opow_add, gg_SC_eps hκ]
      exact mul_le_mul_right (right_le_opow x one_lt_omega0) _
    exact hlt.trans_lt (by
      conv_rhs => rw [← hE]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hp (swK_lt_L k) hx))
  conv_rhs => rw [← hE]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 hk

theorem swTwg_lt (k : ℕ) : ∀ j, swTwg κ k j < veblen 1 (κ + ((k : Ordinal.{0}) + 1))
  | 0 => by
    have h1 : veblen 1 (κ + (k : Ordinal.{0})) < veblen 1 (κ + ((k : Ordinal.{0}) + 1)) :=
      (veblen_right_strictMono 1).lt_iff_lt.2 (by rw [← add_assoc]; exact lt_add_one _)
    have hlim : IsSuccLimit (veblen 1 (κ + ((k : Ordinal.{0}) + 1))) := by
      rw [← gg_veblen_eps (x := (1 : Ordinal.{0})) one_ne_zero]
      exact isSuccLimit_opow_left isSuccLimit_omega0 (veblen_pos).ne'
    exact hlim.succ_lt h1
  | j + 1 => swOpow_lt hκ (swTwg_lt k j)

omit hκ in
theorem swTwg_pos (k : ℕ) : ∀ j, 0 < swTwg κ k j
  | 0 => zero_lt_one.trans_le le_add_self
  | _ + 1 => opow_pos _ omega0_pos

/-- `(ω^·)^[n](φ(1, κ + k) + 1) ≤ t_n`. -/
theorem swIter_le (k : ℕ) : ∀ n : ℕ,
    (fun a : Ordinal.{0} => ω ^ a)^[n] (veblen 1 (κ + (k : Ordinal.{0})) + 1) ≤ swTwg κ k n
  | 0 => le_rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    refine (opow_le_opow_right omega0_pos (swIter_le k n)).trans ?_
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right _ hκ.1)

/-- **The tower is cofinal in the leaf.** -/
theorem swTwg_cof (k : ℕ) {x : Ordinal.{0}} (hx : x < veblen 1 (κ + ((k : Ordinal.{0}) + 1))) :
    ∃ j, x < swTwg κ k j := by
  rw [← add_assoc, swVeb_succ] at hx
  obtain ⟨n, hn⟩ := lt_nfp_iff.1 hx
  exact ⟨n, hn.trans_le (swIter_le hκ k n)⟩

end Tw

/-- **The base term of the tower of `L_k`**: `Ω₂ + 1` for `k = 0`, `L_{k-1} + 1` otherwise. -/
def swBase : ℕ → SwT
  | 0 => .term (.term .zero (.term .zero .zero 1) 1) .zero 1
  | k + 1 => .term (.eps k) .zero 1

/-- **The tower terms of `L_k`**: `t_0 = swBase k`, `t_{j+1} = W^{t_j}`. -/
def swTw (k : ℕ) : ℕ → SwT
  | 0 => swBase k
  | j + 1 => .term .zero (swTw k j) 1

section TwT

variable {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) < upsilon l)

include h1

theorem swTw_val (k : ℕ) : ∀ j, swV (swTw k j) = swTwg (Om (1 + 1)) k j ∧
    swI S l (swTw k j) = swTwg (Om 1) k j
  | 0 => by
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    cases k with
    | zero =>
      show (0 + leWe (0 + leWe 0 * 1) * 1) + leWe 0 * 1 = _ ∧
        (0 + leOe (0 + leOe 0 * gxTh (upsilon l) (ldAtR S l) 1) * gxTh (upsilon l) (ldAtR S l) 1) +
          leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      simp only [swTwg, hΘ1, leWe_zero, leOe_zero, mul_one, zero_add, Nat.cast_zero, add_zero, leWe_one]
      refine ⟨by rw [ldOm2_SC.veblen_right (gg_one_lt_of_SC ldOm2_SC)], ?_⟩
      have : leOe 1 = Om 1 := by unfold leOe; rw [mul_one, gg_SC_eps Ph.ph_SC_Om1]
      rw [this, Ph.ph_SC_Om1.veblen_right (gg_one_lt_of_SC Ph.ph_SC_Om1)]
    | succ k =>
      show swL k + leWe 0 * 1 = _ ∧ swLh k + leOe 0 * gxTh (upsilon l) (ldAtR S l) 1 = _
      simp only [swTwg, hΘ1, leWe_zero, leOe_zero, mul_one, swL, swLh, Nat.cast_succ]
      exact ⟨trivial, trivial⟩
  | j + 1 => by
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small h1.le
    obtain ⟨e1, e2⟩ := swTw_val k j
    show 0 + leWe (swV (swTw k j)) * 1 = _ ∧ 0 + leOe (swI S l (swTw k j)) * gxTh (upsilon l) (ldAtR S l) 1 = _
    rw [e1, e2, hΘ1, mul_one, mul_one, zero_add, zero_add]
    exact ⟨rfl, rfl⟩

theorem swTw_wf (k : ℕ) : ∀ j, SwWF S l (swTw k j)
  | 0 => by
    have hc : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small h1
    have hW := gg_one_lt_of_SC ldOm2_SC
    cases k with
    | zero => exact ⟨⟨trivial, ⟨trivial, trivial, hc, le_rfl, hW⟩, hc, le_rfl, hW⟩, trivial, hc, le_rfl, hW⟩
    | succ k => exact ⟨trivial, trivial, hc, le_rfl, hW⟩
  | j + 1 => ⟨trivial, swTw_wf k j, GxCl.small h1, le_rfl, gg_one_lt_of_SC ldOm2_SC⟩

omit h1 in
/-- **The tower terms are own under every evaluation** (all coefficients are `1`). -/
theorem swTw_own {b X0 : Ordinal.{0}} (k : ℕ) : ∀ j (e : Ordinal.{0} → Ordinal.{0}), SwOwn S b X0 e (swTw k j)
  | 0, _ => by
    cases k with
    | zero => exact ⟨⟨trivial, ⟨trivial, trivial, sgLimC_one⟩, sgLimC_one⟩, trivial, sgLimC_one⟩
    | succ k => exact ⟨trivial, trivial, sgLimC_one⟩
  | j + 1, _ => ⟨trivial, swTw_own k j _, sgLimC_one⟩

end TwT

/-! ## Bounds of contexts -/

section Bd

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

theorem swE_lt_G3 : ∀ K : SwC, SwWFC S l K → ∀ y yh, y < S.psi 0 (Om (1 + 1 + 1)) → yh < S.psi 0 (Om (1 + 1)) →
    swE K y < S.psi 0 (Om (1 + 1 + 1)) ∧ swEh S l K yh < S.psi 0 (Om (1 + 1))
  | .hole, _, _, _, h1, h2 => ⟨h1, h2⟩
  | .pfx K Q, ⟨hK, hQ⟩, y, yh, h1, h2 => by
    obtain ⟨a1, a2⟩ := swV_lt_G3 hl hX Q hQ
    exact swE_lt_G3 K hK _ _ (rwG3_SC.isPrincipal a1 h1) (rwG_SC.isPrincipal a2 h2)
  | .lft K, hK, y, yh, h1, h2 =>
    swE_lt_G3 K hK _ _ (leWe_lt_SC rwG3_SC rwW_lt_G3 h1).1 (leOe_lt_SC rwG_SC rwO_lt_G h2).1

end Bd

end Googology.Trans.PoR.InaccPsi.R2.Sw
