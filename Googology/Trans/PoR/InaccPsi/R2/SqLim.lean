import Googology.Trans.PoR.InaccPsi.R2.SqAt

/-!
# The `ω`-limit rule: a level statement at a limit of an `ω`-sequence of levels

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`.

The derivations `Sc.ScDer` reach limits only through shapes indexed by the codes `ζ < Ω₂` (`om`, `lim`).  A limit
exponent `E` that is the supremum of an `ω`-sequence of exponents `E_k` with level statements (the `EX`-type
sequence of a limit such as `ε_{Ω₂+1} = sup_k t_k`) is handled here once, for any level:

* `sqLevLim` (**THE ω-LIMIT RULE**: if `E` has own data (`Sc.ScOwP Ow E Ê`), `E, Ê` are below `ψ_{Ω₃}(0)`,
  `ψ_{Ω₂}(0)`, every `E_k < E` has the level statement and the own data for an own predicate `Ow_k` implied by
  `Ow`, `Ê_k < Ê`, the `W^{E_k}` are cofinal in `W^E` and the `Ω^{Ê_k}` are cofinal in `Ω^{Ê}`, then
  `Sc.ScLev Ow E Ê`: `Θ(T_{X₀ + W^E}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Ê}})` over every own offset at every base);
* `sqWe_cof` (`E_k` cofinal in a limit `E` gives `W^{E_k}` cofinal in `W^E`; the same for `Ω^·`, `sqOe_cof`);
* `sqLev_eps'` (**`Sq.sqLev_eps` as an instance** of the rule with the towers `t_k`, `t̂_k`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sn

variable {S : InaccSeq.{0}}

/-- `E_k` cofinal in a limit `E` gives `ω^{κ·E_k}` cofinal in `ω^{κ·E}`. -/
theorem sqK_cof {κ E : Ordinal.{0}} (hκ : 0 < κ) (hlim : IsSuccLimit E) {e : ℕ → Ordinal.{0}}
    (hcof : ∀ x, x < E → ∃ k, x < e k) {y : Ordinal.{0}} (hy : y < ω ^ (κ * E)) :
    ∃ k, y < ω ^ (κ * e k) := by
  have hnorm : IsNormal (fun x : Ordinal.{0} => ω ^ (κ * x)) :=
    (isNormal_opow one_lt_omega0).comp (isNormal_mul_right hκ)
  obtain ⟨x, hxE, hyx⟩ := (hnorm.lt_iff_exists_lt hlim).1 hy
  obtain ⟨k, hk⟩ := hcof x hxE
  exact ⟨k, hyx.trans (hnorm.strictMono hk)⟩

theorem sqWe_cof {E : Ordinal.{0}} (hlim : IsSuccLimit E) {e : ℕ → Ordinal.{0}}
    (hcof : ∀ x, x < E → ∃ k, x < e k) : ∀ y, y < leWe E → ∃ k, y < leWe (e k) :=
  fun _ hy => sqK_cof ldOm2_SC.1 hlim hcof hy

theorem sqOe_cof {E : Ordinal.{0}} (hlim : IsSuccLimit E) {e : ℕ → Ordinal.{0}}
    (hcof : ∀ x, x < E → ∃ k, x < e k) : ∀ y, y < leOe E → ∃ k, y < leOe (e k) :=
  fun _ hy => sqK_cof (Om_pos one_ne_zero) hlim hcof hy

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE ω-LIMIT RULE.** -/
theorem sqLevLim {Ow : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}} (hP : ScOwP S l Ow E Eh)
    (hEG : E < S.psi 0 (Om (1 + 1 + 1))) (hEhG : Eh < S.psi 0 (Om (1 + 1)))
    {e eh : ℕ → Ordinal.{0}} {Ow' : ℕ → Ordinal.{0} → Ordinal.{0} → Prop}
    (hPk : ∀ k, ScOwP S l (Ow' k) (e k) (eh k)) (hLk : ∀ k, ScLev S l (Ow' k) (e k) (eh k))
    (himp : ∀ k b X0, Ow b X0 → Ow' k b X0) (hek : ∀ k, e k < E) (hehk : ∀ k, eh k < Eh)
    (hcof : ∀ y, y < leWe E → ∃ k, y < leWe (e k)) (hcofh : ∀ z, z < leOe Eh → ∃ k, z < leOe (eh k)) :
    ScLev S l Ow E Eh := by
  intro b X0 Xh0 hoff hd hG3 hG hOw
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 := sqTh_one (S := S) hl hX
  have hG3S := rwG3_SC (S := S)
  have hG1 := rwG_SC (S := S)
  -- the members `X₀ + W^{E_k}`
  have hm : ∀ k, RvSh S l b (X0 + leWe (e k) * 1) (Xh0 + leOe (eh k) * gxTh (upsilon l) (ldAtR S l) 1) ∧
      RvTop S l b (X0 + leWe (e k) * 1) (Xh0 + leOe (eh k) * gxTh (upsilon l) (ldAtR S l) 1) 0 := by
    intro k
    have hE1 : e k + 1 ≤ E := Order.add_one_le_of_lt (hek k)
    have hdE : leWe (e k + 1) ∣ X0 := (leWe_dvd hE1).trans hd
    have hG3' : X0 + leWe (e k + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hE1)) _) hG3
    have hG' : Xh0 + leOe (eh k + 1) + Om 1 < S.psi 0 (Om (1 + 1)) :=
      lt_of_le_of_lt (add_le_add_left ((add_le_add_iff_left Xh0).2
        (leOe_mono (Order.add_one_le_of_lt (hehk k)))) _) hG
    have h := scFam hl hX (hPk k) (hLk k) hoff hdE hG3' hG' (himp k b X0 hOw) 1
      (GxCl.small (gg_one_lt_of_SC hρSC)) ⟨0, show (1 : Ordinal.{0}) < Om 1 from sqOne_lt_Om1⟩
      (by rw [hΘ1]; exact sqOne_lt_Om1)
    refine rvOff_ne h fun h' => (leWe_pos (e k)).ne' ?_
    have := le_antisymm (h' ▸ le_add_self : leWe (e k) * 1 ≤ 0) zero_le
    rwa [mul_one] at this
  -- the shift `X₀ + W^E`
  have hX0 : X0 < S.psi 0 (Om (1 + 1 + 1)) := (le_self_add.trans le_self_add).trans_lt hG3
  have hXh0 : Xh0 < S.psi 0 (Om (1 + 1)) := (le_self_add.trans le_self_add).trans_lt hG
  have hW : leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    (leWe_lt_SC hG3S rwW_lt_G3 (hG3S.isSuccLimit.succ_lt hEG)).1
  have hO : leOe (Eh + 1) < S.psi 0 (Om (1 + 1)) :=
    (leOe_lt_SC hG1 rwO_lt_G (hG1.isSuccLimit.succ_lt hEhG)).1
  have hs : RvSh S l b (X0 + leWe E) (Xh0 + leOe Eh) := by
    have h := scSh_m hl hX hoff (hP.dat b X0 hOw) (ζ := 1) (GxCl.small (gg_one_lt_of_SC hρSC))
      (gg_one_lt_of_SC ldOm2_SC) one_ne_zero (sqOne_lt_Om1.trans (psiS_bounds (S := S) _ 1).1)
      (by rw [hΘ1]; exact sqOne_lt_Om1) (hG3S.isPrincipal (hG3S.isPrincipal hX0 hW) rwW_lt_G3)
      (hG1.isPrincipal (hG1.isPrincipal hXh0 hO) rwO_lt_G)
    rwa [mul_one, hΘ1, mul_one] at h
  refine rvTopLimSh hl hX hs ?_ ?_
  · intro x _ hx
    obtain ⟨k, hk⟩ : ∃ k, x < X0 + leWe (e k) := by
      rcases lt_or_ge x X0 with h | h
      · exact ⟨0, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        obtain ⟨k, hk⟩ := hcof y ((add_lt_add_iff_left X0).1 hx)
        exact ⟨k, (add_lt_add_iff_left X0).2 hk⟩
    obtain ⟨hsk, htk⟩ := hm k
    refine ⟨_, _, ?_, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_le_add_iff_left X0).2 (leWe_mono (hek k).le)
    · rw [mul_one]; exact hk
    · rw [hΘ1, mul_one]; exact (add_lt_add_iff_left Xh0).2 (leOe_lt (hehk k))
  · intro z hz
    obtain ⟨k, hk⟩ : ∃ k, z < Xh0 + leOe (eh k) := by
      rcases lt_or_ge z Xh0 with h | h
      · exact ⟨0, h.trans_le le_self_add⟩
      · obtain ⟨y, rfl⟩ := exists_add_of_le h
        obtain ⟨k, hk⟩ := hcofh y ((add_lt_add_iff_left Xh0).1 hz)
        exact ⟨k, (add_lt_add_iff_left Xh0).2 hk⟩
    obtain ⟨hsk, htk⟩ := hm k
    refine ⟨_, _, ?_, ?_, hsk, htk⟩
    · rw [mul_one]; exact (add_lt_add_iff_left X0).2 (leWe_lt (hek k))
    · rw [hΘ1, mul_one]; exact hk

/-- **`Sq.sqLev_eps` is an instance of the ω-limit rule** (members `t_k`, own predicates `Sn.SnCL t_k`). -/
theorem sqLev_eps' :
    ScLev S l (fun _ _ => True) (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  refine sqLevLim hl hX sqOwP_eps snEps_lt_G3 sqEpsH_lt_G (e := sqTw (Om (1 + 1)))
    (eh := fun k => sgThH S l (sqTw (Om (1 + 1)) k)) (Ow' := fun k => SnCL S (sqTw (Om (1 + 1)) k))
    (fun k => snOwP hl hX (sqTwW_mem k) (sqOne_le_tw ldOm2_SC k) (sqTw_lt ldOm2_SC k))
    (fun k => snLev hl hX (sqTwW_mem k) (sqOne_le_tw ldOm2_SC k) (sqTw_lt ldOm2_SC k))
    (fun k b X0 _ Q hQ _ => sqTw_cl ldOm2_SC hQ k) (sqTw_lt ldOm2_SC)
    (fun k => by show sgThH S l _ < _; rw [sqThH_tw l h1ρ k]; exact sqTw_lt Ph.ph_SC_Om1 k) ?_ ?_
  · rw [sqEps_We]
    intro y hy
    obtain ⟨k, hk⟩ := sqTw_cof ldOm2_SC hy
    exact ⟨k, hk.trans (sqTw_lt_succ ldOm2_SC k)⟩
  · rw [sqEpsH_Oe]
    intro z hz
    obtain ⟨k, hk⟩ := sqTw_cof Ph.ph_SC_Om1 hz
    refine ⟨k, ?_⟩
    show z < leOe (sgThH S l _)
    rw [sqThH_tw l h1ρ k]
    exact hk.trans (sqTw_lt_succ Ph.ph_SC_Om1 k)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Sq
