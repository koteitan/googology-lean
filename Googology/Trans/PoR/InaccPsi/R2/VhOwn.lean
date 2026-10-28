import Googology.Trans.PoR.InaccPsi.R2.VhAgree
import Googology.Trans.PoR.InaccPsi.R2.UgOwn

/-!
# `T` maps codes of level `k + 2` to codes of level `k + 1`, one proof for every `k`

`T = Vb.vbT S λ`, `D = Vb.VbD S λ`, `UgC S K Q` (**the codes of level `K` over `Q`** with the atoms
`ψ_{Ω_{K+1}}(d)`, `d < ψ_{Ω_{K+1}}(d)`, module `Ug.UgCode`), `Θ = gxTh ρ_λ (ldAtR λ)`.

* `vhC_mulNat` (`UgC` is closed under `·n`), `vhC_SC` (**a strongly critical code `w ≥ Q` of level `K` is `Ω_K` or
  an atom `ψ_{Ω_{K+1}}(d)` with a code `d < ψ_{Ω_{K+1}}(d)`**), `vhNf_le` (**every argument of the value `ψ_κ(d)`,
  `d < ψ_κ(d)`, is `≤ d`**);
* `vhT_cnf` (**`T(ω^e·n + s) = ω^{T e}·n + T s` for every exponent**, `s < ω^e`, on `D`);
* `vhOwn` (**THE OWN PROPERTY OF `T` AT EVERY LEVEL**): for `k : ℕ`, `x ∈ D`, a strongly critical `T₀ < Ω₂` such that
  `x` is a level-`(k+2)` code over every strongly critical `Q ≥ T₀`, the image `T x` is a level-`(k+1)` code over
  every strongly critical `Q ≥ Θ(T₀)`.  No bound `Y₃`: every member of `D` (up to `Ω_ω`) is covered;
* `vhOwn2`, `vhOwnCL` (`Ug.ugOwn`, `Ug.ugOwnCL` for `T` on all of `D`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

theorem vhC_mulNat {K Q x : Ordinal.{0}} (hQ : 0 < Q) (hx : UgC S K Q x) : ∀ n : ℕ, UgC S K Q (x * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact UgC.zero hQ
  | n + 1 => by rw [Nat.cast_succ, mul_add_one]; exact UgC.add (vhC_mulNat hQ hx n) hx

/-- **A strongly critical code `w ≥ Q` of level `K` is `Ω_K` or an atom `ψ_{Ω_{K+1}}(d)`.** -/
theorem vhC_SC {K Q : Ordinal.{0}} : ∀ w, UgC S K Q w → SC w → Q ≤ w →
    w = Om K ∨ ∃ d, UgC S K Q d ∧ d < S.psi d (Om (K + 1)) ∧ w = S.psi d (Om (K + 1)) := by
  intro w hw
  induction hw with
  | small h => exact fun _ hQ => absurd h (not_lt.2 hQ)
  | om => exact fun _ _ => Or.inl rfl
  | @add x y _ _ ihx ihy =>
    intro hS hQ
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at hS hQ ⊢; exact ihx hS hQ
    have hy : y = x + y := by
      rcases (le_add_self : y ≤ x + y).lt_or_eq with h | h
      · exact absurd (hS.isPrincipal (lt_add_of_pos_right x (pos_iff_ne_zero.2 hy0)) h) (lt_irrefl _)
      · exact h
    rw [← hy] at hS hQ ⊢; exact ihy hS hQ
  | @phi x y _ _ ihx ihy =>
    intro hS hQ
    rcases (right_le_veblen x y).lt_or_eq with h | h
    · obtain ⟨e1, -⟩ := ugSC_veb hS rfl h
      have hS' : SC x := by rw [e1]; exact hS
      have hQ' : Q ≤ x := by rw [e1]; exact hQ
      rw [← e1]; exact ihx hS' hQ'
    · rw [← h] at hS hQ ⊢; exact ihy hS hQ
  | @psi d hd hdl _ => exact fun _ _ => Or.inr ⟨d, hd, hdl, rfl⟩

/-- **Every argument of the value `ψ_κ(d)`, `d < ψ_κ(d)`, is `≤ d` (and below its own value).** -/
theorem vhNf_le {κ d d' : Ordinal.{0}} (hκ : S.InR κ) (hd : d < S.psi d κ) (he : S.psi d' κ = S.psi d κ)
 : d' ≤ d ∧ d' < S.psi d' κ := by
  have hle : d' ≤ d := by
    by_contra hc
    push Not at hc
    have h := psi_lt_psi_of_mem (S := S) hκ hc (CSet.of_lt (hd.trans_eq he.symm))
    rw [he] at h; exact lt_irrefl _ h
  exact ⟨hle, hle.trans_lt (hd.trans_eq he.symm)⟩

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T(ω^e·n + s) = ω^{T e}·n + T s` for every exponent** (`s < ω^e`, `n ≥ 1`, `e, s ∈ D`). -/
theorem vhT_cnf {e s : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (he : VbD S l e) (hs : VbD S l s) (hse : s < ω ^ e) :
    vbT S l (ω ^ e * n + s) = ω ^ vbT S l e * n + vbT S l s := by
  obtain ⟨heE, heK⟩ := vbT_eq hl hX he
  obtain ⟨hsE, hsK⟩ := vbT_eq hl hX hs
  have hlt : vbT S l s < ω ^ vbT S l e :=
    (vbK_lt_iff hl hX hsE (vhE_opow heE)).2 (by rw [hsK, vhK_opow hl hX heE, heK]; exact hse)
  have hK : vbK S l (ω ^ vbT S l e * n + vbT S l s) = ω ^ e * n + s := by
    rw [vhK_cnf hl hX n hn1 heE hsE hlt, heK, hsK]
  rw [← hK]; exact vbT_K hl hX (vhE_add (vhE_mulNat (vhE_opow heE) n) hsE)

/-- **THE OWN PROPERTY OF `T` AT EVERY LEVEL**: level-`(k+2)` codes over every `Q ≥ T₀` go to level-`(k+1)` codes
over every `Q ≥ Θ(T₀)`. -/
theorem vhOwn (k : ℕ) : ∀ x, VbD S l x → ∀ T0, SC T0 → T0 < Om (1 + 1) →
    (∀ Q, SC Q → T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1 + 1) Q x) →
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1) Q (vbT S l x) := by
  have hK0 : ((k : Ordinal.{0}) + 1 + 1) ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx T0 hT0 hT2 hcl Q hQ hTQ
  rcases lt_or_ge x (Om (1 + 1)) with hx2 | hx2
  · -- a code `x < Ω₂`: `x < T₀`
    have hxK : x < Om ((k : Ordinal.{0}) + 1 + 1) :=
      hx2.trans_le (Om_le_Om.2 (by gcongr; exact le_add_self))
    have hxT : x < T0 := ugC_lt_om hT0 (hcl T0 hT0 le_rfl) hxK
    rw [vbT_code hl hX hx2 hx.1]
    exact UgC.small ((gxTh_lt ((ldHull_iff hl hX hx2).1 hx.1) hxT).trans_le hTQ)
  have hx0 : x ≠ 0 := (ldOm2_SC.1.trans_le hx2).ne'
  have hxE := vbD_E hl hX hx
  by_cases hε : ω ^ x = x
  swap
  · -- the Cantor normal form
    have hlog : log ω x < x := by
      refine lt_of_le_of_ne (log_le_self ω x) fun e => hε ?_
      refine le_antisymm ?_ (right_le_opow x one_lt_omega0)
      calc ω ^ x = ω ^ log ω x := by rw [e]
        _ ≤ x := opow_log_le_self ω hx0
    obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
    have hpos : (0 : Ordinal.{0}) < n := hn ▸ div_opow_log_pos ω hx0
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact lt_irrefl _ hpos)
    have hdm : x = ω ^ log ω x * n + x % ω ^ log ω x := by
      rw [← hn]; exact (Ordinal.div_add_mod x _).symm
    have hs : x % ω ^ log ω x < ω ^ log ω x := Ordinal.mod_lt x (opow_pos _ omega0_pos).ne'
    have hsx : x % ω ^ log ω x < x := hs.trans_le (opow_log_le_self ω hx0)
    obtain ⟨heD, -, -⟩ := vbD_log hx hxE
    obtain ⟨hsD, -, -⟩ := vbD_rem hx hxE
    have hecl : ∀ Q, SC Q → T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1 + 1) Q (log ω x) :=
      fun Q hQ hTQ => (ugCDec hQ hK0 x (hcl Q hQ hTQ)).2
    have hscl : ∀ Q, SC Q → T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1 + 1) Q (x % ω ^ log ω x) :=
      fun Q hQ hTQ => ugC_mod hQ hK0 _ (hcl Q hQ hTQ)
    rw [(congrArg (vbT S l) hdm).trans (vhT_cnf hl hX n hn1 heD hsD hs)]
    exact UgC.add (vhC_mulNat hQ.1 (UgC.opow hQ.1 (IH _ hlog heD T0 hT0 hT2 hecl Q hQ hTQ)) n)
      (IH _ hsx hsD T0 hT0 hT2 hscl Q hQ hTQ)
  by_cases hS : SC x
  · -- `Ω_{k+2}` or an atom `ψ_{Ω_{k+3}}(d)`
    rcases vhC_SC x (hcl T0 hT0 le_rfl) hS (hT2.le.trans hx2) with hΩ | ⟨d, -, hdl, hxd⟩
    · have h := vbT_Om hl hX (k := k + 1) (by omega)
      rw [Nat.cast_succ] at h
      rw [hΩ, h]; exact UgC.om
    have hb := psiS_bounds (S := S) d ((k : Ordinal.{0}) + 1 + 1)
    rw [← hxd] at hb
    have h1 : Om 1 < x := (Om_lt_Om.2 (lt_add_one 1)).trans_le hx2
    have hne : ¬ ∃ j : ℕ, x = Om (j : Ordinal.{0}) := fun ⟨j, hj⟩ => not_Om_of_between hb.1 hb.2 _ hj
    obtain ⟨j, hj, d', hd'E, hd'n, hxd', -⟩ := rxE_atom (vbZ hl hX).2.le hxE hS h1 hne
    have hd'D : VbD S l d' := vbD_atom hl hX (hxd' ▸ hx) hd'E hd'n hj
    have hj2 : (j : Ordinal.{0}) = (k : Ordinal.{0}) + 1 + 1 := by
      have hb' := psiS_bounds (S := S) d' (j : Ordinal.{0})
      rw [← hxd'] at hb'
      exact between_unique hb'.1 hb'.2 hb.1 hb.2
    have hκ : S.InR (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) := InR_Om_succ _
    rw [hj2] at hxd' hd'n
    obtain ⟨-, hd'l⟩ := vhNf_le hκ hdl (hxd'.symm.trans hxd)
    have hd'x : d' < x := hxd' ▸ hd'l
    have hdcl : ∀ Q, SC Q → T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1 + 1) Q d' := by
      intro Q hQ hTQ
      rcases lt_or_ge x Q with hxQ | hQx
      · exact UgC.small (hd'x.trans hxQ)
      rcases vhC_SC x (hcl Q hQ hTQ) hS hQx with hΩ | ⟨d2, -, hd2l, hxd2⟩
      · exact absurd hΩ (not_Om_of_between hb.1 hb.2 _)
      exact ugC_psiArg hd'l x (hcl Q hQ hTQ) hxd'
    have hA := vbT_atom hl hX (k := k + 1) (by omega) hd'D (by rw [Nat.cast_succ]; exact hd'n)
    rw [Nat.cast_succ] at hA
    have hTd := IH d' hd'x hd'D T0 hT0 hT2 hdcl Q hQ hTQ
    have hdK : d' < Om (((k + 1 : ℕ) : Ordinal.{0}) + 1 + 1) := by rw [Nat.cast_succ]; exact hd'x.trans hb.2
    have hTdK := vbT_lt_lev hl hX hd'D (k + 1) hdK
    rw [Nat.cast_succ] at hTdK
    rw [hxd', hA.1]
    exact UgC.psi hTd (lt_psi_of_mem (InR_Om_succ _) hA.2 hTdK)
  -- a node `x = φ(a, b)`
  have hv : veblen (invVeblen₁ x) (invVeblen₂ x) = x := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ x < x := by have := invVeblen₂_lt x; rwa [hε] at this
  have h0 : 0 < x := pos_iff_ne_zero.2 hx0
  have ha0 : 0 < invVeblen₁ x := by
    refine pos_iff_ne_zero.2 fun h => ?_
    rw [h, veblen_zero_apply] at hv
    have : invVeblen₂ x = x := (opow_right_inj one_lt_omega0).1 (hv.trans hε.symm)
    exact absurd this hb.ne
  have ha : invVeblen₁ x < x := by
    refine lt_of_le_of_ne (invVeblen₁_le x) fun e => ?_
    rw [e] at hv
    have hle : veblen x 0 ≤ x := (veblen_le_veblen_iff_right.2 zero_le).trans hv.le
    exact hS (Ru.ruSC_of_veblen h0 (le_antisymm hle (left_le_veblen x 0)))
  obtain ⟨haD, hbD, -⟩ := vbD_veb hx hxE hv hb
  have hacl : ∀ Q, SC Q → T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1 + 1) Q (invVeblen₁ x) :=
    fun Q hQ hTQ => ugC_lev _ (hcl Q hQ hTQ) _ _ hv.symm hb
  have hbcl : ∀ Q, SC Q → T0 ≤ Q → UgC S ((k : Ordinal.{0}) + 1 + 1) Q (invVeblen₂ x) :=
    fun Q hQ hTQ => ugC_arg hQ _ (hcl Q hQ hTQ) _ _ hv.symm hb
  rw [vbT_veb hl hX hx hv ha0.ne' hb hx2]
  exact UgC.phi (IH _ ha haD T0 hT0 hT2 hacl Q hQ hTQ) (IH _ hb hbD T0 hT0 hT2 hbcl Q hQ hTQ)

/-- **The own property at level 2 on all of `D`** (no bound `Y₃`): `Ug.ugOwn` with `T` in place of `ugTh`. -/
theorem vhOwn2 {x : Ordinal.{0}} (hx : VbD S l x) {T0 : Ordinal.{0}} (hT0 : SC T0) (hT2 : T0 < Om (1 + 1))
    (hcl : ∀ Q, SC Q → T0 ≤ Q → UgC S (1 + 1) Q x) :
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T0 ≤ Q → UgC S 1 Q (vbT S l x) := by
  have h := vhOwn hl hX 0 x hx T0 hT0 hT2 (by simpa using hcl)
  simpa using h

/-- **The own property from the closure condition with `ψ₃`-atoms, on all of `D`** (`Ug.ugOwnCL` past `Y₃`). -/
theorem vhOwnCL {E b X0 : Ordinal.{0}} (hE : VbD S l E) (h : UgCL S E b X0) :
    ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) ≤ Q →
      UgC S 1 Q (vbT S l E) :=
  vhOwn2 hl hX hE (SC_psi (InR_Om_succ 1) _) (psi_lt (InR_Om_succ 1) _) h


end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vh
