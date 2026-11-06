import Googology.Trans.PoR.InaccPsi.R2.KzMono

/-!
# Kz: THE DOMAIN `D_K` AND THE IMAGE `T_K` BELOW A BOUND `K` (`Vb.VbDef` past `Ω_ω`)

`H_λ = cdHull S λ`, `κ_λ = vbK S λ`, `W_λ = vbW S λ`, a bound `K` (`Kz.KzB`).

* `VbDK S λ K x` (**the domain below `K`**: `x ∈ H_λ`, `x ∈ Cl(K, ψ₂ K)`, `x < K`; `Vb.VbD` is `K = Ω_ω`);
* `vbTK S λ K x` (**THE IMAGE ONE LEVEL DOWN BELOW `K`**: the member `y` of `RxEK S W_λ K` with `κ_λ y = x`);
* `vbTK_spec`, `vbKK_mono`, `vbKK_inj`, `vbKK_le_iff`, `vbKK_lt_iff`, `vbTK_K`, `vbTK_lt`, `vbDK_E`, `vbDK_log`,
  `vbDK_rem`, `vbDK_veb`, `vbDK_atom`.

No new axiom.  New definitions: `VbDK`, `vbTK`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

/-- **The domain below `K`.** -/
def VbDK (S : InaccSeq.{0}) (l K x : Ordinal.{0}) : Prop :=
  x ∈ cdHull S l ∧ x ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧ x < K

open Classical in
/-- **THE IMAGE ONE LEVEL DOWN BELOW `K`.** -/
noncomputable def vbTK (S : InaccSeq.{0}) (l K x : Ordinal.{0}) : Ordinal.{0} :=
  if h : ∃ y, RxEK S (vbW S l) K y ∧ vbK S l y = x then Classical.choose h else 0

theorem vbTK_spec {l K x : Ordinal.{0}} (h : ∃ y, RxEK S (vbW S l) K y ∧ vbK S l y = x) :
    RxEK S (vbW S l) K (vbTK S l K x) ∧ vbK S l (vbTK S l K x) = x := by
  have e : vbTK S l K x = Classical.choose h := by unfold vbTK; rw [dif_pos h]
  rw [e]; exact Classical.choose_spec h

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hK : KzB S K)

include hl hX hK

theorem vbKK_mono {y' y : Ordinal.{0}} (hy' : RxEK S (vbW S l) K y') (hy : RxEK S (vbW S l) K y) (h : y' < y) :
    vbK S l y' < vbK S l y :=
  kzL_mono (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _) hK hy' hy h

theorem vbKK_inj {y' y : Ordinal.{0}} (hy' : RxEK S (vbW S l) K y') (hy : RxEK S (vbW S l) K y)
    (e : vbK S l y' = vbK S l y) : y' = y := by
  rcases lt_trichotomy y' y with h | h | h
  · exact absurd e (vbKK_mono hl hX hK hy' hy h).ne
  · exact h
  · exact absurd e.symm (vbKK_mono hl hX hK hy hy' h).ne

theorem vbKK_le_iff {y' y : Ordinal.{0}} (hy' : RxEK S (vbW S l) K y') (hy : RxEK S (vbW S l) K y) :
    y' ≤ y ↔ vbK S l y' ≤ vbK S l y := by
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (vbKK_mono hl hX hK hy' hy h).le
    · rw [h]
  · intro h
    by_contra hc
    exact absurd h (not_le.2 (vbKK_mono hl hX hK hy hy' (not_le.1 hc)))

theorem vbKK_lt_iff {y' y : Ordinal.{0}} (hy' : RxEK S (vbW S l) K y') (hy : RxEK S (vbW S l) K y) :
    y' < y ↔ vbK S l y' < vbK S l y := by
  rw [← not_le, ← not_le, vbKK_le_iff hl hX hK hy hy']

/-- **`T_K(κ_λ y) = y`.** -/
theorem vbTK_K {y : Ordinal.{0}} (hy : RxEK S (vbW S l) K y) : vbTK S l K (vbK S l y) = y := by
  obtain ⟨h1, h2⟩ := vbTK_spec (S := S) (l := l) (K := K) ⟨y, hy, rfl⟩
  exact vbKK_inj hl hX hK h1 hy h2

/-- **`T_K` is strictly increasing on the values of `κ_λ`.** -/
theorem vbTK_lt {x' x : Ordinal.{0}} (hx' : ∃ y, RxEK S (vbW S l) K y ∧ vbK S l y = x')
    (hx : ∃ y, RxEK S (vbW S l) K y ∧ vbK S l y = x) (h : x' < x) : vbTK S l K x' < vbTK S l K x := by
  obtain ⟨h1, e1⟩ := vbTK_spec hx'
  obtain ⟨h2, e2⟩ := vbTK_spec hx
  rw [vbKK_lt_iff hl hX hK h1 h2, e1, e2]; exact h

omit hK in
theorem vbDK_E {x : Ordinal.{0}} (hx : VbDK S l K x) : RxEK S (upsilon l) K x :=
  ⟨vbHullN hl hX hx.1, hx.2.1, hx.2.2⟩

omit hl hX hK in
theorem vbDK_log {x : Ordinal.{0}} (hx : VbDK S l K x) (hxE : RxEK S (upsilon l) K x) :
    VbDK S l K (log ω x) ∧ RxEK S (upsilon l) K (log ω x) ∧
      rxH S (upsilon l) (log ω x) ≤ rxH S (upsilon l) x := by
  obtain ⟨hE, hh⟩ := kzE_log hxE
  exact ⟨⟨(rxCDec x hx.1).2, hE.2.1, hE.2.2⟩, hE, hh⟩

omit hl hX hK in
theorem vbDK_rem {x : Ordinal.{0}} (hx : VbDK S l K x) (hxE : RxEK S (upsilon l) K x) :
    VbDK S l K (x % ω ^ log ω x) ∧ RxEK S (upsilon l) K (x % ω ^ log ω x) ∧
      rxH S (upsilon l) (x % ω ^ log ω x) ≤ rxH S (upsilon l) x := by
  obtain ⟨hE, hh⟩ := kzE_rem hxE
  exact ⟨⟨vbC_rem hx.1, hE.2.1, hE.2.2⟩, hE, hh⟩

omit hl hX hK in
theorem vbDK_veb {x a b : Ordinal.{0}} (hx : VbDK S l K x) (hxE : RxEK S (upsilon l) K x) (e : veblen a b = x)
    (hb : b < x) :
    VbDK S l K a ∧ VbDK S l K b ∧ RxEK S (upsilon l) K a ∧ RxEK S (upsilon l) K b ∧
      rxH S (upsilon l) a ≤ rxH S (upsilon l) x ∧ rxH S (upsilon l) b ≤ rxH S (upsilon l) x := by
  obtain ⟨haE, hbE, hha, hhb⟩ := kzE_veb hxE e hb
  obtain ⟨haC, hbC⟩ := rxCDecV hx.1 a b e hb
  exact ⟨⟨haC, haE.2.1, haE.2.2⟩, ⟨hbC, hbE.2.1, hbE.2.2⟩, haE, hbE, hha, hhb⟩

omit hK in
/-- The normal argument of an atom of the domain is in the domain. -/
theorem vbDK_atom {d : Ordinal.{0}} {k : ℕ} (hx : VbDK S l K (S.psi d (Om ((k : Ordinal.{0}) + 1))))
    (hdE : RxEK S (upsilon l) K d) (hdn : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1))))
    (hk : 1 ≤ k) : VbDK S l K d := by
  have hρ1 := (vbZ hl hX).2
  have hρx : upsilon l ≤ S.psi d (Om ((k : Ordinal.{0}) + 1)) :=
    (hρ1.trans_le ((rxOm1_le_nat hk).trans (psiS_bounds (S := S) d (k : Ordinal.{0})).1.le)).le
  have hρL : upsilon l ≤ S.Lam :=
    (hρ1.trans (lt_Lam_of_mem zero_le (CSet.Om_mem (CSet.one_mem (S := S) 0 0)))).le
  exact ⟨(arg_mem_of_psi_mem (InR_Om_succ _) hx.1 hρx hρL hdn).1, hdE.2.1, hdE.2.2⟩

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Kz
