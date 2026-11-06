import Googology.Trans.PoR.InaccPsi.R2.KzOnto

/-!
# Kz: THE LAWS OF THE IMAGE `T_K` BELOW A BOUND `K` (`Vb.VbLaw` past `Ω_ω`)

* `vbKK_veb`, `vbKK_cnf`; `vbTK_mono` (**`T_K` is strictly increasing on `D_K`**), `vbTK_le_iff`, `vbTK_inj`;
  `vbTK_code` (`T_K x = Θ x` for the codes), `vbTK_Om` (`T_K Ω_{k+1} = Ω_k`), `vbTK_OmW` (**`T_K Ω_ω = Ω_ω`**),
  `vbTK_atom` (**`T_K ψ_{k+2}(d) = ψ_{k+1}(T_K d)`**), `vbTK_veb`, `vbTK_opow`, `vbTK_cnf`, `vbTK_lt_lev`,
  `vbTK_ge_lev`, `vbTK_mem`, `vbTK_SC`, `vbTK_eps`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX hKB

/-- `κ_λ` on a Veblen value built from members. -/
theorem vbKK_veb {ya yb a b : Ordinal.{0}} (hyaE : RxEK S (vbW S l) K ya) (hybE : RxEK S (vbW S l) K yb)
    (hya : vbK S l ya = a) (hyb : vbK S l yb = b) (ha0 : a ≠ 0) (hb : b < veblen a b)
    (h2 : Om (1 + 1) ≤ veblen a b) :
    RxEK S (vbW S l) K (veblen ya yb) ∧ vbK S l (veblen ya yb) = veblen a b := by
  obtain ⟨hZ, -⟩ := vbZ hl hX
  have hya0 : ya ≠ 0 := fun h => by
    rw [h] at hya
    have e0 : vbK S l 0 = 0 := rxL_zero hZ
    rw [e0] at hya
    exact ha0 hya.symm
  have hab2 : Om (1 + 1) ≤ a ∨ Om (1 + 1) ≤ b := by
    by_contra hc
    push Not at hc
    exact absurd h2 (not_le.2 (ldOm2_SC.2 _ hc.1 _ hc.2))
  set y := veblen ya yb with hydef
  have hy1 : Om 1 ≤ y := by
    rcases hab2 with h | h
    · exact (vbLowK hl hX hKB hyaE hya h).trans (left_le_veblen ya yb)
    · exact (vbLowK hl hX hKB hybE hyb h).trans (right_le_veblen ya yb)
  have hyε : ω ^ y = y := gg_veblen_eps hya0
  have hyE : RxEK S (vbW S l) K y :=
    ⟨RxN.phi hyaE.1 hybE.1, CSet.phi_mem hyaE.2.1 hybE.2.1, hKB.sc.2 _ hyaE.2.2 _ hybE.2.2⟩
  refine ⟨hyE, ?_⟩
  obtain ⟨a', b', hv', hb', -, ha'E, -, hκy, -, -, -⟩ := kzLDecV hZ hKB hyE hy1 hyε
  rw [hydef] at hv'
  rcases veblen_eq_veblen_iff.1 hv' with ⟨e1, e2⟩ | ⟨-, e2⟩ | ⟨h3, e3⟩
  · show rxL S (upsilon l) (ldAtR S l) (vbW S l) y = _
    rw [hκy, e1, e2]
    show veblen (vbK S l ya) (vbK S l yb) = _
    rw [hya, hyb]
  · exact absurd hb' (by rw [e2, ← hydef]; exact lt_irrefl _)
  · exfalso
    have hyb' : yb = y := e3.symm.trans (hv'.trans hydef.symm)
    have hbκ : b = veblen (vbK S l a') (vbK S l b') := by
      rw [← hyb, hyb']; exact hκy
    have hlt : a < vbK S l a' := by rw [← hya]; exact vbKK_mono hl hX hKB hyaE ha'E h3
    have h4 := veblen_veblen_of_lt hlt (vbK S l b')
    rw [← hbκ] at h4
    rw [h4] at hb
    exact lt_irrefl _ hb

/-- `κ_λ` on a Cantor normal form built from members. -/
theorem vbKK_cnf {yl yr : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (hylE : RxEK S (vbW S l) K yl)
    (hyrE : RxEK S (vbW S l) K yr) (hyl1 : Om 1 ≤ yl) (hyrlt : yr < ω ^ yl) :
    RxEK S (vbW S l) K (ω ^ yl * n + yr) ∧
      vbK S l (ω ^ yl * n + yr) = ω ^ vbK S l yl * n + vbK S l yr := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hoW : ω ^ yl < K := by
    have := hKB.sc.2 0 hKB.sc.1 yl hylE.2.2; rwa [veblen_zero_apply] at this
  have hoC : ω ^ yl ∈ S.CSet K (S.psi K (Om (1 + 1))) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hylE.2.1; rwa [veblen_zero_apply] at this
  have hoE : RxEK S (vbW S l) K (ω ^ yl) := ⟨RxN.opow hylE.1, hoC, hoW⟩
  set y := ω ^ yl * n + yr with hydef
  have hyE : RxEK S (vbW S l) K y :=
    ⟨RxN.add (RxN.mul_nat hoE.1 n) hyrE.1, CSet.add_mem (ConjT.mul_nat_mem S hoC n) hyrE.2.1,
      hKB.sc.isPrincipal (vbMulNat_lt hKB.sc.isPrincipal hKB.sc.1 hoW n) hyrE.2.2⟩
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn1
  have hy1 : Om 1 ≤ y :=
    ((hyl1.trans (right_le_opow _ one_lt_omega0)).trans (Ordinal.le_mul_left _ (zero_lt_one.trans_le hn1'))).trans
      le_self_add
  refine ⟨hyE, ?_⟩
  obtain ⟨n', -, hdm', hκy, -⟩ := kzLDecK hZ hZ1 hAt hKB hyE hy1
  have hlogy : log ω y = yl := by
    rw [hydef, log_opow_mul_add one_lt_omega0 hn0 hyrlt, log_eq_zero (natCast_lt_omega0 n), add_zero]
  have hmody : y % ω ^ yl = yr := by
    rw [hydef, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyrlt]
  have hyl0 : ω ^ yl ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hnn : (n' : Ordinal.{0}) = n := by
    rw [hlogy, hmody] at hdm'
    have e1 : y / ω ^ yl = n := by
      rw [hydef, Ordinal.mul_add_div _ hyl0, Ordinal.div_eq_zero_of_lt hyrlt, add_zero]
    have e2 : y / ω ^ yl = n' := by
      rw [hdm', Ordinal.mul_add_div _ hyl0, Ordinal.div_eq_zero_of_lt hyrlt, add_zero]
    rw [← e1, ← e2]
  show rxL S (upsilon l) (ldAtR S l) (vbW S l) y = _
  rw [hκy, hlogy, hmody, hnn]

/-- **`T` is strictly increasing on `VbD`.** -/
theorem vbTK_mono {x' x : Ordinal.{0}} (hx' : VbDK S l K x') (hx : VbDK S l K x) (h : x' < x) :
    vbTK S l K x' < vbTK S l K x :=
  vbTK_lt hl hX hKB (vbOntoK hl hX hKB x' hx') (vbOntoK hl hX hKB x hx) h

theorem vbTK_le_iff {x' x : Ordinal.{0}} (hx' : VbDK S l K x') (hx : VbDK S l K x) :
    x' ≤ x ↔ vbTK S l K x' ≤ vbTK S l K x := by
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (vbTK_mono hl hX hKB hx' hx h).le
    · rw [h]
  · intro h
    by_contra hc
    exact absurd h (not_le.2 (vbTK_mono hl hX hKB hx hx' (not_le.1 hc)))

theorem vbTK_inj {x' x : Ordinal.{0}} (hx' : VbDK S l K x') (hx : VbDK S l K x) (e : vbTK S l K x' = vbTK S l K x) :
    x' = x :=
  le_antisymm ((vbTK_le_iff hl hX hKB hx' hx).2 e.le) ((vbTK_le_iff hl hX hKB hx hx').2 e.ge)

/-- **`T x = Θ x` for the codes `x < Ω₂` of `H_λ`.** -/
theorem vbTK_code {x : Ordinal.{0}} (hx2 : x < Om (1 + 1)) (hxH : x ∈ cdHull S l) :
    vbTK S l K x = gxTh (upsilon l) (ldAtR S l) x := by
  obtain ⟨hE, hK⟩ := vbCodeK hl hX hKB hx2 hxH
  have h := vbTK_K hl hX hKB hE
  rwa [hK] at h

/-- **`T Ω_{k+1} = Ω_k`** (`k ≥ 1`). -/
theorem vbTK_Om {k : ℕ} (hk : 1 ≤ k) : vbTK S l K (Om ((k : Ordinal.{0}) + 1)) = Om (k : Ordinal.{0}) := by
  have hE : RxEK S (vbW S l) K (Om (k : Ordinal.{0})) :=
    ⟨RxN.om (rxN_nat k), rxC_Om_nat _ _ k, (Om_lt_Om.2 (natCast_lt_omega0 k)).trans_le hKB.ge⟩
  have hK : vbK S l (Om (k : Ordinal.{0})) = Om ((k : Ordinal.{0}) + 1) := rxL_Om hk
  rw [← hK]; exact vbTK_K hl hX hKB hE


/-- **`T_K Ω_ω = Ω_ω`** (`Ω_ω < K`). -/
theorem vbTK_OmW (hWK : Om ω < K) : vbTK S l K (Om ω) = Om ω := by
  have hωN : RxN S (vbW S l) ω := by
    have := RxN.phi (RxN.zero (S := S) (T := vbW S l)) (RxN.succ (RxN.zero (S := S) (T := vbW S l)))
    rwa [veblen_zero_apply, zero_add, opow_one] at this
  have hE : RxEK S (vbW S l) K (Om ω) := ⟨RxN.om hωN, ConjT.OmW_mem S _ _, hWK⟩
  have h := vbTK_K hl hX hKB hE
  rwa [show vbK S l (Om ω) = Om ω from kzL_OmW] at h

/-- **THE ATOM LAW AT EVERY LEVEL**: `T ψ_{k+2}(d) = ψ_{k+1}(T d)`, `T d` normal for `ψ_{k+1}` (`k ≥ 1`). -/
theorem vbTK_atom {d : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hd : VbDK S l K d)
    (hdn : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1)))) :
    vbTK S l K (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1))) = S.psi (vbTK S l K d) (Om ((k : Ordinal.{0}) + 1)) ∧
      vbTK S l K d ∈ S.CSet (vbTK S l K d) (S.psi (vbTK S l K d) (Om ((k : Ordinal.{0}) + 1))) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hd
  have hn := kzBack hZ hZ1 (ldAt_GxAt _ _) hKB hk hE hK hdn
  refine ⟨?_, hn⟩
  have hK2 : vbK S l (S.psi (vbTK S l K d) (Om ((k : Ordinal.{0}) + 1))) =
      S.psi d (Om ((k : Ordinal.{0}) + 1 + 1)) := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [(kzL_psiE hKB hk hE hn).1]
    show S.psi (vbK S l (vbTK S l K d)) _ = _
    rw [hK]
  rw [← hK2]; exact vbTK_K hl hX hKB (kzE_psi hKB hk hE hn)

/-- **THE `φ` LAW**: `T φ(a, b) = φ(T a, T b)` at a Veblen normal form `x = φ(a, b) ≥ Ω₂`, `b < x`. -/
theorem vbTK_veb {x a b : Ordinal.{0}} (hx : VbDK S l K x) (hv : veblen a b = x) (ha0 : a ≠ 0) (hb : b < x)
    (h2 : Om (1 + 1) ≤ x) : vbTK S l K x = veblen (vbTK S l K a) (vbTK S l K b) := by
  obtain ⟨haD, hbD, -⟩ := vbDK_veb hx (vbDK_E hl hX hx) hv hb
  obtain ⟨haE, haK⟩ := vbTK_eq hl hX hKB haD
  obtain ⟨hbE, hbK⟩ := vbTK_eq hl hX hKB hbD
  obtain ⟨hyE, hyK⟩ := vbKK_veb hl hX hKB haE hbE haK hbK ha0 (hv ▸ hb) (hv ▸ h2)
  rw [← hv, ← hyK]; exact vbTK_K hl hX hKB hyE

/-- **`T ω^ℓ = ω^{T ℓ}`** for `ℓ ≥ Ω₂`. -/
theorem vbTK_opow {ℓ : Ordinal.{0}} (hℓ : VbDK S l K ℓ) (h2 : Om (1 + 1) ≤ ℓ) :
    vbTK S l K (ω ^ ℓ) = ω ^ vbTK S l K ℓ := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hℓ
  have h1 := vbLowK hl hX hKB hE hK h2
  have hoE : RxEK S (vbW S l) K (ω ^ vbTK S l K ℓ) := by
    have := (vbKK_cnf hl hX hKB 1 le_rfl hE (kzE_zero hKB) h1 (opow_pos _ omega0_pos)).1
    rwa [Nat.cast_one, mul_one, add_zero] at this
  have hK2 : vbK S l (ω ^ vbTK S l K ℓ) = ω ^ ℓ := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [kzL_opow (Z := upsilon l) (At := ldAtR S l) hZ hZ1 (ldAt_GxAt _ _) hKB hE hoE h1]
    show ω ^ vbK S l (vbTK S l K ℓ) = _
    rw [hK]
  rw [← hK2]; exact vbTK_K hl hX hKB hoE

/-- **THE CANTOR NORMAL FORM**: `T(ω^ℓ·n + r) = ω^{T ℓ}·n + T r` for `r < ω^ℓ`, `ℓ ≥ Ω₂`, `n ≥ 1`. -/
theorem vbTK_cnf {ℓ r : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (hℓ : VbDK S l K ℓ) (hr : VbDK S l K r)
    (h2 : Om (1 + 1) ≤ ℓ) (hrl : r < ω ^ ℓ) :
    vbTK S l K (ω ^ ℓ * n + r) = ω ^ vbTK S l K ℓ * n + vbTK S l K r := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hlE, hlK⟩ := vbTK_eq hl hX hKB hℓ
  obtain ⟨hrE, hrK⟩ := vbTK_eq hl hX hKB hr
  have h1 := vbLowK hl hX hKB hlE hlK h2
  have hoE : RxEK S (vbW S l) K (ω ^ vbTK S l K ℓ) := by
    have := (vbKK_cnf hl hX hKB 1 le_rfl hlE (kzE_zero hKB) h1 (opow_pos _ omega0_pos)).1
    rwa [Nat.cast_one, mul_one, add_zero] at this
  have hK2 : vbK S l (ω ^ vbTK S l K ℓ) = ω ^ ℓ := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [kzL_opow (Z := upsilon l) (At := ldAtR S l) hZ hZ1 (ldAt_GxAt _ _) hKB hlE hoE h1]
    show ω ^ vbK S l (vbTK S l K ℓ) = _
    rw [hlK]
  have hrlt : vbTK S l K r < ω ^ vbTK S l K ℓ := by
    rw [vbKK_lt_iff hl hX hKB hrE hoE, hrK, hK2]; exact hrl
  obtain ⟨hyE, hyK⟩ := vbKK_cnf hl hX hKB n hn1 hlE hrE h1 hrlt
  rw [hlK, hrK] at hyK
  rw [← hyK]; exact vbTK_K hl hX hKB hyE

/-- **The levels, from above**: `x < Ω_{k+2} ⇒ T x < Ω_{k+1}`. -/
theorem vbTK_lt_lev {x : Ordinal.{0}} (hx : VbDK S l K x) (k : ℕ) (h : x < Om ((k : Ordinal.{0}) + 1 + 1)) :
    vbTK S l K x < Om ((k : Ordinal.{0}) + 1) := by
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hx
  by_contra hc
  push Not at hc
  have h' := kzL_ge_lev (vbZ hl hX).1 (vbZ hl hX).2 (ldAt_GxAt _ _ : GxAt (ldAtR S l)) hKB _ hE (k + 1) (by omega) (by rw [Nat.cast_succ]; exact hc)
  rw [Nat.cast_succ] at h'
  exact absurd (h'.trans_eq hK) (not_le.2 h)

/-- **The levels, from below**: `Ω_{k+2} ≤ x ⇒ Ω_{k+1} ≤ T x`. -/
theorem vbTK_ge_lev {x : Ordinal.{0}} (hx : VbDK S l K x) (k : ℕ) (h : Om ((k : Ordinal.{0}) + 1 + 1) ≤ x) :
    Om ((k : Ordinal.{0}) + 1) ≤ vbTK S l K x := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hx
  by_contra hc
  push Not at hc
  have h' := kzL_lt_lev hZ hZ1 (ldAt_GxAt _ _ : GxAt (ldAtR S l)) hKB _ hE k hc
  exact absurd (hK.symm.trans_lt h') (not_lt.2 h)

/-- `T x ∈ Cl(Ω_ω, θ)` and `T x < Ω_ω`. -/
theorem vbTK_mem {x : Ordinal.{0}} (hx : VbDK S l K x) :
    vbTK S l K x ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧ vbTK S l K x < K :=
  (vbTK_eq hl hX hKB hx).1.2

/-- **Strongly critical members `≥ Ω₂` go to strongly critical values.** -/
theorem vbTK_SC {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) ≤ x) (hS : SC x) : SC (vbTK S l K x) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hx
  have h1 := vbLowK hl hX hKB hE hK h2
  by_contra hS'
  rcases eq_or_lt_of_le h1 with e | h1'
  · exact hS' (e ▸ Ph.ph_SC_Om1)
  by_cases hε : ω ^ vbTK S l K x = vbTK S l K x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb h1' hε hS'
    have hκ := kzL_veb (Z := upsilon l) (At := ldAtR S l) hE h1' hε hS'
    obtain ⟨haE, -⟩ := kzE_veb hE hv hb
    have hlt : vbK S l (invVeblen₁ (vbTK S l K x)) < x := (vbKK_mono hl hX hKB haE hE ha).trans_eq hK
    have hblt : vbK S l (invVeblen₂ (vbTK S l K x)) < x :=
      (vbKK_mono hl hX hKB (kzE_veb hE hv hb).2.1 hE hb).trans_eq hK
    have e : x = veblen (vbK S l (invVeblen₁ (vbTK S l K x))) (vbK S l (invVeblen₂ (vbTK S l K x))) :=
      hK.symm.trans hκ
    exact hS.not_veblen_lt hlt hblt e.symm
  · obtain ⟨n, hn1, -, hκ, hlE, hrE, hoE, hrlt, hopx, hℓ1, hor, -⟩ := kzLDecK hZ hZ1
      (ldAt_GxAt _ _ : GxAt (ldAtR S l)) hKB hE h1
    have hlz := hor.resolve_left hε
    have hκx : x = ω ^ vbK S l (log ω (vbTK S l K x)) * n + vbK S l (vbTK S l K x % ω ^ log ω (vbTK S l K x)) :=
      hK.symm.trans hκ
    have hll : vbK S l (log ω (vbTK S l K x)) < x := (vbKK_mono hl hX hKB hlE hE hlz).trans_eq hK
    have hP := hS.isPrincipal
    have hxε := gg_SC_eps hS
    -- `x` is an `ε`-number, so a Cantor normal form with exponent below `x` stays below `x`
    have hopx' : ω ^ vbK S l (log ω (vbTK S l K x)) < x := by
      have := (opow_lt_opow_iff_right one_lt_omega0).2 hll
      rwa [hxε] at this
    have hrx : vbK S l (vbTK S l K x % ω ^ log ω (vbTK S l K x)) < x :=
      (vbKK_mono hl hX hKB hrE hE (hrlt.trans_le hopx)).trans_eq hK
    have : ω ^ vbK S l (log ω (vbTK S l K x)) * n + vbK S l (vbTK S l K x % ω ^ log ω (vbTK S l K x)) < x :=
      hP (vbMulNat_lt hP hS.1 hopx' n) hrx
    rw [← hκx] at this
    exact lt_irrefl _ this

/-- **`ε`-numbers `≥ Ω₂` go to `ε`-numbers.** -/
theorem vbTK_eps {x : Ordinal.{0}} (hx : VbDK S l K x) (h2 : Om (1 + 1) ≤ x) (hε : ω ^ x = x) :
    ω ^ vbTK S l K x = vbTK S l K x := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbTK_eq hl hX hKB hx
  have h1 := vbLowK hl hX hKB hE hK h2
  by_contra hne
  have h1' : Om 1 < vbTK S l K x := lt_of_le_of_ne h1 fun e => hne (by rw [← e]; exact Om1_opow)
  obtain ⟨n, hn1, -, hκ, hlE, hrE, hoE, hrlt, hopx, hℓ1, hor, -⟩ := kzLDecK hZ hZ1
      (ldAt_GxAt _ _ : GxAt (ldAtR S l)) hKB hE h1
  have hlz := hor.resolve_left hne
  have hκx : x = ω ^ vbK S l (log ω (vbTK S l K x)) * n + vbK S l (vbTK S l K x % ω ^ log ω (vbTK S l K x)) :=
    hK.symm.trans hκ
  have hll : vbK S l (log ω (vbTK S l K x)) < x := (vbKK_mono hl hX hKB hlE hE hlz).trans_eq hK
  have hP : IsPrincipal (· + ·) x := by rw [← hε]; exact isPrincipal_add_omega0_opow _
  have hx0 : 0 < x := (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans_le h2
  have hopx' : ω ^ vbK S l (log ω (vbTK S l K x)) < x := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hll
    rwa [hε] at this
  have hrx : vbK S l (vbTK S l K x % ω ^ log ω (vbTK S l K x)) < x :=
    (vbKK_mono hl hX hKB hrE hE (hrlt.trans_le hopx)).trans_eq hK
  have : ω ^ vbK S l (log ω (vbTK S l K x)) * n + vbK S l (vbTK S l K x % ω ^ log ω (vbTK S l K x)) < x :=
    hP (vbMulNat_lt hP hx0 hopx' n) hrx
  rw [← hκx] at this
  exact lt_irrefl _ this

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Kz
