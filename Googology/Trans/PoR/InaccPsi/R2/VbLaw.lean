import Googology.Trans.PoR.InaccPsi.R2.VbOnto

/-!
# The laws of the image one level down, at every level

`ρ_λ = υ_λ`, `H_λ = cdHull S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `κ_λ = vbK S λ`, `T = vbT S λ`, `VbD S λ` the domain
(members of
`H_λ ∩ Cl(Ω_ω, θ)` below `Ω_ω`), `ψ_k = ψ_{Ω_k}`, `φ = veblen`.  Every statement carries the restart hypotheses
`IsRestartIdx λ`, `ρ_λ < P(η_x)`.

* `vbK_veb`, `vbK_cnf` (`κ_λ` on a Veblen value and on a Cantor normal form built from members);
* `vbT_mono` (**`T` is strictly increasing on `VbD`**), `vbT_le_iff`, `vbT_inj`;
* `vbT_code` (**`T x = Θ x` for the codes `x < Ω₂`**), `vbT_Om` (**`T Ω_{k+1} = Ω_k`**, `k ≥ 1`);
* `vbT_atom` (**`T ψ_{k+2}(d) = ψ_{k+1}(T d)` with `T d` a normal argument for `ψ_{k+1}`**, for every normal
  argument `d ∈ VbD` of `ψ_{k+2}` and every `k ≥ 1`: one statement for all levels);
* `vbT_veb` (**the `φ` law** `T φ(a, b) = φ(T a, T b)` at every Veblen normal form `≥ Ω₂`), `vbT_opow`
  (`T ω^ℓ = ω^{T ℓ}` for `ℓ ≥ Ω₂`), `vbT_cnf` (**`T(ω^ℓ·n + r) = ω^{T ℓ}·n + T r`**, `r < ω^ℓ`, `ℓ ≥ Ω₂`);
* `vbT_lt_lev`, `vbT_ge_lev` (**the levels**: `x < Ω_{k+2} ⇒ T x < Ω_{k+1}`, `Ω_{k+2} ≤ x ⇒ Ω_{k+1} ≤ T x`),
  `vbT_mem` (`T x ∈ Cl(Ω_ω, θ)`, `T x < Ω_ω`), `vbT_SC` (strongly critical members `≥ Ω₂` go to strongly critical
  values), `vbT_eps`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Vb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `κ_λ` on a Veblen value built from members. -/
theorem vbK_veb {ya yb a b : Ordinal.{0}} (hyaE : RxE S (vbW S l) ya) (hybE : RxE S (vbW S l) yb)
    (hya : vbK S l ya = a) (hyb : vbK S l yb = b) (ha0 : a ≠ 0) (hb : b < veblen a b)
    (h2 : Om (1 + 1) ≤ veblen a b) :
    RxE S (vbW S l) (veblen ya yb) ∧ vbK S l (veblen ya yb) = veblen a b := by
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
    · exact (vbLow hl hX hyaE hya h).trans (left_le_veblen ya yb)
    · exact (vbLow hl hX hybE hyb h).trans (right_le_veblen ya yb)
  have hyε : ω ^ y = y := gg_veblen_eps hya0
  have hyE : RxE S (vbW S l) y :=
    ⟨RxN.phi hyaE.1 hybE.1, CSet.phi_mem hyaE.2.1 hybE.2.1, vbOmW_SC.2 _ hyaE.2.2 _ hybE.2.2⟩
  refine ⟨hyE, ?_⟩
  obtain ⟨a', b', hv', hb', -, ha'E, -, hκy, -, -, -⟩ := rxLDecV hZ hyE hy1 hyε
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
    have hlt : a < vbK S l a' := by rw [← hya]; exact vbK_mono hl hX hyaE ha'E h3
    have h4 := veblen_veblen_of_lt hlt (vbK S l b')
    rw [← hbκ] at h4
    rw [h4] at hb
    exact lt_irrefl _ hb

/-- `κ_λ` on a Cantor normal form built from members. -/
theorem vbK_cnf {yl yr : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (hylE : RxE S (vbW S l) yl)
    (hyrE : RxE S (vbW S l) yr) (hyl1 : Om 1 ≤ yl) (hyrlt : yr < ω ^ yl) :
    RxE S (vbW S l) (ω ^ yl * n + yr) ∧
      vbK S l (ω ^ yl * n + yr) = ω ^ vbK S l yl * n + vbK S l yr := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hn0 : (n : Ordinal.{0}) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hoW : ω ^ yl < Om ω := by
    have := vbOmW_SC.2 0 (Om_pos omega0_ne_zero) yl hylE.2.2; rwa [veblen_zero_apply] at this
  have hoC : ω ^ yl ∈ S.CSet (Om ω) (ConjT.th S) := by
    have := CSet.phi_mem (S := S) (CSet.zero_mem _ _) hylE.2.1; rwa [veblen_zero_apply] at this
  have hoE : RxE S (vbW S l) (ω ^ yl) := ⟨RxN.opow hylE.1, hoC, hoW⟩
  set y := ω ^ yl * n + yr with hydef
  have hyE : RxE S (vbW S l) y :=
    ⟨RxN.add (RxN.mul_nat hoE.1 n) hyrE.1, CSet.add_mem (ConjT.mul_nat_mem S hoC n) hyrE.2.1,
      vbOmW_SC.isPrincipal (vbMulNat_lt vbOmW_SC.isPrincipal vbOmW_SC.1 hoW n) hyrE.2.2⟩
  have hn1' : (1 : Ordinal.{0}) ≤ n := by exact_mod_cast hn1
  have hy1 : Om 1 ≤ y :=
    ((hyl1.trans (right_le_opow _ one_lt_omega0)).trans (Ordinal.le_mul_left _ (zero_lt_one.trans_le hn1'))).trans
      le_self_add
  refine ⟨hyE, ?_⟩
  obtain ⟨n', -, hdm', hκy, -⟩ := rxLDecK hZ hZ1 hAt hyE hy1
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
theorem vbT_mono {x' x : Ordinal.{0}} (hx' : VbD S l x') (hx : VbD S l x) (h : x' < x) :
    vbT S l x' < vbT S l x :=
  vbT_lt hl hX (vbOnto hl hX x' hx') (vbOnto hl hX x hx) h

theorem vbT_le_iff {x' x : Ordinal.{0}} (hx' : VbD S l x') (hx : VbD S l x) :
    x' ≤ x ↔ vbT S l x' ≤ vbT S l x := by
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · exact (vbT_mono hl hX hx' hx h).le
    · rw [h]
  · intro h
    by_contra hc
    exact absurd h (not_le.2 (vbT_mono hl hX hx hx' (not_le.1 hc)))

theorem vbT_inj {x' x : Ordinal.{0}} (hx' : VbD S l x') (hx : VbD S l x) (e : vbT S l x' = vbT S l x) :
    x' = x :=
  le_antisymm ((vbT_le_iff hl hX hx' hx).2 e.le) ((vbT_le_iff hl hX hx hx').2 e.ge)

/-- **`T x = Θ x` for the codes `x < Ω₂` of `H_λ`.** -/
theorem vbT_code {x : Ordinal.{0}} (hx2 : x < Om (1 + 1)) (hxH : x ∈ cdHull S l) :
    vbT S l x = gxTh (upsilon l) (ldAtR S l) x := by
  obtain ⟨hE, hK⟩ := vbCode_K hl hX hx2 hxH
  have h := vbT_K hl hX hE
  rwa [hK] at h

/-- **`T Ω_{k+1} = Ω_k`** (`k ≥ 1`). -/
theorem vbT_Om {k : ℕ} (hk : 1 ≤ k) : vbT S l (Om ((k : Ordinal.{0}) + 1)) = Om (k : Ordinal.{0}) := by
  have hE : RxE S (vbW S l) (Om (k : Ordinal.{0})) :=
    ⟨RxN.om (rxN_nat k), rxC_Om_nat _ _ k, Om_lt_Om.2 (natCast_lt_omega0 k)⟩
  have hK : vbK S l (Om (k : Ordinal.{0})) = Om ((k : Ordinal.{0}) + 1) := rxL_Om hk
  rw [← hK]; exact vbT_K hl hX hE

/-- **THE ATOM LAW AT EVERY LEVEL**: `T ψ_{k+2}(d) = ψ_{k+1}(T d)`, `T d` normal for `ψ_{k+1}` (`k ≥ 1`). -/
theorem vbT_atom {d : Ordinal.{0}} {k : ℕ} (hk : 1 ≤ k) (hd : VbD S l d)
    (hdn : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1)))) :
    vbT S l (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1))) = S.psi (vbT S l d) (Om ((k : Ordinal.{0}) + 1)) ∧
      vbT S l d ∈ S.CSet (vbT S l d) (S.psi (vbT S l d) (Om ((k : Ordinal.{0}) + 1))) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbT_eq hl hX hd
  have hn := vbBack hZ hZ1 (ldAt_GxAt _ _) hk hE hK hdn
  refine ⟨?_, hn⟩
  have hK2 : vbK S l (S.psi (vbT S l d) (Om ((k : Ordinal.{0}) + 1))) =
      S.psi d (Om ((k : Ordinal.{0}) + 1 + 1)) := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [(rxL_psiE hk hE hn).1]
    show S.psi (vbK S l (vbT S l d)) _ = _
    rw [hK]
  rw [← hK2]; exact vbT_K hl hX (rxE_psi hk hE hn)

/-- **THE `φ` LAW**: `T φ(a, b) = φ(T a, T b)` at a Veblen normal form `x = φ(a, b) ≥ Ω₂`, `b < x`. -/
theorem vbT_veb {x a b : Ordinal.{0}} (hx : VbD S l x) (hv : veblen a b = x) (ha0 : a ≠ 0) (hb : b < x)
    (h2 : Om (1 + 1) ≤ x) : vbT S l x = veblen (vbT S l a) (vbT S l b) := by
  obtain ⟨haD, hbD, -⟩ := vbD_veb hx (vbD_E hl hX hx) hv hb
  obtain ⟨haE, haK⟩ := vbT_eq hl hX haD
  obtain ⟨hbE, hbK⟩ := vbT_eq hl hX hbD
  obtain ⟨hyE, hyK⟩ := vbK_veb hl hX haE hbE haK hbK ha0 (hv ▸ hb) (hv ▸ h2)
  rw [← hv, ← hyK]; exact vbT_K hl hX hyE

/-- **`T ω^ℓ = ω^{T ℓ}`** for `ℓ ≥ Ω₂`. -/
theorem vbT_opow {ℓ : Ordinal.{0}} (hℓ : VbD S l ℓ) (h2 : Om (1 + 1) ≤ ℓ) :
    vbT S l (ω ^ ℓ) = ω ^ vbT S l ℓ := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbT_eq hl hX hℓ
  have h1 := vbLow hl hX hE hK h2
  have hoE : RxE S (vbW S l) (ω ^ vbT S l ℓ) := by
    have := (vbK_cnf hl hX 1 le_rfl hE rxE_zero h1 (opow_pos _ omega0_pos)).1
    rwa [Nat.cast_one, mul_one, add_zero] at this
  have hK2 : vbK S l (ω ^ vbT S l ℓ) = ω ^ ℓ := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [rxL_opow (Z := upsilon l) (At := ldAtR S l) hZ hZ1 (ldAt_GxAt _ _) hE hoE h1]
    show ω ^ vbK S l (vbT S l ℓ) = _
    rw [hK]
  rw [← hK2]; exact vbT_K hl hX hoE

/-- **THE CANTOR NORMAL FORM**: `T(ω^ℓ·n + r) = ω^{T ℓ}·n + T r` for `r < ω^ℓ`, `ℓ ≥ Ω₂`, `n ≥ 1`. -/
theorem vbT_cnf {ℓ r : Ordinal.{0}} (n : ℕ) (hn1 : 1 ≤ n) (hℓ : VbD S l ℓ) (hr : VbD S l r)
    (h2 : Om (1 + 1) ≤ ℓ) (hrl : r < ω ^ ℓ) :
    vbT S l (ω ^ ℓ * n + r) = ω ^ vbT S l ℓ * n + vbT S l r := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hlE, hlK⟩ := vbT_eq hl hX hℓ
  obtain ⟨hrE, hrK⟩ := vbT_eq hl hX hr
  have h1 := vbLow hl hX hlE hlK h2
  have hoE : RxE S (vbW S l) (ω ^ vbT S l ℓ) := by
    have := (vbK_cnf hl hX 1 le_rfl hlE rxE_zero h1 (opow_pos _ omega0_pos)).1
    rwa [Nat.cast_one, mul_one, add_zero] at this
  have hK2 : vbK S l (ω ^ vbT S l ℓ) = ω ^ ℓ := by
    show rxL S (upsilon l) (ldAtR S l) (vbW S l) _ = _
    rw [rxL_opow (Z := upsilon l) (At := ldAtR S l) hZ hZ1 (ldAt_GxAt _ _) hlE hoE h1]
    show ω ^ vbK S l (vbT S l ℓ) = _
    rw [hlK]
  have hrlt : vbT S l r < ω ^ vbT S l ℓ := by
    rw [vbK_lt_iff hl hX hrE hoE, hrK, hK2]; exact hrl
  obtain ⟨hyE, hyK⟩ := vbK_cnf hl hX n hn1 hlE hrE h1 hrlt
  rw [hlK, hrK] at hyK
  rw [← hyK]; exact vbT_K hl hX hyE

/-- **The levels, from above**: `x < Ω_{k+2} ⇒ T x < Ω_{k+1}`. -/
theorem vbT_lt_lev {x : Ordinal.{0}} (hx : VbD S l x) (k : ℕ) (h : x < Om ((k : Ordinal.{0}) + 1 + 1)) :
    vbT S l x < Om ((k : Ordinal.{0}) + 1) := by
  obtain ⟨hE, hK⟩ := vbT_eq hl hX hx
  by_contra hc
  push Not at hc
  have h' := rxL_ge_lev (Z := upsilon l) (At := ldAtR S l) _ hE (k + 1) (by omega) (by rw [Nat.cast_succ]; exact hc)
  rw [Nat.cast_succ] at h'
  exact absurd (h'.trans_eq hK) (not_le.2 h)

/-- **The levels, from below**: `Ω_{k+2} ≤ x ⇒ Ω_{k+1} ≤ T x`. -/
theorem vbT_ge_lev {x : Ordinal.{0}} (hx : VbD S l x) (k : ℕ) (h : Om ((k : Ordinal.{0}) + 1 + 1) ≤ x) :
    Om ((k : Ordinal.{0}) + 1) ≤ vbT S l x := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbT_eq hl hX hx
  by_contra hc
  push Not at hc
  have h' := rxL_lt_lev hZ hZ1 (ldAt_GxAt _ _ : GxAt (ldAtR S l)) _ hE k hc
  exact absurd (hK.symm.trans_lt h') (not_lt.2 h)

/-- `T x ∈ Cl(Ω_ω, θ)` and `T x < Ω_ω`. -/
theorem vbT_mem {x : Ordinal.{0}} (hx : VbD S l x) :
    vbT S l x ∈ S.CSet (Om ω) (ConjT.th S) ∧ vbT S l x < Om ω :=
  (vbT_eq hl hX hx).1.2

/-- **Strongly critical members `≥ Ω₂` go to strongly critical values.** -/
theorem vbT_SC {x : Ordinal.{0}} (hx : VbD S l x) (h2 : Om (1 + 1) ≤ x) (hS : SC x) : SC (vbT S l x) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbT_eq hl hX hx
  have h1 := vbLow hl hX hE hK h2
  by_contra hS'
  rcases eq_or_lt_of_le h1 with e | h1'
  · exact hS' (e ▸ Ph.ph_SC_Om1)
  by_cases hε : ω ^ vbT S l x = vbT S l x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb h1' hε hS'
    have hκ := rxL_veb (Z := upsilon l) (At := ldAtR S l) hE h1' hε hS'
    obtain ⟨haE, -⟩ := rxE_veb hE hv hb
    have hlt : vbK S l (invVeblen₁ (vbT S l x)) < x := (vbK_mono hl hX haE hE ha).trans_eq hK
    have hblt : vbK S l (invVeblen₂ (vbT S l x)) < x :=
      (vbK_mono hl hX (rxE_veb hE hv hb).2.1 hE hb).trans_eq hK
    have e : x = veblen (vbK S l (invVeblen₁ (vbT S l x))) (vbK S l (invVeblen₂ (vbT S l x))) :=
      hK.symm.trans hκ
    exact hS.not_veblen_lt hlt hblt e.symm
  · obtain ⟨n, hn1, -, hκ, hlE, hrE, hoE, hrlt, hopx, hℓ1, hor, -⟩ := rxLDecK hZ hZ1
      (ldAt_GxAt _ _ : GxAt (ldAtR S l)) hE h1
    have hlz := hor.resolve_left hε
    have hκx : x = ω ^ vbK S l (log ω (vbT S l x)) * n + vbK S l (vbT S l x % ω ^ log ω (vbT S l x)) :=
      hK.symm.trans hκ
    have hll : vbK S l (log ω (vbT S l x)) < x := (vbK_mono hl hX hlE hE hlz).trans_eq hK
    have hP := hS.isPrincipal
    have hxε := gg_SC_eps hS
    -- `x` is an `ε`-number, so a Cantor normal form with exponent below `x` stays below `x`
    have hopx' : ω ^ vbK S l (log ω (vbT S l x)) < x := by
      have := (opow_lt_opow_iff_right one_lt_omega0).2 hll
      rwa [hxε] at this
    have hrx : vbK S l (vbT S l x % ω ^ log ω (vbT S l x)) < x :=
      (vbK_mono hl hX hrE hE (hrlt.trans_le hopx)).trans_eq hK
    have : ω ^ vbK S l (log ω (vbT S l x)) * n + vbK S l (vbT S l x % ω ^ log ω (vbT S l x)) < x :=
      hP (vbMulNat_lt hP hS.1 hopx' n) hrx
    rw [← hκx] at this
    exact lt_irrefl _ this

/-- **`ε`-numbers `≥ Ω₂` go to `ε`-numbers.** -/
theorem vbT_eps {x : Ordinal.{0}} (hx : VbD S l x) (h2 : Om (1 + 1) ≤ x) (hε : ω ^ x = x) :
    ω ^ vbT S l x = vbT S l x := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  obtain ⟨hE, hK⟩ := vbT_eq hl hX hx
  have h1 := vbLow hl hX hE hK h2
  by_contra hne
  have h1' : Om 1 < vbT S l x := lt_of_le_of_ne h1 fun e => hne (by rw [← e]; exact Om1_opow)
  obtain ⟨n, hn1, -, hκ, hlE, hrE, hoE, hrlt, hopx, hℓ1, hor, -⟩ := rxLDecK hZ hZ1
      (ldAt_GxAt _ _ : GxAt (ldAtR S l)) hE h1
  have hlz := hor.resolve_left hne
  have hκx : x = ω ^ vbK S l (log ω (vbT S l x)) * n + vbK S l (vbT S l x % ω ^ log ω (vbT S l x)) :=
    hK.symm.trans hκ
  have hll : vbK S l (log ω (vbT S l x)) < x := (vbK_mono hl hX hlE hE hlz).trans_eq hK
  have hP : IsPrincipal (· + ·) x := by rw [← hε]; exact isPrincipal_add_omega0_opow _
  have hx0 : 0 < x := (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans_le h2
  have hopx' : ω ^ vbK S l (log ω (vbT S l x)) < x := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 hll
    rwa [hε] at this
  have hrx : vbK S l (vbT S l x % ω ^ log ω (vbT S l x)) < x :=
    (vbK_mono hl hX hrE hE (hrlt.trans_le hopx)).trans_eq hK
  have : ω ^ vbK S l (log ω (vbT S l x)) * n + vbK S l (vbT S l x % ω ^ log ω (vbT S l x)) < x :=
    hP (vbMulNat_lt hP hx0 hopx' n) hrx
  rw [← hκx] at this
  exact lt_irrefl _ this

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Vb
