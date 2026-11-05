import Googology.Trans.PoR.InaccPsi.R2.ZlReach

/-!
# The supply from any code of the hull: `υ_{μ+X} ≤ r(μ)` for every `X` read below `Ω₂`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`ρ = υ_μ`, `u' = υ_{μ+1}`, `θ = ψ_{Ω₂}(Ω_ω)`, `At = Ld.ldAt S (Ω_ω+1) ρ`, `Θ = gxTh ρ At`, `C = Vy.vyC S ρ`.

`Wu.wuPast` reads ONE code (`φ(1, θ+1)`).  Here the step is generic: **every** code `m₀` of the closure
`GxCl ρ At` below `Ω₂` reads into the code set, `Θ(m₀) ≤ otp(C ∩ θ_{k+2})` (`zlPast`), so every limit `X ≤ Θ(m₀)`,
`X ≤ P(η_μ+2)` is supplied, `υ_{μ+X} ≤ r(μ)` (`zlSupCode`).  The code closure is closed under `+` and `φ` and `Θ` keeps
both, so from `Wc.WcRead0` (`u' ≤ Θ(θ)`) the whole `φ`-ladder `g₀ = u'+1`, `g_{n+1} = φ(g_n, 0)` (cofinal in the least
`Γ`-number above `u'`) is supplied (`zlSupG`).

* `zlPast` (**generic reading**: `m₀ ∈ GxCl ρ At`, `m₀ < Ω₂` ⇒ `Θ(m₀) ≤ otp(C ∩ θ_{k+2})`);
* `zlSupCode` (**generic supply**: `X` limit, `X ≤ P(η_μ+2)`, `X ≤ Θ(m₀)` ⇒ `υ_{μ+X} ≤ Θ_μ(G') ≤ r(μ)`);
* `zlG` (the ladder), `zlG_cl`, `zlG_lt`, `zlG_th`, `zlG_mono`, `zlG_E`, `zlG_lt_SC`;
* `zlSupG` (**the supply along the `φ`-ladder** from `WcRead0`), `zlSupG_le` (every `B ≤ g_{n+1}`), `zlSupG_wuX`
  (`ε_{u'+1} ≤ φ(1, u'+1) ≤ g₁`: the ladder contains `Wu.wuSup`).

No new axiom.  New definition: `zlG` (an ordinal term).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- The `φ`-ladder: `zlG x 0 = x + 1`, `zlG x (n+1) = φ(zlG x n, 0)`. -/
noncomputable def zlG (x : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => x + 1
  | n + 1 => veblen (zlG x n) 0

theorem zlG_one_le (x : Ordinal.{0}) : ∀ n, 1 ≤ zlG x n
  | 0 => le_add_self
  | n + 1 => (zlG_one_le x n).trans (by
      show zlG x n ≤ veblen (zlG x n) 0
      exact left_le_veblen _ _)

theorem zlG_mono {x y : Ordinal.{0}} (h : x ≤ y) : ∀ n, zlG x n ≤ zlG y n
  | 0 => add_le_add_left h 1
  | n + 1 => by
    show veblen (zlG x n) 0 ≤ veblen (zlG y n) 0
    exact veblen_left_monotone 0 (zlG_mono h n)

theorem zlG_lt_SC {s x : Ordinal.{0}} (hs : SC s) (hx : x < s) : ∀ n, zlG x n < s
  | 0 => hs.isPrincipal hx (Wc.wcSC_one hs)
  | n + 1 => hs.2 _ (zlG_lt_SC hs hx n) 0 (lt_trans zero_lt_one (Wc.wcSC_one hs))

theorem zlG_E (x : Ordinal.{0}) (n : ℕ) : InE (zlG x (n + 1)) := by
  show ω ^ veblen (zlG x n) 0 = veblen (zlG x n) 0
  have := veblen_veblen_of_lt (lt_of_lt_of_le zero_lt_one (zlG_one_le x n)) 0
  rwa [veblen_zero_apply] at this

theorem zlG_limit (x : Ordinal.{0}) (n : ℕ) : IsSuccLimit (zlG x (n + 1)) := by
  have hE := zlG_E x n
  have h := isSuccLimit_opow_left isSuccLimit_omega0 (InE.pos hE).ne'
  rwa [hE] at h

section Pos

variable {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ)
  (hc : cdCode S μ = Ls.lsG S (k + 1 + 1) + 1) (hω : upsilon μ < Nc.ncL S ω)
include hR hc hω

/-- **Generic reading**: every code `m₀ ∈ GxCl ρ At` below `Ω₂` reads into the code set. -/
theorem zlPast {m0 : Ordinal.{0}} (hm0 : GxCl (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) m0)
    (hm0lt : m0 < Om (1 + 1)) :
    gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) m0 ≤
      cdOtp (Vy.vyC S (upsilon μ)) (Lc.lcTh S (k + 1 + 1)) := by
  have hOm2 : Om (1 + 1 : Ordinal.{0}) < Lc.lcTh S (k + 1 + 1) := by
    have h := (psiS_bounds (S := S) (Om ω) ((k + 1 + 1 : ℕ) : Ordinal.{0})).1
    refine (Om_le_Om.2 ?_).trans_lt h
    have : ((1 + 1 : ℕ) : Ordinal.{0}) ≤ ((k + 1 + 1 : ℕ) : Ordinal.{0}) := by
      exact_mod_cast (show 1 + 1 ≤ k + 1 + 1 by omega)
    simp
  set Z := upsilon μ
  set At := Ld.ldAt S (Om ω + 1) Z
  refine Vy.vyOtp_of_map (Ru.ruInv Z At) (fun x hx => ?_) (fun x hx => ?_) (fun y x hyx hx => ?_)
  · exact Wc.wcCode_vyC (Ru.ruInv_spec hx).1
  · exact ((Ru.ruInv_spec hx).2.1.trans hm0lt).trans hOm2
  · exact Ru.ruInv_lt hx hyx

/-- **Generic supply**: a limit `X ≤ P(η_μ+2)` read below a code `m₀ ∈ GxCl ρ At`, `m₀ < Ω₂`, is supplied:
`υ_{μ+X} ≤ Θ_μ(G') ≤ r(μ)`. -/
theorem zlSupCode {m0 X : Ordinal.{0}} (hm0 : GxCl (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) m0)
    (hm0lt : m0 < Om (1 + 1)) (hXl : IsSuccLimit X) (hXP : X ≤ Nm.Pv S (cdEta S μ + 1 + 1))
    (hXm : X ≤ gxTh (upsilon μ) (Ld.ldAt S (Om ω + 1) (upsilon μ)) m0) :
    upsilon (μ + X) ≤ cdTheta S μ (Ls.lsG S (k + 1 + 1)) ∧ upsilon (μ + X) ≤ cdR S μ :=
  Vy.vySup (k + 1) hR hc hXl (Wu.wuGood hR hXP) (hXP.trans (Nm.Pv_lt_Om1 S _).le)
    (hXm.trans (zlPast hR hc hω hm0 hm0lt))

/-- `u' = υ_{μ+1} = P(η_μ + 1) < P(η_μ + 2)`, a strongly critical ordinal. -/
theorem zl_u1_lt_P : upsilon (μ + 1) < Nm.Pv S (cdEta S μ + 1 + 1) := by
  obtain ⟨hg, -, -⟩ := Ra.raName hR
  set η := cdEta S μ with hηdef
  have hE : ∀ e, 1 < Nm.Pv S e := fun e => So.soOne_lt_E (Sl.slPv_E (S := S) e)
  have hg1 : Bt.Good S (η + 1) := Rz.rz_good_shift hg (hE _)
  have hu : upsilon (μ + 1) = Nm.Pv S (η + 1) := by
    rw [Wc.wcUps1 hR (k := k + 1) hc hω]
    show _ = S.psi (ConjT.Aη S (η + 1)) (Om 1)
    rw [← ConjT.A_succ]
  rw [hu]
  exact Nm.Pv_lt_succ hg1

omit hR hc hω in
theorem zlG_cl {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ1 : 1 < Z) {x : Ordinal.{0}} (hx : GxCl Z At x) :
    ∀ n, GxCl Z At (zlG x n)
  | 0 => GxCl.add hx (GxCl.small hZ1)
  | n + 1 => GxCl.phi (zlG_cl hZ1 hx n) (GxCl.small (lt_trans zero_lt_one hZ1))

omit hR hc hω in
theorem zlG_th {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : SC Z) (hAt : GxAt At) {x : Ordinal.{0}}
    (hx : GxCl Z At x) : ∀ n, gxTh Z At (zlG x n) = zlG (gxTh Z At x) n
  | 0 => by
    show gxTh Z At (x + 1) = gxTh Z At x + 1
    rw [gxTh_add hZ hAt hx, gxTh_small (Wc.wcSC_one hZ).le]
  | n + 1 => by
    show gxTh Z At (veblen (zlG x n) 0) = veblen (zlG (gxTh Z At x) n) 0
    rw [gxTh_phi hZ hAt _ (zlG_cl (Wc.wcSC_one hZ) hx n) 0 (GxCl.small (lt_trans zero_lt_one (Wc.wcSC_one hZ))),
      zlG_th hZ hAt hx n, gxTh_zero]

/-- **The supply along the `φ`-ladder**: from `Wc.WcRead0` (`u' ≤ Θ(θ)`), `υ_{μ+g_{n+1}} ≤ r(μ)` for every `n`,
`g₀ = u'+1`, `g_{n+1} = φ(g_n, 0)`. -/
theorem zlSupG (hr : Wc.WcRead0 S μ) (n : ℕ) :
    upsilon (μ + zlG (upsilon (μ + 1)) (n + 1)) ≤ cdR S μ := by
  have hX := Wc.wcX_pv hR (k := k + 1) hc hω
  obtain ⟨hZ, -⟩ := Le.leRho hR.1 hX
  set Z := upsilon μ with hZdef
  set At := Ld.ldAt S (Om ω + 1) Z with hAtdef
  have hAt : GxAt At := Ld.ldAt_GxAt _ _
  have hθ : GxCl Z At (ConjT.th S) :=
    GxCl.atom ⟨Om ω, ConjT.OmW_mem S _ _, lt_add_one _, rfl⟩
  have hθ2 : ConjT.th S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  have hcl := zlG_cl (Wc.wcSC_one hZ) hθ (n + 1)
  have hlt := zlG_lt_SC Ld.ldOm2_SC hθ2 (n + 1)
  have hle : zlG (upsilon (μ + 1)) (n + 1) ≤ gxTh Z At (zlG (ConjT.th S) (n + 1)) := by
    rw [zlG_th hZ hAt hθ]; exact zlG_mono hr (n + 1)
  have hPs : SC (Nm.Pv S (cdEta S μ + 1 + 1)) := Nm.Pv_SC S _
  have hXP : zlG (upsilon (μ + 1)) (n + 1) ≤ Nm.Pv S (cdEta S μ + 1 + 1) :=
    (zlG_lt_SC hPs (zl_u1_lt_P hR hc hω) (n + 1)).le
  exact (zlSupCode hR hc hω hcl hlt (zlG_limit _ n) hXP hle).2

/-- Every `B ≤ g_{n+1}` is supplied. -/
theorem zlSupG_le (hr : Wc.WcRead0 S μ) (n : ℕ) {B : Ordinal.{0}} (hB : B ≤ zlG (upsilon (μ + 1)) (n + 1)) :
    upsilon (μ + B) ≤ cdR S μ :=
  (upsilon_normal.strictMono.monotone (add_le_add_right hB μ)).trans (zlSupG hR hc hω hr n)

omit hR hc hω in
/-- The ladder contains the supply of `Wu.wuSup`: `φ(1, u+1) ≤ g₁ = φ(u+1, 0)` for `1 ≤ u`. -/
theorem zlSupG_wuX {u : Ordinal.{0}} (hu : 1 ≤ u) : Wu.wuX u ≤ zlG u 1 := by
  show veblen 1 (u + 1) ≤ veblen (u + 1) 0
  have h1 : (1 : Ordinal.{0}) < u + 1 := Order.lt_add_one_iff.2 hu
  have hfix := veblen_veblen_of_lt h1 0
  calc veblen 1 (u + 1) ≤ veblen 1 (veblen (u + 1) 0) :=
        veblen_le_veblen_iff_right.2 (left_le_veblen _ _)
    _ = veblen (u + 1) 0 := hfix

end Pos

end Googology.Trans.PoR.InaccPsi.R2.Zl
