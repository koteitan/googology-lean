import Googology.Trans.PoR.InaccPsi.R2.YcSys

/-!
# YcBase: THE RAW DATUM `Γ(k)` — THE `G`-SPECIFIC FACTS OF THE FAMILY, PROVED OVER `Γ(k)`

The generic family (`Ws.wsStep_om1`, `Ws.wsFam`, `Ws.wsSysAll`) uses of its raw datum exactly the fields of
`Ws.WsGood`; at the datum `G` they are proved by `Ws.wsGood_G` from facts about `G`.  The facts that are specific
to `G` are: `G ≤ F` and `hdNx ℓ F < Γ(1)` (bounds), `F ∈ Cl(a, b)` and the hull membership of `hdNx μ F`,
`hdNx (μ + Ω₁) F` (asked for every `0 < a`), the atom set `{G}` of the digit gate (`F_code`, `F_cl`, `S_cl`), the
reading `Γ_{x+1}` of `F` as a fixed point of `φ(R μ x, ·)` below the outer low field (`rd`), Lemma EXACT for
`hdNx (R μ ρ) Γ_{ρ+1}` (`S_pi`) and for `Γ_{ρ+1}` (`Fr_pi`), and the outer low field below `Γ_{x+2}` (`Zo_G1`).

Here they are stated with `Γ(k)` in place of `G` (`YcGood`: bounds `Γ(k) ≤ F`, `hdNx ℓ F < Γ(k+1)`, outer low field
below `Γ_{x+2+k}`, atoms `Xk.XkAt k`, and the hull fields asked for `k < a`: by `Yc.ycG_notMem` they FAIL at
`0 < a ≤ k`) and PROVED for the datum `Γ(k)` (`ycGood_base`):

* `yc_low`, `yc_glA_fix` (**`ϑˣ(Ω₁·α + P) = φ(α, P + 1)` at a fixed point `P < Γ_{x+1+W}` of `φ(α, ·)`**, every
  `W < ε₀`; `Hc.hc_glA_fixG` is `W = 1`), `yc_glA_gq` (**`ϑˣ(Ω₁·q + Γ_{x+1+k}) = hdNx q Γ_{x+1+k}`**), `yc_S_pi`
  (**Lemma EXACT for `hdNx q(ρ) Γ_{ρ+1+k}`**, `Hj.hjG_S_pi` at `k = 0`), `yc_G_mem` (**`Γ(k) ∈ Cl(a, b)` for
  `k < a`**);
* `ycRk` (the datum `Γ(k)`: point `Γ(k)`, reading `Γ_{x+1+k}`, gate `0`, outer low field of `C`), `YcGood`
  (**`Ws.WsGood` over `Γ(k)`**), `ycGood_base` (**THE DATUM `Γ(k)` IS GOOD UP TO EVERY LEVEL** of every repaired
  code interface with the base facts of `Γ(k)`, `k + 1 < ε₀`), `ycGood_one` (`k = 1`, every `Ws.WsC`, through
  `Yc.ycC1`), `ycGood_one_wit` (non-vacuity: the level `t₀` of `Xu.xuCn 1`).

No new axiom.  New definitions: `ycRk`, `YcGood`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Mx

/-! ## `ϑˣ(Ω₁·α + P)` at a fixed point below `Γ_{x+1+W}` -/

section Fix

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) {W : Ordinal.{0}} (hW : W < ε₀)
include hx hx1 hW

/-- `ϑˣ(Ω₁·α + σ) < P` for every `σ < P` (`P ∈ (x, Γ_{x+1+W})` a fixed point of `φ(α, ·)`, `α < P`). -/
theorem yc_low {α P : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq W x) (hP : veblen α P = P) (hαP : α < P)
    (hxP : x < P) (hPq : P < gq W x) : ∀ σ, σ < P → glA α σ x < P := by
  obtain ⟨hαT, hαΩ⟩ := xx_T hx hx1 hW hαq
  have hP2 : LuP α P := ⟨P, hP⟩
  have hP3 : LuP (α + 1) P := hc_LuP_of_fix hP
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  obtain ⟨hσT, hσ1⟩ := xx_T hx hx1 hW (hσ.trans hPq)
  have hle : glA α σ x ≤ P := glA_min hx hx1 hα1 hαT hαΩ hσT hσ1 hP2 hxP hσ hαP
    (fun σ' h' => IH σ' h' (h'.trans hσ))
  exact lt_of_le_of_ne hle (fun e => glA_notP hx hx1 hα1 hαT hαΩ hσT hσ1 (by rw [e]; exact hP3))

/-- **`ϑˣ(Ω₁·α + P) = φ(α, P + 1)`** at a fixed point `P ∈ (x, Γ_{x+1+W})` of `φ(α, ·)` with `α < P`. -/
theorem yc_glA_fix {α P : Ordinal.{0}} (hα1 : 1 ≤ α) (hαq : α < gq W x) (hP : veblen α P = P) (hαP : α < P)
    (hxP : x < P) (hPq : P < gq W x) : glA α P x = veblen α (P + 1) := by
  obtain ⟨hαT, hαΩ⟩ := xx_T hx hx1 hW hαq
  obtain ⟨hPT, hP1⟩ := xx_T hx hx1 hW hPq
  have hlow := yc_low hx hx1 hW hα1 hαq hP hαP hxP hPq
  have hPS : P < veblen α (P + 1) := hc_lt_next hP
  refine le_antisymm ?_ ?_
  · exact glA_min hx hx1 hα1 hαT hαΩ hPT hP1 ⟨_, rfl⟩ (hxP.trans hPS) hPS (hαP.trans hPS)
      (fun σ hσ => (hlow σ hσ).trans hPS)
  · obtain ⟨-, -, -, -, -, hta⟩ := glA_facts hx hx1 hα1 hαT hαΩ hPT hP1
    obtain ⟨i, hi⟩ := glA_P hx hx1 hα1 hαT hαΩ hPT hP1
    rw [← hi] at hta ⊢
    conv_lhs at hta => rw [← hP]
    exact (isNormal_veblen α).monotone (Order.add_one_le_of_lt ((isNormal_veblen α).strictMono.lt_iff_lt.1 hta))

end Fix

section GQ

variable {k x : Ordinal.{0}} (hk : k + 1 < ε₀) (hx : InE x) (hx1 : x < Om1)
include hk hx hx1

/-- **`ϑˣ(Ω₁·q + Γ_{x+1+k}) = hdNx q Γ_{x+1+k}`** for `1 ≤ q < Γ_{x+1+k}`. -/
theorem yc_glA_gq {q : Ordinal.{0}} (h1 : 1 ≤ q) (hq : q < gq k x) : glA q (gq k x) x = hdNx q (gq k x) := by
  obtain ⟨hT, hk1, -⟩ := xxW_T hx hx1 (yc_k_eps hk)
  have hfix : veblen q (gq k x) = gq k x := xk_fix hx hx1 hT hk1 h1 hq
  have hlt := yc_gq_lt_succ hk hx hx1
  rw [hdNx_fixP hfix]
  exact yc_glA_fix hx hx1 hk h1 (hq.trans hlt) hfix hq (xx_facts hx hx1 (yc_k_eps hk)).2.1 hlt

end GQ

/-- **Lemma EXACT for `hdNx q(ρ) Γ_{ρ+1+k}`** for a level `q` with Lemma EXACT (`Hj.hjG_S_pi` at `k = 0`). -/
theorem yc_S_pi {k σ ρ qρ qσ : Ordinal.{0}} (hk : k + 1 < ε₀) (hB : Bases σ ρ)
    (hq : qρ ∈ TB ρ σ ∧ pi σ ρ qρ = qσ) (h1ρ : 1 ≤ qρ) (hqρ : qρ < gq k ρ) (h1σ : 1 ≤ qσ) (hqσ : qσ < gq k σ) :
    hdNx qρ (gq k ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx qρ (gq k ρ)) = hdNx qσ (gq k σ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hkσ : k < σ := (xxW_T hB.1 hσ1 (yc_k_eps hk)).2.2
  obtain ⟨g1, g2⟩ := gq_pi hB hkσ
  have hGρ := (xx_facts hB.2.1 hρ1 (yc_k_eps hk)).2.2.1
  have h := glA_pi hB hq.1 (hqρ.trans hGρ) g1 hGρ
  rw [hq.2, g2, yc_glA_gq hk hB.2.1 hρ1 h1ρ hqρ, yc_glA_gq hk hB.1 hσ1 h1σ hqσ] at h
  exact h

/-- **`Γ(k) ∈ Cl(a, b)` for `k < a`** (`k < ε₀`; at `0 < a ≤ k` it fails, `Yc.ycG_notMem`). -/
theorem yc_G_mem (S : InaccSeq.{0}) {k a b : Ordinal.{0}} (hk : k < ε₀) (hka : k < a) : gcG k ∈ S.CSet a b := by
  have hkG : k ≤ gcG 0 := (hk.trans_le gc_eps0_le_Om1).le.trans (gcG_Om1_lt 0).le
  rw [← gmS_psi S k hkG]
  exact CSet.psi_mem hka (InR_Om_succ 1) (ga_Om2_mem _ _) (gc_cst_mem a b k hk)

/-! ## The datum `Γ(k)` -/

variable {k : Ordinal.{0}}

/-- **`Γ(k)` as a raw datum** for `C : YcC k`: point `Γ(k)`, reading `Γ_{x+1+k}`, code gate `0`, outer low field
`C.Zo`. -/
noncomputable def ycRk (C : YcC k) : Wo.WoR := ⟨gcG k, gq k, 0, C.Zo⟩

/-- **`Ws.WsGood` OVER `Γ(k)`**: the fields of `Ws.WsGood` with `G`, `Γ(1)`, `Γ_{x+2}`, `{G}` replaced by `Γ(k)`,
`Γ(k+1)`, `Γ_{x+2+k}`, `Xk.XkAt k`, and the hull fields asked for `k < a`. -/
structure YcGood (C : YcC k) (r : Wo.WoR) (ℓ : Ordinal.{0}) : Prop where
  lev : YcLev C ℓ
  γ_lt : r.γ < Om1
  F_P : LuP ℓ r.F
  G_le : gcG k ≤ r.F
  S_lt1 : hdNx ℓ r.F < gcG (k + 1)
  F_mem : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, k < a → r.γ < b → r.F ∈ S.CSet a b
  S_mem : ∀ μ, YcLev C μ → μ ≤ ℓ → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, k < a → max r.γ (C.g μ) < b →
    hdNx μ r.F ∈ S.CSet a b
  S_memW : ∀ μ, YcLev C μ → μ + Om1 ≤ ℓ → ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, k < a →
    max r.γ (C.g μ) < b → hdNx (μ + Om1) r.F ∈ S.CSet a b
  F_code : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z (XkAt k) y → r.F ≤ y → y < hdNx ℓ r.F →
    GxCl Z (XkAt k) r.F
  F_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → ∀ y, GxCl Z (XkAt k) y → r.F ≤ y → y < hdNx ℓ r.F → r.γ < Z
  S_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z (XkAt k) (hdNx ℓ r.F) → r.γ < Z
  rd : ∀ μ, YcLev C μ → μ ≤ ℓ → ∀ x, InE x → x < Om1 → max r.γ (C.g μ) < x →
    LuP (C.R μ x) (r.Fr x) ∧ C.R μ x < r.Fr x ∧ hdNx (C.R μ x) (r.Fr x) < r.Zo x
  S_pi : ∀ μ, YcLev C μ → μ ≤ ℓ → ∀ σ ρ, Bases σ ρ → max r.γ (C.g μ) < σ →
    hdNx (C.R μ ρ) (r.Fr ρ) ∈ TB ρ σ ∧ pi σ ρ (hdNx (C.R μ ρ) (r.Fr ρ)) = hdNx (C.R μ σ) (r.Fr σ)
  Zo_fix : ∀ x, veblen 2 (r.Zo x) = r.Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → r.Zo x < gq (k + 1) x
  Fr_pi : ∀ {σ ρ}, Bases σ ρ → r.γ < σ → r.Fr ρ ∈ TB ρ σ ∧ pi σ ρ (r.Fr ρ) = r.Fr σ

theorem yc_one_le_R {C : YcC k} {μ x : Ordinal.{0}} (hμ : YcLev C μ) (hx : InE x) (hx1 : x < Om1)
    (hg : C.g μ < x) : (1 : Ordinal.{0}) ≤ C.R μ x :=
  (Ws.WsC.one_lt_inE hx).le.trans (C.le_R hx hx1 hμ.1 hμ.2.2 hg)

/-- **THE DATUM `Γ(k)` IS GOOD UP TO EVERY LEVEL** of a repaired code interface over `Γ(k)` with the base facts of
`Γ(k)` (`k + 1 < ε₀`; `Ws.wsGood_G` at `k = 0`). -/
theorem ycGood_base {C : YcC k} (hG : YcCG C) (hk : k + 1 < ε₀) {ℓ : Ordinal.{0}} (hℓ : YcLev C ℓ) :
    YcGood C (ycRk C) ℓ := by
  have hkε : k < ε₀ := yc_k_eps hk
  have hfixG : ∀ μ, μ < C.Bd → veblen μ (gcG k) = gcG k := fun μ hμ =>
    gn_veb_fix (gcG_SC k) (hμ.trans_le hG.Bd_le)
  have hGm : ∀ (S : InaccSeq.{0}) {a b : Ordinal.{0}}, k < a → gcG k ∈ S.CSet a b :=
    fun S _ _ hka => yc_G_mem S hkε hka
  have hgate : ∀ μ b, max (0 : Ordinal.{0}) (C.g μ) < b → C.g μ < b := fun μ b h => (max_lt_iff.1 h).2
  refine
    { lev := hℓ
      γ_lt := Gv.gv_Om1_pos
      F_P := ⟨gcG k, hfixG ℓ hℓ.2.2⟩
      G_le := le_rfl
      S_lt1 := ?_
      F_mem := fun S _ _ hka _ => hGm S hka
      S_mem := fun μ hμ _ S a b hka hb => ?_
      S_memW := fun μ hμ hle S a b hka hb => ?_
      F_code := fun _ _ _ _ _ _ _ => GxCl.atom ⟨k, le_rfl, rfl⟩
      F_cl := fun _ hZ _ _ _ _ _ => hZ.1
      S_cl := fun _ hZ _ _ => hZ.1
      rd := fun μ hμ _ x hx hx1 hg => ?_
      S_pi := fun μ hμ _ σ ρ hB hg => ?_
      Zo_fix := C.Zo_fix
      Zo_G1 := fun x hx hx1 => C.Zo_G1 x hx hx1
      Fr_pi := fun {σ ρ} hB _ => gq_pi hB (xxW_T hB.1 (hB.2.2.1.trans hB.2.2.2) hkε).2.2 }
  · have hG1 := gcG_SC (k + 1)
    have hE := Low.opow_eq_self_of_SC hG1
    have hfix1 : veblen ℓ (gcG (k + 1)) = gcG (k + 1) :=
      gn_veb_fix hG1 (hℓ.2.2.trans C.Bd_lt1)
    have h2 := (isNormal_veblen ℓ).strictMono ((ev_isSuccLimit_of_inE hE).add_one_lt (gcG_lt (lt_add_one k)))
    show hdNx ℓ (gcG k) < gcG (k + 1)
    rw [hdNx_fixP (hfixG ℓ hℓ.2.2)]; rwa [hfix1] at h2
  · show hdNx μ (gcG k) ∈ _
    rw [hdNx_fixP (hfixG μ hμ.2.2)]
    exact CSet.phi_mem (C.L_mem μ hμ.2.2 S a b hka (hgate μ b hb)) (CSet.succ_mem (hGm S hka))
  · show hdNx (μ + Om1) (gcG k) ∈ _
    have hμW : μ + Om1 < C.Bd := hle.trans_lt hℓ.2.2
    rw [hdNx_fixP (hfixG _ hμW)]
    have hO : Om1 ∈ S.CSet a b := by rw [Br.Om1_eq]; exact CSet.Om_mem (CSet.one_mem _ _)
    exact CSet.phi_mem (CSet.add_mem (C.L_mem μ hμ.2.2 S a b hka (hgate μ b hb)) hO) (CSet.succ_mem (hGm S hka))
  · have hgx : C.g μ < x := hgate μ x hg
    have hlt := hG.R_lt hx hx1 hμ.2.2 hgx
    obtain ⟨hT, hk1, -⟩ := xxW_T hx hx1 hkε
    exact ⟨⟨gq k x, xk_fix hx hx1 hT hk1 (yc_one_le_R hμ hx hx1 hgx) hlt⟩, hlt, hG.Zo_gt hx hx1 hμ.1 hμ.2.2 hgx⟩
  · have hgσ : C.g μ < σ := hgate μ σ hg
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hgρ : C.g μ < ρ := hgσ.trans hB.2.2.1
    exact yc_S_pi hk hB (C.R_pi hB hμ.2.2 hgσ) (yc_one_le_R hμ hB.2.1 hρ1 hgρ) (hG.R_lt hB.2.1 hρ1 hμ.2.2 hgρ)
      (yc_one_le_R hμ hB.1 hσ1 hgσ) (hG.R_lt hB.1 hσ1 hμ.2.2 hgσ)

/-- **`k = 1`: the datum `Γ(1)` is good up to every level of every `Ws.WsC`** (through `Yc.ycC1`). -/
theorem ycGood_one (C : Ws.WsC) {ℓ : Ordinal.{0}} (hℓ : C.Lev ℓ) : YcGood (ycC1 C) (ycRk (ycC1 C)) ℓ :=
  ycGood_base (ycCG1 C) yc_one_one_eps hℓ

/-- **Non-vacuity**: the datum `Γ(1)` is good up to the level `t₀` of the (A3) interface `Xu.xuCn 1`. -/
theorem ycGood_one_wit : YcGood (ycC1 (Xu.xuCn 1)) (ycRk (ycC1 (Xu.xuCn 1))) (Wj.wjT 0) :=
  ycGood_one _ (Xu.xu_t_lev Nat.zero_lt_one)

end Googology.Trans.PoR.InaccPsi.R2.Yc
