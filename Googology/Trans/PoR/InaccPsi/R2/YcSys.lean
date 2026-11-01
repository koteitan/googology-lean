import Googology.Trans.PoR.InaccPsi.R2.YcFront
import Googology.Trans.PoR.InaccPsi.R2.XuBr
import Googology.Trans.PoR.InaccPsi.R2.XuEnd

/-!
# YcSys: THE REPAIRED `skLaySys` REDUCED TO ONE FAMILY STATEMENT OVER `Γ(k)`; THE LEVEL SIDE AT `k = 1`

`Ws.wsSysAll` turns a code interface `Ws.WsC` (levels below `Γ(1)`), the facts of `G` as a base (`Ws.WsCG`) and a
classification (`Ws.WsCls`) into the systems `φ(ℓ, G+1)` (`Hg.HgVD`).  Its statement over `Γ(k)` is
`YcSysAll k` (repaired interfaces `Yc.YcC k`, `Yc.YcCG`, `Yc.YcVD k`); its instance `k = 0` IS `Ws.wsSysAll`
(`ycSysAll_zero`).  The repaired `skLaySys k` follows from `YcSysAll k` and the LEVEL SIDE `YcLevAll S k` (a code
interface over `Γ(k)` with a classification and a level `ℓ' ≥ ℓ` of gate below `K`, for every `ℓ < Γ(k)`)
(`ycLaySys_of`), and the level side at `k = 1` is a THEOREM: every `WsC` is a code interface over `Γ(1)` (`ycC1`,
with the outer low field `ycZo 1` of `Γ(1)`), the (A3) interfaces `Xu.xuCn (n+1)` with their classifications
`Xu.xuClsN` and the levels `t_n` of gate `1` cover every `ℓ < Γ(1)` (`ycLevAll1`).  So

  **the repaired `skLaySys 1` ⇐ `YcSysAll 1`** (`ycLaySys1_of`), the family over the raw datum `Γ(1)` alone.

* `ycZo k` (**the outer low field of `Γ(k)`**: the next fixed point of `φ(Γ_{x+1+k}, ·)` above `Γ_{x+1+k}`),
  `ycZo_fix`, `ycZo_lt` (`< Γ_{x+2+k}`), `ycZo_gt` (above every `hdNx a (Γ_{x+1+k})`, `1 ≤ a < Γ_{x+1+k}`);
* `YcLev`, `YcFs`, `YcSeq1`, `YcFs1`, `YcCls` (`Ws.WsC.Lev`, `Fs`, `Seq1`, `Fs1`, `Ws.WsCls` for `Yc.YcC k`);
* `YcSysAll k` (**THE FAMILY STATEMENT OVER `Γ(k)`**), `ycSysAll_zero` (**= `Ws.wsSysAll`**);
* `ycC1` (**every `Ws.WsC` is a `Yc.YcC 1`**), `ycCG1`, `ycCls1`; `YcLevAll S k`, `ycLevAll1` (**the level side at
  `k = 1`, no hypothesis**), `ycLaySys_of`, `ycLaySys1_of`, `ycLaySys0'` (the reduction at `k = 0`: non-vacuity).

No new axiom.  New definitions: `ycZo`, `YcLev`, `YcFs`, `YcSeq1`, `YcFs1`, `YcCls`, `YcSysAll`, `ycC1`, `YcLevAll`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gb
  Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Xx Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Gg

/-! ## The outer low field of `Γ(k)` -/

/-- **The outer low field of `Γ(k)`**: `hdNx (max ω Γ_{x+1+k} + 1) Γ_{x+1+k}` (the pattern of `Wn.wnZo`). -/
noncomputable def ycZo (k x : Ordinal.{0}) : Ordinal.{0} := hdNx (max ω (gq k x) + 1) (gq k x)

theorem ycZo_fix (k x : Ordinal.{0}) : veblen 2 (ycZo k x) = ycZo k x := by
  unfold ycZo
  refine hdNx_fix ?_ _
  calc (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2
  _ ≤ max ω (gq k x) := le_max_left _ _
  _ < max ω (gq k x) + 1 := lt_add_one _

theorem yc_k_eps {k : Ordinal.{0}} (hk : k + 1 < ε₀) : k < ε₀ := (lt_add_one k).trans hk

section Zo

variable {k x : Ordinal.{0}} (hk : k + 1 < ε₀) (hx : InE x) (hx1 : x < Om1)
include hk hx hx1

theorem yc_gq_max : max ω (gq k x) = gq k x := by
  obtain ⟨-, h2, -, -⟩ := xx_facts hx hx1 (yc_k_eps hk)
  exact max_eq_right ((omega0_lt_inE hx).trans h2).le

theorem yc_gq_lt_succ : gq k x < gq (k + 1) x := by
  obtain ⟨hT, h1, -⟩ := xxW_T hx hx1 hk
  exact gmq_lt hx hx1 hT h1 (lt_add_one k)

/-- **`Z_o(x) < Γ_{x+2+k}`.** -/
theorem ycZo_lt : ycZo k x < gq (k + 1) x := by
  unfold ycZo
  rw [yc_gq_max hk hx hx1, hdNx_succ]
  obtain ⟨hT, h1, -⟩ := xxW_T hx hx1 hk
  obtain ⟨-, -, -, hE⟩ := xx_facts hx hx1 hk
  have hlt := yc_gq_lt_succ hk hx hx1
  have hl : IsSuccLimit (gq (k + 1) x) := ev_isSuccLimit_of_inE hE
  have h1lt : gq k x + 1 < gq (k + 1) x := hl.add_one_lt hlt
  have hfix : veblen (gq k x + 1) (gq (k + 1) x) = gq (k + 1) x :=
    xk_fix hx hx1 hT h1 le_add_self h1lt
  have hj : veblen (gq k x) (veblen (gq k x + 1) (gq k x + 1)) = veblen (gq k x + 1) (gq k x + 1) :=
    veblen_veblen_of_lt (lt_add_one _) _
  refine (hcN_le hj ((lt_add_one _).trans_le (right_le_veblen _ _))).trans_lt ?_
  rw [← hfix]; exact (isNormal_veblen _).strictMono h1lt

/-- **`hdNx a (Γ_{x+1+k}) < Z_o(x)`** for every `1 ≤ a < Γ_{x+1+k}`. -/
theorem ycZo_gt {a : Ordinal.{0}} (h1 : 1 ≤ a) (ha : a < gq k x) : hdNx a (gq k x) < ycZo k x := by
  obtain ⟨hT, hk1, -⟩ := xxW_T hx hx1 (yc_k_eps hk)
  rw [hdNx_fixP (xk_fix hx hx1 hT hk1 h1 ha)]
  have haZ : a < max ω (gq k x) + 1 := by rw [yc_gq_max hk hx hx1]; exact ha.trans (lt_add_one _)
  have hfix : veblen a (ycZo k x) = ycZo k x := hdNx_fix haZ _
  have hE : InE (ycZo k x) := hdNx_E (by simp) _
  have hlt : gq k x + 1 < ycZo k x := (ev_isSuccLimit_of_inE hE).add_one_lt (hdNx_gt _ _)
  rw [← hfix]
  exact (isNormal_veblen a).strictMono hlt

end Zo

/-! ## Levels, sequences and the classification of a repaired code interface -/

variable {k : Ordinal.{0}}

/-- **A level** of `C : YcC k` (`Ws.WsC.Lev`). -/
def YcLev (C : YcC k) (ℓ : Ordinal.{0}) : Prop := Om1 ≤ ℓ ∧ Om1 ∣ ℓ ∧ ℓ < C.Bd

/-- An `ω`-sequence of levels for `ℓ` (`Ws.WsC.Fs`). -/
def YcFs (C : YcC k) (ℓ : Ordinal.{0}) : Prop :=
  ∃ ls : ℕ → Ordinal.{0}, (∀ k, Om1 ≤ ls k ∧ Om1 ∣ ls k) ∧ (∀ k, ls k < ls (k + 1)) ∧ (∀ k, ls k < ℓ) ∧
    (∀ t, t < ℓ → ∃ k, t + 1 < ls k) ∧ ∀ k, C.g (ls k) ≤ C.g ℓ

/-- An `Ω₁`-sequence below `a` (`Ws.WsC.Seq1`). -/
def YcSeq1 (C : YcC k) (a : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}) : Prop :=
  (∀ μ, μ < Om1 → 1 ≤ s μ ∧ s μ < a) ∧ (∀ μ' μ, μ' < μ → μ < Om1 → s μ' < s μ) ∧
    (∀ x, InE x → x < Om1 → C.g a < x → ∀ μ, μ < x → C.g (s μ) < x) ∧
    ∀ σ, InE σ → σ < Om1 → ∀ b, b < a → C.g b < σ → ∃ μ, μ < σ ∧ b < s μ

/-- An `Ω₁`-sequence of levels below `ℓ` (`Ws.WsC.Fs1`). -/
def YcFs1 (C : YcC k) (ℓ : Ordinal.{0}) (s : Ordinal.{0} → Ordinal.{0}) : Prop :=
  YcSeq1 C ℓ s ∧ ∀ μ, μ < Om1 → Om1 ≤ s μ ∧ Om1 ∣ s μ

/-- **The classification below `L`** (`Ws.WsCls`). -/
def YcCls (C : YcC k) (L : Ordinal.{0}) : Prop :=
  ∀ ℓ, YcLev C ℓ → ℓ < L → ℓ ≠ Om1 → (¬ ∃ ℓ', YcLev C ℓ' ∧ ℓ = ℓ' + Om1) → ¬ YcFs C ℓ → ∃ s, YcFs1 C ℓ s

/-- **THE FAMILY STATEMENT OVER `Γ(k)`** (`Ws.wsSysAll` over the raw datum `Γ(k)`): for every repaired code
interface over `Γ(k)` with the base facts of `Γ(k)` and a classification below `L`, a repaired system over `Γ(k)`
at every level `ℓ < L`, bound `φ(ℓ, Γ(k)+1)`, gate at most that of `ℓ`. -/
def YcSysAll (k : Ordinal.{0}) : Prop :=
  ∀ C : YcC k, YcCG C → ∀ L, YcCls C L → ∀ ℓ, YcLev C ℓ → ℓ < L →
    ∃ D : YcVD k, D.B = veblen ℓ (gcG k + 1) ∧ D.γ ≤ C.g ℓ

/-- **`k = 0` IS `Ws.wsSysAll`.** -/
theorem ycSysAll_zero : YcSysAll 0 := by
  intro C hG L hc ℓ hℓ hL
  let C' : Ws.WsC := (YcC.toXk0 C).toWs
  have hG' : Ws.WsCG C' := ⟨hG.Bd_le, fun hx hx1 hℓ' hg => by
      show C.R _ _ < _; rw [mg_gq0 hx hx1]; exact hG.R_lt hx hx1 hℓ' hg,
    fun hx hx1 h1 hℓ' hg => by show hdNx (C.R _ _) _ < C.Zo _; rw [mg_gq0 hx hx1]; exact hG.Zo_gt hx hx1 h1 hℓ' hg⟩
  have hc' : Ws.WsCls C' L := fun ℓ h1 h2 h3 h4 h5 => hc ℓ h1 h2 h3 h4 h5
  obtain ⟨V, hB, hγ⟩ := Ws.wsSysAll hG' hc' ℓ hℓ hL
  exact ⟨YcVD.ofHg V, hB, hγ⟩

/-! ## The level side at `k = 1` -/

theorem yc_one_one_eps : (1 : Ordinal.{0}) + 1 < ε₀ := by
  rw [show (1 : Ordinal.{0}) + 1 = ((2 : ℕ) : Ordinal.{0}) by norm_num]
  exact (natCast_lt_omega0 2).trans (omega0_lt_epsilon 0)

theorem yc_zero_one_eps : (0 : Ordinal.{0}) + 1 < ε₀ := by
  rw [zero_add]; exact one_lt_omega0.trans (omega0_lt_epsilon 0)

/-- **Every code `y` of a level datum's digit-gate window lies below `Γ(1)`**: `Ω₁·(Ω₁·(ℓ/Ω₁²)) + Ω₁² < Γ(1)`
for `ℓ < Γ(1)`. -/
theorem yc_win_lt {ℓ : Ordinal.{0}} (hℓ : ℓ < gcG 1) :
    Om 1 * (Om1 * (ℓ / (Om1 * Om1))) + Om 1 * Om 1 < gcG 1 := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have hO : Om 1 < gcG 1 := gcG_Om1_lt 1
  have h1 : Om 1 * (Om1 * (ℓ / (Om1 * Om1))) ≤ ℓ := by
    rw [← Br.Om1_eq, ← mul_assoc]; exact Ordinal.mul_div_le ℓ _
  have h2 : Om 1 * Om 1 < gcG 1 := by
    have hw : ω ^ Om (1 : Ordinal.{0}) = Om 1 := Bt.Om1_opow
    calc Om 1 * Om 1 = ω ^ (Om 1 + Om 1) := by rw [opow_add, hw]
    _ < ω ^ gcG 1 := (opow_lt_opow_iff_right one_lt_omega0).2 ((inE_indec hE).add_lt hO hO)
    _ = gcG 1 := hE
  exact (inE_indec hE).add_lt (h1.trans_lt hℓ) h2

/-- **EVERY `Ws.WsC` IS A REPAIRED CODE INTERFACE OVER `Γ(1)`** (bound `< Γ(1) < Γ(2)`, readings `< Γ_{x+2} <
Γ_{x+3}`, the digit gate with the atom `Γ(1)` reduced to the atom `G` by `Xx.xx_cl_restrict`, outer low field
`ycZo 1`). -/
noncomputable def ycC1 (C : Ws.WsC) : YcC 1 where
  Bd := C.Bd
  R := C.R
  g := C.g
  Zo := ycZo 1
  Om1_lt := C.Om1_lt
  Bd_lt1 := C.Bd_lt1.trans (gcG_lt (lt_add_one 1))
  add_lt := C.add_lt
  g_lt := C.g_lt
  R_Om1 := C.R_Om1
  g_Om1 := C.g_Om1
  succ_R := C.succ_R
  succ_g := C.succ_g
  succ_g_lt := C.succ_g_lt
  g_succ1 := C.g_succ1
  le_R := C.le_R
  R_lt := fun hx hx1 hℓ hg => (C.R_lt hx hx1 hℓ hg).trans (yc_gq_lt_succ yc_one_one_eps hx hx1)
  R_mono := C.R_mono
  R_cof := C.R_cof
  R_pi := C.R_pi
  g_cl := fun ℓ h1 h2 h3 Z y hZ hZ1 hy hℓy hyw => by
    have hyN : y < gcG 1 := hyw.trans (yc_win_lt (h3.trans C.Bd_lt1))
    have hAt : ∀ s ∈ XkAt 1, s ∈ XkAt 0 ∨ gcG 1 ≤ s := by
      rintro s ⟨k', hk', rfl⟩
      rcases lt_or_ge k' 1 with h | h
      · exact Or.inl ⟨k', Order.lt_one_iff.1 h ▸ le_rfl, rfl⟩
      · exact Or.inr (gcG_le h)
    have h0 := xx_cl_restrict hAt hy hyN
    rw [xkAt_zero] at h0
    exact C.g_cl ℓ h1 h2 h3 Z y hZ hZ1 h0 hℓy hyw
  L_mem := fun ℓ hℓ S a b ha hb => C.L_mem ℓ hℓ S a b (zero_lt_one.trans ha) hb
  Zo_fix := ycZo_fix 1
  Zo_G1 := fun _ hx hx1 => ycZo_lt yc_one_one_eps hx hx1

/-- **`Γ(1)` as a base for `ycC1 C`.** -/
theorem ycCG1 (C : Ws.WsC) : YcCG (ycC1 C) where
  Bd_le := C.Bd_lt1.le
  R_lt := fun hx hx1 hℓ hg => C.R_lt hx hx1 hℓ hg
  Zo_gt := fun hx hx1 h1 hℓ hg =>
    ycZo_gt yc_one_one_eps hx hx1 ((Ws.WsC.one_lt_inE hx).le.trans (C.le_R hx hx1 h1 hℓ hg))
      (C.R_lt hx hx1 hℓ hg)

/-- **The classification transfers to `ycC1 C`.** -/
theorem ycCls1 {C : Ws.WsC} {L : Ordinal.{0}} (h : Ws.WsCls C L) : YcCls (ycC1 C) L :=
  fun ℓ h1 h2 h3 h4 h5 => h ℓ h1 h2 h3 h4 h5

/-- **THE LEVEL SIDE over `Γ(k)`**: for every `ℓ < Γ(k)` a repaired code interface over `Γ(k)` with the base facts of
`Γ(k)`, a classification below `L`, and a level `ℓ' ≥ ℓ`, `ℓ' < L`, of gate below `K`. -/
def YcLevAll (S : InaccSeq.{0}) (k : Ordinal.{0}) : Prop :=
  ∀ ℓ, ℓ < gcG k → ∃ C : YcC k, YcCG C ∧ ∃ L, YcCls C L ∧
    ∃ ℓ', ℓ ≤ ℓ' ∧ YcLev C ℓ' ∧ ℓ' < L ∧ C.g ℓ' < Td.tdK S

/-- **THE REDUCTION**: the family statement and the level side over `Γ(k)` give the repaired `skLaySys k`. -/
theorem ycLaySys_of {S : InaccSeq.{0}} (hA : YcSysAll k) (hL : YcLevAll S k) : YcLaySys S k := fun ℓ hℓ => by
  obtain ⟨C, hCG, L, hc, ℓ', hle, hlev, hlt, hg⟩ := hL ℓ hℓ
  obtain ⟨D, hB, hγ⟩ := hA C hCG L hc ℓ' hlev hlt
  exact ⟨D, hB ▸ veblen_left_monotone _ hle, hγ.trans_lt hg⟩

theorem yc_one_lt_K (S : InaccSeq.{0}) : (1 : Ordinal.{0}) < Td.tdK S :=
  one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (Td.tdK_SC (S := S))))

/-- **THE LEVEL SIDE AT `k = 1` IS A THEOREM** (the (A3) interfaces `Xu.xuCn (n+1)`, the levels `t_n` of gate `1`). -/
theorem ycLevAll1 (S : InaccSeq.{0}) : YcLevAll S 1 := fun ℓ hℓ => by
  obtain ⟨n, hn⟩ := Xu.xu_A3_end.2.1 ℓ hℓ
  have hlev := Xu.xu_t_lev (Nat.lt_succ_self n)
  refine ⟨ycC1 (Xu.xuCn (n + 1)), ycCG1 _, Wj.wjT (n + 1), ycCls1 (Xu.xuClsN (n + 1)), Wj.wjT n, hn.le,
    hlev, hlev.2.2, ?_⟩
  show Xu.xuGg (Wj.wjT n) < Td.tdK S
  rw [Xu.xuGg_t n]; exact yc_one_lt_K S

/-- **THE REPAIRED `skLaySys 1` FROM THE FAMILY STATEMENT OVER `Γ(1)` ALONE.** -/
theorem ycLaySys1_of (S : InaccSeq.{0}) (hA : YcSysAll 1) : YcLaySys S 1 := ycLaySys_of hA (ycLevAll1 S)

end Googology.Trans.PoR.InaccPsi.R2.Yc
