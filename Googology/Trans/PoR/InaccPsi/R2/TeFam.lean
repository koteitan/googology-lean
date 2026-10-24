import Googology.Trans.PoR.InaccPsi.R2.TeNext

/-!
# The finite `ε`-tower above `Γ_{x+1}`: offset code systems with top `ε_{Γ_{x+1}+1+n}`, and their union

`eNG n x = ε_{Γ_{x+1}+1+n}` (`Gn.eNG`), `G₀ = Γ_{Ω₁+1}` (`Gc.gcG 0`).  Starting from `Tb.tbEc` (codes below `ε_{G₀+1}`,
top `ε_{Γ_{x+1}+1}`) the `ε`-step `Te.teNext` applies again and again:

* `te_ix_G0`, `te_evA_G0` (`ε_{G₀+c} = φ(1, G₀ + c)`), `teHyp_of` (**`TeHyp K` for every `K` with top `eNG n` and code
  bound `ε_{G₀+n+1}`**: Lemma EXACT for `eNG n`, `eNG (n+1)` is `Gn.eNG_pi`, the bounds are `Gn.eNG_lt1` and
  `θ_{k+1}` strongly critical);
* `teFam n` (**an offset code system with top `ε_{Γ_{x+1}+1+n}`** and code bound `ε_{G₀+n+1}`; `teFam 0 = Tb.tbEc`);
* `te_real_iSup` (**realizers up to `υ_{a+f(n)}` for every `n` give realizers up to `υ_{a+sup_n f(n)}`**, `υ` normal),
  `teW` (`teW x = sup_n ε_{Γ_{x+1}+1+n} = ε_{Γ_{x+1}+ω}`), `teW_le` (**`ε_{Γ_{x+1}+ω}` is at most every `υ`-point
  above `x`**), `teW_lt_b` (`υ_{a+ε_{Γ_{a+1}+ω}} < b` for every `υ`-fixed `ε`-number `b > a`);
* `teRealW_M`, `teRealW_L` (**`LrReal S a υ_{a+ε_{Γ_{a+1}+ω}}` at `m*` and every `L(n+1)`**, below `L(1)`, `L(n+2)`).

No new axiom.  New definitions: `teFam`, `teW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Te

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

/-! ## The hypotheses of the step along the tower -/

theorem te_ix_G0 : evIx (Gc.gcG 0) = Gc.gcG 0 := by
  have hfix : Ordinal.epsilon (Gc.gcG 0) = Gc.gcG 0 := Gn.gn_veb_fix (Gc.gcG_SC 0) Gn.gn_one_lt
  conv_lhs => rw [← hfix]
  exact evIx_epsilon _

/-- `ε_{G₀+c} = φ(1, G₀ + c)`. -/
theorem te_evA_G0 (c : Ordinal.{0}) : evA (Gc.gcG 0) c = veblen 1 (Gc.gcG 0 + c) := by
  rw [evA, te_ix_G0]

theorem te_nat_mem (S : InaccSeq.{0}) (a b : Ordinal.{0}) : ∀ n : ℕ, (n : Ordinal.{0}) ∈ S.CSet a b
  | 0 => by rw [Nat.cast_zero]; exact CSet.zero_mem _ _
  | n + 1 => by rw [Nat.cast_succ]; exact CSet.add_mem (te_nat_mem S a b n) (CSet.one_mem _ _)

/-- `ε_{G₀+c} < θ_{k+1}` for `c < ω`. -/
theorem te_evA_lt_th (S : InaccSeq.{0}) (k n : ℕ) : evA (Gc.gcG 0) (n : Ordinal.{0}) < Lc.lcTh S (k + 1) := by
  have hSC := Ls.lsTh_SC (S := S) (k + 1)
  have hE : InE (Lc.lcTh S (k + 1)) := Low.opow_eq_self_of_SC hSC
  have hG : Gc.gcG 0 < Lc.lcTh S (k + 1) := Tb.tb_G0_lt_th S k
  have hn : (n : Ordinal.{0}) < Lc.lcTh S (k + 1) := (natCast_lt_omega0 n).trans (omega0_lt_inE hE)
  rw [te_evA_G0]
  exact hSC.2 1 (Gn.gn_one_lt.trans hG) _ (hE.add_lt hG hn)

/-- **`TeHyp K`** for every offset code system with top `eNG n` and code bound `ε_{G₀+n+1}`. -/
theorem teHyp_of (K : Tb.TbCS) (n : ℕ) (hV : K.V = fun x => Gn.eNG n x)
    (hB : K.B = evA (Gc.gcG 0) ((n : Ordinal.{0}) + 1)) : TeHyp K where
  BE := by rw [hB]; exact evA_E _ _
  Bmem := fun S a b ha => by
    rw [hB, te_evA_G0, ← Nat.cast_succ]
    exact CSet.phi_mem (CSet.one_mem _ _) (CSet.add_mem (Gm.gmS_G0_mem S ha) (te_nat_mem S a b (n + 1)))
  Bth := fun S k => by
    rw [hB, ← evA_add_one, ← Nat.cast_succ, ← Nat.cast_succ]
    exact (te_evA_lt_th S k (n + 1 + 1)).le
  VT := fun x hx hx1 => by
    rw [hV]
    exact Gm.gm1_T hx hx1 (Gn.eNG_lt1 hx hx1 (n + 1))
  Vpi := fun σ ρ hB' => by rw [hV]; exact Gn.eNG_pi hB' n
  VNpi := fun σ ρ hB' => by rw [hV]; exact Gn.eNG_pi hB' (n + 1)

/-- **The tower**: an offset code system with top `ε_{Γ_{x+1}+1+n}` and code bound `ε_{G₀+n+1}`. -/
noncomputable def teFam : (n : ℕ) →
    {K : Tb.TbCS // K.V = (fun x => Gn.eNG n x) ∧ K.B = evA (Gc.gcG 0) ((n : Ordinal.{0}) + 1)}
  | 0 => ⟨Tb.tbEc, rfl, by
      show Tb.tbB = _
      rw [Nat.cast_zero, evA_add_one, evA_zero Gl.gl_G0_E]; rfl⟩
  | n + 1 => ⟨teNext (teFam n).1 (teHyp_of _ n (teFam n).2.1 (teFam n).2.2), by
      show (fun x => eN ((teFam n).1.V x)) = _
      rw [(teFam n).2.1]; rfl, by
      show eN (teFam n).1.B = _
      rw [(teFam n).2.2, Nat.cast_succ, evA_add_one (Gc.gcG 0) ((n : Ordinal.{0}) + 1)]⟩

theorem teFam_V (n : ℕ) (x : Ordinal.{0}) : (teFam n).1.V x = Gn.eNG n x := by rw [(teFam n).2.1]

/-! ## The union -/

variable {S : InaccSeq.{0}}

/-- **Realizers up to `υ_{a+f(n)}` for every `n` give realizers up to `υ_{a+sup_n f(n)}`.** -/
theorem te_real_iSup {a : Ordinal.{0}} {f : ℕ → Ordinal.{0}} (h : ∀ n, LrReal S a (upsilon (a + f n))) :
    LrReal S a (upsilon (a + ⨆ n, f n)) := by
  intro X Y hX hY hXY
  have hg : Order.IsNormal (fun z => upsilon (a + z)) := upsilon_normal.comp (isNormal_add_right a)
  have he : upsilon (a + ⨆ n, f n) = ⨆ n, upsilon (a + f n) := hg.map_iSup Ordinal.bddAbove_of_small
  have hex : ∃ n, ∀ y ∈ Y, y < upsilon (a + f n) := by
    rcases Y.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, by simp⟩
    · have hm := (hY _ (Y.max'_mem hne)).2
      rw [he] at hm
      obtain ⟨n, hn⟩ := (lt_ciSup_iff Ordinal.bddAbove_of_small).1 hm
      exact ⟨n, fun y hy => (Y.le_max' y hy).trans_lt hn⟩
  obtain ⟨n, hn⟩ := hex
  exact h n X Y hX (fun y hy => ⟨(hY y hy).1, hn y hy⟩) hXY

/-- `teW x = sup_n ε_{Γ_{x+1}+1+n} = ε_{Γ_{x+1}+ω}`. -/
noncomputable def teW (x : Ordinal.{0}) : Ordinal.{0} := ⨆ n : ℕ, Gn.eNG n x

theorem teW_ge (n : ℕ) (x : Ordinal.{0}) : Gn.eNG n x ≤ teW x :=
  Ordinal.le_iSup (fun n : ℕ => Gn.eNG n x) n

/-- `ε_{Γ_{x+1}+1} < ε_{Γ_{x+1}+ω}`. -/
theorem teW_gt (x : Ordinal.{0}) : eN (lgG x) < teW x :=
  (Gn.eNG_lt_succ 0 x).trans_le (teW_ge 1 x)

/-- **`ε_{Γ_{x+1}+ω}` is at most every `υ`-point above `x`.** -/
theorem teW_le {x u : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hxu : x < u) (hu : UpsPt u) : teW x ≤ u :=
  Ordinal.iSup_le fun n => by
    have := (teFam n).1.V_le x u hx hx1 hxu hu
    rwa [teFam_V] at this

/-- `υ_{a+ε_{Γ_{a+1}+ω}} < b` for every `υ`-fixed `ε`-number `b > a` (`a` a `υ`-fixed `ε`-number below `Ω₁`). -/
theorem teW_lt_b {a b : Ordinal.{0}} (haE : InE a) (ha1 : a < Om1) (hua : upsilon a = a)
    (hbE : InE b) (hub : upsilon b = b) (hab : a < b) : upsilon (a + teW a) < b := by
  have hm := upsilon_normal.strictMono
  have hU : UpsPt (upsilon (a + 1)) := upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one a))
  have ha1u : a < upsilon (a + 1) := by
    calc a = upsilon a := hua.symm
      _ < upsilon (a + 1) := hm (lt_add_one a)
  have hW : teW a ≤ upsilon (a + 1) := teW_le haE ha1 ha1u hU
  have h1 : upsilon (a + 1) < b := by
    calc upsilon (a + 1) < upsilon b := hm ((ev_isSuccLimit_of_inE hbE).add_one_lt hab)
      _ = b := hub
  have h2 : a + teW a < b := hbE.add_lt hab (hW.trans_lt h1)
  calc upsilon (a + teW a) < upsilon b := hm h2
    _ = b := hub

/-! ## The realizers up to `υ_{a+ε_{Γ_{a+1}+ω}}` -/

/-- **The realizers at `m*` up to `υ_{m*+ε_{Γ_{m*+1}+ω}} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem teRealW_M (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0))) ∧
      upsilon (Nc.ncL S 0 + teW (Nc.ncL S 0)) < Nc.ncL S 1 := by
  refine ⟨te_real_iSup fun n => ?_, ?_⟩
  · have := (Tb.tbReal_M (teFam n).1 hlow hU hL hstd).1
    rwa [teFam_V] at this
  · have hu0 : upsilon (Nc.ncL S 0) = Nc.ncL S 0 := by simpa using teUps_L (S := S) 0
    have hu1 : upsilon (Nc.ncL S 1) = Nc.ncL S 1 := by simpa using teUps_L (S := S) 1
    have hE0 : InE (Nc.ncL S 0) := Gg.gg_SC_eps (Lw.lw_L_SC S 0)
    have hE1 : InE (Nc.ncL S 1) := Gg.gg_SC_eps (Lw.lw_L_SC S 1)
    have h01 : Nc.ncL S 0 < Nc.ncL S 1 := Rl.rlM_lt_L1 (S := S)
    have ha1 : Nc.ncL S 0 < Om1 := by
      have := Lw.lw_L_eq S 0; rw [this, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _
    exact teW_lt_b hE0 ha1 hu0 hE1 hu1 h01

/-- **The realizers at `L(n+1)` up to `υ_{a+ε_{Γ_{a+1}+ω}} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem teRealW_L (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (k : ℕ) :
    LrReal S (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})))) ∧
      upsilon (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) + teW (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}))) <
        Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0}) := by
  refine ⟨te_real_iSup fun n => ?_, ?_⟩
  · have := (Tb.tbReal_L (teFam n).1 hlow hU hL hstd k).1
    rwa [teFam_V] at this
  · have hu0 := teUps_L (S := S) (k + 1)
    have hu1 := teUps_L (S := S) (k + 2)
    have hE0 : InE (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) := Gg.gg_SC_eps (Lw.lw_L_SC S _)
    have hE1 : InE (Nc.ncL S ((k + 2 : ℕ) : Ordinal.{0})) := Gg.gg_SC_eps (Lw.lw_L_SC S _)
    have h01 := teL_lt_succ (S := S) (k + 1)
    have ha1 : Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Om1 := by
      have := Lw.lw_L_eq S ((k + 1 : ℕ) : Ordinal.{0}); rw [this, Br.Om1_eq]; exact Nm.Pv_lt_Om1 S _
    exact teW_lt_b hE0 ha1 hu0 hE1 hu1 h01

end Googology.Trans.PoR.InaccPsi.R2.Te
