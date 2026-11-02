import Googology.Trans.PoR.InaccPsi.R2.YhLDN

/-!
# YhDir: THE DIRECT READING OF EVERY LAYER — `YcDirect S c Γ(c+1)` FOR EVERY `c` WITH `c + 1 < ε₀` (ONE THEOREM)

The reading `Yh.yhR` (all base atoms) below every `ε`-number bound `G < B < Γ(c+1)` is a reading system over the base
atom `Γ(c)` (`Xx.XxRS c`): code system `yhKN` (hulls `Yh.yh_mem`, code gate `Yh.yh_code_gate`, countability through
the readings below `Γ_{x+2+c}`), Lemma EXACT `Yh.yh_pi`, cofinality `Yh.yhR_cof`, the limit data `Yh.yh_ldN` with
Lemma IMG by `Xk.xkPkg_cst`.  The tower `t₀ = Γ(c)`, `t_{n+1} = yhPsi t_n 0` (gate `0`) is cofinal in `Γ(c+1)` (its
supremum is strongly critical above `Γ(c)`), so the route (c) of `Yc.YcDirect` holds at every layer:

* `yhKN`, `yhRSN` (**THE READING SYSTEM OF THE LAYER `c` BELOW `B`**), `yhTw`, `yhTw_cof`;
* `yhDirect` (**`YcDirect S c Γ(c+1)` FOR EVERY `c + 1 < ε₀`, UNCONDITIONAL**: the leaf `skLayDirect`), `yhLay`
  (**UPPER ∧ LOWER ∧ CapV at every range restart below `ι(Γ(φ(ℓ, Γ(c)+1))·ω)` for every `ℓ < Γ(c+1)`**);
* non-vacuity: `yhDirect_A2` (**`c = 0` recovers `Yc.ycDirect_A2`**), `yhDirect_one` (`c = 1`).

No new axiom.  New definitions: `yhKN`, `yhRSN`, `yhTw`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yh

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Notation.InaccPsi
  Googology.Notation.InaccPsi.InaccSeq Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Xu
  Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Xk Googology.Trans.PoR.InaccPsi.R2.Xx
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gh

theorem yh_N_le {N B : Ordinal.{0}} (hN : N < ε₀) (hGB : gcG 0 < B) : N ≤ B :=
  ((hN.trans_le gc_eps0_le_Om1).trans (gcG_Om1_lt 0)).le.trans hGB.le

theorem yh_countN {N B c y : Ordinal.{0}} (hN : N < ε₀) (hBN : B < gcG N) (hc : c ≤ B) (hy : InE y)
    (hy1 : y < Om1) : Countable {b : Iio c // yhG b.1 < y} := by
  have hq1 : gq N y < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact (yh_gqN hy hy1 hN).2.2.1
  haveI := Gc.gc_countable hq1
  let f : {b : Iio c // yhG b.1 < y} → Iio (gq N y) := fun b =>
    ⟨yhR b.1.1 y, yhR_lt hy hy1 hN ((lt_of_lt_of_le b.1.2 hc).trans hBN) b.2⟩
  refine Function.Injective.countable (f := f) fun b b' hbb => ?_
  have e : yhR b.1.1 y = yhR b'.1.1 y := congrArg Subtype.val hbb
  rcases lt_trichotomy b.1.1 b'.1.1 with h | h | h
  · exact absurd e (yhR_mono hy hy1 hN ((lt_of_lt_of_le b'.1.2 hc).trans hBN) h b'.2 b.2).ne
  · exact Subtype.ext (Subtype.ext h)
  · exact absurd e (yhR_mono hy hy1 hN ((lt_of_lt_of_le b.1.2 hc).trans hBN) h b.2 b'.2).ne'

/-- **The code system of the codes below `B < Γ(N)`**: gate `yhG`, atoms `Γ(c)`. -/
noncomputable def yhKN (N B : Ordinal.{0}) (hN : N < ε₀) (hBE : InE B) (hGB : gcG 0 < B) (hBN : B < gcG N) :
    GsCS where
  B := B
  gt := yhG
  B_V := hBN.trans_le (gcG_le (yh_N_le hN hGB))
  gt_zero := yhG_zero
  gt_lt := fun c _ => yhG_lt_Om1 c
  gt_succ := fun b _ hZ _ hg => yhG_succ hZ b hg
  mem := fun S _ _ c hc hca hg => (yh_mem (S := S) hN c (hc.trans hBN) hca hg).1
  κ := yhG B
  κ_lt := yhG_lt_Om1 B
  B_mem := fun S _ _ ha hκ => (yh_mem (S := S) hN B hBN ha hκ).1
  code_gate := fun Z hZ1 hZ0 _ hZp c hc _ => by
    have hSC : SC Z := ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩
    have hZ1' : Z ≤ Om1 := hZ1
    refine yh_code_gate hSC hZ1' ?_ c hc
    rintro s ⟨c', -, -, rfl⟩
    exact yhAt_gcG c'
  count := fun _ _ hc hy hy1 => yh_countN hN hBN hc hy hy1

theorem yh_cofEN {N x c : Ordinal.{0}} (hN : N < ε₀) (hx : InE x) (hx1 : x < Om1) (hc : c < gcG N)
    (hEc : gfE < c) (hg : yhG c < x) {ν : Ordinal.{0}} (hν : ν < yhR c x) :
    ∃ b, gfE ≤ b ∧ b < c ∧ yhG b < x ∧ ν ≤ yhR b x := by
  have hgE : yhG gfE = 0 := by rw [yhG_low gfE_lt_G0, glG_E]
  obtain ⟨b, hbc, hgb, hνb⟩ := yhR_cof hx hx1 hN c hc hg ν hν
  rcases lt_or_ge b gfE with hbE | hbE
  · refine ⟨gfE, le_rfl, hEc, by rw [hgE]; exact hx.pos, ?_⟩
    exact hνb.trans (yhR_mono hx hx1 hN (hEc.trans hc) hbE (by rw [hgE]; exact hx.pos) hgb).le
  · exact ⟨b, hbE, hbc, hgb, hνb⟩

/-- **The limit data with Lemma IMG** at every limit code `ε_{Ω₁+1} < c < B`. -/
theorem yh_ldGsN (c B : Ordinal.{0}) (hc : c + 1 < ε₀) (hBE : InE B) (hGB : gcG 0 < B) (hBN : B < gcG (c + 1)) :
    ∀ d, IsSuccLimit d → gfE < d → d < B → Nonempty (GsmLD (yhKN (c + 1) B hc hBE hGB hBN) yhR d) := by
  intro d hl hEd hd
  have hgE : yhG gfE = 0 := by rw [yhG_low gfE_lt_G0, glG_E]
  obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := yh_ldN hc d hl (hd.trans hBN)
  have hlg : ∀ x, InE x → x < Om1 → yhG d < x → lg (yhR d x) = T x := fun x hx hx1 hg => by
    obtain ⟨e1, e2, -, -⟩ := hdec x hx hx1 hg
    rw [e1]; exact Ge.lg_add_opow e2
  refine ⟨{
    cp := if gfE ≤ cp then cp else gfE
    lp := lp
    cp_ge := ?_
    cp_lt := ?_
    cp_g := ?_
    dec := ?_
    pkg := ?_ }⟩
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact hcp
    · exact hEd
  · show yhG _ ≤ yhG d
    split_ifs with h
    · exact hgcp
    · rw [hgE]; exact zero_le
  · intro x hx hx1 hg
    obtain ⟨e1, e2, e3, e4⟩ := hdec x hx hx1 hg
    show yhR d x = _ ∧ _
    rw [hlg x hx hx1 hg]
    refine ⟨e1, e2, e3, ?_⟩
    split_ifs with h
    · exact e4
    · push Not at h
      exact e4.trans (yhR_mono hx hx1 hc (hEd.trans (hd.trans hBN)) h (by rw [hgE]; exact hx.pos)
        (hgcp.trans_lt hg)).le
  · intro ρ τ δ h hg
    show GhPkg (yhG d) ρ δ (fun y => lg (yhR d y))
    have hρE := upsPt_inE h.ρU
    obtain ⟨e1, -, -, -⟩ := hdec ρ hρE h.ρ1 hg
    have hTρ : T ρ < gq (c + 1) ρ := by
      have h1 : T ρ ≤ yhR d ρ := by
        rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
      exact h1.trans_lt (yhR_lt hρE h.ρ1 hc (hd.trans hBN) hg)
    have hP := Xk.xkPkg_cst h le_add_self hc hg (C := ∅) (by simp) hTρ
      (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
    exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg

/-- **THE READING SYSTEM OF THE LAYER `c` BELOW AN `ε`-NUMBER BOUND `G < B < Γ(c+1)`** over the base atom `Γ(c)`. -/
noncomputable def yhRSN (c B : Ordinal.{0}) (hc : c + 1 < ε₀) (hBE : InE B) (hGB : gcG 0 < B)
    (hBN : B < gcG (c + 1)) : XxRS c where
  K := yhKN (c + 1) B hc hBE hGB hBN
  R := yhR
  E_lt := gfE_lt_G0.trans hGB
  B_lim := ev_isSuccLimit_of_inE hBE
  gt_E := by show yhG gfE = 0; rw [yhG_low gfE_lt_G0, glG_E]
  gt_lowE := fun d hd => by show yhG d = gtc d; rw [yhG_low (hd.trans gfE_lt_G0), glG_low hd]
  R_E := fun x _ _ => by rw [yhR_low gfE_lt_G0, glR_E]
  lt0 := fun d x hx hx1 hd hg => yhR_lt hx hx1 hc (hd.trans hBN) hg
  mono := fun b d x hx hx1 hd hbd hgb hgd => yhR_mono hx hx1 hc (hd.trans hBN) hbd hgd hgb
  succ := fun b x _ => yhR_succ b x
  gt_le_succ := yhG_le_succ
  cof := fun d x hx hx1 hd hEd hg ν hν => yh_cofEN hc hx hx1 (hd.trans hBN) hEd hg hν
  ex := fun σ ρ d hB hd hg => yh_pi hB hc d (hd.trans hBN) hg
  ld := yh_ldGsN c B hc hBE hGB hBN
  W_lt := hc

theorem yhRSN_B (c B : Ordinal.{0}) (hc : c + 1 < ε₀) (hBE : InE B) (hGB : gcG 0 < B) (hBN : B < gcG (c + 1)) :
    (yhRSN c B hc hBE hGB hBN).K.B = B := rfl

theorem yhRSN_gt (c B : Ordinal.{0}) (hc : c + 1 < ε₀) (hBE : InE B) (hGB : gcG 0 < B) (hBN : B < gcG (c + 1)) :
    (yhRSN c B hc hBE hGB hBN).K.gt = yhG := rfl

/-! ## The tower `Γ(c), yhPsi Γ(c) 0, …` cofinal in `Γ(c+1)` -/

/-- **The tower**: `t₀ = Γ(c)`, `t_{n+1} = yhPsi t_n 0`. -/
noncomputable def yhTw (c : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => gcG c
  | n + 1 => yhPsi (yhTw c n) 0

theorem yhTw_one_le (c : Ordinal.{0}) : ∀ n, 1 ≤ yhTw c n
  | 0 => (Lu.lu_one_lt_E (Low.opow_eq_self_of_SC (gcG_SC c))).le
  | n + 1 => (yhTw_one_le c n).trans (yhPsi_gt (yhTw_one_le c n) 0).2.le

theorem yhTw_lt_succ (c : Ordinal.{0}) (n : ℕ) : yhTw c n < yhTw c (n + 1) :=
  (yhPsi_gt (yhTw_one_le c n) 0).2

theorem yhTw_strictMono (c : Ordinal.{0}) : StrictMono (yhTw c) :=
  strictMono_nat_of_lt_succ (yhTw_lt_succ c)

theorem yhTw_ge (c : Ordinal.{0}) (n : ℕ) : gcG c ≤ yhTw c n :=
  (yhTw_strictMono c).monotone (Nat.zero_le n)

theorem yhTw_lt (c : Ordinal.{0}) : ∀ n, yhTw c n < gcG (c + 1)
  | 0 => gcG_lt (lt_add_one c)
  | n + 1 => yhPsi_lt_SC (gcG_SC _) (by rw [Br.Om1_eq]; exact gcG_Om1_lt _) (yhTw_lt c n) (gcG_SC _).1

theorem yhTw_G (c : Ordinal.{0}) (n : ℕ) : gcG 0 < yhTw c (n + 1) :=
  (gcG_le zero_le).trans_lt ((yhTw_ge c n).trans_lt (yhTw_lt_succ c n))

theorem yhTw_E (c : Ordinal.{0}) (n : ℕ) : InE (yhTw c (n + 1)) := yhPsi_E (yhTw_one_le c n) 0

theorem yhTw_g (c : Ordinal.{0}) : ∀ n, yhG (yhTw c n) = 0
  | 0 => yhG_atom c
  | n + 1 => by
    show yhG (yhPsi (yhTw c n) 0) = 0
    rw [yhG_psi (yhTw_one_le c n) (yhTw_G c n), yhQ_zero]
    have hω : ¬ yhTw c n < ω := not_lt.2 ((omega0_lt_inE gl_G0_E).le.trans
      ((gcG_le zero_le).trans (yhTw_ge c n)))
    unfold yhQ; rw [if_neg hω, yhTw_g c n, max_self]

/-- **THE TOWER IS COFINAL IN `Γ(c+1)`**: its supremum is strongly critical above `Γ(c)`. -/
theorem yhTw_cof (c : Ordinal.{0}) : ∀ B, B < gcG (c + 1) → ∃ n, B < yhTw c n := by
  intro B hB
  by_contra hcon
  push Not at hcon
  have hbdd : BddAbove (Set.range (yhTw c)) := Ordinal.bddAbove_of_small
  set u := ⨆ n, yhTw c n with hu
  have hle : ∀ n, yhTw c n ≤ u := fun n => le_ciSup hbdd n
  have huB : u ≤ B := ciSup_le hcon
  have hlt : ∀ n, yhTw c n < u := fun n => (yhTw_lt_succ c n).trans_le (hle (n + 1))
  have hSC : SC u := by
    refine ⟨(gcG_SC c).1.trans_le (hle 0), fun a ha b hb => ?_⟩
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 ha
    obtain ⟨m, hm⟩ := (lt_ciSup_iff hbdd).1 hb
    have hk : ∀ j, j ≤ max n m → yhTw c j ≤ yhTw c (max n m) := fun j hj => (yhTw_strictMono c).monotone hj
    have hak : a < yhTw c (max n m) := hn.trans_le (hk n (le_max_left _ _))
    have hbk : b < yhTw c (max n m + 1) :=
      (hm.trans_le (hk m (le_max_right _ _))).trans (yhTw_lt_succ c _)
    obtain ⟨y, hy⟩ := yhPsi_P (yhTw c (max n m)) 0
    have hfix : veblen a (yhTw c (max n m + 1)) = yhTw c (max n m + 1) := by
      show veblen a (yhPsi (yhTw c (max n m)) 0) = yhPsi (yhTw c (max n m)) 0
      rw [← hy]; exact veblen_veblen_of_lt hak y
    calc veblen a b < veblen a (yhTw c (max n m + 1)) := veblen_lt_veblen_iff_right.2 hbk
      _ = yhTw c (max n m + 1) := hfix
      _ < u := hlt _
  have hOu : Om 1 < u := (gcG_Om1_lt c).trans_le (hle 0)
  have hGu : gcG (c + 1) ≤ u := gcG_le_of hSC hOu (fun β hβ =>
    (gcG_le (Order.lt_add_one_iff.1 hβ)).trans_lt (hlt 0))
  exact absurd (hGu.trans huB) (not_le.2 hB)

/-- **ROUTE (c) AT EVERY LAYER: `YcDirect S c Γ(c+1)` FOR EVERY `c` WITH `c + 1 < ε₀`, UNCONDITIONAL** (the leaf
`skLayDirect`): every `B < Γ(c+1)` lies below a tower code `t_n` (gate `0`) of the reading system `yhRSN c t_{n+1}`. -/
theorem yhDirect (S : InaccSeq.{0}) (c : Ordinal.{0}) (hc : c + 1 < ε₀) : Yc.YcDirect S c (gcG (c + 1)) := by
  intro B hB
  obtain ⟨n, hn⟩ := yhTw_cof c B hB
  refine ⟨yhRSN c (yhTw c (n + 1)) hc (yhTw_E c n) (yhTw_G c n) (yhTw_lt c (n + 1)), yhTw c n, hn.le,
    (gfE_lt_G0.trans_le ((gcG_le zero_le).trans (yhTw_ge c n))).le, yhTw_lt_succ c n, ?_⟩
  show yhG (yhTw c n) < Td.tdK S
  rw [yhTw_g]; exact Td.tdK_SC.1

/-- **THE WHOLE LAYER `c` FROM THE DIRECT READING** (`c + 1 < ε₀`): UPPER ∧ LOWER ∧ CapV at every range restart
`l < ι(Γ(φ(ℓ, Γ(c)+1))·ω)`, `ℓ < Γ(c+1)` (the conclusions of `skLayLo` and `skLayHi` at `c`). -/
theorem yhLay (S : InaccSeq.{0}) (c : Ordinal.{0}) (hc : c + 1 < ε₀) : ∀ l, Cd.CdRange S l →
    (∃ ℓ, ℓ < gcG (c + 1) ∧ l < Bt.iota S (gcG (veblen ℓ (gcG c + 1)) * ω)) →
      Cd.CdUpper S l ∧ Cd.CdLower S l ∧ Cd.CdCapV S l :=
  Yc.ycLay_of_direct (yhDirect S c hc)

/-- `YcDirect` is monotone in the bound. -/
theorem yhDirect_mono {S : InaccSeq.{0}} {c B₀ B₁ : Ordinal.{0}} (h : Yc.YcDirect S c B₀) (hB : B₁ ≤ B₀) :
    Yc.YcDirect S c B₁ := fun B hB1 => h B (hB1.trans_le hB)

theorem yh_one_eps : (1 : Ordinal.{0}) + 1 < ε₀ := by
  rw [one_add_one_eq_two]; exact (natCast_lt_omega0 2).trans (omega0_lt_epsilon 0)

theorem yh_zero_eps : (0 : Ordinal.{0}) + 1 < ε₀ := by
  rw [zero_add]; exact one_lt_omega0.trans (omega0_lt_epsilon 0)

/-- **Non-vacuity, `c = 0`**: the generic theorem recovers `Yc.ycDirect_A2` (`φ(G, 1) < Γ(1)`). -/
theorem yhDirect_A2 (S : InaccSeq.{0}) : Yc.YcDirect S 0 (veblen (gcG 0) 1) :=
  yhDirect_mono (yhDirect S 0 yh_zero_eps) (by rw [zero_add]; exact (xu_veb_lt_G1 xu_G0_lt_G1 (lt_of_lt_of_le
    one_lt_omega0 (omega0_lt_inE xu_G1_E).le)).le)

/-- **The layer `1`**: `YcDirect S 1 Γ(2)`. -/
theorem yhDirect_one (S : InaccSeq.{0}) : Yc.YcDirect S 1 (gcG (1 + 1)) := yhDirect S 1 yh_one_eps

end Googology.Trans.PoR.InaccPsi.R2.Yh
