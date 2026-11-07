import Googology.Trans.PoR.InaccPsi.R2.AwOps
import Googology.Trans.PoR.InaccPsi.R2.ZkShift
import Googology.Trans.PoR.InaccPsi.R2.XjFrag

/-!
# AwCan: THE FRAG MAP MOVES THE READINGS: `Ψ(Θ_ρ c) = Θ_σ c`

`Θ_y = gxTh y (awAt S y)`.  For a FRAG map `Ψ` (`Xj.XjFragConcl Xe.XeLev`) of a chain with `b₀ = ρ`, `b₁ = awNx ρ`, `c₀ = σ`,
`c₁ = awNx σ` (in either direction: `σ < ρ` or `ρ < σ`) and a finite set `H` of codes over `κ` closed under the parts of
`AwOps` (`AwStep`), with the readings at `ρ` in the domain of `Ψ`: `Ψ(Θ_ρ z) = Θ_σ z` for `z ∈ H`.  The node over `x = b₁` of a
reading has a parameter only, the reading of a smaller code (`aw_Rd_opow`, `aw_Rd_phi`, `aw_read`), so the hull clauses
`Vl.VlCl`, `Xj.XjCl` of FRAG apply at terms `th1 (par w)`, `thc u (par w)`, and the argument moves by induction.

* `AwStep` (the parts of a code), `aw_closure` (**every code below `K_ω` lies in a finite closed set of codes**);
* `aw_opow_mul`, `aw_Rd_cnf` (the reading on the Cantor normal form), `aw_zkEx_Rd`, `aw_vcLv_mul`, `aw_zkCnf`
  (**the level of a node moves as a code**);
* `aw_mv_xi` (**below `θ`: `mv ρ σ (R_ρ z) = R_σ z`**), `aw_seg_lt`;
* `aw_can` (**`Ψ(Θ_ρ z) = Θ_σ z`**).

No new axiom.  New definition: `AwStep`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Aw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Qf Googology.Trans.PoR.InaccPsi.R2.Zk Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl Googology.Trans.PoR.InaccPsi.R2.Xj

variable {S : InaccSeq.{0}}

/-- The atoms `awAt` form an atom family. -/
theorem aw_gxAt (S : InaccSeq.{0}) (y : Ordinal.{0}) : GxAt (awAt S y) := (awU S).gxAt y

/-- **The parts of a code in a finite set `H`**: a code `≤ θ`, a sum, an `ω`-power, a Veblen value or an atom. -/
def AwStep (S : InaccSeq.{0}) (H : Finset Ordinal.{0}) (z : Ordinal.{0}) : Prop :=
  z ≤ ConjT.th S ∨
    (∃ u v, u ∈ H ∧ v ∈ H ∧ z = u + v ∧ u < z ∧ v < z) ∨
    (∃ a, a ∈ H ∧ awS0 S a ∈ H ∧ z = ω ^ a ∧ ω ^ a ≠ a ∧ ConjT.th S ≤ a ∧ a < z ∧ awS0 S a < z) ∨
    (∃ a b, a ∈ H ∧ b ∈ H ∧ qfInd a (ConjT.th S) b ∈ H ∧ 1 ≤ a ∧ z = veblen a b ∧ a < z ∧ b < z ∧
      qfInd a (ConjT.th S) b < z ∧ ZkEx (fun e => e ∈ H ∧ e < z) a) ∨
    (∃ d, d ∈ H ∧ 0 < d ∧ z = S.psi (Om ω + d) (Om (1 + 1)) ∧ d < z)

theorem AwStep.mono {H H' : Finset Ordinal.{0}} (h : H ⊆ H') {z : Ordinal.{0}} (hz : AwStep S H z) : AwStep S H' z := by
  rcases hz with hz | ⟨u, v, h1, h2, h3⟩ | ⟨a, h1, h2, h3⟩ | ⟨a, b, h1, h2, h3, h4⟩ | ⟨d, h1, h2⟩
  · exact Or.inl hz
  · exact Or.inr (Or.inl ⟨u, v, h h1, h h2, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, h h1, h h2, h3⟩))
  · obtain ⟨h5, h6, h7, h8, h9, h10⟩ := h4
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, h h1, h h2, h h3, h5, h6, h7, h8, h9,
      zkEx_mono (fun e he => ⟨h he.1, he.2⟩) a h10⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, h h1, h2⟩)))

/-- The parts of a code satisfy a property, a statement closed under finite unions. -/
private theorem aw_union {H1 H2 : Finset Ordinal.{0}} {P : Ordinal.{0} → Prop}
    (h1 : ∀ z ∈ H1, P z ∧ AwStep S H1 z) (h2 : ∀ z ∈ H2, P z ∧ AwStep S H2 z) :
    ∀ z ∈ H1 ∪ H2, P z ∧ AwStep S (H1 ∪ H2) z := by
  intro z hz
  rcases Finset.mem_union.1 hz with hz | hz
  · exact ⟨(h1 z hz).1, (h1 z hz).2.mono Finset.subset_union_left⟩
  · exact ⟨(h2 z hz).1, (h2 z hz).2.mono Finset.subset_union_right⟩

section Cnf

variable {y : Ordinal.{0}} (hy : SC y)
include hy

theorem aw_mul_nat {u : Ordinal.{0}} (hu : GxCl y (awAt S y) u) : ∀ n : ℕ, GxCl y (awAt S y) (u * n)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hy.1
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact GxCl.add (aw_mul_nat hu n) hu

theorem aw_Rd_mul_nat {u : Ordinal.{0}} (hu : GxCl y (awAt S y) u) :
    ∀ n : ℕ, gxTh y (awAt S y) (u * n) = gxTh y (awAt S y) u * n
  | 0 => by rw [Nat.cast_zero, mul_zero, mul_zero, gxTh_zero]
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one, mul_add_one, gxTh_add hy (aw_gxAt S y) (aw_mul_nat hy hu n),
      aw_Rd_mul_nat hu n]

/-- The parts of a code `ω^c·k + r` are codes. -/
theorem aw_parts_code {c k r : Ordinal.{0}} (hk0 : k ≠ 0) (hk : k < ω) (hr : r < ω ^ c)
    (ha : GxCl y (awAt S y) (ω ^ c * k + r)) : GxCl y (awAt S y) c ∧ GxCl y (awAt S y) r := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  obtain ⟨-, hl, -, -⟩ := zk_parts hk0 hk hr
  have hcc : GxCl y (awAt S y) c := by
    have := (gxDec hy hAt _ ha).2
    rwa [hl] at this
  refine ⟨hcc, ?_⟩
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  have := (gxDec hy hAt _ ha).1 _ (aw_mul_nat hy (hcc.opow hy.1) n) le_self_add
  rwa [Ordinal.add_sub_cancel] at this

/-- **The reading on the Cantor normal form.** -/
theorem aw_Rd_cnf {c k r : Ordinal.{0}} (hk : k < ω) (hc : GxCl y (awAt S y) c) (hrc : GxCl y (awAt S y) r)
    (hr : r < ω ^ c) :
    gxTh y (awAt S y) (ω ^ c * k + r) = ω ^ gxTh y (awAt S y) c * k + gxTh y (awAt S y) r ∧
      gxTh y (awAt S y) r < ω ^ gxTh y (awAt S y) c := by
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  obtain ⟨n, rfl⟩ := lt_omega0.1 hk
  have hop := gxTh_opow hy hAt hc
  constructor
  · rw [gxTh_add hy hAt (aw_mul_nat hy (hc.opow hy.1) n), aw_Rd_mul_nat hy (hc.opow hy.1) n, hop]
  · rw [← hop]; exact gxTh_lt hrc hr

/-- The Cantor exponents of a code are codes, in a finite set. -/
theorem aw_exps_code (hy1 : y < Om1) : ∀ a, GxCl y (awAt S y) a →
    ∃ E : Finset Ordinal.{0}, (∀ w ∈ E, GxCl y (awAt S y) w ∧ w ≤ a) ∧ ZkEx (· ∈ E) a := by
  classical
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro ha
  rcases eq_or_ne a 0 with rfl | h0
  · exact ⟨∅, by simp, zkEx_zero _⟩
  obtain ⟨hk0, hk, hr, he⟩ := zk_dec h0
  rw [← he] at ha
  obtain ⟨hlc, hrc⟩ := aw_parts_code hy hk0 hk hr ha
  have hlt := mod_opow_log_lt_self ω h0
  obtain ⟨E, hE1, hE2⟩ := IH _ hlt hrc
  refine ⟨insert (log ω a) E, fun w hw => ?_, ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hlc, log_le_self _ _⟩
    · exact ⟨(hE1 w hw).1, (hE1 w hw).2.trans hlt.le⟩
  · rw [zkEx_ne _ h0]
    exact ⟨Finset.mem_insert_self _ _, zkEx_mono (fun w hw => Finset.mem_insert_of_mem hw) _ hE2⟩

/-- A property of the readings of the exponents of a code is a property of the exponents of its reading. -/
theorem aw_zkEx_Rd {P : Ordinal.{0} → Prop} : ∀ a, GxCl y (awAt S y) a →
    ZkEx (fun e => P (gxTh y (awAt S y) e)) a → ZkEx P (gxTh y (awAt S y) a) := by
  refine zk_ind (fun _ _ => by rw [gxTh_zero]; exact zkEx_zero _) ?_
  intro c k r hk0 hk hr IH ha hE
  obtain ⟨hcc, hrc⟩ := aw_parts_code hy hk0 hk hr ha
  obtain ⟨e1, e2⟩ := aw_Rd_cnf hy hk hcc hrc hr
  rw [zkEx_step _ hk0 hk hr] at hE
  rw [e1, zkEx_step _ hk0 hk e2]
  exact ⟨hE.1, IH hrc hE.2⟩

end Cnf

/-- **The exponent map of `f` sends the reading at `ρ` to the reading at `σ`** when it does on the exponents. -/
theorem aw_zkCnf {ρ σ : Ordinal.{0}} (hρ : SC ρ) (hσ : SC σ) {f : Ordinal.{0} → Ordinal.{0}} :
    ∀ a, GxCl ρ (awAt S ρ) a → GxCl σ (awAt S σ) a →
      ZkEx (fun e => f (gxTh ρ (awAt S ρ) e) = gxTh σ (awAt S σ) e) a →
      zkCnf f (gxTh ρ (awAt S ρ) a) = gxTh σ (awAt S σ) a := by
  refine zk_ind (fun _ _ _ => by rw [gxTh_zero, gxTh_zero, zkCnf_zero]) ?_
  intro c k r hk0 hk hr IH ha hb hE
  obtain ⟨hcc, hrc⟩ := aw_parts_code hρ hk0 hk hr ha
  obtain ⟨hcc', hrc'⟩ := aw_parts_code hσ hk0 hk hr hb
  obtain ⟨e1, e2⟩ := aw_Rd_cnf hρ hk hcc hrc hr
  obtain ⟨e1', -⟩ := aw_Rd_cnf hσ hk hcc' hrc' hr
  rw [zkEx_step _ hk0 hk hr] at hE
  rw [e1, e1', zkCnf_step f hk0 hk e2, hE.1, IH hrc hrc' hE.2]

/-- **The leaves of `Ω₁·v` from its exponents.** -/
theorem aw_vcLv_mul {P : Ordinal.{0} → Prop} (hP0 : P 0) :
    ∀ v, v < Om1 → ZkEx P v → Vc.VcLv P (Om1 * v) := by
  refine zk_ind (fun _ _ => by rw [mul_zero]; exact (Vc.VcLv_small P Rj.rj_Om1_pos).2 hP0) ?_
  intro c k r hk0 hk hr IH hv hE
  have hO : (0 : Ordinal.{0}) < Om1 := Rj.rj_Om1_pos
  have hrv : r < Om1 := (le_add_self (a := r)).trans_lt hv
  have hcv : c < Om1 := by
    have h1 : ω ^ c ≤ ω ^ c * k + r := (le_mul_left _ (pos_iff_ne_zero.2 hk0)).trans le_self_add
    exact ((right_le_opow c zk_one_lt_omega).trans h1).trans_lt hv
  rw [zkEx_step _ hk0 hk hr] at hE
  obtain ⟨hz, hzr⟩ := zk_mul_cnf (k := k) hr
  by_cases h1 : ω ^ c * k + r = 1
  · rw [h1, mul_one]
    unfold Vc.VcLv
    rw [dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_neg (lt_irrefl _)]
    trivial
  have hne0 := (zk_parts hk0 hk hr).1
  have hv2 : 2 ≤ ω ^ c * k + r := by
    rcases lt_or_ge (ω ^ c * k + r) 2 with h | h
    · exfalso
      have : ω ^ c * k + r < 1 + 1 := by rwa [one_add_one_eq_two]
      rcases (Order.lt_add_one_iff.1 this).lt_or_eq with h' | h'
      · exact hne0 (Ordinal.lt_one_iff_zero.1 h')
      · exact h1 h'
    · exact h
  set z := Om1 * (ω ^ c * k + r) with hzdef
  have hzO : Om1 < z := by
    have := mul_le_mul_left' hv2 Om1
    rw [Ordinal.mul_two] at this
    exact (lt_add_of_pos_right _ hO).trans_le this
  have hzB : z < Uc.ucB := zk_Om1_mul_lt_B hv
  have hzE : ω ^ z ≠ z := zk_mul_not_eps hv2 hv
  obtain ⟨-, hl, -, hm⟩ := zk_parts (c := Om1 + c) hk0 hk hzr
  rw [← hz] at hl hm
  rw [Vc.VcLv, dif_pos ⟨hzO, hzB⟩, dif_neg hzE]
  dsimp only
  rw [hl, hm]
  refine ⟨?_, IH hrv hE.2⟩
  by_cases hc0 : c = 0
  · subst hc0
    rw [add_zero, zk_Om1_opow, if_pos rfl]
    unfold Vc.VcLv
    rw [dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_neg (lt_irrefl _)]
    trivial
  · have hne : ω ^ (Om1 + c) ≠ Om1 + c := by
      intro h
      have h2 : Om1 + c < Om1 * ω ^ c := by
        have hω : (2 : Ordinal.{0}) ≤ ω ^ c :=
          zk_two_lt_omega.le.trans (left_le_opow ω (pos_iff_ne_zero.2 hc0))
        have := mul_le_mul_left' hω Om1
        rw [Ordinal.mul_two] at this
        exact ((add_lt_add_iff_left Om1).2 hcv).trans_le this
      rw [opow_add, zk_Om1_opow] at h
      exact absurd h h2.ne'
    rw [if_neg hne, Ordinal.add_sub_cancel]
    exact (Vc.VcLv_small P hcv).2 hE.1

section Closure

variable {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1)
include hy hy1

/-- **Every code below `K_ω` lies in a finite set of codes `≤` it, closed under the parts.** -/
theorem aw_closure : ∀ c, GxCl y (awAt S y) c → c < awV S →
    ∃ H : Finset Ordinal.{0}, c ∈ H ∧ ∀ z ∈ H, (GxCl y (awAt S y) z ∧ z ≤ c) ∧ AwStep S H z := by
  classical
  have hAt : GxAt (awAt S y) := (awU S).gxAt y
  have hy1' : y < Om 1 := by rw [← Rj.rj_Om1]; exact hy1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcV
  rcases le_or_gt c (ConjT.th S) with hθ | hθ
  · exact ⟨{c}, by simp, fun z hz => by
      rw [Finset.mem_singleton.1 hz]
      exact ⟨⟨hc, le_rfl⟩, Or.inl hθ⟩⟩
  -- a helper: from finitely many smaller codes
  have hnew : ∀ (L : Finset Ordinal.{0}), (∀ w ∈ L, GxCl y (awAt S y) w ∧ w < c) →
      ∃ H : Finset Ordinal.{0}, L ⊆ H ∧ ∀ z ∈ H, (GxCl y (awAt S y) z ∧ z < c) ∧ AwStep S H z := by
    intro L
    induction L using Finset.induction_on with
    | empty => exact fun _ => ⟨∅, by simp, by simp⟩
    | @insert w L _ ih =>
      intro hL
      obtain ⟨H0, hs0, h0⟩ := ih fun u hu => hL u (Finset.mem_insert_of_mem hu)
      obtain ⟨hwc, hwlt⟩ := hL w (Finset.mem_insert_self _ _)
      obtain ⟨H1, hw1, h1⟩ := IH w hwlt hwc (hwlt.trans hcV)
      refine ⟨H0 ∪ H1, ?_, ?_⟩
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact Finset.mem_union_right _ hw1
        · exact Finset.mem_union_left _ (hs0 hu)
      · refine aw_union (P := fun z => GxCl y (awAt S y) z ∧ z < c) h0 fun z hz => ?_
        obtain ⟨⟨a1, a2⟩, a3⟩ := h1 z hz
        exact ⟨⟨a1, a2.trans_lt hwlt⟩, a3⟩
  have hfin : ∀ (L : Finset Ordinal.{0}), (∀ w ∈ L, GxCl y (awAt S y) w ∧ w < c) →
      (∀ H : Finset Ordinal.{0}, L ⊆ H → AwStep S (insert c H) c) →
      ∃ H : Finset Ordinal.{0}, c ∈ H ∧ ∀ z ∈ H, (GxCl y (awAt S y) z ∧ z ≤ c) ∧ AwStep S H z := by
    intro L hL hst
    obtain ⟨H, hLH, hH⟩ := hnew L hL
    refine ⟨insert c H, Finset.mem_insert_self _ _, fun z hz => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨⟨hc, le_rfl⟩, hst H hLH⟩
    · obtain ⟨⟨a1, a2⟩, a3⟩ := hH z hz
      exact ⟨⟨a1, a2.le⟩, a3.mono (Finset.subset_insert _ _)⟩
  have hc0 : c ≠ 0 := ((Om_pos one_ne_zero).trans ((psiS_bounds (S := S) _ 1).1.trans hθ)).ne'
  by_cases hP : IsPrincipal (· + ·) c
  · by_cases hE : ω ^ c = c
    · by_cases hI : invVeblen₁ c < c
      · have e : veblen (invVeblen₁ c) (invVeblen₂ c) = c := by rw [veblen_invVeblen₁_invVeblen₂, hE]
        have h2 : invVeblen₂ c < c := Tf.tf_inv2_lt hE
        obtain ⟨hac, hbc⟩ := gxDecV hy.1 hAt hc _ _ e h2
        set a := invVeblen₁ c with ha
        set b := invVeblen₂ c with hb
        have hab : a < veblen a b := by rw [e]; exact hI
        have hbb : b < veblen a b := by rw [e]; exact h2
        have hθφ : ConjT.th S < veblen a b := by rw [e]; exact hθ
        obtain ⟨hic, hib, -⟩ := aw_Rd_ind (S := S) hy hy1 hac hbc hab hbb hθφ
        have ha1 : 1 ≤ a := by
          refine one_le_iff_ne_zero.2 fun h0 => ?_
          rw [h0, veblen_zero_apply] at e
          exact absurd (opow_inj (e.trans hE.symm)) h2.ne
        -- the exponents of `a`
        obtain ⟨E, hE1, hE2⟩ := aw_exps_code (S := S) hy hy1 a hac
        refine hfin (insert a (insert b (insert (qfInd a (ConjT.th S) b) E))) ?_ fun H hL => ?_
        · intro w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | rfl | rfl | hw
          · exact ⟨hac, hI⟩
          · exact ⟨hbc, h2⟩
          · exact ⟨hic, hib.trans_lt h2⟩
          · exact ⟨(hE1 w hw).1, (hE1 w hw).2.trans_lt hI⟩
        · have hsub : ∀ w ∈ insert a (insert b (insert (qfInd a (ConjT.th S) b) E)),
              w ∈ insert c H := fun w hw => Finset.mem_insert_of_mem (hL hw)
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hsub _ (by simp), hsub _ (by simp), hsub _ (by simp), ha1,
            e.symm, hI, h2, hib.trans_lt h2, ?_⟩)))
          exact zkEx_mono (fun w hw => ⟨hsub w (by simp [hw]), (hE1 w hw).2.trans_lt hI⟩) a hE2
      · have hOc : (Om1 : Ordinal.{0}) < c := by
          rw [Rj.rj_Om1]; exact (psiS_bounds (S := S) _ 1).1.trans hθ
        have hSC : SC c := by
          rw [← Tf.tf_SC_gamma hOc hI]; exact Lq.lq_gamma_SC _
        have hc1 : Om 1 < c := by rw [← Rj.rj_Om1]; exact hOc
        have hat : c ∈ awAt S y := gxSC_atom hy1' hc hSC hc1
        obtain ⟨d, hd0, hdc, -, hdc', e⟩ := aw_atom_form hy hy1'.le hat hθ
        refine hfin {d} ?_ fun H hL => ?_
        · intro w hw
          rw [Finset.mem_singleton.1 hw]
          exact ⟨hdc', hdc⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨d, Finset.mem_insert_of_mem (hL (by simp)), hd0, e, hdc⟩)))
    · -- `c = ω^a`
      obtain ⟨a, rfl⟩ := indec_eq_opow (indec_iff.2 ⟨hc0, hP⟩)
      have hEa : ω ^ a ≠ a := by
        intro h
        apply hE
        rw [h]; exact h
      have haT : a < ω ^ a := lt_of_le_of_ne (right_le_opow a one_lt_omega0) (Ne.symm hEa)
      have hac : GxCl y (awAt S y) a := by
        have := (gxDec hy hAt _ hc).2
        rwa [log_opow one_lt_omega0] at this
      have hθa : ConjT.th S ≤ a := by
        by_contra hlt
        push Not at hlt
        have : ω ^ a < ConjT.th S := by
          conv_rhs => rw [← show ω ^ ConjT.th S = ConjT.th S from aw_th_E]
          exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
        exact absurd hθ (not_lt.2 this.le)
      obtain ⟨hsc, hsa, -⟩ := aw_Rd_opow (S := S) hy hy1 hac hθa hEa
      refine hfin {a, awS0 S a} ?_ fun H hL => ?_
      · intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact ⟨hac, haT⟩
        · exact ⟨hsc, hsa.trans_lt haT⟩
      · exact Or.inr (Or.inr (Or.inl ⟨a, Finset.mem_insert_of_mem (hL (by simp)),
          Finset.mem_insert_of_mem (hL (by simp)), rfl, hEa, hθa, haT, hsa.trans_lt haT⟩))
  · have hlc : lead c < c := lt_of_le_of_ne (lead_le hc0) fun e =>
      hP (by rw [← e]; exact isPrincipal_add_omega0_opow _)
    have htc : tail c < c := tail_lt hc0
    have hlcode : GxCl y (awAt S y) (lead c) := (gxDec hy hAt c hc).2.opow hy.1
    have htcode : GxCl y (awAt S y) (tail c) := (gxDec hy hAt c hc).1 _ hlcode (lead_le hc0)
    refine hfin {lead c, tail c} ?_ fun H hL => ?_
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact ⟨hlcode, hlc⟩
      · exact ⟨htcode, htc⟩
    · exact Or.inr (Or.inl ⟨lead c, tail c, Finset.mem_insert_of_mem (hL (by simp)),
        Finset.mem_insert_of_mem (hL (by simp)), (lead_add_tail hc0).symm, hlc, htc⟩)

end Closure

/-- **Every finite set of codes below `K_ω` lies in a finite set of codes, closed under the parts.** -/
theorem aw_closure_fin {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om1) (s : Finset Ordinal.{0})
    (hs : ∀ c ∈ s, GxCl y (awAt S y) c ∧ c < awV S) :
    ∃ H : Finset Ordinal.{0}, s ⊆ H ∧ ∀ z ∈ H, (GxCl y (awAt S y) z ∧ z < awV S) ∧ AwStep S H z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert a s _ IH =>
    obtain ⟨H1, hs1, h1⟩ := IH fun c hc => hs c (Finset.mem_insert_of_mem hc)
    obtain ⟨hac, haV⟩ := hs a (Finset.mem_insert_self a s)
    obtain ⟨H2, ha2, h2⟩ := aw_closure hy hy1 a hac haV
    refine ⟨H1 ∪ H2, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact Finset.mem_union_right _ ha2
      · exact Finset.mem_union_left _ (hs1 hw)
    · exact aw_union h1 (fun z hz => ⟨⟨(h2 z hz).1.1, (h2 z hz).1.2.trans_lt haV⟩, (h2 z hz).2⟩)

/-! ## The base change below `θ` -/

/-- **Below `θ`: `mv ρ σ (R_ρ z) = R_σ z`.** -/
theorem aw_mv_xi {ρ σ z : Ordinal.{0}} (hρ : InE ρ) (hρ1 : ρ < Om1) (hσ : InE σ) (hσ1 : σ < Om1)
    (hzρ : WDom S ρ z) (hzσ : WDom S σ z) : mv ρ σ (xiR ρ z) = xiR σ z := by
  unfold mv
  rcases lt_trichotomy σ ρ with h | rfl | h
  · rw [if_pos h]; exact (xiR_pi hσ hρ h hρ1 z hzσ).2
  · rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]; rfl
  · rw [if_neg (not_lt.2 h.le), if_pos h]
    have hB : Bases ρ σ := ⟨hρ, hσ, h, hσ1⟩
    obtain ⟨h1, h2⟩ := xiR_pi hρ hσ h hσ1 z hzρ
    obtain ⟨h3, h4⟩ := up_spec hB (xiR_T S hρ hρ1 z hzρ).1
    exact (pi_bijOn hB).1.injOn h3 h1 (h4.trans h2.symm)

/-- A point below the next `υ`-point lies in the segment. -/
theorem aw_inSeg {x v m : Ordinal.{0}} (hxv : x ≤ v) (hvm : v < m) (hm1 : m < Om1) (hn : IsNext x m) : InSeg x v :=
  ⟨hxv, hvm.trans hm1, fun u hu hU => hvm.trans_le (hn.2.2 u hu hU)⟩

/-- The constant level `Ω₁`. -/
theorem aw_lev_Om1 {κ : Ordinal.{0}} (hκ : 0 < κ) : Xe.XeLev κ Om1 := by
  refine Or.inl (Uy.uyLev_of_uh ⟨?_, Rj.rj_Om1_lt_E, ?_⟩)
  · exact Order.one_le_iff_pos.2 Rj.rj_Om1_pos
  · rw [Rj.rjDat_Om1]; exact hκ

section Can

variable {κ ρ σ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} {F : Finset Ordinal.{0}}
  {Ψ : Ordinal.{0} → Ordinal.{0}}

/-- **THE FRAG MAP MOVES THE READINGS: `Ψ(Θ_ρ z) = Θ_σ z`.** -/
theorem aw_can (hρS : SC ρ) (hρ1 : ρ < Om1) (hσS : SC σ) (hσ1 : σ < Om1) (hκE : InE κ) (hκρ : κ < ρ) (hκσ : κ < σ)
    (hm : 2 ≤ m) (hb0 : b 0 = ρ) (hb1 : b 1 = awNx ρ) (hc0 : c 0 = σ) (hc1 : c 1 = awNx σ)
    (hΨ : XjFragConcl Xe.XeLev κ b c m F Ψ) {H : Finset Ordinal.{0}}
    (hH : ∀ z ∈ H, GxCl ρ (awAt S ρ) z ∧ GxCl σ (awAt S σ) z ∧ z < awV S ∧ AwStep S H z)
    (hW : ∀ z ∈ H, z < ConjT.th S → WDom S κ z)
    (hF : ∀ z ∈ H, gxTh ρ (awAt S ρ) z ∈ F) (hF' : ∀ z ∈ H, cdOff (gxTh ρ (awAt S ρ) z) ∈ F)
    (hxF : awNx ρ ∈ F) : ∀ z ∈ H, Ψ (gxTh ρ (awAt S ρ) z) = gxTh σ (awAt S σ) z := by
  obtain ⟨⟨hTr, hVl, -, hid⟩, hXj⟩ := hΨ
  obtain ⟨⟨⟨⟨-, -, Q3, Q4, -, -, -⟩, -⟩, -⟩, Q10⟩ := hTr
  have hκ1 : κ < Om1 := hκρ.trans hρ1
  have hOθ : Om1 < ConjT.th S := by rw [Rj.rj_Om1]; exact Vd.vd_Om1_lt_B.trans Vd.vd_B_lt_th
  have hAtρ : GxAt (awAt S ρ) := (awU S).gxAt ρ
  have hAtσ : GxAt (awAt S σ) := (awU S).gxAt σ
  have hρE : InE ρ := Low.opow_eq_self_of_SC hρS
  have hσE : InE σ := Low.opow_eq_self_of_SC hσS
  obtain ⟨hρx, -, hxS, hx1, -, -⟩ := awNx_facts hρS hρ1
  obtain ⟨hxm, -, hmS, hm1, hTm, hnx⟩ := awNx_facts hxS hx1
  obtain ⟨-, -, hx'S, hx'1, -, -⟩ := awNx_facts hσS hσ1
  have h01 : 0 < m := by omega
  have h11 : 1 < m := by omega
  have hTx : ∀ {z}, GxCl ρ (awAt S ρ) z →
      gxTh ρ (awAt S ρ) z ∈ Tset (awNx ρ) ∧ gxTh ρ (awAt S ρ) z < Om1 ∧ gxTh ρ (awAt S ρ) z < awNx (awNx ρ) := by
    intro z hz
    have h1 := aw_Rd_lt (S := S) hρS hρ1 hz
    exact ⟨(hTm _ (h1.trans hm1)).2 h1, h1.trans hm1, h1⟩
  have hΨ0 : Ψ 0 = 0 := hid 0 hκE.pos
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzH
  obtain ⟨hzρ, hzσ, hzV, hst⟩ := hH z hzH
  rcases lt_or_ge z (Om 1) with hz1 | hz1
  · have hz1' : z < Om1 := by rw [Rj.rj_Om1]; exact hz1
    have hzk : z < κ := by
      rcases hW z hzH (hz1'.trans hOθ) with h | ⟨h, -, -⟩
      · exact h
      · exact absurd hz1' (not_lt.2 h)
    rw [gxTh_small (hzk.trans hκρ).le, gxTh_small (hzk.trans hκσ).le]
    exact hid z hzk
  have hseg : ∀ v, awNx ρ ≤ v → v < awNx (awNx ρ) → InSeg (b 1) v := fun v h1 h2 => by
    rw [hb1]; exact aw_inSeg h1 h2 hm1 hnx
  by_cases hθ : z ≤ ConjT.th S
  · -- `z ≤ θ`
    rcases hθ.lt_or_eq with hθ | rfl
    · have hdκ : WDom S κ z := hW z hzH hθ
      have hdρ : WDom S ρ z := wDom_mono hκρ.le hdκ
      have hdσ : WDom S σ z := wDom_mono hκσ.le hdκ
      have e1 := aw_Rd_xi (S := S) hρS hρ1 hdρ
      rw [e1, aw_Rd_xi (S := S) hσS hσ1 hdσ]
      have hz1' : (Om1 : Ordinal.{0}) ≤ z := by rw [Rj.rj_Om1]; exact hz1
      have hFz : xiR ρ z ∈ F := e1 ▸ hF z hzH
      obtain ⟨hRT, hR1⟩ := xiR_T S hρE hρ1 z hdρ
      obtain ⟨-, -, -, -, hTρ, hnρ⟩ := awNx_facts hρS hρ1
      have hs0 : InSeg (b 0) (xiR ρ z) := by
        rw [hb0]
        exact aw_inSeg (xi_le_val hρE hρ1 hdρ hz1') ((hTρ _ hR1).1 hRT) hx1 hnρ
      have hTB : xiR ρ z ∈ TB (b 0) κ := by
        rw [hb0]; exact (xiR_TB S hρE hρ1 z hdρ κ hκE hκρ.le).2 hdκ
      rw [Q10 0 h01 _ hFz hs0 hTB, hb0, hc0]
      exact aw_mv_xi hρE hρ1 hσE hσ1 hdρ hdσ
    · rw [aw_Rd_th hρS hρ1, aw_Rd_th hσS hσ1, ← hb1, ← hc1]
      exact Q3 1 h11 (by rw [hb1]; exact hxF)
  have hθz : ConjT.th S < z := not_le.1 hθ
  rcases hst with hθ' | ⟨u, v, hu, hv, e, hu1, hv1⟩ | ⟨a, ha, hs, e, hE, hθa, ha1, hs1⟩ |
    ⟨a, d, ha, hd, hi, h1a, e, ha1, hd1, hi1, hEx⟩ | ⟨d, hd, hd0, e, hd1⟩
  · exact absurd hθ' hθ
  · -- a sum
    obtain ⟨huρ, huσ, -, -⟩ := hH u hu
    have e1 : gxTh ρ (awAt S ρ) z = gxTh ρ (awAt S ρ) u + gxTh ρ (awAt S ρ) v := by
      rw [e]; exact gxTh_add hρS hAtρ huρ v
    have e2 : gxTh σ (awAt S σ) z = gxTh σ (awAt S σ) u + gxTh σ (awAt S σ) v := by
      rw [e]; exact gxTh_add hσS hAtσ huσ v
    have h3 := (Q4.2.2 _ (hF u hu) _ (hF v hv) _ (hF z hzH)).1 e1.symm
    rw [e2, ← IH u hu1 hu, ← IH v hv1 hv]
    exact h3.symm
  · -- `ω^a`
    obtain ⟨haρ, haσ, -, -⟩ := hH a ha
    obtain ⟨hsρ, -, -, -⟩ := hH _ hs
    obtain ⟨-, -, e1⟩ := aw_Rd_opow (S := S) hρS hρ1 haρ hθa hE
    obtain ⟨-, -, e2⟩ := aw_Rd_opow (S := S) hσS hσ1 haσ hθa hE
    rw [← e] at e1 e2
    obtain ⟨hwT, hw1, -⟩ := hTx hsρ
    set w := gxTh ρ (awAt S ρ) (awS0 S a) with hw
    have hxz : awNx ρ ≤ gxTh ρ (awAt S ρ) z := by
      rw [← aw_Rd_th (S := S) hρS hρ1]; exact gxTh_mono hθz.le
    have hzm := (hTx hzρ).2.2
    have hval : UnT.ev (b 1) (UnT.th1 (UnT.par w) : UnC) = gxTh ρ (awAt S ρ) z := by
      rw [e1, hb1]; rfl
    have hc := hVl 1 h11 (UnT.th1 (UnT.par w)) trivial ⟨trivial, hw1⟩ (hF _ hs) trivial
      (by rw [hb1]; exact hwT) trivial (by rw [hval]; exact hF z hzH)
      (by rw [hval]; exact hseg _ hxz hzm)
    rw [hval] at hc
    rw [hc.1, e2, hc1]
    show vt (awNx σ) (1 + Ψ w) = _
    rw [hw, IH _ hs1 hs]
  · -- `φ(a, d)`
    obtain ⟨haρ, haσ, -, -⟩ := hH a ha
    obtain ⟨hdρ, hdσ, -, -⟩ := hH d hd
    obtain ⟨hiρ, -, -, -⟩ := hH _ hi
    have hab : a < veblen a d := by rw [← e]; exact ha1
    have hdb : d < veblen a d := by rw [← e]; exact hd1
    have hθφ : ConjT.th S < veblen a d := by rw [← e]; exact hθz
    have e1 := aw_Rd_phi (S := S) hρS hρ1 haρ hdρ h1a hab hdb hθφ
    have e2 := aw_Rd_phi (S := S) hσS hσ1 haσ hdσ h1a hab hdb hθφ
    rw [← e] at e1 e2
    obtain ⟨huT, hu1, -⟩ := hTx haρ
    obtain ⟨hiT, hi1', -⟩ := hTx hiρ
    set u := gxTh ρ (awAt S ρ) a with hu
    set i := gxTh ρ (awAt S ρ) (qfInd a (ConjT.th S) d) with hidef
    have hu1' : 1 ≤ u := by
      have := gxTh_mono (Z := ρ) (At := awAt S ρ) h1a
      rwa [gxTh_small (Gg.gg_one_lt_of_SC hρS).le] at this
    have hxz : awNx ρ ≤ gxTh ρ (awAt S ρ) z := by
      rw [← aw_Rd_th (S := S) hρS hρ1]; exact gxTh_mono hθz.le
    have hzm := (hTx hzρ).2.2
    have hxE : InE (awNx ρ) := Low.opow_eq_self_of_SC hxS
    obtain ⟨f1, -, -, -, -, -, -, f2⟩ := ul_facts hxE hx1 hu1' huT hu1 hiT hi1'
    obtain ⟨g1, -⟩ := ul_facts hxE hx1 hu1' huT hu1 (mem_T_of_le hxE hx1 zero_le) (hxE.pos.trans hx1)
    rw [add_zero] at g1
    have hval : UnT.ev (b 1) (UnT.thc u (UnT.par i) : UnC) = gxTh ρ (awAt S ρ) z := by
      rw [e1, hb1]; rfl
    have hExF : ZkEx (fun x => x ∈ F ∨ x < κ) u := by
      refine aw_zkEx_Rd hρS a haρ (zkEx_mono (fun x hx => Or.inl (hF x hx.1)) a hEx)
    have hExT : ZkEx (· ∈ Tset (awNx ρ)) u := by
      refine aw_zkEx_Rd hρS a haρ (zkEx_mono (fun x hx => ?_) a hEx)
      exact (hTx (hH x hx.1).1).1
    have hLF := aw_vcLv_mul (P := fun x => x ∈ F ∨ x < κ) (Or.inr hκE.pos) u hu1 hExF
    have hLT := aw_vcLv_mul (P := (· ∈ Tset (awNx ρ)))
      (mem_T_of_le (Low.opow_eq_self_of_SC hxS) hx1 zero_le) u hu1 hExT
    have hc := hVl 1 h11 (UnT.thc u (UnT.par i))
      (by
        rw [hb1]
        exact ⟨⟨hu1', zk_Om1_mul_lt_B hu1, g1, f1, f2⟩, trivial⟩)
      ⟨trivial, hi1'⟩ (hF _ hi) ⟨hLF, trivial⟩ (by rw [hb1]; exact hiT) (by rw [hb1]; exact ⟨hLT, trivial⟩)
      (by rw [hval]; exact hF z hzH) (by rw [hval]; exact hseg _ hxz hzm)
    rw [hval] at hc
    rw [hc.1, e2, hc1]
    show vt (awNx σ) (Om1 * vq Ψ u + Ψ i) = _
    have hvq : vq Ψ u = gxTh σ (awAt S σ) a := by
      unfold vq
      rw [zk_vcSub_mul Ψ hΨ0 u hu1, Ordinal.mul_div_cancel _ Rj.rj_Om1_pos.ne']
      refine aw_zkCnf hρS hσS a haρ haσ (zkEx_mono (fun x hx => ?_) a hEx)
      exact IH x hx.2 hx.1
    rw [hvq, hidef, IH _ hi1 hi]
  · -- an atom
    obtain ⟨hdρ, hdσ, -, -⟩ := hH d hd
    have hzAt : z ∈ awAt S ρ := by
      rw [e]; exact aw_atom_mem hdρ (e ▸ hzV)
    have hzAt' : z ∈ awAt S σ := by
      rw [e]; exact aw_atom_mem hdσ (e ▸ hzV)
    have e1 := (aw_read (S := S) hρS hρ1 z hzAt).2 d e hd0 hdρ
    have e2 := (aw_read (S := S) hσS hσ1 z hzAt').2 d e hd0 hdσ
    set w := gxTh ρ (awAt S ρ) d with hw
    obtain ⟨hwT, hw1, hwm⟩ := hTx hdρ
    have hηm : cdOff w < awNx (awNx ρ) := (cdOff_le w).trans_lt hwm
    have hηT : cdOff w ∈ Tset (awNx ρ) := (hTm _ (hηm.trans hm1)).2 hηm
    have hval : vt (b 1) (Om1 * Om1 + UnT.ev (b 1) (UnT.par (cdOff w) : UnC)) = gxTh ρ (awAt S ρ) z := by
      rw [e1, hb1]; rfl
    have hxz : awNx ρ ≤ gxTh ρ (awAt S ρ) z := by
      rw [← aw_Rd_th (S := S) hρS hρ1]; exact gxTh_mono hθz.le
    have hc := hXj 1 h11 Om1 (UnT.par (cdOff w)) (aw_lev_Om1 hκE.pos) trivial trivial
      (hηm.trans hm1) (hF' d hd) trivial (by rw [hb1]; exact hηT) trivial
      (by rw [hval]; exact hF z hzH) (by rw [hval]; exact hseg _ hxz (hTx hzρ).2.2)
    rw [hval] at hc
    rw [hc.1, e2, hc1]
    show vt (awNx σ) (Om1 * Om1 + Ψ (cdOff w)) = _
    unfold awG
    have hΨw : Ψ w = gxTh σ (awAt S σ) d := IH d hd1 hd
    congr 2
    rcases lt_or_ge w ω with hwω | hwω
    · have hωκ : ω < κ := omega0_lt_inE hκE
      have hη : cdOff w < κ := ((cdOff_le w).trans_lt hwω).trans hωκ
      rw [hid _ hη, ← hΨw, hid _ (hwω.trans hωκ)]
    · have hω' : ω ≤ gxTh σ (awAt S σ) d := by
        have hdω : ω ≤ d := by
          by_contra hlt
          push Not at hlt
          have h1 : d < ρ := hlt.trans (omega0_lt_inE hρE)
          rw [hw, gxTh_small h1.le] at hwω
          exact absurd hwω (not_le.2 hlt)
        have h2 := gxTh_mono (Z := σ) (At := awAt S σ) hdω
        rwa [gxTh_small (omega0_lt_inE hσE).le] at h2
      rw [Cp.cpOff_of_ge hwω, Cp.cpOff_of_ge hω', hΨw]

end Can

end Googology.Trans.PoR.InaccPsi.R2.Aw
