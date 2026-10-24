import Googology.Trans.PoR.InaccPsi.R2.GmG0

/-!
# THE CODES BELOW `Γ_{Ω₁+1}·ω` AS A READING SYSTEM PAST `Γ_{Ω₁+1}`: THE CODE `Γ_{Ω₁+1}` LOCATED

The codes `Γ_{Ω₁+1}·k + c'` (`R2.GmG0`) with the atoms `Γ_{Ω₁+1+c}` (`c < Γ_{Ω₁+1}·ω`; the atom `Γ_{Ω₁+1}` itself is
a code, so the codes `≥ Γ_{Ω₁+1}` contain an atom) form a code system `mgCS : GmCS` (`R2.GmAt`), and with the reading
`mgR` and the last terms below a reading system `mgRS : GmRS` (`R2.GmRS`, offsets below `Γ_{x+2}`).  At the limit
codes `Γ_{Ω₁+1}·(j+1)` the logend is `Γ_{x+1} = lgG x` (Lemma IMG: `LgK.lgTopPkg`).  The generic results then give:

* `mg_noAt` (a code below every atom uses no atom), `mg_code_gate`, `mg_mem`, `mgB_mem`, `mg_count`, `mgCS`;
* `mgLD` (**the last term of every limit code in `(ε_{Ω₁+1}, Γ_{Ω₁+1}·ω)`**), `mgRS` (**THE READING SYSTEM**,
  cofinal codes `Γ_{Ω₁+1}·(k+1)`, gate `0`);
* `mg_spec` (**the gated layer of every code `c = Γ_{Ω₁+1}·k + c'`**: top `ϑˣ(Ω₁·Ω₁ + Γ_{x+1}·k + c'(x))`),
  `mg_loc` (**every such code with gate below `ε₀` located**: `Λ⁺ = ι(Γ_{Ω₁+1+c}·ω)`, `P(⋯) < L(0)`), `mg_G0_loc`
  (**THE CODE `Γ_{Ω₁+1}` (round 83 stopped there)**: `Λ⁺ = ι(Γ_{Γ_{Ω₁+1}}·ω)`);
* `mgW_sup` (**`sup = ι(Γ_{Γ_{Ω₁+1}·ω})`, `P(Γ_{Γ_{Ω₁+1}·ω}) < L(0)`**), `mgFam_blk` (**BLK^O and the exact reaches**),
  `mgFam_enum` (**ENUM-REACH**, fixed points included), `mgFam_capV` (**CapV**), `mgFam_road` (**THE ROAD**),
  `mg_fr_order` (past `ι(Γ_{Γ_{Ω₁+1}})` of `R2.GmSup`).

No new axiom.  New definitions: `mgCS`, `mgRS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The code system -/

/-- **A code below every atom uses no atom.** -/
theorem mg_noAt {Z m : Ordinal.{0}} {At : Set Ordinal.{0}} (hAt : ∀ s ∈ At, m ≤ s) {v : Ordinal.{0}}
    (hv : GxCl Z At v) : v < m → GxCl Z ∅ v := by
  induction hv with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | atom hs => exact fun h => absurd (h.trans_le (hAt _ hs)) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

theorem mg_G0_mul_cl {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (hZ : 0 < Z) (hG : gcG 0 ∈ At) :
    ∀ k : ℕ, GxCl Z At (gcG 0 * k)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero hZ
  | k + 1 => by rw [Nat.cast_succ, mul_add_one]; exact GxCl.add (mg_G0_mul_cl hZ hG k) (GxCl.atom hG)

/-- **The gate of a code over `Z` (with the atoms `Γ_{Ω₁+1+c''}`, `c'' < Γ_{Ω₁+1}·ω`, gate below `Z`) is below `Z`**:
`c = Γ_{Ω₁+1}·k + c'` with `c' = c − Γ_{Ω₁+1}·k` a code (`gxDec`), below every atom, so atom-free
(`mg_noAt`), and `Gl.gl_code_gate`. -/
theorem mg_code_gate {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z) (hZa : ∀ u v, u < Z → v < Z → u + v < Z)
    (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z) {c : Ordinal.{0}}
    (hc : GxCl Z {s | ∃ c', c' < mgB ∧ mgG c' < Z ∧ s = gcG c'} c) (hcB : c < mgB) : mgG c < Z := by
  set At := {s | ∃ c', c' < mgB ∧ mgG c' < Z ∧ s = gcG c'} with hAtdef
  have hSC : SC Z := ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩
  have hGx : GxAt At := by
    rintro s ⟨c', -, -, rfl⟩
    exact ⟨gcG_SC c', gcG_Om1_lt c'⟩
  have hG0 : gcG 0 ∈ At := ⟨0, (lt_of_le_of_lt zero_le mg_G0_lt_B), by rw [mgG_zero]; exact hZ0, rfl⟩
  obtain ⟨k, c', hc', rfl⟩ := mg_split hcB
  rw [mgG_split k hc']
  have hk := mg_G0_mul_cl hZ0 hG0 k
  have hsub := (gxDec hSC hGx _ hc).1 _ hk le_self_add
  rw [Ordinal.add_sub_cancel] at hsub
  have hfree : GxCl Z ∅ c' := mg_noAt (m := gcG 0) (fun s hs => by
    obtain ⟨c'', -, -, rfl⟩ := hs; exact gcG_le zero_le) hsub hc'
  exact gl_code_gate le_rfl hZ1 hZ0 hZa hZp (fun s hs => absurd hs (Set.notMem_empty s)) gfE_lt_G0.le hfree hc'

theorem mg_G0_mul_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) : ∀ k : ℕ, gcG 0 * k ∈ S.CSet a b
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem _ _
  | k + 1 => by rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem (mg_G0_mul_mem ha k) (gmS_G0_mem S ha)

/-- **A code lies in every hull `Cl(a, b)` with `c < a` and its gate below `b`.** -/
theorem mg_mem {S : InaccSeq.{0}} {a b c : Ordinal.{0}} (hc : c < mgB) (hca : c < a) (hg : mgG c < b) :
    c ∈ S.CSet a b := by
  obtain ⟨k, c', hc', rfl⟩ := mg_split hc
  rw [mgG_split k hc'] at hg
  exact CSet.add_mem (mg_G0_mul_mem (lt_of_le_of_lt zero_le hca) k) (gl_mem c' hc' hg).1

theorem mgB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : mgB < a) : mgB ∈ S.CSet a b := by
  have e : mgB = veblen 0 (gcG 0 + 1) := by
    rw [veblen_zero_apply]; unfold mgB; rw [opow_add, opow_one, geG_E]
  rw [e]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (gmS_G0_mem S (lt_of_le_of_lt zero_le ha))
    (CSet.one_mem _ _))

/-- The codes below `c ≤ Γ_{Ω₁+1}·ω` with gate below a countable `y` are countably many. -/
theorem mg_count {c y : Ordinal.{0}} (hc : c ≤ mgB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // mgG b.1 < y} := by
  have hω : ω < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact omega_lt_Om1
  haveI := Gc.gc_countable hω
  haveI := gl_count (c := gcG 0) le_rfl hy hy1
  let f : {b : Iio c // mgG b.1 < y} → Iio ω × {b : Iio (gcG 0) // glG b.1 < y} := fun b =>
    (⟨b.1.1 / gcG 0, (Ordinal.div_lt mg_G0_ne).2 (lt_of_lt_of_le b.1.2 hc)⟩,
      ⟨⟨b.1.1 % gcG 0, Ordinal.mod_lt _ mg_G0_ne⟩, b.2⟩)
  have hinj : Function.Injective f := by
    intro b b' hbb
    have h1 : b.1.1 / gcG 0 = b'.1.1 / gcG 0 := congrArg (fun p => p.1.1) hbb
    have h2 : b.1.1 % gcG 0 = b'.1.1 % gcG 0 := congrArg (fun p => p.2.1.1) hbb
    have e : b.1.1 = b'.1.1 := by rw [← Ordinal.div_add_mod b.1.1 (gcG 0), h1, h2, Ordinal.div_add_mod]
    exact Subtype.ext (Subtype.ext e)
  exact hinj.countable

theorem mgB_V : mgB < gcG mgB := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : mgB < gcG 1 := InE.mul_lt hE (gcG_lt zero_lt_one) (omega0_lt_inE hE)
  exact h1.trans_le (gcG_le (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le mg_G0_lt_B)))

/-- **THE CODE SYSTEM below `Γ_{Ω₁+1}·ω`** (atoms `Γ_{Ω₁+1+c}`, the atom `Γ_{Ω₁+1}` among the codes). -/
noncomputable def mgCS : GmCS where
  B := mgB
  gt := mgG
  B_V := mgB_V
  gt_zero := mgG_zero
  gt_lt := fun c _ => mgG_lt_Om1 c
  gt_succ := fun b _ hZ _ hg => mgG_succ hZ b hg
  mem := fun _ _ _ _ hc hca hg => mg_mem hc hca hg
  B_mem := fun _ _ _ ha => mgB_mem ha
  code_gate := fun _ hZ1 hZ0 hZa hZp _ hc hcB => mg_code_gate hZ1 hZ0 hZa hZp hc hcB
  count := fun _ _ hc hy hy1 => mg_count hc hy hy1

/-! ## The last terms -/

theorem mg_lgG_dvd {x T : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hT : T ≤ lgG x) (j : ℕ) :
    ω ^ T ∣ lgG x * j := by
  have hE := (lgG_facts hx hx1).2.2.2.1
  have h1 : ω ^ T ∣ lgG x := by
    have := opow_dvd_opow ω hT
    rwa [hE] at this
  exact dvd_mul_of_dvd_left h1 _

/-- **The last term of every limit code `c ∈ (ε_{Ω₁+1}, Γ_{Ω₁+1}·ω)`**, with Lemma IMG for its logend: below
`Γ_{Ω₁+1}` the data of `Gl.gl_GiLD`; at `Γ_{Ω₁+1}·k + c'` (`c'` a limit) the last term of `c'` (`Gl.gl_ld`,
`Gl.glPkgG_of_ex`) after the prefix `Γ_{x+1}·k`; at `Γ_{Ω₁+1}·(j+1)` the logend `Γ_{x+1}` (`LgK.lgTopPkg`). -/
theorem mgLD (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < mgB) : Nonempty (GmLD mgCS mgR c) := by
  obtain ⟨k, c', hc', rfl⟩ := mg_split hc
  rcases k with _ | j
  · -- below `Γ_{Ω₁+1}`
    have e0 : gcG 0 * ((0 : ℕ) : Ordinal.{0}) + c' = c' := by simp
    rw [e0] at hl hEc ⊢
    obtain ⟨n, hn⟩ := glBn_cof hc'
    obtain ⟨L⟩ := gl_GiLD (glD n) c' hl hEc hn
    have hcp : L.cp < gcG 0 := L.cp_lt.trans hc'
    refine ⟨{
      cp := L.cp
      lp := L.lp
      cp_ge := L.cp_ge
      cp_lt := L.cp_lt
      cp_g := by show mgG L.cp ≤ mgG c'; rw [mgG_low hcp, mgG_low hc']; exact L.cp_g
      dec := fun x hx hx1 hg => by
        show mgR c' x = _ ∧ _
        have hg' : glG c' < x := by rw [← mgG_low hc']; exact hg
        rw [mgR_low hc', mgR_low hcp]
        exact L.dec x hx hx1 hg'
      pkg := fun ρ τ δ h hg => by
        show GhPkg (mgG c') ρ δ (fun y => lg (mgR c' y))
        have hg' : glG c' < ρ := by rw [← mgG_low hc']; exact hg
        rw [mgG_low hc']
        exact GhPkg.congr h (L.pkg ρ τ δ h hg') (fun y _ _ _ => by rw [mgR_low hc']) hg' }⟩
  · rcases Ordinal.zero_or_succ_or_isSuccLimit c' with h0 | ⟨d, hd⟩ | hlim
    · -- `c = Γ_{Ω₁+1}·(j+1)`: logend `Γ_{x+1}`
      subst h0
      have hR : ∀ x, InE x → x < Om1 → mgR (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + 0) x = lgG x * j + lgG x :=
        fun x _ _ => by rw [mgR_split (j + 1) gl_G0_E.pos x, glR_zero, add_zero, Nat.cast_succ, mul_add_one]
      have hgc : mgG (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + 0) = 0 := by
        rw [mgG_split (j + 1) gl_G0_E.pos, glG_zero]
      have hlg : ∀ x, InE x → x < Om1 → lg (mgR (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + 0) x) = lgG x := by
        intro x hx hx1
        have hE := (lgG_facts hx hx1).2.2.2.1
        have hd : lgG x * j + lgG x = lgG x * j + ω ^ lgG x := by rw [hE]
        rw [hR x hx hx1, hd]
        exact Ge.lg_add_opow (mg_lgG_dvd hx hx1 le_rfl j)
      have hpkg : ∀ ρ τ δ, RstK ρ τ δ → mgCS.gt (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + 0) < ρ →
          GhPkg (mgCS.gt (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + 0)) ρ δ
            (fun y => lg (mgR (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + 0) y)) := fun ρ τ δ h hg =>
        GhPkg.congr h (GhPkg.of_img (LgK.lgTopPkg h)) (fun y hyE hy1 _ => (hlg y hyE hy1).symm) hg
      rcases j with _ | i
      · refine ⟨{
          cp := gfE
          lp := fun _ => 0
          cp_ge := le_rfl
          cp_lt := ?_
          cp_g := by show mgG gfE ≤ _; rw [mgG_E]; exact zero_le
          dec := fun x hx hx1 _ => ?_
          pkg := hpkg }⟩
        · rw [add_zero, Nat.cast_succ, Nat.cast_zero, zero_add, mul_one]; exact gfE_lt_G0
        · have hE := (lgG_facts hx hx1).2.2.2.1
          refine ⟨?_, dvd_zero _, ?_, zero_le⟩
          · rw [hlg x hx hx1, hR x hx hx1, hE, Nat.cast_zero, mul_zero, zero_add]
          · rw [hlg x hx hx1]; exact (lgG_pos hx hx1).ne'
      · refine ⟨{
          cp := gcG 0 * ((i + 1 : ℕ) : Ordinal.{0}) + 0
          lp := fun x => lgG x * ((i + 1 : ℕ) : Ordinal.{0})
          cp_ge := ?_
          cp_lt := ?_
          cp_g := by
            show mgG _ ≤ mgG _
            rw [mgG_split (i + 1) gl_G0_E.pos, mgG_split (i + 1 + 1) gl_G0_E.pos]
          dec := fun x hx hx1 _ => ?_
          pkg := hpkg }⟩
        · rw [add_zero, Nat.cast_succ, mul_add_one]; exact gfE_lt_G0.le.trans le_add_self
        · rw [add_zero, add_zero]
          exact (mul_lt_mul_iff_right₀ gl_G0_E.pos).2 (by exact_mod_cast Nat.lt_succ_self (i + 1))
        · have hE := (lgG_facts hx hx1).2.2.2.1
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hlg x hx hx1, hR x hx hx1, hE]
          · rw [hlg x hx hx1]
            exact mg_lgG_dvd hx hx1 le_rfl (i + 1)
          · rw [hlg x hx hx1]; exact (lgG_pos hx hx1).ne'
          · rw [mgR_split (i + 1) gl_G0_E.pos x, glR_zero, add_zero]
    · -- a successor: not a limit
      exfalso
      subst hd
      have hlt : gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + d < gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + Order.succ d :=
        (add_lt_add_iff_left _).2 (Order.lt_succ d)
      have := hl.add_one_lt hlt
      rw [Order.succ_eq_add_one, ← add_assoc] at this
      exact lt_irrefl _ this
    · -- `c' > 0` a limit: the last term of `c'`
      obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := gl_ld c' hlim hc'
      have hcpG : cp < gcG 0 := hcp.trans hc'
      have hgc : mgG (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + c') = glG c' := mgG_split (j + 1) hc'
      have hTl : ∀ x, InE x → x < Om1 → glG c' < x → T x < lgG x := fun x hx hx1 hg => by
        obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
        have h1 : T x ≤ glR c' x := by rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
        exact h1.trans_lt (glR_lt_G hx hx1 hc' hg)
      have hdv : ∀ x, InE x → x < Om1 → glG c' < x →
          ω ^ T x ∣ lgG x * ((j + 1 : ℕ) : Ordinal.{0}) + lp x := fun x hx hx1 hg => by
        obtain ⟨-, e2, -, -⟩ := hdec x hx hx1 hg
        exact dvd_add (mg_lgG_dvd hx hx1 (hTl x hx hx1 hg).le (j + 1)) e2
      have hR : ∀ x, InE x → x < Om1 → glG c' < x → mgR (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + c') x =
          (lgG x * ((j + 1 : ℕ) : Ordinal.{0}) + lp x) + ω ^ T x := fun x hx hx1 hg => by
        obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
        rw [mgR_split (j + 1) hc' x, e1, add_assoc]
      have hlg : ∀ x, InE x → x < Om1 → glG c' < x →
          lg (mgR (gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + c') x) = T x := fun x hx hx1 hg => by
        rw [hR x hx hx1 hg]; exact Ge.lg_add_opow (hdv x hx hx1 hg)
      refine ⟨{
        cp := gcG 0 * ((j + 1 : ℕ) : Ordinal.{0}) + cp
        lp := fun x => lgG x * ((j + 1 : ℕ) : Ordinal.{0}) + lp x
        cp_ge := ?_
        cp_lt := (add_lt_add_iff_left _).2 hcp
        cp_g := by show mgG _ ≤ mgG _; rw [mgG_split (j + 1) hcpG, hgc]; exact hgcp
        dec := fun x hx hx1 hg => ?_
        pkg := fun ρ τ δ h hg => ?_ }⟩
      · rw [Nat.cast_succ, mul_add_one]; exact gfE_lt_G0.le.trans (le_add_self.trans le_self_add)
      · have hg' : glG c' < x := by rw [← hgc]; exact hg
        obtain ⟨-, -, e3, e4⟩ := hdec x hx hx1 hg'
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hlg x hx hx1 hg']; exact hR x hx hx1 hg'
        · rw [hlg x hx hx1 hg']; exact hdv x hx hx1 hg'
        · rw [hlg x hx hx1 hg']; exact e3
        · rw [mgR_split (j + 1) hcpG x]; exact add_le_add_right e4 _
      · have hg' : glG c' < ρ := by rw [← hgc]; exact hg
        have hρE := upsPt_inE h.ρU
        have hP := glPkgG_of_ex h (C := ∅) hg' (by simp) (hTl ρ hρE h.ρ1 hg')
          (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
        show GhPkg (mgG _) ρ δ _
        rw [hgc]
        exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg'

end Googology.Trans.PoR.InaccPsi.R2.Gm
