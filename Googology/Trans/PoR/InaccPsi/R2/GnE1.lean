import Googology.Trans.PoR.InaccPsi.R2.GnE0

/-!
# THE CODES `ε_{Γ_{Ω₁+1}+1}·k + c'`: Lemma IMG at `ε_{Γ_{ρ+1}+1}`, the code system, the last terms

* `gnI_eNG` (**Lemma IMG in `π`-form for the value `ε_{Γ_{ρ+1}+1}`**: its copy is an `ε`-number (the source atom
  `E ≤₁ E·2`) above the copy of `Γ_{ρ+1}`), `gnImg_G1` (**Lemma IMG for every value below `ε_{ε_{Γ_{ρ+1}+1}+1}`**,
  by `gnImg_of_eps`), `gn_pkg_eNG` (**Lemma IMG (gated) for `y ↦ ε_{Γ_{y+1}+1}`**);
* `ne_restrict`, `ne_code_gate` (**a code below `ε_{G+1}·ω` over `Z` has its gate below `Z`**: `c = ε_{G+1}·k + c'`,
  `c' = c − ε_{G+1}·k` a code (`gxDec`) below `Γ_{Ω₁+2}`, so its only atom is `Γ_{Ω₁+1}`, and `gn_code_gate`),
  `ne_mem`, `neB_mem`, `ne_count`, `neB_V`, `neCS` (**THE CODE SYSTEM below `ε_{G+1}·ω`**);
* `neLD` (**the last term of every limit code in `(ε_{Ω₁+1}, ε_{G+1}·ω)`**, with Lemma IMG for its logend: below
  `ε_{G+1}` the data `gnLD`; at `ε_{G+1}·(j+1)` the logend `ε_{Γ_{x+1}+1}` (`gn_pkg_eNG`); at `ε_{G+1}·(j+1) + c'`,
  `c'` a limit, the last term of `c'`).

No new axiom.  New definition: `neCS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gn

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Lemma IMG at `ε_{Γ_{ρ+1}+1}` -/

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Lemma IMG in `π`-form for the value `ε_{Γ_{ρ+1}+1}`.** -/
theorem gnI_eNG : GnI ρ δ (eN (lgG ρ)) := by
  classical
  have hρE := h.ρE
  set E := eN (lgG ρ) with hEdef
  have hE : InE E := eN_E _
  obtain ⟨hGT, hρG, hG1, -, -⟩ := lgG_facts hρE h.ρ1
  have hET : E ∈ Tset ρ ∧ E < Om1 := gm1_T hρE h.ρ1 (gn_eNG_lt1 hρE h.ρ1)
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hEEδ : E + E < δ := (inE_indec h.δE).add_lt hEδ hEδ
  have hρE' : ρ < E := hρG.trans (lt_eN _)
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (gnI_G h)
  have w2 := w1.insW hρE'.le hEδ (Or.inl (inE_indec hE))
  have w3 := w2.insW (hρE'.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
  refine gnI_mk h w3 (by simp) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hW1 : ↑W1 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ1 : ↑Z1 ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
  obtain ⟨hGA, -, pG⟩ := b1 A f hW1 hZ1 C
  have hEA : E ∈ A := hW (by simp)
  have hEEA : E + E ∈ A := hW (by simp)
  have hB := h.img_bases C
  have hfGE : f (lgG ρ) < f E := C.mono hGA hEA (lt_eN _)
  have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρE' hEEδ.le) (lt_of_le_of_lt zero_le hfGE)
  rw [(gn_eNG_pi hB).2]
  rw [(mg_lgG_pi hB).2] at pG
  exact eN_le (lt_of_le_of_lt pG hfGE) hfE

/-- **Lemma IMG for every value below `ε_{ε_{Γ_{ρ+1}+1}+1}`.** -/
theorem gnImg_G1 : ∀ v, v < eN (eN (lgG ρ)) → GnI ρ δ v := by
  have hρE := h.ρE
  have hq := gm1_facts hρE h.ρ1
  have hle : eN (eN (lgG ρ)) ≤ gq 1 ρ := eN_le (gn_eNG_lt1 hρE h.ρ1) hq.2.2.2
  refine gnImg_of_eps h (fun v hv => gm1_T hρE h.ρ1 (hv.trans_le hle)) (fun e he _ heB _ => ?_)
  rcases lt_trichotomy e (lgG ρ) with hlt | rfl | hgt
  · exact gnI_lowG h hlt
  · exact gnI_G h
  · rcases lt_trichotomy e (eN (lgG ρ)) with h1 | rfl | h2
    · exact absurd (eN_le hgt he) (not_le.2 h1)
    · exact gnI_eNG h
    · exact absurd (eN_le h2 he) (not_le.2 heB)

/-- **Lemma IMG (gated) for `y ↦ ε_{Γ_{y+1}+1}`.** -/
theorem gn_pkg_eNG {g : Ordinal.{0}} (hgρ : g < ρ) : GhPkg g ρ δ (fun y => eN (lgG y)) :=
  gnPkg_of_GnI h (C := ∅) hgρ (by simp) (gnI_eNG h) (GjEx.of_bases fun _ _ hB _ => gn_eNG_pi hB)

end Img

/-! ## The code system -/

/-- A code below `m` uses only atoms below `m`. -/
theorem ne_restrict {Z m : Ordinal.{0}} {At : Set Ordinal.{0}} {v : Ordinal.{0}} (hv : GxCl Z At v) :
    v < m → GxCl Z {s | s ∈ At ∧ s < m} v := by
  induction hv with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs => exact fun h => GxCl.atom ⟨hs, h⟩
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

theorem ne_E1_cl {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (h1 : 1 < Z) (hG : gcG 0 ∈ At) : GxCl Z At gnB := by
  rw [gnB_eq]
  exact GxCl.phi (GxCl.small h1) (GxCl.add (GxCl.atom hG) (GxCl.small h1))

theorem ne_E1_mul_cl {Z : Ordinal.{0}} {At : Set Ordinal.{0}} (h1 : 1 < Z) (hG : gcG 0 ∈ At) :
    ∀ k : ℕ, GxCl Z At (gnB * k)
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact GxCl.zero (zero_lt_one.trans h1)
  | k + 1 => by rw [Nat.cast_succ, mul_add_one]; exact GxCl.add (ne_E1_mul_cl h1 hG k) (ne_E1_cl h1 hG)

/-- **The gate of a code over `Z` (atoms `Γ_{Ω₁+1+c''}`, `c'' < ε_{G+1}·ω`, gate below `Z`) is below `Z`.** -/
theorem ne_code_gate {Z : Ordinal.{0}} (hZ1 : Z ≤ Om1) (hZ0 : 0 < Z) (hZa : ∀ u v, u < Z → v < Z → u + v < Z)
    (hZp : ∀ u v, u < Z → v < Z → veblen u v < Z) {c : Ordinal.{0}}
    (hc : GxCl Z {s | ∃ c', c' < neB ∧ neG c' < Z ∧ s = gcG c'} c) (hcB : c < neB) : neG c < Z := by
  set At := {s | ∃ c', c' < neB ∧ neG c' < Z ∧ s = gcG c'} with hAtdef
  have hSC : SC Z := ⟨hZ0, fun u hu v hv => hZp u v hu hv⟩
  have hGx : GxAt At := by
    rintro s ⟨c', -, -, rfl⟩
    exact ⟨gcG_SC c', gcG_Om1_lt c'⟩
  have hG0 : gcG 0 ∈ At := ⟨0, (lt_of_le_of_lt zero_le ne_E1_lt_B), by rw [neG_zero]; exact hZ0, rfl⟩
  have h1Z : (1 : Ordinal.{0}) < Z := by
    have := hZp 0 0 hZ0 hZ0; rwa [veblen_zero_apply, opow_zero] at this
  obtain ⟨k, c', hc', rfl⟩ := ne_split hcB
  rw [neG_split k hc']
  have hk := ne_E1_mul_cl h1Z hG0 k
  have hsub := (gxDec hSC hGx _ hc).1 _ hk le_self_add
  rw [Ordinal.add_sub_cancel] at hsub
  have hres := ne_restrict hsub (hc'.trans gnB_lt_G1)
  have hmono : GxCl Z {s | ∃ c'', c'' < gnB ∧ gnG c'' < Z ∧ s = gcG c''} c' := by
    refine hres.mono le_rfl ?_
    rintro s ⟨⟨c'', -, -, rfl⟩, hs⟩
    have h0 : c'' = 0 := by
      by_contra h0
      exact absurd hs (not_lt.2 (gcG_le (Order.one_le_iff_ne_zero.2 h0)))
    subst h0
    exact ⟨0, gnB_E.pos, by rw [gnG_zero]; exact hZ0, rfl⟩
  exact gn_code_gate hZ1 hZ0 hZa hZp hmono hc'

theorem ne_E1_mul_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : 0 < a) (k : ℕ) : gnB * k ∈ S.CSet a b :=
  lg_cset_mul_nat (gnB_mem ha) k

/-- **A code lies in every hull `Cl(a, b)` with `c < a` and its gate below `b`.** -/
theorem ne_mem {S : InaccSeq.{0}} {a b c : Ordinal.{0}} (hc : c < neB) (hca : c < a) (hg : neG c < b) :
    c ∈ S.CSet a b := by
  obtain ⟨k, c', hc', rfl⟩ := ne_split hc
  rw [neG_split k hc'] at hg
  have ha : 0 < a := lt_of_le_of_lt zero_le hca
  exact CSet.add_mem (ne_E1_mul_mem ha k) (gn_mem ha c' hc' hg)

theorem neB_mem {S : InaccSeq.{0}} {a b : Ordinal.{0}} (ha : neB < a) : neB ∈ S.CSet a b := by
  have e : neB = veblen 0 (gnB + 1) := by rw [veblen_zero_apply, neB_eq]
  rw [e]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.add_mem (gnB_mem (lt_of_le_of_lt zero_le ha)) (CSet.one_mem _ _))

/-- The codes below `c ≤ ε_{G+1}·ω` with gate below a countable `y` are countably many. -/
theorem ne_count {c y : Ordinal.{0}} (hc : c ≤ neB) (hy : InE y) (hy1 : y < Om1) :
    Countable {b : Iio c // neG b.1 < y} := by
  have hω : ω < Om (1 : Ordinal.{0}) := by rw [← Br.Om1_eq]; exact omega_lt_Om1
  haveI := Gc.gc_countable hω
  haveI := gn_count (c := gnB) le_rfl hy hy1
  let f : {b : Iio c // neG b.1 < y} → Iio ω × {b : Iio gnB // gnG b.1 < y} := fun b =>
    (⟨b.1.1 / gnB, (Ordinal.div_lt gnB_ne).2 (lt_of_lt_of_le b.1.2 hc)⟩,
      ⟨⟨b.1.1 % gnB, Ordinal.mod_lt _ gnB_ne⟩, b.2⟩)
  have hinj : Function.Injective f := by
    intro b b' hbb
    have h1 : b.1.1 / gnB = b'.1.1 / gnB := congrArg (fun p => p.1.1) hbb
    have h2 : b.1.1 % gnB = b'.1.1 % gnB := congrArg (fun p => p.2.1.1) hbb
    have e : b.1.1 = b'.1.1 := by rw [← Ordinal.div_add_mod b.1.1 gnB, h1, h2, Ordinal.div_add_mod]
    exact Subtype.ext (Subtype.ext e)
  exact hinj.countable

theorem neB_V : neB < gcG neB := by
  have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
  have h1 : neB < gcG 1 := InE.mul_lt hE gnB_lt_G1 (omega0_lt_inE hE)
  exact h1.trans_le (gcG_le (Order.one_le_iff_pos.2 (lt_of_le_of_lt zero_le ne_E1_lt_B)))

/-- **THE CODE SYSTEM below `ε_{Γ_{Ω₁+1}+1}·ω`.** -/
noncomputable def neCS : GmCS where
  B := neB
  gt := neG
  B_V := neB_V
  gt_zero := neG_zero
  gt_lt := fun c _ => neG_lt_Om1 c
  gt_succ := fun b _ hZ _ hg => neG_succ hZ b hg
  mem := fun _ _ _ _ hc hca hg => ne_mem hc hca hg
  B_mem := fun _ _ _ ha => neB_mem ha
  code_gate := fun _ hZ1 hZ0 hZa hZp _ hc hcB => ne_code_gate hZ1 hZ0 hZa hZp hc hcB
  count := fun _ _ hc hy hy1 => ne_count hc hy hy1

/-! ## The last terms -/

theorem ne_eNG_dvd {x T : Ordinal.{0}} (hT : T ≤ eN (lgG x)) (j : ℕ) : ω ^ T ∣ eN (lgG x) * j := by
  have h1 : ω ^ T ∣ eN (lgG x) := by
    have := opow_dvd_opow ω hT
    rwa [show ω ^ eN (lgG x) = eN (lgG x) from eN_E _] at this
  exact dvd_mul_of_dvd_left h1 _

/-- **The last term of every limit code `c ∈ (ε_{Ω₁+1}, ε_{G+1}·ω)`**, with Lemma IMG for its logend. -/
theorem neLD (c : Ordinal.{0}) (hl : IsSuccLimit c) (hEc : gfE < c) (hc : c < neB) :
    Nonempty (GmLD neCS neR c) := by
  obtain ⟨k, c', hc', rfl⟩ := ne_split hc
  rcases k with _ | j
  · -- below `ε_{G+1}`
    have e0 : gnB * ((0 : ℕ) : Ordinal.{0}) + c' = c' := by simp
    rw [e0] at hl hEc ⊢
    obtain ⟨L⟩ := gnLD c' hl hEc hc'
    have hcp : L.cp < gnB := L.cp_lt.trans hc'
    refine ⟨{
      cp := L.cp
      lp := L.lp
      cp_ge := L.cp_ge
      cp_lt := L.cp_lt
      cp_g := by show neG L.cp ≤ neG c'; rw [neG_low hcp, neG_low hc']; exact L.cp_g
      dec := fun x hx hx1 hg => by
        show neR c' x = _ ∧ _
        have hg' : gnG c' < x := by rw [← neG_low hc']; exact hg
        rw [neR_low hc', neR_low hcp]
        exact L.dec x hx hx1 hg'
      pkg := fun ρ τ δ h hg => by
        show GhPkg (neG c') ρ δ (fun y => lg (neR c' y))
        have hg' : gnG c' < ρ := by rw [← neG_low hc']; exact hg
        rw [neG_low hc']
        exact GhPkg.congr h (L.pkg ρ τ δ h hg') (fun y _ _ _ => by rw [neR_low hc']) hg' }⟩
  · rcases Ordinal.zero_or_succ_or_isSuccLimit c' with h0 | ⟨d, hd⟩ | hlim
    · -- `c = ε_{G+1}·(j+1)`: logend `ε_{Γ_{x+1}+1}`
      subst h0
      have hR : ∀ x, neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + 0) x = eN (lgG x) * j + eN (lgG x) :=
        fun x => by rw [neR_split (j + 1) gnB_E.pos x, gnR_zero, add_zero, Nat.cast_succ, mul_add_one]
      have hlg : ∀ x, lg (neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + 0) x) = eN (lgG x) := by
        intro x
        have hd : eN (lgG x) * j + eN (lgG x) = eN (lgG x) * j + ω ^ eN (lgG x) := by
          rw [show ω ^ eN (lgG x) = eN (lgG x) from eN_E _]
        rw [hR x, hd]
        exact Ge.lg_add_opow (ne_eNG_dvd le_rfl j)
      have hpkg : ∀ ρ τ δ, RstK ρ τ δ → neCS.gt (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + 0) < ρ →
          GhPkg (neCS.gt (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + 0)) ρ δ
            (fun y => lg (neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + 0) y)) := fun ρ τ δ h hg =>
        GhPkg.congr h (gn_pkg_eNG h hg) (fun y _ _ _ => (hlg y).symm) hg
      rcases j with _ | i
      · refine ⟨{
          cp := gfE
          lp := fun _ => 0
          cp_ge := le_rfl
          cp_lt := ?_
          cp_g := by show neG gfE ≤ _; rw [neG_E]; exact zero_le
          dec := fun x hx hx1 _ => ?_
          pkg := hpkg }⟩
        · rw [add_zero, Nat.cast_succ, Nat.cast_zero, zero_add, mul_one]
          exact gfE_lt_G0.trans gn_G0_lt_B
        · refine ⟨?_, dvd_zero _, ?_, zero_le⟩
          · rw [hlg x, hR x, show ω ^ eN (lgG x) = eN (lgG x) from eN_E _, Nat.cast_zero, mul_zero, zero_add]
          · rw [hlg x]; exact (eN_E _).pos.ne'
      · refine ⟨{
          cp := gnB * ((i + 1 : ℕ) : Ordinal.{0}) + 0
          lp := fun x => eN (lgG x) * ((i + 1 : ℕ) : Ordinal.{0})
          cp_ge := ?_
          cp_lt := ?_
          cp_g := by
            show neG _ ≤ neG _
            rw [neG_split (i + 1) gnB_E.pos, neG_split (i + 1 + 1) gnB_E.pos]
          dec := fun x hx hx1 _ => ?_
          pkg := hpkg }⟩
        · rw [add_zero, Nat.cast_succ, mul_add_one]; exact (gfE_lt_G0.trans gn_G0_lt_B).le.trans le_add_self
        · rw [add_zero, add_zero]
          exact (mul_lt_mul_iff_right₀ gnB_E.pos).2 (by exact_mod_cast Nat.lt_succ_self (i + 1))
        · refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hlg x, hR x, show ω ^ eN (lgG x) = eN (lgG x) from eN_E _]
          · rw [hlg x]; exact ne_eNG_dvd le_rfl (i + 1)
          · rw [hlg x]; exact (eN_E _).pos.ne'
          · rw [neR_split (i + 1) gnB_E.pos x, gnR_zero, add_zero]
    · -- a successor: not a limit
      exfalso
      subst hd
      have hlt : gnB * ((j + 1 : ℕ) : Ordinal.{0}) + d < gnB * ((j + 1 : ℕ) : Ordinal.{0}) + Order.succ d :=
        (add_lt_add_iff_left _).2 (Order.lt_succ d)
      have := hl.add_one_lt hlt
      rw [Order.succ_eq_add_one, ← add_assoc] at this
      exact lt_irrefl _ this
    · -- `c' > 0` a limit: the last term of `c'`
      have hgc : neG (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + c') = gnG c' := neG_split (j + 1) hc'
      have hEG : gfE ≤ gnB * ((j + 1 : ℕ) : Ordinal.{0}) := by
        rw [Nat.cast_succ, mul_add_one]; exact (gfE_lt_G0.trans gn_G0_lt_B).le.trans le_add_self
      rcases lt_or_ge c' (gcG 0) with hc'G | hc'G
      · -- `c'` below `G`: `Gl.gl_ld`
        obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := gl_ld c' hlim hc'G
        have hcpG : cp < gcG 0 := hcp.trans hc'G
        have hgc' : ∀ y, gnG c' < y → glG c' < y := fun y h => by rw [← gnG_low hc'G]; exact h
        have hTl : ∀ x, InE x → x < Om1 → glG c' < x → T x < lgG x := fun x hx hx1 hg => by
          obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
          have h1 : T x ≤ glR c' x := by rw [e1]; exact (right_le_opow _ one_lt_omega0).trans le_add_self
          exact h1.trans_lt (glR_lt_G hx hx1 hc'G hg)
        have hdv : ∀ x, InE x → x < Om1 → glG c' < x →
            ω ^ T x ∣ eN (lgG x) * ((j + 1 : ℕ) : Ordinal.{0}) + lp x := fun x hx hx1 hg => by
          obtain ⟨-, e2, -, -⟩ := hdec x hx hx1 hg
          exact dvd_add (ne_eNG_dvd ((hTl x hx hx1 hg).le.trans (lt_eN _).le) (j + 1)) e2
        have hR : ∀ x, InE x → x < Om1 → glG c' < x → neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + c') x =
            (eN (lgG x) * ((j + 1 : ℕ) : Ordinal.{0}) + lp x) + ω ^ T x := fun x hx hx1 hg => by
          obtain ⟨e1, -, -, -⟩ := hdec x hx hx1 hg
          rw [neR_split (j + 1) hc' x, gnR_low hc'G, e1, add_assoc]
        have hlg : ∀ x, InE x → x < Om1 → glG c' < x →
            lg (neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + c') x) = T x := fun x hx hx1 hg => by
          rw [hR x hx hx1 hg]; exact Ge.lg_add_opow (hdv x hx hx1 hg)
        refine ⟨{
          cp := gnB * ((j + 1 : ℕ) : Ordinal.{0}) + cp
          lp := fun x => eN (lgG x) * ((j + 1 : ℕ) : Ordinal.{0}) + lp x
          cp_ge := hEG.trans le_self_add
          cp_lt := (add_lt_add_iff_left _).2 hcp
          cp_g := by
            show neG _ ≤ neG _
            rw [neG_split (j + 1) (hcpG.trans gn_G0_lt_B), hgc, gnG_low hcpG, gnG_low hc'G]; exact hgcp
          dec := fun x hx hx1 hg => ?_
          pkg := fun ρ τ δ h hg => ?_ }⟩
        · have hg' : glG c' < x := hgc' x (by rw [← hgc]; exact hg)
          obtain ⟨-, -, e3, e4⟩ := hdec x hx hx1 hg'
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hlg x hx hx1 hg']; exact hR x hx hx1 hg'
          · rw [hlg x hx hx1 hg']; exact hdv x hx hx1 hg'
          · rw [hlg x hx hx1 hg']; exact e3
          · rw [neR_split (j + 1) (hcpG.trans gn_G0_lt_B) x, gnR_low hcpG]; exact add_le_add_right e4 _
        · have hg' : glG c' < ρ := hgc' ρ (by rw [← hgc]; exact hg)
          have hρE := upsPt_inE h.ρU
          have hP := glPkgG_of_ex h (C := ∅) hg' (by simp) (hTl ρ hρE h.ρ1 hg')
            (Gj.GjEx.of_bases fun σ ρ' hB hgσ => hex σ ρ' hB hgσ)
          show GhPkg (neG _) ρ δ _
          rw [hgc, gnG_low hc'G]
          exact GhPkg.congr h hP (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg'
      · -- `c' ∈ [G, ε_{G+1})` a limit: `gnLD`
        obtain ⟨D⟩ := gnLD c' hlim (gfE_lt_G0.trans_le hc'G) hc'
        have hcpB : D.cp < gnB := D.cp_lt.trans hc'
        have hdv : ∀ x, InE x → x < Om1 → gnG c' < x →
            ω ^ lg (gnR c' x) ∣ eN (lgG x) * ((j + 1 : ℕ) : Ordinal.{0}) + D.lp x := fun x hx hx1 hg => by
          obtain ⟨-, e2, -, -⟩ := D.dec x hx hx1 hg
          have hlt : lg (gnR c' x) ≤ eN (lgG x) := by
            have h0 : gnR c' x ≠ 0 := (gnR_pos hx hx1 (gn_ne_of_le hc'G) hc' hg).ne'
            exact (lg_le h0).trans (gnR_lt_eNG hx hx1 hc' hg).le
          exact dvd_add (ne_eNG_dvd hlt (j + 1)) e2
        have hR : ∀ x, InE x → x < Om1 → gnG c' < x → neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + c') x =
            (eN (lgG x) * ((j + 1 : ℕ) : Ordinal.{0}) + D.lp x) + ω ^ lg (gnR c' x) := fun x hx hx1 hg => by
          obtain ⟨e1, -, -, -⟩ := D.dec x hx hx1 hg
          rw [neR_split (j + 1) hc' x, add_assoc, ← e1]
        have hlg : ∀ x, InE x → x < Om1 → gnG c' < x →
            lg (neR (gnB * ((j + 1 : ℕ) : Ordinal.{0}) + c') x) = lg (gnR c' x) := fun x hx hx1 hg => by
          rw [hR x hx hx1 hg]; exact Ge.lg_add_opow (hdv x hx hx1 hg)
        refine ⟨{
          cp := gnB * ((j + 1 : ℕ) : Ordinal.{0}) + D.cp
          lp := fun x => eN (lgG x) * ((j + 1 : ℕ) : Ordinal.{0}) + D.lp x
          cp_ge := hEG.trans le_self_add
          cp_lt := (add_lt_add_iff_left _).2 D.cp_lt
          cp_g := by
            show neG _ ≤ neG _
            rw [neG_split (j + 1) hcpB, hgc]; exact D.cp_g
          dec := fun x hx hx1 hg => ?_
          pkg := fun ρ τ δ h hg => ?_ }⟩
        · have hg' : gnG c' < x := by rw [← hgc]; exact hg
          obtain ⟨-, -, e3, e4⟩ := D.dec x hx hx1 hg'
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hlg x hx hx1 hg']; exact hR x hx hx1 hg'
          · rw [hlg x hx hx1 hg']; exact hdv x hx hx1 hg'
          · rw [hlg x hx hx1 hg']; exact e3
          · rw [neR_split (j + 1) hcpB x]; exact add_le_add_right e4 _
        · have hg' : gnG c' < ρ := by rw [← hgc]; exact hg
          show GhPkg (neG _) ρ δ _
          rw [hgc]
          exact GhPkg.congr h (D.pkg ρ τ δ h hg') (fun y hyE hy1 hgy => (hlg y hyE hy1 hgy).symm) hg'

end Googology.Trans.PoR.InaccPsi.R2.Gn
