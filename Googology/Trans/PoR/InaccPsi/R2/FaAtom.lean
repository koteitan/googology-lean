import Googology.Trans.PoR.InaccPsi.R2.FaCert

/-!
# Fa: `T` MOVES THE ATOMS ONE CARDINAL DOWN

`T = Kz.vbTK S λ K` on `D_K`, `W = Ω_{k+2}`, `V = Ω_{k+3}`, `W' = Ω_{k+1}`, `V' = Ω_{k+2}`, `Hˡ = Ul.ulH S (k+1)`,
`Hˡ' = Ul.ulH S k`, `k ≥ 1`.

* `fa_nota` (a member of `Cl(a, b)`, `b` below a collapse, is a closed term), `fa_arg`, `fa_coll` (**`ψ_π(e) ∈ D_K ⇔
  e ∈ D_K`, `e < A`** for own `e`), `fa_dig` (the digit of `M + W^γ·D` at `γ` is not `0`);
* `faGap` (**the largest `ψ_W`-value at or below the datum of a member of `D_K` is in `D_K`**);
* `fa_first_of` (`Vp.vp_first_of_cert` with the visibility in place of the datum and no notation hypothesis);
* `faFirst` (**`T(Hˡ_γ(0)) = Hˡ'_{T γ}(0)`**), `faAtom` (**`T(Hˡ_γ(y)) = Hˡ'_{T γ}(T y)`**, and `γ, y ∈ D_K`, `T γ < V'`,
  for `Hˡ_γ(y) ∈ D_K`, `γ < V`, `y < Hˡ_γ(y) < W`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Ru Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rx Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

/-- **A member of `Cl(a, b)` with `b` below a collapse is a closed term.** -/
theorem fa_nota {a b A x : Ordinal.{0}} (hb : b ≤ S.psi A (Om 1)) (hx : x ∈ S.CSet a b) : x ∈ ⋃ c, S.CSet c 0 := by
  induction hx with
  | small h => exact Bc.mem_of_lt_psi S (h.trans_le hb)
  | zero => exact mem_iUnion.2 ⟨0, CSet.zero_mem _ _⟩
  | inacc n => exact mem_iUnion.2 ⟨0, CSet.I_mem _ _ n⟩
  | inaccW => exact mem_iUnion.2 ⟨0, CSet.Iw_mem _ _⟩
  | add _ _ ihx ihy =>
    obtain ⟨c1, h1⟩ := mem_iUnion.1 ihx
    obtain ⟨c2, h2⟩ := mem_iUnion.1 ihy
    exact mem_iUnion.2 ⟨max c1 c2, CSet.add_mem (CSet_mono (le_max_left _ _) le_rfl h1)
      (CSet_mono (le_max_right _ _) le_rfl h2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨c1, h1⟩ := mem_iUnion.1 ihx
    obtain ⟨c2, h2⟩ := mem_iUnion.1 ihy
    exact mem_iUnion.2 ⟨max c1 c2, CSet.phi_mem (CSet_mono (le_max_left _ _) le_rfl h1)
      (CSet_mono (le_max_right _ _) le_rfl h2)⟩
  | om _ ih =>
    obtain ⟨c1, h1⟩ := mem_iUnion.1 ih
    exact mem_iUnion.2 ⟨c1, CSet.Om_mem h1⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨c1, h1⟩ := mem_iUnion.1 ihπ
    obtain ⟨c2, h2⟩ := mem_iUnion.1 ihe
    refine mem_iUnion.2 ⟨max (max c1 c2) (e.1 + 1), ?_⟩
    have hlt : e.1 < max (max c1 c2) (e.1 + 1) := (lt_add_one _).trans_le (le_max_right _ _)
    exact CSet.psi_mem hlt hπ (CSet_mono ((le_max_left _ _).trans (le_max_left _ _)) le_rfl h1)
      (CSet_mono ((le_max_right _ _).trans (le_max_left _ _)) le_rfl h2)

/-- **The digit of `M + W^γ·D` at `γ` is not `0`** (`0 < D < W`). -/
theorem fa_dig {r M γ D : Ordinal.{0}} (hD0 : D ≠ 0) (hD : D < Om (r + 1)) :
    (M + Om (r + 1) ^ γ * D) / Om (r + 1) ^ γ % Om (r + 1) ≠ 0 := by
  have hWγ : Om (r + 1) ^ γ ≠ 0 := (Ui.ui_W_pos r γ).ne'
  have hW0 : (Om (r + 1) : Ordinal.{0}) ≠ 0 := (Ui.ui_SC_W r).1.ne'
  have hI : Indec (Om (r + 1) ^ γ) := Vp.vp_Wg_indec r γ
  have habs : M % Om (r + 1) ^ γ + Om (r + 1) ^ γ * D = Om (r + 1) ^ γ * D := by
    obtain ⟨d, rfl⟩ : ∃ d, D = 1 + d := ⟨D - 1, (Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)).symm⟩
    rw [mul_add, mul_one, ← add_assoc, hI.add_eq (Ordinal.mod_lt M hWγ)]
  have e1 : M + Om (r + 1) ^ γ * D = Om (r + 1) ^ γ * (M / Om (r + 1) ^ γ + D) := by
    conv_lhs => rw [← Ordinal.div_add_mod M (Om (r + 1) ^ γ)]
    rw [add_assoc, habs, mul_add]
  rw [e1, Ordinal.mul_div_cancel _ hWγ]
  set m := M / Om (r + 1) ^ γ
  have e2 : m + D = Om (r + 1) * (m / Om (r + 1)) + (m % Om (r + 1) + D) := by
    conv_lhs => rw [← Ordinal.div_add_mod m (Om (r + 1))]
    rw [add_assoc]
  have hlt : m % Om (r + 1) + D < Om (r + 1) :=
    (Ui.ui_SC_W r).isPrincipal (Ordinal.mod_lt m hW0) hD
  rw [e2, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]
  exact (lt_of_lt_of_le (pos_iff_ne_zero.2 hD0) le_add_self).ne'

/-- **`Vp.vp_first_of_cert` with the visibility in place of the datum.** -/
theorem fa_first_of {s : Ordinal.{0}} (hs : s < ω) {γ B0 K : Ordinal.{0}} (hγ0 : γ ≠ 0)
    (hown : B0 ∈ S.CSet B0 (S.psi B0 (Om (s + 1)))) (hval : S.psi B0 (Om (s + 1)) ∈ range (ulH S s γ))
    (hB0K : B0 = K + Om (s + 1) ^ γ) (hownK : K ∈ S.CSet K (S.psi K (Om (s + 1))))
    (hK : K = 0 ∨ ¬ UlK S s (S.psi K (Om (s + 1))) γ ∨ S.psi K (Om (s + 1 + 1)) < γ ∨
      (S.psi K (Om (s + 1 + 1)) ≤ γ ∧ ¬ Om (s + 1) ^ γ ∣ K)) :
    ulH S s γ 0 = S.psi B0 (Om (s + 1)) := by
  have hκ : S.InR (Om (s + 1)) := InR_Om_succ s
  have hκV : S.InR (Om (s + 1 + 1)) := InR_Om_succ (s + 1)
  obtain ⟨o, ho⟩ := hval
  have hle : ulH S s γ 0 ≤ S.psi B0 (Om (s + 1)) := by rw [← ho]; exact (ulH_le_iff γ).2 zero_le
  have hlt1 : ulH S s γ 0 < S.psi (B0 + 1) (Om (s + 1)) := hle.trans_lt (Ui.ui_psi_lt_of_own hown (lt_add_one B0))
  obtain ⟨B, hownB, hB⟩ := Ui.ui_own_of_SC hs (ulH_SC γ 0) (ulH_gt γ 0) hlt1
  have hvB : ulH S s γ 0 = S.psi B (Om (s + 1)) := hB.symm
  suffices hB0B : B0 ≤ B by
    exact le_antisymm hle (by rw [hvB]; exact (psi_mono hκ hB0B).1)
  have hdvd : Om (s + 1) ^ γ ∣ B := Us.us_dvd_val hs hownB hvB
  have hγψ : γ ≤ S.psi B (Om (s + 1 + 1)) := Us.us_val_le hs hownB hvB
  rw [hB0K]
  have hKB : K < B := by
    rcases hK with hK0 | hKm | hKV | ⟨hKV, hKd⟩
    · rw [hK0]; exact pos_iff_ne_zero.2 (Vp.vp_B0_ne hs hγ0 hvB)
    · by_contra hc
      push Not at hc
      refine hKm ((ul_vis (Ui.ui_psi_SC (s := s) K)).1 ?_)
      have h1 : ulD S s γ < S.psi B (Om (s + 1)) := by rw [← hvB]; exact ulH_D_lt γ 0
      exact h1.trans_le (psi_mono hκ hc).1
    · by_contra hc
      push Not at hc
      exact absurd (((psi_mono hκV hc).1.trans_lt hKV).trans_le hγψ) (lt_irrefl _)
    · by_contra hc
      push Not at hc
      have he : S.psi B (Om (s + 1 + 1)) = S.psi K (Om (s + 1 + 1)) :=
        le_antisymm ((psi_mono hκV hc).1) (hKV.trans hγψ)
      have hBK := Ui.ui_own_unique (s := s + 1) (Vp.vp_ownV hownB) (Vp.vp_ownV hownK) he
      exact hKd (hBK ▸ hdvd)
  exact Vp.vp_add_le_of_dvd (Vp.vp_Wg_indec s γ) hdvd hKB

section Rst

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) {K : Ordinal.{0}} (hKB : KzB S K)

include hl hX in
/-- **`e ∈ D_K`, `e < A`, `e < K` for own `e` with `ψ_π(e) ∈ D_K`** (`π = Ω_{r+1}`, `r ≥ 1`). -/
theorem fa_arg {r e : Ordinal.{0}} (hr : Om (1 : Ordinal.{0}) ≤ Om r) (hz : VbDK S l K (S.psi e (Om (r + 1))))
    (hown : e ∈ S.CSet e (S.psi e (Om (r + 1)))) : VbDK S l K e ∧ e < ConjT.Aη S (cdEta S l) := by
  have hκ : S.InR (Om (r + 1)) := InR_Om_succ r
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hρ1 := (vbZ hl hX).2
  have hOr := (psiS_bounds (S := S) e r).1
  have hρx : upsilon l ≤ S.psi e (Om (r + 1)) := (hρ1.trans_le (hr.trans hOr.le)).le
  have hρL : upsilon l ≤ S.Lam :=
    (hρ1.trans (lt_Lam_of_mem zero_le (CSet.Om_mem (CSet.one_mem (S := S) 0 0)))).le
  have hθL : S.psi K (Om (1 + 1)) ≤ S.Lam :=
    ((psi_lt hκ2 _).trans (lt_Lam_of_mem zero_le (Mx.mxOm2_mem (S := S) 0 0))).le
  obtain ⟨h1, h2⟩ := arg_mem_of_psi_mem hκ hz.1 hρx hρL hown
  have hE : e ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧ e < K := by
    rcases le_or_gt (S.psi K (Om (1 + 1))) (S.psi e (Om (r + 1))) with hθ | hθ
    · exact arg_mem_of_psi_mem hκ hz.2.1 hθ hθL hown
    · have hr3 : r < 1 + 1 := Om_lt_Om.1 (hOr.trans (hθ.trans (psi_lt hκ2 _)))
      obtain rfl : r = 1 := le_antisymm (Order.lt_add_one_iff.1 hr3) (Om_le_Om.1 hr)
      have hdW : e < K := by
        by_contra hc; push Not at hc; exact absurd hθ (not_lt.2 (psi_mono hκ2 hc).1)
      exact ⟨CSet_mono hdW.le hθ.le hown, hdW⟩
  exact ⟨⟨h1, hE.1, hE.2⟩, h2⟩

/-- **`ψ_π(e) ∈ D_K`** for `e ∈ D_K`, `e < A`, `π = Ω_{j+1}`, `j` finite. -/
theorem fa_coll (hKB : KzB S K) {j : ℕ} {e : Ordinal.{0}} (he : VbDK S l K e) (heA : e < ConjT.Aη S (cdEta S l)) :
    VbDK S l K (S.psi e (Om ((j : Ordinal.{0}) + 1))) := by
  have hκ : S.InR (Om ((j : Ordinal.{0}) + 1)) := InR_Om_succ _
  have hOD := fa_Om1_D (S := S) (l := l) hKB j
  exact ⟨CSet.psi_mem heA hκ hOD.1 he.1, CSet.psi_mem he.2.2 hκ hOD.2.1 he.2.1,
    (psi_lt hκ e).trans hOD.2.2⟩

include hl hX hKB

theorem fa_T_one : vbTK S l K 1 = 1 := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have h := kzT_cnf hl hX hKB 1 le_rfl hPC.zero hPC.zero (opow_pos 0 omega0_pos)
  simpa [vbTK_zero hl hX hKB] using h

theorem fa_T_succ {γ : Ordinal.{0}} (hγ : VbDK S l K γ) : vbTK S l K (γ + 1) = vbTK S l K γ + 1 := by
  have hPC := faPC_D (S := S) (l := l) hKB
  rw [kzT_add hl hX hKB hγ hPC.one, fa_T_one hl hX hKB]

/-- **The largest `ψ_W`-value at or below the datum of a member of `D_K` is in `D_K`.** -/
theorem faGap {k : ℕ} {K₁ : Ordinal.{0}} (hown : K₁ ∈ S.CSet K₁ (S.psi K₁ (Om ((k : Ordinal.{0}) + 1 + 1)))) :
    ∀ x, VbDK S l K x → ¬ UlK S ((k : Ordinal.{0}) + 1) (S.psi K₁ (Om ((k : Ordinal.{0}) + 1 + 1))) x →
      UlK S ((k : Ordinal.{0}) + 1) (S.psi (K₁ + 1) (Om ((k : Ordinal.{0}) + 1 + 1))) x →
      VbDK S l K (S.psi K₁ (Om ((k : Ordinal.{0}) + 1 + 1))) := by
  obtain ⟨hZ, hZ1⟩ := vbZ hl hX
  have hsk1 := fa_nat1_lt k
  set q := S.psi K₁ (Om ((k : Ordinal.{0}) + 1 + 1)) with hqdef
  set q2 := S.psi (K₁ + 1) (Om ((k : Ordinal.{0}) + 1 + 1)) with hq2def
  have hqS : SC q := Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) K₁
  have hq2S : SC q2 := Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) (K₁ + 1)
  have h1 : Om ((k : Ordinal.{0}) + 1) < q := Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) K₁
  have h1' : Om ((k : Ordinal.{0}) + 1) < q2 := Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) (K₁ + 1)
  have hq2W : q2 < Om ((k : Ordinal.{0}) + 1 + 1) := Ui.ui_psi_lt (s := (k : Ordinal.{0}) + 1) _
  have h10 : Om (1 : Ordinal.{0}) < q := (Om_le_Om.2 le_add_self).trans_lt h1
  have hq2L : q2 ≤ S.Lam :=
    (hq2W.trans ((fa_Om2_D (S := S) (l := l) hKB k).2.2.trans (kzK_lt_Lam hKB))).le
  refine rxMs_ind (S := S) (T := upsilon l) fun x IH hx hN hY => ?_
  have hxE : RxEK S (upsilon l) K x := vbDK_E hl hX hx
  by_cases hxq : x < q
  · exact absurd (UlK.small hxq) hN
  have hqx : q ≤ x := not_lt.1 hxq
  have hx1 : Om 1 < x := h10.trans_le hqx
  have h0 : x ≠ 0 := ((Om_pos one_ne_zero).trans hx1).ne'
  by_cases hΩ : ∃ j : ℕ, x = Om (j : Ordinal.{0})
  · obtain ⟨j, rfl⟩ := hΩ
    exact absurd (UlK.om (UlK.nat j)) hN
  by_cases hxW : x = Om ω
  · subst hxW
    have hω : UlK S ((k : Ordinal.{0}) + 1) q (ω : Ordinal.{0}) := by
      have := UlK.opow (UlK.one (S := S) (s := (k : Ordinal.{0}) + 1) (q := q)); rwa [opow_one] at this
    exact absurd (UlK.om hω) hN
  by_cases hSx : SC x
  · obtain ⟨j, hj, d, hdE, hdn, rfl, hst⟩ := kzE_atom hKB hZ1.le hxE hSx hx1 (kzNe hKB hxE hΩ hxW)
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hdD : VbDK S l K d := vbDK_atom hl hX hx hdE hdn hj
    have hms := rxMs_lt_stage (kzE_lt_Lam hKB hdE) hst
    rw [Nat.cast_succ] at hdn hx hqx hxq hx1 h0 hxE hms hN hY
    have hπ : S.InR (Om ((j' : Ordinal.{0}) + 1 + 1)) := InR_Om_succ _
    rcases lt_trichotomy j' k with hlt | heq | hgt
    · exfalso
      have hle : Om ((j' : Ordinal.{0}) + 1 + 1) ≤ Om ((k : Ordinal.{0}) + 1) := by
        refine Om_le_Om.2 ?_
        have : j' + 1 ≤ k := hlt
        have h' : ((j' + 1 : ℕ) : Ordinal.{0}) ≤ k := by exact_mod_cast this
        rw [Nat.cast_succ] at h'
        exact add_le_add h' le_rfl
      exact hxq (((psiS_bounds (S := S) d ((j' : Ordinal.{0}) + 1)).2.trans_le hle).trans h1)
    · subst heq
      have hlt2 := ulK_lt_W hsk1 hq2S h1' hY (psiS_bounds (S := S) d ((j' : Ordinal.{0}) + 1)).2
      have e := Vs.vs_gap_eq (s := (j' : Ordinal.{0})) (natCast_lt_omega0 j') hown hSx hqx hlt2
      have e' : q = S.psi d (Om ((j' : Ordinal.{0}) + 1 + 1)) := e.symm
      rw [e']; exact hx
    · have hne1 : Om ((j' : Ordinal.{0}) + 1 + 1) ≠ Om ((k : Ordinal.{0}) + 1 + 1) := by
        intro e
        have e1 : (j' : Ordinal.{0}) + 1 + 1 = (k : Ordinal.{0}) + 1 + 1 :=
          le_antisymm (Om_le_Om.1 e.le) (Om_le_Om.1 e.ge)
        have e3 : ((j' + 1 + 1 : ℕ) : Ordinal.{0}) = ((k + 1 + 1 : ℕ) : Ordinal.{0}) := by push_cast; exact e1
        have e4 := Nat.cast_inj.1 e3
        omega
      have hOm2 : UlK S ((k : Ordinal.{0}) + 1) q (Om ((j' : Ordinal.{0}) + 1 + 1)) := by
        have := UlK.nat (S := S) (s := (k : Ordinal.{0}) + 1) (q := q) (j' + 1 + 1)
        push_cast at this
        exact UlK.om this
      have hWx : q2 ≤ S.psi d (Om ((j' : Ordinal.{0}) + 1 + 1)) := by
        refine hq2W.le.trans (((Om_le_Om.2 ?_).trans (psiS_bounds (S := S) d ((j' : Ordinal.{0}) + 1)).1.le))
        have : k + 1 ≤ j' := hgt
        have h' : ((k + 1 : ℕ) : Ordinal.{0}) ≤ j' := by exact_mod_cast this
        rw [Nat.cast_succ] at h'
        exact add_le_add h' le_rfl
      have hNd : ¬ UlK S ((k : Ordinal.{0}) + 1) q d := fun h => hN (UlK.coll hπ hne1 hOm2 h)
      have hYd := Uo.uoArg hq2L hπ hdn hY hWx
      exact IH d hms hdD hNd hYd
  by_cases hε : ω ^ x = x
  · obtain ⟨hv, ha0, ha, hb⟩ := rxVeb hx1 hε hSx
    obtain ⟨haD, hbD, -, -, hha, hhb⟩ := vbDK_veb hx hxE hv hb
    have hY' : UlK S ((k : Ordinal.{0}) + 1) q2 (veblen (invVeblen₁ x) (invVeblen₂ x)) := by rw [hv]; exact hY
    obtain ⟨h3, h4⟩ := Qt.ulK_veb_parts hY' (by rw [hv]; exact ha) (by rw [hv]; exact hb)
    by_cases hA : UlK S ((k : Ordinal.{0}) + 1) q (invVeblen₁ x)
    · have hB : ¬ UlK S ((k : Ordinal.{0}) + 1) q (invVeblen₂ x) := fun h => hN (by
        have := UlK.phi hA h; rwa [hv] at this)
      exact IH _ (rxMs_lt_val hhb hb) hbD hB h4
    · exact IH _ (rxMs_lt_val hha ha) haD hA h3
  -- the Cantor normal form
  have hlx : log ω x < x := ruLog_lt hx1 hε
  obtain ⟨hlD, -, hlh⟩ := vbDK_log hx hxE
  obtain ⟨hrD, -, hrh⟩ := vbDK_rem hx hxE
  obtain ⟨n, hdec, h3, h4, -⟩ := ulK_split hq2S hY h0
  by_cases hA : UlK S ((k : Ordinal.{0}) + 1) q (log ω x)
  · have hB : ¬ UlK S ((k : Ordinal.{0}) + 1) q (x % ω ^ log ω x) := fun h => hN (by
      have := UlK.add ((UlK.opow hA).mul_nat n) h; rwa [hdec] at this)
    exact IH _ (rxMs_lt_val hrh (mod_opow_log_lt_self ω h0)) hrD hB h4
  · exact IH _ (rxMs_lt_val hlh hlx) hlD hA h3

theorem fa_T_psiV {k : ℕ} (hk : 1 ≤ k) {d : Ordinal.{0}} (hd : VbDK S l K d)
    (hdn : d ∈ S.CSet d (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1 + 1)))) :
    vbTK S l K (S.psi d (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) = S.psi (vbTK S l K d) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
  have h := vbTK_atom hl hX hKB (k := k + 1) (by omega) hd (by rw [Nat.cast_succ]; exact hdn)
  have h1 := h.1
  rwa [Nat.cast_succ] at h1

omit hl hX in
theorem fa_collW {k : ℕ} {e : Ordinal.{0}} (he : VbDK S l K e) (heA : e < ConjT.Aη S (cdEta S l)) :
    VbDK S l K (S.psi e (Om ((k : Ordinal.{0}) + 1 + 1))) := by
  have := fa_coll (S := S) (l := l) hKB (j := k + 1) he heA
  rwa [Nat.cast_succ] at this

omit hl hX in
theorem fa_collV {k : ℕ} {e : Ordinal.{0}} (he : VbDK S l K e) (heA : e < ConjT.Aη S (cdEta S l)) :
    VbDK S l K (S.psi e (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) := by
  have := fa_coll (S := S) (l := l) hKB (j := k + 1 + 1) he heA
  rwa [Nat.cast_succ, Nat.cast_succ] at this

theorem fa_r2 {k : ℕ} (hk : 1 ≤ k) : Om (1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1) := by
  have hk1 : (1 : Ordinal.{0}) ≤ k := by exact_mod_cast hk
  exact Om_le_Om.2 (add_le_add hk1 le_rfl)

/-- **The threshold `K₁` of a member of `D_K` is in `D_K`.** -/
theorem fa_K1_D {k : ℕ} {γ K1 : Ordinal.{0}} (hγD : VbDK S l K γ) (hγN : γ ∈ ⋃ a, S.CSet a 0)
    (hK1o : K1 ∈ S.CSet K1 (S.psi K1 (Om ((k : Ordinal.{0}) + 1 + 1))))
    (hK1 : ∀ e, e ≠ 0 → (ulDat S (Om ((k : Ordinal.{0}) + 1 + 1)) γ < S.psi e (Om ((k : Ordinal.{0}) + 1 + 1)) ↔ K1 < e)) :
    VbDK S l K K1 := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hs := fa_nat1_lt k
  rcases eq_or_ne K1 0 with rfl | h0
  · exact hPC.zero
  have hviz : ∀ e, UlK S ((k : Ordinal.{0}) + 1) (S.psi e (Om ((k : Ordinal.{0}) + 1 + 1))) γ ↔
      ulDat S (Om ((k : Ordinal.{0}) + 1 + 1)) γ < S.psi e (Om ((k : Ordinal.{0}) + 1 + 1)) := fun e =>
    Uo.uo_K_iff_dat hs (Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) e) (Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) e)
      (Ui.ui_psi_lt (s := (k : Ordinal.{0}) + 1) e).le hγN
  have hN : ¬ UlK S ((k : Ordinal.{0}) + 1) (S.psi K1 (Om ((k : Ordinal.{0}) + 1 + 1))) γ := fun h =>
    lt_irrefl K1 ((hK1 K1 h0).1 ((hviz K1).1 h))
  have hY : UlK S ((k : Ordinal.{0}) + 1) (S.psi (K1 + 1) (Om ((k : Ordinal.{0}) + 1 + 1))) γ :=
    (hviz _).2 ((hK1 (K1 + 1) (lt_of_le_of_lt zero_le (lt_add_one K1)).ne').2 (lt_add_one K1))
  have hψ := faGap hl hX hKB hK1o γ hγD hN hY
  exact (fa_arg hl hX (r := (k : Ordinal.{0}) + 1) (Om_le_Om.2 le_add_self) hψ hK1o).1

/-- **The threshold `K₂` of a member of `D_K` is in `D_K`.** -/
theorem fa_K2_D {k : ℕ} {γ K2 : Ordinal.{0}} (hγD : VbDK S l K γ)
    (hK2o : K2 ∈ S.CSet K2 (S.psi K2 (Om ((k : Ordinal.{0}) + 1 + 1 + 1))))
    (hK2g : K2 = 0 ∨ S.psi K2 (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ≤ γ)
    (hK2 : ∀ e, e ≠ 0 → (γ < S.psi e (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ↔ K2 < e)) :
    VbDK S l K K2 := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hs := fa_nat1_lt k
  rcases eq_or_ne K2 0 with rfl | h0
  · exact hPC.zero
  have h1 := hK2g.resolve_left h0
  have h2 : γ < S.psi (K2 + 1) (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) :=
    (hK2 (K2 + 1) (lt_of_le_of_lt zero_le (lt_add_one K2)).ne').2 (lt_add_one K2)
  have hρ1 := (vbZ hl hX).2
  have hr1 : (Om (1 : Ordinal.{0})) ≤ Om ((k : Ordinal.{0}) + 1) := Om_le_Om.2 le_add_self
  have hle : Om ((k : Ordinal.{0}) + 1) ≤ Om ((k : Ordinal.{0}) + 1 + 1) := Om_le_Om.2 le_self_add
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have h2b : Om (1 + 1 : Ordinal.{0}) ≤ Om ((k : Ordinal.{0}) + 1 + 1) := Om_le_Om.2 (add_le_add le_add_self le_rfl)
  have hψ : VbDK S l K (S.psi K2 (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) :=
    ⟨Vs.vs_gap_C hs ((hρ1.trans_le (hr1.trans hle)).le) hK2o γ hγD.1 h1 h2,
     Vs.vs_gap_C hs (((psi_lt hκ2 _).trans_le h2b).le) hK2o γ hγD.2.1 h1 h2,
     (psi_lt (InR_Om_succ _) _).trans (fa_Om1_D (S := S) (l := l) hKB (k + 1 + 1) |> fun h => by
       rw [Nat.cast_succ, Nat.cast_succ] at h; exact h.2.2)⟩
  exact (fa_arg hl hX (r := (k : Ordinal.{0}) + 1 + 1) (hr1.trans hle) hψ hK2o).1

/-- **`T` keeps the level test at an own `B` of `D_K`.** -/
theorem fa_K_psi {k : ℕ} (hk : 1 ≤ k) {B γ : Ordinal.{0}} (hBD : VbDK S l K B) (hown : B ∈ S.CSet B (S.psi B (Om ((k : Ordinal.{0}) + 1 + 1))))
    (hBA : B < ConjT.Aη S (cdEta S l)) (hγD : VbDK S l K γ) :
    UlK S ((k : Ordinal.{0}) + 1) (S.psi B (Om ((k : Ordinal.{0}) + 1 + 1))) γ ↔
      UlK S (k : Ordinal.{0}) (S.psi (vbTK S l K B) (Om ((k : Ordinal.{0}) + 1))) (vbTK S l K γ) := by
  have h := faK_iff hl hX hKB hk (fa_collW hKB hBD hBA) (Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) B)
    (Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) B) (Ui.ui_psi_lt (s := (k : Ordinal.{0}) + 1) B).le γ hγD
  rwa [(vbTK_atom hl hX hKB hk hBD hown).1] at h

/-- **THE FIRST VALUES MOVE**: `T(Hˡ_γ(0)) = Hˡ'_{T γ}(0)`. -/
theorem faFirst {k : ℕ} (hk : 1 ≤ k) {γ : Ordinal.{0}} (hγD : VbDK S l K γ) (hγV : γ < Om ((k : Ordinal.{0}) + 1 + 1 + 1))
    (hz : VbDK S l K (ulH S ((k : Ordinal.{0}) + 1) γ 0)) (hzW : ulH S ((k : Ordinal.{0}) + 1) γ 0 < Om ((k : Ordinal.{0}) + 1 + 1)) :
    vbTK S l K (ulH S ((k : Ordinal.{0}) + 1) γ 0) = ulH S (k : Ordinal.{0}) (vbTK S l K γ) 0 := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hs := fa_nat1_lt k
  have hs' : (k : Ordinal.{0}) < ω := natCast_lt_omega0 k
  have hs1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 := le_add_self
  have hκ : S.InR (Om ((k : Ordinal.{0}) + 1 + 1)) := InR_Om_succ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hr := fa_r2 hl hX hKB hk
  rcases eq_or_ne γ 0 with rfl | hγ0
  · have hp : ulH S ((k : Ordinal.{0}) + 1) 0 0 = S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1)) := Us.us_psi0 hs
    have hown0 : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1))) := CSet.zero_mem _ _
    rw [hp, (vbTK_atom hl hX hKB hk hPC.zero hown0).1, vbTK_zero hl hX hKB, Us.us_psi0 hs']
  have hθ : S.psi K (Om (1 + 1)) ≤ S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    ((psi_lt hκ2 _).le.trans (hr)).trans (Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) K).le
  have hA : ulH S ((k : Ordinal.{0}) + 1) γ 0 < S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    lt_psi_of_mem hκ (CSet_mono le_rfl hθ hz.2.1) hzW
  have hγN : γ ∈ ⋃ a, S.CSet a 0 := fa_nota hX.le hγD.1
  obtain ⟨K1, K2, hK1o, hK1m, hK1, hK2o, hK2g, hK2, B0, hown, hB0, hform⟩ :=
    faCert (S := S) (s := (k : Ordinal.{0}) + 1) hs hs1 hγ0 hγV hγN hA
  have hzB : VbDK S l K (S.psi B0 (Om ((k : Ordinal.{0}) + 1 + 1))) := by rw [hB0]; exact hz
  obtain ⟨hB0D, hB0A⟩ := fa_arg hl hX (r := (k : Ordinal.{0}) + 1) (Om_le_Om.2 le_add_self) hzB hown
  have hvB : ulH S ((k : Ordinal.{0}) + 1) γ 0 = S.psi B0 (Om ((k : Ordinal.{0}) + 1 + 1)) := hB0.symm
  obtain ⟨hTz, hown'⟩ := vbTK_atom hl hX hKB hk hB0D hown
  have hdvd := Us.us_dvd_val hs hown hvB
  have hγψ := Us.us_val_le hs hown hvB
  have hTV := fa_T_psiV hl hX hKB hk hB0D (Vp.vp_ownV hown)
  have hψVD : VbDK S l K (S.psi B0 (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) := fa_collV hKB hB0D hB0A
  have hγψ' : vbTK S l K γ ≤ S.psi (vbTK S l K B0) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
    rw [← hTV]; exact (vbTK_le_iff hl hX hKB hγD hψVD).1 hγψ
  have hdvd' := (faT_Wdvd hl hX hKB (k := k) hγD hB0D).1 hdvd
  have hKγ : UlK S ((k : Ordinal.{0}) + 1) (S.psi B0 (Om ((k : Ordinal.{0}) + 1 + 1))) γ :=
    (ul_vis (Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) B0)).1 (by rw [← hvB]; exact ulH_D_lt γ 0)
  have hK' := (fa_K_psi hl hX hKB hk hB0D hown hB0A hγD).1 hKγ
  have hpos : ∀ {x : Ordinal.{0}}, VbDK S l K x → x ≠ 0 → vbTK S l K x ≠ 0 := fun hx hx0 => by
    have h := vbTK_mono hl hX hKB hPC.zero hx (pos_iff_ne_zero.2 hx0)
    rw [vbTK_zero hl hX hKB] at h
    exact h.ne'
  have hB00 : B0 ≠ 0 := Vp.vp_B0_ne hs hγ0 hvB
  have hγ'0 := hpos hγD hγ0
  have hγ'V : vbTK S l K γ < Om ((k : Ordinal.{0}) + 1 + 1) := hγψ'.trans_lt (Ui.ui_psi_lt (s := (k : Ordinal.{0}) + 1) _)
  have hval' := Vp.vp_val_of hs' hown' (hpos hB0D hB00) hγ'0 hγ'V hdvd' hγψ' hK'
  rw [hvB, hTz]
  rcases hform with ⟨hBK, hg⟩ | ⟨hBM, hMo, hopt⟩
  · have hγT : vbTK S l K γ = S.psi (vbTK S l K B0) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
      rw [← hTV, hBK, ← hg]
    have hU := Us.us_bv hs' (vbTK S l K B0) hown' (hpos hB0D hB00) (vbTK S l K γ) hγ'0 hγ'V hdvd' hγψ' hK' (Or.inl hγT)
    exact hU.symm
  · set M := max K1 K2 with hMdef
    have hMD : VbDK S l K M := by
      rcases le_total K1 K2 with h | h
      · rw [hMdef, max_eq_right h]; exact fa_K2_D hl hX hKB hγD hK2o hK2g hK2
      · rw [hMdef, max_eq_left h]; exact fa_K1_D hl hX hKB hγD hγN hK1o hK1
    have hMB : M ≤ B0 := by rw [hBM]; exact le_self_add
    have hMA : M < ConjT.Aη S (cdEta S l) := hMB.trans_lt hB0A
    have hWD : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * 1) :=
      by
        rw [Ui.ui_W_eq]
        have hW := fa_Om2_D (S := S) (l := l) hKB k
        have hWγ : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) := by
          have := hPC.opow_mul hW γ hγD; rwa [Ui.ui_W_opow _] at this
        exact hPC.opow_mul hWγ _ hPC.one
    have hTW : vbTK S l K (Om ((k : Ordinal.{0}) + 1 + 1) ^ γ) = Om ((k : Ordinal.{0}) + 1) ^ vbTK S l K γ := by
      have h := faT_Wmul hl hX hKB (k := k) hγD hPC.one
      rwa [mul_one, fa_T_one hl hX hKB, mul_one] at h
    have hWD' : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) ^ γ) := by rwa [mul_one] at hWD
    have hTB : vbTK S l K B0 = vbTK S l K M + Om ((k : Ordinal.{0}) + 1) ^ vbTK S l K γ := by
      rw [hBM, kzT_add hl hX hKB hMD hWD', hTW]
    obtain ⟨-, hMown'⟩ := vbTK_atom hl hX hKB hk hMD hMo
    refine (fa_first_of hs' hγ'0 hown' hval' hTB hMown' ?_).symm
    rcases hopt with h0 | hd | hV | ⟨hV, hnd⟩
    · left; rw [h0, vbTK_zero hl hX hKB]
    · right; left
      intro hK2'
      have hK3 := (fa_K_psi hl hX hKB hk hMD hMo hMA hγD).2 hK2'
      have hd' := (Uo.uo_K_iff_dat hs (Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) M) (Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) M)
        (Ui.ui_psi_lt (s := (k : Ordinal.{0}) + 1) M).le hγN).1 hK3
      exact absurd hd (not_le.2 hd')
    · right; right; left
      rw [← fa_T_psiV hl hX hKB hk hMD (Vp.vp_ownV hMo)]
      exact vbTK_mono hl hX hKB (fa_collV hKB hMD hMA) hγD hV
    · right; right; right
      refine ⟨?_, fun hd => hnd ((faT_Wdvd hl hX hKB (k := k) hγD hMD).2 hd)⟩
      rw [← fa_T_psiV hl hX hKB hk hMD (Vp.vp_ownV hMo)]
      exact (vbTK_le_iff hl hX hKB (fa_collV hKB hMD hMA) hγD).1 hV

/-- **THE ATOMS MOVE**: for `Hˡ_γ(y) ∈ D_K`, `γ < V`, `y < Hˡ_γ(y) < W`: `γ, y ∈ D_K`, `T γ < V'` and
`T(Hˡ_γ(y)) = Hˡ'_{T γ}(T y)`. -/
theorem faAtom {k : ℕ} (hk : 1 ≤ k) {γ y : Ordinal.{0}} (hγ : γ < Om ((k : Ordinal.{0}) + 1 + 1 + 1))
    (hy : y < ulH S ((k : Ordinal.{0}) + 1) γ y) (hzW : ulH S ((k : Ordinal.{0}) + 1) γ y < Om ((k : Ordinal.{0}) + 1 + 1))
    (hzD : VbDK S l K (ulH S ((k : Ordinal.{0}) + 1) γ y)) :
    VbDK S l K γ ∧ VbDK S l K y ∧ vbTK S l K γ < Om ((k : Ordinal.{0}) + 1 + 1) ∧
      vbTK S l K (ulH S ((k : Ordinal.{0}) + 1) γ y) = ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K y) := by
  have hPC := faPC_D (S := S) (l := l) hKB
  have hs := fa_nat1_lt k
  have hs' : (k : Ordinal.{0}) < ω := natCast_lt_omega0 k
  have hs1 : (1 : Ordinal.{0}) ≤ (k : Ordinal.{0}) + 1 := le_add_self
  have hκ : S.InR (Om ((k : Ordinal.{0}) + 1 + 1)) := InR_Om_succ _
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hr := fa_r2 hl hX hKB hk
  have hW := fa_Om2_D (S := S) (l := l) hKB k
  have hθ : S.psi K (Om (1 + 1)) ≤ S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    ((psi_lt hκ2 _).le.trans (hr)).trans (Ui.ui_L_lt_psi (s := (k : Ordinal.{0}) + 1) K).le
  have hA : ulH S ((k : Ordinal.{0}) + 1) γ y < S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    lt_psi_of_mem hκ (CSet_mono le_rfl hθ hzD.2.1) hzW
  obtain ⟨B, c, D, hown, hc, hcD, hcond, hcase⟩ := Vp.vp_dec (S := S) (s := (k : Ordinal.{0}) + 1) hs hy hA
  have hDy : D ≤ y := by rw [← hcD]; exact le_add_self
  have hDW : D < Om ((k : Ordinal.{0}) + 1 + 1) := (hDy.trans_lt hy).trans hzW
  obtain ⟨hψe, howne⟩ := Vp.vp_run (S := S) (s := (k : Ordinal.{0}) + 1) hs hγ hown hc hDW hcond
  rw [hcD] at hψe
  have hzeD : VbDK S l K (S.psi (B + Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D) (Om ((k : Ordinal.{0}) + 1 + 1))) := by
    rw [hψe]; exact hzD
  obtain ⟨heD, heA⟩ := fa_arg hl hX (r := (k : Ordinal.{0}) + 1) (Om_le_Om.2 le_add_self) hzeD howne
  have hBe : B ≤ B + Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D := le_self_add
  have hBA : B < ConjT.Aη S (cdEta S l) := hBe.trans_lt heA
  have h0A : ulH S ((k : Ordinal.{0}) + 1) γ 0 < S.psi K (Om ((k : Ordinal.{0}) + 1 + 1)) :=
    ((ulH_le_iff γ).2 zero_le).trans_lt hA
  -- the parts
  have hparts : VbDK S l K γ ∧ VbDK S l K D ∧ VbDK S l K B ∧ VbDK S l K c := by
    rcases hcase with hc0 | ⟨hcf, hmax⟩
    · -- the first run
      subst hc0
      refine (show VbDK S l K γ ∧ VbDK S l K D ∧ VbDK S l K B from ?_).imp_right fun h => h.imp_right fun h => ⟨h, hPC.zero⟩
      rcases eq_or_ne γ 0 with rfl | hγ0
      · have hB0 : B = 0 := by
          have hp : S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1)) = S.psi B (Om ((k : Ordinal.{0}) + 1 + 1)) := by
            rw [← Us.us_psi0 hs]; exact hc
          exact Ui.ui_own_unique (s := (k : Ordinal.{0}) + 1) hown (CSet.zero_mem _ _) hp.symm
        subst hB0
        rw [opow_zero, one_mul, zero_add] at heD
        exact ⟨hPC.zero, heD, hPC.zero⟩
      have hγN : γ ∈ ⋃ a, S.CSet a 0 := by
        obtain ⟨a, ha⟩ := mem_iUnion.1 (fa_nota hX.le hzD.1)
        have hzC : ulH S ((k : Ordinal.{0}) + 1) γ y ∈ S.CSet a (S.psi a (Om (0 + 1))) :=
          CSet_mono le_rfl zero_le ha
        have hK0 : UlK S 0 (S.psi a (Om (0 + 1))) (ulH S ((k : Ordinal.{0}) + 1) γ y) := ul_K_of_mem hzC
        have hq : SC (S.psi a (Om (0 + 1))) := Ui.ui_psi_SC (s := 0) a
        have hqL : S.psi a (Om (0 + 1)) ≤ Om (0 + 1) := (Ui.ui_psi_lt (s := 0) a).le
        have hi : (0 : Ordinal.{0}) < (k : Ordinal.{0}) + 1 := lt_of_lt_of_le zero_lt_one le_add_self
        have h := (Uz.uz_L1_mp hs hi hq hqL hγ hzW (ne_of_gt hy) hK0).1
        have hlam : S.psi a (Om (0 + 1)) ≤ S.Lam := Us.us_qΛ (i := 0) omega0_pos hqL
        exact fa_nota (A := a) (by rw [zero_add]) (Uw.uw_K_CSet hlam h)
      obtain ⟨K1, K2, hK1o, -, hK1, hK2o, hK2g, hK2, B0, hown0, hB0, hform⟩ :=
        faCert (S := S) (s := (k : Ordinal.{0}) + 1) hs hs1 hγ0 hγ hγN h0A
      have hBB : B0 = B := Ui.ui_own_unique (s := (k : Ordinal.{0}) + 1) hown0 hown (hB0.trans hc)
      subst hBB
      have hγD : VbDK S l K γ := by
        rcases hform with ⟨hBK, hg⟩ | ⟨hBM, -, -⟩
        · rcases eq_or_ne D 0 with rfl | hD0
          · rw [mul_zero, add_zero] at heD heA
            rw [hg, ← hBK]
            exact fa_collV hKB heD heA
          · exact hPC.dig_exp (r := (k : Ordinal.{0}) + 1) hW heD γ (fa_dig hD0 hDW)
        · have e1 : B0 + Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D =
              max K1 K2 + Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * (1 + D) := by
            rw [hBM, mul_add, mul_one, add_assoc]
          rw [e1] at heD
          have hD1 : 1 + D ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
          have hD2 : 1 + D < Om ((k : Ordinal.{0}) + 1 + 1) :=
            (Ui.ui_SC_W ((k : Ordinal.{0}) + 1)).isPrincipal (Ui.ui_one_lt_SC (Ui.ui_SC_W _)) hDW
          exact hPC.dig_exp (r := (k : Ordinal.{0}) + 1) hW heD γ (fa_dig hD1 hD2)
      have hWγ : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) := by
        have := hPC.opow_mul hW γ hγD; rwa [Ui.ui_W_opow _] at this
      have hBD : VbDK S l K B0 := by
        rcases hform with ⟨hBK, -⟩ | ⟨hBM, -, -⟩
        · rw [hBK]; exact fa_K2_D hl hX hKB hγD hK2o hK2g hK2
        · rw [hBM]
          have hMD : VbDK S l K (max K1 K2) := by
            rcases le_total K1 K2 with h | h
            · rw [max_eq_right h]; exact fa_K2_D hl hX hKB hγD hK2o hK2g hK2
            · rw [max_eq_left h]; exact fa_K1_D hl hX hKB hγD hγN hK1o hK1
          refine hPC.add hMD ?_
          rw [Ui.ui_W_eq]
          have := hPC.opow_mul hWγ _ hPC.one
          rwa [mul_one] at this
      have hsub : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D) := by
        have := hPC.sub heD hBD hBe
        rwa [Ordinal.add_sub_cancel] at this
      have hDD : VbDK S l K D := by
        have h := hPC.div _ hsub _ hWγ
        rwa [← Ui.ui_W_eq, Ordinal.mul_div_cancel _ (Ui.ui_W_pos _ γ).ne'] at h
      exact ⟨hγD, hDD, hBD⟩
    · -- a later run
      have hψc : S.psi B (Om ((k : Ordinal.{0}) + 1 + 1)) = c := hc.symm.trans hcf
      have hfixB : ulH S ((k : Ordinal.{0}) + 1) γ (S.psi B (Om ((k : Ordinal.{0}) + 1 + 1))) =
          S.psi B (Om ((k : Ordinal.{0}) + 1 + 1)) := by rw [hψc, hcf]
      have hB0 : B ≠ 0 := by
        rintro rfl
        have hp0 : S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1)) = ulH S ((k : Ordinal.{0}) + 1) 0 0 := (Us.us_psi0 hs).symm
        have hf0 : ulH S ((k : Ordinal.{0}) + 1) 0 (S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1))) =
            S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1)) :=
          Uc.ucG_fix_mono zero_le hfixB ((ulD_le_self 0).trans_lt (Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) 0).1)
        rw [hp0] at hf0
        exact Us.us_val0_ne hf0
      obtain ⟨hdiv, -, -⟩ := (Us.us_fix_iff hs hown hB0 hγ).1 hfixB
      have hD0 : D ≠ 0 := by
        rintro rfl
        rw [add_zero] at hcD
        rw [← hcD, hcf] at hy
        exact lt_irrefl _ hy
      obtain ⟨hγD, hDD, hBD⟩ := hPC.run (r := (k : Ordinal.{0}) + 1) hW heD hdiv hD0 hDW
      refine ⟨hγD, hDD, hBD, ?_⟩
      rw [← hψc]; exact fa_collW hKB hBD hBA
  obtain ⟨hγD, hDD, hBD, hcD'⟩ := hparts
  have hyD : VbDK S l K y := by rw [← hcD]; exact hPC.add hcD' hDD
  refine ⟨hγD, hyD, ?_⟩
  -- the moves
  obtain ⟨hTz, hown'⟩ := vbTK_atom hl hX hKB hk heD howne
  obtain ⟨hTB, hownB'⟩ := vbTK_atom hl hX hKB hk hBD hown
  have hTe : vbTK S l K (B + Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D) =
      vbTK S l K B + Om ((k : Ordinal.{0}) + 1) ^ vbTK S l K γ * vbTK S l K D := by
    have hWD : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) ^ γ * D) := by
      have hWγ : VbDK S l K (Om ((k : Ordinal.{0}) + 1 + 1) * γ) := by
        have := hPC.opow_mul hW γ hγD; rwa [Ui.ui_W_opow _] at this
      rw [Ui.ui_W_eq]; exact hPC.opow_mul hWγ _ hDD
    rw [kzT_add hl hX hKB hBD hWD, faT_Wmul hl hX hKB hγD hDD]
  rw [hψe] at hTz
  rw [hTe] at hTz
  have hTV := fa_T_psiV hl hX hKB hk hBD (Vp.vp_ownV hown)
  have hψVD : VbDK S l K (S.psi B (Om ((k : Ordinal.{0}) + 1 + 1 + 1))) := fa_collV hKB hBD hBA
  have hγψ := Us.us_val_le hs hown hc
  have hγψ' : vbTK S l K γ ≤ S.psi (vbTK S l K B) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
    rw [← hTV]; exact (vbTK_le_iff hl hX hKB hγD hψVD).1 hγψ
  have hγ'V : vbTK S l K γ < Om ((k : Ordinal.{0}) + 1 + 1) := hγψ'.trans_lt (Ui.ui_psi_lt (s := (k : Ordinal.{0}) + 1) _)
  have hbase : ulH S (k : Ordinal.{0}) (vbTK S l K γ) (vbTK S l K c) = S.psi (vbTK S l K B) (Om ((k : Ordinal.{0}) + 1)) := by
    rcases hcase with hc0 | ⟨hcf, -⟩
    · subst hc0
      rw [vbTK_zero hl hX hKB]
      have hz0 : VbDK S l K (ulH S ((k : Ordinal.{0}) + 1) γ 0) := by rw [hc]; exact fa_collW hKB hBD hBA
      have hz0W : ulH S ((k : Ordinal.{0}) + 1) γ 0 < Om ((k : Ordinal.{0}) + 1 + 1) :=
        ((ulH_le_iff γ).2 zero_le).trans_lt hzW
      rw [← faFirst hl hX hKB hk hγD hγ hz0 hz0W, hc, hTB]
    · have hψc : S.psi B (Om ((k : Ordinal.{0}) + 1 + 1)) = c := hc.symm.trans hcf
      have hfixB : ulH S ((k : Ordinal.{0}) + 1) γ (S.psi B (Om ((k : Ordinal.{0}) + 1 + 1))) =
          S.psi B (Om ((k : Ordinal.{0}) + 1 + 1)) := by rw [hψc, hcf]
      have hB0 : B ≠ 0 := by
        rintro rfl
        have hp0 : S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1)) = ulH S ((k : Ordinal.{0}) + 1) 0 0 := (Us.us_psi0 hs).symm
        have hf0 : ulH S ((k : Ordinal.{0}) + 1) 0 (S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1))) =
            S.psi 0 (Om ((k : Ordinal.{0}) + 1 + 1)) :=
          Uc.ucG_fix_mono zero_le hfixB ((ulD_le_self 0).trans_lt (Ui.ui_psi_SC (s := (k : Ordinal.{0}) + 1) 0).1)
        rw [hp0] at hf0
        exact Us.us_val0_ne hf0
      obtain ⟨hdiv, hlt, hKγ⟩ := (Us.us_fix_iff hs hown hB0 hγ).1 hfixB
      have hγ1 : VbDK S l K (γ + 1) := hPC.add hγD hPC.one
      have hdiv' : Om ((k : Ordinal.{0}) + 1) ^ (vbTK S l K γ + 1) ∣ vbTK S l K B := by
        have h := (faT_Wdvd hl hX hKB (k := k) hγ1 hBD).1 hdiv
        rwa [fa_T_succ hl hX hKB hγD] at h
      have hlt' : vbTK S l K γ < S.psi (vbTK S l K B) (Om ((k : Ordinal.{0}) + 1 + 1)) := by
        rw [← hTV]; exact vbTK_mono hl hX hKB hγD hψVD hlt
      have hK' := (fa_K_psi hl hX hKB hk hBD hown hBA hγD).1 hKγ
      have hB'0 : vbTK S l K B ≠ 0 := by
        have h := vbTK_mono hl hX hKB hPC.zero hBD (pos_iff_ne_zero.2 hB0)
        rw [vbTK_zero hl hX hKB] at h
        exact h.ne'
      have hfix' := (Us.us_fix_iff hs' hownB' hB'0 hγ'V).2 ⟨hdiv', hlt', hK'⟩
      have hTc : vbTK S l K c = S.psi (vbTK S l K B) (Om ((k : Ordinal.{0}) + 1)) := by rw [← hψc, hTB]
      rw [hTc, hfix']
  have hdvd' := Us.us_dvd_val hs' hownB' hbase
  have hv' : vbTK S l K D <
      S.psi (vbTK S l K B + Om ((k : Ordinal.{0}) + 1) ^ vbTK S l K γ * vbTK S l K D) (Om ((k : Ordinal.{0}) + 1)) := by
    rw [← hTz]; exact vbTK_mono hl hX hKB hDD hzD (hDy.trans_lt hy)
  have hcond' := Vp.vp_valid (S := S) (s := (k : Ordinal.{0})) hs' hdvd' hbase hv'
  have hD'W : vbTK S l K D < Om ((k : Ordinal.{0}) + 1) := hv'.trans (Ui.ui_psi_lt (s := (k : Ordinal.{0})) _)
  have hrun := Us.us_run hs' hγ'V hownB' hbase hD'W hcond'
  have hTy : vbTK S l K y = vbTK S l K c + vbTK S l K D := by
    rw [← hcD]; exact kzT_add hl hX hKB hcD' hDD
  refine ⟨hγ'V, ?_⟩
  rw [hTz, hrun, hTy]

end Rst

end Googology.Trans.PoR.InaccPsi.R2.Fa
