import Googology.Trans.PoR.InaccPsi.R2.UfRun
import Googology.Trans.PoR.InaccPsi.R2.TwMove

/-!
# `B_n` on the codes below `B₂`: `B_n(H_γ(y)) = H_{ucMap B_n γ}(B_n y)`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ψ = ψ_{Ω₂}`, `H_γ = Uc.ucH γ`, `X = Tl.tlX`, `B₂ = Uc.ucB`,
`UcCl Z` the codes over `Z` (`R2.UcCl`), `ucDat` their data, `MvD` the domain of `B_n`.  Below `X` this is
`Tw.twB_code`; from `X` on the atom case moves the run of the atom (`Uf.ufRun`): its own argument `B + Ω₂^γ·D` goes to
`B_n B + Ω₂^{B_n γ}·B_n D` (`Uf.ufB_mulW`), whose collapse is computed again by `Uc.uc_eq_all`.  The base `B` of the
first value `H_γ(0)` is `K + Ω₂^γ` with `ψ(K)` the largest strongly critical point `≤ ucC γ` (or `K = 0`), moved by
`Uf.uf_least0`.

* `uf_ucC_mem` (the largest component is a component), `uf_fold_comm` (**a fold commutes with a function monotone on
  its values**), `ufB_X` (`B_n X = X`), `ufB_psi1` (`B_n ψ(1) = ψ(1)`);
* `ufB_code` (**for a code `μ` over a strongly critical `x < L(ω)` with `B_n x ≤ Ω₁`: `μ` is in the domain of `B_n`,
  `B_n μ` is a code over `B_n x`, `B_n μ < B₂`, `ucDat (B_n μ) = B_n (ucDat μ)`; an atom `μ` has an own argument `e`
  in the domain with `B_n μ = ψ(B_n e)`, `B_n e` own; an atom `μ ≥ X` has `X ≤ B_n μ` and
  `B_n μ = H_{B_n λ}(B_n y)` for its level `λ` and index `y`**);
* `ufB_cl`, `ufB_lt_B`, `ufB_dat` (the case `x = c_{n+1}`), `ufB_atom` (**`B_n(H_γ(y)) = H_{B_n γ}(B_n y)`, with
  `B_n γ = ucMap B_n γ`, for codes over `c_{n+1}`, `X ≤ H_γ(y)`, `y < H_γ(y)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Rj

variable {S : InaccSeq.{0}}

/-- **The largest component is a component** (`γ < E₂`). -/
theorem uf_ucC_mem : ∀ γ : Ordinal.{0}, γ < ucE → ucC γ ∈ ucComps γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ
  by_cases h1 : γ < OmTwo
  · rw [ucC_small h1, ucComps_small h1]; rfl
  have h2 := not_lt.1 h1
  have hel := uc_log_lt h2 hγ
  have hrl := uc_mod_lt h2
  have he := IH _ hel (hel.trans hγ)
  have hr := IH _ hrl (hrl.trans hγ)
  rw [ucComps_big h2 hγ]
  unfold ucC at he hr ⊢
  rw [ucFold_big id h2 hγ]
  rcases max_choice (ucFold id (log OmTwo γ))
    (max (id (γ / OmTwo ^ log OmTwo γ)) (ucFold id (γ % OmTwo ^ log OmTwo γ))) with e1 | e1 <;> rw [e1]
  · exact Or.inl he
  · rcases max_choice (id (γ / OmTwo ^ log OmTwo γ)) (ucFold id (γ % OmTwo ^ log OmTwo γ)) with e2 | e2 <;>
      rw [e2]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hr)

/-- **A fold commutes with a function monotone on its values**: `ucFold (f ∘ g) γ = f (ucFold g γ)` (`γ < E₂`). -/
theorem uf_fold_comm (f g : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, γ < ucE → (∀ a ∈ ucComps γ, ∀ b ∈ ucComps γ, g a ≤ g b → f (g a) ≤ f (g b)) →
      ucFold g γ ∈ g '' ucComps γ ∧ ucFold (fun x => f (g x)) γ = f (ucFold g γ) := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hf
  by_cases h1 : γ < OmTwo
  · rw [ucFold_small _ h1, ucFold_small _ h1, ucComps_small h1]
    exact ⟨⟨γ, rfl, rfl⟩, rfl⟩
  have h2 := not_lt.1 h1
  have hel := uc_log_lt h2 hγ
  have hrl := uc_mod_lt h2
  have hc := ucComps_big h2 hγ
  have hsub1 : ucComps (log OmTwo γ) ⊆ ucComps γ := fun x hx => by rw [hc]; exact Or.inl hx
  have hsub3 : ucComps (γ % OmTwo ^ log OmTwo γ) ⊆ ucComps γ := fun x hx => by rw [hc]; exact Or.inr (Or.inr hx)
  have hdm : γ / OmTwo ^ log OmTwo γ ∈ ucComps γ := by rw [hc]; exact Or.inr (Or.inl rfl)
  obtain ⟨he1, he2⟩ := IH _ hel (hel.trans hγ) fun a ha b hb => hf a (hsub1 ha) b (hsub1 hb)
  obtain ⟨hr1, hr2⟩ := IH _ hrl (hrl.trans hγ) fun a ha b hb => hf a (hsub3 ha) b (hsub3 hb)
  rw [ucFold_big _ h2 hγ, ucFold_big _ h2 hγ, he2, hr2]
  obtain ⟨a, ha, hae⟩ := he1
  obtain ⟨b, hb, hbe⟩ := hr1
  have hmax : ∀ u ∈ ucComps γ, ∀ v ∈ ucComps γ, max (f (g u)) (f (g v)) = f (max (g u) (g v)) :=
    fun u hu v hv => by
      rcases le_total (g u) (g v) with h | h
      · rw [max_eq_right h, max_eq_right (hf u hu v hv h)]
      · rw [max_eq_left h, max_eq_left (hf v hv u hu h)]
  set d := γ / OmTwo ^ log OmTwo γ
  rw [← hae, ← hbe]
  have hin : ∀ u ∈ ucComps γ, ∀ v ∈ ucComps γ, ∃ w ∈ ucComps γ, max (g u) (g v) = g w := fun u hu v hv => by
    rcases max_choice (g u) (g v) with e | e <;> rw [e]
    · exact ⟨u, hu, rfl⟩
    · exact ⟨v, hv, rfl⟩
  obtain ⟨w, hw, hwe⟩ := hin d hdm b (hsub3 hb)
  rw [hmax d hdm b (hsub3 hb), hwe, hmax a (hsub1 ha) w hw]
  obtain ⟨w', hw', hw'e⟩ := hin a (hsub1 ha) w hw
  exact ⟨⟨w', hw', hw'e.symm⟩, rfl⟩

/-- **`B_n X = X`.** -/
theorem ufB_X {n : ℕ} : MvD S tlX ∧ Bc.bcB S n tlX = tlX := by
  have hQ : ∀ c ∈ ucComps (OmTwo : Ordinal.{0}), c = 0 ∨ c = 1 := fun c hc => by
    rw [ucComps_Om2] at hc
    rcases hc with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hQD : ∀ v, (v = 0 ∨ v = 1) → MvD S v := fun v hv => by
    rcases hv with rfl | rfl
    · exact ufD_zero
    · exact Rk.rk_one_D
  have hQdec : ∀ v, (v = 0 ∨ v = 1) → v ≠ 0 → (log ω v = 0 ∨ log ω v = 1) ∧
      (v - ω ^ log ω v = 0 ∨ v - ω ^ log ω v = 1) := fun v hv hv0 => by
    rcases hv with rfl | rfl
    · exact absurd rfl hv0
    · refine ⟨Or.inl (Ordinal.log_one_right _), Or.inl ?_⟩
      rw [Ordinal.log_one_right, opow_zero, Ordinal.sub_self]
  have hQW : ∀ v, (v = 0 ∨ v = 1) → v < OmTwo := fun v hv => by
    rcases hv with rfl | rfl
    · exact uc_SC_Om2.1
    · exact uc_one_lt_Om2
  obtain ⟨-, -, -, -, hDW, hBW, -, -, -⟩ := ufB_lev (S := S) (n := n) (fun v => v = 0 ∨ v = 1) hQD hQdec hQW
    OmTwo ucE_gt hQ
  rw [(ufB_Om2 (S := S) (n := n)).2] at hBW
  have hown : Le.leWe (Om (1 + 1)) ∈ S.CSet (Le.leWe (Om (1 + 1))) (S.psi (Le.leWe (Om (1 + 1))) (Om (1 + 1))) :=
    Ts.tsW_mem _ _
  have hWe : Le.leWe (Om (1 + 1)) = OmTwo ^ OmTwo := by rw [uc_leWe, ← uf_Om2]
  rw [← hWe] at hDW hBW
  obtain ⟨hD, hB⟩ := Mx.mxB_atom (n := n) hDW hown
  rw [hBW, Ts.ts_psiW_eq_X] at hB
  rw [Ts.ts_psiW_eq_X] at hD
  exact ⟨hD, hB⟩

/-- **`B_n ψ(1) = ψ(1)`**, `ψ(1)` in the domain. -/
theorem ufB_psi1 {n : ℕ} : MvD S (S.psi 1 (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi 1 (Om (1 + 1))) = S.psi 1 (Om (1 + 1)) := by
  have hown : (1 : Ordinal.{0}) ∈ S.CSet 1 (S.psi 1 (Om (1 + 1))) := CSet.one_mem _ _
  obtain ⟨hD, hB⟩ := Mx.mxB_atom (n := n) (Rk.rk_one_D (S := S)) hown
  rw [Mw.mwB_one] at hB
  exact ⟨hD, hB⟩

/-- `B_n` keeps `≤` on its domain. -/
theorem ufB_le {n : ℕ} {a b : Ordinal.{0}} (ha : MvD S a) (hb : MvD S b) (h : a ≤ b) :
    Bc.bcB S n a ≤ Bc.bcB S n b := by
  rcases h.lt_or_eq with h' | h'
  · exact ((mvB_lt_iff ha hb).2 h').le
  · rw [h']

/-- **`B_n` on the codes below `B₂`**: for a code `μ` over a strongly critical `x < L(ω)` with `B_n x ≤ Ω₁`, `μ` is in
the domain of `B_n`, `B_n μ` is a code over `B_n x`, `B_n μ < B₂`, `ucDat (B_n μ) = B_n (ucDat μ)`; an atom `μ` has an
own argument `e` in the domain with `B_n e` own and `B_n μ = ψ(B_n e)`; an atom `μ ≥ X` has `X ≤ B_n μ` and
`B_n μ = H_{B_n λ}(B_n y)` for its level `λ = ucLev μ` and index `y`. -/
theorem ufB_code {n : ℕ} {x : Ordinal.{0}} (hxS : SC x) (hxL : x < Nc.ncL S ω) (hBx : Bc.bcB S n x ≤ Om 1) :
    ∀ μ, UcCl x μ → MvD S μ ∧ UcCl (Bc.bcB S n x) (Bc.bcB S n μ) ∧ Bc.bcB S n μ < ucB ∧
      ucDat (Bc.bcB S n μ) = Bc.bcB S n (ucDat μ) ∧
      (SC μ → Om1 < μ → ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = μ ∧ MvD S e ∧
        Bc.bcB S n e ∈ S.CSet (Bc.bcB S n e) (S.psi (Bc.bcB S n e) (Om (1 + 1))) ∧
        Bc.bcB S n μ = S.psi (Bc.bcB S n e) (Om (1 + 1))) ∧
      (SC μ → tlX ≤ μ → tlX ≤ Bc.bcB S n μ ∧
        Bc.bcB S n μ = ucH (Bc.bcB S n (ucLev μ)) (Bc.bcB S n (ucI (ucLev μ) μ))) := by
  have hx1 : x ≤ Om1 := by rw [uf_Om1]; exact (hxL.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  have hBx1 : Bc.bcB S n x ≤ Om1 := by rw [uf_Om1]; exact hBx
  have hD0 : MvD S (0 : Ordinal.{0}) := mvD_of_lt (lt_of_le_of_lt zero_le hxL)
  have hBxpos : 0 < Bc.bcB S n x := by
    have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hxL) hxL).2 hxS.1
    rwa [Bc.bcB_zero] at this
  have hdL : ∀ w, UcCl x w → ucDat w < Nc.ncL S ω := fun w hw => (uc_cl_dat hxS w hw).trans hxL
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hDO1 : MvD S Om1 := by rw [uf_Om1]; exact hDO
  have hBO1 : Bc.bcB S n Om1 = Om1 := by rw [uf_Om1]; exact hBO
  obtain ⟨hDX, hBX⟩ := ufB_X (S := S) (n := n)
  have hXle : ∀ {w : Ordinal.{0}}, MvD S w → tlX ≤ w → tlX ≤ Bc.bcB S n w := fun hw h => by
    have := ufB_le (n := n) hDX hw h; rwa [hBX] at this
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz
  have hzB : z < ucB := uf_cl_lt_B hx1 hz
  rcases lt_or_ge z tlX with hzX | hXz
  · -- below `X`: `Tw.twB_code`
    have htl := uc_cl_lt_X hz hzX
    obtain ⟨hD, hC, hBX', hd, hlast⟩ := Tw.twB_code hxS hxL hBx z htl
    refine ⟨hD, UcCl.tl hC, hBX'.trans uc_X_lt_B, by rw [ucDat_lt_X hBX', ucDat_lt_X hzX, hd],
      fun hS h1 => ?_, fun _ h => absurd h (not_le.2 hzX)⟩
    obtain ⟨e, a, b, c, d, f, -⟩ := hlast hS h1
    exact ⟨e, a, b, c, d, f⟩
  have h : Om1 < z := uc_Om1_lt_of_X hXz
  have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h).ne'
  have hOz : ∀ {w : Ordinal.{0}}, MvD S w → Om1 < w → Om1 < Bc.bcB S n w := fun hDw hw => by
    have := (mvB_lt_iff (k := n) hDO1 hDw).2 hw; rwa [hBO1] at this
  by_cases hE : ω ^ z = z
  · by_cases hI : invVeblen₁ z < z
    · -- a Veblen normal form `φ(o, b)`
      set o := invVeblen₁ z with ho
      set b := invVeblen₂ z with hb
      have hbz : b < z := tf_inv2_lt hE
      obtain ⟨hco, hcb⟩ := uc_cl_inv hx1 z hz h hE hI
      have hev : veblen o b = z := by rw [ho, hb, veblen_invVeblen₁_invVeblen₂, hE]
      have ho0 : o ≠ 0 := by
        intro e
        rw [e, veblen_zero_apply] at hev
        have : ω ^ b = ω ^ z := by rw [hev, hE]
        exact absurd ((opow_right_inj one_lt_omega0).1 this) hbz.ne
      obtain ⟨hDo, hCo, -, hdo, -, -⟩ := IH o hI hco
      obtain ⟨hDb, hCb, -, hdb, -, -⟩ := IH b hbz hcb
      obtain ⟨hDz, hBz⟩ := Mw.mwB_phi (k := n) hDo hDb (by rw [hev]; exact hI) (by rw [hev]; exact hbz)
      rw [hev] at hBz hDz
      have hBo0 : Bc.bcB S n o ≠ 0 := by
        intro e
        have h1 := (mvB_lt_iff (k := n) hD0 hDo).2 (pos_iff_ne_zero.2 ho0)
        rw [Bc.bcB_zero, e] at h1
        exact lt_irrefl _ h1
      have hBb : Bc.bcB S n b < veblen (Bc.bcB S n o) (Bc.bcB S n b) := by
        rw [← hBz]; exact (mvB_lt_iff hDb hDz).2 hbz
      have hBo : Bc.bcB S n o < Bc.bcB S n z := (mvB_lt_iff hDo hDz).2 hI
      have hCz : UcCl (Bc.bcB S n x) (Bc.bcB S n z) := by rw [hBz]; exact UcCl.phi hCo hCb
      have hBzB : Bc.bcB S n z < ucB := uf_cl_lt_B hBx1 hCz
      refine ⟨hDz, hCz, hBzB, ?_, fun hSC _ => absurd hI (tl_SC_facts hSC).2,
        fun hSC _ => absurd hI (tl_SC_facts hSC).2⟩
      have hBE : ω ^ Bc.bcB S n z = Bc.bcB S n z := by rw [hBz]; exact Gg.gg_veblen_eps hBo0
      have hBI : invVeblen₁ (Bc.bcB S n z) < Bc.bcB S n z := by
        rw [hBz, invVeblen₁_veblen hBb, ← hBz]; exact hBo
      rw [ucDat_phi (hXle hDz hXz) hBzB hBE hBI, ucDat_phi hXz hzB hE hI, hBz, invVeblen₁_veblen hBb,
        invVeblen₂_veblen hBo0 hBb, hdo, hdb]
      rcases le_total (ucDat o) (ucDat b) with hle | hle
      · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL b hcb) hle)]
      · rw [max_eq_left hle, max_eq_left (Ri.riB_mono (hdL o hco) hle)]
    · -- an atom `H_λ(y)`
      have hSC := tl_SC_of h hI
      have hne := uc_nf_of_lt hSC h hzB
      obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h hne
      obtain ⟨hnf, hyz⟩ := uc_nf hSC h hne
      obtain ⟨hcl, hcy⟩ := uc_cl_atom hx1 z hz hSC hXz hzB
      generalize hldef : ucLev z = l at hlE hlv hnf hyz hcl hcy ⊢
      generalize hydef : ucI l z = y at hnf hyz hcy ⊢
      -- the class of the codes below `z`
      set Q : Ordinal.{0} → Prop := fun v => v < z ∧ UcCl x v with hQdef
      have hQD : ∀ v, Q v → MvD S v := fun v hv => (IH v hv.1 hv.2).1
      have hQdec : ∀ v, Q v → v ≠ 0 → Q (log ω v) ∧ Q (v - ω ^ log ω v) :=
        fun v hv hv0 => ⟨⟨(log_le_self _ _).trans_lt hv.1, (ucDec hxS hx1 v hv.2).2⟩,
          ⟨(Ordinal.sub_le_self _ _).trans_lt hv.1,
            (ucDec hxS hx1 v hv.2).1 _ (UcCl.opow hxS.1 (ucDec hxS hx1 v hv.2).2) (opow_log_le_self ω hv0)⟩⟩
      have hQW : ∀ v, Q v → v < OmTwo := fun v hv => uf_cl_lt_Om2 hx1 hv.2
      have hQl : ∀ c ∈ ucComps l, Q c := fun c hc => ⟨(le_ucC hc).trans_lt hlv, hcl c hc⟩
      obtain ⟨hDl, -, -, -, hDWl, hBWl, hBlE, hCl, hFl⟩ := ufB_lev (n := n) Q hQD hQdec hQW l hlE hQl
      set l' := Bc.bcB S n l with hl'def
      have hCl' : ucC l' = Bc.bcB S n (ucC l) := by
        unfold ucC
        rw [hFl id]
        exact (uf_fold_comm (Bc.bcB S n) id l hlE fun a ha b hb hab => ufB_le (hQD a (hQl a ha))
          (hQD b (hQl b hb)) hab).2
      obtain ⟨hDy, hCy, -, hdy, -, -⟩ := IH y hyz hcy
      obtain ⟨B, c, D, hown, hBE, hdvd, hc, hcD, hD2, hval, hcc, hDc, hcase⟩ :=
        ufRun (S := S) hxS hx1 hlE hcy (by rw [hnf]; exact hyz) (by rw [hnf]; exact hzB)
      have hcz : c < z := (le_self_add.trans_eq hcD).trans_lt hyz
      have hDz : D < z := (le_add_self.trans_eq hcD).trans_lt hyz
      obtain ⟨hDc', -, hBcB, -, hlastc, hlastc2⟩ := IH c hcz hcc
      obtain ⟨hDD, -, -, -, -, -⟩ := IH D hDz hDc
      obtain ⟨hDW, hBW⟩ := ufB_mulW (n := n) Q hQD hQdec hQW hlE hQl ⟨hDz, hDc⟩
      -- the base and its image
      have hbase : MvD S B ∧
          Bc.bcB S n B ∈ S.CSet (Bc.bcB S n B) (S.psi (Bc.bcB S n B) (Om (1 + 1))) ∧
          Bc.bcB S n B < ucE ∧ ucH l' (Bc.bcB S n c) = S.psi (Bc.bcB S n B) (Om (1 + 1)) := by
        rcases hcase with hc0 | ⟨hc1, hcf, -, -⟩
        · subst hc0
          rw [Bc.bcB_zero]
          rcases eq_or_ne l 0 with hl0 | hl0
          · have hψ : S.psi B (Om (1 + 1)) = S.psi 0 (Om (1 + 1)) := by
              rw [← hc, hl0, uf_H0]
            have hB0 : B = 0 := Ts.ts_own_unique hown (CSet.zero_mem _ _) hψ
            subst hB0
            rw [hl'def, hl0, Bc.bcB_zero, uf_H0]
            exact ⟨hD0, CSet.zero_mem _ _, h0E, rfl⟩
          have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl0
          have hl'1 : 1 ≤ l' := by
            rcases hl1.lt_or_eq with hlt | heq
            · rw [← Mw.mwB_one (S := S) n]; exact ((mvB_lt_iff Rk.rk_one_D hDl).2 hlt).le
            · rw [hl'def, ← heq, Mw.mwB_one]
          have hmc : ucC l ∈ ucComps l := uf_ucC_mem l hlE
          have hQm := hQl _ hmc
          obtain ⟨hDm, -, -, -, -, -⟩ := IH _ hQm.1 hQm.2
          obtain ⟨hD1, hB1⟩ := ufB_psi1 (S := S) (n := n)
          by_cases hm1 : ucC l < S.psi 1 (Om (1 + 1))
          · -- `K = 0`
            obtain ⟨h0eq, -, -⟩ := uf_least0 (S := S) hl1 hlE (CSet.zero_mem _ _) h0E (Or.inr rfl)
              (by rw [zero_add]; exact hm1)
            rw [zero_add] at h0eq
            have hBw : B = OmTwo ^ l := Ts.ts_own_unique hown
              (by have := (uf_least0 (S := S) hl1 hlE (CSet.zero_mem _ _) h0E (Or.inr rfl)
                    (by rw [zero_add]; exact hm1)).2.1; rwa [zero_add] at this) (by rw [← hc, h0eq])
            subst hBw
            have hm1' : ucC l' < S.psi (0 + 1) (Om (1 + 1)) := by
              rw [hCl', zero_add, ← hB1]; exact (mvB_lt_iff hDm hD1).2 hm1
            obtain ⟨h0eq', hown', hE'⟩ := uf_least0 (S := S) hl'1 hBlE (CSet.zero_mem _ _) h0E (Or.inr rfl) hm1'
            rw [zero_add] at h0eq' hown' hE'
            rw [hBWl]
            exact ⟨hDWl, hown', hE', h0eq'⟩
          · -- `K` with `ψ(K)` the largest strongly critical point `≤ ucC l`
            set m := ucC l with hmdef
            set P : Set Ordinal.{0} := {s | SC s ∧ Om1 < s ∧ s ≤ m} with hPdef
            have hψ1S : SC (S.psi 1 (Om (1 + 1))) := Ts.ts_psi_SC 1
            have hψ11 : Om1 < S.psi 1 (Om (1 + 1)) := by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi 1
            have hPne : P.Nonempty := ⟨_, hψ1S, hψ11, not_lt.1 hm1⟩
            have hPb : BddAbove P := ⟨m, fun s hs => hs.2.2⟩
            set v := sSup P with hvdef
            have hvm : v ≤ m := csSup_le hPne fun s hs => hs.2.2
            have hvS : SC v := uc_SC_sSup (fun s hs => hs.1) hPne hPb
            have hv1 : Om1 < v := hψ11.trans_le (le_csSup hPb ⟨hψ1S, hψ11, not_lt.1 hm1⟩)
            have hvmax : ∀ s, SC s → Om1 < s → s ≤ m → s ≤ v := fun s a b c => le_csSup hPb ⟨a, b, c⟩
            obtain ⟨t, htc, htS, hvt, htm⟩ := uf_SC_code hx1 m hQm.2 v hvS hv1 hvm
            have htv : t = v := le_antisymm (hvmax t htS (hv1.trans_le hvt) htm) hvt
            rw [htv] at htc
            have hvz : v < z := hvm.trans_lt hQm.1
            obtain ⟨-, -, hBvB, -, hlastv, -⟩ := IH v hvz htc
            obtain ⟨K, hownK, hψK, hDK, hownK', hBv⟩ := hlastv hvS hv1
            have hKE : K < ucE := uf_own_lt_E hownK (by rw [hψK]; exact hvz.trans hzB)
            have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om (1 + 1))) :=
              CSet.add_mem ((psi_mono (S := S) (InR_Om_succ 1) le_self_add).2 hownK) (CSet.one_mem _ _)
            have hmK : m < S.psi (K + 1) (Om (1 + 1)) := by
              by_contra hc'
              push Not at hc'
              have h1 := hvmax _ (Ts.ts_psi_SC _) (by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi _) hc'
              rw [← hψK] at h1
              exact absurd (Ts.ts_psi_lt_of_own hownK (lt_add_one K)) (not_lt.2 h1)
            obtain ⟨h0eq, hownE, -⟩ := uf_least0 (S := S) hl1 hlE hownK hKE (Or.inl (by rw [hψK]; exact hvm))
              hmK
            have hBK : B = K + OmTwo ^ l := Ts.ts_own_unique hown hownE (by rw [← hc, h0eq])
            subst hBK
            -- the image of `K`
            set K' := Bc.bcB S n K with hK'def
            have hK'E : K' < ucE := uf_own_lt_E hownK' (by rw [← hBv]; exact hBvB)
            obtain ⟨hDK1, hBK1⟩ := mvB_add (k := n) hDK (Rk.rk_one_D (S := S))
            rw [Mw.mwB_one] at hBK1
            obtain ⟨hDψ1, hBψ1⟩ := Mx.mxB_atom (n := n) hDK1 hown1
            rw [hBK1] at hBψ1
            have hle' : S.psi K' (Om (1 + 1)) ≤ ucC l' := by
              rw [← hBv, hCl', ← hψK]; exact ufB_le (by rw [hψK]; exact (IH v hvz htc).1) hDm (by rw [hψK]; exact hvm)
            have hlt' : ucC l' < S.psi (K' + 1) (Om (1 + 1)) := by
              rw [hCl', ← hBψ1]; exact (mvB_lt_iff hDm hDψ1).2 hmK
            obtain ⟨h0eq', hown', hE'⟩ := uf_least0 (S := S) hl'1 hBlE hownK' hK'E (Or.inl hle') hlt'
            obtain ⟨hDB, hBB⟩ := mvB_add (k := n) hDK hDWl
            rw [hBWl] at hBB
            rw [hBB]
            exact ⟨hDB, hown', hE', h0eq'⟩
        · -- a fixed point `c`
          have hcSC : SC c := by rw [← hcf]; exact ucH_SC l c
          obtain ⟨ec, hownc, hψc, hDec, hownc', hBc⟩ := hlastc hcSC hc1
          have hψB : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
          have hBe : B = ec := Ts.ts_own_unique hown hownc (by rw [hψB, hψc])
          subst hBe
          have hClc : ucC l < c := by rw [← hcf]; exact ucH_C_lt l c
          have hBClc : ucC l' < Bc.bcB S n c := by
            rw [hCl']
            have hmc : ucC l ∈ ucComps l := uf_ucC_mem l hlE
            exact (mvB_lt_iff (hQD _ (hQl _ hmc)) hDc').2 hClc
          have hfix' : ucH l' (Bc.bcB S n c) = Bc.bcB S n c := by
            rcases lt_or_ge c tlX with hcX | hcX
            · -- below `X`: the level `l < Ω₂` and `F_l`
              have hl2 : l < OmTwo := by
                by_contra hc'
                exact absurd (uf_fix_ge_X (not_lt.1 hc') hcf) (not_le.2 hcX)
              rw [ucC_small hl2] at hClc
              have hl2' : l' < OmTwo := by
                have := (mvB_lt_iff (k := n) hDl (ufB_Om2 (S := S) (n := n)).1).2 hl2
                rwa [(ufB_Om2 (S := S) (n := n)).2] at this
              rw [ucC_small hl2'] at hBClc
              have hFc : rhF l c = c := (ucH_fix_iff_F hl2 (max_lt hc1 hClc)).1 hcf
              have htlc := uc_cl_lt_X hcc hcX
              obtain ⟨hlc, hnfc, -⟩ := tlLev_spec hcSC hc1 hcX
              have hlev : l < tlLev c := not_le.1 fun hle => hnfc (rhF_fix_mono hle hFc)
              obtain ⟨hcl', -⟩ := tl_cl_atom hx1 c htlc hcSC hc1
              obtain ⟨hDlc, -, -, -, -⟩ := Tw.twB_code hxS hxL hBx (tlLev c) hcl'
              obtain ⟨-, -, -, -, hlastT⟩ := Tw.twB_code hxS hxL hBx c htlc
              obtain ⟨-, -, -, -, -, -, hBcF⟩ := hlastT hcSC hc1
              have hlt' : l' < Bc.bcB S n (tlLev c) := (mvB_lt_iff hDl hDlc).2 hlev
              have hF' : rhF l' (Bc.bcB S n c) = Bc.bcB S n c := by
                rw [hBcF]; exact rhF_fix_lower hlt' _
              exact (ucH_fix_iff_F hl2' (max_lt (hOz hDc' hc1) hBClc)).2 hF'
            · -- at or above `X`: the level of `c` is above `l`
              obtain ⟨hXc', hBcH⟩ := hlastc2 hcSC hcX
              have hcB : c < ucB := hcz.trans hzB
              have hnec := uc_nf_of_lt hcSC hc1 hcB
              obtain ⟨hκE, hκc, hκne, hκlow, -⟩ := ucLev_spec hcSC hc1 hnec
              have hlκ : l < ucLev c := by
                rcases lt_trichotomy l (ucLev c) with h' | h' | h'
                · exact h'
                · exact absurd (h' ▸ hcf) hκne
                · exact absurd (ucG_fix_lower h' ⟨c, hcf⟩ hκc) hκne
              obtain ⟨hcκ, -⟩ := uc_cl_atom hx1 c hcc hcSC hcX hcB
              have hQκ : ∀ c' ∈ ucComps (ucLev c), Q c' := fun c' hc' =>
                ⟨((le_ucC hc').trans_lt hκc).trans hcz, hcκ c' hc'⟩
              have hDκ := (ufB_lev (n := n) Q hQD hQdec hQW _ hκE hQκ).1
              have hlt' : l' < Bc.bcB S n (ucLev c) := (mvB_lt_iff hDl hDκ).2 hlκ
              rw [hBcH]
              exact ucG_fix_lower hlt' ⟨_, rfl⟩ (by rw [← hBcH]; exact hBClc)
          exact ⟨hDec, hownc', uf_own_lt_E hownc' (by rw [← hBc]; exact hBcB), by rw [hfix', hBc]⟩
      obtain ⟨hDB, hownB', hBBE, hc'⟩ := hbase
      have hdvd' : OmTwo ^ l' ∣ Bc.bcB S n B := uf_dvd_of_range hownB' hBBE fun j hj hd => by
        rw [← hc'] at hd ⊢; exact ucG_fix_lower hj ⟨_, rfl⟩ hd
      -- the move of the run
      obtain ⟨hψe, -, howne, -⟩ := ufRun_eq hlE hown hBE hdvd hc hD2 hval
      rw [hcD, hnf] at hψe
      obtain ⟨hDe, hBe⟩ := mvB_add (k := n) hDB hDW
      rw [hBW] at hBe
      obtain ⟨hDzz, hBz⟩ := Mx.mxB_atom (n := n) hDe howne
      rw [hψe] at hDzz hBz
      have hBDz : Bc.bcB S n D < Bc.bcB S n z := (mvB_lt_iff hDD hDzz).2 hDz
      have hv' : Bc.bcB S n D < S.psi (Bc.bcB S n B + OmTwo ^ l' * Bc.bcB S n D) (Om (1 + 1)) := by
        rw [← hBe, ← hBz]; exact hBDz
      have hval' := uf_valid hBlE hdvd' hBBE hc' hv'
      have hBD2 : Bc.bcB S n D < OmTwo :=
        hv'.trans_le (le_of_lt (by rw [uf_Om2]; exact Ts.ts_psi_lt _))
      obtain ⟨heq', -, hown2, -⟩ := ufRun_eq hBlE hownB' hBBE hdvd' hc' hBD2 hval'
      obtain ⟨-, hBcD⟩ := mvB_add (k := n) hDc' hDD
      rw [hcD] at hBcD
      have hBz2 : Bc.bcB S n z = ucH l' (Bc.bcB S n y) := by rw [hBz, hBe, heq', hBcD]
      -- the image atom
      have hByz : Bc.bcB S n y < Bc.bcB S n z := (mvB_lt_iff hDy hDzz).2 hyz
      have hXBz : tlX ≤ Bc.bcB S n z := hXle hDzz hXz
      have hCz : UcCl (Bc.bcB S n x) (Bc.bcB S n z) := by
        rw [hBz2]
        refine UcCl.hatom hBlE (fun c' hc' => ?_) hCy (by rw [← hBz2]; exact hXBz)
        rw [hCl] at hc'
        obtain ⟨c0, hc0, rfl⟩ := hc'
        exact (IH c0 (hQl c0 hc0).1 (hQl c0 hc0).2).2.1
      have hBzB : Bc.bcB S n z < ucB := uf_cl_lt_B hBx1 hCz
      refine ⟨hDzz, hCz, hBzB, ?_, fun _ _ => ⟨_, howne, hψe, hDe, by rw [hBe]; exact hown2, by rw [hBz, hBe]⟩,
        fun _ _ => ⟨hXBz, hBz2⟩⟩
      have hByH : Bc.bcB S n y < ucH l' (Bc.bcB S n y) := by rw [← hBz2]; exact hByz
      rw [hBz2, ucDat_H hBlE hByH (by rw [← hBz2]; exact hXBz) (by rw [← hBz2]; exact hBzB), hFl ucDat,
        ← hnf, ucDat_H hlE (by rw [hnf]; exact hyz) (by rw [hnf]; exact hXz) (by rw [hnf]; exact hzB), hdy]
      have hcong : ucFold (fun x' => ucDat (Bc.bcB S n x')) l = ucFold (fun x' => Bc.bcB S n (ucDat x')) l :=
        ucFold_congr l fun c' hc' => (IH c' (hQl c' hc').1 (hQl c' hc').2).2.2.2.1
      have hcomm := (uf_fold_comm (Bc.bcB S n) ucDat l hlE fun a ha _ hb hab =>
        Ri.riB_mono (hdL _ (hQl _ hb).2) hab).2
      rw [hcong, hcomm]
      have hFdL : ucFold ucDat l < Nc.ncL S ω :=
        (ucFold_lt_iff ucDat (zero_le.trans_lt hxL) l).2 fun c' hc' => hdL c' (hQl c' hc').2
      rcases le_total (ucFold ucDat l) (ucDat y) with hle | hle
      · rw [max_eq_right hle, max_eq_right (Ri.riB_mono (hdL y hcy) hle)]
      · rw [max_eq_left hle, max_eq_left (Ri.riB_mono hFdL hle)]
  · -- Cantor normal form
    obtain ⟨hsub, hlog⟩ := ucDec hxS hx1 z hz
    set g := log ω z with hgdef
    have hgz : g < z := tf_log_lt h hE
    obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt z one_lt_omega0)
    have hk0 : k ≠ 0 := by
      intro e
      have h1 := Ordinal.div_opow_log_pos ω hz0
      rw [hk, e, Nat.cast_zero] at h1
      exact lt_irrefl _ h1
    have hdec : ω ^ g * k + z % ω ^ g = z := by
      have := Ordinal.div_add_mod z (ω ^ g); rwa [hk] at this
    have hrg : z % ω ^ g < ω ^ g := Ordinal.mod_lt z (opow_pos _ omega0_pos).ne'
    have hwk : UcCl x (ω ^ g * k) := UcCl.mul_nat hxS.1 (UcCl.opow hxS.1 hlog) k
    have hle : ω ^ g * k ≤ z := by
      conv_rhs => rw [← hdec]
      exact le_self_add
    have hr : UcCl x (z % ω ^ g) := by
      have e : z - ω ^ g * k = z % ω ^ g := by
        nth_rewrite 1 [← hdec]; exact Ordinal.add_sub_cancel _ _
      rw [← e]; exact hsub _ hwk hle
    have hrz : z % ω ^ g < z := Rj.rj_mod_lt hz0
    obtain ⟨hDg, hCg, -, hdg, -, -⟩ := IH g hgz hlog
    obtain ⟨hDr, hCr, -, hdr, -, -⟩ := IH _ hrz hr
    obtain ⟨hDw, hBw⟩ := Rk.rkB_opow_nat (n := n) hDg k
    obtain ⟨hDz, hBz⟩ := mvB_add (k := n) hDw hDr
    rw [hdec] at hBz hDz
    obtain ⟨hDog, hBog⟩ := Ld.ldB_opow (n := n) hDg
    have hBr : Bc.bcB S n (z % ω ^ g) < ω ^ Bc.bcB S n g := by
      rw [← hBog]; exact (mvB_lt_iff hDr hDog).2 hrg
    have hCz : UcCl (Bc.bcB S n x) (Bc.bcB S n z) := by
      rw [hBz, hBw]; exact UcCl.add (UcCl.mul_nat hBxpos (UcCl.opow hBxpos hCg) k) hCr
    have hBzB : Bc.bcB S n z < ucB := uf_cl_lt_B hBx1 hCz
    refine ⟨hDz, hCz, hBzB, ?_, fun hSC _ => absurd (tl_SC_facts hSC).1 hE,
      fun hSC _ => absurd (tl_SC_facts hSC).1 hE⟩
    have hlogB : log ω (Bc.bcB S n z) = Bc.bcB S n g := by
      rw [hBz, hBw, log_opow_mul_add one_lt_omega0 (by exact_mod_cast hk0) hBr,
        Ordinal.log_eq_zero (natCast_lt_omega0 k), add_zero]
    have hmodB : Bc.bcB S n z % ω ^ log ω (Bc.bcB S n z) = Bc.bcB S n (z % ω ^ g) := by
      rw [hlogB, hBz, hBw, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hBr]
    have hBE : ω ^ Bc.bcB S n z ≠ Bc.bcB S n z := by
      intro e
      have h1 : log ω (Bc.bcB S n z) = Bc.bcB S n z := by
        conv_lhs => rw [← e]
        exact log_opow one_lt_omega0 _
      rw [hlogB] at h1
      exact absurd h1 ((mvB_lt_iff hDg hDz).2 hgz).ne
    rw [ucDat_cnf (hXle hDz hXz) hBzB hBE, hmodB, hlogB, hdg, hdr, ucDat_cnf hXz hzB hE]
    rcases le_total (ucDat g) (ucDat (z % ω ^ g)) with hle' | hle'
    · rw [max_eq_right hle', max_eq_right (Ri.riB_mono (hdL _ hr) hle')]
    · rw [max_eq_left hle', max_eq_left (Ri.riB_mono (hdL g hlog) hle')]

/-- **A code over `c_{n+1}` is in the domain of `B_n`; its image is a code over `B_n c_{n+1}` below `B₂`, with
`ucDat (B_n μ) = B_n (ucDat μ)`.** -/
theorem ufB_cl {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) :
    MvD S μ ∧ UcCl (Bc.bcB S n (Bc.bcC S (n + 1))) (Bc.bcB S n μ) ∧ Bc.bcB S n μ < ucB ∧
      ucDat (Bc.bcB S n μ) = Bc.bcB S n (ucDat μ) := by
  obtain ⟨a, b, c, d, -⟩ := ufB_code (Lw.lw_L_SC S _) (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) μ hμ
  exact ⟨a, b, c, d⟩

theorem ufB_lt_B {n : ℕ} {μ : Ordinal.{0}} (hμ : UcCl (Bc.bcC S (n + 1)) μ) : Bc.bcB S n μ < ucB :=
  (ufB_cl hμ).2.2.1

theorem ufB_dat {n : ℕ} {z : Ordinal.{0}} (hz : UcCl (Bc.bcC S (n + 1)) z) :
    ucDat (Bc.bcB S n z) = Bc.bcB S n (ucDat z) := (ufB_cl hz).2.2.2

/-- **`B_n(H_γ(y)) = H_{B_n γ}(B_n y)`**, `B_n γ = ucMap B_n γ`, for `γ < E₂` with every component a code over
`c_{n+1}`, a code `y` over `c_{n+1}`, `y < H_γ(y)`, `X ≤ H_γ(y)`; the atom is in the domain of `B_n`, and so is its
own argument `e`, with `B_n(H_γ(y)) = ψ(B_n e)`, `B_n e` own. -/
theorem ufB_atom {n : ℕ} {γ y : Ordinal.{0}} (hγ : γ < ucE) (hc : ∀ x ∈ ucComps γ, UcCl (Bc.bcC S (n + 1)) x)
    (hy : UcCl (Bc.bcC S (n + 1)) y) (hyz : y < ucH γ y) (hX : tlX ≤ ucH γ y) :
    MvD S (ucH γ y) ∧ Bc.bcB S n (ucH γ y) = ucH (Bc.bcB S n γ) (Bc.bcB S n y) ∧
      Bc.bcB S n γ = ucMap (Bc.bcB S n) γ ∧
      ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = ucH γ y ∧ MvD S e ∧
        Bc.bcB S n e ∈ S.CSet (Bc.bcB S n e) (S.psi (Bc.bcB S n e) (Om (1 + 1))) ∧
        Bc.bcB S n (ucH γ y) = S.psi (Bc.bcB S n e) (Om (1 + 1)) := by
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hz : UcCl (Bc.bcC S (n + 1)) (ucH γ y) := UcCl.hatom hγ hc hy hX
  obtain ⟨hD, -, -, -, hlast, hlast2⟩ := ufB_code (Lw.lw_L_SC S _) (Bc.bcC_lt S (n + 1)) (Tc.tcB_c_le n) _ hz
  have h1 : Om1 < ucH γ y := ucH_gt γ y
  obtain ⟨e, h2, h3, h4, h5, h6⟩ := hlast (ucH_SC γ y) h1
  obtain ⟨-, h7⟩ := hlast2 (ucH_SC γ y) hX
  obtain ⟨hl, hi⟩ := ucLev_H hγ hyz
  rw [hl, hi] at h7
  have hx1 : Bc.bcC S (n + 1) ≤ Om1 := by
    rw [uf_Om1]; exact (Bc.bcC_lt S (n + 1) |>.trans (InaccSeq.psi_lt Low.InR_Om_one _)).le
  set Q : Ordinal.{0} → Prop := fun v => UcCl (Bc.bcC S (n + 1)) v with hQdef
  have hQD : ∀ v, Q v → MvD S v := fun v hv => (ufB_cl hv).1
  have hQdec : ∀ v, Q v → v ≠ 0 → Q (log ω v) ∧ Q (v - ω ^ log ω v) :=
    fun v hv hv0 => ⟨(ucDec hcS hx1 v hv).2,
      (ucDec hcS hx1 v hv).1 _ (UcCl.opow hcS.1 (ucDec hcS hx1 v hv).2) (opow_log_le_self ω hv0)⟩
  have hQW : ∀ v, Q v → v < OmTwo := fun v hv => uf_cl_lt_Om2 hx1 hv
  obtain ⟨-, hBm, -⟩ := ufB_lev (S := S) (n := n) Q hQD hQdec hQW γ hγ hc
  exact ⟨hD, h7, hBm, e, h2, h3, h4, h5, h6⟩

end Googology.Trans.PoR.InaccPsi.R2.Uf
