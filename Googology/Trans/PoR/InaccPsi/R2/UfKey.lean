import Googology.Trans.PoR.InaccPsi.R2.UfM

/-!
# The key lemma below `B₂`: the collapse of an argument with code components is a code

`ψ = ψ_{Ω₂}`, `X = Tl.tlX`, `B₂ = Uc.ucB = ψ(ε_{Ω₂+1})`, `H_λ = Uc.ucH λ`, `UcCl q` the codes over `q`, `UfP P x`
(every hereditary base-`Ω₂` component of `x` is in `P`).  An argument `e` is *own* when `e ∈ Cl(e, ψ(e))`.

* `uf_first_base` (**the base of the first value**: for `1 ≤ λ < E₂` the own argument of `H_λ(0)` is `K + Ω₂^λ` with
  `K` own, `K < E₂`, and the `λ`-digit of `K` zero; `ψ(K)` is the largest strongly critical point `≤ ucC λ`, or
  `K = 0`);
* `uf_own_code` (**`ψ(e) < B₂` is a code over `q ≤ Ω₁` when `e` is own and every component of `e` is a code over
  `q`**, by the run `e = B + Ω₂^λ·D` of `Uf.ufRun`; below `X` by `Tz.tz_own_code`);
* `uf_key` (**`ψ(e) < B₂` is a code over `q` for every `e` whose components are codes over `q` or `≥ B₂`**:
  `ψ(e) = ψ(M(e))`, `M(e)` own with code components by `Uf.uf_M_cd`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl

variable {S : InaccSeq.{0}}

/-- **The base of the first value of `H_λ`**: for `1 ≤ λ < E₂` and an own `B` with `ψ(B) = H_λ(0)`,
`B = K + Ω₂^λ` with `K` own, `K < E₂`, the `λ`-digit of `K` zero, and `ψ(K) ≤ ucC λ < ψ(K + 1)` or `K = 0`,
`ucC λ < ψ(1)`. -/
theorem uf_first_base {l B : Ordinal.{0}} (hl1 : 1 ≤ l) (hlE : l < ucE) (hlB : ucH l 0 < ucB)
    (hownB : B ∈ S.CSet B (S.psi B (Om (1 + 1)))) (hc : ucH l 0 = S.psi B (Om (1 + 1))) :
    ∃ K, K ∈ S.CSet K (S.psi K (Om (1 + 1))) ∧ K < ucE ∧ B = K + OmTwo ^ l ∧ K / OmTwo ^ l % OmTwo = 0 ∧
      ((K = 0 ∧ ucC l < S.psi 1 (Om (1 + 1))) ∨
        (S.psi K (Om (1 + 1)) ≤ ucC l ∧ ucC l < S.psi (K + 1) (Om (1 + 1)) ∧
          ∀ s, SC s → Om1 < s → s ≤ ucC l → s ≤ S.psi K (Om (1 + 1)))) := by
  have h0E : (0 : Ordinal.{0}) < ucE := uc_SC_Om2.1.trans ucE_gt
  by_cases hm1 : ucC l < S.psi 1 (Om (1 + 1))
  · obtain ⟨h0eq, hown0, -⟩ := uf_least0 (S := S) hl1 hlE (CSet.zero_mem _ _) h0E (Or.inr rfl)
      (by rw [zero_add]; exact hm1)
    have hBK : B = 0 + OmTwo ^ l := Ts.ts_own_unique hownB hown0 (by rw [← hc, h0eq])
    exact ⟨0, CSet.zero_mem _ _, h0E, hBK, by rw [Ordinal.zero_div, Ordinal.zero_mod], Or.inl ⟨rfl, hm1⟩⟩
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
  have hvB : v < ucB := hvm.trans_lt ((ucH_C_lt l 0).trans hlB)
  obtain ⟨K, hownK, hKE, hψK⟩ := uc_own_of_SC (S := S) hvS (by rw [← uf_Om1]; exact hv1) hvB
  have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono (S := S) (InR_Om_succ 1) le_self_add).2 hownK) (CSet.one_mem _ _)
  have hmK : m < S.psi (K + 1) (Om (1 + 1)) := by
    by_contra hc'
    push Not at hc'
    have h1 := hvmax _ (Ts.ts_psi_SC _) (by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi _) hc'
    rw [← hψK] at h1
    exact absurd (Ts.ts_psi_lt_of_own hownK (lt_add_one K)) (not_lt.2 h1)
  obtain ⟨h0eq, hownE, -⟩ := uf_least0 (S := S) hl1 hlE hownK hKE (Or.inl (by rw [hψK]; exact hvm)) hmK
  have hBK : B = K + OmTwo ^ l := Ts.ts_own_unique hownB hownE (by rw [← hc, h0eq])
  have hdig : K / OmTwo ^ l % OmTwo = 0 := by
    by_contra hd
    have h1 := uf_dig_C hKE l hd
    have h2 : ucC K < S.psi K (Om (1 + 1)) :=
      (ucC_lt_iff (Ts.ts_psi_SC K).1 K).2 (uc_own_comps hownK hKE)
    rw [hψK] at h2
    exact absurd ((h1.trans_lt h2).trans_le hvm) (lt_irrefl _)
  exact ⟨K, hownK, hKE, hBK, hdig, Or.inr ⟨by rw [hψK]; exact hvm, hmK,
    fun s a b c => by rw [hψK]; exact hvmax s a b c⟩⟩

/-- `K + Ω₂^λ = T + Ω₂^λ` with `T = Ω₂^λ·(K / Ω₂^λ)`, and `Ω₂^{λ+1} ∣ T` when the `λ`-digit of `K` is zero. -/
theorem uf_base_split {K l : Ordinal.{0}} (hdig : K / OmTwo ^ l % OmTwo = 0) :
    K + OmTwo ^ l = OmTwo ^ l * (K / OmTwo ^ l) + OmTwo ^ l ∧ OmTwo ^ (l + 1) ∣ OmTwo ^ l * (K / OmTwo ^ l) := by
  have hu0 : OmTwo ^ l ≠ 0 := (uc_W_pos l).ne'
  refine ⟨?_, ?_⟩
  · calc K + OmTwo ^ l = OmTwo ^ l * (K / OmTwo ^ l) + (K % OmTwo ^ l + OmTwo ^ l) := by
          rw [← add_assoc, Ordinal.div_add_mod]
      _ = OmTwo ^ l * (K / OmTwo ^ l) + OmTwo ^ l := by
          have := Rd.rdk_absorb (uc_W_indec l) (Ordinal.mod_lt K hu0) (le_refl (1 : Ordinal.{0}))
          rw [mul_one] at this; rw [this]
  · have h := Ordinal.div_add_mod (K / OmTwo ^ l) OmTwo
    rw [hdig, add_zero] at h
    rw [← h, ← mul_assoc, ← uc_W_succ]
    exact dvd_mul_right _ _

/-- **`ψ(e) < B₂` is a code over `q` when `e` is own and every component of `e` is a code over `q`** (`q` strongly
critical, `q ≤ Ω₁`). -/
theorem uf_own_code {q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) :
    ∀ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) → UfP (UcCl q) e → S.psi e (Om (1 + 1)) < ucB →
      UcCl q (S.psi e (Om (1 + 1))) := by
  have hO1S : SC (Om1 : Ordinal.{0}) := by rw [uf_Om1]; exact Ph.ph_SC_Om1
  have hP0 : UcCl q 0 := UcCl.zero hq.1
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro hown hP hsB
  set s := S.psi e (Om (1 + 1)) with hsdef
  have hsS : SC s := Ts.ts_psi_SC e
  have hs1 : Om1 < s := by rw [uf_Om1]; exact Ts.ts_Om1_lt_psi e
  have heE : e < ucE := uf_own_lt_E hown hsB
  have hcomps : UcLt s e := uc_own_comps hown heE
  rcases lt_or_ge s tlX with hsX | hXs
  · -- below `X`
    have hWown := Ts.tsW_mem (S := S) (Le.leWe (Om (1 + 1))) (S.psi (Le.leWe (Om (1 + 1))) (Om (1 + 1)))
    have heW : e < Le.leWe (Om (1 + 1)) := uf_own_lt hown hWown (by rw [Ts.ts_psiW_eq_X]; exact hsX)
    have hPt : UfP (TlCl q) e := fun c hc => uc_cl_lt_X (hP c hc) ((hcomps c hc).trans hsX)
    have hG := uf_tzG (TlCl.zero hq.1) e heW hPt
    exact UcCl.tl (Tz.tz_own_code hq e hown hG hsX)
  -- at or above `X`: the normal form and the run
  have hne := uc_nf_of_lt hsS hs1 hsB
  obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hsS hs1 hne
  obtain ⟨hnf, hyz⟩ := uc_nf hsS hs1 hne
  generalize hldef : ucLev s = l at hlE hlv hnf hyz
  generalize hydef : ucI l s = y at hnf hyz
  have hyB : y < ucB := hyz.trans hsB
  have hyc : UcCl Om1 y := uc_code Rj.rj_Om1_pos y hyB (ucDat_lt_Om1 y)
  obtain ⟨B, c, D, hownB, hBE, hdvd, hc, hcD, hD2, hval, -, -, hcase⟩ :=
    ufRun (S := S) hO1S le_rfl hlE hyc (by rw [hnf]; exact hyz) (by rw [hnf]; exact hsB)
  obtain ⟨hψe, -, howne, -⟩ := ufRun_eq hlE hownB hBE hdvd hc hD2 hval
  rw [hcD, hnf] at hψe
  have hee : e = B + OmTwo ^ l * D := Ts.ts_own_unique hown howne (by rw [hψe])
  have hcodes : (∀ x ∈ ucComps l, UcCl q x) ∧ UcCl q c ∧ UcCl q D := by
    rcases hcase with hc0 | ⟨hc1, hcf, hdvd1, -⟩
    · subst hc0
      rcases eq_or_ne l 0 with hl0 | hl0
      · subst hl0
        have hψ : S.psi B (Om (1 + 1)) = S.psi 0 (Om (1 + 1)) := by rw [← hc, uf_H0]
        have hB0 : B = 0 := Ts.ts_own_unique hownB (CSet.zero_mem _ _) hψ
        rw [hB0, zero_add, opow_zero, one_mul] at hee
        rw [hee] at hP
        refine ⟨fun x hx => ?_, hP0, (ufP_small hD2).1 hP⟩
        rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hx; rw [hx]; exact hP0
      have hl1 : 1 ≤ l := Order.one_le_iff_ne_zero.2 hl0
      have h0B : ucH l 0 < ucB := ((uf_H_le_iff l).2 zero_le).trans_lt (by rw [hnf]; exact hsB)
      obtain ⟨K, -, -, hBK, hdig, -⟩ := uf_first_base (S := S) hl1 hlE h0B hownB hc
      obtain ⟨hsplit, hTd⟩ := uf_base_split hdig
      set T := OmTwo ^ l * (K / OmTwo ^ l) with hTdef
      have he2 : e = T + OmTwo ^ l * (1 + D) := by rw [hee, hBK, hsplit, mul_add, mul_one, add_assoc]
      have h1D2 : 1 + D < OmTwo := (Lq.lq_SC_indec uc_SC_Om2).add_lt uc_one_lt_Om2 hD2
      have hlt : OmTwo ^ l * (1 + D) < OmTwo ^ (l + 1) := by
        rw [uc_W_succ]; exact (mul_lt_mul_iff_right₀ (uc_W_pos l)).2 h1D2
      have hc1 := ufP_concat (P := UcCl q) hP0 T (OmTwo ^ l * (1 + D)) (l + 1) hTd hlt (by rw [← he2]; exact heE)
      rw [← he2] at hc1
      have h2 := (hc1.1 hP).2
      have hcn := ufP_cnf (P := UcCl q) hl1 (pos_iff_ne_zero.1 (zero_lt_one.trans_le le_self_add)) h1D2
        (uc_W_pos l) (by rw [add_zero]; exact le_add_self.trans_lt (by rw [← he2]; exact heE))
      rw [add_zero] at hcn
      obtain ⟨hl', h1D, -⟩ := hcn.1 h2
      have hD := (ucDec hq hq1 (1 + D) h1D).1 1 (UcCl.one hq.1) le_self_add
      rw [Ordinal.add_sub_cancel] at hD
      exact ⟨hl', hP0, hD⟩
    · have hD0 : D ≠ 0 := by
        rintro rfl
        rw [add_zero] at hcD
        have h : y < ucH l y := by rw [hnf]; exact hyz
        rw [← hcD, hcf] at h
        exact lt_irrefl _ h
      have hlt : OmTwo ^ l * D < OmTwo ^ (l + 1) := by
        rw [uc_W_succ]; exact (mul_lt_mul_iff_right₀ (uc_W_pos l)).2 hD2
      have hc1 := ufP_concat (P := UcCl q) hP0 B (OmTwo ^ l * D) (l + 1) hdvd1 hlt (by rw [← hee]; exact heE)
      rw [← hee] at hc1
      obtain ⟨hPB, h2⟩ := hc1.1 hP
      have hBe : B < e := by
        rw [hee]; exact lt_add_of_pos_right _ (mul_pos (uc_W_pos l) (pos_iff_ne_zero.2 hD0))
      have hψB : S.psi B (Om (1 + 1)) = c := by rw [← hc, hcf]
      have hcB : c < ucB := (le_self_add.trans_eq hcD).trans_lt hyB
      have hcc := IH B hBe hownB hPB (by rw [hψB]; exact hcB)
      rw [hψB] at hcc
      rcases eq_or_ne l 0 with hl0 | hl0
      · subst hl0
        rw [opow_zero, one_mul] at h2
        refine ⟨fun x hx => ?_, hcc, (ufP_small hD2).1 h2⟩
        rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hx; rw [hx]; exact hP0
      · have hcn := ufP_cnf (P := UcCl q) (Order.one_le_iff_ne_zero.2 hl0) hD0 hD2 (uc_W_pos l)
          (by rw [add_zero]; exact le_add_self.trans_lt (by rw [← hee]; exact heE))
        rw [add_zero] at hcn
        obtain ⟨hl', hD', -⟩ := hcn.1 h2
        exact ⟨hl', hcc, hD'⟩
  obtain ⟨hcl, hcc, hDc⟩ := hcodes
  rw [← hnf, ← hcD]
  exact UcCl.hatom hlE hcl (UcCl.add hcc hDc) (by rw [hcD, hnf]; exact hXs)

/-- **The key lemma below `B₂`**: for `e` whose components are codes over `q` or `≥ B₂`, `ψ(e) < B₂` is a code over
`q` (`q` strongly critical, `q ≤ Ω₁`). -/
theorem uf_key {q : Ordinal.{0}} (hq : SC q) (hq1 : q ≤ Om1) {e : Ordinal.{0}}
    (hG : UfP (fun c => c < ucB → UcCl q c) e) (hsB : S.psi e (Om (1 + 1)) < ucB) :
    UcCl q (S.psi e (Om (1 + 1))) := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  set s := S.psi e (Om (1 + 1)) with hsdef
  have heE : e < ucE := by
    by_contra hc
    push Not at hc
    have := (psi_mono (S := S) hκ hc).1
    rw [uc_psiE_eq_B] at this
    exact absurd hsB (not_lt.2 this)
  have heL : e < S.Lam := heE.trans uf_E_lt_Lam
  have hψm : S.psi (S.M e s e) (Om (1 + 1)) = s := psi_M_eq hκ heL
  have hownm := M_mem_self (S := S) hκ heL
  rw [hψm] at hownm
  have hsS : SC s := Ts.ts_psi_SC e
  have hs1 : Om 1 < s := Ts.ts_Om1_lt_psi e
  have hs2 : s < OmTwo := by rw [uf_Om2]; exact Ts.ts_psi_lt e
  have hR : ∀ x ∈ S.CSet e s, UcLt s x := uc_hull hsS hs1 hs2 heE.le fun e' he' heC _ =>
    lt_psi_of_mem hκ (CSet.psi_mem he' hκ (mem_CSet_psi hκ e) heC) (psi_lt hκ _)
  have hownm' : S.M e s e ∈ S.CSet (S.M e s e) (S.psi (S.M e s e) (Om (1 + 1))) := by rw [hψm]; exact hownm
  have hME : S.M e s e < ucE := uf_own_lt_E hownm' (by rw [hψm]; exact hsB)
  have hcd := uf_M_cd (S := S) hsS hs1 hs2 hR (P := fun c => c < ucB → UcCl q c) (fun _ => UcCl.zero hq.1)
    (fun _ => UcCl.one hq.1) (fun z hz h => UcCl.add (hz ((lt_add_one z).trans h)) (UcCl.one hq.1)) e heE hG hME
  have hcomp : UcLt s (S.M e s e) := by
    have := uc_own_comps hownm' hME; rwa [hψm] at this
  have hP' : UfP (UcCl q) (S.M e s e) := fun c hc => hcd c hc ((hcomp c hc).trans hsB)
  have := uf_own_code hq hq1 (S.M e s e) hownm' hP' (by rw [hψm]; exact hsB)
  rwa [hψm] at this

end Googology.Trans.PoR.InaccPsi.R2.Uf
