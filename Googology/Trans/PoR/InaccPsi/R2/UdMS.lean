import Googology.Trans.PoR.InaccPsi.R2.UdArg

/-!
# Every limit exponent below `Γ₂` has a member system

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`,
`Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)`, member systems `Ua.UaMA`, `Ua.UaMB`.

* `udNodeHi` (**every node `φ(a, y) < Γ₂` with a level `a > Ω₂` has a member system**, given those of `a` and `y`
  when they are limits: towers at successor levels (`Ud.udMA_succ`, `Ud.udMA_zero`), the members of the level at
  limit levels (`Ud.udMA_levLim`, `Ud.udMA_lev0`, …), the members of the argument at limit arguments
  (`Ud.udMA_argLim`, …));
* `udNodeAll` (**every node `G ≤ r < Γ₂`**: a code level in its window by `Ua.uaNodeMS`, the level `Ω₂` by
  `Ua.uaNodeW`, a level above `Ω₂` by `udNodeHi`);
* `udMS` (**EVERY LIMIT EXPONENT `e + r < Γ₂` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM**; `Ua.uaMS3` is
  the bound `X₃`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ud

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu
  Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Every node `φ(a, y) < Γ₂` with a level `a > Ω₂` has a member system** (given those of `a` and `y` when they
are limits). -/
theorem udNodeHi {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hyH : y ∈ cdHull S l) (hΩa : Om (1 + 1) < a)
    (hyE : y < veblen a y) (hEG : veblen a y < uaGam)
    (IHa : IsSuccLimit a → UaMA S l a ∨ UaMB S l a) (IHy : IsSuccLimit y → UaMA S l y ∨ UaMB S l y) :
    UaMA S l (veblen a y) ∨ UaMB S l (veblen a y) := by
  rcases zero_or_succ_or_isSuccLimit y with hy0 | ⟨y', hy'⟩ | hyl
  rotate_left
  · -- a successor argument
    rw [succ_eq_add_one] at hy'
    subst hy'
    have hy'H : y' ∈ cdHull S l := mem_of_add_one_mem hyH
    rcases zero_or_succ_or_isSuccLimit a with ha0 | ⟨a', ha'⟩ | hal
    · rw [ha0] at hΩa; exact absurd hΩa (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at ha'
      subst ha'
      exact Or.inl (udMA_succ hl hX (mem_of_add_one_mem haH) (Order.lt_add_one_iff.1 hΩa) hy'H hEG)
    · rcases IHa hal with hA | hB
      · exact Or.inl (udMA_levLim hl hX haH hΩa hal hy'H hEG hA)
      · exact Or.inr (udMB_levLim hl hX haH hΩa hal hy'H hEG hB)
  · -- a limit argument
    rcases IHy hyl with hA | hB
    · exact Or.inl (udMA_argLim hl hX haH hΩa hyH hyl hyE hEG hA)
    · exact Or.inr (udMB_argLim hl hX haH hΩa hyH hyl hyE hEG hB)
  · -- the argument `0`
    subst hy0
    rcases zero_or_succ_or_isSuccLimit a with ha0 | ⟨a', ha'⟩ | hal
    · rw [ha0] at hΩa; exact absurd hΩa (not_lt.2 zero_le)
    · rw [succ_eq_add_one] at ha'
      subst ha'
      exact Or.inl (udMA_zero hl hX (mem_of_add_one_mem haH) (Order.lt_add_one_iff.1 hΩa) hEG)
    · rcases IHa hal with hA | hB
      · exact Or.inl (udMA_lev0 hl hX haH hΩa hal hEG hA)
      · exact Or.inr (udMB_lev0 hl hX haH hΩa hal hEG hB)

/-- **The member system of a node `G ≤ r < Γ₂`.** -/
theorem udNodeAll {r : Ordinal.{0}} (hrH : r ∈ cdHull S l) (hGr : veblen (Om (1 + 1)) 1 ≤ r) (hrG : r < uaGam)
    (hrs : ¬ sgLW r < r)
    (IHa : IsSuccLimit (invVeblen₁ r) → UaMA S l (invVeblen₁ r) ∨ UaMB S l (invVeblen₁ r))
    (IH : IsSuccLimit (invVeblen₂ r) → UaMA S l (invVeblen₂ r) ∨ UaMB S l (invVeblen₂ r)) :
    UaMA S l r ∨ UaMB S l r := by
  obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := uaNode hGr hrG hrs
  set a := invVeblen₁ r with ha_def
  set y := invVeblen₂ r with hy_def
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
  rcases lt_trichotomy a (Om (1 + 1)) with haW | haW | haW
  · -- a code level: the window of `r`
    have hΩr : veblen (Om (1 + 1)) 0 ≤ r := by
      rw [ldOm2_SC.veblen_zero]; exact tgOm_lt_G.le.trans hGr
    obtain ⟨u, huH, hu1', hu2'⟩ := txHull_idx hrH hΩr
    have hne : veblen (Om (1 + 1)) u ≠ r := by
      intro he
      have hfix : veblen a r = r := by rw [← he]; exact veblen_veblen_of_lt haW _
      have : y = r := by
        have h2 : veblen a y = veblen a r := by rw [hv, hfix]
        exact veblen_injective a h2
      exact absurd (this ▸ hbE) (lt_irrefl _)
    have hu1 : 1 ≤ u := by
      by_contra hc
      push Not at hc
      rw [Order.lt_one_iff] at hc
      rw [hc, zero_add] at hu2'
      exact absurd hGr (not_le.2 hu2')
    have h := uaNodeMS hl hX hu1 huH hmem.1 (Order.one_le_iff_pos.2 ha0) haW hmem.2
      (by rw [hv]; exact lt_of_le_of_ne hu1' hne) (by rw [hv]; exact hu2') (by rw [hv]; exact hrG) IH
    rwa [hv] at h
  · -- the level `Ω₂`
    have hy1 : 1 ≤ y := by
      rw [Order.one_le_iff_ne_zero]
      intro h0
      rw [haW, h0, ldOm2_SC.veblen_zero] at hv
      rw [← hv] at hGr
      exact absurd hGr (not_le.2 tgOm_lt_G)
    have h := uaNodeW hl hX hmem.2 hy1 (by rw [← haW, hv]; exact hrG) IH
    rwa [← haW, hv] at h
  · -- a level above `Ω₂`
    have h := udNodeHi hl hX hmem.1 hmem.2 haW (by rw [hv]; exact hbE) (by rw [hv]; exact hrG) IHa IH
    rwa [hv] at h

/-- **EVERY LIMIT EXPONENT `e + r < Γ₂` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM.** -/
theorem udMS : ∀ r, r ∈ cdHull S l → IsSuccLimit r → ∀ e, e ∈ cdHull S l →
    e + r < uaGam → leWe (sgLW r + 1) ∣ e → UaMA S l (e + r) ∨ UaMB S l (e + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hrlim e heH hlt hd
  have hrE : r < uaGam := le_add_self.trans_lt hlt
  have hr0 : 0 < r := hrlim.bot_lt
  by_cases hrs : sgLW r < r
  swap
  · have hWr : leWe r = r := uaW_fix hr0 hrs
    have hsr : sgLW r = r := le_antisymm (txSg_le r) (not_lt.1 hrs)
    have hdr : leWe r ∣ e := (leWe_dvd (le_self_add : r ≤ r + 1)).trans (by rw [← hsr]; exact hd)
    have hlt' : e + leWe r < uaGam := by rw [hWr]; exact hlt
    have hMS : UaMA S l r ∨ UaMB S l r := by
      rcases lt_or_ge r (veblen (Om (1 + 1)) 1) with hrG | hrG
      · have h := txMS hl hX r hrH hrlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
        rw [zero_add] at h
        rcases h with hA | hB
        · exact Or.inl (uaMA_of_tu hl hX hrG hA)
        · exact Or.inr (uaMB_of_tu hl hX hrG hB)
      obtain ⟨-, hv, -, haE, hbE, -, -⟩ := uaNode hrG hrE hrs
      have hmem := mem_of_veblen_mem (by rw [hv]; exact hrH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
      refine udNodeAll hl hX hrH hrG hrE hrs (fun hal => ?_) (fun hyl => ?_)
      · have h := IH _ haE hmem.1 hal 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact haE.trans hrE) (dvd_zero _)
        rwa [zero_add] at h
      · have h := IH _ hbE hmem.2 hyl 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hbE.trans hrE) (dvd_zero _)
        rwa [zero_add] at h
    rw [← hWr]
    rcases hMS with hA | hB
    · exact Or.inl (uaMA_lift hl hX heH hrH hdr hlt' hA)
    · exact Or.inr (uaMB_lift hl hX heH hrH hdr hlt' hB)
  obtain ⟨hfH, -, hcc, hc1, hcW, hr'H, hr'f, hrdec⟩ := uaBase hl hX hrH hr0
  have hfr : sgLW r < r := hrs
  set f := sgLW r with hf_def
  set c := r / leWe f with hc_def
  set r' := r % leWe f with hr'_def
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hcc
  have hdf : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hrc : r = leWe f * c := by rw [hr'0, add_zero] at hrdec; exact hrdec
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c1, hcs⟩ | hclim
    · exact absurd hc1 (by rw [h0]; exact not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hcs
      have hc1W : c1 < Om (1 + 1) := (lt_add_one c1).trans (hcs ▸ hcW)
      have hc1c : GxCl (upsilon l) (ldAtR S l) c1 := rqCode_pred hl hX (hcs ▸ hcc) (hcs ▸ hcW)
      have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1c
      have he2H : e + leWe f * c1 ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hc1H)
      have he2r : e + leWe f * c1 + leWe f = e + r := by rw [hrc, ← hcs, mul_add_one, add_assoc]
      have hd2 : leWe f ∣ e + leWe f * c1 := dvd_add hdf (dvd_mul_right _ _)
      have hlt2 : e + leWe f * c1 + leWe f < uaGam := he2r ▸ hlt
      rw [← he2r]
      rcases zero_or_succ_or_isSuccLimit f with hf0 | ⟨f1, hfs⟩ | hflim
      · exfalso
        have hrc1 : r = c1 + 1 := by rw [hrc, hf0, leWe_zero, one_mul, ← hcs]
        have h := hrlim.succ_lt (show c1 < r from hrc1 ▸ lt_add_one c1)
        rw [Order.succ_eq_add_one, ← hrc1] at h
        exact lt_irrefl _ h
      · rw [succ_eq_add_one] at hfs
        have hf1H : f1 ∈ cdHull S l := mem_of_add_one_mem (hfs ▸ hfH)
        rw [← hfs] at hd2 hlt2 he2H ⊢
        exact Or.inr (uaMB_succ hl hX he2H hf1H hd2 hlt2)
      · have hMSf := IH f hfr hfH hflim 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hfr.trans hrE)
          (dvd_zero _)
        rw [zero_add] at hMSf
        rcases hMSf with hA | hB
        · exact Or.inl (uaMA_lift hl hX he2H hfH hd2 hlt2 hA)
        · exact Or.inr (uaMB_lift hl hX he2H hfH hd2 hlt2 hB)
    · rw [hrc] at hlt ⊢
      exact Or.inl (uaMA_coef hl hX heH hfH hcc hclim hcW hd hlt)
  · have hr'lim : IsSuccLimit r' := by
      rcases zero_or_succ_or_isSuccLimit r' with h0 | ⟨r1, hr1⟩ | hl'
      · exact absurd h0 hr'0
      · exfalso
        rw [succ_eq_add_one] at hr1
        have hr2 : r = leWe f * c + r1 + 1 := by rw [add_assoc, hr1]; exact hrdec
        have h := hrlim.succ_lt (show leWe f * c + r1 < r from hr2 ▸ lt_add_one _)
        rw [Order.succ_eq_add_one, ← hr2] at h
        exact lt_irrefl _ h
      · exact hl'
    have hs' : sgLW r' < f := tuLogW_lt hr'0 hr'f
    have he2 : e + leWe f * c + r' = e + r := by
      conv_rhs => rw [hrdec]
      rw [add_assoc]
    have hr'r : r' < r := hr'f.trans_le (sgLW_le hr0)
    have h := IH r' hr'r hr'H hr'lim (e + leWe f * c) (CSet.add_mem heH (leMulWe_mem hfH hcH))
      (he2 ▸ hlt) ((leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_add hdf (dvd_mul_right _ _)))
    rwa [he2] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ud
