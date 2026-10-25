import Googology.Trans.PoR.InaccPsi.R2.UdMS

/-!
# The step, the ladder and the base at every exponent below `Γ₂`; the level systems up to every limit `E_b < Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`, `H_λ = cdHull S λ`,
`G = φ(Ω₂, 1)`, `Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)`, weak prefixes `Ua.UaPD`.

* `udStepLad` (**THE STEP AND THE LADDER AT EVERY EXPONENT `1 ≤ e < Γ₂` OF `H_λ`, FROM EVERY WEAK PREFIX**:
  limits by `Ud.udMS`);
* `udBase0` (**the base `W^e·c`, image `Ω^{T e}·Θ c`, for every `1 ≤ e < Γ₂`**), `udPfx`;
* `udLevHi` (**the own data and the level statement of every level `G ≤ E < Γ₂`** with the image `T E`);
* `udLS` (**`St.StLS S λ E_b T` for every limit `E_b < Γ₂`**), `udLSX` (at `E_b = X_k`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ud

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE STEP AND THE LADDER AT EVERY EXPONENT `1 ≤ e < Γ₂` OF `H_λ`, FROM EVERY WEAK PREFIX.** -/
theorem udStepLad : ∀ e, e ∈ cdHull S l → 1 ≤ e → e < uaGam → UaStepX S l e ∧ UaLadX S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH he1 heE
  have heG : e < uaGam := heE
  have hfin : UaStepX S l e → UaStepX S l e ∧ UaLadX S l e := fun hS =>
    ⟨hS, uaLad_of_step hl hX heH he1 heG hS⟩
  refine hfin ?_
  rcases lt_or_ge e (veblen (Om (1 + 1)) 1) with hlt | hge
  · exact uaStepLow hl hX heH he1 hlt
  rcases hge.lt_or_eq with hgt | heq
  swap
  · rw [← heq]; exact uaStepG hl hX
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · exact absurd he1 (by rw [h0]; exact not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at he0
    subst he0
    have he0H : e0 ∈ cdHull S l := mem_of_add_one_mem heH
    have he0G : veblen (Om (1 + 1)) 1 ≤ e0 := by
      by_contra hc
      push Not at hc
      exact absurd hgt (not_lt.2 (Order.add_one_le_of_lt hc))
    have he01 : 1 ≤ e0 := (Order.one_le_iff_pos.2 veblen_pos).trans he0G
    exact uaStep_succ hl hX he0H heG (IH e0 (lt_add_one e0) he0H he01 ((lt_add_one e0).trans heE)).2
  · have hIH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < e → UaStepX S l m := fun m hmH hm1 hme =>
      (IH m hme hmH hm1 (hme.trans heE)).1
    have hMS := udMS hl hX e heH hlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
    rw [zero_add] at hMS
    rcases hMS with hA | hB
    · exact uaStep_MA hl hX heH he1 heG hA hIH
    · exact uaStep_MB hl hX heH he1 heG hB hIH

/-- **THE BASE**: `W^e·c` with the image `Ω^{T e}·Θ c` is a prefix (`1 ≤ e < Γ₂`, codes `1 ≤ c < Ω₂`). -/
theorem udBase0 {e c : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heE : e < uaGam)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) :
    StPD S l (leWe e * c) (leOe (uaTh S l e) * gxTh (upsilon l) (ldAtR S l) c) := by
  have h := (udStepLad hl hX e heH he1 heE).2 0 0 (uaPD_zero l) (dvd_zero _) (dvd_zero _) c hc hc1 hcW
  rwa [zero_add, zero_add] at h

/-- **Every `r < Γ₂` of `H_λ` with `Ω₂ ∣ r` adds to a weak prefix**: `(P + r, P̂ + T r)` is a weak prefix. -/
theorem udPfx : ∀ r, r ∈ cdHull S l → Om (1 + 1) ∣ r → r < uaGam → ∀ P Ph, UaPD S l P Ph →
    leWe (sgLW r + 1) ∣ P → leOe (uaTh S l (sgLW r) + 1) ∣ Ph → UaPD S l (P + r) (Ph + uaTh S l r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hdr hrE P Ph hD hdP hdh
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, uaTh_zero, add_zero]; exact hD
  have h0 : 0 < r := pos_iff_ne_zero.2 hr0
  have hrG : r < uaGam := hrE
  obtain ⟨hgH, hgr, hdc, hd1, hdW, hr'H, hr'g, hrdec, hTr, -⟩ := uaParts hl hX hrH h0 hrG
  set g := sgLW r with hg
  set d := r / leWe g with hd_def
  set r' := r % leWe g with hr'_def
  have hg1 : 1 ≤ g := by
    by_contra hc
    push Not at hc
    rw [Order.lt_one_iff] at hc
    have h1 : r < leWe (g + 1) := sgLW_lt r
    rw [hc, zero_add, leWe_one] at h1
    obtain ⟨q, hq⟩ := hdr
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hr0 hq
    have : Om (1 + 1) ≤ r := by
      rw [hq]; exact (mul_one _).symm.le.trans (mul_le_mul_left' (Order.one_le_iff_ne_zero.2 hq0) _)
    exact absurd h1 (not_lt.2 this)
  have hgE : g < uaGam := hgr.trans_lt hrE
  have hD1 := (udStepLad hl hX g hgH hg1 hgE).2 P Ph hD hdP hdh d hdc hd1 hdW
  have hr'r : r' < r := hr'g.trans_le (sgLW_le h0)
  have hdr' : Om (1 + 1) ∣ r' := by
    have h := tuDvd_mod (e := r) (f := 1) (g := g) (by rw [leWe_one]; exact hdr) hg1
    rwa [leWe_one] at h
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · rw [hTr, hrdec, hr'0, add_zero, uaTh_zero, add_zero]
    exact uaPD_of hD1
  have hs' : sgLW r' < g := tuLogW_lt hr'0 hr'g
  have hs'H : sgLW r' ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hr'H)
  have hdP' : leWe (sgLW r' + 1) ∣ P + leWe g * d := by
    refine dvd_add ((leWe_dvd ((Order.add_one_le_of_lt hs').trans le_self_add)).trans hdP) ?_
    exact (leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_mul_right _ _)
  have hTs : uaTh S l (sgLW r') < uaTh S l g := uaLt hl hX hs'H hgH (hgr.trans_lt hrG) hs'
  have hdh' : leOe (uaTh S l (sgLW r') + 1) ∣ Ph + leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) d := by
    refine dvd_add ((tuOe_dvd ((Order.add_one_le_of_lt hTs).trans le_self_add)).trans hdh) ?_
    exact (tuOe_dvd (Order.add_one_le_of_lt hTs)).trans (dvd_mul_right _ _)
  have h := IH r' hr'r hr'H hdr' (hr'r.trans hrE) _ _ (uaPD_of hD1) hdP' hdh'
  rw [hTr, hrdec, ← add_assoc, ← add_assoc]
  exact h

/-- **The own data and the level statement of every level `G ≤ E < Γ₂` of `H_λ`** (image `T E`). -/
theorem udLevHi {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hGE : veblen (Om (1 + 1)) 1 ≤ E) (hE : E < uaGam) :
    ScOwP S l (SnCL S E) E (uaTh S l E) ∧ ScLev S l (SnCL S E) E (uaTh S l E) := by
  have hEG : E < uaGam := hE
  set P := leWe 1 * (E / leWe 1) with hP_def
  set c := E % leWe 1 with hc_def
  have hW1 : leWe 1 = Om (1 + 1) := leWe_one
  have hPH : P ∈ cdHull S l := Ts.ts_mod_mem le_rfl E hEH
  have hcH : c ∈ cdHull S l := leModP_mem (Om (1 + 1) * 1) hEH
  have hdec : E = P + c := (Ordinal.div_add_mod E _).symm
  have hcW : c < Om (1 + 1) := by rw [← hW1]; exact Ordinal.mod_lt _ (leWe_pos _).ne'
  have hcc : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hcW).1 hcH
  have hPd : Om (1 + 1) ∣ P := by rw [← hW1]; exact dvd_mul_right _ _
  have hPE : P ≤ E := by rw [hdec]; exact le_self_add
  have hGP : veblen (Om (1 + 1)) 1 ≤ P := by
    by_contra hc
    push Not at hc
    have h1 : E < P + Om (1 + 1) := by rw [hdec]; exact (add_lt_add_iff_left P).2 hcW
    have h2 : P + Om (1 + 1) < veblen (Om (1 + 1)) 1 := txG_prin hc tgOm_lt_G
    exact absurd (h1.trans h2) (not_lt.2 hGE)
  have hDP := udPfx hl hX P hPH hPd (hPE.trans_lt hE) 0 0 (uaPD_zero l) (dvd_zero _) (dvd_zero _)
  rw [zero_add, zero_add] at hDP
  have hD : StPD S l P (uaTh S l P) := by
    rcases hDP with h | ⟨h0, -⟩
    · exact h
    · exact absurd (h0 ▸ hGP) (not_le.2 veblen_pos)
  have hTE : uaTh S l E = uaTh S l P + gxTh (upsilon l) (ldAtR S l) c := by
    have hsc : sgLW c = 0 := by
      unfold sgLW
      exact Ordinal.div_eq_zero_of_lt ((log_le_self ω c).trans_lt hcW)
    have hcG : c < veblen (Om (1 + 1)) 1 := hcW.trans tgOm_lt_G
    rw [hdec, uaAdd hl hX P hPH c hcH (hdec ▸ hEG) (by rw [hsc, zero_add, hW1]; exact hPd), uaTh_lt hcG,
      tuThL_code hl hX hcW]
  rw [hTE, hdec]
  exact ⟨stPreOwP hl hX hD hcc hcW, stPreLev hl hX hD c hcc hcW⟩

/-- **THE LEVEL SYSTEM UP TO EVERY LIMIT `E_b < Γ₂` WITH THE IMAGE `T`.** -/
theorem udLS {Eb : Ordinal.{0}} (hEb : IsSuccLimit Eb) (hEbG : Eb < uaGam) : StLS S l Eb (uaTh S) := by
  have hT := tjLS (S := S) hl hX
  refine ⟨hEb, hEbG.trans_le uaGam_le_G3, fun E hEH _ hE => uaLtG1 hl hX E hEH (hE.trans hEbG), ?_, ?_⟩
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [uaTh_lt hlt]; exact hT.own E hEH h1 hlt
    · exact (udLevHi hl hX hEH hge (hE.trans hEbG)).1
  · intro E hEH h1 hE
    rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hlt | hge
    · rw [uaTh_lt hlt]; exact hT.lev E hEH h1 hlt
    · exact (udLevHi hl hX hEH hge (hE.trans hEbG)).2

/-- **THE LEVEL SYSTEM UP TO `X_k`** (`Ud.udX`). -/
theorem udLSX (k : ℕ) : StLS S l (udX k) (uaTh S) := udLS hl hX (udX_lim k) (udX_lt k)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ud
