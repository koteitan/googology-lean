import Googology.Trans.PoR.InaccPsi.R2.UmStep

/-!
# The step and the ladder past `Γ₂` at every exponent below `Γ₂`, and the level statement past `Γ₂` at every
level `Ω₂ ≤ E < Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ua.uaTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`, `H_λ = cdHull S λ`,
`Γ₂ = Ua.uaGam = ψ_{Ω₃}(0)`, `G₁ = ψ_{Ω₂}(0)`, `X_k = Ud.udX k` (cofinal in `Γ₂`), `Y₃ = ψ_{Ω₃}(Ω₃)`.

**ONE INDUCTION FOR EVERY EXPONENT `1 ≤ e < Γ₂`** (`umStepLad`): `e = 1` by the next prefix `Um.umPreW` (and the
level `Ω₂` over every offset past `Γ₂`, `Um.umLev_W`, from `P = 0`), successors by `Um.umStep_succ`, limits by the
member systems of `Ud.udMS` (every limit below `Γ₂` has one) and `Um.umStep_MA`, `Um.umStep_MB`.  No case split by
ranges: the per-range systems of `St`, `Sq`, `Sw`, `Ta`, `Td`, `Tj`, `Tn`, `Tu`, `Tx`, `Ua`, `Ud` enter only
through their `Sc` data (the prefixes `St.StPD` of `Ud.udStepLad`); the level statements past `Γ₂` are proved
once.

* `umStepLad` (**THE STEP AND THE LADDER PAST `Γ₂` AT EVERY EXPONENT `1 ≤ e < Γ₂` OF `H_λ`**);
* `umPfx` (every `r < Γ₂` of `H_λ` with `Ω₂ ∣ r` adds to a weak prefix past `Γ₂`);
* `umLevHi` (**THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < Γ₂` OF `H_λ`**: `UjLev (CL E) E (T E)` with
  the own data);
* `umLevX` (`UjLev (CL X_k) (X_k) (T X_k)`, own predicate always true), `umGamLevHi`, `umGamReadHi` (**the
  readings `Θ(ψ_{Ω₂}(W^{Γ₂ + W^E})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{T E}})` for every `Ω₂ ≤ E < Γ₂` of `H_λ` with
  `CL E 0 Γ₂`**), `umGamReadX` (the same at `E = X_k`, no own hypothesis).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The step past `Γ₂` at `e = 1`**: `P + Ω₂` with the image `P̂ + Ω₁` from every weak prefix past `Γ₂`. -/
theorem umStepOne : UmStepX S l 1 := by
  have hT1 : uaTh S l 1 = 1 := by rw [uaThCode hl hX (gg_one_lt_of_SC ldOm2_SC), sqTh_one hl hX]
  have h1G : (1 : Ordinal.{0}) < uaGam := (gg_one_lt_of_SC ldOm2_SC).trans uaGam_spec.2
  intro P Ph hD hdP hdh
  rcases hD with hD | ⟨rfl, rfl⟩
  · rw [hT1, leWe_one, leOe_one]; exact umPreW hl hX hD
  · have hsc := (udStepLad hl hX 1 (CSet.one_mem _ _) le_rfl h1G).1 0 0 (uaPD_zero l) (dvd_zero _) (dvd_zero _)
    refine ⟨hsc, ?_⟩
    rw [hT1, leWe_one, leOe_one, zero_add, zero_add]
    exact umLevUp (umLev_W hl hX) (fun _ _ _ h hb => snCL_mono h hb le_rfl) (fun _ _ _ _ _ _ _ _ => trivial)

/-- **THE STEP AND THE LADDER PAST `Γ₂` AT EVERY EXPONENT `1 ≤ e < Γ₂` OF `H_λ`, FROM EVERY WEAK PREFIX PAST
`Γ₂`.** -/
theorem umStepLad : ∀ e, e ∈ cdHull S l → 1 ≤ e → e < uaGam → UmStepX S l e ∧ UmLadX S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH he1 heE
  have hfin : UmStepX S l e → UmStepX S l e ∧ UmLadX S l e := fun hS =>
    ⟨hS, umLad_of_step hl hX heH he1 heE hS⟩
  refine hfin ?_
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · exact absurd he1 (by rw [h0]; exact not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | h00
    · rw [zero_add]; exact umStepOne hl hX
    have he0H : e0 ∈ cdHull S l := mem_of_add_one_mem heH
    have he01 : 1 ≤ e0 := Order.one_le_iff_ne_zero.2 h00
    exact umStep_succ hl hX he0H heE (IH e0 (lt_add_one e0) he0H he01 ((lt_add_one e0).trans heE)).2
  · have hIH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < e → UmStepX S l m := fun m hmH hm1 hme =>
      (IH m hme hmH hm1 (hme.trans heE)).1
    have hMS := udMS hl hX e heH hlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
    rw [zero_add] at hMS
    rcases hMS with hA | hB
    · exact umStep_MA hl hX heH he1 heE hA hIH
    · exact umStep_MB hl hX heH he1 heE hB hIH

/-- **Every `r < Γ₂` of `H_λ` with `Ω₂ ∣ r` adds to a weak prefix past `Γ₂`.** -/
theorem umPfx : ∀ r, r ∈ cdHull S l → Om (1 + 1) ∣ r → r < uaGam → ∀ P Ph, UmPDw S l P Ph →
    leWe (sgLW r + 1) ∣ P → leOe (uaTh S l (sgLW r) + 1) ∣ Ph → UmPDw S l (P + r) (Ph + uaTh S l r) := by
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
      rw [hq]; exact (mul_one _).symm.le.trans (mul_le_mul_right (Order.one_le_iff_ne_zero.2 hq0) _)
    exact absurd h1 (not_lt.2 this)
  have hgE : g < uaGam := hgr.trans_lt hrE
  have hD1 := (umStepLad hl hX g hgH hg1 hgE).2 P Ph hD hdP hdh d hdc hd1 hdW
  have hr'r : r' < r := hr'g.trans_le (sgLW_le h0)
  have hdr' : Om (1 + 1) ∣ r' := by
    have h := tuDvd_mod (e := r) (f := 1) (g := g) (by rw [leWe_one]; exact hdr) hg1
    rwa [leWe_one] at h
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · rw [hTr, hrdec, hr'0, add_zero, uaTh_zero, add_zero]
    exact Or.inl hD1
  have hs' : sgLW r' < g := tuLogW_lt hr'0 hr'g
  have hs'H : sgLW r' ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hr'H)
  have hdP' : leWe (sgLW r' + 1) ∣ P + leWe g * d := by
    refine dvd_add ((leWe_dvd ((Order.add_one_le_of_lt hs').trans le_self_add)).trans hdP) ?_
    exact (leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_mul_right _ _)
  have hTs : uaTh S l (sgLW r') < uaTh S l g := uaLt hl hX hs'H hgH (hgr.trans_lt hrG) hs'
  have hdh' : leOe (uaTh S l (sgLW r') + 1) ∣ Ph + leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) d := by
    refine dvd_add ((tuOe_dvd ((Order.add_one_le_of_lt hTs).trans le_self_add)).trans hdh) ?_
    exact (tuOe_dvd (Order.add_one_le_of_lt hTs)).trans (dvd_mul_right _ _)
  have h := IH r' hr'r hr'H hdr' (hr'r.trans hrE) _ _ (Or.inl hD1) hdP' hdh'
  rw [hTr, hrdec, ← add_assoc, ← add_assoc]
  exact h


/-- **THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < Γ₂` OF `H_λ`** (image `T E`, own predicate `CL E`). -/
theorem umLevHi {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E) (hE : E < uaGam) :
    UjOwP S l (SnCL S E) E (uaTh S l E) ∧ UjLev S l (SnCL S E) E (uaTh S l E) := by
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
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hdec
    exact absurd (hdec ▸ hcW) (not_lt.2 hWE)
  have hDP := umPfx hl hX P hPH hPd (hPE.trans_lt hE) 0 0 (Or.inr ⟨rfl, rfl⟩) (dvd_zero _) (dvd_zero _)
  rw [zero_add, zero_add] at hDP
  have hD : UmPD S l P (uaTh S l P) := by
    rcases hDP with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 hP0
  have hTE : uaTh S l E = uaTh S l P + gxTh (upsilon l) (ldAtR S l) c := by
    have hsc : sgLW c = 0 := by
      unfold sgLW
      exact Ordinal.div_eq_zero_of_lt ((log_le_self ω c).trans_lt hcW)
    have hcG : c < veblen (Om (1 + 1)) 1 := hcW.trans tgOm_lt_G
    rw [hdec, uaAdd hl hX P hPH c hcH (hdec ▸ hEG) (by rw [hsc, zero_add, hW1]; exact hPd), uaTh_lt hcG,
      tuThL_code hl hX hcW]
  rw [hTE, hdec]
  exact ⟨umOwP_of_sc (stPreOwP hl hX hD.sc hcc hcW), umPreLev hl hX hD c hcc hcW⟩


/-- **`UjLev (CL X_k) X_k (T X_k)`** at every level `X_k` of the ladder to `Γ₂`. -/
theorem umLevX (k : ℕ) : UjOwP S l (SnCL S (udX k)) (udX k) (uaTh S l (udX k)) ∧
    UjLev S l (SnCL S (udX k)) (udX k) (uaTh S l (udX k)) :=
  umLevHi hl hX (ugX_mem _ _ k) (udX_gt k).le (udX_lt k)

/-- **`RvTop (Γ₂ + W^E) (G₁ + Ω^{T E}) 0`** at every base `b` with `CL E b Γ₂`, for every `Ω₂ ≤ E < Γ₂` of `H_λ`. -/
theorem umGamLevHi (b : Ordinal.{0}) {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < uaGam) (hcl : SnCL S E b uaGam) :
    RvTop S l b (uaGam + leWe E) (S.psi 0 (Om (1 + 1)) + leOe (uaTh S l E)) 0 := by
  obtain ⟨hd, hG3, hG⟩ := umGam_bounds (S := S) (by rw [← udGam_eq]; exact hE) (uaLtG1 hl hX E hEH hE)
  exact (umLevHi hl hX hEH hWE hE).2 b _ _ (ujGamOff hl hX b) hd hG3 hG hcl

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^E})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{T E}})`** for every `Ω₂ ≤ E < Γ₂` of `H_λ` with
`CL E 0 Γ₂`, at every restart `λ` with `A` own, `ψ_{Ω₁}(A) = ρ_λ`. -/
theorem umGamReadHi {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E) (hE : E < uaGam) (hcl : SnCL S E 0 uaGam) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + leWe E)) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe (uaTh S l E))) (Om 1) := by
  obtain ⟨-, hG3, -⟩ := umGam_bounds (S := S) (by rw [← udGam_eq]; exact hE) (uaLtG1 hl hX E hEH hE)
  exact ujRead0 (umGamLevHi hl hX 0 hEH hWE hE hcl) (lt_of_le_of_lt le_self_add hG3) hA hρ

/-- **`Θ_λ(ψ_{Ω₂}(W^{Γ₂ + W^{X_k}})) = ψ_{Ω₁}(A + 1 + Ω^{G₁ + Ω^{T X_k}})`** at every restart `λ` with `A` own,
`ψ_{Ω₁}(A) = ρ_λ` (no own hypothesis: `X_k` is a code over every strongly critical `Q`). -/
theorem umGamReadX {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)
    (k : ℕ) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (uaGam + leWe (udX k))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (S.psi 0 (Om (1 + 1)) + leOe (uaTh S l (udX k)))) (Om 1) :=
  umGamReadHi hl hX hA hρ (ugX_mem _ _ k) (udX_gt k).le (udX_lt k) (fun _ hQ _ => ugX_cl hQ k)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
