import Googology.Trans.PoR.InaccPsi.R2.UqMS

/-!
# One induction for every exponent below a bound `B ≤ Y₃`: the level statement past `Γ₂` at every `E < B`

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Ug.ugTh`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`CL₃ = Ug.UgCL`, `Γ₂ = Ua.uaGam`, `G₁ = ψ_{Ω₂}(0)`, `X_k = Ud.udX k`, `Y₃ = ψ_{Ω₃}(Ω₃)`,
`ε' = φ(1, Γ₂ + 1)` (the least `ε`-number above `Γ₂`).

* `uqStepLad` (**THE STEP AND THE LADDER AT EVERY EXPONENT `1 ≤ e < B` OF `H_λ`, FROM EVERY WEAK PREFIX**, given
  `Uq.UqFixMS S λ B`, `B ≤ Y₃`: one induction, successors by `Uq.uqStep_succ`, limits by `Uq.uqMS`,
  `Uq.uqStep_MA`, `Uq.uqStep_MB`);
* `uqPfx` (every `r < B` of `H_λ` with `Ω₂ ∣ r` adds to a weak prefix), `uqLevB` (**THE LEVEL STATEMENT PAST `Γ₂` AT
  EVERY LEVEL `Ω₂ ≤ E < B` OF `H_λ`**, image `T E`, own predicate `CL₃ E`, given `UqFixMS S λ B`);
* `uqW_eps`, `uqEps_next` (a `W`-fixed point `r > Γ₂` is `≥ ε'`), `uqMA_gam` (**the members `X_k` of `Γ₂`** with the
  image `G₁`), `uqFixEps` (**`UqFixMS S λ ε'` holds**: the only `W`-fixed limit in `[Γ₂, ε')` is `Γ₂`);
* `uqLevEps` (**UNCONDITIONAL: `UjLev (CL₃ E) E (T E)` at every level `Ω₂ ≤ E < ε'` of `H_λ`**, i.e. at every
  `E ∈ [Γ₂, ε_{Γ₂+1})` past `Γ₂`), `uqLevAll` (**every `Ω₂ ≤ E < Y₃` of `H_λ`, given `UqFixMS S λ Y₃`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

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
  Googology.Trans.PoR.InaccPsi.R2.Um

variable {S : InaccSeq.{0}}

/-- A `W`-fixed `r > 0` is an `ε`-number. -/
theorem uqW_eps {r : Ordinal.{0}} (h0 : 0 < r) (hs : ¬ sgLW r < r) : ω ^ r = r := by
  have hsE : sgLW r = r := le_antisymm (txSg_le r) (not_lt.1 hs)
  have hlogE : log ω r = r := by
    refine le_antisymm (log_le_self ω r) ?_
    calc r = sgLW r := hsE.symm
      _ ≤ log ω r := Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)
  refine le_antisymm ?_ (right_le_opow r one_lt_omega0)
  calc ω ^ r = ω ^ log ω r := by rw [hlogE]
    _ ≤ r := opow_log_le_self ω h0.ne'

/-- **An `ε`-number `r > Γ₂` is `≥ ε' = φ(1, Γ₂ + 1)`.** -/
theorem uqEps_next {r : Ordinal.{0}} (hε : ω ^ r = r) (hGr : uaGam < r) : veblen 1 (uaGam + 1) ≤ r := by
  have hv : veblen (invVeblen₁ r) (invVeblen₂ r) = r := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ r < r := by have := invVeblen₂_lt r; rwa [hε] at this
  have ha0 : 0 < invVeblen₁ r := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, veblen_zero_apply] at hv
    have : invVeblen₂ r = r := (opow_right_inj one_lt_omega0).1 (hv.trans hε.symm)
    exact absurd this hb.ne
  obtain ⟨β, hβ⟩ : ∃ β, veblen 1 β = r := by
    rcases (Order.one_le_iff_pos.2 ha0).lt_or_eq with h1 | h1
    · refine ⟨r, ?_⟩
      calc veblen 1 r = veblen 1 (veblen (invVeblen₁ r) (invVeblen₂ r)) := by rw [hv]
        _ = veblen (invVeblen₁ r) (invVeblen₂ r) := veblen_veblen_of_lt h1 _
        _ = r := hv
    · exact ⟨invVeblen₂ r, by rw [h1]; exact hv⟩
  have hG : veblen 1 uaGam = uaGam := uaGam_spec.1.veblen_right (gg_one_lt_of_SC uaGam_spec.1)
  have hGβ : uaGam < β := by
    rw [← hβ, ← hG] at hGr; exact (veblen_lt_veblen_iff_right).1 hGr
  rw [← hβ]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hGβ)

/-- `ε' = φ(1, Γ₂ + 1) < Y₃`, a limit. -/
theorem uqEps_lt_Y : veblen 1 (uaGam + 1) < ugY S :=
  uqY_SC.2 1 (gg_one_lt_of_SC uqY_SC) _ (uqY_SC.isSuccLimit.add_one_lt ujGam_lt_Y)

theorem uqEps_lim : IsSuccLimit (veblen 1 (uaGam + 1)) := taVeb_lim one_ne_zero

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE STEP AND THE LADDER AT EVERY EXPONENT `1 ≤ e < B` OF `H_λ`, FROM EVERY WEAK PREFIX** (`B ≤ Y₃`, given the
member systems at the `W`-fixed limits in `[Γ₂, B)`). -/
theorem uqStepLad {B : Ordinal.{0}} (hF : UqFixMS S l B) (hB : B ≤ ugY S) :
    ∀ e, e ∈ cdHull S l → 1 ≤ e → e < B → UqStepX S l e ∧ UqLadX S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH he1 heB
  have heY : e < ugY S := heB.trans_le hB
  have hfin : UqStepX S l e → UqStepX S l e ∧ UqLadX S l e := fun hS =>
    ⟨hS, uqLad_of_step hl hX heH he1 heY hS⟩
  refine hfin ?_
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · exact absurd he1 (by rw [h0]; exact not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | h00
    · rw [zero_add]; exact uqStepOne hl hX
    have he0H : e0 ∈ cdHull S l := mem_of_add_one_mem heH
    have he01 : 1 ≤ e0 := Order.one_le_iff_ne_zero.2 h00
    exact uqStep_succ hl hX he0H heY (IH e0 (lt_add_one e0) he0H he01 ((lt_add_one e0).trans heB)).2
  · have hIH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < e → UqStepX S l m := fun m hmH hm1 hme =>
      (IH m hme hmH hm1 (hme.trans heB)).1
    have hMS := uqMS hl hX hF hB e heH hlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
    rw [zero_add] at hMS
    rcases hMS with hA | hB'
    · exact uqStep_MA hl hX heH he1 heY hA hIH
    · exact uqStep_MB hl hX heH he1 heY hB' hIH

/-- **Every `r < B` of `H_λ` with `Ω₂ ∣ r` adds to a weak prefix**: `(P + r, P̂ + T r)`. -/
theorem uqPfx {B : Ordinal.{0}} (hF : UqFixMS S l B) (hB : B ≤ ugY S) (hBl : IsSuccLimit B) :
    ∀ r, r ∈ cdHull S l → Om (1 + 1) ∣ r → r < B → ∀ P Ph, UqPDw S l P Ph → P < ugY S →
    leWe (sgLW r + 1) ∣ P → leOe (ugTh S l (sgLW r) + 1) ∣ Ph → UqPDw S l (P + r) (Ph + ugTh S l r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hdr hrB P Ph hD hPY hdP hdh
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ugTh_zero, add_zero]; exact hD
  have h0 : 0 < r := pos_iff_ne_zero.2 hr0
  have hrY : r < ugY S := hrB.trans_le hB
  obtain ⟨hgH, hgr, hdc, hd1, hdW, hr'H, hr'g, hrdec, hTr, -⟩ := ugParts hl hX hrH h0 hrY
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
  have hgB : g < B := hgr.trans_lt hrB
  have hg1Y : g + 1 < ugY S := (hBl.add_one_lt hgB).trans_le hB
  have hW1Y : leWe (g + 1) < ugY S := (leWe_lt_SC uqY_SC uqW_lt_Y hg1Y).1
  have hPW : P + leWe (g + 1) < ugY S := uqY_SC.isPrincipal hPY hW1Y
  have hD1 := (uqStepLad hl hX hF hB g hgH hg1 hgB).2 P Ph hD hdP hdh hPW d hdc hd1 hdW
  have hPd : P + leWe g * d < ugY S := lt_of_le_of_lt ((add_le_add_iff_left P).2
    (by rw [leWe_succ]; exact mul_le_mul_right hdW.le _)) hPW
  have hr'r : r' < r := hr'g.trans_le (sgLW_le h0)
  have hdr' : Om (1 + 1) ∣ r' := by
    have h := tuDvd_mod (e := r) (f := 1) (g := g) (by rw [leWe_one]; exact hdr) hg1
    rwa [leWe_one] at h
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · rw [hTr, hrdec, hr'0, add_zero, ugTh_zero, add_zero]
    exact Or.inl hD1
  have hs' : sgLW r' < g := tuLogW_lt hr'0 hr'g
  have hs'H : sgLW r' ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hr'H)
  have hdP' : leWe (sgLW r' + 1) ∣ P + leWe g * d := by
    refine dvd_add ((leWe_dvd ((Order.add_one_le_of_lt hs').trans le_self_add)).trans hdP) ?_
    exact (leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_mul_right _ _)
  have hTs : ugTh S l (sgLW r') < ugTh S l g := ugLt hl hX hs'H hgH (hgr.trans_lt hrY) hs'
  have hdh' : leOe (ugTh S l (sgLW r') + 1) ∣ Ph + leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) d := by
    refine dvd_add ((tuOe_dvd ((Order.add_one_le_of_lt hTs).trans le_self_add)).trans hdh) ?_
    exact (tuOe_dvd (Order.add_one_le_of_lt hTs)).trans (dvd_mul_right _ _)
  have h := IH r' hr'r hr'H hdr' (hr'r.trans hrB) _ _ (Or.inl hD1) hPd hdP' hdh'
  rw [hTr, hrdec, ← add_assoc, ← add_assoc]
  exact h

/-- **THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < B` OF `H_λ`** (image `T E`, own predicate `CL₃ E`),
given the member systems at the `W`-fixed limits in `[Γ₂, B)`. -/
theorem uqLevB {B : Ordinal.{0}} (hF : UqFixMS S l B) (hB : B ≤ ugY S) (hBl : IsSuccLimit B)
    {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E) (hEB : E < B) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) := by
  have hEY : E < ugY S := hEB.trans_le hB
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
  have hDP := uqPfx hl hX hF hB hBl P hPH hPd (hPE.trans_lt hEB) 0 0 (Or.inr ⟨rfl, rfl⟩) uqY_SC.1
    (dvd_zero _) (dvd_zero _)
  rw [zero_add, zero_add] at hDP
  have hD : UqPD S l P (ugTh S l P) := by
    rcases hDP with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 hP0
  have hTE : ugTh S l E = ugTh S l P + gxTh (upsilon l) (ldAtR S l) c := by
    have hsc : sgLW c = 0 := by
      unfold sgLW
      exact Ordinal.div_eq_zero_of_lt ((log_le_self ω c).trans_lt hcW)
    have hcG : c < uaGam := hcW.trans uaGam_spec.2
    rw [hdec, ugAdd hl hX P hPH c hcH (hdec ▸ hEY) (by rw [hsc, zero_add, hW1]; exact hPd), ugTh_lt hcG,
      uaThCode hl hX hcW]
  rw [hTE, hdec]
  exact ⟨uqPreOwP hl hX hD hcc hcW, uqPreLev hl hX hD c hcc hcW⟩

/-- **The members `X_k` of `Γ₂`** (image `G₁ = ψ_{Ω₂}(0)`). -/
theorem uqMA_gam : UqMA S l uaGam := by
  refine ⟨fun m => ∃ k, m = udX k, ?_, ⟨_, 0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨k, rfl⟩
    exact ⟨ugX_mem _ _ k, (gg_one_lt_of_SC ldOm2_SC).le.trans (udX_gt k).le, udX_lt k⟩
  · intro y _ hy
    obtain ⟨k, hk⟩ := udX_cof hy
    exact ⟨_, ⟨k, rfl⟩, hk⟩
  · intro z hz
    rw [ugGam] at hz
    obtain ⟨k, hk⟩ := ugThX_cof hl hX hz
    exact ⟨_, ⟨k, rfl⟩, by rw [ugTh_lt (udX_lt k)]; exact hk⟩
  · rintro Q hQ m h ⟨k, rfl⟩ _ _ _
    exact UgC.of_le (ugX_cl hQ k)

/-- **`UqFixMS` below `ε' = φ(1, Γ₂ + 1)`**: the only `W`-fixed limit in `[Γ₂, ε')` is `Γ₂`, with the members `X_k`. -/
theorem uqFixEps : UqFixMS S l (veblen 1 (uaGam + 1)) := by
  intro r _ hGr hrB hrs _
  have hr : r = uaGam := by
    rcases hGr.lt_or_eq with hlt | heq
    · exact absurd (uqEps_next (uqW_eps (ugGam_pos.trans hlt) hrs) hlt) (not_le.2 hrB)
    · exact heq.symm
  subst hr
  exact Or.inl (uqMA_gam hl hX)

/-- **UNCONDITIONAL: THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < φ(1, Γ₂ + 1)` OF `H_λ`.** -/
theorem uqLevEps {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < veblen 1 (uaGam + 1)) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevB hl hX (uqFixEps hl hX) uqEps_lt_Y.le uqEps_lim hEH hWE hE

/-- **THE LEVEL STATEMENT PAST `Γ₂` AT EVERY LEVEL `Ω₂ ≤ E < Y₃` OF `H_λ`**, given the member systems at the
`W`-fixed limits in `[Γ₂, Y₃)`. -/
theorem uqLevAll (hF : UqFixMS S l (ugY S)) {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hWE : Om (1 + 1) ≤ E)
    (hE : E < ugY S) :
    UjOwP S l (UgCL S E) E (ugTh S l E) ∧ UjLev S l (UgCL S E) E (ugTh S l E) :=
  uqLevB hl hX hF le_rfl uqY_SC.isSuccLimit hEH hWE hE

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
