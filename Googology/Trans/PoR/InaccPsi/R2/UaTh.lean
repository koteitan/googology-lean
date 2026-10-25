import Googology.Trans.PoR.InaccPsi.R2.TxSys2

/-!
# The image of the exponents `≥ G`: the substitution `Ω₂ ↦ Ω₁`, codes `↦ Θ`, on Veblen normal forms

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`, `Γ₂ = Ua.uaGam` (the least strongly critical ordinal above `Ω₂`, `Γ₂ ≤ ψ_{Ω₃}(0)`).

**The image** `Ua.uaTh S λ E` (`T E`): `Θ̂_L E` below `G`; at `E ≥ G` off the `W`-fixed points the base-`Ω₂`
normal form `T(W^g·d + r) = Ω^{T g}·Θ d + T r` (`g = log_W E`); at a `W`-fixed point `E ≥ G` the Veblen normal
form `T(φ(a, b)) = φ(T a, T b)` (`a = invVeblen₁ E`, `b = invVeblen₂ E`; the level `a` may be `≥ Ω₂`, e.g.
`T G = φ(T Ω₂, T 1) = Ĝ`).

* `uaGam`, `uaGam_spec`, `uaGam_le`, `uaGam_le_G3`, `uaG_lt_Gam`; `uaNode` (**a `W`-fixed point
  `G ≤ E < Γ₂` is `φ(a, b)`, `0 < a < E`, `b < E`, `W^E = E`**), `uaWfix` (an `ε`-number above `Ω₂` is `W`-fixed);
* `uaTh_lt`, `uaTh_cnf`, `uaTh_node` (the three clauses);
* `uaGe` (`G ≤ x ⇒ Ĝ ≤ T x`), `uaPos`, `uaGtOm` (`Ω₂ < x ⇒ Ω₁ < T x`), `uaParts` (**the normal form
  `T x = Ω^{T g}·Θ d + T r` at every `0 < x < Γ₂` of `H_λ`, nodes included**).

No new axiom.  New definitions: `uaGam`, `uaTh`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

/-- **The least strongly critical ordinal above `Ω₂`.** -/
noncomputable def uaGam : Ordinal.{0} := sInf {b | SC b ∧ Om (1 + 1) < b}

theorem uaGam_spec : SC uaGam ∧ Om (1 + 1 : Ordinal.{0}) < uaGam :=
  csInf_mem (s := {b | SC b ∧ Om (1 + 1) < b})
    ⟨Om (1 + 1 + 1), SC_Om (zero_lt_one.trans_le le_add_self).ne', Om_lt_Om.2 (lt_add_one _)⟩

theorem uaGam_le {b : Ordinal.{0}} (hb : SC b) (h : Om (1 + 1) < b) : uaGam ≤ b :=
  csInf_le' (s := {b | SC b ∧ Om (1 + 1) < b}) ⟨hb, h⟩

theorem uaGam_le_G3 : uaGam ≤ S.psi 0 (Om (1 + 1 + 1)) := uaGam_le rwG3_SC rwW_lt_G3

theorem uaG_lt_Gam : veblen (Om (1 + 1 : Ordinal.{0})) 1 < uaGam :=
  uaGam_spec.1.2 _ uaGam_spec.2 _ (gg_one_lt_of_SC uaGam_spec.1)

/-- **An `ε`-number above `Ω₂` is `W`-fixed**: `log_W E = E` and `W^E = E`. -/
theorem uaWfix {E : Ordinal.{0}} (hE : ω ^ E = E) (h2 : Om (1 + 1) < E) : sgLW E = E ∧ leWe E = E := by
  have hab : Om (1 + 1) + E = E := by
    have := Ordinal.add_absorp (a := Om (1 + 1)) (b := E) (c := ω ^ E) (by rw [hE]; exact h2) le_rfl
    rwa [hE] at this
  have hm : Om (1 + 1) * E = E := by
    rw [← gg_SC_eps ldOm2_SC]
    conv_lhs => rw [← hE]
    rw [← opow_add, hab, hE]
  have hlog : log ω E = E := by
    conv_lhs => rw [← hE]
    exact log_opow one_lt_omega0 E
  refine ⟨?_, ?_⟩
  · unfold sgLW; rw [hlog]
    conv_lhs => rw [← hm]
    exact Ordinal.mul_div_cancel _ ldOm2_SC.1.ne'
  · unfold leWe; rw [hm, hE]

/-- **The node data**: a `W`-fixed point `G ≤ E < Γ₂` is an `ε`-number `φ(a, b)` with `0 < a < E`, `b < E`
(`a = invVeblen₁ E`, `b = invVeblen₂ E`), `log_W E = E`, `W^E = E`. -/
theorem uaNode {E : Ordinal.{0}} (hG : veblen (Om (1 + 1)) 1 ≤ E) (hE : E < uaGam) (hs : ¬ sgLW E < E) :
    ω ^ E = E ∧ veblen (invVeblen₁ E) (invVeblen₂ E) = E ∧ 0 < invVeblen₁ E ∧ invVeblen₁ E < E ∧
      invVeblen₂ E < E ∧ sgLW E = E ∧ leWe E = E := by
  have hsE : sgLW E = E := le_antisymm (txSg_le E) (not_lt.1 hs)
  have h2 : Om (1 + 1) < E := tgOm_lt_G.trans_le hG
  have hpos : 0 < E := (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans h2
  have hlogE : log ω E = E := by
    refine le_antisymm (log_le_self ω E) ?_
    calc E = sgLW E := hsE.symm
      _ ≤ log ω E := Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)
  have hε : ω ^ E = E := by
    refine le_antisymm ?_ (right_le_opow E one_lt_omega0)
    calc ω ^ E = ω ^ log ω E := by rw [hlogE]
      _ ≤ E := opow_log_le_self ω hpos.ne'
  have hv : veblen (invVeblen₁ E) (invVeblen₂ E) = E := by rw [veblen_invVeblen₁_invVeblen₂, hε]
  have hb : invVeblen₂ E < E := by have := invVeblen₂_lt E; rwa [hε] at this
  refine ⟨hε, hv, ?_, ?_, hb, hsE, (uaWfix hε h2).2⟩
  · refine pos_iff_ne_zero.2 fun h0 => ?_
    rw [h0, veblen_zero_apply] at hv
    have : invVeblen₂ E = E := (opow_right_inj one_lt_omega0).1 (hv.trans hε.symm)
    exact absurd this hb.ne
  · refine lt_of_le_of_ne (invVeblen₁_le E) fun e => ?_
    rw [e] at hv
    have hle : veblen E 0 ≤ E := (veblen_le_veblen_iff_right.2 zero_le).trans hv.le
    have hSC := Ru.ruSC_of_veblen hpos (le_antisymm hle (left_le_veblen E 0))
    exact absurd (uaGam_le hSC h2) (not_le.2 hE)

open Classical in
/-- **The image of the exponents**: `Θ̂_L` below `G`, the base-`Ω₂` normal form off the `W`-fixed points, the Veblen
normal form at the `W`-fixed points `≥ G` (levels read by the image itself). -/
noncomputable def uaTh (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if hG : E < veblen (Om (1 + 1)) 1 then tdThL S l E
  else if h1 : sgLW E < E then
    leOe (uaTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      uaTh S l (E % leWe (sgLW E))
  else if h2 : invVeblen₁ E < E ∧ invVeblen₂ E < E then
    veblen (uaTh S l (invVeblen₁ E)) (uaTh S l (invVeblen₂ E))
  else 0
termination_by E
decreasing_by
  · exact h1
  · exact (Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le (veblen_pos.trans_le (not_lt.1 hG)))
  · exact h2.1
  · exact h2.2

theorem uaTh_lt {l E : Ordinal.{0}} (hE : E < veblen (Om (1 + 1)) 1) : uaTh S l E = tdThL S l E := by
  rw [uaTh, dif_pos hE]

theorem uaTh_cnf {l E : Ordinal.{0}} (hG : veblen (Om (1 + 1)) 1 ≤ E) (h : sgLW E < E) :
    uaTh S l E = leOe (uaTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      uaTh S l (E % leWe (sgLW E)) := by
  rw [uaTh, dif_neg (not_lt.2 hG), dif_pos h]

theorem uaTh_node {l E : Ordinal.{0}} (hG : veblen (Om (1 + 1)) 1 ≤ E) (h : ¬ sgLW E < E)
    (h2 : invVeblen₁ E < E ∧ invVeblen₂ E < E) :
    uaTh S l E = veblen (uaTh S l (invVeblen₁ E)) (uaTh S l (invVeblen₂ E)) := by
  rw [uaTh, dif_neg (not_lt.2 hG), dif_neg h, dif_pos h2]

theorem uaTh_zero (l : Ordinal.{0}) : uaTh S l 0 = 0 := by
  rw [uaTh_lt veblen_pos, tjThL_zero]

/-- `Ω^X = X` for an `ε`-number `X > Ω₁`. -/
theorem uaOe_fix {X : Ordinal.{0}} (hX : ω ^ X = X) (h1 : Om 1 < X) : leOe X = X := by
  have hab : Om 1 + X = X := by
    have := Ordinal.add_absorp (a := Om 1) (b := X) (c := ω ^ X) (by rw [hX]; exact h1) le_rfl
    rwa [hX] at this
  have hm : Om 1 * X = X := by
    rw [← gg_SC_eps Ph.ph_SC_Om1]
    conv_lhs => rw [← hX]
    rw [← opow_add, hab, hX]
  unfold leOe; rw [hm, hX]

/-- The base-`Ω₂` parts of `x > 0` (no bound). -/
theorem uaBase {l ηx x : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hxH : x ∈ cdHull S l)
    (h0 : 0 < x) :
    sgLW x ∈ cdHull S l ∧ sgLW x ≤ x ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) := by
  set g := sgLW x with hg
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have hWe : leWe g ≤ x := sgLW_le h0
  have hE2 : x < leWe g * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
  have hqW : x / leWe g < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : x / leWe g ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * g) (dvd_mul_right _ _) hxH ?_
    have : leWe (g + 1) = ω ^ (Om (1 + 1) * g + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt x
  exact ⟨ldDivK_mem ldOm2_SC (leLog_mem hxH), txSg_le x, (ldHull_iff hl hX hqW).1 hqH,
    Order.one_le_iff_pos.2 ((Ordinal.div_pos hW0).2 hWe), hqW, leModP_mem (Om (1 + 1) * g) hxH,
    Ordinal.mod_lt _ hW0, (Ordinal.div_add_mod x (leWe g)).symm⟩

/-- `G ≤ x` gives `G ≤ log_W x`. -/
theorem uaG_le_log {x : Ordinal.{0}} (hG : veblen (Om (1 + 1)) 1 ≤ x) : veblen (Om (1 + 1)) 1 ≤ sgLW x := by
  have h : leWe (veblen (Om (1 + 1)) 1) < leWe (sgLW x + 1) := by rw [tgWe_G]; exact hG.trans_lt (sgLW_lt x)
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.2 (leWe_mono (Order.add_one_le_of_lt hc)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`G ≤ x` gives `Ĝ ≤ T x`** (`x ∈ H_λ`, `x < Γ₂`). -/
theorem uaGe : ∀ x, x ∈ cdHull S l → veblen (Om (1 + 1)) 1 ≤ x → x < uaGam →
    veblen (Om 1) 1 ≤ uaTh S l x := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  have hΩGh : Om (1 : Ordinal.{0}) < veblen (Om 1) 1 := (lt_add_one _).trans tnOm1_lt_Gh
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hGx hxE
  have h0 : 0 < x := veblen_pos.trans_le hGx
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, hd1, -, -, -, -⟩ := uaBase hl hX hxH h0
    have hGg := uaG_le_log hGx
    have hTg := IH _ hs hgH hGg (hs.trans hxE)
    have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
      rwa [sqTh_one hl hX] at h
    rw [uaTh_cnf hGx hs]
    calc veblen (Om 1) 1 = leOe (veblen (Om 1) 1) := txOe_Gh.symm
      _ ≤ leOe (uaTh S l (sgLW x)) := leOe_mono hTg
      _ ≤ leOe (uaTh S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) :=
          (mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)
      _ ≤ _ := le_self_add
  · obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := uaNode hGx hxE hs
    set a := invVeblen₁ x with ha_def
    set b := invVeblen₂ x with hb_def
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    rw [uaTh_node hGx hs ⟨haE, hbE⟩, ← ha_def, ← hb_def]
    rcases lt_trichotomy a (Om (1 + 1)) with haW | haW | haW
    · -- a code level: the argument is above `G`
      have hGb : veblen (Om (1 + 1)) 1 ≤ b := by
        by_contra hc
        push Not at hc
        have h1 : veblen a b < veblen a (veblen (Om (1 + 1)) 1) := veblen_lt_veblen_iff_right.2 hc
        rw [veblen_veblen_of_lt haW, hv] at h1
        exact absurd hGx (not_le.2 h1)
      exact (IH b hbE hmem.2 hGb (hbE.trans hxE)).trans (right_le_veblen _ _)
    · -- the level `Ω₂`: the argument is `≥ 1`
      rw [haW] at hv ⊢
      have hb0 : b ≠ 0 := by
        rintro h0
        rw [h0, ldOm2_SC.veblen_zero] at hv
        rw [← hv] at hGx
        exact absurd hGx (not_le.2 tgOm_lt_G)
      have hTa : uaTh S l (Om (1 + 1)) = Om 1 := by rw [uaTh_lt tgOm_lt_G]; exact txOm2 hl hX
      have hTb : 1 ≤ uaTh S l b := by
        rcases lt_or_ge b (veblen (Om (1 + 1)) 1) with hbG | hbG
        · rw [uaTh_lt hbG]; exact Order.one_le_iff_pos.2 (txPos hl hX hmem.2 (pos_iff_ne_zero.2 hb0) hbG)
        · exact (Order.one_le_iff_pos.2 veblen_pos).trans (IH b hbE hmem.2 hbG (hbE.trans hxE))
      rw [hTa]; exact veblen_le_veblen_iff_right.2 hTb
    · -- a level above `Ω₂`
      have hTa : Om 1 < uaTh S l a := by
        rcases lt_or_ge a (veblen (Om (1 + 1)) 1) with haG | haG
        · rw [uaTh_lt haG, ← txOm2 hl hX]
          exact txLt hl hX (mxOm2_mem _ _) hmem.1 haG haW
        · exact hΩGh.trans_le (IH a haE hmem.1 haG (haE.trans hxE))
      refine (veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hTa, ?_⟩))).le.trans (veblen_le_veblen_iff_right.2 zero_le)
      exact (gg_one_lt_of_SC Ph.ph_SC_Om1).trans (hTa.trans_le (left_le_veblen _ _))

/-- **`T x > 0` for `0 < x < Γ₂`.** -/
theorem uaPos {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hxE : x < uaGam) : 0 < uaTh S l x := by
  rcases lt_or_ge x (veblen (Om (1 + 1)) 1) with hxG | hxG
  · rw [uaTh_lt hxG]; exact txPos hl hX hxH h0 hxG
  · exact veblen_pos.trans_le (uaGe hl hX x hxH hxG hxE)

/-- **`Ω₂ < x` gives `Ω₁ < T x`.** -/
theorem uaGtOm {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h2 : Om (1 + 1) < x) (hxE : x < uaGam) :
    Om 1 < uaTh S l x := by
  rcases lt_or_ge x (veblen (Om (1 + 1)) 1) with hxG | hxG
  · rw [uaTh_lt hxG, ← txOm2 hl hX]; exact txLt hl hX (mxOm2_mem _ _) hxH hxG h2
  · exact ((lt_add_one _).trans tnOm1_lt_Gh).trans_le (uaGe hl hX x hxH hxG hxE)

/-- **The image of a node `≥ G`** is an `ε`-number `> Ω₁` with `Ω^{T x} = T x`. -/
theorem uaNodeTh {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hGx : veblen (Om (1 + 1)) 1 ≤ x) (hxE : x < uaGam)
    (hs : ¬ sgLW x < x) :
    uaTh S l x = veblen (uaTh S l (invVeblen₁ x)) (uaTh S l (invVeblen₂ x)) ∧ ω ^ uaTh S l x = uaTh S l x ∧
      leOe (uaTh S l x) = uaTh S l x := by
  obtain ⟨-, hv, ha0, haE, hbE, -, -⟩ := uaNode hGx hxE hs
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
  have hT := uaTh_node (S := S) (l := l) hGx hs ⟨haE, hbE⟩
  have hTa : uaTh S l (invVeblen₁ x) ≠ 0 := (uaPos hl hX hmem.1 ha0 (haE.trans hxE)).ne'
  have hε : ω ^ uaTh S l x = uaTh S l x := by rw [hT]; exact gg_veblen_eps hTa
  have hΩ : Om 1 < uaTh S l x := ((lt_add_one _).trans tnOm1_lt_Gh).trans_le (uaGe hl hX x hxH hGx hxE)
  exact ⟨hT, hε, uaOe_fix hε hΩ⟩

/-- **The parts of `x ∈ H_λ`, `0 < x < Γ₂`, and the normal form `T x = Ω^{T g}·Θ d + T r`** (nodes included). -/
theorem uaParts {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hxE : x < uaGam) :
    sgLW x ∈ cdHull S l ∧ sgLW x ≤ x ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) ∧
      uaTh S l x = leOe (uaTh S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) +
        uaTh S l (x % leWe (sgLW x)) ∧
      (sgLW x < x ∨ (sgLW x = x ∧ x / leWe (sgLW x) = 1 ∧ x % leWe (sgLW x) = 0)) := by
  have base := uaBase hl hX hxH h0
  rcases lt_or_ge x (veblen (Om (1 + 1)) 1) with hxG | hxG
  · obtain ⟨-, hgx, -, -, -, -, hrg, -, hT, hor⟩ := txParts hl hX hxH h0 hxG
    have hgG : sgLW x < veblen (Om (1 + 1)) 1 := hgx.trans_lt hxG
    have hrG : x % leWe (sgLW x) < veblen (Om (1 + 1)) 1 := (hrg.trans_le (sgLW_le h0)).trans hxG
    refine ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, ?_, hor⟩
    rw [uaTh_lt hxG, uaTh_lt hgG, uaTh_lt hrG]; exact hT
  by_cases hs : sgLW x < x
  · exact ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, uaTh_cnf hxG hs, Or.inl hs⟩
  · obtain ⟨-, -, -, -, -, hsx, hWx⟩ := uaNode hxG hxE hs
    have hq : x / leWe (sgLW x) = 1 := by rw [hsx, hWx]; exact Ordinal.div_self h0.ne'
    have hr : x % leWe (sgLW x) = 0 := by rw [hsx, hWx]; exact Ordinal.mod_self x
    refine ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, ?_, Or.inr ⟨hsx, hq, hr⟩⟩
    rw [hq, hr, sqTh_one hl hX, mul_one, uaTh_zero, add_zero, hsx]
    exact (uaNodeTh hl hX hxH hxG hxE hs).2.2.symm

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ua
