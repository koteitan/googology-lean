import Googology.Trans.PoR.InaccPsi.R2.UgDef

/-!
# The parts of the image past `Γ₂`: lower and upper bounds, the normal form at every point of `H_λ ∩ Y₃`

`T = Ug.ugTh S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`Γ₂ = Ua.uaGam = ψ₃(0)`, `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`, `Y₃ = ψ₃(Ω₃)`.

* `ugLeOe` (`x ≤ Ω^x`), `ugGe2` (**`Γ₂ ≤ x` gives `ψ₂(0) ≤ T x`**: the image jumps over every image below `Γ₂`,
  `Ua.uaLtG1`), `ugPos`, `ugGtOm1`, `ugLtOm2` (**`T x < Ω₂`** on `H_λ ∩ Y₃`);
* `ugWfixTh` (**at a `W`-fixed point `x ≥ Γ₂` the image is `Ω`-fixed**: `Ω^{T x} = T x`; at an atom `T x` is
  strongly critical), `ugNodeTh` (the node clause with `Ω^{T x} = T x`);
* `ugParts` (**the parts of `x ∈ H_λ`, `0 < x < Y₃`, and the normal form `T x = Ω^{T g}·Θ d + T r`**, nodes and
  `ψ₃`-atoms included; `Ua.uaParts` for `T`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ug

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Ru

variable {S : InaccSeq.{0}}

/-- `x ≤ Ω^x`. -/
theorem ugLeOe (x : Ordinal.{0}) : x ≤ leOe x :=
  (Ordinal.le_mul_right x (Om_pos one_ne_zero)).trans (right_le_opow _ one_lt_omega0)

/-- `Γ₂ ≤ x < W^{g+1}` gives `Γ₂ ≤ g`. -/
theorem ugGam_le_log {x : Ordinal.{0}} (hG : uaGam ≤ x) : uaGam ≤ sgLW x := by
  by_contra hc
  push Not at hc
  have hW := (ugSC_W uaGam_spec.1 uaGam_spec.2).2
  have h1 : leWe (sgLW x + 1) ≤ leWe uaGam := leWe_mono (Order.add_one_le_of_lt hc)
  rw [hW] at h1
  exact absurd ((sgLW_lt x).trans_le h1) (not_lt.2 hG)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`Γ₂ ≤ x` gives `ψ₂(0) ≤ T x`** (`x ∈ H_λ`, `x < Y₃`). -/
theorem ugGe2 : ∀ x, x ∈ cdHull S l → uaGam ≤ x → x < ugY S → S.psi 0 (Om (1 + 1)) ≤ ugTh S l x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hGx hxY
  have h0 : 0 < x := ugGam_pos.trans_le hGx
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, hd1, -, -, -, -⟩ := uaBase hl hX hxH h0
    have hGg := ugGam_le_log hGx
    have hTg := IH _ hs hgH hGg (hs.trans hxY)
    have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
      rwa [sqTh_one hl hX] at h
    rw [ugTh_cnf hGx hs]
    calc S.psi 0 (Om (1 + 1)) ≤ ugTh S l (sgLW x) := hTg
      _ ≤ leOe (ugTh S l (sgLW x)) := ugLeOe _
      _ ≤ leOe (ugTh S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) :=
          (mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)
      _ ≤ _ := le_self_add
  by_cases hS : SC x
  · obtain ⟨d, -, hd, -, rfl⟩ := ugAtomH hl hX hxH hS (uaGam_spec.2.trans_le hGx) hxY
    rw [ugTh_atom hd]
    exact (psi_mono (InR_Om_succ 1) zero_le).1
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := ugNode hGx hS hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    rw [ugTh_node hGx hs hS ⟨haE, hbE⟩]
    by_cases ha : uaGam ≤ invVeblen₁ x
    · exact (IH _ haE hmem.1 ha (haE.trans hxY)).trans (left_le_veblen _ _)
    by_cases hb : uaGam ≤ invVeblen₂ x
    · exact (IH _ hbE hmem.2 hb (hbE.trans hxY)).trans (right_le_veblen _ _)
    exfalso
    have := uaGam_spec.1.2 _ (not_le.1 ha) _ (not_le.1 hb)
    rw [hv] at this
    exact absurd hGx (not_le.2 this)

/-- **`T x > 0` for `0 < x < Y₃`.** -/
theorem ugPos {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hxY : x < ugY S) : 0 < ugTh S l x := by
  rcases lt_or_ge x uaGam with hxE | hxE
  · rw [ugTh_lt hxE]; exact uaPos hl hX hxH h0 hxE
  · exact rwG_SC.1.trans_le (ugGe2 hl hX x hxH hxE hxY)

/-- **`Γ₂ ≤ x` gives `Ω₁ < T x`.** -/
theorem ugGtOm1 {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hGx : uaGam ≤ x) (hxY : x < ugY S) :
    Om 1 < ugTh S l x :=
  rwO_lt_G.trans_le (ugGe2 hl hX x hxH hGx hxY)

/-- **The image at a `W`-fixed point `x ≥ Γ₂`**: `log_W x = x`, `W^x = x`, `Ω^{T x} = T x`; the node clause or the
atom clause applies. -/
theorem ugWfixTh {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hGx : uaGam ≤ x) (hxY : x < ugY S)
    (hs : ¬ sgLW x < x) :
    sgLW x = x ∧ leWe x = x ∧ ω ^ ugTh S l x = ugTh S l x ∧ leOe (ugTh S l x) = ugTh S l x := by
  have hΩ := ugGtOm1 hl hX hxH hGx hxY
  by_cases hS : SC x
  · obtain ⟨d, -, hd, -, rfl⟩ := ugAtomH hl hX hxH hS (uaGam_spec.2.trans_le hGx) hxY
    have hW := ugSC_W hS (ugOm2_lt_psi3 d)
    have hε : ω ^ ugTh S l (S.psi d (Om (1 + 1 + 1))) = ugTh S l (S.psi d (Om (1 + 1 + 1))) := by
      rw [ugTh_atom hd]; exact gg_SC_eps (SC_psi (InR_Om_succ 1) _)
    exact ⟨hW.1, hW.2, hε, uaOe_fix hε hΩ⟩
  · obtain ⟨-, hv, ha0, haE, hbE, hsx, hWx⟩ := ugNode hGx hS hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    have hTa : ugTh S l (invVeblen₁ x) ≠ 0 := (ugPos hl hX hmem.1 ha0 (haE.trans hxY)).ne'
    have hε : ω ^ ugTh S l x = ugTh S l x := by
      rw [ugTh_node hGx hs hS ⟨haE, hbE⟩]; exact gg_veblen_eps hTa
    exact ⟨hsx, hWx, hε, uaOe_fix hε hΩ⟩

/-- **The image of a node `x ≥ Γ₂`** (not strongly critical): `T x = φ(T a, T b)`, an `ε`-number `> Ω₁`. -/
theorem ugNodeTh {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hGx : uaGam ≤ x) (hxY : x < ugY S) (hS : ¬ SC x)
    (hs : ¬ sgLW x < x) :
    ugTh S l x = veblen (ugTh S l (invVeblen₁ x)) (ugTh S l (invVeblen₂ x)) ∧
      leOe (ugTh S l x) = ugTh S l x := by
  obtain ⟨-, -, -, haE, hbE, -, -⟩ := ugNode hGx hS hs
  exact ⟨ugTh_node hGx hs hS ⟨haE, hbE⟩, (ugWfixTh hl hX hxH hGx hxY hs).2.2.2⟩

/-- **`T x < Ω₂`** on `H_λ ∩ Y₃`. -/
theorem ugLtOm2 : ∀ x, x ∈ cdHull S l → x < ugY S → ugTh S l x < Om (1 + 1) := by
  have hW := ldOm2_SC
  have h12 : Om (1 : Ordinal.{0}) < Om (1 + 1) := Om_lt_Om.2 (lt_add_one 1)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxY
  rcases lt_or_ge x uaGam with hxE | hGx
  · rw [ugTh_lt hxE]; exact (uaLtG1 hl hX x hxH hxE).trans (psi_lt (InR_Om_succ 1) 0)
  have h0 : 0 < x := ugGam_pos.trans_le hGx
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -⟩ := uaBase hl hX hxH h0
    have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le h0)
    rw [ugTh_cnf hGx hs]
    exact hW.isPrincipal (ldMul_lt_SC hW (leOe_lt_SC hW h12 (IH _ hs hgH (hs.trans hxY))).1
      ((snTh_lt_Om1 hl hX hdW.le).trans h12)) (IH _ hrx hrH (hrx.trans hxY))
  by_cases hS : SC x
  · obtain ⟨d, -, hd, -, rfl⟩ := ugAtomH hl hX hxH hS (uaGam_spec.2.trans_le hGx) hxY
    rw [ugTh_atom hd]; exact psi_lt (InR_Om_succ 1) _
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := ugNode hGx hS hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    rw [ugTh_node hGx hs hS ⟨haE, hbE⟩]
    exact hW.2 _ (IH _ haE hmem.1 (haE.trans hxY)) _ (IH _ hbE hmem.2 (hbE.trans hxY))

/-- **The parts of `x ∈ H_λ`, `0 < x < Y₃`, and the normal form `T x = Ω^{T g}·Θ d + T r`** (nodes and `ψ₃`-atoms
included). -/
theorem ugParts {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hxY : x < ugY S) :
    sgLW x ∈ cdHull S l ∧ sgLW x ≤ x ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) ∧
      ugTh S l x = leOe (ugTh S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) +
        ugTh S l (x % leWe (sgLW x)) ∧
      (sgLW x < x ∨ (sgLW x = x ∧ x / leWe (sgLW x) = 1 ∧ x % leWe (sgLW x) = 0)) := by
  have base := uaBase hl hX hxH h0
  rcases lt_or_ge x uaGam with hxE | hGx
  · obtain ⟨-, hgx, -, -, -, -, hrg, -, hT, hor⟩ := uaParts hl hX hxH h0 hxE
    have hgG : sgLW x < uaGam := hgx.trans_lt hxE
    have hrG : x % leWe (sgLW x) < uaGam := (hrg.trans_le (sgLW_le h0)).trans hxE
    refine ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, ?_, hor⟩
    rw [ugTh_lt hxE, ugTh_lt hgG, ugTh_lt hrG]; exact hT
  by_cases hs : sgLW x < x
  · exact ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, ugTh_cnf hGx hs, Or.inl hs⟩
  · obtain ⟨hsx, hWx, -, hOx⟩ := ugWfixTh hl hX hxH hGx hxY hs
    have hq : x / leWe (sgLW x) = 1 := by rw [hsx, hWx]; exact Ordinal.div_self h0.ne'
    have hr : x % leWe (sgLW x) = 0 := by rw [hsx, hWx]; exact Ordinal.mod_self x
    refine ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, ?_, Or.inr ⟨hsx, hq, hr⟩⟩
    rw [hq, hr, sqTh_one hl hX, mul_one, ugTh_zero, add_zero, hsx]
    exact hOx.symm

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ug
