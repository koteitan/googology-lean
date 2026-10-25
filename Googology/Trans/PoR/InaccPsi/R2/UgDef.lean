import Googology.Trans.PoR.InaccPsi.R2.UdRoad

/-!
# The image of the exponents past `Γ₂`: `ψ_{Ω₃}`-atoms read one `Ω` down

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`, `Γ₂ = Ua.uaGam`
(`= ψ_{Ω₃}(0)`, `Ud.udGam_eq`), `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`, `Y₃ = ψ₃(Ω₃)` (`ugY`).

**The image** `ugTh S λ E` (`T E`): `Ua.uaTh` below `Γ₂`; above `Γ₂` the base-`Ω₂` normal form
`T(W^g·d + r) = Ω^{T g}·Θ d + T r` off the `W`-fixed points, **`T(ψ₃(d)) = ψ₂(T d)` at a `ψ₃`-atom with its
normal argument `d < ψ₃(d)`** (`ugD`), and `T(φ(a, b)) = φ(T a, T b)` at the other `W`-fixed points.  Below `Y₃`
every `ψ₃`-atom of `H_λ` has its normal argument below itself, so the clauses cover `H_λ ∩ Y₃`.

* `ugD`, `ugD_eq` (**the normal argument is unique**), `ugY`, `ugGam_pos`, `ugGam_le_psi3`, `ugY_lt_Om3`;
* `ugTh_lt`, `ugTh_cnf`, `ugTh_atom`, `ugTh_node` (the clauses), `ugTh_zero`;
* `ugNode` (**the node data above `Γ₂`**: a `W`-fixed point `E ≥ Γ₂` that is not strongly critical is `φ(a, b)`,
  `0 < a < E`, `b < E`);
* `ugAtomH` (**THE `ψ₃`-ATOMS OF THE HULL**: a strongly critical `E ∈ H_λ` with `Ω₂ < E < Y₃` is `ψ₃(d)` with
  `d ∈ H_λ`, `d < ψ₃(d)`, `d ∈ Cl(d, ψ₃(d))`).

No new axiom.  New definitions: `ugY`, `ugD`, `ugTh`.
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
  Googology.Trans.PoR.InaccPsi.R2.Ry

variable {S : InaccSeq.{0}}

/-- The bound `Y₃ = ψ_{Ω₃}(Ω₃)`. -/
noncomputable def ugY (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1))

/-- **The normal argument at the level `Ω₃`**: the least `d < E` with `ψ_{Ω₃}(d) = E`. -/
noncomputable def ugD (S : InaccSeq.{0}) (E : Ordinal.{0}) : Ordinal.{0} :=
  sInf {d | d < E ∧ S.psi d (Om (1 + 1 + 1)) = E}

theorem ugInR3 : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)

/-- **The normal argument is unique**: `d < ψ₃(d)` gives `ugD (ψ₃ d) = d`. -/
theorem ugD_eq {d : Ordinal.{0}} (hd : d < S.psi d (Om (1 + 1 + 1))) :
    ugD S (S.psi d (Om (1 + 1 + 1))) = d := by
  refine le_antisymm (csInf_le' ⟨hd, rfl⟩) (le_csInf ⟨d, hd, rfl⟩ fun d' hd' => ?_)
  obtain ⟨h1, h2⟩ := hd'
  by_contra hlt
  have hlt' : d' < d := not_le.1 hlt
  have := psi_lt_psi_of_mem (S := S) ugInR3 hlt' (CSet.of_lt h1)
  rw [h2] at this
  exact lt_irrefl _ this

theorem ugGam_pos : (0 : Ordinal.{0}) < uaGam :=
  (Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)).trans uaGam_spec.2

theorem ugGam_le_psi3 (d : Ordinal.{0}) : uaGam ≤ S.psi d (Om (1 + 1 + 1)) := by
  rw [udGam_eq (S := S)]; exact (psi_mono ugInR3 zero_le).1

theorem ugY_lt_Om3 : ugY S < Om (1 + 1 + 1) := psi_lt ugInR3 _

theorem ugOm2_lt_psi3 (d : Ordinal.{0}) : Om (1 + 1 : Ordinal.{0}) < S.psi d (Om (1 + 1 + 1)) :=
  (psiS_bounds (S := S) d (1 + 1)).1

open Classical in
/-- **The image past `Γ₂`**: `Ua.uaTh` below `Γ₂`, the base-`Ω₂` normal form off the `W`-fixed points,
`ψ₃(d) ↦ ψ₂(T d)` at the `ψ₃`-atoms with `d < ψ₃(d)`, the Veblen normal form at the other `W`-fixed points. -/
noncomputable def ugTh (S : InaccSeq.{0}) (l E : Ordinal.{0}) : Ordinal.{0} :=
  if hE : E < uaGam then uaTh S l E
  else if h1 : sgLW E < E then
    leOe (ugTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      ugTh S l (E % leWe (sgLW E))
  else if h3 : ugD S E < E ∧ S.psi (ugD S E) (Om (1 + 1 + 1)) = E then
    S.psi (ugTh S l (ugD S E)) (Om (1 + 1))
  else if h2 : invVeblen₁ E < E ∧ invVeblen₂ E < E then
    veblen (ugTh S l (invVeblen₁ E)) (ugTh S l (invVeblen₂ E))
  else 0
termination_by E
decreasing_by
  · exact h1
  · exact (Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le (ugGam_pos.trans_le (not_lt.1 hE)))
  · exact h3.1
  · exact h2.1
  · exact h2.2

theorem ugTh_lt {l E : Ordinal.{0}} (hE : E < uaGam) : ugTh S l E = uaTh S l E := by
  rw [ugTh, dif_pos hE]

theorem ugTh_zero (l : Ordinal.{0}) : ugTh S l 0 = 0 := by
  rw [ugTh_lt ugGam_pos, uaTh_zero]

theorem ugTh_cnf {l E : Ordinal.{0}} (hG : uaGam ≤ E) (h : sgLW E < E) :
    ugTh S l E = leOe (ugTh S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      ugTh S l (E % leWe (sgLW E)) := by
  rw [ugTh, dif_neg (not_lt.2 hG), dif_pos h]

/-- A strongly critical `E > Ω₂` is `W`-fixed. -/
theorem ugSC_W {E : Ordinal.{0}} (hS : SC E) (h2 : Om (1 + 1) < E) : sgLW E = E ∧ leWe E = E :=
  uaWfix (gg_SC_eps hS) h2

/-- **`T(ψ₃(d)) = ψ₂(T d)`** at a normal argument `d < ψ₃(d)`. -/
theorem ugTh_atom {l d : Ordinal.{0}} (hd : d < S.psi d (Om (1 + 1 + 1))) :
    ugTh S l (S.psi d (Om (1 + 1 + 1))) = S.psi (ugTh S l d) (Om (1 + 1)) := by
  set E := S.psi d (Om (1 + 1 + 1)) with hE
  have hG : uaGam ≤ E := ugGam_le_psi3 d
  have hW := ugSC_W (SC_psi (S := S) ugInR3 d) (ugOm2_lt_psi3 (S := S) d)
  have hs : ¬ sgLW E < E := by rw [hW.1]; exact lt_irrefl _
  have hD : ugD S E = d := ugD_eq hd
  have h3 : ugD S E < E ∧ S.psi (ugD S E) (Om (1 + 1 + 1)) = E := by rw [hD]; exact ⟨hd, rfl⟩
  rw [ugTh, dif_neg (not_lt.2 hG), dif_neg hs, dif_pos h3, hD]

theorem ugTh_node {l E : Ordinal.{0}} (hG : uaGam ≤ E) (h : ¬ sgLW E < E) (hS : ¬ SC E)
    (h2 : invVeblen₁ E < E ∧ invVeblen₂ E < E) :
    ugTh S l E = veblen (ugTh S l (invVeblen₁ E)) (ugTh S l (invVeblen₂ E)) := by
  have h3 : ¬ (ugD S E < E ∧ S.psi (ugD S E) (Om (1 + 1 + 1)) = E) := fun h3 => by
    rw [← h3.2] at hS; exact hS (SC_psi ugInR3 _)
  rw [ugTh, dif_neg (not_lt.2 hG), dif_neg h, dif_neg h3, dif_pos h2]

/-- **The node data above `Γ₂`**: a `W`-fixed point `E ≥ Γ₂` that is not strongly critical is `φ(a, b)` with
`0 < a < E`, `b < E`, `ω^E = E`, `log_W E = E`, `W^E = E`. -/
theorem ugNode {E : Ordinal.{0}} (hG : uaGam ≤ E) (hS : ¬ SC E) (hs : ¬ sgLW E < E) :
    ω ^ E = E ∧ veblen (invVeblen₁ E) (invVeblen₂ E) = E ∧ 0 < invVeblen₁ E ∧ invVeblen₁ E < E ∧
      invVeblen₂ E < E ∧ sgLW E = E ∧ leWe E = E := by
  have hsE : sgLW E = E := le_antisymm (txSg_le E) (not_lt.1 hs)
  have h2 : Om (1 + 1) < E := uaGam_spec.2.trans_le hG
  have hpos : 0 < E := ugGam_pos.trans_le hG
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
    exact hS (ruSC_of_veblen hpos (le_antisymm hle (left_le_veblen E 0)))

section Hull

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE `ψ₃`-ATOMS OF THE HULL**: a strongly critical `E ∈ H_λ` with `Ω₂ < E < Y₃` is `ψ₃(d)` with `d ∈ H_λ`,
`d < ψ₃(d)` and `d ∈ Cl(d, ψ₃(d))`. -/
theorem ugAtomH {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hSC : SC E) (h2 : Om (1 + 1) < E) (hY : E < ugY S) :
    ∃ d, d ∈ cdHull S l ∧ d < S.psi d (Om (1 + 1 + 1)) ∧
      d ∈ S.CSet d (S.psi d (Om (1 + 1 + 1))) ∧ S.psi d (Om (1 + 1 + 1)) = E := by
  have hρ := leRho hl hX
  have hρE : upsilon l ≤ E := (hρ.2.trans ((Om_lt_Om.2 (lt_add_one 1)).trans h2)).le
  have hE3 : E < Om (1 + 1 + 1) := hY.trans ugY_lt_Om3
  have hO3L : Om (1 + 1 + 1 : Ordinal.{0}) ≤ S.Lam := (lt_Lam_of_mem zero_le (ryOm3_mem (S := S) 0 0)).le
  rcases prin_mem_cases hEH hρE hSC.isPrincipal hSC.1.ne' with
    ⟨n, hn⟩ | hw | ⟨p, q, _, _, hp, hq, hpq⟩ | ⟨p, _, hp, hpz⟩ | ⟨π, e, hπ, _, heC, heα, hz⟩
  · exact absurd (hE3.trans (leOm3_lt_I (S := S) n)) (by rw [hn]; exact lt_irrefl _)
  · exact absurd (hE3.trans ((leOm3_lt_I (S := S) 0).trans (S.I_lt_Iw 0))) (by rw [hw]; exact lt_irrefl _)
  · exact absurd hpq.symm (hSC.not_veblen_lt hp hq)
  · exact absurd hpz (not_Om_of_between h2 hE3 p)
  -- `E = ψ_π(e)`: the subscript is `Ω₃`
  have hπ3 : π = Om (1 + 1 + 1) := by
    rcases hπ with ⟨m, rfl⟩ | ⟨s, rfl⟩
    · exfalso
      have hf := Om_psiI (S := S) e m
      rw [← hz] at hf
      exact not_Om_of_between h2 hE3 E hf.symm
    · have hb := psiS_bounds (S := S) e s
      rw [← hz] at hb
      rw [between_unique hb.1 hb.2 h2 hE3]
  subst hπ3
  have hbY : S.psi e (Om (1 + 1 + 1)) < S.psi (Om (1 + 1 + 1)) (Om (1 + 1 + 1)) := by rw [← hz]; exact hY
  obtain ⟨hdX, heq, hself, -⟩ := ryNf_spec ugInR3 (ryOm3_mem (S := S)) hbY
  obtain ⟨hdH, -⟩ := ryNf_mem (a := ConjT.Aη S (cdEta S l)) ugInR3 hO3L (ryOm3_mem (S := S)) hbY
    (by rw [← hz]; exact hEH) (by rw [← hz]; exact hρE)
  refine ⟨ryNf S (Om (1 + 1 + 1)) e, hdH, ?_, hself, heq.trans hz.symm⟩
  exact lt_psi_of_mem ugInR3 hself hdX

end Hull

end Googology.Trans.PoR.InaccPsi.R2.Ug
