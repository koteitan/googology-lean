import Googology.Trans.PoR.InaccPsi.R2.TjWalk

/-!
# ONE level system up to `G = φ(Ω₂, 1)` with the levels read by `Θ`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `Θ̂_L = Td.tdThL` (the image of the normal-form term with the
node levels read by `Θ`: `φ(a, Ω₂ + Y) ↦ φ(Θ a, Ω₁ + Ŷ)`), `CL = Sn.SnCL`, `G1 = ψ_{Ω₂}(0)`, `G3 = ψ_{Ω₃}(0)`.

* `tjThL_cnf` (`Θ̂_L(W^e·q + r) = Ω^{Θ̂_L e}·Θ q + Θ̂_L r` off the fixed points), `tjThL_own` (**`Θ̂_L E ∈ Cl(0, Θ T)`
  and `Θ̂_L E` is a level-1 code over every strongly critical `Q ≥ Θ T`** when `E < G` in `H_λ` is a code over every
  `Q ≥ T`: at a node `φ(a, y)` the level `a` is a code below `T`, `Td.tdCl_lev_lt`), `tjThL_lt_G`;
* `tjOwP` (the closure condition is an own predicate with data), `tjLev` (**THE LEVEL STATEMENT AT EVERY
  `1 ≤ E < G` OF `H_λ`**: `Tj.tjLev_term` with `Tj.tjOwn_of_cl`);
* `tjG_lim`, `tjG_lt_G3`, `tjLS` (**THE LEVEL SYSTEM `St.StLS S λ G Θ̂_L`**: every level `1 ≤ E < φ(Ω₂, 1)` of the
  hull, code levels included; no hypothesis beyond the restart index).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.St
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg

variable {S : InaccSeq.{0}}

theorem tjG_lim : IsSuccLimit (veblen (Om (1 + 1 : Ordinal.{0})) 1) := taVeb_lim ldOm2_SC.1.ne'

theorem tjG_lt_G3 : veblen (Om (1 + 1 : Ordinal.{0})) 1 < S.psi 0 (Om (1 + 1 + 1)) := by
  have hG3 := rwG3_SC (S := S)
  exact hG3.2 _ rwW_lt_G3 _ (gg_one_lt_of_SC hG3)

/-- **`Θ̂_L(W^e·q + r) = Ω^{Θ̂_L e}·Θ q + Θ̂_L r`** off the fixed points (the remainder's term well formed). -/
theorem tjThL_cnf {l : Ordinal.{0}} (h1 : (1 : Ordinal.{0}) ≤ upsilon l) {E : Ordinal.{0}} (h : 0 < E ∧ sgLW E < E)
    (hr : TgWF S l (taTm (E % leWe (sgLW E)))) :
    tdThL S l E = leOe (tdThL S l (sgLW E)) * gxTh (upsilon l) (ldAtR S l) (E / leWe (sgLW E)) +
      tdThL S l (E % leWe (sgLW E)) := by
  unfold tdThL
  rw [taTm_eq h, tgI_cat h1 _ _ hr]
  show 0 + _ + _ = _
  rw [zero_add]

section Own

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The image `Θ̂_L E` of an exponent that is a code above `T`** is in `Cl(0, Θ T)` and a level-1 code above
`Θ T`. -/
theorem tjThL_own : ∀ E, E ∈ cdHull S l → E < veblen (Om (1 + 1)) 1 → ∀ T, SC T →
    (∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q E) →
    tdThL S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) ∧
      ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → LeCl (Om 1) Q (tdThL S l E) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE T hT hcl
  rcases eq_or_ne E 0 with rfl | hE0
  · have h0 : tdThL S l 0 = 0 := by unfold tdThL; rw [taTm_zero]; rfl
    rw [h0]; exact ⟨CSet.zero_mem _ _, fun Q hQ _ => LeCl.zero hQ.1⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  by_cases hc : 0 < E ∧ sgLW E < E
  swap
  · -- a node with a code level
    obtain ⟨ha1, haW, hΩy, hyE, hval⟩ := tdNode_nfW hE1 hE (fun h => hc ⟨hpos, h⟩)
    have haE : invVeblen₁ E < E := haW.trans (hΩy.trans hyE)
    have hmem := mem_of_veblen_mem (by rw [hval]; exact hEH) (by rw [hval]; exact haE) (by rw [hval]; exact hyE)
    have hyH : invVeblen₂ E ∈ cdHull S l := hmem.2
    have hac : GxCl (upsilon l) (ldAtR S l) (invVeblen₁ E) := (ldHull_iff hl hX haW).1 hmem.1
    have hy'H : invVeblen₂ E - Om (1 + 1) ∈ cdHull S l := taSub_mem _ hyH _
    have hy'E : invVeblen₂ E - Om (1 + 1) < E := (Ordinal.sub_le_self _ _).trans_lt hyE
    have hEcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (veblen (invVeblen₁ E) (invVeblen₂ E)) :=
      fun Q hQ hTQ => by rw [hval]; exact hcl Q hQ hTQ
    have hycl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (invVeblen₂ E - Om (1 + 1)) := fun Q hQ hTQ => by
      have hy := taCl_inv hQ ldOm2_SC haW (hEcl Q hQ hTQ)
      exact (leClDec hQ ldOm2_SC _ hy).1 _ LeCl.om hΩy.le
    have haT : invVeblen₁ E < T :=
      tdCl_lev_lt hT ldOm2_SC (hEcl T hT le_rfl) (by rw [hval]; exact hyE) haW
    have hΘaT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hac haT
    obtain ⟨h1, h2⟩ := IH _ hy'E hy'H (hy'E.trans hE) T hT hycl
    rw [tdThL_node hc ⟨hΩy, hyE⟩]
    exact ⟨CSet.phi_mem (CSet.of_lt hΘaT) (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) h1),
      fun Q hQ hTQ => LeCl.phi (LeCl.small (hΘaT.trans_le hTQ)) (LeCl.add LeCl.om (h2 Q hQ hTQ))⟩
  set e := sgLW E with he
  have hel : e < E := hc.2
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have heH : e ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hEH)
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hrH : E % leWe e ∈ cdHull S l := leModP_mem (Om (1 + 1) * e) hEH
  have hE2 : E < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
    have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt E
  have hqH : E / leWe e ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hEH hE2
  have hqW : E / leWe e < Om (1 + 1) := by
    have h2 : E < leWe e * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt E
    exact (Ordinal.lt_mul_iff_div_lt hW0).1 h2
  have hqc : GxCl (upsilon l) (ldAtR S l) (E / leWe e) := (ldHull_iff hl hX hqW).1 hqH
  have hecl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ => (Sw.swCl_cnf hQ (hcl Q hQ hTQ)).1
  have hrcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (E % leWe e) := fun Q hQ hTQ =>
    (Sw.swCl_cnf hQ (hcl Q hQ hTQ)).2.1
  have hqT : E / leWe e < T := (Sw.swCl_cnf hT (hcl T hT le_rfl)).2.2
  have hΘq := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hqc hqT
  obtain ⟨he1, he2⟩ := IH e hel heH (hel.trans hE) T hT hecl
  obtain ⟨hr1, hr2⟩ := IH _ hr hrH (hr.trans hE) T hT hrcl
  rw [tjThL_cnf h1ρ hc (tgTm_spec hl hX _ hrH (hr.trans hE)).1]
  refine ⟨CSet.add_mem (leMulOe_mem he1 (CSet.of_lt hΘq)) hr1, fun Q hQ hTQ => ?_⟩
  refine LeCl.add ?_ (hr2 Q hQ hTQ)
  exact rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (he2 Q hQ hTQ)) Ph.ph_SC_Om1 _
    (LeCl.small (hΘq.trans_le hTQ))

/-- **`Θ̂_L E < ψ_{Ω₂}(0)`** for every `E < G` in the hull. -/
theorem tjThL_lt_G {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE : E < veblen (Om (1 + 1)) 1) :
    tdThL S l E < S.psi 0 (Om (1 + 1)) :=
  (tgV_lt_G3 hl hX (taTm E) (tgTm_spec hl hX E hEH hE).1).2

/-- **The closure condition is an own predicate with data** (`Sc.ScOwP`), code levels included. -/
theorem tjOwP {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen (Om (1 + 1)) 1) :
    ScOwP S l (Sn.SnCL S E) E (tdThL S l E) := by
  refine ⟨fun b X0 h => ?_, fun b β X0 X0' h hb hX' => Sn.snCL_mono h hb hX'⟩
  have hT : SC (S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1))) := SC_psi (InR_Om_succ 1) _
  obtain ⟨h1, h2⟩ := tjThL_own hl hX E hEH hE _ hT h
  exact ⟨hE1, hEH, sjCl_mem (h _ hT le_rfl), h1, h, h2⟩

/-- **THE LEVEL STATEMENT AT EVERY `1 ≤ E < φ(Ω₂, 1)` OF `H_λ` WITH THE CLOSURE CONDITION**:
`Sc.ScLev (CL E) E (Θ̂_L E)`, code levels included. -/
theorem tjLev {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hE : E < veblen (Om (1 + 1)) 1) :
    ScLev S l (Sn.SnCL S E) E (tdThL S l E) := by
  obtain ⟨hw, -, hv⟩ := tgTm_spec hl hX E hEH hE
  have hL := (tjLev_term hl hX (taTm E) hw (by rw [hv]; exact hE1)).1
  rw [hv] at hL
  intro b X0 Xh0 hoff hd hG3 hG hcl β Â hb hbβ hÂ hbase
  have hoffβ := rvOff_mono hbβ hoff
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoffβ
  have hb' := hb
  obtain ⟨hβd, -, -, hβown, -⟩ := hb'
  rw [add_zero] at hβd hβown
  have hOw : TjOwn S β X0 (fun y => y) (taTm E) :=
    tjOwn_of_cl hl hX hβd hβown hX0m hX0cl (le_self_add.trans_lt hG3)
      (fun Q hQ hQ' => hcl Q hQ ((psi_mono (S := S) (InR_Om_succ 1) (add_le_add_left hbβ _)).1.trans hQ')) hEH hE
  exact hL β X0 Xh0 hoffβ hd hG3 hG hOw β Â hb le_rfl hÂ hbase

end Own

/-- **THE LEVEL SYSTEM UP TO `G = φ(Ω₂, 1)` WITH CODE LEVELS**: `St.StLS S λ G Θ̂_L`. -/
theorem tjLS {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) :
    StLS S l (veblen (Om (1 + 1)) 1) (tdThL S) :=
  ⟨tjG_lim, tjG_lt_G3, fun _ hEH _ hE => tjThL_lt_G hl hX hEH hE,
    fun _ hEH h1 hE => tjOwP hl hX hEH h1 hE, fun _ hEH h1 hE => tjLev hl hX hEH h1 hE⟩

end Googology.Trans.PoR.InaccPsi.R2.Tj
