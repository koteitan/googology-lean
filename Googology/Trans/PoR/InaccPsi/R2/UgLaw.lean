import Googology.Trans.PoR.InaccPsi.R2.UgMono

/-!
# The laws of the image past `Γ₂`: the φ law, the atom law, the bounds, the sum laws, the wall of `St.StLS`

`T = Ug.ugTh S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`Γ₂ = Ua.uaGam = ψ₃(0)`, `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`, `Y₃ = ψ₃(Ω₃)`.

* `ugGam` (**`T Γ₂ = ψ₂(0)`**, `ψ₂(0)` the bound of every image below `Γ₂`), `ugGam_mem`;
* `ugAtom` (**THE ATOM LAW**: `T(ψ₃(d)) = ψ₂(T d)` with `ψ₂(T d)` in normal form, `d ∈ H_λ ∩ Y₃`);
* `ugVeb` (**THE φ LAW PAST `Γ₂`, FIXED POINTS AND STRONGLY CRITICAL VALUES INCLUDED**: `T(φ(a, y)) = φ(T a, T y)`
  for `a ≠ 0`, `a, y ∈ H_λ`, `Γ₂ ≤ φ(a, y) < Y₃`);
* `ugLtY2` (**`T x < ψ₂(Ω₂)`** on `H_λ ∩ Y₃`: the image of `H_λ ∩ ψ₃(Ω₃)` lies below `ψ₂(Ω₂)`);
* `ugAdd`, `ugTerm`, `ugAddT`, `ugAddW`, `ugSucc`, `ugDvd` (the sum laws of `Ua.uaAdd` … `Ua.uaDvd` up to `Y₃`);
* `ugWall` (**THE WALL OF THE FIELD `ltG`**: a bound `E_b` with `T E < ψ₂(0)` for every `1 ≤ E < E_b` of `H_λ` has
  `E_b ≤ Γ₂`; so a level system with images `T` past `Γ₂` must drop both `ltG3` and `ltG` of `St.StLS`, and the
  bounds `ltG3`, `ltG` of `Rv.RvSh` / `Ro.RoSh`), `ugLS_iff` (**`St.StLS` with `T` is `St.StLS` with `Ua.uaTh`**),
  `ugLS` (every limit `E_b < Γ₂`).

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
  Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

/-- **`T Γ₂ = ψ₂(0)`.** -/
theorem ugGam (l : Ordinal.{0}) : ugTh S l uaGam = S.psi 0 (Om (1 + 1)) := by
  have h0 : (0 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (SC_psi ugInR3 0).1
  rw [udGam_eq (S := S), ugTh_atom h0, ugTh_zero]

/-- `Γ₂ ∈ H_λ`. -/
theorem ugGam_mem (l : Ordinal.{0}) : uaGam ∈ cdHull S l := by
  rw [udGam_eq (S := S)]
  exact CSet.psi_mem (lg_A_pos _) ugInR3 (Ry.ryOm3_mem _ _) (CSet.zero_mem _ _)

/-- **THE WALL OF THE FIELD `ltG`**: if every `1 ≤ E < E_b` of `H_λ` has `T E < ψ₂(0)`, then `E_b ≤ Γ₂`. -/
theorem ugWall {l Eb : Ordinal.{0}}
    (h : ∀ E, E ∈ cdHull S l → 1 ≤ E → E < Eb → ugTh S l E < S.psi 0 (Om (1 + 1))) : Eb ≤ uaGam := by
  by_contra hc
  push Not at hc
  have h1 : (1 : Ordinal.{0}) ≤ uaGam := Order.one_le_iff_pos.2 ugGam_pos
  have := h uaGam (ugGam_mem l) h1 hc
  rw [ugGam] at this
  exact lt_irrefl _ this

/-- **`St.StLS` with `T` is `St.StLS` with `Ua.uaTh`.** -/
theorem ugLS_iff {l Eb : Ordinal.{0}} : StLS S l Eb (ugTh S) ↔ StLS S l Eb (uaTh S) := by
  have key : ∀ {Th Th' : Ordinal.{0} → Ordinal.{0} → Ordinal.{0}},
      (∀ E, E < uaGam → Th l E = Th' l E) → StLS S l Eb Th → StLS S l Eb Th' := by
    intro Th Th' heq hS
    have hEb : Eb < uaGam := udLS_wall hS
    refine ⟨hS.lim, hS.ltG3, fun E hEH h1 hE => ?_, fun E hEH h1 hE => ?_, fun E hEH h1 hE => ?_⟩
    · rw [← heq E (hE.trans hEb)]; exact hS.ltG E hEH h1 hE
    · rw [← heq E (hE.trans hEb)]; exact hS.own E hEH h1 hE
    · rw [← heq E (hE.trans hEb)]; exact hS.lev E hEH h1 hE
  exact ⟨key (fun E hE => ugTh_lt hE), key (fun E hE => (ugTh_lt hE).symm)⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE ATOM LAW**: `T(ψ₃(d)) = ψ₂(T d)` with `ψ₂(T d)` in normal form (`d ∈ H_λ`, `d < ψ₃(d)`, `ψ₃(d) < Y₃`). -/
theorem ugAtom {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hd : d < S.psi d (Om (1 + 1 + 1)))
    (hY : S.psi d (Om (1 + 1 + 1)) < ugY S) :
    ugTh S l (S.psi d (Om (1 + 1 + 1))) = S.psi (ugTh S l d) (Om (1 + 1)) ∧
      ugTh S l d ∈ S.CSet (ugTh S l d) (S.psi (ugTh S l d) (Om (1 + 1))) ∧
      ugTh S l d < S.psi (ugTh S l d) (Om (1 + 1)) :=
  ⟨ugTh_atom hd, ugNormAll hl hX hdH (hd.trans hY)⟩

/-- **THE φ LAW PAST `Γ₂`**: `T(φ(a, y)) = φ(T a, T y)` (`a ≠ 0`, `Γ₂ ≤ φ(a, y) < Y₃`). -/
theorem ugVeb {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hyH : y ∈ cdHull S l) (ha0 : a ≠ 0)
    (hG : uaGam ≤ veblen a y) (hY : veblen a y < ugY S) :
    ugTh S l (veblen a y) = veblen (ugTh S l a) (ugTh S l y) := by
  set x := veblen a y with hx_def
  have hxH : x ∈ cdHull S l := CSet.phi_mem haH hyH
  have hε : ω ^ x = x := gg_veblen_eps ha0
  have hΩx : Om (1 + 1) < x := uaGam_spec.2.trans_le hG
  have hxs : ¬ sgLW x < x := by rw [(uaWfix hε hΩx).1]; exact lt_irrefl _
  by_cases hS : SC x
  · -- a strongly critical value: an atom
    obtain ⟨d, -, hd, -, hxd⟩ := ugAtomH hl hX hxH hS hΩx hY
    have hTS : SC (ugTh S l x) := by rw [← hxd, ugTh_atom hd]; exact SC_psi (InR_Om_succ 1) _
    rcases (left_le_veblen a y).lt_or_eq with hax | hax
    · -- `a < x`: then `y = x`
      have hyx : y = x := by
        rcases (right_le_veblen a y).lt_or_eq with hyx | hyx
        · exact absurd (hS.2 a hax y hyx) (lt_irrefl _)
        · exact hyx
      have hTa : ugTh S l a < ugTh S l x := ugLt hl hX haH hxH hY hax
      conv_rhs => rw [hyx, ← hTS.veblen_zero, veblen_veblen_of_lt hTa 0, hTS.veblen_zero]
    · -- `a = x`: then `y = 0`
      have hy0 : y = 0 := by
        have h2 : veblen a y = veblen a 0 := by
          conv_rhs => rw [hax, hS.veblen_zero]
        exact veblen_injective a h2
      have hax' : a = x := hax
      rw [hy0, ugTh_zero, hax', hTS.veblen_zero]
  obtain ⟨-, hv, -, haxE, hbxE, -, -⟩ := ugNode hG hS hxs
  have hT := (ugNodeTh hl hX hxH hG hY hS hxs).1
  rcases (right_le_veblen a y).lt_or_eq with hlt | heq
  · have h1 : invVeblen₁ x = a := invVeblen₁_veblen hlt
    have h2 : invVeblen₂ x = y := invVeblen₂_veblen ha0 hlt
    rw [hT, h1, h2]
  -- the fixed point `y = φ(a, y)`
  set b := invVeblen₁ x with hb_def
  set w := invVeblen₂ x with hw_def
  have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haxE) (by rw [hv]; exact hbxE)
  have hyx : y = x := heq
  have hab : a < b := by
    rcases lt_trichotomy a b with h | h | h
    · exact h
    · exfalso
      rw [← h] at hv
      have : w = y := by
        have h2 : veblen a w = veblen a y := by rw [hv]
        exact veblen_injective a h2
      rw [this, hyx] at hbxE; exact lt_irrefl _ hbxE
    · exfalso
      have hfix : veblen b x = x := by
        conv_lhs => rw [hx_def]
        exact veblen_veblen_of_lt h _
      have h2 : veblen b w = veblen b x := by rw [hfix, hv]
      have := veblen_injective b h2
      rw [this] at hbxE; exact lt_irrefl _ hbxE
  have hTab : ugTh S l a < ugTh S l b := ugLt hl hX haH hmem.1 (haxE.trans hY) hab
  conv_rhs => rw [hyx, hT]
  rw [veblen_veblen_of_lt hTab, ← hT]

/-- **`T x < ψ₂(Ω₂)`** on `H_λ ∩ Y₃`. -/
theorem ugLtY2 : ∀ x, x ∈ cdHull S l → x < ugY S → ugTh S l x < S.psi (Om (1 + 1)) (Om (1 + 1)) := by
  have hP := SC_psi (S := S) (InR_Om_succ 1) (Om (1 + 1))
  have hΩP : Om (1 : Ordinal.{0}) < S.psi (Om (1 + 1)) (Om (1 + 1)) := (psiS_bounds (S := S) _ 1).1
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxY
  rcases lt_or_ge x uaGam with hxE | hGx
  · rw [ugTh_lt hxE]
    exact (uaLtG1 hl hX x hxH hxE).trans_le (psi_mono (InR_Om_succ 1) zero_le).1
  have h0 : 0 < x := ugGam_pos.trans_le hGx
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -⟩ := uaBase hl hX hxH h0
    have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le h0)
    rw [ugTh_cnf hGx hs]
    exact hP.isPrincipal (ldMul_lt_SC hP (leOe_lt_SC hP hΩP (IH _ hs hgH (hs.trans hxY))).1
      ((snTh_lt_Om1 hl hX hdW.le).trans hΩP)) (IH _ hrx hrH (hrx.trans hxY))
  by_cases hS : SC x
  · obtain ⟨d, hdH, hd, -, rfl⟩ := ugAtomH hl hX hxH hS (uaGam_spec.2.trans_le hGx) hxY
    rw [ugTh_atom hd]
    exact psi_lt_psi (InR_Om_succ 1) (ugLtOm2 hl hX d hdH (hd.trans hxY))
      (ugNormAll hl hX hdH (hd.trans hxY)).1
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := ugNode hGx hS hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    rw [ugTh_node hGx hs hS ⟨haE, hbE⟩]
    exact hP.2 _ (IH _ haE hmem.1 (haE.trans hxY)) _ (IH _ hbE hmem.2 (hbE.trans hxY))

/-- **`T(e + y) = T e + T y` when `W^{log_W y + 1} ∣ e`** (`e, y ∈ H_λ`, `e + y < Y₃`). -/
theorem ugAdd : ∀ e, e ∈ cdHull S l → ∀ y, y ∈ cdHull S l → e + y < ugY S →
    leWe (sgLW y + 1) ∣ e → ugTh S l (e + y) = ugTh S l e + ugTh S l y := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH y hyH hlt hd
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, ugTh_zero, add_zero]
  rcases eq_or_ne e 0 with rfl | he0
  · rw [zero_add, ugTh_zero, zero_add]
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  have heE : e < ugY S := le_self_add.trans_lt hlt
  obtain ⟨hs, hdr⟩ := tuDvd_parts he0' hd
  obtain ⟨-, -, -, -, hdW, hrH, hrg, hedec, hTe, -⟩ := ugParts hl hX heH he0' heE
  set g := sgLW e with hg
  set d := e / leWe g with hd_def
  set r := e % leWe g with hr_def
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have hyg : y < leWe g := (sgLW_lt y).trans_le (leWe_mono hs)
  have hry : r + y < leWe g := (isPrincipal_add_omega0_opow (Om (1 + 1) * g)) hrg hyg
  have hey : e + y = leWe g * d + (r + y) := by
    conv_lhs => rw [hedec]
    rw [add_assoc]
  have hdiv : (e + y) / leWe g = d := by
    rw [hey, Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hry, add_zero]
  have hmod : (e + y) % leWe g = r + y := by
    rw [hey, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hry]
  have hsg : sgLW (e + y) = g := by
    have h1 : leWe g ≤ e + y := (sgLW_le he0').trans le_self_add
    have h2 : e + y < leWe (g + 1) := by
      rw [hey, leWe_succ]
      calc leWe g * d + (r + y) < leWe g * d + leWe g := (add_lt_add_iff_left _).2 hry
        _ = leWe g * (d + 1) := (mul_add_one _ _).symm
        _ ≤ leWe g * Om (1 + 1) := mul_le_mul_left' (Order.add_one_le_of_lt hdW) _
    obtain ⟨a1, a2⟩ := sjLogW h1 h2
    exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
  have hrx : r < e := hrg.trans_le (sgLW_le he0')
  have hrylt : r + y < ugY S := (add_le_add_left hrx.le y).trans_lt hlt
  have hIH := IH r hrx hrH y hyH hrylt hdr
  have heyH : e + y ∈ cdHull S l := CSet.add_mem heH hyH
  have hey0 : 0 < e + y := he0'.trans_le le_self_add
  rw [(ugParts hl hX heyH hey0 hlt).2.2.2.2.2.2.2.2.1, hsg, hdiv, hmod, hIH, hTe, add_assoc]

/-- `T(W^f·c) = Ω^{T f}·Θ c` for `1 ≤ c < Ω₂`, `W^f·c < Y₃`. -/
theorem ugTerm {f c : Ordinal.{0}} (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hH : leWe f * c ∈ cdHull S l)
    (hlt : leWe f * c < ugY S) :
    ugTh S l (leWe f * c) = leOe (ugTh S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have h0 : 0 < leWe f * c := mul_pos (leWe_pos f) (zero_lt_one.trans_le hc1)
  obtain ⟨e1, e2, e3⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [(ugParts hl hX hH h0 hlt).2.2.2.2.2.2.2.2.1, e1, e2, e3, ugTh_zero, add_zero]

/-- `T(e + W^f·c) = T e + Ω^{T f}·Θ c` for `W^{f+1} ∣ e`. -/
theorem ugAddT {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hcH : c ∈ cdHull S l) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe f * c < ugY S) :
    ugTh S l (e + leWe f * c) = ugTh S l e + leOe (ugTh S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have hyH : leWe f * c ∈ cdHull S l := leMulWe_mem hfH hcH
  obtain ⟨hs, -, -⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [ugAdd hl hX e heH _ hyH hlt (by rw [hs]; exact hd), ugTerm hl hX hc1 hcW hyH (le_add_self.trans_lt hlt)]

/-- **`T(e + W^f) = T e + Ω^{T f}` for `W^f ∣ e`.** -/
theorem ugAddW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < ugY S) :
    ugTh S l (e + leWe f) = ugTh S l e + leOe (ugTh S l f) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  set m := leWe (f + 1) * (e / leWe (f + 1)) with hm
  set s := e % leWe (f + 1) with hs
  have hmH : m ∈ cdHull S l := Ts.ts_mod_mem le_add_self e heH
  have hsH : s ∈ cdHull S l := leModP_mem (Om (1 + 1) * (f + 1)) heH
  have hes : e = m + s := (Ordinal.div_add_mod e _).symm
  have hsW : s < leWe (f + 1) := Ordinal.mod_lt _ (leWe_pos _).ne'
  have hsd : leWe f ∣ s := tuDvd_mod hd le_self_add
  set d := s / leWe f with hd_def
  have hsdec : s = leWe f * d := by
    obtain ⟨q, hq⟩ := hsd
    rw [hd_def, hq, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
  have hdW : d < Om (1 + 1) := by
    have : s < leWe f * Om (1 + 1) := by rw [← leWe_succ]; exact hsW
    exact (Ordinal.lt_mul_iff_div_lt (leWe_pos _).ne').1 this
  have hdH : d ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hsH ?_
    have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact hsW
  have hdc : GxCl (upsilon l) (ldAtR S l) d := (ldHull_iff hl hX hdW).1 hdH
  have hmd : leWe (f + 1) ∣ m := dvd_mul_right _ _
  have hd1W : d + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hdW
  have hd1H : d + 1 ∈ cdHull S l := CSet.succ_mem hdH
  have he2 : e + leWe f = m + leWe f * (d + 1) := by rw [hes, hsdec, mul_add_one, add_assoc]
  rw [he2, ugAddT hl hX hmH hfH hd1H le_add_self hd1W hmd (he2 ▸ hlt), gxTh_add hρSC hAt hdc,
    sqTh_one hl hX, mul_add_one, ← add_assoc]
  congr 1
  rw [hes, hsdec]
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
  · exact (ugAddT hl hX hmH hfH hdH (Order.one_le_iff_ne_zero.2 h0) hdW hmd
      ((le_self_add.trans_eq (by rw [hes, hsdec])).trans_lt hlt)).symm

/-- `T(e + 1) = T e + 1`. -/
theorem ugSucc {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (hlt : e + 1 < ugY S) :
    ugTh S l (e + 1) = ugTh S l e + 1 := by
  have h := ugAddW hl hX heH (CSet.zero_mem _ _) (by rw [leWe_zero]; exact one_dvd _) (by rwa [leWe_zero])
  rwa [leWe_zero, ugTh_zero, leOe_zero] at h

/-- **`W^f ∣ e` gives `Ω^{T f} ∣ T e`.** -/
theorem ugDvd : ∀ e, e ∈ cdHull S l → e < ugY S → ∀ f, f ∈ cdHull S l →
    leWe f ∣ e → leOe (ugTh S l f) ∣ ugTh S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH heE f hfH hd
  rcases eq_or_ne e 0 with rfl | he0
  · rw [ugTh_zero]; exact dvd_zero _
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  obtain ⟨hgH, hge, -, -, -, hrH, hrg, -, hTe, -⟩ := ugParts hl hX heH he0' heE
  set g := sgLW e with hg
  have hfg : f ≤ g := by
    obtain ⟨q, hq⟩ := hd
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact he0 hq
    have hle : leWe f ≤ e := by
      rw [hq]; exact (mul_one _).symm.le.trans (mul_le_mul_left' (Order.one_le_iff_ne_zero.2 hq0) _)
    exact (sjLogW hle (sgLW_lt e)).1
  have hrx : e % leWe g < e := hrg.trans_le (sgLW_le he0')
  have hIH := IH _ hrx hrH (hrx.trans heE) f hfH (tuDvd_mod hd hfg)
  rw [hTe]
  exact dvd_add ((tuOe_dvd (ugLe hl hX hfH hgH (hge.trans_lt heE) hfg)).trans (dvd_mul_right _ _)) hIH

/-- **The level systems of `T` below `Γ₂`** (`Ud.udLS`). -/
theorem ugLS {Eb : Ordinal.{0}} (hEb : IsSuccLimit Eb) (hEbG : Eb < uaGam) : StLS S l Eb (ugTh S) :=
  ugLS_iff.2 (udLS hl hX hEb hEbG)

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ug
