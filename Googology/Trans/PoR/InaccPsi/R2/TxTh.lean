import Googology.Trans.PoR.InaccPsi.R2.TuSysG

/-!
# The image `Θ̂_L` on the whole hull below `G = φ(Ω₂, 1)`: nodes, normal form, bounds, monotonicity, sums

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`G = φ(Ω₂, 1)`, `Ĝ = φ(Ω₁, 1)`.  Every `x ∈ H_λ`, `0 < x < G`, is `W^g·d + r` (`g = log_W x ≤ x`, `d` a code below
`Ω₂`, `r < W^g`); either `g < x`, or `x` is a **node** `φ(a, Ω₂ + z)` (`1 ≤ a < Ω₂`, `z ≥ 1`, `Ω₂ + z < x`, `W^x = x`,
`g = x`, `d = 1`, `r = 0`).

* `txNode` (the node data), `txPos` (`Θ̂_L x > 0`), `txNodeTh` (`Θ̂_L x = φ(Θ a, Ω₁ + Θ̂_L z)`, `Ω^{Θ̂_L x} = Θ̂_L x`),
  `txParts` / `txCnf` (**the normal form `Θ̂_L x = Ω^{Θ̂_L g}·Θ d + Θ̂_L r` at every `0 < x < G`, nodes included**);
* `txMono` (**`Θ̂_L` is strictly increasing on `H_λ ∩ G`**), `txLt`, `txLe`;
* `txAdd`, `txTerm`, `txAddT`, `txAddW`, `txSucc`, `txDvd` (the sum laws of `Tu.tuThG_*` up to `G`);
* `txVeb` (**THE φ LAW AT EVERY NODE FORM, FIXED POINTS INCLUDED**: `Θ̂_L(φ(a, Ω₂ + z)) = φ(Θ a, Ω₁ + Θ̂_L z)`);
* `txLtGh` (`Θ̂_L x < Ĝ`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

/-- `log_W E ≤ E`. -/
theorem txSg_le (E : Ordinal.{0}) : sgLW E ≤ E :=
  (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ ldOm2_SC.1)).trans (log_le_self ω E)

/-- `Ω₁ + X = X` for `X = φ(a, y) > Ω₁` (`a ≠ 0`). -/
theorem txOm1_add {a y : Ordinal.{0}} (ha : a ≠ 0) (h : Om 1 < veblen a y) : Om 1 + veblen a y = veblen a y := by
  have hE := gg_veblen_eps (y := y) ha
  rw [← hE]
  exact Ordinal.add_absorp (by rw [hE]; exact h) le_rfl

/-- `Ω₂ + X = X` for `X = φ(a, y) > Ω₂` (`a ≠ 0`). -/
theorem txOm2_add {a y : Ordinal.{0}} (ha : a ≠ 0) (h : Om (1 + 1) < veblen a y) :
    Om (1 + 1) + veblen a y = veblen a y := by
  have hE := gg_veblen_eps (y := y) ha
  rw [← hE]
  exact Ordinal.add_absorp (by rw [hE]; exact h) le_rfl

/-- `G` is principal for `+`. -/
theorem txG_prin : IsPrincipal (· + ·) (veblen (Om (1 + 1 : Ordinal.{0})) 1) := Ph.ph_veblen_prin _ _

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The node data**: a `W`-fixed point `0 < E < G` of `H_λ` is `φ(a, Ω₂ + z)` with `1 ≤ a < Ω₂` a code of
`H_λ`, `1 ≤ z ∈ H_λ`, `Ω₂ + z < E`. -/
theorem txNode {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (h0 : 0 < E) (hE : E < veblen (Om (1 + 1)) 1)
    (hfix : ¬ sgLW E < E) :
    ∃ a z, E = veblen a (Om (1 + 1) + z) ∧ 1 ≤ a ∧ a < Om (1 + 1) ∧ 1 ≤ z ∧ Om (1 + 1) + z < E ∧
      a ∈ cdHull S l ∧ z ∈ cdHull S l ∧ GxCl (upsilon l) (ldAtR S l) a := by
  obtain ⟨h1a, haW, hΩy, hyE, hval⟩ := tdNode_nfW (Order.one_le_iff_pos.2 h0) hE hfix
  have hy : Om (1 + 1) + (invVeblen₂ E - Om (1 + 1)) = invVeblen₂ E := Ordinal.add_sub_cancel_of_le hΩy.le
  have hz1 : 1 ≤ invVeblen₂ E - Om (1 + 1) := by
    rw [Order.one_le_iff_ne_zero]
    intro h
    rw [Ordinal.sub_eq_zero_iff_le] at h
    exact absurd h (not_le.2 hΩy)
  have haE : invVeblen₁ E < veblen (invVeblen₁ E) (invVeblen₂ E) := by
    rw [hval]; exact haW.trans (hΩy.trans hyE)
  have hyE' : invVeblen₂ E < veblen (invVeblen₁ E) (invVeblen₂ E) := by rw [hval]; exact hyE
  have hEH' : veblen (invVeblen₁ E) (invVeblen₂ E) ∈ cdHull S l := by rw [hval]; exact hEH
  obtain ⟨haH, hyH⟩ := mem_of_veblen_mem hEH' haE hyE'
  refine ⟨invVeblen₁ E, invVeblen₂ E - Om (1 + 1), by rw [hy, hval], h1a, haW, hz1, by rw [hy]; exact hyE, haH,
    Ta.taSub_mem (S := S) _ hyH _, (ldHull_iff hl hX haW).1 haH⟩

omit hl hX in
/-- `log_W E = E` and `W^E = E` at a node `E = φ(a, Ω₂ + z)` (`a ≠ 0`, `z ≥ 1`). -/
theorem txNode_W {a z : Ordinal.{0}} (ha : a ≠ 0) (hz : 1 ≤ z) :
    leWe (veblen a (Om (1 + 1) + z)) = veblen a (Om (1 + 1) + z) ∧
      sgLW (veblen a (Om (1 + 1) + z)) = veblen a (Om (1 + 1) + z) := by
  have hW := taWe_veb ha hz
  refine ⟨hW, ?_⟩
  conv_lhs => rw [← hW]
  exact taSgLW_We _

/-- **`Θ̂_L x > 0` for `0 < x < G` in `H_λ`.** -/
theorem txPos {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < veblen (Om (1 + 1)) 1) :
    0 < tdThL S l x := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  by_cases hs : sgLW x < x
  · have hrH : x % leWe (sgLW x) ∈ cdHull S l := leModP_mem (Om (1 + 1) * sgLW x) hxH
    have hrG : x % leWe (sgLW x) < veblen (Om (1 + 1)) 1 :=
      ((Ordinal.mod_lt _ (leWe_pos _).ne').trans_le (sgLW_le h0)).trans hx
    rw [tjThL_cnf h1ρ ⟨h0, hs⟩ (tgTm_spec hl hX _ hrH hrG).1]
    have hW0 : leWe (sgLW x) ≠ 0 := (leWe_pos _).ne'
    have hd0 : 0 < x / leWe (sgLW x) := (Ordinal.div_pos hW0).2 (sgLW_le h0)
    have hΘ : 0 < gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) := by
      have h := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.small (zero_lt_one.trans_le h1ρ)) hd0
      rwa [gxTh_zero] at h
    exact (mul_pos (leOe_pos _) hΘ).trans_le le_self_add
  · obtain ⟨a, z, rfl, h1a, -, hz1, hlt, -, -, -⟩ := txNode hl hX hxH h0 hx hs
    rw [tdThL_veb (zero_lt_one.trans_le h1a).ne' hz1 hlt]
    exact veblen_pos

/-- **The image of a node**: `Θ̂_L(φ(a, Ω₂ + z)) = φ(Θ a, Ω₁ + Θ̂_L z)` (`Ω₂ + z < φ(a, Ω₂ + z)`), and
`Ω^{Θ̂_L x} = Θ̂_L x`, `Ω₁ < Θ̂_L x`. -/
theorem txNodeTh {a z : Ordinal.{0}} (h1a : 1 ≤ a) (haW : a < Om (1 + 1)) (hz1 : 1 ≤ z) (hzH : z ∈ cdHull S l)
    (hlt : Om (1 + 1) + z < veblen a (Om (1 + 1) + z)) (hG : veblen a (Om (1 + 1) + z) < veblen (Om (1 + 1)) 1) :
    tdThL S l (veblen a (Om (1 + 1) + z)) = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l z) ∧
      leOe (tdThL S l (veblen a (Om (1 + 1) + z))) = tdThL S l (veblen a (Om (1 + 1) + z)) ∧
      Om 1 < tdThL S l (veblen a (Om (1 + 1) + z)) := by
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC (leRho hl hX).1
  have hT := tdThL_veb (S := S) (l := l) (zero_lt_one.trans_le h1a).ne' hz1 hlt
  have hzG : z < veblen (Om (1 + 1)) 1 := (le_add_self.trans_lt hlt).trans hG
  have hTz : 1 ≤ tdThL S l z := Order.one_le_iff_pos.2 (txPos hl hX hzH (zero_lt_one.trans_le hz1) hzG)
  have hΘa : gxTh (upsilon l) (ldAtR S l) a ≠ 0 := by
    have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) h1a
    rw [gxTh_small h1ρ.le] at h
    exact (zero_lt_one.trans_le h).ne'
  refine ⟨hT, by rw [hT]; exact taOe_veb hΘa hTz, ?_⟩
  rw [hT]
  exact (lt_add_of_pos_right _ (zero_lt_one.trans_le hTz)).trans_le (right_le_veblen _ _)

/-- **The parts of `x ∈ H_λ`, `0 < x < G`, and the normal form of `Θ̂_L x`** (nodes included). -/
theorem txParts {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < veblen (Om (1 + 1)) 1) :
    sgLW x ∈ cdHull S l ∧ sgLW x ≤ x ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) ∧
      tdThL S l x = leOe (tdThL S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) +
        tdThL S l (x % leWe (sgLW x)) ∧
      (sgLW x < x ∨ (sgLW x = x ∧ x / leWe (sgLW x) = 1 ∧ x % leWe (sgLW x) = 0)) := by
  have h1ρ : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC (leRho hl hX).1).le
  set g := sgLW x with hg
  have hW0 : leWe g ≠ 0 := (leWe_pos g).ne'
  have hWe : leWe g ≤ x := sgLW_le h0
  have hE2 : x < leWe g * Om (1 + 1) := by rw [← leWe_succ]; exact sgLW_lt x
  have hqW : x / leWe g < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hE2
  have hqH : x / leWe g ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * g) (dvd_mul_right _ _) hxH ?_
    have : leWe (g + 1) = ω ^ (Om (1 + 1) * g + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact sgLW_lt x
  have hrH : x % leWe g ∈ cdHull S l := leModP_mem (Om (1 + 1) * g) hxH
  have hrG : x % leWe g < veblen (Om (1 + 1)) 1 :=
    ((Ordinal.mod_lt _ hW0).trans_le hWe).trans hx
  have base : sgLW x ∈ cdHull S l ∧ sgLW x ≤ x ∧
      GxCl (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) ∧ 1 ≤ x / leWe (sgLW x) ∧ x / leWe (sgLW x) < Om (1 + 1) ∧
      x % leWe (sgLW x) ∈ cdHull S l ∧ x % leWe (sgLW x) < leWe (sgLW x) ∧
      x = leWe (sgLW x) * (x / leWe (sgLW x)) + x % leWe (sgLW x) :=
    ⟨ldDivK_mem ldOm2_SC (leLog_mem hxH), txSg_le x, (ldHull_iff hl hX hqW).1 hqH,
      Order.one_le_iff_pos.2 ((Ordinal.div_pos hW0).2 hWe), hqW, hrH, Ordinal.mod_lt _ hW0,
      (Ordinal.div_add_mod x (leWe g)).symm⟩
  by_cases hs : g < x
  · refine ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, tjThL_cnf h1ρ ⟨h0, hs⟩ (tgTm_spec hl hX _ hrH hrG).1, Or.inl hs⟩
  · obtain ⟨a, z, hxe, h1a, haW, hz1, hlt, -, hzH, -⟩ := txNode hl hX hxH h0 hx hs
    have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
    obtain ⟨hWx, hgx⟩ := txNode_W ha0 hz1
    rw [← hxe] at hWx hgx
    have hq : x / leWe g = 1 := by rw [hg, hgx, hWx]; exact Ordinal.div_self h0.ne'
    have hr : x % leWe g = 0 := by rw [hg, hgx, hWx]; exact Ordinal.mod_self x
    refine ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2.1, base.2.2.2.2.2.1, base.2.2.2.2.2.2.1,
      base.2.2.2.2.2.2.2, ?_, Or.inr ⟨hgx, hq, hr⟩⟩
    rw [hq, hr, sqTh_one hl hX, mul_one, tjThL_zero, add_zero, hg, hgx]
    have hxG : veblen a (Om (1 + 1) + z) < veblen (Om (1 + 1)) 1 := hxe ▸ hx
    have hlt' : Om (1 + 1) + z < veblen a (Om (1 + 1) + z) := hxe ▸ hlt
    have h := (txNodeTh hl hX h1a haW hz1 hzH hlt' hxG).2.1
    rw [← hxe] at h
    exact h.symm

/-- **The normal form of `Θ̂_L x`** at every `0 < x < G` of `H_λ`. -/
theorem txCnf {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < veblen (Om (1 + 1)) 1) :
    tdThL S l x = leOe (tdThL S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) +
      tdThL S l (x % leWe (sgLW x)) :=
  (txParts hl hX hxH h0 hx).2.2.2.2.2.2.2.2.1

/-- `Ω^{Θ̂_L x} = Θ̂_L x` at a node. -/
theorem txNode_Oe {x : Ordinal.{0}} (hxH : x ∈ cdHull S l) (h0 : 0 < x) (hx : x < veblen (Om (1 + 1)) 1)
    (hs : ¬ sgLW x < x) : leOe (tdThL S l x) = tdThL S l x := by
  obtain ⟨a, z, hxe, h1a, haW, hz1, hlt, -, hzH, -⟩ := txNode hl hX hxH h0 hx hs
  subst hxe
  exact (txNodeTh hl hX h1a haW hz1 hzH hlt hx).2.1

/-- **`Θ̂_L` is strictly increasing on `H_λ ∩ G`, and `x < W^y` gives `Θ̂_L x < Ω^{Θ̂_L y}`.** -/
theorem txMono : ∀ y, y ∈ cdHull S l → y < veblen (Om (1 + 1)) 1 →
    (∀ x, x ∈ cdHull S l → x < y → tdThL S l x < tdThL S l y) ∧
    (∀ x, x ∈ cdHull S l → x < veblen (Om (1 + 1)) 1 → x < leWe y → tdThL S l x < leOe (tdThL S l y)) := by
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC (leRho hl hX).1
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyH hyE
  -- the bound below `Ω^{Θ̂_L g}` from the strict increase at `y`
  have bnd : (∀ x, x ∈ cdHull S l → x < y → tdThL S l x < tdThL S l y) →
      ∀ x, x ∈ cdHull S l → x < veblen (Om (1 + 1)) 1 → x < leWe y → tdThL S l x < leOe (tdThL S l y) := by
    intro hM x hxH hxE hxy
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [tjThL_zero]; exact leOe_pos _
    have h0 := pos_iff_ne_zero.2 hx0
    obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hT, -⟩ := txParts hl hX hxH h0 hxE
    set g := sgLW x with hg
    have hgy : g < y := tuLogW_lt hx0 hxy
    have hrx : x % leWe g < veblen (Om (1 + 1)) 1 := ((hrg.trans_le (sgLW_le h0))).trans hxE
    have hrb : tdThL S l (x % leWe g) < leOe (tdThL S l g) :=
      (IH g hgy hgH (hgy.trans hyE)).2 _ hrH hrx hrg
    have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
    rw [hT]
    calc leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + tdThL S l (x % leWe g)
        < leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (tdThL S l g) :=
          (add_lt_add_iff_left _).2 hrb
      _ = leOe (tdThL S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
      _ ≤ leOe (tdThL S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
      _ = leOe (tdThL S l g + 1) := (leOe_succ _).symm
      _ ≤ leOe (tdThL S l y) := leOe_mono (Order.add_one_le_of_lt (hM g hgH hgy))
  have hM : ∀ x, x ∈ cdHull S l → x < y → tdThL S l x < tdThL S l y := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x IHx =>
    intro hxH hxy
    have hy0 : 0 < y := lt_of_le_of_lt zero_le hxy
    have hxE : x < veblen (Om (1 + 1)) 1 := hxy.trans hyE
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [tjThL_zero]; exact txPos hl hX hyH hy0 hyE
    have hx0' := pos_iff_ne_zero.2 hx0
    by_cases hys : sgLW y < y
    · -- `y` off the nodes
      obtain ⟨hgH, -, hdc, hd1, hdW, hrH, hrg, hydec, hTy, -⟩ := txParts hl hX hyH hy0 hyE
      set g := sgLW y with hg
      have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (y / leWe g) := by
        have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
        rwa [sqTh_one hl hX] at h
      have hTy' : leOe (tdThL S l g) ≤ tdThL S l y := by
        rw [hTy]
        exact ((mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)).trans le_self_add
      rcases lt_or_ge x (leWe g) with hxg | hxg
      · exact ((IH g hys hgH (hys.trans hyE)).2 x hxH hxE hxg).trans_le hTy'
      have hsx : sgLW x = g := by
        obtain ⟨a1, a2⟩ := sjLogW hxg (hxy.trans (sgLW_lt y))
        exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
      obtain ⟨-, -, hdxc, -, hdxW, hrxH, hrxg, hxdec, hTx, hxor⟩ := txParts hl hX hxH hx0' hxE
      rw [hsx] at hdxc hdxW hrxH hrxg hxdec hTx
      have hdd : x / leWe g ≤ y / leWe g :=
        (Ordinal.le_div (leWe_pos g).ne').2 ((Ordinal.mul_div_le x _).trans hxy.le)
      rw [hTx, hTy]
      have hb := (IH g hys hgH (hys.trans hyE)).2 _ hrxH ((hrxg.trans_le hxg).trans hxE) hrxg
      rcases hdd.lt_or_eq with hlt | heq
      · have hΘlt := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hdxc hlt
        calc leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + tdThL S l (x % leWe g)
            < leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (tdThL S l g) :=
              (add_lt_add_iff_left _).2 hb
          _ = leOe (tdThL S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
          _ ≤ leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (y / leWe g) :=
              mul_le_mul_left' (Order.add_one_le_of_lt hΘlt) _
          _ ≤ _ := le_self_add
      · rw [heq]
        refine (add_lt_add_iff_left _).2 ?_
        have hrr : x % leWe g < y % leWe g := by
          have h := hxy
          rw [hxdec, hydec, heq] at h
          exact (add_lt_add_iff_left _).1 h
        have hry : y % leWe g < y := hrg.trans_le (sgLW_le hy0)
        exact (IH _ hry hrH (hry.trans hyE)).1 _ hrxH hrr
    · -- `y` a node
      have hyO := txNode_Oe hl hX hyH hy0 hyE hys
      by_cases hxs : sgLW x < x
      · -- `x` off the nodes: `Θ̂_L x < Ω^{Θ̂_L g + 1} ≤ Ω^{Θ̂_L y}`
        have hgx := hxs
        obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hTx, -⟩ := txParts hl hX hxH hx0' hxE
        set g := sgLW x with hg
        have hgy : g < y := hgx.trans hxy
        have hTg : tdThL S l g < tdThL S l y := IHx g hgx hgH hgy
        have hrb : tdThL S l (x % leWe g) < leOe (tdThL S l g) :=
          (IH g hgy hgH (hgy.trans hyE)).2 _ hrH ((hrg.trans_le (sgLW_le hx0')).trans hxE) hrg
        have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
        rw [hTx, ← hyO]
        calc leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + tdThL S l (x % leWe g)
            < leOe (tdThL S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (tdThL S l g) :=
              (add_lt_add_iff_left _).2 hrb
          _ = leOe (tdThL S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
          _ ≤ leOe (tdThL S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
          _ = leOe (tdThL S l g + 1) := (leOe_succ _).symm
          _ ≤ leOe (tdThL S l y) := leOe_mono (Order.add_one_le_of_lt hTg)
      · -- both nodes: the Veblen comparison
        obtain ⟨a, z, hye, h1a, haW, hz1, hylt, -, hzH, hac⟩ := txNode hl hX hyH hy0 hyE hys
        obtain ⟨b, w, hxe, h1b, hbW, hw1, hxlt, -, hwH, hbc⟩ := txNode hl hX hxH hx0' hxE hxs
        have hTy := (txNodeTh hl hX h1a haW hz1 hzH (hye ▸ hylt) (hye ▸ hyE)).1
        have hTx := (txNodeTh hl hX h1b hbW hw1 hwH (hxe ▸ hxlt) (hxe ▸ hxE)).1
        have hOy := (txNodeTh hl hX h1a haW hz1 hzH (hye ▸ hylt) (hye ▸ hyE)).2.2
        rw [← hye] at hTy hOy
        rw [← hxe] at hTx
        have hcmp := hxy
        rw [hxe, hye] at hcmp
        rw [hTx, hTy]
        have hzy : z < y := le_add_self.trans_lt hylt
        have hwx : w < x := le_add_self.trans_lt hxlt
        rcases veblen_lt_veblen_iff.1 hcmp with ⟨rfl, hlt⟩ | ⟨hba, hlt⟩ | ⟨hab, hlt⟩
        · have hwz : w < z := (add_lt_add_iff_left _).1 hlt
          exact (veblen_lt_veblen_iff_right).2 ((add_lt_add_iff_left _).2
            ((IH z hzy hzH (hzy.trans hyE)).1 w hwH hwz))
        · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨gxTh_lt hbc hba, ?_⟩))
          rw [← hTy]
          -- `Ω₁ + Θ̂_L w < Θ̂_L y`
          have hwy : w < y := hwx.trans hxy
          have hTw : tdThL S l w < tdThL S l y := IHx w hwx hwH hwy
          have hTyp : IsPrincipal (· + ·) (tdThL S l y) := by
            rw [hTy]; exact Ph.ph_veblen_prin _ _
          exact hTyp (hTy ▸ hOy) hTw
        · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inr ⟨gxTh_lt hac hab, ?_⟩))
          -- `x < Ω₂ + z`, and `x ≠ z`, so `x < z`
          have hxz : x < Om (1 + 1) + z := by rw [hxe]; exact hlt
          have hb0 : b ≠ 0 := (zero_lt_one.trans_le h1b).ne'
          have hΩx : Om (1 + 1) < x := (lt_add_of_pos_right _ (zero_lt_one.trans_le hw1)).trans hxlt
          have hxz' : x ≤ z := by
            by_contra hc
            push Not at hc
            have hp : IsPrincipal (· + ·) x := by rw [hxe]; exact Ph.ph_veblen_prin _ _
            exact absurd (hp hΩx hc) (not_lt.2 hxz.le)
          rcases hxz'.lt_or_eq with hxz2 | hxz2
          · rw [← hTx]
            exact ((IH z hzy hzH (hzy.trans hyE)).1 x hxH hxz2).trans_le le_add_self
          · exfalso
            -- `z = x = φ(b, ·)` is fixed by `φ(a, ·)` (`a < b`), so `y = φ(a, Ω₂ + z) = z`
            have hΩz : Om (1 + 1) + z = z := by
              rw [← hxz2, hxe]; exact txOm2_add hb0 (hxe ▸ hΩx)
            have hfix : veblen a z = z := by
              rw [← hxz2, hxe]; exact veblen_veblen_of_lt hab _
            have : y = z := by rw [hye, hΩz, hfix]
            exact absurd (this ▸ hzy) (lt_irrefl _)
  exact ⟨hM, bnd hM⟩

/-- **`Θ̂_L x < Θ̂_L y`** for `x < y` in `H_λ ∩ G`. -/
theorem txLt {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l)
    (hyE : y < veblen (Om (1 + 1)) 1) (hxy : x < y) : tdThL S l x < tdThL S l y :=
  (txMono hl hX y hyH hyE).1 x hxH hxy

theorem txLe {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l)
    (hyE : y < veblen (Om (1 + 1)) 1) (hxy : x ≤ y) : tdThL S l x ≤ tdThL S l y := by
  rcases hxy.lt_or_eq with h | rfl
  · exact (txLt hl hX hxH hyH hyE h).le
  · exact le_rfl

/-- **`Θ̂_L(e + y) = Θ̂_L e + Θ̂_L y` when `W^{log_W y + 1} ∣ e`** (`e, y ∈ H_λ`, `e + y < G`). -/
theorem txAdd : ∀ e, e ∈ cdHull S l → ∀ y, y ∈ cdHull S l → e + y < veblen (Om (1 + 1)) 1 →
    leWe (sgLW y + 1) ∣ e → tdThL S l (e + y) = tdThL S l e + tdThL S l y := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH y hyH hlt hd
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, tjThL_zero, add_zero]
  rcases eq_or_ne e 0 with rfl | he0
  · rw [zero_add, tjThL_zero, zero_add]
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  have heE : e < veblen (Om (1 + 1)) 1 := le_self_add.trans_lt hlt
  obtain ⟨hs, hdr⟩ := tuDvd_parts he0' hd
  obtain ⟨-, -, -, -, hdW, hrH, hrg, hedec, hTe, -⟩ := txParts hl hX heH he0' heE
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
  have hrylt : r + y < veblen (Om (1 + 1)) 1 := (add_le_add_left hrx.le y).trans_lt hlt
  have hIH := IH r hrx hrH y hyH hrylt hdr
  have heyH : e + y ∈ cdHull S l := CSet.add_mem heH hyH
  have hey0 : 0 < e + y := he0'.trans_le le_self_add
  rw [txCnf hl hX heyH hey0 hlt, hsg, hdiv, hmod, hIH, hTe, add_assoc]

/-- `Θ̂_L(W^f·c) = Ω^{Θ̂_L f}·Θ c` for `1 ≤ c < Ω₂`, `W^f·c < G`. -/
theorem txTerm {f c : Ordinal.{0}} (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hH : leWe f * c ∈ cdHull S l)
    (hlt : leWe f * c < veblen (Om (1 + 1)) 1) :
    tdThL S l (leWe f * c) = leOe (tdThL S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have h0 : 0 < leWe f * c := mul_pos (leWe_pos f) (zero_lt_one.trans_le hc1)
  obtain ⟨e1, e2, e3⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [txCnf hl hX hH h0 hlt, e1, e2, e3, tjThL_zero, add_zero]

/-- `Θ̂_L(e + W^f·c) = Θ̂_L e + Ω^{Θ̂_L f}·Θ c` for `W^{f+1} ∣ e`. -/
theorem txAddT {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hcH : c ∈ cdHull S l) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe f * c < veblen (Om (1 + 1)) 1) :
    tdThL S l (e + leWe f * c) = tdThL S l e + leOe (tdThL S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have hyH : leWe f * c ∈ cdHull S l := leMulWe_mem hfH hcH
  obtain ⟨hs, -, -⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [txAdd hl hX e heH _ hyH hlt (by rw [hs]; exact hd),
    txTerm hl hX hc1 hcW hyH (le_add_self.trans_lt hlt)]

/-- **`Θ̂_L(e + W^f) = Θ̂_L e + Ω^{Θ̂_L f}` for `W^f ∣ e`** (`e, f ∈ H_λ`, `e + W^f < G`). -/
theorem txAddW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < veblen (Om (1 + 1)) 1) :
    tdThL S l (e + leWe f) = tdThL S l e + leOe (tdThL S l f) := by
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
  rw [he2, txAddT hl hX hmH hfH hd1H le_add_self hd1W hmd (he2 ▸ hlt), gxTh_add hρSC hAt hdc,
    sqTh_one hl hX, mul_add_one, ← add_assoc]
  congr 1
  rw [hes, hsdec]
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
  · exact (txAddT hl hX hmH hfH hdH (Order.one_le_iff_ne_zero.2 h0) hdW hmd
      ((le_self_add.trans_eq (by rw [hes, hsdec])).trans_lt hlt)).symm

/-- `Θ̂_L(e + 1) = Θ̂_L e + 1` (`e + 1 < G`). -/
theorem txSucc {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (hlt : e + 1 < veblen (Om (1 + 1)) 1) :
    tdThL S l (e + 1) = tdThL S l e + 1 := by
  have h := txAddW hl hX heH (CSet.zero_mem _ _) (by rw [leWe_zero]; exact one_dvd _) (by rwa [leWe_zero])
  rwa [leWe_zero, tjThL_zero, leOe_zero] at h

/-- **`W^f ∣ e` gives `Ω^{Θ̂_L f} ∣ Θ̂_L e`** (`e, f ∈ H_λ`, `e < G`). -/
theorem txDvd : ∀ e, e ∈ cdHull S l → e < veblen (Om (1 + 1)) 1 → ∀ f, f ∈ cdHull S l →
    leWe f ∣ e → leOe (tdThL S l f) ∣ tdThL S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH heE f hfH hd
  rcases eq_or_ne e 0 with rfl | he0
  · rw [tjThL_zero]; exact dvd_zero _
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  obtain ⟨hgH, hge, -, -, -, hrH, hrg, -, hTe, -⟩ := txParts hl hX heH he0' heE
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
  exact dvd_add ((tuOe_dvd (txLe hl hX hfH hgH (hge.trans_lt heE) hfg)).trans (dvd_mul_right _ _)) hIH

/-- `Θ̂_L(Ω₂) = Ω₁`. -/
theorem txOm2 : tdThL S l (Om (1 + 1)) = Om 1 := by
  have hW1 : leWe 1 = Om (1 + 1) := by unfold leWe; rw [mul_one]; exact gg_SC_eps ldOm2_SC
  have hO1 : leOe 1 = Om 1 := by unfold leOe; rw [mul_one]; exact gg_SC_eps Ph.ph_SC_Om1
  have h := txAddW hl hX (CSet.zero_mem _ _) (CSet.one_mem _ _) (dvd_zero _)
    (by rw [zero_add, hW1]; exact tgOm_lt_G)
  rwa [zero_add, hW1, tjThL_zero, zero_add, tuThL_code hl hX (gg_one_lt_of_SC ldOm2_SC), sqTh_one hl hX,
    hO1] at h

/-- **THE φ LAW AT EVERY NODE FORM, FIXED POINTS INCLUDED**: `Θ̂_L(φ(a, Ω₂ + z)) = φ(Θ a, Ω₁ + Θ̂_L z)` for a
level `1 ≤ a < Ω₂` of `H_λ` and every `z ∈ H_λ` with `φ(a, Ω₂ + z) < G`. -/
theorem txVeb {a z : Ordinal.{0}} (haH : a ∈ cdHull S l) (h1a : 1 ≤ a) (haW : a < Om (1 + 1))
    (hzH : z ∈ cdHull S l) (hG : veblen a (Om (1 + 1) + z) < veblen (Om (1 + 1)) 1) :
    tdThL S l (veblen a (Om (1 + 1) + z)) = veblen (gxTh (upsilon l) (ldAtR S l) a) (Om 1 + tdThL S l z) := by
  have hac : GxCl (upsilon l) (ldAtR S l) a := (ldHull_iff hl hX haW).1 haH
  have hΘa : gxTh (upsilon l) (ldAtR S l) a < Om 1 := snTh_lt_Om1 hl hX haW.le
  have ha0 : a ≠ 0 := (zero_lt_one.trans_le h1a).ne'
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [add_zero, ldOm2_SC.veblen_right haW, tjThL_zero, add_zero, Ph.ph_SC_Om1.veblen_right hΘa]
    exact txOm2 hl hX
  have hz1 : 1 ≤ z := Order.one_le_iff_ne_zero.2 hz0
  rcases (right_le_veblen a (Om (1 + 1) + z)).lt_or_eq with hlt | heq
  · exact (txNodeTh hl hX h1a haW hz1 hzH hlt hG).1
  -- the fixed point `x = Ω₂ + z = φ(a, x)`
  set x := veblen a (Om (1 + 1) + z) with hx_def
  have hxH : x ∈ cdHull S l := by
    rw [hx_def]; exact CSet.phi_mem haH (CSet.add_mem (mxOm2_mem _ _) hzH)
  have hx0 : 0 < x := veblen_pos
  obtain ⟨hWx, hgx⟩ := txNode_W ha0 hz1
  have hxs : ¬ sgLW x < x := by rw [hx_def, hgx]; exact lt_irrefl _
  obtain ⟨b, w, hxe, h1b, hbW, hw1, hxlt, hbH, hwH, hbc⟩ := txNode hl hX hxH hx0 hG hxs
  have hΩx : Om (1 + 1) < x := by
    rw [← heq]; exact lt_add_of_pos_right _ (zero_lt_one.trans_le hz1)
  have hzx : z = x := by
    have hp : IsPrincipal (· + ·) x := by rw [hx_def]; exact Ph.ph_veblen_prin _ _
    have hzle : z ≤ x := le_add_self.trans heq.le
    rcases hzle.lt_or_eq with h | h
    · have h2 : Om (1 + 1) + z < x := hp hΩx h
      rw [heq] at h2; exact absurd h2 (lt_irrefl _)
    · exact h
  -- the level `b` of the normal form is above `a`
  have hab : a < b := by
    rcases lt_trichotomy a b with h | rfl | h
    · exact h
    · exfalso
      have : Om (1 + 1) + w = Om (1 + 1) + z := by
        have h2 : veblen a (Om (1 + 1) + w) = veblen a (Om (1 + 1) + z) := by rw [← hxe]
        exact veblen_injective a h2
      rw [this, heq] at hxlt; exact lt_irrefl _ hxlt
    · exfalso
      have hfix : veblen b x = x := by
        conv_lhs => rw [hx_def]
        exact veblen_veblen_of_lt h _
      have h2 : veblen b (Om (1 + 1) + w) = veblen b x := by rw [hfix, ← hxe]
      have := veblen_injective b h2
      rw [this] at hxlt; exact lt_irrefl _ hxlt
  have hT := txNodeTh hl hX h1b hbW hw1 hwH (hxe ▸ hxlt) (hxe ▸ hG)
  rw [← hxe] at hT
  obtain ⟨hTx, -, hΩT⟩ := hT
  have hb1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) b := by
    have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) h1b
    rwa [sqTh_one hl hX] at h
  have hb0 : gxTh (upsilon l) (ldAtR S l) b ≠ 0 := (zero_lt_one.trans_le hb1).ne'
  rw [hzx, hTx, txOm1_add hb0 (hTx ▸ hΩT)]
  exact (veblen_veblen_of_lt (gxTh_lt hac hab) _).symm

/-- **`Θ̂_L x < Ĝ = φ(Ω₁, 1)`** for `x ∈ H_λ`, `x < G`. -/
theorem txLtGh : ∀ x, x ∈ cdHull S l → x < veblen (Om (1 + 1)) 1 →
    tdThL S l x < veblen (Om (1 : Ordinal.{0})) 1 := by
  have hfix : ω ^ veblen (Om (1 : Ordinal.{0})) 1 = veblen (Om 1) 1 := gg_veblen_eps (Om_pos one_ne_zero).ne'
  have hp : IsPrincipal (· + ·) (veblen (Om (1 : Ordinal.{0})) 1) := Ph.ph_veblen_prin _ _
  have hO : Om (1 : Ordinal.{0}) < veblen (Om 1) 1 := (lt_add_one _).trans tnOm1_lt_Gh
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxE
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [tjThL_zero]; exact veblen_pos
  have h0 := pos_iff_ne_zero.2 hx0
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hT, -⟩ := txParts hl hX hxH h0 hxE
    have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le h0)
    have hTg := IH _ hs hgH (hs.trans hxE)
    have hTr := IH _ hrx hrH (hrx.trans hxE)
    have hOe : leOe (tdThL S l (sgLW x)) < veblen (Om (1 : Ordinal.{0})) 1 := (tuOe_Gh hTg).1
    have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) < veblen (Om (1 : Ordinal.{0})) 1 :=
      (snTh_lt_Om1 hl hX hdW.le).trans hO
    rw [hT]
    exact hp (tuMul_lt_fix hfix hOe hΘd) hTr
  · obtain ⟨a, z, hxe, h1a, haW, hz1, hlt, -, hzH, -⟩ := txNode hl hX hxH h0 hxE hs
    have hzx : z < x := le_add_self.trans_lt hlt
    have hTz := IH z hzx hzH (hzx.trans hxE)
    rw [hxe, (txNodeTh hl hX h1a haW hz1 hzH (hxe ▸ hlt) (hxe ▸ hxE)).1]
    refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨snTh_lt_Om1 hl hX haW.le, ?_⟩))
    exact hp hO hTz

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tx
