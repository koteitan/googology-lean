import Googology.Trans.PoR.InaccPsi.R2.UgPart

/-!
# The image past `Γ₂` is strictly increasing on `H_λ ∩ Y₃`, and its values at the arguments are normal

`T = Ug.ugTh S λ`, `Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`,
`Γ₂ = Ua.uaGam = ψ₃(0)`, `ψ₂ = ψ_{Ω₂}`, `ψ₃ = ψ_{Ω₃}`, `Y₃ = ψ₃(Ω₃)`.

* `ugCl` (**THE CLOSURE LEMMA**: if `T` is increasing below `y`, every `x ∈ H_λ`, `x < y`, has
  `T x ∈ Cl(a, ψ₂(a))` for every `a ≥ T x`);
* `ugNorm` (**THE IMAGE OF A NORMAL ARGUMENT IS NORMAL**: `T d ∈ Cl(T d, ψ₂(T d))` and `T d < ψ₂(T d)`, so
  `ψ₂(T d)` is in normal form);
* `ugMono` (**`T` IS STRICTLY INCREASING ON `H_λ ∩ Y₃`, and `x < W^y` gives `T x < Ω^{T y}`**; the new cases: two
  `ψ₃`-atoms `ψ₃(d') < ψ₃(d)` give `ψ₂(T d') < ψ₂(T d)` by `ugNorm`, an atom below a node, a node or a sum below an
  atom), `ugLt`, `ugLe`, `ugNormAll` (`ugNorm` with no hypothesis).

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

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE CLOSURE LEMMA**: if `T` is increasing below `y`, then `T x ∈ Cl(a, ψ₂(a))` for `x ∈ H_λ`, `x < y`,
`x < Y₃` and every `a ≥ T x`. -/
theorem ugCl {y : Ordinal.{0}}
    (hM : ∀ z, z ∈ cdHull S l → z < y → ∀ x, x ∈ cdHull S l → x < z → ugTh S l x < ugTh S l z) :
    ∀ x, x ∈ cdHull S l → x < y → x < ugY S → ∀ a, ugTh S l x ≤ a →
      ugTh S l x ∈ S.CSet a (S.psi a (Om (1 + 1))) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxy hxY a ha
  have hΩa : Om 1 < S.psi a (Om (1 + 1)) := (psiS_bounds (S := S) a 1).1
  rcases lt_or_ge x uaGam with hxE | hGx
  · rw [ugTh_lt hxE]
    exact CSet.of_lt ((uaLtG1 hl hX x hxH hxE).trans_le (psi_mono (InR_Om_succ 1) zero_le).1)
  have h0 : 0 < x := ugGam_pos.trans_le hGx
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, hd1, hdW, hrH, hrg, -⟩ := uaBase hl hX hxH h0
    have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le h0)
    have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) := by
      have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
      rwa [sqTh_one hl hX] at h
    rw [ugTh_cnf hGx hs] at ha ⊢
    have hTg : ugTh S l (sgLW x) ≤ a := by
      refine le_trans ?_ ha
      calc ugTh S l (sgLW x) ≤ leOe (ugTh S l (sgLW x)) := ugLeOe _
        _ ≤ leOe (ugTh S l (sgLW x)) * gxTh (upsilon l) (ldAtR S l) (x / leWe (sgLW x)) :=
            (mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)
        _ ≤ _ := le_self_add
    have hTr : ugTh S l (x % leWe (sgLW x)) ≤ a := le_add_self.trans ha
    have hg := IH _ hs hgH (hs.trans hxy) (hs.trans hxY) a hTg
    have hr := IH _ hrx hrH (hrx.trans hxy) (hrx.trans hxY) a hTr
    exact CSet.add_mem (leMulOe_mem hg (CSet.of_lt ((snTh_lt_Om1 hl hX hdW.le).trans hΩa))) hr
  by_cases hS : SC x
  · obtain ⟨d, hdH, hd, -, hxd⟩ := ugAtomH hl hX hxH hS (uaGam_spec.2.trans_le hGx) hxY
    have hdx : d < x := hxd ▸ hd
    have hTd := hM x hxH hxy d hdH hdx
    rw [← hxd, ugTh_atom hd] at hTd ha ⊢
    have hlt : ugTh S l d < a := hTd.trans_le ha
    exact CSet.psi_mem hlt (InR_Om_succ 1) (mxOm2_mem _ _)
      (IH d hdx hdH (hdx.trans hxy) (hdx.trans hxY) a hlt.le)
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := ugNode hGx hS hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    rw [ugTh_node hGx hs hS ⟨haE, hbE⟩] at ha ⊢
    exact CSet.phi_mem (IH _ haE hmem.1 (haE.trans hxy) (haE.trans hxY) a ((left_le_veblen _ _).trans ha))
      (IH _ hbE hmem.2 (hbE.trans hxy) (hbE.trans hxY) a ((right_le_veblen _ _).trans ha))

/-- **THE IMAGE OF A NORMAL ARGUMENT IS NORMAL**: `T d ∈ Cl(T d, ψ₂(T d))` and `T d < ψ₂(T d)`. -/
theorem ugNorm {y : Ordinal.{0}}
    (hM : ∀ z, z ∈ cdHull S l → z < y → ∀ x, x ∈ cdHull S l → x < z → ugTh S l x < ugTh S l z)
    {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hdy : d < y) (hdY : d < ugY S) :
    ugTh S l d ∈ S.CSet (ugTh S l d) (S.psi (ugTh S l d) (Om (1 + 1))) ∧
      ugTh S l d < S.psi (ugTh S l d) (Om (1 + 1)) := by
  have h := ugCl hl hX hM d hdH hdy hdY _ le_rfl
  exact ⟨h, lt_psi_of_mem (InR_Om_succ 1) h (ugLtOm2 hl hX d hdH hdY)⟩

/-- **`T` IS STRICTLY INCREASING ON `H_λ ∩ Y₃`, and `x < W^y` gives `T x < Ω^{T y}`.** -/
theorem ugMono : ∀ y, y ∈ cdHull S l → y < ugY S →
    (∀ x, x ∈ cdHull S l → x < y → ugTh S l x < ugTh S l y) ∧
    (∀ x, x ∈ cdHull S l → x < ugY S → x < leWe y → ugTh S l x < leOe (ugTh S l y)) := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyH hyY
  have bnd : (∀ x, x ∈ cdHull S l → x < y → ugTh S l x < ugTh S l y) →
      ∀ x, x ∈ cdHull S l → x < ugY S → x < leWe y → ugTh S l x < leOe (ugTh S l y) := by
    intro hM x hxH hxY hxy
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [ugTh_zero]; exact leOe_pos _
    have h0 := pos_iff_ne_zero.2 hx0
    obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hT, -⟩ := ugParts hl hX hxH h0 hxY
    set g := sgLW x with hg
    have hgy : g < y := tuLogW_lt hx0 hxy
    have hrx : x % leWe g < ugY S := ((hrg.trans_le (sgLW_le h0))).trans hxY
    have hrb : ugTh S l (x % leWe g) < leOe (ugTh S l g) := (IH g hgy hgH (hgy.trans hyY)).2 _ hrH hrx hrg
    have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
    rw [hT]
    calc leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + ugTh S l (x % leWe g)
        < leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (ugTh S l g) :=
          (add_lt_add_iff_left _).2 hrb
      _ = leOe (ugTh S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
      _ ≤ leOe (ugTh S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
      _ = leOe (ugTh S l g + 1) := (leOe_succ _).symm
      _ ≤ leOe (ugTh S l y) := leOe_mono (Order.add_one_le_of_lt (hM g hgH hgy))
  have hMono : ∀ z, z ∈ cdHull S l → z < y → ∀ x, x ∈ cdHull S l → x < z → ugTh S l x < ugTh S l z :=
    fun z hzH hzy => (IH z hzy hzH (hzy.trans hyY)).1
  have hM : ∀ x, x ∈ cdHull S l → x < y → ugTh S l x < ugTh S l y := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x IHx =>
    intro hxH hxy
    have hy0 : 0 < y := lt_of_le_of_lt zero_le hxy
    have hxY : x < ugY S := hxy.trans hyY
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [ugTh_zero]; exact ugPos hl hX hyH hy0 hyY
    have hx0' := pos_iff_ne_zero.2 hx0
    -- below `Γ₂`: the old image
    rcases lt_or_ge y uaGam with hyG | hyG
    · rw [ugTh_lt hyG, ugTh_lt (hxy.trans hyG)]; exact uaLt hl hX hxH hyH hyG hxy
    rcases lt_or_ge x uaGam with hxG | hxG
    · rw [ugTh_lt hxG]; exact (uaLtG1 hl hX x hxH hxG).trans_le (ugGe2 hl hX y hyH hyG hyY)
    by_cases hys : sgLW y < y
    · -- `y` off the `W`-fixed points
      obtain ⟨hgH, -, hdc, hd1, hdW, hrH, hrg, hydec, hTy, -⟩ := ugParts hl hX hyH hy0 hyY
      set g := sgLW y with hg
      have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (y / leWe g) := by
        have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
        rwa [sqTh_one hl hX] at h
      have hTy' : leOe (ugTh S l g) ≤ ugTh S l y := by
        rw [hTy]
        exact ((mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)).trans le_self_add
      rcases lt_or_ge x (leWe g) with hxg | hxg
      · exact ((IH g hys hgH (hys.trans hyY)).2 x hxH hxY hxg).trans_le hTy'
      have hsx : sgLW x = g := by
        obtain ⟨a1, a2⟩ := sjLogW hxg (hxy.trans (sgLW_lt y))
        exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
      obtain ⟨-, -, hdxc, -, hdxW, hrxH, hrxg, hxdec, hTx, -⟩ := ugParts hl hX hxH hx0' hxY
      rw [hsx] at hdxc hdxW hrxH hrxg hxdec hTx
      have hdd : x / leWe g ≤ y / leWe g :=
        (Ordinal.le_div (leWe_pos g).ne').2 ((Ordinal.mul_div_le x _).trans hxy.le)
      rw [hTx, hTy]
      have hb := (IH g hys hgH (hys.trans hyY)).2 _ hrxH ((hrxg.trans_le hxg).trans hxY) hrxg
      rcases hdd.lt_or_eq with hlt | heq
      · have hΘlt := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hdxc hlt
        calc leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + ugTh S l (x % leWe g)
            < leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (ugTh S l g) :=
              (add_lt_add_iff_left _).2 hb
          _ = leOe (ugTh S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
          _ ≤ leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (y / leWe g) :=
              mul_le_mul_left' (Order.add_one_le_of_lt hΘlt) _
          _ ≤ _ := le_self_add
      · rw [heq]
        refine (add_lt_add_iff_left _).2 ?_
        have hrr : x % leWe g < y % leWe g := by
          have h := hxy
          rw [hxdec, hydec, heq] at h
          exact (add_lt_add_iff_left _).1 h
        have hry : y % leWe g < y := hrg.trans_le (sgLW_le hy0)
        exact (IH _ hry hrH (hry.trans hyY)).1 _ hrxH hrr
    by_cases hyS : SC y
    · -- `y` a `ψ₃`-atom
      obtain ⟨d, hdH, hd, -, hyd⟩ := ugAtomH hl hX hyH hyS (uaGam_spec.2.trans_le hyG) hyY
      have hdy : d < y := hyd ▸ hd
      have hTy : ugTh S l y = S.psi (ugTh S l d) (Om (1 + 1)) := by rw [← hyd]; exact ugTh_atom hd
      have hTyS : SC (ugTh S l y) := by rw [hTy]; exact SC_psi (InR_Om_succ 1) _
      have hΩy : Om 1 < ugTh S l y := by rw [hTy]; exact (psiS_bounds (S := S) _ 1).1
      by_cases hxs : sgLW x < x
      · obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hT, -⟩ := ugParts hl hX hxH hx0' hxY
        have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le hx0')
        have hTg := IHx _ hxs hgH (hxs.trans hxy)
        have hTr := IHx _ hrx hrH (hrx.trans hxy)
        rw [hT]
        exact hTyS.isPrincipal (ldMul_lt_SC hTyS (leOe_lt_SC hTyS hΩy hTg).1
          ((snTh_lt_Om1 hl hX hdW.le).trans hΩy)) hTr
      by_cases hxS : SC x
      · obtain ⟨d', hd'H, hd', -, hxd⟩ := ugAtomH hl hX hxH hxS (uaGam_spec.2.trans_le hxG) hxY
        have hdd : d' < d := by
          by_contra hc
          have := (psi_mono (S := S) ugInR3 (not_lt.1 hc)).1
          rw [hyd, hxd] at this
          exact absurd hxy (not_lt.2 this)
        have hTdd := (IH d hdy hdH (hdy.trans hyY)).1 d' hd'H hdd
        have hd'y : d' < y := hdd.trans hdy
        have hnf := (ugNorm hl hX hMono hd'H hd'y (hd'y.trans hyY)).1
        rw [hTy, ← hxd, ugTh_atom hd']
        exact psi_lt_psi (InR_Om_succ 1) hTdd hnf
      · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := ugNode hxG hxS hxs
        have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
        rw [ugTh_node hxG hxs hxS ⟨haE, hbE⟩]
        exact hTyS.2 _ (IHx _ haE hmem.1 (haE.trans hxy)) _ (IHx _ hbE hmem.2 (hbE.trans hxy))
    -- `y` a node
    obtain ⟨hTyv, hyO⟩ := ugNodeTh hl hX hyH hyG hyY hyS hys
    obtain ⟨-, hyv, -, hayE, hbyE, -, -⟩ := ugNode hyG hyS hys
    have hmy := mem_of_veblen_mem (by rw [hyv]; exact hyH) (by rw [hyv]; exact hayE) (by rw [hyv]; exact hbyE)
    by_cases hxs : sgLW x < x
    · -- `x` off the `W`-fixed points: `T x < Ω^{T g + 1} ≤ Ω^{T y}`
      obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hTx, -⟩ := ugParts hl hX hxH hx0' hxY
      set g := sgLW x with hg
      have hgy : g < y := hxs.trans hxy
      have hTg : ugTh S l g < ugTh S l y := IHx g hxs hgH hgy
      have hrb : ugTh S l (x % leWe g) < leOe (ugTh S l g) :=
        (IH g hgy hgH (hgy.trans hyY)).2 _ hrH ((hrg.trans_le (sgLW_le hx0')).trans hxY) hrg
      have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
      rw [hTx, ← hyO]
      calc leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + ugTh S l (x % leWe g)
          < leOe (ugTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (ugTh S l g) :=
            (add_lt_add_iff_left _).2 hrb
        _ = leOe (ugTh S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
        _ ≤ leOe (ugTh S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
        _ = leOe (ugTh S l g + 1) := (leOe_succ _).symm
        _ ≤ leOe (ugTh S l y) := leOe_mono (Order.add_one_le_of_lt hTg)
    set a := invVeblen₁ y with ha_def
    set z := invVeblen₂ y with hz_def
    by_cases hxS : SC x
    · -- a `ψ₃`-atom `x` below the node `y = φ(a, z)`
      rw [hTyv]
      rcases lt_or_ge x a with hxa | hax
      · exact ((IH a hayE hmy.1 (hayE.trans hyY)).1 x hxH hxa).trans_le (left_le_veblen _ _)
      rcases hax.eq_or_lt with hax | hax
      · -- `a = x`: the argument `z` is not `0`
        have hz0 : z ≠ 0 := by
          intro h0
          have h' := hyv
          rw [hax, h0, hxS.veblen_zero] at h'
          exact absurd h' hxy.ne
        have hTz := ugPos hl hX hmy.2 (pos_iff_ne_zero.2 hz0) (hbyE.trans hyY)
        rw [hax]
        exact (left_le_veblen _ _).trans_lt (veblen_lt_veblen_iff_right.2 hTz)
      · -- `a < x`: then `x < z`
        have hxz : x < z := by
          rcases lt_or_ge z x with hzx | hxz
          · exfalso
            have := hxS.2 _ hax _ hzx
            rw [hyv] at this
            exact absurd hxy (not_lt.2 this.le)
          rcases hxz.eq_or_lt with h | h
          · exfalso
            have hfix : veblen a x = x := by
              conv_lhs => rw [← hxS.veblen_zero]
              rw [veblen_veblen_of_lt hax 0, hxS.veblen_zero]
            have h' := hyv
            rw [← h, hfix] at h'
            exact absurd h' hxy.ne
          · exact h
        exact ((IH z hbyE hmy.2 (hbyE.trans hyY)).1 x hxH hxz).trans_le (right_le_veblen _ _)
    · -- both nodes: the Veblen comparison
      obtain ⟨-, hxv, -, haxE, hbxE, -, -⟩ := ugNode hxG hxS hxs
      have hTxv := (ugNodeTh hl hX hxH hxG hxY hxS hxs).1
      set b := invVeblen₁ x with hb_def
      set w := invVeblen₂ x with hw_def
      have hmx := mem_of_veblen_mem (by rw [hxv]; exact hxH) (by rw [hxv]; exact haxE) (by rw [hxv]; exact hbxE)
      have hcmp : veblen b w < veblen a z := by rw [hxv, hyv]; exact hxy
      rw [hTxv, hTyv]
      rcases veblen_lt_veblen_iff.1 hcmp with ⟨hba, hlt⟩ | ⟨hba, hlt⟩ | ⟨hab, hlt⟩
      · rw [hba]
        exact veblen_lt_veblen_iff_right.2 ((IH z hbyE hmy.2 (hbyE.trans hyY)).1 w hmx.2 hlt)
      · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨(IH a hayE hmy.1 (hayE.trans hyY)).1 b hmx.1 hba, ?_⟩))
        rw [← hTyv]
        exact IHx w hbxE hmx.2 (hbxE.trans hxy)
      · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inr ⟨(IH b (haxE.trans hxy) hmx.1
          ((haxE.trans hxy).trans hyY)).1 a hmy.1 hab, ?_⟩))
        rw [← hTxv]
        rw [hxv] at hlt
        exact (IH z hbyE hmy.2 (hbyE.trans hyY)).1 x hxH hlt
  exact ⟨hM, bnd hM⟩

theorem ugLt {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l) (hyY : y < ugY S) (hxy : x < y) :
    ugTh S l x < ugTh S l y :=
  (ugMono hl hX y hyH hyY).1 x hxH hxy

theorem ugLe {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l) (hyY : y < ugY S) (hxy : x ≤ y) :
    ugTh S l x ≤ ugTh S l y := by
  rcases hxy.lt_or_eq with h | rfl
  · exact (ugLt hl hX hxH hyH hyY h).le
  · exact le_rfl

/-- **The image of every `d ∈ H_λ ∩ Y₃` is normal for `ψ₂`.** -/
theorem ugNormAll {d : Ordinal.{0}} (hdH : d ∈ cdHull S l) (hdY : d < ugY S) :
    ugTh S l d ∈ S.CSet (ugTh S l d) (S.psi (ugTh S l d) (Om (1 + 1))) ∧
      ugTh S l d < S.psi (ugTh S l d) (Om (1 + 1)) :=
  ugNorm hl hX (y := ugY S) (fun z hzH hzY x hxH hxz => ugLt hl hX hxH hzH hzY hxz) hdH hdY hdY

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ug
