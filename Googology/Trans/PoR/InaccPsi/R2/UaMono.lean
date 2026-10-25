import Googology.Trans.PoR.InaccPsi.R2.UaTh

/-!
# The laws of the image `T = Ua.uaTh` on `H_λ ∩ Γ₂`: monotone, φ law, sums, bound, own property

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`,
`Ĝ = φ(Ω₁, 1)`, `Γ₂ = Ua.uaGam`, codes `LeCl κ Q`.

* `uaMono` (**`T` is strictly increasing on `H_λ ∩ Γ₂`, and `x < W^y` gives `T x < Ω^{T y}`**), `uaLt`, `uaLe`;
* `uaVeb` (**THE φ LAW AT EVERY LEVEL, FIXED POINTS INCLUDED**: `T(φ(a, y)) = φ(T a, T y)` for `a ≠ 0`, `a, y ∈ H_λ`,
  `G ≤ φ(a, y) < Γ₂`; the level `a` may be `≥ Ω₂`), `uaG` (`T G = Ĝ`);
* `uaAdd`, `uaTerm`, `uaAddT`, `uaAddW`, `uaSucc`, `uaDvd` (the sum laws), `uaLtG1` (`T x < ψ_{Ω₂}(0)`);
* `uaCl_arg` (**THE ARGUMENT OF A CODE IS A CODE, AT EVERY LEVEL**: `φ(a, y)` a code with `y < φ(a, y)` gives `y`
  a code; `Ta.taCl_inv` asked `a < κ`), `uaOwn` (**the own property**: an exponent `E < Γ₂` of `H_λ` that is a code
  over every `Q ≥ T` has `T E ∈ Cl(0, Θ T)` and `T E` a level-1 code over every `Q ≥ Θ T`; `Tj.tjThL_own` for `T`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ua

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx

variable {S : InaccSeq.{0}}

/-- **THE ARGUMENT OF A CODE IS A CODE, AT EVERY LEVEL.** -/
theorem uaCl_arg {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) :
    ∀ w, LeCl κ Q w → ∀ a y, w = veblen a y → y < w → LeCl κ Q y := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro a y he hy
    exact LeCl.small (hy.trans hwQ)
  | om =>
    intro a y he hy
    rcases lt_or_ge a κ with haκ | hκa
    · have : veblen a y < κ := hκ.2 a haκ y hy
      rw [← he] at this; exact absurd this (lt_irrefl _)
    · have hle : a ≤ κ := by rw [he]; exact left_le_veblen a y
      have ha : a = κ := le_antisymm hle hκa
      rw [ha] at he
      have hy0 : y = 0 := by
        have h2 : veblen κ y = veblen κ 0 := by rw [← he, hκ.veblen_zero]
        exact veblen_injective κ h2
      rw [hy0]; exact LeCl.zero hQ.1
  | @add x z _ _ ihx ihz =>
    intro a y he hy
    by_cases hz : z = x + z
    · exact ihz a y (hz.trans he) (hz ▸ hy)
    · by_cases hx : x = x + z
      · exact ihx a y (hx.trans he) (hx ▸ hy)
      · have hzl : z < x + z := lt_of_le_of_ne le_add_self hz
        have hxl : x < x + z := lt_of_le_of_ne le_self_add hx
        rw [he] at hzl hxl
        have := Ph.ph_veblen_prin a y hxl hzl
        rw [← he] at this; exact absurd this (lt_irrefl _)
  | @phi p q _ hq _ ihq =>
    intro a y he hy
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hfix : veblen p (veblen a y) = veblen a y := veblen_veblen_of_lt hpa y
      have hq' : q = veblen a y := by
        have h2 : veblen p q = veblen p (veblen a y) := by rw [hfix]; exact he
        exact veblen_injective p h2
      exact ihq a y hq' (by rw [hq']; rw [← he]; exact hy)
    · have : q = y := veblen_injective p he
      rw [← this]; exact hq
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      rw [he] at hfix
      have hyy : veblen a y = y := veblen_injective a hfix
      rw [he, hyy] at hy; exact absurd hy (lt_irrefl _)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T` is strictly increasing on `H_λ ∩ Γ₂`, and `x < W^y` gives `T x < Ω^{T y}`.** -/
theorem uaMono : ∀ y, y ∈ cdHull S l → y < uaGam →
    (∀ x, x ∈ cdHull S l → x < y → uaTh S l x < uaTh S l y) ∧
    (∀ x, x ∈ cdHull S l → x < uaGam → x < leWe y → uaTh S l x < leOe (uaTh S l y)) := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyH hyE
  have bnd : (∀ x, x ∈ cdHull S l → x < y → uaTh S l x < uaTh S l y) →
      ∀ x, x ∈ cdHull S l → x < uaGam → x < leWe y → uaTh S l x < leOe (uaTh S l y) := by
    intro hM x hxH hxE hxy
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [uaTh_zero]; exact leOe_pos _
    have h0 := pos_iff_ne_zero.2 hx0
    obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hT, -⟩ := uaParts hl hX hxH h0 hxE
    set g := sgLW x with hg
    have hgy : g < y := tuLogW_lt hx0 hxy
    have hrx : x % leWe g < uaGam := ((hrg.trans_le (sgLW_le h0))).trans hxE
    have hrb : uaTh S l (x % leWe g) < leOe (uaTh S l g) := (IH g hgy hgH (hgy.trans hyE)).2 _ hrH hrx hrg
    have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
    rw [hT]
    calc leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + uaTh S l (x % leWe g)
        < leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (uaTh S l g) :=
          (add_lt_add_iff_left _).2 hrb
      _ = leOe (uaTh S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
      _ ≤ leOe (uaTh S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
      _ = leOe (uaTh S l g + 1) := (leOe_succ _).symm
      _ ≤ leOe (uaTh S l y) := leOe_mono (Order.add_one_le_of_lt (hM g hgH hgy))
  have hM : ∀ x, x ∈ cdHull S l → x < y → uaTh S l x < uaTh S l y := by
    intro x
    induction x using WellFoundedLT.induction with
    | ind x IHx =>
    intro hxH hxy
    have hy0 : 0 < y := lt_of_le_of_lt zero_le hxy
    have hxE : x < uaGam := hxy.trans hyE
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [uaTh_zero]; exact uaPos hl hX hyH hy0 hyE
    have hx0' := pos_iff_ne_zero.2 hx0
    -- below `G`: the old image
    rcases lt_or_ge y (veblen (Om (1 + 1)) 1) with hyG | hyG
    · rw [uaTh_lt hyG, uaTh_lt (hxy.trans hyG)]; exact txLt hl hX hxH hyH hyG hxy
    rcases lt_or_ge x (veblen (Om (1 + 1)) 1) with hxG | hxG
    · rw [uaTh_lt hxG]; exact (txLtGh hl hX x hxH hxG).trans_le (uaGe hl hX y hyH hyG hyE)
    by_cases hys : sgLW y < y
    · -- `y` off the nodes
      obtain ⟨hgH, -, hdc, hd1, hdW, hrH, hrg, hydec, hTy, -⟩ := uaParts hl hX hyH hy0 hyE
      set g := sgLW y with hg
      have hΘd1 : 1 ≤ gxTh (upsilon l) (ldAtR S l) (y / leWe g) := by
        have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
        rwa [sqTh_one hl hX] at h
      have hTy' : leOe (uaTh S l g) ≤ uaTh S l y := by
        rw [hTy]
        exact ((mul_one _).symm.le.trans (mul_le_mul_left' hΘd1 _)).trans le_self_add
      rcases lt_or_ge x (leWe g) with hxg | hxg
      · exact ((IH g hys hgH (hys.trans hyE)).2 x hxH hxE hxg).trans_le hTy'
      have hsx : sgLW x = g := by
        obtain ⟨a1, a2⟩ := sjLogW hxg (hxy.trans (sgLW_lt y))
        exact le_antisymm (Order.lt_add_one_iff.1 a2) a1
      obtain ⟨-, -, hdxc, -, hdxW, hrxH, hrxg, hxdec, hTx, -⟩ := uaParts hl hX hxH hx0' hxE
      rw [hsx] at hdxc hdxW hrxH hrxg hxdec hTx
      have hdd : x / leWe g ≤ y / leWe g :=
        (Ordinal.le_div (leWe_pos g).ne').2 ((Ordinal.mul_div_le x _).trans hxy.le)
      rw [hTx, hTy]
      have hb := (IH g hys hgH (hys.trans hyE)).2 _ hrxH ((hrxg.trans_le hxg).trans hxE) hrxg
      rcases hdd.lt_or_eq with hlt | heq
      · have hΘlt := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hdxc hlt
        calc leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + uaTh S l (x % leWe g)
            < leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (uaTh S l g) :=
              (add_lt_add_iff_left _).2 hb
          _ = leOe (uaTh S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
          _ ≤ leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (y / leWe g) :=
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
    · -- `y` a node `≥ G`
      obtain ⟨hTyv, -, hyO⟩ := uaNodeTh hl hX hyH hyG hyE hys
      by_cases hxs : sgLW x < x
      · -- `x` off the nodes: `T x < Ω^{T g + 1} ≤ Ω^{T y}`
        obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hTx, -⟩ := uaParts hl hX hxH hx0' hxE
        set g := sgLW x with hg
        have hgy : g < y := hxs.trans hxy
        have hTg : uaTh S l g < uaTh S l y := IHx g hxs hgH hgy
        have hrb : uaTh S l (x % leWe g) < leOe (uaTh S l g) :=
          (IH g hgy hgH (hgy.trans hyE)).2 _ hrH ((hrg.trans_le (sgLW_le hx0')).trans hxE) hrg
        have hΘd : gxTh (upsilon l) (ldAtR S l) (x / leWe g) < Om 1 := snTh_lt_Om1 hl hX hdW.le
        rw [hTx, ← hyO]
        calc leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + uaTh S l (x % leWe g)
            < leOe (uaTh S l g) * gxTh (upsilon l) (ldAtR S l) (x / leWe g) + leOe (uaTh S l g) :=
              (add_lt_add_iff_left _).2 hrb
          _ = leOe (uaTh S l g) * (gxTh (upsilon l) (ldAtR S l) (x / leWe g) + 1) := (mul_add_one _ _).symm
          _ ≤ leOe (uaTh S l g) * Om 1 := mul_le_mul_left' (Order.add_one_le_of_lt hΘd) _
          _ = leOe (uaTh S l g + 1) := (leOe_succ _).symm
          _ ≤ leOe (uaTh S l y) := leOe_mono (Order.add_one_le_of_lt hTg)
      · -- both nodes: the Veblen comparison
        obtain ⟨-, hyv, -, hayE, hbyE, -, -⟩ := uaNode hyG hyE hys
        obtain ⟨-, hxv, -, haxE, hbxE, -, -⟩ := uaNode hxG hxE hxs
        have hTxv := (uaNodeTh hl hX hxH hxG hxE hxs).1
        set a := invVeblen₁ y with ha_def
        set z := invVeblen₂ y with hz_def
        set b := invVeblen₁ x with hb_def
        set w := invVeblen₂ x with hw_def
        have hmy := mem_of_veblen_mem (by rw [hyv]; exact hyH) (by rw [hyv]; exact hayE) (by rw [hyv]; exact hbyE)
        have hmx := mem_of_veblen_mem (by rw [hxv]; exact hxH) (by rw [hxv]; exact haxE) (by rw [hxv]; exact hbxE)
        have hcmp : veblen b w < veblen a z := by rw [hxv, hyv]; exact hxy
        rw [hTxv, hTyv]
        rcases veblen_lt_veblen_iff.1 hcmp with ⟨hba, hlt⟩ | ⟨hba, hlt⟩ | ⟨hab, hlt⟩
        · rw [hba]
          exact veblen_lt_veblen_iff_right.2 ((IH z hbyE hmy.2 (hbyE.trans hyE)).1 w hmx.2 hlt)
        · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨(IH a hayE hmy.1 (hayE.trans hyE)).1 b hmx.1 hba, ?_⟩))
          rw [← hTyv]
          exact IHx w hbxE hmx.2 (hbxE.trans hxy)
        · refine veblen_lt_veblen_iff.2 (Or.inr (Or.inr ⟨(IH b (haxE.trans hxy) hmx.1
            ((haxE.trans hxy).trans hyE)).1 a hmy.1 hab, ?_⟩))
          rw [← hTxv]
          rw [hxv] at hlt
          exact (IH z hbyE hmy.2 (hbyE.trans hyE)).1 x hxH hlt
  exact ⟨hM, bnd hM⟩

theorem uaLt {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l) (hyE : y < uaGam) (hxy : x < y) :
    uaTh S l x < uaTh S l y :=
  (uaMono hl hX y hyH hyE).1 x hxH hxy

theorem uaLe {x y : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hyH : y ∈ cdHull S l) (hyE : y < uaGam) (hxy : x ≤ y) :
    uaTh S l x ≤ uaTh S l y := by
  rcases hxy.lt_or_eq with h | rfl
  · exact (uaLt hl hX hxH hyH hyE h).le
  · exact le_rfl

/-- **THE φ LAW AT EVERY LEVEL, FIXED POINTS INCLUDED**: `T(φ(a, y)) = φ(T a, T y)` (`a ≠ 0`, `G ≤ φ(a, y) < Γ₂`). -/
theorem uaVeb {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hyH : y ∈ cdHull S l) (ha0 : a ≠ 0)
    (hG : veblen (Om (1 + 1)) 1 ≤ veblen a y) (hE : veblen a y < uaGam) :
    uaTh S l (veblen a y) = veblen (uaTh S l a) (uaTh S l y) := by
  set x := veblen a y with hx_def
  have hxH : x ∈ cdHull S l := CSet.phi_mem haH hyH
  have hε : ω ^ x = x := gg_veblen_eps ha0
  have hΩx : Om (1 + 1) < x := tgOm_lt_G.trans_le hG
  have hxs : ¬ sgLW x < x := by rw [(uaWfix hε hΩx).1]; exact lt_irrefl _
  obtain ⟨-, hv, -, haxE, hbxE, -, -⟩ := uaNode hG hE hxs
  have hT := (uaNodeTh hl hX hxH hG hE hxs).1
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
  have hTab : uaTh S l a < uaTh S l b := uaLt hl hX haH hmem.1 (haxE.trans hE) hab
  conv_rhs => rw [hyx, hT]
  rw [veblen_veblen_of_lt hTab, ← hT]

/-- `T G = Ĝ`. -/
theorem uaG : uaTh S l (veblen (Om (1 + 1)) 1) = veblen (Om 1) 1 := by
  have h := uaVeb hl hX (mxOm2_mem _ _) (CSet.one_mem _ _) ldOm2_SC.1.ne' le_rfl uaG_lt_Gam
  rw [h, uaTh_lt tgOm_lt_G, txOm2 hl hX, uaTh_lt ((gg_one_lt_of_SC ldOm2_SC).trans tgOm_lt_G),
    tuThL_code hl hX (gg_one_lt_of_SC ldOm2_SC), sqTh_one hl hX]

/-- **`T(e + y) = T e + T y` when `W^{log_W y + 1} ∣ e`** (`e, y ∈ H_λ`, `e + y < Γ₂`). -/
theorem uaAdd : ∀ e, e ∈ cdHull S l → ∀ y, y ∈ cdHull S l → e + y < uaGam →
    leWe (sgLW y + 1) ∣ e → uaTh S l (e + y) = uaTh S l e + uaTh S l y := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH y hyH hlt hd
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero, uaTh_zero, add_zero]
  rcases eq_or_ne e 0 with rfl | he0
  · rw [zero_add, uaTh_zero, zero_add]
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  have heE : e < uaGam := le_self_add.trans_lt hlt
  obtain ⟨hs, hdr⟩ := tuDvd_parts he0' hd
  obtain ⟨-, -, -, -, hdW, hrH, hrg, hedec, hTe, -⟩ := uaParts hl hX heH he0' heE
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
  have hrylt : r + y < uaGam := (add_le_add_left hrx.le y).trans_lt hlt
  have hIH := IH r hrx hrH y hyH hrylt hdr
  have heyH : e + y ∈ cdHull S l := CSet.add_mem heH hyH
  have hey0 : 0 < e + y := he0'.trans_le le_self_add
  rw [(uaParts hl hX heyH hey0 hlt).2.2.2.2.2.2.2.2.1, hsg, hdiv, hmod, hIH, hTe, add_assoc]

/-- `T(W^f·c) = Ω^{T f}·Θ c` for `1 ≤ c < Ω₂`, `W^f·c < Γ₂`. -/
theorem uaTerm {f c : Ordinal.{0}} (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hH : leWe f * c ∈ cdHull S l)
    (hlt : leWe f * c < uaGam) :
    uaTh S l (leWe f * c) = leOe (uaTh S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have h0 : 0 < leWe f * c := mul_pos (leWe_pos f) (zero_lt_one.trans_le hc1)
  obtain ⟨e1, e2, e3⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [(uaParts hl hX hH h0 hlt).2.2.2.2.2.2.2.2.1, e1, e2, e3, uaTh_zero, add_zero]

/-- `T(e + W^f·c) = T e + Ω^{T f}·Θ c` for `W^{f+1} ∣ e`. -/
theorem uaAddT {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hcH : c ∈ cdHull S l) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe f * c < uaGam) :
    uaTh S l (e + leWe f * c) = uaTh S l e + leOe (uaTh S l f) * gxTh (upsilon l) (ldAtR S l) c := by
  have hyH : leWe f * c ∈ cdHull S l := leMulWe_mem hfH hcH
  obtain ⟨hs, -, -⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [uaAdd hl hX e heH _ hyH hlt (by rw [hs]; exact hd), uaTerm hl hX hc1 hcW hyH (le_add_self.trans_lt hlt)]

/-- **`T(e + W^f) = T e + Ω^{T f}` for `W^f ∣ e`.** -/
theorem uaAddW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < uaGam) :
    uaTh S l (e + leWe f) = uaTh S l e + leOe (uaTh S l f) := by
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
  rw [he2, uaAddT hl hX hmH hfH hd1H le_add_self hd1W hmd (he2 ▸ hlt), gxTh_add hρSC hAt hdc,
    sqTh_one hl hX, mul_add_one, ← add_assoc]
  congr 1
  rw [hes, hsdec]
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
  · exact (uaAddT hl hX hmH hfH hdH (Order.one_le_iff_ne_zero.2 h0) hdW hmd
      ((le_self_add.trans_eq (by rw [hes, hsdec])).trans_lt hlt)).symm

/-- `T(e + 1) = T e + 1`. -/
theorem uaSucc {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (hlt : e + 1 < uaGam) :
    uaTh S l (e + 1) = uaTh S l e + 1 := by
  have h := uaAddW hl hX heH (CSet.zero_mem _ _) (by rw [leWe_zero]; exact one_dvd _) (by rwa [leWe_zero])
  rwa [leWe_zero, uaTh_zero, leOe_zero] at h

/-- **`W^f ∣ e` gives `Ω^{T f} ∣ T e`.** -/
theorem uaDvd : ∀ e, e ∈ cdHull S l → e < uaGam → ∀ f, f ∈ cdHull S l →
    leWe f ∣ e → leOe (uaTh S l f) ∣ uaTh S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH heE f hfH hd
  rcases eq_or_ne e 0 with rfl | he0
  · rw [uaTh_zero]; exact dvd_zero _
  have he0' : 0 < e := pos_iff_ne_zero.2 he0
  obtain ⟨hgH, hge, -, -, -, hrH, hrg, -, hTe, -⟩ := uaParts hl hX heH he0' heE
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
  exact dvd_add ((tuOe_dvd (uaLe hl hX hfH hgH (hge.trans_lt heE) hfg)).trans (dvd_mul_right _ _)) hIH

/-- **`T x < ψ_{Ω₂}(0)`** for `x ∈ H_λ`, `x < Γ₂`. -/
theorem uaLtG1 : ∀ x, x ∈ cdHull S l → x < uaGam → uaTh S l x < S.psi 0 (Om (1 + 1)) := by
  have hG1 := rwG_SC (S := S)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hxH hxE
  rcases lt_or_ge x (veblen (Om (1 + 1)) 1) with hxG | hxG
  · rw [uaTh_lt hxG]; exact tjThL_lt_G hl hX hxH hxG
  have h0 : 0 < x := veblen_pos.trans_le hxG
  by_cases hs : sgLW x < x
  · obtain ⟨hgH, -, -, -, hdW, hrH, hrg, -, hT, -⟩ := uaParts hl hX hxH h0 hxE
    have hrx : x % leWe (sgLW x) < x := hrg.trans_le (sgLW_le h0)
    have hTg := IH _ hs hgH (hs.trans hxE)
    have hTr := IH _ hrx hrH (hrx.trans hxE)
    rw [hT]
    exact hG1.isPrincipal (ldMul_lt_SC hG1 (leOe_lt_SC hG1 rwO_lt_G hTg).1
      ((snTh_lt_Om1 hl hX hdW.le).trans rwO_lt_G)) hTr
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := uaNode hxG hxE hs
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hxH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    rw [(uaNodeTh hl hX hxH hxG hxE hs).1]
    exact hG1.2 _ (IH _ haE hmem.1 (haE.trans hxE)) _ (IH _ hbE hmem.2 (hbE.trans hxE))

/-- **THE OWN PROPERTY**: an exponent `E < Γ₂` of `H_λ` that is a code over every `Q ≥ T` has `T E ∈ Cl(0, Θ T)`, and
`T E` is a level-1 code over every `Q ≥ Θ T`. -/
theorem uaOwn : ∀ E, E ∈ cdHull S l → E < uaGam → ∀ T, SC T →
    (∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q E) →
    uaTh S l E ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) ∧
      ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) T ≤ Q → LeCl (Om 1) Q (uaTh S l E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hEH hE T hT hcl
  rcases lt_or_ge E (veblen (Om (1 + 1)) 1) with hEG | hEG
  · rw [uaTh_lt hEG]; exact tjThL_own hl hX E hEH hEG T hT hcl
  have hpos : 0 < E := veblen_pos.trans_le hEG
  by_cases hc : sgLW E < E
  swap
  · obtain ⟨-, hv, -, haE, hbE, -, -⟩ := uaNode hEG hE hc
    have hmem := mem_of_veblen_mem (by rw [hv]; exact hEH) (by rw [hv]; exact haE) (by rw [hv]; exact hbE)
    have hEcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (veblen (invVeblen₁ E) (invVeblen₂ E)) :=
      fun Q hQ hTQ => by rw [hv]; exact hcl Q hQ hTQ
    have hacl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (invVeblen₁ E) := fun Q hQ hTQ =>
      tdCl_lev ldOm2_SC _ (hEcl Q hQ hTQ) _ _ rfl (by rw [hv]; exact hbE)
    have hbcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (invVeblen₂ E) := fun Q hQ hTQ =>
      uaCl_arg hQ ldOm2_SC _ (hEcl Q hQ hTQ) _ _ rfl (by rw [hv]; exact hbE)
    obtain ⟨a1, a2⟩ := IH _ haE hmem.1 (haE.trans hE) T hT hacl
    obtain ⟨b1, b2⟩ := IH _ hbE hmem.2 (hbE.trans hE) T hT hbcl
    rw [(uaNodeTh hl hX hEH hEG hE hc).1]
    exact ⟨CSet.phi_mem a1 b1, fun Q hQ hTQ => LeCl.phi (a2 Q hQ hTQ) (b2 Q hQ hTQ)⟩
  obtain ⟨heH, -, hqc, -, -, hrH, -, -, hTE, -⟩ := uaParts hl hX hEH hpos hE
  set e := sgLW E with he
  have hel : e < E := hc
  have hWe : leWe e ≤ E := sgLW_le hpos
  have hW0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have hr : E % leWe e < E := (Ordinal.mod_lt _ hW0).trans_le hWe
  have hecl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ => (Sw.swCl_cnf hQ (hcl Q hQ hTQ)).1
  have hrcl : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (E % leWe e) := fun Q hQ hTQ =>
    (Sw.swCl_cnf hQ (hcl Q hQ hTQ)).2.1
  have hqT : E / leWe e < T := (Sw.swCl_cnf hT (hcl T hT le_rfl)).2.2
  have hΘq := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hqc hqT
  obtain ⟨he1, he2⟩ := IH e hel heH (hel.trans hE) T hT hecl
  obtain ⟨hr1, hr2⟩ := IH _ hr hrH (hr.trans hE) T hT hrcl
  rw [hTE]
  refine ⟨CSet.add_mem (leMulOe_mem he1 (CSet.of_lt hΘq)) hr1, fun Q hQ hTQ => ?_⟩
  refine LeCl.add ?_ (hr2 Q hQ hTQ)
  exact rvCl_mulOp hQ (LeCl.mulK hQ Ph.ph_SC_Om1 _ (he2 Q hQ hTQ)) Ph.ph_SC_Om1 _
    (LeCl.small (hΘq.trans_le hTQ))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Ua
