import Googology.Trans.PoR.InaccPsi.R2.UqLad

/-!
# Windows past `Γ₂`: the index, the fine decomposition and the own transfers for the level codes

`T = Ug.ugTh`, `W^E = Ω₂^E`, `H_λ = cdHull S λ`, `C_k(Q) = Ug.UgC S k Q` (codes of level `k` with
`ψ_{Ω_{k+1}}`-atoms), `F_u = φ(Ω₂, u)` (windows `(F_u, F_{u+1})`), `Γ₂ = Ua.uaGam = F_{Γ₂}`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

`Ta.taCl_dec`, `Ta.taCl_idx`, `Ua.uaCl_idx`, `Ua.uaCl_FW`, `Ua.uaCl_levW`, `Ua.uaCl_NWin`, `Ua.uaCl_argW` for the level
codes: the atoms `ψ_{Ω_{k+1}}(d)` are strongly critical, so they are handled like `Ω_k` (an index `s` or `0`), and
no atom lies strictly inside a window.  `Ua.uaLimT`, `Ua.uaTh_max` for the image `T` below `Y₃`.

* `uqCl_dec` (**THE FINE DECOMPOSITION FOR LEVEL CODES**: a code `w < φ(a, X)`, `X` a limit, `a < Ω_k`, is below
  `φ(a, u)` for a code `u < X`), `uqIdx_SCz`, `uqCl_idx` (**the index of a level code is a code at every level `a`**);
* `uqGam_le_F`, `uqCl_FW`, `uqCl_levW`, `uqCl_NWin`, `uqCl_argW` (**the own transfers in a window `F_u ≥ Γ₂`**);
* `uqLimT` (**`T z` is a limit for a limit `z ∈ H_λ ∩ Y₃`**), `uqTh_max`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

section Code

variable {k Q : Ordinal.{0}} (hQ : SC Q) (hk : k ≠ 0)

include hQ hk

/-- **THE FINE DECOMPOSITION FOR LEVEL CODES**: a code `w < φ(a, X)` (`X` a limit, `a < Ω_k`) is below `φ(a, u)` for a
code `u < X`. -/
theorem uqCl_dec {a X : Ordinal.{0}} (haκ : a < Om k) (hX : IsSuccLimit X) :
    ∀ w, UgC S k Q w → w < veblen a X → ∃ u, UgC S k Q u ∧ u < X ∧ w < veblen a u := by
  have hκ : SC (Om k) := SC_Om hk
  -- a strongly critical code `s > a` below `φ(a, X)`
  have hSCc : ∀ s, SC s → a < s → UgC S k Q s → s < veblen a X → ∃ u, UgC S k Q u ∧ u < X ∧ s < veblen a u := by
    intro s hs has hsc hlt
    have hfix : veblen a s = s := hs.veblen_right has
    have hsX : s < X := by rw [← hfix] at hlt; exact (veblen_lt_veblen_iff_right).1 hlt
    refine ⟨s + 1, UgC.add hsc (UgC.small (gg_one_lt_of_SC hQ)), hX.add_one_lt hsX, ?_⟩
    calc s = veblen a s := hfix.symm
      _ < veblen a (s + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    by_cases hwX : w < X
    · exact ⟨w + 1, UgC.small (hQ.add_one_lt hwQ), hX.add_one_lt hwX,
        (lt_add_one w).trans_le (right_le_veblen a _)⟩
    · push Not at hwX
      obtain ⟨u, hu, hwu⟩ := ((isNormal_veblen a).lt_iff_exists_lt hX).1 hlt
      exact ⟨u, UgC.small ((hu.trans_le hwX).trans hwQ), hu, hwu⟩
  | om => exact hSCc _ hκ haκ UgC.om
  | @add x y _ _ ihx ihy =>
    intro hlt
    obtain ⟨u1, h1, hu1, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨u2, h2, hu2, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    refine ⟨max u1 u2, ?_, max_lt hu1 hu2, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
    · rcases le_total u1 u2 with h | h
      · rw [max_eq_right h]; exact h2
      · rw [max_eq_left h]; exact h1
    · exact (veblen_le_veblen_iff_right).2 (le_max_left _ _)
    · exact (veblen_le_veblen_iff_right).2 (le_max_right _ _)
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · obtain ⟨u, hu, huX, hqu⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      refine ⟨u, hu, huX, ?_⟩
      calc veblen p q < veblen p (veblen a u) := (veblen_lt_veblen_iff_right).2 hqu
        _ = veblen a u := veblen_veblen_of_lt hpa u
    · have hqX : q < X := (veblen_lt_veblen_iff_right).1 hlt
      exact ⟨q + 1, UgC.add hq (UgC.small (gg_one_lt_of_SC hQ)), hX.add_one_lt hqX,
        (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      have hwX : veblen p q < X := by
        rw [← hfix] at hlt; exact (veblen_lt_veblen_iff_right).1 hlt
      refine ⟨veblen p q + 1, UgC.add (UgC.phi hp hq) (UgC.small (gg_one_lt_of_SC hQ)), hX.add_one_lt hwX, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @psi d hd hdl _ =>
    have hs : SC (S.psi d (Om (k + 1))) := SC_psi (InR_Om_succ k) d
    exact hSCc _ hs (haκ.trans (psiS_bounds (S := S) d k).1) (UgC.psi hd hdl)

omit hk in
/-- **The index of a strongly critical code `z ≥ φ(a, 0)`** is a code (`z` itself, or `0` when `a = z`). -/
theorem uqIdx_SCz {a z : Ordinal.{0}} (hz : SC z) (hzc : UgC S k Q z) (h0 : veblen a 0 ≤ z) :
    ∃ u, UgC S k Q u ∧ veblen a u ≤ z ∧ z < veblen a (u + 1) := by
  rcases lt_or_ge a z with haz | hza
  · exact ⟨z, hzc, taIdx_SC hz haz⟩
  · have haz : a = z := le_antisymm ((left_le_veblen a 0).trans h0) hza
    subst haz
    refine ⟨0, UgC.zero hQ.1, hz.veblen_zero.le, ?_⟩
    calc a = veblen a 0 := hz.veblen_zero.symm
      _ < veblen a (0 + 1) := (veblen_lt_veblen_iff_right).2 (by rw [zero_add]; exact zero_lt_one)

/-- **THE INDEX OF A LEVEL CODE IS A CODE AT EVERY LEVEL `a`.** -/
theorem uqCl_idx {a : Ordinal.{0}} :
    ∀ w, UgC S k Q w → veblen a 0 ≤ w → ∃ u, UgC S k Q u ∧ veblen a u ≤ w ∧ w < veblen a (u + 1) := by
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, UgC.small (((right_le_veblen a u).trans h1).trans_lt hwQ), h1, h2⟩
  | om => exact uqIdx_SCz hQ (SC_Om hk) UgC.om
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin a 0
    by_cases hxa : veblen a 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin a _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin a _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hq0 : veblen a 0 ≤ q := by
        by_contra hq'
        push Not at hq'
        have : veblen p q < veblen a 0 := by
          calc veblen p q < veblen p (veblen a 0) := (veblen_lt_veblen_iff_right).2 hq'
            _ = veblen a 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen a (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen a (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, UgC.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @psi d hd hdl _ => exact uqIdx_SCz hQ (SC_psi (InR_Om_succ k) d) (UgC.psi hd hdl)

end Code

/-- `Γ₂ ≤ F_u` for `Γ₂ ≤ u`. -/
theorem uqGam_le_F {u : Ordinal.{0}} (hu : uaGam ≤ u) : uaGam ≤ veblen (Om (1 + 1)) u := by
  have h := (veblen_le_veblen_iff_right (o := Om (1 + 1))).2 hu
  rwa [uaGam_spec.1.veblen_right uaGam_spec.2] at h

/-- **No `ψ_{Ω₃}`-atom lies in `(F_u, F_{u+1})`.** -/
theorem uqWin_noAtom {u d : Ordinal.{0}} (h1 : veblen (Om (1 + 1)) u < S.psi d (Om (1 + 1 + 1)))
    (h2 : S.psi d (Om (1 + 1 + 1)) < veblen (Om (1 + 1)) (u + 1)) : False := by
  set s := S.psi d (Om (1 + 1 + 1)) with hs_def
  have hs : SC s := SC_psi (InR_Om_succ (1 + 1)) d
  have hfix : veblen (Om (1 + 1)) s = s := hs.veblen_right (ugOm2_lt_psi3 d)
  have hus : u < s := by rw [← hfix] at h1; exact (veblen_lt_veblen_iff_right).1 h1
  have hu1 : u + 1 < s := hs.isSuccLimit.add_one_lt hus
  have : veblen (Om (1 + 1)) (u + 1) < s := by
    calc veblen (Om (1 + 1)) (u + 1) < veblen (Om (1 + 1)) s := (veblen_lt_veblen_iff_right).2 hu1
      _ = s := hfix
  exact absurd (h2.trans this) (lt_irrefl _)

section Code2

variable {Q : Ordinal.{0}} (hQ : SC Q)

include hQ

/-- **A level-2 code inside `[F_u, F_{u+1})` gives the code `F_u`.** -/
theorem uqCl_FW {u h : Ordinal.{0}} (hh : UgC S (1 + 1) Q h) (h1 : veblen (Om (1 + 1)) u ≤ h)
    (h2 : h < veblen (Om (1 + 1)) (u + 1)) : UgC S (1 + 1) Q (veblen (Om (1 + 1)) u) := by
  have h0 : veblen (Om (1 + 1)) 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u', hu', hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
  have e : u' = u := taIdx_uniq hu1 hu2 h1 h2
  rw [← e]; exact UgC.phi UgC.om hu'

/-- **The level of a level-2 code above a node inside a window**: a code `h` with `φ(c, y) ≤ h < F_{u+1}`,
`F_u < φ(c, y)`, `c < Ω₂` gives the code `c`. -/
theorem uqCl_levW {u c y : Ordinal.{0}} (hcW : c < Om (1 + 1))
    (hF : veblen (Om (1 + 1)) u < veblen c y) :
    ∀ h, UgC S (1 + 1) Q h → veblen c y ≤ h → h < veblen (Om (1 + 1)) (u + 1) →
      UgC S (1 + 1) Q c := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle _
    exact UgC.small (((left_le_veblen c y).trans hle).trans_lt hwQ)
  | om =>
    intro hle _
    have h2 : Om (1 + 1) < veblen c y :=
      (ldOm2_SC.veblen_zero.symm.le.trans ((veblen_le_veblen_iff_right).2 zero_le)).trans_lt hF
    exact absurd (h2.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle hX
    by_cases hx : veblen c y ≤ x
    · exact ihx hx (le_self_add.trans_lt hX)
    by_cases hz : veblen c y ≤ z
    · exact ihz hz (le_add_self.trans_lt hX)
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle hX
    rcases lt_trichotomy p c with hpc | rfl | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      exact ihq hq ((right_le_veblen p q).trans_lt hX)
    · exact hp
    · have hpW : p < Om (1 + 1) := uaWin_lev (hF.trans_le hle) hX
      exact UgC.small (hcp.trans (ugC_lt_om hQ hp hpW))
  | @psi d _ _ _ =>
    intro hle hX
    exact (uqWin_noAtom (hF.trans_le hle) hX).elim

/-- **The own transfer at a successor argument in a window**: a level-2 code `h` with
`N = φ(a, y') < h ≤ φ(a, y' + 1)`, `h < F_{u+1}`, `F_u ≤ N`, `a < Ω₂`, gives the code `N`. -/
theorem uqCl_NWin {u a y' h : Ordinal.{0}} (haW : a < Om (1 + 1))
    (hFN : veblen (Om (1 + 1)) u ≤ veblen a y') (hh : UgC S (1 + 1) Q h) (h1 : veblen a y' < h)
    (h2 : h ≤ veblen a (y' + 1)) (hX : h < veblen (Om (1 + 1)) (u + 1)) : UgC S (1 + 1) Q (veblen a y') := by
  rcases hFN.lt_or_eq with hlt | heq
  · have hac := uqCl_levW hQ haW hlt h hh h1.le hX
    have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
    obtain ⟨u', hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
    have hlo : y' ≤ u' := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
    have hhi : u' ≤ y' + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
    exact UgC.phi hac (uqCl_of_succ hQ hlo hhi hu)
  · rw [← heq]; exact uqCl_FW hQ hh (heq ▸ h1.le) hX

/-- **The own transfer in the argument in a window**: a level-2 code `h` with `φ(a, m) ≤ h ≤ φ(a, z)`,
`h < F_{u+1}`, `F_u < φ(a, m)`, `a < Ω₂`, gives the code `a` and a code `v` with `m ≤ v ≤ z`. -/
theorem uqCl_argW {u a m z h : Ordinal.{0}} (haW : a < Om (1 + 1))
    (hFm : veblen (Om (1 + 1)) u < veblen a m) (hh : UgC S (1 + 1) Q h) (h1 : veblen a m ≤ h)
    (h2 : h ≤ veblen a z) (hX : h < veblen (Om (1 + 1)) (u + 1)) :
    UgC S (1 + 1) Q a ∧ ∃ v, UgC S (1 + 1) Q v ∧ m ≤ v ∧ v ≤ z := by
  have hac := uqCl_levW hQ haW hFm h hh h1 hX
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u', hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
  have hlo : m ≤ u' := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
  have hhi : u' ≤ z := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact ⟨hac, u', hu, hlo, hhi⟩

end Code2

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T z` is a limit for a limit `z ∈ H_λ ∩ Y₃`.** -/
theorem uqLimT : ∀ z, z ∈ cdHull S l → IsSuccLimit z → z < ugY S → IsSuccLimit (ugTh S l z) := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzH hlim hzY
  have h0 : 0 < z := hlim.bot_lt
  rcases lt_or_ge z uaGam with hzG | hGz
  · rw [ugTh_lt hzG]; exact uaLimT hl hX z hzH hlim hzG
  by_cases hs : sgLW z < z
  · obtain ⟨hgH, -, hdc, hd1, hdW, hrH, hrg, hzdec, hT, -⟩ := ugParts hl hX hzH h0 hzY
    set g := sgLW z with hg
    rw [hT]
    rcases eq_or_ne (z % leWe g) 0 with hr0 | hr0
    · rw [hr0, ugTh_zero, add_zero]
      rw [hr0, add_zero] at hzdec
      rcases eq_or_ne g 0 with hg0 | hg0
      · exfalso
        have hzW : z < Om (1 + 1) := by
          have h1 := sgLW_lt z
          rw [← hg, hg0, zero_add, leWe_one] at h1; exact h1
        exact absurd (hzW.trans uaGam_spec.2) (not_lt.2 hGz)
      · have hgpos : 0 < ugTh S l g := ugPos hl hX hgH (pos_iff_ne_zero.2 hg0) (hs.trans hzY)
        have hOlim : IsSuccLimit (leOe (ugTh S l g)) := by
          unfold leOe
          exact Ph.ph_opow_lim (mul_ne_zero (Om_pos one_ne_zero).ne' hgpos.ne')
        have hΘd : 0 < gxTh (upsilon l) (ldAtR S l) (z / leWe g) := by
          have h := gxTh_mono (Z := upsilon l) (At := ldAtR S l) hd1
          rw [sqTh_one hl hX] at h
          exact zero_lt_one.trans_le h
        exact isSuccLimit_mul_left hOlim hΘd
    · have hrlim : IsSuccLimit (z % leWe g) := by
        rcases zero_or_succ_or_isSuccLimit (z % leWe g) with h | ⟨r1, hr1⟩ | h
        · exact absurd h hr0
        · exfalso
          rw [succ_eq_add_one] at hr1
          have hz2 : z = leWe g * (z / leWe g) + r1 + 1 := by rw [add_assoc, hr1]; exact hzdec
          have h := hlim.succ_lt (lt_of_lt_of_eq (lt_add_one (leWe g * (z / leWe g) + r1)) hz2.symm)
          rw [Order.succ_eq_add_one, ← hz2] at h
          exact lt_irrefl _ h
        · exact h
      have hrz : z % leWe g < z := hrg.trans_le (sgLW_le h0)
      exact isSuccLimit_add _ (IH _ hrz hrH hrlim (hrz.trans hzY))
  · have hW := ugWfixTh hl hX hzH hGz hzY hs
    have hpos : 0 < ugTh S l z := ugPos hl hX hzH h0 hzY
    rw [← hW.2.2.1]
    exact Ph.ph_opow_lim hpos.ne'

/-- `T(max x z) = max (T x) (T z)`. -/
theorem uqTh_max {x z : Ordinal.{0}} (hxH : x ∈ cdHull S l) (hzH : z ∈ cdHull S l) (hxY : x < ugY S)
    (hzY : z < ugY S) : ugTh S l (max x z) = max (ugTh S l x) (ugTh S l z) := by
  rcases le_total x z with h | h
  · rw [max_eq_right h, max_eq_right (ugLe hl hX hxH hzH hzY h)]
  · rw [max_eq_left h, max_eq_left (ugLe hl hX hzH hxH hxY h)]

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
