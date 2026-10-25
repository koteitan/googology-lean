import Googology.Trans.PoR.InaccPsi.R2.UqNodeW

/-!
# Level codes at the levels above `Ω₂`: the own transfers for nodes `φ(a, y)` with any level `a`, past `Γ₂`

`φ = veblen`, `C_k(Q) = Ug.UgC S k Q` (`Q` strongly critical), `T = Ug.ugTh`, `G = φ(Ω₂, 1)`, `Y₃ = ψ_{Ω₃}(Ω₃)`.

`Ud.udCl_levGe`, `Ua.uaCl_levG`, `Ud.udCl_N`, `Ud.udCl_tow`, `Ud.udCl_dec`, `Ud.udCl_levDec0`, `Ud.udThr`,
`Ud.udOwn0`, `Ud.udOwnArg` for the level codes: an atom `ψ_{Ω₃}(d)` is strongly critical, hence a fixed point of
every `φ(c, ·)` with `c` below it and equal to `φ(s, 0)`, so it is one more node `φ(s, 0)` with the code level `s`.

* `uqCl_levGe`, `uqCl_levG` (**THE LEVEL OF A LEVEL CODE AT EVERY LEVEL**), `uqCl_N` (**THE OWN TRANSFER AT A SUCCESSOR
  ARGUMENT, EVERY LEVEL**), `uqCl_tow`, `uqCl_decA`, `uqCl_levDec0`;
* `uqThr` (**the threshold of a limit argument** with level codes), `uqOwn0`, `uqOwnArg`;
* `uqVeb` (**`T(φ(a, y)) = φ(T a, T y)` for `G ≤ φ(a, y) < Y₃`**, by `Ua.uaVeb` below `Γ₂`, `Ug.ugVeb` above).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua Googology.Trans.PoR.InaccPsi.R2.Ud Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

section Code

variable {Q : Ordinal.{0}} (hQ : SC Q)

include hQ

omit hQ in
/-- **A level-2 code above `φ(c, y) > Ω₂` contains a node with a code level `p ≥ c` between them.** -/
theorem uqCl_levGe {c y : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen c y) :
    ∀ h, UgC S (1 + 1) Q h → veblen c y ≤ h →
      ∃ p q, UgC S (1 + 1) Q p ∧ c ≤ p ∧ veblen c y ≤ veblen p q ∧ veblen p q ≤ h := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle
    exact ⟨c, y, UgC.small (((left_le_veblen c y).trans hle).trans_lt hwQ), le_rfl, le_rfl, hle⟩
  | om =>
    intro hle
    exact absurd (hΩ.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle
    by_cases hx : veblen c y ≤ x
    · obtain ⟨p, q, a1, a2, a3, a4⟩ := ihx hx
      exact ⟨p, q, a1, a2, a3, a4.trans le_self_add⟩
    by_cases hz : veblen c y ≤ z
    · obtain ⟨p, q, a1, a2, a3, a4⟩ := ihz hz
      exact ⟨p, q, a1, a2, a3, a4.trans le_add_self⟩
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle
    rcases lt_or_ge p c with hpc | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      obtain ⟨p', q', a1, a2, a3, a4⟩ := ihq hq
      exact ⟨p', q', a1, a2, a3, a4.trans (right_le_veblen p q)⟩
    · exact ⟨p, q, hp, hcp, hle, le_rfl⟩
  | @psi d hd hdl _ =>
    intro hle
    have hs : SC (S.psi d (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) d
    refine ⟨_, 0, UgC.psi hd hdl, (left_le_veblen c y).trans hle, ?_, ?_⟩
    · rw [hs.veblen_zero]; exact hle
    · rw [hs.veblen_zero]

omit hQ in
/-- **THE LEVEL OF A LEVEL CODE AT EVERY LEVEL**: a code `h ≥ φ(c, y) > Ω₂` with no fixed point of `φ(c, ·)` in
`[φ(c, y), h]` gives the code `c`. -/
theorem uqCl_levG {c y : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen c y) :
    ∀ h, UgC S (1 + 1) Q h → veblen c y ≤ h → (∀ v, veblen c y ≤ v → v ≤ h → veblen c v ≠ v) →
      UgC S (1 + 1) Q c := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle _
    exact UgC.small (((left_le_veblen c y).trans hle).trans_lt hwQ)
  | om =>
    intro hle _
    exact absurd (hΩ.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle hnf
    by_cases hx : veblen c y ≤ x
    · exact ihx hx fun v h1 h2 => hnf v h1 (h2.trans le_self_add)
    by_cases hz : veblen c y ≤ z
    · exact ihz hz fun v h1 h2 => hnf v h1 (h2.trans le_add_self)
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle hnf
    rcases lt_trichotomy p c with hpc | rfl | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      exact ihq hq fun v h1 h2 => hnf v h1 (h2.trans (right_le_veblen p q))
    · exact hp
    · exact absurd (veblen_veblen_of_lt hcp q) (hnf _ hle le_rfl)
  | @psi d hd hdl _ =>
    intro hle hnf
    have hs : SC (S.psi d (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) d
    rcases lt_or_ge c (S.psi d (Om (1 + 1 + 1))) with hcs | hsc
    · exact absurd (hs.veblen_right hcs) (hnf _ hle le_rfl)
    · have : c = S.psi d (Om (1 + 1 + 1)) := le_antisymm ((left_le_veblen c y).trans hle) hsc
      rw [this]; exact UgC.psi hd hdl

/-- **THE OWN TRANSFER AT A SUCCESSOR ARGUMENT, EVERY LEVEL, FOR LEVEL CODES**: a code `h` with
`N = φ(a, y') < h ≤ φ(a, y' + 1)`, `Ω₂ < N`, gives the code `N`. -/
theorem uqCl_N {a y' h : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen a y') (hh : UgC S (1 + 1) Q h)
    (h1 : veblen a y' < h) (h2 : h ≤ veblen a (y' + 1)) : UgC S (1 + 1) Q (veblen a y') := by
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
  obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
  have hlo : y' ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
  have hhi : u ≤ y' + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  have hy' : UgC S (1 + 1) Q y' := uqCl_of_succ hQ hlo hhi hu
  by_cases hfix : veblen a y' = y'
  · rw [hfix]; exact hy'
  · have hy : y' < veblen a y' := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hfix)
    have hac := uqCl_levG hΩ h hh h1.le fun v hv1 hv2 => by
      rcases hv1.lt_or_eq with hlt | rfl
      · exact uaNoFix hlt (hv2.trans h2)
      · exact udNotFix hy
    exact UgC.phi hac hy'

/-- **The level of a tower for level codes**: a code `h` with `φ(a', x) ≤ h ≤ φ(a' + 1, y)` (`y < φ(a' + 1, y)`,
`Ω₂ < φ(a', x)`) and every `φ(a' + 1, z)`, `z < y`, below `φ(a', x)` gives the code `a'`. -/
theorem uqCl_tow {a' x y h : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen a' x) (hy : y < veblen (a' + 1) y)
    (hlow : ∀ z, z < y → veblen (a' + 1) z < veblen a' x) (hh : UgC S (1 + 1) Q h)
    (h1 : veblen a' x ≤ h) (h2 : h ≤ veblen (a' + 1) y) : UgC S (1 + 1) Q a' := by
  rcases h2.lt_or_eq with hlt | heq
  · refine uqCl_levG hΩ h hh h1 fun v hv1 hv2 hfix => ?_
    obtain ⟨z, hz, hzv⟩ := udFix_lt hfix (hv2.trans_lt hlt)
    have := hlow z hz
    rw [hzv] at this
    exact absurd hv1 (not_le.2 this)
  · have ha : UgC S (1 + 1) Q (a' + 1) := ugC_lev h hh (a' + 1) y heq (heq ▸ hy)
    exact uqC_pred hQ ugTwo_ne a' ha

/-- **The fine decomposition at every level `a`** for level-`k` codes: a code `w < φ(a, X)` (`X` a limit) is below
`φ(a, u)` for a code `u < X`. -/
theorem uqCl_decA {k a X : Ordinal.{0}} (hk : k ≠ 0) (hX : IsSuccLimit X) :
    ∀ w, UgC S k Q w → w < veblen a X → ∃ u, UgC S k Q u ∧ u < X ∧ w < veblen a u := by
  intro w hw hwX
  have h1X : 1 < X := Rv.rvLim_one_lt hX
  rcases lt_or_ge w (veblen a 0) with hw0 | hw0
  · exact ⟨1, UgC.small (gg_one_lt_of_SC hQ), h1X, hw0.trans ((veblen_lt_veblen_iff_right).2 zero_lt_one)⟩
  · obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ hk w hw hw0
    have huX : u < X := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hwX)
    exact ⟨u + 1, UgC.add hu (UgC.small (gg_one_lt_of_SC hQ)), hX.add_one_lt huX, hu2⟩

/-- **The level decomposition at the argument `0` for level codes**: at a limit level `c`, a code `w < φ(c, 0)` is
below `φ(c', 0)` for a code `c' < c`. -/
theorem uqCl_levDec0 {k c : Ordinal.{0}} (hk : k ≠ 0) (hc : IsSuccLimit c) :
    ∀ w, UgC S k Q w → w < veblen c 0 → ∃ c', UgC S k Q c' ∧ c' < c ∧ w < veblen c' 0 := by
  have h1 : UgC S k Q (1 : Ordinal.{0}) := UgC.small (gg_one_lt_of_SC hQ)
  have triv : ∀ w, UgC S k Q w → w < c → ∃ c', UgC S k Q c' ∧ c' < c ∧ w < veblen c' 0 := fun w hw hwc =>
    ⟨w + 1, UgC.add hw h1, hc.add_one_lt hwc, (lt_add_one w).trans_le (left_le_veblen _ _)⟩
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    rcases lt_or_ge w c with hwc | hcw
    · exact triv w (UgC.small hwQ) hwc
    · obtain ⟨c', hc', hwc'⟩ := udLev0 hc hlt
      exact ⟨c', UgC.small ((hc'.trans_le hcw).trans hwQ), hc', hwc'⟩
  | om =>
    intro hlt
    exact triv _ UgC.om (udSC_lt (SC_Om hk) hlt)
  | @add x y hx hy ihx ihy =>
    intro hlt
    obtain ⟨c1, hc1, hc1c, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨c2, hc2, hc2c, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    rcases le_total c1 c2 with h | h
    · exact ⟨c2, hc2, hc2c, Ph.ph_veblen_prin c2 _ (hx1.trans_le (veblen_left_monotone _ h)) hy2⟩
    · exact ⟨c1, hc1, hc1c, Ph.ph_veblen_prin c1 _ hx1 (hy2.trans_le (veblen_left_monotone _ h))⟩
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p c with hpc | rfl | hpc
    · obtain ⟨cq, hcq, hcqc, hqq⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      set m := max p cq with hm
      have hmc : m < c := max_lt hpc hcqc
      have hmcl : UgC S k Q m := by
        rcases le_total p cq with h | h
        · rw [hm, max_eq_right h]; exact hcq
        · rw [hm, max_eq_left h]; exact hp
      refine ⟨m + 1, UgC.add hmcl h1, hc.add_one_lt hmc, ?_⟩
      have hpm : p < m + 1 := (le_max_left p cq).trans_lt (lt_add_one m)
      have hq' : q < veblen (m + 1) 0 :=
        hqq.trans_le (veblen_left_monotone _ ((le_max_right p cq).trans (le_self_add : m ≤ m + 1)))
      calc veblen p q < veblen p (veblen (m + 1) 0) := (veblen_lt_veblen_iff_right).2 hq'
        _ = veblen (m + 1) 0 := veblen_veblen_of_lt hpm _
    · exact absurd hlt (not_lt.2 ((veblen_le_veblen_iff_right).2 zero_le))
    · exact absurd hlt (udVeb_not_lt0 hpc)
  | @psi d hd hdl _ =>
    intro hlt
    exact triv _ (UgC.psi hd hdl) (udSC_lt (SC_psi (InR_Om_succ k) d) hlt)

end Code

/-- **The threshold of a limit argument, level codes**: `t < y` in the closure with no fixed point of `φ(a, ·)` in
`(t, y]`, and `t + 1` a level-2 code under every code `h` with `φ(a, t + 1) ≤ h ≤ φ(a, y)`. -/
theorem uqThr {A B a y : Ordinal.{0}} (haH : a ∈ S.CSet A B) (hyH : y ∈ S.CSet A B) (hΩ : Om (1 + 1) < a)
    (hy : y < veblen a y) (hylim : IsSuccLimit y) :
    ∃ t, t ∈ S.CSet A B ∧ t < y ∧ (∀ v, t < v → v ≤ y → veblen a v ≠ v) ∧
      (∀ Q, SC Q → ∀ h, UgC S (1 + 1) Q h → veblen a (t + 1) ≤ h → h ≤ veblen a y →
        UgC S (1 + 1) Q (t + 1)) := by
  rcases lt_or_ge y (veblen (a + 1) 0) with hy0 | hy0
  · refine ⟨0, CSet.zero_mem _ _, hylim.bot_lt, fun v _ hvy hfix => ?_, fun Q hQ _ _ _ _ => ?_⟩
    · obtain ⟨z, hz, -⟩ := udFix_lt hfix (hvy.trans_lt hy0)
      exact absurd hz (not_lt.2 zero_le)
    · rw [zero_add]; exact UgC.small (gg_one_lt_of_SC hQ)
  obtain ⟨u, huH, hu1, hu2⟩ := txHull_idx hyH hy0
  set t := veblen (a + 1) u with ht
  have htfix : veblen a t = t := veblen_veblen_of_lt (lt_add_one a) u
  have hty : t < y := lt_of_le_of_ne hu1 fun e => absurd (e ▸ htfix) (ne_of_gt hy)
  have hΩt : Om (1 + 1) < t :=
    hΩ.trans_le ((le_self_add.trans (left_le_veblen (a + 1) 0)).trans ((veblen_le_veblen_iff_right).2 zero_le))
  refine ⟨t, CSet.phi_mem (CSet.succ_mem haH) huH, hty, fun v htv hvy hfix => ?_, fun Q hQ h hh h1 h2 => ?_⟩
  · obtain ⟨z, hz, hzv⟩ := udFix_lt hfix (hvy.trans_lt hu2)
    have : v ≤ t := by rw [← hzv]; exact (veblen_le_veblen_iff_right).2 (Order.lt_add_one_iff.1 hz)
    exact absurd htv (not_lt.2 this)
  · have hE : veblen a y < veblen (a + 1) (u + 1) := by
      calc veblen a y < veblen a (veblen (a + 1) (u + 1)) := (veblen_lt_veblen_iff_right).2 hu2
        _ = veblen (a + 1) (u + 1) := veblen_veblen_of_lt (lt_add_one a) _
    have htc : UgC S (1 + 1) Q t := uqCl_N hQ hΩt hh
      ((lt_add_one t).trans_le ((right_le_veblen a (t + 1)).trans h1)) (h2.trans hE.le)
    exact UgC.add htc (UgC.small (gg_one_lt_of_SC hQ))

/-- The own transfer at a node `φ(m, 0) ≤ h ≤ φ(a, 0)` (`m > Ω₂`): a code level `p` with `m ≤ p ≤ a`. -/
theorem uqOwn0 {Q a m h : Ordinal.{0}} (hm : Om (1 + 1) < m) (hh : UgC S (1 + 1) Q h) (h1 : veblen m 0 ≤ h)
    (h2 : h ≤ veblen a 0) : ∃ p, UgC S (1 + 1) Q p ∧ m ≤ p ∧ p ≤ a := by
  obtain ⟨p, q, hp, hmp, -, hq2⟩ := uqCl_levGe (hm.trans_le (left_le_veblen m 0)) h hh h1
  exact ⟨p, hp, hmp, udLev_le0 (hq2.trans h2)⟩

/-- The own transfer at a node `φ(a, m) ≤ h ≤ φ(a, y)` (`a > Ω₂`, no fixed point of `φ(a, ·)` in `[m, y]`): the
code `a` and a code `u` with `m ≤ u ≤ y`. -/
theorem uqOwnArg {Q a m y h : Ordinal.{0}} (hQ : SC Q) (hΩa : Om (1 + 1) < a)
    (hnf : ∀ v, m ≤ v → v ≤ y → veblen a v ≠ v) (hh : UgC S (1 + 1) Q h) (h1 : veblen a m ≤ h)
    (h2 : h ≤ veblen a y) : UgC S (1 + 1) Q a ∧ ∃ u, UgC S (1 + 1) Q u ∧ m ≤ u ∧ u ≤ y := by
  have hΩ : Om (1 + 1) < veblen a m := hΩa.trans_le (left_le_veblen a m)
  have hac := uqCl_levG hΩ h hh h1 fun v hv1 hv2 hfix => by
    have hmv : m ≤ v := by
      have := hv1; rw [← hfix] at this; exact (veblen_le_veblen_iff_right).1 this
    have hvy : v ≤ y := by
      have := hv2.trans h2; rw [← hfix] at this; exact (veblen_le_veblen_iff_right).1 this
    exact hnf v hmv hvy hfix
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u, hu, hu1, hu2⟩ := uqCl_idx hQ ugTwo_ne h hh h0
  have hlo : m ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
  have hhi : u ≤ y := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact ⟨hac, u, hu, hlo, hhi⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`T(φ(a, y)) = φ(T a, T y)` for `G ≤ φ(a, y) < Y₃`** (`a ≠ 0`). -/
theorem uqVeb {a y : Ordinal.{0}} (haH : a ∈ cdHull S l) (hyH : y ∈ cdHull S l) (ha0 : a ≠ 0)
    (hG : veblen (Om (1 + 1)) 1 ≤ veblen a y) (hY : veblen a y < ugY S) :
    ugTh S l (veblen a y) = veblen (ugTh S l a) (ugTh S l y) := by
  rcases lt_or_ge (veblen a y) uaGam with h | h
  · rw [ugTh_lt h, ugTh_lt ((left_le_veblen a y).trans_lt h), ugTh_lt ((right_le_veblen a y).trans_lt h)]
    exact uaVeb hl hX haH hyH ha0 hG h
  · exact ugVeb hl hX haH hyH ha0 h hY

end Main

end Googology.Trans.PoR.InaccPsi.R2.Uq
