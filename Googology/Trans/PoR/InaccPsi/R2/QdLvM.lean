import Googology.Trans.PoR.InaccPsi.R2.QdLv

/-!
# QdLvM: THE READING OF A VEBLEN LEVEL — ORDER, BOUND, DATA (Phase D1)

For a reading `f` of the leaves that is strictly increasing on a class `Dm` (containing `0`), below `Ω₁` and `0` at
`0`, the reading `Qd.qdLv f` of the Veblen levels `z < Γ_{Ω₂+1}` with leaves in `Dm` is below `Γ_{Ω₁+1}`, below `Ω₁`
exactly below `Ω₂`, an `ε`-number at an `ε`-number, with its data at most the largest reading of a leaf, and strictly
increasing (one induction; at a non-`ε` level `ω^l·n + r` the readings below `ω^l` stay below `ω^{l(x)}`,
`qd_top`).

* `qd_veb_inv`, `qd_cnf_parts`, `qd_cnf_log`, `qd_cnf_mod`, `qd_eps_pos`;
* `qdLv_main` (**THE READING OF A VEBLEN LEVEL**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

theorem qd_veb_inv {z : Ordinal.{0}} (hE : ω ^ z = z) : veblen (invVeblen₁ z) (invVeblen₂ z) = z := by
  rw [← (invVeblen₂_eq_iff.1 rfl), hE]

/-- The Cantor normal form `z = ω^l·n + r` of a non-`ε` `z > Ω₂`. -/
theorem qd_cnf_parts {z : Ordinal.{0}} (h1 : OmTwo < z) (hE : ω ^ z ≠ z) :
    ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z = z ∧ z % ω ^ log ω z < ω ^ log ω z ∧
      z / ω ^ log ω z ≠ 0 ∧ z / ω ^ log ω z < ω ∧ OmTwo ≤ log ω z ∧ log ω z < z := by
  have hz0 : z ≠ 0 := (qd_Om2_pos.trans h1).ne'
  have hω0 : ω ^ log ω z ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨div_add_mod z _, mod_lt z hω0, (div_opow_log_pos ω hz0).ne', div_opow_log_lt z one_lt_omega0, ?_,
    Ss.ss_log_lt hz0 hE⟩
  refine le_log_of_opow_le one_lt_omega0 ?_
  rw [show ω ^ (OmTwo : Ordinal.{0}) = OmTwo from Low.opow_eq_self_of_SC uc_SC_Om2]; exact h1.le

/-- The parts of a constructed Cantor normal form. -/
theorem qd_cnf_log {u n r : Ordinal.{0}} (hn0 : n ≠ 0) (hn : n < ω) (hr : r < ω ^ u) :
    log ω (ω ^ u * n + r) = u ∧ (ω ^ u * n + r) % ω ^ u = r ∧ (ω ^ u * n + r) / ω ^ u = n := by
  have hω0 : ω ^ u ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [log_opow_mul_add one_lt_omega0 hn0 hr, log_eq_zero hn, add_zero]
  · rw [mul_add_mod_self, mod_eq_of_lt hr]
  · rw [mul_add_div _ hω0, div_eq_zero_of_lt hr, add_zero]

/-- An `ε`-number `veblen o a` with `o ≥ 1`. -/
theorem qd_eps_veb {o a : Ordinal.{0}} (ho : o ≠ 0) : ω ^ veblen o a = veblen o a := by
  rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 ho) a

section Main

variable (f : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → f d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
include hf0 hD0 hfΩ hfm

/-- **THE READING OF A VEBLEN LEVEL**: below `Γ_{Ω₁+1}`, below `Ω₁` exactly below `Ω₂`, an `ε`-number at an
`ε`-number `≥ Ω₂`, its data at most the largest reading of a leaf, and strictly increasing. -/
theorem qdLv_main : ∀ z : Ordinal.{0}, z < qdG2 → (∀ d ∈ qdComps z, Dm d) →
    qdLv f z < ggGam ∧ Ss.ssDat (qdLv f z) ≤ qdFold f z ∧ (z < OmTwo → qdLv f z < Om1) ∧
      (OmTwo ≤ z → Om1 ≤ qdLv f z) ∧ (OmTwo ≤ z → ω ^ z = z → ω ^ qdLv f z = qdLv f z) ∧
      ∀ z', z' < z → (∀ d ∈ qdComps z', Dm d) → qdLv f z' < qdLv f z := by
  have hO1G : (Om1 : Ordinal.{0}) < ggGam := Ss.ss_Om1_lt_Gam
  have hGS : SC (ggGam : Ordinal.{0}) := ggGam_spec.1
  have hO1E : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  have hc0 : ∀ d ∈ qdComps 0, Dm d := fun d hd => by
    rw [qdComps_small qd_Om2_pos, mem_singleton_iff] at hd; rw [hd]; exact hD0
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzG hzD
  -- the order below `z` (pairs below `z`)
  have hord : ∀ u v, u < v → v < z → (∀ d ∈ qdComps u, Dm d) → (∀ d ∈ qdComps v, Dm d) →
      qdLv f u < qdLv f v := fun u v huv hvz hu hv =>
    (IH v hvz (hvz.trans hzG) hv).2.2.2.2.2 u huv hu
  rcases lt_trichotomy z OmTwo with hz2 | hz2 | hz2
  · -- a leaf
    have hzd : Dm z := hzD z (by rw [qdComps_small hz2]; exact mem_singleton _)
    rw [qdLv_small f hz2]
    refine ⟨(hfΩ z hzd).trans hO1G, ?_, fun _ => hfΩ z hzd, fun h => absurd hz2 (not_lt.2 h),
      fun h => absurd hz2 (not_lt.2 h), fun z' hz' hz'D => ?_⟩
    · rw [Ss.ssDat_small (hfΩ z hzd), qdFold_small f hz2]
    · have hz'd : Dm z' := hz'D z' (by rw [qdComps_small (hz'.trans hz2)]; exact mem_singleton _)
      rw [qdLv_small f (hz'.trans hz2)]; exact hfm z' z hz'd hzd hz'
  · -- `Ω₂`
    subst hz2
    rw [qdLv_Om2]
    refine ⟨hO1G, by rw [Ss.ssDat_Om1]; exact zero_le, fun h => absurd h (lt_irrefl _), fun _ => le_rfl,
      fun _ _ => hO1E, fun z' hz' hz'D => ?_⟩
    have hz'd : Dm z' := hz'D z' (by rw [qdComps_small hz']; exact mem_singleton _)
    rw [qdLv_small f hz']; exact hfΩ z' hz'd
  -- `z ∈ (Ω₂, Γ_{Ω₂+1})`
  have hz0 : z ≠ 0 := (qd_Om2_pos.trans hz2).ne'
  -- the facts of the parts below `z`
  have hpart : ∀ u, u < z → (∀ d ∈ qdComps u, Dm d) →
      qdLv f u < ggGam ∧ Ss.ssDat (qdLv f u) ≤ qdFold f u ∧ (u < OmTwo → qdLv f u < Om1) ∧
        (OmTwo ≤ u → Om1 ≤ qdLv f u) ∧ (OmTwo ≤ u → ω ^ u = u → ω ^ qdLv f u = qdLv f u) := fun u hu hD =>
    let h := IH u hu (hu.trans hzG) hD; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  have hL0 : qdLv f 0 = 0 := by rw [qdLv_small f qd_Om2_pos, hf0]
  by_cases hE : ω ^ z = z
  · -- an `ε`-number `z = φ(a, b)`
    set a := invVeblen₁ z with hadef
    set b := invVeblen₂ z with hbdef
    have hab : veblen a b = z := qd_veb_inv hE
    have haz : a < z := qd_inv1_lt hz2 hzG
    have hbz : b < z := Ss.ss_inv2_lt hE
    have hc := qdComps_phi hz2 hzG hE
    have haD : ∀ d ∈ qdComps a, Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inl hd)
    have hbD : ∀ d ∈ qdComps b, Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inr hd)
    have ha0 : a ≠ 0 := by
      intro h0
      have hzb : ω ^ b = z := by rw [← veblen_zero_apply, ← h0, hab]
      have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 hbz
      rw [hzb, hE] at h1
      exact lt_irrefl _ h1
    have hLa : 0 < qdLv f a := by
      rw [← hL0]; exact hord 0 a (pos_iff_ne_zero.2 ha0) haz hc0 haD
    have hLz : qdLv f z = veblen (qdLv f a) (qdLv f b) := qdLv_phi f hz2 hzG hE
    obtain ⟨ha1, ha2, ha3, ha4, -⟩ := hpart a haz haD
    obtain ⟨hb1, hb2, hb3, hb4, -⟩ := hpart b hbz hbD
    have hLzE : ω ^ qdLv f z = qdLv f z := by rw [hLz]; exact qd_eps_veb hLa.ne'
    -- `Ω₁ < z(x)`
    have hemp : ∀ d ∈ qdComps OmTwo, Dm d := by rw [qdComps_Om2]; exact fun _ h => absurd h (Set.notMem_empty _)
    have hOz : Om1 < qdLv f z := by
      rcases lt_trichotomy a OmTwo with h | h | h
      · have hb2' : OmTwo < b := by
          rcases lt_trichotomy b OmTwo with h' | h' | h'
          · exfalso
            have : veblen a b < OmTwo := uc_SC_Om2.2 a h b h'
            rw [hab] at this; exact absurd hz2 (not_lt.2 this.le)
          · exfalso
            have : veblen a OmTwo = OmTwo := uc_SC_Om2.veblen_right h
            rw [← h', hab] at this; exact absurd this hbz.ne'
          · exact h'
        have := hord OmTwo b hb2' hbz hemp hbD
        rw [qdLv_Om2] at this
        rw [hLz]; exact this.trans_le (right_le_veblen _ _)
      · have hb0 : b ≠ 0 := by
          intro h0
          have : veblen OmTwo 0 = OmTwo := uc_SC_Om2.veblen_zero
          rw [← h, ← h0, hab] at this; exact absurd this haz.ne'
        have hLb : 0 < qdLv f b := by rw [← hL0]; exact hord 0 b (pos_iff_ne_zero.2 hb0) hbz hc0 hbD
        rw [hLz, h, qdLv_Om2]
        calc Om1 = veblen Om1 0 := (Qc.qc_Om1_SC.veblen_zero).symm
          _ < veblen Om1 (qdLv f b) := veblen_lt_veblen_iff_right.2 hLb
      · have := hord OmTwo a h haz hemp haD
        rw [qdLv_Om2] at this
        rw [hLz]; exact this.trans_le (left_le_veblen _ _)
    -- the order
    have hP4 : ∀ w, w < z → (∀ d ∈ qdComps w, Dm d) → qdLv f w < qdLv f z := by
      intro w
      induction w using WellFoundedLT.induction with
      | ind w IHw =>
      intro hwz hwD
      rcases lt_trichotomy w OmTwo with hw2 | hw2 | hw2
      · have hwd : Dm w := hwD w (by rw [qdComps_small hw2]; exact mem_singleton _)
        rw [qdLv_small f hw2]; exact (hfΩ w hwd).trans hOz
      · rw [hw2, qdLv_Om2]; exact hOz
      have hwG : w < qdG2 := hwz.trans hzG
      by_cases hwE : ω ^ w = w
      · have hab' : veblen (invVeblen₁ w) (invVeblen₂ w) = w := qd_veb_inv hwE
        have ha'w : invVeblen₁ w < w := qd_inv1_lt hw2 hwG
        have hb'w : invVeblen₂ w < w := Ss.ss_inv2_lt hwE
        have hcw := qdComps_phi hw2 hwG hwE
        have ha'D : ∀ d ∈ qdComps (invVeblen₁ w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inl hd)
        have hb'D : ∀ d ∈ qdComps (invVeblen₂ w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inr hd)
        have hlt : veblen (invVeblen₁ w) (invVeblen₂ w) < veblen a b := by rw [hab', hab]; exact hwz
        rw [qdLv_phi f hw2 hwG hwE, hLz]
        rcases veblen_lt_veblen_iff.1 hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1]
          exact veblen_lt_veblen_iff_right.2 (hord _ b h2 hbz hb'D hbD)
        · have hLb' : qdLv f (invVeblen₂ w) < qdLv f z := IHw _ hb'w (h2.trans_eq hab) hb'D
          rw [hLz] at hLb'
          exact veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hord _ a h1 haz ha'D haD, hLb'⟩))
        · have h3 : w < b := by rw [← hab']; exact h2
          have := hord w b h3 hbz hwD hbD
          rw [qdLv_phi f hw2 hwG hwE] at this
          exact this.trans_le (right_le_veblen _ _)
      · obtain ⟨-, -, hn0, hnω, -, hlw⟩ := qd_cnf_parts hw2 hwE
        have hrw : w % ω ^ log ω w < w := rj_mod_lt (qd_Om2_pos.trans hw2).ne'
        have hcw := qdComps_cnf hw2 hwG hwE
        have hlD : ∀ d ∈ qdComps (log ω w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inl hd)
        have hrD : ∀ d ∈ qdComps (w % ω ^ log ω w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inr hd)
        rw [qdLv_cnf f hw2 hwG hwE]
        have hl := IHw _ hlw (hlw.trans hwz) hlD
        have hr := IHw _ hrw (hrw.trans hwz) hrD
        have hmul : ω ^ qdLv f (log ω w) * (w / ω ^ log ω w) < qdLv f z := by
          calc ω ^ qdLv f (log ω w) * (w / ω ^ log ω w) < ω ^ qdLv f (log ω w) * ω :=
                (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 hnω
            _ = ω ^ (qdLv f (log ω w) + 1) := by rw [opow_add, opow_one]
            _ < ω ^ qdLv f z := (opow_lt_opow_iff_right one_lt_omega0).2
                ((ev_isSuccLimit_of_inE hLzE).add_one_lt hl)
            _ = qdLv f z := hLzE
        exact (inE_indec hLzE).add_lt hmul hr
    refine ⟨?_, ?_, fun h => absurd hz2 (not_lt.2 h.le), fun _ => hOz.le, fun _ _ => hLzE, hP4⟩
    · rw [hLz]; exact hGS.2 _ ha1 _ hb1
    · -- the data
      have hLb := hP4 b hbz hbD
      rw [hLz] at hLb
      have hzG' : qdLv f z < ggGam := by rw [hLz]; exact hGS.2 _ ha1 _ hb1
      rw [Ss.ssDat_eq_phi hOz hzG' hLzE, hLz, invVeblen₁_veblen hLb, invVeblen₂_veblen hLa.ne' hLb,
        qdFold_phi f hz2 hzG hE]
      exact max_le_max ha2 hb2
  · -- a non-`ε` level `z = ω^l·n + r`
    obtain ⟨hdec, hrl, hn0, hnω, hl2, hlz⟩ := qd_cnf_parts hz2 hE
    have hrz : z % ω ^ log ω z < z := rj_mod_lt hz0
    have hc := qdComps_cnf hz2 hzG hE
    have hlD : ∀ d ∈ qdComps (log ω z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inl hd)
    have hrD : ∀ d ∈ qdComps (z % ω ^ log ω z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inr hd)
    have hLz : qdLv f z = ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) + qdLv f (z % ω ^ log ω z) :=
      qdLv_cnf f hz2 hzG hE
    obtain ⟨hl1, hl2', -, hl4, hl5⟩ := hpart _ hlz hlD
    obtain ⟨hr1, hr2, -, -, -⟩ := hpart _ hrz hrD
    have hOl : Om1 ≤ qdLv f (log ω z) := hl4 hl2
    have hzl : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
    -- the readings below `ω^u` stay below `ω^{u(x)}`, `Ω₂ ≤ u ≤ l`
    have htop : ∀ w u, OmTwo ≤ u → u ≤ log ω z → (∀ d ∈ qdComps u, Dm d) → w < ω ^ u →
        (∀ d ∈ qdComps w, Dm d) → qdLv f w < ω ^ qdLv f u := by
      intro w
      induction w using WellFoundedLT.induction with
      | ind w IHw =>
      intro u hu2 hul huD hwu hwD
      have huz : u < z := hul.trans_lt hlz
      have hwz : w < z := hwu.trans_le ((opow_le_opow_right omega0_pos hul).trans hzl)
      rcases lt_trichotomy w OmTwo with hw2 | hw2 | hw2
      · have hwd : Dm w := hwD w (by rw [qdComps_small hw2]; exact mem_singleton _)
        rw [qdLv_small f hw2]
        exact (hfΩ w hwd).trans_le (((IH u huz (huz.trans hzG) huD).2.2.2.1 hu2).trans
          (right_le_opow _ one_lt_omega0))
      · have hu2s : OmTwo < u := lt_of_le_of_ne hu2 fun h => by
          rw [← h, hO2E, hw2] at hwu; exact lt_irrefl _ hwu
        rw [hw2, qdLv_Om2]
        have := hord OmTwo u hu2s huz (by rw [qdComps_Om2]; exact fun _ h => absurd h (Set.notMem_empty _)) huD
        rw [qdLv_Om2] at this
        exact this.trans_le (right_le_opow _ one_lt_omega0)
      have hwG : w < qdG2 := hwz.trans hzG
      by_cases hwE : ω ^ w = w
      · have hwu' : w < u := by rw [← hwE] at hwu; exact (opow_lt_opow_iff_right one_lt_omega0).1 hwu
        exact (hord w u hwu' huz hwD huD).trans_le (right_le_opow _ one_lt_omega0)
      · obtain ⟨-, hrlw, hn0w, hnωw, hl2w, hlww⟩ := qd_cnf_parts hw2 hwE
        have hrw : w % ω ^ log ω w < w := rj_mod_lt (qd_Om2_pos.trans hw2).ne'
        have hcw := qdComps_cnf hw2 hwG hwE
        have hlwD : ∀ d ∈ qdComps (log ω w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inl hd)
        have hrwD : ∀ d ∈ qdComps (w % ω ^ log ω w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inr hd)
        have hlwu : log ω w < u := (lt_opow_iff_log_lt one_lt_omega0 (qd_Om2_pos.trans hw2).ne').1 hwu
        have hr := IHw _ hrw (log ω w) hl2w (hlwu.le.trans hul) hlwD hrlw hrwD
        have hlt := hord _ u hlwu huz hlwD huD
        rw [qdLv_cnf f hw2 hwG hwE]
        calc ω ^ qdLv f (log ω w) * (w / ω ^ log ω w) + qdLv f (w % ω ^ log ω w)
            < ω ^ qdLv f (log ω w) * (w / ω ^ log ω w) + ω ^ qdLv f (log ω w) := (add_lt_add_iff_left _).2 hr
          _ = ω ^ qdLv f (log ω w) * (w / ω ^ log ω w + 1) := (mul_add_one _ _).symm
          _ ≤ ω ^ qdLv f (log ω w) * ω := mul_le_mul_right (Order.add_one_le_of_lt hnωw) _
          _ = ω ^ (qdLv f (log ω w) + 1) := by rw [opow_add, opow_one]
          _ ≤ ω ^ qdLv f u := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hlt)
    have hrtop : qdLv f (z % ω ^ log ω z) < ω ^ qdLv f (log ω z) :=
      htop _ _ hl2 le_rfl hlD hrl hrD
    have hpow_le : ω ^ qdLv f (log ω z) ≤ qdLv f z := by
      rw [hLz]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)).trans le_self_add
    -- the reading of `ω^l`
    have hpowL : ∀ (h0 : ∀ d ∈ qdComps (ω ^ log ω z), Dm d), qdLv f (ω ^ log ω z) = ω ^ qdLv f (log ω z) := by
      intro _
      rcases hl2.lt_or_eq with hl2s | hl2e
      · by_cases hlE : ω ^ log ω z = log ω z
        · rw [hlE]; exact (hl5 hl2 hlE).symm
        · have h1 : OmTwo < ω ^ log ω z := hl2s.trans_le (right_le_opow _ one_lt_omega0)
          have hnE : ω ^ (ω ^ log ω z) ≠ ω ^ log ω z := fun h => hlE ((isNormal_opow one_lt_omega0).strictMono.injective h)
          rw [qdLv_cnf f h1 (hzl.trans_lt hzG) hnE]
          obtain ⟨e1, e2, e3⟩ := qd_cnf_log (u := log ω z) one_ne_zero one_lt_omega0 (opow_pos _ omega0_pos)
          rw [mul_one, add_zero] at e1 e2 e3
          rw [e1, e3, e2, mul_one, qdLv_small f qd_Om2_pos, hf0, add_zero]
      · rw [← hl2e, hO2E, qdLv_Om2, hO1E]
    -- the order
    have hP4 : ∀ w, w < z → (∀ d ∈ qdComps w, Dm d) → qdLv f w < qdLv f z := by
      intro w hwz hwD
      rcases lt_or_ge w (ω ^ log ω z) with hwl | hwl
      · exact (htop w _ hl2 le_rfl hlD hwl hwD).trans_le hpow_le
      rcases hwl.lt_or_eq with hwl' | hwl'
      · -- `ω^l < w < z`: `w = ω^l·n' + r'`
        have hw2 : OmTwo < w := (hl2.trans (right_le_opow _ one_lt_omega0)).trans_lt hwl'
        have hwG : w < qdG2 := hwz.trans hzG
        have hlog : log ω w = log ω z :=
          le_antisymm (log_mono_right _ hwz.le) (le_log_of_opow_le one_lt_omega0 hwl'.le)
        have hwE : ω ^ w ≠ w := by
          intro h
          have h1 : log ω w = w := by conv_lhs => rw [← h]
                                      exact log_opow one_lt_omega0 w
          rw [h1] at hlog
          rw [← hlog] at hwl'
          exact absurd hwl' (not_lt.2 (right_le_opow _ one_lt_omega0))
        obtain ⟨hdecw, hrlw, hn0w, hnωw, -, -⟩ := qd_cnf_parts hw2 hwE
        have hcw := qdComps_cnf hw2 hwG hwE
        have hrwD : ∀ d ∈ qdComps (w % ω ^ log ω w), Dm d := fun d hd => hwD d (by rw [hcw]; exact Or.inr hd)
        rw [qdLv_cnf f hw2 hwG hwE, hLz, hlog]
        rw [hlog] at hrwD hdecw hrlw
        have hrw' : qdLv f (w % ω ^ log ω z) < ω ^ qdLv f (log ω z) := htop _ _ hl2 le_rfl hlD hrlw hrwD
        rcases lt_trichotomy (w / ω ^ log ω z) (z / ω ^ log ω z) with hn | hn | hn
        · calc ω ^ qdLv f (log ω z) * (w / ω ^ log ω z) + qdLv f (w % ω ^ log ω z)
              < ω ^ qdLv f (log ω z) * (w / ω ^ log ω z) + ω ^ qdLv f (log ω z) := (add_lt_add_iff_left _).2 hrw'
            _ = ω ^ qdLv f (log ω z) * (w / ω ^ log ω z + 1) := (mul_add_one _ _).symm
            _ ≤ ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) := mul_le_mul_right (Order.add_one_le_of_lt hn) _
            _ ≤ _ := le_self_add
        · rw [hn]
          have hrr : w % ω ^ log ω z < z % ω ^ log ω z := by
            have h : ω ^ log ω z * (z / ω ^ log ω z) + w % ω ^ log ω z <
                ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z := by
              calc _ = w := by rw [← hn]; exact hdecw
                _ < z := hwz
                _ = _ := hdec.symm
            exact (add_lt_add_iff_left _).1 h
          exact (add_lt_add_iff_left _).2 (hord _ _ hrr hrz hrwD hrD)
        · exfalso
          have : z < w :=
            calc z = ω ^ log ω z * (z / ω ^ log ω z) + z % ω ^ log ω z := hdec.symm
              _ < ω ^ log ω z * (z / ω ^ log ω z) + ω ^ log ω z := (add_lt_add_iff_left _).2 hrl
              _ = ω ^ log ω z * (z / ω ^ log ω z + 1) := (mul_add_one _ _).symm
              _ ≤ ω ^ log ω z * (w / ω ^ log ω z) := mul_le_mul_right (Order.add_one_le_of_lt hn) _
              _ ≤ ω ^ log ω z * (w / ω ^ log ω z) + w % ω ^ log ω z := le_self_add
              _ = w := hdecw
          exact absurd hwz (not_lt.2 this.le)
      · -- `w = ω^l`
        rw [← hwl', hpowL (hwl' ▸ hwD), hLz]
        rcases eq_or_ne (z % ω ^ log ω z) 0 with hr0 | hr0
        · have hn1 : 1 < z / ω ^ log ω z := by
            by_contra h; push Not at h
            have h1 : z / ω ^ log ω z = 1 := le_antisymm h (one_le_iff_ne_zero.2 hn0)
            have : z = ω ^ log ω z := by
              conv_lhs => rw [← hdec]
              rw [h1, hr0, mul_one, add_zero]
            exact absurd hwz (by rw [← hwl', ← this]; exact lt_irrefl _)
          rw [hr0, qdLv_small f qd_Om2_pos, hf0, add_zero]
          calc ω ^ qdLv f (log ω z) = ω ^ qdLv f (log ω z) * 1 := (mul_one _).symm
            _ < ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) := (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 hn1
        · have hLr : 0 < qdLv f (z % ω ^ log ω z) := by
            rw [← hL0]; exact hord 0 _ (pos_iff_ne_zero.2 hr0) hrz hc0 hrD
          calc ω ^ qdLv f (log ω z) ≤ ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) :=
                le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)
            _ < _ := lt_add_of_pos_right _ hLr
    have hGE : ω ^ (ggGam : Ordinal.{0}) = ggGam := Low.opow_eq_self_of_SC hGS
    have hz1 : qdLv f z < ggGam := by
      rw [hLz]
      have hm : ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) < ggGam := by
        calc ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) < ω ^ qdLv f (log ω z) * ω :=
              (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 hnω
          _ = ω ^ (qdLv f (log ω z) + 1) := by rw [opow_add, opow_one]
          _ < ω ^ ggGam := (opow_lt_opow_iff_right one_lt_omega0).2 (hGS.isSuccLimit.add_one_lt hl1)
          _ = ggGam := hGE
      exact (inE_indec hGE).add_lt hm hr1
    have hOz : Om1 < qdLv f z := hOl.trans_lt (hP4 _ hlz hlD)
    refine ⟨hz1, ?_, fun h => absurd hz2 (not_lt.2 h.le), fun _ => hOz.le, fun _ h => absurd h hE, hP4⟩
    -- the data
    obtain ⟨e1, e2, -⟩ := qd_cnf_log (u := qdLv f (log ω z)) hn0 hnω hrtop
    have hnE : ω ^ qdLv f z ≠ qdLv f z := by
      intro h
      have h1 : log ω (qdLv f z) = qdLv f z := by conv_lhs => rw [← h]
                                                  exact log_opow one_lt_omega0 _
      have h2 := hP4 _ hlz hlD
      rw [hLz, e1] at h1
      rw [hLz] at h2
      rw [← h1] at h2; exact lt_irrefl _ h2
    rw [Ss.ssDat_eq_cnf hOz hz1 hnE, hLz, e1, e2, qdFold_cnf f hz2 hzG hE]
    exact max_le_max hl2' hr2

end Main

end Googology.Trans.PoR.InaccPsi.R2.Qd
