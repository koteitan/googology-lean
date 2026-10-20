import Googology.Trans.PoR.InaccPsi.R2.LvGLev

/-!
# `lvgSys n` has terms for every code below `gc n`, and its frontier lies below `L(0)`

The codes of the tops: `gc 0 = φ(1, Ω₁ + 1) = ε_{Ω₁+1}`, `gc (n+1) = φ(gc n, 0)` (`gc n < Γ_{Ω₁+1}`):

* `gcTh` (**`Θ_y(gc n) = gT n y`** for a strongly critical `y < Ω₁`), `levToG` (the theta-free terms of `LvET` read in
  `LvGT`, stage `0`);
* `lvgPoly` (**`GgPoly (lvgSys n) (gc n)` for every `n`**, by induction on `n`: a code `c < φ(gc n, 0)` is a constant,
  `Ω₁`, a sum, a power, `φ_a(b)` with a constant level `1 ≤ a < Z` (the term `th0 a t`), or `φ_a(b)` with
  `Ω₁ ≤ a < gc n`, read as `tl l t` with the term `l` of `a` given by `GgPoly (lvgSys n) (gc n)`);
* `lvg_fr` (**`Λ⁺(lvgSys n) ≤ ι(ω^{gc n}·ω) < L(0)`, `υ_{Λ⁺(lvgSys n)} < L(0)`**), `lvg_fr_order`.

No new axiom beyond `R2.CitedLu` and `R2.CitedLv`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Ph Lu

/-- The codes of the tops. -/
noncomputable def gc : ℕ → Ordinal.{0}
  | 0 => veblen 1 (Om 1 + 1)
  | n + 1 => veblen (gc n) 0

/-- The theta-free terms of `LvET`, read in `LvGT`. -/
def levToG : LvET → LvGT
  | .cst a => .cst a
  | .bs => .bs
  | .th0 _ _ => .cst 0
  | .tl _ _ => .cst 0
  | .sm a b => .sm (levToG a) (levToG b)
  | .pw t => .pw (levToG t)

theorem levToG_val : ∀ l : LvET, LvET.isLev l → ∀ x, LvGT.val (levToG l) x = LvET.val l x
  | .cst _, _, _ => rfl
  | .bs, _, _ => rfl
  | .th0 _ _, h, _ => absurd h id
  | .tl _ _, h, _ => absurd h id
  | .sm a b, h, x => by
      show LvGT.val (levToG a) x + LvGT.val (levToG b) x = _
      rw [levToG_val a h.1 x, levToG_val b h.2 x]; rfl
  | .pw t, h, x => by
      show ω ^ LvGT.val (levToG t) x = _
      rw [levToG_val t h x]; rfl

theorem levToG_cb : ∀ l : LvET, LvET.isLev l → ∀ {x}, LvET.CBt l x → LvGT.CBt (levToG l) x
  | .cst _, _, _, h => h
  | .bs, _, _, _ => trivial
  | .th0 _ _, h, _, _ => absurd h id
  | .tl _ _, h, _, _ => absurd h id
  | .sm a b, h, _, hc => ⟨levToG_cb a h.1 hc.1, levToG_cb b h.2 hc.2⟩
  | .pw t, h, _, hc => levToG_cb t h hc

theorem levToG_stage : ∀ l : LvET, LvET.isLev l → LvGT.stage (levToG l) = 0
  | .cst _, _ => rfl
  | .bs, _ => rfl
  | .th0 _ _, h => absurd h id
  | .tl _ _, h => absurd h id
  | .sm a b, h => by
      show max (LvGT.stage (levToG a)) (LvGT.stage (levToG b)) = 0
      rw [levToG_stage a h.1, levToG_stage b h.2]; rfl
  | .pw t, h => levToG_stage t h

section Codes

variable {Z : Ordinal.{0}}

theorem gc_cl (hZ : SC Z) : ∀ n : ℕ, GgCl Z (gc n)
  | 0 => GgCl.phi (GgCl.small (gg_one_lt_of_SC hZ)) (ph_cl_Om1_one hZ)
  | n + 1 => GgCl.phi (gc_cl hZ n) (GgCl.zero hZ.1)

theorem gc_Om1_le : ∀ n : ℕ, Om 1 ≤ gc n
  | 0 => le_self_add.trans (right_le_veblen _ _)
  | n + 1 => (gc_Om1_le n).trans (left_le_veblen _ _)

theorem gc_lt_Gam : ∀ n : ℕ, gc n < ggGam
  | 0 => ggGam_spec.1.2 1 (gg_one_lt_of_SC ggGam_spec.1) _ (ggGam_spec.1.add_one_lt ggGam_spec.2)
  | n + 1 => ggGam_spec.1.2 _ (gc_lt_Gam n) _ ggGam_spec.1.1

/-- **`Θ_y(gc n) = gT n y`** for a strongly critical `y < Ω₁`. -/
theorem gcTh {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ∀ n : ℕ, ggTh y (gc n) = gT n y
  | 0 => by
      show ggTh y (veblen 1 (Om 1 + 1)) = eN y
      rw [phTh_phi hy _ (GgCl.small (gg_one_lt_of_SC hy)) _ (ph_cl_Om1_one hy), ggTh_small (gg_one_lt_of_SC hy).le,
        phTh_Om1_one hy hy1, lveSC_eN hy]
  | n + 1 => by
      have hyE : InE y := gg_SC_eps hy
      have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
      show ggTh y (veblen (gc n) 0) = gT (n + 1) y
      rw [phTh_phi hy _ (gc_cl hy n) _ (GgCl.zero hy.1), gcTh hy hy1 n, phTh_zero]
      apply le_antisymm
      · obtain ⟨j, hj⟩ := lvg_top_P hyE hy1' n
        rw [← hj]
        exact (veblen_le_veblen_iff_right).2 zero_le
      · refine lvg_top_least hyE hy1' n (luP_veblen (gT n y) 0) ?_
        calc y = veblen y 0 := hy.veblen_zero.symm
          _ < veblen (gT n y) 0 := veblen_zero_lt_veblen_zero.2 (gT_facts hyE hy1' n).2.1

end Codes

section Poly

variable {Z : Ordinal.{0}}

/-- **`lvgSys n` has terms for every code below `gc n`.** -/
theorem lvgPoly : ∀ n : ℕ, GgPoly (lvgSys n) (gc n) := by
  intro n
  induction n with
  | zero =>
    refine phPoly_of_SC fun Z hZ _ => ?_
    intro c hc hcB
    obtain ⟨l, hl, -, hlv⟩ := levPoly hZ c hc hcB
    refine ⟨levToG l, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := hlv y hy hy1 hZy
    exact ⟨⟨levToG_cb l hl c1, by rw [levToG_stage l hl]⟩, by rw [← v1]; exact levToG_val l hl y⟩
  | succ n ihn =>
    refine phPoly_of_SC fun Z hZ hZ1 => ?_
    intro c
    induction c using WellFoundedLT.induction with
    | ind c IH =>
    intro hc hcB
    rcases lt_trichotomy c (Om 1) with hc1 | hc1 | hc1
    · have hcZ : c < Z := hc.lt_of_lt_Om1 hZ hc1
      exact ⟨LvGT.cst c, fun y _ _ hZy =>
        ⟨⟨lt_of_lt_of_le hcZ hZy, Nat.zero_le _⟩, by show c = ggTh y c; rw [ggTh_small (hcZ.le.trans hZy)]⟩⟩
    · subst hc1
      exact ⟨LvGT.bs, fun y hy hy1 _ => ⟨⟨trivial, Nat.zero_le _⟩, by show y = ggTh y (Om 1); rw [ggTh_Om1 hy hy1]⟩⟩
    have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hc1).ne'
    obtain ⟨hsub, hlog⟩ := ggDec hZ c hc
    have hw : GgCl Z (ω ^ log ω c) := GgCl.opow hZ.1 hlog
    have hwc : ω ^ log ω c ≤ c := opow_log_le_self ω hc0
    rcases hwc.lt_or_eq with hwc' | hwc'
    · have hr := hsub _ hw hwc
      have hcr : ω ^ log ω c + (c - ω ^ log ω c) = c := Ordinal.add_sub_cancel_of_le hwc
      have hrc : c - ω ^ log ω c < c := by
        rcases (Ordinal.sub_le_self c (ω ^ log ω c)).lt_or_eq with h | h
        · exact h
        · exfalso
          have h1 : ω ^ log ω c + c = c := by conv_rhs => rw [← hcr]
                                              rw [h]
          have h2 := add_eq_right_iff_mul_omega0_le.1 h1
          rw [← opow_succ] at h2
          exact absurd (lt_opow_succ_log_self one_lt_omega0 c) (not_lt.2 h2)
      obtain ⟨s1, hs1⟩ := IH _ hwc' hw (hwc'.trans hcB)
      obtain ⟨s2, hs2⟩ := IH _ hrc hr (hrc.trans hcB)
      refine ⟨LvGT.sm s1 s2, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs1 y hy hy1 hZy
      obtain ⟨c2, v2⟩ := hs2 y hy hy1 hZy
      refine ⟨⟨⟨c1.1, c2.1⟩, max_le c1.2 c2.2⟩, ?_⟩
      show (lvgSys (n + 1)).val s1 y + (lvgSys (n + 1)).val s2 y = _
      rw [v1, v2, ← ggTh_add hy (hw.mono hZy), hcr]
    rcases (log_le_self ω c).lt_or_eq with hL | hL
    · obtain ⟨s, hs⟩ := IH _ hL hlog (hL.trans hcB)
      refine ⟨LvGT.pw s, fun y hy hy1 hZy => ?_⟩
      obtain ⟨c1, v1⟩ := hs y hy hy1 hZy
      refine ⟨c1, ?_⟩
      show ω ^ (lvgSys (n + 1)).val s y = _
      rw [v1, ← ggTh_opow hy (hlog.mono hZy), hwc']
    have hcE : ω ^ c = c := by conv_lhs => rw [← hL]
                               exact hwc'
    have hdec : veblen (invVeblen₁ c) (invVeblen₂ c) = c := by rw [veblen_invVeblen₁_invVeblen₂, hcE]
    have hb1 : invVeblen₂ c < c := by have := invVeblen₂_lt c; rwa [hcE] at this
    obtain ⟨ha, hb⟩ := phDec hZ.1 hc _ _ hdec hb1
    set a := invVeblen₁ c with hadef
    set b := invVeblen₂ c with hbdef
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, veblen_zero_apply] at hdec
      have e := hcE
      rw [← hdec] at e
      have e2 := (opow_right_inj one_lt_omega0).1 e
      rw [← hdec, e2] at hb1
      exact lt_irrefl _ hb1
    have hSC1 := ph_SC_Om1
    have haOO : a < gc n := by
      have hlt : veblen a b < veblen (gc n) 0 := by rw [hdec]; exact hcB
      rcases veblen_lt_veblen_iff.1 hlt with ⟨_, hb'⟩ | ⟨h', _⟩ | ⟨_, h'⟩
      · exact absurd hb' (not_lt.2 zero_le)
      · exact h'
      · exact absurd h' (not_lt.2 zero_le)
    have hbv : b < veblen a b := by rw [hdec]; exact hb1
    rcases lt_or_ge a (Om 1) with haO | haO
    · have haZ : a < Z := ha.lt_of_lt_Om1 hZ haO
      have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
      have hbO : Om 1 < b := by
        by_contra hle
        push Not at hle
        have h3 := (veblen_le_veblen_iff_right (o := a)).2 hle
        rw [hdec, hSC1.veblen_right haO] at h3
        exact absurd hc1 (not_lt.2 h3)
      obtain ⟨d, hd, hdb, hdθ⟩ := luIndCode hZ haZ hb hbO hbv
      obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
      refine ⟨LvGT.th0 a t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
      have hay : a < y := haZ.trans_le hZy
      refine ⟨⟨⟨ha1, hay, ct.1⟩, max_le (Nat.succ_le_succ (Nat.zero_le n)) ct.2⟩, ?_⟩
      show vt y (Om1 * a + (lvgSys (n + 1)).val t y) = ggTh y c
      have hby := hb.mono hZy
      have hThc : ggTh y c = veblen a (ggTh y b) := by
        rw [← hdec, luTh_veblen_lvl hy hay hby]
      have hyb : y < ggTh y b := by
        have := ggTh_lt (GgCl.om (Z := y)) hbO (y := y); rwa [ggTh_Om1 hy hy1] at this
      have hbP : ¬ LuP (a + 1) (ggTh y b) := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [luTh_veblen_lvl hy hay hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := LvGT.lvg_T (gg_SC_eps hy) hy1' t ct.1
      have hTv : (lvgSys (n + 1)).val t y ∈ Tset y ∧ (lvgSys (n + 1)).val t y < Om1 :=
        ⟨htT, htlt.trans (gT_facts (gg_SC_eps hy) hy1' _).2.2.1⟩
      have e1 : (lvgSys (n + 1)).val t y = luInd a y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      rw [hThc, luPhLev hy hy1' ha1 hay _ hyb hbP hTv.1 hTv.2]
    · -- a level code `Ω₁ ≤ a < ε_{Ω₁+1}`: the term `tl l t`
      obtain ⟨l, hlv⟩ := ihn Z a ha haOO
      have hl : ¬ LvGT.noB l := fun hn => by
        obtain ⟨c0, v0⟩ := hlv Z hZ hZ1 le_rfl
        have h1 := LvGT.noB_lt (gg_SC_eps hZ) l hn c0.1
        have h2 : Z ≤ ggTh Z a := by
          rcases haO.lt_or_eq with h | h
          · have := ggTh_lt (GgCl.om (Z := Z)) h (y := Z); rw [ggTh_Om1 hZ hZ1] at this; exact this.le
          · rw [← h, ggTh_Om1 hZ hZ1]
        exact absurd (v0 ▸ h1) (not_lt.2 h2)
      have hb0 : a = Om 1 → 0 < b := by
        intro hO
        rcases eq_or_ne b 0 with hb0 | hb0
        · exfalso
          rw [hO, hb0, hSC1.veblen_zero] at hdec
          rw [← hdec] at hc1
          exact lt_irrefl _ hc1
        · exact pos_iff_ne_zero.2 hb0
      obtain ⟨d, hd, hdb, hdθ⟩ := lveIndCode hZ ha haO hb hb0 hbv
      obtain ⟨t, ht⟩ := IH d (hdb.trans_lt hb1) hd ((hdb.trans_lt hb1).trans hcB)
      refine ⟨LvGT.tl l t, fun y hy hy1 hZy => ?_⟩
      obtain ⟨ct, vt'⟩ := ht y hy hy1 hZy
      obtain ⟨clc, clv⟩ := hlv y hy hy1 hZy
      have hyE : InE y := gg_SC_eps hy
      have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
      refine ⟨⟨⟨hl, clc.1, ct.1⟩, max_le (Nat.succ_le_succ clc.2) ct.2⟩, ?_⟩
      show vt y (Om1 * LvGT.val l y + (lvgSys (n + 1)).val t y) = ggTh y c
      have hby := hb.mono hZy
      have hThc : ggTh y c = veblen (ggTh y a) (ggTh y b) := by
        rw [← hdec, phTh_phi hy _ (ha.mono hZy) _ hby]
      have hyΘ : y ≤ ggTh y a := by
        rcases haO.lt_or_eq with h | h
        · have := ggTh_lt (GgCl.om (Z := y)) h (y := y); rw [ggTh_Om1 hy hy1] at this; exact this.le
        · rw [← h, ggTh_Om1 hy hy1]
      have hyb : y < veblen (ggTh y a) (ggTh y b) := by
        rcases haO.lt_or_eq with h | h
        · have h2 : y < ggTh y a := by
            have := ggTh_lt (GgCl.om (Z := y)) h (y := y); rwa [ggTh_Om1 hy hy1] at this
          calc y = veblen y 0 := hy.veblen_zero.symm
            _ < veblen (ggTh y a) 0 := veblen_zero_lt_veblen_zero.2 h2
            _ ≤ veblen (ggTh y a) (ggTh y b) := (veblen_le_veblen_iff_right).2 zero_le
        · rw [← h, ggTh_Om1 hy hy1]
          have hpos : 0 < ggTh y b := by
            have := ggTh_lt (GgCl.zero hy.1) (hb0 h.symm) (y := y); rwa [phTh_zero] at this
          calc y = veblen y 0 := hy.veblen_zero.symm
            _ < veblen y (ggTh y b) := (veblen_lt_veblen_iff_right).2 hpos
      have hbP : ¬ LuP (ggTh y a + 1) (ggTh y b) := by
        intro hP
        have h1 := ggTh_lt hby hbv
        rw [phTh_phi hy _ (ha.mono hZy) _ hby, luP_succ.1 hP] at h1
        exact lt_irrefl _ h1
      obtain ⟨htT, htlt⟩ := LvGT.lvg_T hyE hy1' t ct.1
      have hTv : (lvgSys (n + 1)).val t y ∈ Tset y ∧ (lvgSys (n + 1)).val t y < Om1 :=
        ⟨htT, htlt.trans (gT_facts hyE hy1' _).2.2.1⟩
      have e1 : (lvgSys (n + 1)).val t y = lvInd (ggTh y a) y (ggTh y b) := by rw [vt', hdθ y hy hy1 hZy]
      rw [e1] at hTv ⊢
      have hLT := (LvGT.lvg_T hyE hy1' l clc.1).1
      have hyL := LvGT.le_of_not_noB hyE hy1' l clc.1 hl
      have hL1 := LvGT.lvg_lt_Om1 hyE hy1' l clc.1
      have clv' : LvGT.val l y = ggTh y a := clv
      rw [clv'] at hLT hyL hL1
      have hβ1 : 1 ≤ ggTh y a := (lu_one_lt_E hyE).le.trans hyL
      have hβu : ∀ u, LuP (ggTh y a) u → y < u → ggTh y a < u := by
        intro u hPu hyu
        obtain ⟨j, hj⟩ := hPu
        refine lt_of_le_of_ne (hj ▸ left_le_veblen _ _) fun e => ?_
        have hP : LuP (ggTh y a) (ggTh y a) := ⟨j, hj.trans e.symm⟩
        have h1 := lvg_P_self hyE hy1' n (ggTh y a) (e ▸ hyu) hP
        have h2 : ggTh y a < gT n y := by
          have := ggTh_lt (ha.mono hZy) haOO (y := y); rwa [gcTh hy hy1 n] at this
        exact absurd h1 (not_le.2 h2)
      rw [clv', hThc, lvPhLev hy hy1' hβ1 hLT hL1 hβu _ hyb hbP hTv.1 hTv.2]

end Poly

/-! ## The frontier lies below `L(0)` -/

variable {S : InaccSeq.{0}}

/-- **The frontier of `lvgSys n`**: `Λ(lvgSys n) ≤ ι(ω^{gc n})`, `Λ⁺(lvgSys n) ≤ ι(ω^{gc n}·ω) < L(0)` and
`υ_{Λ⁺(lvgSys n)} < L(0)`. -/
theorem lvg_fr (n : ℕ) :
    (∀ k : ℕ, XtFr (lvgSys n) (iota S (ω ^ gc n * ((k : Ordinal.{0}) + 1))) ∧
      upsilon (iota S (ω ^ gc n * ((k : Ordinal.{0}) + 1))) = iota S (ω ^ gc n * ((k : Ordinal.{0}) + 1))) ∧
    xtLam (lvgSys n) ≤ iota S (ω ^ gc n) ∧ xtB1 (lvgSys n) ≤ iota S (ω ^ gc n * ω) ∧
    iota S (ω ^ gc n * ω) < Nc.ncL S 0 ∧ upsilon (xtB1 (lvgSys n)) < Nc.ncL S 0 :=
  phFrGen (gc_lt_Gam n) (phPolyR_of (lvgPoly n)) (fun _ hy hy1 => (gcTh hy hy1 n).symm) (fun _ hZ => gc_cl hZ n)
    (gc_Om1_le n)

/-- **Where the frontiers lie**: `ρ` of `Λ⁺(lvgSys n)` < `ρ` of `Λ(lvgSys (n+1))` < `ρ` of `Λ⁺(lvgSys (n+1))` <
`L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, and `Λ⁺(lvgSys (n+1)) < L(ω+1)`, unconditionally. -/
theorem lvg_fr_order (n k : ℕ) :
    upsilon (xtB1 (lvgSys n)) < upsilon (xtLam (lvgSys (n + 1))) ∧
    upsilon (xtLam (lvgSys (n + 1))) < upsilon (xtB1 (lvgSys (n + 1))) ∧
    upsilon (xtB1 (lvgSys (n + 1))) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 (lvgSys (n + 1)) < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  have hU := (lvg_fr (S := S) (n + 1)).2.2.2.2
  refine ⟨upsilon_normal.strictMono (lvgLam_gt n), upsilon_normal.strictMono (lvg_lamLtB1 (n + 1)), hU, h0, h1,
    h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hU.trans_le h0).trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
