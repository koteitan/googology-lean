import Googology.Trans.PoR.InaccPsi.R2.PhUni
import Googology.Trans.PoR.InaccPsi.R2.LyEpR

/-!
# `Ly.lyEB` has terms for every code below the code `ε_{phB+1} = φ(1, phB + 1)` of its top

`phEB = φ(1, phB + 1)`, `Θ_y(phEB) = ε_{B(y)+1} = eN(B(y))` (`phTh_EB`).  The terms of `lyEB` are
`Σ ω^{B(x) + dᵢ(x)}·kᵢ + s(x)` with exponent terms `dᵢ` of `Ly.LyTm` decreasing at every `υ`-point base.

* `phLyTm` (**`LyTm` has terms for every code below `phEB`**: constants and `φ(n, ·)`-terms below `phB` from
  `phPoly_vz`, the atom `B` for `phB`, sums and powers above it, since no `ε`-number lies in `(phB, phEB)`);
* `phLeGt_of_ref` (**the order of two exponent terms at one `υ`-point base `ρ` above their constants is their order at
  every `υ`-point base above their constants**, by Lemma EXACT `Ly.lyt_uni_lt`);
* `phCNFTm` (**the Cantor normal form of a code `g`, as an exponent list**: `ω^{B(y)}·Θ_y(g)` is the value
  `Σ ω^{B(y) + dᵢ(y)}·kᵢ`, decreasing exponents);
* `phPoly_lyEB` (**`PhPolyR lyEB phEB`**: `c = ω^{phB}·g + r`, the list of `g` and the `vzSys` term of `r`);
* `phLyE` (**THEOREM UNI for `lyEB` up to `phEB`**), `phLyEO`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ph

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ly

variable {S : InaccSeq.{0}} {Z : Ordinal.{0}}

/-- The code `φ(1, phB + 1)` of `ε_{B+1}`. -/
noncomputable def phEB : Ordinal.{0} := veblen 1 (phB + 1)

theorem ph_cl_EB (hZ : SC Z) : GgCl Z phEB :=
  GgCl.phi (GgCl.small (gg_one_lt_of_SC hZ)) (GgCl.add (ph_cl_B hZ) (GgCl.small (gg_one_lt_of_SC hZ)))

theorem ph_EB_eps : ω ^ phEB = phEB := gg_veblen_eps one_ne_zero

theorem ph_B_lt_EB : phB < phEB := (lt_add_one phB).trans_le (right_le_veblen _ _)

theorem ph_EB_lt_Gam : phEB < ggGam := ph_lt_Gam (ph_cl_EB ph_SC_Om1)

/-- The least `ε`-number above an `ε`-number `b` with `φ(1, b) = b` is `φ(1, b + 1)`. -/
theorem ph_eN_eq {b : Ordinal.{0}} (hb : veblen 1 b = b) : eN b = veblen 1 (b + 1) := by
  apply le_antisymm
  · exact eN_le ((lt_add_one b).trans_le (right_le_veblen _ _)) (gg_veblen_eps one_ne_zero)
  · have hE : InE (eN b) := eN_E b
    obtain ⟨γ, hγ⟩ := (vzP_one (a := eN b)).2 hE
    rw [Nat.cast_one] at hγ
    rw [← hγ]
    refine veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt ?_)
    by_contra hle
    push Not at hle
    have h2 := (veblen_le_veblen_iff_right (o := (1 : Ordinal.{0}))).2 hle
    rw [hb, hγ] at h2
    exact absurd (lt_eN b) (not_lt.2 h2)

/-- **`Θ_y(phEB) = ε_{B(y)+1}`**. -/
theorem phTh_EB {y : Ordinal.{0}} (hy : SC y) (hy1 : y < Om 1) : ggTh y phEB = eN (VzB y) := by
  unfold phEB
  have h1 := gg_one_lt_of_SC hy
  rw [phTh_phi hy _ (GgCl.small h1) _ (GgCl.add (ph_cl_B hy) (GgCl.small h1)), ggTh_small h1.le,
    ggTh_add hy (ph_cl_B hy), ggTh_small h1.le, phTh_B hy hy1]
  have hy1' : y < Om1 := by rw [ph_Om1_eq]; exact hy1
  obtain ⟨⟨γ, hγ⟩, -, -⟩ := vzB_omega (gg_SC_eps hy) hy1'
  have hfix : veblen 1 (VzB y) = VzB y := by
    rw [← hγ]; exact veblen_veblen_of_lt (one_lt_omega0) γ
  exact (ph_eN_eq hfix).symm

/-- **`LyTm` has terms for every code below `phEB`.** -/
theorem phLyTm (hZ : SC Z) : ∀ d, GgCl Z d → d < phEB →
    ∃ t : LyTm, ∀ y, SC y → y < Om 1 → Z ≤ y → t.CBt y ∧ t.val y = ggTh y d := by
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hd hdE
  rcases lt_trichotomy d phB with h | h | h
  · obtain ⟨s, hs⟩ := phPoly_vz Z d hd h
    exact ⟨LyTm.vz s, fun y hy hy1 hZy => hs y hy hy1 hZy⟩
  · subst h
    exact ⟨LyTm.bB, fun y hy hy1 _ => ⟨trivial, (phTh_B hy hy1).symm⟩⟩
  have hd0 : d ≠ 0 := (lt_of_le_of_lt zero_le h).ne'
  obtain ⟨hsub, hlog⟩ := ggDec hZ d hd
  have hw : GgCl Z (ω ^ log ω d) := GgCl.opow hZ.1 hlog
  have hwd : ω ^ log ω d ≤ d := opow_log_le_self ω hd0
  rcases hwd.lt_or_eq with hwd' | hwd'
  · have hr := hsub _ hw hwd
    have hdr : ω ^ log ω d + (d - ω ^ log ω d) = d := Ordinal.add_sub_cancel_of_le hwd
    have hrd := ph_sub_log_lt hd0
    obtain ⟨t1, ht1⟩ := IH _ hwd' hw (hwd'.trans hdE)
    obtain ⟨t2, ht2⟩ := IH _ hrd hr (hrd.trans hdE)
    refine ⟨LyTm.sm t1 t2, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := ht1 y hy hy1 hZy
    obtain ⟨c2, v2⟩ := ht2 y hy hy1 hZy
    refine ⟨⟨c1, c2⟩, ?_⟩
    rw [LyTm.val_sm, v1, v2, ← ggTh_add hy (hw.mono hZy), hdr]
  rcases (log_le_self ω d).lt_or_eq with hL | hL
  · obtain ⟨t, ht⟩ := IH _ hL hlog (hL.trans hdE)
    refine ⟨LyTm.pw t, fun y hy hy1 hZy => ?_⟩
    obtain ⟨c1, v1⟩ := ht y hy hy1 hZy
    refine ⟨c1, ?_⟩
    rw [LyTm.val_pw, v1, ← ggTh_opow hy (hlog.mono hZy), hwd']
  -- `d` would be an `ε`-number in `(phB, phEB)`
  exfalso
  have hdE' : ω ^ d = d := by conv_lhs => rw [← hL]
                              exact hwd'
  obtain ⟨γ, hγ⟩ := (vzP_one (a := d)).2 hdE'
  rw [Nat.cast_one] at hγ
  have hBfix : veblen 1 phB = phB := veblen_veblen_of_lt one_lt_omega0 _
  have hγB : phB < γ := by
    by_contra hle
    push Not at hle
    have h2 := (veblen_le_veblen_iff_right (o := (1 : Ordinal.{0}))).2 hle
    rw [hBfix, hγ] at h2
    exact absurd h (not_lt.2 h2)
  have h3 := (veblen_le_veblen_iff_right (o := (1 : Ordinal.{0}))).2 (Order.add_one_le_of_lt hγB)
  rw [hγ] at h3
  exact absurd hdE (not_lt.2 h3)

/-- **The order of two exponent terms at one `υ`-point base above their constants is their order at every
`υ`-point base above their constants.** -/
theorem phLeGt_of_ref {t u : LyTm} {k k' ρ : Ordinal.{0}} (hρU : UpsPt ρ) (hρ1 : ρ < Om1) (ht : t.CBt ρ)
    (hu : u.CBt ρ) (hlt : u.val ρ < t.val ρ) : LeGt (t, k) (u, k') := by
  intro y hyU hy1 hct hcu
  have hty : t.CBt y := LyTm.cbt_iff t ρ y ht hct
  have huy : u.CBt y := LyTm.cbt_iff u ρ y hu hcu
  rcases lt_trichotomy y ρ with h | rfl | h
  · exact (lyt_uni_lt hyU hρU ⟨upsPt_inE hyU, upsPt_inE hρU, h, hρ1⟩ huy hty).1 hlt
  · exact hlt
  · exact (lyt_uni_lt hρU hyU ⟨upsPt_inE hρU, upsPt_inE hyU, h, hy1⟩ hu ht).2 hlt

/-- **The Cantor normal form of a code as an exponent list.** -/
theorem phCNFTm (hZ : SC Z) {ρ : Ordinal.{0}} (hρU : UpsPt ρ) (hρS : SC ρ) (hρ1 : ρ < Om 1) (hZρ : Z ≤ ρ) :
    ∀ g, GgCl Z g → ∀ U, U ≤ phEB → g < ω ^ U →
      ∃ ps : List (LyTm × Ordinal.{0}), ps.Pairwise LeGt ∧
        (∀ q ∈ ps, (∃ d, GgCl Z d ∧ d < U ∧ ∀ y, SC y → y < Om 1 → Z ≤ y → q.1.CBt y ∧ q.1.val y = ggTh y d) ∧
          0 < q.2 ∧ q.2 < ω) ∧
        ∀ y, SC y → y < Om 1 → Z ≤ y → leSum vzLay y ps = ω ^ VzB y * ggTh y g := by
  have hρ1' : ρ < Om1 := by rw [ph_Om1_eq]; exact hρ1
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg U hU hgU
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨[], List.Pairwise.nil, fun q hq => absurd hq (List.not_mem_nil), fun y _ _ _ => by
      rw [leSum_nil, phTh_zero, mul_zero]⟩
  obtain ⟨hsub, hlog⟩ := ggDec hZ g hg
  set L := log ω g with hLdef
  have hLU : L < U := (lt_opow_iff_log_lt one_lt_omega0 hg0).1 hgU
  have hT0 : ω ^ L ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hk : g / ω ^ L < ω := by
    refine (Ordinal.lt_mul_iff_div_lt hT0).1 ?_
    have := lt_opow_succ_log_self one_lt_omega0 g
    rwa [opow_succ] at this
  obtain ⟨n, hn⟩ := lt_omega0.1 hk
  have hn0 : 0 < n := by
    have h1 : (1 : Ordinal.{0}) ≤ g / ω ^ L :=
      (Ordinal.mul_le_iff_le_div hT0).1 (by rw [mul_one]; exact opow_log_le_self ω hg0)
    rw [hn] at h1; exact_mod_cast h1
  have hgdec : ω ^ L * n + g % ω ^ L = g := by rw [← hn]; exact div_add_mod g _
  have hwn : GgCl Z (ω ^ L * n) := GgCl.mul_nat hZ.1 (GgCl.opow hZ.1 hlog) n
  have hr : GgCl Z (g % ω ^ L) := by
    have := hsub _ hwn (by rw [← hgdec]; exact le_self_add)
    rwa [Ordinal.sub_eq_of_add_eq hgdec] at this
  have hrL : g % ω ^ L < ω ^ L := mod_lt g hT0
  have hrg : g % ω ^ L < g := hrL.trans_le (opow_log_le_self ω hg0)
  obtain ⟨ps, hpw, hps, hsum⟩ := IH _ hrg hr L (hLU.le.trans hU) hrL
  obtain ⟨t, ht⟩ := phLyTm hZ L hlog (hLU.trans_le hU)
  obtain ⟨htρ, htv⟩ := ht ρ hρS hρ1 hZρ
  refine ⟨(t, (n : Ordinal.{0})) :: ps, List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩, fun q hq => ?_,
    fun y hy hy1 hZy => ?_⟩
  · obtain ⟨⟨d, hd, hdL, hdv⟩, -⟩ := hps q hq
    obtain ⟨hqρ, hqv⟩ := hdv ρ hρS hρ1 hZρ
    refine phLeGt_of_ref hρU hρ1' htρ hqρ ?_
    rw [hqv, htv]; exact ggTh_lt (hd.mono hZρ) hdL
  · rcases List.mem_cons.1 hq with rfl | hq'
    · exact ⟨⟨L, hlog, hLU, ht⟩, show (0 : Ordinal.{0}) < (n : Ordinal.{0}) by exact_mod_cast hn0,
        natCast_lt_omega0 n⟩
    · obtain ⟨⟨d, hd, hdL, hdv⟩, h2⟩ := hps q hq'
      exact ⟨⟨d, hd, hdL.trans hLU, hdv⟩, h2⟩
  · obtain ⟨-, htv'⟩ := ht y hy hy1 hZy
    have hly := hlog.mono hZy
    rw [leSum_cons, hsum y hy hy1 hZy]
    show ω ^ (VzB y + t.val y) * (n : Ordinal.{0}) + ω ^ VzB y * ggTh y (g % ω ^ L) = ω ^ VzB y * ggTh y g
    conv_rhs => rw [← hgdec]
    rw [ggTh_add hy (hwn.mono hZy), phTh_opow_mul hy hly _ (ph_cl_nat hy n), phTh_nat hy, htv', mul_add,
      opow_add, mul_assoc]

/-- **`lyEB` has terms for every code below `phEB`** (given a reference base). -/
theorem phPoly_lyEB : PhPolyR lyEB phEB := by
  refine phPolyR_of_SC fun Z hZ _ hρ c hc hcE => ?_
  obtain ⟨ρ, hρU, hρS, hρ1, hZρ⟩ := hρ
  obtain ⟨g, r, hg, hr, hrB, hcgr⟩ := phDivCode hZ (ph_cl_B hZ) c hc
  rw [ph_B_eps] at hrB
  obtain ⟨s, hs⟩ := phPoly_vz Z r hr hrB
  have hgc : g ≤ c := by
    rw [hcgr]
    exact (le_mul_right g (opow_pos _ omega0_pos)).trans le_self_add
  obtain ⟨ps, hpw, hps, hsum⟩ := phCNFTm hZ hρU hρS hρ1 hZρ g hg phEB le_rfl
    (by rw [ph_EB_eps]; exact hgc.trans_lt hcE)
  refine ⟨(ps, s), fun y hy hy1 hZy => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hZy
  refine ⟨⟨hpw, fun q hq => ⟨((hps q hq).1.choose_spec.2.2 y hy hy1 hZy).1, (hps q hq).2⟩, h1⟩, ?_⟩
  show leVal vzLay (ps, s) y = ggTh y c
  unfold leVal
  have hgy := hg.mono hZy
  rw [hsum y hy hy1 hZy, show vzLay.sys.val s y = vzSys.val s y from rfl, h2, hcgr,
    ggTh_add hy (ph_cl_opow_mul hy (ph_cl_B hy) g hgy), phTh_opow_mul hy (ph_cl_B hy) g hgy, phTh_B hy hy1]

/-- **THEOREM UNI for `lyEB` up to `phEB`.** -/
theorem phLyE {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phEB) : cdTheta S F (cdCode S F) = xtOrec lyEB F :=
  phUniTh ph_EB_lt_Gam.le phPoly_lyEB hF hfix hX he

theorem phLyEO {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hX : upsilon F < Pv S ηx)
    (he : cdExp (cdEta S F) ≤ phEB) : xtOrec lyEB F = ggTh F (cdExp (cdEta S F)) :=
  phUni ph_EB_lt_Gam.le phPoly_lyEB F ηx hF hfix hX he

end Googology.Trans.PoR.InaccPsi.R2.Ph
