import Googology.Trans.PoR.InaccPsi.R2.HoW

/-!
# HoOU: THE UNION OF AN `Ω₁`-INDEXED INCREASING FAMILY OF GATED DIGIT SYSTEMS

ONE generic form of the unions `Hn.hnQU` (over a pseudo-base) and `Hn.hnU` (over `G`): a family `D μ`, `μ < Ω₁`, of
`Hg.HgVD` systems, each extending the earlier ones, with bounds cofinal in `B`, with SMALL (a code of `D μ` with gate
below an `ε`-number `σ` lies in some `D μ'`, `μ' < σ`), and, at every base `x` above the gate `γ`, the members
`μ < x` have gate below `x`, base reading and bound field below `b(x)`, cofinal in `b(x)`; below the gate their
bound fields lie below `Zo(x)`.  Then the union is a gated digit system with the bound `B`, the gate `γ`, the base
reading `b(x)` and the bound field `evZ(b(x))` above `γ`, `Zo(x)` below.  The proofs are those of `Hn.hnQU` with the
members as data.

* `HoFam`, `hoN`, `hoN_R`, `hoN_g`, `hoN_small`;
* `hoOU` (**THE UNION**), `hoOU_R`, `hoOU_g`, `hoOU_B`, `hoOU_γ`, `hoOU_b`, `hoOU_Z`.

No new axiom.  New definitions: `HoFam`, `hoN`, `hoOU`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ho

open Googology.Trans.PoR.InaccPsi.R2.Hn Googology.Trans.PoR.InaccPsi.R2.Hl
open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk
open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **An `Ω₁`-indexed increasing family of gated digit systems with a union bound `B`, a gate `γ`, a base reading
`b` and a low field `Zo`.** -/
structure HoFam where
  D : Ordinal.{0} → HgVD
  B : Ordinal.{0}
  γ : Ordinal.{0}
  b : Ordinal.{0} → Ordinal.{0}
  Zo : Ordinal.{0} → Ordinal.{0}
  γ_lt : γ < Om1
  γ_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} B → γ < Z
  G_lt : gcG 0 < B
  B_E : InE B
  B_lt1 : B < gcG 1
  B_fix1 : veblen 1 B = B
  B_mem : ∀ (S : InaccSeq.{0}) (a b' : Ordinal.{0}), 0 < a → γ < b' → B ∈ S.CSet a b'
  DB_lt : ∀ μ, μ < Om1 → (D μ).B < B
  B_cof : ∀ c, c < B → ∃ μ, μ < Om1 ∧ c < (D μ).B
  ext : ∀ μ' μ, μ' ≤ μ → μ < Om1 → ∀ c x, c < (D μ').B → (D μ).R c x = (D μ').R c x ∧ (D μ).g c = (D μ').g c
  small : ∀ μ, μ < Om1 → ∀ c, c < (D μ).B → ∀ σ, InE σ → σ < Om1 → (D μ).g c < σ →
    ∃ μ', μ' < σ ∧ c < (D μ').B
  γD : ∀ x, InE x → x < Om1 → γ < x → ∀ μ, μ < x → (D μ).γ < x
  bD : ∀ x, InE x → x < Om1 → γ < x → ∀ μ, μ < x → (D μ).b x < b x
  ZD : ∀ x, InE x → x < Om1 → γ < x → ∀ μ, μ < x → (D μ).Z x ≤ b x
  b_cof : ∀ x, InE x → x < Om1 → γ < x → ∀ ν, ν < b x → ∃ μ, μ < x ∧ ν < (D μ).b x
  b_E : ∀ x, InE x → x < Om1 → γ < x → InE (b x)
  x_lt_b : ∀ x, InE x → x < Om1 → γ < x → x < b x
  b_fix1 : ∀ x, InE x → x < Om1 → γ < x → veblen 1 (b x) = b x
  b_lt1 : ∀ x, InE x → x < Om1 → γ < x → b x < gq 1 x
  b_pi : ∀ σ ρ, Bases σ ρ → γ < σ → b ρ ∈ TB ρ σ ∧ pi σ ρ (b ρ) = b σ
  Z_low : ∀ μ, μ < Om1 → ∀ x, InE x → x < Om1 → ¬ γ < x → (D μ).Z x ≤ Zo x
  Zo_fix : ∀ x, veblen 2 (Zo x) = Zo x
  Zo_G1 : ∀ x, InE x → x < Om1 → Zo x < gq 1 x

section Fam

variable (F : HoFam)

theorem hoB_lim : IsSuccLimit F.B := ev_isSuccLimit_of_inE F.B_E

/-- The first member containing `c`. -/
noncomputable def hoN (c : Ordinal.{0}) : Ordinal.{0} := sInf {μ | μ < Om1 ∧ c < (F.D μ).B}

theorem hoN_spec {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (F.D μ).B) :
    hoN F c ≤ μ ∧ hoN F c < Om1 ∧ c < (F.D (hoN F c)).B := by
  have hne : ({μ | μ < Om1 ∧ c < (F.D μ).B} : Set Ordinal.{0}).Nonempty := ⟨μ, hμ, hc⟩
  have hm := csInf_mem hne
  exact ⟨csInf_le' ⟨hμ, hc⟩, hm.1, hm.2⟩

theorem hoN_high {c : Ordinal.{0}} (hc : F.B ≤ c) : hoN F c = 0 := by
  unfold hoN
  have he : ({μ | μ < Om1 ∧ c < (F.D μ).B} : Set Ordinal.{0}) = ∅ := by
    ext μ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hμ hcμ
    exact absurd (hcμ.trans (F.DB_lt μ hμ)) (not_lt.2 hc)
  rw [he]; exact Ordinal.sInf_empty

theorem hoN_R {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (F.D μ).B) (x : Ordinal.{0}) :
    (F.D (hoN F c)).R c x = (F.D μ).R c x := by
  obtain ⟨h1, -, h3⟩ := hoN_spec F hμ hc
  exact (F.ext _ _ h1 hμ c x h3).1.symm

theorem hoN_g {c μ : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (F.D μ).B) :
    (F.D (hoN F c)).g c = (F.D μ).g c := by
  obtain ⟨h1, -, h3⟩ := hoN_spec F hμ hc
  exact (F.ext _ _ h1 hμ c 0 h3).2.symm

theorem hoN_R_succ (c x : Ordinal.{0}) :
    (F.D (hoN F (c + 1))).R (c + 1) x = (F.D (hoN F c)).R c x + 1 := by
  rcases lt_or_ge c F.B with h | h
  · obtain ⟨n, hn1, hn⟩ := F.B_cof _ ((hoB_lim F).add_one_lt h)
    rw [hoN_R F hn1 hn, hoN_R F hn1 ((lt_add_one c).trans hn), (F.D n).R_succ]
  · rw [hoN_high F h, hoN_high F (h.trans (le_self_add (a := c) (b := 1))), (F.D 0).R_succ]

theorem hoN_g_le_succ (c : Ordinal.{0}) : (F.D (hoN F c)).g c ≤ (F.D (hoN F (c + 1))).g (c + 1) := by
  rcases lt_or_ge c F.B with h | h
  · obtain ⟨n, hn1, hn⟩ := F.B_cof _ ((hoB_lim F).add_one_lt h)
    rw [hoN_g F hn1 hn, hoN_g F hn1 ((lt_add_one c).trans hn)]; exact (F.D n).g_le_succ c
  · rw [hoN_high F h, hoN_high F (h.trans (le_self_add (a := c) (b := 1)))]
    exact (F.D 0).g_le_succ c

theorem hoN_small {c σ : Ordinal.{0}} (hc : c < F.B) (hσ : InE σ) (hσ1 : σ < Om1)
    (hg : (F.D (hoN F c)).g c < σ) : ∃ μ, μ < σ ∧ c < (F.D μ).B := by
  obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
  rw [hoN_g F hn1 hn] at hg
  exact F.small n hn1 c hn σ hσ hσ1 hg

/-- **THE UNION OF THE FAMILY**: a gated digit system with the bound `B`, the gate `γ`, the base reading `b`. -/
noncomputable def hoOU : HgVD where
  B := F.B
  γ := F.γ
  γ_lt := F.γ_lt
  γ_cl := F.γ_cl
  γ_G := fun h => absurd h F.G_lt.ne'
  R := fun c x => (F.D (hoN F c)).R c x
  g := fun c => (F.D (hoN F c)).g c
  b := fun x => F.b x
  ba := fun x => F.b x
  ix := F.B
  Z := fun x => if F.γ < x then evZ (F.b x) else F.Zo x
  B_E := F.B_E
  G_le := F.G_lt.le
  B_lt1 := F.B_lt1
  B_ix := F.B_fix1.symm
  Z_fix := fun x _ _ => by
    split_ifs
    · exact epsilon_evZ _
    · exact hc_fix_down one_le_two (F.Zo_fix x)
  Z_G1 := fun x hx hx1 => by
    split_ifs with h
    · exact gw_evZ_lt1 hx hx1 (F.b_lt1 x hx hx1 h)
    · exact F.Zo_G1 x hx hx1
  ix_mem := fun S a b ha hb => F.B_mem S a b ha hb
  g_lt := fun c hc => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    rw [hoN_g F hn1 hn]; exact (F.D n).g_lt c hn
  g_zero := by rw [hoN_g F gv_Om1_pos (F.D 0).B_pos]; exact (F.D 0).g_zero
  g_nat := fun k => by
    rw [hoN_g F gv_Om1_pos ((F.D 0).nat_lt_B k)]; exact (F.D 0).g_nat k
  g_E := by rw [hoN_g F gv_Om1_pos (F.D 0).E_lt_B]; exact (F.D 0).g_E
  g_lowE := fun c hc => by
    rw [hoN_g F gv_Om1_pos (hc.trans (F.D 0).E_lt_B)]; exact (F.D 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ h
    rw [hoN_g F hn1 hn]; exact (F.D n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hxy
    have hx : x < (F.D n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (F.D n).B := lt_of_le_of_lt le_add_self hn
    show (F.D (hoN F (x + y))).g (x + y) < Z
    rw [hoN_g F hn1 hn]; rw [hoN_g F hn1 hx] at hgx; rw [hoN_g F hn1 hy] at hgy
    exact (F.D n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hy
    have hy' : y < (F.D n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    show (F.D (hoN F (ω ^ y))).g (ω ^ y) < Z
    rw [hoN_g F hn1 hn]; rw [hoN_g F hn1 hy'] at hg
    exact (F.D n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hcB
    show (F.D (hoN F c)).g c < Z
    rw [hoN_g F hn1 hn]
    exact (F.D n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (F.DB_lt n hn1).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    have hc' : c < (F.D n).B := (lt_add_one c).trans hn
    show (F.D (hoN F (c + 1))).g (c + 1) < Z
    rw [hoN_g F hn1 hn]; rw [hoN_g F hn1 hc'] at hg
    exact (F.D n).g_succ Z hZ c hn hg
  g_le_succ := hoN_g_le_succ F
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    rw [hoN_g F hn1 hn] at hg
    exact (F.D n).mem S a b ha c hn hg
  R_zero := fun x => by
    rw [hoN_R F gv_Om1_pos (F.D 0).B_pos]; exact (F.D 0).R_zero x
  R_nat := fun k x => by
    rw [hoN_R F gv_Om1_pos ((F.D 0).nat_lt_B k)]; exact (F.D 0).R_nat k x
  R_E := fun x => by rw [hoN_R F gv_Om1_pos (F.D 0).E_lt_B]; exact (F.D 0).R_E x
  R_succ := hoN_R_succ F
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    show 0 < (F.D (hoN F c)).R c x
    rw [hoN_R F hn1 hn]; rw [hoN_g F hn1 hn] at hg
    exact (F.D n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    show ω ≤ (F.D (hoN F c)).R c x
    rw [hoN_R F hn1 hn]; rw [hoN_g F hn1 hn] at hg
    exact (F.D n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 hγ c hc hg => by
    obtain ⟨μ, hμx, hcμ⟩ := hoN_small F hc hx hx1 hg
    have hμ1 : μ < Om1 := hμx.trans hx1
    show (F.D (hoN F c)).R c x < F.b x
    rw [hoN_R F hμ1 hcμ]; rw [hoN_g F hμ1 hcμ] at hg
    exact ((F.D μ).R_lt_Z x hx hx1 c hcμ hg).trans_le (F.ZD x hx hx1 hγ μ hμx)
  R_lt_Z := fun x hx hx1 c hc hg => by
    show (F.D (hoN F c)).R c x <
      if F.γ < x then evZ (F.b x) else F.Zo x
    split_ifs with hγ
    · obtain ⟨μ, hμx, hcμ⟩ := hoN_small F hc hx hx1 hg
      have hμ1 : μ < Om1 := hμx.trans hx1
      rw [hoN_R F hμ1 hcμ]; rw [hoN_g F hμ1 hcμ] at hg
      exact (((F.D μ).R_lt_Z x hx hx1 c hcμ hg).trans_le (F.ZD x hx hx1 hγ μ hμx)).trans
        (lt_evZ _)
    · obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
      rw [hoN_R F hn1 hn]; rw [hoN_g F hn1 hn] at hg
      have := (F.D n).R_lt_Z x hx hx1 c hn hg
      exact this.trans_le (F.Z_low n hn1 x hx hx1 hγ)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    have hd : d < (F.D n).B := hdc.trans hn
    show (F.D (hoN F d)).R d x < (F.D (hoN F c)).R c x
    rw [hoN_R F hn1 hn, hoN_R F hn1 hd]; rw [hoN_g F hn1 hn] at hgc
    rw [hoN_g F hn1 hd] at hgd
    exact (F.D n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    rw [hoN_R F hn1 hn] at hν; rw [hoN_g F hn1 hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (F.D n).cof x hx hx1 c hn hg ν hν
    have hd : d < (F.D n).B := hdc.trans hn
    exact ⟨d, hdc, by show (F.D (hoN F d)).g d < x; rw [hoN_g F hn1 hd]; exact hgd,
      by show ν ≤ (F.D (hoN F d)).R d x; rw [hoN_R F hn1 hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγ ν hν => by
    obtain ⟨μ, hμ, hνμ⟩ := F.b_cof x hx hx1 hγ ν hν
    have hμ1 : μ < Om1 := hμ.trans hx1
    obtain ⟨d, hd, hgd, hνd⟩ := (F.D μ).b_cof x hx hx1 (F.γD x hx hx1 hγ μ hμ) ν hνμ
    exact ⟨d, hd.trans (F.DB_lt μ hμ1),
      by show (F.D (hoN F d)).g d < x; rw [hoN_g F hμ1 hd]; exact hgd,
      by show ν < (F.D (hoN F d)).R d x; rw [hoN_R F hμ1 hd]; exact hνd⟩
  b_E := fun x hx hx1 hγ => F.b_E x hx hx1 hγ
  x_lt_b := fun x hx hx1 hγ => F.x_lt_b x hx hx1 hγ
  b_eN := fun x hx hx1 hγ => gz_eN_fix hx hx1 (F.b_fix1 x hx hx1 hγ) (F.x_lt_b x hx hx1 hγ) (F.b_lt1 x hx hx1 hγ)
  ba_lt := fun x hx hx1 hγ => F.b_lt1 x hx hx1 hγ
  b_Z := fun x _ _ hγ => by
    show eN (F.b x) < if F.γ < x then evZ (F.b x) else F.Zo x
    rw [if_pos hγ]; exact go_eN_lt_evZ (lt_evZ _)
  b_pi := fun σ ρ hB hγ => F.b_pi σ ρ hB hγ
  ba_pi := fun σ ρ hB hγ => F.b_pi σ ρ hB hγ
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    show (F.D (hoN F c)).R c ρ ∈ TB ρ σ ∧
      pi σ ρ ((F.D (hoN F c)).R c ρ) = (F.D (hoN F c)).R c σ
    rw [hoN_R F hn1 hn, hoN_R F hn1 hn]; rw [hoN_g F hn1 hn] at hg
    exact (F.D n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB hγ d hd hg P P' hat => by
    have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
    obtain ⟨μ, hμσ, hdμ⟩ := hoN_small F hd hB.1 hσ1 hg
    have hμ1 : μ < Om1 := hμσ.trans hσ1
    show ω ^ P * (F.D (hoN F d)).R d ρ ∈ TB ρ σ ∧
      pi σ ρ (ω ^ P * (F.D (hoN F d)).R d ρ) = ω ^ P' * (F.D (hoN F d)).R d σ
    rw [hoN_R F hμ1 hdμ, hoN_R F hμ1 hdμ]; rw [hoN_g F hμ1 hdμ] at hg
    exact (F.D μ).dig σ ρ hB (F.γD σ hB.1 hσ1 hγ μ hμσ) d hdμ hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans (F.bD ρ hB.2.1 hB.2.2.2 (hγ.trans hB.2.2.1) μ (hμσ.trans hB.2.2.1))))
  ld := fun c hl hc => by
    obtain ⟨n, hn1, hn⟩ := F.B_cof _ hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (F.D n).ld c hl hn
    have hcpn : cp < (F.D n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, ?_, fun x hx hx1 hg => ?_, fun σ ρ hB hg => hex σ ρ hB ?_⟩
    · show (F.D (hoN F cp)).g cp ≤ (F.D (hoN F c)).g c
      rw [hoN_g F hn1 hn, hoN_g F hn1 hcpn]; exact hgcp
    · have hg' : (F.D n).g c < x := by rw [← hoN_g F hn1 hn]; exact hg
      show (F.D (hoN F c)).R c x = _ ∧ _
      rw [hoN_R F hn1 hn, hoN_R F hn1 hcpn]
      exact hdec x hx hx1 hg'
    · rw [← hoN_g F hn1 hn]; exact hg


theorem hoOU_B : (hoOU F).B = F.B := rfl

theorem hoOU_γ : (hoOU F).γ = F.γ := rfl

theorem hoOU_b (x : Ordinal.{0}) : (hoOU F).b x = F.b x := rfl

theorem hoOU_Z (x : Ordinal.{0}) : (hoOU F).Z x = if F.γ < x then evZ (F.b x) else F.Zo x := rfl

theorem hoOU_R {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (F.D μ).B) (x : Ordinal.{0}) :
    (hoOU F).R c x = (F.D μ).R c x := hoN_R F hμ hc x

theorem hoOU_g {μ c : Ordinal.{0}} (hμ : μ < Om1) (hc : c < (F.D μ).B) : (hoOU F).g c = (F.D μ).g c :=
  hoN_g F hμ hc

end Fam

end Googology.Trans.PoR.InaccPsi.R2.Ho
