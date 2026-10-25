import Googology.Trans.PoR.InaccPsi.R2.GrStep

/-!
# A CHAIN OF GATED DIGIT SYSTEMS AND ITS UNION, constant indices up to `ζ_{Γ₀+1}`

Port of `R2.GqLim` to `GrD`.  A chain `GrCh` carries a base gate `γω < ζ_{Γ₀+1}` above the gates of its members and the
code-gate condition of its base `φ(1, ixω)`; its union `GrCh.lim` is a `GrD`.  A sequence `GrSeq` with bases
`φ(1, i(x) + δ_k)`, `δ_k → Δ`, offsets `s_k → T`, `T ≤ γω ≤ Δ < ζ_{Γ₀+1}` and `ixω = G + Δ` is a chain: the
condition of the base comes from `gr_cl_Bl` (`φ(1, G + Δ)` a code over `Z` ⇒ `Δ < Z`), the bounds at every
`ε`-number base `x` from `ζ_{Γ₀+1} ≤ ζ_{Γ_{x+1}+1} < gq 1 x` (`grK_le_evZ`, `grK_lt_gq1`; `Gq.gqK_le_lgG`), and
`T < φ(1, i(x) + Δ)` from `gr_lt_veb`.

* `gr_lt_veb` (**a constant `T ≤ Δ < ζ_{Γ₀+1}` lies below `φ(1, i + Δ)` when `Γ₀ ≤ φ(1, i)`**), `grK_lt_gcG1`;
* `GrCh`, `GrCh.N`, `GrCh.R`, `GrCh.g`, `GrCh.lim` (**THE GATED UNION**), `lim_R`, `lim_g`;
* `GrSeq`, `GrSeq.bω_eq` (`ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`), `GrSeq.toCh`.

No new axiom.  New definitions: `GrCh`, `GrCh.N`, `GrCh.R`, `GrCh.g`, `GrCh.lim`, `GrSeq`, `GrSeq.toCh`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gr

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gj
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Go
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## Constants below `ζ_{Γ₀+1}` -/

/-- **A constant index below `ζ_{Γ₀+1}` lies below `φ(1, i + Δ)`** whenever `Γ₀ ≤ φ(1, i)` and `T ≤ Δ < ζ_{Γ₀+1}`:
either `T < Γ₀`, or `i ≥ Γ₀` and `φ(1, i + Δ) ≤ Δ` would make `Δ = i + Δ` a fixed point of `ε` in `(Γ₀, ζ_{Γ₀+1})`. -/
theorem gr_lt_veb {i T Δ : Ordinal.{0}} (hi : gamma 0 ≤ veblen 1 i) (hTΔ : T ≤ Δ) (hΔ : Δ < grK) :
    T < veblen 1 (i + Δ) := by
  by_cases hT : T < gamma 0
  · exact hT.trans_le (hi.trans ((veblen_le_veblen_iff_right).2 le_self_add))
  push Not at hT
  have h1G : (1 : Ordinal.{0}) < gamma 0 := one_lt_omega0.trans (omega0_lt_gamma 0)
  have hiG : gamma 0 ≤ i := by
    by_contra h
    push Not at h
    exact absurd hi (not_le.2 ((Lq.lq_gamma_SC 0).2 1 h1G i h))
  refine hTΔ.trans_lt ?_
  by_contra hnot
  push Not at hnot
  have e1 : i + Δ ≤ Δ := (right_le_veblen 1 _).trans hnot
  have e2 : i + Δ = Δ := le_antisymm e1 le_add_self
  have e3 : Ordinal.epsilon Δ = Δ := by
    show veblen 1 Δ = Δ
    rw [e2] at hnot; exact le_antisymm hnot (right_le_veblen 1 Δ)
  have hi0 : 0 < i := gamma_pos.trans_le hiG
  have hiw : i * ω ≤ Δ := add_eq_right_iff_mul_omega0_le.1 e2
  have hlt : gamma 0 < Δ := hiG.trans_lt ((lt_mul_of_one_lt_right hi0 one_lt_omega0).trans_le hiw)
  exact absurd hΔ (not_lt.2 (evZ_le hlt e3))

theorem grK_lt_gcG1 : grK < gcG 1 :=
  grK_lt_Om1.trans ((Br.Om1_eq ▸ gcG_Om1_lt 1 : (Om1 : Ordinal.{0}) < gcG 1))

/-! ## A chain of gated digit systems -/

/-- **A chain of gated digit systems** with the base data of its union and its base gate `γω`. -/
structure GrCh where
  D : ℕ → GrD
  ixω : Ordinal.{0}
  bω : Ordinal.{0} → Ordinal.{0}
  baω : Ordinal.{0} → Ordinal.{0}
  γω : Ordinal.{0}
  γω_lt : γω < grK
  γ_cl : ∀ Z : Ordinal.{0}, SC Z → Z ≤ Om 1 → GxCl Z {gcG 0} (veblen 1 ixω) → γω < Z
  γ_le : ∀ n, (D n).γ ≤ γω
  coh_R : ∀ n c x, c < (D n).B → (D (n + 1)).R c x = (D n).R c x
  coh_g : ∀ n c, c < (D n).B → (D (n + 1)).g c = (D n).g c
  B_mono : ∀ n, (D n).B < (D (n + 1)).B
  B_lt : ∀ n, (D n).B < veblen 1 ixω
  B_cof : ∀ c, c < veblen 1 ixω → ∃ n, c < (D n).B
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → ixω ∈ S.CSet a b
  ix_lt : ixω < gcG 1
  cf_g : ∀ n, (D (n + 1)).g (D n).B ≤ max γω ε₀
  b_le : ∀ n x, InE x → x < Om1 → (D n).b x ≤ bω x
  b_sup : ∀ x, InE x → x < Om1 → ∀ ν, ν < bω x → ∃ n, ν < (D n).b x
  b_E : ∀ x, InE x → x < Om1 → InE (bω x)
  b_eN : ∀ x, InE x → x < Om1 → eN (bω x) = glA 1 (baω x) x
  ba_lt : ∀ x, InE x → x < Om1 → baω x < gq 1 x
  b_Z : ∀ x, InE x → x < Om1 → eN (bω x) < evZ (lgG x)
  b_pi : ∀ σ ρ, Bases σ ρ → γω < σ → bω ρ ∈ TB ρ σ ∧ pi σ ρ (bω ρ) = bω σ
  ba_pi : ∀ σ ρ, Bases σ ρ → γω < σ → baω ρ ∈ TB ρ σ ∧ pi σ ρ (baω ρ) = baω σ

namespace GrCh

variable (C : GrCh)

theorem B_mono' {n m : ℕ} (h : n ≤ m) : (C.D n).B ≤ (C.D m).B := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (C.B_mono m).le

theorem coh_R' {n m : ℕ} (h : n ≤ m) {c : Ordinal.{0}} (hc : c < (C.D n).B) (x : Ordinal.{0}) :
    (C.D m).R c x = (C.D n).R c x := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [C.coh_R m c x (hc.trans_le (C.B_mono' hnm)), ih]

theorem coh_g' {n m : ℕ} (h : n ≤ m) {c : Ordinal.{0}} (hc : c < (C.D n).B) : (C.D m).g c = (C.D n).g c := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => rw [C.coh_g m c (hc.trans_le (C.B_mono' hnm)), ih]

open Classical in
/-- The first system containing `c` (`0` above the union). -/
noncomputable def N (c : Ordinal.{0}) : ℕ := if h : ∃ n, c < (C.D n).B then Nat.find h else 0

theorem N_spec {c : Ordinal.{0}} {n : ℕ} (hc : c < (C.D n).B) : C.N c ≤ n ∧ c < (C.D (C.N c)).B := by
  classical
  have h : ∃ n, c < (C.D n).B := ⟨n, hc⟩
  unfold GrCh.N
  rw [dif_pos h]
  exact ⟨Nat.find_min' h hc, Nat.find_spec h⟩

theorem N_high {c : Ordinal.{0}} (hc : veblen 1 C.ixω ≤ c) : C.N c = 0 := by
  classical
  unfold GrCh.N
  rw [dif_neg]
  rintro ⟨n, hn⟩
  exact absurd (hn.trans (C.B_lt n)) (not_lt.2 hc)

/-- The reading of the union. -/
noncomputable def R (c x : Ordinal.{0}) : Ordinal.{0} := (C.D (C.N c)).R c x

/-- The gate of the union. -/
noncomputable def g (c : Ordinal.{0}) : Ordinal.{0} := (C.D (C.N c)).g c

theorem R_eq {c : Ordinal.{0}} {n : ℕ} (hc : c < (C.D n).B) (x : Ordinal.{0}) : C.R c x = (C.D n).R c x := by
  obtain ⟨h1, h2⟩ := C.N_spec hc
  exact (C.coh_R' h1 h2 x).symm

theorem g_eq {c : Ordinal.{0}} {n : ℕ} (hc : c < (C.D n).B) : C.g c = (C.D n).g c := by
  obtain ⟨h1, h2⟩ := C.N_spec hc
  exact (C.coh_g' h1 h2).symm

theorem B_lim' : IsSuccLimit (veblen 1 C.ixω) := ev_isSuccLimit_of_inE (omega0_opow_epsilon C.ixω)

theorem R_succ' (c x : Ordinal.{0}) : C.R (c + 1) x = C.R c x + 1 := by
  rcases lt_or_ge c (veblen 1 C.ixω) with h | h
  · obtain ⟨n, hn⟩ := C.B_cof _ (C.B_lim'.add_one_lt h)
    rw [C.R_eq hn, C.R_eq ((lt_add_one c).trans hn), (C.D n).R_succ]
  · unfold GrCh.R
    rw [C.N_high h, C.N_high (h.trans (le_self_add (a := c) (b := 1))), (C.D 0).R_succ]

theorem g_le_succ' (c : Ordinal.{0}) : C.g c ≤ C.g (c + 1) := by
  rcases lt_or_ge c (veblen 1 C.ixω) with h | h
  · obtain ⟨n, hn⟩ := C.B_cof _ (C.B_lim'.add_one_lt h)
    rw [C.g_eq hn, C.g_eq ((lt_add_one c).trans hn)]; exact (C.D n).g_le_succ c
  · unfold GrCh.g
    rw [C.N_high h, C.N_high (h.trans (le_self_add (a := c) (b := 1)))]; exact (C.D 0).g_le_succ c

theorem B0_lt : (C.D 0).B < veblen 1 C.ixω := C.B_lt 0

/-- **THE GATED UNION OF A CHAIN** (a gated digit system at the base `φ(1, ixω)`, base gate `γω`). -/
noncomputable def lim : GrD where
  B := veblen 1 C.ixω
  γ := C.γω
  γ_lt := C.γω_lt
  γ_cl := C.γ_cl
  γ_G := fun h => absurd h (ne_of_gt ((C.D 0).G_le.trans_lt C.B0_lt))
  R := C.R
  g := C.g
  b := C.bω
  ba := C.baω
  ix := C.ixω
  B_E := omega0_opow_epsilon C.ixω
  G_le := (C.D 0).G_le.trans C.B0_lt.le
  B_lt1 := (gcG_SC 1).2 1 (one_lt_omega0.trans (omega0_lt_inE (Low.opow_eq_self_of_SC (gcG_SC 1)))) _ C.ix_lt
  B_ix := rfl
  ix_mem := C.ix_mem
  g_lt := fun c hc => by
    obtain ⟨n, hn⟩ := C.B_cof c hc
    rw [C.g_eq hn]; exact (C.D n).g_lt c hn
  g_zero := by rw [C.g_eq (C.D 0).B_pos]; exact (C.D 0).g_zero
  g_nat := fun k => by rw [C.g_eq ((C.D 0).nat_lt_B k)]; exact (C.D 0).g_nat k
  g_E := by rw [C.g_eq (C.D 0).E_lt_B]; exact (C.D 0).g_E
  g_lowE := fun c hc => by rw [C.g_eq (hc.trans (C.D 0).E_lt_B)]; exact (C.D 0).g_lowE c hc
  g_G0 := fun h => by
    obtain ⟨n, hn⟩ := C.B_cof _ h
    rw [C.g_eq hn]; exact (C.D n).g_G0 hn
  g_add := fun Z hZ hωZ x y hxy hgx hgy => by
    obtain ⟨n, hn⟩ := C.B_cof _ hxy
    have hx : x < (C.D n).B := lt_of_le_of_lt le_self_add hn
    have hy : y < (C.D n).B := lt_of_le_of_lt le_add_self hn
    rw [C.g_eq hn]; rw [C.g_eq hx] at hgx; rw [C.g_eq hy] at hgy
    exact (C.D n).g_add Z hZ hωZ x y hn hgx hgy
  g_opow := fun Z hZw hωZ y hy hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hy
    have hy' : y < (C.D n).B := lt_of_le_of_lt (right_le_opow y one_lt_omega0) hn
    rw [C.g_eq hn]; rw [C.g_eq hy'] at hg
    exact (C.D n).g_opow Z hZw hωZ y hn hg
  code_gate := fun Z hZ1 hZ0 hZa hZp At hAt c hc hcB => by
    obtain ⟨n, hn⟩ := C.B_cof _ hcB
    rw [C.g_eq hn]
    exact (C.D n).code_gate Z hZ1 hZ0 hZa hZp At (fun s hs => (hAt s hs).imp_right
      (fun h => (C.B_lt n).le.trans h)) c hc hn
  g_succ := fun Z hZ c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    have hc' : c < (C.D n).B := (lt_add_one c).trans hn
    rw [C.g_eq hn]; rw [C.g_eq hc'] at hg
    exact (C.D n).g_succ Z hZ c hn hg
  g_le_succ := C.g_le_succ'
  mem := fun S a b ha c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.g_eq hn] at hg
    exact (C.D n).mem S a b ha c hn hg
  R_zero := fun x => by rw [C.R_eq (C.D 0).B_pos]; exact (C.D 0).R_zero x
  R_nat := fun k x => by rw [C.R_eq ((C.D 0).nat_lt_B k)]; exact (C.D 0).R_nat k x
  R_E := fun x => by rw [C.R_eq (C.D 0).E_lt_B]; exact (C.D 0).R_E x
  R_succ := C.R_succ'
  R_pos := fun x hx hx1 c hc0 hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).R_pos x hx hx1 c hc0 hn hg
  R_omega := fun x hx hx1 c hω hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).R_omega x hx hx1 c hω hn hg
  R_lt_b := fun x hx hx1 c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn]; rw [C.g_eq hn] at hg
    exact ((C.D n).R_lt_b x hx hx1 c hn hg).trans_le (C.b_le n x hx hx1)
  mono := fun x hx hx1 c hc d hdc hgc hgd => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    have hd : d < (C.D n).B := hdc.trans hn
    rw [C.R_eq hn, C.R_eq hd]; rw [C.g_eq hn] at hgc; rw [C.g_eq hd] at hgd
    exact (C.D n).mono x hx hx1 c hn d hdc hgc hgd
  cof := fun x hx hx1 c hc hg ν hν => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn] at hν; rw [C.g_eq hn] at hg
    obtain ⟨d, hdc, hgd, hνd⟩ := (C.D n).cof x hx hx1 c hn hg ν hν
    have hd : d < (C.D n).B := hdc.trans hn
    exact ⟨d, hdc, by rw [C.g_eq hd]; exact hgd, by rw [C.R_eq hd]; exact hνd⟩
  b_cof := fun x hx hx1 hγx ν hν => by
    obtain ⟨n, hn⟩ := C.b_sup x hx hx1 ν hν
    obtain ⟨d, hd, hgd, hνd⟩ := (C.D n).b_cof x hx hx1 ((C.γ_le n).trans_lt hγx) ν hn
    exact ⟨d, hd.trans (C.B_lt n), by rw [C.g_eq hd]; exact hgd, by rw [C.R_eq hd]; exact hνd⟩
  b_E := C.b_E
  x_lt_b := fun x hx hx1 => ((C.D 0).x_lt_b x hx hx1).trans_le (C.b_le 0 x hx hx1)
  b_eN := C.b_eN
  ba_lt := C.ba_lt
  b_Z := C.b_Z
  b_pi := C.b_pi
  ba_pi := C.ba_pi
  ex := fun σ ρ hB c hc hg => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    rw [C.R_eq hn, C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).ex σ ρ hB c hn hg
  dig := fun σ ρ hB d hd hg P P' hat => by
    obtain ⟨n, hn⟩ := C.B_cof _ hd
    rw [C.R_eq hn, C.R_eq hn]; rw [C.g_eq hn] at hg
    exact (C.D n).dig σ ρ hB d hn hg P P' (fun β hβ hβe =>
      hat β hβ (hβe.trans_le (C.b_le n ρ hB.2.1 hB.2.2.2)))
  ld := fun c hl hc => by
    obtain ⟨n, hn⟩ := C.B_cof _ hc
    obtain ⟨cp, lp, T, hcp, hgcp, hdec, hex⟩ := (C.D n).ld c hl hn
    have hcpn : cp < (C.D n).B := hcp.trans hn
    refine ⟨cp, lp, T, hcp, by rw [C.g_eq hn, C.g_eq hcpn]; exact hgcp, fun x hx hx1 hg => ?_,
      fun σ ρ hB hg => hex σ ρ hB (by rw [← C.g_eq hn]; exact hg)⟩
    rw [C.g_eq hn] at hg
    rw [C.R_eq hn, C.R_eq hcpn]
    exact hdec x hx hx1 hg
  cf := fun k => (C.D k).B
  cf_ge := fun k => (C.D k).E_lt_B.le
  cf_lt := C.B_lt
  cf_g := fun k => by rw [C.g_eq (C.B_mono k)]; exact C.cf_g k
  cf_mono := C.B_mono
  cf_cof := C.B_cof

theorem lim_B : C.lim.B = veblen 1 C.ixω := rfl

theorem lim_b : C.lim.b = C.bω := rfl

theorem lim_γ : C.lim.γ = C.γω := rfl

theorem lim_ix : C.lim.ix = C.ixω := rfl

theorem lim_ba : C.lim.ba = C.baω := rfl

/-- **The union extends every member of the chain** (readings). -/
theorem lim_R {n : ℕ} {c : Ordinal.{0}} (hc : c < (C.D n).B) (x : Ordinal.{0}) : C.lim.R c x = (C.D n).R c x :=
  C.R_eq hc x

/-- **The union extends every member of the chain** (gates). -/
theorem lim_g {n : ℕ} {c : Ordinal.{0}} (hc : c < (C.D n).B) : C.lim.g c = (C.D n).g c := C.g_eq hc

end GrCh

/-! ## A sequence of gated digit systems with a common index pattern -/

/-- **A sequence of gated digit systems** `D k` with bases `φ(1, i(x) + δ_k)`, offsets `a(x) + s_k`, bounds
`φ(1, ix0 + δ_k)`, `δ_k → Δ`, `s_k → T` (constants below `ζ_{Γ₀+1}`, `T ≤ γω ≤ Δ`), each extending
the previous. -/
structure GrSeq where
  D : ℕ → GrD
  ix0 : Ordinal.{0}
  i : Ordinal.{0} → Ordinal.{0}
  a : Ordinal.{0} → Ordinal.{0}
  δ : ℕ → Ordinal.{0}
  s : ℕ → Ordinal.{0}
  Δ : Ordinal.{0}
  T : Ordinal.{0}
  γω : Ordinal.{0}
  hix : ∀ k, (D k).ix = ix0 + δ k
  hb : ∀ k x, InE x → x < Om1 → (D k).b x = veblen 1 (i x + δ k)
  hba : ∀ k x, (D k).ba x = a x + s k
  coh_R : ∀ k c x, c < (D k).B → (D (k + 1)).R c x = (D k).R c x
  coh_g : ∀ k c, c < (D k).B → (D (k + 1)).g c = (D k).g c
  cf_g : ∀ k, (D (k + 1)).g (D k).B ≤ max γω ε₀
  γ_le : ∀ k, (D k).γ ≤ γω
  γω_lt : γω < grK
  γω_le : γω ≤ Δ
  T_le : T ≤ γω
  δ_mono : ∀ k, δ k < δ (k + 1)
  δ_lt : ∀ k, δ k < Δ
  δ_cof : ∀ t, t < Δ → ∃ k, t < δ k
  Δ_lim : IsSuccLimit Δ
  Δ_lt : Δ < grK
  s_lt : ∀ k, s k < T
  s_cof : ∀ t, t < T → ∃ k, t < s k
  T_lt : T < grK
  ix_mem : ∀ (S : InaccSeq.{0}) (a b : Ordinal.{0}), 0 < a → ix0 + Δ ∈ S.CSet a b
  ix0_lt : ix0 < gcG 1
  ix0_G : ix0 = gcG 0
  a_lt : ∀ x, InE x → x < Om1 → a x < gq 1 x
  a_pi : ∀ σ ρ, Bases σ ρ → γω < σ → a ρ ∈ TB ρ σ ∧ pi σ ρ (a ρ) = a σ
  i_big : ∀ x, InE x → x < Om1 → lgG x ≤ veblen 1 (i x)

namespace GrSeq

variable (Q : GrSeq)

theorem B_eq (k : ℕ) : (Q.D k).B = veblen 1 (Q.ix0 + Q.δ k) := by rw [(Q.D k).B_ix, Q.hix]

theorem Δ_ne : Q.Δ ≠ 0 := Q.Δ_lim.bot_lt.ne'

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem T_lt1 : Q.a x + Q.T < gq 1 x := by
  have hq := (gm1_facts hx hx1).2.2.2
  exact (inE_indec hq).add_lt (Q.a_lt x hx hx1) (Q.T_lt.trans (grK_lt_gq1 hx hx1))

theorem hval (k : ℕ) : glA 1 (Q.a x + Q.s k) x = veblen 1 (Q.i x + Q.δ k + 1) := by
  rw [← Q.hba, ← (Q.D k).b_eN x hx hx1, Q.hb k x hx hx1, go_eN_veb]

/-- **The base of the union**: `ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`. -/
theorem bω_eq : glA 1 (Q.a x + Q.T) x = veblen 1 (Q.i x + Q.Δ) := by
  have hF : IsSuccLimit (Q.i x + Q.Δ) := isSuccLimit_add _ Q.Δ_lim
  refine go_glA_sup hx hx1 (s := fun k => Q.a x + Q.s k) (f := fun k => Q.i x + Q.δ k + 1) (Q.T_lt1 hx hx1)
    (fun k => (add_lt_add_iff_left _).2 (Q.s_lt k)) (fun σ hσ => ?_) (fun k => ?_) (fun σ hσ => ?_) hF ?_
    (fun k => Q.hval hx hx1 k)
  · exact go_lt_add_sup (lt_of_le_of_lt zero_le (Q.s_lt 0)).ne' Q.s_cof hσ
  · show Q.i x + Q.δ k + 1 < Q.i x + Q.Δ
    rw [add_assoc]; exact (add_lt_add_iff_left _).2 (Q.Δ_lim.add_one_lt (Q.δ_lt k))
  · obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof hσ
    exact ⟨k, hk.trans (lt_add_one _)⟩
  · have h0 := Q.hval hx hx1 0
    have hT0 : Q.a x + Q.s 0 < gq 1 x := ((add_lt_add_iff_left _).2 (Q.s_lt 0)).trans (Q.T_lt1 hx hx1)
    obtain ⟨hT0T, hT01⟩ := gm1_T hx hx1 hT0
    obtain ⟨h1T, h11⟩ := gl_one_T hx hx1
    have ha : Q.a x < veblen 1 (Q.i x + Q.Δ) := by
      have h1 := (glA_facts hx hx1 le_rfl h1T h11 hT0T hT01).2.2.2.2.2
      rw [h0] at h1
      refine (le_self_add.trans_lt h1).trans ((isNormal_veblen 1).strictMono ?_)
      rw [add_assoc]; exact (add_lt_add_iff_left _).2 (Q.Δ_lim.add_one_lt (Q.δ_lt 0))
    have hTb : Q.T < veblen 1 (Q.i x + Q.Δ) :=
      gr_lt_veb ((gqK_le_lgG hx hx1).trans (Q.i_big x hx hx1)) (Q.T_le.trans Q.γω_le) Q.Δ_lt
    exact (inE_indec (omega0_opow_epsilon _)).add_lt ha hTb

end Base

/-- **THE CHAIN OF A SEQUENCE**: base `ϑˣ(Ω₁ + a(x) + T) = φ(1, i(x) + Δ)`, bound `φ(1, ix0 + Δ)`, base gate `γω`. -/
noncomputable def toCh : GrCh where
  D := Q.D
  ixω := Q.ix0 + Q.Δ
  bω := fun x => glA 1 (Q.a x + Q.T) x
  baω := fun x => Q.a x + Q.T + 1
  γω := Q.γω
  γω_lt := Q.γω_lt
  γ_cl := fun Z hZ hZ1 h => Q.γω_le.trans_lt (gr_cl_Bl hZ hZ1 Q.Δ_ne (Q.Δ_lt.trans grK_lt_Om1')
    (by have h' := h; rw [Q.ix0_G] at h'; exact h'))
  γ_le := Q.γ_le
  coh_R := Q.coh_R
  coh_g := Q.coh_g
  B_mono := fun k => by
    rw [Q.B_eq, Q.B_eq]
    exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (Q.δ_mono k))
  B_lt := fun k => by
    rw [Q.B_eq]; exact (isNormal_veblen 1).strictMono ((add_lt_add_iff_left _).2 (Q.δ_lt k))
  B_cof := fun c hc => by
    obtain ⟨t, ht, hct⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ Q.Δ_lim)).1 hc
    obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof ht
    exact ⟨k, by rw [Q.B_eq]; exact hct.trans ((isNormal_veblen 1).strictMono hk)⟩
  ix_mem := Q.ix_mem
  ix_lt := by
    have hE : InE (gcG 1) := Low.opow_eq_self_of_SC (gcG_SC 1)
    exact (inE_indec hE).add_lt Q.ix0_lt (Q.Δ_lt.trans grK_lt_gcG1)
  cf_g := Q.cf_g
  b_le := fun k x hx hx1 => by
    rw [Q.hb k x hx hx1, Q.bω_eq hx hx1]
    exact (isNormal_veblen 1).monotone ((add_le_add_iff_left _).2 (Q.δ_lt k).le)
  b_sup := fun x hx hx1 ν hν => by
    rw [Q.bω_eq hx hx1] at hν
    obtain ⟨t, ht, hνt⟩ := ((isNormal_veblen 1).lt_iff_exists_lt (isSuccLimit_add _ Q.Δ_lim)).1 hν
    obtain ⟨k, hk⟩ := go_lt_add_sup Q.Δ_ne Q.δ_cof ht
    exact ⟨k, by rw [Q.hb k x hx hx1]; exact hνt.trans ((isNormal_veblen 1).strictMono hk)⟩
  b_E := fun x hx hx1 => by rw [Q.bω_eq hx hx1]; exact omega0_opow_epsilon _
  b_eN := fun x hx hx1 => by
    obtain ⟨hT, h1⟩ := gm1_T hx hx1 (Q.T_lt1 hx hx1)
    exact glA_eN_one hx hx1 hT h1
  ba_lt := fun x hx hx1 =>
    (ev_isSuccLimit_of_inE (gm1_facts hx hx1).2.2.2).add_one_lt (Q.T_lt1 hx hx1)
  b_Z := fun x hx hx1 => by
    refine go_eN_lt_evZ ?_
    rw [Q.bω_eq hx hx1]
    have hZ := evZ_E (lgG x)
    have hi : Q.i x < evZ (lgG x) := by
      have h0 := (Q.D 0).b_Z x hx hx1
      rw [Q.hb 0 x hx hx1] at h0
      exact (le_self_add.trans (right_le_veblen 1 _)).trans_lt ((lt_eN _).trans h0)
    have hiΔ : Q.i x + Q.Δ < evZ (lgG x) :=
      (inE_indec hZ).add_lt hi (Q.Δ_lt.trans_le (grK_le_evZ hx hx1))
    have := (isNormal_veblen 1).strictMono hiΔ
    rwa [show veblen 1 (evZ (lgG x)) = evZ (lgG x) from epsilon_evZ _] at this
  b_pi := fun σ ρ hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hTσ : Q.T < σ := Q.T_le.trans_lt hγ
    obtain ⟨g1, g2⟩ := Q.a_pi σ ρ hB hγ
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hTσ)
    obtain ⟨o1, o2⟩ := one_TB hB
    have h := glA_pi hB o1 (gl_one_T hB.2.1 hρ1).2 s1 (gm1_T hB.2.1 hρ1 (Q.T_lt1 hB.2.1 hρ1)).2
    rw [o2, s2, g2, pi_lt hB hTσ] at h
    exact h
  ba_pi := fun σ ρ hB hγ => by
    have hTσ : Q.T < σ := Q.T_le.trans_lt hγ
    obtain ⟨g1, g2⟩ := Q.a_pi σ ρ hB hγ
    obtain ⟨s1, s2⟩ := pi_add hB g1 (mem_TB_of_lt hB hTσ)
    obtain ⟨o1, o2⟩ := one_TB hB
    obtain ⟨t1, t2⟩ := pi_add hB s1 o1
    exact ⟨t1, by rw [t2, s2, g2, o2, pi_lt hB hTσ]⟩

theorem toCh_D : Q.toCh.D = Q.D := rfl

theorem toCh_lim_ix : Q.toCh.lim.ix = Q.ix0 + Q.Δ := rfl

theorem toCh_lim_γ : Q.toCh.lim.γ = Q.γω := rfl

theorem toCh_lim_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) :
    Q.toCh.lim.b x = veblen 1 (Q.i x + Q.Δ) := Q.bω_eq hx hx1

theorem toCh_lim_ba (x : Ordinal.{0}) : Q.toCh.lim.ba x = Q.a x + Q.T + 1 := rfl

end GrSeq

end Googology.Trans.PoR.InaccPsi.R2.Gr
