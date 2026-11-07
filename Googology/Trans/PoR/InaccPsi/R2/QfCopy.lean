import Googology.Trans.PoR.InaccPsi.R2.QfMul
import Googology.Trans.PoR.InaccPsi.R2.QfSep
import Googology.Trans.PoR.InaccPsi.R2.QcUps

/-!
# QfCopy: THE COPY LEMMA FOR THE READINGS `Θ_E(z)` OF ALL CODES `z < Γ_{Ω₁+1}`

`Qc.qc_copy` for the codes below `ε_{Ω₁+1}`; here for every code over `E` (all below `Γ_{Ω₁+1}`), with the new case of
an `ε`-code `c = φ(a, b)`: in a copy `f` with `f(Θ_E c) < π(Θ_u c)` take `w` with `π(w) = f(Θ_E c)`
(`Gn.gn_pi_inv`); the source `Θ_E c ≤₁ Θ_E(qfRe c) = Θ_E c·(1+A) + e_A + logend(B)` (`Qf.qf_re`) gives, with the
product copy lemma `Qf.qf_mul` and the copy data of `a`, `e_a`, `logend(b)`, `w ≤₁ luL(w, Θ_u a) + logend(Θ_u b)`;
the copy data of `b` and of `φ(a, b₁)` (`b = b₁ + ω^{b₂}`) put `w` above `Θ_u b` and `φ(Θ_u a, Θ_u b₁)`, where
`Qf.qf_sep` (the separation below `φ(Θ_u a, Θ_u b)` over `u`) excludes it.  The membership `Θ_u c ∈ Tᵖ[f(ρ)]` is the
hypothesis `QfTBphi` (`Tᵖ[σ]` is closed under the countable values of `φ`).

* `QfTBphi`, `qf_cd_mono`, `qf_copy` (**THE COPY LEMMA FOR EVERY CODE**, given `QfTBphi`).

No new axiom.  New definition: `QfTBphi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.He Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **`Tᵖ[σ]` is closed under the countable values of `φ`** (a hypothesis). -/
def QfTBphi : Prop :=
  ∀ σ ρ a b : Ordinal.{0}, Bases σ ρ → a ∈ TB ρ σ → b ∈ TB ρ σ → veblen a b < Om1 → veblen a b ∈ TB ρ σ

/-- Copy data survive enlarging the base witness sets. -/
theorem qf_cd_mono {ρ δ E z : Ordinal.{0}} {W Z W₁ Z₁ : Finset Ordinal.{0}} (w₁ : WZ ρ δ W₁ Z₁) (hW : W ⊆ W₁)
    (hZ : Z ⊆ Z₁) (h : QfCD ρ δ E W Z z) : QfCD ρ δ E W₁ Z₁ z := by
  obtain ⟨W', Z', w', hW', hZ', hm, b⟩ := h
  refine ⟨W' ∪ W₁, Z' ∪ Z₁, w'.union w₁, Finset.subset_union_right, Finset.subset_union_right, ?_,
    fun A f hA hZA C u hu huT hu1 huz hπu => b A f (he_sub Finset.subset_union_left hA)
      (he_sub Finset.subset_union_left hZA) C u hu huT hu1 huz hπu⟩
  rcases Finset.mem_union.1 hm with h1 | h1
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)

/-- Inserting a sum `p + q` (`q < p`, `p ∈ W`, `q` zero or a witness) into the witness sets. -/
theorem qf_ins_sum {ρ δ p q : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hp : p ∈ W)
    (hq : q = 0 ∨ q ∈ W ∪ Z) (hqp : q < p) (hρp : ρ ≤ p) (hpqδ : p + q < δ) :
    ∃ W' : Finset Ordinal.{0}, WZ ρ δ W' Z ∧ W ⊆ W' ∧ p + q ∈ W' := by
  rcases eq_or_ne q 0 with h0 | h0
  · subst h0; rw [add_zero]; exact ⟨W, w, subset_refl _, hp⟩
  · have hq' : q ∈ W ∪ Z := hq.resolve_left h0
    have hq0 : 0 < q := pos_iff_ne_zero.2 h0
    exact ⟨insert (p + q) W, w.insW (hρp.trans le_self_add) hpqδ (Or.inr ⟨p, Finset.mem_union_left _ hp, q, hq',
      lt_add_of_pos_right _ hq0, hqp.trans_le le_self_add, rfl⟩), Finset.subset_insert _ _,
      Finset.mem_insert_self _ _⟩

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE `ε`-CODE CASE OF THE COPY LEMMA**: copy data for every code below an `ε`-code `z ∈ (Ω₁, Γ_{Ω₁+1})` give copy
data for `z` (given `QfTBphi`). -/
theorem qf_copy_eps (hTB : QfTBphi) {E z : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W)
    (hρE : ρ < E) (hES : SC E) (hE1 : E < Om1) (hET : E ∈ Tset ρ)
    (hthδ : ∀ y, GgCl E y → ggTh E y < δ) (hz : GgCl E z) (hz1 : Om 1 < z) (hzE : ω ^ z = z)
    (hCD : ∀ y, GgCl E y → y < z → QfCD ρ δ E W Z y) : QfCD ρ δ E W Z z := by
  classical
  have hE1' : E < Om 1 := qf_y1 hE1
  obtain ⟨hdec, hb1, haC, hbC, ha1, hap⟩ := qf_eps_dec hES hE1 hz hz1 hzE
  set a := invVeblen₁ z with hadef
  set b := invVeblen₂ z with hbdef
  set A := ggTh E a with hAdef
  set B := ggTh E b with hBdef
  set X := ggTh E z with hXdef
  have hX : X = veblen A B := by
    rw [hXdef]; conv_lhs => rw [← hdec]
    exact Ph.phTh_phi hES a haC b hbC
  have hXE : InE X := by rw [hX]; exact luP_E (by
    have := ggTh_mono (y := E) ha1; rwa [ggTh_small (gg_one_lt_of_SC hES).le] at this) (luP_veblen _ _)
  have hEX : E < X := (ggTh_Om1 hES hE1').symm.trans_lt (ggTh_lt GgCl.om hz1)
  have hρX : ρ < X := hρE.trans hEX
  have hXδ : X < δ := hthδ z hz
  have hδI := inE_indec h.δE
  have hXXδ : X + X < δ := hδI.add_lt hXδ hXδ
  have hzI : Indec z := by rw [← hzE]; exact indec_opow _
  have h1C : GgCl E (1 : Ordinal.{0}) := GgCl.small (gg_one_lt_of_SC hES)
  have h1aC : GgCl E (1 + a) := GgCl.add h1C haC
  have h1az : 1 + a < z := hzI.add_lt (lt_of_lt_of_le one_lt_omega0 (omega0_le_of_isSuccLimit
    (ev_isSuccLimit_of_inE hzE)) |>.trans_le le_rfl) hap
  have hTh1a : ggTh E (1 + a) = 1 + A := by rw [ggTh_add hES h1C, ggTh_small (gg_one_lt_of_SC hES).le]
  -- the base witness sets with `X` and `X + X`
  have w0 : WZ ρ δ (insert X W) Z := w.insW hρX.le hXδ (Or.inl (inE_indec hXE))
  have w0' : WZ ρ δ (insert (X + X) (insert X W)) Z := w0.insW (hρX.le.trans le_self_add) hXXδ
    (Or.inr ⟨X, Finset.mem_union_left _ (Finset.mem_insert_self _ _), X,
      Finset.mem_union_left _ (Finset.mem_insert_self _ _), lt_add_of_pos_right _ hXE.pos,
      lt_add_of_pos_right _ hXE.pos, rfl⟩)
  set W0 := insert (X + X) (insert X W) with hW0
  have hWW0 : W ⊆ W0 := fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hXW0 : X ∈ W0 := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hXXW0 : X + X ∈ W0 := Finset.mem_insert_self _ _
  have hCD0 : ∀ y, GgCl E y → y < z → QfCD ρ δ E W0 Z y := fun y hy hyz =>
    qf_cd_mono w0' hWW0 (subset_refl _) (hCD y hy hyz)
  -- the product `X·(1 + A)`
  obtain ⟨W1, Z1, w1, hW01, hZ1, hPW1, bP⟩ := qf_mul h w0' hXW0 hρX hXE hXδ hES hE1' hCD0
    (fun m hm hmz => by rw [hXdef]; exact ggTh_lt hm hmz) (1 + a) h1aC h1az (lt_of_lt_of_le zero_lt_one le_self_add)
  rw [hTh1a] at hPW1
  -- the parts
  have heC : GgCl E (hcE a) := qf_hcE_code hES haC
  have hez : hcE a < z := (hcE_le a).trans_lt hap
  have hlgC : GgCl E (lg b) := Qc.qc_lg_code hES hbC
  have hlgb : lg b ≤ b := by
    rcases eq_or_ne b 0 with h0 | h0
    · rw [h0, Qc.qc_lg_zero]
    · exact lg_le h0
  have hlgz : lg b < z := hlgb.trans_lt hb1
  obtain ⟨c1, hc1C, hc1z, hc10, hc1b⟩ : ∃ c1, GgCl E c1 ∧ c1 < z ∧ (b = 0 → c1 = a) ∧
      (b ≠ 0 → ∃ b1, b = b1 + ω ^ lg b ∧ GgCl E b1 ∧ ω ^ lg b ∣ b1 ∧ c1 = veblen a b1) := by
    rcases eq_or_ne b 0 with h0 | h0
    · exact ⟨a, haC, hap, fun _ => rfl, fun h' => absurd h0 h'⟩
    · obtain ⟨b1, b2, hbs, hb1b, hb1C, -, hb2l, hb2d⟩ := Qc.qc_split hES b hbC h0
      refine ⟨veblen a b1, GgCl.phi haC hb1C, ?_, fun h' => absurd h' h0,
        fun _ => ⟨b1, by rw [← hb2l]; exact hbs, hb1C, by rw [← hb2l]; exact hb2d, rfl⟩⟩
      rw [← hdec]; exact (veblen_lt_veblen_iff_right).2 hb1b
  obtain ⟨Wa, Za, wa, hWa, hZa, ma, ba⟩ := hCD0 a haC hap
  obtain ⟨Wb, Zb, wb, hWb, hZb, mb, bb⟩ := hCD0 b hbC hb1
  obtain ⟨We, Ze, we, hWe, hZe, me, be⟩ := hCD0 (hcE a) heC hez
  obtain ⟨Wl, Zl, wl, hWl, hZl, ml, bl⟩ := hCD0 (lg b) hlgC hlgz
  obtain ⟨Wc, Zc, wc, hWc, hZc, mc, bc⟩ := hCD0 c1 hc1C hc1z
  set WU := W1 ∪ Wa ∪ Wb ∪ We ∪ Wl ∪ Wc with hWU
  set ZU := Z1 ∪ Za ∪ Zb ∪ Ze ∪ Zl ∪ Zc with hZU
  have wU : WZ ρ δ WU ZU := ((((w1.union wa).union wb).union we).union wl).union wc
  have s1 : W1 ⊆ WU := fun x hx => by simp [hWU, hx]
  have sa : Wa ⊆ WU := fun x hx => by simp [hWU, hx]
  have sb : Wb ⊆ WU := fun x hx => by simp [hWU, hx]
  have se : We ⊆ WU := fun x hx => by simp [hWU, hx]
  have sl : Wl ⊆ WU := fun x hx => by simp [hWU, hx]
  have sc : Wc ⊆ WU := fun x hx => by simp [hWU, hx]
  have t1 : Z1 ⊆ ZU := fun x hx => by simp [hZU, hx]
  have ta : Za ⊆ ZU := fun x hx => by simp [hZU, hx]
  have tb : Zb ⊆ ZU := fun x hx => by simp [hZU, hx]
  have te : Ze ⊆ ZU := fun x hx => by simp [hZU, hx]
  have tl : Zl ⊆ ZU := fun x hx => by simp [hZU, hx]
  have tc : Zc ⊆ ZU := fun x hx => by simp [hZU, hx]
  have hmemU : ∀ {W' Z' : Finset Ordinal.{0}} {v : Ordinal.{0}}, W' ⊆ WU → Z' ⊆ ZU → v ∈ W' ∪ Z' → v ∈ WU ∪ ZU :=
    fun hW' hZ' hv => by
      rcases Finset.mem_union.1 hv with h1 | h1
      · exact Finset.mem_union_left _ (hW' h1)
      · exact Finset.mem_union_right _ (hZ' h1)
  -- the reach `R = X·(1+A) + e_A + logend(B)` of `X`
  set P := X * (1 + A) with hPdef
  set e := ggTh E (hcE a) with hedef
  set g := ggTh E (lg b) with hgdef
  have hXP : X ≤ P := le_mul_of_one_le_right' le_self_add
  have heX : e < X := ggTh_lt heC hez
  have hgX : g < X := ggTh_lt hlgC hlgz
  have hRth : ggTh E (qfRe z) = P + e + g := by
    unfold qfRe
    rw [← hadef, ← hbdef]
    have hpa : GgCl E (z * (1 + a)) := by
      have := Ph.ph_cl_opow_mul hES hz (1 + a) h1aC; rwa [hzE] at this
    rw [ggTh_add hES (GgCl.add hpa heC), ggTh_add hES hpa]
    have e1 : ggTh E (z * (1 + a)) = P := by
      have := Ph.phTh_opow_mul hES hz (1 + a) h1aC
      rw [hzE, hTh1a, ← ggTh_opow hES hz, hzE] at this
      exact this
    rw [e1]
  obtain ⟨hReC, hL⟩ := qf_re hES hE1 hz hz1 hzE
  rw [hRth] at hL
  have hRδ : P + e + g < δ := by rw [← hRth]; exact hthδ _ hReC
  have hPeδ : P + e < δ := (le_self_add).trans_lt hRδ
  have hPW : P ∈ WU := s1 hPW1
  obtain ⟨W2, w2, hU2, hSW2⟩ := qf_ins_sum wU hPW (Or.inr (hmemU se te me)) (heX.trans_le hXP)
    (hρX.le.trans hXP) hPeδ
  have hgW2 : g = 0 ∨ g ∈ W2 ∪ ZU := by
    right
    rcases Finset.mem_union.1 (hmemU sl tl ml) with h1 | h1
    · exact Finset.mem_union_left _ (hU2 h1)
    · exact Finset.mem_union_right _ h1
  obtain ⟨W3, w3, h23, hRW3⟩ := qf_ins_sum w2 hSW2 hgW2 ((hgX.trans_le hXP).trans_le le_self_add)
    ((hρX.le.trans hXP).trans le_self_add) hRδ
  have hsrc : le1 X (P + e + g) := (h.lowδ _ _ hρX hRδ.le).2 hL.1
  have hW3 : W ⊆ W3 := fun x hx => h23 (hU2 (s1 (hW01 (hWW0 hx))))
  refine ⟨W3, ZU, w3, hW3, fun x hx => t1 (hZ1 hx), ?_, fun As f hA hZA C u hu huT hu1 huz hπu => ?_⟩
  · exact Finset.mem_union_left _ (h23 (hU2 (s1 (hW01 hXW0))))
  have hB := h.img_bases C
  have hWUA : ↑WU ⊆ As := fun x hx => hA (Finset.mem_coe.2 (h23 (hU2 (Finset.mem_coe.1 hx))))
  have hZUA : ↑ZU ⊆ As := hZA
  have hXA : X ∈ As := hWUA (Finset.mem_coe.2 (s1 (hW01 hXW0)))
  have hXXA : X + X ∈ As := hWUA (Finset.mem_coe.2 (s1 (hW01 hXXW0)))
  have hPA : P ∈ As := hWUA (Finset.mem_coe.2 hPW)
  have hSA : P + e ∈ As := hA (Finset.mem_coe.2 (h23 hSW2))
  have hRA : P + e + g ∈ As := hA (Finset.mem_coe.2 hRW3)
  have heA : e ∈ As := mem_A (hmemU se te me) hWUA hZUA
  have hgA : g ∈ As := mem_A (hmemU sl tl ml) hWUA hZUA
  have hBA : B ∈ As := mem_A (hmemU sb tb mb) hWUA hZUA
  have hAA : A ∈ As := mem_A (hmemU sa ta ma) hWUA hZUA
  have hc1A : ggTh E c1 ∈ As := mem_A (hmemU sc tc mc) hWUA hZUA
  -- the codes over `u`
  obtain ⟨hau, hbu⟩ := Ph.phDec hu.1 huz a b hdec hb1
  have heu : GgCl u (hcE a) := qf_hcE_code hu hau
  have hlu : GgCl u (lg b) := Qc.qc_lg_code hu hbu
  have h1u : GgCl u (1 : Ordinal.{0}) := GgCl.small (gg_one_lt_of_SC hu)
  have h1au : GgCl u (1 + a) := GgCl.add h1u hau
  have hc1u : GgCl u c1 ∧ (b ≠ 0 → ∃ b1, GgCl u b1 ∧ ggTh u b = ggTh u b1 + ω ^ ggTh u (lg b) ∧
      ggTh u c1 = veblen (ggTh u a) (ggTh u b1)) := by
    rcases eq_or_ne b 0 with h0 | h0
    · rw [hc10 h0]; exact ⟨hau, fun h' => absurd h0 h'⟩
    · obtain ⟨b1, hbs, -, hdv, hc1eq⟩ := hc1b h0
      obtain ⟨b1', b2', hbs', -, hb1u', -, hb2l', hb2d'⟩ := Qc.qc_split hu b hbu h0
      rw [hb2l'] at hbs' hb2d'
      have e1 : b1' = b1 := Qc.qc_split_unique hbs' hbs hb2d' hdv
      rw [e1] at hb1u'
      refine ⟨by rw [hc1eq]; exact GgCl.phi hau hb1u', fun _ => ⟨b1, hb1u', ?_, ?_⟩⟩
      · conv_lhs => rw [hbs]
        rw [ggTh_add hu hb1u', ggTh_opow hu hlu]
      · rw [hc1eq]; exact Ph.phTh_phi hu a hau b1 hb1u'
  -- the copy data at `u`
  obtain ⟨haT, pa⟩ := ba As f (he_sub sa hWUA) (he_sub ta hZUA) C u hu huT hu1 hau hπu
  obtain ⟨hbT, pb⟩ := bb As f (he_sub sb hWUA) (he_sub tb hZUA) C u hu huT hu1 hbu hπu
  obtain ⟨heT, pe⟩ := be As f (he_sub se hWUA) (he_sub te hZUA) C u hu huT hu1 heu hπu
  obtain ⟨hlT, pl⟩ := bl As f (he_sub sl hWUA) (he_sub tl hZUA) C u hu huT hu1 hlu hπu
  obtain ⟨hcT, pc⟩ := bc As f (he_sub sc hWUA) (he_sub tc hZUA) C u hu huT hu1 hc1u.1 hπu
  obtain ⟨h1aT, pP⟩ := bP As f (he_sub (s1) hWUA) (he_sub t1 hZUA) C u hu huT hu1 h1au hπu
  rw [hTh1a] at pP
  set Au := ggTh u a with hAu
  set Bu := ggTh u b with hBu
  have hThu1a : ggTh u (1 + a) = 1 + Au := by rw [ggTh_add hu h1u, ggTh_small (gg_one_lt_of_SC hu).le]
  rw [hThu1a] at h1aT pP
  have hu1' : u < Om1 := by rw [rj_Om1]; exact hu1
  have hYeq : ggTh u z = veblen Au Bu := by
    conv_lhs => rw [← hdec]
    exact Ph.phTh_phi hu a hau b hbu
  have hY1 : ggTh u z < Om1 := by rw [rj_Om1]; exact Ph.phTh_lt_Om1 hu hu1 huz
  have hYT : ggTh u z ∈ TB ρ (f ρ) := by
    rw [hYeq]; exact hTB (f ρ) ρ Au Bu hB haT hbT (hYeq ▸ hY1)
  refine ⟨hYT, ?_⟩
  by_contra hlt
  push Not at hlt
  have hσ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
  have hfρX : f ρ < f X := C.mono C.rho hXA hρX
  have hU : ¬ UpsPt (f X) := fun hU =>
    absurd hlt (not_lt.2 (gn_lt_ups (upsPt_inE C.ups) hσ1 ((pi_bijOn hB).1.mapsTo hYT)
      (vz_pi_lt_Om1 hB hYT hY1) hU hfρX).le)
  obtain ⟨w', hwT, hπw, hwY⟩ := gn_pi_inv hB hYT hY1 hlt
  have hfXE : InE (f X) := gk_img_inE C hXA hXXA (gk_src2 h hXE hρX hXXδ.le) (lt_of_le_of_lt zero_le hfρX)
  have hw1 : w' < Om1 := hwY.trans hY1
  have hw0 : 0 < w' := by
    rcases eq_or_ne w' 0 with h0 | h0
    · rw [h0, pi_lt hB hB.1.pos] at hπw
      exact absurd hπw.symm hfXE.pos.ne'
    · exact pos_iff_ne_zero.2 h0
  have hwE : InE w' := gn_eps_down C.ups h.ρU hB hwT hw1 (by rw [hπw]; exact hfXE) hw0
  have hπlt : ∀ x, x ∈ TB ρ (f ρ) → pi (f ρ) ρ x < f X → x < w' := fun x hxT hx => by
    have : pi (f ρ) ρ x < pi (f ρ) ρ w' := by rw [hπw]; exact hx
    exact ((pi_bijOn hB).2.lt_iff_lt hxT hwT).1 this
  have hEA : E ∈ As := hA (Finset.mem_coe.2 (hW3 hEW))
  have huw : u < w' := hπlt u huT (by rw [hπu]; exact C.mono hEA hXA hEX)
  have hAuw : Au < w' := hπlt Au haT (pa.trans_lt (C.mono hAA hXA (ggTh_lt haC hap)))
  have hBuw : Bu < w' := hπlt Bu hbT (pb.trans_lt (C.mono hBA hXA (ggTh_lt hbC hb1)))
  have hc1w : ggTh u c1 < w' := hπlt _ hcT (pc.trans_lt (C.mono hc1A hXA (ggTh_lt hc1C hc1z)))
  -- the source, copied
  have himg : le1 (f X) (f (P + e + g)) := C.cov1 _ hXA _ hRA hsrc
  have hR : le1R (f X) (f (P + e + g)) := (C.sk _ (C.low _ hXA) hU _).1 himg
  have hfR : f (P + e + g) = f P + f e + f g := by
    rw [C.add _ hPA _ heA _ hSA rfl, C.add _ hSA _ hgA _ hRA rfl]
  -- the lower bound of `f(R)` at `w'`
  have h1Au1 : 1 + Au < Om1 := by rw [← hThu1a, rj_Om1]; exact Ph.phTh_lt_Om1 hu hu1 h1au
  obtain ⟨hmT, hmπ⟩ := he_pi_mul C.ups h.ρU hB hwT hw1 hwE (1 + Au) h1aT h1Au1
  obtain ⟨hT12, hπ12⟩ := pi_add hB hmT heT
  obtain ⟨hT123, hπ123⟩ := pi_add hB hT12 hlT
  set T := w' * (1 + Au) + ggTh u (hcE a) + ggTh u (lg b) with hTdef
  have hlow : pi (f ρ) ρ T ≤ f (P + e + g) := by
    rw [hπ123, hπ12, hmπ, hπw, hfR]
    exact add_le_add (add_le_add pP pe) pl
  have hwTle : w' ≤ T := (le_mul_of_one_le_right' le_self_add).trans (le_self_add.trans le_self_add)
  have hρu : ρ < u := by
    obtain ⟨hρT, hπρ⟩ := pi_base hB
    refine ((pi_bijOn hB).2.lt_iff_lt hρT huT).1 ?_
    rw [hπρ, hπu]; exact C.mono C.rho hEA hρE
  obtain ⟨l, hl, hlT', hπl⟩ := lh_pi hB hwT (hρu.trans huw) hw1
  -- `w' ≤₁ T`
  have hle1 : le1R (f X) (pi (f ρ) ρ T) := by
    have h1 : pi (f ρ) ρ w' ≤ pi (f ρ) ρ T := ((pi_bijOn hB).2.le_iff_le hwT hT123).2 hwTle
    rw [hπw] at h1
    exact le1R_of_le h1 hlow hR
  have hTl : pi (f ρ) ρ T ≤ pi (f ρ) ρ l := hπl.2 _ (by rw [hπw]; exact hle1)
  have hTl' : T ≤ l := ((pi_bijOn hB).2.le_iff_le hT123 hlT').1 hTl
  have hwT' : le1R w' T := le1R_of_le hwTle hTl' hl.1
  -- `T = luL(w', Θ_u a) + logend(Θ_u b)`
  have h1Au : 1 ≤ Au := by
    have := ggTh_mono (y := u) ha1; rwa [ggTh_small (gg_one_lt_of_SC hu).le] at this
  have hlgB : ggTh u (lg b) = lg Bu := by
    rcases eq_or_ne b 0 with h0 | h0
    · rw [hBu, h0, Qc.qc_lg_zero, ggTh_small zero_le, Qc.qc_lg_zero]
    · exact Qc.qc_th_lg hu hbu h0
  have hTeq : T = luL w' Au + lg Bu := by
    rw [hTdef, hc_luL_dec hwE h1Au hAuw, qf_th_hcE hu hau, hlgB]
  -- the separation below `φ(Θ_u a, Θ_u b)` over `u`
  have hYG : veblen Au Bu < lgG u := by rw [← hYeq]; exact qf_th_lt_G hu hu1' z huz
  set L := max (max u Au) (max Bu (ggTh u c1)) with hLdef
  have hLw : L < w' := max_lt (max_lt huw hAuw) (max_lt hBuw hc1w)
  have hL2 : ∀ b', b' < Bu → lg Bu ≤ lg b' → veblen Au b' ≤ L := by
    intro b' hb' hlg
    rcases eq_or_ne b 0 with h0 | h0
    · rw [hBu, h0, ggTh_small zero_le] at hb'; exact absurd hb' (not_lt.2 zero_le)
    · obtain ⟨b1, -, hBeq, hc1eq⟩ := hc1u.2 h0
      rw [hBeq] at hb' hlg
      rw [lu_lg_add_right (opow_pos _ omega0_pos).ne', LvE.lve_lg_opow] at hlg
      have hb'1 := qf_lg_lt_last hb' hlg
      calc veblen Au b' ≤ veblen Au (ggTh u b1) := (veblen_le_veblen_iff_right).2 hb'1
        _ = ggTh u c1 := hc1eq.symm
        _ ≤ L := (le_max_right _ _).trans (le_max_right _ _)
  have hsep := qf_sep hu hu1' h1Au hYG ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_left _ _)) hL2 w' hwE hLw
    (by rw [← hYeq]; exact hwY)
  exact hsep (hTeq ▸ hwT')

end Copy

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE COPY LEMMA FOR EVERY CODE** (`QfTBphi` given): for a strongly critical `E ∈ Tᵖ ∩ (ρ, δ)` in `W` with Lemma
IMG below `E`, every code `z` over `E` has copy data: the witness sets can be enlarged to contain `Θ_E(z)`, and
`π(Θ_u z) ≤ f(Θ_E z)` in every copy `f` for every strongly critical `u ∈ Tᵖ[f(ρ)] ∩ Ω₁` with `π(u) = f(E)` over which
`z` is a code. -/
theorem qf_copy (hTB : QfTBphi) {E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W)
    (hρE : ρ < E) (hES : SC E) (hE1 : E < Om 1) (hET : E ∈ Tset ρ) (hEδ : E < δ) (IH : ∀ v, v < E → GnI ρ δ v) :
    ∀ z, GgCl E z → ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧
      ggTh E z ∈ W' ∪ Z' ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A →
        ImgCtx ρ A f → ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u z → pi (f ρ) ρ u = f E →
          ggTh u z ∈ TB ρ (f ρ) ∧ pi (f ρ) ρ (ggTh u z) ≤ f (ggTh E z) := by
  classical
  have hE : InE E := Low.opow_eq_self_of_SC hES
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hρS : SC ρ := Qc.qc_rstK_SC h
  have hE1' : E < Om1 := by rw [rj_Om1]; exact hE1
  have hthδ : ∀ z, GgCl E z → ggTh E z < δ := fun z hz => by
    obtain ⟨hT, h1⟩ := qf_T_lgG hρS h.ρ1 hET hE1' hES _ (qf_th_lt_G hES hE1' z hz)
    exact gn_lt_δ h hT h1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IHz =>
  intro hz
  rcases lt_trichotomy z (Om 1) with hzΩ | rfl | hzΩ
  · -- a countable code: Lemma IMG at `z < E`
    have hzE' : z < E := hz.lt_of_lt_Om1 hES hzΩ
    obtain ⟨W0, Z0, w0, m0, -, -, b0⟩ := gnI_use h (IH z hzE')
    refine ⟨W ∪ W0, Z ∪ Z0, w.union w0, Finset.subset_union_left, Finset.subset_union_left, ?_,
      fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
    · rw [ggTh_small hzE'.le]
      rcases Finset.mem_union.1 m0 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
    · have hzu : z < u := huz.lt_of_lt_Om1 hu hzΩ
      obtain ⟨-, hzT, hπz⟩ := b0 A f (he_sub Finset.subset_union_right hW) (he_sub Finset.subset_union_right hZ) C
      rw [ggTh_small hzu.le, ggTh_small hzE'.le]
      exact ⟨hzT, hπz⟩
  · -- `Ω₁`: `Θ_E(Ω₁) = E`, `Θ_u(Ω₁) = u`
    refine ⟨W, Z, w, subset_refl _, subset_refl _, ?_, fun A f _ _ C u hu huT hu1 _ hπu => ?_⟩
    · rw [ggTh_Om1 hES hE1]; exact Finset.mem_union_left _ hEW
    · rw [ggTh_Om1 hu hu1, ggTh_Om1 hES hE1]
      exact ⟨huT, hπu.le⟩
  -- `Ω₁ < z < ε_{Ω₁+1}`
  have hz0 : z ≠ 0 := (lt_of_le_of_lt zero_le hzΩ).ne'
  have hz1 : Om1 < z := by rw [rj_Om1]; exact hzΩ
  obtain ⟨hsub, hlog⟩ := ggDec hES z hz
  set g := log ω z with hgdef
  by_cases hzEps : ω ^ z = z
  · -- an `ε`-code
    exact qf_copy_eps h hTB w hEW hρE hES hE1' hET hthδ hz hzΩ hzEps (fun y hy hyz => IHz y hyz hy)
  have hgz : g < z := by
    refine lt_of_le_of_ne (log_le_self ω z) fun e => hzEps ?_
    refine le_antisymm ?_ (right_le_opow z one_lt_omega0)
    calc ω ^ z = ω ^ log ω z := by rw [← hgdef, e]
      _ ≤ z := opow_log_le_self ω hz0
  have hwg : ω ^ g ≤ z := opow_log_le_self ω hz0
  have hEz : E < ggTh E z :=
    calc E = ggTh E (Om 1) := (ggTh_Om1 hES hE1).symm
      _ < ggTh E z := ggTh_lt GgCl.om hzΩ
  have hρz : ρ ≤ ggTh E z := (hρE.trans hEz).le
  rcases hwg.lt_or_eq with hwlt | hweq
  · -- a sum `z = ω^g + (z − ω^g)`
    have hwC : GgCl E (ω ^ g) := GgCl.opow hES.1 hlog
    have hrC : GgCl E (z - ω ^ g) := hsub _ hwC hwg
    have hzs : z = ω ^ g + (z - ω ^ g) := (Ordinal.add_sub_cancel_of_le hwg).symm
    have hr0 : z - ω ^ g ≠ 0 := fun h0 => by rw [h0, add_zero] at hzs; exact absurd hzs hwlt.ne'
    have hrz : z - ω ^ g < z := by
      refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
      have habs : ω ^ g + z = z := by
        conv_rhs => rw [hzs]
        rw [e]
      have h1 : ω ^ g * ω ≤ z := Ordinal.add_eq_right_iff_mul_omega0_le.1 habs
      rw [← opow_succ] at h1
      exact absurd (lt_opow_succ_log_self one_lt_omega0 z) (not_lt.2 h1)
    obtain ⟨W1, Z1, w1, hW1, hZ1, m1, b1⟩ := IHz _ hwlt hwC
    obtain ⟨W2, Z2, w2, hW2, hZ2, m2, b2⟩ := IHz _ hrz hrC
    have hthz : ggTh E z = ggTh E (ω ^ g) + ggTh E (z - ω ^ g) := by
      conv_lhs => rw [hzs]
      exact ggTh_add hES hwC _
    have hlt1 : ggTh E (ω ^ g) < ggTh E z := ggTh_lt hwC hwlt
    have hlt2 : ggTh E (z - ω ^ g) < ggTh E z := ggTh_lt hrC hrz
    have wU := w1.union w2
    have hzmem : ggTh E z ∈ insert (ggTh E z) (W1 ∪ W2) ∪ (Z1 ∪ Z2) :=
      Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    have m1' : ggTh E (ω ^ g) ∈ (W1 ∪ W2) ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m1 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hm)
    have m2' : ggTh E (z - ω ^ g) ∈ (W1 ∪ W2) ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m2 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
    refine ⟨insert (ggTh E z) (W1 ∪ W2), Z1 ∪ Z2,
      wU.insW hρz (hthδ z hz) (Or.inr ⟨_, m1', _, m2', hlt1, hlt2, hthz.symm⟩),
      fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha)),
      fun a ha => Finset.mem_union_left _ (hZ1 ha), hzmem, fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
    have hWU : ↑(W1 ∪ W2) ⊆ A := he_sub (Finset.subset_insert _ _) hW
    obtain ⟨hlogu, -⟩ := (ggDec hu z huz)
    obtain ⟨hsubu, hlogu'⟩ := ggDec hu z huz
    have hwCu : GgCl u (ω ^ g) := GgCl.opow hu.1 hlogu'
    have hrCu : GgCl u (z - ω ^ g) := hsubu _ hwCu hwg
    obtain ⟨hT1, hp1⟩ := b1 A f (he_sub Finset.subset_union_left hWU) (he_sub Finset.subset_union_left hZ) C u hu
      huT hu1 hwCu hπu
    obtain ⟨hT2, hp2⟩ := b2 A f (he_sub Finset.subset_union_right hWU) (he_sub Finset.subset_union_right hZ) C u hu
      huT hu1 hrCu hπu
    have hB := h.img_bases C
    obtain ⟨hTs, hπs⟩ := pi_add hB hT1 hT2
    have hthu : ggTh u z = ggTh u (ω ^ g) + ggTh u (z - ω ^ g) := by
      conv_lhs => rw [hzs]
      exact ggTh_add hu hwCu _
    have hA1 : ggTh E (ω ^ g) ∈ A := mem_A m1 (he_sub Finset.subset_union_left hWU)
      (he_sub Finset.subset_union_left hZ)
    have hA2 : ggTh E (z - ω ^ g) ∈ A := mem_A m2 (he_sub Finset.subset_union_right hWU)
      (he_sub Finset.subset_union_right hZ)
    have hAz : ggTh E z ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hfz : f (ggTh E z) = f (ggTh E (ω ^ g)) + f (ggTh E (z - ω ^ g)) :=
      (C.add _ hA1 _ hA2 _ hAz hthz.symm).symm
    rw [hthu, hfz, hπs]
    exact ⟨hTs, add_le_add hp1 hp2⟩
  · -- a power `z = ω^g`, `Ω₁ < g`
    have hgΩ : Om 1 < g := by
      by_contra hle
      push Not at hle
      have : z ≤ Om 1 := by
        rw [← hweq, ← Bt.Om1_opow]; exact opow_le_opow_right omega0_pos hle
      exact absurd hzΩ (not_lt.2 this)
    have hg0 : g ≠ 0 := (lt_of_le_of_lt zero_le hgΩ).ne'
    obtain ⟨g₁, g₂, hgs, hg₁g, hg₁C, hg₂C, hg₂l, hg₂d⟩ := qc_split hES g hlog hg0
    have hz₁ : ω ^ g₁ < z := by
      rw [← hweq]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hg₁g
    have hg₂z : g₂ < z := by
      have h1 : ω ^ g₂ ≤ g := by rw [hgs]; exact le_add_self
      exact ((right_le_opow g₂ one_lt_omega0).trans h1).trans_lt hgz
    have hz₁C : GgCl E (ω ^ g₁) := GgCl.opow hES.1 hg₁C
    obtain ⟨W1, Z1, w1, hW1, hZ1, m1, b1⟩ := IHz _ hz₁ hz₁C
    obtain ⟨W2, Z2, w2, hW2, hZ2, m2, b2⟩ := IHz _ hg₂z hg₂C
    set G := ggTh E g with hGdef
    set G₁ := ggTh E g₁ with hG₁def
    set G₂ := ggTh E g₂ with hG₂def
    have hGs : G = G₁ + ω ^ G₂ := by
      rw [hGdef, hgs, ggTh_add hES hg₁C, ggTh_opow hES hg₂C]
    have hthz : ggTh E z = ω ^ G := by rw [← hweq, ggTh_opow hES hlog]
    have hth₁ : ggTh E (ω ^ g₁) = ω ^ G₁ := ggTh_opow hES hg₁C
    have hG₁G : G₁ < G := by rw [hGs]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
    have hwδ : ω ^ G < δ := by rw [← hthz]; exact hthδ z hz
    have hρw : ρ ≤ ω ^ G := by rw [← hthz]; exact hρz
    have wU := w1.union w2
    set W3 := insert (ω ^ G) (W1 ∪ W2) with hW3
    have w3 : WZ ρ δ W3 (Z1 ∪ Z2) := wU.insW hρw hwδ (Or.inl (indec_opow _))
    have hwW3 : ω ^ G ∈ W3 := Finset.mem_insert_self _ _
    have m2' : G₂ ∈ W3 ∪ (Z1 ∪ Z2) := by
      rcases Finset.mem_union.1 m2 with hm | hm
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
    have hEG : E < G :=
      calc E = ggTh E (Om 1) := (ggTh_Om1 hES hE1).symm
        _ < G := ggTh_lt GgCl.om hgΩ
    have hGw : G < ω ^ G := by rw [← hthz]; exact ggTh_lt hlog hgz
    have hG₂w : G₂ < ω ^ G :=
      ((right_le_opow G₂ one_lt_omega0).trans (by rw [hGs]; exact le_add_self)).trans_lt hGw
    have hEw : E < ω ^ G := hEG.trans hGw
    have hw₁w : ω ^ G₁ < ω ^ G := (opow_lt_opow_iff_right one_lt_omega0).2 hG₁G
    have hlgG : lg G = G₂ := by rw [hGs, lu_lg_add_right (opow_pos _ omega0_pos).ne', LvE.lve_lg_opow]
    -- the common part of a copy
    have core : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W3 ⊆ A → ↑(Z1 ∪ Z2) ⊆ A →
        ImgCtx ρ A f → ∀ u, SC u → u ∈ TB ρ (f ρ) → u < Om 1 → GgCl u z → pi (f ρ) ρ u = f E →
        ∃ a', f (ω ^ G) = ω ^ a' ∧ ω ^ G ∈ A ∧ G₂ ∈ A ∧ E ∈ A ∧
          ggTh u z = ω ^ (ggTh u g₁ + ω ^ ggTh u g₂) ∧ ggTh u z ∈ TB ρ (f ρ) ∧
          pi (f ρ) ρ (ggTh u z) = ω ^ (pi (f ρ) ρ (ggTh u g₁) + ω ^ pi (f ρ) ρ (ggTh u g₂)) ∧
          pi (f ρ) ρ (ggTh u g₁) < a' ∧ pi (f ρ) ρ (ggTh u g₂) ≤ f G₂ ∧
          (g₂ ≠ 0 → 0 < pi (f ρ) ρ (ggTh u g₂)) := by
      intro A f hW hZ C u hu huT hu1 huz hπu
      have hB := h.img_bases C
      have hWU : ↑(W1 ∪ W2) ⊆ A := he_sub (Finset.subset_insert _ _) hW
      have hlogu : GgCl u g := (ggDec hu z huz).2
      obtain ⟨g₁', g₂', hgs', -, hg₁u', hg₂u', hg₂l', hg₂d'⟩ := qc_split hu g hlogu hg0
      have e2 : g₂' = g₂ := by rw [hg₂l', hg₂l]
      rw [e2] at hgs' hg₂d' hg₂u'
      have e1 : g₁' = g₁ := qc_split_unique hgs' hgs hg₂d' hg₂d
      rw [e1] at hg₁u'
      set G₁u := ggTh u g₁ with hG₁u
      set G₂u := ggTh u g₂ with hG₂u
      have hthu : ggTh u z = ω ^ (G₁u + ω ^ G₂u) := by
        rw [← hweq, ggTh_opow hu hlogu, hgs, ggTh_add hu hg₁u', ggTh_opow hu hg₂u']
      have hz₁u : GgCl u (ω ^ g₁) := GgCl.opow hu.1 hg₁u'
      obtain ⟨hT1, hp1⟩ := b1 A f (he_sub Finset.subset_union_left hWU) (he_sub Finset.subset_union_left hZ) C u hu
        huT hu1 hz₁u hπu
      obtain ⟨hT2, hp2⟩ := b2 A f (he_sub Finset.subset_union_right hWU) (he_sub Finset.subset_union_right hZ) C u
        hu huT hu1 hg₂u' hπu
      rw [ggTh_opow hu hg₁u', hth₁] at hp1
      rw [ggTh_opow hu hg₁u'] at hT1
      have hOmE : InE (Om (1 : Ordinal.{0})) := Low.opow_eq_self_of_SC (SC_Om one_ne_zero)
      have hcnt : ∀ c, GgCl u c → ggTh u c < Om1 := fun c hc => by
        rw [rj_Om1]; exact Ph.phTh_lt_Om1 hu hu1 hc
      have hthg : ggTh u g = G₁u + ω ^ G₂u := by rw [hgs, ggTh_add hu hg₁u', ggTh_opow hu hg₂u']
      have hG₁1 : G₁u < Om1 := hcnt _ hg₁u'
      have hG₂1 : G₂u < Om1 := hcnt _ hg₂u'
      have hs1 : G₁u + ω ^ G₂u < Om1 := by rw [← hthg]; exact hcnt _ hlogu
      have hG₁T : G₁u ∈ TB ρ (f ρ) := by
        have hw1 : ω ^ G₁u < Om1 := by
          have := hcnt _ hz₁u; rwa [ggTh_opow hu hg₁u'] at this
        have := (he_TB_cnf C.ups h.ρU hB hT1 hw1 (opow_pos _ omega0_pos).ne').2.1
        rwa [log_opow one_lt_omega0] at this
      obtain ⟨hw₂T, hw₂π⟩ := pi_opowZ C.ups h.ρU hB hT2 hG₂1
      obtain ⟨hsT, hsπ⟩ := pi_add hB hG₁T hw₂T
      obtain ⟨hzT, hzπ⟩ := pi_opowZ C.ups h.ρU hB hsT hs1
      obtain ⟨-, hw₁π⟩ := pi_opowZ C.ups h.ρU hB hG₁T hG₁1
      have hA3 : ω ^ G ∈ A := hW (Finset.mem_coe.2 hwW3)
      have hA2 : G₂ ∈ A := mem_A m2 (he_sub Finset.subset_union_right hWU) (he_sub Finset.subset_union_right hZ)
      have hA1 : ω ^ G₁ ∈ A := by
        have := mem_A m1 (he_sub Finset.subset_union_left hWU) (he_sub Finset.subset_union_left hZ)
        rwa [hth₁] at this
      have hEA : E ∈ A := hWU (Finset.mem_coe.2 (Finset.mem_union_left _ (hW1 hEW)))
      obtain ⟨a', ha'⟩ := hc_indec_opow h (C.indec _ hA3 (indec_opow _))
      have hlt1 : f (ω ^ G₁) < f (ω ^ G) := C.mono hA1 hA3 hw₁w
      have hG₁a : pi (f ρ) ρ G₁u < a' := by
        have : ω ^ pi (f ρ) ρ G₁u < ω ^ a' := by rw [← hw₁π, ← ha']; exact hp1.trans_lt hlt1
        exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      have hpos : g₂ ≠ 0 → 0 < pi (f ρ) ρ G₂u := fun hg₂0 => by
        have h0 : ggTh u 0 < G₂u := ggTh_lt (GgCl.zero hu.1) (pos_iff_ne_zero.2 hg₂0)
        rw [ggTh_small zero_le] at h0
        have h0T : (0 : Ordinal.{0}) ∈ TB ρ (f ρ) := mem_TB_of_lt hB hB.1.pos
        have := (pi_bijOn hB).2 h0T hT2 h0
        rwa [pi_lt hB hB.1.pos] at this
      refine ⟨a', ha', hA3, hA2, hEA, hthu, by rw [hthu]; exact hzT, by rw [hthu, hzπ, hsπ, hw₂π], hG₁a, hp2,
        hpos⟩
    have hW13 : W ⊆ W3 := fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha))
    have hZ13 : Z ⊆ Z1 ∪ Z2 := fun a ha => Finset.mem_union_left _ (hZ1 ha)
    rcases eq_or_ne g₂ 0 with hg₂0 | hg₂0
    · -- `g = g₁ + 1`
      refine ⟨W3, Z1 ∪ Z2, w3, hW13, hZ13, by rw [hthz]; exact Finset.mem_union_left _ hwW3,
        fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
      obtain ⟨a', ha', -, -, -, -, hzT, hzπ, hG₁a, -, -⟩ := core A f hW hZ C u hu huT hu1 huz hπu
      have hB := h.img_bases C
      refine ⟨hzT, ?_⟩
      have e0 : ggTh u g₂ = 0 := by rw [hg₂0]; exact ggTh_small zero_le
      rw [hzπ, hthz, ha', e0, pi_lt hB hB.1.pos, opow_zero]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hG₁a)
    · -- the source `ω^G ≤₁ ω^G + Θ_E(g₂)`
      have hG₂0 : 0 < G₂ := by
        have := ggTh_lt (GgCl.zero hES.1) (pos_iff_ne_zero.2 hg₂0); rwa [ggTh_small zero_le] at this
      have hTop : ω ^ G + G₂ < δ := hδI.add_lt hwδ (hG₂w.trans hwδ)
      set W4 := insert (ω ^ G + G₂) W3 with hW4
      have w4 : WZ ρ δ W4 (Z1 ∪ Z2) := w3.insW (hρw.trans le_self_add) hTop
        (Or.inr ⟨ω ^ G, Finset.mem_union_left _ hwW3, G₂, m2', lt_add_of_pos_right _ hG₂0,
          hG₂w.trans_le le_self_add, rfl⟩)
      have hL := lu_lh_opow (pos_iff_ne_zero.1 (hE.pos.trans hEG)) hGw
      rw [hlgG] at hL
      have hsrc : le1 (ω ^ G) (ω ^ G + G₂) := (h.lowδ _ _ (hρE.trans hEw) hTop.le).2 hL.1
      refine ⟨W4, Z1 ∪ Z2, w4, fun a ha => Finset.mem_insert_of_mem (hW13 ha), hZ13,
        by rw [hthz]; exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hwW3),
        fun A f hW hZ C u hu huT hu1 huz hπu => ?_⟩
      have hW3A : ↑W3 ⊆ A := he_sub (Finset.subset_insert _ _) hW
      obtain ⟨a', ha', hA3, hA2, hEA, -, hzT, hzπ, hG₁a, hp2, hpos⟩ := core A f hW3A hZ C u hu huT hu1 huz hπu
      have hB := h.img_bases C
      refine ⟨hzT, ?_⟩
      rw [hthz]
      have hTA : ω ^ G + G₂ ∈ A := hW (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      have himg : le1 (f (ω ^ G)) (f (ω ^ G) + f G₂) := by
        have := C.cov1 _ hA3 _ hTA hsrc
        rwa [← C.add _ hA3 _ hA2 _ hTA rfl] at this
      by_cases hU : UpsPt (f (ω ^ G))
      · have hfE : InE (f (ω ^ G)) := upsPt_inE hU
        have hlt : f E < f (ω ^ G) := C.mono hEA hA3 hEw
        have hz1u : ggTh u z < Om1 := by rw [rj_Om1]; exact Ph.phTh_lt_Om1 hu hu1 huz
        have hσ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
        have hσw : f ρ < f (ω ^ G) := C.mono C.rho hA3 (hρE.trans hEw)
        exact (gn_lt_ups (upsPt_inE C.ups) hσ1 ((pi_bijOn hB).1.mapsTo hzT) (vz_pi_lt_Om1 hB hzT hz1u) hU
          hσw).le
      · have hR := (C.sk _ (C.low _ hA3) hU _).1 himg
        have hf0 : 0 < f G₂ := (hpos hg₂0).trans_le hp2
        have hfle : f G₂ ≤ f (ω ^ G) := (C.mono hA2 hA3 hG₂w).le
        obtain ⟨a'', -, ha'', hlg⟩ := (le1R_thm22 hf0 hfle).1 hR
        have e : a'' = a' := by
          have h2 : ω ^ a'' = ω ^ a' := ha''.symm.trans ha'
          exact le_antisymm ((opow_le_opow_iff_right one_lt_omega0).1 h2.le)
            ((opow_le_opow_iff_right one_lt_omega0).1 h2.ge)
        rw [e] at hlg
        set p₁ := pi (f ρ) ρ (ggTh u g₁) with hp₁
        have hsplit : a' = p₁ + (a' - p₁) := (Ordinal.add_sub_cancel_of_le hG₁a.le).symm
        have hr0 : a' - p₁ ≠ 0 := fun h0 => by
          rw [h0, add_zero] at hsplit; exact absurd hsplit hG₁a.ne'
        have hlgr : lg a' = lg (a' - p₁) := by
          conv_lhs => rw [hsplit]
          exact lu_lg_add_right hr0
        have hdvd : ω ^ pi (f ρ) ρ (ggTh u g₂) ∣ a' - p₁ := (le_lg_iff hr0 _).1 (by rw [← hlgr]; exact hp2.trans hlg)
        have hge : p₁ + ω ^ pi (f ρ) ρ (ggTh u g₂) ≤ a' := by
          conv_rhs => rw [hsplit]
          exact add_le_add le_rfl (Ordinal.le_of_dvd hr0 hdvd)
        rw [hzπ, ha']
        exact opow_le_opow_right omega0_pos hge

end Copy

end Googology.Trans.PoR.InaccPsi.R2.Qf
