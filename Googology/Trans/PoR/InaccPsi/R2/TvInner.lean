import Googology.Trans.PoR.InaccPsi.R2.TrFrag
import Googology.Trans.PoR.InaccPsi.R2.CitedTv

/-!
# `TrInner` from [W07a] §6, and Theorem FRAG with the segment move on every segment

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The round-95 reduction (`R2.Tr.trFrag`, `R2.Tr.trComm_iff_inner`) left one statement per segment pair,
`TrInner κ b c M`: `mv b c` maps the low-parameter points of `[ϑᵇ(Δ_M), ϑᵇ(Δ_M)⁺)` (read in `T^{ϑᵇ(Δ_M)}`) onto those of
`[ϑᶜ(Δ_M), ϑᶜ(Δ_M)⁺)`.  Here it follows from the cited `R2.tvSeg_pi` ([W07a] Def 6.2, Lemma 6.3 with Def 5.1):

* `tvSeg_hyp`, `tvSeg_base` (the hypotheses of `R2.tvSeg_pi` are met at `y = α`, where its conclusion is a
  theorem of the earlier axioms);
* `tvInner_lt` (`c < b`: `π_{c,b}` maps `TrTop (ϑᵇ(Δ_M)) κ M` onto `TrTop (ϑᶜ(Δ_M)) κ M`), `tvInner`
  (**`TrInner κ b c M` for all countable `υ`-points `b, c` above `κ ∈ E` and `M ≥ 1`**),
  `tvInnerAll` (every pair of chains);
* `tvComm` (**`mv b' c' ∘ π_{β,b} = π_{γ,c} ∘ mv b c` on the low-parameter points of height `≤ M`**), `tvCarry`;
* `tvFrag` (**Theorem FRAG with `Ψ = mv b_k c_k` on the low-parameter points of EVERY segment, for every
  configuration `F ⊆ D_m`, no hypothesis beyond the two chains**).

New axiom: `R2.tvSeg_pi` (file `CitedTv`).  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tv

open Ordinal Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tr

/-- **The hypotheses of `R2.tvSeg_pi` are satisfiable**: `y = α = ϑᵗ(Δₙ)` meets them. -/
theorem tvSeg_hyp {σ τ : Ordinal.{0}} (h : Bases σ τ) {n : ℕ} (hn : 1 ≤ n) :
    Dl τ n ∈ TB (Dl τ n) σ ∧ Dl τ n ≤ Dl τ n ∧ Dl τ n < Dp τ n := by
  obtain ⟨hτα, hαE, -⟩ := Dl_E h.2.1 h.2.2.2 hn
  obtain ⟨-, hα1, -⟩ := Dl_spec h.2.1 h.2.2.2 n
  have hB : Bases σ (Dl τ n) := ⟨h.1, hαE, h.2.2.1.trans hτα, hα1⟩
  refine ⟨(pi_base hB).1, le_rfl, ?_⟩
  rw [(Dp_spec h.2.1 h.2.2.2 hn).2.2]
  exact (Dl_E hαE hα1 hn).1

/-- **Consistency of `R2.tvSeg_pi` at `y = α`**: there its conclusion is already a theorem of the earlier axioms
(`R2.Tr.trDl_pi`, `R2.pi_base`), `π_{σ,α'}(π_{σ,τ}(α)) = σ = π_{σ,α}(α)`. -/
theorem tvSeg_base {σ τ : Ordinal.{0}} (h : Bases σ τ) {n : ℕ} (hn : 1 ≤ n) :
    pi σ τ (Dl τ n) ∈ TB (Dl σ n) σ ∧ pi σ (Dl σ n) (pi σ τ (Dl τ n)) = pi σ (Dl τ n) (Dl τ n) := by
  have hσ1 : σ < Om1 := h.2.2.1.trans h.2.2.2
  obtain ⟨hτα, hαE, -⟩ := Dl_E h.2.1 h.2.2.2 hn
  obtain ⟨-, hα1, -⟩ := Dl_spec h.2.1 h.2.2.2 n
  obtain ⟨hσα', hα'E, -⟩ := Dl_E h.1 hσ1 hn
  obtain ⟨-, hα'1, -⟩ := Dl_spec h.1 hσ1 n
  have hB : Bases σ (Dl τ n) := ⟨h.1, hαE, h.2.2.1.trans hτα, hα1⟩
  have hB' : Bases σ (Dl σ n) := ⟨h.1, hα'E, hσα', hα'1⟩
  rw [(trDl_pi h hn).2, (pi_base hB').2, (pi_base hB).2]
  exact ⟨(pi_base hB').1, rfl⟩

/-- **`π_{c,b}` maps `TrTop (ϑᵇ(Δ_M)) κ M` onto `TrTop (ϑᶜ(Δ_M)) κ M`** (`c < b`). -/
theorem tvInner_lt {κ b c : Ordinal.{0}} (hκ : InE κ) (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c)
    (hcb : c < b) (hκc : κ < c) {M : ℕ} (hM : 1 ≤ M) :
    pi c b '' TrTop (Dl b M) κ M = TrTop (Dl c M) κ M := by
  have hbE := upsPt_inE hb
  have hcE := upsPt_inE hc
  have hc1 := hcb.trans hb1
  have hB : Bases c b := ⟨hcE, hbE, hcb, hb1⟩
  obtain ⟨hbβ, hβE, -⟩ := Dl_E hbE hb1 hM
  obtain ⟨-, hβ1, -⟩ := Dl_spec hbE hb1 M
  obtain ⟨hcγ, hγE, -⟩ := Dl_E hcE hc1 hM
  obtain ⟨-, hγ1, -⟩ := Dl_spec hcE hc1 M
  have hBβ : Bases c (Dl b M) := ⟨hcE, hβE, hcb.trans hbβ, hβ1⟩
  have hBγ : Bases c (Dl c M) := ⟨hcE, hγE, hcγ, hγ1⟩
  have hDp : Dp b M = Dl (Dl b M) M := (Dp_spec hbE hb1 hM).2.2
  -- the cited step on a point of the top set
  have key : ∀ y ∈ TrTop (Dl b M) κ M, pi c b y ∈ TB (Dl c M) c ∧
      pi c (Dl c M) (pi c b y) = pi c (Dl b M) y := by
    intro y hy
    obtain ⟨hyT, hβy, hy1, hyM⟩ := hy
    have hyD : y < Dp b M := by rw [hDp]; exact lt_Dl_of_ht hβE hβ1 hyT.1 hy1 hyM
    exact tvSeg_pi hB hM (trTB_mono hκc.le hyT) hβy hyD
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hz, hzeq⟩ := key y hy
    obtain ⟨hyT, hβy, hy1, hyM⟩ := hy
    have hyc : y ∈ TB (Dl b M) c := trTB_mono hκc.le hyT
    have hL := (trParDown hκ hb hb1 (hκc.trans hcb) hM ⟨hyT, hβy, hy1, hyM⟩).1
    have hPz := pi_ht_Par hBγ hz
    have hPy := pi_ht_Par hBβ hyc
    rw [hzeq] at hPz
    refine ⟨⟨hz.1, ?_⟩, ?_, down_lt_Om1 hB (trTB_mono hκc.le hL.1) hL.2, ?_⟩
    · rw [← hPz.2, hPy.2]; exact hyT.2
    · by_contra hlt
      have hzc : pi c b y < c := (TB_inter_lt hBγ (not_le.1 hlt)).1 hz
      have e1 : pi c (Dl c M) (pi c b y) = pi c b y := pi_lt hBγ hzc
      have h2 := down_ge hBβ hyc hβy
      rw [← hzeq, e1] at h2
      exact absurd hzc (not_lt.2 h2)
    · rw [← hPz.1, hPy.1]; exact hyM
  · rintro ⟨hwT, hγw, hw1, hwM⟩
    have hwc : w ∈ TB (Dl c M) c := trTB_mono hκc.le hwT
    have huT : pi c (Dl c M) w ∈ Tset c := (pi_bijOn hBγ).1.mapsTo hwc
    obtain ⟨hvT, hpv⟩ := up_spec hBβ huT
    set v := up c (Dl b M) (pi c (Dl c M) w) with hvdef
    have hPv := pi_ht_Par hBβ hvT
    have hPw := pi_ht_Par hBγ hwc
    rw [hpv] at hPv
    have hcu : c ≤ pi c (Dl c M) w := down_ge hBγ hwc hγw
    have hv : v ∈ TrTop (Dl b M) κ M := by
      refine ⟨⟨hvT.1, ?_⟩, ?_, up_lt_Om1 hBβ huT (down_lt_Om1 hBγ hwc hw1), ?_⟩
      · rw [← hPv.2, hPw.2]; exact hwT.2
      · by_contra hlt
        have hvc : v < c := (TB_inter_lt hBβ (not_le.1 hlt)).1 hvT
        have e1 : pi c (Dl b M) v = v := pi_lt hBβ hvc
        rw [hpv] at e1
        rw [e1] at hcu
        exact absurd hvc (not_lt.2 hcu)
      · rw [← hPv.1, hPw.1]; exact hwM
    obtain ⟨hz, hzeq⟩ := key v hv
    refine ⟨v, hv, (pi_bijOn hBγ).1.injOn hz hwc ?_⟩
    rw [hzeq, hpv]

/-- **`TrInner κ b c M`** for countable `υ`-points `b, c` above `κ ∈ E` and `M ≥ 1`. -/
theorem tvInner {κ b c : Ordinal.{0}} (hκ : InE κ) (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c)
    (hc1 : c < Om1) (hκb : κ < b) (hκc : κ < c) {M : ℕ} (hM : 1 ≤ M) : TrInner κ b c M := by
  rcases trMv_cases hb1 hc1 hb hc with ⟨h, -, e⟩ | ⟨rfl, -⟩ | ⟨h, hB, e⟩
  · unfold TrInner; rw [e]; exact tvInner_lt hκ hb hb1 hc h hκc hM
  · exact trInner_self κ b M
  · have h2 := tvInner_lt hκ hc hc1 hb h hκb hM
    unfold TrInner
    rw [e, ← h2, ← Set.image_comp]
    have hid : ∀ x ∈ TrTop (Dl c M) κ M, (up b c ∘ pi b c) x = id x := fun x hx =>
      up_pi hB (trTB_mono hκb.le (trParDown hκ hc hc1 hκc hM hx).1.1)
    rw [Set.image_congr hid, Set.image_id]

/-- `TrInnerAll` for every pair of chains. -/
theorem tvInnerAll {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} (hb : Chain κ b m)
    (hc : Chain κ c m) : TrInnerAll κ b c m := by
  intro k hk M hM
  have hkm : k < m := by omega
  exact tvInner (upsPt_inE hb.kap) (hb.ups k hkm).1 (hb.ups k hkm).2 (hc.ups k hkm).1 (hc.ups k hkm).2
    (hb.bot k hkm) (hc.bot k hkm) hM

/-- **The commutation `mv b' c' ∘ π_{β,b} = π_{γ,c} ∘ mv b c`** on the low-parameter points of `seg(b)` of height
`≤ M` (`β = ϑ^{b'}(Δ_M)`, `γ = ϑ^{c'}(Δ_M)`). -/
theorem tvComm {κ b c b' c' : Ordinal.{0}} (hκ : InE κ) (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c)
    (hc1 : c < Om1) (hb' : UpsPt b') (hc' : UpsPt c') (hb'b : b' < b) (hc'c : c' < c) (hκb' : κ < b')
    (hκc' : κ < c') {M : ℕ} (hM : 1 ≤ M) {x : Ordinal.{0}} (hx : x ∈ TrTop b κ M) :
    mv b' c' (pi (Dl b' M) b x) = pi (Dl c' M) c (mv b c x) :=
  trComm_of_inner hκ hb hb1 hc hc1 hb' hc' hb'b hc'c hκb' hκc' hM
    (tvInner hκ hb' (hb'b.trans hb1) hc' (hc'c.trans hc1) hκb' hκc' hM) hx

/-- **The carry of the FRAG step**: `π_{γ,c}⁻¹ ∘ mv b' c' ∘ π_{β,b} = mv b c` on the low-parameter points of `seg(b)`
of height `≤ M`, and `mv b' c'` sends `β` to `γ`. -/
theorem tvCarry {κ b c b' c' : Ordinal.{0}} (hκ : InE κ) (hb : UpsPt b) (hb1 : b < Om1) (hc : UpsPt c)
    (hc1 : c < Om1) (hb' : UpsPt b') (hc' : UpsPt c') (hb'b : b' < b) (hc'c : c' < c) (hκb' : κ < b')
    (hκc' : κ < c') {M : ℕ} (hM : 1 ≤ M) {x : Ordinal.{0}} (hx : x ∈ TrTop b κ M) :
    up (Dl c' M) c (mv b' c' (pi (Dl b' M) b x)) = mv b c x ∧ mv b' c' (Dl b' M) = Dl c' M :=
  trCarry_of_inner hκ hb hb1 hc hc1 hb' hc' hb'b hc'c hκb' hκc' hM
    (tvInner hκ hb' (hb'b.trans hb1) hc' (hc'c.trans hc1) hκb' hκc' hM) hx

/-- **Theorem FRAG with the segment move on every segment**: for two chains and every finite `F ⊆ D_m` there is
`Ψ` with the conclusion of `R2.soFrag` ((F-a)–(F-f), `Ψ = mv b₀ c₀` on `F ∩ D_1`) and `Ψ x = mv b_k c_k x` for every
`x ∈ F ∩ seg(b_k) ∩ T^{b_k}[κ]`, every `k < m`. -/
theorem tvFrag {m : ℕ} {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} (hb : Chain κ b m) (hc : Chain κ c m)
    (F : Finset Ordinal.{0}) (hF : ↑F ⊆ DD κ b m) : ∃ Ψ, TrFragConcl κ b c m F Ψ :=
  trFrag hb hc (tvInnerAll hb hc) F hF

end Googology.Trans.PoR.InaccPsi.R2.Tv
