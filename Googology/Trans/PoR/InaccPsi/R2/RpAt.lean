import Googology.Trans.PoR.InaccPsi.R2.RpT1

/-!
# The codes `G(x)` are atoms of the hull at every Range restart with code `G' + 1`

`G(ζ) = ψ_{Ω₂}(Ω_ω + θ₂·ζ)` (`Lc.lcG`), `G' = G(θ_{k+1}·ω²)` (`Ls.lsG S (k+1)`), `A = A_{η_μ}`, `ρ_μ = ψ_{Ω₁}(A)`,
the atoms `Ls.lsAt S A ρ_μ` (the `ψ_{Ω₂}(e)`, `e < A`, `e ∈ Cl(A, ρ_μ)`).

* `rpG_lt` (**`G(x) < G'`** for `x < Ω₁`);
* `rpExp_code` (**code `G' + 1` means last exponent `G' + 1`**: the π-code is strongly critical, and a finite
  exponent has a finite code);
* `rpG'_atom` (**`G'` is an atom at `μ`**: the last exponent of a good name lies in the hull (`Gg.ggExp_HCl`), and a
  strongly critical code above `Ω₁` is an atom (`Mx.gxSC_atom`));
* `rpG_atom` (**every `G(x)`, `x < ρ_μ`, is an atom at `μ`, and `G(x) < G'`**: `G' = ψ_{Ω₂}(e)` with `e < A`, and
  `e ≤ Ω_ω + θ₂·x` would give `G' ≤ G(x) < G'`);
* `rpStep_of_read` (**`RpRead` gives `RpStep`**, so `RpStep ⇔ RpRead` at every Range restart);
* `RpBlkAt S μ x` (**one block**: the atoms below `G(x+1)` cover `ψ_{Ω₁}(A + θ·x + ζ)`, `ζ < θ`), `rpG_lt_succ`,
  `rpStep_of_blkAt` (**the base reading `υ_{μ+x} ≤ Θ_μ(G(x))` and the block at `x` give
  `υ_{μ+x+1} ≤ Θ_μ(G(x+1))`**: the collapses below `A + θ·x` are covered by the atom `G(x)`), `rpReadAll_of_blkAt`
  (**`RpReadAll` from the blocks, each given the reading of its base**).

So the codes that `Rp.RpRead` reads are codes of the hull at every restart it is asked at.

No new axiom.  New definition (hypothesis name only): `RpBlkAt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

theorem rpThx_mem {a b x : Ordinal.{0}} (ha : Om ω < a) (hx : x < b) :
    Om ω + Lc.lcTh S 2 * x ∈ S.CSet a b := by
  have h := Nm.mem_opow_mul (S := S) (Ls.lsTh_mem (S := S) (b := b) ha 2) hx
  rw [Ls.lsTh_opow] at h
  exact CSet.add_mem (ConjT.OmW_mem S a b) h

/-- **`G(x) < G'`** for `x < Ω₁`. -/
theorem rpG_lt {x : Ordinal.{0}} (k : ℕ) (hx : x < Om 1) : Lc.lcG S x < Ls.lsG S (k + 1) := by
  have hxk : x < Lc.lcTh S (k + 1) * ω ^ 2 :=
    (hx.trans (rpOm1_lt_th (S := S) k)).trans_le (Ordinal.le_mul_left _ (pow_pos omega0_pos 2))
  have hpos : 0 < Lc.lcTh S 2 := (Ls.lsTh_SC 2).1
  have hlt : Om ω + Lc.lcTh S 2 * x < Om ω + Lc.lcTh S 2 * (Lc.lcTh S (k + 1) * ω ^ 2) :=
    (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hpos).2 hxk)
  have hX0 : Om ω < Om ω + Lc.lcTh S 2 * (Lc.lcTh S (k + 1) * ω ^ 2) :=
    lt_of_le_of_lt le_self_add hlt
  exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt
    (rpThx_mem hX0 (hx.trans (psiS_bounds (S := S) _ 1).1))

/-- **Code `G' + 1` means last exponent `G' + 1`.** -/
theorem rpExp_code {μ : Ordinal.{0}} {k : ℕ} (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) :
    cdExp (cdEta S μ) = Ls.lsG S (k + 1) + 1 := by
  have hGSC : SC (Ls.lsG S (k + 1)) := Ls.lsG_SC _
  have h : cdCodeOf S (cdEta S μ) = Ls.lsG S (k + 1) + 1 := hc
  unfold cdCodeOf at h
  split_ifs at h with h2
  · unfold cdOff at h
    split_ifs at h with hω
    · exfalso
      have h3 : Ls.lsG S (k + 1) + 1 < ω := h ▸ (Ordinal.sub_le_self _ _).trans_lt hω
      exact absurd ((le_self_add).trans_lt h3) (not_lt.2 (Pp.ppOmega_lt_SC hGSC).le)
    · exact h
  · exact absurd h ((SC_psi (InR_Om_succ 1) _).ne_add_one _)

/-- **`G'` is an atom at a Range restart with code `G' + 1`.** -/
theorem rpG'_atom {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1) :
    Ls.lsG S (k + 1) ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ) := by
  have hX : upsilon μ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by rw [← Lw.lw_L_eq]; exact hR.2.2.1
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hR.1.1 hX
  have hH := Gg.ggExp_HCl (Nn.nnGood_HCl hg)
  have hmem : cdExp (cdEta S μ) ∈ S.CSet (ConjT.Aη S (cdEta S μ)) (upsilon μ) := by
    rw [← hpv]; exact hH.mem_CSet
  rw [rpExp_code hc] at hmem
  have hG := mem_of_add_one_mem hmem
  have hρ : S.psi (ConjT.Aη S (cdEta S μ)) (Om 1) = upsilon μ := hpv
  exact Mx.gxSC_atom (Ls.lsRho_lt hρ) ((Ls.lsHull_iff hρ (Lc.lcG_lt_Om2 _)).1 hG)
    (Ls.lsG_SC _) (Ls.lsG_Om1 _)

/-- **Every `G(x)`, `x < ρ_μ`, is an atom at `μ`, and `G(x) < G'`.** -/
theorem rpG_atom {μ x : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hx : x < upsilon μ) :
    Lc.lcG S x ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ) ∧ Lc.lcG S x < Ls.lsG S (k + 1) := by
  have hx1 : x < Om 1 := Rg.rgGam_lt hR hx
  have hGx := rpG_lt (S := S) k hx1
  obtain ⟨e, heA, heC, hGe⟩ := rpG'_atom hR hc
  have hlt : Om ω + Lc.lcTh S 2 * x < e := by
    by_contra hle
    push Not at hle
    have h1 : S.psi e (Om (1 + 1)) ≤ Lc.lcG S x := (psi_mono (S := S) (InR_Om_succ 1) hle).1
    rw [← hGe] at h1
    exact absurd (h1.trans_lt hGx) (lt_irrefl _)
  have hA : Om ω < ConjT.Aη S (cdEta S μ) := lt_of_le_of_lt le_self_add (hlt.trans heA)
  exact ⟨⟨Om ω + Lc.lcTh S 2 * x, hlt.trans heA, rpThx_mem hA hx, rfl⟩, hGx⟩

/-- **`RpRead` gives `RpStep`.** -/
theorem rpStep_of_read {μ : Ordinal.{0}} (h : RpRead S μ) : RpStep S μ :=
  fun x hx _ => h x ((Order.lt_add_one_iff.2 le_rfl).trans hx)

/-- `G(x) < G(x+1)` for `x < Ω₁`. -/
theorem rpG_lt_succ {x : Ordinal.{0}} (hx : x < Om 1) : Lc.lcG S x < Lc.lcG S (x + 1) := by
  have hpos : 0 < Lc.lcTh S 2 := (Ls.lsTh_SC 2).1
  have hlt : Om ω + Lc.lcTh S 2 * x < Om ω + Lc.lcTh S 2 * (x + 1) :=
    (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ hpos).2 (Order.lt_add_one_iff.2 le_rfl))
  exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt
    (rpThx_mem (lt_of_le_of_lt le_self_add hlt) (hx.trans (psiS_bounds (S := S) _ 1).1))

/-- **One block at `x`**: the atoms below `G(x+1)` cover `ψ_{Ω₁}(A + θ·x + ζ)` for every `ζ < θ`. -/
def RpBlkAt (S : InaccSeq.{0}) (μ x : Ordinal.{0}) : Prop :=
  ∀ ζ < ConjT.th S, ∃ t ∈ Ls.lsAt S (ConjT.Aη S (cdEta S μ)) (upsilon μ), t < Lc.lcG S (x + 1) ∧
    S.psi (ConjT.Aη S (cdEta S μ) + (ConjT.th S * x + ζ)) (Om 1) ≤ cdTheta S μ t

/-- **The step from the block at `x`**: given the reading `υ_{μ+x} ≤ Θ_μ(G(x))` of the base, the block at `x`
gives `υ_{μ+x+1} ≤ Θ_μ(G(x+1))` (`G(x)` is an atom below `G(x+1)`). -/
theorem rpStep_of_blkAt {μ : Ordinal.{0}} {k : ℕ} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (k + 1) + 1)
    (h : ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RpBlkAt S μ x) :
    RpStep S μ := by
  intro x hx hP
  have hd := Ls.lsDiv_of_code hc
  have hxρ : x < upsilon μ := (Order.lt_add_one_iff.2 le_rfl).trans hx
  have hx1 : x + 1 ≤ upsilon μ := hx.le
  have hB := h x hx hP
  rw [Rg.rgUps_eq hR hx1]
  refine Rg.rgPsi_le_cover (Ls.lsPv_range hR) (SC_psi (InR_Om_succ 1) _) (psiS_bounds (S := S) _ 1).1
    (psi_lt (InR_Om_succ 1) _).le (Rg.rgDvd_A hd) (Rg.rgD_le (Rg.rgGam_lt hR hx)) ?_
  intro ζ _ hζ
  right
  rcases lt_or_ge ζ (ConjT.th S * x) with hlo | hhi
  · obtain ⟨hat, -⟩ := rpG_atom hR hc hxρ
    refine ⟨Lc.lcG S x, hat, rpG_lt_succ (Rg.rgGam_lt hR hxρ), ?_⟩
    calc S.psi (ConjT.Aη S (cdEta S μ) + ζ) (Om 1)
        ≤ S.psi (ConjT.Aη S (cdEta S μ) + ConjT.th S * x) (Om 1) :=
          (psi_mono (S := S) Low.InR_Om_one (add_le_add le_rfl hlo.le)).1
      _ = upsilon (μ + x) := (Rg.rgUps_eq hR hxρ.le).symm
      _ ≤ cdTheta S μ (Lc.lcG S x) := hP
  · obtain ⟨ζ', rfl⟩ := exists_add_of_le hhi
    have hζ' : ζ' < ConjT.th S := by
      rw [mul_add_one] at hζ; exact (add_lt_add_iff_left _).1 hζ
    exact hB ζ' hζ'

/-- **The road needs only the blocks**: at every Range restart below `L(ω)` with code `G' + 1`, the block at `x`
given the reading of its base `G(x)`. -/
theorem rpReadAll_of_blkAt {k : ℕ}
    (h : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RpBlkAt S μ x) :
    RpReadAll S k :=
  rpReadAll_of_step fun μ hR hω hc => rpStep_of_blkAt hR hc (h μ hR hω hc)

end Googology.Trans.PoR.InaccPsi.R2.Rp
