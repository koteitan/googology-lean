import Googology.Trans.PoR.InaccPsi.R2.ZbNo

/-!
# ZbAt: AN ABSTRACT ATOM SYSTEM FOR THE HULL CALCULUS (NO BOUND BELOW `B_Γ`)

`Zb.zbGsCS_lt_BG`: the code systems `Gs.GsCS` (atoms `Γ_{Ω₁+1+c}`, `c < B`, with the law `ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}`
for `c ≤ B`) end below `B_Γ`.  The hull calculus of `Gs.GsmUni` uses a code system only through its atom sets: the
codes over `Z` are `GxCl Z (At Z)`, they lie in the hulls `Cl(a, b)` with `Ω_ω ≤ a`, `Z ≤ b`, every member of a hull
`Cl(a, Z)` with countable part below `Z` that is below the bound `V` is a code over `Z`, and the atoms have support
below every strongly critical `Z`.  `ZbAS` asks exactly these facts, so the atoms may be any strongly critical
ordinals `> Ω₁` (`B_Γ` and the values of every `F_β` included, `Zb.ZbTl`).  The proofs are those of `Gs.GsmUni`
with `K.At` replaced by `A.At`; every `GsCS` is an instance (`ZbAS.ofGs`).

* `ZbAS`, `ZbAS.Ok` (the hull facts at `S`), `ZbAS.ofGs`, `zb_Pv_N`; `cl_lt_V`, `cl_mem_CSet`, `support`;
* `hull_iff` (**at a named fixed point `F` the hull below `V` is the set of codes over `F`**), `theta_eq`, `code_eq`
  (`m_F = e(η_F)`), `expMem`, `cof` (**named fixed points with a prescribed last exponent are cofinal**).

No new axiom.  New definitions: `ZbAS`, `ZbAS.Ok`, `ZbAS.ofGs`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Cd
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cp Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gs
  Googology.Trans.PoR.InaccPsi.R2.Ga Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Ph

/-- **An abstract atom system**: atom sets `At Z` (strongly critical, above `Ω₁`, monotone in `Z`, with support below
every strongly critical `Z`) and a strongly critical bound `V < Ω₂` above every atom; the hull facts at `S` are
`ZbAS.Ok`. -/
structure ZbAS where
  At : Ordinal.{0} → Set Ordinal.{0}
  V : Ordinal.{0}
  V_SC : SC V
  V_lt : V < Om (1 + 1)
  Om1_lt_V : Om 1 < V
  gxAt : ∀ Z, GxAt (At Z)
  mono : ∀ Z Z', Z ≤ Z' → At Z ⊆ At Z'
  lt_V : ∀ Z s, s ∈ At Z → s < V
  supp : ∀ Z s, SC Z → s ∈ At Z → ∃ Z', Z' < Z ∧ s ∈ At Z'

/-- **The hull facts of an atom system at `S`**: hull membership of the atoms over `Z` in every `Cl(a, b)` with
`Ω_ω ≤ a`, `Z ≤ b ≤ Ω₁` (`b` strongly critical) when every ordinal below `Z` is of the notation, and THE HULL LEMMA
below `V`.  Separate from `ZbAS`, so that the atoms may depend on `S`. -/
structure ZbAS.Ok (A : ZbAS) (S : InaccSeq.{0}) : Prop where
  mem : ∀ (a b Z s : Ordinal.{0}), Om ω ≤ a → SC b → b ≤ Om 1 → Z ≤ b → (∀ z < Z, z ∈ ⋃ e, S.CSet e 0) →
    s ∈ A.At Z → s ∈ S.CSet a b
  hull : ∀ (a Z : Ordinal.{0}), SC Z → Z ≤ Om 1 → (∀ y ∈ S.CSet a Z, y < Om 1 → y < Z) →
    ∀ x ∈ S.CSet a Z, x < A.V → GxCl Z (A.At Z) x

/-- **Every code system `Gs.GsCS` is an atom system.** -/
noncomputable def ZbAS.ofGs (K : GsCS) (S0 : InaccSeq.{0}) : ZbAS where
  At := K.At
  V := K.V
  V_SC := gsmV_SC
  V_lt := gsmV_lt_Om2 K S0
  Om1_lt_V := gcG_Om1_lt _
  gxAt := gsmAt_GxAt
  mono := fun _ _ h => gsmAt_mono h
  lt_V := fun _ _ h => gsmAt_lt_V h
  supp := fun Z s hZ hs => by
    obtain ⟨c, hc, hg, rfl⟩ := hs
    exact ⟨K.gt c + 1, hZ.isPrincipal hg (gg_one_lt_of_SC hZ), gsmG_atom hc (lt_add_one _)⟩

theorem ZbAS.ofGs_ok (K : GsCS) (S0 S : InaccSeq.{0}) : (ZbAS.ofGs K S0).Ok S where
  mem := fun _ _ _ _ ha _ _ hZb _ hs =>
    gsmAt_mem (S := S) ((gsm_B_lt_V K).trans ((gsmV_lt_Om2 K S).trans (ph_Om2_lt_Omw.trans_le ha))) hZb hs
  hull := fun _ _ hZ hZ1 hkey x hx hxV => gsmCl_of_CSet (S := S) hZ.1 hZ1 hkey x hx hxV

instance (K : GsCS) (S0 S : InaccSeq.{0}) : Fact ((ZbAS.ofGs K S0).Ok S) := ⟨ZbAS.ofGs_ok K S0 S⟩

/-- **Every ordinal below `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` is of the notation.** -/
theorem zb_Pv_N {S : InaccSeq.{0}} (η : Ordinal.{0}) {z : Ordinal.{0}} (hz : z < Pv S η) :
    z ∈ ⋃ e, S.CSet e 0 := by
  have h := Low.lt_psi_one_mem_Vals (S := S) _ z hz
  rw [← Term.vals_eq S]; exact h

namespace ZbAS

variable (A : ZbAS) {S : InaccSeq.{0}}

theorem cl_mono {Z Z' c : Ordinal.{0}} (h : Z ≤ Z') (hc : GxCl Z (A.At Z) c) : GxCl Z' (A.At Z') c :=
  hc.mono h (A.mono Z Z' h)

/-- **A code over `Z ≤ Ω₁` is below `V`.** -/
theorem cl_lt_V {Z c : Ordinal.{0}} (hZ : Z ≤ Om 1) (hc : GxCl Z (A.At Z) c) : c < A.V := by
  induction hc with
  | small h => exact (h.trans_le hZ).trans A.Om1_lt_V
  | om => exact A.Om1_lt_V
  | atom hs => exact A.lt_V _ _ hs
  | add _ _ ihx ihy => exact A.V_SC.isPrincipal ihx ihy
  | phi _ _ ihx ihy => exact A.V_SC.2 _ ihx _ ihy

/-- **A code over `Z` lies in every hull `Cl(a, b)` with `Ω_ω ≤ a` and `Z ≤ b`.** -/
theorem cl_mem_CSet [hA : Fact (A.Ok S)] {Z a b : Ordinal.{0}} (ha : Om ω ≤ a) (hb : SC b) (hb1 : b ≤ Om 1)
    (hZb : Z ≤ b) (hbN : ∀ z < b, z ∈ ⋃ e, S.CSet e 0) {x : Ordinal.{0}}
    (hx : GxCl Z (A.At Z) x) : x ∈ S.CSet a b := by
  induction hx with
  | small h => exact CSet.of_lt (lt_of_lt_of_le h hZb)
  | om => exact CSet.Om_mem (CSet.one_mem _ _)
  | atom hs => exact hA.out.mem a b Z _ ha hb hb1 hZb (fun z hz => hbN z (hz.trans_le hZb)) hs
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **A code over a strongly critical `Z` is a code over some `Z' < Z`.** -/
theorem support {Z : Ordinal.{0}} (hZ : SC Z) {x : Ordinal.{0}} (hx : GxCl Z (A.At Z) x) :
    ∃ Z' < Z, GxCl Z' (A.At Z') x := by
  have h1 := gg_one_lt_of_SC hZ
  induction hx with
  | @small x h => exact ⟨x + 1, hZ.isPrincipal h h1, GxCl.small (lt_add_one x)⟩
  | om => exact ⟨0, hZ.1, GxCl.om⟩
  | @atom s hs =>
    obtain ⟨Z', hZ', hs'⟩ := A.supp Z s hZ hs
    exact ⟨Z', hZ', GxCl.atom hs'⟩
  | add _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.add (A.cl_mono (le_max_left _ _) g1) (A.cl_mono (le_max_right _ _) g2)⟩
  | phi _ _ ihx ihy =>
    obtain ⟨Z1, h1', g1⟩ := ihx
    obtain ⟨Z2, h2', g2⟩ := ihy
    exact ⟨max Z1 Z2, max_lt h1' h2', GxCl.phi (A.cl_mono (le_max_left _ _) g1) (A.cl_mono (le_max_right _ _) g2)⟩

theorem Omw_le_A (η : Ordinal.{0}) : Om ω ≤ ConjT.Aη S η := le_self_add

theorem Omw_le_A1 (η : Ordinal.{0}) : Om ω ≤ ConjT.Aη S η + 1 := (Omw_le_A (S := S) η).trans le_self_add

/-- **At a named fixed point the hull below `V` is the set of codes over `F`.** -/
theorem hull_iff [hA : Fact (A.Ok S)] {F ηx x : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hx : x < A.V) : x ∈ cdHull S F ↔ GxCl F (A.At F) x := by
  have hSC : SC (upsilon F) := by rw [hfix]; exact ggSC_fix hF hfix hX
  have hF1 : upsilon F ≤ Om 1 := by rw [hfix]; exact (Fx.fx_fix_lt_Om1 hfix hX).le
  constructor
  · intro h
    have := hA.out.hull _ (upsilon F) hSC hF1 (ggKey hF hX) x h hx
    rwa [hfix] at this
  · intro h
    exact A.cl_mem_CSet (Omw_le_A (S := S) _) hSC hF1 (by rw [hfix]) (fun z hz => zb_Pv_N ηx (hz.trans hX)) h

/-- **`Θ_F(m) = Θ^b_F(m)`** (reading with the atoms over `F`) for `m ≤ V` at a named fixed point. -/
theorem theta_eq [Fact (A.Ok S)] {F ηx m : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hm : m ≤ A.V) : cdTheta S F m = gxTh F (A.At F) m :=
  ggOtp_congr m fun _ hx => A.hull_iff hF hfix hX (hx.trans_le hm)

/-- **`m_F = e(η_F)`** at a named fixed point with `e(η_F) ≤ V`. -/
theorem code_eq {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) ≤ A.V) : cdCode S F = cdExp (cdEta S F) := by
  have hFe := Fx.fxExp_fix hF hfix hX
  have hω : ω ≤ cdExp (cdEta S F) :=
    ((le_mul_left _ omega0_pos).trans (gg_ww_lt hF hfix).le).trans hFe
  unfold cdCode
  rw [cdCodeOf_of_lt (he.trans_lt A.V_lt), cpOff_of_ge hω]

/-- **The last exponent of the name of a named fixed point is a code over it** (when below `V`). -/
theorem expMem [Fact (A.Ok S)] {F ηx : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (he : cdExp (cdEta S F) < A.V) : GxCl F (A.At F) (cdExp (cdEta S F)) := by
  obtain ⟨hg, -, -, hpv⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hH := ggExp_HCl (Nn.nnGood_HCl hg)
  have hmem : cdExp (cdEta S F) ∈ cdHull S F := by
    unfold cdHull; rw [← hpv]; exact hH.mem_CSet
  exact (A.hull_iff hF hfix hX he).1 hmem

/-- **Named fixed points with a prescribed last exponent `c ≥ Ω₁` (a code over `Z`) are cofinal below `F`.** -/
theorem cof [Fact (A.Ok S)] {F ηx c Z ν : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F)
    (hX : upsilon F < Pv S ηx) (hc : GxCl Z (A.At Z) c) (hc1 : Om 1 ≤ c) (hce : c < cdExp (cdEta S F))
    (hZ : Z < F) (hν : ν < F) :
    ∃ μ, IsRestartIdx μ ∧ upsilon μ = μ ∧ ν < μ ∧ μ < F ∧ Z ≤ μ ∧ cdExp (cdEta S μ) = c := by
  obtain ⟨hg, hι, -, -⟩ := cdEta_pv_spec (S := S) hF.1 hX
  have hFlim : IsSuccLimit F := ri_lim hF
  have hww := (cp_fix_facts hF hfix).2.2
  have hη0 : cdEta S F ≠ 0 := by
    intro h
    rw [h, iota_zero] at hι
    have h1 : (1 : Ordinal.{0}) < ω * ω := lt_of_lt_of_le one_lt_omega0 (le_mul_left _ omega0_pos)
    exact absurd (hι ▸ hww) (not_lt.2 h1.le)
  obtain ⟨η0, hdec, hd⟩ := cdExp_decomp hη0
  set e := cdExp (cdEta S F) with he
  set i1 := max ν Z + 1 with hi1
  have hi1F : i1 < F := by
    rw [hi1, ← succ_eq_add_one]; exact hFlim.succ_lt (max_lt hν hZ)
  have h1i1 : 1 ≤ i1 := by rw [hi1]; exact le_add_self
  obtain ⟨hg1, hι1, hlt1⟩ := cdEta_spec (S := S) h1i1 (by rw [hι]; exact hi1F)
  set η1 := cdEta S i1 with hη1
  have hce' : ω ^ c < ω ^ e := (opow_lt_opow_iff_right one_lt_omega0).2 hce
  have hlt' : η1 + ω ^ c < cdEta S F := by
    rw [hdec]
    rcases lt_or_ge η1 η0 with h | h
    · calc η1 + ω ^ c ≤ η0 + ω ^ c := by gcongr
        _ < η0 + ω ^ e := (add_lt_add_iff_left _).2 hce'
    · obtain ⟨t, ht1⟩ := exists_add_of_le h
      have ht : t < ω ^ e := by
        have := hlt1; rw [hdec, ht1] at this; exact (add_lt_add_iff_left _).1 this
      rw [ht1, add_assoc]
      exact (add_lt_add_iff_left _).2 (isPrincipal_add_omega0_opow e ht hce')
  have hP1 : Pv S η1 = upsilon i1 := by rw [← hι1]; exact (ups_iota S η1).symm
  have hZP : Z ≤ Pv S (η1 + ω ^ c) := by
    calc Z ≤ max ν Z := le_max_right _ _
      _ ≤ i1 := le_self_add
      _ ≤ upsilon i1 := upsilon_normal.strictMono.le_apply
      _ = Pv S η1 := hP1.symm
      _ ≤ Pv S (η1 + ω ^ c) := Pv_mono le_self_add
  have hg' : Bt.Good S (η1 + ω ^ c) := by
    refine good_add hg1 ?_
    have hcC : c ∈ S.CSet (ConjT.Aη S (η1 + ω ^ c) + 1) (Pv S (η1 + ω ^ c)) :=
      A.cl_mem_CSet (Omw_le_A1 (S := S) _) (Pv_SC S _) (Pv_lt_Om1 S _).le hZP (fun z hz => zb_Pv_N _ hz) hc
    have := CSet.phi_mem (CSet.zero_mem _ _) hcC
    rwa [veblen_zero_apply] at this
  have hc0 : c ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans one_lt_Om1) hc1).ne'
  have hOm : Om 1 ≤ ω ^ c := by
    rw [← Om1_opow]; exact opow_le_opow_right omega0_pos hc1
  have hp1 : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := by
    rw [← Om1_opow]; exact isPrincipal_add_omega0_opow _
  have hgap : ∀ ζ < η1 + ω ^ c, ζ + Om 1 ≤ η1 + ω ^ c := by
    intro ζ hζ
    rcases lt_or_ge ζ η1 with h | h
    · calc ζ + Om 1 ≤ η1 + Om 1 := by gcongr
        _ ≤ η1 + ω ^ c := (add_le_add_iff_left _).2 hOm
    · obtain ⟨s, rfl⟩ := exists_add_of_le h
      have hs : s < ω ^ c := (add_lt_add_iff_left _).1 hζ
      rw [add_assoc]
      refine (add_le_add_iff_left _).2 ?_
      rcases hOm.lt_or_eq with hlt | heq
      · exact (isPrincipal_add_omega0_opow c hs hlt).le
      · rw [← heq] at hs ⊢; exact (hp1.add_eq_right hs).le
  have hfx := ggFix (S := S) (isSuccLimit_add η1 (gg_opow_lim hc0)) hgap
  set μ := iota S (η1 + ω ^ c) with hμ
  have hμ1 : 1 ≤ μ := by have := iota_mono (S := S) (η1 + ω ^ c) 0 zero_le; rwa [iota_zero] at this
  have hμ0 : μ ≠ 0 := (lt_of_lt_of_le zero_lt_one hμ1).ne'
  have hi1μ : i1 < μ := by
    rw [← hι1]; exact cd_iota_lt_of_good hg1 (lt_add_of_pos_right _ (opow_pos _ omega0_pos))
  refine ⟨μ, Fx.fx_ri_of_fix hμ0 hfx, hfx, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left ν Z).trans_lt ((lt_add_one _).trans hi1μ)
  · rw [← hι]; exact cd_iota_lt_of_good hg' hlt'
  · exact ((le_max_right ν Z).trans_lt ((lt_add_one _).trans hi1μ)).le
  · rw [cdEta_unique hg' rfl, cpExp_add η1 (Nn.nn_opow_ne c), ggExp_opow]

end ZbAS

end Googology.Trans.PoR.InaccPsi.R2.Zb
