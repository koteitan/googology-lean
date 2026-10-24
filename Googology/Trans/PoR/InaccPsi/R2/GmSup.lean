import Googology.Trans.PoR.InaccPsi.R2.GlR8

/-!
# THE SUPREMUM OF ALL FRONTIERS BELOW THE CODE `Γ_{Ω₁+1}`: `ι(Γ_{Γ_{Ω₁+1}})`

Round 83 located every code below `Γ_{Ω₁+1}` (`R2.Gl`), one reading system `glRS (glD n)` per bound `glBn n`, with the
frontiers `ι(Γ_{Ω₁+1+glBn n})`.  Here the codes `c_k = glCfn k 0` (`c_0 = ε_{Ω₁+1}`, `c_{k+1} = φ(c_k, 0)`, gate `0`)
are cofinal in `Γ_{Ω₁+1}` (`gmC_cof`), and their layers form ONE family whose supremum is `ι(Γ_{Γ_{Ω₁+1}})`:

* `gmC`, `gmC_spec`, `gmC_mono`, `gmC_cof` (**`sup_k c_k = Γ_{Ω₁+1}`**);
* `gmS_psi` (**`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for every `c ≤ Γ_{Ω₁+1}`**), `gmS_V_lt_Om2`, `gmS_V_good`;
* `gmSX`, `gmSX_loc`, `gmSFam`, `gmSFam_sup` (**`sup = ι(Γ_{Γ_{Ω₁+1}})`, `P(Γ_{Γ_{Ω₁+1}}) < L(0)`**), `gmSFam_enum`
  (**ENUM-REACH**, fixed points included), `gmSFam_capV`, `gmSFam_blk` (**BLK^O and the exact reaches**),
  `gmSFam_road` (**THE ROAD with UPPER, LOWER, CapV asked only at `λ ≥ ι(Γ_{Γ_{Ω₁+1}})`**), `gmSup_fr_order`.

No new axiom.  New definitions: `gmC`, `gmSX`, `gmSFam`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gm

open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gi Googology.Trans.PoR.InaccPsi.R2.Gk
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## The cofinal codes `c_k` -/

/-- **The cofinal codes**: `c_k = glCfn k 0` (`c_0 = ε_{Ω₁+1}`, `c_{k+1} = φ(c_k, 0)`), the first cofinal code of
the bound `glBn k`. -/
noncomputable def gmC (k : ℕ) : Ordinal.{0} := glCfn k 0

theorem gmC_spec (k : ℕ) : gfE ≤ gmC k ∧ gmC k < glBn k ∧ glG (gmC k) = 0 :=
  let h := ((glBn_spec k).2.2.2.2.1 0)
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem gmC_lt_G0 (k : ℕ) : gmC k < gcG 0 := (gmC_spec k).2.1.trans (glBn_spec k).1

theorem gmC_succ (k : ℕ) : gmC (k + 1) = veblen (gmC k) 0 := rfl

theorem gmC_mono (k : ℕ) : gmC k < gmC (k + 1) := by
  rw [gmC_succ]
  exact gl_veb_zero_gt (Om1_lt_eW.trans_le (gmC_spec k).1) (gmC_lt_G0 k)

/-- **`sup_k c_k = Γ_{Ω₁+1}`**: every code below `Γ_{Ω₁+1}` is below some `c_k`. -/
theorem gmC_cof {c : Ordinal.{0}} (hc : c < gcG 0) : ∃ k, c < gmC k := by
  by_contra hcon
  push Not at hcon
  have hbdd : BddAbove (Set.range gmC) := ⟨c, by rintro _ ⟨k, rfl⟩; exact hcon k⟩
  set S := ⨆ k, gmC k with hSdef
  have hSc : S ≤ c := Ordinal.iSup_le hcon
  have hfix : veblen S 0 = S := by
    refine le_antisymm ?_ (by simpa using left_le_veblen S 0)
    rw [(isNormal_veblen_zero).map_iSup hbdd]
    exact Ordinal.iSup_le fun n => Ordinal.le_iSup gmC (n + 1)
  have hOS : Om1 < S := (Om1_lt_eW.trans_le (gmC_spec 0).1).trans_le (Ordinal.le_iSup gmC 0)
  have h1 := gl_G0_le (gl_SC_of_fix hfix (lt_of_le_of_lt zero_le hOS)) hOS
  exact absurd (hc.trans_le (h1.trans hSc)) (lt_irrefl c)

/-! ## `ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` up to `c = Γ_{Ω₁+1}` -/

/-- **`ψ_{Ω₂}(c) = Γ_{Ω₁+1+c}` for every `c ≤ Γ_{Ω₁+1}`** (the codes below `Γ_{Ω₁+1}` lie in every hull containing
their gate, `gl_mem`). -/
theorem gmS_psi (S : InaccSeq.{0}) : ∀ c : Ordinal.{0}, c ≤ gcG 0 → S.psi c (Om (1 + 1)) = gcG c := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc
  refine le_antisymm (gaPsi_le S (gcG_SC c) (gcG_Om1_lt c) fun e he => ?_)
    (gcG_le_of (ga_psi_SC c) (ga_Om1_lt_psi c) fun β hβ => ?_)
  · rw [IH e he (he.le.trans hc)]; exact gcG_lt he
  · rw [← IH β hβ (hβ.le.trans hc)]
    have hβW : β < gcG 0 := hβ.trans_le hc
    refine psi_lt_psi_of_mem (InR_Om_succ 1) hβ (gl_mem β hβW ?_).1
    exact (glG_lt_Om1 β hβW).trans (by rw [Br.Om1_eq]; exact ga_Om1_lt_psi c)

/-- `Γ_{Ω₁+1}` lies in every hull `Cl(a, b)` with `0 < a`. -/
theorem gmS_G0_mem (S : InaccSeq.{0}) {a b : Ordinal.{0}} (ha : 0 < a) : gcG 0 ∈ S.CSet a b := by
  rw [← gmS_psi S 0 zero_le]
  exact CSet.psi_mem ha (InR_Om_succ 1) (ga_Om2_mem _ _) (CSet.zero_mem _ _)

theorem gmS_V_psi (S : InaccSeq.{0}) : S.psi (gcG 0) (Om (1 + 1)) = gcG (gcG 0) := gmS_psi S _ le_rfl

theorem gmS_V_lt_Om2 (S : InaccSeq.{0}) : gcG (gcG 0) < Om (1 + 1) := by
  rw [← gmS_V_psi S]; exact psi_lt (InR_Om_succ 1) _

theorem gmS_G0_lt_A (S : InaccSeq.{0}) (η : Ordinal.{0}) : gcG 0 < ConjT.Aη S η + 1 := by
  have h1 : gcG 0 < gcG (gcG 0) := gcG_lt (gcG_SC 0).1
  have h2 : gcG (gcG 0) < Om (1 + 1) := gmS_V_lt_Om2 S
  have h2ω : (1 + 1 : Ordinal.{0}) < ω := by
    rw [show (1 + 1 : Ordinal.{0}) = ((2 : ℕ) : Ordinal.{0}) by norm_num]; exact natCast_lt_omega0 2
  have h3 : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 h2ω
  exact ((h1.trans (h2.trans (h3.trans_le le_self_add))).trans_le le_self_add)

/-- **`Γ_{Γ_{Ω₁+1}}` is good**: it lies in the hull of its own `A`. -/
theorem gmS_V_good (S : InaccSeq.{0}) : Bt.Good S (gcG (gcG 0)) := by
  show gcG (gcG 0) ∈ S.CSet (ConjT.Aη S (gcG (gcG 0)) + 1) (S.psi (ConjT.Aη S (gcG (gcG 0))) (Om 1))
  have := CSet.psi_mem (S := S) (a := ConjT.Aη S (gcG (gcG 0)) + 1)
    (b := S.psi (ConjT.Aη S (gcG (gcG 0))) (Om 1)) (gmS_G0_lt_A S _) (InR_Om_succ 1) (ga_Om2_mem _ _)
    (gmS_G0_mem S (lt_of_le_of_lt zero_le (gmS_G0_lt_A S _)))
  rwa [gmS_V_psi S] at this

/-! ## The family of the layers of the codes `c_k` -/

/-- **The layer of the code `c_k`**, in the reading system of the bound `glBn k`. -/
noncomputable def gmSX (k : ℕ) : XtSys := (glRS (glD k)).giXk 0

theorem gmSX_code (k : ℕ) : (glRS (glD k)).cf 0 = gmC k := rfl

theorem gmSX_loc (S : InaccSeq.{0}) (k : ℕ) : xtB1 (gmSX k) = iota S (gcG (gmC k) * ω) :=
  (glRS (glD k)).giXk_loc S 0

theorem gmS_good_mul (S : InaccSeq.{0}) (k : ℕ) : Bt.Good S (gcG (gmC k) * ω) :=
  (glRS (glD k)).giGood_mul ((glRS (glD k)).cf_lt 0) ((glRS (glD k)).cf_g 0) S

/-- **THE FAMILY of the layers of the codes `c_k`** (each in its own reading system). -/
noncomputable def gmSFam (S : InaccSeq.{0}) : XtFam where
  bd := fun k => xtB1 (gmSX k)
  off := fun k => xtOrec (gmSX k)
  spec := fun k => xtSpec1 ((glRS (glD k)).giX_pkg _ _ _ _)
  mono := fun k => by
    show xtB1 (gmSX k) < xtB1 (gmSX (k + 1))
    rw [gmSX_loc S, gmSX_loc S]
    refine cd_iota_lt_of_good (gmS_good_mul S k) ?_
    have hE := geG_E (gmC (k + 1))
    exact (InE.mul_lt hE (gcG_lt (gmC_mono k)) (omega0_lt_inE hE)).trans_le
      (le_mul_of_one_le_right' one_lt_omega0.le)
  nonfix := fun k => (glRS (glD k)).giX_nonfix _ _ _ _

/-- **`sup_k Λ⁺(c_k) = ι(Γ_{Γ_{Ω₁+1}})`, `υ` of it `= P(Γ_{Γ_{Ω₁+1}}) < L(0)`.** -/
theorem gmSFam_sup (S : InaccSeq.{0}) : (gmSFam S).famSup = iota S (gcG (gcG 0)) ∧
    upsilon (gmSFam S).famSup = Pv S (gcG (gcG 0)) ∧ Pv S (gcG (gcG 0)) < Nc.ncL S 0 := by
  have hVS : SC (gcG (gcG 0)) := gcG_SC _
  have hVE : ω ^ gcG (gcG 0) = gcG (gcG 0) := Low.opow_eq_self_of_SC hVS
  have heq : (gmSFam S).famSup = iota S (gcG (gcG 0)) := by
    refine le_antisymm (Ordinal.iSup_le fun k => ?_) ?_
    · show xtB1 (gmSX k) ≤ _
      rw [gmSX_loc S k]
      exact iota_mono _ _ (InE.mul_lt hVE (gcG_lt (gmC_lt_G0 k)) (omega0_lt_inE hVE)).le
    · rw [iota_limit hVS.isSuccLimit]
      refine ciSup_le' fun e => ?_
      obtain ⟨c, hc, hec⟩ := gcG_lt_of_lt_limit gl_G0_lim e.2
      obtain ⟨n, hn⟩ := gmC_cof hc
      have h1 : e.1 < gcG (gmC n) * ω :=
        (hec.trans (gcG_lt hn)).trans_le (le_mul_of_one_le_right' one_lt_omega0.le)
      calc iota S e.1 ≤ iota S (gcG (gmC n) * ω) := iota_mono _ _ h1.le
        _ = xtB1 (gmSX n) := (gmSX_loc S n).symm
        _ ≤ (gmSFam S).famSup := ((gmSFam S).famBd_lt n).le
  have hups : upsilon (gmSFam S).famSup = Pv S (gcG (gcG 0)) := by rw [heq, ups_iota S]
  exact ⟨heq, hups, ga_Pv_lt_L0 S (gmS_V_lt_Om2 S).le⟩

theorem gmSFam_fix (S : InaccSeq.{0}) : (gmSFam S).famTHfix S :=
  fun k _ hr hlk hfix => (glRS (glD k)).giFix _ _ _ _ S hr hlk hfix

theorem gmSFam_lt {S : InaccSeq.{0}} {l : Ordinal.{0}} (hl : l < iota S (gcG (gcG 0))) :
    ∃ k, l < iota S (gcG (gmC k) * ω) := by
  rw [← (gmSFam_sup S).1] at hl
  obtain ⟨k, hk⟩ := (gmSFam S).famLt hl
  exact ⟨k, by rw [← gmSX_loc S k]; exact hk⟩

/-- **ENUM-REACH at every range restart below `ι(Γ_{Γ_{Ω₁+1}})`, fixed points included.** -/
theorem gmSFam_enum (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gcG 0))) :
    CdUpper S l ∧ CdLower S l := by
  obtain ⟨k, hk⟩ := gmSFam_lt hl
  exact (glRS (glD k)).giEnum _ ((glRS (glD k)).cf_ge 0) ((glRS (glD k)).cf_lt 0) ((glRS (glD k)).cf_g 0) S hr hk

/-- **CapV at every range restart below `ι(Γ_{Γ_{Ω₁+1}})`, fixed points included.** -/
theorem gmSFam_capV (S : InaccSeq.{0}) {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S (gcG (gcG 0))) :
    CdCapV S l := by
  obtain ⟨k, hk⟩ := gmSFam_lt hl
  exact (glRS (glD k)).giCapV _ ((glRS (glD k)).cf_ge 0) ((glRS (glD k)).cf_lt 0) ((glRS (glD k)).cf_g 0) S hr hk

/-- **Theorem BLK^O below `υ_{ι(Γ_{Γ_{Ω₁+1}})} = P(Γ_{Γ_{Ω₁+1}})`**, with the exact reaches. -/
theorem gmSFam_blk (S : InaccSeq.{0}) :
    (∀ c d, c < d → d < upsilon (gmSFam S).famSup → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < (gmSFam S).famSup ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < (gmSFam S).bd k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + (gmSFam S).off k l)) ∧
    (∀ α < upsilon (gmSFam S).famSup, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := (gmSFam S).famBlk

/-- **THE ROAD past every code below `Γ_{Ω₁+1}`**: UPPER, LOWER and CapV asked only at `λ ≥ ι(Γ_{Γ_{Ω₁+1}})` (CapV
also `υ_λ < L(ω)`), (CL), EQ, TCrest, (EMB₂) ⟹ `ν_C = L(ω+1)`, `L(ω) ≤ ν_C`, `L(ω) <₂ L(ω+1)`, (P), (Q), the reaches. -/
theorem gmSFam_road (S : InaccSeq.{0}) (hU : ∀ l, CdRange S l → iota S (gcG (gcG 0)) ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S (gcG (gcG 0)) ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → iota S (gcG (gcG 0)) ≤ l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have hF := (gmSFam_sup S).1
  refine (gmSFam S).famRoad3 (fun l hr h => hU l hr (hF ▸ h)) (fun l hr h => hL l hr (hF ▸ h)) (gmSFam_fix S)
    (fun l hr hlω _ => ?_) hC hEQ hrest hB2
  rcases le_or_gt (gmSFam S).famSup l with h | h
  · exact hV l hr hlω (hF ▸ h)
  · exact gmSFam_capV S hr (hF ▸ h)

/-- **The order of the frontiers**: `ι(Γ_{Ω₁+1+glBn n}) < ι(Γ_{Γ_{Ω₁+1}}) < ι(Ω₂)`, and
`P(Γ_{Γ_{Ω₁+1}}) < P(Ω₂) < L(0)`. -/
theorem gmSup_fr_order (n : ℕ) (S : InaccSeq.{0}) :
    iota S (gcG (glBn n)) < iota S (gcG (gcG 0)) ∧ iota S (gcG (gcG 0)) < iota S (Om (1 + 1)) ∧
      Pv S (gcG (gcG 0)) < Pv S (Om (1 + 1)) ∧ Pv S (Om (1 + 1)) < Nc.ncL S 0 := by
  have hgood : Bt.Good S (gcG (glBn n)) := by
    show gcG (glBn n) ∈ S.CSet (ConjT.Aη S (gcG (glBn n)) + 1) (S.psi (ConjT.Aη S (gcG (glBn n))) (Om 1))
    have := CSet.psi_mem (S := S) (a := ConjT.Aη S (gcG (glBn n)) + 1)
      (b := S.psi (ConjT.Aη S (gcG (glBn n))) (Om 1))
      ((glBn_spec n).1.trans (gmS_G0_lt_A S _)) (InR_Om_succ 1) (ga_Om2_mem _ _)
      ((glBn_spec n).2.2.2.1 S _ _)
    rwa [gmS_psi S _ (glBn_spec n).1.le] at this
  have h2 : iota S (gcG (glBn n)) < iota S (gcG (gcG 0)) := cd_iota_lt_of_good hgood (gcG_lt (glBn_spec n).1)
  have h3 : iota S (gcG (gcG 0)) < iota S (Om (1 + 1)) := cd_iota_lt_of_good (gmS_V_good S) (gmS_V_lt_Om2 S)
  have h4 : Pv S (gcG (gcG 0)) < Pv S (Om (1 + 1)) := by
    have := upsilon_normal.strictMono h3
    rw [ups_iota S, ups_iota S] at this
    exact this
  exact ⟨h2, h3, h4, ga_Pv_lt_L0 S le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2.Gm
