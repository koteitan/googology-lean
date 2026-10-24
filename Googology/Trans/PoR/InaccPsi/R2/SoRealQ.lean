import Googology.Trans.PoR.InaccPsi.R2.SoSupQ

/-!
# The base renaming `a ↦ ρ_μ` of the offsets below `a^a`: realizers at `m*` and `L(n+1)` up to `υ_{a+a^a}`

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`a = m*` or `a = L(n+1)`, a named point with `ι(η_a) = a = P(η_a)`, `ω^{Ω₁} ∣ η_a`.  The inner restarts below
`υ_{a+a^a}` are `a + g`, `g = Σ a^{e_i}·c_i < a^a` (`e_i, c_i < a`), with the name `η_a + g` and the short code
`-1 + e(g)`, `e(g) = a·E + q` (`E` the last exponent, `q = e(c)` for the last digit `c`): the codes `a·ω`,
`a·ω²`, … (offsets `a^ω`, `a^{ω²}`, …) appear.  The renaming `f = So.soG ρ_μ a` keeps the exponents and the
digits and moves the base: the image restart `μ + f(g)` has the code `ρ_μ·E + q`.  The reach
`υ_{a+g+ω+1} + a·E + q` is carried by `So.soReal_ren` (the map is `π_{υ_μ,υ_λ}` on `seg(υ_λ)`, so
`υ_λ·E ↦ υ_μ·E`); the supply `υ_{μ+ρ_μ^{ρ_μ}} ≤ r(μ)` is `So.soSupQ`.

* `soCode_shiftQ` (**`η_{ι(η)+g} = η + g`, `m_{ι(η)+g} = -1+e(g)` for `0 < g < P(η)^{P(η)}`**), `soDivUniqO`,
  `soUps_injO` (`υ_{λ+h} + υ_λ·J + p` determines `h`, `J`, `p` for `J, p < υ_λ`);
* `soFormQ` (**the code `-1 + e(g)` is `a·J + p`, and `-1 + e(soQ ρ a g) = ρ·J + p`**, `J, p < a`);
* `soRealQ_named` (**`LrReal S a υ_{a+a^a}`** at a named point, from the family below `a`, UPPER at the inner
  restarts, LOWER at their images, `CxStdPairTop`), `soRealQ_M`, `soRealQ_L` (**at `m*` and at every
  `L(n+1)`, given `L(ω) ≤ ν_C`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Lr

variable {S : InaccSeq.{0}}

/-- **`η_{ι(η)+g} = η + g` and `m_{ι(η)+g} = -1 + e(g)`** for `0 < g < P(η)^{P(η)}` (`ω^{Ω₁} ∣ η`). -/
theorem soCode_shiftQ {η g : Ordinal.{0}} (hg : Bt.Good S η) (hdiv : ω ^ Om 1 ∣ η) (hg0 : g ≠ 0)
    (hgP : g < Nm.Pv S η ^ Nm.Pv S η) :
    cdEta S (Bt.iota S η + g) = η + g ∧ cdCode S (Bt.iota S η + g) = cdOff (cdExp g) := by
  have hg1 : g < Om 1 := hgP.trans (soPvPv_lt_Om1 η hg)
  have hι : Bt.iota S (η + g) = Bt.iota S η + g :=
    Pp.ppIota_add η g fun y hy => soGoodQ hg (hy.trans hgP)
  have he : cdEta S (Bt.iota S η + g) = η + g := cdEta_unique (soGoodQ hg hgP) hι
  refine ⟨he, ?_⟩
  unfold cdCode
  rw [he]
  have hexp := Ls.lsExp_add hdiv hg0 hg1
  have h2 : cdExp (η + g) < Om (1 + 1) := by
    rw [hexp]
    exact ((Ls.lsExp_le hg0).trans_lt hg1).trans (Om_lt_Om.2 (lt_add_one 1))
  rw [cdCodeOf_of_lt h2, hexp]

/-- `a·J + q = a·J' + q'` with `q, q' < a` gives `J = J'`, `q = q'`. -/
theorem soDivUniqO {a q q' J J' : Ordinal.{0}} (ha : a ≠ 0) (hq : q < a) (hq' : q' < a)
    (e : a * J + q = a * J' + q') : J = J' ∧ q = q' := by
  have hd : J = J' := by
    have := congrArg (· / a) e
    simp only at this
    rwa [Ordinal.mul_add_div _ ha, Ordinal.mul_add_div _ ha, Ordinal.div_eq_zero_of_lt hq,
      Ordinal.div_eq_zero_of_lt hq', add_zero, add_zero] at this
  have hm : q = q' := by
    have := congrArg (· % a) e
    simp only at this
    rwa [Ordinal.mul_add_mod_self, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hq,
      Ordinal.mod_eq_of_lt hq'] at this
  exact ⟨hd, hm⟩

/-- **`υ_{λ+h} + υ_λ·J + p` determines `h`, `J` and `p`** (`0 < h`, `J, p < υ_λ`). -/
theorem soUps_injO {l h h' J J' p p' : Ordinal.{0}} (hh : 0 < h) (hh' : 0 < h')
    (hJ : J < upsilon l) (hJ' : J' < upsilon l) (hp : p < upsilon l) (hp' : p' < upsilon l)
    (e : upsilon (l + h) + upsilon l * J + p = upsilon (l + h') + upsilon l * J' + p') :
    h = h' ∧ J = J' ∧ p = p' := by
  have hm := upsilon_normal.strictMono
  have hs : ∀ {h J p : Ordinal.{0}}, 0 < h → J < upsilon l → p < upsilon l →
      upsilon l * J + p < upsilon (l + h) := by
    intro h J p hh hJ hp
    have hE : InE (upsilon (l + h)) :=
      upsPt_inE (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_of_pos_right l hh)))
    have hlh : upsilon l < upsilon (l + h) := hm (lt_add_of_pos_right l hh)
    exact hE.add_lt (Sl.slE_mul_lt hE hlh (hJ.trans hlh)) (hp.trans hlh)
  rw [add_assoc, add_assoc] at e
  have hseg := lr_seg_unique (y := upsilon (l + h) + (upsilon l * J + p)) le_self_add
    (Ls.lsUps_add_lt (hs hh hJ hp)) (by rw [e]; exact le_self_add)
    (by rw [e]; exact Ls.lsUps_add_lt (hs hh' hJ' hp'))
  have hhh : h = h' := add_left_cancel hseg
  subst hhh
  have e2 := add_left_cancel e
  have hl0 : upsilon l ≠ 0 := (lt_of_le_of_lt zero_le hp).ne'
  obtain ⟨h1, h2⟩ := soDivUniqO hl0 hp hp' e2
  exact ⟨rfl, h1, h2⟩

/-- **The code form**: `-1 + e(g) = a·J + p` and `-1 + e(soQ ρ a g) = ρ·J + p` (`J, p < a`). -/
theorem soFormQ {a g : Ordinal.{0}} (ha : InE a) (hg0 : 0 < g) (hg : g < a ^ a) :
    ∃ J p, J < a ∧ p < a ∧ cdOff (cdExp g) = a * J + p ∧
      ∀ ρ, InE ρ → soMX a g < ρ → cdOff (cdExp (soQ ρ a g)) = ρ * J + p := by
  have ha1 := soOne_lt_E ha
  have hMa := soMX_lt ha1 g hg
  obtain ⟨E, q, hE, hqa, -, h1, -⟩ := soExpQ ha ha g hg0.ne' hMa
  have hEa : E < a := hE.trans_lt hMa
  have huniq : ∀ ρ, InE ρ → soMX a g < ρ → cdExp (soQ ρ a g) = ρ * E + q := by
    intro ρ hρ hd
    obtain ⟨E', q', -, hqa', -, h1', h2'⟩ := soExpQ ha hρ g hg0.ne' hd
    obtain ⟨hEE, hqq⟩ := soDivUniqO ha.pos.ne' hqa hqa' (h1.symm.trans h1')
    rw [h2', hEE, hqq]
  rcases eq_or_ne E 0 with hE0 | hE0
  · refine ⟨0, cdOff q, ha.pos, (cdOff_le q).trans_lt hqa, by rw [h1, hE0]; simp, fun ρ hρ hd => ?_⟩
    rw [huniq ρ hρ hd, hE0]; simp
  · refine ⟨E, q, hEa, hqa, ?_, fun ρ hρ hd => ?_⟩
    · rw [h1]
      refine soOff_id ((Sl.slE_omega_lt ha).le.trans ?_)
      exact (Ordinal.le_mul_left a (pos_iff_ne_zero.2 hE0)).trans le_self_add
    · rw [huniq ρ hρ hd]
      refine soOff_id ((Sl.slE_omega_lt hρ).le.trans ?_)
      exact (Ordinal.le_mul_left ρ (pos_iff_ne_zero.2 hE0)).trans le_self_add

/-- `a + a^a < b` for `a < b`, `b` an `ε`-number. -/
theorem soAA_lt {a b : Ordinal.{0}} (hb : InE b) (hab : a < b) : a + a ^ a < b :=
  hb.add_lt hab (soE_opow_lt hb hab hab)

/-- **Realizer maps at a named point `a` up to `υ_{a+a^a}`**, along the base renaming `a ↦ ρ_μ`. -/
theorem soRealQ_named {a ηa : Ordinal.{0}} {k : ℕ}
    (hg : Bt.Good S ηa) (hι : Bt.iota S ηa = a) (hP : Nm.Pv S ηa = a) (hdiv : ω ^ Om 1 ∣ ηa)
    (hri : IsRestartIdx a) (hzl : Rz.rzLam < a)
    (hν : a < nuC) (hνβ : upsilon (a + a ^ a) ≤ nuC) (hβL : upsilon (a + a ^ a) < Nc.ncL S (ω + 1))
    (hcof : ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧
      cdCode S μ = Ls.lsG S (k + 1) + 1)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hstd : Cx.CxStdPairTop S) (haL : a ≤ Nc.ncL S (ω + 1)) :
    LrReal S a (upsilon (a + a ^ a)) := by
  have hm := upsilon_normal.strictMono
  have hua : upsilon a = a := by
    have h := Bt.ups_iota S ηa; rw [hι] at h; exact h.trans hP
  have ha1' : a < Om 1 := by rw [← hP]; exact Nm.Pv_lt_Om1 S ηa
  have ha1 : a < Om1 := by rw [Br.Om1_eq]; exact ha1'
  have haE : InE a := by rw [← hP]; exact Sl.slPv_E ηa
  have haO := soOne_lt_E haE
  have haW1 : a ^ a < Om 1 := by
    have := soPvPv_lt_Om1 (S := S) ηa hg; rwa [hP] at this
  have hB0a : cdB0 < a := by
    obtain ⟨μ, hR, -, h2, -⟩ := hcof 0 (pos_iff_ne_zero.2 hri.1)
    refine lt_of_le_of_lt hR.2.1 ?_
    rw [← hua] at h2; exact hm.lt_iff_lt.1 h2
  have hWβ : ω ^ 2 ∣ a ^ a := soW_dvd_aa haE
  have h2 : ω + 1 < ω ^ 2 := by
    have := lr_omega_mul_add_one_lt 1
    rwa [Nat.cast_one, mul_one] at this
  have hinner : ∀ g, g < a ^ a → ω ^ 2 ∣ g → g + ω + 1 < a ^ a := by
    intro g hgβ hgd
    rw [add_assoc]; exact (lr_addL (a := g) h2).trans_le (lr_dvd_add_le hgd hWβ hgβ)
  have hgP : ∀ g, g < a ^ a → g < Nm.Pv S ηa ^ Nm.Pv S ηa := fun g h => by rw [hP]; exact h
  -- the codes at the inner restarts `a + g`
  have hcodeA : ∀ g, 0 < g → g < a ^ a → cdCode S (a + g) = cdOff (cdExp g) := by
    intro g hg0 hgβ
    have := (soCode_shiftQ hg hdiv hg0.ne' (hgP g hgβ)).2
    rwa [hι] at this
  -- the reaches at the inner restarts
  have hrA : ∀ g, 0 < g → g < a ^ a → ω ^ 2 ∣ g →
      cdR S (a + g) = upsilon (a + (g + ω + 1)) + cdOff (cdExp g) := by
    intro g hg0 hgβ hgd
    have hri' : IsRestartIdx (a + g) := ⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le),
      dvd_add hri.2 hgd⟩
    have hC : upsilon (a + g + ω + 1) < nuC := by
      refine lt_of_lt_of_le (hm ?_) hνβ
      rw [add_assoc, add_assoc]; exact lr_addL (a := a) (by rw [← add_assoc]; exact hinner g hgβ hgd)
    have hsh : cdCode S (a + g) ≤ upsilon (a + g) := by
      rw [hcodeA g hg0 hgβ]
      exact (Ls.lsOff_le g hg0.ne').trans (le_add_self.trans hm.le_apply)
    rw [Ls.lsR_short hri' hC hsh, hcodeA g hg0 hgβ]
    unfold cdDelta; simp only [add_assoc]
  have hfh : ∀ ρ, InE ρ → ∀ x, ω ^ 2 ∣ x → soG ρ a (x + ω + 1) = soG ρ a x + ω + 1 := by
    rintro ρ hρ x ⟨q, rfl⟩
    rw [add_assoc, (soOff_cnf haE hρ ∅ (fun d hd => absurd hd (Finset.notMem_empty d))).res q _ h2,
      add_assoc]
  have hreal := soReal_ren (S := S) (l := a) (β := a ^ a) hri (by rw [hua]; exact ha1)
    (by rw [hua]; exact hν) hνβ ?_ ?_ ?_ hstd (by rw [hua]; exact haL)
  · rwa [hua] at hreal
  · -- UPPER at the inner restarts
    intro g hg0 hgβ hgd
    refine hU _ ⟨⟨fun h => hri.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hri.2 hgd⟩,
      hB0a.le.trans le_self_add, (hm (lr_addL (a := a) hgβ)).trans hβL, ?_⟩
      (Or.inl (hzl.le.trans le_self_add))
    rw [hcodeA g hg0 hgβ]
    exact (Ls.lsOff_le g hg0.ne').trans_lt ((hgβ.trans haW1).trans (Lw.lw_Om1_lt_Pp S))
  · -- the form of the inner reaches
    intro g hg0 hgβ hgd
    obtain ⟨j, p, hja, hpa, hcp, -⟩ := soFormQ haE hg0 hgβ
    refine Or.inr ⟨g + ω + 1, j, p, lt_of_le_of_lt zero_le (lt_add_one _), hinner g hgβ hgd,
      by rw [hua]; exact hja, by rw [hua]; exact hpa, ?_⟩
    rw [hrA g hg0 hgβ hgd, hcp, hua]
    exact (add_assoc _ _ _).symm
  · -- the Range restarts, the renaming, the supply and the carry
    intro γ hγ Os hOs
    rw [hua] at hγ
    have hzua : upsilon Rz.rzLam < a := by rw [← hua]; exact hm hzl
    have hMa : Os.sup (fun d => soMX a d) < a :=
      (Finset.sup_lt_iff haE.pos).2 fun d hd => soMX_lt haO d (hOs d hd)
    obtain ⟨μ, hR, hγμ, hμa, hc⟩ := hcof (max γ (max (Os.sup (fun d => soMX a d)) (upsilon Rz.rzLam)))
      (max_lt hγ (max_lt hMa hzua))
    have hγ' : γ < upsilon μ := (le_max_left _ _).trans_lt hγμ
    have hMρ : Os.sup (fun d => soMX a d) < upsilon μ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hγμ
    have hzμ : Rz.rzLam < μ :=
      hm.lt_iff_lt.1 (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hγμ)
    have hμa' : μ < a := by rw [← hua] at hμa; exact hm.lt_iff_lt.1 hμa
    have hρE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hR.1.1))
    have hρW : ω ^ 2 ∣ upsilon μ := soW_dvd_E hρE
    have hρWω : ω ^ 2 ∣ upsilon μ ^ upsilon μ := soW_dvd_aa hρE
    have hOs' : ∀ d ∈ Os, d < a ^ a ∧ soMX a d < upsilon μ := fun d hd =>
      ⟨hOs d hd, (Finset.le_sup (f := fun d => soMX a d) hd).trans_lt hMρ⟩
    have hoff := soOff_cnf haE hρE Os hOs'
    have hμBa : μ + upsilon μ ^ upsilon μ < a :=
      haE.add_lt hμa' (soE_opow_lt haE hμa hμa)
    refine ⟨μ, soG (upsilon μ) a, upsilon μ ^ upsilon μ, hR, hγ', by rw [hua]; exact hμa, hμBa.le,
      hρWω, (soSupQ k hR hc).2, hoff, ?_⟩
    intro g hgO hg0 hgd
    have hgβ := hOs g hgO
    have hgr : soMX a g < upsilon μ := (hOs' g hgO).2
    obtain ⟨j0, p0, hj0, hp0, hcp, hcpρ⟩ := soFormQ haE hg0 hgβ
    have hfeq : soG (upsilon μ) a g = soQ (upsilon μ) a g := soG_eq hgβ
    have hfg := hcpρ (upsilon μ) hρE hgr
    rw [← hfeq] at hfg
    have hpv := Ls.lsPv_range hR
    obtain ⟨hgμ, hιμ, -⟩ := cdEta_spec (S := S) (Order.one_le_iff_ne_zero.2 hR.1.1)
      (cd_lt_iota (η0 := Om ω + Nc.ncPp S * (ω + 1)) (by rw [← Lw.lw_L_eq]; exact hR.2.2.1))
    have hdivμ := Ls.lsDiv_of_code hc
    have hfgB : soG (upsilon μ) a g < upsilon μ ^ upsilon μ := hoff.bd g hgO
    have hfg0 : soG (upsilon μ) a g ≠ 0 := by
      have := hoff.mono (Finset.mem_coe.2 (Finset.mem_insert_self 0 Os))
        (Finset.mem_coe.2 (Finset.mem_insert_of_mem hgO)) hg0
      rw [hoff.zero] at this; exact this.ne'
    have hcM : cdCode S (μ + soG (upsilon μ) a g) = cdOff (cdExp (soG (upsilon μ) a g)) := by
      have := (soCode_shiftQ hgμ hdivμ hfg0 (by rw [hpv]; exact hfgB)).2
      rwa [hιμ] at this
    have hgdW : ω ^ 2 ∣ soG (upsilon μ) a g := by obtain ⟨q, rfl⟩ := hgd; exact hoff.dvd q
    have hriμ : IsRestartIdx (μ + soG (upsilon μ) a g) :=
      ⟨fun h => hR.1.1 (le_antisymm (h ▸ le_self_add) zero_le), dvd_add hR.1.2 hgdW⟩
    have hfW : soG (upsilon μ) a g + ω ^ 2 ≤ upsilon μ ^ upsilon μ := lr_dvd_add_le hgdW hρWω hfgB
    have hμfa : μ + soG (upsilon μ) a g + ω + 1 < a := by
      calc μ + soG (upsilon μ) a g + ω + 1 = μ + (soG (upsilon μ) a g + (ω + 1)) := by
            rw [add_assoc, add_assoc]
        _ < μ + (soG (upsilon μ) a g + ω ^ 2) :=
            lr_addL (a := μ) (lr_addL (a := soG (upsilon μ) a g) h2)
        _ ≤ μ + upsilon μ ^ upsilon μ := lr_addLe (a := μ) hfW
        _ < a := hμBa
    have hCμ : upsilon (μ + soG (upsilon μ) a g + ω + 1) < nuC :=
      ((hm hμfa).trans_eq hua).trans hν
    have hshμ : cdCode S (μ + soG (upsilon μ) a g) ≤ upsilon (μ + soG (upsilon μ) a g) := by
      rw [hcM]; exact (Ls.lsOff_le _ hfg0).trans (le_add_self.trans hm.le_apply)
    have hrμ : cdR S (μ + soG (upsilon μ) a g) =
        upsilon (μ + (soG (upsilon μ) a g + ω + 1)) + (upsilon μ * j0 + p0) := by
      rw [Ls.lsR_short hriμ hCμ hshμ, hcM, hfg]; unfold cdDelta; simp only [add_assoc]
    have hRμ : CdRange S (μ + soG (upsilon μ) a g) := by
      refine ⟨hriμ, hR.2.1.trans le_self_add, ?_, ?_⟩
      · exact ((hm (lt_of_le_of_lt (le_self_add.trans le_self_add) hμfa)).trans_eq hua).trans_le haL
      · rw [hcM]
        refine (Ls.lsOff_le _ hfg0).trans_lt ((hfgB.trans ?_).trans (Lw.lw_Om1_lt_Pp S))
        rw [← hpv]; exact soPvPv_lt_Om1 _ hgμ
    refine ⟨hL _ hRμ (Or.inl (hzμ.le.trans le_self_add)), fun hbig => ?_,
      fun h hhO j p hh0 hjγ hpγ hr => ?_⟩
    · exfalso
      rw [hrA g hg0 hgβ hgd] at hbig
      have hgl : g < a + (g + ω + 1) :=
        lt_of_lt_of_le (lt_of_le_of_lt le_self_add (lt_add_one (g + ω))) le_add_self
      have hcl : cdOff (cdExp g) < upsilon (a + (g + ω + 1)) :=
        (Ls.lsOff_le g hg0.ne').trans_lt (hgl.trans_le hm.le_apply)
      have h1 := Ls.lsUps_add_lt hcl
      have h3 : upsilon (succ (a + (g + ω + 1))) ≤ upsilon (a + a ^ a) := by
        refine hm.monotone ?_
        rw [lr_succ_add]
        exact lr_addLe (a := a) (Order.succ_le_of_lt (hinner g hgβ hgd))
      exact absurd (hbig.trans_lt (h1.trans_le h3)) (lt_irrefl _)
    · have hcp' : cdOff (cdExp g) = upsilon a * j0 + p0 := by rw [hua]; exact hcp
      have e : upsilon (a + (g + ω + 1)) + upsilon a * j0 + p0 =
          upsilon (a + h) + upsilon a * j + p := by
        rw [add_assoc, ← hcp', ← hrA g hg0 hgβ hgd, hr]
      have hpa : p < upsilon a := by rw [hua]; exact hpγ.trans (hγ'.trans hμa)
      have hja : j < upsilon a := by rw [hua]; exact hjγ.trans (hγ'.trans hμa)
      obtain ⟨hh, hj, hpp⟩ := soUps_injO (lt_of_le_of_lt zero_le (lt_add_one _)) hh0
        (by rw [hua]; exact hj0) hja (by rw [hua]; exact hp0) hpa e
      rw [← hh, ← hj, ← hpp, hrμ, hfh _ hρE g hgd, add_assoc]

/-- **The realizers at `m*` up to `υ_{m*+m*^{m*}} < L(1)`**, given `L(ω) ≤ ν_C`. -/
theorem soRealQ_M (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) :
    LrReal S (Nc.ncL S 0) (upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0)) ∧
      upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0) < Nc.ncL S 1 := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsM_named (S := S)
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) 0
  have hm := upsilon_normal.strictMono
  have hb : upsilon (Nc.ncL S 0 + Nc.ncL S 0 ^ Nc.ncL S 0) < Nc.ncL S 1 := by
    have hu1 : upsilon (Nc.ncL S 1) = Nc.ncL S 1 := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; simpa using h.trans hP1
    have hE1 : InE (Nc.ncL S 1) := by
      have := Sl.slPv_E (S := S) (Om ω + Nc.ncPp S * ((0 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; simpa using this
    rw [← hu1]
    exact hm (soAA_lt hE1 (Rl.rlM_lt_L1 (S := S)))
  have hL1w : Nc.ncL S 1 ≤ Nc.ncL S ω := Pp.ppL_mono one_lt_omega0.le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨soRealQ_named hg hι hP hdiv hri hzl ((Rl.rlM_lt_L1 (S := S)).trans_le (hL1w.trans hlow))
    (hb.le.trans (hL1w.trans hlow)) (hb.trans_le hL1w |>.trans hLw1) (Ls.lsNames_M (S := S) 0) hU hL
    hstd (Pp.ppL_mono zero_le), hb⟩

/-- **The realizers at `L(n+1)` up to `υ_{a+a^a} < L(n+2)`**, given `L(ω) ≤ ν_C`. -/
theorem soRealQ_L (hlow : Nc.ncL S ω ≤ nuC)
    (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l) (hstd : Cx.CxStdPairTop S) (n : ℕ) :
    LrReal S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
        (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
            ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) ∧
      upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
          ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) <
        Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
  obtain ⟨hg, hι, hP, hdiv, hri, hzl⟩ := Ls.lsL_named (S := S) n
  obtain ⟨hg1, hι1, hP1, -, -, -⟩ := Ls.lsL_named (S := S) (n + 1)
  have hm := upsilon_normal.strictMono
  have hb : upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})
      ^ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) <
      Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
    have hu1 : upsilon (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) = Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) := by
      have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hι1] at h; exact h.trans hP1
    have hE1 : InE (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0})) := by
      have := Sl.slPv_E (S := S) (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0}))
      rw [hP1] at this; exact this
    rw [← hu1]
    exact hm (soAA_lt hE1 (Pp.ppL_lt_succ (S := S) n))
  have h2w : Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}) ≤ Nc.ncL S ω := (Pp.ppL_lt_omega (n + 1)).le
  have hLw1 : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  refine ⟨soRealQ_named hg hι hP hdiv hri hzl ((Pp.ppL_lt_omega n).trans_le hlow)
    (hb.le.trans (h2w.trans hlow)) ((hb.trans_le h2w).trans hLw1) (Ls.lsNames_L (S := S) n 0) hU hL
    hstd ((Pp.ppL_lt_omega n).le.trans hLw1.le), hb⟩

end Googology.Trans.PoR.InaccPsi.R2.So
