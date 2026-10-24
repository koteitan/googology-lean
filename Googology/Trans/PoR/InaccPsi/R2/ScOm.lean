import Googology.Trans.PoR.InaccPsi.R2.ScSq

/-!
# The reading at the top of a shape: `Θ(ψ_{Ω₂}(β + W^{X₀ + G*})) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ĝ*})`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `SQ_j = Sc.scSq S G X₀ β j`.

**One theorem for every shape** (`scOmTop`).  A shape `G` (code parameters `ζ < Ω₂`, strictly monotone, below its
top `G* = ω^k`) with its image shape `Ĝ` (image parameters `v < Ω₁`, below `Ĝ*`), at a base `β` of `X₀ + G*` with
a reading `Θ(ψ_{Ω₂}(β)) = ψ_{Ω₁}(Â)`, over an offset `(X₀, X̂₀)` (`Rv.RvOff` at `β`).  If
* `G ζ` is in the hull for a code `ζ`, `G` and `Ĝ` keep the closures above the bottom `T_{X₀ + G 1}(β)`;
* the closure law of `G` (`Sc.ScShCl`) and of `Ĝ` (with `Ω₁`) at every strongly critical `Q` above the bottom;
* every hull `r < G*` is below `G(q+1)` for a code `q` with `G q ≤ r` (if `q ≠ 0`) (**the index**);
* the reading at the members: `Θ(T_{X₀ + G ζ}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ĝ(Θ ζ)})` for every code `1 ≤ ζ < T` with
  `Θ ζ < Ω₁`;
then `Θ(T_{X₀ + G*}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ĝ*})`.  The own parameters below the top come from `Sc.scSq_sup`; a
parameter `q ≥ T` never gives an atom below `T` (`Sc.scSq_ge`).  `Rw.rwTopWW` (`G ζ = W^ζ`, `X₀ = 0`) and the
successor step `Rw.rwLevC_succ` (`G ζ = W^E·ζ`) are instances.

* `scOm_codes` (`SQ_j` is a code with `Θ(SQ_j) < Ω₁`), `scOm_own` (every code `ζ < T` is own, `Θ ζ < Ω₁`);
* `scOmTop` (**THE READING AT THE TOP OF A SHAPE**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw

variable {S : InaccSeq.{0}}

section Top

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {G Gh : Ordinal.{0} → Ordinal.{0}} {Gs Ghs X0 Xh0 β Â : Ordinal.{0}}
  (hGst : StrictMono G) (hGs : ∀ x, x < Om (1 + 1) → G x < Gs)
  (hGhs : ∀ v, v < Om 1 → Gh v < Ghs)
  (hoff : RvOff S l β X0 Xh0) (hb : RoBaseE S l (X0 + Gs) 0 β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
  (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1))
  (hGH : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < Om (1 + 1) → G ζ ∈ cdHull S l)
  (hGm : ∀ x c, x ∈ S.CSet 0 c → leTe S (X0 + G 1) β ≤ c → G x ∈ S.CSet 0 c)
  (hcl : ∀ Q, SC Q → leTe S (X0 + G 1) β ≤ Q → ScShCl G Gs Q)
  (hG3 : X0 + Gs < S.psi 0 (Om (1 + 1 + 1)))
  (hsub : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < leTe S (X0 + Gs) β →
    gxTh (upsilon l) (ldAtR S l) ζ < Om 1 →
    gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + G ζ) β) =
      S.psi (Â + leOe (Xh0 + Gh (gxTh (upsilon l) (ldAtR S l) ζ))) (Om 1))

include hl hX hGst hGs hoff hb hÂ hbase hGH hGm hcl hG3 hsub

omit hÂ hbase hcl hG3 in
/-- **`SQ_j` is a code with `Θ(SQ_j) < Ω₁`.** -/
theorem scOm_codes : ∀ j, GxCl (upsilon l) (ldAtR S l) (scSq S G X0 β j) ∧
    gxTh (upsilon l) (ldAtR S l) (scSq S G X0 β j) < Om 1 ∧ scSq S G X0 β j < leTe S (X0 + Gs) β := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨-, hX0H, hX0m, -, -, -⟩ := rvOff_data hoff
  obtain ⟨-, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβA hβown
  have hGs' : ∀ x, x < Om (1 + 1) → G x ≤ Gs := fun x hx => (hGs x hx).le
  have hGm' : ∀ x c, x ∈ S.CSet 0 c → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c → G x ∈ S.CSet 0 c :=
    fun x c hx hc => hGm x c hx (le_trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone (Order.one_le_iff_pos.2 (Om_pos one_ne_zero))))))).1 hc)
  have hlt : ∀ j, scSq S G X0 β j < leTe S (X0 + Gs) β := fun j =>
    (scSq_lt_succ hGst hGs' hβown hX0m hGm' j).trans_le (scSq_le_top hGs' (j + 1))
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_, hlt 0⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ, -⟩ := IHj
    have hjW : scSq S G X0 β j < Om (1 + 1) := scSq_lt_Om2 j
    have hargl : β + leWe (X0 + G (scSq S G X0 β j)) < β + leWe (X0 + Gs) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (hGs _ hjW)))
    have hat : scSq S G X0 β (j + 1) ∈ ldAtR S l :=
      ⟨β + leWe (X0 + G (scSq S G X0 β j)), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (hGH _ hc hjW))),
        hargl.trans hβA, rfl⟩
    refine ⟨GxCl.atom hat, ?_, hlt (j + 1)⟩
    have hj1 : 1 ≤ scSq S G X0 β j := (Order.one_le_iff_pos.2 (Om_pos one_ne_zero)).trans (scSq_Om1_le j)
    have e1 := hsub _ hc hj1 (hlt j) hΘ
    change gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + G (scSq S G X0 β j)) β) < Om 1
    rw [e1]; exact psi_lt Low.InR_Om_one _

omit hÂ hbase in
/-- **Every code `ζ < T` is own, with `Θ ζ < Ω₁`.** -/
theorem scOm_own {ζ : Ordinal.{0}} (hζT : ζ < leTe S (X0 + Gs) β) :
    ζ < S.psi (β + leWe (X0 + G ζ)) (Om (1 + 1)) ∧ gxTh (upsilon l) (ldAtR S l) ζ < Om 1 := by
  obtain ⟨-, -, hX0m, -, hX0cl, -⟩ := rvOff_data hoff
  have hcodes := scOm_codes hl hX hGst hGs hoff hb hGH hGm hsub
  obtain ⟨hβd, -, -, hβown, -⟩ := hb
  rw [add_zero] at hβd hβown
  have hGs' : ∀ x, x < Om (1 + 1) → G x ≤ Gs := fun x hx => (hGs x hx).le
  have hbot : leTe S (X0 + G 1) β ≤ S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone (Order.one_le_iff_pos.2 (Om_pos one_ne_zero))))))).1
  have hGm' : ∀ x c, x ∈ S.CSet 0 c → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c → G x ∈ S.CSet 0 c :=
    fun x c hx hc => hGm x c hx (hbot.trans hc)
  have hcl' : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → ScShCl G Gs Q :=
    fun Q hQ hc => hcl Q hQ (hbot.trans hc)
  obtain ⟨j, hj⟩ := scSq_sup hGst hGs' hβown hX0m hGm' hcl' hβd hX0cl hG3 hζT
  exact ⟨scSq_gt hGst.monotone j ζ hj, (gxTh_mono hj.le).trans_lt (hcodes j).2.1⟩

include hGhs in
/-- **THE READING AT THE TOP OF A SHAPE.** -/
theorem scOmTop {k : Ordinal.{0}} (hk : Gs = ω ^ k)
    (hGhm : ∀ v c, v ∈ S.CSet 0 c → gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + G 1) β) ≤ c → Gh v ∈ S.CSet 0 c)
    (himg : ∀ Q, SC Q → gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + G 1) β) ≤ Q →
      ∀ w, LeCl (Om 1) Q w → w < Om 1 * Ghs → ∃ v, v < Q ∧ w < Om 1 * Gh (v + 1))
    (hidx : ∀ r, r ∈ cdHull S l → r < Gs → ∃ q, GxCl (upsilon l) (ldAtR S l) q ∧ q < Om (1 + 1) ∧
      r < G (q + 1) ∧ (q ≠ 0 → G q ≤ r))
    (hXh0G : Xh0 + Ghs < S.psi 0 (Om (1 + 1))) (hGsH : Gs ∈ cdHull S l) (hdX0 : Gs ∣ X0) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + Gs) β) = S.psi (Â + leOe (Xh0 + Ghs)) (Om 1) := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hown := fun {ζ} (hζT : ζ < leTe S (X0 + Gs) β) =>
    scOm_own hl hX hGst hGs hoff hb hGH hGm hcl hG3 hsub hζT
  obtain ⟨-, hX0H, hX0m, hXh0m, hX0cl, hXh0cl⟩ := rvOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (X0 + Gs) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  set Y := S.psi (Â + leOe (Xh0 + Ghs)) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh0 + Ghs)) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  have hbotT : leTe S (X0 + G 1) β ≤ T :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGs 1 (gg_one_lt_of_SC ldOm2_SC)).le)))).1
  have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ T :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hbot : leTe S (X0 + G 1) β ≤ S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone (Order.one_le_iff_pos.2 (Om_pos one_ne_zero))))))).1
  have hGm' : ∀ x c, x ∈ S.CSet 0 c → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ c → G x ∈ S.CSet 0 c :=
    fun x c hx hc => hGm x c hx (hbot.trans hc)
  have hcl' : ∀ Q, SC Q → S.psi (β + leWe (X0 + G (Om 1))) (Om (1 + 1)) ≤ Q → ScShCl G Gs Q :=
    fun Q hQ hc => hcl Q hQ (hbot.trans hc)
  -- the members `T_{X₀ + G ζ}(β)`, `1 ≤ ζ < T` a code
  have hsubG : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → 1 ≤ ζ → ζ < T →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + G ζ) β) =
        S.psi (Â + leOe (Xh0 + Gh (gxTh (upsilon l) (ldAtR S l) ζ))) (Om 1) ∧
      leTe S (X0 + G ζ) β ∈ ldAtR S l ∧ leTe S (X0 + G ζ) β < T ∧
      S.psi (Â + leOe (Xh0 + Gh (gxTh (upsilon l) (ldAtR S l) ζ))) (Om 1) < Y := by
    intro ζ hζ h1 hζT
    have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
    obtain ⟨hζo, hΘ1⟩ := hown hζT
    have e1 := hsub ζ hζ h1 hζT hΘ1
    have hlt : β + leWe (X0 + G ζ) < β + leWe (X0 + Gs) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (hGs ζ hζW)))
    refine ⟨e1, ⟨β + leWe (X0 + G ζ), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (hGH ζ hζ hζW))),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · have hX0T : X0 ∈ S.CSet (β + leWe (X0 + Gs)) T := CSet_mono zero_le hle0 hX0m
      exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem hX0T (CSet_mono zero_le le_rfl (hGm ζ T (CSet.of_lt hζT) hbotT)))))
    · have hlt2 : Â + leOe (Xh0 + Gh (gxTh (upsilon l) (ldAtR S l) ζ)) < Â + leOe (Xh0 + Ghs) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh0).2 (hGhs _ hΘ1)))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      have hle0ζ : S.psi (β + leWe X0) (Om (1 + 1)) ≤ leTe S (X0 + G ζ) β :=
        (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
      have hbotζ : leTe S (X0 + G 1) β ≤ leTe S (X0 + G ζ) β :=
        (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
          (leWe_mono ((add_le_add_iff_left X0).2 (hGst.monotone h1))))).1
      have hΘζ : gxTh (upsilon l) (ldAtR S l) ζ ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + G ζ) β)) :=
        CSet.of_lt (gxTh_lt hζ hζo)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (CSet_mono zero_le ((gxTh_mono hle0ζ).trans e1.le) hXh0m)
          (CSet_mono zero_le e1.le (hGhm _ _ hΘζ (gxTh_mono hbotζ)))))
  have hsub0 : X0 ≠ 0 → gxTh (upsilon l) (ldAtR S l) (leTe S X0 β) = S.psi (Â + leOe Xh0) (Om 1) ∧
      leTe S X0 β ∈ ldAtR S l ∧ leTe S X0 β < T ∧ S.psi (Â + leOe Xh0) (Om 1) < Y := by
    intro hX00
    obtain ⟨-, ht0⟩ := rvOff_ne hoff hX00
    have e1 := ht0 β Â (roBaseE_shift hb' (by rw [add_zero]; exact le_self_add) zero_le) le_rfl hÂ hbase
    rw [add_zero, gxTh_zero, add_zero] at e1
    have hlt : β + leWe X0 < β + leWe (X0 + Gs) :=
      (add_lt_add_iff_left β).2 (leWe_lt (lt_add_of_pos_right X0 (by
        rw [hk]; exact opow_pos k omega0_pos)))
    refine ⟨e1, ⟨β + leWe X0, CSet.add_mem hβH (leWe_mem hX0H), hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet_mono zero_le hle0 hX0m)))
    · have hlt2 : Â + leOe Xh0 < Â + leOe (Xh0 + Ghs) :=
        (add_lt_add_iff_left Â).2 (leOe_lt (lt_add_of_pos_right Xh0 (zero_le.trans_lt
          (hGhs 0 (Om_pos one_ne_zero)))))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      exact CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet_mono zero_le e1.le hXh0m))
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (X0 + Gs), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H hGsH)), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) T ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd' : d < leWe (X0 + Gs) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X0 + Gs)) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X0 + Gs)) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X0 + Gs) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd']
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X0 + Gs) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd')
    have hxW : x < X0 + Gs := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    have hWx : leWe x ≤ d := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
    rcases lt_or_ge x X0 with hxX | hxX
    · have hX00 : X0 ≠ 0 := (zero_le.trans_lt hxX).ne'
      obtain ⟨e1, -, -, hY1⟩ := hsub0 hX00
      have hdX : d < leWe X0 := hdx.trans_le (leWe_mono (Order.add_one_le_of_lt hxX))
      refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 hdX.le)).1) ?_
      change gxTh (upsilon l) (ldAtR S l) (leTe S X0 β) < Y
      rw [e1]; exact hY1
    obtain ⟨r, hr_def⟩ := exists_add_of_le hxX
    have hr : r < Gs := by
      have : X0 + r < X0 + Gs := by rw [← hr_def]; exact hxW
      exact (add_lt_add_iff_left X0).1 this
    have hrH : r ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) k hxH
      have hm : x % ω ^ k = r := by
        obtain ⟨q', hq'⟩ := hdX0
        rw [hr_def, ← hk, hq', Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
      rwa [hm] at h1
    obtain ⟨q, hqc, hqW, hrq, hGq⟩ := hidx r hrH hr
    have hqT : q < T := by
      by_contra h
      push Not at h
      have hq0 : q ≠ 0 := fun h0 => absurd (h0 ▸ h) (not_le.2 hTSC0.1)
      have h1 := scSq_ge hGst (fun x hx => (hGs x hx).le) hβown hX0m hGm' hcl' hβd hX0cl hG3 h
      have h2 : leWe (X0 + G q) ≤ d := by
        refine (leWe_mono ?_).trans hWx
        rw [hr_def]; exact (add_le_add_iff_left X0).2 (hGq hq0)
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h2)).1)
        (not_le.2 hts)
    have hq1T := hTSC0.isSuccLimit.succ_lt hqT
    have hq1c := rqCode_succ hl hX hqc (hq1T.trans (leTe_lt_Om2 _ _))
    have hdq : d < leWe (X0 + G (q + 1)) := by
      refine hdx.trans_le (leWe_mono (Order.add_one_le_of_lt ?_))
      rw [hr_def]; exact (add_lt_add_iff_left X0).2 hrq
    obtain ⟨e1, -, -, hY1⟩ := hsubG _ hq1c le_add_self hq1T
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdq.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < Y
    rw [e1]; exact hY1
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < T :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  refine lePsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Xh0 + Ghs) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * (Xh0 + Ghs)) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (Xh0 + Ghs)) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hXh0G).2] at hc2
  have hmod : (Â + r) % leOe (Xh0 + Ghs) = Â % leOe (Xh0 + Ghs) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Xh0 + Ghs) + r with hy_def
  have hyP : y < leOe (Xh0 + Ghs) :=
    isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have hlogy : w < Om 1 * Xh0 + Om 1 * Ghs := by
    rw [← mul_add]
    exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hylt := lt_opow_succ_log_self one_lt_omega0 y
  rw [Order.succ_eq_add_one] at hylt
  obtain ⟨-, hlogC⟩ := leClDec hTSC Ph.ph_SC_Om1 y hc2
  rcases lt_or_ge w (Om 1 * Xh0) with h1 | h1
  · have hXh00 : Xh0 ≠ 0 := by rintro rfl; rw [mul_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    have hX00 : X0 ≠ 0 := (rvOff_neh hoff hXh00).1.ne
    obtain ⟨e1, hat1, hlt1, -⟩ := hsub0 hX00
    have hrg : r ≤ leOe Xh0 :=
      hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))).le
    refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
    rw [← e1]
    exact hTs _ hat1 hlt1
  have hXC := LeCl.mulK hTSC Ph.ph_SC_Om1 Xh0 (hXh0cl _ hTSC (gxTh_mono hle0))
  have hu := (leClDec hTSC Ph.ph_SC_Om1 w hlogC).1 _ hXC h1
  have hdec : Om 1 * Xh0 + (w - Om 1 * Xh0) = w := Ordinal.add_sub_cancel_of_le h1
  have hu2 : w - Om 1 * Xh0 < Om 1 * Ghs := by
    have : Om 1 * Xh0 + (w - Om 1 * Xh0) < Om 1 * Xh0 + Om 1 * Ghs := by rw [hdec]; exact hlogy
    exact (add_lt_add_iff_left _).1 this
  obtain ⟨v, hvQ, hv⟩ := himg _ hTSC (gxTh_mono hbotT) _ hu hu2
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hvQ
  have hg1T := hTSC0.isSuccLimit.succ_lt hgT
  have hg1c := rqCode_succ hl hX hgc (hg1T.trans (leTe_lt_Om2 _ _))
  have hΘg1 : gxTh (upsilon l) (ldAtR S l) (g + 1) = v + 1 := by rw [rqTh_succ hl hX hgc, hgx]
  have key : w + 1 ≤ Om 1 * (Xh0 + Gh (gxTh (upsilon l) (ldAtR S l) (g + 1))) := by
    rw [hΘg1, mul_add, ← hdec, add_assoc]
    exact (add_le_add_iff_left _).2 (Order.add_one_le_of_lt hv)
  have hrg : r ≤ leOe (Xh0 + Gh (gxTh (upsilon l) (ldAtR S l) (g + 1))) :=
    hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos key)).le
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG (g + 1) hg1c le_add_self hg1T
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1
end Top

end Googology.Trans.PoR.InaccPsi.R2.Sc
