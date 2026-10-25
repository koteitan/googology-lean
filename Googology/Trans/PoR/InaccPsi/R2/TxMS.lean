import Googology.Trans.PoR.InaccPsi.R2.TxNode

/-!
# Every limit exponent below `G = φ(Ω₂, 1)` has a member system

`Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `log_W = Sg.sgLW`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`, member systems
`Tu.TuMA`, `Tu.TuMB`.

* `txMS` (**EVERY LIMIT EXPONENT `e + r < G` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM**): one induction
  on `r`; off the nodes along the base-`Ω₂` normal form as in `Tu.tuMS`, at a node `r = φ(a, Ω₂ + z) = W^r` by
  `Tx.txNodeMS` (with the induction hypothesis at the argument `z < r`) and the lift `Tx.txMA_lift` /
  `Tx.txMB_lift`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg
  Googology.Trans.PoR.InaccPsi.R2.Tj Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **EVERY LIMIT EXPONENT `e + r < G` OF `H_λ` (`W^{log_W r + 1} ∣ e`) HAS A MEMBER SYSTEM**, Veblen nodes
included. -/
theorem txMS : ∀ r, r ∈ cdHull S l → IsSuccLimit r → ∀ e, e ∈ cdHull S l →
    e + r < veblen (Om (1 + 1)) 1 → leWe (sgLW r + 1) ∣ e → TuMA S l (e + r) ∨ TuMB S l (e + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hrlim e heH hlt hd
  have hrE : r < veblen (Om (1 + 1)) 1 := le_add_self.trans_lt hlt
  have hr0 : 0 < r := hrlim.bot_lt
  by_cases hs : sgLW r < r
  swap
  · -- `r` is a node `φ(a, Ω₂ + z)`: the members of the node, lifted to `e + W^r = e + r`
    obtain ⟨a, z, hre, h1a, haW, hz1, hzr, haH, hzH, -⟩ := txNode hl hX hrH hr0 hrE hs
    have hzr' : z < r := le_add_self.trans_lt hzr
    have hN := txNodeMS hl hX haH h1a haW hzH hz1 (hre ▸ hrE) (fun hzl => by
      have h := IH z hzr' hzH hzl 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hzr'.trans hrE) (dvd_zero _)
      rwa [zero_add] at h)
    rw [← hre] at hN
    obtain ⟨hWr, hgr⟩ := txNode_W (zero_lt_one.trans_le h1a).ne' hz1
    rw [← hre] at hWr hgr
    rw [hgr] at hd
    have hdr : leWe r ∣ e := (leWe_dvd le_self_add).trans hd
    have hlt' : e + leWe r < veblen (Om (1 + 1)) 1 := by rw [hWr]; exact hlt
    rcases hN with hA | hB
    · have h := txMA_lift hl hX heH hrH hdr hlt' hA
      rw [hWr] at h; exact Or.inl h
    · have h := txMB_lift hl hX heH hrH hdr hlt' hB
      rw [hWr] at h; exact Or.inr h
  obtain ⟨hfH, -, hcc, hc1, hcW, hr'H, hr'f, hrdec, -, -⟩ := txParts hl hX hrH hr0 hrE
  set f := sgLW r with hf_def
  set c := r / leWe f with hc_def
  set r' := r % leWe f with hr'_def
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hcc
  have hdf : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hrc : r = leWe f * c := by rw [hr'0, add_zero] at hrdec; exact hrdec
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c1, hcs⟩ | hclim
    · exact absurd hc1 (by rw [h0]; exact not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hcs
      have hc1W : c1 < Om (1 + 1) := (lt_add_one c1).trans (hcs ▸ hcW)
      have hc1c : GxCl (upsilon l) (ldAtR S l) c1 := rqCode_pred hl hX (hcs ▸ hcc) (hcs ▸ hcW)
      have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1c
      have he2H : e + leWe f * c1 ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hc1H)
      have he2r : e + leWe f * c1 + leWe f = e + r := by rw [hrc, ← hcs, mul_add_one, add_assoc]
      have hd2 : leWe f ∣ e + leWe f * c1 := dvd_add hdf (dvd_mul_right _ _)
      have hlt2 : e + leWe f * c1 + leWe f < veblen (Om (1 + 1)) 1 := he2r ▸ hlt
      rw [← he2r]
      rcases zero_or_succ_or_isSuccLimit f with hf0 | ⟨f1, hfs⟩ | hflim
      · exfalso
        have hrc1 : r = c1 + 1 := by rw [hrc, hf0, leWe_zero, one_mul, ← hcs]
        have h := hrlim.succ_lt (show c1 < r from hrc1 ▸ lt_add_one c1)
        rw [Order.succ_eq_add_one, ← hrc1] at h
        exact lt_irrefl _ h
      · rw [succ_eq_add_one] at hfs
        have hf1H : f1 ∈ cdHull S l := mem_of_add_one_mem (hfs ▸ hfH)
        rw [← hfs] at hd2 hlt2 he2H ⊢
        exact Or.inr (txMB_succ hl hX he2H hf1H hd2 hlt2)
      · have hMSf := IH f hs hfH hflim 0 (CSet.zero_mem _ _) (by rw [zero_add]; exact hs.trans hrE)
          (dvd_zero _)
        rw [zero_add] at hMSf
        rcases hMSf with hA | hB
        · exact Or.inl (txMA_lift hl hX he2H hfH hd2 hlt2 hA)
        · exact Or.inr (txMB_lift hl hX he2H hfH hd2 hlt2 hB)
    · rw [hrc] at hlt ⊢
      exact Or.inl (txMA_coef hl hX heH hfH hcc hclim hcW hd hlt)
  · have hr'lim : IsSuccLimit r' := by
      rcases zero_or_succ_or_isSuccLimit r' with h0 | ⟨r1, hr1⟩ | hl'
      · exact absurd h0 hr'0
      · exfalso
        rw [succ_eq_add_one] at hr1
        have hr2 : r = leWe f * c + r1 + 1 := by rw [add_assoc, hr1]; exact hrdec
        have h := hrlim.succ_lt (show leWe f * c + r1 < r from hr2 ▸ lt_add_one _)
        rw [Order.succ_eq_add_one, ← hr2] at h
        exact lt_irrefl _ h
      · exact hl'
    have hs' : sgLW r' < f := tuLogW_lt hr'0 hr'f
    have he2 : e + leWe f * c + r' = e + r := by
      conv_rhs => rw [hrdec]
      rw [add_assoc]
    have hr'r : r' < r := hr'f.trans_le (sgLW_le hr0)
    have h := IH r' hr'r hr'H hr'lim (e + leWe f * c) (CSet.add_mem heH (leMulWe_mem hfH hcH))
      (he2 ▸ hlt) ((leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_add hdf (dvd_mul_right _ _)))
    rwa [he2] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tx
