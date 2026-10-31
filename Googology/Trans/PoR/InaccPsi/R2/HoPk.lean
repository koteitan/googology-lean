import Googology.Trans.PoR.InaccPsi.R2.HoStep

/-!
# HoPk: ONE RECURSION OF THE PREFIX PACKAGES `Ω₁²·(1+ν)`, `ν < Ω₁`

The package at the prefix `Ω₁²·(1+ν)` (read `x·x·(1+ν)` above the gate `hlGt (1+ν)`), by one recursion on `ν`:
`ν = 0` is `Hn.hnPkSq` (the level `Ω₁·Ω₁`); the successor is `Ho.hoPkNx` (the union of the band packages of the
previous prefix at every pseudo-base); at a limit `λ` the limit package `Ho.hoPkL` of the coherent sequence at
`heFs λ k` (prefix data `hoLv (1+λ) 0`).  Later packages extend earlier ones (`Hn.HnkExt`).

* `ho_ext_trans` (the extension statement composes), `HoPInv`, `hoPSucc`, `HoPCoh`, `hoPSeqOf`, `hoPLimF`;
* `hoKp ν` (**THE PREFIX PACKAGES**), `hoKp_inv` (**THE INVARIANT**), `hoKp_lim_Λ`.

No new axiom.  New definitions: `HoPInv`, `hoPSucc`, `HoPCoh`, `hoPSeqOf`, `hoPLimF`, `hoKp`.
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

/-- **The extension statement composes.** -/
theorem ho_ext_trans {K1 K2 K3 : HnPk} (h12 : HnkExt K1 K2) (h23 : HnkExt K2 K3) (g12 : K1.Λ.g ≤ K2.Λ.g)
    (L12 : K1.Λ.L + Om1 ≤ K2.Λ.L) (l12 : ∀ x, InE x → x < Om1 → K2.Λ.g < x → K1.Λ.l x + x ≤ K2.Λ.l x)
    (g23 : K2.Λ.g ≤ K3.Λ.g) (L23 : K2.Λ.L + Om1 ≤ K3.Λ.L)
    (l23 : ∀ x, InE x → x < Om1 → K3.Λ.g < x → K2.Λ.l x + x ≤ K3.Λ.l x) : HnkExt K1 K3 := by
  intro hg hL hl Q U hU c x hc
  have hB1 := (K1.h0 (Q.lowr K1.Λ hg hL hl) U hU).B
  have hB2 := (K2.h0 (Q.lowr K2.Λ g23 L23 l23) U hU).B
  have hc2 : c < (K2.St0 (Q.lowr K2.Λ g23 L23 l23) U hU).B := by
    rw [hB2]; rw [hB1] at hc
    exact hc.trans_le (hdNx_mono (add_le_add (le_self_add.trans L12) le_rfl) _)
  obtain ⟨r2, g2⟩ := h23 g23 L23 l23 Q U hU c x hc2
  obtain ⟨r1, g1⟩ := h12 g12 L12 l12 (Q.lowr K2.Λ g23 L23 l23) U hU c x hc
  exact ⟨r2.trans r1, g2.trans g1⟩

/-- **`a·a·p + a ≤ a·a·q`** for `p < q`. -/
theorem ho_sq_step {a p q : Ordinal.{0}} (hpq : p < q) : a * a * p + a ≤ a * a * q :=
  calc a * a * p + a ≤ a * a * p + a * a := add_le_add le_rfl (hn_le_sq a)
  _ = a * a * (p + 1) := (mul_add_one _ _).symm
  _ ≤ a * a * q := mul_le_mul_left' (Order.add_one_le_of_lt hpq) _

theorem ho_hlGt1 : hlGt (1 + 0) = 0 := by
  rw [add_zero]; unfold hlGt
  rw [if_pos (one_lt_omega0.trans (omega0_lt_inE hc_eps0_E))]

theorem ho_1l_eq {l : Ordinal.{0}} (hl : IsSuccLimit l) : 1 + l = l :=
  one_add_of_omega0_le (omega0_le_of_isSuccLimit hl)

/-! ## The invariant of a prefix package -/

/-- **A package of the prefix `Ω₁²·(1+ν)`**: level `Ω₁²·(1+ν)`, read `x·x·(1+ν)` above its gate `hlGt (1+ν)`. -/
def HoPInv (ν : Ordinal.{0}) (K : HnPk) : Prop :=
  K.Λ.L = Om1 * Om1 * (1 + ν) ∧ (∀ x, K.Λ.g < x → K.Λ.l x = x * x * (1 + ν)) ∧ K.Λ.g = hlGt (1 + ν)

theorem hoPInv_rel {ν' ν : Ordinal.{0}} {K' K : HnPk} (h' : HoPInv ν' K') (h : HoPInv ν K) (hlt : ν' < ν) :
    K'.Λ.g ≤ K.Λ.g ∧ K'.Λ.L + Om1 ≤ K.Λ.L ∧ ∀ x, InE x → x < Om1 → K.Λ.g < x → K'.Λ.l x + x ≤ K.Λ.l x := by
  have hg : K'.Λ.g ≤ K.Λ.g := by rw [h'.2.2, h.2.2]; exact hlGt_mono (add_le_add le_rfl hlt.le)
  refine ⟨hg, by rw [h'.1, h.1]; exact ho_sq_step ((add_lt_add_iff_left 1).2 hlt), fun x _ _ hx => ?_⟩
  rw [h'.2.1 x (hg.trans_lt hx), h.2.1 x hx]; exact ho_sq_step ((add_lt_add_iff_left 1).2 hlt)

open Classical in
/-- **The successor case**: the next prefix package (when the invariant holds). -/
noncomputable def hoPSucc (ν : Ordinal.{0}) (K : HnPk) : HnPk :=
  if h : 1 + ν < Om1 ∧ HoPInv ν K then hoPkNx le_self_add h.1 K h.2.1 h.2.2.1 h.2.2.2 else K

/-- **The condition at a limit**: the earlier packages have the invariant and extend each other. -/
def HoPCoh (l : Ordinal.{0}) (IH : ∀ ν, ν < l → HnPk) : Prop :=
  (∀ ν (h : ν < l), HoPInv ν (IH ν h)) ∧ ∀ ν' ν (h' : ν' < l) (h : ν < l), ν' < ν → HnkExt (IH ν' h') (IH ν h)

/-- **The coherent sequence of prefix packages at a limit `λ < Ω₁`**, below the prefix datum `hoLv (1+λ) 0`. -/
noncomputable def hoPSeqOf (l : Ordinal.{0}) (hl : IsSuccLimit l) (hle : l < Om1) (IH : ∀ ν, ν < l → HnPk)
    (H : HoPCoh l IH) : HoSeq (hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos) where
  K := fun k => IH (heFs l k) (heFs_lt hl (hl_om hle) k)
  Kg := fun k => by
    rw [(H.1 _ _).2.2]
    exact le_max_of_le_left (hlGt_mono (add_le_add le_rfl (heFs_lt hl (hl_om hle) k).le))
  Kgm := fun k => by
    rw [(H.1 _ _).2.2, (H.1 _ _).2.2]
    exact hlGt_mono (add_le_add le_rfl (heFs_mono hl (hl_om hle) k).le)
  hL := fun k => by
    rw [(H.1 _ _).1, hoLv_L0]; exact ho_sq_step ((add_lt_add_iff_left 1).2 (heFs_lt hl (hl_om hle) k))
  hl := fun k x _ _ hg => by
    have hgk : (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).Λ.g < x := by
      rw [(H.1 _ _).2.2]
      exact (le_max_of_le_left (hlGt_mono (add_le_add le_rfl (heFs_lt hl (hl_om hle) k).le)) :
        hlGt (1 + heFs l k) ≤ max (hlGt (1 + l)) (hlGt 0)).trans_lt hg
    rw [(H.1 _ _).2.1 x hgk, hoLv_l0 _ _ hg]
    exact ho_sq_step ((add_lt_add_iff_left 1).2 (heFs_lt hl (hl_om hle) k))
  hLs := fun k => by
    rw [(H.1 _ _).1, (H.1 _ _).1]; exact ho_sq_step ((add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k))
  hls := fun k x _ _ hg => by
    have hgk : (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).Λ.g < x := by
      rw [(H.1 _ _).2.2]; rw [(H.1 _ _).2.2] at hg
      exact (hlGt_mono (add_le_add le_rfl (heFs_mono hl (hl_om hle) k).le)).trans_lt hg
    rw [(H.1 _ _).2.1 x hgk, (H.1 _ _).2.1 x hg]
    exact ho_sq_step ((add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k))
  cofL := fun b hb => by
    rw [hoLv_L0] at hb
    obtain ⟨k, hk⟩ := hk_mul_cof1 (Ms := fun k => 1 + heFs l k) ho_OO_pos
      (fun k => (add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k))
      (fun t ht => by
        rw [ho_1l_eq hl] at ht
        obtain ⟨k, hk⟩ := heFs_cof hl (hl_om hle) t ht
        exact ⟨k, hk.trans_le le_add_self⟩) hb
    exact ⟨k, by rw [(H.1 _ _).1]; exact hk⟩
  cofl := fun x hx _ hg b hb => by
    rw [hoLv_l0 _ _ hg] at hb
    obtain ⟨k, hk⟩ := hk_mul_cof1 (Ms := fun k => 1 + heFs l k) (mul_pos hx.pos hx.pos)
      (fun k => (add_lt_add_iff_left 1).2 (heFs_mono hl (hl_om hle) k))
      (fun t ht => by
        rw [ho_1l_eq hl] at ht
        obtain ⟨k, hk⟩ := heFs_cof hl (hl_om hle) t ht
        exact ⟨k, hk.trans_le le_add_self⟩) hb
    refine ⟨k, ?_⟩
    have hgk : (IH (heFs l k) (heFs_lt hl (hl_om hle) k)).Λ.g < x := by
      rw [(H.1 _ _).2.2]
      exact (le_max_of_le_left (hlGt_mono (add_le_add le_rfl (heFs_lt hl (hl_om hle) k).le)) :
        hlGt (1 + heFs l k) ≤ max (hlGt (1 + l)) (hlGt 0)).trans_lt hg
    rw [(H.1 _ _).2.1 x hgk]; exact hk
  ext := fun k => H.2 _ _ _ _ (heFs_mono hl (hl_om hle) k)

open Classical in
/-- **The limit case**: the limit package of the coherent sequence (when `λ < Ω₁` and the condition holds). -/
noncomputable def hoPLimF (l : Ordinal.{0}) (hl : IsSuccLimit l) (IH : ∀ ν, ν < l → HnPk) : HnPk :=
  if h : l < Om1 ∧ HoPCoh l IH then hoPkL (hoPSeqOf l hl h.1 IH h.2) else hnPkSq

/-- **THE PACKAGES OF ALL PREFIXES `Ω₁²·(1+ν)`, BY ONE RECURSION ON `ν`.** -/
noncomputable def hoKp (ν : Ordinal.{0}) : HnPk :=
  Ordinal.limitRecOn (motive := fun _ => HnPk) ν hnPkSq hoPSucc hoPLimF

theorem hoKp_zero : hoKp 0 = hnPkSq := by unfold hoKp; rw [Ordinal.limitRecOn_zero]

theorem hoKp_succ (ν : Ordinal.{0}) : hoKp (ν + 1) = hoPSucc ν (hoKp ν) := by
  unfold hoKp; rw [Ordinal.limitRecOn_add_one]

theorem hoKp_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) : hoKp l = hoPLimF l hl (fun ν _ => hoKp ν) := by
  unfold hoKp; rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

theorem hoPInv_sq : HoPInv 0 hnPkSq := by
  refine ⟨?_, fun x _ => ?_, ?_⟩
  · show Om1 * Om1 = _; rw [add_zero, mul_one]
  · show x * x = _; rw [add_zero, mul_one]
  · show (0 : Ordinal.{0}) = _; rw [ho_hlGt1]

/-- **THE INVARIANT**: for every `ν < Ω₁` the package `hoKp ν` is a package of the prefix `Ω₁²·(1+ν)`, and it extends
every `hoKp ν'`, `ν' < ν`. -/
theorem hoKp_inv : ∀ ν, ν < Om1 → HoPInv ν (hoKp ν) ∧ ∀ ν', ν' < ν → HnkExt (hoKp ν') (hoKp ν) := by
  intro ν
  induction ν using WellFoundedLT.induction with
  | ind ν IH =>
  intro hν
  rcases zero_or_succ_or_isSuccLimit ν with h0 | ⟨μ, hμ⟩ | hlim
  · subst h0
    rw [hoKp_zero]
    exact ⟨hoPInv_sq, fun ν' h => absurd h (not_lt.2 zero_le)⟩
  · have hμ' : ν = μ + 1 := by rw [← hμ, succ_eq_add_one]
    subst hμ'
    have hμ1 : μ < Om1 := (lt_add_one μ).trans hν
    obtain ⟨hinv, hext⟩ := IH μ (lt_add_one μ) hμ1
    have h1 : 1 + μ < Om1 := hl_one_add hμ1
    have e : hoKp (μ + 1) = hoPkNx le_self_add h1 (hoKp μ) hinv.1 hinv.2.1 hinv.2.2 := by
      rw [hoKp_succ]; unfold hoPSucc; rw [dif_pos ⟨h1, hinv⟩]
    have hinv' : HoPInv (μ + 1) (hoKp (μ + 1)) := by
      rw [e]
      refine ⟨?_, fun x hx => ?_, ?_⟩
      · show (hoNxLv h1).L = _; rw [hoNx_L, add_assoc]
      · show (hoNxLv h1).l x = _; rw [hoNx_l h1 x hx, add_assoc]
      · show (hoNxLv h1).g = _; rw [hoNx_g, add_assoc]
    refine ⟨hinv', fun ν' hν' => ?_⟩
    have hN : HnkExt (hoKp μ) (hoKp (μ + 1)) := by rw [e]; exact hoPkNx_ext le_self_add h1 _ _ _ _
    rcases (Order.lt_add_one_iff.1 hν').lt_or_eq with hlt | heq
    · obtain ⟨g12, L12, l12⟩ := hoPInv_rel (IH ν' (hlt.trans (lt_add_one μ)) (hlt.trans hμ1)).1 hinv hlt
      obtain ⟨g23, L23, l23⟩ := hoPInv_rel hinv hinv' (lt_add_one μ)
      exact ho_ext_trans (hext ν' hlt) hN g12 L12 l12 g23 L23 l23
    · subst heq; exact hN
  · have hcoh : HoPCoh ν (fun ν' _ => hoKp ν') :=
      ⟨fun ν' h => (IH ν' h (h.trans hν)).1, fun ν₁ ν₂ h₁ h₂ h12 => (IH ν₂ h₂ (h₂.trans hν)).2 ν₁ h12⟩
    have e : hoKp ν = hoPkL (hoPSeqOf ν hlim hν (fun ν' _ => hoKp ν') hcoh) := by
      rw [hoKp_limit hlim]; unfold hoPLimF; rw [dif_pos ⟨hν, hcoh⟩]
    have hinv : HoPInv ν (hoKp ν) := by
      rw [e]
      refine ⟨hoLv_L0 le_self_add (hl_one_add hν), fun x hx => hoLv_l0 le_self_add (hl_one_add hν) hx, ?_⟩
      show max (hlGt (1 + ν)) (hlGt 0) = _
      rw [ho_hlGt0, max_eq_left zero_le]
    refine ⟨hinv, fun ν' hν' => ?_⟩
    obtain ⟨k, hk⟩ := heFs_cof hlim (hl_om hν) ν' hν'
    have hkl := heFs_lt hlim (hl_om hν) k
    obtain ⟨hinvk, hextk⟩ := IH _ hkl (hkl.trans hν)
    have hN : HnkExt (hoKp (heFs ν k)) (hoKp ν) := by
      rw [e]; exact hoPkL_ext (hoPSeqOf ν hlim hν (fun ν' _ => hoKp ν') hcoh) k
    obtain ⟨g12, L12, l12⟩ := hoPInv_rel (IH ν' hν' (hν'.trans hν)).1 hinvk hk
    obtain ⟨g23, L23, l23⟩ := hoPInv_rel hinvk hinv hkl
    exact ho_ext_trans (hextk ν' hk) hN g12 L12 l12 g23 L23 l23

theorem hoKp_lim_Λ {l : Ordinal.{0}} (hl : IsSuccLimit l) (hle : l < Om1) :
    (hoKp l).Λ = hoLv (1 + l) 0 le_self_add (hl_one_add hle) gv_Om1_pos := by
  have hcoh : HoPCoh l (fun ν' _ => hoKp ν') :=
    ⟨fun ν' h => (hoKp_inv ν' (h.trans hle)).1, fun _ _ _ h₂ h12 => (hoKp_inv _ (h₂.trans hle)).2 _ h12⟩
  rw [hoKp_limit hl]; unfold hoPLimF; rw [dif_pos ⟨hle, hcoh⟩]; rfl

end Googology.Trans.PoR.InaccPsi.R2.Ho
