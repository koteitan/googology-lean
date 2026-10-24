import Googology.Trans.PoR.InaccPsi.R2.GiRS

/-!
# THE UNIFORMITY THEOREM FOR A READING SYSTEM: the top of the layer of every code `c ∈ [ε_{Ω₁+1}, B)` reads the atom
`Γ_{Ω₁+1+c}`

For a reading system `RS : GiRS` (`R2.GiRS`), with the atoms of its code system `RS.K`:

* `GiRS.giK_gfAt`, `GiRS.gfCl_of_giK`, `GiRS.giTh_eq_gf` (**below `Γ_{Ω₁+1+ε_{Ω₁+1}}` the readings with the atoms of
  `RS.K` are those with `Gf.gfAt`**, the gate being `gtc` below `ε_{Ω₁+1}`);
* `GiRS.giEB_codes` (**the code `ε_{Ω₁+1}`**: the union `Gh.ghEB` of all `Gf.gfB c` reads `Γ_{Ω₁+1+ε_{Ω₁+1}}`, by
  `giU_codes` and `Gf.gfB_codes`);
* `GiRS.GiLC`, `GiRS.giL_codes` (**THE UNIFORMITY THEOREM**: one induction on the code; for every
  `c ∈ [ε_{Ω₁+1}, B)` the top of `RS.giL c` reads `Γ_{Ω₁+1+c}` at every strongly critical `y` above the gate of `c`,
  and `RS.giL c` has terms for every code below it over every base above the gate).

No new axiom.  New definition: `GiRS.GiLC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gi

open Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Gf Googology.Trans.PoR.InaccPsi.R2.Gh
open Ordinal Order Set Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ga

namespace GiRS

variable (RS : GiRS)

/-! ## Below `Γ_{Ω₁+1+ε_{Ω₁+1}}` -/

theorem giK_gfAt (Z : Ordinal.{0}) : gfAt Z ⊆ RS.K.At Z := by
  rintro s ⟨c, hc, hg, rfl⟩
  exact ⟨c, hc.trans RS.E_lt, by show RS.K.gt c < Z; rw [RS.gt_lowE c hc]; exact hg, rfl⟩

theorem gfCl_of_giK {Z x : Ordinal.{0}} (hx : GxCl Z (RS.K.At Z) x) : x < gfV → GxCl Z (gfAt Z) x := by
  induction hx with
  | small h => exact fun _ => GxCl.small h
  | om => exact fun _ => GxCl.om
  | @atom s hs =>
    intro h
    obtain ⟨c, -, hgc, rfl⟩ := hs
    have hcE : c < gfE := gcG_lt_iff.1 h
    have hgc' : RS.K.gt c < Z := hgc
    rw [RS.gt_lowE c hcE] at hgc'
    exact GxCl.atom (gfG_atom hcE hgc')
  | @add x y _ _ ihx ihy =>
    exact fun h => GxCl.add (ihx (lt_of_le_of_lt le_self_add h)) (ihy (lt_of_le_of_lt le_add_self h))
  | @phi x y _ _ ihx ihy =>
    exact fun h => GxCl.phi (ihx (lt_of_le_of_lt (left_le_veblen x y) h))
      (ihy (lt_of_le_of_lt (right_le_veblen x y) h))

/-- **`Θ_y` with the atoms of `RS.K` is `Θ_y` with `Gf.gfAt` up to `Γ_{Ω₁+1+ε_{Ω₁+1}}`.** -/
theorem giTh_eq_gf {y c : Ordinal.{0}} (hc : c ≤ gfV) : gxTh y (RS.K.At y) c = gxTh y (gfAt y) c :=
  ggOtp_congr c fun _ hx => ⟨fun h => RS.gfCl_of_giK h (hx.trans_le hc), fun h => h.mono le_rfl (RS.giK_gfAt y)⟩

/-- **The code `ε_{Ω₁+1}`** reads `Γ_{Ω₁+1+ε_{Ω₁+1}}` with the atoms of `RS.K`. -/
theorem giEB_codes (S : InaccSeq.{0}) :
    (∀ y, SC y → y < Om 1 → ghEB.K.E y = gxTh y (RS.K.At y) (gcG gfE)) ∧ GiPolyG RS.K ghEB.K.sys (gcG gfE) := by
  have hK : ∀ (i : ghF0.I) y, SC y → y < Om 1 → ghF0.gi i < y →
      (ghF0.K i).K.E y = gxTh y (RS.K.At y) (gcG (1 + i.1)) := fun i y hy hy1 hi => by
    rw [RS.giTh_eq_gf (gfT_le i.2)]
    exact (gfB_codes S i.1 i.2).1 y hy hy1 hi
  have hKP : ∀ i : ghF0.I, GiPolyG RS.K (ghF0.K i).K.sys (gcG (1 + i.1)) := fun i Z d hg hd hdE => by
    have hdV : d < gfV := hdE.trans_le (gfT_le i.2)
    obtain ⟨s, hs⟩ := (gfB_codes S i.1 i.2).2 Z d hg (RS.gfCl_of_giK hd hdV) hdE
    refine ⟨s, fun y hy hy1 hZy => ⟨(hs y hy hy1 hZy).1, ?_⟩⟩
    have e2 := (hs y hy hy1 hZy).2
    rw [← RS.giTh_eq_gf hdV.le] at e2
    exact e2
  have h := giU_codes (K := RS.K) ghF0 (fun i => 1 + i.1) eW_lim RS.E_lt.le hK hKP (fun i => (gfT_lt i.2).le)
    fun b hb Z _ _ hgb => ⟨⟨b, hb⟩, by
      show gtc b < Z
      have hgb' : RS.K.gt b < Z := hgb
      rwa [RS.gt_lowE b hb] at hgb', le_add_self⟩
  exact ⟨fun y hy hy1 => h.1 y hy hy1 hy.1, h.2⟩

/-! ## The readings of all layers -/

/-- The reading statement at the code `c`. -/
def GiLC (c : Ordinal.{0}) (h : gfE ≤ c) (hc : c < RS.K.B) : Prop :=
  (∀ y, SC y → y < Om 1 → RS.K.gt c < y → (RS.giL c h hc).K.E y = gxTh y (RS.K.At y) (gcG c)) ∧
    GiPolyG RS.K (RS.giL c h hc).K.sys (gcG c)

theorem giL_atom {c Z : Ordinal.{0}} (hc : c < RS.K.B) (hg : RS.K.gt c < Z) : GxCl Z (RS.K.At Z) (gcG c) :=
  GxCl.atom (giG_atom (K := RS.K) hc hg)

/-- **THE UNIFORMITY THEOREM** for every code `c ∈ [ε_{Ω₁+1}, ε_{Ω₁+1}²)`: the top of `RS.giL c` reads `Γ_{Ω₁+1+c}` at
every strongly critical `y` above `RS.K.gt c`, and `RS.giL c` has terms for every code below it over every base above
`RS.K.gt c`. -/
theorem giL_codes (S : InaccSeq.{0}) : ∀ c (h : gfE ≤ c) (hc : c < RS.K.B), RS.GiLC c h hc := by
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH0 =>
  intro h hc
  rcases zero_or_succ_or_isSuccLimit c with rfl | ⟨b, hsb⟩ | hl
  · exact absurd h (not_le.2 eW_E.pos)
  · rw [succ_eq_add_one] at hsb
    subst hsb
    have hb : gfE ≤ b := by
      by_contra hb
      exact gi_not_E_le_succ h hb
    have hbB : b < RS.K.B := (lt_add_one b).trans hc
    obtain ⟨ihE, ihP⟩ := IH0 b (lt_add_one b) hb hbB
    have hg0 : (RS.giL b hb hbB).g = RS.K.gt b := RS.giL_g hb hbB
    have hcl : ∀ Z, SC Z → (RS.giL b hb hbB).g < Z → GxCl Z (RS.K.At Z) (gcG b) := fun Z _ hg => by
      rw [hg0] at hg; exact RS.giL_atom hbB hg
    have hcO : Om 1 ≤ gcG b := (gcG_Om1_lt _).le
    have hKE : ∀ y, SC y → y < Om 1 → (RS.giL b hb hbB).g < y →
        (RS.giL b hb hbB).K.E y = gxTh y (RS.K.At y) (gcG b) :=
      fun y hy hy1 hg => ihE y hy hy1 (hg0 ▸ hg)
    have hQ : cQs (gcG b) = gcG (b + 1) := gc_cQs b
    have H := RS.giH_succ (RS.giRec b hb hbB) hc
    have eL : RS.giL (b + 1) h hc = (geqLimB (RS.giL b hb hbB) (fun x => RS.R b x + 1) H).mono
        (RS.gi_g_succ (RS.giRec b hb hbB) hc) := by
      show (RS.giRec (b + 1) h hc).1 = _
      rw [RS.giRec_succ b hb h hc]; rfl
    rw [GiRS.GiLC, eL]
    refine ⟨fun y hy hy1 hby => ?_, fun Z d hg hd hdE => ?_⟩
    · show gq (RS.R b y + 1) y = _
      have hgy : (RS.giL b hb hbB).g < y := by rw [hg0]; exact (RS.gt_le_succ b).trans_lt hby
      rw [giLim_top (e := fun x => RS.R b x + 1) hcl hKE H hy hy1 hgy, hQ]
    · have hP := (giLim_poly hcl hcO hKE H ihP).mono (RS.gi_g_succ (RS.giRec b hb hbB) hc)
      rw [hQ] at hP
      exact hP Z d hg hd hdE
  · by_cases hE : c = gfE
    · subst hE
      have eL : RS.giL gfE h hc = ghEB := by
        show (RS.giRec gfE h hc).1 = _
        rw [RS.giRec_E h hc]; rfl
      rw [GiRS.GiLC, eL, RS.gt_E]
      obtain ⟨h1, h2⟩ := RS.giEB_codes S
      exact ⟨fun y hy hy1 _ => h1 y hy hy1, h2⟩
    have hEc : gfE < c := lt_of_le_of_ne h (Ne.symm hE)
    set F := RS.giFL c hl hEc hc (fun b hb1 hb2 => RS.giRec b hb1 (hb2.trans hc)) with hF
    have eL : RS.giL c h hc = ghLimB F := by
      show (RS.giRec c h hc).1 = _
      rw [RS.giRec_lim hl hEc h hc]; rfl
    have IH : ∀ i : F.I, RS.GiLC i.1 i.2.1 (i.2.2.trans hc) := fun i => IH0 i.1 i.2.2 i.2.1 (i.2.2.trans hc)
    have hK : ∀ (i : F.I) y, SC y → y < Om 1 → F.gi i < y →
        (F.K i).K.E y = gxTh y (RS.K.At y) (gcG i.1) := fun i y hy hy1 hi => (IH i).1 y hy hy1 hi
    have hKP : ∀ i : F.I, GiPolyG RS.K (F.K i).K.sys (gcG i.1) := fun i => (IH i).2
    have hcov : ∀ b, b < c → ∀ Z, SC Z → RS.K.gt c < Z → RS.K.gt b < Z → ∃ i : F.I, F.gi i < Z ∧ b ≤ i.1 := by
      intro b hb Z hZ _ hgb
      rcases lt_or_ge b gfE with hbE | hbE
      · exact ⟨⟨gfE, le_rfl, hEc⟩, by show RS.K.gt gfE < Z; rw [RS.gt_E]; exact hZ.1, hbE.le⟩
      · exact ⟨⟨b, hbE, hb⟩, hgb, le_rfl⟩
    have hres := giU_codes (K := RS.K) F (fun i => i.1) hl hc.le hK hKP (fun i => i.2.2.le) hcov
    rw [GiRS.GiLC, eL]
    exact hres

end GiRS

end Googology.Trans.PoR.InaccPsi.R2.Gi
