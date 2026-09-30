import Googology.Trans.BMS.PoR.PSS.TR.LCBase

/-!
# The X-form, and Lemma P-lo

* `lcx_of_lc` (`proof/TR-2.md` §4b.1): `LC_B(c)` gives its X-form, for `c` of
  level `k + 1` and `B` about levels `m ≤ k`.
* `p_lo` (**Lemma P-lo**, §4b.2): for `a = (k, cs ++ [c])` not epsilon, with the
  last child `c` replaced by `c⟨n⟩` of level `≤ k` and `𝒯(c⟨n⟩) < 𝒯(c)`,
  `LC_B(c)` gives `LC_B(a)`.  In values `𝒯(a) = ω^{W + 𝒯(c)}` and
  `𝒯(a⟨n⟩) = ω^{W + 𝒯(c⟨n⟩)}`; the summands of `W` absorbed by `𝒯(c)` are
  split off (`absorb_prefix`, `prefix_split`).
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-- **The X-form.** -/
theorem lcx_of_lc {k m : ℕ} {P : WP → Prop} (hmk : m ≤ k) {c : Tm} {cn : ℕ → Tm}
    (hc : c.y = k + 1) (hcn : ∀ n, (cn n).y = k + 1) (h : LC m P c cn) : LCX m P c cn := by
  intro ξ hξ hlt hB
  have hXge : ∀ n, Om (k + 1) ≤ WP.valS (logOmega (trTm (cn n))) := by
    intro n
    by_contra hc'
    have := opow_lt_Om_succ (not_le.mp hc')
    rw [val_log_trTm] at this
    have h2 := Om_le_val_trTm (cn n)
    rw [hcn n] at h2
    exact absurd h2 (not_le.mpr this)
  by_cases hs : WP.valS ξ < Om (k + 1)
  · exact ⟨0, fun n _ => lt_of_lt_of_le hs (hXge n)⟩
  have hXc := logOmega_spec (trTm_nfp c)
  have hXlt : WP.valS (logOmega (trTm c)) < Om (k + 2) :=
    valS_lt_Om hXc.1 (fun q hq => by have := hXc.2.2 q hq; rw [trTm_lvl, hc] at this; exact this)
  have hlev : ∀ q ∈ ξ, q.lvl ≤ k + 1 := by
    intro q hq
    by_contra hc'
    have := Om_le_valS_of_mem hξ hq (m := k + 2) (by omega)
    exact absurd (lt_trans hlt hXlt) (not_lt.mpr this)
  obtain ⟨he1, -, he3⟩ := omegaExp_spec hξ hlev (fun _ => not_lt.mp hs)
  have hγ : NFS [omegaExp ξ (k + 1)] := NFS.single he1
  have hγlt : WP.valS [omegaExp ξ (k + 1)] < (trTm c).val := by
    rw [valS_single, he3, ← val_log_trTm c]
    exact (opow_lt_opow_iff_right one_lt_omega0).mpr hlt
  obtain ⟨n0, hn0⟩ := h _ hγ hγlt (Bm.exp (by omega) hB)
  refine ⟨n0, fun n hn => ?_⟩
  have := hn0 n hn
  rw [valS_single, he3, ← val_log_trTm (cn n)] at this
  exact (opow_lt_opow_iff_right one_lt_omega0).mp this

/-! ## The non-epsilon case with a new last child -/

/-- `Z` without its last summand. -/
def zPre (k : ℕ) (cs : List Tm) : List WP :=
  addAll (headPart k cs ++ (cs.filter (fun c => decide (c.y ≤ k))).map (fun c => [trTm c]))

theorem zPre_nfs (k : ℕ) (cs : List Tm) : NFS (zPre k cs) := by
  refine (addAll_spec (fun x hx => ?_)).1
  rcases List.mem_append.mp hx with hx | hx
  · exact ((headPart_spec k cs).1 x hx).1
  · rw [List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact NFS.single (trTm_nfp c)

theorem zOf_append_lo {k : ℕ} {cs : List Tm} {x : Tm} (hx : x.y ≤ k) :
    zOf k (cs ++ [x]) = addS (zPre k cs) [trTm x] := by
  have hhp : headPart k (cs ++ [x]) = headPart k cs := by
    have : (cs ++ [x]).filter (fun c => decide (c.y = k + 1)) =
        cs.filter (fun c => decide (c.y = k + 1)) := by
      rw [List.filter_append]; simp; omega
    unfold headPart; rw [this]
  have hlo : (cs ++ [x]).filter (fun c => decide (c.y ≤ k)) =
      cs.filter (fun c => decide (c.y ≤ k)) ++ [x] := by
    rw [List.filter_append]; simp [hx]
  rw [zOf, hhp, hlo, List.map_append, List.map_singleton, ← List.append_assoc,
    addAll_append_single, zPre]

theorem val_trTm_append_lo {k : ℕ} {cs : List Tm} {x : Tm} (hx : x.y ≤ k) :
    (trTm (.node k (cs ++ [x]))).val = ω ^ (WP.valS (zPre k cs) + (trTm x).val) := by
  have hne : cs ++ [x] ≠ [] := by simp
  rw [val_trTm_noneps hne (by simp; omega), zOf_append_lo hx,
    (addS_spec (zPre_nfs k cs) (NFS.single (trTm_nfp x))).2, valS_single]

/-- **Lemma P-lo.** -/
theorem p_lo {k m : ℕ} {P : WP → Prop} (hP1 : P one) (hPo : P (om m)) {cs : List Tm} {c : Tm}
    {cn : ℕ → Tm} (hc : c.y ≤ k) (hcn : ∀ n, (cn n).y ≤ k)
    (hLC : LC m P c cn) :
    LC m P (.node k (cs ++ [c])) (fun n => .node k (cs ++ [cn n])) := by
  intro γ hγ hγlt hB
  set W := zPre k cs
  have hWn : NFS W := zPre_nfs k cs
  rw [val_trTm_append_lo hc] at hγlt
  cases γ with
  | nil => exact ⟨0, fun n _ => by simpa using val_pos (trTm_nfp _)⟩
  | cons g γ' =>
    have hg := hγ.head
    by_cases hgl : g.lvl < k
    · refine ⟨0, fun n _ => ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine lt_of_lt_of_le (valS_lt_Om hγ (hγ.lvl_le_of_head (m := k') (by omega))) ?_
      exact Om_le_val_trTm (.node (k' + 1) (cs ++ [cn n]))
    obtain ⟨hξn, hξv, -⟩ := logOmega_spec hg
    set ξ := logOmega g
    have hξlt : WP.valS ξ < WP.valS W + (trTm c).val := by
      refine (opow_lt_opow_iff_right one_lt_omega0).mp ?_
      rw [hξv]
      exact lt_of_le_of_lt le_valS_head hγlt
    have hBξ : Bm m P ξ := Bm.log hP1 hPo hg (hB.single_of_mem (by simp))
    suffices H : ∃ n0, ∀ n ≥ n0, WP.valS ξ + 1 ≤ WP.valS W + (trTm (cn n)).val by
      obtain ⟨n0, hn0⟩ := H
      refine ⟨n0, fun n hn => ?_⟩
      rw [val_trTm_append_lo (hcn n)]
      exact lt_of_lt_of_le (valS_lt_opow_succ hγ hξv.symm)
        ((opow_le_opow_iff_right one_lt_omega0).mpr (hn0 n hn))
    by_cases hξW : WP.valS ξ < WP.valS W
    · exact ⟨0, fun n _ => le_trans (Order.add_one_le_of_lt hξW) le_self_add⟩
    obtain ⟨K, hKW, hKn, hKv, hKeq⟩ := absorb_prefix hWn (trTm_nfp c)
    have h1 : WP.valS K ≤ WP.valS ξ := le_trans (valS_le_of_prefix hKW) (not_lt.mp hξW)
    have h2 : WP.valS ξ < WP.valS K + (trTm c).val := hKeq ▸ hξlt
    obtain ⟨ξ', hξe, hξ'n, hξ'v⟩ := prefix_split (trTm_nfp c) hKn hξn hKv h1 h2
    obtain ⟨n0, hn0⟩ := hLC ξ' hξ'n hξ'v (hBξ.sublist (by rw [hξe]; exact List.sublist_append_right _ _))
    refine ⟨n0, fun n hn => ?_⟩
    obtain ⟨R, hR⟩ := hKW
    rw [hξe, valS_append, add_assoc, ← hR, valS_append, add_assoc]
    refine (add_le_add_iff_left _).mpr (le_trans (Order.add_one_le_of_lt (hn0 n hn)) le_add_self)

end Googology.Trans.PSS.TR
