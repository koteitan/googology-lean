/-
Ported verbatim from koteitan/trio, `lean/Peel2.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Peel2.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
Peel2.lean: srow = 2 のガード付き剥離（the guarded peel）。

コアの自己言及的な hshift 上界を、ホスト橋（hshift_gseg）でホスト
N-係留のガード付き写像形（gmap）に変換し、カスケード前置のガード輸送
（Gtrans.gexp_guard_transport）で mapF_1 ∘ F_k = F_{k+1} と合成して、
ガード付きコピー塔（gtow）に展開する。塔は q = F_1(root) を消去すると
ちょうど M⟦m⟧ の尾部（gcopiesFrom）に一致する。
-/
import Googology.Trans.BMS.TrioCof.ArgDom
import Googology.Trans.BMS.TrioCof.Gtrans

namespace Googology.Trans.BMS.TrioCof

open Classical

/-- Position-anchored guarded map (an offset form of `gcopy`). -/
noncomputable def gmap (N : TrioSeq) (r d0 d1 j a l : ℕ) : TrioSeq :=
  (List.range' a l).map fun p =>
    (entry N 0 p + j * d0,
     entry N 1 p + (if le1 N r p then j * d1 else 0),
     entry N 2 p)

/-- The guarded tower over the shifted block `(r, r+Lb]`. -/
noncomputable def gtow (N : TrioSeq) (r d0 d1 Lb k m : ℕ) : TrioSeq :=
  (List.range' k m).flatMap fun j => gmap N r d0 d1 j (r + 1) Lb

@[simp] theorem gmap_length (N : TrioSeq) (r d0 d1 j a l : ℕ) :
    (gmap N r d0 d1 j a l).length = l := by
  unfold gmap
  simp

theorem gmap_getD {N : TrioSeq} {r d0 d1 j a l i : ℕ} (hi : i < l) :
    (gmap N r d0 d1 j a l).getD i (0, 0, 0)
      = (entry N 0 (a + i) + j * d0,
         entry N 1 (a + i) + (if le1 N r (a + i) then j * d1 else 0),
         entry N 2 (a + i)) := by
  unfold gmap
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hi)]
  rw [Nat.one_mul]
  rfl

theorem gmap_append (N : TrioSeq) (r d0 d1 j a l1 l2 : ℕ) :
    gmap N r d0 d1 j a (l1 + l2)
      = gmap N r d0 d1 j a l1 ++ gmap N r d0 d1 j (a + l1) l2 := by
  unfold gmap
  rw [← List.map_append, ← List.range'_append_1]

theorem seg_getD {N : TrioSeq} {a l i : ℕ} (hi : i < l) :
    (seg N a l).getD i (0, 0, 0)
      = (entry N 0 (a + i), entry N 1 (a + i), entry N 2 (a + i)) := by
  unfold seg
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range' (by simpa using hi)]
  rw [Nat.one_mul]
  rfl

theorem seg_append (N : TrioSeq) (a l1 l2 : ℕ) :
    seg N a (l1 + l2) = seg N a l1 ++ seg N (a + l1) l2 := by
  unfold seg
  rw [← List.map_append, ← List.range'_append_1]

theorem gtow_succ (N : TrioSeq) (r d0 d1 Lb k m : ℕ) :
    gtow N r d0 d1 Lb k (m + 1)
      = gmap N r d0 d1 k (r + 1) Lb ++ gtow N r d0 d1 Lb (k + 1) m := by
  unfold gtow
  rw [List.range'_succ, List.flatMap_cons]

@[simp] theorem gtow_zero (N : TrioSeq) (r d0 d1 Lb k : ℕ) :
    gtow N r d0 d1 Lb k 0 = [] := by
  unfold gtow
  rfl

theorem gmap_ne_nil (N : TrioSeq) (r d0 d1 j a : ℕ) {l : ℕ} (hl : 0 < l) :
    gmap N r d0 d1 j a l ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [gmap_length] at this
  simp at this
  omega

/-- Expansion prefixes are stable in the copy count. -/
theorem gexp_getD_mono {M : TrioSeq} {j0 Lb d0 d1 n p : ℕ}
    (hlen : j0 + Lb + 1 = M.length) (hLb : 0 < Lb)
    (hp : p < j0 + n * Lb) :
    (gexp M j0 Lb d0 d1 (n + 1)).getD p (0, 0, 0)
      = (gexp M j0 Lb d0 d1 n).getD p (0, 0, 0) := by
  rcases Nat.lt_or_ge p j0 with hlow | hhigh
  · rw [gexp_getD_low hlen hlow, gexp_getD_low hlen hlow]
  · obtain ⟨k, q, hk, hq, rfl⟩ := gexp_pos_decomp hLb hhigh hp
    rw [gexp_getD_mir hlen (by omega) hq, gexp_getD_mir hlen hk hq]

theorem getD_triple (N : TrioSeq) (p : ℕ) :
    N.getD p (0, 0, 0) = (entry N 0 p, entry N 1 p, entry N 2 p) := rfl

theorem entry_take {N : TrioSeq} {t y x : ℕ} (hx : x < t) :
    entry (N.take t) y x = entry N y x := by
  unfold entry
  rw [getD_take hx]

/-! ## カスケード上のガード合成 -/

/-- **Cascade guard composition**: on a cascade prefix (agreement with the
`take`-anchored expansion), the `le1` guard at a mirror position equals the
guard at the original block position. -/
theorem cascade_le1 {N : TrioSeq} {r Lb d0 d1 k' q' n' : ℕ}
    (hNlen : r + Lb + 1 ≤ N.length)
    (hup : ∀ l, r < l → l ≤ r + Lb → entry N 0 r < entry N 0 l)
    (hd0pos : 0 < d0) (hd0e : entry N 0 (r + Lb) = entry N 0 r + d0)
    (hd1pos : 0 < d1) (hle1q : le1 N r (r + Lb))
    (hk : k' < n') (hq : q' < Lb)
    (hposb : r + (k' * Lb + q') < N.length)
    (hcas : ∀ p, p ≤ r + (k' * Lb + q') → N.getD p (0, 0, 0)
      = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 n').getD p (0, 0, 0)) :
    (le1 N r (r + (k' * Lb + q')) ↔ le1 N r (r + q')) := by
  have hLb : 0 < Lb := by omega
  set Mv := N.take (r + Lb + 1) with hMv
  have hlenv : r + Lb + 1 = Mv.length := by
    rw [hMv, List.length_take]
    omega
  have hagv : ∀ x, x ≤ r + Lb → Mv.getD x (0, 0, 0) = N.getD x (0, 0, 0) := by
    intro x hx
    rw [hMv, getD_take (by omega)]
  have hupv' : ∀ l, r < l → l ≤ r + Lb → entry Mv 0 r < entry Mv 0 l := by
    intro l h1 h2
    rw [hMv, entry_take (by omega), entry_take (by omega)]
    exact hup l h1 h2
  have hd0ev : entry Mv 0 (r + Lb) = entry Mv 0 r + d0 := by
    rw [hMv, entry_take (by omega), entry_take (by omega)]
    exact hd0e
  have hle1v : le1 Mv r (r + Lb) := by
    refine le1_of_agree (X := Mv) (M := N) (by omega) (by omega) ?_ hle1q
    intro x hx
    exact hagv x hx
  have hbnd : k' * Lb + q' < n' * Lb := by
    have h1 : (k' + 1) * Lb ≤ n' * Lb := Nat.mul_le_mul_right _ (by omega)
    have h2 : (k' + 1) * Lb = k' * Lb + Lb := Nat.succ_mul k' Lb
    omega
  have hglen : (gexp Mv r Lb d0 d1 n').length = r + n' * Lb :=
    gexp_length hlenv
  have h1 : le1 N r (r + (k' * Lb + q'))
      ↔ le1 (gexp Mv r Lb d0 d1 n') r (r + (k' * Lb + q')) := by
    constructor
    · intro h
      refine le1_of_agree (X := gexp Mv r Lb d0 d1 n') (M := N)
        (by rw [hglen]; omega) (by omega) ?_ h
      intro x hx
      exact (hcas x hx).symm
    · intro h
      refine le1_of_agree (X := N) (M := gexp Mv r Lb d0 d1 n')
        (by omega) (by rw [hglen]; omega) ?_ h
      intro x hx
      exact hcas x hx
  have h2 := gexp_guard_transport (n := n') (k := k') (q := q') hlenv hk hq
    hupv' hd0pos hd0ev hd1pos hle1v
  have h3 : le1 Mv r (r + q') ↔ le1 N r (r + q') := by
    constructor
    · intro h
      refine le1_of_agree (X := N) (M := Mv) (by omega) (by omega) ?_ h
      intro x hx
      exact (hagv x (by omega)).symm
    · intro h
      refine le1_of_agree (X := Mv) (M := N) (by omega) (by omega) ?_ h
      intro x hx
      exact hagv x (by omega)
  rw [h1]
  constructor
  · intro h
    exact (h3.1 (h2.1 h))
  · intro h
    exact h2.2 (h3.2 h)

theorem list_ext_getD {A B : TrioSeq} (hlen : A.length = B.length)
    (h : ∀ i, i < A.length → A.getD i (0, 0, 0) = B.getD i (0, 0, 0)) :
    A = B := by
  refine List.ext_getElem hlen ?_
  intro i h1 h2
  have hh := h i h1
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at hh
  simpa using hh

@[simp] theorem seg_length (N : TrioSeq) (a l : ℕ) :
    (seg N a l).length = l := by
  unfold seg
  simp

/-! ## 剥離本体 -/

set_option maxHeartbeats 2000000 in
/-- **The guarded peel**: a self-referential guarded-map bound on a segment
unfolds into the guarded tower. -/
theorem peel2 {N : TrioSeq} {r Lb d0 d1 zl : ℕ}
    (hNlen : r + Lb + 1 ≤ N.length)
    (hLb : 0 < Lb) (hd0pos : 0 < d0) (hd1pos : 0 < d1)
    (hup : ∀ l, r < l → l ≤ r + Lb → entry N 0 r < entry N 0 l)
    (hd0e : entry N 0 (r + Lb) = entry N 0 r + d0)
    (hd1e : entry N 1 (r + Lb) = entry N 1 r + d1)
    (hz2 : entry N 2 (r + Lb) = entry N 2 r)
    (hle1q : le1 N r (r + Lb)) :
    ∀ (fuel k xa xl : ℕ), xl ≤ fuel → 1 ≤ k →
    xa = r + k * Lb + 1 →
    xa + xl ≤ N.length →
    (∀ p, p < xa → N.getD p (0, 0, 0)
      = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 (k + 1)).getD p (0, 0, 0)) →
    sle (seg N xa xl)
      (gmap N r d0 d1 k (r + 1) Lb
        ++ (gmap N r d0 d1 1 xa xl ++ gmap N r d0 d1 1 (xa + xl) zl)) →
    ∃ m, 1 ≤ m ∧ sle (seg N xa xl) (gtow N r d0 d1 Lb k m) := by
  have hlenv : r + Lb + 1 = (N.take (r + Lb + 1)).length := by
    rw [List.length_take]
    omega
  intro fuel
  induction fuel with
  | zero =>
    intro k xa xl hxl _ _ _ _ _
    have hxl0 : xl = 0 := by omega
    subst hxl0
    refine ⟨1, le_rfl, Or.inr ?_⟩
    show seqlex (seg N xa 0) (gtow N r d0 d1 Lb k 1)
    rw [show seg N xa 0 = [] from rfl, gtow_succ, gtow_zero, List.append_nil]
    exact gmap_ne_nil N r d0 d1 k (r + 1) hLb
  | succ fuel ih =>
    intro k xa xl hxl hk1 hxa hxrange hcas hinv
    by_cases hpre : ∃ X', seg N xa xl = gmap N r d0 d1 k (r + 1) Lb ++ X'
    case neg =>
      push Not at hpre
      refine ⟨1, le_rfl, Or.inr ?_⟩
      rw [gtow_succ, gtow_zero, List.append_nil]
      have h := seqlex_of_sle_not_prefix hinv hpre []
      rwa [List.append_nil] at h
    case pos =>
      obtain ⟨X', hX'⟩ := hpre
      have hlen1 : xl = Lb + X'.length := by
        have h := congrArg List.length hX'
        rw [seg_length, List.length_append, gmap_length] at h
        omega
      have hsplit : seg N xa xl = seg N xa Lb ++ seg N (xa + Lb) X'.length := by
        rw [show xl = Lb + X'.length from hlen1, seg_append]
      have hfirst : seg N xa Lb = gmap N r d0 d1 k (r + 1) Lb
          ∧ seg N (xa + Lb) X'.length = X' := by
        rw [hsplit] at hX'
        exact List.append_inj hX' (by rw [seg_length, gmap_length])
      -- the newly learned cascade values
      have hcasX : ∀ i, i < Lb → N.getD (xa + i) (0, 0, 0)
          = (entry N 0 (r + 1 + i) + k * d0,
             entry N 1 (r + 1 + i)
               + (if le1 N r (r + 1 + i) then k * d1 else 0),
             entry N 2 (r + 1 + i)) := by
        intro i hi
        have h := congrArg (fun l => l.getD i (0, 0, 0)) hfirst.1
        dsimp only at h
        rw [seg_getD hi, gmap_getD hi] at h
        rw [getD_triple]
        exact h
      -- take-agreement helpers
      have hMvag : ∀ x, x ≤ r + Lb →
          (N.take (r + Lb + 1)).getD x (0, 0, 0) = N.getD x (0, 0, 0) := by
        intro x hx
        exact getD_take (by omega)
      have hle1iff : ∀ x, x ≤ r + Lb →
          (le1 (N.take (r + Lb + 1)) r x ↔ le1 N r x) := by
        intro x hx
        constructor
        · intro h
          exact le1_of_agree (X := N) (M := N.take (r + Lb + 1)) (by omega)
            (by omega) (fun y hy => (hMvag y (by omega)).symm) h
        · intro h
          exact le1_of_agree (X := N.take (r + Lb + 1)) (M := N) (by omega)
            (by omega) (fun y hy => hMvag y (by omega)) h
      -- extend the cascade to the freshly matched copy
      have hcas' : ∀ p, p < xa + Lb → N.getD p (0, 0, 0)
          = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 (k + 2)).getD p (0, 0, 0) := by
        intro p hp
        rcases Nat.lt_or_ge p xa with hlow | hhigh
        · rw [hcas p hlow]
          have hmono := gexp_getD_mono (M := N.take (r + Lb + 1)) (j0 := r)
            (Lb := Lb) (d0 := d0) (d1 := d1) (n := k + 1) (p := p) hlenv hLb (by
            have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
            omega)
          exact hmono.symm
        · have hiLb : p - xa < Lb := by omega
          have hpe : p = xa + (p - xa) := by omega
          set i := p - xa with hidef
          rw [hpe, hcasX i hiLb]
          rcases Nat.lt_or_ge (1 + i) Lb with hcase | hcase
          · -- mirror (k, 1+i) of copy k
            rw [show xa + i = r + (k * Lb + (1 + i)) from by omega,
              gexp_getD_mir hlenv (show k < k + 2 from by omega) hcase,
              show r + (1 + i) = r + 1 + i from by omega]
            have e0 : entry (N.take (r + Lb + 1)) 0 (r + 1 + i)
                = entry N 0 (r + 1 + i) := entry_take (by omega)
            have e1 : entry (N.take (r + Lb + 1)) 1 (r + 1 + i)
                = entry N 1 (r + 1 + i) := entry_take (by omega)
            have e2 : entry (N.take (r + Lb + 1)) 2 (r + 1 + i)
                = entry N 2 (r + 1 + i) := entry_take (by omega)
            rw [e0, e1, e2]
            by_cases hg : le1 N r (r + 1 + i)
            · rw [if_pos hg, if_pos ((hle1iff (r + 1 + i) (by omega)).2 hg)]
            · rw [if_neg hg, if_neg (fun hc =>
                hg ((hle1iff (r + 1 + i) (by omega)).1 hc))]
          · -- the head of copy k+1
            have hie : 1 + i = Lb := by omega
            rw [show xa + i = r + ((k + 1) * Lb + 0) from by
                have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
                omega,
              gexp_getD_mir hlenv (show k + 1 < k + 2 from by omega) hLb]
            simp only [Nat.add_zero]
            have e0 : entry (N.take (r + Lb + 1)) 0 r = entry N 0 r :=
              entry_take (by omega)
            have e1 : entry (N.take (r + Lb + 1)) 1 r = entry N 1 r :=
              entry_take (by omega)
            have e2 : entry (N.take (r + Lb + 1)) 2 r = entry N 2 r :=
              entry_take (by omega)
            rw [e0, e1, e2, if_pos (le1_refl (by omega)),
              show r + 1 + i = r + Lb from by omega,
              if_pos hle1q]
            have hsd : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
            have hsd1 : (k + 1) * d1 = k * d1 + d1 := Nat.succ_mul k d1
            refine Prod.ext ?_ (Prod.ext ?_ ?_)
            · dsimp only
              omega
            · dsimp only
              omega
            · dsimp only
              omega
      -- the guard identity on the matched copy
      have hguard : ∀ i, i < Lb →
          (le1 N r (xa + i) ↔ le1 N r (r + 1 + i)) := by
        intro i hi
        rcases Nat.lt_or_ge (1 + i) Lb with hcase | hcase
        · have h := cascade_le1 (n' := k + 2) (k' := k) (q' := 1 + i)
            hNlen hup hd0pos hd0e hd1pos hle1q (by omega) hcase
            (by omega)
            (fun p hp => hcas' p (by omega))
          rw [show r + (k * Lb + (1 + i)) = xa + i from by omega,
            show r + (1 + i) = r + 1 + i from by omega] at h
          exact h
        · have hie : 1 + i = Lb := by omega
          have h := cascade_le1 (n' := k + 2) (k' := k + 1) (q' := 0)
            hNlen hup hd0pos hd0e hd1pos hle1q (by omega) hLb
            (by
              have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
              omega)
            (by
              intro p hp
              refine hcas' p ?_
              have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
              omega)
          rw [show r + ((k + 1) * Lb + 0) = xa + i from by
              have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
              omega,
            Nat.add_zero] at h
          constructor
          · intro _
            rw [show r + 1 + i = r + Lb from by omega]
            exact hle1q
          · intro _
            exact h.2 (le1_refl (by omega))
      -- THE COMPOSITION: shifting the matched copy once more
      have hcomp : gmap N r d0 d1 1 xa Lb
          = gmap N r d0 d1 (k + 1) (r + 1) Lb := by
        refine list_ext_getD (by rw [gmap_length, gmap_length]) ?_
        intro i h1
        rw [gmap_length] at h1
        rw [gmap_getD h1, gmap_getD h1]
        have h0 : entry N 0 (xa + i) = entry N 0 (r + 1 + i) + k * d0 := by
          show (N.getD (xa + i) (0, 0, 0)).1 = _
          rw [hcasX i h1]
        have h1' : entry N 1 (xa + i) = entry N 1 (r + 1 + i)
            + (if le1 N r (r + 1 + i) then k * d1 else 0) := by
          show (N.getD (xa + i) (0, 0, 0)).2.1 = _
          rw [hcasX i h1]
        have h2' : entry N 2 (xa + i) = entry N 2 (r + 1 + i) := by
          show (N.getD (xa + i) (0, 0, 0)).2.2 = _
          rw [hcasX i h1]
        have hsd : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
        have hsd1 : (k + 1) * d1 = k * d1 + d1 := Nat.succ_mul k d1
        by_cases hg : le1 N r (r + 1 + i)
        · rw [if_pos ((hguard i h1).2 hg), if_pos hg]
          rw [if_pos hg] at h1'
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · dsimp only
            omega
          · dsimp only
            omega
          · dsimp only
            omega
        · rw [if_neg (fun hc => hg ((hguard i h1).1 hc)), if_neg hg]
          rw [if_neg hg] at h1'
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · dsimp only
            omega
          · dsimp only
            omega
          · dsimp only
            omega
      -- strip and recurse
      have hinv' : sle X' (gmap N r d0 d1 1 xa xl
          ++ gmap N r d0 d1 1 (xa + xl) zl) := by
        rw [hX'] at hinv
        exact (sle_append_cancel _).1 hinv
      have hinv2 : sle (seg N (xa + Lb) X'.length)
          (gmap N r d0 d1 (k + 1) (r + 1) Lb
            ++ (gmap N r d0 d1 1 (xa + Lb) X'.length
              ++ gmap N r d0 d1 1 ((xa + Lb) + X'.length) zl)) := by
        rw [hfirst.2]
        rw [show xl = Lb + X'.length from hlen1, gmap_append, hcomp,
          List.append_assoc,
          show xa + (Lb + X'.length) = xa + Lb + X'.length from by omega]
          at hinv'
        exact hinv'
      obtain ⟨m, hm1, hm⟩ := ih (k + 1) (xa + Lb) X'.length
        (by omega) (by omega)
        (by
          have hsm : (k + 1) * Lb = k * Lb + Lb := Nat.succ_mul k Lb
          omega)
        (by omega)
        (by
          intro p hp
          exact hcas' p hp)
        hinv2
      refine ⟨m + 1, by omega, ?_⟩
      rw [gtow_succ, hX']
      refine (sle_append_cancel _).2 ?_
      rw [← hfirst.2]
      exact hm

/-! ## 橋と裏形（AscArgDom2 用の補助層） -/

theorem gmap_one_eq (N : TrioSeq) (r d0 d1 a l : ℕ) :
    gmap N r d0 d1 1 a l
      = (List.range' a l).map fun p =>
          (entry N 0 p + d0,
           entry N 1 p + (if le1 N r p then d1 else 0),
           entry N 2 p) := by
  unfold gmap
  refine List.map_congr_left ?_
  intro p _
  rw [Nat.one_mul, Nat.one_mul]

theorem seg_append_context (P T : TrioSeq) {l : ℕ} (hl : l ≤ T.length) :
    seg (P ++ T) P.length l = T.take l := by
  refine list_ext_getD ?_ ?_
  · rw [seg_length, List.length_take]
    omega
  · intro i hi
    rw [seg_length] at hi
    rw [seg_getD hi, getD_take hi, ← getD_triple,
      getD_app_right _ _ (by omega),
      show P.length + i - P.length = i from by omega]

theorem gtow_succ_back (N : TrioSeq) (r d0 d1 Lb k m : ℕ) :
    gtow N r d0 d1 Lb k (m + 1)
      = gtow N r d0 d1 Lb k m ++ gmap N r d0 d1 (k + m) (r + 1) Lb := by
  unfold gtow
  rw [List.range'_1_concat, List.flatMap_append]
  simp

theorem gcopiesFrom_succ_back (M : TrioSeq) (r L d0 d1 k m : ℕ) :
    gcopiesFrom M r L d0 d1 k (m + 1)
      = gcopiesFrom M r L d0 d1 k m ++ gcopy M r L d0 d1 (k + m) := by
  induction m generalizing k with
  | zero =>
    rw [gcopiesFrom_succ, gcopiesFrom_zero, gcopiesFrom_zero, Nat.add_zero]
    simp
  | succ m ih =>
    rw [gcopiesFrom_succ, ih (k + 1), gcopiesFrom_succ (M := M) (k0 := k),
      List.append_assoc]
    rw [show k + 1 + m = k + (m + 1) from by omega]

theorem gtow_mem {N : TrioSeq} {r d0 d1 Lb k m : ℕ} {x : ℕ × ℕ × ℕ}
    (hx : x ∈ gtow N r d0 d1 Lb k m) :
    ∃ j p, k ≤ j ∧ j < k + m ∧ r + 1 ≤ p ∧ p < r + 1 + Lb ∧
      x = (entry N 0 p + j * d0,
           entry N 1 p + (if le1 N r p then j * d1 else 0),
           entry N 2 p) := by
  unfold gtow at hx
  obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.1 hx
  obtain ⟨hj1, hj2⟩ := List.mem_range'_1.1 hj
  unfold gmap at hxj
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hxj
  obtain ⟨hp1, hp2⟩ := List.mem_range'_1.1 hp
  exact ⟨j, p, hj1, hj2, hp1, hp2, rfl⟩

/-- **The tower–copies bridge**: prepending the `k`-th root image turns the
guarded tower into the `M`-anchored guarded copies plus one trailing root. -/
theorem gtow_gcopiesFrom {N M : TrioSeq} {r Lb d0 d1 : ℕ}
    (hLb : 0 < Lb)
    (hagree : ∀ x, x < r + Lb → N.getD x (0, 0, 0) = M.getD x (0, 0, 0))
    (hbN : r + Lb < N.length) (hbM : r + Lb < M.length)
    (hle1qN : le1 N r (r + Lb))
    (hq0 : entry N 0 (r + Lb) = entry M 0 r + d0)
    (hq1 : entry N 1 (r + Lb) = entry M 1 r + d1)
    (hq2 : entry N 2 (r + Lb) = entry M 2 r) :
    ∀ m k, 1 ≤ k →
    (entry M 0 r + k * d0, entry M 1 r + k * d1, entry M 2 r)
        :: gtow N r d0 d1 Lb k m
      = gcopiesFrom M r Lb d0 d1 k m
          ++ [(entry M 0 r + (k + m) * d0,
               entry M 1 r + (k + m) * d1, entry M 2 r)] := by
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [gtow_zero, gcopiesFrom_zero, Nat.add_zero]
    rfl
  | succ m ih =>
    intro k hk
    rw [gtow_succ, gcopiesFrom_succ]
    have hLb' : Lb = (Lb - 1) + 1 := by omega
    have hone : gmap N r d0 d1 k (r + Lb) 1
        = [(entry N 0 (r + Lb) + k * d0,
            entry N 1 (r + Lb) + k * d1,
            entry N 2 (r + Lb))] := by
      unfold gmap
      rw [List.range'_one]
      simp only [List.map_cons, List.map_nil]
      rw [if_pos hle1qN]
    have hsplit : gmap N r d0 d1 k (r + 1) Lb
        = gmap N r d0 d1 k (r + 1) (Lb - 1)
          ++ [(entry N 0 (r + Lb) + k * d0,
               entry N 1 (r + Lb) + k * d1,
               entry N 2 (r + Lb))] := by
      have h := gmap_append N r d0 d1 k (r + 1) (Lb - 1) 1
      rw [show Lb - 1 + 1 = Lb from by omega,
        show r + 1 + (Lb - 1) = r + Lb from by omega, hone] at h
      exact h
    have hcsplit : gcopy M r Lb d0 d1 k
        = (entry M 0 r + k * d0, entry M 1 r + k * d1, entry M 2 r)
          :: gmap M r d0 d1 k (r + 1) (Lb - 1) := by
      unfold gcopy gmap
      rw [show Lb = (Lb - 1) + 1 from hLb', List.range'_succ, List.map_cons,
        if_pos (le1_refl (by omega))]
      simp only [Nat.add_sub_cancel]
    have hint : gmap N r d0 d1 k (r + 1) (Lb - 1)
        = gmap M r d0 d1 k (r + 1) (Lb - 1) := by
      refine list_ext_getD (by rw [gmap_length, gmap_length]) ?_
      intro i hi
      rw [gmap_length] at hi
      rw [gmap_getD hi, gmap_getD hi]
      have hpb : r + 1 + i < r + Lb := by omega
      have he : ∀ y, entry N y (r + 1 + i) = entry M y (r + 1 + i) := by
        intro y
        unfold entry
        rw [hagree _ hpb]
      have hg : le1 N r (r + 1 + i) ↔ le1 M r (r + 1 + i) := by
        constructor
        · intro h
          exact le1_of_agree (X := M) (M := N) (by omega) (by omega)
            (fun x hx => (hagree x (by omega)).symm) h
        · intro h
          exact le1_of_agree (X := N) (M := M) (by omega) (by omega)
            (fun x hx => hagree x (by omega)) h
      rw [he 0, he 1, he 2]
      by_cases hgN : le1 M r (r + 1 + i)
      · rw [if_pos (hg.2 hgN), if_pos hgN]
      · rw [if_neg (fun hc => hgN (hg.1 hc)), if_neg hgN]
    have hbnd : ((entry N 0 (r + Lb) + k * d0,
        entry N 1 (r + Lb) + k * d1, entry N 2 (r + Lb)) : ℕ × ℕ × ℕ)
        = ((entry M 0 r + (k + 1) * d0,
            entry M 1 r + (k + 1) * d1, entry M 2 r) : ℕ × ℕ × ℕ) := by
      have hs0 : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
      have hs1 : (k + 1) * d1 = k * d1 + d1 := Nat.succ_mul k d1
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · dsimp only
        omega
      · dsimp only
        omega
      · dsimp only
        omega
    rw [hsplit, hcsplit, hbnd]
    have hih := ih (k + 1) (by omega)
    rw [show k + 1 + m = k + (m + 1) from by omega] at hih
    rw [hint]
    rw [show ((entry M 0 r + k * d0, entry M 1 r + k * d1, entry M 2 r)
          :: (gmap M r d0 d1 k (r + 1) (Lb - 1)
            ++ [((entry M 0 r + (k + 1) * d0,
                 entry M 1 r + (k + 1) * d1, entry M 2 r) : ℕ × ℕ × ℕ)]
            ++ gtow N r d0 d1 Lb (k + 1) m))
        = ((entry M 0 r + k * d0, entry M 1 r + k * d1, entry M 2 r)
            :: gmap M r d0 d1 k (r + 1) (Lb - 1))
          ++ ((entry M 0 r + (k + 1) * d0,
               entry M 1 r + (k + 1) * d1, entry M 2 r)
            :: gtow N r d0 d1 Lb (k + 1) m) from by simp]
    rw [hih, ← List.append_assoc]

/-! ## 第二上昇枝（`srow = 2`, ガード付き） -/

/-- The second ascending branch: the deeper same-pair column's argument is
dominated by the guarded tower in the host. -/
def AscArgDom2 : Prop :=
  ∀ {G R S : TrioSeq} {v0 w1 d0 d1 : ℕ},
    ST_TS ((G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)]) →
    ST_TS ((G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S) →
    (∀ x ∈ R, v0 < x.1) → 0 < d0 → 0 < d1 →
    le1 ((G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)]) G.length
      (G ++ ((v0, w1, 0) :: R)).length →
    ∃ m, 1 ≤ m ∧ sle (S.takeWhile fun p => v0 + d0 < p.1)
      (gtow ((G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S)
        G.length d0 d1 (R.length + 1) 1 m)

set_option maxHeartbeats 2000000 in
theorem ascArgDom2_of_core (H : ArgDomCore) : AscArgDom2 := by
  intro G R S v0 w1 d0 d1 hM hN hRgt hd0 hd1 hle1
  set N := (G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S with hNdef
  set r := G.length with hrdef
  set Lb := R.length + 1 with hLbdef
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set D := S.dropWhile (fun p => v0 + d0 < p.1) with hDdef
  set A2 := D.takeWhile (fun p => v0 < p.1) with hA2def
  set Z := D.dropWhile (fun p => v0 < p.1) with hZdef
  have hSsplit : Shi ++ D = S := List.takeWhile_append_dropWhile
  have hDsplit : A2 ++ Z = D := List.takeWhile_append_dropWhile
  have hSlen : Shi.length + D.length = S.length := by
    have h := congrArg List.length hSsplit
    simpa using h
  have hDlen : A2.length + Z.length = D.length := by
    have h := congrArg List.length hDsplit
    simpa using h
  have hShigt : ∀ x ∈ Shi, v0 + d0 < x.1 := by
    intro x hx
    simpa using List.mem_takeWhile_imp hx
  have hA2gt : ∀ x ∈ A2, v0 < x.1 := by
    intro x hx
    simpa using List.mem_takeWhile_imp hx
  have hA2hd : A2 = [] ∨ (A2.headI).1 ≤ v0 + d0 := by
    rcases hdd : A2 with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have hDne : D ≠ [] := by
        intro he
        rw [hA2def, he] at hdd
        simp at hdd
      have hDhd : (D.headI).1 ≤ v0 + d0 := by
        rcases hd2 : D with _ | ⟨y, Y⟩
        · exact absurd hd2 hDne
        · have h := List.head?_dropWhile_not
            (fun p : ℕ × ℕ × ℕ => decide (v0 + d0 < p.1)) S
          rw [← hDdef, hd2] at h
          simp only [List.head?_cons] at h
          have : ¬ (v0 + d0 < y.1) := by simpa using h
          simp only [List.headI]
          omega
      have hhd : A2.headI = D.headI := by
        rcases hd2 : D with _ | ⟨y, Y⟩
        · exact absurd hd2 hDne
        · rw [hA2def, hd2]
          by_cases hy : v0 < y.1
          · rw [List.takeWhile_cons_of_pos (by simpa using hy)]
            rfl
          · rw [List.takeWhile_cons_of_neg (by simpa using hy)]
            rw [hA2def, hd2, List.takeWhile_cons_of_neg (by simpa using hy)]
              at hdd
            simp at hdd
      rw [← hdd, hhd]
      exact hDhd
  have hZhd : Z = [] ∨ (Z.headI).1 ≤ v0 := by
    rcases hdd : Z with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not
        (fun p : ℕ × ℕ × ℕ => decide (v0 < p.1)) D
      rw [← hZdef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 < z'.1) := by simpa using h
      simp only [List.headI]
      omega
  have hNeq : N = (G ++ (v0, w1, 0)
      :: (R ++ (v0 + d0, w1 + d1, 0) :: (Shi ++ A2))) ++ Z := by
    rw [hNdef, ← hSsplit, ← hDsplit]
    simp
  have hspine : SpineOK R (v0 + d0) (w1 + 1) := by
    have h := spineOK_strict_of_le1 hle1
    simpa using h
  have hcore := H (X := G) (A1 := R) (B := Shi) (A2 := A2) (Z := Z)
    (u := v0) (w1 := w1) (z := 0) (e := d0) (f := d1)
    (by rw [← hNeq]; exact hN)
    hd0 (Or.inr rfl) hRgt hShigt hA2gt hA2hd hZhd hspine
  -- ## the host bridge: hshift form → gmap form
  set l := R.length + 1 + (Shi.length + A2.length) with hldef
  set LIST := R ++ (v0 + d0, w1 + d1, 0) :: (Shi ++ A2) with hLISTdef
  have hLISTlen : LIST.length = l := by
    rw [hLISTdef, hldef]
    simp only [List.length_append, List.length_cons]
    omega
  have hNP : N = (G ++ [(v0, w1, 0)]) ++ (R ++ (v0 + d0, w1 + d1, 0) :: S) := by
    rw [hNdef]
    simp
  have hPlen : (G ++ [(v0, w1, 0)]).length = r + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hTfull : (R ++ (v0 + d0, w1 + d1, 0) :: S).take l = LIST := by
    rw [hLISTdef, ← hSsplit, ← hDsplit]
    have he : R ++ (v0 + d0, w1 + d1, 0) :: (Shi ++ (A2 ++ Z))
        = (R ++ (v0 + d0, w1 + d1, 0) :: (Shi ++ A2)) ++ Z := by
      simp
    rw [he]
    have hlen2 : (R ++ (v0 + d0, w1 + d1, 0) :: (Shi ++ A2)).length = l := by
      rw [hldef]
      simp only [List.length_append, List.length_cons]
      omega
    rw [← hlen2]
    exact List.take_left
  have hseg : seg N (r + 1) l = LIST := by
    have h := seg_append_context (G ++ [(v0, w1, 0)])
      (R ++ (v0 + d0, w1 + d1, 0) :: S)
      (l := l) (by
        rw [hldef]
        simp only [List.length_append, List.length_cons]
        omega)
    rw [hPlen] at h
    rw [hNP, h, hTfull]
  have hLISTgt : ∀ x ∈ LIST, v0 < x.1 := by
    intro x hx
    rw [hLISTdef] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hRgt x hx
    · rcases List.mem_cons.1 hx with rfl | hx
      · dsimp only
        omega
      · rcases List.mem_append.1 hx with hx | hx
        · have := hShigt x hx
          omega
        · exact hA2gt x hx
  have hdict : ∀ i, i < l → N.getD (r + 1 + i) (0, 0, 0) = LIST.getD i (0, 0, 0) := by
    intro i hi
    have h1 : (seg N (r + 1) l).getD i (0, 0, 0) = LIST.getD i (0, 0, 0) := by
      rw [hseg]
    rw [seg_getD hi, ← getD_triple] at h1
    exact h1
  have hgr : N.getD r (0, 0, 0) = (v0, w1, 0) := by
    rw [hNdef]
    rw [show (G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S
      = G ++ ((v0, w1, 0) :: (R ++ (v0 + d0, w1 + d1, 0) :: S)) from by simp]
    rw [getD_app_right _ _ (le_rfl), Nat.sub_self]
    rfl
  have hNlen2 : N.length = r + Lb + 1 + S.length := by
    rw [hNdef]
    simp only [List.length_append, List.length_cons]
    omega
  have hgq : N.getD (r + Lb) (0, 0, 0) = (v0 + d0, w1 + d1, 0) := by
    rw [hNdef]
    have hlen3 : (G ++ ((v0, w1, 0) :: R)).length = r + Lb := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [← hlen3, getD_app_right _ _ le_rfl, Nat.sub_self]
    rfl
  have hupN : ∀ j, r < j → j ≤ r + Lb → entry N 0 r < entry N 0 j := by
    intro j h1 h2
    have hjw : j = r + 1 + (j - r - 1) := by omega
    have hji : j - r - 1 < l := by
      rw [hldef, hLbdef] at *
      omega
    show (N.getD r (0, 0, 0)).1 < (N.getD j (0, 0, 0)).1
    rw [hgr, hjw, hdict _ hji]
    have hmem := getD_mem_of_lt (A := LIST) (j := j - r - 1)
      (by rw [hLISTlen]; exact hji)
    exact hLISTgt _ hmem
  -- window over the whole segment (for the host bridge)
  have hupSeg : ∀ j, r + 1 ≤ j → j < r + 1 + l → entry N 0 r < entry N 0 j := by
    intro j h1 h2
    have hjw : j = r + 1 + (j - r - 1) := by omega
    have hji : j - r - 1 < l := by omega
    show (N.getD r (0, 0, 0)).1 < (N.getD j (0, 0, 0)).1
    rw [hgr, hjw, hdict _ hji]
    have hmem := getD_mem_of_lt (A := LIST) (j := j - r - 1)
      (by rw [hLISTlen]; exact hji)
    exact hLISTgt _ hmem
  have hNlen : r + Lb + 1 ≤ N.length := by
    rw [hNlen2]
    omega
  have hrN : r < N.length := by omega
  have he1r : entry N 1 r = w1 := by
    show (N.getD r (0, 0, 0)).2.1 = w1
    rw [hgr]
  have hbridge : hshift w1 d0 d1 LIST = gmap N r d0 d1 1 (r + 1) l := by
    have h := hshift_gseg (M := N) (r := r) (e := d0) (f := d1) l
      (a := r + 1) (pa := r) (le1_refl hrN) (by omega)
      (by
        rw [hNlen2, hldef, hLbdef]
        omega)
      (fun j hj1 hj2 => hupSeg j hj1 hj2)
      (fun j hj1 hj2 => absurd hj1 (by omega))
    rw [he1r] at h
    have hsegd : ((List.range' (r + 1) l).map fun j =>
        ((entry N 0 j, entry N 1 j, entry N 2 j) : ℕ × ℕ × ℕ)) = LIST := hseg
    rw [hsegd] at h
    rw [gmap_one_eq]
    exact h.symm
  rw [hbridge] at hcore
  -- ## feed the peel
  set xa := r + Lb + 1 with hxadef
  have hlsplit : gmap N r d0 d1 1 (r + 1) l
      = gmap N r d0 d1 1 (r + 1) Lb
        ++ (gmap N r d0 d1 1 xa Shi.length
          ++ gmap N r d0 d1 1 (xa + Shi.length) A2.length) := by
    have h1 : l = Lb + (Shi.length + A2.length) := by
      omega
    rw [h1, gmap_append N r d0 d1 1 (r + 1) Lb (Shi.length + A2.length),
      gmap_append N r d0 d1 1 (r + 1 + Lb) Shi.length A2.length]
    rw [show r + 1 + Lb = xa from by omega]
  rw [hlsplit] at hcore
  -- the subject is a segment
  have hsubj : seg N xa Shi.length = Shi := by
    have h := seg_append_context ((G ++ ((v0, w1, 0) :: R))
        ++ [(v0 + d0, w1 + d1, 0)]) S
      (l := Shi.length) (by omega)
    have hplen2 : ((G ++ ((v0, w1, 0) :: R))
        ++ [(v0 + d0, w1 + d1, 0)]).length = xa := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [hplen2] at h
    have hNP2 : N = ((G ++ ((v0, w1, 0) :: R))
        ++ [(v0 + d0, w1 + d1, 0)]) ++ S := by
      rw [hNdef]
      simp
    rw [hNP2, h]
    conv_lhs => rw [← hSsplit]
    exact List.take_left
  -- entry dictionaries at the two anchors
  have he0r : entry N 0 r = v0 := by
    show (N.getD r (0, 0, 0)).1 = v0
    rw [hgr]
  have he2r : entry N 2 r = 0 := by
    show (N.getD r (0, 0, 0)).2.2 = 0
    rw [hgr]
  have he0q : entry N 0 (r + Lb) = v0 + d0 := by
    show (N.getD (r + Lb) (0, 0, 0)).1 = v0 + d0
    rw [hgq]
  have he1q : entry N 1 (r + Lb) = w1 + d1 := by
    show (N.getD (r + Lb) (0, 0, 0)).2.1 = w1 + d1
    rw [hgq]
  have he2q : entry N 2 (r + Lb) = 0 := by
    show (N.getD (r + Lb) (0, 0, 0)).2.2 = 0
    rw [hgq]
  -- the boundary guard from the host ancestry
  have hle1q : le1 N r (r + Lb) := by
    have hqpos : (G ++ ((v0, w1, 0) :: R)).length = r + Lb := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [hqpos] at hle1
    have hlp : ((G ++ ((v0, w1, 0) :: R))
        ++ [(v0 + d0, w1 + d1, 1)]).getD (r + Lb) (0, 0, 0)
        = (v0 + d0, w1 + d1, 1) := by
      rw [← hqpos, getD_app_right (G ++ ((v0, w1, 0) :: R))
        [(v0 + d0, w1 + d1, 1)] le_rfl, Nat.sub_self]
      rfl
    refine le1_of_agree_last (X := N)
      (M := (G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)])
      (by omega) (by rw [List.length_append, hqpos]; simp) ?_ ?_ ?_ hle1
    · intro x hx
      rw [hNdef]
      rw [getD_append_left (G := G ++ ((v0, w1, 0) :: R))
          (by rw [hqpos]; omega),
        getD_append_left (G := G ++ ((v0, w1, 0) :: R))
          (by rw [hqpos]; omega)]
    · rw [hgq, hlp]
    · rw [hgq, hlp]
  -- the base cascade (k = 1)
  have hcas1 : ∀ p, p < xa → N.getD p (0, 0, 0)
      = (gexp (N.take (r + Lb + 1)) r Lb d0 d1 2).getD p (0, 0, 0) := by
    intro p hp
    have hlenv : r + Lb + 1 = (N.take (r + Lb + 1)).length := by
      rw [List.length_take]
      omega
    rcases Nat.lt_or_ge p r with hlow | hhigh
    · rw [gexp_getD_low hlenv hlow, getD_take (by omega)]
    · rcases Nat.lt_or_ge p (r + Lb) with hmid | hqp
      · -- copy 0: the original block
        have hmir := gexp_getD_mir (M := N.take (r + Lb + 1)) (j0 := r)
          (Lb := Lb) (d0 := d0) (d1 := d1) (n := 2) (k := 0) (q := p - r)
          hlenv (by omega) (by omega)
        simp only [Nat.zero_mul, Nat.zero_add, ite_self, Nat.add_zero] at hmir
        rw [show r + (p - r) = p from by omega] at hmir
        rw [hmir]
        have e0 : entry (N.take (r + Lb + 1)) 0 p = entry N 0 p :=
          entry_take (by omega)
        have e1 : entry (N.take (r + Lb + 1)) 1 p = entry N 1 p :=
          entry_take (by omega)
        have e2 : entry (N.take (r + Lb + 1)) 2 p = entry N 2 p :=
          entry_take (by omega)
        rw [e0, e1, e2, ← getD_triple]
      · -- the copy-1 root = the q column
        have hpe : p = r + Lb := by omega
        have hmir := gexp_getD_mir (M := N.take (r + Lb + 1)) (j0 := r)
          (Lb := Lb) (d0 := d0) (d1 := d1) (n := 2) (k := 1) (q := 0)
          hlenv (by omega) (by omega)
        rw [show r + (1 * Lb + 0) = r + Lb from by omega] at hmir
        simp only [Nat.add_zero, Nat.one_mul] at hmir
        rw [if_pos (le1_refl (show r < (N.take (r + Lb + 1)).length from
          by rw [← hlenv]; omega))] at hmir
        rw [hpe, hgq, hmir]
        have e0 : entry (N.take (r + Lb + 1)) 0 r = entry N 0 r :=
          entry_take (by omega)
        have e1 : entry (N.take (r + Lb + 1)) 1 r = entry N 1 r :=
          entry_take (by omega)
        have e2 : entry (N.take (r + Lb + 1)) 2 r = entry N 2 r :=
          entry_take (by omega)
        rw [e0, e1, e2, he0r, he1r, he2r]
  -- apply the peel
  have hd0e : entry N 0 (r + Lb) = entry N 0 r + d0 := by
    rw [he0q, he0r]
  have hd1e : entry N 1 (r + Lb) = entry N 1 r + d1 := by
    rw [he1q, he1r]
  have hz2e : entry N 2 (r + Lb) = entry N 2 r := by
    rw [he2q, he2r]
  have hinv : sle (seg N xa Shi.length)
      (gmap N r d0 d1 1 (r + 1) Lb
        ++ (gmap N r d0 d1 1 xa Shi.length
          ++ gmap N r d0 d1 1 (xa + Shi.length) A2.length)) := by
    rw [hsubj]
    exact hcore
  have hxrange : xa + Shi.length ≤ N.length := by
    rw [hNlen2, hxadef]
    have : Shi.length ≤ S.length := by
      conv_rhs => rw [← hSsplit]
      simp
    omega
  obtain ⟨m, hm1, hm⟩ := peel2 (N := N) (r := r) (Lb := Lb) (d0 := d0)
    (d1 := d1) (zl := A2.length) hNlen (by omega) hd0 hd1 hupN hd0e hd1e
    hz2e hle1q Shi.length 1 xa Shi.length le_rfl le_rfl (by omega)
    hxrange hcas1 hinv
  refine ⟨m, hm1, ?_⟩
  rw [← hsubj]
  exact hm

/-! ## 第二上昇枝の完結（one extra copy） -/

theorem gmap_cons (N : TrioSeq) (r d0 d1 j a : ℕ) {l : ℕ} (hl : 0 < l) :
    gmap N r d0 d1 j a l
      = (entry N 0 a + j * d0,
         entry N 1 a + (if le1 N r a then j * d1 else 0),
         entry N 2 a) :: gmap N r d0 d1 j (a + 1) (l - 1) := by
  unfold gmap
  rw [show l = (l - 1) + 1 from by omega, List.range'_succ, List.map_cons]
  simp only [Nat.add_sub_cancel]

theorem gcopy_root_cons (M : TrioSeq) (r Lb d0 d1 k : ℕ) (hLb : 0 < Lb)
    (hr : r < M.length) :
    gcopy M r Lb d0 d1 k
      = (entry M 0 r + k * d0, entry M 1 r + k * d1, entry M 2 r)
        :: gmap M r d0 d1 k (r + 1) (Lb - 1) := by
  unfold gcopy gmap
  rw [show Lb = (Lb - 1) + 1 from by omega, List.range'_succ, List.map_cons,
    if_pos (le1_refl hr)]
  simp only [Nat.add_sub_cancel]

set_option maxHeartbeats 2000000 in
/-- **The second ascending branch closes with one extra copy.** -/
theorem asc_crux2 (H : AscArgDom2) {G R S : TrioSeq} {v0 w1 d0 d1 : ℕ}
    (hM : ST_TS ((G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)]))
    (hN : ST_TS ((G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S))
    (hRgt : ∀ x ∈ R, v0 < x.1) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (hle1 : le1 ((G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)])
      G.length (G ++ ((v0, w1, 0) :: R)).length) :
    ∃ n, 1 ≤ n ∧ sle ((v0 + d0, w1 + d1, 0) :: S)
      (gcopiesFrom ((G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)])
        G.length (R.length + 1) d0 d1 1 n) := by
  obtain ⟨m, hm1, hdom⟩ := H hM hN hRgt hd0 hd1 hle1
  set N := (G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S with hNdef
  set Mf := (G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)] with hMfdef
  set r := G.length with hrdef
  set Lb := R.length + 1 with hLbdef
  set Shi := S.takeWhile (fun p => v0 + d0 < p.1) with hShidef
  set Slo := S.dropWhile (fun p => v0 + d0 < p.1) with hSlodef
  have hSsplit : Shi ++ Slo = S := List.takeWhile_append_dropWhile
  have hqpos : (G ++ ((v0, w1, 0) :: R)).length = r + Lb := by
    simp only [List.length_append, List.length_cons]
    omega
  have hNlen2 : N.length = r + Lb + 1 + S.length := by
    rw [hNdef]
    simp only [List.length_append, List.length_cons]
    omega
  have hMflen : Mf.length = r + Lb + 1 := by
    rw [hMfdef]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hgrN : N.getD r (0, 0, 0) = (v0, w1, 0) := by
    rw [hNdef]
    rw [show (G ++ ((v0, w1, 0) :: R)) ++ (v0 + d0, w1 + d1, 0) :: S
      = G ++ ((v0, w1, 0) :: (R ++ (v0 + d0, w1 + d1, 0) :: S)) from by simp]
    rw [getD_app_right _ _ le_rfl, Nat.sub_self]
    rfl
  have hgrM : Mf.getD r (0, 0, 0) = (v0, w1, 0) := by
    rw [hMfdef]
    rw [show (G ++ ((v0, w1, 0) :: R)) ++ [(v0 + d0, w1 + d1, 1)]
      = G ++ ((v0, w1, 0) :: (R ++ [(v0 + d0, w1 + d1, 1)])) from by simp]
    rw [getD_app_right _ _ le_rfl, Nat.sub_self]
    rfl
  have hgqN : N.getD (r + Lb) (0, 0, 0) = (v0 + d0, w1 + d1, 0) := by
    rw [hNdef, ← hqpos, getD_app_right _ _ le_rfl, Nat.sub_self]
    rfl
  have hagree : ∀ x, x < r + Lb → N.getD x (0, 0, 0) = Mf.getD x (0, 0, 0) := by
    intro x hx
    rw [hNdef, hMfdef,
      getD_append_left (G := G ++ ((v0, w1, 0) :: R)) (by rw [hqpos]; omega),
      getD_append_left (G := G ++ ((v0, w1, 0) :: R)) (by rw [hqpos]; omega)]
  have hSloHd : Slo = [] ∨ (Slo.headI).1 ≤ v0 + d0 := by
    rcases hdd : Slo with _ | ⟨z', Z'⟩
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h := List.head?_dropWhile_not
        (fun p : ℕ × ℕ × ℕ => decide (v0 + d0 < p.1)) S
      rw [← hSlodef, hdd] at h
      simp only [List.head?_cons] at h
      have : ¬ (v0 + d0 < z'.1) := by simpa using h
      simp only [List.headI]
      omega
  -- the boundary guard in the crux host
  have hle1qN : le1 N r (r + Lb) := by
    rw [hqpos] at hle1
    have hlp : Mf.getD (r + Lb) (0, 0, 0) = (v0 + d0, w1 + d1, 1) := by
      rw [hMfdef, ← hqpos, getD_app_right _ _ le_rfl, Nat.sub_self]
      rfl
    refine le1_of_agree_last (X := N) (M := Mf)
      (by omega) (by omega) hagree ?_ ?_ hle1
    · rw [hgqN, hlp]
    · rw [hgqN, hlp]
  -- window facts
  have hdictR : ∀ i, i < R.length →
      N.getD (r + 1 + i) (0, 0, 0) = R.getD i (0, 0, 0) := by
    intro i hi
    rw [hNdef,
      getD_append_left (G := G ++ ((v0, w1, 0) :: R)) (by rw [hqpos]; omega)]
    rw [show G ++ ((v0, w1, 0) :: R) = (G ++ [(v0, w1, 0)]) ++ R from by simp]
    rw [getD_app_right (G ++ [(v0, w1, 0)]) R (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)]
    congr 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hupN : ∀ p, r < p → p ≤ r + Lb → v0 < entry N 0 p := by
    intro p h1 h2
    rcases Nat.eq_or_lt_of_le h2 with heq | h2'
    · show (N.getD p (0, 0, 0)).1 > v0
      rw [heq, hgqN]
      dsimp only
      omega
    · have hi : p - r - 1 < R.length := by omega
      show (N.getD p (0, 0, 0)).1 > v0
      rw [show p = r + 1 + (p - r - 1) from by omega, hdictR _ hi]
      exact hRgt _ (getD_mem_of_lt (by omega))
  -- entry dictionaries
  have he0rM : entry Mf 0 r = v0 := by
    show (Mf.getD r (0, 0, 0)).1 = v0
    rw [hgrM]
  have he1rM : entry Mf 1 r = w1 := by
    show (Mf.getD r (0, 0, 0)).2.1 = w1
    rw [hgrM]
  have he2rM : entry Mf 2 r = 0 := by
    show (Mf.getD r (0, 0, 0)).2.2 = 0
    rw [hgrM]
  have hq0 : entry N 0 (r + Lb) = entry Mf 0 r + d0 := by
    show (N.getD (r + Lb) (0, 0, 0)).1 = _
    rw [hgqN, he0rM]
  have hq1 : entry N 1 (r + Lb) = entry Mf 1 r + d1 := by
    show (N.getD (r + Lb) (0, 0, 0)).2.1 = _
    rw [hgqN, he1rM]
  have hq2 : entry N 2 (r + Lb) = entry Mf 2 r := by
    show (N.getD (r + Lb) (0, 0, 0)).2.2 = _
    rw [hgqN, he2rM]
  have hLb0 : 0 < Lb := by omega
  have hbN : r + Lb < N.length := by omega
  have hbM : r + Lb < Mf.length := by omega
  -- the bridge at m + 1
  have hbr := gtow_gcopiesFrom (N := N) (M := Mf) hLb0 hagree hbN hbM
    hle1qN hq0 hq1 hq2 (m + 1) 1 le_rfl
  rw [he0rM, he1rM, he2rM, Nat.one_mul, Nat.one_mul] at hbr
  -- decompose the target copies
  have htgt : gcopiesFrom Mf r Lb d0 d1 1 (m + 2)
      = ((v0 + d0, w1 + d1, 0) :: gtow N r d0 d1 Lb 1 (m + 1))
        ++ gmap Mf r d0 d1 (1 + (m + 1)) (r + 1) (Lb - 1) := by
    rw [gcopiesFrom_succ_back, gcopy_root_cons Mf r Lb d0 d1 _ hLb0 (by omega),
      he0rM, he1rM, he2rM,
      show gcopiesFrom Mf r Lb d0 d1 1 (m + 1)
          ++ ((v0 + (1 + (m + 1)) * d0, w1 + (1 + (m + 1)) * d1, 0)
            :: gmap Mf r d0 d1 (1 + (m + 1)) (r + 1) (Lb - 1))
        = (gcopiesFrom Mf r Lb d0 d1 1 (m + 1)
            ++ [((v0 + (1 + (m + 1)) * d0,
                 w1 + (1 + (m + 1)) * d1, 0) : ℕ × ℕ × ℕ)])
          ++ gmap Mf r d0 d1 (1 + (m + 1)) (r + 1) (Lb - 1) from by simp,
      ← hbr]
  refine ⟨m + 2, by omega, ?_⟩
  rw [htgt]
  show sle ([((v0 + d0 : ℕ), (w1 + d1 : ℕ), (0 : ℕ))] ++ S)
    (([((v0 + d0 : ℕ), (w1 + d1 : ℕ), (0 : ℕ))]
      ++ gtow N r d0 d1 Lb 1 (m + 1))
      ++ gmap Mf r d0 d1 (1 + (m + 1)) (r + 1) (Lb - 1))
  rw [List.append_assoc]
  rw [sle_append_cancel]
  -- S against the extended tower
  rw [gtow_succ_back, List.append_assoc]
  conv_lhs => rw [← hSsplit]
  have hgmapN_gt : ∀ x ∈ gmap N r d0 d1 (1 + m) (r + 1) Lb, v0 + d0 < x.1 := by
    intro x hx
    unfold gmap at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hp1, hp2⟩ := List.mem_range'_1.1 hp
    have := hupN p (by omega) (by omega)
    have hmd : d0 ≤ (1 + m) * d0 := by
      have : 1 * d0 ≤ (1 + m) * d0 := Nat.mul_le_mul_right _ (by omega)
      omega
    dsimp only
    omega
  rcases hdom with heq | hlt
  · -- the tower is exhausted exactly: the next level decides
    rw [heq]
    rw [sle_append_cancel]
    rcases hSloHd with hslo | hslo
    · rw [hslo]
      refine Or.inr ?_
      show (gmap N r d0 d1 (1 + m) (r + 1) Lb
        ++ gmap Mf r d0 d1 (1 + (m + 1)) (r + 1) (Lb - 1)) ≠ []
      intro hc
      have := congrArg List.length hc
      simp only [List.length_append, gmap_length, List.length_nil] at this
      omega
    · rcases hdd : Slo with _ | ⟨s0, Slo'⟩
      · refine Or.inr ?_
        show (gmap N r d0 d1 (1 + m) (r + 1) Lb
          ++ gmap Mf r d0 d1 (1 + (m + 1)) (r + 1) (Lb - 1)) ≠ []
        intro hc
        have := congrArg List.length hc
        simp only [List.length_append, gmap_length, List.length_nil] at this
        omega
      · refine Or.inr ?_
        rw [gmap_cons N r d0 d1 (1 + m) (r + 1) hLb0, List.cons_append]
        refine Or.inl (Or.inl ?_)
        have hhead := hupN (r + 1) (by omega) (by omega)
        have hmd : d0 ≤ (1 + m) * d0 := by
          have : 1 * d0 ≤ (1 + m) * d0 := Nat.mul_le_mul_right _ (by omega)
          omega
        rw [hdd] at hslo
        simp only [List.headI] at hslo
        dsimp only
        omega
  · -- strict divergence inside the tower: splice
    refine Or.inr ?_
    refine seqlex_splice hlt ?_ _
    rcases hSloHd with hslo | hslo
    · exact Or.inl hslo
    · refine Or.inr (fun x hx => ?_)
      obtain ⟨j, p, hj1, hj2, hp1, hp2, rfl⟩ := gtow_mem hx
      have := hupN p (by omega) (by omega)
      have hmd : d0 ≤ j * d0 := by
        have : 1 * d0 ≤ j * d0 := Nat.mul_le_mul_right _ (by omega)
        omega
      refine Or.inl ?_
      dsimp only
      omega

/-! ## `srow = 2` の派遣 -/

set_option maxHeartbeats 2000000 in
/-- The `srow = 2` half of the ascending crux, from the core. -/
theorem trioAsc_srow2 (Hc : ArgDomCore) {M N : TrioSeq} {q : ℕ × ℕ × ℕ}
    {S : TrioSeq} (hM : ST_TS M) (hN : ST_TS N) (L1 : 1 < M.length)
    (hz : ¬ (entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
      entry M 2 (M.length - 1) = 0))
    (hsr2 : srow M (M.length - 1) = 2)
    (hNeq : N = M.dropLast ++ q :: S)
    (hq : collt q (M.getD (M.length - 1) (0, 0, 0))) :
    ∃ n, 1 ≤ n ∧ sle N (M⟦n⟧) := by
  have hp := hasParent_last_ST_TS hM (by omega) hz
  have np := parent_nextR hp
  have j0lt : parent M (srow M (M.length - 1)) (M.length - 1)
      < M.length - 1 := nextR_index_lt np
  have chain := nextR_chain0 np
  have iv : ∀ k, parent M (srow M (M.length - 1)) (M.length - 1) < k →
      k ≤ M.length - 1 →
      entry M 0 (parent M (srow M (M.length - 1)) (M.length - 1))
        < entry M 0 k :=
    fun k h1 h2 => le0_interval_gt chain k ⟨h1, h2⟩
  have np2 : nextrel2 M (parent M (srow M (M.length - 1)) (M.length - 1))
      (M.length - 1) := by
    have np' := np
    unfold nextR at np'
    rw [if_neg (by omega : ¬ srow M (M.length - 1) = 0),
      if_neg (by omega : ¬ srow M (M.length - 1) = 1)] at np'
    exact np'
  set j0 := parent M (srow M (M.length - 1)) (M.length - 1) with hj0
  set L := M.length - 1 - j0 with hLdef
  have hLpos : 0 < L := by omega
  have hj0b : j0 < M.length := by omega
  -- pin the dropped column
  have hlp2 : entry M 2 (M.length - 1) = 1 := by
    have h1 := np2.2.2.2.1
    have h2 := z2ok_ST_TS hM (M.length - 1) (by omega)
    have e2 : entry M 2 (M.length - 1)
        = (M.getD (M.length - 1) (0, 0, 0)).2.2 := rfl
    have e2' : entry M 2 j0 = (M.getD j0 (0, 0, 0)).2.2 := rfl
    omega
  have hj02 : entry M 2 j0 = 0 := by
    have h1 := np2.2.2.2.1
    omega
  have hle1c : le1 M j0 (M.length - 1) := np2.2.2.2.2.1
  set d0i := entry M 0 (M.length - 1) - entry M 0 j0 with hd0i
  set d1i := entry M 1 (M.length - 1) - entry M 1 j0 with hd1i
  have hd0pos : 0 < d0i := by
    have := iv (M.length - 1) j0lt le_rfl
    omega
  have hd1pos : 0 < d1i := by
    have := rtg1_entry1_lt hle1c.2.2 (by omega)
    omega
  have hlp0 : entry M 0 (M.length - 1) = entry M 0 j0 + d0i := by
    have := iv (M.length - 1) j0lt le_rfl
    omega
  have hlp1 : entry M 1 (M.length - 1) = entry M 1 j0 + d1i := by
    have := rtg1_entry1_lt hle1c.2.2 (by omega)
    omega
  have hlpe : M.getD (M.length - 1) (0, 0, 0)
      = (entry M 0 j0 + d0i, entry M 1 j0 + d1i, 1) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show (M.getD (M.length - 1) (0, 0, 0)).1 = entry M 0 j0 + d0i
      exact hlp0
    · exact hlp1
    · exact hlp2
  rw [hlpe] at hq
  unfold collt at hq
  dsimp only at hq
  -- the oper form
  have hd0e : (if 0 < srow M (M.length - 1)
      then entry M 0 (M.length - 1) - entry M 0 j0 else 0) = d0i := by
    rw [if_pos (by omega)]
  have hd1e : (if 1 < srow M (M.length - 1)
      then entry M 1 (M.length - 1) - entry M 1 j0 else 0) = d1i := by
    rw [if_pos (by omega)]
  have hMn2 : ∀ m, M⟦m + 1⟧ = M.dropLast
      ++ gcopiesFrom M j0 L d0i d1i 1 m := by
    intro m
    rw [oper_gcopies (m + 1) (by omega) hz hp, ← hj0, ← hLdef, hd0e, hd1e,
      gcopies_eq_from, gcopiesFrom_succ, gcopy_zero, ← List.append_assoc,
      take_gcopy_zero L1 hz hp]
  have hsegL : seg M j0 L
      = (entry M 0 j0, entry M 1 j0, entry M 2 j0)
        :: seg M (j0 + 1) (L - 1) := by
    obtain ⟨l', hle⟩ : ∃ l', L = l' + 1 := ⟨L - 1, by omega⟩
    rw [hle, seg_cons, Nat.add_sub_cancel]
  rw [hj02] at hsegL
  have hRgt : ∀ x ∈ seg M (j0 + 1) (L - 1), entry M 0 j0 < x.1 := by
    intro x hx
    unfold seg at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hjb := List.mem_range'_1.1 hj
    exact iv j (by omega) (by omega)
  -- the head of the first guarded copy
  have hhead : gcopiesFrom M j0 L d0i d1i 1 1
      = (entry M 0 j0 + d0i, entry M 1 j0 + d1i, 0)
        :: gmap M j0 d0i d1i 1 (j0 + 1) (L - 1) := by
    rw [gcopiesFrom_succ, gcopiesFrom_zero, List.append_nil,
      gcopy_root_cons M j0 L d0i d1i 1 (by omega) (by omega),
      Nat.one_mul, Nat.one_mul, hj02]
  rcases hq with hq1 | ⟨hqe1, hq2⟩
  · -- below the copy level in row 0: one copy decides
    refine ⟨2, by omega, ?_⟩
    rw [hMn2 1, hNeq, hhead]
    refine (sle_append_cancel _).2 (Or.inr ?_)
    exact Or.inl (Or.inl (show q.1 < entry M 0 j0 + d0i by omega))
  rcases hq2 with hq2 | ⟨hqe2, hq3⟩
  · -- below in row 1 at the copy head: one copy decides
    refine ⟨2, by omega, ?_⟩
    rw [hMn2 1, hNeq, hhead]
    refine (sle_append_cancel _).2 (Or.inr ?_)
    exact Or.inl (Or.inr ⟨show q.1 = entry M 0 j0 + d0i by omega,
      Or.inl (show q.2.1 < entry M 1 j0 + d1i by omega)⟩)
  · -- the exact boundary: the second ascending crux
    have hqeq : q = (entry M 0 j0 + d0i, entry M 1 j0 + d1i, 0) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · dsimp only
        omega
      · dsimp only
        omega
      · dsimp only
        omega
    have hMsh : (M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, 0) :: seg M (j0 + 1) (L - 1)))
        ++ [((entry M 0 j0 + d0i, entry M 1 j0 + d1i, 1) : ℕ × ℕ × ℕ)]
        = M := by
      rw [← hsegL]
      have h1 : M.take j0 ++ seg M j0 L = M.dropLast :=
        take_gcopy_zero L1 hz hp
      rw [h1, ← hlpe]
      exact dropLast_snoc_getD (by
        intro he
        rw [he] at L1
        simp at L1)
    have hNsh : (M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, 0) :: seg M (j0 + 1) (L - 1)))
        ++ ((entry M 0 j0 + d0i, entry M 1 j0 + d1i, 0) : ℕ × ℕ × ℕ)
          :: S = N := by
      rw [← hsegL]
      have h1 : M.take j0 ++ seg M j0 L = M.dropLast :=
        take_gcopy_zero L1 hz hp
      rw [h1, hNeq, ← hqeq]
    have htk : (M.take j0).length = j0 := by
      rw [List.length_take]
      omega
    have hbk : (M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, 0)
          :: seg M (j0 + 1) (L - 1))).length = M.length - 1 := by
      rw [List.length_append, htk, List.length_cons, seg_length]
      omega
    have hle1sh : le1 ((M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, 0) :: seg M (j0 + 1) (L - 1)))
        ++ [((entry M 0 j0 + d0i, entry M 1 j0 + d1i, 1) : ℕ × ℕ × ℕ)])
        (M.take j0).length
        (M.take j0
          ++ ((entry M 0 j0, entry M 1 j0, 0)
            :: seg M (j0 + 1) (L - 1))).length := by
      rw [hMsh, htk, hbk]
      exact hle1c
    have hMst : ST_TS ((M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, 0) :: seg M (j0 + 1) (L - 1)))
        ++ [((entry M 0 j0 + d0i, entry M 1 j0 + d1i, 1) : ℕ × ℕ × ℕ)]) := by
      rw [hMsh]
      exact hM
    have hNst : ST_TS ((M.take j0
        ++ ((entry M 0 j0, entry M 1 j0, 0) :: seg M (j0 + 1) (L - 1)))
        ++ ((entry M 0 j0 + d0i, entry M 1 j0 + d1i, 0) : ℕ × ℕ × ℕ)
          :: S) := by
      rw [hNsh]
      exact hN
    obtain ⟨n', hn1, hm⟩ := asc_crux2 (ascArgDom2_of_core Hc)
      hMst hNst hRgt hd0pos hd1pos hle1sh
    rw [hMsh, htk, seg_length] at hm
    rw [show L - 1 + 1 = L from by omega] at hm
    refine ⟨n' + 1, by omega, ?_⟩
    rw [hMn2 n', hNeq, hqeq]
    refine (sle_append_cancel _).2 ?_
    exact hm

/-! ## 上昇 crux の完結と共終性 -/

theorem trioAscCrux_of_core (Hc : ArgDomCore) : TrioAscCrux := by
  intro M N q S hM hN L1 hz hsr hNeq hq
  have hle2 : srow M (M.length - 1) ≤ 2 := by
    unfold srow
    split_ifs <;> omega
  rcases Nat.eq_or_lt_of_le hle2 with h2 | hlt
  · exact trioAsc_srow2 Hc hM hN L1 hz h2 hNeq hq
  · exact trioAsc_srow1 Hc hM hN L1 hz (by omega) hNeq hq

/-- **Trio Bachmann cofinality, modulo the host-free core** — among standard
forms the fundamental sequence is cofinal below `M`. -/
theorem trio_cofinality_of_core (Hc : ArgDomCore) {M N : TrioSeq}
    (hM : ST_TS M) (hN : ST_TS N) (h : translate N <o translate M) :
    ∃ n, 1 ≤ n ∧ translate N ≤o translate (M⟦n⟧) :=
  ts_cofinality_of_crux (badCrux_of_asc (trioAscCrux_of_core Hc)) hM hN h

end Googology.Trans.BMS.TrioCof
