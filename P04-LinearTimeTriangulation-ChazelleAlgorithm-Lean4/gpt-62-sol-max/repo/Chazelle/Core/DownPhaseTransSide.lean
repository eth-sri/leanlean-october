module

public import Chazelle.Core.DownPhaseTransDeg
public import Chazelle.Core.BruteCorner

/-!
# WP-M (T, part 5): the inner side of the top chain

The interior walk of `Q` (`interiorWalk Q`: `Q` itself when `LeftInside Q`, else `Q` reversed)
runs along one side of the double boundary of the top chain `C`: side `A` when `LeftInside Q`,
side `B` otherwise.  With distinct vertex heights that side is not split at the top vertex (the
up direction is not in the interior corner there, `up_not_corner`), so it is one contiguous run of
the chain walk: **chain walk vertex `j + c₀` is interior walk vertex `j` for `j ≤ m`**
(`exists_shift`), and the chain walk edges `j + c₀` (`j < m`) are counted.
-/

namespace Chazelle.Core

namespace Trans

@[expose] public section

open Set Metric
open Chazelle.Chain (sidePt sideLeft sideLeftOf sideCcw)
open TourA (sA tourA)
open TourB (tourB)

variable {Q : Polygon} {C : Chain}

/-- Distinct vertex heights. -/
def DistinctH (Q : Polygon) : Prop :=
  ∀ i j, i < Q.n → j < Q.n → i ≠ j → (Q.vtx i).2 ≠ (Q.vtx j).2

/-- **The up direction lies in one of the two corners** at a vertex above both neighbours. -/
theorem up_in_one_corner {a v b : Point} {h : ℝ} (hh : 0 < h) (ha : a.2 < v.2) (hb : b.2 < v.2) :
    sideCcw (b - v) ((0 : ℝ), h) (a - v) ∨ sideCcw (a - v) ((0 : ℝ), h) (b - v) := by
  rw [Brute.sideCcw_up hh ha hb.ne, Brute.sideCcw_up hh hb ha.ne]
  have e : Chazelle.det b v a = -Chazelle.det a v b := by unfold Chazelle.det; ring
  rw [e]
  have hD : Chazelle.det a v b = (v.1 - a.1) * (b.2 - a.2) - (b.1 - a.1) * (v.2 - a.2) := rfl
  rcases lt_trichotomy (Chazelle.det a v b) 0 with hd | hd | hd
  · by_cases h1 : v.1 < b.1 ∨ a.1 < v.1
    · exact Or.inl (Or.inr (Or.inl ⟨hd, h1⟩))
    · push Not at h1
      right; left
      refine ⟨by linarith, ?_, ?_⟩
      · rcases h1.2.lt_or_eq with h2 | h2
        · exact h2
        · exfalso; rw [h2] at hD; nlinarith
      · rcases h1.1.lt_or_eq with h2 | h2
        · exact h2
        · exfalso; rw [← h2] at hD; nlinarith
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hd, hb⟩)))
  · by_cases h1 : v.1 < b.1 ∧ a.1 < v.1
    · exact Or.inl (Or.inl ⟨hd, h1⟩)
    · right; right; left
      refine ⟨by linarith, ?_⟩
      by_contra h2; push Not at h1 h2
      rcases lt_or_ge v.1 b.1 with h3 | h3
      · have h4 := h1 h3
        have h5 : a.1 = v.1 := le_antisymm h2.1 h4
        rw [h5] at hD; nlinarith
      · have h5 : b.1 = v.1 := le_antisymm h3 h2.2
        rw [h5] at hD; nlinarith

/-- **The up direction is not in the corner of the interior walk at the top vertex.** -/
theorem up_not_corner (hQ : Q.Simple) (T : Top Q C) {p : ℕ} (hp : p < (interiorWalk Q).n)
    (hpv : (interiorWalk Q).vtx p = C.top) :
    ¬ sideCcw ((interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n) - C.top)
      (C.slitTop - C.top)
      ((interiorWalk Q).vtx ((p + (interiorWalk Q).n - 1) % (interiorWalk Q).n) - C.top) := by
  intro hc
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  set W := interiorWalk Q with hW
  have hup : ∀ ε : ℝ, 0 < ε → sideLeft W p 0 (C.top + ε • (C.slitTop - C.top)) := by
    intro ε hε
    rw [Chazelle.Chain.sideLeft_zero]
    unfold sideLeftOf
    rw [hpv, add_sub_cancel_left]
    have := BoxT.sideCcw_smul one_pos hε one_pos
      (W.vtx ((p + 1) % W.n) - C.top) (C.slitTop - C.top)
      (W.vtx ((p + W.n - 1) % W.n) - C.top)
    rw [one_smul, one_smul] at this
    exact this.2 hc
  obtain ⟨rC, hrC, hclean⟩ := FactsInterior.clean hWs hWo hp le_rfl zero_lt_one
  have hrad : C.top.2 < C.radius := C.top_snd_lt_radius
  set ε := rC / (2 * (C.radius - C.top.2)) with hε
  have hε0 : 0 < ε := div_pos hrC (by linarith)
  set y := C.top + ε • (C.slitTop - C.top) with hy
  have hy2 : y.2 = C.top.2 + ε * (C.radius - C.top.2) := by
    show (C.top + ε • (C.slitTop - C.top)).2 = _
    simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    rfl
  have hy1 : y.1 = C.top.1 := by
    show (C.top + ε • (C.slitTop - C.top)).1 = _
    simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    rw [show C.slitTop.1 = C.top.1 from rfl]
    ring
  have hpos : 0 < ε * (C.radius - C.top.2) := mul_pos hε0 (by linarith)
  have hdist : dist y C.top = rC / 2 := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hy1, hy2, sub_self, abs_zero,
      show C.top.2 + ε * (C.radius - C.top.2) - C.top.2 = ε * (C.radius - C.top.2) by ring,
      abs_of_pos hpos, max_eq_right hpos.le, hε]
    have : C.radius - C.top.2 ≠ 0 := by linarith
    field_simp
  have hpt : sidePt W p 0 = C.top := by rw [Chazelle.Chain.sidePt_zero, hpv]
  have hyb : y ∈ ball (sidePt W p 0) rC := by rw [hpt, mem_ball, hdist]; linarith
  have hyD : y ∈ Q.filled \ Q.boundary := by
    by_contra hyD
    exact hclean y hyb (by rw [hWb, hWf]; exact hyD) (hup ε hε0)
  have := T.filled_below_top hQ hyD.1
  rw [hy2] at this
  linarith

theorem iw_n : (interiorWalk Q).n = Q.n := by
  unfold interiorWalk; split_ifs
  · rfl
  · exact FactsInterior.rev_n Q

theorem iw_vtx_left (h : Mountain.LeftInside Q) (j : ℕ) : (interiorWalk Q).vtx j = Q.vtx j := by
  unfold interiorWalk; simp only [h, ↓reduceIte]

theorem iw_vtx_right (h : ¬ Mountain.LeftInside Q) {j : ℕ} (hj : j < Q.n) :
    (interiorWalk Q).vtx j = Q.vtx (Q.n - 1 - j) := by
  unfold interiorWalk; simp only [h, ↓reduceIte]; exact FactsInterior.rev_vtx Q j hj

/-- The neighbours of the top vertex are strictly lower. -/
theorem Top.nbr_lt (T : Top Q C) (hD : DistinctH Q) {k : ℕ} (hk : k < Q.n) (hkT : k ≠ C.topIdx) :
    (Q.vtx k).2 < C.top.2 := by
  have hT : C.topIdx < Q.n := by have := C.topIdx_le; have := T.hm; omega
  have h1 := T.vtx_le_top hk
  have h2 : C.top = Q.vtx C.topIdx := T.vertex_eq hT
  rw [h2] at h1 ⊢
  exact lt_of_le_of_ne h1 (hD k C.topIdx hk hT hkT)

/-- **The tour start is not inside the inner side.** -/
theorem sA_inner (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q) :
    (Mountain.LeftInside Q → sA C C.sideBeta = 0 ∨ C.m ≤ sA C C.sideBeta) ∧
      (¬ Mountain.LeftInside Q → sA C C.sideBeta ≤ C.m) := by
  have hTm := C.topIdx_le
  have hmn : C.m + 1 = Q.n := T.hm
  have hup : (C.slitTop - C.top) = ((0 : ℝ), C.radius - C.top.2) := by
    apply Prod.ext
    · show C.slitTop.1 - C.top.1 = 0; rw [show C.slitTop.1 = C.top.1 from rfl]; ring
    · rfl
  have hrad : 0 < C.radius - C.top.2 := by have := C.top_snd_lt_radius; linarith
  have hvT : ∀ k, k ≤ C.m → C.vertex k = Q.vtx k := fun k hk => T.vertex_eq (by omega)
  -- the corner of the top vertex in `Q`'s own order, and reversed
  have hbeta := C.sideBeta_eq_true_iff
  unfold sA
  constructor
  · intro hL
    rcases C.sideS_mod C.sideBeta with ⟨hs, hc⟩ | ⟨hs, hT0, -⟩
    · rw [hs]
      rcases hc with hb | hT | hT
      · -- `β = true` with the top strictly inside: impossible
        by_contra hcon
        push Not at hcon
        have h0 : 0 < C.topIdx := Nat.pos_of_ne_zero hcon.1
        have h1 : C.topIdx < C.m := hcon.2
        have hc := hbeta.1 hb
        apply up_not_corner hQ T (p := C.topIdx) (by rw [iw_n]; omega)
          (by rw [iw_vtx_left hL]; exact (hvT _ hTm).symm)
        rw [iw_n, iw_vtx_left hL, iw_vtx_left hL,
          Nat.mod_eq_of_lt (show C.topIdx + 1 < Q.n by omega),
          show (C.topIdx + Q.n - 1) % Q.n = C.topIdx - 1 by
            rw [show C.topIdx + Q.n - 1 = (C.topIdx - 1) + Q.n by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)],
          ← hvT _ (by omega), ← hvT _ (by omega)]
        exact hc
      · left; exact hT
      · right; omega
    · rw [hs]; right; omega
  · intro hL
    rcases C.sideS_mod C.sideBeta with ⟨hs, -⟩ | ⟨hs, hT0, hb⟩
    · rw [hs]; exact hTm
    · rw [hs]
      by_contra hcon
      push Not at hcon
      have h1 : C.topIdx < C.m := by omega
      -- the reversed corner contains the up direction
      have hnc : ¬ sideCcw (C.vertex (C.topIdx + 1) - C.top) (C.slitTop - C.top)
          (C.vertex (C.topIdx - 1) - C.top) := fun h => by
        have := hbeta.2 h; rw [hb] at this; exact Bool.false_ne_true this
      have hlo1 : (C.vertex (C.topIdx - 1)).2 < C.top.2 := by
        rw [hvT _ (by omega)]; exact T.nbr_lt hD (by omega) (by omega)
      have hlo2 : (C.vertex (C.topIdx + 1)).2 < C.top.2 := by
        rw [hvT _ (by omega)]; exact T.nbr_lt hD (by omega) (by omega)
      have hor := up_in_one_corner (v := C.top) hrad hlo1 hlo2
      rw [← hup] at hor
      have hrev := hor.resolve_left hnc
      apply up_not_corner hQ T (p := C.m - C.topIdx) (by rw [iw_n]; omega)
        (by rw [iw_vtx_right hL (by omega), show Q.n - 1 - (C.m - C.topIdx) = C.topIdx by omega];
            exact (hvT _ hTm).symm)
      rw [iw_n, iw_vtx_right hL (Nat.mod_lt _ (by omega)),
        iw_vtx_right hL (Nat.mod_lt _ (by omega)),
        Nat.mod_eq_of_lt (show C.m - C.topIdx + 1 < Q.n by omega),
        show (C.m - C.topIdx + Q.n - 1) % Q.n = C.m - C.topIdx - 1 by
          rw [show C.m - C.topIdx + Q.n - 1 = (C.m - C.topIdx - 1) + Q.n by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
        show Q.n - 1 - (C.m - C.topIdx + 1) = C.topIdx - 1 by omega,
        show Q.n - 1 - (C.m - C.topIdx - 1) = C.topIdx + 1 by omega,
        ← hvT _ (by omega), ← hvT _ (by omega)]
      exact hrev

/-- **The inner side is one run of the chain walk.** -/
theorem exists_shift (hQ : Q.Simple) (T : Top Q C) (hD : DistinctH Q) :
    ∃ c₀ : ℕ, 6 ≤ c₀ ∧ c₀ + C.m ≤ 2 * C.m + 6 ∧
      ∀ j, j ≤ C.m → (C.sideWalk C.sideBeta).vtx (j + c₀) = (interiorWalk Q).vtx j := by
  have hmn : C.m + 1 = Q.n := T.hm
  have hm1 := C.one_le
  have hvT : ∀ k, k ≤ C.m → C.vertex k = Q.vtx k := fun k hk => T.vertex_eq (by omega)
  obtain ⟨hL1, hL2⟩ := sA_inner hQ T hD
  by_cases hL : Mountain.LeftInside Q
  · have hs := hL1 hL
    have hlin : ∀ j, j < C.m → tourA C C.sideBeta j = tourA C C.sideBeta 0 + j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [TourA.tourA_succ (by omega) (by omega), ih (by omega)]; ring
    refine ⟨tourA C C.sideBeta 0 + 6, by omega, ?_, fun j hj => ?_⟩
    · have := TourA.tourA_lt (C := C) (β := C.sideBeta) (C.m - 1)
      rw [hlin _ (by omega)] at this; omega
    · rw [iw_vtx_left hL]
      rcases hj.lt_or_eq with hj | rfl
      · rw [show j + (tourA C C.sideBeta 0 + 6) = tourA C C.sideBeta j + 6 by
          rw [hlin j hj]; ring, TourA.vtx_tourA hj, hvT j hj.le]
      · have e := TourA.vtx_tourA_succ (C := C) (β := C.sideBeta) (k := C.m - 1) (by omega)
        rw [Nat.sub_add_cancel hm1, C.sideWalk_next_tour _ (TourA.tourA_lt _),
          hlin _ (by omega)] at e
        rw [← hvT _ le_rfl, ← e]
        congr 1; omega
  · have hs := hL2 hL
    have hlin : ∀ j, j < C.m → tourB C C.sideBeta (C.m - 1 - j) = tourB C C.sideBeta (C.m - 1) + j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ j ih =>
        have := TourB.tourB_succ (C := C) (β := C.sideBeta) (k := C.m - 1 - (j + 1)) (by omega)
          (by omega)
        rw [show C.m - 1 - (j + 1) + 1 = C.m - 1 - j by omega, ih (by omega)] at this
        rw [this]; ring
    refine ⟨tourB C C.sideBeta (C.m - 1) + 6, by omega, ?_, fun j hj => ?_⟩
    · have := TourB.tourB_lt (C := C) (β := C.sideBeta) (C.m - 1 - (C.m - 1))
      rw [hlin _ (by omega)] at this; omega
    · rw [iw_vtx_right hL (by omega)]
      rcases hj.lt_or_eq with hj | rfl
      · rw [show j + (tourB C C.sideBeta (C.m - 1) + 6) = tourB C C.sideBeta (C.m - 1 - j) + 6 by
          rw [hlin j hj]; ring, TourB.vtx_tourB (by omega),
          show C.m - 1 - j + 1 = Q.n - 1 - j by omega, hvT _ (by omega)]
      · have e := TourB.vtx_tourB_succ (C := C) (β := C.sideBeta) (k := 0) (by omega)
        rw [C.sideWalk_next_tour _ (TourB.tourB_lt _)] at e
        have h0 := hlin (C.m - 1) (by omega)
        rw [show C.m - 1 - (C.m - 1) = 0 by omega] at h0
        rw [show Q.n - 1 - C.m = 0 by omega, ← hvT 0 (by omega), ← e, h0]
        congr 1; omega

end

end Trans

end Chazelle.Core
