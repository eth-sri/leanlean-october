module

public import Chazelle.Core.DownPhaseHostArc
public import Chazelle.Core.RestorePrune

/-!
# WP-E, the search: the pieces tile the arc

The cutter's pieces `[s i, e i]` (`i < q`) of an arc `[a, b]` (`a ≠ b`, keys in `[0, n)`) are
consecutive key intervals from `a` to `b` (`s 0 = a`, `e (q - 1) = b`, `e i = s (i + 1)`, and `e i`
strictly between `s i` and `b` before the last piece).  Unwrapped from `a`, their ends increase
(`tile_mono`); every key of the closed arc lies in a closed piece (`tile_cover`), and every key
strictly inside a piece is strictly inside the arc (`tile_inner`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sideInArc)
open DownHost ArcT

variable {n a b : ℝ} {q : ℕ} {s e : ℕ → ℝ}

/-- The hypotheses of a tiling. -/
structure Tile (n a b : ℝ) (q : ℕ) (s e : ℕ → ℝ) : Prop where
  ha : 0 ≤ a ∧ a < n
  hb : 0 ≤ b ∧ b < n
  hab : a ≠ b
  hq : 1 ≤ q
  hs : ∀ i, i < q → 0 ≤ s i ∧ s i < n
  he : ∀ i, i < q → 0 ≤ e i ∧ e i < n
  s0 : s 0 = a
  eq : e (q - 1) = b
  hse : ∀ i, i + 1 < q → e i = s (i + 1)
  hin : ∀ i, i + 1 < q → sideInArc (s i) b (e i)

theorem unwrap_b (h : Tile n a b q s e) : a < unwrapK n a b := by
  have := unwrapK_bounds h.ha h.hb
  unfold unwrapK at *
  split_ifs at * with h1
  · exact lt_of_le_of_ne h1 h.hab
  · linarith [h.ha.2, h.hb.1]

/-- **The unwrapped piece starts increase** and stay below the arc's end. -/
theorem tile_mono (h : Tile n a b q s e) :
    ∀ i, i < q → a ≤ unwrapK n a (s i) ∧ unwrapK n a (s i) < unwrapK n a b ∧
      unwrapK n a (s i) < unwrapK n a (e i) ∧ unwrapK n a (e i) ≤ unwrapK n a b := by
  have hub := unwrap_b h
  have hlast : ∀ i, i < q → a ≤ unwrapK n a (s i) → unwrapK n a (s i) < unwrapK n a b →
      unwrapK n a (s i) < unwrapK n a (e i) ∧ unwrapK n a (e i) ≤ unwrapK n a b := by
    intro i hi h1 h2
    by_cases hl : i + 1 < q
    · have := (cyc_unwrap h.ha (h.hs i hi) h.hb (h.he i hi) h2).1 (h.hin i hl)
      exact ⟨this.1, this.2.le⟩
    · have : i = q - 1 := by omega
      subst this
      rw [h.eq]; exact ⟨h2, le_rfl⟩
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : unwrapK n a (s 0) = a := by rw [h.s0, unwrapK_self]
    refine ⟨by rw [h0], by rw [h0]; exact hub, ?_⟩
    exact hlast 0 hi (by rw [h0]) (by rw [h0]; exact hub)
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2, h3, -⟩ := ih (by omega)
    have hn := (cyc_unwrap h.ha (h.hs i (by omega)) h.hb (h.he i (by omega)) h2).1
      (h.hin i hi)
    rw [← h.hse i hi]
    refine ⟨by linarith, hn.2, ?_⟩
    have := hlast (i + 1) hi (by rw [← h.hse i hi]; linarith) (by rw [← h.hse i hi]; exact hn.2)
    rw [← h.hse i hi] at this
    exact this

/-- **Every key of the closed arc lies in a closed piece.** -/
theorem tile_cover (h : Tile n a b q s e) {x : ℝ} (_hx : 0 ≤ x ∧ x < n)
    (hxa : a ≤ unwrapK n a x) (hxb : unwrapK n a x ≤ unwrapK n a b) :
    ∃ i, i < q ∧ unwrapK n a (s i) ≤ unwrapK n a x ∧ unwrapK n a x ≤ unwrapK n a (e i) := by
  have hm := tile_mono h
  -- the last piece starting at or before `x`
  classical
  have hex : ∃ i, i < q ∧ unwrapK n a (s i) ≤ unwrapK n a x := ⟨0, h.hq, by
    rw [h.s0, unwrapK_self]; exact hxa⟩
  let i := Nat.findGreatest (fun i => i < q ∧ unwrapK n a (s i) ≤ unwrapK n a x) q
  have hi : i < q ∧ unwrapK n a (s i) ≤ unwrapK n a x := by
    obtain ⟨j, hj, hj'⟩ := hex
    exact Nat.findGreatest_spec (P := fun i => i < q ∧ unwrapK n a (s i) ≤ unwrapK n a x)
      hj.le ⟨hj, hj'⟩
  refine ⟨i, hi.1, hi.2, ?_⟩
  by_contra hc
  push Not at hc
  by_cases hl : i + 1 < q
  · have hmax := Nat.le_findGreatest (P := fun i => i < q ∧ unwrapK n a (s i) ≤ unwrapK n a x)
      (m := i + 1) hl.le ⟨hl, by rw [← h.hse i hl]; exact hc.le⟩
    omega
  · have : i = q - 1 := by omega
    have he' : e i = b := by rw [this, h.eq]
    rw [he'] at hc
    linarith

/-- **A key strictly inside a piece is strictly inside the arc.** -/
theorem tile_inner (h : Tile n a b q s e) {i : ℕ} (hi : i < q) {y : ℝ} (hy : 0 ≤ y ∧ y < n)
    (hiy : sideInArc (s i) (e i) y) : sideInArc a b y := by
  obtain ⟨h1, -, h3, h4⟩ := tile_mono h i hi
  have hub := unwrap_b h
  have := (cyc_unwrap h.ha (h.hs i hi) (h.he i hi) hy h3).1 hiy
  have ha0 : unwrapK n a a = a := unwrapK_self
  exact (cyc_unwrap h.ha h.ha h.hb hy (by rw [ha0]; exact hub)).2
    ⟨by rw [ha0]; linarith [this.1], by linarith [this.2]⟩

end

end Restore

end Chazelle.Core
