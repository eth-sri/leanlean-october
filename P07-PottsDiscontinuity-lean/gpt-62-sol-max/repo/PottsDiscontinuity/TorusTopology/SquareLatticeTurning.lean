module

public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.TorusTopology.LatticeSecants
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-! The discrete Umlaufsatz on the literal square lattice. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph
open Planar.Medial

/-- Compass label of an actual directed square-lattice edge: east, north,
west, south in positive cyclic order. Adjacency exhausts these four cases. -/
def squareDartCompass (d : FK.squareLattice.Dart) : Fin 4 :=
  if d.fst.1 < d.snd.1 then 0 else if d.fst.2 < d.snd.2 then 1
  else if d.snd.1 < d.fst.1 then 2 else 3

/-- The ordered geometric directions of every edge of a lattice walk. -/
def squareWalkCompassDirections {u v : ℤ × ℤ} (p : FK.squareLattice.Walk u v) :
    List (Fin 4) := p.darts.map squareDartCompass

/-- The signed quarter-turn sum, including the last-to-first edge pair. -/
def squareWalkCyclicTurn {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u) : ℤ :=
  ((squareWalkCompassDirections p).zipWith primalCompassQuarterTurn
    ((squareWalkCompassDirections p).rotate 1)).sum

private def direction (f : ℕ → ℤ × ℤ) (i : ℕ) : Fin 4 :=
  let a := f (i+1) - f i
  if 0 < a.1 then 0 else if 0 < a.2 then 1 else if a.1 < 0 then 2 else 3

private theorem cyclicTurn_rotate {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u)
    (w : ℤ × ℤ) (hw : w ∈ p.support) :
    squareWalkCyclicTurn (p.rotate w hw) = squareWalkCyclicTurn p := by
  obtain ⟨k, hk⟩ := (p.rotate_darts w hw).symm.map squareDartCompass
  change (squareWalkCompassDirections p).rotate k = squareWalkCompassDirections (p.rotate w hw) at hk
  unfold squareWalkCyclicTurn
  rw [← hk, List.rotate_rotate, ← Nat.add_comm, ← List.rotate_rotate,
    ← List.zipWith_rotate_distrib _ _ _ _ (by simp)]
  exact (List.rotate_perm _ _).sum_eq

private theorem cyclicTurn_eq_sum {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u) (hp : 0 < p.length) :
    squareWalkCyclicTurn p =
      (∑ i ∈ Finset.range (p.length-1), primalCompassQuarterTurn
        (direction p.getVert i) (direction p.getVert (i+1))) +
      primalCompassQuarterTurn (direction p.getVert (p.length-1)) (direction p.getVert 0) := by
  let L := squareWalkCompassDirections p
  have hL : L.length = p.length := by simp [L, squareWalkCompassDirections]
  have hd (i : ℕ) (hi : i < L.length) : L[i] = direction p.getVert i := by
    simp [L, squareWalkCompassDirections, Walk.darts_getElem_eq_getVert, squareDartCompass, direction]
  let f i := primalCompassQuarterTurn (direction p.getVert i)
    (direction p.getVert ((i+1) % p.length))
  have hlist : L.zipWith primalCompassQuarterTurn (L.rotate 1) = (List.range p.length).map f := by
    apply List.ext_getElem
    · simp [hL]
    intro i hi hj
    simp [hd, hL, f]
  change (L.zipWith _ _).sum = _
  rw [hlist]
  change (∑ i ∈ Finset.range p.length, f i) = _
  have he : p.length - 1 + 1 = p.length := by omega
  rw [← he, Finset.sum_range_succ, he]
  simp only [f, he, Nat.mod_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Every simple square-lattice cycle has total signed turn +4 or -4. -/
theorem squareWalkCyclicTurn_eq_four_or_neg_four {u : ℤ × ℤ}
    (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    squareWalkCyclicTurn p = 4 ∨ squareWalkCyclicTurn p = -4 := by
  classical
  obtain ⟨w, hw, hmin⟩ := p.support.toFinset.exists_min_image (fun z => toLex (Prod.swap z))
    ⟨u, by simp⟩
  let q := p.rotate w (List.mem_toFinset.mp hw)
  have hq : q.IsCycle := hp.rotate _
  let n := q.length
  let f := q.getVert
  have hn : 3 ≤ n := hq.three_le_length
  have hc : f n = f 0 := by simp [f,n]
  have hstep (i : ℕ) (hi : i < n) : FK.squareLattice.Adj (f i) (f (i+1)) := q.adj_getVert_succ hi
  have hinj : Set.InjOn f (Set.Iio n) := by
    intro i hi j hj hij
    have hi' := hi
    have hj' := hj
    exact hq.isPath_dropLast.getVert_injOn
      (show i ≤ q.dropLast.length by simpa using Nat.le_pred_of_lt hi')
      (show j ≤ q.dropLast.length by simpa using Nat.le_pred_of_lt hj')
      (by rwa [Walk.getVert_dropLast hi', Walk.getVert_dropLast hj'])
  have hlowest (i : ℕ) (hi : 0 < i) (hi' : i < n) :
      (f 0).2 < (f i).2 ∨ (f 0).2 = (f i).2 ∧ (f 0).1 < (f i).1 := by
    have hmem := (p.mem_support_rotate_iff _ _).mp (q.getVert_mem_support i)
    have hm := Prod.Lex.toLex_le_toLex.mp (hmin (f i) (List.mem_toFinset.mpr hmem))
    have hne : f 0 ≠ f i := fun ht => (Nat.ne_of_gt hi) (hinj hi' (show 0 < n by omega) ht.symm)
    have hzero : f 0 = w := by simp [f]
    rw [hzero] at hne ⊢
    simp only [ne_eq, Prod.ext_iff] at hne
    change w.2 < (f i).2 ∨ w.2 = (f i).2 ∧ w.1 ≤ (f i).1 at hm
    omega
  have ht := LatticeSecants.turn_sum f n hn hstep hinj hc hlowest
  have ht' (i : ℕ) (hi : i < n) : LatticeSecants.UnitStep (f (i+1)-f i) :=
    LatticeSecants.unitStep_sub (hstep i hi)
  have hs : (∑ i ∈ Finset.range (n-1), LatticeSecants.turn (f (i+1)-f i) (f (i+2)-f (i+1))) =
      2 * ∑ i ∈ Finset.range (n-1), primalCompassQuarterTurn (direction f i) (direction f (i+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    exact LatticeSecants.turn_eq_quarter (ht' i (by omega)) (ht' (i+1) (by omega))
  have hlast := LatticeSecants.turn_eq_quarter (ht' (n-1) (by omega)) (ht' 0 (by omega))
  change LatticeSecants.turn (f (n-1+1)-f (n-1)) (f 1-f 0) =
    2 * primalCompassQuarterTurn (direction f (n-1)) (direction f 0) at hlast
  rw [show n-1+1 = n by omega] at hlast
  dsimp only at ht
  rw [hs, hlast, ← mul_add, ← cyclicTurn_eq_sum q (show 0 < n by omega), cyclicTurn_rotate] at ht
  omega

end PottsDiscontinuity.TorusTopology
