module

public import PottsDiscontinuity.FK.Lattice
public import PottsDiscontinuity.TorusTopology.PlanarFiniteCompassFan
public import Mathlib.Tactic

/-!
The discrete secant proof of the turning theorem. On the triangle of pairs of
unequal points of a polygon, record the direction of each secant in eighths
of a turn (the axes and the four open quadrants). The angular increment is
locally a difference of lifted angles, so it sums to zero around each cell.
Sweeping from the adjacent-vertex diagonal to the outer two sides reduces
turning to the two directions at a lowest, leftmost vertex.
-/

public section

namespace PottsDiscontinuity.TorusTopology.LatticeSecants
open Finset

private def octant (v : ℤ × ℤ) : ℤ :=
  if 0 < v.2 then (if 0 < v.1 then 1 else if v.1 = 0 then 2 else 3)
  else if v.2 = 0 then (if 0 < v.1 then 0 else 4)
  else if v.1 < 0 then 5 else if v.1 = 0 then 6 else 7

private def swing (a b : ℤ) : ℤ := (b - a + 3) % 8 - 3

private theorem swing_eq_sub {a b : ℤ} (h₁ : -3 ≤ b - a) (h₂ : b - a ≤ 4) :
    swing a b = b - a := by
  unfold swing
  omega

private theorem octant_neg {v : ℤ × ℤ} (hv : v ≠ 0) :
    octant (-v) = (octant v + 4) % 8 := by
  simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hv
  simp only [octant, Prod.fst_neg, Prod.snd_neg]
  split_ifs <;> omega

private theorem swing_neg {a b : ℤ × ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    swing (octant (-a)) (octant (-b)) = swing (octant a) (octant b) := by
  rw [octant_neg ha, octant_neg hb]
  unfold swing
  omega

/-- An oriented unit step. -/
def UnitStep (v : ℤ × ℤ) : Prop := v = (1,0) ∨ v = (0,1) ∨ v = (-1,0) ∨ v = (0,-1)

theorem unitStep_sub {u v : ℤ × ℤ} (h : FK.squareLattice.Adj u v) : UnitStep (v - u) := by
  simp only [UnitStep, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
  have := (FK.squareLattice_adj_iff u v).mp h
  omega

private theorem unitStep_neg {v : ℤ × ℤ} (h : UnitStep v) : UnitStep (-v) := by
  rcases h with rfl | rfl | rfl | rfl <;> (unfold UnitStep; decide)

private theorem corner {a b : ℤ × ℤ} (ha : UnitStep a) (hb : UnitStep b) (h : a + b ≠ 0) :
    swing (octant a) (octant (a + b)) + swing (octant (a + b)) (octant b) =
      swing (octant a) (octant b) := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl 
  all_goals trivial

private theorem corner_sub {u v w : ℤ × ℤ} (h₁ : UnitStep (v-u)) (h₂ : UnitStep (w-v))
    (h : w ≠ u) :
    swing (octant (v-u)) (octant (w-u)) + swing (octant (w-u)) (octant (w-v)) =
      swing (octant (v-u)) (octant (w-v)) := by
  have he : (v - u) + (w - v) = w-u := by abel
  simpa using corner h₁ h₂ (by rwa [he, sub_ne_zero])

private def side (d : Fin 4) (v : ℤ × ℤ) : ℤ :=
  ![v.1, v.2, -v.1, -v.2] d

private theorem swing_center (d : Fin 4) (v : ℤ × ℤ) (hv : 0 < side d v) :
    -1 ≤ swing (2 * (d.val : ℤ)) (octant v) ∧ swing (2 * (d.val : ℤ)) (octant v) ≤ 1 := by
  fin_cases d <;> simp [side, swing, octant] at * <;>
    omega

private theorem swing_eq_of_side (d : Fin 4) {a b : ℤ × ℤ}
    (ha : 0 < side d a) (hb : 0 < side d b) :
    swing (octant a) (octant b) =
      swing (2 * (d.val : ℤ)) (octant b) - swing (2 * (d.val : ℤ)) (octant a) := by
  have h₁ := swing_center d a ha
  have h₂ := swing_center d b hb
  unfold swing at *
  omega

-- Each unit edge has just its endpoints as integer points in its bounding box.
private theorem bbox_unit {u v p : ℤ × ℤ} (huv : FK.squareLattice.Adj u v)
    (hx₁ : min u.1 v.1 ≤ p.1) (hx₂ : p.1 ≤ max u.1 v.1)
    (hy₁ : min u.2 v.2 ≤ p.2) (hy₂ : p.2 ≤ max u.2 v.2) : p = u ∨ p = v := by
  simp only [FK.squareLattice_adj_iff] at huv
  simp only [Prod.ext_iff]
  omega

-- Disjoint unit lattice edges have a strict separating coordinate line.
private theorem separated {u v w z : ℤ × ℤ} (huv : FK.squareLattice.Adj u v)
    (hwz : FK.squareLattice.Adj w z) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) :
    ∃ d : Fin 4, 0 < side d (w-u) ∧ 0 < side d (w-v) ∧
      0 < side d (z-u) ∧ 0 < side d (z-v) := by
  have h : max u.1 v.1 < min w.1 z.1 ∨ max u.2 v.2 < min w.2 z.2 ∨
      max w.1 z.1 < min u.1 v.1 ∨ max w.2 z.2 < min u.2 v.2 := by
    by_contra! h
    let p := (max (min u.1 v.1) (min w.1 z.1), max (min u.2 v.2) (min w.2 z.2))
    have h₁ := bbox_unit (p := p) huv (le_max_left ..) (max_le (min_le_max ..) h.1)
      (le_max_left ..) (max_le (min_le_max ..) h.2.1)
    have h₂ := bbox_unit (p := p) hwz (le_max_right ..) (max_le h.2.2.1 (min_le_max ..))
      (le_max_right ..) (max_le h.2.2.2 (min_le_max ..))
    rcases h₁ with hp | hp <;> rw [hp] at h₂ <;> tauto
  rcases h with h | h | h | h
  · refine ⟨0, ?_⟩; simp [side]; omega
  · refine ⟨1, ?_⟩; simp [side]; omega
  · refine ⟨2, ?_⟩; simp [side]; omega
  · refine ⟨3, ?_⟩; simp [side]; omega

private theorem square {u v w z : ℤ × ℤ} (huv : FK.squareLattice.Adj u v)
    (hwz : FK.squareLattice.Adj w z) (huw : u ≠ w) (huz : u ≠ z) (hvw : v ≠ w) (hvz : v ≠ z) :
    let d := swing (octant (w-u)) (octant (z-v))
    (swing (octant (w-u)) (octant (z-u)) + swing (octant (z-u)) (octant (z-v)) = d) ∧
    (swing (octant (w-u)) (octant (w-v)) + swing (octant (w-v)) (octant (z-v)) = d) := by
  obtain ⟨d, h₁,h₂,h₃,h₄⟩ := separated huv hwz huw huz hvw hvz
  dsimp only
  rw [swing_eq_of_side d h₁ h₃, swing_eq_of_side d h₃ h₄,
    swing_eq_of_side d h₁ h₂, swing_eq_of_side d h₂ h₄, swing_eq_of_side d h₁ h₄]
  constructor <;> ring

-- Transport one horizontal step through a strip of flat cells.
private theorem sweep_row (H V : ℕ → ℕ → ℤ) (i k : ℕ) (hik : i+2 ≤ k)
    (h : ∀ j, i+1 < j → j < k → V i j + H i (j+1) = H i j + V (i+1) j) :
    V i (i+1) + H i (i+2) + (∑ j ∈ Ico (i+2) k, V (i+1) j) =
      (∑ j ∈ Ico (i+1) k, V i j) + H i k := by
  have ht := Finset.sum_congr (rfl : Ico (i+2) k = Ico (i+2) k)
    (fun j hj => show H i (j+1) - H i j = V (i+1) j - V i j by
      have ⟨h₁,h₂⟩ := mem_Ico.mp hj
      linarith [h j (by omega) h₂])
  rw [sum_Ico_sub (H i) hik, sum_sub_distrib] at ht
  rw [sum_eq_sum_Ico_succ_bot (show i+1 < k by omega)]
  linarith

-- The missing corner cell shortens only the first strip by one step.
private theorem sweep_corner (H V : ℕ → ℕ → ℤ) (n : ℕ) (hn : 3 ≤ n)
    (h : ∀ i j, i+1 < j → j < n → (i ≠ 0 ∨ j+1 ≠ n) →
      V i j + H i (j+1) = H i j + V (i+1) j) :
    (∑ i ∈ range (n-1), (V i (i+1) + H i (i+2))) =
      (∑ j ∈ Ico 1 (n-1), V 0 j) + (H 0 (n-1) + V 1 (n-1)) +
        ∑ i ∈ Ico 1 (n-1), H i n := by
  let S i := ∑ j ∈ Ico (i+1) n, V i j
  have hs : S 1 = (∑ j ∈ Ico 2 (n-1), V 1 j) + V 1 (n-1) := by
    simpa [show n-1+1=n by omega] using
          sum_Ico_succ_top (f := V 1) (show 2 ≤ n-1 by omega)
  have hr : (∑ i ∈ Ico 1 (n-1), (V i (i+1) + H i (i+2))) = S 1 + ∑ i ∈ Ico 1 (n-1), H i n := calc
    _ = ∑ i ∈ Ico 1 (n-1), (-(S (i+1) - S i) + H i n) := by
      apply sum_congr rfl
      intro i hi
      have ⟨hl,hu⟩ := mem_Ico.mp hi
      have hrow := sweep_row H V i n (by omega) (fun j hj hj' => h i j hj hj' (Or.inl (by omega)))
      linarith
    _ = _ := by
      rw [sum_add_distrib, sum_neg_distrib, sum_Ico_sub S (by omega)]
      simp [S, show n-1+1=n by omega]
  have h0 := sweep_row H V 0 (n-1) (by omega) (fun j hj hj' => h 0 j hj (by omega) (Or.inr (by omega)))
  rw [← Nat.Ico_zero_eq_range, sum_eq_sum_Ico_succ_bot (show 0 < n-1 by omega), hr, hs]
  linarith

private theorem top_octant {v : ℤ × ℤ} (h : 0 < v.2 ∨ v.2 = 0 ∧ 0 < v.1) :
    0 ≤ octant v ∧ octant v ≤ 3 := by
  unfold octant
  split_ifs <;> omega

private theorem outer_turn {a b : ℤ × ℤ} (ha : UnitStep a) (hb : UnitStep b) (hne : a ≠ b)
    (ha' : 0 ≤ octant a ∧ octant a ≤ 3) (hb' : 0 ≤ octant b ∧ octant b ≤ 3) :
    2 * (octant b - octant a) + 2 * swing (octant (-b)) (octant a) = 8 ∨
    2 * (octant b - octant a) + 2 * swing (octant (-b)) (octant a) = -8 := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  all_goals norm_num [octant, swing, Prod.fst_neg, Prod.snd_neg] at *

/-- Successive lattice steps turn in units of an eighth of a revolution. -/
def turn (a b : ℤ × ℤ) : ℤ := swing (octant a) (octant b)

/-- The total signed turn of a simple lattice polygon based at its lowest,
leftmost vertex is a full turn, with either sign. -/
theorem turn_sum (f : ℕ → ℤ × ℤ) (n : ℕ) (hn : 3 ≤ n)
    (hstep : ∀ i < n, FK.squareLattice.Adj (f i) (f (i+1)))
    (hinj : Set.InjOn f (Set.Iio n)) (hclose : f n = f 0)
    (hmin : ∀ i, 0 < i → i < n → (f 0).2 < (f i).2 ∨
      (f 0).2 = (f i).2 ∧ (f 0).1 < (f i).1) :
    let t := (∑ i ∈ range (n-1), turn (f (i+1)-f i) (f (i+2)-f (i+1))) +
      turn (f n-f (n-1)) (f 1-f 0)
    t = 8 ∨ t = -8 := by
  have hne (i j : ℕ) (hi : i < n) (hj : j ≤ n) (hij : i < j) (he : i ≠ 0 ∨ j ≠ n) :
      f j ≠ f i := by
    intro hh
    by_cases h : j = n
    · subst j
      rw [hclose] at hh
      have := hinj (show 0 < n by omega) hi hh
      omega
    · have := hinj (show j < n by omega) hi hh
      omega
  let A i j := octant (f j - f i)
  let H i j := swing (A i j) (A (i+1) j)
  let V i j := swing (A i j) (A i (j+1))
  have hcell (i j : ℕ) (hij : i+1 < j) (hj : j < n) (he : i ≠ 0 ∨ j+1 ≠ n) :
      V i j + H i (j+1) = H i j + V (i+1) j := by
    have h := square (hstep i (by omega)) (hstep j hj)
      (hne i j (by omega) (by omega) (by omega) (by omega)).symm
      (hne i (j+1) (by omega) (by omega) (by omega) he).symm
      (hne (i+1) j (by omega) (by omega) hij (by omega)).symm
      (hne (i+1) (j+1) (by omega) (by omega) (by omega) (by omega)).symm
    exact h.1.trans h.2.symm
  have hdiag : (∑ i ∈ range (n-1), (V i (i+1) + H i (i+2))) =
      ∑ i ∈ range (n-1), turn (f (i+1)-f i) (f (i+2)-f (i+1)) := by
    apply sum_congr rfl
    intro i hi
    have hi := mem_range.mp hi
    exact corner_sub (unitStep_sub (hstep i (by omega))) (unitStep_sub (hstep (i+1) (by omega)))
      (hne i (i+2) (by omega) (by omega) (by omega) (by omega))
  have htop (i : ℕ) (hi : 0 < i) (hi' : i < n) : 0 ≤ A 0 i ∧ A 0 i ≤ 3 :=
    top_octant (by
      simp only [Prod.fst_sub, Prod.snd_sub, sub_pos, sub_eq_zero]
      rw [eq_comm (a := (f i).2)]
      exact hmin i hi hi')
  have hside : (∑ j ∈ Ico 1 (n-1), V 0 j) = A 0 (n-1) - A 0 1 := by
    rw [← sum_Ico_sub (A 0) (show 1 ≤ n-1 by omega)]
    apply sum_congr rfl
    intro j hj
    have ⟨hl,hr⟩ := mem_Ico.mp hj
    have := htop j (by omega) (by omega)
    have := htop (j+1) (by omega) (by omega)
    exact swing_eq_sub (by omega) (by omega)
  have hopp : (∑ i ∈ Ico 1 (n-1), H i n) = ∑ i ∈ Ico 1 (n-1), V 0 i := by
    apply sum_congr rfl
    intro i hi
    have ⟨hl,hr⟩ := mem_Ico.mp hi
    have h₁ := hne 0 i (by omega) (by omega) (by omega) (by omega)
    have h₂ := hne 0 (i+1) (by omega) (by omega) (by omega) (by omega)
    simpa [H, A, hclose] using swing_neg (sub_ne_zero.mpr h₁) (sub_ne_zero.mpr h₂)
  let a := f 1-f 0
  let b := f (n-1)-f 0
  have ha := unitStep_sub (hstep 0 (by omega))
  have hb : UnitStep b := by
    simpa [hclose, show n-1+1=n by omega] using
          unitStep_neg (unitStep_sub (hstep (n-1) (by omega)))
  have hcorner : H 0 (n-1) + V 1 (n-1) = turn (-b) a := by
    have he : b + -a = f (n-1) - f 1 := by dsimp [a,b]; abel
    have hc := corner hb (unitStep_neg ha) (by
      rw [he, sub_ne_zero]; exact hne 1 (n-1) (by omega) (by omega) (by omega) (by omega))
    have hn' := swing_neg (a := b) (b := -a)
      (sub_ne_zero.mpr (hne 0 (n-1) (by omega) (by omega) (by omega) (by omega)))
      (neg_ne_zero.mpr (sub_ne_zero.mpr (hne 0 1 (by omega) (by omega) (by omega) (by omega))))
    rw [neg_neg] at hn'
    simpa [V, A, turn, show n-1+1=n by omega, hclose, b] using hc.trans hn'.symm
  have htotal := sweep_corner H V n hn hcell
  rw [hdiag, hopp, hside, hcorner] at htotal
  have hab : a ≠ b := by
    dsimp [a,b]
    simpa using (hne 1 (n-1) (by omega) (by omega) (by omega) (by omega)).symm
  have hout := outer_turn ha hb hab (htop 1 (by omega) (by omega)) (htop (n-1) (by omega) (by omega))
  change 2 * (A 0 (n-1) - A 0 1) + 2 * turn (-b) a = 8 ∨
    2 * (A 0 (n-1) - A 0 1) + 2 * turn (-b) a = -8 at hout
  have he : f n - f (n-1) = -b := by simp [hclose, b]
  dsimp only
  rw [he, htotal]
  rcases hout with h | h
  · left; linarith
  · right; linarith

/-- A simple periodic lattice line has zero turn per period. Its secants of
length `L` all have the same direction (the displacement `D`), so the
outer staircase contributes zero. The two translated sides cancel. -/
theorem turn_periodic_sum (f : ℕ → ℤ × ℤ) (L : ℕ) (D : ℤ × ℤ)
    (hstep : ∀ i, FK.squareLattice.Adj (f i) (f (i+1)))
    (hinj : Function.Injective f) (hper : ∀ i, f (i+L) = f i + D) :
    (∑ i ∈ range L, turn (f (i+1)-f i) (f (i+2)-f (i+1))) = 0 := by
  by_cases hL : 1 < L
  swap
  · interval_cases L
    · simp
    · have hs (i : ℕ) : f (i+1) - f i = D := by rw [hper]; abel
      simp [hs, turn, swing]
  let A i j := octant (f j - f i)
  let H i j := swing (A i j) (A (i+1) j)
  let V i j := swing (A i j) (A i (j+1))
  let S i := ∑ j ∈ Ico (i+1) (i+L), V i j
  have hcell (i j : ℕ) (hij : i+1 < j) := square (hstep i) (hstep j)
    (hinj.ne (by omega : i ≠ j)) (hinj.ne (by omega : i ≠ j+1))
    (hinj.ne (by omega : i+1 ≠ j)) (hinj.ne (by omega : i+1 ≠ j+1))
  have hdeck (i : ℕ) : A i (i+L) = octant D := by
    dsimp [A]; simp [hper]
  have hturn (i : ℕ) : turn (f (i+1)-f i) (f (i+2)-f (i+1)) = S i - S (i+1) := by
    have hrow := sweep_row H V i (i+L+1) (by omega) fun j hj _ =>
      (hcell i j hj).1.trans (hcell i j hj).2.symm
    rw [sum_Ico_succ_top (show i+1 ≤ i+L by omega), show i+L+1=(i+1)+L by omega] at hrow
    change V i (i+1) + H i (i+2) + S (i+1) = S i + V i (i+L) + H i ((i+1)+L) at hrow
    have hout := (hcell i (i+L) (by omega)).1
    change V i (i+L) + H i (i+L+1) = swing (A i (i+L)) (A (i+1) (i+L+1)) at hout
    rw [show i+L+1=(i+1)+L by omega, hdeck, hdeck] at hout
    simp [swing] at hout
    have hdiag : V i (i+1) + H i (i+2) = turn (f (i+1)-f i) (f (i+2)-f (i+1)) :=
      corner_sub (unitStep_sub (hstep i)) (unitStep_sub (hstep (i+1))) (hinj.ne (by omega))
    linarith
  have ht (i j : ℕ) : A (i+L) (j+L) = A i j := by simp [A, hper]
  have ht' (i j : ℕ) : V (i+L) (j+L) = V i j := by
    dsimp only [V]
    simp [show j+L+1=j+1+L by omega, ht]
  have hS : S L = S 0 := by
    simp only [S, sum_Ico_eq_sum_range, zero_add,
      show L+L-(L+1)=L-1 by omega]
    apply sum_congr rfl
    intro j _
    rw [show L+1+j = (1+j)+L by omega]
    simpa using ht' 0 (1+j)
  simp_rw [hturn]
  rw [sum_range_sub', hS, sub_self]

-- The octant convention agrees with the compass convention on unit steps.
theorem turn_eq_quarter {a b : ℤ × ℤ} (ha : UnitStep a) (hb : UnitStep b) :
    turn a b = 2 * PottsDiscontinuity.TorusTopology.Planar.Medial.primalCompassQuarterTurn
      (if 0 < a.1 then 0 else if 0 < a.2 then 1 else if a.1 < 0 then 2 else 3)
      (if 0 < b.1 then 0 else if 0 < b.2 then 1 else if b.1 < 0 then 2 else 3) := by
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  all_goals decide

end PottsDiscontinuity.TorusTopology.LatticeSecants
