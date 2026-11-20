module

public import PottsDiscontinuity.FK.BoxLaw
public import PottsDiscontinuity.Frozen.Defs.RCInfiniteOpenGraph

/-!
# Exponential two-point decay excludes an infinite origin cluster

The hypothesis below uses the integer lattice's ℓ¹ distance, explicitly
`|x₁| + |x₂|`. This module works for any measure with the stated bound; it
requires neither a Gibbs property nor planar duality. It does not prove wired
percolation or the discontinuity implication.
-/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

/-- The actual open cluster, with no boundary identifications. -/
def cluster (ω : FK.LatticeConfiguration) (v : ℤ × ℤ) : Set (ℤ × ℤ) :=
  {x | (rcInfiniteOpenGraph ω).Reachable v x}

/-- The two-point event for actual open connectivity. -/
def connectionEvent (v x : ℤ × ℤ) : Set FK.LatticeConfiguration :=
  {ω | x ∈ cluster ω v}

/-- The event that the actual open cluster of `v` has infinitely many vertices. -/
def infiniteClusterAt (v : ℤ × ℤ) : Set FK.LatticeConfiguration :=
  {ω | (cluster ω v).Infinite}

/-- Existence of an infinite actual open cluster. -/
def existsInfiniteCluster : Set FK.LatticeConfiguration :=
  {ω | ∃ v : ℤ × ℤ, (cluster ω v).Infinite}

lemma summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by
  apply summable_int_iff_summable_nat_and_neg.2
  have h := Real.summable_exp_nat_mul_iff.2 (neg_neg_of_pos hc)
  constructor
  · grind only [Int.cast_natCast, abs_of_nonneg]
  · simpa [mul_comm] using h

lemma summable_exp_neg_l1 {c : ℝ} (hc : 0 < c) :
    Summable (fun x : ℤ × ℤ => Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := by
  have h := summable_exp_neg_abs_int hc
  have hh := h.mul_of_nonneg h (fun _ => (Real.exp_pos _).le)
    (fun _ => (Real.exp_pos _).le)
  simpa [mul_add, Real.exp_add] using hh

/-- An ℓ¹ exponential bound makes the infinite origin-cluster event null:
the bridge is Borel–Cantelli applied to the summable two-point probabilities. -/
theorem infiniteClusterAt_zero_of_exponential_decay
    (μ : Measure FK.LatticeConfiguration) [IsFiniteMeasure μ] (C c : ℝ) (hc : 0 < c)
    (hdecay : ∀ x : ℤ × ℤ, μ.real (connectionEvent 0 x) ≤
      C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) :
    μ (infiniteClusterAt 0) = 0 := by
  apply ae_finite_setOfPred_mem (s := connectionEvent 0)
  refine ne_top_of_le_ne_top ((summable_exp_neg_l1 hc).mul_left C).tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum fun x => ?_)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (hdecay x)

end PottsDiscontinuity.Duality
