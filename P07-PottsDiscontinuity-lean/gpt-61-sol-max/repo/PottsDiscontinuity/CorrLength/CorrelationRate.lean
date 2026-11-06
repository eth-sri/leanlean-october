module
public import Mathlib

public import PottsDiscontinuity.CorrLength.Positivity
public import PottsDiscontinuity.CorrLength.SubadditiveRate
public import PottsDiscontinuity.CorrLength.RotatedLattice

/-!
# Existence of the correlation-length rate

The finite-distance connection probabilities are positive and
supermultiplicative. Fekete's lemma applied to their negative logarithms gives
the diagonal rate; the frozen sites `diagonalSite n` repeat each diagonal point
at the two consecutive indices `2*m` and `2*m+1`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.CorrLength

open PottsDiscontinuity.FK

noncomputable section

/-- The free-limit connection probability at the diagonal point `(n,n)`. -/
def diagonalConnectionProbability (μ : Measure LatticeConfiguration) (n : ℕ)  :=
  μ.real (connectionEvent (0, 0) ((n : ℤ), (n : ℤ)))

section

variable (θ : Parameters) (μ : Measure LatticeConfiguration)
include θ μ

section

variable (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ) (n : ℕ)
include hμ

private theorem diagonalConnectionProbability_pos 
     :
    0 < diagonalConnectionProbability μ n := by
                                               solve_by_elim [_root_.PottsDiscontinuity.CorrLength.isRCInfiniteVolumeLimit_connection_positive]

private theorem diagonalConnectionProbability_le_one 
     :
    diagonalConnectionProbability μ n ≤ 1 := by
  
  have hle := ProbabilityMeasure.apply_le_one  ⟨μ, hμ.1⟩ 
    (connectionEvent (0, 0) ( n ,  n ))
  aesop

end

section

variable (hμ : PottsDiscontinuity.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 0 μ)
include hμ

private theorem diagonalConnectionProbability_supermultiplicative
    
     (m n : ℕ) :
    diagonalConnectionProbability μ m * diagonalConnectionProbability μ n ≤
      diagonalConnectionProbability μ (m + n) := by
  have h := isRCInfiniteVolumeLimit_origin_connection_supermultiplicative θ μ hμ
    ( m ,  m ) ( n ,  n )
  aesop

/-- There is a finite nonnegative limit for the negative logarithmic rate along
the points `(n,n)`. -/
theorem diagonal_correlation_rate_exists 
     :
    ∃ aInf : ℝ, 0 ≤ aInf ∧ aInf ≤ -Real.log (diagonalConnectionProbability μ 1) ∧
      Tendsto (fun n : ℕ =>
        -Real.log (diagonalConnectionProbability μ n) / (n : ℝ)) atTop (𝓝 aInf) := log_rate_of_supermultiplicative (diagonalConnectionProbability μ) (diagonalConnectionProbability_pos θ μ hμ)
                                                                                     (diagonalConnectionProbability_le_one θ μ hμ) (diagonalConnectionProbability_supermultiplicative θ μ hμ)

/-- Reindexing the free-limit connection probabilities by the frozen sites
`xₙ = diagonalSite n` halves the diagonal rate. -/
theorem diagonalSite_correlation_rate_exists 
     :
    ∃ aInf : ℝ, 0 ≤ aInf ∧
      Tendsto (fun n : ℕ =>
        -Real.log (μ.real (connectionEvent (0, 0)
          (PottsDiscontinuity.diagonalSite n))) / (n : ℝ))
        atTop (𝓝 (aInf / 2)) := by
  obtain ⟨aInf, haInf, _, hrate⟩ := diagonal_correlation_rate_exists θ μ hμ
  
  
  
  
  
  have hdiag := tendsto_rate_of_even_odd_subsequence (fun m => -Real.log (diagonalConnectionProbability μ m)) (fun n =>
                                                                                                                 -Real.log (μ.real (connectionEvent (0, 0)
                                                                                                                   (PottsDiscontinuity.diagonalSite n)))) aInf  hrate   fun m => by
                                                                        aesop   fun m => by
                                                                              aesop 
  refine ⟨aInf, haInf, ?_⟩
  simpa  using hdiag

end

end

end

end PottsDiscontinuity.CorrLength
