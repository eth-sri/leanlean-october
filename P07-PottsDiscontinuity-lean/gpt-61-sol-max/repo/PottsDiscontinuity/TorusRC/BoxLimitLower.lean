module
public import Mathlib

public import PottsDiscontinuity.TorusRC.SquareBoxComparison
public import PottsDiscontinuity.TorusRC.FiniteEventMeasure

/-! # Cofinal native squares recover the exact rotated free connection probability -/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.TorusRC

open CorrLength FK

theorem rotatedDiagonalProbability_pos (θ : Parameters) (n : ℕ) :
    0 < ((rotatedDiagonalConnectionProbability θ n : NNReal):ℝ) := by
  rw [rotatedDiagonalConnectionProbability_eq]
  
  exact freeBoxLimit_connection_positive θ _ _

/-- Every strict lower bound on the infinite-volume connection probability
`rotatedDiagonalConnectionProbability` (`CorrLength/RotatedFreeLimit.lean`)
holds eventually for the native square free-box probabilities. Only cofinal
domain inclusion and the proved free-box exhaustion theorem
`FK.freeBoxLimit_existsUnique` are used. -/
theorem liftedBoxFreeDiagonalProbability_eventually_gt (θ : Parameters) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t)
    (htp : t < ((rotatedDiagonalConnectionProbability θ n : NNReal):ℝ)) :
    ∀ᶠ R in atTop, t < liftedBoxFreeConnectionProbability θ rotatedLatticeOrigin R
      rotatedLatticeOrigin (rotatedDiagonalSite n) := by
  
  
  
  
  obtain ⟨r,hr,hrn⟩ := ((open_probability_eventually_gt _ (Classical.choose (freeBoxLimit_existsUnique θ)) ((Classical.choose_spec (freeBoxLimit_existsUnique θ)).1 (fun _ => (0,0)) (fun r => r)
                                                                                origin_latticeBox_nested origin_latticeBox_exhaustive)
                           (connectionEvent (0,0) (n,n)) (connectionEvent_isOpen _ _) t ht (by
                                                                                              rw [rotatedDiagonalConnectionProbability_eq] at htp
                                                                                              simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using htp)).and (eventually_ge_atTop n)).exists
  
  
  let u : BoxVertex (0,0) r := ⟨(0,0), center_mem_latticeBox _ _ ⟩
  let v : BoxVertex (0,0) r := ⟨(n,n), by
                                         rw [mem_latticeBox]
                                         simp_all ⟩
  
  
  
  filter_upwards [eventually_ge_atTop (2*r)] with R hR
  have hcomp := squareBox_connection_probability_le_native θ r R hR u v
  rw [(by
         
         ext <;> dsimp [squareToRotatedVertex, rotatedDiagonalSite] <;> ring : squareToRotatedVertex v.val = rotatedDiagonalSite n), ←  boxProbabilityMeasure_connection_eq θ (0,0) r u v ] at hcomp
  exact hr.trans_le hcomp

end PottsDiscontinuity.TorusRC
