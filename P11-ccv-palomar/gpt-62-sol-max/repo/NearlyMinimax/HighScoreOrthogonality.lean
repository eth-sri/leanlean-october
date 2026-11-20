module

public import NearlyMinimax.HighLocalScores
public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.Risk
public import NearlyMinimax.ActualSeparatedPacket

@[expose] public section

/-! Locality and disjoint-patch orthogonality of the actual high-regime
density-response score. Density resets need not be independent: conditioning
on the design leaves independent response coordinates, and the outside
response likelihood cancels from each true signed-packet ratio. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section FinitePacket
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

section
variable {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)

theorem high_response_variance_ratio (c : ι → ℝ)
    (y : Fin n → Fin 3) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highResponseVarianceTerm a V η g w φ c y i / highResponseProduct a V η g w φ c y =
      ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i) :=
  product_erase_div_product _ i _ (fun j => (hp j).ne')

end

end FinitePacket

/-- The actual observation indices in a torus patch. -/
def highPatchSampleIndices (d k n : ℕ) (j : HighWindowLabels d k)
    (x : Fin n → Covariate d) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ∈ highTorusPatch d k j)

section
variable (d k n : ℕ)

theorem highPatchSampleIndices_disjoint [NeZero k]
    (x : Fin n → Covariate d) (j l : HighWindowLabels d k)
    (hjl : l ∉ highNeighborLabels d k j) :
    Disjoint (highPatchSampleIndices d k n j x) (highPatchSampleIndices d k n l x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (highTorusPatch_disjoint_of_not_neighbor d k j l hjl)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem highPeriodicTensor_sample_zero_outside_patch
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) (i : Fin n)
    (hi : i ∉ highPatchSampleIndices d k n j x) :
    highPeriodicTensor d k j (x i) = 0 := by
  by_contra h
  have hx := highPeriodicTensor_supported_patch d k j h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)

end

end NearlyMinimax
