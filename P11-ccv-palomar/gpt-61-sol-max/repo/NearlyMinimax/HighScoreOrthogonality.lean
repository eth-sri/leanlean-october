module

public import NearlyMinimax.HighLocalScores
public import NearlyMinimax.ScoreSupport
public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.NeighborScoreEnergy
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
variable {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)

theorem high_response_ratio_depends_on_support  c v
    (S : Finset (Fin n)) (hw : ∀ i, i ∉ S → w i = 0)
    y y' (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    highResponseProduct a V η g w φ v y / highResponseProduct a V η g w φ c y =
      highResponseProduct a V η g w φ v y' / highResponseProduct a V η g w φ c y' := by
  let outside (z : Fin n → Fin 3)  :=
    ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, ternaryMass a (g i) V (z i)
  let inside (z : Fin n → Fin 3) (u : ι → ℝ)  :=
    ∏ i ∈ S, ternaryMass a (coefficientRegression η g w φ u i) V (z i)
  have hfactor (z : Fin n → Fin 3) (u : ι → ℝ) :
      highResponseProduct a V η g w φ u z = outside z * inside z u := by
    unfold highResponseProduct
    rw [← Finset.prod_sdiff (Finset.subset_univ S)]
    dsimp [outside, inside]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2]
  have hout (z : Fin n → Fin 3) : outside z ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    simpa [coefficientRegression, hw i (Finset.mem_sdiff.mp hi).2] using hp i (z i)
  have hin (z : Fin n → Fin 3) : inside z c ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => hp i (z i)))
  have hs (u : ι → ℝ) : inside y u = inside y' u := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hyy i hi]
  rw [hfactor y v, hfactor y c, hfactor y' v, hfactor y' c, hs v, hs c]
  field_simp [hout y, hout y', hin y']

theorem high_response_variance_ratio  c
    y i
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highResponseVarianceTerm a V η g w φ c y i / highResponseProduct a V η g w φ c y =
      ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i) := by
  unfold highResponseVarianceTerm highResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (coefficientRegression η g w φ c k) V (y k)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun k _ => hp k))
  exact mul_div_mul_right _ _ hrest
end


end FinitePacket

/-- Product-law orthogonality from local response dependence and actual
conditional centering. This helper is used below only with properties proved
from the explicit signed density-response packet. -/
theorem local_response_scores_orthogonal {n }
    μ [∀ i, IsProbabilityMeasure (μ i)]
    (r s : (Fin n → Fin 3) → ℝ) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hr : ∀ y y', (∀ i ∈ S, y i = y' i) → r y = r y')
    (hs : ∀ y y', (∀ i ∈ T, y i = y' i) → s y = s y')
    (hc : (∫ y, r y ∂Measure.pi μ) = 0) :
    (∫ y, r y * s y ∂Measure.pi μ) = 0 := by
  let R (y : S → Fin 3) := r (extendPatchResponses n S y)
  let Q (y : T → Fin 3) := s (extendPatchResponses n T y)
  have hR (y : Fin n → Fin 3) : r y = R (fun i : S => y i) := by
    apply hr
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ (y : Fin n → Fin 3) : s y = Q (fun i : T => y i) := by
    apply hs
    intro i hi
    simp [extendPatchResponses, hi]
  have hcenter : (∫ y, R (fun i : S => y i) ∂Measure.pi μ) = 0 := by
    simpa only [← hR] using hc
  simp_rw [hR, hQ]
  exact finite_product_local_scores_orthogonal n μ S T hST R Q hcenter

section IntegratedPacket
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]

end IntegratedPacket

section Family
variable {J ι E Z : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
  [Fintype E] [MeasurableSpace Z]

end Family

section
variable (d k n : ℕ)

/-- The actual observation indices in a torus patch. -/
def highPatchSampleIndices  j
    (x : Fin n → Covariate d)  :=
  Finset.univ.filter (fun i => x i ∈ highTorusPatch d k j)

theorem highPatchSampleIndices_disjoint  [NeZero k]
    x j l
    (hjl : l ∉ highNeighborLabels d k j) :
    Disjoint (highPatchSampleIndices d k n j x) (highPatchSampleIndices d k n l x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (highTorusPatch_disjoint_of_not_neighbor d k j l hjl)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem highPeriodicTensor_sample_zero_outside_patch 
    j x i
    (hi : i ∉ highPatchSampleIndices d k n j x) :
    highPeriodicTensor d k j (x i) = 0 := by
  by_contra h
  have hx := highPeriodicTensor_supported_patch d k j h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩)
end


end NearlyMinimax
