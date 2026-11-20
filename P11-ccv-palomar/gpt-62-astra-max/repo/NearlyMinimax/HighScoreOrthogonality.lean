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

variable {n : ℕ}

theorem high_response_ratio_depends_on_support {a V η : ℝ}
    {g w : Fin n → ℝ} {φ : Fin n → ι → ℝ} (c v : ι → ℝ)
    {S : Finset (Fin n)} (hw : ∀ i, i ∉ S → w i = 0)
    {y y' : TernaryVector n} (hyy : ∀ i ∈ S, y i = y' i)
    (hp : ∀ i b, 0 < ternaryMass a (coefficientRegression η g w φ c i) V b) :
    let product := highResponseProduct a V η g w φ
    product v y / product c y =
      product v y' / product c y' := by
  exact product_ratio_depends_on _ _ (fun i hi => by simp [coefficientRegression, hw i hi])
    (fun i b => (hp i b).ne') hyy

theorem high_response_variance_ratio (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : TernaryVector n) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highResponseVarianceTerm a V η g w φ c y i / highResponseProduct a V η g w φ c y =
      ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i) := by
  unfold highResponseVarianceTerm highResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : (∏ k ∈ Finset.univ.erase i,
      ternaryMass a (coefficientRegression η g w φ c k) V (y k)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun k _ => hp k))
  exact mul_div_mul_right _ _ hrest

end FinitePacket

/-- Product-law orthogonality from local response dependence and actual
conditional centering. This helper is used below only with properties proved
from the explicit signed density-response packet. -/
theorem local_response_scores_orthogonal {n : ℕ}
    (μ : Fin n → Measure (Fin 3)) [∀ i, IsProbabilityMeasure (μ i)]
    (r s : (TernaryVector n) → ℝ) {S T : Finset (Fin n)} (hST : Disjoint S T)
    (hr : ∀ y y', (∀ i ∈ S, y i = y' i) → r y = r y')
    (hs : ∀ y y', (∀ i ∈ T, y i = y' i) → s y = s y')
    (hc : (∫ y, r y ∂Measure.pi μ) = 0) :
    (∫ y, r y * s y ∂Measure.pi μ) = 0 := by
  let R (y : S → Fin 3) := r (extendPatchResponses S y)
  let Q (y : T → Fin 3) := s (extendPatchResponses T y)
  have hR (y : TernaryVector n) : r y = R (fun i : S => y i) := by
    apply hr
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ (y : TernaryVector n) : s y = Q (fun i : T => y i) := by
    apply hs
    intro i hi
    simp [extendPatchResponses, hi]
  have hcenter : (∫ y, R (fun i : S => y i) ∂Measure.pi μ) = 0 := by
    simpa only [← hR] using hc
  simp_rw [hR, hQ]
  solve_by_elim [finite_product_local_scores_orthogonal]

section IntegratedPacket
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]

end IntegratedPacket

section Family
variable {J ι E Z : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
  [Fintype E] [MeasurableSpace Z]

end Family

variable {d k n : ℕ}

end NearlyMinimax
