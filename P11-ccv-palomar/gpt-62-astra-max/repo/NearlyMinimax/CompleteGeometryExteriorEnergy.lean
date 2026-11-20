module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.AliasTailSummation

@[expose] public section

/-! Actual count-two and exterior factorial blocks of the complete source
geometry. Every constant is fixed before the degrees and count cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable (d : ℕ) (Cs Chi : ℝ)

def completeGeometryExteriorConstant : ℝ :=
  max 1 (Cs * (3*2^d*Chi^2))

theorem completeGeometryExteriorConstant_pos :
    0 < completeGeometryExteriorConstant d Cs Chi :=
  zero_lt_one.trans_le (le_max_left _ _)

end

variable {d : ℕ} (D M R q n : ℕ) (h3 : 3 ≤ n) (hn : D < n) (J : ℕ) (hD : 2 ≤ D)
    (aD bD c0 ell N mu C a rho eta Chi Bl Cs : ℝ)

include h3 hn in
theorem completeSourceGeometryEnvelope_exterior_integral_of_three_le :
    (∫ U, completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl n U
      ∂fullSpatialPatchDesign d n) = (3*2^d*Chi^2)^n*eta^4*(Bl+1)^2 := by
  rcases n with _|_|_|n <;> try omega
  · solve_by_elim [completeSourceGeometryEnvelope_exterior_integral]

include hD in
/-- The true exterior integrals, including response and spatial volume,
give the source factorial tail with its fixed exponential constant. -/
theorem completeSourceGeometryEnvelope_exterior_factorial_le
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Cs*mu) (D+1+j) *
      ∫ U, completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu
        C a rho eta Chi Bl (D+1+j) U ∂fullSpatialPatchDesign d (D+1+j)) ≤
      Real.exp (completeGeometryExteriorConstant d Cs Chi) * eta^4*(Bl+1)^2 *
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*mu) (D+1) := by
  let B := 3*2^d*Chi^2
  let P := eta^4*(Bl+1)^2
  let ch := completeGeometryExteriorConstant d Cs Chi
  have hB : 0 ≤ B := by positivity
  have hP : 0 ≤ P := by positivity
  have hbase : Cs*B ≤ ch := le_max_right _ _
  have heq j :
      (∫ U, completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl _ U ∂fullSpatialPatchDesign d (D+1+j)) =
      B^(D+1+j)*P := by
    linarith [completeSourceGeometryEnvelope_exterior_integral_of_three_le (d := d) D M R q (D+1+j) (by omega) (by omega) aD bD c0 ell N mu C a rho eta Chi Bl]
  simp_rw [heq]
  have hterm j : poissonCountWeight (Cs*mu) (D+1+j) * (B^(D+1+j)*P) =
      P * poissonCountWeight (Cs*B*mu) (D+1+j) := by
    simp [poissonCountWeight] <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Cs*B*mu) (D+1) J
  apply (mul_le_mul_of_nonneg_left ht hP).trans
  have h := mul_le_mul (by
    apply Real.exp_le_exp.mpr
    exact (mul_le_of_le_one_right (mul_nonneg hCs hB) hmu1).trans hbase) (poissonCountWeight_mono (by positivity) (mul_le_mul_of_nonneg_right hbase hmu) (D+1)) (poissonCountWeight_nonneg (by positivity) _)
    (Real.exp_pos ch).le
  exact (mul_le_mul_of_nonneg_left h hP).trans_eq (by ring)

def completeGeometryRadialConstant (d : ℕ) (B a rho Cs : ℝ) : ℝ :=
  27*Cs^2*B^4*((2*rho+a)/a^2)^4*2^d*spatialExponentialConstant d

/-- The actual pair envelope integrates the genuine radial defect. Its
count-two Poisson factor yields `η⁴ μ² N⁻ᵈ` with a fixed density-upper cap. -/
theorem completeSourceGeometryEnvelope_pair_factorial_le (B : ℝ)
    (hd : 0 < d) (hN : 0 < N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ mu)
    (hbd : 0 ≤ bD-(M : ℝ)⁻¹) (hbdB : bD-(M : ℝ)⁻¹ ≤ B) :
    poissonCountWeight (Cs*mu) 2 *
      (∫ U, completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu
        C a rho eta Chi Bl 2 U ∂fullSpatialPatchDesign d 2) ≤
      completeGeometryRadialConstant d B a rho Cs * eta^4*mu^2*N^(-(d : ℝ)) := by
  have hi := ((finePairCountTwoGeometryEnvelope_integrable_and_le hd _ _ _ _ hN).2 : ∫ (U : DesignSample d 2), completeSourceGeometryEnvelope D M R q aD bD c0 ell N mu C a rho eta Chi Bl 2 U ∂fullSpatialPatchDesign d 2 ≤ 9 * finePairCountTwoSpatialBudget d (bD - (↑M)⁻¹) a rho eta N)
  apply (mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2)).trans
  have hp  := pow_le_pow_left₀ hbd hbdB 4
  let K := 27*Cs^2*((2*rho+a)/a^2)^4*2^d*spatialExponentialConstant d *
    eta^4*mu^2/(N^d)
  have hK : 0 ≤ K := by
    have := spatialExponentialConstant_nonneg d
    positivity
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  convert (mul_le_mul_of_nonneg_right hp hK) using 1 <;> simp [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
    <;> dsimp [K] <;> norm_num only [Nat.factorial] <;> ring

end NearlyMinimax
