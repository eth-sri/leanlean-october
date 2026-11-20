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

def completeGeometryExteriorConstant (d : ℕ) (Cs Chi : ℝ) : ℝ :=
  max 1 (Cs * (3*(2 : ℝ)^d*Chi^2))

section
variable (d : ℕ) (Cs Chi : ℝ)

theorem completeGeometryExteriorConstant_ge_one :
    1 ≤ completeGeometryExteriorConstant d Cs Chi := le_max_left _ _

theorem completeGeometryExteriorConstant_pos :
    0 < completeGeometryExteriorConstant d Cs Chi :=
  zero_lt_one.trans_le (completeGeometryExteriorConstant_ge_one d Cs Chi)

end

section
variable {d : ℕ}

/-- The true exterior integrals, including response and spatial volume,
give the source factorial tail with its fixed exponential constant. -/
theorem SourceGeometry.envelope_exterior_factorial_le
    (S : SourceGeometry d) (J : ℕ) (hD : 2 ≤ S.D) (Chi Bl Cs : ℝ)
    (hCs : 0 ≤ Cs) (hmu : 0 ≤ S.mu) (hmu1 : S.mu ≤ 1) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Cs*S.mu) (S.D+1+j) *
      ∫ U, S.envelope Chi Bl (S.D+1+j) U ∂fullSpatialPatchDesign d (S.D+1+j)) ≤
      Real.exp (completeGeometryExteriorConstant d Cs Chi) * S.eta^4*(Bl+1)^2 *
        poissonCountWeight (completeGeometryExteriorConstant d Cs Chi*S.mu) (S.D+1) := by
  let B := 3*(2 : ℝ)^d*Chi^2
  let P := S.eta^4*(Bl+1)^2
  let ch := completeGeometryExteriorConstant d Cs Chi
  have hB : 0 ≤ B := by positivity
  have hP : 0 ≤ P := by positivity
  have hbase : Cs*B ≤ ch := le_max_right _ _
  have heq (j : ℕ) :
      (∫ U, S.envelope Chi Bl (S.D+1+j) U ∂fullSpatialPatchDesign d (S.D+1+j)) =
      B^(S.D+1+j)*P := by
    simpa only [B, P, mul_assoc] using S.envelope_exterior_integral Chi Bl (S.D+1+j) (by omega) (by omega)
  simp_rw [heq]
  have hterm (j : ℕ) : poissonCountWeight (Cs*S.mu) (S.D+1+j) * (B^(S.D+1+j)*P) =
      P * poissonCountWeight (Cs*B*S.mu) (S.D+1+j) := by
    rw [← mul_assoc, poissonCountWeight_mul_pow, mul_comm, mul_left_comm B, ← mul_assoc Cs B]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Cs*B*S.mu) (S.D+1) J
  apply (mul_le_mul_of_nonneg_left ht hP).trans
  have hexp : Real.exp (Cs*B*S.mu) ≤ Real.exp ch := by
    simpa using (mul_le_of_le_one_right (mul_nonneg hCs hB) hmu1).trans hbase
  have hweight := poissonCountWeight_mono (by positivity : 0 ≤ Cs*B*S.mu)
    (mul_le_mul_of_nonneg_right hbase hmu) (S.D+1)
  have h := mul_le_mul hexp hweight (poissonCountWeight_nonneg (by positivity) _)
    (Real.exp_pos ch).le
  exact (mul_le_mul_of_nonneg_left h hP).trans_eq (by ring)

end

def completeGeometryRadialConstant (d : ℕ) (B a rho Cs : ℝ) : ℝ :=
  27*Cs^2*B^4*((2*rho+a)/a^2)^4*(2 : ℝ)^d*spatialExponentialConstant d

/-- The actual pair envelope integrates the genuine radial defect. Its
count-two Poisson factor yields `η⁴ μ² N⁻ᵈ` with a fixed density-upper cap. -/
theorem SourceGeometry.envelope_pair_factorial_le {d : ℕ}
    (S : SourceGeometry d) (Chi Bl Cs B : ℝ)
    (hd : 0 < d) (hN : 0 < S.N) (hCs : 0 ≤ Cs) (hmu : 0 ≤ S.mu)
    (hbd : 0 ≤ S.bd) (hbdB : S.bd ≤ B) :
    poissonCountWeight (Cs*S.mu) 2 *
      (∫ U, S.envelope Chi Bl 2 U ∂fullSpatialPatchDesign d 2) ≤
      completeGeometryRadialConstant d B S.a S.rho Cs * S.eta^4*S.mu^2*S.N^(-(d : ℝ)) := by
  have hi := S.envelope_pair_integral_le Chi Bl hd hN
  apply (mul_le_mul_of_nonneg_left hi (poissonCountWeight_nonneg (mul_nonneg hCs hmu) 2)).trans
  have hp := pow_le_pow_left₀ hbd hbdB 4
  let K := 27*Cs^2*((2*S.rho+S.a)/S.a^2)^4*(2 : ℝ)^d*spatialExponentialConstant d *
    S.eta^4*S.mu^2/(S.N^d)
  have hK : 0 ≤ K := by
    have := spatialExponentialConstant_nonneg d
    dsimp [K]
    positivity
  have h := mul_le_mul_of_nonneg_right hp hK
  rw [Real.rpow_neg hN.le, Real.rpow_natCast]
  convert h using 1 <;> simp only [poissonCountWeight, finePairCountTwoSpatialBudget, completeGeometryRadialConstant]
    <;> dsimp [K] <;> norm_num only [Nat.factorial, Nat.cast_ofNat] <;> ring

end NearlyMinimax
