module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.BarrierCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Regularize
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionGeometry
import Mathlib

/-! # Choosing one cylinder for all the tests -/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ClassicalProfile
open Set Real

variable {d : ℕ} {α : ℝ} (m : ClassicalProfile d α)

def test (S k r : ℝ) := cappedQuad (1/S^2) (k/S^2) (m.regular r)

private theorem boundary_bounds {S : ℝ} (hS : 0 < S) {P : KineticPoint d}
    (hP : P ∈ initialFullLateralBoundary ⟨0,0,0⟩ S) : P.time ≤ 0 ∧ PDE.vecNormSq P.velocity ≤ S^2 := by
  apply closure_minimal (s := backwardCylinder ⟨0,0,0⟩ S)
    (t := {P : KineticPoint d | P.time ≤ 0} ∩ {P | PDE.vecNormSq P.velocity ≤ S^2}) _
    ((isClosed_le continuous_time continuous_const).inter (isClosed_le (PDE.continuous_vecNormSq.comp continuous_velocity) continuous_const)) hP.1
  intro P hP
  obtain ⟨_,ht,hv,_⟩ := (construction_mem_cylinder_iff 0 S hS P).mp hP
  exact ⟨ht.le,(PDE.vecEuclideanNorm_sq _).symm.le.trans (pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hv.le 2)⟩

/-- On the bottom face the time term cancels the height even in the core. The other
faces are far from the core, where homogeneity gives a large subtractive term. -/
theorem exists_cylinder (k : ℝ) (hk : 0 ≤ k) (ha : 0 < α) : ∃ S : ℝ, 0 < S ∧ ∀ r,
    0 < r → r ≤ 1 → ∀ P ∈ initialFullLateralBoundary ⟨0,0,0⟩ S, m.test S k r P = 0 := by
  obtain ⟨R,hR,hlarge⟩ := m.regular_large ha (k+1)
  let S := max (R+1) (√(4*k*R^2))
  have hRS : R < S := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hS : 0 < S := by linarith
  have hsq : 4*k*R^2 ≤ S^2 := by
    rw [← sq_sqrt (show 0 ≤ 4*k*R^2 by positivity)]; exact pow_le_pow_left₀ (sqrt_nonneg _) (le_max_right _ _) _
  refine ⟨S,hS,fun r hr hr1 P hP => timeCutoffTheta_eq_zero _ ?_⟩
  let q := (P.position,P.velocity)
  have ht := boundary_bounds hS hP
  change 3/4 + 1/S^2 * P.time + k/S^2 * PDE.vecNormSq P.velocity - m.regular r q ≤ 0
  have hz : 0 < S^2 := sq_pos_of_pos hS
  have hmul := div_nonneg hk hz.le
  by_cases hq : R ≤ rho q
  · have hb := mul_le_mul_of_nonneg_left ht.2 hmul
    rw [div_mul_cancel₀ _ hz.ne'] at hb
    linarith [mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hz).le ht.1, hlarge r hr hr1 q hq]
  obtain ⟨hx,hv⟩ := rho_coordinate_bounds q
  have hvR : PDE.vecEuclideanNorm P.velocity < R := hv.trans_lt (lt_of_not_ge hq)
  have hxS : PDE.vecEuclideanNorm P.position < S^3 := hx.trans_lt (pow_lt_pow_left₀ ((lt_of_not_ge hq).trans hRS) (rho_nonneg _) (by decide))
  have hvS2 : PDE.vecNormSq P.velocity < S^2 := by rw [← PDE.vecEuclideanNorm_sq]; exact pow_lt_pow_left₀ (hvR.trans hRS) (PDE.vecEuclideanNorm_nonneg _) (by decide)
  have hxS2 : PDE.vecNormSq P.position < (S^3)^2 := by rw [← PDE.vecEuclideanNorm_sq]; exact pow_lt_pow_left₀ hxS (PDE.vecEuclideanNorm_nonneg _) (by decide)
  have he : P.time = -(S^2) ∨ PDE.vecNormSq P.velocity = S^2 ∨ PDE.vecNormSq P.position = (S^3)^2 := by
    simpa only [relativePosition, sub_zero, smul_zero, zero_sub, mem_union, mem_ofPred_eq, or_assoc,
      PDE.euclideanSphere, PDE.euclideanSqDist] using hP.2
  rcases he with hb | e | e
  · have hv2 : PDE.vecNormSq P.velocity ≤ R^2 := by rw [← PDE.vecEuclideanNorm_sq]; exact pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hvR.le _
    have hsmall : k/S^2 * PDE.vecNormSq P.velocity ≤ 1/4 := by
      rw [div_mul_eq_mul_div,div_le_iff₀ hz]; nlinarith [mul_le_mul_of_nonneg_left hv2 hk]
    rw [hb,mul_neg,div_mul_cancel₀ _ hz.ne']; linarith [m.regular_nonneg hr q]
  · exact (hvS2.ne e).elim
  · exact (hxS2.ne e).elim

theorem test_height {S : ℝ} (hS : 0 < S) (k r : ℝ) : ∃ P ∈ backwardCylinder ⟨0,0,0⟩ S, 1/4 ≤ m.test S k r P := by
  refine ⟨⟨-S^2/4,0,0⟩,(construction_mem_cylinder_iff _ _ hS _).mpr ?_,?_⟩
  · simpa [PDE.vecEuclideanNorm,PDE.vecNormSq,PDE.vecDot] using
      And.intro (show -(S^2) < -S^2/4 by linarith [sq_pos_of_pos hS])
        ⟨by linarith [sq_pos_of_pos hS],hS,pow_pos hS 3⟩
  · have e : (1:ℝ)/S^2 * (-S^2/4) = -1/4 := by field_simp
    change 1/4 ≤ timeCutoffTheta (3/4 + 1/S^2 * (-S^2/4) + k/S^2 * PDE.vecNormSq 0 - m.regular r 0)
    simp only [e,regular_zero,sub_zero]; simp [PDE.vecNormSq,PDE.vecDot]; linarith [timeCutoffTheta_lower (3/4 + -1/4)]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ClassicalProfile
