module

public import NearlyMinimax.SpatialGeometryFactorialEnergy
public import NearlyMinimax.OrdinaryFineAliasSaddleEnvelope


@[expose] public section

/-! Actual higher-count envelope integration and factorial assembly. The
only intermediate ordinary-family input is its genuine finite spatial
integral sum; the canonical module derives it from the constructed bands. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

private theorem integral_gated {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (P : Prop) [Decidable P] (f : X → ℝ) :
    (∫ x, if P then f x else 0 ∂μ) = if P then ∫ x, f x ∂μ else 0 := by
  split_ifs <;> simp

theorem SourceGeometry.higherEnvelope_factorial_le {d : ℕ} [NeZero d]
    (S : SourceGeometry d) (hd : 5 ≤ d) (hD : 3 ≤ S.D) (K Cs Eord : ℝ) (haD : 0 < S.aD) (ha : 0 < S.a)
    (hshrink : S.ad < S.bd)
    (htau : S.tau ≤ S.c0)
    (hc0 : 0 ≤ S.c0) (hK : 0 ≤ K) (hCs : 0 ≤ Cs)
    (hell : 1 ≤ S.ell) (hellN : S.ell ≤ S.N) (hcut : S.ell=S.N*Real.exp (-S.c0*S.D))
    (hDM : (S.D : ℝ) ≤ K*S.M) (hmu : 0 < S.mu) (hmu1 : S.mu ≤ 1)
    (hmuH : S.mu*(1+Real.log S.N) ≤ 1) (hTaylor : S.eta^(4*S.q)*S.N^d ≤ 1)
    (hfield : Real.exp (2*S.tau*S.M) * (S.ell^(2-(d : ℝ)))^2 * S.mu^4 ≤
        S.mu^2*S.N^(-(d : ℝ)))
    (hord : (∑ j ∈ Finset.range (S.D-S.M), poissonCountWeight (Cs*S.mu) (S.M+1+j) *
      ∫ U, S.ordinary U ∂fullSpatialPatchDesign d (S.M+1+j)) ≤ Eord) :
    (∑ j ∈ Finset.range (S.D-2), poissonCountWeight (Cs*S.mu) (3+j) *
      ∫ U, S.higherEnvelope U ∂fullSpatialPatchDesign d (3+j)) ≤
      4*(cardinalGeometryFactorialConstant d S.q S.bD S.C S.a S.rho Cs*S.eta^4*S.N^(-(d : ℝ))*S.mu^2 + Eord +
        finePairSaddleAliasFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K (3*Cs) *
          (S.eta^4*S.N^(4-(d : ℝ))) *
          poissonCountWeight (finePairSaddleAliasFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 K (3*Cs)*S.mu) (S.M+1) +
        finePairFieldFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 (3*Cs)*S.eta^4*S.mu^2*S.N^(-(d : ℝ))) := by
  have hN := hell.trans hellN
  have hNpos := lt_of_lt_of_le zero_lt_one hN
  have had : S.aD ≤ S.ad := le_add_of_nonneg_right
    (inv_nonneg.mpr (Nat.cast_nonneg S.M))
  have hbd : S.bd ≤ S.bD := by simp
  have hbd0 := (haD.trans_le had).le.trans hshrink.le
  have hA := finite_cardinal_geometry_budget_le (D := S.D) (F := S.D) hd hbd0 hbd S.q S.C S.a S.rho S.eta Cs ha hCs hN hmu hmu1 hmuH hTaylor
  have hP := finite_fine_pair_alias_geometry_budget_le (D := S.D) hd haD had hbd hshrink htau hc0 hK S.M S.q
    S.C S.a S.rho S.eta S.ell S.N Cs S.mu hNpos hcut hell hellN hDM hCs hmu.le hmu1
  have hF := finite_fine_field_geometry_budget_le (D := S.D) hd hD haD had hbd hshrink htau S.M S.q S.C S.a S.rho S.eta
    S.ell S.N Cs S.mu (lt_of_lt_of_le zero_lt_one hell) hCs hmu.le hmu1
  have hFconst : 0 ≤ finePairFieldFactorialConstant d S.q S.aD S.bD S.C S.a S.rho S.c0 (3*Cs) := by
    unfold finePairFieldFactorialConstant fieldTailConstant countTailConstant
    have hPre := finePairUniformSpatialPrefactor_nonneg d S.q S.aD S.bD S.C S.a S.rho S.c0
    have hP4 := poissonCountWeight_nonneg (by positivity [finePairFieldGeometricBase_nonneg d S.bD] :
      0 ≤ (3*Cs)*(finePairFieldGeometricBase d S.bD*2^12)) 4
    positivity
  have hFs := mul_le_mul_of_nonneg_left hfield
    (mul_nonneg hFconst (by positivity : 0 ≤ S.eta^4))
  let f := fun r => poissonCountWeight (Cs*S.mu) r *
    ∫ U, S.ordinary U ∂fullSpatialPatchDesign d r
  have hf (r : ℕ) : 0 ≤ f r := mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) r)
    (integral_nonneg (fun U => ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U))
  have hO := (finite_refined_gated_sum_le_tail S.D S.M f f hf (fun _ _ _ => le_rfl)).trans hord
  have hInt (j : ℕ) := (S.higherEnvelope_integrable_and_eq (r := 3+j) hd (by omega) hell hellN).2
  simp only [hInt, Fin.sum_univ_four, components, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, integral_gated]
  have halg (w A B P F : ℝ) : w*(4*(A+B+P+F))=4*(w*A+w*B+w*P+w*F) := by ring
  simp only [halg, mul_ite, mul_zero]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hO)
    (by simpa only [mul_ite, mul_zero] using hP)) (hF.trans ?_)) (by norm_num)
  convert hFs using 1 <;> ring

end NearlyMinimax
