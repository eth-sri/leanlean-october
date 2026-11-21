module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.RankOne.RightDerivedAction

@[expose] public section

namespace DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction

namespace MatrixPaths
export KPCplxLoweringCoordinateBoost.Geometry (rawRowNormSq rawNormalizedSphereCoordinate
  rawNoncompactPath rawAxis rawCoefficient actual_noncompact_normalized_compact_lift
  actual_noncompact_matrix_path_tangent normalized_induction_weight_tangent)
end MatrixPaths

namespace PolynomialDerivatives
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
open DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.InfinitesimalAction
open KPCplxLoweringCoordinateBoost.Geometry (rawRowNormSq rawNoncompactPath rawNormalizedSphereCoordinate)
open scoped BigOperators Matrix Matrix.Norms.Elementwise

export KPCplxLoweringCoordinateBoost.Geometry (polynomial_profile_curve_derivative
  weighted_polynomial_profile_curve_derivative noncompactVectorPolynomial noncompactWeightPolynomial
  noncompact_hopf_derivative_of_matrix_tangent)

noncomputable abbrev noncompactNormalizedSU2 := KPCplxLoweringCoordinateBoost.Geometry.liftSU2
abbrev noncompactAxis := KPCplxLoweringCoordinateBoost.Geometry.rawAxis
noncomputable abbrev noncompactCoefficient := KPCplxLoweringCoordinateBoost.Geometry.rawCoefficient

alias normalizedNoncompactRowNormSq_pos := KPCplxLoweringCoordinateBoost.Geometry.rawRowNormSq_pos
alias normalizedNoncompactRowNormSq_compact := KPCplxLoweringCoordinateBoost.Geometry.rawRowNormSq_compact
noncomputable abbrev normalizedNoncompactSphereCoordinate := rawNormalizedSphereCoordinate

theorem noncompactNormalizedSU2_factor (g : ComplexGL2) :
    ∃ (a d : ℂˣ) (b : ℂ), g = upperTriangular a d b * complexSU2Embedding (noncompactNormalizedSU2 g) := by
  obtain ⟨a, d, b, h, -, -⟩ := KPCplxLoweringCoordinateBoost.Geometry.liftSU2_factor g
  exact ⟨a, d, b, h⟩

theorem noncompactVectorPolynomial_degree (j i : Fin 3) :
    (noncompactVectorPolynomial j i).totalDegree ≤ 2 := by
  unfold noncompactVectorPolynomial
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C]; omega
  · simpa only [MvPolynomial.totalDegree_X] using
      MvPolynomial.totalDegree_mul
        (MvPolynomial.X (noncompactAxis j) : MvPolynomial (Fin 3) ℂ)
        (MvPolynomial.X i)

theorem noncompactWeightPolynomial_degree (s : ℝ) (j : Fin 3) :
    (noncompactWeightPolynomial s j).totalDegree ≤ 1 := by
  unfold noncompactWeightPolynomial
  simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add]
    using MvPolynomial.totalDegree_mul
      (MvPolynomial.C (-noncompactCoefficient j * (1 + 2 * (s : ℂ))))
      (MvPolynomial.X (noncompactAxis j) : MvPolynomial (Fin 3) ℂ)

theorem noncompact_polynomial_profile_curve_derivative
    (s : ℝ) (j : Fin 3) (x : Fin 3 → ℂ) (c : ℝ → Fin 3 → ℂ)
    (hc : c 0 = x)
    (hd : ∀ i, HasDerivAt (fun t => c t i)
      (MvPolynomial.eval x (noncompactVectorPolynomial j i)) 0)
    (w : ℝ → ℂ) (hw : w 0 = 1)
    (hwd : HasDerivAt w (MvPolynomial.eval x (noncompactWeightPolynomial s j)) 0)
    (p : MvPolynomial (Fin 3) ℂ) :
    deriv (fun t => w t * MvPolynomial.eval (c t) p) 0 =
      MvPolynomial.eval x (noncompactWeightPolynomial s j * p +
        ∑ i : Fin 3, noncompactVectorPolynomial j i * MvPolynomial.pderiv i p) :=
  (weighted_polynomial_profile_curve_derivative
    (noncompactVectorPolynomial j) (noncompactWeightPolynomial s j)
    x c hc hd w hw hwd p).deriv

theorem noncompact_derivative_polynomial_coefficients_of_curves
    (s : ℝ) (j : Fin 3)
    (hcurve : ∀ k : KPCplxCharacterHaar.ComplexSU2,
      ∃ (c : ℝ → KPCplxCharacterHaar.ComplexSU2) (w : ℝ → ℂ),
        c 0 = k ∧ w 0 = 1 ∧
        (∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
          (MvPolynomial.eval (compactSphereCoordinate k)
            (noncompactVectorPolynomial j i)) 0) ∧
        HasDerivAt w (MvPolynomial.eval (compactSphereCoordinate k)
          (noncompactWeightPolynomial s j)) 0 ∧
        (∀ (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (t : ℝ),
          f (KPCplxCharacterHaar.complexSU2Embedding k *
            KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j))) =
          w t * f (KPCplxCharacterHaar.complexSU2Embedding (c t)))) :
    ∃ (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ),
      (∀ i, (A i).totalDegree ≤ 2) ∧ B.totalDegree ≤ 1 ∧
      ∀ (p : MvPolynomial (Fin 3) ℂ)
        (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s),
        compactRestriction s f = polynomialCompactRestriction p →
        compactRestriction s (localDerivative s (false, j) f) =
          polynomialCompactRestriction
            (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p) := by
  refine ⟨noncompactVectorPolynomial j, noncompactWeightPolynomial s j,
    noncompactVectorPolynomial_degree j, noncompactWeightPolynomial_degree s j, ?_⟩
  intro p f hpf
  funext k
  obtain ⟨c, w, hc, hw, hd, hwd, hfactor⟩ := hcurve k
  have he : (fun t : ℝ => f (KPCplxCharacterHaar.complexSU2Embedding k *
      KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j)))) =
      (fun t => w t * MvPolynomial.eval (compactSphereCoordinate (c t)) p) := by
    funext t
    rw [hfactor f t]
    congr 1
    exact congrFun hpf (c t)
  change deriv (fun t : ℝ => f (KPCplxCharacterHaar.complexSU2Embedding k *
      KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j)))) 0 = _
  rw [he]
  exact noncompact_polynomial_profile_curve_derivative s j (compactSphereCoordinate k)
    (fun t => compactSphereCoordinate (c t)) (congrArg compactSphereCoordinate hc)
    hd w hw hwd p

theorem noncompact_derivative_polynomial_coefficients_of_coordinate_tangents
    (s : ℝ) (j : Fin 3)
    (hcurve : ∀ k : KPCplxCharacterHaar.ComplexSU2,
      ∃ (c : ℝ → KPCplxCharacterHaar.ComplexSU2) (w : ℝ → ℂ),
        c 0 = k ∧ w 0 = 1 ∧
        (∀ i, HasDerivAt (fun t => compactSphereCoordinate (c t) i)
          (noncompactCoefficient j * ((if i = noncompactAxis j then 1 else 0) -
            compactSphereCoordinate k (noncompactAxis j) * compactSphereCoordinate k i)) 0) ∧
        HasDerivAt w (-noncompactCoefficient j * (1 + 2 * (s : ℂ)) *
          compactSphereCoordinate k (noncompactAxis j)) 0 ∧
        (∀ (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s) (t : ℝ),
          f (KPCplxCharacterHaar.complexSU2Embedding k *
            KPSmoothActualFlowData.matrixExponential ((t : ℂ) • cartanMatrix (false, j))) =
          w t * f (KPCplxCharacterHaar.complexSU2Embedding (c t)))) :
    ∃ (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ),
      (∀ i, (A i).totalDegree ≤ 2) ∧ B.totalDegree ≤ 1 ∧
      ∀ (p : MvPolynomial (Fin 3) ℂ)
        (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s),
        compactRestriction s f = polynomialCompactRestriction p →
        compactRestriction s (localDerivative s (false, j) f) =
          polynomialCompactRestriction
            (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p) := by
  apply noncompact_derivative_polynomial_coefficients_of_curves s j
  intro k
  obtain ⟨c, w, hc, hw, hd, hwd, hf⟩ := hcurve k
  refine ⟨c, w, hc, hw, ?_, ?_, hf⟩
  · simpa [noncompactVectorPolynomial] using hd
  · simpa [noncompactWeightPolynomial] using hwd
open KPCplxCharacterHaar
open scoped Matrix Matrix.Norms.Elementwise

theorem noncompact_derivative_polynomial_coefficients (s : ℝ) (j : Fin 3) :
    ∃ (A : Fin 3 → MvPolynomial (Fin 3) ℂ) (B : MvPolynomial (Fin 3) ℂ),
      (∀ i, (A i).totalDegree ≤ 2) ∧ B.totalDegree ≤ 1 ∧
      ∀ (p : MvPolynomial (Fin 3) ℂ)
        (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s),
        compactRestriction s f = polynomialCompactRestriction p →
        compactRestriction s (localDerivative s (false, j) f) =
          polynomialCompactRestriction
            (B * p + ∑ i : Fin 3, A i * MvPolynomial.pderiv i p) := by
  apply noncompact_derivative_polynomial_coefficients_of_coordinate_tangents s j
  intro k
  obtain ⟨c, hc, hcoord, hfactor⟩ :=
    MatrixPaths.actual_noncompact_normalized_compact_lift j k
  obtain ⟨hm, hd⟩ := MatrixPaths.actual_noncompact_matrix_path_tangent j k
  obtain ⟨hw, hwd⟩ := MatrixPaths.normalized_induction_weight_tangent s j k
    (fun t => (rawNoncompactPath j k t : Matrix (Fin 2) (Fin 2) ℂ)) hm hd
  refine ⟨c, (fun t => ((rawRowNormSq
    (rawNoncompactPath j k t)).rpow (-(1 + 2 * s)) : ℂ)), hc, hw, ?_, ?_, ?_⟩
  · intro i
    have ht := noncompact_hopf_derivative_of_matrix_tangent j k
      (fun t => (rawNoncompactPath j k t : Matrix (Fin 2) (Fin 2) ℂ)) hm hd i
    have he : (fun t => compactSphereCoordinate (c t) i) =
        (fun t => normalizedNoncompactSphereCoordinate (rawNoncompactPath j k t) i) := by
      funext t
      exact hcoord t i
    rw [he]
    simpa only [noncompactVectorPolynomial, map_mul, map_sub, MvPolynomial.eval_C,
      MvPolynomial.eval_X] using ht
  · simpa only [MatrixPaths.rawCoefficient, MatrixPaths.rawAxis,
      noncompactCoefficient, noncompactAxis] using hwd
  · intro f t
    exact hfactor s f t

end PolynomialDerivatives
end DedekindZetaZeroFree.RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction
