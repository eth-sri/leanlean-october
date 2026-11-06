module

public import HypoellipticAleksandrov.Parabolic.WeakEquationMollificationResidualDecay
public import HypoellipticAleksandrov.Parabolic.WeakSolutionMollifierConvergence
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Aligned residual-bearing weak-solution mollifications

This module selects one concrete localized parabolic jet and proves the
simultaneous compact approximation, residual, coefficient, and positivity
properties of that same jet's literal right mollifications.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal

namespace LocalizedParabolicJet

/-- The concrete localized jet selected for a weak solution has an eventual
pointwise mollified residual equation on its compact carrier. -/
theorem eventually_residual_equation_on
    {d : Nat} {A Aext : CoefficientField d}
    {U K : HypoellipticAleksandrov.Parabolic.Region d} {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (J : LocalizedParabolicJet d U K u)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      parabolicOperator (parabolicMollifyCoefficient Aext n)
          (parabolicMollifiedValue J.g n) z =
        weakEquationMollificationResidual Aext J.g n z := by
  have hp : (1 : ENNReal) ≤ parabolicExponent d := by
    simp [parabolicExponent]


  obtain ⟨O, hO, hclosureVO, hOW, _hvalue, htime, _hgrad, hhessian⟩ :=
    J.exists_open_plateau




  have hEquation := eventually_residual_equation_of_ae_on J.V_closure_compact hO hclosureVO
    J.g hp (by
        apply (ae_restrict_iff' hO.measurableSet).mpr
        have hWeqO' := (ae_restrict_iff' hO.measurableSet).mp ((show J.w.timeDeriv =ᵐ[timeVelocityVolumeOn J.W]
      fun z => matrixContraction (coefficientAt A z) (J.w.velocityHessian z) by
            filter_upwards [(hWeak.equationOn J.W_open J.W_closure_compact J.closure_W_subset_U hp J.w J.w_ae_eq_u)] with z hz
            exact sub_eq_zero.mp (hz)).filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOW)
        have hExtAEO' := (ae_restrict_iff' hO.measurableSet).mp (hExtAE.filter_mono <| ae_mono <| Measure.restrict_mono_set volume (hOW.trans (subset_closure.trans J.closure_W_subset_U)))
        filter_upwards [hWeqO', hExtAEO'] with z hweq hAext hzO
        calc
          J.g.timeDeriv z = J.w.timeDeriv z := htime hzO
          _ = matrixContraction (coefficientAt A z) (J.w.velocityHessian z) := hweq hzO
          _ = matrixContraction (coefficientAt Aext z) (J.g.velocityHessian z) := by
            rw [hAext hzO, hhessian hzO])
  filter_upwards [hEquation] with n hn
  intro z hz
  exact hn z (subset_closure (J.K_subset_V hz))

end LocalizedParabolicJet

/-- A nonnegative local weak solution admits one selected localized jet whose
literal mollifications converge uniformly to the supplied representative,
have decaying residuals, and eventually satisfy all stated smooth classical
approximation properties on the same compact carrier. -/
theorem exists_localizedJet_eventually_nonnegative_residual_mollifications_tendsto
    (d : Nat) (hd : 1 ≤ d) (lam Lam : Real)
    (A Aext : CoefficientField d)
    (U K : HypoellipticAleksandrov.Parabolic.Region d)
    (u q : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A)
    (hExtBorel : IsBorelCoefficient Aext)
    (hExtLower : HasLowerEllipticity lam Aext)
    (hExtUpper : HasUpperEllipticity Lam Aext)
    (hWeak : IsWeakParabolicEquationLoc A U (parabolicExponent d) u)
    (huNonneg : ∀ᵐ z ∂timeVelocityVolumeOn U, 0 ≤ u z)
    (hq : ContinuousOn q U)
    (hqu : q =ᵐ[timeVelocityVolumeOn U] u) :
    ∃ J : LocalizedParabolicJet d U K u,
      TendstoUniformlyOn
        (fun n z => parabolicMollifiedValue J.g n z) q atTop K ∧
      Tendsto (fun n => eLpNorm
        (weakEquationMollificationResidual Aext J.g n)
        (parabolicExponent d) (volume.restrict K)) atTop (nhds 0) ∧
      ∀ᶠ n in atTop,
        IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
        IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
        HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
        HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) ∧
        ContDiff Real (↑PDE.smoothOrder) (parabolicMollifiedValue J.g n) ∧
        (∀ z ∈ K, 0 ≤ parabolicMollifiedValue J.g n z) ∧
        (∀ z ∈ K,
          parabolicOperator (parabolicMollifyCoefficient Aext n)
              (parabolicMollifiedValue J.g n) z =
            weakEquationMollificationResidual Aext J.g n z) := by
  obtain ⟨J, hUniform⟩ :=
    ParabolicW12Loc.exists_localizedJet_mollifications_tendstoUniformlyOn d hd hU hK hKU
      hWeak.parabolicW12Loc hq hqu

  have hResidual := tendsto_eLpNorm_weakEquationMollificationResidual_on_compact d lam Lam
    Aext J.g K hK hExtBorel hExtLower hExtUpper
  have hSymm  :=
    isSymmetricCoefficient_of_hasLowerEllipticity hExtLower
  have hCoefficient : ∀ᶠ n in atTop,
      IsSmoothCoefficient (parabolicMollifyCoefficient Aext n) ∧
      IsSymmetricCoefficient (parabolicMollifyCoefficient Aext n) ∧
      HasLowerEllipticity lam (parabolicMollifyCoefficient Aext n) ∧
      HasUpperEllipticity Lam (parabolicMollifyCoefficient Aext n) :=
    Filter.Eventually.of_forall fun n =>
      ⟨isSmoothCoefficient_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hExtLower
          hExtUpper n,
        isSymmetricCoefficient_parabolicMollifyCoefficient d lam Lam Aext hSymm n,
        hasLowerEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hSymm
          hExtLower hExtUpper n,
        hasUpperEllipticity_parabolicMollifyCoefficient d lam Lam Aext hExtBorel hSymm
          hExtLower hExtUpper n⟩
  obtain ⟨O, hO, hclosureVO, hOW, hvalue, _htime, _hgrad, _hhessian⟩ :=
    J.exists_open_plateau



  have hWValueO  :=
    J.w_ae_eq_u.filter_mono <| ae_mono <| Measure.restrict_mono_set volume hOW
  have huNonnegO  :=
    huNonneg.filter_mono <| ae_mono <| Measure.restrict_mono_set volume (hOW.trans (subset_closure.trans J.closure_W_subset_U))

  have hNonnegative :=
    eventually_nonnegative_parabolicMollifiedValue_of_ae_nonnegative_on hK hO (J.K_subset_V.trans (subset_closure.trans hclosureVO)) J.g (by
        filter_upwards [(show J.g.toFun =ᵐ[timeVelocityVolumeOn O] J.w.toFun by
            filter_upwards [ae_restrict_mem hO.measurableSet] with z hzO
            exact hvalue hzO).trans hWValueO, huNonnegO] with z hgu hnonneg
        rw [hgu]
        exact hnonneg)

  refine ⟨J, ?_, hResidual, ?_⟩
  · exact hUniform
  · filter_upwards [hCoefficient, hNonnegative, (J.eventually_residual_equation_on hExtAE hWeak)] with n hcoefficient hnonnegative
      hequation
    exact ⟨hcoefficient.1, hcoefficient.2.1, hcoefficient.2.2.1, hcoefficient.2.2.2,
      contDiff_parabolicMollifiedValue J.g (by
          simp [parabolicExponent]) n, hnonnegative, hequation⟩

end HypoellipticAleksandrov.Parabolic
