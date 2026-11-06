module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSecondBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionProductSecond
public import PDEFoundation.Calculus.RegularityOrder


/-! # Second velocity derivatives of the literal extended profile -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

variable {d : ℕ}

variable {alpha : ℝ} (h : CounterProfileStatement d alpha)

/-- The literal second representative obtained by differentiating the selected first jet. -/
def constructionExtendedPackedHessian   (r mu R m t : ℝ)
    (x : PDE.Vec (d + d)) (i k : Fin d) : ℝ :=
  constructionPackedCutoff d m R x * spatialPackedCutoffVelocityHessian h r mu R t x i k +
    spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k) *
      fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec (Fin.natAdd d i)) +
    fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec (Fin.natAdd d k)) *
      spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d i) +
    spatialPackedCutoffValue h r mu R t x *
      fderiv ℝ (fun y => fderiv ℝ (constructionPackedCutoff d m R) y
        (PDE.basisVec (Fin.natAdd d k))) x (PDE.basisVec (Fin.natAdd d i))

section
variable (r : ℝ) (hr : 0 < r) (mu R m t : ℝ)

include hr
/-- The selected extended first jets are locally integrable. -/
theorem construction_extendedGradient_locallyIntegrable    (i : Fin (d + d)) :
    LocallyIntegrable (fun x => constructionExtendedPackedGradient h r mu R m t x i)
      volume := by
  have hc := contDiff_providerPackedCutoff d m R

  exact ((construction_cutoffGradient_locallyIntegrable h r hr mu R t i).continuous_mul
    hc.continuous).add ((construction_cutoffValue_continuous h r mu R t).locallyIntegrable
      |>.mul_continuous ((hc.continuous_fderiv (by simp)).clm_apply continuous_const))

/-- The selected extended Hessian components are locally integrable. -/
theorem construction_extendedHessian_locallyIntegrable    (i k : Fin d) :
    LocallyIntegrable (fun x => constructionExtendedPackedHessian h r mu R m t x i k)
      volume := by
  have hc := contDiff_providerPackedCutoff d m R
  have hd (j : Fin d) : ContDiff ℝ PDE.smoothOrder
      (fun x => fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec (Fin.natAdd d j))) :=
    (hc.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)

  exact ((((construction_cutoffHessian_locallyIntegrable h r hr mu R t i k).continuous_mul
    hc.continuous).add ((construction_cutoffGradient_locallyIntegrable h r hr mu R t
      (Fin.natAdd d k)).mul_continuous (hd i).continuous)).add
        ((construction_cutoffGradient_locallyIntegrable h r hr mu R t
          (Fin.natAdd d i)).continuous_mul (hd k).continuous)).add
            ((construction_cutoffValue_continuous h r mu R t).locallyIntegrable
              |>.mul_continuous (((hd k).continuous_fderiv (by simp)).clm_apply continuous_const))
end


/-- The extended first velocity jet has precisely the selected second weak derivative. -/
theorem construction_extended_velocityJet_weak  (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R m t : ℝ) (i k : Fin d) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ PDE.smoothOrder test) (hs : HasCompactSupport test) :
    (∫ x, constructionExtendedPackedGradient h r mu R m t x (Fin.natAdd d k) *
      fderiv ℝ test x (PDE.basisVec (Fin.natAdd d i))) =
      -(∫ x, constructionExtendedPackedHessian h r mu R m t x i k * test x) := by



  have hu := weakPartial_on_of_global univ _
    _
    (((fun x => spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d i))))
    (spatialPackedCutoff_weak_first_of_profile hd ha ha1 h r hr mu R t _)
  have hg := weakPartial_on_of_global univ _
    (((fun x => spatialPackedCutoffGradient h r mu R t x (Fin.natAdd d k))))
    (((fun x => spatialPackedCutoffVelocityHessian h r mu R t x i k)))
    (spatialPackedCutoff_velocityJet_weak_of_profile hd ha ha1 h r hr mu R t i k)




  have he := construction_weak_second_product _ _ _ _ (constructionPackedCutoff d m R)
    (Fin.natAdd d i) (Fin.natAdd d k) hu hg (contDiff_providerPackedCutoff d m R)
    (by
        simpa only [PDE.volumeOn, Measure.restrict_univ] using
          (construction_cutoffValue_continuous h r mu R t).locallyIntegrable) (by
        simpa only [PDE.volumeOn, Measure.restrict_univ] using
          construction_cutoffGradient_locallyIntegrable h r hr mu R t (Fin.natAdd d i)) (by
        simpa only [PDE.volumeOn, Measure.restrict_univ] using
          construction_cutoffGradient_locallyIntegrable h r hr mu R t (Fin.natAdd d k)) (by
        simpa using construction_cutoffHessian_locallyIntegrable h r hr mu R t i k) test ht hs (subset_univ _)
  simpa only [Measure.restrict_univ, constructionExtendedPackedGradient,
    constructionExtendedPackedHessian] using! he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
