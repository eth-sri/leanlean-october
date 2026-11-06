module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Lean.Elab.Tactic.Grind
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Scalar reverse-time distribution separation

This module transfers scalar distribution separation on an open interval from
ambient Lebesgue measure to the literal restricted reverse-time measure.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory Set
open scoped ENNReal

private theorem integrable_mul_of_tsupport_subset
    {U : Set ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f (volume.restrict U)) (hg : Continuous g)
    (hgCompact : HasCompactSupport g) (hgSupport : tsupport g ⊆ U) :
    Integrable (fun tau => f tau * g tau)  := ((integrableOn_iff_integrable_of_support_subset fun ⦃tau⦄ htau => tsupport_mul_subset_right (subset_closure htau)).mp
  (IntegrableOn.mul_continuousOn (IntegrableOn.mono_set hf hgSupport) (Continuous.continuousOn hg)
    (HasCompactSupport.isCompact hgCompact)))

variable (T : ℝ) {f : ℝ → ℝ}

/-- An integrable scalar function on the literal reverse-time interval whose
pairing with every compact smooth reverse-time test vanishes is zero a.e. -/
theorem ae_eq_zero_of_integral_reverseTimeScalarTest

    (hf : MeasureTheory.Integrable f (reverseTimeVolume T))
    (hzero : ∀ eta : ReverseTimeScalarTest T,
      (∫ tau, f tau * eta tau ∂reverseTimeVolume T) = 0) :
    f =ᵐ[reverseTimeVolume T] 0 := by
  let U  := reverseTimeOpenInterval T
  have hUOpen : IsOpen U := by
    simpa only [U, reverseTimeOpenInterval] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) T))
  have hfRestrict : Integrable f (volume.restrict U) := by
    exact hf


  have hAmbient  :=
    hUOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (locallyIntegrableOn_of_locallyIntegrable_restrict hfRestrict.locallyIntegrable) (by
        intro g hgSmooth hgCompact hgSupport
        let eta : ReverseTimeScalarTest T :=
          { toFun := g
            contDiff' := hgSmooth
            hasCompactSupport' := hgCompact
            tsupport_subset' := hgSupport }
        have hzeroOutPublic : ∀ tau, tau ∉ U → f tau * g tau = 0 := by
          intro tau htau

          rw [image_eq_zero_of_notMem_tsupport (fun htsupport => htau (hgSupport htsupport))]
          simp




        exact (show Integrable (fun tau => g tau * f tau)  ∧
              (∫ tau, g tau * f tau) = 0 by
            constructor
            · simpa only [mul_comm] using
                integrable_mul_of_tsupport_subset hfRestrict hgSmooth.continuous hgCompact hgSupport
            · calc
                (∫ tau, g tau * f tau) = ∫ tau in U, g tau * f tau := by
                  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (by
                      intro tau htau
                      simpa only [mul_comm] using hzeroOutPublic tau htau)]
                _ = 0 := (by
                    calc
                      (∫ tau in U, g tau * f tau) =
                          ∫ tau in U, f tau * g tau := by
                            grind
                      _ = 0 := (by
                          have hzeroEta := hzero eta
                          change (∫ tau, f tau * g tau ∂(volume.restrict U)) = 0 at hzeroEta
                          exact hzeroEta))).2)
  rw [Filter.EventuallyEq, reverseTimeVolume,
    ae_restrict_iff' hUOpen.measurableSet]
  exact hAmbient

/-- The `L²` specialization of reverse-time scalar distribution separation. -/
theorem ae_eq_zero_of_memLp_two_integral_reverseTimeScalarTest

    (hf : MeasureTheory.MemLp f (2 ) (reverseTimeVolume T))
    (hzero : ∀ eta : ReverseTimeScalarTest T,
      (∫ tau, f tau * eta tau ∂reverseTimeVolume T) = 0) :
    f =ᵐ[reverseTimeVolume T] 0 := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  exact ae_eq_zero_of_integral_reverseTimeScalarTest T
    (hf.integrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))) hzero

end HypoellipticAleksandrov.Parabolic.Dirichlet
