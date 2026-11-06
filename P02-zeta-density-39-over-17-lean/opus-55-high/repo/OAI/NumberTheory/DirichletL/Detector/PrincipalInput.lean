module
public import OAI.NumberTheory.DirichletL.Detector.PrincipalSplit
public import OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeMellinBoundary
open PrincipalMellinResidues ProbeFiniteProductBounds
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

section
variable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→ PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
include K η S hS P hP hPS W0 W1 X Y Z
lemma principalTuple_source_integrand (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    sourceMellinWeight W0 W1 X Y Z x w z*
      (∏i,(elementNorm (primaryGenerator (P i).val):ℂ)^(z-1))*
      indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) x) w z*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w := by
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    pm_431
  rw [indexedCompensatedHigh_principal_continued η S hS P hP hPS x w z hx hw hz]
  unfold sourceMultiplier sourceMellinWeight
  pm_3780 hnorm slotMultiplier Finset.sum_singleton one_mul localMultiplier Complex.ofReal_natCast Finset.prod_mul_distrib
  ring

theorem principalRowIntegral_eq_sourceMultiplier :
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val) W0 W1 X Y Z =
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((3:ℂ)+t.1.1*Complex.I)
          (globalClosedCorrection η S ((3:ℂ)+t.1.1*Complex.I))
          (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) ((3:ℂ)+t.1.1*Complex.I))
          ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*((2:ℂ)+t.1.2*Complex.I))*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+t.2*Complex.I) ∂ heightMeasure := by
  pm_8147 principalRowIntegral t
  exact principalTuple_source_integrand η S hS P hP hPS W0 W1 X Y Z
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by simp_all)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
end

end SevenEighths.ProbePhysical
end

end OAI
