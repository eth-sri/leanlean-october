module
public import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

section
variable {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
include K S hS hmax
lemma centralCubeIntegral_calibration_zero
    (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

theorem finiteCentralCubeRows_filter_calibration
    (η : Character) (R : Finset FreeRow) (T : Fin K→ Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  pm_3809 finiteCentralCubeRows Finset.sum_filter u hu
  pm_410
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  grind
end

end SevenEighths.ProbeHighRowFamily

end

end OAI
