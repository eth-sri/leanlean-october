module

public import OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube

@[expose] public section

namespace OAI


open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary


lemma centralCubeIntegral_calibration_zero {K : ℕ}
     S   hS   hmax 
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)  η   u 
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
     W0 W1   X Y Z a e H  :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
     S   hS   hmax 
     η   R  (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
     W0 W1   X Y Z e   a H  :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.ProbeHighRowFamily



end OAI
