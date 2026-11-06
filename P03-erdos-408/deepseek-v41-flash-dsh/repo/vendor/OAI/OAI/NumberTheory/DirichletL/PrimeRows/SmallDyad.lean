module

public import OAI.NumberTheory.DirichletL.PrimeRows.TailScales

@[expose] public section

namespace OAI

noncomputable section

open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def absolutePhysicalDyadIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) : ℝ :=
  ∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
      physicalDyadNorm S hS hmax η R T hT W Yp ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure

end SevenEighths.ProbeHighRowFamily
end

end OAI
