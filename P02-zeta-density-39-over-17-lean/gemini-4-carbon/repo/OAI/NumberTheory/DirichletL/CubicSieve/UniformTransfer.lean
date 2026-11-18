module
public import OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set
open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
namespace SecondPassArithmetic
open ConcretePrimeRowBridge (idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

end SecondPassArithmetic
namespace SecondPassIntegration
open SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

end SecondPassIntegration

namespace SecondPassArithmetic

end SecondPassArithmetic
namespace SecondPassIntegration
open SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

end SecondPassIntegration

namespace SecondPassArithmetic

section
open SecondPassFiber (newLabel newRow)
open JointLogSeparation (outerWindow)

end


end SecondPassArithmetic
namespace SecondPassIntegration
open SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

end SecondPassIntegration

namespace SecondPassArithmetic
open SecondPassFiber (newLabel newRow)
open JointLogSeparation (outerWindow)

end SecondPassArithmetic

end

end OAI
