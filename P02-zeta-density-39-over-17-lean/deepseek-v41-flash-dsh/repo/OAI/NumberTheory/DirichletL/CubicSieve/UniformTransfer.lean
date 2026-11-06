module
public import OAI.NumberTheory.DirichletL.CubicSieve.ArithmeticBins

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

end SecondPassArithmetic
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

end SecondPassIntegration

namespace SecondPassArithmetic
open ActualEisensteinCubic

end SecondPassArithmetic
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open JointLogSeparation (outerWindow)

end

open ActualEisensteinCubic

end SecondPassArithmetic
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open JointLogSeparation (outerWindow)

end SecondPassArithmetic

end

end OAI
