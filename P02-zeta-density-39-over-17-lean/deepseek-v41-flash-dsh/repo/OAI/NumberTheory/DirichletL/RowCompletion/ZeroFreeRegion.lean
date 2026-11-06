module
public import OAI.NumberTheory.DirichletL.RowCompletion.BranchDecoding

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set


namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance collectionUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalCoefficientClass CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

end

end CanonicalRowCompletion

namespace ShortDraft

end ShortDraft

end

end OAI
