module
public import OAI.NumberTheory.DirichletL.GaussSum.ActiveReindexing

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CanonicalRowCompletion.GoodMaskRowData
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance rayUnitsFintype : Fintype Eisˣ := by
  letI : Finite Eisˣ:=PrimaryIdealUnitReindex.finite_units
  exact Fintype.ofFinite _

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
    [Fintype (Eis⧸Ideal.span {reflectionConductor q})]
    [∀h:Eis⧸Ideal.span {reflectionConductor q},
      Fintype (fixedFourierGeometry (reflectionConductor q) (reflectionConductor_ne_zero q hq) h).PhaseResidue]

end CanonicalRowCompletion.ActualFiber

namespace CompletedGauss
open ActualEisensteinCubic
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

open scoped Classical BigOperators ContDiff

namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

open scoped Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CubicEisenstein CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

namespace ShortDraft

end ShortDraft

open scoped BigOperators Classical ContDiff

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

end

end OAI
