module

public import OAI.NumberTheory.DirichletL.GaussSum.ActiveReindexing

@[expose] public section

namespace OAI

noncomputable section


open MulChar AddChar Filter Asymptotics MeasureTheory

open MeasureTheory Real

open Finset Complex

open Filter Real Asymptotics ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Filter Asymptotics

open MeasureTheory Set ActualEisensteinCubic UniqueFactorizationMonoid


namespace CanonicalRowCompletion.GoodMaskRowData
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion.GoodMaskRowData

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

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



namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber



namespace CompletedGauss.FreeReflection
open ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
local notation "Eis" => ActualEisensteinCubic.O

end CompletedGauss.FreeReflection

namespace CanonicalRowCompletion.ActualFiber
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable (q:ℕ) (hq:q≠0) (m:Eis) (hm:m≠0)
    (rows:Finset (Ideal Eis)) (R F:Ideal Eis) (hR:R≠0) (hF:Squarefree F)
    (hrows:∀I∈rows,I≠0) (v:Eisˣ)
variable [Fintype (Eis⧸Ideal.span {reflectionConductor q})]

end CanonicalRowCompletion.ActualFiber

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CubicEisenstein CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

namespace ShortDraft

end ShortDraft

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
