/- Common linear/unit/product/raw-pairing consumer interface.
The geometric normalization adapter uses raw B = 3 logHessian. -/
module
public import AlbertGeometry.IntrinsicLocalReconstruction
public import Glennie.NativeGenerationEndpointR01
public import Glennie.Compact.NativeWordTableBasisR01
public import Glennie.Compact.CyclicTraceNullR01

@[expose] public section
namespace Glennie.Compact.MarkedModelConsumerCandidate
noncomputable section
open Glennie
open Glennie.Compact.CyclicTraceNullR01
open Glennie.Compact.NativeWordTableR01
open AlbertGeometry.Cubic AlbertGeometry.BasedNormAdjointTransport
open AlbertGeometry.IntrinsicLocalTransport
open scoped BigOperators

/-- Exactly the existing downstream linear/unit/product/metric boundary,
with the source metric written in the native raw normalization. -/
structure ModelEquiv (E : Type*) [AddCommGroup E] [Module ℝ E]
    (e : E) (j : E → E → E) (B : E → E → ℝ) where
  A : E ≃ₗ[ℝ] Albert
  map_unit : A e = 1
  map_product : ∀ x y, A (j x y) = jordan (A x) (A y)
  map_metric : ∀ x y, B x y = inner (A x) (A y)

/-- Optional marks supplement the same common equivalence interface. -/
structure MarkedModelEquiv (E : Type*) [AddCommGroup E] [Module ℝ E]
    (e : E) (j : E → E → E) (B : E → E → ℝ)
    (a : Fin 3 → E) (b : Fin 3 → Albert) extends ModelEquiv E e j B where
  map_marks : ∀ i, A (a i) = b i

section Consumers
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {e : E} {j : E → E → E} {B : E → E → ℝ}

end Consumers

section GeometricAdapter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable (P : SymmetricTrilinearForm E) (e : E)
  (he : diagonalCubic P.form e = 1)
  (hp : ∀ u : E, u ≠ 0 → 0 < logHessianForm P e u u)

end GeometricAdapter

section MatchingData
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The selected exact 27 syntactic Jordan words evaluated in the candidate.
The ambient product is bilinear, with no Jordan identity or classification input. -/
def candidateWords (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) :
    Fin 27 → E := fun i => eval e a (fun x y => j x y) (words i)

theorem candidateWords_unit (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 0 = e := rfl

theorem candidateWords_mark0 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 1 = a 0 := rfl

theorem candidateWords_mark1 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 2 = a 1 := rfl

theorem candidateWords_mark2 (e : E) (a : Fin 3 → E)
    (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : candidateWords e a j 3 = a 2 := rfl

/-- These are finite scalar observations; none supplies span/closure/recognition. -/
structure Match27 (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Prop where
  gram : ∀ i k,
    Inner.inner ℝ (candidateWords e a j i) (candidateWords e a j k) =
      inner (nativeWords i) (nativeWords k)
  mixed : ∀ i k l,
    Inner.inner ℝ (j (candidateWords e a j i) (candidateWords e a j k))
      (candidateWords e a j l) =
      inner (jordan (nativeWords i) (nativeWords k)) (nativeWords l)
  product_sq : ∀ i k,
    Inner.inner ℝ (j (candidateWords e a j i) (candidateWords e a j k))
      (j (candidateWords e a j i) (candidateWords e a j k)) =
      inner (jordan (nativeWords i) (nativeWords k))
        (jordan (nativeWords i) (nativeWords k))

/-- The intended output carrier, allowing unused ambient directions. -/
def wordSpan (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (candidateWords e a j))

/-- The generated unital product-closed submodule, independently of the word list. -/
def generated (e : E) (a : Fin 3 → E) (j : E →ₗ[ℝ] E →ₗ[ℝ] E) : Submodule ℝ E :=
  sInf {K : Submodule ℝ E | e ∈ K ∧ (∀ i, a i ∈ K) ∧
    (∀ x ∈ K, ∀ y ∈ K, j x y ∈ K)}

/- Closure, generation, and fixed-mark uniqueness from Match27 are proved in
GeneratedRecognitionR01; these definitions contain no recognition premise. -/
end MatchingData
end
end Glennie.Compact.MarkedModelConsumerCandidate
