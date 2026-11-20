/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
import CCDN.ForMathlib.MvPolynomial
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! Linear coordinate substitutions preserve the total-degree filtration.
Their image coordinate rings inject into the original filtered ring. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Substituting polynomials of total degree at most `m` multiplies the total degree by at most `m`.
-/
lemma aeval_totalDegree_le {K σ τ : Type*} [CommSemiring K]
    (a : σ → MvPolynomial τ K) {m : ℕ} (ha : ∀ i, (a i).totalDegree ≤ m)
    (f : MvPolynomial σ K) : (aeval a f).totalDegree ≤ m * f.totalDegree :=
  eval₂Hom_totalDegree_le_mul (RingHom.id K) a ha f

/-- The map from projection coordinates to the original coordinate ring. -/
def projectionCoordinateMap {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K) :
    MvPolynomial σ K →ₐ[K] (MvPolynomial τ K ⧸ I) :=
  (Ideal.Quotient.mkₐ K I).comp (aeval a)

@[simp] lemma projectionCoordinateMap_X {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K) (i : σ) :
    projectionCoordinateMap I a (X i) = Ideal.Quotient.mk I (a i) := by
  simp [projectionCoordinateMap]

lemma projectionCoordinateMap_eq_zero_iff {K σ τ : Type*} [Field K]
    {I : Ideal (MvPolynomial τ K)} {a : σ → MvPolynomial τ K} {f g : MvPolynomial σ K}
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    projectionCoordinateMap I a g = 0 ↔ f ∣ g := by
  change g ∈ RingHom.ker (projectionCoordinateMap I a) ↔ _
  rw [hker, Ideal.mem_span_singleton]

/-- A linear coordinate substitution maps polynomials of total degree at most `M` into the filtered
piece of degree `M` of the coordinate ring. -/
lemma projectionCoordinateMap_filtered {K σ τ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) {M : ℕ}
    (f : MvPolynomial σ K) (hf : f.totalDegree ≤ M) :
    projectionCoordinateMap I a f ∈ filteredCoordinateSpace I M := by
  exact mem_filteredCoordinateSpace.mpr ⟨aeval a f,
    (aeval_totalDegree_le a ha f).trans (by simpa using hf), rfl⟩

lemma projectionKerLift_filtered {K σ τ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) {M : ℕ}
    {v : MvPolynomial σ K ⧸ RingHom.ker (projectionCoordinateMap I a)}
    (hv : v ∈ filteredCoordinateSpace (RingHom.ker (projectionCoordinateMap I a)) M) :
    Ideal.kerLiftAlg (projectionCoordinateMap I a) v ∈ filteredCoordinateSpace I M := by
  obtain ⟨p, hp, rfl⟩ := mem_filteredCoordinateSpace.mp hv
  exact projectionCoordinateMap_filtered I a ha p hp

/-- Linear projection cannot increase any filtered coordinate-ring dimension. -/
theorem linear_projection_filtered_finrank_le {K σ τ : Type*} [Field K]
    [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1) (M : ℕ) :
    Module.finrank K (filteredCoordinateSpace (RingHom.ker (projectionCoordinateMap I a)) M) ≤
      Module.finrank K (filteredCoordinateSpace I M) := by
  let ψ := projectionCoordinateMap I a
  let φ := Ideal.kerLiftAlg ψ
  let V := filteredCoordinateSpace (RingHom.ker ψ) M
  let L := (φ.toLinearMap.comp V.subtype).codRestrict _
    (fun v => projectionKerLift_filtered I a ha v.property)
  exact LinearMap.finrank_le_finrank_of_injective (f := L)
    (fun _ _ h => Subtype.ext (Ideal.kerLiftAlg_injective ψ (congrArg Subtype.val h)))

end
end CCDN
