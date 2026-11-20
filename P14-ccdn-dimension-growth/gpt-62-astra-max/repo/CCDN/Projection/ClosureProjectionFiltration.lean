/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Projection.ProjectiveClosureProjection
public import CCDN.Projection.ProjectiveClosureSpecialization
import CCDN.Algebra.CoordinatePowerGeneration
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Projection.HomogeneousFilteredProjection
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K] {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
  (a : Fin m → MvPolynomial (Fin n) K)

section

variable {σ A : Type*} [CommRing A] [Algebra K A] (ψ : MvPolynomial σ K →ₐ[K] A)

def imagePiece (N : ℕ) := (restrictTotalDegree σ K N).map ψ.toLinearMap

lemma imagePiece_mul {s t : ℕ} {x y : A} (hx : x ∈ imagePiece ψ s) (hy : y ∈ imagePiece ψ t) :
    x * y ∈ imagePiece ψ (s + t) := by
  obtain ⟨f,hf,rfl⟩ := hx
  obtain ⟨g,hg,rfl⟩ := hy
  exact ⟨f*g, (mem_restrictTotalDegree ..).mpr ((totalDegree_mul ..).trans
    (by simp_all [Nat.add_le_add, mem_restrictTotalDegree])), map_mul ψ f g⟩

end

/-- Finiteness on the projective closures makes the affine degree filtration a good
module filtration. After clearing a common conductor, only a bounded degree shift
is needed to express each filtered piece in the subalgebra. -/
theorem closure_projection_conductor_shift (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates a)).IsIntegral)
    (c : MvPolynomial (Fin n) K ⧸ I)
    (hc : ∀ x, ∃ p, projectionCoordinateMap I a p = c * x) :
    ∃ D : ℕ, ∀ N x, x ∈ filteredCoordinateSpace I N → c * x ∈ imagePiece (projectionCoordinateMap I a) (D + N) := by
  classical
  let C := projectiveClosureIdeal I
  let A := MvPolynomial _ K ⧸ C
  let R := MvPolynomial (Fin (m+1)) K
  let ψ := projectionCoordinateMap I a
  let φ := projectionCoordinateMap C (closureProjectionCoordinates a)
  let := φ.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hint⟩
  let := Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let : Module.Finite R A := Algebra.IsIntegral.finite
  obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := A)
  let G : A →ₐ[K] Polynomial _ := Ideal.kerLiftAlg _
  choose p hp using fun i j => hc _
  let D := Finset.univ.sup fun i => (G (v i)).support.sup fun j => (p i j).totalDegree
  have hgen (i j) : c * (G (v i)).coeff j ∈ imagePiece ψ (D+j) := by
    by_cases hj : j ∈ (G (v i)).support
    · exact ⟨p i j, (mem_restrictTotalDegree ..).mpr (((Finset.le_sup (f := fun t => (p i t).totalDegree) hj).trans
        (Finset.le_sup (f := fun i => (G _).support.sup fun j => (p i j).totalDegree) (Finset.mem_univ i))).trans (Nat.le_add_right ..)), hp i j⟩
    · simp [Polynomial.notMem_support_iff.mp hj]
  have hφ (q : R) (j : ℕ) : (G (φ q)).coeff j ∈ imagePiece ψ j := by
    change (projectiveClosureMap I (aeval _ q)).coeff j ∈ _
    rw [projectiveClosureMap_coeff, homogeneousComponent_aeval_linear _ (closureProjectionCoordinates_homogeneous a ha), affineChart_aeval_closureProjectionCoordinates]
    exact ⟨_, (mem_restrictTotalDegree ..).mpr ((affineChart_totalDegree_le _).trans (homogeneousComponent_isHomogeneous j q).totalDegree_le), rfl⟩
  have hcoeff (x : A) : ∀ j, c * (G x).coeff j ∈ imagePiece ψ (D + j) := by
    have hx : x ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
    induction hx using Submodule.span_induction with
    | mem _ h => obtain ⟨i,rfl⟩ := h; exact hgen i
    | zero => simp
    | add x y hx hy ih jh => intro j; simpa [mul_add] using (imagePiece ψ _).add_mem (ih j) (jh j)
    | smul r x hx ih =>
      intro j
      change c * (G (φ r * x)).coeff j ∈ _
      rw [map_mul, Polynomial.coeff_mul, Finset.mul_sum]
      apply Submodule.sum_mem
      intro e he
      have h := imagePiece_mul ψ (hφ r e.1) (ih e.2)
      rw [mul_left_comm] at h
      convert h using 2
      have := Finset.mem_antidiagonal.mp he
      omega
  refine ⟨D, fun N x hx => ?_⟩
  obtain ⟨f,hf,rfl⟩ := hx
  let g := scaledHomogenize N 1 f
  have h := hcoeff ((Ideal.Quotient.mk C) g) N
  change c * (projectiveClosureMap I g).coeff N ∈ _ at h
  rwa [projectiveClosureMap_coeff, homogeneousComponent_eq_self (scaledHomogenize_homogeneous 1 f ((mem_restrictTotalDegree ..).mp hf)), affineChart_scaledHomogenize_one] at h

end
end CCDN
