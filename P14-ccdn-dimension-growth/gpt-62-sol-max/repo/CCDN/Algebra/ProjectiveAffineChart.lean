/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Height.ProjectiveZeroLocus

/-! Affine coordinates on the standard open subset of projective space,
with injectivity and compatibility with homogeneous equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

/-- Affine coordinates in the chart where `k` is the nonzero pivot. -/
def projectiveAffineCoordinatesAt {n : ℕ} (k : Fin (n + 1))
    (x : Projectivization K (Fin (n + 1) → K)) : Fin n → K := fun j =>
  x.rep (Equiv.swap 0 k j.succ) / x.rep k

lemma projectiveAffineCoordinatesAt_normalization {n : ℕ} {k : Fin (n + 1)}
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep k ≠ 0) :
    Fin.cons 1 (projectiveAffineCoordinatesAt k x) ∘ Equiv.swap 0 k = (x.rep k)⁻¹ • x.rep := by
  have h : Fin.cons 1 (projectiveAffineCoordinatesAt k x) =
      (x.rep k)⁻¹ • (x.rep ∘ Equiv.swap 0 k) := by
    funext i
    refine Fin.cases (by simp [hx]) (fun j => ?_) i
    simp [projectiveAffineCoordinatesAt, div_eq_mul_inv, mul_comm]
  rw [h]
  ext i
  simp

/-- The vector `(1, a₁, …, aₙ)` is nonzero. -/
lemma affineCoordinateVector_ne_zero {n : ℕ} (a : Fin n → K) :
    (Fin.cons 1 a : Fin (n + 1) → K) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp at hh

private def affineProjectivePointAt {n : ℕ} (k : Fin (n + 1)) (a : Fin n → K) :
    Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (Fin.cons 1 a ∘ Equiv.swap 0 k) (by
    intro h
    have hh := congrFun h k
    simp at hh)

private lemma projectiveAffineCoordinatesAt_mk {n : ℕ} {k : Fin (n + 1)}
    (x : Projectivization K (Fin (n + 1) → K)) (hx : x.rep k ≠ 0) :
    affineProjectivePointAt k (projectiveAffineCoordinatesAt k x) = x := by
  conv_rhs => rw [← x.mk_rep]
  rw [affineProjectivePointAt, Projectivization.mk_eq_mk_iff']
  exact ⟨_, (projectiveAffineCoordinatesAt_normalization x hx).symm⟩

/-- Projective points with nonzero pivot are determined by their affine coordinates. -/
theorem projectiveAffineCoordinatesAt_injective {n : ℕ} {k : Fin (n + 1)}
    {x y : Projectivization K (Fin (n + 1) → K)}
    (hx : x.rep k ≠ 0) (hy : y.rep k ≠ 0)
    (hxy : projectiveAffineCoordinatesAt k x = projectiveAffineCoordinatesAt k y) : x = y := by
  simpa only [projectiveAffineCoordinatesAt_mk _ hx, projectiveAffineCoordinatesAt_mk _ hy] using
    congrArg (affineProjectivePointAt k) hxy

/-- The point `[1 : a]` of projective space on the standard chart. -/
def affineProjectivePoint {K : Type*} [Field K] {n : ℕ} (a : Fin n → K) :
    Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (Fin.cons 1 a) (affineCoordinateVector_ne_zero a)

/-- The map `a ↦ [1 : a]` from affine space to projective space is injective. -/
theorem affineProjectivePoint_injective {K : Type*} [Field K] (n : ℕ) :
    Function.Injective (@affineProjectivePoint K _ n) := by
  intro a b he
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp he
  have hc1 : (c : K) = 1 := by
    have h := congrFun hc 0
    change (c : K) * 1 = 1 at h
    simpa using h
  simp_all

end
end CCDN
