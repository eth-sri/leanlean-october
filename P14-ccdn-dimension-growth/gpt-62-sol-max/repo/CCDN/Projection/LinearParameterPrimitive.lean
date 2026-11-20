/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import CCDN.Projection.CurvePrimitivePair
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import CCDN.Height.BoundedPrimitiveElement
public import CCDN.Projection.FilteredProjectionRank
import CCDN.Hilbert.LinearCoordinates
import CCDN.Projection.PrimitiveCoordinateField
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! Bounded primitive augmentation of any independent linear parameter
tuple of the Hilbert dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Given `m + 1` linear forms algebraically independent modulo a prime `I` of projective dimension
`m` and degree `d` (in characteristic zero), some moment coordinate with parameter `k ≤ n * d ^ 2`
together with these forms generates the function field of `I`. -/
theorem exists_bounded_linear_parameter_primitive
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (hfg : HasFilteredGenerators I (projectionCoordinateMap I l))
    (hi : Function.Injective (projectionCoordinateMap I l))
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ k : ℕ, k ≤ n * d ^ 2 ∧
      IntermediateField.adjoin K
        (Set.range (fun i : Fin (m + 2) =>
          algebraMap (MvPolynomial (Fin n) K ⧸ I) F
            ((Ideal.Quotient.mk I) (Fin.cases (momentCoordinate K n k) l i)))) = ⊤ := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let φ := IsScalarTower.toAlgHom K A F
  let u := fun i => φ ((Ideal.Quotient.mk I) (l i))
  let R := projectionImageField (F := F) I l
  obtain ⟨hfinite, hrank⟩ := filtered_normalization_rank (F := F) I l hl hfg hi hdimdeg
  obtain ⟨k, hk, hprim⟩ := exists_bounded_curve_primitive_element (R := R) (F := F) I
  refine ⟨k, by simpa only [R, hrank] using hk, ?_⟩
  have hh := primitive_parameter_tuple_adjoin_top u
    (φ ((Ideal.Quotient.mk I) (momentCoordinate K n k))) hprim
  convert hh using 2
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end
end CCDN
