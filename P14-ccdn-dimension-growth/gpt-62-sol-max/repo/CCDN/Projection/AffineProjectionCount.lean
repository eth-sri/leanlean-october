/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Height.Box
public import CCDN.Projection.ProjectionHeight
import CCDN.Hilbert.FilteredHilbertLinearity
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.BoundedLinearProjection
import CCDN.Projection.DerivativeReconstruction
import CCDN.Projection.ExceptionalCount
import CCDN.ForMathlib.MvPolynomial
import CCDN.ForMathlib.MvPolynomialDerivative

/-! Transfer the affine curve count through the bounded birational projection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- An integral affine curve of degree `d` has a bounded projection to an irreducible plane
curve of degree `d`, losing at most `d(d-1)` points. -/
theorem exists_plane_count_reduction {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasAffineCurveDegree I d) :
    ∃ f : MvPolynomial (Fin 2) ℚ, Irreducible f ∧ f.totalDegree = d ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
  classical
  have hdeg := show HasFilteredCurveDegree I d from hdegree
  have hdim := hdeg.dimension_degree hd
  obtain ⟨b, f, hb, hN, hP, hf⟩ := exists_bounded_birational_hypersurface_projection 0 n I d hdim
  let a := fun i => integerLinearForm (b i)
  let π := fun (z : Fin n → ℚ) i => eval z (a i)
  have ha (i) : (a i).totalDegree ≤ 1 := linearForm_totalDegree_le _
  obtain ⟨P, hQ, hrec⟩ := exists_projection_reconstruction I a ha hN.injective f
    hP.irreducible.ne_zero (hf.symm ▸ hdim) hP.ker_eq
  refine ⟨f, hP.irreducible, hf, fun B hB => ?_⟩
  let S := integralPoints (idealZeroLocus I) B
  let R := S.image rationalPoint
  let T := S.image (b *ᵥ ·)
  have hR : ∀ z ∈ R, z ∈ idealZeroLocus I := by
    rintro _ hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact (mem_integralPoints.mp hw).2
  have hcount := projection_card_le_image_add I d hdeg a ha (pderiv 0 f) P hQ hrec R hR
  change R.card ≤ (R.image π).card + _ at hcount
  have hπ (z : IntPoint n) : rationalPoint (b *ᵥ z) = π (rationalPoint z) :=
    (rationalPoint_integer_mulVec b z).trans (integer_mulVec_eq_eval b _)
  have hT : R.image π = T.image rationalPoint := by simp [R, T, Finset.image_image, Function.comp_def, hπ]
  rw [hT, Finset.card_image_of_injective _ (rationalPoint_injective 2),
    Finset.card_image_of_injective _ (rationalPoint_injective n)] at hcount
  have hsub : T ⊆ integralPoints (zeroLocus f) (projectionBoxFactor n d * B) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzbox, hzI⟩ := mem_integralPoints.mp hz
    let H := projectionEntryBound n d
    have hH : 0 ≤ H := (projectionEntryBound_one_le n d).trans' zero_le_one
    refine mem_integralPoints.mpr ⟨fun i => (integer_linear_map_box_bound b hH
      (fun i j => projectionEntryBound_le hd (hb i j)) z hzbox i).trans ?_, ?_⟩
    · unfold projectionBoxFactor
      gcongr
      exact le_add_of_nonneg_right zero_le_one
    · change eval (rationalPoint (b *ᵥ z)) f = 0
      rw [hπ]
      simpa only [eval_polynomial_coordinate_map] using hzI _ hP.aeval_mem
  exact hcount.trans (Nat.add_le_add (Finset.card_le_card hsub) (Nat.mul_le_mul_left _ (hf ▸ pderiv_totalDegree_le f 0)))

end
end CCDN
