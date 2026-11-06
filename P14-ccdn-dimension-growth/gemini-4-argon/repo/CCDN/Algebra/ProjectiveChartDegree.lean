/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
public import CCDN.Algebra.ProjectiveSection
public import CCDN.Hilbert.AffineCurveDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Height.ProjectiveZeroLocus

/-! The affine chart of a projective coordinate domain, constructed from
coordinate ratios in a field. Its filtered Hilbert function agrees exactly
with the homogeneous Hilbert function before dehomogenization. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Given a `K`-algebra map `q` from the coordinate ring of `I` to a field `F`, the
`K`-algebra map from polynomials in the affine coordinates to `F` sending `Xⱼ` to the ratio
`q Xⱼ₊₁ / q X₀`. -/
def projectiveChartCoordinateMap {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F) :
    MvPolynomial (Fin n) K →ₐ[K] F :=
  aeval (fun j => q ((Ideal.Quotient.mk I) (X j.succ)) / q ((Ideal.Quotient.mk I) (X 0)))

/-- When `q X₀ ≠ 0`, the coordinate-ratio map sends the dehomogenization of a homogeneous
polynomial `f` of degree `M` to `(q X₀)⁻¹ ^ M * q f`. -/
lemma projectiveChartCoordinateMap_chart {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n M : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (q : (MvPolynomial (Fin (n + 1)) K ⧸ I) →ₐ[K] F)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    projectiveChartCoordinateMap I q (affineChart n f) =
      (q ((Ideal.Quotient.mk I) (X 0)))⁻¹ ^ M * q ((Ideal.Quotient.mk I) f) := by
  /- A homogeneous polynomial of degree `d` satisfies `f(a • v) = a ^ d * f(v)` for evaluations in
  any field `F` that is a `K`-algebra. -/
  let v : Fin (n + 1) → F := fun j => q ((Ideal.Quotient.mk I) (X j))
  have he : aeval v = q.comp (Ideal.Quotient.mkₐ K I) := MvPolynomial.algHom_ext fun j => by simp [v]
  have hnorm : Fin.cons 1 (fun j => v j.succ / v 0) = (v 0)⁻¹ • v :=
    funext fun j => Fin.cases (by simp [v, h0]) (fun k => by simp [div_eq_mul_inv, mul_comm]) j
  change aeval (fun j => v j.succ / v 0) (affineChart n f) = _
  have hsmul : aeval ((v 0)⁻¹ • v) f = (v 0)⁻¹ ^ M * aeval v f := by
    change eval₂ (algebraMap K F) ((v 0)⁻¹ • v) f = (v 0)⁻¹ ^ M * eval₂ (algebraMap K F) v f
    rw [← eval_map, ← eval_map]
    exact homogeneous_eval_smul (hf.map _) (v 0)⁻¹ v
  rw [show aeval (fun j => v j.succ / v 0) (affineChart n f) =
      aeval (Fin.cons 1 (fun j => v j.succ / v 0)) f by
    change eval₂ (algebraMap K F) _ (affineChart n f) = eval₂ (algebraMap K F) _ f
    rw [← eval_map, ← affineChart_map, affineChart_eval, eval_map],
    hnorm, hsmul, he]
  rfl

/-- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. If `I` defines a
projective curve of degree `d`, then the kernel of the coordinate-ratio map
`projectiveChartCoordinateMap I q` defines an affine curve of degree `d`. -/
theorem projective_chart_degree {F : Type*} [Field F] [Algebra ℚ F] {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (q : (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) →ₐ[ℚ] F) (hq : Function.Injective q)
    (h0 : q ((Ideal.Quotient.mk I) (X 0)) ≠ 0)
    (hdegree : HasProjectiveCurveDegree I d) :
    HasAffineCurveDegree (RingHom.ker (projectiveChartCoordinateMap I q)) d := by
  /- Let `q` embed the coordinate ring of `I` into a field with `q X₀ ≠ 0`. In every degree `M`,
  the filtered Hilbert function of the kernel of the coordinate-ratio map
  `projectiveChartCoordinateMap I q` equals the homogeneous Hilbert function of `I`. -/
  obtain ⟨N, c, hN⟩ := hdegree
  refine ⟨N, c, fun M hM => ?_⟩
  let ψ := projectiveChartCoordinateMap I q
  let η := Ideal.kerLiftAlg ψ
  let V := homogeneousCoordinateSpace I M
  let W := filteredCoordinateSpace (RingHom.ker ψ) M
  let φ : (MvPolynomial (Fin (n + 1)) ℚ ⧸ I) →ₗ[ℚ] F :=
    (LinearMap.mulLeft ℚ ((q ((Ideal.Quotient.mk I) (X 0)))⁻¹ ^ M)).comp q.toLinearMap
  have hφ : Function.Injective φ := fun x y h =>
    hq (mul_left_cancel₀ (pow_ne_zero _ (inv_ne_zero h0)) h)
  have himage : V.map φ = W.map η.toLinearMap := by
    ext x
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨(Ideal.Quotient.mk (RingHom.ker ψ)) (affineChart n f),
        ⟨affineChart n f, (mem_restrictTotalDegree _ _ _).mpr
          ((affineChart_totalDegree_le f).trans hf.totalDegree_le), rfl⟩,
        projectiveChartCoordinateMap_chart I q h0 f hf⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      have h := projectiveChartCoordinateMap_chart I q h0 (scaledHomogenize M 1 f)
        (scaledHomogenize_homogeneous 1 f ((mem_restrictTotalDegree _ _ _).mp hf))
      rw [affineChart_scaledHomogenize_one] at h
      exact ⟨(Ideal.Quotient.mk I) (scaledHomogenize M 1 f),
        ⟨scaledHomogenize M 1 f,
          scaledHomogenize_homogeneous 1 f ((mem_restrictTotalDegree _ _ _).mp hf), rfl⟩,
        h.symm⟩
  have hV := (Submodule.equivMapOfInjective φ hφ V).finrank_eq
  have hW :=
    (Submodule.equivMapOfInjective η.toLinearMap (Ideal.kerLiftAlg_injective ψ) W).finrank_eq
  rw [himage] at hV
  change (Module.finrank ℚ W : ℤ) = _
  rw [hW.trans hV.symm]
  exact hN M hM

end
end CCDN
