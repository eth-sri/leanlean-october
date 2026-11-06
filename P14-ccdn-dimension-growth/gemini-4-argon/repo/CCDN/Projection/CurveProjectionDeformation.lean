/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.LinearProjectionFiltration
public import CCDN.Plane.LinearDeformation
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import CCDN.Algebra.PolynomialFamilyRelations
import CCDN.Projection.PlaneProjectionDegree
import Mathlib.Algebra.MvPolynomial.Monad

/-! Construct a polynomial family of plane relations for linear
projections of a prime affine curve. The relation has degree at most the
curve's Hilbert degree and remains nonzero at parameter zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every bounded-degree linear displacement has a nonzero plane relation.
The relations can be chosen polynomially in the displacement parameter and
with a nonzero specialization at zero. -/
theorem exists_curve_projection_relation_family {K τ : Type*}
    [Field K] [CharZero K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime]
    (a : Fin 2 → MvPolynomial τ K) (ha : ∀ i, (a i).totalDegree ≤ 1)
    (d : ℕ) (hdegree : HasFilteredCurveDegree I d)
    (hu : Transcendental K ((Ideal.Quotient.mk I) (a 0)))
    (l : MvPolynomial τ K) (hl : l.totalDegree ≤ 1) :
    let V := restrictTotalDegree (Fin 2) K d
    let b := Module.finBasis K V
    ∃ v : Fin (Module.finrank K V) → Polynomial K,
      (∑ j, (v j).map (algebraMap K (MvPolynomial τ K ⧸ I)) *
        planeLinearDeformation (fun i => (Ideal.Quotient.mk I) (a i)) 1
          ((Ideal.Quotient.mk I) l) (b j).val) = 0 ∧
      ∃ j, (v j).eval 0 ≠ 0 := by
  classical
  let V := restrictTotalDegree (Fin 2) K d
  let b := Module.finBasis K V
  let ψ := planeLinearDeformation (K := K) (fun i => (Ideal.Quotient.mk I) (a i)) 1
    ((Ideal.Quotient.mk I) l)
  let g := fun j => ψ (b j).val
  refine polynomial_family_relation_nonzero_at_zero g fun k => ?_
  let aT : Fin 2 → MvPolynomial τ K := ![a 0, a 1 + (k : K) • l]
  have hat (i : Fin 2) : (aT i).totalDegree ≤ 1 := by
    fin_cases i
    · exact ha 0
    · exact (totalDegree_add (a 1) ((k : K) • l)).trans
        (max_le (ha 1) ((totalDegree_smul_le _ _).trans hl))
  obtain ⟨p, hp, _, hpd, hkernel⟩ := exists_plane_projection_equation_degree_le
    I aT hat d hdegree 0 hu
  have hpzero : projectionCoordinateMap I aT p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ((hkernel p).mpr (dvd_refl p))
  let pV : V := ⟨p, (mem_restrictTotalDegree _ _ _).mpr hpd⟩
  let c := fun j => b.repr pV j
  have hc : c ≠ 0 := fun hzero => hp.ne_zero <| congrArg Subtype.val
    (show pV = 0 from b.repr.injective <| Finsupp.ext fun j => by
      simpa only [map_zero, Finsupp.zero_apply, Pi.zero_apply] using congrFun hzero j)
  have hs : ∑ j, c j • (b j).val = p := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using congrArg Subtype.val (b.sum_repr pV)
  refine ⟨c, hc, ?_⟩
  let E : Polynomial (MvPolynomial τ K ⧸ I) →ₐ[K] (MvPolynomial τ K ⧸ I) :=
    (Polynomial.aeval (algebraMap K (MvPolynomial τ K ⧸ I) (k : K))).restrictScalars K
  have he : E.comp ψ = projectionCoordinateMap I aT :=
    MvPolynomial.algHom_ext fun i => by
      fin_cases i
      · simp [E, ψ, aT, planeLinearDeformation, projectionCoordinateMap]
      · simp [E, ψ, aT, planeLinearDeformation, projectionCoordinateMap, Algebra.smul_def]; ring
  have hev (j : Fin (Module.finrank K V)) : (g j).eval (k : MvPolynomial τ K ⧸ I) =
      projectionCoordinateMap I aT (b j).val := by
    simpa [E, g, ψ, Polynomial.aeval_def] using congrArg (fun φ => φ (b j).val) he
  simp only [hev, ← map_smul, ← map_sum, hs, hpzero]

end
end CCDN
