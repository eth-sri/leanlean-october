/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! In characteristic zero, a plane relation with a transcendental first
coordinate has a nonzero derivative in the second coordinate. That derivative
is a proper section of degree at most d-1 of the source curve. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The derivative is a proper degree-(d-1) section when f generates the
projection kernel. This is the proposed common reconstruction cut. -/
theorem projection_derivative_proper {K τ : Type*} [Field K] [CharZero K] [Fintype τ]
    (I : Ideal (MvPolynomial τ K)) (a : Fin 2 → MvPolynomial τ K)
    (ha : ∀ i, (a i).totalDegree ≤ 1)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0)
    (hker : ∀ g, aeval a g ∈ I ↔ f ∣ g)
    (j k : Fin 2) (hjk : j ≠ k)
    (hj : Transcendental K ((Ideal.Quotient.mk I) (a j))) :
    aeval a (pderiv k f) ∉ I ∧
      (aeval a (pderiv k f)).totalDegree ≤ f.totalDegree - 1 := by
  /- A nonzero relation cannot omit the coordinate complementary to a
  transcendental coordinate. -/
  classical
  let ψ := projectionCoordinateMap I a
  have hz : ψ f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ((hker f).mpr (dvd_refl f))
  have ht : Transcendental K (ψ (X j)) := by
    change Transcendental K ((Ideal.Quotient.mk I) (aeval a (X j)))
    rwa [aeval_X]
  have hp : pderiv k f ≠ 0 := fun h0 => by
    have hk := notMem_vars_of_pderiv_eq_zero h0 fun n hn _ ↦ Nat.cast_ne_zero.mpr hn.ne'
    obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range f (fun _ : Unit => j)
      (Function.injective_of_subsingleton _) fun t ht => by
        have htk : t ≠ k := fun h => hk (h ▸ ht)
        exact ⟨(), by dsimp; omega⟩
    have he : ψ.comp (rename (fun _ : Unit => j)) = aeval (fun _ : Unit => ψ (X j)) :=
      MvPolynomial.algHom_ext fun _ => by simp
    have hi : Function.Injective (aeval (R := K) (fun _ : Unit => ψ (X j))) :=
      (algebraicIndependent_unique_type_iff (R := K) (x := fun _ : Unit => ψ (X j))).mpr ht
    have hzg : aeval (fun _ : Unit => ψ (X j)) g = 0 := by
      rw [← he]; change ψ (rename (fun _ : Unit => j) g) = 0; rwa [hg]
    have hg0 : g = 0 := hi (by simpa only [map_zero] using hzg)
    exact hf (by rw [← hg, hg0, map_zero])
  refine ⟨fun hbad => not_dvd_pderiv_of_pderiv_ne_zero hf hp ((hker _).mp hbad),
    (aeval_totalDegree_le a ha _).trans ?_⟩
  simpa only [one_mul] using pderiv_totalDegree_le f k

end
end CCDN
