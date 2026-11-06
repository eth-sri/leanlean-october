/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import CCDN.Determinant.PlaneSingularities
import CCDN.ForMathlib.MvPolynomialDerivative
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! In characteristic zero, a plane relation with a transcendental first
coordinate has a nonzero derivative in the second coordinate. That derivative
is a proper section of degree at most d-1 of the source curve. -/

namespace CCDN
section
open MvPolynomial

/-- A nonzero relation cannot omit the coordinate complementary to a
transcendental coordinate. -/
theorem plane_relation_pderiv_ne_zero {K A : Type*} [Field K] [CharZero K]
    [CommRing A] [Algebra K A] (ψ : MvPolynomial (Fin 2) K →ₐ[K] A)
    (f : MvPolynomial (Fin 2) K) (hf : f ≠ 0) (hzero : ψ f = 0)
    (j k : Fin 2) (hjk : j ≠ k) (hj : Transcendental K (ψ (X j))) :
    pderiv k f ≠ 0 := by
  intro hz
  have hk := notMem_vars_of_pderiv_eq_zero hz fun n hn _ ↦ Nat.cast_ne_zero.mpr hn.ne'
  have hvars : (f.vars : Set (Fin 2)) ⊆ Set.range (fun _ : Unit => j) := by grind
  obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range f (fun _ : Unit => j)
    (Function.injective_of_subsingleton _) hvars
  have he : ψ.comp (rename (fun _ : Unit => j)) = aeval (fun _ : Unit => ψ (X j)) := by aesop
  have hi :=
    (algebraicIndependent_unique_type_iff (x := fun _ : Unit => ψ (X j))).mpr hj
  have hz : aeval (fun _ : Unit => ψ (X j)) g = 0 := by
    rw [← he]
    change ψ (rename (fun _ => j) g) = 0
    grind
  have hg0 : g = 0 := hi (by grind)
  exact hf (by grind)

