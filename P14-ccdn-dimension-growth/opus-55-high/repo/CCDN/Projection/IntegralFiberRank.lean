/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Hilbert.LinearProjectionFiltration
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import CCDN.Algebra.BoundedLinearSeparation
import CCDN.Algebra.IntegralMinpolyDegree
import CCDN.Projection.IntegralProjectionFiberCount
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Sharp specialization-fiber bounds over a normal base. A single integral
linear combination separates a finite set of characteristic-zero points.
Its specialized monic minimal polynomial bounds the entire fiber by the
fraction-field rank, independently of the number of coordinates. -/

namespace CCDN
section

/-- Distinct specialization tuples are roots of one separating integral
element's minimal polynomial. Normality bounds its degree by the field rank. -/
theorem integral_coordinate_tuple_count_le_finrank
    (R A F E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Field F] [Field E]
    [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra R E] [Algebra A E] [Algebra F E]
    [IsScalarTower R A E] [IsScalarTower R F E]
    [FiniteDimensional F E]
    {k ι : Type*} [Field k] [CharZero k] [Algebra R k] [Fintype ι]
    (a : ι → A) (ha : ∀ i, IsIntegral R (a i))
    (s : Finset (ι → k))
    (hs : ∀ x ∈ s, ∃ φ : A →ₐ[R] k, ∀ i, φ (a i) = x i) :
    s.card ≤ Module.finrank F E := by
  classical
  let e := (Fintype.equivFin ι).symm
  let v : s → Fin (Fintype.card ι) → k := fun x j => x.val (e j)
  obtain ⟨t, _, ht⟩ := exists_bounded_moment_separation v (by
    intro x y h
    apply Subtype.ext
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j)
  let b : A := ∑ j : Fin (Fintype.card ι), a (e j) * t ^ j.val
  let L : (ι → k) → k := fun x =>
    ∑ j : Fin (Fintype.card ι), x (e j) * t ^ j.val
  have hb : IsIntegral R b :=
    IsIntegral.sum _ (fun j _ => (ha (e j)).mul ((isIntegral_natCast t).pow j.val))
  have hL : Set.InjOn L s := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (ht (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  let P := (minpoly R b).map (algebraMap R k)
  have hP : P.Monic := (minpoly.monic hb).map _
  have hroot : ∀ x ∈ s, L x ∈ P.roots := by
    intro x hx
    obtain ⟨φ, hφ⟩ := hs x hx
    have hφb : φ b = L x := by aesop
    apply Polynomial.mem_roots hP.ne_zero |>.mpr
    change P.eval (L x) = 0
    rw [← hφb]
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply,
      minpoly.aeval, map_zero]
  calc
    s.card = (s.image L).card := (Finset.card_image_of_injOn hL).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card (by grind)
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' _
    _ ≤ (minpoly R b).natDegree := Polynomial.natDegree_map_le
    _ ≤ Module.finrank F E :=
      integral_minpoly_natDegree_le_fraction_finrank R A F E b hb

open MvPolynomial

