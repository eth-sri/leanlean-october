/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import CCDN.Algebra.BoundedLinearSeparation
import CCDN.Algebra.IntegralMinpolyDegree
import CCDN.Projection.IntegralProjectionFiberCount
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Sharp specialization-fiber bounds over a normal base. A single integral
linear combination separates a finite set of characteristic-zero points.
Its specialized monic minimal polynomial bounds the entire fiber by the
fraction-field rank, independently of the number of coordinates. -/

@[expose] public section
namespace CCDN
noncomputable section

open MvPolynomial

/-- In characteristic zero, every fiber of an integral projection of the variety of a prime `I`
by polynomials `l` has at most `[E : F]` points, where `F` is the fraction field of the polynomial
ring of the target and `E` is a finite extension of `F` receiving the coordinate ring of `I`. -/
theorem integral_projection_fiber_card_le_finrank
    {K σ τ : Type*} [Field K] [CharZero K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (l : τ → MvPolynomial σ K)
    [Algebra (MvPolynomial τ K) (MvPolynomial σ K ⧸ I)]
    (hmap : algebraMap (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) =
      (projectionCoordinateMap I l).toRingHom)
    (F E : Type*) [Field F] [Field E]
    [Algebra (MvPolynomial τ K) F] [IsFractionRing (MvPolynomial τ K) F]
    [Algebra (MvPolynomial τ K) E] [Algebra (MvPolynomial σ K ⧸ I) E]
    [Algebra F E]
    [IsScalarTower (MvPolynomial τ K) (MvPolynomial σ K ⧸ I) E]
    [IsScalarTower (MvPolynomial τ K) F E] [FiniteDimensional F E]
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (z : τ → K) (s : Finset (σ → K))
    (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ Module.finrank F E := by
  classical
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let a : σ → A := fun i => Ideal.Quotient.mk I (X i)
  let : Algebra R K := (aeval z).toRingHom.toAlgebra
  have ha (i) : IsIntegral R (a i) := by
    change (algebraMap R A).IsIntegralElem (a i); rw [hmap]; exact hint (a i)
  let e := (Fintype.equivFin σ).symm
  let v : s → Fin (Fintype.card σ) → K := fun x j => x.val (e j)
  have hv : Function.Injective v := fun x y h => Subtype.ext <| funext fun i => by
    obtain ⟨j, rfl⟩ := e.surjective i; exact congrFun h j
  obtain ⟨t, _, ht⟩ := exists_bounded_moment_separation v hv
  let b : A := ∑ j : Fin (Fintype.card σ), a (e j) * (t : A) ^ j.val
  let L : (σ → K) → K := fun x => ∑ j : Fin (Fintype.card σ), x (e j) * (t : K) ^ j.val
  have hb : IsIntegral R b :=
    IsIntegral.sum _ fun j _ => (ha (e j)).mul ((isIntegral_natCast t).pow j.val)
  have hL : Set.InjOn L s := fun x hx y hy hxy =>
    congrArg Subtype.val (ht (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  let P := (minpoly R b).map (algebraMap R K)
  have hP : P.Monic := (minpoly.monic hb).map _
  have hsub : s.image L ⊆ P.roots.toFinset := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨φ, hφ⟩ := exists_projection_fiber_specialization I l hmap z x (hzero x hx) (hproj x hx)
    have hφb : φ b = L x := by simp only [b, a, L, map_sum, map_mul, map_pow, map_natCast, hφ]
    refine Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP.ne_zero).mpr ?_)
    change P.eval (L x) = 0
    rw [← hφb]
    dsimp only [P]
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  calc
    s.card = (s.image L).card := (Finset.card_image_of_injOn hL).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' _
    _ ≤ (minpoly R b).natDegree := Polynomial.natDegree_map_le
    _ ≤ Module.finrank F E := integral_minpoly_natDegree_le_fraction_finrank R A F E b hb

end
end CCDN
