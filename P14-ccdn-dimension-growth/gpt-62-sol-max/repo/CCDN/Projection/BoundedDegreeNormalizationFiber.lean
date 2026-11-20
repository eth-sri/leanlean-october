/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.FilteredHilbertPolynomial
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import CCDN.Projection.FilteredProjectionRank
import CCDN.Hilbert.LinearCoordinates
import CCDN.Algebra.BoundedLinearSeparation
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import CCDN.Projection.PrimitiveCoordinateField
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! A fiber of a linear normalization has at most the Hilbert multiplicity
many points, by the function-field degree bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem linear_normalization_fiber_card_le
    {K : Type*} [Field K] [CharZero K] {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hfg : HasFilteredGenerators I (projectionCoordinateMap I l))
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (z : Fin (m + 1) → K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
    (hproj : ∀ x ∈ s, ∀ i, eval x (l i) = z i) :
    s.card ≤ d := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let E := FractionRing A
  let η := IsScalarTower.toAlgHom K A E
  let R := projectionImageField (F := E) I l
  obtain ⟨hfinite, hrank⟩ := filtered_normalization_rank (F := E) I l hl hfg hi hdimdeg
  let P := MvPolynomial (Fin (m + 1)) K
  let ψ := projectionCoordinateMap I l
  let ρ := projectionFieldMap (F := E) I l
  let : Algebra P A := ψ.toRingHom.toAlgebra
  let : Algebra P R := ρ.toRingHom.toAlgebra
  let ag := (η.comp ψ).toRingHom.toAlgebra
  let : SMul P E := ag.toSMul
  let : IsScalarTower P A E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower P R E := IsScalarTower.of_algebraMap_eq (fun p => (coe_projectionFieldMap I l p).symm)
  have hρ : Function.Injective ρ := (RingHom.injective_iff_ker_eq_bot ρ.toRingHom).mpr <| by
    change RingHom.ker (projectionFieldMap (F := E) I l) = ⊥
    rw [projectionFieldMap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hi
  let : IsFractionRing P R := projectionImageField_isFractionRing I l ρ hρ (AlgHom.id K P) rfl
  obtain ⟨t, _, ht⟩ := exists_bounded_moment_separation (fun x : s => x.val) Subtype.val_injective
  let g := ∑ j : Fin n, X j * C ((t : K) ^ j.val)
  let b : A := Ideal.Quotient.mk I g
  have hb := hfg.isIntegral b
  let Q := minpoly P b
  have hm : Q.Monic := minpoly.monic hb
  have hdeg : Q.natDegree ≤ d := by
    rw [← hm.natDegree_map (algebraMap P R), ← minpoly.isIntegrallyClosed_eq_field_fractions R E hb]
    rw [← hrank]
    exact minpoly.natDegree_le _
  let L (x : Fin n → K) := eval x g
  have hL : Set.InjOn L s := by
    intro x hx y hy he
    apply congrArg Subtype.val (ht (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) ?_)
    simpa [L, g, map_sum] using he
  let q := Q.map (eval z)
  have hq : q.Monic := hm.map _
  have hroot (x : Fin n → K) (hx : x ∈ s) : L x ∈ q.roots := by
    let φ := Ideal.Quotient.liftₐ I (aeval x) (hzero x hx)
    have hφ : φ.comp ψ = aeval z := by
      ext i
      simp only [AlgHom.comp_apply, ψ, projectionCoordinateMap, aeval_X]
      change eval x (l i) = z i
      exact hproj x hx i
    have he := congrArg φ (minpoly.aeval P b)
    change φ.toRingHom (Q.eval₂ (algebraMap P A) b) = φ.toRingHom 0 at he
    rw [Polynomial.hom_eval₂, map_zero, show φ.toRingHom.comp (algebraMap P A) = eval z from
      congrArg AlgHom.toRingHom hφ] at he
    exact Polynomial.mem_roots hq.ne_zero |>.mpr (by rwa [Polynomial.IsRoot, Polynomial.eval_map])
  have hsub : s.image L ⊆ q.roots.toFinset := by grind
  rw [← Finset.card_image_of_injOn hL]
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (Polynomial.natDegree_map_le.trans hdeg)))

end
end CCDN
