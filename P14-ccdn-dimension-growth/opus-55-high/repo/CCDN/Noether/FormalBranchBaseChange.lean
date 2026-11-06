/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import CCDN.Noether.FormalBranchFaithful
import CCDN.Noether.PowerSeriesBaseChange
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! A faithful formal branch remains faithful after arbitrary field extension.
The construction is an embedding of the extended coordinate algebra
into power series over the extension field. -/

namespace CCDN
noncomputable section
open scoped TensorProduct

section
variable {K L A : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K)

/-- Extend a power-series-valued algebra map by scalars. -/
def formalBranchBaseChange
    :
    L ⊗[K] A →ₐ[L] PowerSeries L :=
  AlgHom.liftEquiv K L A (PowerSeries L)
    ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp ψ)

/-- Scalar extension of a faithful formal branch is faithful. -/
theorem formalBranchBaseChange_injective
    (hψ : Function.Injective ψ) :
    Function.Injective (formalBranchBaseChange (L := L) ψ) := by
  let b := Module.Free.chooseBasis K A
  let φ := ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp ψ).toLinearMap
  change Function.Injective (φ.liftBaseChange L)
  rw [LinearMap.liftBaseChange_injective_iff φ b]
  exact powerSeries_linearIndependent_map_of_linearIndependent (ψ ∘ b)
    (b.linearIndependent.map' ψ.toLinearMap (LinearMap.ker_eq_bot.mpr hψ))

end

/-- The coordinate algebra of an irreducible plane curve with a smooth
rational point is a domain after every field extension. -/
theorem isDomain_tensor_plane_quotient_of_smooth_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    IsDomain (L ⊗[K] (MvPolynomial (Fin 2) K ⧸ Ideal.span {f})) := by
  obtain ⟨ψ, _, _, hψ⟩ := exists_faithful_formal_plane_branch f hf z j hz hj
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have hkill : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    exact (hψ a).mpr (Ideal.mem_span_singleton.mp ha)
  let φ := Ideal.Quotient.liftₐ I ψ hkill
  exact (formalBranchBaseChange_injective φ (by
    apply RingHom.lift_injective_of_ker_le_ideal
    intro a ha
    exact Ideal.mem_span_singleton.mpr ((hψ a).mp ha))).isDomain (formalBranchBaseChange φ)

