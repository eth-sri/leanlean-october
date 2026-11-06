/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import CCDN.Noether.FormalBranchFaithful
import CCDN.Noether.PowerSeriesBaseChange
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! A faithful formal branch remains faithful after arbitrary field extension.
The construction is an embedding of the extended coordinate algebra
into power series over the extension field. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped TensorProduct

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
  let A := MvPolynomial (Fin 2) K ⧸ I
  let φ : A →ₐ[K] PowerSeries K := Ideal.Quotient.liftₐ I ψ fun a ha =>
    (hψ a).mpr (Ideal.mem_span_singleton.mp ha)
  have hφ : Function.Injective φ :=
    RingHom.lift_injective_of_ker_le_ideal _ _ fun a ha =>
      Ideal.mem_span_singleton.mpr ((hψ a).mp ha)
  let b := Module.Free.chooseBasis K A
  let Φ : L ⊗[K] A →ₐ[L] PowerSeries L :=
    AlgHom.liftEquiv K L A (PowerSeries L) ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp φ)
  refine Function.Injective.isDomain Φ.toRingHom ?_
  change Function.Injective (((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp φ).toLinearMap.liftBaseChange L)
  rw [LinearMap.liftBaseChange_injective_iff _ b]
  exact powerSeries_linearIndependent_map_of_linearIndependent (φ ∘ b)
    (b.linearIndependent.map' φ.toLinearMap (LinearMap.ker_eq_bot.mpr hφ))

end
end CCDN
