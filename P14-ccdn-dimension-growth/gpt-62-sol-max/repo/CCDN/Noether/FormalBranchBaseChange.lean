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
import Mathlib.LinearAlgebra.Dual.Lemmas
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

/-- Applying a base-field functional to a coefficient of a putative relation recovers a
relation over the original field. -/
private theorem powerSeries_linearIndependent_map {K L ι : Type*}
    [Field K] [Field L] [Algebra K L] (v : ι → PowerSeries K)
    (hv : LinearIndependent K v) :
    LinearIndependent L (fun i => PowerSeries.map (algebraMap K L) (v i)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent] at hv ⊢
  intro s
  refine Fintype.linearIndependent_iff.mpr fun w hw i => ?_
  by_contra hi
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero K hi
  apply hφ
  apply (Fintype.linearIndependent_iff.mp (hv s)) (φ ∘ w) _ i
  ext n
  have he := congrArg (fun p : PowerSeries L => φ (PowerSeries.coeff n p)) hw
  change φ (PowerSeries.coeff n _) = φ (PowerSeries.coeff n _) at he
  simp only [map_sum, map_zero, PowerSeries.coeff_smul, smul_eq_mul] at he ⊢
  have hmul (j : s) :
      φ (w j * PowerSeries.coeff n (PowerSeries.map (algebraMap K L) (v j))) =
        φ (w j) * PowerSeries.coeff n (v j) := by
    rw [PowerSeries.coeff_map]
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simpa only [map_sum, hmul, Function.comp_apply] using he

/-- Extend a power-series-valued algebra map by scalars. -/
private def formalBranchBaseChange {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K) :
    L ⊗[K] A →ₐ[L] PowerSeries L :=
  AlgHom.liftEquiv K L A (PowerSeries L)
    ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp ψ)

section

variable {K L A : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K)
  (hψ : Function.Injective ψ)
include K L A ψ hψ

/-- Scalar extension of a faithful formal branch is faithful. -/
private theorem formalBranchBaseChange_injective :
    Function.Injective (formalBranchBaseChange (L := L) ψ) := by
  let b := Module.Free.chooseBasis K A
  let φ := ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp ψ).toLinearMap
  change Function.Injective (φ.liftBaseChange L)
  rw [LinearMap.liftBaseChange_injective_iff φ b]
  exact powerSeries_linearIndependent_map (ψ ∘ b)
    (b.linearIndependent.map' ψ.toLinearMap (LinearMap.ker_eq_bot.mpr hψ))

/-- Any algebra admitting a faithful power-series branch stays a domain under
an arbitrary extension of its coefficient field. -/
private theorem isDomain_tensor_of_faithful_formal_branch : IsDomain (L ⊗[K] A) :=
  Function.Injective.isDomain (formalBranchBaseChange (L := L) ψ)
    (formalBranchBaseChange_injective ψ hψ)

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
  let I := Ideal.span {f}
  have hkill : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    exact (hψ a).mpr (Ideal.mem_span_singleton.mp ha)
  let φ := Ideal.Quotient.liftₐ I ψ hkill
  have hφ : Function.Injective φ := by
    apply RingHom.lift_injective_of_ker_le_ideal
    intro a ha
    exact Ideal.mem_span_singleton.mpr ((hψ a).mp ha)
  exact isDomain_tensor_of_faithful_formal_branch φ hφ

end
end CCDN
