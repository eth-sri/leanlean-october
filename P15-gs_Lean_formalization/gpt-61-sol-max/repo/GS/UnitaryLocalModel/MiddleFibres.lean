
import GS.UnitaryLocalModel.OuterFibres



/-!
# Exact fibres of the complex middle blocks

The coefficients are complex, but the common Pauli axis is real. Therefore the
only nonzero ambiguity is simultaneous interchange of the two middle matrices
and reversal of the sphere axis. The zero difference collapses the whole sphere.
-/
namespace GS.UnitaryLocalModel

noncomputable def realify {κ : Type*} : (κ → ℂ) →ₗ[ℝ] (κ × Fin 2 → ℝ) :=
  LinearMap.pi fun p =>
    (if p.2 = 0 then Complex.reLm else Complex.imLm).comp (LinearMap.proj p.1)

theorem realify_injective {κ : Type*} : Function.Injective (@realify κ) := by
  intro z w h
  funext j
  apply Complex.ext
  · simpa [realify] using congrFun h (j,0)
  · simpa [realify] using congrFun h (j,1)

variable (a b : ℂ)

def axisCoefficient (H : CMat 2) := ![H 0 0 - H 1 1, H 0 1 + H 1 0, Complex.I * (H 0 1 - H 1 0)]

theorem middleBlock_trace  (u : AxisVector) :
    Matrix.trace (middleBlock a b u) = a+b := by
  simp [Matrix.trace,Fin.sum_univ_two,middleBlock,pauli]
  ring

theorem middleBlock_axisCoefficient  (u : AxisVector) :
    axisCoefficient (middleBlock a b u) = fun i => (u i : ℂ) * (a-b) := by
  funext i
  fin_cases i <;> simp [axisCoefficient,middleBlock,pauli] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

end GS.UnitaryLocalModel
