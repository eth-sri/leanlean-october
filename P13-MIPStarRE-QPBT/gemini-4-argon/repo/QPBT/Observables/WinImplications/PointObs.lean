module

public import QPBT.Observables.WinImplications.FactorTransport

/-!
# Self-consistency of the strategy point observables

This module converts the trace-coarse-grained point consistency of item 1 of
`lem:qld-win-implications` into the observable relation
`eq:pts-obs-consistency` of `lem:qld-win-implications-obs`.

## References

The declarations support `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:294-308`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Linearity of the tensor placement -/

/-- The left tensor placement commutes with weighted finite sums. This is
formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem heteroKron_left_sum_smul {α ιA ιB : Type*} [Fintype α]
    (c : α → ℂ) (A : α → Op ιA) (B : Op ιB) :
    heteroKron (∑ a, c a • A a) B = ∑ a, c a • heteroKron (A a) B := by
  ext i j
  simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
    mul_assoc]

/-- The right tensor placement commutes with weighted finite sums. This is
formalization-only support for `lem:povm-to-obs`, blueprint
`ch14_qpbt_observables.tex:365-382`. -/
theorem heteroKron_right_sum_smul {α ιA ιB : Type*} [Fintype α]
    (c : α → ℂ) (A : Op ιA) (B : α → Op ιB) :
    heteroKron A (∑ a, c a • B a) = ∑ a, c a • heteroKron A (B a) := by
  ext i j
  simp only [heteroKron, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The binary phase character has unit modulus. Paper
`references/qpbt-paper/04_preliminaries.tex:1052-1081`. -/
theorem norm_phaseSign (t : ZMod 2) : ‖phaseSign t‖ = 1 := by
  by_cases ht : t = 0 <;> simp [phaseSign, ht]

/-! ## The point observable as a binary observable -/

/-- The strategy point observable of `def:strategy-observables` is the
binary observable of the trace-coarse-grained point measurement. Paper
`14_analysis_of_the_pauli_basis_test.tex:174-190,294-308`, blueprint
`ch14_qpbt_observables.tex:573-610`. -/
theorem pointObs_eq_traceMeas_obs {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)
    (r : PauliScalar P) (u : Fin P.m → PauliScalar P) :
    S.pointObs side W r u =
      ∑ b : ZMod 2, phaseSign b • (S.pointTraceMeas side W u r).effect b := by
  classical
  rw [ProjectiveSetting.pointObs]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun a : PauliScalar P => fixedBinTrace P.model (a * r))
    (t := (Finset.univ : Finset (ZMod 2)))
    (fun a _ => Finset.mem_univ _)
    (f := fun a => phaseSign (fixedBinTrace P.model (a * r)) •
      (S.pointMeas side W u).effect a)]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [ProjectiveSetting.pointTraceMeas,
    MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

/-! ## Trace-coarse-grained point self-consistency -/

/-! ## The observable consistency relation -/

end WinImplications

end

end MIPStarRE.QPBT
