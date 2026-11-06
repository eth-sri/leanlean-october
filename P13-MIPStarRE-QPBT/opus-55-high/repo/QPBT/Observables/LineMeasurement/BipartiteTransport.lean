module

public import QPBT.Observables.LineMeasurement.LinePointOverlap

/-!
# Bipartite estimates and transport for the expanded line measurements

This module collects the generic distance estimates used by items 2 and 3 of
the expanded-line consistency lemma, and the identities that transport the
placed families of the six-register expanded state to the two opposite-
placement bipartitions. The generic estimates are: the distance between two
oppositely placed complete measurements is at most twice the complement of
their diagonal overlap (`fact:agreement`), and a projective family compared
with itself followed by an effect selected through a coarse-graining is at
most as far as the coarse-grained families are from each other
(`fact:add-a-proj2` for a projective refinement). The transport identities
are formalization-only auxiliaries: they carry a relation between placed
operators on the six-register expanded state to the product shape in which the
generic estimates are stated, a step the source leaves implicit.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons` and `eq:qld-comm-line-pt-cons2`, and
the generic estimates `fact:agreement` and `fact:add-a-proj2` of
`blueprint/src/chapter/ch12_qpbt_games.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Generic bipartite estimates -/

namespace DistanceCalculus

/-- A projective effect is absorbed by the postprocessed effect of the fiber
containing its own outcome. Formalization-only auxiliary for the projective
refinement of `fact:add-a-proj2` used by `eq:qld-comm-line-pt-cons`. -/
theorem effect_mul_postprocess_effect_self {α β ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (g : α → β) (a : α) :
    M.effect a * (M.postprocess g).effect (g a) = M.effect a := by
  grind [SandwichProduct.effect_mul_postprocess_effect]

end DistanceCalculus

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## Transport between the six registers and the bipartitions -/

variable (S : ProjectiveSetting P ε) (X : Op (S.toStrategy.ιA × PauliRegister P)) (Y : Op (S.toStrategy.ιB × PauliRegister P))

set_option synthInstance.maxSize 400 in
/-- On the `AA' | BA''(B'B'')` bipartition, the overlap of left and right
tensor placements is the overlap of the `AA'` and `BA''` placements. -/
theorem stateQForm_aaBa_mul_eq :
    DistanceCalculus.stateQForm
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) *
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P)))) =
      DistanceCalculus.stateQForm S.psiHat (S.place .AA' X * S.place .BA'' Y) := by
  rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
    reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]

set_option synthInstance.maxSize 400 in
/-- On the `AB'' | BB'(A'A'')` bipartition, the overlap of left and right
tensor placements is the overlap of the `AB''` and `BB'` placements. -/
theorem stateQForm_abBb_mul_eq :
    DistanceCalculus.stateQForm
        (reindexState (abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat)
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) *
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P)))) =
      DistanceCalculus.stateQForm S.psiHat (S.place .AB'' X * S.place .BB' Y) := by
  rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul,
    reindexOp_abBbBipartition_left, reindexOp_abBbBipartition_right]

end ProjectiveSetting

end

end MIPStarRE.QPBT
