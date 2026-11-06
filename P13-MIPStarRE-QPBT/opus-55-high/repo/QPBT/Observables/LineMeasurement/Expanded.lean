module

public import QPBT.Observables.LineMeasurement.Projector

/-!
# Expanded line measurements

This module constructs the expanded line measurements by convolving a strategy
line measurement with the Pauli-register line projectors, and records that the
result is a projective measurement whose effects vanish, on an axis-parallel
line, outside the embedded degree-`d` outcome space. It also introduces the
fine strategy--Pauli product measurement of which the expanded line
measurement is the addition postprocessing, and the evaluation-class and
point-effect families used by the consistency estimates.

## References

The declarations formalize `def:expanded-line-measurement`, whose paper
source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

variable {ι κ : Type*}

/-- The tensor placement of a zero left factor vanishes. -/
theorem heteroKron_zero_left (B : Op κ) :
    heteroKron (0 : Op ι) B = 0 := by
  unfold heteroKron
  simp

/-- The tensor placement of a zero right factor vanishes. -/
theorem heteroKron_zero_right (A : Op ι) :
    heteroKron A (0 : Op κ) = 0 := by
  unfold heteroKron
  simp

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

variable (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)

/-- The line measurement of a projective strategy is again projective: folding
the answers of a line question into a coefficient list is a postprocessing, and
postprocessing preserves projectivity. This is the line analogue of the point
measurement projectivity; both follow because postprocessing preserves
projectivity. The line form is what the projectivity assertion of
`def:expanded-line-measurement` needs, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem lineMeas_isProjective :
    MIPStarRE.QPBT.Measurement.IsProjective (S.lineMeas side W line) := by
  apply SandwichProduct.postprocess_isProjective
  cases side with
  | alice => exact S.isProjective.1 _
  | bob => exact S.isProjective.2 _

/-- On an axis-parallel line, strategy line effects vanish outside the
embedded degree-`d` subspace: every prescribed answer is a degree-`d`
coefficient list padded by zero. This is the strategy half of the last
assertion of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem lineMeas_effect_eq_zero_of_axis (haxis : line.kind = .axis) (f : DegPoly P.toLdParams (P.m * P.d))
    (hf : ¬ f.FitsDegree P.d) :
    (S.lineMeas side W line).effect f = 0 := by
  cases line with
  | diagonal base seed direction baseFixed prefixZero =>
      simp_all [LineDesc.kind]
  | axis base seed baseFixed =>
      unfold lineMeas
      apply Finset.sum_eq_zero
      intro a ha
      exfalso
      apply hf
      rw [← (Finset.mem_filter.mp ha).2]
      intro i hi
      have hi' : ¬ i.val < P.d + 1 := by omega
      cases a <;> simp [lineAnswerOrZero, DegPoly.padTo, hi']

/-- The convolution of a strategy line effect with the corresponding
Pauli-register line projector. This is the displayed definition of
`hat M^(Line,W),line_f`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def expLineOp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : DegPoly P.toLdParams (P.m * P.d)) : Op (S.ExpandedLocalSpace side) :=
  ∑ pair ∈ Finset.univ.filter
      (fun pair : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d) => pair.1 + pair.2 = f),
    heteroKron ((S.lineMeas side W line).effect pair.1)
      (tauLineProj P W line pair.2)

/-- Expanded line effects are positive semidefinite. This is the positivity
obligation of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem expLineOp_nonneg (f : DegPoly P.toLdParams (P.m * P.d)) :
    0 ≤ S.expLineOp side W line f :=
  Finset.sum_nonneg fun pair _ => Quantum.kronecker_nonneg
    ((S.lineMeas side W line).pos pair.1) (tauLineProj_nonneg P W line pair.2)

/-- Expanded line effects sum to the identity. This is the completeness
obligation of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem expLineOp_sum_eq_one :
    ∑ f, S.expLineOp side W line f = 1 := by
  let A : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
      Op (S.ExpandedLocalSpace side) := fun pair =>
    heteroKron ((S.lineMeas side W line).effect pair.1)
      (tauLineProj P W line pair.2)
  let g : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
      DegPoly P.toLdParams (P.m * P.d) := fun pair => pair.1 + pair.2
  calc
    (∑ f, S.expLineOp side W line f) =
        ∑ f, ∑ pair ∈ Finset.univ.filter (fun pair => g pair = f), A pair := rfl
    _ = ∑ pair, A pair := Finset.sum_fiberwise Finset.univ g A
    _ = heteroKron (∑ x, (S.lineMeas side W line).effect x)
        (∑ y, tauLineProj P W line y) := by
      rw [Fintype.sum_prod_type]
      exact (heteroKron_sum_sum _ _).symm
    _ = 1 := by
      rw [(S.lineMeas side W line).sum_eq_one, sum_tauLineProj_eq_one]
      exact heteroKron_one_one

/-- The concrete expanded line measurement exhibited in the proof of
`lem:qld-comm-line-cons`. Paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`, blueprint
`def:expanded-line-measurement`. -/
noncomputable def lineMeasExp (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams) :
    Measurement (DegPoly P.toLdParams (P.m * P.d))
      (S.ExpandedLocalSpace side) :=
  Measurement.ofSumEqOne (S.expLineOp side W line)
    (S.expLineOp_nonneg side W line) (S.expLineOp_sum_eq_one side W line)

/-- The effects of the expanded line measurement are the convolution
operators. -/
@[simp] theorem lineMeasExp_effect (f : DegPoly P.toLdParams (P.m * P.d)) :
    (S.lineMeasExp side W line).effect f = S.expLineOp side W line f := rfl



/-- An expanded line effect is idempotent: the strategy line projectors and
the Pauli line projectors are both orthogonal families, so distinct
convolution terms annihilate one another. This is the projectivity
calculation of `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem expLineOp_mul_self (f : DegPoly P.toLdParams (P.m * P.d)) :
    S.expLineOp side W line f * S.expLineOp side W line f =
      S.expLineOp side W line f := by
  have hM := S.lineMeas_isProjective side W line
  set s := Finset.univ.filter
    (fun pair : DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d) => pair.1 + pair.2 = f) with hs
  let K : DegPoly P.toLdParams (P.m * P.d) ×
      DegPoly P.toLdParams (P.m * P.d) → Op (S.ExpandedLocalSpace side) :=
    fun p => heteroKron ((S.lineMeas side W line).effect p.1)
      (tauLineProj P W line p.2)
  calc
    (∑ p ∈ s, K p) * (∑ q ∈ s, K q) = ∑ p ∈ s, ∑ q ∈ s, K p * K q := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ p ∈ s, ∑ q ∈ s, if q = p then K p else 0 := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [heteroKron_mul]
      by_cases hqp : q = p
      · subst hqp
        rw [if_pos rfl, (hM q.1).isIdempotentElem.eq,
          tauLineProj_mul_tauLineProj, if_pos rfl]
      · rw [if_neg hqp]
        by_cases h1 : p.1 = q.1
        · grind
        simp_all [DistanceCalculus.projective_effect_mul_effect_eq_zero, heteroKron_zero_left]
    _ = ∑ p ∈ s, K p := by
      simp

/-- The expanded line measurement is projective. This is the projectivity
assertion in `def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem lineMeasExp_isProjective :
    MIPStarRE.QPBT.Measurement.IsProjective (S.lineMeasExp side W line) := by
  intro f
  refine ⟨?_, ?_⟩
  · change S.expLineOp side W line f * S.expLineOp side W line f =
      S.expLineOp side W line f
    simp [expLineOp_mul_self]
  · change star (S.expLineOp side W line f) = S.expLineOp side W line f
    exact (Matrix.nonneg_iff_posSemidef.mp
      (S.expLineOp_nonneg side W line f)).isHermitian.eq

/-- On an axis line, expanded effects outside the embedded degree-`d` outcome
space vanish. This is the last assertion of
`def:expanded-line-measurement`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. -/
theorem expLineOp_zero_of_not_deg_d (haxis : line.kind = .axis) (f : DegPoly P.toLdParams (P.m * P.d))
    (hf : ¬ f.FitsDegree P.d) :
    S.expLineOp side W line f = 0 := by
  apply Finset.sum_eq_zero
  intro pair hpair
  have hsum := (Finset.mem_filter.mp hpair).2
  by_cases h1 : pair.1.FitsDegree P.d
  · have h2 : ¬ pair.2.FitsDegree P.d := by
      intro h2
      apply hf
      intro i hi
      rw [← hsum, Pi.add_apply, h1 i hi, h2 i hi, add_zero]
    simp_all [tauLineProj_eq_zero_of_axis, heteroKron_zero_right]
  · rw [S.lineMeas_effect_eq_zero_of_axis side W line haxis pair.1 h1,
      heteroKron_zero_left]

/-- Evaluation classes of the expanded line measurement, including the
explicit `none` class for a non-evaluating canonical line. This is the
completed bracket family used in item 3 of `lem:qld-comm-line-cons`, blueprint
`eq:qld-comm-line-pt-cons2`. -/
noncomputable def lineEvalMeasExp (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) :
    Measurement (Option (PauliScalar P)) (S.ExpandedLocalSpace side) :=
  (S.lineMeasExp side W line).postprocess (evalOpt line u)

/-- Complete an expanded point measurement with a zero `none` outcome. This
is the right-hand family in the corrected item 3 of
`lem:qld-comm-line-cons`, blueprint
`eq:qld-comm-line-pt-cons2`. -/
noncomputable def pointMeasExpOption (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    Measurement (Option (PauliScalar P)) (S.ExpandedLocalSpace side) :=
  (S.pointMeasExp side W u).postprocess some

end ProjectiveSetting

end

end MIPStarRE.QPBT
