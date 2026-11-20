module

public import QPBT.Test.Completeness.Commutation

/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

/-- The Magic Square readouts have the prescribed answer form. -/
private theorem honestMagicMeasurement_effect_eq_zero (P : AdmissibleParams)
    (s : MsType) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.ms s) a = false) : (honestMagicMeasurement P s z).effect a = 0 := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · simp only [honestMagicMeasurement, hg, dite_true]
    refine deterministicMeasurement_effect_eq_zero_of_ne ?_
    rintro rfl
    cases s <;> simp [validPauliAnswer] at ha
  · cases s <;>
      simp only [honestMagicMeasurement, hg, dite_false, pauliMagicMeasurement,
        msStrategyMeasurement, Measurement.postprocess_comp] <;>
      refine SandwichProduct.postprocess_effect_eq_zero_of_notMem _ _ ?_ <;>
      rintro ⟨u, rfl⟩ <;> simp [pauliAnswerOfMs, validPauliAnswer] at ha

/-- The honest measurement supports only the answers prescribed by its type. -/
theorem honestMeasurement_effect_eq_zero_of_invalid (P : AdmissibleParams)
    (t : PauliType) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer t a = false) : (honestMeasurement P t z).effect a = 0 := by
  cases t
  case ms s => exact honestMagicMeasurement_effect_eq_zero P s z ha
  case pair =>
    classical
    by_cases hg : pauliPairGamma P z = 0
    · simp only [honestMeasurement, honestPairMeasurement, hg, dite_true]
      refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
      rintro ⟨u, rfl⟩
      simp [validPauliAnswer] at ha
    · simp only [honestMeasurement, honestPairMeasurement, hg, dite_false]
      refine deterministicMeasurement_effect_eq_zero_of_ne ?_
      rintro rfl
      simp [validPauliAnswer] at ha
  all_goals
    refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
    rintro ⟨u, rfl⟩
    simp [validPauliAnswer] at ha

/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

/-- Reading the low-degree register back from its embedding in the
basis-selected Pauli blocks returns the original vector; this is the coordinate
bookkeeping of `def:pauli-question-distribution`. -/
theorem pauliToLd_embedLd (P : AdmissibleParams) (W : PauliKind)
    (u : LdSpace P.toLdParams) : pauliToLd P W (embedLd P W u) = u := by
  funext i
  cases W <;> rcases i with (j | ⟨⟩) | j <;> rfl

section

variable (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P)

/-- The point block of a Point/W question is the point block of the ambient
coefficient vector; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_point :
    pauliPointBlock W (pauliCL P (.point W) z) = pauliPointBlock W z := by
  cases W <;> rfl

/-- The axis-line conditionally linear map of `def:ld-question-distribution` is
idempotent. -/
theorem ldALineCL_idempotent (L : LdParams) (w : LdSpace L) :
    ldALineCL L (ldALineCL L w) = ldALineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · exact congrFun (lineRepMap_apply_self
      (coordinateDirection (chiIndex L w.seed)) w.point) j
  · rfl
  · rfl

/-- The diagonal-line conditionally linear map of `def:ld-question-distribution`
is idempotent. -/
theorem ldDLineCL_idempotent (L : LdParams) (w : LdSpace L) :
    ldDLineCL L (ldDLineCL L w) = ldDLineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · change (lineRepMap (prefixProjection (chiIndex L w.seed)
        (prefixProjection (chiIndex L w.seed) w.direction))
          (lineRepMap (prefixProjection (chiIndex L w.seed) w.direction) w.point)) j =
      (lineRepMap (prefixProjection (chiIndex L w.seed) w.direction) w.point) j
    rw [prefixProjection_idempotent]
    exact congrFun (lineRepMap_apply_self _ _) j
  · rfl
  · change prefixProjection (chiIndex L w.seed)
        (prefixProjection (chiIndex L w.seed) w.direction) j =
      prefixProjection (chiIndex L w.seed) w.direction j
    rw [prefixProjection_idempotent]

/-- The low-degree register carried by an Axis-line/W question is already fixed
by the axis-line conditionally linear map; `def:pauli-question-distribution`. -/
theorem ldALineCL_pauliToLd_pauliCL_aline :
    ldALineCL P.toLdParams (pauliToLd P W (pauliCL P (.aline W) z)) =
      ldALineCL P.toLdParams (pauliToLd P W z) := by
  rw [show pauliToLd P W (pauliCL P (.aline W) z) =
      ldALineCL P.toLdParams (pauliToLd P W z) from pauliToLd_embedLd P W _,
    ldALineCL_idempotent]

/-- The low-degree register carried by a Diagonal-line/W question is already
fixed by the diagonal-line conditionally linear map;
`def:pauli-question-distribution`. -/
theorem ldDLineCL_pauliToLd_pauliCL_dline :
    ldDLineCL P.toLdParams (pauliToLd P W (pauliCL P (.dline W) z)) =
      ldDLineCL P.toLdParams (pauliToLd P W z) := by
  rw [show pauliToLd P W (pauliCL P (.dline W) z) =
      ldDLineCL P.toLdParams (pauliToLd P W z) from pauliToLd_embedLd P W _,
    ldDLineCL_idempotent]

/-- The base of the canonical axis-line description of an Axis-line/W question
is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem aLineDescOf_base_eq :
    (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.aline W) z) := by
  cases W <;> exact lineRepMap_apply_self _ _

/-- The direction of the canonical axis-line description of an Axis-line/W
question is the coordinate direction selected by the scalar block of that
question; `def:pauli-question-distribution`. -/
theorem aLineDescOf_direction_eq :
    (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).direction =
      coordinateDirection
        (chiIndex P.toLdParams (pauliScalarBlock (pauliCL P (.aline W) z))) := by rfl

/-- The direction of the canonical diagonal-line description of a
Diagonal-line/W question is the direction block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_direction_eq :
    (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).direction =
      pauliDirectionBlock (pauliCL P (.dline W) z) := prefixProjection_idempotent _ _

/-- The point block of a Diagonal-line/W question is the point coordinate of
the diagonal-line conditionally linear image; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_dline :
    pauliPointBlock W (pauliCL P (.dline W) z) =
      (ldDLineCL P.toLdParams (pauliToLd P W z)).point := by
  cases W <;> rfl

/-- The base of the canonical diagonal-line description of a Diagonal-line/W
question is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_base_eq :
    (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.dline W) z) := by
  rw [pauliPointBlock_pauliCL_dline]
  exact congrArg LdSpace.point (ldDLineCL_idempotent P.toLdParams (pauliToLd P W z))

end

/-! ### The honest measurements as coarse-grainings of one Pauli basis -/

section

variable (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P)
include P W z

/-- The honest Point/W measurement at a sampled Point/W question reports the
value of the low-degree encoding of the measured Pauli label at the point block
of the ambient vector. -/
theorem honestMeasurement_point_eq :
    honestSampleMeasurement P (.point W) z =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.value (lowDegreeEnc h (pauliPointBlock W z))) := by
  simp only [honestMeasurement, honestPointMeasurement, pauliPointBlock_pauliCL_point]

/-- The honest Axis-line/W measurement at a sampled Axis-line/W question reports
the degree-`d` restriction to the canonical line of the ambient vector. -/
theorem honestMeasurement_aline_eq :
    honestSampleMeasurement P (.aline W) z =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.alinePoly (restrictToAxisLine P.toLdParams
          (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  simp only [honestMeasurement, honestALineMeasurement, ldALineCL_pauliToLd_pauliCL_aline]

/-- The honest Diagonal-line/W measurement at a sampled Diagonal-line/W question
reports the degree-`m d` restriction to the canonical line of the ambient
vector. -/
theorem honestMeasurement_dline_eq :
    honestSampleMeasurement P (.dline W) z =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.dlinePoly (restrictToLine P.toLdParams
          (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  simp only [honestMeasurement, honestDLineMeasurement, ldDLineCL_pauliToLd_pauliCL_dline]

/-- The honest Pauli/W measurement reports the measured Pauli label itself. -/
theorem honestMeasurement_pauli_eq :
    honestSampleMeasurement P (.pauli W) z =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.pauliOutcome h) := rfl

/-- Pair/W reports the binary trace of the low-degree encoding of its label. -/
theorem honestMeasurement_pairW_eq :
    honestSampleMeasurement P (.pairW W) z =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.bit (pauliTraceBit P (pauliPointBlock W z) (pauliTraceFactor W z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

end

/-- Two honest measurements coarse-graining one Pauli basis measurement have
zero operator product at every rejected answer pair, because a single Pauli
label produces an accepted pair. -/
theorem placedBasis_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliQuestion P) (f g : PauliRegister P → PauliAnswer P)
    (hacc : ∀ h : PauliRegister P, pauliWinPredicate P x y (f h) (g h) = true)
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (placedPauliMeasurement (pauliBasisMeasurement W) f).effect a *
      (placedPauliMeasurement (pauliBasisMeasurement W) g).effect b = 0 := by
  refine placedPauliMeasurement_mul_eq_zero_of_incompatible _
    (fun h => pauliProj_isProj W h) f g a b ?_
  grind

/-! ### The consistency clauses along the incidence forms -/

section

variable (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (h : PauliRegister P)
include P W z h

/-- The honest Axis-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the axis-line clause of
`def:pauli-win-predicate`. -/
theorem honest_alinePointCondition :
    pauliAlinePointCondition P W (pauliCL P (.aline W) z) (pauliCL P (.point W) z)
      (restrictToAxisLine P.toLdParams
        (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h))
      (lowDegreeEnc h (pauliPointBlock W z)) := by
  intro t ht
  rw [pauliPointBlock_pauliCL_point] at ht
  have hkey := evalCoefficient_restrictToAxisLine_lowDegreeEncoding P.toLdParams
    (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z))) rfl h t
  rw [aLineDescOf_base_eq, aLineDescOf_direction_eq] at hkey
  rw [ht]
  assumption

/-- The honest Diagonal-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the diagonal-line clause of
`def:pauli-win-predicate`. -/
theorem honest_dlinePointCondition :
    pauliDlinePointCondition P W (pauliCL P (.dline W) z) (pauliCL P (.point W) z)
      (restrictToLine P.toLdParams
        (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h))
      (lowDegreeEnc h (pauliPointBlock W z)) := by
  intro t ht
  rw [pauliPointBlock_pauliCL_point] at ht
  have hkey := evalCoefficient_restrictToLine P.toLdParams
    (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
    (lowDegreeEncoding h)
    (polynomialOnLine_lowDegreeEncoding_natDegree_le P.toLdParams _ h) t
  have hkey2 := eval_polynomialOnLine P.toLdParams
    (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
    (lowDegreeEncoding h) t
  rw [dLineDescOf_base_eq, dLineDescOf_direction_eq] at hkey2
  rw [ht]
  exact hkey.trans hkey2

end

/-! ### Zero products along the incidence forms of the Pauli type graph -/

section

variable (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
include P W z a b

/-- Along the Point/Axis-line incidence form the honest measurements have zero
operator product at every rejected answer pair. -/
theorem honest_point_aline_rejected_mul
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.aline W, pauliCL P (.aline W) z) a b = false) :
    (honestSampleMeasurement P (.point W) z).effect a *
      (honestSampleMeasurement P (.aline W) z).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_aline_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simpa [pauliWinPredicate, validPauliAnswer] using honest_alinePointCondition P W z h

/-- Along the Point/Diagonal-line incidence form the honest measurements have
zero operator product at every rejected answer pair. -/
theorem honest_point_dline_rejected_mul
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.dline W, pauliCL P (.dline W) z) a b = false) :
    (honestSampleMeasurement P (.point W) z).effect a *
      (honestSampleMeasurement P (.dline W) z).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_dline_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simpa [pauliWinPredicate, validPauliAnswer] using honest_dlinePointCondition P W z h

/-- Along the Point/Pauli incidence form the honest measurements have zero
operator product at every rejected answer pair. -/
theorem honest_point_pauli_rejected_mul
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.pauli W, pauliCL P (.pauli W) z) a b = false) :
    (honestSampleMeasurement P (.point W) z).effect a *
      (honestSampleMeasurement P (.pauli W) z).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_pauli_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simp [pauliWinPredicate, validPauliAnswer, pauliPointPauliCondition, pauliPointBlock_pauliCL_point]

/-- A single Pauli label satisfies the point/Pair trace test in either basis. -/
theorem honest_point_pairW_rejected_mul
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.pairW W, pauliCL P (.pairW W) z) a b = false) :
    (honestSampleMeasurement P (.point W) z).effect a *
      (honestSampleMeasurement P (.pairW W) z).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_pairW_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  have hcond : pauliPointPairCondition P W (pauliCL P (.pairW W) z)
      (lowDegreeEnc h (pauliPointBlock W z))
      (pauliTraceBit P (pauliPointBlock W z) (pauliTraceFactor W z) h) := Or.inr rfl
  simpa [pauliWinPredicate, validPauliAnswer] using hcond

/-- The point/variable incidence has zero mass on rejected answers in either basis. -/
theorem honest_point_msVar_rejected_mul
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.ms (.var (selectedMsVar W)), pauliSharedProjection z) a b = false) :
    (honestSampleMeasurement P (.point W) z).effect a *
      (honestMagicMeasurement P (.var (selectedMsVar W)) (pauliSharedProjection z)).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.point W) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms (.var (selectedMsVar W))) b)).symm with hvb | hvb
  · have hz := honestMagicMeasurement_effect_eq_zero P _ (pauliSharedProjection z) hvb
    rw [hz, mul_zero]
  obtain ⟨u, rfl⟩ : ∃ u, a = PauliAnswer.value u := by
    cases a <;> first | exact ⟨_, rfl⟩ | simp [validPauliAnswer] at hva
  obtain ⟨β, rfl⟩ : ∃ c, b = PauliAnswer.bit c := by
    cases b <;> first | exact ⟨_, rfl⟩ | simp [validPauliAnswer] at hvb
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  · simp [pauliWinPredicate, validPauliAnswer, pauliPointVariableCondition, hg] at hrej
  · rw [honestMeasurement_point_eq, honestMagicMeasurement_var_eq_placedBasis P W _ hg]
    refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) _ _ hrej
    have hcond : pauliPointVariableCondition P W (pauliSharedProjection z) (selectedMsVar W)
        (lowDegreeEnc h (pauliPointBlock W z))
        (pauliTraceBit P (pauliPointBlock W (pauliSharedProjection z))
          (pauliTraceFactor W (pauliSharedProjection z)) h) := by
      cases W
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    simpa [pauliWinPredicate, validPauliAnswer] using hcond

end

/-! ### The Pair/W versus Pair incidence form -/

/-- The effect of a placed and injectively relabelled measurement of the Pauli
register at a relabelled outcome is the placed original effect. -/
theorem placedPauliMeasurement_effect_image {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P)
    (hf : Function.Injective f) (a : α) :
    (placedPauliMeasurement M f).effect (f a) =
      heteroKron (M.effect a) (1 : Op (ZMod 2)) := by
  rw [placedPauliMeasurement_effect_eq, SandwichProduct.postprocess_effect_of_injective _ _ hf]

/-- Along the Pair/W versus Pair incidence form the honest measurements have
zero operator product at every rejected answer pair: with a vanishing phase bit
the Pair effect is the product of the two Pair/W effects, and with a nonzero
phase bit every well-formed answer pair is accepted. -/
theorem honest_pairW_pair_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.pairW W, pauliCL P (.pairW W) z)
      (.pair, pauliCL P .pair z) a b = false) :
    (honestSampleMeasurement P (.pairW W) z).effect a *
      (honestSampleMeasurement P .pair z).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true
    (validPauliAnswer (P := P) (PauliType.pairW W) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true
    (validPauliAnswer (P := P) PauliType.pair b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨β, rfl⟩ : ∃ c, a = PauliAnswer.bit c := by
    cases a <;> simp_all [validPauliAnswer]
  obtain ⟨bits, rfl⟩ : ∃ c, b = PauliAnswer.pairBits c := by
    cases b <;> simp_all [validPauliAnswer]
  let q := pauliSharedProjection z
  change pauliWinPredicate P (.pairW W, q) (.pair, q) (.bit β) (.pairBits bits) = false at hrej
  have hcond := of_decide_eq_false hrej
  have hg : pauliPairGamma P q = 0 := by
    by_contra h
    exact hcond (.inl h)
  change (placedPauliMeasurement (pauliTraceReadout P W q) PauliAnswer.bit).effect _ *
    (honestPairMeasurement P q).effect _ = 0
  simp only [honestPairMeasurement, hg, dite_true]
  rw [placedPauliMeasurement_effect_image _ _ (by intro _ _ h; cases h; rfl),
    placedPauliMeasurement_effect_image _ _ (by intro _ _ h; cases h; rfl)]
  refine leftPlaced_mul_eq_zero ?_
  change (pauliTraceReadout P W q).effect β * pauliPairEffect P q bits = 0
  cases W
  · have hne : β ≠ bits.1 := fun h => hcond (.inr h.symm)
    rw [pauliPairEffect, ← mul_assoc,
      DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (pauliTraceMeasurement_projective P .X _ _) hne, zero_mul]
  · have hne : β ≠ bits.2 := fun h => hcond (.inr h.symm)
    rw [pauliPairEffect, ← mul_assoc,
      ← (pauliTraceMeasurement_effect_commute P q hg bits.1 β).eq, mul_assoc,
      DistanceCalculus.projective_effect_mul_effect_eq_zero _
        (pauliTraceMeasurement_projective P .Z _ _) hne, mul_zero]

/-! ### The Magic Square incidence forms -/

private theorem validMsAnswer_in_range {P : AdmissibleParams} {s : MsType} {a : PauliAnswer P}
    (h : validPauliAnswer (.ms s) a = true) : ∃ a', a = pauliAnswerOfMs a' := by
  cases a
  case msTriple β => exact ⟨.triple β, rfl⟩
  case bit β => exact ⟨.bit β, rfl⟩
  all_goals cases s <;> simp [validPauliAnswer] at h

/-- Along every edge of the Magic Square type graph the honest measurements have
zero operator product at every rejected answer pair: a vanishing phase bit makes
the decision predicate accept, and otherwise the honest measurements are the
relabelled Magic Square measurements of `thm:ms-from-ac`. -/
theorem honest_ms_rejected_mul (P : AdmissibleParams) (z : PauliSpace P)
    {s₁ s₂ : MsType} (hms : Sym2.mk s₁ s₂ ∈ msEdges) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.ms s₁, pauliCL P (.ms s₁) z)
      (.ms s₂, pauliCL P (.ms s₂) z) a b = false) :
    (honestSampleMeasurement P (.ms s₁) z).effect a *
      (honestSampleMeasurement P (.ms s₂) z).effect b = 0 := by
  classical
  let q := pauliSharedProjection z
  change pauliWinPredicate P (.ms s₁, q) (.ms s₂, q) a b = false at hrej
  change (honestMeasurement P (.ms s₁) q).effect a * (honestMeasurement P (.ms s₂) q).effect b = 0
  have hsupp : (s₁, s₂) ∈ msGameSymm.μ.support := by
    change (s₁, s₂) ∈ (Finset.univ : Finset (MsType × MsType)).filter
      (fun ab => Sym2.mk ab.1 ab.2 ∈ msEdges)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
  rcases (Bool.eq_false_or_eq_true
    (validPauliAnswer (P := P) (PauliType.ms s₁) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true
    (validPauliAnswer (P := P) (PauliType.ms s₂) b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨a', rfl⟩ := validMsAnswer_in_range hva
  obtain ⟨b', rfl⟩ := validMsAnswer_in_range hvb
  have ⟨hg, hmsrej⟩ : pauliPairGamma P q ≠ 0 ∧ msWinPredicate s₁ s₂ a' b' = false := by
    rcases msGame_support_incidence s₁ s₂ hsupp with
      ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;> cases a' <;> cases b' <;>
      simp_all [pauliWinPredicate, validPauliAnswer, pauliAnswerOfMs, msWinPredicate]
  change (honestMagicMeasurement P s₁ _).effect _ * (honestMagicMeasurement P s₂ _).effect _ = 0
  simp only [honestMagicMeasurement, hg, dite_false,
    SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective]
  let X := pauliTraceReadout P .X q
  let Z := pauliTraceReadout P .Z q
  have hX : Measurement.IsProjective X := pauliTraceMeasurement_projective P .X _ _
  have hZ : Measurement.IsProjective Z := pauliTraceMeasurement_projective P .Z _ _
  exact msStrategyMeasurement_rejected_mul_on_support _ _ _
    (msCellConstraintJoint_mul (obsOf X) (obsOf Z) (obsOf_conjTranspose X hX)
      (obsOf_conjTranspose Z hZ) (obsOf_sq X hX) (obsOf_sq Z hZ)
      (obsOf_pauliTraceMeasurement_anticommute P (pauliSharedProjection z) hg)) _ _ hsupp _ _ hmsrej

/-! ### Zero products along the oriented incidence forms -/

/-- Along every ordered incidence form of the Pauli type graph the honest
measurements have zero operator product at every rejected answer pair. -/
theorem honest_oriented_rejected_mul (P : AdmissibleParams) {t₁ t₂ : PauliType}
    (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (t₁, pauliCL P t₁ z) (t₂, pauliCL P t₂ z) a b = false) :
    (honestSampleMeasurement P t₁ z).effect a *
      (honestSampleMeasurement P t₂ z).effect b = 0 := by
  rcases h with ⟨W, rfl, hW⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hW with rfl | rfl | rfl | rfl
    · exact honest_point_aline_rejected_mul P W z a b hrej
    · exact honest_point_dline_rejected_mul P W z a b hrej
    · exact honest_point_pauli_rejected_mul P W z a b hrej
    · exact honest_point_pairW_rejected_mul P W z a b hrej
  · exact honest_pairW_pair_rejected_mul P W z a b hrej
  · exact honest_point_msVar_rejected_mul P .X z a b hrej
  · exact honest_point_msVar_rejected_mul P .Z z a b hrej

end

end MIPStarRE.QPBT
