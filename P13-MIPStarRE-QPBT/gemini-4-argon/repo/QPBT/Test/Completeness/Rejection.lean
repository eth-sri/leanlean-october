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

/-- The honest Point/W measurement assigns the zero effect to every answer that
is not a field value; part of the answer-format rejection clause of
`def:pauli-win-predicate`. -/
theorem honestPairMeasurement_effect_eq_zero (P : AdmissibleParams)
    (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer .pair a = false) :
    (honestPairMeasurement P z).effect a = 0 := by
  classical
  by_cases hg : pauliPairGamma P z = 0
  · rw [show honestPairMeasurement P z =
      placedPauliMeasurement (pauliPairMeasurement P z hg) PauliAnswer.pairBits by
      simp [honestPairMeasurement, hg]]
    refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
    rintro ⟨u, rfl⟩; simp [validPauliAnswer] at ha
  · rw [show honestPairMeasurement P z =
      deterministicMeasurement (V := HonestIndex P) (.pairBits (0, 0)) by
      simp [honestPairMeasurement, hg]]
    refine deterministicMeasurement_effect_eq_zero_of_ne ?_
    rintro rfl; simp [validPauliAnswer] at ha

theorem honestMagicMeasurement_effect_eq_zero (P : AdmissibleParams)
    (s : MsType) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer (.ms s) a = false) :
    (honestMagicMeasurement P s z).effect a = 0 := by
  classical
  cases s with
  | constraint i =>
      by_cases hg : pauliPairGamma P z = 0
      · simp only [honestMagicMeasurement, hg, dite_true]
        refine deterministicMeasurement_effect_eq_zero_of_ne ?_
        rintro rfl; simp [validPauliAnswer] at ha
      · simp only [honestMagicMeasurement, hg, dite_false, Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca := (Finset.mem_filter.mp hc).2
        cases c
        · exact absurd ha (by rw [← hca]; simp [pauliAnswerOfMs, validPauliAnswer])
        · refine msStrategyMeasurement_constraint_zero _ _ _ i ?_
          rintro ⟨ab, hab⟩; exact MsAnswer.noConfusion hab
  | var j =>
      by_cases hg : pauliPairGamma P z = 0
      · simp only [honestMagicMeasurement, hg, dite_true]
        refine deterministicMeasurement_effect_eq_zero_of_ne ?_
        rintro rfl; simp [validPauliAnswer] at ha
      · simp only [honestMagicMeasurement, hg, dite_false, Measurement.postprocess_effect]
        refine Finset.sum_eq_zero fun c hc => ?_
        have hca := (Finset.mem_filter.mp hc).2
        cases c
        · refine msStrategyMeasurement_var_zero _ _ _ j ?_
          rintro ⟨b, hb⟩; exact MsAnswer.noConfusion hb
        · exact absurd ha (by rw [← hca]; simp [pauliAnswerOfMs, validPauliAnswer])

theorem honestMeasurement_effect_eq_zero_of_invalid (P : AdmissibleParams)
    (t : PauliType) (z : PauliSpace P) {a : PauliAnswer P}
    (ha : validPauliAnswer t a = false) :
    (honestMeasurement P t z).effect a = 0 := by
  cases t with
  | pair => exact honestPairMeasurement_effect_eq_zero P z ha
  | ms s => exact honestMagicMeasurement_effect_eq_zero P s z ha
  | _ =>
    refine placedPauliMeasurement_effect_eq_zero_of_notMem _ _ ?_
    rintro ⟨u, rfl⟩; simp [validPauliAnswer] at ha

/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

theorem pauliToLd_embedLd (P : AdmissibleParams) (W : PauliKind)
    (u : LdSpace P.toLdParams) : pauliToLd P W (embedLd P W u) = u := by
  funext i; cases W <;> rcases i with (j | ⟨⟩) | j <;> rfl

theorem pauliPointBlock_pauliCL_point (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliPointBlock W (pauliCL P (.point W) z) = pauliPointBlock W z := by
  cases W <;> rfl

theorem ldALineCL_idempotent (L : LdParams) (w : LdSpace L) :
    ldALineCL L (ldALineCL L w) = ldALineCL L w := by
  funext i; rcases i with (j | ⟨⟩) | j
  · exact congrFun (lineRepMap_apply_self
      (coordinateDirection (chiIndex L w.seed)) w.point) j
  · rfl
  · rfl

theorem ldDLineCL_idempotent (L : LdParams) (w : LdSpace L) :
    ldDLineCL L (ldDLineCL L w) = ldDLineCL L w := by
  funext i; rcases i with (j | ⟨⟩) | j
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

theorem ldALineCL_pauliToLd_pauliCL_aline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    ldALineCL P.toLdParams (pauliToLd P W (pauliCL P (.aline W) z)) =
      ldALineCL P.toLdParams (pauliToLd P W z) := by
  rw [show pauliToLd P W (pauliCL P (.aline W) z) =
      ldALineCL P.toLdParams (pauliToLd P W z) from pauliToLd_embedLd P W _,
    ldALineCL_idempotent]

theorem ldDLineCL_pauliToLd_pauliCL_dline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    ldDLineCL P.toLdParams (pauliToLd P W (pauliCL P (.dline W) z)) =
      ldDLineCL P.toLdParams (pauliToLd P W z) := by
  rw [show pauliToLd P W (pauliCL P (.dline W) z) =
      ldDLineCL P.toLdParams (pauliToLd P W z) from pauliToLd_embedLd P W _,
    ldDLineCL_idempotent]

theorem aLineDescOf_base_eq (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.aline W) z) := by
  cases W <;> exact lineRepMap_apply_self _ _

theorem aLineDescOf_direction_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (aLineDescOf P.toLdParams
        (ldALineCL P.toLdParams (pauliToLd P W z))).direction =
      coordinateDirection
        (chiIndex P.toLdParams (pauliScalarBlock (pauliCL P (.aline W) z))) := by
  cases W <;> rfl

theorem dLineDescOf_direction_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).direction =
      pauliDirectionBlock (pauliCL P (.dline W) z) :=
  prefixProjection_idempotent _ _

theorem pauliPointBlock_pauliCL_dline (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    pauliPointBlock W (pauliCL P (.dline W) z) =
      (ldDLineCL P.toLdParams (pauliToLd P W z)).point := by
  cases W <;> rfl

theorem dLineDescOf_base_eq (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) :
    (dLineDescOf P.toLdParams
        (ldDLineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.dline W) z) := by
  rw [pauliPointBlock_pauliCL_dline]
  change lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction))
        (lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point) = _
  rw [prefixProjection_idempotent]
  exact lineRepMap_apply_self _ _

/-! ### The honest measurements as coarse-grainings of one Pauli basis -/

theorem honestMeasurement_point_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.point W) (pauliCL P (.point W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.value (lowDegreeEnc h (pauliPointBlock W z))) := by
  rw [honestMeasurement, honestPointMeasurement, pauliPointMeasurement,
    placedPauliMeasurement_postprocess_eq, pauliPointBlock_pauliCL_point]

theorem honestMeasurement_aline_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.aline W) (pauliCL P (.aline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.alinePoly (restrictToAxisLine P.toLdParams
          (aLineDescOf P.toLdParams (ldALineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  rw [honestMeasurement, honestALineMeasurement, pauliALineMeasurement,
    placedPauliMeasurement_postprocess_eq, ldALineCL_pauliToLd_pauliCL_aline]

theorem honestMeasurement_dline_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.dline W) (pauliCL P (.dline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.dlinePoly (restrictToLine P.toLdParams
          (dLineDescOf P.toLdParams (ldDLineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  rw [honestMeasurement, honestDLineMeasurement, pauliDLineMeasurement,
    placedPauliMeasurement_postprocess_eq, ldDLineCL_pauliToLd_pauliCL_dline]

theorem honestMeasurement_pauli_eq (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) :
    honestMeasurement P (.pauli W) (pauliCL P (.pauli W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.pauliOutcome h) := rfl

theorem honestMeasurement_pairW_X_eq (P : AdmissibleParams) (z : PauliSpace P) :
    honestMeasurement P (.pairW .X) (pauliCL P (.pairW .X) z) =
      placedPauliMeasurement (pauliBasisMeasurement .X)
        (fun h => PauliAnswer.bit
          (pauliTraceBit P (pauliXBlock z) (pauliRXBlock z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

theorem honestMeasurement_pairW_Z_eq (P : AdmissibleParams) (z : PauliSpace P) :
    honestMeasurement P (.pairW .Z) (pauliCL P (.pairW .Z) z) =
      placedPauliMeasurement (pauliBasisMeasurement .Z)
        (fun h => PauliAnswer.bit
          (pauliTraceBit P (pauliZBlock z) (pauliRZBlock z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

theorem placedBasis_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (x y : PauliQuestion P) (f g : PauliRegister P → PauliAnswer P)
    (hacc : ∀ h : PauliRegister P, pauliWinPredicate P x y (f h) (g h) = true)
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (placedPauliMeasurement (pauliBasisMeasurement W) f).effect a *
      (placedPauliMeasurement (pauliBasisMeasurement W) g).effect b = 0 := by
  refine placedPauliMeasurement_mul_eq_zero_of_incompatible _
    (fun h => pauliProj_isProj W h) f g a b fun h h1 h2 => ?_
  rw [← h1, ← h2, hacc h] at hrej
  exact Bool.noConfusion hrej

/-! ### The consistency clauses along the incidence forms -/

theorem honest_alinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (h : PauliRegister P) :
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
  rwa [ht]

theorem honest_dlinePointCondition (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (h : PauliRegister P) :
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
  rw [ht]; exact hkey.trans hkey2

/-! ### Zero products along the incidence forms of the Pauli type graph -/

theorem honest_point_aline_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.aline W, pauliCL P (.aline W) z) a b = false) :
    (honestMeasurement P (.point W) (pauliCL P (.point W) z)).effect a *
      (honestMeasurement P (.aline W) (pauliCL P (.aline W) z)).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_aline_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simpa [pauliWinPredicate, validPauliAnswer] using honest_alinePointCondition P W z h

theorem honest_point_dline_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.dline W, pauliCL P (.dline W) z) a b = false) :
    (honestMeasurement P (.point W) (pauliCL P (.point W) z)).effect a *
      (honestMeasurement P (.dline W) (pauliCL P (.dline W) z)).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_dline_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  simpa [pauliWinPredicate, validPauliAnswer] using honest_dlinePointCondition P W z h

theorem honest_point_pauli_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.pauli W, pauliCL P (.pauli W) z) a b = false) :
    (honestMeasurement P (.point W) (pauliCL P (.point W) z)).effect a *
      (honestMeasurement P (.pauli W) (pauliCL P (.pauli W) z)).effect b = 0 := by
  rw [honestMeasurement_point_eq, honestMeasurement_pauli_eq]
  refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
  have hcond : pauliPointPauliCondition P W (pauliCL P (.point W) z) h
      (lowDegreeEnc h (pauliPointBlock W z)) := by
    change lowDegreeEnc h (pauliPointBlock W (pauliCL P (.point W) z)) = _
    rw [pauliPointBlock_pauliCL_point]
  simpa [pauliWinPredicate, validPauliAnswer] using hcond

theorem honest_point_pairW_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.pairW W, pauliCL P (.pairW W) z) a b = false) :
    (honestMeasurement P (.point W) (pauliCL P (.point W) z)).effect a *
      (honestMeasurement P (.pairW W) (pauliCL P (.pairW W) z)).effect b = 0 := by
  cases W <;> {
    rw [honestMeasurement_point_eq]
    first | rw [honestMeasurement_pairW_X_eq] | rw [honestMeasurement_pairW_Z_eq]
    refine placedBasis_rejected_mul P _ _ _ _ _ (fun h => ?_) a b hrej
    simp [pauliWinPredicate, validPauliAnswer]
    exact Or.inr rfl }

theorem honest_point_msVar_X_rejected_mul (P : AdmissibleParams)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.point .X, pauliCL P (.point .X) z)
      (.ms (.var 0), pauliCL P (.ms (.var 0)) z) a b = false) :
    (honestMeasurement P (.point .X) (pauliCL P (.point .X) z)).effect a *
      (honestMeasurement P (.ms (.var 0)) (pauliCL P (.ms (.var 0)) z)).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.point .X) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms (.var 0)) b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨u, rfl⟩ : ∃ u, a = .value u := by
    cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [validPauliAnswer])
  obtain ⟨β, rfl⟩ : ∃ c, b = .bit c := by
    cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [validPauliAnswer])
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  · have hcond : pauliPointVariableCondition P .X (pauliCL P (.ms (.var 0)) z) 0 u β := Or.inl hg
    simp [pauliWinPredicate, validPauliAnswer, hcond] at hrej
  · rw [honestMeasurement_point_eq,
      show honestMeasurement P (.ms (.var 0)) (pauliCL P (.ms (.var 0)) z) = _ from
        (honestMagicMeasurement_var_eq_placedBasis P (pauliSharedProjection z) hg).1]
    refine placedBasis_rejected_mul P .X _ _ _ _ (fun h => ?_) _ _ hrej
    have hcond : pauliPointVariableCondition P .X (pauliCL P (.ms (.var 0)) z) 0
        (lowDegreeEnc h (pauliPointBlock PauliKind.X z))
        (pauliTraceBit P (pauliXBlock (pauliSharedProjection z))
          (pauliRXBlock (pauliSharedProjection z)) h) :=
      Or.inr (Or.inl ⟨by decide, rfl, rfl⟩)
    simpa [pauliWinPredicate, validPauliAnswer] using hcond

theorem honest_point_msVar_Z_rejected_mul (P : AdmissibleParams)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.point .Z, pauliCL P (.point .Z) z)
      (.ms (.var 4), pauliCL P (.ms (.var 4)) z) a b = false) :
    (honestMeasurement P (.point .Z) (pauliCL P (.point .Z) z)).effect a *
      (honestMeasurement P (.ms (.var 4)) (pauliCL P (.ms (.var 4)) z)).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.point .Z) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms (.var 4)) b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨u, rfl⟩ : ∃ u, a = .value u := by
    cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [validPauliAnswer])
  obtain ⟨β, rfl⟩ : ∃ c, b = .bit c := by
    cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [validPauliAnswer])
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  · have hcond : pauliPointVariableCondition P .Z (pauliCL P (.ms (.var 4)) z) 4 u β := Or.inl hg
    simp [pauliWinPredicate, validPauliAnswer, hcond] at hrej
  · rw [honestMeasurement_point_eq,
      show honestMeasurement P (.ms (.var 4)) (pauliCL P (.ms (.var 4)) z) = _ from
        (honestMagicMeasurement_var_eq_placedBasis P (pauliSharedProjection z) hg).2]
    refine placedBasis_rejected_mul P .Z _ _ _ _ (fun h => ?_) _ _ hrej
    have hcond : pauliPointVariableCondition P .Z (pauliCL P (.ms (.var 4)) z) 4
        (lowDegreeEnc h (pauliPointBlock PauliKind.Z z))
        (pauliTraceBit P (pauliZBlock (pauliSharedProjection z))
          (pauliRZBlock (pauliSharedProjection z)) h) :=
      Or.inr (Or.inr ⟨by decide, rfl, rfl⟩)
    simpa [pauliWinPredicate, validPauliAnswer] using hcond

/-! ### The Pair/W versus Pair incidence form -/

theorem placedPauliMeasurement_effect_image {P : AdmissibleParams}
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Measurement α (PauliRegister P)) (f : α → PauliAnswer P)
    (hf : Function.Injective f) (a : α) :
    (placedPauliMeasurement M f).effect (f a) =
      heteroKron (M.effect a) (1 : Op (ZMod 2)) := by
  rw [placedPauliMeasurement_effect_eq, SandwichProduct.postprocess_effect_of_injective _ _ hf]

theorem honest_pairW_pair_rejected_mul (P : AdmissibleParams) (W : PauliKind)
    (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.pairW W, pauliCL P (.pairW W) z)
      (.pair, pauliCL P .pair z) a b = false) :
    (honestMeasurement P (.pairW W) (pauliCL P (.pairW W) z)).effect a *
      (honestMeasurement P .pair (pauliCL P .pair z)).effect b = 0 := by
  classical
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.pairW W) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer .pair b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨β, rfl⟩ : ∃ c, a = .bit c := by
    cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [validPauliAnswer])
  obtain ⟨bits, rfl⟩ : ∃ c, b = .pairBits c := by
    cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [validPauliAnswer])
  have hacc (hc : pauliPairCondition P W (pauliCL P (.pairW W) z) β bits) : False := by
    simp [pauliWinPredicate, validPauliAnswer, hc] at hrej
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  · have h2 : (honestMeasurement P .pair (pauliCL P .pair z)).effect (.pairBits bits) =
        heteroKron ((pauliTraceMeasurement P .X (pauliXBlock (pauliSharedProjection z))
              (pauliRXBlock (pauliSharedProjection z))).effect bits.1 *
            (pauliTraceMeasurement P .Z (pauliZBlock (pauliSharedProjection z))
              (pauliRZBlock (pauliSharedProjection z))).effect bits.2)
          (1 : Op (ZMod 2)) := by
      rw [show honestMeasurement P .pair (pauliCL P .pair z) =
        placedPauliMeasurement (pauliPairMeasurement P (pauliSharedProjection z) hg) .pairBits by
        change honestPairMeasurement P (pauliSharedProjection z) = _
        simp [honestPairMeasurement, hg]]
      exact placedPauliMeasurement_effect_image _ _ (by intro; simp) bits
    rw [h2]
    cases W with
    | X =>
        dsimp only [honestMeasurement, honestPairWMeasurement, pauliCL, pauliPointBlock]
        rw [placedPauliMeasurement_effect_image _ PauliAnswer.bit (by intro; simp) β]
        refine leftPlaced_mul_eq_zero ?_
        rw [← mul_assoc, DistanceCalculus.projective_effect_mul_effect_eq_zero _
          (pauliTraceMeasurement_projective P .X _ _) (fun h => hacc (Or.inr h.symm)), zero_mul]
    | Z =>
        dsimp only [honestMeasurement, honestPairWMeasurement, pauliCL, pauliPointBlock]
        rw [placedPauliMeasurement_effect_image _ PauliAnswer.bit (by intro; simp) β]
        refine leftPlaced_mul_eq_zero ?_
        rw [← mul_assoc,
          ← (pauliTraceMeasurement_effect_commute P (pauliSharedProjection z) hg bits.1 β).eq,
          mul_assoc, DistanceCalculus.projective_effect_mul_effect_eq_zero _
            (pauliTraceMeasurement_projective P .Z _ _) (fun h => hacc (Or.inr h.symm)), mul_zero]
  · exact (hacc (Or.inl hg)).elim

/-! ### The Magic Square incidence forms -/

theorem honest_ms_rejected_mul (P : AdmissibleParams) (z : PauliSpace P)
    {s₁ s₂ : MsType} (hms : Sym2.mk s₁ s₂ ∈ msEdges) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (.ms s₁, pauliCL P (.ms s₁) z)
      (.ms s₂, pauliCL P (.ms s₂) z) a b = false) :
    (honestMeasurement P (.ms s₁) (pauliCL P (.ms s₁) z)).effect a *
      (honestMeasurement P (.ms s₂) (pauliCL P (.ms s₂) z)).effect b = 0 := by
  classical
  have hcl (s : MsType) : pauliCL P (.ms s) z = pauliSharedProjection z := rfl
  simp only [hcl] at hrej ⊢
  have hsupp : (s₁, s₂) ∈ msGameSymm.μ.support :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms s₁) a)).symm with hva | hva
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hva, zero_mul]
  rcases (Bool.eq_false_or_eq_true (validPauliAnswer (.ms s₂) b)).symm with hvb | hvb
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hvb, mul_zero]
  obtain ⟨a', rfl⟩ : ∃ c, a = pauliAnswerOfMs c := by
    cases a
    case msTriple β => exact ⟨.triple β, rfl⟩
    case bit c => exact ⟨.bit c, rfl⟩
    all_goals exact absurd hva (by cases s₁ <;> simp [validPauliAnswer])
  obtain ⟨b', rfl⟩ : ∃ c, b = pauliAnswerOfMs c := by
    cases b
    case msTriple β => exact ⟨.triple β, rfl⟩
    case bit c => exact ⟨.bit c, rfl⟩
    all_goals exact absurd hvb (by cases s₂ <;> simp [validPauliAnswer])
  have hpos (hor : pauliPairGamma P (pauliSharedProjection z) = 0 ∨
      msWinPredicate s₁ s₂ a' b' = true) :
      pauliWinPredicate P (.ms s₁, pauliSharedProjection z)
        (.ms s₂, pauliSharedProjection z) (pauliAnswerOfMs a') (pauliAnswerOfMs b') = true := by
    clear hrej
    rcases msGame_support_incidence s₁ s₂ hsupp with
      ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;>
      cases a' <;> cases b' <;> rcases hor with hg | hmsw <;>
      simp_all [pauliWinPredicate, validPauliAnswer, pauliAnswerOfMs, msWinPredicate]
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  · exact Bool.noConfusion (hrej.symm.trans (hpos (Or.inl hg)))
  · have hmsrej : msWinPredicate s₁ s₂ a' b' = false :=
      Bool.eq_false_iff.mpr fun hmsw => Bool.noConfusion (hrej.symm.trans (hpos (Or.inr hmsw)))
    have hM (s : MsType) : honestMeasurement P (.ms s) (pauliSharedProjection z) =
        (pauliMagicMeasurement P (pauliSharedProjection z) hg s).postprocess
          (pauliAnswerOfMs (P := P)) := by
      change honestMagicMeasurement P s (pauliSharedProjection z) = _
      simp [honestMagicMeasurement, hg]
    rw [hM s₁, hM s₂,
      SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective a',
      SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective b']
    exact msStrategyMeasurement_rejected_mul_on_support _ _ _
      (fun i k ab c => msCellConstraintJoint_mul _ _
        (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X _ _))
        (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z _ _))
        (obsOf_sq _ (pauliTraceMeasurement_projective P .X _ _))
        (obsOf_sq _ (pauliTraceMeasurement_projective P .Z _ _))
        (obsOf_pauliTraceMeasurement_anticommute P (pauliSharedProjection z) hg)
        i k ab c) s₁ s₂ hsupp a' b' hmsrej

/-! ### Zero products along the oriented incidence forms -/

theorem honest_oriented_rejected_mul (P : AdmissibleParams) {t₁ t₂ : PauliType}
    (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P) (a b : PauliAnswer P)
    (hrej : pauliWinPredicate P (t₁, pauliCL P t₁ z) (t₂, pauliCL P t₂ z) a b = false) :
    (honestMeasurement P t₁ (pauliCL P t₁ z)).effect a *
      (honestMeasurement P t₂ (pauliCL P t₂ z)).effect b = 0 := by
  rcases h with ⟨W, rfl, rfl | rfl | rfl | rfl⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact honest_point_aline_rejected_mul P W z a b hrej
  · exact honest_point_dline_rejected_mul P W z a b hrej
  · exact honest_point_pauli_rejected_mul P W z a b hrej
  · exact honest_point_pairW_rejected_mul P W z a b hrej
  · exact honest_pairW_pair_rejected_mul P W z a b hrej
  · exact honest_point_msVar_X_rejected_mul P z a b hrej
  · exact honest_point_msVar_Z_rejected_mul P z a b hrej

end

end MIPStarRE.QPBT
