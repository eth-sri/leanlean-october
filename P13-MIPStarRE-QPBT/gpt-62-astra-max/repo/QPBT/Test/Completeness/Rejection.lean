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

section

variable (L : LdParams) (P : AdmissibleParams) (W : PauliKind) (s : MsType) (t : PauliType)
  (w : LdSpace L) (z : PauliSpace P) {a : PauliAnswer P}

/-- The honest measurement family assigns the zero effect to every answer whose
form is not the one prescribed by its question type; this is the
answer-format rejection clause of `def:pauli-win-predicate`, blueprint
`def:pauli-win-predicate`. -/
theorem honestMeasurement_effect_eq_zero_of_invalid
    (ha : validPauliAnswer t a = false) :
    (honestMeasurement t z).effect a = 0 := by
  classical
  cases t with
  | pair =>
    by_cases hg : pauliPairGamma P z = 0
    · simp only [honestMeasurement, honestPairMeasurement, dif_pos hg]
      apply placedPauliMeasurement_effect_eq_zero_of_notMem
      rintro ⟨_, rfl⟩; cases ha
    · simp only [honestMeasurement, honestPairMeasurement, dif_neg hg]
      apply deterministicMeasurement_effect_eq_zero_of_ne
      rintro rfl; cases ha
  | ms s =>
    by_cases hg : pauliPairGamma P z = 0
    · simp only [honestMeasurement, honestMagicMeasurement, dif_pos hg]
      apply deterministicMeasurement_effect_eq_zero_of_ne
      rintro rfl; cases s <;> cases ha
    · simp only [honestMeasurement, honestMagicMeasurement, dif_neg hg, Measurement.postprocess_effect]
      refine Finset.sum_eq_zero fun c hc => ?_
      have he := (Finset.mem_filter.mp hc).2
      subst a
      cases s <;> cases c <;> first | rfl | cases ha
  | _ =>
    apply placedPauliMeasurement_effect_eq_zero_of_notMem
    rintro ⟨_, rfl⟩; cases ha

private theorem honest_mul_of_valid {P : AdmissibleParams} {t₁ t₂ : PauliType}
    {z₁ z₂ : PauliSpace P} {a b : PauliAnswer P}
    (h : validPauliAnswer t₁ a = true → validPauliAnswer t₂ b = true →
      (honestMeasurement t₁ z₁).effect a * (honestMeasurement t₂ z₂).effect b = 0) :
    (honestMeasurement t₁ z₁).effect a * (honestMeasurement t₂ z₂).effect b = 0 := by
  cases ha : validPauliAnswer t₁ a
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ ha, zero_mul]
  cases hb : validPauliAnswer t₂ b
  · rw [honestMeasurement_effect_eq_zero_of_invalid P _ _ hb, mul_zero]
  exact h ha hb

/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

/-- Reading the low-degree register back from its embedding in the
basis-selected Pauli blocks returns the original vector; this is the coordinate
bookkeeping of `def:pauli-question-distribution`. -/
theorem pauliToLd_embedLd
    (u : LdSpace P.toLdParams) : pauliToLd P W (embedLd P W u) = u := by
  funext i
  cases W <;> rcases i with (j | ⟨⟩) | j <;> rfl

/-- The point block of a Point/W question is the point block of the ambient
coefficient vector; `def:pauli-question-distribution`. -/
theorem pauliPointBlock_pauliCL_point :
    pauliPointBlock W (pauliCL P (.point W) z) = pauliPointBlock W z := by
  cases W <;> rfl

/-- The axis-line conditionally linear map of `def:ld-question-distribution` is
idempotent. -/
theorem ldALineCL_idempotent :
    ldALineCL L (ldALineCL L w) = ldALineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · exact congrFun (lineRepMap_apply_self
      (coordinateDirection (chiIndex L w.seed)) w.point) j
  all_goals rfl

/-- The diagonal-line conditionally linear map of `def:ld-question-distribution`
is idempotent. -/
theorem ldDLineCL_idempotent :
    ldDLineCL L (ldDLineCL L w) = ldDLineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · change (lineRepMap (prefixProjection (chiIndex L w.seed)
        (prefixProjection (chiIndex L w.seed) w.direction))
          (lineRepMap (prefixProjection (chiIndex L w.seed) w.direction) w.point)) j =
      _
    rw [prefixProjection_idempotent]
    solve_by_elim [lineRepMap_apply_self]
  · rfl
  · change prefixProjection (chiIndex L w.seed)
        (prefixProjection (chiIndex L w.seed) w.direction) j =
      prefixProjection (chiIndex L w.seed) w.direction j
    rw [prefixProjection_idempotent]

end

section

variable (P : AdmissibleParams) (W : PauliKind) (z : PauliSpace P) (h : PauliRegister P)

/-- The base of the canonical axis-line description of an Axis-line/W question
is the point block carried by that question;
`def:pauli-question-distribution`. -/
theorem aLineDescOf_base_eq :
    (aLineDescOf
        (ldALineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.aline W) z) := by
  cases W <;> exact lineRepMap_apply_self _ _

/-- The direction of the canonical diagonal-line description of a
Diagonal-line/W question is the direction block carried by that question;
`def:pauli-question-distribution`. -/
theorem dLineDescOf_direction_eq :
    (dLineDescOf
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
    (dLineDescOf
        (ldDLineCL P.toLdParams (pauliToLd P W z))).base =
      pauliPointBlock W (pauliCL P (.dline W) z) := by
  rw [pauliPointBlock_pauliCL_dline]
  change lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
        (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction))
        (lineRepMap (prefixProjection (chiIndex P.toLdParams (pauliToLd P W z).seed)
          (pauliToLd P W z).direction) (pauliToLd P W z).point) =
      _
  rw [prefixProjection_idempotent]
  apply lineRepMap_apply_self

/-! ### The honest measurements as coarse-grainings of one Pauli basis -/

/-- The honest Point/W measurement at a sampled Point/W question reports the
value of the low-degree encoding of the measured Pauli label at the point block
of the ambient vector. -/
theorem honestMeasurement_point_eq :
    honestMeasurement (.point W) (pauliCL P (.point W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.value (lowDegreeEnc h (pauliPointBlock W z))) := by
  have h1 : honestMeasurement (.point W) (pauliCL P (.point W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.value
          (lowDegreeEnc h (pauliPointBlock W (pauliCL P (.point W) z)))) :=
    placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W)
      _
      _
  rw [h1, pauliPointBlock_pauliCL_point]

/-- The honest Axis-line/W measurement at a sampled Axis-line/W question reports
the degree-`d` restriction to the canonical line of the ambient vector. -/
theorem honestMeasurement_aline_eq :
    honestMeasurement (.aline W) (pauliCL P (.aline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.alinePoly (restrictToAxisLine P.toLdParams
          (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  have h1 : honestMeasurement (.aline W) (pauliCL P (.aline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.alinePoly (restrictToAxisLine P.toLdParams
          (aLineDescOf (ldALineCL P.toLdParams
            (pauliToLd P W (pauliCL P (.aline W) z))))
          (lowDegreeEncoding h))) :=
    placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W)
      _
      _
  rw [h1, show pauliToLd _ _ (pauliCL _ (.aline _) _) = ldALineCL P.toLdParams (pauliToLd _ _ _) from pauliToLd_embedLd _ _ _, ldALineCL_idempotent]

/-- The honest Diagonal-line/W measurement at a sampled Diagonal-line/W question
reports the degree-`m d` restriction to the canonical line of the ambient
vector. -/
theorem honestMeasurement_dline_eq :
    honestMeasurement (.dline W) (pauliCL P (.dline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.dlinePoly (restrictToLine
          (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z)))
          (lowDegreeEncoding h))) := by
  have h1 : honestMeasurement (.dline W) (pauliCL P (.dline W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.dlinePoly (restrictToLine
          (dLineDescOf (ldDLineCL P.toLdParams
            (pauliToLd P W (pauliCL P (.dline W) z))))
          (lowDegreeEncoding h))) :=
    placedPauliMeasurement_postprocess_eq (pauliBasisMeasurement W)
      _
      _
  rw [h1, show pauliToLd _ _ (pauliCL _ (.dline _) _) = ldDLineCL P.toLdParams (pauliToLd _ _ _) from pauliToLd_embedLd _ _ _, ldDLineCL_idempotent]

/-- The honest Pauli/W measurement reports the measured Pauli label itself. -/
theorem honestMeasurement_pauli_eq :
    honestMeasurement (.pauli W) (pauliCL P (.pauli W) z) =
      placedPauliMeasurement (pauliBasisMeasurement W)
        (fun h => PauliAnswer.pauliOutcome h) := rfl

/-- The honest Pair/X measurement at a sampled Pair/X question reports the
binary trace of the low-degree encoding of the measured Pauli label. -/
theorem honestMeasurement_pairW_X_eq :
    honestMeasurement (.pairW .X) (pauliCL P (.pairW .X) z) =
      placedPauliMeasurement (pauliBasisMeasurement .X)
        (fun h => PauliAnswer.bit
          (pauliTraceBit (pauliXBlock z) (pauliRXBlock z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

/-- The honest Pair/Z measurement at a sampled Pair/Z question reports the
binary trace of the low-degree encoding of the measured Pauli label. -/
theorem honestMeasurement_pairW_Z_eq :
    honestMeasurement (.pairW .Z) (pauliCL P (.pairW .Z) z) =
      placedPauliMeasurement (pauliBasisMeasurement .Z)
        (fun h => PauliAnswer.bit
          (pauliTraceBit (pauliZBlock z) (pauliRZBlock z) h)) :=
  placedPauliMeasurement_postprocess_eq _ _ _

/-- Two honest measurements coarse-graining one Pauli basis measurement have
zero operator product at every rejected answer pair, because a single Pauli
label produces an accepted pair. -/
theorem placedBasis_rejected_mul
    (x y : PauliQuestion P) (f g : PauliRegister P → PauliAnswer P)
    (hacc : ∀ h : PauliRegister P, pauliWinPredicate P x y (f h) (g h) = true)
    (a b : PauliAnswer P) (hrej : pauliWinPredicate P x y a b = false) :
    (placedPauliMeasurement (pauliBasisMeasurement W) f).effect a *
      (placedPauliMeasurement (pauliBasisMeasurement W) g).effect b = 0 := by
  refine placedPauliMeasurement_mul_eq_zero_of_incompatible _
    (fun h => pauliProj_isProj W h) f g a b ?_
  grind

/-! ### The consistency clauses along the incidence forms -/

/-- The honest Axis-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the axis-line clause of
`def:pauli-win-predicate`. -/
theorem honest_alinePointCondition :
    pauliAlinePointCondition P W (pauliCL P (.aline W) z) (pauliCL P (.point W) z)
      (restrictToAxisLine P.toLdParams
        (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h))
      (lowDegreeEnc h (pauliPointBlock W z)) := by
  intro t ht
  rw [pauliPointBlock_pauliCL_point] at ht
  have hkey := evalCoefficient_restrictToAxisLine_lowDegreeEncoding P.toLdParams
    (aLineDescOf (ldALineCL P.toLdParams (pauliToLd P W z))) rfl h t
  simp [aLineDescOf_base_eq] at hkey
  rw [ht]
  exact hkey

/-- The honest Diagonal-line/W answer evaluates, at every line parameter of the
sampled point, to the honest Point/W value; this is the diagonal-line clause of
`def:pauli-win-predicate`. -/
theorem honest_dlinePointCondition :
    pauliDlinePointCondition P W (pauliCL P (.dline W) z) (pauliCL P (.point W) z)
      (restrictToLine
        (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z)))
        (lowDegreeEncoding h))
      (lowDegreeEnc h (pauliPointBlock W z)) := by
  intro t ht
  rw [pauliPointBlock_pauliCL_point] at ht
  have hkey2 := eval_polynomialOnLine
    (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z)))
    (lowDegreeEncoding h) t
  rw [dLineDescOf_base_eq, dLineDescOf_direction_eq] at hkey2
  rw [ht]
  exact (evalCoefficient_restrictToLine
    (dLineDescOf (ldDLineCL P.toLdParams (pauliToLd P W z)))
    (polynomialOnLine_lowDegreeEncoding_natDegree_le P.toLdParams _ h) t).trans hkey2

end

/-! ### Zero products along the incidence forms of the Pauli type graph -/

variable (P : AdmissibleParams) (W : PauliKind) {t₁ t₂ : PauliType}
  (h : PauliEdgeOriented t₁ t₂) (z : PauliSpace P) {s₁ s₂ : MsType}
  (hms : Sym2.mk s₁ s₂ ∈ msEdges) (a b : PauliAnswer P)

private theorem honest_point_msVar_rejected_mul
    (hrej : pauliWinPredicate P (.point W, pauliCL P (.point W) z)
      (.ms (.var (WinImplications.selectedMsVar W)), pauliCL P (.ms (.var (WinImplications.selectedMsVar W))) z) a b = false) :
    (honestMeasurement (.point W) (pauliCL P (.point W) z)).effect a *
      (honestMeasurement (.ms (.var (WinImplications.selectedMsVar W))) (pauliCL P (.ms (.var (WinImplications.selectedMsVar W))) z)).effect b = 0 := by
  classical
  refine honest_mul_of_valid fun hva hvb => ?_
  cases a <;> try contradiction
  rename_i u
  cases b <;> try contradiction
  rename_i β
  let s := pauliSharedProjection z
  let r : PauliKind → PauliScalar P | .X => pauliRXBlock s | .Z => pauliRZBlock s
  by_cases hg : pauliPairGamma P s = 0
  · have hok : pauliPointVariableCondition P W s (WinImplications.selectedMsVar W) u β := Or.inl hg
    simpa [pauliWinPredicate, validPauliAnswer, hok, s, pauliCL] using hrej
  · have hm : honestMagicMeasurement (.var (WinImplications.selectedMsVar W)) s =
        placedPauliMeasurement (pauliBasisMeasurement W)
          (fun h => .bit (pauliTraceBit (pauliPointBlock W s) (r W) h)) := by
      cases W with
      | X => exact (honestMagicMeasurement_var_eq_placedBasis P hg).1
      | Z => exact (honestMagicMeasurement_var_eq_placedBasis P hg).2
    change _ * (honestMagicMeasurement (.var (WinImplications.selectedMsVar W)) s).effect _ = 0
    rw [honestMeasurement_point_eq, hm]
    refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) _ _ hrej
    have hok : pauliPointVariableCondition P W s (WinImplications.selectedMsVar W) (lowDegreeEnc h (pauliPointBlock W z))
        (pauliTraceBit (pauliPointBlock W s) (r W) h) := by
      cases W with
      | X => exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
      | Z => exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
    exact decide_eq_true hok

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
theorem honest_pairW_pair_rejected_mul
    (hrej : pauliWinPredicate P (.pairW W, pauliCL P (.pairW W) z)
      (.pair, pauliCL P .pair z) a b = false) :
    (honestMeasurement (.pairW W) (pauliCL P (.pairW W) z)).effect a *
      (honestMeasurement .pair (pauliCL P .pair z)).effect b = 0 := by
  let effectAt :=
    (pauliTraceMeasurement .X (pauliXBlock (pauliSharedProjection z))
    (pauliRXBlock (pauliSharedProjection z))).effect
  classical
  refine honest_mul_of_valid fun hva hvb => ?_
  obtain ⟨β, rfl⟩ : ∃ c, a = PauliAnswer.bit c := by
    cases a <;> first | exact ⟨_, rfl⟩ | exact absurd hva (by simp [validPauliAnswer])
  obtain ⟨bits, rfl⟩ : ∃ c, b = PauliAnswer.pairBits c := by
    cases b <;> first | exact ⟨_, rfl⟩ | exact absurd hvb (by simp [validPauliAnswer])
  have hacc : pauliPairCondition P W (pauliCL P (.pairW W) z) β bits →
      pauliWinPredicate P (PauliType.pairW W, pauliCL P (.pairW W) z)
        (PauliType.pair, pauliCL P .pair z) (PauliAnswer.bit β)
        (PauliAnswer.pairBits bits) = true := by
    simp [pauliWinPredicate, validPauliAnswer]
  by_cases hg : pauliPairGamma P (pauliSharedProjection z) = 0
  let readout :=
    pauliTraceMeasurement .Z (pauliZBlock (pauliSharedProjection z))
     (pauliRZBlock (pauliSharedProjection z))
  · have hcond : ¬ pauliPairCondition P W (pauliCL P (.pairW W) z) β bits := by
      simp_all
    have hpair : honestMeasurement PauliType.pair (pauliCL P PauliType.pair z) =
        placedPauliMeasurement (pauliPairMeasurement (pauliSharedProjection z) hg)
          (PauliAnswer.pairBits) := by
      change honestPairMeasurement P (pauliSharedProjection z) = _
      simp [honestPairMeasurement, hg]
    have h2 : (honestMeasurement PauliType.pair
          (pauliCL P PauliType.pair z)).effect (PauliAnswer.pairBits bits) =
        heteroKron (effectAt bits.1 *
            readout.effect bits.2)
          1 := by
      rw [hpair]
      exact placedPauliMeasurement_effect_image _ _ (by intro; simp) bits
    cases W with
    | X =>
        have hne : β ≠ bits.1 := by
          solve_by_elim [Or.inr]
        have h1 : (honestMeasurement (PauliType.pairW PauliKind.X)
              (pauliCL P (.pairW .X) z)).effect (PauliAnswer.bit β) =
            heteroKron (effectAt β) 1 :=
          placedPauliMeasurement_effect_image _ _ (by intro; simp) β
        simp_all
        apply leftPlaced_mul_eq_zero
        simp [effectAt, ← mul_assoc, DistanceCalculus.projective_effect_mul_effect_eq_zero
            (pauliTraceMeasurement .X (pauliXBlock (pauliSharedProjection z))
              (pauliRXBlock (pauliSharedProjection z)))
            (pauliTraceMeasurement_projective P .X _ _) hne]
    | Z =>
        have hne : β ≠ bits.2 := by
          solve_by_elim [Or.inr]
        have h1 : (honestMeasurement (PauliType.pairW PauliKind.Z)
              (pauliCL P (.pairW .Z) z)).effect (PauliAnswer.bit β) =
            heteroKron (readout.effect β) 1 :=
          placedPauliMeasurement_effect_image _ _ (by intro; simp) β
        simp_all
        apply leftPlaced_mul_eq_zero
        rw [← mul_assoc,
          ← (pauliTraceMeasurement_effect_commute hg
            bits.1 β).eq, mul_assoc,
          DistanceCalculus.projective_effect_mul_effect_eq_zero
            (pauliTraceMeasurement .Z (pauliZBlock (pauliSharedProjection z))
              (pauliRZBlock (pauliSharedProjection z)))
            (pauliTraceMeasurement_projective P .Z _ _) hne,
          mul_zero]
  · simp_all [hacc (Or.inl hg)]

/-! ### The Magic Square incidence forms -/

include hms in
/-- Along every edge of the Magic Square type graph the honest measurements have
zero operator product at every rejected answer pair: a vanishing phase bit makes
the decision predicate accept, and otherwise the honest measurements are the
relabelled Magic Square measurements of `thm:ms-from-ac`. -/
theorem honest_ms_rejected_mul
    (hrej : pauliWinPredicate P (.ms s₁, pauliCL P (.ms s₁) z)
      (.ms s₂, pauliCL P (.ms s₂) z) a b = false) :
    (honestMeasurement (.ms s₁) (pauliCL P (.ms s₁) z)).effect a *
      (honestMeasurement (.ms s₂) (pauliCL P (.ms s₂) z)).effect b = 0 := by
  classical
  have hcl : ∀ s : MsType, pauliCL P (PauliType.ms s) z = pauliSharedProjection z :=
    fun _ => rfl
  simp only [hcl] at hrej ⊢
  have hsupp : (s₁, s₂) ∈ msGameSymm.μ.support := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hms⟩
  refine honest_mul_of_valid fun hva hvb => ?_
  obtain ⟨a', rfl⟩ : ∃ c, a = pauliAnswerOfMs c := by
    cases a
    case msTriple β => solve_by_elim [MsAnswer.triple]
    case bit c => solve_by_elim [MsAnswer.bit]
    all_goals simp_all [validPauliAnswer]
  obtain ⟨b', rfl⟩ : ∃ c, b = pauliAnswerOfMs c := by
    cases b
    case msTriple β => solve_by_elim [MsAnswer.triple]
    case bit c => solve_by_elim [MsAnswer.bit]
    all_goals simp_all [validPauliAnswer]
  have rejected : ¬(pauliPairGamma P (pauliSharedProjection z) = 0 ∨ msWinPredicate s₁ s₂ a' b') := by
    intro hgood
    have hpos : pauliWinPredicate P (.ms s₁, pauliSharedProjection z)
        (.ms s₂, pauliSharedProjection z)
        (pauliAnswerOfMs a') (pauliAnswerOfMs b') = true := by
      clear hrej
      rcases msGame_support_incidence s₁ s₂ hsupp with
        ⟨i, k, rfl, rfl⟩ | ⟨i, k, rfl, rfl⟩ <;>
        cases a' <;> cases b' <;>
        simp_all [pauliWinPredicate, validPauliAnswer, pauliAnswerOfMs, msWinPredicate]
    simp_all
  obtain ⟨hg, hmsrej⟩ := not_or.mp rejected
  have hM : ∀ s : MsType, honestMeasurement (.ms s) (pauliSharedProjection z) =
      (pauliMagicMeasurement _ hg s).postprocess
        (pauliAnswerOfMs) := by
    intro s
    change honestMagicMeasurement (P := P) s _ = _
    simp [honestMagicMeasurement, hg]
  rw [hM, hM,
    SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective a',
    SandwichProduct.postprocess_effect_of_injective _ _ pauliAnswerOfMs_injective b']
  refine msStrategyMeasurement_rejected_mul_on_support _ _ _ ?_ s₁ s₂ hsupp a' b' (by simpa using hmsrej)
  intro i k ab c
  exact msCellConstraintJoint_mul _ _
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .X
      (pauliXBlock (pauliSharedProjection z))
      (pauliRXBlock (pauliSharedProjection z))))
    (obsOf_conjTranspose _ (pauliTraceMeasurement_projective P .Z
      (pauliZBlock (pauliSharedProjection z))
      (pauliRZBlock (pauliSharedProjection z))))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .X
      (pauliXBlock (pauliSharedProjection z))
      (pauliRXBlock (pauliSharedProjection z))))
    (obsOf_sq _ (pauliTraceMeasurement_projective P .Z
      (pauliZBlock (pauliSharedProjection z))
      (pauliRZBlock (pauliSharedProjection z))))
    (obsOf_pauliTraceMeasurement_anticommute hg)
    i k ab c

/-! ### Zero products along the oriented incidence forms -/

include h in
/-- Along every ordered incidence form of the Pauli type graph the honest
measurements have zero operator product at every rejected answer pair. -/
theorem honest_oriented_rejected_mul
    (hrej : pauliWinPredicate P (t₁, pauliCL P t₁ z) (t₂, pauliCL P t₂ z) a b = false) :
    (honestMeasurement t₁ (pauliCL P t₁ z)).effect a *
      (honestMeasurement t₂ (pauliCL P t₂ z)).effect b = 0 := by
  rcases h with ⟨W, rfl, hW⟩ | ⟨W, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hW with rfl | rfl | rfl | rfl
    · rw [honestMeasurement_point_eq, honestMeasurement_aline_eq]
      refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
      simpa [pauliWinPredicate, validPauliAnswer] using honest_alinePointCondition P W z h
    · rw [honestMeasurement_point_eq, honestMeasurement_dline_eq]
      refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
      simpa [pauliWinPredicate, validPauliAnswer] using honest_dlinePointCondition P W z h
    · rw [honestMeasurement_point_eq, honestMeasurement_pauli_eq]
      refine placedBasis_rejected_mul P W _ _ _ _ (fun h => ?_) a b hrej
      simpa [pauliWinPredicate, validPauliAnswer] using (by
        change _ =
          lowDegreeEnc h (pauliPointBlock W z)
        rw [pauliPointBlock_pauliCL_point])
    · cases W
      · rw [honestMeasurement_point_eq, honestMeasurement_pairW_X_eq]
        refine placedBasis_rejected_mul P .X _ _ _ _ (fun h => ?_) a b hrej
        have hcond : pauliPointPairCondition P .X (pauliCL P (.pairW .X) z)
            (lowDegreeEnc h (pauliPointBlock PauliKind.X z))
            (pauliTraceBit (pauliXBlock z) (pauliRXBlock z) h) := Or.inr rfl
        simpa [pauliWinPredicate, validPauliAnswer] using hcond
      · rw [honestMeasurement_point_eq, honestMeasurement_pairW_Z_eq]
        refine placedBasis_rejected_mul P .Z _ _ _ _ (fun h => ?_) a b hrej
        have hcond : pauliPointPairCondition P .Z (pauliCL P (.pairW .Z) z)
            (lowDegreeEnc h (pauliPointBlock PauliKind.Z z))
            (pauliTraceBit (pauliZBlock z) (pauliRZBlock z) h) := Or.inr rfl
        simpa [pauliWinPredicate, validPauliAnswer] using hcond
  · solve_by_elim [honest_pairW_pair_rejected_mul]
  · solve_by_elim [honest_point_msVar_rejected_mul]
  · solve_by_elim [honest_point_msVar_rejected_mul]

end

end MIPStarRE.QPBT
