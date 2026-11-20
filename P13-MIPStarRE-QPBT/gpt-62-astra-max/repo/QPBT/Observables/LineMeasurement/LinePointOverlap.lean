module

public import QPBT.Observables.LineMeasurement.SelfConsistency
public import QPBT.Observables.LineMeasurement.Evaluation

/-!
# Overlap of expanded line and expanded point measurements

This module computes the diagonal overlap, on the expanded state, between an
expanded line measurement on one placement and the expanded point effects
selected by evaluation at the sampled point on the opposite placement. Each
product of convolution terms factorizes into a strategy overlap and an EPR
overlap; the EPR overlap of a Pauli line projector with a Pauli point projector
vanishes unless the line polynomial evaluates to the point value, and then
equals the EPR overlap of the line projector alone. Summing over the
convolution fibers identifies the expanded overlap with the overlap of the
strategy's evaluation classes and its completed point measurement. This is the
computation displayed in items 2 and 3 of the expanded-line consistency lemma.

The sections on the linearity of the state quadratic form, on register
placements, and on the completed point measurements collect formalization-only
auxiliaries: the source uses these facts without stating them.

## References

Items 2 and 3 of `lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Linearity of the state quadratic form -/

namespace DistanceCalculus

/-- The state quadratic form of the zero operator vanishes. -/
theorem stateQForm_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : stateQForm ψ (0 : Op ι) = 0 := by
  simp [stateQForm, applyOperatorToState]

end DistanceCalculus

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-- A register placement respects finite sums of operators.
Formalization-only auxiliary for the register placements of
`def:symmetric-equivalents`; the source uses this additivity without stating
it. -/
theorem place_finset_sum (S : ProjectiveSetting P ε) (p : Placement)
    {γ : Type*} (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ g ∈ s, O g) = ∑ g ∈ s, S.place p (O g) := by
  ext i j
  cases p <;> simp only [place, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]

/-- A register placement of the zero operator is zero. -/
theorem place_zero (S : ProjectiveSetting P ε) (p : Placement) :
    S.place p (0 : Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [place]

section

variable (S : ProjectiveSetting P ε) {γ : Type*} (s : Finset γ)

/-- The `AA'` placement respects finite sums. -/
theorem place_AA'_finset_sum (O : γ → Op (S.ExpandedLocalSpace .alice)) :
    S.place .AA' (∑ g ∈ s, O g : Op (S.ExpandedLocalSpace .alice)) =
      ∑ g ∈ s, S.place .AA' (O g) :=
  place_finset_sum S .AA' s O

/-- The `BA''` placement respects finite sums. -/
theorem place_BA''_finset_sum (O : γ → Op (S.ExpandedLocalSpace .bob)) :
    S.place .BA'' (∑ g ∈ s, O g : Op (S.ExpandedLocalSpace .bob)) =
      ∑ g ∈ s, S.place .BA'' (O g) :=
  place_finset_sum S .BA'' s O

end

/-! ## Effects of the completed measurement families -/

section

variable (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)

/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (u : PauliPoint P)
    (b : PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (u : PauliPoint P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp

section

variable (line : LineDesc P.toLdParams) (u : PauliPoint P)

/-- The expanded point effect selected by a line answer is the completed
expanded point effect at the partial evaluation of the answer. This
identifies the two presentations of item 2 and item 3 of
`lem:qld-comm-line-cons`, blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`. -/
theorem pointMeasExpOption_effect_evalOpt (f : PauliLinePoly P) :
    (S.pointMeasExpOption side W u).effect (evalOpt line u f) =
      S.expPointEffectAtLineAnswer side W line u f := by
  unfold expPointEffectAtLineAnswer
  cases evalOpt line u f with
  | none => apply S.pointMeasExpOption_effect_none
  | some a => apply S.pointMeasExpOption_effect_some

/-- The expanded point effect selected by a line answer, written through the
convolution form of the expanded point measurement. -/
theorem expPointEffectAtLineAnswer_eq_elim (f : PauliLinePoly P) :
    S.expPointEffectAtLineAnswer side W line u f =
      (evalOpt line u f).elim 0 (fun a =>
        ∑ q ∈ Finset.univ.filter
          (fun q : PauliScalar P × PauliScalar P => q.1 + q.2 = a),
          heteroKron ((S.pointMeas side W u).effect q.1)
            (tauPointProj W u q.2)) := by
  unfold expPointEffectAtLineAnswer
  cases evalOpt line u f with
  | none => rfl
  | some a => apply S.expPointOp_eq_convolution

/-- Effects of the expanded evaluation classes are the fiber sums of expanded
line effects. -/
theorem lineEvalMeasExp_effect (o : Option (PauliScalar P)) :
    (S.lineEvalMeasExp side W line u).effect o =
      ∑ f ∈ Finset.univ.filter
        (fun f : PauliLinePoly P => evalOpt line u f = o),
        S.expLineOp side W line f := by
  rfl

end

end

/-! ## Factorization of opposite placements with distinct Pauli factors -/

set_option synthInstance.maxSize 400 in
/-- The product of opposite `AA'` and `BA''` placements with distinct Pauli
factors separates into the strategy product, the first EPR-pair product, and
the identity on the second EPR pair. -/
theorem reindexOp_sixRegShuffle_place_AA'_mul_BA''_two
    (S : ProjectiveSetting P ε) (A : Op S.toStrategy.ιA)
    (B : Op S.toStrategy.ιB) (T T' : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T')) =
      heteroKron (heteroKron (heteroKron A B) (heteroKron T T'))
        (1 : Op (PauliRegister P × PauliRegister P)) := by
  rw [WinImplications.reindexOp_mul,
    reindexOp_sixRegShuffle_place_AA'_heteroKron,
    reindexOp_sixRegShuffle_place_BA''_heteroKron]
  simp [heteroKron_mul, heteroKron_one_one]

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AA'`--`BA''` product with distinct
Pauli factors factors into the strategy overlap and the first EPR-pair
overlap. This is the factorization behind the ancillary consistency in items
2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem stateQForm_place_AA'_mul_BA''_two {S : ProjectiveSetting P ε}
    {A : Op S.toStrategy.ιA} {B : Op S.toStrategy.ιB}
    {T T' : Op (PauliRegister P)} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T T') := by
  have hAB :=
    heteroKron_isHermitian hA hB
  have hTT :=
    heteroKron_isHermitian hT hT'
  rw [psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    reindexOp_sixRegShuffle_place_AA'_mul_BA''_two,
    stateQForm_vecTensor_heteroKron _ _ _ _ (heteroKron_isHermitian hAB hTT) Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB hTT,
    DistanceCalculus.stateQForm_one, eprState_norm]
  ring

variable (S : ProjectiveSetting P ε) (X : Op (S.ExpandedLocalSpace .alice))
  (Y : Op (S.ExpandedLocalSpace .bob))

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AA'` and on `BA''` commute. -/
theorem place_AA'_mul_place_BA''_comm :
    S.place .AA' X * S.place .BA'' Y = S.place .BA'' Y * S.place .AA' X := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      S.place .AA' X' * S.place .BA'' Y' = S.place .BA'' Y' * S.place .AA' X' := by
    intro X' Y'
    simp [← WinImplications.reindexOp_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul, ← reindexOp_aaBaBipartition_left S X', ← reindexOp_aaBaBipartition_right S Y']
  apply key

end ProjectiveSetting

/-! ## The overlap identity -/

section

variable (P : AdmissibleParams) (W : PauliKind) {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL]
  [Fintype ιP] [DecidableEq ιP] (LM : Measurement (PauliLinePoly P) ιL)
  (PM : Measurement (ScalarQ P.toLdParams) ιP)
  (Φ : Op (ιL × PauliRegister P) → Op (ιP × PauliRegister P) → ℝ) (Ψ : Op ιL → Op ιP → ℝ)
  (line : LineDesc P.toLdParams) (u : Fin P.m → ScalarQ P.toLdParams)

/-- The convolution-fiber rearrangement behind `eq:qld-comm-line-pt-cons`
and `eq:qld-comm-line-pt-cons2`, at a point of the line. The statement is an
abstract bilinear identity: `Φ` and `Ψ` are any two functions of a pair of
operators subject to the vanishing, additivity and factorization hypotheses
below, and the conclusion sums `Φ` over the convolution fibers of the expanded
line and point effects. It is applied with `Φ` the expanded overlap of two
product operators on opposite placements and `Ψ` the strategy overlap, the
factorization hypothesis then being the exact agreement of the ancillary
projectors `tau^{W,line}_{f''}` and `tau^{W,u}_{f''(u)}` on the EPR pairs; the
conclusion is the overlap of the strategy's evaluation classes with its
completed point measurement. Paper `14_analysis_of_the_pauli_basis_test.tex:534-545`,
blueprint `eq:qld-comm-line-pt-cons`, `eq:qld-comm-line-pt-cons2`. -/
theorem overlap_identity_of_mem
    (hu : u ∈ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΦl : ∀ (s : Finset (PauliLinePoly P ×
        PauliLinePoly P))
      (X : PauliLinePoly P × PauliLinePoly P →
        Op (ιL × PauliRegister P)) (Y : Op (ιP × PauliRegister P)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y)
    (hΦr : ∀ (X : Op (ιL × PauliRegister P))
      (t : Finset (ScalarQ P.toLdParams × ScalarQ P.toLdParams))
      (Y : ScalarQ P.toLdParams × ScalarQ P.toLdParams → Op (ιP × PauliRegister P)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j))
    (hΦfact : ∀ (f' f'' : PauliLinePoly P) (b' b'' : ScalarQ P.toLdParams),
      Φ (heteroKron (LM.effect f') (tauLineProj W line f''))
          (heteroKron (PM.effect b') (ProjectiveSetting.tauPointProj W u b'')) =
        Ψ (LM.effect f') (PM.effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj W line f'') (1 : Op (PauliRegister P)))
          else 0))
    (hΨl : ∀ (s : Finset (PauliLinePoly P))
      (A : PauliLinePoly P → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : PauliLinePoly P,
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : PauliLinePoly P ×
            PauliLinePoly P => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj W line p.2))
        ((evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  let c : PauliLinePoly P → ℝ := fun f'' =>
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (tauLineProj W line f'') 1)
  let Pt : Option (ScalarQ P.toLdParams) → Op ιP := (PM.postprocess some).effect
  have hPt_none : Pt none = 0 := by
    simp only [Pt]
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    simp
  have hPt_some (b : ScalarQ P.toLdParams) : Pt (some b) = PM.effect b := by
    simp only [Pt]
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    simp [Finset.filter_eq']
  have hc0 : ∀ f'', evalOpt line u f'' = none → c f'' = 0 := by
    intro f'' h
    simp [c, heteroKron_zero_left, DistanceCalculus.stateQForm_zero, tauLineProj_eq_zero_of_evalOpt_none P W line u hu f'' h]
  have hterm : ∀ (f : PauliLinePoly P)
      (p : PauliLinePoly P × PauliLinePoly P),
      p.1 + p.2 = f →
      Φ (heteroKron (LM.effect p.1) (tauLineProj W line p.2))
          ((evalOpt line u f).elim 0 (fun a =>
            ∑ q ∈ Finset.univ.filter
              (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
              heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2))) =
        Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 := by
    intro f p hp
    rcases hf : evalOpt line u f with _ | a
    · rw [Option.elim_none, hΦ0]
      rcases h1 : evalOpt line u p.1 with _ | a'
      · simp [*]
      · have h2 : evalOpt line u p.2 = none := by
          rcases h2 : evalOpt line u p.2 with _ | b
          · rfl
          · exfalso
            have hsum := ((evalOpt_eq_some_iff _ _ _ _).mpr
                           (((evalOpt_eq_some_iff _ _ _ _).mp h1).add
                             ((evalOpt_eq_some_iff _ _ _ _).mp h2)))
            rw [hp, hf] at hsum
            exact absurd hsum (by simp)
        simp [*]
    · simp [hΦr]
      simp_rw [hΦfact]
      rcases h2 : evalOpt line u p.2 with _ | c''
      · simp [*]
      · have hsum : evalOpt line u (p.1 + p.2) = some a := by simp [*]
        have h1 :=
          ((evalOpt_eq_some_iff _ _ _ _).mpr
            (((evalOpt_eq_some_iff _ _ _ _).mp hsum).left_of_add
              ((evalOpt_eq_some_iff _ _ _ _).mp h2)))
        rw [h1, hPt_some]
        rw [Finset.sum_eq_single (a - c'', c'')]
        · rw [if_pos rfl]
        · intro q hq hne
          rw [if_neg, mul_zero]
          intro heq
          apply hne
          have hq2 := (Option.some_inj.mp heq).symm
          have hq1 := (Finset.mem_filter.mp hq).2
          ext
          · simp [← hq1, hq2]
          · exact hq2
        · simp
  calc
    _ = ∑ f : PauliLinePoly P,
        ∑ p ∈ Finset.univ.filter
          (fun p : PauliLinePoly P ×
            PauliLinePoly P => p.1 + p.2 = f),
          Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 := by
      congr 1 with f
      rw [hΦl]
      exact Finset.sum_congr rfl fun p hp => hterm f p (Finset.mem_filter.mp hp).2
    _ = ∑ p : PauliLinePoly P × PauliLinePoly P,
        Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 :=
      Finset.sum_fiberwise Finset.univ
        (fun p : PauliLinePoly P ×
          PauliLinePoly P => p.1 + p.2)
        _
    _ = ∑ f' : PauliLinePoly P,
        Ψ (LM.effect f') (Pt (evalOpt line u f')) := by
      rw [Fintype.sum_prod_type]
      congr 1 with f'
      change ∑ y, Ψ (LM.effect f') (Pt (evalOpt line u f')) * c y =
        _
      rw [← Finset.mul_sum, (sum_stateQForm_eprState_tauLineProj_one P W line), mul_one]
    _ = ∑ o : Option (ScalarQ P.toLdParams),
        ∑ f' ∈ Finset.univ.filter
          (fun f' : PauliLinePoly P => evalOpt line u f' = o),
          Ψ (LM.effect f') (Pt o) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun f' => evalOpt line u f')
        (fun f' => Ψ (LM.effect f') (Pt (evalOpt line u f')))]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun f' hf' => ?_
      rw [(Finset.mem_filter.mp hf').2]
    _ = _ := by
      congr 1 with o
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect, hΨl]

/-- Off the line, both sides of the overlap identity vanish: no line
polynomial evaluates, so the selected point effects are zero and the
evaluation classes with a proper value are empty. -/
theorem overlap_identity_of_not_mem
    (hu : u ∉ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΨl : ∀ (s : Finset (PauliLinePoly P))
      (A : PauliLinePoly P → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : PauliLinePoly P,
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : PauliLinePoly P ×
            PauliLinePoly P => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj W line p.2))
        ((evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  have hnone : ∀ f : PauliLinePoly P, evalOpt line u f = none :=
    fun f => (by
               rw [evalOpt_eq_none_iff]
               rintro ⟨a, ha⟩
               exact hu ha.1)
  rw [Finset.sum_eq_zero fun f _ => by simp [*]]
  symm
  refine Finset.sum_eq_zero fun o _ => ?_
  rcases o with _ | b
  · have hPt : (PM.postprocess some).effect none = 0 := by
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      simp
    simp_all
  · have hempty : Finset.univ.filter
        (fun f' : PauliLinePoly P => evalOpt line u f' = some b) =
          ∅ := by
      simp_all
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect, hempty, Finset.sum_empty]
    exact hΨl ∅ (fun _ => 0) ((PM.postprocess some).effect (some b))

end

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The four placement pairs -/

section

variable (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind)

/-- A strategy line effect is Hermitian, being positive semidefinite. -/
private theorem lineMeas_effect_isHermitian (line : LineDesc P.toLdParams)
    (f : PauliLinePoly P) :
    ((S.lineMeas side W line).effect f).IsHermitian :=
  (measurement_effect_hermitian (S.lineMeas side W line) f)

/-- A strategy point effect is Hermitian, being positive semidefinite. -/
private theorem pointMeas_effect_isHermitian (u : PauliPoint P)
    (b : PauliScalar P) :
    ((S.pointMeas side W u).effect b).IsHermitian :=
  (measurement_effect_hermitian (S.pointMeas side W u) b)

end

/-- A Pauli line projector is Hermitian, being positive semidefinite. -/
private theorem tauLineProj_isHermitian (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : PauliLinePoly P) :
    (tauLineProj W line f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (tauLineProj_nonneg P W line f)).isHermitian

/-- A Pauli point projector is Hermitian, being positive semidefinite. -/
private theorem tauPointProj_isHermitian (W : PauliKind)
    (u : PauliPoint P) (b : PauliScalar P) :
    (tauPointProj W u b).IsHermitian :=
  (measurement_effect_hermitian (tauPointMeas W u) b)

set_option synthInstance.maxSize 400 in
/-- The expanded overlap of Alice's line measurement on `AA'` with Bob's
selected point effects on `BA''` is the strategy overlap of Alice's
evaluation classes with Bob's completed point measurement. This is the
computation `eq:qld-mhat-line-1`--`eq:qld-comm-line-pt-cons-eps` of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:560-596`. -/
theorem overlap_AA'_BA''_eq (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : PauliPoint P) :
    ∑ f : PauliLinePoly P,
        DistanceCalculus.stateQForm S.psiHat
          (S.place .AA' (S.expLineOp .alice W line f) *
            S.place .BA'' (S.expPointEffectAtLineAnswer .bob W line u f)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.lineEvalMeas .alice W line u).effect o)
            ((S.pointMeasOption .bob W u).effect o)) := by
  let Φ : _ →
      _ → ℝ := fun X Y =>
    DistanceCalculus.stateQForm S.psiHat (S.place .AA' X * S.place .BA'' Y)
  let Ψ : Op S.toStrategy.ιA → Op S.toStrategy.ιB → ℝ := fun L Q =>
    DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron L Q)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    simp only [Φ]
    simp [place_zero _ .BA'', DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : _)
      (X : PauliLinePoly P × PauliLinePoly P →
        Op (S.ExpandedLocalSpace .alice))
      (Y : Op (S.ExpandedLocalSpace .bob)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [place_AA'_finset_sum, Finset.sum_mul,
      DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace .alice))
      (t : _)
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace .bob)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [place_BA''_finset_sum, Finset.mul_sum,
      DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : _)
      (A : PauliLinePoly P → Op S.toStrategy.ιA)
      (B : Op S.toStrategy.ιB), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    simp [Ψ, DistanceCalculus.heteroKron_finset_sum_left, DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    simp [Ψ, heteroKron_zero_right, DistanceCalculus.stateQForm_zero]
  simp_rw [expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · refine overlap_identity_of_mem P W _
      _ Φ Ψ line u hu hΦ0 hΦl hΦr ?_ hΨl hΨ0
    intro f' f'' b' b''
    simp only [Φ, Ψ]
    have hfac := stateQForm_place_AA'_mul_BA''_two
      (lineMeas_effect_isHermitian S .alice W line f')
      (pointMeas_effect_isHermitian S .bob W u b')
      (tauLineProj_isHermitian W line f'') (tauPointProj_isHermitian W u b'')
    rw [stateQForm_eprState_tauLineProj_tauPointProj P W line u hu f'' b''] at hfac
    exact hfac
  · exact overlap_identity_of_not_mem P W (S.lineMeas .alice W line)
      (S.pointMeas .bob W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

set_option synthInstance.maxSize 400 in
/-- The expanded overlap of Bob's line measurement on `BA''` with Alice's
selected point effects on `AA'` is the strategy overlap of Alice's completed
point measurement with Bob's evaluation classes. This is the interchanged
form of the computation in items 2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:560-596`. -/
theorem overlap_BA''_AA'_eq (S : ProjectiveSetting P ε) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : PauliPoint P) :
    ∑ f : PauliLinePoly P,
        DistanceCalculus.stateQForm S.psiHat
          (S.place .BA'' (S.expLineOp .bob W line f) *
            S.place .AA' (S.expPointEffectAtLineAnswer .alice W line u f)) =
      ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeasOption .alice W u).effect o)
            ((S.lineEvalMeas .bob W line u).effect o)) := by
  let Φ : _ →
      _ → ℝ := fun X Y =>
    DistanceCalculus.stateQForm S.psiHat (S.place .BA'' X * S.place .AA' Y)
  let Ψ : Op S.toStrategy.ιB → Op S.toStrategy.ιA → ℝ := fun L Q =>
    DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron Q L)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by
    simp only [Φ]
    simp [place_zero _ .AA', DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : _)
      (X : PauliLinePoly P × PauliLinePoly P →
        Op (S.ExpandedLocalSpace .bob))
      (Y : Op (S.ExpandedLocalSpace .alice)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    intro s X Y
    simp only [Φ]
    rw [place_BA''_finset_sum, Finset.sum_mul,
      DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace .bob))
      (t : _)
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace .alice)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    intro X t Y
    simp only [Φ]
    rw [place_AA'_finset_sum, Finset.mul_sum,
      DistanceCalculus.stateQForm_finset_sum]
  have hΨl : ∀ (s : _)
      (A : PauliLinePoly P → Op S.toStrategy.ιB)
      (B : Op S.toStrategy.ιA), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B := by
    simp [Ψ, DistanceCalculus.heteroKron_finset_sum_right, DistanceCalculus.stateQForm_finset_sum]
  have hΨ0 : ∀ A, Ψ A 0 = 0 := by
    simp [Ψ, heteroKron_zero_left, DistanceCalculus.stateQForm_zero]
  simp_rw [expPointEffectAtLineAnswer_eq_elim]
  by_cases hu : u ∈ line.pointSet
  · refine overlap_identity_of_mem P W _
      _ Φ Ψ line u hu hΦ0 hΦl hΦr ?_ hΨl hΨ0
    intro f' f'' b' b''
    simp only [Φ, Ψ]
    have hfac := stateQForm_place_AA'_mul_BA''_two
      (pointMeas_effect_isHermitian S .alice W u b')
      (lineMeas_effect_isHermitian S .bob W line f')
      (tauPointProj_isHermitian W u b'') (tauLineProj_isHermitian W line f'')
    rw [stateQForm_eprState_tauPointProj_tauLineProj P W line u hu f'' b''] at hfac
    have hcomm := place_AA'_mul_place_BA''_comm S
      (heteroKron ((S.pointMeas .alice W u).effect b') (tauPointProj W u b''))
      (heteroKron ((S.lineMeas .bob W line).effect f') (tauLineProj W line f''))
    exact (congrArg (DistanceCalculus.stateQForm S.psiHat) hcomm.symm).trans hfac
  · exact overlap_identity_of_not_mem P W (S.lineMeas .bob W line)
      (S.pointMeas .alice W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

end ProjectiveSetting

end

end MIPStarRE.QPBT
