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

/-! ## Effects of the completed measurement families -/

/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (b : PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_eq_zero
  intro a ha
  exact absurd (Finset.mem_filter.mp ha).2 (by simp)

/-- Effects of the expanded evaluation classes are the fiber sums of expanded
line effects. -/
theorem lineEvalMeasExp_effect (S : ProjectiveSetting P ε) (side : PlayerSide)
    (W : PauliKind) (line : LineDesc P.toLdParams)
    (u : Fin P.m → PauliScalar P) (o : Option (PauliScalar P)) :
    (S.lineEvalMeasExp side W line u).effect o =
      ∑ f ∈ Finset.univ.filter
        (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
        S.expLineOp side W line f := by
  unfold lineEvalMeasExp
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rfl

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
  simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
    heteroKron_one_one]

set_option synthInstance.maxSize 400 in
/-- The product of opposite `AB''` and `BB'` placements with distinct Pauli
factors separates into the strategy product, the identity on the first EPR
pair, and the second EPR-pair product. -/
theorem reindexOp_sixRegShuffle_place_AB''_mul_BB'_two
    (S : ProjectiveSetting P ε) (A : Op S.toStrategy.ιA)
    (B : Op S.toStrategy.ιB) (T T' : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AB'' (heteroKron A T) * S.place .BB' (heteroKron B T')) =
      heteroKron (heteroKron (heteroKron A B)
          (1 : Op (PauliRegister P × PauliRegister P)))
        (heteroKron T' T) := by
  rw [WinImplications.reindexOp_mul,
    reindexOp_sixRegShuffle_place_AB''_heteroKron,
    reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
    heteroKron_one_one]

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AA'`--`BA''` product with distinct
Pauli factors factors into the strategy overlap and the first EPR-pair
overlap. This is the factorization behind the ancillary consistency in items
2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem stateQForm_place_AA'_mul_BA''_two (S : ProjectiveSetting P ε)
    (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T T' : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T T') := by
  have hAB : (heteroKron A B).IsHermitian :=
    heteroKron_isHermitian A B hA hB
  have hTT : (heteroKron T T').IsHermitian :=
    heteroKron_isHermitian T T' hT hT'
  have hactive :
      (heteroKron (heteroKron A B) (heteroKron T T')).IsHermitian :=
    heteroKron_isHermitian _ _ hAB hTT
  rw [psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    reindexOp_sixRegShuffle_place_AA'_mul_BA''_two,
    stateQForm_vecTensor_heteroKron _ _ _ _ hactive Matrix.isHermitian_one,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB hTT,
    stateQForm_one_eq_norm_sq, eprState_norm]
  ring

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AB''`--`BB'` product with distinct
Pauli factors factors into the strategy overlap and the second EPR-pair
overlap, the Pauli factor of `BB'` acting on the first half of the pair.
Paper `14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem stateQForm_place_AB''_mul_BB'_two (S : ProjectiveSetting P ε)
    (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T T' : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AB'' (heteroKron A T) * S.place .BB' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T' T) := by
  have hAB : (heteroKron A B).IsHermitian :=
    heteroKron_isHermitian A B hA hB
  have hpassive :
      (heteroKron (heteroKron A B)
        (1 : Op (PauliRegister P × PauliRegister P))).IsHermitian :=
    heteroKron_isHermitian _ _ hAB Matrix.isHermitian_one
  have hTT : (heteroKron T' T).IsHermitian :=
    heteroKron_isHermitian T' T hT' hT
  rw [psiHat_eq_reindexState, WinImplications.stateQForm_reindexState,
    reindexOp_sixRegShuffle_place_AB''_mul_BB'_two,
    stateQForm_vecTensor_heteroKron _ _ _ _ hpassive hTT,
    stateQForm_vecTensor_heteroKron _ _ _ _ hAB Matrix.isHermitian_one,
    stateQForm_one_eq_norm_sq, eprState_norm]
  ring

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AA'` and on `BA''` commute. -/
theorem place_AA'_mul_place_BA''_comm (S : ProjectiveSetting P ε)
    (X : Op (S.ExpandedLocalSpace .alice))
    (Y : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AA' X * S.place .BA'' Y = S.place .BA'' Y * S.place .AA' X := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      S.place .AA' X' * S.place .BA'' Y' = S.place .BA'' Y' * S.place .AA' X' := by
    intro X' Y'
    rw [← reindexOp_aaBaBipartition_left S X', ← reindexOp_aaBaBipartition_right S Y',
      ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    congr 1
    rw [heteroKron_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  exact key X Y

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AB''` and on `BB'` commute. -/
theorem place_AB''_mul_place_BB'_comm (S : ProjectiveSetting P ε)
    (X : Op (S.ExpandedLocalSpace .alice))
    (Y : Op (S.ExpandedLocalSpace .bob)) :
    S.place .AB'' X * S.place .BB' Y = S.place .BB' Y * S.place .AB'' X := by
  have key : ∀ (X' : Op (S.toStrategy.ιA × PauliRegister P))
      (Y' : Op (S.toStrategy.ιB × PauliRegister P)),
      S.place .AB'' X' * S.place .BB' Y' = S.place .BB' Y' * S.place .AB'' X' := by
    intro X' Y'
    rw [← reindexOp_abBbBipartition_left S X', ← reindexOp_abBbBipartition_right S Y',
      ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul]
    congr 1
    rw [heteroKron_mul, heteroKron_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul]
  exact key X Y

end ProjectiveSetting

/-! ## The overlap identity -/

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
theorem overlap_identity_of_mem (P : AdmissibleParams) (W : PauliKind)
    {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP]
    (LM : Measurement (DegPoly P.toLdParams (P.m * P.d)) ιL)
    (PM : Measurement (ScalarQ P.toLdParams) ιP)
    (Φ : Op (ιL × PauliRegister P) → Op (ιP × PauliRegister P) → ℝ)
    (Ψ : Op ιL → Op ιP → ℝ)
    (line : LineDesc P.toLdParams) (u : Fin P.m → ScalarQ P.toLdParams)
    (hu : u ∈ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) ×
        DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (ιL × PauliRegister P)) (Y : Op (ιP × PauliRegister P)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y)
    (hΦr : ∀ (X : Op (ιL × PauliRegister P))
      (t : Finset (ScalarQ P.toLdParams × ScalarQ P.toLdParams))
      (Y : ScalarQ P.toLdParams × ScalarQ P.toLdParams → Op (ιP × PauliRegister P)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j))
    (hΦfact : ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d)) (b' b'' : ScalarQ P.toLdParams),
      Φ (heteroKron (LM.effect f') (tauLineProj P W line f''))
          (heteroKron (PM.effect b') (ProjectiveSetting.tauPointProj W u b'')) =
        Ψ (LM.effect f') (PM.effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0))
    (hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : DegPoly P.toLdParams (P.m * P.d),
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
        ((evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  let c : DegPoly P.toLdParams (P.m * P.d) → ℝ := fun f'' =>
    DistanceCalculus.stateQForm (eprState (PauliRegister P))
      (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
  let Pt : Option (ScalarQ P.toLdParams) → Op ιP := fun o => (PM.postprocess some).effect o
  have hPt_none : Pt none = 0 := by
    simp only [Pt]
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    apply Finset.sum_eq_zero
    intro a ha
    exact absurd (Finset.mem_filter.mp ha).2 (by simp)
  have hPt_some (b : ScalarQ P.toLdParams) : Pt (some b) = PM.effect b := by
    simp only [Pt]
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
    simp [Finset.filter_eq']
  have hc : ∑ f'', c f'' = 1 := sum_stateQForm_eprState_tauLineProj_one P W line
  have hc0 : ∀ f'', evalOpt line u f'' = none → c f'' = 0 := by
    intro f'' h
    simp only [c]
    rw [tauLineProj_eq_zero_of_evalOpt_none P W line u hu f'' h,
      heteroKron_zero_left, DistanceCalculus.stateQForm_zero]
  have hterm : ∀ (f : DegPoly P.toLdParams (P.m * P.d))
      (p : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d)),
      p.1 + p.2 = f →
      Φ (heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
          ((evalOpt line u f).elim 0 (fun a =>
            ∑ q ∈ Finset.univ.filter
              (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
              heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2))) =
        Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 := by
    intro f p hp
    rcases hf : evalOpt line u f with _ | a
    · rw [Option.elim_none, hΦ0]
      rcases h1 : evalOpt line u p.1 with _ | a'
      · rw [hPt_none, hΨ0, zero_mul]
      · have h2 : evalOpt line u p.2 = none := by
          rcases h2 : evalOpt line u p.2 with _ | b
          · rfl
          · exfalso
            have hsum := evalOpt_add_of_some h1 h2
            rw [hp, hf] at hsum
            exact absurd hsum (by simp)
        rw [hc0 p.2 h2, mul_zero]
    · rw [Option.elim_some, hΦr]
      simp_rw [hΦfact]
      rcases h2 : evalOpt line u p.2 with _ | c''
      · have h1 : evalOpt line u p.1 = none := by
          rcases h1 : evalOpt line u p.1 with _ | a'
          · rfl
          · exfalso
            have hsum : evalOpt line u (p.2 + p.1) = some a := by
              rw [add_comm, hp, hf]
            have h2' := evalOpt_left_of_add_some hsum h1
            rw [h2] at h2'
            exact absurd h2' (by simp)
        rw [h1, hPt_none, hΨ0, zero_mul]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [if_neg (by simp), mul_zero]
      · have hsum : evalOpt line u (p.1 + p.2) = some a := by rw [hp, hf]
        have h1 : evalOpt line u p.1 = some (a - c'') :=
          evalOpt_left_of_add_some hsum h2
        rw [h1, hPt_some]
        rw [Finset.sum_eq_single (a - c'', c'')]
        · change Ψ (LM.effect p.1) (PM.effect (a - c'')) *
            (if some c'' = some c'' then c p.2 else 0) =
              Ψ (LM.effect p.1) (PM.effect (a - c'')) * c p.2
          rw [if_pos rfl]
        · intro q hq hne
          rw [if_neg, mul_zero]
          intro heq
          apply hne
          have hq2 : q.2 = c'' := (Option.some_inj.mp heq).symm
          have hq1 : q.1 + q.2 = a := (Finset.mem_filter.mp hq).2
          ext
          · change q.1 = a - c''
            rw [← hq1, hq2, add_sub_cancel_right]
          · exact hq2
        · intro hnot
          exfalso
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_add_cancel a c''⟩)
  calc
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        ∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 := by
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [hΦl]
      exact Finset.sum_congr rfl fun p hp => hterm f p (Finset.mem_filter.mp hp).2
    _ = ∑ p : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d),
        Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2 :=
      Finset.sum_fiberwise Finset.univ
        (fun p : DegPoly P.toLdParams (P.m * P.d) ×
          DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2)
        (fun p => Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2)
    _ = ∑ f' : DegPoly P.toLdParams (P.m * P.d),
        Ψ (LM.effect f') (Pt (evalOpt line u f')) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun f' _ => ?_
      change ∑ y, Ψ (LM.effect f') (Pt (evalOpt line u f')) * c y =
        Ψ (LM.effect f') (Pt (evalOpt line u f'))
      rw [← Finset.mul_sum, hc, mul_one]
    _ = ∑ o : Option (ScalarQ P.toLdParams),
        ∑ f' ∈ Finset.univ.filter
          (fun f' : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f' = o),
          Ψ (LM.effect f') (Pt o) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun f' => evalOpt line u f')
        (fun f' => Ψ (LM.effect f') (Pt (evalOpt line u f')))]
      refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun f' hf' => ?_
      rw [(Finset.mem_filter.mp hf').2]
    _ = ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o) (Pt o) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect, hΨl]

/-- Off the line, both sides of the overlap identity vanish: no line
polynomial evaluates, so the selected point effects are zero and the
evaluation classes with a proper value are empty. -/
theorem overlap_identity_of_not_mem (P : AdmissibleParams) (W : PauliKind)
    {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP]
    (LM : Measurement (DegPoly P.toLdParams (P.m * P.d)) ιL)
    (PM : Measurement (ScalarQ P.toLdParams) ιP)
    (Φ : Op (ιL × PauliRegister P) → Op (ιP × PauliRegister P) → ℝ)
    (Ψ : Op ιL → Op ιP → ℝ)
    (line : LineDesc P.toLdParams) (u : Fin P.m → ScalarQ P.toLdParams)
    (hu : u ∉ line.pointSet)
    (hΦ0 : ∀ X, Φ X 0 = 0)
    (hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    (∑ f : DegPoly P.toLdParams (P.m * P.d),
      Φ (∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
        ((evalOpt line u f).elim 0 (fun a =>
          ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2)))) =
      ∑ o : Option (ScalarQ P.toLdParams),
        Ψ ((LM.postprocess (evalOpt line u)).effect o)
          ((PM.postprocess some).effect o) := by
  have hnone : ∀ f : DegPoly P.toLdParams (P.m * P.d), evalOpt line u f = none :=
    fun f => evalOpt_eq_none_of_not_mem hu f
  rw [Finset.sum_eq_zero fun f _ => by rw [hnone f, Option.elim_none, hΦ0]]
  symm
  refine Finset.sum_eq_zero fun o _ => ?_
  rcases o with _ | b
  · have hPt : (PM.postprocess some).effect none = 0 := by
      rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
      apply Finset.sum_eq_zero
      intro a ha
      exact absurd (Finset.mem_filter.mp ha).2 (by simp)
    rw [hPt, hΨ0]
  · have hempty : Finset.univ.filter
        (fun f' : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f' = some b) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro f' _ h
      rw [hnone f'] at h
      exact absurd h (by simp)
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect, hempty, Finset.sum_empty]
    simpa using hΨl ∅ (fun _ => 0) ((PM.postprocess some).effect (some b))

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The four placement pairs -/

theorem lineMeas_effect_isHermitian (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (line : LineDesc P.toLdParams)
    (f : DegPoly P.toLdParams (P.m * P.d)) :
    ((S.lineMeas side W line).effect f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((S.lineMeas side W line).pos f)).isHermitian

theorem pointMeas_effect_isHermitian (S : ProjectiveSetting P ε)
    (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (b : PauliScalar P) :
    ((S.pointMeas side W u).effect b).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas side W u).pos b)).isHermitian

theorem tauLineProj_isHermitian (W : PauliKind)
    (line : LineDesc P.toLdParams) (f : DegPoly P.toLdParams (P.m * P.d)) :
    (tauLineProj P W line f).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp (tauLineProj_nonneg P W line f)).isHermitian

theorem tauPointProj_isHermitian (W : PauliKind)
    (u : Fin P.m → PauliScalar P) (b : PauliScalar P) :
    (tauPointProj W u b).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp ((tauPointMeas W u).pos b)).isHermitian

set_option synthInstance.maxSize 400 in
theorem sum_stateQForm_evalClass_eq (S : ProjectiveSetting P ε)
    (pL pP : Placement) (W : PauliKind)
    (line : LineDesc P.toLdParams) (u : Fin P.m → PauliScalar P)
    (Ψ : Op (S.LocalSpace pL.side) → Op (S.LocalSpace pP.side) → ℝ)
    (hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op (S.LocalSpace pL.side))
      (B : Op (S.LocalSpace pP.side)), Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0)
    (hfact : u ∈ line.pointSet → ∀ (f' f'' : DegPoly P.toLdParams (P.m * P.d))
      (b' b'' : PauliScalar P),
      DistanceCalculus.stateQForm S.psiHat
        (S.place pL (heteroKron ((S.lineMeas pL.side W line).effect f')
          (tauLineProj P W line f'')) *
          S.place pP (heteroKron ((S.pointMeas pP.side W u).effect b')
            (tauPointProj W u b''))) =
        Ψ ((S.lineMeas pL.side W line).effect f') ((S.pointMeas pP.side W u).effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0)) :
    ∑ o : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (S.place pL ((S.lineEvalMeasExp pL.side W line u).effect o) *
            S.place pP ((S.pointMeasExpOption pP.side W u).effect o)) =
      ∑ o : Option (PauliScalar P),
        Ψ ((S.lineEvalMeas pL.side W line u).effect o)
          ((S.pointMeasOption pP.side W u).effect o) := by
  let Φ : Op (S.ExpandedLocalSpace pL.side) → Op (S.ExpandedLocalSpace pP.side) → ℝ :=
    fun X Y => DistanceCalculus.stateQForm S.psiHat (S.place pL X * S.place pP Y)
  have hΦ0 : ∀ X, Φ X 0 = 0 := fun X => by
    simp only [Φ, place_zero, mul_zero, DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d)))
      (X : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d) →
        Op (S.ExpandedLocalSpace pL.side))
      (Y : Op (S.ExpandedLocalSpace pP.side)),
      Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := fun s X Y => by
    simp only [Φ, place_finset_sum, Finset.sum_mul, DistanceCalculus.stateQForm_finset_sum]
  have hΦr : ∀ (X : Op (S.ExpandedLocalSpace pL.side))
      (t : Finset (PauliScalar P × PauliScalar P))
      (Y : PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace pP.side)),
      Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := fun X t Y => by
    simp only [Φ, place_finset_sum, Finset.mul_sum, DistanceCalculus.stateQForm_finset_sum]
  calc
    _ = ∑ o : Option (PauliScalar P),
        ∑ f ∈ Finset.univ.filter
          (fun f : DegPoly P.toLdParams (P.m * P.d) => evalOpt line u f = o),
          Φ (S.expLineOp pL.side W line f)
            ((S.pointMeasExpOption pP.side W u).effect (evalOpt line u f)) := by
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [Φ, lineEvalMeasExp_effect, place_finset_sum, Finset.sum_mul,
        DistanceCalculus.stateQForm_finset_sum]
      exact Finset.sum_congr rfl fun f hf => by rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : DegPoly P.toLdParams (P.m * P.d),
        Φ (S.expLineOp pL.side W line f)
          ((evalOpt line u f).elim 0 (fun a =>
            ∑ q ∈ Finset.univ.filter
              (fun q : PauliScalar P × PauliScalar P => q.1 + q.2 = a),
              heteroKron ((S.pointMeas pP.side W u).effect q.1)
                (tauPointProj W u q.2))) := by
      refine (Finset.sum_fiberwise Finset.univ (fun f => evalOpt line u f) _).trans
        (Finset.sum_congr rfl fun f _ => congrArg (Φ _) ?_)
      rcases evalOpt line u f with _ | a
      · exact S.pointMeasExpOption_effect_none pP.side W u
      · exact (S.pointMeasExpOption_effect_some pP.side W u a).trans
          (S.expPointOp_eq_convolution pP.side W u a)
    _ = _ := by
      by_cases hu : u ∈ line.pointSet
      · exact overlap_identity_of_mem P W (S.lineMeas pL.side W line)
          (S.pointMeas pP.side W u) Φ Ψ line u hu hΦ0 hΦl hΦr (hfact hu) hΨl hΨ0
      · exact overlap_identity_of_not_mem P W (S.lineMeas pL.side W line)
          (S.pointMeas pP.side W u) Φ Ψ line u hu hΦ0 hΨl hΨ0

end ProjectiveSetting

end

end MIPStarRE.QPBT
