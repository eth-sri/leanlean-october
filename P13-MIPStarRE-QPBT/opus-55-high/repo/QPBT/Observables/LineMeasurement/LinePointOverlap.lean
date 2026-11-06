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

variable (S : ProjectiveSetting P ε)

/-- A register placement respects finite sums of operators.
Formalization-only auxiliary for the register placements of
`def:symmetric-equivalents`; the source uses this additivity without stating
it. -/
theorem place_finset_sum (p : Placement)
    {γ : Type*} (s : Finset γ) (O : γ → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ g ∈ s, O g) = ∑ g ∈ s, S.place p (O g) := by
  ext i j
  cases p <;> simp only [place, Matrix.sum_apply, Finset.sum_mul, Finset.mul_sum]

/-- A register placement of the zero operator is zero. -/
theorem place_zero (p : Placement) :
    S.place p (0 : Op (S.ExpandedLocalSpace p.side)) = 0 := by
  ext i j
  cases p <;> simp [place]

/-! ## Effects of the completed measurement families -/

/-- The completed expanded point measurement agrees with the expanded point
measurement on proper values. -/
theorem pointMeasExpOption_effect_some (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P)
    (b : PauliScalar P) :
    (S.pointMeasExpOption side W u).effect (some b) =
      (S.pointMeasExp side W u).effect b := by
  unfold pointMeasExpOption
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect]
  simp [Finset.filter_eq']

/-- The completed expanded point measurement assigns zero to `none`. -/
theorem pointMeasExpOption_effect_none (side : PlayerSide) (W : PauliKind) (u : Fin P.m → PauliScalar P) :
    (S.pointMeasExpOption side W u).effect none = 0 := by
  grind [pointMeasExpOption, MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_eq_zero, absurd]

/-- The completed expanded point effects, written through the convolution
form of the expanded point measurement. -/
theorem pointMeasExpOption_effect_eq_elim (side : PlayerSide) (W : PauliKind)
    (u : Fin P.m → PauliScalar P) : ∀ o, (S.pointMeasExpOption side W u).effect o =
      o.elim 0 fun a => ∑ q ∈ Finset.univ.filter
          (fun q : PauliScalar P × PauliScalar P => q.1 + q.2 = a),
          heteroKron ((S.pointMeas side W u).effect q.1) (tauPointProj W u q.2)
  | none => S.pointMeasExpOption_effect_none side W u
  | some a => (S.pointMeasExpOption_effect_some side W u a).trans (S.expPointOp_eq_convolution side W u a)


/-! ## Factorization of opposite placements with distinct Pauli factors -/

set_option synthInstance.maxSize 400 in
/-- The product of opposite `AA'` and `BA''` placements with distinct Pauli
factors separates into the strategy product, the first EPR-pair product, and
the identity on the second EPR pair. -/
theorem reindexOp_sixRegShuffle_place_AA'_mul_BA''_two
    (A : Op S.toStrategy.ιA)
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
/-- The product of opposite `AB''` and `BB'` placements with distinct Pauli
factors separates into the strategy product, the identity on the first EPR
pair, and the second EPR-pair product. -/
theorem reindexOp_sixRegShuffle_place_AB''_mul_BB'_two
    (A : Op S.toStrategy.ιA)
    (B : Op S.toStrategy.ιB) (T T' : Op (PauliRegister P)) :
    reindexOp (sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
        (S.place .AB'' (heteroKron A T) * S.place .BB' (heteroKron B T')) =
      heteroKron (heteroKron (heteroKron A B)
          (1 : Op (PauliRegister P × PauliRegister P)))
        (heteroKron T' T) := by
  rw [WinImplications.reindexOp_mul,
    reindexOp_sixRegShuffle_place_AB''_heteroKron,
    reindexOp_sixRegShuffle_place_BB'_heteroKron]
  simp [heteroKron_mul, heteroKron_one_one]

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AA'`--`BA''` product with distinct
Pauli factors factors into the strategy overlap and the first EPR-pair
overlap. This is the factorization behind the ancillary consistency in items
2 and 3 of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem stateQForm_place_AA'_mul_BA''_two (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T T' : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' (heteroKron A T) * S.place .BA'' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T T') := by
  grind [heteroKron, heteroKron_isHermitian, psiHat_eq_reindexState, WinImplications.stateQForm_reindexState, reindexOp_sixRegShuffle_place_AA'_mul_BA''_two, stateQForm_vecTensor_heteroKron, Matrix.isHermitian_one, DistanceCalculus.stateQForm_one, eprState_norm]

set_option synthInstance.maxSize 400 in
/-- The diagonal quadratic form for the `AB''`--`BB'` product with distinct
Pauli factors factors into the strategy overlap and the second EPR-pair
overlap, the Pauli factor of `BB'` acting on the first half of the pair.
Paper `14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem stateQForm_place_AB''_mul_BB'_two (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB)
    (T T' : Op (PauliRegister P)) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hT : T.IsHermitian) (hT' : T'.IsHermitian) :
    DistanceCalculus.stateQForm S.psiHat
        (S.place .AB'' (heteroKron A T) * S.place .BB' (heteroKron B T')) =
      DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
        DistanceCalculus.stateQForm (eprState (PauliRegister P))
          (heteroKron T' T) := by
  have hAB : (heteroKron A B).IsHermitian :=
    heteroKron_isHermitian A B hA hB
  grind [heteroKron, heteroKron_isHermitian, psiHat_eq_reindexState, WinImplications.stateQForm_reindexState, reindexOp_sixRegShuffle_place_AB''_mul_BB'_two, stateQForm_vecTensor_heteroKron, Matrix.isHermitian_one, DistanceCalculus.stateQForm_one, eprState_norm]

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AA'` and on `BA''` commute. -/
theorem place_AA'_mul_place_BA''_comm (X : Op (S.ExpandedLocalSpace .alice))
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
  simp_all

set_option synthInstance.maxSize 400 in
/-- Operators placed on `AB''` and on `BB'` commute. -/
theorem place_AB''_mul_place_BB'_comm (X : Op (S.ExpandedLocalSpace .alice))
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
  simp_all

end ProjectiveSetting

/-! ## The overlap identity -/

variable (P : AdmissibleParams) (W : PauliKind) {ιL ιP : Type*} [Fintype ιL] [DecidableEq ιL] [Fintype ιP] [DecidableEq ιP] (LM : Measurement (DegPoly P.toLdParams (P.m * P.d)) ιL) (PM : Measurement (ScalarQ P.toLdParams) ιP) (Ψ : Op ιL → Op ιP → ℝ) (line : LineDesc P.toLdParams) (u : Fin P.m → ScalarQ P.toLdParams)

/-- The overlap identity for a diagonal quadratic form of a product of two
additive placements, summed over the evaluation classes: the expanded overlap
of the evaluation classes with the completed point effects equals the strategy
overlap `Ψ`. Paper `14_analysis_of_the_pauli_basis_test.tex:534-545`. -/
theorem overlap_identity {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (φ : EuclideanSpace ℂ Ω)
    (pl : Op (ιL × PauliRegister P) → Op Ω) (pr : Op (ιP × PauliRegister P) → Op Ω)
    (hpl : ∀ {γ : Type} (s : Finset γ) (X : γ → _), pl (∑ i ∈ s, X i) = ∑ i ∈ s, pl (X i))
    (hpr : ∀ {γ : Type} (s : Finset γ) (X : γ → _), pr (∑ i ∈ s, X i) = ∑ i ∈ s, pr (X i))
    (L : DegPoly P.toLdParams (P.m * P.d) → Op (ιL × PauliRegister P))
    (hL : ∀ f, L f = ∑ p ∈ Finset.univ.filter
          (fun p : DegPoly P.toLdParams (P.m * P.d) ×
            DegPoly P.toLdParams (P.m * P.d) => p.1 + p.2 = f),
          heteroKron (LM.effect p.1) (tauLineProj P W line p.2))
    (Pt : Option (ScalarQ P.toLdParams) → Op (ιP × PauliRegister P))
    (hPt : ∀ o, Pt o = o.elim 0 fun a => ∑ q ∈ Finset.univ.filter
            (fun q : ScalarQ P.toLdParams × ScalarQ P.toLdParams => q.1 + q.2 = a),
            heteroKron (PM.effect q.1) (ProjectiveSetting.tauPointProj W u q.2))
    (hfact : u ∈ line.pointSet → ∀ f' f'' b' b'',
      DistanceCalculus.stateQForm φ (pl (heteroKron (LM.effect f') (tauLineProj P W line f'')) *
          pr (heteroKron (PM.effect b') (ProjectiveSetting.tauPointProj W u b''))) =
        Ψ (LM.effect f') (PM.effect b') *
          (if evalOpt line u f'' = some b'' then
            DistanceCalculus.stateQForm (eprState (PauliRegister P))
              (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
          else 0))
    (hΨl : ∀ (s : Finset (DegPoly P.toLdParams (P.m * P.d)))
      (A : DegPoly P.toLdParams (P.m * P.d) → Op ιL) (B : Op ιP),
      Ψ (∑ i ∈ s, A i) B = ∑ i ∈ s, Ψ (A i) B)
    (hΨ0 : ∀ A, Ψ A 0 = 0) :
    ∑ o, DistanceCalculus.stateQForm φ
        (pl (∑ f ∈ Finset.univ.filter (fun f => evalOpt line u f = o), L f) * pr (Pt o)) =
      ∑ o, Ψ ((LM.postprocess (evalOpt line u)).effect o) ((PM.postprocess some).effect o) := by
  have h0 : pr 0 = 0 := by simpa using hpr (γ := Unit) ∅ 0
  let Φ := fun X Y => DistanceCalculus.stateQForm φ (pl X * pr Y)
  have hΦ0 : ∀ X, Φ X 0 = 0 := by simp [Φ, h0, DistanceCalculus.stateQForm_zero]
  have hΦl : ∀ {γ : Type} (s : Finset γ) (X : γ → _) Y, Φ (∑ i ∈ s, X i) Y = ∑ i ∈ s, Φ (X i) Y := by
    simp only [Φ, hpl, Finset.sum_mul, DistanceCalculus.stateQForm_finset_sum, implies_true]
  have hΦr : ∀ {γ : Type} X (t : Finset γ) (Y : γ → _), Φ X (∑ j ∈ t, Y j) = ∑ j ∈ t, Φ X (Y j) := by
    simp only [Φ, hpr, Finset.mul_sum, DistanceCalculus.stateQForm_finset_sum, implies_true]
  trans ∑ f, Φ (L f) (Pt (evalOpt line u f))
  · rw [← Finset.sum_fiberwise Finset.univ (evalOpt line u)]
    refine Finset.sum_congr rfl fun o _ => ?_
    exact (hΦl _ _ _).trans (Finset.sum_congr rfl fun f hf => by rw [(Finset.mem_filter.mp hf).2])
  simp only [hL, hPt]
  by_cases hu : u ∈ line.pointSet
  · have hΦfact := hfact hu
    let c : DegPoly P.toLdParams (P.m * P.d) → ℝ := fun f'' =>
      DistanceCalculus.stateQForm (eprState (PauliRegister P))
        (heteroKron (tauLineProj P W line f'') (1 : Op (PauliRegister P)))
    let Pt : Option (ScalarQ P.toLdParams) → Op ιP := fun o => (PM.postprocess some).effect o
    have hPt_none : Pt none = 0 := by
      simp only [Pt, MIPStarRE.Quantum.Measurement.postprocess_effect]; simp
    have hPt_some (b : ScalarQ P.toLdParams) : Pt (some b) = PM.effect b := by
      simp only [Pt, MIPStarRE.Quantum.Measurement.postprocess_effect]; simp [Finset.filter_eq']
    have hc : ∑ f'', c f'' = 1 := sum_stateQForm_eprState_tauLineProj_one P W line
    have hc0 : ∀ f'', evalOpt line u f'' = none → c f'' = 0 := by
      intro f'' h
      simp [c, tauLineProj_eq_zero_of_evalOpt_none P W line u hu f'' h, heteroKron_zero_left,
        DistanceCalculus.stateQForm_zero]
    trans ∑ p : DegPoly P.toLdParams (P.m * P.d) × DegPoly P.toLdParams (P.m * P.d),
      Ψ (LM.effect p.1) (Pt (evalOpt line u p.1)) * c p.2
    · rw [← Finset.sum_fiberwise Finset.univ fun p : DegPoly P.toLdParams (P.m * P.d) × _ => p.1 + p.2]
      refine Finset.sum_congr rfl fun f _ => (hΦl _ _ _).trans (Finset.sum_congr rfl fun p hp => ?_)
      replace hp := (Finset.mem_filter.mp hp).2
      rcases hf : evalOpt line u f with _ | a
      · rw [Option.elim_none, hΦ0]
        rcases h1 : evalOpt line u p.1 with _ | a'
        · simp_all
        · have h2 : evalOpt line u p.2 = none := by
            rcases h2 : evalOpt line u p.2 with _ | b
            · rfl
            · have hsum := evalOpt_add_of_some h1 h2
              simp_all
          simp_all
      · rw [Option.elim_some, hΦr]
        simp_rw [Φ, hΦfact]
        rcases h2 : evalOpt line u p.2 with _ | c''
        · simp_all
        · have hsum : evalOpt line u (p.1 + p.2) = some a := by rw [hp, hf]
          have h1 : evalOpt line u p.1 = some (a - c'') :=
            evalOpt_left_of_add_some hsum h2
          rw [h1, hPt_some]
          rw [Finset.sum_eq_single (a - c'', c'')]
          · grind
          · grind
          simp
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hc, mul_one]
    rw [← Finset.sum_fiberwise Finset.univ (evalOpt line u)]
    exact Finset.sum_congr rfl fun o _ => (Finset.sum_congr rfl fun f hf => by
      rw [(Finset.mem_filter.mp hf).2]).trans (hΨl _ _ _).symm
  · have : ∀ B, Ψ 0 B = 0 := fun B => by simpa using hΨl ∅ (fun _ => 0) B
    simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, evalOpt_eq_none_of_not_mem hu,
      Option.elim_none, hΦ0, Finset.sum_const_zero, Fintype.sum_option]
    simp [this, hΨ0]

end

end MIPStarRE.QPBT
