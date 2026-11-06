module

public import QPBT.Observables.LineMeasurement.BipartiteTransport

/-!
# Expanded line measurements
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- The square-root error exhibited by the expanded-line consistency proof. -/
noncomputable def deltaLine (ε : ℝ) : ℝ :=
  Real.sqrt ε

set_option synthInstance.maxSize 400 in
private theorem evalClassDist_bipartition_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε)
    (placeA : Op (S.toStrategy.ιA × PauliRegister P) →
      Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (placeB : Op (S.toStrategy.ιB × PauliRegister P) →
      Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      (S.toStrategy.ιA × PauliRegister P) ×
        ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)))
    (A : LineDesc P.toLdParams × (Fin P.m → PauliScalar P) →
      Measurement (Option (PauliScalar P)) (S.toStrategy.ιA × PauliRegister P))
    (B : LineDesc P.toLdParams × (Fin P.m → PauliScalar P) →
      Measurement (Option (PauliScalar P)) (S.toStrategy.ιB × PauliRegister P))
    (A0 : LineDesc P.toLdParams × (Fin P.m → PauliScalar P) →
      Measurement (Option (PauliScalar P)) S.toStrategy.ιA)
    (B0 : LineDesc P.toLdParams × (Fin P.m → PauliScalar P) →
      Measurement (Option (PauliScalar P)) S.toStrategy.ιB)
    (hnorm : ∀ X Y,
      ‖applyOperatorToState (placeA X - placeB Y) S.psiHat‖ =
        ‖applyOperatorToState
          (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
              (PauliRegister P × PauliRegister P))) -
            heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
              (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P))))
          (reindexState e S.psiHat)‖)
    (hmul : ∀ X Y,
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
        (heteroKron X (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))) *
          heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
            (heteroKron Y (1 : Op (PauliRegister P × PauliRegister P)))) =
        DistanceCalculus.stateQForm S.psiHat (placeA X * placeB Y))
    (hov : ∀ sample : LineDesc P.toLdParams × (Fin P.m → PauliScalar P),
      ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.psiHat
          (placeA ((A sample).effect a) * placeB ((B sample).effect a)) =
      ∑ a : Option (PauliScalar P),
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((A0 sample).effect a) ((B0 sample).effect a)))
    (hcons : consistencyDefect (linePointDist P.toLdParams)
      (fun sample a => heteroKron ((A0 sample).effect a) 1)
      (fun sample a => heteroKron 1 ((B0 sample).effect a))
      S.toStrategy.ψ ≤ 86 * ε) :
    opFamilyDistSq (linePointDist P.toLdParams)
      (fun sample a => placeA ((A sample).effect a))
      (fun sample a => placeB ((B sample).effect a))
      S.psiHat ≤ 348 * deltaLine ε := by
  let μ := linePointDist P.toLdParams
  let B' := fun sample => DistanceCalculus.leftPlacedMeasurement
    (ιB := PauliRegister P × PauliRegister P) (B sample)
  have hμ : μ.IsProbability := linePointDist_isProbability P.toLdParams
  have heq : opFamilyDistSq μ
      (fun sample a => placeA ((A sample).effect a))
      (fun sample a => placeB ((B sample).effect a)) S.psiHat =
      opFamilyDistSq μ
        (fun sample a => heteroKron ((A sample).effect a) 1)
        (fun sample a => heteroKron 1 ((B' sample).effect a))
        (reindexState e S.psiHat) :=
    avgOver_congr _ _ _ fun sample => Finset.sum_congr rfl fun a _ => by
      dsimp only [B', DistanceCalculus.leftPlacedMeasurement, Measurement.ofSumEqOne]
      rw [hnorm]
  have hle4 : opFamilyDistSq μ
      (fun sample a => placeA ((A sample).effect a))
      (fun sample a => placeB ((B sample).effect a)) S.psiHat ≤ 4 := by
    rw [heq]
    exact DistanceCalculus.opFamilyDistSq_placed_le_four μ hμ A B' _
      (ProjectiveSetting.norm_reindexState_psiHat S e)
  have hle2 : opFamilyDistSq μ
      (fun sample a => placeA ((A sample).effect a))
      (fun sample a => placeB ((B sample).effect a)) S.psiHat ≤ 2 * (86 * ε) := by
    rw [heq]
    refine (DistanceCalculus.opFamilyDistSq_placed_le_two_mul_one_sub_overlap μ hμ
      A B' _ (ProjectiveSetting.norm_reindexState_psiHat S e)).trans ?_
    refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ hcons) (by norm_num)
    refine (congrArg (1 - ·) (avgOver_congr _ _ _ fun sample => ?_)).trans
      (DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
        (fun sample => DistanceCalculus.leftPlacedMeasurement (A0 sample))
        (fun sample => DistanceCalculus.rightPlacedMeasurement (B0 sample))
        S.toStrategy.ψ hμ S.toStrategy.ψ_norm).symm
    refine (Finset.sum_congr rfl fun a _ => hmul _ _).trans ((hov sample).trans ?_)
    exact Finset.sum_congr rfl fun a _ =>
      (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm
  calc
    _ ≤ (2 * 86 + 4) * Real.sqrt ε :=
      le_mul_sqrt_of_le_mul_of_le_four (by norm_num)
        (DistanceCalculus.opFamilyDistSq_nonneg _ _ _ _)
        (by rw [mul_assoc]; exact hle2) hle4
    _ ≤ 348 * deltaLine ε := by
      unfold deltaLine
      exact mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg ε)

theorem exp_line_point_cons_explicit' :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ → ∀ W : PauliKind,
      opFamilyDistSq (linePointDist P.toLdParams)
        (fun sample a => S.place p₁
          ((S.lineEvalMeasExp p₁.side W sample.1 sample.2).effect a))
        (fun sample a => S.place p₂
          ((S.pointMeasExpOption p₂.side W sample.2).effect a))
        S.psiHat ≤ 348 * deltaLine ε := by
  intro P ε S p₁ p₂ hopp W
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · exact evalClassDist_bipartition_le S (S.place .AA') (S.place .BA'')
      (ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
      (fun s => S.lineEvalMeasExp .alice W s.1 s.2)
      (fun s => S.pointMeasExpOption .bob W s.2)
      (fun s => S.lineEvalMeas .alice W s.1 s.2)
      (fun s => S.pointMeasOption .bob W s.2)
      (ProjectiveSetting.norm_place_AA'_sub_place_BA'' S)
      (ProjectiveSetting.stateQForm_aaBa_mul_eq S)
      (fun s => ProjectiveSetting.sum_stateQForm_evalClass_eq S .AA' .BA'' W s.1 s.2
        (fun L Q => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron L Q))
        (fun _ _ _ => by
          simp only [MagicSquareRigidity.heteroKron_finset_sum_left,
            DistanceCalculus.stateQForm_finset_sum])
        (fun _ => by simp only [heteroKron_zero_right, DistanceCalculus.stateQForm_zero])
        (fun hu f' f'' b' b'' => by
          rw [ProjectiveSetting.stateQForm_place_AA'_mul_BA''_two S _ _ _ _
              (ProjectiveSetting.lineMeas_effect_isHermitian S .alice W s.1 f')
              (ProjectiveSetting.pointMeas_effect_isHermitian S .bob W s.2 b')
              (ProjectiveSetting.tauLineProj_isHermitian W s.1 f'')
              (ProjectiveSetting.tauPointProj_isHermitian W s.2 b''),
            stateQForm_eprState_tauLineProj_tauPointProj P W s.1 s.2 hu f'' b'']))
      (WinImplications.win_low_degree_explicit P ε S S.eps_nonneg W)
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    exact evalClassDist_bipartition_le S (S.place .AA') (S.place .BA'')
      (ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
      (fun s => S.pointMeasExpOption .alice W s.2)
      (fun s => S.lineEvalMeasExp .bob W s.1 s.2)
      (fun s => S.pointMeasOption .alice W s.2)
      (fun s => S.lineEvalMeas .bob W s.1 s.2)
      (ProjectiveSetting.norm_place_AA'_sub_place_BA'' S)
      (ProjectiveSetting.stateQForm_aaBa_mul_eq S)
      (fun s => (Finset.sum_congr rfl fun a _ =>
        congrArg (DistanceCalculus.stateQForm S.psiHat)
          (ProjectiveSetting.place_AA'_mul_place_BA''_comm S _ _)).trans
        (ProjectiveSetting.sum_stateQForm_evalClass_eq S .BA'' .AA' W s.1 s.2
          (fun L Q => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron Q L))
          (fun _ _ _ => by
            simp only [MagicSquareRigidity.heteroKron_finset_sum_right,
              DistanceCalculus.stateQForm_finset_sum])
          (fun _ => by simp only [heteroKron_zero_left, DistanceCalculus.stateQForm_zero])
          (fun hu f' f'' b' b'' => by
            rw [← ProjectiveSetting.place_AA'_mul_place_BA''_comm S,
              ProjectiveSetting.stateQForm_place_AA'_mul_BA''_two S _ _ _ _
                (ProjectiveSetting.pointMeas_effect_isHermitian S .alice W s.2 b')
                (ProjectiveSetting.lineMeas_effect_isHermitian S .bob W s.1 f')
                (ProjectiveSetting.tauPointProj_isHermitian W s.2 b'')
                (ProjectiveSetting.tauLineProj_isHermitian W s.1 f''),
              stateQForm_eprState_tauPointProj_tauLineProj P W s.1 s.2 hu f'' b''])))
      (WinImplications.win_low_degree_interchanged_explicit P ε S S.eps_nonneg W)
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    exact evalClassDist_bipartition_le S (S.place .AB'') (S.place .BB')
      (ProjectiveSetting.abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
      (fun s => S.pointMeasExpOption .alice W s.2)
      (fun s => S.lineEvalMeasExp .bob W s.1 s.2)
      (fun s => S.pointMeasOption .alice W s.2)
      (fun s => S.lineEvalMeas .bob W s.1 s.2)
      (ProjectiveSetting.norm_place_AB''_sub_place_BB' S)
      (ProjectiveSetting.stateQForm_abBb_mul_eq S)
      (fun s => (Finset.sum_congr rfl fun a _ =>
        congrArg (DistanceCalculus.stateQForm S.psiHat)
          (ProjectiveSetting.place_AB''_mul_place_BB'_comm S _ _)).trans
        (ProjectiveSetting.sum_stateQForm_evalClass_eq S .BB' .AB'' W s.1 s.2
          (fun L Q => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron Q L))
          (fun _ _ _ => by
            simp only [MagicSquareRigidity.heteroKron_finset_sum_right,
              DistanceCalculus.stateQForm_finset_sum])
          (fun _ => by simp only [heteroKron_zero_left, DistanceCalculus.stateQForm_zero])
          (fun hu f' f'' b' b'' => by
            rw [← ProjectiveSetting.place_AB''_mul_place_BB'_comm S,
              ProjectiveSetting.stateQForm_place_AB''_mul_BB'_two S _ _ _ _
                (ProjectiveSetting.pointMeas_effect_isHermitian S .alice W s.2 b')
                (ProjectiveSetting.lineMeas_effect_isHermitian S .bob W s.1 f')
                (ProjectiveSetting.tauPointProj_isHermitian W s.2 b'')
                (ProjectiveSetting.tauLineProj_isHermitian W s.1 f''),
              stateQForm_eprState_tauLineProj_tauPointProj P W s.1 s.2 hu f'' b''])))
      (WinImplications.win_low_degree_interchanged_explicit P ε S S.eps_nonneg W)
  · exact evalClassDist_bipartition_le S (S.place .AB'') (S.place .BB')
      (ProjectiveSetting.abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
      (fun s => S.lineEvalMeasExp .alice W s.1 s.2)
      (fun s => S.pointMeasExpOption .bob W s.2)
      (fun s => S.lineEvalMeas .alice W s.1 s.2)
      (fun s => S.pointMeasOption .bob W s.2)
      (ProjectiveSetting.norm_place_AB''_sub_place_BB' S)
      (ProjectiveSetting.stateQForm_abBb_mul_eq S)
      (fun s => ProjectiveSetting.sum_stateQForm_evalClass_eq S .AB'' .BB' W s.1 s.2
        (fun L Q => DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron L Q))
        (fun _ _ _ => by
          simp only [MagicSquareRigidity.heteroKron_finset_sum_left,
            DistanceCalculus.stateQForm_finset_sum])
        (fun _ => by simp only [heteroKron_zero_right, DistanceCalculus.stateQForm_zero])
        (fun hu f' f'' b' b'' => by
          rw [ProjectiveSetting.stateQForm_place_AB''_mul_BB'_two S _ _ _ _
              (ProjectiveSetting.lineMeas_effect_isHermitian S .alice W s.1 f')
              (ProjectiveSetting.pointMeas_effect_isHermitian S .bob W s.2 b')
              (ProjectiveSetting.tauLineProj_isHermitian W s.1 f'')
              (ProjectiveSetting.tauPointProj_isHermitian W s.2 b''),
            stateQForm_eprState_tauPointProj_tauLineProj P W s.1 s.2 hu f'' b'']))
      (WinImplications.win_low_degree_explicit P ε S S.eps_nonneg W)

end

end MIPStarRE.QPBT
