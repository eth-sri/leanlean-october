module

public import QPBT.Observables.ExpandedPlacement

/-!
# Approximate commutation of the expanded point projections

The trace-coarse-grained expanded point projections approximately commute on
each of the four register placements.  The commutator of the two projections is
a scalar multiple of a factorized operator whose strategy factor is the twisted
commutator of the two point observables and whose Pauli factor is a product of
generalized Pauli observables; the latter is an isometry, so the placement
bookkeeping of `ExpandedPlacement` reduces the estimate to the twisted
commutation relation of `lem:qld-win-implications-obs` on the corresponding
player side.  Both player sides are treated explicitly.

## References

The declarations prove item 2 of `lem:qld-comm-cons` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:466-505`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section
variable {K ι : Type*} [Field K]


/-! ## Algebraic preliminaries -/

/-- The generalized Pauli observables are self-adjoint. This identity supports
`lem:qld-comm-cons`. Blueprint `lem:twisted-commutation`,
paper `references/qpbt-paper/04_preliminaries.tex:1052-1096`. -/
theorem tauObservable_conjTranspose  [Finite K]
    [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι] [DecidableEq ι]
    (W : PauliKind) (v : ι → K) :
    (tauObservable W v)ᴴ = tauObservable W v := by
  cases nonempty_fintype K
  rw [tauObservable_eq_sum_pauliProj, Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Matrix.conjTranspose_smul, star_phaseSign]
  congr 1
  exact (Matrix.posSemidef_vecMulVec_self_star (pauliVec W e)).isHermitian.eq

/-- The generalized Pauli observables are reflections. Blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1089`. -/
theorem tauObservable_conjTranspose_mul_self 
    [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] [Fintype ι]
    [DecidableEq ι] (W : PauliKind) (v : ι → K) :
    (tauObservable W v)ᴴ * tauObservable W v = 1 := by
  rw [tauObservable_conjTranspose, tauObservable_sq]

namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

/-! ## The commutator of two expanded point projections -/

/-- The Pauli-register factor of the expanded `X` observable at a tuple. -/
noncomputable def tauX (P : AdmissibleParams) (ω : PauliTuple P) :
    Op (PauliRegister P) :=
  tauObservable .X (fun h => ω.2.2.1 * indicatorVec ω.1 h)

/-- The Pauli-register factor of the expanded `Z` observable at a tuple. -/
noncomputable def tauZ (P : AdmissibleParams) (ω : PauliTuple P) :
    Op (PauliRegister P) :=
  tauObservable .Z (fun h => ω.2.2.2 * indicatorVec ω.2.1 h)

/-- The product of the two Pauli-register factors is an isometry. Blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`references/qpbt-paper/04_preliminaries.tex:1088-1095`. -/
theorem tauX_mul_tauZ_isometry (P : AdmissibleParams) (ω : PauliTuple P) :
    (tauX P ω * tauZ P ω)ᴴ * (tauX P ω * tauZ P ω) = 1 :=
  WinImplications.mul_conjTranspose_mul_self
    (tauObservable_conjTranspose_mul_self _ _)
    (tauObservable_conjTranspose_mul_self _ _)

/-- The two Pauli-register factors commute up to the tuple's commutation sign.
This is the exact half of the argument of `lem:qld-comm-cons`; blueprint
`ch11_qpbt_algebra.tex:596-644`, paper
`14_analysis_of_the_pauli_basis_test.tex:495-505`. -/
theorem tauZ_mul_tauX (P : AdmissibleParams) (ω : PauliTuple P) :
    tauZ P ω * tauX P ω =
      phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
        (tauX P ω * tauZ P ω) := by
  have h := tauObservable_X_mul_Z (K := PauliScalar P)
    (fun h => ω.2.2.1 * indicatorVec ω.1 h)
    (fun h => ω.2.2.2 * indicatorVec ω.2.1 h)
  have hg : binTrace (PauliScalar P)
      (dotProduct (fun h => ω.2.2.1 * indicatorVec ω.1 h)
        (fun h => ω.2.2.2 * indicatorVec ω.2.1 h)) =
      gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2 := rfl
  rw [hg, show (tauObservable .X fun k => ω.2.2.1 * indicatorVec ω.1 k) =
      tauX P ω from rfl,
    show (tauObservable .Z fun k => ω.2.2.2 * indicatorVec ω.2.1 k) =
      tauZ P ω from rfl] at h
  have hsq := phaseSign_mul_self (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)
  calc tauZ P ω * tauX P ω
      = (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) *
          phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2)) •
            (tauZ P ω * tauX P ω) := by rw [hsq, one_smul]
    _ = phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
            (tauZ P ω * tauX P ω)) := by rw [smul_smul]
    _ = phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          (tauX P ω * tauZ P ω) := by rw [← h]

/-- The twisted commutator of the two point observables at a tuple. -/
noncomputable def twistedCommutator (S : ProjectiveSetting P ε)
    (side : PlayerSide) (ω : PauliTuple P) : Op (S.LocalSpace side) :=
  S.pointObs side .X ω.2.2.1 ω.1 * S.pointObs side .Z ω.2.2.2 ω.2.1 -
    phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
      (S.pointObs side .Z ω.2.2.2 ω.2.1 * S.pointObs side .X ω.2.2.1 ω.1)
variable (S : ProjectiveSetting P ε)


/-- The commutator of the two expanded observables factorizes with the twisted
commutator of the point observables on the strategy register. This is the
display following `eq:lc-23` in the proof of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:487-505`, blueprint
`ch14_qpbt_observables.tex:1164-1175`. -/
theorem expObs_commutator  (side : PlayerSide)
    (ω : PauliTuple P) :
    S.expObs side .X ω.2.2.1 ω.1 * S.expObs side .Z ω.2.2.2 ω.2.1 -
        S.expObs side .Z ω.2.2.2 ω.2.1 * S.expObs side .X ω.2.2.1 ω.1 =
      heteroKron (S.twistedCommutator side ω) (tauX P ω * tauZ P ω) := by
  rw [expObs, expObs, heteroKron_mul, heteroKron_mul, show tauObservable .X (fun h => ω.2.2.1 * indicatorVec ω.1 h) =
    tauX P ω from rfl,
    show tauObservable .Z (fun h => ω.2.2.2 * indicatorVec ω.2.1 h) =
      tauZ P ω from rfl, tauZ_mul_tauX, MagicSquareRigidity.heteroKron_smul_right,
    ← WinImplications.heteroKron_smul_left,
    ← heteroKron_sub_left, twistedCommutator]
theorem place_smul  (p : Placement) (c : ℂ)
    (O : Op (S.ExpandedLocalSpace p.side)) :
    S.place p (c • O) = c • S.place p O := by
  ext i j
  cases p <;> simp [place, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- The twisted commutator of the point observables is small on average, on
either player side. This packages both orientations of
`eq:pts-obs-commutation`; paper
`14_analysis_of_the_pauli_basis_test.tex:309-354`, blueprint
`ch14_qpbt_observables.tex:761-794`. -/
theorem twisted_commutator_avg_le_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
        (side : PlayerSide), 0 ≤ ε →
      avgOver (uniformDistribution (PauliTuple P)) (fun ω =>
        ‖applyOperatorToState (S.placeStrategySide side (S.twistedCommutator side ω))
          S.toStrategy.ψ‖ ^ 2) ≤
        2 * (2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  intro P ε S side hε
  have hs : (0 : ℝ) ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  cases side with
  | alice =>
      have h := WinImplications.point_obs_twisted_commutation_explicit P ε S hε
      rw [WinImplications.opDistSq_eq_avgOver] at h
      refine le_trans (le_of_eq ?_) (le_trans h ?_)
      · refine avgOver_congr _ _ _ (fun ω => ?_)
        have hop : S.placeStrategySide .alice (S.twistedCommutator .alice ω) =
            heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1)
                (1 : Op S.toStrategy.ιB) -
              phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                heteroKron (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                  S.pointObs .alice .X ω.2.2.1 ω.1) 1 := by
          have h1 : heteroKron (S.twistedCommutator .alice ω)
              (1 : Op S.toStrategy.ιB) =
              heteroKron (S.pointObs .alice .X ω.2.2.1 ω.1 *
                S.pointObs .alice .Z ω.2.2.2 ω.2.1) 1 -
                heteroKron
                  (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                    (S.pointObs .alice .Z ω.2.2.2 ω.2.1 *
                      S.pointObs .alice .X ω.2.2.1 ω.1)) 1 :=
            heteroKron_sub_left _ _ _
          rw [← WinImplications.heteroKron_smul_left]
          exact h1
        rw [hop]
      · have hcoeff : 0 ≤
            2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
                1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
              (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
                3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4 := by
          positivity
        nlinarith
  | bob =>
      have h :=
        WinImplications.point_obs_twisted_commutation_interchanged_explicit P ε S hε
      rw [WinImplications.opDistSq_eq_avgOver] at h
      refine le_trans (le_of_eq ?_) (le_trans h ?_)
      · refine avgOver_congr _ _ _ (fun ω => ?_)
        have hop : S.placeStrategySide .bob (S.twistedCommutator .bob ω) =
            heteroKron (1 : Op S.toStrategy.ιA)
                (S.pointObs .bob .X ω.2.2.1 ω.1 *
                  S.pointObs .bob .Z ω.2.2.2 ω.2.1) -
              phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                heteroKron 1 (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
                  S.pointObs .bob .X ω.2.2.1 ω.1) := by
          have h1 : heteroKron (1 : Op S.toStrategy.ιA)
              (S.twistedCommutator .bob ω) =
              heteroKron 1 (S.pointObs .bob .X ω.2.2.1 ω.1 *
                S.pointObs .bob .Z ω.2.2.2 ω.2.1) -
                heteroKron 1
                  (phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
                    (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
                      S.pointObs .bob .X ω.2.2.1 ω.1)) :=
            heteroKron_sub_right _ _ _
          rw [← MagicSquareRigidity.heteroKron_smul_right]
          exact h1
        rw [hop]
      · have hcoeff : 0 ≤
            2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
                1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
              (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
                3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4 := by
          positivity
        nlinarith

end ProjectiveSetting

end

end MIPStarRE.QPBT
