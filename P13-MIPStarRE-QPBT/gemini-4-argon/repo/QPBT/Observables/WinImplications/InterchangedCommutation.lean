module

public import QPBT.Observables.WinImplications.FactorTransport
public import QPBT.Observables.WinImplications.TwistedCommutation

/-!
# The factor-interchanged winning implications
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-- Factor-interchanged form of the low-degree winning implication. -/
theorem win_low_degree_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (linePointDist P.toLdParams)
        (fun sample a => heteroKron
          ((S.pointMeasOption .alice W sample.2).effect a) 1)
        (fun sample a => heteroKron 1
          ((S.lineEvalMeas .bob W sample.1 sample.2).effect a))
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S hε W
  rw [← consistencyDefect_swappedState]
  exact win_low_degree_explicit P ε S.swap hε W

/-- Factor-interchanged form of the Pauli-basis consistency implication. -/
theorem win_pauli_basis_cons_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pauliEvalMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S hε W
  rw [← consistencyDefect_swappedState]
  exact win_pauli_basis_cons_explicit P ε S.swap hε W

/-- The factor-interchanged phase-signed commutation relation on Bob's factor. -/
theorem point_obs_twisted_commutation_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointObs .bob .X ω.2.2.1 ω.1 *
            S.pointObs .bob .Z ω.2.2.2 ω.2.1))
        (fun ω => phaseSign (gammaValue P ω.1 ω.2.1 ω.2.2.1 ω.2.2.2) •
          heteroKron 1
            (S.pointObs .bob .Z ω.2.2.2 ω.2.1 *
              S.pointObs .bob .X ω.2.2.1 ω.1))
        S.toStrategy.ψ ≤
          (2 * (1024 * (2 * (Fintype.card PauliEdge : ℝ)) +
              1024 * Real.sqrt (4 * (Fintype.card PauliEdge : ℝ))) +
            (96 * (16 * (Fintype.card PauliEdge : ℝ)) +
              3551040 * (16 * (Fintype.card PauliEdge : ℝ))) + 4) *
            Real.sqrt ε := by
  intro P ε S hε
  rw [← opDistSq_smul_swappedState]
  exact point_obs_twisted_commutation_explicit P ε S.swap hε

end WinImplications

end

end MIPStarRE.QPBT
