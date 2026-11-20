module

public import QPBT.Observables.WinImplications.FactorTransport
public import QPBT.Observables.WinImplications.TwistedCommutation

/-!
# The factor-interchanged phase-signed commutation relation

Interchanging the tensor factors places Bob's point observables on the left.
The reversed consistency estimates of `lem:qld-win-implications` and Alice's
Magic Square anticommutation give the bound, which is then transported to the
original state. This proves the factor-interchanged relation in
`lem:qld-win-implications-obs`.

## References

The declarations formalize the trailing clause of
`lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-- The twisted commutation estimate on Bob's register follows by exchanging
players and transporting the estimate back to the original tensor order. -/
theorem point_obs_twisted_commutation_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε →
      opDistSq (uniformDistribution (PauliTuple P))
        (fun ω => heteroKron 1
          (S.pointProductAt .bob .X ω))
        (fun ω => ω.phase •
          heteroKron 1
            (S.pointProductAt .bob .Z ω))
        S.toStrategy.ψ ≤
          twistedCommutationConstant *
            Real.sqrt ε := by
  intro P ε S hε
  refine le_of_eq_of_le (opDistSq_smul_swappedState
    (uniformDistribution (PauliTuple P))
    PauliTuple.phase
    (S.pointProductAt .bob .X)
    (S.pointProductAt .bob .Z)
    S.toStrategy.ψ).symm ?_
  exact point_obs_twisted_commutation_explicit P ε S.swap hε

end WinImplications

end

end MIPStarRE.QPBT
