module
public import QPBT.Observables.WinImplications.FactorTransport
public import QPBT.Games.DistanceTheorems.RoundingTransport
public import QPBT.Test.PauliSymmetry

/-! # Transporting winning bounds by symmetry of the verifier -/
@[expose] public section
open scoped BigOperators
namespace MIPStarRE.QPBT
open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
noncomputable section

namespace SymmetricGame
variable (G : SymmetricGame) (S : Strategy G.toGame)

/-- The players can be exchanged even when their local spaces are different. -/
def swapStrategy : Strategy G.toGame where
  ιA := S.ιB
  ιB := S.ιA
  ψ := reindexState (Equiv.prodComm _ _) S.ψ
  ψ_norm := (reindexState_norm_eq _ _).trans S.ψ_norm
  A := S.B
  B := S.A

theorem value_swapStrategy : (G.swapStrategy S).value = S.value := by
  simp only [Strategy.value, avgOver_eq_sum_univ, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  erw [G.μ_symm x y]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  exact congrArg₂ (fun t v => if t = true then v else 0) (G.decide_symm x y a b)
    ((by
       change DistanceCalculus.stateQForm (reindexState (Equiv.prodComm _ _) S.ψ)
         (heteroKron ((S.B x).effect a) ((S.A y).effect b)) = _
       rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_prodComm_heteroKron]
       rfl))

end SymmetricGame

def ProjectiveSetting.swap {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) :
    ProjectiveSetting P ε where
  toStrategy := (pauliBasisTestSymm P).swapStrategy S.toStrategy
  isProjective := ⟨S.isProjective.2, S.isProjective.1⟩
  win := ((pauliBasisTestSymm P).value_swapStrategy S.toStrategy).symm ▸ S.win

namespace WinImplications

/-- Factor-interchanged form of the low-degree winning implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:200-204,227`, blueprint
`ch14_qpbt_observables.tex:699-701`. -/
theorem win_low_degree_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (linePointDist P.toLdParams)
        (fun sample => S.pointMeasOption .alice W sample.2)
        (fun sample => S.lineEvalMeas .bob W sample.1 sample.2)
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S hε W
  rw [← bipartiteDefect_prodComm]
  exact win_low_degree_explicit P ε S.swap hε W

/-- Factor-interchanged form of the Pauli-basis consistency implication. Paper
`14_analysis_of_the_pauli_basis_test.tex:205-209,227`. -/
theorem win_pauli_basis_cons_interchanged_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
      0 ≤ ε → ∀ W : PauliKind,
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pauliEvalMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ ≤ 86 * ε := by
  intro P ε S hε W
  rw [← bipartiteDefect_prodComm]
  exact win_pauli_basis_cons_explicit P ε S.swap hε W

end WinImplications
end
end MIPStarRE.QPBT
