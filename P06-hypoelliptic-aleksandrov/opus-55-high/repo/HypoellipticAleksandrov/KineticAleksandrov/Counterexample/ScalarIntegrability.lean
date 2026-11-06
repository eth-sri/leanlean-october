module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetBounds
import Mathlib.Tactic

/-! # Local integrability of the actual scalar representative jets -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- Every selected scalar jet is locally integrable with respect to native spatial volume. -/
theorem scalarJets_locallyIntegrable (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    (∀ i, LocallyIntegrable (fun q => scalarGx gamma Lam q i) volume) ∧
    (∀ i, LocallyIntegrable (fun q => scalarGv gamma Lam q i) volume) ∧
    (∀ i k, LocallyIntegrable (fun q => scalarHess gamma Lam q i k) volume) := by
  have hx (i : Fin 1) : LocallyIntegrable (fun q => scalarGx gamma Lam q i) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega)
      (fun q => scalarGx gamma Lam q i)
      ((measurable_pi_apply i).comp (measurable_scalarGx gamma Lam)) (3 * gamma.1 - 3)
      (by grind) (by grind)
    · intro r hr q
      exact congrArg (fun w => w i) (scalarGx_homogeneous gamma Lam r hLam hr q)
    · intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      refine ⟨M, fun q hq => ?_⟩
      have hh : |scalarGx gamma Lam q i| ≤ ‖scalarGx gamma Lam q‖ := by
        simpa using norm_le_pi_norm (scalarGx gamma Lam q) i
      grind
  have hv (i : Fin 1) : LocallyIntegrable (fun q => scalarGv gamma Lam q i) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega)
      (fun q => scalarGv gamma Lam q i)
      ((measurable_pi_apply i).comp (measurable_scalarGv gamma Lam)) (3 * gamma.1 - 1)
      (by grind) (by grind)
    · intro r hr q
      exact congrArg (fun w => w i) (scalarGv_homogeneous gamma Lam r hLam hr q)
    · intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      refine ⟨M, fun q hq => ?_⟩
      have hh : |scalarGv gamma Lam q i| ≤ ‖scalarGv gamma Lam q‖ := by
        simpa using norm_le_pi_norm (scalarGv gamma Lam q) i
      grind
  have hh (i k : Fin 1) : LocallyIntegrable (fun q => scalarHess gamma Lam q i k) volume := by
    apply homogeneous_component_locallyIntegrable 1 (by omega)
      _ (measurable_scalarHess gamma Lam i k)
      (3 * gamma.1 - 2) (by grind) (by grind)
    · intro r hr q
      exact congrArg (fun w => w i k) (scalarHess_homogeneous gamma Lam r hLam hr q)
    · intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      exact ⟨M, fun q hq => (hM q hq).2.2 i k⟩
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
