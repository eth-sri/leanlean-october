module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace DedekindZetaZeroFree.CompatibleFiniteNorm

noncomputable section

variable {𝕜 V : Type*} [NormedField 𝕜] [AddCommGroup V] [Module 𝕜 V]

section

variable (N : AddGroupNorm V)

abbrev normedAddCommGroup : NormedAddCommGroup V :=
  N.toNormedAddCommGroup

abbrev normedSpace
    (hN : ∀ (c : 𝕜) (v : V), N (c • v) = ‖c‖ * N v) :
    @NormedSpace 𝕜 V _ (normedAddCommGroup N).toSeminormedAddCommGroup := by
  letI := normedAddCommGroup N
  exact { toModule := inferInstance
          norm_smul_le := fun c v => (hN c v).le }

abbrev topology : TopologicalSpace V :=
  (normedAddCommGroup N).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

end

theorem exists_compatible (V : Type*) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] :
    ∃ N : AddGroupNorm V, ∀ (c : ℂ) (v : V), N (c • v) = ‖c‖ * N v := by
  classical
  let E := (Module.finBasis ℂ V).equivFun
  let N : AddGroupNorm V := {
    toFun := fun v => ‖E v‖
    map_zero' := by simp
    add_le' := by grind [norm_add_le]
    neg' := by simp
    eq_zero_of_map_eq_zero' := fun x hx => E.injective (by simpa using norm_eq_zero.mp hx)
  }
  refine ⟨N, ?_⟩
  intro c v
  change ‖E (c • v)‖ = ‖c‖ * ‖E v‖
  simp [norm_smul]

end
end DedekindZetaZeroFree.CompatibleFiniteNorm
